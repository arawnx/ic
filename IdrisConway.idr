module IdrisConway

-- an implementation of https://kleczkow.ski/conway-aol-with-comonads/
-- thanks to Konrad Kleczowski

import Data.List
import Data.String

interface Functor w => Comonad (0 w : Type -> Type) where
  extract : w a -> a
  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate
  duplicate : w a -> w (w a)
  duplicate = extend id

interface Comonad w => VerifiedComonad (w : Type -> Type) where
  comonadLeftIdentity : (wx : w a) -> IdrisConway.extract `extend` wx = wx
  comonadRightIdentity : (wx : w a) -> (f : w a -> b) -> extract (f `extend` wx) = f wx
  comonadAssociative : (wx : w a) -> (f : w b -> c) -> (g : w a -> b) -> (extend f . extend g) wx = extend (f . extend g) wx

-- composeCoKleisli : Comonad w => (w a -> b) -> (w b -> c) -> (w a) -> c
-- composeCoKleisli f g l = g (extend f l)

data StoreComonad s a = Store s (s -> a)

extractStore : StoreComonad s a -> a
extractStore (Store s a) = a s

scmap : (StoreComonad s a -> b) -> StoreComonad s a -> StoreComonad s b
scmap f (Store s a) = Store s (\x => f (Store x a))

Functor (StoreComonad w) where
  map f = scmap (f . extractStore)

Comonad (StoreComonad w) where
  extract = extractStore
  extend = scmap

CellPlane : (a : Type) -> Type
CellPlane a = StoreComonad (Int,Int) a

data Conway = Dead | Alive

Eq Conway where
  (==) Dead Dead = True
  (==) Alive Alive = True
  (==) Dead Alive = False
  (==) Alive Dead = False

Show Conway where
  show Alive = "Alive"
  show Dead = "Dead"

experiment : Functor f => (s -> f s) -> StoreComonad s a -> f a
experiment f (Store s a) = map a (f s)

neighbors : (Int,Int) -> List (Int,Int)
neighbors (x,y) = [ (x+k,y+j) | k <- [(-1)..1], j <- [(-1)..1], (j,k)/=(0,0)]

neighborCells : CellPlane Conway -> List Conway
neighborCells = experiment neighbors

oneStep : CellPlane Conway -> Conway
oneStep p = case (extract p) of
              Alive => if (nn `elem` [2,3]) then Alive else Dead
              Dead => if (nn == 3) then Alive else Dead
          where
            nn : Nat
            nn = length (filter (== Alive) (neighborCells p))

toCellPlane : List (Int,Int,Conway) -> CellPlane Conway
toCellPlane cs = Store (0,0) access
  where
    access : (Int,Int) -> Conway
    access (x,y) = if (x,y,Alive) `elem` cs then Alive else Dead

rectify : ((a,b),c) -> (a,b,c)
rectify ((a,b),c) = (a,b,c)
unrectify : (a,b,c) -> ((a,b),c)
unrectify (a,b,c) = ((a,b),c)

toCellPlane' : List ((Int,Int),Conway) -> CellPlane Conway
toCellPlane' = toCellPlane . (map rectify)

fromCellPlane :  (Int,Int,Int,Int) -> CellPlane Conway -> List ((Int,Int),Conway)
fromCellPlane (x,y,w,h) p = zip coords (experiment (const coords) p)
  where
    coords : List (Int,Int)
    coords = concat [[(x+i,y+j) | i <- [0..h]] | j <- [0..w]]

fromCellPlaneLiving :  (Int,Int,Int,Int) -> CellPlane Conway -> List ((Int,Int),Conway)
fromCellPlaneLiving x y = (filter filt) $ (fromCellPlane x y)
  where filt : (_,Conway) -> Bool
        filt (_,Alive) = True
        filt (_,Dead)  = False

evolutions : Nat -> CellPlane Conway -> List (CellPlane Conway)
evolutions Z r = pure r
evolutions (S k) r = r :: (evolutions k rr)
  where rr : CellPlane Conway
        rr = extend oneStep r

width : Int
width = 20
height : Int
height = width

rView : (Int,Int,Int,Int)
rView = ((width*(-1)),(height*(-1)),width*2,height*2)

glider' : List ((Int,Int),Conway)
glider' = unrectify <$> [(0,0,Alive),((-1),0,Alive),(1,0,Alive),(1,1,Alive),(0,2,Alive)]

glider : CellPlane Conway
glider=toCellPlane [(0,0,Alive),((-1),0,Alive),(1,0,Alive),(1,1,Alive),(0,2,Alive)]

-- b : CellPlane Conway
-- b = (extend oneStep) $ toCellPlane $ rectify <$> (fromCellPlaneLiving rView glider)
--   where rectify ((a,b),c) = (a,b,c)
--
-- c : CellPlane Conway
-- c = (extend oneStep) $ toCellPlane $ rectify <$> (fromCellPlaneLiving rView b)

memoizeEvolutions : Nat -> CellPlane Conway -> List ( List ((Int,Int),Conway) )
memoizeEvolutions Z a = [fromCellPlaneLiving rView b]
  where b : CellPlane Conway
        b = (extend oneStep) a
memoizeEvolutions (S k) a = (fromCellPlaneLiving rView b) :: (memoizeEvolutions k c)
  where b : CellPlane Conway
        c : CellPlane Conway
        b = (extend oneStep) a
        c = toCellPlane' $ fromCellPlaneLiving rView b

advance : List ((Int,Int),Conway) -> IO ()
advance las = do putStrLn (show las)
                 _ <- getLine
                 let nlas = extend oneStep $ toCellPlane' las
                 advance $ fromCellPlaneLiving rView nlas

access : List ((Int,Int),Conway) -> (Int -> Int -> Conway)
access ls x y = if (((((x,y),Dead) `elem` ls) || (((== 0) . length) $ filter f ls))) then Dead else Alive
  where f : ((Int,Int),Conway) -> Bool
        f (a,_) = (x,y) == a

reify : Int -> Int -> (Int -> Int -> Conway) -> String
reify w h f = unlines $ pack <$> [[ff x y | y <- [(-h)..h]] | x <- [(-w)..w]]
  where ff : Int -> Int -> Char
        ff x y = if (f x y == Alive) then '#' else '_'

toText : Int -> Int -> List ((Int,Int),Conway) -> String
toText w h ls = (reify w h) (access ls)

firstTen : String
firstTen = unlines $ f <$> memoizeEvolutions 10 glider
  where f = toText width height

firstN : Nat -> String
firstN n = unlines $ f <$> memoizeEvolutions n glider

main : IO ()
main = do putStrLn "How many? "
          s <- getLine
          case (parsePositive s) of
            Just n => putStrLn $ firstN n
            Nothing => pure ()
