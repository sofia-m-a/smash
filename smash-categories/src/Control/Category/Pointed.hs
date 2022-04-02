{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Control.Category.Pointed where

import Control.Arrow (Kleisli(..))
import Control.Categorical.Bifunctor (PFunctor, QFunctor)
import qualified Control.Categorical.Bifunctor as Bi
import Control.Categorical.Object
import qualified Control.Category as Cat
import Control.Category.Associative
import Control.Category.Braided
import Control.Category.Monoidal
import Control.Category.Cartesian
import Data.Bifunctor
import Data.Bitraversable
import Data.Can
import Data.Smash
import Data.These
import Data.These.Combinators
import Data.Wedge
import Data.Void
import qualified Data.Can as Can
import qualified Data.Smash as Smash
import qualified Data.Wedge as Wedge


newtype Marrow a b = Marrow { runMarrow :: a -> Maybe b }
    deriving Cat.Category via Kleisli Maybe


-- Note: Can, Smash, and Wedge are the shadow on (->) of These, (,), and Either in Marrow
-- namely, (a `Marrow` (b, c)) ~ (a -> Smash b c) etc.
-- So it's really the types These, (,), and Either that form the actual product, tensor, and coproduct in Marrow


-- Void is the zero object in Hask*
instance HasTerminalObject Marrow where
    type Terminal Marrow = Void
    terminate = Marrow (const Nothing)

instance HasInitialObject Marrow where
    type Initial Marrow = Void
    initiate = Marrow (const Nothing)


-- Can a b ~ Maybe (These a b)
toCan :: Maybe (These a b) -> Can a b
toCan = maybe Non (these One Eno Two)

fromCan :: Can a b -> Maybe (These a b)
fromCan = can Nothing (Just . This) (Just . That) (\a b -> Just $ These a b)

instance PFunctor These Marrow Marrow where
    first (Marrow f) = Marrow $ bitraverse f Just
instance QFunctor These Marrow Marrow where
    second (Marrow f) = Marrow $ bitraverse Just f
instance Bi.Bifunctor These Marrow Marrow Marrow where
    bimap (Marrow f) (Marrow g) = Marrow $ bitraverse f g
instance Associative Marrow These where
    associate = Marrow $ Just . assocThese
    disassociate = Marrow $ Just . unassocThese
instance Braided Marrow These where
    braid = Marrow $ Just . swapThese
instance Symmetric Marrow These
instance Monoidal Marrow These where
    type Id Marrow These = Void
    idl = Marrow $ \case
        These v _ -> absurd v
        This v -> absurd v
        That a -> Just a
    idr = Marrow $ \case
        These  _ v -> absurd v
        This a -> Just a
        That v -> absurd v
    coidl = Marrow $ Just . That
    coidr = Marrow $ Just . This

-- Can is the product in Hask*
instance Cartesian Marrow where
    type Product Marrow = These
    fst = Marrow justHere
    snd = Marrow justThere
    diag = Marrow $ \a -> Just (These a a)
    Marrow f &&& Marrow g = Marrow $ \a -> case (f a, g a) of
        (Just a, Just b) -> Just (These a b)
        (Just a, Nothing) -> Just (This a)
        (Nothing, Just b) -> Just (That b)
        (Nothing, Nothing) -> Nothing

instance PFunctor Can (->) (->) where
    first = first
instance QFunctor Can (->) (->) where
    second = second
instance Bi.Bifunctor Can (->) (->) (->) where
    bimap = bimap
instance Associative (->) Can where
    associate = Can.reassocLR
    disassociate = Can.reassocRL
instance Braided (->) Can where
    braid = swapCan
instance Symmetric (->) Can
-- instance Monoidal (->) Can is impossible


-- Smash a b ~ Maybe (a, b)
instance PFunctor (,) Marrow Marrow where
    first (Marrow f) = Marrow $ bitraverse f Just
instance QFunctor (,) Marrow Marrow where
    second (Marrow f) = Marrow $ bitraverse Just f
instance Bi.Bifunctor (,) Marrow Marrow Marrow where
    bimap (Marrow f) (Marrow g) = Marrow $ bitraverse f g
instance Associative Marrow (,) where
    associate = Marrow $ \((a, b), c) -> Just (a, (b, c))
    disassociate = Marrow $ \(a, (b, c)) -> Just ((a, b), c)
instance Braided Marrow (,) where
    braid = Marrow $ \(a, b) -> Just (b, a)
instance Monoidal Marrow (,) where
    type Id Marrow (,) = ()
    idl = Marrow $ \((), a) -> Just a
    idr = Marrow $ \(a, ()) -> Just a
    coidl = Marrow $ \a -> Just ((), a)
    coidr = Marrow $ \a -> Just (a, ())
instance Symmetric Marrow (,)

-- Smash, or rather (,) which is the shadow of Smash on the category Marrow,
-- forms a tensor/hom adjunction
curryMarrow :: ((a, b) `Marrow` c) -> a `Marrow` (b `Marrow` c)
curryMarrow (Marrow f) = Marrow $ \a -> Just $ Marrow $ \b -> f (a, b)

uncurryMarrow :: a `Marrow` (b `Marrow` c) -> ((a, b) `Marrow` c)
uncurryMarrow (Marrow f) = Marrow $ \(a, b) -> f a >>= ($ b) . runMarrow

{-
uncurryMarrow $ curryMarrow (Marrow f)
= 
Marrow $ \(a, b) -> (\a -> Just $ Marrow $ \b -> f (a, b)) a >>= ($ b) . runMarrow
=
Marrow $ \(a, b) -> Just $ Marrow $ \b -> f (a, b) >>= ($ b) . runMarrow
=
Marrow $ \(a, b) -> ($ b) . runMarrow $ Marrow $ \b -> f (a, b)
=
Marrow $ \(a, b) -> f (a, b)
=
Marrow f

curryMarrow $ uncurryMarrow (Marrow f)
=
Marrow $ \a -> Just $ Marrow $ \b -> (\(a, b) -> f a >>= ($ b) . runMarrow) (a, b)
=
Marrow $ \a -> Just $ Marrow $ \b -> f a >>= ($ b) . runMarrow
=
Marrow $ \a -> Just $ Marrow $ \b -> case f a of
    Nothing -> Nothing
    Just (Marrow g) -> g b
=
Marrow $ \a -> case f a of
    Nothing -> Just $ Marrow $ \b -> Nothing
    Just (Marrow g) -> Just $ Marrow $ \b -> g b
= but, Just (Marrow $ const Nothing) should be ~ Nothing
Marrow $ \a -> case f a of
    Nothing -> Nothing
    Just (Marrow g) -> Just $ Marrow $ \b -> g b
= Marrow $ \a -> f a
= Marrow f
-}

instance PFunctor Smash (->) (->) where
    first = first
instance QFunctor Smash (->) (->) where
    second = second
instance Bi.Bifunctor Smash (->) (->) (->) where
    bimap = bimap
instance Associative (->) Smash where
    associate = Smash.reassocLR
    disassociate = Smash.reassocRL
instance Braided (->) Smash where
    braid = swapSmash
instance Symmetric (->) Smash
-- instance Monoidal (->) Smash is impossible


-- Wedge a b ~ Maybe (Either a b)
toWedge :: Maybe (Either a b) -> Wedge a b
toWedge = maybe Nowhere (either Here There)

fromWedge :: Wedge a b -> Maybe (Either a b)
fromWedge = wedge Nothing (Just . Left) (Just . Right)

instance PFunctor Either Marrow Marrow where
    first (Marrow f) = Marrow $ bitraverse f Just
instance QFunctor Either Marrow Marrow where
    second (Marrow f) = Marrow $ bitraverse Just f
instance Bi.Bifunctor Either Marrow Marrow Marrow where
    bimap (Marrow f) (Marrow g) = Marrow $ bitraverse f g
instance Associative Marrow Either where
    associate = Marrow $ Just . assocEither
    disassociate = Marrow $ Just . unassocEither
instance Braided Marrow Either where
    braid = Marrow $ Just . either Right Left
instance Monoidal Marrow Either where
    type Id Marrow Either = Void
    idl = Marrow $ either absurd Just
    idr = Marrow $ either Just absurd
    coidl = Marrow $ Just . Right
    coidr = Marrow $ Just . Left
instance Symmetric Marrow Either

{--}
assocEither :: Either (Either a b) c -> Either a (Either b c)
assocEither (Left (Left a)) = Left a
assocEither (Left (Right b)) = Right (Left b)
assocEither (Right c) = Right (Right c)

unassocEither :: Either a (Either b c) -> Either (Either a b) c
unassocEither (Left a) = Left (Left a)
unassocEither (Right (Left b)) = Left (Right b)
unassocEither (Right (Right c)) = Right c
{--}

-- Wedge is the coproduct in Hask*
instance CoCartesian Marrow where
    type Sum Marrow = Either
    inl = Marrow $ Just . Left
    inr = Marrow $ Just . Right
    codiag = Marrow $ Just . either id id
    Marrow f ||| Marrow g = Marrow $ either f g

instance PFunctor Wedge (->) (->) where
    first = first
instance QFunctor Wedge (->) (->) where
    second = second
instance Bi.Bifunctor Wedge (->) (->) (->) where
    bimap = bimap
instance Associative (->) Wedge where
    associate = Wedge.reassocLR
    disassociate = Wedge.reassocRL
instance Braided (->) Wedge where
    braid = swapWedge
instance Symmetric (->) Wedge
-- instance Monoidal (->) Wedge is impossible
