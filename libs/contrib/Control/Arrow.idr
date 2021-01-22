module Control.Arrow

import Control.Category
import Data.Either
import Data.Morphisms


infixr 5 <++>
infixr 3 ***
infixr 3 &&&
infixr 2 +++
infixr 2 \|/

public export
interface Category arr => Arrow (0 arr : Type -> Type -> Type) where
  arrow  : (a -> b) -> arr a b
  first  : arr a b -> arr (a, c) (b, c)

  second : arr a b -> arr (c, a) (c, b)
  second f = arrow {arr = arr} swap >>> first f >>> arrow {arr = arr} swap
    where
    swap : (x, y) -> (y, x)
    swap (a, b) = (b, a)

  (***)  : arr a b -> arr a' b' -> arr (a, a') (b, b')
  f *** g = first f >>> second g

  (&&&)  : arr a b -> arr a b' -> arr a (b, b')
  f &&& g = arrow dup >>> f *** g
    where
    dup : x -> (x,x)
    dup x = (x,x)

public export
implementation Arrow Morphism where
  arrow  f            = Mor f
  first  (Mor f)      = Mor $ \(a, b) => (f a, b)
  second (Mor f)      = Mor $ \(a, b) => (a, f b)
  (Mor f) *** (Mor g) = Mor $ \(a, b) => (f a, g b)
  (Mor f) &&& (Mor g) = Mor $ \a => (f a, g a)

public export
implementation Monad m => Arrow (Kleislimorphism m) where
  arrow f = Kleisli (pure . f)
  first (Kleisli f) =  Kleisli $ \(a, b) => do x <- f a
                                               pure (x, b)

  second (Kleisli f) = Kleisli $ \(a, b) => do x <- f b
                                               pure (a, x)

  (Kleisli f) *** (Kleisli g) = Kleisli $ \(a, b) => do x <- f a
                                                        y <- g b
                                                        pure (x, y)

  (Kleisli f) &&& (Kleisli g) = Kleisli $ \a => do x <- f a
                                                   y <- g a
                                                   pure (x, y)

public export
interface Arrow arr => ArrowZero (0 arr : Type -> Type -> Type) where
  zeroArrow : arr a b

public export
interface ArrowZero arr => ArrowPlus (0 arr : Type -> Type -> Type) where
  (<++>) : arr a b -> arr a b -> arr a b

public export
interface Arrow arr => ArrowChoice (0 arr : Type -> Type -> Type) where
  left  : arr a b -> arr (Either a c) (Either b c)

  right : arr a b -> arr (Either c a) (Either c b)
  right f = arrow mirror >>> left f >>> arrow mirror


  (+++) : arr a b -> arr c d -> arr (Either a c) (Either b d)
  f +++ g = left f >>> right g

  (\|/) : arr a b -> arr c b -> arr (Either a c) b
  f \|/ g = f +++ g >>> arrow fromEither
    where
    fromEither : Either b b -> b
    fromEither (Left b) = b
    fromEither (Right b) = b

public export
implementation Monad m => ArrowChoice (Kleislimorphism m) where
  left f                      = f          +++ (arrow id)
  right f                     = (arrow id) +++ f
  f           +++ g           = (f >>> (arrow Left)) \|/ (g >>> (arrow Right))
  (Kleisli f) \|/ (Kleisli g) = Kleisli (either f g)

public export
interface Arrow arr => ArrowApply (0 arr : Type -> Type -> Type) where
  app : arr (arr a b, a) b

public export
implementation Monad m => ArrowApply (Kleislimorphism m) where
  app = Kleisli $ \(Kleisli f, x) => f x

public export
data ArrowMonad : (Type -> Type -> Type) -> Type -> Type where
  MkArrowMonad : (runArrowMonad : arr (the Type ()) a) -> ArrowMonad arr a

public export
runArrowMonad : ArrowMonad arr a -> arr (the Type ()) a
runArrowMonad (MkArrowMonad a) = a

public export
implementation Arrow a => Functor (ArrowMonad a) where
  map f (MkArrowMonad m) = MkArrowMonad $ m >>> arrow f

public export
implementation Arrow a => Applicative (ArrowMonad a) where
  pure x = MkArrowMonad $ arrow $ \_ => x
  (MkArrowMonad f) <*> (MkArrowMonad x) = MkArrowMonad $ f &&& x >>> arrow (uncurry id)

public export
implementation ArrowApply a => Monad (ArrowMonad a) where
  (MkArrowMonad m) >>= f =
    MkArrowMonad $ m >>> (arrow $ \x => (runArrowMonad (f x), ())) >>> app

public export
interface Arrow arr => ArrowLoop (0 arr : Type -> Type -> Type) where
  loop : arr (Pair a c) (Pair b c) -> arr a b
