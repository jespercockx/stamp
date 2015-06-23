module Data where


data Foo = Barry | Bar Bool

data Foo2 = Barry2 | Bar2 Bool Foo

data Pair a b = Pair a b


data ARecord a
  = ARecord
    { _aBool :: Bool
    , _aChar :: Char
    , _anA   :: a
    }
