{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
-- | This module implements bitvector operations on top of fixed-length words
module Data.BitVector.Word (
  -- * Type and construction
  BV,
  bv,
  bv',
  ones,
  zeros,
  append,
  -- * Inspection
  null,
  empty,
  -- * Modifications
  slice,
  inject,
  -- * Conversion
  zeroExtend,
  signExtend,
  extract,
  -- * Kind stuff
  VecState(..)
  ) where

import Data.Bits
import Data.Monoid

import Prelude hiding ( null, length )

data VecState = Extended
              | Unextended

-- | BitVectors backed by a concrete fixed-width word type and parameterized by
-- a state.
--
-- Unextended vectors can be extended by 'appending' one 'BV' to another.
-- Extended vectors can be subject to standard bitwise operations from the
-- 'Bits' and 'FiniteBits' classes.
data BV w (e :: VecState) = BV {-# UNPACK #-}!Word w
  deriving (Eq, Ord, Show)

-- | Extend the first 'BV' by the second.
--
-- The bits of the first 'BV' are shifted left in the underlying word to make
-- room for the new bits from the second 'BV'.  Note that this can drop bits
-- from the first 'BV' if there is not enough room in the underlying word for
-- all of the bits.
append :: (FiniteBits w) => BV w 'Unextended -> BV w 'Unextended -> BV w 'Unextended
append (BV l1 w1) (BV l2 w2) = BV l3 w3
  where
    l3 = truncBits (l1 + l2) w1
    w3 = (w1 `shiftL` fromIntegral l2) .|. w2
{-# INLINE append #-}

-- | Zero extend the underlying word, making it suitable for bitwise operations.
--
-- Note that this is actually a no-op and really just changes the type of the
-- bitvector.
zeroExtend :: (FiniteBits w) => BV w 'Unextended -> BV w 'Extended
zeroExtend (BV _ w) = BV (fromIntegral (finiteBitSize w)) w
{-# INLINE zeroExtend #-}

-- | Sign extend the underlying word, making it suitable for bitwise operations.
signExtend :: (FiniteBits w, Num w) => BV w 'Unextended -> BV w 'Extended
signExtend bits@(BV l w)
  | l == 0 || w == 0 = BV (fromIntegral (finiteBitSize w)) w
  | otherwise =
    case testBit w (fromIntegral l - 1) of
      False -> zeroExtend bits
      True -> zeroExtend (ones (fromIntegral nBits) `append` bits)
  where
    nBits = finiteBitSize w
{-# INLINE signExtend #-}

-- | Extract the underlying word from the bitvector
extract :: BV w 'Extended -> w
extract (BV _ w) = w
{-# INLINE extract #-}

-- | Test if the bitvector is empty (i.e., has no bits)
null :: BV w e -> Bool
null (BV l _) = l == 0
{-# INLINE null #-}

-- | Construct an empty bitvector
empty :: (FiniteBits w, Num w) => BV w 'Unextended
empty = zeros 0
{-# INLINE empty #-}

-- | Construct a bitvector of a given length with all ones
ones :: (FiniteBits w, Num w) => Word -> BV w 'Unextended
ones num = BV num (w0 `shiftL` fromIntegral nBits)
  where
    w0 = 1
    nBits = truncBits num w0
{-# INLINE ones #-}

-- | Construct a bitvector of the given length with all zeros
zeros :: (FiniteBits w, Num w) => Word -> BV w 'Unextended
zeros num = BV nBits w
  where
    w = 0
    nBits = truncBits num w
{-# INLINE zeros #-}

-- | Construct a bitvector from the low bits of the given word
--
-- The high bits are discarded.
bv :: (FiniteBits w, Num w) => Word -> w -> BV w 'Unextended
bv nBits w = BV nBits' (mask .&. w)
  where
    nBits' = truncBits nBits w
    mask = 1 `shiftL` fromIntegral nBits'
{-# INLINE bv #-}

-- | Construct an extended bitvector from an existing word
bv' :: (FiniteBits w) => w -> BV w 'Extended
bv' w = BV (fromIntegral (finiteBitSize w)) w
{-# INLINE bv' #-}

-- | Extract a contiguous sequence of bits from a bitvector, shifting the result
-- such that the least significant bit of the slice is located at bit zero.
slice :: (FiniteBits w, Num w)
      => BV w 'Extended
      -> Word
      -- ^ Bit index to slice from
      -> Word
      -- ^ Number of bits to include in the slice
      -> w
slice (BV _ w) ix nBits = mask .&. (w `shiftR` fromIntegral ix)
  where
    mask = 1 `shiftL` fromIntegral nBits
{-# INLINE slice #-}

-- | Inject a specified number of bits at the given index in a source word into
-- a bitvector
inject :: (FiniteBits w, Num w)
       => Word
       -- ^ The number of bits of the source word @w@ to inject
       -> Word
       -- ^ The index into the bitvector to inject the bits at
       -> w
       -- ^ The word @w@ containing source bits
       -> BV w 'Extended
       -- ^ The bitvector to modify
       -> BV w 'Extended
inject nBits ix w0 (BV l w1) = BV l (w1 .|. w2)
  where
    mask = 1 `shiftL` fromIntegral nBits
    bits = w0 .&. mask
    w2 = bits `shiftL` fromIntegral ix
{-# INLINE inject #-}

-- | This is a helper to ensure we always have a sane number of bits in the size
-- field
truncBits :: (FiniteBits w) => Word -> w -> Word
truncBits n w = min n (fromIntegral (finiteBitSize w))
{-# INLINE truncBits #-}

-- | Only unextended bitvectors can be subject to the monoid operations
instance (FiniteBits w, Num w) => Monoid (BV w 'Unextended) where
  mempty = empty
  mappend = append

-- | Only extended bitvectors can be used in bitwise operations
instance (FiniteBits w, Num w) => Bits (BV w 'Extended) where
  (BV l1 w1) .&. (BV _ w2) = BV l1 (w1 .&. w2)
  (BV l1 w1) .|. (BV _ w2) = BV l1 (w1 .|. w2)
  (BV l1 w1) `xor` (BV _ w2) = BV l1 (w1 `xor` w2)
  complement (BV l w) = BV l (complement w)
  (BV l w) `shift` i = BV l (w `shift` i)
  (BV l w) `rotate` i = BV l (w `rotate` i)
  zeroBits = zeroExtend empty
  bit i =
    let w = bit i
    in BV (fromIntegral (finiteBitSize w)) w
  testBit (BV _ w) i = testBit w i
  bitSizeMaybe (BV _ w) = bitSizeMaybe w
  bitSize (BV _ w) = finiteBitSize w
  isSigned (BV _ w) = isSigned w
  shiftL (BV l w) i = BV l (shiftL w i)
  shiftR (BV l w) i = BV l (shiftR w i)
  rotateL (BV l w) i = BV l (rotateL w i)
  rotateR (BV l w) i = BV l (rotateR w i)
  popCount (BV _ w) = popCount w

instance (FiniteBits w, Num w) => FiniteBits (BV w 'Extended) where
  finiteBitSize (BV _ w) = finiteBitSize w
