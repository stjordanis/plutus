{-# OPTIONS -Wall #-}







module PlutusCore.BuiltinEvaluation where

import PlutusCore.Term
import PlutusShared.BoolToTerm
--import PlutusShared.Qualified
import Utils.ABT
import Utils.Pretty

import Crypto.Hash
import qualified Crypto.Sign.Ed25519 as Ed25519 ()
import qualified Data.Binary as B
import qualified Data.ByteArray as BA
import qualified Data.ByteString.Lazy as BS
import Data.List (intercalate)








builtin :: String
        -> [Term]
        -> Either String Term
builtin "addInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (PrimInteger (x + y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin addInteger: "
                ++ intercalate "," (map pretty xs)
builtin "subtractInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (PrimInteger (x - y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin subtractInteger: "
                ++ intercalate "," (map pretty xs)
builtin "multiplyInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (PrimInteger (x * y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin multiplyInteger: "
                ++ intercalate "," (map pretty xs)
builtin "divideInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (PrimInteger (div x y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin divideInteger: "
                ++ intercalate "," (map pretty xs)
builtin "remainderInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (PrimInteger (mod x y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin remainderInteger: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (boolToScottTerm (x < y))
    _ ->
      Left $ "Incorrect arguments for builtin lessThanInteger: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanEqualsInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (boolToScottTerm (x <= y))
    _ ->
      Left $ "Incorrect arguments for builtin lessThanEqualsInteger: "
                ++ intercalate "," (map pretty xs)
builtin "greaterThanInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (boolToScottTerm (x > y))
    _ ->
      Left $ "Incorrect arguments for builtin greaterThanInteger: "
                ++ intercalate "," (map pretty xs)
builtin "greaterThanEqualsInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (boolToScottTerm (x >= y))
    _ ->
      Left $ "Incorrect arguments for builtin greaterThanEqualsInteger: "
                ++ intercalate "," (map pretty xs)

builtin "equalsInteger" xs =
  case xs of
    [PrimInteger x :$: [], PrimInteger y :$: []] ->
      Right (boolToScottTerm (x == y))
    _ ->
      Left $ "Incorrect arguments for builtin equalsInteger: "
                ++ intercalate "," (map pretty xs)
builtin "intToFloat" xs =
  case xs of
    [PrimInteger x :$: []] ->
      Right (PrimFloat (fromInteger x) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin intToFloat: "
                ++ intercalate "," (map pretty xs)
builtin "intToByteString" xs =
  case xs of
    [PrimInteger x :$: []] ->
      Right (PrimByteString (B.encode x) :$: [])
    _ ->
      Left
        $ "Incorrect arguments for builtin intToBytestring: "
       ++ intercalate "," (map pretty xs)
builtin "addFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (PrimFloat (x + y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin addFloat: "
                ++ intercalate "," (map pretty xs)
builtin "subtractFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (PrimFloat (x - y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin subtractFloat: "
                ++ intercalate "," (map pretty xs)  
builtin "multiplyFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (PrimFloat (x * y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin multiplyFloat: "
                ++ intercalate "," (map pretty xs)
builtin "divideFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (PrimFloat (x / y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin divideFloat: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (boolToScottTerm (x < y))
    _ ->
      Left $ "Incorrect arguments for builtin lessThanFloat: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanEqualsFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (boolToScottTerm (x <= y))
    _ ->
      Left $ "Incorrect arguments for builtin lessThanEqualsFloat: "
                ++ intercalate "," (map pretty xs)
builtin "greaterThanFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (boolToScottTerm (x > y))
    _ ->
      Left $ "Incorrect arguments for builtin greaterThanFloat: "
                ++ intercalate "," (map pretty xs)
builtin "greaterThanEqualsFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (boolToScottTerm (x >= y))
    _ ->
      Left $ "Incorrect arguments for builtin greaterThanEqualsFloat: "
                ++ intercalate "," (map pretty xs)
builtin "equalsFloat" xs =
  case xs of
    [PrimFloat x :$: [], PrimFloat y :$: []] ->
      Right (boolToScottTerm (x == y))
    _ ->
      Left $ "Incorrect arguments for builtin equalsFloat: "
                ++ intercalate "," (map pretty xs)
builtin "ceiling" xs =
  case xs of
    [PrimFloat x :$: []] ->
      Right (PrimInteger (ceiling x) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin ceiling: "
                ++ intercalate "," (map pretty xs)
builtin "floor" xs =
  case xs of
    [PrimFloat x :$: []] ->
      Right (PrimInteger (floor x) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin floor: "
                ++ intercalate "," (map pretty xs)
builtin "round" xs =
  case xs of
    [PrimFloat x :$: []] ->
      Right (PrimInteger (round x) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin round: "
                ++ intercalate "," (map pretty xs)
builtin "concatenate" xs =
  case xs of
    [PrimByteString x :$: [], PrimByteString y :$: []] ->
      Right (PrimByteString (BS.concat [x,y]) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin concatenate: "
                ++ intercalate "," (map pretty xs)
builtin "dropByteString" xs =
  case xs of
    [PrimInteger x :$: [], PrimByteString y :$: []] ->
      Right (PrimByteString (BS.drop (fromIntegral x) y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin dropByteString: "
                ++ intercalate "," (map pretty xs)
builtin "takeByteString" xs =
  case xs of
    [PrimInteger x :$: [], PrimByteString y :$: []] ->
      Right (PrimByteString (BS.take (fromIntegral x) y) :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin takeByteString: "
                ++ intercalate "," (map pretty xs)
builtin "sha2_256" xs =
  case xs of
    [PrimByteString x :$: []] ->
      Right (PrimByteString
                   (BS.pack
                     (BA.unpack (hash (BS.toStrict x) :: Digest SHA256)))
                     :$: [])
    _ ->
      Left $ "Incorrect arguments for builtin sha2_256: "
                ++ intercalate "," (map pretty xs)
builtin "sha3_256" xs =
  case xs of
    [PrimByteString x :$: []] ->
      Right (PrimByteString
                   (BS.pack
                     (BA.unpack (hash (BS.toStrict x) :: Digest SHA3_256)))
                     :$: [])
    _ ->         
      Left $ "Incorrect arguments for builtin sha2_256: "
                ++ intercalate "," (map pretty xs)
builtin "equalsByteString" xs =
  case xs of
    [PrimByteString x :$: [], PrimByteString y :$: []] ->
      Right (boolToScottTerm (x == y))
    _ ->
      Left $ "Incorrect arguments for builtin equalsByteString: "
                ++ intercalate "," (map pretty xs)     
builtin n _ =
  Left $ "No builtin named " ++ n