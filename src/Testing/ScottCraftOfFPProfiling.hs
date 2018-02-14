module Testing.ScottCraftOfFPProfiling where

import Testing.Testing

main :: IO ()
main = replFiles ["src/ScottPrelude.plc", "src/Testing/ScottCraftOfFP.plc"]