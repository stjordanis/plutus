{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}







-- | This module defines the main server functionality of Language Engine.

module Main where

import Interface.JSVM

{-
import API.Apps
import API.Authorization
import API.Login
import API.Packages
import API.Users
-}

import Data.Aeson
import GHC.Generics
{-
import qualified Data.ByteString.Char8 as BS
import qualified Database.PostgreSQL.Simple as DB
import Network.Mail.SMTP
-}
import Network.Socket (HostName,PortNumber)
import Network.Wai.Handler.Warp
--import Network.Wai.Middleware.Cors
import Servant
import System.Environment
import System.IO

import Paths_plutus_prototype








data TryPlutusRequest =
  TryPlutusRequest
  { declarations :: String
  , expression :: String
  }
  deriving (Generic)

instance FromJSON TryPlutusRequest

data TryPlutusResponse =
  TryPlutusResponse
  { responseText :: String
  , responseInfo :: String
  }
  deriving (Generic)

instance ToJSON TryPlutusResponse

-- | The API has a number of sub-APIs for various functionalities.

type TryPlutusAPI =
  "compile"
    :> ReqBody '[JSON] TryPlutusRequest
    :> Post '[JSON] TryPlutusResponse





apiServer :: Server TryPlutusAPI
apiServer (TryPlutusRequest decls expr) =
  case loadExpression decls expr of
    Left err -> return $ TryPlutusResponse "Error" err
    Right expr' -> return $ TryPlutusResponse "Ok" expr'





type TryPlutusSite = Raw





siteServer :: FilePath -> Server TryPlutusSite
siteServer fp
  = serveDirectory fp





-- | The whole LE server type consists of a site server and an api server.

type TryPlutusServer =
       "api" :> TryPlutusAPI
  :<|> "site" :> TryPlutusSite





server :: FilePath -> Server TryPlutusServer
server fp =
       apiServer
  :<|> siteServer fp





tryPlutusServer :: Proxy TryPlutusServer
tryPlutusServer = Proxy





-- basicAuthMain :: IO ()
-- basicAuthMain = run 8080 (serveWithContext basicAuthApi serverContext server)

main :: IO ()
main = do
  --fp <- getDataFileName ""
  let fp = "./site"
  putStrLn $ "data file location: " ++ fp
  hSetBuffering stdout LineBuffering
  env <- getEnvironment
  let port = maybe 80 read $ lookup "PORT" env
  putStrLn $ "Running server on port " ++ show port ++ "..."
  run port (serve tryPlutusServer (server fp))