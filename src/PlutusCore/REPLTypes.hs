{-# OPTIONS -Wall #-}





module PlutusCore.REPLTypes where





data REPLCommand = Empty              -- all whitespace
                 | Quit               -- :q :quit
                 | Reload             -- :r :reload
                 | EvalPrefix String  -- :p :prefixEvaluate
                 | GetType String     -- :t :type
                 | GetInfo String     -- :i :info
                 | FindName String    -- :f :find
                 | Invalid String     -- :X for any other X
                 | Eval String        -- anything not of the form :X
                 