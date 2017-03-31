/*

data TermF r
  = Decname (Sourced String) [Type]
  | Let r r
  | Lam Type r
  | App r r
  | Con String [r]
  | Case [r] [ClauseF r]
  | Success r
  | Failure Type
  | Bind r r
  | PrimData PrimData
  | Builtin String [r]
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "Decname",
           "Let",
           "Lam",
           "App",
           "Con",
           "Case",
           "Success",
           "Failure",
           "Bind",
           "PrimData",
           "Builtin" );





/*

data PrimData = PrimInt Int
              | PrimFloat Float
              | PrimByteString BS.ByteString
  deriving (Eq,Generic)

*/

Data.Alts( "PrimInt",
           "PrimFloat",
           "PrimByteString" );





/*

data ClauseF r = Clause [Scope PatternF] r
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "Clause" );





/*

data PatternF r = ConPat String [r]
                | PrimPat PrimData
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "VarPat",
           "ConPat",
           "PrimPat" );



function prettyPrintTerm(tm) {
  return cases(tm, {
    
    Decname: function (n) {
      return n;
    },
    
    Let: function (m,sc) {
      return "let(" +
               prettyPrintTerm(m) +
               "; " +
               prettyPrintTermScope(sc) +
               ")";
    },
    
    Lam: function (sc) {
      return "λ(" +
               prettyPrintTermScope(sc) +
               ")";
    },
    
    App: function (f,x) {
      return "apply(" +
               prettyPrintTerm(f) +
               ";" +
               prettyPrintTerm(x) +
               ")";
    },
    
    Con: function (c,ms) {
      return c +
               "(" +
               ms.map(m => prettyPrintTerm(m)).join(",") +
               ")";
    },
    
    Case: function (ms, cls) {
      return "case(" +
               ms.map(m => prettyPrintTerm(m)).join(",") +
               "; " +
               cls.map(cl => prettyPrintClause(cl)).join(",") +
               ")"
    },
    
    Success: function (m) {
      return "success(" + prettyPrintTerm(m) + ")";
    },
    
    Failure: function () {
      return "failure";
    },
    
    Bind: function (m,sc) {
      return "bind(" +
               prettyPrintTerm(m) +
               "; " +
               prettyPrintTermScope(sc) +
               ")";
    },
    
    PrimData: function (pd) {
      return pd.args[0].toString();
    },
    
    Builtin: function (n,ms) {
      console.log(ms);
      return "builtin[" +
               n +
               "](" +
               ms.map(m => prettyPrintTerm(m)).join(",") +
               ")";
    },
    
    otherwise: function () {
      return show(tm);
    }
    
  });
}

function prettyPrintTermScope(sc) {
    let names = sc.toString().match(/^\(([^\)]*)\)/)[1].split(",");
    let vars = names.map(x => ({ variable: true, name: x }));
    return names.join(",") + "." + prettyPrintTerm(sc.apply(null, vars));
}

function prettyPrintClause(cl) {
  return cases(cl, {
    Clause: function (pats, sc) {
      return "cl(" +
               pats.map(pat => prettyPrintPattern(pat)).join(",") +
               "; " +
               prettyPrintTermScope(sc) +
               ")";
    }
  })
}

function prettyPrintPattern(pat) {
  return cases(pat, {
    ConPat: function (n,ps) {
      return n +
               "(" +
               ps.map(p => prettyPrintPattern(p)).join(",") +
               ")";
    },
    
    Var: function () {
      return "_"
    }
  });
}