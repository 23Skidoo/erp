module Erp
   where

data ErpAst = Var String | Abs
              deriving (Eq, Show)

data ErpType = ErpString | ErpFunc ErpType ErpType
               deriving (Eq, Show)

data ErpValue = ErpValString | ErpValFun ErpAst
                deriving (Eq, Show)

erp_typecheck :: ErpAst -> ErpType
erp_typecheck = undefined

erp_interpret :: ErpAst -> ErpValue
erp_interpret = undefined
