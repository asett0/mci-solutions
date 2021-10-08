module Chap1

import Data.Vect

Id : Type
Id = String 

data Binop = Plus | Minus | Times | Div

Table : Type
Table = List (Id, Int)

mutual
    data Exp = IdExp Id | NumExp Int | OpExp Exp Binop Exp | EseqExp Stm Exp
    data Stm = CompoundStm Stm Stm | AssignStm Id Exp | PrintStm (Vect (S n) Exp) 

update : Id -> Int -> Table -> Table
update c v t = (c, v) :: t 

lookup : Id -> Table -> Maybe Int
lookup c [] = Nothing
lookup c ((c', v) :: t) = if c == c' then Just v else lookup c t

mutual
    maxArgs : Stm -> Int
    maxArgs (CompoundStm stm stm') = max (maxArgs stm) (maxArgs stm')
    maxArgs (AssignStm id exp) = maxArgsHelper exp
    maxArgs (PrintStm expList) = max (cast $ length expList) (foldl1 max $ map maxArgsHelper expList)

    maxArgsHelper : Exp -> Int
    maxArgsHelper (OpExp exp _ exp') = max (maxArgsHelper exp) (maxArgsHelper exp')
    maxArgsHelper (EseqExp stm exp) = max (maxArgs stm) (maxArgsHelper exp)
    maxArgsHelper _ = 0

interp : Stm -> IO ()
-- interp

mutual
    interpStm : Stm -> Table -> IO (Table)
    interpStm (CompoundStm stm stm') t = do 
        t' <- interpStm stm t
        interpStm stm t'
    interpStm (AssignStm id exp) t = do 
        (v, t') <- interpExp exp t
        pure (update id v t')
    interpStm (PrintStm [exp]) t = do
        (v, t') <- interpExp exp t
        printLn v
        pure t'
    interpStm (PrintStm (exp::exp'::expList)) t = do
        (v, t') <- interpExp exp t
        print v
        print ' '
        interpStm (PrintStm (exp'::expList)) t'
    
    interpExp : Exp -> Table -> IO (Int, Table)
    interpExp (IdExp id) t = case lookup id t of
        Nothing => print ("Error! ") 



prog : Stm
prog = CompoundStm 
    (AssignStm 
        "a" 
        (OpExp (NumExp 5) Plus (NumExp 3))
    ) 
    (CompoundStm 
        (AssignStm 
            "b" 
            (EseqExp 
                (PrintStm [IdExp " a" , OpExp (IdExp "a") Minus (NumExp 1) ]) 
                (OpExp (NumExp 10) Times (IdExp"a"))
            )
        ) 
        (PrintStm [IdExp "b"])
    )

Key : Type
Key = String

data Tree = Leaf | Node Tree Key Tree

empty : Tree
empty = Leaf

insert : Key -> Tree -> Tree
insert key Leaf = Node Leaf key Leaf
insert key (Node l k r) = case compare key k of
    LT => Node (insert key l) k r
    EQ => Node l k r
    GT => Node l k (insert key r)

member : Key -> Tree -> Bool