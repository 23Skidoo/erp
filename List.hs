module List
    where

import Control.Monad

type OwnerRecord = (String, Int)
type OwnerTable = [OwnerRecord]
type AccountRecord = (Int, Int)
type AccountTable = [AccountRecord]

owners :: OwnerTable
owners = [("name1", 123), ("name2", 456), ("name3", 789)]

accounts :: AccountTable
accounts = [(123, 23), (456, 56), (789, 100)]

type QueryResult = [(String, Int)]

sugaredQuery :: QueryResult
sugaredQuery = [(name, amount) | (name, accountnr) <- owners,
                (accountnr', amount) <- accounts,
                accountnr == accountnr']

doQuery :: QueryResult
doQuery = do (name, accountnr) <- owners
             (accountnr', amount) <- accounts
             guard (accountnr == accountnr')
             return (name, amount)

almostDesugaredQuery :: QueryResult
almostDesugaredQuery = concatMap (\(name, accountnr) ->
                                concatMap (\(accountnr', amount) ->
                                               do guard (accountnr == accountnr')
                                                  return (name, amount)
                                          ) accounts
                           ) owners

desugaredQuery :: QueryResult
desugaredQuery = concatMap (\(name, accountnr) ->
                                concatMap (\(accountnr', amount) ->
                                               if accountnr == accountnr'
                                               then [(name, amount)]
                                               else []
                                          ) accounts
                           ) owners


check :: Bool
check = (sugaredQuery == doQuery) == (almostDesugaredQuery == desugaredQuery)

main :: IO ()
main = do if check
              then putStrLn "OK"
              else fail "FAIL"
