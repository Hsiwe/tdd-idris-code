module Main
import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)


data Command : Schema -> Type where 
             SetSchema : (newschema : Schema) -> Command schema
             Add : SchemaType schema -> Command schema
             Get : Integer -> Command schema
             GetAll : Command schema
             Quit : Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
     where
          getQuoted : List Char -> Maybe (String, String)
          getQuoted ('"' :: xs) = case span (/= '"') xs of
                                       (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                                       _ => Nothing
          getQuoted _ = Nothing
          
parsePrefix SInt x = case span isDigit x of
                          ("", rest) => Nothing
                          (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input = getFirst (unpack input)
     where 
          getFirst : List Char -> Maybe (Char, String)
          getFirst (x :: rest) = Just (x, ltrim (pack rest))
          getFirst _ = Nothing

parsePrefix (schemal .+. schemar) input
    = case parsePrefix schemal input of
           Nothing => Nothing
           Just (l_val, input') =>
                case parsePrefix schemar input' of
                     Nothing => Nothing
                     Just (r_val, input'') =>
                          Just ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  (Just (a, b)) => Just a
                                  Nothing => Nothing
                                  Just _ => Nothing


parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs)
     = case xs of
            [] => Just SString
            _ => (case parseSchema xs of
                       Nothing => Just SString
                       (Just x) => Just (SString .+. x))

parseSchema ("Int" :: xs)
     = case xs of
          [] => Just SInt
          _ => (case parseSchema xs of
                     Nothing => Just SInt
                     (Just x) => Just (SInt .+. x))

parseSchema ("Char" :: xs)
     = case xs of
          [] => Just SChar
          _ => (case parseSchema xs of
                     Nothing => Just SChar
                     (Just x) => Just (SChar .+. x))
                     
parseSchema _ = Nothing


parseCommand : (schema : Schema) -> (cmd : String) -> String -> Maybe (Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
                                      Nothing => Nothing
                                      Just restok => Just (Add restok)
parseCommand schema "get" val = case length val of
                                   Z => Just GetAll
                                   _ => case all isDigit (unpack val) of
                                             True => Just (Get (cast val))
                                             False => Nothing
parseCommand schema "schema" rest = case parseSchema (words rest) of
                                         Nothing => Nothing
                                         (Just x) => Just (SetSchema x)
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing


parse : (schema : Schema) -> 
        (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                   (cmd, args) => parseCommand schema cmd (ltrim args)


record DataStore where
     constructor MkData 
     schema : Schema
     size : Nat
     items : Vect size (SchemaType schema)

-- size : DataStore -> Nat
-- size (MkData schema size' items') = size'

-- items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
-- items (MkData schema' size' items') = items'
-- size (MkData size' items') = size'

-- items : (store : DataStore) -> Vect (size store) String
-- items (MkData size' items') = items'

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newItem = MkData schema _ (addToData items)
               where
                    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
                    addToData [] = [newItem]
                    addToData (x :: xs) = x :: addToData xs

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = SChar} item = pack (unpack "" ++ [item])
display {schema = (y .+. z)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                             case integerToFin pos (size store) of
                                   Nothing => Just ("Out of range\n", store)
                                   (Just id) => Just (display (index id (items store)) ++ "\n", store)

getEntries : (store : DataStore) -> (String, DataStore)
getEntries store@(MkData schema size items) = (print_items items 0, store)
                              where 
                                   print_items : Vect n (SchemaType schema) -> Integer -> String
                                   print_items [] index = ""
                                   print_items (x :: xs) index = (show index) ++ ": " ++ display x ++ "\n" ++ (print_items xs (index + 1))

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                         Z => Just (MkData schema _ [])
                         (S k) => Nothing


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                              Nothing => Just ("Invalid command\n", store)
                              (Just (Add x)) => Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
                              (Just (Get x)) => getEntry x store
                              (Just GetAll) => Just (getEntries store)
                              (Just (SetSchema schema')) => (case setSchema store schema' of
                                                                  Nothing => Just ("Can't update schema\n", store)
                                                                  (Just newstore) => Just ("OK\n", newstore))
                              (Just Quit) => Nothing

-- main : IO ()
-- main = replWith (MkData SString _ []) "Command: " processInput

main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ [])
                "Command: " processInput
