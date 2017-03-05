import Data.Maybe
import Data.List

type AttName = String

type AttValue = String

type Attribute = (AttName, [AttValue])

type Header = [Attribute]

type Row = [AttValue]

type DataSet = (Header, [Row])

data DecisionTree = Null |
                    Leaf AttValue | 
                    Node AttName [(AttValue, DecisionTree)]
                  deriving (Eq, Show)

type Partition = [(AttValue, DataSet)]

type AttSelector = DataSet -> Attribute -> Attribute

xlogx :: Double -> Double
xlogx p
  | p <= 1e-100 = 0.0
  | otherwise   = p * log2 p 
  where
    log2 x = log x / log 2

lookUp :: (Eq a, Show a, Show b) => a -> [(a, b)] -> b
lookUp x table
  = fromMaybe (error ("lookUp error - no binding for " ++ show x ++ 
                      " in table: " ++ show table))
              (lookup x table)

--------------------------------------------------------------------
-- PART I (START 16.21, FINISH 16.59 - 38 minutes)
--------------------------------------------------------------------

-- Note less than equal to to handle the zero case
allSame :: Eq a => [a] -> Bool
allSame xs 
  = length (nub xs) <= 1

remove :: Eq a => a -> [(a, b)] -> [(a, b)]
remove key entries
  = filter (otherKey) entries
  where 
    otherKey entry = fst entry /= key

getHeaderRowPairs :: Header -> Row -> [(AttName, AttValue)]
--Helper associating table names with elements in a row
getHeaderRowPairs header row
  = zip (map fst header) row

lookUpAtt :: AttName -> Header -> Row -> AttValue
--Pre: The attribute name is present in the given header.
lookUpAtt attribute header row
  = lookUp attribute (getHeaderRowPairs header row)

removeAtt :: AttName -> Header -> Row -> Row
--Note: This is safe, because remove maintains ordering as well
removeAtt attribute header row
  = map snd (remove attribute (getHeaderRowPairs header row))

addToMapping :: Eq a => (a, b) -> [(a, [b])] -> [(a, [b])]
addToMapping (key, value) [] 
  = [(key, [value])]
addToMapping (key, value) (currEntry : entries)
  | key == fst currEntry = (add value currEntry) : entries
  | otherwise            = [currEntry] ++ addToMapping (key, value) entries
  where
    add value (entryKey, entryValues) = (entryKey, value : entryValues)

buildFrequencyTable :: Attribute -> DataSet -> [(AttValue, Int)]
--Pre: Each row of the data set contains an instance of the attribute
buildFrequencyTable attribute dataset
  = map takeCounts (partitionOnAtt attribute dataset)
  where
    takeCounts (key, values) = (key, length values)

partitionOnAtt :: Attribute -> DataSet -> [(AttValue, [Row])]
--Partitions the dataset into rows on a given attribute
partitionOnAtt attribute dataset
  = partitionOnAttAccumulator attribute dataset (initializeAccumulator attribute)
  where
    initializeAccumulator attribute = zip (snd attribute) (repeat [])

partitionOnAttAccumulator :: Attribute -> DataSet -> [(AttValue, [Row])] -> [(AttValue, [Row])]
--Internal recursive method for partitionOnAtt
partitionOnAttAccumulator _ (_, []) accumulator
  = accumulator
partitionOnAttAccumulator attribute (header, row : rows) accumulator
  = partitionOnAttAccumulator attribute (header, rows) newAccumulator
  where
    newAccumulator = addToMapping (constructKey attribute header row) accumulator
    constructKey attribute header row = (lookUpAtt (fst attribute) header row, row)

--------------------------------------------------------------------
-- PART II (START 16.59, FINISH 17.14 - 15 minutes)
--------------------------------------------------------------------

nodes :: DecisionTree -> Int
nodes Null
  = 0
nodes (Leaf _)
  = 1
nodes (Node _ classifications)
  = 1 + foldl1 (+) (map (nodes . snd) classifications)

evalTree :: DecisionTree -> Header -> Row -> AttValue
evalTree Null _ _
  = ""
evalTree (Leaf value) _ _
  = value
evalTree (Node attribute classifications) header row
  = evalTree (findSubtree attribute classifications header row) header row
  where
    findSubtree attribute classifications header row
      = (snd . head) $ filter (\entry -> fst entry == lookUpAtt attribute header row) classifications

--------------------------------------------------------------------
-- PART III
--------------------------------------------------------------------

--
-- Given...
-- In this simple case, the attribute selected is the first input attribute 
-- in the header. Note that the classifier attribute may appear in any column,
-- so we must exclude it as a candidate.
--
nextAtt :: AttSelector
--Pre: The header contains at least one input attribute
nextAtt (header, _) (classifierName, _)
  = head (filter ((/= classifierName) . fst) header)

partitionData :: DataSet -> Attribute -> Partition
partitionData 
  = undefined

buildTree :: DataSet -> Attribute -> AttSelector -> DecisionTree 
buildTree 
  = undefined

--------------------------------------------------------------------
-- PART IV
--------------------------------------------------------------------

entropy :: DataSet -> Attribute -> Double
entropy 
  = undefined

gain :: DataSet -> Attribute -> Attribute -> Double
gain 
  = undefined

bestGainAtt :: AttSelector
bestGainAtt 
  = undefined

--------------------------------------------------------------------

outlook :: Attribute
outlook 
  = ("outlook", ["sunny", "overcast", "rainy"])

temp :: Attribute 
temp 
  = ("temp", ["hot", "mild", "cool"])

humidity :: Attribute 
humidity 
  = ("humidity", ["high", "normal"])

wind :: Attribute 
wind 
  = ("wind", ["windy", "calm"])

result :: Attribute 
result
  = ("result", ["good", "bad"])

fishingData :: DataSet
fishingData
  = (header, table)

header :: Header
table  :: [Row]
header 
  =  [outlook,    temp,   humidity, wind,    result] 
table 
  = [["sunny",    "hot",  "high",   "calm",  "bad" ],
     ["sunny",    "hot",  "high",   "windy", "bad" ],
     ["overcast", "hot",  "high",   "calm",  "good"],
     ["rainy",    "mild", "high",   "calm",  "good"],
     ["rainy",    "cool", "normal", "calm",  "good"],
     ["rainy",    "cool", "normal", "windy", "bad" ],
     ["overcast", "cool", "normal", "windy", "good"],
     ["sunny",    "mild", "high",   "calm",  "bad" ],
     ["sunny",    "cool", "normal", "calm",  "good"],
     ["rainy",    "mild", "normal", "calm",  "good"],
     ["sunny",    "mild", "normal", "windy", "good"],
     ["overcast", "mild", "high",   "windy", "good"],
     ["overcast", "hot",  "normal", "calm",  "good"],
     ["rainy",    "mild", "high",   "windy", "bad" ]]

--
-- This is the same as the above table, but with the result in the second 
-- column...
--
fishingData' :: DataSet
fishingData'
  = (header', table')

header' :: Header
table'  :: [Row]
header' 
  =  [outlook,    result, temp,   humidity, wind] 
table' 
  = [["sunny",    "bad",  "hot",  "high",   "calm"],
     ["sunny",    "bad",  "hot",  "high",   "windy"],
     ["overcast", "good", "hot",  "high",   "calm"],
     ["rainy",    "good", "mild", "high",   "calm"],
     ["rainy",    "good", "cool", "normal", "calm"],
     ["rainy",    "bad",  "cool", "normal", "windy"],
     ["overcast", "good", "cool", "normal", "windy"],
     ["sunny",    "bad",  "mild", "high",   "calm"],
     ["sunny",    "good", "cool", "normal", "calm"],
     ["rainy",    "good", "mild", "normal", "calm"],
     ["sunny",    "good", "mild", "normal", "windy"],
     ["overcast", "good", "mild", "high",   "windy"],
     ["overcast", "good", "hot",  "normal", "calm"],
     ["rainy",    "bad",  "mild", "high",   "windy"]]

fig1 :: DecisionTree
fig1
  = Node "outlook" 
         [("sunny", Node "temp" 
                         [("hot", Leaf "bad"),
                          ("mild",Node "humidity" 
                                       [("high",   Leaf "bad"),
                                        ("normal", Leaf "good")]),
                          ("cool", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "temp" 
                         [("hot", Null),
                          ("mild", Node "humidity" 
                                        [("high",Node "wind" 
                                                      [("windy",  Leaf "bad"),
                                                       ("calm", Leaf "good")]),
                                         ("normal", Leaf "good")]),
                          ("cool", Node "humidity" 
                                        [("high", Null),
                                         ("normal", Node "wind" 
                                                         [("windy",  Leaf "bad"),
                                                          ("calm", Leaf "good")])])])]

fig2 :: DecisionTree
fig2
  = Node "outlook" 
         [("sunny", Node "humidity" 
                         [("high", Leaf "bad"),
                          ("normal", Leaf "good")]),
          ("overcast", Leaf "good"),
          ("rainy", Node "wind" 
                         [("windy", Leaf "bad"),
                          ("calm", Leaf "good")])]


outlookPartition :: Partition
outlookPartition
  = [("sunny",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","bad"],["hot","high","windy","bad"],
                   ["mild","high","calm","bad"],["cool","normal","calm","good"],
                   ["mild","normal","windy","good"]])),
     ("overcast",([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["hot","high","calm","good"],["cool","normal","windy","good"],
                   ["mild","high","windy","good"],["hot","normal","calm","good"]])),
     ("rainy",   ([("temp",["hot","mild","cool"]),("humidity",["high","normal"]),
                   ("wind",["windy","calm"]),("result",["good","bad"])],
                  [["mild","high","calm","good"],["cool","normal","calm","good"],
                   ["cool","normal","windy","bad"],["mild","normal","calm","good"],
                   ["mild","high","windy","bad"]]))]
