{-
    Typechecked using Agda version 2.8.0. No library needed.
-}

module Everything where

-- Classical first-order logic as a GAT
import FirstOrderLogic.Classical.Model
import FirstOrderLogic.Classical.Iterator
import FirstOrderLogic.Classical.Syntax

-- Intuitionistic first-order logic as a GAT
import FirstOrderLogic.IntFull.Model
import FirstOrderLogic.IntFull.Iterator
import FirstOrderLogic.IntFull.Syntax

-- Intuitionistic first-order logic with a split context
-- In this setting we can define the iterator as a IIT 
import FirstOrderLogic.IntFullSplit.Model
import FirstOrderLogic.IntFullSplit.Iterator
import FirstOrderLogic.IntFullSplit.Syntax