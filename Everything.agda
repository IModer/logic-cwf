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

-- Negative fragment of Intuitionistic first-order logic with a split context
import FirstOrderLogic.IntNegative.Model
import FirstOrderLogic.IntNegative.Iterator
import FirstOrderLogic.IntNegative.Syntax

-- Models and Beth completeness
import FirstOrderLogic.IntFullSplit.KripkeModel
import FirstOrderLogic.IntFullSplit.BethModel
import FirstOrderLogic.IntFullSplit.BethCompleteness

import FirstOrderLogic.IntNegative.KripkeModel

-- Double-negation translation between IntFull and Classical
import FirstOrderLogic.DoubleNegationTranslation

-- Propositional logic

-- Full Intuitionistic
import PropositionalLogic.IntFull.Model
import PropositionalLogic.IntFull.Iterator
import PropositionalLogic.IntFull.Syntax

-- Models and Beth completeness
import PropositionalLogic.IntFull.TarskiModel
import PropositionalLogic.IntFull.FamModel
import PropositionalLogic.IntFull.BoolModel
import PropositionalLogic.IntFull.KripkeModel
import PropositionalLogic.IntFull.BethModel

import PropositionalLogic.IntFull.Examples

-- Negative Intuitionistic
import PropositionalLogic.IntNegative.Model
import PropositionalLogic.IntNegative.Iterator
import PropositionalLogic.IntNegative.Syntax

-- Models and Kripke completeness
import PropositionalLogic.IntNegative.KripkeModel

-- Full Classical
import PropositionalLogic.Classical.Model
import PropositionalLogic.Classical.Iterator
import PropositionalLogic.Classical.Syntax
import PropositionalLogic.Classical.BoolModel