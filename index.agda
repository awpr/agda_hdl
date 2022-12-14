{-# OPTIONS --sized-types #-}

module index where

-- Hacky standin for a build system / test suite: a single top module
-- that transitively imports everything, so Agda can check it all in
-- one go.
--
-- Everything below this comment header is generated by gen-index.sh
-- according to what's tracked by Git, and will be overwritten without
-- warning.
--
-- This line is a mArKeR to delimit the generated portion.

import Categories
import Categories.Adjunction
import Categories.Bicartesian
import Categories.BicartesianClosed
import Categories.Bifunctor
import Categories.Braided
import Categories.Cartesian
import Categories.CartesianClosed
import Categories.Category
import Categories.Category.Functors
import Categories.Category.Setoids
import Categories.Category.Types
import Categories.CausalLoop
import Categories.ClosedMonoidal
import Categories.Coalgebra
import Categories.Constructions.Core
import Categories.Constructions.FullImage
import Categories.Constructions.Opposite
import Categories.Constructions.Product
import Categories.Coproducts
import Categories.Distributive
import Categories.Functor
import Categories.Functor.Monoidal
import Categories.Gel.Bicartesian
import Categories.Gel.BicartesianClosed
import Categories.Gel.Bool
import Categories.Gel.Cartesian
import Categories.Gel.CartesianClosed
import Categories.Gel.CausalLoop
import Categories.Gel.Coproducts
import Categories.Gel.Distributive
import Categories.Gel.Maybe
import Categories.Gel.Product
import Categories.Gel.Sum
import Categories.Gel.Vec
import Categories.Inverse
import Categories.Monoidal
import Categories.NaturalTransformation
import Categories.PolyQuiver
import Categories.Symmetric
import Categories.Syntax.Cartesian
import Categories.Syntax.Cartesian.Core
import Categories.Syntax.Cartesian.Functors
import Categories.Terminal
import Circuits.Binary
import Circuits.Bit
import Circuits.Compressor
import Circuits.Counter
import Circuits.Registers
import Circuits.Sandbox
import Data.Bit
import Data.Bit.Properties
import Data.Finite
import Experiments.ANF
import Experiments.Binary
import Experiments.BinaryIndexed
import Experiments.BinaryPositive
import Experiments.CatSyn
import Experiments.FixedBinary
import Experiments.Free
import Experiments.Gate
import Experiments.Monad
import Experiments.NetPHOAS
import Experiments.Signatures.Unityped
import Experiments.Signatures.Verilog
import Instances
import Mealy
import Relation.Binary.PropositionalEquality.Extras
import Relation.Binary.PropositionalEquality.Properties.Extras
import Tactic.Exhaustion
