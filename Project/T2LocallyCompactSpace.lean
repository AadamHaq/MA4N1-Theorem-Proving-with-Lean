import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- For regular measure
import Mathlib.MeasureTheory.Measure.Regular



open Nat Int Real Finset MeasureTheory
open scoped Topology

-- namespace MeasureTheory

variable {α β ι : Type*} {m : MeasurableSpace α} [n : MetricSpace β] {μ : Measure α}

-- aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- this is slightly more restrictive than the theorem in Cohn's book

class T2LocallyCompactSpace (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] : Prop
    where

instance (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] :
    T2LocallyCompactSpace α := {}

def T2LocallyCompactSpaceBorel (T2LocallyCompactSpace α) (m : MeasurableSpace α) :=
BorelSpace X

/-
We are using the following BorelSpace class definition, given below.
Namely, this tells us that the measurable sets are exactly the Borel-measurable sets.

class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
    measurable_eq : ‹MeasurableSpace α› = borel α
-/

/-
Theorem: the pre-image of a singleton under f measurable is measurable
-/

-- write theorem here

/-
Theorem: the countable union of compact sets is compact.
-/

-- write theorem here

/-
Proposition 1.2.5 in Cohn's book [Continuity of Measure]: μ(⋃ A_k) = lim μ(A_k) for an increasing sequence of sets {A_k} with A = ⋃ A_k
-/

-- write proposition here

/- Lusin's Theorem for measurable f which takes **countably many values**. Suppose that f takes countable many values {a_1,...,a_k}. Define A_k = f^-1(a_k) for each k, with A = ⋃ A_k.

Now apply Prop 1.2.5 to show that lim μ(⋃ A_k) = μ(A). Since μ is regular, μ(A) < ∞ and so the measure of A \ ⋃_k^n A_k is arbitrarily small.

We now apply the regularity of μ to apply a similar argument, only this time with compact K = ⋃ K_k for K_k compact.
-/

-- write countable f theorem here


-- Lusin's Theorem!
theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]

#check Field

#synth T2Space ℝ
#synth LocallyCompactSpace ℝ
#synth TopologicalSpace ℝ
#synth T2LocallyCompactSpace ℝ
