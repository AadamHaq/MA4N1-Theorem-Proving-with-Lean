import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

--I added this import - it's used in the Egorov file so we probably need it
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Regular
-- for sequence indexing with τ
import Mathlib.Init.Order.Defs


open Nat Int Real Finset MeasureTheory
open scoped Topology

-- aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- this is slightly more restrictive than the theorem in Cohn's book


namespace MeasureTheory


--Template copied from Egorov
--variable {α β ι : Type*} {m : MeasurableSpace α} [n : MetricSpace β] {μ : Measure α}


class T2LocallyCompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point.
    In a T2 space distinct points are contained within disjoint open sets--/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
  t2 : ∀ (x y : X), x ≠ y → ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v

/- Old definition
class T2LocallyCompactBorelSpace (X : Type*)[TopologicalSpace X] [T2LocallyCompactSpace X] [MeasurableSpace X] : Prop where
  /- The measurable sets are exactly the Borel-measurable sets. -/
  measurable_eq : ‹MeasurableSpace X› = borel X
-/







variable  {X : Type*} [TopologicalSpace X][t : T2LocallyCompactSpace X]

--Checking that properties work as we would expect

theorem IsOpenDoubleUnion  {s₁ : Set X} {s₂ : Set X} [T2LocallyCompactSpace X](h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) :=
by exact IsOpen.union h₁ h₂
theorem IsOpenUnion {s : Set (Set X)}  [T2LocallyCompactSpace X] (h: ∀ p ∈ s, IsOpen p) : IsOpen (⋃₀ s) :=
by exact isOpen_sUnion h

-- there should be no errors above

instance T2LocComp  : MeasurableSpace X :=
 borel X



example[ α : T2LocCompBorel X] [countable β] {f : α →  β}




/--variable {X: Type*} {m : T2LocallyCompactBorelSpace α} [MetricSpace ℝ] {μ : Measure.Regular α}--/


-- pre-image of a measurable set under measurable f is measurable: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html#measurableSet_preimage


/-
Theorem: the pre-image of a **singleton** under f measurable is measurable
-/

-- result from Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSingletonClass

-- e.g. "apply Mathlib.MeasureTheory.MeasurableSpace.Defs.measurableSet_singleton"


/-
Theorem: union of measurable sets is measurable.
-/

-- write mathlib reference here



/-
Theorem: the countable union of compact sets is compact.
-/

-- I think we want to invoke: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#isCompact_iUnion

-- e.g. "apply Mathlib.Topology.Compactness.Compact.isCompact_iUnion"



/-
Proposition 1.2.5 in Cohn's book [continuity of measure]: μ(⋃ A_k) = lim μ(A_k) for an increasing sequence of sets {A_k} with A = ⋃ A_k
-/

-- result from Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpace.html#MeasureTheory.tendsto_measure_iUnion

-- e.g. "apply MeasureTheory.tendsto_measure_iUnion"



/-
Proposition 7.2.6 in Cohn's book [compactness-supremum characterisation of a set under a regular measure]: let X be a Hausdorff space endowed with the Borel σ-algebra B. Let μ be a regular measure on B.
If A ∈ B (and A is σ-finite under μ) then μ(A) = sup{μ(K) : K ⊆ A, K compact}.
-/

-- class of regular functions in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#MeasureTheory.Measure.Regular note that there are definitions of inner regular and outer regular incorporated with this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html



/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, then f is constant on each K_i. Hence, f|K (i.e. f restricted to the set K) continuous.

Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/

--theorem measurable_func_constant_on_sets_is_continuous_on__union [preorder τ] [countable τ] (hcs : compact K)



/- Lusin's Theorem for measurable f which takes **countably many values**. Suppose that f takes countable many values {a_1,...,a_k}. Define A_k = f^-1(a_k) for each k, with A = ⋃ A_k.

Now apply Prop 1.2.5 to show that lim μ(⋃ A_k) = μ(A). Since μ is regular, μ(A) < ∞ and so the measure of A \ ⋃_k^n A_k is arbitrarily small.

We now apply the regularity of μ to apply a similar argument, only this time with compact K = ⋃ K_k for K_k compact.
-/

-- write countable f theorem here



/-
From proof in MA359 notes: the sequence of functions f_n := 2^-n * floor(2^n f) converges uniformly to f.
-/

-- write uniform convergence proof here



/- Lusin's Theorem for f taking **uncountably many values**:
-/

-- write uncountable f theorem here



-- Lusin's Theorem!

theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]
theorem LusinonT2LocallyCompactSpace [measure.regular μ]
 ∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by sorry
