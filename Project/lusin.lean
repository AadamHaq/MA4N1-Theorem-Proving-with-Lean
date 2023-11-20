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

-- Here we make our definition of the function

variable  {β : Type u} {m : MeasurableSpace X}{μ : Measure X} [MetricSpace ℝ] (f : α → β)






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
Theorem (kinda obvious but may need a bitesize outline here): If K is a compact subset of a set A and f is constant on A, i.e. A = f^-1({a}) for a singleton {a}, then f is constant on K.
-/


/-
Lemma: if f is a measurable function which is disjoint on the sets A and B, with f constant on A and f constant on B, then f is continuous on A ⋃ B.
-/

--theorem disjoint_pair_with_constant_distinct_images_is_continuous_under_image_of_measurable_func {α : Type u_1} {β : Type u_2} {f : α → β} [MeasurableSpace α] [TopologicalSpace α] [MeasurableSpace β] {A : Set α} {B : Set α} (hf : Measurable f) (ha : MeasurableSet A) (hb : MeasurableSet B) (hd : Disjoint A B) (hi : ∀ a ∈ A, f a = 1) :  := by sorry

/-
Alternative to the above: if f : α → β is measurable with a,b ∈ β and a ≠ b, then f⁻¹(a ∨ b) is open.
-/

-- theorem singleton_in_Borel_sigma_algebra [MeasurableSpace ℝ] [TopologicalSpace ℝ] [BorelSpace ℝ] [Singleton a] (a : ℝ) : (MeasurableSet a) := by

-- theorem countable_set_is_measurable [MeasurableSpace ℝ] [TopologicalSpace ℝ] [BorelSpace ℝ] [Preorder ι] [Countable ι] (a : ι → Set ℝ) (hm : ∀ i ∈ ι, MeasurableSet (a i)) : MeasurableSet (⋃ i, a i) := by sorry

theorem countable_set_is_measurable [MeasurableSpace ℝ] [TopologicalSpace ℝ] [BorelSpace ℝ] [Preorder ι] [Countable ι] (a : ι → ℝ)  : MeasurableSet (⋃ i, a i) := by sorry



-- theorem pre_image_of_singletons_is_open {α : Type u_1} {β : Type u_2} {f : α → β} [MeasurableSpace α] [TopologicalSpace α] [MeasurableSpace β] (hf : Measurable f) (B : Set β) (a b : B) (h : a ≠ b) : IsOpen ( f ⁻¹' (a ∨ b) ):= by

theorem pre_image_of_singleton_is_open {α : Type u_1} {f : α → ℝ} [TopologicalSpace α] [BorelSpace α] [BorelSpace ℝ] (hf : Measurable f) (a : ℝ) : IsOpen ( f ⁻¹' ({a})) := by
  refine isOpen_coinduced.mp ?_
  sorry


-- theorem pre_image_of_singletons_is_open {α : Type u_1} {f : α → ℝ} [TopologicalSpace α] [BorelSpace α] [BorelSpace ℝ] (hf : Measurable f) (a b : ℝ) (hd : a ≠ b) : IsOpen ( f ⁻¹' ({a ∪ b}) ):= by sorry



/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, with f constant on each K_i, then f|K (i.e. f restricted to the set K) is continuous.

Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/

-- NOTE: in the below it may be better to use ℕ for sequence indexing rather than preorder/countable ι (that was just the convention that the Egorov proof followed)
theorem measurable_func_constant_on_sets_is_continuous_on_union {α : Type u_1} {β : Type u_2} {c : β} {m1: MeasurableSpace α} {m2: TopologicalSpace α} {m3 : MeasurableSpace β} {f : α → β } {K : ι → set α} [Preorder ι] [Countable ι] (hf : Measurable f) (hcs : ∀ (i : ι), IsCompact (K i)) (hck : f (K i) = c) (hpd: ∀ (i : ι), Pairwise (Disjoint on K)) : (1=2) := by sorry



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
-- this may be related (but not the same!): https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.html#stronglyMeasurable_id



-- Lusin's Theorem!

theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]
theorem LusinonT2LocallyCompactSpace [measure.regular μ]
 ∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by sorry
