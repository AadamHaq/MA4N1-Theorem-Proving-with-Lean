import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Init.Order.Defs


open Nat Int Real Finset MeasureTheory
open scoped Topology

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's book

namespace MeasureTheory

-- Calling universal variables
-- Will need to review what is needed
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α ][BorelSpace α]{μ : Measure α}
variable [BorelSpace ℝ] (f: α → ℝ) (a : ℕ → ℝ)


--Might not be needed but kept in case
theorem singleton_measurable (a : ℝ) : MeasurableSet ( {a}) := by
  exact MeasurableSet.singleton a
  done

--Proof that a countable union of singletons in the Reals is measurable
theorem countable_union_singleton_measurable  : MeasurableSet (⋃ i, {a i}) := by
  refine MeasurableSet.iUnion ?h
  intro b
  exact singleton_measurable (a b)
  done

--Proof that the pre-image of the above under a function from a measurable space to the Reals is measurable
theorem preimage_union_singleton_measurable (hf : Measurable f) : MeasurableSet (f ⁻¹'(⋃ i, {a i})) := by
  apply MeasurableSet.preimage
  exact countable_union_singleton_measurable a
  exact hf
  done

--We define the following sets on which we will apply continuity of measure.

-- These are the A_k as defined in the notes so A_k is referred to by A a f k 
def A (i : ℕ ) := f ⁻¹'({a i})

-- Check that the Union_A_i is equal to the countable union of A i over N, as we'd expect
theorem f_union_eq_union_f  : f ⁻¹'(⋃ i, {a i}) = ⋃ i, A a f i  := by
 exact Set.preimage_iUnion
 done

-- Next we define the partial union of sets up to k
def Partial_Union_A  (k : ℕ ) := ⋃ i ∈ Set.Iic k , A a f i 
---def Partial_Union (k : ℕ ) := ⋃ i ∈ Set.Iic k , {a i}


--Next goal is to show that B is an increasing sequence of sets (MIGHT NOT BE NEEDED)
/-
theorem Partial_Union_increasing (x y : ℕ) (hf : x ≤ y): (⋃ i ∈ Set.Iic x, f ⁻¹'({a i})) ⊆ (⋃ i ∈ Set.Iic y, f ⁻¹'({a i})) := by 
 sorry
-/


theorem partial_union_increasing: Monotone (Partial_Union_A a f) := by
unfold Partial_Union_A
unfold Monotone
intro x y
sorry 

theorem continuity_of_measure (ε : ENNReal) : ∃ N : ℕ, μ ((⋃ i, f ⁻¹'{a i}) \ f ⁻¹' (⋃ i ∈ Set.Icc 1 N, {a i})) < ε/2 := by
  simp only [ge_iff_le, not_le, lt_one_iff, gt_iff_lt, Set.mem_Icc, Set.preimage_iUnion]
  -- Aadam is working on this proof!
  sorry

--The two below are useful
/-
theorem tendsto_measure_iUnions [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι]
    {s : ι → Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  rw [measure_iUnion_eq_iSup hm.directed_le]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Union MeasureTheory.tendsto_measure_iUnion

def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
#align monotone Monotone
-/


/-
Next step: μ(A_n \ K_n) < ε/2n, where the A_k are defined as the pre-images of the {a_k} under f, and the K_k are compact subsets of the A_k.

The N : ℕ given as a hypothesis below should is provided as a result from the continuity_of_measure theorem above.
-/
-- Theorem 2 of 3 for μ(A \ K) for countable f
theorem compact_subsets_from_regular_measure (n : ℕ) (K : ℕ → Set α) : ∀ i ∈ Set.Icc 1 n, ∃ i, IsCompact (K i) ∧ K i ⊂ f ⁻¹'{a i} ∧ μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n) := by sorry


/-
Final step involving A = ⋃ A_i, we now claim that the measure of A \ K is less than ε.
-/
-- Theorem 3 of 3 for μ(A \ K) < ε for countable f
-- NEED TO FIX ISSUE WITH INDEX i
theorem lusin_for_countable_f (n : ℕ) (K : ℕ → Set α) (hck : ∀ i ∈ Set.Icc 1 n, IsCompact (K i)) (hc : ∀ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i}) (hε : μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n)) : μ (⋃ i, f ⁻¹'{a i} \ ⋃ i, K i) < ε := by sorry


/-
Proposition 1.2.5 in Cohn's book [continuity of measure]: μ(⋃ A_k) = lim μ(A_k) for an increasing sequence of sets {A_k} with A = ⋃ A_k
-/

-- result from Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpace.html#MeasureTheory.tendsto_measure_iUnion

-- e.g. "apply MeasureTheory.tendsto_measure_iUnion"

-- monotonicity needed https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Monotone/Basic.html#Monotone

/-
Proposition 7.2.6 in Cohn's book [compactness-supremum characterisation of a set under a regular measure]: let X be a Hausdorff space endowed with the Borel σ-algebra B. Let μ be a regular measure on B.
If A ∈ B (and A is σ-finite under μ) then μ(A) = sup{μ(K) : K ⊆ A, K compact}.
-/



-- class of regular functions in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#MeasureTheory.Measure.Regular note that there are definitions of inner regular and outer regular incorporated with this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html

/-
Theorem: the countable union of compact sets is compact.
-/

-- I think we want to invoke: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#isCompact_iUnion

-- e.g. "apply Mathlib.Topology.Compactness.Compact.isCompact_iUnion"



/-
Theorem (kinda obvious but may need a bitesize outline here): If K is a compact subset of a set A and f is constant on A, i.e. A = f^-1({a}) for a singleton {a}, then f is constant on K.
-/

theorem preimage_of_const_func_on_compact_subset_is_constant (K : Set α) (a : ℝ) (hk : IsCompact K) (hs : K ⊂ f ⁻¹' ({a} : Set ℝ)) : (∀ x ∈ K, f x = a) := by sorry



/-
Lemma: if f is a measurable function which is disjoint on the sets A and B, with f constant on A and f constant on B, then f is continuous on A ⋃ B.
-/

lemma meas_func_const_on_disjoint_pair_is_continuous (A B : Set α) (a b : ℝ) (hf : Measurable f) (ha : ∀ x : A, f x = a) (hb : ∀ x : B, f x = b) (hac : IsCompact A) (hbc : IsCompact B) (hd : A ∩ B = ∅) : ContinuousOn f (A∪B) := by sorry

--theorem disjoint_pair_with_constant_distinct_images_is_continuous_under_image_of_measurable_func {α : Type u_1} {β : Type u_2} {f : α → β} [MeasurableSpace α] [TopologicalSpace α] [MeasurableSpace β] {A : Set α} {B : Set α} (hf : Measurable f) (ha : MeasurableSet A) (hb : MeasurableSet B) (hd : Disjoint A B) (hi : ∀ a ∈ A, f a = 1) :  := by sorry




/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, then f is constant on each K_i. Hence, f|K (i.e. f restricted to the set K) continuous.


Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/

theorem meas_func_const_on_disjoint_finite_union_is_continuous (n : ℕ) (K : ℕ → Set α) (hpd: ∀ i ∈ Set.Icc 1 n, Pairwise (Disjoint on K i)) : ContinuousOn f (⋃ i ∈ Set.Icc 1 n, K i) := by sorry

--theorem measurable_func_constant_on_sets_is_continuous_on__union [preorder τ] [countable τ] (hcs : compact K)

-- NOTE: in the below it may be better to use ℕ for sequence indexing rather than preorder/countable ι (that was just the convention that the Egorov proof followed)
-- theorem measurable_func_constant_on_sets_is_continuous_on_union {α : Type u_1} {β : Type u_2} {c : β} {m1: MeasurableSpace α} {m2: TopologicalSpace α} {m3 : MeasurableSpace β} {f : α → β } {K : ι → set α} [Preorder ι] [Countable ι] (hf : Measurable f) (hcs : ∀ (i : ι), IsCompact (K i)) (hck : f (K i) = c) (hpd: ∀ (i : ι), Pairwise (Disjoint on K)) : (1=2) := by sorry

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
