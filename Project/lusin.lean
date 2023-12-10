import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Init.Order.Defs
import Mathlib.Order.PartialSups
import Mathlib.Order.Filter.AtTopBot

import Mathlib.Order.Filter.Basic

open Nat Int Real Finset MeasureTheory ENNReal Filter
open scoped Topology

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's book

namespace MeasureTheory

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α ][BorelSpace α]{μ : Measure α}[Measure.Regular μ]
variable [BorelSpace ℝ] (f: α → ℝ) (a : ℕ → ℝ) (h: Measurable f)
variable (B : Set α)(hm : MeasurableSet B)(hf : μ B < T)(hcount : f '' B = Set.range a)
variable (ε : NNReal )(hε : 0 < ε)

--Might not be needed but kept in case
theorem pre_im_singleton_measurable (i : ℕ ) : MeasurableSet (f ⁻¹'({a i})) := by
  apply MeasurableSet.preimage
  exact MeasurableSet.singleton (a i)
  exact h
  done

-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus ⋃ i A_i = B which is proven here

theorem B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[(Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i}))).symm]
  rw[(Set.preimage_iUnion).symm]
  rw[(Set.range_eq_iUnion a).symm]
  rw[hcount.symm]
  simp
  simp_rw[Set.subset_preimage_image f B]
  done

/-
We will be applying continuity of measure to show that the measure of the partial unions of these sets
converges up to the measure of Aa. Below we prove that the partial unions are an increasing sequence of
measurable sets, the hypothesis of continuity of measure.
-/
theorem measurable_A: (MeasurableSet (A f a B i)) := by
  unfold A
  apply MeasurableSet.inter
  apply pre_im_singleton_measurable
  apply h
  exact hm
  done

-- Next we show that the partial union of sets up to k is measurable
theorem partial_union_A_measurable (k : ℕ): MeasurableSet (⋃ i ∈ Set.Iic k , A f a B i )  := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic k
  intro b
  exact fun _ => measurable_A f a h B hm
  done

--Next goal is to show that the sequence of partial unions is increasing
--The Monotone theorem works, but it requires "partial_union_increasing" which is sorried out.
--mwe is basically the same as partial_union_increasing I just simplified the statement as much as possible

theorem mwe (s: ℕ → Set α)(n k : ℕ)(hk: n ≤ k ): s n ⊆ ⋃ i, ⋃ (_ : i ≤ k), s i := by
  exact Set.subset_biUnion_of_mem hk
  done

theorem partial_union_increasing (x y : ℕ) (h : x ≤ y): ⋃ i ∈ Set.Iic x, A f a B i  ≤ ⋃ i ∈ Set.Iic y, A f a B i  := by
  simp
  intro j hj
  have hy := hj.trans h
  apply mwe (A f a B) j y hy
  done

theorem monotone_A: Monotone (fun k => ⋃ i ∈ Set.Iic k , A f a B i) := by
  unfold Monotone
  intro x y
  apply partial_union_increasing
  done

theorem mwe_2 (s: ℕ → Set α) (i : ℕ): s i ⊆
⋃ j ∈ Set.Iic i , s j  := by
  apply mwe
  rfl
  done

/-We need a result which says that the union of partial unions is just the union.
This together with B_eq_Union_Ai will give us convergence up to μ(B) when we apply
continuity of measure. -/

theorem union_partial_eq_union (s: ℕ → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j ∈ Set.Iic i , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp
  intro t
  have hj := mwe_2 s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x => ⋃ (j : ℕ) (_ : j ∈ Set.Iic x), s j ) t
  done

theorem union_partial_A_eq_B: ⋃ k,  ⋃ i ∈ Set.Iic k , A f a B i = B := by
  rw[(union_partial_eq_union (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hcount
  done

theorem continuity_of_measure: Tendsto (↑↑μ ∘ (fun k ↦ ⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_A_eq_B f a B]
  simp
  apply tendsto_measure_iUnion
  apply monotone_A
  exact hcount
  done

theorem epsilon_tendsto (s : ℕ → ℝ) (x : ℝ) : Tendsto s atTop (𝓝 x) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, s n ∈ Set.Ioo (x - ε) (x + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Set.Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x)]
  simp
  done

theorem epsilon_definition (s : ℕ → ℝ) (x : ℝ) (hh : Tendsto s atTop (𝓝 x)) : ∃ N, ∀ n ≥ N,  x - ε < s n ∧ s n < x + ε   := by
  rw[epsilon_tendsto] at hh
  simp at hh
  simp
  apply hh
  exact hε
  done

---This result just weakens epsilon_definition just to get the left inequality
theorem epsilon_definition_left (s : ℕ → ℝ) (x : ℝ) (hh : Tendsto s atTop (𝓝 x)) : ∃ N, ∀ n ≥ N,  x - ε < s n   := by
  have hj :=  epsilon_definition ε hε s x hh
  choose h1 h2 h3 using hj
  aesop
  done

---We now want to weaken the result further going from ∃ N, ∀ n ≥ N, to just ∃ N
---For this we need

theorem existence (x : ℝ) (s: ℕ → ℝ)(hh: ∃ N, ∀ n ≥ N,  x - ε  < s n  ) : ( ∃ m,  x - ε < s m ) := by
  rcases hh with ⟨ N, hN⟩
  exact ⟨ N, hN _ le_rfl⟩
  done

theorem epsilon_definition_fixed_N (s : ℕ → ℝ) (x : ℝ) (hh : Tendsto s atTop (𝓝 x)) : ∃ N,  x - ε < s N   := by
  have hj :=  epsilon_definition_left ε hε s x hh
  exact existence  ε x s hj


theorem epsilon_definition_WANT  (s : ℕ → ENNReal) (x : ENNReal) (hx : x < T) (hh : Tendsto s atTop (𝓝 x)) : ∃ N,  x - ε < s N  := by
  sorry

theorem mwe_3 (s b: ENNReal)(e: NNReal) (h : b - e < s) : (b < s + e)  := by
---rw[lt_sub_iff_add_lt b s e] at h
---exact sub_lt_iff_lt_add.mp h
---exact lt_add_of_tsub_lt_right h
--ENNReal making this a pain to prove

  sorry


theorem mwe_4 (b : ENNReal ) (s: ℕ → ENNReal) (ht : ∃ N, b - ε < s N) :  (∃ N, b < s N + ε ) :=
by
  let ⟨n, Hn⟩ := ht
  have hm := mwe_3 (s n) b ε Hn
  aesop
  done




theorem difference_le_epsilon : ∃ N : ℕ, μ (B) < μ (⋃ i ∈ Set.Iic N , A f a B i) + ε := by

     have hr := epsilon_definition_WANT ε (fun k ↦ μ (⋃ i ∈ Set.Iic k , A f a B i)) (μ B) hf (continuity_of_measure f a B hcount)
     simp at hr
     unfold Set.Iic
     simp
     exact mwe_4 ε (μ B) (fun k ↦ μ (⋃ i ∈ Set.Iic k , A f a B i)) hr


---The next two theorems are required to apply the mathlib result measure_diff_lt_of_lt_add to obtain the set difference theorem

theorem subset (N : ℕ) : ⋃ i ∈ Set.Iic N , A f a B i ⊆ B := by
  unfold Set.Iic
  unfold A
  aesop
  done

theorem partial_union_finite (N : ℕ) : μ (⋃ i ∈ Set.Iic N , A f a B i) ≠  T  :=
by
  have hk := subset f a B N
  have ht := (measure_mono hk).trans_lt hf
  aesop
  done

--- Now the final result follows from the other results using measure_diff_lt_of_lt_add

theorem set_difference_le_epsilon : μ (B \ (⋃ i ∈ Set.Iic N , A f a B i)) < ε := by
  have hs := difference_le_epsilon f a B hf hcount ε
  let ⟨ N, hN ⟩ := hs
  ---constructor

  ---have hy :=  measure_diff_lt_of_lt_add (partial_union_A_measurable f a h B hm N) (subset f a B N) (finite f a B hf N) hN
  ---exact measure_diff_lt_of_lt_add (partial_union_A_measurable f a h B hm N) (subset f a B N) (partial_union_finite f a B hf N) hN
  exact measure_diff_lt_of_lt_add (partial_union_A_measurable f a h B hm N) (subset f a B N) (partial_union_finite f a B hf N) hN
  sorry


-- Theorem 2 of 3 for μ(A \ K) for countable f
theorem compact_subsets_from_regular_measure (n : ℕ) (K : ℕ → Set α) : ∀ i ∈ Set.Icc 1 n, ∃ i, IsCompact (K i) ∧ K i ⊂ f ⁻¹'{a i} ∧ μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n) := by sorry


-- Theorem 3 of 3 for μ(A \ K) < ε for countable f
-- NEED TO FIX ISSUE WITH INDEX i
theorem lusin_for_countable_f (n : ℕ) (K : ℕ → Set α) (hck : ∀ i ∈ Set.Icc 1 n, IsCompact (K i)) (hc : ∀ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i}) (hε : μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n)) : μ (⋃ i, f ⁻¹'{a i} \ ⋃ i, K i) < ε := by sorry


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


/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, then f is constant on each K_i. Hence, f|K (i.e. f restricted to the set K) continuous.


Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/

theorem meas_func_const_on_disjoint_finite_union_is_continuous (n : ℕ) (K : ℕ → Set α) (hpd: ∀ i ∈ Set.Icc 1 n, Pairwise (Disjoint on K i)) : ContinuousOn f (⋃ i ∈ Set.Icc 1 n, K i) := by sorry

--theorem measurable_func_constant_on_sets_is_continuous_on__union [preorder τ] [countable τ] (hcs : compact K)

-- NOTE: in the below it may be better to use ℕ for sequence indexing rather than preorder/countable ι (that was just the convention that the Egorov proof followed)
-- theorem measurable_func_constant_on_sets_is_continuous_on_union {α : Type u_1} {β : Type u_2} {c : β} {m1: MeasurableSpace α} {m2: TopologicalSpace α} {m3 : MeasurableSpace β} {f : α → β } {K : ι → set α} [Preorder ι] [Countable ι] (hf : Measurable f) (hcs : ∀ (i : ι), IsCompact (K i)) (hck : f (K i) = c) (hpd: ∀ (i : ι), Pairwise (Disjoint on K)) : (1=2) := by sorry


-- write countable f theorem here



/-
From proof in MA359 notes: the sequence of functions f_n := 2^-n * floor(2^n f) converges uniformly to f.
-/

-- write uniform convergence proof here



/- Lusin's Theorem for f taking **uncountably many values**:
-/
theorem Lusin [measure.Regular μ] :
∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by
sorry

 ∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by sorry
