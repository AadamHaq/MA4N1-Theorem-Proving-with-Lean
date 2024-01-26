import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Init.Order.Defs
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.Basic

set_option maxHeartbeats 0

open MeasureTheory ENNReal Filter Finset BigOperators
open scoped Topology

-- The aim of this lean file is to prove Lusin's Theorem in the case where the function f takes finitely many values (i.e. NOT countably many values). The main file works for countable values however does not cover the finite case: this would not an issue from the perspective of a measure theory course, but of course is problem when working with Lean4. This file attemps to adapt the proof and rewrite it in terms of finite many values i.e. the function goes from [1, n] -> ℝ rather than what was shown previously; ℕ -> ℝ.

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
-- Finite Case
variable [BorelSpace ℝ] (f: α → ℝ) (a: Set.Icc 1 n → ℝ) (hinja : Function.Injective a) (hmf: Measurable f)
variable (B : Set α)(hmb : MeasurableSet B)(hf : μ B ≠ ∞)(hfin : f '' B = Set.range a)

-- f takes finitely many values
def A (i : Set.Icc 1 n) := f ⁻¹'({a i}) ∩ B

-- All of the previous lemmas and theorems are similar to the countable case, but with finite variables. The proofs are similar but there are some subtle differences.
lemma B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hfin ]
  simp only [Set.inter_eq_right]
  simp_rw[Set.subset_preimage_image f B]
  done

-- Demonstrating the measurability of A_1,...,A_n
lemma measurable_Ai : ∀ (i : Set.Icc 1 n), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter ((MeasurableSet.preimage (MeasurableSet.singleton (a b)) hmf)) (hmb)
  done

-- Demonstrating the pairwise disjointness of A_1,...A_n
theorem disjoint_Ai (i j : Set.Icc 1 n) (h : i ≠ j) :  A f a B i ∩ A f a B j = ∅ := by
  unfold A
  have hj : Disjoint (f ⁻¹' {a i}) (f ⁻¹' {a j}) := by
    have hj2 : Disjoint {a i} {a j} := by
      have neq : a i ≠ a j := by
        exact Function.Injective.ne hinja h
      rw[← Set.disjoint_singleton] at neq
      exact neq
    exact Disjoint.preimage f hj2
  rw [@Set.inter_inter_inter_comm]
  simp
  have ss := Set.inter_subset_left (f ⁻¹' {a i} ∩ f ⁻¹' {a j}) B
  rw [@Set.disjoint_iff_inter_eq_empty] at hj
  exact Set.subset_eq_empty ss hj
  done

theorem monotone_Ai : Monotone (fun k => ⋃ i, ⋃ (_ : i ≤ k) , A f a B i) := by
  unfold Monotone
  intro a b
  simp only [ge_iff_le, not_le, Nat.lt_one_iff, gt_iff_lt, Set.mem_Icc,
    Set.le_eq_subset, Set.iUnion_subset_iff]
  intro hab i hia
  have hib := hia.trans hab
  apply Set.subset_biUnion_of_mem
  exact hib
  done

lemma element_subset_union_elements_fin (s: Set.Icc 1 n → Set α) (j : Set.Icc 1 n): s j ⊆ ⋃ i, ⋃ (_ : i ≤ j) , s i  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done

lemma union_partial_eq_union_fin (s: Set.Icc 1 n → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j, ⋃ (_ : j ≤ i) , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp only [Set.iUnion_subset_iff]
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp only [Set.iUnion_subset_iff]
  intro t
  have hj := element_subset_union_elements_fin s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x =>  ⋃ j, ⋃ (_ : j ≤ x), s j) t
  done

lemma union_partial_Ai_eq_B: ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k), A f a B i = B := by
  rw[(union_partial_eq_union_fin (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hfin
  done

lemma continuity_of_measure_fin: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_Ai_eq_B f a B hfin]
  apply tendsto_measure_iUnion
  apply monotone_Ai
  done

theorem partial_union_Ai_up_B_leq_epsilon : ∃ k : Set.Icc 1 n, μ (B)  ≤
μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ENNReal.ofReal (ε * (1/2))  := by
  /-have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure_fin μ f a B hfin) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl

  exact ⟨N, hy⟩
  -/
  sorry

/- The issue above most comes from ENNReal only thinking [1, n] can be empty. This can be seen by uncommenting the 'proof' above.
This is not the case as we want n to be an integer ≥ 1. Despite adding hypotheses and trying to change the variables using this stipulation, further progress could not be achieved in proving this fact.
-/

-- Despite this, it was decided to continue the proof but with the previous proof 'sorry'd'

theorem partial_union_Ai_measurable (N : Set.Icc 1 n): MeasurableSet (⋃ i, ⋃ (_ : i ≤ N), A f a B i) := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun _ => measurable_Ai f a hmf B hmb b
  done

lemma Ai_subset_B (N : Set.Icc 1 n) : ⋃ i, ⋃ (_ : i ≤ N) , A f a B i ⊆ B := by
  unfold A
  simp_all only [ne_eq, Set.iUnion_subset_iff, Set.inter_subset_right, implies_true, forall_const]
  done

theorem B_set_diff_Ai_leq_epsilon : ∃ N : Set.Icc 1 n,
μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i) ≤ ENNReal.ofReal (ε/2) := by
  /-
  have ht := partial_union_Ai_up_B_leq_epsilon μ f a B hf hcount ε hε
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (Ai_subset_B f a B k) (partial_union_Ai_measurable f a hmf B hmb k)
    (ne_top_of_lt (LE.le.trans_lt (measure_mono (Ai_subset_B f a B k)) (Ne.lt_top hf)))
  have h5 := tsub_le_iff_left.mpr h4
  rw[← hq] at h5
  simp at h5
  exact ⟨ k, h5 ⟩
  done
  -/
  sorry

-- There was a similar issue with the above proof unfortunately

theorem finite_Ai (i : Set.Icc 1 n) : μ (A f a B i) ≠ ∞ := by
  have ss := Set.inter_subset_right (f ⁻¹' {a i}) B
  have hy := (measure_mono ss).trans_lt (Ne.lt_top hf)
  exact LT.lt.ne hy
  done

theorem compact_subset(δ : ℝ)(hδ : 0 < δ  )(i : Set.Icc 1 n) : ∃ K : Set α,  K ⊆ (A f a B i) ∧  IsCompact K ∧ μ ((A f a B i)\K) ≤  ENNReal.ofReal δ    := by
  have ⟨ K, HK1, HK2, HK3 ⟩ := MeasurableSet.exists_isCompact_lt_add (measurable_Ai f a hmf B hmb i) (finite_Ai μ f a B hf i) (zero_lt_iff.mp (ofReal_pos.mpr hδ))
  have hq := measure_diff (HK1) (IsCompact.measurableSet HK2) (ne_top_of_lt (LE.le.trans_lt (measure_mono (Set.Subset.trans HK1 (Set.inter_subset_right (f ⁻¹' {a i}) B))) (Ne.lt_top hf)))
  have HK4 := tsub_le_iff_left.mpr (le_of_lt HK3)
  rw[← hq] at HK4
  exact ⟨ K, HK1, HK2, HK4 ⟩
  done

theorem Ai_set_diff_compact_subset_Ai_leq_delta (δ : ℝ)(hδ : 0 < δ ): ∃ (K : Set.Icc 1 n → Set α), ∀ i, K i ⊆ (A f a B i) ∧ IsCompact (K i) ∧ μ ((A f a B i)\ (K i)) ≤  ENNReal.ofReal δ := by
  choose K hK using compact_subset μ f a hmf B hmb hf δ hδ
  exact ⟨K, hK⟩
  done

-- The following couple of theorems are the same for the finite case
theorem set_diff (b c a : Set α )(h1 : b ⊆ c)(h2: c ⊆ a) : a\b = a\c ∪ c\b := by
  exact (Set.diff_union_diff_cancel h2 h1).symm
  done

theorem subset_disjoint_subset_complement (a b c: Set α )(h : c ⊆ b)(hc : a ∩ b = ∅ ) : a ⊆ cᶜ := by
  have dj : (a ∩ b = ∅) ↔ Disjoint a b := by
    exact Iff.symm Set.disjoint_iff_inter_eq_empty
  rw[dj] at hc
  apply Set.Subset.trans (Disjoint.subset_compl_left (Disjoint.symm hc)) (Set.compl_subset_compl.mpr h)
  done

theorem set_diff_subset (a b c : Set α)(h : b ⊆ c)(hz : a ∩ (c\b) = ∅) : a\b = a\c := by
  have cb : cᶜ ⊆ bᶜ := by exact Set.compl_subset_compl.mpr h
  have hr :  a \ c ∪ (a ∩ (c\b)) = a \ b := by
    rw[Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, Set.union_distrib_left, Set.union_distrib_right,
    Set.union_self, Set.union_inter_cancel_right, Set.union_distrib_left, Set.union_distrib_right,
    Set.union_distrib_right, Set.compl_union_self, Set.univ_inter, Set.union_eq_self_of_subset_left cb,
     Set.inter_comm bᶜ (a ∪ bᶜ), Set.union_inter_cancel_right, Set.inter_comm bᶜ (a ∪ c), ← Set.inter_assoc,
     Set.inter_comm a (a ∪ c), ←Set.diff_eq, Set.union_inter_cancel_left ]
  rw[← hr,hz]
  exact Set.union_empty (a \ c)
  done

theorem set_diff_union_base_case(a1 a2 k1 k2 : Set α)(h1: k1 ⊆ a1) (h2: k2 ⊆ a2) (h3 : a2 ∩ a1 = ∅):(a1 ∪ a2) \  (k1 ∪ k2) = (a1\k1) ∪ (a2 \ k2)   := by
  have t1 := subset_disjoint_subset_complement a2 a1 k1 h1 h3
  rw[Set.inter_comm] at h3
  have t2 := subset_disjoint_subset_complement a1 a2 k2 h2 h3
  rw[Set.diff_eq_compl_inter, Set.compl_union, Set.inter_distrib_left, Set.inter_assoc, Set.inter_assoc, Set.inter_comm k2ᶜ a2, ← Set.inter_assoc k1ᶜ a2 k2ᶜ, Set.inter_comm k1ᶜ a2, Set.inter_comm k2ᶜ a1, Set.inter_eq_self_of_subset_left t1, Set.inter_eq_self_of_subset_left t2, Set.inter_comm a2 k2ᶜ, ← Set.diff_eq_compl_inter, ← Set.diff_eq_compl_inter]
  done

theorem collection_disjoint_subset_union (m : Set.Icc 1 n) (A : Set.Icc 1 n → Set α)(h2 : ∀ i j, i ≠ j → A i ∩ A j = ∅ ) : (A (m + 1)) ∩ (⋃ i, ⋃ (_ : i ≤ m), A i) = ∅ := by
  /-
  have hj : ∀ i ≤ m, A (m+1) ∩ A i = ∅  := by
    intro i
    have neq (h : i ≤ m) :  i ≠ m+1  := by
      aesop
    have dsj2 (h: i ≠ m+1): Disjoint (A (m + 1)) (A i) := by
      exact Set.disjoint_iff_inter_eq_empty.mpr (h2 (m + 1) i (id (Ne.symm h)))
    exact fun a => Disjoint.inter_eq (dsj2 (neq a))
    done
  rw [@Set.inter_iUnion₂]
  simp
  exact hj
  done
  -/
  sorry


theorem disjoint_K (n : ℕ) (A : Set.Icc 1 n → Set α)(K : Set.Icc 1 n → Set α)(h1 : ∀ i,  K i  ⊆ A i)(h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) : ∀ i : Set.Icc 1 n,  Disjoint (K i) (K (n+1)) := by
  intro i
  have neq (h : i ≤ n) :  i ≠ n+1  := by
    aesop
  have dsj2 (h: i ≠ n+1): Disjoint (A i) (A (n + 1))  := by
    exact Set.disjoint_iff_inter_eq_empty.mpr (h2 i (n + 1) h)
  exact fun a => Set.disjoint_of_subset (h1 i) (h1 (n + 1)) (dsj2 (neq a))


theorem set_diff_union_n (n : ℕ) (A : ℕ → Set α)(K : ℕ → Set α)(h1 : ∀ i,  K i  ⊆ A i) (h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) :
⋃ i, ⋃ (_ : i ≤ n), ((A i)\(K i)) = (⋃ i, ⋃ (_ : i ≤ n), A i)\(⋃ i, ⋃ (_ : i ≤ n), K i) := by
  induction' n with n ih
  --base case
  simp
  --main proof
  have ss1 : ⋃ i, ⋃ (_ : i ≤ n+1), K i = (⋃ i, ⋃ (_ : i ≤ n), K i ) ∪ K (n+1) := by
    rw [← @Set.biUnion_le_succ]
  have dsj1 : ((⋃ i, ⋃ (_ : i ≤ n + 1), K i )\(⋃ i, ⋃ (_ : i ≤ n), K i )) = K (n+1) := by
    rw[ss1]
    simp only [Set.union_diff_left, sdiff_eq_left, Set.disjoint_iUnion_right]
    have h := disjoint_K n A K h1 h2
    intro i
    specialize h i
    rw [@disjoint_comm]
    exact h
  have s1 : ⋃ i, ⋃ (_ : i ≤ Nat.succ n), (A i)\(K i) = (⋃ i, ⋃ (_ : i ≤ n), (A i)\(K i)) ∪ (A (n+1))\(K (n+1)) := by
    rw [← @Set.biUnion_le_succ]
  have s2 : (⋃ i, ⋃ (_ : i ≤ n), A i)\(⋃ i, ⋃ (_ : i ≤ n), K i) = (⋃ i, ⋃ (_ : i ≤ n), A i)\(⋃ i, ⋃ (_ : i ≤ n+1), K i) := by
    have ss : ⋃ i, ⋃ (_ : i ≤ n), K i ⊆ ⋃ i, ⋃ (_ : i ≤ n+1), K i := by
      have ss1 : ⋃ i, ⋃ (_ : i ≤ n+1), K i = (⋃ i, ⋃ (_ : i ≤ n), K i ) ∪ K (n+1) := by
        rw [← @Set.biUnion_le_succ]
      rw[ss1]
      aesop
      done
    have dsj : (⋃ i, ⋃ (_ : i ≤ n), A i) ∩ ((⋃ i, ⋃ (_ : i ≤ n + 1), K i )\(⋃ i, ⋃ (_ : i ≤ n), K i )) = ∅ := by
      rw[dsj1]
      have ss2: (⋃ (i : ℕ) (_ : i ≤ n), A i) ∩ K (n + 1) ⊆ (⋃ (i : ℕ) (_ : i ≤ n), A i) ∩ A (n+1) := by
        specialize h1 (n+1)
        exact Set.inter_subset_inter_right (⋃ (i : ℕ) (_ : i ≤ n), A i) h1
      have h3 := collection_disjoint_subset_union n A h2
      rw [@Set.inter_comm] at h3
      exact Set.subset_eq_empty ss2 h3
    exact set_diff_subset (⋃ i, ⋃ (_ : i ≤ n), A i) (⋃ (i : ℕ) (_ : i ≤ n), K i) (⋃ (i : ℕ) (_ : i ≤ n + 1), K i) ss dsj
  have s3 : (A (n+1))\(K (n+1)) = (A (n+1))\((⋃ i, ⋃ (_ : i ≤ n+1), K i)) := by
    have ss : (K (n+1)) ⊆ ((⋃ i, ⋃ (_ : i ≤ n+1), K i)) := by
      exact element_subset_union_elements K (n + 1)
    have dsj : (A (n+1)) ∩ (((⋃ i, ⋃ (_ : i ≤ n+1), K i))\ K (n+1)) = ∅ := by
      have hj : (((⋃ i, ⋃ (_ : i ≤ n+1), K i))\ K (n+1)) = ((⋃ i, ⋃ (_ : i ≤ n), K i)) := by
        rw[ss1]
        simp only [Set.union_diff_right, sdiff_eq_left, Set.disjoint_iUnion_left]
        exact disjoint_K n A K h1 h2
      rw[hj]
      have hy : A (n + 1) ∩ ⋃ i, ⋃  (_ : i ≤ n), K i ⊆ A (n + 1) ∩ ⋃ i, ⋃ (_ : i ≤ n), A i := by
        have hj : (⋃ i, ⋃ (_ : i ≤ n), K i ) ⊆ (⋃ i, ⋃ (_ : i ≤ n), A i ) := by
          rw [@Set.iUnion₂_subset_iff]
          exact fun i j => Set.subset_iUnion₂_of_subset i j (h1 i)
        exact Set.inter_subset_inter_right (A (n + 1)) hj
      have h5 := collection_disjoint_subset_union n A h2
      exact Set.subset_eq_empty hy h5
    exact set_diff_subset (A (n+1)) (K (n+1)) ((⋃ i, ⋃ (_ : i ≤ n+1), K i)) ss dsj
  have s4 : (⋃ (i : ℕ) (_ : i ≤ n), A i)\(⋃ (i : ℕ) (_ : i ≤ n + 1), K i) ∪
    (A (n + 1))\(⋃ (i : ℕ) (_ : i ≤ n + 1), K i) = (⋃ i, ⋃ (_ : i ≤ n+1), A i)\(⋃ i, ⋃ (_ : i ≤ n+1), K i) := by
    have s5 :  ((⋃ (i : ℕ) (_ : i ≤ n), A i) ∪ A (n + 1)) = (⋃ (i : ℕ) (_ : i ≤ n+1), A i) := by
      rw [← @Set.biUnion_le_succ]
    rw[Set.union_diff_distrib.symm]
    rw[s5]
  rw[s1,ih,s2,s3,s4]
  done
