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

-- The aim of this lean file is to prove Lusin's Theorem in the case where the function f takes finitely many values (i.e. NOT countably many values). The main file works for countable values however does not cover the finite case: this would not an issue from the perspective of a measure theory course, but is problematic when working with Lean4. This file attemps to adapt the proof and rewrite it in terms of finite many values i.e. the function goes from [1, n] -> ℝ rather than what was shown previously; ℕ -> ℝ.

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
-- Finite Case
variable {n : ℕ} (hn : n ≥ 1)
variable [BorelSpace ℝ] (f: α → ℝ) (a: Set.Icc 1 n → ℝ) (hinja : Function.Injective a) (hmf: Measurable f)
variable (B : Set α)(hmb : MeasurableSet B)(hf : μ B ≠ ∞)(hfin : f '' B = Set.range a)
variable (ε : ℝ)(hε: 0 < ε)

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
  have hn_nonempty : Nonempty (Set.Icc 1 n) := ⟨⟨1, by simp [hn]⟩⟩
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure_fin μ f a B hfin) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl

  exact ⟨N, hy⟩

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
  have ht := partial_union_Ai_up_B_leq_epsilon μ hn f a B hf hfin ε hε
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (Ai_subset_B f a B k) (partial_union_Ai_measurable f a hmf B hmb k)
    (ne_top_of_lt (LE.le.trans_lt (measure_mono (Ai_subset_B f a B k)) (Ne.lt_top hf)))
  have h5 := tsub_le_iff_left.mpr h4
  rw [← hq] at h5
  simp only [one_div] at h5
  exact ⟨k, h5⟩
  done

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


-- Issue with the below is that we are not able to add to elements of 'Set.Icc 1 n'. Currently unsure as to how this can be resolved.

theorem finite_collection_disjoint_subset_union (n : ℕ) (A : ℕ → Set α) (h2 : ∀ i j, i ≠ j → A i ∩ A j = ∅): (A (n + 1)) ∩ (⋃ i : Fin n, A i) = ∅ := by
/-
  have hj : ∀ (i : Fin n), A (n + 1) ∩ A i = ∅
  { intros i
    have neq : (i : ℕ) ≠ n + 1 := ne_of_lt i.2
    have dsj2 : disjoint (A (n + 1)) (A i) := disjoint_iff_inter_eq_empty.mp (h2 _ _ neq)
    exact set.disjoint_iff_inter_eq_empty.mp dsj2 }
  rw [set.inter_Union]
  simp [hj]
  done
-/
  sorry

-- This theorem section is slightly odd as it is impossible to have a case where n+1 is in the function as the maximum value has to be n. After looking on MathLib for a while, Fin n was found. With this, it may be possible to proceed, however if this is the case, perhaps the entire function for A will have to be redefined in the variables.

theorem disjoint_K (n : ℕ) (A : Set.Icc 1 n → Set α)(K : Set.Icc 1 n → Set α)(h1 : ∀ i,  K i  ⊆ A i)(h2 : ∀ i j, i ≠ j → A i ∩ A j = ∅ ) : ∀ i j : Set.Icc 1 n,  Disjoint (K i) (K (j)) := by
  sorry

-- Changed this by introducing the variable N and modifying the bounds of each union accordingly
theorem set_diff_union_n (N : Set.Icc 1 n) (A : Set.Icc 1 n → Set α)(K : Set.Icc 1 n → Set α)(h1 : ∀ i,  K i  ⊆ A i) (h2 : ∀ i j, i ≠ j → A i ∩ A j = ∅ ) :
⋃ i, ⋃ (_ : i ≤ N), ((A i)\(K i)) = (⋃ i, ⋃ (_ : i ≤ N), A i)\(⋃ i, ⋃ (_ : i ≤ N), K i) := by
  sorry

-- Don't think this theorem requires modification in the finite case?
theorem upper_bound_sum(N : ℕ)(b :ENNReal)(m : ℕ → ENNReal)(h : ∀ i, (m i) ≤ b) : ∑ i in Icc 0 N, m i ≤ (N+1) * b := by
  induction' N with N ih
  aesop
  simp
  rw [add_assoc, @add_left_comm, @one_add_mul, add_comm, ← Nat.add_one]
  have h2 : ∑ i in Icc 0 (N + 1), m i = (∑ i in Icc 0 N , m i ) + m (N+1) := by
    have hh2 : Icc 0 (N + 1) = (Icc 0 N) ∪ {N+1} := by
      apply Finset.coe_injective; push_cast
      have ge0 : 0 ≤ Nat.succ N := by aesop
      rw[Set.union_singleton, Nat.add_one,← Nat.succ_eq_succ, ← Order.Icc_succ_right ge0]
    rw[hh2]
    rw[Finset.sum_union]
    aesop
    aesop
  rw[h2]
  have h3 : ∑ i in Icc 0 N, m i + m (N + 1) ≤ (↑N + 1) * b + m (N+1) := by
    exact add_le_add_right ih (m (N+1))
  have h4 : (↑N+1)*b + m (N+1) ≤ (↑N+1)*b + b := by
    exact add_le_add_left (h (N + 1)) ((↑N + 1) * b)
  exact le_trans h3 h4

-- This theorem can also be kept the same
theorem epsilon_ennreal_cancellation (N : ℕ): (↑N + 1)*ENNReal.ofReal (ε/(2*(↑N+1))) = ENNReal.ofReal (ε/2) := by
  rw[div_mul_eq_div_div, ENNReal.ofReal_div_of_pos, ← ENNReal.mul_comm_div]
  have h : ENNReal.ofReal (↑N + 1)  = ↑N + 1 := by
    have h2 := ENNReal.ofReal_coe_nat (N+1)
    aesop
  rw[h, ENNReal.div_self, one_mul]
  simp
  aesop
  exact Nat.cast_add_one_pos N
  done

-- now need results on the continuity of f|K:
theorem restriction_f_K_continuous (K : Set α) (a : ℝ)(s1 : K ⊆ f ⁻¹'({a})) : ContinuousOn f K := by
  have hh1 : f '' K ⊆ {a} := by
    exact Set.mapsTo'.mp s1
  have hh2 : Set.range (Set.restrict K f)  = f '' K := by
    aesop
  have hh3 : Set.range (Set.restrict K f) ⊆ {a} := by
    exact Eq.trans_subset hh2 hh1
  have hh4 :=  Set.eq_or_ssubset_of_subset hh3
  have hh5 : Set.restrict K f = Set.restrict K (fun _  ↦ a ) := by
    exact Set.restrict_eq_iff.mpr s1
  cases' hh4 with c1 c2
  have hh6 : Continuous (Set.restrict K f ) := by
    rw[hh5]
    have hh7 : Continuous (Set.restrict K (fun _  ↦ a )) := by
      rw [← @continuousOn_iff_continuous_restrict]
      exact continuousOn_const
    exact hh7
  exact continuousOn_iff_continuous_restrict.mpr hh6
  have hh8 : Set.range (Set.restrict K f) = ∅  := by
    exact Set.ssubset_singleton_iff.mp c2
  rw[Set.range_eq_empty_iff] at hh8
  have hh9 : K = ∅ := by exact Set.isEmpty_coe_sort.mp hh8
  rw[hh9]
  exact continuousOn_empty f
  done

-- again, same as in main file
theorem restriction_f_union_Ki_continuous (N : ℕ)(K : Icc 0 N → Set α)(h1: ∀ (i : Icc 0 N), IsCompact (K i))(h2 : ∀ (i : Icc 0 N), K i ⊆ f ⁻¹'({a i })) : ContinuousOn f ((⋃ i : Icc 0 N, K i)) := by
  have lf : LocallyFinite K := by
    exact locallyFinite_of_finite K
  have h_cont : ∀ (i : Icc 0 N), ContinuousOn f (K i) := by
    --use restriction_f_K_continuous here
    intro i
    specialize h1 i
    specialize h2 i
    exact restriction_f_K_continuous  f (K i) (a i) h2
  exact LocallyFinite.continuousOn_iUnion lf (fun i => IsCompact.isClosed (h1 i)) h_cont
  done

-- Statement of Lusin's Theorem for when f takes __finitely__ many values:
-- for now I think it ought to be the same as for the countable case?
theorem lusin_finite: ∃ K : Set α, K ⊆ B ∧ IsCompact K ∧ μ (B \ K ) ≤ ENNReal.ofReal ε ∧ ContinuousOn f K := by
  have ⟨ N, HSD ⟩ := B_set_diff_Ai_leq_epsilon μ f a hmf B hmb hf hcount ε hε
  have p : 0 < (ε / (2 * (N+1) )) := by
  sorry
