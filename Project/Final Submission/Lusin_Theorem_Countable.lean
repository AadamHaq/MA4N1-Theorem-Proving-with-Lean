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

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's "Measure Theory" book

namespace Lusin

-- Calling universal variables:
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
variable [BorelSpace ℝ] (f: α → ℝ) (a: ℕ → ℝ) (hinj : Function.Injective a) (hmf: Measurable f)
variable (B : Set α)(hmb : MeasurableSet B)(hf : μ B ≠ ∞)(hcount : f '' B = Set.range a)
variable (ε : ℝ)(hε: 0 < ε)

-- We define the sequence of sets A_i as follows. Note that the B we are referring to here is actually the Borel set mentioned in the theorem statement. In the statement it is referred to as A, and so we are using B here to avoid confusing it with the A_i.
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B


/-
We begin by verifying the key properties of the expressions we have introduced.
-/

-- Since f maps to {a1, a2, ...} we have that ⋃ i f ⁻¹({a i}) is the whole space, and thus ⋃ i A_i = B, which is proven here.
lemma B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hcount ]
  simp only [Set.inter_eq_right]
  simp_rw[Set.subset_preimage_image f B]
  done

-- A_i are measurable, for all i.
lemma measurable_Ai : ∀ (i : ℕ), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter ((MeasurableSet.preimage (MeasurableSet.singleton (a b)) hmf)) (hmb)
  done

-- The sequence (A_i) is a sequence of pairwise disjoint sets.
theorem disjoint_Ai (i j : ℕ) (h : i ≠ j) :  A f a B i ∩ A f a B j = ∅ := by
  unfold A
  have hj : Disjoint (f ⁻¹' {a i}) (f ⁻¹' {a j}) := by
    have hj2 : Disjoint {a i} {a j} := by
      have neq : a i ≠ a j := by
        exact Function.Injective.ne hinj h
      rw[← Set.disjoint_singleton] at neq
      exact neq
    exact Disjoint.preimage f hj2
  rw [@Set.inter_inter_inter_comm]
  simp
  have ss := Set.inter_subset_left (f ⁻¹' {a i} ∩ f ⁻¹' {a j}) B
  rw [@Set.disjoint_iff_inter_eq_empty] at hj
  exact Set.subset_eq_empty ss hj

-- Next we show the mapping given by the partial unions of the elements of the sequence (A_i) are monotone. This mapping is used in the 'continuity_of_measure' lemma provided later.
theorem monotone_Ai : Monotone (fun k => ⋃ i, ⋃ (_ : i ≤ k) , A f a B i) := by
  unfold Monotone
  intro x y
  simp
  intro hxy j hjx
  have hjy := hjx.trans hxy
  apply Set.subset_biUnion_of_mem
  exact hjy
  done

-- Any element of a sequence is contained in the union of the elements of the sequence up to that element. Quite obvious, but we declare and prove this to help us later.
lemma element_subset_union_elements (s: ℕ → Set α) (j : ℕ): s j ⊆ ⋃ i, ⋃ (_ : i ≤ j) , s i  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done


/-
The next seven lemmas/theorems are dedicated to proving that μ(⋃ A_i \ ⋃ A_k) < ε/2 for k ≤ n. The value of n is provided by the definition of the continuity of measure (i.e. ∀ ε, ∃ n such that...).
-/

-- A rather unusual-looking lemma, but this idea of rewriting into a double union is applied in the main result of this subsection.
lemma union_partial_eq_union (s: ℕ → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j, ⋃ (_ : j ≤ i) , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp
  intro t
  have hj := element_subset_union_elements s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x =>  ⋃ j, ⋃ (_ : j ≤ x), s j) t
  done

-- Verifying that this 'double union' formulation satisfies the same condition as in the standard union case:
lemma union_partial_Ai_eq_B: ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k), A f a B i = B := by
  rw[(union_partial_eq_union (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hcount
  done

-- Mathlib does indeed have the notion of the continuity of measure built-in, and so this is more of an ergonomic lemma for us, i.e. writing the result out in a way which is bespoke for our needs.
lemma continuity_of_measure: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_Ai_eq_B f a B hcount]
  apply tendsto_measure_iUnion
  apply monotone_Ai
  done

-- Introducing an ε/2 gap between the full union ⋃ A_i and the finite union A_1 ∪ ... ∪ A_k:
theorem partial_union_Ai_up_B_leq_epsilon : ∃ k : ℕ, μ (B)  ≤
μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ENNReal.ofReal (ε * (1/2))  := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure μ f a B hcount) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl
  exact ⟨N, hy⟩
  done

--- These results will be required to turns this result into a set difference
theorem partial_union_Ai_measurable (N : ℕ): MeasurableSet (⋃ i, ⋃ (_ : i ≤ N), A f a B i) := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun _ => measurable_Ai f a hmf B hmb b
  done

lemma Ai_subset_B (N : ℕ) : ⋃ i, ⋃ (_ : i ≤ N) , A f a B i ⊆ B := by
  unfold A
  simp_all only [ne_eq, Set.iUnion_subset_iff, Set.inter_subset_right, implies_true, forall_const]
  done

--The final result
theorem B_set_diff_Ai_leq_epsilon : ∃ N : ℕ,
μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i) ≤ ENNReal.ofReal (ε/2) := by
  have ht := partial_union_Ai_up_B_leq_epsilon μ f a B hf hcount ε hε
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (Ai_subset_B f a B k) (partial_union_Ai_measurable f a hmf B hmb k)
    (ne_top_of_lt (LE.le.trans_lt (measure_mono (Ai_subset_B f a B k)) (Ne.lt_top hf)))
  have h5 := tsub_le_iff_left.mpr h4
  rw[← hq] at h5
  simp at h5
  exact ⟨ k, h5 ⟩
  done


/-
We now turn our attention to the comapact subsets of each A_i, in order to achieve the bound μ(A_N \ K_N) ≤ ε/2N. We must first verify the existence of these compact subsets K_N, before once again applying continuity of measure for the desired bound. The bound in this case is not as simple as before, as our bound is now contingent on the value of N.
-/

--Here we obtain the compact subsets K_i of A_i for each i, after two technical results
theorem finite_Ai (i : ℕ) : μ (A f a B i) ≠ ∞ := by
  have ss := Set.inter_subset_right (f ⁻¹' {a i}) B
  have hy := (measure_mono ss).trans_lt (Ne.lt_top hf)
  exact LT.lt.ne hy
  done

---We will take δ = ε/2N once N exists
theorem compact_subset(δ : ℝ)(hδ : 0 < δ  )(i : ℕ) : ∃ K : Set α,  K ⊆ (A f a B i) ∧  IsCompact K ∧ μ ((A f a B i)\K) ≤  ENNReal.ofReal δ    := by
  have ⟨ K, HK1, HK2, HK3 ⟩ := MeasurableSet.exists_isCompact_lt_add (measurable_Ai f a hmf B hmb i) (finite_Ai μ f a B hf i) (zero_lt_iff.mp (ofReal_pos.mpr hδ))
  have hq := measure_diff (HK1) (IsCompact.measurableSet HK2) (ne_top_of_lt (LE.le.trans_lt (measure_mono (Set.Subset.trans HK1 (Set.inter_subset_right (f ⁻¹' {a i}) B))) (Ne.lt_top hf)))
  have HK4 := tsub_le_iff_left.mpr (le_of_lt HK3)
  rw[← hq] at HK4
  exact ⟨ K, HK1, HK2, HK4 ⟩
  done

theorem Ai_set_diff_compact_subset_Ai_leq_delta (δ : ℝ)(hδ : 0 < δ ): ∃ (K : ℕ → Set α), ∀ i, K i ⊆ (A f a B i) ∧ IsCompact (K i) ∧ μ ((A f a B i)\ (K i)) ≤  ENNReal.ofReal δ := by
  choose K hK using compact_subset μ f a hmf B hmb hf δ hδ
  exact ⟨K, hK⟩

--These results will be needed to manipulate the sets
theorem set_diff (b c a : Set α )(h1 : b ⊆ c)(h2: c ⊆ a) : a\b = a\c ∪ c\b := by
  exact (Set.diff_union_diff_cancel h2 h1).symm
  done

--subset_disjoint_subset_complement needed for set_diff_union_base_case
theorem subset_disjoint_subset_complement (a b c: Set α )(h : c ⊆ b)(hc : a ∩ b = ∅ ) : a ⊆ cᶜ := by
  have dj : (a ∩ b = ∅) ↔ Disjoint a b := by
    exact Iff.symm Set.disjoint_iff_inter_eq_empty
  rw[dj] at hc
  apply Set.Subset.trans (Disjoint.subset_compl_left (Disjoint.symm hc)) (Set.compl_subset_compl.mpr h)

--This will be needed in the induction proof
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

--This is the easier case of what we want to prove
theorem set_diff_union_base_case(a1 a2 k1 k2 : Set α)(h1: k1 ⊆ a1) (h2: k2 ⊆ a2) (h3 : a2 ∩ a1 = ∅):(a1 ∪ a2) \  (k1 ∪ k2) = (a1\k1) ∪ (a2 \ k2)   := by
  have t1 := subset_disjoint_subset_complement a2 a1 k1 h1 h3
  rw[Set.inter_comm] at h3
  have t2 := subset_disjoint_subset_complement a1 a2 k2 h2 h3
  rw[Set.diff_eq_compl_inter, Set.compl_union, Set.inter_distrib_left, Set.inter_assoc, Set.inter_assoc, Set.inter_comm k2ᶜ a2, ← Set.inter_assoc k1ᶜ a2 k2ᶜ, Set.inter_comm k1ᶜ a2, Set.inter_comm k2ᶜ a1, Set.inter_eq_self_of_subset_left t1, Set.inter_eq_self_of_subset_left t2, Set.inter_comm a2 k2ᶜ, ← Set.diff_eq_compl_inter, ← Set.diff_eq_compl_inter]

--This is the general version we need which should follow from set_diff_union_base_case using induction
theorem collection_disjoint_subset_union (n : ℕ) (A : ℕ → Set α)(h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) : (A (n + 1)) ∩ (⋃ i, ⋃ (_ : i ≤ n), A i) = ∅ := by
  have hj : ∀ i ≤ n, A (n+1) ∩ A i = ∅  := by
    intro i
    have neq (h : i ≤ n) :  i ≠ n+1  := by
      aesop
    have dsj2 (h: i ≠ n+1): Disjoint (A (n + 1)) (A i) := by
      exact Set.disjoint_iff_inter_eq_empty.mpr (h2 (n + 1) i (id (Ne.symm h)))
    exact fun a => Disjoint.inter_eq (dsj2 (neq a))
    done
  rw [@Set.inter_iUnion₂]
  simp
  exact hj

-- Proof that if the A_i's are disjoint, then the compact subsets of the A_i's are also disjoint. This is used in the theorem after.
theorem disjoint_K (n : ℕ) (A : ℕ → Set α)(K : ℕ → Set α)(h1 : ∀ i,  K i  ⊆ A i)(h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) : ∀ i ≤ n,  Disjoint (K i) (K (n+1)) := by
  intro i
  have neq (h : i ≤ n) :  i ≠ n+1  := by
    aesop
  have dsj2 (h: i ≠ n+1): Disjoint (A i) (A (n + 1))  := by
    exact Set.disjoint_iff_inter_eq_empty.mpr (h2 i (n + 1) h)
  exact fun a => Set.disjoint_of_subset (h1 i) (h1 (n + 1)) (dsj2 (neq a))

-- Proof that for disjoint A_i with disjoint compact subsets K_i that the union of (A_i \ K_i) is the same as the union of A_i \ union of K_i. This is used in the final proof of Lusin's theorem.
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

-- A fairly simple theorem that states if m_i <_ b for all i, then the sum from 0 to N of m_i is less than or equal to (N+1)*b. This is clear from the definitions of upper bounds. It is used in the final proof of Lusin's Theorem.
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

-- Another simple theorem used in the final proof of Lusin's Theorem that cancels the constant in the denominator. It is a seperate theorem due to the technicalities of ENNReal.
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


/-
The final component of Lusin's Theorem pertains to demonstrating that f is continous when restricted to the set K = ⋃ K_i. This is proven using the two theorems below:
-/

--A proof that shows the restriction of the function f to just one of the sets K is continuous. This is used in the theorem after which is a generalisation.
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

-- This theorem then proves that f restricted to the union up to N of K sets is continuous. This is used in the final proof of Lusin's Theorem.
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


-- Finally, below is the statement and proof of Lusin's Theorem for when f takes countably many values, using the previous theorems in its proof.
theorem lusin_countable: ∃ K : Set α, K ⊆ B ∧ IsCompact K ∧ μ (B \ K ) ≤ ENNReal.ofReal ε ∧ ContinuousOn f K := by
  have ⟨ N, HSD ⟩ := B_set_diff_Ai_leq_epsilon μ f a hmf B hmb hf hcount ε hε
  have p : 0 < (ε / (2 * (N+1) )) := by
    apply(div_pos hε)
    rw[zero_lt_mul_left]
    exact Nat.cast_add_one_pos N
    apply zero_lt_two
    done
  have ⟨ K , HK ⟩  := Ai_set_diff_compact_subset_Ai_leq_delta μ f a hmf B hmb  hf (ε/(2*(N+1))) p
  choose HK1 HK2 HK3 using HK
  have HK1' : ∀ i : Icc 0 N, K i ⊆ f ⁻¹'({a i }) := by
    intro i
    specialize HK1 i
    unfold A at HK1
    exact le_trans HK1 (Set.inter_subset_left (f ⁻¹' {a ↑i}) B)
  have HK2' : ∀ i : Icc 0 N, IsCompact (K i) := by aesop
  have KMP : IsCompact (⋃ (i : { x // x ∈ Icc 0 N }), (fun i => K ↑i) i) := by
    exact isCompact_iUnion HK2'
  have SS : (⋃ (i : { x // x ∈ Icc 0 N }), (fun i => K ↑i) i) ⊆ B := by
    have hh1 :  ∀ i ≤ N, K i ⊆ A f a B i := by aesop
    have hh2 : ∀ i ≤ N, A f a B i ⊆ B := by
      intro i
      unfold A
      aesop
    have hh3 : ∀ i ≤ N, K i ⊆ B := by
      exact fun i a_1 => Set.Subset.trans (hh1 i a_1) (hh2 i a_1)
    have _ := Set.iUnion₂_subset hh3
    aesop
  have S1 : μ (B\(⋃ i, ⋃ (_ : i ≤ N), K i)) ≤  μ (B\(⋃ i, ⋃ (_ : i ≤ N), A f a B i) )  + μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ i, ⋃ (_ : i ≤ N), K i)) := by
    have h2: (⋃ i, ⋃ (_ : i ≤ N), K i) ⊆ ⋃ i, ⋃ (_ : i ≤ N), A f a B i := by
      simp
      exact fun i i_1 => Set.subset_iUnion₂_of_subset i i_1 (HK1 i)
    have SS1 := (Set.diff_union_diff_cancel (Ai_subset_B f a B N) h2).symm
    have SS2 : μ ((B \ ⋃ (i : ℕ) (_ : i ≤ N), A f a B i) ∪ ((⋃ (i : ℕ) (_ : i ≤ N), A f a B i) \ ⋃ (i : ℕ) (_ : i ≤ N), K i)) ≤ μ (B \ ⋃ (i : ℕ) (_ : i ≤ N), A f a B i) + μ  ((⋃ (i : ℕ) (_ : i ≤ N), A f a B i) \ ⋃ (i : ℕ) (_ : i ≤ N), K i) := by
      exact
        measure_union_le (B \ ⋃ (i : ℕ) (_ : i ≤ N), A f a B i)
          ((⋃ (i : ℕ) (_ : i ≤ N), A f a B i) \ ⋃ (i : ℕ) (_ : i ≤ N), K i)
    rw[← SS1] at SS2
    exact SS2
  have S2 : μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ (i ∈ Icc 0 N), K i)) ≤ ∑ i in Icc 0 N, μ ((A f a B i) \ (K i)) := by
    have SS2 := set_diff_union_n N (A f a B) K HK1 (fun i j a_1 => disjoint_Ai f a hinj B i j a_1)
    simp
    rw[← SS2]
    have h2 : μ (⋃ (i : ℕ) (_ : i ∈ Icc 0 N), (A f a B i \ K i)) ≤ ∑ i in Icc 0 N, μ (A f a B i \ K i) := by
      exact measure_biUnion_finset_le (Icc 0 N) (fun i ↦(A f a B i \ K i) )
    aesop
  have S3 : ∑ i in Icc 0 N, μ ((A f a B i) \ (K i)) ≤  ENNReal.ofReal (ε/2) := by
    have SS3 := upper_bound_sum N (ENNReal.ofReal (ε/(2*(N+1)))) (fun i ↦ μ ((A f a B i) \ (K i))) HK3
    simp at SS3
    rw[epsilon_ennreal_cancellation ε N] at SS3
    exact SS3
  have APP : μ (B \ ⋃ (i : { x // x ∈ Icc 0 N }), (fun i => K i) ↑i)  ≤  ENNReal.ofReal ε := by
    have P2 : μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i) + μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i) \ ⋃ i, ⋃  (_ : i ≤ N), K i) ≤
    ENNReal.ofReal ε := by
      have H := le_trans (add_le_add_left S3 (μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i))) (add_le_add_right HSD (ENNReal.ofReal (ε / 2)))
      rw[add_comm] at H
      have HH := le_trans (add_le_add_right S2 (μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i)) ) H
      have rε : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
        rw[ENNReal.ofReal_div_of_pos two_pos]
        simp only [ofReal_ofNat, ENNReal.add_halves]
      rw[rε , @add_comm] at HH
      simp at HH
      exact HH
    have P3 : (B \ ⋃ (i : ℕ) (_ : i ≤ N), K i) = (B\ ⋃ (i : { x // x ∈ Icc 0 N }), (fun i => K ↑i) i) := by
      simp
      unhygienic ext
      simp_all only [Set.mem_diff, Set.mem_iUnion, Subtype.exists, mem_Icc, zero_le, true_and]
    rw[P3] at S1
    exact le_trans S1 P2
  exact ⟨ (⋃ (i : { x // x ∈ Icc 0 N }), (fun i => K ↑i) i), SS, KMP,  APP, restriction_f_union_Ki_continuous f a N (fun (i : Icc 0 N) ↦ K i) HK2' HK1' ⟩
  done
