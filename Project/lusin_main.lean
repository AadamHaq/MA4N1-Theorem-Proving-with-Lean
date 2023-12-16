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
-- This is slightly more restrictive than the theorem in Cohn's book

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
variable [BorelSpace ℝ] (f: α → ℝ) (a: ℕ → ℝ) (hinj : Function.Injective a) (hmf: Measurable f)
variable (B : Set α)(hmb : MeasurableSet B)(hf : μ B ≠ ∞)(hcount : f '' B = Set.range a)
variable (ε : ℝ)(hε: 0 < ε)

-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus
-- ⋃ i A_i = B which is proven here
theorem B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hcount ]
  simp only [Set.inter_eq_right]
  simp_rw[Set.subset_preimage_image f B]
  done

--Here we show some sets are measurable for later use
theorem measurable_A : ∀ (i : ℕ), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter
  apply MeasurableSet.preimage
  apply MeasurableSet.singleton (a b)
  apply hmf
  exact hmb
  done

--We can just use 'MeasurableSet.iUnion (measurable_A f a h B hm)' later and then delete this
theorem measurable_Ai_Union : MeasurableSet (⋃ i, A f a B i) := by
  apply MeasurableSet.iUnion (measurable_A f a hmf B hmb)
  done

--Next we show partial unions are monotone
theorem monotone_A : Monotone (fun k => ⋃ i, ⋃ (_ : i ≤ k) , A f a B i) := by
  unfold Monotone
  intro x y
  simp
  intro hxy j hjx
  have hjy := hjx.trans hxy
  apply Set.subset_biUnion_of_mem
  exact hjy
  done

theorem mwe_2 (s: ℕ → Set α) (j : ℕ): s j ⊆ ⋃ i, ⋃ (_ : i ≤ j) , s i  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done

theorem union_partial_eq_union (s: ℕ → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j, ⋃ (_ : j ≤ i) , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp
  intro t
  have hj := mwe_2 s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x =>  ⋃ j, ⋃ (_ : j ≤ x), s j) t
  done

theorem union_partial_A_eq_B: ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k), A f a B i = B := by
  rw[(union_partial_eq_union (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hcount
  done

theorem continuity_of_measure: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_A_eq_B f a B hcount]
  apply tendsto_measure_iUnion
  apply monotone_A
  done

theorem difference_epsilon : ∃ k : ℕ, μ (B)  ≤
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
theorem partial_union_A_measurable (N : ℕ): MeasurableSet (⋃ i, ⋃ (_ : i ≤ N), A f a B i) := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun _ => measurable_A f a hmf B hmb b
  done

theorem subset (N : ℕ) : ⋃ i, ⋃ (_ : i ≤ N) , A f a B i ⊆ B := by
  unfold A
  simp_all only [ne_eq, Set.iUnion_subset_iff, Set.inter_subset_right, implies_true, forall_const]
  done

--The final result
theorem set_difference_epsilon : ∃ N : ℕ,
μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i) ≤ ENNReal.ofReal (ε * (1/2)) := by
  have ht := difference_epsilon μ f a B hf hcount ε hε
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (subset f a B k) (partial_union_A_measurable f a hmf B hmb k)
    (ne_top_of_lt (LE.le.trans_lt (measure_mono (subset f a B k)) (Ne.lt_top hf)))
  have h5 := tsub_le_iff_left.mpr h4
  rw[← hq] at h5
  exact ⟨ k, h5 ⟩
  done

--Here we obtain the compact subsets K_i of A_i for each i, after two technical results
theorem finite_A (i : ℕ) : μ (A f a B i) ≠ ∞ := by
  have ss := Set.inter_subset_right (f ⁻¹' {a i}) B
  have hy := (measure_mono ss).trans_lt (Ne.lt_top hf)
  exact LT.lt.ne hy
  done


---We will take δ = ε/2N once N exists
theorem compact_subset(δ : ℝ)(hδ : 0 < δ  )(i : ℕ) : ∃ K : Set α,  K ⊆ (A f a B i) ∧  IsCompact K ∧ μ ((A f a B i)\K) ≤  ENNReal.ofReal δ    := by
  have ⟨ K, HK1, HK2, HK3 ⟩ := MeasurableSet.exists_isCompact_lt_add (measurable_A f a hmf B hmb i) (finite_A μ f a B hf i) (zero_lt_iff.mp (ofReal_pos.mpr hδ))
  have hq := measure_diff (HK1) (IsCompact.measurableSet HK2) (ne_top_of_lt (LE.le.trans_lt (measure_mono (Set.Subset.trans HK1 (Set.inter_subset_right (f ⁻¹' {a i}) B))) (Ne.lt_top hf)))
  have HK4 := tsub_le_iff_left.mpr (le_of_lt HK3)
  rw[← hq] at HK4
  exact ⟨ K, HK1, HK2, HK4 ⟩
  done


theorem compact_subset_N (δ : ℝ)(hδ : 0 < δ ): ∃ (K : ℕ → Set α), ∀ i, K i ⊆ (A f a B i) ∧ IsCompact (K i) ∧ μ ((A f a B i)\ (K i)) ≤  ENNReal.ofReal δ := by
  choose K hK using compact_subset μ f a hmf B hmb hf δ hδ
  exact ⟨K, hK⟩

--These results will be needed to manipulate the sets

theorem set_diff (b c a : Set α )(h1 : b ⊆ c)(h2: c ⊆ a) : a\b = a\c ∪ c\b := by
  exact (Set.diff_union_diff_cancel h2 h1).symm
  done

--triv needed for set_diff_union_0
theorem triv (a b c: Set α )(h : c ⊆ b)(hc : a ∩ b = ∅ ) : a ⊆ cᶜ := by
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
theorem set_diff_union_0(a1 a2 k1 k2 : Set α)(h1: k1 ⊆ a1) (h2: k2 ⊆ a2) (h3 : a2 ∩ a1 = ∅):(a1 ∪ a2) \  (k1 ∪ k2) = (a1\k1) ∪ (a2 \ k2)   := by
  have t1 := triv a2 a1 k1 h1 h3
  rw[Set.inter_comm] at h3
  have t2 := triv a1 a2 k2 h2 h3
  rw[Set.diff_eq_compl_inter, Set.compl_union, Set.inter_distrib_left, Set.inter_assoc, Set.inter_assoc, Set.inter_comm k2ᶜ a2, ← Set.inter_assoc k1ᶜ a2 k2ᶜ, Set.inter_comm k1ᶜ a2, Set.inter_comm k2ᶜ a1, Set.inter_eq_self_of_subset_left t1, Set.inter_eq_self_of_subset_left t2, Set.inter_comm a2 k2ᶜ, ← Set.diff_eq_compl_inter, ← Set.diff_eq_compl_inter]


--This is the general version we need which should follow from set_diff_union_0 using induction

theorem A_intersect_empty (n : ℕ) (A : ℕ → Set α)(h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) : (A (n + 1)) ∩ (⋃ i, ⋃ (_ : i ≤ n), A i) = ∅ := by
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

theorem disjoint_K (n : ℕ) (A : ℕ → Set α)(K : ℕ → Set α)(h1 : ∀ i,  K i  ⊆ A i)(h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) : ∀ i ≤ n,  Disjoint (K i) (K (n+1)) := by
  intro i
  have neq (h : i ≤ n) :  i ≠ n+1  := by
    aesop
  have dsj2 (h: i ≠ n+1): Disjoint (A i) (A (n + 1))  := by
    exact Set.disjoint_iff_inter_eq_empty.mpr (h2 i (n + 1) h)
  exact fun a => Set.disjoint_of_subset (h1 i) (h1 (n + 1)) (dsj2 (neq a))


theorem set_diff_union (n : ℕ) (A : ℕ → Set α)(K : ℕ → Set α)(h1 : ∀ i,  K i  ⊆ A i) (h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) :
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

      have h3 := A_intersect_empty n A h2
      rw [@Set.inter_comm] at h3
      exact Set.subset_eq_empty ss2 h3

    exact set_diff_subset (⋃ i, ⋃ (_ : i ≤ n), A i) (⋃ (i : ℕ) (_ : i ≤ n), K i) (⋃ (i : ℕ) (_ : i ≤ n + 1), K i) ss dsj

  have s3 : (A (n+1))\(K (n+1)) = (A (n+1))\((⋃ i, ⋃ (_ : i ≤ n+1), K i)) := by
    have ss : (K (n+1)) ⊆ ((⋃ i, ⋃ (_ : i ≤ n+1), K i)) := by
      exact mwe_2 K (n + 1)
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

      have h5 := A_intersect_empty n A h2

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






theorem mwe_4 (N : ℕ)(P Q Z: ℕ → Prop)(h : ∀ i, P i ∧ Q i ∧ Z i ) : ∀ i ≤ N, Q i := by
  choose h1 h2 h3 using h


--Will need isCompact_iUnion, and sub-additivity of measure
theorem lusin: ∃ K : Set α, K ⊆ B ∧ IsCompact K ∧ μ (B \ K ) ≤ ENNReal.ofReal ε ∧ Continuous (Set.restrict K f) := by
  have ⟨ N, HSD ⟩ := set_difference_epsilon μ f a hmf B hmb hf hcount ε hε
  have not0 : N > 0 := by
    sorry


  have p : 0 < (ε / (2 * N )) := by
    apply(div_pos hε)
    rw[zero_lt_mul_left, Nat.cast_pos]
    apply not0
    apply zero_lt_two

  have ⟨ K , HK ⟩  := compact_subset_N μ f a hmf B hmb  hf (ε/(2*N)) p
  choose HK1 HK2 HK3 using HK


  have KMP : IsCompact (⋃ i, ⋃ (_ : i ≤ N), K i) := by
    have S1 : (⋃ (i : ℕ) (_ : i ≤ N), K i) = ⋃ i ∈ (Set.Icc 0 N), K i := by
      aesop
    have KMP3 : ∀ i ∈ Set.Icc 0 N, IsCompact (K i) := by
      aesop
    have FN : Finite (Set.Icc 0 N) := by
      exact Finite.of_fintype ↑(Set.Icc 0 N)
    sorry






  have SS : (⋃ i, ⋃ (_ : i ≤ N), K i) ⊆ B := by

    have hh1 :  ∀ i ≤ N, K i ⊆ A f a B i := by
      aesop

    have hh2 : ∀ i ≤ N, A f a B i ⊆ B := by
      intro i
      unfold A
      aesop

    have hh3 : ∀ i ≤ N, K i ⊆ B := by
      exact fun i a_1 => Set.Subset.trans (hh1 i a_1) (hh2 i a_1)

    exact Set.iUnion₂_subset hh3


  --This part relates to showing APP

  have S1 : μ (B\(⋃ i, ⋃ (_ : i ≤ N), K i)) ≤  μ (B\(⋃ i, ⋃ (_ : i ≤ N), A f a B i) )  + μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ i, ⋃ (_ : i ≤ N), K i)) := by
    ---have SS1 := (Set.diff_union_diff_cancel h2 h1).symm

    ---have SS2 := measure_union_le (Set.diff B ((⋃ i, ⋃ (_ : i ≤ N), A f a B i))) (Set.diff (⋃ i, ⋃ (_ : i ≤ N), A f a B i) (⋃ i, ⋃ (_ : i ≤ N), K i))
    sorry

  have S2 : μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ i, ⋃ (_ : i ≤ N), K i)) ≤ ∑ᶠ (i : Icc 0 N), μ ((A f a B i) \ (K i)) := by
    --have SS2 := set_diff_union
    sorry

  have S3 : ∑ᶠ (i : Icc 0 N), μ ((A f a B i) \ (K i)) ≤  ENNReal.ofReal (ε/2) := by
    sorry

  ---Then will just use S3 and HSD to show APP
  have APP : μ (B\(⋃ i, ⋃ (_ : i ≤ N), K i))  ≤  ENNReal.ofReal ε := by
    sorry


  have CTS : Continuous (Set.restrict (⋃ i, ⋃ (_ : i ≤ N), K i) f) := by
    sorry

  exact ⟨ (⋃ i, ⋃ (_ : i ≤ N), K i), SS, KMP,  APP, CTS ⟩
  done
