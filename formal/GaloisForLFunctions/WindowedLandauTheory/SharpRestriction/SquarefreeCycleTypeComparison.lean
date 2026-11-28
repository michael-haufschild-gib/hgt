import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreeTypeCount
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.PermutationPartitionWeights
import Mathlib.Data.Nat.Choose.Bounds

/-! The squarefree polynomial mass of each degree partition
is at most the uniform permutation mass of that partition.
The comparison extends to unions of partition fibers. -/

noncomputable section

open Finset Polynomial Equiv WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

private theorem choose_weight_le (q d i n : ℕ) (hq : 1 < q) (hd : 1 ≤ d)
    (hi : d * i ≤ q ^ d - 1) :
    (i.choose n : ℝ) * (((q : ℝ) ^ d - 1)⁻¹) ^ n ≤
      ((d : ℝ) ^ n * (n.factorial : ℝ))⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hpow : 1 < (q : ℝ) ^ d := one_lt_pow₀ hqR (by omega)
  have hiR : (d : ℝ) * i ≤ (q : ℝ) ^ d - 1 := by
    have hb : d * i + 1 ≤ q ^ d := by
      have : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
      omega
    have hc : (d : ℝ) * i + 1 ≤ (q : ℝ) ^ d := by exact_mod_cast hb
    linarith only [hc]
  have hbase : (0 : ℝ) < (q : ℝ) ^ d - 1 := sub_pos.mpr hpow
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  calc
    (i.choose n : ℝ) * (((q : ℝ) ^ d - 1)⁻¹) ^ n ≤
        ((i : ℝ) ^ n / n.factorial) / ((q : ℝ) ^ d - 1) ^ n := by
      rw [inv_pow, div_eq_mul_inv _ (((q : ℝ) ^ d - 1) ^ n)]
      exact mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div n i) (by positivity)
    _ ≤ ((d : ℝ) ^ n * (n.factorial : ℝ))⁻¹ := by
      rw [div_div, inv_eq_one_div, div_le_div_iff₀ (mul_pos hfact (pow_pos hbase _))
        (mul_pos (pow_pos hdR _) hfact), one_mul]
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d : ℝ) * i) hiR n
      calc
        (i : ℝ) ^ n * ((d : ℝ) ^ n * (n.factorial : ℝ)) =
            ((d : ℝ) * i) ^ n * (n.factorial : ℝ) := by rw [mul_pow]; ac_rfl
        _ ≤ ((q : ℝ) ^ d - 1) ^ n * (n.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right h hfact.le
        _ = _ := mul_comm _ _

variable (g : ℕ) [Fact g.Prime]

theorem squarefreeWeight_nonneg (f : (ZMod g)[X]) : 0 ≤ squarefreeWeight g f := by
  have hg : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  unfold squarefreeWeight
  apply Multiset.prod_nonneg
  intro a ha
  obtain ⟨d, -, rfl⟩ := Multiset.mem_map.mp ha
  exact inv_nonneg.mpr (sub_nonneg.mpr (one_le_pow₀ hg))

open Classical in
theorem squarefree_partition_weight_le (N : ℕ) (m : Multiset ℕ)
    (hm : ∀ d ∈ m, 1 ≤ d) (hs : m.sum = N) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => degreeType (monicOf c) = m),
      squarefreeWeight g (monicOf c) ≤
    (((univ : Finset (Perm (Fin N))).filter (fun σ => σ.partition.parts = m)).card : ℝ) / N.factorial := by
  classical
  let S := (squarefreeCoefficients g N).filter (fun c => degreeType (monicOf c) = m)
  let I := m.toFinset
  let A (d : ℕ) := (nonzeroIrreducibleCoefficients (ZMod g) d).card
  let w (d : ℕ) := ((g : ℝ) ^ d - 1)⁻¹
  have hI : I ⊆ Icc 1 N := by
    intro d hd
    have hdm : d ∈ m := Multiset.mem_toFinset.mp hd
    exact mem_Icc.mpr ⟨hm d hdm, (Multiset.le_sum_of_mem hdm).trans_eq hs⟩
  have hc : S.card ≤ ∏ d ∈ I, (A d).choose (m.count d) := by
    have hupper := squarefree_type_count_upper (ZMod g) N m.count
    refine ((Finset.card_le_card (s := S) ?_).trans hupper).trans_eq ?_
    · intro c hc
      obtain ⟨hS, he⟩ := Finset.mem_filter.mp hc
      obtain ⟨hfree, h0⟩ := (Finset.mem_filter.mp hS).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hfree, h0, fun d _ => by rw [he]⟩
    · symm
      apply Finset.prod_subset hI
      intro d _ hd
      have hz : m.count d = 0 := Multiset.count_eq_zero.mpr (fun h => hd (Multiset.mem_toFinset.mpr h))
      rw [hz, Nat.choose_zero_right]
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg.le
  have hw0 (d : ℕ) : 0 ≤ w d := inv_nonneg.mpr (sub_nonneg.mpr (one_le_pow₀ hgR))
  have hcount : (S.card : ℝ) ≤ ∏ d ∈ I, ((A d).choose (m.count d) : ℝ) := by exact_mod_cast hc
  have hweight : ∑ c ∈ S, squarefreeWeight g (monicOf c) =
      (S.card : ℝ) * ∏ d ∈ I, w d ^ m.count d := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun c hc => ?_
    have he := (Finset.mem_filter.mp hc).2
    simp only [squarefreeWeight, he, Finset.prod_multiset_map_count, I, w]
  change ∑ c ∈ S, squarefreeWeight g (monicOf c) ≤ _
  rw [partition_probability N m hm hs, hweight]
  refine (mul_le_mul_of_nonneg_right hcount (Finset.prod_nonneg fun d _ => pow_nonneg (hw0 d) _)).trans ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun d _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hw0 d) _)) ?_
  intro d hd
  have hd1 := hm d (Multiset.mem_toFinset.mp hd)
  have hi := irreducible_count_upper_nonzero (ZMod g) d hd1
  rw [ZMod.card] at hi
  exact choose_weight_le g d (A d) _ hg hd1 hi

open Classical in
theorem squarefree_partition_set_weight_le (N : ℕ) (A : Multiset ℕ → Prop) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => A (degreeType (monicOf c))),
      squarefreeWeight g (monicOf c) ≤
    (((univ : Finset (Perm (Fin N))).filter (fun σ => A σ.partition.parts)).card : ℝ) / N.factorial := by
  classical
  let T := (univ : Finset N.Partition).image fun p => p.parts
  have hmem {m : Multiset ℕ} (h1 : ∀ d ∈ m, 1 ≤ d) (h2 : m.sum = N) : m ∈ T :=
    Finset.mem_image.mpr ⟨⟨m, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩
  have hparts {m : Multiset ℕ} (hm : m ∈ T) : (∀ d ∈ m, 1 ≤ d) ∧ m.sum = N := by
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨fun _ hd => p.parts_pos hd, p.parts_sum⟩
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => degreeType (monicOf c))
    (fun c _ => hmem (one_le_of_mem_degreeType _)
      (by rw [sum_degreeType _ (monic_monicOf c).ne_zero, natDegree_monicOf]))]
  rw [Finset.card_eq_sum_card_fiberwise (t := T) (f := fun σ : Perm (Fin N) => σ.partition.parts)
    (fun σ _ => hmem (fun _ hd => σ.partition.parts_pos hd) (by rw [σ.partition.parts_sum, Fintype.card_fin]))]
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨h1, h2⟩ := hparts hm
  by_cases ha : A m
  · have hl : ((squarefreeCoefficients g N).filter (fun c => A (degreeType (monicOf c)))).filter
        (fun c => degreeType (monicOf c) = m) =
        (squarefreeCoefficients g N).filter (fun c => degreeType (monicOf c) = m) := by
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ ha⟩, h.2⟩⟩
    have hr : (((univ : Finset (Perm (Fin N))).filter (fun σ => A σ.partition.parts)).filter
        (fun σ => σ.partition.parts = m)) =
        univ.filter (fun σ : Perm (Fin N) => σ.partition.parts = m) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
    rw [hl, hr]
    exact squarefree_partition_weight_le g N m h1 h2
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro c hc
      have he := (Finset.mem_filter.mp hc).2
      exact (ha (he ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2)).elim

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.squarefree_partition_set_weight_le
