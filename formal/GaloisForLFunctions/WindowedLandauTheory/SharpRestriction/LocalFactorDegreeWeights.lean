import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRowWeightBounds
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreeCycleTypeComparison
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.InvariantSubsetCount
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.PermutationInvariantSubsum
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LongPrimeCycleCount

/-! Divisor degrees are subsums of the irreducible factor partition.
The permutation bounds control both prescribed divisor degrees
and the absence of a large factor of prime degree. -/

noncomputable section

open Finset Equiv Polynomial UniqueFactorizationMonoid WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open Classical in
private theorem divisor_degree_iff_subsum {K : Type} [Field K] (f : K[X]) (hf : f ≠ 0) (a : ℕ) :
    (∃ Q : K[X], Q ∣ f ∧ Q.natDegree = a) ↔ ∃ u ≤ degreeType f, u.sum = a := by
  have hdeg (u : Multiset K[X]) (hu : u ≤ normalizedFactors f) :
      u.prod.natDegree = (u.map natDegree).sum :=
    natDegree_multiset_prod _ fun h0 => zero_notMem_normalizedFactors f (Multiset.mem_of_le hu h0)
  unfold degreeType
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    have hQ0 : Q ≠ 0 := fun h => hf (zero_dvd_iff.mp (h ▸ hQ))
    have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hQ0 hf).mp hQ
    refine ⟨(normalizedFactors Q).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hQ0))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map natDegree _ s hs
    exact ⟨u.prod, (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd, hdeg u hu⟩

open Classical in
private theorem long_prime_factor_iff {K : Type} [Field K] (N : ℕ) (f : K[X]) (hf : f ≠ 0) :
    (∃ Q : K[X], Irreducible Q ∧ Q ∣ f ∧ Q.natDegree.Prime ∧ N < 2 * Q.natDegree ∧
      Q.natDegree + 3 ≤ N) ↔
      ∃ p ∈ degreeType f, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N := by
  unfold degreeType
  constructor
  · rintro ⟨P, hi, hd, hp⟩
    obtain ⟨Q, hQ, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hi hd
    have he := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
    exact ⟨Q.natDegree, Multiset.mem_map.mpr ⟨Q, hQ, rfl⟩, he ▸ hp⟩
  · rintro ⟨p, hp, h⟩
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hp
    exact ⟨Q, irreducible_of_normalized_factor Q hQ, dvd_of_mem_normalizedFactors hQ, h⟩

variable (g N : ℕ) [Fact g.Prime]

open Classical in
theorem local_divisor_degree_weight_le (a : ℕ) (ha : a ∈ Icc 1 (N / 2)) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (hasDivisorDegree g N a),
      squarefreeWeight g (monicOf c) ≤ 7 / 8 := by
  let A (m : Multiset ℕ) : Prop := ∃ u ≤ m, u.sum = a
  have hfilt : (squarefreeCoefficients g N).filter (hasDivisorDegree g N a) =
      (squarefreeCoefficients g N).filter (fun c => A (degreeType (monicOf c))) := by
    apply Finset.filter_congr
    intro c _
    exact divisor_degree_iff_subsum _ (monic_monicOf c).ne_zero a
  have ha' := Finset.mem_Icc.mp ha
  have hP := invariant_subset_card_bound N a (by omega) (by omega)
  have hcount : ((univ : Finset (Perm (Fin N))).filter (fun σ => A σ.partition.parts)).card ≤
      ((univ : Finset (Perm (Fin N))).filter
        (fun σ => ∃ S : Finset (Fin N), S.card = a ∧ ∀ x ∈ S, σ x ∈ S)).card := by
    apply Finset.card_le_card
    intro σ hσ
    obtain ⟨S, hS, hc⟩ := invariant_subset_of_subsum σ a (Finset.mem_filter.mp hσ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, hc, hS⟩
  have hnat := (Nat.mul_le_mul_left 8 hcount).trans hP
  have hreal : 8 * (((univ : Finset (Perm (Fin N))).filter (fun σ => A σ.partition.parts)).card : ℝ) ≤
      7 * (N.factorial : ℝ) := by exact_mod_cast hnat
  have hfac : (0 : ℝ) < N.factorial := by positivity
  rw [hfilt]
  refine (squarefree_partition_set_weight_le g N A).trans ((div_le_iff₀ hfac).mpr ?_)
  linarith only [hreal]

open Classical in
theorem local_no_long_prime_weight_le (hN : 20000 ≤ N) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ hasLongPrimeFactor g N c),
      squarefreeWeight g (monicOf c) ≤ 1 - 1 / (5 * Real.log N) := by
  let A (m : Multiset ℕ) : Prop := ∃ p ∈ m, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N
  have hfilt : (squarefreeCoefficients g N).filter (fun c => ¬ hasLongPrimeFactor g N c) =
      (squarefreeCoefficients g N).filter (fun c => ¬ A (degreeType (monicOf c))) :=
    Finset.filter_congr fun c _ => not_congr (long_prime_factor_iff N _ (monic_monicOf c).ne_zero)
  have hparts (σ : Perm (Fin N)) : A σ.partition.parts ↔ A σ.cycleType := by
    have hs := σ.filter_parts_partition_eq_cycleType
    constructor
    · rintro ⟨p, hp, h⟩
      exact ⟨p, hs ▸ Multiset.mem_filter.mpr ⟨hp, h.1.two_le⟩, h⟩
    · rintro ⟨p, hp, h⟩
      exact ⟨p, (Multiset.mem_filter.mp (hs.symm ▸ hp)).1, h⟩
  let B := (univ : Finset (Perm (Fin N))).filter (fun σ => ¬ A σ.partition.parts)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Perm (Fin N))))
    (fun σ => A σ.partition.parts)
  change ((univ : Finset (Perm (Fin N))).filter (fun σ => A σ.partition.parts)).card + B.card =
    (univ : Finset (Perm (Fin N))).card at hsplit
  rw [Finset.filter_congr (fun σ _ => hparts σ), Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsplit
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  rw [Nat.cast_add, long_prime_cycle_count N] at hr
  have hs : ∑ p ∈ longPrimes N, (N.factorial : ℝ) / p =
      (N.factorial : ℝ) * longPrimeReciprocalSum N := by
    rw [longPrimeReciprocalSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [mul_one_div]
  rw [hs] at hr
  have hfac : (0 : ℝ) < N.factorial := by positivity
  have hprod := mul_le_mul_of_nonneg_left (long_prime_reciprocal_sum_le N hN) hfac.le
  rw [hfilt]
  have hB : (B.card : ℝ) / N.factorial ≤ 1 - 1 / (5 * Real.log N) := by
    rw [div_le_iff₀ hfac]
    linarith only [hr, hprod]
  have h := squarefree_partition_set_weight_le g N (fun m => ¬ A m)
  refine (le_of_eq ?_).trans (h.trans ?_)
  · first | rfl | (congr 1; ext c; simp only [Finset.mem_filter])
  · convert hB using 4 <;>
      first | rfl | (apply Finset.ext; intro σ; simp only [B, Finset.mem_filter])

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.local_divisor_degree_weight_le
#print axioms WindowedLandauTheory.ConcN.local_no_long_prime_weight_le
