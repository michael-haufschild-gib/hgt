import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreeCycleTypeComparison

/-! Dividing out a prescribed monic factor injects its squarefree
multiples into the smaller degree, preserving weight up to the
factor's own weight. -/

noncomputable section

open Finset Polynomial UniqueFactorizationMonoid WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

variable (g : ℕ) [Fact g.Prime]

private theorem degreeType_mul {K : Type} [Field K] (f h : K[X]) (hf : f ≠ 0) (hh : h ≠ 0) :
    degreeType (f * h) = degreeType f + degreeType h := by
  classical
  simp only [degreeType, normalizedFactors_mul hf hh, Multiset.map_add]

private theorem degreeType_of_irreducible {K : Type} [Field K] (P : K[X])
    (hP : Irreducible P) (hmon : P.Monic) : degreeType P = {P.natDegree} := by
  classical
  rw [degreeType, normalizedFactors_irreducible hP, hmon.normalize_eq_self, Multiset.map_singleton]

theorem squarefreeWeight_mul (f h : (ZMod g)[X]) (hf : f ≠ 0) (hh : h ≠ 0) :
    squarefreeWeight g (f * h) = squarefreeWeight g f * squarefreeWeight g h := by
  simp only [squarefreeWeight, degreeType_mul f h hf hh, Multiset.map_add, Multiset.prod_add]

theorem squarefreeWeight_of_irreducible (P : (ZMod g)[X]) (hP : Irreducible P) (hmon : P.Monic) :
    squarefreeWeight g P = ((g : ℝ) ^ P.natDegree - 1)⁻¹ := by
  simp only [squarefreeWeight, degreeType_of_irreducible P hP hmon, Multiset.map_singleton,
    Multiset.prod_singleton]

theorem square_mass_le_one (N : ℕ) :
    ∑ c ∈ squarefreeCoefficients g N, squarefreeWeight g (monicOf c) ≤ 1 := by
  classical
  simpa only [Finset.filter_true, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, div_self (by positivity : (N.factorial : ℝ) ≠ 0)] using
    squarefree_partition_set_weight_le g N (fun _ => True)

theorem squarefree_divisor_weight_le (N : ℕ) (P : (ZMod g)[X]) (hmon : P.Monic)
    (S : Finset (Fin N → ZMod g))
    (hS : ∀ c ∈ S, c ∈ squarefreeCoefficients g N ∧ P ∣ monicOf c) :
    ∑ c ∈ S, squarefreeWeight g (monicOf c) ≤ squarefreeWeight g P := by
  classical
  let M := N - P.natDegree
  let φ (c : Fin N → ZMod g) (i : Fin M) := (monicOf c / P).coeff i
  have hmul (c : Fin N → ZMod g) (hc : c ∈ S) :
      P * (monicOf c / P) = monicOf c := EuclideanDomain.mul_div_cancel' hmon.ne_zero (hS c hc).2
  have hqmon (c : Fin N → ZMod g) (hc : c ∈ S) : (monicOf c / P).Monic :=
    hmon.of_mul_monic_left (by rw [hmul c hc]; exact monic_monicOf c)
  have hφ (c : Fin N → ZMod g) (hc : c ∈ S) : monicOf (φ c) = monicOf c / P := by
    apply monicOf_coeffs _ (hqmon c hc)
    have h := hmon.natDegree_mul (hqmon c hc)
    rw [hmul c hc, natDegree_monicOf] at h
    dsimp only [M]
    omega
  have hφmem (c : Fin N → ZMod g) (hc : c ∈ S) : φ c ∈ squarefreeCoefficients g M := by
    obtain ⟨hfree, h0⟩ := (Finset.mem_filter.mp (hS c hc).1).2
    simp only [squarefreeCoefficients, Finset.mem_filter, Finset.mem_univ, true_and, hφ c hc]
    refine ⟨hfree.squarefree_of_dvd ⟨P, by rw [mul_comm, hmul c hc]⟩, fun h => h0 ?_⟩
    rw [← hmul c hc, Polynomial.mul_coeff_zero, h, mul_zero]
  have hinj : Set.InjOn φ (S : Set (Fin N → ZMod g)) := by
    intro c hc c' hc' he
    apply monicOf_injective
    rw [← hmul c hc, ← hmul c' hc', ← hφ c hc, ← hφ c' hc', he]
  have hw (c : Fin N → ZMod g) (hc : c ∈ S) :
      squarefreeWeight g (monicOf c) = squarefreeWeight g P * squarefreeWeight g (monicOf (φ c)) := by
    rw [hφ c hc, ← squarefreeWeight_mul g _ _ hmon.ne_zero (hqmon c hc).ne_zero, hmul c hc]
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
  have h1 : ∑ c ∈ S, squarefreeWeight g (monicOf (φ c)) ≤ 1 := by
    rw [← Finset.sum_image (f := fun c' => squarefreeWeight g (monicOf c')) hinj]
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun c _ _ => squarefreeWeight_nonneg g _)).trans
      (square_mass_le_one g M)
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact hφmem d hd
  exact (mul_le_mul_of_nonneg_left h1 (squarefreeWeight_nonneg g _)).trans_eq (mul_one _)

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.squarefree_divisor_weight_le
