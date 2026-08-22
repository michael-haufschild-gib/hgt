import GaloisForLFunctions.HTGeometry.TwoLocalTheoremCWitness
import GaloisForLFunctions.HTGeometry.IntegerMatrixAlgebraicSpectrum
import GaloisForLFunctions.HTGeometry.SpectralOrbitWindowBridge
import GaloisForLFunctions.HTGeometry.ArithmeticWindowHardCell

/-!
# The selected two-local Hamiltonian obeys the arithmetic window law

Theorem C's selection feeds Theorem B: the spectrum of the selected integer matrix is a family of
algebraic integers of the splitting field of its characteristic polynomial, the rigidity of that
family is the integer-relation hypothesis, and the orbit fidelity is the physical one.

## Main results

* `exists_algebraic_spectrum_package` — the spectrum of an integer matrix in Theorem B's format.
-/

open Matrix Polynomial NumberField
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

/-- **The spectrum of a traceless integer matrix with symmetric Galois group, in the format
Theorems A and B consume.** -/
theorem exists_algebraic_spectrum_package {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (hcard : Fintype.card ι = d + 1) (Hz : Matrix ι ι ℤ)
    (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
    (hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)))
    (hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (d + 1).factorial)
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) {R : ℝ}
    (hRbd : ∀ i, |hH.eigenvalues i| ≤ R) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : NumberField K)
      (Ealg : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (ρ : ι ≃ Fin (d + 1)),
      (∀ i, ((hH.eigenvalues i : ℝ) : ℂ) = σ₀ ((Ealg (ρ i) : 𝓞 K) : K)) ∧
      (∀ (τ : K →+* ℂ) (j : Fin (d + 1)), ‖τ ((Ealg j : 𝓞 K) : K)‖ ≤ R) ∧
      (∀ m : Fin d → ℤ, m ≠ 0 → spectralForm Ealg m ≠ 0) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set p : Polynomial ℚ := Hz.charpoly.map (Int.castRingHom ℚ) with hp
  have hmonic : p.Monic := (Hz.charpoly_monic).map _
  have hdeg : p.natDegree = d + 1 := by
    rw [hp, (Hz.charpoly_monic).natDegree_map, Matrix.charpoly_natDegree_eq_dim, hcard]
  have hcoeff : p.coeff (d + 1 - 1) = 0 := by
    have htrZ : Hz.charpoly.coeff (Fintype.card ι - 1) = 0 := by
      have htrc := Matrix.trace_eq_neg_charpoly_coeff Hz
      rw [htr] at htrc
      linarith
    rw [hp, Polynomial.coeff_map, show d + 1 - 1 = Fintype.card ι - 1 from by omega, htrZ,
      map_zero]
  have hcharC : p.map (algebraMap ℚ ℂ) = (Hz.map (Int.castRingHom ℂ)).charpoly := by
    rw [hp, Polynomial.map_map, Matrix.charpoly_map]
    congr 1
  have hEprod : p.map (algebraMap ℚ ℂ)
      = ∏ i, (X - C ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [hcharC, hH.charpoly_eq]
    rfl
  have hEinj : Function.Injective (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    refine Polynomial.separable_prod_X_sub_C_iff.mp ?_
    rw [← hEprod]
    exact (Polynomial.separable_map _).mpr hirr.separable
  obtain ⟨γ, hγinj, hγ, hker⟩ := exists_rigid_root_family hmonic hirr hdeg hd1 hcoeff hgal
  haveI hsf : IsSplittingField ℚ p.SplittingField p :=
    Polynomial.IsSplittingField.splittingField p
  haveI hfd : FiniteDimensional ℚ p.SplittingField :=
    Polynomial.IsSplittingField.finiteDimensional p.SplittingField p
  haveI : CharZero p.SplittingField :=
    charZero_of_injective_algebraMap (algebraMap ℚ p.SplittingField).injective
  haveI : NumberField p.SplittingField := ⟨⟩
  obtain ⟨σ₀, ρ, hmatch⟩ := exists_embedding_matching_roots hγinj hγ hEinj hEprod
  have hroot : ∀ j, ((p.map (algebraMap ℚ p.SplittingField)).IsRoot (γ j)) := by
    intro j
    rw [Polynomial.IsRoot, hγ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  set Ealg : Fin (d + 1) → 𝓞 p.SplittingField :=
    fun j => ⟨γ j, isIntegral_of_isRoot_charpoly Hz (hroot j)⟩ with hEalg
  have hEalgval : ∀ j, ((Ealg j : 𝓞 p.SplittingField) : p.SplittingField) = γ j := fun j => rfl
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, Ealg, σ₀, ρ, ?_, ?_, ?_⟩
  · intro i
    rw [hEalgval]
    exact (hmatch i).symm
  · intro τ j
    rw [hEalgval]
    refine norm_embedding_le p hEprod (hroot j) τ ?_
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hRbd i
  · intro m hm
    refine spectralForm_ne_zero_of_ker_eq_constLine Ealg ?_ m hm
    have hfun : (fun j => ((Ealg j : 𝓞 p.SplittingField) : p.SplittingField)) = γ :=
      funext hEalgval
    rw [hfun]
    exact hker

/-! ### The window law in physical form -/

set_option maxHeartbeats 2000000 in
/-- **Theorem B for an integer matrix, in physical form.**  A traceless integer Hermitian matrix
whose characteristic polynomial is irreducible with the full symmetric Galois group robustly avoids
every finite target family on a definite fraction of every long enough window. -/
theorem half_mul_le_measureReal_hardWindow_physical
    {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (hcard : Fintype.card ι = d + 1) (Hz : Matrix ι ι ℤ)
    (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
    (hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)))
    (hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (d + 1).factorial)
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) {R : ℝ}
    (hRbd : ∀ i, |hH.eigenvalues i| ≤ R)
    {Ω : ι → ℂ} (hΩ : finiteComplexInner Ω Ω = 1)
    {C : Type} [Fintype C] [Nonempty C] [DecidableEq C] (Z : C → (ι → ℂ))
    (hZ : ∀ c, finiteComplexInner (Z c) (Z c) = 1)
    {N : ℕ} {ρ T a : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi)
    (hposR : 0 < 2 * (d : ℝ) * (N : ℝ) * R) (hT : 0 < T) (ha : 0 < a) (r : ℕ)
    (h22 : (Fintype.card C : ℝ) * (r.factorial : ℝ)
      * (16 * spectralCollision (hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH) Ω
          / a ^ 2) ^ r < 1)
    (hNbig : 8 * Real.pi * (d : ℝ)
      ≤ ρ * (ρ / (2 * Real.pi)) ^ d * Real.sqrt ((N : ℝ) + 1))
    (hTbigK : ∀ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : NumberField K),
      8 * ((N : ℝ) + 1) ^ d
        ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹)
    (u : ℝ) :
    ((ρ / (2 * Real.pi)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ | ∀ c,
          finitePureStateFidelity
            (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) (Z c) < a + 2 * ρ}
            ∩ Set.Ioc u (u + T))).toReal := by
  classical
  obtain ⟨K, instF, instA, instN, Ealg, σ₀, ρe, hmatch, hRK, hindep⟩ :=
    exists_algebraic_spectrum_package hcard Hz hH hirr hgal hd1 htr hRbd
  haveI := instF
  haveI := instA
  haveI := instN
  set e : ι → ι → ℂ := hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH with he
  set lam : ι → ℝ := hH.eigenvalues with hlam
  have heb : IsOrthoEigenBasis (Hz.map (Int.castRingHom ℂ)) e lam :=
    isOrthoEigenBasis_hermitian _ hH
  set Elam : Fin (d + 1) → ℝ := fun j => lam (ρe.symm j) with hElam
  set pw : Fin (d + 1) → ℝ := fun j => spectralWeights e Ω (ρe.symm j) with hpw
  set ψw : Fin (d + 1) → ℝ := fun j => spectralPhases e Ω (ρe.symm j) with hψw
  set z : C → (Fin (d + 1) → ℂ) := fun c j => eigenCoords e (Z c) (ρe.symm j) with hz
  have hE : ∀ j, ((Elam j : ℝ) : ℂ) = σ₀ ((Ealg j : 𝓞 K) : K) := by
    intro j
    have hj := hmatch (ρe.symm j)
    rw [hElam]
    simpa using hj
  have hpnn : ∀ j, 0 ≤ pw j := fun j => spectralWeights_nonneg e Ω _
  have hpsum : ∑ j, pw j ≤ 1 := by
    have hsum : ∑ j, pw j = ∑ i, spectralWeights e Ω i :=
      Fintype.sum_equiv ρe.symm _ _ (fun _ => rfl)
    rw [hsum, sum_spectralWeights heb hΩ]
  have hzunit : ∀ c, finiteComplexInner (z c) (z c) = 1 := by
    intro c
    have hre : finiteComplexInner (z c) (z c)
        = finiteComplexInner (eigenCoords e (Z c)) (eigenCoords e (Z c)) :=
      finiteComplexInner_reindex ρe _ _
    rw [hre, finiteComplexInner_eigenCoords heb]
    exact hZ c
  have hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1 := by
    intro c
    have := sum_normSq_eq_one_of_inner (hzunit c)
    exact le_of_eq this
  have h22' : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ)
      * (16 * occupationCollision pw / a ^ 2) ^ r < 1 := by
    have hcoll : occupationCollision pw = spectralCollision e Ω := by
      rw [hpw, occupationCollision_reindex ρe (spectralWeights e Ω),
        occupationCollision_spectralWeights]
    have hfrN : Module.finrank ℂ (replicaTargetSpan r z) ≤ Fintype.card C :=
      finrank_range_le_card (R := ℂ) (fun c => finitePureTensorPowerEuclidean r (z c))
    have hfr : (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) ≤ (Fintype.card C : ℝ) := by
      exact_mod_cast hfrN
    have hcollnn : 0 ≤ spectralCollision e Ω := spectralCollision_nonneg _ _
    have hXnn : (0 : ℝ) ≤ (16 * occupationCollision pw / a ^ 2) ^ r := by
      rw [hcoll]
      positivity
    rw [hcoll] at hXnn ⊢
    refine lt_of_le_of_lt ?_ h22
    refine mul_le_mul_of_nonneg_right ?_ hXnn
    exact mul_le_mul_of_nonneg_right hfr (by positivity)
  have hmain := half_mul_le_measureReal_hardWindow Ealg σ₀ Elam hE hρ hρπ hRK hposR hindep hT u
    hNbig (hTbigK K instF instA instN) hpnn hpsum z hzunit hznorm ha r h22' ψw
  refine le_trans hmain (ENNReal.toReal_mono ?_ ?_)
  · refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · refine MeasureTheory.measure_mono (Set.inter_subset_inter_left _ fun t ht c => ?_)
    have hbridge : finitePureStateFidelity (radianOrbit pw (flowPhase ψw Elam t)) (z c)
        = finitePureStateFidelity
            (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) (Z c) := by
      have hre : finitePureStateFidelity (radianOrbit pw (flowPhase ψw Elam t)) (z c)
          = finitePureStateFidelity
              (radianOrbit (spectralWeights e Ω)
                (fun i => spectralPhases e Ω i - t * lam i)) (eigenCoords e (Z c)) :=
        finitePureStateFidelity_reindex ρe _ _
      rw [hre, finitePureStateFidelity_radianOrbit_spectral heb Ω (Z c) t]
    rw [← hbridge]
    exact ht c

end

end GaloisForLFunctions.HTGeometry
