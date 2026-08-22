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
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) {R T : ℝ} {N : ℕ}
    (hRbd : ∀ i, |hH.eigenvalues i| ≤ R)
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ ((d + 1).factorial - 1))⁻¹) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : NumberField K)
      (Ealg : Fin (d + 1) → 𝓞 K) (σ₀ : K →+* ℂ) (ρ : ι ≃ Fin (d + 1)),
      (∀ i, ((hH.eigenvalues i : ℝ) : ℂ) = σ₀ ((Ealg (ρ i) : 𝓞 K) : K)) ∧
      (∀ (τ : K →+* ℂ) (j : Fin (d + 1)), ‖τ ((Ealg j : 𝓞 K) : K)‖ ≤ R) ∧
      (∀ m : Fin d → ℤ, m ≠ 0 → spectralForm Ealg m ≠ 0) ∧
      8 * ((N : ℝ) + 1) ^ d
        ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹ := by
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
  have hcardEmb : Fintype.card (p.SplittingField →+* ℂ) = (d + 1).factorial := by
    rw [NumberField.Embeddings.card, ← Polynomial.Gal.card_of_separable hirr.separable]
    exact hgal
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, Ealg, σ₀, ρ,
    ?_, ?_, ?_, ?_⟩
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
  · rw [hcardEmb]
    exact hTbig

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
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ ((d + 1).factorial - 1))⁻¹)
    (u : ℝ) :
    ((ρ / (2 * Real.pi)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ | ∀ c,
          finitePureStateFidelity
            (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) (Z c) < a + 2 * ρ}
            ∩ Set.Ioc u (u + T))).toReal := by
  classical
  obtain ⟨K, instF, instA, instN, Ealg, σ₀, ρe, hmatch, hRK, hindep, hTbigK⟩ :=
    exists_algebraic_spectrum_package hcard Hz hH hirr hgal hd1 htr hRbd hTbig
  set e : ι → ι → ℂ := hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH with he
  set lam : ι → ℝ := hH.eigenvalues with hlam
  have heb : IsOrthoEigenBasis (Hz.map (Int.castRingHom ℂ)) e lam :=
    isOrthoEigenBasis_hermitian _ hH
  obtain ⟨Elam, hElam⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => lam (ρe.symm j) := ⟨_, rfl⟩
  obtain ⟨pw, hpw⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => spectralWeights e Ω (ρe.symm j) :=
    ⟨_, rfl⟩
  obtain ⟨ψw, hψw⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => spectralPhases e Ω (ρe.symm j) :=
    ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ f : C → (Fin (d + 1) → ℂ), f = fun c j => eigenCoords e (Z c) (ρe.symm j) :=
    ⟨_, rfl⟩
  have hE : ∀ j, ((Elam j : ℝ) : ℂ) = σ₀ ((Ealg j : 𝓞 K) : K) := by
    intro j
    have hj := hmatch (ρe.symm j)
    rw [hElam]
    simpa using hj
  have hpnn : ∀ j, 0 ≤ pw j := by
    intro j
    rw [hpw]
    exact spectralWeights_nonneg e Ω _
  have hpsum : ∑ j, pw j ≤ 1 := by
    have hsum : ∑ j, pw j = ∑ i, spectralWeights e Ω i := by
      rw [hpw]
      exact Fintype.sum_equiv ρe.symm (fun j => spectralWeights e Ω (ρe.symm j))
        (spectralWeights e Ω) (fun _ => rfl)
    rw [hsum, sum_spectralWeights heb hΩ]
  have hzunit : ∀ c, finiteComplexInner (z c) (z c) = 1 := by
    intro c
    have hfun2 : z c = fun j => eigenCoords e (Z c) (ρe.symm j) := by rw [hz]
    have hre : finiteComplexInner (z c) (z c)
        = finiteComplexInner (eigenCoords e (Z c)) (eigenCoords e (Z c)) := by
      rw [hfun2]
      exact finiteComplexInner_reindex ρe (eigenCoords e (Z c)) (eigenCoords e (Z c))
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
  have hmain : ((ρ / (2 * Real.pi)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ | ∀ c,
          finitePureStateFidelity (radianOrbit pw (flowPhase ψw Elam t)) (z c) < a + 2 * ρ}
            ∩ Set.Ioc u (u + T))).toReal :=
    half_mul_le_measureReal_hardWindow (K := K) (d := d) (C := C) Ealg σ₀ Elam hE hρ hρπ hRK
      hposR hindep hT u hNbig hTbigK hpnn hpsum z hzunit hznorm ha r h22' ψw
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
                (fun i => spectralPhases e Ω i - t * lam i)) (eigenCoords e (Z c)) := by
        have hfun1 : radianOrbit pw (flowPhase ψw Elam t)
            = fun j => radianOrbit (spectralWeights e Ω)
                (fun i => spectralPhases e Ω i - t * lam i) (ρe.symm j) := by
          rw [hpw, hψw, hElam]
          rfl
        have hfun2 : z c = fun j => eigenCoords e (Z c) (ρe.symm j) := by rw [hz]
        rw [hfun1, hfun2]
        exact finitePureStateFidelity_reindex ρe
          (radianOrbit (spectralWeights e Ω) (fun i => spectralPhases e Ω i - t * lam i))
          (eigenCoords e (Z c))
      rw [hre, finitePureStateFidelity_radianOrbit_spectral heb Ω (Z c) t]
    rw [← hbridge]
    exact ht c

set_option maxHeartbeats 1000000 in
/-- **Theorem B's recurrence half for an integer matrix, in physical form.**  A traceless integer
Hermitian matrix whose characteristic polynomial is irreducible with the full symmetric Galois group
returns projectively to its initial state on a definite fraction of every long enough window. -/
theorem half_mul_le_measureReal_recurrenceWindow_physical
    {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (hcard : Fintype.card ι = d + 1) (Hz : Matrix ι ι ℤ)
    (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
    (hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)))
    (hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (d + 1).factorial)
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) {R T : ℝ} {N : ℕ}
    (hRbd : ∀ i, |hH.eigenvalues i| ≤ R)
    (hTbig : 8 * ((N : ℝ) + 1) ^ d
      ≤ T * ((2 * (d : ℝ) * (N : ℝ) * R) ^ ((d + 1).factorial - 1))⁻¹)
    {Ω : ι → ℂ} (hΩ : finiteComplexInner Ω Ω = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hposR : 0 < 2 * (d : ℝ) * (N : ℝ) * R) (hT : 0 < T)
    (hNbig : 8 * Real.pi * (d : ℝ)
      ≤ δ * (δ / (2 * Real.pi)) ^ d * Real.sqrt ((N : ℝ) + 1))
    (u : ℝ) :
    ((δ / (2 * Real.pi)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ | ∃ β : ℝ,
          ‖(WithLp.toLp 2 (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω)
              : EuclideanSpace ℂ ι)
            - Complex.exp ((β : ℂ) * Complex.I) • (WithLp.toLp 2 Ω : EuclideanSpace ℂ ι)‖ ≤ δ}
            ∩ Set.Ioc u (u + T))).toReal := by
  classical
  obtain ⟨K, instF, instA, instN, Ealg, σ₀, ρe, hmatch, hRK, hindep, hTbigK⟩ :=
    exists_algebraic_spectrum_package hcard Hz hH hirr hgal hd1 htr hRbd hTbig
  set e : ι → ι → ℂ := hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH with he
  set lam : ι → ℝ := hH.eigenvalues with hlam
  have heb : IsOrthoEigenBasis (Hz.map (Int.castRingHom ℂ)) e lam :=
    isOrthoEigenBasis_hermitian _ hH
  obtain ⟨Elam, hElam⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => lam (ρe.symm j) := ⟨_, rfl⟩
  obtain ⟨pw, hpw⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => spectralWeights e Ω (ρe.symm j) :=
    ⟨_, rfl⟩
  obtain ⟨ψw, hψw⟩ : ∃ f : Fin (d + 1) → ℝ, f = fun j => spectralPhases e Ω (ρe.symm j) :=
    ⟨_, rfl⟩
  have hE : ∀ j, ((Elam j : ℝ) : ℂ) = σ₀ ((Ealg j : 𝓞 K) : K) := by
    intro j
    have hj := hmatch (ρe.symm j)
    rw [hElam]
    simpa using hj
  have hpnn : ∀ j, 0 ≤ pw j := by
    intro j
    rw [hpw]
    exact spectralWeights_nonneg e Ω _
  have hpsum : ∑ j, pw j ≤ 1 := by
    have hsum : ∑ j, pw j = ∑ i, spectralWeights e Ω i := by
      rw [hpw]
      exact Fintype.sum_equiv ρe.symm (fun j => spectralWeights e Ω (ρe.symm j))
        (spectralWeights e Ω) (fun _ => rfl)
    rw [hsum, sum_spectralWeights heb hΩ]
  have hmain : ((δ / (2 * Real.pi)) ^ d / 2) * T
      ≤ (MeasureTheory.volume ({t : ℝ |
          ‖(WithLp.toLp 2 (radianOrbit pw (flowPhase ψw Elam t))
              : EuclideanSpace ℂ (Fin (d + 1)))
            - Complex.exp (((-(t * Elam 0) : ℝ) : ℂ) * Complex.I) •
              (WithLp.toLp 2 (radianOrbit pw ψw) : EuclideanSpace ℂ (Fin (d + 1)))‖ ≤ δ}
            ∩ Set.Ioc u (u + T))).toReal :=
    half_mul_le_measureReal_recurrenceWindow (K := K) (d := d) Ealg σ₀ Elam hE hδ hδπ hRK
      hposR hindep hT u hNbig hTbigK hpnn hpsum ψw
  refine le_trans hmain (ENNReal.toReal_mono ?_ ?_)
  · refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · refine MeasureTheory.measure_mono (Set.inter_subset_inter_left _ fun t ht => ?_)
    simp only [Set.mem_setOf_eq] at ht
    refine ⟨-(t * Elam 0), ?_⟩
    set cc : ℂ := Complex.exp (((-(t * Elam 0) : ℝ) : ℂ) * Complex.I) with hcc
    have hfun1 : radianOrbit pw (flowPhase ψw Elam t)
        = fun j => eigenCoords e (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω)
            (ρe.symm j) := by
      rw [hpw, hψw, hElam, ← radianOrbit_spectral_eq_eigenCoords heb Ω t]
      rfl
    have hfun2 : radianOrbit pw ψw = fun j => eigenCoords e Ω (ρe.symm j) := by
      rw [hpw, hψw, ← radianOrbit_spectral_zero e Ω]
      rfl
    rw [hfun1, hfun2] at ht
    have hcollapse : ((WithLp.toLp 2
          (fun j => eigenCoords e (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω)
            (ρe.symm j)) : EuclideanSpace ℂ (Fin (d + 1)))
          - cc • (WithLp.toLp 2 (fun j => eigenCoords e Ω (ρe.symm j))
              : EuclideanSpace ℂ (Fin (d + 1))))
        = WithLp.toLp 2 (fun j =>
            (fun i => eigenCoords e (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) i
              - cc * eigenCoords e Ω i) (ρe.symm j)) := PiLp.ext fun _ => rfl
    rw [hcollapse, norm_toLp_reindex ρe
        (fun i => eigenCoords e (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) i
          - cc * eigenCoords e Ω i),
      eigenCoords_sub_smul e (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) Ω cc,
      norm_toLp_eigenCoords heb] at ht
    have hfinal : ((WithLp.toLp 2 (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω)
          : EuclideanSpace ℂ ι) - cc • (WithLp.toLp 2 Ω : EuclideanSpace ℂ ι))
        = WithLp.toLp 2 (fun x =>
            (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ Ω) x - cc * Ω x) :=
      PiLp.ext fun _ => rfl
    rw [hfinal]
    exact ht

/-- **Rigidity gives maximal projective energy.**  A balanced integer relation among the eigenvalues
is a rational relation whose coefficient vector must be constant, and balancedness forces the
constant to vanish. -/
theorem maximallyProjectiveEnergy_of_ker_eq_constLine {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {lam : ι → ℝ}
    (hker : LinearMap.ker (SpectralExp.relationForm (fun i => ((lam i : ℝ) : ℂ)))
      = PermSubspace.constLine (K := ℚ) (ι := ι)) :
    MaximallyProjectiveEnergy lam := by
  classical
  intro k hbal hzero
  set a : ι → ℚ := fun i => ((k i : ℤ) : ℚ) with ha
  have hmem : a ∈ LinearMap.ker (SpectralExp.relationForm (fun i => ((lam i : ℝ) : ℂ))) := by
    rw [LinearMap.mem_ker, SpectralExp.relationForm_apply]
    have hC : ∑ i, (a i : ℚ) • ((lam i : ℝ) : ℂ)
        = (((∑ i, (k i : ℝ) * lam i : ℝ)) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha, Rat.smul_def]
      push_cast
      ring
    rw [hC, hzero]
    simp
  rw [hker] at hmem
  obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine hmem
  have hsum : (Fintype.card ι : ℚ) * c = 0 := by
    have hs : ∑ i, a i = ∑ i : ι, c := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun hc i
      exact this
    have hbalQ : ∑ i, a i = 0 := by
      rw [ha]
      have : ((∑ i, k i : ℤ) : ℚ) = 0 := by rw [hbal]; simp
      rw [← this]
      push_cast
      rfl
    rw [hbalQ] at hs
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    exact hs.symm
  have hcard : (Fintype.card ι : ℚ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    have hne : (Fintype.card ι : ℕ) ≠ 0 := by omega
    exact_mod_cast hne
  have hc0 : c = 0 := (mul_eq_zero.mp hsum).resolve_left hcard
  funext i
  have hi := congrFun hc i
  rw [hc0] at hi
  have : ((k i : ℤ) : ℚ) = 0 := hi
  exact_mod_cast this

/-- **The eigenvalues of a traceless integer matrix with symmetric Galois group are rationally
rigid.** -/
theorem ker_relationForm_eq_constLine_of_integer_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (hcard : Fintype.card ι = d + 1) (Hz : Matrix ι ι ℤ)
    (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
    (hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)))
    (hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (d + 1).factorial)
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) :
    LinearMap.ker (SpectralExp.relationForm (fun i => ((hH.eigenvalues i : ℝ) : ℂ)))
      = PermSubspace.constLine (K := ℚ) (ι := ι) := by
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
  exact ker_relationForm_eq_constLine_of_gal hmonic hirr hdeg hd1 hcoeff hgal hEinj hEprod

/-- **A traceless integer matrix with symmetric Galois group has maximal projective energy.** -/
theorem maximallyProjectiveEnergy_of_integer_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (hcard : Fintype.card ι = d + 1) (Hz : Matrix ι ι ℤ)
    (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
    (hirr : Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)))
    (hgal : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (d + 1).factorial)
    (hd1 : 1 < d + 1) (htr : Hz.trace = 0) :
    MaximallyProjectiveEnergy hH.eigenvalues := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact maximallyProjectiveEnergy_of_ker_eq_constLine
    (ker_relationForm_eq_constLine_of_integer_matrix hcard Hz hH hirr hgal hd1 htr)

/-- Maximal projective energy transports along a relabelling. -/
theorem maximallyProjectiveEnergy_reindex {ι J : Type} [Fintype ι] [Fintype J] (ρ : ι ≃ J)
    {lam : ι → ℝ} (h : MaximallyProjectiveEnergy lam) :
    MaximallyProjectiveEnergy (fun j => lam (ρ.symm j)) := by
  classical
  intro k hbal hzero
  have hk' : (fun i => k (ρ i)) = 0 := by
    refine h (fun i => k (ρ i)) ?_ ?_
    · show ∑ i, k (ρ i) = 0
      rw [Fintype.sum_equiv ρ (fun i => k (ρ i)) k (fun _ => rfl)]
      exact hbal
    · show ∑ i, ((k (ρ i) : ℤ) : ℝ) * lam i = 0
      rw [Fintype.sum_equiv ρ (fun i => ((k (ρ i) : ℤ) : ℝ) * lam i)
        (fun j => ((k j : ℤ) : ℝ) * lam (ρ.symm j)) (fun i => by simp)]
      exact hzero
  funext j
  have := congrFun hk' (ρ.symm j)
  simpa using this

end

end GaloisForLFunctions.HTGeometry
