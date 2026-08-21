/-
# Almost every nearest-neighbour direction is maximally projective

The endpoint-complete Pauli seed is one Hamiltonian of the nearest-neighbour family whose spectrum
admits no nonzero balanced integer relation.  The one-witness genericity theorem for a polynomial
Hermitian family then makes that property hold outside a Lebesgue-null cone, hence almost everywhere
on the coefficient shell.

Main results:
* `charpoly_unitary_conj_diagonal` — a rectangular unitary conjugation preserves the characteristic
  polynomial.
* `exists_chainShell_maximallyProjective_witness` — the seed, in chain coordinates.
* `maximallyProjectiveEnergy_chainShell_ae` — **almost every shell direction is maximally
  projective**.
-/
import GaloisForLFunctions.HTGeometry.PauliChainSpanWitness
import GaloisForLFunctions.HTGeometry.SpanCoordinateJunction
import GaloisForLFunctions.HTGeometry.ShellFamilySimpleSpectrum
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity
import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.OneKnobSpectralActivationLaw
import GaloisForLFunctions.HTGeometry.ShellQuadraticRateWitness
import GaloisForLFunctions.HTGeometry.SeedOrbitRecurrence

open Matrix MeasureTheory Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- **A rectangular unitary conjugation preserves the characteristic polynomial.** -/
theorem charpoly_unitary_conj_diagonal {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I]
    {U : Matrix P I ℂ} (hUleft : Uᴴ * U = (1 : Matrix I I ℂ))
    (hUright : U * Uᴴ = (1 : Matrix P P ℂ)) (E : I → ℂ) :
    (U * Matrix.diagonal E * Uᴴ).charpoly = (Matrix.diagonal E).charpoly := by
  have hrecover : U * Matrix.diagonal E * Uᴴ
      = U * Matrix.diagonal E * Uᴴ := rfl
  have hconj : (unitaryMulVecEquiv hUleft hUright).conj (Matrix.diagonal E).mulVecLin
      = (U * Matrix.diagonal E * Uᴴ).mulVecLin := by
    apply LinearMap.ext
    intro v
    change U *ᵥ (Matrix.diagonal E *ᵥ (Uᴴ *ᵥ v)) = _ *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  calc (U * Matrix.diagonal E * Uᴴ).charpoly
      = (U * Matrix.diagonal E * Uᴴ).mulVecLin.charpoly :=
        (Matrix.charpoly_mulVecLin _).symm
    _ = ((unitaryMulVecEquiv hUleft hUright).conj (Matrix.diagonal E).mulVecLin).charpoly := by
        rw [hconj]
    _ = (Matrix.diagonal E).mulVecLin.charpoly :=
        (unitaryMulVecEquiv hUleft hUright).charpoly_conj _
    _ = (Matrix.diagonal E).charpoly := Matrix.charpoly_mulVecLin _

theorem matrixCharpolyRelation_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℂ) (i : I) : matrixCharpolyRelation (Matrix.diagonal E, E i) = 0 := by
  show (Matrix.scalar I (E i) - Matrix.diagonal E).det = 0
  have hd : (Matrix.scalar I (E i) - Matrix.diagonal E)
      = Matrix.diagonal (fun j => E i - E j) := by
    ext x y
    by_cases h : x = y
    · subst h
      simp [Matrix.scalar, Matrix.diagonal]
    · simp [Matrix.scalar_apply, h]
  rw [hd, Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)

/-- The numbering of the seed spectrum of the `(k+3)`-qubit stage. -/
def seedSpectrumFin (k : ℕ) : seedIndex (k + 1) ≃ Fin (2 ^ (k + 3)) :=
  Fintype.equivFinOfCardEq (card_seedIndex (k + 1))

/-- **The seed, in chain coordinates.** -/
theorem exists_chainShell_maximallyProjective_witness (k : ℕ) :
    ∃ θ₀ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ,
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues := by
  classical
  obtain ⟨E, U, V, hEmax, hEsum, hUleft, hUright, hVherm, hVspan, hHspan, hVtrans⟩ :=
    exists_pauliChainSeed (k + 1)
  obtain ⟨θ₀, hθ₀⟩ := exists_realCoeff_of_mem_span (chainPauliFin (k + 3))
    (reindexFin_mem_span_range_chainPauliFin hHspan)
  have hEq : spectralEnsembleMatrix (chainPauliFin (k + 3)) θ₀
      = Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
        (U * Matrix.diagonal (fun i => (E i : ℂ)) * Uᴴ) := hθ₀.symm
  refine ⟨θ₀, ?_⟩
  refine maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket _
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ₀)
    (fun j => E ((seedSpectrumFin k).symm j))
    (maximallyProjectiveEnergy_equiv (seedSpectrumFin k).symm hEmax) ?_
  intro j
  show (Matrix.scalar _ ((E ((seedSpectrumFin k).symm j) : ℝ) : ℂ)
    - spectralEnsembleMatrix (chainPauliFin (k + 3)) θ₀).det = 0
  rw [← Matrix.eval_charpoly, hEq, Matrix.charpoly_reindex,
    charpoly_unitary_conj_diagonal hUleft hUright, Matrix.eval_charpoly]
  exact matrixCharpolyRelation_diagonal (fun i => (E i : ℂ)) ((seedSpectrumFin k).symm j)

/-! ## Almost every shell direction -/

theorem measurableSet_polynomialMatrixProjectiveGenericSet_compl {m : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (M : Matrix I I (MvPolynomial (Fin m) ℂ)) :
    MeasurableSet (polynomialMatrixProjectiveGenericSet M)ᶜ := by
  classical
  have hcont : ∀ Q : MvPolynomial (Fin m) ℂ,
      Continuous fun p : Fin m → ℝ =>
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) Q := by
    intro Q
    have h1 : (fun p : Fin m → ℝ =>
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) Q)
        = (fun z : Fin m → ℂ => MvPolynomial.eval z Q) ∘
          (fun p : Fin m → ℝ => fun t => ((p t : ℝ) : ℂ)) := rfl
    rw [h1]
    refine (MvPolynomial.continuous_eval Q).comp ?_
    exact continuous_pi fun t => Complex.continuous_ofReal.comp (continuous_apply t)
  have hEq : (polynomialMatrixProjectiveGenericSet M)ᶜ
      = ⋃ k : I → ℤ, {p : Fin m → ℝ |
          (SpectralCharacterBalanced k ∧ k ≠ 0) ∧
          MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
            (complexSpectralCoefficientObstructionPullback
              (matrixCharacteristicElementaryPolynomial M) k) = 0} := by
    ext p
    constructor
    · intro hp
      have hp' : ¬ ∀ k : I → ℤ, SpectralCharacterBalanced k → k ≠ 0 →
          MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
            (complexSpectralCoefficientObstructionPullback
              (matrixCharacteristicElementaryPolynomial M) k) ≠ 0 := hp
      push Not at hp'
      obtain ⟨k, hb, hk, hz⟩ := hp'
      exact Set.mem_iUnion.mpr ⟨k, ⟨hb, hk⟩, hz⟩
    · intro hp hcon
      obtain ⟨k, ⟨hb, hk⟩, hz⟩ := Set.mem_iUnion.mp hp
      exact hcon k hb hk hz
  rw [hEq]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hk : SpectralCharacterBalanced k ∧ k ≠ 0
  · have hset : {p : Fin m → ℝ |
        (SpectralCharacterBalanced k ∧ k ≠ 0) ∧
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
          (complexSpectralCoefficientObstructionPullback
            (matrixCharacteristicElementaryPolynomial M) k) = 0}
        = {p : Fin m → ℝ |
          MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
            (complexSpectralCoefficientObstructionPullback
              (matrixCharacteristicElementaryPolynomial M) k) = 0} := by
      ext p
      simp [hk]
    rw [hset]
    exact (hcont _).measurable (measurableSet_singleton (0 : ℂ))
  · have hset : {p : Fin m → ℝ |
        (SpectralCharacterBalanced k ∧ k ≠ 0) ∧
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
          (complexSpectralCoefficientObstructionPullback
            (matrixCharacteristicElementaryPolynomial M) k) = 0} = ∅ := by
      ext p
      simp [hk]
    rw [hset]
    exact MeasurableSet.empty

variable {N D : ℕ}

theorem map_spectralGenericMatrix_eq {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (θ : Fin N → ℝ) :
    (spectralGenericMatrix P).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => ((θ t : ℝ) : ℂ)))
      = spectralEnsembleMatrix P θ := by
  rw [← mapMatrix_spectralGenericMatrix P θ]
  rfl

theorem mem_genericSet_iff_maximallyProjective {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    θ ∈ polynomialMatrixProjectiveGenericSet (spectralGenericMatrix P)
      ↔ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  have hH : ((spectralGenericMatrix P).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => ((θ t : ℝ) : ℂ)))).IsHermitian := by
    rw [map_spectralGenericMatrix_eq θ]
    exact isHermitian_spectralEnsembleMatrix hP θ
  have hev : hH.eigenvalues = (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues :=
    eigenvalues_congr_of_eq hH (isHermitian_spectralEnsembleMatrix hP θ)
      (map_spectralGenericMatrix_eq θ)
  constructor
  · intro hmem
    rw [← hev]
    exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet _ θ hmem hH
  · intro hmax
    refine mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective _ θ hH ?_
    rw [hev]
    exact hmax

theorem maximallyProjectiveEnergy_spectralEnsemble_smul_iff
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : t ≠ 0)
    (θ : Fin N → ℝ) :
    MaximallyProjectiveEnergy
        (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues
      ↔ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  have hsm : (spectralEnsembleMatrix P fun a => t * θ a)
      = ((t : ℂ)) • spectralEnsembleMatrix P θ := spectralEnsembleMatrix_smul P t θ
  have hherm : (((t : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian := by
    rw [← hsm]
    exact isHermitian_spectralEnsembleMatrix hP _
  have hev : (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues
      = hherm.eigenvalues :=
    eigenvalues_congr_of_eq (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)) hherm hsm
  rw [hev]
  have hscaled : ((t⁻¹ : ℝ) : ℂ) • (((t : ℂ)) • spectralEnsembleMatrix P θ)
      = spectralEnsembleMatrix P θ := by
    rw [smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
  have hh2 : (((t⁻¹ : ℝ) : ℂ) • (((t : ℂ)) • spectralEnsembleMatrix P θ)).IsHermitian := by
    rw [hscaled]
    exact isHermitian_spectralEnsembleMatrix hP θ
  constructor
  · intro hmax
    have hback := maximallyProjectiveEnergy_eigenvalues_real_smul
      (((t : ℂ)) • spectralEnsembleMatrix P θ) hherm (c := t⁻¹) (inv_ne_zero ht) hh2 hmax
    rw [eigenvalues_congr_of_eq (isHermitian_spectralEnsembleMatrix hP θ) hh2 hscaled.symm]
    exact hback
  · intro hmax
    exact maximallyProjectiveEnergy_eigenvalues_real_smul (spectralEnsembleMatrix P θ)
      (isHermitian_spectralEnsembleMatrix hP θ) ht hherm hmax

/-- **Almost every direction of the nearest-neighbour shell is maximally projective.** -/
theorem maximallyProjectiveEnergy_chainShell_ae (k : ℕ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (k + 3))))),
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues := by
  classical
  obtain ⟨θ₀, hθ₀⟩ := exists_chainShell_maximallyProjective_witness k
  have hBadEq : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}
      = (polynomialMatrixProjectiveGenericSet
          (spectralGenericMatrix (chainPauliFin (k + 3))))ᶜ := by
    ext θ
    exact not_congr (mem_genericSet_iff_maximallyProjective
      (chainPauliFin_isHermitian (k + 3)) θ).symm
  have hBadmeas : MeasurableSet {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := by
    rw [hBadEq]
    exact measurableSet_polynomialMatrixProjectiveGenericSet_compl _
  have hBadnull : (volume : Measure (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ))
      {θ | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} = 0 := by
    rw [hBadEq]
    refine (polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
      (spectralGenericMatrix (chainPauliFin (k + 3))) θ₀
      (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues
      hθ₀ hθ₀.injective ?_).2.2
    intro i
    show (Matrix.scalar _ (((isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3)) θ₀).eigenvalues i : ℝ) : ℂ)
        - (spectralGenericMatrix (chainPauliFin (k + 3))).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => ((θ₀ t : ℝ) : ℂ)))).det = 0
    rw [map_spectralGenericMatrix_eq θ₀]
    exact charpolyRelation_eigenvalues
      (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ₀) i
  have hEBadnull : (volume : Measure (EuclideanSpace ℝ
      (Fin (Fintype.card (ChainLabel (k + 3))))))
      {x | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues} = 0 := by
    have hmp := PiLp.volume_preserving_ofLp (Fin (Fintype.card (ChainLabel (k + 3))))
    have hpre : {x : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues}
        = WithLp.ofLp ⁻¹' {θ | ¬ MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} :=
      rfl
    rw [hpre, hmp.measure_preimage hBadmeas.nullMeasurableSet, hBadnull]
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ {x : EuclideanSpace ℝ
      (Fin (Fintype.card (ChainLabel (k + 3)))) |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues},
      r • x ∈ {x : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues} := by
    intro r hr x hx hmax
    refine hx ?_
    have hofLp : (WithLp.ofLp (r • x)) = fun i => r * (WithLp.ofLp x) i := rfl
    rw [hofLp] at hmax
    exact (maximallyProjectiveEnergy_spectralEnsemble_smul_iff
      (chainPauliFin_isHermitian (k + 3)) hr.ne' (WithLp.ofLp x)).mp hmax
  have hsphere : (volume : Measure (EuclideanSpace ℝ
      (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere
      (shellCoefficientMap (Fin (Fintype.card (ChainLabel (k + 3)))) ⁻¹'
        {θ | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}) = 0 := by
    refine toSphere_eq_zero_of_scaleInvariant hEBadnull hcone
      (hBadmeas.preimage measurable_shellCoefficientMap) ?_
    intro θ hθ
    exact hθ
  rw [Filter.eventually_iff, mem_ae_iff]
  have hcompl : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}ᶜ
      = {θ | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := rfl
  rw [hcompl, shellProbability, Measure.smul_apply, shellCoefficientMeasure,
    Measure.map_apply measurable_shellCoefficientMap hBadmeas, hsphere, smul_eq_mul, mul_zero]

/-- **Almost every nearest-neighbour direction has a seed recurrence at arbitrarily late times.**
This is item 3 of the low--plateau--recurrence trajectory: after any prescribed time the orbit of
the seed returns to within `ρ` of the seed itself. -/
theorem ae_exists_late_seed_recurrence_chainShell (k : ℕ)
    (Om : Fin (2 ^ (k + 3)) → ℂ) (hOm : finiteComplexInner Om Om = 1)
    (i₀ : Fin (2 ^ (k + 3))) {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (k + 3))))),
      ∃ s : ℝ, A < s ∧ 1 - ρ ≤ ‖finiteComplexInner
        (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) θ) s *ᵥ Om) Om‖ := by
  filter_upwards [maximallyProjectiveEnergy_chainShell_ae k] with θ hmax
  exact exists_late_seed_recurrence
    (isOrthoEigenBasis_hermitian _
      (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ))
    hmax.injective hmax i₀ Om hOm hρ A

end GaloisForLFunctions.HTGeometry

end
