import GaloisForLFunctions.RHTower.StaticChoiFullStateProjectionLaw

/-!
# Operational trace-distance form of the static Choi law

The full-state plateau theorem is first obtained in Hilbert--Schmidt density
geometry. This file closes the operational metric gap for physical circuit
targets. It proves from coordinates that Hilbert--Schmidt distance between
normalized pure-state densities is exactly `sqrt 2` times pure-state trace
distance, identifies the static diagonal-unitary Choi density with the density
of its normalized Choi vector, and transfers the syndetic hardness law without
dimension loss.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Rank-one density coordinates of a finite pure state. -/
def pureStateDensity {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun ij ↦ ψ ij.1 * starRingEnd ℂ (ψ ij.2)

@[simp] theorem pureStateDensity_apply {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) (ij : ι × ι) :
    pureStateDensity ψ ij = ψ ij.1 * starRingEnd ℂ (ψ ij.2) := rfl

theorem norm_pureStateDensity_sq {ι : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) :
    ‖pureStateDensity ψ‖ ^ (2 : ℕ) = ‖ψ‖ ^ (4 : ℕ) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [pureStateDensity_apply, norm_mul, RCLike.norm_conj, mul_pow]
  rw [← Fintype.sum_mul_sum, ← EuclideanSpace.norm_sq_eq]
  ring

theorem inner_pureStateDensity {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) :
    inner ℂ (pureStateDensity ψ) (pureStateDensity φ) =
      (‖inner ℂ ψ φ‖ ^ (2 : ℕ) : ℂ) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, pureStateDensity_apply, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  have hfactor (i j : ι) :
      φ i * starRingEnd ℂ (φ j) *
          (starRingEnd ℂ (ψ i) * ψ j) =
        (φ i * starRingEnd ℂ (ψ i)) *
          (ψ j * starRingEnd ℂ (φ j)) := by ring
  change
    (∑ i, ∑ j,
      φ i * starRingEnd ℂ (φ j) *
        starRingEnd ℂ (ψ i * starRingEnd ℂ (ψ j))) =
      (‖inner ℂ ψ φ‖ ^ (2 : ℕ) : ℂ)
  simp_rw [map_mul]
  simp_rw [starRingEnd_self_apply]
  simp_rw [hfactor]
  rw [← Fintype.sum_mul_sum]
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ i, φ i * starRingEnd ℂ (ψ i)) *
        (∑ j, ψ j * starRingEnd ℂ (φ j)) =
      (‖∑ i, φ i * starRingEnd ℂ (ψ i)‖ ^ (2 : ℕ) : ℂ)
  rw [show (∑ j, ψ j * starRingEnd ℂ (φ j)) =
      starRingEnd ℂ (∑ i, φ i * starRingEnd ℂ (ψ i)) by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul, starRingEnd_self_apply]
        ring]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_num

/-- Trace distance between normalized pure states, in its fidelity form. -/
def pureStateTraceDistance {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) : ℝ :=
  Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ (2 : ℕ))

theorem dist_pureStateDensity_sq {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    dist (pureStateDensity ψ) (pureStateDensity φ) ^ (2 : ℕ) =
      2 * (1 - ‖inner ℂ ψ φ‖ ^ (2 : ℕ)) := by
  rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), norm_pureStateDensity_sq,
    norm_pureStateDensity_sq, inner_pureStateDensity]
  change ‖ψ‖ ^ (4 : ℕ) - 2 * (((‖inner ℂ ψ φ‖ : ℂ) ^ (2 : ℕ)).re) + ‖φ‖ ^ (4 : ℕ) =
    2 * (1 - ‖inner ℂ ψ φ‖ ^ (2 : ℕ))
  simp [hψ, hφ, pow_two, Complex.mul_re]
  ring

theorem pureStateTraceDistance_nonneg {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) :
    0 ≤ pureStateTraceDistance ψ φ :=
  Real.sqrt_nonneg _

/-- For normalized pure states, Hilbert--Schmidt density distance is exactly
`sqrt 2` times operational trace distance. -/
theorem dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
    {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    dist (pureStateDensity ψ) (pureStateDensity φ) =
      Real.sqrt 2 * pureStateTraceDistance ψ φ := by
  have hid := dist_pureStateDensity_sq ψ φ hψ hφ
  have hdeficit : 0 ≤ 1 - ‖inner ℂ ψ φ‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (dist (pureStateDensity ψ) (pureStateDensity φ))]
  apply (sq_eq_sq₀ dist_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (pureStateTraceDistance_nonneg ψ φ))).mp
  rw [hid, mul_pow, pureStateTraceDistance, Real.sq_sqrt (by norm_num),
    Real.sq_sqrt hdeficit]

theorem pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist
    {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateTraceDistance ψ φ =
      (Real.sqrt 2)⁻¹ * dist (pureStateDensity ψ) (pureStateDensity φ) := by
  rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance ψ φ hψ hφ]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- Normalized Choi vector of a diagonal unitary in its spectral basis. -/
def fullUniformPhaseChoiVector (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij ↦
    if ij.1 = ij.2 then
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x ij.1)
    else 0

@[simp] theorem fullUniformPhaseChoiVector_apply
    (d : ℕ) (x : Fin d → UnitAddCircle) (ij : Fin d × Fin d) :
    fullUniformPhaseChoiVector d x ij =
      if ij.1 = ij.2 then
        ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x ij.1)
      else 0 := rfl

theorem fullUniformPhaseChoiVector_norm
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    ‖fullUniformPhaseChoiVector d x‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [fullUniformPhaseChoiVector_apply]
  simp_rw [apply_ite (fun z : ℂ ↦ ‖z‖), norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, fourier_apply, Circle.norm_coe]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdR)
  simp only [norm_zero, mul_one, one_pow]
  have hsum (i : Fin d) :
      (∑ j : Fin d,
        (if i = j then |Real.sqrt (d : ℝ)|⁻¹ else 0) ^ (2 : ℕ)) =
        |Real.sqrt (d : ℝ)|⁻¹ ^ (2 : ℕ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  simp_rw [hsum]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [abs_of_pos (Real.sqrt_pos.2 hdR), inv_pow]
  rw [show (Real.sqrt (d : ℝ)) ^ (2 : ℕ) = (d : ℝ) by
    exact Real.sq_sqrt hdR.le]
  field_simp

theorem pureStateDensity_fullUniformPhaseChoiVector
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    pureStateDensity (fullUniformPhaseChoiVector d x) =
      fullUniformPhaseChoiDensity d x := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdR)
  have hreal : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    field_simp [hsqrt]
    simpa [pow_two] using (Real.mul_self_sqrt hdR.le).symm
  have hcoef :
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) =
        ((d : ℝ)⁻¹ : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, map_inv₀, Complex.conj_ofReal]
    exact_mod_cast hreal
  ext pq
  simp only [pureStateDensity_apply, fullUniformPhaseChoiVector_apply,
    fullUniformPhaseChoiDensity]
  by_cases h1 : pq.1.1 = pq.1.2 <;>
    by_cases h2 : pq.2.1 = pq.2.2
  · simp only [h1, h2, and_self, if_pos, map_mul]
    rw [show
      (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x pq.1.2)) *
          (starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) *
            starRingEnd ℂ (fourier 1 (x pq.2.2))) =
        ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
          fourier 1 (x pq.1.2) *
            starRingEnd ℂ (fourier 1 (x pq.2.2))) by ring,
      hcoef]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- **Operational trace-distance form of the syndetic Choi law.** Every
normalized pure circuit dictionary misses the exact static-Hamiltonian Choi
state by more than `ε` in pure-state trace distance in every interval of one
fixed finite length. -/
theorem maximallyProjective_pureChoiTraceHardTimes_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ (2 : ℕ)) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : PaddedCircuitWord gate s,
        ε < pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨L, hL, hhits⟩ :=
    maximallyProjective_fullChoiCircuitTargets_syndetic
      energy hmax s (fun w ↦ pureStateDensity (target w))
      (mul_pos hsqrt hε) hentropy
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, fun w ↦ ?_⟩
  let ψ := fullUniformPhaseChoiVector (d + 1)
    (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  have hψ : ‖ψ‖ = 1 :=
    fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _
  have hdist := hhard w
  rw [← pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d),
    dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance
      ψ (target w) hψ (htarget w)] at hdist
  nlinarith

end RHTower
