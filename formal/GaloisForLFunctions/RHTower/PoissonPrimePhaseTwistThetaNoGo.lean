import GaloisForLFunctions.RHTower.PoissonPrimeClockCommutator
import GaloisForLFunctions.RHTower.HardyTitchmarshSourceTransport
import GaloisForLFunctions.RHTower.HedenmalmThetaTrace
import GaloisForLFunctions.RHTower.HedenmalmCompactSourceEigenmode
import GaloisForLFunctions.RHTower.STCPrimeLogSquarePoleScaling

/-!
# Phase twists and the theta source inverse against the prime Poisson Calkin model

**Phase twists.**  For real `τ` the diagonal unitary `D_τ δ_p = p^{iτ} δ_p` commutes with every
diagonal clock multiplier.  The twisted kernel `K_τ = D_τ K D_τ*` has matrix
`p^{iτ} q^{-iτ} K(p,q)`, the same Weyl spectrum `[0, 4]` and essential norm `4` as `K`; its clock
commutator has matrix `(x_p - x_q) K_τ(p,q)` and essential norm at least `h(3)`; and no physical
column `t_p K_τ(p,q)` is square summable.  In particular an ordinate inserted only as a prime phase
changes none of these invariants.

**Theta source inverse.**  For every positive density source the compact source inverse
`B f(t) = i q(t) (∫_0^t f - t ∫_0^1 f)` is not self-adjoint: `B 1 = 0` while
`⟪1, B t⟫ = -(i/2) ∫ q(t) t(1-t) dt ≠ 0`.  Hence the theta source inverse, whose regularized
determinant vanishes exactly on the centred Xi divisor, is unitarily equivalent to no self-adjoint
operator, in particular not to the self-adjoint Hilbert–Schmidt defect `U K U* - W` of the prime
Poisson Calkin model.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### The kernel as an aperture aggregate -/

theorem exp_neg_half_stcClock (p : Nat.Primes) :
    Real.exp (-(stcClock p / 2)) = (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, ← Real.exp_neg, stcClock]
  ring_nf

/-- **All apertures aggregated with the Poisson half-density.**  With the literal depth-zero
Gamma–Euler amplitude `b_u(p) = log p · p^{-(1+u)/2}`,
`K(p,q) = ∫_0^∞ u b_u(p) b_u(q) du = 4 t_p t_q / (√(pq) (t_p + t_q)²)`. -/
theorem stcPrimePoissonKernel_eq_integral_aperture (p q : Nat.Primes) :
    stcPrimePoissonKernel p q =
      ∫ u in Ioi (0 : ℝ), u * (stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q) := by
  have hp := stcClock_pos' p
  have hq := stcClock_pos' q
  set c : ℝ := (stcClock p + stcClock q) / 2
  have hc : 0 < c := by positivity
  have hint : ∀ u, u * (stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q) =
      (stcClock p * stcClock q * Real.exp (-(stcClock p / 2)) * Real.exp (-(stcClock q / 2))) *
        (u * Real.exp (-(c * u))) := by
    intro u
    rw [stcDepthZeroAmplitude_eq_exp, stcDepthZeroAmplitude_eq_exp]
    have e : Real.exp (-((1 + u) / 2) * Real.log ((p : ℕ) : ℝ)) *
        Real.exp (-((1 + u) / 2) * Real.log ((q : ℕ) : ℝ)) =
        Real.exp (-(stcClock p / 2)) * Real.exp (-(stcClock q / 2)) * Real.exp (-(c * u)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [c, stcClock]
      ring
    change u * (stcClock p * Real.exp (-((1 + u) / 2) * Real.log ((p : ℕ) : ℝ)) *
      (stcClock q * Real.exp (-((1 + u) / 2) * Real.log ((q : ℕ) : ℝ)))) = _
    rw [show ∀ a b x y : ℝ, u * (a * x * (b * y)) = a * b * (x * y) * u from
      fun a b x y => by ring, e]
    ring
  simp_rw [hint]
  rw [integral_const_mul, integral_Ioi_mul_exp_neg hc, exp_neg_half_stcClock,
    exp_neg_half_stcClock, stcPrimePoissonKernel]
  have hsp : 0 < Real.sqrt ((p : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast p.prop.pos)
  have hsq : 0 < Real.sqrt ((q : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast q.prop.pos)
  simp only [c]
  field_simp
  ring

/-! ### Unitary conjugation -/

theorem mem_weylEssentialSpectrum_unitaryPush {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (u : H ≃ₗᵢ[ℂ] K)
    {T : H →L[ℂ] H} {c : ℂ} (hc : c ∈ weylEssentialSpectrum T) :
    c ∈ weylEssentialSpectrum (unitaryPush u T) := by
  obtain ⟨f, hf1, hfw, hT⟩ := hc
  refine ⟨fun n => u (f n), fun n => by rw [u.norm_map, hf1], fun ℓ => ?_, ?_⟩
  · simpa using hfw (ℓ ∘L (u : H →L[ℂ] K))
  · refine hT.congr fun n => ?_
    rw [← u.norm_map]
    simp

theorem unitaryPush_symm_unitaryPush' {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (u : H ≃ₗᵢ[ℂ] K)
    (T : H →L[ℂ] H) : unitaryPush u.symm (unitaryPush u T) = T := by
  ext x; simp

theorem isSelfAdjoint_unitaryPush {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (u : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) : IsSelfAdjoint (unitaryPush u T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, unitaryPush_apply]
  have hs := hT.isSymmetric (u.symm x) (u.symm y)
  simp only [ContinuousLinearMap.coe_coe] at hs
  calc inner ℂ (u (T (u.symm x))) y = inner ℂ (u (T (u.symm x))) (u (u.symm y)) := by
        rw [u.apply_symm_apply]
    _ = inner ℂ (T (u.symm x)) (u.symm y) := u.inner_map_map _ _
    _ = inner ℂ (u.symm x) (T (u.symm y)) := hs
    _ = inner ℂ (u (u.symm x)) (u (T (u.symm y))) := (u.inner_map_map _ _).symm
    _ = inner ℂ x (u (T (u.symm y))) := by rw [u.apply_symm_apply]

/-! ### The prime phase unitary -/

/-- The prime phase `p^{iτ}`. -/
def primePhase (τ : ℝ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)

theorem norm_primePhase (τ : ℝ) (p : Nat.Primes) : ‖primePhase τ p‖ = 1 := by
  rw [primePhase, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp

theorem primePhase_mul_neg (τ : ℝ) (p : Nat.Primes) : primePhase τ p * primePhase (-τ) p = 1 := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [primePhase, primePhase, ← Complex.cpow_add _ _ hp]
  push_cast
  ring_nf
  exact Complex.cpow_zero _

/-- The diagonal phase operator `D_τ δ_p = p^{iτ} δ_p`. -/
def phaseTwistOp (τ : ℝ) : ℓ²P →L[ℂ] ℓ²P :=
  LpDiagonal.lpDiag (primePhase τ) 1 zero_le_one fun p => (norm_primePhase τ p).le

theorem phaseTwistOp_coord (τ : ℝ) (f : ℓ²P) (p : Nat.Primes) :
    (phaseTwistOp τ f : Nat.Primes → ℂ) p = primePhase τ p * (f : Nat.Primes → ℂ) p := by
  rw [phaseTwistOp, LpDiagonal.lpDiag_coe]

theorem phaseTwistOp_neg_apply (τ : ℝ) (f : ℓ²P) : phaseTwistOp τ (phaseTwistOp (-τ) f) = f := by
  ext p
  rw [phaseTwistOp_coord, phaseTwistOp_coord, ← mul_assoc, primePhase_mul_neg, one_mul]

theorem norm_phaseTwistOp_apply (τ : ℝ) (f : ℓ²P) : ‖phaseTwistOp τ f‖ = ‖f‖ := by
  have h1 := HilbertSchmidt.lp_norm_sq_eq (phaseTwistOp τ f)
  have h2 := HilbertSchmidt.lp_norm_sq_eq f
  have : ‖phaseTwistOp τ f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [h1, h2]
    refine tsum_congr fun p => ?_
    rw [phaseTwistOp_coord, norm_mul, norm_primePhase, one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The prime phase unitary `D_τ`. -/
def phaseTwistEquiv (τ : ℝ) : ℓ²P ≃ₗᵢ[ℂ] ℓ²P :=
  { toLinearEquiv := LinearEquiv.ofLinear (phaseTwistOp τ : ℓ²P →ₗ[ℂ] ℓ²P)
      (phaseTwistOp (-τ) : ℓ²P →ₗ[ℂ] ℓ²P)
      (LinearMap.ext fun f => phaseTwistOp_neg_apply τ f)
      (LinearMap.ext fun f => by
        have := phaseTwistOp_neg_apply (-τ) f
        rw [neg_neg] at this
        exact this)
    norm_map' := norm_phaseTwistOp_apply τ }

theorem phaseTwistEquiv_apply (τ : ℝ) (f : ℓ²P) : phaseTwistEquiv τ f = phaseTwistOp τ f := rfl

theorem phaseTwistEquiv_symm_apply (τ : ℝ) (f : ℓ²P) :
    (phaseTwistEquiv τ).symm f = phaseTwistOp (-τ) f := rfl

theorem phaseTwistOp_lpBasisVec (τ : ℝ) (q : Nat.Primes) :
    phaseTwistOp τ (lpBasisVec q) = primePhase τ q • lpBasisVec q := by
  classical
  ext p
  rw [phaseTwistOp_coord, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lpBasisVec, lp.single_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-- Conjugation of a matrix by the phase unitary. -/
theorem hasLpMatrix_unitaryPush_phaseTwist {T : ℓ²P →L[ℂ] ℓ²P} {M : Nat.Primes → Nat.Primes → ℂ}
    (hT : HasLpMatrix T M) (τ : ℝ) :
    HasLpMatrix (unitaryPush (phaseTwistEquiv τ) T)
      fun p q => primePhase τ p * primePhase (-τ) q * M p q := by
  intro p q
  rw [unitaryPush_apply, phaseTwistEquiv_symm_apply, phaseTwistEquiv_apply, phaseTwistOp_coord,
    phaseTwistOp_lpBasisVec, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hT p q]
  ring

/-- The phase-twisted prime Poisson operator `K_τ = D_τ K D_τ*`. -/
def twistedPoissonPrimeOp (τ : ℝ) : ℓ²P →L[ℂ] ℓ²P := unitaryPush (phaseTwistEquiv τ) poissonPrimeOp

/-- The phase-twisted clock commutator `C_τ = D_τ C D_τ*`. -/
def twistedPoissonPrimeCommOp (τ : ℝ) : ℓ²P →L[ℂ] ℓ²P :=
  unitaryPush (phaseTwistEquiv τ) poissonPrimeCommOp

theorem hasLpMatrix_twistedPoissonPrimeOp (τ : ℝ) :
    HasLpMatrix (twistedPoissonPrimeOp τ) fun p q =>
      primePhase τ p * primePhase (-τ) q * (stcPrimePoissonKernel p q : ℂ) :=
  hasLpMatrix_unitaryPush_phaseTwist hasLpMatrix_poissonPrimeOp τ

/-- **The twisted commutator is the clock commutator of the twisted kernel.** -/
theorem hasLpMatrix_twistedPoissonPrimeCommOp (τ : ℝ) :
    HasLpMatrix (twistedPoissonPrimeCommOp τ) fun p q =>
      ((mertensPrimeClock p : ℂ) - mertensPrimeClock q) *
        (primePhase τ p * primePhase (-τ) q * (stcPrimePoissonKernel p q : ℂ)) :=
  (hasLpMatrix_unitaryPush_phaseTwist hasLpMatrix_poissonPrimeCommOp τ).congr fun p q => by ring

/-- **Phase-twist invariance of the Weyl spectrum.** -/
theorem weylEssentialSpectrum_twistedPoissonPrimeOp (τ : ℝ) :
    weylEssentialSpectrum (twistedPoissonPrimeOp τ) = weylIntervalZeroFour := by
  rw [← weylEssentialSpectrum_poissonPrimeOp]
  refine Set.Subset.antisymm (fun c hc => ?_) fun c hc =>
    mem_weylEssentialSpectrum_unitaryPush (phaseTwistEquiv τ) hc
  have h := mem_weylEssentialSpectrum_unitaryPush (phaseTwistEquiv τ).symm hc
  rwa [twistedPoissonPrimeOp, unitaryPush_symm_unitaryPush'] at h

/-- **Phase-twist invariance of the essential norm.** -/
theorem essentialNorm_twistedPoissonPrimeOp (τ : ℝ) :
    essentialNorm (twistedPoissonPrimeOp τ) = 4 := by
  rw [twistedPoissonPrimeOp, essentialNorm_unitaryPush, essentialNorm_poissonPrimeOp]

theorem sechSqHalf_three_le_essentialNorm_twistedPoissonPrimeCommOp (τ : ℝ) :
    sechSqHalf 3 ≤ essentialNorm (twistedPoissonPrimeCommOp τ) := by
  rw [twistedPoissonPrimeCommOp, essentialNorm_unitaryPush]
  exact sechSqHalf_three_le_essentialNorm_poissonPrimeCommOp

/-- **The physical-clock domain wall is phase-twist invariant.** -/
theorem not_summable_twisted_physical_column (τ : ℝ) (q : Nat.Primes) :
    ¬ Summable fun p =>
      ‖(stcClock p : ℂ) * (primePhase τ p * primePhase (-τ) q * (stcPrimePoissonKernel p q : ℂ))‖ ^ 2 := by
  have h : ∀ p, ‖(stcClock p : ℂ) * (primePhase τ p * primePhase (-τ) q *
      (stcPrimePoissonKernel p q : ℂ))‖ ^ 2 = (stcClock p * stcPrimePoissonKernel p q) ^ 2 := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_primePhase, norm_primePhase, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, one_mul, ← abs_mul, sq_abs]
  simp_rw [h]
  exact stcPrimePoissonKernel_physical_column_not_summable q

/-! ### The compact source inverse is not self-adjoint -/

section SourceInverse

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmCompactSource HedenmalmThetaSource

variable (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)

theorem intervalIntegral_pinnedOne {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..t, (pinnedOne : ℝ → ℂ) u = t := by
  have hae : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 → (pinnedOne : ℝ → ℂ) u = 1 :=
    (ae_restrict_iff' measurableSet_Icc).mp pinnedOne_coeFn
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℂ)) ?_]
  · simp
  · filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    exact hu ⟨hmem.1.le, hmem.2.trans ht.2⟩

theorem intervalIntegral_pinnedCoordinate {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..t, (pinnedCoordinate : ℝ → ℂ) u = (t : ℂ) ^ 2 / 2 := by
  have hae : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 → (pinnedCoordinate : ℝ → ℂ) u = (u : ℂ) :=
    (ae_restrict_iff' measurableSet_Icc).mp pinnedCoordinate_coeFn
  rw [intervalIntegral.integral_congr_ae (g := fun u : ℝ => (u : ℂ)) ?_]
  · rw [intervalIntegral.integral_ofReal, integral_id]
    push_cast; ring
  · filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    exact hu ⟨hmem.1.le, hmem.2.trans ht.2⟩

theorem sourceInverse_pinnedOne :
    kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure (pinnedKernelL2 S hfin)
      pinnedOne = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [pinnedKernelOperator_ae S hfin pinnedOne, ae_restrict_mem measurableSet_Icc]
    with t h ht
  rw [h, pinnedKernelField_apply_eq_pinnedVolterraFun, pinnedVolterraFun,
    pinnedPrefix_eq_intervalIntegral _ ht, intervalIntegral_pinnedOne ht, pinnedMean_pinnedOne]
  simp

theorem sourceInverse_pinnedCoordinate_ae :
    (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure (pinnedKernelL2 S hfin)
      pinnedCoordinate : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => -(Complex.I / 2) * ((quantileSpeed S t * (t * (1 - t)) : ℝ) : ℂ) := by
  filter_upwards [pinnedKernelOperator_ae S hfin pinnedCoordinate,
    ae_restrict_mem measurableSet_Icc] with t h ht
  rw [h, pinnedKernelField_apply_eq_pinnedVolterraFun, pinnedVolterraFun,
    pinnedPrefix_eq_intervalIntegral _ ht, intervalIntegral_pinnedCoordinate ht,
    pinnedMean_pinnedCoordinate]
  push_cast
  ring

/-- **The compact source inverse is not self-adjoint.** -/
theorem not_isSelfAdjoint_sourceInverse :
    ¬ IsSelfAdjoint
      (kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure (pinnedKernelL2 S hfin)) := by
  intro hB
  set B := kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure (pinnedKernelL2 S hfin)
  set g : ℝ → ℝ := fun t => quantileSpeed S t * (t * (1 - t)) with hg
  have hsym : inner ℂ pinnedOne (B pinnedCoordinate) = 0 := by
    have h := hB.isSymmetric pinnedOne pinnedCoordinate
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h, sourceInverse_pinnedOne, inner_zero_left]
  have hinner : inner ℂ pinnedOne (B pinnedCoordinate) =
      -(Complex.I / 2) * ((∫ t, g t ∂unitIntervalMeasure : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [pinnedOne_coeFn, sourceInverse_pinnedCoordinate_ae S hfin] with t h1 h2
    rw [h1, h2, RCLike.inner_apply]
    simp [hg]
  -- integrability of `g` from `B t ∈ L¹`
  have hint : Integrable g unitIntervalMeasure := by
    have hB1 := (integrable_coe (B pinnedCoordinate)).norm
    have h2 : Integrable (fun t => 2 * ‖(B pinnedCoordinate : ℝ → ℂ) t‖) unitIntervalMeasure :=
      hB1.const_mul 2
    refine h2.congr ?_
    filter_upwards [sourceInverse_pinnedCoordinate_ae S hfin, ae_restrict_mem measurableSet_Icc]
      with t h ht
    rw [h, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat]
    have hq := quantileSpeed_pos S t
    have : 0 ≤ quantileSpeed S t * (t * (1 - t)) := by
      have h1 : 0 ≤ t := ht.1
      have h2 : 0 ≤ 1 - t := by linarith [ht.2]
      positivity
    rw [abs_of_nonneg this]
    ring
  have hpos : 0 < ∫ t, g t ∂unitIntervalMeasure := by
    have hnonneg : 0 ≤ᵐ[unitIntervalMeasure] g := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hq := quantileSpeed_pos S t
      have h1 : 0 ≤ t := ht.1
      have h2 : 0 ≤ 1 - t := by linarith [ht.2]
      simp only [hg, Pi.zero_apply]
      positivity
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
    have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support g := by
      intro t ht
      have hq := quantileSpeed_pos S t
      have h1 : 0 < t := ht.1
      have h2 : 0 < 1 - t := by linarith [ht.2]
      simp only [Function.mem_support, hg]
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr Ioo_subset_Icc_self, Real.volume_Ioo]
    norm_num
  rw [hinner] at hsym
  have hI : -(Complex.I / 2) ≠ 0 := by simp
  have h0 := (mul_eq_zero.mp hsym).resolve_left hI
  have : (∫ t, g t ∂unitIntervalMeasure) = 0 := by exact_mod_cast h0
  linarith

end SourceInverse

/-- **The theta source inverse is not self-adjoint.** -/
theorem not_isSelfAdjoint_thetaKernelOperator :
    ¬ IsSelfAdjoint HedenmalmThetaSource.thetaKernelOperator :=
  not_isSelfAdjoint_sourceInverse _ _

/-- **No unitary identification of the theta source inverse with the Poisson Calkin defect.**
The defect `U K U* - W` is self-adjoint, while the theta source inverse is not. -/
theorem not_exists_unitary_thetaKernelOperator_eq_poissonCalkinDefect :
    ¬ ∃ V : Lp ℂ 2 unitIntervalMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 halfLineMeasure,
      unitaryPush V HedenmalmThetaSource.thetaKernelOperator =
        primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint - wienerHopfSechOp := by
  rintro ⟨V, hV⟩
  have hsa : IsSelfAdjoint
      (primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint - wienerHopfSechOp) := by
    rw [primeCellOp_conj_poissonPrimeOp]
    exact isSelfAdjoint_mertensStepSechOp.sub isSelfAdjoint_wienerHopfSechOp
  rw [← hV] at hsa
  have h := isSelfAdjoint_unitaryPush V.symm hsa
  rw [unitaryPush_symm_unitaryPush'] at h
  exact not_isSelfAdjoint_thetaKernelOperator h

end

end RHTower
