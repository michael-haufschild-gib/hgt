import GaloisForLFunctions.RHTower.CircleHolomorphicPhaseSeamContraction

/-!
# The seam margin is controlled by the boundary modulus ratio

Let `u` be a circle phase with `conj u = conj(h) · h⁻¹`.  Here `h` and `h⁻¹` are bounded symbols
without negative Fourier modes, i.e. boundary values of a holomorphic function on the disc that has
a holomorphic square root without zeros.  With bounds `|h| ≤ A` and `|h⁻¹| ≤ B` on the circle,

`‖(1 − P) U† P‖² ≤ 1 − 1/(AB)²`   (`norm_sq_adjointSeam_le_of_outer_factor`).

Mechanism: for Hardy `f` put `g = h⁻¹ f`, again a Hardy vector.  Co-analytic multipliers commute
past the Hardy projection (`hardy_mul_multiplier_mul_one_sub_hardy_eq_zero`, the adjoint of
"holomorphic multipliers preserve the Hardy space").  Hence `P(conj(h⁻¹) P(conj(h) g)) = g`, and
`‖g‖ ≤ B ‖P(U† f)‖`.  Since `f = h g`, `‖f‖ ≤ A ‖g‖`.  So `‖P U† f‖ ≥ ‖f‖/(AB)`, and Pythagoras
turns this lower bound into the seam bound.  For the phase of a zero-free holomorphic `F`, with
`h = F^{1/2}` in suitable coordinates, `(AB)² = max|F|/min|F|`.  The margin
`1 − ‖(1 − P) U† P‖²` is therefore at least the boundary ratio `min|F| / max|F|`.
-/

noncomputable section

open Complex MeasureTheory ContinuousLinearMap

namespace RHTower

namespace SeamModulusMargin

/-- The adjoint of a circle multiplier is the multiplier by the conjugate symbol. -/
theorem adjoint_ccmCircleMultiplier (a b : CCMCircleBoundedSymbol)
    (hab : ∀ z, b.toFun z = starRingEnd ℂ (a.toFun z)) :
    adjoint (ccmCircleMultiplier a) = ccmCircleMultiplier b := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ccmCircleMultiplier_coeFn b x, ccmCircleMultiplier_coeFn a y] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, hab, Complex.conj_conj]
  ring

/-- Co-analytic multipliers commute past the Hardy projection:
`P M_{conj a} (1 − P) = 0` when `a` has no negative Fourier modes. -/
theorem hardy_mul_multiplier_mul_one_sub_hardy_eq_zero (a b : CCMCircleBoundedSymbol)
    (ha : ∀ n : ℤ, n < 0 → fourierCoeff a.toFun n = 0)
    (hab : ∀ z, b.toFun z = starRingEnd ℂ (a.toFun z)) :
    ccmCircleHardyProjection * ccmCircleMultiplier b * (1 - ccmCircleHardyProjection) = 0 := by
  have h := one_sub_hardy_mul_multiplier_mul_hardy_eq_zero a ha
  have h2 := congrArg star h
  rw [star_zero, star_mul, star_mul, star_sub, star_one,
    ContinuousLinearMap.star_eq_adjoint, ccmCircleHardyProjection_adjoint,
    ContinuousLinearMap.star_eq_adjoint, adjoint_ccmCircleMultiplier a b hab] at h2
  rw [← h2, mul_assoc]

theorem apply_of_mul_eq_zero {X Y Z : CCMCircleL2 →L[ℂ] CCMCircleL2} (h : X * Y * Z = 0)
    (v : CCMCircleL2) : X (Y (Z v)) = 0 := by
  have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T v) h
  simpa [mul_apply_eq_comp] using this

theorem hardy_idem (v : CCMCircleL2) :
    ccmCircleHardyProjection (ccmCircleHardyProjection v) = ccmCircleHardyProjection v := by
  have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T v)
    ccmCircleHardyProjection_idempotent.eq
  simpa [mul_apply_eq_comp] using this

/-- A holomorphic multiplier keeps Hardy vectors Hardy. -/
theorem hardy_multiplier_of_hardy (a : CCMCircleBoundedSymbol)
    (ha : ∀ n : ℤ, n < 0 → fourierCoeff a.toFun n = 0) {f : CCMCircleL2}
    (hf : ccmCircleHardyProjection f = f) :
    ccmCircleHardyProjection (ccmCircleMultiplier a f) = ccmCircleMultiplier a f := by
  have h := apply_of_mul_eq_zero (one_sub_hardy_mul_multiplier_mul_hardy_eq_zero a ha) f
  rw [hf] at h
  simp only [sub_apply, one_apply_eq_self] at h
  exact (sub_eq_zero.mp h).symm

/-- `P(M_b (P v)) = P(M_b v)` for a co-analytic multiplier `b`. -/
theorem hardy_coanalytic_hardy (a b : CCMCircleBoundedSymbol)
    (ha : ∀ n : ℤ, n < 0 → fourierCoeff a.toFun n = 0)
    (hab : ∀ z, b.toFun z = starRingEnd ℂ (a.toFun z)) (v : CCMCircleL2) :
    ccmCircleHardyProjection (ccmCircleMultiplier b (ccmCircleHardyProjection v)) =
      ccmCircleHardyProjection (ccmCircleMultiplier b v) := by
  have h := apply_of_mul_eq_zero (hardy_mul_multiplier_mul_one_sub_hardy_eq_zero a b ha hab) v
  simp only [sub_apply, one_apply_eq_self, map_sub] at h
  exact (sub_eq_zero.mp h).symm

/-- **Toeplitz lower bound for an outer factorization.**  With `conj u = conj(h) · h⁻¹` as
multipliers, `‖f‖ ≤ A B ‖P(M_{conj h} M_{h⁻¹} f)‖` for every Hardy vector `f`. -/
theorem norm_le_of_outer_factor (h hi hc hic : CCMCircleBoundedSymbol)
    (_hh : ∀ n : ℤ, n < 0 → fourierCoeff h.toFun n = 0)
    (hhi : ∀ n : ℤ, n < 0 → fourierCoeff hi.toFun n = 0)
    (hc_eq : ∀ z, hc.toFun z = starRingEnd ℂ (h.toFun z))
    (hic_eq : ∀ z, hic.toFun z = starRingEnd ℂ (hi.toFun z))
    (hinv : ∀ z, h.toFun z * hi.toFun z = 1)
    (f : CCMCircleL2) (hf : ccmCircleHardyProjection f = f) :
    ‖f‖ ≤ h.bound * hic.bound *
      ‖ccmCircleHardyProjection (ccmCircleMultiplier hc (ccmCircleMultiplier hi f))‖ := by
  set P := ccmCircleHardyProjection
  set g := ccmCircleMultiplier hi f with hg
  have hPg : P g = g := hardy_multiplier_of_hardy hi hhi hf
  -- `f = h g`
  have hfg : ccmCircleMultiplier h g = f := by
    have hone : ccmCircleMultiplier h * ccmCircleMultiplier hi = 1 := by
      rw [ccmCircleMultiplier_mul_eq h hi (continuousCircleSymbol (fun _ => 1) continuous_const)
        (fun z => by rw [hinv z]; rfl)]
      exact ccmCircleMultiplier_eq_one _ (fun _ => rfl)
    have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f) hone
    simpa [mul_apply_eq_comp, hg] using this
  -- `g = P(conj(hi) P(conj(h) g))`
  have hback : P (ccmCircleMultiplier hic (P (ccmCircleMultiplier hc g))) = g := by
    rw [hardy_coanalytic_hardy hi hic hhi hic_eq]
    have hone : ccmCircleMultiplier hic * ccmCircleMultiplier hc = 1 := by
      rw [ccmCircleMultiplier_mul_eq hic hc (continuousCircleSymbol (fun _ => 1) continuous_const)
        (fun z => by
          rw [hic_eq z, hc_eq z, ← map_mul, mul_comm, hinv z, map_one]; rfl)]
      exact ccmCircleMultiplier_eq_one _ (fun _ => rfl)
    have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T g) hone
    simp only [mul_apply_eq_comp, one_apply_eq_self] at this
    rw [show ccmCircleMultiplier hic (ccmCircleMultiplier hc g) = g from this, hPg]
  have hPnorm : ‖P‖ ≤ 1 := by
    have h1 : ∀ v : CCMCircleL2, ‖P v‖ ≤ ‖v‖ := fun v => by
      have := norm_sq_eq_add_of_orthogonalProjection P ccmCircleHardyProjection_idempotent
        ccmCircleHardyProjection_adjoint v
      nlinarith [norm_nonneg (P v), norm_nonneg v, sq_nonneg ‖v - P v‖]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simpa using h1 v)
  have hMic : ‖ccmCircleMultiplier hic‖ ≤ hic.bound :=
    MeasureTheory.norm_lpBoundedMulCLM_le _ _ _
  have hMh : ‖ccmCircleMultiplier h‖ ≤ h.bound :=
    MeasureTheory.norm_lpBoundedMulCLM_le _ _ _
  have hg_le : ‖g‖ ≤ hic.bound * ‖P (ccmCircleMultiplier hc g)‖ := by
    calc ‖g‖ = ‖P (ccmCircleMultiplier hic (P (ccmCircleMultiplier hc g)))‖ := by rw [hback]
      _ ≤ ‖ccmCircleMultiplier hic (P (ccmCircleMultiplier hc g))‖ := by
          calc _ ≤ ‖P‖ * ‖ccmCircleMultiplier hic (P (ccmCircleMultiplier hc g))‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖ccmCircleMultiplier hic (P (ccmCircleMultiplier hc g))‖ := by gcongr
            _ = _ := one_mul _
      _ ≤ ‖ccmCircleMultiplier hic‖ * ‖P (ccmCircleMultiplier hc g)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ hic.bound * ‖P (ccmCircleMultiplier hc g)‖ := by gcongr
  have hf_le : ‖f‖ ≤ h.bound * ‖g‖ := by
    calc ‖f‖ = ‖ccmCircleMultiplier h g‖ := by rw [hfg]
      _ ≤ ‖ccmCircleMultiplier h‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ h.bound * ‖g‖ := by gcongr
  calc ‖f‖ ≤ h.bound * ‖g‖ := hf_le
    _ ≤ h.bound * (hic.bound * ‖P (ccmCircleMultiplier hc g)‖) := by
        gcongr; exact h.bound_nonneg
    _ = _ := by ring

/-- **Seam margin from an outer factorization.**  If the conjugate phase factors as
`conj(h) · h⁻¹` with `h`, `h⁻¹` holomorphic bounded symbols, then
`‖(1 − P) U† P‖² ≤ 1 − 1/(AB)²` with `A`, `B` the symbol bounds of `h` and `conj(h⁻¹)`. -/
theorem norm_sq_adjointSeam_le_of_outer_factor (u : CCMCirclePhase)
    (h hi hc hic : CCMCircleBoundedSymbol)
    (hh : ∀ n : ℤ, n < 0 → fourierCoeff h.toFun n = 0)
    (hhi : ∀ n : ℤ, n < 0 → fourierCoeff hi.toFun n = 0)
    (hc_eq : ∀ z, hc.toFun z = starRingEnd ℂ (h.toFun z))
    (hic_eq : ∀ z, hic.toFun z = starRingEnd ℂ (hi.toFun z))
    (hinv : ∀ z, h.toFun z * hi.toFun z = 1)
    (hu : ∀ z, starRingEnd ℂ (u.toFun z) = hc.toFun z * hi.toFun z)
    (hAB : 0 < h.bound * hic.bound) :
    ‖u.datum.adjointHankelSeam‖ ^ 2 ≤ 1 - 1 / (h.bound * hic.bound) ^ 2 := by
  set P := ccmCircleHardyProjection
  set c := 1 / (h.bound * hic.bound) with hcdef
  have hconj : u.conjMultiplier = ccmCircleMultiplier hc * ccmCircleMultiplier hi :=
    (ccmCircleMultiplier_mul_eq hc hi u.conjSymbol (fun z => (hu z).symm)).symm
  -- lower bound on `P U† f`
  have hlow : ∀ f : CCMCircleL2, P f = f → c * ‖f‖ ≤ ‖P (u.conjMultiplier f)‖ := by
    intro f hf
    have := norm_le_of_outer_factor h hi hc hic hh hhi hc_eq hic_eq hinv f hf
    rw [hconj]
    simp only [mul_apply_eq_comp]
    rw [hcdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ hAB]
    linarith
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  -- the seam bound
  have hc1 : c ≤ 1 := by
    have hz := u.norm_eq_one 0
    obtain ⟨z, -⟩ : ∃ z : AddCircle (1 : ℝ), True := ⟨0, trivial⟩
    have h1 : ‖h.toFun z‖ ≤ h.bound := h.norm_le z
    have h2 : ‖hic.toFun z‖ ≤ hic.bound := hic.norm_le z
    have h3 : ‖h.toFun z‖ * ‖hic.toFun z‖ = 1 := by
      rw [hic_eq z, Complex.norm_conj, ← norm_mul, hinv z, norm_one]
    have h4 : 1 ≤ h.bound * hic.bound := by
      calc (1 : ℝ) = ‖h.toFun z‖ * ‖hic.toFun z‖ := h3.symm
        _ ≤ h.bound * hic.bound :=
          mul_le_mul h1 h2 (norm_nonneg _) h.bound_nonneg
    rw [hcdef, div_le_one hAB]
    exact h4
  have hbound : ∀ y : CCMCircleL2, ‖u.datum.adjointHankelSeam y‖ ≤
      Real.sqrt (1 - c ^ 2) * ‖y‖ := by
    intro y
    set f := P y with hfdef
    have hPf : P f = f := hardy_idem y
    have hseam : u.datum.adjointHankelSeam y =
        u.conjMultiplier f - P (u.conjMultiplier f) := by
      change ((1 - P) * adjoint u.multiplier * P) y = _
      rw [u.adjoint_multiplier]
      simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self]
      rfl
    have hiso : ‖u.conjMultiplier f‖ = ‖f‖ := by
      have hsq : ‖u.conjMultiplier f‖ ^ 2 = ‖f‖ ^ 2 := by
        rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, ← u.adjoint_multiplier,
          adjoint_inner_left]
        have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f)
          u.multiplier_mul_conjMultiplier
        simp only [mul_apply_eq_comp, one_apply_eq_self] at this
        rw [← u.adjoint_multiplier] at this
        rw [this]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    have hpy := norm_sq_eq_add_of_orthogonalProjection P ccmCircleHardyProjection_idempotent
      ccmCircleHardyProjection_adjoint (u.conjMultiplier f)
    rw [hiso] at hpy
    have hl := hlow f hPf
    have hfy : ‖f‖ ≤ ‖y‖ := by
      have := norm_sq_eq_add_of_orthogonalProjection P ccmCircleHardyProjection_idempotent
        ccmCircleHardyProjection_adjoint y
      nlinarith [norm_nonneg (P y), norm_nonneg y, sq_nonneg ‖y - P y‖]
    rw [hseam]
    have hsq : ‖u.conjMultiplier f - P (u.conjMultiplier f)‖ ^ 2 ≤ (1 - c ^ 2) * ‖y‖ ^ 2 := by
      have hl2 : (c * ‖f‖) ^ 2 ≤ ‖P (u.conjMultiplier f)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hl 2
      have hfy2 : ‖f‖ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfy 2
      have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith
      nlinarith
    have hnn : 0 ≤ 1 - c ^ 2 := by nlinarith
    calc ‖u.conjMultiplier f - P (u.conjMultiplier f)‖
        = Real.sqrt (‖u.conjMultiplier f - P (u.conjMultiplier f)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 - c ^ 2) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (1 - c ^ 2) * ‖y‖ := by
          rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]
  have hop : ‖u.datum.adjointHankelSeam‖ ≤ Real.sqrt (1 - c ^ 2) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hbound
  have hnn : 0 ≤ 1 - c ^ 2 := by nlinarith
  calc ‖u.datum.adjointHankelSeam‖ ^ 2 ≤ Real.sqrt (1 - c ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = 1 - c ^ 2 := Real.sq_sqrt hnn
    _ = 1 - 1 / (h.bound * hic.bound) ^ 2 := by rw [hcdef, div_pow, one_pow]

end SeamModulusMargin

end RHTower
