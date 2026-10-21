import GaloisForLFunctions.RHTower.HyperbolicPointPairFormHorocyclicCoordinates
import GaloisForLFunctions.RHTower.MaassWhittakerUniqueness

/-!
# Horocyclic Whittaker eigenfunctions of the hyperbolic Laplacian

For `ξ ≠ 0`, `k = 2π|ξ|` and real `τ` the horocyclic Whittaker function

`E_{ξ,τ}(x + iy) = e^{−2πiξx} √y K_{iτ}(ky)`   (`horocyclicWhittaker`)

is a `C²` eigenfunction of the positive Laplacian `−y²(∂ₓ² + ∂ᵧ²)` with eigenvalue `¼ + τ² =
s(1 − s)`, `s = ½ + iτ` (`positiveHyperbolicLaplacian_horocyclicWhittaker`).

**Separation of variables** (`positiveHyperbolicLaplacian_sep`).  For `E(x + iy) = a(x) b(y)`,
`−y²ΔE = −y²(a''(x) b(y) + a(x) b''(y))`.  Here `a'' = −k² a` and, by Bessel's equation,
`b'' = (k² + (ν² − ¼)/y²) b` with `ν = iτ`, so `−y²ΔE = (¼ − ν²) E`.

`K_{iτ}(x)` is real for real `τ` and `x > 0` (`im_besK_I_mul`), since
`conj K_ν = K_{ν̄}` and `K_{−ν} = K_ν`.
-/

open Complex Filter Topology UpperHalfPlane MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open MaassWhittaker

/-! ### Separation of variables -/

theorem hasFDerivAt_sep {c d : ℝ → ℂ} {c' d' : ℂ} {u : ℂ} (hc : HasDerivAt c c' u.re)
    (hd : HasDerivAt d d' u.im) :
    HasFDerivAt (fun w : ℂ => c w.re * d w.im)
      (c u.re • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d').comp imCLM) +
        d u.im • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c').comp reCLM)) u := by
  have h1 : HasFDerivAt (fun w : ℂ => c w.re)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c').comp reCLM) u :=
    hc.hasFDerivAt.comp u reCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℂ => d w.im)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d').comp imCLM) u :=
    hd.hasFDerivAt.comp u imCLM.hasFDerivAt
  exact h1.mul h2

/-- `D(a(x) b(y))[v] = a'(x) b(y) Re v + a(x) b'(y) Im v`. -/
theorem fderiv_sep_apply {c d : ℝ → ℂ} {c' d' : ℂ} {u : ℂ} (hc : HasDerivAt c c' u.re)
    (hd : HasDerivAt d d' u.im) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => c w.re * d w.im) u v = c' * d u.im * v.re + c u.re * d' * v.im := by
  rw [(hasFDerivAt_sep hc hd).fderiv]
  simp [Complex.real_smul]
  ring

/-- **The Laplacian of a separated function.**  For `E(x + iy) = a(x) b(y)`,
`−y²ΔE = −y²(a''(x) b(y) + a(x) b''(y))`. -/
theorem positiveHyperbolicLaplacian_sep {E : ℍ → ℂ} {a a' a'' b b' b'' : ℝ → ℂ}
    (hE : ∀ z : ℍ, E z = a z.re * b z.im)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : ∀ t, HasDerivAt a' (a'' t) t)
    (hb : ∀ y, 0 < y → HasDerivAt b (b' y) y) (hb' : ∀ y, 0 < y → HasDerivAt b' (b'' y) y)
    (z : ℍ) :
    positiveHyperbolicLaplacian E z = -((z.im : ℂ) ^ 2) * (a'' z.re * b z.im + a z.re * b'' z.im) := by
  have hF : ∀ w : ℂ, 0 < w.im → (E ∘ ofComplex) =ᶠ[𝓝 w] fun u => a u.re * b u.im := by
    intro w hw
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, hE, ofComplex_apply_of_im_pos hu]
    rfl
  have hz : 0 < (z : ℂ).im := z.im_pos
  have h1 : (fun w : ℂ => fderiv ℝ (E ∘ ofComplex) w 1) =ᶠ[𝓝 (z : ℂ)]
      fun w => a' w.re * b w.im := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    rw [(hF w hw).fderiv_eq, fderiv_sep_apply (ha w.re) (hb w.im hw)]
    simp
  have hI : (fun w : ℂ => fderiv ℝ (E ∘ ofComplex) w Complex.I) =ᶠ[𝓝 (z : ℂ)]
      fun w => a w.re * b' w.im := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    rw [(hF w hw).fderiv_eq, fderiv_sep_apply (ha w.re) (hb w.im hw)]
    simp
  rw [positiveHyperbolicLaplacian, h1.fderiv_eq, hI.fderiv_eq,
    fderiv_sep_apply (ha' (z : ℂ).re) (hb (z : ℂ).im hz),
    fderiv_sep_apply (ha (z : ℂ).re) (hb' (z : ℂ).im hz)]
  simp

/-! ### The Whittaker eigenfunction -/

/-- `K_{iτ}(x)` is real. -/
theorem im_besK_I_mul (τ x : ℝ) : (besK ((τ : ℂ) * Complex.I) x).im = 0 := by
  have h := modifiedBesselKOrder_conj x ((τ : ℂ) * Complex.I)
  rw [show conj ((τ : ℂ) * Complex.I) = -((τ : ℂ) * Complex.I) by simp, modifiedBesselKOrder_neg] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  simp only [besK]
  linarith

theorem conj_besK_I_mul (τ x : ℝ) : conj (besK ((τ : ℂ) * Complex.I) x) = besK ((τ : ℂ) * Complex.I) x :=
  Complex.conj_eq_iff_im.mpr (im_besK_I_mul τ x)

/-- The phase `a(x) = e^{−2πiξx}`. -/
def horocyclicPhase (ξ x : ℝ) : ℂ := cexp (-(2 * π * ξ * Complex.I) * x)

/-- **The horocyclic Whittaker function** `E_{ξ,τ}(x + iy) = e^{−2πiξx} √y K_{iτ}(2π|ξ|y)`. -/
def horocyclicWhittaker (ξ τ : ℝ) (z : ℍ) : ℂ :=
  horocyclicPhase ξ z.re * whittakerW (2 * π * |ξ|) ((τ : ℂ) * Complex.I) z.im

theorem hasDerivAt_horocyclicPhase (ξ x : ℝ) :
    HasDerivAt (horocyclicPhase ξ) (-(2 * π * ξ * Complex.I) * horocyclicPhase ξ x) x := by
  have h : HasDerivAt (fun y : ℝ => -(2 * π * ξ * Complex.I) * (y : ℂ))
      (-(2 * π * ξ * Complex.I)) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(2 * π * ξ * Complex.I))
  show HasDerivAt (fun y : ℝ => cexp (-(2 * π * ξ * Complex.I) * (y : ℂ))) _ x
  convert h.cexp using 1
  rw [horocyclicPhase]; ring

theorem hasDerivAt_horocyclicPhase' (ξ x : ℝ) :
    HasDerivAt (fun x => -(2 * π * ξ * Complex.I) * horocyclicPhase ξ x)
      (-(2 * π * ξ * Complex.I) * (-(2 * π * ξ * Complex.I) * horocyclicPhase ξ x)) x :=
  (hasDerivAt_horocyclicPhase ξ x).const_mul _

/-- **The eigenvalue equation.**  `−y²ΔE_{ξ,τ} = (¼ + τ²) E_{ξ,τ}` for `ξ ≠ 0`. -/
theorem positiveHyperbolicLaplacian_horocyclicWhittaker {ξ : ℝ} (hξ : ξ ≠ 0) (τ : ℝ) (z : ℍ) :
    positiveHyperbolicLaplacian (horocyclicWhittaker ξ τ) z =
      (1 / 2 + τ * Complex.I) * (1 - (1 / 2 + τ * Complex.I)) * horocyclicWhittaker ξ τ z := by
  have hk : 0 < 2 * π * |ξ| := by positivity
  rw [positiveHyperbolicLaplacian_sep (E := horocyclicWhittaker ξ τ) (a := horocyclicPhase ξ)
    (b := whittakerW (2 * π * |ξ|) ((τ : ℂ) * Complex.I)) (fun z => rfl)
    (hasDerivAt_horocyclicPhase ξ)
    (hasDerivAt_horocyclicPhase' ξ) (fun y hy => hasDerivAt_whittakerW hk hy)
    (fun y hy => hasDerivAt_whittakerWd hk hy), horocyclicWhittaker]
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have habs : ((2 * π * |ξ| : ℝ) : ℂ) ^ 2 = ((2 * π * ξ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, mul_pow, mul_pow (2 * π) ξ, sq_abs]
  push_cast at habs ⊢
  field_simp
  rw [Complex.I_sq]
  linear_combination (-(16 : ℂ) * horocyclicPhase ξ z.re *
    whittakerW (2 * π * |ξ|) (Complex.I * τ) z.im * (z.im : ℂ) ^ 2) * habs +
    ((16 : ℂ) * horocyclicPhase ξ z.re * whittakerW (2 * π * |ξ|) (Complex.I * τ) z.im *
      (τ : ℂ) ^ 2) * Complex.I_sq

/-! ### Regularity -/

/-- A function with two derivatives on `(0, ∞)`, the second continuous, is `C²` there. -/
theorem contDiffOn_two_of_hasDerivAt {b b' b'' : ℝ → ℂ}
    (hb : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt b (b' y) y)
    (hb' : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt b' (b'' y) y) (hb'' : ContinuousOn b'' (Ioi 0)) :
    ContDiffOn ℝ 2 b (Ioi 0) := by
  have hd : EqOn (deriv b) b' (Ioi 0) := fun y hy => (hb y hy).deriv
  have hd' : EqOn (deriv b') b'' (Ioi 0) := fun y hy => (hb' y hy).deriv
  have h1 : ContDiffOn ℝ 1 b' (Ioi 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hb' y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact contDiffOn_zero.mpr (hb''.congr hd')
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨fun y hy => (hb y hy).differentiableAt.differentiableWithinAt, by simp,
    h1.congr hd⟩

theorem contDiffOn_whittakerW {k : ℝ} (hk : 0 < k) (ν : ℂ) :
    ContDiffOn ℝ 2 (whittakerW k ν) (Ioi 0) := by
  have hc : ContinuousOn (whittakerW k ν) (Ioi 0) := fun y hy =>
    (hasDerivAt_whittakerW hk hy).continuousAt.continuousWithinAt
  refine contDiffOn_two_of_hasDerivAt (fun y hy => hasDerivAt_whittakerW hk hy)
    (fun y hy => hasDerivAt_whittakerWd hk hy) ?_
  refine ContinuousOn.mul ?_ hc
  refine continuousOn_const.add (ContinuousOn.div continuousOn_const ?_ fun y hy => ?_)
  · exact (Complex.continuous_ofReal.pow 2).continuousOn
  · exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))

/-- `E_{ξ,τ}` is `C²` on `ℍ`. -/
theorem isRealSmooth_horocyclicWhittaker {ξ : ℝ} (hξ : ξ ≠ 0) (τ : ℝ) :
    IsRealSmoothUpperHalfPlane (horocyclicWhittaker ξ τ) := by
  have hk : 0 < 2 * π * |ξ| := by positivity
  have hW := (contDiffOn_whittakerW hk ((τ : ℂ) * Complex.I)).comp
    (Complex.imCLM.contDiff.contDiffOn (s := {z : ℂ | 0 < z.im}))
    (fun z hz => (show 0 < z.im from hz))
  have hP : ContDiff ℝ 2 fun u : ℂ => horocyclicPhase ξ u.re := by
    unfold horocyclicPhase
    have h1 : ContDiff ℝ 2 fun u : ℂ => -(2 * π * ξ * Complex.I) * ((u.re : ℝ) : ℂ) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff)
    exact ((Complex.contDiff_exp : ContDiff ℂ 2 cexp).restrict_scalars ℝ).comp h1
  refine (hP.contDiffOn.mul hW).congr fun u hu => ?_
  have hu' : 0 < u.im := hu
  simp only [Function.comp_apply, horocyclicWhittaker, ofComplex_apply_of_im_pos hu']
  rfl

/-- `E_{ξ,τ}` is continuous. -/
theorem continuous_horocyclicWhittaker {ξ : ℝ} (hξ : ξ ≠ 0) (τ : ℝ) :
    Continuous (horocyclicWhittaker ξ τ) :=
  HyperbolicPointPair.continuous_of_smooth (isRealSmooth_horocyclicWhittaker hξ τ)

/-! ### The fibre eigen-relation -/

/-- The fibre kernel `K_ξ(y, y') = ∫ k((t² + (y − y')²)/(4yy')) e^{−2πiξt} dt`. -/
def horocyclicFibreKernel (k : ℝ → ℝ) (ξ y y' : ℝ) : ℂ :=
  ∫ t : ℝ, (k (pairUCoord t y 0 y') : ℂ) * horocyclicPhase ξ t

theorem horocyclicWhittaker_ofComplex (ξ τ x y : ℝ) (hy : 0 < y) :
    horocyclicWhittaker ξ τ (ofComplex ⟨x, y⟩) =
      horocyclicPhase ξ x * whittakerW (2 * π * |ξ|) ((τ : ℂ) * Complex.I) y := by
  rw [horocyclicWhittaker, ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
  rfl

/-- **The fibre eigen-relation.**  For `ξ ≠ 0` and `y > 0`,
`∫_0^∞ K_ξ(y, y') W_τ(y') dy'/y'² = h_k(½ + iτ) W_τ(y)`, `W_τ(y) = √y K_{iτ}(2π|ξ|y)`
(Selberg's theorem for `E_{ξ,τ}`, integrated along the horocycle). -/
theorem integral_horocyclicFibreKernel_mul_whittakerW {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hkR : DeckPointPair.KernelSupport k R) {ξ : ℝ} (hξ : ξ ≠ 0) (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ y' in Ioi (0 : ℝ), (y' ^ 2)⁻¹ •
        (horocyclicFibreKernel k ξ y y' * whittakerW (2 * π * |ξ|) ((τ : ℂ) * Complex.I) y') =
      whittakerW (2 * π * |ξ|) ((τ : ℂ) * Complex.I) y *
        DeckPointPair.selbergTransform k (1 / 2 + τ * Complex.I) := by
  set z : ℍ := ofComplex ⟨0, y⟩
  have hsel := DeckPointPair.integral_pairKernel_mul_eigen hkc hkR
    (isRealSmooth_horocyclicWhittaker hξ τ) (positiveHyperbolicLaplacian_horocyclicWhittaker hξ τ) z
  have hint : Integrable fun w => ((k (pairU z w) : ℝ) : ℂ) * horocyclicWhittaker ξ τ w :=
    (DeckPointPair.integrable_pairKernel_smul' hkc hkR (continuous_horocyclicWhittaker hξ τ) z).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  rw [integral_upperHalfPlane_eq_iterated _ hint, horocyclicWhittaker_ofComplex ξ τ 0 y hy,
    show horocyclicPhase ξ 0 = 1 by simp [horocyclicPhase], one_mul] at hsel
  rw [← hsel]
  refine setIntegral_congr_fun measurableSet_Ioi fun y' hy' => ?_
  have hy'0 : (0 : ℝ) < y' := hy'
  congr 1
  rw [horocyclicFibreKernel, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
  simp only
  rw [horocyclicWhittaker_ofComplex ξ τ x' y' hy'0, pairU_ofComplex_eq hy hy'0]
  rw [show ((0 - x') ^ 2 + (y - y') ^ 2) / (4 * y * y') = pairUCoord x' y 0 y' by
    simp [pairUCoord]]
  ring

end GaloisForLFunctions.RHTower.MehlerFock
