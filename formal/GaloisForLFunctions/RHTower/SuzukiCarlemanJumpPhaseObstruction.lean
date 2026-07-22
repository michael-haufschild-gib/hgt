import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux
import GaloisForLFunctions.RHTower.SuzukiCarlemanJumpEulerDefectWeld

/-!
# Centered Euler observable and the mixed-coordinate phase falsifier

The centered Euler observable `J[f](z)=z*(z*f'(z)-f(z))` annihilates linear endpoint escape,
makes a simple pole at the central boundary point removable, and retains exact one-degree pole
amplification at every nonzero point.  A single analytic upper-half-plane source germ for this
observable still proves RH.

The final section retains an algebraic phase falsifier for a *mixed* coordinate: centered Xi
multiplier `G_eta` combined directly with an unrephased physical Volterra triangle.  It does not
model Suzuki's physical or canonically normalized sheet.  The physical multiplier is `I*G_eta`,
so `SuzukiCarlemanCoordinatePhase` proves that the interval input paired with `G_eta` is
`-I*T_phys`.  Under that correction source quadrature makes the normalized central flux real,
and no scalar Herglotz obstruction follows.  The earlier source-semantic interpretation of the
mixed-coordinate theorem is retracted.

No RH assumption, positivity premise, estimate, or numerical computation occurs here.
-/

open Complex Filter Topology GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Centered Euler observable -/

/-- Euler defect with the functional-equation center removed:
`J[f](z)=z*(z*f'(z)-f(z))`. -/
def suzukiCenteredEulerDefect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * suzukiEulerDefect f z

/-- At the origin, the Euler defect preserves every negative meromorphic order.  If
`f(w)=w^n g(w)` with `n<0`, its leading coefficient is multiplied by `n-1`, which is nonzero. -/
theorem meromorphicOrderAt_suzukiEulerDefect_zero_eq
    {f : ℂ → ℂ} {n : ℤ}
    (hf : MeromorphicAt f 0) (hn : n < 0)
    (horder : meromorphicOrderAt f 0 = (n : WithTop ℤ)) :
    meromorphicOrderAt (suzukiEulerDefect f) 0 = (n : WithTop ℤ) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp horder
  let G : ℂ → ℂ := fun w =>
    ((n - 1 : ℤ) : ℂ) * g w + w * deriv g w
  have hG : AnalyticAt ℂ G 0 := by
    dsimp only [G]
    fun_prop
  have hn1 : ((n - 1 : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hG0 : G 0 ≠ 0 := by
    dsimp only [G]
    simpa only [Int.cast_sub, Int.cast_one, zero_mul, add_zero] using
      (mul_ne_zero hn1 hg0)
  have hfg' : f =ᶠ[𝓝[≠] 0] fun w => w ^ n * g w := by
    simpa only [sub_zero, smul_eq_mul] using hfg
  have hfactorDeriv :
      deriv (fun w : ℂ => w ^ n * g w) =ᶠ[𝓝[≠] 0]
        fun w => (n : ℂ) * w ^ (n - 1) * g w +
          w ^ n * deriv g w := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hg.eventually_analyticAt,
      self_mem_nhdsWithin] with w hgw hw
    have hw0 : w ≠ 0 := by simpa using hw
    exact ((hasDerivAt_zpow n w (Or.inl hw0)).mul
      hgw.differentiableAt.hasDerivAt).deriv
  have hEeq : suzukiEulerDefect f =ᶠ[𝓝[≠] 0]
      fun w => w ^ n * G w := by
    have hderiv := Filter.EventuallyEq.nhdsNE_deriv hfg'
    filter_upwards [hfg', hderiv, hfactorDeriv, self_mem_nhdsWithin]
      with w hfw hdf hfac hw
    have hw0 : w ≠ 0 := by simpa using hw
    have hpown : w ^ n = w ^ (n - 1) * w := by
      rw [← zpow_add_one₀ hw0 (n - 1), sub_add_cancel]
    rw [suzukiEulerDefect, hfw, hdf, hfac, hpown]
    dsimp only [G]
    rw [Int.cast_sub, Int.cast_one]
    ring
  have hE : MeromorphicAt (suzukiEulerDefect f) 0 :=
    ((MeromorphicAt.id 0).mul hf.deriv).sub hf
  apply (meromorphicOrderAt_eq_int_iff hE).mpr
  exact ⟨G, hG, hG0, by simpa only [sub_zero, smul_eq_mul] using hEeq⟩

/-- Multiplication by the center coordinate raises the origin order by one.  In particular,
`suzukiCenteredEulerDefect` makes every simple pole at zero removable. -/
theorem meromorphicOrderAt_suzukiCenteredEulerDefect_zero_eq_add_one
    {f : ℂ → ℂ} {n : ℤ}
    (hf : MeromorphicAt f 0) (hn : n < 0)
    (horder : meromorphicOrderAt f 0 = (n : WithTop ℤ)) :
    meromorphicOrderAt (suzukiCenteredEulerDefect f) 0 =
      ((n + 1 : ℤ) : WithTop ℤ) := by
  have hE : MeromorphicAt (suzukiEulerDefect f) 0 :=
    ((MeromorphicAt.id 0).mul hf.deriv).sub hf
  rw [show suzukiCenteredEulerDefect f = fun z => id z * suzukiEulerDefect f z by rfl]
  rw [fun_meromorphicOrderAt_mul (MeromorphicAt.id 0) hE,
    meromorphicOrderAt_id, meromorphicOrderAt_suzukiEulerDefect_zero_eq hf hn horder]
  norm_num [add_comm]

/-- Away from the center, multiplication by `z` is an analytic unit, so the centered observable
retains the Euler defect's exact one-degree pole amplification. -/
theorem meromorphicOrderAt_suzukiCenteredEulerDefect_eq_sub_one
    {f : ℂ → ℂ} {z : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z) (hz : z ≠ 0) (hn : n < 0)
    (horder : meromorphicOrderAt f z = (n : WithTop ℤ)) :
    meromorphicOrderAt (suzukiCenteredEulerDefect f) z =
      ((n - 1 : ℤ) : WithTop ℤ) := by
  have hE : MeromorphicAt (suzukiEulerDefect f) z :=
    ((MeromorphicAt.id z).mul hf.deriv).sub hf
  have hid : meromorphicOrderAt id z = (0 : WithTop ℤ) := by
    rw [analyticAt_id.meromorphicOrderAt_eq,
      analyticAt_id.analyticOrderAt_eq_zero.mpr hz]
    simp
  rw [show suzukiCenteredEulerDefect f = fun w => id w * suzukiEulerDefect f w by rfl]
  rw [fun_meromorphicOrderAt_mul (MeromorphicAt.id z) hE, hid,
    meromorphicOrderAt_suzukiEulerDefect_eq_sub_one hf hz hn horder]
  simp

/-- Centering retains exact invariance under linear Nevanlinna endpoint escape. -/
theorem suzukiCenteredEulerDefect_add_linear
    (f : ℂ → ℂ) (c z : ℂ) (hf : AnalyticAt ℂ f z) :
    suzukiCenteredEulerDefect (fun w => f w + c * w) z =
      suzukiCenteredEulerDefect f z := by
  rw [suzukiCenteredEulerDefect, suzukiCenteredEulerDefect,
    suzukiEulerDefect_add_linear f c z hf]

/-- A single analytic source germ for the centered Euler observable still proves RH.  Division by
`z` is analytic throughout the upper half-plane and reduces this statement to the existing Euler
germ-weld capstone. -/
theorem riemannHypothesis_of_suzukiAffineSewnExteriorWeylCenteredEulerDefect_source_germ_weld
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta D : ℂ → ℂ} {u : ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    (hD : AnalyticOnNhd ℂ D UpperHalfPlane.upperHalfPlaneSet)
    (hu : u ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hseed :
      suzukiCenteredEulerDefect
          (RHTower.suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta) =ᶠ[𝓝[≠] u] D) :
    RiemannHypothesis := by
  let D₀ : ℂ → ℂ := fun z => D z / z
  have hD₀ : AnalyticOnNhd ℂ D₀ UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    change 0 < z.im at hz
    exact (hD z hz).div analyticAt_id (by
      intro hzero
      subst z
      simp at hz)
  have hu0 : u ≠ 0 := by
    change 0 < u.im at hu
    intro hzero
    subst u
    simp at hu
  have hseed₀ :
      suzukiEulerDefect
          (RHTower.suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta) =ᶠ[𝓝[≠] u] D₀ := by
    filter_upwards [hseed, eventually_ne_nhdsWithin hu0] with z hz hz0
    dsimp only [D₀]
    have hz' : z * suzukiEulerDefect
        (RHTower.suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z = D z := by
      simpa only [suzukiCenteredEulerDefect] using hz
    apply (eq_div_iff hz0).mpr
    simpa only [mul_comm] using hz'
  exact
    RHTower.riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
      hab hWAlpha hWBeta hRAlpha hRBeta hrealAlpha hrealBeta hD₀ hu hseed₀

end

end GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Mixed-coordinate falsifier (not the physical or Weyl-normalized sheet) -/

/-- Feeding a purely imaginary *unrephased physical* triangle directly into the centered
`G_eta W-I` algebra makes this mixed-coordinate flux purely imaginary. -/
theorem suzukiMixedCoordinateCentralSourceFlux_re_eq_zero_of_real_pureImag
    (alpha beta a b rightAlpha rightBeta : ℝ) :
    (suzukiAffineSewnCentralSourceFlux
      (suzukiCenteredShiftParameter alpha)
      (suzukiCenteredShiftParameter beta)
      (a : ℂ) (b : ℂ) (I * (rightAlpha : ℂ)) (I * (rightBeta : ℂ))).re = 0 := by
  rw [suzukiAffineSewnCentralSourceFlux_centered_eq]
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, zero_mul, Complex.I_im, one_mul, sub_zero, Complex.sub_im,
    Complex.mul_im, mul_zero, zero_add, Complex.normSq_apply]
  ring

/-- The corresponding mixed-coordinate central residue has strictly positive real part.  This
does not apply after the required `-I` rephasing of the physical triangle. -/
theorem suzukiMixedCoordinateCentralResidue_re_pos_of_real_pureImag
    (alpha beta a b rightAlpha rightBeta : ℝ) :
    0 <
      (-(deriv (deriv XiC) 0 / XiC 0) +
        suzukiAffineSewnCentralSourceFlux
          (suzukiCenteredShiftParameter alpha)
          (suzukiCenteredShiftParameter beta)
          (a : ℂ) (b : ℂ) (I * (rightAlpha : ℂ))
          (I * (rightBeta : ℂ))).re := by
  rw [Complex.add_re, Complex.neg_re,
    suzukiMixedCoordinateCentralSourceFlux_re_eq_zero_of_real_pureImag
      alpha beta a b rightAlpha rightBeta, add_zero]
  exact neg_pos.mpr XiC_secondDeriv_div_center_re_neg

/-- **Mixed-coordinate no-go.** The quotient obtained by pairing the centered multiplier with an
unrephased physical triangle cannot be Herglotz.  This theorem is a convention falsifier, not a
no-go for Suzuki's correctly normalized physical sheet. -/
theorem not_suzukiMixedCoordinateExteriorWeylQuotient_herglotz_of_real_pureImag_source
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    {a b rightAlphaZero rightBetaZero : ℝ}
    (hWAlpha : HasDerivAt WAlpha (a : ℂ) 0)
    (hWBeta : HasDerivAt WBeta (b : ℂ) 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    (hRightAlpha0 : rightAlpha 0 = I * (rightAlphaZero : ℂ))
    (hRightBeta0 : rightBeta 0 = I * (rightBetaZero : ℂ))
    {alpha beta : ℝ} (hab : alpha ≠ beta) :
    ¬ ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient
        (suzukiCenteredShiftParameter alpha)
        (suzukiCenteredShiftParameter beta)
        WAlpha WBeta rightAlpha rightBeta z).im := by
  intro hHerglotz
  have habCentered : suzukiCenteredShiftParameter alpha ≠
      suzukiCenteredShiftParameter beta :=
    suzukiCenteredShiftParameter_injective.ne hab
  have hneg := suzukiAffineSewnCentralSourceFlux_re_neg_of_herglotz
    hWAlpha hWBeta hWAlpha0 hWBeta0
    (Complex.ofReal_ne_zero.mpr ha) (Complex.ofReal_ne_zero.mpr hb)
    hRightAlpha hRightBeta habCentered hHerglotz
  rw [hRightAlpha0, hRightBeta0] at hneg
  have hzero :=
    suzukiMixedCoordinateCentralSourceFlux_re_eq_zero_of_real_pureImag
      alpha beta a b rightAlphaZero rightBetaZero
  rw [hzero] at hneg
  exact (lt_irrefl 0) hneg

end

end RHTower
