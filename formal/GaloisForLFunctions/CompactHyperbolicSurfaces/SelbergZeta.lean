import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergEulerProduct
import GaloisForLFunctions.CompactHyperbolicSurfaces.SpectralProduct
import GaloisForLFunctions.CompactHyperbolicSurfaces.PsiSeries

/-!
# The Selberg zeta function on `Re s > 0`

Fix `a > 1`, `c = a(a − 1)`, `|F|` the area, `A = Φ(a)/(2a − 1)`, and

  `R(s) = (2s − 1)(A + (|F|/2π) ψ_a(s))`,  `G(s) = A(s² − s) + (|F|/2π) G_a(s)`  (`G' = R`).

* **Continuation of `Φ`.**  On `Re s > 1`, `Φ = R + E'/E` (`lengthSeries_eq`): both sides are
  analytic there and agree at real `s > a` by the trace formula, `D_{a,s}(0) = ψ_a(s)/2π` and
  `E'/E(s) = −(2s − 1) Σ_j ν_j(a, s)`.
* **The zeta function.**  `Z(s) = κ E(s) e^{G(s)}` is holomorphic on `Re s > 0` and equals the Euler
  product on `Re s > 1` (`eulerZeta_eq_selbergZeta`): `Z_E e^{−G}/E` has derivative
  `(Z_E e^{−G}/E)(Φ − R − E'/E) = 0`.
* **Functional equation** on `0 < Re s < 1` (`selbergZeta_one_sub`):
  `Z(1 − s) = Z(s) exp(−|F| ∫_0^1 (s − ½) v tan(πv) dt)`, `v = t(s − ½)`; indeed `E(1 − s) = E(s)` and
  `R(w) + R(1 − w) = |F|(w − ½) tan(π(w − ½))` from `ψ_a(w) − ψ_a(1 − w) = −π cot πw`.
* **Zeros** (`selbergZeta_eq_zero_iff`): on `Re s > 0`, `Z(s) = 0` iff `λ_j + s(s − 1) = 0` for some `j`.
-/

open MeasureTheory Set Real Filter Metric
open scoped MatrixGroups Topology

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

namespace CompactQuotient

variable {X : CompactQuotient}

/-- The area `|F|`. -/
def area (X : CompactQuotient) : ℝ := (volume X.F).toReal

/-- `A = Φ(a)/(2a − 1)`. -/
def zConst (X : CompactQuotient) (a : ℝ) : ℝ := (∑' c : X.NClass, X.realWeight a c) / (2 * a - 1)

/-- `R(s) = (2s − 1)(A + (|F|/2π) ψ_a(s))`. -/
def zR (X : CompactQuotient) (a : ℝ) (s : ℂ) : ℂ :=
  (2 * s - 1) * ((X.zConst a : ℂ) + (X.area / (2 * π) : ℝ) * psiDiff a s)

/-- `G(s) = A(s² − s) + (|F|/2π) G_a(s)`. -/
def zG (X : CompactQuotient) (a : ℝ) (s : ℂ) : ℂ :=
  (X.zConst a : ℂ) * (s * s - s) + (X.area / (2 * π) : ℝ) * gSeries a s

theorem hasDerivAt_zG {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (X.zG a) (X.zR a s) s := by
  have h1 : HasDerivAt (fun s : ℂ => (X.zConst a : ℂ) * (s * s - s)) ((X.zConst a : ℂ) * (2 * s - 1)) s :=
    (((hasDerivAt_id s).mul (hasDerivAt_id s)).sub (hasDerivAt_id s)).const_mul _ |>.congr_deriv
      (by simp only [id]; ring)
  have h2 := (hasDerivAt_gSeries ha hs).const_mul (((X.area / (2 * π) : ℝ)) : ℂ)
  exact (h1.add h2).congr_deriv (by rw [zR]; ring)

theorem differentiableOn_zR {a : ℝ} (ha : 0 < a) : DifferentiableOn ℂ (X.zR a) {s | 0 < s.re} :=
  ((differentiableOn_id.const_mul 2).sub_const 1).mul
    ((differentiableOn_const _).add ((differentiableOn_psiDiff ha).const_mul _))

variable (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a)

include ha in
theorem lam_add_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) (j : X.SpecIndex ha) :
    (X.spectralParam ha j : ℂ) + s * (s - 1) ≠ 0 := by
  intro h
  have hl := X.spectralParam_nonneg ha j
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.sub_im, Complex.one_im,
    Complex.sub_re, Complex.one_re, zero_add, Complex.zero_im, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.zero_re] at him hre
  have hy : s.im = 0 := by
    have : s.im * (2 * s.re - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  rw [hy] at hre
  nlinarith

/-- **`Φ = R + E'/E` at real points** `σ > a`. -/
theorem lengthSeries_eq_real {σ : ℝ} (haσ : a < σ) :
    X.lengthSeries σ = X.zR a σ + logDeriv (X.specProd ha) σ := by
  have hσ1 : 1 < σ := lt_trans ha haσ
  have hσre : 1 < (σ : ℂ).re := by simpa using hσ1
  have ha0 : 0 < a := by linarith
  -- the trace formula
  have htr := X.trace_formula_lengthSeries hhyp ha haσ
  have hD := diffKernel_zero (a := a) (b := σ) (by linarith) haσ.le
  have hD' : diffKernel a σ 0 = 1 / (2 * π) * ∑' k : ℕ, (1 / (a + k) - 1 / (σ + k)) := by
    rw [← hD.tsum_eq, tsum_mul_left]
  -- the spectral side
  have hnu : logDeriv (X.specProd ha) σ =
      ((-(2 * σ - 1) * ∑' j, X.nu ha (b := σ) j : ℝ) : ℂ) := by
    rw [logDeriv_specProd X ha (lam_add_ne_zero_of_one_lt_re ha hσre), Complex.ofReal_mul,
      Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [nu_def]
    push_cast
    ring
  rw [lengthSeries_ofReal, hnu, zR, psiDiff_ofReal]
  have h2σ : (2 * σ - 1) ≠ 0 := by linarith
  have h2a : (2 * a - 1) ≠ 0 := by linarith
  have hΦ : ∑' c : X.NClass, X.realWeight σ c = (2 * σ - 1) * (X.zConst a + X.area * diffKernel a σ 0 -
      ∑' j, X.nu ha (b := σ) j) := by
    rw [zConst, area, htr]
    field_simp
    ring
  rw [hΦ, hD']
  push_cast
  ring

/-- **`Φ = R + E'/E` on `Re s > 1`** (identity theorem). -/
theorem lengthSeries_eq {s : ℂ} (hs : 1 < s.re) :
    X.lengthSeries s = X.zR a s + logDeriv (X.specProd ha) s := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have ha0 : 0 < a := by linarith
  have hE := X.differentiable_specProd ha
  have hEne : ∀ s ∈ U, X.specProd ha s ≠ 0 := fun s hs h => by
    obtain ⟨j, hj⟩ := (X.specProd_eq_zero_iff ha s).mp h
    exact lam_add_ne_zero_of_one_lt_re ha hs j hj
  have hf : AnalyticOnNhd ℂ X.lengthSeries U :=
    (differentiableOn_lengthSeries hhyp).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun s => X.zR a s + logDeriv (X.specProd ha) s) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    refine ((differentiableOn_zR ha0).mono fun s hs => ?_).add ?_
    · show 0 < s.re; have : 1 < s.re := hs; linarith
    · have hd : DifferentiableOn ℂ (deriv (X.specProd ha)) U :=
        (hE.differentiableOn.deriv isOpen_univ).mono (subset_univ _)
      exact (hd.div hE.differentiableOn hEne).congr fun s _ => logDeriv_apply _ _
  have hp : ((a + 1 : ℝ) : ℂ) ∈ U := by show 1 < ((a + 1 : ℝ) : ℂ).re; simp; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((a + 1 : ℝ) : ℂ),
      X.lengthSeries z = X.zR a z + logDeriv (X.specProd ha) z := by
    have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (a + 1)) (𝓝[≠] ((a + 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.tendsto _ |>.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun x hx => by
          simpa using (show x ≠ a + 1 from hx))
    refine htend.frequently ?_
    have hev : ∀ᶠ x in 𝓝[≠] (a + 1 : ℝ), a < x :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
    exact (hev.mono fun x hx => lengthSeries_eq_real hhyp ha hx).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUc hp hfreq hs

/-! ### The zeta function -/

/-- The normalizing constant `κ = Z_E(p) e^{−G(p)}/E(p)`, `p = a + 1`. -/
def zetaConst (X : CompactQuotient) {a : ℝ} (ha : 1 < a) : ℂ :=
  X.eulerZeta ((a + 1 : ℝ) : ℂ) * Complex.exp (-X.zG a ((a + 1 : ℝ) : ℂ)) /
    X.specProd ha ((a + 1 : ℝ) : ℂ)

/-- **The Selberg zeta function** `Z(s) = κ E(s) e^{G(s)}`. -/
def selbergZeta (X : CompactQuotient) {a : ℝ} (ha : 1 < a) (s : ℂ) : ℂ :=
  X.zetaConst ha * X.specProd ha s * Complex.exp (X.zG a s)

/-- **`Z` is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_selbergZeta : DifferentiableOn ℂ (X.selbergZeta ha) {s | 0 < s.re} := by
  have ha0 : 0 < a := by linarith
  intro s hs
  have hG : DifferentiableAt ℂ (X.zG a) s := (hasDerivAt_zG ha0 hs).differentiableAt
  exact ((((differentiableAt_const _).mul (X.differentiable_specProd ha s)).mul
    hG.cexp)).differentiableWithinAt

/-- **The Euler product.**  On `Re s > 1`, `Z(s) = Π_{p, k} (1 − e^{−(s+k)ℓ_p})`. -/
theorem eulerZeta_eq_selbergZeta {s : ℂ} (hs : 1 < s.re) : X.eulerZeta s = X.selbergZeta ha s := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have ha0 : 0 < a := by linarith
  have hEne : ∀ s ∈ U, X.specProd ha s ≠ 0 := fun s hs h => by
    obtain ⟨j, hj⟩ := (X.specProd_eq_zero_iff ha s).mp h
    exact lam_add_ne_zero_of_one_lt_re ha hs j hj
  set H : ℂ → ℂ := fun s => X.eulerZeta s * Complex.exp (-X.zG a s) / X.specProd ha s
  have hderiv : ∀ s ∈ U, HasDerivAt H 0 s := by
    intro s hs
    have hs' : 1 < s.re := hs
    have hs0 : 0 < s.re := by linarith
    have hZ : HasDerivAt X.eulerZeta (X.lengthSeries s * X.eulerZeta s) s := by
      have hd := ((differentiableOn_eulerZeta hhyp) s hs).differentiableAt (hU.mem_nhds hs)
      have hl := logDeriv_eulerZeta hhyp hs'
      rw [logDeriv_apply] at hl
      have : deriv X.eulerZeta s = X.lengthSeries s * X.eulerZeta s := by
        rw [← hl, div_mul_cancel₀ _ (eulerZeta_ne_zero hhyp hs')]
      rw [← this]; exact hd.hasDerivAt
    have hE : HasDerivAt (X.specProd ha) (logDeriv (X.specProd ha) s * X.specProd ha s) s := by
      have : deriv (X.specProd ha) s = logDeriv (X.specProd ha) s * X.specProd ha s := by
        rw [logDeriv_apply, div_mul_cancel₀ _ (hEne s hs)]
      rw [← this]; exact (X.differentiable_specProd ha s).hasDerivAt
    have hG := (hasDerivAt_zG ha0 hs0).neg.cexp
    have hH := (hZ.mul hG).div hE (hEne s hs)
    refine hH.congr_deriv ?_
    have hid := lengthSeries_eq hhyp ha hs'
    have hne := hEne s hs
    rw [hid]
    field_simp
    ring
  have hconst : ∀ s ∈ U, H s = H ((a + 1 : ℝ) : ℂ) := by
    intro s hs
    have hp : ((a + 1 : ℝ) : ℂ) ∈ U := by show 1 < ((a + 1 : ℝ) : ℂ).re; simp; linarith
    refine hU.is_const_of_deriv_eq_zero hUc (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hderiv s hs).deriv) hs hp
  have h := hconst s hs
  simp only [H] at h
  rw [selbergZeta, zetaConst, ← h]
  have hne := hEne s hs
  field_simp
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem zetaConst_ne_zero : X.zetaConst ha ≠ 0 := by
  have hp : 1 < ((a + 1 : ℝ) : ℂ).re := by simp; linarith
  have hEne : X.specProd ha ((a + 1 : ℝ) : ℂ) ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := (X.specProd_eq_zero_iff ha _).mp h
    exact lam_add_ne_zero_of_one_lt_re ha hp j hj
  exact div_ne_zero (mul_ne_zero (eulerZeta_ne_zero hhyp hp) (Complex.exp_ne_zero _)) hEne

/-- **The zeros of `Z`.** -/
theorem selbergZeta_eq_zero_iff (s : ℂ) :
    X.selbergZeta ha s = 0 ↔ ∃ j : X.SpecIndex ha, (X.spectralParam ha j : ℂ) + s * (s - 1) = 0 := by
  rw [selbergZeta, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), mul_eq_zero,
    or_iff_right (zetaConst_ne_zero hhyp ha), specProd_eq_zero_iff]

/-! ### The functional equation -/

theorem zR_add_zR_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    X.zR a w + X.zR a (1 - w) = X.area * ((w - 1 / 2) * Complex.tan (π * (w - 1 / 2))) := by
  have ha0 : 0 < a := by linarith
  have hψ := psiDiff_sub_psiDiff_one_sub ha0 h0 h1
  have hcot : Complex.cot (π * w) = -Complex.tan (π * (w - 1 / 2)) := by
    have e : (π : ℂ) * w = π * (w - 1 / 2) + π / 2 := by ring
    rw [e, Complex.cot_eq_cos_div_sin, Complex.tan_eq_sin_div_cos, Complex.cos_add_pi_div_two,
      Complex.sin_add_pi_div_two, neg_div]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [zR, zR, hcot] at *
  have e : (2 * w - 1) * ((X.zConst a : ℂ) + (X.area / (2 * π) : ℝ) * psiDiff a w) +
      (2 * (1 - w) - 1) * ((X.zConst a : ℂ) + (X.area / (2 * π) : ℝ) * psiDiff a (1 - w)) =
      (2 * w - 1) * ((X.area / (2 * π) : ℝ) * (psiDiff a w - psiDiff a (1 - w))) := by ring
  rw [e, hψ, hcot]
  push_cast
  field_simp
  ring

/-- **The functional equation.**  For `0 < Re s < 1`,
`Z(1 − s) = Z(s) exp(−|F| ∫_0^1 (s − ½) v tan(πv) dt)`, `v = t(s − ½)`. -/
theorem selbergZeta_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    X.selbergZeta ha (1 - s) = X.selbergZeta ha s * Complex.exp (-(X.area *
      ∫ t in (0 : ℝ)..1, (s - 1 / 2) * (((t : ℂ) * (s - 1 / 2)) *
        Complex.tan (π * ((t : ℂ) * (s - 1 / 2)))))) := by
  have ha0 : 0 < a := by linarith
  -- `Q(w) = G(1 − w) − G(w)` along the segment `w(t) = ½ + t(s − ½)`
  set w : ℝ → ℂ := fun t => 1 / 2 + (t : ℂ) * (s - 1 / 2)
  have hw_strip : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < (w t).re ∧ (w t).re < 1 := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    simp only [w, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
    norm_num
    constructor <;> nlinarith
  set Q : ℂ → ℂ := fun z => X.zG a (1 - z) - X.zG a z
  have hQ : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      HasDerivAt Q (-(X.zR a (1 - z)) - X.zR a z) z := by
    intro z hz0 hz1
    have h1' : HasDerivAt (fun z => X.zG a (1 - z)) (X.zR a (1 - z) * (-1)) z := by
      have := (hasDerivAt_zG ha0 (s := 1 - z) (by simp; linarith)).comp z
        ((hasDerivAt_id z).const_sub 1)
      simpa using this
    exact (h1'.sub (hasDerivAt_zG ha0 hz0)).congr_deriv (by ring)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Q (w t))
      ((-(X.zR a (1 - w t)) - X.zR a (w t)) * (s - 1 / 2)) t := by
    intro t ht
    obtain ⟨hw0, hw1⟩ := hw_strip t ht
    have hwd : HasDerivAt (fun z : ℂ => 1 / 2 + z * (s - 1 / 2)) (s - 1 / 2) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (s - 1 / 2)).const_add (1 / 2 : ℂ)
    have := ((hQ (w t) hw0 hw1).comp (t : ℂ) hwd).comp_ofReal
    exact this
  have hcont : ContinuousOn (fun t : ℝ => (-(X.zR a (1 - w t)) - X.zR a (w t)) * (s - 1 / 2))
      (uIcc 0 1) := by
    have hR : ContinuousOn (X.zR a) {z | 0 < z.re} := (differentiableOn_zR ha0).continuousOn
    have hwc : Continuous w := by simp only [w]; fun_prop
    refine ContinuousOn.mul (ContinuousOn.sub (ContinuousOn.neg ?_) ?_) continuousOn_const
    · exact hR.comp (continuous_const.sub hwc).continuousOn fun t ht => by
        show 0 < (1 - w t).re; simp; linarith [(hw_strip t ht).2]
    · exact hR.comp hwc.continuousOn fun t ht => (hw_strip t ht).1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hQ0 : Q (w 0) = 0 := by simp only [Q, w]; push_cast; ring_nf
  have hQ1 : w 1 = s := by simp only [w]; push_cast; ring
  rw [hQ1, hQ0, sub_zero] at hftc
  -- the integrand in tangent form
  have hint : ∫ t in (0 : ℝ)..1, (-(X.zR a (1 - w t)) - X.zR a (w t)) * (s - 1 / 2) =
      -(X.area * ∫ t in (0 : ℝ)..1, (s - 1 / 2) * (((t : ℂ) * (s - 1 / 2)) *
        Complex.tan (π * ((t : ℂ) * (s - 1 / 2))))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    obtain ⟨hw0, hw1⟩ := hw_strip t ht
    have h := zR_add_zR_one_sub ha hw0 hw1
    have hv : w t - 1 / 2 = (t : ℂ) * (s - 1 / 2) := by simp only [w]; ring
    rw [hv] at h
    simp only
    linear_combination (s - 1 / 2) * h
  rw [hint] at hftc
  -- assemble
  rw [selbergZeta, selbergZeta, specProd_one_sub, ← hftc]
  simp only [Q]
  rw [mul_assoc, mul_assoc, ← Complex.exp_add]
  ring_nf

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
