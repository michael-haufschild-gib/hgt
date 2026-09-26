import GaloisForLFunctions.RHTower.HalfWeightShimuraKernel
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The forced zero of the Shimura transform of an exceptional Maass form

For a Maass cusp form `f` on `Γ₀(N+1)` with `λ = 1/4 - τ²`, `0 < τ < 1/2`, and the kernel
`G(z) = f(4z) \overline{θ(z)} y^{1/4}`:

* **`integral_mode`**: `∫_0^∞ y^{w-7/4} e^{-Ay} W_τ(Ay) dy = A^{3/4-w} Mel_τ(w - 1/4)` with
  `Mel_τ(μ) = 2^{μ-1}Γ(μ)Γ(μ+τ)Γ(μ-τ)/Γ(2μ)` (`integral_Kb_exp_cpow` after `y ↦ Ay`);
* `integrableOn_Gsh_strip`: `G y^w` is integrable on the strip for `Re w > 7/4`;
* `inner_integral`: `∫_0^1 G(x+iy) y^{w-2} dx = y^{w-7/4} Σ_j e^{-8πj²y} ρ_{j²} W_τ(8πj²y)`;
* **`strip_integral_Gsh`**: `∫_{strip} G y^w dμ = (Σ_j ρ_{j²}(8πj²)^{3/4-w}) Mel_τ(w - 1/4)`
  (Fubini, then termwise Mellin transforms dominated by `|j|^{3/2-2Re w}`);
* `summable_zCoef`: absolute convergence of `Z(w) = Σ_j ρ_{j²}(8πj²)^{3/4-w}` on `Re w > 5/4`;
* `invMel`: `1/Mel_τ`, holomorphic on `Re μ > 0` (`1/Γ` entire, `Γ(2μ)` pole-free), with
  `invMel τ τ = 0` since `1/Γ(0) = 0`;
* `regF_quarter_add_ne_zero`: `ρ(1/4+τ) = (4τ-2)(4τ-1)ζ(4τ) ≠ 0`;
* **`shimura_forced_zero`**: `Ẑ = I·Mel_τ(w-1/4)⁻¹/(2ρ)`, with `I` the folded Rankin–Selberg
  integral against the regularised weight-½ Eisenstein series, is holomorphic on `Re w > 1/4` off
  the zeros of `ρ`, equals `Z` on `Re w > 7/4`, and vanishes at `w = 1/4 + τ`.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### The Mellin transform of one Whittaker mode -/

/-- `Mel_τ(μ) = 2^{μ-1} Γ(μ) Γ(μ+τ) Γ(μ-τ) / Γ(2μ)`. -/
def melK (τ : ℝ) (μ : ℂ) : ℂ :=
  (2 : ℂ) ^ (μ - 1) * Complex.Gamma μ * Complex.Gamma (μ + τ) * Complex.Gamma (μ - τ) /
    Complex.Gamma (2 * μ)

theorem ofReal_cpow_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a * b : ℝ) : ℂ) ^ s = (a : ℂ) ^ s * (b : ℂ) ^ s := by
  push_cast; exact Complex.mul_cpow_ofReal_nonneg ha.le hb.le s

theorem sqrt_mul_cpow {t : ℝ} (ht : 0 < t) (s : ℂ) :
    (Real.sqrt t : ℂ) * (t : ℂ) ^ s = (t : ℂ) ^ (s + 1 / 2) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [Complex.cpow_add _ _ ht0, Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
  push_cast; ring

/-- **One Whittaker mode**: for `A > 0` and `Re w > 1/4 + τ`,
`∫_0^∞ y^{w-7/4} e^{-Ay} W_τ(Ay) dy = A^{3/4-w} Mel_τ(w - 1/4)`. -/
theorem integral_mode {τ : ℝ} (hτ : 0 ≤ τ) {A : ℝ} (hA : 0 < A) {w : ℂ} (hw : 1 / 4 + τ < w.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 7 / 4) * ((Real.exp (-(A * y)) : ℝ) : ℂ) * Wh τ (A * y) =
      (A : ℂ) ^ (3 / 4 - w) * melK τ (w - 1 / 4) := by
  have hμ : |((τ : ℂ)).re| < (w - 1 / 4).re := by
    simp only [Complex.ofReal_re, Complex.sub_re]
    rw [abs_of_nonneg hτ]; norm_num; linarith
  have hM := integral_Kb_exp_cpow hμ
  set g : ℝ → ℂ := fun t => ((t / A : ℝ) : ℂ) ^ (w - 7 / 4) * ((Real.exp (-t) : ℝ) : ℂ) * Wh τ t
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi g 0 hA
  simp only [mul_zero] at hsub
  have e1 : ∀ y : ℝ, g (A * y) = (y : ℂ) ^ (w - 7 / 4) * ((Real.exp (-(A * y)) : ℝ) : ℂ) * Wh τ (A * y) := by
    intro y; simp only [g]; rw [mul_div_cancel_left₀ _ hA.ne']
  simp_rw [e1] at hsub
  rw [hsub]
  have e2 : ∀ t ∈ Ioi (0 : ℝ), g t = (A : ℂ) ^ (-(w - 7 / 4)) *
      (Kb (τ : ℂ) t * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((w - 1 / 4) - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    simp only [g, Wh]
    rw [div_eq_mul_inv, ofReal_cpow_mul_pos ht0 (inv_pos.2 hA), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
    have hs := sqrt_mul_cpow ht0 (w - 7 / 4)
    rw [show w - 1 / 4 - 1 = w - 7 / 4 + 1 / 2 by ring, ← hs]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, hM, Complex.real_smul,
    Complex.ofReal_inv]
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e3 : (A : ℂ)⁻¹ * (A : ℂ) ^ (-(w - 7 / 4)) = (A : ℂ) ^ (3 / 4 - w) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hA0]; congr 1; ring
  unfold melK
  rw [← e3]
  ring


/-! ### The Shimura strip integral -/

section Strip

open SelbergMaassFourier SelbergMaassMean
open _root_.RHTower GaloisForLFunctions.RHTower

variable {N : ℕ} {τ : ℝ}
  {f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ))}

/-- A global exponential bound `‖f(4z)‖ ≤ K e^{-c Im z}`. -/
theorem f_four_global (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ z : ℍ, ‖(f.1.1 ∘ ofComplex) (4 * (z : ℂ))‖ ≤ K * Real.exp (-c * z.im) := by
  obtain ⟨C, c, t₀, hC0, hc, ht₀, hdecay⟩ := f_four_decay (f := f) hτ0 hτ1 1
  obtain ⟨Bf, hBf⟩ := gz_bounded f
  refine ⟨max C (max Bf 0 * Real.exp (c * t₀)), c, le_max_of_le_left hC0, hc, fun z => ?_⟩
  rcases le_or_gt t₀ z.im with h | h
  · have := hdecay z h
    rw [one_smul] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := hBf (ofComplex (4 * (z : ℂ)))
    have h2 : Bf ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * z.im) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 1 ≤ Real.exp (c * t₀ + -c * z.im) := Real.one_le_exp (by nlinarith)
      nlinarith [le_max_left Bf 0, le_max_right Bf 0]
    calc _ ≤ Bf := h1
      _ ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * z.im) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem modularStrip_eq_coord :
    GaloisForLFunctions.HTGeometry.modularStrip = {z : ℍ | (z.re, z.im) ∈ Ico (0 : ℝ) 1 ×ˢ Ioi 0} := by
  ext z; simp [GaloisForLFunctions.HTGeometry.modularStrip, z.im_pos]

theorem ofComplex_mk {x y : ℝ} (hy : 0 < y) : ((ofComplex (⟨x, y⟩ : ℂ) : ℍ) : ℂ) = ⟨x, y⟩ := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]

/-- **Integrability on the strip** for `Re w > 7/4`. -/
theorem integrableOn_Gsh_strip (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 7 / 4 < w.re) :
    IntegrableOn (fun z : ℍ => Gsh N f z * ((z.im : ℝ) : ℂ) ^ w) GaloisForLFunctions.HTGeometry.modularStrip := by
  obtain ⟨K, c, hK0, hc, hK⟩ := f_four_global (f := f) hτ0 hτ1
  have hA : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  have hpos : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ), 0 < p.2 := fun p hp => hp.2
  rw [modularStrip_eq_coord, GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable.integrableOn_coord_iff hA hpos]
  -- the dominating function
  set g : ℝ → ℝ := fun y => K * (y ^ (w.re - 7 / 4) * Real.exp (-c * y ^ (1 : ℝ)) +
    1 / π * (y ^ (w.re - 11 / 4) * Real.exp (-c * y ^ (1 : ℝ))))
  have hg : IntegrableOn g (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 7 / 4) (b := c) (by linarith)
      le_rfl hc
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 11 / 4) (b := c) (by linarith)
      le_rfl hc
    exact (h1.add (h2.const_mul (1 / π))).const_mul K
  have hprod := (integrable_const (1 : ℝ) (μ := volume.restrict (Ico (0 : ℝ) 1))).mul_prod hg
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Integrable.mono' hprod ?_ ?_
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_) hA
    have hp2 : 0 < p.2 := hp.2
    have hmk : ContinuousWithinAt (fun p : ℝ × ℝ => (ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ))
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have e : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      have hc1 : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by rw [e]; fun_prop
      have hc2 : ContinuousAt (ofComplex : ℂ → ℍ) (⟨p.1, p.2⟩ : ℂ) :=
        (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) (by simpa using hp2)).continuousAt
      exact (ContinuousAt.comp (x := p) (f := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        (g := (ofComplex : ℂ → ℍ)) hc2 hc1.continuousAt).continuousWithinAt
    have hG := ((continuous_Gsh N f).continuousAt).comp_continuousWithinAt hmk
    have hy : ContinuousWithinAt (fun p : ℝ × ℝ => ((ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ).im : ℂ) ^ w)
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have := (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (UpperHalfPlane.continuous_im.continuousAt.comp_continuousWithinAt hmk))
      refine this.cpow continuousWithinAt_const ?_
      simp only [Function.comp]
      exact Complex.ofReal_mem_slitPlane.2 (ofComplex (⟨p.1, p.2⟩ : ℂ)).im_pos
    exact (hG.mul hy).div (by fun_prop) (by exact_mod_cast (pow_pos hp2 2).ne')
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem hA fun p hp => ?_
    have hp2 : 0 < p.2 := hp.2
    set z : ℍ := ofComplex (⟨p.1, p.2⟩ : ℂ)
    have hz : (z : ℂ) = ⟨p.1, p.2⟩ := ofComplex_mk hp2
    have hzim : z.im = p.2 := by simp [UpperHalfPlane.im, hz]
    simp only [one_mul]
    rw [norm_div, norm_mul, Gsh, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp2, hzim]
    have hf := hK z
    rw [hzim] at hf
    have hθ := norm_theta_le (v := (z : ℂ)) z.im_pos
    have hzim' : (z : ℂ).im = p.2 := by rw [hz]
    rw [hzim'] at hθ
    set y := p.2
    have hy14 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 = y ^ (w.re - 7 / 4) := by
      rw [← Real.rpow_add hp2, ← Real.rpow_natCast, ← Real.rpow_sub hp2]; congr 1; push_cast; ring
    have hy11 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y = y ^ (w.re - 11 / 4) := by
      rw [hy14, ← Real.rpow_sub_one hp2.ne']; congr 1; ring
    simp only [g, Real.rpow_one]
    calc ‖(f.1.1 ∘ ofComplex) (4 * (z : ℂ))‖ * ‖theta z‖ * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2
        ≤ K * Real.exp (-c * y) * (1 + 1 / (π * y)) * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 := by
          gcongr
      _ = K * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 * Real.exp (-c * y) +
            1 / π * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y * Real.exp (-c * y))) := by
          field_simp
      _ = _ := by rw [hy11, hy14]

variable (f) in
/-- The Whittaker modes `a_j(y) = e^{-8πj²y} ρ_{j²} W_τ(8πj²y)`. -/
def aMode (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (j : ℤ) (y : ℝ) : ℂ :=
  ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
    (rhoW f hτ0 hτ1 (j ^ 2) * Wh τ (8 * π * (j : ℝ) ^ 2 * y))

variable (f) in
/-- The Dirichlet coefficients `ρ_{j²} (8πj²)^{3/4-w}` (and `0` at `j = 0`). -/
def zCoef (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (w : ℂ) (j : ℤ) : ℂ :=
  if j = 0 then 0 else rhoW f hτ0 hτ1 (j ^ 2) * ((8 * π * (j : ℝ) ^ 2 : ℝ) : ℂ) ^ (3 / 4 - w)

theorem Gsh_coord {x y : ℝ} (hy : 0 < y) :
    Gsh N f (ofComplex (⟨x, y⟩ : ℂ)) = (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
      starRingEnd ℂ (theta (point x y)) * ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  have hz := ofComplex_mk (x := x) hy
  have hp : (⟨x, y⟩ : ℂ) = point x y := by apply Complex.ext <;> simp [point]
  have him : (ofComplex (⟨x, y⟩ : ℂ)).im = y := by
    rw [UpperHalfPlane.im, hz]
  unfold Gsh
  rw [him, hz, hp]
  congr 3
  simp only [point]; push_cast; ring

/-- **The horizontal integral** at height `y`: `∫_0^1 G(x+iy) y^{w-2} dx = y^{w-7/4} Σ_j a_j(y)`. -/
theorem inner_integral (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (w : ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, Gsh N f (ofComplex (⟨x, y⟩ : ℂ)) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) * ∑' j : ℤ, aMode f hτ0 hτ1 j y := by
  have h := (hasSum_zeroth (N := N) (f := f) hτ0 hτ1 hy).tsum_eq
  have hc : ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0,
      ← Complex.cpow_sub _ _ hy0]
    congr 1; push_cast; ring
  simp_rw [Gsh_coord hy]
  have e : ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point x y)) *
      ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point x y))) *
        ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    intro x; rw [← hc]; ring
  simp_rw [e]
  rw [integral_mul_const, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← h, mul_comm]
  rfl

theorem rhoW_zero (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) : rhoW f hτ0 hτ1 0 = 0 := by
  rw [rhoW, dif_pos rfl]

/-- **The Mellin transform of each mode**: `∫_0^∞ y^{w-7/4} a_j(y) dy = ρ_{j²}(8πj²)^{3/4-w} Mel_τ(w-1/4)`. -/
theorem integral_aMode (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (j : ℤ) {w : ℂ} (hw : 1 / 4 + τ < w.re) :
    ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y =
      zCoef f hτ0 hτ1 w j * melK τ (w - 1 / 4) := by
  by_cases hj : j = 0
  · subst hj
    simp [aMode, zCoef, rhoW_zero]
  · have hA : 0 < 8 * π * (j : ℝ) ^ 2 := by
      have : (0 : ℝ) < (j : ℝ) ^ 2 := by
        have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
        positivity
      positivity
    have e : ∀ y : ℝ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y =
        rhoW f hτ0 hτ1 (j ^ 2) * (((y : ℝ) : ℂ) ^ (w - 7 / 4) *
          ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) * Wh τ (8 * π * (j : ℝ) ^ 2 * y)) := by
      intro y; simp only [aMode]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_mode hτ0.le hA hw, zCoef, if_neg hj]
    ring

/-- **Norm bound for each mode**, `Re w > 3/4`. -/
theorem integral_norm_aMode_le (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {R : ℝ}
    (hR : ∀ k : ℤ, ‖rhoW f hτ0 hτ1 k‖ ≤ R) (j : ℤ) {w : ℂ} (hw : 3 / 4 < w.re) :
    IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y‖ ≤
      R * Real.sqrt (2 * π) * Real.Gamma (w.re - 3 / 4) * (8 * π) ^ (3 / 4 - w.re) *
        |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
  have hτ : |τ| ≤ 1 / 2 := by rw [abs_of_pos hτ0]; linarith
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  by_cases hj : j = 0
  · subst hj
    have hz : ∀ y : ℝ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 0 y = 0 := by
      intro y; simp [aMode, rhoW_zero]
    simp_rw [hz]
    refine ⟨integrableOn_zero, ?_⟩
    simp only [norm_zero, integral_zero, Int.cast_zero, abs_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  set A : ℝ := 8 * π * (j : ℝ) ^ 2
  have hA : 0 < A := by
    have : (0 : ℝ) < (j : ℝ) ^ 2 := by
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      positivity
    simp only [A]; positivity
  set σ := w.re
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 7 / 4) (b := A) (by linarith)
    le_rfl hA
  simp only [Real.rpow_one] at hmaj
  have hW : ∀ y ∈ Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y‖ ≤
      R * Real.sqrt (2 * π) * (y ^ (σ - 7 / 4) * Real.exp (-A * y)) := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, aMode, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hWb := norm_Wh_le hτ (t := A * y) (by positivity)
    have hs2 : Real.sqrt Real.pi * Real.sqrt 2 = Real.sqrt (2 * π) := by
      rw [← Real.sqrt_mul Real.pi_pos.le]; ring_nf
    rw [hs2] at hWb
    have hre : (w - 7 / 4).re = σ - 7 / 4 := by simp [σ]
    rw [hre, show -(8 * π * (j : ℝ) ^ 2 * y) = -A * y by simp only [A]; ring,
      show 8 * π * (j : ℝ) ^ 2 * y = A * y by simp only [A]]
    calc y ^ (σ - 7 / 4) * (Real.exp (-A * y) * (‖rhoW f hτ0 hτ1 (j ^ 2)‖ * ‖Wh τ (A * y)‖))
        ≤ y ^ (σ - 7 / 4) * (Real.exp (-A * y) * (R * Real.sqrt (2 * π))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul (hR _) hWb (norm_nonneg _) hR0
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    refine ContinuousAt.continuousWithinAt ?_
    have hc1 : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4)) y :=
      Complex.continuous_ofReal.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.2 hy0)
    have hc2 : ContinuousAt (fun y : ℝ => Wh τ (8 * π * (j : ℝ) ^ 2 * y)) y :=
      ((hasDerivAt_Wh (by positivity) (τ : ℂ)).continuousAt).comp (by fun_prop : Continuous
        fun y : ℝ => 8 * π * (j : ℝ) ^ 2 * y).continuousAt
    simp only [aMode]
    exact hc1.mul ((by fun_prop : Continuous fun y : ℝ =>
      ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ)).continuousAt.mul (continuousAt_const.mul hc2))
  have hint : IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y) (Ioi 0) :=
    (hmaj.const_mul (R * Real.sqrt (2 * π))).mono' hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioi hW)
  refine ⟨hint, ?_⟩
  calc ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y‖
      ≤ ∫ y in Ioi (0 : ℝ), R * Real.sqrt (2 * π) * (y ^ (σ - 7 / 4) * Real.exp (-A * y)) :=
        setIntegral_mono_on hint.norm (hmaj.const_mul _) measurableSet_Ioi hW
    _ = R * Real.sqrt (2 * π) * ((1 / A) ^ (σ - 3 / 4) * Real.Gamma (σ - 3 / 4)) := by
        rw [integral_const_mul]
        have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ - 3 / 4) (r := A) (by linarith) hA
        rw [show σ - 3 / 4 - 1 = σ - 7 / 4 by ring] at this
        simp_rw [show ∀ y : ℝ, -A * y = -(A * y) by intro y; ring]
        rw [this]
    _ = _ := by
        have hj2 : (j : ℝ) ^ 2 = |(j : ℝ)| ^ (2 : ℝ) := by
          rw [Real.rpow_two, sq_abs]
        rw [one_div, Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]
        simp only [A]
        rw [Real.mul_rpow (by positivity) (sq_nonneg _), hj2, ← Real.rpow_mul (abs_nonneg _)]
        rw [show -(σ - 3 / 4) = 3 / 4 - σ by ring, show (2 : ℝ) * (3 / 4 - σ) = -(2 * σ - 3 / 2) by ring]
        ring

/-- **The Shimura strip integral** for `Re w > 7/4`:
`∫_{strip} G(z) y^w dμ = (Σ_j ρ_{j²}(8πj²)^{3/4-w}) Mel_τ(w - 1/4)`. -/
theorem strip_integral_Gsh (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 7 / 4 < w.re) :
    ∫ z in GaloisForLFunctions.HTGeometry.modularStrip, Gsh N f z * ((z.im : ℝ) : ℂ) ^ w =
      (∑' j : ℤ, zCoef f hτ0 hτ1 w j) * melK τ (w - 1 / 4) := by
  obtain ⟨R, hR0, hR⟩ := rhoW_bounded (N := N) (f := f) hτ0 hτ1
  have hw34 : 3 / 4 < w.re := by linarith
  have hwτ : 1 / 4 + τ < w.re := by linarith
  rw [GaloisForLFunctions.HTGeometry.setIntegral_modularStrip_eq_iterated _
    (integrableOn_Gsh_strip hτ0 hτ1 hw)]
  have e : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1,
      Gsh N f (ofComplex ⟨x, y⟩) * (((ofComplex (⟨x, y⟩ : ℂ)).im : ℝ) : ℂ) ^ w =
      ∑' j : ℤ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y := by
    intro y hy
    have hy0 : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex (⟨x, y⟩ : ℂ)).im = y := fun x => by
      rw [UpperHalfPlane.im, ofComplex_mk hy0]
    simp_rw [him]
    have h := inner_integral (N := N) (f := f) hτ0 hτ1 w hy0
    rw [integral_div] at h
    rw [tsum_mul_left, ← h, Complex.real_smul, div_eq_inv_mul]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    ← integral_tsum_of_summable_integral_norm (fun j => (integral_norm_aMode_le hτ0 hτ1 hR j hw34).1)]
  · simp_rw [integral_aMode (f := f) hτ0 hτ1 _ hwτ]
    exact tsum_mul_right
  · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => (integral_norm_aMode_le hτ0 hτ1 hR j hw34).2) ?_
    exact (Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left _

theorem norm_zCoef_le (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {R : ℝ}
    (hR : ∀ k : ℤ, ‖rhoW f hτ0 hτ1 k‖ ≤ R) (w : ℂ) (j : ℤ) :
    ‖zCoef f hτ0 hτ1 w j‖ ≤ R * (8 * π) ^ (3 / 4 - w.re) * |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  by_cases hj : j = 0
  · subst hj; rw [zCoef, if_pos rfl, norm_zero]
    exact mul_nonneg (mul_nonneg hR0 (by positivity)) (by positivity)
  have hj0 : (0 : ℝ) < |(j : ℝ)| := abs_pos.2 (by exact_mod_cast hj)
  rw [zCoef, if_neg hj, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have e : (8 * π * (j : ℝ) ^ 2) ^ (3 / 4 - w).re =
      (8 * π) ^ (3 / 4 - w.re) * |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
    rw [show (3 / 4 - w).re = 3 / 4 - w.re by simp, Real.mul_rpow (by positivity) (sq_nonneg _),
      ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
    congr 2; push_cast; ring
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hR _) (by positivity)) (by positivity)

/-- The Dirichlet series `Σ_j ρ_{j²}(8πj²)^{3/4-w}` converges absolutely for `Re w > 5/4`. -/
theorem summable_zCoef (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 5 / 4 < w.re) :
    Summable (zCoef f hτ0 hτ1 w) := by
  obtain ⟨R, -, hR⟩ := rhoW_bounded (N := N) (f := f) hτ0 hτ1
  refine Summable.of_norm_bounded
    ((Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left
      (R * (8 * π) ^ (3 / 4 - w.re))) fun j => ?_
  exact norm_zCoef_le hτ0 hτ1 hR w j

end Strip

/-! ### The forced zero -/

/-- `1/Mel_τ(μ) = Γ(2μ) 2^{1-μ} / (Γ(μ)Γ(μ+τ)Γ(μ-τ))`. -/
def invMel (τ : ℝ) (μ : ℂ) : ℂ :=
  Complex.Gamma (2 * μ) * (2 : ℂ) ^ (1 - μ) * (Complex.Gamma μ)⁻¹ * (Complex.Gamma (μ + τ))⁻¹ *
    (Complex.Gamma (μ - τ))⁻¹

/-- `1/Mel_τ` is holomorphic on `Re μ > 0`: `1/Γ` is entire and `Γ(2μ)` has no pole there. -/
theorem differentiableAt_invMel (τ : ℝ) {μ : ℂ} (hμ : 0 < μ.re) : DifferentiableAt ℂ (invMel τ) μ := by
  have hG : DifferentiableAt ℂ (fun μ : ℂ => Complex.Gamma (2 * μ)) μ := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp μ (differentiableAt_id.const_mul 2)
    have h' := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re,
      Complex.re_ofNat, Complex.im_ofNat] at h'
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hinv := Complex.differentiable_one_div_Gamma
  have h2 : DifferentiableAt ℂ (fun μ : ℂ => (2 : ℂ) ^ (1 - μ)) μ :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  unfold invMel
  exact (((hG.mul h2).mul (hinv μ)).mul ((hinv.comp (differentiable_id.add_const _)) μ)).mul
    ((hinv.comp (differentiable_id.sub_const _)) μ)

theorem melK_mul_invMel {τ : ℝ} {μ : ℂ} (h1 : 0 < μ.re - |τ|) : melK τ μ * invMel τ μ = 1 := by
  have hμ : 0 < μ.re := by linarith [abs_nonneg τ]
  have hp : 0 < (μ + τ).re := by simp; linarith [neg_abs_le τ]
  have hm : 0 < (μ - τ).re := by simp; linarith [le_abs_self τ]
  have h2μ : 0 < (2 * μ).re := by simp; linarith
  have e2 : (2 : ℂ) ^ (μ - 1) * (2 : ℂ) ^ (1 - μ) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero]; simp
  have g1 := Complex.Gamma_ne_zero_of_re_pos hμ
  have g2 := Complex.Gamma_ne_zero_of_re_pos hp
  have g3 := Complex.Gamma_ne_zero_of_re_pos hm
  have g4 := Complex.Gamma_ne_zero_of_re_pos h2μ
  unfold melK invMel
  rw [div_eq_mul_inv]
  calc _ = ((2 : ℂ) ^ (μ - 1) * (2 : ℂ) ^ (1 - μ)) * (Complex.Gamma μ * (Complex.Gamma μ)⁻¹) *
        (Complex.Gamma (μ + τ) * (Complex.Gamma (μ + τ))⁻¹) *
        (Complex.Gamma (μ - τ) * (Complex.Gamma (μ - τ))⁻¹) *
        (Complex.Gamma (2 * μ) * (Complex.Gamma (2 * μ))⁻¹) := by ring
    _ = 1 := by
      rw [e2, mul_inv_cancel₀ g1, mul_inv_cancel₀ g2, mul_inv_cancel₀ g3, mul_inv_cancel₀ g4]; ring

theorem invMel_self (τ : ℝ) : invMel τ τ = 0 := by
  simp [invMel, Complex.Gamma_zero]

theorem regF_ne_zero_of_one_lt {w : ℂ} (hw : 1 < w.re) : regF w ≠ 0 := by
  unfold regF
  have h3 : 4 * w - 3 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1 : 4 * w - 1 ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [RHTower.zetaResidueFactor_of_ne h1]
  refine mul_ne_zero h3 (mul_ne_zero (fun h => ?_) (riemannZeta_ne_zero_of_one_le_re ?_))
  · have := congrArg Complex.re h; simp at this; linarith
  · simp; linarith

/-- `ρ(1/4 + τ) = (4τ-2)(4τ-1)ζ(4τ) ≠ 0` for `0 < τ < 1/2`. -/
theorem regF_quarter_add_ne_zero {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) :
    regF (1 / 4 + τ) ≠ 0 := by
  unfold regF
  have e1 : 4 * (1 / 4 + (τ : ℂ)) - 3 = ((4 * τ - 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : 4 * (1 / 4 + (τ : ℂ)) - 1 = ((4 * τ : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]
  refine mul_ne_zero (by exact_mod_cast (show 4 * τ - 2 ≠ 0 by linarith)) ?_
  by_cases h : 4 * τ = 1
  · rw [h]; simp
  have h1 : ((4 * τ : ℝ) : ℂ) ≠ 1 := by exact_mod_cast h
  rw [RHTower.zetaResidueFactor_of_ne h1]
  refine mul_ne_zero (sub_ne_zero.2 h1) ?_
  rcases lt_or_gt_of_ne h with h' | h'
  · exact RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) h'
  · exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

section ForcedZero

open SelbergMaassFourier SelbergMaassMean
open _root_.RHTower GaloisForLFunctions.RHTower

variable (N : ℕ) {τ : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ)))

/-- The regularised Shimura transform `Ẑ(w) = I(w) Mel_τ(w - 1/4)⁻¹ / (2ρ(w))`, where `I` is the folded
Rankin–Selberg integral of the kernel `G(z) = f(4z) θ̄(z) y^{1/4}` against the regularised weight-½
Eisenstein series of level `4(N+1)`. -/
def Zhat (w : ℂ) : ℂ :=
  rsFold (N + 1) (Gsh N f) w * invMel τ (w - 1 / 4) / (2 * regF w)

variable {N f}

theorem differentiableAt_Zhat (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 1 / 4 < w.re)
    (hreg : regF w ≠ 0) : DifferentiableAt ℂ (Zhat N f) w := by
  have hI := differentiableAt_rsFold (N + 1) (continuous_Gsh N f)
    (fun B c => Gsh_hdec hτ0 hτ1 B (Quotient.out c)) hw
  have hM : DifferentiableAt ℂ (fun w : ℂ => invMel τ (w - 1 / 4)) w :=
    (differentiableAt_invMel τ (by simp; linarith)).comp w (differentiableAt_id.sub_const _)
  exact (hI.mul hM).div ((differentiable_regF w).const_mul 2) (mul_ne_zero two_ne_zero hreg)

theorem Zhat_eq (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 7 / 4 < w.re) :
    Zhat N f w = ∑' j : ℤ, zCoef f hτ0 hτ1 w j := by
  have hreg := regF_ne_zero_of_one_lt (w := w) (by linarith)
  unfold Zhat
  rw [rsFold_eq (N + 1) (fun γ hγ z => Gsh_smul N f hγ z) (by linarith) (integrableOn_Gsh_strip hτ0 hτ1 hw),
    strip_integral_Gsh hτ0 hτ1 hw]
  have hmel := melK_mul_invMel (τ := τ) (μ := w - 1 / 4)
    (by rw [abs_of_pos hτ0]; simp; linarith)
  set S := ∑' j : ℤ, zCoef f hτ0 hτ1 w j
  set m := melK τ (w - 1 / 4)
  set v := invMel τ (w - 1 / 4)
  rw [show 2 * regF w * (S * m) * v / (2 * regF w) = S * (m * v) * ((2 * regF w) / (2 * regF w)) by ring,
    hmel, div_self (mul_ne_zero two_ne_zero hreg)]
  ring

/-- **The forced zero of the Shimura transform.**  Let `f` be a Maass cusp eigenform on `Γ₀(N+1)` with
exceptional eigenvalue `1/4 - τ²`, `0 < τ < 1/2`.  The Dirichlet series `Z(w) = Σ_{j ≠ 0} ρ_{j²}(8πj²)^{3/4-w}`
of its square-indexed Whittaker coefficients converges absolutely on `Re w > 5/4`; it agrees on
`Re w > 7/4` with `Ẑ`, which is holomorphic at every point of `Re w > 1/4` off the zeros of
`ρ(w) = (4w-3)(4w-2)ζ(4w-1)`, in particular at `w = 1/4 + τ`, and `Ẑ(1/4 + τ) = 0`: the pole of
`Γ(w - 1/4 - τ)` in the archimedean factor cannot be matched by the holomorphic Rankin–Selberg integral. -/
theorem shimura_forced_zero (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) :
    (∀ w : ℂ, 5 / 4 < w.re → Summable (zCoef f hτ0 hτ1 w)) ∧
    (∀ w : ℂ, 7 / 4 < w.re → Zhat N f w = ∑' j : ℤ, zCoef f hτ0 hτ1 w j) ∧
    (∀ w : ℂ, 1 / 4 < w.re → regF w ≠ 0 → DifferentiableAt ℂ (Zhat N f) w) ∧
    DifferentiableAt ℂ (Zhat N f) (1 / 4 + τ) ∧ Zhat N f (1 / 4 + τ) = 0 := by
  refine ⟨fun w hw => summable_zCoef hτ0 hτ1 hw, fun w hw => Zhat_eq hτ0 hτ1 hw,
    fun w hw hreg => differentiableAt_Zhat hτ0 hτ1 hw hreg,
    differentiableAt_Zhat hτ0 hτ1 (by simp; linarith) (regF_quarter_add_ne_zero hτ0 hτ1), ?_⟩
  unfold Zhat
  rw [show (1 / 4 + (τ : ℂ)) - 1 / 4 = τ by ring, invMel_self]
  simp

end ForcedZero
