import GaloisForLFunctions.RHTower.ThetaWindowDirectionalLaw
import GaloisForLFunctions.RHTower.TiltedClusterNyquistExclusion

/-!
# The theta-window law in the steep directions

`ThetaWindowDirectionalLaw` bounds the quotient `h = M_F/ξ` of a rate-`c` function
(`|F(x)| ≤ C e^{k|x|} exp(−c e^{2|x|})`, `0 < c < π`) by `exp(r J_c(φ))`. There `J_c` is the
support function of the theta window `D_c = {v + iθ : π e^{−2|v|} cos 2θ ≥ c}` in the directions
`π cos φ ≥ c`, and it is larger in the steep directions.

This file closes the gap. Put `φ₀ = arccos(c/π)` and `θ* = φ₀/2`. In the steep sectors
`φ₀ ≤ |arg u| ≤ π − φ₀` (centred variable `u = s − ½`), `theta_window_steep_law` gives

`‖h(½ + u)‖ ≤ B (|u|+1)^m e^{θ*|Im u|}`,

and `θ*|sin(arg u)|` is exactly the support function of `D_c` there. So the growth of `h` never
exceeds the window's support function, in any direction. The bound is attained
(`theta_window_tilt_attained`): the tilted kernel `Φ(· + iθ*)` has rate exactly `c`, since
`π cos 2θ* = c`, and quotient `e^{−iθ*(s−½)}` of modulus `e^{θ* Im s}`.

**Proof.**
* On the boundary rays the L47 exponent reduces to `θ* t`, because `log(π cos φ₀/c) = 0` and
  `½ log(1 + tan² φ₀) = log(π/c)` (`windowExponent_on_boundary_ray`).
* Moving the apex from `0` to `½` costs a constant: `σ ↦ ½|t| arctan(|t|/σ) − (σ/4) log(1+t²/σ²)`
  is antitone, with derivative `−¼ log(1+t²/σ²)` (`windowTail_antitone`).
* The rays `π − φ₀` follow from the functional equation.
* Phragmén–Lindelöf in the sector of opening `π − 2φ₀ < π`, with multiplier `e^{iθ*z}`
  (`norm_le_sector_of_rays_exp_im`, through `z = e^w` and the strip principle), carries the ray
  bound inside. Complex conjugation of `F` gives the lower half.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-! ## The window exponent along the real direction -/

/-- The σ-dependent part of the window exponent,
`σ ↦ ½|t| arctan(|t|/σ) − (σ/4) log(1+t²/σ²)`, is antitone on `σ > 0`
(its derivative is `−¼ log(1 + t²/σ²)`). -/
theorem windowTail_antitone (t : ℝ) :
    AntitoneOn (fun σ : ℝ => |t| / 2 * Real.arctan (|t| / σ) - σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2))
      (Set.Ioi 0) := by
  have hderiv : ∀ σ : ℝ, 0 < σ → HasDerivAt
      (fun σ : ℝ => |t| / 2 * Real.arctan (|t| / σ) - σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2))
      (-(1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2)) σ := by
    intro σ hσ
    have hσ0 : σ ≠ 0 := hσ.ne'
    have hq : 0 < 1 + t ^ 2 / σ ^ 2 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => |t| / x) (-(|t| / σ ^ 2)) σ := by
      have h := (hasDerivAt_inv hσ0).const_mul |t|
      have e : (fun x : ℝ => |t| * x⁻¹) = fun x => |t| / x := by funext x; rw [div_eq_mul_inv]
      rw [e] at h
      exact h.congr_deriv (by ring)
    have h2 := (Real.hasDerivAt_arctan (|t| / σ)).comp σ h1
    have h3 : HasDerivAt (fun x : ℝ => 1 + t ^ 2 / x ^ 2) (-(2 * t ^ 2 / σ ^ 3)) σ := by
      have h := (hasDerivAt_const σ (t ^ 2)).div (hasDerivAt_pow 2 σ) (pow_ne_zero 2 hσ0)
      exact ((hasDerivAt_const σ (1 : ℝ)).add h).congr_deriv (by field_simp; ring)
    have h4 := (Real.hasDerivAt_log hq.ne').comp σ h3
    have h5 := ((hasDerivAt_id σ).div_const 4).mul h4
    have h6 := (h2.const_mul (|t| / 2)).sub h5
    refine h6.congr_deriv ?_
    have hat : |t| ^ 2 = t ^ 2 := sq_abs t
    simp only [Function.comp, id]
    field_simp
    rw [hat]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro σ hσ; exact (hderiv σ hσ).continuousAt.continuousWithinAt
  · intro σ hσ
    rw [interior_Ioi] at hσ
    exact (hderiv σ hσ).differentiableAt.differentiableWithinAt
  · intro σ hσ
    rw [interior_Ioi] at hσ
    rw [(hderiv σ hσ).deriv]
    have : 0 ≤ Real.log (1 + t ^ 2 / σ ^ 2) := Real.log_nonneg (by
      have := div_nonneg (sq_nonneg t) (sq_nonneg σ); linarith)
    linarith

/-- Shifting `σ` to the right costs at most `(σ'−σ)/2 · log(π/c)` in the window exponent. -/
theorem windowExponent_shift_le {c σ σ' t : ℝ} (hσ : 0 < σ) (hσσ : σ ≤ σ') :
    σ' / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ') -
        σ' / 4 * Real.log (1 + t ^ 2 / σ' ^ 2) ≤
      σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
        σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2) + (σ' - σ) / 2 * Real.log (π / c) := by
  have h := windowTail_antitone t (a := σ) (b := σ') hσ (lt_of_lt_of_le hσ hσσ) hσσ
  simp only at h
  linarith

/-- **The window exponent on the boundary ray.** With `cos φ₀ = c/π`, at `σ = r cos φ₀`,
`t = r sin φ₀` the exponent equals `(φ₀/2) t`. -/
theorem windowExponent_on_boundary_ray {c r : ℝ} (hc : 0 < c) (hcπ : c < π) (hr : 0 < r) :
    let φ₀ := Real.arccos (c / π)
    r * Real.cos φ₀ / 2 * Real.log (π / c) +
        |r * Real.sin φ₀| / 2 * Real.arctan (|r * Real.sin φ₀| / (r * Real.cos φ₀)) -
        r * Real.cos φ₀ / 4 * Real.log (1 + (r * Real.sin φ₀) ^ 2 / (r * Real.cos φ₀) ^ 2) =
      φ₀ / 2 * (r * Real.sin φ₀) := by
  intro φ₀
  have hq : c / π ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by
    have := div_pos hc Real.pi_pos; linarith, by rw [div_lt_one Real.pi_pos]; exact hcπ⟩
  have hcos : Real.cos φ₀ = c / π := Real.cos_arccos (by linarith [hq.1]) hq.2.le
  have hφ0 : 0 < φ₀ := Real.arccos_pos.mpr hq.2
  have hφ1 : φ₀ < π / 2 := by
    show Real.arccos (c / π) < π / 2
    rw [Real.arccos_lt_pi_div_two]; exact div_pos hc Real.pi_pos
  have hsin : 0 < Real.sin φ₀ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hcospos : 0 < Real.cos φ₀ := by rw [hcos]; positivity
  have habs : |r * Real.sin φ₀| = r * Real.sin φ₀ := abs_of_pos (by positivity)
  rw [habs]
  have htan : r * Real.sin φ₀ / (r * Real.cos φ₀) = Real.tan φ₀ := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  rw [htan, Real.arctan_tan (by linarith) hφ1]
  have h1 : 1 + (r * Real.sin φ₀) ^ 2 / (r * Real.cos φ₀) ^ 2 = (π / c) ^ 2 := by
    have hsc := Real.sin_sq_add_cos_sq φ₀
    have e : 1 + (r * Real.sin φ₀) ^ 2 / (r * Real.cos φ₀) ^ 2 = 1 / Real.cos φ₀ ^ 2 := by
      field_simp; nlinarith
    rw [e, hcos]; field_simp
  rw [h1, Real.log_pow]
  push_cast
  ring

/-- **Sector Phragmén–Lindelöf with a linear-in-`Im` weight.** If `h` is entire of exponential type
and `‖h z‖ ≤ B |z + i|^m e^{β Im z}` on the rays `arg z = δ, π − δ` (`z = e^w`), the same bound holds
on the sector `δ ≤ arg z ≤ π − δ`. -/
theorem norm_le_sector_of_rays_exp_im {h : ℂ → ℂ} (hh : Differentiable ℂ h) {A τ B δ β : ℝ}
    {m : ℕ} (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδ2 : δ < π / 2) (hβ0 : 0 ≤ β)
    (hgrow : ∀ z : ℂ, ‖h z‖ ≤ A * Real.exp (τ * ‖z‖))
    (hray : ∀ w : ℂ, (w.im = δ ∨ w.im = π - δ) →
      ‖h (cexp w)‖ ≤ B * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im))
    {w : ℂ} (hw1 : δ ≤ w.im) (hw2 : w.im ≤ π - δ) :
    ‖h (cexp w)‖ ≤ B * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set G : ℂ → ℂ := fun w => h (cexp w) * cexp (I * β * cexp w) / (cexp w + I) ^ m with hG
  -- `e^w + i` is nonzero with norm `≥ 1` on the closed strip
  have hnz : ∀ w : ℂ, δ ≤ w.im → w.im ≤ π - δ → 1 ≤ ‖cexp w + I‖ := by
    intro w h1 h2
    have him := im_exp_ge hδ.le h1 h2
    have hpos : 0 ≤ Real.exp w.re * Real.sin δ := by positivity
    have := Complex.abs_im_le_norm (cexp w + I)
    rw [Complex.add_im, Complex.I_im, abs_of_nonneg (by linarith)] at this
    linarith
  have hexpI : ∀ w : ℂ, ‖cexp (I * β * cexp w)‖ = Real.exp (-(β * (cexp w).im)) := by
    intro w
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  -- the key identity `‖G w‖ ‖e^w + i‖^m e^{β Im e^w} = ‖h(e^w)‖`
  have hGnorm : ∀ w : ℂ, δ ≤ w.im → w.im ≤ π - δ →
      ‖h (cexp w)‖ = ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
    intro w h1 h2
    have hn := hnz w h1 h2
    have hpow : 0 < ‖cexp w + I‖ ^ m := pow_pos (by linarith) m
    simp only [hG]
    rw [norm_div, norm_mul, norm_pow, hexpI]
    rw [div_mul_cancel₀ _ hpow.ne', mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      mul_one]
  -- differentiability on the closed strip
  have hdiff : DifferentiableOn ℂ G (closure (Complex.im ⁻¹' Set.Ioo δ (π - δ))) := by
    rw [Complex.closure_preimage_im, closure_Ioo (by linarith)]
    intro w hw
    have hn := hnz w hw.1 hw.2
    have hne : (cexp w + I) ^ m ≠ 0 := pow_ne_zero _ (by
      intro h0; rw [h0, norm_zero] at hn; linarith)
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => h (cexp w) * cexp (I * β * cexp w)) w :=
      ((hh _).comp w (Complex.differentiableAt_exp)).mul
        ((differentiableAt_const _).mul Complex.differentiableAt_exp).cexp
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (cexp w + I) ^ m) w :=
      (Complex.differentiableAt_exp.add (differentiableAt_const _)).pow m
    exact h1.div h2 hne
  have hc : (1 : ℝ) < π / (π - δ - δ) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hGgrow : ∀ w : ℂ, w ∈ Complex.im ⁻¹' Set.Ioo δ (π - δ) →
      ‖G w‖ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) := by
    intro w hw
    have h1 : δ ≤ w.im := hw.1.le
    have h2 : w.im ≤ π - δ := hw.2.le
    have hn := hnz w h1 h2
    have him := im_exp_ge hδ.le h1 h2
    have hpos : 0 ≤ β * (cexp w).im := mul_nonneg hβ0 (le_trans (by positivity) him)
    simp only [hG]
    rw [norm_div, norm_mul, norm_pow, hexpI]
    have hpow : 1 ≤ ‖cexp w + I‖ ^ m := one_le_pow₀ hn
    have hE : Real.exp (-(β * (cexp w).im)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh1 := hgrow (cexp w)
    rw [Complex.norm_exp] at hh1
    have hre : Real.exp w.re ≤ Real.exp (1 * |w.re|) :=
      Real.exp_le_exp.mpr (by rw [one_mul]; exact le_abs_self _)
    have hhb : ‖h (cexp w)‖ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) :=
      hh1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hre hτ)) hA)
    rw [div_le_iff₀ (by linarith)]
    calc ‖h (cexp w)‖ * Real.exp (-(β * (cexp w).im))
        ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) * 1 :=
          mul_le_mul hhb hE (Real.exp_pos _).le (by positivity)
      _ ≤ A * Real.exp (τ * Real.exp (1 * |w.re|)) * ‖cexp w + I‖ ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound : ∀ w : ℂ, (w.im = δ ∨ w.im = π - δ) → ‖G w‖ ≤ B := by
    intro w hwi
    have h1 : δ ≤ w.im := by rcases hwi with h | h <;> linarith
    have h2 : w.im ≤ π - δ := by rcases hwi with h | h <;> linarith
    have hn := hnz w h1 h2
    have hpow : 0 < ‖cexp w + I‖ ^ m := pow_pos (by linarith) m
    have hr := hray w hwi
    have hid := hGnorm w h1 h2
    have hEpos : 0 < Real.exp (β * (cexp w).im) := Real.exp_pos _
    by_contra hcon
    push Not at hcon
    have : B * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) <
        ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
      apply mul_lt_mul_of_pos_right _ hEpos
      exact mul_lt_mul_of_pos_right hcon hpow
    linarith
  have hPL := PhragmenLindelof.horizontal_strip (f := G) (a := δ) (b := π - δ) (C := B)
    hdiff.diffContOnCl
    ⟨1, hc, τ, Asymptotics.IsBigO.of_bound A (by
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with w hw
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hGgrow w hw)⟩
    (fun z hz => hbound z (Or.inl hz)) (fun z hz => hbound z (Or.inr hz)) hw1 hw2
  rw [hGnorm w hw1 hw2]
  have hpow : 0 ≤ ‖cexp w + I‖ ^ m := by positivity
  calc ‖G w‖ * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im)
      ≤ B * ‖cexp w + I‖ ^ m * Real.exp (β * (cexp w).im) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hPL hpow

/-! ## The steep boundary rays -/

/-- The monotone assembly of the steep-ray bound. -/
theorem steep_chain_le {Cl A B P S E Q1 Q2 R T G : ℝ} (hCl : 0 ≤ Cl) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : P ≤ Q1 * Q2) (hS0 : 0 ≤ S) (hS : S ≤ R) (hE0 : 0 ≤ E) (hE : E ≤ T * G)
    (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hR : 0 ≤ R) :
    Cl * (A * B * P) * S * E ≤ Cl * A * B * Q1 * R * G * Q2 * T := by
  have hCAB : 0 ≤ Cl * (A * B) := mul_nonneg hCl (mul_nonneg hA hB)
  calc Cl * (A * B * P) * S * E = Cl * (A * B) * P * S * E := by ring
    _ ≤ Cl * (A * B) * (Q1 * Q2) * S * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP hCAB) hS0) hE0
    _ ≤ Cl * (A * B) * (Q1 * Q2) * R * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS
          (mul_nonneg hCAB (mul_nonneg hQ1 hQ2))) hE0
    _ ≤ Cl * (A * B) * (Q1 * Q2) * R * (T * G) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg (mul_nonneg hCAB (mul_nonneg hQ1 hQ2)) hR)
    _ = Cl * A * B * Q1 * R * G * Q2 * T := by ring

/-- Common constant: the L47 law at `(σ, t)` with `σ = ½ + r cos φ₀ ≥ 2`, `|t| = r sin φ₀`,
`|u + i| ≥ max(r, 1)`, is at most `B₁ |u+i|^m e^{θ* r sin φ₀}`. -/
theorem steep_law_bound {c k Cl r σ t N : ℝ} {m : ℕ} (hc : 0 < c) (hcπ : c < π) (hk : 0 ≤ k)
    (hCl : 0 ≤ Cl) (hr : 0 < r) (hσeq : σ = 1 / 2 + r * Real.cos (Real.arccos (c / π)))
    (hσ : 2 ≤ σ) (ht : |t| = r * Real.sin (Real.arccos (c / π))) (hNr : r ≤ N) (hN1 : 1 ≤ N)
    (hm : (k + 1 / 2 + 1) / 2 ≤ m) :
    Cl * Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
        (k + 1 / 2) / 2 * Real.log (π / c)) * Real.sqrt (1 + t ^ 2 / σ ^ 2) *
      Real.exp (σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
        σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2)) ≤
      Cl * Real.exp c * Real.exp ((k + 1 / 2) / 2 * Real.log (π / c)) *
          (3 / 2 + (k + 1 / 2)) ^ m * (π / c) * Real.exp (Real.log (π / c) / 4) * N ^ m *
        Real.exp (Real.arccos (c / π) / 2 * (r * Real.sin (Real.arccos (c / π)))) := by
  have hq : c / π ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by
    have := div_pos hc Real.pi_pos; linarith, by rw [div_lt_one Real.pi_pos]; exact hcπ⟩
  have hcos : Real.cos (Real.arccos (c / π)) = c / π :=
    Real.cos_arccos (by linarith [hq.1]) hq.2.le
  have hqpos : 0 < c / π := div_pos hc Real.pi_pos
  have hsin0 : 0 ≤ Real.sin (Real.arccos (c / π)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hsc : Real.sin (Real.arccos (c / π)) ^ 2 = 1 - (c / π) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (Real.arccos (c / π)); rw [hcos] at this; linarith
  have hσ0 : 0 < σ := by linarith
  have hσ₀pos : 0 < r * Real.cos (Real.arccos (c / π)) := by rw [hcos]; positivity
  have hσσ₀ : r * Real.cos (Real.arccos (c / π)) ≤ σ := by rw [hσeq]; linarith
  have hL0 : 0 ≤ Real.log (π / c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  -- the exponent
  have hshift := windowExponent_shift_le (c := c) (t := t) hσ₀pos hσσ₀
  have hray := windowExponent_on_boundary_ray hc hcπ hr
  simp only at hray
  have habs_ray : |r * Real.sin (Real.arccos (c / π))| = |t| := by
    rw [ht, abs_of_nonneg (by positivity)]
  have hsq_ray : (r * Real.sin (Real.arccos (c / π))) ^ 2 = t ^ 2 := by
    rw [← sq_abs t, ht]
  rw [habs_ray, hsq_ray] at hray
  have hexp : σ / 2 * Real.log (π / c) + |t| / 2 * Real.arctan (|t| / σ) -
      σ / 4 * Real.log (1 + t ^ 2 / σ ^ 2) ≤
      Real.arccos (c / π) / 2 * (r * Real.sin (Real.arccos (c / π))) + Real.log (π / c) / 4 := by
    have h1 : (σ - r * Real.cos (Real.arccos (c / π))) / 2 * Real.log (π / c) =
        Real.log (π / c) / 4 := by rw [hσeq]; ring
    linarith
  -- the square root
  have hsq : Real.sqrt (1 + t ^ 2 / σ ^ 2) ≤ π / c := by
    rw [Real.sqrt_le_left (by positivity)]
    have ht2 : t ^ 2 ≤ r ^ 2 * (1 - (c / π) ^ 2) := by
      rw [← hsc, ← sq_abs t, ht]; ring_nf; rfl
    have hσ2 : r ^ 2 * (c / π) ^ 2 ≤ σ ^ 2 := by
      have h0 : 0 ≤ r * (c / π) := by positivity
      have : r * (c / π) ≤ σ := by rw [← hcos]; exact hσσ₀
      nlinarith
    have hkey : t ^ 2 ≤ σ ^ 2 * ((π / c) ^ 2 - 1) := by
      have e : r ^ 2 * (1 - (c / π) ^ 2) = r ^ 2 * (c / π) ^ 2 * ((π / c) ^ 2 - 1) := by
        field_simp
      have hnn : 0 ≤ (π / c) ^ 2 - 1 := by
        have : 1 ≤ π / c := by rw [le_div_iff₀ hc]; linarith
        nlinarith
      nlinarith
    have : t ^ 2 / σ ^ 2 ≤ (π / c) ^ 2 - 1 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  -- the polynomial factor
  have hpoly : Real.exp ((k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2))) ≤
      (3 / 2 + (k + 1 / 2)) ^ m * N ^ m := by
    have hb : 1 ≤ σ + (k + 1 / 2) := by linarith
    have hσK : σ + (k + 1 / 2) ≤ (3 / 2 + (k + 1 / 2)) * N := by
      have h1 : r * Real.cos (Real.arccos (c / π)) ≤ r :=
        mul_le_of_le_one_right hr.le (Real.cos_le_one _)
      have h2 : (k + 1 / 2) * 1 ≤ (k + 1 / 2) * N :=
        mul_le_mul_of_nonneg_left hN1 (by linarith)
      have h3 : (3 / 2 + (k + 1 / 2)) * N = 3 / 2 * N + (k + 1 / 2) * N := by ring
      rw [hσeq, h3]
      linarith
    rw [mul_comm, ← Real.rpow_def_of_pos (by linarith)]
    calc (σ + (k + 1 / 2)) ^ ((k + 1 / 2 + 1) / 2) ≤ (σ + (k + 1 / 2)) ^ (m : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb hm
      _ = (σ + (k + 1 / 2)) ^ m := Real.rpow_natCast _ _
      _ ≤ ((3 / 2 + (k + 1 / 2)) * N) ^ m := pow_le_pow_left₀ (by linarith) hσK m
      _ = (3 / 2 + (k + 1 / 2)) ^ m * N ^ m := mul_pow _ _ _
  have hsplit : Real.exp (c + (k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2)) +
        (k + 1 / 2) / 2 * Real.log (π / c)) =
      Real.exp c * Real.exp ((k + 1 / 2) / 2 * Real.log (π / c)) *
        Real.exp ((k + 1 / 2 + 1) / 2 * Real.log (σ + (k + 1 / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hsplit]
  have hE := Real.exp_le_exp.mpr hexp
  rw [Real.exp_add] at hE
  exact steep_chain_le hCl (Real.exp_pos _).le (Real.exp_pos _).le hpoly (Real.sqrt_nonneg _) hsq
    (Real.exp_pos _).le hE (by positivity) (by positivity) (by positivity)

/-- Rate-`c` decay with prefactor gives rate-`c/2` decay without prefactor. -/
theorem decay_half_of_rate {F : ℝ → ℂ} {C k c : ℝ} (hk : 0 ≤ k) (hc : 0 < c)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|))) :
    ∀ x, ‖F x‖ ≤ C * Real.exp (legendreMajorant (c / 2) k) *
      Real.exp (-(c / 2 * Real.exp (2 * |x|))) := by
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - c * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  intro x
  have hleg := le_legendreMajorant (c := c / 2) (by positivity) hk |x|
  refine (hF x).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  linarith

/-- **Steep sector, upper half.** On the rays of `arg u ∈ [φ₀, π − φ₀]`, `φ₀ = arccos(c/π)`,
the quotient satisfies `‖h(½ + u)‖ ≤ B |u + i|^m e^{θ* Im u}`, `θ* = φ₀/2`. -/
theorem steep_sector_upper {F : ℝ → ℂ} {C k c : ℝ} (hk : 0 ≤ k) (hc : 0 < c) (hcπ : c < π)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|)))
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    ∃ B : ℝ, ∀ w : ℂ, Real.arccos (c / π) ≤ w.im → w.im ≤ π - Real.arccos (c / π) →
      ‖h (1 / 2 + cexp w)‖ ≤ B * ‖cexp w + I‖ ^ (⌈(k + 1 / 2 + 1) / 2⌉₊) *
        Real.exp (Real.arccos (c / π) / 2 * (cexp w).im) := by
  set φ₀ := Real.arccos (c / π) with hφ₀
  set m := ⌈(k + 1 / 2 + 1) / 2⌉₊ with hm
  have hmle : (k + 1 / 2 + 1) / 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hC : 0 ≤ C := by
    have h1 := hF 0
    have h2 := norm_nonneg (F 0)
    have h3 := Real.exp_pos (k * |(0 : ℝ)| - c * Real.exp (2 * |(0 : ℝ)|))
    by_contra hneg; push Not at hneg; nlinarith
  have hq : c / π ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by
    have := div_pos hc Real.pi_pos; linarith, by rw [div_lt_one Real.pi_pos]; exact hcπ⟩
  have hcos : Real.cos φ₀ = c / π := Real.cos_arccos (by linarith [hq.1]) hq.2.le
  have hφ0 : 0 < φ₀ := Real.arccos_pos.mpr hq.2
  have hφ1 : φ₀ < π / 2 := by
    rw [hφ₀, Real.arccos_lt_pi_div_two]; exact div_pos hc Real.pi_pos
  have hsinφ : 0 < Real.sin φ₀ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  -- exponential type of `h`
  obtain ⟨A, τ, hA, hτ, hgrow⟩ := exists_quotient_exponential_type (c := c / 2) (δ := c / 4)
    (by positivity) (by linarith) (decay_half_of_rate hk hc hF) hh hdiv
  -- the directional laws for `h` and for the reflected quotient
  set J := ∫ x : ℝ, Real.exp (-|x|) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set Cl := 3 * (C * J) with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  have hR := fun σ t (hσ : 2 ≤ σ) =>
    theta_window_directional_law hk hc hF (fun s _ => hdiv s) (σ := σ) (t := t) hσ
  have hFrefl : ∀ x, ‖(fun y => F (-y)) x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|)) := by
    intro x; simpa [abs_neg] using hF (-x)
  have hR' := fun σ t (hσ : 2 ≤ σ) =>
    theta_window_directional_law (h := fun w => h (1 - w)) hk hc hFrefl
      (fun w _ => centredLaplace_reflect_eq hdiv w) (σ := σ) (t := t) hσ
  set B₁ := Cl * Real.exp c * Real.exp ((k + 1 / 2) / 2 * Real.log (π / c)) *
    (3 / 2 + (k + 1 / 2)) ^ m * (π / c) * Real.exp (Real.log (π / c) / 4) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  set B₂ := A * Real.exp (τ / 2) * Real.exp (τ * (3 * π / (2 * c))) with hB₂
  have hB₂0 : 0 ≤ B₂ := by positivity
  refine ⟨B₁ + B₂, fun w hw1 hw2 => ?_⟩
  exact norm_le_sector_of_rays_exp_im (h := fun u => h (1 / 2 + u)) (A := A * Real.exp (τ / 2))
    (τ := τ) (B := B₁ + B₂) (δ := φ₀) (β := φ₀ / 2) (m := m) (w := w)
    ((hh.comp ((differentiable_const _).add differentiable_id)))
    (by positivity) hτ hφ0 hφ1 (by positivity)
    (fun z => by
      have := hgrow (1 / 2 + z)
      have hn : ‖(1 / 2 : ℂ) + z‖ ≤ 1 / 2 + ‖z‖ := by
        have := norm_add_le (1 / 2 : ℂ) z; rwa [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at this
      calc ‖h (1 / 2 + z)‖ ≤ A * Real.exp (τ * ‖(1 / 2 : ℂ) + z‖) := this
        _ ≤ A * Real.exp (τ * (1 / 2 + ‖z‖)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hτ)) hA
        _ = A * Real.exp (τ / 2) * Real.exp (τ * ‖z‖) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf)
    (fun w hw => by
      set u := cexp w with hu
      set r := ‖u‖ with hr
      have hr0 : 0 < r := by rw [hr, hu, Complex.norm_exp]; exact Real.exp_pos _
      have hre : u.re = r * Real.cos w.im := by rw [hu, Complex.exp_re, hr, hu, Complex.norm_exp]
      have him : u.im = r * Real.sin w.im := by rw [hu, Complex.exp_im, hr, hu, Complex.norm_exp]
      have hsinw : Real.sin w.im = Real.sin φ₀ := by
        rcases hw with h | h
        · rw [h]
        · rw [h, Real.sin_pi_sub]
      rw [hsinw] at him
      have himnn : 0 ≤ u.im := by rw [him]; positivity
      obtain ⟨hNr, hN1⟩ := norm_le_norm_add_I himnn
      have hNm : 1 ≤ ‖u + I‖ ^ m := one_le_pow₀ hN1
      have hE1 : 1 ≤ Real.exp (φ₀ / 2 * u.im) := Real.one_le_exp (by positivity)
      -- small `r`: the global bound
      have hsmall : r * Real.cos φ₀ < 3 / 2 →
          ‖h (1 / 2 + u)‖ ≤ (B₁ + B₂) * ‖u + I‖ ^ m * Real.exp (φ₀ / 2 * u.im) := by
        intro hrc
        have hr3 : r ≤ 3 * π / (2 * c) := by
          rw [hcos] at hrc
          rw [le_div_iff₀ (by positivity)]
          have : r * c < 3 / 2 * π := by
            have := (mul_lt_mul_of_pos_right hrc Real.pi_pos)
            field_simp at this; linarith
          linarith
        have hg := hgrow (1 / 2 + u)
        have hn : ‖(1 / 2 : ℂ) + u‖ ≤ 1 / 2 + r := by
          have := norm_add_le (1 / 2 : ℂ) u
          rwa [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at this
        have h1 : ‖h (1 / 2 + u)‖ ≤ B₂ := by
          refine hg.trans ?_
          rw [hB₂, mul_assoc, ← Real.exp_add]
          apply mul_le_mul_of_nonneg_left _ hA
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left (hn.trans (by linarith : 1 / 2 + r ≤ 1 / 2 + 3 * π / (2 * c))) hτ
          linarith
        calc ‖h (1 / 2 + u)‖ ≤ B₂ := h1
          _ ≤ (B₁ + B₂) * 1 * 1 := by linarith
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hNm (by positivity)) hE1 zero_le_one
              (by positivity)
      rcases hw with hwφ | hwφ
      · -- right ray
        have hre' : u.re = r * Real.cos φ₀ := by rw [hre, hwφ]
        by_cases h2 : 2 ≤ 1 / 2 + r * Real.cos φ₀
        · obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 / 2 + r * Real.cos φ₀ := ⟨_, rfl⟩
          have heq : (1 / 2 : ℂ) + u = (σ : ℂ) + ((u.im : ℝ) : ℂ) * I := by
            apply Complex.ext
            · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
              norm_num; linarith
            · simp
          rw [← hσdef] at h2
          have hb := hR σ u.im h2
          have hl := steep_law_bound (m := m) (N := ‖u + I‖) (t := u.im) hc hcπ hk hCl0 hr0 hσdef h2
            (by rw [him, abs_of_nonneg (by positivity)]) hNr hN1 hmle
          show ‖h (1 / 2 + u)‖ ≤ _
          rw [heq]
          refine hb.trans (hl.trans ?_)
          rw [← him]
          have : B₁ * ‖u + I‖ ^ m * Real.exp (φ₀ / 2 * u.im) ≤
              (B₁ + B₂) * ‖u + I‖ ^ m * Real.exp (φ₀ / 2 * u.im) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          convert this using 2
        · push Not at h2; exact hsmall (by linarith)
      · -- left ray, through `w ↦ h(1 − w)`
        have hcosw : Real.cos w.im = -Real.cos φ₀ := by rw [hwφ, Real.cos_pi_sub]
        have hre' : u.re = -(r * Real.cos φ₀) := by rw [hre, hcosw]; ring
        by_cases h2 : 2 ≤ 1 / 2 + r * Real.cos φ₀
        · obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 / 2 + r * Real.cos φ₀ := ⟨_, rfl⟩
          have heq : (1 / 2 : ℂ) + u = 1 - ((σ : ℂ) + ((-u.im : ℝ) : ℂ) * I) := by
            apply Complex.ext
            · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
                Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
                sub_zero]
              norm_num; linarith
            · simp
          rw [← hσdef] at h2
          have hb := hR' σ (-u.im) h2
          have hl := steep_law_bound (m := m) (N := ‖u + I‖) (t := -u.im) hc hcπ hk hCl0 hr0 hσdef h2
            (by rw [abs_neg, him, abs_of_nonneg (by positivity)]) hNr hN1 hmle
          show ‖h (1 / 2 + u)‖ ≤ _
          rw [heq]
          refine hb.trans (hl.trans ?_)
          rw [← him]
          have : B₁ * ‖u + I‖ ^ m * Real.exp (φ₀ / 2 * u.im) ≤
              (B₁ + B₂) * ‖u + I‖ ^ m * Real.exp (φ₀ / 2 * u.im) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          convert this using 2
        · push Not at h2; exact hsmall (by linarith)) hw1 hw2


/-! ## The sharp law in the steep directions and its attainment -/

/-- **Theta window, steep directions.** Let `|F(x)| ≤ C e^{k|x|} exp(−c e^{2|x|})` with `0 < c < π`
and `M_F = ξ · h`. With `φ₀ = arccos(c/π)`, in the steep sectors `φ₀ ≤ |arg u| ≤ π − φ₀`,
`‖h(½ + u)‖ ≤ B (|u|+1)^m e^{(φ₀/2)|Im u|}`. There `(φ₀/2)|sin(arg u)|` is exactly the support function
of the theta window `D_c`, so together with `theta_window_directional_law` the growth of `h` never
exceeds the window's support function. -/
theorem theta_window_steep_law {F : ℝ → ℂ} {C k c : ℝ} (hk : 0 ≤ k) (hc : 0 < c) (hcπ : c < π)
    (hF : ∀ x, ‖F x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|)))
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hdiv : ∀ s, centredLaplace F s = xi s * h s) :
    ∃ B : ℝ, ∀ u : ℂ, u ≠ 0 → Real.arccos (c / π) ≤ |u.arg| → |u.arg| ≤ π - Real.arccos (c / π) →
      ‖h (1 / 2 + u)‖ ≤ B * (‖u‖ + 1) ^ (⌈(k + 1 / 2 + 1) / 2⌉₊) *
        Real.exp (Real.arccos (c / π) / 2 * |u.im|) := by
  set m := ⌈(k + 1 / 2 + 1) / 2⌉₊ with hm
  obtain ⟨B, hB⟩ := steep_sector_upper hk hc hcπ hF hh hdiv
  -- the conjugate problem
  set F' : ℝ → ℂ := fun x => (starRingEnd ℂ) (F x) with hF'
  set h' : ℂ → ℂ := fun s => (starRingEnd ℂ) (h ((starRingEnd ℂ) s)) with hh'
  have hF'd : ∀ x, ‖F' x‖ ≤ C * Real.exp (k * |x| - c * Real.exp (2 * |x|)) := by
    intro x; rw [hF', Complex.norm_conj]; exact hF x
  have hh'd : Differentiable ℂ h' := by
    intro s
    have := (hh ((starRingEnd ℂ) s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hdiv' : ∀ s, centredLaplace F' s = xi s * h' s := by
    intro s
    rw [hF', centredLaplace_conj, hdiv, map_mul, xi_conj, Complex.conj_conj]
  obtain ⟨B', hB'⟩ := steep_sector_upper hk hc hcπ hF'd hh'd hdiv'
  have hφ0 : 0 < Real.arccos (c / π) := Real.arccos_pos.mpr (by rw [div_lt_one Real.pi_pos]; exact hcπ)
  refine ⟨max (max B B') 0, fun u hu h1 h2 => ?_⟩
  have hmax : 0 ≤ max (max B B') 0 := le_max_right _ _
  have hBle : B ≤ max (max B B') 0 := (le_max_left B B').trans (le_max_left _ _)
  have hB'le : B' ≤ max (max B B') 0 := (le_max_right B B').trans (le_max_left _ _)
  have hEpos : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  rcases le_or_gt 0 u.arg with harg | harg
  · -- upper half: `w = log u`
    have hua : |u.arg| = u.arg := abs_of_nonneg harg
    rw [hua] at h1 h2
    have hb := hB (Complex.log u) (by rw [Complex.log_im]; exact h1) (by rw [Complex.log_im]; exact h2)
    rw [Complex.exp_log hu] at hb
    have him : 0 ≤ u.im := Complex.arg_nonneg_iff.mp harg
    rw [abs_of_nonneg him]
    have hn : ‖u + I‖ ≤ ‖u‖ + 1 := by
      have := norm_add_le u I; rwa [Complex.norm_I] at this
    calc ‖h (1 / 2 + u)‖ ≤ B * ‖u + I‖ ^ m * Real.exp (Real.arccos (c / π) / 2 * u.im) := hb
      _ ≤ max (max B B') 0 * (‖u‖ + 1) ^ m * Real.exp (Real.arccos (c / π) / 2 * u.im) := by
          apply mul_le_mul_of_nonneg_right _ (hEpos _)
          exact mul_le_mul hBle (pow_le_pow_left₀ (norm_nonneg _) hn m) (by positivity) hmax
  · -- lower half: conjugate
    have him : u.im < 0 := Complex.arg_neg_iff.mp harg
    have hua : |u.arg| = -u.arg := abs_of_neg harg
    rw [hua] at h1 h2
    have hπ : u.arg ≠ π := by linarith [Real.pi_pos]
    have hcarg : ((starRingEnd ℂ) u).arg = -u.arg := by rw [Complex.arg_conj, if_neg hπ]
    have hcu : (starRingEnd ℂ) u ≠ 0 := by
      intro h0; apply hu; simpa using congrArg (starRingEnd ℂ) h0
    have hb := hB' (Complex.log ((starRingEnd ℂ) u)) (by rw [Complex.log_im, hcarg]; exact h1)
      (by rw [Complex.log_im, hcarg]; exact h2)
    rw [Complex.exp_log hcu] at hb
    have e : h' (1 / 2 + (starRingEnd ℂ) u) = (starRingEnd ℂ) (h (1 / 2 + u)) := by
      rw [hh']; simp only [map_add, Complex.conj_conj, map_div₀, map_one, map_ofNat]
    rw [e, Complex.norm_conj] at hb
    have hci : ((starRingEnd ℂ) u).im = |u.im| := by rw [Complex.conj_im, abs_of_neg him]
    rw [hci] at hb
    have hn : ‖(starRingEnd ℂ) u + I‖ ≤ ‖u‖ + 1 := by
      have := norm_add_le ((starRingEnd ℂ) u) I; rwa [Complex.norm_I, Complex.norm_conj] at this
    calc ‖h (1 / 2 + u)‖ ≤ B' * ‖(starRingEnd ℂ) u + I‖ ^ m *
          Real.exp (Real.arccos (c / π) / 2 * |u.im|) := hb
      _ ≤ max (max B B') 0 * (‖u‖ + 1) ^ m * Real.exp (Real.arccos (c / π) / 2 * |u.im|) := by
          apply mul_le_mul_of_nonneg_right _ (hEpos _)
          exact mul_le_mul hB'le (pow_le_pow_left₀ (norm_nonneg _) hn m) (by positivity) hmax

/-- **Attainment in the steep directions.** The tilted kernel `Φ(· + iθ*)`, `θ* = ½ arccos(c/π)`, has
transform `e^{−iθ*(s−½)} ξ(s)`, whose quotient has modulus `e^{θ* Im s}`. -/
theorem centredLaplace_tiltedPhi {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (s : ℂ) :
    centredLaplace (tiltedPhi θ) s = xi s * cexp (-(I * θ * (s - 1 / 2))) := by
  have h := paperFT_tiltedPhi_eq hθ0 hθ (-(I * (s - 1 / 2)))
  unfold Zeta23.paperFT at h
  rw [riemannXiHat_eq_xi] at h
  have e1 : (1 / 2 : ℂ) + I * -(I * (s - 1 / 2)) = s := by ring_nf; rw [Complex.I_sq]; ring
  rw [e1] at h
  unfold centredLaplace
  have e2 : (fun u : ℝ => tiltedPhi θ u * cexp (I * -(I * (s - 1 / 2)) * u)) =
      fun u : ℝ => cexp ((s - 1 / 2) * u) * tiltedPhi θ u := by
    funext u; rw [mul_comm]; congr 2; ring_nf; rw [Complex.I_sq]; ring
  rw [e2] at h
  rw [h, mul_comm]
  congr 1; ring_nf


/-- The tilted kernel decays at the rate `π cos 2θ` with prefactor `e^{9|x|/2}`, globally. -/
theorem tiltedPhi_rate {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    ∃ C : ℝ, ∀ x : ℝ, ‖tiltedPhi θ x‖ ≤
      C * Real.exp (9 / 2 * |x| - π * Real.cos (2 * θ) * Real.exp (2 * |x|)) := by
  have hcos : 0 < Real.cos (2 * θ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hπc : 0 < π * Real.cos (2 * θ) := mul_pos Real.pi_pos hcos
  set R := |Real.log (π * Real.cos (2 * θ))| / 2 + 1 with hR
  have hcont : Continuous (tiltedPhi θ) :=
    continuous_tiltedPhi (by rw [abs_of_nonneg hθ0]; linarith)
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM := tiltedPhiTailConst_nonneg
  refine ⟨tiltedPhiTailConst + |C₀| * Real.exp 1, fun x => ?_⟩
  have hE : 0 < Real.exp (9 / 2 * |x| - π * Real.cos (2 * θ) * Real.exp (2 * |x|)) := Real.exp_pos _
  by_cases hX : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * |x|)
  · have := norm_tiltedPhi_le_of_rate hθ0 hθ hX
    calc ‖tiltedPhi θ x‖ ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |x|) *
          Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * |x|))) := this
      _ = tiltedPhiTailConst * Real.exp (9 / 2 * |x| - π * Real.cos (2 * θ) * Real.exp (2 * |x|)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hE.le
          have : 0 ≤ |C₀| * Real.exp 1 := by positivity
          linarith
  · push Not at hX
    have hxR : x ∈ Set.Icc (-R) R := by
      have hlt : 2 * |x| < -Real.log (π * Real.cos (2 * θ)) := by
        have := Real.log_lt_log (by positivity) hX
        rw [Real.log_one, Real.log_mul hπc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
        linarith
      have : |x| ≤ R := by
        rw [hR]; have := neg_le_abs (Real.log (π * Real.cos (2 * θ))); linarith
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have hb := hC₀ x hxR
    have hlow : Real.exp (-1) ≤ Real.exp (9 / 2 * |x| - π * Real.cos (2 * θ) * Real.exp (2 * |x|)) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    calc ‖tiltedPhi θ x‖ ≤ |C₀| := hb.trans (le_abs_self _)
      _ = |C₀| * Real.exp 1 * Real.exp (-1) := by rw [mul_assoc, he, mul_one]
      _ ≤ |C₀| * Real.exp 1 *
          Real.exp (9 / 2 * |x| - π * Real.cos (2 * θ) * Real.exp (2 * |x|)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hE.le
          linarith

/-- **The steep law is attained.** For `0 < c < π` and `θ* = ½ arccos(c/π)`, the tilted kernel
`Φ(· + iθ*)` decays at exactly the rate `c` (prefactor `e^{9|x|/2}`), and its quotient
`e^{−iθ*(s−½)}` has modulus `e^{θ* Im s}`, which meets `theta_window_steep_law` with equality. -/
theorem theta_window_tilt_attained {c : ℝ} (hc : 0 < c) (hcπ : c < π) :
    let θ := Real.arccos (c / π) / 2
    (∃ C : ℝ, ∀ x : ℝ, ‖tiltedPhi θ x‖ ≤ C * Real.exp (9 / 2 * |x| - c * Real.exp (2 * |x|))) ∧
    (∀ s : ℂ, centredLaplace (tiltedPhi θ) s = xi s * cexp (-(I * θ * (s - 1 / 2)))) ∧
    ∀ s : ℂ, ‖cexp (-(I * θ * (s - 1 / 2)))‖ = Real.exp (θ * s.im) := by
  intro θ
  have hq : c / π ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by
    have := div_pos hc Real.pi_pos; linarith, by rw [div_lt_one Real.pi_pos]; exact hcπ⟩
  have hθ0 : 0 ≤ θ := by
    show 0 ≤ Real.arccos (c / π) / 2
    have := Real.arccos_nonneg (c / π); linarith
  have hθ1 : 2 * θ < π / 2 := by
    show 2 * (Real.arccos (c / π) / 2) < π / 2
    have := Real.arccos_lt_pi_div_two.mpr (div_pos hc Real.pi_pos); linarith
  have hcos2 : π * Real.cos (2 * θ) = c := by
    show π * Real.cos (2 * (Real.arccos (c / π) / 2)) = c
    rw [show 2 * (Real.arccos (c / π) / 2) = Real.arccos (c / π) by ring,
      Real.cos_arccos (by linarith [hq.1]) hq.2.le]
    field_simp
  refine ⟨?_, fun s => centredLaplace_tiltedPhi hθ0 hθ1 s, fun s => ?_⟩
  · obtain ⟨C, hC⟩ := tiltedPhi_rate hθ0 hθ1
    exact ⟨C, fun x => by rw [← hcos2]; exact hC x⟩
  · rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]


end

end RHTower
