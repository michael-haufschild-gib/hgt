import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The constrained endpoint response constants

The endpoint-response identity fixes the endpoint square of a prolate mode in terms of the
derivative of its leakage; the classical fixed-mode asymptotic fixes that derivative.  Everything
after that is *transport of limits*, and this module proves that transport, unconditionally:

```text
E_m/(lambda d_m) -> 2 pi                                                       (10)
ell_0²/(ell_0²+ell_1²) -> 8/11                                                 (12)
|g_lambda(lambda)|²/(lambda d_1) -> 16 pi/11                                   (13)
|a_lambda|²/d_1 -> 16/(11 pi)                                                  (15)
R_lambda/d_1 -> (4 pi/33)(-zeta'(2)/zeta(2))                                   (18)
```

Each statement is an implication between limits whose hypotheses are exactly the named inputs of the
card: the endpoint identity `(5)`, the logarithmic-derivative asymptotic `(9)`, the constrained
ground-state ratio, and the exterior sawtooth incidence constant.  Nothing else is used — in
particular no prolate theory enters here, so the algebra can be checked independently of the
analytic inputs it consumes.

The one nontrivial step is the cross term of the two-mode seed: it is controlled by
`tendsto_cross_div_zero`, which turns a vanishing normalized square into a vanishing product through
`|uv|/w = sqrt(u²/w) sqrt(v²/w)`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **The cross term vanishes.**  If `u²/w` tends to `0` and `v²/w` converges, then `uv/w` tends to
`0`: on the positive part of `w` the product is exactly `sqrt(u²/w) · sqrt(v²/w)` in absolute
value. -/
theorem tendsto_cross_div_zero {u v w : ℝ → ℝ} {A : ℝ}
    (hw : ∀ᶠ l in atTop, 0 < w l)
    (hu : Tendsto (fun l => u l ^ 2 / w l) atTop (𝓝 0))
    (hv : Tendsto (fun l => v l ^ 2 / w l) atTop (𝓝 A)) :
    Tendsto (fun l => u l * v l / w l) atTop (𝓝 0) := by
  have h1 : Tendsto (fun l => Real.sqrt (u l ^ 2 / w l)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hu
    simpa [Function.comp_def] using h
  have h2 : Tendsto (fun l => Real.sqrt (v l ^ 2 / w l)) atTop (𝓝 (Real.sqrt A)) := by
    have h := (Real.continuous_sqrt.tendsto A).comp hv
    simpa [Function.comp_def] using h
  have hprod : Tendsto (fun l => Real.sqrt (u l ^ 2 / w l) * Real.sqrt (v l ^ 2 / w l)) atTop
      (𝓝 0) := by
    have h := h1.mul h2
    simpa using h
  refine squeeze_zero_norm' ?_ hprod
  filter_upwards [hw] with l hl
  have hsqrtw : Real.sqrt (w l) * Real.sqrt (w l) = w l := Real.mul_self_sqrt hl.le
  have hid : Real.sqrt (u l ^ 2 / w l) * Real.sqrt (v l ^ 2 / w l) = |u l| * |v l| / w l := by
    rw [Real.sqrt_div (sq_nonneg (u l)), Real.sqrt_div (sq_nonneg (v l)), Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, div_mul_div_comm, hsqrtw]
  rw [hid, Real.norm_eq_abs, abs_div, abs_of_pos hl, abs_mul]

/-- **Equation (10).**  The normalized endpoint square of a fixed mode tends to `2 pi`.  The inputs
are the endpoint-response identity `E = -d'/(4(1-d))` and the asymptotic `d'/(lambda d) -> -8 pi`
of the classical fixed-mode expansion. -/
theorem tendsto_endpointSq_div_leakage {d dp E : ℝ → ℝ}
    (hd : Tendsto d atTop (𝓝 0))
    (hlog : Tendsto (fun l => dp l / (l * d l)) atTop (𝓝 (-(8 * Real.pi))))
    (hrel : ∀ᶠ l in atTop, E l = -dp l / (4 * (1 - d l))) :
    Tendsto (fun l => E l / (l * d l)) atTop (𝓝 (2 * Real.pi)) := by
  have hden : Tendsto (fun l => 4 * (1 - d l)) atTop (𝓝 4) := by
    have h1 : Tendsto (fun l => 1 - d l) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hd
    have h2 := h1.const_mul (4 : ℝ)
    simpa using h2
  have hnum : Tendsto (fun l => -(dp l / (l * d l))) atTop (𝓝 (8 * Real.pi)) := by
    simpa using hlog.neg
  have hinv : Tendsto (fun l => (4 * (1 - d l))⁻¹) atTop (𝓝 (4⁻¹ : ℝ)) :=
    hden.inv₀ (by norm_num)
  have hquot : Tendsto (fun l => -(dp l / (l * d l)) * (4 * (1 - d l))⁻¹) atTop
      (𝓝 (8 * Real.pi * 4⁻¹)) := hnum.mul hinv
  have hval : 8 * Real.pi * (4 : ℝ)⁻¹ = 2 * Real.pi := by ring
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [hrel] with l hl
  rw [hl]
  ring

/-- **Equation (11), transport form.**  A mode whose leakage is negligible against the reference
leakage has negligible normalized endpoint square. -/
theorem tendsto_endpointSq_div_reference {d0 d1 e0 : ℝ → ℝ}
    (hne : ∀ᶠ l in atTop, d0 l ≠ 0)
    (h0 : Tendsto (fun l => e0 l ^ 2 / (l * d0 l)) atTop (𝓝 (2 * Real.pi)))
    (hsmall : Tendsto (fun l => d0 l / d1 l) atTop (𝓝 0)) :
    Tendsto (fun l => e0 l ^ 2 / (l * d1 l)) atTop (𝓝 0) := by
  have hprod := h0.mul hsmall
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [hne] with l hl
  field_simp

/-- **Equation (12).**  The constrained ground-state leakage ratio `delta/d_1 -> 8/11` is the same
statement as the coefficient ratio `ell_0²/(ell_0²+ell_1²) -> 8/11`, once the ground leakage is
negligible against the excited one. -/
theorem tendsto_ellSqRatio_of_deltaRatio {d0 d1 L0 L1 δ : ℝ → ℝ}
    (hd1 : ∀ᶠ l in atTop, d1 l ≠ 0)
    (hsum : ∀ᶠ l in atTop, L0 l ^ 2 + L1 l ^ 2 ≠ 0)
    (hδ : ∀ᶠ l in atTop, δ l = (L1 l ^ 2 * d0 l + L0 l ^ 2 * d1 l) / (L0 l ^ 2 + L1 l ^ 2))
    (hratio : Tendsto (fun l => δ l / d1 l) atTop (𝓝 (8 / 11)))
    (hsmall : Tendsto (fun l => L1 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2) * (d0 l / d1 l)) atTop (𝓝 0)) :
    Tendsto (fun l => L0 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2)) atTop (𝓝 (8 / 11)) := by
  have hsub := hratio.sub hsmall
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [hd1, hsum, hδ] with l h1 h2 h3
  rw [h3]
  field_simp
  ring

/-- **Equation (13).**  The two-mode CCM seed
`g = (ell_1 e_0 - ell_0 e_1)/sqrt(ell_0²+ell_1²)` has normalized endpoint square tending to
`16 pi/11`: the ground contribution and the cross term vanish, and the excited contribution carries
the weight `ell_0²/(ell_0²+ell_1²) -> 8/11` against the endpoint constant `2 pi`. -/
theorem tendsto_constrainedEndpointSq {d1 e0 e1 L0 L1 : ℝ → ℝ}
    (hw : ∀ᶠ l in atTop, 0 < l * d1 l)
    (hE0 : Tendsto (fun l => e0 l ^ 2 / (l * d1 l)) atTop (𝓝 0))
    (hE1 : Tendsto (fun l => e1 l ^ 2 / (l * d1 l)) atTop (𝓝 (2 * Real.pi)))
    (hq0 : Tendsto (fun l => L0 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2)) atTop (𝓝 (8 / 11)))
    (hq1 : Tendsto (fun l => L1 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2)) atTop (𝓝 (3 / 11))) :
    Tendsto (fun l => (L1 l * e0 l - L0 l * e1 l) ^ 2 / (L0 l ^ 2 + L1 l ^ 2) / (l * d1 l))
      atTop (𝓝 (16 * Real.pi / 11)) := by
  -- the ground term
  have hterm0 : Tendsto (fun l => L1 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2) * (e0 l ^ 2 / (l * d1 l)))
      atTop (𝓝 0) := by
    have h := hq1.mul hE0
    simpa using h
  -- the excited term
  have hterm1 : Tendsto (fun l => L0 l ^ 2 / (L0 l ^ 2 + L1 l ^ 2) * (e1 l ^ 2 / (l * d1 l)))
      atTop (𝓝 (16 * Real.pi / 11)) := by
    have h := hq0.mul hE1
    have hval : 8 / 11 * (2 * Real.pi) = 16 * Real.pi / 11 := by ring
    rwa [hval] at h
  -- the cross term
  have hcross0 : Tendsto (fun l => e0 l * e1 l / (l * d1 l)) atTop (𝓝 0) :=
    tendsto_cross_div_zero hw hE0 hE1
  have hcross : Tendsto (fun l =>
      2 * (L0 l * L1 l / (L0 l ^ 2 + L1 l ^ 2)) * (e0 l * e1 l / (l * d1 l))) atTop (𝓝 0) := by
    have habs : Tendsto (fun l => |e0 l * e1 l / (l * d1 l)|) atTop (𝓝 0) := by
      simpa using hcross0.abs
    refine squeeze_zero_norm' ?_ habs
    refine Filter.Eventually.of_forall fun l => ?_
    have hb : |2 * (L0 l * L1 l / (L0 l ^ 2 + L1 l ^ 2))| ≤ 1 := by
      rcases eq_or_ne (L0 l ^ 2 + L1 l ^ 2) 0 with hz | hz
      · rw [hz]
        simp
      · have hpos : 0 < L0 l ^ 2 + L1 l ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
        rw [mul_div_assoc', abs_div, abs_of_pos hpos, div_le_one hpos]
        have h := two_mul_le_add_sq |L0 l| |L1 l|
        rw [sq_abs, sq_abs] at h
        rw [abs_mul, abs_two, abs_mul]
        linarith [h]
    calc ‖2 * (L0 l * L1 l / (L0 l ^ 2 + L1 l ^ 2)) * (e0 l * e1 l / (l * d1 l))‖
        = |2 * (L0 l * L1 l / (L0 l ^ 2 + L1 l ^ 2))| * |e0 l * e1 l / (l * d1 l)| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ 1 * |e0 l * e1 l / (l * d1 l)| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = |e0 l * e1 l / (l * d1 l)| := one_mul _
  have hsum := (hterm0.sub hcross).add hterm1
  rw [sub_zero, zero_add] at hsum
  refine hsum.congr' (Filter.Eventually.of_forall fun l => ?_)
  ring

/-- **Equation (15).**  Scaling the seed's endpoint value by `1/(pi sqrt lambda)` turns the endpoint
constant `16 pi/11` into the amplitude constant `16/(11 pi)`. -/
theorem tendsto_lowerExteriorAmplitudeSq {d1 G A : ℝ → ℝ}
    (hA : ∀ᶠ l in atTop, A l = G l ^ 2 / (Real.pi ^ 2 * l))
    (hG : Tendsto (fun l => G l ^ 2 / (l * d1 l)) atTop (𝓝 (16 * Real.pi / 11))) :
    Tendsto (fun l => A l / d1 l) atTop (𝓝 (16 / (11 * Real.pi))) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := hG.const_mul (Real.pi ^ 2)⁻¹
  have hval : (Real.pi ^ 2)⁻¹ * (16 * Real.pi / 11) = 16 / (11 * Real.pi) := by
    field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [hA] with l hl
  rw [hl]
  ring

/-- **Equation (18).**  The all-prime response constant: the amplitude constant `16/(11 pi)` times
the exterior sawtooth incidence constant `pi²/12 · z` is `(4 pi/33) z`. -/
theorem tendsto_primeResponse_div_leakage {d1 A S R : ℝ → ℝ} {z : ℝ}
    (hR : ∀ᶠ l in atTop, R l = A l * S l)
    (hA : Tendsto (fun l => A l / d1 l) atTop (𝓝 (16 / (11 * Real.pi))))
    (hS : Tendsto S atTop (𝓝 (Real.pi ^ 2 / 12 * z))) :
    Tendsto (fun l => R l / d1 l) atTop (𝓝 (4 * Real.pi / 33 * z)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := hA.mul hS
  have hval : 16 / (11 * Real.pi) * (Real.pi ^ 2 / 12 * z) = 4 * Real.pi / 33 * z := by
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [hR] with l hl
  rw [hl]
  ring

end GaloisForLFunctions.RHTower

end
