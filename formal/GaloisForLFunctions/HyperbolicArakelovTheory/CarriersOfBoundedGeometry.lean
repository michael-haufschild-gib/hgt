import GaloisForLFunctions.HyperbolicArakelovTheory.TheDilationLimitOfATwistedCarrier

/-!
# Carriers of bounded geometry cannot carry the torsion

`TheDilationLimitOfATwistedCarrier` excludes twisted carriers that see the end `∞` of the degree
geodesic as a point of discontinuity. If `∞` is a limit point of the carrier, its images return near
the degree points and there is no dilation limit to take. This file excludes such carriers as long
as their geometry stays bounded along the degree pairs at one prime ratio.

**Bounded geometry at `(M, pM)`** (`BoundedGeometryAt`). No image of `z_{pM}` coincides with `z_M`,
and the untwisted Green majorant is bounded: `Σ_i 2πG_{1/2}(d(z_M, γ_i z_{pM})) ≤ B`. For a
geometrically finite group with `δ(Γ) < ½` whose degree ray returns to the convex core, this holds
along a positive proportion of `M` (classical: the majorant is bounded on compact sets of pairs off
the singular set).

**Mechanism.**
* *Every image is far once the majorant is bounded.* Near `cosh d = 1` the Green function is
  Newtonian, `2πG_{1/2} ≥ 1/(6√(2(X − 1)))` (`le_greenOfCosh_of_le_two`); so a majorant `≤ B`
  forces `cosh d ≥ 1 + 2h(B)` for every image (`one_add_le_of_greenOfCosh_le`).
* *Passing from `(M, pM)` to `(M, pM + 1)` moves every image distance by relative `1/(pM)`*: the
  second degree is multiplied by `λ = 1 + 1/(pM)`, and
  `cosh d(z_t, γz_{λu}) ∈ [λ⁻¹, λ]·cosh d(z_t, γz_u)` (`imageCosh_mul_right_le`).
* *The Green function is log-Lipschitz away from `X = 1`*: `X·|g′(X)| ≤ (1 + 1/h)² g(X)` on
  `X ≥ 1 + h` (`mul_abs_deriv_greenOfCosh_le`), with
  `g′ = −g·(½ + 2e^{−2d}/(1 − e^{−2d}))/sinh d`. Hence each term moves by `≤ 2(1 + 1/h)²/(pM)` of
  itself (`abs_greenOfCosh_sub_le`).

So `‖F(M, pM) − F(M, pM + 1)‖ ≤ 2(1 + 1/h)²B/(pM) → 0` along the bounded-geometry pairs
(`norm_carrierSum_sub_le`), while the torsion kernel has the constant jump `Λ(p)/√p`
(`not_carrierSum_eq_torsion_of_boundedGeometry`). With the endpoint Eisenstein condition this
leaves, for B118′.2, only carriers whose Green majorant along the degree pairs is unbounded.
-/

open Filter Topology Set
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-! ## The logarithmic derivative of the Green function -/

/-- `−archProfile′/archProfile = ½ + 2e^{−2d}/(1 − e^{−2d})`. -/
def archLogDeriv (d : ℝ) : ℝ := 1 / 2 + 2 * Real.exp (-2 * d) / (1 - Real.exp (-2 * d))

theorem hasDerivAt_archProfile {d : ℝ} (hd : d ≠ 0) :
    HasDerivAt archProfile (-(archProfile d * archLogDeriv d)) d := by
  have hu : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) d := by
    simpa using (hasDerivAt_id d).neg.div_const 2
  have hv : HasDerivAt (fun x : ℝ => -2 * x) (-2) d := by
    simpa using (hasDerivAt_id d).const_mul (-2)
  have hden := one_sub_exp_neg_two_mul_ne_zero hd
  have h3 := hu.exp.div (hv.exp.const_sub 1) hden
  refine h3.congr_deriv ?_
  simp only [archProfile, archLogDeriv]
  set E := Real.exp (-2 * d)
  set F := Real.exp (-d / 2)
  field_simp
  ring

theorem hasDerivAt_greenOfCosh {X : ℝ} (hX : 1 < X) :
    HasDerivAt greenOfCosh
      (-(greenOfCosh X * archLogDeriv (Real.arcosh X)) * (Real.sqrt (X ^ 2 - 1))⁻¹) X :=
  (hasDerivAt_archProfile (Real.arcosh_pos hX).ne').comp X (Real.hasDerivAt_arcosh hX)

/-- `½ ≤ archLogDeriv(arcosh X) ≤ ½ + 1/(X² − 1)`: `e^{2d} − 1 ≥ 2(X² − 1)`. -/
theorem archLogDeriv_arcosh_le {X : ℝ} (hX : 1 < X) :
    0 ≤ archLogDeriv (Real.arcosh X) ∧ archLogDeriv (Real.arcosh X) ≤ 1 / 2 + 1 / (X ^ 2 - 1) := by
  set d := Real.arcosh X
  have hd : 0 < d := Real.arcosh_pos hX
  have hE : Real.exp d = X + Real.sqrt (X ^ 2 - 1) := Real.exp_arcosh hX.le
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ X ^ 2 - 1 by nlinarith)
  have hs0 := Real.sqrt_nonneg (X ^ 2 - 1)
  have he2 : Real.exp (-2 * d) = (Real.exp d ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hE2 : 2 * X ^ 2 - 1 ≤ Real.exp d ^ 2 := by rw [hE]; nlinarith
  have hpos : 0 < Real.exp d ^ 2 - 1 := by nlinarith
  have hfrac : 2 * Real.exp (-2 * d) / (1 - Real.exp (-2 * d)) = 2 / (Real.exp d ^ 2 - 1) := by
    rw [he2]
    have hne : Real.exp d ^ 2 ≠ 0 := by positivity
    have hne2 : Real.exp d ^ 2 - 1 ≠ 0 := hpos.ne'
    field_simp
  have hX1 : 0 < X ^ 2 - 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · unfold archLogDeriv
    rw [hfrac]; linarith [div_pos two_pos hpos]
  · unfold archLogDeriv
    rw [hfrac]
    have : 2 / (Real.exp d ^ 2 - 1) ≤ 1 / (X ^ 2 - 1) := by
      rw [div_le_div_iff₀ hpos hX1]; nlinarith
    linarith

/-- **Log-Lipschitz bound.** `X·|g′(X)| ≤ (1 + 1/h)²·g(X)` for `X ≥ 1 + h`, `h > 0`. -/
theorem mul_abs_deriv_greenOfCosh_le {h X : ℝ} (hh : 0 < h) (hX : 1 + h ≤ X) :
    X * |-(greenOfCosh X * archLogDeriv (Real.arcosh X)) * (Real.sqrt (X ^ 2 - 1))⁻¹| ≤
      (1 + 1 / h) ^ 2 * greenOfCosh X := by
  have hX1 : 1 < X := by linarith
  have hsq : 2 * h ≤ X ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt (X ^ 2 - 1) := Real.sqrt_pos.mpr (by linarith)
  have hg := greenOfCosh_nonneg hX1.le
  obtain ⟨hL0, hL⟩ := archLogDeriv_arcosh_le hX1
  have hL' : archLogDeriv (Real.arcosh X) ≤ 1 + 1 / h := by
    have : 1 / (X ^ 2 - 1) ≤ 1 / (2 * h) := one_div_le_one_div_of_le (by positivity) hsq
    have : 1 / (2 * h) ≤ 1 / h := one_div_le_one_div_of_le hh (by linarith)
    linarith
  have hR : X * (Real.sqrt (X ^ 2 - 1))⁻¹ ≤ 1 + 1 / h := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]
    have hK : 0 ≤ 1 + 1 / h := by positivity
    have h2 : X ^ 2 ≤ (1 + 1 / h) ^ 2 * (X ^ 2 - 1) := by
      have h3 : 1 + 2 / h ≤ (1 + 1 / h) ^ 2 := by
        have e : (1 + 1 / h) ^ 2 = 1 + 2 / h + (1 / h) ^ 2 := by ring
        linarith [sq_nonneg (1 / h)]
      have h4 : 1 ≤ (X ^ 2 - 1) / h := by rw [le_div_iff₀ hh]; linarith
      have h7 : (1 + 2 / h) * (X ^ 2 - 1) ≤ (1 + 1 / h) ^ 2 * (X ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right h3 (by linarith)
      have h5 : (1 + 2 / h) * (X ^ 2 - 1) = (X ^ 2 - 1) + 2 * ((X ^ 2 - 1) / h) := by ring
      linarith
    have h6 := Real.abs_le_sqrt h2
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK] at h6
    exact (le_abs_self X).trans h6
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hg, abs_of_nonneg hL0,
    abs_of_nonneg (inv_nonneg.mpr hs.le)]
  calc X * (greenOfCosh X * archLogDeriv (Real.arcosh X) * (Real.sqrt (X ^ 2 - 1))⁻¹)
      = greenOfCosh X * archLogDeriv (Real.arcosh X) * (X * (Real.sqrt (X ^ 2 - 1))⁻¹) := by ring
    _ ≤ greenOfCosh X * (1 + 1 / h) * (1 + 1 / h) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL' hg) hR
          (mul_nonneg (by linarith) (inv_nonneg.mpr hs.le)) (mul_nonneg hg (by positivity))
    _ = (1 + 1 / h) ^ 2 * greenOfCosh X := by ring

/-- **Mean value step.** For `1 + h ≤ X ≤ Y`, `g(X) − g(Y) ≤ (1 + 1/h)² g(X)·(Y − X)/X`. -/
theorem greenOfCosh_sub_le {h X Y : ℝ} (hh : 0 < h) (hX : 1 + h ≤ X)
    (hXY : X ≤ Y) :
    greenOfCosh X - greenOfCosh Y ≤ (1 + 1 / h) ^ 2 * greenOfCosh X * ((Y - X) / X) := by
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  rcases hXY.eq_or_lt with rfl | hlt
  · simp
  have hcont : ContinuousOn greenOfCosh (Icc X Y) := fun x hx =>
    (continuousAt_greenOfCosh (hX1.trans_le hx.1)).continuousWithinAt
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope greenOfCosh
    (fun x => -(greenOfCosh x * archLogDeriv (Real.arcosh x)) * (Real.sqrt (x ^ 2 - 1))⁻¹)
    hlt hcont (fun x hx => hasDerivAt_greenOfCosh (hX1.trans hx.1))
  have hc1 : 1 + h ≤ c := hX.trans hc.1.le
  have hc0 : 0 < c := by linarith
  have hb := mul_abs_deriv_greenOfCosh_le hh hc1
  rw [hderiv] at hb
  have hgc : greenOfCosh c ≤ greenOfCosh X := greenOfCosh_anti hX1 hc.1.le
  have hYX : 0 < Y - X := by linarith
  have habs : |(greenOfCosh Y - greenOfCosh X) / (Y - X)| ≤
      (1 + 1 / h) ^ 2 * greenOfCosh X / X := by
    rw [le_div_iff₀ hX0]
    calc |(greenOfCosh Y - greenOfCosh X) / (Y - X)| * X
        ≤ |(greenOfCosh Y - greenOfCosh X) / (Y - X)| * c := by
          gcongr; exact hc.1.le
      _ = c * |(greenOfCosh Y - greenOfCosh X) / (Y - X)| := by ring
      _ ≤ (1 + 1 / h) ^ 2 * greenOfCosh c := hb
      _ ≤ (1 + 1 / h) ^ 2 * greenOfCosh X := by gcongr
  have h1 : greenOfCosh X - greenOfCosh Y ≤
      |(greenOfCosh Y - greenOfCosh X) / (Y - X)| * (Y - X) := by
    rw [abs_div, abs_of_pos hYX, div_mul_cancel₀ _ hYX.ne', abs_sub_comm]
    exact le_abs_self _
  calc greenOfCosh X - greenOfCosh Y
      ≤ |(greenOfCosh Y - greenOfCosh X) / (Y - X)| * (Y - X) := h1
    _ ≤ (1 + 1 / h) ^ 2 * greenOfCosh X / X * (Y - X) := mul_le_mul_of_nonneg_right habs hYX.le
    _ = (1 + 1 / h) ^ 2 * greenOfCosh X * ((Y - X) / X) := by ring

/-- **Relative stability.** If `X ≥ 1 + 2h`, `Y ∈ [X/λ, λX]` with `λ = 1 + ε`, `ε ≤ h/2` and
`(1 + 1/h)²ε ≤ ½`, then `|g(Y) − g(X)| ≤ 2(1 + 1/h)²ε·g(X)`. -/
theorem abs_greenOfCosh_sub_le {h ε X Y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hε : 0 ≤ ε)
    (hεh : ε ≤ h / 2) (hεK : (1 + 1 / h) ^ 2 * ε ≤ 1 / 2) (hX : 1 + 2 * h ≤ X)
    (hY1 : X ≤ (1 + ε) * Y) (hY2 : Y ≤ (1 + ε) * X) :
    |greenOfCosh Y - greenOfCosh X| ≤ 2 * ((1 + 1 / h) ^ 2 * ε) * greenOfCosh X := by
  set K := (1 + 1 / h) ^ 2 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hX0 : 0 < X := by linarith
  have hgX := greenOfCosh_nonneg (show (1 : ℝ) ≤ X by linarith)
  rcases le_total X Y with hXY | hYX
  · -- `Y ≥ X`: `g(Y) ≤ g(X)`
    have h1 := greenOfCosh_sub_le hh (by linarith) hXY
    have hrel : (Y - X) / X ≤ ε := by rw [div_le_iff₀ hX0]; linarith
    have hgY : greenOfCosh Y ≤ greenOfCosh X := greenOfCosh_anti (by linarith) hXY
    rw [abs_of_nonpos (by linarith)]
    have : K * greenOfCosh X * ((Y - X) / X) ≤ K * greenOfCosh X * ε :=
      mul_le_mul_of_nonneg_left hrel (mul_nonneg hK0 hgX)
    nlinarith [mul_nonneg (mul_nonneg hK0 hgX) hε]
  · -- `Y ≤ X`: compare from `Y`, which stays above `1 + h`
    have hY0 : 0 < Y := by nlinarith
    have hYh : 1 + h ≤ Y := by
      have : (1 + h) * (1 + ε) ≤ 1 + 2 * h := by nlinarith
      nlinarith
    have h1 := greenOfCosh_sub_le hh hYh hYX
    have hrel : (X - Y) / Y ≤ ε := by rw [div_le_iff₀ hY0]; linarith
    have hgY := greenOfCosh_nonneg (show (1 : ℝ) ≤ Y by linarith)
    have hstep : greenOfCosh Y - greenOfCosh X ≤ K * ε * greenOfCosh Y := by
      have : K * greenOfCosh Y * ((X - Y) / Y) ≤ K * greenOfCosh Y * ε :=
        mul_le_mul_of_nonneg_left hrel (mul_nonneg hK0 hgY)
      nlinarith
    have hgY2 : greenOfCosh Y ≤ 2 * greenOfCosh X := by nlinarith
    have hgXY : greenOfCosh X ≤ greenOfCosh Y := greenOfCosh_anti (by linarith) hYX
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hK0 hε) hgY]

/-! ## Bounded majorants keep every image away from the degree point -/

/-- The Newtonian lower bound `2πG_{1/2} ≥ 1/(6√(2(X − 1)))` for `1 < X ≤ 2`. -/
theorem le_greenOfCosh_of_le_two {X : ℝ} (hX : 1 < X) (hX2 : X ≤ 2) :
    1 / (6 * Real.sqrt (2 * (X - 1))) ≤ greenOfCosh X := by
  set d := Real.arcosh X
  have hd : 0 < d := Real.arcosh_pos hX
  have hcd : Real.cosh d = X := Real.cosh_arcosh hX.le
  -- `cosh d ≥ 1 + d²/2`
  have hcosh : 1 + d ^ 2 / 2 ≤ X := by
    have h2 : Real.cosh d = 1 + 2 * Real.sinh (d / 2) ^ 2 := by
      have := Real.cosh_two_mul (d / 2)
      rw [show 2 * (d / 2) = d by ring, Real.cosh_sq] at this
      linarith
    have hsh : d / 2 ≤ Real.sinh (d / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    have : (d / 2) ^ 2 ≤ Real.sinh (d / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hsh 2
    rw [← hcd, h2]; nlinarith
  have hd2 : d ≤ 2 := by nlinarith
  have hdle : d ≤ Real.sqrt (2 * (X - 1)) := by
    rw [show d = Real.sqrt (d ^ 2) from (Real.sqrt_sq hd.le).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  -- `archProfile d ≥ e^{−d/2}/(2d) ≥ 1/(6d)`
  have hden : 1 - Real.exp (-2 * d) ≤ 2 * d := by
    have := Real.add_one_le_exp (-2 * d); linarith
  have hden0 : 0 < 1 - Real.exp (-2 * d) := by
    have : Real.exp (-2 * d) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hexp : 1 / 3 ≤ Real.exp (-d / 2) := by
    have h1 : Real.exp (-1) ≤ Real.exp (-d / 2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have h3 : 1 / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 1) h2
    linarith
  have hsq0 : 0 < Real.sqrt (2 * (X - 1)) := Real.sqrt_pos.mpr (by linarith)
  calc 1 / (6 * Real.sqrt (2 * (X - 1))) ≤ 1 / (6 * d) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
    _ = (1 / 3) / (2 * d) := by ring
    _ ≤ Real.exp (-d / 2) / (1 - Real.exp (-2 * d)) :=
        div_le_div₀ (Real.exp_pos _).le hexp hden0 hden
    _ = greenOfCosh X := rfl

/-- The distance threshold `h(B) = min(½, 1/(144B²))`. -/
def nearThreshold (B : ℝ) : ℝ := min (1 / 2) (1 / (144 * B ^ 2))

theorem nearThreshold_pos {B : ℝ} (hB : 0 < B) : 0 < nearThreshold B := by
  unfold nearThreshold; positivity

theorem nearThreshold_le_half (B : ℝ) : nearThreshold B ≤ 1 / 2 := min_le_left _ _

/-- **A bounded Green value keeps the image away.** `1 < X` and `g(X) ≤ B` give `X ≥ 1 + 2h(B)`. -/
theorem one_add_le_of_greenOfCosh_le {B X : ℝ} (hB : 0 < B) (hX : 1 < X) (hg : greenOfCosh X ≤ B) :
    1 + 2 * nearThreshold B ≤ X := by
  have hh := nearThreshold_le_half B
  by_contra hlt
  push Not at hlt
  have hX2 : X ≤ 2 := by linarith
  have hsmall : X - 1 < 1 / (72 * B ^ 2) := by
    have : nearThreshold B ≤ 1 / (144 * B ^ 2) := min_le_right _ _
    have e : 2 * (1 / (144 * B ^ 2)) = 1 / (72 * B ^ 2) := by field_simp; ring
    linarith
  have hlow := le_greenOfCosh_of_le_two hX hX2
  have hs : Real.sqrt (2 * (X - 1)) < 1 / (6 * B) := by
    rw [show 1 / (6 * B) = Real.sqrt ((1 / (6 * B)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_lt_sqrt (by linarith)
    have e : (1 / (6 * B)) ^ 2 = 2 * (1 / (72 * B ^ 2)) := by field_simp; ring
    rw [e]; linarith
  have hs0 : 0 < Real.sqrt (2 * (X - 1)) := Real.sqrt_pos.mpr (by linarith)
  have : B < 1 / (6 * Real.sqrt (2 * (X - 1))) := by
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hs (show 0 < 6 * B by positivity)
    rw [show 6 * B * (1 / (6 * B)) = 1 by field_simp] at this
    nlinarith
  linarith

/-! ## Relative motion of the image distances -/

/-- Multiplying the second degree by `λ ≥ 1` moves `cosh d(z_t, γz_u)` within `[λ⁻¹, λ]`. -/
theorem imageCosh_mul_right_le (g : SL2C) {t u l : ℝ} (ht : 0 < t) (hu : 0 < u) (hl : 1 ≤ l) :
    imageCosh g t (l * u) ≤ l * imageCosh g t u ∧ imageCosh g t u ≤ l * imageCosh g t (l * u) := by
  have hl0 : 0 < l := by linarith
  have hl2 : 0 ≤ l ^ 2 - 1 := by nlinarith
  constructor
  · have e : l * imageCosh g t u - imageCosh g t (l * u) =
        (l ^ 2 - 1) * (‖g.1 0 1‖ ^ 2 + ‖g.1 1 1‖ ^ 2 * t ^ 2) / (2 * t * l * u) := by
      unfold imageCosh; field_simp [ht.ne', hu.ne', hl0.ne']; ring
    have : 0 ≤ (l ^ 2 - 1) * (‖g.1 0 1‖ ^ 2 + ‖g.1 1 1‖ ^ 2 * t ^ 2) / (2 * t * l * u) :=
      div_nonneg (mul_nonneg hl2 (by positivity)) (by positivity)
    linarith
  · have e : l * imageCosh g t (l * u) - imageCosh g t u =
        (l ^ 2 - 1) * (‖g.1 0 0‖ ^ 2 * u ^ 2 + ‖g.1 1 0‖ ^ 2 * t ^ 2 * u ^ 2) / (2 * t * u) := by
      unfold imageCosh; field_simp [ht.ne', hu.ne', hl0.ne']; ring
    have : 0 ≤ (l ^ 2 - 1) * (‖g.1 0 0‖ ^ 2 * u ^ 2 + ‖g.1 1 0‖ ^ 2 * t ^ 2 * u ^ 2) /
        (2 * t * u) := div_nonneg (mul_nonneg hl2 (by positivity)) (by positivity)
    linarith

/-! ## The jump of a carrier of bounded geometry -/

/-- **Bounded geometry at `(M, pM)`**: no image of `z_{pM}` hits `z_M`, and the untwisted Green
majorant `Σ_i 2πG_{1/2}(d(z_M, γ_i z_{pM}))` converges with sum `≤ B`. -/
def BoundedGeometryAt {ι : Type*} (γ : ι → SL2C) (p B M : ℝ) : Prop :=
  (∀ i, 1 < imageCosh (γ i) M (p * M)) ∧
    Summable (fun i => greenOfCosh (imageCosh (γ i) M (p * M))) ∧
    ∑' i, greenOfCosh (imageCosh (γ i) M (p * M)) ≤ B

/-- **The jump of a bounded-geometry carrier is `O(1/M)`.** -/
theorem norm_carrierSum_sub_le {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1)
    {p B M : ℝ} (hp : 1 ≤ p) (hB : 0 < B) (hM : 0 < M)
    (hlarge : 2 * (1 + 1 / nearThreshold B) ^ 2 + 2 / nearThreshold B ≤ p * M)
    (hbg : BoundedGeometryAt γ p B M) :
    ‖carrierSum γ w M (p * M) - carrierSum γ w M (p * M + 1)‖ ≤
      2 * ((1 + 1 / nearThreshold B) ^ 2 * (1 / (p * M))) * B := by
  obtain ⟨hsing, hsum, hle⟩ := hbg
  set h := nearThreshold B with hhdef
  have hh := nearThreshold_pos hB
  have hh1 : h ≤ 1 := (nearThreshold_le_half B).trans (by norm_num)
  set ε := 1 / (p * M) with hεdef
  have hpM : 0 < p * M := by nlinarith
  have hε0 : 0 ≤ ε := by positivity
  set K := (1 + 1 / h) ^ 2 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hεh : ε ≤ h / 2 := by
    rw [hεdef, div_le_div_iff₀ hpM (by norm_num : (0 : ℝ) < 2)]
    have : 2 / h ≤ p * M := by have := sq_nonneg (1 + 1 / h); linarith
    rw [div_le_iff₀ hh] at this; nlinarith
  have hεK : K * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ hpM (by norm_num : (0 : ℝ) < 2)]
    have : 0 ≤ 2 / h := by positivity
    linarith
  have hlam : p * M + 1 = (1 + ε) * (p * M) := by rw [hεdef]; field_simp [hpM.ne']
  -- each term
  have hterm : ∀ i, |greenOfCosh (imageCosh (γ i) M (p * M + 1)) -
      greenOfCosh (imageCosh (γ i) M (p * M))| ≤
      2 * (K * ε) * greenOfCosh (imageCosh (γ i) M (p * M)) := by
    intro i
    have hgi : greenOfCosh (imageCosh (γ i) M (p * M)) ≤ B :=
      (hsum.le_tsum i fun j _ => greenOfCosh_nonneg (one_le_imageCosh _ hM hpM)).trans hle
    have hX := one_add_le_of_greenOfCosh_le hB (hsing i) hgi
    obtain ⟨h1, h2⟩ := imageCosh_mul_right_le (γ i) hM hpM (show 1 ≤ 1 + ε by linarith)
    rw [← hlam] at h1 h2
    exact abs_greenOfCosh_sub_le hh hh1 hε0 hεh hεK hX h2 h1
  -- summability of the moved majorant
  have hsum' : Summable fun i => greenOfCosh (imageCosh (γ i) M (p * M + 1)) := by
    refine Summable.of_nonneg_of_le (fun i => greenOfCosh_nonneg
      (one_le_imageCosh _ hM (by linarith))) (fun i => ?_) (hsum.mul_left 2)
    have := hterm i
    have h0 := greenOfCosh_nonneg (one_le_imageCosh (γ i) hM hpM)
    have : greenOfCosh (imageCosh (γ i) M (p * M + 1)) ≤
        greenOfCosh (imageCosh (γ i) M (p * M)) + 2 * (K * ε) *
          greenOfCosh (imageCosh (γ i) M (p * M)) := by
      have := le_abs_self (greenOfCosh (imageCosh (γ i) M (p * M + 1)) -
        greenOfCosh (imageCosh (γ i) M (p * M)))
      linarith
    nlinarith
  have hc1 : Summable fun i => w i * (greenOfCosh (imageCosh (γ i) M (p * M)) : ℂ) :=
    Summable.of_norm_bounded hsum fun i =>
      norm_carrierTerm_le (hw i) (one_le_imageCosh _ hM hpM)
  have hc2 : Summable fun i => w i * (greenOfCosh (imageCosh (γ i) M (p * M + 1)) : ℂ) :=
    Summable.of_norm_bounded hsum' fun i =>
      norm_carrierTerm_le (hw i) (one_le_imageCosh _ hM (by linarith))
  unfold carrierSum
  rw [← hc1.tsum_sub hc2]
  have hb : ∀ i, ‖w i * (greenOfCosh (imageCosh (γ i) M (p * M)) : ℂ) -
      w i * (greenOfCosh (imageCosh (γ i) M (p * M + 1)) : ℂ)‖ ≤
      2 * (K * ε) * greenOfCosh (imageCosh (γ i) M (p * M)) := by
    intro i
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm]
    have h0 : 0 ≤ |greenOfCosh (imageCosh (γ i) M (p * M + 1)) -
        greenOfCosh (imageCosh (γ i) M (p * M))| := abs_nonneg _
    calc ‖w i‖ * |greenOfCosh (imageCosh (γ i) M (p * M + 1)) -
          greenOfCosh (imageCosh (γ i) M (p * M))|
        ≤ 1 * |greenOfCosh (imageCosh (γ i) M (p * M + 1)) -
          greenOfCosh (imageCosh (γ i) M (p * M))| := by gcongr; exact hw i
      _ ≤ 2 * (K * ε) * greenOfCosh (imageCosh (γ i) M (p * M)) := by
          rw [one_mul]; exact hterm i
  calc ‖∑' i, (w i * (greenOfCosh (imageCosh (γ i) M (p * M)) : ℂ) -
        w i * (greenOfCosh (imageCosh (γ i) M (p * M + 1)) : ℂ))‖
      ≤ ∑' i, 2 * (K * ε) * greenOfCosh (imageCosh (γ i) M (p * M)) :=
        tsum_of_norm_bounded (hsum.mul_left _).hasSum hb
    _ = 2 * (K * ε) * ∑' i, greenOfCosh (imageCosh (γ i) M (p * M)) := tsum_mul_left
    _ ≤ 2 * (K * ε) * B := by gcongr

/-- **No carrier of bounded geometry carries the torsion kernel.** If for one prime `p` the
carrier has bounded geometry at `(M, pM)` for infinitely many `M`, then
`F(m, n) = κ·Λ(n/m)(n/m)^{−1/2}` fails for every `κ ≠ 0`. -/
theorem not_carrierSum_eq_torsion_of_boundedGeometry {ι : Type*} {γ : ι → SL2C} {w : ι → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) {p : ℕ} (hp : p.Prime) {B : ℝ} (hB : 0 < B)
    (hbg : ∃ᶠ M : ℕ in atTop, BoundedGeometryAt γ p B M) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum γ w m n = κ * (weilPrimeKernel m n : ℂ) := by
  intro hid
  set c := ‖κ‖ * (Real.log p / Real.sqrt p) with hcdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hc : 0 < c := mul_pos (norm_pos_iff.mpr hκ)
    (div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.sqrt_pos.mpr (by linarith)))
  set h := nearThreshold B
  have hh := nearThreshold_pos hB
  set A := 2 * (1 + 1 / h) ^ 2 * B with hA
  have hA0 : 0 ≤ A := by positivity
  -- eventually the bound is below the jump
  have hev : ∀ᶠ M : ℕ in atTop, 2 ≤ M ∧
      2 * (1 + 1 / h) ^ 2 + 2 / h ≤ (p : ℝ) * M ∧ A / ((p : ℝ) * M) < c := by
    have ht : Tendsto (fun M : ℕ => (p : ℝ) * M) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
    have h3 : Tendsto (fun M : ℕ => A / ((p : ℝ) * M)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ht
    exact (eventually_ge_atTop 2).and ((ht.eventually_ge_atTop _).and
      (h3.eventually (gt_mem_nhds hc)))
  obtain ⟨M, hbgM, hM2, hlarge, hsmall⟩ := (hbg.and_eventually hev).exists
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hbound := norm_carrierSum_sub_le hw hp1 hB hM0 hlarge hbgM
  -- the jump of the torsion kernel
  have e1 := hid M (p * M) (by omega) (Nat.mul_pos hp.pos (by omega))
    (by intro h'; nlinarith [hp.two_le])
  have e2 := hid M (p * M + 1) (by omega) (by omega) (by intro h'; nlinarith [hp.two_le])
  push_cast at e1 e2
  rw [e1, e2, weilPrimeKernel_mul_prime hp (by omega),
    weilPrimeKernel_mul_prime_add_one hp.one_lt.le hM2] at hbound
  have hjump : ‖κ * ((Real.log p / Real.sqrt p : ℝ) : ℂ) - κ * ((0 : ℝ) : ℂ)‖ = c := by
    rw [Complex.ofReal_zero, mul_zero, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (Real.log_nonneg hp1) (Real.sqrt_nonneg _))]
  rw [hjump] at hbound
  have : 2 * ((1 + 1 / h) ^ 2 * (1 / ((p : ℝ) * M))) * B = A / ((p : ℝ) * M) := by
    rw [hA]; ring
  linarith

/-- **Pigeonhole over the prime ratios.** It suffices that for infinitely many `M` one of the primes
of a finite set `F` gives bounded geometry at `(M, pM)`. -/
theorem not_carrierSum_eq_torsion_of_frequently_boundedGeometry {ι : Type*} {γ : ι → SL2C}
    {w : ι → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) {B : ℝ} (hB : 0 < B)
    (hbg : ∃ᶠ M : ℕ in atTop, ∃ p ∈ F, BoundedGeometryAt γ p B M) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum γ w m n = κ * (weilPrimeKernel m n : ℂ) := by
  have : ∃ p ∈ F, ∃ᶠ M : ℕ in atTop, BoundedGeometryAt γ p B M := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ᶠ M : ℕ in atTop, ∀ p ∈ (F : Set ℕ), ¬ BoundedGeometryAt γ p B M :=
      (eventually_all_finite F.finite_toSet).mpr fun p hp => (hcon p hp).mono fun M h => h
    exact hbg (hall.mono fun M hM ⟨p, hp, h⟩ => hM p hp h)
  obtain ⟨p, hp, hfreq⟩ := this
  exact not_carrierSum_eq_torsion_of_boundedGeometry hw hκ (hF p hp) hB hfreq

end GaloisForLFunctions.HyperbolicArakelovTheory
