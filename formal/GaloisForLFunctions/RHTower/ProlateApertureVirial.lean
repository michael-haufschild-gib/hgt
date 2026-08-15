import GaloisForLFunctions.RHTower.ProlateSecondMoment

/-!
# The aperture virial identity and the Gaussian shape of a prolate mode

The weight `x(1−x²)` vanishes at both aperture endpoints, so integrating

`(x(1−x²)Φ²)′ = (1 − 3x²)Φ² + 2x(1−x²)ΦΦ′`

over `[−1,1]` has no boundary contribution and gives the exact identity

`∫Φ² − 3∫x²Φ² = −2∫ x(1−x²)ΦΦ′` .

The arithmetic–geometric split of the right side against the bandwidth,

`−2x(1−x²)ΦΦ′ = c x²Φ² + (1−x²)²Φ′²/c − (cxΦ + (1−x²)Φ′)²/c` ,

is exact, and `(1−x²)² ≤ 1−x²` on the aperture, so with the prolate Rayleigh identity
`μ∫Φ² = (∫(1−x²)Φ′²)/c + c∫x²Φ²` it yields

`∫(cxΦ + (1−x²)Φ′)² ≤ c ((μ−1)∫Φ² + 3∫x²Φ²)` .

Two consequences.  Dropping the left side and using the second-moment bound `∫x²Φ² ≤ (μ/c)∫Φ²`
gives `c ≤ μ(c+3)`, a lower bound for the separation constant with no window, no averaging and no
endpoint value.  Keeping it says that once `μ` approaches `1` the mode satisfies
`(1−x²)Φ′ ≈ −cxΦ` in mean square — the prolate Gaussian shape.
-/

open MeasureTheory Set

namespace RHTower

/-- Derivative of the aperture virial weight `x(1−x²)Φ²`. -/
theorem hasDerivAt_apertureVirialWeight {Phi : ℝ → ℝ} (h1 : Differentiable ℝ Phi) (x : ℝ) :
    HasDerivAt (fun y => y * (1 - y ^ 2) * Phi y ^ 2)
      ((1 - 3 * x ^ 2) * Phi x ^ 2 + 2 * (x * (1 - x ^ 2)) * (Phi x * deriv Phi x)) x := by
  have hb : HasDerivAt (fun y => Phi y ^ 2) (2 * Phi x * deriv Phi x) x := by
    refine (((h1 x).hasDerivAt).pow 2).congr_deriv ?_
    push_cast
    ring
  have ha : HasDerivAt (fun y : ℝ => y * (1 - y ^ 2)) (1 - 3 * x ^ 2) x := by
    have hp : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      have := (hasDerivAt_pow 2 x).const_sub 1
      refine this.congr_deriv ?_
      push_cast
      ring
    refine ((hasDerivAt_id x).mul hp).congr_deriv ?_
    simp only [id_eq]
    ring
  refine (ha.mul hb).congr_deriv ?_
  ring

/-- **Aperture virial identity.**  The endpoint weight kills both boundary terms. -/
theorem integral_apertureVirial {Phi : ℝ → ℝ} (h1 : Differentiable ℝ Phi)
    (h2 : Continuous (deriv Phi)) :
    (∫ x in (-1 : ℝ)..1, Phi x ^ 2) - 3 * (∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      = -(2 * ∫ x in (-1 : ℝ)..1, (x * (1 - x ^ 2)) * (Phi x * deriv Phi x)) := by
  have hcPhi : Continuous Phi := h1.continuous
  have hsq0 : Continuous fun x : ℝ => Phi x ^ 2 := hcPhi.pow 2
  have hA0 : Continuous fun x : ℝ => (1 - 3 * x ^ 2) * Phi x ^ 2 :=
    (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))).mul hsq0
  have hB0 : Continuous fun x : ℝ => 2 * (x * (1 - x ^ 2)) * (Phi x * deriv Phi x) :=
    (continuous_const.mul
      (continuous_id.mul (continuous_const.sub (continuous_id.pow 2)))).mul (hcPhi.mul h2)
  have hcont : Continuous fun x : ℝ =>
      (1 - 3 * x ^ 2) * Phi x ^ 2 + 2 * (x * (1 - x ^ 2)) * (Phi x * deriv Phi x) := hA0.add hB0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => y * (1 - y ^ 2) * Phi y ^ 2)
    (f' := fun x : ℝ =>
      (1 - 3 * x ^ 2) * Phi x ^ 2 + 2 * (x * (1 - x ^ 2)) * (Phi x * deriv Phi x))
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (fun x _ => hasDerivAt_apertureVirialWeight h1 x)
    (hcont.intervalIntegrable _ _)
  have hend : (1 : ℝ) * (1 - (1 : ℝ) ^ 2) * Phi 1 ^ 2
      - (-1 : ℝ) * (1 - (-1 : ℝ) ^ 2) * Phi (-1) ^ 2 = 0 := by norm_num
  rw [hend] at hFTC
  rw [intervalIntegral.integral_add (hA0.intervalIntegrable _ _) (hB0.intervalIntegrable _ _)]
    at hFTC
  have hsq : Continuous fun x : ℝ => Phi x ^ 2 := hsq0
  have hmom : Continuous fun x : ℝ => x ^ 2 * Phi x ^ 2 :=
    (continuous_id.pow 2).mul hsq
  have hA' : (∫ x in (-1 : ℝ)..1, (1 - 3 * x ^ 2) * Phi x ^ 2)
      = (∫ x in (-1 : ℝ)..1, Phi x ^ 2) - 3 * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hsq.intervalIntegrable _ _) ((hmom.const_mul _).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hB' : (∫ x in (-1 : ℝ)..1, 2 * (x * (1 - x ^ 2)) * (Phi x * deriv Phi x))
      = 2 * ∫ x in (-1 : ℝ)..1, (x * (1 - x ^ 2)) * (Phi x * deriv Phi x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hA', hB'] at hFTC
  linarith

/-- **Exact arithmetic--geometric split at the aperture scale.** -/
theorem apertureVirial_split {c x p q : ℝ} (hc : c ≠ 0) :
    -(2 * ((x * (1 - x ^ 2)) * (p * q)))
      = c * (x ^ 2 * p ^ 2) + (1 - x ^ 2) ^ 2 * q ^ 2 / c
        - (c * x * p + (1 - x ^ 2) * q) ^ 2 / c := by
  field_simp
  ring

/-- **Gaussian shape estimate.**  The mean-square deviation from `(1−x²)Φ′ = −cxΦ` is controlled by
how far the separation constant exceeds the first oscillator rung. -/
theorem integral_prolateGaussianDefect_le {c chi : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (∫ x in (-1 : ℝ)..1, (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2)
      ≤ c * (((c * radialSeparationRatio c chi) - 1) * (∫ x in (-1 : ℝ)..1, Phi x ^ 2)
        + 3 * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hdd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) := (contDiff_infty_iff_deriv.mp hsm).2
  have h2c : Continuous (deriv Phi) := ((contDiff_infty_iff_deriv.mp hdd).1).continuous
  have hcPhi : Continuous Phi := h1.continuous
  have hRay := GaloisForLFunctions.RHTower.neg_separation_div_sq_mul_integral_sq_eq hcne hsm heig
  have hvir := integral_apertureVirial h1 h2c
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∫ x in (-1 : ℝ)..1, Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = ∫ x in (-1 : ℝ)..1, (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu = c * radialSeparationRatio c chi := ⟨_, rfl⟩
  rw [← hS, ← hM] at hvir
  rw [← hS, ← hM, ← hG] at hRay
  have hmuval : mu = -chi / c := by
    rw [hmu, radialSeparationRatio]
    field_simp
  have hmuS : mu * S = G / c + c * M := by
    rw [hmuval]
    field_simp at hRay ⊢
    linarith
  -- the split, integrated
  have hint : (∫ x in (-1 : ℝ)..1, -(2 * ((x * (1 - x ^ 2)) * (Phi x * deriv Phi x))))
      = ∫ x in (-1 : ℝ)..1, (c * (x ^ 2 * Phi x ^ 2)
        + (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 / c
        - (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 / c) :=
    intervalIntegral.integral_congr fun x _ => apertureVirial_split hcne
  have hleft : (∫ x in (-1 : ℝ)..1, -(2 * ((x * (1 - x ^ 2)) * (Phi x * deriv Phi x))))
      = -(2 * ∫ x in (-1 : ℝ)..1, (x * (1 - x ^ 2)) * (Phi x * deriv Phi x)) := by
    have hcongr : (∫ x in (-1 : ℝ)..1, -(2 * ((x * (1 - x ^ 2)) * (Phi x * deriv Phi x))))
        = ∫ x in (-1 : ℝ)..1, (-2 : ℝ) * ((x * (1 - x ^ 2)) * (Phi x * deriv Phi x)) :=
      intervalIntegral.integral_congr fun x _ => by ring
    rw [hcongr, intervalIntegral.integral_const_mul]
    ring
  obtain ⟨V2, hV2⟩ : ∃ V2 : ℝ,
      V2 = ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 := ⟨_, rfl⟩
  have hright : (∫ x in (-1 : ℝ)..1, (c * (x ^ 2 * Phi x ^ 2)
        + (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 / c
        - (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 / c))
      = c * M + V2 / c - D / c := by
    have ha : Continuous fun x : ℝ => c * (x ^ 2 * Phi x ^ 2) :=
      continuous_const.mul ((continuous_id.pow 2).mul (hcPhi.pow 2))
    have hb : Continuous fun x : ℝ => (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 / c :=
      (((continuous_const.sub (continuous_id.pow 2)).pow 2).mul (h2c.pow 2)).div_const c
    have hdc : Continuous fun x : ℝ =>
        (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 / c :=
      (((((continuous_const.mul continuous_id).mul hcPhi).add
        ((continuous_const.sub (continuous_id.pow 2)).mul h2c))).pow 2).div_const c
    have hab : IntervalIntegrable (fun x : ℝ => c * (x ^ 2 * Phi x ^ 2)
        + (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 / c) volume (-1) 1 :=
      (ha.add hb).intervalIntegrable _ _
    have hdi : IntervalIntegrable (fun x : ℝ =>
        (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 / c) volume (-1) 1 :=
      hdc.intervalIntegrable _ _
    have hai : IntervalIntegrable (fun x : ℝ => c * (x ^ 2 * Phi x ^ 2)) volume (-1) 1 :=
      ha.intervalIntegrable _ _
    have hbi : IntervalIntegrable
        (fun x : ℝ => (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2 / c) volume (-1) 1 :=
      hb.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hab hdi, intervalIntegral.integral_add hai hbi,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_div, ← hM, ← hV2, ← hD]
  rw [hleft, hright] at hint
  -- the squared weight is dominated by the linear one
  have hV2le : V2 ≤ G := by
    rw [hV2, hG]
    have hi1 : IntervalIntegrable
        (fun x : ℝ => (1 - x ^ 2) ^ 2 * (deriv Phi x) ^ 2) volume (-1) 1 :=
      (((continuous_const.sub (continuous_id.pow 2)).pow 2).mul (h2c.pow 2)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun x : ℝ => (1 - x ^ 2) * (deriv Phi x) ^ 2) volume (-1) 1 :=
      ((continuous_const.sub (continuous_id.pow 2)).mul (h2c.pow 2)).intervalIntegrable _ _
    refine intervalIntegral.integral_mono_on (by norm_num) hi1 hi2 ?_
    intro x hx
    have hx1 : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hx2 : (1 - x ^ 2) ≤ 1 := by nlinarith [sq_nonneg x]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hx1, hx2]) (sq_nonneg (deriv Phi x))
  rw [← hS, ← hM, ← hD]
  have hkey : S - 3 * M = c * M + V2 / c - D / c := by linarith [hvir, hint]
  have hstep : D / c ≤ (mu - 1) * S + 3 * M := by
    have hGc : V2 / c ≤ G / c := by gcongr
    linarith [hkey, hmuS, hGc]
  have hfin : D ≤ c * ((mu - 1) * S + 3 * M) := by
    rw [div_le_iff₀ hc] at hstep
    linarith [hstep]
  rw [← hmu]
  linarith [hfin]

/-- **Uniform lower bound for the separation constant, from the aperture virial.**
`c ≤ μ (c + 3)`, so `μ ≥ c/(c+3) → 1`. -/
theorem bandwidthSeparation_ge {c chi : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hpos : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ 2)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    c ≤ (c * radialSeparationRatio c chi) * (c + 3) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdef := integral_prolateGaussianDefect_le hc hsm heig
  have hDnn : (0 : ℝ)
      ≤ ∫ x in (-1 : ℝ)..1, (c * x * Phi x + (1 - x ^ 2) * deriv Phi x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have hMle := integral_sq_mul_sq_le_separation hcne hsm heig
  have hmul : (0 : ℝ) ≤ ((c * radialSeparationRatio c chi) - 1)
      * (∫ x in (-1 : ℝ)..1, Phi x ^ 2) + 3 * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2 := by
    nlinarith [hdef, hDnn, hc]
  have hM3 : 3 * (∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      ≤ 3 * (radialSeparationRatio c chi * ∫ x in (-1 : ℝ)..1, Phi x ^ 2) := by
    linarith [hMle]
  have hcomb : (0 : ℝ) ≤ (((c * radialSeparationRatio c chi) - 1)
      + 3 * radialSeparationRatio c chi) * ∫ x in (-1 : ℝ)..1, Phi x ^ 2 := by
    nlinarith [hmul, hM3]
  have hfac := (mul_nonneg_iff_of_pos_right hpos).1 hcomb
  have hid : c * (radialSeparationRatio c chi * (c + 3))
      = c * ((c * radialSeparationRatio c chi) - 1) + 3 * (c * radialSeparationRatio c chi) + c := by
    ring
  nlinarith [hfac, hc]

end RHTower
