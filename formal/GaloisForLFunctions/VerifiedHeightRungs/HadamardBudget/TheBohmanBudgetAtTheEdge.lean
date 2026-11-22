import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheFejerBudget

/-!
# The positive-definite Bohman budget at the edge of absolute convergence

Replacing the Fejér triangle `(1 - |u| / L)₊` (`O(τ⁻²)` frequency tail, infinite second moment)
with the compactly supported positive-definite **Bohman kernel**

`W_L(u) = (1 - |u| / L) cos(π |u| / L) + sin(π |u| / L) / π`  (`|u| ≤ L`),  `0` (`|u| ≥ L`),

eliminates the `O(1 / γ)` archimedean smoothing remainder completely:

1. **Positive-definite `O(τ⁻⁴)` probability density (`bohmanK`)**:
   `B_L(τ) = 4 π L cos²(L τ / 2) / (π² - L² τ²)² ≥ 0` (`B_L(±π/L) = L / (4π)`) satisfies
   `∫ B_L(τ) cos(y τ) dτ = W_L(y)`, `∫ B_L(τ) dτ = 1`, and finite second moment
   `∫ τ² B_L(τ) dτ ≤ 72 / L²`.
2. **Closed-form Laplace transform (`bohmanLaplace_eq`)**:
   `∫₀^∞ W_L(u) e^{-x u} du = L² x / (L² x² + π²) + 2 π² L (1 + e^{-x L}) / (L² x² + π²)²`.
3. **Edge budget (`bohman_budget_at_edge`)**: passing `a → (1/2)⁺` (`Re s → 1⁺`) bounds an off-line
   zero of `ξ` at ordinate `γ ≥ 4` (`4 π < L γ`) with purely `O(1 / (L² γ²))` archimedean tail:
   `4 L² / (L² + 4 π²) + 64 π² L (1 + e^{-L/2}) / (L² + 4 π²)² ≤`
   `  1/4 log(9/4 + γ²/4) - (log π)/2 + 1/1215 + 18/(L² γ²) + 1200/(L³ γ⁴)`
   `  - ∑_{n < N} (Λ(n)/n) W_L(log n) cos(γ log n)`.
-/

open Complex MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Bohman kernel on `[-L, L]` -/

/-- The positive-definite Bohman kernel `(1 - |u|/L) cos(π|u|/L) + sin(π|u|/L)/π` on `|u| ≤ L`,
vanishing for `|u| ≥ L`. -/
def bohmanFn (L u : ℝ) : ℝ :=
  let t := min (|u| / L) 1
  (1 - t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t) / Real.pi

variable {L : ℝ}

theorem continuous_bohmanFn (L : ℝ) : Continuous (bohmanFn L) := by
  unfold bohmanFn
  fun_prop

theorem bohmanFn_zero (L : ℝ) : bohmanFn L 0 = 1 := by
  simp [bohmanFn]

theorem bohmanFn_neg (L u : ℝ) : bohmanFn L (-u) = bohmanFn L u := by
  simp [bohmanFn]

theorem bohmanFn_of_nonneg_of_le (hL : 0 < L) {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ L) :
    bohmanFn L u = (1 - u / L) * Real.cos (Real.pi * u / L) + Real.sin (Real.pi * u / L) / Real.pi := by
  unfold bohmanFn
  have hle : |u| / L ≤ 1 := by rw [abs_of_nonneg hu0, div_le_one hL]; exact huL
  rw [min_eq_left hle, abs_of_nonneg hu0, mul_div_assoc]

theorem bohmanFn_eq_zero (hL : 0 < L) {u : ℝ} (hu : L ≤ |u|) : bohmanFn L u = 0 := by
  unfold bohmanFn
  have hge : 1 ≤ |u| / L := (one_le_div hL).mpr hu
  rw [min_eq_right hge]
  simp

/-- Monotone envelope of `g(θ) = (π - θ) cos θ + sin θ` on `[0, π]`, where `g'(θ) = -(π - θ) sin θ ≤ 0`. -/
private theorem bohman_angle_bounds {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    0 ≤ (Real.pi - θ) * Real.cos θ + Real.sin θ ∧
      (Real.pi - θ) * Real.cos θ + Real.sin θ ≤ Real.pi := by
  let g : ℝ → ℝ := fun x => (Real.pi - x) * Real.cos x + Real.sin x
  have hderiv : ∀ x : ℝ, HasDerivAt g (-(Real.pi - x) * Real.sin x) x := fun x => by
    have h1 : HasDerivAt (fun y => Real.pi - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub Real.pi
    refine ((h1.mul (Real.hasDerivAt_cos x)).add (Real.hasDerivAt_sin x)).congr_deriv ?_
    ring
  have hanti : AntitoneOn g (Icc 0 Real.pi) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 Real.pi)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x).hasDerivWithinAt) fun x hx => ?_
    have hx' : x ∈ Ioo 0 Real.pi := by rwa [interior_Icc] at hx
    have hsin : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx'.1.le hx'.2.le
    have hsub : 0 ≤ Real.pi - x := sub_nonneg.mpr hx'.2.le
    nlinarith
  have hg0 : g 0 = Real.pi := by simp [g]
  have hgπ : g Real.pi = 0 := by simp [g]
  have hmem : θ ∈ Icc 0 Real.pi := ⟨h0, hπ⟩
  have hle_top := hanti ⟨le_rfl, Real.pi_pos.le⟩ hmem h0
  have hge_bot := hanti hmem ⟨Real.pi_pos.le, le_rfl⟩ hπ
  rw [hg0] at hle_top
  rw [hgπ] at hge_bot
  exact ⟨hge_bot, hle_top⟩

theorem bohmanFn_nonneg (hL : 0 < L) (u : ℝ) : 0 ≤ bohmanFn L u := by
  unfold bohmanFn
  set t := min (|u| / L) 1
  have ht0 : 0 ≤ t := le_min (by positivity) zero_le_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have hπ := Real.pi_pos
  have hθ0 : 0 ≤ Real.pi * t := mul_nonneg hπ.le ht0
  have hθπ : Real.pi * t ≤ Real.pi := by nlinarith
  have hb := (bohman_angle_bounds hθ0 hθπ).1
  have hid : (1 - t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t) / Real.pi =
      ((Real.pi - Real.pi * t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t)) / Real.pi := by
    field_simp
  rw [hid]
  exact div_nonneg hb hπ.le

theorem bohmanFn_le_one (hL : 0 < L) (u : ℝ) : bohmanFn L u ≤ 1 := by
  unfold bohmanFn
  set t := min (|u| / L) 1
  have ht0 : 0 ≤ t := le_min (by positivity) zero_le_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have hπ := Real.pi_pos
  have hθ0 : 0 ≤ Real.pi * t := mul_nonneg hπ.le ht0
  have hθπ : Real.pi * t ≤ Real.pi := by nlinarith
  have hb := (bohman_angle_bounds hθ0 hθπ).2
  have hid : (1 - t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t) / Real.pi =
      ((Real.pi - Real.pi * t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t)) / Real.pi := by
    field_simp
  rw [hid, div_le_one hπ]
  exact hb

theorem hasCompactSupport_bohmanFn (hL : 0 < L) : HasCompactSupport (bohmanFn L) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -L) (b := L)) ?_
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hnot
  apply hu
  apply bohmanFn_eq_zero hL
  rw [mem_Icc, not_and_or, not_le, not_le] at hnot
  rcases hnot with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_bohmanFn (hL : 0 < L) : Integrable (bohmanFn L) :=
  (continuous_bohmanFn L).integrable_of_hasCompactSupport (hasCompactSupport_bohmanFn hL)

/-! ## Unified complex exponential integral on `[0, L]` -/

/-- Exact complex integral `∫₀^L W_L(u) e^{z u} du` for every `z ∈ ℂ` with `z² + (π/L)² ≠ 0`. -/
private theorem integral_bohman_cexp_right (hL : 0 < L) {z : ℂ}
    (hz : z ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2 ≠ 0) :
    ∫ u in (0 : ℝ)..L, ((bohmanFn L u : ℝ) : ℂ) * cexp (z * (u : ℂ)) =
      -z / (z ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2) +
        2 * ((Real.pi / L : ℝ) : ℂ) ^ 2 * (1 + cexp (z * (L : ℂ))) /
          ((L : ℂ) * (z ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2) ^ 2) := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  set ω : ℝ := Real.pi / L
  let fR (u : ℝ) : ℝ := (1 - u / L) * Real.cos (ω * u) + Real.sin (ω * u) / Real.pi
  let gR (u : ℝ) : ℝ := -(ω * (1 - u / L) * Real.sin (ω * u))
  have hf_deriv : ∀ u : ℝ, HasDerivAt fR (gR u) u := fun u => by
    have h1 : HasDerivAt (fun y : ℝ => 1 - y / L) (-(1 / L)) u := by
      simpa using ((hasDerivAt_id u).div_const L).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => Real.cos (ω * y)) (-Real.sin (ω * u) * ω) u :=
      ((Real.hasDerivAt_cos (ω * u)).comp u ((hasDerivAt_id u).const_mul ω)).congr_deriv (by ring)
    have h3 : HasDerivAt (fun y : ℝ => Real.sin (ω * y) / Real.pi)
        (Real.cos (ω * u) * ω / Real.pi) u :=
      (((Real.hasDerivAt_sin (ω * u)).comp u
        ((hasDerivAt_id u).const_mul ω)).div_const Real.pi).congr_deriv (by ring)
    refine ((h1.mul h2).add h3).congr_deriv ?_
    dsimp only [gR, ω]
    have hπr : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hLr : L ≠ 0 := hL.ne'
    field_simp [hπr, hLr]
    ring
  have hg_deriv : ∀ u : ℝ,
      HasDerivAt gR (-(ω ^ 2) * fR u + 2 * (ω / L) * Real.sin (ω * u)) u := fun u => by
    have h1 : HasDerivAt (fun y : ℝ => ω * (1 - y / L)) (-(ω / L)) u := by
      have := (((hasDerivAt_id u).div_const L).const_sub 1).const_mul ω
      exact this.congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (ω * y)) (Real.cos (ω * u) * ω) u :=
      ((Real.hasDerivAt_sin (ω * u)).comp u ((hasDerivAt_id u).const_mul ω)).congr_deriv (by ring)
    refine (h1.mul h2).neg.congr_deriv ?_
    dsimp only [fR, ω]
    have hπr : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hLr : L ≠ 0 := hL.ne'
    field_simp [hπr, hLr]
    ring
  set D : ℂ := z ^ 2 + (ω : ℂ) ^ 2
  have hD : D ≠ 0 := by simpa only [D, ω] using hz
  let prim (u : ℝ) : ℂ :=
    cexp (z * (u : ℂ)) / D *
      (z * (fR u : ℂ) - (gR u : ℂ) +
        2 * ((ω : ℂ) / (L : ℂ)) *
          (z * (Real.sin (ω * u) : ℂ) - (ω : ℂ) * (Real.cos (ω * u) : ℂ)) / D)
  have hprim_deriv : ∀ u : ℝ, HasDerivAt prim ((fR u : ℂ) * cexp (z * (u : ℂ))) u := fun u => by
    have he : HasDerivAt (fun y : ℝ => cexp (z * (y : ℂ))) (cexp (z * (u : ℂ)) * z) u := by
      simpa using ((hasDerivAt_id u).ofReal_comp.const_mul z).cexp
    have hfC : HasDerivAt (fun y : ℝ => (fR y : ℂ)) (gR u : ℂ) u := (hf_deriv u).ofReal_comp
    have hgC : HasDerivAt (fun y : ℝ => (gR y : ℂ))
        (((-(ω ^ 2) * fR u + 2 * (ω / L) * Real.sin (ω * u) : ℝ)) : ℂ) u :=
      (hg_deriv u).ofReal_comp
    have hsinC : HasDerivAt (fun y : ℝ => (Real.sin (ω * y) : ℂ))
        (((Real.cos (ω * u) * ω : ℝ)) : ℂ) u :=
      (((Real.hasDerivAt_sin (ω * u)).comp u
        ((hasDerivAt_id u).const_mul ω)).congr_deriv (by ring)).ofReal_comp
    have hcosC : HasDerivAt (fun y : ℝ => (Real.cos (ω * y) : ℂ))
        (((-Real.sin (ω * u) * ω : ℝ)) : ℂ) u :=
      (((Real.hasDerivAt_cos (ω * u)).comp u
        ((hasDerivAt_id u).const_mul ω)).congr_deriv (by ring)).ofReal_comp
    have hinner : HasDerivAt
        (fun y : ℝ => z * (fR y : ℂ) - (gR y : ℂ) +
          2 * ((ω : ℂ) / (L : ℂ)) *
            (z * (Real.sin (ω * y) : ℂ) - (ω : ℂ) * (Real.cos (ω * y) : ℂ)) / D)
        (z * (gR u : ℂ) - (((-(ω ^ 2) * fR u + 2 * (ω / L) * Real.sin (ω * u) : ℝ)) : ℂ) +
          2 * ((ω : ℂ) / (L : ℂ)) *
            (z * (((Real.cos (ω * u) * ω : ℝ)) : ℂ) -
              (ω : ℂ) * (((-Real.sin (ω * u) * ω : ℝ)) : ℂ)) / D) u :=
      ((hfC.const_mul z).sub hgC).add
        ((((hsinC.const_mul z).sub (hcosC.const_mul (ω : ℂ))).const_mul
          (2 * ((ω : ℂ) / (L : ℂ)))).div_const D)
    refine ((he.div_const D).mul hinner).congr_deriv ?_
    generalize cexp (z * (u : ℂ)) = E
    have hcast1 : (((-(ω ^ 2) * fR u + 2 * (ω / L) * Real.sin (ω * u) : ℝ)) : ℂ) =
        -((ω : ℂ) ^ 2) * (fR u : ℂ) + 2 * ((ω : ℂ) / (L : ℂ)) * (Real.sin (ω * u) : ℂ) := by
      push_cast; ring
    have hcast2 : (((Real.cos (ω * u) * ω : ℝ)) : ℂ) = (Real.cos (ω * u) : ℂ) * (ω : ℂ) := by
      push_cast; ring
    have hcast3 : (((-Real.sin (ω * u) * ω : ℝ)) : ℂ) = -(Real.sin (ω * u) : ℂ) * (ω : ℂ) := by
      push_cast; ring
    rw [hcast1, hcast2, hcast3]
    have hD_def : z ^ 2 + (ω : ℂ) ^ 2 = D := rfl
    field_simp [hD, hLc]
    linear_combination E * ((L : ℂ) * (fR u : ℂ) * D - 2 * (ω : ℂ) * (Real.sin (ω * u) : ℂ)) * hD_def
  have hcongr : ∫ u in (0 : ℝ)..L, ((bohmanFn L u : ℝ) : ℂ) * cexp (z * (u : ℂ)) =
      ∫ u in (0 : ℝ)..L, (fR u : ℂ) * cexp (z * (u : ℂ)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hL.le] at hu
    congr 2
    rw [bohmanFn_of_nonneg_of_le hL hu.1 hu.2]
    dsimp only [fR, ω]
    rw [div_mul_eq_mul_div]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hprim_deriv u)
    ((by fun_prop : Continuous fun u => (fR u : ℂ) * cexp (z * (u : ℂ))).intervalIntegrable _ _)]
  have hf0 : fR 0 = 1 := by simp [fR]
  have hg0 : gR 0 = 0 := by simp [gR]
  have hωL : ω * L = Real.pi := by dsimp only [ω]; field_simp
  have hfL : fR L = 0 := by simp [fR, div_self hL.ne', hωL]
  have hgL : gR L = 0 := by simp [gR, div_self hL.ne']
  dsimp only [prim]
  rw [hf0, hg0, hfL, hgL, mul_zero, Real.sin_zero, Real.cos_zero, hωL, Real.sin_pi, Real.cos_pi]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, mul_zero,
    Complex.exp_zero, sub_zero, zero_sub, mul_one, one_div, zero_add]
  have hD_def : D = z ^ 2 + (ω : ℂ) ^ 2 := rfl
  rw [hD_def] at hD ⊢
  field_simp [hD, hLc]
  ring

/-! ## The Bohman frequency profile and probability density -/

/-- Exact Fourier transform `∫_{-L}^L W_L(u) e^{i v u} du` of `bohmanFn L`. -/
def bohmanBandProfile (L v : ℝ) : ℝ :=
  if (L * v) ^ 2 = Real.pi ^ 2 then L / 2
  else 8 * Real.pi ^ 2 * L * Real.cos (L * v / 2) ^ 2 / (Real.pi ^ 2 - (L * v) ^ 2) ^ 2

/-- Resonant integral at `v = ±π / L`: `∫₀^L W_L(u) cos(π u / L) du = L / 4`. -/
private theorem integral_bohman_cos_resonant (hL : 0 < L) :
    ∫ u in (0 : ℝ)..L, bohmanFn L u * Real.cos (Real.pi * u / L) = L / 4 := by
  let ω : ℝ := Real.pi / L
  let fR (u : ℝ) : ℝ :=
    ((1 - u / L) * Real.cos (ω * u) + Real.sin (ω * u) / Real.pi) * Real.cos (ω * u)
  let G (u : ℝ) : ℝ :=
    (u - u ^ 2 / (2 * L)) / 2 +
      L / (4 * Real.pi) * (1 - u / L) * Real.sin (2 * ω * u) -
      3 * L / (8 * Real.pi ^ 2) * Real.cos (2 * ω * u)
  have hderiv : ∀ u : ℝ, HasDerivAt G (fR u) u := fun u => by
    have h1 : HasDerivAt (fun y : ℝ => (y - y ^ 2 / (2 * L)) / 2) ((1 - u / L) / 2) u := by
      have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
        simpa using (hasDerivAt_pow 2 u)
      refine (((hasDerivAt_id u).sub (hp.div_const (2 * L))).div_const 2).congr_deriv ?_
      have hLr : L ≠ 0 := hL.ne'
      field_simp [hLr]
    have h2a : HasDerivAt (fun y : ℝ => L / (4 * Real.pi) * (1 - y / L)) (-(1 / (4 * Real.pi))) u := by
      refine ((((hasDerivAt_id u).div_const L).const_sub 1).const_mul
        (L / (4 * Real.pi))).congr_deriv ?_
      have hLr : L ≠ 0 := hL.ne'
      have hπr : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp [hLr, hπr]
    have h2b : HasDerivAt (fun y : ℝ => Real.sin (2 * ω * y)) (Real.cos (2 * ω * u) * (2 * ω)) u :=
      ((Real.hasDerivAt_sin (2 * ω * u)).comp u
        ((hasDerivAt_id u).const_mul (2 * ω))).congr_deriv (by ring)
    have h3 : HasDerivAt (fun y : ℝ => 3 * L / (8 * Real.pi ^ 2) * Real.cos (2 * ω * y))
        (3 * L / (8 * Real.pi ^ 2) * (-Real.sin (2 * ω * u) * (2 * ω))) u := by
      refine ((Real.hasDerivAt_cos (2 * ω * u)).comp u
        ((hasDerivAt_id u).const_mul (2 * ω))).const_mul (3 * L / (8 * Real.pi ^ 2)) |>.congr_deriv ?_
      ring
    refine ((h1.add (h2a.mul h2b)).sub h3).congr_deriv ?_
    have hc2 : Real.cos (2 * ω * u) = 2 * Real.cos (ω * u) ^ 2 - 1 := by
      rw [show 2 * ω * u = 2 * (ω * u) by ring, Real.cos_two_mul]
    have hs2 : Real.sin (2 * ω * u) = 2 * Real.sin (ω * u) * Real.cos (ω * u) := by
      rw [show 2 * ω * u = 2 * (ω * u) by ring, Real.sin_two_mul]
    rw [hc2, hs2]
    dsimp only [fR, ω]
    have hLr : L ≠ 0 := hL.ne'
    have hπr : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hLr, hπr]
    ring
  have hcongr : ∫ u in (0 : ℝ)..L, bohmanFn L u * Real.cos (Real.pi * u / L) =
      ∫ u in (0 : ℝ)..L, fR u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hL.le] at hu
    rw [bohmanFn_of_nonneg_of_le hL hu.1 hu.2]
    dsimp only [fR, ω]
    rw [div_mul_eq_mul_div]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    ((by fun_prop : Continuous fR).intervalIntegrable _ _)]
  have h2ωL : 2 * ω * L = 2 * Real.pi := by dsimp only [ω]; field_simp
  dsimp only [G]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, h2ωL, Real.sin_two_pi, Real.cos_two_pi]
  have hLr : L ≠ 0 := hL.ne'
  have hπr : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hLr, hπr]
  ring

/-- `∫_{-L}^L W_L(ξ) e^{i ξ v} dξ = bohmanBandProfile L v` for all `v ∈ ℝ`. -/
theorem integral_bohman_cexp_eq_profile (hL : 0 < L) (v : ℝ) :
    ∫ ξ in (-L)..L, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)) =
      (bohmanBandProfile L v : ℂ) := by
  have hcont : Continuous (fun ξ : ℝ => ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ))) := by
    have := continuous_bohmanFn L; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hleft : ∫ ξ in (-L)..0, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)) =
      ∫ u in (0 : ℝ)..L, ((bohmanFn L u : ℝ) : ℂ) * cexp ((-I * (v : ℂ)) * (u : ℂ)) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := L)
      (fun ξ : ℝ => ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [bohmanFn_neg, Complex.ofReal_neg]
    congr 2; ring
  have hright : ∫ ξ in (0 : ℝ)..L, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)) =
      ∫ u in (0 : ℝ)..L, ((bohmanFn L u : ℝ) : ℂ) * cexp ((I * (v : ℂ)) * (u : ℂ)) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2; ring
  rw [hleft, hright]
  by_cases hres : (L * v) ^ 2 = Real.pi ^ 2
  · unfold bohmanBandProfile
    rw [if_pos hres, ← intervalIntegral.integral_add
      ((by have := continuous_bohmanFn L; fun_prop : Continuous fun u : ℝ => ((bohmanFn L u : ℝ) : ℂ) *
          cexp ((-I * (v : ℂ)) * (u : ℂ))).intervalIntegrable _ _)
      ((by have := continuous_bohmanFn L; fun_prop : Continuous fun u : ℝ => ((bohmanFn L u : ℝ) : ℂ) *
          cexp ((I * (v : ℂ)) * (u : ℂ))).intervalIntegrable _ _)]
    have habs : |v| = Real.pi / L := by
      have h1 : |L * v| = Real.pi := by
        have hsq : |L * v| ^ 2 = Real.pi ^ 2 := by rw [sq_abs, hres]
        exact (sq_eq_sq₀ (abs_nonneg _) Real.pi_pos.le).mp hsq
      rw [abs_mul, abs_of_pos hL] at h1
      exact (eq_div_iff hL.ne').mpr (by linarith)
    have hcos_eq : ∀ u : ℝ,
        cexp ((-I * (v : ℂ)) * (u : ℂ)) + cexp ((I * (v : ℂ)) * (u : ℂ)) =
          ((2 * Real.cos (Real.pi * u / L) : ℝ) : ℂ) := fun u => by
      have he1 : (-I * (v : ℂ)) * (u : ℂ) = ((-(v * u) : ℝ) : ℂ) * I := by push_cast; ring
      have he2 : (I * (v : ℂ)) * (u : ℂ) = ((v * u : ℝ) : ℂ) * I := by push_cast; ring
      rw [he1, he2, Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      have hvu : Real.cos (v * u) = Real.cos (Real.pi * u / L) := by
        rcases abs_cases v with ⟨habs_eq, _⟩ | ⟨habs_eq, _⟩
        · have hv' : v = Real.pi / L := by linarith
          rw [hv']; congr 1; ring
        · have hv' : v = -(Real.pi / L) := by linarith
          rw [hv', neg_mul, Real.cos_neg]; congr 1; ring
      rw [hvu]
      push_cast; ring
    have hint_eq : (∫ u in (0 : ℝ)..L,
          ((bohmanFn L u : ℝ) : ℂ) * cexp ((-I * (v : ℂ)) * (u : ℂ)) +
            ((bohmanFn L u : ℝ) : ℂ) * cexp ((I * (v : ℂ)) * (u : ℂ))) =
        ((2 * ∫ u in (0 : ℝ)..L, bohmanFn L u * Real.cos (Real.pi * u / L) : ℝ) : ℂ) := by
      have hpt : ∀ u : ℝ,
          ((bohmanFn L u : ℝ) : ℂ) * cexp ((-I * (v : ℂ)) * (u : ℂ)) +
            ((bohmanFn L u : ℝ) : ℂ) * cexp ((I * (v : ℂ)) * (u : ℂ)) =
          (((2 * (bohmanFn L u * Real.cos (Real.pi * u / L)) : ℝ)) : ℂ) := fun u => by
        rw [← mul_add, hcos_eq u]; push_cast; ring
      simp_rw [hpt]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
    rw [hint_eq, integral_bohman_cos_resonant hL]
    push_cast; ring
  · unfold bohmanBandProfile
    rw [if_neg hres]
    have hD_ne : ∀ s : ℂ, s ^ 2 = -((v : ℂ) ^ 2) →
        s ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2 ≠ 0 := by
      intro s hs h0
      rw [hs] at h0
      have hreal : -(v ^ 2) + (Real.pi / L) ^ 2 = 0 := by
        have := congrArg Complex.re h0
        simpa [pow_two] using this
      apply hres
      have hLr : L ≠ 0 := hL.ne'
      field_simp [hLr] at hreal
      linarith
    have h1 := integral_bohman_cexp_right hL (z := -I * (v : ℂ))
      (hD_ne _ (by ring_nf; simp [Complex.I_sq]))
    have h2 := integral_bohman_cexp_right hL (z := I * (v : ℂ))
      (hD_ne _ (by ring_nf; simp [Complex.I_sq]))
    rw [h1, h2]
    have hsq1 : (-I * (v : ℂ)) ^ 2 = -((v : ℂ) ^ 2) := by ring_nf; simp [Complex.I_sq]
    have hsq2 : (I * (v : ℂ)) ^ 2 = -((v : ℂ) ^ 2) := by ring_nf; simp [Complex.I_sq]
    rw [hsq1, hsq2]
    have hexp_sum : 1 + cexp (-I * (v : ℂ) * (L : ℂ)) + (1 + cexp (I * (v : ℂ) * (L : ℂ))) =
        ((4 * Real.cos (L * v / 2) ^ 2 : ℝ) : ℂ) := by
      have he1 : -I * (v : ℂ) * (L : ℂ) = ((-(L * v) : ℝ) : ℂ) * I := by push_cast; ring
      have he2 : I * (v : ℂ) * (L : ℂ) = ((L * v : ℝ) : ℂ) * I := by push_cast; ring
      rw [he1, he2, Complex.exp_mul_I, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      have hc : Real.cos (L * v) = 2 * Real.cos (L * v / 2) ^ 2 - 1 := by
        conv_lhs => rw [show L * v = 2 * (L * v / 2) by ring, Real.cos_two_mul]
      rw [hc]
      push_cast; ring
    have hD_c : -((v : ℂ) ^ 2) + ((Real.pi / L : ℝ) : ℂ) ^ 2 =
        (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) := by
      have hLr : L ≠ 0 := hL.ne'
      push_cast; field_simp [hLr]; ring
    have hdiff_ne : ((Real.pi ^ 2 - (L * v) ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hres))
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    rw [hD_c]
    have halg : -(-I * (v : ℂ)) / (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) +
          2 * ((Real.pi / L : ℝ) : ℂ) ^ 2 * (1 + cexp (-I * (v : ℂ) * (L : ℂ))) /
            ((L : ℂ) * (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) ^ 2) +
        (-(I * (v : ℂ)) / (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) +
          2 * ((Real.pi / L : ℝ) : ℂ) ^ 2 * (1 + cexp (I * (v : ℂ) * (L : ℂ))) /
            ((L : ℂ) * (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) ^ 2)) =
        2 * ((Real.pi / L : ℝ) : ℂ) ^ 2 *
          (1 + cexp (-I * (v : ℂ) * (L : ℂ)) + (1 + cexp (I * (v : ℂ) * (L : ℂ)))) /
          ((L : ℂ) * (((Real.pi ^ 2 - (L * v) ^ 2) / L ^ 2 : ℝ) : ℂ) ^ 2) := by ring
    rw [halg, hexp_sum]
    push_cast
    field_simp [hdiff_ne, hLc]
    ring

theorem bohmanBandProfile_nonneg (hL : 0 < L) (v : ℝ) : 0 ≤ bohmanBandProfile L v := by
  unfold bohmanBandProfile
  split_ifs
  · positivity
  · positivity

theorem bohmanBandProfile_neg (L v : ℝ) : bohmanBandProfile L (-v) = bohmanBandProfile L v := by
  unfold bohmanBandProfile
  have hsq : (L * -v) ^ 2 = (L * v) ^ 2 := by ring
  have hcos : Real.cos (L * -v / 2) = Real.cos (L * v / 2) := by
    rw [show L * -v / 2 = -(L * v / 2) by ring, Real.cos_neg]
  rw [hsq, hcos]

theorem continuous_bohmanBandProfile (hL : 0 < L) : Continuous (bohmanBandProfile L) := by
  have h : (fun v : ℝ => ((bohmanBandProfile L v : ℝ) : ℂ)) =
      fun v : ℝ => ∫ ξ in (-L)..L, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)) := by
    funext v; exact (integral_bohman_cexp_eq_profile hL v).symm
  have hc : Continuous (fun v : ℝ =>
      ∫ ξ in (-L)..L, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ))) := by
    have := continuous_bohmanFn L
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (v : ℝ) (ξ : ℝ) => ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)))
      (by fun_prop) continuous_const
  rw [← h] at hc
  exact (Complex.continuous_re.comp hc).congr fun v => by simp

/-- Global supremum `bohmanBandProfile L v ≤ 8 L / π²`, proved directly from `W_L ≥ 0` and
`bohmanBandProfile L 0 = 8 L / π²`. -/
theorem bohmanBandProfile_le (hL : 0 < L) (v : ℝ) :
    bohmanBandProfile L v ≤ 8 * L / Real.pi ^ 2 := by
  have hre_v : bohmanBandProfile L v =
      ∫ ξ in (-L)..L, bohmanFn L ξ * Real.cos (ξ * v) := by
    have hpt : ∀ ξ : ℝ, ((bohmanFn L ξ : ℝ) : ℂ) * cexp (I * (ξ : ℂ) * (v : ℂ)) =
        ((bohmanFn L ξ * Real.cos (ξ * v) : ℝ) : ℂ) +
          ((bohmanFn L ξ * Real.sin (ξ * v) : ℝ) : ℂ) * I := fun ξ => by
      have he : I * (ξ : ℂ) * (v : ℂ) = ((ξ * v : ℝ) : ℂ) * I := by push_cast; ring
      rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
    have h := integral_bohman_cexp_eq_profile hL v
    simp_rw [hpt] at h
    rw [intervalIntegral.integral_add
      ((by have := continuous_bohmanFn L; fun_prop : Continuous _).intervalIntegrable _ _)
      ((by have := continuous_bohmanFn L; fun_prop : Continuous _).intervalIntegrable _ _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at hre
    exact hre.symm
  have hre_0 : bohmanBandProfile L 0 = ∫ ξ in (-L)..L, bohmanFn L ξ := by
    have h0 := congrArg Complex.re (integral_bohman_cexp_eq_profile hL 0)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      intervalIntegral.integral_ofReal, Complex.ofReal_re] at h0
    exact h0.symm
  have hval_0 : bohmanBandProfile L 0 = 8 * L / Real.pi ^ 2 := by
    unfold bohmanBandProfile
    rw [mul_zero, zero_pow (by norm_num), if_neg (pow_pos Real.pi_pos 2).ne]
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    simp only [zero_div, Real.cos_zero, one_pow, mul_one, sub_zero]
    field_simp [hπ]
  rw [hre_v, ← hval_0, hre_0]
  refine intervalIntegral.integral_mono_on (by linarith)
    ((by have := continuous_bohmanFn L; fun_prop : Continuous _).intervalIntegrable _ _)
    ((continuous_bohmanFn L).intervalIntegrable _ _) fun ξ _ => ?_
  exact mul_le_of_le_one_right (bohmanFn_nonneg hL ξ) (Real.cos_le_one _)

/-- Quartic tail decay for `|v| > 2 π / L`: `bohmanBandProfile L v ≤ 128 π² / (9 L³ v⁴)`. -/
theorem bohmanBandProfile_le_inv_pow_four (hL : 0 < L) {v : ℝ} (hv : 2 * Real.pi / L < |v|) :
    bohmanBandProfile L v ≤ 128 * Real.pi ^ 2 / (9 * L ^ 3 * v ^ 4) := by
  have := Real.pi_pos
  have hLv : 2 * Real.pi < L * |v| := by linarith [(div_lt_iff₀ hL).mp hv]
  have hsq_gt : 4 * Real.pi ^ 2 < (L * v) ^ 2 := by
    have h1 : (2 * Real.pi) ^ 2 < (L * |v|) ^ 2 :=
      pow_lt_pow_left₀ hLv (by positivity) (by norm_num : 2 ≠ 0)
    have h2 : (L * |v|) ^ 2 = (L * v) ^ 2 := by rw [mul_pow, sq_abs, mul_pow]
    linarith
  have hne : (L * v) ^ 2 ≠ Real.pi ^ 2 := by nlinarith [sq_pos_of_pos Real.pi_pos, hsq_gt]
  unfold bohmanBandProfile
  rw [if_neg hne]
  have hgap : 3 / 4 * (L * v) ^ 2 ≤ (L * v) ^ 2 - Real.pi ^ 2 := by linarith
  have hden : (3 / 4 * (L * v) ^ 2) ^ 2 ≤ (Real.pi ^ 2 - (L * v) ^ 2) ^ 2 := by
    rw [show (Real.pi ^ 2 - (L * v) ^ 2) ^ 2 = ((L * v) ^ 2 - Real.pi ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hgap 2
  have hcos : Real.cos (L * v / 2) ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  have hv0 : v ≠ 0 := by rintro rfl; simp at hLv; linarith
  have hpos_den : 0 < (3 / 4 * (L * v) ^ 2) ^ 2 := by positivity
  calc 8 * Real.pi ^ 2 * L * Real.cos (L * v / 2) ^ 2 / (Real.pi ^ 2 - (L * v) ^ 2) ^ 2
      ≤ 8 * Real.pi ^ 2 * L * 1 / (Real.pi ^ 2 - (L * v) ^ 2) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
    _ ≤ (8 * Real.pi ^ 2 * L) / (3 / 4 * (L * v) ^ 2) ^ 2 := by
        rw [mul_one]
        exact div_le_div_of_nonneg_left (by positivity) hpos_den hden
    _ = 128 * Real.pi ^ 2 / (9 * L ^ 3 * v ^ 4) := by
        field_simp [hL.ne', hv0]; ring

theorem bohmanBandProfile_le_lorentz (hL : 0 < L) (v : ℝ) :
    bohmanBandProfile L v ≤
      (8 * L / Real.pi ^ 2) * (1 + (2 * Real.pi / L) ^ 2) * (1 + v ^ 2)⁻¹ := by
  have hπ := Real.pi_pos
  have hpos : 0 < 1 + v ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  rcases le_or_gt |v| (2 * Real.pi / L) with hsmall | hlarge
  · have hv2 : v ^ 2 ≤ (2 * Real.pi / L) ^ 2 := by
      rw [← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg v) hsmall 2
    exact mul_le_mul (bohmanBandProfile_le hL v) (by linarith) hpos.le (by positivity)
  · have hv2 : (2 * Real.pi / L) ^ 2 < v ^ 2 := by
      rw [← sq_abs v]; exact pow_lt_pow_left₀ hlarge (by positivity) (by norm_num : 2 ≠ 0)
    have hv0 : v ≠ 0 := by rintro rfl; simp at hlarge; linarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hπ) hL]
    have hbd := bohmanBandProfile_le_inv_pow_four hL hlarge
    calc bohmanBandProfile L v * (1 + v ^ 2)
        ≤ (128 * Real.pi ^ 2 / (9 * L ^ 3 * v ^ 4)) * (1 + v ^ 2) :=
          mul_le_mul_of_nonneg_right hbd hpos.le
      _ ≤ (8 * L / Real.pi ^ 2) * (1 + (2 * Real.pi / L) ^ 2) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have h4 : (2 * Real.pi / L) ^ 4 ≤ v ^ 4 := by
            have := pow_le_pow_left₀ (by positivity) hv2.le 2
            nlinarith
          have hkey1 : 128 * Real.pi ^ 2 ≤
              8 * L / Real.pi ^ 2 * (2 * Real.pi / L) ^ 2 * (9 * L ^ 3 * (2 * Real.pi / L) ^ 2) := by
            field_simp [hL.ne', hπ.ne']; norm_num
          have hkey2 : 128 * Real.pi ^ 2 * v ^ 2 ≤
              8 * L / Real.pi ^ 2 * (2 * Real.pi / L) ^ 2 * (9 * L ^ 3 * v ^ 4) := by
            have hm1 := mul_le_mul_of_nonneg_right hkey1 (sq_nonneg v)
            have hm2 : (2 * Real.pi / L) ^ 2 * v ^ 2 ≤ v ^ 4 := by nlinarith [sq_nonneg v]
            have hc : 0 ≤ 8 * L / Real.pi ^ 2 * (2 * Real.pi / L) ^ 2 * (9 * L ^ 3) := by positivity
            linarith [hm1, mul_le_mul_of_nonneg_left hm2 hc]
          have hkey0 : 128 * Real.pi ^ 2 ≤
              8 * L / Real.pi ^ 2 * 1 * (9 * L ^ 3 * v ^ 4) := by
            have hm3 := mul_le_mul_of_nonneg_left h4
              (by positivity : (0 : ℝ) ≤ 72 * L / Real.pi ^ 2 * L ^ 3)
            have hid : 72 * L / Real.pi ^ 2 * L ^ 3 * (2 * Real.pi / L) ^ 4 = 1152 * Real.pi ^ 2 := by
              field_simp [hL.ne', hπ.ne']; ring
            have hid2 : 72 * L / Real.pi ^ 2 * L ^ 3 * v ^ 4 =
                8 * L / Real.pi ^ 2 * 1 * (9 * L ^ 3 * v ^ 4) := by ring
            linarith [hm3, hid, hid2, sq_nonneg Real.pi]
          linarith

theorem integrable_bohmanBandProfile (hL : 0 < L) : Integrable (bohmanBandProfile L) := by
  refine Integrable.mono'
    (integrable_inv_one_add_sq.const_mul ((8 * L / Real.pi ^ 2) * (1 + (2 * Real.pi / L) ^ 2)))
    (continuous_bohmanBandProfile hL).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (bohmanBandProfile_nonneg hL v)]
  exact bohmanBandProfile_le_lorentz hL v

/-- `bohmanBandProfile L v = 𝓕(bohmanFn L)(-v / (2π))`. -/
private theorem bohmanBandProfile_eq_fourier (hL : 0 < L) (v : ℝ) :
    ((bohmanBandProfile L v : ℝ) : ℂ) =
      FourierTransform.fourier (fun u : ℝ => ((bohmanFn L u : ℝ) : ℂ)) (-v / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq, ← integral_bohman_cexp_eq_profile hL v]
  have hrew : (∫ x : ℝ, Real.fourierChar (-((x : ℝ) * (-v / (2 * Real.pi)))) •
        ((bohmanFn L x : ℝ) : ℂ)) =
      ∫ u : ℝ, ((bohmanFn L u : ℝ) : ℂ) * cexp (I * (u : ℂ) * (v : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    push_cast; field_simp [hπ]
  rw [hrew]
  have hsupp' : ∀ u ∉ Ioc (-L) L, ((bohmanFn L u : ℝ) : ℂ) * cexp (I * (u : ℂ) * (v : ℂ)) = 0 := by
    intro u hu
    rw [bohmanFn_eq_zero hL, Complex.ofReal_zero, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp',
    ← intervalIntegral.integral_of_le (by linarith)]

private theorem integrable_fourier_bohmanFn (hL : 0 < L) :
    Integrable (FourierTransform.fourier (fun u : ℝ => ((bohmanFn L u : ℝ) : ℂ))) := by
  have h : FourierTransform.fourier (fun u : ℝ => ((bohmanFn L u : ℝ) : ℂ)) =
      fun w : ℝ => ((bohmanBandProfile L (-(2 * Real.pi) * w) : ℝ) : ℂ) := by
    funext w
    rw [bohmanBandProfile_eq_fourier hL]
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hπ]
  rw [h]
  exact ((integrable_bohmanBandProfile hL).comp_mul_left'
    (neg_ne_zero.mpr (by positivity))).ofReal

/-- **Fourier inversion for the Bohman profile:** `∫ bohmanBandProfile L v · e^{-i y v} dv = 2 π W_L(y)`. -/
theorem integral_bohmanBandProfile_mul_cexp (hL : 0 < L) (y : ℝ) :
    ∫ v, ((bohmanBandProfile L v : ℝ) : ℂ) * cexp (-(I * (y : ℂ) * (v : ℂ))) =
      2 * Real.pi * ((bohmanFn L y : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun u => ((bohmanFn L u : ℝ) : ℂ) with hf
  have hfc : Continuous f := by have := continuous_bohmanFn L; fun_prop
  have hfi : Integrable f := (integrable_bohmanFn hL).ofReal
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi (integrable_fourier_bohmanFn hL)) y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq] at hinv
  set g : ℝ → ℂ := fun w =>
    FourierTransform.fourier f w * cexp (((2 * Real.pi * (w * y)) : ℝ) * I) with hg
  have hinv' : ∫ w, g w = f y := by
    rw [← hinv]
    congr 1 with w
    simp only [hg, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [mul_comm, show -(w * -y) = w * y by ring]
  have hcov := Measure.integral_comp_mul_left g (-(1 / (2 * Real.pi)))
  have hpt : ∀ v : ℝ, g (-(1 / (2 * Real.pi)) * v) =
      ((bohmanBandProfile L v : ℝ) : ℂ) * cexp (-(I * (y : ℂ) * (v : ℂ))) := by
    intro v
    simp only [hg, hf]
    rw [bohmanBandProfile_eq_fourier hL]
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    congr 2
    · ring_nf
    · push_cast; field_simp [hπ]
  simp_rw [hpt] at hcov
  rw [hcov, hinv', show |(-(1 / (2 * Real.pi)))⁻¹| = 2 * Real.pi by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)], Complex.real_smul]
  simp only [hf]
  push_cast; ring

/-- The normalized Bohman probability density `B_L(τ) = bohmanBandProfile L τ / (2 π)`. -/
def bohmanK (L τ : ℝ) : ℝ := bohmanBandProfile L τ / (2 * Real.pi)

theorem bohmanK_nonneg (hL : 0 < L) (τ : ℝ) : 0 ≤ bohmanK L τ :=
  div_nonneg (bohmanBandProfile_nonneg hL τ) (by positivity)

theorem bohmanK_neg (L τ : ℝ) : bohmanK L (-τ) = bohmanK L τ := by
  unfold bohmanK; rw [bohmanBandProfile_neg]

theorem continuous_bohmanK (hL : 0 < L) : Continuous (bohmanK L) :=
  (continuous_bohmanBandProfile hL).div_const _

theorem integrable_bohmanK (hL : 0 < L) : Integrable (bohmanK L) :=
  (integrable_bohmanBandProfile hL).div_const _

theorem bohmanK_le (hL : 0 < L) (τ : ℝ) : bohmanK L τ ≤ 4 * L / Real.pi ^ 3 := by
  unfold bohmanK
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  calc bohmanBandProfile L τ / (2 * Real.pi)
      ≤ (8 * L / Real.pi ^ 2) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (bohmanBandProfile_le hL τ) (by positivity)
    _ = 4 * L / Real.pi ^ 3 := by field_simp [hπ]; ring

theorem bohmanK_le_inv_pow_four (hL : 0 < L) {τ : ℝ} (hτ : 2 * Real.pi / L < |τ|) :
    bohmanK L τ ≤ 64 * Real.pi / (9 * L ^ 3 * τ ^ 4) := by
  unfold bohmanK
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hτ0 : τ ≠ 0 := by
    rintro rfl; simp at hτ
    linarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hL]
  calc bohmanBandProfile L τ / (2 * Real.pi)
      ≤ (128 * Real.pi ^ 2 / (9 * L ^ 3 * τ ^ 4)) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (bohmanBandProfile_le_inv_pow_four hL hτ) (by positivity)
    _ = 64 * Real.pi / (9 * L ^ 3 * τ ^ 4) := by field_simp [hL.ne', hτ0, hπ]; ring

private theorem integrable_bohmanProfile_mul_cexp (hL : 0 < L) (y : ℝ) :
    Integrable fun v : ℝ => ((bohmanBandProfile L v : ℝ) : ℂ) * cexp (-(I * (y : ℂ) * (v : ℂ))) := by
  refine (integrable_bohmanBandProfile hL).ofReal.mul_bdd
    (c := 1) (by fun_prop : Continuous fun v : ℝ => cexp (-(I * (y : ℂ) * (v : ℂ)))).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  have : -(I * (y : ℂ) * (v : ℂ)) = ((-(y * v) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private theorem cexp_neg_mul_bohman (y v : ℝ) :
    cexp (-(I * (y : ℂ) * (v : ℂ))) =
      ((Real.cos (y * v) : ℝ) : ℂ) - ((Real.sin (y * v) : ℝ) : ℂ) * I := by
  have : -(I * (y : ℂ) * (v : ℂ)) = ((-(y * v) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast; ring

private theorem re_ofReal_mul_sub_bohman (F c s : ℝ) :
    ((F : ℂ) * ((c : ℂ) - (s : ℂ) * I)).re = F * c := by
  simp [Complex.mul_re]

private theorem im_ofReal_mul_sub_bohman (F c s : ℝ) :
    ((F : ℂ) * ((c : ℂ) - (s : ℂ) * I)).im = -(F * s) := by
  simp [Complex.mul_im]

/-- `∫ bohmanK L τ * cos(y τ) dτ = bohmanFn L y`. -/
theorem integral_bohmanK_mul_cos (hL : 0 < L) (y : ℝ) :
    ∫ τ, bohmanK L τ * Real.cos (y * τ) = bohmanFn L y := by
  have h := integral_bohmanBandProfile_mul_cexp hL y
  have h2π : (2 : ℂ) * (Real.pi : ℂ) * ((bohmanFn L y : ℝ) : ℂ) =
      ((2 * Real.pi * bohmanFn L y : ℝ) : ℂ) := by push_cast; ring
  rw [h2π] at h
  have hre := congrArg Complex.re h
  have hint := integrable_bohmanProfile_mul_cexp hL y
  rw [Complex.ofReal_re, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint] at hre
  have e : ∀ v : ℝ, Complex.reCLM (((bohmanBandProfile L v : ℝ) : ℂ) *
      cexp (-(I * (y : ℂ) * (v : ℂ)))) = bohmanBandProfile L v * Real.cos (y * v) := fun v => by
    rw [Complex.reCLM_apply, cexp_neg_mul_bohman, re_ofReal_mul_sub_bohman]
  simp_rw [e] at hre
  unfold bohmanK
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, hre]
  have := Real.pi_pos
  field_simp

/-- `∫ bohmanK L τ * sin(y τ) dτ = 0`. -/
theorem integral_bohmanK_mul_sin (hL : 0 < L) (y : ℝ) :
    ∫ τ, bohmanK L τ * Real.sin (y * τ) = 0 := by
  have h := integral_bohmanBandProfile_mul_cexp hL y
  have h2π : (2 : ℂ) * (Real.pi : ℂ) * ((bohmanFn L y : ℝ) : ℂ) =
      ((2 * Real.pi * bohmanFn L y : ℝ) : ℂ) := by push_cast; ring
  rw [h2π] at h
  have him := congrArg Complex.im h
  have hint := integrable_bohmanProfile_mul_cexp hL y
  rw [Complex.ofReal_im, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint] at him
  have e : ∀ v : ℝ, Complex.imCLM (((bohmanBandProfile L v : ℝ) : ℂ) *
      cexp (-(I * (y : ℂ) * (v : ℂ)))) = -(bohmanBandProfile L v * Real.sin (y * v)) := fun v => by
    rw [Complex.imCLM_apply, cexp_neg_mul_bohman, im_ofReal_mul_sub_bohman]
  simp_rw [e] at him
  rw [integral_neg, neg_eq_zero] at him
  unfold bohmanK
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, him, zero_div]

theorem integral_bohmanK (hL : 0 < L) : ∫ τ, bohmanK L τ = 1 := by
  simpa [bohmanFn_zero] using integral_bohmanK_mul_cos hL 0

theorem integrable_bohmanK_mul_bdd (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ τ, |f τ| ≤ C) : Integrable fun τ => bohmanK L τ * f τ :=
  (integrable_bohmanK hL).mul_bdd (c := C) hf.aestronglyMeasurable
    (ae_of_all _ fun τ => by simpa [Real.norm_eq_abs] using hC τ)

theorem integral_bohmanK_mul_cos_add (hL : 0 < L) (γ θ : ℝ) :
    ∫ τ, bohmanK L τ * Real.cos ((γ + τ) * θ) = bohmanFn L θ * Real.cos (γ * θ) := by
  have e : ∀ τ, bohmanK L τ * Real.cos ((γ + τ) * θ) =
      Real.cos (γ * θ) * (bohmanK L τ * Real.cos (θ * τ)) -
        Real.sin (γ * θ) * (bohmanK L τ * Real.sin (θ * τ)) := fun τ => by
    rw [show (γ + τ) * θ = γ * θ + θ * τ by ring, Real.cos_add]; ring
  simp_rw [e]
  have hc := integrable_bohmanK_mul_bdd hL (f := fun τ => Real.cos (θ * τ)) (by fun_prop)
    (C := 1) (fun _ => Real.abs_cos_le_one _)
  have hs := integrable_bohmanK_mul_bdd hL (f := fun τ => Real.sin (θ * τ)) (by fun_prop)
    (C := 1) (fun _ => Real.abs_sin_le_one _)
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    integral_bohmanK_mul_cos hL, integral_bohmanK_mul_sin hL]
  ring

/-! ## Finite second moment of `bohmanK` -/

private def bohmanTailSq (R τ : ℝ) : ℝ := if R < |τ| then (τ ^ 2)⁻¹ else 0

private theorem integrable_bohmanTailSq {R : ℝ} (hR : 0 < R) : Integrable (bohmanTailSq R) := by
  have hmeas : Measurable (bohmanTailSq R) := by
    unfold bohmanTailSq
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const
  refine ((integrable_inv_one_add_sq).const_mul ((1 + R ^ 2) / R ^ 2)).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  unfold bohmanTailSq
  split_ifs with h
  · have hτ2 : R ^ 2 ≤ τ ^ 2 := by rw [← sq_abs τ]; exact pow_le_pow_left₀ hR.le h.le 2
    have hτ2_pos : 0 < τ ^ 2 := lt_of_lt_of_le (by positivity) hτ2
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ2_pos),
      ← div_eq_mul_inv, div_div, inv_eq_one_div, div_le_div_iff₀ hτ2_pos (by positivity)]
    nlinarith [sq_nonneg τ]
  · rw [norm_zero]; positivity

private theorem integral_bohmanTailSq {R : ℝ} (hR : 0 < R) :
    ∫ τ, bohmanTailSq R τ = 2 / R := by
  have h := integral_comp_abs (f := fun r : ℝ => if R < r then (r ^ 2)⁻¹ else 0)
  have hcongr : bohmanTailSq R = fun τ => if R < |τ| then (|τ| ^ 2)⁻¹ else 0 := by
    funext τ; unfold bohmanTailSq; rw [sq_abs]
  rw [hcongr, h]
  have e : (∫ r in Ioi (0 : ℝ), (if R < r then (r ^ 2)⁻¹ else 0)) =
      ∫ r in Ioi R, r ^ (-2 : ℝ) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    by_cases hr : R < r
    · have hr0 : 0 < r := hR.trans hr
      simp only [indicator, mem_Ioi, hr0, hr, ↓reduceIte]
      rw [Real.rpow_neg hr0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · simp [indicator, hr]
  rw [e, integral_Ioi_rpow_of_lt (by norm_num) hR, show (-2 : ℝ) + 1 = -1 by norm_num,
    Real.rpow_neg_one]
  field_simp

/-- Finite second moment `∫ τ² B_L(τ) dτ ≤ 72 / L²` of the Bohman probability density. -/
theorem integrable_and_integral_sq_mul_bohmanK_le (hL : 0 < L) :
    Integrable (fun τ => τ ^ 2 * bohmanK L τ) ∧
      ∫ τ, τ ^ 2 * bohmanK L τ ≤ 72 / L ^ 2 := by
  have hπ := Real.pi_pos
  set R : ℝ := 2 * Real.pi / L
  have hR : 0 < R := by positivity
  let maj (τ : ℝ) : ℝ :=
    (16 / (Real.pi * L)) * Set.indicator (Icc (-R) R) (fun _ => (1 : ℝ)) τ +
      (64 * Real.pi / (9 * L ^ 3)) * bohmanTailSq R τ
  have hind : Integrable (Set.indicator (Icc (-R) R) fun _ => (1 : ℝ)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmaj_int : Integrable maj :=
    (hind.const_mul _).add ((integrable_bohmanTailSq hR).const_mul _)
  have hpt : ∀ τ : ℝ, τ ^ 2 * bohmanK L τ ≤ maj τ := fun τ => by
    by_cases hτ : |τ| ≤ R
    · have hmem : τ ∈ Icc (-R) R := abs_le.mp hτ
      have htail0 : bohmanTailSq R τ = 0 := by simp [bohmanTailSq, not_lt.mpr hτ]
      dsimp only [maj]
      rw [Set.indicator_of_mem hmem, htail0, mul_one, mul_zero, add_zero]
      have hτ2 : τ ^ 2 ≤ R ^ 2 := by rw [← sq_abs τ]; exact pow_le_pow_left₀ (abs_nonneg _) hτ 2
      calc τ ^ 2 * bohmanK L τ
          ≤ R ^ 2 * (4 * L / Real.pi ^ 3) :=
            mul_le_mul hτ2 (bohmanK_le hL τ) (bohmanK_nonneg hL τ) (by positivity)
        _ = 16 / (Real.pi * L) := by dsimp only [R]; field_simp [hL.ne', hπ.ne']; ring
    · have hgt : R < |τ| := not_le.mp hτ
      have hnot : τ ∉ Icc (-R) R := fun hm => hτ (abs_le.mpr hm)
      have hτ0 : τ ≠ 0 := by rintro rfl; simp at hgt; linarith
      have htail : bohmanTailSq R τ = (τ ^ 2)⁻¹ := by simp [bohmanTailSq, hgt]
      dsimp only [maj]
      rw [Set.indicator_of_notMem hnot, htail, mul_zero, zero_add]
      calc τ ^ 2 * bohmanK L τ
          ≤ τ ^ 2 * (64 * Real.pi / (9 * L ^ 3 * τ ^ 4)) :=
            mul_le_mul_of_nonneg_left (bohmanK_le_inv_pow_four hL hgt) (sq_nonneg τ)
        _ = 64 * Real.pi / (9 * L ^ 3) * (τ ^ 2)⁻¹ := by field_simp [hL.ne', hτ0]
  have hint_sq : Integrable (fun τ => τ ^ 2 * bohmanK L τ) := by
    have hc := (continuous_pow 2).mul (continuous_bohmanK hL)
    refine hmaj_int.mono' hc.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (bohmanK_nonneg hL τ))]
    exact hpt τ
  refine ⟨hint_sq, (integral_mono hint_sq hmaj_int hpt).trans ?_⟩
  dsimp only [maj]
  rw [integral_add (hind.const_mul _) ((integrable_bohmanTailSq hR).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Icc,
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith),
    integral_bohmanTailSq hR]
  dsimp only [R]
  field_simp [hL.ne', hπ.ne']
  nlinarith [sq_pos_of_pos hL]

/-! ## Laplace transform of the Bohman kernel -/

/-- `∫₀^∞ bohmanFn L u * e^{-x u} du`. -/
def bohmanLaplace (L x : ℝ) : ℝ := ∫ u in Ioi 0, bohmanFn L u * Real.exp (-x * u)

private theorem integrableOn_bohman_mul_exp (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => bohmanFn L u * Real.exp (-x * u)) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  refine Integrable.bdd_mul h (c := 1) (continuous_bohmanFn L).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (bohmanFn_nonneg hL u)]
  exact bohmanFn_le_one hL u

theorem integral_bohmanK_mul_lorentz (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    ∫ τ, bohmanK L τ * (x / (x ^ 2 + τ ^ 2)) = bohmanLaplace L x := by
  have hexp : Integrable (fun u => Real.exp (-x * u)) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  have hswap : Integrable (Function.uncurry fun (τ u : ℝ) =>
      bohmanK L τ * (Real.exp (-x * u) * Real.cos (τ * u)))
      (volume.prod (volume.restrict (Ioi 0))) := by
    refine ((integrable_bohmanK hL).mul_prod hexp).mono' ?_ (ae_of_all _ fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have := continuous_bohmanK hL
      simp only [Function.uncurry_def]; fun_prop
    · simp only [Function.uncurry_def, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (bohmanK_nonneg hL _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
        (bohmanK_nonneg hL _)
  calc ∫ τ, bohmanK L τ * (x / (x ^ 2 + τ ^ 2))
      = ∫ τ, ∫ u in Ioi 0, bohmanK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) := by
        refine integral_congr_ae (ae_of_all _ fun τ => ?_)
        simp only; rw [lorentz_eq_integral hx τ, integral_const_mul]
    _ = ∫ u in Ioi 0, ∫ τ, bohmanK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) :=
        integral_integral_swap hswap
    _ = bohmanLaplace L x := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        have e : ∀ τ, bohmanK L τ * (Real.exp (-x * u) * Real.cos (τ * u)) =
            Real.exp (-x * u) * (bohmanK L τ * Real.cos (u * τ)) := fun τ => by
          rw [mul_comm τ u]; ring
        simp_rw [e]
        rw [integral_const_mul, integral_bohmanK_mul_cos hL, mul_comm]

theorem two_mul_bohmanLaplace_le (hL : 0 < L) {a δ : ℝ} (h1 : 0 < a - δ) (h2 : 0 < a + δ) :
    2 * bohmanLaplace L a ≤ bohmanLaplace L (a - δ) + bohmanLaplace L (a + δ) := by
  have ha : 0 < a := by linarith
  unfold bohmanLaplace
  rw [← integral_add (integrableOn_bohman_mul_exp hL h1) (integrableOn_bohman_mul_exp hL h2),
    ← integral_const_mul]
  refine integral_mono ((integrableOn_bohman_mul_exp hL ha).const_mul 2)
    ((integrableOn_bohman_mul_exp hL h1).add (integrableOn_bohman_mul_exp hL h2)) fun u => ?_
  have hcosh := Real.one_le_cosh (δ * u)
  rw [Real.cosh_eq] at hcosh
  have e1 : Real.exp (-(a - δ) * u) = Real.exp (-a * u) * Real.exp (δ * u) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(a + δ) * u) = Real.exp (-a * u) * Real.exp (-(δ * u)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := mul_le_mul_of_nonneg_left
    (by linarith : (2 : ℝ) ≤ Real.exp (δ * u) + Real.exp (-(δ * u)))
    (mul_nonneg (bohmanFn_nonneg hL u) (Real.exp_pos (-a * u)).le)
  simp only [e1, e2]
  linarith only [h3]

/-- Closed form of the Laplace transform of `bohmanFn`. -/
theorem bohmanLaplace_eq (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    bohmanLaplace L x =
      L ^ 2 * x / (L ^ 2 * x ^ 2 + Real.pi ^ 2) +
        2 * Real.pi ^ 2 * L * (1 + Real.exp (-x * L)) / (L ^ 2 * x ^ 2 + Real.pi ^ 2) ^ 2 := by
  have := Real.pi_pos
  have hsplit : (fun u => bohmanFn L u * Real.exp (-x * u)) =ᵐ[volume.restrict (Ioi 0)]
      Set.indicator (Ioc 0 L) (fun u => bohmanFn L u * Real.exp (-x * u)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
    have hu0 : 0 < u := hu
    by_cases huL : u ≤ L
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 L from ⟨hu0, huL⟩)]
    · rw [Set.indicator_of_notMem (show u ∉ Ioc 0 L from fun hm => huL hm.2)]
      change bohmanFn L u * Real.exp (-x * u) = 0
      rw [bohmanFn_eq_zero hL (by rw [abs_of_pos hu0]; linarith), zero_mul]
  unfold bohmanLaplace
  rw [integral_congr_ae hsplit, setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc 0 L = Ioc 0 L by
      ext u; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto,
    ← intervalIntegral.integral_of_le hL.le]
  have hz_ne : (-(x : ℂ)) ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have hpos : 0 < x ^ 2 + (Real.pi / L) ^ 2 := by positivity
    have hcast : (-(x : ℂ)) ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2 =
        ((x ^ 2 + (Real.pi / L) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have hc := congrArg Complex.re (integral_bohman_cexp_right hL (z := -(x : ℂ)) hz_ne)
  have hlhs : (∫ u in (0 : ℝ)..L, ((bohmanFn L u : ℝ) : ℂ) * cexp (-(x : ℂ) * (u : ℂ))).re =
      ∫ u in (0 : ℝ)..L, bohmanFn L u * Real.exp (-x * u) := by
    have hpt : ∀ u : ℝ, ((bohmanFn L u : ℝ) : ℂ) * cexp (-(x : ℂ) * (u : ℂ)) =
        (((bohmanFn L u * Real.exp (-x * u) : ℝ)) : ℂ) := fun u => by
      have : -(x : ℂ) * (u : ℂ) = ((-x * u : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_exp]; push_cast; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  rw [← hlhs, hc]
  have hrhs : -(-(x : ℂ)) / ((-(x : ℂ)) ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2) +
      2 * ((Real.pi / L : ℝ) : ℂ) ^ 2 * (1 + cexp (-(x : ℂ) * (L : ℂ))) /
        ((L : ℂ) * ((-(x : ℂ)) ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2) ^ 2) =
      ((L ^ 2 * x / (L ^ 2 * x ^ 2 + Real.pi ^ 2) +
        2 * Real.pi ^ 2 * L * (1 + Real.exp (-x * L)) /
          (L ^ 2 * x ^ 2 + Real.pi ^ 2) ^ 2 : ℝ) : ℂ) := by
    have hexp : cexp (-(x : ℂ) * (L : ℂ)) = ((Real.exp (-x * L) : ℝ) : ℂ) := by
      have : -(x : ℂ) * (L : ℂ) = ((-x * L : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_exp]
    rw [hexp]
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    have hden_pos : 0 < L ^ 2 * x ^ 2 + Real.pi ^ 2 := by positivity
    have hden_c : ((L ^ 2 * x ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hden_pos.ne'
    have hd_eq : (-(x : ℂ)) ^ 2 + ((Real.pi / L : ℝ) : ℂ) ^ 2 =
        ((L ^ 2 * x ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) / (L : ℂ) ^ 2 := by
      push_cast; field_simp [hLc]
    rw [hd_eq]
    push_cast
    field_simp [hLc, hden_c]
  rw [hrhs, Complex.ofReal_re]

/-! ## Smoothed prime series and quadratic archimedean majorants -/

/-- The Bohman-smoothed prime cosine series. -/
def bohmanPrimeSum (σ L γ : ℝ) : ℝ :=
  ∑' n : ℕ, primeCoeff σ n * bohmanFn L (Real.log n) * Real.cos (γ * Real.log n)

theorem bohmanPrimeSum_eq_sum (hL : 0 < L) {N : ℕ} (hN : ∀ n, N ≤ n → L ≤ Real.log n)
    (σ γ : ℝ) :
    bohmanPrimeSum σ L γ = ∑ n ∈ Finset.range N,
      primeCoeff σ n * bohmanFn L (Real.log n) * Real.cos (γ * Real.log n) := by
  unfold bohmanPrimeSum
  refine tsum_eq_sum fun n hn => ?_
  have hn' : N ≤ n := by simpa using hn
  have h := hN n hn'
  rw [bohmanFn_eq_zero hL (by rw [abs_of_pos (hL.trans_le h)]; exact h)]
  ring

theorem integral_bohmanK_mul_primeSeries (hL : 0 < L) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    ∫ τ, bohmanK L τ * primeSeries σ (γ + τ) = bohmanPrimeSum σ L γ := by
  have hs := summable_primeCoeff hσ
  have hint (n : ℕ) : Integrable fun τ => bohmanK L τ *
      (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) := by
    refine integrable_bohmanK_mul_bdd hL (by fun_prop) (C := primeCoeff σ n) fun τ => ?_
    rw [abs_mul, abs_of_nonneg (primeCoeff_nonneg σ n)]
    exact mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _)
  have hnorm (n : ℕ) : ∫ τ, ‖bohmanK L τ * (primeCoeff σ n *
      Real.cos ((γ + τ) * Real.log n))‖ ≤ primeCoeff σ n := by
    calc _ ≤ ∫ τ, bohmanK L τ * primeCoeff σ n := by
          refine integral_mono (hint n).norm ((integrable_bohmanK hL).mul_const _) fun τ => ?_
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (bohmanK_nonneg hL τ),
            abs_of_nonneg (primeCoeff_nonneg σ n)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (primeCoeff_nonneg σ n) (Real.abs_cos_le_one _))
            (bohmanK_nonneg hL τ)
      _ = _ := by rw [integral_mul_const, integral_bohmanK hL, one_mul]
  have hsum : Summable fun n : ℕ => ∫ τ, ‖bohmanK L τ * (primeCoeff σ n *
      Real.cos ((γ + τ) * Real.log n))‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm hs
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hmul : ∀ τ, bohmanK L τ * primeSeries σ (γ + τ) =
      ∑' n : ℕ, bohmanK L τ * (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) :=
    fun _ => tsum_mul_left.symm
  simp_rw [hmul]
  rw [← hswap]
  unfold bohmanPrimeSum
  refine tsum_congr fun n => ?_
  have e : ∀ τ, bohmanK L τ * (primeCoeff σ n * Real.cos ((γ + τ) * Real.log n)) =
      primeCoeff σ n * (bohmanK L τ * Real.cos ((γ + τ) * Real.log n)) := fun _ => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_bohmanK_mul_cos_add hL]
  ring

theorem integral_bohmanK_mul_primeSeries_sub (hL : 0 < L) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    ∫ τ, bohmanK L τ * primeSeries σ (γ - τ) = bohmanPrimeSum σ L γ := by
  rw [← integral_bohmanK_mul_primeSeries hL hσ γ,
    ← integral_neg_eq_self (fun τ => bohmanK L τ * primeSeries σ (γ + τ)) volume]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [bohmanK_neg, sub_eq_add_neg]

/-- Global quadratic bound `log(1 + τ⁴ / γ⁴) ≤ 2 τ² / γ²`, eliminating `O(1/γ)` tail loss. -/
private theorem log_one_add_pow_four_le {γ : ℝ} (hγ : 0 < γ) (τ : ℝ) :
    1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4) ≤ τ ^ 2 / (4 * γ ^ 2) := by
  set u : ℝ := τ ^ 2 / γ ^ 2
  have hu0 : 0 ≤ u := by positivity
  have h1 : 1 + τ ^ 4 / γ ^ 4 ≤ (1 + u) ^ 2 := by
    have hu2 : u ^ 2 = τ ^ 4 / γ ^ 4 := by dsimp only [u]; field_simp
    nlinarith [hu0]
  have h2 : (1 + u) ^ 2 ≤ Real.exp (2 * u) := by
    have he := Real.add_one_le_exp u
    rw [add_comm] at he
    calc (1 + u) ^ 2 ≤ Real.exp u ^ 2 := pow_le_pow_left₀ (by positivity) he 2
      _ = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; push_cast; rfl
  have hlog := Real.log_le_log (by positivity) (h1.trans h2)
  rw [Real.log_exp] at hlog
  have hrhs : τ ^ 2 / (4 * γ ^ 2) = u / 4 := by dsimp only [u]; ring
  rw [hrhs]
  linarith

/-- Pole Poisson kernel majorant against `bohmanK` when `4 π < L γ`. -/
private theorem bohmanK_mul_lorentz_le (hL : 0 < L) {x γ τ y : ℝ} (hx : 0 < x) (hγ : 0 < γ)
    (hLγ : 4 * Real.pi < L * γ) (hy : γ - |τ| ≤ |y|) :
    bohmanK L τ * (x / (x ^ 2 + y ^ 2)) ≤ bohmanK L τ * (4 * x / γ ^ 2) +
      (1024 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + y ^ 2)) := by
  have := Real.pi_pos
  have hK := bohmanK_nonneg hL τ
  have hP0 : 0 ≤ x / (x ^ 2 + y ^ 2) := by positivity
  by_cases hτγ : |τ| ≤ γ / 2
  · have hy2 : γ / 2 ≤ |y| := by linarith only [hy, hτγ]
    have hy3 : γ ^ 2 / 4 ≤ y ^ 2 := by
      rw [← sq_abs y]
      nlinarith only [pow_le_pow_left₀ (by positivity : 0 ≤ γ / 2) hy2 2]
    have hle : x / (x ^ 2 + y ^ 2) ≤ 4 * x / γ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_pos hx (sq_pos_of_pos hx), mul_le_mul_of_nonneg_left hy3 hx.le]
    have h3 : 0 ≤ (1024 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + y ^ 2)) := by positivity
    linarith only [mul_le_mul_of_nonneg_left hle hK, h3]
  · have hτ : γ / 2 < |τ| := not_le.mp hτγ
    have hgt : 2 * Real.pi / L < |τ| := by
      have : 2 * Real.pi / L < γ / 2 := by
        rw [div_lt_div_iff₀ hL (by norm_num)]
        linarith
      exact this.trans hτ
    have hτ4 : (γ / 2) ^ 4 ≤ τ ^ 4 := by
      have hsq : (γ / 2) ^ 2 ≤ τ ^ 2 := by
        rw [← sq_abs τ]; exact pow_le_pow_left₀ (by positivity) hτ.le 2
      have := pow_le_pow_left₀ (by positivity) hsq 2
      nlinarith
    have hK4 : bohmanK L τ ≤ 1024 * Real.pi / (9 * L ^ 3 * γ ^ 4) := by
      refine (bohmanK_le_inv_pow_four hL hgt).trans ?_
      have hpos : 0 < 9 * L ^ 3 * (γ / 2) ^ 4 := by positivity
      calc 64 * Real.pi / (9 * L ^ 3 * τ ^ 4)
          ≤ 64 * Real.pi / (9 * L ^ 3 * (γ / 2) ^ 4) :=
            div_le_div_of_nonneg_left (by positivity) hpos
              (mul_le_mul_of_nonneg_left hτ4 (by positivity))
        _ = 1024 * Real.pi / (9 * L ^ 3 * γ ^ 4) := by field_simp [hL.ne', hγ.ne']; ring
    have h2 : 0 ≤ bohmanK L τ * (4 * x / γ ^ 2) := by positivity
    linarith only [mul_le_mul_of_nonneg_right hK4 hP0, h2]

/-! ## The Bohman budget right of `Re s = 1` and at the edge `Re s = 1` -/

/-- Archimedean budget with the Bohman density (`O(1 / (L² γ²))` remainder). -/
def bohmanArchBudget (a L γ : ℝ) : ℝ :=
  1 / 4 * Real.log ((1 + (1 / 2 + a) / 2) ^ 2 + γ ^ 2 / 4) - Real.log Real.pi / 2 +
    1 / (240 * (1 + (1 / 2 + a) / 2) ^ 4) + 4 * (a - 1 / 2) / γ ^ 2 +
    18 / (L ^ 2 * γ ^ 2) + 1200 / (L ^ 3 * γ ^ 4)

private theorem integrable_bohmanK_mul_lorentz (hL : 0 < L) {x : ℝ} (hx : 0 < x) :
    Integrable fun τ => bohmanK L τ * (x / (x ^ 2 + τ ^ 2)) := by
  refine integrable_bohmanK_mul_bdd hL (C := 1 / x) ?_ fun τ => ?_
  · refine Continuous.div (by fun_prop) (by fun_prop) fun _ => by positivity
  · rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hx]
    nlinarith only [sq_nonneg τ, sq_nonneg x]

private theorem shifted_lorentz_bohman {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Integrable (fun τ : ℝ => x / (x ^ 2 + (c + τ) ^ 2)) ∧
      ∫ τ : ℝ, x / (x ^ 2 + (c + τ) ^ 2) = Real.pi := by
  have e : ∀ τ : ℝ, x / (x ^ 2 + (c + τ) ^ 2) = x⁻¹ * ((1 + ((c + τ) / x) ^ 2)⁻¹) := fun τ => by
    have hp : 0 < x ^ 2 + (c + τ) ^ 2 := by positivity
    field_simp
  simp_rw [e]
  refine ⟨((integrable_inv_one_add_sq.comp_div (R := x) hx.ne').comp_add_left c).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add_left_eq_self (fun τ => (1 + (τ / x) ^ 2)⁻¹) c,
    Measure.integral_comp_div (fun v => (1 + v ^ 2)⁻¹) x, integral_univ_inv_one_add_sq,
    abs_of_pos hx, smul_eq_mul]
  field_simp

private theorem pair_le_envelope_bohman {a : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) {σ x δ γ : ℝ} (hσ : σ = 1 / 2 + a) (hx : x = σ - 1)
    (hδ : δ = (q.1 : ℂ).re - 1 / 2) (hγ : (q.1 : ℂ).im = γ) (τ y : ℝ) (hy : y - γ = τ) :
    xiLinePairRe a δ τ ≤ x / (x ^ 2 + y ^ 2) - Real.log Real.pi / 2 +
      1 / 4 * Real.log ((1 + σ / 2) ^ 2 + y ^ 2 / 4) + 1 / (240 * (1 + σ / 2) ^ 4) -
        primeSeries σ y := by
  have hσ1 : 1 < σ := by rw [hσ]; linarith only [ha]
  have hH := xiLinePairRe_le_re_logDeriv_xi ha q hoff y
  rw [hγ, hy, ← hδ, ← hσ] at hH
  have hU := re_logDeriv_xi_le (σ := σ) (y := y) hσ1
  rw [re_logDeriv_riemannZeta_eq hσ1, ← hx] at hU
  linarith only [hH, hU]

/-- **The Bohman budget of an off-line zero** for `a > 1/2`. -/
theorem two_mul_bohmanLaplace_le_of_offLine {a : ℝ} (ha : 1 / 2 < a) (hL : 0 < L)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) {γ : ℝ} (hγq : (q.1 : ℂ).im = γ)
    (hγ1 : 1 ≤ γ) (hLγ : 4 * Real.pi < L * γ)
    (hγ2 : 4 * (1 + (1 / 2 + a) / 2) ^ 2 ≤ γ ^ 2) :
    2 * bohmanLaplace L a ≤ bohmanArchBudget a L γ - bohmanPrimeSum (1 / 2 + a) L γ := by
  have hπ := Real.pi_pos
  have hγ : 0 < γ := by linarith only [hγ1]
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = 1 / 2 + a := ⟨_, rfl⟩
  have hσ : 1 < σ := by rw [hσdef]; linarith only [ha]
  obtain ⟨x, hxdef⟩ : ∃ x, x = σ - 1 := ⟨_, rfl⟩
  have hx : 0 < x := by rw [hxdef]; linarith only [hσ]
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = (q.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  have hq0 := xiZeroCopy_re_pos q
  have hq1 := xiZeroCopy_re_lt_one q
  have hd1 : 0 < a - δ := by rw [hδdef]; linarith only [ha, hq1]
  have hd2 : 0 < a + δ := by rw [hδdef]; linarith only [ha, hq0]
  obtain ⟨C2, hC2⟩ : ∃ C2, C2 = (1 + σ / 2) ^ 2 := ⟨_, rfl⟩
  have hC20 : 0 < C2 := by rw [hC2]; positivity
  have hC4 : 4 * C2 ≤ γ ^ 2 := by rw [hC2, hσdef]; exact hγ2
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, ε₀ = 1 / (240 * (1 + σ / 2) ^ 4) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 1 / 4 * Real.log (C2 + γ ^ 2 / 4) - Real.log Real.pi / 2 + ε₀ +
      4 * x / γ ^ 2 := ⟨_, rfl⟩
  have hpair_eq : ∀ u : ℝ, xiLinePairRe a δ u =
      (a - δ) / ((a - δ) ^ 2 + u ^ 2) + (a + δ) / ((a + δ) ^ 2 + u ^ 2) := fun _ => rfl
  have hpair_neg : ∀ u : ℝ, xiLinePairRe a δ (-u) = xiLinePairRe a δ u := fun u => by
    simp only [hpair_eq, neg_sq]
  have hleft : 2 * bohmanLaplace L a ≤ ∫ τ, bohmanK L τ * xiLinePairRe a δ τ := by
    simp_rw [hpair_eq, mul_add]
    rw [integral_add (integrable_bohmanK_mul_lorentz hL hd1) (integrable_bohmanK_mul_lorentz hL hd2),
      integral_bohmanK_mul_lorentz hL hd1, integral_bohmanK_mul_lorentz hL hd2]
    exact two_mul_bohmanLaplace_le hL hd1 hd2
  have hLHSint : Integrable fun τ => bohmanK L τ * xiLinePairRe a δ τ := by
    simp_rw [hpair_eq, mul_add]
    exact (integrable_bohmanK_mul_lorentz hL hd1).add (integrable_bohmanK_mul_lorentz hL hd2)
  have hS1 : Integrable fun τ => bohmanK L τ * primeSeries σ (γ + τ) :=
    integrable_bohmanK_mul_bdd hL ((continuous_primeSeries hσ).comp (by fun_prop))
      (C := ∑' n, primeCoeff σ n) fun _ => abs_primeSeries_le hσ _
  have hS2 : Integrable fun τ => bohmanK L τ * primeSeries σ (γ - τ) :=
    integrable_bohmanK_mul_bdd hL ((continuous_primeSeries hσ).comp (by fun_prop))
      (C := ∑' n, primeCoeff σ n) fun _ => abs_primeSeries_le hσ _
  have hK0 : Integrable fun τ => bohmanK L τ * B₀ := (integrable_bohmanK hL).mul_const _
  obtain ⟨hsq_int, hsq_le⟩ := integrable_and_integral_sq_mul_bohmanK_le hL
  have hL1 := (shifted_lorentz_bohman hx γ).1
  have hL2 := (shifted_lorentz_bohman hx γ).2
  have hL3 : Integrable fun τ : ℝ => x / (x ^ 2 + (γ - τ) ^ 2) :=
    hL1.comp_neg.congr (ae_of_all _ fun _ => by simp only [sub_eq_add_neg])
  have hL4 : ∫ τ : ℝ, x / (x ^ 2 + (γ - τ) ^ 2) = Real.pi := by
    rw [← hL2, ← integral_neg_eq_self (fun τ : ℝ => x / (x ^ 2 + (γ + τ) ^ 2)) volume]
    exact integral_congr_ae (ae_of_all _ fun _ => by simp only [sub_eq_add_neg])
  let Maj : ℝ → ℝ := fun τ =>
    (bohmanK L τ * B₀ - 1 / 2 * (bohmanK L τ * primeSeries σ (γ + τ)) -
      1 / 2 * (bohmanK L τ * primeSeries σ (γ - τ))) +
    (1 / (4 * γ ^ 2)) * (τ ^ 2 * bohmanK L τ) +
    ((512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + (γ + τ) ^ 2)) +
      (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + (γ - τ) ^ 2)))
  have h1 : Integrable fun τ => bohmanK L τ * B₀ - 1 / 2 * (bohmanK L τ * primeSeries σ (γ + τ)) :=
    hK0.sub (hS1.const_mul (1 / 2))
  have h2 : Integrable fun τ =>
      bohmanK L τ * B₀ - 1 / 2 * (bohmanK L τ * primeSeries σ (γ + τ)) -
        1 / 2 * (bohmanK L τ * primeSeries σ (γ - τ)) :=
    h1.sub (hS2.const_mul (1 / 2))
  have h3 : Integrable fun τ =>
      (bohmanK L τ * B₀ - 1 / 2 * (bohmanK L τ * primeSeries σ (γ + τ)) -
        1 / 2 * (bohmanK L τ * primeSeries σ (γ - τ))) +
        (1 / (4 * γ ^ 2)) * (τ ^ 2 * bohmanK L τ) :=
    h2.add (hsq_int.const_mul (1 / (4 * γ ^ 2)))
  have h4 : Integrable fun τ =>
      (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + (γ + τ) ^ 2)) +
        (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * (x / (x ^ 2 + (γ - τ) ^ 2)) :=
    (hL1.const_mul (512 * Real.pi / (9 * L ^ 3 * γ ^ 4))).add
      (hL3.const_mul (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)))
  have hMajInt : Integrable Maj := h3.add h4
  have hpoint : ∀ τ, bohmanK L τ * xiLinePairRe a δ τ ≤ Maj τ := fun τ => by
    have hK := bohmanK_nonneg hL τ
    have hp := pair_le_envelope_bohman ha q hoff hσdef hxdef hδdef hγq τ (γ + τ) (by ring)
    have hm := pair_le_envelope_bohman ha q hoff hσdef hxdef hδdef hγq (-τ) (γ - τ) (by ring)
    rw [hpair_neg] at hm
    rw [← hC2, ← hε₀] at hp hm
    have hlogp := log_pair_le (τ := τ) hC20 hγ hC4
    have hlog_q := mul_le_mul_of_nonneg_left (log_one_add_pow_four_le hγ τ) hK
    have hl1 := bohmanK_mul_lorentz_le hL (τ := τ) (y := γ + τ) hx hγ hLγ (by
      have := abs_sub_abs_le_abs_sub γ (-τ)
      rwa [abs_neg, sub_neg_eq_add, abs_of_pos hγ] at this)
    have hl2 := bohmanK_mul_lorentz_le hL (τ := τ) (y := γ - τ) hx hγ hLγ (by
      have := abs_sub_abs_le_abs_sub γ τ
      rwa [abs_of_pos hγ] at this)
    have hmean : xiLinePairRe a δ τ ≤ 1 / 2 * (x / (x ^ 2 + (γ + τ) ^ 2)) +
        1 / 2 * (x / (x ^ 2 + (γ - τ) ^ 2)) - Real.log Real.pi / 2 + ε₀ -
        1 / 2 * primeSeries σ (γ + τ) - 1 / 2 * primeSeries σ (γ - τ) +
        1 / 4 * Real.log (C2 + γ ^ 2 / 4) + 1 / 8 * Real.log (1 + τ ^ 4 / γ ^ 4) := by
      linarith only [hp, hm, hlogp]
    have hstep := mul_le_mul_of_nonneg_left hmean hK
    have e512 : 512 * Real.pi / (9 * L ^ 3 * γ ^ 4) =
        1 / 2 * (1024 * Real.pi / (9 * L ^ 3 * γ ^ 4)) := by ring
    have eq_sq : bohmanK L τ * (τ ^ 2 / (4 * γ ^ 2)) =
        (1 / (4 * γ ^ 2)) * (τ ^ 2 * bohmanK L τ) := by ring
    rw [eq_sq] at hlog_q
    dsimp only [Maj]
    rw [hB₀, e512]
    generalize bohmanK L τ = A at *
    generalize x / (x ^ 2 + (γ + τ) ^ 2) = P₁ at *
    generalize x / (x ^ 2 + (γ - τ) ^ 2) = P₂ at *
    generalize 4 * x / γ ^ 2 = D at *
    generalize 1024 * Real.pi / (9 * L ^ 3 * γ ^ 4) = F at *
    linarith only [hstep, hlog_q, hl1, hl2]
  have hMaj_le : ∫ τ, Maj τ ≤ B₀ - bohmanPrimeSum σ L γ +
      18 / (L ^ 2 * γ ^ 2) + 1200 / (L ^ 3 * γ ^ 4) := by
    dsimp only [Maj]
    rw [integral_add h3 h4, integral_add h2 (hsq_int.const_mul _),
      integral_sub h1 (hS2.const_mul _), integral_sub hK0 (hS1.const_mul _),
      integral_add (hL1.const_mul _) (hL3.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_mul_const, integral_bohmanK hL, integral_bohmanK_mul_primeSeries hL hσ,
      integral_bohmanK_mul_primeSeries_sub hL hσ, hL2, hL4]
    have hsq_term : (1 / (4 * γ ^ 2)) * ∫ τ, τ ^ 2 * bohmanK L τ ≤ 18 / (L ^ 2 * γ ^ 2) := by
      calc (1 / (4 * γ ^ 2)) * ∫ τ, τ ^ 2 * bohmanK L τ
          ≤ (1 / (4 * γ ^ 2)) * (72 / L ^ 2) :=
            mul_le_mul_of_nonneg_left hsq_le (by positivity)
        _ = 18 / (L ^ 2 * γ ^ 2) := by field_simp [hL.ne', hγ.ne']; ring
    have hpole_term : (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * Real.pi +
        (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * Real.pi ≤ 1200 / (L ^ 3 * γ ^ 4) := by
      have hπ_lt : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
      have hπ2 : Real.pi ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ hπ.le hπ_lt 2
      have hnum : 1024 * Real.pi ^ 2 ≤ 9 * 1200 := by nlinarith only [hπ2]
      calc (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * Real.pi +
            (512 * Real.pi / (9 * L ^ 3 * γ ^ 4)) * Real.pi
          = (1024 * Real.pi ^ 2) / (9 * L ^ 3 * γ ^ 4) := by field_simp [hL.ne', hγ.ne']; ring
        _ ≤ (9 * 1200) / (9 * L ^ 3 * γ ^ 4) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = 1200 / (L ^ 3 * γ ^ 4) := by field_simp [hL.ne', hγ.ne']
    linarith only [hsq_term, hpole_term]
  have hfinal := (hleft.trans (integral_mono hLHSint hMajInt hpoint)).trans hMaj_le
  rw [hB₀] at hfinal
  unfold bohmanArchBudget
  rw [← hσdef, ← hC2, ← hε₀]
  have hx_eq : 4 * (a - 1 / 2) / γ ^ 2 = 4 * x / γ ^ 2 := by rw [hxdef, hσdef]; ring
  rw [hx_eq]
  linarith only [hfinal]

private theorem continuousAt_primeCoeff_edge (n : ℕ) :
    ContinuousAt (fun a : ℝ => primeCoeff (1 / 2 + a) n) (1 / 2) := by
  by_cases hn : n = 0
  · subst hn; simp only [primeCoeff, ArithmeticFunction.map_zero, zero_mul]; exact continuousAt_const
  · unfold primeCoeff
    refine continuousAt_const.mul ?_
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact (Real.continuous_const_rpow hn0).continuousAt.comp (f := fun a : ℝ => -(1 / 2 + a))
      (by fun_prop)

private theorem primeCoeff_edge_one (n : ℕ) : primeCoeff (1 / 2 + 1 / 2) n = vonMangoldt n / n := by
  unfold primeCoeff
  rw [show -(1 / 2 + 1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv]

/-- **The Bohman budget on the line `Re s = 1` (`a = 1/2`).** -/
theorem bohman_budget_at_edge {N : ℕ} (hL : 0 < L) (hN : ∀ n, N ≤ n → L ≤ Real.log n)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) {γ : ℝ} (hγq : (q.1 : ℂ).im = γ)
    (hγ4 : 4 ≤ γ) (hLγ : 4 * Real.pi < L * γ) :
    4 * L ^ 2 / (L ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * L * (1 + Real.exp (-(L / 2))) / (L ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤
      1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
        18 / (L ^ 2 * γ ^ 2) + 1200 / (L ^ 3 * γ ^ 4) -
        ∑ n ∈ Finset.range N, vonMangoldt n / n * bohmanFn L (Real.log n) *
          Real.cos (γ * Real.log n) := by
  have := Real.pi_pos
  have : 0 < γ := by linarith only [hγ4]
  let lapEdge (a : ℝ) : ℝ :=
    L ^ 2 * a / (L ^ 2 * a ^ 2 + Real.pi ^ 2) +
      2 * Real.pi ^ 2 * L * (1 + Real.exp (-a * L)) / (L ^ 2 * a ^ 2 + Real.pi ^ 2) ^ 2
  let F : ℝ → ℝ := fun a =>
    bohmanArchBudget a L γ - ∑ n ∈ Finset.range N, primeCoeff (1 / 2 + a) n *
      bohmanFn L (Real.log n) * Real.cos (γ * Real.log n) - 2 * lapEdge a
  have hF : ∀ᶠ a in 𝓝[>] (1 / 2 : ℝ), 0 ≤ F a := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with a ha
    have ha0 : 0 < a := by linarith only [ha.1]
    have h2 : 4 * (1 + (1 / 2 + a) / 2) ^ 2 ≤ γ ^ 2 := by
      have h3 : 1 + (1 / 2 + a) / 2 ≤ 2 := by linarith only [ha.2]
      have h4 : 0 ≤ 1 + (1 / 2 + a) / 2 := by linarith only [ha0]
      nlinarith only [h3, h4, hγ4]
    have h := two_mul_bohmanLaplace_le_of_offLine ha.1 hL q hoff hγq (by linarith only [hγ4]) hLγ h2
    rw [bohmanPrimeSum_eq_sum hL hN, bohmanLaplace_eq hL ha0] at h
    dsimp only [F, lapEdge]
    linarith only [h]
  have hcont : ContinuousAt F (1 / 2) := by
    have h1 : ContinuousAt (fun a : ℝ => bohmanArchBudget a L γ) (1 / 2) := by
      unfold bohmanArchBudget
      have h2 : ContinuousAt (fun a : ℝ => Real.log ((1 + (1 / 2 + a) / 2) ^ 2 + γ ^ 2 / 4)) (1 / 2) :=
        ContinuousAt.log
          (by fun_prop : Continuous fun a : ℝ => (1 + (1 / 2 + a) / 2) ^ 2 + γ ^ 2 / 4).continuousAt
          (by positivity)
      have h3 : ContinuousAt (fun a : ℝ => 1 / (240 * (1 + (1 / 2 + a) / 2) ^ 4)) (1 / 2) :=
        ContinuousAt.div continuousAt_const
          (by fun_prop : Continuous fun a : ℝ => 240 * (1 + (1 / 2 + a) / 2) ^ 4).continuousAt
          (by norm_num)
      have h4 : ContinuousAt (fun a : ℝ => 4 * (a - 1 / 2) / γ ^ 2) (1 / 2) :=
        (by fun_prop : Continuous fun a : ℝ => 4 * (a - 1 / 2) / γ ^ 2).continuousAt
      exact ((((((continuousAt_const.mul h2).sub continuousAt_const).add h3).add h4).add
        continuousAt_const).add continuousAt_const)
    have h5 : ContinuousAt (fun a : ℝ => ∑ n ∈ Finset.range N, primeCoeff (1 / 2 + a) n *
        bohmanFn L (Real.log n) * Real.cos (γ * Real.log n)) (1 / 2) := by
      refine tendsto_finsetSum _ fun n _ => ?_
      exact ((continuousAt_primeCoeff_edge n).mul continuousAt_const).mul continuousAt_const
    have h6 : ContinuousAt lapEdge (1 / 2) := by
      dsimp only [lapEdge]
      have hd_ne : L ^ 2 * (1 / 2 : ℝ) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
      exact (ContinuousAt.div
          (by fun_prop : Continuous fun a : ℝ => L ^ 2 * a).continuousAt
          (by fun_prop : Continuous fun a : ℝ => L ^ 2 * a ^ 2 + Real.pi ^ 2).continuousAt
          hd_ne).add
        (ContinuousAt.div
          (by fun_prop : Continuous fun a : ℝ => 2 * Real.pi ^ 2 * L * (1 + Real.exp (-a * L))).continuousAt
          (by fun_prop : Continuous fun a : ℝ => (L ^ 2 * a ^ 2 + Real.pi ^ 2) ^ 2).continuousAt
          (pow_ne_zero 2 hd_ne))
    exact (h1.sub h5).sub (continuousAt_const.mul h6)
  have hlim := ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hF
  dsimp only [F, lapEdge] at hlim
  have e1 : bohmanArchBudget (1 / 2) L γ = 1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) -
      Real.log Real.pi / 2 + 1 / 1215 + 18 / (L ^ 2 * γ ^ 2) + 1200 / (L ^ 3 * γ ^ 4) := by
    unfold bohmanArchBudget; norm_num
  have e2 : 2 * (L ^ 2 * (1 / 2) / (L ^ 2 * (1 / 2) ^ 2 + Real.pi ^ 2) +
        2 * Real.pi ^ 2 * L * (1 + Real.exp (-(1 / 2 : ℝ) * L)) /
          (L ^ 2 * (1 / 2) ^ 2 + Real.pi ^ 2) ^ 2) =
      4 * L ^ 2 / (L ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * L * (1 + Real.exp (-(L / 2))) / (L ^ 2 + 4 * Real.pi ^ 2) ^ 2 := by
    have hd1 : L ^ 2 * (1 / 2 : ℝ) ^ 2 + Real.pi ^ 2 ≠ 0 := by positivity
    have hd2 : L ^ 2 + 4 * Real.pi ^ 2 ≠ 0 := by positivity
    rw [show -(1 / 2 : ℝ) * L = -(L / 2) by ring]
    field_simp [hd1, hd2]
    ring
  rw [e1, e2] at hlim
  simp_rw [primeCoeff_edge_one] at hlim
  linarith only [hlim]

#print axioms bohman_budget_at_edge

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
