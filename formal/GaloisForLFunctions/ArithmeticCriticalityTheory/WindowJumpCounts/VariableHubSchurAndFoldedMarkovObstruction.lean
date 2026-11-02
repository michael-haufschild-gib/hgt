import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.EvenSectorPoleCalibration

/-!
# Variable-hub Schur squares, `T₂`-stick elimination, and the folded-Markov corner obstruction

On an even window `[−a, a]` past the plastic threshold `log ρ ≈ 0.2812` (`ρ³ = ρ + 1`), the folded
archimedean-minus-pole jump conductance `ω(|x − y|) + ω(x + y) − 4 cosh(x/2) cosh(y/2)` ceases to be
pointwise nonnegative, and near the window edge `x ≈ a` the gauge potential turns negative. This
module proves both the positive sum-of-squares mechanisms that absorb negative edge potentials and
the sharp corner obstruction showing that non-local inter-point squares are forced:

1. **Variable-hub Schur squares and harmonic-mean hub reduction**:
   `variableHub_pointwise_sq_eq` and `integral_variableHub_sq_eq` complete the square between a
   hub jump `w(x)(u(x) − ū)²` and a signed potential `p(x) u(x)²`, yielding a manifest square plus
   the Schur scalar `(w p / (w + p)) ū²` whenever `w + p > 0`. `harmonicHub_jump_ge_hubMean_sq`
   derives the continuous hub weight `w(x) = m_Z² / ∫_Z (M(z)/K(x, z)) dz` directly from positive
   two-point conductances `K(x, z) > 0` on a hub `Z`.
2. **Coupled 2-vertex `T₂`-stick elimination**:
   On `log 2 < 2a ≤ log 3`, each edge point `x₂ ∈ [log 2 − a, a]` is paired with its `T₂`-mirror
   `x₁ = log 2 − x₂` near the origin by the `T₂`-graph jump `g₁₂ (u₁ − u₂)²`. `twoVertexStick_sq_eq`
   resolves `p₁ u₁² + w₁(u₁ − ū)² + p₂ u₂² + w₂(u₂ − ū)² + g₁₂(u₁ − u₂)²` into three manifest
   squares even when `p₂ + w₂ < 0`, provided `d₁ = p₁ + w₁ + g₁₂ > 0` and `d₁ d₂ − g₁₂² > 0`.
3. **Exact folded-Markov corner ceiling and closed radical obstructions at `log 2` and `log 3`**:
   For any `c₀`-calibrated folded jump conductance
   `ω(|x − y|) + ω(x + y) − c₀ cosh(x/2) cosh(y/2)`, pointwise nonnegativity on `0 < x < y < a`
   forces `c₀ ≤ cornerCeiling a = 2 ω(a) / cosh(a/2)` at `(x, y) → (0⁺, a⁻)`
   (`le_cornerCeiling_of_foldedCalibratedConductance_nonneg`). At the first two prime thresholds,
   - `cornerCeiling (log 2 / 2) = 8(√2 − 1) < 4` (`cornerCeiling_half_log_two`),
   - `cornerCeiling (log 3 / 2) = 3(√3 − 1) < 4` (`cornerCeiling_half_log_three`),
   so full pole calibration (`c₀ = 4`, i.e. `weilJumpDensity`) fails strictly inside `(0, a)²`
   for every `a` past the plastic root `e^{−2a} + e^{−3a} = 1`, including `a = ½ log 2` and
   `a = ½ log 3`. On the Doob ground state `Φ`, `phiDoob_halfLine_coshMass_split` establishes the
   matching exterior leakage identity `∫_{(0, a]} Φ cosh(x/2) + ∫_{(a, ∞)} Φ cosh(x/2) = 1/4`.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticCriticalityTheory.WindowJumpCounts

open GaloisForLFunctions.ArithmeticCriticalityTheory
open _root_.RHTower _root_.RHTower.CHMDPolar

/-! ### 1. Variable-hub Schur completion and harmonic-mean hub Cauchy–Schwarz -/

/-- Pointwise completion of the square for a hub jump `w (u − ū)²` plus a signed potential `p u²`. -/
theorem variableHub_pointwise_sq_eq {w p : ℝ} (hwp : w + p ≠ 0) (u uBar : ℝ) :
    w * (u - uBar) ^ 2 + p * u ^ 2 =
      (w + p) * (u - w * uBar / (w + p)) ^ 2 + (w * p / (w + p)) * uBar ^ 2 := by
  field_simp [hwp]
  ring

/-- When `w + p > 0`, a signed potential `p u²` (even with `p < 0`) plus the hub jump `w (u − ū)²`
is bounded below by the Schur complement `(w p / (w + p)) ū²`. -/
theorem variableHub_pointwise_ge_schur {w p : ℝ} (hwp : 0 < w + p) (u uBar : ℝ) :
    (w * p / (w + p)) * uBar ^ 2 ≤ w * (u - uBar) ^ 2 + p * u ^ 2 := by
  rw [variableHub_pointwise_sq_eq hwp.ne']
  have hsq : 0 ≤ (w + p) * (u - w * uBar / (w + p)) ^ 2 :=
    mul_nonneg hwp.le (sq_nonneg _)
  linarith

/-- Integral form of the variable-hub sum-of-squares identity against a gauge weight `M`. -/
theorem integral_variableHub_sq_eq {X : Set ℝ} (hX : MeasurableSet X)
    {M w p u : ℝ → ℝ} (uBar : ℝ) (hwp : ∀ x ∈ X, w x + p x ≠ 0)
    (i_sq : IntegrableOn
      (fun x => M x * ((w x + p x) * (u x - w x * uBar / (w x + p x)) ^ 2)) X)
    (i_schur : IntegrableOn (fun x => M x * (w x * p x / (w x + p x))) X) :
    (∫ x in X, M x * (w x * (u x - uBar) ^ 2 + p x * u x ^ 2)) =
      (∫ x in X, M x * ((w x + p x) * (u x - w x * uBar / (w x + p x)) ^ 2)) +
        (∫ x in X, M x * (w x * p x / (w x + p x))) * uBar ^ 2 := by
  rw [← integral_mul_const, ← integral_add i_sq (i_schur.mul_const (uBar ^ 2))]
  refine setIntegral_congr_fun hX fun x hx => ?_
  dsimp only
  rw [variableHub_pointwise_sq_eq (hwp x hx)]
  ring

/-- Discriminant inequality for a nonnegative scalar quadratic `A t² + 2 B t + C ≥ 0`. -/
theorem sq_le_mul_of_quad_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (hq : ∀ t : ℝ, 0 ≤ A * t ^ 2 + 2 * B * t + C) : B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hA with rfl | hApos
  · by_cases hB : B = 0
    · simp [hB]
    · exfalso
      have h := hq (-(C + 1) / (2 * B))
      have hsimp : 0 * (-(C + 1) / (2 * B)) ^ 2 + 2 * B * (-(C + 1) / (2 * B)) + C = -1 := by
        field_simp [hB]; ring
      linarith
  · have h := hq (-B / A)
    have hmul := mul_nonneg hApos.le h
    have hsimp : A * (A * (-B / A) ^ 2 + 2 * B * (-B / A) + C) = A * C - B ^ 2 := by
      field_simp [hApos.ne']; ring
    linarith

/-- Continuous harmonic-mean Cauchy–Schwarz on a hub `Z`:
`(∫_Z M(z) (u_x − u(z)) dz)² ≤ (∫_Z M(z)/K(z) dz) (∫_Z K(z) M(z) (u_x − u(z))² dz)`. -/
theorem harmonicHub_cauchy_schwarz {Z : Set ℝ} (hZ : MeasurableSet Z)
    {M K u : ℝ → ℝ} (ux : ℝ) (hM : ∀ z ∈ Z, 0 ≤ M z) (hK : ∀ z ∈ Z, 0 < K z)
    (i_inv : IntegrableOn (fun z => M z / K z) Z)
    (i_lin : IntegrableOn (fun z => M z * (ux - u z)) Z)
    (i_quad : IntegrableOn (fun z => K z * M z * (ux - u z) ^ 2) Z) :
    (∫ z in Z, M z * (ux - u z)) ^ 2 ≤
      (∫ z in Z, M z / K z) * (∫ z in Z, K z * M z * (ux - u z) ^ 2) := by
  have hA : 0 ≤ ∫ z in Z, M z / K z :=
    setIntegral_nonneg hZ fun z hz => div_nonneg (hM z hz) (hK z hz).le
  refine sq_le_mul_of_quad_nonneg hA fun t => ?_
  have i1 : IntegrableOn (fun z => (M z / K z) * t ^ 2) Z := i_inv.mul_const (t ^ 2)
  have i2 : IntegrableOn (fun z => 2 * (M z * (ux - u z)) * t) Z := (i_lin.const_mul 2).mul_const t
  have hsum : (∫ z in Z, M z / K z) * t ^ 2 + 2 * (∫ z in Z, M z * (ux - u z)) * t +
      (∫ z in Z, K z * M z * (ux - u z) ^ 2) =
      ∫ z in Z, ((M z / K z) * t ^ 2 + 2 * (M z * (ux - u z)) * t + K z * M z * (ux - u z) ^ 2) := by
    rw [← integral_mul_const, ← integral_const_mul, ← integral_mul_const,
      ← integral_add i1 i2, ← integral_add (i1.add i2) i_quad]
    rfl
  rw [hsum]
  refine setIntegral_nonneg hZ fun z hz => ?_
  have hKz : K z ≠ 0 := (hK z hz).ne'
  have hpt : (M z / K z) * t ^ 2 + 2 * (M z * (ux - u z)) * t + K z * M z * (ux - u z) ^ 2 =
      (M z / K z) * (t + K z * (ux - u z)) ^ 2 := by
    field_simp [hKz]; ring
  rw [hpt]
  exact mul_nonneg (div_nonneg (hM z hz) (hK z hz).le) (sq_nonneg _)

/-- **Harmonic-mean hub jump bound.** Integrating two-point jumps `K(z) M(z) (u_x − u(z))²` over a
hub `Z` of mass `m_Z = ∫_Z M > 0` yields at least `(m_Z² / ∫_Z (M/K)) (u_x − ū)²`, where
`ū = (∫_Z M u) / m_Z`. -/
theorem harmonicHub_jump_ge_hubMean_sq {Z : Set ℝ} (hZ : MeasurableSet Z)
    {M K u : ℝ → ℝ} (ux : ℝ) (hM : ∀ z ∈ Z, 0 ≤ M z) (hK : ∀ z ∈ Z, 0 < K z)
    (i_M : IntegrableOn M Z) (i_Mu : IntegrableOn (fun z => M z * u z) Z)
    (i_inv : IntegrableOn (fun z => M z / K z) Z)
    (i_quad : IntegrableOn (fun z => K z * M z * (ux - u z) ^ 2) Z)
    (hmZ : 0 < ∫ z in Z, M z) (hinv_pos : 0 < ∫ z in Z, M z / K z) :
    ((∫ z in Z, M z) ^ 2 / (∫ z in Z, M z / K z)) *
        (ux - (∫ z in Z, M z * u z) / (∫ z in Z, M z)) ^ 2 ≤
      ∫ z in Z, K z * M z * (ux - u z) ^ 2 := by
  have i_lin : IntegrableOn (fun z => M z * (ux - u z)) Z := by
    have : (fun z => M z * (ux - u z)) = fun z => M z * ux - M z * u z :=
      funext fun z => by ring
    rw [this]
    exact (i_M.mul_const ux).sub i_Mu
  have hcs := harmonicHub_cauchy_schwarz hZ ux hM hK i_inv i_lin i_quad
  have hlin_eq : (∫ z in Z, M z * (ux - u z)) =
      (∫ z in Z, M z) * (ux - (∫ z in Z, M z * u z) / (∫ z in Z, M z)) := by
    have hpt : (fun z => M z * (ux - u z)) = fun z => M z * ux - M z * u z :=
      funext fun z => by ring
    rw [hpt, integral_sub (i_M.mul_const ux) i_Mu, integral_mul_const]
    field_simp [hmZ.ne']
    ring
  rw [hlin_eq] at hcs
  rw [div_mul_eq_mul_div, div_le_iff₀ hinv_pos]
  linarith [hcs]

/-! ### 2. Coupled 2-vertex `T₂`-stick Gaussian elimination -/

/-- First diagonal pivot `p₁ + w₁ + g₁₂` of a `T₂`-coupled pair `(u₁, u₂)`. -/
def stickDiag1 (p₁ w₁ g₁₂ : ℝ) : ℝ := p₁ + w₁ + g₁₂

/-- Second diagonal entry `p₂ + w₂ + g₁₂` of a `T₂`-coupled pair `(u₁, u₂)`. -/
def stickDiag2 (p₂ w₂ g₁₂ : ℝ) : ℝ := p₂ + w₂ + g₁₂

/-- `2 × 2` stick determinant `(p₁ + w₁ + g₁₂)(p₂ + w₂ + g₁₂) − g₁₂²`. -/
def stickDet (p₁ p₂ w₁ w₂ g₁₂ : ℝ) : ℝ :=
  stickDiag1 p₁ w₁ g₁₂ * stickDiag2 p₂ w₂ g₁₂ - g₁₂ ^ 2

/-- Numerator `(p₁ p₂ + g₁₂(p₁ + p₂))(w₁ + w₂) + (p₁ + p₂) w₁ w₂` of the stick Schur complement. -/
def stickSchurNum (p₁ p₂ w₁ w₂ g₁₂ : ℝ) : ℝ :=
  (p₁ * p₂ + g₁₂ * (p₁ + p₂)) * (w₁ + w₂) + (p₁ + p₂) * w₁ * w₂

theorem stickDet_eq (p₁ p₂ w₁ w₂ g₁₂ : ℝ) :
    stickDet p₁ p₂ w₁ w₂ g₁₂ = (p₁ + w₁) * (p₂ + w₂) + g₁₂ * (p₁ + p₂ + w₁ + w₂) := by
  unfold stickDet stickDiag1 stickDiag2
  ring

/-- **Exact 3-square elimination of a `T₂`-coupled pair.**
For any potentials `p₁, p₂` (allowing `p₂ + w₂ < 0` at the outer endpoint), hub weights `w₁, w₂`,
and `T₂`-bridge conductance `g₁₂` with nonzero pivots `d₁ ≠ 0` and `Δ ≠ 0`, the 2-vertex block
decomposes into two elimination squares plus the exact Schur scalar `(stickSchurNum / Δ) ū²`. -/
theorem twoVertexStick_sq_eq {p₁ p₂ w₁ w₂ g₁₂ : ℝ}
    (hd₁ : stickDiag1 p₁ w₁ g₁₂ ≠ 0) (hΔ : stickDet p₁ p₂ w₁ w₂ g₁₂ ≠ 0)
    (u₁ u₂ uBar : ℝ) :
    p₁ * u₁ ^ 2 + w₁ * (u₁ - uBar) ^ 2 + p₂ * u₂ ^ 2 + w₂ * (u₂ - uBar) ^ 2 +
        g₁₂ * (u₁ - u₂) ^ 2 =
      stickDiag1 p₁ w₁ g₁₂ *
          (u₁ - (g₁₂ * u₂ + w₁ * uBar) / stickDiag1 p₁ w₁ g₁₂) ^ 2 +
        (stickDet p₁ p₂ w₁ w₂ g₁₂ / stickDiag1 p₁ w₁ g₁₂) *
          (u₂ - (stickDiag1 p₁ w₁ g₁₂ * w₂ + g₁₂ * w₁) * uBar /
            stickDet p₁ p₂ w₁ w₂ g₁₂) ^ 2 +
        (stickSchurNum p₁ p₂ w₁ w₂ g₁₂ / stickDet p₁ p₂ w₁ w₂ g₁₂) * uBar ^ 2 := by
  set d₁ := stickDiag1 p₁ w₁ g₁₂
  set Δ := stickDet p₁ p₂ w₁ w₂ g₁₂
  have hd₁' : d₁ ≠ 0 := hd₁
  have hΔ' : Δ ≠ 0 := hΔ
  field_simp [hd₁', hΔ']
  unfold d₁ Δ stickDiag1 stickDet stickDiag2 stickSchurNum
  ring

/-- Positivity of the two elimination pivots bounds the `T₂`-coupled pair below by its Schur
complement `(stickSchurNum / stickDet) ū²`. -/
theorem twoVertexStick_ge_schur {p₁ p₂ w₁ w₂ g₁₂ : ℝ}
    (hd₁ : 0 < stickDiag1 p₁ w₁ g₁₂) (hΔ : 0 < stickDet p₁ p₂ w₁ w₂ g₁₂)
    (u₁ u₂ uBar : ℝ) :
    (stickSchurNum p₁ p₂ w₁ w₂ g₁₂ / stickDet p₁ p₂ w₁ w₂ g₁₂) * uBar ^ 2 ≤
      p₁ * u₁ ^ 2 + w₁ * (u₁ - uBar) ^ 2 + p₂ * u₂ ^ 2 + w₂ * (u₂ - uBar) ^ 2 +
        g₁₂ * (u₁ - u₂) ^ 2 := by
  rw [twoVertexStick_sq_eq hd₁.ne' hΔ.ne']
  have hs1 : 0 ≤ stickDiag1 p₁ w₁ g₁₂ *
      (u₁ - (g₁₂ * u₂ + w₁ * uBar) / stickDiag1 p₁ w₁ g₁₂) ^ 2 :=
    mul_nonneg hd₁.le (sq_nonneg _)
  have hs2 : 0 ≤ (stickDet p₁ p₂ w₁ w₂ g₁₂ / stickDiag1 p₁ w₁ g₁₂) *
      (u₂ - (stickDiag1 p₁ w₁ g₁₂ * w₂ + g₁₂ * w₁) * uBar /
        stickDet p₁ p₂ w₁ w₂ g₁₂) ^ 2 :=
    mul_nonneg (div_pos hΔ hd₁).le (sq_nonneg _)
  linarith

/-! ### 3. Folded-Markov corner ceiling and closed radical obstructions at `log 2` and `log 3` -/

/-- The `c₀`-calibrated folded archimedean-minus-pole jump conductance on `(0, a)²`:
`ω(|x − y|) + ω(x + y) − c₀ cosh(x/2) cosh(y/2)`. Full pole calibration corresponds to `c₀ = 4`. -/
def foldedCalibratedConductance (c₀ x y : ℝ) : ℝ :=
  archLevyDensity |x - y| + archLevyDensity (x + y) - c₀ * Real.cosh (x / 2) * Real.cosh (y / 2)

/-- The corner ceiling `c_max(a) = 2 ω(a) / cosh(a/2)` imposed on `c₀` at `(x, y) → (0⁺, a⁻)`. -/
def cornerCeiling (a : ℝ) : ℝ := 2 * archLevyDensity a / Real.cosh (a / 2)

/-- Hyperbolic sum-to-product identity `cosh(s/2) + cosh((s + 2x)/2) = 2 cosh(x/2) cosh((x + s)/2)`. -/
theorem cosh_half_add_cosh_half_shift (x s : ℝ) :
    Real.cosh (s / 2) + Real.cosh ((s + 2 * x) / 2) =
      2 * Real.cosh (x / 2) * Real.cosh ((x + s) / 2) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
  have h1 : (s + 2 * x) / 2 = s / 2 + x / 2 + x / 2 := by ring
  have h2 : -((s + 2 * x) / 2) = -(s / 2) + -(x / 2) + -(x / 2) := by ring
  have h3 : (x + s) / 2 = x / 2 + s / 2 := by ring
  have h4 : -((x + s) / 2) = -(x / 2) + -(s / 2) := by ring
  rw [h1, h2, h3, h4]
  simp only [Real.exp_add]
  have hex : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination -(Real.exp (s / 2) + Real.exp (-(s / 2))) * hex / 2

/-- For `s > 0`, the folded Weil jump conductance `κ(s) + κ(s + 2x)` equals
`foldedCalibratedConductance 4 x (x + s)`. -/
theorem weilJumpDensity_fold_eq_foldedCalibratedConductance_four {x s : ℝ} (hs : 0 < s) :
    weilJumpDensity s + weilJumpDensity (s + 2 * x) =
      foldedCalibratedConductance 4 x (x + s) := by
  unfold weilJumpDensity foldedCalibratedConductance
  have habs : |x - (x + s)| = s := by
    rw [show x - (x + s) = -s by ring, abs_neg, abs_of_pos hs]
  have hadd : x + (x + s) = s + 2 * x := by ring
  rw [habs, hadd]
  linarith [cosh_half_add_cosh_half_shift x s]

/-- **Exact plastic-number threshold**: for `a > 0`, `ω(a) < 2 cosh(a/2)` holds if and only if
`e^{−2a} + e^{−3a} < 1` (i.e., `e^a > ρ` where `ρ³ = ρ + 1` is the plastic number). -/
theorem archLevyDensity_lt_two_mul_cosh_iff_plastic {a : ℝ} (ha : 0 < a) :
    archLevyDensity a < 2 * Real.cosh (a / 2) ↔
      Real.exp (-2 * a) + Real.exp (-3 * a) < 1 := by
  set u := Real.exp (-(a / 2)) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_neg : Real.exp (-a / 2) = u := by rw [hu]; congr 1; ring
  have h_inv : Real.exp (a / 2) * u = 1 := by rw [hu, ← Real.exp_add]; simp
  have h4 : Real.exp (-2 * a) = u ^ 4 := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h6 : Real.exp (-3 * a) = u ^ 6 := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc : 2 * Real.cosh (a / 2) = Real.exp (a / 2) + u := by
    rw [Real.cosh_eq, hu]; ring
  have hden : 0 < 1 - u ^ 4 := by
    have : u ^ 4 < 1 := pow_lt_one₀ hu0.le hu1 (by norm_num)
    linarith
  have hid : u * ((Real.exp (a / 2) + u) * (1 - u ^ 4)) = 1 + u ^ 2 - u ^ 4 - u ^ 6 := by
    linear_combination (1 - u ^ 4) * h_inv
  unfold archLevyDensity
  rw [h_neg, h4, h6, hc, div_lt_iff₀ hden]
  constructor
  · intro hlt
    have hm := mul_lt_mul_of_pos_left hlt hu0
    linarith [hid]
  · intro hlt
    have hm : u * u < u * ((Real.exp (a / 2) + u) * (1 - u ^ 4)) := by linarith [hid]
    exact lt_of_mul_lt_mul_left hm hu0.le

theorem continuousAt_archLevyDensity {a : ℝ} (ha : 0 < a) :
    ContinuousAt archLevyDensity a := by
  unfold archLevyDensity
  refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
  have : Real.exp (-2 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- Corner limit `(x, y) = (ε, a − ε) → (0⁺, a⁻)` of `foldedCalibratedConductance c₀`. -/
theorem tendsto_foldedCalibratedConductance_corner {a : ℝ} (ha : 0 < a) (c₀ : ℝ) :
    Tendsto (fun ε => foldedCalibratedConductance c₀ ε (a - ε)) (𝓝[>] 0)
      (𝓝 (2 * archLevyDensity a - c₀ * Real.cosh (a / 2))) := by
  have hbase : Tendsto
      (fun ε : ℝ => archLevyDensity (a - 2 * ε) + archLevyDensity a -
        c₀ * Real.cosh (ε / 2) * Real.cosh ((a - ε) / 2))
      (𝓝 0) (𝓝 (2 * archLevyDensity a - c₀ * Real.cosh (a / 2))) := by
    have hsub : Tendsto (fun ε : ℝ => a - 2 * ε) (𝓝 0) (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).sub (tendsto_id.const_mul 2)
    have h1 : Tendsto (fun ε : ℝ => archLevyDensity (a - 2 * ε)) (𝓝 0) (𝓝 (archLevyDensity a)) :=
      (continuousAt_archLevyDensity ha).tendsto.comp hsub
    have h2 : ContinuousAt (fun ε : ℝ => c₀ * Real.cosh (ε / 2) * Real.cosh ((a - ε) / 2)) 0 := by
      fun_prop
    have hlim := (h1.add tendsto_const_nhds).sub h2.tendsto
    simpa [Real.cosh_zero, show 2 * archLevyDensity a = archLevyDensity a + archLevyDensity a by ring]
      using hlim
  refine (hbase.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < a / 2))] with ε hε0 hεa
  unfold foldedCalibratedConductance
  have habs : |ε - (a - ε)| = a - 2 * ε := by
    rw [show ε - (a - ε) = -(a - 2 * ε) by ring, abs_neg, abs_of_pos (by linarith)]
  have hadd : ε + (a - ε) = a := by ring
  rw [habs, hadd]

/-- **Corner ceiling theorem.** Pointwise nonnegativity of `foldedCalibratedConductance c₀` on
`0 < x < y < a` forces `c₀ ≤ cornerCeiling a = 2 ω(a) / cosh(a/2)`. -/
theorem le_cornerCeiling_of_foldedCalibratedConductance_nonneg {a c₀ : ℝ} (ha : 0 < a)
    (hnn : ∀ x y, 0 < x → x < y → y < a → 0 ≤ foldedCalibratedConductance c₀ x y) :
    c₀ ≤ cornerCeiling a := by
  unfold cornerCeiling
  rw [le_div_iff₀ (Real.cosh_pos (a / 2))]
  by_contra! hlt
  set L := 2 * archLevyDensity a - c₀ * Real.cosh (a / 2)
  have hLneg : L < 0 := by linarith
  have hsub : ContinuousAt (fun ε : ℝ => a - 2 * ε) 0 := by fun_prop
  have h1 : ContinuousAt (fun ε : ℝ => archLevyDensity (a - 2 * ε)) 0 := by
    change ContinuousAt (archLevyDensity ∘ fun ε : ℝ => a - 2 * ε) 0
    refine ContinuousAt.comp ?_ hsub
    simpa using continuousAt_archLevyDensity ha
  have h2 : ContinuousAt (fun ε : ℝ => c₀ * Real.cosh (ε / 2) * Real.cosh ((a - ε) / 2)) 0 := by
    fun_prop
  have hcont : ContinuousAt
      (fun ε : ℝ => archLevyDensity (a - 2 * ε) + archLevyDensity a -
        c₀ * Real.cosh (ε / 2) * Real.cosh ((a - ε) / 2)) 0 :=
    (h1.add continuousAt_const).sub h2
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont (-L / 2) (by linarith)
  set ε := min (δ / 2) (a / 4)
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : |ε - 0| < δ := by
    rw [sub_zero, abs_of_pos hε0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hεa : ε < a / 2 := (min_le_right _ _).trans_lt (by linarith)
  have hdist := hclose hεδ
  have hval0 : archLevyDensity (a - 2 * 0) + archLevyDensity a -
      c₀ * Real.cosh (0 / 2) * Real.cosh ((a - 0) / 2) = L := by
    simp [L, Real.cosh_zero]; ring
  rw [Real.dist_eq, hval0] at hdist
  have hneg_val : archLevyDensity (a - 2 * ε) + archLevyDensity a -
      c₀ * Real.cosh (ε / 2) * Real.cosh ((a - ε) / 2) < 0 := by
    linarith [(abs_lt.mp hdist).2]
  have hpos_val := hnn ε (a - ε) hε0 (by linarith) (by linarith)
  unfold foldedCalibratedConductance at hpos_val
  have habs : |ε - (a - ε)| = a - 2 * ε := by
    rw [show ε - (a - ε) = -(a - 2 * ε) by ring, abs_neg, abs_of_pos (by linarith)]
  have hadd : ε + (a - ε) = a := by ring
  rw [habs, hadd] at hpos_val
  linarith

/-- **Interior sign failure past the plastic corner.** Whenever `a > 0` satisfies
`e^{−2a} + e^{−3a} < 1`, there exist interior points `0 < x`, `0 < s`, `x + s < a` where the
folded Weil jump conductance `weilJumpDensity s + weilJumpDensity (s + 2x)` is strictly negative. -/
theorem exists_folded_weilJumpDensity_neg_of_plastic {a : ℝ} (ha : 0 < a)
    (hpl : Real.exp (-2 * a) + Real.exp (-3 * a) < 1) :
    ∃ x s : ℝ, 0 < x ∧ 0 < s ∧ x + s < a ∧
      weilJumpDensity s + weilJumpDensity (s + 2 * x) < 0 := by
  by_contra! hnn
  have hcal : ∀ x y, 0 < x → x < y → y < a → 0 ≤ foldedCalibratedConductance 4 x y := by
    intro x y hx hxy hya
    have hs : 0 < y - x := sub_pos.mpr hxy
    have h := hnn x (y - x) hx hs (by linarith)
    rw [weilJumpDensity_fold_eq_foldedCalibratedConductance_four hs,
      show x + (y - x) = y by ring] at h
    exact h
  have hceil := le_cornerCeiling_of_foldedCalibratedConductance_nonneg ha hcal
  unfold cornerCeiling at hceil
  rw [le_div_iff₀ (Real.cosh_pos (a / 2))] at hceil
  have hlt := (archLevyDensity_lt_two_mul_cosh_iff_plastic ha).mpr hpl
  linarith

/-- **Closed radical form at the first prime (`2a = log 2`):**
`cornerCeiling (log 2 / 2) = 8 (√2 − 1)`. -/
theorem cornerCeiling_half_log_two :
    cornerCeiling (Real.log 2 / 2) = 8 * (Real.sqrt 2 - 1) := by
  set r := Real.exp (Real.log 2 / 4) with hr
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_sq : r ^ 2 = Real.sqrt 2 := by
    have h4 : (r ^ 2) ^ 2 = 2 := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (2 * (Real.log 2 / 4)) = Real.log 2 by ring, Real.exp_log (by norm_num)]
    rw [← Real.sqrt_sq (sq_nonneg r), h4]
  have h_neg_exp : Real.exp (-(Real.log 2 / 2) / 2) = r⁻¹ := by
    rw [hr, ← Real.exp_neg]; congr 1; ring
  have hexp_two : Real.exp (-2 * (Real.log 2 / 2)) = 1 / 2 := by
    rw [show -2 * (Real.log 2 / 2) = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  have hcosh : Real.cosh ((Real.log 2 / 2) / 2) = (r + r⁻¹) / 2 := by
    rw [Real.cosh_eq, show (Real.log 2 / 2) / 2 = Real.log 2 / 4 by ring, Real.exp_neg, ← hr]
  unfold cornerCeiling archLevyDensity
  rw [h_neg_exp, hexp_two, hcosh]
  have h1 : 2 * (r⁻¹ / (1 - 1 / 2)) / ((r + r⁻¹) / 2) = 8 / (r ^ 2 + 1) := by
    field_simp [hr_pos.ne']; ring
  rw [h1, hr_sq, div_eq_iff (by positivity)]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Closed radical form at the second prime (`2a = log 3`):**
`cornerCeiling (log 3 / 2) = 3 (√3 − 1)`. -/
theorem cornerCeiling_half_log_three :
    cornerCeiling (Real.log 3 / 2) = 3 * (Real.sqrt 3 - 1) := by
  set r := Real.exp (Real.log 3 / 4) with hr
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_sq : r ^ 2 = Real.sqrt 3 := by
    have h4 : (r ^ 2) ^ 2 = 3 := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (2 * (Real.log 3 / 4)) = Real.log 3 by ring, Real.exp_log (by norm_num)]
    rw [← Real.sqrt_sq (sq_nonneg r), h4]
  have h_neg_exp : Real.exp (-(Real.log 3 / 2) / 2) = r⁻¹ := by
    rw [hr, ← Real.exp_neg]; congr 1; ring
  have hexp_three : Real.exp (-2 * (Real.log 3 / 2)) = 1 / 3 := by
    rw [show -2 * (Real.log 3 / 2) = -Real.log 3 by ring, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  have hcosh : Real.cosh ((Real.log 3 / 2) / 2) = (r + r⁻¹) / 2 := by
    rw [Real.cosh_eq, show (Real.log 3 / 2) / 2 = Real.log 3 / 4 by ring, Real.exp_neg, ← hr]
  unfold cornerCeiling archLevyDensity
  rw [h_neg_exp, hexp_three, hcosh]
  have h1 : 2 * (r⁻¹ / (1 - 1 / 3)) / ((r + r⁻¹) / 2) = 6 / (r ^ 2 + 1) := by
    field_simp [hr_pos.ne']; ring
  rw [h1, hr_sq, div_eq_iff (by positivity)]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- At `2a = log 2`, the corner ceiling `8(√2 − 1)` is strictly below full pole calibration `4`. -/
theorem cornerCeiling_half_log_two_lt_four :
    cornerCeiling (Real.log 2 / 2) < 4 := by
  rw [cornerCeiling_half_log_two]
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- At `2a = log 3`, the corner ceiling `3(√3 − 1)` is strictly below full pole calibration `4`. -/
theorem cornerCeiling_half_log_three_lt_four :
    cornerCeiling (Real.log 3 / 2) < 4 := by
  rw [cornerCeiling_half_log_three]
  have hsqrt : Real.sqrt 3 < 7 / 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- The folded Weil jump conductance takes strictly negative values inside `(0, ½ log 2)²`. -/
theorem exists_folded_weilJumpDensity_neg_half_log_two :
    ∃ x s : ℝ, 0 < x ∧ 0 < s ∧ x + s < Real.log 2 / 2 ∧
      weilJumpDensity s + weilJumpDensity (s + 2 * x) < 0 := by
  have ha : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  by_contra! hnn
  have hcal : ∀ x y, 0 < x → x < y → y < Real.log 2 / 2 → 0 ≤ foldedCalibratedConductance 4 x y := by
    intro x y hx hxy hya
    have hs : 0 < y - x := sub_pos.mpr hxy
    have h := hnn x (y - x) hx hs (by linarith)
    rw [weilJumpDensity_fold_eq_foldedCalibratedConductance_four hs,
      show x + (y - x) = y by ring] at h
    exact h
  linarith [le_cornerCeiling_of_foldedCalibratedConductance_nonneg ha hcal,
    cornerCeiling_half_log_two_lt_four]

/-- The folded Weil jump conductance takes strictly negative values inside `(0, ½ log 3)²`. -/
theorem exists_folded_weilJumpDensity_neg_half_log_three :
    ∃ x s : ℝ, 0 < x ∧ 0 < s ∧ x + s < Real.log 3 / 2 ∧
      weilJumpDensity s + weilJumpDensity (s + 2 * x) < 0 := by
  have ha : 0 < Real.log 3 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  by_contra! hnn
  have hcal : ∀ x y, 0 < x → x < y → y < Real.log 3 / 2 → 0 ≤ foldedCalibratedConductance 4 x y := by
    intro x y hx hxy hya
    have hs : 0 < y - x := sub_pos.mpr hxy
    have h := hnn x (y - x) hx hs (by linarith)
    rw [weilJumpDensity_fold_eq_foldedCalibratedConductance_four hs,
      show x + (y - x) = y by ring] at h
    exact h
  linarith [le_cornerCeiling_of_foldedCalibratedConductance_nonneg ha hcal,
    cornerCeiling_half_log_three_lt_four]

/-- **Half-line Doob pole-mass conservation (`I_in(a) + I_ext(a) = 1/4`).**
For every `a ≥ 0`, the interior `cosh(x/2)` mass of `riemannKernelReal` on `(0, a]` and its
exterior leakage on `(a, ∞)` sum to `1/4`, with `I_ext(a) > 0`. -/
theorem phiDoob_halfLine_coshMass_split {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in Ioc (0 : ℝ) a, riemannKernelReal x * Real.cosh (x / 2)) +
      (∫ x in Ioi a, riemannKernelReal x * Real.cosh (x / 2)) = 1 / 4 := by
  have hi : Integrable (fun x : ℝ => riemannKernelReal x * Real.cosh (x / 2)) := by
    have hp : Integrable (fun x : ℝ => riemannKernelReal x * Real.exp ((1 / 2 : ℝ) * x)) :=
      integrable_riemannKernelReal_mul_exp (1 / 2)
    have hm : Integrable (fun x : ℝ => riemannKernelReal x * Real.exp ((-(1 / 2) : ℝ) * x)) :=
      integrable_riemannKernelReal_mul_exp (-(1 / 2))
    refine ((hp.add hm).div_const 2).congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Real.cosh_eq, show (1 / 2 : ℝ) * x = x / 2 by ring,
      show (-(1 / 2) : ℝ) * x = -(x / 2) by ring]
    ring
  rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hi.integrableOn hi.integrableOn, Ioc_union_Ioi_eq_Ioi ha]
  have heven_half : 2 * (∫ x in Ioi (0 : ℝ), riemannKernelReal x * Real.cosh (x / 2)) =
      ∫ x : ℝ, riemannKernelReal x * Real.cosh (x / 2) := by
    rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi]
    have hneg := integral_comp_neg_Ioi 0 (fun x => riemannKernelReal x * Real.cosh (x / 2))
    rw [neg_zero] at hneg
    rw [← hneg]
    have hev : (∫ x in Ioi (0 : ℝ), riemannKernelReal (-x) * Real.cosh (-x / 2)) =
        ∫ x in Ioi (0 : ℝ), riemannKernelReal x * Real.cosh (x / 2) :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => by
        rw [riemannKernelReal_neg', show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    rw [hev]
    ring
  linarith [heven_half, integral_riemannKernelReal_cosh_half]

end GaloisForLFunctions.ArithmeticCriticalityTheory.WindowJumpCounts

end
