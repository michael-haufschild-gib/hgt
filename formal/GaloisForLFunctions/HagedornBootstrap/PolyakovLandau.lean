import GaloisForLFunctions.HagedornBootstrap.GrossWittenWall
import GaloisForLFunctions.HTGeometry.Thermodynamics.LandauCanonicalCriticality

/-!
# The order of the deconfinement transition: Landau theory of the Polyakov loop

Near the Hagedorn temperature only the Polyakov loop `u₁` is light. Integrating out the heavy
second moment `u₂`, coupled to `u₁²` by the cubic term `κ(u₁²ū₂ + c.c.)`, shifts the quartic
coefficient to `b = b̃ − κ²/m₂`: exchange of a massive mode always attracts. In the real slice
this is exactly the Schur complement of the corpus heavy-channel form, with the heavy channel
`u₂` and the light channel `u₁²`.

With the Gross–Witten–Wadia wall the potential of `u = |u₁|` is
`S(u) = V(u) − u² + m u² + b u⁴`. Its phase structure is decided by the sign of `b`:

* `b = −B < 0` (**first order**): for `0 < m` the confined point `u = 0` is a strict local
  minimum; for `m < B/2` an unstable saddle `u_s = √(m/2B)` (the small black hole) sits below
  `u = 1/2` with barrier `m²/4B`; for `m < B/4` the gapped region beats `u = 0`, so for
  `0 < m < B/4` both phases coexist (metastability); for `m < 0` the origin is unstable.
* `b > 0` (**second order**): for `m ≥ 0` the origin is the unique minimum; for `−b/2 ≤ m < 0`
  the global minimum is `−m²/4b`, attained at `u² = −m/2b ≤ 1/4` (the corpus canonical Landau
  minimum), growing continuously from `0`.

On a linear mass `m = σ(T_H − T)` the coexistence window has the exchange temperature exactly
in the middle: `T_H − T_c = (T_H − T_min)/2`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

open HTGeometry.TraceDynamics HTGeometry.Thermodynamics

/-! ### Exchange of the heavy mode -/

/-- Real slice of the two-mode action: light loop `x`, heavy moment `w`. -/
def twoModeAction (m1 m2 κ bt x w : ℝ) : ℝ := m1 * x ^ 2 + m2 * w ^ 2 + 2 * κ * x ^ 2 * w + bt * x ^ 4

/-- The heavy-mode part is the corpus heavy-channel quadratic in `(w, x²)`. -/
theorem twoModeAction_eq_heavyChannel (m1 a κ bt x w : ℝ) :
    twoModeAction m1 (Real.exp a) κ bt x w = m1 * x ^ 2 + heavyChannelQuadratic a κ bt w (x ^ 2) := by
  unfold twoModeAction heavyChannelQuadratic
  ring

/-- Completing the square in the heavy mode. -/
theorem twoModeAction_decomposition {m2 : ℝ} (hm2 : m2 ≠ 0) (m1 κ bt x w : ℝ) :
    twoModeAction m1 m2 κ bt x w =
      m1 * x ^ 2 + m2 * (w + κ * x ^ 2 / m2) ^ 2 + (bt - κ ^ 2 / m2) * x ^ 4 := by
  unfold twoModeAction
  field_simp
  ring

/-- **Integrating out the heavy mode** leaves the quartic `b = b̃ − κ²/m₂`. -/
theorem twoModeAction_ge_effective {m2 : ℝ} (hm2 : 0 < m2) (m1 κ bt x w : ℝ) :
    m1 * x ^ 2 + (bt - κ ^ 2 / m2) * x ^ 4 ≤ twoModeAction m1 m2 κ bt x w := by
  rw [twoModeAction_decomposition hm2.ne']
  nlinarith [mul_nonneg hm2.le (sq_nonneg (w + κ * x ^ 2 / m2))]

theorem twoModeAction_at_saddle {m2 : ℝ} (hm2 : 0 < m2) (m1 κ bt x : ℝ) :
    twoModeAction m1 m2 κ bt x (-(κ * x ^ 2 / m2)) = m1 * x ^ 2 + (bt - κ ^ 2 / m2) * x ^ 4 := by
  rw [twoModeAction_decomposition hm2.ne']
  ring

/-- Exchange always attracts: the effective quartic never exceeds the bare one. -/
theorem effectiveQuartic_le {m2 : ℝ} (hm2 : 0 < m2) (κ bt : ℝ) : bt - κ ^ 2 / m2 ≤ bt := by
  have : 0 ≤ κ ^ 2 / m2 := by positivity
  linarith

/-- The effective quartic is negative exactly when `κ² > b̃ m₂`. -/
theorem effectiveQuartic_neg_iff {m2 : ℝ} (hm2 : 0 < m2) (κ bt : ℝ) :
    bt - κ ^ 2 / m2 < 0 ↔ bt * m2 < κ ^ 2 := by
  rw [sub_neg, lt_div_iff₀ hm2]

/-- Via the corpus heavy-channel criterion: the exchanged quartic form is nonnegative in
`(w, x²)` exactly when the effective quartic is nonnegative. -/
theorem exchange_nonneg_iff (a κ bt : ℝ) :
    (∀ w y, 0 ≤ heavyChannelQuadratic a κ bt w y) ↔ 0 ≤ bt - κ ^ 2 / Real.exp a := by
  rw [heavyChannel_nonnegative_iff, sub_nonneg]

/-- The complex exchange: `m₂|w|² + 2κ Re(ū² w) ≥ −κ²|u|⁴/m₂`, with equality at
`w = −κu²/m₂`. -/
theorem complexExchange_ge {m2 : ℝ} (hm2 : 0 < m2) (κ : ℝ) (u w : ℂ) :
    -(κ ^ 2 * ‖u‖ ^ 4 / m2) ≤ m2 * ‖w‖ ^ 2 + 2 * κ * ((starRingEnd ℂ) (u ^ 2) * w).re := by
  have key : m2 * ‖w‖ ^ 2 + 2 * κ * ((starRingEnd ℂ) (u ^ 2) * w).re + κ ^ 2 * ‖u‖ ^ 4 / m2 =
      ‖(m2 : ℂ) * w + κ * u ^ 2‖ ^ 2 / m2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      show ‖u‖ ^ 4 = (‖u ^ 2‖) ^ 2 by rw [norm_pow]; ring, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  have : 0 ≤ ‖(m2 : ℂ) * w + κ * u ^ 2‖ ^ 2 / m2 := by positivity
  linarith

/-! ### The potential with the wall -/

/-- `S(u) = V(u) − u² + m u² + b u⁴`. -/
def polyakovAction (m b u : ℝ) : ℝ := gwwPotential u - u ^ 2 + m * u ^ 2 + b * u ^ 4

theorem polyakovAction_of_le {m b u : ℝ} (h : u ≤ 1 / 2) :
    polyakovAction m b u = m * u ^ 2 + b * u ^ 4 := by
  rw [polyakovAction, gwwPotential_of_le h]; ring

theorem polyakovAction_zero (m b : ℝ) : polyakovAction m b 0 = 0 := by
  rw [polyakovAction_of_le (by norm_num)]; ring

/-- The wall only raises the potential. -/
theorem polyakovAction_ge {m b u : ℝ} (h1 : u < 1) :
    m * u ^ 2 + b * u ^ 4 ≤ polyakovAction m b u := by
  have := sq_le_gwwPotential h1
  unfold polyakovAction; linarith

/-! #### Negative quartic: first order -/

/-- For `m > 0` the confined point is a strict local minimum: `S > 0` for `0 < u < √(m/B)`,
`u ≤ 1/2`. -/
theorem confined_strict_localMin {m B u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    (hsmall : B * u ^ 2 < m) : 0 < polyakovAction m (-B) u := by
  rw [polyakovAction_of_le hu]
  have : 0 < u ^ 2 := by positivity
  nlinarith

/-- The small-black-hole saddle `u_s² = m/2B` is the maximum of the ungapped branch, with
barrier height `m²/4B`. -/
theorem smallBlackHole_barrier {m B u : ℝ} (hB : 0 < B) (hu : u ≤ 1 / 2) :
    polyakovAction m (-B) u ≤ m ^ 2 / (4 * B) := by
  rw [polyakovAction_of_le hu]
  have key : m ^ 2 / (4 * B) - (m * u ^ 2 + -B * u ^ 4) = B * (u ^ 2 - m / (2 * B)) ^ 2 := by
    field_simp; ring
  have : 0 ≤ B * (u ^ 2 - m / (2 * B)) ^ 2 := by positivity
  linarith

theorem smallBlackHole_value {m B : ℝ} (hB : 0 < B) (hm : 0 ≤ m) (hs : m / (2 * B) ≤ 1 / 4) :
    polyakovAction m (-B) (Real.sqrt (m / (2 * B))) = m ^ 2 / (4 * B) := by
  have hnn : 0 ≤ m / (2 * B) := by positivity
  have hle : Real.sqrt (m / (2 * B)) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs
  rw [polyakovAction_of_le hle, show Real.sqrt (m / (2 * B)) ^ 4 =
    (Real.sqrt (m / (2 * B)) ^ 2) ^ 2 by ring, Real.sq_sqrt hnn]
  field_simp
  ring

/-- The saddle is a critical point of the ungapped branch. -/
theorem hasDerivAt_quartic_smallBlackHole {m B : ℝ} (hB : 0 < B) (hm : 0 ≤ m) :
    HasDerivAt (fun u : ℝ => m * u ^ 2 + -B * u ^ 4) 0 (Real.sqrt (m / (2 * B))) := by
  have hnn : 0 ≤ m / (2 * B) := by positivity
  set s := Real.sqrt (m / (2 * B))
  have hs2 : s ^ 2 = m / (2 * B) := Real.sq_sqrt hnn
  refine (((hasDerivAt_pow 2 s).const_mul m).add ((hasDerivAt_pow 4 s).const_mul (-B))).congr_deriv ?_
  push_cast
  rw [pow_one, show s ^ 3 = s * s ^ 2 by ring, hs2]
  field_simp
  ring

/-- Below `m = B/4` the gap point `u = 1/2` already beats the confined phase. -/
theorem deconfined_beats_confined {m B : ℝ} (hm : m < B / 4) :
    polyakovAction m (-B) (1 / 2) < polyakovAction m (-B) 0 := by
  rw [polyakovAction_zero, polyakovAction_of_le le_rfl]
  nlinarith

/-- Above `m = B/4` the confined phase wins on the whole ungapped branch. -/
theorem confined_wins_ungapped {m B u : ℝ} (hB : 0 ≤ B) (hm : B / 4 ≤ m) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2) : 0 ≤ polyakovAction m (-B) u := by
  rw [polyakovAction_of_le hu]
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have h0 : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith [mul_nonneg (mul_nonneg hB h0) (sub_nonneg.mpr hu2),
    mul_nonneg (sub_nonneg.mpr hm) h0]

/-- **Metastable coexistence**, the hallmark of a first-order transition: for `0 < m < B/4` the
confined point is a strict local minimum while another configuration has lower action. -/
theorem firstOrder_coexistence {m B : ℝ} (hm : m < B / 4) :
    (∀ u : ℝ, 0 < u → u ≤ 1 / 2 → B * u ^ 2 < m → 0 < polyakovAction m (-B) u) ∧
      ∃ u, polyakovAction m (-B) u < polyakovAction m (-B) 0 :=
  ⟨fun _ hu0 hu hs => confined_strict_localMin hu0 hu hs, ⟨1 / 2, deconfined_beats_confined hm⟩⟩

/-- The confined point is unstable once `b u² < −m` for small `u`, in particular for `m < 0`. -/
theorem confined_unstable {m b u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    (hsmall : b * u ^ 2 < -m) : polyakovAction m b u < 0 := by
  rw [polyakovAction_of_le hu]
  have : 0 < u ^ 2 := by positivity
  nlinarith

/-! #### Positive quartic: second order -/

/-- For `b > 0` and `m ≥ 0` the origin is the unique minimum on `[0, 1)`. -/
theorem secondOrder_confined {m b u : ℝ} (hb : 0 < b) (hm : 0 ≤ m) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < polyakovAction m b u := by
  have h := polyakovAction_ge (m := m) (b := b) hu1
  have : 0 < b * u ^ 4 := by positivity
  nlinarith [mul_nonneg hm (sq_nonneg u)]

/-- For `b > 0` the action is bounded below by the corpus canonical Landau minimum `−m²/4b`. -/
theorem secondOrder_lower_bound {m b u : ℝ} (hb : 0 < b) (hu1 : u < 1) :
    landauScalarMinimum (Real.log b / 2) m ≤ polyakovAction m b u := by
  have hexp : Real.exp (Real.log b / 2) ^ 2 = b := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (Real.log b / 2) = Real.log b by push_cast; ring,
      Real.exp_log hb]
  have h1 := landauScalar_global_lower_bound (Real.log b / 2) m u
  rw [landauScalar_slice, hexp] at h1
  exact h1.trans (polyakovAction_ge hu1)

/-- For `b > 0`, `−b/2 ≤ m < 0` the minimum `−m²/4b` is attained at `u² = −m/2b ≤ 1/4`:
the loop grows continuously from zero (second order). -/
theorem secondOrder_minimum_attained {m b : ℝ} (hb : 0 < b) (hm : m < 0) (hm' : -(b / 2) ≤ m) :
    polyakovAction m b (Real.sqrt (-m / (2 * b))) = -(m ^ 2) / (4 * b) ∧
      ∀ u, u < 1 → -(m ^ 2) / (4 * b) ≤ polyakovAction m b u := by
  have hnn : 0 ≤ -m / (2 * b) := div_nonneg (by linarith) (by positivity)
  have hle : Real.sqrt (-m / (2 * b)) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]; linarith
  constructor
  · rw [polyakovAction_of_le hle, show Real.sqrt (-m / (2 * b)) ^ 4 =
      (Real.sqrt (-m / (2 * b)) ^ 2) ^ 2 by ring, Real.sq_sqrt hnn]
    field_simp
    ring
  · intro u hu1
    have := polyakovAction_ge (m := m) (b := b) hu1
    have key : m * u ^ 2 + b * u ^ 4 - (-(m ^ 2) / (4 * b)) = b * (u ^ 2 + m / (2 * b)) ^ 2 := by
      field_simp; ring
    have : 0 ≤ b * (u ^ 2 + m / (2 * b)) ^ 2 := by positivity
    linarith

/-! ### Temperatures -/

/-- On a linear mass `m = σ(T_H − T)`, `σ > 0`, the exchange point `m = B/4` is the midpoint of
the coexistence window between `m = B/2` (`T_min`) and `m = 0` (`T_H`). -/
theorem exchange_temperature_midpoint {σ B TH : ℝ} (hσ : 0 < σ) :
    let Tmin := TH - B / (2 * σ)
    let Tc := TH - B / (4 * σ)
    σ * (TH - Tmin) = B / 2 ∧ σ * (TH - Tc) = B / 4 ∧ TH - Tc = (TH - Tmin) / 2 := by
  simp only
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- With the slope `m ≈ (3/2)β₀(T_H − T)/T_H` the relative widths are `|b|/6β₀` and `|b|/3β₀`. -/
theorem relative_window_widths {β₀ B : ℝ} (hβ : 0 < β₀) :
    3 / 2 * β₀ * (B / (6 * β₀)) = B / 4 ∧ 3 / 2 * β₀ * (B / (3 * β₀)) = B / 2 := by
  exact ⟨by field_simp; ring, by field_simp⟩

/-- The latent heat: `∂_β m = 3/2` at `u² = 1/4` gives `ΔE = (3/2)·(1/4) = 3/8` in units of
`N²/R`. -/
theorem latent_heat : (3 / 2 : ℝ) * (1 / 2) ^ 2 = 3 / 8 := by norm_num

end GaloisForLFunctions.HagedornBootstrap
