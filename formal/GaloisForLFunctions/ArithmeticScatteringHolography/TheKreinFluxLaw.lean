import GaloisForLFunctions.ArithmeticScatteringHolography.TheExactRingdown
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Krein flux law

The ringdown of the black hole is one damped oscillator: `R_{n+2} = t R_{n+1} - q R_n`. Any such oscillator
carries the quadratic form

  `𝒬(x, y) = y² - t x y + q x²`,

and along a trajectory `𝒬` is multiplied by exactly `q` per double tick, whatever `t` is
(`kreinSquare_step`). In the energy normalization, where a double tick divides the amplitude by `q`, this
is decay by `1/q`: **the Krein square decays at the universal rate on every black hole**, true or fake.

This answers the two questions about the universal rate.

* **What decays at the universal rate?** The Krein square (`normalizedKrein_step`). It is the
  Turán determinant `y² - x z` of three consecutive echoes (`kreinSquare_eq_turan`), read from the reflected
  signal alone, with no knowledge of `t`.
* **What is `¼`?** Two solutions have Wronskian multiplied by `q` per double tick (`wronskian_step`), which is
  Liouville's formula for the state map of determinant `q`. So the area of phase space shrinks at a rate
  fixed by the functional equation, and each pair of partner modes has rates summing to `½`. The value `¼`
  is the isotropic case. **Universal damping says that every oscillator is underdamped.** At `t² = 4q` it is
  critically damped; for `t² > 4q` it is overdamped, with two real rates, one faster and one slower than
  `¼`.

The flux is `𝓕 = (1 - 1/q) 𝒬` (`normalizedKrein_flux`), so nonnegative flux for all boundary data is
positivity of `𝒬`. By completing the square, `𝒬` is then a sum of squares of boundary signals, and this
happens exactly when `t² ≤ 4q` (`kreinSquare_nonneg_iff`). So a flux law exists on every black hole, and
it is a manifest boundary square exactly under universal damping.

The form is `deg(m - nF)`, the degree form of the Frobenius that Cassels and Weil use. A two-term causal
probe multiplies `𝒬` by this form (`kreinSquare_probe`). Pulses have positive Krein square, and the fake
black holes are detected only by a probe (`kreinSquare_ringSignal`).
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

section Algebra

variable {R : Type*} [CommRing R]

/-- The Krein square `𝒬(x, y) = y² - t x y + q x²` of the state `(x, y)`. -/
def kreinSquare (q t x y : R) : R := y ^ 2 - t * x * y + q * x ^ 2

/-- **The Krein flux law.** Along the recurrence, `𝒬` is multiplied by exactly `q`. -/
theorem kreinSquare_step (q t x y : R) :
    kreinSquare q t y (t * y - q * x) = q * kreinSquare q t x y := by
  unfold kreinSquare
  ring

/-- **The Krein square is the Turán determinant** of three consecutive values. -/
theorem kreinSquare_eq_turan (q t x y : R) :
    kreinSquare q t x y = y ^ 2 - x * (t * y - q * x) := by
  unfold kreinSquare
  ring

/-- **Liouville.** The Wronskian of two solutions is multiplied by `q`, independently of `t`. -/
theorem wronskian_step (q t x y x' y' : R) :
    y * (t * y' - q * x') - (t * y - q * x) * y' = q * (x * y' - y * x') := by
  ring

/-- The form of a two-term probe `g₀ + g₁ w`: the degree form `deg(m - nF)`, up to the sign of `n`. -/
def probeNorm (q t g₀ g₁ : R) : R := q * g₀ ^ 2 + t * g₀ * g₁ + g₁ ^ 2

/-- **A two-term probe multiplies the Krein square by the degree form.** -/
theorem kreinSquare_probe (q t g₀ g₁ x y : R) :
    kreinSquare q t (g₀ * y + g₁ * x) (g₀ * (t * y - q * x) + g₁ * y) =
      probeNorm q t g₀ g₁ * kreinSquare q t x y := by
  unfold kreinSquare probeNorm
  ring

end Algebra

/-! ### Positivity -/

/-- **A mode is a null vector of the Krein form.** Each eigenstate `(1, a)` has `𝒬 = 0`. -/
theorem kreinSquare_mode_eq_zero {q t a : ℂ} (ha : a ^ 2 - t * a + q = 0) : kreinSquare q t 1 a = 0 := by
  unfold kreinSquare
  linear_combination ha

/-- **Two modes span a plane of signature `(1, 1)` when they are real.** The sum `(2, t)` of the two eigenstates has
`𝒬 = 4q - t²`, negative above the critical discriminant. -/
theorem kreinSquare_sum_of_modes (q t : ℝ) : kreinSquare q t 2 t = 4 * q - t ^ 2 := by
  unfold kreinSquare
  ring

/-- **The form is positive exactly under universal damping.** -/
theorem kreinSquare_nonneg_iff {q t : ℝ} :
    (∀ x y : ℝ, 0 ≤ kreinSquare q t x y) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have h1 := h 2 t
    unfold kreinSquare at h1
    nlinarith
  · intro h x y
    unfold kreinSquare
    nlinarith [sq_nonneg (y - t * x / 2), mul_nonneg (sub_nonneg.mpr h) (sq_nonneg x)]

/-- Below the critical discriminant, the Krein square is a sum of squares of two boundary signals. -/
theorem kreinSquare_eq_sum_sq {q t : ℝ} (h : t ^ 2 ≤ 4 * q) (x y : ℝ) :
    kreinSquare q t x y = (y - t * x / 2) ^ 2 + (Real.sqrt (q - t ^ 2 / 4) * x) ^ 2 := by
  have hs : Real.sqrt (q - t ^ 2 / 4) ^ 2 = q - t ^ 2 / 4 :=
    Real.sq_sqrt (by linarith)
  unfold kreinSquare
  rw [mul_pow, hs]
  ring

/-- Above it, there is a state with negative Krein square, and a null direction. -/
theorem exists_kreinSquare_neg {q t : ℝ} (h : 4 * q < t ^ 2) :
    ∃ x y : ℝ, kreinSquare q t x y < 0 := by
  refine ⟨2, t, ?_⟩
  unfold kreinSquare
  nlinarith

/-- The probe form is positive exactly under universal damping. -/
theorem probeNorm_nonneg_iff {q t : ℝ} :
    (∀ g₀ g₁ : ℝ, 0 ≤ probeNorm q t g₀ g₁) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have h1 := h 2 (-t)
    unfold probeNorm at h1
    nlinarith
  · intro h g₀ g₁
    unfold probeNorm
    nlinarith [sq_nonneg (g₁ + t * g₀ / 2), mul_nonneg (sub_nonneg.mpr h) (sq_nonneg g₀)]

/-! ### Flux in the energy normalization -/

/-- The Krein square in the energy normalization, where the amplitude at double tick `n` carries `q^{-n}`. -/
def normalizedKrein (q t x y : ℝ) (n : ℕ) : ℝ := kreinSquare q t x y / q ^ (2 * n)

/-- **Decay at the universal rate.** After one double tick, the normalized Krein square is divided by `q`.
Per tick this is `q^{-1/2}`, the square of `q^{-1/4}`. -/
theorem normalizedKrein_step {q : ℝ} (hq : q ≠ 0) (t x y : ℝ) (n : ℕ) :
    normalizedKrein q t y (t * y - q * x) (n + 1) = normalizedKrein q t x y n / q := by
  unfold normalizedKrein
  rw [kreinSquare_step]
  field_simp
  ring

/-- **The flux.** The Krein square lost in one double tick is `(1 - 1/q) 𝒬`. -/
theorem normalizedKrein_flux {q : ℝ} (hq : q ≠ 0) (t x y : ℝ) (n : ℕ) :
    normalizedKrein q t x y n - normalizedKrein q t y (t * y - q * x) (n + 1) =
      (1 - 1 / q) * normalizedKrein q t x y n := by
  rw [normalizedKrein_step hq]
  ring

/-- **Chetaev on the graph.** The flux is nonnegative on all boundary data exactly under universal damping.
A mode with negative Krein square decays only because its flux is negative: it is fed, not dissipated. -/
theorem flux_nonneg_iff {q : ℝ} (hq : 1 < q) (t : ℝ) (n : ℕ) :
    (∀ x y : ℝ, 0 ≤ normalizedKrein q t x y n - normalizedKrein q t y (t * y - q * x) (n + 1)) ↔
      t ^ 2 ≤ 4 * q := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < 1 - 1 / q := by
    rw [sub_pos, div_lt_one hq0]
    exact hq
  have hqn : 0 < q ^ (2 * n) := by positivity
  rw [← kreinSquare_nonneg_iff]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [normalizedKrein_flux hq0.ne', mul_nonneg_iff_of_pos_left hq1]
  unfold normalizedKrein
  exact ⟨fun h => by
    have := mul_nonneg h hqn.le
    rwa [div_mul_cancel₀ _ hqn.ne'] at this, fun h => div_nonneg h hqn.le⟩

/-! ### The actual ringdown -/

/-- The first state of the ringdown has Krein square `q² h'`, with `h' = q + 1 + t`. -/
theorem kreinSquare_ringSignal_zero (q t : ℂ) :
    kreinSquare q t (ringSignal q t 0) (ringSignal q t 1) = q ^ 2 * (q + 1 + t) := by
  simp only [ringSignal, lucas, kreinSquare]
  ring

/-- **The Krein square of a pulse.** It is `q^{n+2} h'` at double tick `n`: positive on every black hole,
true or fake. The pulse alone does not detect an off-line mode. -/
theorem kreinSquare_ringSignal (q t : ℂ) (n : ℕ) :
    kreinSquare q t (ringSignal q t n) (ringSignal q t (n + 1)) = q ^ (n + 2) * (q + 1 + t) := by
  induction n with
  | zero => simpa using kreinSquare_ringSignal_zero q t
  | succ n ih =>
    show kreinSquare q t (ringSignal q t (n + 1)) (ringSignal q t (n + 2)) = _
    rw [ringSignal_add_two, kreinSquare_step, ih]
    ring

/-- **A two-term probe on the actual echo train**: the Krein square is the degree form times `q^{n+2} h'`. -/
theorem kreinSquare_probe_ringSignal (q t g₀ g₁ : ℂ) (n : ℕ) :
    kreinSquare q t (g₀ * ringSignal q t (n + 1) + g₁ * ringSignal q t n)
        (g₀ * ringSignal q t (n + 2) + g₁ * ringSignal q t (n + 1)) =
      probeNorm q t g₀ g₁ * (q ^ (n + 2) * (q + 1 + t)) := by
  rw [ringSignal_add_two, kreinSquare_probe, kreinSquare_ringSignal]

/-- **Universal damping is positivity of the Krein square under causal probes.** The Krein square is read
from the reflected signal. Pulses alone are positive on every black hole; probes with two terms separate
true from fake. -/
theorem probe_krein_nonneg_iff {q t : ℝ} (hq : 0 < q) (hh : 0 < q + 1 + t) (n : ℕ) :
    (∀ g₀ g₁ : ℝ, 0 ≤ probeNorm q t g₀ g₁ * (q ^ (n + 2) * (q + 1 + t))) ↔ t ^ 2 ≤ 4 * q := by
  have hpos : 0 < q ^ (n + 2) * (q + 1 + t) := mul_pos (pow_pos hq _) hh
  rw [← probeNorm_nonneg_iff]
  exact forall_congr' fun g₀ => forall_congr' fun g₁ => mul_nonneg_iff_of_pos_right hpos

/-! ### Underdamped, critical, overdamped -/

/-- **The modes are on the universal circle exactly when the oscillator is not overdamped.** -/
theorem modes_on_circle_iff {q t : ℝ} (hq : 0 < q) :
    (∀ a : ℂ, a ^ 2 - t * a + q = 0 → Complex.normSq a = q) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    by_contra hlt
    have hlt' : 4 * q < t ^ 2 := not_le.mp hlt
    set D := Real.sqrt (t ^ 2 - 4 * q) with hD
    have hDsq : D ^ 2 = t ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
    have hDpos : 0 < D := Real.sqrt_pos.mpr (by linarith)
    have root (x : ℝ) (hx : x ^ 2 - t * x + q = 0) : x ^ 2 = q := by
      have := h (x : ℂ) (by exact_mod_cast hx)
      rw [Complex.normSq_ofReal] at this
      nlinarith
    have h1 := root ((t + D) / 2) (by nlinarith)
    have h2 := root ((t - D) / 2) (by nlinarith)
    nlinarith
  · intro h a ha
    have hre := congrArg Complex.re ha
    have him := congrArg Complex.im ha
    simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.zero_im] at hre him
    rw [Complex.normSq_apply]
    by_cases hy : a.im = 0
    · rw [hy] at hre
      have h3 : (2 * a.re - t) ^ 2 = t ^ 2 - 4 * q := by nlinarith
      have h4 : 2 * a.re - t = 0 := by
        have : (2 * a.re - t) ^ 2 ≤ 0 := by linarith
        exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
      rw [hy]
      nlinarith
    · have h5 : 2 * a.re = t := by
        have : a.im * (2 * a.re - t) = 0 := by nlinarith
        have h6 := (mul_eq_zero.mp this).resolve_left hy
        linarith
      linear_combination -hre + a.re * h5

/-- Above the critical discriminant one real mode is slower than universal. -/
theorem exists_slow_mode {q t : ℝ} (hq : 0 < q) (h : 4 * q < t ^ 2) :
    ∃ x x' : ℝ, x + x' = t ∧ x * x' = q ∧ q < x ^ 2 ∧ x' ^ 2 < q := by
  set D := Real.sqrt (t ^ 2 - 4 * q) with hD
  have hDsq : D ^ 2 = t ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have hprod : (t + D) / 2 * ((t - D) / 2) = q := by nlinarith
  have hne : t ≠ 0 := by
    rintro rfl
    nlinarith
  rcases lt_or_gt_of_ne hne with ht | ht
  · refine ⟨(t - D) / 2, (t + D) / 2, by ring, by linarith, ?_, ?_⟩ <;> nlinarith
  · refine ⟨(t + D) / 2, (t - D) / 2, by ring, hprod, ?_, ?_⟩ <;> nlinarith

/-- Below the critical discriminant the two modes are a conjugate pair on the universal circle. -/
theorem exists_roots_on_circle {q t : ℝ} (h : t ^ 2 ≤ 4 * q) :
    ∃ α β : ℂ, α + β = t ∧ α * β = q ∧ ‖α‖ = Real.sqrt q ∧ ‖β‖ = Real.sqrt q := by
  set D := Real.sqrt (4 * q - t ^ 2) with hD
  have hDsq : D ^ 2 = 4 * q - t ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨⟨t / 2, D / 2⟩, ⟨t / 2, -(D / 2)⟩, ?_, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp
    · simp
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re]
      nlinarith
    · simp only [Complex.mul_im, Complex.ofReal_im]
      ring
  · rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only
    nlinarith
  · rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only
    nlinarith

/-! ### Damping domination -/

/-- The Frobenius polynomial `P(w) = 1 - t w + q w²`, the denominator of the ringdown. -/
def frobPolyGenusOne (q t : ℝ) (w : ℂ) : ℂ := 1 - t * w + q * w ^ 2

/-- On the unit circle, extra damping loses at most a factor of two. -/
theorem norm_one_sub_le_two_mul {z : ℂ} (hz : ‖z‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ‖1 - z‖ ≤ 2 * ‖1 - (ρ : ℂ) * z‖ := by
  have hρn : ‖((1 - ρ : ℝ) : ℂ) * z‖ = 1 - ρ := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h1 : 1 - ρ ≤ ‖1 - (ρ : ℂ) * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((ρ : ℂ) * z)
    rw [norm_one, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] at this
    exact this
  have e : 1 - z = (1 - (ρ : ℂ) * z) - ((1 - ρ : ℝ) : ℂ) * z := by
    push_cast
    ring
  calc ‖1 - z‖ = ‖(1 - (ρ : ℂ) * z) - ((1 - ρ : ℝ) : ℂ) * z‖ := by rw [← e]
    _ ≤ ‖1 - (ρ : ℂ) * z‖ + ‖((1 - ρ : ℝ) : ℂ) * z‖ := norm_sub_le _ _
    _ ≤ 2 * ‖1 - (ρ : ℂ) * z‖ := by rw [hρn]; linarith

/-- **Damping domination.** Extra uniform damping amplifies the response of the critical circle by a
bounded factor exactly when no mode is slower than universal. So damping domination is the statement of
universal damping, not a consequence of the wave dynamics. -/
theorem damping_domination_iff {q t : ℝ} (hq : 0 < q) :
    (∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → ∀ w : ℂ, q * Complex.normSq w = 1 →
      ‖frobPolyGenusOne q t w‖ ≤ C * ‖frobPolyGenusOne q t ((ρ : ℂ) * w)‖) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hlt
    obtain ⟨x, x', hsum, hprod, hbig, hsmall⟩ := exists_slow_mode hq (not_le.mp hlt)
    have hx0 : x ≠ 0 := by
      rintro rfl
      nlinarith
    set r := Real.sqrt q with hr
    have hrsq : r ^ 2 = q := Real.sq_sqrt hq.le
    have hrpos : 0 < r := Real.sqrt_pos.mpr hq
    have hxabs : r < |x| := by
      have : r ^ 2 < |x| ^ 2 := by rw [sq_abs, hrsq]; exact hbig
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg x) this
    set σ : ℝ := ((SignType.sign x : SignType) : ℝ) with hσ
    have hsign : σ ^ 2 = 1 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · simp [hσ, sign_neg h]
      · simp [hσ, sign_pos h]
    have hab : σ * |x| = x := sign_mul_abs x
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx0
    have hσx : σ * x = |x| := by linear_combination (-σ) * hab + |x| * hsign
    set w₀ : ℝ := σ / r with hw₀
    have hw₀sq : q * w₀ ^ 2 = 1 := by
      rw [hw₀, div_pow, hsign, hrsq]
      field_simp
    set ρ : ℝ := r / |x| with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      rw [hρ, div_lt_one (abs_pos.mpr hx0)]
      exact hxabs
    have hρw : ρ * w₀ = 1 / x := by
      have e1 : r / |x| * (σ / r) = σ / |x| := by
        field_simp
      rw [hρ, hw₀, e1, div_eq_div_iff habs hx0]
      linarith
    have hzero : frobPolyGenusOne q t (((ρ : ℂ)) * (w₀ : ℂ)) = 0 := by
      unfold frobPolyGenusOne
      have e : ((ρ : ℂ)) * (w₀ : ℂ) = ((1 / x : ℝ) : ℂ) := by
        rw [← hρw]
        push_cast
        ring
      rw [e, ← hsum, ← hprod]
      have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
      push_cast
      field_simp
      ring
    have hle := hC ρ hρ0 hρ1 (w₀ : ℂ) (by rw [Complex.normSq_ofReal]; nlinarith)
    rw [hzero, norm_zero, mul_zero] at hle
    have hnz : frobPolyGenusOne q t (w₀ : ℂ) = 0 := norm_le_zero_iff.mp hle
    unfold frobPolyGenusOne at hnz
    have hreal : 1 - t * w₀ + q * w₀ ^ 2 = 0 := by exact_mod_cast hnz
    have h2 : t * w₀ = 2 := by linarith
    have hfin : t ^ 2 = 4 * q := by
      have : (t * w₀) ^ 2 = 4 := by rw [h2]; norm_num
      nlinarith
    exact hlt (le_of_eq hfin)
  · intro h
    refine ⟨4, fun ρ hρ0 hρ1 w hw => ?_⟩
    obtain ⟨α, β, hsum, hprod, hnα', hnβ'⟩ := exists_roots_on_circle h
    have hP (z : ℂ) : frobPolyGenusOne q t z = (1 - α * z) * (1 - β * z) := by
      unfold frobPolyGenusOne
      rw [← hsum, ← hprod]
      ring
    have hnw : Real.sqrt q * ‖w‖ = 1 := by
      rw [Complex.norm_def, ← Real.sqrt_mul hq.le, hw, Real.sqrt_one]
    have hnα : ‖α * w‖ = 1 := by rw [norm_mul, hnα', hnw]
    have hnβ : ‖β * w‖ = 1 := by rw [norm_mul, hnβ', hnw]
    have e1 : ∀ c : ℂ, c * ((ρ : ℂ) * w) = (ρ : ℂ) * (c * w) := fun c => by ring
    rw [hP, hP, norm_mul, norm_mul, e1, e1]
    have b1 := norm_one_sub_le_two_mul hnα hρ0 hρ1
    have b2 := norm_one_sub_le_two_mul hnβ hρ0 hρ1
    calc ‖1 - α * w‖ * ‖1 - β * w‖
        ≤ (2 * ‖1 - (ρ : ℂ) * (α * w)‖) * (2 * ‖1 - (ρ : ℂ) * (β * w)‖) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ = 4 * (‖1 - (ρ : ℂ) * (α * w)‖ * ‖1 - (ρ : ℂ) * (β * w)‖) := by ring

/-! ### Integer probes -/

/-- **The sign on the integer lattice decides.** The Krein square of a state is nonnegative on all pairs of integers
exactly when it is nonnegative everywhere. So if the Krein squares of integer probes are counts, as the degrees of
endomorphisms are, the oscillator is not overdamped. This is Hasse's argument in the language of the ringdown; a fake black
hole has an integer probe with negative Krein square. -/
theorem integer_kreinSquare_nonneg_iff {q t : ℝ} :
    (∀ m n : ℤ, 0 ≤ kreinSquare q t (n : ℝ) (m : ℝ)) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    by_contra hlt
    have hlt' : 4 * q < t ^ 2 := not_le.mp hlt
    set D := Real.sqrt (t ^ 2 - 4 * q) with hD
    have hDsq : D ^ 2 = t ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
    have hDpos : 0 < D := Real.sqrt_pos.mpr (by linarith)
    set r₁ := (t - D) / 2 with hr₁
    set r₂ := (t + D) / 2 with hr₂
    have hgap : r₂ - r₁ = D := by
      rw [hr₁, hr₂]
      ring
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / D)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hND : 1 < N * D := by
      rw [div_lt_iff₀ hDpos] at hN
      exact hN
    set m : ℤ := ⌊r₁ * N⌋ + 1 with hm
    have hm1 : r₁ * N < (m : ℝ) := by
      rw [hm]
      push_cast
      exact Int.lt_floor_add_one _
    have hm2 : (m : ℝ) < r₂ * N := by
      have hfl : ((⌊r₁ * N⌋ : ℤ) : ℝ) ≤ r₁ * N := Int.floor_le _
      rw [hm]
      push_cast
      have : r₂ * N = r₁ * N + N * D := by
        rw [← hgap]
        ring
      linarith
    have hval := h m (N : ℤ)
    unfold kreinSquare at hval
    push_cast at hval
    have hfac : (m : ℝ) ^ 2 - t * N * m + q * (N : ℝ) ^ 2 =
        ((m : ℝ) - r₁ * N) * ((m : ℝ) - r₂ * N) := by
      have e : r₁ * r₂ = q := by
        rw [hr₁, hr₂]
        nlinarith
      have e2 : r₁ + r₂ = t := by
        rw [hr₁, hr₂]
        ring
      rw [← e, ← e2]
      ring
    have hneg : ((m : ℝ) - r₁ * N) * ((m : ℝ) - r₂ * N) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  · intro h m n
    exact kreinSquare_nonneg_iff.mpr h _ _

/-! ### The rate of the reflected signal -/

/-- The Lucas sequence with two given roots. -/
theorem lucas_mul_sub (α β : ℂ) (n : ℕ) :
    (α - β) * lucas (α * β) (α + β) n = α ^ (n + 1) - β ^ (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucas]
  | one => simp only [lucas]; ring
  | more n h0 h1 =>
    rw [lucas_add_two]
    have e : (α - β) * ((α + β) * lucas (α * β) (α + β) (n + 1) - α * β * lucas (α * β) (α + β) n) =
        (α + β) * ((α - β) * lucas (α * β) (α + β) (n + 1)) -
          α * β * ((α - β) * lucas (α * β) (α + β) n) := by ring
    rw [e, h0, h1]
    ring

/-- The auxiliary form of the Lucas sequence, summing `α^i β^{n-i}` by a recursion. -/
def lucasAux (α β : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => α * lucasAux α β n + β ^ (n + 1)

theorem lucas_eq_aux (α β : ℂ) (n : ℕ) : lucas (α * β) (α + β) n = lucasAux α β n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [lucas, lucasAux]
  | more n h0 h1 =>
    rw [lucas_add_two, h0, h1]
    simp only [lucasAux]
    ring

/-- On the universal circle the Lucas sequence has size at most `(n + 1) r^n`. -/
theorem norm_lucasAux_le {α β : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ‖α‖ = r) (hβ : ‖β‖ = r) (n : ℕ) :
    ‖lucasAux α β n‖ ≤ (n + 1) * r ^ n := by
  induction n with
  | zero => simp [lucasAux]
  | succ n ih =>
    simp only [lucasAux]
    calc ‖α * lucasAux α β n + β ^ (n + 1)‖
        ≤ ‖α‖ * ‖lucasAux α β n‖ + ‖β‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ r * ((n + 1) * r ^ n) + r ^ (n + 1) := by
          rw [hα, hβ]
          gcongr
      _ = ((n + 1 : ℕ) + 1) * r ^ (n + 1) := by
          push_cast
          ring

/-- **The universal rate of a mixed signal.** A combination `A l_{n+1} + B l_n` of the Lucas sequence has size
`O((n+1) q^{n/2})` exactly when the oscillator is not overdamped, provided the slow mode is excited, that is,
`A x + B ≠ 0` at the real modes. -/
theorem lucasMix_rate_iff {q t A B : ℝ} (hq : 0 < q)
    (hex : ∀ x : ℝ, x ^ 2 - t * x + q = 0 → A * x + B ≠ 0) :
    (∃ C : ℝ, ∀ n : ℕ,
      ‖(A : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) + (B : ℂ) * lucas (q : ℂ) (t : ℂ) n‖ ≤
        C * (n + 1) * Real.sqrt q ^ n) ↔ t ^ 2 ≤ 4 * q := by
  set r := Real.sqrt q with hr
  have hrsq : r ^ 2 = q := Real.sq_sqrt hq.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hq
  constructor
  · rintro ⟨C, hC⟩
    by_contra hlt
    obtain ⟨x, x', hsum, hprod, hbig, hsmall⟩ := exists_slow_mode hq (not_le.mp hlt)
    have hx0 : x ≠ 0 := by
      rintro rfl
      nlinarith
    have hne : x ≠ x' := by
      rintro rfl
      nlinarith
    have hxex : A * x + B ≠ 0 := hex x (by rw [← hsum, ← hprod]; ring)
    -- the closed form
    have hclosed (n : ℕ) : ((x - x' : ℝ) : ℂ) *
        ((A : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) + (B : ℂ) * lucas (q : ℂ) (t : ℂ) n) =
        (((x ^ (n + 1) * (A * x + B) - x' ^ (n + 1) * (A * x' + B) : ℝ)) : ℂ) := by
      have hqc : (q : ℂ) = (x : ℂ) * x' := by
        rw [← hprod]
        push_cast
        ring
      have htc : (t : ℂ) = (x : ℂ) + x' := by
        rw [← hsum]
        push_cast
        ring
      rw [hqc, htc]
      have h1 := lucas_mul_sub (x : ℂ) x' (n + 1)
      have h0 := lucas_mul_sub (x : ℂ) x' n
      push_cast
      linear_combination (A : ℂ) * h1 + (B : ℂ) * h0
    set a := |x| / r with ha
    have hxabs : r < |x| := by
      have : r ^ 2 < |x| ^ 2 := by rw [sq_abs, hrsq]; exact hbig
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg x) this
    have ha1 : 1 < a := by
      rw [ha, one_lt_div hrpos]
      exact hxabs
    have hx'abs : |x'| < r := by
      have : |x'| ^ 2 < r ^ 2 := by rw [sq_abs, hrsq]; exact hsmall
      exact lt_of_pow_lt_pow_left₀ 2 hrpos.le this
    set E := |x| * |A * x + B| with hE
    have hEpos : 0 < E := mul_pos (abs_pos.mpr hx0) (abs_pos.mpr hxex)
    set F := |x'| * |A * x' + B| with hF
    have hFnn : 0 ≤ F := by positivity
    set C' := |C| * |x - x'| with hC'
    have hbound (n : ℕ) : a ^ n * E ≤ C' * (n + 1) + F := by
      have h1 := hC n
      have h2 := hclosed n
      have hnorm : |x - x'| *
          ‖(A : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) + (B : ℂ) * lucas (q : ℂ) (t : ℂ) n‖ =
          |x ^ (n + 1) * (A * x + B) - x' ^ (n + 1) * (A * x' + B)| := by
        have := congrArg norm h2
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at this
        exact this
      have hrn : 0 < r ^ n := pow_pos hrpos n
      have h3 : |x| ^ (n + 1) * |A * x + B| - |x'| ^ (n + 1) * |A * x' + B| ≤
          |x ^ (n + 1) * (A * x + B) - x' ^ (n + 1) * (A * x' + B)| := by
        have := abs_sub_abs_le_abs_sub (x ^ (n + 1) * (A * x + B)) (x' ^ (n + 1) * (A * x' + B))
        simpa [abs_mul, abs_pow] using this
      have h4 : |x'| ^ (n + 1) * |A * x' + B| ≤ F * r ^ n := by
        have : |x'| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg _) hx'abs.le n
        calc |x'| ^ (n + 1) * |A * x' + B| = |x'| ^ n * F := by rw [hF, pow_succ]; ring
          _ ≤ r ^ n * F := mul_le_mul_of_nonneg_right this hFnn
          _ = F * r ^ n := by ring
      have h5 : |x| ^ (n + 1) * |A * x + B| = a ^ n * E * r ^ n := by
        rw [ha, hE, div_pow, pow_succ]
        field_simp
      have h6 : |x - x'| *
          ‖(A : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) + (B : ℂ) * lucas (q : ℂ) (t : ℂ) n‖ ≤
          C' * (n + 1) * r ^ n := by
        have hC1 : C * (n + 1) * r ^ n ≤ |C| * (n + 1) * r ^ n := by
          gcongr
          exact le_abs_self C
        have := mul_le_mul_of_nonneg_left (h1.trans hC1) (abs_nonneg (x - x'))
        calc _ ≤ |x - x'| * (|C| * (n + 1) * r ^ n) := this
          _ = _ := by rw [hC']; ring
      have h7 : a ^ n * E * r ^ n ≤ (C' * (n + 1) + F) * r ^ n := by
        rw [← h5, add_mul]
        linarith [hnorm ▸ h6]
      exact le_of_mul_le_mul_right h7 hrn
    -- exponential beats linear
    have ht1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / a ^ n) atTop (𝓝 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt 1 ha1
    have ht2 : Tendsto (fun n : ℕ => (1 / a) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (by rw [div_lt_one (by linarith)]; exact ha1)
    have ht3 : Tendsto (fun n : ℕ => C' * ((n : ℝ) ^ 1 / a ^ n) + (C' + F) * (1 / a) ^ n) atTop
        (𝓝 (C' * 0 + (C' + F) * 0)) :=
      (ht1.const_mul C').add (ht2.const_mul (C' + F))
    simp only [mul_zero, add_zero] at ht3
    have hev := ht3.eventually (gt_mem_nhds hEpos)
    obtain ⟨n, hn⟩ := hev.exists
    have han : 0 < a ^ n := pow_pos (by linarith) n
    have h8 := hbound n
    have h9 : C' * ((n : ℝ) ^ 1 / a ^ n) + (C' + F) * (1 / a) ^ n = (C' * (n + 1) + F) / a ^ n := by
      rw [one_div, inv_pow]
      field_simp
      ring
    rw [h9, div_lt_iff₀ han] at hn
    linarith
  · intro h
    obtain ⟨α, β, hsum, hprod, hnα, hnβ⟩ := exists_roots_on_circle h
    refine ⟨|A| * r * 2 + |B|, fun n => ?_⟩
    rw [← hsum, ← hprod, lucas_eq_aux, lucas_eq_aux]
    have b1 := norm_lucasAux_le hrpos.le hnα hnβ (n + 1)
    have b0 := norm_lucasAux_le hrpos.le hnα hnβ n
    have hrn : 0 ≤ r ^ n := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hAA : 0 ≤ |A| := abs_nonneg A
    have hBB : 0 ≤ |B| := abs_nonneg B
    calc ‖(A : ℂ) * lucasAux α β (n + 1) + (B : ℂ) * lucasAux α β n‖
        ≤ |A| * ‖lucasAux α β (n + 1)‖ + |B| * ‖lucasAux α β n‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ |A| * (((n + 1 : ℕ) + 1) * r ^ (n + 1)) + |B| * ((n + 1) * r ^ n) := by
          gcongr
      _ ≤ (|A| * r * 2 + |B|) * (n + 1) * r ^ n := by
          push_cast
          have h1 : ((n : ℝ) + 1 + 1) * r ^ (n + 1) ≤ r * 2 * (n + 1) * r ^ n := by
            rw [pow_succ]
            have h2 : (0 : ℝ) ≤ r * r ^ n := by positivity
            nlinarith
          have h3 := mul_le_mul_of_nonneg_left h1 hAA
          nlinarith

/-- **The universal rate of the reflected signal.** The ringdown signal has size `O((n+1) q^{n/2})` exactly
when the oscillator is not overdamped. Above the critical discriminant the slow mode is excited, because
`h' ≠ 0`. So the universal rate is a statement about the signal only under universal damping. -/
theorem ringSignal_rate_iff {q t : ℝ} (hq : 0 < q) (hh : q + 1 + t ≠ 0) :
    (∃ C : ℝ, ∀ n : ℕ, ‖ringSignal (q : ℂ) (t : ℂ) n‖ ≤ C * (n + 1) * Real.sqrt q ^ n) ↔
      t ^ 2 ≤ 4 * q := by
  have h := lucasMix_rate_iff (q := q) (t := t) (A := 1) (B := q) hq (by
    intro x hx hzero
    apply hh
    have hx' : x = -q := by linarith
    rw [hx'] at hx
    have : q * (q + 1 + t) = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_left hq.ne')
  simp only [Complex.ofReal_one, one_mul] at h
  exact h

end GaloisForLFunctions.ArithmeticScatteringHolography

end
