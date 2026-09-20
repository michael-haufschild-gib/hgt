/-
The pool-form torus supply: every quadrant at every scale, in Chebyshev bulk.

The two-phase window construction places a full fast quarter-tile inside the slow
difference window; here the window is kept as a set rather than sampled once — EVERY
prime of the multiplicative window `(e^W, e^{W+π/(4a)}]` has its fast phase in the
prescribed quarter-tile and its difference phase within `π/8` of the target, and the
window scale `W` is pinned to `[X, X + 5π/(a−b) + 2π/a]`.  The window's logarithmic
length exceeds `log 2`, so Chebyshev's bounds give its prime count a divergent floor:
each sign quadrant of the two-frequency sine pair is realized not by isolated primes
but by pools of unboundedly many, all with the same `√2/2` sine floor and, at the
basepoint tilts, magnitude floors and ceilings at the same exponent `Re ρ`.  These
pools are the fuel of the staircase descent.
-/
import GaloisForLFunctions.RHTower.TorusWalk
import GaloisForLFunctions.RHTower.StaircaseDescent

noncomputable section

namespace RHTower

open Complex Metric Finset

/-- **The two-phase window pool**: for nearby frequencies `b < a` with `9(a−b) ≤ a`
and `a·(4 log 2) < π`, any fast offset `o`, any difference target `d ∈ [0, π]`, and
any base scale `X ≥ 0`, there is a window position `W ∈ [X, X + 5π/(a−b) + 2π/a]`
such that EVERY prime of the multiplicative window `(e^W, e^{W+π/(4a)}]` has fast
phase `a·log q` in the quarter-tile `(o, o + π/4]` mod `2π` and difference phase
`(a−b)·log q` within `π/8` of `d` mod `2π`. -/
theorem two_phase_window_pool {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hnarrow : 9 * (a - b) ≤ a)
    {o d : ℝ} (hd : 0 ≤ d) (hdπ : d ≤ Real.pi) {X : ℝ} (hX : 0 ≤ X) :
    ∃ (W : ℝ) (m j : ℤ), X ≤ W ∧ W ≤ X + 5 * Real.pi / (a - b) + 2 * Real.pi / a ∧
      ∀ q ∈ windowPrimes (Real.exp W) (Real.exp (W + Real.pi / (4 * a))),
        a * Real.log q - 2 * Real.pi * m ∈ Set.Ioc o (o + Real.pi / 4) ∧
        (a - b) * Real.log q - 2 * Real.pi * j
          ∈ Set.Ioc (d - Real.pi / 8) (d + Real.pi / 8) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hΔ : (0 : ℝ) < a - b := sub_pos.mpr hba
  have ha : (0 : ℝ) < a := lt_trans hb hba
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  -- the difference-window index, controlled on both sides
  set r : ℝ := ((a - b) * X + Real.pi / 8) / (2 * Real.pi) with hrdef
  have hr0 : 0 ≤ r := by
    have h1 : 0 ≤ (a - b) * X := mul_nonneg hΔ.le hX
    rw [hrdef]
    exact div_nonneg (by linarith) h2pi.le
  set j : ℕ := ⌈r⌉₊ + 1 with hjdef
  have hjlo : r < (j : ℝ) := by
    have h := Nat.le_ceil r
    rw [hjdef]
    push_cast
    linarith
  have hjhi : (j : ℝ) ≤ r + 2 := by
    have h := Nat.ceil_lt_add_one hr0
    rw [hjdef]
    push_cast
    linarith
  set Jl : ℝ := (2 * Real.pi * (j : ℝ) + d - Real.pi / 8) / (a - b) with hJldef
  set Jr : ℝ := (2 * Real.pi * (j : ℝ) + d + Real.pi / 8) / (a - b) with hJrdef
  have h2pir : 2 * Real.pi * r = (a - b) * X + Real.pi / 8 := by
    rw [hrdef, mul_comm, div_mul_cancel₀ _ h2pi.ne']
  have hJlX : X < Jl := by
    rw [hJldef, lt_div_iff₀ hΔ]
    have h1 : 2 * Real.pi * r < 2 * Real.pi * (j : ℝ) :=
      mul_lt_mul_of_pos_left hjlo h2pi
    have hcomm : X * (a - b) = (a - b) * X := mul_comm _ _
    linarith
  have hJlJr : Jr - Jl = (Real.pi / 4) / (a - b) := by
    rw [hJrdef, hJldef, div_sub_div_same]
    congr 1
    ring
  have hJlhi : Jl ≤ X + 5 * Real.pi / (a - b) := by
    have h2 : 2 * Real.pi * (j : ℝ) ≤ (a - b) * X + Real.pi / 8 + 4 * Real.pi := by
      have h := mul_le_mul_of_nonneg_left hjhi h2pi.le
      have hexpand : 2 * Real.pi * (r + 2) = 2 * Real.pi * r + 4 * Real.pi := by ring
      linarith
    rw [hJldef, div_le_iff₀ hΔ]
    have hexp : (X + 5 * Real.pi / (a - b)) * (a - b)
        = X * (a - b) + 5 * Real.pi := by
      rw [add_mul, div_mul_cancel₀ _ hΔ.ne']
    rw [hexp]
    have hcomm : X * (a - b) = (a - b) * X := mul_comm _ _
    linarith
  -- the full fast tile inside the difference window
  set m : ℤ := ⌈(a * Jl - o) / (2 * Real.pi)⌉ with hmdef
  set Wl : ℝ := (2 * Real.pi * (m : ℝ) + o) / a with hWldef
  have hWlJl : Jl ≤ Wl := by
    have hceil : (a * Jl - o) / (2 * Real.pi) ≤ (m : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ h2pi] at hceil
    rw [hWldef, le_div_iff₀ ha]
    linarith
  have hWlJl2 : Wl ≤ Jl + 2 * Real.pi / a := by
    have hceil : (m : ℝ) < (a * Jl - o) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    have hceil1 : (m : ℝ) - 1 < (a * Jl - o) / (2 * Real.pi) := by linarith
    rw [lt_div_iff₀ h2pi] at hceil1
    have hcancel : 2 * Real.pi / a * a = 2 * Real.pi := div_mul_cancel₀ _ ha.ne'
    rw [hWldef, div_le_iff₀ ha]
    linarith
  have hWrJr : Wl + Real.pi / (4 * a) ≤ Jr := by
    have h0 : 2 * Real.pi / a = 8 * Real.pi / (4 * a) := by
      rw [div_eq_div_iff ha.ne' (by positivity : (4 : ℝ) * a ≠ 0)]
      ring
    have hfit : 2 * Real.pi / a + Real.pi / (4 * a) ≤ (Real.pi / 4) / (a - b) := by
      rw [h0, ← add_div, div_le_div_iff₀ (by positivity) hΔ]
      nlinarith
    linarith
  refine ⟨Wl, m, (j : ℤ), le_of_lt (lt_of_lt_of_le hJlX hWlJl), by linarith, ?_⟩
  intro q hq
  obtain ⟨hprime, hlo, hhi⟩ :=
    (mem_windowPrimes (Real.exp_pos _).le (Real.exp_pos _).le).mp hq
  have hq0 : (0 : ℝ) < q := lt_trans (Real.exp_pos _) hlo
  have hlog_lo : Wl < Real.log q := by
    rw [← Real.log_exp Wl]
    exact Real.log_lt_log (Real.exp_pos _) hlo
  have hlog_hi : Real.log q ≤ Wl + Real.pi / (4 * a) := by
    rw [← Real.log_exp (Wl + Real.pi / (4 * a))]
    exact Real.log_le_log hq0 hhi
  have haWl : a * Wl = 2 * Real.pi * (m : ℝ) + o := by
    rw [hWldef, mul_comm, div_mul_cancel₀ _ ha.ne']
  have haWr : a * (Wl + Real.pi / (4 * a))
      = 2 * Real.pi * (m : ℝ) + o + Real.pi / 4 := by
    rw [mul_add, haWl, show a * (Real.pi / (4 * a)) = Real.pi / 4 from by
      rw [mul_comm (4 : ℝ) a, ← div_div, ← mul_div_assoc,
        mul_comm a (Real.pi / a), div_mul_cancel₀ _ ha.ne']]
  constructor
  · constructor
    · have h := mul_lt_mul_of_pos_left hlog_lo ha
      rw [haWl] at h
      linarith
    · have h := mul_le_mul_of_nonneg_left hlog_hi ha.le
      rw [haWr] at h
      linarith
  · constructor
    · have h := mul_lt_mul_of_pos_left (lt_of_le_of_lt hWlJl hlog_lo) hΔ
      have hΔJl : (a - b) * Jl = 2 * Real.pi * (j : ℝ) + d - Real.pi / 8 := by
        rw [hJldef, mul_comm, div_mul_cancel₀ _ hΔ.ne']
      rw [hΔJl] at h
      push_cast
      linarith
    · have h := mul_le_mul_of_nonneg_left (le_trans hlog_hi hWrJr) hΔ.le
      have hΔJr : (a - b) * Jr = 2 * Real.pi * (j : ℝ) + d + Real.pi / 8 := by
        rw [hJrdef, mul_comm, div_mul_cancel₀ _ hΔ.ne']
      rw [hΔJr] at h
      push_cast
      linarith

/-- **The quadrant pool at the sine level**: every sign pair of the two-frequency
sines is realized by the FULL prime pool of a multiplicative window of logarithmic
length `π/(4a) > log 2`, at a controlled scale, with the uniform `√2/2` floor on both
sine magnitudes. -/
theorem sin_sign_pair_pool {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hnarrow : 9 * (a - b) ≤ a)
    (ε₁ ε₂ : Bool) {X : ℝ} (hX : 0 ≤ X) :
    ∃ W : ℝ, X ≤ W ∧ W ≤ X + 5 * Real.pi / (a - b) + 2 * Real.pi / a ∧
      ∀ q ∈ windowPrimes (Real.exp W) (Real.exp (W + Real.pi / (4 * a))),
        (if ε₁ then 0 < Real.sin (a * Real.log q)
          else Real.sin (a * Real.log q) < 0) ∧
        (if ε₂ then 0 < Real.sin (b * Real.log q)
          else Real.sin (b * Real.log q) < 0) ∧
        Real.sqrt 2 / 2 ≤ |Real.sin (a * Real.log q)| ∧
        Real.sqrt 2 / 2 ≤ |Real.sin (b * Real.log q)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  cases ε₁ <;> cases ε₂
  · -- fast negative, slow negative: difference near 0
    obtain ⟨W, m, j, hW1, hW2, hmem⟩ := two_phase_window_pool hb hba hnarrow
      (o := 11 * Real.pi / 8) (d := 0) le_rfl hpi.le hX
    refine ⟨W, hW1, hW2, fun q hq => ?_⟩
    obtain ⟨hfast, hdiff⟩ := hmem q hq
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply sin_neg_of_shifted_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply sin_neg_of_shifted_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
    · apply abs_sin_floor_neg_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply abs_sin_floor_neg_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
  · -- fast negative, slow positive: difference near π
    obtain ⟨W, m, j, hW1, hW2, hmem⟩ := two_phase_window_pool hb hba hnarrow
      (o := 11 * Real.pi / 8) (d := Real.pi) hpi.le le_rfl hX
    refine ⟨W, hW1, hW2, fun q hq => ?_⟩
    obtain ⟨hfast, hdiff⟩ := hmem q hq
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply sin_neg_of_shifted_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply sin_pos_of_shifted_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
    · apply abs_sin_floor_neg_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply abs_sin_floor_pos_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
  · -- fast positive, slow negative: difference near π
    obtain ⟨W, m, j, hW1, hW2, hmem⟩ := two_phase_window_pool hb hba hnarrow
      (o := 3 * Real.pi / 8) (d := Real.pi) hpi.le le_rfl hX
    refine ⟨W, hW1, hW2, fun q hq => ?_⟩
    obtain ⟨hfast, hdiff⟩ := hmem q hq
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply sin_pos_of_shifted_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply sin_neg_of_shifted_window (m := m - j - 1)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
    · apply abs_sin_floor_pos_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply abs_sin_floor_neg_window (m := m - j - 1)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
  · -- fast positive, slow positive: difference near 0
    obtain ⟨W, m, j, hW1, hW2, hmem⟩ := two_phase_window_pool hb hba hnarrow
      (o := 3 * Real.pi / 8) (d := 0) le_rfl hpi.le hX
    refine ⟨W, hW1, hW2, fun q hq => ?_⟩
    obtain ⟨hfast, hdiff⟩ := hmem q hq
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply sin_pos_of_shifted_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply sin_pos_of_shifted_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith
    · apply abs_sin_floor_pos_window (m := m)
      · have := hfast.1; linarith
      · have := hfast.2; linarith
    · apply abs_sin_floor_pos_window (m := m - j)
      · have h1 := hfast.1; have h2 := hdiff.2; push_cast; linarith
      · have h1 := hfast.2; have h2 := hdiff.1; push_cast; linarith

/-- **The quadrant pool for the tilts at the basepoints**: every sign pair of the two
steering-tilt increments at `ρ ± ci` is realized by the full prime pool of a
scale-controlled multiplicative window, each element carrying the arctangent floor at
the basepoint exponent `Re ρ`. -/
theorem tilt_sign_pair_pool_base {ρ : ℂ} {c : ℝ} (hre0 : 0 < ρ.re)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (ε₁ ε₂ : Bool) {X : ℝ} (hX : 0 ≤ X) :
    ∃ W : ℝ, X ≤ W ∧
      W ≤ X + 5 * Real.pi / (2 * c) + 2 * Real.pi / (ρ.im + c) ∧
      ∀ q ∈ windowPrimes (Real.exp W)
          (Real.exp (W + Real.pi / (4 * (ρ.im + c)))),
        (if ε₁ then 0 < primeTilt q (ρ + (c : ℂ) * I)
          else primeTilt q (ρ + (c : ℂ) * I) < 0) ∧
        (if ε₂ then 0 < primeTilt q (ρ - (c : ℂ) * I)
          else primeTilt q (ρ - (c : ℂ) * I) < 0) ∧
        Real.arctan ((q : ℝ) ^ (-ρ.re) * (Real.sqrt 2 / 2) / 2)
          ≤ |primeTilt q (ρ + (c : ℂ) * I)| ∧
        Real.arctan ((q : ℝ) ^ (-ρ.re) * (Real.sqrt 2 / 2) / 2)
          ≤ |primeTilt q (ρ - (c : ℂ) * I)| := by
  have himp : (ρ + (c : ℂ) * I).im = ρ.im + c := by simp
  have himm : (ρ - (c : ℂ) * I).im = ρ.im - c := by simp
  have hrep : (ρ + (c : ℂ) * I).re = ρ.re := by simp
  have hrem : (ρ - (c : ℂ) * I).re = ρ.re := by simp
  have hb : (0 : ℝ) < ρ.im - c := sub_pos.mpr hcτ
  have hba : ρ.im - c < ρ.im + c := by linarith
  have hnarrow' : 9 * ((ρ.im + c) - (ρ.im - c)) ≤ ρ.im + c := by
    have h : (ρ.im + c) - (ρ.im - c) = 2 * c := by ring
    rw [h]
    exact hnarrow
  obtain ⟨W, hW1, hW2, hmem⟩ :=
    sin_sign_pair_pool hb hba hnarrow' ε₁ ε₂ hX
  have hsub : (ρ.im + c) - (ρ.im - c) = 2 * c := by ring
  rw [hsub] at hW2
  refine ⟨W, hW1, hW2, fun q hq => ?_⟩
  have hprime : Nat.Prime q :=
    ((mem_windowPrimes (Real.exp_pos _).le (Real.exp_pos _).le).mp hq).1
  obtain ⟨hsin1, hsin2, hfl1, hfl2⟩ := hmem q hq
  have hrep0 : 0 < (ρ + (c : ℂ) * I).re := by rw [hrep]; exact hre0
  have hrem0 : 0 < (ρ - (c : ℂ) * I).re := by rw [hrem]; exact hre0
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases ε₁ with
    | false =>
      show primeTilt q (ρ + (c : ℂ) * I) < 0
      rw [primeTilt_neg_iff hprime.two_le hrep0, himp]
      exact hsin1
    | true =>
      show 0 < primeTilt q (ρ + (c : ℂ) * I)
      rw [primeTilt_pos_iff hprime.two_le hrep0, himp]
      exact hsin1
  · cases ε₂ with
    | false =>
      show primeTilt q (ρ - (c : ℂ) * I) < 0
      rw [primeTilt_neg_iff hprime.two_le hrem0, himm]
      exact hsin2
    | true =>
      show 0 < primeTilt q (ρ - (c : ℂ) * I)
      rw [primeTilt_pos_iff hprime.two_le hrem0, himm]
      exact hsin2
  · have h := abs_primeTilt_floor hprime.two_le hrep0 (by rw [himp]; exact hfl1)
    rwa [hrep] at h
  · have h := abs_primeTilt_floor hprime.two_le hrem0 (by rw [himm]; exact hfl2)
    rwa [hrem] at h

/-- **The pool count at a controlled scale**: a multiplicative window of logarithmic
length `L > log 2` positioned anywhere in `[X, X + Bt − L]` contains at least `N`
primes as soon as the Chebyshev mass `e^X·(e^L·log 2 − log 4)` dominates
`N·(X + Bt)` plus the explicit lower-order terms.  The mass is evaluated at the left
scale, the divisor `log y` and the defect terms at the right — so one budget
inequality serves every window of the batch. -/
theorem windowPrimes_card_of_scale {L : ℝ} (hL2 : Real.log 2 < L) {W X Bt : ℝ}
    (hX : 0 ≤ X) (hWlo : X ≤ W) (hWhi : W + L ≤ X + Bt) {N : ℝ} (hN : 0 ≤ N)
    (hbudget : N * (X + Bt) + Real.log 2 + Real.log 3 + (X + Bt)
        + 8 * Real.exp (3 * (X + Bt) / 4)
      ≤ Real.exp X * (Real.exp L * Real.log 2 - Real.log 4)) :
    N ≤ ((windowPrimes (Real.exp W) (Real.exp (W + L))).card : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) < L := lt_trans hlog2 hL2
  set x : ℝ := Real.exp W with hxdef
  set y : ℝ := Real.exp (W + L) with hydef
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hxdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hxy : x ≤ y := Real.exp_le_exp.mpr (by linarith)
  have hy1 : (1 : ℝ) ≤ y := le_trans hx1 hxy
  have hcard := windowPrimes_card_ge hx1 hxy
  have hlogy : Real.log y = W + L := Real.log_exp _
  have hlogy_pos : 0 < Real.log y := by rw [hlogy]; linarith
  have hlogy_le : Real.log y ≤ X + Bt := by rw [hlogy]; linarith
  have hXBt0 : 0 < X + Bt := by linarith
  have hyx : y = x * Real.exp L := by rw [hydef, hxdef, ← Real.exp_add]
  -- the lower-order terms, bounded at the right endpoint of the batch
  have hlog_y2 : Real.log (y + 2) ≤ Real.log 3 + (X + Bt) := by
    have h32 : y + 2 ≤ 3 * y := by linarith
    have h := Real.log_le_log (by linarith : (0 : ℝ) < y + 2) h32
    rw [Real.log_mul (by norm_num) (by linarith : y ≠ 0)] at h
    linarith
  have hsqrt : Real.sqrt y = Real.exp ((W + L) / 2) := by
    rw [hydef, show Real.exp (W + L) = Real.exp ((W + L) / 2) ^ 2 from by
      rw [sq, ← Real.exp_add]; congr 1; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hsqrt_le : Real.sqrt y ≤ Real.exp ((X + Bt) / 2) := by
    rw [hsqrt]
    exact Real.exp_le_exp.mpr (by linarith)
  have hXBt1 : X + Bt ≤ 4 * Real.exp ((X + Bt) / 4) := by
    have h1exp : (1 : ℝ) ≤ Real.exp (X + Bt) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hXBt0.le
    have h := log_le_mul_rpow h1exp (m := 4) (by norm_num)
    rw [Real.log_exp] at h
    have hpow : Real.exp (X + Bt) ^ ((1 : ℝ) / 4) = Real.exp ((X + Bt) / 4) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rwa [hpow] at h
  have hsq_term : 2 * Real.sqrt y * Real.log y ≤ 8 * Real.exp (3 * (X + Bt) / 4) := by
    have h3 : Real.exp ((X + Bt) / 2) * Real.exp ((X + Bt) / 4)
        = Real.exp (3 * (X + Bt) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hstep : 2 * Real.sqrt y * Real.log y
        ≤ 2 * Real.exp ((X + Bt) / 2) * (4 * Real.exp ((X + Bt) / 4)) := by
      have hmul := mul_le_mul (by linarith : 2 * Real.sqrt y ≤ 2 * Real.exp ((X + Bt) / 2))
        (le_trans hlogy_le hXBt1) hlogy_pos.le (by positivity)
      linarith
    have hcollect : 2 * Real.exp ((X + Bt) / 2) * (4 * Real.exp ((X + Bt) / 4))
        = 8 * (Real.exp ((X + Bt) / 2) * Real.exp ((X + Bt) / 4)) := by ring
    rw [hcollect, h3] at hstep
    exact hstep
  -- the Chebyshev mass beats the budget
  have hA0 : 0 < Real.exp L * Real.log 2 - Real.log 4 := by
    have h2 : (2 : ℝ) < Real.exp L := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp L := Real.exp_lt_exp.mpr hL2
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    nlinarith only [h2, hlog4, Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have hxX : Real.exp X ≤ x := Real.exp_le_exp.mpr hWlo
  have hylog : (y - 1) * Real.log 2 - Real.log 4 * x
      = x * (Real.exp L * Real.log 2 - Real.log 4) - Real.log 2 := by
    rw [hyx]
    ring
  have hx_lower : Real.exp X * (Real.exp L * Real.log 2 - Real.log 4)
      ≤ x * (Real.exp L * Real.log 2 - Real.log 4) :=
    mul_le_mul_of_nonneg_right hxX hA0.le
  have hmass : N * (X + Bt)
      ≤ (y - 1) * Real.log 2 - Real.log (y + 2) - 2 * Real.sqrt y * Real.log y
        - Real.log 4 * x := by
    linarith
  have hNlogy : N * Real.log y ≤ N * (X + Bt) :=
    mul_le_mul_of_nonneg_left hlogy_le hN
  exact le_of_mul_le_mul_right (by linarith) hlogy_pos

set_option maxHeartbeats 8000000 in
/-- **Pair-reachability of the two basepoint tilts** (nonnegative quadrant): for a
strip point `ρ` and a narrow height split `c`, the pair
`(anchorTilt P (ρ+ci), anchorTilt P (ρ−ci))` reaches any nonnegative target pair
within any tolerance, over finite prime sets avoiding any initial segment.  The
staircase consumes three quadrant pools drawn at one common scale `X`: the scale is
pushed until the pool ceilings fall below the tolerance and the Chebyshev mass
`e^X/X` of each window outgrows the `e^{Re ρ·X}` steps-per-target cost — possible
exactly because the floor and ceiling share the exponent `Re ρ < 1`. -/
theorem anchorTilt_pair_reachable_nonneg {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {Tp Tm : ℝ} (hTp : 0 ≤ Tp) (hTm : 0 ≤ Tm) {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      |Tp - anchorTilt P (ρ + (c : ℂ) * I)| ≤ ε ∧
      |Tm - anchorTilt P (ρ - (c : ℂ) * I)| ≤ ε := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : (0 : ℝ) < ρ.im + c := by linarith
  have hσ0 : 0 < ρ.re := hre0
  have hL2 : Real.log 2 < Real.pi / (4 * (ρ.im + c)) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * (ρ.im + c))]
    have hcomm : Real.log 2 * (4 * (ρ.im + c)) = (ρ.im + c) * (4 * Real.log 2) := by ring
    linarith
  have hL0 : 0 < Real.pi / (4 * (ρ.im + c)) := lt_trans hlog2 hL2
  set Bt : ℝ := 5 * Real.pi / (2 * c) + 2 * Real.pi / (ρ.im + c)
    + Real.pi / (4 * (ρ.im + c)) with hBtdef
  have hBt0 : 0 < Bt := by
    rw [hBtdef]
    have h1 : 0 < 5 * Real.pi / (2 * c) := div_pos (by linarith) (by linarith)
    have h2 : 0 < 2 * Real.pi / (ρ.im + c) := div_pos (by linarith) ha0
    linarith
  set A₀ : ℝ := Real.exp (Real.pi / (4 * (ρ.im + c))) * Real.log 2 - Real.log 4
    with hA₀def
  have hA₀0 : 0 < A₀ := by
    rw [hA₀def]
    have h2 : (2 : ℝ) < Real.exp (Real.pi / (4 * (ρ.im + c))) := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ < _ := Real.exp_lt_exp.mpr hL2
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    nlinarith only [h2, hlog4, Real.log_pos (by norm_num : (1:ℝ) < 2)]
  set m₀ : ℝ := 2 / (1 - ρ.re) with hm₀def
  have hm₀1 : 1 ≤ m₀ := by
    rw [hm₀def, le_div_iff₀ (by linarith)]
    linarith
  set M₁ : ℝ := m₀ * Real.exp Bt with hM₁def
  have hM₁0 : 0 < M₁ := by
    rw [hM₁def]
    exact mul_pos (by linarith) (Real.exp_pos _)
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set c₆ : ℝ := (Tp + Tm + 2) * (8 / Real.sqrt 2) * Real.exp (ρ.re * Bt) with hc₆def
  have hc₆0 : 0 < c₆ := by
    rw [hc₆def]
    have h1 : (0 : ℝ) < Tp + Tm + 2 := by linarith
    have h2 : (0 : ℝ) < 8 / Real.sqrt 2 := div_pos (by norm_num) hsqrt2
    exact mul_pos (mul_pos h1 h2) (Real.exp_pos _)
  set c₇ : ℝ := Real.log 2 + Real.log 3 with hc₇def
  have hc₇0 : 0 < c₇ := by
    rw [hc₇def]
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  set c₈ : ℝ := 8 * Real.exp (3 * Bt / 4) with hc₈def
  have hc₈0 : 0 < c₈ := by
    rw [hc₈def]
    exact mul_pos (by norm_num) (Real.exp_pos _)
  set K : ℝ := c₆ * M₁ + 3 * M₁ + c₇ + c₈ with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have h1 : 0 < c₆ * M₁ := mul_pos hc₆0 hM₁0
    linarith
  -- the common scale
  set X : ℝ := max 1 (max (Real.log ((Q : ℝ) + 1)) (max (Real.log 2 / ρ.re)
    (max (-Real.log (ε / 2) / ρ.re)
      (Real.log (K / A₀) / ((1 - ρ.re) / 4))))) with hXdef
  have hX1 : (1 : ℝ) ≤ X := le_max_left _ _
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXQ : Real.log ((Q : ℝ) + 1) ≤ X :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hXB : Real.log 2 / ρ.re ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hXC : -Real.log (ε / 2) / ρ.re ≤ X :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hXD : Real.log (K / A₀) / ((1 - ρ.re) / 4) ≤ X :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hexpXQ : (Q : ℝ) + 1 ≤ Real.exp X := by
    calc (Q : ℝ) + 1 = Real.exp (Real.log ((Q : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp X := Real.exp_le_exp.mpr hXQ
  have hXhalf : Real.exp (-(ρ.re * X)) ≤ 1 / 2 := by
    have h : Real.log 2 ≤ ρ.re * X := by
      have h1 := hXB
      rw [div_le_iff₀ hσ0] at h1
      linarith [mul_comm X ρ.re]
    calc Real.exp (-(ρ.re * X)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
  have hXeps : 2 * Real.exp (-(ρ.re * X)) ≤ ε := by
    have h : -Real.log (ε / 2) ≤ ρ.re * X := by
      have h1 := hXC
      rw [div_le_iff₀ hσ0] at h1
      linarith [mul_comm X ρ.re]
    have h2 : Real.exp (-(ρ.re * X)) ≤ ε / 2 := by
      calc Real.exp (-(ρ.re * X)) ≤ Real.exp (Real.log (ε / 2)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = ε / 2 := Real.exp_log (by positivity)
    linarith
  have hXbudget : K * Real.exp ((3 + ρ.re) / 4 * X) ≤ Real.exp X * A₀ := by
    have hlam : Real.log (K / A₀) ≤ (1 - ρ.re) / 4 * X := by
      have h1 := hXD
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 - ρ.re) / 4)] at h1
      linarith [mul_comm X ((1 - ρ.re) / 4)]
    have hKA : K / A₀ ≤ Real.exp ((1 - ρ.re) / 4 * X) := by
      calc K / A₀ = Real.exp (Real.log (K / A₀)) :=
            (Real.exp_log (div_pos hK0 hA₀0)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlam
    have hK_le : K ≤ A₀ * Real.exp ((1 - ρ.re) / 4 * X) := by
      rw [div_le_iff₀ hA₀0] at hKA
      linarith [mul_comm (Real.exp ((1 - ρ.re) / 4 * X)) A₀]
    have hsplit : Real.exp ((1 - ρ.re) / 4 * X) * Real.exp ((3 + ρ.re) / 4 * X)
        = Real.exp X := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc K * Real.exp ((3 + ρ.re) / 4 * X)
        ≤ A₀ * Real.exp ((1 - ρ.re) / 4 * X) * Real.exp ((3 + ρ.re) / 4 * X) :=
          mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le
      _ = Real.exp X * A₀ := by
          rw [mul_assoc, hsplit]
          ring
  -- the uniform floor and ceiling of the batch
  set fs : ℝ := Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 8) with hfsdef
  set ds : ℝ := 2 * Real.exp (-(ρ.re * X)) with hdsdef
  have hfs0 : 0 < fs := by
    rw [hfsdef]
    exact mul_pos (Real.exp_pos _) (by positivity)
  have hds0 : 0 < ds := by
    rw [hdsdef]
    positivity
  have hsqrt2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hfsds : fs ≤ ds := by
    rw [hfsdef, hdsdef]
    have h1 : Real.exp (-(ρ.re * (X + Bt))) ≤ Real.exp (-(ρ.re * X)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_pos hσ0 hBt0])
    have h2 : Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 8)
        ≤ Real.exp (-(ρ.re * X)) * (Real.sqrt 2 / 8) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : Real.exp (-(ρ.re * X)) * (Real.sqrt 2 / 8)
        ≤ Real.exp (-(ρ.re * X)) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    linarith
  have hdsε : ds ≤ ε := by
    rw [hdsdef]
    exact hXeps
  have hds2 : ds ≤ 2 := by
    rw [hdsdef]
    have h := Real.exp_le_exp.mpr
      (show -(ρ.re * X) ≤ 0 by nlinarith [mul_nonneg hσ0.le hX0])
    rw [Real.exp_zero] at h
    linarith
  -- the two step counts
  set n₁ : ℕ := ⌈Tp / fs⌉₊ with hn₁def
  set n₂ : ℕ := ⌈max Tm ds / fs⌉₊ with hn₂def
  have hmax0 : 0 ≤ max Tm ds := le_trans hTm (le_max_left _ _)
  have hn₁budget : Tp ≤ n₁ * fs + ds := by
    have h := Nat.le_ceil (Tp / fs)
    rw [div_le_iff₀ hfs0] at h
    rw [hn₁def]
    linarith
  have hn₂budget : max Tm ds ≤ n₂ * fs + ds := by
    have h := Nat.le_ceil (max Tm ds / fs)
    rw [div_le_iff₀ hfs0] at h
    rw [hn₂def]
    linarith
  have hn₁up : (n₁ : ℝ) ≤ Tp / fs + 1 := by
    rw [hn₁def]
    have h := Nat.ceil_lt_add_one (div_nonneg hTp hfs0.le)
    linarith
  have hn₂up : (n₂ : ℝ) ≤ (Tm + 2) / fs + 1 := by
    rw [hn₂def]
    have h1 := Nat.ceil_lt_add_one (div_nonneg hmax0 hfs0.le)
    have h2 : max Tm ds ≤ Tm + 2 := max_le (by linarith) (by linarith)
    have h3 : max Tm ds / fs ≤ (Tm + 2) / fs := by
      rw [div_le_div_iff₀ hfs0 hfs0]
      exact mul_le_mul_of_nonneg_right h2 hfs0.le
    linarith
  have hNle : (n₁ : ℝ) + n₂ ≤ c₆ * Real.exp (ρ.re * X) + 2 := by
    have hkey : c₆ * Real.exp (ρ.re * X) * fs = Tp + Tm + 2 := by
      rw [hc₆def, hfsdef]
      have he : Real.exp (ρ.re * Bt) * Real.exp (ρ.re * X)
          * Real.exp (-(ρ.re * (X + Bt))) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
        congr 1
        ring
      have hs8 : 8 / Real.sqrt 2 * (Real.sqrt 2 / 8) = 1 := by
        field_simp
      calc (Tp + Tm + 2) * (8 / Real.sqrt 2) * Real.exp (ρ.re * Bt)
            * Real.exp (ρ.re * X)
            * (Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 8))
          = (Tp + Tm + 2) * (8 / Real.sqrt 2 * (Real.sqrt 2 / 8))
            * (Real.exp (ρ.re * Bt) * Real.exp (ρ.re * X)
              * Real.exp (-(ρ.re * (X + Bt)))) := by ring
        _ = Tp + Tm + 2 := by
            rw [he, hs8]
            ring
    have hdiv : (Tp + Tm + 2) / fs = c₆ * Real.exp (ρ.re * X) := by
      rw [div_eq_iff hfs0.ne']
      exact hkey.symm
    have hsum : Tp / fs + (Tm + 2) / fs = (Tp + Tm + 2) / fs := by
      rw [← add_div]
      congr 1
      ring
    linarith
  -- the master budget: Chebyshev mass beats the staircase cost at scale X
  have habsorb : ((n₁ : ℝ) + n₂) * (X + Bt) + Real.log 2 + Real.log 3 + (X + Bt)
      + 8 * Real.exp (3 * (X + Bt) / 4)
      ≤ Real.exp X * A₀ := by
    have hXBt0 : (0 : ℝ) < X + Bt := by linarith
    have hlin : X + Bt ≤ M₁ * Real.exp ((1 - ρ.re) / 2 * X) := by
      have h1exp : (1 : ℝ) ≤ Real.exp (X + Bt) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hXBt0.le
      have h := log_le_mul_rpow h1exp hm₀1
      rw [Real.log_exp] at h
      have hpow : Real.exp (X + Bt) ^ (1 / m₀) = Real.exp ((X + Bt) / m₀) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      rw [hpow] at h
      have hm₀pos : (0 : ℝ) < m₀ := by linarith
      have hexp2 : Real.exp ((X + Bt) / m₀)
          ≤ Real.exp Bt * Real.exp ((1 - ρ.re) / 2 * X) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hXm : X / m₀ = (1 - ρ.re) / 2 * X := by
          rw [hm₀def]
          field_simp
        have hBtm : Bt / m₀ ≤ Bt := by
          rw [div_le_iff₀ hm₀pos]
          nlinarith
        have hsplit : (X + Bt) / m₀ = X / m₀ + Bt / m₀ := by ring
        linarith
      calc X + Bt ≤ m₀ * Real.exp ((X + Bt) / m₀) := h
        _ ≤ m₀ * (Real.exp Bt * Real.exp ((1 - ρ.re) / 2 * X)) :=
            mul_le_mul_of_nonneg_left hexp2 (by linarith)
        _ = M₁ * Real.exp ((1 - ρ.re) / 2 * X) := by
            rw [hM₁def]
            ring
    have hN0 : (0 : ℝ) ≤ (n₁ : ℝ) + n₂ := by positivity
    have hc₆e0 : (0 : ℝ) ≤ c₆ * Real.exp (ρ.re * X) + 2 := by
      have := mul_pos hc₆0 (Real.exp_pos (ρ.re * X))
      linarith
    have hprod : ((n₁ : ℝ) + n₂) * (X + Bt)
        ≤ (c₆ * Real.exp (ρ.re * X) + 2) * (M₁ * Real.exp ((1 - ρ.re) / 2 * X)) :=
      mul_le_mul hNle hlin hXBt0.le hc₆e0
    have hcollect : (c₆ * Real.exp (ρ.re * X) + 2)
          * (M₁ * Real.exp ((1 - ρ.re) / 2 * X))
        = c₆ * M₁ * (Real.exp (ρ.re * X) * Real.exp ((1 - ρ.re) / 2 * X))
          + 2 * (M₁ * Real.exp ((1 - ρ.re) / 2 * X)) := by ring
    have hemerge : Real.exp (ρ.re * X) * Real.exp ((1 - ρ.re) / 2 * X)
        = Real.exp ((1 + ρ.re) / 2 * X) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he1 : Real.exp ((1 + ρ.re) / 2 * X) ≤ Real.exp ((3 + ρ.re) / 4 * X) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hX0 (by linarith : (0 : ℝ) ≤ 1 - ρ.re)])
    have he2 : Real.exp ((1 - ρ.re) / 2 * X) ≤ Real.exp ((3 + ρ.re) / 4 * X) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hX0 hσ0.le])
    have he3 : Real.exp (3 * X / 4) ≤ Real.exp ((3 + ρ.re) / 4 * X) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hσ0.le hX0])
    have he0 : (1 : ℝ) ≤ Real.exp ((3 + ρ.re) / 4 * X) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hσ0.le hX0])
    have hsplit8 : 8 * Real.exp (3 * (X + Bt) / 4) = c₈ * Real.exp (3 * X / 4) := by
      rw [hc₈def, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hcM0 : (0 : ℝ) ≤ c₆ * M₁ := (mul_pos hc₆0 hM₁0).le
    have h_a : ((n₁ : ℝ) + n₂) * (X + Bt)
        ≤ c₆ * M₁ * Real.exp ((3 + ρ.re) / 4 * X)
          + 2 * (M₁ * Real.exp ((3 + ρ.re) / 4 * X)) := by
      have h1 : c₆ * M₁ * (Real.exp (ρ.re * X) * Real.exp ((1 - ρ.re) / 2 * X))
          ≤ c₆ * M₁ * Real.exp ((3 + ρ.re) / 4 * X) := by
        rw [hemerge]
        exact mul_le_mul_of_nonneg_left he1 hcM0
      have h2 : 2 * (M₁ * Real.exp ((1 - ρ.re) / 2 * X))
          ≤ 2 * (M₁ * Real.exp ((3 + ρ.re) / 4 * X)) := by
        have := mul_le_mul_of_nonneg_left he2 hM₁0.le
        linarith
      linarith [hprod, hcollect.le, hcollect.ge]
    have h_b : Real.log 2 + Real.log 3 ≤ c₇ * Real.exp ((3 + ρ.re) / 4 * X) := by
      have h := mul_le_mul_of_nonneg_left he0 hc₇0.le
      rw [mul_one] at h
      rw [hc₇def] at h ⊢
      linarith
    have h_c : X + Bt ≤ M₁ * Real.exp ((3 + ρ.re) / 4 * X) := by
      have h := mul_le_mul_of_nonneg_left he2 hM₁0.le
      linarith
    have h_d : 8 * Real.exp (3 * (X + Bt) / 4)
        ≤ c₈ * Real.exp ((3 + ρ.re) / 4 * X) := by
      rw [hsplit8]
      exact mul_le_mul_of_nonneg_left he3 hc₈0.le
    have hKt : K * Real.exp ((3 + ρ.re) / 4 * X)
        = c₆ * M₁ * Real.exp ((3 + ρ.re) / 4 * X)
          + 2 * (M₁ * Real.exp ((3 + ρ.re) / 4 * X))
          + c₇ * Real.exp ((3 + ρ.re) / 4 * X)
          + M₁ * Real.exp ((3 + ρ.re) / 4 * X)
          + c₈ * Real.exp ((3 + ρ.re) / 4 * X) := by
      rw [hKdef]
      ring
    linarith [hXbudget]
  -- the three quadrant pools at scale X
  obtain ⟨W₁, hW₁lo, hW₁hi, hpool₁⟩ :=
    tilt_sign_pair_pool_base hre0 hc hcτ hnarrow true true hX0
  obtain ⟨W₂, hW₂lo, hW₂hi, hpool₂⟩ :=
    tilt_sign_pair_pool_base hre0 hc hcτ hnarrow true false hX0
  obtain ⟨W₃, hW₃lo, hW₃hi, hpool₃⟩ :=
    tilt_sign_pair_pool_base hre0 hc hcτ hnarrow false true hX0
  -- uniform per-element facts on any window of the batch
  have helem : ∀ W : ℝ, X ≤ W →
      W ≤ X + 5 * Real.pi / (2 * c) + 2 * Real.pi / (ρ.im + c) →
      ∀ q ∈ windowPrimes (Real.exp W)
        (Real.exp (W + Real.pi / (4 * (ρ.im + c)))),
      (Nat.Prime q ∧ Q < q) ∧
      fs ≤ Real.arctan ((q : ℝ) ^ (-ρ.re) * (Real.sqrt 2 / 2) / 2) ∧
      (q : ℝ) ^ (-ρ.re) / (1 - (q : ℝ) ^ (-ρ.re)) ≤ ds := by
    intro W hWlo hWhi q hq
    obtain ⟨hprime, hlo, hhi⟩ :=
      (mem_windowPrimes (Real.exp_pos _).le (Real.exp_pos _).le).mp hq
    have hq0 : (0 : ℝ) < q := lt_trans (Real.exp_pos _) hlo
    have hlogq_lo : X < Real.log q := by
      have h1 : W < Real.log q := by
        rw [← Real.log_exp W]
        exact Real.log_lt_log (Real.exp_pos _) hlo
      linarith
    have hlogq_hi : Real.log q ≤ X + Bt := by
      have h1 : Real.log q ≤ W + Real.pi / (4 * (ρ.im + c)) := by
        rw [← Real.log_exp (W + Real.pi / (4 * (ρ.im + c)))]
        exact Real.log_le_log hq0 hhi
      rw [hBtdef]
      linarith
    have hQq : Q < q := by
      have h2 : Real.exp X ≤ Real.exp W := Real.exp_le_exp.mpr hWlo
      have h3 : (Q : ℝ) < (q : ℝ) := by linarith
      exact_mod_cast h3
    have hrpow_eq : (q : ℝ) ^ (-ρ.re) = Real.exp (Real.log q * -ρ.re) :=
      Real.rpow_def_of_pos hq0 _
    have hrpow_up : (q : ℝ) ^ (-ρ.re) ≤ Real.exp (-(ρ.re * X)) := by
      rw [hrpow_eq]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlogq_lo.le hσ0.le]
    have hrpow_lo : Real.exp (-(ρ.re * (X + Bt))) ≤ (q : ℝ) ^ (-ρ.re) := by
      rw [hrpow_eq]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlogq_hi hσ0.le]
    refine ⟨⟨hprime, hQq⟩, ?_, ?_⟩
    · have hexp1 : Real.exp (-(ρ.re * (X + Bt))) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hσ0.le (by linarith : (0 : ℝ) ≤ X + Bt)]
      have ht₀1 : Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 2) / 2 ≤ 1 := by
        nlinarith [hsqrt2le, Real.exp_pos (-(ρ.re * (X + Bt)))]
      have ht₀0 : 0 ≤ Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 2) / 2 := by
        positivity
      have h1 := arctan_ge_half_self ht₀0 ht₀1
      have h2 : Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 2) / 2
          ≤ (q : ℝ) ^ (-ρ.re) * (Real.sqrt 2 / 2) / 2 := by
        have h := mul_le_mul_of_nonneg_right hrpow_lo
          (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)
        linarith
      have h3 := Real.arctan_mono h2
      have hfseq : fs = Real.exp (-(ρ.re * (X + Bt))) * (Real.sqrt 2 / 2) / 2 / 2 := by
        rw [hfsdef]
        ring
      linarith
    · have ht0 : 0 < (q : ℝ) ^ (-ρ.re) := Real.rpow_pos_of_pos hq0 _
      have htu : (q : ℝ) ^ (-ρ.re) ≤ Real.exp (-(ρ.re * X)) := hrpow_up
      have hu2 : Real.exp (-(ρ.re * X)) ≤ 1 / 2 := hXhalf
      have hupos : 0 < Real.exp (-(ρ.re * X)) := Real.exp_pos _
      have hmono : (q : ℝ) ^ (-ρ.re) / (1 - (q : ℝ) ^ (-ρ.re))
          ≤ Real.exp (-(ρ.re * X)) / (1 - Real.exp (-(ρ.re * X))) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have hfinal : Real.exp (-(ρ.re * X)) / (1 - Real.exp (-(ρ.re * X)))
          ≤ 2 * Real.exp (-(ρ.re * X)) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith only [hupos, hu2]
      rw [hdsdef]
      linarith
  -- the three pools as staircase fuel
  have hApp : ∀ q ∈ windowPrimes (Real.exp W₁)
      (Real.exp (W₁ + Real.pi / (4 * (ρ.im + c)))),
      fs ≤ (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ≤ ds ∧
      fs ≤ (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ≤ ds := by
    intro q hq
    obtain ⟨⟨hprime, hQq⟩, hfl, hce⟩ := helem W₁ hW₁lo hW₁hi q hq
    obtain ⟨hs1, hs2, hb1, hb2⟩ := hpool₁ q hq
    have hs1' : 0 < primeTilt q (ρ + (c : ℂ) * I) := hs1
    have hs2' : 0 < primeTilt q (ρ - (c : ℂ) * I) := hs2
    have hrp : ρ.re ≤ (ρ + (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ + (c : ℂ) * I).re = ρ.re).symm
    have hrm : ρ.re ≤ (ρ - (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ - (c : ℂ) * I).re = ρ.re).symm
    have hce1 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrp) hce
    have hce2 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrm) hce
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := le_trans hfl hb1
      rwa [abs_of_pos hs1'] at this
    · exact le_trans (le_abs_self _) hce1
    · have := le_trans hfl hb2
      rwa [abs_of_pos hs2'] at this
    · exact le_trans (le_abs_self _) hce2
  have hApM : ∀ q ∈ windowPrimes (Real.exp W₂)
      (Real.exp (W₂ + Real.pi / (4 * (ρ.im + c)))),
      fs ≤ (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ≤ ds ∧
      -ds ≤ (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ≤ -fs := by
    intro q hq
    obtain ⟨⟨hprime, hQq⟩, hfl, hce⟩ := helem W₂ hW₂lo hW₂hi q hq
    obtain ⟨hs1, hs2, hb1, hb2⟩ := hpool₂ q hq
    have hs1' : 0 < primeTilt q (ρ + (c : ℂ) * I) := hs1
    have hs2' : primeTilt q (ρ - (c : ℂ) * I) < 0 := hs2
    have hrp : ρ.re ≤ (ρ + (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ + (c : ℂ) * I).re = ρ.re).symm
    have hrm : ρ.re ≤ (ρ - (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ - (c : ℂ) * I).re = ρ.re).symm
    have hce1 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrp) hce
    have hce2 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrm) hce
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := le_trans hfl hb1
      rwa [abs_of_pos hs1'] at this
    · exact le_trans (le_abs_self _) hce1
    · exact (abs_le.mp hce2).1
    · have := le_trans hfl hb2
      rw [abs_of_neg hs2'] at this
      linarith
  have hAMp : ∀ q ∈ windowPrimes (Real.exp W₃)
      (Real.exp (W₃ + Real.pi / (4 * (ρ.im + c)))),
      -ds ≤ (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ + (c : ℂ) * I)) q ≤ -fs ∧
      fs ≤ (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ∧
      (fun q => primeTilt q (ρ - (c : ℂ) * I)) q ≤ ds := by
    intro q hq
    obtain ⟨⟨hprime, hQq⟩, hfl, hce⟩ := helem W₃ hW₃lo hW₃hi q hq
    obtain ⟨hs1, hs2, hb1, hb2⟩ := hpool₃ q hq
    have hs1' : primeTilt q (ρ + (c : ℂ) * I) < 0 := hs1
    have hs2' : 0 < primeTilt q (ρ - (c : ℂ) * I) := hs2
    have hrp : ρ.re ≤ (ρ + (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ + (c : ℂ) * I).re = ρ.re).symm
    have hrm : ρ.re ≤ (ρ - (c : ℂ) * I).re :=
      le_of_eq (by simp : (ρ - (c : ℂ) * I).re = ρ.re).symm
    have hce1 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrp) hce
    have hce2 := le_trans (abs_primeTilt_le hprime.two_le hσ0 hrm) hce
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (abs_le.mp hce1).1
    · have := le_trans hfl hb1
      rw [abs_of_neg hs1'] at this
      linarith
    · have := le_trans hfl hb2
      rwa [abs_of_pos hs2'] at this
    · exact le_trans (le_abs_self _) hce2
  -- the pools are disjoint: their tilt signs disagree
  have hd1 : Disjoint (windowPrimes (Real.exp W₁)
      (Real.exp (W₁ + Real.pi / (4 * (ρ.im + c)))))
      (windowPrimes (Real.exp W₂)
        (Real.exp (W₂ + Real.pi / (4 * (ρ.im + c))))) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have hs1 : 0 < primeTilt q (ρ - (c : ℂ) * I) := (hpool₁ q h1).2.1
    have hs2 : primeTilt q (ρ - (c : ℂ) * I) < 0 := (hpool₂ q h2).2.1
    exact absurd hs2 (asymm hs1)
  have hd2 : Disjoint (windowPrimes (Real.exp W₁)
      (Real.exp (W₁ + Real.pi / (4 * (ρ.im + c)))))
      (windowPrimes (Real.exp W₃)
        (Real.exp (W₃ + Real.pi / (4 * (ρ.im + c))))) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have hs1 : 0 < primeTilt q (ρ + (c : ℂ) * I) := (hpool₁ q h1).1
    have hs2 : primeTilt q (ρ + (c : ℂ) * I) < 0 := (hpool₃ q h2).1
    exact absurd hs2 (asymm hs1)
  have hd3 : Disjoint (windowPrimes (Real.exp W₂)
      (Real.exp (W₂ + Real.pi / (4 * (ρ.im + c)))))
      (windowPrimes (Real.exp W₃)
        (Real.exp (W₃ + Real.pi / (4 * (ρ.im + c))))) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have hs1 : 0 < primeTilt q (ρ + (c : ℂ) * I) := (hpool₂ q h1).1
    have hs2 : primeTilt q (ρ + (c : ℂ) * I) < 0 := (hpool₃ q h2).1
    exact absurd hs2 (asymm hs1)
  -- the pool budgets, from the Chebyshev window count
  have hNcast0 : (0 : ℝ) ≤ ((n₁ + n₂ : ℕ) : ℝ) := by positivity
  have hbudget_master : ((n₁ + n₂ : ℕ) : ℝ) * (X + Bt) + Real.log 2 + Real.log 3
      + (X + Bt) + 8 * Real.exp (3 * (X + Bt) / 4)
      ≤ Real.exp X * (Real.exp (Real.pi / (4 * (ρ.im + c))) * Real.log 2
        - Real.log 4) := by
    rw [← hA₀def]
    push_cast
    exact habsorb
  have hcard₁ : n₁ + n₂ ≤ (windowPrimes (Real.exp W₁)
      (Real.exp (W₁ + Real.pi / (4 * (ρ.im + c))))).card := by
    have h := windowPrimes_card_of_scale (Bt := Bt) hL2 hX0 hW₁lo
      (by rw [hBtdef]; linarith) hNcast0 hbudget_master
    exact_mod_cast h
  have hcard₂ : n₁ + n₂ ≤ (windowPrimes (Real.exp W₂)
      (Real.exp (W₂ + Real.pi / (4 * (ρ.im + c))))).card := by
    have h := windowPrimes_card_of_scale (Bt := Bt) hL2 hX0 hW₂lo
      (by rw [hBtdef]; linarith) hNcast0 hbudget_master
    exact_mod_cast h
  have hcard₃ : n₁ + n₂ ≤ (windowPrimes (Real.exp W₃)
      (Real.exp (W₃ + Real.pi / (4 * (ρ.im + c))))).card := by
    have h := windowPrimes_card_of_scale (Bt := Bt) hL2 hX0 hW₃lo
      (by rw [hBtdef]; linarith) hNcast0 hbudget_master
    exact_mod_cast h
  -- run the staircase
  obtain ⟨S, hSsub, hSu, hSv⟩ := staircase_reach_nonneg hfs0 hfsds hd1 hd2 hd3
    hApp hApM hAMp hTp hTm hn₁budget hn₂budget hcard₁
    (le_trans (Nat.le_add_right n₁ n₂) hcard₂)
    (le_trans (Nat.le_add_left n₂ n₁) hcard₃)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp (hSsub hp) with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact (helem W₁ hW₁lo hW₁hi p h').1
      · exact (helem W₂ hW₂lo hW₂hi p h').1
    · exact (helem W₃ hW₃lo hW₃hi p h).1
  · have hrfl : anchorTilt S (ρ + (c : ℂ) * I)
        = ∑ q ∈ S, (fun q => primeTilt q (ρ + (c : ℂ) * I)) q := rfl
    rw [hrfl]
    exact le_trans hSu hdsε
  · have hrfl : anchorTilt S (ρ - (c : ℂ) * I)
        = ∑ q ∈ S, (fun q => primeTilt q (ρ - (c : ℂ) * I)) q := rfl
    rw [hrfl]
    exact le_trans hSv hdsε

/-- **Pair-reachability of the two mirror-point tilts**: the same steering at the
line-reflected basepoints `1 − conj(ρ ± ci)` — these are the basepoints of the
mirror annulus at `1 − conj ρ`, whose real part lies in `(0,1)` exactly when
`Re ρ` does. -/
theorem anchorTilt_pair_reachable_nonneg_mirror {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {Tp Tm : ℝ} (hTp : 0 ≤ Tp) (hTm : 0 ≤ Tm) {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      |Tp - anchorTilt P (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))| ≤ ε ∧
      |Tm - anchorTilt P (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))| ≤ ε := by
  have h1 : 1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)
      = (1 - (starRingEnd ℂ) ρ) + (c : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have h2 : 1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)
      = (1 - (starRingEnd ℂ) ρ) - (c : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hre0' : 0 < (1 - (starRingEnd ℂ) ρ).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hre1' : (1 - (starRingEnd ℂ) ρ).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
    simp
  obtain ⟨P, hP, hu, hv⟩ := anchorTilt_pair_reachable_nonneg hre0' hre1' hc
    (by rw [him']; exact hcτ) (by rw [him']; exact hnarrow)
    (by rw [him']; exact hcap) hTp hTm hε Q
  refine ⟨P, hP, ?_, ?_⟩
  · rwa [h1]
  · rwa [h2]

end RHTower
