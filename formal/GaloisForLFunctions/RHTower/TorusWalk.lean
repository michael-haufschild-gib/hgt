/-
The two-basepoint torus walk: every sign quadrant is supplied.

The parity criterion compares the mirror orientations at the two annulus basepoints,
and both orientation-steering tilts ride the SAME prime walk at two nearby frequencies
`a = τ + c` and `b = τ − c` (the basepoint heights).  Per prime the pair of increments
is `(sin(a·log q), sin(b·log q))`-signed: a step on the torus.  The two phases differ
by the slow difference phase `(a−b)·log q`, so prescribing the difference phase near
`0` or near `π` — a LONG logarithmic window, of length inversely proportional to the
annulus size — and inside it a full fast-phase tile, realizes every sign pair: the
torus walk has steps in all four quadrants, at every prime scale.  This is the
structure an Euler-product-free mirror analogue does not possess: two incommensurably
sampled sine laws steered by one multiplicative support.
-/
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.RelativePhase

noncomputable section

namespace RHTower

open Complex Metric

/-- **The two-phase window supply**: for nearby frequencies `b < a` with
`9(a−b) ≤ a` and `a·(4 log 2) < π`, and any fast offset `o` and difference target
`d ≥ 0`, there are primes beyond any bound whose fast phase `a·log q` lies in a
prescribed quarter-tile `(o, o + π/4)` mod `2π` while the difference phase
`(a−b)·log q` lies within `π/8` of `d` mod `2π`: the slow difference window is long
enough to contain a full fast tile, and the fast tile is longer than `log 2`. -/
theorem exists_prime_two_phase_window {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hnarrow : 9 * (a - b) ≤ a) (hcap : a * (4 * Real.log 2) < Real.pi)
    {o d : ℝ} (hd : 0 ≤ d) (Q : ℕ) :
    ∃ (q : ℕ) (m j : ℤ), Nat.Prime q ∧ Q < q ∧
      a * Real.log q - 2 * Real.pi * m ∈ Set.Ioo o (o + Real.pi / 4) ∧
      (a - b) * Real.log q - 2 * Real.pi * j
        ∈ Set.Ioo (d - Real.pi / 8) (d + Real.pi / 8) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hΔ : (0 : ℝ) < a - b := sub_pos.mpr hba
  have ha : (0 : ℝ) < a := lt_trans hb hba
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmargin : 0 < Real.pi / (4 * a) - Real.log 2 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    nlinarith
  -- choose the difference-window index far enough out
  set M : ℝ := max (Real.log ((Q : ℝ) + 1))
    (-Real.log (Real.pi / (4 * a) - Real.log 2)) with hMdef
  obtain ⟨j, hj⟩ := exists_nat_gt (((a - b) * M + Real.pi / 8) / (2 * Real.pi))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  set Jl : ℝ := (2 * Real.pi * (j : ℝ) + d - Real.pi / 8) / (a - b) with hJldef
  set Jr : ℝ := (2 * Real.pi * (j : ℝ) + d + Real.pi / 8) / (a - b) with hJrdef
  have hJlM : M < Jl := by
    rw [div_lt_iff₀ h2pi] at hj
    rw [hJldef, lt_div_iff₀ hΔ]
    nlinarith
  -- the full fast tile inside the difference window
  set m : ℤ := ⌈(a * Jl - o) / (2 * Real.pi)⌉ with hmdef
  set Wl : ℝ := (2 * Real.pi * (m : ℝ) + o) / a with hWldef
  have hWlJl : Jl ≤ Wl := by
    have hceil : (a * Jl - o) / (2 * Real.pi) ≤ (m : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ h2pi] at hceil
    rw [hWldef, le_div_iff₀ ha]
    nlinarith
  have hWlJl2 : Wl ≤ Jl + 2 * Real.pi / a := by
    have hceil : (m : ℝ) < (a * Jl - o) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    have hceil1 : (m : ℝ) - 1 < (a * Jl - o) / (2 * Real.pi) := by linarith
    rw [lt_div_iff₀ h2pi] at hceil1
    have hcancel : 2 * Real.pi / a * a = 2 * Real.pi := div_mul_cancel₀ _ ha.ne'
    rw [hWldef, div_le_iff₀ ha]
    nlinarith
  have hWrJr : Wl + Real.pi / (4 * a) ≤ Jr := by
    have hlen : Jr - Jl = (Real.pi / 4) / (a - b) := by
      rw [hJrdef, hJldef, div_sub_div_same]
      congr 1
      ring
    have h0 : 2 * Real.pi / a = 8 * Real.pi / (4 * a) := by
      rw [div_eq_div_iff ha.ne' (by positivity : (4 : ℝ) * a ≠ 0)]
      ring
    have hfit : 2 * Real.pi / a + Real.pi / (4 * a) ≤ (Real.pi / 4) / (a - b) := by
      rw [h0, ← add_div, div_le_div_iff₀ (by positivity) hΔ]
      nlinarith
    linarith
  -- the prime in the fast tile
  have hWlM : M < Wl := lt_of_lt_of_le hJlM hWlJl
  have hb1 : (Q : ℝ) < Real.exp Wl := by
    have h1 : Real.log ((Q : ℝ) + 1) ≤ M := le_max_left _ _
    have h2 : (Q : ℝ) + 1 = Real.exp (Real.log ((Q : ℝ) + 1)) :=
      (Real.exp_log (by positivity)).symm
    have h3 := Real.exp_lt_exp.mpr (lt_of_le_of_lt h1 hWlM)
    linarith [h2 ▸ h3]
  have hb2 : Real.exp (-Wl) < Real.pi / (4 * a) - Real.log 2 := by
    have h1 : -Real.log (Real.pi / (4 * a) - Real.log 2) ≤ M := le_max_right _ _
    have h3 : Real.exp (-Wl) < Real.exp (Real.log (Real.pi / (4 * a) - Real.log 2)) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_log hmargin] at h3
  obtain ⟨q, hq, hQq, hmem⟩ :=
    exists_prime_log_mem_Ioo (L := Real.pi / (4 * a)) Q hb1 hb2
  refine ⟨q, m, (j : ℤ), hq, hQq, ?_, ?_⟩
  · constructor
    · have h := mul_lt_mul_of_pos_left hmem.1 ha
      have haWl : a * Wl = 2 * Real.pi * (m : ℝ) + o := by
        rw [hWldef, mul_comm, div_mul_cancel₀ _ ha.ne']
      linarith
    · have h := mul_lt_mul_of_pos_left hmem.2 ha
      have hexp : a * (Wl + Real.pi / (4 * a))
          = 2 * Real.pi * (m : ℝ) + o + Real.pi / 4 := by
        rw [mul_add, hWldef, mul_comm a, div_mul_cancel₀ _ ha.ne',
          show a * (Real.pi / (4 * a)) = Real.pi / 4 from by
            rw [mul_comm (4 : ℝ) a, ← div_div, ← mul_div_assoc,
              mul_comm a (Real.pi / a), div_mul_cancel₀ _ ha.ne']]
      linarith
  · have hqJ : Real.log q ∈ Set.Ioo Jl Jr := by
      constructor
      · exact lt_of_le_of_lt hWlJl hmem.1
      · exact lt_of_lt_of_le hmem.2 hWrJr
    constructor
    · have h := mul_lt_mul_of_pos_left hqJ.1 hΔ
      have hΔJl : (a - b) * Jl = 2 * Real.pi * (j : ℝ) + d - Real.pi / 8 := by
        rw [hJldef, mul_comm, div_mul_cancel₀ _ hΔ.ne']
      push_cast
      linarith
    · have h := mul_lt_mul_of_pos_left hqJ.2 hΔ
      have hΔJr : (a - b) * Jr = 2 * Real.pi * (j : ℝ) + d + Real.pi / 8 := by
        rw [hJrdef, mul_comm, div_mul_cancel₀ _ hΔ.ne']
      push_cast
      linarith

/-- Sign of the sine from a shifted-window membership: positive on `(0, π)` mod `2π`. -/
theorem sin_pos_of_shifted_window {θ : ℝ} {m : ℤ} (h1 : 2 * Real.pi * m < θ)
    (h2 : θ < 2 * Real.pi * m + Real.pi) :
    0 < Real.sin θ := by
  have hper : Real.sin θ = Real.sin (θ - m * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  rw [hper]
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith
  · nlinarith

/-- Sign of the sine from a shifted-window membership: negative on `(π, 2π)` mod
`2π`. -/
theorem sin_neg_of_shifted_window {θ : ℝ} {m : ℤ} (h1 : 2 * Real.pi * m + Real.pi < θ)
    (h2 : θ < 2 * Real.pi * m + 2 * Real.pi) :
    Real.sin θ < 0 := by
  have hper : Real.sin θ = Real.sin (θ - m * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  have hshift : Real.sin (θ - m * (2 * Real.pi))
      = -Real.sin (θ - m * (2 * Real.pi) - Real.pi) := by
    have h := Real.sin_add_pi (θ - m * (2 * Real.pi) - Real.pi)
    rw [sub_add_cancel] at h
    exact h
  rw [hper, hshift, neg_lt_zero]
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith
  · nlinarith

/-- **The torus walk fills all four quadrants**: for nearby frequencies `b < a`
(`9(a−b) ≤ a`, `a·(4 log 2) < π`) and ANY prescribed sign pair, there are primes beyond
any bound realizing that pair of sine signs at the two frequencies simultaneously —
prescribe the difference phase near `0` (equal signs) or near `π` (opposite signs), and
place the fast phase in the matching quarter tile. -/
theorem exists_prime_sin_sign_pair {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hnarrow : 9 * (a - b) ≤ a) (hcap : a * (4 * Real.log 2) < Real.pi)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      (if ε₁ then 0 < Real.sin (a * Real.log q) else Real.sin (a * Real.log q) < 0) ∧
      (if ε₂ then 0 < Real.sin (b * Real.log q) else Real.sin (b * Real.log q) < 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  cases ε₁ <;> cases ε₂
  · -- (false, false): fast negative, slow negative — difference near 0
    obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 11 * Real.pi / 8) (d := 0) le_rfl Q
    refine ⟨q, hq, hQq, ?_, ?_⟩
    · apply sin_neg_of_shifted_window (m := m)
      · have := hfast.1
        linarith
      · have := hfast.2
        linarith
    · apply sin_neg_of_shifted_window (m := m - j)
      · have h1 := hfast.1
        have h2 := hdiff.2
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
      · have h1 := hfast.2
        have h2 := hdiff.1
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
  · -- (false, true): fast negative, slow positive — difference near π
    obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 11 * Real.pi / 8) (d := Real.pi) hpi.le Q
    refine ⟨q, hq, hQq, ?_, ?_⟩
    · apply sin_neg_of_shifted_window (m := m)
      · have := hfast.1
        linarith
      · have := hfast.2
        linarith
    · apply sin_pos_of_shifted_window (m := m - j)
      · have h1 := hfast.1
        have h2 := hdiff.2
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
      · have h1 := hfast.2
        have h2 := hdiff.1
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
  · -- (true, false): fast positive, slow negative — difference near π
    obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 3 * Real.pi / 8) (d := Real.pi) hpi.le Q
    refine ⟨q, hq, hQq, ?_, ?_⟩
    · apply sin_pos_of_shifted_window (m := m)
      · have := hfast.1
        linarith
      · have := hfast.2
        linarith
    · apply sin_neg_of_shifted_window (m := m - j - 1)
      · have h1 := hfast.1
        have h2 := hdiff.2
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
      · have h1 := hfast.2
        have h2 := hdiff.1
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
  · -- (true, true): fast positive, slow positive — difference near 0
    obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 3 * Real.pi / 8) (d := 0) le_rfl Q
    refine ⟨q, hq, hQq, ?_, ?_⟩
    · apply sin_pos_of_shifted_window (m := m)
      · have := hfast.1
        linarith
      · have := hfast.2
        linarith
    · apply sin_pos_of_shifted_window (m := m - j)
      · have h1 := hfast.1
        have h2 := hdiff.2
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith
      · have h1 := hfast.2
        have h2 := hdiff.1
        have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
        push_cast
        linarith

/-- **The torus quadrant supply for the two basepoint tilts.**  At the two basepoints
`ρ ± c·i` of a narrow annulus in the strip, the two orientation-steering tilt
increments realize EVERY sign pair at every prime scale: the pair
`(primeTilt q (1−conj(ρ+ci)), primeTilt q (1−conj(ρ−ci)))` visits all four quadrants.
This two-frequency steering is the structure that requires the Euler product — the
walk's support IS the primes — and is what a Davenport–Heilbronn analogue lacks. -/
theorem exists_prime_tilt_sign_pair {ρ : ℂ} {c : ℝ} (hre : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      (if ε₁ then 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))
        else primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)) < 0) ∧
      (if ε₂ then 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))
        else primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)) < 0) := by
  have himp : (ρ + (c : ℂ) * I).im = ρ.im + c := by
    simp
  have himm : (ρ - (c : ℂ) * I).im = ρ.im - c := by
    simp
  have hrep : (ρ + (c : ℂ) * I).re = ρ.re := by
    simp
  have hrem : (ρ - (c : ℂ) * I).re = ρ.re := by
    simp
  have hb : (0 : ℝ) < ρ.im - c := sub_pos.mpr hcτ
  have hba : ρ.im - c < ρ.im + c := by linarith
  have hnarrow' : 9 * ((ρ.im + c) - (ρ.im - c)) ≤ ρ.im + c := by
    have h : (ρ.im + c) - (ρ.im - c) = 2 * c := by ring
    rw [h]
    exact hnarrow
  obtain ⟨q, hq, hQq, hsin1, hsin2⟩ :=
    exists_prime_sin_sign_pair hb hba hnarrow' hcap ε₁ ε₂ Q
  refine ⟨q, hq, hQq, ?_, ?_⟩
  · cases ε₁ with
    | false =>
      show primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)) < 0
      rw [primeTilt_mirror_neg_iff hq.two_le (by rw [hrep]; exact hre), himp]
      exact hsin1
    | true =>
      show 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))
      rw [primeTilt_mirror_pos_iff hq.two_le (by rw [hrep]; exact hre), himp]
      exact hsin1
  · cases ε₂ with
    | false =>
      show primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)) < 0
      rw [primeTilt_mirror_neg_iff hq.two_le (by rw [hrem]; exact hre), himm]
      exact hsin2
    | true =>
      show 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))
      rw [primeTilt_mirror_pos_iff hq.two_le (by rw [hrem]; exact hre), himm]
      exact hsin2

/-! ### The per-coordinate floors: bounded step eccentricity in every quadrant -/

/-- The single-tilt arctangent floor: with a positive sine the tilt beats the
arctangent of half the factor's imaginary part. -/
theorem primeTilt_ge {q : ℕ} (hq : 2 ≤ q) {w : ℂ} (h0 : 0 < w.re)
    (hsin : 0 < Real.sin (w.im * Real.log q)) :
    Real.arctan ((q : ℝ) ^ (-w.re) * Real.sin (w.im * Real.log q) / 2)
      ≤ primeTilt q w := by
  have hre := re_eulerFactor_pos hq h0
  have hreh : ((1 : ℂ) - (q : ℂ) ^ (-w)).re ≤ 2 := by
    have habs := Complex.abs_re_le_norm ((q : ℂ) ^ (-w))
    rw [norm_prime_cpow_neg hq w] at habs
    have hle1 : (q : ℝ) ^ (-w.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (by omega : 1 ≤ q)) (by linarith)
    have hneg := neg_le_abs (((q : ℂ) ^ (-w)).re)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have him : ((1 : ℂ) - (q : ℂ) ^ (-w)).im
      = (q : ℝ) ^ (-w.re) * Real.sin (w.im * Real.log q) := im_eulerFactor hq w
  have hrp : (0 : ℝ) < (q : ℝ) ^ (-w.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) _
  have himpos : 0 < ((1 : ℂ) - (q : ℂ) ^ (-w)).im := by
    rw [him]
    exact mul_pos hrp hsin
  have hstep : (q : ℝ) ^ (-w.re) * Real.sin (w.im * Real.log q) / 2
      ≤ ((1 : ℂ) - (q : ℂ) ^ (-w)).im / ((1 : ℂ) - (q : ℂ) ^ (-w)).re := by
    rw [← him]
    exact div_le_div_of_nonneg_left himpos.le hre hreh
  rw [primeTilt, arg_eq_arctan_of_re_pos hre]
  exact Real.arctan_mono hstep

/-- **The eccentricity-bounded step floor**: whenever the sine is at least `√2/2` in
absolute value, the tilt is at least `arctan(q^(−Re w)·(√2/2)/2)` in absolute value —
floor and ceiling of the step live at the SAME exponent. -/
theorem abs_primeTilt_floor {q : ℕ} (hq : 2 ≤ q) {w : ℂ} (h0 : 0 < w.re)
    (hsin : Real.sqrt 2 / 2 ≤ |Real.sin (w.im * Real.log q)|) :
    Real.arctan ((q : ℝ) ^ (-w.re) * (Real.sqrt 2 / 2) / 2) ≤ |primeTilt q w| := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrp : (0 : ℝ) < (q : ℝ) ^ (-w.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) _
  rcases lt_trichotomy (Real.sin (w.im * Real.log q)) 0 with hneg | hzero | hpos
  · have hconjre : 0 < ((starRingEnd ℂ) w).re := by rwa [Complex.conj_re]
    have hconjsin : 0 < Real.sin (((starRingEnd ℂ) w).im * Real.log q) := by
      rw [Complex.conj_im, neg_mul, Real.sin_neg]
      linarith
    have hfl := primeTilt_ge hq hconjre hconjsin
    rw [primeTilt_conj hq h0] at hfl
    have hsin' : Real.sqrt 2 / 2 ≤ Real.sin (((starRingEnd ℂ) w).im * Real.log q) := by
      rw [Complex.conj_im, neg_mul, Real.sin_neg]
      rw [abs_of_neg hneg] at hsin
      linarith
    have hmono : Real.arctan ((q : ℝ) ^ (-w.re) * (Real.sqrt 2 / 2) / 2)
        ≤ Real.arctan ((q : ℝ) ^ (-((starRingEnd ℂ) w).re)
          * Real.sin (((starRingEnd ℂ) w).im * Real.log q) / 2) := by
      apply Real.arctan_mono
      rw [Complex.conj_re]
      have := mul_le_mul_of_nonneg_left hsin' hrp.le
      linarith
    rw [Complex.conj_re] at hmono
    have habs : -primeTilt q w ≤ |primeTilt q w| := neg_le_abs _
    rw [Complex.conj_re] at hfl
    linarith
  · rw [hzero, abs_zero] at hsin
    linarith
  · have hfl := primeTilt_ge hq h0 hpos
    have hsin' : Real.sqrt 2 / 2 ≤ Real.sin (w.im * Real.log q) := by
      rwa [abs_of_pos hpos] at hsin
    have hmono : Real.arctan ((q : ℝ) ^ (-w.re) * (Real.sqrt 2 / 2) / 2)
        ≤ Real.arctan ((q : ℝ) ^ (-w.re) * Real.sin (w.im * Real.log q) / 2) := by
      apply Real.arctan_mono
      have := mul_le_mul_of_nonneg_left hsin' hrp.le
      linarith
    have habs : primeTilt q w ≤ |primeTilt q w| := le_abs_self _
    linarith

/-- Sine floor from a positively-shifted central window. -/
theorem abs_sin_floor_pos_window {θ : ℝ} {m : ℤ}
    (h1 : 2 * Real.pi * m + Real.pi / 4 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi * m + 3 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ |Real.sin θ| := by
  have hper : Real.sin θ = Real.sin (θ - m * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  have hfl : Real.sqrt 2 / 2 ≤ Real.sin (θ - m * (2 * Real.pi)) := by
    apply sin_ge_sqrt_two_div_two
    · linarith
    · linarith
  rw [hper]
  exact le_trans hfl (le_abs_self _)

/-- Sine floor from a negatively-shifted central window. -/
theorem abs_sin_floor_neg_window {θ : ℝ} {m : ℤ}
    (h1 : 2 * Real.pi * m + 5 * Real.pi / 4 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi * m + 7 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ |Real.sin θ| := by
  have hper : Real.sin θ = Real.sin (θ - m * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  have hshift : Real.sin (θ - m * (2 * Real.pi))
      = -Real.sin (θ - m * (2 * Real.pi) - Real.pi) := by
    have h := Real.sin_add_pi (θ - m * (2 * Real.pi) - Real.pi)
    rw [sub_add_cancel] at h
    exact h
  have hfl : Real.sqrt 2 / 2 ≤ Real.sin (θ - m * (2 * Real.pi) - Real.pi) := by
    apply sin_ge_sqrt_two_div_two
    · linarith
    · linarith
  rw [hper, hshift, abs_neg]
  exact le_trans hfl (le_abs_self _)

/-- **The quadrant supply with per-coordinate floors**: every sign pair is realized at
every prime scale with BOTH sines at least `√2/2` in absolute value — the torus steps
in each quadrant have bounded eccentricity. -/
theorem exists_prime_sin_sign_pair_floors {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (hnarrow : 9 * (a - b) ≤ a) (hcap : a * (4 * Real.log 2) < Real.pi)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      (if ε₁ then 0 < Real.sin (a * Real.log q) else Real.sin (a * Real.log q) < 0) ∧
      (if ε₂ then 0 < Real.sin (b * Real.log q) else Real.sin (b * Real.log q) < 0) ∧
      Real.sqrt 2 / 2 ≤ |Real.sin (a * Real.log q)| ∧
      Real.sqrt 2 / 2 ≤ |Real.sin (b * Real.log q)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  cases ε₁ <;> cases ε₂
  · obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 11 * Real.pi / 8) (d := 0) le_rfl Q
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
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
  · obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 11 * Real.pi / 8) (d := Real.pi) hpi.le Q
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
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
  · obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 3 * Real.pi / 8) (d := Real.pi) hpi.le Q
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
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
  · obtain ⟨q, m, j, hq, hQq, hfast, hdiff⟩ := exists_prime_two_phase_window hb hba
      hnarrow hcap (o := 3 * Real.pi / 8) (d := 0) le_rfl Q
    have hb' : b * Real.log q = a * Real.log q - (a - b) * Real.log q := by ring
    refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
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

/-- **The quadrant supply for the basepoint tilts, with eccentricity-bounded floors**:
every sign pair of the two steering-tilt increments is realized at every prime scale,
with BOTH increments at least `arctan(q^(σ−1)·(√2/2)/2)` in absolute value — floor and
ceiling at the same exponent `1 − Re ρ`, so the torus steps in every quadrant have
bounded shape as the scale grows. -/
theorem exists_prime_tilt_sign_pair_floors {ρ : ℂ} {c : ℝ} (hre : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      (if ε₁ then 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))
        else primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)) < 0) ∧
      (if ε₂ then 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))
        else primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)) < 0) ∧
      Real.arctan ((q : ℝ) ^ (-(1 - ρ.re)) * (Real.sqrt 2 / 2) / 2)
        ≤ |primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))| ∧
      Real.arctan ((q : ℝ) ^ (-(1 - ρ.re)) * (Real.sqrt 2 / 2) / 2)
        ≤ |primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))| := by
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
  obtain ⟨q, hq, hQq, hsin1, hsin2, hfl1, hfl2⟩ :=
    exists_prime_sin_sign_pair_floors hb hba hnarrow' hcap ε₁ ε₂ Q
  have hwp_re : (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.conj_re]
  have hwp_im : (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)).im = ρ.im + c := by
    simp [Complex.sub_im, Complex.conj_im]
    ring
  have hwm_re : (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.conj_re]
  have hwm_im : (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)).im = ρ.im - c := by
    simp [Complex.sub_im, Complex.conj_im]
    ring
  have hwp_re0 : 0 < (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)).re := by
    rw [hwp_re]
    linarith
  have hwm_re0 : 0 < (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)).re := by
    rw [hwm_re]
    linarith
  refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
  · cases ε₁ with
    | false =>
      show primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I)) < 0
      rw [primeTilt_mirror_neg_iff hq.two_le (by rw [hrep]; exact hre), himp]
      exact hsin1
    | true =>
      show 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ + (c : ℂ) * I))
      rw [primeTilt_mirror_pos_iff hq.two_le (by rw [hrep]; exact hre), himp]
      exact hsin1
  · cases ε₂ with
    | false =>
      show primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I)) < 0
      rw [primeTilt_mirror_neg_iff hq.two_le (by rw [hrem]; exact hre), himm]
      exact hsin2
    | true =>
      show 0 < primeTilt q (1 - (starRingEnd ℂ) (ρ - (c : ℂ) * I))
      rw [primeTilt_mirror_pos_iff hq.two_le (by rw [hrem]; exact hre), himm]
      exact hsin2
  · have h := abs_primeTilt_floor hq.two_le hwp_re0 (by rw [hwp_im]; exact hfl1)
    rwa [hwp_re] at h
  · have h := abs_primeTilt_floor hq.two_le hwm_re0 (by rw [hwm_im]; exact hfl2)
    rwa [hwm_re] at h

/-- **The quadrant supply for the tilts AT the basepoints, with floors**: the
orientation of the annulus's own basepoints is steered by the anchor tilts at those
basepoints (the mirror-of-mirror identity), and every sign pair of THOSE two increments
is realized at every prime scale, with both increments floored at the basepoint
exponent `Re ρ`. -/
theorem exists_prime_tilt_sign_pair_floors_base {ρ : ℂ} {c : ℝ} (hre0 : 0 < ρ.re)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
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
  obtain ⟨q, hq, hQq, hsin1, hsin2, hfl1, hfl2⟩ :=
    exists_prime_sin_sign_pair_floors hb hba hnarrow' hcap ε₁ ε₂ Q
  have hrep0 : 0 < (ρ + (c : ℂ) * I).re := by rw [hrep]; exact hre0
  have hrem0 : 0 < (ρ - (c : ℂ) * I).re := by rw [hrem]; exact hre0
  refine ⟨q, hq, hQq, ?_, ?_, ?_, ?_⟩
  · cases ε₁ with
    | false =>
      show primeTilt q (ρ + (c : ℂ) * I) < 0
      rw [primeTilt_neg_iff hq.two_le hrep0, himp]
      exact hsin1
    | true =>
      show 0 < primeTilt q (ρ + (c : ℂ) * I)
      rw [primeTilt_pos_iff hq.two_le hrep0, himp]
      exact hsin1
  · cases ε₂ with
    | false =>
      show primeTilt q (ρ - (c : ℂ) * I) < 0
      rw [primeTilt_neg_iff hq.two_le hrem0, himm]
      exact hsin2
    | true =>
      show 0 < primeTilt q (ρ - (c : ℂ) * I)
      rw [primeTilt_pos_iff hq.two_le hrem0, himm]
      exact hsin2
  · have h := abs_primeTilt_floor hq.two_le hrep0 (by rw [himp]; exact hfl1)
    rwa [hrep] at h
  · have h := abs_primeTilt_floor hq.two_le hrem0 (by rw [himm]; exact hfl2)
    rwa [hrem] at h

end RHTower
