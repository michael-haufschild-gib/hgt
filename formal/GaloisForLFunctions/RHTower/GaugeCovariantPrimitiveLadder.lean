import GaloisForLFunctions.RHTower.HarmonicPrimitiveLadder
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Gauge covariance of the primitive ladder

The weighted pairing `C_M(f, A) = ∑_{n ≤ M} f_n w_n A_n` is unchanged by any nonvanishing gauge:

`C_M(f, A) = C_M(g f, g^{-1} A)`.

Running the Abel recursion on the right-hand side therefore gives a covariant identity in which the
primitive is taken of the *gauged* source and the difference quotient of the *gauged* receiver.
Choosing the exact polar gauge `g_n = A_n/|A_n|` makes the receiver a positive amplitude and moves
the entire complex oscillation into the covariant source tail

`(H(gf))_n = -∑_{m > n} w_m g_m f_m`,

which is a primitive of the gauged source on the whole pairing range.

A smooth phase gauge with constant logarithmic frequency is exactly a Mellin twist: it satisfies
`g(x) = g(y) (x/y)^{iτ}` identically, so it can only re-coordinate the pairing, never change the
real exponent it carries.
-/

namespace RHTower

noncomputable section

section GeneralField

variable {K : Type*} [Field K]

/-- The weighted pairing over an arbitrary field. -/
def gaugeAbelPairing (f w A : ℕ → K) (M : ℕ) : K :=
  ∑ n ∈ Finset.Icc 1 M, f n * w n * A n

/-- The weighted backward difference quotient over an arbitrary field. -/
def gaugeDiscreteDeriv (w A : ℕ → K) (n : ℕ) : K := (A n - A (n + 1)) / w n

theorem gaugeAbelPairing_real (f w A : ℕ → ℝ) (M : ℕ) :
    gaugeAbelPairing f w A M = abelPairing f w A M := rfl

theorem gaugeDiscreteDeriv_real (w A : ℕ → ℝ) (n : ℕ) :
    gaugeDiscreteDeriv w A n = discreteDeriv w A n := rfl

theorem gauge_sum_telescope (g A : ℕ → K) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 (M + 1), (g n - g (n - 1)) * A n
      = g (M + 1) * A (M + 1) - g 0 * A 1
        + ∑ n ∈ Finset.Icc 1 M, g n * (A n - A (n + 1)) := by
  induction M with
  | zero => simp [sub_mul]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

/-- The Abel recursion against a primitive that is required to be one only on the pairing range. -/
theorem gaugeAbelPairing_recursion {f w A g : ℕ → K} (hw : ∀ n, 1 ≤ n → w n ≠ 0) (M : ℕ)
    (hg : ∀ n ∈ Finset.Icc 1 (M + 1), g n - g (n - 1) = w n * f n) :
    gaugeAbelPairing f w A (M + 1)
      = g (M + 1) * A (M + 1) - g 0 * A 1
        + gaugeAbelPairing g w (gaugeDiscreteDeriv w A) M := by
  have h1 : ∀ n ∈ Finset.Icc 1 (M + 1), f n * w n * A n = (g n - g (n - 1)) * A n := by
    intro n hn
    rw [hg n hn]
    ring
  rw [gaugeAbelPairing, Finset.sum_congr rfl h1, gauge_sum_telescope]
  congr 1
  rw [gaugeAbelPairing]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hwn := hw n hn.1
  rw [gaugeDiscreteDeriv]
  field_simp

/-- **(24.79) The weighted pairing is invariant under every nonvanishing gauge.** -/
theorem gaugeAbelPairing_gauge {f w A g : ℕ → K} (hg : ∀ n, 1 ≤ n → g n ≠ 0) (M : ℕ) :
    gaugeAbelPairing f w A M
      = gaugeAbelPairing (fun n => g n * f n) w (fun n => A n / g n) M := by
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hgn := hg n hn.1
  field_simp

/-- **(24.80) The covariant Abel identity.**  The primitive is taken of the gauged source and the
difference quotient of the gauged receiver. -/
theorem gaugeAbelPairing_covariant {f w A g h : ℕ → K} (hw : ∀ n, 1 ≤ n → w n ≠ 0)
    (hgne : ∀ n, 1 ≤ n → g n ≠ 0) (M : ℕ)
    (hh : ∀ n ∈ Finset.Icc 1 (M + 1), h n - h (n - 1) = w n * (g n * f n)) :
    gaugeAbelPairing f w A (M + 1)
      = h (M + 1) * (A (M + 1) / g (M + 1)) - h 0 * (A 1 / g 1)
        + gaugeAbelPairing h w (gaugeDiscreteDeriv w (fun n => A n / g n)) M := by
  rw [gaugeAbelPairing_gauge hgne (M + 1)]
  exact gaugeAbelPairing_recursion hw M hh

/-! ## The covariant source tail -/

/-- The truncated covariant source tail `-∑_{m > n} w_m f_m`. -/
def tailPrimitive (w f : ℕ → K) (M n : ℕ) : K := -∑ m ∈ Finset.Icc (n + 1) M, w m * f m

/-- **(24.81) The truncated tail is a primitive of the source on the whole pairing range.** -/
theorem tailPrimitive_diff (w f : ℕ → K) {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    tailPrimitive w f M n - tailPrimitive w f M (n - 1) = w n * f n := by
  classical
  have hstep : n - 1 + 1 = n := by omega
  have hsplit : ∑ m ∈ Finset.Icc n M, w m * f m
      = w n * f n + ∑ m ∈ Finset.Icc (n + 1) M, w m * f m := by
    rw [Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ioc_insert_left hnM,
      Finset.sum_insert (by simp)]
  rw [tailPrimitive, tailPrimitive, hstep, hsplit]
  ring

/-- The tail primitive vanishes at the top of the range. -/
@[simp]
theorem tailPrimitive_top (w f : ℕ → K) (M : ℕ) : tailPrimitive w f M M = 0 := by
  rw [tailPrimitive, Finset.Icc_eq_empty (by omega), Finset.sum_empty, neg_zero]

/-- The covariant Abel identity driven by the exact source tail. -/
theorem gaugeAbelPairing_tail {f w A g : ℕ → K} (hw : ∀ n, 1 ≤ n → w n ≠ 0)
    (hgne : ∀ n, 1 ≤ n → g n ≠ 0) (M : ℕ) :
    gaugeAbelPairing f w A (M + 1)
      = -(tailPrimitive w (fun n => g n * f n) (M + 1) 0) * (A 1 / g 1)
        + gaugeAbelPairing (tailPrimitive w (fun n => g n * f n) (M + 1)) w
            (gaugeDiscreteDeriv w (fun n => A n / g n)) M := by
  have hh : ∀ n ∈ Finset.Icc 1 (M + 1),
      tailPrimitive w (fun m => g m * f m) (M + 1) n
        - tailPrimitive w (fun m => g m * f m) (M + 1) (n - 1) = w n * (g n * f n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact tailPrimitive_diff w (fun m => g m * f m) hn.1 hn.2
  rw [gaugeAbelPairing_covariant hw hgne M hh, tailPrimitive_top]
  ring

end GeneralField

/-! ## The polar gauge -/

/-- The exact polar gauge `A_n / |A_n|` of a receiver. -/
def polarGauge (A : ℕ → ℂ) (n : ℕ) : ℂ := A n / ((‖A n‖ : ℝ) : ℂ)

theorem polarGauge_ne_zero {A : ℕ → ℂ} {n : ℕ} (h : A n ≠ 0) : polarGauge A n ≠ 0 := by
  have hnorm : ((‖A n‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.2 h
  exact div_ne_zero h hnorm

@[simp]
theorem norm_polarGauge {A : ℕ → ℂ} {n : ℕ} (h : A n ≠ 0) : ‖polarGauge A n‖ = 1 := by
  have hpos : 0 < ‖A n‖ := norm_pos_iff.2 h
  rw [polarGauge, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    div_self hpos.ne']

/-- **The polar gauge turns the receiver into its positive amplitude.** -/
theorem div_polarGauge {A : ℕ → ℂ} {n : ℕ} (h : A n ≠ 0) :
    A n / polarGauge A n = ((‖A n‖ : ℝ) : ℂ) := by
  have hnorm : ((‖A n‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.2 h
  rw [polarGauge]
  field_simp

/-- In the polar gauge the pairing is a pairing against the positive amplitude. -/
theorem gaugeAbelPairing_polar {f A : ℕ → ℂ} {w : ℕ → ℂ} (h : ∀ n, 1 ≤ n → A n ≠ 0) (M : ℕ) :
    gaugeAbelPairing f w A M
      = gaugeAbelPairing (fun n => polarGauge A n * f n) w
          (fun n => ((‖A n‖ : ℝ) : ℂ)) M := by
  rw [gaugeAbelPairing_gauge (g := polarGauge A) (fun n hn => polarGauge_ne_zero (h n hn)) M]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  dsimp only
  rw [div_polarGauge (h n hn.1)]

/-! ## A constant-frequency phase gauge is exactly a Mellin twist -/

/-- A smooth phase gauge of constant logarithmic frequency `τ`. -/
def mellinTwistGauge (tau c : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((tau * Real.log x + c : ℝ) : ℂ))

@[simp]
theorem norm_mellinTwistGauge (tau c x : ℝ) : ‖mellinTwistGauge tau c x‖ = 1 := by
  rw [mellinTwistGauge, Complex.norm_exp]
  simp

theorem mellinTwistGauge_ne_zero (tau c x : ℝ) : mellinTwistGauge tau c x ≠ 0 :=
  Complex.exp_ne_zero _

/-- **(24.83) A constant-frequency phase gauge is exactly a local Mellin twist.** -/
theorem mellinTwistGauge_ratio {tau c x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinTwistGauge tau c x
      = mellinTwistGauge tau c y
        * Complex.exp (Complex.I * ((tau * Real.log (x / y) : ℝ) : ℂ)) := by
  rw [mellinTwistGauge, mellinTwistGauge, ← Complex.exp_add, Real.log_div hx.ne' hy.ne']
  congr 1
  push_cast
  ring

/-- The Mellin twist factor depends only on the multiplicative displacement. -/
theorem mellinTwistGauge_ratio_scale {tau c x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    mellinTwistGauge tau c (x * s)
      = mellinTwistGauge tau c x * Complex.exp (Complex.I * ((tau * Real.log s : ℝ) : ℂ)) := by
  have hxs : 0 < x * s := mul_pos hx hs
  have hratio := mellinTwistGauge_ratio (tau := tau) (c := c) hxs hx
  have hcancel : x * s / x = s := by
    field_simp
  rw [hratio, hcancel]

end

end RHTower
