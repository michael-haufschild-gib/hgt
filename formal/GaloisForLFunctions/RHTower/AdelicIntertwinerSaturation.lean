import Mathlib

/-!
# The unramified intertwiner has saturated accelerated type

On the spherical vector the unnormalized local intertwiner of an unramified principal series is a
scalar; after spherical normalization the complementary Iwahori block carries the eigenvalue

```text
λ_p(z) = (p z² − 1) / (p − z²).
```

Two exact facts about it.  Its equality locus is the unit circle, because the two squared norms
differ by `(p² − 1)(‖z‖⁴ − 1)`.  And at `z = p^{c − iτ}` its logarithm is `2c log p` up to
`O(p^{−(1−2c)})` *uniformly in the phase* `τ`, so the finite tensor over the primes below the
cutoff has logarithm growing linearly in the cutoff.
-/

namespace RHTower

/-- The Iwahori eigenvalue of the unramified intertwiner on the complementary block. -/
noncomputable def intertwinerEigen (p : ℕ) (z : ℂ) : ℂ :=
  ((p : ℂ) * z ^ 2 - 1) / ((p : ℂ) - z ^ 2)

theorem intertwinerEigen_def (p : ℕ) (z : ℂ) :
    intertwinerEigen p z = ((p : ℂ) * z ^ 2 - 1) / ((p : ℂ) - z ^ 2) := rfl

theorem normSq_intertwiner_num (P : ℝ) (z : ℂ) :
    ‖(P : ℂ) * z ^ 2 - 1‖ ^ 2 = P ^ 2 * (‖z‖ ^ 2) ^ 2 - 2 * P * (z ^ 2).re + 1 := by
  have h1 : ‖(P : ℂ) * z ^ 2 - 1‖ ^ 2 = Complex.normSq ((P : ℂ) * z ^ 2 - 1) :=
    (Complex.normSq_eq_norm_sq _).symm
  have h3 : (‖z‖ ^ 2) ^ 2 = Complex.normSq (z ^ 2) := by
    have : Complex.normSq (z ^ 2) = ‖z ^ 2‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [this, norm_pow]
  rw [h1, h3]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

theorem normSq_intertwiner_den (P : ℝ) (z : ℂ) :
    ‖(P : ℂ) - z ^ 2‖ ^ 2 = P ^ 2 - 2 * P * (z ^ 2).re + (‖z‖ ^ 2) ^ 2 := by
  have h1 : ‖(P : ℂ) - z ^ 2‖ ^ 2 = Complex.normSq ((P : ℂ) - z ^ 2) :=
    (Complex.normSq_eq_norm_sq _).symm
  have h3 : (‖z‖ ^ 2) ^ 2 = Complex.normSq (z ^ 2) := by
    have : Complex.normSq (z ^ 2) = ‖z ^ 2‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [this, norm_pow]
  rw [h1, h3]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem abs_re_sq_le (z : ℂ) : |(z ^ 2).re| ≤ ‖z‖ ^ 2 := by
  have h := Complex.abs_re_le_norm (z ^ 2)
  rw [norm_pow] at h
  exact h

/-- **The exact equality locus.**  The two squared norms differ by `(p² − 1)(‖z‖⁴ − 1)`. -/
theorem normSq_intertwiner_sub (P : ℝ) (z : ℂ) :
    ‖(P : ℂ) * z ^ 2 - 1‖ ^ 2 - ‖(P : ℂ) - z ^ 2‖ ^ 2 = (P ^ 2 - 1) * (‖z‖ ^ 4 - 1) := by
  have h1 := normSq_intertwiner_num P z
  have h2 := normSq_intertwiner_den P z
  have h3 : ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
  rw [h1, h2, h3]
  ring

/-- **The Iwahori eigenvalue has modulus one exactly on the unit circle.** -/
theorem norm_intertwinerEigen_eq_one_iff {p : ℕ} (hp : 2 ≤ p) {z : ℂ}
    (hden : ((p : ℝ) : ℂ) - z ^ 2 ≠ 0) :
    ‖intertwinerEigen p z‖ = 1 ↔ ‖z‖ = 1 := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hcast : ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
  have hdennorm : (0 : ℝ) < ‖((p : ℝ) : ℂ) - z ^ 2‖ := norm_pos_iff.mpr hden
  have hval : ‖intertwinerEigen p z‖
      = ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ / ‖((p : ℝ) : ℂ) - z ^ 2‖ := by
    rw [intertwinerEigen_def, hcast, norm_div]
  have hid := normSq_intertwiner_sub (p : ℝ) z
  constructor
  · intro h
    rw [hval, div_eq_one_iff_eq (ne_of_gt hdennorm)] at h
    rw [h] at hid
    have hz4 : ‖z‖ ^ 4 = 1 := by
      have hP : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
      have : ((p : ℝ) ^ 2 - 1) * (‖z‖ ^ 4 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    have hsq : (‖z‖ ^ 2) ^ 2 = 1 := by nlinarith [hz4]
    have hz2 : ‖z‖ ^ 2 = 1 := by
      have hfac : (‖z‖ ^ 2 - 1) * (‖z‖ ^ 2 + 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with h' | h'
      · linarith
      · nlinarith [sq_nonneg ‖z‖]
    have hfac : (‖z‖ - 1) * (‖z‖ + 1) = 0 := by nlinarith [hz2]
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · linarith [norm_nonneg z]
  · intro h
    have hz4 : ‖z‖ ^ 4 = 1 := by rw [h]; norm_num
    rw [hz4] at hid
    have heq : ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2 = ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2 := by
      simp only [sub_self, mul_zero] at hid
      linarith
    have hnn : (0 : ℝ) ≤ ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ := norm_nonneg _
    have hnum : ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ = ‖((p : ℝ) : ℂ) - z ^ 2‖ := by
      nlinarith [heq, hnn, hdennorm]
    rw [hval, hnum, div_self (ne_of_gt hdennorm)]

/-- The comparison of the two squared norms with the pure power `ρ²`, in plain real variables. -/
theorem log_intertwiner_ratio_bound {P ρ δ x A B : ℝ}
    (hP0 : 0 < P) (hρ1 : 1 ≤ ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hPδ : P * δ = ρ)
    (hρP : ρ < P) (hx1 : x ≤ ρ) (hx2 : -ρ ≤ x)
    (hA : A = P ^ 2 * ρ ^ 2 - 2 * P * x + 1) (hB : B = P ^ 2 - 2 * P * x + ρ ^ 2) :
    |Real.log A - Real.log (ρ ^ 2 * B)|
      ≤ 2 * (Real.log (1 + δ) - Real.log (1 - δ)) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hd0 : (0 : ℝ) < 1 - δ := by linarith
  have hu0 : (0 : ℝ) < 1 + δ := by linarith
  have hρ3 : ρ ≤ ρ ^ 3 := by nlinarith
  have hρ4 : (1 : ℝ) ≤ ρ ^ 4 := by nlinarith
  -- the four two-sided bounds
  have hAub : A ≤ (P * ρ * (1 + δ)) ^ 2 := by
    have hexp : (P * ρ * (1 + δ)) ^ 2
        = P ^ 2 * ρ ^ 2 + 2 * ρ ^ 2 * P * (P * δ) + ρ ^ 2 * (P * δ) ^ 2 := by ring
    rw [hA, hexp, hPδ]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ x + ρ by linarith),
      mul_nonneg hP0.le (show (0:ℝ) ≤ ρ ^ 3 - ρ by linarith), hρ4]
  have hAlb : (P * ρ * (1 - δ)) ^ 2 ≤ A := by
    have hexp : (P * ρ * (1 - δ)) ^ 2
        = P ^ 2 * ρ ^ 2 - 2 * ρ ^ 2 * P * (P * δ) + ρ ^ 2 * (P * δ) ^ 2 := by ring
    rw [hA, hexp, hPδ]
    have k1 : (0 : ℝ) ≤ ρ ^ 2 - 1 := by nlinarith
    have k2 : (0 : ℝ) ≤ 2 * P * ρ - ρ ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg k1 k2, mul_nonneg hP0.le (show (0:ℝ) ≤ ρ - x by linarith)]
  have hBub : B ≤ (P * (1 - δ)) ^ 2 + 4 * P * ρ := by
    have hexp : (P * (1 - δ)) ^ 2 = P ^ 2 - 2 * P * (P * δ) + (P * δ) ^ 2 := by ring
    rw [hB, hexp, hPδ]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ρ - x by linarith)]
  have hBub' : B ≤ (P * (1 + δ)) ^ 2 := by
    have hexp : (P * (1 + δ)) ^ 2 = P ^ 2 + 2 * P * (P * δ) + (P * δ) ^ 2 := by ring
    rw [hB, hexp, hPδ]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ x + ρ by linarith)]
  have hBlb : (P * (1 - δ)) ^ 2 ≤ B := by
    have hexp : (P * (1 - δ)) ^ 2 = P ^ 2 - 2 * P * (P * δ) + (P * δ) ^ 2 := by ring
    rw [hB, hexp, hPδ]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ρ - x by linarith)]
  -- positivity
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hAlb
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (by positivity) hBlb
  -- the two logarithm comparisons
  have hlogA_ub : Real.log A ≤ 2 * (Real.log P + Real.log ρ + Real.log (1 + δ)) := by
    refine le_trans (Real.log_le_log hApos hAub) (le_of_eq ?_)
    rw [Real.log_pow]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have hlogA_lb : 2 * (Real.log P + Real.log ρ + Real.log (1 - δ)) ≤ Real.log A := by
    refine le_trans (le_of_eq ?_) (Real.log_le_log (by positivity) hAlb)
    rw [Real.log_pow]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have hlogB_ub : Real.log (ρ ^ 2 * B) ≤ 2 * (Real.log ρ + Real.log P + Real.log (1 + δ)) := by
    have hle : ρ ^ 2 * B ≤ ρ ^ 2 * (P * (1 + δ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hBub' (by positivity)
    refine le_trans (Real.log_le_log (by positivity) hle) (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have hlogB_lb : 2 * (Real.log ρ + Real.log P + Real.log (1 - δ)) ≤ Real.log (ρ ^ 2 * B) := by
    have hle : ρ ^ 2 * (P * (1 - δ)) ^ 2 ≤ ρ ^ 2 * B :=
      mul_le_mul_of_nonneg_left hBlb (by positivity)
    refine le_trans (le_of_eq ?_) (Real.log_le_log (by positivity) hle)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  rw [abs_le]
  constructor <;> linarith

theorem abs_log_norm_intertwinerEigen_sub_le {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : ‖z‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    |Real.log ‖intertwinerEigen p z‖ - 2 * c * Real.log (p : ℝ)|
      ≤ 2 / (1 - (2 : ℝ) ^ (2 * c - 1)) * (p : ℝ) ^ (2 * c - 1) := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hρ1 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by
    rw [hz]; exact Real.one_le_rpow hP1 (by linarith)
  have hρ0 : (0 : ℝ) < ‖z‖ ^ 2 := by linarith
  have hδ0 : (0 : ℝ) < (p : ℝ) ^ (2 * c - 1) := Real.rpow_pos_of_pos hP0 _
  have hPδ : (p : ℝ) * (p : ℝ) ^ (2 * c - 1) = ‖z‖ ^ 2 := by
    have h : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (2 * c) := by
      rw [← Real.rpow_add hP0]; congr 1; ring
    rw [hz, ← h, Real.rpow_one]
  have hμ : (p : ℝ) ^ (2 * c - 1) ≤ (2 : ℝ) ^ (2 * c - 1) := by
    have hexp : (0 : ℝ) < 1 - 2 * c := by linarith
    have h2 : (2 : ℝ) ^ (1 - 2 * c) ≤ (p : ℝ) ^ (1 - 2 * c) :=
      Real.rpow_le_rpow (by norm_num) hP2 hexp.le
    have hP' : (p : ℝ) ^ (2 * c - 1) = ((p : ℝ) ^ (1 - 2 * c))⁻¹ := by
      rw [← Real.rpow_neg hP0.le]; congr 1; ring
    have h2' : (2 : ℝ) ^ (2 * c - 1) = ((2 : ℝ) ^ (1 - 2 * c))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]; congr 1; ring
    rw [hP', h2']
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hP0 _) (Real.rpow_pos_of_pos (by norm_num) _)).mpr h2
  have hμ1 : (2 : ℝ) ^ (2 * c - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ1 : (p : ℝ) ^ (2 * c - 1) < 1 := lt_of_le_of_lt hμ hμ1
  have hκ0 : (0 : ℝ) < 1 - (2 : ℝ) ^ (2 * c - 1) := by linarith
  have hρP : ‖z‖ ^ 2 < (p : ℝ) := by
    rw [← hPδ]; nlinarith [hP0, hδ1]
  have hxle : |(z ^ 2).re| ≤ ‖z‖ ^ 2 := abs_re_sq_le z
  have hx1 : (z ^ 2).re ≤ ‖z‖ ^ 2 := le_trans (le_abs_self _) hxle
  have hx2 : -(‖z‖ ^ 2) ≤ (z ^ 2).re := neg_le_of_abs_le hxle
  have hkey := log_intertwiner_ratio_bound (P := (p : ℝ)) (ρ := ‖z‖ ^ 2)
    (δ := (p : ℝ) ^ (2 * c - 1)) (x := (z ^ 2).re)
    (A := ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2) (B := ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2)
    hP0 hρ1 hδ0 hδ1 hPδ hρP hx1 hx2 (normSq_intertwiner_num _ _) (normSq_intertwiner_den _ _)
  -- identify the logarithm of the eigenvalue
  have hApos : (0 : ℝ) < ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2 := by
    rw [normSq_intertwiner_num]
    have hPρ : (2 : ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2 := by nlinarith [hP2, hρ1]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ‖z‖ ^ 2 - (z ^ 2).re by linarith),
      mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2)
        (by linarith : (0:ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2 - 2)]
  have hBpos : (0 : ℝ) < ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2 := by
    rw [normSq_intertwiner_den]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ‖z‖ ^ 2 - (z ^ 2).re by linarith),
      mul_pos (sub_pos.mpr hρP) (sub_pos.mpr hρP)]
  have hnum : ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
  have hnumne : ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ≠ 0 := by
    intro h; rw [h] at hApos; simp at hApos
  have hdenne : ‖((p : ℝ) : ℂ) - z ^ 2‖ ≠ 0 := by
    intro h; rw [h] at hBpos; simp at hBpos
  have hL : Real.log ‖intertwinerEigen p z‖
      = (Real.log (‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2)
        - Real.log (‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2)) / 2 := by
    rw [intertwinerEigen_def, hnum, norm_div, Real.log_div hnumne hdenne,
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogρ : Real.log (‖z‖ ^ 2) = 2 * c * Real.log (p : ℝ) := by
    rw [hz, Real.log_rpow hP0]
  have hsplit : Real.log (‖z‖ ^ 2 * ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2)
      = Real.log (‖z‖ ^ 2) + Real.log (‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hBpos)]
  have hbase : Real.log ‖intertwinerEigen p z‖ - 2 * c * Real.log (p : ℝ)
      = (Real.log (‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2)
        - Real.log ((‖z‖ ^ 2) ^ 2 * ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2)) / 2 := by
    have hsq : Real.log ((‖z‖ ^ 2) ^ 2 * ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2)
        = 2 * Real.log (‖z‖ ^ 2) + Real.log (‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hBpos), Real.log_pow]
      push_cast; ring
    rw [hL, hsq, hlogρ]
    ring
  rw [hbase]
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < (2:ℝ))]
  refine le_trans hkey ?_
  -- the elementary logarithm bounds
  have hlogup : Real.log (1 + (p : ℝ) ^ (2 * c - 1)) ≤ (p : ℝ) ^ (2 * c - 1) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + (p : ℝ) ^ (2 * c - 1) by linarith)
    linarith
  have hlogdown : -Real.log (1 - (p : ℝ) ^ (2 * c - 1))
      ≤ (p : ℝ) ^ (2 * c - 1) / (1 - (2 : ℝ) ^ (2 * c - 1)) := by
    have hd0 : (0 : ℝ) < 1 - (p : ℝ) ^ (2 * c - 1) := by linarith
    have hinv := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - (p : ℝ) ^ (2 * c - 1))⁻¹ by
      positivity)
    rw [Real.log_inv] at hinv
    have hstep : (1 - (p : ℝ) ^ (2 * c - 1))⁻¹ - 1
        = (p : ℝ) ^ (2 * c - 1) / (1 - (p : ℝ) ^ (2 * c - 1)) := by
      field_simp
      ring
    rw [hstep] at hinv
    refine le_trans hinv ?_
    refine div_le_div_of_nonneg_left hδ0.le hκ0 ?_
    linarith
  have hone : (1 : ℝ) ≤ 1 / (1 - (2 : ℝ) ^ (2 * c - 1)) := by
    rw [le_div_iff₀ hκ0]; linarith
  have hfin : Real.log (1 + (p : ℝ) ^ (2 * c - 1)) - Real.log (1 - (p : ℝ) ^ (2 * c - 1))
      ≤ 2 / (1 - (2 : ℝ) ^ (2 * c - 1)) * (p : ℝ) ^ (2 * c - 1) := by
    have hsplit2 : 2 / (1 - (2 : ℝ) ^ (2 * c - 1)) * (p : ℝ) ^ (2 * c - 1)
        = (p : ℝ) ^ (2 * c - 1) * (1 / (1 - (2 : ℝ) ^ (2 * c - 1)))
          + (p : ℝ) ^ (2 * c - 1) / (1 - (2 : ℝ) ^ (2 * c - 1)) := by
      field_simp; ring
    rw [hsplit2]
    have h1 : Real.log (1 + (p : ℝ) ^ (2 * c - 1))
        ≤ (p : ℝ) ^ (2 * c - 1) * (1 / (1 - (2 : ℝ) ^ (2 * c - 1))) := by
      refine le_trans hlogup ?_
      nlinarith [hδ0, hone]
    linarith
  linarith


/-- On the radial family the Iwahori eigenvalue is nonzero: the numerator is at least `(pρ − 1)²`
and the denominator at least `(p − ρ)²`, both positive because `ρ = p^{2c} < p`. -/
theorem norm_intertwinerEigen_pos {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : ‖z‖ ^ 2 = (p : ℝ) ^ (2 * c)) :
    0 < ‖intertwinerEigen p z‖ := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hρ1 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by
    rw [hz]; exact Real.one_le_rpow hP1 (by linarith)
  have hρ0 : (0 : ℝ) < ‖z‖ ^ 2 := by linarith
  have hρP : ‖z‖ ^ 2 < (p : ℝ) := by
    rw [hz]
    have hlt : (p : ℝ) ^ (2 * c) < (p : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    rwa [Real.rpow_one] at hlt
  have hxle : |(z ^ 2).re| ≤ ‖z‖ ^ 2 := abs_re_sq_le z
  have hx1 : (z ^ 2).re ≤ ‖z‖ ^ 2 := le_trans (le_abs_self _) hxle
  have hApos : (0 : ℝ) < ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ ^ 2 := by
    rw [normSq_intertwiner_num]
    have hPρ : (2 : ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2 := by nlinarith [hP2, hρ1]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ‖z‖ ^ 2 - (z ^ 2).re by linarith),
      mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2)
        (by linarith : (0:ℝ) ≤ (p : ℝ) * ‖z‖ ^ 2 - 2)]
  have hBpos : (0 : ℝ) < ‖((p : ℝ) : ℂ) - z ^ 2‖ ^ 2 := by
    rw [normSq_intertwiner_den]
    nlinarith [mul_nonneg hP0.le (show (0:ℝ) ≤ ‖z‖ ^ 2 - (z ^ 2).re by linarith),
      mul_pos (sub_pos.mpr hρP) (sub_pos.mpr hρP)]
  have hcast : ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
  rw [intertwinerEigen_def, hcast, norm_div]
  have hnum : (0 : ℝ) < ‖((p : ℝ) : ℂ) * z ^ 2 - 1‖ := by
    rcases (norm_nonneg (((p : ℝ) : ℂ) * z ^ 2 - 1)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hApos; simp at hApos
  have hden : (0 : ℝ) < ‖((p : ℝ) : ℂ) - z ^ 2‖ := by
    rcases (norm_nonneg (((p : ℝ) : ℂ) - z ^ 2)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hBpos; simp at hBpos
  exact div_pos hnum hden


end RHTower
