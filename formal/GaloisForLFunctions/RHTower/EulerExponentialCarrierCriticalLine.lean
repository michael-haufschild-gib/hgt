import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.RHTower.Reflection

/-!
# Symmetrized Euler exponentials have their strip zeros on the critical line

For a finite real Dirichlet exponent `D(s) = Σ_{n∈S} c(n) n^{-s}` put `E(s) = exp D(s)` and

`Z(s) = E(s) + χ(s) E(1-s)`,

where `χ(s) = Γ_ℝ(1-s)/Γ_ℝ(s)` is the factor of ζ's functional equation (`zetaChi`). On the open
strip `Z` satisfies ζ's functional equation `Z(1-s) = χ(1-s) Z(s)`, and `E` never vanishes.

Let `K = Σ_{n∈S} |c(n)| log n`. Every zero of `Z` in the open critical strip with `|Im s| ≥ 8` and
`log(|Im s|/2π) > 2K + 1` lies on the critical line (`re_eq_half_of_carrier_eq_zero`).

Mechanism, at `s = σ+it` with `1/2 < σ < 1`, `t > 0`:
* `n^{-(1-s)} = n^{2σ-1}·conj(n^{-s})`, so
  `Re D(1-s) - Re D(s) = Σ c(n)(n^{2σ-1}-1) Re n^{-s} ≤ (2σ-1) K`,
  using `(n^{2σ-1}-1) n^{-σ} = n^{σ-1} - n^{-σ} ≤ (2σ-1) log n`;
* `log |χ(s)| ≤ -(σ-1/2)(log(t/2π) - 4/t² - π/t)` (`norm_zetaChi_le_right_line_exp`).
Hence `|χ(s)E(1-s)| < |E(s)|` and `Z(s) ≠ 0`. Conjugation covers `t < 0` and the functional
equation covers `σ < 1/2`.

For `c(n) = Λ(n)/log n` on `2 ≤ n ≤ N`, `E` is the exponential of the truncated logarithm of the
Euler product and `K = Σ_{2≤n≤N} Λ(n)` (`logMass_eulerLogCoeff`). So the finite-depth statement
holds at every Euler depth `N`, but only above height `2π·exp(2ψ(N)+1)`: the archimedean factor
pays for Euler depth logarithmic in the height. Nothing here locates the zeros of `ζ`.
-/

open Complex

namespace RHTower

noncomputable section

namespace EulerExponentialCarrier

/-- A finite real Dirichlet exponent `D(s) = Σ_{n ∈ S} c(n) n^{-s}`. -/
def dirichletExponent (S : Finset ℕ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (c n : ℂ) * (n : ℂ) ^ (-s)

/-- The `χ`-symmetrized exponential `exp D(s) + χ(s) exp D(1-s)`. -/
def carrier (S : Finset ℕ) (c : ℕ → ℝ) : ℂ → ℂ :=
  chiSymmetrize zetaChi (fun s => Complex.exp (dirichletExponent S c s))

/-- The logarithmic mass `K = Σ_{n∈S} |c(n)| log n`. -/
def logMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ S, |c n| * Real.log n

/-- The reflected power is a real rescaling of the conjugate power:
`n^{-(1-s)} = n^{2 Re s - 1} · conj(n^{-s})`. -/
theorem natCast_cpow_neg_one_sub {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    (n : ℂ) ^ (-(1 - s)) =
      (((n : ℝ) ^ (2 * s.re - 1) : ℝ) : ℂ) * (starRingEnd ℂ) ((n : ℂ) ^ (-s)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hsplit : -(1 - s) = (((2 * s.re - 1 : ℝ)) : ℂ) + (starRingEnd ℂ) (-s) := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.conj_re]
      ring
    · simp
  have hreal : (n : ℂ) ^ (((2 * s.re - 1 : ℝ)) : ℂ) = (((n : ℝ) ^ (2 * s.re - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hsplit, Complex.cpow_add _ _ hn0, hreal, natCast_cpow_conj]

/-- Real part of a reflected term. -/
theorem re_reflected_term {n : ℕ} (hn : 1 ≤ n) (a : ℝ) (s : ℂ) :
    ((a : ℂ) * (n : ℂ) ^ (-(1 - s))).re =
      (n : ℝ) ^ (2 * s.re - 1) * ((a : ℂ) * (n : ℂ) ^ (-s)).re := by
  rw [natCast_cpow_neg_one_sub hn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_im]
  ring

/-- `(n^{2σ-1} - 1) n^{-σ} = n^{σ-1} - n^{-σ} ≤ (2σ-1) log n` for `1/2 ≤ σ ≤ 1`. -/
theorem rpow_reflect_sub_le {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    ((n : ℝ) ^ (2 * σ - 1) - 1) * (n : ℝ) ^ (-σ) ≤ (2 * σ - 1) * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  set y := Real.log (n : ℝ)
  have hx : 0 ≤ y * (2 * σ - 1) := mul_nonneg hy (by linarith)
  have ha : y * (σ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy (by linarith)
  have hkey : (Real.exp (y * (2 * σ - 1)) - 1) * Real.exp (y * -σ) =
      Real.exp (y * (σ - 1)) - Real.exp (y * (σ - 1)) * Real.exp (-(y * (2 * σ - 1))) := by
    rw [sub_mul, one_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> ring
  rw [hkey]
  have hexp1 : 1 - y * (2 * σ - 1) ≤ Real.exp (-(y * (2 * σ - 1))) := by
    have := Real.add_one_le_exp (-(y * (2 * σ - 1)))
    linarith
  have hea : Real.exp (y * (σ - 1)) ≤ 1 := Real.exp_le_one_iff.mpr ha
  have hea0 : 0 < Real.exp (y * (σ - 1)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left hexp1 hea0.le, mul_le_mul_of_nonneg_right hea hx]

/-- The reflected exponent exceeds the direct one by at most `(2σ-1) K`. -/
theorem re_dirichletExponent_one_sub_sub_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ)
    {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 1) :
    (dirichletExponent S c (1 - s)).re - (dirichletExponent S c s).re ≤
      (2 * s.re - 1) * logMass S c := by
  unfold dirichletExponent logMass
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 := hS n hn
  rw [re_reflected_term hn1 (c n) s]
  have hre : |((c n : ℂ) * (n : ℂ) ^ (-s)).re| ≤ |c n| * (n : ℝ) ^ (-s.re) := by
    calc |((c n : ℂ) * (n : ℂ) ^ (-s)).re| ≤ ‖(c n : ℂ) * (n : ℂ) ^ (-s)‖ :=
          Complex.abs_re_le_norm _
      _ = |c n| * (n : ℝ) ^ (-s.re) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hr1 : 1 ≤ (n : ℝ) ^ (2 * s.re - 1) :=
    Real.one_le_rpow (by exact_mod_cast hn1) (by linarith)
  have hb := rpow_reflect_sub_le hn1 h1 h2
  have hc : 0 ≤ |c n| := abs_nonneg _
  calc (n : ℝ) ^ (2 * s.re - 1) * ((c n : ℂ) * (n : ℂ) ^ (-s)).re
        - ((c n : ℂ) * (n : ℂ) ^ (-s)).re
        = ((n : ℝ) ^ (2 * s.re - 1) - 1) * ((c n : ℂ) * (n : ℂ) ^ (-s)).re := by ring
    _ ≤ ((n : ℝ) ^ (2 * s.re - 1) - 1) * (|c n| * (n : ℝ) ^ (-s.re)) :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hre) (by linarith)
    _ = |c n| * (((n : ℝ) ^ (2 * s.re - 1) - 1) * (n : ℝ) ^ (-s.re)) := by ring
    _ ≤ |c n| * ((2 * s.re - 1) * Real.log n) := mul_le_mul_of_nonneg_left hb hc
    _ = (2 * s.re - 1) * (|c n| * Real.log n) := by ring

/-- The archimedean correction `4/t² + π/t` is below one from height eight on. -/
theorem chi_correction_lt_one {t : ℝ} (ht : 8 ≤ t) :
    1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)) < 1 := by
  have ht0 : 0 < t := by linarith
  have h1 : 1 / (t / 2) ^ 2 ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : Real.pi / (2 * (t / 2)) ≤ Real.pi / 8 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  have h3 := Real.pi_le_four
  linarith

/-- **Domination in the upper right quarter-strip.** -/
theorem norm_chi_mul_exp_one_sub_lt {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {c : ℕ → ℝ} {s : ℂ}
    (hσ1 : 1 / 2 < s.re) (hσ2 : s.re < 1) (ht8 : 8 ≤ s.im)
    (hT : 2 * logMass S c + 1 < Real.log (s.im / (2 * Real.pi))) :
    ‖zetaChi s * Complex.exp (dirichletExponent S c (1 - s))‖ <
      ‖Complex.exp (dirichletExponent S c s)‖ := by
  set σ := s.re with hσdef
  set t := s.im with htdef
  have ht0 : 0 < t := by linarith
  have hχ := norm_zetaChi_le_right_line_exp (σ := σ) (t := t) hσ1.le hσ2 ht0
  rw [hσdef, htdef, Complex.re_add_im s] at hχ
  have hD := re_dirichletExponent_one_sub_sub_le hS c hσ1.le hσ2.le
  rw [← hσdef] at hD
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have hE := chi_correction_lt_one ht8
  have hlog : Real.log Real.pi - Real.log (t / 2) = -Real.log (t / (2 * Real.pi)) := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
    ring
  have hneg : (σ - 1 / 2) * (Real.log Real.pi - Real.log (t / 2) +
      (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) + 2 * logMass S c) < 0 := by
    apply mul_neg_of_pos_of_neg (by linarith)
    rw [hlog]
    linarith
  calc ‖zetaChi s‖ * Real.exp (dirichletExponent S c (1 - s)).re
      ≤ Real.exp ((σ - 1 / 2) * (Real.log Real.pi - Real.log (t / 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))))) *
          Real.exp ((dirichletExponent S c s).re + (2 * σ - 1) * logMass S c) :=
        mul_le_mul hχ (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp ((dirichletExponent S c s).re) *
          Real.exp ((σ - 1 / 2) * (Real.log Real.pi - Real.log (t / 2) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) + 2 * logMass S c)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ < Real.exp ((dirichletExponent S c s).re) :=
        mul_lt_of_lt_one_right (Real.exp_pos _)
          ((Real.exp_lt_exp.mpr hneg).trans_eq Real.exp_zero)

/-- No zero in the upper right quarter-strip above the threshold. -/
theorem carrier_ne_zero_of_upper {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {c : ℕ → ℝ} {s : ℂ}
    (hσ1 : 1 / 2 < s.re) (hσ2 : s.re < 1) (ht8 : 8 ≤ s.im)
    (hT : 2 * logMass S c + 1 < Real.log (s.im / (2 * Real.pi))) :
    carrier S c s ≠ 0 := by
  intro h
  have hlt := norm_chi_mul_exp_one_sub_lt hS hσ1 hσ2 ht8 hT
  unfold carrier chiSymmetrize at h
  have hsolve : Complex.exp (dirichletExponent S c s) =
      -(zetaChi s * Complex.exp (dirichletExponent S c (1 - s))) := by
    linear_combination h
  rw [hsolve, norm_neg] at hlt
  exact lt_irrefl _ hlt

theorem dirichletExponent_conj (S : Finset ℕ) (c : ℕ → ℝ) (s : ℂ) :
    dirichletExponent S c ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (dirichletExponent S c s) := by
  unfold dirichletExponent
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← natCast_cpow_conj, map_neg]

/-- The carrier is real on the real axis: `Z(conj s) = conj Z(s)`. -/
theorem carrier_conj (S : Finset ℕ) (c : ℕ → ℝ) (s : ℂ) :
    carrier S c ((starRingEnd ℂ) s) = (starRingEnd ℂ) (carrier S c s) := by
  unfold carrier chiSymmetrize
  beta_reduce
  rw [dirichletExponent_conj, show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) by
      rw [map_sub, map_one],
    dirichletExponent_conj, zetaChi_conj, Complex.exp_conj, Complex.exp_conj, map_add, map_mul]

/-- The functional equation `Z(1-s) = χ(1-s) Z(s)` on the open strip. -/
theorem carrier_one_sub {S : Finset ℕ} {c : ℕ → ℝ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    carrier S c (1 - s) = zetaChi (1 - s) * carrier S c s :=
  chiSymmetrize_one_sub_at (zetaChi_mul_one_sub_of_mem_strip h0 h1)

/-- No zero in the right half of the strip above the threshold, either sign of the height. -/
theorem carrier_ne_zero_right {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {c : ℕ → ℝ} {s : ℂ}
    (hσ1 : 1 / 2 < s.re) (hσ2 : s.re < 1) (ht8 : 8 ≤ |s.im|)
    (hT : 2 * logMass S c + 1 < Real.log (|s.im| / (2 * Real.pi))) :
    carrier S c s ≠ 0 := by
  rcases le_or_gt 0 s.im with h | h
  · rw [abs_of_nonneg h] at ht8 hT
    exact carrier_ne_zero_of_upper hS hσ1 hσ2 ht8 hT
  · rw [abs_of_neg h] at ht8 hT
    intro hz
    have hconj := carrier_ne_zero_of_upper (s := (starRingEnd ℂ) s) hS
      (by simpa using hσ1) (by simpa using hσ2) (by simpa using ht8) (by simpa using hT)
    apply hconj
    rw [carrier_conj, hz, map_zero]

/-- **Critical-line theorem for symmetrized Euler exponentials.** Every zero of
`exp D(s) + χ(s) exp D(1-s)` in the open critical strip with `|Im s| ≥ 8` and
`log(|Im s|/2π) > 2K + 1`, `K = Σ |c(n)| log n`, lies on the critical line. -/
theorem re_eq_half_of_carrier_eq_zero {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {c : ℕ → ℝ}
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht8 : 8 ≤ |s.im|)
    (hT : 2 * logMass S c + 1 < Real.log (|s.im| / (2 * Real.pi)))
    (hz : carrier S c s = 0) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hz' : carrier S c (1 - s) = 0 := by rw [carrier_one_sub h0 h1, hz, mul_zero]
    have hre : (1 - s).re = 1 - s.re := by simp
    have him : |(1 - s).im| = |s.im| := by simp
    exact carrier_ne_zero_right hS (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rwa [him]) (by rwa [him]) hz'
  · exact heq
  · exact absurd hz (carrier_ne_zero_right hS hgt h1 ht8 hT)

/-! ## The truncated Euler logarithm -/

/-- The coefficients `Λ(n)/log n` of the logarithm of the Euler product. -/
def eulerLogCoeff (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.log n

/-- For the truncated Euler logarithm the logarithmic mass is `Σ_{2≤n≤N} Λ(n)`. -/
theorem logMass_eulerLogCoeff (N : ℕ) :
    logMass (Finset.Icc 2 N) eulerLogCoeff =
      ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n := by
  unfold logMass eulerLogCoeff
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [abs_div, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_pos hlog,
    div_mul_cancel₀ _ hlog.ne']

/-- **Finite Euler depth.** For every `N`, the symmetrized exponential of the truncated Euler
logarithm `exp(Σ_{2≤n≤N} Λ(n) n^{-s}/log n) + χ(s)·exp(Σ_{2≤n≤N} Λ(n) n^{s-1}/log n)` has every
zero of the open strip with `|Im s| ≥ 8` and `log(|Im s|/2π) > 2Σ_{2≤n≤N}Λ(n) + 1` on the
critical line. -/
theorem eulerCarrier_re_eq_half (N : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (ht8 : 8 ≤ |s.im|)
    (hT : 2 * (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n) + 1 <
      Real.log (|s.im| / (2 * Real.pi)))
    (hz : carrier (Finset.Icc 2 N) eulerLogCoeff s = 0) : s.re = 1 / 2 := by
  refine re_eq_half_of_carrier_eq_zero (fun n hn => ?_) h0 h1 ht8 ?_ hz
  · exact le_trans (by norm_num) (Finset.mem_Icc.mp hn).1
  · rwa [logMass_eulerLogCoeff]

end EulerExponentialCarrier

end

end RHTower
