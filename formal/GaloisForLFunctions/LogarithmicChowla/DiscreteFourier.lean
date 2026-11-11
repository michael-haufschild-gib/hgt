import Mathlib

/-!
# Discrete Fourier analysis on `ℤ/R`

`e(x) = exp(2πix)` (`ex`). For `|d| < R`, `Σ_{r<R} e(dr/R) = R·[d = 0]` (`sum_ex_mul_div`). Hence,
for a finite sequence `c_0, …, c_{L−1}` and a shift `d` with `L + d ≤ R`,

`Σ_{r<R} |Σ_{s<L} c_s e(sr/R)|² e(dr/R) = R Σ_{s+d<L} c_s \bar c_{s+d}` (`sum_normSq_mul_ex`),

with Parseval's identity as the case `d = 0` (`sum_normSq_eq`).

The Dirichlet kernel `D_T(θ) = Σ_{u<T} e(−uθ)` has `|D_T(θ)| ≥ T/2` for `|θ| ≤ 1/(4T)`
(`half_le_norm_dirichlet`): after the rotation by `e((T−1)θ/2)` its real part is a sum of `T`
cosines of angles at most `π/4`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Complex

noncomputable section

/-- `e(x) = exp(2πix)`. -/
def ex (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

theorem ex_add (x y : ℝ) : ex (x + y) = ex x * ex y := by
  rw [ex, ex, ex, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem norm_ex (x : ℝ) : ‖ex x‖ = 1 := by
  rw [ex, show (2 * (Real.pi : ℂ) * I * x) = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ex (x : ℝ) : (starRingEnd ℂ) (ex x) = ex (-x) := by
  rw [ex, ex, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem ex_int (n : ℤ) : ex n = 1 := by
  rw [ex, show (2 * (Real.pi : ℂ) * I * ((n : ℝ) : ℂ)) = (n : ℂ) * (2 * Real.pi * I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem ex_add_int (x : ℝ) (n : ℤ) : ex (x + n) = ex x := by
  rw [ex_add, ex_int, mul_one]

theorem ex_re (x : ℝ) : (ex x).re = Real.cos (2 * Real.pi * x) := by
  rw [ex, show (2 * (Real.pi : ℂ) * I * x) = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- **Orthogonality.** `Σ_{r<R} e(dr/R) = R·[d = 0]` for `|d| < R`. -/
theorem sum_ex_mul_div {R : ℕ} (hR : 0 < R) {d : ℤ} (hd : |d| < R) :
    ∑ r ∈ range R, ex (d * r / R) = if d = 0 then (R : ℂ) else 0 := by
  split_ifs with h0
  · subst h0
    simp [ex_zero]
  · set ζ : ℂ := ex (d / R) with hζ
    have hpow : ∀ r : ℕ, ex (d * r / R) = ζ ^ r := by
      intro r
      rw [hζ, ex, ex, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp_rw [hpow]
    have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    have hζR : ζ ^ R = 1 := by
      rw [← hpow, show (d : ℝ) * (R : ℕ) / R = ((d : ℤ) : ℝ) by field_simp]
      exact ex_int d
    have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, ex] at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have h3 : ((d / R : ℝ) : ℂ) = n := by
        have := hn
        rw [show (2 * (Real.pi : ℂ) * I * ((d / R : ℝ) : ℂ))
          = ((d / R : ℝ) : ℂ) * (2 * Real.pi * I) by ring] at this
        exact mul_right_cancel₀ h2 this
      have h4 : (d : ℝ) / R = n := by exact_mod_cast h3
      rw [div_eq_iff hR0] at h4
      have h5 : d = n * R := by exact_mod_cast h4
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at h5
        exact h0 h5
      have : (R : ℤ) ≤ |d| := by
        rw [h5, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ R)]
        exact le_mul_of_one_le_left (by positivity) (Int.one_le_abs hn0)
      omega
    rw [geom_sum_eq hζ1, hζR, sub_self, zero_div]

/-- **Twisted Parseval.** For `L + d ≤ R`,
`Σ_{r<R} |Σ_{s<L} c_s e(sr/R)|² e(dr/R) = R Σ_{s<L} c_s \bar c_{s+d} 1[s+d<L]`. -/
theorem sum_normSq_mul_ex {R L d : ℕ} (hR : 0 < R) (hLd : L + d ≤ R) (c : ℕ → ℂ) :
    ∑ r ∈ range R, ((Complex.normSq (∑ s ∈ range L, c s * ex (s * r / R)) : ℝ) : ℂ)
        * ex (d * r / R)
      = R * ∑ s ∈ range L, if s + d < L then c s * (starRingEnd ℂ) (c (s + d)) else 0 := by
  have hexp : ∀ r : ℕ, ((Complex.normSq (∑ s ∈ range L, c s * ex (s * r / R)) : ℝ) : ℂ)
      * ex (d * r / R)
      = ∑ s ∈ range L, ∑ s' ∈ range L, c s * (starRingEnd ℂ) (c s')
          * ex (((s : ℤ) - s' + d : ℤ) * r / R) := by
    intro r
    rw [← Complex.mul_conj, map_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun s' _ => ?_
    rw [map_mul, conj_ex]
    have : ex (((s : ℤ) - s' + d : ℤ) * r / R)
        = ex (s * r / R) * ex (-(s' * r / R)) * ex (d * r / R) := by
      rw [← ex_add, ← ex_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  simp_rw [hexp]
  rw [sum_comm]
  rw [mul_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [sum_comm]
  simp_rw [← mul_sum]
  have hs' : s < L := mem_range.mp hs
  have horth : ∀ s' ∈ range L,
      ∑ r ∈ range R, ex (((s : ℤ) - s' + d : ℤ) * r / R)
        = if s' = s + d then (R : ℂ) else 0 := by
    intro s' hs''
    have hs''' : s' < L := mem_range.mp hs''
    have hbound : |((s : ℤ) - s' + d)| < R := by
      rw [abs_lt]
      constructor <;> omega
    rw [sum_ex_mul_div hR hbound]
    congr 1
    apply propext
    omega
  rw [sum_congr rfl fun s' hs'' => by rw [horth s' hs'']]
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq' (range L) (s + d)]
  simp only [mem_range]
  split_ifs <;> ring

/-- **Parseval.** For `L ≤ R`, `Σ_{r<R} |Σ_{s<L} c_s e(sr/R)|² = R Σ_{s<L} |c_s|²`. -/
theorem sum_normSq_eq {R L : ℕ} (hR : 0 < R) (hL : L ≤ R) (c : ℕ → ℂ) :
    ∑ r ∈ range R, Complex.normSq (∑ s ∈ range L, c s * ex (s * r / R))
      = R * ∑ s ∈ range L, Complex.normSq (c s) := by
  have h := sum_normSq_mul_ex (d := 0) hR (by simpa using hL) c
  simp only [Nat.cast_zero, zero_mul, zero_div, ex_zero, mul_one, add_zero] at h
  have h' : ((∑ r ∈ range R, Complex.normSq (∑ s ∈ range L, c s * ex (s * r / R)) : ℝ) : ℂ)
      = ((R * ∑ s ∈ range L, Complex.normSq (c s) : ℝ) : ℂ) := by
    push_cast
    rw [h]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    rw [if_pos (mem_range.mp hs), Complex.mul_conj]
  exact_mod_cast h'

/-- The Dirichlet kernel `D_T(θ) = Σ_{u<T} e(−uθ)`. -/
def dirichlet (T : ℕ) (θ : ℝ) : ℂ := ∑ u ∈ range T, ex (-(u * θ))

/-- `|D_T(θ)| ≥ T/2` for `|θ| ≤ 1/(4T)`. -/
theorem half_le_norm_dirichlet {T : ℕ} (hT : 0 < T) {θ : ℝ} (hθ : |θ| ≤ 1 / (4 * T)) :
    (T : ℝ) / 2 ≤ ‖dirichlet T θ‖ := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set φ : ℝ := ((T : ℝ) - 1) / 2 * θ with hφ
  have hrot : ex φ * dirichlet T θ = ∑ u ∈ range T, ex ((((T : ℝ) - 1) / 2 - u) * θ) := by
    rw [dirichlet, mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [← ex_add]
    congr 1
    rw [hφ]
    ring
  have hterm : ∀ u ∈ range T, (1 : ℝ) / 2 ≤ (ex ((((T : ℝ) - 1) / 2 - u) * θ)).re := by
    intro u hu
    have hu' : (u : ℝ) ≤ T - 1 := by
      have := mem_range.mp hu
      have : (u : ℝ) + 1 ≤ T := by exact_mod_cast this
      linarith
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    have habs : |((T : ℝ) - 1) / 2 - u| ≤ T / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hangle : |2 * Real.pi * ((((T : ℝ) - 1) / 2 - u) * θ)| ≤ Real.pi / 4 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos]
      calc 2 * Real.pi * (|((T : ℝ) - 1) / 2 - u| * |θ|)
          ≤ 2 * Real.pi * (T / 2 * (1 / (4 * T))) := by
            gcongr
      _ = Real.pi / 4 := by field_simp
    rw [ex_re]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ((((T : ℝ) - 1) / 2 - u) * θ))
    have hsq : (2 * Real.pi * ((((T : ℝ) - 1) / 2 - u) * θ)) ^ 2 ≤ (Real.pi / 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hangle 2
    have hpi : (Real.pi / 4) ^ 2 ≤ 1 := by
      have := Real.pi_le_four
      have h0 := Real.pi_pos
      rw [div_pow]
      rw [div_le_one (by norm_num)]
      nlinarith
    linarith
  have hre : (T : ℝ) / 2 ≤ (ex φ * dirichlet T θ).re := by
    rw [hrot, re_sum]
    calc (T : ℝ) / 2 = ∑ _u ∈ range T, (1 : ℝ) / 2 := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum hterm
  calc (T : ℝ) / 2 ≤ (ex φ * dirichlet T θ).re := hre
    _ ≤ ‖ex φ * dirichlet T θ‖ := Complex.re_le_norm _
    _ = ‖dirichlet T θ‖ := by rw [norm_mul, norm_ex, one_mul]

end

end GaloisForLFunctions.LogarithmicChowla
