import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Exponential

/-!
# A finite net on the unit circle

`circlePoint M m = exp((2πm/M − π)i)` are `M` equally spaced points on the unit circle, and
`exists_circlePoint_close` says they form a `4π/M`-net: every complex number of modulus one lies
within `4π/M` of one of them.

This is the pigeonhole input for the construction of multiplicative Bohr sets: applying it to the
values of finitely many Dirichlet characters at a point produces a partition of `(ZMod q)ˣ` into
`M^k` cells on each of which all the characters are nearly constant.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AddComb

/-- `M` equally spaced points on the unit circle, starting at `-1`. -/
def circlePoint (M m : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * m / M - Real.pi : ℝ) : ℂ) * Complex.I)

/-- The `M` equally spaced points are `4π/M`-dense on the unit circle. -/
theorem exists_circlePoint_close {z : ℂ} (hz : ‖z‖ = 1) {M : ℕ}
    (hM : 2 * Real.pi ≤ (M : ℝ)) :
    ∃ m < M, ‖z - circlePoint M m‖ ≤ 4 * Real.pi / (M : ℝ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMnat : 0 < M := by exact_mod_cast hMpos
  set θ : ℝ := Complex.arg z with hθdef
  have hθ1 : -Real.pi < θ := Complex.neg_pi_lt_arg z
  have hθ2 : θ ≤ Real.pi := Complex.arg_le_pi z
  set t : ℝ := (θ + Real.pi) / (2 * Real.pi) with htdef
  have ht0 : 0 ≤ t := by
    rw [htdef]
    apply div_nonneg <;> linarith
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one (by linarith)]
    linarith
  set m : ℕ := min (Nat.floor ((M : ℝ) * t)) (M - 1) with hmdef
  have hmlt : m < M := by
    have : m ≤ M - 1 := min_le_right _ _
    omega
  have hmclose : |t - (m : ℝ) / (M : ℝ)| ≤ 1 / (M : ℝ) := by
    by_cases hle : Nat.floor ((M : ℝ) * t) ≤ M - 1
    · have hm : m = Nat.floor ((M : ℝ) * t) := min_eq_left hle
      have hfl : ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) ≤ (M : ℝ) * t :=
        Nat.floor_le (by positivity)
      have hfu : (M : ℝ) * t < ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      rw [hm, abs_le]
      have hlow : ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) / (M : ℝ) ≤ t := by
        rw [div_le_iff₀ hMpos]
        nlinarith [hfl]
      have hup : t ≤ ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by
        have hcomb : ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) / (M : ℝ) + 1 / (M : ℝ)
            = (((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) + 1) / (M : ℝ) := by ring
        rw [hcomb, le_div_iff₀ hMpos]
        nlinarith [hfu]
      have hMinv : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      constructor <;> linarith
    · have hge : M ≤ Nat.floor ((M : ℝ) * t) := by omega
      have hM1 : (M : ℝ) ≤ (M : ℝ) * t := by
        calc (M : ℝ) ≤ ((Nat.floor ((M : ℝ) * t) : ℕ) : ℝ) := by exact_mod_cast hge
          _ ≤ (M : ℝ) * t := Nat.floor_le (by positivity)
      have ht1' : t = 1 := by nlinarith [ht1, hMpos]
      have hm : m = M - 1 := min_eq_right (by omega)
      have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        have h1 : 1 ≤ M := hMnat
        rw [Nat.cast_sub h1, Nat.cast_one]
      rw [hm, ht1', hcast]
      have hval : (1 : ℝ) - ((M : ℝ) - 1) / (M : ℝ) = 1 / (M : ℝ) := by
        field_simp
        ring
      rw [hval, abs_of_nonneg (by positivity)]
  have hzexp : z = Complex.exp ((θ : ℂ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set β : ℝ := 2 * Real.pi * m / M - Real.pi with hβdef
  have hdiff : |θ - β| ≤ 2 * Real.pi / (M : ℝ) := by
    have hexp : θ - β = 2 * Real.pi * (t - (m : ℝ) / (M : ℝ)) := by
      rw [hβdef, htdef]
      field_simp
      ring
    rw [hexp, abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * Real.pi * |t - (m : ℝ) / (M : ℝ)| ≤ 2 * Real.pi * (1 / (M : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmclose (by positivity)
      _ = 2 * Real.pi / (M : ℝ) := by ring
  have hsmall : ‖((θ - β : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have : 2 * Real.pi / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMpos]
      linarith
    linarith [hdiff]
  have hfactor : z - circlePoint M m
      = Complex.exp ((β : ℂ) * Complex.I)
        * (Complex.exp (((θ - β : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [circlePoint, hzexp, ← hβdef]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨m, hmlt, ?_⟩
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ‖Complex.exp (((θ - β : ℝ) : ℂ) * Complex.I) - 1‖
      ≤ 2 * ‖((θ - β : ℝ) : ℂ) * Complex.I‖ := Complex.norm_exp_sub_one_le hsmall
    _ = 2 * |θ - β| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * (2 * Real.pi / (M : ℝ)) := by linarith [hdiff]
    _ = 4 * Real.pi / (M : ℝ) := by ring

end GaloisForLFunctions.HTGeometry.AddComb
