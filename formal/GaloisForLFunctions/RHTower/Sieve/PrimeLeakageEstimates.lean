import GaloisForLFunctions.RHTower.Sieve.PrimeSumDominatedVanishing
import GaloisForLFunctions.RHTower.ProjectivePrimeWeylModel

/-!
# The prime Weyl leakage as a function of the prime

The exact compression leakage of the projective clock of a prime `p`,

`L_p(z) = ((p-1)/p) · (e^z - 1)² / (p + e^{2z})`,

is recorded here as a function of `p` directly, together with the three estimates that an all-prime
limit needs:

* it is nonnegative and bounded by its leading prime-density term `(e^z - 1)²/p`;
* it stays uniformly below `1`, in fact below `(E²+1)/(2+E²)` whenever `e^z ≤ E` — so `1 - L_p` is
  bounded away from `0` and its logarithm is controlled;
* it differs from `(e^z - 1)²/p` by `O(p⁻²)`.

The last two are exactly what turns the product `∏_p √(1 - L_p)` into an exponentiated prime sum
with a summable remainder.  The identification with the geometric leakage of the projective clock
is `primeLeakage_eq_projLeakageValue`.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-- The exact Weyl compression leakage of the projective clock of the prime `p`. -/
def primeLeakage (p : ℕ) (z : ℝ) : ℝ :=
  ((p : ℝ) - 1) / (p : ℝ) * (Real.exp z - 1) ^ 2 / ((p : ℝ) + Real.exp z ^ 2)

/-- The prime leakage is the geometric leakage of the projective clock `P¹(F_p)`. -/
theorem primeLeakage_eq_projLeakageValue (p : ℕ) [Fact p.Prime] (z : ℝ) :
    primeLeakage p z = RHTower.projLeakageValue (Option (ZMod p)) z := by
  rw [primeLeakage, RHTower.projLeakageValue, RHTower.projDeg_optionZMod]

@[simp]
theorem primeLeakage_zero (p : ℕ) : primeLeakage p 0 = 0 := by
  simp [primeLeakage]

theorem primeLeakage_nonneg {p : ℕ} (hp : 2 ≤ p) (z : ℝ) : 0 ≤ primeLeakage p z := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hE : (0 : ℝ) < Real.exp z := Real.exp_pos z
  rw [primeLeakage]
  have h1 : (0 : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) := by
    apply div_nonneg <;> linarith
  have h2 : (0 : ℝ) < (p : ℝ) + Real.exp z ^ 2 := by positivity
  positivity

/-- The leakage is bounded by its leading prime-density term. -/
theorem primeLeakage_le_div {p : ℕ} (hp : 2 ≤ p) (z : ℝ) :
    primeLeakage p z ≤ (Real.exp z - 1) ^ 2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hE : (0 : ℝ) < Real.exp z := Real.exp_pos z
  have hden : (0 : ℝ) < (p : ℝ) + Real.exp z ^ 2 := by positivity
  have hsq : (0 : ℝ) ≤ (Real.exp z - 1) ^ 2 := sq_nonneg _
  rw [primeLeakage, div_le_div_iff₀ hden (by linarith)]
  have hfac : ((p : ℝ) - 1) / (p : ℝ) * (Real.exp z - 1) ^ 2 * (p : ℝ)
      = ((p : ℝ) - 1) * (Real.exp z - 1) ^ 2 := by
    field_simp
  rw [hfac]
  nlinarith [hsq, hden, hpR]

/-- The leakage stays uniformly below `1` on any bounded weight range. -/
theorem primeLeakage_le_theta {p : ℕ} (hp : 2 ≤ p) {z F : ℝ} (hz : z ≤ F) :
    primeLeakage p z ≤ (Real.exp F ^ 2 + 1) / (2 + Real.exp F ^ 2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hE : (0 : ℝ) < Real.exp z := Real.exp_pos z
  have hEF : Real.exp z ≤ Real.exp F := Real.exp_le_exp.mpr hz
  have hEsq : Real.exp z ^ 2 ≤ Real.exp F ^ 2 := by nlinarith [hE.le, hEF]
  have hden : (0 : ℝ) < (p : ℝ) + Real.exp z ^ 2 := by positivity
  have hden2 : (0 : ℝ) < 2 + Real.exp z ^ 2 := by positivity
  have hdenF : (0 : ℝ) < 2 + Real.exp F ^ 2 := by positivity
  have hfrac1 : ((p : ℝ) - 1) / (p : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hA : (Real.exp z - 1) ^ 2 ≤ Real.exp z ^ 2 + 1 := by nlinarith [hE]
  have hnum : ((p : ℝ) - 1) / (p : ℝ) * (Real.exp z - 1) ^ 2 ≤ Real.exp z ^ 2 + 1 :=
    le_trans (mul_le_of_le_one_left (sq_nonneg _) hfrac1) hA
  have hstep1 : primeLeakage p z ≤ (Real.exp z ^ 2 + 1) / (2 + Real.exp z ^ 2) := by
    calc primeLeakage p z
        = (((p : ℝ) - 1) / (p : ℝ) * (Real.exp z - 1) ^ 2) / ((p : ℝ) + Real.exp z ^ 2) := rfl
      _ ≤ (Real.exp z ^ 2 + 1) / ((p : ℝ) + Real.exp z ^ 2) := by gcongr
      _ ≤ (Real.exp z ^ 2 + 1) / (2 + Real.exp z ^ 2) := by
          gcongr
  refine le_trans hstep1 ?_
  rw [div_le_div_iff₀ hden2 hdenF]
  nlinarith [hEsq, hE]

theorem theta_lt_one (F : ℝ) :
    (Real.exp F ^ 2 + 1) / (2 + Real.exp F ^ 2) < 1 := by
  have hdenF : (0 : ℝ) < 2 + Real.exp F ^ 2 := by positivity
  rw [div_lt_one hdenF]
  linarith

/-- **The `O(p⁻²)` expansion of the prime leakage.** -/
theorem abs_primeLeakage_sub_div_le {p : ℕ} (hp : 2 ≤ p) (z : ℝ) :
    |primeLeakage p z - (Real.exp z - 1) ^ 2 / (p : ℝ)|
      ≤ (Real.exp z - 1) ^ 2 * (1 + Real.exp z ^ 2) / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hE : (0 : ℝ) < Real.exp z := Real.exp_pos z
  have hden : (0 : ℝ) < (p : ℝ) + Real.exp z ^ 2 := by positivity
  have hkey : primeLeakage p z - (Real.exp z - 1) ^ 2 / (p : ℝ)
      = -((Real.exp z - 1) ^ 2 * (1 + Real.exp z ^ 2) /
          ((p : ℝ) * ((p : ℝ) + Real.exp z ^ 2))) := by
    rw [primeLeakage]
    field_simp
    ring
  rw [hkey, abs_neg, abs_of_nonneg (by positivity)]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  nlinarith [sq_nonneg (Real.exp z), hpR]

/-! ## The logarithm near one -/

/-- **The logarithmic defect is quadratic.**  For `0 ≤ u ≤ θ < 1`, `log (1-u) + u` is `O(u²)`. -/
theorem abs_log_one_sub_add_le {u θ : ℝ} (h0 : 0 ≤ u) (hθ : θ < 1) (huθ : u ≤ θ) :
    |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - θ) := by
  have hu1 : u < 1 := lt_of_le_of_lt huθ hθ
  have habs : |u| < 1 := by rw [abs_of_nonneg h0]; exact hu1
  have h1 := Real.abs_log_sub_add_sum_range_le habs 1
  simp at h1
  rw [abs_of_nonneg h0] at h1
  rw [add_comm (Real.log (1 - u)) u]
  refine le_trans h1 ?_
  refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
  linarith

end

end RHTower.Sieve
