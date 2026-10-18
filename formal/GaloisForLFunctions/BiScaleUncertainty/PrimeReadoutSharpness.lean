import GaloisForLFunctions.BiScaleUncertainty.SixthReadoutStability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharp stability exponents for actual prime-family observations

Two coefficients at the fixed odd primes 3 and 5 embed the degeneration families
at every cutoff `N+10`; all additional modes are zero. Their exact common-sign
errors and actual normalized sixth readouts prove the optimal exponents `1/6`
at zero and `1/3` on a nonzero-mass stratum. Power barriers quantify over every
real exponent and are proved by an explicit exponential witness.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeSharpness
set_option autoImplicit false

/-- Actual prime coefficients, supported on 3 and 5 at cutoff `N+10`. -/
def coefficients (x y : ℝ) (p : ℕ) : ℝ :=
  (if p = 3 then x else 0) + (if p = 5 then y else 0)

def vector (N : ℕ) (x y : ℝ) (p : oddPrimeModes (N+10)) : ℝ := coefficients x y p

private def primeThree (N : ℕ) : oddPrimeModes (N+10) :=
  ⟨3, by norm_num [mem_oddPrimeModes]⟩
private def primeFive (N : ℕ) : oddPrimeModes (N+10) :=
  ⟨5, by norm_num [mem_oddPrimeModes]⟩

private theorem sum_two (N : ℕ) (F : ℝ → ℝ → ℝ) (x y u v : ℝ)
    (hF : F 0 0 = 0) :
    (∑ p : oddPrimeModes (N+10), F (vector N x y p) (vector N u v p)) = F x u + F y v := by
  have h3 (p : oddPrimeModes (N+10)) : ((p : ℕ) = 3) ↔ p = primeThree N := by
    constructor
    · exact fun h => Subtype.ext h
    · exact fun h => congrArg Subtype.val h
  have h5 (p : oddPrimeModes (N+10)) : ((p : ℕ) = 5) ↔ p = primeFive N := by
    constructor
    · exact fun h => Subtype.ext h
    · exact fun h => congrArg Subtype.val h
  have hne : primeThree N ≠ primeFive N := by
    intro h
    have he := congrArg Subtype.val h
    norm_num [primeThree, primeFive] at he
  have he (p : oddPrimeModes (N+10)) :
      F (vector N x y p) (vector N u v p) =
        (if p = primeThree N then F x u else 0) + (if p = primeFive N then F y v else 0) := by
    simp only [vector, coefficients, h3, h5]
    by_cases hp : p = primeThree N <;> by_cases hq : p = primeFive N <;> simp_all
  simp_rw [he, Finset.sum_add_distrib]
  simp

private theorem error_two (N : ℕ) (x y u v : ℝ) :
    CubedGram.error6 (vector N x y) (vector N u v) = (x-u)^6+(y-v)^6 := by
  exact sum_two N (fun a b => (a-b)^6) x y u v (by norm_num)

private theorem vector_neg (N : ℕ) (u v : ℝ) :
    (fun p => -vector N u v p) = vector N (-u) (-v) := by
  funext p
  unfold vector coefficients
  split_ifs <;> ring

private theorem error_neg_two (N : ℕ) (x y u v : ℝ) :
    CubedGram.error6 (vector N x y) (fun p => -vector N u v p) = (x+u)^6+(y+v)^6 := by
  rw [vector_neg, error_two]
  simp only [sub_neg_eq_add]

private theorem mass_two (N : ℕ) (x y u v : ℝ) :
    CubedGram.mass6 (vector N x y) (vector N u v) = x^6+u^6+(y^6+v^6) := by
  exact sum_two N (fun a b => a^6+b^6) x y u v (by norm_num)

private theorem noise_two (N : ℕ) (x y u v : ℝ) :
    primeSixthNoise (N+10) (coefficients x y) (coefficients u v) =
      (x^6-u^6)^2+2*((x*y)^3-(u*v)^3)^2+(y^6-v^6)^2 := by
  unfold primeSixthNoise
  simp only [normalizedPrimeSixthReadout_eq]
  change (∑ p : oddPrimeModes (N+10), ∑ q : oddPrimeModes (N+10),
    ((vector N x y p * vector N x y q)^3-(vector N u v p * vector N u v q)^3)^2) = _
  have hi (p : oddPrimeModes (N+10)) :
      (∑ q : oddPrimeModes (N+10),
        ((vector N x y p * vector N x y q)^3-(vector N u v p * vector N u v q)^3)^2) =
      ((vector N x y p*x)^3-(vector N u v p*u)^3)^2 +
      ((vector N x y p*y)^3-(vector N u v p*v)^3)^2 :=
    sum_two N (fun a b => ((vector N x y p*a)^3-(vector N u v p*b)^3)^2)
      x y u v (by ring)
  simp_rw [hi]
  rw [Finset.sum_add_distrib,
    sum_two N (fun a b => ((a*x)^3-(b*u)^3)^2) x y u v (by ring),
    sum_two N (fun a b => ((a*y)^3-(b*v)^3)^2) x y u v (by ring)]
  ring

/-- Sixth power of the coefficient distance modulo the actual common-sign ambiguity. -/
def quotientError (N : ℕ) (x y u v : ℝ) : ℝ :=
  min (CubedGram.error6 (vector N x y) (vector N u v))
    (CubedGram.error6 (vector N x y) (fun p => -vector N u v p))

/-- A one-mode degeneration inside the actual sieve family. -/
theorem one_mode_scaling (N : ℕ) (t : ℝ) :
    quotientError N t 0 0 0 = t^6 ∧
      primeSixthNoise (N+10) (coefficients t 0) (coefficients 0 0) = t^12 := by
  constructor
  · simp [quotientError, error_two, error_neg_two]
  · rw [noise_two]
    ring

/-- A sign collision with nonvanishing total mass inside the actual sieve family. -/
theorem two_mode_vanishing (N : ℕ) (t : ℝ) :
    quotientError N 1 t 1 (-t) = min (64*t^6) 64 ∧
      primeSixthNoise (N+10) (coefficients 1 t) (coefficients 1 (-t)) = 8*t^6 ∧
      CubedGram.mass6 (vector N 1 t) (vector N 1 (-t)) = 2+2*t^6 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold quotientError
    rw [error_two, error_neg_two]
    congr 1 <;> ring
  · rw [noise_two]
    ring
  · rw [mass_two]
    ring

private theorem small_power_iff (u v : ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → t^u ≤ C*t^v) ↔ v ≤ u := by
  constructor
  · rintro ⟨C,hC⟩
    by_contra h
    have hδ : 0 < v-u := by linarith
    let x : ℝ := (|C|+1)/(v-u)
    let t : ℝ := Real.exp (-x)
    have hx : 0 < x := by dsimp [x]; positivity
    have ht : 0 < t := Real.exp_pos _
    have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hd : 0 < t^v := by positivity
    have hb : t^(u-v) ≤ C := by
      rw [Real.rpow_sub ht]
      exact (div_le_iff₀ hd).mpr (hC t ht ht1)
    have he : t^(u-v) = Real.exp (|C|+1) := by
      rw [Real.rpow_def_of_pos ht]
      change Real.exp (Real.log (Real.exp (-x))*(u-v)) = _
      rw [Real.log_exp]
      congr 1
      dsimp [x]
      field_simp [hδ.ne']; ring
    rw [he] at hb
    linarith [Real.add_one_le_exp (|C|+1), le_abs_self C]
  · intro hv
    refine ⟨1, fun t ht ht1 => ?_⟩
    simpa only [one_mul] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hv

private theorem scaled_power_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (k l : ℕ) (α : ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → a*t^k ≤ C*(b*t^l)^α) ↔
      (l : ℝ)*α ≤ (k : ℝ) := by
  have hbα : 0 < b^α := by positivity
  have hp (t : ℝ) (ht : 0 < t) : (b*t^l)^α = b^α*t^((l : ℝ)*α) := by
    rw [Real.mul_rpow hb.le (pow_nonneg ht.le _), ← Real.rpow_natCast t l,
      ← Real.rpow_mul ht.le]
  constructor
  · rintro ⟨C,hC⟩
    apply (small_power_iff (k : ℝ) ((l : ℝ)*α)).mp
    refine ⟨C*b^α/a, fun t ht ht1 => ?_⟩
    have he := hC t ht ht1
    rw [hp t ht, ← Real.rpow_natCast t k] at he
    calc
      _ = (a*t^(k : ℝ))/a := by field_simp
      _ ≤ (C*(b^α*t^((l : ℝ)*α)))/a := div_le_div_of_nonneg_right he ha.le
      _ = _ := by ring
  · intro hα
    refine ⟨a/b^α, fun t ht ht1 => ?_⟩
    rw [hp t ht, ← Real.rpow_natCast t k]
    have he : (a/b^α)*(b^α*t^((l : ℝ)*α)) = a*t^((l : ℝ)*α) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht ht1 hα) ha.le

/-- No uniform power bound improves the sixth-root norm exponent at zero.
Here the distance is raised to six and the observation norm is squared. -/
theorem one_mode_power_barrier (N : ℕ) (α : ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      quotientError N t 0 0 0 ≤
        C*(primeSixthNoise (N+10) (coefficients t 0) (coefficients 0 0))^α) ↔ α ≤ 1/2 := by
  simp_rw [(one_mode_scaling N _).1, (one_mode_scaling N _).2]
  have h := scaled_power_iff 1 1 (by norm_num) (by norm_num) 6 12 α
  simp only [one_mul, Nat.cast_ofNat] at h
  rw [h]
  constructor <;> intro h <;> linarith

/-- The nonzero-mass stratum has sharp cube-root norm exponent at a vanishing mode. -/
theorem two_mode_power_barrier (N : ℕ) (α : ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      quotientError N 1 t 1 (-t) ≤
        C*(primeSixthNoise (N+10) (coefficients 1 t) (coefficients 1 (-t)))^α) ↔ α ≤ 1 := by
  have he (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : quotientError N 1 t 1 (-t) = 64*t^6 := by
    rw [(two_mode_vanishing N t).1]
    apply min_eq_left
    have h6 : t^6 ≤ (1 : ℝ)^6 := by gcongr
    norm_num at h6
    linarith
  have heq : (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      quotientError N 1 t 1 (-t) ≤
        C*(primeSixthNoise (N+10) (coefficients 1 t) (coefficients 1 (-t)))^α) ↔
      (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → 64*t^6 ≤ C*(8*t^6)^α) := by
    constructor <;> rintro ⟨C,hC⟩ <;> refine ⟨C, fun t ht ht1 => ?_⟩
    · simpa only [he t ht ht1, (two_mode_vanishing N t).2.1] using hC t ht ht1
    · simpa only [he t ht ht1, (two_mode_vanishing N t).2.1] using hC t ht ht1
  rw [heq, scaled_power_iff 64 8 (by norm_num) (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeSharpness
