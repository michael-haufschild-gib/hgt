import GaloisForLFunctions.RHTower.SteinhausEulerSecondMoment
import Mathlib.NumberTheory.EulerProduct.Basic

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal coefficient norm, with no lower bound on the real part. -/
theorem norm_steinhausEulerPrimeTerm {n : ℕ} (hn : 0 < n) (s : ℂ) (ω : Omega) :
    ‖steinhausEulerPrimeTerm s ω n‖ = (n : ℝ) ^ (-s.re) := by
  rw [steinhausEulerPrimeTerm, norm_mul, norm_X, one_mul,
    Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

/-- At zero the character's factorization convention is replaced by the multiplicative zero. -/
private def eulerCoefficientHom (s : ℂ) (ω : Omega) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else steinhausEulerPrimeTerm s ω n
  map_one' := by simp [steinhausEulerPrimeTerm, X_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
      steinhausEulerPrimeTerm, X_mul hm hn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring

private theorem smooth_euler_hasSum (N : ℕ) {s : ℂ} (hs : 0 < s.re) (ω : Omega) :
    Summable (fun n : N.smoothNumbers => ‖steinhausEulerPrimeTerm s ω n‖) ∧
      HasSum (fun n : N.smoothNumbers => steinhausEulerPrimeTerm s ω n)
        (steinhausFiniteEulerProduct (Nat.primesBelow N) s ω) := by
  have hp {p : ℕ} (hprime : p.Prime) : ‖eulerCoefficientHom s ω p‖ < 1 := by
    change ‖if p = 0 then 0 else steinhausEulerPrimeTerm s ω p‖ < 1
    rw [if_neg hprime.ne_zero, norm_steinhausEulerPrimeTerm hprime.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_neg_of_pos hs)
  have h := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp N
  have heq (n : N.smoothNumbers) : eulerCoefficientHom s ω n = steinhausEulerPrimeTerm s ω n := by
    change (if (n : ℕ) = 0 then 0 else _) = _
    rw [if_neg (Nat.ne_zero_of_mem_smoothNumbers n.property)]
  have hprod : (∏ p ∈ Nat.primesBelow N, (1 - eulerCoefficientHom s ω p)⁻¹) =
      steinhausFiniteEulerProduct (Nat.primesBelow N) s ω := by
    apply Finset.prod_congr rfl
    intro p hpN
    have hp0 := (Nat.mem_primesBelow.mp hpN).2.ne_zero
    change (1 - (if p = 0 then 0 else _))⁻¹ = _
    rw [if_neg hp0]
  simpa only [heq, hprod] using h

/-- Every finite-prime Dirichlet series is absolutely convergent throughout Re(s)>0. -/
theorem summable_norm_steinhausEulerSmoothSeries (N : ℕ) {s : ℂ} (hs : 0 < s.re) (ω : Omega) :
    Summable (fun n : N.smoothNumbers => ‖steinhausEulerPrimeTerm s ω n‖) :=
  (smooth_euler_hasSum N hs ω).1

/-- Exact smooth-number expansion of the literal finite random Euler product. -/
theorem hasSum_steinhausEulerSmoothSeries (N : ℕ) {s : ℂ} (hs : 0 < s.re) (ω : Omega) :
    HasSum (fun n : N.smoothNumbers => steinhausEulerPrimeTerm s ω n)
      (steinhausFiniteEulerProduct (Nat.primesBelow N) s ω) :=
  (smooth_euler_hasSum N hs ω).2

theorem steinhausFiniteEulerProduct_eq_tsum_smoothNumbers (N : ℕ) {s : ℂ}
    (hs : 0 < s.re) (ω : Omega) :
    steinhausFiniteEulerProduct (Nat.primesBelow N) s ω =
      ∑' n : N.smoothNumbers, X n ω * (n : ℂ) ^ (-s) :=
  (hasSum_steinhausEulerSmoothSeries N hs ω).tsum_eq.symm

/-- The fixed-prime power majorant is summable even on the critical line. -/
theorem summable_smoothNumbers_neg_rpow (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : N.smoothNumbers => (n : ℝ) ^ (-σ)) := by
  have h := summable_norm_steinhausEulerSmoothSeries N (s := (σ : ℂ)) hσ (0 : Omega)
  simpa only [norm_steinhausEulerPrimeTerm (Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (Subtype.property _))), Complex.ofReal_re] using h

end RHTower
