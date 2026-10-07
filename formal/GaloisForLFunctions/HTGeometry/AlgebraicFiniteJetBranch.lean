import GaloisForLFunctions.Bottcher.AlgebraicBranch
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Polynomial

/-!
# An analytic branch from a nonsingular formal algebraic branch

A formal root of a bivariate complex polynomial, with nonzero formal derivative,
produces an actual local analytic root with the same constant term. The formal
derivative need not have nonzero constant term.

Truncate the formal root past the derivative's order. Exact Taylor divisibility
then reduces the equation to a polynomial whose special fiber is linear with
nonzero slope. The scalar analytic implicit-function theorem finishes the proof.
No convergence-radius or coefficient-growth estimate is used.

This is classical formal-to-analytic machinery, used as a dependency of the
reflected-cosine algebraic-curve classification; no novelty or RH claim is made.
-/

namespace GaloisForLFunctions.HTGeometry.AlgebraicFiniteJetBranch

open Polynomial
open scoped Topology

noncomputable section

abbrev Series := PowerSeries ℂ
abbrev BiPoly := Polynomial (Polynomial ℂ)

/-- Regard the first polynomial variable as a formal-series variable. -/
def formalize (P : BiPoly) : Polynomial Series :=
  P.map Polynomial.coeToPowerSeries.ringHom

@[simp] theorem formalize_eval_coe (P : BiPoly) (p : Polynomial ℂ) :
    (formalize P).eval (p : Series) = ((P.eval p : Polynomial ℂ) : Series) := by
  rw [formalize, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Polynomial.coeToPowerSeries.ringHom p

@[simp] theorem formalize_derivative (P : BiPoly) :
    formalize P.derivative = (formalize P).derivative := by
  simp [formalize]

theorem polynomial_X_pow_dvd_of_series {p : Polynomial ℂ} {n : ℕ}
    (h : (PowerSeries.X : Series) ^ n ∣ (p : Series)) :
    (Polynomial.X : Polynomial ℂ) ^ n ∣ p := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  simpa using (PowerSeries.X_pow_dvd_iff.mp h j hj)

/-- Substitute the finite jet plus a monomial times a new dependent variable. -/
def scaledTaylor (P : BiPoly) (p : Polynomial ℂ) (m : ℕ) : BiPoly :=
  (P.taylor p).comp (C ((Polynomial.X : Polynomial ℂ) ^ m) * X)

theorem scaledTaylor_coeff (P : BiPoly) (p : Polynomial ℂ) (m i : ℕ) :
    (scaledTaylor P p m).coeff i = (P.taylor p).coeff i * Polynomial.X ^ (m * i) := by
  rw [scaledTaylor, Polynomial.comp_C_mul_X_coeff, ← pow_mul]

/-- Exact finite-jet division produces a polynomial with a linear special fiber. -/
theorem exists_scaled_factor (P : BiPoly) (y : Series)
    (hy : (formalize P).eval y = 0)
    (hd : (formalize P).derivative.eval y ≠ 0) :
    ∃ (m k : ℕ) (p : Polynomial ℂ) (G : BiPoly) (z : Series),
      0 < m ∧ y = (p : Series) + PowerSeries.X ^ m * z ∧
      scaledTaylor P p m = C (Polynomial.X ^ k) * G ∧
      (formalize G).eval z = 0 ∧
      (G.coeff 1).coeff 0 ≠ 0 ∧
      ∀ i, 2 ≤ i → (G.coeff i).coeff 0 = 0 := by
  let F := formalize P
  let D := F.derivative.eval y
  let d := D.order.toNat
  let m := d + 1
  let p := PowerSeries.trunc m y
  have hm : 0 < m := by dsimp [m]; omega
  have hdm : d < m := by dsimp [m]; omega
  have hrem : (PowerSeries.X : Series) ^ m ∣ y - (p : Series) := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    simp only [map_sub, Polynomial.coeff_coe, p, PowerSeries.coeff_trunc, if_pos hi, sub_self]
  obtain ⟨z, hz⟩ := hrem
  have hyp : y = (p : Series) + PowerSeries.X ^ m * z := by linear_combination hz
  have hdiff : (PowerSeries.X : Series) ^ m ∣
      ((P.derivative.eval p : Polynomial ℂ) : Series) - D := by
    have hp : (PowerSeries.X : Series) ^ m ∣ (p : Series) - y := by
      rw [← neg_sub]
      exact dvd_neg.mpr ⟨z, hz⟩
    simpa only [F, D, ← formalize_derivative, formalize_eval_coe] using
      hp.trans (Polynomial.sub_dvd_eval_sub (p : Series) y F.derivative)
  have hD : (PowerSeries.X : Series) ^ d ∣ D := PowerSeries.X_pow_order_dvd
  have hDp : (PowerSeries.X : Series) ^ d ∣ ((P.derivative.eval p : Polynomial ℂ) : Series) := by
    have hsub := (pow_dvd_pow PowerSeries.X hdm.le).trans hdiff
    convert dvd_add hsub hD using 1
    ring
  have hcoeffD : PowerSeries.coeff d ((P.derivative.eval p : Polynomial ℂ) : Series) =
      PowerSeries.coeff d D := by
    have hh := PowerSeries.X_pow_dvd_iff.mp hdiff d hdm
    simpa only [map_sub, sub_eq_zero] using hh
  have hconst : (PowerSeries.X : Series) ^ (m + d) ∣ ((P.eval p : Polynomial ℂ) : Series) := by
    obtain ⟨a, ha⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
      F (p : Series) (PowerSeries.X ^ m * z)
    rw [← hyp, hy] at ha
    have h2 : (PowerSeries.X : Series) ^ (m + d) ∣
        a * (PowerSeries.X ^ m * z) ^ 2 := by
      have hp2 : (PowerSeries.X : Series) ^ (m + d) ∣ PowerSeries.X ^ (2 * m) :=
        pow_dvd_pow _ (by omega)
      convert dvd_mul_of_dvd_left hp2 (a * z ^ 2) using 1
      ring
    have h1 : (PowerSeries.X : Series) ^ (m + d) ∣
        F.derivative.eval (p : Series) * (PowerSeries.X ^ m * z) := by
      obtain ⟨v, hv⟩ := hDp
      refine ⟨v * z, ?_⟩
      rw [← formalize_derivative, formalize_eval_coe, hv, pow_add]
      ring
    have hh := dvd_neg.mpr (dvd_add h2 h1)
    convert hh using 1
    rw [← formalize_eval_coe]
    linear_combination ha
  have hdiv : C ((Polynomial.X : Polynomial ℂ) ^ (m + d)) ∣ scaledTaylor P p m := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    rw [scaledTaylor_coeff]
    rcases i with _ | i
    · simpa only [taylor_coeff_zero, mul_zero, pow_zero, mul_one] using
        polynomial_X_pow_dvd_of_series hconst
    rcases i with _ | i
    · simp only [Nat.zero_add, Nat.mul_one, taylor_coeff_one]
      obtain ⟨v, hv⟩ := polynomial_X_pow_dvd_of_series hDp
      refine ⟨v, ?_⟩
      rw [hv, pow_add]
      ring
    · exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by nlinarith)) _
  obtain ⟨G, hG⟩ := hdiv
  have hGcoeff (i : ℕ) :
      (scaledTaylor P p m).coeff i = Polynomial.X ^ (m + d) * G.coeff i := by
    rw [hG, coeff_C_mul]
  have hlead (i : ℕ) :
      PowerSeries.coeff (m + d) ((scaledTaylor P p m).coeff i : Series) =
        (G.coeff i).coeff 0 := by
    rw [hGcoeff, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    simpa using PowerSeries.coeff_X_pow_mul (G.coeff i : Series) (m + d) 0
  have hrootG : (formalize G).eval z = 0 := by
    have hQ : (formalize (scaledTaylor P p m)).eval z = 0 := by
      simpa [formalize, scaledTaylor, Polynomial.eval_comp, Polynomial.map_comp,
        Polynomial.taylor_eval, hyp, add_comm] using hy
    rw [hG] at hQ
    have hh : (PowerSeries.X : Series) ^ (m + d) * (formalize G).eval z = 0 := by
      simpa [formalize] using hQ
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  refine ⟨m, m + d, p, G, z, hm, hyp, hG, hrootG, ?_, ?_⟩
  · rw [← hlead 1, scaledTaylor_coeff, taylor_coeff_one, mul_one,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    rw [Nat.add_comm m d, PowerSeries.coeff_mul_X_pow, hcoeffD]
    exact PowerSeries.coeff_order hd
  · intro i hi
    rw [← hlead i, scaledTaylor_coeff, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coeff_mul_X_pow']
    rw [if_neg (by nlinarith)]

/-- Specialize the parameter while retaining the dependent polynomial variable. -/
def specialize (P : BiPoly) (s : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom s)

/-- Evaluate the parameter and the dependent variable. -/
def evalAt (P : BiPoly) (s w : ℂ) : ℂ := (specialize P s).eval w

theorem evalAt_sum (P : BiPoly) (s w : ℂ) :
    evalAt P s w = ∑ i ∈ P.support, (P.coeff i).aeval s * w ^ i := by
  simp [evalAt, specialize, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, Polynomial.coe_aeval_eq_eval]

theorem map_formalize_constantCoeff (P : BiPoly) :
    (formalize P).map PowerSeries.constantCoeff = specialize P 0 := by
  ext i
  simp [formalize, specialize, Polynomial.coeff_zero_eq_eval_zero]

theorem evalAt_zero_of_formal_root (P : BiPoly) (z : Series)
    (hz : (formalize P).eval z = 0) :
    evalAt P 0 (PowerSeries.constantCoeff z) = 0 := by
  rw [evalAt, ← map_formalize_constantCoeff, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, hz, map_zero]

theorem exists_analytic_root_of_linear_specialization (G : BiPoly) (z : Series)
    (hz : (formalize G).eval z = 0)
    (h1 : (G.coeff 1).coeff 0 ≠ 0)
    (hhigh : ∀ i, 2 ≤ i → (G.coeff i).coeff 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = PowerSeries.constantCoeff z ∧
      ∀ᶠ s in 𝓝 0, evalAt G s (g s) = 0 := by
  let H := specialize G 0
  have hcoeff (i : ℕ) : H.coeff i = (G.coeff i).coeff 0 := by
    simp [H, specialize, ← Polynomial.coeff_zero_eq_eval_zero]
  have hlin : H = C (H.coeff 0) + C (H.coeff 1) * X := by
    ext i
    rcases i with _ | i
    · simp
    rcases i with _ | i
    · simp
    · have hh : H.coeff (i + 1 + 1) = 0 := by rw [hcoeff]; exact hhigh _ (by omega)
      simpa using hh
  have hev (w : ℂ) : evalAt G 0 w = H.coeff 0 + H.coeff 1 * w := by
    change H.eval w = _
    conv_lhs => rw [hlin]
    simp
  have hpartial : HasDerivAt (fun w => evalAt G 0 w) (H.coeff 1)
      (PowerSeries.constantCoeff z) := by
    simp_rw [hev]
    simpa using ((hasDerivAt_id (PowerSeries.constantCoeff z)).const_mul
      (H.coeff 1)).const_add (H.coeff 0)
  have hd : H.coeff 1 ≠ 0 := by rw [hcoeff]; exact h1
  obtain ⟨g, hg, hg0, hgroot⟩ := Bottcher.exists_analyticAt_branch_poly G
    (by rw [← evalAt_sum]; exact evalAt_zero_of_formal_root G z hz)
    (by simpa only [evalAt_sum] using hpartial) hd
  exact ⟨g, hg, hg0, by simpa only [evalAt_sum] using hgroot⟩

theorem evalAt_scaledTaylor (P : BiPoly) (p : Polynomial ℂ) (m : ℕ) (s w : ℂ) :
    evalAt (scaledTaylor P p m) s w = evalAt P s (p.eval s + s ^ m * w) := by
  simp [evalAt, specialize, scaledTaylor, Polynomial.map_comp, Polynomial.eval_comp,
    Polynomial.taylor_eval, add_comm]

theorem evalAt_C_mul (p : Polynomial ℂ) (G : BiPoly) (s w : ℂ) :
    evalAt (C p * G) s w = p.eval s * evalAt G s w := by
  simp [evalAt, specialize]

/-- A formal algebraic root with nonzero formal derivative gives an analytic root.
The derivative may vanish at the origin; finite-jet division removes that singularity. -/
theorem exists_analytic_root (P : BiPoly) (y : Series)
    (hy : (formalize P).eval y = 0)
    (hd : (formalize P).derivative.eval y ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0 = PowerSeries.constantCoeff y ∧
      ∀ᶠ s in 𝓝 0, evalAt P s (f s) = 0 := by
  obtain ⟨m, k, p, G, z, hm, hyz, hG, hz, h1, hhigh⟩ := exists_scaled_factor P y hy hd
  obtain ⟨g, hg, hg0, hgroot⟩ := exists_analytic_root_of_linear_specialization G z hz h1 hhigh
  refine ⟨fun s => p.eval s + s ^ m * g s, ?_, ?_, ?_⟩
  · exact ((AnalyticOnNhd.eval_polynomial p 0 (Set.mem_univ _))).add
      ((analyticAt_id.pow m).mul hg)
  · rw [hyz]
    simp [map_add, map_mul, map_pow, ne_of_gt hm, Polynomial.constantCoeff_coe,
      Polynomial.coeff_zero_eq_eval_zero]
  · filter_upwards [hgroot] with s hs
    rw [← evalAt_scaledTaylor, hG, evalAt_C_mul, hs, mul_zero]

end

end GaloisForLFunctions.HTGeometry.AlgebraicFiniteJetBranch
