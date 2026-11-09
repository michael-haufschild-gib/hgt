import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.BinomialMultipliers
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.DivisorTransitions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Positive polynomial multiples with negative-root correcting factors

A real polynomial positive on the nonnegative axis can be multiplied
into the coefficientwise positive cone using only factors `X+r`, `r>0`.
Real irreducible factorization reduces this to the quadratic binomial
repair law. The correcting polynomial cannot vanish in the closed right
half-plane, which preserves low-phase exponential modes under translation.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

/-- A correcting polynomial whose roots are strictly negative when every listed radius is positive. -/
def negativeRootMultiplier (L : List ℝ) : ℝ[X] :=
  (L.map fun r => X + C r).prod

theorem negativeRootMultiplier_nil : negativeRootMultiplier [] = 1 := rfl

theorem negativeRootMultiplier_append (L M : List ℝ) :
    negativeRootMultiplier (L ++ M) = negativeRootMultiplier L * negativeRootMultiplier M := by
  simp only [negativeRootMultiplier, List.map_append, List.prod_append]

theorem negativeRootMultiplier_replicate (n : ℕ) (r : ℝ) :
    negativeRootMultiplier (List.replicate n r) = (X + C r) ^ n := by
  simp only [negativeRootMultiplier, List.map_replicate, List.prod_replicate]

theorem negativeRootMultiplier_coeffNonneg {L : List ℝ} (hL : ∀ r ∈ L, 0 < r) :
    CoeffNonneg (negativeRootMultiplier L) := by
  induction L with
  | nil =>
    intro k
    rw [negativeRootMultiplier_nil, coeff_one]
    split_ifs <;> norm_num
  | cons r L ih =>
    have hr : 0 < r := hL r (by simp)
    have hf : CoeffNonneg (X + C r : ℝ[X]) := by
      intro k
      simp only [coeff_add, coeff_X, coeff_C]
      split_ifs <;> linarith only [hr]
    simpa only [negativeRootMultiplier, List.map_cons, List.prod_cons] using
      hf.mul (ih fun s hs => hL s (by simp [hs]))

/-- Correcting factors do not vanish in the closed right half-plane. -/
theorem negativeRootMultiplier_eval₂_ne_zero {L : List ℝ} (hL : ∀ r ∈ L, 0 < r)
    {z : ℂ} (hz : 0 ≤ z.re) :
    (negativeRootMultiplier L).eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  induction L with
  | nil => simp [negativeRootMultiplier]
  | cons r L ih =>
    simp only [negativeRootMultiplier, List.map_cons, List.prod_cons,
      eval₂_mul, eval₂_add, eval₂_X, eval₂_C]
    apply mul_ne_zero ?_ (ih fun s hs => hL s (by simp [hs]))
    intro he
    have hh := congrArg Complex.re he
    have hr := hL r (by simp)
    simp only [Complex.add_re, Complex.coe_algebraMap, Complex.ofReal_re, Complex.zero_re] at hh
    linarith only [hh, hr, hz]

private def conjugateQuadratic (a r : ℝ) : ℝ[X] :=
  X ^ 2 - C (2 * a) * X + C (r ^ 2)

private theorem conjugateQuadratic_monic (a r : ℝ) :
    (conjugateQuadratic a r).Monic := by
  have he : conjugateQuadratic a r = X ^ 2 + (C (r ^ 2) - C (2 * a) * X) := by
    unfold conjugateQuadratic
    ring
  rw [he]
  refine (monic_X_pow 2).add_of_left ?_
  rw [degree_X_pow]
  calc degree (C (r ^ 2) - C (2 * a) * X) ≤ 1 := by compute_degree
    _ < 2 := by norm_num

private theorem conjugateQuadratic_natDegree (a r : ℝ) :
    (conjugateQuadratic a r).natDegree = 2 := by
  unfold conjugateQuadratic
  compute_degree <;> norm_num

/-- A quadratic without a positive real root admits a multiplier with negative real roots. -/
private theorem exists_quadratic_negativeRoot_repair {a r : ℝ} (hr : 0 < r) (ha : a < r) :
    ∃ n : ℕ, CoeffNonneg (conjugateQuadratic a r * (X + C r) ^ n) := by
  let b : ℝ := a / r
  have hb : b < 1 := (div_lt_one hr).mpr ha
  -- The exact middle-coefficient criterion eventually holds for every ratio below one.
  obtain ⟨m, hm⟩ := exists_nat_gt (b / (1 - b))
  have hh := (div_lt_iff₀ (sub_pos.mpr hb)).mp hm
  have hc : CoeffNonneg (binomialRepair b (2 * m)) :=
    (coeffNonneg_binomialRepair_even_iff b m).mpr (by linarith only [hh])
  have hrb : r * b = a := by dsimp only [b]; exact mul_div_cancel₀ _ hr.ne'
  have hq : (conjugateQuadratic a r).comp (C r * X) =
      C (r ^ 2) * (X ^ 2 - C (2 * b) * X + 1) := by
    rw [← hrb]
    simp only [conjugateQuadratic, add_comp, sub_comp, pow_comp, mul_comp, C_comp, X_comp]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  have hl : (X + C r : ℝ[X]).comp (C r * X) = C r * (X + 1) := by
    simp only [add_comp, X_comp, C_comp]
    ring
  refine ⟨2 * m, (coeffNonneg_positive_rescale_iff _ hr).mp ?_⟩
  rw [mul_comp, pow_comp, hq, hl, mul_pow]
  have he : C (r ^ 2) * (X ^ 2 - C (2 * b) * X + 1) *
      (C r ^ (2 * m) * (X + 1) ^ (2 * m)) =
      C (r ^ (2 * m + 2)) * binomialRepair b (2 * m) := by
    simp only [binomialRepair, pow_add, map_mul, map_pow]
    ring
  rw [he]
  exact hc.C_mul (pow_pos hr _).le

private theorem monic_irreducible_positive_repair {p : ℝ[X]} (hm : p.Monic)
    (hi : Irreducible p) (hn : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0) :
    (∀ x : ℝ, 0 ≤ x → 0 < p.eval x) ∧
      ∃ L : List ℝ, (∀ r ∈ L, 0 < r) ∧ CoeffNonneg (p * negativeRootMultiplier L) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hi).ne'
  by_cases him : z.im = 0
  · have he : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [him])
    have hroot : p.IsRoot z.re := by
      rw [← he] at hz
      change aeval (algebraMap ℝ ℂ z.re) p = 0 at hz
      rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hz
      change ((p.eval z.re : ℝ) : ℂ) = 0 at hz
      exact Complex.ofReal_injective hz
    have hd : p.natDegree = 1 := by
      by_contra h
      exact hi.not_isRoot_of_natDegree_ne_one h hroot
    have hp : p = X - C z.re :=
      (eq_of_monic_of_dvd_of_natDegree_le (monic_X_sub_C z.re) hm
        (dvd_iff_isRoot.mpr hroot) (by rw [hd, natDegree_X_sub_C]))
    have hzneg : z.re < 0 := lt_of_not_ge fun h => hn z.re h hroot
    constructor
    · intro x hx
      rw [hp]
      simp only [eval_sub, eval_X, eval_C]
      linarith only [hx, hzneg]
    · refine ⟨[], by simp, ?_⟩
      rw [negativeRootMultiplier_nil, mul_one, hp]
      intro k
      simp only [coeff_sub, coeff_X, coeff_C]
      split_ifs <;> linarith only [hzneg]
  · have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq z).symm
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => him (by simp [h]))
    have ha : z.re < ‖z‖ := by
      by_contra h
      have hle : ‖z‖ ≤ z.re := le_of_not_gt h
      have hs := mul_self_le_mul_self (norm_nonneg z) hle
      nlinarith only [hs, hnorm, sq_pos_of_ne_zero him]
    have hp : p = conjugateQuadratic z.re ‖z‖ :=
      (eq_of_monic_of_dvd_of_natDegree_le (conjugateQuadratic_monic _ _) hm
        (p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him)
        (by rw [conjugateQuadratic_natDegree]; exact hi.natDegree_le_two))
    constructor
    · intro x _
      rw [hp]
      simp only [conjugateQuadratic, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
      nlinarith only [hnorm, sq_nonneg (x - z.re), sq_pos_of_ne_zero him]
    · obtain ⟨n, hn⟩ := exists_quadratic_negativeRoot_repair hr ha
      refine ⟨List.replicate n ‖z‖, ?_, ?_⟩
      · intro r hrm
        have he : r = ‖z‖ := (List.mem_replicate.mp hrm).2
        rwa [he]
      · rw [hp, negativeRootMultiplier_replicate]
        exact hn

/-- Every polynomial positive on the nonnegative axis has a coefficient-positive multiple
whose correcting factors all have strictly negative real roots. -/
theorem exists_negativeRootMultiplier_repair (p : ℝ[X])
    (hp : ∀ x : ℝ, 0 ≤ x → 0 < p.eval x) :
    ∃ L : List ℝ, (∀ r ∈ L, 0 < r) ∧ CoeffNonneg (p * negativeRootMultiplier L) := by
  classical
  generalize hd : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n = 0
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hd.trans hn)
      have hc : 0 < p.coeff 0 := by
        have hh := hp 0 le_rfl
        rwa [he, eval_C] at hh
      refine ⟨[], by simp, ?_⟩
      rw [negativeRootMultiplier_nil, mul_one, he]
      intro k
      simp only [coeff_C]
      split_ifs <;> positivity
    · have hpne : p ≠ 0 := fun h => by simpa [h] using hp 0 le_rfl
      have hdeg : 0 < p.natDegree := by omega
      obtain ⟨f, hfm, hfi, g, hfg⟩ :=
        exists_monic_irreducible_factor p (not_isUnit_of_natDegree_pos p hdeg)
      -- Each monic real irreducible factor stays positive on the nonnegative axis.
      have hfne : f ≠ 0 := hfi.ne_zero
      have hgne : g ≠ 0 := fun h => hpne (by rw [hfg, h, mul_zero])
      have hfn : ∀ x : ℝ, 0 ≤ x → f.eval x ≠ 0 := by
        intro x hx hf
        have hh := hp x hx
        rw [hfg, eval_mul, hf, zero_mul] at hh
        exact (lt_irrefl _ hh).elim
      obtain ⟨hfpos, L, hL, hLc⟩ := monic_irreducible_positive_repair hfm hfi hfn
      have hgpos : ∀ x : ℝ, 0 ≤ x → 0 < g.eval x := by
        intro x hx
        have hh := hp x hx
        rw [hfg, eval_mul] at hh
        exact (mul_pos_iff_of_pos_left (hfpos x hx)).mp hh
      have hgdeg : g.natDegree < n := by
        have hs : p.natDegree = f.natDegree + g.natDegree := by
          rw [hfg, natDegree_mul hfne hgne]
        have hfdeg := hfi.natDegree_pos
        omega
      obtain ⟨M, hM, hMc⟩ := ih g.natDegree hgdeg g hgpos rfl
      refine ⟨L ++ M, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hL r hr
        · exact hM r hr
      · have hh := hLc.mul hMc
        rw [hfg, negativeRootMultiplier_append]
        convert hh using 1
        ring

#print axioms exists_negativeRootMultiplier_repair
#print axioms negativeRootMultiplier_eval₂_ne_zero

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
