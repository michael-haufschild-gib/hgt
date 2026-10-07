import GaloisForLFunctions.HTGeometry.SchottkyHalfPlaneGrowth
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Rational expressions on a half-plane

Schottky bounds control every reciprocal factor of an omitted polynomial.
A rational expression then has an exponential bound along a horizontal ray,
provided its nonconstant denominator and one further value are omitted.
-/

open Complex Polynomial

namespace GaloisForLFunctions.HTGeometry

private theorem exp_ray_bound_multiset_prod (R : ℝ) (s : Multiset ℂ) (F : ℂ → ℂ → ℂ)
    (hb : ∀ b ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖F b ((R + t : ℝ) : ℂ)‖ ≤ Real.exp (C * t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(s.map (fun b => F b ((R + t : ℝ) : ℂ))).prod‖ ≤ Real.exp (C * t) := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨1, by positivity, fun t ht => ?_⟩
    simpa using Real.one_le_exp (show 0 ≤ t by linarith)
  | @cons b s ih =>
    obtain ⟨A, hA, ha⟩ := hb b (by simp)
    obtain ⟨B, hB, hs⟩ := ih (fun c hc => hb c (by simp [hc]))
    refine ⟨A + B, by positivity, fun t ht => ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    calc
      _ ≤ Real.exp (A * t) * Real.exp (B * t) := by
        exact mul_le_mul (ha t ht) (hs t ht) (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((A + B) * t) := by rw [← Real.exp_add]; congr 1; ring

/-- Avoiding the roots of a polynomial and one further value bounds its reciprocal on a ray. -/
theorem exists_exp_ray_bound_polynomial_inv (R : ℝ) (q : Polynomial ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | R < z.re}) {b : ℂ} (hqb : q.eval b ≠ 0)
    (homit : ∀ z : ℂ, R < z.re → q.eval (f z) ≠ 0 ∧ f z ≠ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(q.eval (f ((R + t : ℝ) : ℂ)))⁻¹‖ ≤ Real.exp (C * t) := by
  classical
  have hq : q ≠ 0 := by intro he; simp [he] at hqb
  have hroot (c : ℂ) (hc : c ∈ q.roots) : q.eval c = 0 := (Polynomial.mem_roots hq).mp hc
  have hbnd (c : ℂ) (hc : c ∈ q.roots) :
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
        ‖(f ((R + t : ℝ) : ℂ) - c)⁻¹‖ ≤ Real.exp (C * t) := by
    have hbc : b - c ≠ 0 := by
      intro he
      exact hqb (by rw [sub_eq_zero.mp he, hroot c hc])
    have hfne : ∀ z : ℂ, R < z.re → f z - c ≠ 0 := by
      intro z hz he
      exact (homit z hz).1 (by rw [sub_eq_zero.mp he, hroot c hc])
    have hg : DifferentiableOn ℂ (fun z => (f z - c)⁻¹) {z : ℂ | R < z.re} :=
      (hf.sub_const c).inv hfne
    apply exists_exp_ray_bound_of_omitting_two_halfPlane R hg (inv_ne_zero hbc).symm
    intro z hz
    refine ⟨inv_ne_zero (hfne z hz), fun he => ?_⟩
    apply (homit z hz).2
    have he' := inv_inj.mp he
    linear_combination he'
  obtain ⟨A, hA, hb⟩ := exp_ray_bound_multiset_prod R q.roots
    (fun c z => (f z - c)⁻¹) hbnd
  have hshape (z : ℂ) : (q.eval (f z))⁻¹ =
      q.leadingCoeff⁻¹ * (q.roots.map (fun c => (f z - c)⁻¹)).prod := by
    conv_lhs => rw [(IsAlgClosed.splits q).eq_prod_roots]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X]
    rw [mul_inv, Multiset.prod_map_inv]
  let M := ‖q.leadingCoeff⁻¹‖ + 1
  refine ⟨M + A, by dsimp [M]; positivity, fun t ht => ?_⟩
  have hM : ‖q.leadingCoeff⁻¹‖ ≤ Real.exp (M * t) := by
    dsimp [M]
    nlinarith [Real.add_one_le_exp ((‖q.leadingCoeff⁻¹‖ + 1) * t), norm_nonneg (q.leadingCoeff⁻¹)]
  rw [hshape, norm_mul]
  calc
    _ ≤ Real.exp (M * t) * Real.exp (A * t) :=
      mul_le_mul hM (hb t ht) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((M + A) * t) := by rw [← Real.exp_add]; congr 1; ring

/-- A rational expression with a nonconstant omitted denominator has an exponential ray bound. -/
theorem exists_exp_ray_bound_rational (R : ℝ) (p q : Polynomial ℂ)
    (hqdeg : 0 < q.natDegree) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | R < z.re}) {b : ℂ} (hqb : q.eval b ≠ 0)
    (homit : ∀ z : ℂ, R < z.re → q.eval (f z) ≠ 0 ∧ f z ≠ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖p.eval (f ((R + t : ℝ) : ℂ)) / q.eval (f ((R + t : ℝ) : ℂ))‖ ≤
        Real.exp (C * t) := by
  have hq : q ≠ 0 := by intro he; simp [he] at hqdeg
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root q (by
    rw [Polynomial.degree_eq_natDegree hq]
    exact_mod_cast (Nat.ne_of_gt hqdeg))
  have hcb : c ≠ b := by intro he; exact hqb (he ▸ hc)
  have hfomit : ∀ z : ℂ, R < z.re → f z ≠ c ∧ f z ≠ b := by
    intro z hz
    exact ⟨fun he => (homit z hz).1 (by rw [he]; exact hc), (homit z hz).2⟩
  obtain ⟨A, hA, hp⟩ := exists_exp_ray_bound_polynomial R p
    (exists_exp_ray_bound_of_omitting_two_halfPlane R hf hcb hfomit)
  obtain ⟨B, hB, hq'⟩ := exists_exp_ray_bound_polynomial_inv R q hf hqb homit
  refine ⟨A + B, by positivity, fun t ht => ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ Real.exp (A * t) * Real.exp (B * t) :=
      mul_le_mul (hp t ht) (hq' t ht) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((A + B) * t) := by rw [← Real.exp_add]; congr 1; ring

end GaloisForLFunctions.HTGeometry
