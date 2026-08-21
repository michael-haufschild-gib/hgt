import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UrysohnsLemma

/-!
# Intertwiners of self-adjoint elements with disjoint spectra vanish

If `S X = X T` with `S`, `T` self-adjoint in a unital C\*-algebra, then `X` intertwines the whole
continuous functional calculus: `f(S) X = X f(T)` for every continuous real `f`.  The proof is the
classical one — polynomials first, then Weierstrass approximation on an interval containing both
spectra, using that the calculus is norm-controlled by the sup norm on the spectrum.

Consequently, if the two spectra are **disjoint**, Urysohn's lemma supplies a continuous `f` equal
to `1` on `σ(S)` and `0` on `σ(T)`, so `X = 1 · X = f(S) X = X f(T) = X · 0 = 0`.

This is the self-adjoint case of Rosenblum's theorem on the Sylvester equation, and it is what
turns "the relative-resolvent corner vanishes" into "the crossing operator is zero".
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
/-- Powers of an intertwined pair stay intertwined. -/
theorem pow_mul_eq_mul_pow_of_intertwine {S T X : A} (h : S * X = X * T) (n : ℕ) :
    S ^ n * X = X * T ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

omit [Nontrivial A] in
/-- Polynomials of an intertwined pair stay intertwined. -/
theorem aeval_mul_eq_mul_aeval_of_intertwine {S T X : A} (h : S * X = X * T) (q : ℝ[X]) :
    (aeval S q) * X = X * (aeval T q) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [map_add, add_mul, mul_add, hp, hr]
  | monomial n c =>
      rw [aeval_monomial, aeval_monomial, mul_assoc, pow_mul_eq_mul_pow_of_intertwine h,
        ← mul_assoc, Algebra.commutes, mul_assoc]

/-- The spectrum of a self-adjoint element sits inside a symmetric interval of radius its norm. -/
theorem spectrum_subset_Icc (S : A) :
    spectrum ℝ S ⊆ Set.Icc (-‖S‖) ‖S‖ := by
  intro x hx
  have hle : ‖x‖ ≤ ‖S‖ := spectrum.norm_le_norm_of_mem hx
  rw [Real.norm_eq_abs, abs_le] at hle
  exact ⟨hle.1, hle.2⟩

/-- **The continuous functional calculus of an intertwined self-adjoint pair is intertwined.** -/
theorem cfc_mul_eq_mul_cfc_of_intertwine {S T X : A} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (h : S * X = X * T) {f : ℝ → ℝ} (hf : Continuous f) :
    cfc f S * X = X * cfc f T := by
  classical
  set M : ℝ := max ‖S‖ ‖T‖ with hM
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg S) (le_max_left _ _)
  have hSsub : spectrum ℝ S ⊆ Set.Icc (-M) M := by
    refine (spectrum_subset_Icc S).trans (Set.Icc_subset_Icc ?_ ?_)
    · exact neg_le_neg (le_max_left _ _)
    · exact le_max_left _ _
  have hTsub : spectrum ℝ T ⊆ Set.Icc (-M) M := by
    refine (spectrum_subset_Icc T).trans (Set.Icc_subset_Icc ?_ ?_)
    · exact neg_le_neg (le_max_right _ _)
    · exact le_max_right _ _
  have key : ∀ ε : ℝ, 0 < ε → ‖cfc f S * X - X * cfc f T‖ ≤ 2 * ε * ‖X‖ := by
    intro ε hε
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-M) M f
      (hf.continuousOn) ε hε
    have hqS : ‖cfc f S - aeval S q‖ ≤ ε := by
      rw [← cfc_polynomial (R := ℝ) q S, ← cfc_sub (R := ℝ) f (fun x => q.eval x) S]
      refine norm_cfc_le hε.le fun x hx => ?_
      have := hq x (hSsub hx)
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact this.le
    have hqT : ‖aeval T q - cfc f T‖ ≤ ε := by
      rw [← cfc_polynomial (R := ℝ) q T, ← cfc_sub (R := ℝ) (fun x => q.eval x) f T]
      refine norm_cfc_le hε.le fun x hx => ?_
      have := hq x (hTsub hx)
      rw [Real.norm_eq_abs]
      exact this.le
    have hmid : aeval S q * X = X * aeval T q :=
      aeval_mul_eq_mul_aeval_of_intertwine h q
    have hsplit : cfc f S * X - X * cfc f T
        = (cfc f S - aeval S q) * X + X * (aeval T q - cfc f T) := by
      rw [sub_mul, mul_sub, hmid]
      abel
    calc ‖cfc f S * X - X * cfc f T‖
        = ‖(cfc f S - aeval S q) * X + X * (aeval T q - cfc f T)‖ := by rw [hsplit]
      _ ≤ ‖(cfc f S - aeval S q) * X‖ + ‖X * (aeval T q - cfc f T)‖ := norm_add_le _ _
      _ ≤ ‖cfc f S - aeval S q‖ * ‖X‖ + ‖X‖ * ‖aeval T q - cfc f T‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ε * ‖X‖ + ‖X‖ * ε :=
          add_le_add (mul_le_mul_of_nonneg_right hqS (norm_nonneg X))
            (mul_le_mul_of_nonneg_left hqT (norm_nonneg X))
      _ = 2 * ε * ‖X‖ := by ring
  have hzero : cfc f S * X - X * cfc f T = 0 := by
    by_contra hne
    have hpos : 0 < ‖cfc f S * X - X * cfc f T‖ := norm_pos_iff.2 hne
    rcases eq_or_lt_of_le (norm_nonneg X) with hX0 | hX
    · have hXz : X = 0 := norm_eq_zero.1 hX0.symm
      rw [hXz, mul_zero, zero_mul, sub_zero] at hpos
      simp at hpos
    · have hε : 0 < ‖cfc f S * X - X * cfc f T‖ / (4 * ‖X‖) := by positivity
      have hk := key _ hε
      have hrw : 2 * (‖cfc f S * X - X * cfc f T‖ / (4 * ‖X‖)) * ‖X‖
          = ‖cfc f S * X - X * cfc f T‖ / 2 := by
        field_simp
        ring
      rw [hrw] at hk
      linarith
  exact sub_eq_zero.mp hzero

/-- **Disjoint self-adjoint spectra force the intertwiner to vanish.** -/
theorem eq_zero_of_intertwine_of_disjoint_spectrum {S T X : A}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (h : S * X = X * T)
    (hdisj : Disjoint (spectrum ℝ S) (spectrum ℝ T)) : X = 0 := by
  classical
  obtain ⟨g, hgT, hgS, _⟩ := exists_continuous_zero_one_of_isClosed
    (spectrum.isClosed T) (spectrum.isClosed S) hdisj.symm
  have hcont : Continuous (g : ℝ → ℝ) := g.continuous
  have hmain := cfc_mul_eq_mul_cfc_of_intertwine hS hT h hcont
  have hS1 : cfc (g : ℝ → ℝ) S = 1 := by
    rw [cfc_congr (f := (g : ℝ → ℝ)) (g := fun _ => (1 : ℝ)) (a := S) fun x hx => hgS hx]
    exact cfc_const_one ℝ S
  have hT0 : cfc (g : ℝ → ℝ) T = 0 := by
    rw [cfc_congr (f := (g : ℝ → ℝ)) (g := fun _ => (0 : ℝ)) (a := T) fun x hx => hgT hx]
    exact cfc_const_zero ℝ T
  rw [hS1, hT0, one_mul, mul_zero] at hmain
  exact hmain

end

end GaloisForLFunctions.HTGeometry
