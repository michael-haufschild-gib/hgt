import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.ResidueTargetProjection
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheAverageRowIsBlindToTheTarget

/-!
# Recovering the reciprocal target without the completion denominator

Subtract the known geometric term from each local Poisson row and multiply
by `1 - R`. Nonprincipal projection then recovers the signed reciprocal Euler
coefficient `-ηX`. This identity matches the literal local coefficient series
on its convergence domain. Perturbations of the original rows cost at most
`‖1 - R‖` times their mean absolute error.
-/

noncomputable section
open Complex NumberField IsDedekindDomain Finset
open scoped Classical

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

variable (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)

/-- The completed row after removing its known geometric term and denominator. -/
def rowTargetPolynomial (Q R ηp X Y V ρ : ℂ) : ℂ :=
  (1 - R * Q⁻¹ - ηp * (Q - 1) * X * Y * V) * (1 - V)⁻¹ +
    (R * Y) * ρ - (ηp * X) * ρ⁻¹

/-- Exact matching with the original Poisson row wherever its completion denominator is nonzero. -/
theorem rowLocalSum_remove_completion (Q R ηp X Y V ρ : ℂ) (hR : 1 - R ≠ 0) :
    (1 - R) * (rowLocalSum Q R ηp X Y V ρ - ρ * Y * (1 - ρ * Y)⁻¹) =
      rowTargetPolynomial Q R ηp X Y V ρ := by
  unfold rowLocalSum rowTargetPolynomial
  calc
    _ = (1 - R) * (1 - V)⁻¹ + ((1 - R) * (1 - R)⁻¹) *
        (R * (1 - Q⁻¹) * (1 - V)⁻¹ + ρ * Y * R - ηp * ρ⁻¹ * X -
          ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hR, one_mul]; ring

/-- The target is recovered for every value of the completion parameter in the polynomial row. -/
theorem residueTargetProjection_rowTargetPolynomial (Q R ηp X Y V : ℂ) :
    residueTargetProjection P hg (fun a =>
      rowTargetPolynomial Q R ηp X Y V (complexSexticChar P hg a)) = -(ηp * X) :=
  residueTargetProjection_three_modes P hg _ _ _

/-- Projection of the corrected actual local row recovers the reciprocal Euler coefficient. -/
theorem residueTargetProjection_rowLocalSum (Q R ηp X Y V : ℂ) (hR : 1 - R ≠ 0) :
    residueTargetProjection P hg (fun a =>
      (1 - R) * (rowLocalSum Q R ηp X Y V (complexSexticChar P hg a) -
        complexSexticChar P hg a * Y * (1 - complexSexticChar P hg a * Y)⁻¹)) = -(ηp * X) := by
  simp_rw [rowLocalSum_remove_completion Q R ηp X Y V _ hR]
  exact residueTargetProjection_rowTargetPolynomial P hg Q R ηp X Y V

/-- The extracted arithmetic coefficient has its exact prime-norm decay, uniformly in completion. -/
theorem norm_residueTargetProjection_primeWeight (Q : ℝ) (hQ : 0 < Q)
    (R ηp x Y V : ℂ) :
    ‖residueTargetProjection P hg (fun a =>
      rowTargetPolynomial Q R ηp ((Q : ℂ) ^ (-x)) Y V (complexSexticChar P hg a))‖ =
        ‖ηp‖ * Q ^ (-x.re) := by
  rw [residueTargetProjection_rowTargetPolynomial, norm_neg, norm_mul, norm_cpow_neg_eq hQ]

/-- Error control in the original row values has factor `‖1 - R‖`, with no pole as `R → 1`. -/
theorem norm_rowLocalSum_target_error_le (Q R ηp X Y V : ℂ) (hR : 1 - R ≠ 0)
    (f : O ⧸ P → ℂ) :
    ‖residueTargetProjection P hg (fun a =>
        (1 - R) * (f a - complexSexticChar P hg a * Y *
          (1 - complexSexticChar P hg a * Y)⁻¹)) + ηp * X‖ ≤
      ‖1 - R‖ * residueRowMeanNorm P (fun a =>
        f a - rowLocalSum Q R ηp X Y V (complexSexticChar P hg a)) := by
  have ht := residueTargetProjection_rowLocalSum P hg Q R ηp X Y V hR
  have he :
      residueTargetProjection P hg (fun a =>
        (1 - R) * (f a - complexSexticChar P hg a * Y *
          (1 - complexSexticChar P hg a * Y)⁻¹)) + ηp * X =
      residueTargetProjection P hg (fun a => (1 - R) *
        (f a - rowLocalSum Q R ηp X Y V (complexSexticChar P hg a))) := by
    conv_lhs => rw [← neg_neg (ηp * X), ← ht, ← sub_eq_add_neg]
    rw [← residueTargetProjection_sub]
    congr 1
    funext a
    ring
  rw [he]
  exact norm_residueTargetProjection_mul_le P hg (1 - R) _

/-- The same extraction applies to the literal local coefficient series on its convergence domain.
The zero residue is annihilated by the character, so no value of that row is assumed. -/
theorem residueTargetProjection_localTerm (π : O) [NeZero π]
    [(Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
    (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)
    (ηp X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π ηp X V‖ < 1) :
    residueTargetProjection (Ideal.span {π}) hlam (fun a =>
      (1 - primeR π ηp X V) *
        ((∑' v, localTerm π ηp X Y V a.out 0 v) -
          complexSexticChar (Ideal.span {π}) hlam a * Y *
            (1 - complexSexticChar (Ideal.span {π}) hlam a * Y)⁻¹)) = -(ηp * X) := by
  have hR0 : 1 - primeR π ηp X V ≠ 0 := by
    intro h
    have he : primeR π ηp X V = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hR
    exact (lt_irrefl 1) hR
  calc
    _ = residueTargetProjection (Ideal.span {π}) hlam (fun a =>
        (1 - primeR π ηp X V) *
          (rowLocalSum (primeQ π) (primeR π ηp X V) ηp X Y V
              (complexSexticChar (Ideal.span {π}) hlam a) -
            complexSexticChar (Ideal.span {π}) hlam a * Y *
              (1 - complexSexticChar (Ideal.span {π}) hlam a * Y)⁻¹)) := by
      unfold residueTargetProjection
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp only [ha, MulChar.map_zero, zero_mul]
      · have hu : a.out ∉ Ideal.span {π} := by
          intro h
          have he : Ideal.Quotient.mk (Ideal.span {π}) a.out = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr h
          rw [Ideal.Quotient.mk_out] at he
          exact ha he
        have hW :
            ‖complexSexticChar (Ideal.span {π}) hlam
              (Ideal.Quotient.mk _ a.out) * Y‖ < 1 := by
          rw [Ideal.Quotient.mk_out, norm_mul, norm_sexticChar_eq_indicator, if_neg ha, one_mul]
          exact hY
        have hs := hasSum_localTerm_rowLocalSum π hlam h2 hprim ηp X Y V hu hV hW hR
        dsimp only
        rw [hs.tsum_eq, Ideal.Quotient.mk_out]
    _ = -(ηp * X) := residueTargetProjection_rowLocalSum
      (Ideal.span {π}) hlam (primeQ π) (primeR π ηp X V) ηp X Y V hR0


end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
