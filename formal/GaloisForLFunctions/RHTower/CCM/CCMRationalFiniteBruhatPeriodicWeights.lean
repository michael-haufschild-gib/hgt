import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleIntegerPeriod
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicBruhatSimpleTensorTraceClass
import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicWeightedPoisson

/-!
# Periodic residue weights from rational finite-adele Bruhat factors

After clearing one nonzero integer denominator, restriction of a finite-adele
Bruhat factor to the rational diagonal is a periodic integer sequence.  This
file proves that statement on the actual finite adele ring and factors every
such sequence through finitely many residue weights.

This closes the finite-place topological step left abstract in the periodic
weighted Poisson module.  No choice of prime enumeration and no numerical
calculation enters the proof.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct algebraMap

namespace GaloisForLFunctions
namespace RHTower

/-- The finite residue weight associated with a periodic integer sequence. -/
def ccmRationalPeriodicResidueWeight
    (M : ℕ) [NeZero M] (F : ℤ → ℂ) : Fin M → ℂ :=
  fun r => F (r : ℤ)

/-- A sequence of positive period `M` is exactly recovered from its finite
residue weight. -/
theorem ccmRationalPeriodic_eq_residueWeight
    (M : ℕ) [NeZero M] (F : ℤ → ℂ)
    (hF : Function.Periodic F (M : ℤ)) (n : ℤ) :
    F n = ccmRationalPeriodicResidueWeight M F
      (ccmRationalPeriodicResidue M n) := by
  let p : ℤ × Fin M := Int.divModEquiv M n
  have hn : n = p.1 * (M : ℤ) + (p.2 : ℤ) := by
    change n = (Int.divModEquiv M n).1 * (M : ℤ) +
      ((Int.divModEquiv M n).2 : ℤ)
    exact (Int.divModEquiv M).symm_apply_apply n |>.symm
  calc
    F n = F (p.2 : ℤ) := by
      rw [hn, add_comm]
      exact hF.int_mul p.1 (p.2 : ℤ)
    _ = ccmRationalPeriodicResidueWeight M F
        (ccmRationalPeriodicResidue M n) := rfl

/-- Right translation by a finite idele leaves a periodic sequence on the
diagonal integer lattice. -/
theorem ccmRationalFiniteBruhatMulRight_exists_positiveIntegerPeriod
    (f : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    ∃ M : ℕ, 0 < M ∧ Function.Periodic
      (fun n : ℤ =>
        f.1 (algebraMap ℤ CCMRationalFiniteAdele n * b)) (M : ℤ) := by
  obtain ⟨M, hM, hper⟩ :=
    ccmRationalFiniteBruhat_exists_positiveIntegerPeriod
      (ccmRationalFiniteBruhatMulRight f b)
  refine ⟨M, hM, fun n => ?_⟩
  have h := hper (algebraMap ℤ CCMRationalFiniteAdele n)
  simpa [ccmRationalFiniteBruhatMulRight_apply, map_add] using h

/-- After a prescribed nonzero denominator `d`, finite-adele Bruhat values on
`n / d` form a periodic integer sequence. -/
theorem ccmRationalFiniteBruhat_denominatorOrbit_exists_positiveIntegerPeriod
    (f : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) (d : ℤ) (hd : d ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ Function.Periodic
      (fun n : ℤ =>
        f.1 (algebraMap ℚ CCMRationalFiniteAdele
          ((n : ℚ) / (d : ℚ)) * b)) (M : ℤ) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  let uQ : ℚˣ := Units.mk0 ((d : ℚ)⁻¹) (inv_ne_zero hdQ)
  let bd : CCMRationalFiniteAdeleˣ :=
    FiniteAdeleRing.unitEmbedding ℤ ℚ uQ * b
  obtain ⟨M, hM, hper⟩ :=
    ccmRationalFiniteBruhat_exists_positiveIntegerPeriod
      (ccmRationalFiniteBruhatMulRight f bd)
  refine ⟨M, hM, fun n => ?_⟩
  have h := hper (algebraMap ℤ CCMRationalFiniteAdele n)
  have hscale (z : ℤ) :
      algebraMap ℤ CCMRationalFiniteAdele z *
          (bd : CCMRationalFiniteAdele) =
        algebraMap ℚ CCMRationalFiniteAdele
          ((z : ℚ) / (d : ℚ)) * b := by
    change algebraMap ℤ CCMRationalFiniteAdele z *
        (algebraMap ℚ CCMRationalFiniteAdele ((d : ℚ)⁻¹) * b) = _
    rw [show algebraMap ℤ CCMRationalFiniteAdele z =
        algebraMap ℚ CCMRationalFiniteAdele (z : ℚ) by simp]
    rw [← mul_assoc, ← map_mul]
    congr 2
  rw [ccmRationalFiniteBruhatMulRight_apply,
    ccmRationalFiniteBruhatMulRight_apply] at h
  have hadd :
      algebraMap ℤ CCMRationalFiniteAdele n +
          (M : CCMRationalFiniteAdele) =
        algebraMap ℤ CCMRationalFiniteAdele (n + (M : ℤ)) := by
    simp [map_add]
  rw [hadd, hscale, hscale] at h
  simpa using h

/-- Exact finite-residue factorization of every denominator-cleared rational
Bruhat orbit. -/
theorem ccmRationalFiniteBruhat_denominatorOrbit_exists_residueWeight
    (f : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) (d : ℤ) (hd : d ≠ 0) :
    ∃ (M : ℕ) (hM : NeZero M) (w : Fin M → ℂ),
      0 < M ∧ ∀ n : ℤ,
        f.1 (algebraMap ℚ CCMRationalFiniteAdele
          ((n : ℚ) / (d : ℚ)) * b) =
          w (@ccmRationalPeriodicResidue M hM n) := by
  obtain ⟨M, hM, hper⟩ :=
    ccmRationalFiniteBruhat_denominatorOrbit_exists_positiveIntegerPeriod
      f b d hd
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let F : ℤ → ℂ := fun n =>
    f.1 (algebraMap ℚ CCMRationalFiniteAdele
      ((n : ℚ) / (d : ℚ)) * b)
  let w : Fin M → ℂ := ccmRationalPeriodicResidueWeight M F
  refine ⟨M, inferInstance, w, hM, fun n => ?_⟩
  exact ccmRationalPeriodic_eq_residueWeight M F hper n

end RHTower
end GaloisForLFunctions
