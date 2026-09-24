import GaloisForLFunctions.RHTower.EulerDeletionLiteralResidueSourceBridge
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Exact Fourier energy of the centered Euler-deletion source

The factorial-period DFT has total normalized energy exactly equal to the
complete-period covariance of the literal centered residue source. This
identifies the energy to which the Farey large sieve can be applied.
-/

noncomputable section
open Finset

namespace RHTower.DeletionPeriodCovariance

private theorem sum_zmod_natCast_real {d : ℕ} [NeZero d] (f : ZMod d → ℝ) :
    (∑ r : ZMod d, f r) = ∑ r ∈ Finset.range d, f (r : ZMod d) := by
  have hfinEquiv (r : Fin d) : ZMod.finEquiv d r = (r.val : ZMod d) := by
    cases d with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ d =>
        apply ZMod.val_injective
        change r.val = r.val % (d + 1)
        rw [Nat.mod_eq_of_lt r.isLt]
  calc
    (∑ r : ZMod d, f r) = ∑ r : Fin d, f (ZMod.finEquiv d r) :=
      ((ZMod.finEquiv d).sum_comp f).symm
    _ = ∑ r : Fin d, f (r.val : ZMod d) := by simp_rw [hfinEquiv]
    _ = ∑ r ∈ Finset.range d, f (r : ZMod d) := by
      exact Fin.sum_univ_eq_sum_range (fun r : ℕ => f (r : ZMod d)) d

/-- Normalized DFT energy of the literal source on the factorial clock. -/
def centeredSourceFourierEnergy (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  letI : NeZero N.factorial := ⟨(Nat.factorial_pos N).ne'⟩
  ∑ k : ZMod N.factorial,
    Complex.normSq (((N.factorial : ℂ)⁻¹) *
      ZMod.dft (RHTower.Sieve.centeredSourcePeriod N.factorial N a) k)

/-- Parseval converts the exact period covariance into DFT coefficient energy. -/
theorem centeredSourceFourierEnergy_eq_periodCovariance
    (N : ℕ) (a : ℕ → ℝ) :
    centeredSourceFourierEnergy N a =
      periodCovariance (Finset.Icc 1 N) a := by
  let P := N.factorial
  let S := Finset.Icc 1 N
  letI : NeZero P := ⟨(Nat.factorial_pos N).ne'⟩
  have hsum :
      (∑ x : ZMod P,
        Complex.normSq (RHTower.Sieve.centeredSourcePeriod P N a x)) =
      ∑ r ∈ Finset.range P,
        (residueCombination S a r - periodMean S a) ^ (2 : ℕ) := by
    rw [sum_zmod_natCast_real]
    apply Finset.sum_congr rfl
    intro r hr
    change Complex.normSq
      (RHTower.Sieve.centeredSourcePeriod N.factorial N a (r : ZMod P)) = _
    rw [centeredSourcePeriod_apply_eq_complex_centered_residue]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
      Complex.normSq_ofReal]
    ring
  have hcov :
      (∑ r ∈ Finset.range P,
        (residueCombination S a r - periodMean S a) ^ (2 : ℕ)) =
        (P : ℝ) * periodCovariance S a := by
    exact sum_residueCombination_centered_sq a
      (fun m hm => (Finset.mem_Icc.mp hm).1)
      (fun m hm => Nat.dvd_factorial (Finset.mem_Icc.mp hm).1
        (Finset.mem_Icc.mp hm).2)
  unfold centeredSourceFourierEnergy
  rw [GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_normalized_parseval]
  rw [hsum, hcov]
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  field_simp
  rfl

end RHTower.DeletionPeriodCovariance
