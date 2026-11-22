import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # A phase on a spectral interval from a cyclic addition -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralSorting
noncomputable section

/-- Phase of the linear binary register readout, measured in radians. -/
def linearPhase {d : ℕ} (θ : ℝ) (x : Fin d) : ℂ :=
  Complex.exp (((θ*(x.val:ℝ)/d:ℝ):ℂ)*Complex.I)

private theorem linearPhase_wrap {d : ℕ} (θ : ℝ) (b x : Fin d) :
    linearPhase θ (x+b)*star (linearPhase θ x) =
      linearPhase θ b*(if d ≤ x.val+b.val then Complex.exp (-(θ:ℂ)*Complex.I) else 1) := by
  have hd : (d:ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (fun h => by have := x.isLt; omega)).ne'
  have he (j : Fin d) : star (linearPhase θ j)=Complex.exp (-((θ:ℂ)*(j.val:ℂ)/d)*Complex.I) := by
    simp [linearPhase,Complex.star_def,←Complex.exp_conj]
    ring_nf
  rw [he]
  simp only [linearPhase,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast,Fin.val_add_eq_ite]
  split_ifs with h
  · rw [Nat.cast_sub h,Nat.cast_add,←Complex.exp_add,←Complex.exp_add]
    congr 1
    field_simp
    ring
  · rw [Nat.cast_add,mul_one,←Complex.exp_add]
    congr 1
    ring

/-- A cyclic relabeling of a diagonal matrix shifts its diagonal by the
same permutation. -/
theorem relabel_diagonal {I : Type*} [Fintype I] [DecidableEq I] (p : Equiv.Perm I) (f : I→ℂ) :
    p.permMatrix ℂ*diagonal f*star (p.permMatrix ℂ)=diagonal (f ∘ p) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext i
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix]
  simp only [←Matrix.mulVec_mulVec,Matrix.permMatrix_mulVec,Matrix.mulVec_diagonal,Function.comp_apply]
  simp

/-- Adding b modulo d, applying the linear phase, and undoing both
operations puts the same extra phase on precisely the final b labels. -/
theorem addition_phase_commutator {d : ℕ} [NeZero d] (b : Fin d) (θ : ℝ) :
    let S := (Equiv.addRight b).permMatrix ℂ
    let G := diagonal (linearPhase θ : Fin d→ℂ)
    S*G*star S*star G =
      linearPhase θ b • diagonal (fun x : Fin d =>
        if d ≤ x.val+b.val then Complex.exp (-(θ:ℂ)*Complex.I) else 1) := by
  intro S G
  rw [show S*G*star S=diagonal ((linearPhase θ) ∘ (Equiv.addRight b)) from relabel_diagonal ..]
  change diagonal _*(diagonal (linearPhase θ))ᴴ=_
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases h : x=y
  · subst y
    simpa only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,Function.comp_apply] using linearPhase_wrap θ b x
  · simp [Matrix.diagonal_apply_ne _ h]

#print axioms addition_phase_commutator
end
end GaloisForLFunctions.HTGeometry.SpectralSorting
