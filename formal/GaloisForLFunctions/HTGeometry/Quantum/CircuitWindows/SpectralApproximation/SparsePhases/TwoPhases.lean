import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.SparsePhases.AngularFloor
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget

/-! # Exact spectator error for a phase on a small spectral subspace -/

open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.SparsePhases
noncomputable section

private abbrev Conf (N : ℕ) := Fin N → Bool
private abbrev Reg (N : ℕ) := Matrix (Conf N) (Conf N) ℂ
/-- Unit complex phase at angle a in radians. -/
def phase (a : ℝ) := Complex.exp ((a:ℂ)*Complex.I)

/-- Phase of angle 2a on marked columns of the chosen basis, identity
on its other columns. -/
def twoPhase {N : ℕ} (V : unitaryGroup (Conf N) ℂ) (A : Finset (Conf N)) (a : ℝ) : Reg N :=
  V.val * diagonal (fun i => if i ∈ A then phase (2*a) else 1) * star V.val

private theorem scalar_distance {N : ℕ} (V : unitaryGroup (Conf N) ℂ) (f : Conf N → ℂ) (w : ℂ) :
    ‖V.val*diagonal f*star V.val-w • (1 : Reg N)‖ = ‖fun i => f i-w‖ := by
  have hs : V.val*diagonal (fun _ : Conf N => w)*star V.val = w • (1 : Reg N) := by
    rw [←smul_one_eq_diagonal_const,Matrix.mul_smul,mul_one,Matrix.smul_mul,V.property.2]
  rw [←hs,←sub_mul,←mul_sub,l2_opNorm_unitary_conj_eq V.property,Matrix.diagonal_sub,l2_opNorm_diagonal]
  rfl

/-- If the marked dimension is smaller than one spectator multiplicity,
no supported unitary beats the scalar at the angular midpoint. Both
the projector basis and the supported fitting unitary are arbitrary. -/
theorem two_phase_optimum {N : ℕ} (V : unitaryGroup (Conf N) ℂ) (A : Finset (Conf N))
    (hA : A.Nonempty) (a : ℝ) (ha : 0 ≤ a) (hπ : a ≤ π/2) :
    ‖twoPhase V A a-phase a • (1 : Reg N)‖ = 2*sin (a/2) ∧
      ∀ (S : Finset (Fin N)) (B : unitaryGroup (Conf N) ℂ),
        A.card < 2^(N-S.card) → IsSiteSupported S B.val →
          2*sin (a/2) ≤ ‖twoPhase V A a-B.val‖ := by
  classical
  let f (i : Conf N) : ℂ := if i ∈ A then phase (2*a) else 1
  have hsin := sin_nonneg_of_nonneg_of_le_pi ha (by linarith only [hπ,pi_pos])
  have hhalf := sin_nonneg_of_nonneg_of_le_pi (half_nonneg ha) (by linarith only [hπ,pi_pos] : a/2 ≤ π)
  have hmid (i : Conf N) : ‖f i-phase a‖=2*sin (a/2) := by
    by_cases hi : i ∈ A
    · rw [f,if_pos hi,phase,phase,norm_expI_sub_expI,show 2*a-a=a by ring,abs_of_nonneg hhalf]
    · rw [f,if_neg hi,norm_sub_rev,phase,norm_expI_sub_one,abs_of_nonneg hhalf]
  obtain ⟨i,hi⟩ := hA
  constructor
  · change ‖V.val*diagonal f*star V.val-_‖=_
    rw [scalar_distance]
    exact le_antisymm ((pi_norm_le_iff_of_nonneg (mul_nonneg zero_le_two hhalf)).mpr
      fun j => (hmid j).le) ((hmid i).symm.le.trans (norm_le_pi_norm (fun j => f j-phase a) i))
  intro S B hcard hB
  have hdf : diagonal f ∈ unitaryGroup (Conf N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
    congr 1
    funext j
    change f j*star (f j)=1
    have hn : ‖f j‖=1 := by by_cases h : j ∈ A <;> simp [f,h,phase,Complex.norm_exp_ofReal_mul_I]
    simp [Complex.star_def,Complex.mul_conj',hn]
  have hu : twoPhase V A a ∈ unitary (Reg N) :=
    mul_mem (mul_mem V.property hdf) (Unitary.star_mem V.property)
  have he : 1-twoPhase V A a = V.val*(1-diagonal f)*star V.val := by
    rw [mul_sub,sub_mul,mul_one,V.property.2]; rfl
  have hr : (1-twoPhase V A a).rank ≤ A.card := by
    rw [he]
    apply (Matrix.rank_mul_le_left ..).trans ((Matrix.rank_mul_le_right ..).trans ?_)
    rw [←Matrix.diagonal_one,Matrix.diagonal_sub,Matrix.rank_diagonal,Fintype.card_subtype]
    apply Finset.card_le_card
    intro j hj
    by_contra h
    exact (Finset.mem_filter.mp hj).2 (by simp [f,h])
  have hdist := norm_le_pi_norm (fun j => f j-(1:ℂ)) i
  have hchord : ‖f i-(1:ℂ)‖=2*sin a := by
    rw [f,if_pos hi,phase,norm_expI_sub_one,show 2*a/2=a by ring,abs_of_nonneg hsin]
  have hh := scalar_distance V f 1
  rw [one_smul] at hh
  apply half_angle_floor hu B.property hB (hr.trans_lt hcard) ha hπ
  exact hchord.symm.le.trans (hdist.trans_eq hh.symm)

#print axioms two_phase_optimum
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.SparsePhases
