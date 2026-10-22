import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllOrderGaussianLimit
import GaloisForLFunctions.HTGeometry.PoleUnitGammaBase
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Complete native positivity on a cofinal ray at every finite rank

All Gaussian-balanced native moments converge at each fixed order. Their
shifted limiting matrices are strictly positive Gamma moment matrices.
Consequently each finite native shifted Hankel matrix is positive definite
past a rank-dependent radius. No compact-center or integrated sign follows.
-/

open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
namespace RHTower.ThetaCuspGaussianLimit
noncomputable section

private theorem profile_jet_step (n : ℕ) :
    iteratedDeriv (n+2) profile 0 =
      -8*((n : ℝ)+1)*iteratedDeriv n profile 0 := by
  have hd : deriv profile = fun t => -8*(t*profile t) := by
    funext t
    have h : HasDerivAt profile (Real.exp (-4*t^(2 : ℕ))*(-8*t)) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul (-4)).exp using 1
      · funext y
        rfl
      · norm_num
        ring
    exact h.deriv.trans (by unfold profile; ring)
  have hc : ContDiff ℝ (n+1 : ℕ) profile := by unfold profile; fun_prop
  rw [show n+2=(n+1)+1 by omega, iteratedDeriv_succ', hd,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul
      (show ContDiffAt ℝ (n+1 : ℕ) (fun t : ℝ => t) 0 by fun_prop) hc.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq', Finset.mem_range, Nat.choose_one_right]
  ring

def gaussianMoment (k : ℕ) : ℝ :=
  16^k*GaloisForLFunctions.HTGeometry.gammaShapeMoment (1/2) k

private theorem gaussianMoment_step (k : ℕ) :
    gaussianMoment (k+1) = 8*(2*(k : ℝ)+1)*gaussianMoment k := by
  rw [gaussianMoment, pow_succ, GaloisForLFunctions.HTGeometry.gammaShapeMoment_succ]
  unfold gaussianMoment
  ring

/-- The exact signed Gaussian jets are positive Gamma moments at every order. -/
theorem profile_signed_even_jet (k : ℕ) :
    (-1 : ℝ)^k*iteratedDeriv (2*k) profile 0 = gaussianMoment k := by
  induction k with
  | zero => simp [profile, gaussianMoment]
  | succ k ih =>
    rw [Nat.mul_succ, profile_jet_step, pow_succ, gaussianMoment_step]
    push_cast
    calc
      _ = 8*(2*(k : ℝ)+1)*((-1 : ℝ)^k*iteratedDeriv (2*k) profile 0) := by ring
      _ = _ := by rw [ih]

private theorem gaussianMoment_pos (k : ℕ) : 0 < gaussianMoment k := by
  induction k with
  | zero => norm_num [gaussianMoment]
  | succ k ih => rw [gaussianMoment_step]; positivity

private theorem gaussianMoment_add (s n : ℕ) :
    gaussianMoment (s+n) = gaussianMoment s*16^n*gammaShapeMoment ((s : ℝ)+1/2) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show s+(n+1)=(s+n)+1 by omega, gaussianMoment_step, ih,
      pow_succ, gammaShapeMoment_succ]
    push_cast
    ring

private theorem gaussian_matrix_posDef (N s : ℕ) :
    Matrix.PosDef (fun i j : Fin N => gaussianMoment (i.val+j.val+s)) := by
  let A := _root_.HTGeometry.momentHankelMatrix (gammaShapeMoment ((s : ℝ)+1/2)) N
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => (16 : ℝ)^i.val)
  have hA : A.PosDef := gammaShapeMoment_momentHankelMatrix_posDef (by positivity) N
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (16 : ℝ) ≠ 0)) hi
  have he : (fun i j : Fin N => gaussianMoment (i.val+j.val+s)) =
      gaussianMoment s • (Dᴴ*A*D) := by
    ext i j
    rw [show i.val+j.val+s=s+(i.val+j.val) by omega, gaussianMoment_add]
    simp only [D, A, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, _root_.HTGeometry.momentHankelMatrix, pow_add]
    ring
  rw [he]
  exact (hA.conjTranspose_mul_mul_same hD).smul (gaussianMoment_pos s)

/-- Native Fourier-signed even jets at an arbitrary shifted finite rank. -/
def nativeShiftedMatrix (N s : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val+s)*thetaCuspNativeReflectionJet (2*(i.val+j.val+s)) x

private def balancedMatrix (N s : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val+s) x

private theorem balancedMatrix_posDef_eventually (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, (balancedMatrix N s x).PosDef := by
  have hh (x : ℝ) : (balancedMatrix N s x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [balancedMatrix, add_comm]
  apply posDef_eventually_of_tendsto (gaussian_matrix_posDef N s)
    (Filter.Eventually.of_forall hh)
  intro i j
  simpa only [balancedMatrix, profile_signed_even_jet] using
    native_scaled_jet_tendsto (i.val+j.val+s)

/-- Every finite shifted native Hankel matrix of the complete source is positive
on a cofinal ray. The threshold is allowed to depend on both rank and shift. -/
theorem nativeShiftedMatrix_posDef_eventually (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, (nativeShiftedMatrix N s x).PosDef := by
  filter_upwards [balancedMatrix_posDef_eventually N s, eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f*q^i.val)
  have hqp : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hq := hqp.ne'
  have hf : f ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : nativeShiftedMatrix N s x = q^s • (Dᴴ*balancedMatrix N s x*D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, nativeShiftedMatrix, balancedMatrix,
      thetaCuspNativeScaledEvenJet]
    change _ = q^s*(f*q^i.val * (_/(f^(2 : ℕ)*q^(i.val+j.val+s))) * (f*q^j.val))
    rw [pow_add, pow_add]
    field_simp [hf, hq]
    ring
  rw [he]
  exact (hx.conjTranspose_mul_mul_same hD).smul (pow_pos hqp s)

end
end RHTower.ThetaCuspGaussianLimit
