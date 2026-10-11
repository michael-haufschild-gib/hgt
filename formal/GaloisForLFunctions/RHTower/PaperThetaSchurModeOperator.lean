import GaloisForLFunctions.RHTower.PaperThetaSchurModeCharge
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin

/-!
# The full theta-stage quartic mode operator

Every mode at every actual corrected theta stage is retained. A fixed source bound gives a
bounded diagonal operator. Finite initial stage sets contain only finitely many modes, while
vectors whose stage tends to infinity escape weakly.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Classical
open scoped Topology NNReal ENNReal

abbrev PaperThetaSchurSpace := lp (fun _ : PaperThetaSchurMode => ℂ) 2

/-- All modes of all stages strictly below a finite cutoff. -/
def paperThetaSchurEarlyModes (N : ℕ) : Finset PaperThetaSchurMode :=
  (Finset.range N).sigma (fun _ => Finset.univ)

@[simp] theorem mem_paperThetaSchurEarlyModes (N : ℕ) (p : PaperThetaSchurMode) :
    p ∈ paperThetaSchurEarlyModes N ↔ p.1 < N := by
  simp [paperThetaSchurEarlyModes]

theorem paperThetaSchur_stage_tendsto :
    Tendsto (fun p : PaperThetaSchurMode => p.1) cofinite atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [(paperThetaSchurEarlyModes N).finite_toSet.compl_mem_cofinite] with p hp
  simpa using hp

theorem norm_paperThetaSchurModeCharge_complex_le (S : PaperThetaSchurFamily)
    (p : PaperThetaSchurMode) :
    ‖(paperThetaSchurModeCharge S p : ℂ)‖ ≤ paperThetaSchurChargeBound := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperThetaSchurModeCharge_nonneg S p)] using
    paperThetaSchurModeCharge_le_bound S p

/-- Literal positive quartic charge on the full mode Hilbert space. -/
def paperThetaSchurModeOperator (S : PaperThetaSchurFamily) :
    PaperThetaSchurSpace →L[ℂ] PaperThetaSchurSpace :=
  _root_.GaloisForLFunctions.lpDiagonalCLM (fun p => (paperThetaSchurModeCharge S p : ℂ))
    paperThetaSchurChargeBound_pos.le (norm_paperThetaSchurModeCharge_complex_le S)

@[simp] theorem paperThetaSchurModeOperator_apply (S : PaperThetaSchurFamily)
    (f : PaperThetaSchurSpace) (p : PaperThetaSchurMode) :
    paperThetaSchurModeOperator S f p = (paperThetaSchurModeCharge S p : ℂ) * f p := rfl

theorem norm_paperThetaSchurModeOperator_le (S : PaperThetaSchurFamily) :
    ‖paperThetaSchurModeOperator S‖ ≤ paperThetaSchurChargeBound :=
  _root_.GaloisForLFunctions.norm_lpDiagonalCLM_le _ _ _

theorem paperThetaSchurModeOperator_basis (S : PaperThetaSchurFamily)
    (p : PaperThetaSchurMode) :
    paperThetaSchurModeOperator S (HilbertSchmidt.lpBasis PaperThetaSchurMode p) =
      (paperThetaSchurModeCharge S p : ℂ) • HilbertSchmidt.lpBasis PaperThetaSchurMode p := by
  rw [HilbertSchmidt.lpBasis_apply]
  change _root_.GaloisForLFunctions.lpDiagonalCLM _ _ _ (lp.single 2 p (1 : ℂ)) = _
  rw [_root_.GaloisForLFunctions.lpDiagonalCLM_single]
  ext q
  simp only [lp.single_apply, Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs with hq
  · subst hq
    simp
  · simp

/-- Any sequence of modes escaping in stage is weakly null. -/
theorem paperThetaSchur_basis_weaklyNull (j : ℕ → PaperThetaSchurMode)
    (hj : Tendsto (fun n => (j n).1) atTop atTop) (z : PaperThetaSchurSpace) :
    Tendsto (fun n => inner ℂ z (HilbertSchmidt.lpBasis PaperThetaSchurMode (j n)))
      atTop (𝓝 0) := by
  apply tendsto_inner_lp_of_coord (fun n => HilbertSchmidt.lpBasis PaperThetaSchurMode (j n))
    zero_le_one
  · intro n
    exact ((HilbertSchmidt.lpBasis PaperThetaSchurMode).orthonormal.1 (j n)).le
  · intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [hj.eventually (eventually_ge_atTop (p.1 + 1))] with n hn
    have hne : j n ≠ p := by
      intro he
      rw [he] at hn
      omega
    simp [HilbertSchmidt.lpBasis_apply, lp.single_apply, Ne.symm hne]

end
end RHTower.HedenmalmThetaSource
