import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.OverlapPacking
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.TraceDecay
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # High spectral overlap in arbitrarily translated time intervals -/
open MeasureTheory Filter Set Matrix Finset GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

def orbitChoi (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) :=
  choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)

private theorem orbit_inner (ω : PathPauliDisorder) (n : ℕ) (a b : ℝ) :
    inner ℂ (orbitChoi ω n a) (orbitChoi ω n b)=amplitude ω n (b-a) := by
  let H : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  let U (t : ℝ) := unitaryEvolution H.val t
  have hU : U a*(U a)ᴴ=1 := (unitaryEvolution_mem_unitary H.property a).2
  have he : U b*(U a)ᴴ=U (b-a) := by
    calc _ = (U (b-a)*U a)*(U a)ᴴ := congrArg (fun x => x*(U a)ᴴ) (unitaryEvolution_sub_mul H b a).symm
         _ = _ := by rw [mul_assoc,hU,mul_one]
  rw [orbitChoi,orbitChoi,inner_choiVector Fintype.card_pos,Matrix.trace_mul_comm]
  change (U b*(U a)ᴴ).trace/(Fintype.card (Fin (n+2)→Bool):ℂ)=_
  rw [he]
  simp only [amplitude,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,U,H]

/-- The test unitary is fixed within the interval and can depend on
the interval, the disorder, and the entire physical orbit. -/
def largeOverlap (ω : PathPauliDisorder) (n : ℕ) (C : unitaryGroup (Fin (n+2)→Bool) ℂ)
    (k κ : ℝ) : Set ℝ :=
  {t | κ ≤ ‖inner ℂ (orbitChoi ω n (k*t)) (choiVector C.val)‖}

theorem empty_large_overlap (ω : PathPauliDisorder) (n : ℕ) (k κ : ℝ) :
    largeOverlap ω n 1 k κ={t | κ ≤ ‖amplitude ω n (k*t)‖} := by
  ext t
  change (κ ≤ ‖inner ℂ (orbitChoi ω n (k*t)) (choiVector (1:Reg (n+2)))‖) ↔ _
  have hzero : orbitChoi ω n 0=choiVector (1:Reg (n+2)) := by
    simp only [orbitChoi,unitaryEvolution,zero_smul,NormedSpace.exp_zero]
  rw [norm_inner_symm,←hzero,orbit_inner,sub_zero]
  rfl

/-- Autocorrelation at short lags controls a target at every origin.
The loss depends on the minimum lag, independent of the interval origin. -/
theorem local_overlap_duration (ω : PathPauliDisorder) (n : ℕ) {h B k κ : ℝ} (hh : 0 ≤ h)
    (hk : 0 < k) (hκ : 0 < κ) (htail : ∀ s∈Icc (k*h) (k*B), ‖amplitude ω n s‖ ≤ κ^2/2)
    (C : unitaryGroup (Fin (n+2)→Bool) ℂ) (v : ℝ) :
    volume.real (largeOverlap ω n C k κ ∩ Icc v (v+B)) ≤ (⌈2/κ^2⌉₊:ℝ)*(2*h) := by
  apply volume_of_separated_card _ _ hh
  intro F hF hsep
  let U (x : ℝ) := orbitChoi ω n (k*x)
  have hn (x) : ‖U x‖=1 := norm_choiVector_eq_one Fintype.card_pos
    (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) _).1
  have hz : ‖choiVector C.val‖=1 := norm_choiVector_eq_one Fintype.card_pos C.property.1
  have hordered (x) (hx : x∈F) (y) (hy : y∈F) (hxy : x < y) :
      ‖inner ℂ (U x) (U y)‖ ≤ κ^2/2 := by
    have hd := hsep y hy x hx hxy.ne'
    rw [abs_of_pos (sub_pos.mpr hxy)] at hd
    have hlo := (hF hx).2.1
    have hhi := (hF hy).2.2
    change ‖inner ℂ (orbitChoi ω n (k*x)) (orbitChoi ω n (k*y))‖ ≤ _
    rw [orbit_inner,←mul_sub]
    exact htail _ ⟨mul_le_mul_of_nonneg_left hd.le hk.le,mul_le_mul_of_nonneg_left
      (by linarith only [hlo,hhi]) hk.le⟩
  have hcard := common_target_card F U _ hκ hz.le (fun x _ => (hn x).le) (fun _ h => (hF h).1)
    (fun x hx y hy h => by
      rcases lt_or_gt_of_ne h with h|h
      · exact hordered x hx y hy h
      · rw [norm_inner_symm]; exact hordered y hy x hx h)
  exact Nat.cast_le.mp (hcard.trans (Nat.le_ceil _))

/-- For one frozen path, the fraction of any unit interval on which
the orbit has a prescribed positive overlap with one target tends
uniformly to zero over all interval origins and target unitaries. -/
theorem gaussian_moving_overlap {κ η k B : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hk : 0 < k) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ (C : unitaryGroup (Fin (n+2)→Bool) ℂ) (v : ℝ),
      volume.real (largeOverlap ω n C k κ ∩ Icc v (v+B)) ≤ η := by
  let M : ℝ := ⌈2/κ^2⌉₊
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let h := η/(2*(1+M))
  have hh : 0 < h := div_pos hη (by positivity)
  have hs : (2*(1+M))*h=η := by dsimp only [h]; field_simp [show 1+M≠0 by positivity]
  filter_upwards [gaussian_uniform_trace_decay (T:=k*B) (mul_pos hk hh)
    (show 0 < κ^2/2 by positivity)] with ω hw
  filter_upwards [hw] with n hn
  intro C v
  apply (local_overlap_duration ω n hh.le hk hκ (fun s h => (hn s h).le) C v).trans
  change M*(2*h) ≤ η
  linarith only [hs,hh]

#print axioms local_overlap_duration
#print axioms gaussian_moving_overlap
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
