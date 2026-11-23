import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # A half-budget increment at the speed of the largest coupling -/
open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes
noncomputable section

/-- Product of physical duration and maximum coupling certified by local simulation. -/
def travelProduct (N : ℕ) : ℝ := 2*(N:ℝ)*localCrossingWidth N

private theorem unit_box {n : ℕ} (x : PrefixIndex n → ℝ) (t : ℝ)
    (hs : 128 ≤ (n+2).sqrt) (hcap : ∀ i, |x i| ≤ 2*((n+2:ℕ):ℝ))
    (ht : |t| ≤ localCrossingWidth (n+2)) :
    pathGateDistance n (nearHilbertContinuousCircuitBudget (n+2)/2) x t ≤ 1/100 := by
  let N := n+2
  let u : PathShell n := WithLp.toLp 2 fun l => x ((pathCoeffEquiv n).symm l)
  have hgen : numberedGenerator n x = pathHamiltonian u := by
    simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  obtain ⟨hvol,hpay⟩ := local_width_budget ((by decide : 64 ≤ 128).trans hs) hN (abs_nonneg t) ht
  obtain ⟨p,r,hr,he,hcost⟩ := binary_patch_schedule N N |t| (2*(N:ℝ)) (abs_nonneg t) hvol hs
    (by positivity) le_rfl
  have h := path_patch_circuit_abs u (2*(N:ℝ)) (by positivity) (fun l => hcap ((pathCoeffEquiv n).symm l)) p r hr t
  have hpaid := hpay _ hcost
  change 2*(r*(N*patchGateCost p 21)) ≤ nearHilbertContinuousCircuitBudget N at hpaid
  have h' := approx_enlarge h he (show r*(N*patchGateCost p 21) ≤ nearHilbertContinuousCircuitBudget N/2 by omega)
  unfold pathGateDistance
  rw [hgen]
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp h'

/-- Scaling the generator to the full coupling range of the binary local
schedule converts its increment duration into an inverse-coupling bound. -/
theorem capped_increment {n : ℕ} (x : PrefixIndex n → ℝ) (t : ℝ)
    (hs : 128 ≤ (n+2).sqrt) {R : ℝ} (hR : 0 < R) (hcap : ∀ i, |x i| ≤ R)
    (ht : R*|t| ≤ travelProduct (n+2)) :
    pathGateDistance n (nearHilbertContinuousCircuitBudget (n+2)/2) x t ≤ 1/100 := by
  let N := n+2
  let a := 2*(N:ℝ)/R
  have ha : 0 < a := div_pos (by dsimp [N]; positivity) hR
  have har : a*R = 2*(N:ℝ) := div_mul_cancel₀ _ hR.ne'
  have hy (i) : |(a • x) i| ≤ 2*(N:ℝ) := by
    rw [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left (hcap i) ha.le).trans_eq har
  have hw : |t/a| ≤ localCrossingWidth N := by
    rw [abs_div,abs_of_pos ha,div_le_iff₀ ha]
    apply (mul_le_mul_iff_left₀ hR).mp
    rw [mul_assoc,har,mul_comm |t|,mul_comm (localCrossingWidth N)]
    exact ht
  have hd := unit_box (a • x) (t/a) hs hy hw
  rwa [distance_dilate,mul_comm a,div_mul_cancel₀ _ ha.ne'] at hd

#print axioms capped_increment
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
