import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.EnergyLaw
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.RHTower.ChiRamanujanMixedProfileCancellation

/-! # Locally uniform convergence of the finite orientation energy transforms -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology Set Metric _root_.RHTower _root_.RHTower.BAGTrace

/-- Energy measured in cutoff logarithms at unit inverse temperature. -/
def unitEnergy (N : ℕ) (x : Config N) : ℝ := finiteSquarefreeHamiltonian (packet N) x/Real.log N

def unitWeight (N : ℕ) (x : Config N) : ℝ := finiteSquarefreeBornWeight (packet N) 1 x

def unitTransform (N : ℕ) := energyMoment N 0

theorem unit_expansion (N : ℕ) (z : ℂ) :
    unitTransform N z = ∑ x : Config N, (unitWeight N x:ℂ)*Complex.exp (z*(unitEnergy N x:ℂ)) := by
  simp only [unitTransform,energyMoment,zero_div,sub_zero,unitWeight,unitEnergy]

theorem unitWeight_nonneg (N : ℕ) (x : Config N) : 0 ≤ unitWeight N x := by
  unfold unitWeight
  rw [← norm_finiteSquarefreeSourceCoefficient_sq]
  exact sq_nonneg _

theorem unitEnergy_nonneg (N : ℕ) (x : Config N) : 0 ≤ unitEnergy N x := by
  have hL : 0 ≤ Real.log (N:ℝ) := by
    obtain rfl | h := Nat.eq_zero_or_pos N
    · simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  change 0 ≤ (∑ p : ↥(packet N), ((x p).val:ℝ)*Real.log (p.val.val:ℝ))/Real.log N
  exact div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast p.val.property.one_le))) hL

theorem unit_entire (N : ℕ) : Differentiable ℂ (unitTransform N) := by
  rw [show unitTransform N = _ from funext (unit_expansion N)]
  fun_prop

theorem unit_pointwise (w : ℂ) :
    Tendsto (fun N => unitTransform N w) atTop (𝓝 (criticalEulerCarrier w)) := by
  have h := energyMoment_limit 0 w
  have h0 : profile 0 = 0 := by simp [profile,criticalEulerProfile]
  change Tendsto (fun N => energyMoment N 0 w) atTop (𝓝 (Complex.exp (profile w)))
  simpa only [Complex.ofReal_zero,zero_add,h0,sub_zero] using h

/-- Positive energies bound a complex probe by the real probe at the right edge. -/
theorem unit_norm_le (N : ℕ) (w : ℂ) {R : ℝ} (hw : w.re ≤ R) :
    ‖unitTransform N w‖ ≤ ‖unitTransform N (R:ℂ)‖ := by
  let S := ∑ x : Config N, unitWeight N x*Real.exp (R*unitEnergy N x)
  have hs : 0 ≤ S := Finset.sum_nonneg fun x _ => mul_nonneg (unitWeight_nonneg N x) (Real.exp_pos _).le
  have hr : unitTransform N (R:ℂ) = (S:ℂ) := by
    rw [unit_expansion]
    simp only [S,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs,unit_expansion]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (unitWeight_nonneg N x),Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw (unitEnergy_nonneg N x)))
    (unitWeight_nonneg N x)

/-- The finite critical transforms converge uniformly on compact subsets of the complex plane. -/
theorem unit_locally_uniform :
    TendstoLocallyUniformlyOn unitTransform criticalEulerCarrier atTop univ := by
  have hb (z : ℂ) : ∃ R : ℝ, 0 < R ∧ ball z R ⊆ univ ∧ ∃ C : ℝ,
      ∀ N, ∀ w ∈ ball z R, ‖unitTransform N w‖ ≤ C := by
    let A := ‖z‖+1
    obtain ⟨C,hC⟩ := (unit_pointwise (A:ℂ)).norm.bddAbove_range
    refine ⟨1,zero_lt_one,subset_univ _,C,fun N w hw => (unit_norm_le N w ?_).trans (hC (mem_range_self N))⟩
    have h := dist_triangle w z 0
    simp only [dist_zero_right] at h
    exact (Complex.re_le_norm w).trans (by dsimp [A]; linarith only [h,mem_ball.mp hw])
  obtain ⟨G,_,hG⟩ := GaloisForLFunctions.HTGeometry.vitali_tendstoLocallyUniformlyOn_of_isPreconnected
    (F := unitTransform) (Y := univ) (z₀ := (0:ℂ)) isPreconnected_univ
    (fun N => (unit_entire N).differentiableOn) (fun z _ => hb z) (mem_univ _)
    (Frequently.of_forall (fun _ => mem_univ _)) (fun z _ => ⟨_,unit_pointwise z⟩)
  have he : G = criticalEulerCarrier := funext fun z =>
    tendsto_nhds_unique (hG.tendsto_at (mem_univ z)) (unit_pointwise z)
  exact he ▸ hG

theorem unit_jet_uniform (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N => iteratedDeriv k (unitTransform N))
      (iteratedDeriv k criticalEulerCarrier) atTop univ :=
  GaloisForLFunctions.iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform isOpen_univ
    unit_locally_uniform (Eventually.of_forall fun N => (unit_entire N).differentiableOn) k

/-- Every derivative remains convergent when both cutoff and probe move. -/
theorem unit_jet_moving {ι : Type*} {l : Filter ι} {N : ι → ℕ} {w : ι → ℂ} {z : ℂ}
    (hN : Tendsto N l atTop) (hw : Tendsto w l (𝓝 z)) (k : ℕ) :
    Tendsto (fun i => iteratedDeriv k (unitTransform (N i)) (w i)) l
      (𝓝 (iteratedDeriv k criticalEulerCarrier z)) := by
  have hF : Differentiable ℂ criticalEulerCarrier :=
    fun u => ((criticalEulerExponent_hasDerivAt u).cexp).differentiableAt
  have hd := GaloisForLFunctions.differentiableOn_iteratedDeriv isOpen_univ hF.differentiableOn k
  have hc := (differentiableOn_univ.mp hd).continuous.continuousAt.tendsto.comp hw
  have hu := (isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp (unit_jet_uniform k))
    z (mem_univ z)
  exact hc.congr_uniformity (hu.comp (hN.prodMk hw))

#print axioms unit_expansion
#print axioms unitWeight_nonneg
#print axioms unitEnergy_nonneg
#print axioms unit_entire
#print axioms unit_pointwise
#print axioms unit_norm_le
#print axioms unit_locally_uniform
#print axioms unit_jet_uniform
#print axioms unit_jet_moving

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
