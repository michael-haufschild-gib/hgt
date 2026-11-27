import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.PhysicalEnergies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.BalancedScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.SpectralStability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.JoinLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.Carrier
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.BoxMass

/-! # A positive Gaussian seed for the recursive spectral spacing estimate -/
open Set Matrix MeasureTheory Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open Dephasing.GappedSpin.CentralCut
noncomputable section

def gapEvent (n : ℕ) (g : ℝ) : Set (PathLabel n→ℝ) :=
  {x | ∀ i j, i≠j → g≤|energies n x i-energies n x j|}

theorem measurable_gapEvent (n : ℕ) (g : ℝ) : MeasurableSet (gapEvent n g) := by
  simp only [gapEvent,setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (((measurable_energies n i).sub (measurable_energies n j)).abs)

/-- A box around a simple Ising spectrum has positive probability
and already clears the required initial spacing. -/
theorem seed_mass (n : ℕ) : 0<(standardLaw (PathLabel n)).real (gapEvent n (gapScale (n+2))) := by
  classical
  let K := n+2
  let M : ℝ := Fintype.card (PathLabel n)
  let g := 1/(3:ℝ)^K
  let w := nearUniformCarrier n (g/2)
  let r := min 1 (g/(8*M))
  have hM : 0<M := Nat.cast_pos.mpr Fintype.card_pos
  have hg : 0<g := by dsimp only [g]; positivity
  have hr : 0<r := lt_min zero_lt_one (div_pos hg (mul_pos (by norm_num) hM))
  have hsep i j (hij : i≠j) : g≤|pathDiagEnergy w i-pathDiagEnergy w j| := by
    have hs : g/2*3^(n+2)=1/2 := by dsimp only [g,K]; field_simp
    have h := separation_nearUniformCarrier (half_pos hg) (hs.le.trans (by norm_num)) hij
    simpa only [show 2*(g/2)=g by ring,w] using h
  let E := Set.univ.pi fun l => Icc (w l-r) (w l+r)
  have hb := gaussian_rectangular_floor (∅ : Finset (PathLabel n)) w.ofLp hr (min_le_left ..) (le_refl (1:ℝ))
  simp only [Finset.notMem_empty,if_false,card_empty,pow_zero,one_mul] at hb
  have hE : 0<(standardLaw (PathLabel n)).real E :=
    (mul_pos (pow_pos (mul_pos (mul_pos two_pos (by positivity)) hr) _) (exp_pos _)).trans_le hb
  apply hE.trans_le (measureReal_mono _ (measure_ne_top _ _))
  intro x hx
  let u : PathShell n := WithLp.toLp 2 x
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have hn : ‖pathHamiltonian w-pathHamiltonian u‖<g/4 := by
    have hb (l) : |w l-u l|≤r := by
      have hl := hx l (mem_univ l)
      exact abs_le.mpr ⟨by linarith only [hl.2],by linarith only [hl.1]⟩
    apply (coordinate_norm_bound w u hb).trans_lt
    change M*r<g/4
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 (g/(8*M))) hM.le
    have he : M*(g/(8*M))=g/8 := by field_simp
    rw [he] at h
    exact h.trans_lt (by linarith only [hg])
  have hs i : ((pathDiagEnergy w i:ℝ):ℂ)∈spectrum ℂ (pathHamiltonian w) := by
    rw [pathHamiltonian_eq_diagonal w (nearUniformCarrier_offDiag _),Matrix.spectrum_diagonal]
    exact mem_range_self _
  have hh := stable_spacing _ _ hH (pathDiagEnergy w) hs hg hsep hn
  have hh' := transfer_spacing (qubitConfigFin K) (energies_range x).symm (half_pos hg) hh
  intro i j hij
  apply le_trans _ (hh' i j hij)
  have h₁ : gapScale K≤(1/2:ℝ)^K*(1/3:ℝ)^K := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h₂ : (1/2:ℝ)^K≤1/2 := by
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp only [K]; omega : 1≤K)).trans_eq (pow_one _)
  exact h₁.trans ((mul_le_mul_of_nonneg_right h₂ (by positivity)).trans_eq (by rw [one_div_pow]; dsimp only [g]; ring))

#print axioms seed_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
