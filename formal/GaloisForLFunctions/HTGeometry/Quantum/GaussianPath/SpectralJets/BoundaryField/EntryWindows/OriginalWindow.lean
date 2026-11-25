import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.DateProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.TerminalField
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Conditional probability of a forecast for the true empty-circuit entry -/

open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
open PrecisionReturns PrefixCouplings
noncomputable section

/-- The original physical prefix when the last longitudinal coefficient is y. -/
def replacedGenerator (ω : PathPauliDisorder) (k : ℕ) (y : ℝ) : selfAdjoint (Register (k+3)) :=
  let p := pathPauliDisorderShell (Function.update ω (terminalCoordinate k) y) (k+1)
  ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian _⟩

theorem replaced_affine (ω : PathPauliDisorder) (k : ℕ) (y : ℝ) :
    (replacedGenerator ω k y).val=boundaryHamiltonian ω k (-ω (terminalCoordinate k))+
      (y:ℂ) • SpinExtension.lastPauli (k+2) 2 := by
  have h := boundary_update ω k y 0
  simp only [add_zero] at h
  rw [boundaryHamiltonian,Complex.ofReal_zero,zero_smul,add_zero] at h
  change pathHamiltonian _=_
  rw [h,boundaryHamiltonian,boundaryHamiltonian,add_assoc,←add_smul,←Complex.ofReal_add,
    show -ω (terminalCoordinate k)+y=y-ω (terminalCoordinate k) by ring]

/-- After revealing all other couplings, the probability of any genuine
first scalar entry in a short window around a positive forecast is
O(h^(1/D²)) on every bounded interval of the unrevealed field. The
origin of the first entry can use the full Hamiltonian. -/
theorem gaussian_truncated_first_entry_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ T> (0:ℝ), ∀ R≥(0:ℝ), ∀ ε∈Ioo (0:ℝ) (sqrt 2),
      let D := 2^(k+3)
      ∃ c> (0:ℝ), ∃ K : ℝ, ∀ r∈Ioc (0:ℝ) 1,
        (gaussianReal 0 1).real {y : ℝ | |y|≤R ∧ ∃ a> (0:ℝ),
          let H := replacedGenerator ω k y
          ε<orbitCircuitDistance H 0 a ∧ |firstVisit H a 0 ε-T|<c*r^(D^2)}≤K*r := by
  filter_upwards [gaussian_gapPencil_nonzero] with ω hω
  intro k T hT R hR ε he D
  let A := boundaryHamiltonian ω k (-ω (terminalCoordinate k))
  let Z := SpinExtension.lastPauli (k+2) 2
  have hH (y : ℝ) : (A+(y:ℂ) • Z).IsHermitian := by
    rw [←replaced_affine ω k y]
    exact (replacedGenerator ω k y).2.isHermitian
  let H (y : ℝ) : selfAdjoint (Register (k+3)) := ⟨A+(y:ℂ) • Z,(hH y).isSelfAdjoint⟩
  have hphys (y : ℝ) : replacedGenerator ω k y=H y := Subtype.ext (replaced_affine ω k y)
  let L := 1+‖A‖+R*‖Z‖
  have hL : 0<L := by dsimp only [L]; linarith only [norm_nonneg A,mul_nonneg hR (norm_nonneg Z)]
  obtain ⟨c,hc,K,hK⟩ := pencil_entry_window A Z hH (hω k _) T L ε hT hL he
  refine ⟨c,hc,K,fun r hr => (measureReal_mono ?_).trans (hK r hr)⟩
  rintro y ⟨hy,a,ha,hout,hv⟩
  refine ⟨fun i => (abs_eigenvalue_le_l2_opNorm (hH y) i).trans ?_,a,ha,?_,?_⟩
  · have h := norm_add_le A ((y:ℂ) • Z)
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at h
    dsimp only [L]
    linarith only [h,mul_le_mul_of_nonneg_right hy (norm_nonneg Z)]
  · simpa only [hphys] using hout
  · simpa only [hphys] using hv

#print axioms gaussian_truncated_first_entry_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
