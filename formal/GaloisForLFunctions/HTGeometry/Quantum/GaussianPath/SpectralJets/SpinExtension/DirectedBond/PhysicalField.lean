import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.FiniteEnergy

/-! # The directed bond and the physical terminal field in spin coordinates -/
open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*}

/-- The new onsite X operator exchanges the two computational sectors. -/
def tip (I : Type*) [DecidableEq I] : Matrix (I⊕I) (I⊕I) ℂ :=
  fromBlocks 0 1 1 0

/-- The old terminal direction A is now coupled to the new spin's Z operator. -/
def baseNext (H : E→M) (A : M) (n : ℕ) (p : E × ℂ) :=
  physical (H p.1) (p.2 • A) ((3/5)*height n) ((4/5)*height n)

theorem physical_field (H : E→M) (A : M) (n : ℕ) (p : E × ℂ) (y : ℂ) :
    physical (H p.1) (p.2 • A) ((3/5)*height n) ((4/5+inverseHeight n*y)*height n) =
      baseNext H A n p+y • tip I := by
  have he : (4/5+inverseHeight n*y)*height n=(4/5)*height n+y := by
    calc _ = (4/5)*height n+y*(height n*inverseHeight n) := by ring
         _ = _ := by rw [height_mul_inverse,mul_one]
  simp only [he,baseNext,physical,tip,fromBlocks_smul,fromBlocks_add,smul_zero,add_zero,add_smul]

variable [Fintype I] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem baseNext_analytic {H : E→M} (hH : AnalyticAt ℂ H 0) (A : M) (n : ℕ) :
    AnalyticAt ℂ (baseNext H A n) 0 := by
  have hx : AnalyticAt ℂ (fun p : E × ℂ => p.1) 0 := analyticAt_fst
  have hh : AnalyticAt ℂ (fun p : E × ℂ => H p.1) 0 := hH.comp (f:=fun p : E × ℂ => p.1) (x:=0) hx
  have hv : AnalyticAt ℂ (fun p : E × ℂ => p.2 • A) 0 := analyticAt_snd.smul analyticAt_const
  have hplus : AnalyticAt ℂ (fun p : E × ℂ => H p.1+p.2 • A+((3/5)*height n) • (1:M)) 0 :=
    (hh.add hv).add analyticAt_const
  have hminus : AnalyticAt ℂ (fun p : E × ℂ => H p.1-p.2 • A-((3/5)*height n) • (1:M)) 0 :=
    (hh.sub hv).sub analyticAt_const
  apply analyticAt_matrix_of_entries
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · exact analyticAt_matrix_entry hplus i j
  · exact analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_matrix_entry hminus i j

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
