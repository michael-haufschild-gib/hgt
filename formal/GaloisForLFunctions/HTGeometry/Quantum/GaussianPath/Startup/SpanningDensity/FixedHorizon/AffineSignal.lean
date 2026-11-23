import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GaussianFields
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.TraceResponse

/-! # Gaussian sublevel bounds for affine Hamiltonian correlations -/
open Matrix MeasureTheory ProbabilityTheory Function NormedSpace Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private abbrev Op (ι : Type*) := Matrix ι ι ℂ

/-- Hamiltonian with a fixed exterior and freely varied local terms. -/
def affineHamiltonian {m : ℕ} (H : Op ι) (P : Fin m → Op ι) (x : Fin m → ℝ) : Op ι :=
  H+∑ i, (x i:ℂ) • P i

/-- Normalized real correlation of a transported output and a fixed input. -/
def signal (K Y B : Op ι) (t : ℝ) : ℝ :=
  ((Fintype.card ι : ℂ)⁻¹*(unitaryEvolution K (-t)*Y*unitaryEvolution K t*B).trace).re

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
private theorem shiftField {m : ℕ} (H : Op ι) (P : Fin m → Op ι) (x : Fin m→ℝ) (i : Fin m) (s : ℝ) :
    affineHamiltonian H P (update x i s)=
      (H+∑ j∈Finset.univ.erase i, (x j:ℂ) • P j)+(s:ℂ) • P i := by
  unfold affineHamiltonian
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),update_self,←add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

theorem continuous_signal (Y B : Op ι) (t : ℝ) : Continuous (fun K => signal K Y B t) := by
  letI : CStarAlgebra (Op ι) := {}
  letI : NormedAlgebra ℚ (Op ι) := .restrictScalars ℚ ℂ _
  have flow (s : ℝ) : Continuous (fun K : Op ι => unitaryEvolution K s) :=
    NormedSpace.exp_continuous.comp ((continuous_id.const_smul (-Complex.I)).const_smul s)
  let L := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  exact Complex.continuous_re.comp (continuous_const.mul (L.continuous.comp
    ((((flow (-t)).mul continuous_const).mul (flow t)).mul continuous_const)))

theorem continuous_signal_fields {m : ℕ} (H : Op ι) (P : Fin m → Op ι)
    (Y B : Op ι) (t : ℝ) : Continuous (fun x => signal (affineHamiltonian H P x) Y B t) := by
  apply (continuous_signal Y B t).comp
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ => (Complex.continuous_ofReal.comp (continuous_apply i)).smul continuous_const)

/-- Varying one field while all others are fixed gives an entire
response with growth controlled by the observation horizon. -/
theorem entire_signal_fields {m : ℕ} (H Y B : Op ι) (P : Fin m → Op ι)
    (hH : IsSelfAdjoint H) (hY : Y.IsHermitian) (hB : B.IsHermitian)
    (hYn : ‖Y‖ ≤ 1) (hBn : ‖B‖ ≤ 1) (hP : ∀ i, IsSelfAdjoint (P i)) (hPn : ∀ i, ‖P i‖ ≤ 1)
    {t T : ℝ} (ht : |t| ≤ T) :
    ∀ i, EntireFieldSlice (fun x => signal (affineHamiltonian H P x) Y B t) (fun R => Real.exp (2*T*R)) i := by
  intro i x
  let R := H+∑ j∈Finset.univ.erase i, (x j:ℂ) • P j
  have hR : IsSelfAdjoint R := by
    change star (H+∑ j∈Finset.univ.erase i, (x j:ℂ) • P j)=H+∑ j∈Finset.univ.erase i, (x j:ℂ) • P j
    simp only [star_add,star_sum,star_smul,hH.star_eq,fun j => (hP j).star_eq,Complex.star_def,Complex.conj_ofReal]
  refine ⟨fieldTrace R (P i) Y B t,fieldTrace_differentiable R (P i) Y B t,fun s => ?_,fun z => ?_⟩
  · change _ = Complex.ofReal (signal (affineHamiltonian H P (update x i s)) Y B t)
    rw [shiftField]
    have him := fieldTrace_real R (P i) Y B hR (hP i) hY hB t s
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using him)
  · apply (norm_fieldTrace R (P i) Y B hR (hP i) hYn hBn (hPn i) t z).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) (norm_nonneg _))

/-- A single threshold detects a calibrated physical signal uniformly over
matrix size, exterior Hamiltonian, normalized probes and bounded times. -/
theorem affine_gaussian_signal (m : ℕ) {a h η T : ℝ} (hh : 0<h) (hη : 0<η) :
    ∃ r : ℝ, 0<r ∧ ∀ (κ : Type*) [Fintype κ] [DecidableEq κ] [Nonempty κ],
      ∀ (H Y B : Op κ) (P : Fin m → Op κ),
      IsSelfAdjoint H → Y.IsHermitian → B.IsHermitian → ‖Y‖≤1 → ‖B‖≤1 →
      (∀ i, IsSelfAdjoint (P i)) → (∀ i, ‖P i‖≤1) →
      ∀ t : ℝ, |t|≤T → ∀ u : Fin m → ℝ, (∀ i, |u i|≤a) →
      h≤|signal (affineHamiltonian H P u) Y B t| →
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1))
        {x | |signal (affineHamiltonian H P x) Y B t|≤r} ≤ ENNReal.ofReal η := by
  let M := fun q : ℝ => Real.exp (2*T*q)
  obtain ⟨r,hr,hg⟩ := gaussian_fields_signal (a:=a) m hh hη M (fun _ => (Real.exp_pos _).le)
  refine ⟨r,hr,?_⟩
  intro κ _ _ _ H Y B P hH hY hB hYn hBn hP hPn t ht u hu hsig
  exact hg _ (continuous_signal_fields H P Y B t)
    (entire_signal_fields H Y B P hH hY hB hYn hBn hP hPn ht) u hu hsig

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
