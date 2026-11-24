import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BlockWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.BoxFrequency

/-! # Mean width of independent contiguous pieces of one frozen chain -/

open Filter Set MeasureTheory ProbabilityTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

/-- A row contains three onsite coefficients and nine bonds to its successor. -/
abbrev RowBlock (L : ℕ) := Fin L × PathPauliDirections

def readRows (L : ℕ) (ω : PathPauliDisorder) (j : ℕ) (p : RowBlock L) : ℝ :=
  ω (j*L+p.1.val,p.2)

def rowLabel {n : ℕ} : PathLabel n → RowBlock (n+2)
  | .inl (i,a) => (i,.inl a)
  | .inr (e,ab) => (e.castSucc,.inr ab)

def readBlock (n : ℕ) (ω : PathPauliDisorder) (j : ℕ) (l : PathLabel n) : ℝ :=
  readRows (n+2) ω j (rowLabel l)

private theorem index_injective (L : ℕ) : Function.Injective
    (fun p : ℕ × RowBlock L => (p.1*L+p.2.1.val,p.2.2)) := by
  have sep {a b : ℕ} (hab : a<b) (i : Fin L) : a*L+i.val<b*L := by
    calc _ < a*L+L := Nat.add_lt_add_left i.isLt _
         _ = (a+1)*L := (Nat.succ_mul ..).symm
         _ ≤ _ := Nat.mul_le_mul_right _ hab
  rintro ⟨a,i,p⟩ ⟨b,j,q⟩ h
  obtain ⟨hh,hd⟩ := Prod.mk.inj h
  change a*L+i.val=b*L+j.val at hh
  have hab : a=b := by
    apply le_antisymm <;> apply le_of_not_gt <;> intro h
    · have := sep h j
      omega
    · have := sep h i
      omega
  subst b
  exact Prod.ext rfl (Prod.ext (Fin.ext (Nat.add_left_cancel hh)) hd)

/-- Disjoint blocks obey the strong law for every integrable block observable. -/
theorem block_strong_law (L : ℕ) (f : (RowBlock L → ℝ)→ℝ) (hf : Measurable f)
    (hi : Integrable f (Measure.infinitePi fun _ : RowBlock L => gaussianReal 0 1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, f (readRows L ω j))/k) atTop
      (𝓝 (∫ u, f u ∂Measure.infinitePi fun _ : RowBlock L => gaussianReal 0 1)) := by
  let μ := Measure.infinitePi fun _ : RowBlock L => gaussianReal 0 1
  let ν := Measure.infinitePi fun _ : ℕ => μ
  have hr : MeasurePreserving (readRows L) pathPauliDisorderLaw ν :=
    SpanningDensity.FixedHorizon.disjoint_window_law _ _ (index_injective L)
  let X (j : ℕ) (u : ℕ→RowBlock L→ℝ) := f (u j)
  have hid (j : ℕ) : IdentDistrib (X j) f ν μ := by
    have h := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) j
    have he : IdentDistrib (Function.eval j) id ν μ :=
      ⟨h.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact h.map_eq⟩
    exact he.comp hf
  have hind : iIndepFun X ν := iIndepFun_infinitePi (P:=fun _ => μ) (fun _ => hf)
  have h := strong_law_ae_real X ((hid 0).integrable_iff.mpr hi)
    (fun _ _ h => hind.indepFun h) (fun j => (hid j).trans (hid 0).symm)
  rw [(hid 0).integral_eq] at h
  exact hr.quasiMeasurePreserving.ae h

/-- Energy diameter for the indicated finite collection of Gaussian coefficients. -/
def blockWidth (n : ℕ) (u : PathLabel n→ℝ) : ℝ :=
  circuitHamiltonianSpectralWidth (shellOperator (WithLp.toLp 2 u))

private theorem continuous_blockWidth (n : ℕ) : Continuous (blockWidth n) := by
  have hW : LipschitzWith 2 (fun H : selfAdjoint (Register (n+2)) => circuitHamiltonianSpectralWidth H) := by
    apply LipschitzWith.of_dist_le_mul
    intro H K
    rw [Real.dist_eq]
    rw [dist_eq_norm]
    change |circuitHamiltonianSpectralWidth H-circuitHamiltonianSpectralWidth K|≤2*‖H.val-K.val‖
    have h₁ := width_perturb K H
    have h₂ := width_perturb H K
    rw [norm_sub_rev] at h₂
    exact abs_le.mpr ⟨by linarith only [h₂],by linarith only [h₁]⟩
  have hc : Continuous (fun u : PathLabel n→ℝ => pathHamiltonian (WithLp.toLp 2 u)) :=
    (pathHamiltonianLM n).continuous_of_finiteDimensional.comp (PiLp.continuous_toLp 2 _)
  exact hW.continuous.comp (hc.subtype_mk fun u => isSelfAdjoint_pathHamiltonian _)


/-- Absolute values of individual Gaussian coordinates are integrable on a row block. -/
theorem integrable_row_abs {L : ℕ} (l : RowBlock L) :
    Integrable (fun u : RowBlock L→ℝ => |u l|) (Measure.infinitePi fun _ : RowBlock L => gaussianReal 0 1) := by
  let γ := gaussianReal 0 1
  let μ := Measure.infinitePi fun _ : RowBlock L => γ
  have hi : Integrable (fun t : ℝ => |t|) γ := by
    have h : MemLp id 1 γ := memLp_id_gaussianReal' _ (by simp)
    simpa [Real.norm_eq_abs] using (memLp_one_iff_integrable.mp h).norm
  have h := measurePreserving_eval_infinitePi (fun _ : RowBlock L => γ) l
  have he : IdentDistrib (Function.eval l) id μ γ :=
    ⟨h.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact h.map_eq⟩
  exact (he.comp measurable_abs).integrable_iff.mpr hi

theorem width_le_mass (n : ℕ) (u : PathLabel n→ℝ) : blockWidth n u ≤ 2*∑ l, |u l| := by
  have hp := width_perturb (0 : selfAdjoint (Register (n+2))) (shellOperator (WithLp.toLp 2 u))
  rw [width_zero,zero_add] at hp
  change blockWidth n u≤2*‖pathHamiltonian (WithLp.toLp 2 u)-0‖ at hp
  rw [sub_zero] at hp
  apply hp.trans (mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2))
  rw [pathHamiltonian_eq_sum]
  simpa only [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one] using
    norm_sum_le Finset.univ (fun l : PathLabel n => ((u l:ℝ):ℂ) • finitePauliMatrix (pathWord l))

/-- Expected open-chain width on n+2 sites. The last outgoing bond is unused. -/
def meanWidth (n : ℕ) : ℝ := ∫ u, blockWidth n (fun l => u (rowLabel l))
  ∂Measure.infinitePi fun _ : RowBlock (n+2) => gaussianReal 0 1

theorem gaussian_block_width_law :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, blockWidth n (readBlock n ω j))/k) atTop (𝓝 (meanWidth n)) := by
  apply ae_all_iff.mpr
  intro n
  let F (u : RowBlock (n+2)→ℝ) := blockWidth n (fun l => u (rowLabel l))
  have hf : Measurable F := (continuous_blockWidth n).measurable.comp
    (measurable_pi_lambda _ fun l => measurable_pi_apply (rowLabel l))
  apply block_strong_law (n+2) F hf
  have h := integrable_finsetSum Finset.univ (fun (l : PathLabel n) _ => integrable_row_abs (rowLabel l))
  apply (h.const_mul 2).mono' hf.aestronglyMeasurable
  filter_upwards with u
  have hn : 0≤F u := circuitHamiltonianSpectralWidth_nonneg _
  rw [Real.norm_of_nonneg hn]
  exact width_le_mass n _

#print axioms gaussian_block_width_law
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
