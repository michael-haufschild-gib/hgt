import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BondMinimum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.DisjointWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Weakest-bond estimates on disjoint candidates of the frozen chain -/

open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

/-- In a buffer beginning at s, use every third bond so that none of
the other candidates can be a direct neighbour of a chosen cut. -/
def candidateIndex (s : ℕ) {N : ℕ} (j : Fin N × Fin 9) : ℕ × PathPauliDirections :=
  (s+3*j.1.val,Sum.inr ((finProdFinEquiv (m:=3) (n:=3)).symm j.2))

private theorem candidate_injective (s N : ℕ) : Function.Injective (candidateIndex s (N:=N)) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  have hp := congrArg Prod.fst h
  change s+3*i.val=s+3*j.val at hp
  have hd := congrArg Prod.snd h
  apply Prod.ext
  · apply Fin.ext
    change i.val=j.val
    omega
  · exact (finProdFinEquiv (m:=3) (n:=3)).symm.injective (Sum.inr.inj hd)

/-- All N candidate bonds exceed the weak box with the exact product
miss probability, at any specified position of the original chain. -/
theorem physical_miss_mass (s N : ℕ) (δ : ℝ) :
    pathPauliDisorderLaw.real {ω | ∀ j : Fin N, (fun k => ω (candidateIndex s (j,k)))∉weakBond δ} =
      (1-(gaussianReal 0 1).real (Icc (-δ) δ)^9)^N := by
  let γ := gaussianReal 0 1
  let F := fun (ω : PathPauliDisorder) (j : Fin N) k => ω (candidateIndex s (j,k))
  let E := Set.univ.pi fun _ : Fin N => (weakBond δ)ᶜ
  have hE : MeasurableSet E := MeasurableSet.univ_pi fun _ => (weakBond_measurable δ).compl
  have hp := SpanningDensity.FixedHorizon.disjoint_window_law γ (candidateIndex s) (candidate_injective s N)
  simp only [Measure.infinitePi_eq_pi] at hp
  have he := hp.measureReal_preimage hE.nullMeasurableSet
  change pathPauliDisorderLaw.real (F ⁻¹' E)=_ at he
  have hset : {ω | ∀ j : Fin N, (fun k => ω (candidateIndex s (j,k)))∉weakBond δ}=F ⁻¹' E := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_preimage,E,Set.mem_univ_pi,Set.mem_compl_iff,F]
  rw [hset]
  exact he.trans (buffer_miss_mass N δ)

/-- A candidate buffer of length 3N fails with probability at most
exp(-c N δ⁹) for 0 ≤ δ ≤ 1. -/
theorem physical_miss_tail (s N : ℕ) {δ : ℝ} (hδ : 0≤δ) (h₁ : δ≤1) :
    pathPauliDisorderLaw.real {ω | ∀ j : Fin N, (fun k => ω (candidateIndex s (j,k)))∉weakBond δ} ≤
      exp (-(N:ℝ)*((2*gaussianDensityFloor)*δ)^9) := by
  rw [physical_miss_mass,←buffer_miss_mass]
  exact buffer_miss_bound N hδ h₁


/-- Every one of b consecutive buffers has a cut of size at most
q⁻⁶, outside probability b exp(-c q⁸), for q⁶² candidates per buffer. -/
theorem all_buffer_miss_bound (b k : ℕ) :
    let q := k+1
    let N := q^62
    pathPauliDisorderLaw.real (⋃ i : Fin b, {ω | ∀ j : Fin N,
      (fun l => ω (candidateIndex (3*N*i.val) (j,l)))∉weakBond (((q:ℝ)^6)⁻¹)}) ≤
      b*exp (-((2*gaussianDensityFloor)^9)*(q:ℝ)^8) := by
  intro q N
  have hp : (0:ℝ)<q := by dsimp only [q]; positivity
  have hq : 1≤(q:ℝ) := by exact_mod_cast (by omega : 1≤q)
  have hδ : (((q:ℝ)^6)⁻¹)≤1 := (inv_le_one₀ (pow_pos hp _)).mpr (one_le_pow₀ hq)
  have hprice : -(N:ℝ)*((2*gaussianDensityFloor)*((q:ℝ)^6)⁻¹)^9 =
      -((2*gaussianDensityFloor)^9)*(q:ℝ)^8 := by
    dsimp only [N]
    rw [Nat.cast_pow]
    field_simp
  apply (measureReal_iUnion_fintype_le _).trans
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin b) _ =>
    physical_miss_tail (3*N*i.val) N (inv_nonneg.mpr (pow_nonneg hp.le _)) hδ)
  simpa only [hprice,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

#print axioms all_buffer_miss_bound
#print axioms physical_miss_mass
#print axioms physical_miss_tail
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
