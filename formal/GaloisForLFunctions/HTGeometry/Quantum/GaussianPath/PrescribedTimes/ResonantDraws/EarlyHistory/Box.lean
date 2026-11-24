import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass

/-! # Gaussian mass of a prescribed collection of affordable observations -/
open Set MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
open WeakBonds ShortWindows
noncomputable section

/-- All specified dates admit their respective gate budgets at error one tenth. -/
def affordableHistory (n : ℕ) (A : Set ℝ) (s : ℝ → ℕ) : Set (PrefixIndex n → ℝ) :=
  {x | ∀ t ∈ A, pathGateDistance n (s t) x t ≤ 1/10}

theorem closed_affordableHistory (n : ℕ) (A : Set ℝ) (s : ℝ → ℕ) :
    IsClosed (affordableHistory n A s) := by
  have he : affordableHistory n A s = ⋂ t : A, {x | pathGateDistance n (s t) x t ≤ 1/10} := by
    ext x
    simp only [affordableHistory,mem_setOf_eq,mem_iInter,Subtype.forall]
  rw [he]
  exact isClosed_iInter fun t => isClosed_le (continuous_distance_at_time ..) continuous_const

private theorem norm_generator {n : ℕ} {x : PrefixIndex n → ℝ} {δ : ℝ} (h : ∀ i, |x i| ≤ δ) :
    ‖numberedGenerator n x‖ ≤ (Fintype.card (PrefixIndex n):ℝ)*δ := by
  unfold numberedGenerator
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : PathLabel n, δ := Finset.sum_le_sum fun l _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
      exact h _
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_congr (pathCoeffEquiv n)]

private theorem full_box_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → ℝ}
    {δ : ℝ} (h : x∈coefficientBox Finset.univ δ univ) (i : ι) : |x i| ≤ δ := by
  change ∀ j ∈ (univ : Set ι), x j ∈ (if j ∈ (Finset.univ : Finset ι) then Icc (-δ) δ else univ) at h
  exact abs_le.mpr (by simpa only [Finset.mem_univ,if_true,mem_Icc] using h i (mem_univ _))

/-- If every coupling is at most δ in absolute value, the identity fits
throughout a symmetric interval. The same box supports arbitrarily many
simultaneous observations, including a continuous history. -/
theorem gaussian_history_mass (k : ℕ) (A : Set ℝ) (s : ℝ → ℕ) {T δ : ℝ}
    (hA : ∀ t ∈ A, |t|≤T) (hδ : 0≤δ) (hδ' : δ≤1)
    (hfit : (Fintype.card (PrefixIndex (k+1)):ℝ)*δ*T ≤ 1/10) :
    (2*gaussianDensityFloor*δ)^Fintype.card (PrefixIndex (k+1)) ≤
      pathPauliDisorderLaw.real (prefixPoint k ⁻¹' affordableHistory (k+1) A s) := by
  let n := k+1
  let m := Fintype.card (PrefixIndex n)
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  let K := coefficientBox (Finset.univ : Finset (PrefixIndex n)) δ univ
  have hlow : (2*gaussianDensityFloor*δ)^m ≤ μ.real K := by
    simpa only [mul_pow,Finset.card_univ,probReal_univ,one_pow,mul_one] using
      coefficientBox_floor (Finset.univ : Finset (PrefixIndex n)) univ hδ hδ'
  have hsub : K ⊆ affordableHistory n A s := by
    intro x hx t ht
    have hg := norm_generator (n:=n) (x:=x) (δ:=δ) (full_box_coordinate (ι:=PrefixIndex n) hx)
    have he : IsSelfAdjoint (numberedGenerator n x) := (prefixGenerator n x).2
    have hzero : unitaryEvolution (numberedGenerator n x) 0=1 := by simp [unitaryEvolution]
    have htime := norm_unitaryEvolution_time_sub_le he t 0
    rw [hzero,sub_zero] at htime
    have hdist := htime.trans ((mul_le_mul hg (hA t ht) (abs_nonneg t)
      (mul_nonneg (Nat.cast_nonneg _) hδ)).trans hfit)
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
    simpa only [TwoQubitCircuit.one_eval,one_smul] using hdist
  have hm := (gaussian_pauli_prefix_coordinates_law n).measureReal_preimage
    (closed_affordableHistory n A s).measurableSet.nullMeasurableSet
  exact (hlow.trans (measureReal_mono (μ:=μ) hsub)).trans_eq hm.symm

#print axioms gaussian_history_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
