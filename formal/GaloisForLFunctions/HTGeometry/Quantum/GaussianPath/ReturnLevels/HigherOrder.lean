import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.PathIncrement
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedPathCircuit

/-! # Higher-order local sweeps reduce the dimension of exceptional tolerances -/
open Set MeasureTheory Matrix NormedSpace
open scoped ENNReal NNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section
open LocalPatches (Register)
local instance (N : ℕ) : CStarAlgebra (Register N) where

private theorem higher_step {n : ℕ} (u : PathShell n) (j : ℕ) :
    ∃ B : ℝ≥0, ∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) ((B:ℝ)*|t|^(j+2))
      (3^j*Fintype.card (PathLabel n)) (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨Z,hlen,hsum,_,_,hs⟩ := exists_path_gate_generators u
  obtain ⟨w,hw,hu,hwlen,_⟩ := ProductFormula.exists_word Z j
  let K := 1+ProductFormula.mass w+‖Z.sum‖
  have hmass := ProductFormula.mass_nonneg w
  have hnorm := norm_nonneg Z.sum
  have hK : 0 < K := by dsimp only [K]; linarith only [hmass,hnorm]
  have hm : ProductFormula.mass w ≤ K := by dsimp only [K]; linarith only [hnorm]
  have hz : ‖Z.sum‖ ≤ K := by dsimp only [K]; linarith only [hmass]
  refine ⟨⟨6*K^(j+2),by positivity⟩,?_⟩
  intro t
  change HasProjectiveCircuitApproximation _ (6*K^(j+2)*|t|^(j+2)) _ _
  have hB : 6*K^(j+2)*|t|^(j+2)=6*(|t| * K)^(j+2) := by rw [mul_pow]; ring
  rw [hB]
  by_cases ht : |t| * K ≤ 1
  · have ht' : ‖(t:ℂ)‖ * K ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht
    have he := ProductFormula.contact_error hw hK hm hz ht'
    have hf (y) (hy : y ∈ w) : ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit (n+2),
        C.gateCount=1 ∧ exp (t • y)=c • (C.eval : Register (n+2)) := by
      obtain ⟨x,hx,b,rfl⟩ := hu y hy
      rw [Complex.coe_smul,smul_smul]
      exact hs (t*b) x hx
    obtain ⟨c,hc,C,hC,hprod⟩ := compile_path_word_steps w t hf
    have hword : ProductFormula.word w (t:ℂ)=(w.map fun y => exp (t • y)).prod := by simp [ProductFormula.word]
    rw [hword,hprod,Complex.coe_smul,hsum,norm_sub_rev,Complex.norm_real,Real.norm_eq_abs] at he
    exact ⟨c,hc,C,(hC.trans (hwlen.trans (congrArg (3^j*·) hlen))).le,he⟩
  · have hu := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
    have hdist := norm_sub_le (unitaryEvolution (pathHamiltonian u) t) (1:Register (n+2))
    rw [CStarRing.norm_of_mem_unitary hu,norm_one] at hdist
    refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
    rw [one_smul,TwoQubitCircuit.one_eval]
    exact hdist.trans (by linarith only [one_le_pow₀ (le_of_not_ge ht) (n := j+2)])

/-- The dimension bound holds for every contact order. Its gate
overhead is the physical length of the corresponding product formula. -/
theorem higher_shared_levels_dimension {n : ℕ} (x : PathShell n) (j : ℕ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
    let J := 3^j*Fintype.card (PathLabel n)
    dimH (⋃ s : ℕ, orbitCircuitDistance H s '' {t | orbitCircuitDistance H s t=orbitCircuitDistance H (s+J) t}) ≤
      1/((j+2:ℕ):ℝ≥0∞) := by
  intro H J
  obtain ⟨B,hB⟩ := higher_step x j
  rw [dimH_iUnion]
  apply iSup_le
  intro s
  apply shared_levels_dimension _ _ B (j+2) (by omega)
  intro t u
  have hu := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u) s
    (orbitCircuitDistance H s u)).mpr le_rfl
  have h := affordable_add_time H hu (hB (t-u))
  rw [show u+(t-u)=t by ring] at h
  exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp h

#print axioms higher_shared_levels_dimension
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
