import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedPathCircuit
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # Physical approximation of a short patch Hamiltonian at arbitrary order -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
abbrev Register (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

/-- A generator whose real-time flow is a physical one-gate operation up to phase. -/
def OneGateFlow {N : ℕ} (x : Register N) : Prop :=
  ∀ t : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit N, C.gateCount = 1 ∧
    exp (t • x) = c • (C.eval : Register N)

/-- Concatenating physical approximations adds the gate counts and errors. -/
theorem approx_product {N i j : ℕ} {a b : Register N} {e f : ℝ}
    (hb : b ∈ unitary (Register N)) (ha : HasProjectiveCircuitApproximation N e i a)
    (hc : HasProjectiveCircuitApproximation N f j b) :
    HasProjectiveCircuitApproximation N (e+f) (i+j) (a*b) := by
  by_contra hno
  have hfar : ProjectiveCircuitSeparated N (e+f) (i+j) (a*b) :=
    fun z hz C hC => lt_of_not_ge fun h => hno ⟨z,hz,C,hC,h⟩
  have h := projectiveCircuitSeparated_left_of_product hb rfl (by omega : j ≤ i+j) hfar hc le_rfl
  rw [Nat.add_sub_cancel] at h
  obtain ⟨z,hz,C,hC,he⟩ := ha
  exact (h z hz C hC).not_ge he

/-- The gate count is independent of the step size. For small steps the
contact order gives the error; for large steps the unitary diameter suffices. -/
theorem short_word {N : ℕ} (v : List (Register N)) (p : ℕ) (t : ℝ)
    (hs : ∀ x ∈ v, x ∈ skewAdjoint (Register N)) (hg : ∀ x ∈ v, OneGateFlow x) :
    HasProjectiveCircuitApproximation N (6*(7^p*(1+ProductFormula.mass v)*|t|)^(p+1))
      (3^p*v.length) (exp (t • v.sum)) := by
  let K : ℝ := 7^p*(1+ProductFormula.mass v)
  have hmass := ProductFormula.mass_nonneg v
  have hK : 0 < K := by dsimp [K]; positivity
  have hnorm : ‖v.sum‖ ≤ K := (norm_list_sum_le v).trans (by
    change ProductFormula.mass v ≤ 7^p*(1+ProductFormula.mass v)
    exact (by linarith : ProductFormula.mass v ≤ 1+ProductFormula.mass v).trans
      (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))))
  have harg : 0 ≤ K*|t| := mul_nonneg hK.le (abs_nonneg _)
  by_cases hsmall : K*|t| ≤ 1
  · obtain ⟨w,hw,hu,hcount,hsize⟩ := ProductFormula.exists_word v p
    have hcap : ProductFormula.mass w ≤ K := hsize.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
    have he := ProductFormula.contact_error hw hK hcap hnorm (z := (t:ℂ))
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,mul_comm] using hsmall)
    have hword : ProductFormula.word w (t:ℂ) = (w.map fun x => exp (t • x)).prod := by
      simp [ProductFormula.word]
    have hphys (y) (hy : y ∈ w) : ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit N, C.gateCount=1 ∧
        exp (t • y) = z • (C.eval : Register N) := by
      obtain ⟨x,hx,c,rfl⟩ := hu y hy
      rw [Complex.coe_smul,smul_smul]
      exact hg x hx (t*c)
    obtain ⟨z,hz,C,hC,heval⟩ := compile_path_word_steps w t hphys
    rw [hword,heval,Complex.coe_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm |t| K,norm_sub_rev] at he
    exact ⟨z,hz,C,hC.trans_le hcount.le,he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one harg hsmall (by omega : p+1 ≤ p+2)) (by norm_num))⟩
  · have hU := exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem t (list_sum_mem_addSubgroup (skewAdjoint _) v hs))
    refine ⟨1,norm_one,TwoQubitCircuit.one N,Nat.zero_le _,?_⟩
    rw [one_smul,TwoQubitCircuit.one_eval]
    change ‖exp (t • v.sum)-(1:Register N)‖ ≤ 6*(K*|t|)^(p+1)
    have hbound := norm_sub_le (exp (t • v.sum)) (1:Register N)
    rw [CStarRing.norm_of_mem_unitary hU,norm_one] at hbound
    linarith only [hbound,one_le_pow₀ (le_of_not_ge hsmall : 1 ≤ K*|t|) (n := p+1)]

#print axioms short_word
end
end GaloisForLFunctions.HTGeometry.LocalPatches
