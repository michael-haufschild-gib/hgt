import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.AllOrders
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.LocalError
import GaloisForLFunctions.HTGeometry.QuantitativeLieProductFormula

/-! # Arbitrary-order unitary simulation at fixed operator-norm error -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.ProductFormula
noncomputable section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

private theorem budget_error (j : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    q^(j+2)*(6*(1/(100*q))^(j+2)) ≤ 1/100 := by
  have hq' : 0 < q := by linarith only [hq]
  calc
    _ = 6*(1/100:ℝ)^(j+2) := by
      rw [mul_left_comm,← mul_pow]
      congr 2
      field_simp
    _ ≤ 6*(1/100:ℝ)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ _ := by norm_num

/-- With q^(j+2) repetitions, the time radius grows as q^(j+1).
The word is independent of the requested real time. -/
theorem exists_repeated_word (inputs : List A) (hi : ∀ x ∈ inputs, x ∈ skewAdjoint A) (j : ℕ) :
    ∃ w : List A, Uses w inputs ∧ w.length=3^j*inputs.length ∧
    ∀ (q : ℕ) (t : ℝ), 0 < q → 7^j*(1+mass inputs)*|t| ≤ (q:ℝ)^(j+1)/100 →
      ‖(w.map fun y => exp ((t/((q:ℝ)^(j+2))) • y)).prod^(q^(j+2)) -
        exp (t • inputs.sum)‖ ≤ 1/100 := by
  obtain ⟨w,hw,hu,hlen,hm⟩ := exists_word inputs j
  refine ⟨w,hu,hlen,?_⟩
  intro q t hq ht
  let K : ℝ := 7^j*(1+mass inputs)
  let r := q^(j+2)
  let h := t/(r:ℝ)
  have hr : (r:ℝ) = (q:ℝ)^(j+2) := by simp [r]
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0:ℝ) < q := by positivity
  have hr' : (0:ℝ) < r := by rw [hr]; positivity
  have hMass := mass_nonneg inputs
  have hK : 0 < K := by dsimp [K]; positivity
  have hwm : mass w ≤ K := hm.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hxm : ‖inputs.sum‖ ≤ K := by
    apply (norm_list_sum_le inputs).trans
    change mass inputs ≤ 7^j*(1+mass inputs)
    exact le_trans (by linarith : mass inputs ≤ 1+mass inputs)
      (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))
  have hs : ‖(h:ℂ)‖*K ≤ 1/(100*(q:ℝ)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hr',hr]
    rw [div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by positivity)]
    have hqpow : (q:ℝ)^(j+2)=(q:ℝ)^(j+1)*q := pow_succ _ _
    rw [hqpow,one_mul]
    have ht' : |t| * K*100 ≤ (q:ℝ)^(j+1) := (le_div_iff₀ (by norm_num)).mp (by rw [mul_comm]; exact ht)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ht' hqp.le
  have hs1 : ‖(h:ℂ)‖*K ≤ 1 := hs.trans ((div_le_one (by positivity)).mpr (by linarith))
  have he := contact_error hw hK hwm hxm hs1
  have hreal : word w (h:ℂ) = (w.map fun y => exp (h • y)).prod := by simp [word]
  rw [hreal,Complex.coe_smul] at he
  have hskew : ∀ y ∈ w, y ∈ skewAdjoint A := by
    intro y hy
    obtain ⟨x,hx,c,rfl⟩ := hu y hy
    rw [Complex.coe_smul]
    exact skewAdjoint.smul_mem c (hi x hx)
  have hU := list_exp_product_mem_unitary w hskew h
  have hV := exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem h (list_sum_mem_addSubgroup (skewAdjoint A) inputs hi))
  have hpow : (exp (h • inputs.sum))^r = exp (t • inputs.sum) := by
    rw [exp_real_smul_pow]; congr 2; dsimp [h]; field_simp
  have htel := unitary_pow_norm_sub_pow_le _ _ hU hV r
  rw [hpow] at htel
  change ‖(w.map fun y => exp ((t/(q:ℝ)^(j+2)) • y)).prod^r - _‖ ≤ _
  rw [← hr]
  apply htel.trans
  calc
    _ ≤ (r:ℝ)*(6*(1/(100*(q:ℝ)))^(j+2)) := by
      apply mul_le_mul_of_nonneg_left (he.trans _) hr'.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hK.le) hs _) (by norm_num)
    _ ≤ _ := by rw [hr]; exact budget_error j q hq'

#print axioms exists_repeated_word
end
end GaloisForLFunctions.HTGeometry.ProductFormula
