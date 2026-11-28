import GaloisForLFunctions.HTGeometry.CentralizerBudgetSplit
import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct

/-! # Accumulated error of bracket pulses in an ordered product -/

open NormedSpace
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
noncomputable section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

omit [Nontrivial A] in
private theorem zip_bound {n : ℕ} (a b : Fin n → A) {e : ℝ}
    (h : ∀ i, ‖a i-b i‖≤e) :
    (List.zipWith (fun x y => ‖x-y‖) (List.ofFn a) (List.ofFn b)).sum≤n*e := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [List.ofFn_succ,List.zipWith_cons_cons,List.sum_cons,Nat.cast_succ,add_mul,one_mul,
      add_comm ((n:ℝ)*e) e] using add_le_add (h 0) (ih _ _ (fun i => h i.succ))

/-- Every error propagates through unitary factors without amplification. -/
theorem product_perturbation {n : ℕ} (a b : Fin n → A)
    (ha : ∀ i, a i∈unitary A) (hb : ∀ i, b i∈unitary A) {e : ℝ} (h : ∀ i, ‖a i-b i‖≤e) :
    ‖(List.ofFn a).prod-(List.ofFn b).prod‖≤n*e := by
  have hu (f : Fin n → A) (hf : ∀ i, f i∈unitary A) (z : A) (hz : z∈List.ofFn f) : ‖z‖≤1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact (CStarRing.norm_of_mem_unitary (hf i)).le
  exact (norm_listProd_sub_le _ _ (hu a ha) (hu b hb) (by simp)).trans (zip_bound a b h)

/-- A pulse within $8b^3$ of the bracket tangent is within $10b^3$
of its exponential for $0≤b≤1$ and bracket norm at most two. -/
theorem pulse_exponential (X Y : A) (hx : X∈skewAdjoint A) (hn : ‖X‖≤2)
    {b : ℝ} (hb : 0≤b) (hb' : b≤1) (he : ‖Y-(1+b^2 • X)‖≤8*b^3) :
    ‖Y-exp (b^2 • X)‖≤10*b^3 := by
  have ht : ‖exp (b^2 • X)-(1+b^2 • X)‖≤‖X‖^2*(b^2)^2/2 := by
    simpa [cstarExponentialTaylor_one,abs_of_nonneg (sq_nonneg b)] using
      norm_exp_sub_cstarExponentialTaylor_le X hx 1 (b^2)
  have h := norm_sub_le_norm_sub_add_norm_sub Y (1+b^2 • X) (exp (b^2 • X))
  rw [norm_sub_rev (1+b^2 • X)] at h
  have hh : ‖X‖^2*(b^2)^2≤(2:ℝ)^2*(b^2)^2 := by gcongr
  nlinarith only [ht,h,he,hh,mul_nonneg (pow_nonneg hb 3) (sub_nonneg.mpr hb')]

#print axioms pulse_exponential
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
