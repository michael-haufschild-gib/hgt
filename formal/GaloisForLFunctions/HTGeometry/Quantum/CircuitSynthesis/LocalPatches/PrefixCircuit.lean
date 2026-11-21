import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PatchLists
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord

/-! # Ancilla-free simulation by successive local corrections to the prefix flow -/
open NormedSpace Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
local instance (N : ℕ) : CStarAlgebra (Register N) where
local instance (N : ℕ) : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ _

/-- Local frequency scale controlling a patch of at most p+1 sites. -/
def patchScale (p : ℕ) (M : ℝ) : ℝ := 8^(p+1)*(1+((p:ℝ)+1)*M)

/-- Gate allowance for removing one old patch flow and inserting the enlarged one. -/
def patchGateCost (p m : ℕ) := 2*(3^p*((p+1)*m))

theorem approx_enlarge {N j k : ℕ} {e f : ℝ} {U : Register N}
    (h : HasProjectiveCircuitApproximation N e j U) (he : e ≤ f) (hj : j ≤ k) :
    HasProjectiveCircuitApproximation N f k U := by
  obtain ⟨z,hz,C,hC,he'⟩ := h
  exact ⟨z,hz,C,hC.trans hj,he'.trans he⟩

/-- One sweep over N sites has extensive cost. The error depends on the
mass of a single site and the order, independent of the full prefix norm. -/
theorem prefix_circuit {N : ℕ} (Z : ℕ → List (Register N)) (p m : ℕ) (M : ℝ)
    (hM : 0 ≤ M) (hm : ∀ i, (Z i).length ≤ m) (hsize : ∀ i, ProductFormula.mass (Z i) ≤ M)
    (hs : ∀ i x, x ∈ Z i → x ∈ skewAdjoint (Register N)) (hg : ∀ i x, x ∈ Z i → OneGateFlow x)
    (hcomm : ∀ i j, i+1 < j → Commute (Z i).sum (Z j).sum) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    HasProjectiveCircuitApproximation N ((n:ℝ)*(14*(patchScale p M*t)^(p+1)))
      (n*patchGateCost p m) (exp (t • intervalSum (fun i => (Z i).sum) 0 n)) := by
  let X := fun i => (Z i).sum
  let K := patchScale p M
  let E := (K*t)^(p+1)
  have hX i : X i ∈ skewAdjoint (Register N) := list_sum_mem_addSubgroup _ _ (hs i)
  have hKpos : 0 ≤ K := by dsimp [K,patchScale]; positivity
  have h8 : (2:ℝ) ≤ 8^(p+1) := by
    rw [pow_succ]
    linarith only [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 8) (n := p)]
  have hscale : 2*(1+((p:ℝ)+1)*M) ≤ K :=
    mul_le_mul_of_nonneg_right h8 (by positivity)
  have hPM : (p:ℝ)*M ≤ ((p:ℝ)+1)*M := by linarith only [hM]
  have hMs : M ≤ K := by nlinarith only [hscale,mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hM,hM]
  have h7 : (7:ℝ)^p ≤ 8^(p+1) := (pow_le_pow_left₀ (by norm_num) (by norm_num : (7:ℝ)≤8) p).trans
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))
  have compile (v : List (Register N)) (hv : ProductFormula.mass v ≤ ((p:ℝ)+1)*M)
      (hlen : v.length ≤ (p+1)*m) (hsv : ∀ x ∈ v, x ∈ skewAdjoint (Register N))
      (hgv : ∀ x ∈ v, OneGateFlow x) (s : ℝ) (hs' : |s|=t) :
      HasProjectiveCircuitApproximation N (6*E) (3^p*((p+1)*m)) (exp (s • v.sum)) := by
    apply approx_enlarge (short_word v p s hsv hgv) _ (Nat.mul_le_mul_left _ hlen)
    rw [hs']
    have h := mul_le_mul h7 (add_le_add le_rfl hv : 1+ProductFormula.mass v ≤ 1+((p:ℝ)+1)*M) (by have := ProductFormula.mass_nonneg v; positivity)
      (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by have := ProductFormula.mass_nonneg v; positivity) (mul_le_mul_of_nonneg_right h ht) _) (by norm_num)
  induction n with
  | zero =>
    refine ⟨1,norm_one,TwoQubitCircuit.one N,Nat.zero_le _,?_⟩
    simp [intervalSum,TwoQubitCircuit.one_eval]
  | succ i ih =>
    let a := intervalSum X 0 i
    let b := intervalSum X (i-p) i
    let v := patchList Z (i-p) i
    have hvsum : v.sum = b := sum_patchList Z _ _
    have hd : i-(i-p) ≤ p := by omega
    have hvlen : v.length ≤ p*m := (length_patchList_le Z hm _ _).trans (Nat.mul_le_mul_right m hd)
    have hvm : ProductFormula.mass v ≤ (p:ℝ)*M := (mass_patchList_le Z hsize _ _).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hM)
    have hvprop x (hx : x ∈ v) : x ∈ skewAdjoint (Register N) ∧ OneGateFlow x := by
      obtain ⟨j,_,hj⟩ := mem_patchList.mp hx
      exact ⟨hs _ _ hj,hg _ _ hj⟩
    have hprev := compile v (hvm.trans hPM) (hvlen.trans (Nat.mul_le_mul_right m (Nat.le_succ p)))
      (fun x hx => (hvprop x hx).1) (fun x hx => (hvprop x hx).2) (-t) (by simp [abs_of_nonneg ht])
    rw [hvsum,neg_smul,←smul_neg] at hprev
    have hnext := compile (v++Z i) (by rw [ProductFormula.mass_append]; linarith only [hvm,hsize i])
      (by rw [List.length_append,Nat.add_mul]; simpa using Nat.add_le_add hvlen (hm i))
      (fun x hx => (List.mem_append.mp hx).elim (fun hh => (hvprop x hh).1) (hs i x))
      (fun x hx => (List.mem_append.mp hx).elim (fun hh => (hvprop x hh).2) (hg i x))
      t (abs_of_nonneg ht)
    rw [List.sum_append,hvsum] at hnext
    have hb : b ∈ skewAdjoint (Register N) := (skewAdjoint _).sum_mem fun j _ => hX j
    have unit (y : Register N) (hy : y ∈ skewAdjoint (Register N)) :
        exp (t • y) ∈ unitary (Register N) := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hy)
    have hp := approx_product (unit (b+X i) ((skewAdjoint _).add_mem hb (hX i)))
      (approx_product (unit (-b) ((skewAdjoint _).neg_mem hb)) ih hprev) hnext
    obtain ⟨z,hz,C,hC,he⟩ := hp
    have hlocal := path_patch_error X hX hcomm i p t ht
    have hbnd : 2*‖b‖ ≤ K := by
      have hnb := norm_list_sum_le v
      rw [hvsum] at hnb
      change ‖b‖ ≤ ProductFormula.mass v at hnb
      linarith only [hnb,hvm,hscale,hPM]
    have hxi : ‖X i‖ ≤ K := (norm_list_sum_le (Z i)).trans ((hsize i).trans hMs)
    have hcut : ‖exp (t • a)*exp (t • (-b))*exp (t • (b+X i))-exp (t • (a+X i))‖ ≤ 2*E := by
      apply hlocal.trans
      calc
        _ ≤ 2*K^p*K*t^(p+1) := by gcongr
        _ = _ := by dsimp [E]; rw [mul_pow,pow_succ K p]; ring
    have hsum : intervalSum X 0 (i+1) = a+X i := by simp [intervalSum,a,sum_range_succ]
    refine ⟨z,hz,C,?_,?_⟩
    · rw [Nat.add_mul,one_mul]; dsimp [patchGateCost] at hC ⊢; omega
    · change ‖exp (t • intervalSum X 0 (i+1))-_‖ ≤ ((i+1:ℕ):ℝ)*(14*E)
      rw [hsum,Nat.cast_add,Nat.cast_one]
      have htri := norm_sub_le_norm_sub_add_norm_sub (exp (t • (a+X i)))
        (exp (t • a)*exp (t • (-b))*exp (t • (b+X i))) (z • (C.eval : Register N))
      rw [norm_sub_rev] at hcut
      change ‖exp (t • a)*exp (t • (-b))*exp (t • (b+X i))-_‖ ≤ (i:ℝ)*(14*E)+6*E+6*E at he
      linarith only [htri,hcut,he]

#print axioms prefix_circuit
end
end GaloisForLFunctions.HTGeometry.LocalPatches
