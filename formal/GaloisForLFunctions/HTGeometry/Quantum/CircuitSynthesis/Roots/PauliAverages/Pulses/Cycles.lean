import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Pulses.Product

/-! # Repeated sweeps of sampled brackets -/

open NormedSpace Finset
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
noncomputable section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

/-- For $N ≥ m^2$, $m$ sweeps approximate the exponential of the
normalized bracket sum to operator error $14/m$ up to time one. -/
theorem sweep_error (N m : ℕ) (hm : 0 < m) (hN : m^2 ≤ N) (X Y : Fin N → A)
    (hx : ∀ i, X i∈skewAdjoint A) (hn : ∀ i, ‖X i‖ ≤ 2) (hy : ∀ i, Y i∈unitary A)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hf : ∀ i, let b := Real.sqrt (t/(m*N))
      ‖Y i-(1+b^2 • X i)‖ ≤ 8*b^3) :
    ‖(List.ofFn Y).prod^m-exp (t • ((N:ℝ)⁻¹ • ∑ i, X i))‖ ≤ 14/m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (m:ℝ)^2 ≤ N := by exact_mod_cast hN
  have hN₁ : (1:ℝ) ≤ N := (one_le_pow₀ hm₁).trans hN'
  have hNp : (0:ℝ) < N := zero_lt_one.trans_le hN₁
  let b := Real.sqrt (t/(m*N))
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hsq : b^2=t/(m*N) := Real.sq_sqrt (by positivity)
  have htN : t ≤ (m:ℝ)*N := ht'.trans (one_le_mul_of_one_le_of_one_le hm₁ hN₁)
  have hb₁ : b ≤ 1 := by
    have h := (div_le_one (by positivity : (0:ℝ) < m*N)).2 htN
    nlinarith only [hsq,h,sq_nonneg (b-1)]
  have hbm : b ≤ (m:ℝ)⁻¹ := by
    have hd : t*m ≤ (N:ℝ) := calc
      _ ≤ (m:ℝ) := by simpa using mul_le_mul_of_nonneg_right ht' hm'.le
      _ ≤ _ := (by nlinarith only [mul_nonneg hm'.le (sub_nonneg.mpr hm₁)] : (m:ℝ) ≤ m^2).trans hN'
    have ht₂ : b^2 ≤ ((m:ℝ)⁻¹)^2 := by
      rw [hsq]
      field_simp
      exact hd
    by_contra! hl
    nlinarith only [ht₂,mul_self_lt_mul_self (inv_nonneg.mpr hm'.le) hl]
  let Z := List.ofFn X
  let T (i : Fin N) := exp (b^2 • X i)
  have hT (i) : T i∈unitary A := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem _ (hx i))
  have hZ (z : A) (hz : z∈Z) : z∈skewAdjoint A := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact hx i
  have hmass : (Z.map norm).sum ≤ 2*(N:ℝ) := by
    rw [show Z=List.ofFn X by rfl,List.map_ofFn,List.sum_ofFn]
    exact (sum_le_sum fun i _ => hn i).trans_eq (by simp [nsmul_eq_mul,mul_comm])
  have half := product_perturbation Y T hy hT (fun i => pulse_exponential _ _ (hx i) (hn i) hb hb₁ (hf i))
  have hpow := unitary_pow_norm_sub_pow_le (List.ofFn Y).prod (List.ofFn T).prod
    (Submonoid.list_prod_mem _ fun y hy' => (List.mem_ofFn.mp hy').elim (fun i hi => hi ▸ hy i))
    (Submonoid.list_prod_mem _ fun y hy' => (List.mem_ofFn.mp hy').elim (fun i hi => hi ▸ hT i)) m
  have he := list_lie_product_pow_mass_error Z hZ (t/N) m hm
  have heq : t/(N:ℝ)/m=b^2 := by rw [hsq]; ring
  have hs : (t/(N:ℝ)) • Z.sum=t • ((N:ℝ)⁻¹ • ∑ i, X i) := by
    simp only [Z,List.sum_ofFn,smul_smul,div_eq_mul_inv]
  rw [heq,hs,List.map_ofFn] at he
  have hmass₀ : 0 ≤ (Z.map norm).sum := (norm_nonneg _).trans (norm_list_sum_le Z)
  have htop : (Z.map norm).sum^2*|t/(N:ℝ)|^2/m ≤ 4/(m:ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (2*(N:ℝ))^2*(1/(N:ℝ))^2/m := by gcongr
      _ = _ := by field_simp; ring
  have hpulse : (m:ℝ)*(N*(10*b^3)) ≤ 10/(m:ℝ) := by
    have hid : (m:ℝ)*N*b^2=t := by rw [hsq]; field_simp
    calc
      _ = 10*t*b := by rw [←hid]; ring
      _ ≤ 10*1*((m:ℝ)⁻¹) := by gcongr
      _ = _ := by ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((List.ofFn T).prod^m) _).trans
    ((add_le_add (hpow.trans ((mul_le_mul_of_nonneg_left half hm'.le).trans hpulse))
      (he.trans htop)).trans_eq (by ring))

#print axioms sweep_error
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Pulses
