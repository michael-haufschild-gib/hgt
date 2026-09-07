import GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens

/-!
# Full omitted-floor hyperbola and harmonic quotient-depth cost

Reverse the actual finite divisor sums before estimating Mertens increments.
The depth loss is harmonic, and the complete infinite energy tail is retained.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionQuotientTail
open DeletionMobiusPrimitive

/-- Exact finite hyperbola reversal for arbitrary signed coefficients. -/
theorem truncated_floor_hyperbola (f : ℕ → ℝ) (N n : ℕ) :
    (∑ m ∈ Finset.Ioc N n, f m*((n/m : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (n/(N+1)), ∑ m ∈ Finset.Ioc N (n/j), f m := by
  have hrow (m : ℕ) (hm : m ∈ Finset.Ioc N n) :
      f m*((n/m : ℕ) : ℝ) =
        ∑ j ∈ Finset.Icc 1 (n/(N+1)), if j ≤ n/m then f m else 0 := by
    have hmlo := (Finset.mem_Ioc.mp hm).1
    have hbound : n/m ≤ n/(N+1) := Nat.div_le_div_left (by omega) (by omega)
    have hset : (Finset.Icc 1 (n/(N+1))).filter (fun j => j ≤ n/m) = Finset.Icc 1 (n/m) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter,hset]
    simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hrow,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hj1,hjcap⟩ := Finset.mem_Icc.mp hj
  have hset : (Finset.Ioc N n).filter (fun m => j ≤ n/m) = Finset.Ioc N (n/j) := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hNm,hmn⟩,hdiv⟩
      refine ⟨hNm,(Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hdiv
      simpa only [Nat.mul_comm] using h
    · rintro ⟨hNm,hmdiv⟩
      refine ⟨⟨hNm,hmdiv.trans (Nat.div_le_self n j)⟩,?_⟩
      apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < j)).mp hmdiv
      simpa only [Nat.mul_comm] using h
  rw [← Finset.sum_filter,hset]

/-- Every coordinate of the omitted residual retains all active Mertens quotient increments. -/
theorem floorResidual_eq_quotient_mertens (N n : ℕ) (hn : 1 ≤ n) :
    bdMobiusFloorResidual N n = ∑ j ∈ Finset.Icc 1 (n/(N+1)),
      (Sieve.mertensM (n/j)-Sieve.mertensM N) := by
  by_cases hnN : n ≤ N
  · rw [bdMobiusFloorResidual_eq_zero N n hn hnN,Nat.div_eq_of_lt (by omega)]
    simp
  rw [bdMobiusFloorResidual_eq_sum_Ioc N n hn (by omega),truncated_floor_hyperbola]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hj1,hjcap⟩ := Finset.mem_Icc.mp hj
  have hNdiv : N ≤ n/j := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < j)).mpr
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < N+1)).mp hjcap
    nlinarith
  rw [show Finset.Ioc N (n/j) = Finset.Ico (N+1) (n/j+1) by ext m; simp,
    Finset.sum_Ico_eq_sub _ (by omega)]
  rfl

/-- The global source error keeps the exact cutoff counterterm and every quotient scale. -/
theorem error_eq_quotient_sum (N n : ℕ) (hn : 1 ≤ n) :
    1-bdMobiusModularApproximant N n = (n : ℝ)*deningerHarmonicPartial N -
      ((n/(N+1) : ℕ) : ℝ)*Sieve.mertensM N +
      ∑ j ∈ Finset.Icc 1 (n/(N+1)), Sieve.mertensM (n/j) := by
  rw [one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual,
    floorResidual_eq_quotient_mertens N n hn,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  ring

private theorem harmonic_cast_eq (L : ℕ) :
    (harmonic L : ℝ) = ∑ j ∈ Finset.Icc 1 L, 1/(j : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- Exact active quotient depth costs a harmonic sum, rather than its full cardinality. -/
theorem floorResidual_le_harmonic {N n : ℕ} {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 1 ≤ n)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    |bdMobiusFloorResidual N n| ≤ eps*(n : ℝ)*(1+(harmonic (n/(N+1)) : ℝ)) := by
  let J := n/(N+1)
  rw [floorResidual_eq_quotient_mertens N n hn]
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 J) :
      |Sieve.mertensM (n/j)-Sieve.mertensM N| ≤ eps*(n : ℝ)/(j : ℝ)+eps*(N : ℝ) := by
    obtain ⟨hj1,hjJ⟩ := Finset.mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hNdiv : N ≤ n/j := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < j)).mpr
      have h := (Nat.le_div_iff_mul_le (by omega : 0 < N+1)).mp hjJ
      nlinarith
    calc _ ≤ |Sieve.mertensM (n/j)|+|Sieve.mertensM N| := abs_sub _ _
         _ ≤ eps*((n/j : ℕ) : ℝ)+eps*(N : ℝ) := add_le_add (hM _ hNdiv) (hM _ le_rfl)
         _ ≤ _ := by
           apply add_le_add _ le_rfl
           simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
             (Nat.cast_div_le (α := ℝ) (m := n) (n := j)) heps
  have hJ : (N : ℝ)*(J : ℝ) ≤ n := by
    have h := Nat.div_mul_le_self n (N+1)
    have hnat : N*J ≤ n := by dsimp [J]; nlinarith
    exact_mod_cast hnat
  calc _ ≤ ∑ j ∈ Finset.Icc 1 J, |Sieve.mertensM (n/j)-Sieve.mertensM N| :=
         Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ j ∈ Finset.Icc 1 J, (eps*(n : ℝ)/(j : ℝ)+eps*(N : ℝ)) := Finset.sum_le_sum hterm
       _ = eps*(n : ℝ)*(harmonic J : ℝ)+eps*(N : ℝ)*(J : ℝ) := by
         rw [harmonic_cast_eq,Finset.sum_add_distrib,Finset.mul_sum]
         simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
         have he : (∑ j ∈ Finset.Icc 1 J, eps*(n : ℝ)/(j : ℝ)) =
             ∑ j ∈ Finset.Icc 1 J, eps*(n : ℝ)*(1/(j : ℝ)) := by
           apply Finset.sum_congr rfl
           intro j hj
           ring
         rw [he]
         ring
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hJ heps]

private theorem harmonic_cast_mono {J L : ℕ} (hJL : J ≤ L) :
    (harmonic J : ℝ) ≤ (harmonic L : ℝ) := by
  rw [harmonic_cast_eq,harmonic_cast_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj hnot
    positivity

/-- A multiplicatively extended prefix pays only harmonic quotient-depth cost. -/
theorem floorResidual_le_of_depth {N L n : ℕ} {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 1 ≤ n) (hcap : n ≤ N*L)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    |bdMobiusFloorResidual N n| ≤ eps*(n : ℝ)*(1+(harmonic L : ℝ)) := by
  have hJ : n/(N+1) ≤ L := by
    have h := Nat.div_mul_le_self n (N+1)
    nlinarith
  exact (floorResidual_le_harmonic heps hn hM).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (harmonic_cast_mono hJ)) (by positivity))

/-- The complete primitive inherits the improved signed quotient estimate. -/
theorem primitive_extended_prefix_le {N L n : ℕ} {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 1 ≤ n) (hcap : n ≤ N*L)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    ‖primitive N n‖ ≤ 1+(n : ℝ)*(|deningerHarmonicPartial N|+eps*(1+(harmonic L : ℝ))) := by
  rw [primitive_eq_modular,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  have hr := floorResidual_le_of_depth heps hn hcap hM
  have hid := one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual N n
  have he : bdMobiusModularApproximant N n =
      1-((n : ℝ)*deningerHarmonicPartial N+bdMobiusFloorResidual N n) := by linarith
  rw [he]
  calc _ ≤ |(1 : ℝ)|+|(n : ℝ)*deningerHarmonicPartial N+bdMobiusFloorResidual N n| := abs_sub _ _
       _ ≤ 1+((n : ℝ)*|deningerHarmonicPartial N|+|bdMobiusFloorResidual N n|) := by
         simp only [abs_one]
         apply add_le_add le_rfl
         simpa only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] using
           abs_add_le ((n : ℝ)*deningerHarmonicPartial N) (bdMobiusFloorResidual N n)
       _ ≤ _ := by nlinarith

/-- Full source energy with harmonic depth cost and the entire infinite tail retained. -/
theorem primitiveEnergy_le_harmonic_depth {N L : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*
      (|deningerHarmonicPartial N|+eps*(1+(harmonic L : ℝ)))^2+(N : ℝ)/(L : ℝ) := by
  have h := DeletionMobiusGlobal.primitiveEnergy_le_of_extended_prefix (N := N) (T := N*L)
    (b := |deningerHarmonicPartial N|+eps*(1+(harmonic L : ℝ)))
    (by nlinarith : 1 ≤ N*L)
    (fun n hn hcap => primitive_extended_prefix_le heps hn hcap hM)
  calc primitiveEnergy N ≤ _ := h
       _ = _ := by
         have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
         have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
         push_cast
         field_simp

/-- An explicit logarithmic-depth version of the full infinite energy estimate. -/
theorem primitiveEnergy_le_log_depth {N L : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*
      (|deningerHarmonicPartial N|+eps*(2+Real.log (L : ℝ)))^2+(N : ℝ)/(L : ℝ) := by
  have hh : 0 ≤ (harmonic L : ℝ) := by rw [harmonic_cast_eq]; exact Finset.sum_nonneg (fun j _ => by positivity)
  have hcost : |deningerHarmonicPartial N|+eps*(1+(harmonic L : ℝ)) ≤
      |deningerHarmonicPartial N|+eps*(2+Real.log (L : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) heps]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ |deningerHarmonicPartial N|+eps*(1+(harmonic L : ℝ))) hcost 2
  exact (primitiveEnergy_le_harmonic_depth hN hL heps hM).trans
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (by positivity))) le_rfl)

/-- The same sharpened complete bound applies to the actual modular Hilbert source. -/
theorem modular_norm_sq_le_log_depth {N L : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    ‖bdMobiusModularApproximantVec N‖^2 ≤ 4+2*(N : ℝ)*(L : ℝ)*
      (|deningerHarmonicPartial N|+eps*(2+Real.log (L : ℝ)))^2+(N : ℝ)/(L : ℝ) :=
  (DeletionMobiusGlobal.modular_norm_sq_le_primitiveEnergy N).trans
    (primitiveEnergy_le_log_depth hN hL heps hM)

/-- The corpus's unconditional Mertens saving supplies one estimate valid at every tail depth. -/
theorem exists_primitiveEnergy_uniform_log_depth_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, 1 ≤ L →
      primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*
        (|deningerHarmonicPartial N|+B*deningerMertensSaving (N : ℝ)*(2+Real.log (L : ℝ)))^2+
          (N : ℝ)/(L : ℝ) := by
  obtain ⟨B,hB,hrate⟩ := deningerMertensM_rate
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hrate
  refine ⟨B,hB,?_⟩
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 2] with N hNK hN2
  intro L hL
  apply primitiveEnergy_le_log_depth (by omega) hL
    (mul_nonneg hB (deningerMertensSaving_pos (N : ℝ)).le)
  intro k hNk
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hNkR : (N : ℝ) ≤ k := by exact_mod_cast hNk
  have hsave : deningerMertensSaving (k : ℝ) ≤ deningerMertensSaving (N : ℝ) := by
    unfold deningerMertensSaving
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow (Real.log_nonneg hN1.le)
      (Real.log_le_log hN0 hNkR) (show (0 : ℝ) ≤ 1/3 by norm_num)
    linarith
  calc |Sieve.mertensM k| ≤ B*(k : ℝ)*deningerMertensSaving (k : ℝ) := hK k (by omega)
       _ ≤ B*(k : ℝ)*deningerMertensSaving (N : ℝ) :=
         mul_le_mul_of_nonneg_left hsave (by positivity)
       _ = _ := by ring

end RHTower.DeletionQuotientTail
end
