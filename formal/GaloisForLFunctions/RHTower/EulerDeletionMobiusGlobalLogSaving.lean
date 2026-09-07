import GaloisForLFunctions.RHTower.EulerDeletionMobiusGramCancellation

/-!
# Full arithmetic energy from Mertens cancellation on an extended prefix

Finite Abel summation controls the entire omitted floor sum. An independent
inverse-square tail estimate then gives a bound for the complete primitive energy.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionMobiusGlobal
open DeletionMobiusPrimitive

private theorem abs_sum_mul_antitone_le (a w : ℕ → ℝ) (L : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ k, 0 ≤ w k) (hanti : Antitone w)
    (hprefix : ∀ K ≤ L, |∑ i ∈ Finset.range K, a i| ≤ B) :
    |∑ i ∈ Finset.range L, w i * a i| ≤ B * w 0 := by
  by_cases hL : L = 0
  · subst L
    simpa using mul_nonneg hB (hw 0)
  let P (K : ℕ) := ∑ i ∈ Finset.range K, a i
  have he : (∑ i ∈ Finset.range L, w i * a i) =
      w (L-1)*P L + ∑ i ∈ Finset.range (L-1), (w i-w (i+1))*P (i+1) := by
    have h := Finset.sum_range_by_parts w a L
    simp only [smul_eq_mul] at h
    rw [h]
    simp only [sub_mul, Finset.sum_sub_distrib, P]
    ring
  rw [he]
  calc _ ≤ |w (L-1)*P L| + ∑ i ∈ Finset.range (L-1), |(w i-w (i+1))*P (i+1)| :=
         (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
       _ ≤ w (L-1)*B + ∑ i ∈ Finset.range (L-1), (w i-w (i+1))*B := by
         apply add_le_add
         · rw [abs_mul, abs_of_nonneg (hw _)]
           exact mul_le_mul_of_nonneg_left (hprefix L le_rfl) (hw _)
         · apply Finset.sum_le_sum
           intro i hi
           have hd : 0 ≤ w i-w (i+1) := sub_nonneg.mpr (hanti (by omega))
           rw [abs_mul, abs_of_nonneg hd]
           exact mul_le_mul_of_nonneg_left (hprefix (i+1) (by simp only [Finset.mem_range] at hi; omega)) hd
       _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub']; ring

private theorem mertens_succ (k : ℕ) :
    Sieve.mertensM (k+1) = Sieve.mertensM k + ((moebius (k+1) : ℤ) : ℝ) := by
  exact Finset.sum_range_succ _ (k+1)

private theorem shifted_mertens_prefix (N K : ℕ) :
    (∑ i ∈ Finset.range K, ((moebius (N+i+1) : ℤ) : ℝ)) =
      Sieve.mertensM (N+K)-Sieve.mertensM N := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show N+(K+1) = (N+K)+1 by omega, mertens_succ]
    ring

/-- The complete omitted floor sum is controlled by Mertens cancellation on its actual interval. -/
theorem floorResidual_le_of_mertens {N L n : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps) (hn : 1 ≤ n) (hcap : n ≤ N*L)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    |bdMobiusFloorResidual N n| ≤ 2*eps*(n : ℝ)*(L : ℝ) := by
  by_cases hsmall : n ≤ N
  · rw [bdMobiusFloorResidual_eq_zero N n hn hsmall, abs_zero]
    positivity
  have hNn : N ≤ n := by omega
  rw [bdMobiusFloorResidual_eq_sum_Ioc N n hn hNn]
  let a (i : ℕ) : ℝ := ((moebius (N+i+1) : ℤ) : ℝ)
  let w (i : ℕ) : ℝ := (n/(N+i+1) : ℕ)
  have heq : (∑ m ∈ Finset.Ioc N n, ((moebius m : ℤ) : ℝ)*((n/m : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range (n-N), w i*a i := by
    rw [show Finset.Ioc N n = Finset.Ico (N+1) (n+1) by ext k; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right]
    apply Finset.sum_congr rfl
    intro i hi
    simp [a, w, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm]
  rw [heq]
  have hpref (K : ℕ) (hK : K ≤ n-N) : |∑ i ∈ Finset.range K, a i| ≤ 2*eps*(n : ℝ) := by
    change |∑ i ∈ Finset.range K, ((moebius (N+i+1) : ℤ) : ℝ)| ≤ _
    rw [shifted_mertens_prefix]
    have hNK : N+K ≤ n := by omega
    calc _ ≤ |Sieve.mertensM (N+K)|+|Sieve.mertensM N| := abs_sub _ _
         _ ≤ eps*((N+K : ℕ) : ℝ)+eps*(N : ℝ) := add_le_add (hM _ (by omega)) (hM _ le_rfl)
         _ ≤ _ := by
           have h1 := mul_le_mul_of_nonneg_left (show ((N+K : ℕ) : ℝ) ≤ n by exact_mod_cast hNK) heps
           have h2 := mul_le_mul_of_nonneg_left (show (N : ℝ) ≤ n by exact_mod_cast hNn) heps
           linarith
  have hw (i : ℕ) : 0 ≤ w i := Nat.cast_nonneg _
  have ha : Antitone w := by
    intro i j hij
    change ((n/(N+j+1) : ℕ) : ℝ) ≤ ((n/(N+i+1) : ℕ) : ℝ)
    have hdiv : n/(N+j+1) ≤ n/(N+i+1) :=
      Nat.div_le_div_left (by omega : N+i+1 ≤ N+j+1) (by omega : 0 < N+i+1)
    exact_mod_cast hdiv
  have hw0 : w 0 ≤ (L : ℝ) := by
    change ((n/(N+0+1) : ℕ) : ℝ) ≤ _
    exact_mod_cast Nat.div_le_of_le_mul (by nlinarith : n ≤ (N+0+1)*L)
  exact (abs_sum_mul_antitone_le a w (n-N) (by positivity) hw ha hpref).trans
    (mul_le_mul_of_nonneg_left hw0 (by positivity))

/-- The full arithmetic primitive is small on a multiplicatively extended prefix, including
all coordinates beyond the original channel cutoff. -/
theorem primitive_extended_prefix_le {N L n : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps) (hn : 1 ≤ n) (hcap : n ≤ N*L)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    ‖primitive N n‖ ≤ 1+(n : ℝ)*(|deningerHarmonicPartial N|+2*eps*(L : ℝ)) := by
  rw [primitive_eq_modular, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hr := floorResidual_le_of_mertens hN hL heps hn hcap hM
  have hid := one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual N n
  have he : bdMobiusModularApproximant N n =
      1-((n : ℝ)*deningerHarmonicPartial N+bdMobiusFloorResidual N n) := by linarith
  rw [he]
  calc _ ≤ |(1 : ℝ)|+|(n : ℝ)*deningerHarmonicPartial N+bdMobiusFloorResidual N n| := abs_sub _ _
       _ ≤ 1+((n : ℝ)*|deningerHarmonicPartial N|+|bdMobiusFloorResidual N n|) := by
         simp only [abs_one]
         apply add_le_add le_rfl
         simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] using
           abs_add_le ((n : ℝ)*deningerHarmonicPartial N) (bdMobiusFloorResidual N n)
       _ ≤ _ := by nlinarith

private theorem sum_inv_sq_head_le (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (1 : ℝ)/(n : ℝ)^2) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (T+1)
  have he : Finset.Ioo 0 (T+1) = Finset.Icc 1 T := by ext n; simp; omega
  simpa only [he, Nat.cast_zero, zero_add, div_one, one_div] using h

/-- A finite coordinate bound and the literal uniform primitive bound control the complete
infinite arithmetic energy, with an explicit complementary-tail cost. -/
theorem primitiveEnergy_le_of_extended_prefix {N T : ℕ} {b : ℝ}
    (hT : 1 ≤ T)
    (hprefix : ∀ n, 1 ≤ n → n ≤ T → ‖primitive N n‖ ≤ 1+(n : ℝ)*b) :
    primitiveEnergy N ≤ 4+2*(T : ℝ)*b^2+(N : ℝ)^2/(T : ℝ) := by
  let f (n : ℕ) : ℝ := ‖primitive N n‖^2/(n : ℝ)^2
  have hf (n : ℕ) : 0 ≤ f n := by unfold f; positivity
  have hfirst (n : ℕ) (hn : n ∈ Finset.Icc 1 T) :
      f n ≤ 2/(n : ℝ)^2+2*b^2 := by
    obtain ⟨hn1,hnT⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h := hprefix n hn1 hnT
    have hs : ‖primitive N n‖^2 ≤ (1+(n : ℝ)*b)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    unfold f
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    have he : (2/(n : ℝ)^2+2*b^2)*(n : ℝ)^2 = 2+2*((n : ℝ)*b)^2 := by field_simp
    rw [he]
    nlinarith [sq_nonneg ((n : ℝ)*b-1)]
  have hhead : ∑ n ∈ Finset.Icc 1 T, f n ≤ 4+2*(T : ℝ)*b^2 := by
    calc _ ≤ ∑ n ∈ Finset.Icc 1 T, (2/(n : ℝ)^2+2*b^2) := Finset.sum_le_sum hfirst
         _ = 2*(∑ n ∈ Finset.Icc 1 T, (1 : ℝ)/(n : ℝ)^2)+2*(T : ℝ)*b^2 := by
           simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum,
             Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
           ring
         _ ≤ _ := by linarith [sum_inv_sq_head_le T]
  have htail (K : ℕ) : ∑ n ∈ Finset.Ioc T (K+T), f n ≤ (N : ℝ)^2/(T : ℝ) := by
    have hbound (n : ℕ) : f n ≤ (N : ℝ)^2*((n : ℝ)^2)⁻¹ := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_primitive_le N n) 2
      exact (div_le_div_of_nonneg_right h (sq_nonneg (n : ℝ))).trans_eq (div_eq_mul_inv _ _)
    calc _ ≤ ∑ n ∈ Finset.Ioc T (K+T), (N : ℝ)^2*((n : ℝ)^2)⁻¹ := Finset.sum_le_sum (fun n _ => hbound n)
         _ = (N : ℝ)^2*∑ n ∈ Finset.Ioc T (K+T), ((n : ℝ)^2)⁻¹ := (Finset.mul_sum _ _ _).symm
         _ ≤ (N : ℝ)^2*((T : ℝ)⁻¹-((K+T : ℕ) : ℝ)⁻¹) :=
           mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : T ≠ 0) (by omega : T ≤ K+T)) (sq_nonneg _)
         _ ≤ _ := by
           rw [div_eq_mul_inv]
           exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (sq_nonneg _)
  have hfinite (K : ℕ) : ∑ n ∈ Finset.Icc 1 K, f n ≤ 4+2*(T : ℝ)*b^2+(N : ℝ)^2/(T : ℝ) := by
    have hu : Finset.Icc 1 T ∪ Finset.Ioc T (K+T) = Finset.Icc 1 (K+T) := by ext n; simp; omega
    have hd : Disjoint (Finset.Icc 1 T) (Finset.Ioc T (K+T)) := by
      simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    calc _ ≤ ∑ n ∈ Finset.Icc 1 (K+T), f n :=
           Finset.sum_le_sum_of_subset_of_nonneg
             (by intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega) (fun n _ _ => hf n)
         _ = (∑ n ∈ Finset.Icc 1 T, f n)+∑ n ∈ Finset.Ioc T (K+T), f n := by rw [← hu, Finset.sum_union hd]
         _ ≤ _ := add_le_add hhead (htail K)
  have hshift (K : ℕ) : (∑ i ∈ Finset.range K, normalizedPrimitive N i^2) = ∑ n ∈ Finset.Icc 1 K, f n := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
      simp [normalizedPrimitive, f, div_pow]
  apply le_of_tendsto (summable_normalizedPrimitive_sq N).hasSum.tendsto_sum_nat
  exact Eventually.of_forall (fun K => by rw [hshift]; exact hfinite K)

/-- Full-source Mertens-to-energy estimate. The tail remains present with cost N/L. -/
theorem primitiveEnergy_le_of_mertens {N L : ℕ} {eps : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (heps : 0 ≤ eps)
    (hM : ∀ k, N ≤ k → |Sieve.mertensM k| ≤ eps*(k : ℝ)) :
    primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*
      (|deningerHarmonicPartial N|+2*eps*(L : ℝ))^2+(N : ℝ)/(L : ℝ) := by
  have h := primitiveEnergy_le_of_extended_prefix (N := N) (T := N*L)
    (b := |deningerHarmonicPartial N|+2*eps*(L : ℝ))
    (by nlinarith : 1 ≤ N*L)
    (fun n hn hcap => primitive_extended_prefix_le hN hL heps hn hcap hM)
  calc primitiveEnergy N ≤ _ := h
       _ = _ := by
         have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
         have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
         push_cast
         field_simp

/-- The existing modular carrier norm is bounded by the same complete arithmetic energy. -/
theorem modular_norm_sq_le_primitiveEnergy (N : ℕ) :
    ‖bdMobiusModularApproximantVec N‖^2 ≤ primitiveEnergy N := by
  have hg := hasSum_stepGram (abs_bdMobiusModularApproximant_le N) (abs_bdMobiusModularApproximant_le N)
  have hGram : stepGram (bdMobiusModularApproximant N) (bdMobiusModularApproximant N)=
      ‖bdMobiusModularApproximantVec N‖^2 := by
    have hi : (RCLike.re (inner ℂ (bdMobiusModularApproximantVec N)
        (bdMobiusModularApproximantVec N)) : ℝ)=‖bdMobiusModularApproximantVec N‖^2 := inner_self_eq_norm_sq _
    rw [bdMobiusModularApproximantVec,inner_stepVec] at hi
    exact hi
  have hterm (n : ℕ) : bdMobiusModularApproximant N (n+1)*bdMobiusModularApproximant N (n+1)/
        (((n : ℝ)+1)*((n : ℝ)+2)) ≤ normalizedPrimitive N n^2 := by
    rw [normalizedPrimitive, primitive_eq_modular, norm_neg, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (sq_nonneg (bdMobiusModularApproximant N (n+1))) (show 0 ≤ (n : ℝ)+1 by positivity)]
  rw [← hGram, ← hg.tsum_eq]
  exact Summable.tsum_le_tsum hterm hg.summable (summable_normalizedPrimitive_sq N)

private theorem log_tendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem log_pow_le_nat_eventually (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ)^r ≤ (N : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (burnolEventually_log_pow_le_rpow (δ := 1) (by norm_num) r)
  simpa only [Real.rpow_one] using h

/-- Unconditional arbitrary logarithmic saving for the full arithmetic energy relative to N.
The exponent q+1 is positive; the complete tail is included. -/
theorem primitiveEnergy_log_saving (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      primitiveEnergy N ≤ B*(N : ℝ)/Real.log (N : ℝ)^(q+1) := by
  let r := q+1
  obtain ⟨C,hC,hMrate⟩ := Sieve.deningerMertensM_log_pow_rate (2*r)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hMrate
  have hHlim := (Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero (2*r)).norm
  have hH : ∀ᶠ N : ℕ in atTop, |Real.log (N : ℝ)^(2*r)*deningerHarmonicPartial N| ≤ 1 := by
    have h := hHlim.eventually (eventually_lt_nhds (show ‖(0 : ℝ)‖ < (1 : ℝ) by norm_num))
    filter_upwards [h] with N hN
    exact (show |Real.log (N : ℝ)^(2*r)*deningerHarmonicPartial N| < 1 from hN).le
  refine ⟨6+2*(1+2*C)^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 1,
    log_tendsto.eventually_ge_atTop 2, log_pow_le_nat_eventually r, hH] with N hKN hN hlog hPN hHN
  let P : ℝ := Real.log (N : ℝ)^r
  let L : ℕ := ⌊P⌋₊
  let eps : ℝ := C/P^2
  let b : ℝ := |deningerHarmonicPartial N|+2*eps*(L : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by linarith
  have hP : 2 ≤ P := by
    have hq := one_le_pow₀ hlog1 (n := q)
    dsimp [P,r]
    rw [pow_succ]
    nlinarith
  have hP0 : 0 < P := by linarith
  have hP2 : Real.log (N : ℝ)^(2*r) = P^2 := by
    dsimp [P]
    rw [Nat.mul_comm 2 r, pow_mul]
  have hLP : (L : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hPL : P < (L : ℝ)+1 := Nat.lt_floor_add_one P
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hhalf : P/2 ≤ (L : ℝ) := by linarith
  have heps : 0 ≤ eps := div_nonneg hC (sq_nonneg P)
  have hM (k : ℕ) (hk : N ≤ k) : |Sieve.mertensM k| ≤ eps*(k : ℝ) := by
    have hpow : P^2 ≤ Real.log (k : ℝ)^(2*r) := by
      rw [← hP2]
      exact pow_le_pow_left₀ hlog0.le (Real.log_le_log hN0 (by exact_mod_cast hk)) _
    calc _ ≤ C*(k : ℝ)/Real.log (k : ℝ)^(2*r) := hK k (hKN.trans hk)
         _ ≤ C*(k : ℝ)/P^2 := div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg k)) (sq_pos_of_pos hP0) hpow
         _ = _ := by dsimp [eps]; ring
  have hHN' : |deningerHarmonicPartial N| ≤ 1/P^2 := by
    rw [hP2, abs_mul, abs_of_nonneg (sq_nonneg P)] at hHN
    apply (le_div_iff₀ (sq_pos_of_pos hP0)).mpr
    simpa only [mul_comm] using hHN
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbP : b ≤ (1+2*C)/P := by
    calc b ≤ 1/P^2+2*(C/P^2)*P :=
           add_le_add hHN' (mul_le_mul_of_nonneg_left hLP (by positivity))
         _ = 1/P^2+(2*C)/P := by field_simp
         _ ≤ 1/P+(2*C)/P := by
           apply add_le_add _ le_rfl
           apply (div_le_div_iff₀ (sq_pos_of_pos hP0) hP0).mpr
           nlinarith
         _ = _ := by ring
  have henergy := primitiveEnergy_le_of_mertens hN hL1 heps hM
  change primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*b^2+(N : ℝ)/(L : ℝ) at henergy
  have hhead : 2*(N : ℝ)*(L : ℝ)*b^2 ≤ 2*(1+2*C)^2*(N : ℝ)/P := by
    have hsq := pow_le_pow_left₀ hb hbP 2
    calc _ = (2*(N : ℝ))*((L : ℝ)*b^2) := by ring
         _ ≤ (2*(N : ℝ))*(P*((1+2*C)/P)^2) :=
           mul_le_mul_of_nonneg_left (mul_le_mul hLP hsq (sq_nonneg b) hP0.le) (by positivity)
         _ = _ := by field_simp
  have htail : (N : ℝ)/(L : ℝ) ≤ 2*(N : ℝ)/P := by
    apply (div_le_div_iff₀ hL0 hP0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hN0.le]
  have hfour : (4 : ℝ) ≤ 4*(N : ℝ)/P := by
    apply (le_div_iff₀ hP0).mpr
    change P ≤ (N : ℝ) at hPN
    linarith
  calc primitiveEnergy N ≤ 4+2*(N : ℝ)*(L : ℝ)*b^2+(N : ℝ)/(L : ℝ) := henergy
       _ ≤ 4*(N : ℝ)/P+2*(1+2*C)^2*(N : ℝ)/P+2*(N : ℝ)/P := add_le_add (add_le_add hfour hhead) htail
       _ = _ := by change _ = (6+2*(1+2*C)^2)*(N : ℝ)/P; ring

/-- The full existing modular carrier inherits every unconditional logarithmic saving. -/
theorem modular_norm_log_saving (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ‖bdMobiusModularApproximantVec N‖^2 ≤ B*(N : ℝ)/Real.log (N : ℝ)^(q+1) := by
  obtain ⟨B,hB,h⟩ := primitiveEnergy_log_saving q
  exact ⟨B,hB,h.mono (fun N hN => (modular_norm_sq_le_primitiveEnergy N).trans hN)⟩

/-- The complete signed cross sum, in absolute value, has arbitrary logarithmic savings
relative to N. This does not give the much smaller polynomial-log ceiling required for RH. -/
theorem abs_cross_log_saving (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |DeletionMobiusGram.cross N| ≤ B*(N : ℝ)/Real.log (N : ℝ)^(q+1) := by
  obtain ⟨B,hB,hE⟩ := primitiveEnergy_log_saving q
  refine ⟨B+4,by positivity,?_⟩
  filter_upwards [hE, DeletionMobiusGram.diagonal_eventually_le_four_log,
    log_tendsto.eventually_ge_atTop 1, log_pow_le_nat_eventually (q+2)] with N hEN hD hlog hpow
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  have hx : DeletionMobiusGram.cross N =
      ‖bdMobiusModularApproximantVec N‖^2-DeletionMobiusGram.diagonal N := by
    linarith [DeletionMobiusGram.modular_norm_sq_eq_diagonal_add_cross N]
  have hcross : |DeletionMobiusGram.cross N| ≤ primitiveEnergy N+4*Real.log (N : ℝ) := by
    rw [hx]
    calc _ ≤ |‖bdMobiusModularApproximantVec N‖^2|+|DeletionMobiusGram.diagonal N| := abs_sub _ _
         _ = ‖bdMobiusModularApproximantVec N‖^2+DeletionMobiusGram.diagonal N := by
           rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (DeletionMobiusGram.diagonal_nonneg N)]
         _ ≤ _ := add_le_add (modular_norm_sq_le_primitiveEnergy N) hD
  have hfour : 4*Real.log (N : ℝ) ≤ 4*(N : ℝ)/Real.log (N : ℝ)^(q+1) := by
    apply (le_div_iff₀ (pow_pos hlog0 _)).mpr
    rw [show q+2=(q+1)+1 by omega, pow_succ] at hpow
    nlinarith
  calc _ ≤ primitiveEnergy N+4*Real.log (N : ℝ) := hcross
       _ ≤ B*(N : ℝ)/Real.log (N : ℝ)^(q+1)+4*(N : ℝ)/Real.log (N : ℝ)^(q+1) := add_le_add hEN hfour
       _ = _ := by ring

private theorem weighted_log_limit {F : ℕ → ℝ} (hf : ∀ N, 0 ≤ F N) (q : ℕ)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      F N ≤ B*(N : ℝ)/Real.log (N : ℝ)^(q+1)) :
    Tendsto (fun N : ℕ => F N*Real.log (N : ℝ)^q/(N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := hbound
  have hlim : Tendsto (fun N : ℕ => B/Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_tendsto
  apply squeeze_zero' _ _ hlim
  · filter_upwards [log_tendsto.eventually_ge_atTop 1] with N hlog
    exact div_nonneg (mul_nonneg (hf N) (pow_nonneg (by linarith) q)) (Nat.cast_nonneg N)
  · filter_upwards [h,log_tendsto.eventually_ge_atTop 1,eventually_ge_atTop 1] with N hN hlog hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have hlog0 : 0 < Real.log (N : ℝ) := by linarith
    calc _ ≤ (B*(N : ℝ)/Real.log (N : ℝ)^(q+1))*Real.log (N : ℝ)^q/(N : ℝ) :=
           div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hN (pow_nonneg hlog0.le q)) hNr.le
         _ = _ := by rw [pow_succ]; field_simp

/-- Every fixed log power times the full arithmetic energy divided by N tends to zero. -/
theorem primitiveEnergy_log_pow_div_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => primitiveEnergy N*Real.log (N : ℝ)^q/(N : ℝ)) atTop (𝓝 0) :=
  weighted_log_limit (fun _ => tsum_nonneg (fun _ => sq_nonneg _)) q (primitiveEnergy_log_saving q)

/-- The same unconditional full-norm saving in the existing modular Hilbert carrier. -/
theorem modular_norm_log_pow_div_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => ‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ)^q/(N : ℝ)) atTop (𝓝 0) :=
  weighted_log_limit (fun _ => sq_nonneg _) q (modular_norm_log_saving q)

/-- Absolute aggregate cross interference is o(N/(log N)^q) at every fixed logarithmic order. -/
theorem abs_cross_log_pow_div_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => |DeletionMobiusGram.cross N| *Real.log (N : ℝ)^q/(N : ℝ)) atTop (𝓝 0) :=
  weighted_log_limit (fun _ => abs_nonneg _) q (abs_cross_log_saving q)

/-- Every actual-zero full current inherits the unconditional arithmetic upper saving.
Together with off-line superlogarithmic escape this leaves an explicit unresolved growth gap. -/
theorem abs_sourceCurrent_log_pow_div_tendsto_zero (rho : RiemannGaussian.NontrivialZetaZero) (q : ℕ) :
    Tendsto (fun N : ℕ => |(DeletionMobiusCurrent.sourceCurrent N rho.1).re| *
      Real.log (N : ℝ)^q/(N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hcurrent⟩ := exists_current_bound_by_primitiveEnergy rho
  obtain ⟨B,hB,hE⟩ := primitiveEnergy_log_saving q
  apply weighted_log_limit (fun _ => abs_nonneg _) q
  refine ⟨C*B,mul_nonneg hC.le hB,?_⟩
  filter_upwards [hE] with N hN
  calc _ ≤ C*primitiveEnergy N := hcurrent N
       _ ≤ C*(B*(N : ℝ)/Real.log (N : ℝ)^(q+1)) := mul_le_mul_of_nonneg_left hN hC.le
       _ = _ := by ring

end RHTower.DeletionMobiusGlobal
end
