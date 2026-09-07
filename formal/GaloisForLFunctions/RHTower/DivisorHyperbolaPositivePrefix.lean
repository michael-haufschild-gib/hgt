import GaloisForLFunctions.RHTower.HarmonicSecondErrorBounds
import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
import GaloisForLFunctions.RHTower.MobiusDivisorAbelHomothety

/-!
# Positive large prefixes of the literal divisor source

A quadratic floor on each smooth square block outweighs the exact negative
centered modular primitives. This gives a linear ordinary-prefix floor and, by
Abel summation with the finite initial contribution retained, a square-root
floor for the undilated half-order response. No arithmetic signed aggregation
or Riemann-hypothesis premise is used.
-/

noncomputable section
open Finset
namespace RHTower

private theorem hyperbola_quadratic_floor {x s : ℝ} (hs : 1 ≤ s)
    (hlo : s^2 ≤ x) (hhi : x ≤ s^2+2*s) :
    (x-s^2)^2/(2*(s+1)^2) ≤ x*(Real.log x-2*Real.log s)-x+s^2 := by
  have hs0 : 0 < s := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (sq_pos_of_pos hs0) hlo
  have hlog : 2*(x-s^2)/(x+s^2) ≤ Real.log x-2*Real.log s := by
    by_cases heq : x = s^2
    · subst x
      simp [Real.log_pow]
    have hu : 0 < (x-s^2)/s^2 := by positivity
    have h := (Real.lt_log_one_add_of_pos hu).le
    have harg : 1+(x-s^2)/s^2=x/s^2 := by field_simp; ring
    rw [harg,Real.log_div hx0.ne' (ne_of_gt (sq_pos_of_pos hs0)),Real.log_pow] at h
    have hcoeff : 2*((x-s^2)/s^2)/((x-s^2)/s^2+2)=2*(x-s^2)/(x+s^2) := by
      field_simp [hs0.ne']
      ring_nf
      field_simp [ne_of_gt (show 0 < x+s^2 by positivity)]
    rwa [hcoeff] at h
  have hmul := mul_le_mul_of_nonneg_left hlog hx0.le
  have hid : x*(2*(x-s^2)/(x+s^2))-x+s^2 = (x-s^2)^2/(x+s^2) := by
    field_simp; ring
  have hfirst : (x-s^2)^2/(x+s^2) ≤ x*(Real.log x-2*Real.log s)-x+s^2 := by
    rw [← hid]
    linarith only [hmul]
  apply le_trans _ hfirst
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith only [hhi,hs]

private theorem hyperbola_quadratic_correction {x s : ℝ} (hs : 1 ≤ s)
    (hhi : x ≤ s^2+2*s) :
    (x-s^2-s)^2/(2*(s+1)^2)-5/s ≤
      1/3 - 1/(2*s) + (x-s^2)^2/(2*(s+1)^2) - (x-s^2)/s +
        (2*x+1)/(12*(s+1)^2) := by
  have hs0 : 0 < s := by linarith
  have hprod : 0 ≤ (2*s-(x-s^2))*(22*s+12) :=
    mul_nonneg (by linarith) (by positivity)
  field_simp
  nlinarith only [hprod,sq_nonneg s,hs]

/-- The smooth divisor-hyperbola boundary retains a quadratic well on each square block. -/
theorem divisorHyperbolaSmoothRemainder_ge_quadratic {N : ℕ} (hN : 1 ≤ N) :
    let s : ℝ := Nat.sqrt N
    ((N : ℝ)-s^2-s)^2/(2*(s+1)^2)-5/s ≤ divisorHyperbolaSmoothRemainder N := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by positivity
  have hlo : (s : ℝ)^2 ≤ N := by
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le N
  have hhi : (N : ℝ) ≤ (s : ℝ)^2+2*s := by
    have h := Nat.lt_succ_sqrt N
    change N < (s+1)*(s+1) at h
    have h' : N ≤ s*s+2*s := by nlinarith
    rw [pow_two]
    exact_mod_cast h'
  have hb := hyperbola_quadratic_floor hsR hlo hhi
  have hc := hyperbola_quadratic_correction hsR hhi
  have hfact := sum_log_Icc_ge_half_log_stirling hN
  have hH := harmonic_mascheroni_le_half_sub_twelfth hs
  have hHm := mul_le_mul_of_nonneg_left hH (show (0:ℝ) ≤ 2*N+1 by positivity)
  have hg : Real.eulerMascheroniConstant ≤ 7/12 := by
    have h := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    linarith
  have hlog : 0 ≤ Real.log N-2*Real.log s := by
    have h := Real.log_le_log (sq_pos_of_pos hs0) hlo
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hid : (2*(N : ℝ)+1)/(2*s) = (N : ℝ)/s+1/(2*s) := by ring
  have hcancel : (s : ℝ)^2/s=s := by field_simp
  dsimp only
  change ((N : ℝ)-(s : ℝ)^2-s)^2/(2*((s : ℝ)+1)^2)-5/s ≤ _
  change _ ≤ (∑ m ∈ Icc 1 N, Real.log m) -
    (2*(N : ℝ)+1)*((harmonic s : ℚ) : ℝ)+(s : ℝ)^2+s+2*Real.eulerMascheroniConstant*N
  simp only [mul_sub,mul_one_div] at hHm
  rw [hid] at hHm
  rw [sub_div,hcancel] at hc
  nlinarith only [hb,hc,hfact,hHm,hg,hlog,hid,hcancel]

private theorem sum_range_cast_id (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)) = n*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

private theorem sum_range_cast_sq (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)^2) = n*((n : ℝ)-1)*(2*n-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

private theorem sum_centered_square_block (s : ℕ) :
    (∑ k ∈ Ico (s*s) ((s+1)*(s+1)), ((k : ℝ)-(s : ℝ)^2-s)^2) =
      (s : ℝ)*(s+1)*(2*s+1)/3 := by
  have hn : (s+1)*(s+1)=s*s+(2*s+1) := by ring
  rw [hn,sum_Ico_eq_sum_range]
  have hnum : s*s+(2*s+1)-s*s=2*s+1 := by omega
  rw [hnum]
  have hpoly (i : ℕ) : (((s*s+i : ℕ) : ℝ)-(s : ℝ)^2-s)^2 =
      (i : ℝ)^2-2*s*i+(s : ℝ)^2 := by push_cast; ring
  simp_rw [hpoly]
  rw [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_range_cast_sq,sum_range_cast_id]
  simp only [sum_const,card_range,nsmul_eq_mul]
  push_cast
  ring

/-- A complete square block supplies a quantitative positive quadratic contribution. -/
theorem sum_divisorHyperbolaSmoothRemainder_square_block_ge {s : ℕ} (hs : 1 ≤ s) :
    (s : ℝ)/3-91/6 ≤ ∑ k ∈ Ico (s*s) ((s+1)*(s+1)), divisorHyperbolaSmoothRemainder k := by
  have hpoint (k : ℕ) (hk : k ∈ Ico (s*s) ((s+1)*(s+1))) :
      ((k : ℝ)-(s : ℝ)^2-s)^2/(2*((s : ℝ)+1)^2)-5/s ≤ divisorHyperbolaSmoothRemainder k := by
    have hroot : Nat.sqrt k=s := (Nat.eq_sqrt.mpr (mem_Ico.mp hk)).symm
    have hk1 : 1 ≤ k := by have := (mem_Ico.mp hk).1; nlinarith
    simpa only [hroot] using divisorHyperbolaSmoothRemainder_ge_quadratic hk1
  have hsum := sum_le_sum hpoint
  rw [sum_sub_distrib,← sum_div,sum_centered_square_block] at hsum
  have hcard : (Ico (s*s) ((s+1)*(s+1))).card=2*s+1 := by
    rw [Nat.card_Ico]
    have h : (s+1)*(s+1)=s*s+(2*s+1) := by ring
    omega
  simp only [sum_const,hcard,nsmul_eq_mul] at hsum
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpoly : (s : ℝ)/3-91/6 ≤
      ((s : ℝ)*(s+1)*(2*s+1)/3)/(2*((s : ℝ)+1)^2) - (2*s+1 : ℕ)*(5/(s : ℝ)) := by
    push_cast
    field_simp
    nlinarith [sq_nonneg ((s : ℝ)-1)]
  exact hpoly.trans hsum

private theorem smooth_square_prefix (t : ℕ) :
    ((t+1 : ℕ) : ℝ)^2/6-(46/3)*((t+1 : ℕ) : ℝ)+91/6 ≤
      ∑ k ∈ Ico 1 ((t+1)*(t+1)), divisorHyperbolaSmoothRemainder k := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    have hs : 1 ≤ (t+1)*(t+1) := by nlinarith
    have hstep : (t+1)*(t+1) ≤ (t+1+1)*(t+1+1) := by nlinarith
    have hsplit := sum_Ico_consecutive hs hstep (f := divisorHyperbolaSmoothRemainder)
    rw [← hsplit]
    have hblock := sum_divisorHyperbolaSmoothRemainder_square_block_ge (s := t+1) (by omega)
    push_cast at ih hblock ⊢
    nlinarith only [ih,hblock]

/-- Complete smooth-prefix floor with the last partial square block retained. -/
theorem sum_divisorHyperbolaSmoothRemainder_ge {N : ℕ} (hN : 1 ≤ N) :
    (Nat.sqrt N : ℝ)^2/6-16*Nat.sqrt N ≤
      ∑ k ∈ Icc 1 N, divisorHyperbolaSmoothRemainder k := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsN : s*s ≤ N := Nat.sqrt_le N
  have hupper : N < (s+1)*(s+1) := Nat.lt_succ_sqrt N
  have hpref := smooth_square_prefix (s-1)
  rw [Nat.sub_add_cancel hs] at hpref
  have hpoint (k : ℕ) (hk : k ∈ Ico (s*s) (N+1)) :
      -(5/(s : ℝ)) ≤ divisorHyperbolaSmoothRemainder k := by
    have hk' := mem_Ico.mp hk
    have hk1 : 1 ≤ k := by nlinarith
    have hroot : Nat.sqrt k=s := (Nat.eq_sqrt.mpr ⟨hk'.1,by omega⟩).symm
    have h := divisorHyperbolaSmoothRemainder_ge_quadratic hk1
    simp only [hroot] at h
    have hq : 0 ≤ ((k : ℝ)-(s : ℝ)^2-s)^2/(2*((s : ℝ)+1)^2) := by positivity
    linarith only [h,hq]
  have hlast := sum_le_sum hpoint
  have hcard : (Ico (s*s) (N+1)).card ≤ 2*s+1 := by
    rw [Nat.card_Ico]
    have hmax : N+1 ≤ s*s+2*s+1 := by nlinarith
    omega
  have hcardR : ((Ico (s*s) (N+1)).card : ℝ) ≤ 2*s+1 := by exact_mod_cast hcard
  simp only [sum_const,nsmul_eq_mul] at hlast
  have hlast' : -(15:ℝ) ≤ ∑ k ∈ Ico (s*s) (N+1), divisorHyperbolaSmoothRemainder k := by
    have hmul := mul_le_mul_of_nonneg_right hcardR (show 0 ≤ 5/(s : ℝ) by positivity)
    have hsmall : (2*(s : ℝ)+1)*(5/s) ≤ 15 := by
      rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ)<s)]
      linarith only [hsR]
    nlinarith only [hlast,hmul,hsmall]
  rw [← Ico_add_one_right_eq_Icc]
  rw [← sum_Ico_consecutive (show 1 ≤ s*s by nlinarith) (show s*s ≤ N+1 by omega)
    (f := divisorHyperbolaSmoothRemainder)]
  change (s : ℝ)^2/6-16*s ≤ _
  linarith only [hpref,hlast',hsR]

private theorem centered_hyperbola_range_birth (M : ℕ) :
    (∑ k ∈ range M, centeredDivisorHyperbola k) =
      ∑ d ∈ Icc 1 (Nat.sqrt (M-1)), ∑ k ∈ Ico (d*d) M, HTGeometry.centeredModularRamp d k := by
  let D := Icc 1 (Nat.sqrt (M-1))
  have hfibre (k : ℕ) (hk : k ∈ range M) :
      Icc 1 (Nat.sqrt k)=D.filter (fun d => d*d ≤ k) := by
    have hkM : k ≤ M-1 := by have := mem_range.mp hk; omega
    ext d
    simp only [mem_Icc,mem_filter,D]
    constructor
    · intro hd
      exact ⟨⟨hd.1,hd.2.trans (Nat.sqrt_le_sqrt hkM)⟩,Nat.le_sqrt.mp hd.2⟩
    · intro hd
      exact ⟨hd.1.1,Nat.le_sqrt.mpr hd.2⟩
  have htime (d : ℕ) : (range M).filter (fun k => d*d ≤ k)=Ico (d*d) M := by
    ext k
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  unfold centeredDivisorHyperbola
  calc
    _ = ∑ k ∈ range M, ∑ d ∈ D,
        if d*d ≤ k then HTGeometry.centeredModularRamp d k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [hfibre k hk,sum_filter]
    _ = ∑ d ∈ D, ∑ k ∈ range M,
        if d*d ≤ k then HTGeometry.centeredModularRamp d k else 0 := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [← sum_filter,htime]

/-- Exact ordinary prefix of the centered hyperbola, retaining every square-birth boundary. -/
theorem sum_centeredDivisorHyperbola_eq_primitives (N : ℕ) :
    (∑ k ∈ Icc 1 N, centeredDivisorHyperbola k) =
      ∑ d ∈ Icc 1 (Nat.sqrt N), HTGeometry.centeredModularPrimitive d (N+1) := by
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sub _ (by omega : 1 ≤ N+1)]
  have hz : centeredDivisorHyperbola 0=0 := by simp [centeredDivisorHyperbola]
  rw [sum_range_one,hz,sub_zero,centered_hyperbola_range_birth]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl
  intro d hd
  have hdN : d*d ≤ N := (Nat.le_sqrt.mp (mem_Icc.mp hd).2)
  rw [sum_Ico_eq_sub _ (by omega : d*d ≤ N+1),HTGeometry.sum_centeredModularRamp,
    HTGeometry.sum_centeredModularRamp]
  simp [HTGeometry.centeredModularPrimitive]

private theorem sum_cast_Icc_id (n : ℕ) :
    (∑ d ∈ Icc 1 n, (d : ℝ)) = n*((n : ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega : 1 ≤ n+1),ih]; push_cast; ring

/-- The complete centered ordinary prefix has a quadratic floor in the square-root index. -/
theorem sum_centeredDivisorHyperbola_bounds (N : ℕ) :
    -(Nat.sqrt N : ℝ)*(Nat.sqrt N+1)/16 ≤
      (∑ k ∈ Icc 1 N, centeredDivisorHyperbola k) ∧
      (∑ k ∈ Icc 1 N, centeredDivisorHyperbola k) ≤ 0 := by
  rw [sum_centeredDivisorHyperbola_eq_primitives]
  constructor
  · have h := sum_le_sum (fun d (_hd : d ∈ Icc 1 (Nat.sqrt N)) =>
        (HTGeometry.centeredModularPrimitive_bounds d (N+1)).1)
    simp only [sum_neg_distrib,← sum_div,sum_cast_Icc_id,neg_div] at h
    linarith only [h]
  · exact sum_nonpos (fun d _ => (HTGeometry.centeredModularPrimitive_bounds d (N+1)).2)

/-- The literal divisor-defect prefixes have a positive linear floor after a square-root loss. -/
theorem sum_primeFreeDivisorDefect_ge {N : ℕ} (hN : 1 ≤ N) :
    (Nat.sqrt N : ℝ)^2/24-17*Nat.sqrt N ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect k := by
  have hR := sum_divisorHyperbolaSmoothRemainder_ge hN
  have hE := (sum_centeredDivisorHyperbola_bounds N).1
  have hsplit : (∑ k ∈ Icc 1 N, primeFreeDivisorDefect k) =
      (∑ k ∈ Icc 1 N, divisorHyperbolaSmoothRemainder k)+
        2*∑ k ∈ Icc 1 N, centeredDivisorHyperbola k := by
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    simpa only [primeFreeDivisorDefect,mul_comm] using (divisorHyperbolaSmooth_add_centered k).symm
  have hs : (0:ℝ) ≤ Nat.sqrt N := by positivity
  rw [hsplit]
  nlinarith only [hR,hE,hs]

/-- Every literal ordinary divisor-defect prefix beyond the explicit square threshold is nonnegative. -/
theorem sum_primeFreeDivisorDefect_nonneg_of_large {N : ℕ} (hN : 408*408 ≤ N) :
    0 ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect k := by
  have hs : 408 ≤ Nat.sqrt N := Nat.le_sqrt.mpr hN
  have hsR : (408:ℝ) ≤ Nat.sqrt N := by exact_mod_cast hs
  have h := sum_primeFreeDivisorDefect_ge (by omega : 1 ≤ N)
  nlinarith [mul_nonneg (show 0 ≤ (Nat.sqrt N : ℝ) by positivity)
    (show 0 ≤ (Nat.sqrt N : ℝ)-408 by linarith)]

/-- A uniform affine floor for the actual ordinary prefixes, including the empty prefix. -/
theorem sum_primeFreeDivisorDefect_ge_affine (N : ℕ) :
    (N : ℝ)/48-3500 ≤ ∑ k ∈ Icc 1 N, primeFreeDivisorDefect k := by
  by_cases hN : N=0
  · simp [hN]
  have h := sum_primeFreeDivisorDefect_ge (by omega : 1 ≤ N)
  have hupper : (N : ℝ) ≤ (Nat.sqrt N : ℝ)^2+2*Nat.sqrt N := by
    have h' := Nat.sqrt_le_add N
    rw [pow_two]
    exact_mod_cast (show N ≤ Nat.sqrt N*Nat.sqrt N+2*Nat.sqrt N by omega)
  nlinarith only [h,hupper,sq_nonneg ((Nat.sqrt N : ℝ)-409)]

/-- An explicit square-root floor for the actual undilated half-order source response. -/
theorem divisorUnsignedDilationChannel_one_ge (M : ℕ) :
    Real.sqrt M/48-3501 ≤ divisorUnsignedDilationChannel M 1 := by
  by_cases hM : M ≤ 1
  · have hzero : divisorUnsignedDilationChannel M 1=0 := by
      simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1 < 1)]
    have hroot : Real.sqrt M ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show (M : ℝ) ≤ 1 by exact_mod_cast hM)
    rw [hzero]
    linarith only [hroot]
  let N := M-1
  let w : ℕ → ℝ := HTGeometry.halfOrderAbelStep 0
  let f : ℕ → ℝ := fun k => primeFreeDivisorDefect k-1/48+(if k=1 then 3500 else 0)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hMN : N+1=M := by dsimp [N]; omega
  have hprefix (n : ℕ) (hn : 1 ≤ n) : 0 ≤ ∑ k ∈ Icc 1 n, f k := by
    have h := sum_primeFreeDivisorDefect_ge_affine n
    have hmem : 1 ∈ Icc 1 n := by simpa
    simp only [f,sum_add_distrib,sum_sub_distrib,sum_const,Nat.card_Icc,nsmul_eq_mul,Nat.add_sub_cancel]
    rw [sum_ite_eq',if_pos hmem]
    linarith only [h]
  have hnonneg : 0 ≤ ∑ k ∈ Icc 1 N, f k*w k := by
    rw [HTGeometry.sum_mul_eq_partial_mul_diff_ring]
    apply add_nonneg
    · apply sum_nonneg
      intro k hk
      exact mul_nonneg (hprefix k (mem_Icc.mp hk).1)
        (sub_nonneg.mpr (HTGeometry.halfOrderAbelStep_antitone 0 (show k ≤ k+1 by omega)))
    · exact mul_nonneg (hprefix N hN) (HTGeometry.halfOrderAbelStep_nonneg 0 (N+1))
  have htel : (∑ k ∈ Icc 1 N, w k)=Real.sqrt M-1 := by
    simpa only [w,HTGeometry.halfOrderAbelStep,Nat.zero_add,hMN,Nat.cast_one,Real.sqrt_one] using
      sum_sqrt_succ_sub_sqrt_Icc_general hN
  have hsum : (∑ k ∈ Icc 1 N, f k*w k) = divisorUnsignedDilationChannel M 1 -
      (Real.sqrt M-1)/48+3500*w 1 := by
    have hmem : 1 ∈ Icc 1 N := by simpa
    simp only [f,add_mul,sub_mul,sum_add_distrib,sum_sub_distrib,← mul_sum,ite_mul,zero_mul]
    rw [sum_ite_eq',if_pos hmem,htel]
    have hbase : (∑ k ∈ Icc 1 N, primeFreeDivisorDefect k*w k)=divisorUnsignedDilationChannel M 1 := by
      unfold divisorUnsignedDilationChannel
      apply sum_congr rfl
      intro k _
      simp only [w,HTGeometry.halfOrderAbelStep,Nat.zero_add,Nat.div_one]
      ring
    rw [hbase]
    ring
  have hw : w 1 ≤ 1 := by
    have h := HTGeometry.halfOrderAbelStep_square_initial 1
    simpa only [w,Nat.mul_one,HTGeometry.halfOrderAbelStep,Nat.add_zero,Nat.zero_add,Nat.cast_one,
      Real.sqrt_one,one_mul] using (le_trans h (by norm_num : (1/2:ℝ) ≤ 1))
  rw [hsum] at hnonneg
  nlinarith only [hnonneg,hw]

/-- The undilated literal half-order response tends to positive infinity unconditionally. -/
theorem tendsto_divisorUnsignedDilationChannel_one_atTop :
    Filter.Tendsto (fun M : ℕ => divisorUnsignedDilationChannel M 1) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono divisorUnsignedDilationChannel_one_ge
  have ht : Filter.Tendsto (fun M : ℕ => Real.sqrt M) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hm := ht.const_mul_atTop (by norm_num : (0:ℝ) < 1/48)
  have ha : Filter.Tendsto (fun M : ℕ => (1/48:ℝ)*Real.sqrt M+(-3501))
      Filter.atTop Filter.atTop := hm.atTop_add tendsto_const_nhds
  convert ha using 1
  funext M
  ring

end RHTower
