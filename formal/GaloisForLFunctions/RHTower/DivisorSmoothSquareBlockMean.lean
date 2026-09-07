import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds
import GaloisForLFunctions.RHTower.DivisorSecondCenteredHyperbola
import GaloisForLFunctions.RHTower.MobiusDivisorTwoPrimeLocalCriterion

/-!
# Exact smooth square-block mean and bounded-quotient obstruction

The literal smooth divisor boundary has an exact quadratic square phase and a
reciprocal square-root error. Complete blocks and the last partial block yield
its linear prefix mean; finite Abel summation gives the exact square-root
coefficient with logarithmic error. Its strict constant margin and the centered
source bounds prove factor-two dilation control for every sufficiently large
quotient, uniformly in the cutoff and dilation. Any original two-prime ceiling
failure must therefore occur through a bounded quotient profile. Those remaining
profiles, the all-cutoff ceiling and aggregate signed dominance remain open.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private theorem quadratic_boundary_bounds {x s : ℝ} (hs : 1 ≤ s)
    (hlo : s^2 ≤ x) (hhi : x ≤ s^2+2*s) :
    (x-s^2)^2/(2*s^2)-4/s ≤ x*(Real.log x-2*Real.log s)-x+s^2 ∧
    x*(Real.log x-2*Real.log s)-x+s^2 ≤ (x-s^2)^2/(2*s^2) := by
  have hs0 : 0 < s := by linarith
  have hx : 0 < x := lt_of_lt_of_le (sq_pos_of_pos hs0) hlo
  have hs2 : 0 < s^2 := sq_pos_of_pos hs0
  have hv : 0 ≤ x-s^2 := sub_nonneg.mpr hlo
  have hv2 : (x-s^2)^2 ≤ 4*s^2 := by nlinarith only [hv,hhi]
  have hu := log_le_half_sub_inv (x := x/s^2) (by rw [le_div_iff₀ hs2]; simpa only [one_mul] using hlo)
  rw [Real.log_div hx.ne' hs2.ne',Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hum := mul_le_mul_of_nonneg_left hu hx.le
  have hue : x*((x/s^2-(x/s^2)⁻¹)/2)-x+s^2=(x-s^2)^2/(2*s^2) := by field_simp; ring
  have hl : 2*(x-s^2)/(x+s^2) ≤ Real.log x-2*Real.log s := by
    by_cases he : x=s^2
    · subst x; simp [Real.log_pow]
    have hp : 0 < (x-s^2)/s^2 := by positivity
    have h := (Real.lt_log_one_add_of_pos hp).le
    have he1 : 1+(x-s^2)/s^2=x/s^2 := by field_simp; ring
    rw [he1,Real.log_div hx.ne' hs2.ne',Real.log_pow] at h
    have he2 : 2*((x-s^2)/s^2)/((x-s^2)/s^2+2)=2*(x-s^2)/(x+s^2) := by
      field_simp [hs0.ne']
      ring
    rwa [he2] at h
  have hlm := mul_le_mul_of_nonneg_left hl hx.le
  have hle : x*(2*(x-s^2)/(x+s^2))-x+s^2=(x-s^2)^2/(x+s^2) := by field_simp; ring
  have hlq : (x-s^2)^2/(2*(s+1)^2) ≤ (x-s^2)^2/(x+s^2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith only [hhi,hs]
  have hdiff : (x-s^2)^2/(2*s^2)-(x-s^2)^2/(2*(s+1)^2) ≤ 4/s := by
    have h := mul_le_mul_of_nonneg_right hv2 (show 0 ≤ (2*s+1)/(2*s^2*(s+1)^2) by positivity)
    have he : (x-s^2)^2/(2*s^2)-(x-s^2)^2/(2*(s+1)^2)=
        (x-s^2)^2*((2*s+1)/(2*s^2*(s+1)^2)) := by field_simp; ring
    rw [he]
    refine h.trans ?_
    field_simp
    nlinarith [sq_nonneg s]
  constructor <;> nlinarith only [hlm,hle,hlq,hdiff,hum,hue]

/-- The literal smooth boundary retains the exact Stirling constant and its quadratic square phase. -/
theorem divisorHyperbolaSmoothRemainder_exact_quadratic_bounds {N : ℕ} (hN : 1 ≤ N) :
    let s : ℝ := Nat.sqrt N
    let q := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/3+
      ((N:ℝ)-s^2-s)^2/(2*s^2)
    q-5/s ≤ divisorHyperbolaSmoothRemainder N ∧
      divisorHyperbolaSmoothRemainder N ≤ q+2/s := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by positivity
  have hx : (0:ℝ) < N := by positivity
  have hlo : (s:ℝ)^2 ≤ N := by rw [pow_two]; exact_mod_cast Nat.sqrt_le N
  have hhi : (N:ℝ) ≤ (s:ℝ)^2+2*s := by
    have h := Nat.lt_succ_sqrt N
    change N < (s+1)*(s+1) at h
    have h' : N ≤ s*s+2*s := by nlinarith
    rw [pow_two]; exact_mod_cast h'
  have hB := quadratic_boundary_bounds hsR hlo hhi
  have hF := sum_log_Icc_exact_stirling_bounds hN
  dsimp only at hF
  have hHlo := harmonic_mascheroni_ge_half_sub_twelfth hs
  have hHhi := harmonic_mascheroni_le_half_sub_twelfth hs
  have hHlo' := mul_le_mul_of_nonneg_left hHlo (show (0:ℝ) ≤ 2*N+1 by positivity)
  have hHhi' := mul_le_mul_of_nonneg_left hHhi (show (0:ℝ) ≤ 2*N+1 by positivity)
  have hLlo : 0 ≤ Real.log N-2*Real.log s := by
    have h := Real.log_le_log (sq_pos_of_pos hs0) hlo
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hLhi : Real.log N/2-Real.log s ≤ 1/s := by
    have h := Real.log_le_sub_one_of_pos (x := (N:ℝ)/(s:ℝ)^2) (by positivity)
    rw [Real.log_div hx.ne' (ne_of_gt (sq_pos_of_pos hs0)),Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hr : (N:ℝ)/(s:ℝ)^2-1 ≤ 2/s := by field_simp; nlinarith only [hhi]
    simp only [div_eq_mul_inv] at h hr ⊢
    linarith only [h,hr]
  have hFlo : (0:ℝ) ≤ 1/(12*N) := by positivity
  have hFhi : (1:ℝ)/(12*N) ≤ 1/s := by
    apply div_le_div_of_nonneg_left (by norm_num) hs0
    nlinarith only [hlo,hsR]
  have hElo : (s:ℝ)-(2*N+1)*(1/(2*s)-1/(12*((s:ℝ)+1)^2)) ≥
      -((N:ℝ)-(s:ℝ)^2)/s+1/6-1/s := by
    field_simp
    nlinarith [sq_nonneg (s:ℝ)]
  have hEhi : (s:ℝ)-(2*N+1)*(1/(2*s)-1/(12*(s:ℝ)^2)) ≤
      -((N:ℝ)-(s:ℝ)^2)/s+1/6 := by
    field_simp
    nlinarith only [hhi,hsR]
  have hq : ((N:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2)-1/3 =
      ((N:ℝ)-(s:ℝ)^2)^2/(2*(s:ℝ)^2)-((N:ℝ)-(s:ℝ)^2)/s+1/6 := by field_simp; ring
  have hid : divisorHyperbolaSmoothRemainder N =
      ((∑ k ∈ Icc 1 N,Real.log k)-(N:ℝ)*Real.log N+N-Real.log N/2)-Real.eulerMascheroniConstant+
      ((N:ℝ)*(Real.log N-2*Real.log s)-N+(s:ℝ)^2)+
      (Real.log N/2-Real.log s)+(s:ℝ)-
      (2*N+1)*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant) := by
    dsimp [divisorHyperbolaSmoothRemainder,s]; ring
  change Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/3+
      ((N:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2)-5/s ≤ _ ∧ _ ≤
      Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/3+
      ((N:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2)+2/s
  rw [hid]
  simp only [div_eq_mul_inv] at hB hF hHlo' hHhi' hLlo hLhi hFhi hElo hEhi hq ⊢
  constructor <;> nlinarith only [hB.1,hB.2,hF.1,hF.2,hHlo',hHhi',hLlo,hLhi,hFhi,hElo,hEhi,hq]

/-- Exact mean coefficient of the smooth square-block source. -/
def divisorHyperbolaSmoothMean : ℝ := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/6

private theorem sum_square_phase (s : ℕ) :
    (∑ k ∈ Ico (s*s) ((s+1)*(s+1)),((k:ℝ)-(s:ℝ)^2-s)^2)=
      (s:ℝ)*(s+1)*(2*s+1)/3 := by
  have h1 (n : ℕ) : (∑ i ∈ range n,(i:ℝ))=n*((n:ℝ)-1)/2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring
  have h2 (n : ℕ) : (∑ i ∈ range n,(i:ℝ)^2)=n*((n:ℝ)-1)*(2*n-1)/6 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring
  have hn : (s+1)*(s+1)=s*s+(2*s+1) := by ring
  rw [hn,sum_Ico_eq_sum_range,show s*s+(2*s+1)-s*s=2*s+1 by omega]
  have he (i : ℕ) : (((s*s+i:ℕ):ℝ)-(s:ℝ)^2-s)^2=(i:ℝ)^2-2*s*i+(s:ℝ)^2 := by push_cast; ring
  simp_rw [he]
  rw [sum_add_distrib,sum_sub_distrib,← mul_sum,h1,h2]
  simp only [sum_const,card_range,nsmul_eq_mul]
  push_cast
  ring

/-- Every complete square block has bounded total error from its exact mean. -/
theorem sum_divisorHyperbolaSmooth_square_block_mean_error {s : ℕ} (hs : 1 ≤ s) :
    |∑ k ∈ Ico (s*s) ((s+1)*(s+1)),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean)| ≤ 15 := by
  have hp (k : ℕ) (hk : k ∈ Ico (s*s) ((s+1)*(s+1))) :
      Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/3+
        ((k:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2)-5/s ≤ divisorHyperbolaSmoothRemainder k ∧
      divisorHyperbolaSmoothRemainder k ≤ Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/3+
        ((k:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2)+2/s := by
    have h := divisorHyperbolaSmoothRemainder_exact_quadratic_bounds
      (show 1 ≤ k by have := (mem_Ico.mp hk).1; nlinarith)
    have hr : Nat.sqrt k=s := (Nat.eq_sqrt.mpr (mem_Ico.mp hk)).symm
    simpa only [hr] using h
  have hlow := sum_le_sum (fun k hk => (hp k hk).1)
  have hhigh := sum_le_sum (fun k hk => (hp k hk).2)
  simp only [sum_sub_distrib,sum_add_distrib,← sum_div,sum_const,nsmul_eq_mul] at hlow hhigh
  have hcard : (Ico (s*s) ((s+1)*(s+1))).card=2*s+1 := by
    rw [Nat.card_Ico]
    have he : (s+1)*(s+1)=s*s+(2*s+1) := by ring
    omega
  rw [hcard,sum_square_phase] at hlow hhigh
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by positivity
  have hmean : ((s:ℝ)*(s+1)*(2*s+1)/3)/(2*(s:ℝ)^2)-((2*s+1:ℕ):ℝ)/6 =
      (2*s+1)/(6*(s:ℝ)) := by push_cast; field_simp; ring
  have hlo : -(15:ℝ) ≤ (2*s+1)/(6*(s:ℝ))-(2*s+1:ℕ)*(5/(s:ℝ)) := by
    push_cast; field_simp; nlinarith only [hsR]
  have hhi : (2*s+1)/(6*(s:ℝ))+(2*s+1:ℕ)*(2/(s:ℝ)) ≤ 15 := by
    push_cast; field_simp; nlinarith only [hsR]
  rw [abs_le]
  simp only [sum_sub_distrib,sum_const,hcard,nsmul_eq_mul,divisorHyperbolaSmoothMean]
  simp only [div_eq_mul_inv] at hlow hhigh hmean hlo hhi ⊢
  constructor <;> nlinarith only [hlow,hhigh,hmean,hlo,hhi]

private theorem smooth_mean_point_bound {N : ℕ} (hN : 1 ≤ N) :
    |divisorHyperbolaSmoothRemainder N-divisorHyperbolaSmoothMean| ≤ 6 := by
  have hb := divisorHyperbolaSmoothRemainder_exact_quadratic_bounds hN
  dsimp only at hb
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by positivity
  have hlo : (s:ℝ)^2 ≤ N := by rw [pow_two]; exact_mod_cast Nat.sqrt_le N
  have hhi : (N:ℝ) ≤ (s:ℝ)^2+2*s := by
    have h := Nat.lt_succ_sqrt N
    change N < (s+1)*(s+1) at h
    have h' : N ≤ s*s+2*s := by nlinarith
    rw [pow_two]; exact_mod_cast h'
  have hq0 : 0 ≤ ((N:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2) := by positivity
  have hq1 : ((N:ℝ)-(s:ℝ)^2-s)^2/(2*(s:ℝ)^2) ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hlo,hhi]
  have h5 : (5:ℝ)/s ≤ 5 := by rw [div_le_iff₀ hs0]; linarith only [hsR]
  have h2 : (2:ℝ)/s ≤ 2 := by rw [div_le_iff₀ hs0]; linarith only [hsR]
  change _-5/(s:ℝ) ≤ _ ∧ _ ≤ _+2/(s:ℝ) at hb
  rw [abs_le]
  dsimp [divisorHyperbolaSmoothMean]
  constructor <;> linarith only [hb.1,hb.2,hq0,hq1,h5,h2]

private theorem smooth_mean_square_prefix (t : ℕ) :
    |∑ k ∈ Ico 1 ((t+1)*(t+1)),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean)| ≤ 15*t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs : 1 ≤ (t+1)*(t+1) := by nlinarith
    have hstep : (t+1)*(t+1) ≤ (t+1+1)*(t+1+1) := by nlinarith
    rw [← sum_Ico_consecutive hs hstep (f := fun k => divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean)]
    have hb := sum_divisorHyperbolaSmooth_square_block_mean_error (s := t+1) (by omega)
    have ht := abs_add_le
      (∑ k ∈ Ico 1 ((t+1)*(t+1)),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean))
      (∑ k ∈ Ico ((t+1)*(t+1)) ((t+1+1)*(t+1+1)),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean))
    push_cast
    linarith only [ht,ih,hb]

/-- The complete smooth prefix has its exact linear mean with a square-root error, including the terminal partial block. -/
theorem sum_divisorHyperbolaSmooth_mean_error (N : ℕ) :
    |(∑ k ∈ Icc 1 N,divisorHyperbolaSmoothRemainder k)-divisorHyperbolaSmoothMean*N| ≤ 33*Real.sqrt N := by
  by_cases hz : N=0
  · simp [hz]
  have hN : 1 ≤ N := by omega
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hsN : s*s ≤ N := Nat.sqrt_le N
  have hhi : N < (s+1)*(s+1) := Nat.lt_succ_sqrt N
  have hp := smooth_mean_square_prefix (s-1)
  rw [Nat.sub_add_cancel hs] at hp
  have ht : |∑ k ∈ Ico (s*s) (N+1),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean)| ≤ 18*s := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    have hb := sum_le_sum (fun k (hk : k ∈ Ico (s*s) (N+1)) =>
      smooth_mean_point_bound (show 1 ≤ k by have := (mem_Ico.mp hk).1; nlinarith))
    have hc : (Ico (s*s) (N+1)).card ≤ 2*s+1 := by
      rw [Nat.card_Ico]
      have he : (s+1)*(s+1)=s*s+2*s+1 := by ring
      omega
    have hcR : ((Ico (s*s) (N+1)).card:ℝ) ≤ 2*s+1 := by exact_mod_cast hc
    simp only [sum_const,nsmul_eq_mul] at hb
    linarith only [hb,hcR,hsR]
  have hid : (∑ k ∈ Icc 1 N,divisorHyperbolaSmoothRemainder k)-divisorHyperbolaSmoothMean*N =
      ∑ k ∈ Ico 1 (N+1),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean) := by
    rw [Ico_add_one_right_eq_Icc,sum_sub_distrib]
    simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [hid,← sum_Ico_consecutive (show 1 ≤ s*s by nlinarith) (show s*s ≤ N+1 by omega) (f := fun k => divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean)]
  have h := abs_add_le
    (∑ k ∈ Ico 1 (s*s),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean))
    (∑ k ∈ Ico (s*s) (N+1),(divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean))
  have hsqrt := Real.nat_sqrt_le_real_sqrt (a := N)
  have hsub : ((s-1:ℕ):ℝ) ≤ s := by exact_mod_cast (show s-1 ≤ s by omega)
  change (s:ℝ) ≤ Real.sqrt N at hsqrt
  linarith only [h,hp,ht,hsqrt,hsub]

private theorem sqrt_mul_clock_gap_le {k : ℕ} (hk : 0<k) :
    Real.sqrt k*(halfOrderAbelStep 0 k-halfOrderAbelStep 0 (k+1))≤1/(4*(k:ℝ)) := by
  rw [halfOrderAbelStep_gap_eq]
  simp only [Nat.zero_add]
  have h1 : Real.sqrt k≤Real.sqrt (k+1:ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast (show k≤k+1 by omega))
  have h2 : Real.sqrt k≤Real.sqrt (k+2:ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast (show k≤k+2 by omega))
  have hden : (2*Real.sqrt k)^3 ≤
      (Real.sqrt k+Real.sqrt (k+1:ℕ))*(Real.sqrt (k+1:ℕ)+Real.sqrt (k+2:ℕ))*
      (Real.sqrt k+Real.sqrt (k+2:ℕ)) := by
    have h := mul_le_mul (mul_le_mul
      (by linarith only [h1] : 2*Real.sqrt k≤Real.sqrt k+Real.sqrt (k+1:ℕ))
      (by linarith only [h1,h2] : 2*Real.sqrt k≤Real.sqrt (k+1:ℕ)+Real.sqrt (k+2:ℕ))
      (by positivity) (by positivity))
      (by linarith only [h2] : 2*Real.sqrt k≤Real.sqrt k+Real.sqrt (k+2:ℕ))
      (by positivity) (by positivity)
    nlinarith only [h]
  have hs := congrArg (fun x : ℝ => 8*Real.sqrt k*x) (Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k))
  rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hden,hs]

/-- The actual smooth half-order source has its exact square-root coefficient with logarithmic error. -/
theorem divisorHyperbolaSmoothAbel_mean_error (M : ℕ) :
    |divisorHyperbolaSmoothAbel M-divisorHyperbolaSmoothMean*Real.sqrt M| ≤
      9*Real.log ((M:ℝ)+1)+25+|divisorHyperbolaSmoothMean| := by
  have hlog0 := Real.log_nonneg (show (1:ℝ) ≤ (M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  by_cases hM : M ≤ 1
  · have hz : divisorHyperbolaSmoothAbel M=0 := by
      interval_cases M <;> norm_num [divisorHyperbolaSmoothAbel,divisorHyperbolaSmoothRemainder]
    have hr : Real.sqrt M ≤ 1 := by simpa using Real.sqrt_le_sqrt (show (M:ℝ) ≤ 1 by exact_mod_cast hM)
    rw [hz,zero_sub,abs_neg,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    have h := mul_le_mul_of_nonneg_left hr (abs_nonneg divisorHyperbolaSmoothMean)
    linarith only [h,hlog0]
  let N := M-1
  let w := halfOrderAbelStep 0
  let f := fun k => divisorHyperbolaSmoothRemainder k-divisorHyperbolaSmoothMean
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hMN : N+1=M := by dsimp [N]; omega
  have hpre (n : ℕ) : |∑ k ∈ Icc 1 n,f k| ≤ 33*Real.sqrt n := by
    have h := sum_divisorHyperbolaSmooth_mean_error n
    simpa only [f,sum_sub_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_comm] using h
  have hg (k : ℕ) : 0 ≤ w k-w (k+1) :=
    sub_nonneg.mpr (halfOrderAbelStep_antitone 0 (show k ≤ k+1 by omega))
  have hs : |∑ k ∈ Icc 1 N,(∑ j ∈ Icc 1 k,f j)*(w k-w (k+1))| ≤
      33*(∑ k ∈ Icc 1 N,Real.sqrt k*(w k-w (k+1))) := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    rw [abs_mul,abs_of_nonneg (hg k)]
    have h := mul_le_mul_of_nonneg_right (hpre k) (hg k)
    linarith only [h]
  have ht : |(∑ j ∈ Icc 1 N,f j)*w (N+1)| ≤ 33*Real.sqrt N*w (N+1) := by
    rw [abs_mul,abs_of_nonneg (halfOrderAbelStep_nonneg 0 (N+1))]
    exact mul_le_mul_of_nonneg_right (hpre N) (halfOrderAbelStep_nonneg 0 (N+1))
  have hb := sum_le_sum (fun k (hk : k ∈ Icc 1 N) =>
    sqrt_mul_clock_gap_le (show 0<k by have := (mem_Icc.mp hk).1; omega))
  have hrec : (∑ k ∈ Icc 1 N,1/(4*(k:ℝ)))=((harmonic N:ℚ):ℝ)/4 := by
    simp_rw [show ∀ k : ℕ,1/(4*(k:ℝ))=(1/(k:ℝ))/4 by intro k; ring]
    rw [← sum_div]
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [hrec] at hb
  have hrootclock : Real.sqrt N*w (N+1) ≤ 1/2 := by
    have h0 := mul_le_mul_of_nonneg_left (halfOrderAbelStep_antitone 0 (show N ≤ N+1 by omega)) (Real.sqrt_nonneg (N:ℝ))
    have h1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (N+1))
    have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have h3 := sq_nonneg (w N)
    dsimp [w,halfOrderAbelStep] at h0 h3 ⊢
    push_cast at h0 h1 h2 h3 ⊢
    simp only [zero_add] at h0 h3 ⊢
    nlinarith only [h0,h1,h2,h3]
  have hab := sum_mul_eq_partial_mul_diff_ring f w N
  have hw : (∑ k ∈ Icc 1 N,w k)=Real.sqrt M-1 := by
    have h := sum_sqrt_succ_sub_sqrt_Icc_general hN
    simpa only [w,halfOrderAbelStep,Nat.zero_add,hMN,Nat.cast_one,Real.sqrt_one] using h
  have hSmooth : (∑ k ∈ Icc 1 N,divisorHyperbolaSmoothRemainder k*w k)=divisorHyperbolaSmoothAbel M := by
    rw [← Ico_add_one_right_eq_Icc,hMN,sum_Ico_eq_sub _ (show 1 ≤ M by omega)]
    have hz : divisorHyperbolaSmoothRemainder 0=0 := by norm_num [divisorHyperbolaSmoothRemainder]
    simp only [sum_range_one,hz,zero_mul,sub_zero,divisorHyperbolaSmoothAbel,w]
  have hleft : (∑ k ∈ Icc 1 N,f k*w k)=
      divisorHyperbolaSmoothAbel M-divisorHyperbolaSmoothMean*(Real.sqrt M-1) := by
    simp only [f,sub_mul,sum_sub_distrib,← mul_sum]
    rw [hSmooth,hw]
  have hH : ((harmonic N:ℚ):ℝ) ≤ 1+Real.log ((M:ℝ)+1) := by
    have hl := Real.log_le_log (show (0:ℝ)<N by positivity)
      (show (N:ℝ) ≤ (M:ℝ)+1 by exact_mod_cast (show N ≤ M+1 by omega))
    linarith only [hl,harmonic_le_one_add_log N]
  have habs := abs_add_le
    (∑ k ∈ Icc 1 N,(∑ j ∈ Icc 1 k,f j)*(w k-w (k+1)))
    ((∑ j ∈ Icc 1 N,f j)*w (N+1))
  rw [hleft] at hab
  rw [← hab] at habs
  have htri := abs_sub (divisorHyperbolaSmoothAbel M-divisorHyperbolaSmoothMean*(Real.sqrt M-1)) divisorHyperbolaSmoothMean
  have he : divisorHyperbolaSmoothAbel M-divisorHyperbolaSmoothMean*(Real.sqrt M-1)-divisorHyperbolaSmoothMean =
      divisorHyperbolaSmoothAbel M-divisorHyperbolaSmoothMean*Real.sqrt M := by ring
  rw [he] at htri
  change _ ≤ (harmonic N:ℝ)/4 at hb
  change (∑ k ∈ Icc 1 N,Real.sqrt k*(w k-w (k+1))) ≤ _ at hb
  nlinarith only [htri,habs,hs,ht,hb,hrootclock,hH,hlog0]

private theorem eventually_log_add_one_le_sqrt (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop,Real.log ((M:ℝ)+1)+1≤ε*Real.sqrt M := by
  have hlog : Tendsto (fun M : ℕ => Real.log M/Real.sqrt M) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)
  have hroot : Tendsto (fun M : ℕ => Real.sqrt M) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hroot
  have hlim : Tendsto (fun M : ℕ => (Real.log M+2)/Real.sqrt M) atTop (𝓝 0) := by
    have h := hlog.add (hinv.const_mul 2)
    simpa only [Function.comp_def,mul_zero,zero_add,add_div,div_eq_mul_inv,add_mul] using h
  have hev : ∀ᶠ M : ℕ in atTop,(Real.log M+2)/Real.sqrt M<ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hev,eventually_ge_atTop 1] with M hsmall hM
  have hMp : (0:ℝ)<M := by positivity
  have hrootp : 0<Real.sqrt M := Real.sqrt_pos.mpr hMp
  have hlog' := Real.log_le_sub_one_of_pos (x := ((M:ℝ)+1)/M) (by positivity)
  rw [Real.log_div (by positivity) hMp.ne'] at hlog'
  have hrat : ((M:ℝ)+1)/M-1≤1 := by
    rw [sub_le_iff_le_add,div_le_iff₀ hMp]
    have : (1:ℝ)≤M := by exact_mod_cast hM
    linarith only [this]
  have hm := (div_lt_iff₀ hrootp).mp hsmall
  linarith only [hm,hlog',hrat]

/-- The exact smooth mean has the strict margin needed by the factor-two comparison. -/
theorem divisorHyperbolaSmoothMean_gt_one_sixth : 1/6 < divisorHyperbolaSmoothMean := by
  have hlim := ((Real.continuousAt_log (show Real.sqrt Real.pi ≠ 0 by positivity)).tendsto).comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hc : 1-(12:ℝ)⁻¹-Real.log 2/2 ≤ Real.log (Real.sqrt Real.pi) :=
    ge_of_tendsto hlim (Eventually.of_forall Stirling.log_stirlingSeq_bounded_by_constant)
  rw [Real.log_sqrt Real.pi_pos.le] at hc
  have hg := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  unfold divisorHyperbolaSmoothMean
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  norm_num at hc
  linarith only [hc,hg]

/-- The complete unit source has matching exact-mean bounds with logarithmic error. -/
theorem divisorUnsignedDilationChannel_one_exact_mean_bounds (M : ℕ) :
    (divisorHyperbolaSmoothMean-5/48)*Real.sqrt M-
        10*Real.log ((M:ℝ)+1)-26-|divisorHyperbolaSmoothMean| ≤ divisorUnsignedDilationChannel M 1 ∧
    divisorUnsignedDilationChannel M 1 ≤ (divisorHyperbolaSmoothMean-1/24)*Real.sqrt M+
        10*Real.log ((M:ℝ)+1)+26+|divisorHyperbolaSmoothMean| := by
  have hs := (abs_le.mp (divisorHyperbolaSmoothAbel_mean_error M))
  have hc := centeredDivisorHyperbolaAbel_sqrt_log_bounds M
  have hid := mobiusDivisorDilationChannel_one_eq_hyperbola M
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned] at hid
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul] at hid
  have hl := Real.log_nonneg (show (1:ℝ) ≤ (M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  constructor <;> nlinarith only [hs.1,hs.2,hc.1,hc.2,hid,hl]

/-- The exact-mean coefficient band holds on a common tail of all unit cutoffs. -/
theorem eventually_divisorUnsignedDilationChannel_one_exact_mean_bounds (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      (divisorHyperbolaSmoothMean-5/48-ε)*Real.sqrt M ≤ divisorUnsignedDilationChannel M 1 ∧
      divisorUnsignedDilationChannel M 1 ≤ (divisorHyperbolaSmoothMean-1/24+ε)*Real.sqrt M := by
  let C := 36+|divisorHyperbolaSmoothMean|
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_log_add_one_le_sqrt (ε/C) (by positivity)] with M hM
  have hb := divisorUnsignedDilationChannel_one_exact_mean_bounds M
  have hl := Real.log_nonneg (show (1:ℝ) ≤ (M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith)
  have hp := mul_nonneg (abs_nonneg divisorHyperbolaSmoothMean) hl
  have he : C*((ε/C)*Real.sqrt M)=ε*Real.sqrt M := by field_simp
  have hm := mul_le_mul_of_nonneg_left hM hC.le
  rw [he] at hm
  dsimp only [C] at hm
  constructor <;> nlinarith only [hb.1,hb.2,hm,hl,hp,abs_nonneg divisorHyperbolaSmoothMean]

/-- Factor-two dilation control is unconditional once the quotient is sufficiently large; the clipped terminal clock is retained. -/
theorem exists_divisorUnsignedDilationChannel_large_quotient_factor_two :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M p : ℕ, 0 < p → T ≤ M/p →
      divisorUnsignedDilationChannel M p ≤ 2*divisorUnsignedDilationChannel M 1 := by
  let a := divisorHyperbolaSmoothMean
  let ε := (a-1/6)/4
  have hε : 0 < ε := by dsimp [ε,a]; linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_divisorUnsignedDilationChannel_one_exact_mean_bounds ε hε)
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro M p hp hMp
  have hN : T ≤ M/p := (le_max_left _ _).trans hMp
  have hM : T ≤ M := hN.trans (Nat.div_le_self M p)
  have hN1 : T ≤ M/p+1 := by omega
  let U := a-1/24+ε
  let L := a-5/48-ε
  have hUM : divisorUnsignedDilationChannel M p ≤ U*Real.sqrt M := by
    have hw0 := divisorPrimeClipWeight_nonneg M p hp
    have hw1 : 0 ≤ 1-divisorPrimeClipWeight M p := by
      have h := divisorPrimeClipWeight_lt_one M p hp; linarith only [h]
    have hA := mul_le_mul_of_nonneg_left (hT (M/p) hN).2 hw1
    have hB := mul_le_mul_of_nonneg_left (hT (M/p+1) hN1).2 hw0
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hA hB) (Real.sqrt_nonneg (p:ℝ))
    have hc := divisorUnsignedDilationChannel_prime_interpolation M p 1 hp
    simp only [Nat.mul_one] at hc
    have hclock := divisorPrimeClipWeight_mul_step M p hp
    push_cast at hclock
    rw [Real.sqrt_mul (Nat.cast_nonneg p)] at hclock
    rw [hc]
    dsimp only [U,a]
    push_cast at hsum ⊢
    have he := congrArg (fun x : ℝ => U*x) hclock
    dsimp only [U,a] at he
    nlinarith only [hsum,he]
  have hLM : L*Real.sqrt M ≤ divisorUnsignedDilationChannel M 1 := (hT M hM).1
  have hgap : U ≤ 2*L := by
    dsimp [U,L,ε,a]
    linarith only [divisorHyperbolaSmoothMean_gt_one_sixth]
  have hm := mul_le_mul_of_nonneg_right hgap (Real.sqrt_nonneg (M:ℝ))
  nlinarith only [hUM,hLM,hm]

/-- Any actual factor-two failure has bounded quotient, uniformly in cutoff and dilation. -/
theorem exists_divisorUnsignedDilationChannel_factor_two_failure_quotient_bound :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M p : ℕ, 0 < p →
      2*divisorUnsignedDilationChannel M 1 < divisorUnsignedDilationChannel M p → M/p < T := by
  obtain ⟨T,hT,h⟩ := exists_divisorUnsignedDilationChannel_large_quotient_factor_two
  refine ⟨T,hT,?_⟩
  intro M p hp hfail
  by_contra hn
  have hb := h M p hp (by omega)
  linarith only [hb,hfail]
/-- A universal quotient bound localizes every possible original two-prime ceiling failure to bounded quotient profiles. -/
theorem exists_mobiusDivisorSelectionEnergy_two_prime_bounded_quotient_obstruction :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ (M p q : ℕ), p.Prime → q.Prime → p<M → q<M → p≠q →
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ ∨
      ∃ N r : ℕ, r<N ∧ N ≤ M ∧ (r=p ∨ r=q) ∧ N/r<T ∧
        2*divisorUnsignedDilationChannel N 1 < divisorUnsignedDilationChannel N r := by
  obtain ⟨T,hT,hbound⟩ := exists_divisorUnsignedDilationChannel_factor_two_failure_quotient_bound
  refine ⟨T,hT,?_⟩
  intro M p q hp hq hpM hqM hpq
  rcases mobiusDivisorSelectionEnergy_two_primes_le_or_unit_failure M hp hq hpM hqM hpq with h | ⟨N,r,hrN,hNM,hr,hfail⟩
  · exact Or.inl h
  · have hrpos : 0<r := hr.elim (fun h => h ▸ hp.pos) (fun h => h ▸ hq.pos)
    exact Or.inr ⟨N,r,hrN,hNM,hr,hbound N r hrpos hfail,hfail⟩

end RHTower
