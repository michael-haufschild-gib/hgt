import GaloisForLFunctions.RHTower.MobiusDivisorCurrentClockPayment
import GaloisForLFunctions.RHTower.MobiusDivisorAbelDiagonalBound
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual prime batches pay growing cutoff intervals

Literal divisor-defect increments give a total source variation bound
`24 (L-M) sqrt L`, uniformly over every processed core. Extending both
cutoffs to the complete squarefree field retains all newly active coordinates.
Weighted square expansion then pays their mixed terms and self-energy.

A fourth-root cutoff interval costs `o(M^2)` on every bounded logarithmic
energy budget, with a threshold independent of the processed core. Actual
current-clock prime batches supply that budget and the payment: all batch
prefixes retain full weighted control, and the endpoint preserves half the
quadratic reserve throughout the interval.

This does not supply growing-depth omitted-prime payment or an exhaustive
prime/clock schedule.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

private lemma channel_zero {M d : ℕ} (hd : 0<d) (hMd : M ≤ d) :
    mobiusDivisorDilationChannel M d=0 := by
  simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (show M-1<d by omega)]

private lemma channel_step {M d : ℕ} (hd : 1 ≤ d) :
    |mobiusDivisorDilationChannel (M+1) d-mobiusDivisorDilationChannel M d| ≤
      12 / Real.sqrt d := by
  by_cases hdM : d ≤ M
  · rw [mobiusDivisorDilationChannel_succ_of_le hd hdM,add_sub_cancel_left]
    have hstep : 0 ≤ Real.sqrt (M+1:ℕ)-Real.sqrt M :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ M))
    have hhalf : (Real.sqrt (M+1:ℕ)-Real.sqrt M)*Real.sqrt M ≤ 1/2 := by
      have h0 := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
      have h1 := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) (M+1))
      have h2 := sq_nonneg (Real.sqrt (M+1:ℕ)-Real.sqrt M)
      push_cast at h1 h2 ⊢
      nlinarith only [h0,h1,h2]
    have hD := abs_primeFreeDivisorDefect_le
      ((Nat.le_div_iff_mul_le (by omega : 0<d)).mpr (by simpa using hdM))
    have hroot : Real.sqrt d*Real.sqrt (M/d:ℕ) ≤ Real.sqrt M := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show d*(M/d) ≤ M by simpa [mul_comm] using Nat.div_mul_le_self M d)
    have hscaled : Real.sqrt d*|primeFreeDivisorDefect (M/d)| ≤ 24*Real.sqrt M := by
      have hh := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg d)
      nlinarith only [hh,hroot]
    have hbound := mul_le_mul_of_nonneg_left hscaled hstep
    have hmu : |((ArithmeticFunction.moebius d : ℤ):ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    rw [abs_mul,abs_mul,abs_of_nonneg hstep]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hd))).mpr
    have hh := mul_le_mul_of_nonneg_right hmu
      (show 0 ≤ (Real.sqrt (M+1:ℕ)-Real.sqrt M)*|primeFreeDivisorDefect (M/d)| * Real.sqrt d by positivity)
    nlinarith only [hbound,hhalf,hh]
  · rw [channel_zero hd (by omega),channel_zero hd (by omega),sub_self,abs_zero]
    positivity

private lemma channel_gap {M L d : ℕ} (hd : 1 ≤ d) (hML : M ≤ L) :
    |mobiusDivisorDilationChannel L d-mobiusDivisorDilationChannel M d| ≤
      12*((L:ℝ)-M)/Real.sqrt d := by
  induction L with
  | zero =>
    have hM : M=0 := by omega
    subst M
    simp
  | succ L ih =>
    by_cases h : M ≤ L
    · have hh := (abs_add_le (mobiusDivisorDilationChannel (L+1) d-mobiusDivisorDilationChannel L d)
        (mobiusDivisorDilationChannel L d-mobiusDivisorDilationChannel M d)).trans
        (add_le_add (channel_step hd) (ih h))
      rw [sub_add_sub_cancel] at hh
      calc
        _ ≤ 12/Real.sqrt d+12*((L:ℝ)-M)/Real.sqrt d := hh
        _ = _ := by push_cast; ring
    · have he : M=L+1 := by omega
      subst M
      simp

private lemma grouped_abs_le {ι κ : Type*} [DecidableEq ι]
    (T : Finset ι) (I : Finset κ) (a : κ → ι) (c : κ → ℝ) :
    (∑ R ∈ T, |∑ n ∈ I, if a n=R then c n else 0|) ≤ ∑ n ∈ I, |c n| := by
  calc
    _ ≤ ∑ R ∈ T, ∑ n ∈ I, |if a n=R then c n else 0| :=
      sum_le_sum (fun R _ => abs_sum_le_sum_abs _ _)
    _ = ∑ n ∈ I, ∑ R ∈ T, if a n=R then |c n| else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro R hR
      split_ifs <;> simp
    _ ≤ ∑ n ∈ I, |c n| := by
      apply sum_le_sum
      intro n hn
      simp only [sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _

private lemma fibre_extended (P R : Finset ℕ) {M L : ℕ} (hML : M ≤ L) :
    mobiusDivisorSelectionFibre M P R =
      ∑ d ∈ Icc 1 L, if d.primeFactors \ P=R then mobiusDivisorDilationChannel M d else 0 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  apply sum_subset
  · exact Icc_subset_Icc le_rfl hML
  · intro d hd hn
    have hd' := mem_Icc.mp hd
    have hMd : M ≤ d := by simp only [mem_Icc,not_and] at hn; have := hn hd'.1; omega
    simp [channel_zero hd'.1 hMd]

/-- All original source coordinates, including newly active ones, obey a
core-independent total variation bound between any two integer cutoffs. -/
theorem sum_abs_mobiusDivisorSelectionFibre_cutoff_sub_le
    (P : Finset ℕ) (T : Finset (Finset ℕ)) {M L : ℕ} (hML : M ≤ L) :
    (∑ R ∈ T, |mobiusDivisorSelectionFibre L P R-mobiusDivisorSelectionFibre M P R|) ≤
      24*((L:ℝ)-M)*Real.sqrt L := by
  have he (R : Finset ℕ) :
      mobiusDivisorSelectionFibre L P R-mobiusDivisorSelectionFibre M P R =
      ∑ d ∈ Icc 1 L, if d.primeFactors \ P=R then
        mobiusDivisorDilationChannel L d-mobiusDivisorDilationChannel M d else 0 := by
    rw [fibre_extended P R le_rfl,fibre_extended P R hML,← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    split_ifs <;> simp
  simp_rw [he]
  apply (grouped_abs_le T (Icc 1 L) (fun d => d.primeFactors \ P)
    (fun d => mobiusDivisorDilationChannel L d-mobiusDivisorDilationChannel M d)).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 L, 12*((L:ℝ)-M)/Real.sqrt d :=
      sum_le_sum (fun d hd => channel_gap (mem_Icc.mp hd).1 hML)
    _ = 12*((L:ℝ)-M)*(∑ d ∈ Icc 1 L, 1/Real.sqrt d) := by
      simp only [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le L)
        (show 0 ≤ 12*((L:ℝ)-M) by
          have : (M:ℝ) ≤ L := by exact_mod_cast hML
          positivity)
      nlinarith only [h]

private lemma square_as_fibre (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hs : Squarefree r) (hd : Disjoint r.primeFactors P) :
    (r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 =
      (mobiusDivisorSelectionFibre M P r.primeFactors)^2 := by
  have h := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hs] at h
  have hm : (((ArithmeticFunction.moebius r : ℤ):ℝ))^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
  rw [h,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg r),hm,mul_one]

private lemma sample_vanish (P : Finset ℕ) {M r : ℕ} (hr : 0<r) (hMr : M ≤ r) :
    mobiusDivisorInterpolatedFibre M r P ∅=0 := by
  have h0 : mobiusDivisorSelectionFibre 0 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  rcases hMr.eq_or_lt with rfl | hlt
  · have hw : divisorPrimeClipWeight M M=0 := by simp [divisorPrimeClipWeight,Nat.div_self hr]
    simp [mobiusDivisorInterpolatedFibre,Nat.div_self hr,hw,h1]
  · simp [mobiusDivisorInterpolatedFibre,Nat.div_eq_of_lt hlt,h0,h1]

private lemma clock_extended (P : Finset ℕ) {M L : ℕ} (hML : M ≤ L) :
    mobiusDivisorFiniteClockEnergy 1 M P =
      ∑ r ∈ fixedCoreSquarefreeIndices P L,
        (1+Real.log r)*(mobiusDivisorSelectionFibre M P r.primeFactors)^2 := by
  unfold mobiusDivisorFiniteClockEnergy
  calc
    _ = ∑ r ∈ fixedCoreSquarefreeIndices P M,
        (1+Real.log r)*(mobiusDivisorSelectionFibre M P r.primeFactors)^2 := by
      apply sum_congr rfl
      intro r hr
      obtain ⟨_,hs,hd⟩ := mem_filter.mp hr
      rw [mul_assoc,square_as_fibre P M hs hd]
    _ = _ := by
      apply sum_subset
      · intro r hr
        obtain ⟨hr,hs⟩ := mem_filter.mp hr
        exact mem_filter.mpr ⟨Icc_subset_Icc le_rfl hML hr,hs⟩
      · intro r hr hn
        obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
        have hr' := mem_Icc.mp hr
        have hMr : M ≤ r := by
          by_contra h
          exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,by omega⟩,hs,hd⟩)
        rw [← square_as_fibre P M hs hd,sample_vanish P hr'.1 hMr]
        simp

/-- Complete weighted cutoff transport. Its error includes both mixed terms
and all new-coordinate self-energy, uniformly in the processed core. -/
theorem mobiusDivisorFiniteClockEnergy_cutoff_le
    (P : Finset ℕ) {M L : ℕ} (hML : M ≤ L) (hL : 1 ≤ L)
    {ε : ℝ} (hε : 0<ε) :
    mobiusDivisorFiniteClockEnergy 1 L P ≤
      (1+ε)*mobiusDivisorFiniteClockEnergy 1 M P+
        (1+1/ε)*(1+Real.log L)*(24*((L:ℝ)-M)*Real.sqrt L)^2 := by
  let S := fixedCoreSquarefreeIndices P L
  let f := fun r : ℕ => mobiusDivisorSelectionFibre M P r.primeFactors
  let g := fun r => mobiusDivisorSelectionFibre L P r.primeFactors-f r
  have hinj : Set.InjOn Nat.primeFactors (↑S) := by
    intro r hr s hs he
    have h := congrArg (fun V : Finset ℕ => ∏p ∈ V,p) he
    simpa only [Nat.prod_primeFactors_of_squarefree (mem_filter.mp hr).2.1,
      Nat.prod_primeFactors_of_squarefree (mem_filter.mp hs).2.1] using h
  have hgap := sum_abs_mobiusDivisorSelectionFibre_cutoff_sub_le P (S.image Nat.primeFactors) hML
  rw [sum_image hinj] at hgap
  have hsq := sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun r=>|g r|) (fun _ _=>abs_nonneg _)
  simp only [sq_abs] at hsq
  have hB : 0 ≤ 24*((L:ℝ)-M)*Real.sqrt L := by
    have : (M:ℝ) ≤ L := by exact_mod_cast hML
    positivity
  have hgg : (∑r ∈ S,(g r)^2) ≤ (24*((L:ℝ)-M)*Real.sqrt L)^2 :=
    hsq.trans ((sq_le_sq₀ (sum_nonneg (fun _ _=>abs_nonneg _)) hB).mpr hgap)
  have point (r : ℕ) : (f r+g r)^2 ≤ (1+ε)*(f r)^2+(1+1/ε)*(g r)^2 := by
    have hh := sq_nonneg (ε*f r-g r)
    have hh' : ε*((1+ε)*(f r)^2+(1+1/ε)*(g r)^2-(f r+g r)^2)=
        (ε*f r-g r)^2 := by field_simp [hε.ne']; ring
    have hd : 0 ≤ (1+ε)*(f r)^2+(1+1/ε)*(g r)^2-(f r+g r)^2 := by
      by_contra hn
      have ht := mul_neg_of_pos_of_neg hε (lt_of_not_ge hn)
      rw [hh'] at ht
      linarith only [hh,ht]
    linarith only [hd]
  have hlog : 0 ≤ 1+Real.log (L:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ L by exact_mod_cast hL)
    linarith
  rw [clock_extended P le_rfl,clock_extended P hML]
  change (∑r ∈ S,(1+Real.log r)*(mobiusDivisorSelectionFibre L P r.primeFactors)^2) ≤ _
  calc
    _ ≤ ∑r ∈ S, (1+Real.log r)*((1+ε)*(f r)^2+(1+1/ε)*(g r)^2) := by
      apply sum_le_sum
      intro r hr
      have hr1 := (mem_Icc.mp (mem_filter.mp hr).1).1
      have hw : 0 ≤ 1+Real.log (r:ℝ) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ r by exact_mod_cast hr1); linarith
      have hh := mul_le_mul_of_nonneg_left (point r) hw
      simpa only [f,g,add_sub_cancel] using hh
    _ = (1+ε)*(∑r ∈ S,(1+Real.log r)*(f r)^2)+
        (1+1/ε)*(∑r ∈ S,(1+Real.log r)*(g r)^2) := by
      simp only [mul_add,sum_add_distrib,mul_sum]; congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ (1+ε)*(∑r ∈ S,(1+Real.log r)*(f r)^2)+
        (1+1/ε)*((1+Real.log L)*(∑r ∈ S,(g r)^2)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [mul_sum]
      apply sum_le_sum
      intro r hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add le_rfl
      exact Real.log_le_log (by exact_mod_cast hr'.1) (by exact_mod_cast hr'.2)
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgg hlog)
          (by positivity : 0 ≤ 1+1/ε)

private lemma clock_cutoff_fourth_root (P : Finset ℕ) {M L : ℕ}
    (hM : 1 ≤ M) (hML : M ≤ L) {C : ℝ} (hC : 0 ≤ C)
    (hW : mobiusDivisorFiniteClockEnergy 1 M P ≤ C*(M:ℝ)^2*(1+Real.log M))
    (hgap : (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M)) :
    mobiusDivisorFiniteClockEnergy 1 L P ≤ mobiusDivisorFiniteClockEnergy 1 M P+
      (C+2304)*(M:ℝ)^2*(1+Real.log (2*M:ℝ))/Real.sqrt (Real.sqrt M) := by
  let u := Real.sqrt (Real.sqrt M)
  let s := Real.sqrt M
  let w := 1+Real.log (2*M:ℝ)
  let B := 24*((L:ℝ)-M)*Real.sqrt L
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hs : s^2=(M:ℝ) := Real.sq_sqrt (Nat.cast_nonneg M)
  have hu : u^2=s := Real.sq_sqrt (Real.sqrt_nonneg M)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hMr
  have hu1 : 1 ≤ u := Real.one_le_sqrt.mpr hs1
  have hu0 : 0<u := by linarith only [hu1]
  have hum : u ≤ (M:ℝ) := by
    have hus : u ≤ s := by nlinarith only [hu,hu1]
    have hsm : s ≤ (M:ℝ) := by nlinarith only [hs,hs1]
    exact hus.trans hsm
  have hLM : (L:ℝ) ≤ 2*M := by change _ ≤ u at hgap; linarith only [hgap,hum]
  have hMLr : (M:ℝ) ≤ L := by exact_mod_cast hML
  have hL : 1 ≤ L := hM.trans hML
  have hw : 0 ≤ w := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*M by linarith only [hMr])
    dsimp [w]; linarith
  have hwL : 0 ≤ 1+Real.log (L:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ L by exact_mod_cast hL)
    linarith
  have hlogL : 1+Real.log (L:ℝ) ≤ w :=
    add_le_add le_rfl (Real.log_le_log (by exact_mod_cast hL) hLM)
  have hlogM : 1+Real.log (M:ℝ) ≤ w :=
    add_le_add le_rfl (Real.log_le_log (by exact_mod_cast hM) (by linarith only [hMr]))
  have hgap2 : ((L:ℝ)-M)^2 ≤ s := by
    have hh := (sq_le_sq₀ (sub_nonneg.mpr hMLr) hu0.le).mpr hgap
    exact hh.trans_eq hu
  have hB : B^2 ≤ 1152*(M:ℝ)*s := by
    calc
      B^2=576*((L:ℝ)-M)^2*(L:ℝ) := by
        dsimp [B]
        rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg L)]
        ring
      _ ≤ 576*s*(2*M) := by gcongr
      _ = _ := by ring
  have huu : u*(1+u) ≤ 2*s := by nlinarith only [hu,hu1]
  have herr : (1+u)*(1+Real.log L)*B^2 ≤ 2304*(M:ℝ)^2*w/u := by
    apply (le_div_iff₀ hu0).mpr
    calc
      _ = (1+Real.log L)*(u*(1+u))*B^2 := by ring
      _ ≤ w*(2*s)*(1152*(M:ℝ)*s) := by gcongr
      _ = _ := by
        rw [show w*(2*s)*(1152*(M:ℝ)*s)=2304*(M:ℝ)*w*s^2 by ring,hs]
        ring
  have hW' : mobiusDivisorFiniteClockEnergy 1 M P ≤ C*(M:ℝ)^2*w :=
    hW.trans (mul_le_mul_of_nonneg_left hlogM (by positivity))
  have h := mobiusDivisorFiniteClockEnergy_cutoff_le P hML hL
    (show 0<1/u by positivity)
  have hWdiv := div_le_div_of_nonneg_right hW' hu0.le
  change _ ≤ (1+1/u)*mobiusDivisorFiniteClockEnergy 1 M P+
    (1+1/(1/u))*(1+Real.log L)*B^2 at h
  rw [one_div_one_div] at h
  change _ ≤ _+(C+2304)*(M:ℝ)^2*w/u
  calc
    _ ≤ (1+1/u)*mobiusDivisorFiniteClockEnergy 1 M P+2304*(M:ℝ)^2*w/u :=
      h.trans (add_le_add le_rfl herr)
    _ = mobiusDivisorFiniteClockEnergy 1 M P+mobiusDivisorFiniteClockEnergy 1 M P/u+
        2304*(M:ℝ)^2*w/u := by ring
    _ ≤ mobiusDivisorFiniteClockEnergy 1 M P+C*(M:ℝ)^2*w/u+
        2304*(M:ℝ)^2*w/u := by linarith only [hWdiv]
    _ = _ := by ring

private lemma fourth_root_eq (M : ℕ) :
    Real.sqrt (Real.sqrt M)=(M:ℝ)^(1/4:ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg (α:=ℝ) M)]
  norm_num

private lemma clock_fourth_root_ratio_zero :
    Tendsto (fun M : ℕ => (1+Real.log (2*M:ℝ))/Real.sqrt (Real.sqrt M)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ => (M:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun M : ℕ => (1+Real.log 2)/(M:ℝ)^(1/4:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using hpow.inv_tendsto_atTop.const_mul (1+Real.log 2)
  have hlog : Tendsto (fun M : ℕ => Real.log (M:ℝ)/(M:ℝ)^(1/4:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  apply (show Tendsto (fun M : ℕ => (1+Real.log 2)/(M:ℝ)^(1/4:ℝ)+
      Real.log (M:ℝ)/(M:ℝ)^(1/4:ℝ)) atTop (𝓝 0) from by simpa using hconst.add hlog).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  rw [fourth_root_eq,Real.log_mul (by norm_num) (by exact_mod_cast (show M≠0 by omega))]
  ring

/-- A fourth-root interval of literal cutoffs costs arbitrarily little on the
quadratic payment scale. The threshold is uniform over every processed core. -/
theorem eventually_mobiusDivisorFiniteClockEnergy_fourth_root_transport
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0<δ) :
    ∀ᶠ M : ℕ in atTop, ∀P : Finset ℕ,
      mobiusDivisorFiniteClockEnergy 1 M P ≤ C*(M:ℝ)^2*(1+Real.log M) →
      ∀L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
        mobiusDivisorFiniteClockEnergy 1 L P ≤ mobiusDivisorFiniteClockEnergy 1 M P+δ*(M:ℝ)^2 := by
  have ht : Tendsto (fun M : ℕ =>
      (C+2304)*((1+Real.log (2*M:ℝ))/Real.sqrt (Real.sqrt M))) atTop (𝓝 0) := by
    simpa using clock_fourth_root_ratio_zero.const_mul (C+2304)
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (gt_mem_nhds hδ)] with M hM hsmall
  intro P hW L hML hgap
  have h := clock_cutoff_fourth_root P hM hML hC hW hgap
  have hh := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg (M:ℝ))
  have he : (C+2304)*(M:ℝ)^2*(1+Real.log (2*M:ℝ))/Real.sqrt (Real.sqrt M)=
      ((C+2304)*((1+Real.log (2*M:ℝ))/Real.sqrt (Real.sqrt M)))*(M:ℝ)^2 := by ring
  rw [he] at h
  exact h.trans (add_le_add le_rfl hh)

private lemma clock_source_bound (P : Finset ℕ) (hP : ∀p ∈ P,p.Prime) {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorFiniteClockEnergy 1 M P ≤
      ((3/5:ℝ)*2^(P.card-1))^2*(M:ℝ)^2*(1+Real.log M) := by
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  have hlog : 0 ≤ 1+Real.log (M:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ M by exact_mod_cast hM); linarith
  have hcard : (fixedCoreSquarefreeIndices P M).card ≤ M := by
    have hh := card_le_card (filter_subset (fun r => Squarefree r ∧ Disjoint r.primeFactors P) (Icc 1 M))
    simpa [fixedCoreSquarefreeIndices,Nat.card_Icc] using hh
  rw [clock_extended P le_rfl]
  calc
    _ ≤ ∑r ∈ fixedCoreSquarefreeIndices P M, (1+Real.log M)*D^2*(M:ℝ) := by
      apply sum_le_sum
      intro r hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      have hw : 0 ≤ 1+Real.log (r:ℝ) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ r by exact_mod_cast hr'.1); linarith
      have ha := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
      have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ D*Real.sqrt M by dsimp [D]; positivity)).mpr ha
      simp only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)] at hs
      have hh := mul_le_mul_of_nonneg_left hs hw
      calc
        _ ≤ (1+Real.log r)*(D^2*(M:ℝ)) := hh
        _ ≤ (1+Real.log M)*(D^2*(M:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply add_le_add le_rfl
          exact Real.log_le_log (by exact_mod_cast hr'.1) (by exact_mod_cast hr'.2)
        _ = _ := by ring
    _ ≤ (M:ℝ)*((1+Real.log M)*D^2*(M:ℝ)) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- Actual current-clock prime batches pay a growing interval of original
cutoffs. Every batch prefix retains complete weighted energy control as its
core and cutoff change, including every new coordinate and self-square.
No payment, source-sign, or energy-bound premise is assumed. -/
theorem eventually_exists_mobiusDivisorInitialClockPayment_cutoff_interval :
    ∃ b : ℕ, ∃ R δ : ℝ, 15 ≤ b ∧ 0 < R ∧ 0 < δ ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 14*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        ∃ l : List ℕ, l.Nodup ∧ l.length=mobiusDivisorCoupledTwoCapacity b N-1 ∧
          l.toFinset ⊆ mobiusDivisorCoupledTwoPool b N ∧
          (∀ k : ℕ, mobiusDivisorFiniteClockEnergy 1 M (P∪(l.take k).toFinset) ≤
            mobiusDivisorFiniteClockEnergy 1 M P+R^2*M) ∧
          (∀ k L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
            mobiusDivisorFiniteClockEnergy 1 L (P∪(l.take k).toFinset) ≤
              mobiusDivisorFiniteClockEnergy 1 M P+R^2*M+δ*(M:ℝ)^2) ∧
          (mobiusDivisorSelectionFibre M (P∪l.toFinset) ∅)^2+
            (1+Real.log 2)*(mobiusDivisorSelectionFibre M (P∪l.toFinset) {2})^2 ≤ R^2*M ∧
          ∀ L : ℕ, M ≤ L → (L:ℝ)-M ≤ Real.sqrt (Real.sqrt M) →
            mobiusDivisorFiniteClockEnergy 1 L (P∪l.toFinset)+
              (mobiusDivisorSelectionFibre M P ∅)^2+
              (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2+
              δ*(M:ℝ)^2 ≤ mobiusDivisorFiniteClockEnergy 1 M P := by
  obtain ⟨b,R,δ,hb,hR,hδ,hproduce⟩ := eventually_exists_mobiusDivisorInitialClockPayment
  let P := mobiusDivisorCoupledTwoCore
  let D : ℝ := (3/5:ℝ)*2^(P.card-1)
  let C : ℝ := D^2+R^2
  have hC : 0 ≤ C := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hprime : ∀p ∈ P,p.Prime := fun p hp => (mem_filter.mp (mem_erase.mp hp).2).2
  have hclock : Tendsto (fun N : ℕ => 14*(b+1)*N) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro N
    change N ≤ 14*(b+1)*N
    nlinarith
  have htransport := hclock.eventually
    (eventually_mobiusDivisorFiniteClockEnergy_fourth_root_transport C (δ/2) hC (by positivity))
  refine ⟨b,R,δ/2,hb,hR,by positivity,?_⟩
  filter_upwards [hproduce,htransport,eventually_ge_atTop (1:ℕ)] with N hprod htrans hN
  let M := 14*(b+1)*N
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨l,hnd,hlen,hpool,hprefix,hpair,hpay⟩ := hprod
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg hMr
  have hscale : (M:ℝ) ≤ (M:ℝ)^2*(1+Real.log M) := by
    have hh := mul_nonneg (sq_nonneg (M:ℝ)) hlogM
    nlinarith only [hMr,hh]
  have hbase : mobiusDivisorFiniteClockEnergy 1 M P+R^2*M ≤ C*(M:ℝ)^2*(1+Real.log M) := by
    have hs : mobiusDivisorFiniteClockEnergy 1 M P ≤ D^2*(M:ℝ)^2*(1+Real.log M) :=
      clock_source_bound P hprime hM
    calc
      _ ≤ D^2*(M:ℝ)^2*(1+Real.log M)+R^2*((M:ℝ)^2*(1+Real.log M)) :=
        add_le_add hs (mul_le_mul_of_nonneg_left hscale (sq_nonneg R))
      _ = _ := by dsimp [C]; ring
  refine ⟨l,hnd,hlen,hpool,hprefix,?_,hpair,?_⟩
  · intro k L hML hgap
    have ht := htrans (P∪(l.take k).toFinset) ((hprefix k).trans hbase) L hML hgap
    exact ht.trans (add_le_add (hprefix k) le_rfl)
  · intro L hML hgap
    have hlog : 0 ≤ 1+Real.log (2:ℝ) := by
      have := Real.log_pos (by norm_num : (1:ℝ)<2)
      linarith
    have hpair0 : 0 ≤ (mobiusDivisorSelectionFibre M P ∅)^2+
        (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2 := by positivity
    have hδsq : 0 ≤ δ*(M:ℝ)^2 := by positivity
    have hpad : 0 ≤ R^2*(M:ℝ) := by positivity
    change mobiusDivisorFiniteClockEnergy 1 M (P∪l.toFinset)+
      (mobiusDivisorSelectionFibre M P ∅)^2+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2+
      δ*(M:ℝ)^2 ≤ mobiusDivisorFiniteClockEnergy 1 M P at hpay
    have hW : mobiusDivisorFiniteClockEnergy 1 M (P∪l.toFinset) ≤ C*(M:ℝ)^2*(1+Real.log M) := by
      linarith only [hpay,hpair0,hδsq,hpad,hbase]
    have ht := htrans (P∪l.toFinset) hW L hML hgap
    change mobiusDivisorFiniteClockEnergy 1 L (P∪l.toFinset) ≤
      mobiusDivisorFiniteClockEnergy 1 M (P∪l.toFinset)+(δ/2)*(M:ℝ)^2 at ht
    change mobiusDivisorFiniteClockEnergy 1 L (P∪l.toFinset)+
      (mobiusDivisorSelectionFibre M P ∅)^2+
      (1+Real.log 2)*(mobiusDivisorSelectionFibre M P {2})^2+
      (δ/2)*(M:ℝ)^2 ≤ mobiusDivisorFiniteClockEnergy 1 M P
    linarith only [ht,hpay]

/-- The paid cutoff radius grows without bound. -/
theorem tendsto_mobiusDivisorPaidCutoffRadius :
    Tendsto (fun M : ℕ => Real.sqrt (Real.sqrt M)) atTop atTop := by
  simp_rw [fourth_root_eq]
  exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop

end RHTower
