import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeCompensation
import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-!
# Actual leading compensation of the smooth-prime intermediate head

Quantitative PNT gives the complete signed channel sum the unconditional estimate
`S(M) log(M) / (M sqrt(M)) → 0`. The exact relation `H-S=T` and the positive
late-prime mass floor then give `S(4N)/T(4N) → 0`, `H(4N)/T(4N) → 1`, and
`H(4N)/(4N) → +∞`.

These are source asymptotics. The critical residual bound `S(M)=O(M)` remains
open; leading relative compensation does not supply that RH-bearing bound.
-/

open Filter Topology Finset
noncomputable section
namespace RHTower

/-- Quantitative PNT controls the actual Gamma-completed source with a logarithmic saving. -/
theorem tendsto_psiDefect_mul_log_div :
    Tendsto (fun k : ℕ => psiDefect k * Real.log k / k) atTop (𝓝 0) := by
  obtain ⟨C,c,hc,hC,hbound⟩ := exists_psi_error_eventually
  have hsaving : Tendsto (fun x : ℝ => C * (Real.log x *
      Real.exp (-c * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have h := (Sieve.tendsto_logRpow_mul_expSaving (d := (1:ℝ)/2)
      (by norm_num) hc (1:ℝ)).const_mul C
    simpa only [Real.rpow_one, ← Real.sqrt_eq_rpow, neg_mul, mul_zero] using h
  have herror : Tendsto (fun k : ℕ =>
      (Chebyshev.psi k - k) * Real.log k / k) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hsaving.comp tendsto_natCast_atTop_atTop)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound,
      eventually_ge_atTop (1:ℕ)] with k hk hk1
    have hkpos : (0:ℝ)<k := by positivity
    have hl : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg hl,abs_of_pos hkpos]
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk hl) hkpos.le
    refine h.trans_eq ?_
    dsimp only [Function.comp_def]
    field_simp
  have hlog : Tendsto (fun k : ℕ => Real.log k / k) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one,Function.comp_def] using h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  have h := herror.add (hlog.const_mul (2*Real.eulerMascheroniConstant))
  convert h using 1
  · funext k
    rw [psiDefect,chebyshevPsi_eq_psi]
    ring
  · norm_num

private theorem sqrt_step_mul_sqrt_le_one (k : ℕ) :
    (Real.sqrt (k+1:ℕ)-Real.sqrt k)*Real.sqrt k ≤ 1 := by
  have ha := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hb := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (k+1))
  have hc := sq_nonneg (Real.sqrt (k+1:ℕ)-Real.sqrt k)
  push_cast at hb hc ⊢
  nlinarith

private theorem weighted_defect_le {M k : ℕ}
    (hk : Real.exp 2 ≤ (k:ℝ)) (hkM : k ≤ M) :
    (Real.sqrt (k+1:ℕ)-Real.sqrt k)*|psiDefect k| * (Real.log M/Real.sqrt M) ≤
      |psiDefect k * Real.log k / k| := by
  have hkpos : (0:ℝ)<k := (Real.exp_pos 2).trans_le hk
  have hs : 0 ≤ Real.sqrt (k+1:ℕ)-Real.sqrt k :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by push_cast; linarith))
  have hlog : 0 ≤ Real.log k := Real.log_nonneg
    ((Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤2)).trans hk)
  have hkm : (k:ℝ) ≤ M := by exact_mod_cast hkM
  have hmono := Real.log_div_sqrt_antitoneOn hk (hk.trans hkm) hkm
  have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hs (abs_nonneg (psiDefect k)))
  apply h1.trans
  rw [abs_div,abs_mul,abs_of_nonneg hlog,abs_of_pos hkpos]
  have hroot : (Real.sqrt k)^2=(k:ℝ) := Real.sq_sqrt hkpos.le
  have hstep : (Real.sqrt (k+1:ℕ)-Real.sqrt k)/Real.sqrt k ≤ 1/(k:ℝ) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hkpos) hkpos).mpr
    nlinarith [sqrt_step_mul_sqrt_le_one k,Real.sqrt_pos.mpr hkpos]
  have h2 := mul_le_mul_of_nonneg_right hstep (mul_nonneg (abs_nonneg (psiDefect k)) hlog)
  convert h2 using 1 <;> first | rfl | ring

/-- Möbius inversion identifies the complete channel sum with the actual source defect. -/
theorem sum_mobiusDivisorDilationChannel_eq_psiDefect_abel (M : ℕ) :
    (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d) =
      ∑ k ∈ Ico 1 M, (Real.sqrt (k+1:ℕ)-Real.sqrt k)*psiDefect k := by
  have hext : (∑ d ∈ Icc 1 (M-1), mobiusDivisorDilationChannel M d) =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
    apply sum_subset (Icc_subset_Icc le_rfl (by omega))
    intro d hd hn
    have hdM : M-1<d := by simp only [mem_Icc] at hd hn; omega
    simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt hdM]
  rw [← hext,← mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels,
    mobiusDivisorSquareRootAbelMoment]
  have hsets : Icc 1 (M-1)=Ico 1 M := by ext k; simp; omega
  rw [hsets]
  apply sum_congr rfl
  intro k hk
  rw [← psiDefect_eq_mobius_primeFreeDivisorDefect (mem_Ico.mp hk).1]

/-- The actual complete signed aggregate is little-o of the late-prime mass scale. -/
theorem tendsto_sum_mobiusDivisorDilationChannel_log_normalized :
    Tendsto (fun M : ℕ => (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d) *
      Real.log M / ((M:ℝ)*Real.sqrt M)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun k => |psiDefect k * Real.log k / k|
  let b : ℕ → ℝ := fun k => (Real.sqrt (k+1:ℕ)-Real.sqrt k)*|psiDefect k|
  obtain ⟨L,hL⟩ := exists_nat_ge (max (Real.exp 2) 1)
  have hL1 : 1 ≤ L := by exact_mod_cast (le_max_right (Real.exp 2) 1).trans hL
  let B : ℝ := ∑ k ∈ Ico 1 L, b k
  have hCesaro : Tendsto (fun M : ℕ => (∑ k ∈ range M, a k)/(M:ℝ)) atTop (𝓝 0) := by
    have h := tendsto_psiDefect_mul_log_div.abs.cesaro
    simpa only [abs_zero,div_eq_mul_inv,mul_comm,a] using h
  have hlogroot : Tendsto (fun M : ℕ => Real.log M/Real.sqrt M) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)
  have hB : Tendsto (fun M : ℕ => B * (Real.log M/Real.sqrt M)/(M:ℝ)) atTop (𝓝 0) := by
    have h := (hlogroot.const_mul B).mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop))
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa only [zero_add] using hB.add hCesaro)
  filter_upwards [eventually_ge_atTop L] with M hLM
  have hM1 : 1 ≤ M := hL1.trans hLM
  have hMpos : (0:ℝ)<M := by positivity
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hprefix : |∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d| ≤
      B + ∑ k ∈ Ico L M, b k := by
    rw [sum_mobiusDivisorDilationChannel_eq_psiDefect_abel]
    have h := abs_sum_le_sum_abs (s := Ico 1 M)
      (f := fun k => (Real.sqrt (k+1:ℕ)-Real.sqrt k)*psiDefect k)
    have heq : (∑ k ∈ Ico 1 M, |(Real.sqrt (k+1:ℕ)-Real.sqrt k)*psiDefect k|) =
        ∑ k ∈ Ico 1 M, b k := by
      apply sum_congr rfl
      intro k _
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr
        (Real.sqrt_le_sqrt (by push_cast; linarith)))]
    rw [heq,← sum_Ico_consecutive b hL1 hLM] at h
    exact h
  have htail : (∑ k ∈ Ico L M, b k) * (Real.log M/Real.sqrt M) ≤
      ∑ k ∈ range M, a k := by
    rw [sum_mul]
    apply (sum_le_sum (fun k hk => weighted_defect_le
      ((le_max_left (Real.exp 2) 1).trans (hL.trans
        (by exact_mod_cast (mem_Ico.mp hk).1))) (mem_Ico.mp hk).2.le)).trans
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_range.mpr (mem_Ico.mp hk).2
    · intro k _ _
      exact abs_nonneg _
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg hlog,
    abs_of_pos (mul_pos hMpos hroot)]
  have h := mul_le_mul_of_nonneg_right hprefix (div_nonneg hlog hroot.le)
  rw [add_mul] at h
  have h' := h.trans (add_le_add le_rfl htail)
  have hd := div_le_div_of_nonneg_right h' hMpos.le
  convert hd using 1 <;> first | rfl | ring

/-- The PNT prime window supplies an explicit eventual late-prime lower mass. -/
theorem eventually_mobiusDivisorLatePrimeMass_ge :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ))) ≤
      mobiusDivisorLatePrimeMass (4*N) := by
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
    (K := (3:ℝ)/2) (by norm_num))
  filter_upwards [hcount] with N hc
  have harg : (3/2:ℝ)*(2*(N:ℝ))=(3*N:ℕ) := by push_cast; ring
  have htwo : 2*(N:ℝ)=((2*N:ℕ):ℝ) := by push_cast; rfl
  rw [harg,htwo,Nat.floor_natCast,Nat.floor_natCast] at hc
  rw [← GaloisForLFunctions.HTGeometry.card_primesInIoc (show 2*N ≤ 3*N by omega)] at hc
  have hm := mobiusDivisorLatePrimeMass_four_mul_ge N
  have h := mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.sqrt N/40 by positivity)
  rw [mul_div_assoc] at hm
  have h' := h.trans hm
  convert h' using 1 <;> first | rfl | (push_cast; ring)

/-- The final signed aggregate is negligible relative to the actual late-prime mass. -/
theorem tendsto_total_div_mobiusDivisorLatePrimeMass :
    Tendsto (fun N : ℕ => (∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d) /
      mobiusDivisorLatePrimeMass (4*N)) atTop (𝓝 0) := by
  have hfour : Tendsto (fun N : ℕ => 4*N) atTop atTop :=
    tendsto_atTop_mono (fun N : ℕ => show N ≤ 4*N by omega) tendsto_id
  have hlim := (tendsto_sum_mobiusDivisorDilationChannel_log_normalized.comp hfour).abs.const_mul 640
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [abs_zero,mul_zero] using hlim)
  filter_upwards [eventually_mobiusDivisorLatePrimeMass_ge,eventually_ge_atTop (1:ℕ)] with N hT hN
  have hNp : (0:ℝ)<N := by positivity
  have hl2 : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by
      have hnR : (1:ℝ)≤N := by exact_mod_cast hN
      linarith)
  have hl4 : 0 < Real.log (4*N:ℕ) := Real.log_pos (by exact_mod_cast (show 1<4*N by omega))
  have hmono : Real.log (2*(N:ℝ)) ≤ Real.log (4*N:ℕ) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have h4 : Real.sqrt (4*N:ℕ)=2*Real.sqrt N := by
    rw [Nat.cast_mul,Real.sqrt_mul (by norm_num)]
    norm_num
  have hsmall : (4*N:ℕ)*Real.sqrt (4*N:ℕ)/(640*Real.log (4*N:ℕ)) ≤
      (N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ))) := by
    rw [h4]
    push_cast
    have h := div_le_div_of_nonneg_left (show 0 ≤ (N:ℝ)*Real.sqrt N/80 by positivity) hl2 hmono
    push_cast at h
    convert h using 1 <;> first | rfl | ring
  have hbase : (0:ℝ)<(4*N:ℕ)*Real.sqrt (4*N:ℕ)/(640*Real.log (4*N:ℕ)) := by positivity
  have hTpos : 0 < mobiusDivisorLatePrimeMass (4*N) := hbase.trans_le (hsmall.trans hT)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hTpos]
  have h := div_le_div_of_nonneg_left
    (abs_nonneg (∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d)) hbase (hsmall.trans hT)
  refine h.trans_eq ?_
  dsimp only [Function.comp_def]
  rw [abs_div,abs_mul,abs_of_pos hl4,abs_of_pos (show (0:ℝ)<(4*N:ℕ)*Real.sqrt (4*N:ℕ) by positivity)]
  field_simp

/-- The smooth-prime intermediate head carries precisely the late-prime mass to leading order. -/
theorem tendsto_mobiusDivisorHalfPrimeHead_div_latePrimeMass :
    Tendsto (fun N : ℕ => mobiusDivisorHalfPrimeHead (4*N)/mobiusDivisorLatePrimeMass (4*N))
      atTop (𝓝 1) := by
  have h := tendsto_total_div_mobiusDivisorLatePrimeMass.add_const 1
  apply (show Tendsto (fun N : ℕ =>
      (∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d)/mobiusDivisorLatePrimeMass (4*N)+1)
      atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [tendsto_mobiusDivisorLatePrimeMass_div_atTop.eventually (eventually_gt_atTop (0:ℝ))]
    with N hN
  have hT : mobiusDivisorLatePrimeMass (4*N) ≠ 0 := by
    intro hz
    rw [hz,zero_div] at hN
    exact lt_irrefl _ hN
  have heq := mobiusDivisorHalfPrimeHead_sub_total (4*N)
  apply (eq_div_iff hT).mpr
  field_simp
  linarith only [heq]

/-- The intermediate head itself grows faster than the final linear receiver scale. -/
theorem tendsto_mobiusDivisorHalfPrimeHead_div_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorHalfPrimeHead (4*N)/(4*(N:ℝ))) atTop atTop := by
  have hhalf := tendsto_mobiusDivisorHalfPrimeHead_div_latePrimeMass.eventually
    (eventually_gt_nhds (show (1:ℝ)/2<1 by norm_num))
  have hlim := tendsto_mobiusDivisorLatePrimeMass_div_atTop.const_mul_atTop
    (show (0:ℝ)<1/2 by norm_num)
  apply tendsto_atTop_mono' _ _ hlim
  filter_upwards [hhalf,eventually_mobiusDivisorLatePrimeMass_ge,eventually_ge_atTop (1:ℕ)]
    with N hH hT hN
  have hl : 0 < Real.log (2*(N:ℝ)) := Real.log_pos
    (by
      have hnR : (1:ℝ)≤N := by exact_mod_cast hN
      linarith)
  have hTp : 0 < mobiusDivisorLatePrimeMass (4*N) :=
    (show (0:ℝ)<(N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ))) by positivity).trans_le hT
  have hH' := (lt_div_iff₀ hTp).mp hH
  have h := div_le_div_of_nonneg_right hH'.le (show (0:ℝ)≤4*N by positivity)
  convert h using 1
  ring
end RHTower
