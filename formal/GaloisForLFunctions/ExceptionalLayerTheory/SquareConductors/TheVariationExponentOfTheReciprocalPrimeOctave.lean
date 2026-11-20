import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFineVariationOfTheReciprocalPrimeOctave
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.VariationUnderADecreasingEnvelope
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Strong variation of the sharp reciprocal Mangoldt octave

The split into long and short increments of Ghosh–Shuin, §4, can be
made at a relative drop of the prime-number-theorem error envelope.
Partial summation controls the envelope using the original octave.
This preserves cancellation when a sampling grid skips many integers.
-/

open Filter Topology Finset ArithmeticFunction MeasureTheory
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The two boundary terms and the integrated Chebyshev error are the
entire sharp-octave defect. The lower endpoint need not be an integer. -/
theorem reciprocal_octave_psi_identity {x : ℝ} (hx : 0<x) :
    (∑ j ∈ Ioc ⌊x⌋₊ ⌊2*x⌋₊, vonMangoldt j/j)-Real.log 2 =
      (Chebyshev.psi (2*x)/(2*x)-1) - (Chebyshev.psi x/x-1) +
      ∫ t in x..2*x, (Chebyshev.psi t/t-1)/t := by
  have hx₂ : x≤2*x := by linarith only [hx]
  have h₂ : 0<2*x := hx.trans_le hx₂
  have cont : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc x (2*x)) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun t ht => pow_ne_zero _ (hx.trans_le ht.1).ne')
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜:=ℝ) (fun n => vonMangoldt n) hx.le hx₂
    (f:=fun t : ℝ => t⁻¹) (fun t ht => (hasDerivAt_inv (hx.trans_le ht.1).ne').differentiableAt)
    (show IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc x (2*x)) from by
      simpa only [deriv_inv] using cont.neg.integrableOn_compact isCompact_Icc)
  simp only [←Chebyshev.psi_eq_sum_Icc,deriv_inv,neg_mul] at habel
  rw [← intervalIntegral.integral_of_le hx₂,intervalIntegral.integral_neg,sub_neg_eq_add] at habel
  have hi₁ : IntervalIntegrable (fun t : ℝ => (t^2)⁻¹*Chebyshev.psi t) volume x (2*x) :=
    Chebyshev.psi_mono.intervalIntegrable.continuousOn_mul (by rwa [Set.uIcc_of_le hx₂])
  have hi₂ : IntervalIntegrable (fun t : ℝ => t⁻¹) volume x (2*x) :=
    (continuousOn_id.inv₀ (fun t (ht : t ∈ Set.Icc x (2*x)) => (hx.trans_le ht.1).ne')).intervalIntegrable_of_Icc hx₂
  have hcorr : (∫ t in x..2*x, (Chebyshev.psi t/t-1)/t) =
      (∫ t in x..2*x, (t^2)⁻¹*Chebyshev.psi t) - Real.log 2 := by
    rw [← show Real.log ((2*x)/x) = Real.log 2 by rw [mul_div_cancel_right₀ _ hx.ne'],
      ←integral_inv_of_pos hx h₂,←intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx₂] at ht
    field_simp [(hx.trans_le ht.1).ne']
    <;> ring
  rw [hcorr]
  simp only [div_eq_inv_mul] at habel ⊢
  linarith only [habel]

/-- Uniform transport of a relative Chebyshev error through a sharp
reciprocal octave costs at most three times the relative error. -/
theorem reciprocal_octave_psi_bound {x η : ℝ} (hx : 0<x)
    (h : ∀ t ∈ Set.Icc x (2*x), |Chebyshev.psi t/t-1|≤η) :
    |(∑ j ∈ Ioc ⌊x⌋₊ ⌊2*x⌋₊, vonMangoldt j/j)-Real.log 2| ≤ 3*η := by
  have hx₂ : x≤2*x := by linarith only [hx]
  have hleft := h x ⟨le_rfl,hx₂⟩
  have hright := h (2*x) ⟨hx₂,le_rfl⟩
  have hη := (abs_nonneg _).trans hleft
  have hi : |∫ t in x..2*x, (Chebyshev.psi t/t-1)/t| ≤ η := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=2*x)
      (f:=fun t => (Chebyshev.psi t/t-1)/t) (C:=η/x) (by
        intro t ht
        rw [Set.uIoc_of_le hx₂] at ht
        have ht₀ := hx.trans ht.1
        rw [Real.norm_eq_abs,abs_div,abs_of_pos ht₀]
        exact (div_le_div_of_nonneg_right (h _ ⟨ht.1.le,ht.2⟩) ht₀.le).trans
          (div_le_div_of_nonneg_left hη hx ht.1.le))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx₂),
      show 2*x-x=x by ring,div_mul_cancel₀ _ hx.ne',mul_div_cancel₀ _ hx.ne'] using hi
  rw [reciprocal_octave_psi_identity hx]
  refine (abs_add_le _ _).trans ?_
  have hd := abs_add_le (Chebyshev.psi (2*x)/(2*x)-1) (-(Chebyshev.psi x/x-1))
  rw [abs_neg,←sub_eq_add_neg] at hd
  linarith only [hd,hi,hright,hleft]

private def octaveEnvelope (c : ℝ) (n : ℕ) := Real.exp (-(c*Real.sqrt (Real.log n)))

private theorem envelope_antitone {c : ℝ} (hc : 0<c) : Antitone (octaveEnvelope c) := by
  intro m n hmn
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos m with rfl|hm
  · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg n
  exact Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmn)

/-- The centered octave inherits a global decreasing square-root-logarithmic
envelope from the classical prime number theorem, including odd endpoints. -/
theorem reciprocal_octave_global_envelope :
    ∃ C c : ℝ, 0<C ∧ 0<c ∧ ∀ n : ℕ,
      |reciprocalOctaveError n| ≤ C*Real.exp (-(c*Real.sqrt (Real.log n))) := by
  obtain ⟨A,d,hd,hA,hp⟩ := RHTower.exists_psi_error_eventually
  obtain ⟨T,hT⟩ := eventually_atTop.mp hp
  obtain ⟨N,hN⟩ := exists_nat_ge (max (2*T) 4)
  let c := d/2
  have hc : 0<c := half_pos hd
  have late (n : ℕ) (hn : N≤n) : |reciprocalOctaveError n|≤3*A*octaveEnvelope c n := by
    have h4 : 4≤(n:ℝ) := (le_max_right _ _).trans (hN.trans (Nat.cast_le.mpr hn))
    have hTn : 2*T≤(n:ℝ) := (le_max_left _ _).trans (hN.trans (Nat.cast_le.mpr hn))
    let x : ℝ := n/2
    have hx : 0<x := by dsimp only [x]; linarith only [h4]
    have h₂x : 2*x=n := by dsimp only [x]; ring
    have hlog : Real.log (n:ℝ) = Real.log 2+Real.log x := by
      rw [←h₂x,Real.log_mul (by norm_num : (2:ℝ)≠0) hx.ne']
    have hw (t : ℝ) (ht : t ∈ Set.Icc x (2*x)) :
        |Chebyshev.psi t/t-1| ≤ A*octaveEnvelope c n := by
      have ht₀ := hx.trans_le ht.1
      have htx : T≤t := by dsimp only [x] at ht; linarith only [hTn,ht.1]
      have hsv := hT t htx
      have hlog₂ : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by
        dsimp only [x] at ht; linarith only [ht.1,h4])
      have hlog₀ : 0≤Real.log t := (by positivity : 0≤Real.log 2).trans hlog₂
      have hs : Real.sqrt (Real.log n) ≤ 2*Real.sqrt (Real.log t) := by
        apply le_of_sq_le_sq _ (by positivity)
        rw [Real.sq_sqrt (Real.log_natCast_nonneg n),mul_pow,Real.sq_sqrt hlog₀]
        linarith only [hlog,hlog₂,Real.log_le_log hx ht.1,hlog₀]
      have hratio : |Chebyshev.psi t/t-1| ≤ A*Real.exp (-(d*Real.sqrt (Real.log t))) := by
        rw [show Chebyshev.psi t/t-1=(Chebyshev.psi t-t)/t by field_simp,abs_div,abs_of_pos ht₀]
        apply (div_le_iff₀ ht₀).mpr
        calc _ ≤ _ := hsv
             _ = _ := by simp only [neg_mul]; ring
      apply hratio.trans
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      dsimp only [c]
      linarith only [mul_le_mul_of_nonneg_left hs hd.le]
    have H := reciprocal_octave_psi_bound hx hw
    have hfloor : ⌊x⌋₊ = n/2 := by simpa only [x,Nat.cast_ofNat,Nat.floor_natCast] using Nat.floor_div_natCast (n:ℝ) 2
    rw [h₂x,Nat.floor_natCast,hfloor] at H
    simpa only [reciprocalOctaveError,mul_assoc] using H
  let D := ∑ j ∈ range N, |reciprocalOctaveError j|/octaveEnvelope c j
  have hD : 0≤D := sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨1+3*A+D,c,by linarith only [hA,hD],hc,fun n => ?_⟩
  change _ ≤ (1+3*A+D)*octaveEnvelope c n
  by_cases h : N≤n
  · exact (late n h).trans (mul_le_mul_of_nonneg_right (by linarith only [hD]) (Real.exp_pos _).le)
  · have hle : |reciprocalOctaveError n|/octaveEnvelope c n ≤ D := single_le_sum
      (fun j _ => div_nonneg (abs_nonneg _) (Real.exp_pos _).le) (mem_range.mpr (lt_of_not_ge h))
    exact ((div_le_iff₀ (Real.exp_pos _)).mp hle).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hA]) (Real.exp_pos _).le)


private theorem jump_le_reciprocal_log {n : ℕ} (hn : 1<n) :
    |octaveEndpointJump n| ≤ 2*Real.log n/n ∧ |octaveEndpointJump n|≤1 := by
  have mass (j : ℕ) (hj : 0<j) : octaveMangoldtMass j ≤ Real.log j/j ∧ Real.log j/j ≤ 1 := by
    refine ⟨div_le_div_of_nonneg_right vonMangoldt_le_log (Nat.cast_nonneg _),?_⟩
    apply (div_le_iff₀ (Nat.cast_pos.mpr hj)).mpr
    linarith only [Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hj)]
  by_cases h : 2∣n
  · obtain ⟨m,rfl⟩ := h
    have hm : 0 < m := by omega
    by_cases he : m=1
    · subst m
      have hlog := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
      norm_num [octave_even_endpoint (n:=1) (by decide),octaveMangoldtMass,
        vonMangoldt_apply_prime Nat.prime_two,abs_of_nonneg (by positivity : 0≤Real.log 2/2)]
      <;> linarith only [hlog,Real.log_natCast_nonneg 2]
    have hneg := octave_even_endpoint_nonpositive (by omega : 1 < m)
    rw [abs_of_nonpos hneg,octave_even_endpoint hm]
    have hl : Real.log m ≤ Real.log (2*m:ℕ) :=
      Real.log_le_log (Nat.cast_pos.mpr hm) (by exact_mod_cast (show m≤2*m by omega))
    have hpos : 0≤octaveMangoldtMass (2*m) := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    have hle : -(octaveMangoldtMass (2*m)-octaveMangoldtMass m) ≤ Real.log m/m := by
      linarith only [(mass m hm).1,hpos]
    refine ⟨hle.trans ?_,hle.trans (mass m hm).2⟩
    rw [Nat.cast_mul,Nat.cast_ofNat] at hl ⊢
    calc _ ≤ Real.log (2*(m:ℝ))/m := div_le_div_of_nonneg_right hl (Nat.cast_nonneg _)
         _ = _ := by ring
  · rw [octave_odd_endpoint hn h,abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]
    have H := mass n (by omega)
    refine ⟨H.1.trans ?_,H.1.trans H.2⟩
    exact div_le_div_of_nonneg_right (by linarith only [Real.log_natCast_nonneg n]) (Nat.cast_nonneg n)

/-- The logarithm in the pointwise Mangoldt bound can be absorbed by half
of a stretched exponential in the square root of the logarithm. -/
private theorem envelope_weighted_jump_sum {C c q : ℝ} (hC : 0<C) (hc : 0<c) (hq : 1<q) :
    Summable (fun j : ℕ => (C*octaveEnvelope c (j+1))^(q-1)*
      |reciprocalOctaveError (j+1)-reciprocalOctaveError j|) := by
  let d := c*(q-1)/4
  have hd : 0<d := div_pos (mul_pos hc (sub_pos.mpr hq)) (by norm_num)
  let K := 2*C^(q-1)/d^2
  have major := (summable_nat_add_iff 2).2 (GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show 0<2*d by positivity))
  apply (summable_nat_add_iff 1).1
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) _) (abs_nonneg _)) _ (major.mul_left K)
  intro j
  let n := j+2
  let x := Real.sqrt (Real.log n)
  have hx : 0≤x := Real.sqrt_nonneg _
  have hn : 1<n := by dsimp only [n]; omega
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hJ : |reciprocalOctaveError n-reciprocalOctaveError (j+1)| ≤ 2*Real.log n/n := by
    simpa only [octaveEndpointJump,n,show j+2-1=j+1 by omega] using (jump_le_reciprocal_log hn).1
  have hlog : x^2=Real.log n := Real.sq_sqrt (Real.log_natCast_nonneg n)
  have he : d*x ≤ Real.exp (d*x) := (by linarith only [Real.add_one_le_exp (d*x)])
  have hsq := pow_le_pow_left₀ (mul_nonneg hd.le hx) he 2
  rw [←Real.exp_nat_mul, Nat.cast_ofNat,mul_pow,hlog] at hsq
  have hb : d^2*Real.log n*Real.exp (-(4*d*x)) ≤ Real.exp (-(2*d*x)) := by
    apply (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add]
    congr 1
    ring
  change (C*octaveEnvelope c n)^(q-1)*_ ≤ K*(Real.exp (-(2*d*x))/n)
  refine (mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) _)).trans ?_
  rw [Real.mul_rpow hC.le (Real.exp_pos _).le,octaveEnvelope,←Real.exp_mul]
  change C^(q-1)*Real.exp (-(c*x)*(q-1))*(2*Real.log n/n) ≤ _
  rw [show -(c*x)*(q-1) = -(4*d*x) by dsimp only [d]; ring]
  dsimp only [K]
  calc _ = (2*C^(q-1)/(d^2*(n:ℝ))) * (d^2*Real.log n*Real.exp (-(4*d*x))) := by
             field_simp [hd.ne',hn'.ne']; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- A common bound over every finite increasing or nondecreasing sampling
grid. Repeated endpoints are allowed. -/
def boundedReciprocalOctaveVariation (q : ℝ) : Prop :=
  ∃ B : ℝ, ∀ t : ℕ → ℕ, Monotone t → ∀ M : ℕ,
    ∑ i ∈ range M, |reciprocalOctaveError (t (i+1))-reciprocalOctaveError (t i)|^q ≤ B

/-- Strong variation is finite at every exponent strictly larger than one.
The same bound covers arbitrary skipped endpoints on the full half-line. -/
theorem bounded_reciprocal_octave_variation {q : ℝ} (hq : 1<q) : boundedReciprocalOctaveVariation q := by
  obtain ⟨C,c,hC,hc,hf⟩ := reciprocal_octave_global_envelope
  let u (n : ℕ) := C*octaveEnvelope c n
  let v (j : ℕ) := u (j+1)^(q-1)*|reciprocalOctaveError (j+1)-reciprocalOctaveError j|
  have hu : Antitone u := fun _ _ h => mul_le_mul_of_nonneg_left (envelope_antitone hc h) hC.le
  have hpos (n : ℕ) : 0≤u n := mul_nonneg hC.le (Real.exp_pos _).le
  have hv (n : ℕ) : 0≤v n := mul_nonneg (Real.rpow_nonneg (hpos _) _) (abs_nonneg _)
  have hS : Summable v := envelope_weighted_jump_sum hC hc hq
  refine ⟨2*(2:ℝ)^q*u 0^q+(4:ℝ)^(q-1)*∑' j, v j,fun t ht M => ?_⟩
  apply (envelope_variation_grid reciprocalOctaveError u hu hf hq.le t ht M).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left ((sub_le_self _ (Real.rpow_nonneg (hpos _) _)).trans
      (Real.rpow_le_rpow (hpos _) (hu (Nat.zero_le _)) (zero_le_one.trans hq.le))) (by positivity)
  · exact mul_le_mul_of_nonneg_left (hS.sum_le_tsum _ fun j _ => hv j) (by positivity)

private theorem consecutive_variation (M : ℕ) :
    ∑ i ∈ range M, |reciprocalOctaveError (i+2)-reciprocalOctaveError (i+1)| =
      octaveFineVariation (M+1) := by
  induction M with
  | zero => simp [octaveFineVariation]
  | succ M ih =>
    rw [sum_range_succ,ih,octaveFineVariation,sum_Ioc_succ_top (by omega : 1≤M+1)]
    rfl

/-- The first exponent is the exact threshold. The divergence there
already occurs on the consecutive-integer grid. -/
theorem reciprocal_octave_variation_iff (q : ℝ) :
    boundedReciprocalOctaveVariation q ↔ 1<q := by
  refine ⟨fun h => ?_,bounded_reciprocal_octave_variation⟩
  by_contra! hq
  obtain ⟨B,hB⟩ := h
  have hb (M : ℕ) : octaveFineVariation (M+1) ≤ B := by
    rw [←consecutive_variation]
    apply le_trans _ (hB (fun n => n+1) (fun _ _ h => Nat.succ_le_succ h) M)
    apply sum_le_sum
    intro i _
    apply Real.self_le_rpow_of_le_one (abs_nonneg _) _ hq
    simpa only [octaveEndpointJump,show i+2-1=i+1 by omega] using (jump_le_reciprocal_log (by omega : 1 < i+2)).2
  let L := -2*Real.eulerMascheroniConstant-2*Real.log 2
  have lower := octave_fine_variation_second_term.eventually_const_lt (show L-1<L by linarith)
  have grow : Tendsto (fun n : ℕ => 2*Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  obtain ⟨n,⟨hn,hl⟩,hg⟩ := (((eventually_ge_atTop 1).and lower).and (grow.eventually_ge_atTop (B-L+2))).exists
  have b := hb (n-1)
  rw [Nat.sub_add_cancel hn] at b
  linarith only [b,hl,hg]

#print axioms bounded_reciprocal_octave_variation
#print axioms reciprocal_octave_variation_iff
#print axioms reciprocal_octave_psi_identity
#print axioms reciprocal_octave_psi_bound
#print axioms reciprocal_octave_global_envelope
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
