import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimeIncrementAcrossAnExtremalWave
import GaloisForLFunctions.HTGeometry.NegPowerCircleAverage

/-!
# The weighted mass of the signed prime increment

The reciprocal of a sinusoid has locally integrable powers of order less
than one. Interpolating the signed square bound with the bound multiplied by
the sinusoid gives absolute Laplace convergence above the critical line.
-/

noncomputable section
open Filter Topology MeasureTheory Set RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem integrableOn_damped_periodic {f : ℝ → ℝ} {P d : ℝ}
    (hP : 0 < P) (hd : 0 < d) (hp : Function.Periodic f P)
    (hf : ∀ t, 0 ≤ f t) (hi : ∀ a b, IntervalIntegrable f volume a b) :
    IntegrableOn (fun t => Real.exp (-d*t)*f t) (Ioi 0) := by
  let g := fun t => Real.exp (-d*t)*f t
  let s := fun n : ℕ => Icc (n*P : ℝ) (n*P+P)
  let C := ∫ t in (0:ℝ)..P, f t
  have hlo (n : ℕ) : n*P ≤ n*P+P := le_add_of_nonneg_right hP.le
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hi a b).continuousOn_mul (by fun_prop)
  have hu (n : ℕ) : (∫ t in s n, ‖g t‖) ≤ Real.exp (-d*P)^n * C := by
    change (∫ t in Icc _ _, ‖g t‖) ≤ _
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (hlo n)]
    have hmono := intervalIntegral.integral_mono_on (hlo n) (hg _ _).norm
      ((hi _ _).const_mul (Real.exp (-d*(n*P)))) (fun t ht => by
        change ‖Real.exp (-d*t)*f t‖ ≤ _
        rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf _))]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hd.le))) (hf _))
    refine hmono.trans_eq ?_
    rw [intervalIntegral.integral_const_mul, hp.intervalIntegral_add_eq (n*P) 0,zero_add,
      ← Real.exp_nat_mul]
    congr 2
    ring
  have hsum := (summable_geometric_of_lt_one (Real.exp_pos (-d*P)).le
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hd) hP))).mul_right C
  have hunion := integrableOn_iUnion_of_summable_integral_norm
    (s := s) (f := g) (μ := volume)
    (fun n => (intervalIntegrable_iff_integrableOn_Icc_of_le (hlo n)).mp (hg _ _))
    (hsum.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hu)
  apply hunion.mono_set
  intro t ht
  let n := ⌊t/P⌋₊
  refine mem_iUnion.mpr ⟨n,?_,?_⟩
  · exact (le_div_iff₀ hP).mp (Nat.floor_le (div_nonneg (le_of_lt ht) hP.le))
  · have h := (div_lt_iff₀ hP).mp (Nat.lt_floor_add_one (t/P))
    linarith only [h]

private theorem interpolate_square_and_product {x b A δ : ℝ}
    (hx : 0 ≤ x) (hb : 0 < b) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsq : x^2 ≤ A) (hp : b*x ≤ A) :
    x ≤ A^((1+δ)/2)*b^(-δ) := by
  rw [Real.rpow_neg hb.le,← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hb _)]
  rcases hx.eq_or_lt with hz | hxpos
  · rw [← hz,zero_mul]
    positivity
  let e := (1-δ)/2
  have he : 0 ≤ e := (half_pos (sub_pos.mpr hδ1)).le
  have hpow : (x^2)^e = x^(1-δ) := by
    rw [← Real.rpow_natCast_mul hx]
    congr 1
    dsimp only [e]
    push_cast
    ring
  calc x*b^δ = (x^2)^e*(b*x)^δ := by
         rw [hpow,Real.mul_rpow hb.le hx, mul_left_comm,← Real.rpow_add hxpos,sub_add_cancel,Real.rpow_one,mul_comm]
    _ ≤ A^e*A^δ := mul_le_mul (Real.rpow_le_rpow (sq_nonneg _) hsq he)
        (Real.rpow_le_rpow (mul_nonneg hb.le hx) hp hδ.le)
        (Real.rpow_nonneg (mul_nonneg hb.le hx) _) (Real.rpow_nonneg hA.le _)
    _ = A^((1+δ)/2) := by rw [← Real.rpow_add hA]; congr 1; dsimp only [e]; ring

private theorem damped_cosine_reciprocal {ω δ d : ℝ} (hω : 0 < ω) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hd : 0 < d) (φ : ℝ) :
    IntegrableOn (fun t => Real.exp (-d*t)*|Real.cos (ω*t+φ)|^(-δ)) (Ioi 0) := by
  let P := 2*Real.pi/ω
  apply integrableOn_damped_periodic (P := P) (by dsimp only [P]; positivity) hd
  · intro t
    change |Real.cos (ω*(t+P)+φ)|^(-δ) = _
    rw [show ω*(t+P)+φ=(ω*t+φ)+2*Real.pi by dsimp only [P]; field_simp [hω.ne'] <;> ring,
      Real.cos_add_two_pi]
  · intro t
    exact Real.rpow_nonneg (abs_nonneg _) _
  · intro a b
    let v := φ+Real.pi/2
    have H := (GaloisForLFunctions.HTGeometry.intervalIntegrable_abs_sin_rpow_neg hδ hδ1
      (ω*a+v) (ω*b+v)).comp_add_right v
    simp only [add_sub_cancel_right] at H
    have H' := H.comp_mul_left (c := ω)
    simp only [mul_div_cancel_left₀ _ hω.ne'] at H'
    simpa only [v,← add_assoc,Real.sin_add_pi_div_two] using H'

private theorem ae_cosine_ne_zero {ω : ℝ} (hω : 0 < ω) (φ : ℝ) :
    ∀ᵐ t : ℝ, Real.cos (ω*t+φ) ≠ 0 := by
  let v := -(φ+Real.pi/2)
  have hc := (GaloisForLFunctions.HTGeometry.countable_sin_shift_eq_zero v).preimage
    (f := fun t : ℝ => ω*t) (fun _ _ h => mul_left_cancel₀ hω.ne' h)
  have hh : ∀ᵐ t : ℝ, t ∉ (fun t : ℝ => ω*t) ⁻¹' {z | Real.sin (z-v) = 0} :=
    hc.ae_notMem volume
  filter_upwards [hh] with t ht
  change Real.sin (ω*t-v) ≠ 0 at ht
  simpa only [v,sub_neg_eq_add,← add_assoc,Real.sin_add_pi_div_two] using ht

/-- Above every supercritical Laplace exponent, the raw signed increment
minus its predicted extremal wave has finite absolute weighted tail mass. -/
theorem integrableOn_tail_signed_prime_increment {γ s : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hs : 1/2 < s) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    let β := zetaZeroAbscissa
    let h := quarterPeriodStep γ
    let D := boundaryStep β h (primeErrorBoundaryTrace β)
    let U := normalizedPrimeIncrement β h
    ∃ T : ℝ, 0 ≤ T ∧ IntegrableOn (fun t => Real.exp ((β-s)*t)*(U t-D t)) (Ioi T) := by
  intro β h D U
  obtain ⟨τ,hτ,hτ'⟩ := exists_between (lt_min hΘ hs)
  have hτβ : τ < β := lt_of_lt_of_le hτ' (min_le_left _ _)
  have hτs : τ < s := lt_of_lt_of_le hτ' (min_le_right _ _)
  have hden : 0 < β-τ := sub_pos.mpr hτβ
  have hex : 2*(β-s)/(β-τ)-1 < 1 := by
    have hlt : 2*(β-s)/(β-τ)<2 := (div_lt_iff₀ hden).mpr (by linarith only [hτs])
    linarith only [hlt]
  obtain ⟨δ,hδ',hδ1⟩ := exists_between (max_lt zero_lt_one hex)
  have hδ : 0 < δ := lt_of_le_of_lt (le_max_left _ _) hδ'
  let a := (1+δ)/2
  let d := s-β+a*(β-τ)
  have hd : 0 < d := by
    have hdδ := lt_of_le_of_lt (le_max_right _ _) hδ'
    have hlo : 2*(β-s)/(β-τ) < δ+1 := by linarith only [hdδ]
    dsimp only [d,a]
    linarith only [(div_lt_iff₀ hden).mp hlo]
  obtain ⟨q,K,φ,_,hK,hD⟩ := exists_cosine_boundaryStep_of_bounded_thetaRadial hΘ hγ hm hb
  let ω := |xiCopyOrdinate q|
  change ∀ t, D t = K*Real.cos (ω*t+φ) at hD
  have hω : 0 < ω := (by norm_num : (0:ℝ)<4).trans (four_lt_abs_xiCopyOrdinate q)
  obtain ⟨M,hM⟩ := signed_prime_increment_on_extremal_wave hτ hτβ hγ hm hb
  obtain ⟨T,hT⟩ := eventually_atTop.mp hM
  let B := |M|+1
  let X := fun t => |U t-D t|
  have hB : 0 < B := by dsimp only [B]; positivity
  let c := B^a*K^(-δ)
  let w := fun t => Real.exp (-d*t)*|Real.cos (ω*t+φ)|^(-δ)
  let T' := max 0 T
  have hw : IntegrableOn w (Ioi T') :=
    (damped_cosine_reciprocal hω hδ hδ1 hd φ).mono_set (Ioi_subset_Ioi (le_max_left _ _))
  have hmeas : Measurable (fun t => Real.exp ((β-s)*t)*(U t-D t)) := by
    have hθ : Measurable thetaLogError :=
      (Chebyshev.theta_mono.measurable.comp Real.continuous_exp.measurable).sub Real.continuous_exp.measurable
    have hU : Measurable U := ((hθ.comp (measurable_id.add measurable_const)).sub hθ).div
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
    have hc : Continuous D := by rw [funext hD]; fun_prop
    exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      (hU.sub hc.measurable)
  refine ⟨T',le_max_left _ _,(hw.const_mul c).mono' hmeas.aestronglyMeasurable ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (ae_cosine_ne_zero hω φ)] with t ht hne
  have H := hT t ((le_max_right _ _).trans (le_of_lt ht))
  let A := B*Real.exp (-(β-τ)*t)
  have hA : 0 < A := mul_pos hB (Real.exp_pos _)
  have hmajor : M*Real.exp (-(β-τ)*t) ≤ A := mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) (Real.exp_pos _).le
  have hsq : X t^2 ≤ A := by
    rw [show X t^2=(U t-D t)^2 from sq_abs _]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (H.trans hmajor)
  have hp : |D t| * X t ≤ A := by
    rw [show |D t| * X t=|D t*(U t-D t)| from (abs_mul _ _).symm]
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans (H.trans hmajor)
  have he := interpolate_square_and_product (abs_nonneg _) (b := |D t|)
    (abs_pos.mpr (by rw [hD]; exact mul_ne_zero hK.ne' hne)) hA hδ hδ1 hsq hp
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq ?_
  dsimp only [A,c,w]
  rw [hD,abs_mul,abs_of_pos hK,Real.mul_rpow hB.le (Real.exp_pos _).le,
    Real.mul_rpow hK.le (abs_nonneg _),← Real.exp_mul]
  change Real.exp ((β-s)*t)*(B^a*Real.exp ((-(β-τ)*t)*a)*(K^(-δ)*|Real.cos (ω*t+φ)|^(-δ))) = _
  rw [show -d*t=(β-s)*t+(-(β-τ)*t)*a by dsimp only [d]; ring,Real.exp_add]
  ring

#print axioms integrableOn_tail_signed_prime_increment

end GaloisForLFunctions.ExceptionalLayerTheory
