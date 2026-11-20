import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.BothSignsInOneGammaAverageOfTheThirdPrimeWave

/-!
# Opposite prime excursions at one macroscopic time

The gamma means of a double-neutral prime wave nearly cancel. At their
absolute Laplace abscissa the exponential tilt localizes both signs at
the same saddle, with time divided by moment order tending to the reciprocal
distance from that abscissa to one. Thus the two large excursions can be
forced into arbitrarily narrow relative time windows.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

open private ordinaryPrimeWave_hilbert from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.GammaAveragesOfTheOrdinaryPrimeError
open private neutral_ordinary_gamma_moments from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositeExcursionsOfTheThirdConfinedPrimeWave
open private laplace_of_gamma_series sign_integrable mass_nonneg weight_nonneg from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.BothSignsInOneGammaAverageOfTheThirdPrimeWave

/-- Absolute Laplace convergence of the physical wave on the positive ray. -/
def waveLaplaceDomain (v : ℝ → ℝ) : Set ℝ :=
  {b | IntegrableOn (fun t => Real.exp (-b*t)*|v t|) (Ioi 0)}

private theorem domain_up {v : ℝ → ℝ} (hm : Measurable v) {s c : ℝ}
    (hs : s ∈ waveLaplaceDomain v) (hsc : s ≤ c) : c ∈ waveLaplaceDomain v := by
  apply hs.mono' (((by fun_prop : Measurable fun t : ℝ => Real.exp (-c*t)).mul hm.abs).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : t ∈ Ioi (0:ℝ))
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hsc) ht.le)) (abs_nonneg _)

private theorem gamma_difference {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n,IntegrableOn (fun t => primeGammaWeight n t*v t) (Ioi 0)) (n : ℕ) :
    gammaSignMass v n-gammaSignMass (fun t => -v t) n = ∫ t in Ioi (0:ℝ),primeGammaWeight n t*v t := by
  have hi' : IntegrableOn (fun t => primeGammaWeight n t*(-v t)) (Ioi 0) :=
    (hi n).neg.congr (Eventually.of_forall fun t => (mul_neg ..).symm)
  rw [gammaSignMass,gammaSignMass,←integral_sub (sign_integrable hm (hi n)) (sign_integrable hm.neg hi')]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  rw [←mul_sub]
  congr 1
  rcases le_total 0 (v t) with h|h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]

/-- Every exponential order strictly below the reciprocal abscissa is
simultaneously exceeded by the two positive gamma measures. -/
private theorem gamma_at_every_order {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n,IntegrableOn (fun t => primeGammaWeight n t*v t) (Ioi 0))
    (hs : Summable fun n => |∫ t in Ioi (0:ℝ),primeGammaWeight n t*v t|)
    {B q : ℝ} (hB : B < 1) (hfail : ∀ b < B,b ∉ waveLaplaceDomain v)
    (hq : 1 < q) (hqB : q < (1-B)⁻¹) (M : ℝ) :
    ∃ᶠ n : ℕ in atTop,M*q^n < min (gammaSignMass v n) (gammaSignMass (fun t => -v t) n) := by
  have hq0 := zero_lt_one.trans hq
  have h₀ : 1-q⁻¹ < B := by
    have he := (lt_inv_comm₀ hq0 (sub_pos.mpr hB)).mp hqB
    linarith only [he]
  obtain ⟨b,hb₀,hb⟩ := exists_between h₀
  have hbpos : 0 < b := (sub_pos.mpr ((inv_lt_one₀ hq0).mpr hq)).trans hb₀
  let r := 1-b
  have hr : 0 < r := sub_pos.mpr (hb.trans hB)
  have hrq : r*q < 1 := by
    rw [←lt_div_iff₀ hq0,one_div]
    dsimp only [r]; linarith only [hb₀]
  have hno : ¬Summable (fun n => r^n*gammaSignMass v n) := by
    intro h
    apply hfail b hb
    apply integrable_abs_of_posPart_of_summable_gamma_moments hbpos.le (hb.trans hB).le hi hs
    simpa only [r,sub_sub_cancel] using laplace_of_gamma_series hm hi hr.le h
  let K := ∑' n,|∫ t in Ioi (0:ℝ),primeGammaWeight n t*v t|
  have hk : 0 ≤ K := tsum_nonneg fun _ => abs_nonneg _
  have diff (n : ℕ) : gammaSignMass v n-gammaSignMass (fun t => -v t) n ≤ K := by
    rw [gamma_difference hm hi]
    exact (le_abs_self _).trans (hs.le_tsum n fun _ _ => abs_nonneg _)
  have many : ∃ᶠ n : ℕ in atTop,(|M|+K)*q^n < gammaSignMass v n := by
    by_contra h
    apply hno
    have hseries := (summable_geometric_of_lt_one (mul_nonneg hr.le hq0.le) hrq).mul_left (|M|+K)
    apply Summable.of_norm_bounded_eventually hseries
    filter_upwards [not_frequently.mp h] with n hn
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr.le _) (mass_nonneg _ _)),mul_pow]
    exact (mul_le_mul_of_nonneg_left (le_of_not_gt hn) (pow_nonneg hr.le _)).trans_eq (by ring)
  refine many.mono fun n hn => ?_
  have h₁ := mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg hq0.le n)
  have h₂ := le_mul_of_one_le_right hk (one_le_pow₀ hq.le (n := n))
  exact lt_min (by linarith only [hn,h₁,h₂,hk]) (by linarith only [hn,h₁,h₂,diff n])

private theorem gamma_tilt {k : ℝ} (hk : 0 < k) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    primeGammaWeight n t ≤ k⁻¹^n*Real.exp ((k-1)*t) := by
  have hf := Real.pow_div_factorial_le_exp (k*t) (mul_nonneg hk.le ht) n
  rw [mul_pow,mul_div_assoc] at hf
  have h := mul_le_mul_of_nonneg_right ((le_div_iff₀ (pow_pos hk n)).mpr
    (by rw [mul_comm]; exact hf) : t^n/n.factorial ≤ Real.exp (k*t)/k^n) (Real.exp_pos (-t)).le
  calc primeGammaWeight n t = (t^n/n.factorial)*Real.exp (-t) := by unfold primeGammaWeight; ring
       _ ≤ _ := h
       _ = _ := by rw [sub_mul,one_mul,sub_eq_add_neg,Real.exp_add,inv_pow]; ring

private theorem strict_drop {f : ℝ → ℝ} {a : ℝ} (ha : a < 0) (hd : HasDerivAt f a 0) :
    ∀ᶠ x in 𝓝[>] (0:ℝ),f x < f 0 := by
  have hh := hd.tendsto_slope.mono_left (nhdsWithin_mono _ (show Ioi (0:ℝ) ⊆ {0}ᶜ from fun _ h => ne_of_gt h))
  filter_upwards [hh.eventually_lt_const ha,self_mem_nhdsWithin] with x hx (hx₀ : 0 < x)
  rw [slope_def_field,sub_zero,div_lt_iff₀ hx₀,zero_mul,sub_neg] at hx
  exact hx

/-- Small positive and negative tilts suppress opposite tails of a gamma
window. Their first variations have opposite signs at its two endpoints. -/
private theorem choose_tilts {B U V s : ℝ} (hB₀ : 0 < B) (hB : B < 1) (hs : s < B)
    (hU : U < (1-B)⁻¹) (hV : (1-B)⁻¹ < V) :
    ∃ c η q : ℝ,B < c ∧ 0 < η ∧ 0 < 1-c-η ∧ 1 < q ∧ q < (1-B)⁻¹ ∧
      Real.exp (η*U)/(1-c+η) ≤ q ∧ Real.exp (-η*V)/(1-c-η) ≤ q ∧
      (1-s)⁻¹ ≤ q := by
  let A := 1-B
  have hA : 0 < A := sub_pos.mpr hB
  have h₁ : U*A < 1 := (lt_div_iff₀ hA).mp (by simpa only [one_div] using hU)
  have h₂ : 1 < V*A := (div_lt_iff₀ hA).mp (by simpa only [one_div] using hV)
  let f := fun x : ℝ => Real.exp (x*U)/(A+x)
  let g := fun x : ℝ => Real.exp (-x*V)/(A-x)
  have hf : HasDerivAt f ((U*A-1)/A^2) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).mul_const U).exp.div ((hasDerivAt_id (0:ℝ)).const_add A) (by simpa using hA.ne')) using 1 <;> simp [f]
  have hg : HasDerivAt g ((1-V*A)/A^2) 0 := by
    convert ((((hasDerivAt_id (0:ℝ)).neg.mul_const V).exp).div
      ((hasDerivAt_const (0:ℝ) A).sub (hasDerivAt_id (0:ℝ))) (by simpa using hA.ne')) using 1 <;> simp [g] <;> ring
  obtain ⟨η,hfη,hgη,hηA,hη⟩ := (((strict_drop (div_neg_of_neg_of_pos (sub_neg.mpr h₁) (sq_pos_of_pos hA)) hf).and
    (strict_drop (div_neg_of_neg_of_pos (sub_neg.mpr h₂) (sq_pos_of_pos hA)) hg)).and
    (((Iio_mem_nhds hA).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)).exists
  have hfη' : Real.exp (η*U)/(1-B+η) < (1-B)⁻¹ := by simpa [f,A] using hfη
  have hgη' : Real.exp (-η*V)/(1-B-η) < (1-B)⁻¹ := by simpa [g,A] using hgη
  have hsmall : η < 1-B := hηA
  have hη₀ : 0 < η := hη
  have c₁ : ContinuousAt (fun b : ℝ => Real.exp (η*U)/(1-b+η)) B :=
    continuousAt_const.div (by fun_prop) (by linarith only [hB,hη₀])
  have c₂ : ContinuousAt (fun b : ℝ => Real.exp (-η*V)/(1-b-η)) B :=
    continuousAt_const.div (by fun_prop) (by linarith only [hsmall])
  have c₃ : ContinuousAt (fun b : ℝ => 1-b-η) B := by fun_prop
  have hcg := ((c₁.eventually_lt continuousAt_const hfη').and
      ((c₂.eventually_lt continuousAt_const hgη').and
        (continuousAt_const.eventually_lt c₃ (by linarith only [hsmall])))).filter_mono nhdsWithin_le_nhds
  obtain ⟨c,⟨hc₁,hc₂,hc₃⟩,hc⟩ := (hcg.and (self_mem_nhdsWithin (s := Ioi B))).exists
  have hsinv : (1-s)⁻¹ < (1-B)⁻¹ := (inv_lt_inv₀ (by linarith only [hs,hB]) hA).mpr (by linarith only [hs])
  have hlevel := max_lt (max_lt hc₁ hc₂) hsinv
  have one_lt : 1 < (1-B)⁻¹ := (one_lt_inv₀ hA).mpr (by linarith only [hB₀])
  obtain ⟨q,hq,hqB⟩ := exists_between (max_lt one_lt hlevel)
  have hq' := (max_lt_iff.mp hq).2
  have hlo := max_lt_iff.mp (max_lt_iff.mp hq').1
  exact ⟨c,η,q,hc,hη₀,hc₃,(max_lt_iff.mp hq).1,hqB,hlo.1.le,hlo.2.le,(max_lt_iff.mp hq').2.le⟩

private theorem tilt_on_side {c e w q t : ℝ} (n : ℕ) (ht : 0 ≤ t)
    (hk : 0 < 1-c+e) (hc : Real.exp (e*w)/(1-c+e) ≤ q) (hside : e*t ≤ n*(e*w)) :
    primeGammaWeight n t ≤ q^n*Real.exp (-c*t) := by
  let k := 1-c+e
  have he := (Real.exp_le_exp.mpr hside).trans_eq (Real.exp_nat_mul (e*w) n)
  calc
    _ ≤ k⁻¹^n*Real.exp ((k-1)*t) := gamma_tilt hk n ht
    _ = (k⁻¹^n*Real.exp (e*t))*Real.exp (-c*t) := by
      rw [mul_assoc,←Real.exp_add,show (k-1)*t=e*t+ -c*t by dsimp [k]; ring]
    _ ≤ (k⁻¹^n*Real.exp (e*w)^n)*Real.exp (-c*t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (pow_nonneg (inv_nonneg.mpr hk.le) n)) (Real.exp_pos _).le
    _ = (Real.exp (e*w)/(1-c+e))^n*Real.exp (-c*t) := by rw [div_pow,inv_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le hk.le) hc _) (Real.exp_pos _).le

private def gammaWindowCost (v : ℝ → ℝ) (c s δ M : ℝ) :=
  (∫ t in Ioi (0:ℝ),Real.exp (-c*t)*|v t|) + ∫ t in Ioi (0:ℝ),M*Real.exp ((δ-s)*t)

private theorem quiet_window_bound {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n,IntegrableOn (fun t => primeGammaWeight n t*v t) (Ioi 0))
    {c η q U V s δ M : ℝ} (hd : c ∈ waveLaplaceDomain v) (hη : 0 < η)
    (hk : 0 < 1-c-η) (hq₀ : 0 < q) (hs : δ < s) (hs₁ : s < 1) (hM : 0 ≤ M)
    (hlo : Real.exp (η*U)/(1-c+η) ≤ q) (hhi : Real.exp (-η*V)/(1-c-η) ≤ q)
    (hmiddle : (1-s)⁻¹ ≤ q) (n : ℕ)
    (hquiet : ∀ t ∈ Ioo (n*U) (n*V),v t ≤ M*Real.exp (δ*t)) :
    gammaSignMass v n ≤ q^n*gammaWindowCost v c s δ M := by
  have hmI : IntegrableOn (fun t : ℝ => M*Real.exp ((δ-s)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (sub_neg.mpr hs) 0).const_mul M
  let major := fun t => Real.exp (-c*t)*|v t|+M*Real.exp ((δ-s)*t)
  have hmj : IntegrableOn major (Ioi 0) := hd.add hmI
  rw [show q^n*gammaWindowCost v c s δ M = ∫ t in Ioi (0:ℝ), q^n*major t by
    rw [integral_const_mul]; simp only [major,gammaWindowCost,integral_add hd hmI]]
  apply integral_mono_ae (sign_integrable hm (hi n)) (hmj.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : t ∈ Ioi (0:ℝ))
  have hpos := weight_nonneg n ht
  have hqpos := pow_nonneg hq₀.le n
  have tail (htail : primeGammaWeight n t ≤ q^n*Real.exp (-c*t)) :
      primeGammaWeight n t*max (v t) 0 ≤ q^n*major t := by
    calc _ ≤ (q^n*Real.exp (-c*t))*|v t| :=
           mul_le_mul htail (max_le (le_abs_self _) (abs_nonneg _)) (le_max_right _ _) (by positivity)
         _ ≤ _ := by
           rw [mul_assoc]
           exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hM (Real.exp_pos _).le)) hqpos
  by_cases hlow : t ≤ n*U
  · apply tail (tilt_on_side n ht.le (by linarith only [hk,hη]) hlo ?_)
    linarith only [mul_le_mul_of_nonneg_left hlow hη.le]
  by_cases hhigh : n*V ≤ t
  · apply tail (tilt_on_side n ht.le (by linarith only [hk] : 0 < 1-c+(-η)) (by simpa only [sub_eq_add_neg] using hhi) ?_)
    linarith only [mul_le_mul_of_nonneg_left hhigh hη.le]
  have hm' := hquiet t ⟨lt_of_not_ge hlow,lt_of_not_ge hhigh⟩
  have hp := gamma_tilt (sub_pos.mpr hs₁) n ht.le
  calc
    _ ≤ ((1-s)⁻¹^n*Real.exp (((1-s)-1)*t))*(M*Real.exp (δ*t)) :=
      mul_le_mul hp (max_le hm' (mul_nonneg hM (Real.exp_pos _).le)) (le_max_right _ _) (by positivity)
    _ = (1-s)⁻¹^n*(M*Real.exp ((δ-s)*t)) := by
      rw [show ((1-s)-1)*t = -s*t by ring,show (δ-s)*t = -s*t+δ*t by ring,Real.exp_add]; ring
    _ ≤ q^n*(M*Real.exp ((δ-s)*t)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr hs₁.le)) hmiddle n)
        (mul_nonneg hM (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))) hqpos

/-- Positive and negative excursions occur in the same arbitrarily narrow
relative window, at each exponential amplitude below the abscissa. -/
theorem opposite_excursions_at_the_laplace_saddle {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n,IntegrableOn (fun t => primeGammaWeight n t*v t) (Ioi 0))
    (hs : Summable fun n => |∫ t in Ioi (0:ℝ),primeGammaWeight n t*v t|)
    {B : ℝ} (hB₀ : 0 < B) (hB : B < 1)
    (hfail : ∀ b < B,b ∉ waveLaplaceDomain v) (hfinite : ∀ c > B,c ∈ waveLaplaceDomain v)
    {U V δ M : ℝ} (hU : U < (1-B)⁻¹) (hV : (1-B)⁻¹ < V) (hδ : δ < B) (hM : 0 ≤ M) :
    ∃ᶠ n : ℕ in atTop,
      (∃ t ∈ Ioo (n*U) (n*V),M*Real.exp (δ*t) < v t) ∧
      (∃ t ∈ Ioo (n*U) (n*V),v t < -(M*Real.exp (δ*t))) := by
  obtain ⟨s,hδs,hsB⟩ := exists_between hδ
  obtain ⟨c,η,q,hc,hη,hk,hq,hqB,hlo,hhi,hmid⟩ := choose_tilts hB₀ hB hsB hU hV
  let C := gammaWindowCost v c s δ M
  have hcn : gammaWindowCost (fun t => -v t) c s δ M = C := by simp only [gammaWindowCost,abs_neg,C]
  have hd := hfinite c hc
  have hd' : c ∈ waveLaplaceDomain (fun t => -v t) := by simpa only [waveLaplaceDomain,mem_setOf_eq,abs_neg] using hd
  have hi' (n : ℕ) : IntegrableOn (fun t => primeGammaWeight n t*(-v t)) (Ioi 0) :=
    (hi n).neg.congr (Eventually.of_forall fun t => (mul_neg ..).symm)
  refine (gamma_at_every_order hm hi hs hB hfail hq hqB C).mono fun n hh => ?_
  obtain ⟨hp,hn⟩ := lt_min_iff.mp hh
  constructor
  · by_contra! quiet
    have h := quiet_window_bound hm hi hd hη hk (zero_lt_one.trans hq) hδs (hsB.trans hB) hM hlo hhi hmid n quiet
    exact hp.not_ge (by simpa only [C,mul_comm] using h)
  · by_contra! quiet
    have he := quiet_window_bound hm.neg hi' hd' hη hk (zero_lt_one.trans hq) hδs (hsB.trans hB) hM hlo hhi hmid n
      (fun t ht => neg_le_of_neg_le (quiet t ht))
    rw [hcn,mul_comm] at he
    exact hn.not_ge he

private theorem prime_wave_upper_damping {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) :
    (7/8:ℝ) ∈ waveLaplaceDomain (fun t => (ordinaryPrimeWave H t).re) := by
  obtain ⟨P,hP,_⟩ := ordinaryPrimeWave_hilbert hH
  have hI := (integrableOn_laplaceRay (φ := (P:ℝ → ℂ)) P.memLp (w := 1/8) (by norm_num)).norm
  have hm : Measurable (fun t => (ordinaryPrimeWave H t).re) := by
    apply Complex.continuous_re.measurable.comp
    apply Measurable.tsum
    intro q
    exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (hH.meas.comp (measurable_id.sub_const _)))
  apply hI.mono' ((Measurable.mul (by fun_prop) hm.abs).aestronglyMeasurable)
  filter_upwards [hP] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)),ht,norm_mul,norm_mul]
  have he : ‖cexp (-(3/4)*(t:ℂ))‖*‖expRay (1/8) t‖=Real.exp (-(7/8)*t) := by
    rw [Complex.norm_exp,norm_expRay,← Real.exp_add]
    congr 1
    norm_num [Complex.mul_re]; ring
  rw [←he]
  calc _ ≤ (‖cexp (-(3/4)*(t:ℂ))‖*‖expRay (1/8) t‖)*‖ordinaryPrimeWave H t‖ :=
           mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
       _ = _ := by ring

/-- Three confined crossings force large opposite ordinary-prime values
in the same interval about every sufficiently well sampled saddle scale.
The abscissa B and the double-neutral combination are fixed before the
relative width and the amplitude exponent are chosen. -/
theorem IsCriticalLadder.exists_same_relative_window_excursions {R : Fin 3 → ℝ} {Φ : Fin 3 → ℝ → ℝ}
    (hL : IsCriticalLadder 2 R Φ) :
    ∃ (c : Fin 3 → ℝ) (B : ℝ),c ≠ 0 ∧ 0 < B ∧ B ≤ 7/8 ∧
      let H := fun u => ∑ i,c i*Φ i u
      let v := fun t => (ordinaryPrimeWave H t).re
      negativeHalfLineLaplace (cx H) (-(1/2))=0 ∧ negativeHalfLineLaplace (cx H) 0=0 ∧
      B=sInf (waveLaplaceDomain v) ∧ ∀ U V δ M : ℝ,U < (1-B)⁻¹ → (1-B)⁻¹ < V → δ < B → 0 ≤ M →
        ∃ᶠ n : ℕ in atTop,
          (∃ t ∈ Ioo (n*U) (n*V),M*Real.exp (δ*t) < v t) ∧
          (∃ t ∈ Ioo (n*U) (n*V),v t < -(M*Real.exp (δ*t))) := by
  obtain ⟨c,b,hc,hb,ha,hz,hpos,_⟩ := hL.exists_double_neutral_opposite_prime_mass
  let H := fun u => ∑ i,c i*Φ i u
  let v := fun t => (ordinaryPrimeWave H t).re
  have hd : CriticalHalfLineEnergyDomain H := (hL.bare_neg_of_nonzero hc).1
  have hm : Measurable v := by
    apply Complex.continuous_re.measurable.comp
    apply Measurable.tsum
    intro q
    exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hd.meas.comp (measurable_id.sub_const _)))
  have h₁ : (7/8:ℝ) ∈ waveLaplaceDomain v := prime_wave_upper_damping hd
  have h₀ : b ∉ waveLaplaceDomain v := by
    intro h
    apply hpos
    apply h.mono' (((by fun_prop : Measurable fun t : ℝ => Real.exp (-b*t)).mul (hm.max measurable_const)).aestronglyMeasurable)
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))]
      exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (Real.exp_pos _).le
  have hlow : ∀ s ∈ waveLaplaceDomain v,b ≤ s := fun s hs => le_of_not_gt fun h => h₀ (domain_up hm hs h.le)
  let B := sInf (waveLaplaceDomain v)
  have hne : (waveLaplaceDomain v).Nonempty := ⟨_,h₁⟩
  have hbd : BddBelow (waveLaplaceDomain v) := ⟨b,hlow⟩
  have hBp : 0 < B := hb.trans_le (le_csInf hne hlow)
  have hB₁ : B ≤ 7/8 := csInf_le hbd h₁
  obtain ⟨hi,hs⟩ := neutral_ordinary_gamma_moments hd ha hz
  refine ⟨c,B,hc,hBp,hB₁,ha,hz,rfl,fun U V δ M hU hV hδ hM => ?_⟩
  apply opposite_excursions_at_the_laplace_saddle hm hi hs hBp (by linarith only [hB₁]) _ _ hU hV hδ hM
  · exact fun s hs hm => hs.not_ge (csInf_le hbd hm)
  · intro z hz
    obtain ⟨s,hs,hsz⟩ := exists_lt_of_csInf_lt hne hz
    exact domain_up hm hs hsz.le

/-- Away from RH and the lone-quartet alternative, the two signs have
exponential excursions whose times have ratio arbitrarily close to one. -/
theorem riemannHypothesis_or_quartet_or_nearby_prime_excursions :
    RiemannHypothesis ∨ (∃ ρ,HasSingleOffLineQuartet ρ) ∨
      ∃ (R : Fin 3 → ℝ) (Φ : Fin 3 → ℝ → ℝ) (c : Fin 3 → ℝ) (B : ℝ),
        IsCriticalLadder 2 R Φ ∧ c ≠ 0 ∧ 0 < B ∧
        let H := fun u => ∑ i,c i*Φ i u
        let v := fun t => (ordinaryPrimeWave H t).re
        negativeHalfLineLaplace (cx H) (-(1/2))=0 ∧ negativeHalfLineLaplace (cx H) 0=0 ∧
        ∀ ε δ M T : ℝ,0 < ε → δ < B → 0 ≤ M →
          ∃ t s : ℝ,T < t ∧ T < s ∧ 0 < t ∧ |s/t-1| < ε ∧
            M*Real.exp (δ*t) < v t ∧ v s < -(M*Real.exp (δ*s)) := by
  classical
  by_cases hq : ∃ ρ,HasSingleOffLineQuartet ρ
  · exact Or.inr (Or.inl hq)
  rcases no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp (not_exists.mp hq) with h|h4
  · exact Or.inl h
  rcases riemannHypothesis_or_criticalLadder with h|⟨_,_,_,_,_,hL⟩
  · exact Or.inl h
  obtain ⟨R,Φ,hL,-,-⟩ := hL 2 ((by norm_num : (3:ℕ∞) ≤ 4).trans h4)
  obtain ⟨c,B,hc,hB,hB',ha,hz,_,he⟩ := hL.exists_same_relative_window_excursions
  refine Or.inr (Or.inr ⟨R,Φ,c,B,hL,hc,hB,ha,hz,?_⟩)
  intro ε δ M T hε hδ hM
  let Q := (1-B)⁻¹
  have hQ : 0 < Q := inv_pos.mpr (by linarith only [hB'])
  let η := min (Q/4) (ε*Q/8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hl : Q/2 < Q-η := by linarith only [min_le_left (Q/4) (ε*Q/8),hQ]
  have hp := he (Q-η) (Q+η) δ M (sub_lt_self _ hη) (lt_add_of_pos_right _ hη) hδ hM
  obtain ⟨N,hN⟩ := exists_nat_gt (max (T/(Q-η)) 0)
  obtain ⟨n,⟨⟨t,ht,htv⟩,⟨s,hs,hsv⟩⟩,hn⟩ := (hp.and_eventually (eventually_ge_atTop N)).exists
  have hn' : max (T/(Q-η)) 0 < (n:ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  have hn₀ : 0 < (n:ℝ) := (le_max_right _ _).trans_lt hn'
  have hL₀ : 0 < Q-η := (half_pos hQ).trans hl
  have hT : T < (n:ℝ)*(Q-η) := (div_lt_iff₀ hL₀).mp ((le_max_left _ _).trans_lt hn')
  have ht₀ : 0 < t := (mul_pos hn₀ hL₀).trans ht.1
  refine ⟨t,s,hT.trans ht.1,hT.trans hs.1,ht₀,?_,htv,hsv⟩
  have hsep : |s-t| < (n:ℝ)*(2*η) := abs_lt.mpr ⟨by linarith only [hs.1,ht.2],by linarith only [hs.2,ht.1]⟩
  have hη₂ : 2*η ≤ ε*(Q/2) := by
    have he' : η ≤ ε*Q/8 := min_le_right _ _
    linarith only [he',mul_pos hε hQ]
  rw [show s/t-1=(s-t)/t by field_simp [ht₀.ne'],abs_div,abs_of_pos ht₀,div_lt_iff₀ ht₀]
  calc _ < n*(2*η) := hsep
       _ ≤ n*(ε*(Q/2)) := mul_le_mul_of_nonneg_left hη₂ hn₀.le
       _ = ε*(n*(Q/2)) := by ring
       _ < ε*t := mul_lt_mul_of_pos_left ((mul_lt_mul_of_pos_left hl hn₀).trans ht.1) hε

end GaloisForLFunctions.ExclusionOfTheCriticalState
