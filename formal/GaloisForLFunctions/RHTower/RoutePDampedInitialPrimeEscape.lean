import GaloisForLFunctions.RHTower.MobiusDivisorPrimeBlockEnergyEscape
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private def dampedFactor (σ : ℝ) (p : ℕ) (t : ℝ) : ℂ :=
  1 - Complex.ofReal ((p : ℝ) ^ (-σ)) * Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)

private lemma dampedFactor_sq (σ : ℝ) (p : ℕ) (t : ℝ) :
    ‖dampedFactor σ p t‖ ^ 2 =
      1 + ((p : ℝ) ^ (-σ)) ^ 2 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) := by
  have he : Complex.normSq (Complex.exp (((-(t*Real.log p) : ℝ) : ℂ)*Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero, one_pow]
  rw [← Complex.normSq_eq_norm_sq, dampedFactor, Complex.normSq_sub,
    Complex.normSq_mul, Complex.normSq_ofReal, he]
  simp only [Complex.normSq_one, one_mul, mul_one, Complex.conj_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, Real.exp_zero]
  ring_nf
  simp only [Real.cos_neg]

private lemma damped_radius_bound {σ : ℝ} (hσ : 1/2 ≤ σ) {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 3/4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : (Real.sqrt p)^2 = p := Real.sq_sqrt hp0.le
  have hr : (p : ℝ) ^ (-σ) ≤ (Real.sqrt p)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine ⟨Real.rpow_nonneg hp0.le _, hr.trans ?_⟩
  have hs0 := Real.sqrt_pos.mpr hp0
  rw [← one_div, div_le_iff₀ hs0]
  nlinarith [sq_nonneg (Real.sqrt p-4/3)]

private lemma damped_factor_loss {σ : ℝ} (hσ : 1/2 ≤ σ) {p : ℕ}
    (hp : p.Prime) (t : ℝ) :
    Real.exp (-8 * (p : ℝ) ^ (-σ)) ≤ ‖dampedFactor σ p t‖^2 := by
  obtain ⟨hr0, hr⟩ := damped_radius_bound hσ hp
  have hlog := neg_log_one_sub_le_of_le hr0 hr (by norm_num : (3/4 : ℝ) < 1)
  norm_num at hlog
  have hpos : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
  have he : Real.exp (-4 * (p : ℝ) ^ (-σ)) ≤ 1 - (p : ℝ) ^ (-σ) := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs := mul_self_le_mul_self (Real.exp_pos _).le he
  have hn := dampedFactor_sq σ p t
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log p))
    (show 0 ≤ 2 * (p : ℝ) ^ (-σ) by positivity)
  have hsq : (1 - (p : ℝ) ^ (-σ))^2 ≤ ‖dampedFactor σ p t‖^2 := by
    nlinarith only [hn, hc]
  have heq : Real.exp (-8 * (p : ℝ) ^ (-σ)) =
      Real.exp (-4 * (p : ℝ) ^ (-σ)) * Real.exp (-4 * (p : ℝ) ^ (-σ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hs.trans (by simpa only [pow_two] using hsq)

private lemma damped_small_prime_loss (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    {σ y : ℝ} (hσ : σ < 1) (hy : 1 ≤ y) :
    (∑ p ∈ R, if (p : ℝ) < Real.sqrt y then (p : ℝ)^(-σ) else 0) ≤
      (Real.sqrt y)^(1-σ) * (1 + Real.log (Real.sqrt y)) := by
  rw [← Finset.sum_filter]
  have hs1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have hsub : R.filter (fun p : ℕ => (p : ℝ) < Real.sqrt y) ⊆ Icc 1 ⌊Real.sqrt y⌋₊ := by
    intro p hp
    obtain ⟨hpR, hp⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(hR p hpR).one_lt.le, Nat.le_floor hp.le⟩
  calc
    _ ≤ ∑ p ∈ Icc 1 ⌊Real.sqrt y⌋₊, (p : ℝ)^(-σ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ Icc 1 ⌊Real.sqrt y⌋₊, (Real.sqrt y)^(1-σ) * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
      have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
      have hps : (p : ℝ) ≤ Real.sqrt y :=
        (Nat.cast_le.mpr (mem_Icc.mp hp).2).trans (Nat.floor_le (Real.sqrt_nonneg y))
      have he : (p : ℝ)^(-σ) = (p : ℝ)^(1-σ) * (p : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]
        congr 1
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hp0.le hps (by linarith)) (inv_nonneg.mpr hp0.le)
    _ = (Real.sqrt y)^(1-σ) * (harmonic ⌊Real.sqrt y⌋₊ : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Finset.mul_sum, one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log _ hs1) (by positivity)

private lemma damped_high_phase {y : ℝ} (hy : 1 < y)
    {p : ℕ} (hp : p.Prime) (hlo : Real.sqrt y ≤ p) (hhi : (p : ℝ) ≤ y) :
    Real.cos ((Real.pi / Real.log y) * Real.log p) ≤ 0 := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogs := Real.log_le_log (Real.sqrt_pos.mpr hy0) hlo
  rw [Real.log_sqrt hy0.le] at hlogs
  have hlogp := Real.log_le_log hp0 hhi
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · calc
      Real.pi/2 = (Real.pi/Real.log y)*(Real.log y/2) := by field_simp
      _ ≤ (Real.pi/Real.log y)*Real.log p :=
        mul_le_mul_of_nonneg_left hlogs (by positivity)
  · have h := mul_le_mul_of_nonneg_left hlogp
        (show 0 ≤ Real.pi/Real.log y by positivity)
    have he : (Real.pi/Real.log y)*Real.log y = Real.pi := by field_simp
    rw [he] at h
    nlinarith [Real.pi_pos]

private lemma damped_window_gain {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 27 ≤ y) :
    (1 + y^(-σ))^(mobiusCriticalPrimeWindow y).card ≤
      ‖∏ p ∈ mobiusCriticalPrimeWindow y,
        dampedFactor σ p (Real.pi/Real.log y)‖^2 := by
  rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    obtain ⟨hpp, _, hpy⟩ := (mem_windowPrimes (by linarith : 0 ≤ y/3)
      (by linarith : 0 ≤ y)).mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hr := Real.rpow_le_rpow_of_nonpos hp0 hpy (by linarith : -σ ≤ 0)
    have hc := mobiusCriticalPrimeWindow_cos_le_neg_half hy hp
    rw [dampedFactor_sq]
    have hmul := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ 2*(p : ℝ)^(-σ) by positivity)
    nlinarith only [hr, hmul, sq_nonneg ((p : ℝ)^(-σ))]

private lemma damped_initial_lower {σ y : ℝ} (hσ0 : 1/2 ≤ σ)
    (hσ1 : σ < 1) (hy : 27 ≤ y) :
    Real.exp (-8*(Real.sqrt y)^(1-σ)*(1+Real.log (Real.sqrt y))) *
        (1+y^(-σ))^(mobiusCriticalPrimeWindow y).card ≤
      ‖∏ p ∈ windowPrimes 0 y, dampedFactor σ p (Real.pi/Real.log y)‖^2 := by
  have hy0 : 0 ≤ y := by linarith
  let Q := windowPrimes 0 y
  let P := mobiusCriticalPrimeWindow y
  let R := Q \ P
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ (p : ℝ) ≤ y := by
    obtain ⟨hpp, _, hpy⟩ := (mem_windowPrimes (by norm_num) hy0).mp hp
    exact ⟨hpp, hpy⟩
  have hPQ : P ⊆ Q := by
    intro p hp
    obtain ⟨hpp, _, hpy⟩ := (mem_windowPrimes (by positivity) hy0).mp hp
    exact (mem_windowPrimes (by norm_num) hy0).mpr
      ⟨hpp, by exact_mod_cast hpp.pos, hpy⟩
  have hR (p : ℕ) (hp : p ∈ R) : p.Prime ∧ (p : ℝ) ≤ y :=
    hQ p (Finset.mem_sdiff.mp hp).1
  let u : ℕ → ℝ := fun p => if (p : ℝ) < Real.sqrt y then (p : ℝ)^(-σ) else 0
  have hpoint (p : ℕ) (hp : p ∈ R) :
      Real.exp (-8*u p) ≤ ‖dampedFactor σ p (Real.pi/Real.log y)‖^2 := by
    dsimp [u]
    split_ifs with hps
    · exact damped_factor_loss hσ0 (hR p hp).1 _
    · simp only [mul_zero, Real.exp_zero]
      rw [dampedFactor_sq]
      have hc := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 2*(p : ℝ)^(-σ) by positivity)
        (damped_high_phase (by linarith) (hR p hp).1 (le_of_not_gt hps) (hR p hp).2)
      nlinarith only [hc, sq_nonneg ((p : ℝ)^(-σ))]
  have hprod := Finset.prod_le_prod (fun p hp => (Real.exp_pos (-8*u p)).le) hpoint
  rw [← Real.exp_sum, ← Finset.mul_sum] at hprod
  have hsum := damped_small_prime_loss R (fun p hp => (hR p hp).1) hσ1 (by linarith : 1 ≤ y)
  have hloss : Real.exp (-8*(Real.sqrt y)^(1-σ)*(1+Real.log (Real.sqrt y))) ≤
      ∏ p ∈ R, ‖dampedFactor σ p (Real.pi/Real.log y)‖^2 := by
    apply le_trans _ hprod
    apply Real.exp_le_exp.mpr
    change (∑ p ∈ R, u p) ≤ _ at hsum
    nlinarith only [hsum]
  have hwindow := damped_window_gain (by linarith : 0 ≤ σ) hy
  have hmult := mul_le_mul hloss hwindow (by positivity)
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
  have he : R ∪ P = Q := Finset.sdiff_union_of_subset hPQ
  have hd : Disjoint R P := Finset.sdiff_disjoint
  rw [norm_prod, ← Finset.prod_pow]
  change _ ≤ ∏ p ∈ Q, ‖dampedFactor σ p (Real.pi/Real.log y)‖^2
  rw [← he, Finset.prod_union hd]
  simpa only [norm_prod, ← Finset.prod_pow] using hmult

private lemma damped_window_card_lower :
    ∀ᶠ y : ℝ in atTop, y/(3*Real.log y) ≤ ((mobiusCriticalPrimeWindow y).card : ℝ) := by
  have hscale : Tendsto (fun y : ℝ => y/3) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hh := hscale.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge (K := 3) (by norm_num))
  filter_upwards [hh, eventually_gt_atTop (3 : ℝ)] with y hh hy
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log (y/3) := Real.log_pos (by linarith)
  have hlo : Real.log (y/3) ≤ Real.log y :=
    Real.log_le_log (by positivity) (by linarith)
  have hc := GaloisForLFunctions.HTGeometry.card_primesInIoc
    (Nat.floor_le_floor (show y/3 ≤ y by linarith))
  have he : GaloisForLFunctions.HTGeometry.primesInIoc ⌊y/3⌋₊ ⌊y⌋₊ =
      mobiusCriticalPrimeWindow y := rfl
  rw [he] at hc
  norm_num only [show (3 : ℝ)-1=2 by norm_num, div_self (by norm_num : (2 : ℝ) ≠ 0),
    one_mul, show (3 : ℝ)*(y/3)=y by ring] at hh
  rw [← hc] at hh
  calc
    y/(3*Real.log y) = (y/3)/Real.log y := by ring
    _ ≤ (y/3)/Real.log (y/3) := div_le_div_of_nonneg_left (by positivity) hlog hlo
    _ ≤ _ := hh

private lemma damped_window_exponential {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᶠ y : ℝ in atTop, Real.exp (y^(1-σ)/(6*Real.log y)) ≤
      (1+y^(-σ))^(mobiusCriticalPrimeWindow y).card := by
  filter_upwards [damped_window_card_lower, eventually_gt_atTop (3 : ℝ)] with y hn hy
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have hz0 : 0 ≤ y^(-σ) := Real.rpow_nonneg hy0.le _
  have hz1 : y^(-σ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ y)
      (show -σ ≤ 0 by linarith)
  have hlog := Real.le_log_one_add_of_nonneg hz0
  have hhalf : y^(-σ)/2 ≤ Real.log (1+y^(-σ)) := by
    apply le_trans _ hlog
    apply (le_div_iff₀ (by positivity : 0 < y^(-σ)+2)).mpr
    nlinarith
  have he : y*y^(-σ) = y^(1-σ) := by
    calc
      _ = y^(1 : ℝ)*y^(-σ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hy0, sub_eq_add_neg]
  have hcount := mul_le_mul_of_nonneg_right hn (show 0 ≤ y^(-σ)/2 by positivity)
  have hden : y^(1-σ)/(6*Real.log y) ≤
      ((mobiusCriticalPrimeWindow y).card : ℝ)*(y^(-σ)/2) := by
    calc
      _ = y/(3*Real.log y)*(y^(-σ)/2) := by rw [← he]; ring
      _ ≤ _ := hcount
  have hbound := hden.trans (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _))
  calc
    _ ≤ Real.exp (((mobiusCriticalPrimeWindow y).card : ℝ)*Real.log (1+y^(-σ))) :=
      Real.exp_le_exp.mpr hbound
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

private lemma damped_small_loss_absorbed {σ : ℝ} (hσ : σ < 1) :
    ∀ᶠ y : ℝ in atTop,
      8*(Real.sqrt y)^(1-σ)*(1+Real.log (Real.sqrt y)) ≤ y^(1-σ)/(12*Real.log y) := by
  let q : ℝ := 1-σ
  have hq : 0 < q := by dsimp [q]; linarith
  have hlog : Tendsto (fun y : ℝ => Real.log y/y^(q/4)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < q/4)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun y : ℝ => 1/y^(q/4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by positivity : 0 < q/4))
  have hsum : Tendsto (fun y : ℝ => (1+Real.log y)/y^(q/4)) atTop (𝓝 0) := by
    simpa only [← add_div, zero_add] using hinv.add hlog
  have hprod := hlog.mul hsum
  simp only [mul_zero] at hprod
  filter_upwards [hprod.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/96)),
    eventually_gt_atTop (1 : ℝ)] with y hy hy1
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy1
  have hz : 0 < y^(q/4) := Real.rpow_pos_of_pos hy0 _
  have hv : 0 < y^(q/2) := Real.rpow_pos_of_pos hy0 _
  have hratio : Real.log y*(1+Real.log y)/(y^(q/4))^2 < 1/96 := by
    change (Real.log y/y^(q/4))*((1+Real.log y)/y^(q/4)) < 1/96 at hy
    have he : (Real.log y/y^(q/4))*((1+Real.log y)/y^(q/4)) =
        Real.log y*(1+Real.log y)/(y^(q/4))^2 := by ring
    rwa [he] at hy
  have hzsq : (y^(q/4))^2 = y^(q/2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    ring
  have hvsq : (y^(q/2))^2 = y^q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    ring
  have hbase : 96*Real.log y*(1+Real.log y) ≤ y^(q/2) := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hz)).mp hratio
    rw [hzsq] at h
    linarith
  have hs : (Real.sqrt y)^(1-σ) = y^(q/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le]
    congr 1
    dsimp [q]
    ring
  rw [hs, Real.log_sqrt hy0.le]
  change 8*y^(q/2)*(1+Real.log y/2) ≤ y^q/(12*Real.log y)
  apply (le_div_iff₀ (by positivity : 0 < 12*Real.log y)).mpr
  have hscaled := mul_le_mul_of_nonneg_right hbase hv.le
  rw [← pow_two, hvsq] at hscaled
  nlinarith only [hscaled, mul_pos hv hl, mul_nonneg hv.le (sq_nonneg (Real.log y))]

private lemma damped_initial_exponential {σ : ℝ} (hσ0 : 1/2 ≤ σ) (hσ1 : σ < 1) :
    ∀ᶠ y : ℝ in atTop, Real.exp (y^(1-σ)/(12*Real.log y)) ≤
      ‖∏ p ∈ windowPrimes 0 y, dampedFactor σ p (Real.pi/Real.log y)‖^2 := by
  filter_upwards [damped_window_exponential (by linarith : 0 ≤ σ),
    damped_small_loss_absorbed hσ1, eventually_ge_atTop (27 : ℝ)] with y hwin hloss hy
  have he : Real.exp (y^(1-σ)/(12*Real.log y)) ≤
      Real.exp (-8*(Real.sqrt y)^(1-σ)*(1+Real.log (Real.sqrt y))) *
        Real.exp (y^(1-σ)/(6*Real.log y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htwo : y^(1-σ)/(6*Real.log y) = 2*(y^(1-σ)/(12*Real.log y)) := by ring
    rw [htwo]
    linarith
  exact (he.trans (mul_le_mul_of_nonneg_left hwin (Real.exp_pos _).le)).trans
    (damped_initial_lower hσ0 hσ1 hy)

private def dampedUnitMellin (α t : ℝ) : ℂ :=
  mellin (fun x : ℝ => (divisorContinuousUnitHead x : ℂ)) (-(α+(t : ℂ)*Complex.I))

private lemma damped_unit_pos {α : ℝ} (hα : 1/2 < α) :
    0 < (dampedUnitMellin α 0).re := by
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x : ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x : ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  have hi := mellinConvergent_mobiusDivisorContinuousHead ∅ (s := (α : ℂ)) (by simpa using hα)
  rw [hempty] at hi
  change IntegrableOn (fun x : ℝ => (x : ℂ)^(-(α : ℂ)-1)*(divisorContinuousUnitHead x : ℂ))
    (Ioi 0) at hi
  have he (x : ℝ) (hx : 0 < x) :
      ((x : ℂ)^(-(α : ℂ)-1)*(divisorContinuousUnitHead x : ℂ)).re =
        x^(-α-1)*divisorContinuousUnitHead x := by
    rw [show -(α : ℂ)-1 = ((-α-1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hir : IntegrableOn (fun x : ℝ => x^(-α-1)*divisorContinuousUnitHead x) (Ioi 0) := by
    apply hi.re.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact he x hx
  have hp : 0 < ∫ x in Ioi (0 : ℝ), x^(-α-1)*divisorContinuousUnitHead x := by
    apply (integral_pos_iff_support_of_nonneg_ae _ hir).mpr
    · have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support
          (fun x : ℝ => x^(-α-1)*divisorContinuousUnitHead x) := by
        intro x hx
        exact (mul_pos (Real.rpow_pos_of_pos (by linarith [hx.1]) _)
          (divisorContinuousUnitHead_pos_first hx)).ne'
      apply lt_of_lt_of_le _ (measure_mono hsub)
      rw [Measure.restrict_apply measurableSet_Ioo,
        inter_eq_left.mpr (show Ioo (1 : ℝ) 2 ⊆ Ioi 0 from fun x hx => by
          change 0 < x; linarith [hx.1]), Real.volume_Ioo]
      norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (divisorContinuousUnitHead_nonneg x)
  have hr := integral_re hi
  simp only [RCLike.re_to_complex] at hr
  have hval : (dampedUnitMellin α 0).re =
      ∫ x in Ioi (0 : ℝ), x^(-α-1)*divisorContinuousUnitHead x := by
    unfold dampedUnitMellin mellin
    simp only [Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul]
    rw [← hr]
    apply setIntegral_congr_fun measurableSet_Ioi
    exact he
  rw [hval]
  exact hp

private lemma damped_unit_floor {α : ℝ} (hα : 1/2 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop,
      c ≤ ‖dampedUnitMellin α (Real.pi/Real.log y)‖^2 := by
  have hempty : (fun x : ℝ => (mobiusDivisorContinuousHead ∅ x : ℂ)) =
      fun x : ℝ => (divisorContinuousUnitHead x : ℂ) := by
    funext x
    simp [mobiusDivisorContinuousHead]
  have hd := differentiableAt_mellin_mobiusDivisorContinuousHead ∅
    (s := α+(0 : ℂ)*Complex.I) (by simpa using hα)
  rw [hempty] at hd
  have hc : ContinuousAt (fun t : ℝ => ‖dampedUnitMellin α t‖^2) 0 :=
    (hd.continuousAt.comp (f := fun t : ℝ => α+(t : ℂ)*Complex.I)
      (by fun_prop)).norm.pow 2
  have hp : 0 < ‖dampedUnitMellin α 0‖^2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    have h := damped_unit_pos hα
    rw [hz, Complex.zero_re] at h
    exact (lt_irrefl _ h)
  have ht : Tendsto (fun y : ℝ => Real.pi/Real.log y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  refine ⟨‖dampedUnitMellin α 0‖^2/2, by positivity, ?_⟩
  have hlim := hc.tendsto.comp ht
  exact (hlim.eventually (eventually_gt_nhds (half_lt_self hp))).mono (fun y hy => hy.le)

private lemma damped_source_weight (α y t : ℝ) (hy : 0 ≤ y) (hα : 1/2 < α) :
    ‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead (windowPrimes 0 y) x : ℂ))
      (-(α+(t : ℂ)*Complex.I))‖^2 =
        ‖dampedUnitMellin α t‖^2 *
          ‖∏ p ∈ windowPrimes 0 y, dampedFactor (α-1/2) p t‖^2 := by
  have hprime : ∀ p ∈ windowPrimes 0 y, p.Prime := fun p hp =>
    ((mem_windowPrimes (by norm_num) hy).mp hp).1
  have he : divisorCoreMellinEuler (windowPrimes 0 y) (α+(t : ℂ)*Complex.I) =
      ∏ p ∈ windowPrimes 0 y, dampedFactor (α-1/2) p t := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    unfold dampedFactor
    rw [Real.rpow_def_of_pos hp0, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [mellin_mobiusDivisorContinuousHead_euler _ hprime (by simpa using hα), he,
    norm_mul, mul_pow]
  exact mul_comm _ _

private lemma damped_source_exponential {α : ℝ} (hα0 : 1 ≤ α) (hα1 : α < 3/2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop,
      c*Real.exp (y^(3/2-α)/(12*Real.log y)) ≤
        ‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead (windowPrimes 0 y) x : ℂ))
          (-(α+((Real.pi/Real.log y : ℝ) : ℂ)*Complex.I))‖^2 := by
  obtain ⟨c, hc, hf⟩ := damped_unit_floor (by linarith : 1/2 < α)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hf, damped_initial_exponential
    (by linarith : 1/2 ≤ α-1/2) (by linarith : α-1/2 < 1),
    eventually_ge_atTop (0 : ℝ)] with y hf hg hy
  rw [damped_source_weight α y _ hy (by linarith)]
  rw [show 1-(α-1/2) = 3/2-α by ring] at hg
  exact mul_le_mul hf hg (Real.exp_pos _).le (by positivity)

private lemma damped_exponential_superpower {q c : ℝ} (hq : 0 < q) (hc : 0 < c)
    (A C : ℝ) (hA : 0 < A) :
    ∀ᶠ y : ℝ in atTop, C*y^A ≤ c*Real.exp (y^q/(12*Real.log y)) := by
  have hsmall : Tendsto (fun y : ℝ => (Real.log y)^2/y^q) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq).tendsto_div_nhds_zero
  have heps : 0 < 1/(12*(A+1)) := by positivity
  filter_upwards [hsmall.eventually (eventually_lt_nhds heps),
    eventually_ge_atTop (C/c), eventually_gt_atTop (1 : ℝ)] with y hh hcy hy
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy
  have hpq : 0 < y^q := Real.rpow_pos_of_pos hy0 _
  have hcross := (div_lt_div_iff₀ hpq (by positivity : 0 < 12*(A+1))).mp hh
  have hexp : (A+1)*Real.log y ≤ y^q/(12*Real.log y) := by
    apply (le_div_iff₀ (by positivity : 0 < 12*Real.log y)).mpr
    nlinarith only [hcross]
  have hp : y^(A+1) ≤ Real.exp (y^q/(12*Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hexp)
  have hcy' : C ≤ c*y := by
    have h := (div_le_iff₀ hc).mp hcy
    nlinarith only [h]
  calc
    _ ≤ (c*y)*y^A := mul_le_mul_of_nonneg_right hcy' (Real.rpow_nonneg hy0.le _)
    _ = c*y^(A+1) := by rw [Real.rpow_add hy0, Real.rpow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hc.le


private def dampedDensity (ε : ℝ) (P : Finset ℕ) (x : ℝ) : ℝ :=
  mobiusDivisorContinuousHead P x ^ 2 * x^(-3-ε)

private def dampedEnergy (ε : ℝ) (P : Finset ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), dampedDensity ε P x

private lemma dampedDensity_integrable {ε : ℝ} (hε : 0 < ε) (P : Finset ℕ) :
    IntegrableOn (dampedDensity ε P) (Ioi 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_mobiusDivisorContinuousHead P
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -2-ε < -1)
    zero_lt_one).const_mul (C^2)
  have hm : Measurable (dampedDensity ε P) := by
    have hh := measurable_mobiusDivisorContinuousHead P
    unfold dampedDensity
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold dampedDensity; positivity)]
  have hs := pow_le_pow_left₀ (abs_nonneg (mobiusDivisorContinuousHead P x)) (hbound x) 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hx0.le] at hs
  calc
    _ ≤ (C^2*x)*x^(-3-ε) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = C^2*x^(-2-ε) := by
      calc
        _ = C^2*(x^(1 : ℝ)*x^(-3-ε)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring

private lemma damped_mellin_le {ε α c : ℝ} (hε : 0 < ε)
    (hα : 1+ε/2 < α) (hc : 0 ≤ c) (P : Finset ℕ) (t : ℝ) :
    2*c*‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ))
      (-(α+(t : ℂ)*Complex.I))‖ ≤ dampedEnergy ε P + c^2/(2*α-2-ε) := by
  let s : ℂ := α+(t : ℂ)*Complex.I
  let F : ℝ → ℂ := fun x => (x : ℂ)^(-s-1)*(mobiusDivisorContinuousHead P x : ℂ)
  have hs : 1/2 < s.re := by dsimp [s]; simp only [Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_self, add_zero]; linarith
  have hi0 : IntegrableOn F (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, F] using
      mellinConvergent_mobiusDivisorContinuousHead P hs
  have his : IntegrableOn F (Ioi 1) := hi0.mono_set (Ioi_subset_Ioi zero_le_one)
  have he : mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ)) (-s) =
      ∫ x in Ioi (1 : ℝ), F x := by
    change (∫ x in Ioi (0 : ℝ), F x) = _
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one)
    intro x hx
    have hx1 : x ≤ 1 := le_of_not_gt hx.2
    simp [F, mobiusDivisorContinuousHead_eq_zero P hx1]
  have hnorm (x : ℝ) (hx : 1 < x) :
      ‖F x‖ = x^(-α-1)*|mobiusDivisorContinuousHead P x| := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx),
      Complex.norm_real, Real.norm_eq_abs]
    congr 2
    simp [s]
  have hp (x : ℝ) (hx : 1 < x) :
      2*c*‖F x‖ ≤ dampedDensity ε P x + c^2*x^(1+ε-2*α) := by
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hab : x^(-(3+ε)/2)*x^((1+ε)/2-α) = x^(-α-1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have ha : (x^(-(3+ε)/2))^2 = x^(-3-ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    have hb : (x^((1+ε)/2-α))^2 = x^(1+ε-2*α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    have hsq := sq_nonneg (|mobiusDivisorContinuousHead P x| * x^(-(3+ε)/2)-c*x^((1+ε)/2-α))
    simp only [sub_sq, mul_pow, sq_abs, ha, hb] at hsq
    have hm : 2*(|mobiusDivisorContinuousHead P x| * x^(-(3+ε)/2))*(c*x^((1+ε)/2-α)) =
        2*c*x^(-α-1)*|mobiusDivisorContinuousHead P x| := by
      calc
        _ = 2*c*|mobiusDivisorContinuousHead P x| * (x^(-(3+ε)/2)*x^((1+ε)/2-α)) := by ring
        _ = _ := by rw [hab]; ring
    rw [hm] at hsq
    rw [hnorm x hx, dampedDensity]
    nlinarith only [hsq]
  have hiE := dampedDensity_integrable hε P
  have ha : 1+ε-2*α < -1 := by linarith
  have hiK := integrableOn_Ioi_rpow_of_lt ha zero_lt_one
  have hmono := integral_mono_ae (his.norm.const_mul (2*c)) (hiE.add (hiK.const_mul (c^2)))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hp x hx)
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hiE (hiK.const_mul (c^2)), integral_const_mul,
    integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow] at hmono
  have hk : -(1 : ℝ)/(1+ε-2*α+1) = 1/(2*α-2-ε) := by
    rw [show 1+ε-2*α+1 = -(2*α-2-ε) by ring, div_neg]
    ring
  rw [hk] at hmono
  have hmono' : 2*c*(∫ x in Ioi (1 : ℝ), ‖F x‖) ≤
      dampedEnergy ε P + c^2/(2*α-2-ε) := by
    simpa only [dampedEnergy, mul_one_div] using hmono
  change 2*c*‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ)) (-s)‖ ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (by positivity)).trans hmono'

private lemma damped_mellin_sq_le {ε α : ℝ} (hε : 0 < ε)
    (hα : 1+ε/2 < α) (P : Finset ℕ) (t : ℝ) :
    (2*α-2-ε)*‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ))
      (-(α+(t : ℂ)*Complex.I))‖^2 ≤ dampedEnergy ε P := by
  let κ := 2*α-2-ε
  let m := ‖mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x : ℂ))
    (-(α+(t : ℂ)*Complex.I))‖
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hm : 0 ≤ m := norm_nonneg _
  have h := damped_mellin_le hε hα (mul_nonneg hκ.le hm) P t
  change 2*(κ*m)*m ≤ dampedEnergy ε P+(κ*m)^2/κ at h
  have he : (κ*m)^2/κ = κ*m^2 := by field_simp
  rw [he] at h
  change κ*m^2 ≤ _
  nlinarith only [h]

private lemma dampedDensity_le (ε : ℝ) (P : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    dampedDensity ε P x ≤ (9/25 : ℝ)*x^(-ε) := by
  have hb := abs_mobiusDivisorContinuousHead_le P x
  have hs := pow_le_pow_left₀ (abs_nonneg (mobiusDivisorContinuousHead P x)) hb 2
  simp only [sq_abs, mul_pow, Real.sq_sqrt hx.le] at hs
  have hsq : mobiusDivisorContinuousHead P x ^ 2 ≤ (9/25 : ℝ)*x^3 := by
    nlinarith only [hs]
  have hpow : x^3*x^(-3-ε) = x^(-ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    congr 1
    ring
  calc
    _ ≤ ((9/25 : ℝ)*x^3)*x^(-3-ε) := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by rw [mul_assoc, hpow]

private lemma damped_prefix_le {ε : ℝ} (hε : 0 < ε) (P : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X) :
    dampedEnergy ε P ≤ (∫ x in Ioi X, dampedDensity ε P x) + (9/25 : ℝ)*X := by
  have hi := dampedDensity_integrable hε P
  have hp : IntervalIntegrable (dampedDensity ε P) volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hpoint (x : ℝ) (hx : x ∈ Icc (1 : ℝ) X) : dampedDensity ε P x ≤ 9/25 := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    have hr : x^(-ε) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx.1 (show -ε ≤ 0 by linarith)
    exact (dampedDensity_le ε P hx0).trans (by nlinarith only [hr])
  have hm := intervalIntegral.integral_mono_on hX hp
    (intervalIntegrable_const (c := (9/25 : ℝ))) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi hX
  change (∫ x in Ioi (1 : ℝ), dampedDensity ε P x) ≤ _
  linarith

private lemma damped_uniform_strong {ε : ℝ} (hε : 1 < ε) (P : Finset ℕ) :
    dampedEnergy ε P ≤ (9/25 : ℝ)/(ε-1) := by
  have hi := dampedDensity_integrable (by linarith : 0 < ε) P
  have hk := integrableOn_Ioi_rpow_of_lt (by linarith : -ε < -1) zero_lt_one
  have h := integral_mono_ae hi (hk.const_mul (9/25 : ℝ))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact dampedDensity_le ε P (zero_lt_one.trans hx))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -ε < -1) zero_lt_one,
    Real.one_rpow] at h
  have he : (9/25 : ℝ)*(-1/(-ε+1)) = (9/25 : ℝ)/(ε-1) := by
    rw [show -ε+1=-(ε-1) by ring, div_neg]
    ring
  exact h.trans_eq he


private lemma initial_damped_energy_superpower {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (A C : ℝ) (hA : 0 < A) :
    ∀ᶠ y : ℝ in atTop, C*y^A ≤ dampedEnergy ε (windowPrimes 0 y) := by
  let α : ℝ := (5+ε)/4
  let κ : ℝ := 2*α-2-ε
  have hα : 1+ε/2 < α := by dsimp [α]; linarith
  have hα0 : 1 ≤ α := by dsimp [α]; linarith
  have hα1 : α < 3/2 := by dsimp [α]; linarith
  have hκ : 0 < κ := by dsimp [κ]; linarith
  obtain ⟨c, hc, hm⟩ := damped_source_exponential hα0 hα1
  have hp := damped_exponential_superpower (by linarith : 0 < 3/2-α)
    (mul_pos hκ hc) A C hA
  filter_upwards [hp, hm] with y hp hm
  have hM := damped_mellin_sq_le hε0 hα (windowPrimes 0 y) (Real.pi/Real.log y)
  have hmul := mul_le_mul_of_nonneg_left hm hκ.le
  change κ*_ ≤ dampedEnergy ε (windowPrimes 0 y) at hM
  calc
    _ ≤ (κ*c)*Real.exp (y^(3/2-α)/(12*Real.log y)) := hp
    _ = κ*(c*Real.exp (y^(3/2-α)/(12*Real.log y))) := by ring
    _ ≤ _ := hmul.trans hM

/-- Positive damping below one does not control the full-ray limit of the
natural initial-prime core. Its physical energy escapes every polynomial
prime-scale cutoff, even after every polynomial rescaling. -/
theorem routeP_damped_initial_prime_scaled_tail_escape {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 0 < A) (B : ℝ) :
    Tendsto (fun y : ℝ => (∫ x in Ioi (y^A),
      mobiusDivisorContinuousHead (windowPrimes 0 y) x ^ 2 * x^(-3-ε))/y^B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro L
  let C : ℝ := max L 0+1
  let D : ℝ := max A B+1
  have hC : 0 < C := by dsimp [C]; have := le_max_right L 0; linarith
  have hD : 0 < D := by dsimp [D]; have := le_max_left A B; linarith
  have hAD : A ≤ D := by dsimp [D]; have := le_max_left A B; linarith
  have hBD : B ≤ D := by dsimp [D]; have := le_max_right A B; linarith
  filter_upwards [initial_damped_energy_superpower hε0 hε1 D (C+9/25) hD,
    eventually_ge_atTop (1 : ℝ)] with y hy hy1
  have hy0 : 0 < y := by linarith
  have hpow : 1 ≤ y^A := Real.one_le_rpow hy1 hA.le
  have hpa : y^A ≤ y^D := Real.rpow_le_rpow_of_exponent_le hy1 hAD
  have hpb : y^B ≤ y^D := Real.rpow_le_rpow_of_exponent_le hy1 hBD
  have hp := damped_prefix_le hε0 (windowPrimes 0 y) hpow
  have hmass : C*y^D ≤ ∫ x in Ioi (y^A), dampedDensity ε (windowPrimes 0 y) x := by
    nlinarith only [hy, hp, hpa]
  have hscaled := (mul_le_mul_of_nonneg_left hpb hC.le).trans hmass
  have hLC : L ≤ C := by dsimp [C]; have := le_max_left L 0; linarith
  exact hLC.trans ((le_div_iff₀ (Real.rpow_pos_of_pos hy0 B)).mpr hscaled)

/-- Above the strict damping threshold, the literal source envelope gives
a uniform full-ray bound for every finite core. No claim about the endpoint
epsilon equal to one is made. -/
theorem routeP_strong_damping_core_uniform_bound {ε : ℝ} (hε : 1 < ε) (P : Finset ℕ) :
    (∫ x in Ioi (1 : ℝ), mobiusDivisorContinuousHead P x ^ 2 * x^(-3-ε)) ≤
      (9/25 : ℝ)/(ε-1) :=
  damped_uniform_strong hε P

end RHTower
