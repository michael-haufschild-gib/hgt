import GaloisForLFunctions.RHTower.ArithmeticStationaryEndpointOrientation
import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole

/-!
# Quantitative height reserves inside the stationary Fourier sector

The exact unit-anchor logarithmic power moment bounds height perturbations of the
actual Fourier atoms. The positive stationary-endpoint sine budget then gives a
strict negative collar inside the stationary sector. Its discarded margins are
retained in the reduced finite-budget comparison. The remaining head and RH are open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The actual power-weighted phase integral in dimensionless anchor coordinates. -/
def anchoredSineProfile (β t v : ℝ) : ℝ :=
  ∫ x in Ioi (1:ℝ), x^(-β)*Real.sin (anchoredLogPhase 1 t v x)

/-- The exact logarithmic moment controls every height perturbation. -/
theorem anchoredSineProfile_height_lipschitz {β : ℝ} (hβ : 1 < β) (t u v : ℝ) :
    |anchoredSineProfile β t v-anchoredSineProfile β u v| ≤ |t-u|/(β-1)^2 := by
  have hm := (RHTower.integrableOn_rpow_mul_log_Ioi_one (show 0 < β-1 by linarith)).const_mul |t-u|
  have he : -(β-1)-1 = -β := by ring
  simp only [he] at hm
  rw [anchoredSineProfile, anchoredSineProfile, ← integral_sub
    (integrable_anchoredLogSine (by norm_num) hβ)
    (integrable_anchoredLogSine (by norm_num) hβ)]
  have hb := norm_integral_le_of_norm_le hm (show ∀ᵐ x ∂volume.restrict (Ioi (1:ℝ)),
      ‖x^(-β)*Real.sin (anchoredLogPhase 1 t v x)-x^(-β)*Real.sin (anchoredLogPhase 1 u v x)‖
        ≤ |t-u| *(x^(-β)*Real.log x) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0:ℝ) < x := zero_lt_one.trans hx
    have hp := Real.rpow_nonneg hx0.le (-β)
    have hl := Real.log_nonneg hx.le
    have hphase : anchoredLogPhase 1 t v x-anchoredLogPhase 1 u v x = (t-u)*Real.log x := by
      simp only [anchoredLogPhase,Real.log_one,sub_zero]
      ring
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hp]
    calc
      _ ≤ x^(-β)*|anchoredLogPhase 1 t v x-anchoredLogPhase 1 u v x| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) hp
      _ = _ := by rw [hphase,abs_mul,abs_of_nonneg hl]; ring)
  rw [integral_const_mul] at hb
  have hi := RHTower.integral_rpow_mul_log_Ioi_one (show 0 < β-1 by linarith)
  simp only [he] at hi
  rw [hi,Real.norm_eq_abs] at hb
  simpa only [div_eq_mul_inv,one_mul] using hb

/-- Dilation carries the power amplitude, phase, and Jacobian together. -/
theorem anchoredLogSine_integral_dilation {a : ℝ} (ha : 0 < a) (β t v : ℝ) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a t v x)) =
      a^(1-β)*anchoredSineProfile β t (v*a) := by
  have hscale := integral_comp_mul_left_Ioi
    (fun x => x^(-β)*Real.sin (anchoredLogPhase a t v x)) 1 ha
  simp only [mul_one, smul_eq_mul] at hscale
  have he : (∫ x in Ioi (1:ℝ), (a*x)^(-β)*Real.sin (anchoredLogPhase a t v (a*x))) =
      a^(-β)*anchoredSineProfile β t (v*a) := by
    rw [anchoredSineProfile, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0:ℝ) < x := zero_lt_one.trans hx
    have hp : anchoredLogPhase a t v (a*x)=anchoredLogPhase 1 t (v*a) x := by
      simp only [anchoredLogPhase, Real.log_mul ha.ne' hx0.ne',Real.log_one]
      ring
    dsimp only
    rw [Real.mul_rpow ha.le hx0.le,hp]
    ring
  rw [he] at hscale
  have hp : a*a^(-β)=a^(1-β) := by
    rw [show 1-β=1+(-β) by ring,Real.rpow_add ha,Real.rpow_one]
  calc
    _ = a*(a^(-β)*anchoredSineProfile β t (v*a)) := by rw [hscale]; field_simp
    _ = _ := by rw [← hp]; ring

/-- The normalized literal atom has no residual anchor amplitude in these coordinates. -/
theorem scaledBernoulliFourierAtom_im_eq_profile {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    (scaledBernoulliFourierAtom s N k).im =
      bernoulliModeWeight k*anchoredSineProfile (s.re+2) s.im (2*Real.pi*k*N) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [scaledBernoulliFourierAtom_im_eq hs hN, anchoredLogSine_integral_dilation hNp]
  have hp : (N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2))=1 := by
    rw [← Real.rpow_add hNp, show s.re+1+(1-(s.re+2))=0 by ring,Real.rpow_zero]
  calc
    _ = ((N:ℝ)^(s.re+1)*(N:ℝ)^(1-(s.re+2)))*
        (bernoulliModeWeight k*anchoredSineProfile (s.re+2) s.im (2*Real.pi*k*N)) := by ring
    _ = _ := by rw [hp,one_mul]

/-- Equal real parts give a height Lipschitz bound independent of integer anchor and frequency phase. -/
theorem scaledBernoulliFourierAtom_im_height_lipschitz {s z : ℂ} (hs : 0 < s.re)
    (hre : z.re=s.re) {N : ℕ} (hN : 1 ≤ N) (k : ℤ) :
    |(scaledBernoulliFourierAtom s N k).im-(scaledBernoulliFourierAtom z N k).im| ≤
      bernoulliModeWeight k*|s.im-z.im|/(s.re+1)^2 := by
  have hz : 0 < z.re := by rwa [hre]
  rw [scaledBernoulliFourierAtom_im_eq_profile hs hN,
    scaledBernoulliFourierAtom_im_eq_profile hz hN,hre,←mul_sub,abs_mul,
    abs_of_nonneg (bernoulliModeWeight_nonneg k)]
  have h := mul_le_mul_of_nonneg_left
    (anchoredSineProfile_height_lipschitz (show 1 < s.re+2 by linarith) s.im z.im (2*Real.pi*k*N))
    (bernoulliModeWeight_nonneg k)
  simpa only [show s.re+2-1=s.re+1 by ring, mul_div_assoc] using h

/-- The stationary-endpoint reserve is determined by a positive integral of the actual source. -/
def stationaryHeightReserve (β v : ℝ) : ℝ :=
  (β-1)^2*anchoredSineProfile β (-v) v/2

/-- The reserve is strictly positive, independently of zeta zeros. -/
theorem stationaryHeightReserve_pos {β v : ℝ} (hβ : 2 < β) (hv : 0 < v) :
    0 < stationaryHeightReserve β v := by
  have he : 0 < anchoredSineProfile β (-v) v := by
    simpa only [anchoredSineProfile,mul_one] using integral_endpoint_logSine_pos (by norm_num : (0:ℝ)<1) hβ hv
  unfold stationaryHeightReserve
  exact div_pos (mul_pos (sq_pos_of_pos (by linarith)) he) (by norm_num)

/-- The reserve has an exact positive compensated-density representation. -/
theorem stationaryHeightReserve_eq_positive_budget {β v : ℝ} (hβ : 2 < β) (hv : 0 < v) :
    stationaryHeightReserve β v = (β-1)^2/2 *
      ∫ x in Ioi (1:ℝ), reciprocalLogDissipation β (-v) v x *
        (1-Real.cos (anchoredLogPhase 1 (-v) v x)) := by
  have he := integral_endpoint_logSine_eq_budget (by norm_num : (0:ℝ)<1) hβ hv
  simp only [mul_one] at he
  rw [stationaryHeightReserve,anchoredSineProfile,he]
  ring

/-- Reversing both phase coefficients reverses the actual profile. -/
theorem anchoredSineProfile_neg_phase (β t v : ℝ) :
    anchoredSineProfile β (-t) (-v) = -anchoredSineProfile β t v := by
  have he (x : ℝ) : anchoredLogPhase 1 (-t) (-v) x = -anchoredLogPhase 1 t v x := by
    unfold anchoredLogPhase
    ring
  simp only [anchoredSineProfile,he,Real.sin_neg,mul_neg,integral_neg]

/-- A perturbation across the stationary boundary spends at most half its negative endpoint mass. -/
theorem anchoredSineProfile_le_neg_half_endpoint {β v t : ℝ} (hβ : 2 < β)
    (hlo : v ≤ t) (hhi : t ≤ v+stationaryHeightReserve β v) :
    anchoredSineProfile β t (-v) ≤ -anchoredSineProfile β (-v) v/2 := by
  have h := (le_abs_self _).trans
    (anchoredSineProfile_height_lipschitz (show 1 < β by linarith) t v (-v))
  have he : anchoredSineProfile β v (-v) = -anchoredSineProfile β (-v) v := by
    simpa only [neg_neg] using anchoredSineProfile_neg_phase β (-v) v
  rw [he, abs_of_nonneg (sub_nonneg.mpr hlo)] at h
  have hd : 0 < (β-1)^2 := sq_pos_of_pos (by linarith)
  have hb : (t-v)/(β-1)^2 ≤ anchoredSineProfile β (-v) v/2 := by
    apply (div_le_iff₀ hd).mpr
    unfold stationaryHeightReserve at hhi
    nlinarith
  linarith

/-- The literal negative-frequency atom retains a strict negative margin throughout its height reserve. -/
theorem scaledBernoulliFourierAtom_neg_im_le_reserve_margin {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) (k : ℤ)
    (hlo : 2*Real.pi*k*N ≤ s.im)
    (hhi : s.im ≤ 2*Real.pi*k*N+stationaryHeightReserve (s.re+2) (2*Real.pi*k*N)) :
    (scaledBernoulliFourierAtom s N (-k)).im ≤
      -bernoulliModeWeight (-k)*anchoredSineProfile (s.re+2) (-(2*Real.pi*k*N)) (2*Real.pi*k*N)/2 := by
  rw [scaledBernoulliFourierAtom_im_eq_profile hs hN]
  have he : 2*Real.pi*((-k:ℤ):ℝ)*N = -(2*Real.pi*k*N) := by push_cast; ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (anchoredSineProfile_le_neg_half_endpoint (by linarith : 2 < s.re+2) hlo hhi)
    (bernoulliModeWeight_nonneg (-k))
  convert! hb using 1
  ring

/-- The strict negative source region extends beyond each stationary-frequency threshold. -/
theorem scaledBernoulliFourierAtom_neg_im_neg_of_height_reserve {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k)
    (hhi : s.im ≤ 2*Real.pi*k*N+stationaryHeightReserve (s.re+2) (2*Real.pi*k*N)) :
    (scaledBernoulliFourierAtom s N (-k)).im < 0 := by
  by_cases hlo : s.im ≤ 2*Real.pi*k*N
  · exact scaledBernoulliFourierAtom_neg_im_neg_of_le hs hN hk hlo
  have hb := scaledBernoulliFourierAtom_neg_im_le_reserve_margin hs hN k (not_le.mp hlo).le hhi
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hv : 0 < 2*Real.pi*(k:ℝ)*N := by positivity
  have he : 0 < anchoredSineProfile (s.re+2) (-(2*Real.pi*k*N)) (2*Real.pi*k*N) := by
    simpa only [anchoredSineProfile,mul_one] using
      integral_endpoint_logSine_pos (by norm_num : (0:ℝ)<1) (by linarith : 2 < s.re+2) hv
  have hw := bernoulliModeWeight_pos (neg_ne_zero.mpr hk.ne')
  have hn : -bernoulliModeWeight (-k)*anchoredSineProfile (s.re+2)
      (-(2*Real.pi*k*N)) (2*Real.pi*k*N)/2 < 0 := by nlinarith [mul_pos hw he]
  exact hb.trans_lt hn

/-- Stationary modes whose heights exceed their positive endpoint reserves. -/
def stationaryBeyondReserveIndices (s : ℂ) (N : ℕ) : Finset ℤ :=
  (stationaryFourierIndices s.im N).filter fun k =>
    2*Real.pi*(-k)*N+stationaryHeightReserve (s.re+2) (2*Real.pi*(-k)*N) < s.im

/-- Actual contribution of the reduced stationary sector. -/
def stationaryBeyondReserveBudget (s : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ stationaryBeyondReserveIndices s N, (scaledBernoulliFourierAtom s N k).im

/-- Guaranteed negative mass carried by the removed stationary modes. -/
def stationaryReserveMass (s : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ (stationaryFourierIndices s.im N).filter (fun (k : ℤ) =>
    s.im ≤ 2*Real.pi*(-k)*N+stationaryHeightReserve (s.re+2) (2*Real.pi*(-k)*N)),
    bernoulliModeWeight k*anchoredSineProfile (s.re+2) (-(2*Real.pi*(-k)*N)) (2*Real.pi*(-k)*N)/2

/-- Every removed stationary mode pays its independently proved endpoint margin. -/
theorem stationary_atom_le_neg_reserve_margin {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : k ∈ stationaryFourierIndices s.im N)
    (hr : s.im ≤ 2*Real.pi*(-k)*N+stationaryHeightReserve (s.re+2) (2*Real.pi*(-k)*N)) :
    (scaledBernoulliFourierAtom s N k).im ≤
      -(bernoulliModeWeight k*anchoredSineProfile (s.re+2)
        (-(2*Real.pi*(-k)*N)) (2*Real.pi*(-k)*N)/2) := by
  obtain ⟨hk0,hkt⟩ := (mem_stationaryFourierIndices hN).mp hk
  have hc : 2*Real.pi*((-k:ℤ):ℝ)*N = 2*Real.pi*(-(k:ℝ))*N := by push_cast; rfl
  have h := scaledBernoulliFourierAtom_neg_im_le_reserve_margin hs hN (-k)
    (by simpa only [hc] using hkt) (by simpa only [hc] using hr)
  simpa only [hc, neg_neg, neg_mul, neg_div] using h

/-- The removed mass is nonnegative and uses only the actual source. -/
theorem stationaryReserveMass_nonneg {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ stationaryReserveMass s N := by
  unfold stationaryReserveMass
  apply Finset.sum_nonneg
  intro k hk
  have hk0 := ((mem_stationaryFourierIndices hN).mp (Finset.mem_filter.mp hk).1).1
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hkR : (k:ℝ) < 0 := by exact_mod_cast hk0
  have hkneg : 0 < -(k:ℝ) := neg_pos.mpr hkR
  have hv : 0 < 2*Real.pi*(-(k:ℝ))*N := by positivity
  have he : 0 < anchoredSineProfile (s.re+2) (-(2*Real.pi*(-k)*N)) (2*Real.pi*(-k)*N) := by
    simpa only [anchoredSineProfile,mul_one] using
      integral_endpoint_logSine_pos (by norm_num : (0:ℝ)<1) (by linarith : 2 < s.re+2) hv
  exact div_nonneg (mul_nonneg (bernoulliModeWeight_nonneg k) he.le) (by norm_num)

/-- The reduced stationary envelope retains the certified negative mass of removed modes. -/
theorem stationaryFourierBudget_le_beyondReserve_sub_mass {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    stationaryFourierBudget s N ≤ stationaryBeyondReserveBudget s N-stationaryReserveMass s N := by
  classical
  unfold stationaryFourierBudget stationaryBeyondReserveBudget stationaryBeyondReserveIndices stationaryReserveMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hr : s.im ≤ 2*Real.pi*(-k)*N+stationaryHeightReserve (s.re+2) (2*Real.pi*(-k)*N)
  · simp only [hr, not_lt.mpr hr,if_false,if_true,zero_sub]
    exact stationary_atom_le_neg_reserve_margin hs hN hk hr
  · simp only [hr,not_le.mp hr,if_true,if_false,sub_zero,le_refl]

/-- Full source comparison retains the reduced head, removed negative margins, both infinite sectors, and mean. -/
theorem normalizedWeightedRemainder_scaled_im_le_beyondReserve {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im ≤
      stationaryBeyondReserveBudget s N-stationaryReserveMass s N+
      1/(12*(2*Real.pi*N+s.im))-s.im/(12*Complex.normSq (s+1)) := by
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_budget hs hs1 ht hN
  have hr := stationaryFourierBudget_le_beyondReserve_sub_mass hs hN
  linarith

/-- In the proved strip, the source is strictly below the reduced head minus its removed mass. -/
theorem normalizedWeightedRemainder_scaled_im_lt_beyondReserve {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im <
      stationaryBeyondReserveBudget s N-stationaryReserveMass s N := by
  exact (normalizedWeightedRemainder_scaled_im_lt_stationary_budget hs hs' ht hN).trans_le
    (stationaryFourierBudget_le_beyondReserve_sub_mass hs hN)

/-- Exhausting the reduced head is sufficient for a strict sign of the complete actual remainder. -/
theorem normalizedWeightedRemainder_im_neg_of_beyondReserve_empty {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hempty : stationaryBeyondReserveIndices s N = ∅) :
    (normalizedWeightedRemainder s N).im < 0 := by
  have hb := normalizedWeightedRemainder_scaled_im_lt_beyondReserve hs hs' ht hN
  have hm := stationaryReserveMass_nonneg hs hN
  rw [stationaryBeyondReserveBudget,hempty,Finset.sum_empty] at hb
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp := Real.rpow_pos_of_pos hNp (2*s.re+1)
  nlinarith

/-- The zero-forced lower bound increases by the removed negative mass. -/
theorem stationaryBeyondReserveBudget_lowerBound_at_zero {s : ℂ} (hs : 0 < s.re)
    (hs' : s.re < 1) (ht : 0 ≤ s.im) (hz : riemannZeta s = 0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      s.im/(12*Complex.normSq (s+1))-1/(12*(2*Real.pi+s.im))+
      stationaryReserveMass s 1 ≤ stationaryBeyondReserveBudget s 1 := by
  have h := stationaryFourierBudget_lowerBound_at_zero hs hs' ht hz
  have hr := stationaryFourierBudget_le_beyondReserve_sub_mass hs (by rfl : 1 ≤ (1:ℕ))
  linarith

/-- Closed-right zeros require the reduced actual head to exceed all the removed mass. -/
theorem stationaryReserveMass_lt_beyondReserveBudget_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    stationaryReserveMass s 1 < stationaryBeyondReserveBudget s 1 := by
  have h := stationaryFourierBudget_pos_at_closed_right_zero hs hs' ht hz
  have hr := stationaryFourierBudget_le_beyondReserve_sub_mass (by linarith : 0 < s.re)
    (by rfl : 1 ≤ (1:ℕ))
  linarith

/-- Every closed-right zero forces a positive first harmonic beyond its positive endpoint reserve. -/
theorem exists_positive_first_harmonic_beyond_height_reserve_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    ∃ N : ℕ, 1 ≤ N ∧
      2*Real.pi*N+stationaryHeightReserve (s.re+2) (2*Real.pi*N) < s.im ∧
      0 < (scaledBernoulliFourierAtom s N (-1)).im := by
  obtain ⟨N,hN,_,hpos⟩ := exists_positive_first_harmonic_strict_interior_at_closed_right_zero hs hs' ht hz
  refine ⟨N,hN,?_,hpos⟩
  by_contra hn
  have h := scaledBernoulliFourierAtom_neg_im_neg_of_height_reserve (by linarith : 0 < s.re)
    hN (by norm_num : (0:ℤ)<1) (by simpa only [Int.cast_one,mul_one] using not_lt.mp hn)
  linarith

/-- The full power mass bounds the magnitude of every profile. -/
theorem anchoredSineProfile_abs_le_mass {β : ℝ} (hβ : 1 < β) (t v : ℝ) :
    |anchoredSineProfile β t v| ≤ 1/(β-1) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) (by norm_num : (0:ℝ)<1)
  have hb := norm_integral_le_of_norm_le hi (show ∀ᵐ x ∂volume.restrict (Ioi (1:ℝ)),
      ‖x^(-β)*Real.sin (anchoredLogPhase 1 t v x)‖ ≤ x^(-β) by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (-β)
    rw [Real.norm_eq_abs, abs_mul,abs_of_nonneg hp]
    exact mul_le_of_le_one_right hp (Real.abs_sin_le_one _))
  have he := RHTower.integral_rpow_neg_Ioi (show 0 < β-1 by linarith) 1 (by norm_num)
  simp only [show -(β-1)-1 = -β by ring,Real.one_rpow] at he
  rw [he,Real.norm_eq_abs] at hb
  exact hb

/-- The source-defined collar has a uniform finite upper width. -/
theorem stationaryHeightReserve_le {β : ℝ} (hβ : 1 < β) (v : ℝ) :
    stationaryHeightReserve β v ≤ (β-1)/2 := by
  have hb := (le_abs_self _).trans (anchoredSineProfile_abs_le_mass hβ (-v) v)
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (β-1))
  have he : (β-1)^2*(1/(β-1)) = β-1 := by field_simp
  rw [he] at hm
  unfold stationaryHeightReserve
  linarith

/-- The first height reserve ends before the second frequency threshold throughout the strip. -/
theorem first_stationary_height_reserve_lt_next_frequency {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    2*Real.pi*N+stationaryHeightReserve (s.re+2) (2*Real.pi*N) < 2*(2*Real.pi*N) := by
  have hr := stationaryHeightReserve_le (by linarith : 1 < s.re+2) (2*Real.pi*N)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hv : 1 < 2*Real.pi*N := by nlinarith [Real.pi_gt_three]
  linarith

/-- At the extended first threshold no unestimated stationary mode remains. -/
theorem stationaryBeyondReserveIndices_eq_empty_of_first_reserve {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    (ht : s.im ≤ 2*Real.pi*N+stationaryHeightReserve (s.re+2) (2*Real.pi*N)) :
    stationaryBeyondReserveIndices s N = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hk,hb⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk0,hkt⟩ := (mem_stationaryFourierIndices hN).mp hk
  have hnext := ht.trans_lt (first_stationary_height_reserve_lt_next_frequency hs hs' hN)
  have hk1 : k = -1 := by
    by_contra hn
    have hk2 : (2:ℝ) ≤ -(k:ℝ) := by exact_mod_cast (show (2:ℤ) ≤ -k by omega)
    have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hv : 0 < 2*Real.pi*N := by positivity
    have hm := mul_le_mul_of_nonneg_left hk2 hv.le
    nlinarith
  rw [hk1] at hb
  simp only [Int.cast_neg,Int.cast_one,neg_neg,mul_one] at hb
  exact (not_lt.mpr ht) hb

/-- The complete literal remainder has strict negative phase beyond the old first threshold,
up to its strictly positive source-defined height reserve. -/
theorem normalizedWeightedRemainder_im_neg_of_first_height_reserve {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hcut : s.im ≤ 2*Real.pi*N+stationaryHeightReserve (s.re+2) (2*Real.pi*N)) :
    (normalizedWeightedRemainder s N).im < 0 := by
  exact normalizedWeightedRemainder_im_neg_of_beyondReserve_empty hs hs' ht hN
    (stationaryBeyondReserveIndices_eq_empty_of_first_reserve hs hs' hN hcut)

/-- The extended unit cutoff excludes every closed-right strip zero in its source-defined chamber. -/
theorem riemannZeta_ne_zero_of_first_height_reserve {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im)
    (hcut : s.im ≤ 2*Real.pi+stationaryHeightReserve (s.re+2) (2*Real.pi)) :
    riemannZeta s ≠ 0 := by
  intro hz
  have h := stationaryReserveMass_lt_beyondReserveBudget_at_closed_right_zero hs hs' ht hz
  have hm := stationaryReserveMass_nonneg (by linarith : 0 < s.re) (by rfl : 1 ≤ (1:ℕ))
  have he := stationaryBeyondReserveIndices_eq_empty_of_first_reserve (by linarith : 0 < s.re)
    hs'.le (by rfl : 1 ≤ (1:ℕ)) (by simpa only [Nat.cast_one,mul_one] using hcut)
  rw [stationaryBeyondReserveBudget,he,Finset.sum_empty] at h
  linarith

end RHTower.DeletionMixedRefinement
