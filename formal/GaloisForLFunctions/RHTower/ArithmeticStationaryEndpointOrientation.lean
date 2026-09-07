import GaloisForLFunctions.RHTower.ArithmeticStationaryFourierDilation

/-!
# Signed orientation at the stationary Fourier endpoint

At `gamma = -omega*a`, the phase derivative vanishes at the anchor and the
reciprocal phase weight has a pole. The actual `1-cos` factor compensates this
pole. Explicit product bounds prove integrability and zero boundary limits for
`beta > 2`, yielding a strictly positive anchored sine integral.

For the literal Bernoulli source, `beta = Re(s)+2`. Thus negative-frequency
atoms have strictly negative imaginary part also when `Im(s) = 2*pi*k*N`.
The normalized-remainder sign includes the endpoint `Im(s) <= 2*pi*N` in the
previous strip and height range. Every positive first-harmonic witness forced
by a closed-right zero lies strictly inside the stationary carrier. The
independent interior-head comparison and RH remain open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Logarithmic concavity bounds the boundary-stationary clock between zero and its linear part. -/
theorem endpoint_phase_bounds {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : a ≤ x) :
    0 ≤ anchoredLogPhase a (-ω*a) ω x ∧
      anchoredLogPhase a (-ω*a) ω x ≤ ω*(x-a) := by
  have hx0 := ha.trans_le hx
  have hl0 : 0 ≤ Real.log x-Real.log a := sub_nonneg.mpr (Real.log_le_log ha hx)
  have hl := Real.log_le_sub_one_of_pos (div_pos hx0 ha)
  rw [Real.log_div hx0.ne' ha.ne'] at hl
  have he : a*(x/a-1) = x-a := by field_simp
  have hla := mul_le_mul_of_nonneg_left hl ha.le
  rw [he] at hla
  have hlaω := mul_le_mul_of_nonneg_left hla hω.le
  have hup := mul_nonneg (mul_pos hω ha).le hl0
  unfold anchoredLogPhase
  constructor <;> nlinarith

/-- The trigonometric factor vanishes at least quadratically in distance from the anchor. -/
theorem endpoint_cos_budget_le {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) (hx : a ≤ x) :
    1-Real.cos (anchoredLogPhase a (-ω*a) ω x) ≤ (ω*(x-a))^2/2 := by
  obtain ⟨h0,h1⟩ := endpoint_phase_bounds ha hω hx
  have hc := Real.one_sub_sq_div_two_le_cos (x := anchoredLogPhase a (-ω*a) ω x)
  nlinarith [sq_nonneg (ω*(x-a)-anchoredLogPhase a (-ω*a) ω x)]

/-- The reciprocal-weight dissipation is strictly positive beyond a stationary endpoint. -/
theorem endpoint_dissipation_pos {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) : 0 < reciprocalLogDissipation β (-ω*a) ω x := by
  have hx0 := ha.trans hx
  have hd : 0 < ω*x+(-ω*a) := by nlinarith
  have hβ1 : 0 < β-1 := by linarith
  unfold reciprocalLogDissipation
  positivity

/-- The power identity used in the compensated endpoint estimates. -/
theorem endpoint_power_identity {β x : ℝ} (hx : 0 < x) :
    x^(-β)*x = x^(1-β) := by
  rw [show 1-β = -β+1 by ring, Real.rpow_add hx, Real.rpow_one]

/-- The actual boundary product cancels the reciprocal-weight pole. -/
theorem endpoint_boundary_bounds {a β ω x : ℝ} (ha : 0 < a) (hω : 0 < ω)
    (hx : a < x) :
    0 ≤ reciprocalLogWeight β (-ω*a) ω x * (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ∧
    reciprocalLogWeight β (-ω*a) ω x * (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ≤
      ω/2*x^(1-β)*(x-a) := by
  have hx0 := ha.trans hx
  have hd : 0 < ω*x+(-ω*a) := by nlinarith
  have hw : 0 ≤ reciprocalLogWeight β (-ω*a) ω x := by
    unfold reciprocalLogWeight
    positivity
  refine ⟨mul_nonneg hw (sub_nonneg.mpr (Real.cos_le_one _)), ?_⟩
  calc
    _ ≤ reciprocalLogWeight β (-ω*a) ω x * ((ω*(x-a))^2/2) :=
      mul_le_mul_of_nonneg_left (endpoint_cos_budget_le ha hω hx.le) hw
    _ = _ := by
      unfold reciprocalLogWeight
      rw [show ω*x+(-ω*a)=ω*(x-a) by ring]
      field_simp [hω.ne', sub_ne_zero.mpr hx.ne']

/-- The compensated positive density has an explicit integrable power majorant when beta exceeds two. -/
theorem endpoint_budget_bounds {a β ω x : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) (hx : a < x) :
    0 ≤ reciprocalLogDissipation β (-ω*a) ω x * (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ∧
    reciprocalLogDissipation β (-ω*a) ω x * (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) ≤
      β*ω/2*x^(1-β) := by
  have hx0 := ha.trans hx
  have hd : 0 < ω*x+(-ω*a) := by nlinarith
  have hw := (endpoint_dissipation_pos ha hβ hω hx).le
  refine ⟨mul_nonneg hw (sub_nonneg.mpr (Real.cos_le_one _)), ?_⟩
  calc
    _ ≤ reciprocalLogDissipation β (-ω*a) ω x * ((ω*(x-a))^2/2) :=
      mul_le_mul_of_nonneg_left (endpoint_cos_budget_le ha hω hx.le) hw
    _ = x^(-β)*((β-1)*(ω*x+(-ω*a))+ω*x)/2 := by
      unfold reciprocalLogDissipation
      rw [show ω*x+(-ω*a)=ω*(x-a) by ring]
      field_simp [hω.ne', sub_ne_zero.mpr hx.ne']
    _ ≤ β*ω/2*x^(1-β) := by
      rw [← endpoint_power_identity hx0]
      have hp : 0 ≤ x^(-β) := Real.rpow_nonneg hx0.le _
      have hβ1 : 0 < β-1 := by linarith
      have ht : 0 ≤ (β-1)*ω*a := by positivity
      nlinarith [mul_nonneg hp ht]

/-- The compensated density is continuous on the open positive half-line. -/
theorem continuousOn_endpoint_budget {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ContinuousOn (fun x => reciprocalLogDissipation β (-ω*a) ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (Ioi a) := by
  apply ContinuousOn.mul ?_
    (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn (continuousOn_anchoredLogPhase ha)))
  intro x hx
  have hx0 := ha.trans hx
  have hd : ω*x+(-ω*a) ≠ 0 := ne_of_gt (by have hxa : a < x := hx; nlinarith)
  unfold reciprocalLogDissipation
  have hp := (Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx0.ne')).continuousAt
  exact (hp.mul ((continuousAt_const.mul
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const)).add
    (continuousAt_const.mul continuousAt_id))).div
    (((continuousAt_const.mul continuousAt_id).add continuousAt_const).pow 2)
    (pow_ne_zero _ hd) |>.continuousWithinAt

/-- The compensated positive density is absolutely integrable despite its singular factors. -/
theorem integrable_endpoint_budget {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β) (hω : 0 < ω) :
    IntegrableOn (fun x => reciprocalLogDissipation β (-ω*a) ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (Ioi a) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : 1-β < -1) ha).const_mul (β*ω/2)).mono'
    ((continuousOn_endpoint_budget ha hω).aestronglyMeasurable measurableSet_Ioi)
  rw [ae_restrict_iff' measurableSet_Ioi]
  apply ae_of_all
  intro x hx
  obtain ⟨h0,h1⟩ := endpoint_budget_bounds ha hβ hω hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1

/-- The actual integration-by-parts boundary product tends to zero at the stationary anchor. -/
theorem tendsto_endpoint_boundary_at_anchor {a β ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    Tendsto (fun x => reciprocalLogWeight β (-ω*a) ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) (𝓝[>] a) (𝓝 0) := by
  have hc : ContinuousAt (fun x : ℝ => ω/2*x^(1-β)*(x-a)) a :=
    (((Real.hasDerivAt_rpow_const (p := 1-β) (Or.inl ha.ne')).continuousAt).const_mul (ω/2)).mul
      (continuousAt_id.sub_const a)
  have hl : Tendsto (fun x : ℝ => ω/2*x^(1-β)*(x-a)) (𝓝[>] a) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact (endpoint_boundary_bounds ha hω hx).1
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact (endpoint_boundary_bounds ha hω hx).2

/-- The actual boundary product also tends to zero at infinity. -/
theorem tendsto_endpoint_boundary_atTop {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    Tendsto (fun x => reciprocalLogWeight β (-ω*a) ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x))) atTop (𝓝 0) := by
  have hl := (tendsto_rpow_neg_atTop (by linarith : 0 < β-2)).const_mul (ω/2)
  rw [show -(β-2)=2-β by ring, mul_zero] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_gt_atTop a] with x hx
    exact (endpoint_boundary_bounds ha hω hx).1
  · filter_upwards [eventually_gt_atTop a] with x hx
    have hx0 := ha.trans hx
    calc
      _ ≤ ω/2*x^(1-β)*(x-a) := (endpoint_boundary_bounds ha hω hx).2
      _ ≤ ω/2*x^(1-β)*x := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ω/2*x^(2-β) := by
        have hp : x^(1-β)*x = x^(2-β) := by
          calc
            _ = x^(1-β)*x^(1:ℝ) := by rw [Real.rpow_one]
            _ = x^((1-β)+1) := (Real.rpow_add hx0 _ _).symm
            _ = _ := by congr 1; ring
        rw [mul_assoc, hp]

/-- The exact positive-budget identity extends through the stationary endpoint. -/
theorem integral_endpoint_logSine_eq_budget {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a (-ω*a) ω x)) =
      ∫ x in Ioi a, reciprocalLogDissipation β (-ω*a) ω x *
        (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) := by
  have hd (x : ℝ) (hx : x ∈ Ioi a) : ω*x+(-ω*a) ≠ 0 := ne_of_gt (by have hxa : a < x := hx; nlinarith)
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => 1-Real.cos (anchoredLogPhase a (-ω*a) ω x))
        ((ω+(-ω*a)/x)*Real.sin (anchoredLogPhase a (-ω*a) ω x)) x := by
    convert! ((hasDerivAt_anchoredLogPhase (ha.trans hx)).cos).const_sub 1 using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      reciprocalLogWeight β (-ω*a) ω x * ((ω+(-ω*a)/x)*Real.sin (anchoredLogPhase a (-ω*a) ω x)) =
      x^(-β)*Real.sin (anchoredLogPhase a (-ω*a) ω x) := by
    rw [← mul_assoc, reciprocalLogWeight_mul_phase_deriv (ha.trans hx) (hd x hx)]
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_reciprocalLogWeight (ha.trans hx) (hd x hx)) hv
    ((integrable_anchoredLogSine ha (by linarith : 1 < β)).congr_fun
      (fun x hx => (he x hx).symm) measurableSet_Ioi)
    ((integrable_endpoint_budget ha hβ hω).neg.congr_fun (fun x _ => by simp) measurableSet_Ioi)
    (tendsto_endpoint_boundary_at_anchor ha hω) (tendsto_endpoint_boundary_atTop ha hβ hω)
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul, integral_neg, sub_self, zero_sub, neg_neg] using hi

/-- Strict phase motion beyond the anchor prevents the sine from vanishing identically. -/
theorem exists_endpoint_sine_ne_zero {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    ∃ x ∈ Ioi a, Real.sin (anchoredLogPhase a (-ω*a) ω x) ≠ 0 := by
  let b := a+1
  have hb : a < b := by dsimp [b]; linarith
  have hb0 := ha.trans hb
  by_cases hs : Real.sin (anchoredLogPhase a (-ω*a) ω b) ≠ 0
  · exact ⟨b,hb,hs⟩
  · have hsz : Real.sin (anchoredLogPhase a (-ω*a) ω b) = 0 := not_ne_iff.mp hs
    have hc : Real.cos (anchoredLogPhase a (-ω*a) ω b) ≠ 0 := by
      intro hc0
      have hi := Real.sin_sq_add_cos_sq (anchoredLogPhase a (-ω*a) ω b)
      rw [hsz,hc0] at hi
      norm_num at hi
    have hd : 0 < ω+(-ω*a)/b := by
      have he : ω+(-ω*a)/b = (ω*b-ω*a)/b := by field_simp; ring
      rw [he]
      exact div_pos (by nlinarith) hb0
    have hne := ((hasDerivAt_anchoredLogPhase (a := a) (γ := -ω*a) (ω := ω) hb0).sin).eventually_ne
      (c := 0) (mul_ne_zero hc hd.ne')
    have hf : 𝓝[>] b ≤ 𝓝[≠] b := nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
    obtain ⟨x,hx,hns⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] b, x ∈ Ioi b).and
      (hne.filter_mono hf)).exists
    exact ⟨x,lt_trans hb hx,hns⟩

/-- The literal anchored sine integral is strictly positive at the stationary endpoint. -/
theorem integral_endpoint_logSine_pos {a β ω : ℝ} (ha : 0 < a) (hβ : 2 < β)
    (hω : 0 < ω) :
    0 < ∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a (-ω*a) ω x) := by
  rw [integral_endpoint_logSine_eq_budget ha hβ hω]
  have hn : ∀ᵐ x ∂volume.restrict (Ioi a), 0 ≤ reciprocalLogDissipation β (-ω*a) ω x *
      (1-Real.cos (anchoredLogPhase a (-ω*a) ω x)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun x hx => (endpoint_budget_bounds ha hβ hω hx).1)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (integrable_endpoint_budget ha hβ hω)]
  have ho := (continuousOn_endpoint_budget (β := β) ha hω).isOpen_inter_preimage isOpen_Ioi
    (isClosed_singleton (x := (0:ℝ))).isOpen_compl
  rw [Set.inter_comm] at ho
  apply ho.measure_pos volume
  obtain ⟨x,hx,hsx⟩ := exists_endpoint_sine_ne_zero ha hω
  have hc : Real.cos (anchoredLogPhase a (-ω*a) ω x) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro he
    have hs := Real.sin_sq_add_cos_sq (anchoredLogPhase a (-ω*a) ω x)
    rw [he] at hs
    have hz : Real.sin (anchoredLogPhase a (-ω*a) ω x) = 0 := by
      nlinarith [sq_nonneg (Real.sin (anchoredLogPhase a (-ω*a) ω x))]
    exact hsx hz
  exact ⟨x,(mul_pos (endpoint_dissipation_pos ha hβ hω hx) (sub_pos.mpr hc)).ne',hx⟩

/-- Strict sine orientation holds with a nonnegative initial phase speed. -/
theorem integral_anchoredLogSine_pos_of_den_nonneg {a β γ ω : ℝ} (ha : 0 < a)
    (hβ : 2 < β) (hω : 0 < ω) (hd : 0 ≤ ω*a+γ) :
    0 < ∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x) := by
  rcases eq_or_lt_of_le hd with he | hl
  · have hγ : γ = -ω*a := by linarith
    rw [hγ]
    exact integral_endpoint_logSine_pos ha hβ hω
  · exact integral_anchoredLogSine_pos ha (by linarith) hω hl

/-- The opposite negative frequency has strict negative orientation, including zero initial speed. -/
theorem anchoredLogSine_neg_frequency_of_den_nonneg {a β γ ω : ℝ} (ha : 0 < a)
    (hβ : 2 < β) (hω : 0 < ω) (hd : 0 ≤ ω*a-γ) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ (-ω) x)) < 0 := by
  have he (x : ℝ) : anchoredLogPhase a γ (-ω) x = -anchoredLogPhase a (-γ) ω x := by
    unfold anchoredLogPhase
    ring
  simp_rw [he, Real.sin_neg, mul_neg, integral_neg]
  exact neg_neg_of_pos (integral_anchoredLogSine_pos_of_den_nonneg ha hβ hω (by simpa using hd))

/-- The literal scaled negative-frequency atom has negative imaginary part at and above its frequency threshold. -/
theorem scaledBernoulliFourierAtom_neg_im_neg_of_le {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) {k : ℤ} (hk : 0 < k) (ht : s.im ≤ 2*Real.pi*k*N) :
    (scaledBernoulliFourierAtom s N (-k)).im < 0 := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [scaledBernoulliFourierAtom_im_eq hs hN]
  apply mul_neg_of_pos_of_neg (mul_pos (Real.rpow_pos_of_pos hNp _)
    (bernoulliModeWeight_pos (neg_ne_zero.mpr hk.ne')))
  simp only [Int.cast_neg, mul_neg]
  exact anchoredLogSine_neg_frequency_of_den_nonneg hNp (by linarith) (by positivity) (sub_nonneg.mpr ht)

/-- At the first-frequency threshold the finite stationary budget is exactly the boundary atom. -/
theorem stationaryFourierBudget_eq_first_atom_at_threshold {s : ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ht : s.im = 2*Real.pi*N) :
    stationaryFourierBudget s N = (scaledBernoulliFourierAtom s N (-1)).im := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : s.im/(2*Real.pi*N)=1 := by rw [ht,div_self (by positivity)]
  simp [stationaryFourierBudget,stationaryFourierIndices,he]

/-- The complete source sign includes equality at the frequency cutoff in the proved strip and height range. -/
theorem normalizedWeightedRemainder_im_neg_of_le_frequency {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hsub : s.im ≤ 2*Real.pi*N) : (normalizedWeightedRemainder s N).im < 0 := by
  rcases lt_or_eq_of_le hsub with hl | he
  · exact normalizedWeightedRemainder_im_neg_of_subresonant hs hs' ht hN hl
  · have hb := normalizedWeightedRemainder_scaled_im_lt_stationary_budget hs hs' ht hN
    rw [stationaryFourierBudget_eq_first_atom_at_threshold hN he] at hb
    have hn := scaledBernoulliFourierAtom_neg_im_neg_of_le hs hN (by norm_num : (0:ℤ) < 1)
      (by simpa using hsub)
    have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    nlinarith [Real.rpow_pos_of_pos hNp (2*s.re+1)]

/-- Every closed-right strip zero of height at least one requires a positive first harmonic strictly inside the stationary carrier. -/
theorem exists_positive_first_harmonic_strict_interior_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ 2*Real.pi*N < s.im ∧
      0 < (scaledBernoulliFourierAtom s N (-1)).im := by
  obtain ⟨N,hN,hpos⟩ := exists_positive_first_harmonic_at_closed_right_zero hs hs' ht hz
  obtain ⟨hN1,hNk⟩ := Finset.mem_Icc.mp hN
  have hs0 : 0 < s.re := by linarith
  have hc : (N:ℝ) ≤ s.im/(2*Real.pi) := (Nat.le_floor_iff' (by omega : N ≠ 0)).mp hNk
  have hNt : 2*Real.pi*N ≤ s.im := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2*Real.pi by positivity)).mp hc
    nlinarith
  refine ⟨N,hN1,lt_of_le_of_ne hNt ?_,hpos⟩
  intro he
  have hn := scaledBernoulliFourierAtom_neg_im_neg_of_le hs0 hN1 (by norm_num : (0:ℤ) < 1)
    (by simpa using le_of_eq he.symm)
  linarith

end RHTower.DeletionMixedRefinement
