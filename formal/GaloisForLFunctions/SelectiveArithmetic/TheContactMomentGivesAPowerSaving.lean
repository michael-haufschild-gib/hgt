import GaloisForLFunctions.SelectiveArithmetic.TheContactPolynomialHasFewLargeHeights
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheBadHeightsOfTheLocalSignHaveGaussianTails

/-!
# Power savings for exceptional contact heights

Taking the moment order `⌊log T/log N⌋` keeps the polynomial length below `T`.
The full mean-value error costs only `9T(1+log T)`, and the factorial moment
bound gives the explicit saving `T^(log θ/log N)`.
-/

open Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open ArithmeticCastelnuovoSeveri BiScaleUncertainty ArithmeticCriticalityTheory

private theorem large_contact_subset_prime {N : ℕ} (hN : 1 ≤ N) (V : ℝ) :
    {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ⊆
      {t | V ≤ ‖_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)‖} := by
  intro t ht
  have he := abs_contactPoly_sub_prime_re_le hN t
  have hre := Complex.abs_re_le_norm
    (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
      (_root_.RHTower.displacedLinePt 0 t))
  have htri := abs_add_le
    (contactPoly N t - (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
      (_root_.RHTower.displacedLinePt 0 t)).re)
    (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
      (_root_.RHTower.displacedLinePt 0 t)).re
  rw [sub_add_cancel] at htri
  change V + _ ≤ _ at ht
  change V ≤ _
  linarith only [ht, he, hre, htri]

/-- A moment of any order whose polynomial length is at most `T` saves `θ^k`. -/
theorem measureReal_contactPoly_le_theta_pow {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {T V θ : ℝ} (hV : 0 < V) (_hθ : 0 ≤ θ) (hlen : ((N ^ k : ℕ) : ℝ) ≤ T)
    (hvar : k * (Real.log N * (Real.log N + Real.log 4 + 4)) ≤ θ * V ^ 2) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ≤
      9 * (T * (1 + Real.log T)) * θ ^ k := by
  have hprime : ∀ n, primeContactCoeff N n ≠ 0 → n.Prime := by
    intro n hn
    by_contra hp
    exact hn (by simp [primeContactCoeff, hp])
  have hsupport : ∀ n, primeContactCoeff N n ≠ 0 → n ≤ N := by
    intro n hn
    by_contra hnN
    exact hn (by simp [primeContactCoeff, hnN])
  let E : ℝ → ℂ := fun t => _root_.RHTower.edPoly (primeContactCoeff N)
    (Finset.Icc 1 N) (_root_.RHTower.displacedLinePt 0 t)
  let W : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖primeContactCoeff N n‖ ^ 2 / (n : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg fun n _ => by positivity
  have hY : (1 : ℝ) ≤ (N ^ k : ℕ) := by exact_mod_cast Nat.one_le_pow k N hN
  have hT : 1 ≤ T := hY.trans hlen
  have hTT : T ≤ 2 * T := by linarith only [hT]
  have hc : Continuous E := _root_.RHTower.WeilConeMoments.continuous_edPoly_displaced _ N 0
  have hi : Integrable (fun t => ‖E t ^ k‖ ^ 2) (volume.restrict (Ioc T (2 * T))) :=
    (((hc.pow k).norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T (2 * T)))
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖E t ^ k‖) hi (V ^ (2 * k))
  have hset : {t | V ≤ ‖E t‖} = {t | V ^ (2 * k) ≤ ‖E t ^ k‖ ^ 2} := by
    ext t
    simp only [mem_setOf_eq, norm_pow, ← pow_mul, mul_comm k 2]
    constructor
    · exact fun h => pow_le_pow_left₀ hV.le h _
    · intro h
      by_contra hn
      have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) (norm_nonneg (E t))
        (show 2 * k ≠ 0 by omega)
      exact (not_lt_of_ge h) hh
  rw [← hset] at hmk
  have hmom := _root_.RHTower.integral_norm_edPoly_pow_displaced_le
    hprime hsupport 0 k T (2 * T) hTT
  rw [intervalIntegral.integral_of_le hTT] at hmom
  have hmom' : (∫ t in Ioc T (2 * T), ‖E t ^ k‖ ^ 2) ≤
      (T + 8 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ))) *
        ((k.factorial : ℝ) * W ^ k) := by
    simpa only [E, W, mul_zero, zero_sub, Real.rpow_neg_one, ← div_eq_mul_inv,
      two_mul, add_sub_cancel_left] using hmom
  have hlogY : 0 ≤ Real.log (N ^ k : ℕ) := Real.log_nonneg hY
  have hlogYT : Real.log (N ^ k : ℕ) ≤ Real.log T :=
    Real.log_le_log (zero_lt_one.trans_le hY) hlen
  have hwin : T + 8 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ)) ≤
      9 * (T * (1 + Real.log T)) := by
    have hm := mul_le_mul hlen (add_le_add_left hlogYT 1)
      (by linarith only [hlogY]) (zero_le_one.trans hT)
    have htlog := mul_nonneg (zero_le_one.trans hT) (Real.log_nonneg hT)
    nlinarith only [hm, htlog]
  have hkW : (k : ℝ) * W ≤ θ * V ^ 2 :=
    (mul_le_mul_of_nonneg_left (primeContactEnergy_le hN) (Nat.cast_nonneg k)).trans hvar
  have hfac : (k.factorial : ℝ) * W ^ k ≤ θ ^ k * V ^ (2 * k) := by
    calc
      _ ≤ (k : ℝ) ^ k * W ^ k := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow k)
          (pow_nonneg hW k)
      _ = ((k : ℝ) * W) ^ k := (mul_pow _ _ _).symm
      _ ≤ (θ * V ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hkW k
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hp : 0 < V ^ (2 * k) := pow_pos hV _
  refine (measureReal_mono (large_contact_subset_prime hN V)).trans ?_
  apply le_of_mul_le_mul_right _ hp
  calc
    _ ≤ (T + 8 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ))) *
        ((k.factorial : ℝ) * W ^ k) := by
      have hm : (volume.restrict (Ioc T (2 * T))).real {t | V ≤ ‖E t‖} *
          V ^ (2 * k) ≤ ∫ t in Ioc T (2 * T), ‖E t ^ k‖ ^ 2 := by
        simpa only [mul_comm] using hmk
      exact hm.trans hmom'
    _ ≤ (9 * (T * (1 + Real.log T))) * (θ ^ k * V ^ (2 * k)) :=
      mul_le_mul hwin hfac (by positivity)
        (mul_nonneg (by norm_num) (mul_nonneg (zero_le_one.trans hT)
          (by linarith only [Real.log_nonneg hT])))
    _ = _ := by ring

/-- A logarithmic cutoff `L≥log N` permits moment order `⌊log T/L⌋`. -/
theorem measureReal_contactPoly_power_saving_of_log_cutoff {N : ℕ} (hN : 1 ≤ N)
    {T V θ L : ℝ} (hT0 : 0 < T) (hL : 0 < L) (hNL : Real.log N ≤ L)
    (hLT : L ≤ Real.log T) (hV : 0 < V) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hvar : Real.log T * (L + Real.log 4 + 4) ≤ θ * V ^ 2) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ≤
      9 * (T * (1 + Real.log T)) * (θ⁻¹ * T ^ (Real.log θ / L)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  let q := Real.log T / L
  let k := ⌊q⌋₊
  have hq : 1 ≤ q := (le_div_iff₀ hL).mpr (by simpa only [one_mul] using hLT)
  have hk : 1 ≤ k := (Nat.le_floor_iff (zero_le_one.trans hq)).mpr (by simpa using hq)
  have hkq : (k : ℝ) ≤ q := Nat.floor_le (zero_le_one.trans hq)
  have hqk : q < k + 1 := Nat.lt_floor_add_one q
  have hlen : ((N ^ k : ℕ) : ℝ) ≤ T := by
    rw [Nat.cast_pow, ← Real.log_le_log_iff (by positivity) hT0, Real.log_pow]
    exact (mul_le_mul_of_nonneg_left hNL (Nat.cast_nonneg k)).trans
      ((le_div_iff₀ hL).mp hkq)
  have hW : 0 ≤ L * (L + Real.log 4 + 4) := by positivity
  have hkW : k * (Real.log N * (Real.log N + Real.log 4 + 4)) ≤ θ * V ^ 2 := by
    calc
      _ ≤ (k : ℝ) * (L * (L + Real.log 4 + 4)) := by gcongr
      _ ≤ q * (L * (L + Real.log 4 + 4)) := mul_le_mul_of_nonneg_right hkq hW
      _ = Real.log T * (L + Real.log 4 + 4) := by dsimp [q]; field_simp
      _ ≤ _ := hvar
  have hpow : θ ^ k ≤ θ⁻¹ * T ^ (Real.log θ / L) := by
    rw [← Real.rpow_natCast]
    calc
      θ ^ (k : ℝ) ≤ θ ^ (q - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by linarith only [hqk])
      _ = _ := by
        rw [Real.rpow_sub hθ, Real.rpow_one, Real.rpow_def_of_pos hθ,
          Real.rpow_def_of_pos hT0, div_eq_inv_mul]
        congr 2
        dsimp [q]
        ring
  have hfront : 0 ≤ 9 * (T * (1 + Real.log T)) := by
    have htlog : 0 ≤ Real.log T := hL.le.trans hLT
    positivity
  exact (measureReal_contactPoly_le_theta_pow hN hk hV hθ.le hlen hkW).trans
    (mul_le_mul_of_nonneg_left hpow hfront)

/-- Choosing the exact cutoff `log N` gives the finite-scale power-saving formula. -/
theorem measureReal_contactPoly_power_saving {N : ℕ} (hN : 2 ≤ N) {T V θ : ℝ}
    (hNT : (N : ℝ) ≤ T) (hV : 0 < V) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hvar : Real.log T * (Real.log N + Real.log 4 + 4) ≤ θ * V ^ 2) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ≤
      9 * (T * (1 + Real.log T)) * (θ⁻¹ * T ^ (Real.log θ / Real.log N)) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  exact measureReal_contactPoly_power_saving_of_log_cutoff (by omega)
    (hN0.trans_le hNT) (Real.log_pos hN1) le_rfl (Real.log_le_log hN0 hNT)
    hV hθ hθ1 hvar

private theorem tendsto_log_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun u : ℝ => Real.log (a * u + b) / u) atTop (𝓝 0) := by
  have haff : Tendsto (fun u : ℝ => a * u + b) atTop atTop := by
    refine tendsto_atTop.2 fun r => ?_
    filter_upwards [eventually_ge_atTop ((r - b) / a)] with u hu
    have hm := (div_le_iff₀ ha).mp hu
    linarith only [hm]
  have hlog : Tendsto (fun u : ℝ => Real.log (a * u + b) / (a * u + b))
      atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp haff
  have hb : Tendsto (fun u : ℝ => b / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hrat : Tendsto (fun u : ℝ => a + b / u) atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add hb
  have h := hlog.mul hrat
  simp only [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), haff.eventually_gt_atTop 0] with u hu hau
  field_simp

/-- The variance-to-threshold ratio on rung `κ`, with `u=log T`. -/
def rungMomentRatio (κ v u : ℝ) : ℝ :=
  (2 * κ * Real.log u + Real.log 4 + 4) / (v ^ 2 * u)

theorem tendsto_rungMomentRatio_zero (κ : ℝ) {v : ℝ} (hv : 0 < v) :
    Tendsto (rungMomentRatio κ v) atTop (𝓝 0) := by
  have hl : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hc : Tendsto (fun u : ℝ => (Real.log 4 + 4) / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((hl.const_mul (2 * κ)).add hc).div_const (v ^ 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  unfold rungMomentRatio
  field_simp
  ring

/-- On a fixed rung, the logarithm of the moment ratio is asymptotic to `−log u`. -/
theorem tendsto_log_rungMomentRatio_div_log {κ v : ℝ} (hκ : 0 < κ) (hv : 0 < v) :
    Tendsto (fun u : ℝ => Real.log (rungMomentRatio κ v u) / Real.log u)
      atTop (𝓝 (-1)) := by
  have hn : Tendsto (fun u : ℝ =>
      Real.log (2 * κ * Real.log u + (Real.log 4 + 4)) / Real.log u) atTop (𝓝 0) :=
    (tendsto_log_affine_div (mul_pos two_pos hκ) (Real.log 4 + 4)).comp
      Real.tendsto_log_atTop
  have hc : Tendsto (fun u : ℝ => Real.log (v ^ 2) / Real.log u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := (hn.sub hc).sub (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num only [sub_zero, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hnum : 0 < 2 * κ * Real.log u + Real.log 4 + 4 := by positivity
  rw [rungMomentRatio, Real.log_div hnum.ne' (by positivity),
    Real.log_mul (by positivity : v ^ 2 ≠ 0) hu0.ne']
  field_simp
  ring

/-- The exceptional-height saving has limiting exponent `−1/(2κ)`. -/
theorem tendsto_rungMomentSavingExponent {κ v : ℝ} (hκ : 0 < κ) (hv : 0 < v) :
    Tendsto (fun u : ℝ => Real.log (rungMomentRatio κ v u) / (2 * κ * Real.log u))
      atTop (𝓝 (-(1 / (2 * κ)))) := by
  have h := (tendsto_log_rungMomentRatio_div_log hκ hv).div_const (2 * κ)
  simpa only [div_div, mul_comm (Real.log _) (2 * κ), neg_div] using h

private theorem eventually_rungMomentEnvelope_le {κ v ε : ℝ}
    (hκ : 0 < κ) (hv : 0 < v) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop,
      9 * (Real.exp u * (1 + u)) *
        ((rungMomentRatio κ v u)⁻¹ *
          Real.exp (u * (Real.log (rungMomentRatio κ v u) / (2 * κ * Real.log u)))) ≤
      Real.exp ((1 - 1 / (2 * κ) + ε) * u) := by
  have hl : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hr : Tendsto (fun u => Real.log (rungMomentRatio κ v u) / u) atTop (𝓝 0) := by
    have h := (tendsto_log_rungMomentRatio_div_log hκ hv).mul hl
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hlu : Real.log u ≠ 0 := (Real.log_pos hu).ne'
    field_simp
  have h9 : Tendsto (fun u : ℝ => Real.log 9 / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun u : ℝ => Real.log (1 + u) / u) atTop (𝓝 0) := by
    simpa only [one_mul, add_comm] using tendsto_log_affine_div zero_lt_one 1
  have hsum := (((h9.add (tendsto_const_nhds (x := (1 : ℝ)))).add h1).sub hr).add
    (tendsto_rungMomentSavingExponent hκ hv)
  simp only [zero_add, add_zero, sub_zero, ← sub_eq_add_neg] at hsum
  have he := hsum.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with u hu hu1
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hθ : 0 < rungMomentRatio κ v u := by
    unfold rungMomentRatio
    have hlu := Real.log_pos hu1
    positivity
  have hlarge := (mul_lt_mul_of_pos_right hu hu0).le
  have harg : Real.log 9 + u + Real.log (1 + u) - Real.log (rungMomentRatio κ v u) +
      u * (Real.log (rungMomentRatio κ v u) / (2 * κ * Real.log u)) ≤
      (1 - 1 / (2 * κ) + ε) * u := by
    convert hlarge using 1 <;> first | rfl | (field_simp [hu0.ne'] <;> ring)
  refine le_of_eq_of_le ?_ (Real.exp_le_exp.mpr harg)
  rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_add,
    Real.exp_log (by norm_num : (0 : ℝ) < 9),
    Real.exp_log (by positivity : 0 < 1 + u), Real.exp_log hθ]
  ring

/-- On rung `κ`, contact values above `c log T` occupy at most
`T^(1−1/(2κ)+ε)` for every positive `ε`, eventually. -/
theorem eventually_measureReal_contactPoly_rung_le_rpow {κ c ε : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      (volume.restrict (Ioc T (2 * T))).real
        {t | c * Real.log T ≤
          |contactPoly ⌊Real.exp (2 * κ * Real.log (Real.log T))⌋₊ t|} ≤
        T ^ (1 - 1 / (2 * κ) + ε) := by
  let v := c / 2
  have hv : 0 < v := half_pos hc
  have hl : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcut : Tendsto (fun u : ℝ => (2 * κ * Real.log u) / u) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hl.const_mul (2 * κ)
  have hconst : Tendsto (fun u : ℝ => (4 * Real.log 4 + 16) / u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have htail : Tendsto (fun u : ℝ =>
      (4 * κ * Real.log u + 4 * Real.log 4 + 16) / u) atTop (𝓝 0) := by
    have h := (hl.const_mul (4 * κ)).add hconst
    simpa only [mul_zero, zero_add, ← mul_div_assoc, ← add_div, add_assoc] using h
  have huBound : ∀ᶠ u : ℝ in atTop,
      (volume.restrict (Ioc (Real.exp u) (2 * Real.exp u))).real
        {t | c * u ≤ |contactPoly ⌊Real.exp (2 * κ * Real.log u)⌋₊ t|} ≤
        Real.exp ((1 - 1 / (2 * κ) + ε) * u) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hcut.eventually (gt_mem_nhds zero_lt_one),
      (tendsto_rungMomentRatio_zero κ hv).eventually (gt_mem_nhds zero_lt_one),
      htail.eventually (gt_mem_nhds hv),
      eventually_rungMomentEnvelope_le hκ hv hε] with u hu hcut hθ1 htail henv
    let L := 2 * κ * Real.log u
    let N := ⌊Real.exp L⌋₊
    let θ := rungMomentRatio κ v u
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hL : 0 < L := by dsimp [L]; exact mul_pos (mul_pos two_pos hκ) (Real.log_pos hu)
    have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos L).le).mpr
      (by simpa only [Nat.cast_one] using Real.one_le_exp hL.le)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hNL : Real.log N ≤ L := by
      simpa only [Real.log_exp] using Real.log_le_log hN0 (Nat.floor_le (Real.exp_pos L).le)
    have hLu : L ≤ u := ((div_lt_one hu0).mp hcut).le
    have hθ : 0 < θ := by
      dsimp [θ, rungMomentRatio]
      have hlu := Real.log_pos hu
      positivity
    have hV : 0 < v * u := mul_pos hv hu0
    have hvar : Real.log (Real.exp u) * (L + Real.log 4 + 4) ≤ θ * (v * u) ^ 2 := by
      apply le_of_eq
      dsimp [θ, rungMomentRatio, L]
      rw [Real.log_exp]
      field_simp
    have hpow := measureReal_contactPoly_power_saving_of_log_cutoff hN (Real.exp_pos u)
      hL hNL (by simpa only [Real.log_exp] using hLu) hV hθ hθ1.le hvar
    have hH : 2 * Real.log N + 4 * Real.log 4 + 16 ≤ v * u := by
      have ht := (div_lt_iff₀ hu0).mp htail
      dsimp [L] at hNL
      linarith only [ht, hNL]
    have hsub : {t | c * u ≤ |contactPoly N t|} ⊆
        {t | v * u + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} := by
      intro t ht
      change c * u ≤ _ at ht
      change v * u + _ ≤ _
      dsimp [v] at *
      linarith only [ht, hH]
    refine (measureReal_mono hsub).trans (hpow.trans ?_)
    simpa only [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos u)] using henv
  filter_upwards [Real.tendsto_log_atTop.eventually huBound,
    eventually_gt_atTop (0 : ℝ)] with T hT hT0
  calc
    _ ≤ Real.exp ((1 - 1 / (2 * κ) + ε) * Real.log T) := by
      simpa only [Real.exp_log hT0] using hT
    _ = _ := by
      rw [Real.rpow_def_of_pos hT0]
      congr 1
      ring

/-- The uniform sign estimate only needs the actual polynomial length `N^k≤T`;
the moment order has no further restriction. -/
theorem exists_boundedShape_sign_of_moment_length {N k : ℕ} {T δ M A : ℝ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (hT : 0 < T) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hM : 1 ≤ M) (hA : 0 < A) (hAeq : A = δ / (64 * M ^ 2) * Real.log T)
    (hAbig : 1 + fieldConstant + 2 ≤ A)
    (hLC : 8 * (10 + Real.log 4) + 8 ≤ Real.log T) (hAT : A ≤ Real.log T / 64)
    (hNA : Real.exp (2 * A) ≤ N) (hlogN : Real.log N ≤ 2 * A + 1)
    (hNk : (N : ℝ) ^ k ≤ T) :
    ∃ B : Set ℝ, volume B ≤ ENNReal.ofReal (209 * T * (4 * k * δ ^ 2) ^ k) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ,
        ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, A < |u| → F₀ u = 0) →
        shapeNorm A F₀ ^ 2 ≤ M ^ 2 * A * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hM0 : M ≠ 0 := by linarith only [hM]
  have hC : 0 < 10 + Real.log 4 := by positivity
  have hL : 0 < Real.log T := by linarith only [hLC, hC]
  have hfc := fieldConstant_pos
  obtain ⟨B, hB, hgood⟩ := exists_bad_heights_moment hN hk hT hδ hδ4 hA
  refine ⟨B, hB.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have hm := mul_le_mul_of_nonneg_right
      (show T + 208 * (N : ℝ) ^ k ≤ 209 * T by linarith only [hNk])
      (show 0 ≤ (k : ℝ) ^ k * (4 * δ ^ 2) ^ k by positivity)
    have he : (k : ℝ) ^ k * (4 * δ ^ 2) ^ k = (4 * k * δ ^ 2) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    simpa only [he] using hm
  · intro γ hγ hγB F₀ hF₀ hF₀c hsupp hshape hpos
    have hbase := hgood γ hγ hγB A hA.le hNA F₀ hF₀ hF₀c hsupp
    have hγT : T ≤ γ := hγ.1
    have hγ0 : 0 < γ := hT.trans_le hγT
    have hlogγ : Real.log T ≤ Real.log (2 + |γ|) := by
      rw [abs_of_pos hγ0]
      exact Real.log_le_log hT (by linarith only [hγT])
    have hfield := field_term_le hδ hM0 hL hA
      (show Real.log N + fieldConstant ≤ 3 * A by linarith only [hlogN, hAbig]) hAeq hshape
    have hexpA : Real.exp A ≤ T := by
      have hh := Real.exp_le_exp.mpr (show A ≤ Real.log T by linarith only [hAT, hL])
      rwa [Real.exp_log hT] at hh
    have hT2 : 2 ≤ T := by
      have hh := Real.exp_le_exp.mpr (show (1 : ℝ) ≤ Real.log T by linarith only [hLC, hC])
      rw [Real.exp_log hT] at hh
      have he := Real.add_one_le_exp (1 : ℝ)
      linarith only [hh, he]
    have hpole := pole_term_le hT2 hγT hexpA (envelopeWindowNorm_nonneg F₀)
      (envelopeWindowNorm_le_shapeNorm (show 1 ≤ A by linarith only [hAbig, hfc]) F₀)
    have hshape' : shapeNorm A F₀ ^ 2 ≤ 1 / 64 * Real.log T * ∫ u, F₀ u ^ 2 := by
      refine hshape.trans ?_
      rw [hAeq, shape_scale_eq hM0]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by linarith only [hδ4]) hL.le) hpos.le
    have hmain : (Real.log T / 2 - (10 + Real.log 4)) * (∫ u, F₀ u ^ 2) ≤
        (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * ∫ u, F₀ u ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hlogγ]) hpos.le
    exact closing_inequality hpos hLC hC hfield (hpole.trans hshape')
      (by linarith only [hbase, hmain])

/-- Every slightly larger rung parameter gives its full moment saving uniformly
over all packets of bounded shape at aperture `κ log log T`. -/
theorem eventually_boundedShape_rung_exceptions {κ κ' M ε : ℝ}
    (hκ : 0 < κ) (hκ' : κ < κ') (hM : 1 ≤ M) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (T ^ (1 - 1 / (2 * κ') + ε)) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ,
        ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, κ * Real.log (Real.log T) < |u| → F₀ u = 0) →
        shapeNorm (κ * Real.log (Real.log T)) F₀ ^ 2 ≤
          M ^ 2 * (κ * Real.log (Real.log T)) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hκ'0 : 0 < κ' := hκ.trans hκ'
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  let v := κ' / (64 * M ^ 2 * κ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hl : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcut := hl.const_mul (2 * κ')
  have hδlim := hl.const_mul (64 * M ^ 2 * κ)
  have hAlim := hl.const_mul κ
  simp only [mul_zero] at hcut hδlim hAlim
  have hAbig : Tendsto (fun u : ℝ => κ * Real.log u) atTop atTop :=
    Tendsto.const_mul_atTop hκ Real.tendsto_log_atTop
  have huBound : ∀ᶠ u : ℝ in atTop, ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (Real.exp ((1 - 1 / (2 * κ') + ε) * u)) ∧
      ∀ γ ∈ Icc (Real.exp u) (2 * Real.exp u), γ ∉ B → ∀ F₀ : ℝ → ℝ,
        ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ t : ℝ, κ * Real.log u < |t| → F₀ t = 0) →
        shapeNorm (κ * Real.log u) F₀ ^ 2 ≤ M ^ 2 * (κ * Real.log u) * (∫ t, F₀ t ^ 2) →
        0 < ∫ t, F₀ t ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
    filter_upwards [eventually_ge_atTop (24 : ℝ),
      eventually_ge_atTop (8 * (10 + Real.log 4) + 8),
      hcut.eventually (gt_mem_nhds zero_lt_one),
      hδlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      hAlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
      hAbig.eventually_ge_atTop (1 + fieldConstant + 2),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 / (2 * (κ' - κ))),
      (tendsto_rungMomentRatio_zero κ' hv).eventually (gt_mem_nhds zero_lt_one),
      eventually_rungMomentEnvelope_le hκ'0 hv hε] with u hu24 huLC huL huδ huA huAbig hugap huθ henv
    have hu : 1 < u := by linarith only [hu24]
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hlu : 0 < Real.log u := Real.log_pos hu
    let A := κ * Real.log u
    let L := 2 * κ' * Real.log u
    let δ := 64 * M ^ 2 * A / u
    let θ := rungMomentRatio κ' v u
    let q := u / L
    let k := ⌊q⌋₊
    have hA : 0 < A := mul_pos hκ hlu
    have hL : 0 < L := mul_pos (mul_pos two_pos hκ'0) hlu
    have hLu : L ≤ u := by
      have hh : L / u < 1 := by simpa only [L, mul_div_assoc] using huL
      exact ((div_lt_one hu0).mp hh).le
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ4 : δ ≤ 1 / 4 := by
      change 64 * M ^ 2 * (κ * Real.log u) / u ≤ 1 / 4
      simpa only [mul_div_assoc, mul_assoc] using huδ.le
    have hAT : A ≤ u / 64 := by
      have hh : A / u < 1 / 64 := by simpa only [A, mul_div_assoc] using huA
      have hh' := (div_lt_iff₀ hu0).mp hh
      linarith only [hh']
    have hAL : 2 * A + 1 ≤ L := by
      have hg := (div_le_iff₀ (mul_pos two_pos (sub_pos.mpr hκ'))).mp hugap
      dsimp [A, L]
      nlinarith only [hg]
    have hAeq : A = δ / (64 * M ^ 2) * Real.log (Real.exp u) := by
      dsimp [δ]
      rw [Real.log_exp]
      field_simp
    obtain ⟨N, hN, hNA, _, hlogN⟩ := exists_polynomial_length hA.le (Real.exp_pos u)
      (by simpa only [Real.log_exp] using hAL.trans hLu)
    have hq : 1 ≤ q := (le_div_iff₀ hL).mpr (by simpa only [one_mul] using hLu)
    have hk : 1 ≤ k := (Nat.le_floor_iff (zero_le_one.trans hq)).mpr (by simpa using hq)
    have hkq : (k : ℝ) ≤ q := Nat.floor_le (zero_le_one.trans hq)
    have hqk : q < k + 1 := Nat.lt_floor_add_one q
    have hNk : (N : ℝ) ^ k ≤ Real.exp u := by
      rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos u), Real.log_pow, Real.log_exp]
      exact (mul_le_mul_of_nonneg_left (hlogN.trans hAL) (Nat.cast_nonneg k)).trans
        ((le_div_iff₀ hL).mp hkq)
    obtain ⟨B, hB, hgood⟩ := exists_boundedShape_sign_of_moment_length hN hk (Real.exp_pos u)
      hδ hδ4 hM hA hAeq huAbig (by simpa only [Real.log_exp] using huLC)
      (by simpa only [Real.log_exp] using hAT) hNA hlogN hNk
    have hθ : 0 < θ := by dsimp [θ, rungMomentRatio]; positivity
    have hbase : 4 * (k : ℝ) * δ ^ 2 ≤ θ := by
      have hm := mul_le_mul_of_nonneg_right hkq (show 0 ≤ 4 * δ ^ 2 by positivity)
      have he : q * (4 * δ ^ 2) = (2 * κ' * Real.log u) / (v ^ 2 * u) := by
        dsimp [q, L, δ, A, v]
        field_simp
        ring
      have hb : (2 * κ' * Real.log u) / (v ^ 2 * u) ≤ θ := by
        dsimp [θ, rungMomentRatio]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
        linarith only [h4]
      rw [he] at hm
      nlinarith only [hm, hb]
    have hpow : θ ^ k ≤ θ⁻¹ * Real.exp (u * (Real.log θ / L)) := by
      rw [← Real.rpow_natCast]
      calc
        θ ^ (k : ℝ) ≤ θ ^ (q - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hθ huθ.le (by linarith only [hqk])
        _ = _ := by
          rw [Real.rpow_sub hθ, Real.rpow_one, Real.rpow_def_of_pos hθ, div_eq_inv_mul]
          congr 2
          dsimp [q]
          ring
    refine ⟨B, hB.trans (ENNReal.ofReal_le_ofReal ?_), hgood⟩
    calc
      _ ≤ 209 * Real.exp u * θ ^ k := by gcongr
      _ ≤ 209 * Real.exp u * (θ⁻¹ * Real.exp (u * (Real.log θ / L))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 9 * (Real.exp u * (1 + u)) * (θ⁻¹ * Real.exp (u * (Real.log θ / L))) := by
        have hf := mul_le_mul_of_nonneg_right
          (show (209 : ℝ) ≤ 9 * (1 + u) by linarith only [hu24]) (Real.exp_pos u).le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith only [hf]
      _ ≤ _ := henv
  filter_upwards [Real.tendsto_log_atTop.eventually huBound,
    eventually_gt_atTop (0 : ℝ)] with T hT hT0
  obtain ⟨B, hB, hgood⟩ := hT
  refine ⟨B, ?_, ?_⟩
  · convert hB using 1
    rw [Real.rpow_def_of_pos hT0]
    congr 2
    ring
  · simpa only [Real.exp_log hT0] using hgood

/-- Uniform bounded-shape positivity on rung `κ` fails on at most
`T^(1−1/(2κ)+ε)` heights, for every positive `ε`, eventually. -/
theorem eventually_boundedShape_rung_exceptions_sharp {κ M ε : ℝ}
    (hκ : 0 < κ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (T ^ (1 - 1 / (2 * κ) + ε)) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ,
        ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, κ * Real.log (Real.log T) < |u| → F₀ u = 0) →
        shapeNorm (κ * Real.log (Real.log T)) F₀ ^ 2 ≤
          M ^ 2 * (κ * Real.log (Real.log T)) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  let κ' := κ + ε * κ ^ 2
  have hκ' : κ < κ' := lt_add_of_pos_right κ (mul_pos hε (sq_pos_of_pos hκ))
  have hκ'0 : 0 < κ' := hκ.trans hκ'
  have hdiff : 1 / (2 * κ) - 1 / (2 * κ') = (κ' - κ) / (2 * κ * κ') := by
    field_simp
  have hbound : (κ' - κ) / (2 * κ * κ') ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * κ * κ')).mpr
    have hm := mul_le_mul_of_nonneg_left hκ'.le (mul_nonneg hε.le hκ.le)
    have he : κ' - κ = ε * κ ^ 2 := by dsimp [κ']; ring
    rw [he]
    nlinarith only [hm]
  have hexp : 1 - 1 / (2 * κ') + ε / 2 ≤ 1 - 1 / (2 * κ) + ε := by
    rw [← hdiff] at hbound
    linarith only [hbound]
  filter_upwards [eventually_boundedShape_rung_exceptions hκ hκ' hM (half_pos hε),
    eventually_ge_atTop (1 : ℝ)] with T hT hT1
  obtain ⟨B, hB, hgood⟩ := hT
  exact ⟨B, hB.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hT1 hexp)), hgood⟩

end GaloisForLFunctions.SelectiveArithmetic
