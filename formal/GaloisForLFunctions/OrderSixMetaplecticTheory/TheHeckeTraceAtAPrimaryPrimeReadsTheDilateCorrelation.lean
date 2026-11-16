import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsAPhasedSumOverHeckePoints

/-!
# The constant term of the Hecke trace at a primary prime

For the projected theta function `θ_s` (Fourier series `Σ_h b(v, h) e(ξ_hz)`), the Hecke points of
`(z, v)` are `(pz, |p|v)` and `((z + 3t)/p, v/|p|)`. Three tools compute the constant term of the Hecke trace:

* averaging over `O/p` (`sum_cuspCharacterSeries_low`):
  `Σ_{x ∈ O/p} S_c((z + 3x)/p) = N(p) S_{c(·p)}(z)`, since `x ↦ e(ξ_k·3x/p)` is the principal trace character of
  `O/p` at `k` (`tracePhase_low`), primitive, so its sum is `N(p)` or `0` as `p ∣ k` or not;
* products of cusp series are cusp series of the convolution (`cuspCharacterSeries_mul`);
* cross-Parseval for the dilate `S_a(pz)` (`integral_cuspCharacterSeries_mul_dilate`).

With `β_y` from the Bezout matrices (`pδ_y − 9yβ_y = 1`) the result is (`integral_sourceHeckeTrace`)

`∫_P Tr_pθ_s = N(p)|P| (2 Σ_h b(|p|v, h) b(v/|p|, −p²h) + Σ_{y≢0} (3y/p)₃ Σ_k b(v/|p|, k) e(−ξ_k·3β_y/p) b(v/|p|, −k))`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-! ### Products of cusp series -/

/-- The convolution `(c ⋆ d)(m) = Σ_k c(k) d(m − k)`. -/
def cuspConv (c d : O → ℂ) (m : O) : ℂ := ∑' k : O, c k * d (m - k)

/-- `(m, k) ↦ (k, m − k)`. -/
def convEquiv : O × O ≃ O × O where
  toFun q := (q.2, q.1 - q.2)
  invFun r := (r.1 + r.2, r.1)
  left_inv q := by simp
  right_inv r := by simp

theorem summable_conv_family {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖)) :
    Summable (fun q : O × O => ‖c q.2‖ * ‖d (q.1 - q.2)‖) := by
  have h := hc.mul_norm hd
  simp only [norm_mul] at h
  exact (convEquiv.summable_iff (f := fun r : O × O => ‖c r.1‖ * ‖d r.2‖)).mpr h

theorem summable_cuspConv {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖)) :
    Summable (fun m => ‖cuspConv c d m‖) := by
  have hF := summable_conv_family hc hd
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hF.prod
  have hs : Summable (fun k => ‖c k * d (m - k)‖) := by
    simpa only [norm_mul] using hF.prod_factor m
  calc ‖cuspConv c d m‖ ≤ ∑' k, ‖c k * d (m - k)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k, ‖c k‖ * ‖d (m - k)‖ := by simp only [norm_mul]

theorem cuspFrequency_add_sub (k m : O) : cuspFrequency k + cuspFrequency (m - k) = cuspFrequency m := by
  simp only [cuspFrequency, map_sub]
  ring

/-- **Products of cusp series.** `S_c S_d = S_{c ⋆ d}`. -/
theorem cuspCharacterSeries_mul {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (u : ℂ) : cuspCharacterSeries c u * cuspCharacterSeries d u = cuspCharacterSeries (cuspConv c d) u := by
  have hcs : Summable (fun k => ‖c k * tracePhase (cuspFrequency k * u)‖) := by
    simpa only [norm_mul, tracePhase_norm, mul_one] using hc
  have hds : Summable (fun k => ‖d k * tracePhase (cuspFrequency k * u)‖) := by
    simpa only [norm_mul, tracePhase_norm, mul_one] using hd
  have hF := summable_conv_family hc hd
  set G : O × O → ℂ := fun q => c q.2 * d (q.1 - q.2) * tracePhase (cuspFrequency q.1 * u) with hG
  have hGs : Summable G := by
    refine Summable.of_norm_bounded hF fun q => ?_
    simp only [hG, norm_mul, tracePhase_norm, mul_one, le_refl]
  unfold cuspCharacterSeries
  rw [tsum_mul_tsum_of_summable_norm hcs hds,
    ← convEquiv.tsum_eq (fun r : O × O => c r.1 * tracePhase (cuspFrequency r.1 * u) *
      (d r.2 * tracePhase (cuspFrequency r.2 * u)))]
  have hterm : ∀ q : O × O, c (convEquiv q).1 * tracePhase (cuspFrequency (convEquiv q).1 * u) *
      (d (convEquiv q).2 * tracePhase (cuspFrequency (convEquiv q).2 * u)) = G q := by
    intro q
    simp only [convEquiv, Equiv.coe_fn_mk, hG]
    rw [show c q.2 * tracePhase (cuspFrequency q.2 * u) * (d (q.1 - q.2) *
        tracePhase (cuspFrequency (q.1 - q.2) * u)) =
        c q.2 * d (q.1 - q.2) * (tracePhase (cuspFrequency q.2 * u) *
          tracePhase (cuspFrequency (q.1 - q.2) * u)) by ring, ← AddChar.map_add_eq_mul, ← add_mul,
      cuspFrequency_add_sub]
  simp_rw [hterm]
  rw [hGs.tsum_prod]
  refine tsum_congr fun m => ?_
  simp only [hG, cuspConv]
  rw [tsum_mul_right]

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Averaging over `O/p` -/

/-- `e(ξ_k·3x/p) = ψ_p(xk)`, the principal trace character modulo `p`. -/
theorem tracePhase_low (k x : O) :
    tracePhase (cuspFrequency k * (3 * ringComplex x / ringComplex P.p)) =
      principalTraceChar P.p P.ne_zero (P.res x * P.res k) := by
  have hP := P.ringComplex_ne_zero
  have hτ : ringComplex traceLambda ≠ 0 :=
    MetaplecticMobiusDescent.CubicEisenstein.ringComplex_ne_zero traceLambda_ne_zero
  rw [← map_mul, ← tracePhase_div_eq_principalTraceChar P.p (x * k) P.ne_zero]
  congr 1
  simp only [cuspFrequency, map_mul]
  field_simp

theorem sum_tracePhase_low (k : O) :
    ∑ x : P.Res, tracePhase (cuspFrequency k * (3 * ringComplex (P.lift x) / ringComplex P.p)) =
      if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0 := by
  simp_rw [P.tracePhase_low, res_lift]
  rw [AddChar.sum_mulShift _ (principalTraceChar_primitive P.p P.ne_zero)]
  by_cases hk : P.p ∣ k
  · rw [if_pos ((P.res_eq_zero_iff k).mpr hk), if_pos hk]
  · rw [if_neg (fun h => hk ((P.res_eq_zero_iff k).mp h)), if_neg hk]
    simp

/-- **Averaging over `O/p`.** `Σ_x S_c((z + 3x)/p) = N(p) S_{c(·p)}(z)`. -/
theorem sum_cuspCharacterSeries_low (c : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (z : ℂ) :
    ∑ x : P.Res, cuspCharacterSeries c ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
      (Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => c (m * P.p)) z := by
  have hP := P.ringComplex_ne_zero
  have hsum : ∀ x : P.Res, Summable (fun k => c k *
      tracePhase (cuspFrequency k * ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p))) := fun x =>
    Summable.of_norm (by simpa only [norm_mul, tracePhase_norm, mul_one] using hc)
  unfold cuspCharacterSeries
  rw [← Summable.tsum_finsetSum (fun x _ => hsum x)]
  have hpt : ∀ k, ∑ x : P.Res, c k *
      tracePhase (cuspFrequency k * ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p)) =
      c k * tracePhase (cuspFrequency k * (z / ringComplex P.p)) *
        (if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0) := by
    intro k
    rw [← P.sum_tracePhase_low k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_div, mul_add, AddChar.map_add_eq_mul]
    ring
  simp_rw [hpt]
  have hinj : Function.Injective (fun m : O => m * P.p) := fun a b h => mul_right_cancel₀ P.ne_zero h
  have hsupp : Function.support (fun k => c k * tracePhase (cuspFrequency k * (z / ringComplex P.p)) *
      (if P.p ∣ k then (Fintype.card P.Res : ℂ) else 0)) ⊆ Set.range (fun m : O => m * P.p) := by
    intro k hk
    by_contra hn
    apply hk
    have hk' : ¬ P.p ∣ k := fun ⟨m, hm⟩ => hn ⟨m, by rw [hm, mul_comm]⟩
    simp only [if_neg hk', mul_zero]
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [if_pos (dvd_mul_left _ _), cuspFrequency_mul_right,
    show cuspFrequency m * ringComplex P.p * (z / ringComplex P.p) = cuspFrequency m * z by field_simp]
  ring

end PrimaryPrime


namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The constant term for the projected theta function -/

/-- The Hecke trace at `p` of the projected theta function. -/
abbrev sourceHeckeTrace : HyperbolicSpace → ℂ := P.heckeTrace sourceTheta

theorem heckeHigh_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeHigh sourceTheta (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (‖ringComplex P.p‖ * v)) (ringComplex P.p * z) := by
  rw [heckeHigh, P.dilation_upperPoint, sourceTheta, cubicSourceResidualFunction_fourier_expansion]

theorem heckeLow_source (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeLow sourceTheta t (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖))
        ((z + 3 * ringComplex t) / ringComplex P.p) := by
  rw [heckeLow, transThree_smul_upperPoint, P.contraction_upperPoint, sourceTheta,
    cubicSourceResidualFunction_fourier_expansion]

/-- The coefficients of the low point shifted by `−3β/p`. -/
def shiftedLow (v : ℝ) (β : O) (k : O) : ℂ :=
  rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) k *
    tracePhase (cuspFrequency k * (-(3 * ringComplex β) / ringComplex P.p))

theorem summable_shiftedLow (v : ℝ) (hv : 0 < v) (β : O) : Summable (fun k => ‖P.shiftedLow v β k‖) := by
  simpa only [shiftedLow, norm_mul, tracePhase_norm, mul_one] using
    rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)

theorem integral_cuspCharacterSeries (g : O → ℂ) (hg : Summable (fun h => ‖g h‖)) :
    ∫ z in periodDomain, cuspCharacterSeries g z = periodArea * g 0 := by
  have h := cuspCharacterSeries_fourier g hg 0
  simp only [cuspFrequency, map_zero, zero_div, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [h]

/-- The trace at `(z, v)` as cusp series: two dilate terms and the phased low–low terms. -/
theorem sourceHeckeTrace_upperPoint (v : ℝ) (hv : 0 < v) (z : ℂ) :
    P.sourceHeckeTrace (upperPoint z v hv) =
      2 * (cuspCharacterSeries (rationalSourceModeAmplitude (‖ringComplex P.p‖ * v)) (ringComplex P.p * z) *
          ((Fintype.card P.Res : ℂ) *
            cuspCharacterSeries (fun m => rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (m * P.p)) z)) +
        ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
          ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1)))
            (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖)) (m * P.p)) z) := by
  rw [sourceHeckeTrace, P.heckeTrace_eq_hecke sourceTheta sourceTheta_automorphy]
  simp only [P.heckeHigh_source, P.heckeLow_source]
  set a := rationalSourceModeAmplitude (‖ringComplex P.p‖ * v)
  set b := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖)
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)
  have hii : ∑ x : P.Res, cuspCharacterSeries b ((z + 3 * ringComplex (P.wShift + P.lift x)) / ringComplex P.p) =
      (Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => b (m * P.p)) z := by
    have e : ∀ x : P.Res, z + 3 * ringComplex (P.wShift + P.lift x) =
        (z + 3 * ringComplex P.wShift) + 3 * ringComplex (P.lift x) := by
      intro x
      rw [map_add]
      ring
    simp_rw [e]
    rw [P.sum_cuspCharacterSeries_low b hb, cuspCharacterSeries_period]
  have hiii : ∀ y : {y : P.Res // y ≠ 0}, ∑ x : P.Res, ringComplex (symbol (3 * P.lift y.1) P.p) *
      cuspCharacterSeries b ((z + 3 * ringComplex (P.lift x - P.lowBeta (P.lift y.1))) / ringComplex P.p) *
        cuspCharacterSeries b ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
      ringComplex (symbol (3 * P.lift y.1) P.p) * ((Fintype.card P.Res : ℂ) *
        cuspCharacterSeries (fun m => cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1))) b (m * P.p)) z) := by
    intro y
    set β := P.lowBeta (P.lift y.1)
    have e : ∀ x : P.Res, cuspCharacterSeries b ((z + 3 * ringComplex (P.lift x - β)) / ringComplex P.p) *
        cuspCharacterSeries b ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
        cuspCharacterSeries (cuspConv (P.shiftedLow v β) b) ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) := by
      intro x
      rw [show (z + 3 * ringComplex (P.lift x - β)) / ringComplex P.p =
          (z + 3 * ringComplex (P.lift x)) / ringComplex P.p + (-(3 * ringComplex β) / ringComplex P.p) by
        rw [map_sub]; ring, cuspCharacterSeries_translate]
      change cuspCharacterSeries (P.shiftedLow v β) ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) *
        cuspCharacterSeries b ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) = _
      rw [cuspCharacterSeries_mul (P.summable_shiftedLow v hv β) hb]
    simp_rw [mul_assoc, e]
    rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low _ (summable_cuspConv (P.summable_shiftedLow v hv β) hb)]
  rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low b hb z, ← Finset.sum_mul, hii, Finset.sum_comm]
  simp_rw [hiii]
  ring

/-- **The constant term of the Hecke trace at `p`.** -/
theorem integral_sourceHeckeTrace (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceHeckeTrace (upperPoint z v hv) =
      (Fintype.card P.Res : ℂ) * periodArea *
        (2 * ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) +
          ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
            cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1))) (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖)) 0) := by
  set a := rationalSourceModeAmplitude (‖ringComplex P.p‖ * v)
  set b := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖)
  have ha : Summable (fun h => ‖a h‖) := rationalSourceModeAmplitude_summable _ (mul_pos P.norm_pos hv)
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  have hbp : Summable (fun m => ‖b (m * P.p)‖) := hb.comp_injective hinj
  have hg : ∀ β : O, Summable (fun m => ‖cuspConv (P.shiftedLow v β) b (m * P.p)‖) := fun β =>
    (summable_cuspConv (P.summable_shiftedLow v hv β) hb).comp_injective hinj
  simp_rw [P.sourceHeckeTrace_upperPoint v hv]
  have hc1 : Continuous (fun z : ℂ => cuspCharacterSeries a (ringComplex P.p * z) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => b (m * P.p)) z)) :=
    ((cuspCharacterSeries_continuous a ha).comp (continuous_const.mul continuous_id)).mul
      (continuous_const.mul (cuspCharacterSeries_continuous _ hbp))
  have hc2 : ∀ y : {y : P.Res // y ≠ 0}, Continuous (fun z : ℂ => ringComplex (symbol (3 * P.lift y.1) P.p) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1)))
        b (m * P.p)) z)) := fun y =>
    continuous_const.mul (continuous_const.mul (cuspCharacterSeries_continuous _ (hg _)))
  have h1 := integral_cuspCharacterSeries_mul_dilate P.p a (fun m => b (m * P.p)) ha hbp
  have I1 : ∫ z in periodDomain, cuspCharacterSeries a (ringComplex P.p * z) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => b (m * P.p)) z) =
      (Fintype.card P.Res : ℂ) * (periodArea * ∑' h : O, a h * b (-(h * P.p) * P.p)) := by
    rw [show (fun z : ℂ => cuspCharacterSeries a (ringComplex P.p * z) *
        ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => b (m * P.p)) z)) =
        fun z => (Fintype.card P.Res : ℂ) * (cuspCharacterSeries a (ringComplex P.p * z) *
          cuspCharacterSeries (fun m => b (m * P.p)) z) by funext z; ring, integral_const_mul, h1]
  have I2 : ∀ y : {y : P.Res // y ≠ 0}, ∫ z in periodDomain, ringComplex (symbol (3 * P.lift y.1) P.p) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1)))
        b (m * P.p)) z) =
      ringComplex (symbol (3 * P.lift y.1) P.p) * ((Fintype.card P.Res : ℂ) *
        (periodArea * cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1))) b 0)) := by
    intro y
    rw [integral_const_mul, integral_const_mul, integral_cuspCharacterSeries _ (hg _), zero_mul]
  rw [integral_add ((integrableOn_periodDomain_of_continuous _ hc1).const_mul 2)
      (integrable_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc2 y)),
    integral_const_mul, I1, integral_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc2 y),
    Finset.sum_congr rfl fun y _ => I2 y, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun y _ => by ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
