import GaloisForLFunctions.BiScaleUncertainty.CramerLimitLaw

/-!
# Asymptotics of the finite-cutoff packet energy including the endpoint term

For a compactly supported `C²` source `F` vanishing outside `[−w, w]` and a prime–polar cutoff
`L = cutoff N = log(N + 2) ≥ 2w`, the finite-cutoff signed packet `signedSource F N` is supported
in `[−L − w, w]` and decomposes across three zones:

1. **Cutoff boundary layer `[−L − w, −L + w]`:** Here `F(u + L)` carries its full `L²` norm
   `autocorr F 0`, while the boundary-corrected residual `R_N(u) − D_N(u)` only samples the
   normalized Chebyshev error `Ẽ(t)` on the trailing window `t ∈ [L − 2w, L]` of fixed width `2w`.
2. **Stationary bulk `[−L + w, −w]`:** Here `F(u + L) = 0` and `signedSource F N (−τ)` coincides
   pointwise with the stationary prime–polar packet `stationaryPacket F τ` for `τ ∈ [w, L − w)`.
3. **Origin zone `[−w, w]`:** Here `F(u + L) = 0` (for `L > 2w`) and `D_N(u)` only samples `Ẽ(t)`
   on the initial window `t ∈ [0, 2w]`, contributing `O_F(1)` energy independent of `N`.

Main results:

* **Three-zone energy identity** (`packetEnergy_eq_three_zones`):
  `packetEnergy F N = ∫_{−L−w}^{−L+w} (signedSource F N)² + ∫_w^{L−w} P_F² + ∫_{−w}^w (signedSource F N)²`.
* **Exact asymptotics of the boundary-corrected packet and gauge convolution**
  (`tendsto_boundaryCorrectedPacketEnergy_div_cutoff`,
  `tendsto_chebyshevGaugeConvolution_energy_div_cutoff`): under RH, subtracting the cutoff jump
  `Ẽ(L) F(· + L)` removes the boundary oscillation and both normalized energies converge to
  `criticalPacketEnergy F = Σ_ρ m_ρ² |F̂(γ_ρ)|²`.
* **Asymptotic sandwich of the finite-cutoff packet energy including `Ẽ(L)²`**
  (`eventually_packetEnergy_div_cutoff_bounds`, `eventually_packetEnergy_div_cutoff_ge`): under RH,
  for every `η > 0` and `ε > 0`, eventually
  `E(F) + (1 + η)⁻¹ Ẽ(L)² h_F(0) / L − ε ≤ packetEnergy F N / L ≤ E(F) + (1 + η) Ẽ(L)² h_F(0) / L + ε`.
* **Exact convergence criterion for the unadjusted packet energy**
  (`tendsto_packetEnergy_div_cutoff_iff`): under RH, `packetEnergy F N / cutoff N → E(F)` along any
  filter finer than `atTop` if and only if `Ẽ(cutoff N)² * autocorr F 0 / cutoff N → 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Support localization of the gauge derivative and windowed gauge convolution -/

/-- If `f` vanishes outside `[−w, w]`, so does its hyperbolic gauge derivative `f' − f/2`. -/
theorem gaugeDerivative_eq_zero_of_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : w < |v|) :
    gaugeDerivative f v = 0 := by
  have hd : deriv f v = 0 := by
    have hev : f =ᶠ[𝓝 v] (fun _ => 0) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨{x | w < |x|},
        (isOpen_lt continuous_const continuous_abs).mem_nhds hv, fun x hx => hw x hx⟩
    rw [hev.deriv_eq, deriv_const]
  simp [gaugeDerivative, hd, hw v hv]

/-- The Chebyshev gauge convolution restricted to a subwindow `[a, b]`. -/
def windowedGaugeConvolution (f : ℝ → ℝ) (a b : ℝ) (u : ℝ) : ℝ :=
  ∫ t in Icc a b, normalizedLogError t * gaugeDerivative f (u + t)

theorem abs_indicator_Icc_normalizedLogError_le {a b : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    |(Icc a b).indicator normalizedLogError t| ≤
      Chebyshev.psi (Real.exp (max b 0)) + Real.exp (max b 0) := by
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht]
    exact abs_normalizedLogError_le (ha.trans ht.1) (ht.2.trans (le_max_left b 0))
  · rw [Set.indicator_of_notMem ht, abs_zero]
    exact add_nonneg (Chebyshev.psi_nonneg _) (Real.exp_pos _).le

theorem windowedGaugeConvolution_eq_indicator {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    windowedGaugeConvolution f a b u =
      ∫ t in Icc 0 (max b 0), (Icc a b).indicator normalizedLogError t *
        gaugeDerivative f (u + t) := by
  unfold windowedGaugeConvolution
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty hba.not_ge, setIntegral_empty]
    symm
    refine setIntegral_eq_zero_of_forall_eq_zero fun t _ => ?_
    simp
  · have hsub : Icc a b ⊆ Icc 0 (max b 0) :=
      Icc_subset_Icc ha (le_max_left b 0)
    symm
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
      (fun t ht => by rw [Set.indicator_of_notMem ht.2, zero_mul])]
    exact setIntegral_congr_fun measurableSet_Icc fun t ht => by
      rw [Set.indicator_of_mem ht]

theorem continuous_windowedGaugeConvolution (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ))
    {a b : ℝ} (ha : 0 ≤ a) : Continuous (windowedGaugeConvolution f a b) := by
  have h := continuous_windowedTranslate (L := max b 0)
    (φ := (Icc a b).indicator normalizedLogError)
    (measurable_normalizedLogError.indicator measurableSet_Icc)
    (abs_indicator_Icc_normalizedLogError_le ha) (continuous_gaugeDerivative hf)
    (hasCompactSupport_gaugeDerivative f.hasCompactSupport)
  convert h using 1
  funext u
  exact windowedGaugeConvolution_eq_indicator ha u

theorem hasCompactSupport_windowedGaugeConvolution (f : C_c(ℝ, ℝ)) {a b : ℝ} (ha : 0 ≤ a) :
    HasCompactSupport (windowedGaugeConvolution f a b) := by
  have h := hasCompactSupport_windowedTranslate (L := max b 0)
    (φ := (Icc a b).indicator normalizedLogError)
    (hasCompactSupport_gaugeDerivative f.hasCompactSupport)
  convert h using 1
  funext u
  exact windowedGaugeConvolution_eq_indicator ha u

theorem windowedGaugeConvolution_eq_lineConvolution (f : ℝ → ℝ) (a b u : ℝ) :
    windowedGaugeConvolution f a b u =
      GaloisForLFunctions.HTGeometry.lineConvolution (gaugeDerivative f)
        (fun y => (Icc a b).indicator normalizedLogError (-y)) u := by
  unfold windowedGaugeConvolution GaloisForLFunctions.HTGeometry.lineConvolution
  rw [← integral_indicator measurableSet_Icc]
  have hfun : (fun t => (Icc a b).indicator
      (fun t => normalizedLogError t * gaugeDerivative f (u + t)) t) =
      fun t => gaugeDerivative f (u + t) *
        (Icc a b).indicator normalizedLogError (-(u - (u + t))) := by
    funext t
    rw [Set.indicator_mul_left, mul_comm]
    congr 2; ring
  rw [hfun]
  exact integral_add_left_eq_self (fun s => gaugeDerivative f s *
    (Icc a b).indicator normalizedLogError (-(u - s))) u

theorem integrableOn_normalizedLogError_sq_Icc {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => normalizedLogError t ^ 2) (Icc a b) :=
  (integrableOn_normalizedLogError_sq (max b 0)).mono_set
    (Icc_subset_Icc ha (le_max_left b 0))

/-- **Young bound on a subwindow `[a, b]`:**
`∫ (windowedGaugeConvolution f a b)² ≤ ‖f' − f/2‖₁² ∫_a^b Ẽ(t)² dt`. -/
theorem integral_sq_windowedGaugeConvolution_le (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ u, windowedGaugeConvolution f a b u ^ 2) ≤
      (∫ u, |gaugeDerivative f u|) ^ 2 * ∫ t in Icc a b, normalizedLogError t ^ 2 := by
  set g : ℝ → ℝ := gaugeDerivative (f : ℝ → ℝ)
  set V : ℝ → ℝ := fun y => (Icc a b).indicator normalizedLogError (-y)
  have hgc : Continuous g := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport g := hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hVm : Measurable V :=
    (measurable_normalizedLogError.indicator measurableSet_Icc).comp measurable_neg
  have hV2 : Integrable (fun y => V y ^ 2) := by
    have h1 : Integrable ((Icc a b).indicator fun t => normalizedLogError t ^ 2) :=
      (integrableOn_normalizedLogError_sq_Icc ha).integrable_indicator measurableSet_Icc
    refine h1.comp_neg.congr (Filter.Eventually.of_forall fun y => ?_)
    by_cases h : -y ∈ Icc a b
    · simp only [V, Set.indicator_of_mem h]
    · simp only [V, Set.indicator_of_notMem h, zero_pow two_ne_zero]
  have hgabs : Integrable (fun t => |g t|) :=
    hgc.abs.integrable_of_hasCompactSupport (hgs.comp_left abs_zero)
  have hline : GaloisForLFunctions.HTGeometry.lineConvolution g V =
      windowedGaugeConvolution f a b := by
    funext u
    exact (windowedGaugeConvolution_eq_lineConvolution f a b u).symm
  have hconv : Integrable (fun x => GaloisForLFunctions.HTGeometry.lineConvolution g V x ^ 2) := by
    rw [hline]
    exact integrable_sq (continuous_windowedGaugeConvolution f hf ha)
      (hasCompactSupport_windowedGaugeConvolution f ha)
  have h := GaloisForLFunctions.HTGeometry.integral_sq_lineConvolution_le hgc.measurable hVm
    hgabs hV2 hconv
  rw [hline] at h
  have hVint : (∫ y, V y ^ 2) = ∫ t in Icc a b, normalizedLogError t ^ 2 := by
    have hfun : (fun y => V y ^ 2) =
        fun y => (Icc a b).indicator (fun t => normalizedLogError t ^ 2) (-y) := by
      funext y
      by_cases hy : -y ∈ Icc a b
      · simp only [V, Set.indicator_of_mem hy]
      · simp only [V, Set.indicator_of_notMem hy, zero_pow two_ne_zero]
    rw [hfun, integral_neg_eq_self, integral_indicator measurableSet_Icc]
  rwa [hVint] at h

/-- On the cutoff boundary layer `u ≤ −L + w`, `D_N(u)` only integrates `Ẽ(t)` over
`t ∈ [L − 2w, L]`. -/
theorem chebyshevGaugeConvolution_eq_tail_window {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) {u : ℝ}
    (hu : u ≤ -cutoff N + w) :
    chebyshevGaugeConvolution f N u =
      windowedGaugeConvolution f (cutoff N - 2 * w) (cutoff N) u := by
  unfold chebyshevGaugeConvolution windowedGaugeConvolution
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Icc_subset_Icc (by linarith) le_rfl) fun t ht => ?_
  have htlt : t < cutoff N - 2 * w := by
    by_contra h
    exact ht.2 ⟨not_lt.mp h, ht.1.2⟩
  rw [gaugeDerivative_eq_zero_of_lt_abs hw (lt_abs.mpr (Or.inr (by linarith))), mul_zero]

/-- On `u ≥ −w`, `D_N(u)` only integrates `Ẽ(t)` over `t ∈ [0, 2w]`. -/
theorem chebyshevGaugeConvolution_eq_head_window {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) {u : ℝ}
    (hu : -w ≤ u) :
    chebyshevGaugeConvolution f N u =
      windowedGaugeConvolution f 0 (2 * w) u := by
  unfold chebyshevGaugeConvolution windowedGaugeConvolution
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Icc_subset_Icc le_rfl hLw) fun t ht => ?_
  have htgt : 2 * w < t := by
    by_contra h
    exact ht.2 ⟨ht.1.1, not_lt.mp h⟩
  rw [gaugeDerivative_eq_zero_of_lt_abs hw (lt_abs.mpr (Or.inl (by linarith))), mul_zero]

/-! ## Support and three-zone decomposition of the finite-cutoff packet -/

/-- If `F` vanishes outside `[−w, w]`, then `signedSource F N` vanishes outside `[−L − w, w]`. -/
theorem signedSource_eq_zero_of_notMem_Icc (F : C_c(ℝ, ℝ)) {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) {u : ℝ}
    (hu : u ∉ Icc (-cutoff N - w) w) :
    signedSource F N u = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hu
  show atomicSource F N u - polarSource F N u = 0
  have hatom : atomicSource F N u = 0 := by
    change (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * F (u + Real.log n)) = 0
    refine Finset.sum_eq_zero fun n hn => ?_
    obtain ⟨hn0, hnL⟩ := node_bounds N n hn
    have hF0 : F (u + Real.log n) = 0 := by
      rcases hu with hlt | hgt
      · exact hw _ (lt_abs.mpr (Or.inr (by linarith)))
      · exact hw _ (lt_abs.mpr (Or.inl (by linarith)))
    rw [hF0, mul_zero]
  have hpolar : polarSource F N u = 0 := by
    change (∫ t in Icc 0 (cutoff N), polarDensity t * F (u + t)) = 0
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    have hF0 : F (u + t) = 0 := by
      rcases hu with hlt | hgt
      · exact hw _ (lt_abs.mpr (Or.inr (by linarith [ht.2])))
      · exact hw _ (lt_abs.mpr (Or.inl (by linarith [ht.1])))
    rw [hF0, mul_zero]
  rw [hatom, hpolar, sub_self]

/-- The finite-cutoff packet energy equals the interval integral on `[−cutoff N − w, w]`. -/
theorem packetEnergy_eq_intervalIntegral (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) :
    packetEnergy F N = ∫ u in (-cutoff N - w)..w, signedSource F N u ^ 2 := by
  have hL : 0 ≤ cutoff N := cutoff_nonneg N
  have hab : -cutoff N - w ≤ w := by linarith
  unfold packetEnergy
  rw [← integral_sq_eq_autocorr_zero (signedSource F N),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [signedSource_eq_zero_of_notMem_Icc F hw N hu, sq, mul_zero]).symm

/-- On `[−cutoff N + w, −w]` the reflected signed packet integral equals the stationary packet
integral on `[w, cutoff N − w]`. -/
theorem integral_signedSource_sq_bulk_eq_stationaryPacket (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) :
    (∫ u in (-cutoff N + w)..(-w), signedSource F N u ^ 2) =
      ∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2 := by
  have hneg := intervalIntegral.integral_comp_neg (fun u => signedSource F N u ^ 2)
    (a := w) (b := cutoff N - w)
  rw [show -(cutoff N - w) = -cutoff N + w by ring] at hneg
  rw [← hneg]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ τ : ℝ, τ ≠ cutoff N - w := Measure.ae_ne volume (cutoff N - w)
  filter_upwards [hne] with τ hτne hτ
  rw [uIoc_of_le (by linarith)] at hτ
  have hτlt : τ < cutoff N - w := lt_of_le_of_ne hτ.2 hτne
  rw [stationaryPacket_eq_signedSource F hw0 hw (by linarith)]

/-- **Three-zone decomposition of the finite-cutoff packet energy.** For `2w ≤ cutoff N`,
`packetEnergy F N` splits into the cutoff boundary layer `[−L − w, −L + w]`, the stationary bulk
`∫_w^{L−w} P_F²`, and the origin zone `[−w, w]`. -/
theorem packetEnergy_eq_three_zones (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) :
    packetEnergy F N =
      (∫ u in (-cutoff N - w)..(-cutoff N + w), signedSource F N u ^ 2) +
        (∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2) +
        (∫ u in (-w)..w, signedSource F N u ^ 2) := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun u => signedSource F N u ^ 2) volume a b :=
    fun a b => ((signedSource F N).continuous.pow 2).intervalIntegrable a b
  rw [packetEnergy_eq_intervalIntegral F hw0 hw N,
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-cutoff N - w) (-cutoff N + w))
      (hI (-cutoff N + w) w),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-cutoff N + w) (-w))
      (hI (-w) w),
    integral_signedSource_sq_bulk_eq_stationaryPacket F hw0 hw hLw, add_assoc]

/-! ## Boundary-corrected packet energy and zone bounds -/

/-- The signed packet with the cutoff jump `Ẽ(L) F(u + L)` removed:
`boundaryCorrectedPacket F N u = signedSource F N u − Ẽ(cutoff N) F(u + cutoff N) = R_N(u) − D_N(u)`. -/
def boundaryCorrectedPacket (F : C_c(ℝ, ℝ)) (N : ℕ) (u : ℝ) : ℝ :=
  signedSource F N u - normalizedLogError (cutoff N) * F (u + cutoff N)

/-- Total `L²` energy of the boundary-corrected packet. -/
def boundaryCorrectedPacketEnergy (F : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  ∫ u, boundaryCorrectedPacket F N u ^ 2

theorem boundaryCorrectedPacket_eq_gauge (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ))
    (N : ℕ) (u : ℝ) :
    boundaryCorrectedPacket F N u =
      forwardResidual F N u - chebyshevGaugeConvolution F N u := by
  unfold boundaryCorrectedPacket
  rw [signedSource_eq_gauge F hF N u]
  ring

theorem continuous_boundaryCorrectedPacket (F : C_c(ℝ, ℝ)) (N : ℕ) :
    Continuous (boundaryCorrectedPacket F N) :=
  (signedSource F N).continuous.sub
    (continuous_const.mul (F.continuous.comp (continuous_add_const _)))

theorem hasCompactSupport_boundaryCorrectedPacket (F : C_c(ℝ, ℝ)) (N : ℕ) :
    HasCompactSupport (boundaryCorrectedPacket F N) :=
  (signedSource F N).hasCompactSupport.sub
    ((hasCompactSupport_comp_add F.hasCompactSupport (cutoff N)).mul_left)

/-- Outside the cutoff boundary layer `[−L − w, −L + w]`, `F(u + L) = 0`, so the signed packet and
the boundary-corrected packet coincide. -/
theorem signedSource_eq_boundaryCorrectedPacket_of_notMem (F : C_c(ℝ, ℝ)) {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) {u : ℝ}
    (hu : u ∉ Icc (-cutoff N - w) (-cutoff N + w)) :
    signedSource F N u = boundaryCorrectedPacket F N u := by
  unfold boundaryCorrectedPacket
  have hF0 : F (u + cutoff N) = 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hlt | hgt
    · exact hw _ (lt_abs.mpr (Or.inr (by linarith)))
    · exact hw _ (lt_abs.mpr (Or.inl (by linarith)))
  rw [hF0, mul_zero, sub_zero]

/-- On the cutoff boundary layer `[−L − w, −L + w]`, the `L²` norm of `F(u + L)` is `autocorr F 0`. -/
theorem integral_shift_sq_boundary_layer (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) :
    (∫ u in (-cutoff N - w)..(-cutoff N + w), (F : ℝ → ℝ) (u + cutoff N) ^ 2) = autocorr F 0 := by
  have heq : -cutoff N + w + cutoff N = w := by ring
  have heq' : -cutoff N - w + cutoff N = -w := by ring
  rw [intervalIntegral.integral_comp_add_right (fun v => (F : ℝ → ℝ) v ^ 2) (cutoff N),
    heq, heq', intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
      simp only [mem_Icc, not_and_or, not_le] at hv
      have h0 : F v = 0 := by
        rcases hv with hlt | hgt
        · exact hw _ (lt_abs.mpr (Or.inr (by linarith)))
        · exact hw _ (lt_abs.mpr (Or.inl (by linarith)))
      rw [h0, sq, mul_zero]]
  exact integral_sq_eq_autocorr_zero F

/-- Bound on the boundary-corrected packet energy in the cutoff boundary layer `[−L − w, −L + w]`. -/
theorem integral_boundaryCorrectedPacket_sq_boundary_le (F : C_c(ℝ, ℝ))
    (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) :
    (∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) ≤
      20 * autocorr F 0 +
        2 * (∫ u, |gaugeDerivative F u|) ^ 2 *
          ∫ t in Icc (cutoff N - 2 * w) (cutoff N), normalizedLogError t ^ 2 := by
  set a := -cutoff N - w
  set b := -cutoff N + w
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hRc := continuous_forwardResidual F hF N
  have hWc := continuous_windowedGaugeConvolution F hF (a := cutoff N - 2 * w)
    (b := cutoff N) (by linarith)
  have hR2 : Integrable fun u => forwardResidual F N u ^ 2 :=
    integrable_sq hRc (hasCompactSupport_forwardResidual F hF N)
  have hW2 : Integrable fun u => windowedGaugeConvolution F (cutoff N - 2 * w) (cutoff N) u ^ 2 :=
    integrable_sq hWc (hasCompactSupport_windowedGaugeConvolution F (by linarith))
  have hRI : IntervalIntegrable (fun u => 2 * forwardResidual F N u ^ 2) volume a b :=
    ((hRc.pow 2).const_mul 2).intervalIntegrable a b
  have hWI : IntervalIntegrable
      (fun u => 2 * windowedGaugeConvolution F (cutoff N - 2 * w) (cutoff N) u ^ 2) volume a b :=
    ((hWc.pow 2).const_mul 2).intervalIntegrable a b
  have h1 : (∫ u in a..b, boundaryCorrectedPacket F N u ^ 2) ≤
      ∫ u in a..b, (2 * forwardResidual F N u ^ 2 +
        2 * windowedGaugeConvolution F (cutoff N - 2 * w) (cutoff N) u ^ 2) := by
    refine intervalIntegral.integral_mono_on hab
      (((continuous_boundaryCorrectedPacket F N).pow 2).intervalIntegrable a b)
      (hRI.add hWI) fun u hu => ?_
    rw [boundaryCorrectedPacket_eq_gauge F hF N u,
      chebyshevGaugeConvolution_eq_tail_window hw hLw hu.2]
    nlinarith [sq_nonneg (forwardResidual F N u +
      windowedGaugeConvolution F (cutoff N - 2 * w) (cutoff N) u)]
  rw [intervalIntegral.integral_add hRI hWI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
  have hRle : (∫ u in a..b, forwardResidual F N u ^ 2) ≤ 10 * autocorr F 0 :=
    (integral_Ioo_le_integral_of_nonneg hR2 (fun _ => sq_nonneg _) hab).trans
      (integral_sq_forwardResidual_le F N)
  have hWle : (∫ u in a..b, windowedGaugeConvolution F (cutoff N - 2 * w) (cutoff N) u ^ 2) ≤
      (∫ u, |gaugeDerivative F u|) ^ 2 *
        ∫ t in Icc (cutoff N - 2 * w) (cutoff N), normalizedLogError t ^ 2 :=
    (integral_Ioo_le_integral_of_nonneg hW2 (fun _ => sq_nonneg _) hab).trans
      (integral_sq_windowedGaugeConvolution_le F hF (by linarith))
  linarith

/-- Bound on the boundary-corrected packet energy in the origin zone `[−w, w]`. -/
theorem integral_boundaryCorrectedPacket_sq_origin_le (F : C_c(ℝ, ℝ))
    (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) :
    (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) ≤
      20 * autocorr F 0 +
        2 * (∫ u, |gaugeDerivative F u|) ^ 2 *
          ∫ t in Icc 0 (2 * w), normalizedLogError t ^ 2 := by
  have hab : -w ≤ w := by linarith
  have hRc := continuous_forwardResidual F hF N
  have hWc := continuous_windowedGaugeConvolution F hF (a := 0) (b := 2 * w) le_rfl
  have hR2 : Integrable fun u => forwardResidual F N u ^ 2 :=
    integrable_sq hRc (hasCompactSupport_forwardResidual F hF N)
  have hW2 : Integrable fun u => windowedGaugeConvolution F 0 (2 * w) u ^ 2 :=
    integrable_sq hWc (hasCompactSupport_windowedGaugeConvolution F le_rfl)
  have hRI : IntervalIntegrable (fun u => 2 * forwardResidual F N u ^ 2) volume (-w) w :=
    ((hRc.pow 2).const_mul 2).intervalIntegrable (-w) w
  have hWI : IntervalIntegrable
      (fun u => 2 * windowedGaugeConvolution F 0 (2 * w) u ^ 2) volume (-w) w :=
    ((hWc.pow 2).const_mul 2).intervalIntegrable (-w) w
  have h1 : (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) ≤
      ∫ u in (-w)..w, (2 * forwardResidual F N u ^ 2 +
        2 * windowedGaugeConvolution F 0 (2 * w) u ^ 2) := by
    refine intervalIntegral.integral_mono_on hab
      (((continuous_boundaryCorrectedPacket F N).pow 2).intervalIntegrable (-w) w)
      (hRI.add hWI) fun u hu => ?_
    rw [boundaryCorrectedPacket_eq_gauge F hF N u,
      chebyshevGaugeConvolution_eq_head_window hw hLw hu.1]
    nlinarith [sq_nonneg (forwardResidual F N u +
      windowedGaugeConvolution F 0 (2 * w) u)]
  rw [intervalIntegral.integral_add hRI hWI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
  have hRle : (∫ u in (-w)..w, forwardResidual F N u ^ 2) ≤ 10 * autocorr F 0 :=
    (integral_Ioo_le_integral_of_nonneg hR2 (fun _ => sq_nonneg _) hab).trans
      (integral_sq_forwardResidual_le F N)
  have hWle : (∫ u in (-w)..w, windowedGaugeConvolution F 0 (2 * w) u ^ 2) ≤
      (∫ u, |gaugeDerivative F u|) ^ 2 *
        ∫ t in Icc 0 (2 * w), normalizedLogError t ^ 2 :=
    (integral_Ioo_le_integral_of_nonneg hW2 (fun _ => sq_nonneg _) hab).trans
      (integral_sq_windowedGaugeConvolution_le F hF le_rfl)
  linarith

/-- Three-zone decomposition of `boundaryCorrectedPacketEnergy F N`: for `2w ≤ cutoff N`,
`boundaryCorrectedPacketEnergy F N` splits into the boundary layer, the stationary bulk
`∫_w^{L−w} P_F²`, and the origin zone. -/
theorem boundaryCorrectedPacketEnergy_eq_three_zones (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {N : ℕ} (hLw : 2 * w ≤ cutoff N) :
    boundaryCorrectedPacketEnergy F N =
      (∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) +
        (∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2) +
        (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) := by
  have hL : 0 ≤ cutoff N := cutoff_nonneg N
  have hab : -cutoff N - w ≤ w := by linarith
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun u => boundaryCorrectedPacket F N u ^ 2) volume a b :=
    fun a b => ((continuous_boundaryCorrectedPacket F N).pow 2).intervalIntegrable a b
  have hfull : boundaryCorrectedPacketEnergy F N =
      ∫ u in (-cutoff N - w)..w, boundaryCorrectedPacket F N u ^ 2 := by
    unfold boundaryCorrectedPacketEnergy
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    have hnot : u ∉ Icc (-cutoff N - w) (-cutoff N + w) := fun h =>
      hu ⟨h.1, h.2.trans (by linarith)⟩
    rw [← signedSource_eq_boundaryCorrectedPacket_of_notMem F hw N hnot,
      signedSource_eq_zero_of_notMem_Icc F hw N hu, sq, mul_zero]
  have hbulk : (∫ u in (-cutoff N + w)..(-w), boundaryCorrectedPacket F N u ^ 2) =
      ∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2 := by
    rw [← integral_signedSource_sq_bulk_eq_stationaryPacket F hw0 hw hLw]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with u hu
    rw [uIoc_of_le (by linarith)] at hu
    have hnot : u ∉ Icc (-cutoff N - w) (-cutoff N + w) := by
      simp only [mem_Icc, not_and_or, not_le]
      exact Or.inr hu.1
    rw [signedSource_eq_boundaryCorrectedPacket_of_notMem F hw N hnot]
  rw [hfull,
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-cutoff N - w) (-cutoff N + w))
      (hI (-cutoff N + w) w),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (-cutoff N + w) (-w))
      (hI (-w) w),
    hbulk, add_assoc]

/-! ## Unconditional two-sided bounds in the cutoff boundary layer -/

/-- Upper bound in the cutoff boundary layer: for every `η > 0`,
`∫_{−L−w}^{−L+w} (signedSource F N)² ≤ (1 + η) Ẽ(L)² h_F(0) + (1 + 1/η) ∫_{−L−w}^{−L+w} Y_N²`. -/
theorem integral_signedSource_sq_boundary_le (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) {η : ℝ} (hη : 0 < η) :
    (∫ u in (-cutoff N - w)..(-cutoff N + w), signedSource F N u ^ 2) ≤
      (1 + η) * (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) +
        (1 + 1 / η) * ∫ u in (-cutoff N - w)..(-cutoff N + w),
          boundaryCorrectedPacket F N u ^ 2 := by
  set a := -cutoff N - w
  set b := -cutoff N + w
  have hab : a ≤ b := by simp only [a, b]; linarith
  set B : ℝ → ℝ := fun u => normalizedLogError (cutoff N) * F (u + cutoff N)
  have hBc : Continuous B :=
    continuous_const.mul (F.continuous.comp (continuous_add_const _))
  have hYc : Continuous (boundaryCorrectedPacket F N) := continuous_boundaryCorrectedPacket F N
  have hBI : IntervalIntegrable (fun u => (1 + η) * B u ^ 2) volume a b :=
    ((hBc.pow 2).const_mul (1 + η)).intervalIntegrable a b
  have hYI : IntervalIntegrable
      (fun u => (1 + 1 / η) * boundaryCorrectedPacket F N u ^ 2) volume a b :=
    ((hYc.pow 2).const_mul (1 + 1 / η)).intervalIntegrable a b
  have h1 : (∫ u in a..b, signedSource F N u ^ 2) ≤
      ∫ u in a..b, ((1 + η) * B u ^ 2 + (1 + 1 / η) * boundaryCorrectedPacket F N u ^ 2) := by
    refine intervalIntegral.integral_mono_on hab
      (((signedSource F N).continuous.pow 2).intervalIntegrable a b)
      (hBI.add hYI) fun u _ => ?_
    have heq : signedSource F N u = boundaryCorrectedPacket F N u - (-B u) := by
      unfold boundaryCorrectedPacket B; ring
    rw [heq]
    simpa only [neg_sq] using sub_sq_le_weighted hη (boundaryCorrectedPacket F N u) (-B u)
  have hBint : (∫ u in a..b, B u ^ 2) = normalizedLogError (cutoff N) ^ 2 * autocorr F 0 := by
    have hfun : (fun u => B u ^ 2) =
        fun u => normalizedLogError (cutoff N) ^ 2 * (F : ℝ → ℝ) (u + cutoff N) ^ 2 := by
      funext u; simp only [B]; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_shift_sq_boundary_layer F hw0 hw N]
  rw [intervalIntegral.integral_add hBI hYI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hBint] at h1
  exact h1

/-- Lower bound in the cutoff boundary layer: for every `η > 0`,
`(1 + η)⁻¹ Ẽ(L)² h_F(0) − η⁻¹ ∫_{−L−w}^{−L+w} Y_N² ≤ ∫_{−L−w}^{−L+w} (signedSource F N)²`. -/
theorem le_integral_signedSource_sq_boundary (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) (N : ℕ) {η : ℝ} (hη : 0 < η) :
    (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / (1 + η) -
        (1 / η) * (∫ u in (-cutoff N - w)..(-cutoff N + w),
          boundaryCorrectedPacket F N u ^ 2) ≤
      ∫ u in (-cutoff N - w)..(-cutoff N + w), signedSource F N u ^ 2 := by
  set a := -cutoff N - w
  set b := -cutoff N + w
  have hab : a ≤ b := by simp only [a, b]; linarith
  set B : ℝ → ℝ := fun u => normalizedLogError (cutoff N) * F (u + cutoff N)
  have hBc : Continuous B :=
    continuous_const.mul (F.continuous.comp (continuous_add_const _))
  have hYc : Continuous (boundaryCorrectedPacket F N) := continuous_boundaryCorrectedPacket F N
  have hSI : IntervalIntegrable (fun u => (1 + η) * signedSource F N u ^ 2) volume a b :=
    (((signedSource F N).continuous.pow 2).const_mul (1 + η)).intervalIntegrable a b
  have hYI : IntervalIntegrable
      (fun u => (1 + 1 / η) * boundaryCorrectedPacket F N u ^ 2) volume a b :=
    ((hYc.pow 2).const_mul (1 + 1 / η)).intervalIntegrable a b
  have h1 : (∫ u in a..b, B u ^ 2) ≤
      ∫ u in a..b, ((1 + η) * signedSource F N u ^ 2 +
        (1 + 1 / η) * boundaryCorrectedPacket F N u ^ 2) := by
    refine intervalIntegral.integral_mono_on hab
      ((hBc.pow 2).intervalIntegrable a b) (hSI.add hYI) fun u _ => ?_
    have hBsq : B u ^ 2 = (boundaryCorrectedPacket F N u - signedSource F N u) ^ 2 := by
      unfold boundaryCorrectedPacket B; ring
    rw [hBsq]
    exact sub_sq_le_weighted hη (boundaryCorrectedPacket F N u) (signedSource F N u)
  have hBint : (∫ u in a..b, B u ^ 2) = normalizedLogError (cutoff N) ^ 2 * autocorr F 0 := by
    have hfun : (fun u => B u ^ 2) =
        fun u => normalizedLogError (cutoff N) ^ 2 * (F : ℝ → ℝ) (u + cutoff N) ^ 2 := by
      funext u; simp only [B]; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_shift_sq_boundary_layer F hw0 hw N]
  rw [hBint, intervalIntegral.integral_add hSI hYI,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
  have hη1 : 0 < 1 + η := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ hη1]
  have heq : 1 / η * (∫ u in a..b, boundaryCorrectedPacket F N u ^ 2) * (1 + η) =
      (1 + 1 / η) * ∫ u in a..b, boundaryCorrectedPacket F N u ^ 2 := by
    field_simp; ring
  linarith

/-! ## Exact asymptotics of the boundary-corrected packet and gauge convolution -/

theorem tendsto_cutoff_atTop : Tendsto cutoff atTop atTop := by
  have h : cutoff = fun N : ℕ => Real.log ((N : ℝ) + 2) := by
    funext N; unfold cutoff; push_cast; rfl
  rw [h]
  exact Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)

/-- Under RH, the boundary-layer energy of `boundaryCorrectedPacket F N` is `o(cutoff N)`. -/
theorem tendsto_boundary_layer_energy_div_cutoff (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) :
    Tendsto (fun N : ℕ =>
      (∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) / cutoff N)
      atTop (𝓝 0) := by
  have hwin := (tendsto_setIntegral_window_sq_normalizedLogError_div hRH
    (W := 2 * w) (by positivity)).comp tendsto_cutoff_atTop
  have hconst : Tendsto (fun N : ℕ => (20 * autocorr F 0) / cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_cutoff_atTop
  have hupper : Tendsto (fun N : ℕ =>
      (20 * autocorr F 0) / cutoff N +
        2 * (∫ u, |gaugeDerivative F u|) ^ 2 *
          ((∫ t in Icc (cutoff N - 2 * w) (cutoff N), normalizedLogError t ^ 2) / cutoff N))
      atTop (𝓝 0) := by
    simpa using hconst.add (hwin.const_mul (2 * (∫ u, |gaugeDerivative F u|) ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (2 * w))] with N hLw
    exact div_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)
      (cutoff_nonneg N)
  · filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (2 * w))] with N hLw
    have hle := div_le_div_of_nonneg_right
      (integral_boundaryCorrectedPacket_sq_boundary_le F hF hw0 hw hLw) (cutoff_nonneg N)
    calc (∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) / cutoff N
        ≤ (20 * autocorr F 0 + 2 * (∫ u, |gaugeDerivative F u|) ^ 2 *
            ∫ t in Icc (cutoff N - 2 * w) (cutoff N), normalizedLogError t ^ 2) / cutoff N := hle
      _ = (20 * autocorr F 0) / cutoff N +
          2 * (∫ u, |gaugeDerivative F u|) ^ 2 *
            ((∫ t in Icc (cutoff N - 2 * w) (cutoff N), normalizedLogError t ^ 2) / cutoff N) := by
        ring

/-- The origin-zone energy of `boundaryCorrectedPacket F N` is `O_F(1)`, hence `o(cutoff N)`. -/
theorem tendsto_origin_zone_energy_div_cutoff (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ))
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → F v = 0) :
    Tendsto (fun N : ℕ =>
      (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) / cutoff N) atTop (𝓝 0) := by
  set C := 20 * autocorr F 0 +
    2 * (∫ u, |gaugeDerivative F u|) ^ 2 * ∫ t in Icc 0 (2 * w), normalizedLogError t ^ 2
  have hupper : Tendsto (fun N : ℕ => C / cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_cutoff_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with N
    exact div_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)
      (cutoff_nonneg N)
  · filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (2 * w))] with N hLw
    exact div_le_div_of_nonneg_right
      (integral_boundaryCorrectedPacket_sq_origin_le F hF hw0 hw hLw) (cutoff_nonneg N)

/-- Under RH, the stationary bulk energy `(1/cutoff N) ∫_w^{cutoff N − w} P_F²` converges to
`criticalPacketEnergy F`. -/
theorem tendsto_stationary_bulk_energy_div_cutoff (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) :
    Tendsto (fun N : ℕ =>
      (∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2) / cutoff N)
      atTop (𝓝 (criticalPacketEnergy F)) := by
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (F u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  have hP := (tendsto_mean_sq_stationaryPacket_of_blind hF F.hasCompactSupport hw0 hw hblind).comp
    ((tendsto_atTop_add_const_right atTop (-w) tendsto_id).comp tendsto_cutoff_atTop)
  have hratio : Tendsto (fun N : ℕ => (cutoff N - w) / cutoff N) atTop (𝓝 1) := by
    have h := (tendsto_div_add_const w).comp
      ((tendsto_atTop_add_const_right atTop (-w) tendsto_id).comp tendsto_cutoff_atTop)
    refine h.congr fun N => ?_
    simp [sub_eq_add_neg]
  have hmul := hP.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [tendsto_cutoff_atTop.eventually (eventually_gt_atTop w)] with N hNw
  simp only [Function.comp_apply, id, ← sub_eq_add_neg]
  have hne : cutoff N - w ≠ 0 := by linarith
  field_simp

/-- **Exact asymptotic law for the boundary-corrected packet energy.** Under RH, for every `C²`
compactly supported source `F`, removing the cutoff jump `Ẽ(L) F(· + L)` makes the normalized
packet energy converge to `criticalPacketEnergy F = Σ_ρ m_ρ² |F̂(γ_ρ)|²`. -/
theorem tendsto_boundaryCorrectedPacketEnergy_div_cutoff (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) :
    Tendsto (fun N : ℕ => boundaryCorrectedPacketEnergy F N / cutoff N)
      atTop (𝓝 (criticalPacketEnergy F)) := by
  have hF1 : ContDiff ℝ 1 (F : ℝ → ℝ) := hF.of_le (by norm_num)
  obtain ⟨w, hw0, hwf⟩ := F.hasCompactSupport.exists_pos_le_norm
  have hw : ∀ v : ℝ, w < |v| → F v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hbdry := tendsto_boundary_layer_energy_div_cutoff hRH F hF1 hw0.le hw
  have hbulk := tendsto_stationary_bulk_energy_div_cutoff hRH F hF hw0.le hw
  have horig := tendsto_origin_zone_energy_div_cutoff F hF1 hw0.le hw
  have hsum := (hbdry.add hbulk).add horig
  rw [zero_add, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (2 * w))] with N hLw
  rw [boundaryCorrectedPacketEnergy_eq_three_zones F hw0.le hw hLw]
  ring

/-- **Exact asymptotic law for the Chebyshev gauge convolution energy.** Under RH, for every `C²`
compactly supported source `F`,
`lim_{N→∞} (1 / cutoff N) ∫ (chebyshevGaugeConvolution F N)² = criticalPacketEnergy F`. -/
theorem tendsto_chebyshevGaugeConvolution_energy_div_cutoff (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) :
    Tendsto (fun N : ℕ => (∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N)
      atTop (𝓝 (criticalPacketEnergy F)) := by
  have hF1 : ContDiff ℝ 1 (F : ℝ → ℝ) := hF.of_le (by norm_num)
  have hY := tendsto_boundaryCorrectedPacketEnergy_div_cutoff hRH F hF
  have hR : Tendsto (fun N : ℕ => (10 * autocorr F 0) / cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_cutoff_atTop
  rw [Metric.tendsto_atTop]
  intro ε hε
  set E := criticalPacketEnergy F
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => by positivity
  set η := ε / (2 * (E + 1))
  have hη : 0 < η := by positivity
  have hupper : Tendsto (fun N : ℕ =>
      (1 + η) * (boundaryCorrectedPacketEnergy F N / cutoff N) +
        (1 + 1 / η) * ((10 * autocorr F 0) / cutoff N))
      atTop (𝓝 ((1 + η) * E + (1 + 1 / η) * 0)) :=
    (hY.const_mul (1 + η)).add (hR.const_mul (1 + 1 / η))
  have hlower : Tendsto (fun N : ℕ =>
      (boundaryCorrectedPacketEnergy F N / cutoff N) / (1 + η) -
        (1 / η) * ((10 * autocorr F 0) / cutoff N))
      atTop (𝓝 (E / (1 + η) - (1 / η) * 0)) :=
    (hY.div_const (1 + η)).sub (hR.const_mul (1 / η))
  have hlt1 : (1 + η) * E + (1 + 1 / η) * 0 < E + ε := by
    have : η * E ≤ ε / 2 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hlt2 : E - ε < E / (1 + η) - (1 / η) * 0 := by
    rw [mul_zero, sub_zero, lt_div_iff₀ (by positivity)]
    have : η * E ≤ ε / 2 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hev := (hupper.eventually (gt_mem_nhds hlt1)).and
    ((hlower.eventually (lt_mem_nhds hlt2)).and
      (tendsto_cutoff_atTop.eventually (eventually_gt_atTop (0 : ℝ))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hup, hlo, hL0⟩ := hN₀ N hN
  have hR2 : Integrable fun u => forwardResidual F N u ^ 2 :=
    integrable_sq (continuous_forwardResidual F hF1 N) (hasCompactSupport_forwardResidual F hF1 N)
  have hD2 : Integrable fun u => chebyshevGaugeConvolution F N u ^ 2 :=
    integrable_sq (continuous_chebyshevGaugeConvolution F hF1 N)
      (hasCompactSupport_chebyshevGaugeConvolution F N)
  have hY2 : Integrable fun u => boundaryCorrectedPacket F N u ^ 2 :=
    integrable_sq (continuous_boundaryCorrectedPacket F N)
      (hasCompactSupport_boundaryCorrectedPacket F N)
  have hD_le : (∫ u, chebyshevGaugeConvolution F N u ^ 2) ≤
      (1 + η) * boundaryCorrectedPacketEnergy F N + (1 + 1 / η) * (10 * autocorr F 0) := by
    have h1 : (∫ u, chebyshevGaugeConvolution F N u ^ 2) ≤
        ∫ u, ((1 + η) * boundaryCorrectedPacket F N u ^ 2 +
          (1 + 1 / η) * forwardResidual F N u ^ 2) := by
      refine integral_mono hD2 ((hY2.const_mul (1 + η)).add (hR2.const_mul (1 + 1 / η))) fun u => ?_
      have heq : chebyshevGaugeConvolution F N u =
          forwardResidual F N u - boundaryCorrectedPacket F N u := by
        rw [boundaryCorrectedPacket_eq_gauge F hF1 N u]; ring
      rw [heq]
      exact sub_sq_le_weighted hη _ _
    rw [integral_add (hY2.const_mul (1 + η)) (hR2.const_mul (1 + 1 / η)),
      integral_const_mul, integral_const_mul] at h1
    have hRle := integral_sq_forwardResidual_le F N
    have hη1 : 0 ≤ 1 + 1 / η := by positivity
    unfold boundaryCorrectedPacketEnergy
    nlinarith [mul_le_mul_of_nonneg_left hRle hη1]
  have hY_le : boundaryCorrectedPacketEnergy F N ≤
      (1 + η) * (∫ u, chebyshevGaugeConvolution F N u ^ 2) + (1 + 1 / η) * (10 * autocorr F 0) := by
    have h1 : boundaryCorrectedPacketEnergy F N ≤
        ∫ u, ((1 + η) * chebyshevGaugeConvolution F N u ^ 2 +
          (1 + 1 / η) * forwardResidual F N u ^ 2) := by
      refine integral_mono hY2 ((hD2.const_mul (1 + η)).add (hR2.const_mul (1 + 1 / η))) fun u => ?_
      rw [boundaryCorrectedPacket_eq_gauge F hF1 N u]
      exact sub_sq_le_weighted hη _ _
    rw [integral_add (hD2.const_mul (1 + η)) (hR2.const_mul (1 + 1 / η)),
      integral_const_mul, integral_const_mul] at h1
    have hRle := integral_sq_forwardResidual_le F N
    have hη1 : 0 ≤ 1 + 1 / η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hRle hη1]
  have hDdiv_le : (∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N < E + ε := by
    calc (∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N
        ≤ ((1 + η) * boundaryCorrectedPacketEnergy F N +
            (1 + 1 / η) * (10 * autocorr F 0)) / cutoff N :=
          div_le_div_of_nonneg_right hD_le hL0.le
      _ = (1 + η) * (boundaryCorrectedPacketEnergy F N / cutoff N) +
          (1 + 1 / η) * ((10 * autocorr F 0) / cutoff N) := by ring
      _ < E + ε := hup
  have hDdiv_ge : E - ε < (∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N := by
    have hη1 : 0 < 1 + η := by linarith
    have h2 : (boundaryCorrectedPacketEnergy F N / cutoff N) / (1 + η) -
        (1 / η) * ((10 * autocorr F 0) / cutoff N) ≤
        (∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N := by
      rw [sub_le_iff_le_add, div_le_iff₀ hη1]
      have hdiv := div_le_div_of_nonneg_right hY_le hL0.le
      have h3 : (((1 + η) * ∫ u, chebyshevGaugeConvolution F N u ^ 2) +
          (1 + 1 / η) * (10 * autocorr F 0)) / cutoff N =
          ((∫ u, chebyshevGaugeConvolution F N u ^ 2) / cutoff N +
            (1 / η) * ((10 * autocorr F 0) / cutoff N)) * (1 + η) := by
        field_simp; ring
      linarith
    exact hlo.trans_le h2
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ## Asymptotic law for the finite-cutoff packet energy including the endpoint term -/

/-- **Asymptotic sandwich of the finite-cutoff packet energy including `Ẽ(cutoff N)²`.**
Under RH, for every `C²` compactly supported source `F`, every `η > 0`, and every `ε > 0`,
eventually as `N → ∞`:
`E(F) + (1 + η)⁻¹ Ẽ(L)² h_F(0) / L − ε ≤ packetEnergy F N / L ≤ E(F) + (1 + η) Ẽ(L)² h_F(0) / L + ε`. -/
theorem eventually_packetEnergy_div_cutoff_bounds (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      criticalPacketEnergy F +
          (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / ((1 + η) * cutoff N) - ε ≤
        packetEnergy F N / cutoff N ∧
      packetEnergy F N / cutoff N ≤
        criticalPacketEnergy F +
          (1 + η) * (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N + ε := by
  have hF1 : ContDiff ℝ 1 (F : ℝ → ℝ) := hF.of_le (by norm_num)
  obtain ⟨w, hw0, hwf⟩ := F.hasCompactSupport.exists_pos_le_norm
  have hw : ∀ v : ℝ, w < |v| → F v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hbdry := tendsto_boundary_layer_energy_div_cutoff hRH F hF1 hw0.le hw
  have hbulk := tendsto_stationary_bulk_energy_div_cutoff hRH F hF hw0.le hw
  have horig := tendsto_origin_zone_energy_div_cutoff F hF1 hw0.le hw
  have herr_up : Tendsto (fun N : ℕ =>
      (1 + 1 / η) *
        ((∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) / cutoff N) +
      (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) / cutoff N)
      atTop (𝓝 0) := by
    simpa using (hbdry.const_mul (1 + 1 / η)).add horig
  have herr_lo : Tendsto (fun N : ℕ =>
      (1 / η) *
        ((∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) / cutoff N))
      atTop (𝓝 0) := by
    simpa using hbdry.const_mul (1 / η)
  filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (max (2 * w) 1)),
    hbulk.eventually (Ioo_mem_nhds (by linarith : criticalPacketEnergy F - ε / 2 < criticalPacketEnergy F)
      (by linarith : criticalPacketEnergy F < criticalPacketEnergy F + ε / 2)),
    herr_up.eventually (gt_mem_nhds (half_pos hε)),
    herr_lo.eventually (gt_mem_nhds (half_pos hε))] with N hL hbulkN hupN hloN
  have hLw : 2 * w ≤ cutoff N := (le_max_left _ _).trans hL
  have hL0 : 0 < cutoff N := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
  have h3z := packetEnergy_eq_three_zones F hw0.le hw hLw
  have horig_eq : (∫ u in (-w)..w, signedSource F N u ^ 2) =
      ∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with u hu
    rw [uIoc_of_le (by linarith)] at hu
    have hnot : u ∉ Icc (-cutoff N - w) (-cutoff N + w) := by
      simp only [mem_Icc, not_and_or, not_le]
      exact Or.inr (lt_of_le_of_lt (by linarith) hu.1)
    rw [signedSource_eq_boundaryCorrectedPacket_of_notMem F hw N hnot]
  have horig_nn : 0 ≤ (∫ u in (-w)..w, signedSource F N u ^ 2) / cutoff N :=
    div_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _) hL0.le
  constructor
  · have hlo_bdry := div_le_div_of_nonneg_right
      (le_integral_signedSource_sq_boundary F hw0.le hw N hη) hL0.le
    have hdecomp : packetEnergy F N / cutoff N =
        (∫ u in (-cutoff N - w)..(-cutoff N + w), signedSource F N u ^ 2) / cutoff N +
          (∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2) / cutoff N +
          (∫ u in (-w)..w, signedSource F N u ^ 2) / cutoff N := by
      rw [h3z]; ring
    have hdiv_eq : (normalizedLogError (cutoff N) ^ 2 * autocorr F 0 / (1 + η) -
        1 / η * ∫ u in (-cutoff N - w)..(-cutoff N + w), boundaryCorrectedPacket F N u ^ 2) /
        cutoff N =
        (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / ((1 + η) * cutoff N) -
          (1 / η) * ((∫ u in (-cutoff N - w)..(-cutoff N + w),
            boundaryCorrectedPacket F N u ^ 2) / cutoff N) := by
      field_simp
    rw [hdiv_eq] at hlo_bdry
    linarith [hbulkN.1, hloN, horig_nn, hlo_bdry, hdecomp]
  · have hup_bdry := div_le_div_of_nonneg_right
      (integral_signedSource_sq_boundary_le F hw0.le hw N hη) hL0.le
    have hdecomp : packetEnergy F N / cutoff N =
        (∫ u in (-cutoff N - w)..(-cutoff N + w), signedSource F N u ^ 2) / cutoff N +
          (∫ τ in w..(cutoff N - w), stationaryPacket F τ ^ 2) / cutoff N +
          (∫ u in (-w)..w, boundaryCorrectedPacket F N u ^ 2) / cutoff N := by
      rw [h3z, horig_eq]; ring
    have hdiv_eq : ((1 + η) * (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) +
        (1 + 1 / η) * ∫ u in (-cutoff N - w)..(-cutoff N + w),
          boundaryCorrectedPacket F N u ^ 2) / cutoff N =
        (1 + η) * (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N +
          (1 + 1 / η) * ((∫ u in (-cutoff N - w)..(-cutoff N + w),
            boundaryCorrectedPacket F N u ^ 2) / cutoff N) := by
      ring
    rw [hdiv_eq] at hup_bdry
    linarith [hbulkN.2, hupN, hup_bdry, hdecomp]

/-- **Universal asymptotic lower bound on `packetEnergy F N / cutoff N`.** Under RH, for every `C²`
compactly supported source `F` and every `ε > 0`, eventually
`criticalPacketEnergy F − ε ≤ packetEnergy F N / cutoff N`. -/
theorem eventually_packetEnergy_div_cutoff_ge (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      criticalPacketEnergy F - ε ≤ packetEnergy F N / cutoff N := by
  filter_upwards [eventually_packetEnergy_div_cutoff_bounds hRH F hF zero_lt_one hε] with N hN
  have hnn : 0 ≤ (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / ((1 + 1) * cutoff N) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (autocorr_zero_nonneg F))
      (mul_nonneg (by norm_num) (cutoff_nonneg N))
  linarith [hN.1]

/-- **Exact convergence criterion for the unadjusted finite-cutoff packet energy.**
Under RH, along any filter `l ≤ atTop` on `ℕ`, `packetEnergy F N / cutoff N` converges to
`criticalPacketEnergy F` if and only if the normalized endpoint jump energy
`Ẽ(cutoff N)² * autocorr F 0 / cutoff N` converges to `0`. -/
theorem tendsto_packetEnergy_div_cutoff_iff (hRH : RiemannHypothesis)
    (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) {l : Filter ℕ} (hl : l ≤ atTop) :
    Tendsto (fun N : ℕ => packetEnergy F N / cutoff N) l (𝓝 (criticalPacketEnergy F)) ↔
      Tendsto (fun N : ℕ => (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N)
        l (𝓝 0) := by
  constructor
  · intro hP
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev1 := (eventually_packetEnergy_div_cutoff_bounds hRH F hF zero_lt_one (by linarith : 0 < ε / 4)).filter_mono hl
    have hev2 := (Metric.tendsto_nhds.mp hP) (ε / 4) (by linarith)
    filter_upwards [hev1, hev2] with N hN1 hN2
    rw [Real.dist_eq, abs_lt] at hN2
    have hnn : 0 ≤ (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N :=
      div_nonneg (mul_nonneg (sq_nonneg _) (autocorr_zero_nonneg F)) (cutoff_nonneg N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hhalf : (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / ((1 + 1) * cutoff N) =
        ((normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N) / 2 := by ring
    linarith [hN1.1, hN2.2, hhalf]
  · intro hB
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev1 := (eventually_packetEnergy_div_cutoff_bounds hRH F hF zero_lt_one (half_pos hε)).filter_mono hl
    have hev2 := (Metric.tendsto_nhds.mp hB) (ε / 4) (by linarith)
    filter_upwards [hev1, hev2] with N hN1 hN2
    have hnn : 0 ≤ (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N :=
      div_nonneg (mul_nonneg (sq_nonneg _) (autocorr_zero_nonneg F)) (cutoff_nonneg N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hN2
    have hhalf : 0 ≤ (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / ((1 + 1) * cutoff N) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (autocorr_zero_nonneg F))
        (mul_nonneg (by norm_num) (cutoff_nonneg N))
    have htwo : (1 + 1) * (normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N =
        2 * ((normalizedLogError (cutoff N) ^ 2 * autocorr F 0) / cutoff N) := by ring
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hN1.1, hN1.2, hN2, hhalf, htwo]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
