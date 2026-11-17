import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheHeatedZeroPairingOfTwoProfilesIsWeilsForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The prime side beyond the wall is the defect of the translated state

Let `F` be the critical state, `a` the alias coefficient, `F⁺` the profile beyond the wall, `W`
Weil's bare form and `E = W + a ⟨·, ·⟩₈` the full form, `⟨F, G⟩₈ = ∫ F G e^{−8u}`. For `k ≥ 0` the
translate `τ_k F(u) = F(u + k)` lies in the energy domain, and against every profile `G` of the domain

  `W(τ_k F, G) = a (∫_0^k F⁺(x) G(x − k) dx − ∫ e^{−8u} F(u) G(u − k) du)`,
  `E(τ_k F, G) = a (∫_0^k F⁺(x) G(x − k) dx + (e^{8k} − 1) ∫ e^{−8u} F(u) G(u − k) du)`.

The translated state fails the weak equation by the prime side on the collar `−k < u < 0` and by the
confinement left of it. For a profile carried by the collar, `E(τ_k F, G) = a ∫_0^k F⁺(x) G(x − k) dx`:
on `(0, k)` the prime side is the functional `E(τ_k F, ·)`.

* **Wall law** (`criticalState_beyondWallPairing_translate`). For `G = F` the left side vanishes, so
  `∫_0^k F⁺(x) F(x − k) dx = −(1 − e^{−8k}) ∫ F(u) F(u + k) e^{−8u} du`:
  the prime side against the translated state is the weighted autocorrelation of the state. No prime
  sum remains.
* **Boundary value** (`criticalState_tendsto_beyondWallPairing_div`).
  `k⁻¹ ∫_0^k F⁺(x) F(x − k) dx → −8 ∫ F² e^{−8u}` as `k → 0⁺`: across the wall the prime side is
  anticorrelated with the state, at the rate of the confinement.
* **Uncertainty at the wall** (`criticalState_wall_uncertainty`).
  `((1 − e^{−8k}) ∫ F(u) F(u + k) e^{−8u} du)² ≤ ∫_0^k |F⁺|² · ∫_{−k}^0 F²`; in particular the prime
  side is not almost everywhere zero on `(0, k)` for small `k`
  (`criticalState_eventually_integral_sq_beyondWallProfile_pos`).
* **Size on the collar** (`criticalState_norm_sq_beyondWallPairing_collar_le`). For `G` carried by
  `[−k, 0)`, `a |∫_0^k F⁺(x) G(x − k) dx|² ≤ (e^{8k} − 1) ∫ F² e^{−8u} · E(G)`: Cauchy–Schwarz for the
  nonnegative form `E` and `E(τ_k F) = a (e^{8k} − 1) ∫ F² e^{−8u}`.

Mechanism. The heated zero series `Σ_z L F(z) e^{εz² − zT} = a (k_ε * F⁺ − k_ε * (e^{−8u} F))(T)` is
integrated against `G(T − k)`. The zero side is `Σ_z L(τ_k F)(z) L G(−z) e^{εz²}`, which tends to
`W(τ_k F, G)` for two profiles of the domain. On the other side each term is a tilted heat average of
the correlation of two square-integrable profiles, with limit the pairing at lag zero; for a test
reaching beyond the wall the pairing with `F⁺` no longer vanishes.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Two-sided tests against the heated state and the heated prime side -/

/-- Two profiles in half the weight of the confinement multiply to the confinement pairing. -/
theorem integral_confinedHalf_mul_confinedHalf (F G : ℝ → ℝ) :
    (∫ T : ℝ, confinedHalf G T * confinedHalf F T) = statePairing F (cx G) := by
  unfold statePairing
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show ((Real.exp (-(4 * u)) * G u : ℝ) : ℂ) * ((Real.exp (-(4 * u)) * F u : ℝ) : ℂ) =
    ((G u : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)
  have he : Real.exp (-(8 * u)) = Real.exp (-(4 * u)) * Real.exp (-(4 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  ring

/-- The damped test against the datum beyond the wall is the pairing with the prime side. -/
theorem integral_dampedProfile_mul_beyondWallDatum (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (G : ℝ → ℝ) :
    (∫ T : ℝ, dampedProfile G T * beyondWallDatum W₀ hF T) = beyondWallPairing W₀ hF (cx G) := by
  unfold beyondWallPairing
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun T => ?_)
  show ((Real.exp T * G T : ℝ) : ℂ) * Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ) T =
    Set.indicator (Ioi (0 : ℝ)) (fun x : ℝ => cx G x * beyondWallProfile W₀ hF x) T
  by_cases hT : T ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT]
    show ((Real.exp T * G T : ℝ) : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) T =
      ((G T : ℝ) : ℂ) * (Complex.exp (T : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) T)
    push_cast
    ring
  · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, mul_zero]

/-- A test with `e^{−4T} G(T)` square integrable against the heated state: as the heat is switched
off the pairing is the confinement pairing. The test need not vanish beyond the wall. -/
theorem tendsto_integral_cx_mul_heatedState_of_sq {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hGm : Measurable (confinedHalf G))
    (hG2 : Integrable fun T => ‖confinedHalf G T‖ ^ 2) :
    Tendsto (fun ε : ℝ => ∫ T : ℝ, cx G T * ((heatedState ε F T : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (statePairing F (cx G))) := by
  have h := tendsto_integral_mul_integral_tiltedHeatKernel hGm (measurable_confinedHalf hF) hG2
    (integrable_sq_confinedHalf hF) (-4)
  rw [integral_confinedHalf_mul_confinedHalf] at h
  refine h.congr fun ε => ?_
  exact (integral_congr_ae (Eventually.of_forall fun T => cx_mul_heatedState_eq F G ε T)).symm

theorem integrable_cx_mul_heatedState_of_sq {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hGm : Measurable (confinedHalf G)) (hG2 : Integrable fun T => ‖confinedHalf G T‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable fun T : ℝ => cx G T * ((heatedState ε F T : ℝ) : ℂ) := by
  refine (integrable_mul_integral_kernel hGm (measurable_confinedHalf hF) hG2
    (integrable_sq_confinedHalf hF) (continuous_tiltedHeatKernel ε (-4))
    (integrable_tiltedHeatKernel hε (-4))).congr (Eventually.of_forall fun T => ?_)
  exact (cx_mul_heatedState_eq F G ε T).symm

/-- A test with `e^{T} G(T)` square integrable against the heated prime side: as the heat is switched
off the pairing is the pairing with the profile beyond the wall. -/
theorem tendsto_integral_cx_mul_heatedBeyondWall_of_sq (W₀ : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hGm : Measurable (dampedProfile G))
    (hG2 : Integrable fun T => ‖dampedProfile G T‖ ^ 2) :
    Tendsto (fun ε : ℝ => ∫ T : ℝ, cx G T * heatedBeyondWall ε W₀ hF T) (𝓝[>] 0)
      (𝓝 (beyondWallPairing W₀ hF (cx G))) := by
  have h := tendsto_integral_mul_integral_tiltedHeatKernel hGm (measurable_beyondWallDatum W₀ hF) hG2
    (integrable_sq_beyondWallDatum W₀ hF) 1
  rw [integral_dampedProfile_mul_beyondWallDatum] at h
  refine h.congr fun ε => ?_
  exact (integral_congr_ae
    (Eventually.of_forall fun T => cx_mul_heatedBeyondWall_eq W₀ hF G ε T)).symm

theorem integrable_cx_mul_heatedBeyondWall_of_sq (W₀ : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hGm : Measurable (dampedProfile G))
    (hG2 : Integrable fun T => ‖dampedProfile G T‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun T : ℝ => cx G T * heatedBeyondWall ε W₀ hF T := by
  refine (integrable_mul_integral_kernel hGm (measurable_beyondWallDatum W₀ hF) hG2
    (integrable_sq_beyondWallDatum W₀ hF) (continuous_tiltedHeatKernel ε 1)
    (integrable_tiltedHeatKernel hε 1)).congr (Eventually.of_forall fun T => ?_)
  exact (cx_mul_heatedBeyondWall_eq W₀ hF G ε T).symm

/-! ### A profile of the domain moved towards the wall -/

theorem measurable_confinedHalf_comp_sub {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℝ) :
    Measurable (confinedHalf fun x => G (x - k)) :=
  Complex.measurable_ofReal.comp
    ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(4 * u))).mul
      (hG.meas.comp (measurable_id.sub_const k)))

theorem integrable_sq_confinedHalf_comp_sub {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (k : ℝ) : Integrable fun T => ‖confinedHalf (fun x => G (x - k)) T‖ ^ 2 := by
  have h0 := ((integrable_sq_confinedHalf hG).comp_sub_right k).const_mul (Real.exp (-(8 * k)))
  refine h0.congr (Eventually.of_forall fun T => ?_)
  show Real.exp (-(8 * k)) * ‖((Real.exp (-(4 * (T - k))) * G (T - k) : ℝ) : ℂ)‖ ^ 2 =
    ‖((Real.exp (-(4 * T)) * G (T - k) : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have he : Real.exp (-(4 * T)) = Real.exp (-(4 * k)) * Real.exp (-(4 * (T - k))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h8 : Real.exp (-(8 * k)) = Real.exp (-(4 * k)) * Real.exp (-(4 * k)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, h8]
  ring

theorem measurable_dampedProfile_comp_sub {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℝ) :
    Measurable (dampedProfile fun x => G (x - k)) :=
  Complex.measurable_ofReal.comp
    (Real.measurable_exp.mul (hG.meas.comp (measurable_id.sub_const k)))

theorem integrable_sq_dampedProfile_comp_sub {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (k : ℝ) : Integrable fun T => ‖dampedProfile (fun x => G (x - k)) T‖ ^ 2 := by
  have h0 := ((integrable_sq_dampedProfile hG).comp_sub_right k).const_mul (Real.exp (2 * k))
  refine h0.congr (Eventually.of_forall fun T => ?_)
  show Real.exp (2 * k) * ‖((Real.exp (T - k) * G (T - k) : ℝ) : ℂ)‖ ^ 2 =
    ‖((Real.exp T * G (T - k) : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have he : Real.exp T = Real.exp k * Real.exp (T - k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (2 * k) = Real.exp k * Real.exp k := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, h2]
  ring

/-! ### The heated zero series against a translated test -/

theorem stateHeatSymbol_add (ε T k : ℝ) (z : ℂ) :
    stateHeatSymbol ε (T + k) z = stateHeatSymbol ε k z * Complex.exp (-z * (T : ℂ)) := by
  unfold stateHeatSymbol
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cx_comp_sub_add (G : ℝ → ℝ) (k T : ℝ) : cx (fun x => G (x - k)) (T + k) = cx G T := by
  show ((G (T + k - k) : ℝ) : ℂ) = ((G T : ℝ) : ℂ)
  rw [add_sub_cancel_right]

/-- The heated zero series at `T + k` integrated against a profile of the domain. -/
theorem criticalState_hasSum_zeroPairing_heated_add {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ} (hε : 0 < ε) (k : ℝ) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * stateHeatSymbol ε k (centredZero q))
      (∫ T : ℝ, cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (T + k) -
          ((heatedState ε F (T + k) : ℝ) : ℂ)))) := by
  have hzre : ∀ q : XiZeroCopy, (centredZero q).re < 1 / 2 := fun q =>
    (abs_lt.mp (abs_re_centredZero_lt q)).2
  -- each term is an integral over `T`
  have hterm : ∀ q : XiZeroCopy,
      (∫ T : ℝ, cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))) =
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          stateHeatSymbol ε k (centredZero q) := by
    intro q
    have e : (fun T : ℝ => cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε (T + k) (centredZero q))) = fun T : ℝ =>
        (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)) *
          (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) := by
      funext T
      rw [stateHeatSymbol_add]
      ring
    have hL : negativeHalfLineLaplace (cx G) (-centredZero q) =
        ∫ T : ℝ, Complex.exp (-centredZero q * (T : ℂ)) * cx G T := rfl
    rw [e, integral_const_mul, hL]
    ring
  have hint : ∀ q : XiZeroCopy, Integrable fun T : ℝ => cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q)) := by
    intro q
    refine ((integrable_cexp_neg_mul_cx hG (z := centredZero q) (by linarith [hzre q])).const_mul
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε k (centredZero q))).congr (Eventually.of_forall fun T => ?_)
    show negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q) *
        (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) =
      cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))
    rw [stateHeatSymbol_add]
    ring
  -- the terms are dominated by the heated zero series at `T = k` times an exponential moment of `G`
  have hGm := integrable_abs_mul_exp_of_domain hG (c := -(1 / 2)) (by norm_num)
  have hsumk := (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε k).summable.norm
  have key : ∀ a b g x y : ℝ, 0 ≤ a → 0 ≤ b → g * x ≤ g * y →
      g * (a * (b * x)) ≤ a * b * (g * y) := by
    intro a b g x y ha hb h
    calc g * (a * (b * x)) = a * b * (g * x) := by ring
      _ ≤ a * b * (g * y) := mul_le_mul_of_nonneg_left h (mul_nonneg ha hb)
  have hbound : ∀ q : XiZeroCopy,
      (∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖) ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)‖ *
        ∫ u : ℝ, |G u| * Real.exp (-(1 / 2) * u) := by
    intro q
    rw [← integral_const_mul]
    refine integral_mono (hint q).norm (hGm.const_mul _) fun T => ?_
    have hre : (-centredZero q * (T : ℂ)).re = -(centredZero q).re * T := by simp
    have hgx : |G T| * Real.exp (-(centredZero q).re * T) ≤
        |G T| * Real.exp (-(1 / 2) * T) := by
      rcases le_or_gt 0 T with hT | hT
      · rw [hG.support T hT, abs_zero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        nlinarith [mul_pos (sub_pos.mpr (hzre q)) (neg_pos.mpr hT)]
    show ‖((G T : ℝ) : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖ ≤
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε k (centredZero q)‖ *
        (|G T| * Real.exp (-(1 / 2) * T))
    rw [stateHeatSymbol_add, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp (-centredZero q * (T : ℂ)), hre]
    exact key _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hgx
  have hsum : Summable fun q : XiZeroCopy =>
      ∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun T => norm_nonneg _) hbound
      (hsumk.mul_right _)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ T : ℝ, (∑' q : XiZeroCopy, cx G T *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        stateHeatSymbol ε (T + k) (centredZero q))) =
      cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (T + k) -
          ((heatedState ε F (T + k) : ℝ) : ℂ))) := by
    intro T
    rw [tsum_mul_left,
      (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε (T + k)).tsum_eq]
  simp only [hterm, htsum] at h
  exact h

/-- **The heated zero pairing against a translated test.** For the critical state, a profile `G` of
the domain, `ε > 0` and real `k`:
`Σ_z L F(z) L G(−z) e^{εz² − zk} = a ∫ G(T − k) (k_ε * F⁺ − k_ε * (e^{−8u} F))(T) dT`. -/
theorem criticalState_hasSum_zeroPairing_heated_translate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ} (hε : 0 < ε) (k : ℝ) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * stateHeatSymbol ε k (centredZero q))
      (∫ T : ℝ, cx (fun x => G (x - k)) T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
          ((heatedState ε F T : ℝ) : ℂ)))) := by
  have h := criticalState_hasSum_zeroPairing_heated_add hW hthreshold hF hG hε k
  have e : (∫ T : ℝ, cx G T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (T + k) -
          ((heatedState ε F (T + k) : ℝ) : ℂ)))) =
      ∫ T : ℝ, cx (fun x => G (x - k)) T * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
          ((heatedState ε F T : ℝ) : ℂ))) := by
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun T => ?_))
      (integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun T : ℝ => cx (fun x => G (x - k)) T * ((criticalAliasCoefficient W₀ : ℂ) *
          (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
            ((heatedState ε F T : ℝ) : ℂ)))) k)
    show cx G T * _ = cx (fun x => G (x - k)) (T + k) * _
    rw [cx_comp_sub_add]
  rw [e] at h
  exact h

/-! ### Weil's form and the full form at the translated state -/

/-- **Weil's form at the translated state.** For the critical state `F`, `k ≥ 0` and every profile
`G` of the energy domain:
`W(τ_k F, G) = a (∫_{x>0} F⁺(x) G(x − k) dx − ∫ e^{−8u} F(u) G(u − k) du)`. -/
theorem criticalState_bareMixedEnergy_translate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {k : ℝ} (hk : 0 ≤ k) :
    ((bareMixedEnergy (fun u => F (u + k)) G : ℝ) : ℂ) =
      (criticalAliasCoefficient W₀ : ℂ) *
        (beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (cx fun x => G (x - k)) -
          statePairing F (cx fun x => G (x - k))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc8 := measurable_confinedHalf_comp_sub hG k
  have hc2 := integrable_sq_confinedHalf_comp_sub hG k
  have hd8 := measurable_dampedProfile_comp_sub hG k
  have hd2 := integrable_sq_dampedProfile_comp_sub hG k
  have h1 := tendsto_integral_cx_mul_heatedState_of_sq hd hc8 hc2
  have h2 := tendsto_integral_cx_mul_heatedBeyondWall_of_sq W₀ hd hd8 hd2
  have h3 := (h2.sub h1).const_mul (criticalAliasCoefficient W₀ : ℂ)
  have h4 := tendsto_heatedZeroPairing (hd.causalTranslate hk) hG
  refine tendsto_nhds_unique h4 (h3.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  -- the zero values of the translate carry the factor `e^{−zk}`
  have hterm : ∀ q : XiZeroCopy,
      negativeHalfLineLaplace (cx fun u => F (u + k)) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) =
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          stateHeatSymbol ε k (centredZero q) := by
    intro q
    have hL : negativeHalfLineLaplace (cx fun u => F (u + k)) (centredZero q) =
        Complex.exp (-(centredZero q * (k : ℂ))) *
          negativeHalfLineLaplace (cx F) (centredZero q) :=
      laplace_shiftProfile F k (centredZero q)
    have hS : stateHeatSymbol ε k (centredZero q) =
        Complex.exp ((ε : ℂ) * centredZero q ^ 2) *
          Complex.exp (-(centredZero q * (k : ℂ))) := by
      unfold stateHeatSymbol
      rw [sub_eq_add_neg, Complex.exp_add]
    rw [hL, hS]
    ring
  rw [tsum_congr hterm,
    (criticalState_hasSum_zeroPairing_heated_translate hW hthreshold hF hG hε k).tsum_eq,
    ← integral_sub (integrable_cx_mul_heatedBeyondWall_of_sq W₀ hd hd8 hd2 hε)
      (integrable_cx_mul_heatedState_of_sq hd hc8 hc2 hε), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun T => ?_)
  show (criticalAliasCoefficient W₀ : ℂ) *
      (cx (fun x => G (x - k)) T * heatedBeyondWall ε W₀ hd T -
        cx (fun x => G (x - k)) T * ((heatedState ε F T : ℝ) : ℂ)) =
    cx (fun x => G (x - k)) T * ((criticalAliasCoefficient W₀ : ℂ) *
      (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)))
  ring

/-- The confinement pairing of a translate with a profile carried by `u < 0`:
`∫_{u<0} F(u + k) G(u) e^{−8u} du = e^{8k} ∫ G(u − k) e^{−8u} F(u) du`. -/
theorem integral_translate_mul_exp_eq {F G : ℝ → ℝ} (hG : ∀ u, 0 ≤ u → G u = 0) (k : ℝ) :
    ((∫ u in Iio (0 : ℝ), F (u + k) * G u * Real.exp (-(8 * u)) : ℝ) : ℂ) =
      ((Real.exp (8 * k) : ℝ) : ℂ) * statePairing F (cx fun x => G (x - k)) := by
  have h1 : (∫ u in Iio (0 : ℝ), F (u + k) * G u * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F (u + k) * G u * Real.exp (-(8 * u)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hG u (not_lt.mp hu), mul_zero, zero_mul]
  have h2 : statePairing F (cx fun x => G (x - k)) =
      ((∫ u : ℝ, G (u - k) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ) := by
    have hcast : (∫ u : ℝ, ((G (u - k) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ)) =
        ((∫ u : ℝ, G (u - k) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ) := integral_ofReal
    unfold statePairing
    rw [← hcast]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((G (u - k) : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) =
      ((G (u - k) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ)
    push_cast
    ring
  have h3 : (∫ u : ℝ, F (u + k) * G u * Real.exp (-(8 * u))) =
      Real.exp (8 * k) * ∫ u : ℝ, G (u - k) * (Real.exp (-(8 * u)) * F u) := by
    rw [← integral_const_mul]
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun u => ?_))
      (integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun u : ℝ => Real.exp (8 * k) * (G (u - k) * (Real.exp (-(8 * u)) * F u))) k)
    show F (u + k) * G u * Real.exp (-(8 * u)) =
      Real.exp (8 * k) * (G (u + k - k) * (Real.exp (-(8 * (u + k))) * F (u + k)))
    have he : Real.exp (-(8 * u)) = Real.exp (8 * k) * Real.exp (-(8 * (u + k))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [add_sub_cancel_right, he]
    ring
  rw [h1, h3, h2, Complex.ofReal_mul]

/-- **The full form at the translated state.** For the critical state `F`, `k ≥ 0` and every
profile `G` of the energy domain:
`E(τ_k F, G) = a (∫_{x>0} F⁺(x) G(x − k) dx + (e^{8k} − 1) ∫ e^{−8u} F(u) G(u − k) du)`. -/
theorem criticalState_mixedEnergy_translate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {k : ℝ} (hk : 0 ≤ k) :
    ((criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) G : ℝ) : ℂ) =
      (criticalAliasCoefficient W₀ : ℂ) *
        (beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (cx fun x => G (x - k)) +
          ((Real.exp (8 * k) - 1 : ℝ) : ℂ) * statePairing F (cx fun x => G (x - k))) := by
  rw [criticalHalfLineMixedEnergy_eq_bare_add, Complex.ofReal_add, Complex.ofReal_mul,
    criticalState_bareMixedEnergy_translate hW hthreshold hF hG hk,
    integral_translate_mul_exp_eq hG.support k, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-! ### The wall law -/

theorem exponentialPair_translate_eq {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (k : ℝ) :
    (∫ u in Iio (0 : ℝ), F (u + k) * F u * Real.exp (-(8 * u))) =
      criticalHalfLineExponentialPair F (fun u => F (u + k)) := by
  unfold criticalHalfLineExponentialPair
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [hF u (not_lt.mp hu), mul_zero, zero_mul]]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show F (u + k) * F u * Real.exp (-(8 * u)) = F u * F (u + k) * Real.exp (-(8 * u))
  ring

/-- **The wall law.** For the critical state `F` and `k ≥ 0`:
`∫_{x>0} F⁺(x) F(x − k) dx = −(1 − e^{−8k}) ∫ F(u) F(u + k) e^{−8u} du`. The translate is a profile
of the domain, so the state is orthogonal to it for the full form. -/
theorem criticalState_beyondWallPairing_translate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {k : ℝ} (hk : 0 ≤ k) :
    beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (cx fun x => F (x - k)) =
      ((-((1 - Real.exp (-(8 * k))) *
        criticalHalfLineExponentialPair F (fun u => F (u + k))) : ℝ) : ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hdk := hd.causalTranslate hk
  have ha := criticalAliasCoefficient_positive hW
  have hzero : criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) F = 0 := by
    rw [criticalHalfLineMixedEnergy_symm W₀ hdk hd]
    exact criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hdk
  have hm := criticalState_mixedEnergy_translate hW hthreshold hF hd hk
  rw [hzero, Complex.ofReal_zero] at hm
  have hs := integral_translate_mul_exp_eq (F := F) hd.support k
  rw [exponentialPair_translate_eq hd.support k] at hs
  have ha' : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb : beyondWallPairing W₀ hd (cx fun x => F (x - k)) +
      ((Real.exp (8 * k) - 1 : ℝ) : ℂ) * statePairing F (cx fun x => F (x - k)) = 0 := by
    rcases mul_eq_zero.mp hm.symm with h | h
    · exact absurd h ha'
    · exact h
  have he : Real.exp (-(8 * k)) * Real.exp (8 * k) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsp : statePairing F (cx fun x => F (x - k)) =
      ((Real.exp (-(8 * k)) *
        criticalHalfLineExponentialPair F (fun u => F (u + k)) : ℝ) : ℂ) := by
    have h1 : ((Real.exp (-(8 * k)) : ℝ) : ℂ) * ((Real.exp (8 * k) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, he, Complex.ofReal_one]
    rw [Complex.ofReal_mul, hs, ← mul_assoc, h1, one_mul]
  have hfin : beyondWallPairing W₀ hd (cx fun x => F (x - k)) =
      -(((Real.exp (8 * k) - 1 : ℝ) : ℂ) * statePairing F (cx fun x => F (x - k))) :=
    eq_neg_of_add_eq_zero_left hb
  rw [hfin, hsp, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
  congr 1
  linear_combination (-(criticalHalfLineExponentialPair F fun u => F (u + k))) * he

/-- The weighted autocorrelation of a profile of the domain is continuous in the lag. -/
theorem continuous_exponentialPair_translate {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Continuous fun k : ℝ => criticalHalfLineExponentialPair F (fun u => F (u + k)) := by
  have hC := continuous_profileCorrelation (measurable_confinedHalf hF) (measurable_confinedHalf hF)
    (integrable_sq_confinedHalf hF) (integrable_sq_confinedHalf hF)
  have hE : Continuous fun k : ℝ => ((Real.exp (4 * k) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  refine (Complex.continuous_re.comp (hE.mul hC)).congr fun k => ?_
  have hk : ((Real.exp (4 * k) : ℝ) : ℂ) * profileCorrelation (confinedHalf F) (confinedHalf F) k =
      ((criticalHalfLineExponentialPair F (fun u => F (u + k)) : ℝ) : ℂ) := by
    have hcast : (∫ u : ℝ, ((F u * F (u + k) * Real.exp (-(8 * u)) : ℝ) : ℂ)) =
        ((∫ u : ℝ, F u * F (u + k) * Real.exp (-(8 * u)) : ℝ) : ℂ) := integral_ofReal
    unfold profileCorrelation criticalHalfLineExponentialPair
    show ((Real.exp (4 * k) : ℝ) : ℂ) * (∫ T : ℝ, confinedHalf F T * confinedHalf F (T + k)) =
      ((∫ u : ℝ, F u * F (u + k) * Real.exp (-(8 * u)) : ℝ) : ℂ)
    rw [← integral_const_mul, ← hcast]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((Real.exp (4 * k) : ℝ) : ℂ) * (((Real.exp (-(4 * u)) * F u : ℝ) : ℂ) *
        ((Real.exp (-(4 * (u + k))) * F (u + k) : ℝ) : ℂ)) =
      ((F u * F (u + k) * Real.exp (-(8 * u)) : ℝ) : ℂ)
    have he : Real.exp (-(8 * u)) =
        Real.exp (4 * k) * (Real.exp (-(4 * u)) * Real.exp (-(4 * (u + k)))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    push_cast
    ring
  show (((Real.exp (4 * k) : ℝ) : ℂ) *
    profileCorrelation (confinedHalf F) (confinedHalf F) k).re = _
  rw [hk, Complex.ofReal_re]

/-- **The boundary value of the wall law.** As `k → 0⁺`,
`k⁻¹ ∫_{x>0} F⁺(x) F(x − k) dx → −8 ∫ F² e^{−8u}`. -/
theorem criticalState_tendsto_beyondWallPairing_div {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun k : ℝ => beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF)
        (cx fun x => F (x - k)) / (k : ℂ)) (𝓝[>] 0)
      (𝓝 ((-(8 * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hslope : Tendsto (fun k : ℝ => (1 - Real.exp (-(8 * k))) / k) (𝓝[>] 0) (𝓝 8) := by
    have hd0 : HasDerivAt (fun k : ℝ => 1 - Real.exp (-(8 * k))) 8 0 := by
      have h1 : HasDerivAt (fun k : ℝ => -(8 * k)) (-(8 * 1)) 0 :=
        ((hasDerivAt_id' (0 : ℝ)).const_mul 8).neg
      have h2 := (h1.exp).const_sub 1
      have h8 : -(Real.exp (-(8 * (0 : ℝ))) * -(8 * 1)) = 8 := by norm_num
      rw [h8] at h2
      exact h2
    refine hd0.tendsto_slope_zero_right.congr fun k => ?_
    simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hA : Tendsto (fun k : ℝ => criticalHalfLineExponentialPair F (fun u => F (u + k)))
      (𝓝[>] 0) (𝓝 (criticalHalfLineExponentialPair F (fun u => F (u + 0)))) :=
    ((continuous_exponentialPair_translate hd).tendsto 0).mono_left nhdsWithin_le_nhds
  have e0 : criticalHalfLineExponentialPair F (fun u => F (u + 0)) =
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    simp only [add_zero]
    exact criticalHalfLineExponentialPair_self F
  rw [e0] at hA
  have h := (Complex.continuous_ofReal.tendsto _).comp ((hslope.mul hA).neg)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [criticalState_beyondWallPairing_translate hW hthreshold hF (le_of_lt hk)]
  show ((-((1 - Real.exp (-(8 * k))) / k *
      criticalHalfLineExponentialPair F (fun u => F (u + k))) : ℝ) : ℂ) = _
  push_cast
  ring

/-! ### The size of the prime side at the wall -/

/-- The profile beyond the wall is square integrable on every bounded interval. -/
theorem integrableOn_sq_beyondWallProfile (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (k : ℝ) :
    IntegrableOn (fun x => ‖beyondWallProfile W₀ hF x‖ ^ 2) (Ioo (0 : ℝ) k) := by
  have h0 : IntegrableOn (fun x => Real.exp (2 * k) * ‖beyondWallDatum W₀ hF x‖ ^ 2)
      (Ioo (0 : ℝ) k) :=
    ((integrable_sq_beyondWallDatum W₀ hF).const_mul _).integrableOn
  have hm : AEStronglyMeasurable (beyondWallProfile W₀ hF) (volume.restrict (Ioo (0 : ℝ) k)) :=
    (aestronglyMeasurable_beyondWallProfile W₀ hF).mono_measure
      (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
  refine Integrable.mono' h0 (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : x ∈ Ioi (0 : ℝ) := hx.1
  have hP : ‖beyondWallProfile W₀ hF x‖ = Real.exp x * ‖beyondWallDatum W₀ hF x‖ := by
    show ‖Complex.exp (x : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) x‖ =
      Real.exp x * ‖Set.indicator (Ioi (0 : ℝ)) (unitLeftDatum W₀ hF : ℝ → ℂ) x‖
    rw [Set.indicator_of_mem hx0, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  have h2 : Real.exp x ^ 2 ≤ Real.exp (2 * k) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    linarith [hx.2]
  rw [Real.norm_of_nonneg (sq_nonneg _), hP, mul_pow]
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- **Uncertainty at the wall.** For the critical state and `k ≥ 0`:
`((1 − e^{−8k}) ∫ F(u) F(u + k) e^{−8u} du)² ≤ ∫_0^k |F⁺|² · ∫_{−k}^0 F²`. The wall law and
Cauchy–Schwarz on the collar. -/
theorem criticalState_wall_uncertainty {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {k : ℝ} (hk : 0 ≤ k) :
    ((1 - Real.exp (-(8 * k))) * criticalHalfLineExponentialPair F (fun u => F (u + k))) ^ 2 ≤
      (∫ x in Ioo (0 : ℝ) k,
          ‖beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x‖ ^ 2) *
        ∫ u in Ioo (-k) 0, F u ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hlaw := criticalState_beyondWallPairing_translate hW hthreshold hF hk
  -- the pairing only sees the collar `0 < x < k`
  have hcut : beyondWallPairing W₀ hd (cx fun x => F (x - k)) =
      ∫ x in Ioo (0 : ℝ) k, cx (fun x => F (x - k)) x * beyondWallProfile W₀ hd x := by
    unfold beyondWallPairing
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
      fun x hx => ?_
    have hxk : k ≤ x := by
      by_contra h
      exact hx.2 ⟨hx.1, not_le.mp h⟩
    show ((F (x - k) : ℝ) : ℂ) * beyondWallProfile W₀ hd x = 0
    rw [hd.support (x - k) (by linarith), Complex.ofReal_zero, zero_mul]
  have hfm : AEStronglyMeasurable (fun x : ℝ => ‖F (x - k)‖) (volume.restrict (Ioo (0 : ℝ) k)) :=
    (hd.meas.comp (measurable_id.sub_const k)).norm.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x : ℝ => ‖beyondWallProfile W₀ hd x‖)
      (volume.restrict (Ioo (0 : ℝ) k)) :=
    ((aestronglyMeasurable_beyondWallProfile W₀ hd).mono_measure
      (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)).norm
  have hf2 : Integrable (fun x : ℝ => ‖F (x - k)‖ ^ 2) (volume.restrict (Ioo (0 : ℝ) k)) := by
    have h0 : Integrable fun x : ℝ => F (x - k) ^ 2 := hd.sq.comp_sub_right k
    refine (h0.congr (Eventually.of_forall fun x => ?_)).integrableOn
    show F (x - k) ^ 2 = ‖F (x - k)‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hcs := sq_integral_mul_le hfm hgm hf2 (integrableOn_sq_beyondWallProfile W₀ hd k)
  have hnorm : ‖beyondWallPairing W₀ hd (cx fun x => F (x - k))‖ ≤
      ∫ x in Ioo (0 : ℝ) k, ‖F (x - k)‖ * ‖beyondWallProfile W₀ hd x‖ := by
    rw [hcut]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖((F (x - k) : ℝ) : ℂ) * beyondWallProfile W₀ hd x‖ =
      ‖F (x - k)‖ * ‖beyondWallProfile W₀ hd x‖
    rw [norm_mul, Complex.norm_real]
  have hsq : ‖beyondWallPairing W₀ hd (cx fun x => F (x - k))‖ ^ 2 =
      ((1 - Real.exp (-(8 * k))) *
        criticalHalfLineExponentialPair F (fun u => F (u + k))) ^ 2 := by
    rw [hlaw, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
  have hF2 : (∫ x in Ioo (0 : ℝ) k, ‖F (x - k)‖ ^ 2) = ∫ u in Ioo (-k) 0, F u ^ 2 := by
    rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo,
      ← integral_sub_right_eq_self
        (fun u : ℝ => Set.indicator (Ioo (-k) 0) (fun u => F u ^ 2) u) k]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Set.indicator (Ioo (0 : ℝ) k) (fun x => ‖F (x - k)‖ ^ 2) x =
      Set.indicator (Ioo (-k) 0) (fun u => F u ^ 2) (x - k)
    by_cases hx : x ∈ Ioo (0 : ℝ) k
    · have hx' : x - k ∈ Ioo (-k) 0 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Real.norm_eq_abs, sq_abs]
    · have hx' : x - k ∉ Ioo (-k) 0 := fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  calc ((1 - Real.exp (-(8 * k))) *
        criticalHalfLineExponentialPair F (fun u => F (u + k))) ^ 2
      = ‖beyondWallPairing W₀ hd (cx fun x => F (x - k))‖ ^ 2 := hsq.symm
    _ ≤ (∫ x in Ioo (0 : ℝ) k, ‖F (x - k)‖ * ‖beyondWallProfile W₀ hd x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ x in Ioo (0 : ℝ) k, ‖F (x - k)‖ ^ 2) *
        ∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2 := hcs
    _ = _ := by rw [hF2, mul_comm]

/-- **The prime side does not vanish at the wall.** For every small `k > 0` the profile beyond the
wall has positive mass on `(0, k)`: the autocorrelation of the state is positive at small lags. -/
theorem criticalState_eventually_integral_sq_beyondWallProfile_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < ∫ x in Ioo (0 : ℝ) k,
      ‖beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hM : 0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    have hneg := criticalState_zeroNorm_limit_neg hW hF
    by_contra h
    linarith [mul_nonneg ha.le (neg_nonneg.mpr (not_lt.mp h))]
  have hA : Tendsto (fun k : ℝ => criticalHalfLineExponentialPair F (fun u => F (u + k)))
      (𝓝[>] 0) (𝓝 (criticalHalfLineExponentialPair F (fun u => F (u + 0)))) :=
    ((continuous_exponentialPair_translate hd).tendsto 0).mono_left nhdsWithin_le_nhds
  have e0 : criticalHalfLineExponentialPair F (fun u => F (u + 0)) =
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
    simp only [add_zero]
    exact criticalHalfLineExponentialPair_self F
  rw [e0] at hA
  filter_upwards [hA.eventually (lt_mem_nhds hM), self_mem_nhdsWithin] with k hpk hk
  have hk0 : (0 : ℝ) < k := hk
  have hu := criticalState_wall_uncertainty hW hthreshold hF hk0.le
  have h1 : 0 < 1 - Real.exp (-(8 * k)) := by
    have hlt : Real.exp (-(8 * k)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at hlt
    linarith
  have hpos : 0 < ((1 - Real.exp (-(8 * k))) *
      criticalHalfLineExponentialPair F (fun u => F (u + k))) ^ 2 := pow_pos (mul_pos h1 hpk) 2
  have hI1 : 0 ≤ ∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  by_contra hneg
  have hz : (∫ x in Ioo (0 : ℝ) k, ‖beyondWallProfile W₀ hd x‖ ^ 2) = 0 :=
    le_antisymm (not_lt.mp hneg) hI1
  rw [hz, zero_mul] at hu
  linarith

/-! ### The translated state as a functional on the domain -/

/-- The full energy of the translated state: `E(τ_k F) = a (e^{8k} − 1) ∫ F² e^{−8u}`. -/
theorem criticalState_fullEnergy_translate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {k : ℝ} (hk : 0 ≤ k) :
    criticalHalfLineFullEnergy W₀ (fun u => F (u + k)) =
      criticalAliasCoefficient W₀ * (Real.exp (8 * k) - 1) *
        ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalHalfLineFullEnergy_causal_ground_shear hW hthreshold hF hd hk 0
  have e : (fun u => F (u + k) + 0 * F u) = fun u => F (u + k) := by
    funext u
    rw [zero_mul, add_zero]
  rw [e, criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF, zero_add,
    criticalHalfLineExponentialPair_self] at h
  exact h

/-- **The translated state is a bounded functional for the full form.** For every profile `G` of
the domain, `E(τ_k F, G)² ≤ E(G) · a (e^{8k} − 1) ∫ F² e^{−8u}`: Cauchy–Schwarz for the nonnegative
full form. -/
theorem criticalState_sq_mixedEnergy_translate_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {k : ℝ} (hk : 0 ≤ k) :
    criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) G ^ 2 ≤
      criticalHalfLineFullEnergy W₀ G *
        (criticalAliasCoefficient W₀ * (Real.exp (8 * k) - 1) *
          ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hdk := hd.causalTranslate hk
  have hC : 0 ≤ criticalHalfLineFullEnergy W₀ (fun u => F (u + k)) :=
    criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold hdk
  have hq : ∀ t : ℝ, 0 ≤ criticalHalfLineFullEnergy W₀ G +
      2 * criticalHalfLineMixedEnergy W₀ G (fun u => F (u + k)) * t +
      criticalHalfLineFullEnergy W₀ (fun u => F (u + k)) * t ^ 2 := by
    intro t
    have h := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold
      (hG.add_const_mul hdk t)
    rw [criticalHalfLineFullEnergy_add_const_mul W₀ hG hdk t] at h
    linarith
  have h := sq_le_mul_of_quadratic_nonneg hC hq
  rw [criticalHalfLineMixedEnergy_symm W₀ hG hdk,
    criticalState_fullEnergy_translate hW hthreshold hF hk] at h
  exact h

/-- A profile carried by `[−k, 0)`, moved to `[0, k)`, does not meet the state. -/
theorem statePairing_comp_sub_eq_zero {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) {k : ℝ}
    (hGk : ∀ u, u < -k → G u = 0) : statePairing F (cx fun x => G (x - k)) = 0 := by
  unfold statePairing
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  show ((G (u - k) : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) = 0
  rcases le_or_gt 0 u with hu | hu
  · rw [hF u hu, mul_zero, Complex.ofReal_zero, mul_zero]
  · rw [hGk (u - k) (by linarith), Complex.ofReal_zero, zero_mul]

/-- **On the collar the prime side is the translated state.** For a profile `G` of the domain
carried by `[−k, 0)`: `E(τ_k F, G) = a ∫_{x>0} F⁺(x) G(x − k) dx`. -/
theorem criticalState_mixedEnergy_translate_collar {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {k : ℝ} (hk : 0 ≤ k) (hGk : ∀ u, u < -k → G u = 0) :
    ((criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) G : ℝ) : ℂ) =
      (criticalAliasCoefficient W₀ : ℂ) *
        beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (cx fun x => G (x - k)) := by
  rw [criticalState_mixedEnergy_translate hW hthreshold hF hG hk,
    statePairing_comp_sub_eq_zero (criticalHalfLineEnergyDomain_of_groundState hF).support hGk, mul_zero, add_zero]

/-- **The size of the prime side on the collar.** For a profile `G` of the domain carried by
`[−k, 0)`: `a |∫_{x>0} F⁺(x) G(x − k) dx|² ≤ (e^{8k} − 1) ∫ F² e^{−8u} · E(G)`. -/
theorem criticalState_norm_sq_beyondWallPairing_collar_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {k : ℝ} (hk : 0 ≤ k) (hGk : ∀ u, u < -k → G u = 0) :
    criticalAliasCoefficient W₀ *
        ‖beyondWallPairing W₀ (criticalHalfLineEnergyDomain_of_groundState hF) (cx fun x => G (x - k))‖ ^ 2 ≤
      (Real.exp (8 * k) - 1) * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) *
        criticalHalfLineFullEnergy W₀ G := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hm := criticalState_mixedEnergy_translate_collar hW hthreshold hF hG hk hGk
  have h1 : |criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) G| =
      criticalAliasCoefficient W₀ * ‖beyondWallPairing W₀ hd (cx fun x => G (x - k))‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ha.le]
  have hn : criticalHalfLineMixedEnergy W₀ (fun u => F (u + k)) G ^ 2 =
      criticalAliasCoefficient W₀ *
        (criticalAliasCoefficient W₀ * ‖beyondWallPairing W₀ hd (cx fun x => G (x - k))‖ ^ 2) := by
    rw [← sq_abs, h1]
    ring
  have hb := criticalState_sq_mixedEnergy_translate_le hW hthreshold hF hG hk
  rw [hn] at hb
  refine le_of_mul_le_mul_left (hb.trans (le_of_eq ?_)) ha
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
