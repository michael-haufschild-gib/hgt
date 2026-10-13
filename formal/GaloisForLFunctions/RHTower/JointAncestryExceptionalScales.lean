import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel
import GaloisForLFunctions.RHTower.WeilLagFunctionExponentialExceptionCriterion

/-!
# Route JAS tolerates exponentially rare exceptional scales

**Theorem** (`riemannHypothesis_iff_exists_jasIntervalProductPositiveExcept_one`). RH holds iff for
some `X`, some `κ > 0` and some measurable set `S` of log-scales with `∫_S e^{κu} du < ∞`, the
level-one constant-vector JAS product tests are positive on the primes of every interval `(y, y + L]`
with `y ≥ X + 1` and `log y ∉ S`.

So a producer for route JAS may fail on an exponentially rare set of scales `log y`.

**Proof.** The diagonal Bochner window argument is pointwise in the scale: a positive window at
scale `u` bounds `|Φ(u)|` (`exists_abs_weilLagFunctionReal_le_exp_of_windows_except`). The growth
criterion is replaced by its exceptional form (`re_le_half_add_of_weilLagFunctionReal_le_exp_except`,
from the integrated positive-part criterion). Off `S` we have `Φ ≤ M e^{aL}` and on `S` we have
`|Φ| ≤ W e^{αL}`, so the zeros lie in `Re ρ ≤ ½ + max(a, α − κ, 0)`. Since
`max(c, α − min(c, δ/4), α − κ) < α` whenever `α > c`, the window parameter `c` bounds `α`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The growth criterion off an exponentially thin set -/

theorem integral_lagPositivePart_le_exp_except {M κ a α : ℝ} (ha0 : 0 ≤ a) {S : Set ℝ}
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → weilLagFunctionReal u ≤ M * Real.exp (a * u))
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤
      max M 0 * Real.exp (a * T) * T + lagWeightTotal * Real.exp (max (α - κ) 0 * T) *
        ∫ u in S, Real.exp (κ * u) := by
  set m := max (α - κ) 0 with hm
  set ind : ℝ → ℝ := S.indicator (fun u => Real.exp (κ * u)) with hind
  have hindI : Integrable ind := (integrable_indicator_iff hS).mpr hSint
  have hW := lagWeightTotal_nonneg
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hbound : ∀ u ∈ Icc (0:ℝ) T,
      lagPositivePart u ≤ max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u := by
    intro u hu
    rw [lagPositivePart_eq_max]
    have hea : Real.exp (a * u) ≤ Real.exp (a * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 ha0)
    by_cases huS : u ∈ S
    · have h1 := hgrowth u hu.1
      have hind1 : ind u = Real.exp (κ * u) := Set.indicator_of_mem huS _
      rw [hind1]
      have h2 : Real.exp (α * u) ≤ Real.exp (m * T) * Real.exp (κ * u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : (α - κ) * u ≤ m * T :=
          calc (α - κ) * u ≤ m * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1
            _ ≤ m * T := mul_le_mul_of_nonneg_left hu.2 (le_max_right _ _)
        linarith
      have h3 : max (weilLagFunctionReal u) 0 ≤ Real.exp (α * u) * lagWeightTotal :=
        max_le ((le_abs_self _).trans h1) (mul_nonneg (Real.exp_pos _).le hW)
      have h4 : Real.exp (α * u) * lagWeightTotal ≤
          lagWeightTotal * Real.exp (m * T) * Real.exp (κ * u) :=
        calc Real.exp (α * u) * lagWeightTotal
            ≤ (Real.exp (m * T) * Real.exp (κ * u)) * lagWeightTotal :=
              mul_le_mul_of_nonneg_right h2 hW
          _ = _ := by ring
      have h5 : 0 ≤ max M 0 * Real.exp (a * T) := mul_nonneg hM0 (Real.exp_pos _).le
      linarith
    · have hind0 : ind u = 0 := Set.indicator_of_notMem huS _
      rw [hind0, mul_zero, add_zero]
      refine max_le ?_ (mul_nonneg hM0 (Real.exp_pos _).le)
      calc weilLagFunctionReal u ≤ M * Real.exp (a * u) := hM u hu.1 huS
        _ ≤ max M 0 * Real.exp (a * u) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ ≤ max M 0 * Real.exp (a * T) := mul_le_mul_of_nonneg_left hea hM0
  have hint1 : IntegrableOn lagPositivePart (Icc 0 T) :=
    integrableOn_oneSidedDensity_zero_Icc (-1) T
  have hconst : IntegrableOn (fun _ : ℝ => max M 0 * Real.exp (a * T)) (Icc (0:ℝ) T) :=
    integrableOn_const (by simp)
  have hint2 : IntegrableOn
      (fun u => max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u)
      (Icc 0 T) :=
    hconst.add (hindI.integrableOn.const_mul _)
  have hle : ∫ u in Icc (0:ℝ) T, ind u ≤ ∫ u in S, Real.exp (κ * u) := by
    rw [← integral_indicator hS]
    exact setIntegral_le_integral hindI (Filter.Eventually.of_forall fun u =>
      Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
  have hc : 0 ≤ lagWeightTotal * Real.exp (m * T) := mul_nonneg hW (Real.exp_pos _).le
  calc ∫ u in Icc (0:ℝ) T, lagPositivePart u
      ≤ ∫ u in Icc (0:ℝ) T,
          (max M 0 * Real.exp (a * T) + lagWeightTotal * Real.exp (m * T) * ind u) :=
        setIntegral_mono_on hint1 hint2 measurableSet_Icc hbound
    _ = max M 0 * Real.exp (a * T) * T +
          lagWeightTotal * Real.exp (m * T) * ∫ u in Icc (0:ℝ) T, ind u := by
        rw [integral_add hconst (hindI.integrableOn.const_mul _),
          show ∫ u in Icc (0:ℝ) T, lagWeightTotal * Real.exp (m * T) * ind u =
            lagWeightTotal * Real.exp (m * T) * ∫ u in Icc (0:ℝ) T, ind u from
            integral_const_mul _ _,
          setIntegral_const, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]
    _ ≤ max M 0 * Real.exp (a * T) * T +
          lagWeightTotal * Real.exp (m * T) * ∫ u in S, Real.exp (κ * u) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hc]

theorem exists_integral_lagPositivePart_le_exp_except_majorant {M κ a α : ℝ} (ha0 : 0 ≤ a)
    {S : Set ℝ} (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → weilLagFunctionReal u ≤ M * Real.exp (a * u))
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    {η : ℝ} (hη : max (max a (α - κ)) 0 < η) :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ C * Real.exp (η * T) := by
  have hηa : a < η := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hη
  have hηm : max (α - κ) 0 < η := by
    refine max_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hη)
      (lt_of_le_of_lt (le_max_right _ _) hη)
  have hd : 0 < η - a := by linarith
  refine ⟨max M 0 / (η - a) + lagWeightTotal * ∫ u in S, Real.exp (κ * u), fun T hT => ?_⟩
  have h1 := integral_lagPositivePart_le_exp_except ha0 hS hSint hM hgrowth hT (κ := κ)
  have hI0 : 0 ≤ ∫ u in S, Real.exp (κ * u) :=
    setIntegral_nonneg hS fun u _ => (Real.exp_pos _).le
  have hW := lagWeightTotal_nonneg
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have h2 : max M 0 * Real.exp (a * T) * T ≤ max M 0 / (η - a) * Real.exp (η * T) := by
    have hT' : T ≤ Real.exp ((η - a) * T) / (η - a) := by
      rw [le_div_iff₀ hd]
      have := Real.add_one_le_exp ((η - a) * T)
      nlinarith
    have hsplit : Real.exp (η * T) = Real.exp (a * T) * Real.exp ((η - a) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    calc max M 0 * Real.exp (a * T) * T
        ≤ max M 0 * Real.exp (a * T) * (Real.exp ((η - a) * T) / (η - a)) :=
          mul_le_mul_of_nonneg_left hT' (mul_nonneg hM0 (Real.exp_pos _).le)
      _ = max M 0 / (η - a) * Real.exp (η * T) := by rw [hsplit]; field_simp
  have h3 : Real.exp (max (α - κ) 0 * T) ≤ Real.exp (η * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hηm.le hT)
  have h4 : lagWeightTotal * Real.exp (max (α - κ) 0 * T) * ∫ u in S, Real.exp (κ * u) ≤
      lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (η * T) :=
    calc lagWeightTotal * Real.exp (max (α - κ) 0 * T) * ∫ u in S, Real.exp (κ * u)
        = lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (max (α - κ) 0 * T) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hW hI0)
  calc ∫ u in Icc (0:ℝ) T, lagPositivePart u
      ≤ max M 0 * Real.exp (a * T) * T + lagWeightTotal * Real.exp (max (α - κ) 0 * T) *
          ∫ u in S, Real.exp (κ * u) := h1
    _ ≤ max M 0 / (η - a) * Real.exp (η * T) +
          lagWeightTotal * (∫ u in S, Real.exp (κ * u)) * Real.exp (η * T) := by linarith
    _ = (max M 0 / (η - a) + lagWeightTotal * ∫ u in S, Real.exp (κ * u)) *
          Real.exp (η * T) := by ring

/-- **The growth criterion off an exponentially thin set.** If `Φ ≤ M e^{aL}` for `L ≥ 0` outside
`S` with `∫_S e^{κu} < ∞`, and `|Φ| ≤ W e^{αL}`, then `Re ρ ≤ ½ + max(a, α − κ, 0)`. -/
theorem re_le_half_add_of_weilLagFunctionReal_le_exp_except {M κ a α : ℝ} (ha0 : 0 ≤ a)
    {S : Set ℝ} (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hM : ∀ u, 0 ≤ u → u ∉ S → weilLagFunctionReal u ≤ M * Real.exp (a * u))
    (hgrowth : ∀ u, 0 ≤ u → |weilLagFunctionReal u| ≤ Real.exp (α * u) * lagWeightTotal)
    (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + max (max a (α - κ)) 0 :=
  re_le_half_add_of_lagPositivePart_integral (le_max_right _ _)
    (fun _ hη => exists_integral_lagPositivePart_le_exp_except_majorant ha0 hS hSint hM hgrowth hη) q

/-! ## Positive windows off an exceptional set of scales -/

/-- **Exponential growth from positive windows off `S`.** -/
theorem exists_abs_weilLagFunctionReal_le_exp_of_windows_except {σ α δ c : ℝ} {S : Set ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc0 : 0 < c)
    (hW : ∀ᶠ u : ℝ in atTop, u ∉ S → JasPositiveWindow σ δ c u) :
    ∃ M : ℝ, ∀ L, 0 ≤ L → L ∉ S →
      |weilLagFunctionReal L| ≤ M * Real.exp (max c (α - min c (δ / 4)) * L) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c (α - min c (δ / 4)) := ⟨_, rfl⟩
  rw [← hadef]
  have hca : c ≤ a := hadef ▸ le_max_left _ _
  have hm : α - min c (δ / 4) ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have ev4 : ∀ᶠ u : ℝ in atTop, 4 * Real.exp (-(c * u)) ≤ 1 := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(c * u))) atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith))
      refine this.congr fun u => ?_
      simp [Function.comp]
    filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with u hu
    linarith
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (hW.and (ev4.and (eventually_ge_atTop (1 : ℝ))))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * poleSharpConstant + 64 * lagWeightTotal +
      2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal + 80 * (|xiLineTwoLogDerivConstant| + 2) +
        80 * (4 / δ)) := ⟨_, rfl⟩
  have hW0 := lagWeightTotal_nonneg
  refine ⟨max K (Real.exp (|u₀| / 2) * lagWeightTotal), fun L hL hLS => ?_⟩
  rcases le_or_gt u₀ L with hLu | hLu
  · obtain ⟨hWL, hE4, hu1⟩ := hu₀ L hLu
    obtain ⟨P, hposP, hlogP, hMass⟩ := hWL hLS
    have hb := abs_weilLagFunctionReal_le_of_window hα hδ0 hu1 hE4 P hposP hlogP hMass
    have hcoh := diagCoherence_le hδ0 hδ1 hL
    have hb2 := hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcoh (Real.exp_pos _).le))
    have hw := window_bound_le_exp (α := α) (W := lagWeightTotal) (Φ0 := poleSharpConstant)
      (C := |xiLineTwoLogDerivConstant|) hδ0 hc0 hL hW0 poleSharpConstant_pos.le (abs_nonneg _)
      hca hm
    rw [← hK] at hw
    exact (hb2.trans hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
    have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have h4 : |weilLagFunctionReal L| ≤ Real.exp (|u₀| / 2) * lagWeightTotal :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hW0)
    have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
      le_trans (by positivity) (le_max_right _ _)
    calc |weilLagFunctionReal L| ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) :=
          h4.trans (le_max_right _ _)
      _ ≤ max K (Real.exp (|u₀| / 2) * lagWeightTotal) * Real.exp (a * L) :=
          le_mul_of_one_le_right h5 h3

/-- **Positive windows off `S` give the half-plane.** -/
theorem abs_re_sub_half_le_of_windows_except {σ c₀ κ : ℝ} (hκ : 0 < κ) {S : Set ℝ}
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hW : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 →
      ∀ᶠ u : ℝ in atTop, u ∉ S → JasPositiveWindow σ δ c u) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c₀ := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hstrip : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + α := fun q => by
    linarith [(abs_le.mp (hαall q)).2]
  have key : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 → α ≤ c := by
    intro δ c hδ0 hδ hc0 hc hch
    obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
      (by linarith) hc0 (hW δ c hδ0 hδ hc0 hc hch)
    have hm0 : 0 < min c (δ / 4) := lt_min hc0 (by linarith)
    have ha0 : 0 ≤ max c (α - min c (δ / 4)) := le_trans hc0.le (le_max_left _ _)
    have hg : ∀ q : XiZeroCopy,
        (q.1 : ℂ).re ≤ 1 / 2 + max (max (max c (α - min c (δ / 4))) (α - κ)) 0 := fun q =>
      re_le_half_add_of_weilLagFunctionReal_le_exp_except ha0 hS hSint
        (fun L hL hLS => (le_abs_self _).trans (hM L hL hLS))
        (fun u hu => abs_weilLagFunctionReal_le_of_strip hstrip hu) q
    have hsup := zeroReSup_le hg
    have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
    have hle : α ≤ max (max (max c (α - min c (δ / 4))) (α - κ)) 0 := by linarith
    by_contra hlt
    push Not at hlt
    have hc1 : max c (α - min c (δ / 4)) < α := max_lt hlt (by linarith)
    have hc2 : max (max c (α - min c (δ / 4))) (α - κ) < α := max_lt hc1 (by linarith)
    have hc3 : max (max (max c (α - min c (δ / 4))) (α - κ)) 0 < α := max_lt hc2 (by linarith)
    linarith
  have hfin : α ≤ max 0 c₀ := by
    have hαh : α ≤ 1 / 2 := by
      have := zeroReSup_le (fun q : XiZeroCopy => (xiZeroCopy_re_lt_one q).le)
      rw [hαdef]; linarith
    by_cases ht : 1 / 2 ≤ max 0 c₀
    · linarith
    · push Not at ht
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rcases le_or_gt (1 / 2 - max 0 c₀) ε with hε' | hε'
      · linarith
      · have h1 := le_max_left 0 c₀
        have h2 := le_max_right 0 c₀
        have h3 := min_le_left (ε / 2) (1 / 4)
        have h4 := min_le_right (ε / 2) (1 / 4)
        exact key (min (ε / 2) (1 / 4)) (max 0 c₀ + ε) (lt_min (by linarith) (by norm_num))
          (by linarith) (by linarith) (by linarith) (by linarith)
  exact (hαall q).trans hfin

/-! ## Interval positivity off an exceptional set of scales -/

/-- **Interval product positivity off a set `S` of log-scales.** The product tests with a constant
vector are positive on the primes of every interval `(y, y + L]` with `y ≥ X + 1` and `log y ∉ S`. -/
def JasIntervalProductPositiveExcept (X : ℕ) (σ : ℝ) (S : Set ℝ) : Prop :=
  ∀ y L : ℝ, (X : ℝ) + 1 ≤ y → Real.log y ∉ S → 0 ≤ L →
    JasConstProductPositiveOn (jasIntervalPrimes y L) σ

theorem eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept {X : ℕ} {σ : ℝ}
    {S : Set ℝ} (hpos : JasIntervalProductPositiveExcept X σ S) (hσ : 0 ≤ σ) {δ c : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 5 / 12) (hc0 : 0 < c) (hc : σ - 1 + δ < c) :
    ∀ᶠ u : ℝ in atTop, u ∉ S → JasPositiveWindow σ δ c u := by
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  filter_upwards [eventually_diagWindow_conditions X (σ := σ) (δ := δ) (c := c)
    (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith) hc0]
    with u hu huS
  obtain ⟨hE1, hE1', hE2, hE3, -, hu1⟩ := hu
  obtain ⟨P, hPdef, hlogP, hMass⟩ := exists_window (X := X) (c := c) hσ hδ0 (by linarith)
    (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
  refine ⟨P, ?_, hlogP, hMass⟩
  rw [hPdef]
  exact hpos _ _ hE1' (by rwa [Real.log_exp]) (Real.exp_pos _).le

/-- **Interval positivity off an exponentially thin set of scales forces the half-plane.** -/
theorem abs_re_sub_half_le_of_jasIntervalProductPositiveExcept {X : ℕ} {σ κ : ℝ} {S : Set ℝ}
    (hpos : JasIntervalProductPositiveExcept X σ S) (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (σ - 1) :=
  abs_re_sub_half_le_of_windows_except hκ hS hSint (fun _ _ hδ0 hδ hc0 hc _ =>
    eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept hpos hσ hδ0 hδ hc0 hc) q

/-- **Level-one positivity off an exponentially thin set of scales implies RH.** -/
theorem riemannHypothesis_of_jasIntervalProductPositiveExcept {X : ℕ} {σ κ : ℝ} {S : Set ℝ}
    (hpos : JasIntervalProductPositiveExcept X σ S) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hκ : 0 < κ)
    (hS : MeasurableSet S) (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasIntervalProductPositiveExcept hpos hσ0 hκ hS hSint q
  rw [max_eq_left (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ level-one interval positivity off an exponentially thin set of scales.** -/
theorem riemannHypothesis_iff_exists_jasIntervalProductPositiveExcept_one :
    RiemannHypothesis ↔ ∃ (X : ℕ) (κ : ℝ) (S : Set ℝ), 0 < κ ∧ MeasurableSet S ∧
      IntegrableOn (fun u => Real.exp (κ * u)) S ∧ JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
    exact ⟨X, 1, ∅, one_pos, MeasurableSet.empty, integrableOn_empty,
      fun y L hy _ hL => hX y L hy hL⟩
  · rintro ⟨X, κ, S, hκ, hS, hSint, hpos⟩
    exact riemannHypothesis_of_jasIntervalProductPositiveExcept hpos (by norm_num) le_rfl hκ hS
      hSint

end

end RHTower
