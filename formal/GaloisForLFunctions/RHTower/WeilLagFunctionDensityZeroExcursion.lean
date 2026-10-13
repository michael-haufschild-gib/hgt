import GaloisForLFunctions.RHTower.WeilLagFunctionFiniteMeasureExcursion
import GaloisForLFunctions.RHTower.JointAncestryAbscissaStructure

/-!
# An attained top forces lag excursions of positive density

For a configuration with summable weights `a_i` and exponents `Re w_i ≤ B`, `B > 0`, put
`Φ(t) = Re Σ_i a_i e^{t w_i}` and let `c = Σ_{w_i = B} a_i` be the total weight at the real point
`B`. For a set `E` write `J_E(η) = ∫_{E ∩ (0,∞)} e^{−ηu} du`.

**Theorem** (`re_tsum_top_le_of_lagRe_le_except`). If `Φ ≤ M` on `[0, ∞)` outside a measurable set
`E` with `η J_E(η) ≤ δ` for arbitrarily small `η > 0`, then `Re c ≤ δ Σ_i |a_i|`.

So an excursion set `E` with lower Abel density zero (`η J_E(η) → 0` along some `η → 0⁺`) forces
`Re c ≤ 0` (`re_tsum_top_nonpos_of_lagRe_le_lowerAbelDensityZero`). Sets of finite measure, sets
with `|E ∩ [0, T]| = o(T)`, and even sets with `|E ∩ [0, T]| = o(T)` only along a sequence
`T → ∞` qualify (`abelDensityZero_of_volume_ne_top`, `abelDensityZero_of_upperDensityZero`,
`lowerAbelDensityZero_of_lowerDensityZero`).

**Proof.** For real `σ > B`, `∫_0^∞ Φ(u) e^{−σu} du = Re Σ_i a_i/(σ − w_i)`. Off `E` the integrand
is at most `max(M,0) e^{−σu}`, and on `E` it is at most `W e^{−(σ−B)u}` with `W = Σ|a_i|`. Hence
`Re Σ_i a_i/(σ − w_i) ≤ max(M,0)/σ + W J_E(σ − B)`. Multiply by `σ − B` and let `σ → B⁺`. The
residue limit `(σ − B) Σ_i a_i/(σ − w_i) → c` holds by dominated convergence, because
`|σ − w_i| ≥ σ − Re w_i ≥ σ − B` (`tendsto_mul_cauchySeries`). No local finiteness and no analytic
continuation are used.

**For `ζ`** (`re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero`). If `Φ(L) ≤ M e^{aL}` for
all `L ≥ 0` outside a measurable set of Abel density zero, then an attained top `β₀` satisfies
`β₀ ≤ ½ + a`. Consequences:
* RH holds iff the zeros approach the line and some excursion set `{L ≥ 0 : Φ(L) > M}` has upper
  density zero (`riemannHypothesis_iff_zerosApproachLine_and_upperDensityZero_lagExcursion`);
* RH holds iff the zeros approach the line and the level-one constant-vector JAS interval tests are
  positive at every scale `y` with `log y` outside a set of log-scales of upper density zero
  (`riemannHypothesis_iff_zerosApproachLine_and_jasPositiveExcept_upperDensityZero`);
* the asymptotic abscissa law follows from `Φ ≤ M_a e^{aL}` off sets of Abel density zero, for every
  `a > 0` (`asymptoticAbscissaLaw_of_forall_le_exp_abelDensityZero`);
* "zeros approach the line" may be weakened to the absence of an off-line chain (a farthest off-line
  zero exists whenever RH fails): RH holds iff there is no off-line chain and the lag excursions, or
  the exceptional JAS scales, have upper density zero
  (`riemannHypothesis_iff_not_jasOffLineChain_and_upperDensityZero_lagExcursion`,
  `riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_upperDensityZero`);
* upper density may be replaced by lower density
  (`riemannHypothesis_iff_not_jasOffLineChain_and_lowerDensityZero_lagExcursion`,
  `riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_lowerDensityZero`). For example,
  with `T_{n+1} = T_n³` the JAS tests may fail at every scale with `log y ∈ [T_n, T_n²]`.

Quantitatively (`re_lagWeight_le_of_attainedTop_of_le_exp_except`, `not_volume_le_of_attainedTop`):
if the top `β₀ > ½ + a` is attained at `ρ₀`, then for every `M` the set of `L ≥ 0` with
`Φ(L) > M e^{aL}` has upper density at least `Re(1/(ρ₀(1−ρ₀)))/(4 Σ_ρ |1/(ρ(1−ρ))|)`.

So the excursions of an attained top have positive upper density, while the abstract Fejér
configurations with a non-attained top have excursion sets of finite measure.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

namespace RHTower.OneSidedConfiguration

noncomputable section

variable {ι : Type*}

/-! ## Abel density -/

/-- The Laplace mass `J_E(η) = ∫_{E ∩ (0,∞)} e^{−ηu} du`. -/
def abelMass (E : Set ℝ) (η : ℝ) : ℝ :=
  ∫ u in Ioi (0:ℝ), E.indicator (fun u => Real.exp (-η * u)) u

/-- `E` has Abel density zero: `η J_E(η) → 0` as `η → 0⁺`. -/
def AbelDensityZero (E : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ η in 𝓝[>] (0:ℝ), η * abelMass E η ≤ δ

/-- `E` has upper density zero: `|E ∩ [0, T]| ≤ εT` for every `ε > 0` and all large `T`. -/
def UpperDensityZero (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (ε * T)

theorem abelMass_nonneg (E : Set ℝ) (η : ℝ) : 0 ≤ abelMass E η :=
  setIntegral_nonneg measurableSet_Ioi fun u _ =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u

/-- Sets of finite measure have Abel density zero. -/
theorem abelDensityZero_of_volume_ne_top {E : Set ℝ} (hE : MeasurableSet E)
    (hfin : volume E ≠ ⊤) : AbelDensityZero E := by
  intro δ hδ
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume E).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ ENNReal.toReal_nonneg
  have hbd : ∀ η : ℝ, 0 < η → abelMass E η ≤ V := by
    intro η hη
    rw [abelMass, setIntegral_indicator hE]
    have hfin' : volume (Ioi (0:ℝ) ∩ E) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
    calc ∫ u in Ioi (0:ℝ) ∩ E, Real.exp (-η * u)
        ≤ ∫ u in Ioi (0:ℝ) ∩ E, (1:ℝ) := by
          refine setIntegral_mono_on ((exp_neg_integrableOn_Ioi 0 hη).mono_set inter_subset_left)
            (integrableOn_const hfin') (measurableSet_Ioi.inter hE) fun u hu => ?_
          exact Real.exp_le_one_iff.mpr (by nlinarith [hu.1.out])
      _ = (volume (Ioi (0:ℝ) ∩ E)).toReal := by
          rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
      _ ≤ V := hVdef ▸ ENNReal.toReal_mono hfin (measure_mono inter_subset_right)
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < δ / (V + 1) by positivity)] with η hη
  have h1 := hbd η hη.1
  have h2 : η * V ≤ δ / (V + 1) * V := mul_le_mul_of_nonneg_right hη.2.le hV0
  have h3 : δ / (V + 1) * V ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hη.1.le]

/-! ## The residue limit at the real point `B` -/

/-- **Residue limit.** If `Re w_i ≤ B` and the weights are summable, then
`(σ − B) Σ_i a_i/(σ − w_i) → Σ_{w_i = B} a_i` as `σ → B⁺` along the reals. -/
theorem tendsto_mul_cauchySeries {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) :
    Tendsto (fun σ : ℝ => ((σ - B : ℝ) : ℂ) * cauchySeries w a σ) (𝓝[>] B)
      (𝓝 (∑' i, if w i = (B : ℂ) then a i else 0)) := by
  have heq : ∀ σ : ℝ, ((σ - B : ℝ) : ℂ) * cauchySeries w a σ =
      ∑' i, ((σ - B : ℝ) : ℂ) * (a i / ((σ : ℂ) - w i)) := fun σ => by
    rw [cauchySeries, tsum_mul_left]
  simp_rw [heq]
  refine tendsto_tsum_of_dominated_convergence ha (fun i => ?_) ?_
  · by_cases hi : w i = (B : ℂ)
    · rw [if_pos hi]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hne : ((σ - B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hσ).ne'
      rw [hi]
      have hs : (σ : ℂ) - (B : ℂ) = ((σ - B : ℝ) : ℂ) := by push_cast; ring
      rw [hs, mul_div_cancel₀ _ hne]
    · rw [if_neg hi]
      have hne : ((B : ℝ) : ℂ) - w i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      have h1 : ContinuousAt (fun σ : ℝ => ((σ - B : ℝ) : ℂ)) B :=
        (Complex.continuous_ofReal.comp (continuous_sub_right B)).continuousAt
      have h2 : ContinuousAt (fun σ : ℝ => (σ : ℂ) - w i) B :=
        (Complex.continuous_ofReal.sub continuous_const).continuousAt
      have hc' : ContinuousAt (fun σ : ℝ => ((σ - B : ℝ) : ℂ) * (a i / ((σ : ℂ) - w i))) B :=
        h1.mul (continuousAt_const.div h2 hne)
      have hc := hc'.tendsto
      have h0 : ((B - B : ℝ) : ℂ) * (a i / ((B : ℂ) - w i)) = 0 := by simp
      rw [h0] at hc
      exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ i
    have hσB : 0 < σ - B := sub_pos.mpr hσ
    have hnorm : σ - B ≤ ‖(σ : ℂ) - w i‖ := by
      have h1 := Complex.re_le_norm ((σ : ℂ) - w i)
      have h2 : ((σ : ℂ) - w i).re = σ - (w i).re := by simp
      linarith [hB i]
    have hpos : 0 < ‖(σ : ℂ) - w i‖ := lt_of_lt_of_le hσB hnorm
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hσB.le]
    calc (σ - B) * (‖a i‖ / ‖(σ : ℂ) - w i‖) = ‖a i‖ * ((σ - B) / ‖(σ : ℂ) - w i‖) := by ring
      _ ≤ ‖a i‖ * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hpos).mpr hnorm) (norm_nonneg _)
      _ = ‖a i‖ := mul_one _

/-! ## The real Laplace transform of the lag function -/

theorem re_pairSeries_ofReal (a w : ι → ℂ) (σ : ℝ) :
    (pairSeries a w σ).re = (cauchySeries w a σ).re := by
  have hconj : cauchySeries (fun i => conj (w i)) (fun i => conj (a i)) (σ : ℂ) =
      conj (cauchySeries w a σ) := by
    rw [cauchySeries, cauchySeries, Complex.conj_tsum]
    refine tsum_congr fun i => ?_
    rw [map_div₀, map_sub, Complex.conj_ofReal]
  rw [pairSeries, hconj, Complex.add_conj]
  simp

/-- For real `σ > B`, `∫_0^∞ Φ(u) e^{−σu} du = Re Σ_i a_i/(σ − w_i)`. -/
theorem integral_lagRe_mul_exp [Countable ι] {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    {B : ℝ} (hB : ∀ i, (w i).re ≤ B) {σ : ℝ} (hσ : B < σ) :
    IntegrableOn (fun u : ℝ => lagRe a w u * Real.exp (-σ * u)) (Ioi 0) ∧
      ∫ u in Ioi (0:ℝ), lagRe a w u * Real.exp (-σ * u) = (cauchySeries w a σ).re := by
  have hs : B < ((σ : ℂ)).re := by simpa using hσ
  have ha' : Summable fun i => ‖conj (a i)‖ := by simpa using ha
  have hB' : ∀ i, (conj (w i)).re ≤ B := fun i => by simpa using hB i
  have h1 := integrableOn_lagSum_mul_cexp ha hB hs
  have h2 := integrableOn_lagSum_mul_cexp ha' hB' hs
  have hpt : ∀ u : ℝ, (lagRe a w u : ℂ) * cexp (-(σ : ℂ) * u) =
      ((∑' i, a i * cexp (u * w i)) * cexp (-(σ : ℂ) * u) +
        (∑' i, conj (a i) * cexp (u * conj (w i))) * cexp (-(σ : ℂ) * u)) / 2 := fun u => by
    rw [ofReal_lagRe]; ring
  have hF : IntegrableOn (fun u : ℝ => (lagRe a w u : ℂ) * cexp (-(σ : ℂ) * u)) (Ioi 0) := by
    exact IntegrableOn.congr_fun ((h1.add h2).div_const 2) (fun u _ => (hpt u).symm)
      measurableSet_Ioi
  have hre : ∀ u : ℝ, ((lagRe a w u : ℂ) * cexp (-(σ : ℂ) * u)).re =
      lagRe a w u * Real.exp (-σ * u) := fun u => by
    have : cexp (-(σ : ℂ) * u) = ((Real.exp (-σ * u) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine ⟨IntegrableOn.congr_fun (Integrable.re hF)
    (fun u _ => by simp only [RCLike.re_to_complex]; exact hre u) measurableSet_Ioi, ?_⟩
  have := integral_re hF
  simp only [RCLike.re_to_complex] at this
  simp_rw [hre] at this
  rw [this, integral_lagRe_mul_cexp ha hB hs, re_pairSeries_ofReal]

/-! ## Excursions of small Abel density -/

/-- **The top weight is bounded by the Abel density of the excursions.** -/
theorem re_tsum_top_le_of_lagRe_le_except [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {B : ℝ} (hB0 : 0 < B) (hB : ∀ i, (w i).re ≤ B)
    {E : Set ℝ} (hE : MeasurableSet E) {M δ : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M)
    (hδ : ∃ᶠ η in 𝓝[>] (0:ℝ), η * abelMass E η ≤ δ) :
    (∑' i, if w i = (B : ℂ) then a i else 0).re ≤ (∑' i, ‖a i‖) * δ := by
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∑' i, ‖a i‖ := ⟨_, rfl⟩
  rw [← hWdef]
  have hW0 : 0 ≤ W := hWdef ▸ tsum_nonneg fun _ => norm_nonneg _
  have hineq : ∀ σ : ℝ, B < σ →
      (cauchySeries w a σ).re ≤ max M 0 / σ + W * abelMass E (σ - B) := by
    intro σ hσ
    obtain ⟨hint, heq⟩ := integral_lagRe_mul_exp ha hB hσ
    rw [← heq]
    have hσ0 : 0 < σ := hB0.trans hσ
    have hη : 0 < σ - B := sub_pos.mpr hσ
    have hI1 : IntegrableOn (fun u : ℝ => max M 0 * Real.exp (-σ * u)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hσ0).const_mul _
    have hI2 : IntegrableOn
        (fun u : ℝ => W * E.indicator (fun u => Real.exp (-(σ - B) * u)) u) (Ioi 0) :=
      ((exp_neg_integrableOn_Ioi 0 hη).indicator hE).const_mul _
    have hbound : ∀ u ∈ Ioi (0:ℝ), lagRe a w u * Real.exp (-σ * u) ≤
        max M 0 * Real.exp (-σ * u) +
          W * E.indicator (fun u => Real.exp (-(σ - B) * u)) u := by
      intro u hu
      have hu0 : (0:ℝ) ≤ u := le_of_lt hu
      have he := Real.exp_pos (-σ * u)
      by_cases huE : u ∈ E
      · rw [Set.indicator_of_mem huE]
        have h1 := abs_lagRe_le ha hB hu0
        rw [← hWdef] at h1
        have h2 : lagRe a w u * Real.exp (-σ * u) ≤ W * Real.exp (-(σ - B) * u) :=
          calc lagRe a w u * Real.exp (-σ * u) ≤ |lagRe a w u| * Real.exp (-σ * u) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) he.le
            _ ≤ (W * Real.exp (u * B)) * Real.exp (-σ * u) :=
                mul_le_mul_of_nonneg_right h1 he.le
            _ = W * Real.exp (-(σ - B) * u) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        have h3 : 0 ≤ max M 0 * Real.exp (-σ * u) := mul_nonneg (le_max_right _ _) he.le
        linarith
      · rw [Set.indicator_of_notMem huE, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_right ((hM u hu0 huE).trans (le_max_left _ _)) he.le
    have hexp : ∫ u in Ioi (0:ℝ), Real.exp (-σ * u) = 1 / σ := by
      rw [integral_exp_mul_Ioi (by linarith) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    calc ∫ u in Ioi (0:ℝ), lagRe a w u * Real.exp (-σ * u)
        ≤ ∫ u in Ioi (0:ℝ), (max M 0 * Real.exp (-σ * u) +
            W * E.indicator (fun u => Real.exp (-(σ - B) * u)) u) :=
          setIntegral_mono_on hint (hI1.add hI2) measurableSet_Ioi hbound
      _ = max M 0 / σ + W * abelMass E (σ - B) := by
          rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, hexp, abelMass,
            mul_one_div]
  have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_mul_cauchySeries ha hB)
  have hre : ∀ σ : ℝ, (((σ - B : ℝ) : ℂ) * cauchySeries w a σ).re =
      (σ - B) * (cauchySeries w a σ).re := fun σ => Complex.re_ofReal_mul _ _
  have hlim' : Tendsto (fun σ : ℝ => (σ - B) * (cauchySeries w a σ).re) (𝓝[>] B)
      (𝓝 (∑' i, if w i = (B : ℂ) then a i else 0).re) :=
    hlim.congr fun σ => hre σ
  have hadd : Tendsto (fun η : ℝ => B + η) (𝓝[>] (0:ℝ)) (𝓝[>] B) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := ((continuous_const_add B).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with η hη
      show B < B + η
      linarith [show (0:ℝ) < η from hη]
  have hF := hlim'.comp hadd
  have hG : Tendsto (fun η : ℝ => η * (max M 0 / (B + η)) + W * δ) (𝓝[>] (0:ℝ))
      (𝓝 (0 * (max M 0 / (B + 0)) + W * δ)) := by
    have hB' : B + 0 ≠ 0 := by rw [add_zero]; exact hB0.ne'
    have hc : ContinuousAt (fun η : ℝ => η * (max M 0 / (B + η)) + W * δ) 0 :=
      (continuousAt_id.mul (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        hB')).add continuousAt_const
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  simp only [zero_mul, zero_add] at hG
  have hfreq : ∃ᶠ η in 𝓝[>] (0:ℝ), (B + η - B) * (cauchySeries w a ((B + η : ℝ) : ℂ)).re ≤
      η * (max M 0 / (B + η)) + W * δ := by
    refine (hδ.and_eventually self_mem_nhdsWithin).mono fun η hη => ?_
    obtain ⟨hδη, hη0⟩ := hη
    have hη' : (0:ℝ) < η := hη0
    have h1 := hineq (B + η) (by linarith)
    rw [show B + η - B = η by ring] at h1 ⊢
    calc η * (cauchySeries w a ((B + η : ℝ) : ℂ)).re
        ≤ η * (max M 0 / (B + η) + W * abelMass E η) := mul_le_mul_of_nonneg_left h1 hη'.le
      _ = η * (max M 0 / (B + η)) + W * (η * abelMass E η) := by ring
      _ ≤ η * (max M 0 / (B + η)) + W * δ := by
          have := mul_le_mul_of_nonneg_left hδη hW0
          linarith
  by_contra hcon
  push Not at hcon
  have hdiff := (hF.sub hG).eventually (lt_mem_nhds (sub_pos.mpr hcon))
  obtain ⟨η, h1, h2⟩ := (hfreq.and_eventually hdiff).exists
  simp only [Function.comp] at h2
  linarith

/-- **Excursions of Abel density zero give a top weight with nonpositive real part.** -/
theorem re_tsum_top_nonpos_of_lagRe_le_abelDensityZero [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {B : ℝ} (hB0 : 0 < B) (hB : ∀ i, (w i).re ≤ B)
    {E : Set ℝ} (hE : MeasurableSet E) (hEd : AbelDensityZero E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) :
    (∑' i, if w i = (B : ℂ) then a i else 0).re ≤ 0 := by
  have hW0 : 0 ≤ ∑' i, ‖a i‖ := tsum_nonneg fun _ => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (∑' i, ‖a i‖ + 1) := by positivity
  have h := re_tsum_top_le_of_lagRe_le_except ha hB0 hB hE hM (hEd _ hδ).frequently
  have h2 : (∑' i, ‖a i‖) * (ε / (∑' i, ‖a i‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-! ## Upper density zero implies Abel density zero -/

theorem integral_mul_exp_Ioi {η : ℝ} (hη : 0 < η) (u : ℝ) :
    ∫ T in Ioi u, η * Real.exp (-η * T) = Real.exp (-η * u) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) u]
  field_simp

theorem integrableOn_mul_exp_Ioi {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun T : ℝ => T * Real.exp (-η * T)) (Ioi 0) := by
  by_contra hni
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := η) (by norm_num) hη
  have hfun : (fun T : ℝ => T ^ ((2:ℝ) - 1) * Real.exp (-(η * T))) =
      fun T : ℝ => T * Real.exp (-η * T) := by
    funext T; norm_num [neg_mul]
  rw [hfun, integral_undef hni, Real.Gamma_two, mul_one] at h
  have : 0 < (1 / η) ^ (2:ℝ) := by positivity
  linarith

theorem integral_mul_exp_Ioi_eq {η : ℝ} (hη : 0 < η) :
    ∫ T in Ioi (0:ℝ), T * Real.exp (-η * T) = 1 / η ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := η) (by norm_num) hη
  have hfun : (fun T : ℝ => T ^ ((2:ℝ) - 1) * Real.exp (-(η * T))) =
      fun T : ℝ => T * Real.exp (-η * T) := by
    funext T; norm_num [neg_mul]
  rw [hfun, Real.Gamma_two, mul_one, Real.rpow_two, div_pow, one_pow] at h
  exact h

theorem integral_affine_mul_exp_Ioi {η : ℝ} (hη : 0 < η) (ε C : ℝ) :
    ∫ T in Ioi (0:ℝ), η * Real.exp (-η * T) * (ε * T + C) = ε / η + C := by
  have hI2 : IntegrableOn (fun T : ℝ => Real.exp (-η * T)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hη
  have hE1 : ∫ T in Ioi (0:ℝ), Real.exp (-η * T) = 1 / η := by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hsplit : (fun T : ℝ => η * Real.exp (-η * T) * (ε * T + C)) =
      fun T => (η * ε) * (T * Real.exp (-η * T)) + (η * C) * Real.exp (-η * T) := by
    funext T; ring
  rw [hsplit, integral_add ((integrableOn_mul_exp_Ioi hη).const_mul _) (hI2.const_mul _),
    integral_const_mul, integral_const_mul, integral_mul_exp_Ioi_eq hη, hE1]
  field_simp

/-- **Abelian bound.** If `|E ∩ [0, T]| ≤ εT + C` for every `T ≥ 0`, then `J_E(η) ≤ ε/η + C`. -/
theorem abelMass_le_of_volume_le {E : Set ℝ} (hE : MeasurableSet E) {η ε C : ℝ} (hη : 0 < η)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hvol : ∀ T : ℝ, 0 ≤ T → volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (ε * T + C)) :
    abelMass E η ≤ ε / η + C := by
  set g : ℝ → ENNReal := fun T => ENNReal.ofReal (η * Real.exp (-η * T)) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ E ∧ p.1 < p.2} with hS
  have hSm : MeasurableSet S :=
    (hE.preimage measurable_fst).inter (measurableSet_lt measurable_fst measurable_snd)
  set F : ℝ → ℝ → ENNReal := fun u T => S.indicator (fun p => g p.2) (u, T) with hF
  have hFm : Measurable (Function.uncurry F) := (hgm.comp measurable_snd).indicator hSm
  -- the inner integral in `T`
  have hinner : ∀ u ∈ Ioi (0:ℝ), ∫⁻ T in Ioi (0:ℝ), F u T =
      E.indicator (fun u => ENNReal.ofReal (Real.exp (-η * u))) u := by
    intro u hu
    by_cases huE : u ∈ E
    · rw [Set.indicator_of_mem huE]
      have hFu : ∀ T, F u T = (Ioi u).indicator g T := fun T => by
        by_cases hT : u < T
        · show S.indicator (fun p => g p.2) (u, T) = _
          rw [Set.indicator_of_mem (show (u, T) ∈ S from ⟨huE, hT⟩),
            Set.indicator_of_mem (show T ∈ Ioi u from hT)]
        · show S.indicator (fun p => g p.2) (u, T) = _
          rw [Set.indicator_of_notMem (show (u, T) ∉ S from fun h => hT h.2),
            Set.indicator_of_notMem (show T ∉ Ioi u from hT)]
      simp_rw [hFu]
      rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        show Ioi u ∩ Ioi (0:ℝ) = Ioi u from inter_eq_left.mpr (Ioi_subset_Ioi (le_of_lt hu))]
      rw [hg, ← ofReal_integral_eq_lintegral_ofReal, integral_mul_exp_Ioi hη u]
      · exact ((exp_neg_integrableOn_Ioi u hη).const_mul η)
      · filter_upwards with T
        exact mul_nonneg hη.le (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem huE]
      have hFu : ∀ T, F u T = 0 := fun T => by
        show S.indicator (fun p => g p.2) (u, T) = _
        rw [Set.indicator_of_notMem (show (u, T) ∉ S from fun h => huE h.1)]
      simp_rw [hFu, lintegral_zero]
  -- the inner integral in `u`
  have hinner' : ∀ T ∈ Ioi (0:ℝ), ∫⁻ u in Ioi (0:ℝ), F u T ≤
      g T * ENNReal.ofReal (ε * T + C) := by
    intro T hT
    have hFT : ∀ u, F u T = (E ∩ Iio T).indicator (fun _ => g T) u := fun u => by
      by_cases hu : u ∈ E ∩ Iio T
      · show S.indicator (fun p => g p.2) (u, T) = _
        rw [Set.indicator_of_mem (show (u, T) ∈ S from ⟨hu.1, hu.2⟩),
          Set.indicator_of_mem hu]
      · show S.indicator (fun p => g p.2) (u, T) = _
        rw [Set.indicator_of_notMem (show (u, T) ∉ S from fun h => hu ⟨h.1, h.2⟩),
          Set.indicator_of_notMem hu]
    simp_rw [hFT]
    rw [lintegral_indicator_const (hE.inter measurableSet_Iio),
      Measure.restrict_apply (hE.inter measurableSet_Iio)]
    have hmono : volume (E ∩ Iio T ∩ Ioi 0) ≤ ENNReal.ofReal (ε * T + C) :=
      le_trans (measure_mono fun u (hu : u ∈ E ∩ Iio T ∩ Ioi 0) =>
        (⟨hu.1.1, le_of_lt hu.2, le_of_lt hu.1.2⟩ : u ∈ E ∩ Icc 0 T)) (hvol T (le_of_lt hT))
    gcongr
  -- assemble
  have hlhs : ENNReal.ofReal (abelMass E η) =
      ∫⁻ u in Ioi (0:ℝ), E.indicator (fun u => ENNReal.ofReal (Real.exp (-η * u))) u := by
    rw [abelMass, ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun u => ?_
      by_cases hu : u ∈ E
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    · exact (exp_neg_integrableOn_Ioi 0 hη).indicator hE
    · filter_upwards with u
      exact Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u
  have hint : IntegrableOn (fun T : ℝ => η * Real.exp (-η * T) * (ε * T + C)) (Ioi 0) :=
    IntegrableOn.congr_fun (((integrableOn_mul_exp_Ioi hη).const_mul (η * ε)).add
      ((exp_neg_integrableOn_Ioi 0 hη).const_mul (η * C)))
      (fun T _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hbound : ENNReal.ofReal (abelMass E η) ≤ ENNReal.ofReal (ε / η + C) := by
    rw [hlhs]
    calc ∫⁻ u in Ioi (0:ℝ), E.indicator (fun u => ENNReal.ofReal (Real.exp (-η * u))) u
        = ∫⁻ u in Ioi (0:ℝ), ∫⁻ T in Ioi (0:ℝ), F u T :=
          (setLIntegral_congr_fun measurableSet_Ioi fun u hu => hinner u hu).symm
      _ = ∫⁻ T in Ioi (0:ℝ), ∫⁻ u in Ioi (0:ℝ), F u T :=
          lintegral_lintegral_swap hFm.aemeasurable
      _ ≤ ∫⁻ T in Ioi (0:ℝ), g T * ENNReal.ofReal (ε * T + C) :=
          setLIntegral_mono' measurableSet_Ioi hinner'
      _ = ∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (η * Real.exp (-η * T) * (ε * T + C)) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
          rw [hg, ← ENNReal.ofReal_mul (mul_nonneg hη.le (Real.exp_pos _).le)]
      _ = ENNReal.ofReal (ε / η + C) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint, integral_affine_mul_exp_Ioi hη]
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
          exact mul_nonneg (mul_nonneg hη.le (Real.exp_pos _).le)
            (add_nonneg (mul_nonneg hε (le_of_lt hT)) hC)
  have hpos : 0 ≤ ε / η + C := add_nonneg (div_nonneg hε hη.le) hC
  exact (ENNReal.ofReal_le_ofReal_iff hpos).mp hbound

/-- **Upper density zero implies Abel density zero.** -/
theorem abelDensityZero_of_upperDensityZero {E : Set ℝ} (hE : MeasurableSet E)
    (hu : UpperDensityZero E) : AbelDensityZero E := by
  intro δ hδ
  obtain ⟨T₀, hT₀⟩ := hu (δ / 2) (by positivity)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max T₀ 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  have hvol : ∀ T : ℝ, 0 ≤ T → volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (δ / 2 * T + C) := by
    intro T hT
    rcases le_or_gt T₀ T with h | h
    · exact (hT₀ T h).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · calc volume (E ∩ Icc 0 T) ≤ volume (Icc (0:ℝ) T) := measure_mono inter_subset_right
        _ = ENNReal.ofReal (T - 0) := Real.volume_Icc
        _ ≤ ENNReal.ofReal (δ / 2 * T + C) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have : T ≤ C := hCdef ▸ (le_of_lt h).trans (le_max_left _ _)
            nlinarith
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < δ / (2 * (C + 1)) by positivity)] with η hη
  have h1 := abelMass_le_of_volume_le hE hη.1 (by positivity) hC hvol
  have h2 : η * abelMass E η ≤ η * (δ / 2 / η + C) := mul_le_mul_of_nonneg_left h1 hη.1.le
  have h3 : η * (δ / 2 / η + C) = δ / 2 + η * C := by
    rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hη.1.ne']
  have h4 : η * C ≤ δ / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right hη.2.le hC
  have h5 : δ / (2 * (C + 1)) * C ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-! ## Lower densities -/

/-- `E` has lower Abel density zero: `η J_E(η) → 0` along some sequence `η → 0⁺`. -/
def LowerAbelDensityZero (E : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ᶠ η in 𝓝[>] (0:ℝ), η * abelMass E η ≤ δ

/-- `E` has lower density zero: for every `ε > 0`, `|E ∩ [0, T]| ≤ εT` for arbitrarily large `T`. -/
def LowerDensityZero (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (ε * T)

theorem AbelDensityZero.lower {E : Set ℝ} (h : AbelDensityZero E) : LowerAbelDensityZero E :=
  fun δ hδ => (h δ hδ).frequently

theorem UpperDensityZero.lower {E : Set ℝ} (h : UpperDensityZero E) : LowerDensityZero E := by
  intro ε hε T₀
  obtain ⟨T₁, hT₁⟩ := h ε hε
  exact ⟨max T₀ T₁, le_max_left _ _, hT₁ _ (le_max_right _ _)⟩

/-- `J_E(η) ≤ |E ∩ [0, T]| + e^{−ηT}/η`. -/
theorem abelMass_le_volume_add {E : Set ℝ} (hE : MeasurableSet E) {η T : ℝ} (hη : 0 < η)
    (hT : 0 ≤ T) :
    abelMass E η ≤ (volume (E ∩ Icc 0 T)).toReal + Real.exp (-η * T) / η := by
  have hS : MeasurableSet (E ∩ Icc 0 T) := hE.inter measurableSet_Icc
  have hfin : volume (E ∩ Icc 0 T) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hI1 : IntegrableOn (fun u => (E ∩ Icc 0 T).indicator (fun _ => (1:ℝ)) u) (Ioi 0) :=
    ((integrable_indicator_iff hS).mpr (integrableOn_const hfin)).integrableOn
  have hI2 : IntegrableOn (fun u => (Ioi T).indicator (fun u => Real.exp (-η * u)) u) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr
      (exp_neg_integrableOn_Ioi T hη)).integrableOn
  have hI0 : IntegrableOn (fun u => E.indicator (fun u => Real.exp (-η * u)) u) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hη).indicator hE
  have hbound : ∀ u ∈ Ioi (0:ℝ), E.indicator (fun u => Real.exp (-η * u)) u ≤
      (E ∩ Icc 0 T).indicator (fun _ => (1:ℝ)) u +
        (Ioi T).indicator (fun u => Real.exp (-η * u)) u := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    have hn1 := Set.indicator_nonneg (s := E ∩ Icc 0 T)
      (fun (_ : ℝ) _ => (zero_le_one : (0:ℝ) ≤ 1)) u
    have hn2 := Set.indicator_nonneg (s := Ioi T)
      (fun (u : ℝ) _ => (Real.exp_pos (-η * u)).le) u
    by_cases huE : u ∈ E
    · rw [Set.indicator_of_mem huE]
      by_cases huT : u ≤ T
      · rw [Set.indicator_of_mem (show u ∈ E ∩ Icc 0 T from ⟨huE, le_of_lt hu0, huT⟩)]
        have h1 : Real.exp (-η * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      · push Not at huT
        rw [Set.indicator_of_mem (show u ∈ Ioi T from huT)]
        linarith
    · rw [Set.indicator_of_notMem huE]
      linarith
  have e1 : ∫ u in Ioi (0:ℝ), (E ∩ Icc 0 T).indicator (fun _ => (1:ℝ)) u ≤
      (volume (E ∩ Icc 0 T)).toReal := by
    rw [setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
    exact ENNReal.toReal_mono hfin (measure_mono inter_subset_right)
  have e2 : ∫ u in Ioi (0:ℝ), (Ioi T).indicator (fun u => Real.exp (-η * u)) u =
      Real.exp (-η * T) / η := by
    rw [setIntegral_indicator measurableSet_Ioi,
      show Ioi (0:ℝ) ∩ Ioi T = Ioi T from inter_eq_right.mpr (Ioi_subset_Ioi hT),
      integral_exp_mul_Ioi (by linarith) T, neg_div_neg_eq]
  calc abelMass E η
      ≤ ∫ u in Ioi (0:ℝ), ((E ∩ Icc 0 T).indicator (fun _ => (1:ℝ)) u +
          (Ioi T).indicator (fun u => Real.exp (-η * u)) u) :=
        setIntegral_mono_on hI0 (hI1.add hI2) measurableSet_Ioi hbound
    _ ≤ (volume (E ∩ Icc 0 T)).toReal + Real.exp (-η * T) / η := by
        rw [integral_add hI1 hI2, e2]; linarith

/-- **Lower density zero implies lower Abel density zero.** -/
theorem lowerAbelDensityZero_of_lowerDensityZero {E : Set ℝ} (hE : MeasurableSet E)
    (h : LowerDensityZero E) : LowerAbelDensityZero E := by
  intro δ hδ
  obtain ⟨d, hd0, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ δ := ⟨δ, hδ, le_rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (d / 2) ^ 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨r, hr, hrU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hU
  have hr0 : 0 < r := hr
  obtain ⟨T, hT₀, hvol⟩ := h ε hε (2 / (d * r) + 1)
  have hdr : 0 < 2 / (d * r) := by positivity
  have hTpos : 0 < T := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 2 / (d * T) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηr : η < r := by
    have h1 : 2 / (d * r) < T := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [hηdef, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨η, hrU ⟨hη, hηr⟩, ?_⟩
  have h1 := abelMass_le_volume_add hE hη hTpos.le
  have hvol' : (volume (E ∩ Icc 0 T)).toReal ≤ ε * T :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  have hηT : η * T = 2 / d := by rw [hηdef]; field_simp
  have h2 : η * abelMass E η ≤ η * (ε * T) + Real.exp (-η * T) := by
    have hle : abelMass E η ≤ ε * T + Real.exp (-η * T) / η := by linarith
    have h3 := mul_le_mul_of_nonneg_left hle hη.le
    have he : η * (Real.exp (-η * T) / η) = Real.exp (-η * T) := by field_simp
    rw [mul_add, he] at h3
    exact h3
  have h3 : η * (ε * T) = d / 2 := by
    rw [show η * (ε * T) = (η * T) * ε by ring, hηT, hεdef]; field_simp
  have h4 : Real.exp (-η * T) ≤ d / 2 := by
    rw [neg_mul, hηT, Real.exp_neg]
    have h5 : 2 / d ≤ Real.exp (2 / d) := by linarith [Real.add_one_le_exp (2 / d)]
    rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h5
  linarith

/-- **Excursions of lower Abel density zero give a top weight with nonpositive real part.** -/
theorem re_tsum_top_nonpos_of_lagRe_le_lowerAbelDensityZero [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {B : ℝ} (hB0 : 0 < B) (hB : ∀ i, (w i).re ≤ B)
    {E : Set ℝ} (hE : MeasurableSet E) (hEd : LowerAbelDensityZero E) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → t ∉ E → lagRe a w t ≤ M) :
    (∑' i, if w i = (B : ℂ) then a i else 0).re ≤ 0 := by
  have hW0 : 0 ≤ ∑' i, ‖a i‖ := tsum_nonneg fun _ => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (∑' i, ‖a i‖ + 1) := by positivity
  have h := re_tsum_top_le_of_lagRe_le_except ha hB0 hB hE hM (hEd _ hδ)
  have h2 : (∑' i, ‖a i‖) * (ε / (∑' i, ‖a i‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

end

end RHTower.OneSidedConfiguration

/-! ## The lag function of `ζ` -/

namespace RHTower

noncomputable section

open OneSidedConfiguration BacklundConverse LindelofSparse

theorem norm_phaseCoef_zero (γ a : ℝ) (q : Fin 3 × XiZeroCopy) :
    ‖phaseCoef γ 0 0 lagWeight (lagShiftExp a) q‖ = ‖lagWeight q.2‖ * twistWeight q.1 := by
  rw [phaseCoef, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, norm_mul,
    phaseWeight_zero, Complex.norm_real, Real.norm_of_nonneg (twistWeight_pos _).le]

/-- The total weight of the twisted lag configuration is `2 Σ_ρ |1/(ρ(1−ρ))|`. -/
theorem tsum_norm_phaseCoef_zero (γ a : ℝ) :
    ∑' q : Fin 3 × XiZeroCopy, ‖phaseCoef γ 0 0 lagWeight (lagShiftExp a) q‖ =
      2 * lagWeightTotal := by
  have hsum := summable_norm_lagWeight
  simp_rw [norm_phaseCoef_zero]
  have hs : Summable fun q : Fin 3 × XiZeroCopy => ‖lagWeight q.2‖ * twistWeight q.1 :=
    (summable_prod_of_nonneg fun q => mul_nonneg (norm_nonneg _) (twistWeight_pos _).le).mpr
      ⟨fun _ => hsum.mul_right _, Summable.of_finite⟩
  rw [hs.tsum_prod' (fun k => hsum.mul_right _), tsum_fintype, Fin.sum_univ_three]
  simp only [tsum_mul_right, lagWeightTotal, twistWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The weight of an attained top is bounded by the Abel density of the excursions.** Let the
maximal real part `β₀ > ½ + a` be attained at `ρ₀`. If `Φ(L) ≤ M e^{aL}` for every `L ≥ 0` outside a
measurable set `E` with `η J_E(η) ≤ δ` for all small `η > 0`, then
`Re(1/(ρ₀(1−ρ₀))) ≤ 4 δ Σ_ρ |1/(ρ(1−ρ))|`. -/
theorem re_lagWeight_le_of_attainedTop_of_le_exp_except {M a β₀ δ : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hδ : ∃ᶠ η in 𝓝[>] (0:ℝ), η * abelMass E η ≤ δ)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L))
    (htop : AttainedTop β₀) (hlt : 1 / 2 + a < β₀) {q₀ : XiZeroCopy}
    (hq₀ : (q₀.1 : ℂ).re = β₀) : (lagWeight q₀).re ≤ 4 * lagWeightTotal * δ := by
  have hall := htop.2
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (q₀.1 : ℂ).im := ⟨_, rfl⟩
  have hBw : ∀ q, (lagShiftExp a q).re ≤ β₀ - 1 / 2 - a := fun q => by
    rw [re_lagShiftExp]; linarith [hall q]
  have hsum := summable_norm_lagWeight
  have hnormQ : Summable fun q : Fin 3 × XiZeroCopy =>
      ‖phaseCoef γ 0 0 lagWeight (lagShiftExp a) q‖ := by
    simp_rw [norm_phaseCoef_zero]
    exact (summable_prod_of_nonneg fun q => mul_nonneg (norm_nonneg _) (twistWeight_pos _).le).mpr
      ⟨fun _ => hsum.mul_right _, Summable.of_finite⟩
  have hpos : ∀ q : Fin 3 × XiZeroCopy,
      0 < (phaseCoef γ 0 0 lagWeight (lagShiftExp a) q).re := by
    intro q
    rw [phaseCoef, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, phaseWeight_zero,
      Complex.re_mul_ofReal]
    exact mul_pos (lagWeight_re_pos _) (twistWeight_pos _)
  have hMQ : ∀ t : ℝ, 0 ≤ t → t ∉ E →
      lagRe (phaseCoef γ 0 0 lagWeight (lagShiftExp a)) (twistExp γ (lagShiftExp a)) t ≤
        2 * max M 0 := by
    intro t ht htE
    rw [lagRe_phaseTwist hsum hBw γ 0 le_rfl ht]
    simp only [add_zero]
    rw [lagRe_lagShiftExp]
    have he := Real.exp_pos (-(a * t))
    have h2 : Real.exp (-(a * t)) * weilLagFunctionReal t ≤ M :=
      calc Real.exp (-(a * t)) * weilLagFunctionReal t
          ≤ Real.exp (-(a * t)) * (M * Real.exp (a * t)) :=
            mul_le_mul_of_nonneg_left (hM t ht htE) he.le
        _ = M := by
            rw [mul_comm M, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hcos := Real.neg_one_le_cos (γ * t)
    have hcos' := Real.cos_le_one (γ * t)
    have hm := le_max_left M 0
    have hm0 := le_max_right M 0
    nlinarith
  have key := re_tsum_top_le_of_lagRe_le_except (B := β₀ - 1 / 2 - a) hnormQ
    (by linarith) (fun q => by rw [re_twistExp]; exact hBw _) hE hMQ hδ
  rw [tsum_norm_phaseCoef_zero] at key
  have hj : twistExp γ (lagShiftExp a) (2, q₀) = ((β₀ - 1 / 2 - a : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [re_twistExp, re_lagShiftExp, hq₀, Complex.ofReal_re]
    · simp [twistExp, twistShift, im_lagShiftExp, hγ]
  set f : Fin 3 × XiZeroCopy → ℂ := fun q =>
    if twistExp γ (lagShiftExp a) q = ((β₀ - 1 / 2 - a : ℝ) : ℂ) then
      phaseCoef γ 0 0 lagWeight (lagShiftExp a) q else 0 with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded hnormQ fun q => ?_
    simp only [hf]
    split_ifs
    · exact le_rfl
    · simp
  have hre0 : ∀ q, 0 ≤ (f q).re := fun q => by
    simp only [hf]
    split_ifs
    · exact (hpos q).le
    · simp
  have hterm : (f (2, q₀)).re = (lagWeight q₀).re / 2 := by
    simp only [hf]
    rw [if_pos hj, phaseCoef, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      phaseWeight_zero, Complex.re_mul_ofReal]
    simp [twistWeight]
    ring
  have hle : (f (2, q₀)).re ≤ ∑' q, (f q).re :=
    (Complex.reCLM.summable hfs).le_tsum (2, q₀) fun q _ => hre0 q
  rw [Complex.re_tsum hfs] at key
  linarith

/-- **Lag excursions of Abel density zero bound an attained top.** If `Φ(L) ≤ M e^{aL}` for every
`L ≥ 0` outside a measurable set of Abel density zero, and the maximal real part `β₀` of the zeros
is attained, then `β₀ ≤ ½ + a`. -/
theorem re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero {M a β₀ : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEd : AbelDensityZero E)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L))
    (htop : AttainedTop β₀) : β₀ ≤ 1 / 2 + a := by
  by_contra hlt
  push Not at hlt
  obtain ⟨q₀, hq₀⟩ := htop.1
  have hW := lagWeightTotal_pos
  have hw := lagWeight_re_pos q₀
  have hδ : 0 < (lagWeight q₀).re / (8 * lagWeightTotal) := by positivity
  have h := re_lagWeight_le_of_attainedTop_of_le_exp_except hE (hEd _ hδ).frequently hM htop hlt
    hq₀
  have h2 : 4 * lagWeightTotal * ((lagWeight q₀).re / (8 * lagWeightTotal)) =
      (lagWeight q₀).re / 2 := by field_simp; ring
  linarith

/-- **An attained top forces lag excursions of positive upper density.** Let the maximal real part
`β₀ > ½ + a` be attained at `ρ₀`. For every level `M`, the set `E` of `L ≥ 0` with
`Φ(L) > M e^{aL}` does not satisfy `|E ∩ [0, T]| ≤ δT` for all large `T` once
`δ < Re(1/(ρ₀(1−ρ₀)))/(4 Σ_ρ |1/(ρ(1−ρ))|)`. -/
theorem not_volume_le_of_attainedTop {M a β₀ δ : ℝ} (htop : AttainedTop β₀)
    (hlt : 1 / 2 + a < β₀) {q₀ : XiZeroCopy} (hq₀ : (q₀.1 : ℂ).re = β₀)
    (hδ : δ < (lagWeight q₀).re / (4 * lagWeightTotal)) :
    ¬ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume ({L : ℝ | 0 ≤ L ∧ M * Real.exp (a * L) < weilLagFunctionReal L} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  rintro ⟨T₀, hT₀⟩
  set E : Set ℝ := {L : ℝ | 0 ≤ L ∧ M * Real.exp (a * L) < weilLagFunctionReal L} with hEdef
  have hEm : MeasurableSet E :=
    measurableSet_Ici.inter (measurableSet_lt
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
      measurable_weilLagFunctionReal)
  have hW := lagWeightTotal_pos
  have hw := lagWeight_re_pos q₀
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = max δ 0 := ⟨_, rfl⟩
  have hδ₁0 : 0 ≤ δ₁ := hδ₁def ▸ le_max_right _ _
  have hδ₁ : δ₁ < (lagWeight q₀).re / (4 * lagWeightTotal) := by
    rw [hδ₁def]; exact max_lt hδ (by positivity)
  obtain ⟨δ₂, hδ₂def⟩ : ∃ δ₂ : ℝ, δ₂ = (δ₁ + (lagWeight q₀).re / (4 * lagWeightTotal)) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max T₀ 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  have hvol : ∀ T : ℝ, 0 ≤ T → volume (E ∩ Icc 0 T) ≤ ENNReal.ofReal (δ₁ * T + C) := by
    intro T hT
    rcases le_or_gt T₀ T with h | h
    · refine (hT₀ T h).trans (ENNReal.ofReal_le_ofReal ?_)
      have : δ * T ≤ δ₁ * T := mul_le_mul_of_nonneg_right (hδ₁def ▸ le_max_left _ _) hT
      linarith
    · calc volume (E ∩ Icc 0 T) ≤ volume (Icc (0:ℝ) T) := measure_mono inter_subset_right
        _ = ENNReal.ofReal (T - 0) := Real.volume_Icc
        _ ≤ ENNReal.ofReal (δ₁ * T + C) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have : T ≤ C := hCdef ▸ (le_of_lt h).trans (le_max_left _ _)
            nlinarith
  have hgap : 0 < δ₂ - δ₁ := by rw [hδ₂def]; linarith
  have hev : ∀ᶠ η in 𝓝[>] (0:ℝ), η * abelMass E η ≤ δ₂ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < (δ₂ - δ₁) / (C + 1) by positivity)] with η hη
    have h1 := abelMass_le_of_volume_le hEm hη.1 hδ₁0 hC hvol
    have h2 : η * abelMass E η ≤ η * (δ₁ / η + C) := mul_le_mul_of_nonneg_left h1 hη.1.le
    have h3 : η * (δ₁ / η + C) = δ₁ + η * C := by
      rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hη.1.ne']
    have h4 : η * C ≤ (δ₂ - δ₁) / (C + 1) * C := mul_le_mul_of_nonneg_right hη.2.le hC
    have h5 : (δ₂ - δ₁) / (C + 1) * C ≤ δ₂ - δ₁ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L) :=
    fun L hL hLE => not_lt.mp fun h => hLE ⟨hL, h⟩
  have h := re_lagWeight_le_of_attainedTop_of_le_exp_except hEm hev.frequently hM htop hlt hq₀
  have h6 : 4 * lagWeightTotal * δ₂ < (lagWeight q₀).re := by
    have : δ₂ < (lagWeight q₀).re / (4 * lagWeightTotal) := by rw [hδ₂def]; linarith
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  linarith

/-- **Lag excursions of Abel density zero exclude an attained top right of the line.** -/
theorem not_attainedTop_of_weilLagFunctionReal_le_abelDensityZero {M : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEd : AbelDensityZero E)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M) :
    ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  rintro ⟨β₀, hβ₀, htop⟩
  have := re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero (M := M) (a := 0) hE hEd
    (fun L hL hLE => by rw [zero_mul, Real.exp_zero, mul_one]; exact hM L hL hLE) htop
  linarith

/-- **Subexponential one-sided precision off sets of Abel density zero gives the asymptotic
abscissa law.** -/
theorem asymptoticAbscissaLaw_of_forall_le_exp_abelDensityZero
    (h : ∀ a : ℝ, 0 < a → ∃ (M : ℝ) (E : Set ℝ), MeasurableSet E ∧ AbelDensityZero E ∧
      ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L)) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_not_attainedTop ?_
  rintro ⟨β₀, hβ₀, htop⟩
  obtain ⟨M, E, hE, hEd, hM⟩ := h ((β₀ - 1 / 2) / 2) (by linarith)
  have := re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero hE hEd hM htop
  linarith

/-- **Zeros approaching the line and lag excursions of Abel density zero give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_le_abelDensityZero (hZ : ZerosApproachLine)
    {M : ℝ} {E : Set ℝ} (hE : MeasurableSet E) (hEd : AbelDensityZero E)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M) : RiemannHypothesis := by
  by_contra hRH
  exact not_attainedTop_of_weilLagFunctionReal_le_abelDensityZero hE hEd hM
    (exists_attainedTop_of_zerosApproachLine hZ hRH)

theorem measurableSet_lagExcursion (M : ℝ) :
    MeasurableSet {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} :=
  measurableSet_Ici.inter (measurableSet_lt measurable_const measurable_weilLagFunctionReal)

theorem upperDensityZero_empty : UpperDensityZero (∅ : Set ℝ) := fun _ _ =>
  ⟨0, fun T _ => by simp⟩

theorem lagExcursion_eq_empty_of_riemannHypothesis (h : RiemannHypothesis) :
    {u : ℝ | 0 ≤ u ∧ poleSharpConstant < weilLagFunctionReal u} = ∅ := by
  ext u
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro _
  have := norm_weilLagFunction_le_of_riemannHypothesis h u
  rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- **RH ⟺ zeros approach the line ∧ some lag excursion set has upper density zero.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_upperDensityZero_lagExcursion :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      ∃ M : ℝ, UpperDensityZero {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} := by
  constructor
  · intro h
    refine ⟨zerosApproachLine_of_riemannHypothesis h, poleSharpConstant, ?_⟩
    rw [lagExcursion_eq_empty_of_riemannHypothesis h]
    exact upperDensityZero_empty
  · rintro ⟨hZ, M, hd⟩
    exact riemannHypothesis_of_zerosApproachLine_of_le_abelDensityZero hZ
      (measurableSet_lagExcursion M)
      (abelDensityZero_of_upperDensityZero (measurableSet_lagExcursion M) hd)
      (fun u hu huE => not_lt.mp fun h => huE ⟨hu, h⟩)

/-- **RH ⟺ eventual Hadamard positivity ∧ some lag excursion set has upper density zero.** -/
theorem riemannHypothesis_iff_eventualHadamardPositivity_and_upperDensityZero_lagExcursion :
    RiemannHypothesis ↔ EventualHadamardPositivity ∧
      ∃ M : ℝ, UpperDensityZero {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} := by
  rw [eventualHadamardPositivity_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_and_upperDensityZero_lagExcursion

/-- **Zeros approaching the line and level-one JAS positivity off a set of log-scales of Abel
density zero give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_jasIntervalProductPositiveExcept_abelDensityZero
    (hZ : ZerosApproachLine) {X : ℕ} {S : Set ℝ} (hpos : JasIntervalProductPositiveExcept X 1 S)
    (hS : MeasurableSet S) (hSd : AbelDensityZero S) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨β₀, hβ₀, htop⟩ := exists_attainedTop_of_zerosApproachLine hZ hRH
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := htop.2 q
    rw [hαdef]; linarith
  have hαall := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα1 : α < 1 / 2 := by
    obtain ⟨q₀, hq₀⟩ := htop.1
    have := xiZeroCopy_re_lt_one q₀
    rw [hαdef]; linarith
  have hδ0 : 0 < α / 4 := by linarith
  have hc0 : 0 < α / 2 := by linarith
  have hW := eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept hpos zero_le_one
    hδ0 (by linarith) hc0 (by linarith)
  obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
    (by linarith) hc0 hW
  have hmax : max (α / 2) (α - min (α / 2) (α / 4 / 4)) = 15 * α / 16 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [hmax] at hM
  have h := re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero hS hSd
    (fun L hL hLS => (le_abs_self _).trans (hM L hL hLS)) htop
  linarith

/-- **RH ⟺ zeros approach the line ∧ level-one JAS positivity off a set of log-scales of upper
density zero.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasPositiveExcept_upperDensityZero :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ (X : ℕ) (S : Set ℝ), MeasurableSet S ∧
      UpperDensityZero S ∧ JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH, X, ∅, MeasurableSet.empty,
      upperDensityZero_empty, fun y L hy _ hL => hX y L hy hL⟩
  · rintro ⟨hZ, X, S, hS, hSd, hpos⟩
    exact riemannHypothesis_of_zerosApproachLine_of_jasIntervalProductPositiveExcept_abelDensityZero
      hZ hpos hS (abelDensityZero_of_upperDensityZero hS hSd)

/-! ## The attainment input: no off-line chain -/

/-- **Without RH and without an off-line chain, the maximal real part is attained right of the
line.** A farthest off-line zero `ρ₀` gives the top `½ + |Re ρ₀ − ½|`, attained by `ρ₀` or by its
reflection `1 − ρ₀`. -/
theorem exists_attainedTop_of_not_jasOffLineChain (hno : ¬ JasOffLineChain)
    (hRH : ¬ RiemannHypothesis) : ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  have hfar : ∃ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 ∧
      ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
    by_contra h
    push Not at h
    exact hno ⟨⟨q₁, ne_of_gt hq₁⟩, fun q₀ hq₀ => h q₀ hq₀⟩
  obtain ⟨q₀, hq₀, hmax⟩ := hfar
  have he : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq₀)
  refine ⟨1 / 2 + |(q₀.1 : ℂ).re - 1 / 2|, by linarith, ?_, fun q => ?_⟩
  · rcases lt_or_gt_of_ne hq₀ with h | h
    · refine ⟨xiZeroCopyReflectEquiv q₀, ?_⟩
      rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re,
        abs_of_neg (by linarith : (q₀.1 : ℂ).re - 1 / 2 < 0)]
      ring
    · exact ⟨q₀, by rw [abs_of_pos (by linarith : 0 < (q₀.1 : ℂ).re - 1 / 2)]; ring⟩
  · have := hmax q
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ no off-line chain ∧ some lag excursion set has upper density zero.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_upperDensityZero_lagExcursion :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧
      ∃ M : ℝ, UpperDensityZero {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} := by
  constructor
  · intro h
    refine ⟨fun hc => ?_, poleSharpConstant, ?_⟩
    · obtain ⟨⟨q, hq⟩, -⟩ := hc
      exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis h q)
    · rw [lagExcursion_eq_empty_of_riemannHypothesis h]
      exact upperDensityZero_empty
  · rintro ⟨hno, M, hd⟩
    by_contra hRH
    exact not_attainedTop_of_weilLagFunctionReal_le_abelDensityZero
      (measurableSet_lagExcursion M)
      (abelDensityZero_of_upperDensityZero (measurableSet_lagExcursion M) hd)
      (fun u hu huE => not_lt.mp fun h => huE ⟨hu, h⟩)
      (exists_attainedTop_of_not_jasOffLineChain hno hRH)

/-- **An attained top and level-one JAS positivity off a set of log-scales of Abel density zero
give RH.** -/
theorem riemannHypothesis_of_attainedTop_of_jasIntervalProductPositiveExcept_abelDensityZero
    (hatt : ¬ RiemannHypothesis → ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀) {X : ℕ} {S : Set ℝ}
    (hpos : JasIntervalProductPositiveExcept X 1 S) (hS : MeasurableSet S)
    (hSd : AbelDensityZero S) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨β₀, hβ₀, htop⟩ := hatt hRH
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := htop.2 q
    rw [hαdef]; linarith
  have hαall := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα1 : α < 1 / 2 := by
    obtain ⟨q₀, hq₀⟩ := htop.1
    have := xiZeroCopy_re_lt_one q₀
    rw [hαdef]; linarith
  have hδ0 : 0 < α / 4 := by linarith
  have hc0 : 0 < α / 2 := by linarith
  have hW := eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept hpos zero_le_one
    hδ0 (by linarith) hc0 (by linarith)
  obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
    (by linarith) hc0 hW
  have hmax : max (α / 2) (α - min (α / 2) (α / 4 / 4)) = 15 * α / 16 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [hmax] at hM
  have h := re_le_half_add_of_attainedTop_of_le_exp_abelDensityZero hS hSd
    (fun L hL hLS => (le_abs_self _).trans (hM L hL hLS)) htop
  linarith

/-- **RH ⟺ no off-line chain ∧ level-one JAS positivity off a set of log-scales of upper density
zero.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_upperDensityZero :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∃ (X : ℕ) (S : Set ℝ), MeasurableSet S ∧
      UpperDensityZero S ∧ JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
    refine ⟨fun hc => ?_, X, ∅, MeasurableSet.empty, upperDensityZero_empty,
      fun y L hy _ hL => hX y L hy hL⟩
    obtain ⟨⟨q, hq⟩, -⟩ := hc
    exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
  · rintro ⟨hno, X, S, hS, hSd, hpos⟩
    exact riemannHypothesis_of_attainedTop_of_jasIntervalProductPositiveExcept_abelDensityZero
      (exists_attainedTop_of_not_jasOffLineChain hno) hpos hS
      (abelDensityZero_of_upperDensityZero hS hSd)

/-! ## Lower density -/

/-- **Lag excursions of lower Abel density zero bound an attained top.** -/
theorem re_le_half_add_of_attainedTop_of_le_exp_lowerAbelDensityZero {M a β₀ : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEd : LowerAbelDensityZero E)
    (hM : ∀ L, 0 ≤ L → L ∉ E → weilLagFunctionReal L ≤ M * Real.exp (a * L))
    (htop : AttainedTop β₀) : β₀ ≤ 1 / 2 + a := by
  by_contra hlt
  push Not at hlt
  obtain ⟨q₀, hq₀⟩ := htop.1
  have hW := lagWeightTotal_pos
  have hw := lagWeight_re_pos q₀
  have hδ : 0 < (lagWeight q₀).re / (8 * lagWeightTotal) := by positivity
  have h := re_lagWeight_le_of_attainedTop_of_le_exp_except hE (hEd _ hδ) hM htop hlt hq₀
  have h2 : 4 * lagWeightTotal * ((lagWeight q₀).re / (8 * lagWeightTotal)) =
      (lagWeight q₀).re / 2 := by field_simp; ring
  linarith

/-- **An attained top and level-one JAS positivity off a set of log-scales of lower Abel density
zero give RH.** -/
theorem riemannHypothesis_of_attainedTop_of_jasIntervalProductPositiveExcept_lowerAbel
    (hatt : ¬ RiemannHypothesis → ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀) {X : ℕ} {S : Set ℝ}
    (hpos : JasIntervalProductPositiveExcept X 1 S) (hS : MeasurableSet S)
    (hSd : LowerAbelDensityZero S) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨β₀, hβ₀, htop⟩ := hatt hRH
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = β₀ - 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := htop.2 q
    rw [hαdef]; linarith
  have hαall := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα1 : α < 1 / 2 := by
    obtain ⟨q₀, hq₀⟩ := htop.1
    have := xiZeroCopy_re_lt_one q₀
    rw [hαdef]; linarith
  have hδ0 : 0 < α / 4 := by linarith
  have hc0 : 0 < α / 2 := by linarith
  have hW := eventually_jasPositiveWindow_of_jasIntervalProductPositiveExcept hpos zero_le_one
    hδ0 (by linarith) hc0 (by linarith)
  obtain ⟨M, hM⟩ := exists_abs_weilLagFunctionReal_le_exp_of_windows_except hαall hδ0
    (by linarith) hc0 hW
  have hmax : max (α / 2) (α - min (α / 2) (α / 4 / 4)) = 15 * α / 16 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [hmax] at hM
  have h := re_le_half_add_of_attainedTop_of_le_exp_lowerAbelDensityZero hS hSd
    (fun L hL hLS => (le_abs_self _).trans (hM L hL hLS)) htop
  linarith

theorem lowerDensityZero_empty : LowerDensityZero (∅ : Set ℝ) :=
  upperDensityZero_empty.lower

/-- **RH ⟺ no off-line chain ∧ some lag excursion set has lower density zero.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_lowerDensityZero_lagExcursion :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧
      ∃ M : ℝ, LowerDensityZero {u : ℝ | 0 ≤ u ∧ M < weilLagFunctionReal u} := by
  constructor
  · intro h
    refine ⟨fun hc => ?_, poleSharpConstant, ?_⟩
    · obtain ⟨⟨q, hq⟩, -⟩ := hc
      exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis h q)
    · rw [lagExcursion_eq_empty_of_riemannHypothesis h]
      exact lowerDensityZero_empty
  · rintro ⟨hno, M, hd⟩
    by_contra hRH
    obtain ⟨β₀, hβ₀, htop⟩ := exists_attainedTop_of_not_jasOffLineChain hno hRH
    have := re_le_half_add_of_attainedTop_of_le_exp_lowerAbelDensityZero (M := M) (a := 0)
      (measurableSet_lagExcursion M)
      (lowerAbelDensityZero_of_lowerDensityZero (measurableSet_lagExcursion M) hd)
      (fun u hu huE => by
        rw [zero_mul, Real.exp_zero, mul_one]; exact not_lt.mp fun h => huE ⟨hu, h⟩) htop
    linarith

/-- **RH ⟺ no off-line chain ∧ level-one JAS positivity off a set of log-scales of lower density
zero.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_jasPositiveExcept_lowerDensityZero :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∃ (X : ℕ) (S : Set ℝ), MeasurableSet S ∧
      LowerDensityZero S ∧ JasIntervalProductPositiveExcept X 1 S := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasIntervalProductPositive_one.mp hRH
    refine ⟨fun hc => ?_, X, ∅, MeasurableSet.empty, lowerDensityZero_empty,
      fun y L hy _ hL => hX y L hy hL⟩
    obtain ⟨⟨q, hq⟩, -⟩ := hc
    exact hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
  · rintro ⟨hno, X, S, hS, hSd, hpos⟩
    exact riemannHypothesis_of_attainedTop_of_jasIntervalProductPositiveExcept_lowerAbel
      (exists_attainedTop_of_not_jasOffLineChain hno) hpos hS
      (lowerAbelDensityZero_of_lowerDensityZero hS hSd)

end

end RHTower
