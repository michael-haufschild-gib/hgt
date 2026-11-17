import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# No finite mode set reproduces the critical state

The state has the mode expansion `Σ_z L F(z) e^{−zu} = −a e^{−8u} F(u)` on `u < 0` (heated and
against smooth tests). Every finite truncation fails, and so does every other finite set of modes:

* **Finite mode sets are incomplete** (`criticalState_not_finite_modeSum`). On no terminal ray
  `u < −T` is the state almost everywhere a finite exponential sum `Σ_i d_i e^{s_i u}`, whatever
  the complex exponents and coefficients.

Mechanism. A finite sum on the ray makes the transform `L F(w)` the entire transform of the head
`F·1_{u ≥ −T}` plus `Σ_i d_i e^{−(w+s_i)T}/(w + s_i)`: holomorphic off finitely many points. The
continuation of the state agrees with it far to the right, hence (identity theorem on
`Re w > −9` minus a countable set, which is connected) wherever both are holomorphic. But the
continuation has the nonzero residue `−m_ρ L F(ρ − ½)/a` at `ρ − 17/2` for every zero with
`Re ρ ≥ ½` (the transform has no zero on `Re z ≥ 0`), and there are infinitely many such zeros.

This is the theta-cusp caution (`not_thetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete`) for the
state: any completeness statement for its modes is a statement about infinitely many of them.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations HTGeometry ArithmeticCastelnuovoSeveri

/-- The transform of a finite exponential sum on `(−∞, −T)`: `Σ_i d_i e^{−(w+s_i)T}/(w + s_i)`. -/
def modeTail {ι : Type*} [Fintype ι] (d s : ι → ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∑ i, d i * (Complex.exp ((w + s i) * ((-T : ℝ) : ℂ)) / (w + s i))

theorem differentiableAt_modeTail {ι : Type*} [Fintype ι] (d s : ι → ℂ) (T : ℝ) {w : ℂ}
    (hw : ∀ i, w + s i ≠ 0) : DifferentiableAt ℂ (modeTail d s T) w := by
  unfold modeTail
  refine DifferentiableAt.fun_sum fun i _ => ?_
  refine (differentiableAt_const _).mul (DifferentiableAt.div ?_ ?_ (hw i))
  · exact ((differentiableAt_id.add_const _).mul_const _).cexp
  · exact differentiableAt_id.add_const _

/-- **The transform of a profile that is a finite mode sum on a ray** is the transform of its head
plus the mode tail, right of all the modes. -/
theorem laplace_eq_head_add_modeTail {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {ι : Type*} [Fintype ι] (d s : ι → ℂ) (T : ℝ)
    (hmode : ∀ᵐ u ∂volume, u < -T → ((F u : ℝ) : ℂ) = ∑ i, d i * Complex.exp (s i * u))
    {w : ℂ} (hw0 : 0 ≤ w.re) (hws : ∀ i, 0 < (w + s i).re) :
    negativeHalfLineLaplace (cx F) w =
      negativeHalfLineLaplace (cx ((Ici (-T)).indicator F)) w + modeTail d s T w := by
  have hint : Integrable (fun u : ℝ => Complex.exp (w * u) * ((F u : ℝ) : ℂ)) := by
    refine hFi.norm.mono' ((Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal)).aestronglyMeasurable.mul
        (Complex.measurable_ofReal.comp hFm).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    rcases le_or_gt 0 u with hu | hu
    · simp [hsupp u hu]
    · have : (w * (u : ℂ)).re = w.re * u := by simp
      rw [this]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw0 hu.le))
  have hsplit := integral_add_compl (μ := volume) (s := Iio (-T)) measurableSet_Iio hint
  rw [compl_Iio] at hsplit
  have hhead : negativeHalfLineLaplace (cx ((Ici (-T)).indicator F)) w =
      ∫ x in Ici (-T), Complex.exp (w * x) * ((F x : ℝ) : ℂ) := by
    unfold negativeHalfLineLaplace
    rw [← integral_indicator measurableSet_Ici]
    congr 1
    funext x
    by_cases hx : x ∈ Ici (-T) <;> simp [cx, Set.indicator, hx]
  have htail : ∫ x in Iio (-T), Complex.exp (w * x) * ((F x : ℝ) : ℂ) = modeTail d s T w := by
    have hc : ∫ x in Iio (-T), Complex.exp (w * x) * ((F x : ℝ) : ℂ) =
        ∫ x in Iio (-T), ∑ i, d i * Complex.exp ((w + s i) * x) := by
      refine setIntegral_congr_ae measurableSet_Iio ?_
      filter_upwards [hmode] with x hx hxI
      rw [hx hxI, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_mul, Complex.exp_add]
      ring
    rw [hc, integral_finsetSum _ fun i _ =>
      ((integrableOn_exp_mul_complex_Iic (hws i) (-T)).mono_set Iio_subset_Iic_self).const_mul
        (d i)]
    unfold modeTail
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, ← integral_Iic_eq_integral_Iio, integral_exp_mul_complex_Iic (hws i)]
  unfold negativeHalfLineLaplace at hhead ⊢
  rw [show (∫ u : ℝ, Complex.exp (w * u) * cx F u) =
      ∫ u : ℝ, Complex.exp (w * u) * ((F u : ℝ) : ℂ) from rfl, ← hsplit, htail, hhead, add_comm]

/-- Infinitely many zeros of `ζ` lie on or right of the critical line. -/
theorem infinite_riemannZeta_zeros_right :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1}.Infinite := by
  intro hfin
  apply xiZeros_infinite
  refine (hfin.union (hfin.image fun ρ => 1 - ρ)).subset fun ρ hρ => ?_
  obtain ⟨hζ, htriv⟩ := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ
  have h0 : 0 < ρ.re := riemannZeta_zero_re_pos hζ htriv
  have h1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  rcases le_or_gt (1 / 2) ρ.re with h | h
  · exact Or.inl ⟨hζ, h, h1⟩
  · refine Or.inr ⟨1 - ρ, ⟨riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ h0 h1, ?_, ?_⟩,
      by ring⟩ <;> simp <;> linarith

/-- **No finite mode set reproduces the critical state.** On no terminal ray is the state almost
everywhere a finite exponential sum. -/
theorem criticalState_not_finite_modeSum {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ι : Type*} [Fintype ι]
    (d s : ι → ℂ) (T : ℝ) :
    ¬ ∀ᵐ u ∂volume, u < -T → ((F u : ℝ) : ℂ) = ∑ i, d i * Complex.exp (s i * u) := by
  intro hmode
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set H : ℝ → ℝ := (Ici (-T)).indicator F with hH
  have hHd : Differentiable ℂ (negativeHalfLineLaplace (cx H)) :=
    differentiable_laplace_of_head (T := T) (hd.meas.indicator measurableSet_Ici)
      (hd.integrable.indicator measurableSet_Ici)
      (fun u hu => by simp [hH, Set.indicator, hd.support u hu])
      (fun u (hu : u < -T) => by simp [hH, not_le.mpr hu])
  set G : ℂ → ℂ := fun w => negativeHalfLineLaplace (cx H) w + modeTail d s T w with hG
  set C : ℂ → ℂ := stateMeromorphic W₀ F with hC
  set S : Set ℂ := Set.range fun i => -s i with hS
  have hSfin : S.Finite := Set.finite_range _
  have hSopen : IsOpen Sᶜ := hSfin.isClosed.isOpen_compl
  have hnotS : ∀ w, w ∉ S → ∀ i, w + s i ≠ 0 := fun w hw i h =>
    hw ⟨i, by linear_combination -h⟩
  -- holomorphy of the two sides
  have hGd : ∀ w, w ∉ S → DifferentiableAt ℂ G w := fun w hw =>
    (hHd w).add (differentiableAt_modeTail d s T (hnotS w hw))
  have hCd : ∀ w, zetaEntire (w + 17 / 2) ≠ 0 → DifferentiableAt ℂ C w := by
    intro w hw
    have h := differentiableAt_globalRemainder hd (p := w + 8) fun _ => by
      rwa [show (1 : ℂ) / 2 + (w + 8) = w + 17 / 2 by ring]
    exact (h.comp w (differentiableAt_id.add_const (8 : ℂ))).neg.div_const _
  have hcont : Continuous fun w : ℂ => zetaEntire (w + 17 / 2) :=
    differentiable_zetaEntire.continuous.comp (continuous_id.add continuous_const)
  -- the domain: `Re w > −9` minus a countable set
  set V : Set ℂ := {w : ℂ | -9 < w.re} with hV
  set Z : Set ℂ := {w : ℂ | zetaEntire (w + 17 / 2) = 0} ∪ S with hZ
  have hZc : Z.Countable :=
    (countable_setOf_zetaEntire_eq_zero.preimage (add_left_injective (17 / 2 : ℂ))).union
      hSfin.countable
  set A : ℝ := 1 + ∑ i, |(s i).re| with hA
  have hsA : ∀ i, |(s i).re| ≤ A - 1 := fun i => by
    rw [hA, add_sub_cancel_left]
    exact Finset.single_le_sum (f := fun i => |(s i).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ i, |(s i).re| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  -- far to the right both sides are the transform of the state
  have hfar : ∀ w : ℂ, A - 1 / 2 < w.re → C w = G w := by
    intro w hw
    have hw4 : -4 < w.re := by linarith
    rw [hC, stateMeromorphic_eq_levyContinuation (by linarith), levyContinuation_eq_laplace hW ht hF hw4,
      laplace_eq_head_add_modeTail hd.meas hd.integrable hd.support d s T hmode (by linarith)
        fun i => by
          have := neg_abs_le (s i).re
          simp only [Complex.add_re]
          linarith [hsA i]]
  have ha : (A : ℂ) ∈ V \ Z := by
    refine ⟨by simp [hV]; linarith, ?_⟩
    rintro (h | ⟨i, hi⟩)
    · exact zetaEntire_ne_zero_of_riemannZeta_ne_zero
        (riemannZeta_ne_zero_of_one_le_re (by simp; linarith)) h
    · have h1 := congrArg Complex.re hi
      simp only [Complex.neg_re, Complex.ofReal_re] at h1
      linarith [neg_abs_le (s i).re, hsA i]
  have hU : IsPreconnected (V \ Z) :=
    (isPathConnected_diff_of_countable_of_convex (by rw [Complex.rank_real_complex]; norm_num)
      (convex_halfSpace_re_gt (-9)) (isOpen_lt continuous_const Complex.continuous_re) hZc
      ha).isConnected.isPreconnected
  have hCa : AnalyticOnNhd ℂ C (V \ Z) := by
    intro w hw
    have hz : zetaEntire (w + 17 / 2) ≠ 0 := fun h => hw.2 (Or.inl h)
    exact DifferentiableOn.analyticAt (s := {w' | zetaEntire (w' + 17 / 2) ≠ 0})
      (fun w' hw' => (hCd w' hw').differentiableWithinAt)
      ((isOpen_ne_fun hcont continuous_const).mem_nhds hz)
  have hGa : AnalyticOnNhd ℂ G (V \ Z) := by
    intro w hw
    have hs : w ∈ Sᶜ := fun h => hw.2 (Or.inr h)
    exact DifferentiableOn.analyticAt (s := Sᶜ) (fun w' hw' => (hGd w' hw').differentiableWithinAt)
      (hSopen.mem_nhds hs)
  have hfreq : ∃ᶠ z in 𝓝[≠] (A : ℂ), C z = G z := by
    have hev : ∀ᶠ z in 𝓝 (A : ℂ), C z = G z :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (A : ℂ) ∈ {z : ℂ | A - 1 / 2 < z.re} by simp)) fun z hz => hfar z hz
    exact (eventually_nhdsWithin_of_eventually_nhds hev).frequently
  have hEq : EqOn C G (V \ Z) := hCa.eqOn_of_preconnected_of_frequently_eq hGa hU ha hfreq
  -- a zero on or right of the line whose pole is not a mode
  obtain ⟨ρ₀, ⟨hζ₀, hρ₀, hρ₁⟩, hρS⟩ := ((infinite_riemannZeta_zeros_right).sdiff
    (hSfin.image fun σ => σ + 17 / 2)).nonempty
  set w₀ : ℂ := ρ₀ - 17 / 2 with hw₀
  have hw₀S : w₀ ∉ S := fun h => hρS ⟨w₀, h, by rw [hw₀]; ring⟩
  have hρpos : 0 < ρ₀.re := by linarith
  have hres := tendsto_stateMeromorphic_residue (W₀ := W₀) hd hζ₀ hρpos
  have hc0 := (levyResidue_ne_zero_iff hW hζ₀).mpr
    (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF (by simp; linarith))
  -- near the pole, `C = G`
  have hshift : Tendsto (fun w : ℂ => w + 17 / 2) (𝓝[≠] w₀) (𝓝[≠] ρ₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (continuous_add_const (17 / 2 : ℂ)).tendsto w₀
      rw [show w₀ + 17 / 2 = ρ₀ by rw [hw₀]; ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun w hw h => hw ?_
      rw [Set.mem_singleton_iff] at h ⊢
      rw [hw₀]
      linear_combination h
  have hζev : ∀ᶠ w in 𝓝[≠] w₀, zetaEntire (w + 17 / 2) ≠ 0 :=
    (hshift.eventually (eventually_riemannZeta_ne_zero_nhdsNE hρpos hρ₁)).mono fun w hw =>
      zetaEntire_ne_zero_of_riemannZeta_ne_zero hw
  have hVev : ∀ᶠ w in 𝓝[≠] w₀, w ∈ V :=
    eventually_nhdsWithin_of_eventually_nhds ((isOpen_lt continuous_const
      Complex.continuous_re).mem_nhds (show w₀ ∈ V by simp [hV, hw₀]; linarith))
  have hSev : ∀ᶠ w in 𝓝[≠] w₀, w ∈ Sᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hSopen.mem_nhds hw₀S)
  have hcongr : (fun w => (w - w₀) * C w) =ᶠ[𝓝[≠] w₀] fun w => (w - w₀) * G w := by
    filter_upwards [hζev, hVev, hSev] with w h1 h2 h3
    have hmem : w ∈ V \ Z := ⟨h2, fun h => h.elim h1 h3⟩
    rw [hEq hmem]
  exact not_differentiableAt_of_residue (hres.congr' hcongr) hc0 (hGd w₀ hw₀S)

#print axioms criticalState_not_finite_modeSum

end GaloisForLFunctions.ExclusionOfTheCriticalState
