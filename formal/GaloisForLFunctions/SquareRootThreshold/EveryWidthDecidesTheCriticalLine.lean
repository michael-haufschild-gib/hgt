import GaloisForLFunctions.SquareRootThreshold.PolarGroundEnergyAndPoleFreeLagAbscissaBridge
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe

/-!
# Every width decides the critical line

The one-parameter lag receiver (`onLine_iff_lag_twoBump_nonneg`) and the lag-rate law
(`re_le_iff_polarFree_lag_twoBump_ge_neg_exp`) are stated for a good width: the transform of the
smooth bump `κ_w` must not vanish at the spectral point `γ_ρ` of any off-line zero. That transform
is entire with non-real zeros, so for `ζ` only all but countably many widths are certified, and no
particular width is.

A box spline removes the exceptional set. `U_r^{⋆(n+1)}`, the `(n+1)`-fold convolution of the
uniform density on `[−r, r]`, is even, real and supported in `[−(n+1)r, (n+1)r]`; its transform
`(sin(rz)/(rz))^{n+1}` vanishes only on the real axis. An off-line zero has a non-real spectral
point, so every width sees every off-line zero.

* `onLine_iff_lag_splineTwoBump_nonneg`: for a tempered configuration without real zeros and
  every width `w > 0`, all zeros lie on the line iff the Weil form is nonnegative on
  `B_w(t + v/2) − B_w(t − v/2)` for all lags `v ≥ V`, `B_w = U_{w/4}^{⋆4}` (a `C²` cubic spline).
* `riemannHypothesis_iff_lag_splinePrimeWindow_nonneg`: for every `w ∈ (0, ½ log 2)` and `V ≥ 0`,
  RH holds iff the dyadic prime-window functional of these tests is nonnegative at every `v ≥ V`.
* `re_le_iff_polarFree_lag_splineTwoBump_ge_neg_exp`, `zeta_re_le_iff_polarFree_lag_splinePrimeWindow_ge_neg_exp`:
  for every width, all zeros satisfy `Re ρ ≤ ½ + σ` iff the polar-free spline lag family
  `B₂ = B'' − B/4`, `B = U_{w/6}^{⋆6}` (`C⁴`), is `≥ −C e^{σv}` at all large lags.

The arguments are those of the smooth-bump versions; only the spectral nonvanishing changes. The
coefficient laws are proved once for any bump whose transform is real and even.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower Bottcher
open _root_.RHTower.WeilDeletion (unif upow paperFT_upow support_upow_subset)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (contDiff_upow paperFT_unif_ne_zero)

/-! ## Coefficients of a bump with a real, even transform -/

/-- For a bump whose transform satisfies `conj (b̂(conj z)) = b̂(z)`, the coefficient of the zero
`½ + z` is `m b̂(−iz)²`. -/
theorem lagCoeff_eq_of_conj_symm (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hsym : ∀ z, conj (paperFT b (conj z)) = paperFT b z) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) :
    lagCoeff Z b z = (Z.mult (1 / 2 + z) : ℂ) * paperFT b (-(I * z)) ^ 2 := by
  rw [lagCoeff, Set.indicator_of_mem hz, EF.paperFT_weilTest hb hb hbc hbc, hsym,
    gammaOf_half_add]
  ring

/-- **No cancellation between conjugate zeros.** If the transform is also even, the merged
coefficient of `½ + z` is `(m_{½+z} + m_{½+z̄}) b̂(−iz)²`. -/
theorem evenCoeff_eq_of_conj_symm (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hsym : ∀ z, conj (paperFT b (conj z)) = paperFT b z)
    (heven : ∀ z, paperFT b (-z) = paperFT b z) {z : ℂ} (hz : (1 / 2 + z) ∈ Z.carrier) :
    evenCoeff Z b z = ((Z.mult (1 / 2 + z) : ℂ) +
      Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + conj z)) *
        paperFT b (-(I * z)) ^ 2 := by
  rw [evenCoeff, lagCoeff_eq_of_conj_symm Z hb hbc hsym hz, add_mul]
  congr 1
  by_cases hzc : (1 / 2 + conj z) ∈ Z.carrier
  · rw [lagCoeff_eq_of_conj_symm Z hb hbc hsym hzc, map_mul, Complex.conj_natCast, map_pow,
      Set.indicator_of_mem hzc]
    congr 2
    rw [← heven (-(I * conj z)), neg_neg, ← hsym (-(I * z))]
    congr 2
    simp [map_neg, map_mul]
  · rw [lagCoeff, Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzc, map_zero, zero_mul]

/-- At a real exponent the merged coefficient has positive real part whenever `b̂(−ix) ≠ 0`. -/
theorem re_evenCoeff_pos_of_conj_symm (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hsym : ∀ z, conj (paperFT b (conj z)) = paperFT b z)
    (heven : ∀ z, paperFT b (-z) = paperFT b z) {x : ℂ} (hx : (1 / 2 + x) ∈ Z.carrier)
    (him : x.im = 0) (hne : paperFT b (-(I * x)) ≠ 0) :
    0 < (evenCoeff Z b x).re := by
  have hxc : conj x = x := Complex.ext (by simp) (by simp [him])
  rw [evenCoeff_eq_of_conj_symm Z hb hbc hsym heven hx, hxc, Set.indicator_of_mem hx]
  set h := paperFT b (-(I * x)) with hh
  have hc : conj (I * x) = -(I * x) := by rw [map_mul, Complex.conj_I, hxc]; ring
  have hreal : conj h = h := by
    calc conj h = conj (paperFT b (conj (I * x))) := by rw [hh, hc]
      _ = paperFT b (I * x) := hsym _
      _ = h := by rw [hh, heven]
  have hhre : h = (h.re : ℂ) := Complex.ext rfl (by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    simp; linarith)
  have hre0 : h.re ≠ 0 := fun h0 => hne (by rw [hhre, h0, Complex.ofReal_zero])
  have hm : (1 : ℝ) ≤ Z.mult (1 / 2 + x) := by exact_mod_cast Z.one_le_mult _ hx
  rw [hhre, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have : 0 < h.re ^ 2 := by positivity
  nlinarith

/-- The merged coefficient of a right zero `ρ` is nonzero once `b̂(γ_ρ) ≠ 0`. -/
theorem evenCoeff_sub_half_ne_zero_of_conj_symm (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (hsym : ∀ z, conj (paperFT b (conj z)) = paperFT b z)
    (heven : ∀ z, paperFT b (-z) = paperFT b z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hg : paperFT b (gammaOf ρ) ≠ 0) : evenCoeff Z b (ρ - 1 / 2) ≠ 0 := by
  have hz : (1 / 2 + (ρ - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact hρ
  rw [evenCoeff_eq_of_conj_symm Z hb hbc hsym heven hz,
    show -(I * (ρ - 1 / 2)) = gammaOf ρ by rw [gammaOf, Complex.div_I]; ring]
  refine mul_ne_zero (fun h1 => ?_) (pow_ne_zero 2 hg)
  have h2 := congrArg Complex.re h1
  have hm : (1 : ℝ) ≤ Z.mult (1 / 2 + (ρ - 1 / 2)) := by exact_mod_cast Z.one_le_mult _ hz
  by_cases hc : (1 / 2 + conj (ρ - 1 / 2)) ∈ Z.carrier
  · rw [Set.indicator_of_mem hc, Complex.add_re, Complex.natCast_re, Complex.natCast_re,
      Complex.zero_re] at h2
    linarith [(Nat.cast_nonneg (Z.mult (1 / 2 + conj (ρ - 1 / 2))) : (0 : ℝ) ≤ _)]
  · rw [Set.indicator_of_notMem hc, Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
    linarith

/-! ## The receiver and the rate law for such a bump -/

/-- **One parameter decides the line, for a bump with real even transform.** -/
theorem onLine_iff_lag_twoBump_nonneg_of_conj_symm (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (hsym : ∀ z, conj (paperFT b (conj z)) = paperFT b z)
    (heven : ∀ z, paperFT b (-z) = paperFT b z)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT b (gammaOf ρ) ≠ 0) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  refine ⟨fun hon _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  exact evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc hsym heven ht.1
    (hgood t ht.1 (by linarith [ht.2]))
    (evenCoeff_eq_zero_of_difference_nonneg Z hZ hb hbs hreal (V := V) h hzre)

/-- **No exponent beyond the rate.** Let the merged coefficients be positive at every positive
real exponent. If `Re W ≥ −C e^{σv}` on the difference tests for `v ≥ V` (`σ ≥ 0`), every merged
coefficient with `Re z > σ` vanishes. -/
theorem evenCoeff_eq_zero_of_lag_ge_neg_exp_of_pos (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hpos : ∀ x : ℂ, (1 / 2 + x) ∈ Z.carrier → 0 < x.re → x.im = 0 → 0 < (evenCoeff Z b x).re)
    {σ C V : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z : ℂ} (hz : σ < z.re) : evenCoeff Z b z = 0 := by
  classical
  obtain ⟨M, hM0, hMb⟩ := exists_two_re_lagStructure_le_exp Z hZ hb hbs hσ hm
  have hhalf : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.re < 1 / 2 := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · have := hlt _ h; simp at this; linarith
    · have := hlt _ h; simp at this; linarith
  by_contra hne
  have hσh : σ < 1 / 2 := hz.trans (hhalf z hne)
  set R := (finite_evenCoeff_line Z b 0).toFinset.filter fun x => σ < x.re with hR
  have hmemR : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → σ < x.re → x ∈ R := fun x hx him hre =>
    Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hx, him⟩, hre⟩
  by_cases hRne : R.Nonempty
  · obtain ⟨x₀, hx₀R, hmax⟩ := R.exists_max_image Complex.re hRne
    obtain ⟨hx₀L, hx₀σ⟩ := Finset.mem_filter.mp hx₀R
    obtain ⟨hx₀, hx₀im⟩ := (Set.Finite.mem_toFinset _).mp hx₀L
    have habove : ∀ y : ℂ, x₀.re < y.re → evenCoeff Z b y = 0 := fun y hy =>
      evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs (hσ.trans hx₀σ.le)
        (hhalf x₀ hx₀) (fun x hx him => by
          by_contra h
          push Not at h
          exact absurd (hmax x (hmemR x hx him (hx₀σ.trans h))) (not_le.mpr h))
        (fun u hu => (hMb u hu).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx₀σ.le hu)) hM0)) hy
    set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
    haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
    have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
      have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
      exact h0
    have hle : ∀ t : ι, ((t : ℂ) - σ).re ≤ x₀.re - σ := fun t => by
      by_contra h
      have : x₀.re < (t : ℂ).re := by simp at h; linarith
      exact t.2 (habove _ this)
    have hrep : ∀ v : ℝ, 0 ≤ v →
        (∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v)).re ≤ M := fun v hv => by
      have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ⊆ ι :=
        fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * v) = 0 by rw [h0, zero_mul])
      have e1 : ∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v) =
          ((Real.exp (-σ * v) * (2 * (lagStructure Z b v).re) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs v).2,
          ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [e1, Complex.ofReal_re]
      calc Real.exp (-σ * v) * (2 * (lagStructure Z b v).re)
          ≤ Real.exp (-σ * v) * (M * Real.exp (σ * v)) :=
            mul_le_mul_of_nonneg_left (hMb v hv) (Real.exp_pos _).le
        _ = M := by
            rw [mul_left_comm, ← Real.exp_add, show -σ * v + σ * v = 0 by ring, Real.exp_zero,
              mul_one]
    have hpos₀ := hpos x₀
      ((mem_of_evenCoeff_ne_zero hx₀).elim id fun h => by
        rwa [show conj x₀ = x₀ from Complex.ext (by simp) (by simp [hx₀im])] at h)
      (by linarith) hx₀im
    have hnonpos := re_le_zero_of_re_tsum_exp_le (ι := ι) (lam := fun t => (t : ℂ) - σ)
      (q := fun t => evenCoeff Z b t) (hD0.subtype ι) (σ := x₀.re - σ) (by linarith) hle
      ⟨x₀, hx₀⟩ (Complex.ext (by simp) (by simp [hx₀im]))
      (fun t ht => Subtype.ext (sub_left_injective ht)) hrep
    exact absurd hnonpos (not_le.mpr hpos₀)
  · exact hne (evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs hσ hσh
      (fun x hx him => by
        by_contra h
        push Not at h
        exact hRne ⟨x, hmemR x hx him h⟩) hMb hz)

/-- **The lag family measures the abscissa, for a bump seeing every right zero.** -/
theorem re_le_iff_lag_twoBump_ge_neg_exp_of_pos (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hpos : ∀ x : ℂ, (1 / 2 + x) ∈ Z.carrier → 0 < x.re → x.im = 0 → 0 < (evenCoeff Z b x).re)
    (hsees : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → evenCoeff Z b (ρ - 1 / 2) ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v →
      -(C * Real.exp (σ * v)) ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re := by
  constructor
  · intro hre
    set A := 2 * (lagStructure Z b 0).re with hA
    set N := ∑' z : ℂ, ‖evenCoeff Z b z‖ with hN
    refine ⟨|A| + N, 0, fun v hv => ?_⟩
    have h := two_re_lagStructure_le_mul_exp Z hZ hb hbs (τ := σ) (fun z hz => by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · have := hre _ h; simp at this; linarith
      · have := hre _ h; simp at this; linarith) hv
    have he1 : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ hv)
    have h1 : |A| ≤ |A| * Real.exp (σ * v) := le_mul_of_one_le_right (abs_nonneg _) he1
    rw [re_W_lag_eq Z hZ hb hbs, add_mul]
    linarith [neg_abs_le A]
  · rintro ⟨C, V, hm⟩ ρ hρ
    by_contra hre
    push Not at hre
    exact hsees ρ hρ (by linarith)
      (evenCoeff_eq_zero_of_lag_ge_neg_exp_of_pos Z hZ hlt hb hbs hpos hσ hm
        (by simp; linarith))

/-! ## Box splines: transforms vanishing only on the real axis -/

theorem unif_neg (r x : ℝ) : unif r (-x) = unif r x := by
  unfold unif
  by_cases hx : x ∈ Icc (-r) r
  · have hx' : -x ∈ Icc (-r) r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · have hx' : -x ∉ Icc (-r) r := fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

/-- Box splines are even. -/
theorem upow_neg (r : ℝ) : ∀ (n : ℕ) (x : ℝ), upow r n (-x) = upow r n x
  | 0, x => unif_neg r x
  | n + 1, x => by
    show (unif r ⋆ upow r n) (-x) = (unif r ⋆ upow r n) x
    rw [convolution_def, convolution_def, ← integral_neg_eq_self]
    congr 1
    funext t
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [unif_neg, show -x - -t = -(x - t) by ring, upow_neg r n]

/-- The box spline `U_r^{⋆(n+1)}` as a complex bump. -/
def boxSpline (r : ℝ) (n : ℕ) (u : ℝ) : ℂ := (upow r n u : ℂ)

theorem contDiff_boxSpline {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ContDiff ℝ k (boxSpline r (k + 1)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_upow hr k)

theorem boxSpline_support {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ u, boxSpline r n u ≠ 0 → |u| ≤ (n + 1) * r := fun u hu => by
  have hmem : u ∈ Function.support (upow r n) := fun h => hu (by simp [boxSpline, h])
  exact abs_le.mpr (support_upow_subset hr n hmem)

theorem conj_paperFT_boxSpline (r : ℝ) (n : ℕ) (z : ℂ) :
    conj (paperFT (boxSpline r n) (conj z)) = paperFT (boxSpline r n) z :=
  conj_paperFT_ofReal_conj_of_even (upow_neg r n) z

theorem paperFT_boxSpline_neg (r : ℝ) (n : ℕ) (z : ℂ) :
    paperFT (boxSpline r n) (-z) = paperFT (boxSpline r n) z :=
  paperFT_ofReal_neg_of_even (upow_neg r n) z

/-- **Real-rootedness.** The transform of a box spline vanishes at no non-real point. -/
theorem paperFT_boxSpline_ne_zero {r : ℝ} (hr : 0 < r) (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    paperFT (boxSpline r n) z ≠ 0 := by
  have h := paperFT_upow r n z
  change paperFT (boxSpline r n) z = _ at h
  rw [h]
  exact pow_ne_zero _ (paperFT_unif_ne_zero hr hz)

/-- An off-line zero has a non-real spectral point. -/
theorem im_gammaOf_ne_zero {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) : (gammaOf ρ).im ≠ 0 := by
  have h := gammaOf_half_add (ρ - 1 / 2)
  rw [add_sub_cancel] at h
  rw [h]
  simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, zero_mul, one_mul, zero_add, neg_ne_zero]
  intro h0
  apply hρ
  norm_num at h0
  linarith

/-! ## Every width: the receiver -/

/-- The cubic spline of width `w`: `B_w = U_{w/4}^{⋆4}`, `C²`, supported in `[−w, w]`. -/
def splineBump (w : ℝ) : ℝ → ℂ := boxSpline (w / 4) 3

theorem contDiff_splineBump {w : ℝ} (hw : 0 < w) : ContDiff ℝ 2 (splineBump w) :=
  contDiff_boxSpline (by positivity) 2

theorem splineBump_support {w : ℝ} (hw : 0 < w) : ∀ u, splineBump w u ≠ 0 → |u| ≤ w :=
  fun u hu => (boxSpline_support (by positivity) 3 u hu).trans_eq (by push_cast; ring)

/-- **Every width decides the line.** For a tempered configuration without real zeros and every
width `w > 0`, all zeros lie on the critical line iff the Weil form is nonnegative on the
spline difference tests `B_w(t + v/2) − B_w(t − v/2)` at every lag `v ≥ V`. -/
theorem onLine_iff_lag_splineTwoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {w : ℝ} (hw : 0 < w) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (Z.W (twoBump (splineBump w) v (-1)) (twoBump (splineBump w) v (-1))).re :=
  onLine_iff_lag_twoBump_nonneg_of_conj_symm Z hZ hreal (contDiff_splineBump hw)
    (splineBump_support hw) (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _)
    (fun _ _ hre => paperFT_boxSpline_ne_zero (by positivity) 3 (im_gammaOf_ne_zero hre)) V

/-- **For `ζ`, every width in `(0, ½ log 2)`.** All nontrivial zeros lie on the critical line iff
the dyadic prime-window functional of the spline difference tests is nonnegative at every lag
`v ≥ V`. No width is exceptional. -/
theorem zeta_onLine_iff_lag_splinePrimeWindow_nonneg {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (lagPrimeWindowRHS v w (EF.weilTest (twoBump (splineBump w) v (-1))
        (twoBump (splineBump w) v (-1)))).re := by
  refine (onLine_iff_lag_splineTwoBump_nonneg _ temperedConfig_zetaZeroConfig
    zetaZeroConfig_im_ne_zero hw V).trans (forall_congr' fun v => imp_congr_right fun hv => ?_)
  rw [zeta_W_eq_literatureRHS (f := twoBump (splineBump w) v (-1))
    (contDiff_bumpTest (contDiff_splineBump hw) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (splineBump_support hw)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (splineBump_support hw) hw2 (hV.trans hv)]

/-- **RH from one explicit lag family at any width.** -/
theorem riemannHypothesis_iff_lag_splinePrimeWindow_nonneg {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    RiemannHypothesis ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (lagPrimeWindowRHS v w (EF.weilTest (twoBump (splineBump w) v (-1))
        (twoBump (splineBump w) v (-1)))).re :=
  riemannHypothesis_iff_zetaZeroConfig_onLine.trans
    (zeta_onLine_iff_lag_splinePrimeWindow_nonneg hw hw2 hV)

/-! ## Every width: the rate law -/

/-- The polar-free spline `B'' − B/4`, `B = U_{w/6}^{⋆6}` (`C⁴`, supported in `[−w, w]`). Its
transform is `−(z² + 1/4) B̂(z)`, vanishing at the poles `±i/2`. -/
def splinePolarFree (w u : ℝ) : ℂ :=
  deriv (deriv (boxSpline (w / 6) 5)) u - boxSpline (w / 6) 5 u / 4

theorem contDiff_splinePolarFree {w : ℝ} (hw : 0 < w) : ContDiff ℝ 2 (splinePolarFree w) := by
  have h4 : ContDiff ℝ 4 (boxSpline (w / 6) 5) := contDiff_boxSpline (by positivity) 4
  have h3 : ContDiff ℝ 3 (deriv (boxSpline (w / 6) 5)) := h4.deriv'
  exact h3.deriv'.sub ((h4.of_le (by norm_num)).div_const 4)

theorem boxSpline_six_support {w : ℝ} (hw : 0 < w) :
    ∀ u, boxSpline (w / 6) 5 u ≠ 0 → |u| ≤ w :=
  fun u hu => (boxSpline_support (by positivity) 5 u hu).trans_eq (by push_cast; ring)

theorem splinePolarFree_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w < |u|) : splinePolarFree w u = 0 := by
  have hsub : tsupport (boxSpline (w / 6) 5) ⊆ Icc (-w) w := closure_minimal
    (fun x hx => abs_le.mp (boxSpline_six_support hw x hx)) isClosed_Icc
  have hnot : u ∉ tsupport (boxSpline (w / 6) 5) := fun h => by
    have := abs_le.mpr (hsub h); linarith
  have hd1 : tsupport (deriv (boxSpline (w / 6) 5)) ⊆ tsupport (boxSpline (w / 6) 5) :=
    closure_minimal support_deriv_subset (isClosed_tsupport _)
  have hd2 : deriv (deriv (boxSpline (w / 6) 5)) u = 0 :=
    Function.notMem_support.mp fun h => hnot (hd1 (support_deriv_subset h))
  have h0 : boxSpline (w / 6) 5 u = 0 := by
    by_contra h; have := boxSpline_six_support hw u h; linarith
  simp [splinePolarFree, hd2, h0]

theorem splinePolarFree_support {w : ℝ} (hw : 0 < w) :
    ∀ u, splinePolarFree w u ≠ 0 → |u| ≤ w := fun u hu => by
  by_contra h
  push Not at h
  exact hu (splinePolarFree_eq_zero hw h)

theorem paperFT_splinePolarFree {w : ℝ} (hw : 0 < w) (z : ℂ) :
    paperFT (splinePolarFree w) z = -(z ^ 2 + 1 / 4) * paperFT (boxSpline (w / 6) 5) z := by
  have h4 : ContDiff ℝ 4 (boxSpline (w / 6) 5) := contDiff_boxSpline (by positivity) 4
  have hc2 : ContDiff ℝ 2 (boxSpline (w / 6) 5) := h4.of_le (by norm_num)
  have hcs : HasCompactSupport (boxSpline (w / 6) 5) :=
    hasCompactSupport_of_support_subset_abs (boxSpline_six_support hw)
  have hdd := paperFT_deriv_deriv hc2 hcs z
  have hdd2 : ContDiff ℝ 2 (deriv (deriv (boxSpline (w / 6) 5))) :=
    (h4.deriv' : ContDiff ℝ 3 _).deriv'
  have hi1 : Integrable
      (fun u : ℝ => deriv (deriv (boxSpline (w / 6) 5)) u * Complex.exp (I * z * u)) :=
    (hdd2.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.deriv.deriv.mul_right
  have hi0 : Integrable (fun u : ℝ => boxSpline (w / 6) 5 u * Complex.exp (I * z * u)) :=
    (hc2.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hi2 : Integrable (fun u : ℝ => boxSpline (w / 6) 5 u / 4 * Complex.exp (I * z * u)) :=
    (hi0.div_const 4).congr (ae_of_all _ fun u => by simp only; ring)
  unfold paperFT at hdd ⊢
  simp only [splinePolarFree, sub_mul]
  rw [integral_sub hi1 hi2, hdd]
  have : ∫ u : ℝ, boxSpline (w / 6) 5 u / 4 * Complex.exp (I * z * u) =
      (∫ u : ℝ, boxSpline (w / 6) 5 u * Complex.exp (I * z * u)) / 4 := by
    rw [← integral_div]; congr 1; funext u; ring
  rw [this]
  ring

theorem conj_paperFT_splinePolarFree {w : ℝ} (hw : 0 < w) (z : ℂ) :
    conj (paperFT (splinePolarFree w) (conj z)) = paperFT (splinePolarFree w) z := by
  rw [paperFT_splinePolarFree hw, paperFT_splinePolarFree hw, map_mul,
    conj_paperFT_boxSpline]
  congr 1
  simp only [map_neg, map_add, map_pow, Complex.conj_conj, map_div₀, map_one, map_ofNat]

theorem paperFT_splinePolarFree_neg {w : ℝ} (hw : 0 < w) (z : ℂ) :
    paperFT (splinePolarFree w) (-z) = paperFT (splinePolarFree w) z := by
  rw [paperFT_splinePolarFree hw, paperFT_splinePolarFree hw, paperFT_boxSpline_neg, neg_sq]

/-- The polar-free spline sees every point of the open strip off the real axis, except the two
poles. -/
theorem paperFT_splinePolarFree_ne_zero {w : ℝ} (hw : 0 < w) {z : ℂ} (hz : z.im ≠ 0)
    (hpole : z ^ 2 + 1 / 4 ≠ 0) : paperFT (splinePolarFree w) z ≠ 0 := by
  rw [paperFT_splinePolarFree hw]
  exact mul_ne_zero (neg_ne_zero.mpr hpole) (paperFT_boxSpline_ne_zero (by positivity) 5 hz)

/-- At an exponent `x` of the open strip, `x ≠ 0`, the spectral point `−ix` is neither real nor a
pole. -/
theorem neg_I_mul_sq_add_quarter_ne_zero {x : ℂ} (hx : |x.re| < 1 / 2) :
    (-(I * x)) ^ 2 + 1 / 4 ≠ 0 := by
  intro h
  have e : (-(I * x)) ^ 2 = -(x ^ 2) := by rw [neg_sq, mul_pow, Complex.I_sq]; ring
  have hx2 : x ^ 2 = 1 / 4 := by rw [e] at h; linear_combination -h
  have hre : x.re * x.re - x.im * x.im = 1 / 4 := by
    have := congrArg Complex.re hx2
    simpa [sq, Complex.mul_re] using this
  have him : x.re * x.im = 0 := by
    have := congrArg Complex.im hx2
    simp [sq, Complex.mul_im] at this
    linarith
  rcases mul_eq_zero.mp him with h0 | h0
  · rw [h0] at hre
    nlinarith [mul_self_nonneg x.im]
  · rw [h0] at hre
    have := abs_lt.mp hx
    nlinarith [this.1, this.2]

/-- **Every width measures the abscissa.** For a tempered configuration with zeros in
`0 < Re ρ < 1` and every width `w > 0`, all zeros satisfy `Re ρ ≤ ½ + σ` (`σ ≥ 0`) iff the Weil
form on the polar-free spline difference tests is `≥ −C e^{σv}` at all large lags. -/
theorem re_le_iff_polarFree_lag_splineTwoBump_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hgt : ∀ ρ ∈ Z.carrier, 0 < ρ.re) (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v →
      -(C * Real.exp (σ * v)) ≤
        (Z.W (twoBump (splinePolarFree w) v (-1)) (twoBump (splinePolarFree w) v (-1))).re := by
  have hb := contDiff_splinePolarFree hw
  have hbs := splinePolarFree_support hw
  have hbc : HasCompactSupport (splinePolarFree w) := hasCompactSupport_of_support_subset_abs hbs
  have hsym := conj_paperFT_splinePolarFree hw
  have heven := paperFT_splinePolarFree_neg hw
  -- an exponent of the open strip, with `Re ≠ 0`
  have hstrip : ∀ x : ℂ, (1 / 2 + x) ∈ Z.carrier → |x.re| < 1 / 2 := fun x hx => by
    have h1 := hgt _ hx
    have h2 := hlt _ hx
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at h1 h2
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine re_le_iff_lag_twoBump_ge_neg_exp_of_pos Z hZ hlt hb hbs
    (fun x hx hx0 him => re_evenCoeff_pos_of_conj_symm Z hb.continuous hbc hsym heven hx him
      (paperFT_splinePolarFree_ne_zero hw (by simp; exact hx0.ne') ?_))
    (fun ρ hρ hre => evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc hsym heven hρ
      (paperFT_splinePolarFree_ne_zero hw (im_gammaOf_ne_zero (by linarith)) ?_)) hσ
  · exact neg_I_mul_sq_add_quarter_ne_zero (hstrip x hx)
  · have hρ' : (1 / 2 + (ρ - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact hρ
    have := neg_I_mul_sq_add_quarter_ne_zero (hstrip _ hρ')
    rwa [show -(I * (ρ - 1 / 2)) = gammaOf ρ by rw [gammaOf, Complex.div_I]; ring] at this

/-- **For `ζ`, every width in `(0, ½ log 2)` measures the abscissa.** Every nontrivial zero has
`Re ρ ≤ ½ + σ` iff the dyadic prime-window functional of the polar-free spline difference tests is
`≥ −C e^{σv}` at all large lags. -/
theorem zeta_re_le_iff_polarFree_lag_splinePrimeWindow_ge_neg_exp {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
      -(C * Real.exp (σ * v)) ≤
        (lagPrimeWindowRHS v w (EF.weilTest (twoBump (splinePolarFree w) v (-1))
          (twoBump (splinePolarFree w) v (-1)))).re := by
  have hbs := splinePolarFree_support hw
  have hW : ∀ v : ℝ, 0 ≤ v → (zetaZeroConfig.W (twoBump (splinePolarFree w) v (-1))
      (twoBump (splinePolarFree w) v (-1))).re =
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (splinePolarFree w) v (-1))
        (twoBump (splinePolarFree w) v (-1)))).re := fun v hv => by
    rw [zeta_W_eq_literatureRHS (f := twoBump (splinePolarFree w) v (-1))
      (contDiff_bumpTest (contDiff_splinePolarFree hw) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs hbs) v (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS hbs hw2 hv]
  rw [re_le_iff_polarFree_lag_splineTwoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig
    (fun ρ hρ => hρ.2.1) (fun ρ hρ => hρ.2.2) hw hσ]
  constructor
  · rintro ⟨C, V, h⟩
    exact ⟨C, max V 0, le_max_right _ _, fun v hv => by
      rw [← hW v ((le_max_right _ _).trans hv)]
      exact h v ((le_max_left _ _).trans hv)⟩
  · rintro ⟨C, V, hV, h⟩
    exact ⟨C, V, fun v hv => by
      rw [hW v (hV.trans hv)]
      exact h v hv⟩

/-- The admissible negativity rates of the polar-free spline prime windows of width `w`. -/
def splineLagRates (w : ℝ) : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
    (lagPrimeWindowRHS v w (EF.weilTest (twoBump (splinePolarFree w) v (-1))
      (twoBump (splinePolarFree w) v (-1)))).re}

/-- **The zero width is the exponent of the spline prime windows, at every width.** For every
`w ∈ (0, ½ log 2)`, the admissible rates form the half-line `[zetaZeroWidth, ∞)`, so the zero
width is their infimum. -/
theorem zetaZeroWidth_eq_sInf_splineLagRates {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) :
    zetaZeroWidth = sInf (splineLagRates w) := by
  have hset : splineLagRates w = Ici zetaZeroWidth := by
    ext σ
    rw [mem_Ici]
    constructor
    · rintro ⟨hσ, h⟩
      exact (zetaZeroWidth_le_iff_re_le hσ).mpr
        ((zeta_re_le_iff_polarFree_lag_splinePrimeWindow_ge_neg_exp hw hw2 hσ).mpr h)
    · intro hσ
      have hσ0 : 0 ≤ σ := zetaZeroWidth_nonneg.trans hσ
      exact ⟨hσ0, (zeta_re_le_iff_polarFree_lag_splinePrimeWindow_ge_neg_exp hw hw2 hσ0).mp
        ((zetaZeroWidth_le_iff_re_le hσ0).mp hσ)⟩
  rw [hset, csInf_Ici]

end GaloisForLFunctions.SquareRootThreshold
