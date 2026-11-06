import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ThePoissonJensenIdentity
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringNormalization
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffGramKernel

/-!
# The scattering matrix of the modular surface is a Blaschke product

With `φ` the scattering entry of the Eisenstein series, the function

`S(s) = φ(s)(s − 1)/s = ξ(2s − 1)/ξ(2s)`

is an inner function of the half-plane `Re s > ½`, and it is exactly the Blaschke product of its zeros
`a_ρ = (1 + ρ)/2`, one for each nontrivial zero of `ζ` with multiplicity:

`−log |S(w)| = Σ_ρ G(w, (1 + ρ)/2)`, with `G` the Green kernel of the half-plane
(`hasSum_greenKernel_scatteringInner`).

So `S` has no singular inner factor and no outer factor.  Under RH every `a_ρ` lies on `Re s = ¾`.

**Mechanism.**  The Hadamard product `Ξ(z) = Ξ(0) Π (1 − z/a)e^{z/a}` in the spectral variable has no
exponential factor, so `log|S|` is a sum of `log|ρ + 1 − 2w| − log|ρ − 2w| − Re 1/(ρ − ½)`.  The
involution `ρ ↦ 1 − ρ̄` makes `Re 1/(ρ − ½)` odd and exchanges `|ρ − 2w|` with `|ρ + 2w̄ − 1|`.

**Dictionary.**  The zeros of `S` are the reflected resonances: `msA u = 0` gives `S(½ − u) = 0`
(`scatteringInner_eq_zero_of_msA`).  The Gram matrix of the truncated resonant states is the Szegő
kernel of `Re s > ½` at these zeros, times `msB` (`integral_resonant_gram_eq_szego`).  On `Re s = ½`,
`|S| = 1` by the functional equation (`norm_scatteringInner_line`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate
open RHTower
open GaloisForLFunctions.ArithmeticInnerFunctionTheory (greenKernel)
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringNormalization
  (scatteringEntry archimedeanFactor)

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

noncomputable section

/-- The scattering inner function `S(s) = ξ(2s − 1)/ξ(2s)`. -/
def scatteringInner (s : ℂ) : ℂ := xi (2 * s - 1) / xi (2 * s)

theorem xi_two_mul_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) : xi (2 * s) ≠ 0 := by
  intro h
  have hstrip := xi_zero_re_mem_open_unit h
  have hre : (2 * s).re = 2 * s.re := by simp
  rw [hre] at hstrip
  linarith [hstrip.2]

/-- `Γ_ℝ(2s − 1) = A(s) Γ_ℝ(2s)` with the archimedean factor `A(s) = √π Γ(s − ½)/Γ(s)`. -/
theorem gammaR_two_mul_sub_one {s : ℂ} (hs : 0 < s.re) :
    Gammaℝ (2 * s - 1) = archimedeanFactor s * Gammaℝ (2 * s) := by
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hexp : ((Real.pi : ℝ) : ℂ) ^ (-(2 * s - 1) / 2)
      = ((Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((Real.pi : ℝ) : ℂ) ^ (-(2 * s) / 2) := by
    rw [← Complex.cpow_add _ _ hπ]
    congr 1
    ring
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, archimedeanFactor, hexp,
    show (2 * s - 1) / 2 = s - 1 / 2 by ring, show 2 * s / 2 = s by ring]
  field_simp

/-- **`S` is the normalized scattering entry:** `φ(s)(s − 1)/s = ξ(2s − 1)/ξ(2s)`. -/
theorem sub_one_div_mul_scatteringEntry {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    (s - 1) / s * scatteringEntry s = scatteringInner s := by
  have hs0 : s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs
    linarith
  have h2 : (2 * s - 1).re = 2 * s.re - 1 := by simp
  have h3 : (2 * s).re = 2 * s.re := by simp
  have h2pos : 0 < (2 * s - 1).re := by rw [h2]; linarith
  have h3pos : 0 < (2 * s).re := by rw [h3]; linarith
  have h20 : 2 * s - 1 ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at h2pos
    exact lt_irrefl _ h2pos
  have h21 : 2 * s - 1 ≠ 1 := fun h => hs1 (by linear_combination h / 2)
  have h30 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have h31 : 2 * s ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [h3, Complex.one_re] at this
    linarith
  have hζ : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [h3]; linarith)
  have hG : Gammaℝ (2 * s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h3pos
  rw [scatteringInner, scatteringEntry, xi_eq_xiUnit_mul_zeta h20 h21 h2pos,
    xi_eq_xiUnit_mul_zeta h30 h31 h3pos, xiUnit, xiUnit,
    gammaR_two_mul_sub_one (by linarith : 0 < s.re)]
  generalize archimedeanFactor s = A
  generalize riemannZeta (2 * s - 1) = z₁ at *
  generalize riemannZeta (2 * s) = z₂ at *
  generalize Gammaℝ (2 * s) = g at *
  have h1' : 2 * s - 1 ≠ 0 := h20
  field_simp
  ring

/-! ### The Hadamard product in logarithmic form -/

theorem eventually_le_norm_xiSpectralPoint {M : ℝ} (hM : 0 < M) :
    ∀ᶠ q : XiZeroCopy in cofinite, M ≤ ‖xiSpectralPoint q‖ := by
  have hs := xiSpectralPoint_inv_sq_summable
  have hε : 0 < 1 / M ^ (2 : ℕ) := by positivity
  filter_upwards [hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)] with q hq
  have hq0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hlt : ‖xiSpectralPoint q‖ ^ (2 : ℕ) > M ^ (2 : ℕ) := by
    rwa [gt_iff_lt, one_div_lt_one_div (by positivity) (by positivity)] at hq
  exact (lt_of_pow_lt_pow_left₀ 2 hq0.le hlt).le

/-- `|log |(1 − x)e^x|| ≤ |x|²` for `|x| ≤ ½`. -/
theorem abs_log_norm_weierstrassE1_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    |Real.log ‖weierstrassE1 x‖| ≤ ‖x‖ ^ 2 := by
  have hx1 : ‖-x‖ < 1 := by rw [norm_neg]; linarith
  have hlog := Complex.norm_log_one_add_sub_self_le hx1
  have h1x : (1 : ℂ) + -x ≠ 0 := by
    intro h
    have : x = 1 := by linear_combination -h
    rw [this, norm_one] at hx
    linarith
  have hEnorm : ‖weierstrassE1 x‖
      = ‖(1 : ℂ) + -x‖ * Real.exp x.re := by
    rw [weierstrassE1, norm_mul, Complex.norm_exp, sub_eq_add_neg]
  have hre : Real.log ‖weierstrassE1 x‖
      = (Complex.log (1 + -x) - -x).re := by
    rw [hEnorm, Real.log_mul (norm_ne_zero_iff.mpr h1x) (Real.exp_ne_zero _), Real.log_exp,
      Complex.sub_re, Complex.log_re, Complex.neg_re]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hlog.trans ?_)
  rw [norm_neg]
  have hnn : 0 ≤ ‖x‖ := norm_nonneg x
  have hden : (1 - ‖x‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hsq : 0 ≤ ‖x‖ ^ 2 := by positivity
  calc ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖x‖ ^ 2 := by ring

/-- **The Hadamard product in logarithmic form.** -/
theorem hasSum_log_norm_weierstrassE1 {z : ℂ} (hz : XiC z ≠ 0) :
    HasSum (fun q : XiZeroCopy =>
        Real.log ‖weierstrassE1 (z / xiSpectralPoint q)‖)
      (Real.log ‖XiC z‖ - Real.log ‖XiC 0‖) := by
  have hsum : Summable (fun q : XiZeroCopy =>
      Real.log ‖weierstrassE1 (z / xiSpectralPoint q)‖) := by
    refine Summable.of_norm_bounded_eventually
      (xiSpectralPoint_inv_sq_summable.mul_left (‖z‖ ^ 2)) ?_
    have hM : 0 < 2 * ‖z‖ + 1 := by positivity
    filter_upwards [eventually_le_norm_xiSpectralPoint hM] with q hq
    have hq0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hx : ‖z / xiSpectralPoint q‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ hq0]
      linarith
    rw [Real.norm_eq_abs]
    refine (abs_log_norm_weierstrassE1_le hx).trans (le_of_eq ?_)
    rw [norm_div]
    field_simp
  have hmul := xiCanonicalProduct_multipliable z
  have hnormprod := hmul.hasProd.map (normHom : ℂ →*₀ ℝ) continuous_norm
  have hprodne : xiCanonicalProduct z ≠ 0 := by
    intro h0
    apply hz
    rw [XiC_eq_constant_mul_canonicalProduct, Pi.mul_apply, h0, mul_zero]
  have hne : ∀ q : XiZeroCopy,
      weierstrassE1 (z / xiSpectralPoint q) ≠ 0 := by
    intro q h0
    have hq := xiSpectralPoint_ne_zero q
    have h1 : (1 : ℂ) - z / xiSpectralPoint q = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (Complex.exp_ne_zero _)
    have hzq : z = xiSpectralPoint q := by
      field_simp at h1
      linear_combination -h1
    apply hprodne
    rw [hzq]
    exact xiCanonicalProduct_eq_zero q
  have hexp := hsum.hasSum.rexp
  have hconv : (Real.exp ∘ fun q : XiZeroCopy =>
      Real.log ‖weierstrassE1 (z / xiSpectralPoint q)‖)
      = (normHom : ℂ →*₀ ℝ) ∘ fun q : XiZeroCopy =>
        weierstrassE1 (z / xiSpectralPoint q) := by
    funext q
    simp only [Function.comp_apply, normHom_apply]
    exact Real.exp_log (norm_pos_iff.mpr (hne q))
  rw [hconv] at hexp
  have hunique := hexp.unique hnormprod
  have hval : Real.log ‖XiC z‖ - Real.log ‖XiC 0‖ = ∑' q : XiZeroCopy,
      Real.log ‖weierstrassE1 (z / xiSpectralPoint q)‖ := by
    have hX0 : XiC 0 ≠ 0 := XiC_zero_ne
    have hXz : XiC z = XiC 0 * xiCanonicalProduct z := by
      rw [XiC_eq_constant_mul_canonicalProduct, Pi.mul_apply]
    have hnorm : ‖xiCanonicalProduct z‖ = Real.exp (∑' q : XiZeroCopy,
        Real.log ‖weierstrassE1 (z / xiSpectralPoint q)‖) :=
      hunique.symm
    rw [hXz, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hX0) (norm_ne_zero_iff.mpr hprodne),
      hnorm, Real.log_exp]
    ring
  rw [hval]
  exact hsum.hasSum

/-! ### The involution `ρ ↦ 1 − ρ̄` -/

/-- The involution `ρ ↦ 1 − ρ̄` on zero copies. -/
def xiZeroCopyStar : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv

theorem xiZeroCopyStar_val (q : XiZeroCopy) :
    ((xiZeroCopyStar q).1 : ℂ) = 1 - conj (q.1 : ℂ) := by
  have h := xiZeroCopy_reflect_val (xiZeroCopyConjEquiv q)
  have hc : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
  rw [hc] at h
  exact h

/-- An odd function of the involution has total sum zero. -/
theorem tsum_eq_zero_of_star_odd {g : XiZeroCopy → ℝ} (hg : ∀ q, g (xiZeroCopyStar q) = -g q) :
    ∑' q, g q = 0 := by
  have h := xiZeroCopyStar.tsum_eq g
  simp only [hg, tsum_neg] at h
  linarith

/-- `log |ρ + α + δ| − log |ρ + α|` is summable over the zeros for real `δ`: the two squared norms
differ by a bounded amount. -/
theorem summable_log_norm_add_real_sub (α : ℂ) (δ : ℝ) :
    Summable (fun q : XiZeroCopy =>
      Real.log ‖(q.1 : ℂ) + α + δ‖ - Real.log ‖(q.1 : ℂ) + α‖) := by
  set R : ℝ := 1 + |α.re| with hR
  set D : ℝ := 2 * |δ| * R + δ ^ 2 + 1 with hD
  have hD0 : 0 < D := by rw [hD, hR]; positivity
  have hsumm : Summable (fun q : XiZeroCopy => 8 * D * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  refine Summable.of_norm_bounded_eventually hsumm ?_
  set M : ℝ := 2 * ‖α + 1 / 2‖ + 4 * Real.sqrt D + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  filter_upwards [eventually_le_norm_xiSpectralPoint hM0] with q hq
  have hq0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  set y : ℂ := (q.1 : ℂ) + α with hy
  have hspec : ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := norm_xiSpectralPoint q
  have hylower : ‖xiSpectralPoint q‖ / 2 ≤ ‖y‖ := by
    have htri : ‖(q.1 : ℂ) - 1 / 2‖ ≤ ‖y‖ + ‖α + 1 / 2‖ := by
      have heq : (q.1 : ℂ) - 1 / 2 = y - (α + 1 / 2) := by rw [hy]; ring
      rw [heq]
      exact norm_sub_le _ _
    have hsq : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    rw [← hspec] at htri
    rw [hM] at hq
    linarith
  have hsqrtD : Real.sqrt D ≤ ‖y‖ / 2 := by
    have hsq : 0 ≤ ‖α + 1 / 2‖ := norm_nonneg _
    rw [hM] at hq
    linarith
  have hy2D : 4 * D ≤ ‖y‖ ^ 2 := by
    have h := Real.mul_self_sqrt hD0.le
    have hsq0 := Real.sqrt_nonneg D
    nlinarith [mul_self_le_mul_self hsq0 hsqrtD]
  have hy0 : 0 < ‖y‖ := by
    have h1 : 0 < ‖xiSpectralPoint q‖ / 2 := by positivity
    linarith
  -- the difference of squared norms
  have hxsq : ‖y + δ‖ ^ 2 = ‖y‖ ^ 2 + 2 * δ * y.re + δ ^ 2 := by
    have h1 : ‖y + δ‖ ^ 2 = Complex.normSq (y + δ) := (Complex.normSq_eq_norm_sq _).symm
    have h2 : ‖y‖ ^ 2 = Complex.normSq y := (Complex.normSq_eq_norm_sq _).symm
    rw [h1, h2, Complex.normSq_add]
    simp [Complex.normSq_ofReal]
    ring
  have hyre : |y.re| ≤ R := by
    have h0 := (xiZeroCopy_re_pos q).le
    have h1 := (xiZeroCopy_re_lt_one q).le
    have hre : y.re = (q.1 : ℂ).re + α.re := by simp [hy]
    rw [hre, hR]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg h0]
    linarith
  set v : ℝ := (2 * δ * y.re + δ ^ 2) / ‖y‖ ^ 2 with hv
  have hy2 : 0 < ‖y‖ ^ 2 := by positivity
  have hnum : |2 * δ * y.re + δ ^ 2| ≤ D := by
    have h1 : |2 * δ * y.re| ≤ 2 * |δ| * R := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hyre (by positivity)
    have h2 : |δ ^ 2| = δ ^ 2 := abs_of_nonneg (sq_nonneg δ)
    calc |2 * δ * y.re + δ ^ 2| ≤ |2 * δ * y.re| + |δ ^ 2| := abs_add_le _ _
      _ ≤ _ := by rw [h2, hD]; linarith
  have hvabs : |v| ≤ D / ‖y‖ ^ 2 := by
    rw [hv, abs_div, abs_of_pos hy2]
    exact div_le_div_of_nonneg_right hnum hy2.le
  have hv4 : |v| ≤ 1 / 4 := by
    refine hvabs.trans ?_
    rw [div_le_div_iff₀ hy2 (by norm_num)]
    linarith
  have hxy : ‖y + δ‖ ^ 2 = ‖y‖ ^ 2 * (1 + v) := by
    rw [hxsq, hv]
    field_simp
  have hv1 : 0 < 1 + v := by
    have := abs_le.mp hv4
    linarith [this.1]
  have hlog : Real.log ‖y + δ‖ - Real.log ‖y‖ = Real.log (1 + v) / 2 := by
    have h := congrArg Real.log hxy
    rw [Real.log_pow, Real.log_mul hy2.ne' hv1.ne', Real.log_pow] at h
    push_cast at h
    linarith
  have habslog : |Real.log (1 + v)| ≤ 2 * |v| := by
    rw [abs_le]
    have hup := Real.log_le_sub_one_of_pos hv1
    have hlow := Real.one_sub_inv_le_log_of_pos hv1
    have hle := le_abs_self v
    have hge := neg_abs_le v
    constructor
    · have : -(2 * |v|) ≤ 1 - (1 + v)⁻¹ := by
        have h34 : 3 / 4 ≤ 1 + v := by linarith
        have hinv : (1 + v)⁻¹ * (1 + v) = 1 := inv_mul_cancel₀ hv1.ne'
        have hinv0 : 0 < (1 + v)⁻¹ := inv_pos.mpr hv1
        nlinarith
      linarith
    · linarith
  have hgoal : |Real.log ‖y + δ‖ - Real.log ‖y‖| ≤ D / ‖y‖ ^ 2 := by
    rw [hlog, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [Real.norm_eq_abs]
  refine hgoal.trans ?_
  have hsq : ‖xiSpectralPoint q‖ ^ 2 / 4 ≤ ‖y‖ ^ 2 := by
    have hh : 0 ≤ ‖xiSpectralPoint q‖ / 2 := by positivity
    nlinarith
  have hq2 : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
  calc D / ‖y‖ ^ 2 ≤ D / (‖xiSpectralPoint q‖ ^ 2 / 4) :=
        div_le_div_of_nonneg_left hD0.le (by positivity) hsq
    _ ≤ 8 * D * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        linarith

/-! ### The Blaschke product -/

theorem re_inv_sub_half_star (q : XiZeroCopy) :
    (((xiZeroCopyStar q).1 : ℂ) - 1 / 2)⁻¹.re = -(((q.1 : ℂ) - 1 / 2)⁻¹).re := by
  rw [xiZeroCopyStar_val]
  have h : (1 : ℂ) - conj (q.1 : ℂ) - 1 / 2 = -conj ((q.1 : ℂ) - 1 / 2) := by
    simp only [map_sub, map_one, map_div₀, map_ofNat]
    ring
  rw [h, inv_neg, Complex.neg_re, ← map_inv₀, Complex.conj_re]

/-- `Re 1/(ρ − ½)` is summable and odd, so its sum vanishes. -/
theorem hasSum_re_inv_sub_half :
    HasSum (fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re) 0 := by
  have hsum : Summable (fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re) := by
    refine Summable.of_norm_bounded xiSpectralPoint_inv_sq_summable fun q => ?_
    have hne := xiZeroCopy_sub_half_ne_zero q
    have hn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr hne
    have hval : (((q.1 : ℂ) - 1 / 2)⁻¹).re
        = ((q.1 : ℂ) - 1 / 2).re / ‖(q.1 : ℂ) - 1 / 2‖ ^ 2 := by
      rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos (by positivity : 0 < ‖(q.1 : ℂ) - 1 / 2‖ ^ 2),
      norm_xiSpectralPoint]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    have hre : ((q.1 : ℂ) - 1 / 2).re = (q.1 : ℂ).re - 1 / 2 := by simp
    rw [hre, abs_le]
    constructor <;> linarith
  have h0 := tsum_eq_zero_of_star_odd (g := fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re)
    re_inv_sub_half_star
  rw [← h0]
  exact hsum.hasSum

/-- The logarithm of one spectral Weierstrass factor at `z = −i(c − ½)`. -/
theorem log_norm_weierstrassE1_spectral (c : ℂ) (q : XiZeroCopy) (hc : (q.1 : ℂ) - c ≠ 0) :
    Real.log ‖weierstrassE1 (((c - 1 / 2) * (-I)) / xiSpectralPoint q)‖
      = Real.log ‖(q.1 : ℂ) - c‖ - Real.log ‖(q.1 : ℂ) - 1 / 2‖
        + ((c - 1 / 2) * ((q.1 : ℂ) - 1 / 2)⁻¹).re := by
  have hne := xiZeroCopy_sub_half_ne_zero q
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
  have hdiv : ((c - 1 / 2) * (-I)) / xiSpectralPoint q = (c - 1 / 2) * ((q.1 : ℂ) - 1 / 2)⁻¹ := by
    rw [xiSpectralPoint]
    field_simp
  have hone : (1 : ℂ) - (c - 1 / 2) * ((q.1 : ℂ) - 1 / 2)⁻¹
      = ((q.1 : ℂ) - c) / ((q.1 : ℂ) - 1 / 2) := by
    field_simp
    ring
  rw [hdiv, weierstrassE1, hone, norm_mul, Complex.norm_exp,
    Real.log_mul (norm_ne_zero_iff.mpr (div_ne_zero hc hne)) (Real.exp_ne_zero _), Real.log_exp,
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hne)]

theorem xiC_spectral (c : ℂ) : XiC ((c - 1 / 2) * (-I)) = xi c := by
  rw [XiC]
  congr 1
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (-(c - 1 / 2)) * hI

/-- **The scattering inner function is the Blaschke product of its zeros.**  For `Re w > ½` off the
zeros, `−log |S(w)| = Σ_ρ G(w, (1 + ρ)/2)`, over the nontrivial zeros of `ζ` with multiplicity. -/
theorem hasSum_greenKernel_scatteringInner {w : ℂ} (hw : 1 / 2 < w.re) (hne : xi (2 * w - 1) ≠ 0) :
    HasSum (fun q : XiZeroCopy => greenKernel w ((1 + (q.1 : ℂ)) / 2))
      (-Real.log ‖scatteringInner w‖) := by
  have hne2 := xi_two_mul_ne_zero hw
  have hS₁ := hasSum_log_norm_weierstrassE1 (z := ((2 * w - 1) - 1 / 2) * (-I))
    (by rw [xiC_spectral]; exact hne)
  have hS₂ := hasSum_log_norm_weierstrassE1 (z := ((2 * w) - 1 / 2) * (-I))
    (by rw [xiC_spectral]; exact hne2)
  rw [xiC_spectral] at hS₁ hS₂
  have hA : ∀ q : XiZeroCopy, (q.1 : ℂ) - (2 * w - 1) ≠ 0 := fun q h => hne (by
    rw [← sub_eq_zero.mp h]
    exact xi_xiZeroCopy_eq_zero q)
  have hB : ∀ q : XiZeroCopy, (q.1 : ℂ) - 2 * w ≠ 0 := fun q h => hne2 (by
    rw [← sub_eq_zero.mp h]
    exact xi_xiZeroCopy_eq_zero q)
  -- `log |S|` is the sum of the differences of the factors
  have hAB : HasSum (fun q : XiZeroCopy =>
      Real.log ‖(q.1 : ℂ) - (2 * w - 1)‖ - Real.log ‖(q.1 : ℂ) - 2 * w‖)
      (Real.log ‖scatteringInner w‖) := by
    have h := (hS₁.sub hS₂).add hasSum_re_inv_sub_half
    have hval : Real.log ‖xi (2 * w - 1)‖ - Real.log ‖XiC 0‖
        - (Real.log ‖xi (2 * w)‖ - Real.log ‖XiC 0‖) + 0 = Real.log ‖scatteringInner w‖ := by
      rw [scatteringInner, norm_div, Real.log_div (norm_ne_zero_iff.mpr hne)
        (norm_ne_zero_iff.mpr hne2)]
      ring
    rw [hval] at h
    refine h.congr_fun ?_ |> fun h' => h'
    sorry
  sorry

end

end GaloisForLFunctions.RenormalizedIntersectionTheory
