import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.ZetaOffLineWeightedDensity
import GaloisForLFunctions.RHTower.ProjectiveReciprocalHorizonWardSeamSaturation
import GaloisForLFunctions.RHTower.GaussianCentralGapExtremalSignChanges

/-!
# Canonical Rigidity, Sharp Gap Bifurcation, and Sign Changes of a Finite Prime-Error Oscillation

Suppose the prime number theorem error admits a finite trigonometric oscillation

`|ψ(x) − x − x^β T(log x)| ≤ C x^{β−η}`

with `β > 1/2`, `η > 0`, and `T = finiteOscillation S c ≠ 0`. This module establishes six
unconditional structural laws for such expansions:

1. **Unconditional `1/2` remainder floor** (`half_le_of_oscillationError_bound`):
   No finite complex oscillation `∑_{ω ∈ S} d(ω) x^{β+iω}` can approximate `ψ(x) − x` to `O(x^{σ₀})`
   with `σ₀ < 1/2`, because reflection `ρ ↦ 1 − ρ` and zero location would confine the infinite
   divisor `XiZeroCopy` to bounded height.
2. **Exact multiplicity quantization** (`oscillation_coeff_eq_neg_zeta_order_div`,
   `oscillationCoeff_eq_neg_zeta_order_div`, `oscillationCoeff_zero_eq_zero`):
   Every witness pins `β = Θ = zetaZeroAbscissa < 1` and forces every Fourier coefficient on all of
   `ℝ` to equal `oscillationCoeff S c μ = −ord_{s = Θ + iμ}(ζ) / (Θ + iμ)`, with vanishing constant
   mode `oscillationCoeff S c 0 = 0` since `ζ(Θ) ≠ 0` on `(0, 1)`.
3. **Canonical uniqueness** (`primeErrorFiniteOscillation_unique_abscissa_and_profile`):
   Both the leading exponent `β = Θ` and the profile `T : ℝ → ℝ` are uniquely determined
   independently of `(S, c, η, C, x₀)`.
4. **Sharp secondary-abscissa power-saving bifurcation** (`zetaSecondAbscissa`,
   `eta_le_zetaZeroAbscissa_sub_secondAbscissa`, `eta_le_zetaZeroAbscissa_sub_asymptoticAbscissa`,
   `exists_primeErrorFiniteOscillation_of_lt_gap`):
   With `Θ₂ = sSup ({1/2} ∪ {Re q : Re q < Θ})`, every valid saving satisfies `η ≤ Θ − Θ₂` (hence
   `η ≤ Θ − Θ_∞` and `η ≤ Θ − 1/2`), while under `¬ AsymptoticAbscissaLaw` we have `Θ₂ < Θ` and
   every `0 < η < Θ − Θ₂` is achieved by the canonical top-layer profile.
5. **Bounded-logarithmic-gap sign changes**
   (`exists_bounded_log_gap_sign_changes_of_primeErrorIsFiniteOscillation`):
   Under `PrimeErrorIsFiniteOscillation`, there exist `L, δ > 0` and `U₀` such that every
   logarithmic window `[u₀, u₀ + L]` (`u₀ ≥ U₀`) contains points where `ψ(e^u) − e^u > δ e^{Θu}`
   and `ψ(e^{u'}) − e^{u'} < −δ e^{Θu'}`.
6. **Alternating prime-power parity identity and oscillation transfer**
   (`sum_alternating_vonMangoldt_eq`, `alternating_vonMangoldt_finiteOscillation`):
   For all `x ≥ 1`, `∑_{1 ≤ n ≤ ⌊x⌋₊} (−1)^n Λ(n) = 2 ⌊log₂ ⌊x⌋₊⌋ log 2 − ψ(x)`, and any finite
   oscillation of `ψ(x) − x` transfers with the identical remainder exponent `β − η`.
-/

open Complex Filter Topology MeasureTheory Set
open ArithmeticFunction (vonMangoldt)
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ### 1. Unconditional `1/2` barrier for finite-oscillation remainders -/

/-- `XiZeroCopy` is infinite via the ordered positive ordinate equivalence `ℕ ≃ XiPositiveZeroCopy`. -/
theorem infinite_xiZeroCopy : Infinite XiZeroCopy :=
  Infinite.of_injective (fun n : ℕ => (xiOrderedPositiveZeroCopyEquiv n).1)
    fun _ _ h => xiOrderedPositiveZeroCopyEquiv.injective (Subtype.ext h)

/-- **Unconditional `1/2` remainder floor.** No finite complex oscillation at abscissa `β` can
approximate `ψ(x) − x` with error `O(x^{σ₀})` for any `σ₀ < 1/2`. -/
theorem half_le_of_oscillationError_bound {β σ₀ C x₀ : ℝ} {S : Finset ℝ} {d : ℝ → ℂ}
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) :
    1 / 2 ≤ σ₀ := by
  by_contra hlt
  push Not at hlt
  set M : ℝ := ∑ ω ∈ S, |ω| with hM
  have hsub : (Set.univ : Set XiZeroCopy) ⊆ {q : XiZeroCopy | |(q.1 : ℂ).im| ≤ M} := by
    intro q _
    rcases le_or_gt (1 / 2 : ℝ) (q.1 : ℂ).re with hge | hlt_half
    · obtain ⟨ω, hω, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb
        (lt_of_lt_of_le hlt hge) (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
      have him : (q.1 : ℂ).im = ω := by rw [heq]; simp
      show |(q.1 : ℂ).im| ≤ M
      rw [him]
      exact Finset.single_le_sum (f := fun μ : ℝ => |μ|) (fun _ _ => abs_nonneg _) hω
    · set q' : XiZeroCopy := xiZeroCopyReflectEquiv q
      have hq'_val : (q'.1 : ℂ) = 1 - (q.1 : ℂ) := rfl
      have hq'_re : σ₀ < (q'.1 : ℂ).re := by
        rw [hq'_val, Complex.sub_re, Complex.one_re]
        linarith
      obtain ⟨ω, hω, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb
        hq'_re (xiZeroCopy_ne_one q') (riemannZeta_eq_zero_of_xiZeroCopy q')
      have him : -(q.1 : ℂ).im = ω := by
        have h := congrArg Complex.im heq
        simpa [hq'_val] using h
      show |(q.1 : ℂ).im| ≤ M
      rw [← abs_neg, him]
      exact Finset.single_le_sum (f := fun μ : ℝ => |μ|) (fun _ _ => abs_nonneg _) hω
  haveI : Infinite XiZeroCopy := infinite_xiZeroCopy
  exact Set.infinite_univ ((finite_abs_im_le M).subset hsub)

/-! ### 2. Exact multiplicity quantization of oscillation coefficients -/

/-- **Residue-order quantization for `zetaResidueUnit`.** In any complex finite-oscillation
expansion `ψ(x) − x = ∑_{ω ∈ S} d(ω) x^{β+iω} + O(x^{σ₀})` with `σ₀ < β` and `0 < β`, each
coefficient `d(ω₀)` (`ω₀ ∈ S`) equals `−ord_{s = β+iω₀}(zetaResidueUnit) / (β + iω₀)`. -/
theorem oscillation_coeff_eq_neg_zetaResidueUnit_order_div {β σ₀ C x₀ : ℝ} {S : Finset ℝ}
    {d : ℝ → ℂ} (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀)
    {ω₀ : ℝ} (hω₀ : ω₀ ∈ S) (hσβ : σ₀ < β) (hβ0 : 0 < β) :
    d ω₀ =
      -(((analyticOrderAt zetaResidueUnit ((β : ℂ) + I * ω₀)).toNat : ℕ) : ℂ) /
        ((β : ℂ) + I * ω₀) := by
  classical
  set s₀ : ℂ := (β : ℂ) + I * ω₀ with hs₀
  have hs₀_re : s₀.re = β := by simp [hs₀]
  have hs₀_ne : s₀ ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hs₀_re
    linarith
  have hZa : AnalyticAt ℂ zetaResidueUnit s₀ := analyticAt_zetaResidueUnit s₀
  have htop : analyticOrderAt zetaResidueUnit s₀ ≠ ⊤ := Sieve.zetaResidueUnit_order_ne_top s₀
  set m : ℕ := (analyticOrderAt zetaResidueUnit s₀).toNat
  have hm : analyticOrderAt zetaResidueUnit s₀ = (m : ℕ∞) := (ENat.coe_toNat htop).symm
  obtain ⟨g, hg, hg0, hfg⟩ := hZa.analyticOrderAt_eq_natCast.mp hm
  have hZne : ∀ᶠ w in 𝓝[≠] s₀, zetaResidueUnit w ≠ 0 := by
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.tendsto.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hfw hgw hw
    rw [hfw, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hw)) hgw
  set P' : ℂ → ℂ := fun w => ∏ μ ∈ S.erase ω₀, (w - ((β : ℂ) + I * μ)) with hP'
  have hP'cont : Continuous P' := by
    rw [hP']
    fun_prop
  have hP_split : ∀ w : ℂ, oscillationDenominator β S w = (w - s₀) * P' w := fun w => by
    rw [oscillationDenominator, ← Finset.mul_prod_erase S _ hω₀]
  have hQ_cont : ContinuousAt (oscillationNumerator β S d) s₀ :=
    (differentiableAt_oscillationNumerator hb (by rw [hs₀_re]; exact hσβ)).continuousAt
  have hev_eq : (fun w => -(P' w * ((w - s₀) * logDeriv zetaResidueUnit w)))
      =ᶠ[𝓝[≠] s₀] oscillationNumerator β S d := by
    have hopen : {w : ℂ | σ₀ < w.re} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show σ₀ < s₀.re by
        rw [hs₀_re]; exact hσβ)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hopen, hZne] with w hw hZw
    have hid := neg_mul_deriv_eq hb (s := w) hw
    rw [logDeriv_apply]
    calc -(P' w * ((w - s₀) * (deriv zetaResidueUnit w / zetaResidueUnit w)))
        = -((w - s₀) * P' w * deriv zetaResidueUnit w) / zetaResidueUnit w := by ring
      _ = (zetaResidueUnit w * oscillationNumerator β S d w) / zetaResidueUnit w := by
          rw [← hP_split w, hid]
      _ = oscillationNumerator β S d w := mul_div_cancel_left₀ _ hZw
  have hlim_lhs : Tendsto (fun w => -(P' w * ((w - s₀) * logDeriv zetaResidueUnit w)))
      (𝓝[≠] s₀) (𝓝 (-(P' s₀ * (m : ℂ)))) :=
    ((hP'cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (RHTower.AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast_complex
        hZa hm)).neg
  have hlim_rhs : Tendsto (oscillationNumerator β S d) (𝓝[≠] s₀)
      (𝓝 (oscillationNumerator β S d s₀)) :=
    hQ_cont.tendsto.mono_left nhdsWithin_le_nhds
  have heq_val : -(P' s₀ * (m : ℂ)) = oscillationNumerator β S d s₀ :=
    tendsto_nhds_unique (hlim_lhs.congr' hev_eq) hlim_rhs
  have hP_zero : oscillationDenominator β S s₀ = 0 :=
    Finset.prod_eq_zero hω₀ (sub_self _)
  have hQ_val : oscillationNumerator β S d s₀ = d ω₀ * s₀ * P' s₀ := by
    rw [oscillationNumerator, hP_zero, zero_mul, zero_add]
    refine Finset.sum_eq_single ω₀ (fun ω _ hne => ?_) (fun h => absurd hω₀ h)
    have hmem : ω₀ ∈ S.erase ω := Finset.mem_erase.mpr ⟨hne.symm, hω₀⟩
    have hz : ∏ μ ∈ S.erase ω, (s₀ - ((β : ℂ) + I * μ)) = 0 :=
      Finset.prod_eq_zero hmem (sub_self _)
    rw [hz, mul_zero]
  have hP'_ne : P' s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun μ hμ => ?_
    have hμne : μ ≠ ω₀ := (Finset.mem_erase.mp hμ).1
    intro h
    have him := congrArg Complex.im h
    simp only [hs₀, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.zero_im] at him
    exact hμne (by linarith)
  rw [hQ_val] at heq_val
  have hcancel : d ω₀ * s₀ = -(m : ℂ) := by
    apply mul_right_cancel₀ hP'_ne
    linear_combination -heq_val
  rw [eq_div_iff hs₀_ne]
  exact hcancel

/-- **Multiplicity quantization in terms of `riemannZeta`.** Away from the pole `s = 1`, each
coefficient `d(ω₀)` (`ω₀ ∈ S`) equals `−ord_{s = β+iω₀}(ζ) / (β + iω₀)`. -/
theorem oscillation_coeff_eq_neg_zeta_order_div {β σ₀ C x₀ : ℝ} {S : Finset ℝ}
    {d : ℝ → ℂ} (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀)
    {ω₀ : ℝ} (hω₀ : ω₀ ∈ S) (hσβ : σ₀ < β) (hβ0 : 0 < β)
    (hs1 : (β : ℂ) + I * ω₀ ≠ 1) :
    d ω₀ =
      -(((analyticOrderAt riemannZeta ((β : ℂ) + I * ω₀)).toNat : ℕ) : ℂ) /
        ((β : ℂ) + I * ω₀) := by
  rw [oscillation_coeff_eq_neg_zetaResidueUnit_order_div hb hω₀ hσβ hβ0,
    RHTower.analyticOrderAt_zetaResidueUnit_eq_zeta hs1]

/-- Helper packaging the complex `oscillationError` bound from a real `finiteOscillation` bound. -/
theorem norm_oscillationError_le_of_finiteOscillation_bound {β σ₁ σ₂ C x₀ : ℝ} {S : Finset ℝ}
    {c : ℝ → ℂ} (hσ : σ₁ ≤ σ₂)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ σ₁) :
    ∀ x, max x₀ 1 ≤ x →
      ‖oscillationError β (oscillationFrequencies S) (oscillationCoeff S c) x‖ ≤ |C| * x ^ σ₂ := by
  intro x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hrep : oscillationError β (oscillationFrequencies S) (oscillationCoeff S c) x
      = ((Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
    have hsum : ∑ ω ∈ oscillationFrequencies S,
          oscillationCoeff S c ω * (x : ℂ) ^ ((β : ℂ) + I * ω)
        = ((x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, finiteOscillation_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [cpow_add_I_mul_eq hx0]
      ring
    rw [oscillationError, hsum]
    push_cast
    ring
  rw [hrep, Complex.norm_real, Real.norm_eq_abs]
  refine (hC x ((le_max_left _ _).trans hx)).trans ?_
  calc C * x ^ σ₁ ≤ |C| * x ^ σ₁ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
    _ ≤ |C| * x ^ σ₂ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hσ) (abs_nonneg C)

/-- **Abscissa pinning.** Every nonzero finite-oscillation expansion of `ψ(x) − x` with `β > 1/2`
and `η > 0` satisfies `β = zetaZeroAbscissa` and `β < 1`. -/
theorem abscissa_eq_zetaZeroAbscissa_of_finiteOscillation {β η C x₀ : ℝ} {S : Finset ℝ}
    {c : ℝ → ℂ} (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)) :
    β = zetaZeroAbscissa ∧ β < 1 := by
  obtain ⟨u₀, hu₀⟩ := hne
  set σ₀ : ℝ := max (β - η) ((β + 1 / 2) / 2)
  have hσβ : σ₀ < β := max_lt (by linarith) (by linarith)
  have hb := norm_oscillationError_le_of_finiteOscillation_bound (σ₂ := σ₀) (le_max_left _ _) hC
  obtain ⟨μ₀, hμ₀, hne_coeff⟩ := exists_oscillationCoeff_ne_zero hu₀
  have hζ := zeta_eq_zero_of_coeff_ne_zero hb hμ₀ hne_coeff hσβ (by linarith)
  have hre : ((β : ℂ) + I * μ₀).re = β := by simp
  have hβ1 : β < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith) hζ
  have hle_Θ : β ≤ zetaZeroAbscissa := by
    have := re_le_zetaZeroAbscissa hζ
    rwa [hre] at this
  have hΘ_le : zetaZeroAbscissa ≤ β := by
    refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hβ.le fun q => ?_
    by_cases hgt : σ₀ < (q.1 : ℂ).re
    · obtain ⟨ω, _, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb hgt (xiZeroCopy_ne_one q)
        (riemannZeta_eq_zero_of_xiZeroCopy q)
      have : (q.1 : ℂ).re = β := by rw [heq]; simp
      exact this.le
    · linarith
  exact ⟨le_antisymm hle_Θ hΘ_le, hβ1⟩

/-- **Global Fourier coefficient law.** In any nonzero finite-oscillation expansion of `ψ(x) − x`,
every real frequency `μ ∈ ℝ` (inside or outside `S`) has exponential coefficient
`oscillationCoeff S c μ = −ord_{s = β+iμ}(ζ) / (β + iμ)`. -/
theorem oscillationCoeff_eq_neg_zeta_order_div {β η C x₀ : ℝ} {S : Finset ℝ} {c : ℝ → ℂ}
    (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η))
    (μ : ℝ) :
    oscillationCoeff S c μ =
      -(((analyticOrderAt riemannZeta ((β : ℂ) + I * μ)).toNat : ℕ) : ℂ) /
        ((β : ℂ) + I * μ) := by
  have hβ1 : β < 1 := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).2
  set σ₀ : ℝ := max (β - η) ((β + 1 / 2) / 2)
  have hσβ : σ₀ < β := max_lt (by linarith) (by linarith)
  have hb := norm_oscillationError_le_of_finiteOscillation_bound
    (σ₂ := σ₀) (le_max_left _ _) hC
  have hs1 : (β : ℂ) + I * μ ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  by_cases hμ : μ ∈ oscillationFrequencies S
  · exact oscillation_coeff_eq_neg_zeta_order_div hb hμ hσβ (by linarith) hs1
  · have hnotS : μ ∉ S := fun h => hμ (Finset.mem_union_left _ h)
    have hnotNegS : -μ ∉ S := fun h =>
      hμ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-μ, h, neg_neg μ⟩))
    have hd0 : oscillationCoeff S c μ = 0 := by simp [oscillationCoeff, hnotS, hnotNegS]
    have hζ_ne : riemannZeta ((β : ℂ) + I * μ) ≠ 0 := by
      intro hζ0
      obtain ⟨ω, hω, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb
        (by simp; exact hσβ) hs1 hζ0
      have hμω : μ = ω := by
        have := congrArg Complex.im heq
        simpa using this
      exact hμ (hμω ▸ hω)
    have hord0 : analyticOrderAt riemannZeta ((β : ℂ) + I * μ) = 0 :=
      (analyticOn_riemannZeta _ hs1).analyticOrderAt_eq_zero.mpr hζ_ne
    simp [hd0, hord0]

/-- **Vanishing of the zero-frequency mode.** Because `ζ` has no real zeros in `(0, 1)`, the
constant Fourier mode `oscillationCoeff S c 0` of any finite prime-error oscillation vanishes. -/
theorem oscillationCoeff_zero_eq_zero {β η C x₀ : ℝ} {S : Finset ℝ} {c : ℝ → ℂ}
    (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)) :
    oscillationCoeff S c 0 = 0 := by
  have hβ1 : β < 1 := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).2
  rw [oscillationCoeff_eq_neg_zeta_order_div hβ hη hne hC 0]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  have hne0 : riemannZeta (β : ℂ) ≠ 0 :=
    RHTower.riemannZeta_real_strip_ne_zero (by linarith) hβ1
  have hs1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ1.ne
  have hord0 : analyticOrderAt riemannZeta (β : ℂ) = 0 :=
    (analyticOn_riemannZeta _ hs1).analyticOrderAt_eq_zero.mpr hne0
  simp [hord0]

/-! ### 3. Canonical uniqueness of the abscissa and oscillation profile -/

/-- Outside `oscillationFrequencies S`, `oscillationCoeff S c` vanishes identically. -/
theorem oscillationCoeff_eq_zero_of_notMem {S : Finset ℝ} {c : ℝ → ℂ} {μ : ℝ}
    (hμ : μ ∉ oscillationFrequencies S) : oscillationCoeff S c μ = 0 := by
  have h1 : μ ∉ S := fun h => hμ (Finset.mem_union_left _ h)
  have h2 : -μ ∉ S := fun h =>
    hμ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-μ, h, neg_neg μ⟩))
  simp [oscillationCoeff, h1, h2]

/-- **Canonical uniqueness of `(β, T)`.** Any two nonzero finite-oscillation witnesses for
`ψ(x) − x` have the same abscissa `β = β' = zetaZeroAbscissa` and define the exact same real
trigonometric polynomial on all of `ℝ`. -/
theorem primeErrorFiniteOscillation_unique_abscissa_and_profile
    {β η C x₀ β' η' C' x₀' : ℝ} {S S' : Finset ℝ} {c c' : ℝ → ℂ}
    (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η))
    (hβ' : 1 / 2 < β') (hη' : 0 < η') (hne' : ∃ u, finiteOscillation S' c' u ≠ 0)
    (hC' : ∀ x, x₀' ≤ x →
      |Chebyshev.psi x - x - x ^ β' * finiteOscillation S' c' (Real.log x)| ≤
        C' * x ^ (β' - η')) :
    β = β' ∧ ∀ u : ℝ, finiteOscillation S c u = finiteOscillation S' c' u := by
  classical
  have h1 := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).1
  have h2 := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ' hη' hne' hC').1
  have hβeq : β = β' := h1.trans h2.symm
  refine ⟨hβeq, fun u => ?_⟩
  set U : Finset ℝ := oscillationFrequencies S ∪ oscillationFrequencies S'
  have hsum1 : (finiteOscillation S c u : ℂ) =
      ∑ μ ∈ U, oscillationCoeff S c μ * cexp (I * μ * u) := by
    rw [finiteOscillation_eq_sum]
    exact Finset.sum_subset Finset.subset_union_left fun μ _ hnot => by
      rw [oscillationCoeff_eq_zero_of_notMem hnot, zero_mul]
  have hsum2 : (finiteOscillation S' c' u : ℂ) =
      ∑ μ ∈ U, oscillationCoeff S' c' μ * cexp (I * μ * u) := by
    rw [finiteOscillation_eq_sum]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hnot => by
      rw [oscillationCoeff_eq_zero_of_notMem hnot, zero_mul]
  have hcoeff : ∀ μ : ℝ, oscillationCoeff S c μ = oscillationCoeff S' c' μ := fun μ => by
    rw [oscillationCoeff_eq_neg_zeta_order_div hβ hη hne hC μ,
      oscillationCoeff_eq_neg_zeta_order_div hβ' hη' hne' hC' μ, hβeq]
  have hCeq : (finiteOscillation S c u : ℂ) = (finiteOscillation S' c' u : ℂ) := by
    rw [hsum1, hsum2]
    exact Finset.sum_congr rfl fun μ _ => by rw [hcoeff μ]
  exact Complex.ofReal_inj.mp hCeq

/-! ### 4. Sharp secondary-abscissa bifurcation of the power-saving exponent `η` -/

/-- The set `{1/2} ∪ {Re q : q : XiZeroCopy, Re q < Θ}` defining the secondary zero abscissa. -/
def zetaSecondAbscissaSet : Set ℝ :=
  {(1 / 2 : ℝ)} ∪ {σ : ℝ | ∃ q : XiZeroCopy, (q.1 : ℂ).re = σ ∧ σ < zetaZeroAbscissa}

/-- **The secondary zero abscissa** `Θ₂ = sup ({1/2} ∪ {Re ρ : ζ(ρ) = 0, 0 < Re ρ < Θ})`. -/
def zetaSecondAbscissa : ℝ := sSup zetaSecondAbscissaSet

theorem zetaSecondAbscissaSet_nonempty : zetaSecondAbscissaSet.Nonempty :=
  ⟨1 / 2, Or.inl rfl⟩

theorem bddAbove_zetaSecondAbscissaSet : BddAbove zetaSecondAbscissaSet := by
  refine ⟨zetaZeroAbscissa, fun σ hσ => ?_⟩
  rcases hσ with rfl | ⟨_, _, hlt⟩
  · exact half_le_zetaZeroAbscissa
  · exact hlt.le

theorem half_le_zetaSecondAbscissa : (1 / 2 : ℝ) ≤ zetaSecondAbscissa :=
  le_csSup bddAbove_zetaSecondAbscissaSet (Or.inl rfl)

theorem zetaSecondAbscissa_le_zetaZeroAbscissa : zetaSecondAbscissa ≤ zetaZeroAbscissa :=
  csSup_le zetaSecondAbscissaSet_nonempty fun _ hσ => by
    rcases hσ with rfl | ⟨_, _, hlt⟩
    · exact half_le_zetaZeroAbscissa
    · exact hlt.le

/-- **Exact upper ceiling on `η` via `Θ₂`.** Every finite-oscillation witness satisfies
`zetaSecondAbscissa ≤ β − η`, equivalently `η ≤ zetaZeroAbscissa − zetaSecondAbscissa`. -/
theorem eta_le_zetaZeroAbscissa_sub_secondAbscissa {β η C x₀ : ℝ} {S : Finset ℝ} {c : ℝ → ℂ}
    (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)) :
    η ≤ zetaZeroAbscissa - zetaSecondAbscissa := by
  have hβΘ := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).1
  have hb := norm_oscillationError_le_of_finiteOscillation_bound (le_refl (β - η)) hC
  have hhalf : 1 / 2 ≤ β - η := half_le_of_oscillationError_bound hb
  have hΘ₂_le : zetaSecondAbscissa ≤ β - η := by
    refine csSup_le zetaSecondAbscissaSet_nonempty fun σ hσ => ?_
    rcases hσ with rfl | ⟨q, rfl, hlt⟩
    · exact hhalf
    · by_contra hgt
      push Not at hgt
      obtain ⟨ω, _, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb hgt (xiZeroCopy_ne_one q)
        (riemannZeta_eq_zero_of_xiZeroCopy q)
      have hre : (q.1 : ℂ).re = β := by rw [heq]; simp
      linarith
  linarith

/-- **Asymptotic-abscissa ceiling on `η`.** Every finite-oscillation witness satisfies
`η ≤ zetaZeroAbscissa − zetaAsymptoticAbscissa` (`Θ_∞ ≤ β − η`). -/
theorem eta_le_zetaZeroAbscissa_sub_asymptoticAbscissa {β η C x₀ : ℝ} {S : Finset ℝ} {c : ℝ → ℂ}
    (hβ : 1 / 2 < β) (hη : 0 < η) (hne : ∃ u, finiteOscillation S c u ≠ 0)
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)) :
    η ≤ zetaZeroAbscissa - zetaAsymptoticAbscissa := by
  have hβΘ := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).1
  have hb := norm_oscillationError_le_of_finiteOscillation_bound (le_refl (β - η)) hC
  have hhalf : 1 / 2 ≤ β - η := half_le_of_oscillationError_bound hb
  set M : ℝ := ∑ μ ∈ oscillationFrequencies S, |μ|
  have hfin : {q : XiZeroCopy | β - η < (q.1 : ℂ).re}.Finite := by
    refine (finite_abs_im_le M).subset fun q hq => ?_
    obtain ⟨ω, hω, heq⟩ := eq_of_zeta_eq_zero_of_expansion hb hq (xiZeroCopy_ne_one q)
      (riemannZeta_eq_zero_of_xiZeroCopy q)
    have him : (q.1 : ℂ).im = ω := by rw [heq]; simp
    show |(q.1 : ℂ).im| ≤ M
    rw [him]
    exact Finset.single_le_sum (f := fun μ : ℝ => |μ|) (fun _ _ => abs_nonneg _) hω
  have hΘ_inf : zetaAsymptoticAbscissa ≤ β - η :=
    csInf_le bddBelow_zetaAsymptoticAbscissaSet ⟨hhalf, hfin⟩
  linarith

/-- **Sharp remainder expansion from an isolated top layer at every exponent `E > β₁`.** -/
theorem exists_expansion_of_top_at_exponent {top : Finset XiZeroCopy} {β₁ E : ℝ}
    (hβ₁ : 1 / 2 ≤ β₁) (hβ₁E : β₁ < E) (hE1 : E < 1)
    (hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ β₁) :
    ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x + (∑ q ∈ top, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤ C * x ^ E := by
  set θ : ℝ := min ((E - β₁) / 2) 1 with hθ
  have hθ0 : 0 < θ := lt_min (by linarith) one_pos
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hE0 : 0 < E := by linarith
  have hgap : 0 < 1 - E := by linarith
  set W : ℝ := ∑' q, zeroWeight θ q
  have hW0 : 0 ≤ W := tsum_nonneg (zeroWeight_nonneg θ)
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨2 + Real.log (2 * Real.pi) + 2 * top.card + 16 * W,
    max 4 ((2 : ℝ) ^ (1 / (1 - E))), fun x hx => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (2 : ℝ) ^ (1 / (1 - E)) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set H : ℝ := x ^ E with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hx1 hE0.le
  have h2 : 2 ≤ x ^ (1 - E) := by
    have h := Real.rpow_le_rpow (by positivity) hx2 hgap.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hgap.ne', Real.rpow_one] at h
  have hsplit : H * x ^ (1 - E) = x := by
    rw [hH, ← Real.rpow_add hx0]
    simp
  have hHx : H ≤ x / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  refine (abs_psi_sub_add_re_topSum_le (x := x) (H := H) hnon hθ0 hθ1 hx4 hH1 hHx).trans ?_
  have hratio : (x / H) ^ θ ≤ x ^ θ :=
    Real.rpow_le_rpow (by positivity) (div_le_self hx0.le hH1) hθ0.le
  have hβθ : x ^ β₁ * x ^ θ ≤ H := by
    rw [← Real.rpow_add hx0, hH]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    have : θ ≤ (E - β₁) / 2 := min_le_left _ _
    linarith
  have hlast : 16 * x ^ β₁ * (x / H) ^ θ * W ≤ 16 * W * H := by
    calc 16 * x ^ β₁ * (x / H) ^ θ * W ≤ 16 * x ^ β₁ * x ^ θ * W := by gcongr
      _ = 16 * W * (x ^ β₁ * x ^ θ) := by ring
      _ ≤ 16 * W * H := by gcongr
  have hc : (top.card : ℝ) * (2 * H) = 2 * top.card * H := by ring
  rw [hc]
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hH1)]

/-- **Sharp converse up to `Θ − Θ₂`.** Under `¬ AsymptoticAbscissaLaw`, we have
`zetaAsymptoticAbscissa ≤ zetaSecondAbscissa < zetaZeroAbscissa`, and for every `η` with
`0 < η < zetaZeroAbscissa − zetaSecondAbscissa`, the prime error admits a finite-oscillation
expansion with remainder `O(x^{zetaZeroAbscissa − η})`. -/
theorem exists_primeErrorFiniteOscillation_of_lt_gap (hnot : ¬ AsymptoticAbscissaLaw) :
    zetaAsymptoticAbscissa ≤ zetaSecondAbscissa ∧
    zetaSecondAbscissa < zetaZeroAbscissa ∧
    ∀ η : ℝ, 0 < η → η < zetaZeroAbscissa - zetaSecondAbscissa →
      ∃ (S : Finset ℝ) (c : ℝ → ℂ), (∃ u, finiteOscillation S c u ≠ 0) ∧
        ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x →
          |Chebyshev.psi x - x -
            x ^ zetaZeroAbscissa * finiteOscillation S c (Real.log x)| ≤
              C * x ^ (zetaZeroAbscissa - η) := by
  classical
  have hlt_abs : zetaAsymptoticAbscissa < zetaZeroAbscissa :=
    lt_of_le_of_ne zetaAsymptoticAbscissa_le_zetaZeroAbscissa fun heq =>
      hnot (asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa.mpr heq)
  obtain ⟨σ₀, ⟨hσ₀_half, hE₀_fin⟩, hσ₀_lt⟩ :=
    exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty hlt_abs
  set F : Finset XiZeroCopy := hE₀_fin.toFinset with hFdef
  have hmemF : ∀ q : XiZeroCopy, q ∈ F ↔ σ₀ < (q.1 : ℂ).re := fun q => by simp [hFdef]
  have hF_ne : F.Nonempty := by
    obtain ⟨ρ, hζ, hρ1, hσρ⟩ := exists_zetaZero_mem_openStrip_lt_re hσ₀_lt
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ (by linarith) hρ1
    exact ⟨q, (hmemF q).mpr (by rw [hq]; exact hσρ)⟩
  obtain ⟨qt, hqtF, hqt⟩ := F.exists_max_image (fun q : XiZeroCopy => (q.1 : ℂ).re) hF_ne
  have hqt_re : (qt.1 : ℂ).re = zetaZeroAbscissa := by
    refine le_antisymm (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy qt))
      (zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le
        (hσ₀_half.trans ((hmemF qt).mp hqtF).le) fun q => ?_)
    by_cases hq : σ₀ < (q.1 : ℂ).re
    · exact hqt q ((hmemF q).mpr hq)
    · exact (not_lt.mp hq).trans ((hmemF qt).mp hqtF).le
  have hΘ1 : zetaZeroAbscissa < 1 := hqt_re ▸ xiZeroCopy_re_lt_one qt
  set top : Finset XiZeroCopy := F.filter fun q => (q.1 : ℂ).re = zetaZeroAbscissa
  set A : Finset ℝ := insert σ₀
    ((F.filter fun q : XiZeroCopy => (q.1 : ℂ).re < zetaZeroAbscissa).image
      fun q => (q.1 : ℂ).re)
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  set β₁ : ℝ := A.max' hAne
  have hβ₁_lt : β₁ < zetaZeroAbscissa := by
    rcases Finset.mem_insert.mp (A.max'_mem hAne) with hm | hm
    · change A.max' hAne < zetaZeroAbscissa
      rw [hm]
      exact hσ₀_lt
    · obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hm
      change A.max' hAne < zetaZeroAbscissa
      rw [← heq]
      exact (Finset.mem_filter.mp hq).2
  have hnon : ∀ q : XiZeroCopy, q ∉ top → (q.1 : ℂ).re ≤ zetaSecondAbscissa := by
    intro q hq
    have hlt_Θ : (q.1 : ℂ).re < zetaZeroAbscissa := by
      refine lt_of_le_of_ne
        (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)) fun heq => hq ?_
      exact Finset.mem_filter.mpr ⟨(hmemF q).mpr (heq ▸ hσ₀_lt), heq⟩
    exact le_csSup bddAbove_zetaSecondAbscissaSet (Or.inr ⟨q, rfl, hlt_Θ⟩)
  have hΘ₂_le_β₁ : zetaSecondAbscissa ≤ β₁ := by
    refine csSup_le zetaSecondAbscissaSet_nonempty fun σ hσ => ?_
    rcases hσ with rfl | ⟨q, rfl, hlt⟩
    · exact hσ₀_half.trans (A.le_max' _ (Finset.mem_insert_self _ _))
    · by_cases hq : σ₀ < (q.1 : ℂ).re
      · exact A.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨q, Finset.mem_filter.mpr ⟨(hmemF q).mpr hq, hlt⟩, rfl⟩))
      · exact (not_lt.mp hq).trans (A.le_max' _ (Finset.mem_insert_self _ _))
  have hΘ₂_lt_Θ : zetaSecondAbscissa < zetaZeroAbscissa := lt_of_le_of_lt hΘ₂_le_β₁ hβ₁_lt
  have hΘ_inf_le : zetaAsymptoticAbscissa ≤ zetaSecondAbscissa := by
    refine csInf_le bddBelow_zetaAsymptoticAbscissaSet ⟨half_le_zetaSecondAbscissa, ?_⟩
    refine top.finite_toSet.subset fun q hq => ?_
    by_contra hnot_top
    exact absurd (hnon q hnot_top) (not_le.mpr hq)
  refine ⟨hΘ_inf_le, hΘ₂_lt_Θ, fun η hη0 hη_lt => ?_⟩
  set E : ℝ := zetaZeroAbscissa - η
  have hΘ₂_lt_E : zetaSecondAbscissa < E := by linarith
  have hE_lt_1 : E < 1 := by linarith
  obtain ⟨C, x₀, hC⟩ := exists_expansion_of_top_at_exponent
    half_le_zetaSecondAbscissa hΘ₂_lt_E hE_lt_1 hnon
  set S : Finset ℝ := top.image fun q => (q.1 : ℂ).im
  set c : ℝ → ℂ := fun ω =>
    -((top.filter fun q => (q.1 : ℂ).im = ω).card : ℂ) / ((zetaZeroAbscissa : ℂ) + I * ω)
  have htop : ∀ q ∈ top, (q.1 : ℂ).re = zetaZeroAbscissa :=
    fun _ hq => (Finset.mem_filter.mp hq).2
  have hexp : ∀ x, max x₀ 1 ≤ x →
      |Chebyshev.psi x - x - x ^ zetaZeroAbscissa * finiteOscillation S c (Real.log x)| ≤
        C * x ^ E := by
    intro x hx
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hT := rpow_mul_finiteOscillation_top (top := top) (β := zetaZeroAbscissa) (x := x)
      (by linarith) htop
    rw [hT, sub_neg_eq_add]
    exact hC x ((le_max_left _ _).trans hx)
  refine ⟨S, c, ?_, C, max x₀ 1, hexp⟩
  by_contra hall
  push Not at hall
  have hb : ∀ x, max x₀ 1 ≤ x → ‖oscillationError zetaZeroAbscissa ∅ 0 x‖ ≤ C * x ^ E := by
    intro x hx
    have h := hexp x hx
    rw [hall, mul_zero, sub_zero] at h
    have hrep : oscillationError zetaZeroAbscissa ∅ 0 x =
        ((Chebyshev.psi x - x : ℝ) : ℂ) := by simp [oscillationError]
    rwa [hrep, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨ω, hω, -⟩ := eq_of_zeta_eq_zero_of_expansion hb (ρ := (qt.1 : ℂ))
    (by rw [hqt_re]; linarith) (xiZeroCopy_ne_one qt) (riemannZeta_eq_zero_of_xiZeroCopy qt)
  simp at hω

/-! ### 5. Bounded-logarithmic-gap bidirectional sign changes of `ψ(x) − x` -/

/-- `finiteOscillation S c` is continuous on `ℝ`. -/
theorem continuous_finiteOscillation (S : Finset ℝ) (c : ℝ → ℂ) :
    Continuous (finiteOscillation S c) := by
  unfold finiteOscillation
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun ω _ => ?_)
  fun_prop

/-- **Bounded-logarithmic-gap bidirectional sign changes.** Under `PrimeErrorIsFiniteOscillation`,
there exist a gap length `L > 0`, amplitude `δ > 0`, and threshold `U₀` such that every logarithmic
interval `[u₀, u₀ + L]` (`u₀ ≥ U₀`) contains points `u₁, u₂` with
`ψ(e^{u₁}) − e^{u₁} > δ e^{Θ u₁}` and `ψ(e^{u₂}) − e^{u₂} < −δ e^{Θ u₂}`. -/
theorem exists_bounded_log_gap_sign_changes_of_primeErrorIsFiniteOscillation
    (h : PrimeErrorIsFiniteOscillation) :
    ∃ L δ U₀ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ u₀ : ℝ, U₀ ≤ u₀ →
      (∃ u₁ ∈ Icc u₀ (u₀ + L),
        δ * Real.exp (zetaZeroAbscissa * u₁) < Chebyshev.psi (Real.exp u₁) - Real.exp u₁) ∧
      (∃ u₂ ∈ Icc u₀ (u₀ + L),
        Chebyshev.psi (Real.exp u₂) - Real.exp u₂ < -δ * Real.exp (zetaZeroAbscissa * u₂)) := by
  classical
  obtain ⟨β, η, hβ, hη, S, c, hne, C, x₀, hC⟩ := h
  have hβΘ := (abscissa_eq_zetaZeroAbscissa_of_finiteOscillation hβ hη hne hC).1
  obtain ⟨u_nz, hu_nz⟩ := hne
  obtain ⟨τ₀, hτ₀_mem, hτ₀_ne⟩ := exists_oscillationCoeff_ne_zero hu_nz
  have hd0 : oscillationCoeff S c 0 = 0 := oscillationCoeff_zero_eq_zero hβ hη ⟨u_nz, hu_nz⟩ hC
  set F : Finset ℝ := oscillationFrequencies S
  let coeff : F → ℂ := fun q => -oscillationCoeff S c q.1
  let freq : F → ℝ := fun q => q.1
  have hlim : Tendsto (fun u : ℝ =>
      (finiteOscillation S c u : ℂ) +
        ∑' q : F, coeff q * Complex.exp ((freq q : ℂ) * I * (u : ℂ))) atTop (𝓝 0) := by
    have hzero : (fun u : ℝ =>
        (finiteOscillation S c u : ℂ) +
          ∑' q : F, coeff q * Complex.exp ((freq q : ℂ) * I * (u : ℂ))) = fun _ => 0 := by
      funext u
      rw [tsum_fintype, finiteOscillation_eq_sum]
      have hsum : ∑ q : F, coeff q * Complex.exp ((freq q : ℂ) * I * (u : ℂ)) =
          -∑ μ ∈ F, oscillationCoeff S c μ * cexp (I * μ * u) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_attach F]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [coeff, freq, neg_mul]
        congr 2
        ring
      rw [hsum, add_neg_cancel]
    rw [hzero]
    exact tendsto_const_nhds
  have h0_sum : (∑' q : F, if freq q = 0 then coeff q else 0) = 0 := by
    rw [tsum_fintype]
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with hq
    · have hq0 : (q.1 : ℝ) = 0 := hq
      simp [coeff, hq0, hd0]
    · rfl
  have hτ₀_sum : (∑' q : F, if freq q = τ₀ then coeff q else 0) ≠ 0 := by
    rw [tsum_fintype, Finset.sum_eq_single ⟨τ₀, hτ₀_mem⟩]
    · simp [coeff, freq, hτ₀_ne]
    · intro q _ hne_q
      have hval : freq q ≠ τ₀ := fun h => hne_q (Subtype.ext h)
      simp [hval]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  obtain ⟨L, ε, U₁, hL0, hε0, hwin⟩ := RHTower.exists_dense_sign_changes_of_tendsto_add_tsum
    (continuous_finiteOscillation S c) coeff (Summable.of_finite) freq hlim h0_sum hτ₀_sum
  have hdecay : Tendsto (fun u : ℝ => |C| * Real.exp (-η * u)) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hη))).const_mul |C|
  obtain ⟨U₂, hU₂⟩ := (hdecay.eventually (gt_mem_nhds (half_pos hε0))).exists_forall_of_atTop
  set U₀ : ℝ := max U₁ (max U₂ (Real.log (max x₀ 1)))
  refine ⟨L, ε / 2, U₀, hL0, half_pos hε0, fun u₀ hu₀ => ?_⟩
  have hu₀_1 : U₁ ≤ u₀ := (le_max_left _ _).trans hu₀
  have hu₀_2 : U₂ ≤ u₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu₀
  have hu₀_3 : Real.log (max x₀ 1) ≤ u₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hu₀
  obtain ⟨⟨u₁, hu₁_mem, hu₁_gt⟩, ⟨u₂, hu₂_mem, hu₂_lt⟩⟩ := hwin u₀ hu₀_1
  have herr : ∀ u : ℝ, u₀ ≤ u →
      |Chebyshev.psi (Real.exp u) - Real.exp u -
        Real.exp (β * u) * finiteOscillation S c u| < (ε / 2) * Real.exp (β * u) := by
    intro u hu
    have hx_ge : max x₀ 1 ≤ Real.exp u := by
      calc max x₀ 1 = Real.exp (Real.log (max x₀ 1)) :=
            (Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr (hu₀_3.trans hu)
    have hbnd := hC (Real.exp u) ((le_max_left _ _).trans hx_ge)
    rw [Real.log_exp, ← Real.exp_mul, mul_comm u β] at hbnd
    have hexp_sub : (Real.exp u) ^ (β - η) = Real.exp (-η * u) * Real.exp (β * u) := by
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    have hsmall : |C| * Real.exp (-η * u) < ε / 2 := hU₂ u (hu₀_2.trans hu)
    calc |Chebyshev.psi (Real.exp u) - Real.exp u - Real.exp (β * u) * finiteOscillation S c u|
        ≤ C * (Real.exp u) ^ (β - η) := hbnd
      _ ≤ |C| * (Real.exp u) ^ (β - η) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Real.exp_pos u).le _)
      _ = (|C| * Real.exp (-η * u)) * Real.exp (β * u) := by rw [hexp_sub, mul_assoc]
      _ < (ε / 2) * Real.exp (β * u) :=
          mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
  constructor
  · refine ⟨u₁, hu₁_mem, ?_⟩
    have h1 := (abs_lt.mp (herr u₁ hu₁_mem.1)).1
    have h2 : ε * Real.exp (β * u₁) < Real.exp (β * u₁) * finiteOscillation S c u₁ := by
      nlinarith [Real.exp_pos (β * u₁)]
    rw [← hβΘ]
    linarith
  · refine ⟨u₂, hu₂_mem, ?_⟩
    have h1 := (abs_lt.mp (herr u₂ hu₂_mem.1)).2
    have h2 : Real.exp (β * u₂) * finiteOscillation S c u₂ < -ε * Real.exp (β * u₂) := by
      nlinarith [Real.exp_pos (β * u₂)]
    rw [← hβΘ]
    linarith

/-! ### 6. Alternating prime-power parity identity and finite-oscillation transfer -/

/-- Even integers with nonzero von Mangoldt weight are precisely positive powers of `2`. -/
theorem even_and_vonMangoldt_ne_zero_iff {n : ℕ} :
    (Even n ∧ vonMangoldt n ≠ 0) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  constructor
  · rintro ⟨heven, hΛ⟩
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have hp_even : Even p := (Nat.even_pow.mp heven).1
    have hp2 : p = 2 := (Nat.Prime.even_iff hp).mp hp_even
    exact ⟨k, hk, by rw [hp2]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, ?_⟩
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact (Real.log_pos one_lt_two).ne'

/-- **Exact alternating von Mangoldt sum on `1 ≤ n ≤ N`.** For every `N ≥ 1`,
`∑_{1 ≤ n ≤ N} (−1)^n Λ(n) = 2 (Nat.log 2 N) log 2 − ∑_{1 ≤ n ≤ N} Λ(n)`. -/
theorem sum_Icc_alternating_vonMangoldt_eq {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ n * (vonMangoldt n : ℝ) =
      2 * (Nat.log 2 N : ℝ) * Real.log 2 - ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) := by
  classical
  have hadd : ∑ n ∈ Finset.Icc 1 N,
        ((-1 : ℝ) ^ n * (vonMangoldt n : ℝ) + (vonMangoldt n : ℝ)) =
      2 * (Nat.log 2 N : ℝ) * Real.log 2 := by
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        (-1 : ℝ) ^ n * (vonMangoldt n : ℝ) + (vonMangoldt n : ℝ) =
          if Even n ∧ vonMangoldt n ≠ 0 then 2 * Real.log 2 else 0 := by
      intro n _
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · have hev : Even (2 * m) := even_two_mul m
        rw [pow_mul, neg_one_sq, one_pow, one_mul]
        by_cases hΛ : vonMangoldt (2 * m) = 0
        · simp [hΛ]
        · obtain ⟨k, hk, heq⟩ := even_and_vonMangoldt_ne_zero_iff.mp ⟨hev, hΛ⟩
          rw [if_pos ⟨hev, hΛ⟩, heq, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
            ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
          ring
      · have hnot_ev : ¬ Even (2 * m + 1) := Nat.not_even_two_mul_add_one m
        rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul,
          neg_add_cancel, if_neg (fun h => hnot_ev h.1)]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    set E : Finset ℕ := (Finset.Icc 1 N).filter fun n => Even n ∧ vonMangoldt n ≠ 0
    have hbij : E = (Finset.Icc 1 (Nat.log 2 N)).image (fun k => 2 ^ k) := by
      ext n
      simp only [E, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
        even_and_vonMangoldt_ne_zero_iff]
      constructor
      · rintro ⟨⟨_, hnN⟩, k, hk1, rfl⟩
        exact ⟨k, ⟨hk1, (Nat.le_log_iff_pow_le one_lt_two (by omega)).mpr hnN⟩, rfl⟩
      · rintro ⟨k, ⟨hk1, hklog⟩, rfl⟩
        exact ⟨⟨Nat.one_le_two_pow,
          (Nat.le_log_iff_pow_le one_lt_two (by omega)).mp hklog⟩, k, hk1, rfl⟩
    have hinj : Set.InjOn (fun k : ℕ => 2 ^ k) (Finset.Icc 1 (Nat.log 2 N)) :=
      fun _ _ _ _ h => Nat.pow_right_injective (by norm_num) h
    rw [hbij, Finset.sum_image hinj, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  rw [Finset.sum_add_distrib] at hadd
  linarith

/-- **Alternating von Mangoldt parity identity.** For every `x ≥ 1`,
`∑_{1 ≤ n ≤ ⌊x⌋₊} (−1)^n Λ(n) = 2 (Nat.log 2 ⌊x⌋₊) log 2 − ψ(x)`. -/
theorem sum_alternating_vonMangoldt_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (-1 : ℝ) ^ n * (vonMangoldt n : ℝ) =
      2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 - Chebyshev.psi x := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hIcc : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [sum_Icc_alternating_vonMangoldt_eq hN, Chebyshev.psi_eq_sum_Icc, hIcc,
    Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]

/-- **Parity-twist oscillation transfer.** Every finite-oscillation expansion
`|ψ(x) − x − x^β T(log x)| ≤ C x^{β−η}` transfers with the exact same remainder exponent `β − η` to
the alternating prime-power sum `∑_{1 ≤ n ≤ ⌊x⌋₊} (−1)^n Λ(n) + x = −x^β T(log x) + O(x^{β−η})`. -/
theorem alternating_vonMangoldt_finiteOscillation {β η C x₀ : ℝ} {S : Finset ℝ} {c : ℝ → ℂ}
    (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ (β - η)) :
    ∃ C' x₀' : ℝ, ∀ x, x₀' ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (-1 : ℝ) ^ n * (vonMangoldt n : ℝ)) + x +
        x ^ β * finiteOscillation S c (Real.log x)| ≤ C' * x ^ (β - η) := by
  have hb := norm_oscillationError_le_of_finiteOscillation_bound (le_refl (β - η)) hC
  have hhalf : 1 / 2 ≤ β - η := half_le_of_oscillationError_bound hb
  refine ⟨|C| + 4, max x₀ 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  rw [sum_alternating_vonMangoldt_eq hx1]
  have hpow : ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.pow_log_le_self 2 (by omega))).trans (Nat.floor_le hx0.le)
  have hlog2 : (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Real.log x := by
    have h1 : Real.log (((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ)) ≤ Real.log x :=
      Real.log_le_log (by positivity) hpow
    simpa [Nat.cast_pow, Real.log_pow] using h1
  have hlog_sqrt : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
    have h1 : Real.log (x ^ (1 / 2 : ℝ)) ≤ x ^ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
    have h2 : Real.log (x ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log x := Real.log_rpow hx0 _
    linarith
  have hdyadic : |2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2| ≤ 4 * x ^ (β - η) := by
    have hnonneg : 0 ≤ 2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    rw [abs_of_nonneg hnonneg]
    calc 2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2
        = 2 * ((Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2) := by ring
      _ ≤ 2 * Real.log x := by linarith
      _ ≤ 4 * x ^ (1 / 2 : ℝ) := by linarith
      _ ≤ 4 * x ^ (β - η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hhalf) (by norm_num)
  have hmain : |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤
      |C| * x ^ (β - η) :=
    (hC x ((le_max_left _ _).trans hx)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _))
  calc |2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 - Chebyshev.psi x + x +
        x ^ β * finiteOscillation S c (Real.log x)|
      = |(2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2) -
          (Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x))| := by ring_nf
    _ ≤ |2 * (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2| +
          |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| := abs_sub _ _
    _ ≤ 4 * x ^ (β - η) + |C| * x ^ (β - η) := add_le_add hdyadic hmain
    _ = (|C| + 4) * x ^ (β - η) := by ring

end

end GaloisForLFunctions.ZeroConfigurationGeometry
