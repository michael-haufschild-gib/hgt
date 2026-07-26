import GaloisForLFunctions.RHTower.SalemFermiModeCriterion
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Salem's Fermi-mode improper integral

This module proves the source integral omitted by `SalemFermiModeCriterion`.  For
`0 < Re s` and `s ≠ 1`, the literal Fermi kernel has Mellin transform

`mellin (fun t => (exp t + 1)⁻¹) s =
  Gamma(s) * (1 - 2^(1-s)) * zeta(s)`.

On `Re s > 1`, the proof expands the denominator as a geometric series and applies
mathlib's Mellin--Dirichlet interchange.  The resulting alternating Dirichlet series is
regrouped into the already formalized paired eta series.  Mellin holomorphy and the identity
theorem on the existing punctured-half-plane connector extend the identity to `Re s > 0`,
`s ≠ 1`.

Scaling gives the exact improper integral used by the Salem mode equation.  Consequently,
the integral-defined mode solution and exclusion predicates are identified with the formerly
evaluated predicates, and the integral exclusion criterion itself is equivalent to RH.
-/

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

def salemFermiKernel (t : ℝ) : ℂ :=
  ((Real.exp t + 1 : ℝ) : ℂ)⁻¹

theorem salemFermiKernel_eq (t : ℝ) :
    salemFermiKernel t = ((Real.exp t + 1 : ℝ) : ℂ)⁻¹ := rfl

theorem salemFermiKernel_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ n * Real.exp (-(((n + 1 : ℕ) : ℝ) * t)))
      (salemFermiKernel t) := by
  let q : ℝ := Real.exp (-t)
  have hqnorm : ‖(-q : ℂ)‖ < 1 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : HasSum (fun n : ℕ => (-q : ℂ) ^ n) (1 - (-q : ℂ))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hqnorm
  have hmul := hgeo.mul_left (q : ℂ)
  convert hmul using 1
  · funext n
    have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) = q ^ (n + 1) := by
      rw [show q = Real.exp (-t) by rfl, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, pow_succ, neg_pow]
    push_cast
    ring
  · rw [salemFermiKernel, show q = Real.exp (-t) by rfl, Real.exp_neg]
    push_cast
    have hexp : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_ne_zero t)
    field_simp
    ring

theorem salemFermi_weight_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ n‖ / (((n + 1 : ℕ) : ℝ) ^ s.re)) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  refine h.congr fun n => ?_
  rw [norm_pow, norm_neg, norm_one, one_pow, one_div,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  push_cast
  rw [one_div]

theorem tsum_salemAlternating_eq_etaPair {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℂ) ^ s)) = etaPair s := by
  let f : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℂ) ^ s)
  have hsum : Summable f := by
    have hw := salemFermi_weight_summable hs
    apply Summable.of_norm
    refine hw.congr fun n => ?_
    dsimp only [f]
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
  have he : Summable (fun k : ℕ => f (2 * k)) :=
    hsum.comp_injective fun a b hab => by omega
  have ho : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hsum.comp_injective fun a b hab => by omega
  have hsplit := tsum_even_add_odd he ho
  have heterm : ∀ k : ℕ,
      f (2 * k) = (((2 * k + 1 : ℝ) : ℂ) ^ (-s)) := by
    intro k
    dsimp [f]
    rw [pow_mul]
    norm_num
    rw [Complex.cpow_neg]
  have hoterm : ∀ k : ℕ,
      f (2 * k + 1) = -(((2 * k + 2 : ℝ) : ℂ) ^ (-s)) := by
    intro k
    dsimp [f]
    rw [pow_succ, pow_mul]
    norm_num
    have hbase : (2 * (k : ℂ) + 1 + 1) =
        (((2 * k + 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hbase]
    rw [Complex.cpow_neg]
    rw [div_eq_mul_inv]
    rw [show (((2 * (k : ℝ) + 2 : ℝ)) : ℂ) =
      2 * (k : ℂ) + 2 by push_cast; ring]
    ring
  have he' : Summable (fun k : ℕ => (((2 * k + 1 : ℝ) : ℂ) ^ (-s))) :=
    he.congr heterm
  have ho' : Summable (fun k : ℕ => (((2 * k + 2 : ℝ) : ℂ) ^ (-s))) := by
    have hneg : Summable (fun k : ℕ => -(((2 * k + 2 : ℝ) : ℂ) ^ (-s))) :=
      ho.congr hoterm
    simpa using hneg.neg
  rw [show (∑' n : ℕ, (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℂ) ^ s)) = ∑' n, f n by rfl,
    ← hsplit, tsum_congr heterm, tsum_congr hoterm, tsum_neg, etaPair]
  rw [← sub_eq_add_neg, ← he'.tsum_sub ho']
  apply tsum_congr
  intro k
  rw [etaTerm]

theorem mellin_salemFermiKernel_eq_gamma_mul_etaPair_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    mellin salemFermiKernel s = Complex.Gamma s * etaPair s := by
  let a : ℕ → ℂ := fun n => (-1 : ℂ) ^ n
  let p : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  have hp : ∀ n, a n = 0 ∨ 0 < p n := fun n => Or.inr (by
    dsimp [p]
    exact_mod_cast Nat.succ_pos n)
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n => a n * Real.exp (-p n * t)) (salemFermiKernel t) := by
    intro t ht
    have h := salemFermiKernel_hasSum ht
    convert h using 1 with n
    funext n
    dsimp [a, p]
    have harg : -(((n + 1 : ℕ) : ℝ)) * t =
        -t - t * (n : ℝ) := by
      push_cast
      ring
    have harg' : -((((n + 1 : ℕ) : ℝ) * t)) =
        -t - t * (n : ℝ) := by
      push_cast
      ring
    rw [harg, harg']
  have hweight : Summable (fun n => ‖a n‖ / p n ^ s.re) := by
    simpa [a, p] using salemFermi_weight_summable hs
  have hmellin : HasSum (fun n => Complex.Gamma s * a n / (p n : ℂ) ^ s)
      (mellin salemFermiKernel s) :=
    hasSum_mellin hp (by linarith) hF hweight
  rw [← hmellin.tsum_eq]
  calc
    (∑' n, Complex.Gamma s * a n / (p n : ℂ) ^ s) =
        ∑' n, Complex.Gamma s * (a n / (p n : ℂ) ^ s) := by
          apply tsum_congr
          intro n
          ring
    _ = Complex.Gamma s * ∑' n, a n / (p n : ℂ) ^ s := tsum_mul_left
    _ = Complex.Gamma s * etaPair s := by
      rw [show (∑' n, a n / (p n : ℂ) ^ s) =
          ∑' n : ℕ, (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℂ) ^ s) by rfl,
        tsum_salemAlternating_eq_etaPair hs]

theorem continuous_salemFermiKernel : Continuous salemFermiKernel := by
  rw [continuous_iff_continuousAt]
  intro t
  change ContinuousAt (fun u : ℝ => (((Real.exp u + 1 : ℝ) : ℂ))⁻¹) t
  apply ContinuousAt.inv₀
  · fun_prop
  · exact_mod_cast (ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos t) zero_le_one))

theorem norm_salemFermiKernel (t : ℝ) :
    ‖salemFermiKernel t‖ = (Real.exp t + 1)⁻¹ := by
  rw [salemFermiKernel, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_pos_of_nonneg (Real.exp_pos t) zero_le_one)]

theorem norm_salemFermiKernel_le_one (t : ℝ) :
    ‖salemFermiKernel t‖ ≤ 1 := by
  rw [norm_salemFermiKernel]
  exact (inv_le_one₀ (by positivity)).2 (by linarith [Real.exp_pos t])

theorem norm_salemFermiKernel_le_exp_neg (t : ℝ) :
    ‖salemFermiKernel t‖ ≤ Real.exp (-t) := by
  rw [norm_salemFermiKernel, Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos t) (by linarith)

theorem salemFermiKernel_locallyIntegrableOn :
    LocallyIntegrableOn salemFermiKernel (Ioi 0) :=
  continuous_salemFermiKernel.continuousOn.locallyIntegrableOn measurableSet_Ioi

theorem salemFermiKernel_isBigO_exp_neg :
    salemFermiKernel =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [] with t
  rw [one_mul, neg_one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact norm_salemFermiKernel_le_exp_neg t

theorem salemFermiKernel_isBigO_one_at_zero :
    salemFermiKernel =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa [neg_zero, Real.rpow_zero] using norm_salemFermiKernel_le_one t

theorem analyticOnNhd_mellin_salemFermiKernel :
    AnalyticOnNhd ℂ (mellin salemFermiKernel) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := 0) (by norm_num)
    salemFermiKernel_locallyIntegrableOn
    salemFermiKernel_isBigO_exp_neg
    salemFermiKernel_isBigO_one_at_zero hs).differentiableWithinAt

theorem mellin_salemFermiKernel_eq_closedForm
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    mellin salemFermiKernel s =
      Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  let G : ℂ → ℂ := fun z =>
    Complex.Gamma z * (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hleft : AnalyticOnNhd ℂ (mellin salemFermiKernel) U :=
    analyticOnNhd_mellin_salemFermiKernel.mono Set.diff_subset
  have hright : AnalyticOnNhd ℂ G U := by
    intro z hz
    have hGamma := HTGeometry.analyticAt_Gamma_of_re_pos hz.1
    have hdyadic : AnalyticAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) z := by
      have hd : Differentiable ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) := by
        apply Differentiable.sub (differentiable_const _)
        exact Differentiable.const_cpow
          ((differentiable_const 1).sub differentiable_id) (Or.inl two_ne_zero)
      exact (hd.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
    have hzeta : AnalyticAt ℂ riemannZeta z :=
      (analyticOn_riemannZeta z (by simpa using hz.2))
    exact (hGamma.mul hdyadic).mul hzeta
  have htwo : (2 : ℂ) ∈ U := by
    exact ⟨by norm_num, by simp⟩
  have hevent :
      mellin salemFermiKernel =ᶠ[𝓝 (2 : ℂ)] G := by
    have hgt : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    rw [mellin_salemFermiKernel_eq_gamma_mul_etaPair_of_one_lt_re hz,
      etaPair_eq z (by linarith) hz1]
    simp only [G]
    ring
  have hEqOn := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    isPreconnected_halfplane_punctured htwo hevent
  exact hEqOn ⟨hs0, by simpa using hs1⟩

theorem mellin_salemFermiKernel_comp_mul_eq_closedForm
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) :
    mellin (fun t => salemFermiKernel (x * t)) s =
      (x : ℂ) ^ (-s) * Complex.Gamma s *
        (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [mellin_comp_mul_left salemFermiKernel s hx, mellin_salemFermiKernel_eq_closedForm hs0 hs1]
  simp only [smul_eq_mul]
  ring

def salemFermiModeIntegral (delta gamma x : ℝ) : ℂ :=
  let s := salemSpectralParameter delta gamma
  mellin (fun t => salemFermiKernel (x * t)) s

theorem salemFermiModeIntegral_eq_integral (delta gamma x : ℝ) :
    salemFermiModeIntegral delta gamma x =
      ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (salemSpectralParameter delta gamma - 1) *
          salemFermiKernel (x * t) := by
  rfl

theorem salemFermiModeIntegral_eq_transform
    {delta gamma x : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hx : 0 < x) :
    salemFermiModeIntegral delta gamma x =
      salemFermiModeTransform delta gamma x := by
  rw [salemFermiModeIntegral, salemFermiModeTransform]
  apply mellin_salemFermiKernel_comp_mul_eq_closedForm
  · simpa using hdelta0
  · intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  · exact hx

def SalemFermiIntegralModeSolution (delta gamma : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → salemFermiModeIntegral delta gamma x = 0

theorem salemFermiIntegralModeSolution_iff_evaluated
    {delta gamma : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    SalemFermiIntegralModeSolution delta gamma ↔
      SalemFermiModeSolution delta gamma := by
  constructor <;> intro h x hx
  · rw [← salemFermiModeIntegral_eq_transform hdelta0 hdelta1 hx]
    exact h x hx
  · rw [salemFermiModeIntegral_eq_transform hdelta0 hdelta1 hx]
    exact h x hx

theorem salemFermiIntegralModeSolution_iff_riemannZeta_eq_zero
    {delta gamma : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    SalemFermiIntegralModeSolution delta gamma ↔
      riemannZeta (salemSpectralParameter delta gamma) = 0 :=
  (salemFermiIntegralModeSolution_iff_evaluated hdelta0 hdelta1).trans
    (salemFermiModeSolution_iff_riemannZeta_eq_zero hdelta0 hdelta1)

def SalemFermiIntegralModeExclusion : Prop :=
  ∀ delta gamma : ℝ, 1 / 2 < delta → delta < 1 →
    ¬ SalemFermiIntegralModeSolution delta gamma

theorem salemFermiIntegralModeExclusion_iff_evaluated :
    SalemFermiIntegralModeExclusion ↔ SalemFermiModeExclusion := by
  constructor
  · intro h delta gamma hhalf hdelta1 hmode
    have hdelta0 : 0 < delta := lt_trans (by norm_num) hhalf
    exact h delta gamma hhalf hdelta1
      ((salemFermiIntegralModeSolution_iff_evaluated hdelta0 hdelta1).mpr hmode)
  · intro h delta gamma hhalf hdelta1 hmode
    have hdelta0 : 0 < delta := lt_trans (by norm_num) hhalf
    exact h delta gamma hhalf hdelta1
      ((salemFermiIntegralModeSolution_iff_evaluated hdelta0 hdelta1).mp hmode)

theorem salemFermiIntegralModeExclusion_iff_riemannHypothesis :
    SalemFermiIntegralModeExclusion ↔ RiemannHypothesis :=
  salemFermiIntegralModeExclusion_iff_evaluated.trans
    salemFermiModeExclusion_iff_riemannHypothesis

end

end RHTower
