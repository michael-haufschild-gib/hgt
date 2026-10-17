import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.DigammaBinetFourthOrder
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral
import GaloisForLFunctions.RHTower.DigammaVerticalGrowthBound
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy

/-!
# Weil-cone anatomy: pole-free cones are fat, and cones embed under factorization

An archimedean datum `D` is a pole term on tests and a spectral density.  Its Weil functional at
real weights `λ` on the autocorrelation `k = f ⋆ f̃` is
`W_{D,λ}(f) = pole_D(k) + ∫ |f̂(t)|² Ω_D(t) dt − Σ_{n≥2} λ(n) n^{−½} Re(k(log n) + k(−log n))`,
and `λ` lies in the Weil cone of `D` if `W_{D,λ} ≥ 0` on every `f ∈ C²_c` (`InWeilCone`).

**(A) Pole-free data with nonnegative density have fat cones.**
* Level-1 forms of weight `k = 2m ≥ 14`: `Ω_f(t) = (1/π)(Re ψ(m + it) − log 2π) > 0`, because
  `Re ψ(m + it) ≥ ψ(m) ≥ ψ(7) > log 2π` (`modularDatum_zero_mem_cone`; `ψ(7) > log 2π` from the
  fourth-order digamma estimate).
* Dirichlet `L(s, χ)`: `Ω_χ(t) = (1/2π)(log(q/π) + Re ψ((½ + a + it)/2)) ≥ 0` for odd `χ` with
  `q ≥ 10` and even `χ` with `q ≥ 216` (`dirichletDatum_odd_zero_mem_cone`,
  `dirichletDatum_even_zero_mem_cone`).
* Hence no condition can pin such a cone to a single nonzero weight system
  (`eq_zero_of_cone_pinned`).

**(B) Cone embedding.**  For `L = ζ·L′` with `L′` pole-free, `Ω_{L′} ≥ 0`:
`W_{L,λ} = W_{ζ,λ} + ∫ |f̂|² Ω_{L′}` (`weilFunctional_mulDatum`), so under RH `Λ ∈ cone_L`
(`vonMangoldt_mem_cone_mulDatum`); hence a pinning `cone_L ⊆ {Λ + Λ_{L′}}` with `Λ_{L′} ≠ 0`
refutes RH (`not_riemannHypothesis_of_pinned`), e.g. for `ζ·L(s, χ)` with odd `χ` of conductor
`q ≥ 10`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower.PoleDualityAnatomy

noncomputable section

/-- An archimedean datum: a pole functional and a spectral density. -/
structure ArchDatum where
  pole : (ℝ → ℂ) → ℝ
  density : ℝ → ℝ

/-- The prime comb `Σ_{n≥2} λ(n) n^{−½} Re(k(log n) + k(−log n))`. -/
def primeComb (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℝ :=
  (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
    (k (Real.log n) + k (-Real.log n))).re

/-- The Weil functional of a datum. -/
def weilFunctional (D : ArchDatum) (lam : ℕ → ℝ) (f : ℝ → ℂ) : ℝ :=
  D.pole (EF.weilTest f f) + (∫ t : ℝ, ‖paperFT f t‖ ^ 2 * D.density t) -
    primeComb lam (EF.weilTest f f)

/-- Membership in the Weil cone of a datum. -/
def InWeilCone (D : ArchDatum) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ weilFunctional D lam f

theorem primeComb_zero (k : ℝ → ℂ) : primeComb (fun _ => 0) k = 0 := by
  simp [primeComb]

/-- A pole-free datum with nonnegative density contains the zero weights. -/
theorem zero_mem_cone_of_density_nonneg {D : ArchDatum} (hpole : ∀ k, D.pole k = 0)
    (hD : ∀ t, 0 ≤ D.density t) : InWeilCone D fun _ => 0 := by
  intro f _ _
  rw [weilFunctional, hpole, primeComb_zero, zero_add, sub_zero]
  exact integral_nonneg fun t => mul_nonneg (sq_nonneg _) (hD t)

/-- **Pinning forces the weights to vanish.** -/
theorem eq_zero_of_cone_pinned {D : ArchDatum} {Λ' : ℕ → ℝ} (h0 : InWeilCone D fun _ => 0)
    (hpin : ∀ lam, InWeilCone D lam → ∀ n, 2 ≤ n → lam n = Λ' n) : ∀ n, 2 ≤ n → Λ' n = 0 :=
  fun n hn => (hpin _ h0 n hn).symm

/-! ### (A) Holomorphic forms of level one -/

/-- The datum of a level-one form of weight `2m`: no pole, density
`(1/π)(Re ψ(m + it) − log 2π)`. -/
def modularDatum (m : ℕ) : ArchDatum :=
  ⟨fun _ => 0, fun t => 1 / π * ((Complex.digamma ((m : ℂ) + (t : ℂ) * I)).re - Real.log (2 * π))⟩

/-- `ψ(7) > log 2π`. -/
theorem log_two_pi_lt_re_digamma_seven : Real.log (2 * π) < (Complex.digamma (7 : ℂ)).re := by
  have hw : 0 < (7 : ℂ).re := by norm_num
  have h := DigammaBinet.norm_digamma_sub_stirling_le hw
  have h2 := (Complex.abs_re_le_norm _).trans h
  have hlog : (Complex.log (7 : ℂ)).re = Real.log 7 := by
    rw [Complex.log_re]; norm_num
  have h1 : (1 / (2 * (7 : ℂ))).re = 1 / 14 := by norm_num
  have h12 : (1 / (12 * (7 : ℂ) ^ 2)).re = 1 / 588 := by norm_num
  rw [Complex.add_re, Complex.add_re, Complex.sub_re, hlog, h1, h12] at h2
  have hre7 : (7 : ℂ).re = 7 := by norm_num
  rw [hre7] at h2
  have hlow := (abs_le.mp h2).1
  -- `log 7 − log 2π > 0.08 > 1/14 + 1/588 + 1/(120·7⁴)`
  have hratio : (8 / 100 : ℝ) < Real.log 7 - Real.log (2 * π) := by
    rw [← Real.log_div (by norm_num) (by positivity), Real.lt_log_iff_exp_lt (by positivity)]
    have hT := Real.exp_bound' (show (0 : ℝ) ≤ 8 / 100 by norm_num)
      (show (8 / 100 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
    norm_num at hT
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2, Real.pi_pos, Real.exp_pos (8 / 100)]
  norm_num at hlow
  linarith

/-- `Re ψ(m + it) ≥ ψ(7)` for `m ≥ 7`. -/
theorem re_digamma_seven_le {m : ℕ} (hm : 7 ≤ m) (t : ℝ) :
    (Complex.digamma (7 : ℂ)).re ≤ (Complex.digamma ((m : ℂ) + (t : ℂ) * I)).re := by
  have hv := digamma_real_le_re_digamma_add_mul_I (a := (m : ℝ)) (by positivity) t
  push_cast at hv
  refine le_trans ?_ hv
  have hpole : ∀ k : ℕ, (7 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hrec := HTGeometry.digamma_add_nat 7 hpole (m - 7)
  have hcast : (7 : ℂ) + ((m - 7 : ℕ) : ℂ) = (m : ℂ) := by
    rw [Nat.cast_sub hm]; push_cast; ring
  rw [hcast] at hrec
  rw [hrec, Complex.add_re, Complex.re_sum]
  have : 0 ≤ ∑ i ∈ Finset.range (m - 7), ((7 : ℂ) + (i : ℂ))⁻¹.re := by
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Complex.inv_re]
    exact div_nonneg (by simp; positivity) (Complex.normSq_nonneg _)
  linarith

/-- **Level-one forms of weight `≥ 14` have fat cones**: the zero weights lie in the cone. -/
theorem modularDatum_zero_mem_cone {m : ℕ} (hm : 7 ≤ m) : InWeilCone (modularDatum m) fun _ => 0 :=
  zero_mem_cone_of_density_nonneg (fun _ => rfl) fun t => by
    simp only [modularDatum]
    have h1 := re_digamma_seven_le hm t
    have h2 := log_two_pi_lt_re_digamma_seven
    exact mul_nonneg (by positivity) (by linarith)

/-! ### (A) Dirichlet `L`-functions -/

/-- The datum of `L(s, χ)` with conductor `q` and parity `a`: no pole, density
`(1/2π)(log(q/π) + Re ψ((½ + a + it)/2))`. -/
def dirichletDatum (q : ℝ) (a : ℕ) : ArchDatum :=
  ⟨fun _ => 0, fun t => 1 / (2 * π) * (Real.log (q / π) +
    (Complex.digamma ((1 / 2 + (a : ℂ) + (t : ℂ) * I) / 2)).re)⟩

theorem log_pi_le : Real.log π ≤ 11448 / 10000 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have he := Real.exp_one_gt_d9
  have hT := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1448 / 10000 by norm_num) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hsplit : Real.exp (11448 / 10000) = Real.exp 1 * Real.exp (1448 / 10000) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.pi_lt_d6, Real.exp_pos 1, Real.exp_pos (1448 / 10000)]

theorem log_three_ge : 10985 / 10000 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_lt_d9
  have hT := Real.exp_bound' (show (0 : ℝ) ≤ 985 / 10000 by norm_num)
    (show (985 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 4 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hsplit : Real.exp (10985 / 10000) = Real.exp 1 * Real.exp (985 / 10000) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.exp_pos 1, Real.exp_pos (985 / 10000)]

/-- **Odd characters of conductor `q ≥ 10` have fat cones.** -/
theorem dirichletDatum_odd_zero_mem_cone {q : ℝ} (hq : 10 ≤ q) :
    InWeilCone (dirichletDatum q 1) fun _ => 0 := by
  refine zero_mem_cone_of_density_nonneg (fun _ => rfl) fun t => ?_
  simp only [dirichletDatum]
  refine mul_nonneg (by positivity) ?_
  have harg : (1 / 2 + ((1 : ℕ) : ℂ) + (t : ℂ) * I) / 2 = ((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg]
  have hv := digamma_real_le_re_digamma_add_mul_I (a := 3 / 4) (by norm_num) (t / 2)
  have h34 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 + π / 2 := by
    rw [show (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) by push_cast; ring, re_digamma_three_quarters_eq,
      re_digamma_one_quarter]
    ring
  have hγ := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hlogq : Real.log (q / π) ≥ Real.log (10 / π) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hq Real.pi_pos.le)
  have hl10 : Real.log (10 / π) = Real.log 2 + Real.log 5 - Real.log π := by
    rw [Real.log_div (by norm_num) Real.pi_ne_zero, show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h5 := log_five_ge
  have hl2 := Real.log_two_gt_d9
  have hpi := log_pi_le
  have hπ := Real.pi_gt_d2
  linarith

/-- **Even characters of conductor `q ≥ 216` have fat cones.** -/
theorem dirichletDatum_even_zero_mem_cone {q : ℝ} (hq : 216 ≤ q) :
    InWeilCone (dirichletDatum q 0) fun _ => 0 := by
  refine zero_mem_cone_of_density_nonneg (fun _ => rfl) fun t => ?_
  simp only [dirichletDatum]
  refine mul_nonneg (by positivity) ?_
  have harg : (1 / 2 + ((0 : ℕ) : ℂ) + (t : ℂ) * I) / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg]
  have hv := digamma_real_le_re_digamma_add_mul_I (a := 1 / 4) (by norm_num) (t / 2)
  have h14 : (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 - π / 2 := by
    rw [show (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) by push_cast; ring, re_digamma_one_quarter]
  have hγ := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hlogq : Real.log (q / π) ≥ Real.log (216 / π) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hq Real.pi_pos.le)
  have hl216 : Real.log (216 / π) = 3 * Real.log 2 + 3 * Real.log 3 - Real.log π := by
    rw [Real.log_div (by norm_num) Real.pi_ne_zero, show (216 : ℝ) = 2 ^ 3 * 3 ^ 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have h3 := log_three_ge
  have hl2 := Real.log_two_gt_d9
  have hpi := log_pi_le
  have hπ := Real.pi_lt_d6
  linarith

/-! ### (B) Cone embedding under factorization -/

/-- The datum of `ζ`: pole `Re(k̂(i/2) + k̂(−i/2))` and density `Ω/2π`. -/
def zetaDatum : ArchDatum :=
  ⟨fun k => (paperFT k (I / 2) + paperFT k (-I / 2)).re, fun t => 1 / (2 * π) * EF.gammaBracket t⟩

/-- The datum of a product `L₁ L₂`: pole terms and densities add. -/
def mulDatum (D₁ D₂ : ArchDatum) : ArchDatum :=
  ⟨fun k => D₁.pole k + D₂.pole k, fun t => D₁.density t + D₂.density t⟩

theorem integrable_zeta_density {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable fun t : ℝ => ‖paperFT f t‖ ^ 2 * zetaDatum.density t := by
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
  refine (hintC.re.const_mul (1 / (2 * π))).congr (Eventually.of_forall fun r => ?_)
  show 1 / (2 * π) * (paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re = _
  rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [zetaDatum]
  ring

/-- The `ζ` datum recovers the corpus Weil functional. -/
theorem weilFunctional_zetaDatum (lam : ℕ → ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    weilFunctional zetaDatum lam f = (weilFullFunctional lam (EF.weilTest f f)).re := by
  have harch : ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r *
      (EF.gammaBracket r : ℂ)).re = ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * zetaDatum.density t := by
    have hpt : ∀ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
        ((‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
      rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc]; push_cast; ring
    simp_rw [hpt]
    rw [integral_complex_ofReal, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re, ← integral_const_mul]
    congr 1; funext t; simp only [zetaDatum]; ring
  rw [weilFunctional, weilFullFunctional, ← harch, primeComb]
  simp only [zetaDatum, Complex.add_re, Complex.sub_re]
  ring

/-- Densities of at most linear growth pair integrably with test transforms. -/
theorem integrable_density_of_growth {Ω : ℝ → ℝ} (hΩ : Continuous Ω) {A : ℝ}
    (hA : ∀ t, |Ω t| ≤ A * (1 + |t|)) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : Integrable fun t : ℝ => ‖paperFT f t‖ ^ 2 * Ω t := by
  obtain ⟨D, hD0, hD⟩ := WeilOneSided.exists_norm_paperFT_le_decay (⟨f, hf, hfc⟩ : WeilOneSided.WeilTestFn)
  have hA0 : 0 ≤ A := by have := hA 0; simp at this; exact (abs_nonneg _).trans this
  have hbi : Integrable fun t : ℝ => D ^ 2 * A * (1 + ‖t‖) ^ (-(3 : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by simp)).const_mul _
  have hc : Continuous fun t : ℝ => ‖paperFT f t‖ ^ 2 * Ω t :=
    ((((WeilEF.differentiable_paperFT hf.continuous hfc).continuous.comp
      Complex.continuous_ofReal).norm).pow 2).mul hΩ
  refine hbi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 : 0 < 1 + |t| := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : ‖paperFT f t‖ ^ 2 ≤ (D / (1 + |t|) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD t) 2
  calc ‖paperFT f t‖ ^ 2 * |Ω t| ≤ (D / (1 + |t|) ^ 2) ^ 2 * (A * (1 + |t|)) :=
        mul_le_mul hsq (hA t) (abs_nonneg _) (sq_nonneg _)
    _ = D ^ 2 * A * ((1 + |t|) ^ 3)⁻¹ := by field_simp

/-- **Factorization**: for a pole-free `L′` with continuous density of linear growth,
`W_{ζL′,λ} = W_{ζ,λ} + ∫ |f̂|² Ω_{L′}`. -/
theorem weilFunctional_mulDatum {D₂ : ArchDatum} (hpole : ∀ k, D₂.pole k = 0)
    (hc : Continuous D₂.density) {A : ℝ} (hA : ∀ t, |D₂.density t| ≤ A * (1 + |t|))
    (lam : ℕ → ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilFunctional (mulDatum zetaDatum D₂) lam f =
      (weilFullFunctional lam (EF.weilTest f f)).re + ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * D₂.density t := by
  rw [← weilFunctional_zetaDatum lam hf hfc, weilFunctional, weilFunctional]
  have h1 := integrable_zeta_density hf hfc
  have h2 := integrable_density_of_growth hc hA hf hfc
  have hsplit : ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * (mulDatum zetaDatum D₂).density t =
      (∫ t : ℝ, ‖paperFT f t‖ ^ 2 * zetaDatum.density t) +
        ∫ t : ℝ, ‖paperFT f t‖ ^ 2 * D₂.density t := by
    rw [← integral_add h1 h2]
    congr 1; funext t; simp only [mulDatum]; ring
  rw [hsplit]
  simp only [mulDatum, hpole]
  ring

/-- **Under RH, `Λ` lies in the cone of `ζ·L′`.** -/
theorem vonMangoldt_mem_cone_mulDatum (hRH : RiemannHypothesis) {D₂ : ArchDatum}
    (hpole : ∀ k, D₂.pole k = 0) (hD : ∀ t, 0 ≤ D₂.density t) (hc : Continuous D₂.density) {A : ℝ}
    (hA : ∀ t, |D₂.density t| ≤ A * (1 + |t|)) :
    InWeilCone (mulDatum zetaDatum D₂) fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  intro f hf hfc
  rw [weilFunctional_mulDatum hpole hc hA _ hf hfc]
  have hW := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f hf hfc
  exact add_nonneg hW (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (hD t))

/-- **A pinning of the cone of `ζ·L′` refutes RH.**  If the cone of `ζ·L′` is contained in
`{Λ + Λ′}` with `Λ′ ≠ 0` at some `n ≥ 2`, then RH fails. -/
theorem not_riemannHypothesis_of_pinned {D₂ : ArchDatum} (hpole : ∀ k, D₂.pole k = 0)
    (hD : ∀ t, 0 ≤ D₂.density t) (hc : Continuous D₂.density) {A : ℝ}
    (hA : ∀ t, |D₂.density t| ≤ A * (1 + |t|)) {Λ' : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hΛ' : Λ' n₀ ≠ 0)
    (hpin : ∀ lam, InWeilCone (mulDatum zetaDatum D₂) lam → ∀ n, 2 ≤ n →
      lam n = (ArithmeticFunction.vonMangoldt n : ℝ) + Λ' n) :
    ¬ RiemannHypothesis := fun hRH => by
  have := hpin _ (vonMangoldt_mem_cone_mulDatum hRH hpole hD hc hA) n₀ hn₀
  exact hΛ' (by linarith)

/-- The odd Dirichlet density is continuous, nonnegative for `q ≥ 10`, and of linear growth. -/
theorem dirichletDatum_odd_props {q : ℝ} (hq : 10 ≤ q) :
    (∀ t, 0 ≤ (dirichletDatum q 1).density t) ∧ Continuous (dirichletDatum q 1).density ∧
      ∃ A, ∀ t, |(dirichletDatum q 1).density t| ≤ A * (1 + |t|) := by
  have harg : ∀ t : ℝ, (1 / 2 + ((1 : ℕ) : ℂ) + (t : ℂ) * I) / 2 =
      ((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := fun t => by push_cast; ring
  refine ⟨fun t => ?_, ?_, ?_⟩
  · simp only [dirichletDatum]
    refine mul_nonneg (by positivity) ?_
    rw [harg]
    have hv := digamma_real_le_re_digamma_add_mul_I (a := 3 / 4) (by norm_num) (t / 2)
    have h34 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re =
        -Real.eulerMascheroniConstant - 3 * Real.log 2 + π / 2 := by
      rw [show (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) by push_cast; ring, re_digamma_three_quarters_eq,
        re_digamma_one_quarter]
      ring
    have hγ :=
      eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    have hlogq : Real.log (q / π) ≥ Real.log (10 / π) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hq Real.pi_pos.le)
    have hl10 : Real.log (10 / π) = Real.log 2 + Real.log 5 - Real.log π := by
      rw [Real.log_div (by norm_num) Real.pi_ne_zero, show (10 : ℝ) = 2 * 5 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have h5 := log_five_ge
    have hl2 := Real.log_two_gt_d9
    have hpi := log_pi_le
    have hπ := Real.pi_gt_d2
    linarith
  · simp only [dirichletDatum]
    refine continuous_const.mul (continuous_const.add ?_)
    simp_rw [harg]
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
    exact ContinuousAt.comp (g := Complex.digamma)
      (f := fun t : ℝ => ((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)
      (differentiableAt_digamma_of_re_pos (by norm_num)).continuousAt (by fun_prop)
  · set K := digammaVerticalGrowthConst (3 / 4)
    have hK0 : 0 ≤ K := digammaVerticalGrowthConst_nonneg (by norm_num)
    refine ⟨(|Real.log (q / π)| + K + 1) / (2 * π), fun t => ?_⟩
    simp only [dirichletDatum]
    rw [harg]
    have hg := abs_re_digamma_vertical_le (c := 3 / 4) (by norm_num) (t / 2)
    have hlog : Real.log (2 + |t / 2|) ≤ 1 + |t| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + |t / 2| by positivity)
      rw [abs_div, abs_two] at this ⊢
      linarith [abs_nonneg t]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    have h1 : |Real.log (q / π) + (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re| ≤
        |Real.log (q / π)| + K + 1 + |t| := by
      refine (abs_add_le _ _).trans ?_
      linarith
    have h2 : |Real.log (q / π)| + K + 1 + |t| ≤ (|Real.log (q / π)| + K + 1) * (1 + |t|) := by
      nlinarith [abs_nonneg t, abs_nonneg (Real.log (q / π))]
    calc 1 / (2 * π) * |Real.log (q / π) +
          (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re| ≤
        1 / (2 * π) * ((|Real.log (q / π)| + K + 1) * (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = (|Real.log (q / π)| + K + 1) / (2 * π) * (1 + |t|) := by ring

/-- **Example: `ζ·L(s, χ)` for odd `χ` of conductor `q ≥ 10`.**  A pinning of its cone to
`{Λ + Λ′}` with `Λ′ ≠ 0` refutes RH. -/
theorem not_riemannHypothesis_of_pinned_dirichlet {q : ℝ} (hq : 10 ≤ q) {Λ' : ℕ → ℝ} {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hΛ' : Λ' n₀ ≠ 0)
    (hpin : ∀ lam, InWeilCone (mulDatum zetaDatum (dirichletDatum q 1)) lam → ∀ n, 2 ≤ n →
      lam n = (ArithmeticFunction.vonMangoldt n : ℝ) + Λ' n) :
    ¬ RiemannHypothesis := by
  obtain ⟨hD, hc, A, hA⟩ := dirichletDatum_odd_props hq
  exact not_riemannHypothesis_of_pinned (fun _ => rfl) hD hc hA hn₀ hΛ' hpin

end

end RHTower.PoleDualityAnatomy
