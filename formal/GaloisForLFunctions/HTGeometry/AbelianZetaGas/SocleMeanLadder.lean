import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleExchangeWork
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The socle mean as a von Mangoldt ladder

The socle ladder `L(v) = ∏_{j≥1} ζ(jσ + v)` converges locally uniformly on the socle chamber, so its
logarithmic derivative is the sum of the logarithmic derivatives of its factors.  Differentiating
the moment generating function `E_{σ,τ} e^{-tQ} = L(τ + t)/L(τ)` at `t = 0` gives

  `E_{σ,τ} Q = -L'(τ)/L(τ) = ∑_{j≥1} (-ζ'/ζ)(jσ + τ) = ∑_{j≥1} ∑_n Λ(n) n^{-(jσ+τ)}`,

and hence the explicit exchange work
`J(P_0, P_u) = u ∑_{j≥1} [(-ζ'/ζ)(jσ + τ) - (-ζ'/ζ)(jσ + τ + u)]`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Set ArithmeticFunction
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

/-- The depth factor `w ↦ ζ((j+1)σ + w)` of the socle ladder. -/
def ladderFactor (σ : ℝ) (j : ℕ) (w : ℂ) : ℂ := riemannZeta (depthArg σ w (j + 1) 0)

theorem socleLadder_eq_tprod_ladderFactor (σ : ℝ) (w : ℂ) :
    socleLadder σ w = ∏' j, ladderFactor σ j w := by
  rw [socleLadder_eq_tprod]
  refine tprod_congr fun j => ?_
  simp only [ladderFactor, depthArg]
  congr 1
  push_cast
  ring

theorem re_depthArg_succ (σ : ℝ) (w : ℂ) (j : ℕ) :
    (depthArg σ w (j + 1) 0).re = ((j : ℝ) + 1) * σ + w.re := by
  rw [re_depthArg]
  push_cast
  simp

theorem one_lt_re_depthArg_succ {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) {w : ℂ}
    (hw : b < w.re) (j : ℕ) : 1 < (depthArg σ w (j + 1) 0).re := by
  rw [re_depthArg_succ]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem differentiableAt_ladderFactor {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) {w : ℂ}
    (hw : b < w.re) (j : ℕ) : DifferentiableAt ℂ (ladderFactor σ j) w := by
  have hre := one_lt_re_depthArg_succ hσ hb hw j
  have hne : depthArg σ w (j + 1) 0 ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have haff : DifferentiableAt ℂ (fun w : ℂ => depthArg σ w (j + 1) 0) w := by
    show DifferentiableAt ℂ (fun w : ℂ => ((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + (0 : ℂ)) + w) w
    exact (differentiableAt_const _).add differentiableAt_id
  exact (differentiableAt_riemannZeta hne).comp w haff

theorem ladderFactor_ne_zero {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) {w : ℂ} (hw : b < w.re)
    (j : ℕ) : ladderFactor σ j w ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (one_lt_re_depthArg_succ hσ hb hw j)

/-- The socle ladder converges locally uniformly on every half-plane inside the chamber. -/
theorem hasProdLocallyUniformlyOn_ladder {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) :
    HasProdLocallyUniformlyOn (ladderFactor σ) (socleLadder σ) {w : ℂ | b < w.re} := by
  have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmaj : Summable fun j : ℕ => 4 * (((2 : ℝ) ^ (-σ)) ^ (j + 1) * (2 : ℝ) ^ (-b)) :=
    ((((summable_geometric_of_lt_one (geomRatio_nonneg _) (geomRatio_lt_one hσ)).comp_injective
      (add_left_injective 1)).mul_right _).mul_left 4)
  have hbound : ∀ᶠ j in atTop, ∀ w ∈ {w : ℂ | b < w.re},
      ‖riemannZeta (depthArg σ w (j + 1) 0) - 1‖ ≤
        4 * (((2 : ℝ) ^ (-σ)) ^ (j + 1) * (2 : ℝ) ^ (-b)) := by
    filter_upwards [eventually_ge_atTop (SocleTail.socleTailThreshold σ b)] with j hj w hw
    exact SocleTail.norm_zeta_socleArg_sub_one_le hσ hw.le (by omega)
  have hcts : ∀ j, ContinuousOn (fun w => riemannZeta (depthArg σ w (j + 1) 0) - 1)
      {w : ℂ | b < w.re} := fun j w hw =>
    ((differentiableAt_ladderFactor hσ hb hw j).continuousAt.sub
      continuousAt_const).continuousWithinAt
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add hopen hmaj hbound hcts
  have hfun : (fun (j : ℕ) (w : ℂ) => 1 + (riemannZeta (depthArg σ w (j + 1) 0) - 1)) =
      ladderFactor σ := by
    funext j w
    simp only [ladderFactor]
    ring
  have hval : (fun w : ℂ => ∏' j, (1 + (riemannZeta (depthArg σ w (j + 1) 0) - 1))) =
      socleLadder σ := by
    funext w
    rw [socleLadder_eq_tprod_ladderFactor]
    exact tprod_congr fun j => by simp only [ladderFactor]; ring
  rwa [hfun, hval] at h

/-- **Logarithmic derivative of the socle ladder.**  On the socle chamber,
`L'/L = ∑_{j≥1} ζ'/ζ(jσ + v)`. -/
theorem hasSum_logDeriv_ladderFactor {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : v ∈ socleChamber σ) :
    HasSum (fun j => logDeriv (ladderFactor σ j) v) (logDeriv (socleLadder σ) v) := by
  have hv' : 1 - σ < v.re := hv
  set b : ℝ := (1 - σ + v.re) / 2 with hbdef
  have hb : 1 - σ < b := by linarith
  have hvb : b < v.re := by linarith
  have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF := hasProdLocallyUniformlyOn_ladder hσ hb
  have hne : socleLadder σ v ≠ 0 := socleLadder_ne_zero_of_mem hσ hv
  have hlim := Complex.logDeriv_tendsto hopen hvb hF (Eventually.of_forall fun s w hw =>
    (DifferentiableAt.fun_finsetProd fun j _ =>
      differentiableAt_ladderFactor hσ hb hw j).differentiableWithinAt) hne
  refine hlim.congr fun s => ?_
  exact logDeriv_prod (fun j _ => ladderFactor_ne_zero hσ hb hvb j)
    (fun j _ => differentiableAt_ladderFactor hσ hb hvb j)

theorem logDeriv_ladderFactor {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) {w : ℂ} (hw : b < w.re)
    (j : ℕ) :
    logDeriv (ladderFactor σ j) w =
      deriv riemannZeta (depthArg σ w (j + 1) 0) / riemannZeta (depthArg σ w (j + 1) 0) := by
  have hre := one_lt_re_depthArg_succ hσ hb hw j
  have hne : depthArg σ w (j + 1) 0 ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have hcomp : ladderFactor σ j = riemannZeta ∘ fun w : ℂ => depthArg σ w (j + 1) 0 := rfl
  have haff : HasDerivAt (fun w : ℂ => depthArg σ w (j + 1) 0) 1 w := by
    show HasDerivAt (fun w : ℂ => ((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + (0 : ℂ)) + w) 1 w
    exact (hasDerivAt_id w).const_add _
  rw [hcomp, logDeriv_comp (g := fun w : ℂ => depthArg σ w (j + 1) 0)
    (differentiableAt_riemannZeta hne) haff.differentiableAt, haff.deriv, mul_one, logDeriv_apply]

/-- The von Mangoldt mass `∑_n Λ(n) n^{-x} = (-ζ'/ζ)(x)` for `x > 1`. -/
def vonMangoldtMass (x : ℝ) : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-x)

/-- `(-L'/L)(τ) = ∑_{j≥1} (-ζ'/ζ)(jσ + τ)` for real `τ` in the chamber. -/
theorem hasSum_neg_logDeriv_socleLadder {σ τ : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) :
    HasSum (fun j : ℕ => vonMangoldtMass (((j : ℝ) + 1) * σ + τ))
      (-logDeriv (socleLadder σ) (τ : ℂ)).re := by
  set b : ℝ := (1 - σ + τ) / 2 with hbdef
  have hb : 1 - σ < b := by linarith
  have hvb : b < ((τ : ℂ)).re := by simp only [Complex.ofReal_re]; linarith
  have hsum := (hasSum_logDeriv_ladderFactor hσ (v := (τ : ℂ))
    (by simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]; linarith)).neg
  have hterm : ∀ j : ℕ, -logDeriv (ladderFactor σ j) (τ : ℂ) =
      ((vonMangoldtMass (((j : ℝ) + 1) * σ + τ) : ℝ) : ℂ) := by
    intro j
    have hx : 1 < ((j : ℝ) + 1) * σ + τ := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hd : depthArg σ (τ : ℂ) (j + 1) 0 = ((((j : ℝ) + 1) * σ + τ : ℝ) : ℂ) := by
      simp only [depthArg]
      push_cast
      ring
    rw [logDeriv_ladderFactor hσ hb hvb j, vonMangoldtMass, ofReal_tsum_vonMangoldt_eq hx, hd,
      neg_div]
  simp_rw [hterm] at hsum
  exact (Complex.hasSum_re hsum).congr_fun fun j => by simp

namespace GasChamber

variable (c : GasChamber)

/-- The socle mean is minus the logarithmic derivative of the socle ladder:
`E_{σ,τ} Q = -(L'/L)(τ)`. -/
theorem integral_socleLog_law_eq_logDeriv :
    ∫ A, socleLog A ∂c.law = (-logDeriv (socleLadder c.sigma) (c.tau : ℂ)).re := by
  have hτ : (c.tau : ℂ) ∈ socleChamber c.sigma := by
    simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]
    linarith [c.firstDepth]
  have h0 := c.mem_interior_integrableExpSet (t := 0) (by linarith [c.firstDepth])
  have hdm := deriv_mgf h0
  have hev : mgf (fun A => -socleLog A) c.law =ᶠ[𝓝 0] fun t : ℝ =>
      (socleLadder c.sigma ((c.tau : ℂ) + (t : ℂ))).re / c.partition := by
    filter_upwards [Ioi_mem_nhds (show 1 - c.sigma - c.tau < 0 by linarith [c.firstDepth])]
      with t ht
    have htt : 1 < c.sigma + c.tau + t := by
      simp only [mem_Ioi] at ht
      linarith
    rw [mgf, integral_law_exp_neg_socle c htt]
    simp only [partition, translate]
    push_cast
    rfl
  have hL : DifferentiableAt ℂ (socleLadder c.sigma) (c.tau : ℂ) :=
    (differentiableOn_socleLadder c.sigma_pos).differentiableAt
      ((isOpen_socleChamber c.sigma).mem_nhds hτ)
  have hcomp : HasDerivAt (fun w : ℂ => socleLadder c.sigma ((c.tau : ℂ) + w))
      (deriv (socleLadder c.sigma) (c.tau : ℂ)) ((0 : ℝ) : ℂ) := by
    have hL' : HasDerivAt (socleLadder c.sigma) (deriv (socleLadder c.sigma) (c.tau : ℂ))
        ((c.tau : ℂ) + id ((0 : ℝ) : ℂ)) := by
      simpa using hL.hasDerivAt
    have h := hL'.comp ((0 : ℝ) : ℂ) ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_add (c.tau : ℂ))
    rw [mul_one] at h
    exact h
  have hderiv := (hcomp.real_of_complex).div_const c.partition
  rw [hev.deriv_eq, hderiv.deriv] at hdm
  simp only [zero_mul, Real.exp_zero, mul_one] at hdm
  rw [integral_neg] at hdm
  have hP : (c.partition : ℂ) = socleLadder c.sigma (c.tau : ℂ) := c.ofReal_partition
  rw [logDeriv_apply, ← hP, ← neg_div, Complex.div_ofReal_re, Complex.neg_re, neg_div]
  linarith

/-- `(AZC.16)`  **Socle mean ladder.**  `E_{σ,τ} Q = ∑_{j≥1} (-ζ'/ζ)(jσ + τ)
= ∑_{j≥1} ∑_n Λ(n) n^{-(jσ+τ)}`. -/
theorem integral_socleLog_law_eq_tsum :
    ∫ A, socleLog A ∂c.law = ∑' j : ℕ, vonMangoldtMass (((j : ℝ) + 1) * c.sigma + c.tau) := by
  rw [integral_socleLog_law_eq_logDeriv,
    (hasSum_neg_logDeriv_socleLadder c.sigma_pos c.firstDepth).tsum_eq]

theorem hasSum_socleMean :
    HasSum (fun j : ℕ => vonMangoldtMass (((j : ℝ) + 1) * c.sigma + c.tau))
      (∫ A, socleLog A ∂c.law) := by
  rw [integral_socleLog_law_eq_logDeriv]
  exact hasSum_neg_logDeriv_socleLadder c.sigma_pos c.firstDepth

/-- `(AZC.16)`  **Explicit exchange work.**
`J(P_0, P_u) = u ∑_{j≥1} [(-ζ'/ζ)(jσ + τ) - (-ζ'/ζ)(jσ + τ + u)]`. -/
theorem formationJeffreys_translate_eq_tsum (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    formationJeffreys c.law (c.translate u hu).law =
      ENNReal.ofReal (u * ∑' j : ℕ, (vonMangoldtMass (((j : ℝ) + 1) * c.sigma + c.tau) -
        vonMangoldtMass (((j : ℝ) + 1) * c.sigma + c.tau + u))) := by
  have h1 := c.hasSum_socleMean
  have h2 := (c.translate u hu).hasSum_socleMean
  rw [c.formationJeffreys_translate u hu]
  congr 2
  rw [← (h1.sub h2).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [translate, add_assoc]

end GasChamber

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
