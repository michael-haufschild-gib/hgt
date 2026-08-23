import GaloisForLFunctions.RHTower.BVPrimeWindowCoPoissonNormalConnection
import GaloisForLFunctions.RHTower.BVPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.BVPrimeWindowIntervalSource
import GaloisForLFunctions.RHTower.CoefficientHardyLSeries

/-!
# Dirichlet--Hardy exclusion for BV prime-polar coefficients

For every compact BV prime window, its exact polar coefficient has ordinary Dirichlet series equal
to the canonical continued source on `Re s > 3/2`.  If that source sees a completed-zeta zero, its
pole prevents the coefficient from belonging to unweighted coefficient Hardy space `H₀ = ℓ²`.

The proof is multiplicity-safe.  Multiplying by the shifted pole-filled zeta produces the analytic
co-Poisson cancelled source.  At a zero of order `m+1`, this source has exact order `m`, whereas a
holomorphic coefficient L-series would make the product vanish to order at least `m+1`.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- At every uncensored completed-zeta zero, the co-Poisson cancelled source loses exactly one
vanishing order.  This retains the full zero multiplicity without assuming simplicity. -/
theorem analyticOrderAt_coPoissonCancelledSource_eq_pred_of_mellin_ne_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0)
    (hMne : W.mellinTransform (rho + 1 / 2) ≠ 0) :
    ∃ m : ℕ,
      analyticOrderAt
          (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
          (rho + 1 / 2) = (m + 1 : ℕ) ∧
      analyticOrderAt W.coPoissonCancelledSource
          (rho + 1 / 2) = m := by
  let p : ℂ := rho + 1 / 2
  have hpρ : p - 1 / 2 = rho := by
    dsimp only [p]
    ring
  have hreg : AnalyticAt ℂ regularizedRiemannZeta rho :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) rho (Set.mem_univ rho)
  have hmne : (analyticOrderAt regularizedRiemannZeta rho).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt regularizedRiemannZeta rho = 0 := by
      rw [(ENat.coe_toNat
        (analyticOrderAt_regularizedRiemannZeta_ne_top rho)).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hreg
    · exact h hzero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hregOrder : analyticOrderAt regularizedRiemannZeta rho = (m + 1 : ℕ) := by
    calc
      analyticOrderAt regularizedRiemannZeta rho =
          ((analyticOrderAt regularizedRiemannZeta rho).toNat : ℕ∞) :=
        (ENat.coe_toNat
          (analyticOrderAt_regularizedRiemannZeta_ne_top rho)).symm
      _ = (m + 1 : ℕ) := by rw [hm, Nat.succ_eq_add_one]
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAn : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hshiftOrder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := regularizedRiemannZeta) hshiftAn hshiftDeriv
  have hRorder : analyticOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        (m + 1 : ℕ) := by
    rw [show shift p = rho by simpa only [shift] using hpρ,
      hregOrder] at hshiftOrder
    change analyticOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        (m + 1 : ℕ) at hshiftOrder
    exact hshiftOrder
  have hpHalf : 1 / 2 < p.re := by
    dsimp only [p]
    norm_num [Complex.add_re]
    linarith
  have hcancelAn : AnalyticAt ℂ W.coPoissonCancelledSource p :=
    (W.differentiableOn_coPoissonCancelledSource_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hRshiftAn : AnalyticAt ℂ
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p :=
    have hregp : AnalyticAt ℂ regularizedRiemannZeta (p - 1 / 2) := by
      rw [hpρ]
      exact hreg
    AnalyticAt.comp (f := fun s : ℂ => s - 1 / 2) (x := p) hregp hshiftAn
  have hRne : ∀ᶠ s in nhdsWithin p ({p}ᶜ),
      regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
    rcases hRshiftAn.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    · exfalso
      have htop := analyticOrderAt_eq_top.mpr hz
      rw [hRorder] at htop
      exact ENat.coe_ne_top _ htop
    · exact hnz
  have hcongr : W.coPoissonCancelledSource =ᶠ[nhdsWithin p ({p}ᶜ)]
      fun s => regularizedRiemannZeta (s - 1 / 2) * W.continuedSource s := by
    filter_upwards [hRne] with s hs
    exact W.coPoissonCancelledSource_eq_mul_continuedSource hs
  have hRmero : MeromorphicAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p :=
    hRshiftAn.meromorphicAt
  have hSmero : MeromorphicAt W.continuedSource p :=
    W.meromorphicOn_continuedSource_rightHalf p hpHalf
  have horderCongr := meromorphicOrderAt_congr hcongr
  have hRmeroOrder : meromorphicOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        ((m + 1 : ℕ) : WithTop ℤ) := by
    rw [hRshiftAn.meromorphicOrderAt_eq, hRorder, ENat.map_coe]
    norm_num
  have hprodOrder : meromorphicOrderAt
      (fun s => regularizedRiemannZeta (s - 1 / 2) * W.continuedSource s) p =
      (m : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_mul hRmero hSmero, hRmeroOrder,
      W.meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
        hrho hzero hMne]
    exact_mod_cast (show ((m + 1 : ℕ) : ℤ) + (-1 : ℤ) = m by omega)
  refine ⟨m, hRorder, ?_⟩
  have hcancelMeroOrder : meromorphicOrderAt W.coPoissonCancelledSource p =
      (m : WithTop ℤ) := by
    rw [horderCongr, hprodOrder]
  rw [hcancelAn.meromorphicOrderAt_eq] at hcancelMeroOrder
  generalize horder : analyticOrderAt W.coPoissonCancelledSource p = o at hcancelMeroOrder ⊢
  induction o using ENat.recTopCoe with
  | top => simp at hcancelMeroOrder
  | coe n =>
      simp only [ENat.map_coe] at hcancelMeroOrder
      have hnm : n = m := by exact_mod_cast hcancelMeroOrder
      simp [hnm]

/-- On every half-plane where the polar-coefficient L-series converges, analytic uniqueness
identifies its shifted-zeta product with the co-Poisson cancelled source. -/
theorem coPoissonCancelledSource_eq_regularized_mul_LSeries
    (W : CompactBVPrimeWindow) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsum : LSeriesSummable W.polarCoefficient (sigma : ℂ)) :
    Set.EqOn W.coPoissonCancelledSource
      (fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries W.polarCoefficient s)
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt sigma).isPreconnected
  have hcancelDiff : DifferentiableOn ℂ W.coPoissonCancelledSource U :=
    W.differentiableOn_coPoissonCancelledSource_rightHalf.mono (by
      intro s hs
      change sigma < s.re at hs
      change 1 / 2 < s.re
      linarith)
  have hLdiff := differentiableOn_LSeries_rightHalf_of_summable hsum
  have hprodDiff : DifferentiableOn ℂ
      (fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries W.polarCoefficient s) U := by
    intro s hs
    have hR : DifferentiableAt ℂ
        (fun z : ℂ => regularizedRiemannZeta (z - 1 / 2)) s :=
      differentiable_regularizedRiemannZeta.differentiableAt.comp s
        (differentiableAt_id.sub_const (1 / 2))
    exact hR.differentiableWithinAt.mul (hLdiff s hs)
  let x0 : ℝ := max sigma (3 / 2) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change sigma < x0
    dsimp only [x0]
    linarith [le_max_left sigma (3 / 2)]
  have hz0far : 3 / 2 < z0.re := by
    change 3 / 2 < x0
    dsimp only [x0]
    linarith [le_max_right sigma (3 / 2)]
  have hfarOpen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hevent : W.coPoissonCancelledSource =ᶠ[nhds z0]
      fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries W.polarCoefficient s := by
    filter_upwards [hfarOpen.mem_nhds hz0far] with s hs
    have ht : s - 1 / 2 ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [Complex.sub_re] at hre
      linarith
    have htRe : 1 < (s - 1 / 2).re := by
      norm_num [Complex.sub_re]
      linarith
    have hR : regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
      rw [regularizedRiemannZeta_of_ne_one ht]
      exact mul_ne_zero (sub_ne_zero.mpr ht)
        (riemannZeta_ne_zero_of_one_lt_re htRe)
    rw [W.coPoissonCancelledSource_eq_mul_continuedSource hR,
      W.LSeries_polarCoefficient_eq_continuedSource hs]
    rfl
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hcancelDiff.analyticOnNhd hUopen) (hprodDiff.analyticOnNhd hUopen)
      hUpre hz0U hevent

/-- An uncensored shifted zero cannot lie strictly inside a half-plane of absolute convergence
of the exact polar-coefficient Dirichlet series. -/
theorem shiftedZero_re_le_of_polarCoefficient_LSeriesSummable
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0)
    (hMne : W.mellinTransform (rho + 1 / 2) ≠ 0)
    {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsum : LSeriesSummable W.polarCoefficient (sigma : ℂ)) :
    (rho + 1 / 2).re ≤ sigma := by
  by_contra hnot
  have hpole : sigma < (rho + 1 / 2).re := lt_of_not_ge hnot
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : rho + 1 / 2 ∈ U := hpole
  have heqOn := W.coPoissonCancelledSource_eq_regularized_mul_LSeries hsigma hsum
  have hevent : W.coPoissonCancelledSource =ᶠ[nhds (rho + 1 / 2)]
      fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries W.polarCoefficient s := by
    filter_upwards [hUopen.mem_nhds hpoleU] with s hs
    exact heqOn hs
  have horders := analyticOrderAt_congr hevent
  have hLdiff := differentiableOn_LSeries_rightHalf_of_summable hsum
  have hLAn : AnalyticAt ℂ (LSeries W.polarCoefficient) (rho + 1 / 2) :=
    (hLdiff.analyticOnNhd hUopen) _ hpoleU
  have hRAn : AnalyticAt ℂ
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
      (rho + 1 / 2) := by
    have hreg : AnalyticAt ℂ regularizedRiemannZeta rho :=
      (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
        isOpen_univ) _ (Set.mem_univ _)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2)
        (rho + 1 / 2) := by fun_prop
    have hregp : AnalyticAt ℂ regularizedRiemannZeta
        (rho + 1 / 2 - 1 / 2) := by
      simpa only [add_sub_cancel_right] using hreg
    exact AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2)
      (x := rho + 1 / 2) hregp hshift
  obtain ⟨m, hRorder, hcancelOrder⟩ :=
    W.analyticOrderAt_coPoissonCancelledSource_eq_pred_of_mellin_ne_zero
      hrho hzero hMne
  have hprod : (m + 1 : ℕ∞) ≤
      analyticOrderAt
        (fun s => regularizedRiemannZeta (s - 1 / 2) *
          LSeries W.polarCoefficient s)
        (rho + 1 / 2) := by
    rw [show (fun s => regularizedRiemannZeta (s - 1 / 2) *
          LSeries W.polarCoefficient s) =
        (fun s => regularizedRiemannZeta (s - 1 / 2)) *
          LSeries W.polarCoefficient by rfl,
      analyticOrderAt_mul hRAn hLAn, hRorder]
    exact le_add_right le_rfl
  rw [hcancelOrder] at horders
  rw [← horders] at hprod
  exact (not_lt_of_ge hprod) (by exact_mod_cast (Nat.lt_succ_self m))

/-- **Ordinary Dirichlet--Hardy exclusion.**  At every completed-zeta zero with positive real
part that is not Mellin-censored by `W`, the exact polar coefficient is not in unweighted
coefficient Hardy space `H₀ = ℓ²(ℕ+)`. -/
theorem not_summable_polarCoefficient_norm_sq_of_uncensored_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0)
    (hMne : W.mellinTransform (rho + 1 / 2) ≠ 0) :
    ¬ Summable (fun n : ℕ+ => ‖W.polarCoefficient n‖ ^ 2) := by
  intro hsquare
  let sigma : ℝ := 1 / 2 + rho.re / 2
  have hsigma : 1 / 2 < sigma := by
    dsimp only [sigma]
    linarith
  have hsum : LSeriesSummable W.polarCoefficient (sigma : ℂ) :=
    LSeriesSummable_of_positive_squareSummable hsquare hsigma
  have hbound := W.shiftedZero_re_le_of_polarCoefficient_LSeriesSummable
    hrho hzero hMne hsigma hsum
  have hpole : sigma < (rho + 1 / 2).re := by
    dsimp only [sigma]
    norm_num [Complex.add_re]
    linarith
  exact (not_lt_of_ge hbound) hpole

/-- The fixed literal dyadic and triadic rational-interval windows jointly exclude ordinary
`H₀`: at every positive-real-part completed-zeta zero, at least one exact polar coefficient is not
square summable.  No window is selected from the zero divisor. -/
theorem dyadic_or_triadic_polarCoefficient_not_squareSummable_at_zero
    {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0) :
    (¬ Summable (fun n : ℕ+ =>
      ‖dyadicSharpInterval.polarCoefficient n‖ ^ 2)) ∨
    (¬ Summable (fun n : ℕ+ =>
      ‖triadicSharpInterval.polarCoefficient n‖ ^ 2)) := by
  rcases mellinTransform_dyadicSharpInterval_or_triadicSharpInterval_ne_zero
      (rho + 1 / 2) with hdyadic | htriadic
  · exact Or.inl
      (dyadicSharpInterval.not_summable_polarCoefficient_norm_sq_of_uncensored_zero
        hrho hzero hdyadic)
  · exact Or.inr
      (triadicSharpInterval.not_summable_polarCoefficient_norm_sq_of_uncensored_zero
        hrho hzero htriadic)

end CompactBVPrimeWindow
end RHTower
