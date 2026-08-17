import GaloisForLFunctions.RHTower.XiZeroCountingFunction
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic
import GaloisForLFunctions.RHTower.WindingXiCircle
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles

/-!
# The rectangle argument principle for `ξ`

The logarithmic derivative of `ξ` has a simple pole of residue equal to the vanishing order at every
`ξ`-zero and is analytic elsewhere, so the rectangle residue theorem turns its normalized boundary
integral into the total `ξ`-divisor mass of the rectangle:

`(1/2πi) ∮_{∂R} ξ'/ξ = Σ_{ρ ∈ R} ord_ρ ξ`.

The only hypothesis is that the boundary avoids the divisor, which is what a height chosen off the
ordinate set provides.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The local structure of `ξ'/ξ` -/

theorem meromorphicOrderAt_logDeriv_xi_nonneg_of_ne_zero {ρ : ℂ} (hne : xi ρ ≠ 0) :
    (0 : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv xi) ρ := by
  have hxi : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have hquot : AnalyticAt ℂ (fun z => deriv xi z / xi z) ρ := hxi.deriv.div hxi hne
  have heq : logDeriv xi = fun z => deriv xi z / xi z := by
    funext z
    rw [logDeriv_apply]
  rw [heq]
  exact hquot.meromorphicOrderAt_nonneg

theorem hasSimplePolesOn_logDeriv_xi (S : Set ℂ) : HasSimplePolesOn (logDeriv xi) S := by
  intro ρ _
  by_cases h : xi ρ = 0
  · rw [meromorphicOrderAt_logDeriv_xi_eq_neg_one h]
  · exact le_trans (by exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega))
      (meromorphicOrderAt_logDeriv_xi_nonneg_of_ne_zero h)

/-- The poles of `ξ'/ξ` are exactly the zeros of `ξ`. -/
theorem logDeriv_xi_pole_iff (ρ : ℂ) :
    meromorphicOrderAt (logDeriv xi) ρ < 0 ↔ xi ρ = 0 := by
  constructor
  · intro h
    by_contra hne
    exact absurd (meromorphicOrderAt_logDeriv_xi_nonneg_of_ne_zero hne) (not_le.mpr h)
  · intro h
    rw [meromorphicOrderAt_logDeriv_xi_eq_neg_one h]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)

/-- The residue of `ξ'/ξ` at a zero is the vanishing order. -/
theorem residue_logDeriv_xi (ρ : ℂ) :
    residue (logDeriv xi) ρ = (((analyticOrderAt xi ρ).toNat : ℤ) : ℂ) := by
  have hxi : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have horder : meromorphicOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℤ)) := by
    rw [hxi.meromorphicOrderAt_eq, ← ENat.coe_toNat (xi_orderAt_ne_top ρ)]
    rfl
  exact residue_eq_of_tendsto
    (logDeriv_residue_of_meromorphicOrder hxi.meromorphicAt horder)

/-! ## Finiteness -/

theorem xi_zeros_rectangle_finite (z w : ℂ) :
    (Rectangle z w ∩ {u : ℂ | meromorphicOrderAt (logDeriv xi) u < 0}).Finite := by
  have hcpt : IsCompact (Rectangle z w) :=
    ((isCompact_uIcc).reProdIm (isCompact_uIcc))
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : ℂ)
  refine (xi_zeros_closedBall_finite 0 R).subset ?_
  intro u hu
  refine ⟨hR hu.1, ?_⟩
  exact (logDeriv_xi_pole_iff u).mp hu.2

/-! ## The argument principle -/

/-- **The rectangle argument principle for `ξ`.**  If the boundary avoids the divisor, the
normalized boundary integral of `ξ'/ξ` is the total divisor mass of the rectangle. -/
theorem rectangleIntegral_logDeriv_xi {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, xi s ≠ 0) :
    RectangleIntegral' (logDeriv xi) z w
      = ∑ u ∈ (xi_zeros_rectangle_finite z w).toFinset,
          (((analyticOrderAt xi u).toNat : ℤ) : ℂ) := by
  classical
  have hmero : MeromorphicOn (logDeriv xi) (Rectangle z w) :=
    fun u _ => meromorphicAt_logDeriv_xi u
  have hdisj : Disjoint (RectangleBorder z w)
      {u : ℂ | meromorphicOrderAt (logDeriv xi) u < 0} := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact hborder u hu ((logDeriv_xi_pole_iff u).mp hu')
  have hres := RectangleIntegral'_eq_sumResiduesIn hre him hmero hdisj
    (xi_zeros_rectangle_finite z w) (hasSimplePolesOn_logDeriv_xi _)
  rw [hres, sumResiduesIn]
  set hfin := xi_zeros_rectangle_finite z w with hfindef
  haveI : Fintype ↥(Rectangle z w ∩ {u : ℂ | meromorphicOrderAt (logDeriv xi) u < 0}) :=
    hfin.fintype
  rw [tsum_fintype]
  have hbij : ∑ p : ↥(Rectangle z w ∩ {u : ℂ | meromorphicOrderAt (logDeriv xi) u < 0}),
      residue (logDeriv xi) (p : ℂ)
      = ∑ u ∈ hfin.toFinset, residue (logDeriv xi) u := by
    rw [← Finset.sum_coe_sort hfin.toFinset (fun u => residue (logDeriv xi) u)]
    exact Fintype.sum_equiv (Equiv.setCongr hfin.coe_toFinset.symm) _ _ fun p => rfl
  rw [hbij]
  exact Finset.sum_congr rfl fun u _ => residue_logDeriv_xi u

/-- **The rectangle argument principle in divisor-mass form.** -/
theorem rectangleIntegral_logDeriv_xi_eq_regionOrderSum {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hborder : ∀ s ∈ RectangleBorder z w, xi s ≠ 0) :
    RectangleIntegral' (logDeriv xi) z w
      = ((xiRegionOrderSum (Rectangle z w) : ℤ) : ℂ) := by
  classical
  rw [rectangleIntegral_logDeriv_xi hre him hborder, xiRegionOrderSum]
  set hfin := xi_zeros_rectangle_finite z w with hfindef
  have hsupp : Function.support (fun u => (MeromorphicOn.divisor xi (Rectangle z w) u : ℤ))
      ⊆ (hfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have humem : u ∈ Rectangle z w := by
      by_contra hmem
      exact hu (xi_divisor_apply_of_notMem hmem)
    have hzero : xi u = 0 := by
      by_contra hne
      refine hu ?_
      rw [xi_divisor_apply_of_mem humem]
      have hord : analyticOrderAt xi u = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hne)
      rw [hord]
      rfl
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨humem, (logDeriv_xi_pole_iff u).mpr hzero⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  push_cast
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Set.Finite.mem_toFinset] at hu
  rw [xi_divisor_apply_of_mem hu.1]
  push_cast
  ring

end RHTower
