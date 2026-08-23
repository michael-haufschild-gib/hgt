import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalJetExact

/-!
# Hasse detection and realization for arithmetic Xi jets

The complete family of multiplicity-bounded Xi jets detects compact-open middle cohomology and is
globally realizable.  Before quotienting, equality of all local jets is exactly congruence modulo
the global Xi-divisible range.
-/

namespace RHTower

noncomputable section

/-- Two compact-open entire sources have identical local Xi jets exactly when their difference is
globally Xi-divisible. -/
theorem deningerCompactOpenEntire_congr_mod_xi_hasse_iff
    (F G : DeningerCompactOpenEntire) :
    (∀ (rho : XiDivisorSupport) (k : DeningerArithmeticJetIndex rho),
      deningerCompactOpenAllJets F rho k = deningerCompactOpenAllJets G rho k) ↔
      F - G ∈ deningerCompactOpenXiRange := by
  constructor
  · intro h
    apply (deningerCompactOpenXi_allJets_exact (F - G)).mp
    funext rho k
    change deningerCompactOpenAllJets (F - G) rho k = (0 : ℂ)
    have hsub := congrFun
      (congrFun (map_sub deningerCompactOpenAllJets F G) rho) k
    rw [hsub]
    exact sub_eq_zero.mpr (h rho k)
  · intro h rho k
    have hz := (deningerCompactOpenXi_allJets_exact (F - G)).mpr h
    have hcoord := congrFun (congrFun hz rho) k
    change deningerCompactOpenAllJets (F - G) rho k = (0 : ℂ) at hcoord
    have hsub := congrFun
      (congrFun (map_sub deningerCompactOpenAllJets F G) rho) k
    rw [hsub] at hcoord
    exact sub_eq_zero.mp hcoord

/-- Two compact-open middle-cohomology classes agree exactly when every local Xi jet agrees. -/
theorem deningerCompactOpenH1AllJets_congr_hasse_iff
    (x y : DeningerArithmeticCompactOpenH1) :
    (∀ (rho : XiDivisorSupport) (k : DeningerArithmeticJetIndex rho),
      deningerCompactOpenH1AllJets x rho k = deningerCompactOpenH1AllJets y rho k) ↔
      x = y := by
  constructor
  · intro h
    apply deningerCompactOpenH1AllJets_injective
    funext rho k
    exact h rho k
  · rintro rfl rho k
    rfl

/-- Every complete family of multiplicity-bounded local Xi jets has one unique global compact-open
middle-cohomology realization. -/
theorem deningerCompactOpenH1AllJets_existsUnique_hasse
    (a : DeningerArithmeticJetProduct) :
    ∃! x : DeningerArithmeticCompactOpenH1,
      ∀ (rho : XiDivisorSupport) (k : DeningerArithmeticJetIndex rho),
        deningerCompactOpenH1AllJets x rho k = a rho k := by
  obtain ⟨x, hx⟩ := deningerCompactOpenH1AllJets_surjective a
  refine ⟨x, fun rho k => congrFun (congrFun hx rho) k, ?_⟩
  intro y hy
  apply deningerCompactOpenH1AllJets_injective
  funext rho k
  exact (hy rho k).trans (congrFun (congrFun hx rho) k).symm

end


end RHTower
