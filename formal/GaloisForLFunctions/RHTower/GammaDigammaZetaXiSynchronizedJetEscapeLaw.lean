import GaloisForLFunctions.HTGeometry.GammaDigammaJetFreeness
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness
import GaloisForLFunctions.RHTower.XiJetFreeness

/-!
# Synchronized Gamma--digamma--zeta--xi jet escape

Each of Gamma, digamma, zeta, and completed xi has an exact finite-dictionary capacity bound.  A
finite-union pigeonhole argument synchronizes those four separate bounds: one derivative order,
bounded linearly by the dictionary dimension, escapes the dictionary for all four functions at
once.  No joint algebraic-independence premise is required.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- **Synchronized four-source jet escape law.**  Every finite-dimensional dictionary of complex
functions misses the Gamma, digamma, Riemann-zeta, and completed-xi derivatives at one common
order no greater than four times its dimension. -/
theorem exists_synchronized_gamma_digamma_zeta_xi_jet_escape
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ 4 * Module.finrank ℂ V,
      iteratedDeriv n Complex.Gamma ∉ V ∧
      iteratedDeriv n Complex.digamma ∉ V ∧
      iteratedDeriv n riemannZeta ∉ V ∧
      iteratedDeriv n RHTower.xi ∉ V := by
  classical
  let d := Module.finrank ℂ V
  let N := 4 * d + 1
  let sGamma := (Finset.range N).filter fun n => iteratedDeriv n Complex.Gamma ∈ V
  let sDigamma := (Finset.range N).filter fun n => iteratedDeriv n Complex.digamma ∈ V
  let sZeta := (Finset.range N).filter fun n => iteratedDeriv n riemannZeta ∈ V
  let sXi := (Finset.range N).filter fun n => iteratedDeriv n RHTower.xi ∈ V
  have hGamma : sGamma.card ≤ d := by
    apply gamma_iteratedDeriv_mem_finset_card_le_finrank V sGamma
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hDigamma : sDigamma.card ≤ d := by
    apply digamma_iteratedDeriv_mem_finset_card_le_finrank V sDigamma
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hZeta : sZeta.card ≤ d := by
    apply riemannZeta_iteratedDeriv_mem_finset_card_le_finrank V sZeta
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hXi : sXi.card ≤ d := by
    apply RHTower.xi_iteratedDeriv_mem_finset_card_le_finrank V sXi
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  by_contra hnone
  have hall (n : ℕ) (hn : n ≤ 4 * d) :
      iteratedDeriv n Complex.Gamma ∈ V ∨
      iteratedDeriv n Complex.digamma ∈ V ∨
      iteratedDeriv n riemannZeta ∈ V ∨
      iteratedDeriv n RHTower.xi ∈ V := by
    by_contra hmiss
    push Not at hmiss
    exact hnone ⟨n, by simpa only [d] using hn,
      hmiss.1, hmiss.2.1, hmiss.2.2.1, hmiss.2.2.2⟩
  have hcover : Finset.range N ⊆
      sGamma ∪ (sDigamma ∪ (sZeta ∪ sXi)) := by
    intro n hn
    have hnle : n ≤ 4 * d := by
      have hnlt : n < N := Finset.mem_range.mp hn
      dsimp only [N] at hnlt
      omega
    simpa only [Finset.mem_union, Finset.mem_filter, hn, true_and,
      sGamma, sDigamma, sZeta, sXi] using hall n hnle
  have hcardCover : N ≤ (sGamma ∪ (sDigamma ∪ (sZeta ∪ sXi))).card := by
    simpa only [Finset.card_range] using Finset.card_le_card hcover
  have hUnion1 : (sGamma ∪ (sDigamma ∪ (sZeta ∪ sXi))).card ≤
      sGamma.card + (sDigamma ∪ (sZeta ∪ sXi)).card :=
    Finset.card_union_le _ _
  have hUnion2 : (sDigamma ∪ (sZeta ∪ sXi)).card ≤
      sDigamma.card + (sZeta ∪ sXi).card :=
    Finset.card_union_le _ _
  have hUnion3 : (sZeta ∪ sXi).card ≤ sZeta.card + sXi.card :=
    Finset.card_union_le _ _
  dsimp only [N] at hcardCover
  omega

end

end GaloisForLFunctions
