import GaloisForLFunctions.WindowedLandauTheory.TheSlopeChain

/-! Rank-weighted means and maximal slope spread. -/

namespace WindowedLandauTheory.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

abbrev wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ := rankMean d X

def umax {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty X

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

def uF {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxN muN h : ι → ℝ) : ℝ :=
  umax (fun u => muMaxN u - h u) - sF d muN h

def Slopes2 {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muN u = muM u + (Sg0 - dr u) - BE u)

def Slopes2ge {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muM u + (Sg0 - dr u) - BE u ≤ muN u)

def rhsU {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxM muM h dr BE : ι → ℝ) : ℝ :=
  umax (fun u => muMaxM u - h u) - wmean d (fun u => muM u - h u) + wmean d (fun u => dr u + BE u)

def LemmaU (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUge (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

end

end WindowedLandauTheory.LFunctionChainParameters.WeightedMeanLemmas
