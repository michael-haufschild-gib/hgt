import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Passage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.FullBudgetWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Iteration of true first crossings and first affordable returns from the identity -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
open PrecisionReturns
noncomputable section

abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- First date at or after v where the near-Hilbert budget reaches its robust distance. -/
def crossing {N : ℕ} (H : selfAdjoint (Reg N)) (P : ℕ) (v : ℝ) : ℝ :=
  sInf {t | v≤t ∧ 9/80≤orbitCircuitDistance H P t}

/-- The zeroth low visit is the identity. Each following one is the
earliest low visit after the first intervening robust crossing. -/
def lowDate {N : ℕ} (H : selfAdjoint (Reg N)) (P s : ℕ) : ℕ → ℝ
  | 0 => 0
  | i+1 => firstVisit H (crossing H P (lowDate H P s i)) s (1/10)

def highDate {N : ℕ} (H : selfAdjoint (Reg N)) (P s i : ℕ) := crossing H P (lowDate H P s i)

theorem low_visit {N : ℕ} (H : selfAdjoint (Reg N)) (P s i : ℕ) :
    HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (lowDate H P s i)) := by
  cases i with
  | zero =>
    refine ⟨1,norm_one,TwoQubitCircuit.one N,Nat.zero_le _,?_⟩
    simp [lowDate,TwoQubitCircuit.one_eval,unitaryEvolution]
  | succ i => exact (firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2

theorem low_at_larger_budget {N : ℕ} (H : selfAdjoint (Reg N)) (P s i : ℕ) (hs : s≤P) :
    orbitCircuitDistance H P (lowDate H P s i)≤1/10 := by
  obtain ⟨z,hz,C,hC,he⟩ := low_visit H P s i
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hs,he⟩

/-- Sparse one-unit windows force a hard point after every origin. -/
theorem reaches_after {N : ℕ} (H : selfAdjoint (Reg N)) (P : ℕ) {G : ℝ} (hG : 0≤G)
    (hocc : ∀ a T : ℝ, 0≤T → 2*volume.real (robustWindowHits H P 1∩Icc a (a+T))≤T+G)
    (v : ℝ) : ∃ t∈Icc v (v+(G+1)), 9/80≤orbitCircuitDistance H P t := by
  by_contra! hn
  have hT : 0≤G+1 := by linarith only [hG]
  have hsub : Icc v (v+(G+1)) ⊆ robustWindowHits H P 1 := by
    intro t ht
    exact ⟨t,⟨le_rfl,by linarith⟩,by linarith only [hn t ht]⟩
  have h := hocc v (G+1) hT
  rw [inter_eq_right.mpr hsub,Real.volume_real_Icc_of_le (by linarith only [hG])] at h
  linarith only [h]

/-- Each rising part ends at its attained first crossing, with all
prior distances strictly below the robust level. -/
theorem high_first {N : ℕ} (H : selfAdjoint (Reg N)) (P s : ℕ) (hs : s≤P)
    (hfar : ∀ v : ℝ, ∃ t, v≤t ∧ 9/80≤orbitCircuitDistance H P t) (i : ℕ) :
    let v := lowDate H P s i
    let σ := highDate H P s i
    v<σ ∧ orbitCircuitDistance H P σ=9/80 ∧ IsLeast {u | v≤u ∧ 9/80≤orbitCircuitDistance H P u} σ ∧
      ∀ t∈Ico v σ, orbitCircuitDistance H P t<9/80 := by
  intro v σ
  obtain ⟨t,ht,hhard⟩ := hfar v
  have hlow : orbitCircuitDistance H P v<9/80 :=
    (low_at_larger_budget H P s i hs).trans_lt (by norm_num)
  obtain ⟨u,hu,he,hmin⟩ := first_level (orbitCircuitDistance_lipschitz H P).continuous ht hlow hhard
  have hσ : σ=u := hmin.csInf_eq
  rw [hσ]
  exact ⟨hu.1,he,hmin,fun t ht => lt_of_not_ge fun hh => ht.2.not_ge (hmin.2 ⟨ht.1,hh⟩)⟩

#print axioms high_first
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated

