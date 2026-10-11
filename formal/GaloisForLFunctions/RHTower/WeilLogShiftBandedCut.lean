import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalIndexTransport

/-! A prefix cut reads exactly its one boundary edge in every matrix of band width one. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

def finiteWeilCutIndicator {n : ℕ} (i : Fin n) (u : Fin (n + 1)) : ℝ :=
  if (u : ℕ) ≤ (i : ℕ) then 1 else 0

theorem finiteWeilCutIndicator_left {n : ℕ} (i : Fin n) :
    finiteWeilCutIndicator i i.castSucc = 1 := by simp [finiteWeilCutIndicator]

theorem finiteWeilCutIndicator_right {n : ℕ} (i : Fin n) :
    finiteWeilCutIndicator i i.succ = 0 := by simp [finiteWeilCutIndicator]

theorem finiteWeil_banded_cut_pairing {n : ℕ} (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hband : ∀ u v : Fin (n + 1), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) → A u v = 0)
    (i : Fin n) :
    (∑ u, ∑ v, A u v * (finiteWeilCutIndicator i u - finiteWeilCutIndicator i v)) =
      A i.castSucc i.succ - A i.succ i.castSucc := by
  have hne : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hpoint (u v : Fin (n + 1)) :
      A u v * (finiteWeilCutIndicator i u - finiteWeilCutIndicator i v) =
        (if u = i.castSucc then if v = i.succ then A u v else 0 else 0) -
          (if u = i.succ then if v = i.castSucc then A u v else 0 else 0) := by
    by_cases hu : (u : ℕ) ≤ (i : ℕ)
    · by_cases hv : (v : ℕ) ≤ (i : ℕ)
      · have hur : u ≠ i.succ := by
          intro he
          rw [he, Fin.val_succ] at hu
          omega
        have hvr : v ≠ i.succ := by
          intro he
          rw [he, Fin.val_succ] at hv
          omega
        simp [finiteWeilCutIndicator, hu, hv, hur, hvr]
      · by_cases he : u = i.castSucc ∧ v = i.succ
        · obtain ⟨rfl, rfl⟩ := he
          simp [finiteWeilCutIndicator, hne]
        · have hfar : (u : ℕ) + 1 < (v : ℕ) := by
            have hn : ¬((u : ℕ) = (i : ℕ) ∧ (v : ℕ) = (i : ℕ) + 1) := by
              intro h
              exact he ⟨Fin.ext h.1, Fin.ext h.2⟩
            omega
          simp [hband u v (Or.inl hfar)]
    · by_cases hv : (v : ℕ) ≤ (i : ℕ)
      · by_cases he : u = i.succ ∧ v = i.castSucc
        · obtain ⟨rfl, rfl⟩ := he
          simp [finiteWeilCutIndicator, hne.symm]
        · have hfar : (v : ℕ) + 1 < (u : ℕ) := by
            have hn : ¬((v : ℕ) = (i : ℕ) ∧ (u : ℕ) = (i : ℕ) + 1) := by
              intro h
              exact he ⟨Fin.ext h.2, Fin.ext h.1⟩
            omega
          simp [hband u v (Or.inr hfar)]
      · have hul : u ≠ i.castSucc := by
          intro he
          rw [he, Fin.val_castSucc] at hu
          exact hu le_rfl
        have hvl : v ≠ i.castSucc := by
          intro he
          rw [he, Fin.val_castSucc] at hv
          exact hv le_rfl
        simp [finiteWeilCutIndicator, hu, hv, hul, hvl]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp

theorem finiteWeilCanonicalProfiles_cut_pairing (r k : ℕ) (i : Fin (r + 1)) :
    (∑ u, (finiteWeilCanonicalPositiveNNProfile r k u : ℝ) * finiteWeilCutIndicator i u) -
      (∑ u, (finiteWeilCanonicalNegativeNNProfile r k u : ℝ) * finiteWeilCutIndicator i u) =
        finiteWeilCanonicalPrefixDifference r k i := by
  change (∑ u, finiteWeilCanonicalPositiveProfile r k u * finiteWeilCutIndicator i u) -
    (∑ u, finiteWeilCanonicalNegativeProfile r k u * finiteWeilCutIndicator i u) = _
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  simp only [finiteWeilCutIndicator, mul_ite, mul_one, mul_zero]
  change (∑ u, if u ≤ i.castSucc then
    finiteWeilCanonicalPositiveProfile r k u - finiteWeilCanonicalNegativeProfile r k u else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext u
    simp
  · intro u hu
    rfl

theorem finiteWeilCanonicalCoupling_cut_flux (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) → gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan i.castSucc i.succ : ℝ) - (gamma.plan i.succ i.castSucc : ℝ) =
      finiteWeilCanonicalPrefixDifference r k i := by
  have hp := finiteWeilCoupling_pairing gamma (finiteWeilCutIndicator i)
  rw [finiteWeilCanonicalProfiles_cut_pairing] at hp
  unfold finiteWeilCouplingCost at hp
  rw [finiteWeil_banded_cut_pairing (fun u v => (gamma.plan u v : ℝ))
    (fun u v h => by rw [hband u v h]; rfl)] at hp
  exact hp.symm

end RHTower
