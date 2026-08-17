import GaloisForLFunctions.RHTower.XiMassJetAtomTail
import GaloisForLFunctions.RHTower.XiMassJetAtomSeriesCriterion

/-!
# Truncating the jet atom series

The exterior bound holds for every finite set of exterior indices, hence for the whole exterior sum.
Cutting the atom series at an integer cutoff above the retreat therefore changes it by a uniformly
bounded amount — the card's "only a uniformly bounded exterior".
-/

open Complex Filter Finset MeasureTheory

namespace RHTower

noncomputable section

/-- Any finite set of exterior indices obeys the exterior bound. -/
theorem sum_norm_xiMassJetAtom_finset_le {a sigma u H C : ℝ} {k : ℕ}
    (hC : ∀ M : ℕ, ∑ p ∈ (Finset.Icc 1 M).filter (fun p : ℕ => Real.exp H < (p : ℝ)),
        ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k p‖ ≤ C)
    (s : Finset ℕ) (hs : ∀ n ∈ s, Real.exp H < (n : ℝ)) :
    ∑ n ∈ s, ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖ ≤ C := by
  classical
  set M : ℕ := s.sup id with hM
  have hsub : s ⊆ (Finset.Icc 1 M).filter (fun p : ℕ => Real.exp H < (p : ℝ)) := by
    intro n hn
    have hgt := hs n hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exfalso
        have hexp : (0 : ℝ) < Real.exp H := Real.exp_pos H
        norm_num at hgt
        linarith
      · exact hpos
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, ?_⟩, hgt⟩
    exact Finset.le_sup (f := id) hn
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)) (hC M)

/-- The filtered centred prime atoms are absolutely summable. -/
theorem summable_norm_xiMassPolyCenteredPrimeAtom (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun n : ℕ => ‖xiMassPolyCenteredPrimeAtom P a τ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_integral_norm_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca hτ)
  rw [← integral_xiMassPolyBottomPrimeAtom_eq_centered P hhalf hca hτ n]
  exact norm_integral_le_integral_norm _

/-- **Cutting the atom series at an exterior cutoff costs a uniformly bounded amount.** -/
theorem norm_tsum_sub_sum_xiMassPolyCenteredPrimeAtom_le (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {σ u : ℝ} (hσ : 0 < σ) {H C : ℝ} {M k : ℕ}
    (hMH : Real.exp H < (M : ℝ) + 1)
    (hatom : ∀ n : ℕ, Real.exp H < (n : ℝ) →
      xiMassPolyCenteredPrimeAtom P a ((σ : ℂ) + (u : ℂ) * Complex.I) n
        = xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) k n)
    (hC : ∀ s : Finset ℕ, (∀ n ∈ s, Real.exp H < (n : ℝ)) →
      ∑ n ∈ s, ‖xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) k n‖ ≤ C) :
    ‖(∑' n : ℕ, xiMassPolyCenteredPrimeAtom P a ((σ : ℂ) + (u : ℂ) * Complex.I) n)
        - ∑ n ∈ Finset.range (M + 1),
            xiMassPolyCenteredPrimeAtom P a ((σ : ℂ) + (u : ℂ) * Complex.I) n‖ ≤ C := by
  classical
  set τ : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I with hτdef
  have hτre : (0 : ℝ) < τ.re := by rw [hτdef]; simpa [Complex.mul_re] using hσ
  have hnormsum : Summable (fun n : ℕ => ‖xiMassPolyCenteredPrimeAtom P a τ n‖) :=
    summable_norm_xiMassPolyCenteredPrimeAtom P hhalf hca hτre
  have hsum : Summable (fun n : ℕ => xiMassPolyCenteredPrimeAtom P a τ n) :=
    hnormsum.of_norm
  have hsplit := hsum.sum_add_tsum_compl (s := Finset.range (M + 1))
  have hdiff : (∑' n : ℕ, xiMassPolyCenteredPrimeAtom P a τ n)
      - ∑ n ∈ Finset.range (M + 1), xiMassPolyCenteredPrimeAtom P a τ n
      = ∑' n : ↥(((Finset.range (M + 1) : Finset ℕ) : Set ℕ)ᶜ),
          xiMassPolyCenteredPrimeAtom P a τ (n : ℕ) := by
    rw [← hsplit]
    ring
  have hexterior : ∀ n : ↥(((Finset.range (M + 1) : Finset ℕ) : Set ℕ)ᶜ),
      Real.exp H < ((n : ℕ) : ℝ) := by
    intro n
    have hn : (n : ℕ) ∉ Finset.range (M + 1) := by
      have := n.2
      simpa only [Set.mem_compl_iff, Finset.mem_coe] using this
    have hlt : M + 1 ≤ (n : ℕ) := by
      rw [Finset.mem_range] at hn
      omega
    have hcast : ((M : ℝ) + 1) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  have hnormcompl : Summable
      (fun n : ↥(((Finset.range (M + 1) : Finset ℕ) : Set ℕ)ᶜ) =>
        ‖xiMassPolyCenteredPrimeAtom P a τ (n : ℕ)‖) := hnormsum.subtype _
  have hbound : ∑' n : ↥(((Finset.range (M + 1) : Finset ℕ) : Set ℕ)ᶜ),
      ‖xiMassPolyCenteredPrimeAtom P a τ (n : ℕ)‖ ≤ C := by
    refine Summable.tsum_le_of_sum_le hnormcompl fun t => ?_
    have hmap : ∑ n ∈ t, ‖xiMassPolyCenteredPrimeAtom P a τ (n : ℕ)‖
        = ∑ n ∈ Finset.image Subtype.val t, ‖xiMassJetPrimeAtom a τ k n‖ := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.ext hxy)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hatom (n : ℕ) (hexterior n)]
    rw [hmap]
    refine hC _ fun n hn => ?_
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hn
    rw [← hm]
    exact hexterior m
  rw [hdiff]
  exact le_trans (norm_tsum_le_tsum_norm hnormcompl) hbound

end

end RHTower
