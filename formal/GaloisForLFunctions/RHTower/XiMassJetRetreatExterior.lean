import GaloisForLFunctions.RHTower.XiMassJetAtomTruncation

/-!
# The retreated cutoff has a uniformly bounded exterior

At the endpoint coefficient `q_{2N} = (N+1/2)/m_B` the whole exterior of the jet atom series past
`κ_B u − q_{2N} log u` is bounded by a constant, uniformly in the height.  Cutting the criterion's
atom series at that retreated integer cutoff therefore changes it by a uniformly bounded amount:
the modified exact core may be cut there with only a uniformly bounded exterior.
-/

open Complex Filter Finset MeasureTheory

namespace RHTower

noncomputable section

/-- The retreated integer cutoff of the jet hierarchy at order `N`. -/
def xiMassJetRetreatCutoff (a : ℝ) (N : ℕ) (u : ℝ) : ℕ :=
  ⌊Real.exp (xiMassSpacelikeSharpSlope a * u
    - xiMassJetRetreatCoeff a (2 * N) * Real.log u)⌋₊

/-- **(22.11) The retreated cut costs only a uniformly bounded exterior.** -/
theorem exists_bound_xiMassJetAtomSeries_retreat {a c σ : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ)
    (hhalf : 1 / 2 < c) (hca : c < a) (N : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖(∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
            ((σ : ℂ) + (u : ℂ) * Complex.I) n)
          - ∑ n ∈ Finset.range (xiMassJetRetreatCutoff a N u + 1),
              xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
                ((σ : ℂ) + (u : ℂ) * Complex.I) n‖ ≤ C := by
  obtain ⟨C, u₀, hC, hu₀, hbound⟩ :=
    exists_bound_xiMassJetAtomTail_endpoint (a := a) (sigma := σ) ha hσ (2 * N)
  have hq0 : 0 < xiMassJetRetreatCoeff a (2 * N) := xiMassJetRetreatCoeff_pos ha (2 * N)
  obtain ⟨ua, hua0, hact⟩ := exists_logRetreat_data ha hq0
  refine ⟨C, max u₀ (max ua 1), hC,
    lt_of_lt_of_le one_pos (by simp), fun u hu => ?_⟩
  have hu0' : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have hua' : ua ≤ u := le_trans (by simp) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by simp) hu
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  set H : ℝ := xiMassSpacelikeSharpSlope a * u
    - xiMassJetRetreatCoeff a (2 * N) * Real.log u with hHdef
  have hHu : u < H := by
    obtain ⟨hcone, -⟩ := hact u hua'
    have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
    rw [hHdef]
    nlinarith [hcone]
  have hcut : xiMassJetRetreatCutoff a N u = ⌊Real.exp H⌋₊ := by
    rw [xiMassJetRetreatCutoff, hHdef]
  have hMH : Real.exp H < ((⌊Real.exp H⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hatom : ∀ n : ℕ, Real.exp H < (n : ℝ) →
      xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((σ : ℂ) + (u : ℂ) * Complex.I) n
        = xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos H) hn
    have hlog : H < Real.log n := by
      have h := Real.log_lt_log (Real.exp_pos H) hn
      rwa [Real.log_exp] at h
    have habs : |u| < Real.log n := by
      rw [abs_of_pos hupos]
      linarith
    exact xiMassPolyCenteredPrimeAtom_eq_jetPrimeAtom ha hσ N habs
  have hCfin : ∀ s : Finset ℕ, (∀ n ∈ s, Real.exp H < (n : ℝ)) →
      ∑ n ∈ s, ‖xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) n‖ ≤ C := by
    intro s hs
    exact sum_norm_xiMassJetAtom_finset_le (H := H) (hbound u hu0') s hs
  rw [hcut]
  exact norm_tsum_sub_sum_xiMassPolyCenteredPrimeAtom_le (xiMassJetPoly a N)
    hhalf hca hσ hMH hatom hCfin

end

end RHTower
