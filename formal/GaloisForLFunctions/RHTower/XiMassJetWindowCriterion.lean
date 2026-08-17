import GaloisForLFunctions.RHTower.XiMassJetRetreatCriterion

/-!
# The retreated window at every admissible coefficient

The endpoint coefficient `q_{2N} = (N+1/2)/m_B` is the deepest admissible retreat; every shallower
one has a larger cutoff and therefore a smaller exterior.  So for every prescribed coefficient
`0 ≤ Q ≤ q_{2N}` the jet atom sum truncated at `⌊e^{κ_B u − Q log u}⌋` is an exact RH criterion.
Prescribing `Q` first and choosing `N` with `N + 1/2 ≥ m_B Q` therefore produces an RH-equivalent
prime window retreated by `Q log u`.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The window cutoff at retreat coefficient `Q`. -/
def xiMassJetWindowCutoff (a Q u : ℝ) : ℕ :=
  ⌊Real.exp (xiMassSpacelikeSharpSlope a * u - Q * Real.log (max u 1))⌋₊

/-- The jet atom sum truncated at the window cutoff. -/
def xiMassJetWindowSum (a : ℝ) (N : ℕ) (Q σ u : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (xiMassJetWindowCutoff a Q u + 1),
    xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * Complex.I) n

theorem xiMassJetWindowCutoff_le {a : ℝ} (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) :
    xiMassJetWindowCutoff a Q u ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ := by
  refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
  have hlog : 0 ≤ Real.log (max u 1) := Real.log_nonneg (le_max_right u 1)
  nlinarith

/-- **The window cut costs only a uniformly bounded exterior, at every admissible coefficient.** -/
theorem exists_bound_xiMassJetWindowSum_exterior {a c σ : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ)
    (hhalf : 1 / 2 < c) (hca : c < a) (N : ℕ) {Q : ℝ}
    (hQ : Q ≤ xiMassJetRetreatCoeff a (2 * N)) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖(∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
            ((σ : ℂ) + (u : ℂ) * Complex.I) n)
          - xiMassJetWindowSum a N Q σ u‖ ≤ C := by
  obtain ⟨C, u₀, hC, hu₀, hbound⟩ :=
    exists_bound_xiMassJetAtomTail_endpoint (a := a) (sigma := σ) ha hσ (2 * N)
  have hq0 : 0 < xiMassJetRetreatCoeff a (2 * N) := xiMassJetRetreatCoeff_pos ha (2 * N)
  obtain ⟨ua, hua0, hact⟩ := exists_logRetreat_data ha hq0
  refine ⟨C, max u₀ (max ua 1), hC, lt_of_lt_of_le one_pos (by simp), fun u hu => ?_⟩
  have hu0' : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have hua' : ua ≤ u := le_trans (by simp) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by simp) hu
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hmaxu : max u 1 = u := max_eq_left hu1
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  set H : ℝ := xiMassSpacelikeSharpSlope a * u
    - xiMassJetRetreatCoeff a (2 * N) * Real.log u with hHdef
  have hHu : u < H := by
    obtain ⟨hcone, -⟩ := hact u hua'
    have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
    rw [hHdef]
    nlinarith [hcone]
  set M : ℕ := xiMassJetWindowCutoff a Q u with hMdef
  have hMval : M = ⌊Real.exp (xiMassSpacelikeSharpSlope a * u - Q * Real.log u)⌋₊ := by
    rw [hMdef, xiMassJetWindowCutoff, hmaxu]
  have hHle : H ≤ xiMassSpacelikeSharpSlope a * u - Q * Real.log u := by
    rw [hHdef]
    nlinarith [hlog0, hQ]
  have hMH : Real.exp H < ((M : ℕ) : ℝ) + 1 := by
    rw [hMval]
    exact lt_of_le_of_lt (Real.exp_le_exp.2 hHle) (Nat.lt_floor_add_one _)
  have hatom : ∀ p : ℕ, Real.exp H < (p : ℝ) →
      xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((σ : ℂ) + (u : ℂ) * Complex.I) p
        = xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) p := by
    intro p hp
    have hppos : (0 : ℝ) < (p : ℝ) := lt_trans (Real.exp_pos H) hp
    have hlog : H < Real.log p := by
      have h := Real.log_lt_log (Real.exp_pos H) hp
      rwa [Real.log_exp] at h
    have habs : |u| < Real.log p := by
      rw [abs_of_pos hupos]
      linarith
    exact xiMassPolyCenteredPrimeAtom_eq_jetPrimeAtom ha hσ N habs
  have hCfin : ∀ s : Finset ℕ, (∀ p ∈ s, Real.exp H < (p : ℝ)) →
      ∑ p ∈ s, ‖xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) p‖ ≤ C := by
    intro s hs
    exact sum_norm_xiMassJetAtom_finset_le (H := H) (hbound u hu0') s hs
  exact norm_tsum_sub_sum_xiMassPolyCenteredPrimeAtom_le (xiMassJetPoly a N)
    hhalf hca hσ hMH hatom hCfin

/-- **(22.11) The retreated window criterion.**  For every prescribed retreat coefficient
`0 ≤ Q ≤ (N+1/2)/m_B`, RH is equivalent to uniform boundedness on the positive vertical half-line
of the jet atom sum truncated at `⌊e^{κ_B u − Q log u}⌋`. -/
theorem riemannHypothesis_iff_exists_xiMassJetWindowSum_bound {a c : ℝ} (ha : 1 / 2 < a)
    (hhalf : 1 / 2 < c) (hca : c < a) (N : ℕ) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ xiMassJetRetreatCoeff a (2 * N)) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ u : ℝ, 0 ≤ u → ‖xiMassJetWindowSum a N Q σ u‖ ≤ C := by
  constructor
  · intro hRH
    obtain ⟨σ, C₀, hσ, hline⟩ :=
      (riemannHypothesis_iff_exists_xiMassJetAtomSeries_line_bound ha N hhalf hca).mp hRH
    obtain ⟨C₁, u₀, hC₁, hu₀, hret⟩ :=
      exists_bound_xiMassJetWindowSum_exterior (c := c) ha hσ hhalf hca N hQ
    have hV : (0 : ℝ) ≤ xiMassJetVerticalBound a N σ := xiMassJetVerticalBound_nonneg a N σ
    set M₀ : ℕ := ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₀)⌋₊ with hM₀
    refine ⟨σ, max (C₀ + C₁) (7 * (M₀ : ℝ) * xiMassJetVerticalBound a N σ), hσ,
      fun u hu => ?_⟩
    rcases le_or_gt u₀ u with hcase | hcase
    · refine le_trans ?_ (le_max_left _ _)
      have hsplit : xiMassJetWindowSum a N Q σ u
          = (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
              ((σ : ℂ) + (u : ℂ) * Complex.I) n)
            - ((∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
                ((σ : ℂ) + (u : ℂ) * Complex.I) n) - xiMassJetWindowSum a N Q σ u) := by ring
      rw [hsplit]
      exact le_trans (norm_sub_le _ _) (add_le_add (hline u) (hret u hcase))
    · refine le_trans ?_ (le_max_right _ _)
      have hcrude : ‖xiMassJetWindowSum a N Q σ u‖
          ≤ 7 * ((xiMassJetWindowCutoff a Q u : ℕ) : ℝ) * xiMassJetVerticalBound a N σ := by
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum
          (fun n _ => norm_xiMassPolyCenteredPrimeAtom_jet_le ha hσ N n)) ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ hV
        have hpsi : ∑ n ∈ Finset.range (xiMassJetWindowCutoff a Q u + 1),
            (ArithmeticFunction.vonMangoldt n : ℝ) = chebyshevPsi (xiMassJetWindowCutoff a Q u) := by
          rw [sum_range_succ_vonMangoldt_eq_sum_Icc]
          rfl
        rw [hpsi]
        exact chebyshevPsi_le_seven _
      refine le_trans hcrude ?_
      have hmono : xiMassJetWindowCutoff a Q u ≤ M₀ := by
        refine le_trans (xiMassJetWindowCutoff_le Q hQ0 u) ?_
        rw [hM₀]
        refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
        have hκ : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
        nlinarith [hcase.le]
      have hcast : ((xiMassJetWindowCutoff a Q u : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hmono
      nlinarith [hcast, hV]
  · rintro ⟨σ, C, hσ, hbound⟩
    obtain ⟨C₁, u₀, hC₁, hu₀, hret⟩ :=
      exists_bound_xiMassJetWindowSum_exterior (c := c) ha hσ hhalf hca N hQ
    have hτ : ∀ v : ℝ, (0 : ℝ) < ((σ : ℂ) + (v : ℂ) * Complex.I).re := by
      intro v
      simpa [Complex.mul_re] using hσ
    have hfun : ∀ v : ℝ, (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((σ : ℂ) + (v : ℂ) * Complex.I) n)
        = (∫ x : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c
            ((σ : ℂ) + (v : ℂ) * Complex.I) x)
          - (Real.pi : ℂ) * (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
            ((σ : ℂ) + (v : ℂ) * Complex.I) := by
      intro v
      rw [← integral_xiMassPolyBottomPrimeIntegrand_eq_tsum_centeredAtom
        (xiMassJetPoly a N) hhalf hca (hτ v)]
      exact integral_xiMassJetBottomPrimeIntegrand_eq ha N hhalf hca (hτ v)
    have htrace : Continuous (fun v : ℝ =>
        (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
          ((σ : ℂ) + (v : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro v
      have hlin : ContinuousAt (fun w : ℝ => ((σ : ℂ) + (w : ℂ) * Complex.I)) v := by fun_prop
      have hd : DifferentiableAt ℂ
          ((xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N))
          ((σ : ℂ) + (v : ℂ) * Complex.I) :=
        (xiMassFamily ha.le).differentiableAt_traceWC _ (hτ v)
      exact ContinuousAt.comp (g := (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N))
        (f := fun w : ℝ => ((σ : ℂ) + (w : ℂ) * Complex.I)) (x := v) hd.continuousAt hlin
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := u₀)).exists_bound_of_continuousOn
      htrace.continuousOn
    have harch : ∀ v : ℝ, ‖∫ x : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c
          ((σ : ℂ) + (v : ℂ) * Complex.I) x‖
        ≤ xiMassPolyBottomArchUniformBound (xiMassJetPoly a N) a σ :=
      fun v => norm_integral_xiMassPolyBottomArchIntegrand_le_uniform (xiMassJetPoly a N)
        hhalf hca hσ
    set D : ℝ := max (C + C₁)
      (xiMassPolyBottomArchUniformBound (xiMassJetPoly a N) a σ + Real.pi * B) with hD
    have hkey : ∀ v : ℝ, 0 ≤ v →
        ‖∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((σ : ℂ) + (v : ℂ) * Complex.I) n‖ ≤ D := by
      intro v hv
      rcases le_or_gt u₀ v with hc | hc
      · refine le_trans ?_ (le_max_left _ _)
        have hsplit : (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
              ((σ : ℂ) + (v : ℂ) * Complex.I) n)
            = xiMassJetWindowSum a N Q σ v
              + ((∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
                  ((σ : ℂ) + (v : ℂ) * Complex.I) n) - xiMassJetWindowSum a N Q σ v) := by
          ring
        rw [hsplit]
        exact le_trans (norm_add_le _ _) (add_le_add (hbound v hv) (hret v hc))
      · refine le_trans ?_ (le_max_right _ _)
        rw [hfun v]
        refine le_trans (norm_sub_le _ _) (add_le_add (harch v) ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        exact mul_le_mul_of_nonneg_left (hB v ⟨hv, hc.le⟩) Real.pi_pos.le
    refine (riemannHypothesis_iff_exists_xiMassJetAtomSeries_line_bound ha N hhalf hca).mpr
      ⟨σ, D, hσ, fun x => ?_⟩
    rcases le_or_gt 0 x with hx | hx
    · exact hkey x hx
    · have hsym := norm_tsum_xiMassPolyCenteredPrimeAtom_jet_neg (a := a) ha
        (sigma := σ) (u := -x) N
      have hcast : ((-(-x) : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by push_cast; ring
      rw [hcast] at hsym
      rw [hsym]
      exact hkey (-x) (by linarith)

end

end RHTower
