import GaloisForLFunctions.RHTower.XiMassJetRetreatExterior
import GaloisForLFunctions.RHTower.XiMassJetAtomSymmetry
import GaloisForLFunctions.RHTower.XiMassJetPrimeLineCriterion
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The retreated jet criterion

Cutting the jet atom series at the retreated integer cutoff `⌊e^{κ_B u − q_{2N} log u}⌋` changes it
by a uniformly bounded amount, and below the initial interval the truncated sum is a finite sum of
uniformly bounded atoms.  So the Riemann hypothesis is equivalent to uniform boundedness of the
truncated sum on the positive vertical half-line — the retreated prime-discrepancy window of the
caustic-null jet hierarchy.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The jet atom sum truncated at the retreated cutoff. -/
def xiMassJetRetreatSum (a : ℝ) (N : ℕ) (σ u : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (xiMassJetRetreatCutoff a N u + 1),
    xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * Complex.I) n

theorem norm_xiMassPolyCenteredPrimeAtom_jet_le {a σ u : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ)
    (N : ℕ) (n : ℕ) :
    ‖xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * Complex.I) n‖
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * xiMassJetVerticalBound a N σ := by
  have htest : xiMassPolyAnalyticTest (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * Complex.I)
      = xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * Complex.I) := by
    funext z
    exact (xiMassJetAnalyticTest_eq_poly ha N _ z).symm
  have hV : (0 : ℝ) ≤ xiMassJetVerticalBound a N σ := xiMassJetVerticalBound_nonneg a N σ
  rcases eq_or_ne n 0 with rfl | hn
  · rw [xiMassPolyCenteredPrimeAtom, LSeries.term_zero, zero_mul, norm_zero]
    positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have hpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hvm : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    rw [xiMassPolyCenteredPrimeAtom, htest, norm_mul, norm_lseriesTerm_vonMangoldt_nat hn]
    have hF := norm_stripFourier_xiMassJetAnalyticTest_vertical_le ha hσ N u (Real.log n)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
          * ‖stripFourier (xiMassJetAnalyticTest a N ((σ : ℂ) + (u : ℂ) * Complex.I))
              ((Real.log n : ℝ) : ℂ)‖
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * xiMassJetVerticalBound a N σ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hvm) hF (norm_nonneg _) ?_
          positivity
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) * xiMassJetVerticalBound a N σ := by ring

/-- **The crude bound on the truncated sum.**  Every truncated atom sum is at most the Chebyshev
mass of its cutoff times the uniform vertical bound. -/
theorem norm_xiMassJetRetreatSum_le_crude {a σ u : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ) (N : ℕ) :
    ‖xiMassJetRetreatSum a N σ u‖
      ≤ 7 * ((xiMassJetRetreatCutoff a N u : ℕ) : ℝ) * xiMassJetVerticalBound a N σ := by
  have hV : (0 : ℝ) ≤ xiMassJetVerticalBound a N σ := xiMassJetVerticalBound_nonneg a N σ
  set M : ℕ := xiMassJetRetreatCutoff a N u with hM
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (fun n _ => norm_xiMassPolyCenteredPrimeAtom_jet_le ha hσ N n)) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hV
  have hpsi : ∑ n ∈ Finset.range (M + 1), (ArithmeticFunction.vonMangoldt n : ℝ)
      = chebyshevPsi M := by
    rw [sum_range_succ_vonMangoldt_eq_sum_Icc]
    rfl
  rw [hpsi]
  exact chebyshevPsi_le_seven M

/-- **(22.11) The retreated jet criterion.**  RH is equivalent to uniform boundedness, on the
positive vertical half-line, of the jet atom sum truncated at the retreated cutoff. -/
theorem riemannHypothesis_iff_exists_xiMassJetRetreatSum_bound {a c : ℝ} (ha : 1 / 2 < a)
    (hhalf : 1 / 2 < c) (hca : c < a) (N : ℕ) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ u : ℝ, 0 ≤ u → ‖xiMassJetRetreatSum a N σ u‖ ≤ C := by
  constructor
  · intro hRH
    obtain ⟨σ, C₀, hσ, hline⟩ :=
      (riemannHypothesis_iff_exists_xiMassJetAtomSeries_line_bound ha N hhalf hca).mp hRH
    obtain ⟨C₁, u₀, hC₁, hu₀, hret⟩ :=
      exists_bound_xiMassJetAtomSeries_retreat (c := c) ha hσ hhalf hca N
    have hV : (0 : ℝ) ≤ xiMassJetVerticalBound a N σ := xiMassJetVerticalBound_nonneg a N σ
    set M₀ : ℕ := ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₀)⌋₊ with hM₀
    refine ⟨σ, max (C₀ + C₁) (7 * (M₀ : ℝ) * xiMassJetVerticalBound a N σ), hσ,
      fun u hu => ?_⟩
    rcases le_or_gt u₀ u with hcase | hcase
    · refine le_trans ?_ (le_max_left _ _)
      have hsplit : xiMassJetRetreatSum a N σ u
          = (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
              ((σ : ℂ) + (u : ℂ) * Complex.I) n)
            - ((∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
                ((σ : ℂ) + (u : ℂ) * Complex.I) n)
              - xiMassJetRetreatSum a N σ u) := by ring
      rw [hsplit]
      exact le_trans (norm_sub_le _ _) (add_le_add (hline u) (hret u hcase))
    · refine le_trans (norm_xiMassJetRetreatSum_le_crude ha hσ N) ?_
      refine le_trans ?_ (le_max_right _ _)
      have hmono : xiMassJetRetreatCutoff a N u ≤ M₀ := by
        refine le_trans (xiMassJetRetreatCutoff_le ha N u) ?_
        rw [hM₀]
        refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
        have hκ : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
        nlinarith [hcase.le]
      have hcast : ((xiMassJetRetreatCutoff a N u : ℕ) : ℝ) ≤ (M₀ : ℝ) := by
        exact_mod_cast hmono
      have h7 : (0 : ℝ) ≤ 7 := by norm_num
      nlinarith [hcast, hV]
  · rintro ⟨σ, C, hσ, hbound⟩
    obtain ⟨C₁, u₀, hC₁, hu₀, hret⟩ :=
      exists_bound_xiMassJetAtomSeries_retreat (c := c) ha hσ hhalf hca N
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
            = xiMassJetRetreatSum a N σ v
              + ((∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
                  ((σ : ℂ) + (v : ℂ) * Complex.I) n) - xiMassJetRetreatSum a N σ v) := by
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
