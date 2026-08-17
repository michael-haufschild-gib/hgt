import GaloisForLFunctions.RHTower.XiMassJetLogSubcausticWindow
import GaloisForLFunctions.RHTower.XiMassJetWindowCriterion

/-!
# The logarithmically corrected subcaustic criterion for the jet receiver

Cutting the jet atom cone at the logarithmically corrected subcaustic height

`H(u) = κ_B u − L u^{1/10} − q log u`

and replacing the removed primes by their continuum density changes the caustic sum by a uniformly
bounded amount, because the prime-discrepancy annulus of the jet receiver is bounded in the whole
chamber `m_B q ≤ N + 1/2`.  Hence the Riemann hypothesis is equivalent to uniform boundedness of
the resulting quadrature, which is the jet form of `(22.9)`.

The jet gain `u^{-(N+1/2)}` of the transport prefactor is exactly what widens the admissible
logarithmic chamber from `m_B q ≤ 1/2` to `m_B q ≤ N + 1/2`.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- **The jet quadrature at the logarithmically corrected subcaustic height.**  The caustic atom
sum with the primes of the retreated annulus replaced by their continuum density. -/
def xiMassJetSubcausticQuadrature (a : ℝ) (N : ℕ) (L q σ u : ℝ) : ℂ :=
  xiMassJetWindowSum a N 0 σ u
    - ((∑ p ∈ primeLogWindow (xiMassLogSubcausticHeight a L q u)
            (xiMassSpacelikeSharpSlope a * u),
          xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) p)
      - ∫ h in (xiMassLogSubcausticHeight a L q u)..(xiMassSpacelikeSharpSlope a * u),
          ((Real.exp (h / 2) : ℝ) : ℂ) *
            xiMassJetIterate a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) ((h : ℝ) : ℂ))

set_option maxHeartbeats 1000000 in
/-- **(22.9) The logarithmically corrected subcaustic RH criterion at jet order `N`.**  There is a
positive coefficient chamber inside which, for every logarithmic coefficient with
`m_B q ≤ N + 1/2`, RH is equivalent to uniform boundedness of the jet quadrature at the retreated
height `κ_B u − L u^{1/10} − q log u`. -/
theorem exists_riemannHypothesis_iff_jetSubcausticQuadratureBound {a c : ℝ}
    (ha : 1 / 2 < a) (hhalf : 1 / 2 < c) (hca : c < a) (N : ℕ) :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ L q : ℝ, 0 < L → L ≤ Lc → 0 ≤ q →
      (2 * a ^ 2 - 1 / 2) * q ≤ (N : ℝ) + 1 / 2 →
      (RiemannHypothesis ↔ ∃ σ C : ℝ, 0 < σ ∧
        ∀ᶠ u : ℝ in atTop, ‖xiMassJetSubcausticQuadrature a N L q σ u‖ ≤ C) := by
  obtain ⟨Lc, hLc0, hLc⟩ := exists_eventually_norm_jetLogSubcausticWindowDefect_le ha (2 * N)
  have hQ0 : (0 : ℝ) ≤ 0 := le_rfl
  have hQle : (0 : ℝ) ≤ xiMassJetRetreatCoeff a (2 * N) := (xiMassJetRetreatCoeff_pos ha (2 * N)).le
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  refine ⟨Lc, hLc0, fun L q hL hLle hq hqcap => ?_⟩
  have hqcap' : (2 * a ^ 2 - 1 / 2) * q ≤ (((2 * N : ℕ) : ℝ) + 1) / 2 := by
    push_cast
    linarith
  constructor
  · intro hRH
    obtain ⟨σ, C, hσ, hbound⟩ :=
      (riemannHypothesis_iff_exists_xiMassJetWindowSum_bound ha hhalf hca N hQ0 hQle).mp hRH
    obtain ⟨Cw, hCw⟩ := hLc σ hσ L q hL hLle hq hqcap'
    refine ⟨σ, C + Cw, hσ, ?_⟩
    filter_upwards [hCw, eventually_ge_atTop (0 : ℝ)] with u hu hu0
    obtain ⟨-, hD⟩ := hu
    exact (norm_sub_le _ _).trans (add_le_add (hbound u hu0) hD)
  · rintro ⟨σ, C, hσ, hbnd⟩
    obtain ⟨Cw, hCw⟩ := hLc σ hσ L q hL hLle hq hqcap'
    have hV : (0 : ℝ) ≤ xiMassJetVerticalBound a N σ := xiMassJetVerticalBound_nonneg a N σ
    have hcomb : ∀ᶠ u : ℝ in atTop,
        ‖xiMassJetWindowSum a N 0 σ u‖ ≤ C + Cw := by
      filter_upwards [hbnd, hCw] with u hq1 hq2
      obtain ⟨-, hD⟩ := hq2
      have hsplit : xiMassJetWindowSum a N 0 σ u
          = xiMassJetSubcausticQuadrature a N L q σ u
            + ((∑ p ∈ primeLogWindow (xiMassLogSubcausticHeight a L q u)
                  (xiMassSpacelikeSharpSlope a * u),
                xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N) p)
              - ∫ h in (xiMassLogSubcausticHeight a L q u)..(xiMassSpacelikeSharpSlope a * u),
                  ((Real.exp (h / 2) : ℝ) : ℂ) *
                    xiMassJetIterate a ((σ : ℂ) + (u : ℂ) * Complex.I) (2 * N)
                      ((h : ℝ) : ℂ)) := by
        rw [xiMassJetSubcausticQuadrature]
        ring
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add hq1 hD)
    obtain ⟨u₁, hu₁⟩ := (hcomb.and (eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
    have hu₁0 : (0 : ℝ) ≤ u₁ := (hu₁ u₁ le_rfl).2
    set M₀ : ℕ := ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊ with hM₀
    refine (riemannHypothesis_iff_exists_xiMassJetWindowSum_bound ha hhalf hca N hQ0 hQle).mpr
      ⟨σ, max (C + Cw) (7 * (M₀ : ℝ) * xiMassJetVerticalBound a N σ), hσ, fun u hu => ?_⟩
    rcases le_or_gt u₁ u with hcase | hcase
    · exact le_trans (hu₁ u hcase).1 (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hcrude : ‖xiMassJetWindowSum a N 0 σ u‖
          ≤ 7 * ((xiMassJetWindowCutoff a 0 u : ℕ) : ℝ) * xiMassJetVerticalBound a N σ := by
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum
          (fun n _ => norm_xiMassPolyCenteredPrimeAtom_jet_le ha hσ N n)) ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ hV
        have hpsi : ∑ n ∈ Finset.range (xiMassJetWindowCutoff a 0 u + 1),
            (ArithmeticFunction.vonMangoldt n : ℝ)
            = chebyshevPsi (xiMassJetWindowCutoff a 0 u) := by
          rw [sum_range_succ_vonMangoldt_eq_sum_Icc]
          rfl
        rw [hpsi]
        exact chebyshevPsi_le_seven _
      refine le_trans hcrude ?_
      have hmono : xiMassJetWindowCutoff a 0 u ≤ M₀ := by
        refine le_trans (xiMassJetWindowCutoff_le 0 le_rfl u) ?_
        rw [hM₀]
        refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
        nlinarith [hcase.le]
      have hcast : ((xiMassJetWindowCutoff a 0 u : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hmono
      nlinarith [hcast, hV]

end

end RHTower
