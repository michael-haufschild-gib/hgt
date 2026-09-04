import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownActiveBoxSelection

/-!
# Fixed-shift Case-II mean square with the original cofactor

This is the product-length-preserving Case-II receiver.  Every active degree-three box selects a
literal long-enough factor.  Möbius and both zeta/logarithm frequency branches are discharged
internally; fixed-shift Montgomery retains the erase-complement multiplied by the original
Dirichlet cofactor.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- Menon's complete active aggregate, on one positive dyadic frequency band, satisfies a
selected-factor mean-square bound with an arbitrary unshifted Dirichlet cofactor. -/
theorem exists_absolute_eventually_sum_normSq_activeAggregate_mul_dirPoly_le_selectedFactor
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X M : ℕ} {T0 t u sigma U delta H : ℝ},
        1 ≤ L → 1 ≤ X → 1 ≤ M → 1 ≤ sigma → 0 < U →
        0 < delta → 0 ≤ H →
        ∀ (b : Fin M → ℂ) {S : Finset ℕ} {lam : ℕ → ℝ},
        (∀ i, lam i + delta ≤ lam (i + 1)) →
        (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ H) →
        (∀ r ∈ S,
          U ≤ u + lam r ∧ u + lam r ≤ 2 * U ∧
          |u + lam r| ≤ (a : ℝ) ^ (3 : ℕ)) →
        ∃ j : (box : HeathBrownBoxChoice L X 3) →
            HeathBrownBoxFactorIndex 3 box.m,
          (∀ box ∈ menonHeathBrownActiveBoxes L X T0 t (a : ℝ),
            1 ≤ heathBrownBoxFactorExponent box.a box.b box.q (j box) ∧
            (a : ℝ) ^ (1 / 8 : ℝ) ≤
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) : ℕ) : ℝ)) ∧
            (heathBrownBoxFactorKind 3 box.m (j box) = .moebius →
              2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) ≤ L)) ∧
          ∑ r ∈ S,
              ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t (a : ℝ)
                  ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
                dirPoly M b (-lam r)‖ ^ 2 ≤
            (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
              ∑ box ∈ menonHeathBrownActiveBoxes L X T0 t (a : ℝ),
                menonHeathBrownSelectedFactorCofactorCost box (j box)
                  epsilon C sigma
                  (menonHeathBrownSelectedFactorUpper X
                    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) : ℕ) : ℝ))
                    sigma U (heathBrownBoxFactorKind 3 box.m (j box))
                    (heathBrownBoxFactorExponent box.a box.b box.q (j box)))
                  delta H M b := by
  obtain ⟨C, hC, hreceiver⟩ :=
    exists_sum_normSq_windowRelevantAggregate_mul_dirPoly_le_activeSelectedFactor hepsilon
  obtain ⟨q0, hfactorLate⟩ := Filter.eventually_atTop.mp
    eventually_norm_heathBrownBoxFactorValue_le_selectedFactorUpper
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max ((64 : ℕ) ^ 8) (2 ^ (8 * q0)))]
    with a ha
  intro L X M T0 t u sigma U delta H hL hX hM hsigma hU hdelta hH b S lam hgap hband
    hfrequency
  have ha64 : (64 : ℝ) ^ 8 ≤ (a : ℝ) := by
    exact_mod_cast (le_trans (le_max_left _ _) ha)
  obtain ⟨j, hj⟩ := exists_activeBox_selectedFactor (T0 := T0) (t := t) hL ha64
  let V : HeathBrownBoxChoice L X 3 → ℝ := fun box =>
    menonHeathBrownSelectedFactorUpper X
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) : ℕ) : ℝ))
      sigma U (heathBrownBoxFactorKind 3 box.m (j box))
      (heathBrownBoxFactorExponent box.a box.b box.q (j box))
  refine ⟨j, hj, ?_⟩
  apply hreceiver L X T0 t (a : ℝ) M hM b u j V (zero_le_one.trans hsigma)
    (fun box => by
      dsimp only [V]
      rw [menonHeathBrownSelectedFactorUpper]
      exact (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)).trans (le_max_left _ _))
    hdelta hH hgap hband
  intro box hbox r hr
  let q := heathBrownBoxFactorExponent box.a box.b box.q (j box)
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hq : q0 ≤ q := by
    apply exponent_le_of_eight_pow_le_of_rpow_oneEighth_le
    · exact le_trans (le_max_right _ _) ha
    · simpa only [q] using (hj box hbox).2.1
  have hfreq := hfrequency r hr
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hNlower : (a : ℝ) ^ (1 / 8 : ℝ) ≤ N := by
    simpa only [q, N] using (hj box hbox).2.1
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg ha0.le _) hNlower 24
  have haPower : ((a : ℝ) ^ (1 / 8 : ℝ)) ^ (24 : ℕ) =
      (a : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num [Real.rpow_natCast]
  rw [haPower] at hpow
  have hpoint := hfactorLate q hq L X 3 box (j box) sigma U (u + lam r)
    hX hsigma hU hfreq.1 hfreq.2.1 rfl (hj box hbox).2.2
  dsimp only [V]
  exact hpoint (by
    simpa only [q, N] using hfreq.2.2.trans hpow)

end

end RHTower.Sieve
