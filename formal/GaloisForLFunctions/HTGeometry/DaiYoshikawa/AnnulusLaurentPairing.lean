import GaloisForLFunctions.HTGeometry.DaiYoshikawa.AnnulusMonomialIntegral

/-!
# The Laurent pairing over an annulus

Proposition 5.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), evaluates

```text
√−1 ∫_{Y_t ∩ Δ²_p} α_i(x, t/x) \overline{α_j(x, t/x)} dx∧dx̄ / |x|²
```

by expanding both factors in Taylor series and integrating term by term.  On the annulus
`|t| ≤ |x| ≤ 1` each factor becomes a Laurent series in `x`, and only the `x⁰` terms produce a
logarithm; every other pair of exponents contributes a bounded quantity, and unequal exponents
contribute nothing.

This file proves that evaluation exactly, for Laurent expansions with finitely many terms:

```text
∫_{a<|x|<b} (Σ c_k x^k) \overline{(Σ d_k x^k)} |x|^{-2} dA
   = 2π [ c₀ \overline{d₀} log(b/a) + Σ_{k≠0} c_k \overline{d_k} (b^{2k} − a^{2k})/(2k) ] .
```

Only the term `k = 0` diverges as `a → 0`, and its coefficient is the product of the two residues.
-/

open MeasureTheory Set Real Complex

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus)

/-! ## Integrability of a monomial pairing -/

/-- The closed annulus. -/
def closedAnnulus (a b : ℝ) : Set ℂ := {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ ≤ b}

theorem isCompact_closedAnnulus (a b : ℝ) : IsCompact (closedAnnulus a b) := by
  have hclosed : IsClosed (closedAnnulus a b) := by
    have hpre : closedAnnulus a b = (fun w : ℂ => ‖w‖) ⁻¹' (Set.Icc a b) := by
      ext w
      simp [closedAnnulus, Set.mem_Icc]
    rw [hpre]
    exact isClosed_Icc.preimage continuous_norm
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) b) hclosed ?_
  intro w hw
  simpa [Metric.mem_closedBall] using hw.2

theorem deningerAnnulus_subset_closedAnnulus (a b : ℝ) :
    deningerAnnulus a b ⊆ closedAnnulus a b := by
  intro w hw
  exact ⟨le_of_lt hw.1, le_of_lt hw.2⟩

theorem continuousOn_annulusMonomial (j j' : ℤ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (annulusMonomial j j') (closedAnnulus a b) := by
  have hne : ∀ w ∈ closedAnnulus a b, w ≠ 0 := by
    intro w hw hzero
    rw [hzero] at hw
    have hz : a ≤ ‖(0 : ℂ)‖ := hw.1
    rw [norm_zero] at hz
    linarith
  have h1 : ContinuousOn (fun w : ℂ => w ^ j) (closedAnnulus a b) := fun w hw =>
    (continuousAt_zpow₀ w j (Or.inl (hne w hw))).continuousWithinAt
  have h2 : ContinuousOn (fun w : ℂ => (starRingEnd ℂ) w ^ j') (closedAnnulus a b) := by
    refine fun w hw => ?_
    have hcw : ((starRingEnd ℂ) w) ≠ 0 := by
      simpa using (hne w hw)
    exact ((continuousAt_zpow₀ ((starRingEnd ℂ) w) j' (Or.inl hcw)).comp
      (Complex.continuous_conj.continuousAt)).continuousWithinAt
  have h3 : ContinuousOn (fun w : ℂ => ((‖w‖ : ℂ) ^ 2)) (closedAnnulus a b) :=
    (Complex.continuous_ofReal.comp continuous_norm).continuousOn.pow 2
  refine ContinuousOn.div (h1.mul h2) h3 ?_
  intro w hw
  have : ((‖w‖ : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
    exact hne w hw
  exact pow_ne_zero 2 this

theorem integrableOn_annulusMonomial (j j' : ℤ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (annulusMonomial j j') (deningerAnnulus a b) volume := by
  have hcompact : IntegrableOn (annulusMonomial j j') (closedAnnulus a b) volume :=
    (continuousOn_annulusMonomial j j' (a := a) (b := b) ha).integrableOn_compact
      (isCompact_closedAnnulus a b)
  exact hcompact.mono_set (deningerAnnulus_subset_closedAnnulus a b)

/-! ## The Laurent pairing -/

/-- A Laurent polynomial with exponents in `s`. -/
noncomputable def laurentPoly (s : Finset ℤ) (c : ℤ → ℂ) (w : ℂ) : ℂ := ∑ k ∈ s, c k * w ^ k

/-- The pairing of two Laurent polynomials against the cylindrical area element. -/
noncomputable def laurentPairing (s : Finset ℤ) (c d : ℤ → ℂ) (w : ℂ) : ℂ :=
  laurentPoly s c w * (starRingEnd ℂ) (laurentPoly s d w) / ((‖w‖ : ℂ) ^ 2)

/-- The pairing expands into monomial pairings. -/
theorem laurentPairing_eq_sum (s : Finset ℤ) (c d : ℤ → ℂ) (w : ℂ) :
    laurentPairing s c d w
      = ∑ k ∈ s, ∑ k' ∈ s, c k * (starRingEnd ℂ) (d k') * annulusMonomial k k' w := by
  rw [laurentPairing, laurentPoly, laurentPoly, map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [annulusMonomial, map_mul, map_zpow₀]
  ring

/-- **The Laurent pairing over an annulus.**

Off-diagonal exponents cancel; the diagonal contributes a logarithm at exponent zero and a bounded
quantity otherwise. -/
theorem setIntegral_laurentPairing (s : Finset ℤ) (c d : ℤ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in deningerAnnulus a b, laurentPairing s c d w)
      = ∑ k ∈ s, c k * (starRingEnd ℂ) (d k)
          * (if k = 0 then (2 * π * Real.log (b / a) : ℂ)
             else 2 * π * ((b ^ (2 * k) - a ^ (2 * k)) / (2 * k))) := by
  have hint : ∀ k ∈ s, ∀ k' ∈ s,
      IntegrableOn (fun w => c k * (starRingEnd ℂ) (d k') * annulusMonomial k k' w)
        (deningerAnnulus a b) volume := by
    intro k _ k' _
    exact (integrableOn_annulusMonomial k k' ha).const_mul _
  have hstep : (∫ w in deningerAnnulus a b, laurentPairing s c d w)
      = ∑ k ∈ s, ∑ k' ∈ s, c k * (starRingEnd ℂ) (d k')
          * ∫ w in deningerAnnulus a b, annulusMonomial k k' w := by
    have hcongr : (∫ w in deningerAnnulus a b, laurentPairing s c d w)
        = ∫ w in deningerAnnulus a b,
            ∑ k ∈ s, ∑ k' ∈ s, c k * (starRingEnd ℂ) (d k') * annulusMonomial k k' w :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun w => laurentPairing_eq_sum s c d w)
    rw [hcongr, MeasureTheory.integral_finsetSum s
      (fun k hk => MeasureTheory.integrable_finsetSum s (fun k' hk' => hint k hk k' hk'))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [MeasureTheory.integral_finsetSum s (fun k' hk' => hint k hk k' hk')]
    refine Finset.sum_congr rfl fun k' _ => ?_
    exact MeasureTheory.integral_const_mul _ _
  rw [hstep]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hoff : ∀ k' ∈ s, k' ≠ k →
      c k * (starRingEnd ℂ) (d k') * ∫ w in deningerAnnulus a b, annulusMonomial k k' w = 0 := by
    intro k' _ hne
    rw [setIntegral_annulusMonomial_of_ne (Ne.symm hne) ha, mul_zero]
  rw [Finset.sum_eq_single k (fun k' hk' hne => hoff k' hk' hne)
    (fun hnot => absurd hk hnot)]
  by_cases hk0 : k = 0
  · subst hk0
    rw [setIntegral_annulusMonomial_zero ha hab, if_pos rfl]
  · rw [setIntegral_annulusMonomial_diag hk0 ha hab, if_neg hk0]

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
