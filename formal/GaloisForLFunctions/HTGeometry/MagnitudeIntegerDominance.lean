import GaloisForLFunctions.HTGeometry.MagnitudePositiveDegreeDominance

/-!
# Unconditional integer-dominance realization

The positive-jet-degree case is the superlacunary argument.  If the maximal jet degree is zero,
every appearing atom key is zero, so a nonzero grouped weight has no competitor and an arbitrarily
large mass gap can be chosen.  Together these cases discharge the `hintdom` interface of the
Mahler-normalized hypertranscendence capstone.
-/

open Filter Finset PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Zero maximal jet degree leaves only the zero atom key, so any nonzero grouped coefficient is
automatically dominant. -/
theorem exists_intDominance_of_zeroJetDegree {b : ℕ → ℝ} {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0)
    (hDzero : magnitudeMaxJetDegree n Q = 0) :
    ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
  classical
  obtain ⟨N, ν₀, hν₀, hw₀⟩ := exists_nonzero_aevalWeight hQ
  let mass : ℝ :=
    ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖
  let G := Real.log (mass + 1) + 1
  have hkeyZero : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ν = 0 := by
    intro ν hν
    have hcount := appearing_atom_count_le Q hν
    rw [hDzero] at hcount
    have hcount0 : ν.sum (fun _ k => k) = 0 := Nat.eq_zero_of_le_zero hcount
    ext i
    have hi := finsupp_apply_le_count ν i
    rw [hcount0] at hi
    simpa using Nat.eq_zero_of_le_zero hi
  have hmassnn : 0 ≤ mass := by
    dsimp [mass]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmasspos : 0 < mass + 1 := by linarith
  have hmassGap : mass < Real.exp G := by
    change mass < Real.exp (Real.log (mass + 1) + 1)
    rw [Real.exp_add, Real.exp_log hmasspos]
    have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr one_pos).le
    calc
      mass < mass + 1 := by linarith
      _ ≤ (mass + 1) * Real.exp 1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he hmasspos.le
  refine ⟨N, ν₀, G, hν₀, hw₀, ?_, ?_⟩
  · intro ν hν _hw hne
    exact False.elim (hne ((hkeyZero ν hν).trans (hkeyZero ν₀ hν₀).symm))
  · exact hmassGap

/-- The integer-dominance realization for every nonzero polynomial. -/
theorem exists_logSuperlacunary_intDominance {b : ℕ → ℝ}
    (hbpos : ∀ i, 0 < b i)
    (hratio : Tendsto (fun i => b (i + 1) / b i) atTop atTop)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0) :
    ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
  rcases Nat.eq_zero_or_pos (magnitudeMaxJetDegree n Q) with hzero | hpos
  · exact exists_intDominance_of_zeroJetDegree Q hQ hzero
  · exact exists_logSuperlacunary_intDominance_of_positiveJetDegree hbpos hratio Q hpos

/-- Log-superlacunary magnitude hypertranscendence with the integer-dominance interface fully
discharged.  The sole remaining imported input is Mahler integer normalization. -/
theorem hypertranscendental_of_mahler_logSuperlacunary {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {b : ℕ → ℝ}
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (- b i))
    (hbpos : ∀ i, 0 < b i)
    (hratio : Tendsto (fun i => b (i + 1) / b i) atTop atTop)
    (hmahler : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
        aeval (formalJets n (taylorPS f)) Q = 0 →
        ∃ (n' : ℕ) (Q' : MvPolynomial (Fin (n' + 2)) ℂ), Q' ≠ 0 ∧
          (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q' = (z : ℂ)) ∧
          aeval (formalJets n' (taylorPS f)) Q' = 0) :
    Hypertranscendental f := by
  refine hypertranscendental_of_aeval_survives hf (fun n Q hQ => ?_)
  intro hrel
  obtain ⟨n', Q', hQ', hint, hrel'⟩ := hmahler n Q hQ hrel
  obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hmass⟩ :=
    exists_logSuperlacunary_intDominance hbpos hratio Q' hQ'
  have hne := aeval_coeff_ne_zero_of_int_dominant_on_support
    n' N (taylorPS f) Q' hb hint ν₀ hν₀ hw₀ hgap hmass
  rw [hrel', map_zero] at hne
  exact hne rfl

end

end GaloisForLFunctions
