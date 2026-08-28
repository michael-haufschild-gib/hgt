import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricCeilRootedDilation

/-!
# Error bound for the real-rooted minimal geometric schedule

This packages the canonical first-above-`z₀` starting level, the literal real root, its natural
ceiling cutoff, and the repaired grid-free accumulated-error estimate.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- Canonical first-above-cutoff exponent for a literal real root. -/
theorem eventually_exists_canonicalMinimalGeometricCeilRootedDilationCertificate
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ z₁ : ℝ,
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) < z₁ →
      (Nat.ceil z₁ : ℝ) ≤ X →
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth A X)
        (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth A X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) start 0 < z₁),
        ∃ _cert : MTGridFreeDilationCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
            (mtPaperWidth A X) hdelta hz₀Q hroot) A X, True := by
  filter_upwards [eventually_exists_minimalGeometricCeilRootedDilationCertificate A,
    eventually_mtC1_integer_schedule, Filter.eventually_ge_atTop (Real.exp 1)]
      with X hcertX hschedule hX
  intro z₁ hroom hzNatX
  have hlog : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdelta : 0 < mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _
  have hz₀One : 1 ≤ mtLowerCutoffNat X := by omega
  have hbracket := mtFirstGeometricStart_bracket hdelta hz₀One
  let start := mtFirstGeometricStart (mtPaperWidth A X) (mtLowerCutoffNat X)
  have hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
      mtGeometricLevel (mtPaperWidth A X) start 0 := hbracket.1.le
  have hroot : mtGeometricLevel (mtPaperWidth A X) start 0 < z₁ :=
    hbracket.2.trans_lt hroom
  obtain ⟨cert, hcert⟩ := hcertX start z₁ hz₀Q hbracket.2 hroot hzNatX hdelta
  exact ⟨start, hdelta, hz₀Q, hroot, cert, hcert⟩

/-- Exact-`δ_A` real-rooted source data with unconditional accumulated terminal-error bound. -/
theorem eventually_exists_canonicalMinimalGeometricCeilRootedSourceData_dilationErrorBound
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ : ℝ) (Y : ℕ) (a : ArithmeticFunction ℂ) (B : ℝ),
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) < z₁ →
      (Nat.ceil z₁ : ℝ) ≤ X → 1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth A X)
        (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth A X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) start 0 < z₁)
        (_cert : MTGridFreeDilationCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
            (mtPaperWidth A X) hdelta hz₀Q hroot) A X),
        let t := mtMinimalGeometricDepth (mtPaperWidth A X) start z₁ hdelta
        let data := MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
          (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
          (mtPaperWidth A X) hdelta hz₀Q hroot
        data.cutoff (Fin.last t) = Nat.ceil z₁ ∧
          let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
          ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data a J (Fin.last t) n‖ ^ 2 ≤
            25 * B ^ 2 * (Y : ℝ) *
              (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_exists_canonicalMinimalGeometricCeilRootedDilationCertificate A,
    eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_dilation A hA]
      with X hcertX hboundX
  intro z₁ Y a B hroom hzNatX hY hYX hB ha
  obtain ⟨start, hdelta, hz₀Q, hroot, cert, -⟩ := hcertX z₁ hroom hzNatX
  let t := mtMinimalGeometricDepth (mtPaperWidth A X) start z₁ hdelta
  let data := MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
    (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
    (mtPaperWidth A X) hdelta hz₀Q hroot
  refine ⟨start, hdelta, hz₀Q, hroot, cert, ?_, ?_⟩
  · exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_last
      (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
      (mtPaperWidth A X) hdelta hz₀Q hroot
  · exact hboundX t data cert a (Fin.last t) Y B hY hYX hB ha

end

end RHTower.Sieve
