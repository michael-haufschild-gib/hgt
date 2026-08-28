import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricCertificate

/-!
# Repaired terminal error on exact geometric blocks

The canonical rooted geometric schedule now feeds the existing grid-free accumulated-error
theorem without clipped or non-geometric blocks.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

theorem eventually_exists_canonicalMinimalGeometricSourceData_errorBound
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (z₁ Y : ℕ) (a : ArithmeticFunction ℂ) (B : ℝ),
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth (A + 1) X) < (z₁ : ℝ) →
      (z₁ : ℝ) ≤ X → 1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth (A + 1) X)
        (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth (A + 1) X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth (A + 1) X) start 0 < (z₁ : ℝ))
        (_cert : MTGridFreePaperScaleCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
            (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot) A X),
        let t := mtMinimalGeometricDepth (mtPaperWidth (A + 1) X) start
          (z₁ : ℝ) hdelta
        let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
          (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
          (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot
        data.cutoff (Fin.last t) = z₁ ∧
          let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
          ∑ n ∈ Finset.Icc 1 Y,
              ‖mtAccumulatedSourceErrorAF data a J (Fin.last t) n‖ ^ 2 ≤
            15 * B ^ 2 * (Y : ℝ) *
              (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_exists_canonicalMinimalGeometricRootedPaperScaleCertificate A,
    eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_gridFree A hA]
      with X hcertX hboundX
  intro z₁ Y a B hroom hz₁X hY hYX hB ha
  obtain ⟨start, hdelta, hz₀Q, hroot, cert, -⟩ := hcertX z₁ hroom hz₁X
  let t := mtMinimalGeometricDepth (mtPaperWidth (A + 1) X) start
    (z₁ : ℝ) hdelta
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
    (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot
  refine ⟨start, hdelta, hz₀Q, hroot, cert, ?_, ?_⟩
  · exact MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_cutoff_last
      (mtLowerCutoffNat X) (mtTruncationNat X) start z₁
      (mtPaperWidth (A + 1) X) hdelta hz₀Q hroot
  · exact hboundX t data cert a (Fin.last t) Y B hY hYX hB ha

end

end RHTower.Sieve
