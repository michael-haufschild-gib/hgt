import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateIteration
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricCeilRootedError

/-!
# Paper-scale aggregate error with an exact real recursive root

One canonical real-rooted schedule serves all aggregate Harman sources.  Its source cutoff is the
natural ceiling of the literal real root, while every Type-II block scale remains strictly below
that real root.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- Shared exact-real-root schedule, aggregate expansion, and accumulated-error bound. -/
theorem eventually_exists_mtHarmanAggregateIteration_ceilRootedDilationErrorBound
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (zRoot : ℝ) (Q D E Y : ℕ),
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) < zRoot →
      mtLowerCutoffNat X ≤ Nat.ceil zRoot → Nat.ceil zRoot ≤ D →
      (D : ℝ) ≤ X → 1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth A X)
        (hz₀Q : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth A X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) start 0 < zRoot)
        (_cert : MTGridFreeDilationCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start zRoot
            (mtPaperWidth A X) hdelta hz₀Q hroot) A X),
        let t := mtMinimalGeometricDepth (mtPaperWidth A X) start zRoot hdelta
        let data := MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
          (mtLowerCutoffNat X) (mtTruncationNat X) start zRoot
          (mtPaperWidth A X) hdelta hz₀Q hroot
        let endpoint := mtPaperAlignedEndpoint (mtLowerCutoffNat X) D
          (mtPaperWidth A X)
        let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
        data.cutoff (Fin.last t) = Nat.ceil zRoot ∧
          (∀ n ∈ Finset.Icc 1 Y,
            mtHarmanRectangularMinorantMain
                (t := D - mtLowerCutoffNat X) endpoint (Nat.ceil zRoot) Q D E n =
              (mtHarmanAggregateIterationMainAF
                  (outerDepth := D - mtLowerCutoffNat X)
                  endpoint (Nat.ceil zRoot) Q D (E : ℝ) data J (Fin.last t) +
                mtHarmanAggregateIterationErrorAF
                  (outerDepth := D - mtLowerCutoffNat X)
                  endpoint (Nat.ceil zRoot) Q D (E : ℝ) data J (Fin.last t)) n) ∧
          ∑ n ∈ Finset.Icc 1 Y,
              ‖mtHarmanAggregateIterationErrorAF
                (outerDepth := D - mtLowerCutoffNat X)
                endpoint (Nat.ceil zRoot) Q D (E : ℝ) data J (Fin.last t) n‖ ^ 2 ≤
            225 * (Y : ℝ) *
              (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [
    eventually_exists_canonicalMinimalGeometricCeilRootedDilationCertificate A,
    eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_dilation A hA,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    eventually_mtC1_integer_schedule]
      with X hcertX hboundX hprogress hschedule
  intro zRoot Q D E Y hroom hz₀z hzD hDX hY hYX
  have hzDX : (Nat.ceil zRoot : ℝ) ≤ X := by
    have hzDReal : (Nat.ceil zRoot : ℝ) ≤ (D : ℝ) := by exact_mod_cast hzD
    exact hzDReal.trans hDX
  obtain ⟨start, hdelta, hz₀Q, hroot, cert, -⟩ :=
    hcertX zRoot hroom hzDX
  let t := mtMinimalGeometricDepth (mtPaperWidth A X) start zRoot hdelta
  let data := MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
    (mtLowerCutoffNat X) (mtTruncationNat X) start zRoot
    (mtPaperWidth A X) hdelta hz₀Q hroot
  let endpoint := mtPaperAlignedEndpoint (mtLowerCutoffNat X) D
    (mtPaperWidth A X)
  let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
  have hz₀One : 1 ≤ mtLowerCutoffNat X := by omega
  have hz₀D : mtLowerCutoffNat X ≤ D := hz₀z.trans hzD
  have hmono : Monotone endpoint := by
    exact mtPaperAlignedEndpoint_monotone hz₀One hz₀D hdelta.le hprogress
  have hendpoint : ∀ i, 1 ≤ endpoint i := fun i =>
    hz₀One.trans
      (mtPaperAlignedEndpoint_mem_Icc hz₀One hz₀D hdelta.le hprogress i).1
  have hcutoff : data.cutoff (Fin.last t) = Nat.ceil zRoot := by
    exact MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule_cutoff_last
      (mtLowerCutoffNat X) (mtTruncationNat X) start zRoot
      (mtPaperWidth A X) hdelta hz₀Q hroot
  have hz₀Data : 1 < data.z₀ := by
    dsimp [data]
    rw [cert.z₀_eq]
    exact hschedule.1
  have hbaseCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco (Nat.ceil zRoot) Q)) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanBaseOneCoefficient_le_one
      (one_not_mem_primesIco (Nat.ceil zRoot) Q) m
  have hpairCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF
        (mtHarmanPairFamilyCoefficient (t := D - mtLowerCutoffNat X)
          endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanPairFamilyCoefficient_le_one
      hendpoint hmono (primesIco (Nat.ceil zRoot) D) (E : ℝ) m
  have htripleCoeff : ∀ {m : ℕ}, 0 < m →
      ‖mtCoefficientAF
        (mtHarmanTripleFamilyCoefficient (t := D - mtLowerCutoffNat X)
          endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)) m‖ ≤ 1 := by
    intro m hm
    rw [mtCoefficientAF_apply_of_pos _ hm]
    exact norm_mtHarmanTripleFamilyCoefficient_le_one
      hendpoint hmono (primesIco (Nat.ceil zRoot) D) (E : ℝ) m
  have hbaseError :
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF
              (mtHarmanBaseOneCoefficient (primesIco (Nat.ceil zRoot) Q)))
            J (Fin.last t) n‖ ^ 2 ≤
        25 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
    simpa only [J, one_pow, mul_one] using
      hboundX t data cert
        (mtCoefficientAF
          (mtHarmanBaseOneCoefficient (primesIco (Nat.ceil zRoot) Q)))
        (Fin.last t) Y 1 hY hYX (by norm_num) hbaseCoeff
  have hpairError :
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF
              (mtHarmanPairFamilyCoefficient (t := D - mtLowerCutoffNat X)
                endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
            J (Fin.last t) n‖ ^ 2 ≤
        25 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
    simpa only [J, one_pow, mul_one] using
      hboundX t data cert
        (mtCoefficientAF
          (mtHarmanPairFamilyCoefficient (t := D - mtLowerCutoffNat X)
            endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
        (Fin.last t) Y 1 hY hYX (by norm_num) hpairCoeff
  have htripleError :
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data
            (mtCoefficientAF
              (mtHarmanTripleFamilyCoefficient (t := D - mtLowerCutoffNat X)
                endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
            J (Fin.last t) n‖ ^ 2 ≤
        25 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
    simpa only [J, one_pow, mul_one] using
      hboundX t data cert
        (mtCoefficientAF
          (mtHarmanTripleFamilyCoefficient (t := D - mtLowerCutoffNat X)
            endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
        (Fin.last t) Y 1 hY hYX (by norm_num) htripleCoeff
  refine ⟨start, hdelta, hz₀Q, hroot, cert, hcutoff, ?_, ?_⟩
  · intro n hnIcc
    have hn : 0 < n := by
      rw [Finset.mem_Icc] at hnIcc
      omega
    have hnY : n ≤ Y := (Finset.mem_Icc.mp hnIcc).2
    exact mtHarmanRectangularMinorantMain_eq_aggregateIteration
      (outerDepth := D - mtLowerCutoffNat X) endpoint (Nat.ceil zRoot) Q D E data J
      (Fin.last t) hcutoff hn hz₀Data hnY rfl
  · have haggregate := sum_normSq_mtHarmanAggregateIterationErrorAF_le
      (outerDepth := D - mtLowerCutoffNat X) (Finset.Icc 1 Y)
      endpoint (Nat.ceil zRoot) Q D (E : ℝ) data J (Fin.last t)
    calc
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanAggregateIterationErrorAF
            (outerDepth := D - mtLowerCutoffNat X)
            endpoint (Nat.ceil zRoot) Q D (E : ℝ) data J (Fin.last t) n‖ ^ 2 ≤
        3 * ∑ n ∈ Finset.Icc 1 Y,
            ‖mtAccumulatedSourceErrorAF data
              (mtCoefficientAF
                (mtHarmanBaseOneCoefficient (primesIco (Nat.ceil zRoot) Q)))
              J (Fin.last t) n‖ ^ 2 +
        3 * ∑ n ∈ Finset.Icc 1 Y,
            ‖mtAccumulatedSourceErrorAF data
              (mtCoefficientAF
                (mtHarmanPairFamilyCoefficient (t := D - mtLowerCutoffNat X)
                  endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
              J (Fin.last t) n‖ ^ 2 +
        3 * ∑ n ∈ Finset.Icc 1 Y,
            ‖mtAccumulatedSourceErrorAF data
              (mtCoefficientAF
                (mtHarmanTripleFamilyCoefficient (t := D - mtLowerCutoffNat X)
                  endpoint (primesIco (Nat.ceil zRoot) D) (E : ℝ)))
              J (Fin.last t) n‖ ^ 2 := haggregate
      _ ≤ 225 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
        nlinarith

end

end RHTower.Sieve
