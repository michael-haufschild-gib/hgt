import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzEdgeProducer
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Prime-edge cone escape for the literal matched--quantile graph

The coupled Lorentz source has a nonnegative singular graph dissipation, but that does not make
its matched and quantile edge coordinates uniformly comparable.  On actual adjacent prime edges,
the quantile-centroid slope exceeds every fixed multiple of the matched-centroid slope.  Therefore
no fixed local graph-Poincaré wall can turn the new dissipation into a bound for the original
Lorentz source.  A viable wall must use nonlocal prime--polar--Gamma cancellation.

This is a source-level no-go with a positive survivor: explicit prime-edge cone escape.  It does
not estimate the signed completed source, assert a global wall, or claim RH.
-/

open Filter Topology

noncomputable section

namespace RHTower

private theorem ccmActualHeadMatchedPolarCentroid_ge_two_mul_sqrt {n : ℕ} (hn : 0 < n) :
    2 * Real.sqrt (n : ℝ) ≤ ccmActualHeadMatchedPolarCentroid n := by
  have hsq := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid n :=
    ccmActualHeadMatchedPolarCentroid_pos n
  have hsqrt : Real.sqrt (n : ℝ) ^ (2 : ℕ) = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (criticalMellinAtomWeight n)]

private theorem ccmActualHeadMatchedPolarCentroid_succ_sub_le {n : ℕ} (hn : 2 ≤ n) :
    ccmActualHeadMatchedPolarCentroid (n + 1) -
      ccmActualHeadMatchedPolarCentroid n ≤ 5 / (4 * Real.sqrt (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hn10 : 0 < n + 1 := by omega
  have hc : 0 ≤ ccmActualHeadMatchedPolarCentroid (n + 1) -
      ccmActualHeadMatchedPolarCentroid n := by
    have hlt : n - 2 < n + 1 - 2 := by omega
    have hmono := strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hlt
    exact sub_nonneg.mpr (by
      simpa only [Nat.sub_add_cancel hn,
        Nat.sub_add_cancel (show 2 ≤ n + 1 by omega)] using hmono.le)
  have hsqn := ccmActualHeadMatchedPolarCentroid_sq n hn0
  have hsqnext := ccmActualHeadMatchedPolarCentroid_sq (n + 1) hn10
  norm_num [Nat.cast_add] at hsqnext
  have hwnext0 : 0 ≤ criticalMellinAtomWeight (n + 1) :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hwnext2 : criticalMellinAtomWeight (n + 1) ≤ 2 :=
    criticalMellinAtomWeight_le_two_of_pos hn10
  have hwnextsq : criticalMellinAtomWeight (n + 1) ^ (2 : ℕ) ≤ 4 := by
    nlinarith
  have hsqdiff : ccmActualHeadMatchedPolarCentroid (n + 1) ^ (2 : ℕ) -
      ccmActualHeadMatchedPolarCentroid n ^ (2 : ℕ) ≤ 5 := by
    nlinarith [sq_nonneg (criticalMellinAtomWeight n)]
  have hsum : 4 * Real.sqrt (n : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid (n + 1) +
        ccmActualHeadMatchedPolarCentroid n := by
    have hcn := ccmActualHeadMatchedPolarCentroid_ge_two_mul_sqrt hn0
    have hcnext := ccmActualHeadMatchedPolarCentroid_ge_two_mul_sqrt hn10
    have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show n ≤ n + 1 by omega)
    nlinarith
  have hprod : (ccmActualHeadMatchedPolarCentroid (n + 1) -
      ccmActualHeadMatchedPolarCentroid n) *
      (ccmActualHeadMatchedPolarCentroid (n + 1) +
        ccmActualHeadMatchedPolarCentroid n) ≤ 5 := by
    convert hsqdiff using 1 <;> ring
  have hscale : (ccmActualHeadMatchedPolarCentroid (n + 1) -
      ccmActualHeadMatchedPolarCentroid n) * (4 * Real.sqrt (n : ℝ)) ≤ 5 := by
    exact (mul_le_mul_of_nonneg_left hsum hc).trans hprod
  have hsqrt0 : 0 < 4 * Real.sqrt (n : ℝ) := by positivity
  exact (le_div_iff₀ hsqrt0).2 hscale

private theorem ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomMean (n : ℕ) :
    ccmActualHeadQuantilePolarCentroid (n + 1) -
      ccmActualHeadQuantilePolarCentroid n =
        (criticalMellinAtomWeight n + criticalMellinAtomWeight (n + 1)) / 2 := by
  unfold ccmActualHeadQuantilePolarCentroid
  have h0 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have h1 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n + 1)
  norm_num [Nat.add_assoc] at h0 h1 ⊢
  linarith

private theorem criticalMellinAtomWeight_eq_log_div_sqrt_prime (p : Nat.Primes) :
    criticalMellinAtomWeight (p : ℕ) = Real.log (p : ℝ) / Real.sqrt (p : ℝ) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt, ArithmeticFunction.vonMangoldt_apply_prime p.2]

private theorem prime_quantileSlope_ge_log_mul_matchedSlope (p : Nat.Primes) :
    (2 * Real.log (p : ℝ) / 5) *
      (ccmActualHeadMatchedPolarCentroid (p + 1) -
        ccmActualHeadMatchedPolarCentroid p) ≤
      ccmActualHeadQuantilePolarCentroid (p + 1) -
        ccmActualHeadQuantilePolarCentroid p := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hsqrt : 0 < Real.sqrt (p : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast p.2.one_le
  have hfac0 : 0 ≤ 2 * Real.log (p : ℝ) / 5 := by positivity
  have hmatched := ccmActualHeadMatchedPolarCentroid_succ_sub_le hp2
  have hquantile : Real.log (p : ℝ) / (2 * Real.sqrt (p : ℝ)) ≤
      ccmActualHeadQuantilePolarCentroid (p + 1) -
        ccmActualHeadQuantilePolarCentroid p := by
    rw [ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomMean]
    have hnext : 0 ≤ criticalMellinAtomWeight (p + 1) := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    rw [criticalMellinAtomWeight_eq_log_div_sqrt_prime]
    have hrewrite :
        (Real.log (p : ℝ) / Real.sqrt (p : ℝ) +
          criticalMellinAtomWeight (p + 1)) / 2 =
          Real.log (p : ℝ) / (2 * Real.sqrt (p : ℝ)) +
            criticalMellinAtomWeight (p + 1) / 2 := by
      field_simp [hsqrt.ne']
    rw [hrewrite]
    linarith
  calc
    (2 * Real.log (p : ℝ) / 5) *
        (ccmActualHeadMatchedPolarCentroid (p + 1) -
          ccmActualHeadMatchedPolarCentroid p) ≤
        (2 * Real.log (p : ℝ) / 5) * (5 / (4 * Real.sqrt (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hmatched hfac0
    _ = Real.log (p : ℝ) / (2 * Real.sqrt (p : ℝ)) := by
      field_simp [hsqrt.ne']
      ring
    _ ≤ _ := hquantile

/-- **Actual prime-edge cone escape.** For every proposed finite local slope `R`, a literal
adjacent prime edge has positive matched separation and quantile separation greater than `R`
times it.  The assertion uses neither a prime-gap hypothesis nor an asymptotic source premise. -/
theorem exists_actualHeadMatchedQuantilePrimeConeEscape (R : ℝ) :
    ∃ p : Nat.Primes,
      0 < ccmActualHeadMatchedPolarCentroid (p + 1) -
        ccmActualHeadMatchedPolarCentroid p ∧
      R * (ccmActualHeadMatchedPolarCentroid (p + 1) -
        ccmActualHeadMatchedPolarCentroid p) <
        ccmActualHeadQuantilePolarCentroid (p + 1) -
          ccmActualHeadQuantilePolarCentroid p := by
  have hprimeCast : Tendsto (fun j : ℕ => (nth_prime j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop
  have hlog : Tendsto (fun j : ℕ => 2 * Real.log (nth_prime j : ℝ) / 5)
      atTop atTop := by
    have hbase := Real.tendsto_log_atTop.comp hprimeCast
    convert hbase.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 5) using 1
    ext j
    simp only [Function.comp_apply]
    ring
  have heventual : ∀ᶠ j : ℕ in atTop, R < 2 * Real.log (nth_prime j : ℝ) / 5 :=
    hlog.eventually_gt_atTop R
  rcases (eventually_atTop.1 heventual) with ⟨j, hj⟩
  let p : Nat.Primes := ⟨nth_prime j,
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩
  have hpos : 0 < ccmActualHeadMatchedPolarCentroid (p + 1) -
      ccmActualHeadMatchedPolarCentroid p := by
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hp12 : 2 ≤ (p : ℕ) + 1 := by omega
    have hlt : (p : ℕ) - 2 < (p : ℕ) + 1 - 2 := by omega
    have hmono := strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hlt
    exact sub_pos.mpr (by
      simpa only [Nat.sub_add_cancel hp2, Nat.sub_add_cancel hp12] using hmono)
  have hslope := prime_quantileSlope_ge_log_mul_matchedSlope p
  refine ⟨p, hpos, ?_⟩
  have hj' : R < 2 * Real.log (p : ℝ) / 5 := by simpa [p] using hj j (le_refl _)
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hj' hpos) hslope

/-- **Fixed local-wall no-go.** No finite coefficient uniformly dominates quantile-centroid
increments by matched-centroid increments.  Therefore the literal singular graph dissipation
cannot yield the original source bound through a fixed local edge comparison. -/
theorem not_exists_uniform_ccmActualHeadQuantileSlope_le_matchedSlope :
    ¬ ∃ R : ℝ, ∀ n : ℕ,
      ccmActualHeadQuantilePolarCentroid (n + 1) - ccmActualHeadQuantilePolarCentroid n ≤
        R * (ccmActualHeadMatchedPolarCentroid (n + 1) -
          ccmActualHeadMatchedPolarCentroid n) := by
  rintro ⟨R, hR⟩
  obtain ⟨p, _, hp⟩ := exists_actualHeadMatchedQuantilePrimeConeEscape R
  exact (not_lt_of_ge (hR p)) hp

end RHTower
