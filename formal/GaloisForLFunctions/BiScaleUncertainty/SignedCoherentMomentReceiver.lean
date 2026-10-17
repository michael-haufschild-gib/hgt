import GaloisForLFunctions.BiScaleUncertainty.SourceLatticeMultiplierFrame

/-!
# Signed coherent correction improves the odd moment receiver

Equal-weight packets preserve cancellation in the centered source correction.
Its finite lattice support gives an exact affine boundary law. The boundary
intercept disappears from the moment bound, leaving the signed correction sum.
This coefficient controls coherent packets asymptotically, not arbitrary weights.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedCoherentMoment
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment HyperbolicRay SourceLattice
noncomputable section

/-- Signed centered source correction per lattice site. -/
def signedCorrectionMass (f : C_c(ℝ, ℝ)) : ℝ := ∑' k : ℤ, correctionSample f k

/-- Fixed boundary intercept for sufficiently long equal-weight packets. -/
def correctionFirstMoment (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * ∑' m : ℕ, ((m : ℝ) + 1) * correctionSample f ((m : ℤ) + 1)

/-- Budget for the coherent moment; it is not an arbitrary-weight frame bound. -/
def coherentBudget (f : C_c(ℝ, ℝ)) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 + signedCorrectionMass f +
    Real.sqrt (2 * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f)

private theorem summable_transform (f : C_c(ℝ, ℝ)) (g : ℝ → ℝ) (hg : g 0 = 0) :
    Summable (fun k : ℤ => g (correctionSample f k)) := by
  apply summable_of_hasFiniteSupport
  apply (correctionSample_finite f).subset
  intro k hk
  change g (correctionSample f k) ≠ 0 at hk
  change correctionSample f k ≠ 0
  intro hz
  exact hk (by rw [hz, hg])

private theorem positive_support_finite (f : C_c(ℝ, ℝ)) :
    (Function.support (fun m : ℕ => correctionSample f ((m : ℤ) + 1))).Finite := by
  exact (correctionSample_finite f).preimage (f := fun m : ℕ => (m : ℤ) + 1) (by
    intro a _ b _ h
    change (a : ℤ) + 1 = (b : ℤ) + 1 at h
    omega)

theorem signedCorrectionMass_eq_positive (f : C_c(ℝ, ℝ)) :
    signedCorrectionMass f = 2 * ∑' m : ℕ, correctionSample f ((m : ℤ) + 1) := by
  unfold signedCorrectionMass
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (correctionSample_neg f)
    (summable_of_hasFiniteSupport (correctionSample_finite f))]
  rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => correctionSample f (m : ℤ))]
  simp [correctionSample, nsmul_eq_mul]

private theorem even_chain_sum (k : ℤ → ℝ) (hz : k 0 = 0)
    (heven : ∀ z, k (-z) = k z) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - (i : ℤ))) =
      2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1) := by
  induction N with
  | zero => simp [hz]
  | succ N ih =>
    have hi (i : ℕ) :
        (∑ j ∈ Finset.range (N + 1 + 1), k ((j : ℤ) - (i : ℤ))) =
          (∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - (i : ℤ))) +
            k (((N + 1 : ℕ) : ℤ) - (i : ℤ)) := Finset.sum_range_succ _ _
    have hc : (∑ i ∈ Finset.range (N + 1), k (((N + 1 : ℕ) : ℤ) - (i : ℤ))) =
        ∑ m ∈ Finset.range (N + 1), k ((m : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect (fun m => k ((m : ℤ) + 1)) (N + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      congr 1
      omega
    have hr : (∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - ((N + 1 : ℕ) : ℤ))) =
        ∑ i ∈ Finset.range (N + 1), k (((N + 1 : ℕ) : ℤ) - (i : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (j : ℤ) - ((N + 1 : ℕ) : ℤ) =
        -(((N + 1 : ℕ) : ℤ) - (j : ℤ)) by ring, heven]
    have ht : (∑ m ∈ Finset.range (N + 1), (((N + 1 : ℕ) : ℝ) - (m : ℝ)) *
        k ((m : ℤ) + 1)) =
        (∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1)) +
          ∑ m ∈ Finset.range (N + 1), k ((m : ℤ) + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun m => k ((m : ℤ) + 1))]
      simp only [Nat.cast_add, Nat.cast_one]
      have he (m : ℕ) : ((N : ℝ) + 1 - (m : ℝ)) * k ((m : ℤ) + 1) =
          ((N : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1) + k ((m : ℤ) + 1) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      ring
    change (∑ i ∈ Finset.range (N + 1 + 1),
      ∑ j ∈ Finset.range (N + 1 + 1), k ((j : ℤ) - (i : ℤ))) = _
    rw [Finset.sum_range_succ]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, sub_self, hz, add_zero, hr, hc, ih, ht]
    ring

/-- Exact triangular pair count, before taking a limit or absolute values. -/
theorem sourceCorrection_one_eq_triangle (f : C_c(ℝ, ℝ)) (N : ℕ) :
    sourceCorrection f (1 / 2) (sourceMean f (1 / 2)) (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) =
        2 * ∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * correctionSample f ((m : ℤ) + 1) := by
  rw [sourceCorrection_eq_lattice_quad]
  simp only [one_mul]
  exact even_chain_sum _ (by simp [correctionSample]) (correctionSample_neg f) N

/-- Compactness makes the boundary correction exactly constant eventually. -/
theorem sourceCorrection_one_eventually_affine (f : C_c(ℝ, ℝ)) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      sourceCorrection f (1 / 2) (sourceMean f (1 / 2)) (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) =
          ((N : ℝ) + 1) * signedCorrectionMass f - correctionFirstMoment f := by
  obtain ⟨M, hM⟩ := (positive_support_finite f).bddAbove
  refine ⟨M + 1, ?_⟩
  intro N hN
  have hz (m : ℕ) (hm : m ∉ Finset.range N) : correctionSample f ((m : ℤ) + 1) = 0 := by
    by_contra hn
    have hb := hM (Function.mem_support.mpr hn)
    have := Finset.mem_range.not.mp hm
    omega
  have hs : (∑' m : ℕ, correctionSample f ((m : ℤ) + 1)) =
      ∑ m ∈ Finset.range N, correctionSample f ((m : ℤ) + 1) := tsum_eq_sum hz
  have ht : (∑' m : ℕ, ((m : ℝ) + 1) * correctionSample f ((m : ℤ) + 1)) =
      ∑ m ∈ Finset.range N, ((m : ℝ) + 1) * correctionSample f ((m : ℤ) + 1) :=
    tsum_eq_sum (by intro m hm; rw [hz m hm, mul_zero])
  rw [sourceCorrection_one_eq_triangle, signedCorrectionMass_eq_positive,
    correctionFirstMoment, hs, ht]
  rw [show ((N : ℝ) + 1) * (2 * ∑ m ∈ Finset.range N, correctionSample f ((m : ℤ) + 1)) =
    2 * ((N : ℝ) + 1) * ∑ m ∈ Finset.range N, correctionSample f ((m : ℤ) + 1) by ring]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem odd_sinhGram_le_signed_correction (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (N + 1)) w (chainNode (Real.log 2)) ≤
        (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          Real.sqrt (2 * autocorr (centeredSource (oddCompactSource f) (1 / 2)
            (sourceMean (oddCompactSource f) (1 / 2))) 0 * correlationMass (oddCompactSource f))) *
              weightEnergy N w + sourceCorrection (oddCompactSource f) (1 / 2)
                (sourceMean (oddCompactSource f) (1 / 2)) (Finset.range (N + 1)) w
                  (chainNode (Real.log 2)) := by
  let F := oddCompactSource f
  let Q := autocorr (centeredSource F (1 / 2) (sourceMean F (1 / 2))) 0
  have hQ : 0 ≤ Q := autocorr_zero_nonneg _
  have hΓ := correlationMass_nonneg F
  have hW := weightEnergy_nonneg N w
  have hG := (differenceGram_le_lattice F N w).trans
    (mul_le_mul_of_nonneg_left (dyadic_collisionEnergy_le N w) hΓ)
  have hs : Real.sqrt (Q * translationGramEnergy F (pairSet N)
      (differenceWeight (1 / 2) w (chainNode (Real.log 2)))
      (differenceNode (chainNode (Real.log 2)))) ≤
      Real.sqrt (2 * Q * correlationMass F) * weightEnergy N w := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hW, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Q * correlationMass F)]
    have h := mul_le_mul_of_nonneg_left hG hQ
    nlinarith only [h]
  have hd := odd_defect_le_sourceDefectUpper f (1 / 2) (sourceMean F (1 / 2))
    (Finset.range (N + 1)) w (chainNode (Real.log 2))
  unfold sourceDefectUpper at hd
  rw [sinhGram_eq_diagonal_add_defect]
  change autocorr (sinhCompact (1 / 2) F) 0 * weightEnergy N w + _ ≤
    (autocorr (sinhCompact (1 / 2) F) 0 + Real.sqrt (2 * Q * correlationMass F)) *
      weightEnergy N w + _
  change _ ≤ _ + Real.sqrt (Q * translationGramEnergy F (pairSet N)
    (differenceWeight (1 / 2) w (chainNode (Real.log 2)))
    (differenceNode (chainNode (Real.log 2)))) at hd
  linarith only [hd, hs]

/-- Actual coherent multiplier packets retain the signed extensive correction. -/
theorem odd_coherentGram_eventually_le (f : C_c(ℝ, ℝ)) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
        (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) ≤
          coherentBudget (oddCompactSource f) * ((N : ℝ) + 1) -
            correctionFirstMoment (oddCompactSource f) := by
  obtain ⟨M, hM⟩ := sourceCorrection_one_eventually_affine (oddCompactSource f)
  refine ⟨M, ?_⟩
  intro N hN
  have h := odd_sinhGram_le_signed_correction f N (fun _ => 1)
  rw [hM N hN] at h
  simp only [weightEnergy, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at h
  unfold coherentBudget
  linarith only [h]

private theorem integral_sq_le_eventual_affine (g : C_c(ℝ, ℝ)) (C D : ℝ) (M : ℕ)
    (hframe : ∀ N : ℕ, M ≤ N → translationGramEnergy g (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) ≤ C * ((N : ℝ) + 1) + D) :
    (∫ u, g u) ^ 2 ≤ Real.log 2 * C := by
  by_contra hn
  let A := (∫ u, g u) ^ 2
  let B := 2 * (multiplierSourceRadius g + 1)
  let d := Real.log 2
  let K := (B - d) * C + d * D
  let J := (B - d) * D
  have heps : 0 < A - d * C := by dsimp [A, d]; linarith only [hn]
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M : ℝ) ((|K| + |J|) / (A - d * C)))
  have hMN : M ≤ N := by
    have := (le_max_left (M : ℝ) ((|K| + |J|) / (A - d * C))).trans_lt hN
    exact_mod_cast this.le
  have hlarge := (div_lt_iff₀ heps).mp
    ((le_max_right (M : ℝ) ((|K| + |J|) / (A - d * C))).trans_lt hN)
  have hh := (integral_sq_le_chain_gram g N).trans
    (mul_le_mul_of_nonneg_left (hframe N hMN) (chainSpan_pos g N).le)
  have hm : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith only [hN0]
  have hmpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpoly : (A - d * C) * ((N : ℝ) + 1) ^ 2 ≤ K * ((N : ℝ) + 1) + J := by
    dsimp [A, B, d, K, J]
    unfold chainSpan at hh
    nlinarith only [hh]
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hmpos.le
  have hJ : J ≤ |J| * ((N : ℝ) + 1) :=
    (le_abs_self J).trans (by nlinarith only [hm, abs_nonneg J])
  have hlin : (A - d * C) * ((N : ℝ) + 1) ≤ |K| + |J| :=
    le_of_mul_le_mul_right (by nlinarith only [hpoly, hK, hJ]) hmpos
  nlinarith only [hlin, hlarge, heps]

/-- The fixed boundary intercept vanishes; signed source cancellation survives. -/
theorem odd_moment_sq_le_coherentBudget (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      Real.log 2 * coherentBudget (oddCompactSource f) := by
  rw [← integral_sinhCompact_eq_moment]
  obtain ⟨M, hM⟩ := odd_coherentGram_eventually_le f
  exact integral_sq_le_eventual_affine _ _ (-correctionFirstMoment (oddCompactSource f)) M
    (by simpa only [sub_eq_add_neg] using hM)

theorem odd_coherentBudget_nonneg (f : C_c(ℝ, ℝ)) :
    0 ≤ coherentBudget (oddCompactSource f) := by
  have h := (sq_nonneg (∫ u, oddCompactSource f u * Real.sinh (u / 2))).trans
    (odd_moment_sq_le_coherentBudget f)
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith only [h, hd]

/-- Full plastic receiver with an unconditional signed source moment price. -/
theorem odd_plasticCrossover_ge_coherentBudget (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * coherentBudget (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_moment_sq_le_coherentBudget f
  nlinarith only [hp, hm]

/-- Negative centered source corrections measure exactly the recovered cancellation. -/
def negativeCorrectionMass (f : C_c(ℝ, ℝ)) : ℝ := ∑' k : ℤ, max (-correctionSample f k) 0

theorem negativeCorrectionMass_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ negativeCorrectionMass f :=
  tsum_nonneg fun _ => le_max_right _ _

theorem latticeFrame_sub_coherentBudget (f : C_c(ℝ, ℝ)) :
    latticeFrame f - coherentBudget f = 2 * negativeCorrectionMass f := by
  have he (x : ℝ) : |x| - x = 2 * max (-x) 0 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_right (by linarith only [hx])]
      ring
    · rw [abs_of_neg (lt_of_not_ge hx), max_eq_left (by linarith only [hx])]
      ring
  have hs := (summable_transform f abs abs_zero).tsum_sub
    (summable_of_hasFiniteSupport (correctionSample_finite f))
  have hid : correctionMass f - signedCorrectionMass f = 2 * negativeCorrectionMass f := by
    unfold correctionMass signedCorrectionMass negativeCorrectionMass
    rw [← hs]
    simp_rw [he]
    exact tsum_mul_left
  unfold latticeFrame coherentBudget
  linarith only [hid]

theorem coherentBudget_le_latticeFrame (f : C_c(ℝ, ℝ)) : coherentBudget f ≤ latticeFrame f := by
  have h := latticeFrame_sub_coherentBudget f
  have hn := negativeCorrectionMass_nonneg f
  linarith only [h, hn]

/-- A single negative correction gives a strict improvement over the absolute budget. -/
theorem coherentBudget_lt_of_negative_sample (f : C_c(ℝ, ℝ)) (k : ℤ)
    (hk : correctionSample f k < 0) : coherentBudget f < latticeFrame f := by
  have hs := summable_transform f (fun x => max (-x) 0) (by simp)
  have h := hs.le_tsum k (fun _ _ => le_max_right _ _)
  have hm := le_max_left (-correctionSample f k) 0
  have he := latticeFrame_sub_coherentBudget f
  change _ ≤ negativeCorrectionMass f at h
  linarith only [hk, h, hm, he]

/-- Exact gain in the full plastic lower bound, with the collar unchanged. -/
theorem odd_plasticCrossover_ge_cancellation_gain (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * latticeFrame (oddCompactSource f) +
          4 * Real.log 2 * negativeCorrectionMass (oddCompactSource f) ≤
            plasticCrossover (oddCompactSource f) := by
  have h := odd_plasticCrossover_ge_coherentBudget f N
  have he := latticeFrame_sub_coherentBudget (oddCompactSource f)
  have he' := congrArg (fun x : ℝ => Real.log 2 * x) he
  nlinarith only [h, he']

/-- Secondary zero-grid specialization recovers the original variance price exactly. -/
theorem coherentBudget_of_source_zeros (f : C_c(ℝ, ℝ))
    (hz : ∀ m : ℕ, 1 ≤ m → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    coherentBudget f = autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f := by
  have hE := correctionMass_of_source_zeros f hz
  have hs := summable_transform f abs abs_zero
  have he (k : ℤ) : correctionSample f k = 0 := by
    have hk := hs.le_tsum k (fun _ _ => abs_nonneg _)
    change |correctionSample f k| ≤ correctionMass f at hk
    rw [hE] at hk
    exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
  have hn : negativeCorrectionMass f = 0 := by simp [negativeCorrectionMass, he]
  have hg := latticeFrame_sub_coherentBudget f
  rw [hn, mul_zero, latticeFrame_of_source_zeros f hz] at hg
  linarith only [hg]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedCoherentMoment
