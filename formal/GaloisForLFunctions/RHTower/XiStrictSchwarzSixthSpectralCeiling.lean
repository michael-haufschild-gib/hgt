import GaloisForLFunctions.RHTower.PrimeIndexedRVMSignedReflectionCandidate
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction

/-!
# Strict sixth spectral ceiling from an infinite Schwarz divisor

The non-strict sixth spectral ceiling loses the finite-head margin needed by K-RVM.  An infinite
positive divisor has a third atom outside every conjugate pair, making the pair budget strict.
Combined with the same Holder argument, this gives a source-only strict ceiling.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- A strictly positive conjugation-invariant summable weight on an infinite Xi divisor has
strictly more total mass than either Schwarz pair. -/
theorem two_mul_lt_tsum_of_conj_invariant
    {f : XiZeroCopy → ℝ} [Infinite XiZeroCopy]
    (hpos : ∀ r, 0 < f r) (hsum : Summable f)
    (hCinv : ∀ r, f (xiZeroCopyConjEquiv r) = f r) (q : XiZeroCopy) :
    2 * f q < ∑' r, f r := by
  classical
  let qC := xiZeroCopyConjEquiv q
  let t : Finset XiZeroCopy := {q, qC}
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset t
  let s : Finset XiZeroCopy := insert r t
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hle := hsum.sum_le_tsum s (fun x _ => (hpos x).le)
  have hC : f qC = f q := by
    simpa only [qC] using hCinv q
  have hfinite : ∑ x ∈ s, f x = 2 * f q + f r := by
    simp only [s, Finset.sum_insert hr, t]
    rw [Finset.sum_insert (by simp [hqC]), Finset.sum_singleton, hC]
    ring
  rw [hfinite] at hle
  nlinarith [hpos r]

/-- Strict Holder ceiling for any positive Xi-divisor spectral coordinates satisfying the
atomwise sector law. -/
theorem strict_sixth_spectral_ceiling_of_schwarz_atoms
    {a b : XiZeroCopy → ℝ} [Infinite XiZeroCopy]
    (ha : ∀ q, 0 < a q) (hb : ∀ q, 0 < b q)
    (hab : ∀ q, b q ^ 2 ≤ a q ^ 3)
    (hsa : Summable a) (hsa2 : Summable (fun q => a q ^ 2))
    (hainv : ∀ q, a (xiZeroCopyConjEquiv q) = a q) :
    2 * (∑' q, b q) ^ 2 < (∑' q, a q) ^ 3 := by
  let c : XiZeroCopy → ℝ := fun q => b q ^ 2 / a q
  have hpair : ∀ q, 2 * a q < ∑' r, a r := by
    intro q
    exact two_mul_lt_tsum_of_conj_invariant ha hsa hainv q
  have hc : ∀ q, 0 ≤ c q := fun q =>
    div_nonneg (sq_nonneg _) (ha q).le
  have hca2 : ∀ q, c q ≤ a q ^ 2 := by
    intro q
    dsimp only [c]
    apply (div_le_iff₀ (ha q)).2
    nlinarith [hab q]
  have hsc : Summable c :=
    Summable.of_nonneg_of_le hc hca2 hsa2
  have hsqrt : ∀ q, Real.sqrt (a q) * Real.sqrt (c q) = b q := by
    intro q
    have hsqa : Real.sqrt (a q) ^ 2 = a q :=
      Real.sq_sqrt (ha q).le
    have hsqc : Real.sqrt (c q) ^ 2 = c q :=
      Real.sq_sqrt (hc q)
    have hsq :
        (Real.sqrt (a q) * Real.sqrt (c q)) ^ 2 = (b q) ^ 2 := by
      rw [show (Real.sqrt (a q) * Real.sqrt (c q)) ^ 2 =
          Real.sqrt (a q) ^ 2 * Real.sqrt (c q) ^ 2 by ring,
        hsqa, hsqc]
      dsimp only [c]
      field_simp [(ha q).ne']
    exact (sq_eq_sq₀
      (mul_nonneg (Real.sqrt_nonneg (a q)) (Real.sqrt_nonneg (c q)))
      (hb q).le).mp hsq
  have hsqa : Summable (fun q => Real.sqrt (a q) ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, Real.sq_sqrt (ha _).le] using hsa
  have hsqc : Summable (fun q => Real.sqrt (c q) ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, Real.sq_sqrt (hc _)] using hsc
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
      (fun q => Real.sqrt_nonneg (a q))
      (fun q => Real.sqrt_nonneg (c q))
      hsqa hsqc
  have hsum_sqrt :
      (∑' q, b q) = ∑' q, Real.sqrt (a q) * Real.sqrt (c q) := by
    apply tsum_congr
    intro q
    exact (hsqrt q).symm
  have hsum_sq_a :
      (∑' q, Real.sqrt (a q) ^ 2) = ∑' q, a q := by
    apply tsum_congr
    intro q
    exact Real.sq_sqrt (ha q).le
  have hsum_sq_c :
      (∑' q, Real.sqrt (c q) ^ 2) = ∑' q, c q := by
    apply tsum_congr
    intro q
    exact Real.sq_sqrt (hc q)
  have hsum_sq_a_rpow :
      (∑' q, Real.sqrt (a q) ^ (2 : ℝ)) = ∑' q, a q := by
    simpa only [Real.rpow_two] using hsum_sq_a
  have hsum_sq_c_rpow :
      (∑' q, Real.sqrt (c q) ^ (2 : ℝ)) = ∑' q, c q := by
    simpa only [Real.rpow_two] using hsum_sq_c
  have hholderBound :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        (∑' i : XiZeroCopy, Real.sqrt (a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑' i : XiZeroCopy, Real.sqrt (c i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hholder.2
  have hholderReduced :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        (∑' i : XiZeroCopy, a i) ^ (1 / 2 : ℝ) *
          (∑' i : XiZeroCopy, c i) ^ (1 / 2 : ℝ) := by
    calc
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
          (∑' i : XiZeroCopy, Real.sqrt (a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∑' i : XiZeroCopy, Real.sqrt (c i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholderBound
      _ = (∑' i : XiZeroCopy, a i) ^ (1 / 2 : ℝ) *
            (∑' i : XiZeroCopy, c i) ^ (1 / 2 : ℝ) := by
        rw [hsum_sq_a_rpow, hsum_sq_c_rpow]
  have hholderBound' :
      ∑' i : XiZeroCopy, Real.sqrt (a i) * Real.sqrt (c i) ≤
        Real.sqrt (∑' i : XiZeroCopy, a i) *
          Real.sqrt (∑' i : XiZeroCopy, c i) := by
    simpa only [Real.sqrt_eq_rpow] using hholderReduced
  have hBC :
      ∑' q, b q ≤ Real.sqrt (∑' q, a q) * Real.sqrt (∑' q, c q) := by
    rw [hsum_sqrt]
    exact hholderBound'
  have hA : 0 ≤ ∑' q, a q := tsum_nonneg fun q => (ha q).le
  have hB : 0 ≤ ∑' q, b q := tsum_nonneg fun q => (hb q).le
  have hC : 0 ≤ ∑' q, c q := tsum_nonneg hc
  have hBCsq :
      (∑' q, b q) ^ 2 ≤ (∑' q, a q) * ∑' q, c q := by
    have hsA : Real.sqrt (∑' q, a q) ^ 2 = ∑' q, a q :=
      Real.sq_sqrt hA
    have hsC : Real.sqrt (∑' q, c q) ^ 2 = ∑' q, c q :=
      Real.sq_sqrt hC
    nlinarith [Real.sqrt_nonneg (∑' q, a q), Real.sqrt_nonneg (∑' q, c q)]
  have hCsq : ∑' q, c q ≤ ∑' q, a q ^ 2 :=
    hsc.tsum_le_tsum hca2 hsa2
  have hsa2scale : Summable (fun q => 2 * a q ^ 2) :=
    (hsa2.hasSum.mul_left 2).summable
  have hsascale : Summable (fun q => (∑' r, a r) * a q) :=
    (hsa.hasSum.mul_left (∑' r, a r)).summable
  let q0 : XiZeroCopy := Classical.choice (inferInstance : Nonempty XiZeroCopy)
  have hApos : 0 < ∑' q, a q := by
    exact (mul_pos (by norm_num) (ha q0)).trans (hpair q0)
  have hA2 :
      2 * ∑' q, a q ^ 2 < (∑' q, a q) ^ 2 := by
    calc
      2 * ∑' q, a q ^ 2 = ∑' q, 2 * a q ^ 2 := by
        rw [hsa2.tsum_mul_left]
      _ < ∑' q, (∑' r, a r) * a q := by
        apply hsa2scale.tsum_lt_tsum (i := q0)
        · intro q
          convert mul_le_mul_of_nonneg_right (hpair q).le (ha q).le using 1
          ring
        · convert mul_lt_mul_of_pos_right (hpair q0) (ha q0) using 1
          ring
        · exact hsascale
      _ = (∑' q, a q) ^ 2 := by
        rw [hsa.tsum_mul_left]
        ring
  calc
    2 * (∑' q, b q) ^ 2 ≤
        2 * ((∑' q, a q) * ∑' q, c q) :=
      mul_le_mul_of_nonneg_left hBCsq (by norm_num)
    _ ≤ 2 * ((∑' q, a q) * ∑' q, a q ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hCsq hA) (by norm_num)
    _ = (∑' q, a q) * (2 * ∑' q, a q ^ 2) := by ring
    _ < (∑' q, a q) * (∑' q, a q) ^ 2 :=
      mul_lt_mul_of_pos_left hA2 hApos
    _ = (∑' q, a q) ^ 3 := by ring

/-- The actual prime--archimedean moments have a strict sixth spectral ceiling, without RH. -/
theorem normalizedPrimeArchMoment_strict_sixth_spectral_ceiling :
    2 * normalizedPrimeArchMoment 2 ^ 2 < normalizedPrimeArchMoment 1 ^ 3 := by
  let a : XiZeroCopy → ℝ := fun q => (xiZeroCopyReciprocalSquare q ^ 2).re
  let b : XiZeroCopy → ℝ := fun q => (xiZeroCopyReciprocalSquare q ^ 3).re
  have ha : ∀ q, 0 < a q := fun q => by
    exact xiZeroCopyReciprocalSquare_sq_re_pos_of_thermal_sector q
  have hb : ∀ q, 0 < b q := fun q => by
    exact xiZeroCopyReciprocalSquare_cube_re_pos q
  have hab : ∀ q, b q ^ 2 ≤ a q ^ 3 := fun q => by
    exact xiZeroCopyReciprocalSquare_cube_re_sq_le_sq_re_cube q
  have hsa : Summable a := by
    change Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q ^ 2).re)
    exact Complex.reCLM.summable (summable_xiZeroCopyReciprocalSquare_pow 1)
  have hsa2 : Summable (fun q => a q ^ 2) := by
    apply Summable.of_norm_bounded
      (summable_xiZeroCopyReciprocalSquare_pow 3).norm
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      a q ^ 2 ≤ ‖xiZeroCopyReciprocalSquare q ^ 2‖ ^ 2 := by
        exact (sq_le_sq₀ (ha q).le (norm_nonneg _)).mpr
          (Complex.re_le_norm _)
      _ = ‖xiZeroCopyReciprocalSquare q ^ 4‖ := by
        rw [norm_pow, norm_pow]
        ring
  have hainv : ∀ q, a (xiZeroCopyConjEquiv q) = a q := by
    intro q
    change (xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re
    rw [xiZeroCopyReciprocalSquare_conjEquiv]
    have hpow :
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q ^ 2) =
          ((starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)) ^ 2 :=
      map_pow (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) 2
    rw [← hpow, Complex.conj_re]
  have hstrict := strict_sixth_spectral_ceiling_of_schwarz_atoms
    ha hb hab hsa hsa2 hainv
  have hMone : normalizedPrimeArchMoment 1 = ∑' q, a q := by
    change normalizedPrimeArchMoment 1 =
      ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 2).re
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
      ← tsum_xiZeroCopyReciprocalSquare_pow 1,
      Complex.re_tsum (summable_xiZeroCopyReciprocalSquare_pow 1)]
  have hMtwo : normalizedPrimeArchMoment 2 = ∑' q, b q := by
    change normalizedPrimeArchMoment 2 =
      ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 3).re
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
      ← tsum_xiZeroCopyReciprocalSquare_pow 2,
      Complex.re_tsum (summable_xiZeroCopyReciprocalSquare_pow 2)]
  rw [hMone, hMtwo]
  exact hstrict

end

end RHTower
