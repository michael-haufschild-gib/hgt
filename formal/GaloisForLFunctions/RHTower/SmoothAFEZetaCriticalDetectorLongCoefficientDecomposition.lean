import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongRangeSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionDivisorReindex

/-!
# Full-minus-omitted decomposition of long Levinson coefficients

Beyond the finite detector head, the exact product-fibre coefficient is the full differentiated
Barban--Vehov divisor coefficient minus precisely the divisors omitted by the head cutoff.
-/

noncomputable section

namespace RHTower

open Complex Finset

theorem Sieve.finCoeffNat_levinsonCriticalDetectorHeadCoeff
    (lam : ℝ) (L n : ℕ) :
    Sieve.finCoeffNat L
        (fun j : Fin L => Sieve.levinsonCriticalDetectorHeadCoeff lam ((j : ℕ) + 1)) n =
      if 1 ≤ n ∧ n ≤ L then Sieve.levinsonCriticalDetectorHeadCoeff lam n else 0 := by
  rw [Sieve.finCoeffNat]
  split_ifs with h
  · change Sieve.levinsonCriticalDetectorHeadCoeff lam (n - 1 + 1) = _
    rw [Nat.sub_add_cancel h.1]
  · rfl

/-- Exact contribution omitted by truncating the unsmoothed detector head at `L`. -/
def levinsonCriticalDetectorOmittedHeadCoeff
    (lam : ℝ) (L M k : ℕ) : ℂ :=
  ∑ d ∈ k.divisors.filter (fun d => L < d),
    Sieve.levinsonCriticalDetectorHeadCoeff lam d *
      Sieve.levinsonLinearMollifierCoeff M (k / d)

/-- The full differentiated Barban--Vehov coefficient in the complementary-divisor orientation. -/
theorem levinsonLinearMollifiedCriticalDetectorCoeff_eq_headDivisorSum
    (lam : ℝ) (M k : ℕ) :
    Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k =
      ∑ d ∈ k.divisors,
        Sieve.levinsonCriticalDetectorHeadCoeff lam d *
          Sieve.levinsonLinearMollifierCoeff M (k / d) := by
  rw [Sieve.levinsonLinearMollifiedCriticalDetectorCoeff]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun d q => Sieve.levinsonCriticalDetectorHeadCoeff lam d *
      Sieve.levinsonLinearMollifierCoeff M q)]
  exact (Nat.sum_divisorsAntidiagonal'
    (fun d q => Sieve.levinsonCriticalDetectorHeadCoeff lam d *
      Sieve.levinsonLinearMollifierCoeff M q)).symm

/-- Every finite product coefficient is the full coefficient minus the exact omitted head tail. -/
theorem levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    levinsonCriticalDetectorMollifiedFinCoeff lam L M r =
      Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1) -
        levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1) := by
  classical
  let K : ℕ := (r : ℕ) + 1
  have hK : 0 < K := by dsimp only [K]; omega
  have hterm : ∀ d ∈ K.divisors,
      Sieve.finCoeffNat L
          (fun j : Fin L => Sieve.levinsonCriticalDetectorHeadCoeff lam ((j : ℕ) + 1)) d *
        Sieve.finCoeffNat M (levinsonLinearMollifierFinCoeff M) (K / d) =
      if d ≤ L then
        Sieve.levinsonCriticalDetectorHeadCoeff lam d *
          Sieve.levinsonLinearMollifierCoeff M (K / d)
      else 0 := by
    intro d hd
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hd
    have hqpos : 1 ≤ K / d :=
      Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    rw [Sieve.finCoeffNat_levinsonCriticalDetectorHeadCoeff,
      Sieve.finCoeffNat_levinsonLinearMollifierFinCoeff_of_pos M hqpos]
    by_cases hdL : d ≤ L
    · rw [if_pos ⟨hdpos, hdL⟩, if_pos hdL]
    · rw [if_neg (fun h => hdL h.2), if_neg hdL, zero_mul]
  have hfinite :
      levinsonCriticalDetectorMollifiedFinCoeff lam L M r =
        ∑ d ∈ K.divisors.filter (fun d => d ≤ L),
          Sieve.levinsonCriticalDetectorHeadCoeff lam d *
            Sieve.levinsonLinearMollifierCoeff M (K / d) := by
    rw [levinsonCriticalDetectorMollifiedFinCoeff,
      Sieve.dirConv_eq_sum_divisors_finCoeffNat]
    rw [show ((r : ℕ) + 1) = K by rfl]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_filter]
  rw [hfinite,
    levinsonLinearMollifiedCriticalDetectorCoeff_eq_headDivisorSum,
    levinsonCriticalDetectorOmittedHeadCoeff]
  rw [show ((r : ℕ) + 1) = K by rfl]
  rw [← Finset.sum_filter_add_sum_filter_not K.divisors (fun d => d ≤ L)
    (fun d => Sieve.levinsonCriticalDetectorHeadCoeff lam d *
      Sieve.levinsonLinearMollifierCoeff M (K / d))]
  simp only [not_le]
  ring

/-- Full differentiated Barban--Vehov energy on product indices beyond the detector head. -/
def levinsonCriticalDetectorFullLongEnergy
    (lam : ℝ) (L M : ℕ) : ℝ :=
  ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
      (fun r : Fin (L * M) => L < (r : ℕ) + 1),
    ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1)‖ ^ 2

/-- Energy of the exact head divisors omitted on long product indices. -/
def levinsonCriticalDetectorOmittedLongEnergy
    (lam : ℝ) (L M : ℕ) : ℝ :=
  ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
      (fun r : Fin (L * M) => L < (r : ℕ) + 1),
    ‖levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1)‖ ^ 2

theorem levinsonCriticalDetectorFullLongEnergy_nonneg
    (lam : ℝ) (L M : ℕ) :
    0 ≤ levinsonCriticalDetectorFullLongEnergy lam L M := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem levinsonCriticalDetectorOmittedLongEnergy_nonneg
    (lam : ℝ) (L M : ℕ) :
    0 ≤ levinsonCriticalDetectorOmittedLongEnergy lam L M := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Reindex a filtered positive successor range as the natural interval `(L,N]`. -/
theorem Sieve.sum_fin_filter_succ_gt_eq_sum_Ioc
    {R : Type*} [AddCommMonoid R] (N L : ℕ) (f : ℕ → R) :
    ∑ r ∈ (Finset.univ : Finset (Fin N)).filter
        (fun r : Fin N => L < (r : ℕ) + 1), f ((r : ℕ) + 1) =
      ∑ k ∈ Finset.Ioc L N, f k := by
  classical
  let s := (Finset.univ : Finset (Fin N)).filter
    (fun r : Fin N => L < (r : ℕ) + 1)
  have himage : s.image (fun r : Fin N => (r : ℕ) + 1) = Finset.Ioc L N := by
    ext k
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨hr, r.isLt⟩
    · intro hk
      refine ⟨⟨k - 1, by omega⟩, ?_, by simp; omega⟩
      dsimp
      omega
  rw [← himage]
  exact (Finset.sum_image (fun x _ y _ hxy => Fin.ext (by omega))).symm

/-- The full long energy in standard positive-natural interval form. -/
theorem levinsonCriticalDetectorFullLongEnergy_eq_sum_Ioc
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorFullLongEnergy lam L M =
      ∑ k ∈ Finset.Ioc L (L * M),
        ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ 2 := by
  exact Sieve.sum_fin_filter_succ_gt_eq_sum_Ioc (L * M) L
    (fun k => ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ 2)

/-- The omitted-head long energy in standard positive-natural interval form. -/
theorem levinsonCriticalDetectorOmittedLongEnergy_eq_sum_Ioc
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorOmittedLongEnergy lam L M =
      ∑ k ∈ Finset.Ioc L (L * M),
        ‖levinsonCriticalDetectorOmittedHeadCoeff lam L M k‖ ^ 2 := by
  exact Sieve.sum_fin_filter_succ_gt_eq_sum_Ioc (L * M) L
    (fun k => ‖levinsonCriticalDetectorOmittedHeadCoeff lam L M k‖ ^ 2)

/-- Arithmetic quadratic-form normal form of the full differentiated Barban--Vehov long energy. -/
theorem levinsonCriticalDetectorFullLongEnergy_eq_arithmetic
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorFullLongEnergy lam L M =
      ∑ k ∈ Finset.Ioc L (L * M),
        (((1 - lam * Real.log k) * Sieve.barbanVehovCoeff M k +
              lam * Sieve.barbanVehovLogMomentCoeff M k) /
            Real.log M * (1 / Real.sqrt k)) ^ 2 := by
  rw [levinsonCriticalDetectorFullLongEnergy_eq_sum_Ioc]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [Sieve.levinsonLinearMollifiedCriticalDetectorCoeff_eq hkpos]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs]

/-- Exact long energy is reduced to two independent arithmetic tails: the full differentiated
Barban--Vehov coefficient and the omitted-head boundary coefficient. -/
theorem levinsonCriticalDetectorLongEnergy_le_two_mul_full_add_omitted
    (lam : ℝ) (L M : ℕ) :
    levinsonCriticalDetectorLongEnergy lam L M ≤
      2 * levinsonCriticalDetectorFullLongEnergy lam L M +
        2 * levinsonCriticalDetectorOmittedLongEnergy lam L M := by
  classical
  unfold levinsonCriticalDetectorLongEnergy levinsonCriticalDetectorFiniteEnergyTerm
  unfold levinsonCriticalDetectorFullLongEnergy
  unfold levinsonCriticalDetectorOmittedLongEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  rw [levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted]
  rw [← Complex.sq_norm]
  have hnorm := norm_sub_le
    (Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1))
    (levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1))
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [norm_nonneg
      (Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1)),
    norm_nonneg (levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1)),
    sq_nonneg
      (‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1)‖ -
        ‖levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1)‖)]

end RHTower
