import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorDiagonalEnergy
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorDirConv

/-!
# Exact short/long product split of the critical-detector diagonal

The complete product-range diagonal separates into the already-evaluated Barban--Vehov energy on
indices at most the detector length and one explicit nonnegative long-range tail.
-/

noncomputable section

namespace RHTower

open Complex Finset

/-- Exact unsmoothed detector/mollifier coefficient square at one product index. -/
def levinsonCriticalDetectorFiniteEnergyTerm
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) : ℝ :=
  Complex.normSq (levinsonCriticalDetectorMollifiedFinCoeff lam L M r)

/-- Long product-range energy beyond the detector head. -/
def levinsonCriticalDetectorLongEnergy
    (lam : ℝ) (L M : ℕ) : ℝ :=
  ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
      (fun r : Fin (L * M) => L < (r : ℕ) + 1),
    levinsonCriticalDetectorFiniteEnergyTerm lam L M r

private theorem sum_fin_succ_eq_sum_Icc_generic
    {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → R) :
    ∑ n : Fin N, f ((n : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
  classical
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]

/-- The first `L` product indices of the finite convolution are exactly the positive-natural
Barban--Vehov detector coefficients. -/
theorem sum_levinsonCriticalDetectorFiniteEnergyTerm_short_eq
    (lam : ℝ) (L M : ℕ) (hM : 1 ≤ M) :
    ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
        (fun r : Fin (L * M) => (r : ℕ) + 1 ≤ L),
      levinsonCriticalDetectorFiniteEnergyTerm lam L M r =
      ∑ k ∈ Finset.Icc 1 L,
        ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ) := by
  classical
  have hLprod : L ≤ L * M := by
    simpa using Nat.mul_le_mul_left L hM
  let cast : Fin L → Fin (L * M) := Fin.castLE hLprod
  have hfilter :
      (Finset.univ : Finset (Fin (L * M))).filter
          (fun r : Fin (L * M) => (r : ℕ) + 1 ≤ L) =
        (Finset.univ : Finset (Fin L)).image cast := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      let n : Fin L := ⟨(r : ℕ), by omega⟩
      refine ⟨n, ?_⟩
      apply Fin.ext
      rfl
    · rintro ⟨n, rfl⟩
      change (n : ℕ) + 1 ≤ L
      omega
  rw [hfilter]
  rw [Finset.sum_image]
  · rw [show (∑ n : Fin L,
          levinsonCriticalDetectorFiniteEnergyTerm lam L M (cast n)) =
        ∑ n : Fin L,
          ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff
            lam M ((n : ℕ) + 1)‖ ^ (2 : ℕ) by
      apply Finset.sum_congr rfl
      intro n hn
      unfold levinsonCriticalDetectorFiniteEnergyTerm
      rw [levinsonCriticalDetectorMollifiedFinCoeff]
      rw [Sieve.dirConv_levinsonCriticalDetectorHead_eq]
      · have hcastval : (cast n : ℕ) = (n : ℕ) := by rfl
        rw [hcastval, Complex.sq_norm]
      · change (n : ℕ) + 1 ≤ L
        omega]
    exact sum_fin_succ_eq_sum_Icc_generic L (fun k =>
      ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ))
  · intro x hx y hy hxy
    apply Fin.ext
    simpa [cast] using congrArg Fin.val hxy

/-- The complete finite convolution energy is the evaluated short range plus the literal
nonnegative long range. -/
theorem sum_levinsonCriticalDetectorFiniteEnergyTerm_eq_short_add_long
    (lam : ℝ) (L M : ℕ) (hM : 1 ≤ M) :
    ∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r =
      (∑ k ∈ Finset.Icc 1 L,
        ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ)) +
      levinsonCriticalDetectorLongEnergy lam L M := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (L * M)))
    (fun r : Fin (L * M) => (r : ℕ) + 1 ≤ L)
    (levinsonCriticalDetectorFiniteEnergyTerm lam L M)]
  rw [sum_levinsonCriticalDetectorFiniteEnergyTerm_short_eq lam L M hM]
  congr 1
  simp only [levinsonCriticalDetectorLongEnergy, not_le]

/-- Exact critical-detector diagonal as the known short energy plus one nonnegative tail. -/
theorem mollifiedTwistedDiagonalIcc_levinsonCriticalDetector_zero_eq_short_add_long
    (lam : ℝ) (L M : ℕ) (hM : 1 ≤ M) :
    Sieve.mollifiedTwistedDiagonalIcc
        (Sieve.levinsonCriticalDetectorHeadCoeff lam)
        (Sieve.levinsonCriticalDetectorHeadCoeff lam)
        (Sieve.levinsonLinearMollifierCoeff M)
        (Sieve.levinsonLinearMollifierCoeff M) L M 0 =
      (((∑ k ∈ Finset.Icc 1 L,
          ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ)) +
        levinsonCriticalDetectorLongEnergy lam L M : ℝ) : ℂ) := by
  rw [mollifiedTwistedDiagonalIcc_levinsonCriticalDetector_zero_eq_energy]
  rw [← Complex.ofReal_sum]
  change ((∑ r : Fin (L * M),
    levinsonCriticalDetectorFiniteEnergyTerm lam L M r : ℝ) : ℂ) = _
  rw [sum_levinsonCriticalDetectorFiniteEnergyTerm_eq_short_add_long lam L M hM]

/-- The isolated long-range energy is nonnegative. -/
theorem levinsonCriticalDetectorLongEnergy_nonneg
    (lam : ℝ) (L M : ℕ) :
    0 ≤ levinsonCriticalDetectorLongEnergy lam L M := by
  unfold levinsonCriticalDetectorLongEnergy levinsonCriticalDetectorFiniteEnergyTerm
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end RHTower
