/-
# Subpolynomial parabola triple fibers

The first two moments of a parabola triple determine an integral
representation by `u² + 3v²`.  The Eisenstein divisor bound therefore gives
the sharp subpolynomial bound for every nonempty moment fiber.

This is the arithmetic core of the discrete planar `L⁶` estimate: the loss is
`H^ε`, rather than the elementary linear loss.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinDivisorBound

open scoped BigOperators

namespace RHTower

open BourgainEisensteinInt

noncomputable section

/-- A scalar Eisenstein norm raised to `ε / 4` is controlled by `H^ε` when
the scalar is at most `18H²`. -/
theorem eisensteinNorm_natCast_rpow_quarter_le
    {ε : ℝ} (hε : 0 ≤ ε) {H K : ℕ}
    (hKH : (K : ℝ) ≤ 18 * (H : ℝ) ^ (2 : ℕ)) :
    (norm (K : BourgainEisensteinInt) : ℝ) ^ (ε / 4) ≤
      (18 : ℝ) ^ (ε / 2) * (H : ℝ) ^ ε := by
  have hKnonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hHnonneg : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hexp : 0 ≤ ε / 2 := by linarith
  calc
    (norm (K : BourgainEisensteinInt) : ℝ) ^ (ε / 4) =
        ((K : ℝ) ^ (2 : ℕ)) ^ (ε / 4) := by
      rw [norm_natCast]
      norm_cast
    _ = (((K : ℝ) ^ (2 : ℝ)) ^ (ε / 4)) := by
      congr 1
      exact (Real.rpow_natCast (K : ℝ) 2).symm
    _ = (K : ℝ) ^ ((2 : ℝ) * (ε / 4)) :=
      (Real.rpow_mul hKnonneg 2 (ε / 4)).symm
    _ = (K : ℝ) ^ (ε / 2) := by ring_nf
    _ ≤ (18 * (H : ℝ) ^ (2 : ℕ)) ^ (ε / 2) :=
      Real.rpow_le_rpow hKnonneg hKH hexp
    _ = (18 : ℝ) ^ (ε / 2) *
        ((H : ℝ) ^ (2 : ℕ)) ^ (ε / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18)
        (sq_nonneg (H : ℝ))]
    _ = (18 : ℝ) ^ (ε / 2) *
        (((H : ℝ) ^ (2 : ℝ)) ^ (ε / 2)) := by
      congr 1
      congr 1
      exact (Real.rpow_natCast (H : ℝ) 2).symm
    _ = (18 : ℝ) ^ (ε / 2) *
        (H : ℝ) ^ ((2 : ℝ) * (ε / 2)) := by
      rw [Real.rpow_mul hHnonneg 2 (ε / 2)]
    _ = (18 : ℝ) ^ (ε / 2) * (H : ℝ) ^ ε := by
      ring_nf

/-- Bounded representations of an attained parabola moment pair have
subpolynomial cardinality. -/
theorem card_bourgainParabolaRepresentationFinset_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (y : ℕ × ℕ),
        y ∈ (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment →
        ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤
          C * (H : ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hdivisor⟩ :=
    card_eisensteinDivisors_le_const_mul_rpow
      (show 0 < ε / 4 by linarith)
  let D : ℝ := C₀ * (18 : ℝ) ^ (ε / 2)
  refine ⟨1 + D, ?_, ?_⟩
  · have hpow : 0 < (18 : ℝ) ^ (ε / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    dsimp [D]
    positivity
  · intro H y hy
    obtain ⟨h, -, hmoment⟩ := Finset.mem_image.mp hy
    have hH : 1 ≤ H := by
      have := (h 0).isLt
      omega
    have hdiscNonneg : 0 ≤ bourgainParabolaDiscriminant y := by
      rw [← hmoment]
      exact bourgainParabolaDiscriminant_nonneg h
    have hdiscUpper :
        bourgainParabolaDiscriminant y ≤
          18 * (H : ℤ) ^ (2 : ℕ) := by
      rw [← hmoment]
      exact bourgainParabolaDiscriminant_le h
    by_cases hdiscZero : bourgainParabolaDiscriminant y = 0
    · have hcardNat :=
        card_bourgainParabolaRepresentationFinset_le_one_of_discriminant_zero
          H y hdiscZero
      have hcard :
          ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤ 1 := by
        exact_mod_cast hcardNat
      have hHpow : (1 : ℝ) ≤ (H : ℝ) ^ ε :=
        Real.one_le_rpow (by exact_mod_cast hH) hε.le
      have hDnonneg : 0 ≤ D := by
        dsimp [D]
        positivity
      calc
        ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤ 1 :=
          hcard
        _ ≤ (1 + D) * (H : ℝ) ^ ε := by
          nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ H by positivity) ε]
    · have hdiscPos : 0 < bourgainParabolaDiscriminant y :=
        lt_of_le_of_ne hdiscNonneg (Ne.symm hdiscZero)
      let K : ℕ := (bourgainParabolaDiscriminant y).natAbs
      have hK : K ≠ 0 :=
        Int.natAbs_ne_zero.mpr (ne_of_gt hdiscPos)
      have hKz :
          (K : ℤ) ≤ 18 * (H : ℤ) ^ (2 : ℕ) := by
        simpa [K, Int.natAbs_of_nonneg hdiscNonneg] using hdiscUpper
      have hKr :
          (K : ℝ) ≤ 18 * (H : ℝ) ^ (2 : ℕ) := by
        exact_mod_cast hKz
      have hnormBound :
          (norm (K : BourgainEisensteinInt) : ℝ) ^ (ε / 4) ≤
            (18 : ℝ) ^ (ε / 2) * (H : ℝ) ^ ε :=
        eisensteinNorm_natCast_rpow_quarter_le hε.le hKr
      have hcardNat :=
        card_bourgainParabolaRepresentationFinset_le_eisensteinDivisors
          H y hdiscPos
      have hcard :
          ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤
            (@Fintype.card
              {z : BourgainEisensteinInt // z ∣ (K : BourgainEisensteinInt)}
              (UniqueFactorizationMonoid.fintypeSubtypeDvd
                (K : BourgainEisensteinInt)
                (eisenstein_natCast_ne_zero hK)) : ℝ) := by
        simpa [K] using (show
          ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤
            (@Fintype.card
              {z : BourgainEisensteinInt //
                z ∣ ((bourgainParabolaDiscriminant y).natAbs :
                  BourgainEisensteinInt)}
              (UniqueFactorizationMonoid.fintypeSubtypeDvd
                ((bourgainParabolaDiscriminant y).natAbs :
                  BourgainEisensteinInt)
                (eisenstein_natCast_ne_zero
                  (Int.natAbs_ne_zero.mpr
                    (ne_of_gt hdiscPos)))) : ℝ) by
          exact_mod_cast hcardNat)
      have hdivisorK :=
        hdivisor (K : BourgainEisensteinInt)
          (eisenstein_natCast_ne_zero hK)
      have hC₀nonneg : 0 ≤ C₀ := hC₀.le
      have hDnonneg : 0 ≤ D := by
        dsimp [D]
        positivity
      calc
        ((bourgainParabolaRepresentationFinset H y).card : ℝ) ≤
            (@Fintype.card
              {z : BourgainEisensteinInt // z ∣ (K : BourgainEisensteinInt)}
              (UniqueFactorizationMonoid.fintypeSubtypeDvd
                (K : BourgainEisensteinInt)
                (eisenstein_natCast_ne_zero hK)) : ℝ) := hcard
        _ ≤ C₀ *
            (norm (K : BourgainEisensteinInt) : ℝ) ^ (ε / 4) :=
          hdivisorK
        _ ≤ C₀ * ((18 : ℝ) ^ (ε / 2) * (H : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hnormBound hC₀nonneg
        _ = D * (H : ℝ) ^ ε := by
          simp only [D]
          ring
        _ ≤ (1 + D) * (H : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (show (0 : ℝ) ≤ H by positivity) ε)

/-- Every attained `(Σn,Σn²)` fiber has cardinality `Oε(H^ε)`. -/
theorem card_bourgainParabolaTripleMoment_fiber_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (y : ℕ × ℕ),
        y ∈ (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment →
        (((Finset.univ : Finset (Fin 3 → Fin H)).filter
          fun h => bourgainParabolaTripleMoment h = y).card : ℝ) ≤
            C * (H : ℝ) ^ ε := by
  obtain ⟨C, hC, hrepresentation⟩ :=
    card_bourgainParabolaRepresentationFinset_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H y hy
  calc
    (((Finset.univ : Finset (Fin 3 → Fin H)).filter
        fun h => bourgainParabolaTripleMoment h = y).card : ℝ) ≤
        ((bourgainParabolaRepresentationFinset H y).card : ℝ) := by
      exact_mod_cast
        card_bourgainParabolaTripleMoment_fiber_le_representation H y
    _ ≤ C * (H : ℝ) ^ ε := hrepresentation H y hy

/-- Weighted discrete planar `L⁶` fiber estimate with only an `H^ε` loss. -/
theorem bourgainParabolaFiberL2_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        ∑ y ∈
            (Finset.univ : Finset (Fin 3 → Fin H)).image
              bourgainParabolaTripleMoment,
          ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
              (fun h => bourgainParabolaTripleMoment h = y),
            bourgainTripleWeight a h‖ ^ (2 : ℕ) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hfiber⟩ :=
    card_bourgainParabolaTripleMoment_fiber_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a
  exact bourgainParabolaFiberL2_le H a (hfiber H)

end

end RHTower
