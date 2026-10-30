import GaloisForLFunctions.CompletedArithmeticForms.WeilGreenModes
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapTiltedSplineReserve

/-!
# Finite arithmetic control of every complete Green direction

At fixed positive overlap, finitely many Ramanujan readings control the
entire complete inverse. Its norm on their common orthogonal complement
is arbitrarily small beyond one horizon. The defect reserve supplies the
finite certificate; inverse norm quasimodes pay all its coordinates.
-/

noncomputable section

open Matrix Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

private theorem eventually_inverse_modes_small {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹
          (normalizedRamanujanHorizonVector m N) -
        (completedConductorEnergy tiltedUnitSpline c m)⁻¹ •
          normalizedRamanujanHorizonVector m N‖ ≤ δ := by
  induction S using Finset.induction_on with
  | empty => exact Eventually.of_forall fun _ _ h => False.elim (notMem_empty _ h)
  | @insert m S _ ih =>
      filter_upwards [
        (tendsto_tiltedWeil_inverse_ramanujan_residual_norm hc
          (hS m (mem_insert_self _ _))).eventually (ge_mem_nhds hδ),
        ih (fun k hk => hS k (mem_insert_of_mem hk))] with N hmN hSN
      intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · exact hmN
      · exact hSN k hk

/-- Every direction unread by one finite conductor family has arbitrarily small Green norm. -/
theorem exists_tiltedWeil_inverse_finite_reading_tail {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ v : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (∀ m ∈ S, ⟪v, normalizedRamanujanHorizonVector m N⟫ = 0) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)⁻¹ v‖ ≤ ε * ‖v‖ := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  obtain ⟨S, hS, hcert⟩ :=
    exists_finite_ramanujan_coordinate_certificate_of_reserve hβ hres ε⁻¹
  let δ := ε / (6 * ((S.card : ℝ) + 1))
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hcost : (S.card : ℝ) * δ ^ 2 / ε ^ 2 < 1 / 18 := by
    have heq : (S.card : ℝ) * δ ^ 2 / ε ^ 2 =
        (S.card : ℝ) / (36 * ((S.card : ℝ) + 1) ^ 2) := by
      dsimp only [δ]
      field_simp [hε.ne', show (S.card : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith only [hcard, sq_nonneg (S.card : ℝ)]
  refine ⟨S, hS, ?_⟩
  filter_upwards [hcert, eventually_inverse_modes_small hc hδ S hS,
    eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc] with N hcertN hmode hpos
  intro v horth
  by_contra h
  let A := completeWeilMatrix tiltedUnitSpline c N
  let u := Matrix.toEuclideanLin A⁻¹ v
  have hbig : ε * ‖v‖ < ‖u‖ := lt_of_not_ge h
  have hu : 0 < ‖u‖ := (mul_nonneg hε.le (norm_nonneg v)).trans_lt hbig
  let x := ‖u‖⁻¹ • u
  have hx : ‖x‖ = 1 := by
    dsimp only [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu), inv_mul_cancel₀ hu.ne']
  have hinv : Matrix.toEuclideanLin A u = v := by
    apply PiLp.ext
    change ∀ i, (A *ᵥ (A⁻¹ *ᵥ v)) i = v i
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A
      (isUnit_iff_ne_zero.mpr hpos.det_pos.ne'), one_mulVec]
    exact fun _ => rfl
  have hratio : ‖v‖ / ‖u‖ ≤ ε⁻¹ := by
    rw [div_le_iff₀ hu]
    exact (le_inv_mul_iff₀ hε).mpr hbig.le
  have henergy : completeWeilEnergy tiltedUnitSpline c N x ≤ ε⁻¹ := by
    change ⟪Matrix.toEuclideanLin A x, x⟫ ≤ _
    dsimp only [x]
    rw [map_smul, hinv, real_inner_smul_left, real_inner_smul_right]
    calc
      _ ≤ ‖u‖⁻¹ * (‖u‖⁻¹ * (‖v‖ * ‖u‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (real_inner_le_norm v u) (inv_nonneg.mpr hu.le))
          (inv_nonneg.mpr hu.le)
      _ = ‖v‖ / ‖u‖ := by field_simp
      _ ≤ _ := hratio
  have hmass := hcertN x hx henergy
  have hterm : ∀ m ∈ S,
      ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤ δ ^ 2 / ε ^ 2 := by
    intro m hm
    let r := normalizedRamanujanHorizonVector m N
    let E := completedConductorEnergy tiltedUnitSpline c m
    have hsym : ⟪u, r⟫ = ⟪v, Matrix.toEuclideanLin A⁻¹ r⟫ :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hpos.inv.isHermitian) v r
    have he : ⟪u, r⟫ = ⟪v, Matrix.toEuclideanLin A⁻¹ r - E⁻¹ • r⟫ := by
      rw [inner_sub_right, real_inner_smul_right, horth m hm, mul_zero, sub_zero, hsym]
    have hb : |⟪x, r⟫| ≤ δ / ε := by
      dsimp only [x]
      rw [real_inner_smul_left]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hu), he]
      calc
        _ ≤ ‖u‖⁻¹ * (‖v‖ * ‖Matrix.toEuclideanLin A⁻¹ r - E⁻¹ • r‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_nonneg.mpr hu.le)
        _ ≤ ‖u‖⁻¹ * (‖v‖ * δ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hmode m hm) (norm_nonneg v)) (inv_nonneg.mpr hu.le)
        _ = δ * (‖v‖ / ‖u‖) := by ring
        _ ≤ δ * ε⁻¹ := mul_le_mul_of_nonneg_left hratio hδ.le
        _ = _ := by rw [div_eq_mul_inv]
    have hb2 := mul_self_le_mul_self (abs_nonneg _) hb
    simpa only [← sq, sq_abs, div_pow] using hb2
  have hsum := sum_le_sum hterm
  simp only [sum_const, nsmul_eq_mul, ← mul_div_assoc] at hsum
  linarith only [hmass, hsum, hcost]

#print axioms exists_tiltedWeil_inverse_finite_reading_tail

end GaloisForLFunctions.CompletedArithmeticForms
