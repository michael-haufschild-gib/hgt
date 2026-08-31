import GaloisForLFunctions.HTGeometry.FreeToricIsogenyTail
import GaloisForLFunctions.HTGeometry.ToricDiagonalExpandingTail

/-!
# Unconditional partially expanding diagonal split-torus tail

A positive diagonal torus isogeny has two intrinsic sectors: degree-one coordinates are
reversible quotient positions, while coordinates of degree at least two lose position and retain
only logarithmic velocity.  This file identifies the stable tail with exactly those two sectors.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

/-- Positive diagonal matrices are nonsingular, including degree-one reversible coordinates. -/
theorem det_diagonalPowerMatrix_ne_zero_of_pos {r : ℕ} {D : Fin r → ℕ}
    (hD : ∀ i, 0 < D i) : (diagonalPowerMatrix r D).det ≠ 0 := by
  rw [diagonalPowerMatrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Int.natCast_ne_zero.mpr (Nat.ne_of_gt (hD i))

/-- The position--velocity field: all logarithmic velocities together with exactly the
degree-one quotient positions. -/
def torusDiagonalPositionVelocityField
    (C : Type u) [Field C] {E : Type u} [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    {r : ℕ} (x : Fin r → E) (D : Fin r → ℕ) :
    IntermediateField (↥(torusVelocityField C x)) E :=
  IntermediateField.adjoin (↥(torusVelocityField C x))
    (Set.range fun i : {i : Fin r // D i = 1} => x i.1)

/-- Every iterated diagonal deck transformation fixes a degree-one coordinate. -/
theorem eq_one_of_mem_erasedSector_const_diagonal_degree_one
    {C : Type u} [Field C] {r : ℕ} {D : Fin r → ℕ}
    {u : Fin r → Cˣ}
    (hu : u ∈ erasedSector
      (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0)
    {i : Fin r} (hi : D i = 1) : u i = 1 := by
  rw [mem_erasedSector_iff] at hu
  obtain ⟨n, hn⟩ := hu
  rw [prefixHom_torusProtocolGroup,
    prefixMatrix_const_diagonalPowerMatrix D 0 n,
    torusMonomialHom_diagonal] at hn
  have hni := congrFun hn i
  change (u i) ^ ((((D i) ^ n : ℕ) : ℤ)) = 1 at hni
  simpa [hi] using hni

/-- The annihilating characters of a positive diagonal isogeny's full iterated deck sector are
exactly the integer exponent vectors supported on degree-one coordinates. -/
theorem mem_scaleAnnihilator_erasedSector_const_diagonal_iff
    {C : Type u} [Field C] [IsAlgClosed C] [CharZero C]
    {r : ℕ} {D : Fin r → ℕ} (hD : ∀ i, 0 < D i) (a : Fin r → ℤ) :
    a ∈ scaleAnnihilator C
        (erasedSector (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0) ↔
      ∀ i, 2 ≤ D i → a i = 0 := by
  constructor
  · intro ha i hi
    by_contra hai
    let B : ℕ := (a i).natAbs
    have hBpos : 0 < B := Int.natAbs_pos.mpr hai
    have hpow : 2 ^ B ≤ (D i) ^ B := Nat.pow_le_pow_left hi B
    have hlt : B < (D i) ^ B := (Nat.lt_two_pow_self).trans_le hpow
    set N : ℕ := (D i) ^ B with hN
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlt
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosed C hNpos
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hNpos.ne'
    set u : Fin r → Cˣ := fun k => if k = i then Units.mk0 ζ hζ0 else 1 with hu
    have hmemker :
        u ∈ (torusPowerHom C (fun k : Fin r => (((D k) ^ B : ℕ) : ℤ))).ker := by
      rw [mem_ker_torusPowerHom_iff]
      intro k
      by_cases hk : k = i
      · subst k
        apply Units.ext
        simp only [hu, if_pos rfl, Units.val_one, zpow_natCast]
        exact hζ.pow_eq_one
      · simp [hu, if_neg hk]
    have hmem : u ∈ erasedSector
        (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0 := by
      rw [mem_erasedSector_iff]
      refine ⟨B, ?_⟩
      rw [prefixHom_torusProtocolGroup,
        prefixMatrix_const_diagonalPowerMatrix D 0 B, torusMonomialHom_diagonal]
      exact hmemker
    have hchar := ha u hmem
    have hprod : (∏ k, ((u k : C)) ^ (a k)) = ζ ^ (a i) := by
      rw [Finset.prod_eq_single i]
      · simp [hu]
      · intro k _ hki
        simp [hu, hki]
      · intro hi'
        exact absurd (Finset.mem_univ i) hi'
    rw [hprod] at hchar
    have hdivInt : (N : ℤ) ∣ a i := (hζ.zpow_eq_one_iff_dvd (a i)).mp hchar
    have hdivNat : N ∣ B := by
      have h := Int.natAbs_dvd_natAbs.mpr hdivInt
      simpa [B] using h
    exact (not_lt_of_ge (Nat.le_of_dvd hBpos hdivNat)) hlt
  · intro ha u hu
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : D i = 1
    · simp [eq_one_of_mem_erasedSector_const_diagonal_degree_one hu hi]
    · have hi2 : 2 ≤ D i := by
        have := hD i
        omega
      rw [ha i hi2, zpow_zero]

/-- The invariant-monomial description is exactly quotient position plus Maurer--Cartan velocity
for every positive diagonal torus isogeny. -/
theorem torusInvariantMonomialField_erasedSector_const_diagonal_eq_positionVelocity
    {C E : Type u} [Field C] [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    [CharZero E] [CharZero C] [IsAlgClosed C]
    {r : ℕ} {x : Fin r → E} {D : Fin r → ℕ} (hD : ∀ i, 0 < D i) :
    torusInvariantMonomialField C x
        (erasedSector (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0) =
      torusDiagonalPositionVelocityField C x D := by
  apply le_antisymm
  · rw [torusInvariantMonomialField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hsupport :=
      (mem_scaleAnnihilator_erasedSector_const_diagonal_iff hD a).mp ha
    rw [laurentMonomial]
    refine prod_mem fun i _ => ?_
    by_cases hi : D i = 1
    · have hmem : x i ∈ Set.range
          (fun j : {j : Fin r // D j = 1} => x j.1) :=
        ⟨⟨i, hi⟩, rfl⟩
      exact zpow_mem (IntermediateField.subset_adjoin _ _ hmem) (a i)
    · have hi2 : 2 ≤ D i := by
        have := hD i
        omega
      rw [hsupport i hi2, zpow_zero]
      exact one_mem _
  · rw [torusDiagonalPositionVelocityField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    let a : Fin r → ℤ := fun k => if k = i.1 then 1 else 0
    have ha : a ∈ scaleAnnihilator C
        (erasedSector (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0) := by
      rw [mem_scaleAnnihilator_erasedSector_const_diagonal_iff hD]
      intro k hk
      simp only [a]
      split_ifs with hki
      · subst k
        omega
      · rfl
    refine IntermediateField.subset_adjoin _ _ ⟨a, ha, ?_⟩
    rw [laurentMonomial, Finset.prod_eq_single i.1]
    · simp [a]
    · intro k _ hki
      simp [a, hki]
    · intro hi
      exact absurd (Finset.mem_univ i.1) hi

section Tail

variable {C E : Type u} [Field C] [Field E] [Algebra C E]
  [Differential C] [Differential E] [DifferentialAlgebra C E]
  [CharZero E] [CharZero C] [IsAlgClosed C]
  {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

/-- Stable tail of every positive diagonal split-torus isogeny is its quotient-position and
Maurer--Cartan-velocity field. -/
theorem torusDiagonalEndo_stableRangeCore_eq_positionVelocity
    (hconst : ∀ c : C, c′ = 0) {D : Fin r → ℕ} (hD : ∀ i, 0 < D i) :
    stableRangeCore
        (torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero_of_pos hD)) =
      (torusDiagonalPositionVelocityField C x D).restrictScalars C := by
  rw [torusEndo_stableRangeCore_eq_torusInvariantMonomialField hx hgen hconst
    (det_diagonalPowerMatrix_ne_zero_of_pos hD)]
  rw [torusInvariantMonomialField_erasedSector_const_diagonal_eq_positionVelocity hD]

omit [CharZero C] [IsAlgClosed C] in
/-- Every logarithmic velocity has the expected diagonal weight, including weight one on the
reversible sector. -/
theorem torusPositiveDiagonalEndo_logDeriv
    {D : Fin r → ℕ} (hD : ∀ i, 0 < D i) (i : Fin r) :
    torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero_of_pos hD)
        (Differential.logDeriv (x i)) =
      (D i : E) * Differential.logDeriv (x i) := by
  rw [torusEndo_logDeriv hx hgen (det_diagonalPowerMatrix_ne_zero_of_pos hD) i]
  rw [Finset.sum_eq_single i]
  · rw [diagonalPowerMatrix, Matrix.diagonal_apply_eq]
    norm_cast
  · intro j _ hji
    rw [diagonalPowerMatrix, Matrix.diagonal_apply_ne _ (Ne.symm hji)]
    norm_num
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [CharZero C] [IsAlgClosed C] in
/-- Degree-one quotient positions are fixed pointwise by the isogeny. -/
theorem torusPositiveDiagonalEndo_fixedPosition
    {D : Fin r → ℕ} (hD : ∀ i, 0 < D i) {i : Fin r} (hi : D i = 1) :
    torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero_of_pos hD) (x i) = x i := by
  rw [torusEndo_apply, diagonalPowerMatrix, monomialFamily_diagonal_apply, hi]
  norm_num

end Tail

local instance freePartialDiagonalComplexDifferential : Differential ℂ := ⟨0⟩

local instance freePartialDiagonalDifferentialAlgebra (r : ℕ) :
    DifferentialAlgebra ℂ (JetField ℂ (Fin r)) := by
  refine ⟨fun z => ?_⟩
  rw [JetField.deriv_algebraMap z]
  exact (map_zero _).symm

/-- **Unconditional position--velocity law for positive diagonal split-torus isogenies.**
For every finite rank and every positive coordinate degree, the stable tail contains exactly all
logarithmic velocities and the degree-one quotient positions.  Velocities remain differentially
independent, carry no rational position, transform with their exact weights, and all quotient
positions are fixed.  Positivity, genericity, generation, and constant-field structure are
constructed rather than assumed. -/
theorem freeToricPositiveDiagonalIsogenyTail
    (r : ℕ) (D : Fin r → {n : ℕ // 0 < n}) :
    let x := freeTorusGenerator r
    let d : Fin r → ℕ := fun i => (D i).1
    let hd : ∀ i, 0 < d i := fun i => (D i).2
    stableRangeCore
        (torusEndo (differentialIndependent_freeTorusGenerator r)
          (differentialAdjoin_freeTorusGenerator_eq_top r)
          (det_diagonalPowerMatrix_ne_zero_of_pos hd)) =
        (torusDiagonalPositionVelocityField ℂ x d).restrictScalars ℂ
      ∧ DifferentialIndependent ℂ (fun i => Differential.logDeriv (x i))
      ∧ torusVelocityField ℂ x ⊓ IntermediateField.adjoin ℂ (Set.range x) =
          (⊥ : IntermediateField ℂ (JetField ℂ (Fin r)))
      ∧ (∀ i, torusEndo (differentialIndependent_freeTorusGenerator r)
            (differentialAdjoin_freeTorusGenerator_eq_top r)
            (det_diagonalPowerMatrix_ne_zero_of_pos hd)
            (Differential.logDeriv (x i)) =
          (d i : JetField ℂ (Fin r)) * Differential.logDeriv (x i))
      ∧ (∀ i, d i = 1 →
          torusEndo (differentialIndependent_freeTorusGenerator r)
            (differentialAdjoin_freeTorusGenerator_eq_top r)
            (det_diagonalPowerMatrix_ne_zero_of_pos hd) (x i) = x i) := by
  dsimp only
  refine ⟨torusDiagonalEndo_stableRangeCore_eq_positionVelocity
      (differentialIndependent_freeTorusGenerator r)
      (differentialAdjoin_freeTorusGenerator_eq_top r)
      deriv_complex_eq_zero (fun i => (D i).2),
    differentialIndependent_logDeriv (differentialIndependent_freeTorusGenerator r),
    torusVelocityField_inf_adjoin_eq_bot
      (differentialIndependent_freeTorusGenerator r)
      (differentialAdjoin_freeTorusGenerator_eq_top r) deriv_complex_eq_zero,
    torusPositiveDiagonalEndo_logDeriv
      (differentialIndependent_freeTorusGenerator r)
      (differentialAdjoin_freeTorusGenerator_eq_top r) (fun i => (D i).2),
    fun i hi => torusPositiveDiagonalEndo_fixedPosition
      (differentialIndependent_freeTorusGenerator r)
      (differentialAdjoin_freeTorusGenerator_eq_top r) (fun i => (D i).2) hi⟩

end

end GaloisForLFunctions.HTGeometry
