import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiGreenIncidenceComparison

/-!
# All-cross-prime Calderón--Witt incidence and its Koszul differential

The earlier completed incidence comparison fixes one ordered pair of
distinct primes.  Its divisor coefficients are faithful, but its
Calderón--Witt source values lie on one fixed Milnor-incidence witness line.

This module retains every ordered cross-prime witness simultaneously.  A
canonical full-support `ℓ²` horizon embeds the completed Xi carrier
isometrically in an `ℓ²` field of cross-prime packets.  The associated
pair-compatibility Koszul differential has kernel exactly that embedded
carrier.  Thus it annihilates the actual completed Green comparison
unconditionally, while the exact kernel computation proves that packet
compatibility alone leaves the full scalar Xi coefficient as residual
cohomology.

No Riemann-hypothesis, zero-location, positivity, or spectral-synthesis
premise occurs.
-/

open Complex Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Ordered pairs of distinct ordinary primes. -/
def DeningerCalderonWittCrossPrimePacketIndex : Type :=
  {pq : Nat.Primes × Nat.Primes // pq.1 ≠ pq.2}

deriving instance Countable for DeningerCalderonWittCrossPrimePacketIndex

noncomputable local instance :
    Encodable DeningerCalderonWittCrossPrimePacketIndex :=
  Encodable.ofCountable _

noncomputable local instance deningerCalderonWittAllCrossPrimeIncidenceKoszulInst1 : DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- Canonical base pair used to contract the packet Koszul complex. -/
def deningerCalderonWittTwoThreePacketIndex :
    DeningerCalderonWittCrossPrimePacketIndex :=
  ⟨(⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩), by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv⟩

/-- Raw full-support coefficient on the countable cross-prime packet. -/
def deningerCalderonWittCrossPrimePacketRawCoefficient
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℂ :=
  ((1 : ℂ) / 2) ^ Encodable.encode i

theorem summable_norm_sq_deningerCalderonWittCrossPrimePacketRawCoefficient :
    Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖deningerCalderonWittCrossPrimePacketRawCoefficient i‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg
      ‖deningerCalderonWittCrossPrimePacketRawCoefficient i‖)
    (fun i => ?_)
    (summable_geometric_two_encode :
      Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        ((1 : ℝ) / 2) ^ Encodable.encode i))
  rw [deningerCalderonWittCrossPrimePacketRawCoefficient,
    norm_pow, norm_div]
  norm_num
  have hnonneg :
      0 ≤ ((1 : ℝ) / 2) ^ Encodable.encode i := by positivity
  have hle :
      ((1 : ℝ) / 2) ^ Encodable.encode i ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-- Unnormalized full-support cross-prime horizon. -/
def deningerCalderonWittCrossPrimePacketRawHorizon :
    lp (fun _ : DeningerCalderonWittCrossPrimePacketIndex => ℂ) 2 :=
  ⟨deningerCalderonWittCrossPrimePacketRawCoefficient, by
    apply memℓp_gen
    simpa using
      summable_norm_sq_deningerCalderonWittCrossPrimePacketRawCoefficient⟩

@[simp]
theorem deningerCalderonWittCrossPrimePacketRawHorizon_apply
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketRawHorizon i =
      deningerCalderonWittCrossPrimePacketRawCoefficient i :=
  rfl

theorem deningerCalderonWittCrossPrimePacketRawCoefficient_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketRawCoefficient i ≠ 0 := by
  exact pow_ne_zero _ (by norm_num)

theorem deningerCalderonWittCrossPrimePacketRawHorizon_ne_zero :
    deningerCalderonWittCrossPrimePacketRawHorizon ≠ 0 := by
  intro h
  have hi := congrFun (congrArg Subtype.val h)
    deningerCalderonWittTwoThreePacketIndex
  exact
    (deningerCalderonWittCrossPrimePacketRawCoefficient_ne_zero
      deningerCalderonWittTwoThreePacketIndex) (by simpa using hi)

/-- Unit-norm, full-support horizon on every ordered cross-prime witness. -/
def deningerCalderonWittCrossPrimePacketHorizon :
    lp (fun _ : DeningerCalderonWittCrossPrimePacketIndex => ℂ) 2 :=
  ((‖deningerCalderonWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹) •
    deningerCalderonWittCrossPrimePacketRawHorizon

@[simp]
theorem deningerCalderonWittCrossPrimePacketHorizon_apply
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketHorizon i =
      ((‖deningerCalderonWittCrossPrimePacketRawHorizon‖ : ℂ)⁻¹) *
        deningerCalderonWittCrossPrimePacketRawCoefficient i := by
  rfl

theorem deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketHorizon i ≠ 0 := by
  rw [deningerCalderonWittCrossPrimePacketHorizon_apply]
  exact mul_ne_zero
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr
        deningerCalderonWittCrossPrimePacketRawHorizon_ne_zero)))
    (deningerCalderonWittCrossPrimePacketRawCoefficient_ne_zero i)

@[simp]
theorem deningerCalderonWittCrossPrimePacketHorizon_norm :
    ‖deningerCalderonWittCrossPrimePacketHorizon‖ = 1 := by
  rw [deningerCalderonWittCrossPrimePacketHorizon, norm_smul]
  have hnorm :
      ‖deningerCalderonWittCrossPrimePacketRawHorizon‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      deningerCalderonWittCrossPrimePacketRawHorizon_ne_zero
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

/-- Hilbert packet retaining all ordered cross-prime labels. -/
abbrev DeningerCalderonWittCrossPrimePacketHilbert : Type :=
  lp (fun _ : DeningerCalderonWittCrossPrimePacketIndex => ℂ) 2

/-- Completed all-divisor, all-cross-prime incidence carrier. -/
abbrev DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion : Type :=
  lp (fun _ : XiZeroCopy => DeningerCalderonWittCrossPrimePacketHilbert) 2

private def deningerCalderonWittAllCrossPrimeXiIncidenceComparisonToFun
    (x : DeningerArithmeticCompletedH1) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  ⟨fun r => x r • deningerCalderonWittCrossPrimePacketHorizon,
    Memℓp.mono (lp.memℓp x).norm (fun r => by
      rw [norm_smul, deningerCalderonWittCrossPrimePacketHorizon_norm]
      simp)⟩

/-- Isometric simultaneous comparison with every cross-prime incidence packet. -/
def deningerCalderonWittAllCrossPrimeXiIncidenceComparison :
    DeningerArithmeticCompletedH1 →ₗᵢ[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion where
  toFun := deningerCalderonWittAllCrossPrimeXiIncidenceComparisonToFun
  map_add' x y := by
    apply lp.ext
    funext r
    exact add_smul _ _ _
  map_smul' c x := by
    apply lp.ext
    funext r
    exact mul_smul _ _ _
  norm_map' x := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun r => by
        change
          ‖x r • deningerCalderonWittCrossPrimePacketHorizon‖ ≤ ‖x r‖
        rw [norm_smul, deningerCalderonWittCrossPrimePacketHorizon_norm]
        simp)
    · exact lp.norm_mono (by norm_num) (fun r => by
        change ‖x r‖ ≤
          ‖(deningerCalderonWittAllCrossPrimeXiIncidenceComparisonToFun x) r‖
        change
          ‖x r‖ ≤ ‖x r • deningerCalderonWittCrossPrimePacketHorizon‖
        rw [norm_smul, deningerCalderonWittCrossPrimePacketHorizon_norm]
        simp)

@[simp]
theorem deningerCalderonWittAllCrossPrimeXiIncidenceComparison_apply
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeXiIncidenceComparison x r i =
      x r * deningerCalderonWittCrossPrimePacketHorizon i :=
  rfl

/-- The actual completed source Green map into the simultaneous
all-cross-prime incidence carrier. -/
def deningerArithmeticCompletedGreenToAllCrossPrimeIncidence :
    DeningerArithmeticTopologicalH1Compact →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  deningerCalderonWittAllCrossPrimeXiIncidenceComparison.toContinuousLinearMap.comp
    deningerArithmeticSourceGreen

@[simp]
theorem deningerArithmeticCompletedGreenToAllCrossPrimeIncidence_apply
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerArithmeticCompletedGreenToAllCrossPrimeIncidence ell =
      deningerCalderonWittAllCrossPrimeXiIncidenceComparison
        (deningerArithmeticSourceGreen ell) :=
  rfl

theorem norm_deningerArithmeticCompletedGreenToAllCrossPrimeIncidence
    (ell : DeningerArithmeticTopologicalH1Compact) :
    ‖deningerArithmeticCompletedGreenToAllCrossPrimeIncidence ell‖ =
      ‖deningerArithmeticSourceGreen ell‖ :=
  deningerCalderonWittAllCrossPrimeXiIncidenceComparison.norm_map _

/-- Actual algebraic Calderón--Witt source value decoded from one packet coordinate. -/
def deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue
    (r : XiZeroCopy) (i : DeningerCalderonWittCrossPrimePacketIndex) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →ₗ[ℂ]
      deningerCalderonWittGlobalMilnorIncidence where
  toFun z := z r i •
    deningerCalderonWittCrossPrimeGammaWitness i.property
  map_add' z w := by simp [add_smul]
  map_smul' c z := by simp [mul_smul]

@[simp]
theorem deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue_comparison
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittAllCrossPrimeXiIncidenceSourceValue r i
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x) =
      (x r * deningerCalderonWittCrossPrimePacketHorizon i) •
        deningerCalderonWittCrossPrimeGammaWitness i.property := by
  rfl

/-! ## Arithmetic faithfulness of the ordered cross-prime packet -/

theorem deningerCalderonWittGlobalDefectCoordinate_lof_packet_zero
    (p s : Nat.Primes) (u : DeningerPrimeFinitePacketGaugeAlgebraic s) :
    deningerCalderonWittGlobalDefectCoordinate p
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne s (0, u)) = 0 := by
  by_cases h : s = p
  · subst s
    simp [deningerCalderonWittGlobalDefectCoordinate,
      deningerCalderonWittLocalDefectCoordinate]
  · simp [deningerCalderonWittGlobalDefectCoordinate,
      DirectSum.component.of, h]

theorem deningerCalderonWittGlobalPacketFirstMode_lof_defect_zero
    (q r : Nat.Primes) (u : DeningerMeyerPrimeCalderonQuotient r) :
    deningerCalderonWittGlobalPacketFirstMode q
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne r (u, 0)) = 0 := by
  by_cases h : r = q
  · subst r
    simp [deningerCalderonWittGlobalPacketFirstMode,
      deningerCalderonWittLocalPacketFirstMode]
  · simp [deningerCalderonWittGlobalPacketFirstMode,
      DirectSum.component.of, h]

theorem deningerCalderonWittGlobalDefectCoordinate_lof_defect_zero_of_ne
    {p r : Nat.Primes} (hpr : p ≠ r)
    (u : DeningerMeyerPrimeCalderonQuotient r) :
    deningerCalderonWittGlobalDefectCoordinate p
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne r (u, 0)) = 0 := by
  simp [deningerCalderonWittGlobalDefectCoordinate,
    DirectSum.component.of, Ne.symm hpr]

theorem deningerCalderonWittGlobalPacketFirstMode_lof_packet_zero_of_ne
    {q s : Nat.Primes} (hqs : q ≠ s)
    (u : DeningerPrimeFinitePacketGaugeAlgebraic s) :
    deningerCalderonWittGlobalPacketFirstMode q
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne s (0, u)) = 0 := by
  simp [deningerCalderonWittGlobalPacketFirstMode,
    DirectSum.component.of, Ne.symm hqs]

/-- An ordered `(p,q)` exterior coordinate kills the actual witness at every
different ordered pair `(r,s)`.  In particular the two orientations of an
unordered prime pair are distinguished, rather than inserted as duplicate
packet labels. -/
theorem deningerCalderonWittWeightedNonlocalExterior_crossPrimeWitness_of_ne
    {p q r s : Nat.Primes} (hrs : r ≠ s)
    (hpair : (p, q) ≠ (r, s)) (c : ℂ) :
    deningerCalderonWittWeightedNonlocalExterior c p q
        (deningerCalderonWittCrossPrimeGammaWitness hrs).1 = 0 := by
  rw [deningerCalderonWittCrossPrimeGammaWitness,
    deningerCalderonWittWeightedNonlocalExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hpr : p = r
  · subst r
    have hqs : q ≠ s := by
      intro h
      exact hpair (by simp [h])
    change c •
      (deningerCalderonWittGlobalDefectCoordinate p
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne p
              (deningerCalderonWittUnitDefect p, 0)) •
          deningerCalderonWittGlobalPacketFirstMode q
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne s
              (0, deningerCalderonWittAlgebraicUnitPacket s)) -
        deningerCalderonWittGlobalDefectCoordinate p
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne s
              (0, deningerCalderonWittAlgebraicUnitPacket s)) •
          deningerCalderonWittGlobalPacketFirstMode q
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne p
              (deningerCalderonWittUnitDefect p, 0))) = 0
    simp [
      deningerCalderonWittGlobalDefectCoordinate_lof_packet_zero,
      deningerCalderonWittGlobalPacketFirstMode_lof_defect_zero,
      deningerCalderonWittGlobalPacketFirstMode_lof_packet_zero_of_ne hqs]
  · change c •
      (deningerCalderonWittGlobalDefectCoordinate p
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne r
              (deningerCalderonWittUnitDefect r, 0)) •
          deningerCalderonWittGlobalPacketFirstMode q
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne s
              (0, deningerCalderonWittAlgebraicUnitPacket s)) -
        deningerCalderonWittGlobalDefectCoordinate p
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne s
              (0, deningerCalderonWittAlgebraicUnitPacket s)) •
          deningerCalderonWittGlobalPacketFirstMode q
            (DirectSum.lof ℂ Nat.Primes
              DeningerCalderonWittAlgebraicDegreeOne r
              (deningerCalderonWittUnitDefect r, 0))) = 0
    simp [
      deningerCalderonWittGlobalDefectCoordinate_lof_packet_zero,
      deningerCalderonWittGlobalPacketFirstMode_lof_defect_zero,
      deningerCalderonWittGlobalDefectCoordinate_lof_defect_zero_of_ne hpr]

theorem
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness_of_ne
    {p q r s : Nat.Primes} (hpq : p ≠ q) (hrs : r ≠ s)
    (hpair : (p, q) ≠ (r, s)) :
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate p q hpq
        (deningerCalderonWittCrossPrimeGammaWitness hrs) = 0 := by
  rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate]
  change _ * deningerCalderonWittAlgebraicCenterTrace q
    (deningerCalderonWittWeightedNonlocalExterior
      (xiGammaEulerPrimitiveModularExterior 0 (p, 0) (q, 0) : ℂ) p q
      (deningerCalderonWittCrossPrimeGammaWitness hrs).1) = 0
  rw [
    deningerCalderonWittWeightedNonlocalExterior_crossPrimeWitness_of_ne
      hrs hpair,
    map_zero, mul_zero]

/-- Normalized arithmetic coordinate belonging to one ordered cross-prime
packet. -/
def deningerCalderonWittCrossPrimePacketCoordinate
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ] ℂ :=
  deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate
    i.1.1 i.1.2 i.2

/-- The normalized arithmetic coordinate matrix on the actual source
witnesses is the infinite identity matrix. -/
theorem deningerCalderonWittCrossPrimePacketCoordinate_witness
    (i j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketCoordinate i
        (deningerCalderonWittCrossPrimeGammaWitness j.2) =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [deningerCalderonWittCrossPrimePacketCoordinate,
      deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness]
  · rw [if_neg h]
    apply
      deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness_of_ne
        i.2 j.2
    intro hpairs
    apply h
    exact Subtype.ext hpairs

/-- Finite arithmetic realization of ordered cross-prime packet coefficients
by actual Calderón--Witt Milnor-incidence witnesses. -/
def deningerCalderonWittCrossPrimeAlgebraicSourceRealization :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ]
      deningerCalderonWittGlobalMilnorIncidence :=
  Finsupp.linearCombination ℂ
    (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      deningerCalderonWittCrossPrimeGammaWitness i.2)

/-- Every finite packet coefficient is recovered exactly from its realized
arithmetic source. -/
theorem deningerCalderonWittCrossPrimePacketCoordinate_sourceRealization
    (i : DeningerCalderonWittCrossPrimePacketIndex)
    (a : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    deningerCalderonWittCrossPrimePacketCoordinate i
        (deningerCalderonWittCrossPrimeAlgebraicSourceRealization a) = a i := by
  rw [deningerCalderonWittCrossPrimeAlgebraicSourceRealization,
    Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  classical
  simp [deningerCalderonWittCrossPrimePacketCoordinate_witness, eq_comm]

theorem deningerCalderonWittCrossPrimeAlgebraicSourceRealization_injective :
    Function.Injective
      deningerCalderonWittCrossPrimeAlgebraicSourceRealization := by
  intro a b hab
  apply Finsupp.ext
  intro i
  rw [
    ← deningerCalderonWittCrossPrimePacketCoordinate_sourceRealization i a,
    ← deningerCalderonWittCrossPrimePacketCoordinate_sourceRealization i b,
    hab]

/-- Actual ordered cross-prime Calderón--Witt witnesses are linearly
independent.  Hence the full packet direction used below is forced by source
arithmetic and does not overcount exterior relations. -/
theorem deningerCalderonWittCrossPrimeGammaWitness_linearIndependent :
    LinearIndependent ℂ
      (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        deningerCalderonWittCrossPrimeGammaWitness i.2) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  exact deningerCalderonWittCrossPrimeAlgebraicSourceRealization_injective

/-- Contracted packet Koszul differential
`z ↦ η(i₀)z - z(i₀)η`. -/
def deningerCalderonWittPacketKoszulDifferential :
    DeningerCalderonWittCrossPrimePacketHilbert →ₗ[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert where
  toFun z :=
    deningerCalderonWittCrossPrimePacketHorizon
        deningerCalderonWittTwoThreePacketIndex • z -
      z deningerCalderonWittTwoThreePacketIndex •
        deningerCalderonWittCrossPrimePacketHorizon
  map_add' z w := by
    apply lp.ext
    funext i
    change
      deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex * (z i + w i) -
          (z deningerCalderonWittTwoThreePacketIndex +
            w deningerCalderonWittTwoThreePacketIndex) *
            deningerCalderonWittCrossPrimePacketHorizon i =
        (deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * z i -
            z deningerCalderonWittTwoThreePacketIndex *
              deningerCalderonWittCrossPrimePacketHorizon i) +
          (deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * w i -
            w deningerCalderonWittTwoThreePacketIndex *
              deningerCalderonWittCrossPrimePacketHorizon i)
    ring
  map_smul' c z := by
    apply lp.ext
    funext i
    change
      deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex * (c * z i) -
          (c * z deningerCalderonWittTwoThreePacketIndex) *
            deningerCalderonWittCrossPrimePacketHorizon i =
        c * (deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex * z i -
            z deningerCalderonWittTwoThreePacketIndex *
              deningerCalderonWittCrossPrimePacketHorizon i)
    ring

@[simp]
theorem deningerCalderonWittPacketKoszulDifferential_apply
    (z : DeningerCalderonWittCrossPrimePacketHilbert)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittPacketKoszulDifferential z i =
      deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex * z i -
        z deningerCalderonWittTwoThreePacketIndex *
          deningerCalderonWittCrossPrimePacketHorizon i :=
  rfl

@[simp]
theorem deningerCalderonWittPacketKoszulDifferential_horizon :
    deningerCalderonWittPacketKoszulDifferential
        deningerCalderonWittCrossPrimePacketHorizon = 0 := by
  apply lp.ext
  funext i
  rw [deningerCalderonWittPacketKoszulDifferential_apply]
  change
    deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex *
        deningerCalderonWittCrossPrimePacketHorizon i -
      deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex *
        deningerCalderonWittCrossPrimePacketHorizon i = 0
  ring

theorem deningerCalderonWittPacketKoszulDifferential_eq_zero_iff
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    deningerCalderonWittPacketKoszulDifferential z = 0 ↔
      ∃ c : ℂ, z = c • deningerCalderonWittCrossPrimePacketHorizon := by
  constructor
  · intro hz
    let i₀ := deningerCalderonWittTwoThreePacketIndex
    let η := deningerCalderonWittCrossPrimePacketHorizon
    have hη : η i₀ ≠ 0 :=
      deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero i₀
    refine ⟨z i₀ / η i₀, ?_⟩
    apply lp.ext
    funext i
    have hi := congrFun (congrArg Subtype.val hz) i
    change η i₀ * z i - z i₀ * η i = 0 at hi
    rw [sub_eq_zero] at hi
    change z i = (z i₀ / η i₀) * η i
    calc
      z i = (z i₀ * η i) / η i₀ := by
        apply (eq_div_iff hη).2
        simpa [mul_comm] using hi
      _ = (z i₀ / η i₀) * η i := by field_simp
  · rintro ⟨c, rfl⟩
    apply lp.ext
    funext i
    rw [deningerCalderonWittPacketKoszulDifferential_apply]
    simp
    ring

/-- Exact local kernel: only the full-support packet horizon survives. -/
theorem ker_deningerCalderonWittPacketKoszulDifferential :
    LinearMap.ker deningerCalderonWittPacketKoszulDifferential =
      LinearMap.range
        (LinearMap.toSpanSingleton ℂ
          DeningerCalderonWittCrossPrimePacketHilbert
          deningerCalderonWittCrossPrimePacketHorizon) := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨c, rfl⟩ :=
      (deningerCalderonWittPacketKoszulDifferential_eq_zero_iff z).mp hz
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    exact
      (deningerCalderonWittPacketKoszulDifferential_eq_zero_iff
        (c • deningerCalderonWittCrossPrimePacketHorizon)).2 ⟨c, rfl⟩

theorem norm_deningerCalderonWittPacketKoszulDifferential_le
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    ‖deningerCalderonWittPacketKoszulDifferential z‖ ≤ 2 * ‖z‖ := by
  rw [deningerCalderonWittPacketKoszulDifferential]
  calc
    ‖deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex • z -
        z deningerCalderonWittTwoThreePacketIndex •
          deningerCalderonWittCrossPrimePacketHorizon‖
        ≤ ‖deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex • z‖ +
            ‖z deningerCalderonWittTwoThreePacketIndex •
              deningerCalderonWittCrossPrimePacketHorizon‖ :=
      norm_sub_le _ _
    _ = ‖deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex‖ * ‖z‖ +
          ‖z deningerCalderonWittTwoThreePacketIndex‖ := by
      rw [norm_smul, norm_smul,
        deningerCalderonWittCrossPrimePacketHorizon_norm, mul_one]
    _ ≤ 2 * ‖z‖ := by
      have hη := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        deningerCalderonWittCrossPrimePacketHorizon
        deningerCalderonWittTwoThreePacketIndex
      have hz := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        z deningerCalderonWittTwoThreePacketIndex
      rw [deningerCalderonWittCrossPrimePacketHorizon_norm] at hη
      nlinarith [norm_nonneg z]

private def deningerCalderonWittGlobalPacketKoszulDifferentialToFun
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  ⟨fun r => deningerCalderonWittPacketKoszulDifferential (z r),
    Memℓp.mono ((lp.memℓp z).norm.const_smul (2 : ℝ)) (fun r => by
      simpa [Pi.smul_apply, smul_eq_mul] using
        norm_deningerCalderonWittPacketKoszulDifferential_le (z r))⟩

/-- Fibrewise bounded packet differential on the completed global carrier. -/
def deningerCalderonWittGlobalPacketKoszulDifferential :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  LinearMap.mkContinuous
    { toFun := deningerCalderonWittGlobalPacketKoszulDifferentialToFun
      map_add' := fun z w => by
        apply lp.ext
        funext r
        exact map_add deningerCalderonWittPacketKoszulDifferential (z r) (w r)
      map_smul' := fun c z => by
        apply lp.ext
        funext r
        exact map_smul deningerCalderonWittPacketKoszulDifferential c (z r) }
    2 (fun z => by
      have hmono :
          ‖deningerCalderonWittGlobalPacketKoszulDifferentialToFun z‖ ≤
            ‖(2 : ℂ) • z‖ :=
        lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun r => by
          change
            ‖deningerCalderonWittPacketKoszulDifferential (z r)‖ ≤
              ‖((2 : ℂ) • z) r‖
          rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]
          norm_num
          exact norm_deningerCalderonWittPacketKoszulDifferential_le (z r))
      rw [norm_smul] at hmono
      norm_num at hmono
      exact hmono)

@[simp]
theorem deningerCalderonWittGlobalPacketKoszulDifferential_apply
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion)
    (r : XiZeroCopy) :
    deningerCalderonWittGlobalPacketKoszulDifferential z r =
      deningerCalderonWittPacketKoszulDifferential (z r) :=
  rfl

/-- The genuine all-cross-prime comparison is an unconditional packet cycle. -/
@[simp]
theorem deningerCalderonWittGlobalPacketKoszulDifferential_comparison
    (x : DeningerArithmeticCompletedH1) :
    deningerCalderonWittGlobalPacketKoszulDifferential
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x) = 0 := by
  apply lp.ext
  funext r
  rw [deningerCalderonWittGlobalPacketKoszulDifferential_apply]
  exact
    (deningerCalderonWittPacketKoszulDifferential_eq_zero_iff
      (x r • deningerCalderonWittCrossPrimePacketHorizon)).2
      ⟨x r, rfl⟩

/-- The actual completed Xi Green comparison is a packet Koszul cycle for
every source primitive, with no zero-location or RH premise. -/
@[simp]
theorem deningerCalderonWittGlobalPacketKoszulDifferential_completedGreen
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerCalderonWittGlobalPacketKoszulDifferential
        (deningerArithmeticCompletedGreenToAllCrossPrimeIncidence ell) = 0 := by
  rw [deningerArithmeticCompletedGreenToAllCrossPrimeIncidence_apply]
  exact
    deningerCalderonWittGlobalPacketKoszulDifferential_comparison
      (deningerArithmeticSourceGreen ell)

private def deningerCalderonWittPacketKoszulResidualCoefficientToFun
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion) :
    DeningerArithmeticCompletedH1 :=
  ⟨fun r =>
      z r deningerCalderonWittTwoThreePacketIndex /
        deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex,
    Memℓp.mono
      ((lp.memℓp z).norm.const_smul
        ‖(deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex)⁻¹‖)
      (fun r => by
        have hr := lp.norm_apply_le_norm
          (by norm_num : (2 : ENNReal) ≠ 0)
          (z r) deningerCalderonWittTwoThreePacketIndex
        simpa [div_eq_mul_inv, norm_mul, Pi.smul_apply, smul_eq_mul,
          mul_comm] using
          mul_le_mul_of_nonneg_right hr
            (norm_nonneg
              (deningerCalderonWittCrossPrimePacketHorizon
                deningerCalderonWittTwoThreePacketIndex)⁻¹))⟩

/-- Residual scalar coefficient after exact packet compatibility. -/
def deningerCalderonWittPacketKoszulResidualCoefficient :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →ₗ[ℂ]
      DeningerArithmeticCompletedH1 where
  toFun := deningerCalderonWittPacketKoszulResidualCoefficientToFun
  map_add' z w := by
    apply lp.ext
    funext r
    change
      (z r deningerCalderonWittTwoThreePacketIndex +
          w r deningerCalderonWittTwoThreePacketIndex) /
          deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex =
        z r deningerCalderonWittTwoThreePacketIndex /
            deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex +
          w r deningerCalderonWittTwoThreePacketIndex /
            deningerCalderonWittCrossPrimePacketHorizon
              deningerCalderonWittTwoThreePacketIndex
    ring
  map_smul' c z := by
    apply lp.ext
    funext r
    change
      (c * z r deningerCalderonWittTwoThreePacketIndex) /
          deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex =
        c * (z r deningerCalderonWittTwoThreePacketIndex /
          deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex)
    ring

@[simp]
theorem deningerCalderonWittPacketKoszulResidualCoefficient_comparison
    (x : DeningerArithmeticCompletedH1) :
    deningerCalderonWittPacketKoszulResidualCoefficient
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x) = x := by
  apply lp.ext
  funext r
  change
    (x r * deningerCalderonWittCrossPrimePacketHorizon
      deningerCalderonWittTwoThreePacketIndex) /
        deningerCalderonWittCrossPrimePacketHorizon
          deningerCalderonWittTwoThreePacketIndex = x r
  exact mul_div_cancel_right₀ (x r)
    (deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero
      deningerCalderonWittTwoThreePacketIndex)

/-- Exact global kernel: packet compatibility leaves precisely the complete Xi coefficient. -/
theorem ker_deningerCalderonWittGlobalPacketKoszulDifferential :
    LinearMap.ker
        deningerCalderonWittGlobalPacketKoszulDifferential.toLinearMap =
      LinearMap.range
        deningerCalderonWittAllCrossPrimeXiIncidenceComparison.toLinearMap := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    refine
      ⟨deningerCalderonWittPacketKoszulResidualCoefficient z, ?_⟩
    apply lp.ext
    funext r
    have hr :
        deningerCalderonWittPacketKoszulDifferential (z r) = 0 := by
      have hcoord := congrFun (congrArg Subtype.val hz) r
      simpa [deningerCalderonWittGlobalPacketKoszulDifferential_apply] using hcoord
    obtain ⟨c, hc⟩ :=
      (deningerCalderonWittPacketKoszulDifferential_eq_zero_iff (z r)).mp hr
    have hη :=
      deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero
        deningerCalderonWittTwoThreePacketIndex
    change
      (z r deningerCalderonWittTwoThreePacketIndex /
          deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) •
          deningerCalderonWittCrossPrimePacketHorizon = z r
    rw [hc]
    apply lp.ext
    funext i
    change
      ((c * deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) /
          deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) *
        deningerCalderonWittCrossPrimePacketHorizon i =
      c * deningerCalderonWittCrossPrimePacketHorizon i
    rw [mul_div_cancel_right₀ c hη]
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact deningerCalderonWittGlobalPacketKoszulDifferential_comparison x

end

end RHTower
