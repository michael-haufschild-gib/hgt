import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver

/-!
# Logarithm rigidity at the Route-T zero-reserve boundary

The moving derivative reserve can vanish only when the erase-complement has zero logarithmic
length. Earlier classification left the distinguished long atom as “zeta or logarithm.” That is
not sharp: every nonzero Heath--Brown box has positive exponent on its unique logarithm atom. If
that atom remained in a zero-mass complement, its exponent would be forced to zero. Therefore the
distinguished atom is exactly the logarithm atom, and the whole unsigned box core is its single
dyadic logarithm Dirichlet polynomial.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Zero complement mass and a nonzero log atom force the distinguished index to be the unique
logarithm index. -/
theorem distinguished_eq_logIndex_of_complement_mass_zero
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hlog : 1 ≤ box.q) (hT : 1 < T)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0) :
    j = Sum.inr (Sum.inr ()) := by
  classical
  let logIndex : HeathBrownBoxFactorIndex k box.m :=
    Sum.inr (Sum.inr ())
  by_contra hj
  have hmem : logIndex ∈ (Finset.univ.erase j) :=
    Finset.mem_erase.mpr ⟨fun h => hj h.symm, Finset.mem_univ logIndex⟩
  have hexp :=
    heathBrownBox_complement_factorExponent_eq_zero_of_mass_eq_zero
      box j hT hzero logIndex hmem
  change box.q = 0 at hexp
  omega

/-- Kind-level form of zero-reserve logarithm rigidity. -/
theorem distinguished_kind_eq_log_of_complement_mass_zero
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hlog : 1 ≤ box.q) (hT : 1 < T)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0) :
    heathBrownBoxFactorKind k box.m j = .log := by
  rw [distinguished_eq_logIndex_of_complement_mass_zero
    box j hlog hT hzero]
  rfl

/-- **Exact zero-reserve core classification.** The full unsigned box core is one dyadic
logarithm Dirichlet polynomial; every other factor is the multiplicative unit. -/
theorem heathBrownDyadicCoreProduct_eq_logFactor_of_complement_mass_zero
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hlog : 1 ≤ box.q)
    (hT : 1 < T)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0)
    (s : ℂ) :
    heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s =
      LSeries (complexCoeff (arithmeticDyadicBlock
        (coeffTrunc ArithmeticFunction.log X) box.q)) s := by
  classical
  let z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X k box s i
  have hfull : (∏ i, z i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
    simpa [z, heathBrownBoxFactorValue] using
      heathBrownBoxFactorProduct_eq_core L X k box.m box.a box.b box.q s
  have herase : z j * ∏ i ∈ (Finset.univ.erase j), z i = ∏ i, z i :=
    Finset.mul_prod_erase Finset.univ z (Finset.mem_univ j)
  have hcomp :
      (∏ i : {i : HeathBrownBoxFactorIndex k box.m //
          i ∈ (Finset.univ.erase j)},
        LSeries (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m i))
          (heathBrownBoxFactorExponent box.a box.b box.q i))) s) = 1 :=
    heathBrownBox_complement_value_eq_one_of_mass_eq_zero
      box j hL hX hlog hT hzero s
  have heraseOne : ∏ i ∈ (Finset.univ.erase j), z i = 1 := by
    rw [← Finset.prod_attach]
    simpa [z, heathBrownBoxFactorValue] using hcomp
  have hj := distinguished_eq_logIndex_of_complement_mass_zero
    box j hlog hT hzero
  rw [← hfull, ← herase, heraseOne, mul_one, hj]
  rfl

end RHTower.Sieve
