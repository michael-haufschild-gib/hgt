import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPrimeRotationResolution
import GaloisForLFunctions.RHTower.PrimeRotationMarkedXiSource
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The arithmetic rotation relation and the marked Xi source

The actual centered flow matrix on a full singleton Xi jet packet is
triangular, so its relation determinant retains the complete multiplicity.
Pullback through the prime Mellin coordinate gives a literal determinant
germ whose ratio with Xi has order zero and a nonzero limit. Its native
clock K2 symbol agrees with the actual Xi clock correction, and with an
isolated Xi dipole, in the marked tame quotient. The concrete quantum
multiplier has the inverse native-clock orientation.

This proves the source comparison. It does not construct a topological
transgression or identify a Chern pairing with this degree.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

/-- All jets of one actual Xi zero, enumerated without truncating its multiplicity. -/
def deningerMeyerSingleXiSlot (rho : XiDivisorSupport) :
    Fin (xiSupportMultiplicity rho) ≃ DeningerMeyerFiniteXiJetSlot {rho} where
  toFun k := ⟨⟨rho, Finset.mem_singleton_self rho⟩, k⟩
  invFun q := by
    have h : q.1.1 = rho := Finset.mem_singleton.mp q.1.2
    exact ⟨q.2.val, by simpa only [h] using q.2.isLt⟩
  left_inv k := rfl
  right_inv q := by
    rcases q with ⟨⟨s, hs⟩, k⟩
    have h : s = rho := Finset.mem_singleton.mp hs
    subst s
    rfl

/-- Matrix of the literal centered Meyer flow on the full singleton Xi packet. -/
def deningerMeyerSingleXiFlowMatrix (rho : XiDivisorSupport) (c : ℝ) :
    Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho)) ℂ :=
  fun i j => deningerMeyerFiniteXiJetPacketCenteredFlow {rho} c
    (Pi.single (deningerMeyerSingleXiSlot rho j) 1) (deningerMeyerSingleXiSlot rho i)

private theorem singleton_jet_ne (rho : XiDivisorSupport)
    (i j : Fin (xiSupportMultiplicity rho)) (r : ℕ) (h : i.val - r ≠ j.val) :
    (⟨⟨rho, Finset.mem_singleton_self rho⟩,
      ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩⟩ : DeningerMeyerFiniteXiJetSlot {rho}) ≠
      deningerMeyerSingleXiSlot rho j := by
  intro he
  exact h (congrArg (fun q : DeningerMeyerFiniteXiJetSlot {rho} => q.2.val) he)

/-- No higher jet contributes to a lower jet. -/
theorem deningerMeyerSingleXiFlowMatrix_lower (rho : XiDivisorSupport) (c : ℝ)
    (i j : Fin (xiSupportMultiplicity rho)) (hij : i < j) :
    deningerMeyerSingleXiFlowMatrix rho c i j = 0 := by
  unfold deningerMeyerSingleXiFlowMatrix
  rw [deningerMeyerFiniteXiJetPacketCenteredFlow_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  have hne := singleton_jet_ne rho i j r (by have := hij; omega)
  change (i.val.choose r : ℂ) * (c : ℂ) ^ r * Complex.exp ((c : ℂ) * (rho : ℂ)) *
    ((Pi.single (deningerMeyerSingleXiSlot rho j) 1 : DeningerMeyerFiniteXiJetPacket {rho})
      ⟨⟨rho, Finset.mem_singleton_self rho⟩,
        ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩⟩) = 0
  rw [Pi.single_apply, if_neg hne, mul_zero]

/-- The full nilpotent jet block has the centered exponential on every diagonal entry. -/
theorem deningerMeyerSingleXiFlowMatrix_diag (rho : XiDivisorSupport) (c : ℝ)
    (i : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerSingleXiFlowMatrix rho c i i = Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) := by
  unfold deningerMeyerSingleXiFlowMatrix
  rw [deningerMeyerFiniteXiJetPacketCenteredFlow_apply, Finset.sum_eq_single 0]
  · simp only [deningerMeyerSingleXiSlot, Equiv.coe_fn_mk, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, pow_zero, one_mul, mul_one, Pi.single_eq_same]
    rw [← Complex.exp_add]
    congr 1
    ring
  · intro r hr hr0
    have hrle : r ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hne := singleton_jet_ne rho i i r (by omega)
    change (i.val.choose r : ℂ) * (c : ℂ) ^ r * Complex.exp ((c : ℂ) * (rho : ℂ)) *
      ((Pi.single (deningerMeyerSingleXiSlot rho i) 1 : DeningerMeyerFiniteXiJetPacket {rho})
        ⟨⟨rho, Finset.mem_singleton_self rho⟩,
          ⟨i.val - r, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩⟩) = 0
    rw [Pi.single_apply, if_neg hne, mul_zero]
  · simp

/-- The determinant comes from the actual entire jet block, including its nilpotent part. -/
theorem deningerMeyerSingleXiFlowMatrix_pencil_det (rho : XiDivisorSupport) (c : ℝ) (z : ℂ) :
    (Matrix.scalar (Fin (xiSupportMultiplicity rho)) z - deningerMeyerSingleXiFlowMatrix rho c).det =
      (z - Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2))) ^ xiSupportMultiplicity rho := by
  have htri : (Matrix.scalar (Fin (xiSupportMultiplicity rho)) z -
      deningerMeyerSingleXiFlowMatrix rho c).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    rw [Matrix.sub_apply, deningerMeyerSingleXiFlowMatrix_lower rho c i j hij',
      Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij'.ne, sub_zero]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    deningerMeyerSingleXiFlowMatrix_diag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- This is the coefficient matrix of the already proved arithmetic free resolution. -/
theorem deningerMeyerXiClockRelation_singleton (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport)
    (C : DeningerMeyerFiniteXiJetSlot {rho} →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (i : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerXiClockRelation p q {rho} C (deningerMeyerSingleXiSlot rho i) =
      C (deningerMeyerSingleXiSlot rho i) *
        paperRotationPolynomialWord (paperPrimeRotationFrequency p (q + 1)) 0 1 -
      ∑ j : Fin (xiSupportMultiplicity rho),
        deningerMeyerSingleXiFlowMatrix rho (-Real.log p) i j • C (deningerMeyerSingleXiSlot rho j) := by
  have hT : deningerMeyerXiPacketPrimeIntegerFlow p {rho} (Multiplicative.ofAdd 1) =
      deningerMeyerFiniteXiJetPacketCenteredFlow {rho} (-Real.log p) := by
    simp [deningerMeyerXiPacketPrimeIntegerFlow]
  simp only [deningerMeyerXiClockRelation, rotationInducedFreeRelation,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_repr, Pi.basisFun_apply]

  rw [hT]
  congr 1
  exact (deningerMeyerSingleXiSlot rho).sum_comp _ |>.symm

/-- The literal centered prime character of the Mellin coordinate. -/
def deningerMeyerPrimeMellinCoordinate (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-((Real.log p : ℝ) : ℂ) * (s - 1 / 2))

/-- Pullback of the actual full-jet relation determinant to the original Mellin coordinate. -/
def deningerMeyerXiRelationDeterminant (p : Nat.Primes) (rho : XiDivisorSupport) (s : ℂ) : ℂ :=
  (Matrix.scalar (Fin (xiSupportMultiplicity rho)) (deningerMeyerPrimeMellinCoordinate p s) -
    deningerMeyerSingleXiFlowMatrix rho (-Real.log p)).det

theorem deningerMeyerXiRelationDeterminant_eq_power (p : Nat.Primes)
    (rho : XiDivisorSupport) (s : ℂ) :
    deningerMeyerXiRelationDeterminant p rho s =
      (deningerMeyerPrimeMellinCoordinate p s - deningerMeyerPrimeMellinCoordinate p rho) ^
        xiSupportMultiplicity rho := by
  rw [deningerMeyerXiRelationDeterminant, deningerMeyerSingleXiFlowMatrix_pencil_det]
  simp only [deningerMeyerPrimeMellinCoordinate, Complex.ofReal_neg]

private theorem primeCoordinateCentered_analytic (p : Nat.Primes) (rho : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z)) 0 := by
  unfold deningerMeyerPrimeMellinCoordinate
  fun_prop

private theorem primeCoordinateCentered_deriv_ne_zero (p : Nat.Primes) (rho : ℂ) :
    deriv (fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z)) 0 ≠ 0 := by
  have hd := ((((hasDerivAt_id (0 : ℂ)).const_add rho).sub_const (1 / 2)).const_mul
    (-((Real.log p : ℝ) : ℂ))).cexp
  have hl : (Real.log p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast p.property.one_lt))
  rw [show deriv (fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z)) 0 =
    Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho - 1 / 2)) * (-((Real.log p : ℝ) : ℂ)) by
      simpa only [deningerMeyerPrimeMellinCoordinate, id_eq, add_zero, mul_one] using hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (neg_ne_zero.mpr (by exact_mod_cast hl))

private theorem relationDeterminantCentered_analytic (p : Nat.Primes) (rho : XiDivisorSupport) :
    AnalyticAt ℂ (fun z : ℂ => deningerMeyerXiRelationDeterminant p rho (rho + z)) 0 := by
  simp only [deningerMeyerXiRelationDeterminant_eq_power]
  exact ((primeCoordinateCentered_analytic p rho).sub analyticAt_const).pow _

/-- Local order is the complete arithmetic jet multiplicity, proved from the relation matrix. -/
theorem deningerMeyerXiRelationDeterminant_centered_order (p : Nat.Primes) (rho : XiDivisorSupport) :
    meromorphicOrderAt (fun z : ℂ => deningerMeyerXiRelationDeterminant p rho (rho + z)) 0 =
      (xiSupportMultiplicity rho : ℤ) := by
  have h1 : analyticOrderAt
      (fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z) -
        deningerMeyerPrimeMellinCoordinate p rho) 0 = 1 := by
    simpa only [add_zero] using (primeCoordinateCentered_analytic p rho).analyticOrderAt_sub_eq_one_of_deriv_ne_zero (primeCoordinateCentered_deriv_ne_zero p rho)
  have hn : analyticOrderAt (fun z : ℂ => deningerMeyerXiRelationDeterminant p rho (rho + z)) 0 =
      (xiSupportMultiplicity rho : ℕ∞) := by
    simp only [deningerMeyerXiRelationDeterminant_eq_power]
    change analyticOrderAt ((fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z) -
      deningerMeyerPrimeMellinCoordinate p rho) ^ xiSupportMultiplicity rho) 0 = _
    have ha : AnalyticAt ℂ (fun z : ℂ => deningerMeyerPrimeMellinCoordinate p (rho + z) -
        deningerMeyerPrimeMellinCoordinate p rho) 0 :=
      (primeCoordinateCentered_analytic p rho).sub analyticAt_const
    rw [analyticOrderAt_pow ha, h1]
    simp
  rw [(relationDeterminantCentered_analytic p rho).meromorphicOrderAt_eq, hn]
  rfl

/-- The germ is formed from the actual relation determinant, not from a declared order. -/
def deningerMeyerXiRelationGerm (p : Nat.Primes) (rho : XiDivisorSupport) : MeroGermˣ :=
  meroGermUnitOf (fun z => deningerMeyerXiRelationDeterminant p rho (rho + z))
    (relationDeterminantCentered_analytic p rho).meromorphicAt
    (by rw [deningerMeyerXiRelationDeterminant_centered_order]; exact WithTop.coe_ne_top)

theorem deningerMeyerXiRelationGerm_order (p : Nat.Primes) (rho : XiDivisorSupport) :
    meroGermUnitOrder (deningerMeyerXiRelationGerm p rho) = (xiSupportMultiplicity rho : ℤ) := by
  apply WithTop.coe_injective
  rw [deningerMeyerXiRelationGerm, meroGermUnitOf_order,
    deningerMeyerXiRelationDeterminant_centered_order]

/-- The determinant and the literal Xi germ differ by an actual order-zero germ. -/
theorem deningerMeyerXiRelationGerm_ratio_order (p : Nat.Primes) (rho : XiDivisorSupport) :
    meroGermUnitOrder (deningerMeyerXiRelationGerm p rho / xiMeroGermUnit rho) = 0 := by
  change Multiplicative.toAdd (meroGermVal (deningerMeyerXiRelationGerm p rho / xiMeroGermUnit rho)) = 0
  rw [map_div, toAdd_div]
  change meroGermUnitOrder (deningerMeyerXiRelationGerm p rho) -
    meroGermUnitOrder (xiMeroGermUnit rho) = 0
  rw [deningerMeyerXiRelationGerm_order, xiMeroGermUnit_order,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat, sub_self]

/-- The comparison is a local unit: the actual ratio has a finite nonzero punctured limit. -/
theorem deningerMeyerXiRelationGerm_ratio_hasLimit (p : Nat.Primes) (rho : XiDivisorSupport) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((deningerMeyerXiRelationGerm p rho / xiMeroGermUnit rho : MeroGermˣ) : MeroGerm).HasLimit c := by
  let u := deningerMeyerXiRelationGerm p rho / xiMeroGermUnit rho
  have hu : meromorphicOrderAt (u : MeroGerm).rep 0 = 0 := by
    change (u : MeroGerm).order = 0
    rw [← meroGermUnitOrder_coe, deningerMeyerXiRelationGerm_ratio_order]
    rfl
  exact tendsto_ne_zero_of_meromorphicOrderAt_eq_zero (u : MeroGerm).rep_mero hu

/-- The fixed-clock K2 source is built from the literal determinant of the arithmetic relation. -/
def deningerMeyerXiRelationMarkedSource (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) :
    PrimeClockMarkedK2 p q :=
  markedTameSymbol (primeClockComplexUnit p q) (deningerMeyerXiRelationGerm p rho)

/-- Its retained degree is derived from the determinant and the actual full jet block. -/
theorem deningerMeyerXiRelationMarkedSource_degree (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0)
    (rho : XiDivisorSupport) :
    primeClockMarkedDegree p hq (deningerMeyerXiRelationMarkedSource p q rho) =
      (xiSupportMultiplicity rho : ℤ) := by
  rw [primeClockMarkedDegree, deningerMeyerXiRelationMarkedSource,
    markedTameDegree_symbol, deningerMeyerXiRelationGerm_order]

/-- The relation symbol and actual Xi clock correction have precisely the same tame class. -/
theorem deningerMeyerXiRelationMarkedSource_tame_comparison (p : Nat.Primes) {q : ℕ}
    (hq : q ≠ 0) (rho : XiDivisorSupport) :
    meroGermTameBoundary
      ((deningerMeyerXiRelationMarkedSource p q rho).val -
        (xiPrimeMarkedClockCorrection p q ((rho : ℂ) - primeAlgebraicClockStep q)).val) = 0 := by
  apply (markedTameDegree_eq_zero_iff (primeClockComplexUnit p q)
    (primeClockComplexUnit_zpow_injective p hq)
    (deningerMeyerXiRelationMarkedSource p q rho -
      xiPrimeMarkedClockCorrection p q ((rho : ℂ) - primeAlgebraicClockStep q))).mp
  change primeClockMarkedDegree p hq
    (deningerMeyerXiRelationMarkedSource p q rho -
      xiPrimeMarkedClockCorrection p q ((rho : ℂ) - primeAlgebraicClockStep q)) = 0
  rw [map_sub, deningerMeyerXiRelationMarkedSource_degree, xiPrimeMarkedClockCorrection_degree,
    sub_add_cancel, xiSupportMultiplicity_eq_analyticOrderAt_toNat, sub_self]

/-- Equality in the fixed-clock quotient is a theorem about two actual source symbols. -/
theorem deningerMeyerXiRelationMarkedSource_quotient_comparison (p : Nat.Primes) {q : ℕ}
    (hq : q ≠ 0) (rho : XiDivisorSupport) :
    (QuotientAddGroup.mk (deningerMeyerXiRelationMarkedSource p q rho) :
      PrimeClockMarkedK2 p q ⧸ (primeClockMarkedDegree p hq).ker) =
        QuotientAddGroup.mk
          (xiPrimeMarkedClockCorrection p q ((rho : ℂ) - primeAlgebraicClockStep q)) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change primeClockMarkedDegree p hq
    (deningerMeyerXiRelationMarkedSource p q rho -
      xiPrimeMarkedClockCorrection p q ((rho : ℂ) - primeAlgebraicClockStep q)) = 0
  rw [map_sub, deningerMeyerXiRelationMarkedSource_degree, xiPrimeMarkedClockCorrection_degree,
    sub_add_cancel, xiSupportMultiplicity_eq_analyticOrderAt_toNat, sub_self]

/-- An actual isolated Xi dipole and the full arithmetic relation determine the same marked
quotient class at a native prime clock. No topological realization premise is inserted. -/
theorem deningerMeyerXiRelationMarkedSource_dipole_comparison (p : Nat.Primes) (rho : XiDivisorSupport) :
    ∃ (q : ℕ) (hq : 0 < q) (x : PrimeClockMarkedK2 p q),
      x.val = xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho ∧
      (QuotientAddGroup.mk (deningerMeyerXiRelationMarkedSource p q rho) :
        PrimeClockMarkedK2 p q ⧸ (primeClockMarkedDegree p (Nat.ne_of_gt hq)).ker) =
          QuotientAddGroup.mk x := by
  obtain ⟨q, hq, x, hx, hd⟩ := xiPrimeDipole_marked_source p rho
  refine ⟨q, hq, x, hx, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
  change primeClockMarkedDegree p (Nat.ne_of_gt hq)
    (deningerMeyerXiRelationMarkedSource p q rho - x) = 0
  rw [map_sub, deningerMeyerXiRelationMarkedSource_degree, hd,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat, sub_self]

/-- The concrete quantum multiplier is the inverse of the retained native prime clock.
This fixes the orientation for any subsequent topological transgression. -/
theorem paperPrimeRotationQuantumUnit_eq_clock_inv (p : Nat.Primes) (q : ℕ) :
    paperRotationQuantumUnit (paperPrimeRotationFrequency p q) = (primeClockComplexUnit p q)⁻¹ := by
  have hc : (primeClockComplexUnit p q : ℂ) =
      paperRotationPhase (paperPrimeRotationFrequency p q) := by
    rw [paperPrimeRotationPhase_eq_native]
    simpa only [pow_one] using primeClockComplexUnit_pow_eq_phase p q 1
  have hm : paperRotationQuantumUnit (paperPrimeRotationFrequency p q) * primeClockComplexUnit p q = 1 := by
    apply Units.ext
    change paperRotationPhase (-paperPrimeRotationFrequency p q) * (primeClockComplexUnit p q : ℂ) = 1
    rw [hc, ← paperRotationPhase_add, neg_add_cancel, paperRotationPhase_zero]
  calc
    _ = (paperRotationQuantumUnit (paperPrimeRotationFrequency p q) * primeClockComplexUnit p q) *
        (primeClockComplexUnit p q)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by rw [hm, one_mul]

end
end RHTower
