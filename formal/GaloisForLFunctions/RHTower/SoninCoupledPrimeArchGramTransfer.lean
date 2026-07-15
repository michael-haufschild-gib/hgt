import GaloisForLFunctions.RHTower.SoninCoupledPrimeResidual
import GaloisForLFunctions.RHTower.SoninPrimeArchFiniteMomentTransfer
import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage
import Mathlib.Analysis.InnerProductSpace.GramMatrix

open Filter Topology Polynomial
open scoped BigOperators
open scoped ComplexOrder

namespace RHTower

noncomputable section

local instance soninCoupledTransferDecidableEq : DecidableEq SoninHilbertIndex :=
  Classical.decEq _

local instance soninCoupledAllPrimeDecidableEq : DecidableEq SoninAllPrimeIndex :=
  Classical.decEq _

private noncomputable def matrixOfRect
    {κ ι : Type*} [DecidableEq ι]
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2) : κ × ι → ℂ :=
  fun p => T (lp.single 2 p.2 (1 : ℂ)) p.1

private theorem matrixOfRect_isHS
    {κ ι : Type*} [DecidableEq ι]
    {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2}
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    Summable (fun p : κ × ι => ‖matrixOfRect T p‖ ^ 2) := by
  have hcols : ∀ j, Summable
      (fun i => ‖T (lp.single 2 j (1 : ℂ)) i‖ ^ 2) := fun j =>
    HilbertSchmidt.summable_coe_sq (T (lp.single 2 j (1 : ℂ)))
  have henergy : Summable
      (fun j => ∑' i, ‖T (lp.single 2 j (1 : ℂ)) i‖ ^ 2) := by
    refine (hT.summable (HilbertSchmidt.lpBasis ι)).congr fun j => ?_
    rw [HilbertSchmidt.lpBasis_apply, HilbertSchmidt.lp_norm_sq_eq]
  have hswap : Summable
      (fun q : ι × κ => ‖T (lp.single 2 q.1 (1 : ℂ)) q.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => by positivity)]
    exact ⟨fun j => hcols j, henergy⟩
  have h : Summable
      (fun p : κ × ι => ‖T (lp.single 2 p.2 (1 : ℂ)) p.1‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      hswap.comp_injective (Equiv.prodComm κ ι).injective
  exact h.congr fun _ => rfl

private noncomputable def hsRectVector
    {κ ι : Type*} [DecidableEq ι]
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    lp (fun _ : κ × ι => ℂ) 2 :=
  ⟨matrixOfRect T, HilbertSchmidt.memℓp_of_sq (matrixOfRect_isHS hT)⟩

private theorem inner_hsRectVector_eq_hsInner
    {κ ι : Type*} [DecidableEq ι]
    {S T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : κ => ℂ) 2}
    (hS : ContinuousLinearMap.IsHilbertSchmidt S)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    inner ℂ (hsRectVector S hS) (hsRectVector T hT) =
      ContinuousLinearMap.hsInner S T := by
  have hprod : Summable (fun p : κ × ι =>
      (starRingEnd ℂ) (matrixOfRect S p) * matrixOfRect T p) := by
    apply Summable.of_norm_bounded
      (g := fun p => (‖matrixOfRect S p‖ ^ 2 + ‖matrixOfRect T p‖ ^ 2) / 2)
    · exact ((matrixOfRect_isHS hS).add (matrixOfRect_isHS hT)).div_const 2
    · intro p
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖matrixOfRect S p‖ - ‖matrixOfRect T p‖),
        norm_nonneg (matrixOfRect S p), norm_nonneg (matrixOfRect T p)]
  calc
    inner ℂ (hsRectVector S hS) (hsRectVector T hT) =
        ∑' p : κ × ι,
          (starRingEnd ℂ) (matrixOfRect S p) * matrixOfRect T p := by
      rw [lp.inner_eq_tsum]
      exact tsum_congr fun p => by
        rw [RCLike.inner_apply]
        simp [hsRectVector, mul_comm]
    _ = ∑' q : ι × κ,
          (starRingEnd ℂ) (matrixOfRect S (q.2, q.1)) *
            matrixOfRect T (q.2, q.1) := by
      exact (Equiv.prodComm κ ι).tsum_eq
        (fun q : ι × κ =>
          (starRingEnd ℂ) (matrixOfRect S (q.2, q.1)) *
            matrixOfRect T (q.2, q.1))
    _ = ∑' j : ι, ∑' r : κ,
          (starRingEnd ℂ) (matrixOfRect S (r, j)) *
            matrixOfRect T (r, j) := by
      exact ((hprod.comp_injective (Equiv.prodComm ι κ).injective).tsum_prod)
    _ = ContinuousLinearMap.hsInner S T := by
      rw [ContinuousLinearMap.hsInner_eq_tsum_basis hS hT
        (HilbertSchmidt.lpBasis ι)]
      apply tsum_congr
      intro j
      rw [HilbertSchmidt.lpBasis_apply, lp.inner_eq_tsum]
      exact tsum_congr fun r => by
        rw [RCLike.inner_apply]
        simp [matrixOfRect, mul_comm]

/-- The coupled column and the older block-diagonal assembly have exactly the same total
Hilbert--Schmidt energy.  Coupling first changes the trace sequence after the energy is
multiplied, where mixed prime-power words survive. -/
theorem hsNormSqRect_soninAllPrimeColumnKernel_eq_residualKernel
    (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.hsNormSqRect (soninAllPrimeColumnKernel a) =
      HilbertSchmidt.hsNormSq (soninAllPrimeResidualKernel a) := by
  classical
  have hcol := soninAllPrimeColumnKernel_isHSRect a ha
  have hold := soninAllPrimeResidualKernel_isHS a ha
  rw [HilbertSchmidt.hsNormSqRect, HilbertSchmidt.hsNormSq,
    hcol.tsum_prod, hold.tsum_prod]
  apply tsum_congr
  intro row
  have hrow : Summable (fun col : SoninAllPrimeIndex =>
      ‖soninAllPrimeResidualKernel a (row, col)‖ ^ 2) :=
    hold.comp_injective (fun _ _ h => (Prod.mk.inj h).2)
  rw [hrow.tsum_prod]
  rw [tsum_eq_single row.1]
  · simp [soninAllPrimeResidualKernel, soninAllPrimeColumnKernel]
  · intro qk hq
    simp [soninAllPrimeResidualKernel, Ne.symm hq]

private theorem hsInner_self_eq_ofReal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    ContinuousLinearMap.hsInner T T =
      (ContinuousLinearMap.hsNormSq T : ℂ) := by
  apply Complex.ext
  · exact ContinuousLinearMap.hsInner_self_re hT
  · rw [Complex.ofReal_im]
    change (∑' i, inner ℂ
      (T (ContinuousLinearMap.hsBasis ℂ E i))
      (T (ContinuousLinearMap.hsBasis ℂ E i))).im = 0
    rw [Complex.im_tsum (hT.summable_inner hT (ContinuousLinearMap.hsBasis ℂ E))]
    have hzero : (fun i => (inner ℂ
        (T (ContinuousLinearMap.hsBasis ℂ E i))
        (T (ContinuousLinearMap.hsBasis ℂ E i))).im) = fun _ => 0 := by
      funext i
      simpa using inner_self_im (𝕜 := ℂ)
        (T (ContinuousLinearMap.hsBasis ℂ E i))
    rw [hzero, tsum_zero]

/-- A positive Sonin aperture, kept as data rather than an external side condition. -/
def SoninPositiveAperture := {a : ℝ // 0 < a}

/-- The coupled coordinate energy `C_a† C_a` on the one common Sonin source. -/
def soninAllPrimeCoupledCoordinateEnergy (a : SoninPositiveAperture) :
    lp (fun _ : SoninHilbertIndex => ℂ) 2 →L[ℂ]
      lp (fun _ : SoninHilbertIndex => ℂ) 2 :=
  ContinuousLinearMap.adjoint
      (soninAllPrimeColumnCoordinateOperator a.1 a.2) ∘L
    soninAllPrimeColumnCoordinateOperator a.1 a.2

theorem soninAllPrimeCoupledCoordinateEnergy_isSelfAdjoint
    (a : SoninPositiveAperture) :
    ContinuousLinearMap.adjoint (soninAllPrimeCoupledCoordinateEnergy a) =
      soninAllPrimeCoupledCoordinateEnergy a := by
  rw [soninAllPrimeCoupledCoordinateEnergy,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- **One-channel criterion for the coupled positive effect.**  The quantum master effect
`C_a† C_a` is nonzero exactly when one concrete prime-power Sonin residual is nonzero. -/
theorem soninAllPrimeCoupledCoordinateEnergy_ne_zero_iff_exists_primePowerResidual_ne_zero
    (a : SoninPositiveAperture) :
    soninAllPrimeCoupledCoordinateEnergy a ≠ 0 ↔
      ∃ pk : Nat.Primes × ℕ, centralSoninPrimePowerResidual a.1 pk ≠ 0 := by
  change (ContinuousLinearMap.adjoint
      (soninAllPrimeColumnCoordinateOperator a.1 a.2) ∘L
        soninAllPrimeColumnCoordinateOperator a.1 a.2) ≠ 0 ↔ _
  rw [HTGeometry.adjoint_comp_self_ne_zero_iff,
    soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_primePowerResidual_ne_zero]

/-- The output energy is unchanged when the common Sonin source is replaced by its canonical
Hilbert-basis coordinates. -/
theorem soninAllPrimeCoordinateOutputEnergy_eq_outputEnergy
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeColumnCoordinateOperator a ha ∘L
        ContinuousLinearMap.adjoint (soninAllPrimeColumnCoordinateOperator a ha) =
      soninAllPrimeOutputEnergyOperator a ha := by
  let C := soninAllPrimeColumnCoordinateOperator a ha
  let U := (ContinuousLinearMap.hsBasis ℂ SoninL2).repr
  change C ∘L ContinuousLinearMap.adjoint C =
    (C ∘L U.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
      ContinuousLinearMap.adjoint
        (C ∘L U.toContinuousLinearEquiv.toContinuousLinearMap)
  rw [ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  exact (U.apply_symm_apply ((ContinuousLinearMap.adjoint C) x)).symm

private theorem opTrace_sq_adjoint_comp_self_cyclic
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    ContinuousLinearMap.opTrace
        ((ContinuousLinearMap.adjoint C ∘L C) ∘L
          (ContinuousLinearMap.adjoint C ∘L C)) =
      ContinuousLinearMap.opTrace
        ((C ∘L ContinuousLinearMap.adjoint C) ∘L
          (C ∘L ContinuousLinearMap.adjoint C)) := by
  let S : F →L[ℂ] F := C ∘L ContinuousLinearMap.adjoint C
  let B : E →L[ℂ] F := S ∘L C
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    hC.adjoint.comp_left C
  have hB : ContinuousLinearMap.IsHilbertSchmidt B := hC.comp_left S
  have hcyc := ContinuousLinearMap.opTrace_comp_comm hC.adjoint hB
  calc
    ContinuousLinearMap.opTrace
        ((ContinuousLinearMap.adjoint C ∘L C) ∘L
          (ContinuousLinearMap.adjoint C ∘L C)) =
        ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint C ∘L B) := by
      congr 1
    _ = ContinuousLinearMap.opTrace (B ∘L ContinuousLinearMap.adjoint C) := hcyc
    _ = ContinuousLinearMap.opTrace
        ((C ∘L ContinuousLinearMap.adjoint C) ∘L
          (C ∘L ContinuousLinearMap.adjoint C)) := by
      congr 1

/-- The `n`-th coupled source column `C_a (C_a† C_a)^n`. -/
def soninAllPrimeCoupledPowerColumn (a : SoninPositiveAperture) (n : ℕ) :
    lp (fun _ : SoninHilbertIndex => ℂ) 2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeColumnCoordinateOperator a.1 a.2 ∘L
    soninAllPrimeCoupledCoordinateEnergy a ^ n

theorem soninAllPrimeCoupledPowerColumn_isHilbertSchmidt
    (a : SoninPositiveAperture) (n : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt
      (soninAllPrimeCoupledPowerColumn a n) := by
  exact (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
    (soninAllPrimeColumnKernel_isHSRect a.1 a.2)).comp_right
      (soninAllPrimeCoupledCoordinateEnergy a ^ n)

/-- Hilbert--Schmidt coordinate vector of the `n`-th coupled source column. -/
def soninAllPrimeCoupledPowerVector (a : SoninPositiveAperture) (n : ℕ) :
    lp (fun _ : SoninAllPrimeIndex × SoninHilbertIndex => ℂ) 2 :=
  hsRectVector (soninAllPrimeCoupledPowerColumn a n)
    (soninAllPrimeCoupledPowerColumn_isHilbertSchmidt a n)

/-- The complete finite Gram block of coupled prime-power residual columns. -/
def soninAllPrimeCoupledGramBlock (N : ℕ) (a : SoninPositiveAperture) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun n : Fin N =>
    soninAllPrimeCoupledPowerVector a (n : ℕ))

/-- The Gram entries are exactly the Hilbert--Schmidt pairings of the coupled source columns;
the `ℓ²` encoding introduces no surrogate moment data. -/
theorem soninAllPrimeCoupledGramBlock_apply
    (N : ℕ) (a : SoninPositiveAperture) (i j : Fin N) :
    soninAllPrimeCoupledGramBlock N a i j =
      ContinuousLinearMap.hsInner
        (soninAllPrimeCoupledPowerColumn a (i : ℕ))
        (soninAllPrimeCoupledPowerColumn a (j : ℕ)) := by
  rw [soninAllPrimeCoupledGramBlock, Matrix.gram_apply,
    soninAllPrimeCoupledPowerVector]
  exact inner_hsRectVector_eq_hsInner _ _

/-- The coupled Hilbert--Schmidt pairing is intrinsically Hankel: it is the trace of the
`(m+n+1)`-st power of the positive common-source energy. -/
theorem hsInner_soninAllPrimeCoupledPowerColumn_eq_tracePower
    (a : SoninPositiveAperture) (m n : ℕ) :
    ContinuousLinearMap.hsInner
        (soninAllPrimeCoupledPowerColumn a m)
        (soninAllPrimeCoupledPowerColumn a n) =
      ContinuousLinearMap.opTrace
        (soninAllPrimeCoupledCoordinateEnergy a ^ (m + n + 1)) := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  let T := soninAllPrimeCoupledCoordinateEnergy a
  let Vm := soninAllPrimeCoupledPowerColumn a m
  let Vn := soninAllPrimeCoupledPowerColumn a n
  have hT : ContinuousLinearMap.adjoint T = T :=
    soninAllPrimeCoupledCoordinateEnergy_isSelfAdjoint a
  have hpow : ContinuousLinearMap.adjoint (T ^ m) = T ^ m := by
    change star (T ^ m) = T ^ m
    rw [star_pow]
    change ContinuousLinearMap.adjoint T ^ m = T ^ m
    rw [hT]
  calc
    ContinuousLinearMap.hsInner Vm Vn =
        ContinuousLinearMap.opTrace
          (ContinuousLinearMap.adjoint Vm ∘L Vn) := by
      rw [ContinuousLinearMap.opTrace_comp_eq_hsInner
        (ContinuousLinearMap.adjoint Vm) Vn,
        ContinuousLinearMap.adjoint_adjoint]
    _ = ContinuousLinearMap.opTrace (T ^ (m + n + 1)) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [Vm, Vn, soninAllPrimeCoupledPowerColumn,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      rw [hpow]
      change (T ^ m) ((ContinuousLinearMap.adjoint C)
        (C ((T ^ n) x))) = (T ^ (m + n + 1)) x
      have henergy (y) : (ContinuousLinearMap.adjoint C) (C y) = T y := by
        rfl
      rw [henergy]
      change (T ^ m) (T ((T ^ n) x)) = (T ^ (m + n + 1)) x
      rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply]
      congr 1
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

/-- The coupled trace-moment sequence.  Unlike the earlier block-diagonal sequence, its powers
retain every mixed prime word in the common-source energy. -/
def soninAllPrimeCoupledTraceMoment (a : SoninPositiveAperture) (k : ℕ) : ℂ :=
  ContinuousLinearMap.opTrace
    (soninAllPrimeCoupledCoordinateEnergy a ^ (k + 1))

/-- The zeroth coupled moment is exactly the Hilbert--Schmidt energy of the common all-prime
source column.  This identifies its strict-positivity premise with ordinary source
non-degeneracy, before any comparison with the prime--Gamma target. -/
theorem soninAllPrimeCoupledTraceMoment_zero_eq_column_hsNormSq
    (a : SoninPositiveAperture) :
    soninAllPrimeCoupledTraceMoment a 0 =
      (ContinuousLinearMap.hsNormSq
        (soninAllPrimeColumnCoordinateOperator a.1 a.2) : ℂ) := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  calc
    soninAllPrimeCoupledTraceMoment a 0 =
        ContinuousLinearMap.hsInner C C := by
      rw [soninAllPrimeCoupledTraceMoment]
      simp only [zero_add, pow_one, soninAllPrimeCoupledCoordinateEnergy, C]
      exact ContinuousLinearMap.opTrace_adjoint_comp_self C
    _ = (ContinuousLinearMap.hsNormSq C : ℂ) := hsInner_self_eq_ofReal hC

/-- Strict positivity of the normalizing moment is equivalent to the concrete all-prime Sonin
column being nonzero.  Thus the scale-eliminated RH chain needs no independent sign estimate:
its remaining degree-zero input is precisely source non-degeneracy. -/
theorem soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero
    (a : SoninPositiveAperture) :
    0 < (soninAllPrimeCoupledTraceMoment a 0).re ↔
      soninAllPrimeColumnCoordinateOperator a.1 a.2 ≠ 0 := by
  rw [soninAllPrimeCoupledTraceMoment_zero_eq_column_hsNormSq,
    Complex.ofReal_re]
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  constructor
  · intro hpos hzero
    have hCzero : C = 0 := by simpa only [C] using hzero
    have hnormzero : ContinuousLinearMap.hsNormSq C = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mpr hCzero
    linarith
  · intro hne
    have hne' : ContinuousLinearMap.hsNormSq C ≠ 0 := by
      intro hzero
      apply hne
      simpa only [C] using (ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mp hzero
    exact lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg C) (Ne.symm hne')

/-- Degree-zero source positivity is a purely local channel condition: one prime-power residual
witness is necessary and sufficient. -/
theorem soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_exists_primePowerResidual_ne_zero
    (a : SoninPositiveAperture) :
    0 < (soninAllPrimeCoupledTraceMoment a 0).re ↔
      ∃ pk : Nat.Primes × ℕ, centralSoninPrimePowerResidual a.1 pk ≠ 0 := by
  rw [soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero,
    soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_primePowerResidual_ne_zero]

/-- The zeroth coupled trace moment is already the zeroth block-diagonal Sonin moment.  Thus
the coupled route adds no new scalar normalization at degree zero; its genuinely new arithmetic
data begin with mixed words in the second trace moment. -/
theorem soninAllPrimeCoupledTraceMoment_zero_eq_energyMoment
    (a : SoninPositiveAperture) :
    soninAllPrimeCoupledTraceMoment a 0 =
      soninAllPrimeEnergyMoment a.1 0 := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  calc
    soninAllPrimeCoupledTraceMoment a 0 =
        ContinuousLinearMap.hsInner C C := by
      rw [soninAllPrimeCoupledTraceMoment]
      simp only [zero_add, pow_one, soninAllPrimeCoupledCoordinateEnergy, C]
      exact ContinuousLinearMap.opTrace_adjoint_comp_self C
    _ = (ContinuousLinearMap.hsNormSq C : ℂ) := hsInner_self_eq_ofReal hC
    _ = (HilbertSchmidt.hsNormSqRect (soninAllPrimeColumnKernel a.1) : ℂ) := by
      congr 1
      exact HilbertSchmidt.hsNormSq_toOperatorRect
        (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
    _ = (HilbertSchmidt.hsNormSq (soninAllPrimeResidualKernel a.1) : ℂ) := by
      rw [hsNormSqRect_soninAllPrimeColumnKernel_eq_residualKernel a.1 a.2]
    _ = soninAllPrimeEnergyMoment a.1 0 := by
      rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow]
      exact (trace_soninAllPrimeResidualEnergyKernel a.1 a.2).symm

private theorem soninAllPrimeEnergyMoment_one_eq_residualEnergy_hsNormSq
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeEnergyMoment a 1 =
      (HilbertSchmidt.hsNormSq (soninAllPrimeResidualEnergyKernel a) : ℂ) := by
  let T := soninAllPrimeResidualEnergyKernel a
  have hT : HilbertSchmidt.IsHS T := soninAllPrimeResidualEnergyKernel_isHS a ha
  have hself : HilbertSchmidt.hsAdjoint T = T :=
    soninAllPrimeResidualEnergyKernel_selfAdjoint a
  calc
    soninAllPrimeEnergyMoment a 1 =
        ∑' i : SoninAllPrimeIndex,
          HilbertSchmidt.hsComp T T (i, i) := by
      rw [soninAllPrimeEnergyMoment]
      rfl
    _ = HilbertSchmidt.hsInner T T := by
      rw [HilbertSchmidt.hsTrace_hsComp hT hT]
      rw [hself]
    _ = _ := by simpa [T] using HilbertSchmidt.hsInner_self T

private def soninAllPrimeBlockOutputEnergyOperator (a : ℝ) (ha : 0 < a) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeResidualOperator a ha ∘L
    ContinuousLinearMap.adjoint (soninAllPrimeResidualOperator a ha)

private theorem soninAllPrimeBlockOutputEnergyOperator_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt
      (soninAllPrimeBlockOutputEnergyOperator a ha) :=
  (soninAllPrimeResidualOperator_isHilbertSchmidt a ha).adjoint.comp_left
    (soninAllPrimeResidualOperator a ha)

private theorem matrix_soninAllPrimeBlockOutputEnergyOperator
    (a : ℝ) (ha : 0 < a)
    (α β : Nat.Primes × ℕ) (i j : SoninHilbertIndex) :
    HilbertSchmidt.matrixOf (soninAllPrimeBlockOutputEnergyOperator a ha)
        ((α, i), (β, j)) =
      if α = β then
        inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
          (soninPrimePowerCrossOverlap a α α
            (ContinuousLinearMap.hsBasis ℂ SoninL2 j))
      else 0 := by
  let K := soninAllPrimeResidualKernel a
  have hK : HilbertSchmidt.IsHS K := soninAllPrimeResidualKernel_isHS a ha
  have hop : soninAllPrimeBlockOutputEnergyOperator a ha =
      HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_hsComp hK (HilbertSchmidt.isHS_hsAdjoint hK)) := by
    rw [soninAllPrimeBlockOutputEnergyOperator, soninAllPrimeResidualOperator,
      HilbertSchmidt.toOperator_hsComp,
      HilbertSchmidt.adjoint_toOperator]
  rw [hop, HilbertSchmidt.matrixOf_toOperator]
  by_cases hab : α = β
  · subst β
    rw [if_pos rfl]
    rw [HilbertSchmidt.hsComp]
    have hsum := HilbertSchmidt.hsComp_summable hK
      (HilbertSchmidt.isHS_hsAdjoint hK) (α, i) (α, j)
    rw [hsum.tsum_prod]
    simp only [HilbertSchmidt.hsAdjoint, K, soninAllPrimeResidualKernel]
    let b := ContinuousLinearMap.hsBasis ℂ SoninL2
    let A := centralSoninWeightedPrimePowerResidual a α
    change (∑' γ, ∑' k,
      (if α = γ then inner ℂ (b i) (A (b k)) else 0) *
        (starRingEnd ℂ)
          (if α = γ then inner ℂ (b j) (A (b k)) else 0)) =
        inner ℂ (b i) ((A ∘L ContinuousLinearMap.adjoint A) (b j))
    rw [show (fun γ => ∑' k,
        (if α = γ then inner ℂ (b i) (A (b k)) else 0) *
          (starRingEnd ℂ)
            (if α = γ then inner ℂ (b j) (A (b k)) else 0)) =
        fun γ => if γ = α then
          ∑' k, inner ℂ (b i) (A (b k)) *
            (starRingEnd ℂ) (inner ℂ (b j) (A (b k)))
          else 0 by
      funext γ
      by_cases hγ : γ = α
      · subst γ
        simp
      · have hγ' : α ≠ γ := Ne.symm hγ
        simp [hγ, hγ']]
    rw [tsum_ite_eq α]
    calc
      (∑' k, inner ℂ (b i) (A (b k)) *
          (starRingEnd ℂ) (inner ℂ (b j) (A (b k)))) =
          ∑' k, inner ℂ (ContinuousLinearMap.adjoint A (b i)) (b k) *
            inner ℂ (b k) (ContinuousLinearMap.adjoint A (b j)) := by
        apply tsum_congr
        intro k
        rw [show inner ℂ (b i) (A (b k)) =
            inner ℂ (ContinuousLinearMap.adjoint A (b i)) (b k) by
          exact (ContinuousLinearMap.adjoint_inner_left A (b k) (b i)).symm]
        rw [show (starRingEnd ℂ) (inner ℂ (b j) (A (b k))) =
            inner ℂ (b k) (ContinuousLinearMap.adjoint A (b j)) by
          calc
            (starRingEnd ℂ) (inner ℂ (b j) (A (b k))) =
                inner ℂ (A (b k)) (b j) := inner_conj_symm _ _
            _ = _ := (ContinuousLinearMap.adjoint_inner_right A (b k) (b j)).symm]
      _ = inner ℂ (ContinuousLinearMap.adjoint A (b i))
          (ContinuousLinearMap.adjoint A (b j)) :=
        b.tsum_inner_mul_inner _ _
      _ = inner ℂ (b i) ((A ∘L ContinuousLinearMap.adjoint A) (b j)) := by
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_left]
  · rw [if_neg hab]
    rw [HilbertSchmidt.hsComp]
    have hzero : (fun x : SoninAllPrimeIndex =>
        K ((α, i), x) * HilbertSchmidt.hsAdjoint K (x, (β, j))) = 0 := by
      funext x
      rcases x with ⟨γ, k⟩
      simp only [HilbertSchmidt.hsAdjoint, K, soninAllPrimeResidualKernel]
      by_cases haγ : α = γ
      · subst γ
        simp [Ne.symm hab]
      · simp [haγ]
    rw [hzero]
    exact tsum_zero

private def soninAllPrimeBlockSecondMomentEquiv :
    ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) ×
        (SoninHilbertIndex × SoninHilbertIndex) ≃
      SoninAllPrimeIndex × SoninAllPrimeIndex where
  toFun z := ((z.1.1, z.2.2), (z.1.2, z.2.1))
  invFun z := ((z.1.1, z.2.1), (z.2.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem hsNormSq_soninAllPrimeBlockOutputEnergyOperator_eq_diagonal
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (soninAllPrimeBlockOutputEnergyOperator a ha) =
      soninAllPrimeDiagonalSecondMoment a := by
  let S := soninAllPrimeBlockOutputEnergyOperator a ha
  let M := HilbertSchmidt.matrixOf S
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeBlockOutputEnergyOperator_isHilbertSchmidt a ha
  have hM : HilbertSchmidt.IsHS M := HilbertSchmidt.isHS_matrixOf hS
  have hround : HilbertSchmidt.toOperator hM = S :=
    HilbertSchmidt.toOperator_matrixOf hS
  have hnorm : ContinuousLinearMap.hsNormSq S = HilbertSchmidt.hsNormSq M := by
    rw [← hround, HilbertSchmidt.hsNormSq_toOperator]
  rw [show soninAllPrimeBlockOutputEnergyOperator a ha = S from rfl, hnorm,
    soninAllPrimeDiagonalSecondMoment]
  change (∑' z : SoninAllPrimeIndex × SoninAllPrimeIndex, ‖M z‖ ^ 2) = _
  rw [← soninAllPrimeBlockSecondMomentEquiv.tsum_eq
    (fun z : SoninAllPrimeIndex × SoninAllPrimeIndex => ‖M z‖ ^ 2)]
  have hflat : Summable (fun z :
      ((Nat.Primes × ℕ) × (Nat.Primes × ℕ)) ×
        (SoninHilbertIndex × SoninHilbertIndex) =>
      ‖M (soninAllPrimeBlockSecondMomentEquiv z)‖ ^ 2) :=
    (soninAllPrimeBlockSecondMomentEquiv.summable_iff).mpr hM
  rw [hflat.tsum_prod]
  have hab : Summable (fun ab : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      ∑' ji : SoninHilbertIndex × SoninHilbertIndex,
        ‖M (soninAllPrimeBlockSecondMomentEquiv (ab, ji))‖ ^ 2) := by
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hflat |>.2
  rw [hab.tsum_prod]
  apply tsum_congr
  intro α
  rw [show (fun β => ∑' ji : SoninHilbertIndex × SoninHilbertIndex,
        ‖M (soninAllPrimeBlockSecondMomentEquiv ((α, β), ji))‖ ^ 2) =
      fun β => if β = α then
        ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a α α)
      else 0 by
    funext β
    by_cases hβ : β = α
    · subst β
      rw [if_pos rfl]
      rw [ContinuousLinearMap.hsNormSq_eq
        (soninPrimePowerCrossOverlap_isHilbertSchmidt a ha α α)
        (ContinuousLinearMap.hsBasis ℂ SoninL2)]
      have hji : Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
          ‖M (soninAllPrimeBlockSecondMomentEquiv ((α, α), ji))‖ ^ 2) := by
        exact hflat.comp_injective (fun ji ji' h => (Prod.ext_iff.mp h).2)
      rw [hji.tsum_prod]
      apply tsum_congr
      intro j
      rw [← tsum_sq_norm_inner_hilbertBasis
        (ContinuousLinearMap.hsBasis ℂ SoninL2)
        (soninPrimePowerCrossOverlap a α α
          (ContinuousLinearMap.hsBasis ℂ SoninL2 j))]
      apply tsum_congr
      intro i
      rw [show M (soninAllPrimeBlockSecondMomentEquiv ((α, α), (j, i))) =
          inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
            (soninPrimePowerCrossOverlap a α α
              (ContinuousLinearMap.hsBasis ℂ SoninL2 j)) by
        dsimp [M, S]
        simpa using matrix_soninAllPrimeBlockOutputEnergyOperator a ha α α i j]
    · rw [if_neg hβ]
      have hne : α ≠ β := Ne.symm hβ
      have hzero : (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
          ‖M (soninAllPrimeBlockSecondMomentEquiv ((α, β), ji))‖ ^ 2) = 0 := by
        funext ji
        rw [show M (soninAllPrimeBlockSecondMomentEquiv ((α, β), ji)) = 0 by
          dsimp [M, S]
          simpa [hne] using
            matrix_soninAllPrimeBlockOutputEnergyOperator a ha α β ji.2 ji.1]
        simp
      rw [hzero]
      exact tsum_zero]
  rw [tsum_ite_eq α]

private theorem hsNormSq_soninAllPrimeResidualEnergyKernel_eq_blockOutput
    (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.hsNormSq (soninAllPrimeResidualEnergyKernel a) =
      ContinuousLinearMap.hsNormSq (soninAllPrimeBlockOutputEnergyOperator a ha) := by
  let K := soninAllPrimeResidualOperator a ha
  let T := ContinuousLinearMap.adjoint K ∘L K
  let S := K ∘L ContinuousLinearMap.adjoint K
  have hK : ContinuousLinearMap.IsHilbertSchmidt K :=
    soninAllPrimeResidualOperator_isHilbertSchmidt a ha
  have hT : ContinuousLinearMap.IsHilbertSchmidt T := hK.comp_left _
  have hS : ContinuousLinearMap.IsHilbertSchmidt S := hK.adjoint.comp_left _
  have hTself : ContinuousLinearMap.adjoint T = T := by
    dsimp [T]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hSself : ContinuousLinearMap.adjoint S = S := by
    dsimp [S]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hcyc := opTrace_sq_adjoint_comp_self_cyclic hK
  have henergyOp : HilbertSchmidt.toOperator
      (soninAllPrimeResidualEnergyKernel_isHS a ha) = T := by
    dsimp [T, K, soninAllPrimeResidualEnergyKernel,
      soninAllPrimeResidualOperator]
    rw [HilbertSchmidt.toOperator_hsComp,
      HilbertSchmidt.adjoint_toOperator]
  have hkernel : HilbertSchmidt.hsNormSq
      (soninAllPrimeResidualEnergyKernel a) =
      ContinuousLinearMap.hsNormSq T := by
    rw [← henergyOp, HilbertSchmidt.hsNormSq_toOperator]
  rw [hkernel]
  have hTnorm := ContinuousLinearMap.re_opTrace_adjoint_comp_self hT
  have hSnorm := ContinuousLinearMap.re_opTrace_adjoint_comp_self hS
  rw [hTself] at hTnorm
  rw [hSself] at hSnorm
  change ContinuousLinearMap.hsNormSq T = ContinuousLinearMap.hsNormSq S
  rw [← hTnorm, ← hSnorm]
  exact congrArg Complex.re hcyc

/-- The diagonal second-overlap invariant is exactly the degree-one moment of the older
block-diagonal Sonin sequence.  Thus the first coupled correction is measured relative to an
already formalized source moment, rather than only to an analogous block sum. -/
theorem soninAllPrimeEnergyMoment_one_eq_diagonalSecondMoment
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeEnergyMoment a 1 =
      (soninAllPrimeDiagonalSecondMoment a : ℂ) := by
  rw [soninAllPrimeEnergyMoment_one_eq_residualEnergy_hsNormSq a ha]
  rw [hsNormSq_soninAllPrimeResidualEnergyKernel_eq_blockOutput a ha]
  rw [hsNormSq_soninAllPrimeBlockOutputEnergyOperator_eq_diagonal a ha]

/-- The first genuinely coupled moment is the complete second overlap energy: its diagonal part
is the old direct-sum contribution, and its new part is the nonnegative sum of all off-diagonal
prime-power overlap energies. -/
theorem re_soninAllPrimeCoupledTraceMoment_one_eq_diagonal_add_mixed
    (a : SoninPositiveAperture) :
    (soninAllPrimeCoupledTraceMoment a 1).re =
      soninAllPrimeDiagonalSecondMoment a.1 +
        soninAllPrimeMixedSecondInvariant a.1 := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  rw [soninAllPrimeCoupledTraceMoment]
  norm_num only
  rw [pow_two, ContinuousLinearMap.mul_def]
  change (ContinuousLinearMap.opTrace
    ((ContinuousLinearMap.adjoint C ∘L C) ∘L
      (ContinuousLinearMap.adjoint C ∘L C))).re = _
  rw [opTrace_sq_adjoint_comp_self_cyclic hC]
  rw [soninAllPrimeCoordinateOutputEnergy_eq_outputEnergy a.1 a.2]
  rw [← opTrace_sq_soninAllPrimeMixedEnergyOperator_cyclic a.1 a.2]
  exact re_opTrace_sq_soninAllPrimeMixedEnergyOperator_eq_diagonal_add_I2 a.1 a.2

/-- Exact first correction to the old trace sequence: common-source coupling adds precisely the
nonnegative off-diagonal overlap invariant to the old degree-one Sonin moment. -/
theorem re_soninAllPrimeCoupledTraceMoment_one_eq_energyMoment_add_mixed
    (a : SoninPositiveAperture) :
    (soninAllPrimeCoupledTraceMoment a 1).re =
      (soninAllPrimeEnergyMoment a.1 1).re +
        soninAllPrimeMixedSecondInvariant a.1 := by
  rw [re_soninAllPrimeCoupledTraceMoment_one_eq_diagonal_add_mixed]
  rw [soninAllPrimeEnergyMoment_one_eq_diagonalSecondMoment a.1 a.2,
    Complex.ofReal_re]

/-- Every even-indexed coupled trace moment is the squared Hilbert--Schmidt norm of one coupled
power column. -/
theorem soninAllPrimeCoupledTraceMoment_even_eq_hsNormSq_powerColumn
    (a : SoninPositiveAperture) (n : ℕ) :
    soninAllPrimeCoupledTraceMoment a (2 * n) =
      (ContinuousLinearMap.hsNormSq
        (soninAllPrimeCoupledPowerColumn a n) : ℂ) := by
  calc
    soninAllPrimeCoupledTraceMoment a (2 * n) =
        ContinuousLinearMap.hsInner
          (soninAllPrimeCoupledPowerColumn a n)
          (soninAllPrimeCoupledPowerColumn a n) := by
      rw [hsInner_soninAllPrimeCoupledPowerColumn_eq_tracePower,
        soninAllPrimeCoupledTraceMoment]
      congr 2
      omega
    _ = _ := hsInner_self_eq_ofReal
      (soninAllPrimeCoupledPowerColumn_isHilbertSchmidt a n)

theorem soninAllPrimeCoupledCoordinateEnergy_pow_isHilbertSchmidt
    (a : SoninPositiveAperture) {n : ℕ} (hn : 0 < n) :
    ContinuousLinearMap.IsHilbertSchmidt
      (soninAllPrimeCoupledCoordinateEnergy a ^ n) := by
  let C := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hC : ContinuousLinearMap.IsHilbertSchmidt C :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, ContinuousLinearMap.mul_def]
  exact (hC.comp_left (ContinuousLinearMap.adjoint C)).comp_left
    (soninAllPrimeCoupledCoordinateEnergy a ^ m)

/-- Every odd-indexed coupled trace moment is the squared Hilbert--Schmidt norm of a positive
power of the common-source energy. -/
theorem soninAllPrimeCoupledTraceMoment_odd_eq_hsNormSq_energyPower
    (a : SoninPositiveAperture) (n : ℕ) :
    soninAllPrimeCoupledTraceMoment a (2 * n + 1) =
      (ContinuousLinearMap.hsNormSq
        (soninAllPrimeCoupledCoordinateEnergy a ^ (n + 1)) : ℂ) := by
  let T := soninAllPrimeCoupledCoordinateEnergy a
  let S := T ^ (n + 1)
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    soninAllPrimeCoupledCoordinateEnergy_pow_isHilbertSchmidt a (by omega)
  have hSad : ContinuousLinearMap.adjoint S = S := by
    change star (T ^ (n + 1)) = T ^ (n + 1)
    rw [star_pow]
    change ContinuousLinearMap.adjoint T ^ (n + 1) = T ^ (n + 1)
    rw [soninAllPrimeCoupledCoordinateEnergy_isSelfAdjoint]
  calc
    soninAllPrimeCoupledTraceMoment a (2 * n + 1) =
        ContinuousLinearMap.opTrace
          (ContinuousLinearMap.adjoint S ∘L S) := by
      rw [soninAllPrimeCoupledTraceMoment, hSad]
      congr 1
      dsimp only [S]
      change T ^ (2 * n + 1 + 1) =
        (T ^ (n + 1)) ∘L (T ^ (n + 1))
      rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega,
        pow_add, ContinuousLinearMap.mul_def]
    _ = ContinuousLinearMap.hsInner S S :=
      ContinuousLinearMap.opTrace_adjoint_comp_self S
    _ = _ := hsInner_self_eq_ofReal hS

/-- Every coupled trace moment is real before any comparison with the prime--Gamma target. -/
theorem soninAllPrimeCoupledTraceMoment_im_eq_zero
    (a : SoninPositiveAperture) (k : ℕ) :
    (soninAllPrimeCoupledTraceMoment a k).im = 0 := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [soninAllPrimeCoupledTraceMoment_even_eq_hsNormSq_powerColumn,
      Complex.ofReal_im]
  · subst k
    rw [soninAllPrimeCoupledTraceMoment_odd_eq_hsNormSq_energyPower,
      Complex.ofReal_im]

/-- Every individual coupled trace moment is nonnegative.  The RH content of the finite-block
closure is therefore in the simultaneous Hankel relations, not in the signs of isolated source
moments. -/
theorem soninAllPrimeCoupledTraceMoment_re_nonneg
    (a : SoninPositiveAperture) (k : ℕ) :
    0 ≤ (soninAllPrimeCoupledTraceMoment a k).re := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [soninAllPrimeCoupledTraceMoment_even_eq_hsNormSq_powerColumn,
      Complex.ofReal_re]
    exact ContinuousLinearMap.hsNormSq_nonneg _
  · subst k
    rw [soninAllPrimeCoupledTraceMoment_odd_eq_hsNormSq_energyPower,
      Complex.ofReal_re]
    exact ContinuousLinearMap.hsNormSq_nonneg _

theorem soninAllPrimeCoupledGramBlock_eq_traceMoment
    (N : ℕ) (a : SoninPositiveAperture) (i j : Fin N) :
    soninAllPrimeCoupledGramBlock N a i j =
      soninAllPrimeCoupledTraceMoment a ((i : ℕ) + (j : ℕ)) := by
  rw [soninAllPrimeCoupledGramBlock_apply,
    hsInner_soninAllPrimeCoupledPowerColumn_eq_tracePower,
    soninAllPrimeCoupledTraceMoment]

theorem soninAllPrimeCoupledGramBlock_posSemidef
    (N : ℕ) (a : SoninPositiveAperture) :
    (soninAllPrimeCoupledGramBlock N a).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

/-- Finite Hankel block of the normalized continued prime--Gamma source. -/
def primeArchNormalizedHankelBlock (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ)

/-- Static all-coefficient source relation: each finite prime--Gamma Hankel block is a cluster
point of actual coupled all-prime Sonin Gram blocks. -/
def SoninCoupledPrimeArchFiniteGramClosure : Prop :=
  ∀ N : ℕ, primeArchNormalizedHankelBlock N ∈
    closure (Set.range (soninAllPrimeCoupledGramBlock N))

/-- Sequential analytic form of the same source problem: one positive-aperture schedule at each
finite cutoff converges simultaneously in every entry of the coupled Gram block. -/
def SoninCoupledPrimeArchFiniteGramCoupling
    (aperture : ℕ → ℕ → SoninPositiveAperture) : Prop :=
  ∀ N : ℕ,
    Tendsto (fun j : ℕ => soninAllPrimeCoupledGramBlock N (aperture N j))
      atTop (nhds (primeArchNormalizedHankelBlock N))

/-- Reduced analytic target: at cutoff `N`, the first `2N-1` coupled trace moments converge along
one positive-aperture schedule to the normalized prime--Gamma moments.  The Hankel identity above
then supplies all `N²` Gram entries simultaneously. -/
def SoninCoupledPrimeArchFiniteMomentCoupling
    (aperture : ℕ → ℕ → SoninPositiveAperture) : Prop :=
  ∀ N k, k < 2 * N - 1 →
    Tendsto (fun j : ℕ => soninAllPrimeCoupledTraceMoment (aperture N j) k)
      atTop (nhds ((normalizedPrimeArchMoment k : ℝ) : ℂ))

theorem soninCoupledPrimeArchFiniteGramCoupling_of_momentCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteMomentCoupling aperture) :
    SoninCoupledPrimeArchFiniteGramCoupling aperture := by
  intro N
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hij : (i : ℕ) + (j : ℕ) < 2 * N - 1 := by omega
  simpa only [soninAllPrimeCoupledGramBlock_eq_traceMoment,
    primeArchNormalizedHankelBlock] using
      h N ((i : ℕ) + (j : ℕ)) hij

theorem soninCoupledPrimeArchFiniteGramClosure_of_coupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteGramCoupling aperture) :
    SoninCoupledPrimeArchFiniteGramClosure := by
  intro N
  exact mem_closure_of_tendsto (h N)
    (Eventually.of_forall fun j => Set.mem_range_self (aperture N j))

/-! ## Projective finite-block coupling

Positive semidefiniteness is homogeneous, so exact scalar normalization of the source moments is
unnecessary.  A positive scale at each aperture removes the degree-zero matching obstruction and
leaves only projective moment-shape convergence. -/

/-- A strictly positive global scale for one coupled source block. -/
def SoninPositiveScale := {r : ℝ // 0 < r}

/-- A positively rescaled coupled Gram block, realized as an actual Gram matrix by scaling every
source vector with the positive square root. -/
def soninAllPrimeCoupledProjectiveGramBlock
    (N : ℕ) (d : SoninPositiveScale × SoninPositiveAperture) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun n : Fin N =>
    ((Real.sqrt d.1.1 : ℝ) : ℂ) •
      soninAllPrimeCoupledPowerVector d.2 (n : ℕ))

theorem soninAllPrimeCoupledProjectiveGramBlock_apply
    (N : ℕ) (d : SoninPositiveScale × SoninPositiveAperture)
    (i j : Fin N) :
    soninAllPrimeCoupledProjectiveGramBlock N d i j =
      (d.1.1 : ℂ) *
        soninAllPrimeCoupledTraceMoment d.2 ((i : ℕ) + (j : ℕ)) := by
  rw [soninAllPrimeCoupledProjectiveGramBlock, Matrix.gram_apply]
  rw [inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  change ((Real.sqrt d.1.1 : ℝ) : ℂ) *
      (((Real.sqrt d.1.1 : ℝ) : ℂ) *
        soninAllPrimeCoupledGramBlock N d.2 i j) = _
  rw [soninAllPrimeCoupledGramBlock_eq_traceMoment]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (le_of_lt d.1.2)]

theorem soninAllPrimeCoupledProjectiveGramBlock_posSemidef
    (N : ℕ) (d : SoninPositiveScale × SoninPositiveAperture) :
    (soninAllPrimeCoupledProjectiveGramBlock N d).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

/-- Scale-free source relation: every finite target block is a cluster point of positively
rescaled coupled Sonin Gram blocks. -/
def SoninCoupledPrimeArchProjectiveFiniteGramClosure : Prop :=
  ∀ N : ℕ, primeArchNormalizedHankelBlock N ∈
    closure (Set.range (soninAllPrimeCoupledProjectiveGramBlock N))

/-- Sequential projective block coupling. -/
def SoninCoupledPrimeArchProjectiveFiniteGramCoupling
    (data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture) : Prop :=
  ∀ N : ℕ,
    Tendsto (fun j : ℕ => soninAllPrimeCoupledProjectiveGramBlock N (data N j))
      atTop (nhds (primeArchNormalizedHankelBlock N))

/-- Reduced scale-free analytic target: only the shape of the first `2N-1` moments must match;
one positive scalar is shared by the whole finite block. -/
def SoninCoupledPrimeArchProjectiveFiniteMomentCoupling
    (data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture) : Prop :=
  ∀ N k, k < 2 * N - 1 →
    Tendsto (fun j : ℕ =>
        ((data N j).1.1 : ℂ) *
          soninAllPrimeCoupledTraceMoment (data N j).2 k)
      atTop (nhds ((normalizedPrimeArchMoment k : ℝ) : ℂ))

theorem soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_momentCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data) :
    SoninCoupledPrimeArchProjectiveFiniteGramCoupling data := by
  intro N
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hij : (i : ℕ) + (j : ℕ) < 2 * N - 1 := by omega
  simpa only [soninAllPrimeCoupledProjectiveGramBlock_apply,
    primeArchNormalizedHankelBlock] using
      h N ((i : ℕ) + (j : ℕ)) hij

theorem soninCoupledPrimeArchProjectiveFiniteGramClosure_of_coupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteGramCoupling data) :
    SoninCoupledPrimeArchProjectiveFiniteGramClosure := by
  intro N
  exact mem_closure_of_tendsto (h N)
    (Eventually.of_forall fun j => Set.mem_range_self (data N j))

private def finiteRealMatrixQuadratic {N : ℕ}
    (c : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, ((c i * c j : ℝ) : ℂ) * M i j).re

private theorem continuous_finiteRealMatrixQuadratic {N : ℕ} (c : Fin N → ℝ) :
    Continuous (finiteRealMatrixQuadratic c) := by
  unfold finiteRealMatrixQuadratic
  fun_prop

private theorem finiteRealMatrixQuadratic_nonneg_of_posSemidef
    {N : ℕ} (c : Fin N → ℝ) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.PosSemidef) : 0 ≤ finiteRealMatrixQuadratic c M := by
  let z : Fin N → ℂ := fun i => (c i : ℂ)
  have h := hM.dotProduct_mulVec_nonneg z
  have hre : 0 ≤ (star z ⬝ᵥ M.mulVec z).re := (Complex.nonneg_iff.mp h).1
  have heq : finiteRealMatrixQuadratic c M =
      (star z ⬝ᵥ M.mulVec z).re := by
    simp [finiteRealMatrixQuadratic, z, dotProduct, Matrix.mulVec, mul_assoc]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [heq]

/-! ## Canonically normalized scalar value coupling

Whole-block convergence asks one aperture schedule to match every coefficient vector at once.
For the countable RH criterion this is stronger than necessary: one may keep the test polynomial
fixed and transfer only its scalar Gram value.  An arbitrary positive rescaling would collapse
this interface to the nonnegative ray and merely restate positivity, so the scale below is fixed
canonically by the zeroth coupled moment. -/

/-- Positive apertures at which the explicit coupled all-prime source column is nonzero. -/
def SoninCoupledNondegenerateAperture :=
  {a : SoninPositiveAperture //
    soninAllPrimeColumnCoordinateOperator a.1 a.2 ≠ 0}

/-- Build the nondegenerate aperture required by the coupled source-normalization chain from one
concrete prime-power residual witness.  No global all-prime cancellation hypothesis remains. -/
def soninCoupledNondegenerateApertureOfPrimePowerResidual
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ)
    (hpk : centralSoninPrimePowerResidual a pk ≠ 0) :
    SoninCoupledNondegenerateAperture :=
  ⟨⟨a, ha⟩,
    soninAllPrimeColumnCoordinateOperator_ne_zero_of_primePowerResidual_ne_zero
      a ha pk hpk⟩

/-- The scalar coupled Gram value of one real polynomial at one positive aperture. -/
def soninAllPrimeCoupledPolynomialGramValue
    (a : SoninPositiveAperture) (p : Polynomial ℝ) : ℝ :=
  let N := p.natDegree + 1
  finiteRealMatrixQuadratic (Polynomial.toFn N p)
    (soninAllPrimeCoupledGramBlock N a)

/-- The actual coupled source vector read by one polynomial.  It is the same polynomial linear
combination of the Hilbert--Schmidt power columns whose Gram quadratic value appears above. -/
def soninAllPrimeCoupledPolynomialPowerVector
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    lp (fun _ : SoninAllPrimeIndex × SoninHilbertIndex => ℂ) 2 :=
  let N := p.natDegree + 1
  ∑ i : Fin N, ((Polynomial.toFn N p i : ℝ) : ℂ) •
    soninAllPrimeCoupledPowerVector a (i : ℕ)

/-- The per-test scalar is literally a squared Hilbert norm of the explicit coupled Sonin
polynomial source vector. -/
theorem soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledPolynomialGramValue a p =
      ‖soninAllPrimeCoupledPolynomialPowerVector a p‖ ^ 2 := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  change
    (∑ i : Fin N, ∑ j : Fin N,
      ((c i * c j : ℝ) : ℂ) *
        soninAllPrimeCoupledGramBlock N a i j).re =
      ‖∑ i : Fin N, ((c i : ℝ) : ℂ) •
        soninAllPrimeCoupledPowerVector a (i : ℕ)‖ ^ 2
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  apply congrArg Complex.re
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [soninAllPrimeCoupledGramBlock, Matrix.gram_apply]
  push_cast
  ring

theorem soninAllPrimeCoupledPolynomialGramValue_nonneg
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    0 ≤ soninAllPrimeCoupledPolynomialGramValue a p := by
  unfold soninAllPrimeCoupledPolynomialGramValue
  exact finiteRealMatrixQuadratic_nonneg_of_posSemidef _
    (soninAllPrimeCoupledGramBlock_posSemidef _ a)

/-- The unique source normalization which matches the target zeroth moment.  Its value is forced
by the aperture; it is not an independently variable projective parameter. -/
def soninAllPrimeCoupledCanonicalScale
    (a : SoninCoupledNondegenerateAperture) : ℝ :=
  normalizedPrimeArchMoment 0 /
    (soninAllPrimeCoupledTraceMoment a.1 0).re

theorem soninAllPrimeCoupledCanonicalScale_pos
    (a : SoninCoupledNondegenerateAperture) :
    0 < soninAllPrimeCoupledCanonicalScale a := by
  exact div_pos normalizedPrimeArchMoment_zero_pos
    ((soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2)

/-- The polynomial Gram value after the degree-zero source normalization forced by the aperture. -/
def soninAllPrimeCoupledNormalizedPolynomialGramValue
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) : ℝ :=
  soninAllPrimeCoupledCanonicalScale a *
    soninAllPrimeCoupledPolynomialGramValue a.1 p

theorem soninAllPrimeCoupledNormalizedPolynomialGramValue_eq_norm_sq
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledNormalizedPolynomialGramValue a p =
      soninAllPrimeCoupledCanonicalScale a *
        ‖soninAllPrimeCoupledPolynomialPowerVector a.1 p‖ ^ 2 := by
  rw [soninAllPrimeCoupledNormalizedPolynomialGramValue,
    soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq]

theorem soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    0 ≤ soninAllPrimeCoupledNormalizedPolynomialGramValue a p := by
  exact mul_nonneg (le_of_lt (soninAllPrimeCoupledCanonicalScale_pos a))
    (soninAllPrimeCoupledPolynomialGramValue_nonneg a.1 p)

/-- The actual canonically normalized coupled-source values for one fixed integer polynomial.
The aperture varies, but its scale is the forced zeroth-moment quotient rather than a free ray
parameter. -/
def soninCoupledPrimeArchPerTestNormalizedValueLocus
    (p : Polynomial ℤ) : Set ℝ :=
  Set.range (fun a : SoninCoupledNondegenerateAperture =>
    soninAllPrimeCoupledNormalizedPolynomialGramValue a
      (p.map (Int.castRingHom ℝ)))

/-- Source-pure scalar closure: each integer-polynomial prime--Gamma value is a cluster value of
the canonically normalized coupled Sonin value for that same polynomial.  The aperture may depend
on the test, so no simultaneous moment or whole-block convergence is assumed. -/
def SoninCoupledPrimeArchPerTestNormalizedValueClosure : Prop :=
  ∀ p : Polynomial ℤ,
    (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re ∈
      closure (soninCoupledPrimeArchPerTestNormalizedValueLocus p)

/-- Sequential form of the scalar relation, with a separate nondegenerate aperture schedule for
each integer polynomial. -/
def SoninCoupledPrimeArchPerTestNormalizedValueCoupling
    (aperture : Polynomial ℤ → ℕ → SoninCoupledNondegenerateAperture) : Prop :=
  ∀ p : Polynomial ℤ,
    Tendsto
      (fun j : ℕ => soninAllPrimeCoupledNormalizedPolynomialGramValue
        (aperture p j) (p.map (Int.castRingHom ℝ)))
      atTop
      (nhds (primeArchSourceTraceHankel
        (p.map (Int.castRingHom ℝ))).re)

theorem soninCoupledPrimeArchPerTestNormalizedValueClosure_of_coupling
    {aperture : Polynomial ℤ → ℕ → SoninCoupledNondegenerateAperture}
    (h : SoninCoupledPrimeArchPerTestNormalizedValueCoupling aperture) :
    SoninCoupledPrimeArchPerTestNormalizedValueClosure := by
  intro p
  exact mem_closure_of_tendsto (h p)
    (Eventually.of_forall fun j => Set.mem_range_self (aperture p j))

theorem primeArchSourceTraceHankelIntNonnegative_of_soninCoupledPerTestNormalizedValueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  have hsubset : soninCoupledPrimeArchPerTestNormalizedValueLocus p ⊆ Set.Ici 0 := by
    rintro x ⟨a, rfl⟩
    exact soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg a
      (p.map (Int.castRingHom ℝ))
  exact closure_minimal hsubset isClosed_Ici (h p)

/-- **Canonical scalar coupled-Sonin chain to RH.**  Per-test convergence of one actual
normalized coupled Gram value is enough.  This is weaker than simultaneous finite-block or
moment-ratio convergence and retains the mixed-prime words of the coupled source. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchPerTestNormalizedValueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninCoupledPerTestNormalizedValueClosure h)

/-- Explicit sequential chain
`per-test canonical coupled value convergence -> scalar closure -> prime--Gamma positivity -> RH`. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchPerTestNormalizedValueCoupling
    {aperture : Polynomial ℤ → ℕ → SoninCoupledNondegenerateAperture}
    (h : SoninCoupledPrimeArchPerTestNormalizedValueCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchPerTestNormalizedValueClosure
    (soninCoupledPrimeArchPerTestNormalizedValueClosure_of_coupling h)

/-! ## One-sided variational reduction

Exact cluster matching is stronger than positivity transfer needs.  Since every canonically
normalized coupled Sonin value is nonnegative, it is enough to approximate the target from above:
the source infimum for each polynomial may lie strictly below its prime--Gamma value. -/

/-- One-sided per-test source domination.  For every integer polynomial and every positive error,
some nondegenerate aperture has normalized coupled Gram value at most the target prime--Gamma
quadratic value plus that error.  No convergence, equality, or simultaneous moment matching is
required. -/
def SoninCoupledPrimeArchPerTestVariationalUpperBound : Prop :=
  ∀ (p : Polynomial ℤ) (ε : ℝ), 0 < ε →
    ∃ a : SoninCoupledNondegenerateAperture,
      soninAllPrimeCoupledNormalizedPolynomialGramValue a
          (p.map (Int.castRingHom ℝ)) ≤
        (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε

/-- Cross-multiplied Rayleigh form of the same one-sided comparison.  It uses only the squared norm
of the coupled polynomial source vector and the zeroth coupled source energy, so there is no
quotient in the analytic target. -/
def SoninCoupledPrimeArchPerTestRayleighUpperBound : Prop :=
  ∀ (p : Polynomial ℤ) (ε : ℝ), 0 < ε →
    ∃ a : SoninCoupledNondegenerateAperture,
      normalizedPrimeArchMoment 0 *
          ‖soninAllPrimeCoupledPolynomialPowerVector a.1
            (p.map (Int.castRingHom ℝ))‖ ^ 2 ≤
        ((primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re + ε) *
          (soninAllPrimeCoupledTraceMoment a.1 0).re

/-- The normalized variational interface and its cross-multiplied Rayleigh form are exactly
equivalent.  Nondegeneracy supplies the strictly positive denominator. -/
theorem soninCoupledPrimeArchPerTestRayleighUpperBound_iff_variationalUpperBound :
    SoninCoupledPrimeArchPerTestRayleighUpperBound ↔
      SoninCoupledPrimeArchPerTestVariationalUpperBound := by
  constructor
  · intro h p ε hε
    obtain ⟨a, ha⟩ := h p ε hε
    refine ⟨a, ?_⟩
    have hden : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
      (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
    rw [soninAllPrimeCoupledNormalizedPolynomialGramValue_eq_norm_sq,
      soninAllPrimeCoupledCanonicalScale]
    have heq :
        normalizedPrimeArchMoment 0 /
              (soninAllPrimeCoupledTraceMoment a.1 0).re *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (p.map (Int.castRingHom ℝ))‖ ^ 2 =
          (normalizedPrimeArchMoment 0 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (p.map (Int.castRingHom ℝ))‖ ^ 2) /
              (soninAllPrimeCoupledTraceMoment a.1 0).re := by
      field_simp [hden.ne']
    rw [heq]
    exact (div_le_iff₀ hden).2 ha
  · intro h p ε hε
    obtain ⟨a, ha⟩ := h p ε hε
    refine ⟨a, ?_⟩
    have hden : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
      (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
    rw [soninAllPrimeCoupledNormalizedPolynomialGramValue_eq_norm_sq,
      soninAllPrimeCoupledCanonicalScale] at ha
    have heq :
        normalizedPrimeArchMoment 0 /
              (soninAllPrimeCoupledTraceMoment a.1 0).re *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (p.map (Int.castRingHom ℝ))‖ ^ 2 =
          (normalizedPrimeArchMoment 0 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (p.map (Int.castRingHom ℝ))‖ ^ 2) /
              (soninAllPrimeCoupledTraceMoment a.1 0).re := by
      field_simp [hden.ne']
    rw [heq] at ha
    exact (div_le_iff₀ hden).1 ha

/-- Exact value closure implies the weaker one-sided variational interface. -/
theorem soninCoupledPrimeArchPerTestVariationalUpperBound_of_valueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    SoninCoupledPrimeArchPerTestVariationalUpperBound := by
  intro p ε hε
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp (h p) ε hε
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a, ?_⟩
  rw [Real.dist_eq] at hdist
  have hneg := neg_lt_of_abs_lt hdist
  linarith

/-- Exact value closure also supplies the quotient-free Rayleigh comparison. -/
theorem soninCoupledPrimeArchPerTestRayleighUpperBound_of_valueClosure
    (h : SoninCoupledPrimeArchPerTestNormalizedValueClosure) :
    SoninCoupledPrimeArchPerTestRayleighUpperBound :=
  soninCoupledPrimeArchPerTestRayleighUpperBound_iff_variationalUpperBound.mpr
    (soninCoupledPrimeArchPerTestVariationalUpperBound_of_valueClosure h)

/-- One-sided variational domination already forces every integer prime--Gamma Hankel value to be
nonnegative.  A hypothetical negative target is separated from zero by a positive error smaller
than its absolute value, contradicting the nonnegative coupled Gram producer. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_soninCoupledPerTestVariationalUpperBound
    (h : SoninCoupledPrimeArchPerTestVariationalUpperBound) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  let target : ℝ := (primeArchSourceTraceHankel q).re
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨a, ha⟩ := h p ε hε
  have hsource :
      0 ≤ soninAllPrimeCoupledNormalizedPolynomialGramValue a q :=
    soninAllPrimeCoupledNormalizedPolynomialGramValue_nonneg a q
  have htargetε : target + ε < 0 := by
    dsimp [ε]
    linarith
  change soninAllPrimeCoupledNormalizedPolynomialGramValue a q ≤ target + ε at ha
  linarith

/-- **One-sided variational coupled-Sonin chain to RH.**  It is enough to upper-approximate each
prime--Gamma integer-polynomial value by one nonnegative normalized coupled Gram value, with
arbitrarily small positive error.  Exact value convergence and finite-block coupling are absent. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchPerTestVariationalUpperBound
    (h : SoninCoupledPrimeArchPerTestVariationalUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninCoupledPerTestVariationalUpperBound h)

/-- Quotient-free Rayleigh form of the one-sided coupled-Sonin chain to RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchPerTestRayleighUpperBound
    (h : SoninCoupledPrimeArchPerTestRayleighUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchPerTestVariationalUpperBound
    (soninCoupledPrimeArchPerTestRayleighUpperBound_iff_variationalUpperBound.mp h)

private theorem primeArchSourceTraceHankelIntNonnegative_of_finiteQuadraticNonnegative
    (h : ∀ (N : ℕ) (c : Fin N → ℝ),
      0 ≤ finiteRealMatrixQuadratic c (primeArchNormalizedHankelBlock N)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  let N : ℕ := q.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N q
  have hN : q.natDegree < N := by omega
  have hq : Polynomial.ofFn N c = q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hN
  have htarget := h N c
  have heq : finiteRealMatrixQuadratic c (primeArchNormalizedHankelBlock N) =
      (primeArchSourceTraceHankel q).re := by
    change (∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) *
          ((normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ)).re = _
    have hmom : (∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) *
          ((normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ)) =
        primeArchSourceTraceHankel q := by
      calc
        _ = ∑ i : Fin N, ∑ j : Fin N,
            ((c i * c j : ℝ) : ℂ) *
              xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [← primeArchSourceMoment_eq_xiCentralReciprocalMoment]
          rfl
        _ = xiCentralTraceHankel (Polynomial.ofFn N c) :=
          (xiCentralTraceHankel_ofFn N c).symm
        _ = xiCentralTraceHankel q := congrArg xiCentralTraceHankel hq
        _ = primeArchSourceTraceHankel q :=
          xiCentralTraceHankel_eq_primeArchSourceTraceHankel q
    exact congrArg Complex.re hmom
  simpa only [q, heq] using htarget

theorem primeArchSourceTraceHankelIntNonnegative_of_soninCoupledFiniteGramClosure
    (h : SoninCoupledPrimeArchFiniteGramClosure) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  apply primeArchSourceTraceHankelIntNonnegative_of_finiteQuadraticNonnegative
  intro N c
  have hsubset : Set.range (soninAllPrimeCoupledGramBlock N) ⊆
      finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0 := by
    rintro M ⟨a, rfl⟩
    exact finiteRealMatrixQuadratic_nonneg_of_posSemidef c
      (soninAllPrimeCoupledGramBlock_posSemidef N a)
  have hclosed : IsClosed (finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0) :=
    isClosed_Ici.preimage (continuous_finiteRealMatrixQuadratic c)
  exact closure_minimal hsubset hclosed (h N)

theorem primeArchSourceTraceHankelIntNonnegative_of_soninCoupledProjectiveClosure
    (h : SoninCoupledPrimeArchProjectiveFiniteGramClosure) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  apply primeArchSourceTraceHankelIntNonnegative_of_finiteQuadraticNonnegative
  intro N c
  have hsubset : Set.range (soninAllPrimeCoupledProjectiveGramBlock N) ⊆
      finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0 := by
    rintro M ⟨d, rfl⟩
    exact finiteRealMatrixQuadratic_nonneg_of_posSemidef c
      (soninAllPrimeCoupledProjectiveGramBlock_posSemidef N d)
  have hclosed : IsClosed (finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0) :=
    isClosed_Ici.preimage (continuous_finiteRealMatrixQuadratic c)
  exact closure_minimal hsubset hclosed (h N)

/-- **Scale-free coupled Sonin chain to RH.**  Projective finite-block closure is enough; no
absolute degree-zero normalization of the source moment sequence is required. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteGramClosure
    (h : SoninCoupledPrimeArchProjectiveFiniteGramClosure) : RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninCoupledProjectiveClosure h)

/-- Projective Gram convergence implies RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteGramCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteGramCoupling data) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteGramClosure
    (soninCoupledPrimeArchProjectiveFiniteGramClosure_of_coupling h)

/-- Projective trace-moment convergence implies RH.  The positive scale is common to all moments
at one finite cutoff and may vary with the aperture. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteMomentCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteGramCoupling
    (soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_momentCoupling h)

/-! ## Normalized moment-ratio coupling

The projective scale can be eliminated from the theorem interface.  Strict positivity of the
zeroth coupled energy makes the canonical scale `m₀ / S₀(a)` available at every aperture.  The
degree-zero target is then matched identically, so only the nonconstant projective coordinates
`Sₖ(a) / S₀(a)` remain. -/

/-- Source-only normalized moment-shape convergence.  At cutoff `N`, one positive-aperture
schedule must match only the ratios of the first `2N-1` coupled moments, and the trivial degree-zero
ratio is omitted. -/
def SoninCoupledPrimeArchMomentRatioCoupling
    (aperture : ℕ → ℕ → SoninPositiveAperture) : Prop :=
  (∀ N j, 0 <
      (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re) ∧
    ∀ N k, 0 < k → k < 2 * N - 1 →
      Tendsto (fun j : ℕ =>
          soninAllPrimeCoupledTraceMoment (aperture N j) k /
            soninAllPrimeCoupledTraceMoment (aperture N j) 0)
        atTop
        (nhds ((((normalizedPrimeArchMoment k : ℝ) : ℂ) /
          ((normalizedPrimeArchMoment 0 : ℝ) : ℂ))))

private def soninCoupledPrimeArchRatioData
    (aperture : ℕ → ℕ → SoninPositiveAperture)
    (hpos : ∀ N j, 0 <
      (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re)
    (N j : ℕ) : SoninPositiveScale × SoninPositiveAperture :=
  (⟨normalizedPrimeArchMoment 0 /
      (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re,
    div_pos normalizedPrimeArchMoment_zero_pos (hpos N j)⟩,
    aperture N j)

/-- **Scale-eliminated coupled Sonin chain to RH.**  Strictly positive source energy and
convergence of the normalized coupled moment ratios are enough; no external scale sequence and no
degree-zero convergence hypothesis remain. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchMomentRatioCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchMomentRatioCoupling aperture) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_soninCoupledPrimeArchProjectiveFiniteMomentCoupling
    (data := soninCoupledPrimeArchRatioData aperture h.1)
  intro N k hk
  by_cases hk0 : k = 0
  · subst k
    have hfun : (fun j : ℕ =>
        (((soninCoupledPrimeArchRatioData aperture h.1 N j).1.1 : ℝ) : ℂ) *
          soninAllPrimeCoupledTraceMoment
            (soninCoupledPrimeArchRatioData aperture h.1 N j).2 0) =
        fun _ : ℕ => ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) := by
      funext j
      rw [soninCoupledPrimeArchRatioData]
      change
        (((normalizedPrimeArchMoment 0 /
          (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℝ) : ℂ) *
            soninAllPrimeCoupledTraceMoment (aperture N j) 0) =
          ((normalizedPrimeArchMoment 0 : ℝ) : ℂ)
      have hs0 : soninAllPrimeCoupledTraceMoment (aperture N j) 0 =
          ((soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [soninAllPrimeCoupledTraceMoment_im_eq_zero]
      have hs0ne : soninAllPrimeCoupledTraceMoment (aperture N j) 0 ≠ 0 := by
        rw [hs0]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (h.1 N j))
      have hscale :
          ((normalizedPrimeArchMoment 0 /
            (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℝ) : ℂ) =
            ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) /
              soninAllPrimeCoupledTraceMoment (aperture N j) 0 := by
        rw [hs0]
        push_cast
        simp
      rw [hscale]
      exact div_mul_cancel₀ _ hs0ne
    rw [hfun]
    exact tendsto_const_nhds
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hratio := h.2 N k hkpos hk
    have hmul :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => ((normalizedPrimeArchMoment 0 : ℝ) : ℂ))
        atTop (nhds ((normalizedPrimeArchMoment 0 : ℝ) : ℂ))).mul hratio
    convert hmul using 1
    · funext j
      rw [soninCoupledPrimeArchRatioData]
      change
        (((normalizedPrimeArchMoment 0 /
          (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℝ) : ℂ) *
            soninAllPrimeCoupledTraceMoment (aperture N j) k) =
          ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) *
            (soninAllPrimeCoupledTraceMoment (aperture N j) k /
              soninAllPrimeCoupledTraceMoment (aperture N j) 0)
      have hs0 : soninAllPrimeCoupledTraceMoment (aperture N j) 0 =
          ((soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [soninAllPrimeCoupledTraceMoment_im_eq_zero]
      have hs0ne : soninAllPrimeCoupledTraceMoment (aperture N j) 0 ≠ 0 := by
        rw [hs0]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (h.1 N j))
      have hscale :
          ((normalizedPrimeArchMoment 0 /
            (soninAllPrimeCoupledTraceMoment (aperture N j) 0).re : ℝ) : ℂ) =
            ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) /
              soninAllPrimeCoupledTraceMoment (aperture N j) 0 := by
        rw [hs0]
        push_cast
        simp
      rw [hscale]
      field_simp [hs0ne]
    · field_simp [ne_of_gt normalizedPrimeArchMoment_zero_pos]

/-- **Coupled Sonin finite-Gram chain to RH.**  Whole finite-block closure of the fixed
prime--Gamma Hankel matrix inside the canonical coupled all-prime Sonin Gram family forces RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchFiniteGramClosure
    (h : SoninCoupledPrimeArchFiniteGramClosure) : RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_soninCoupledFiniteGramClosure h)

/-- Explicit chain
`coupled finite Gram convergence -> finite Gram closure -> prime--Gamma positivity -> RH`. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchFiniteGramCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteGramCoupling aperture) : RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchFiniteGramClosure
    (soninCoupledPrimeArchFiniteGramClosure_of_coupling h)

/-- Reduced explicit chain
`coupled trace-moment convergence -> coupled Gram convergence -> closure -> RH`. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchFiniteMomentCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteMomentCoupling aperture) : RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchFiniteGramCoupling
    (soninCoupledPrimeArchFiniteGramCoupling_of_momentCoupling h)

end

end RHTower
