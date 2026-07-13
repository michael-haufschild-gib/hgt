import GaloisForLFunctions.RHTower.SoninCoupledPrimeResidual
import GaloisForLFunctions.RHTower.SoninPrimeArchFiniteMomentTransfer
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

theorem primeArchSourceTraceHankelIntNonnegative_of_soninCoupledFiniteGramClosure
    (h : SoninCoupledPrimeArchFiniteGramClosure) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  let N : ℕ := q.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N q
  have hN : q.natDegree < N := by omega
  have hq : Polynomial.ofFn N c = q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hN
  have hsubset : Set.range (soninAllPrimeCoupledGramBlock N) ⊆
      finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0 := by
    rintro M ⟨a, rfl⟩
    exact finiteRealMatrixQuadratic_nonneg_of_posSemidef c
      (soninAllPrimeCoupledGramBlock_posSemidef N a)
  have hclosed : IsClosed (finiteRealMatrixQuadratic c ⁻¹' Set.Ici 0) :=
    isClosed_Ici.preimage (continuous_finiteRealMatrixQuadratic c)
  have htarget : 0 ≤ finiteRealMatrixQuadratic c
      (primeArchNormalizedHankelBlock N) :=
    closure_minimal hsubset hclosed (h N)
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
