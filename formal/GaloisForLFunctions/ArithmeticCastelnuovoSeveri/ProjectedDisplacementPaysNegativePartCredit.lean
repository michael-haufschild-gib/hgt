import GaloisForLFunctions.RHTower.RankTraceNegativePartCredit
import GaloisForLFunctions.RHTower.Zeta23TheoremASpectralSlack

/-!
# Projected displacement pays the negative-part credit

For a Hermitian matrix `Q`, every positive contraction `U` satisfies
`-tr(UQ) ≤ tr(Q₋)`. If `Q = t(A-B)`, the projection onto `ker A` therefore
retains the imaginary evaluation energy which the real evaluation span cannot cancel.

Applied to the actual zeta Gram, the resulting lower bound is a finite sum of
squared projected imaginary evaluation vectors, including their multiplicities.
No separation or orthogonality assumption on different zero pairs is needed.
-/

noncomputable section

open Matrix RHLinalg Finset
open scoped ComplexOrder

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Orthogonal projection onto the kernel of the real-component Gram. -/
def realKernelProjection {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  specMap hA (fun x => if x = 0 then 1 else 0)

theorem realKernelProjection_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (realKernelProjection hA).PosSemidef := by
  apply specMap_posSemidef
  intro i
  split_ifs <;> norm_num

theorem realKernelProjection_complement_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (1 - realKernelProjection hA).PosSemidef := by
  have h1 : specMap hA (fun _ => (1 : ℝ)) = 1 := by unfold specMap; simp
  unfold realKernelProjection
  rw [← h1, ← specMap_sub]
  apply specMap_posSemidef
  intro i
  dsimp
  split_ifs <;> norm_num

theorem realKernelProjection_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    realKernelProjection hA * A = 0 := by
  calc
    _ = specMap hA (fun x => if x = 0 then 1 else 0) * specMap hA id := by
      simp only [specMap_id, realKernelProjection]
    _ = specMap hA ((fun x => if x = 0 then 1 else 0) * id) := (specMap_mul hA _ _).symm
    _ = specMap hA 0 := by congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]
    _ = 0 := specMap_zero hA

theorem realKernelProjection_idem {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    realKernelProjection hA * realKernelProjection hA = realKernelProjection hA := by
  unfold realKernelProjection
  rw [← specMap_mul]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

/-- A positive contraction extracts at most the full negative spectral mass. -/
theorem neg_trace_contraction_le_negPart {Q U : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (hU : U.PosSemidef) (hI : (1 - U).PosSemidef) :
    -rtrace (U * Q) ≤ rtrace (hermNegPart hQ) := by
  have hp : 0 ≤ rtrace (U * hermPosPart hQ) :=
    trace_mul_nonneg_of_posSemidef hU (hermPosPart_posSemidef hQ)
  have hm : 0 ≤ rtrace ((1 - U) * hermNegPart hQ) :=
    trace_mul_nonneg_of_posSemidef hI (hermNegPart_posSemidef hQ)
  rw [sub_mul, one_mul, rtrace_sub] at hm
  have hd : rtrace (U * Q) = rtrace (U * hermPosPart hQ) - rtrace (U * hermNegPart hQ) := by
    conv_lhs => rw [← hermPosPart_sub_hermNegPart hQ]
    rw [mul_sub, rtrace_sub]
  linarith only [hp, hm, hd]

omit [DecidableEq n] in
/-- Projecting a rank-one real Gram retains exactly its squared projected norm. -/
theorem projected_rankOne_trace {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (hUU : U * U = U) (y : n → ℂ) (hy : star y = y) :
    rtrace (U * vecMulVec y y) = ∑ i, ‖(U *ᵥ y) i‖ ^ 2 := by
  have ht : (U * vecMulVec y y).trace = star y ⬝ᵥ (U *ᵥ y) := by
    rw [mul_vecMulVec, trace_vecMulVec, hy]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have hi : star (U *ᵥ y) ⬝ᵥ (U *ᵥ y) = star y ⬝ᵥ (U *ᵥ y) := by
    rw [star_mulVec, hU.eq, ← dotProduct_mulVec, mulVec_mulVec, hUU]
  rw [rtrace, ht, ← hi]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul,
    map_sum, RCLike.re_to_complex]
  exact sum_congr rfl fun i _ => by norm_cast

/-- Imaginary mass in the kernel of the real Gram gives a negative-part lower bound. -/
theorem realKernel_trace_le_negativePart {A B Q : Matrix n n ℂ}
    (hA : A.IsHermitian) (hQ : Q.IsHermitian) (t : ℝ)
    (hQeq : Q = (t : ℂ) • (A - B)) :
    t * rtrace (realKernelProjection hA * B) ≤ rtrace (hermNegPart hQ) := by
  have h := neg_trace_contraction_le_negPart hQ
    (realKernelProjection_posSemidef hA) (realKernelProjection_complement_posSemidef hA)
  have he : -rtrace (realKernelProjection hA * Q) =
      t * rtrace (realKernelProjection hA * B) := by
    rw [hQeq, Matrix.mul_smul, mul_sub, realKernelProjection_mul, zero_sub]
    simp only [rtrace, trace_smul, trace_neg, smul_eq_mul, map_neg,
      RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_neg, neg_neg]
  rwa [he] at h

section ZeroBlocks

open Zeta23.ZeroSide

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Imaginary evaluation energy left after projecting away the real evaluation span. -/
def projectedDisplacementEnergy (D : ZeroBlockData ι n) (P : D.PairReps) : ℝ :=
  ∑ z ∈ P.R, (2 * (D.m z : ℝ)) * ∑ i,
    ‖(realKernelProjection (D.rePart_posSemidef P).isHermitian *ᵥ D.yv z) i‖ ^ 2

theorem projectedDisplacementEnergy_nonneg (D : ZeroBlockData ι n) (P : D.PairReps) :
    0 ≤ projectedDisplacementEnergy D P := by
  exact sum_nonneg fun z _ => mul_nonneg (by positivity) (sum_nonneg fun i _ => sq_nonneg _)

/-- The projected trace is the explicit finite displacement sum. -/
theorem realKernel_trace_imPart (D : ZeroBlockData ι n) (P : D.PairReps) :
    rtrace (realKernelProjection (D.rePart_posSemidef P).isHermitian * D.imPart P) =
      projectedDisplacementEnergy D P := by
  let U := realKernelProjection (D.rePart_posSemidef P).isHermitian
  have hU := (realKernelProjection_posSemidef (D.rePart_posSemidef P).isHermitian).isHermitian
  have hUU := realKernelProjection_idem (D.rePart_posSemidef P).isHermitian
  change rtrace (U * D.imPart P) = _
  unfold ZeroBlockData.imPart projectedDisplacementEnergy
  simp only [Matrix.mul_sum, rtrace, trace_sum, map_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_smul, trace_smul]
  have hz := projected_rankOne_trace hU hUU (D.yv z) (D.star_yv z)
  change (U * vecMulVec (D.yv z) (D.yv z)).trace.re = _ at hz
  simp only [smul_eq_mul, RCLike.re_to_complex, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hz]

/-- The full off-line Gram credits the displacement surviving all real-pair directions. -/
theorem blockQ_negativePart_credit_ge_projectedDisplacement
    (D : ZeroBlockData ι n) (P : D.PairReps) (c : ℝ) :
    2 * c⁻¹ * projectedDisplacementEnergy D P ≤
      2 * rtrace (hermNegPart (D.blockQ_isHermitian c)) := by
  have h := realKernel_trace_le_negativePart (D.rePart_posSemidef P).isHermitian
    (D.blockQ_isHermitian c) c⁻¹ (D.blockQ_eq P c)
  rw [realKernel_trace_imPart] at h
  linarith only [h]

end ZeroBlocks

open Zeta23 Zeta23.ZeroSide

/-- The imaginary evaluation vector written explicitly in the horizontal displacement
`Re ρ − 1/2` and ordinate `Im ρ`. -/
def zetaDisplacementVector (P : Params) (T : ℝ) (ρ : ℂ) : Fin (P.d T) → ℂ :=
  fun k => ((P.phiHat T ((ρ.im : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I -
    (P.tau T k : ℂ))).im : ℂ)

theorem zeta_block_yv_eq_displacement (P : Params) (T : ℝ) (ρ : ZI zetaZeroConfig T) :
    (blockData zetaZeroConfig T P (fun z => GzGp.phiHat_conj P T z)).yv ρ =
      zetaDisplacementVector P T (ρ : ℂ) := by
  have hγ : gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) -
      ((((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ)) * Complex.I := by
    apply Complex.ext <;> simp [gammaOf]
  funext k
  simp only [ZeroBlockData.yv, blockData, mkData_v, evalVec, hγ, zetaDisplacementVector]

/-- Projected displacement of the actual zeta zeros in the prescribed bandwidth Gram. -/
def zetaProjectedDisplacementEnergy (P : Params) (T : ℝ) : ℝ :=
  projectedDisplacementEnergy
    (blockData zetaZeroConfig T P (fun z => GzGp.phiHat_conj P T z))
    (mkPairReps zetaZeroConfig T (evalVec zetaZeroConfig T P)
      (evalVec_reflect (fun z => GzGp.phiHat_conj P T z)))

/-- The actual credit is an explicit finite sum depending on each horizontal displacement. -/
theorem zetaProjectedDisplacementEnergy_eq (P : Params) (T : ℝ) :
    let D := blockData zetaZeroConfig T P (fun z => GzGp.phiHat_conj P T z)
    let R := mkPairReps zetaZeroConfig T (evalVec zetaZeroConfig T P)
      (evalVec_reflect (fun z => GzGp.phiHat_conj P T z))
    let U := realKernelProjection (D.rePart_posSemidef R).isHermitian
    zetaProjectedDisplacementEnergy P T =
      ∑ ρ ∈ R.R, (2 * (D.m ρ : ℝ)) * ∑ i,
        ‖(U *ᵥ zetaDisplacementVector P T (ρ : ℂ)) i‖ ^ 2 := by
  dsimp only
  unfold zetaProjectedDisplacementEnergy projectedDisplacementEnergy
  refine sum_congr rfl fun ρ _ => ?_
  rw [zeta_block_yv_eq_displacement]

/-- Actual zeta negative-part credit, with no unproved condition on its zero configuration. -/
theorem zeta_negativePart_credit_ge_projectedDisplacement (P : Params) (T : ℝ) :
    2 * (P.a T * P.L T ^ 2)⁻¹ * zetaProjectedDisplacementEnergy P T ≤
      2 * rtrace (hermNegPart
        (hatQ_isHermitian zetaZeroConfig T P (fun z => GzGp.phiHat_conj P T z))) :=
  blockQ_negativePart_credit_ge_projectedDisplacement _ _ _

/-- The actual zero-side slack retains the projected displacement credit at every height. -/
theorem zeta_zeroSideSlack_ge_projectedDisplacement (P : Params) (T : ℝ) :
    2 * (P.a T * P.L T ^ 2)⁻¹ * zetaProjectedDisplacementEnergy P T ≤
      RHTower.zeroSideSlack zetaZeroConfig P T := by
  have hc := zeta_negativePart_credit_ge_projectedDisplacement P T
  have hp := RHTower.posSlack_nonneg
    (hatQ_isHermitian zetaZeroConfig T P (fun z => GzGp.phiHat_conj P T z)) 2
  have ho := RHTower.onLineParsevalDefect_nonneg zetaZeroConfig P T
  unfold RHTower.zeroSideSlack RHTower.offLineSpectralSlack
  linarith only [hc, hp, ho]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.neg_trace_contraction_le_negPart
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zetaProjectedDisplacementEnergy_eq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zeta_negativePart_credit_ge_projectedDisplacement
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zeta_zeroSideSlack_ge_projectedDisplacement
