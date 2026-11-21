import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

/-! # Rounding the diagonal of a unitary near a spectral phase packet -/
open Matrix Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance spectralCStar : CStarAlgebra (Matrix ι ι ℂ) where

omit [Nonempty ι] in
private theorem diagonal_overlap (f : ι → ℂ) (hf : ∀ i, ‖f i‖=1)
    (B : Matrix ι ι ℂ) (hB : B ∈ unitary (Matrix ι ι ℂ)) (i : ι) :
    2 - 2*(f i * conj (B i i)).re ≤ ‖diagonal f - B‖^2 := by
  let A := diagonal f
  let Z := A-B
  have hA : star A*A=1 := by
    ext j k
    by_cases h : j=k
    · subst k
      simp [A,Matrix.star_eq_conjTranspose,Complex.conj_mul',hf]
    · simp [A,Matrix.star_eq_conjTranspose,h]
  have hgram : star Z*Z = 1+1-star A*B-star B*A := by
    dsimp only [Z]
    rw [star_sub,sub_mul,mul_sub,mul_sub,hA,(Unitary.mem_iff.mp hB).1]
    abel
  have hentry := (Complex.re_le_norm ((star Z*Z) i i)).trans (norm_entry_le_l2_opNorm _ i i)
  rw [CStarRing.norm_star_mul_self,←sq,hgram] at hentry
  change _ ≤ ‖Z‖^2
  calc
    _ = ((1+1-star A*B-star B*A) i i).re := by
      simp [A,Matrix.star_eq_conjTranspose,Complex.mul_re]
      ring
    _ ≤ _ := hentry

/-- Below squared error two, rounding every diagonal entry to its phase
retains every diagonal unitary captured by the original unitary, even
when the approximating global phase depends on the target. -/
theorem rounded_diagonal_chord (f : ι → ℂ) (hf : ∀ i, ‖f i‖=1)
    (W : Matrix ι ι ℂ) (hW : W ∈ unitary (Matrix ι ι ℂ))
    (c : ℂ) (hc : ‖c‖=1) (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε^2 < 2)
    (h : ‖diagonal f-c • W‖ ≤ ε) (i : ι) :
    ‖f i-c*Complex.exp (((W i i).arg:ℂ)*Complex.I)‖ ≤ ε := by
  let q := Complex.exp (((W i i).arg:ℂ)*Complex.I)
  have hq : ‖q‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hpolar : (‖W i i‖:ℂ)*q = W i i := Complex.norm_mul_exp_arg_mul_I _
  have hcW : c • W ∈ unitary (Matrix ι ι ℂ) := by
    have hc' : conj c*c=1 := by rw [Complex.conj_mul',hc]; norm_num
    apply Unitary.mem_iff.mpr
    constructor <;> simp [star_smul,smul_smul,
      (Unitary.mem_iff.mp hW).1,(Unitary.mem_iff.mp hW).2,hc',mul_comm c (conj c)]
  have hl := (diagonal_overlap f hf (c • W) hcW i).trans (pow_le_pow_left₀ (norm_nonneg _) h 2)
  let y := (f i*conj (c*q)).re
  have hid : (f i*conj ((c • W) i i)).re = ‖W i i‖*y := by
    change (f i*conj (c*W i i)).re = _
    have he : f i*conj (c*W i i) = (‖W i i‖:ℂ)*(f i*conj (c*q)) := by
      conv_lhs => rw [← hpolar]
      simp only [map_mul,Complex.conj_ofReal]
      ring
    rw [he,Complex.re_ofReal_mul]
  rw [hid] at hl
  have hy : 0 ≤ y := by
    by_contra! hn
    linarith only [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (W i i)) hn.le,hl,hsmall]
  have hw : ‖W i i‖ ≤ 1 := (norm_entry_le_l2_opNorm W i i).trans_eq (CStarRing.norm_of_mem_unitary hW)
  have hinner := mul_le_of_le_one_left hy hw
  apply (sq_le_sq₀ (norm_nonneg _) hε).mp
  change ‖f i-c*q‖^2 ≤ _
  rw [Complex.sq_norm,Complex.normSq_sub,← Complex.sq_norm,← Complex.sq_norm,
    hf,norm_mul,hc,hq]
  change 1^2+(1*1)^2-2*y ≤ _
  linarith only [hl,hinner]

#print axioms rounded_diagonal_chord
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
