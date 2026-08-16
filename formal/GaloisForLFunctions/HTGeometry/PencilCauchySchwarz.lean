import GaloisForLFunctions.HTGeometry.FeatureKernelResolventBound
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery

/-!
# The pencil Cauchy--Schwarz bound

A pencil `B = ∑ᵢ cᵢ Bᵢ` spreads a positive state no further than its coefficient norm allows:

`B X B* ≤ ‖c‖₂² ∑ᵢ Bᵢ X Bᵢ*`  for `X > 0`.

The proof is Cauchy--Schwarz in the inner product that `X` defines.  Writing `X = S S` with `S` the
positive square root, the quadratic form of `M X M*` at `v` is the squared length of `S M* v`, the
pencil sends that vector to `∑ᵢ c̄ᵢ (S Bᵢ* v)`, and coordinatewise Cauchy--Schwarz bounds its squared
length by `‖c‖₂²` times the sum of the squared lengths.  No positivity ordering is needed beyond the
existence of the square root, and the scalar case is the usual inequality.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-! ## The scalar inequality -/

section Normed

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The pencil Cauchy--Schwarz bound.** -/
theorem norm_sum_smul_sq_le (c : ι → ℂ) (w : ι → E) :
    ‖∑ i, c i • w i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * (∑ i, ‖w i‖ ^ 2) := by
  have htri : ‖∑ i, c i • w i‖ ≤ ∑ i, ‖c i‖ * ‖w i‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun i _ => le_of_eq (norm_smul (c i) (w i))
  have hnn : (0 : ℝ) ≤ ∑ i, ‖c i‖ * ‖w i‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hsq : ‖∑ i, c i • w i‖ ^ 2 ≤ (∑ i, ‖c i‖ * ‖w i‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖∑ i, c i • w i‖ := norm_nonneg _
    nlinarith [htri, h0, hnn]
  refine le_trans hsq ?_
  exact sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖c i‖) fun i => ‖w i‖

/-- The unit-coefficient case: a plain sum of `k` displacements is at most `k` times the summed
squares. -/
theorem norm_sum_sq_le_card_mul (w : ι → E) :
    ‖∑ i, w i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖w i‖ ^ 2 := by
  have h := norm_sum_smul_sq_le (fun _ : ι => (1 : ℂ)) w
  simp only [one_smul, norm_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at h
  exact h

end Normed

/-! ## Quadratic forms of a congruence -/

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- The quadratic form of `Nᴴ N` is the squared length of `N v`. -/
theorem quadForm_conjTranspose_mul_self (N : Matrix d d ℂ) (v : d → ℂ) :
    star v ⬝ᵥ ((Nᴴ * N) *ᵥ v) = ((∑ l, ‖(N *ᵥ v) l‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

omit [DecidableEq d] in
/-- A congruence by `M` through a squared factor is the squared length of `S Mᴴ v`. -/
theorem quadForm_congruence {X S : Matrix d d ℂ} (hS : Sᴴ = S) (hSS : S * S = X)
    (M : Matrix d d ℂ) (v : d → ℂ) :
    star v ⬝ᵥ ((M * X * Mᴴ) *ᵥ v) = ((∑ l, ‖((S * Mᴴ) *ᵥ v) l‖ ^ 2 : ℝ) : ℂ) := by
  have hfac : M * X * Mᴴ = (S * Mᴴ)ᴴ * (S * Mᴴ) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS, ← hSS]
    simp [Matrix.mul_assoc]
  rw [hfac, quadForm_conjTranspose_mul_self]

/-! ## The pencil inequality -/

variable {ι : Type*} [Fintype ι]

omit [DecidableEq d] in
/-- The square-root image of a pencil is the pencil of square-root images. -/
theorem sqrt_pencil_mulVec (S : Matrix d d ℂ) (c : ι → ℂ) (B : ι → Matrix d d ℂ) (v : d → ℂ)
    (l : d) :
    ((S * (∑ i, c i • B i)ᴴ) *ᵥ v) l
      = ∑ i, (starRingEnd ℂ) (c i) • ((S * (B i)ᴴ) *ᵥ v) l := by
  have hconj : (∑ i, c i • B i)ᴴ = ∑ i, (starRingEnd ℂ) (c i) • (B i)ᴴ := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.conjTranspose_smul (c i) (B i)
  rw [hconj, Finset.mul_sum]
  have hsmul : ∀ i : ι, S * ((starRingEnd ℂ) (c i) • (B i)ᴴ)
      = (starRingEnd ℂ) (c i) • (S * (B i)ᴴ) := fun i => Matrix.mul_smul S _ _
  rw [Finset.sum_congr rfl fun i _ => hsmul i, Matrix.sum_mulVec]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_mulVec, Pi.smul_apply]

/-- **The pencil Cauchy--Schwarz inequality for quadratic forms.**  The state spread by a pencil is
at most the squared coefficient norm times the total state spread by the members. -/
theorem quadForm_pencil_le {X : Matrix d d ℂ} (hX : X.PosDef) (c : ι → ℂ)
    (B : ι → Matrix d d ℂ) (v : d → ℂ) :
    star v ⬝ᵥ (((∑ i, c i • B i) * X * (∑ i, c i • B i)ᴴ) *ᵥ v)
      ≤ ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ)
          * ∑ i, star v ⬝ᵥ ((B i * X * (B i)ᴴ) *ᵥ v) := by
  set S : Matrix d d ℂ := CFC.sqrt X with hSdef
  have hSpd : S.PosDef := positiveMatrixSqrt_posDef hX
  have hS : Sᴴ = S := hSpd.isHermitian.eq
  have hSS : S * S = X := positiveMatrixSqrt_mul_self hX
  have hmem : ∀ i : ι, star v ⬝ᵥ ((B i * X * (B i)ᴴ) *ᵥ v)
      = ((∑ l, ‖((S * (B i)ᴴ) *ᵥ v) l‖ ^ 2 : ℝ) : ℂ) :=
    fun i => quadForm_congruence hS hSS (B i) v
  have hpen := quadForm_congruence hS hSS (∑ i, c i • B i) v
  -- both sides are real; compare the real numbers
  have hreal : ∑ l, ‖((S * (∑ i, c i • B i)ᴴ) *ᵥ v) l‖ ^ 2
      ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ∑ l, ‖((S * (B i)ᴴ) *ᵥ v) l‖ ^ 2 := by
    have hpoint : ∀ l : d, ‖((S * (∑ i, c i • B i)ᴴ) *ᵥ v) l‖ ^ 2
        ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖((S * (B i)ᴴ) *ᵥ v) l‖ ^ 2 := by
      intro l
      rw [sqrt_pencil_mulVec S c B v l]
      have h := norm_sum_smul_sq_le (E := ℂ) (fun i => (starRingEnd ℂ) (c i))
        fun i => ((S * (B i)ᴴ) *ᵥ v) l
      simpa using h
    refine le_trans (Finset.sum_le_sum fun l _ => hpoint l) ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hpen, Finset.sum_congr rfl fun i _ => hmem i, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
  exact Complex.real_le_real.mpr hreal

omit [DecidableEq d] in
/-- A congruence by `M` preserves hermitianity. -/
theorem isHermitian_congruence {X : Matrix d d ℂ} (hX : Xᴴ = X) (M : Matrix d d ℂ) :
    (M * X * Mᴴ)ᴴ = M * X * Mᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX]
  simp [Matrix.mul_assoc]

/-- **The pencil certificate in Loewner order.**  For a positive-definite state `X`,

`B X Bᴴ ≤ ‖c‖₂² ∑ᵢ Bᵢ X Bᵢᴴ`   where `B = ∑ᵢ cᵢ Bᵢ`. -/
theorem posSemidef_pencil_bound {X : Matrix d d ℂ} (hX : X.PosDef) (c : ι → ℂ)
    (B : ι → Matrix d d ℂ) :
    (((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) • (∑ i, B i * X * (B i)ᴴ)
      - (∑ i, c i • B i) * X * (∑ i, c i • B i)ᴴ).PosSemidef := by
  have hXh : Xᴴ = X := hX.isHermitian.eq
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show (_ : Matrix d d ℂ)ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => isHermitian_congruence hXh (B i),
      isHermitian_congruence hXh (∑ i, c i • B i)]
    congr 1
    simp [Complex.conj_ofReal]
  · intro v
    have hkey := quadForm_pencil_le hX c B v
    have hexp : star v ⬝ᵥ ((((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) • (∑ i, B i * X * (B i)ᴴ)
        - (∑ i, c i • B i) * X * (∑ i, c i • B i)ᴴ) *ᵥ v)
        = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) * (∑ i, star v ⬝ᵥ ((B i * X * (B i)ᴴ) *ᵥ v))
          - star v ⬝ᵥ (((∑ i, c i • B i) * X * (∑ i, c i • B i)ᴴ) *ᵥ v) := by
      simp [Matrix.sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
        Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
    rw [hexp, sub_nonneg]
    exact hkey

end GaloisForLFunctions.HTGeometry
