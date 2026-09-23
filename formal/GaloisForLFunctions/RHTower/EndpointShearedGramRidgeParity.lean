import Mathlib

/-!
# Endpoint-sheared Gram ridge parity

For a finite source packet in a complex inner product space, its two-frequency transform in the
coordinates

`a * residue m + b * (residue n - residue m)`

is exactly the Gram entry between the frequency packets at `b - a` and `b`.  This gives the
diagonal norm law, positive semidefiniteness, and Cauchy--Schwarz without any estimate.

The endpoint-ridge equality needs more than Hermitian symmetry: it needs the physical source Gram
to be real.  Under that exact hypothesis the whole transform is invariant under the endpoint swap
`b -> a - b`, and every endpoint-swap-odd channel annihilates exactly.

These are finite `[BRIDGE]` theorems.  They make no asymptotic or RH claim.
-/

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

namespace RHTower

variable {R : Type*} [Fintype R] [CommRing R]
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Frequency packet associated with a finite source family and an additive character. -/
def endpointFrequencyPacket
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E) (j : R) : E :=
  ∑ n, χ (j * residue n) • x n

/-- Two-frequency source transform in the endpoint-sheared coordinates. -/
def endpointShearedDoubleTransform
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E) (a b : R) : ℂ :=
  ∑ m, ∑ n,
    χ (a * residue m + b * (residue n - residue m)) * inner ℂ (x m) (x n)

omit [Fintype R] in
/-- Separated-frequency form of the sheared phase. -/
theorem endpointShearedDoubleTransform_eq_separated
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E) (a b : R) :
    endpointShearedDoubleTransform χ residue x a b =
      ∑ m, ∑ n,
        χ ((a - b) * residue m + b * residue n) * inner ℂ (x m) (x n) := by
  classical
  unfold endpointShearedDoubleTransform
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  rw [show a * residue m + b * (residue n - residue m) =
      (a - b) * residue m + b * residue n by ring]

omit [Fintype R] in
/-- **Sheared Gram identity.**  With mathlib's conjugate-linear-first convention, the raw double
transform is the inner product of the packets at frequencies `b - a` and `b`. -/
theorem endpointShearedDoubleTransform_eq_inner_frequencyPacket
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (a b : R) :
    endpointShearedDoubleTransform χ residue x a b =
      inner ℂ (endpointFrequencyPacket χ residue x (b - a))
        (endpointFrequencyPacket χ residue x b) := by
  classical
  unfold endpointShearedDoubleTransform endpointFrequencyPacket
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  have hphase :
      χ (a * residue m + b * (residue n - residue m)) =
        star (χ ((b - a) * residue m)) * χ (b * residue n) := by
    calc
      χ (a * residue m + b * (residue n - residue m)) =
          χ (-((b - a) * residue m) + b * residue n) := by
            congr 1
            ring
      _ = χ (-((b - a) * residue m)) * χ (b * residue n) :=
        AddChar.map_add_eq_mul χ _ _
      _ = star (χ ((b - a) * residue m)) * χ (b * residue n) := by
        rw [hχstar]
  rw [hphase, starRingEnd_apply]
  ac_rfl

omit [Fintype R] in
/-- The zero-shear diagonal is exactly the squared norm of one frequency packet. -/
theorem endpointShearedDoubleTransform_zero_eq_norm_sq
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (b : R) :
    endpointShearedDoubleTransform χ residue x 0 b =
      ((‖endpointFrequencyPacket χ residue x b‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [endpointShearedDoubleTransform_eq_inner_frequencyPacket χ residue x hχstar]
  simp only [sub_zero]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

omit [Fintype R] in
/-- Cauchy--Schwarz in the original sheared coordinates. -/
theorem norm_endpointShearedDoubleTransform_le
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (a b : R) :
    ‖endpointShearedDoubleTransform χ residue x a b‖ ≤
      ‖endpointFrequencyPacket χ residue x (b - a)‖ *
        ‖endpointFrequencyPacket χ residue x b‖ := by
  rw [endpointShearedDoubleTransform_eq_inner_frequencyPacket χ residue x hχstar]
  exact norm_inner_le_norm _ _

/-- The ordinary Gram matrix obtained by undoing the endpoint shear. -/
def endpointShearedGramMatrix
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E) : Matrix R R ℂ :=
  fun j k => endpointShearedDoubleTransform χ residue x (k - j) k

omit [Fintype R] in
/-- Every entry of the unsheared matrix is the corresponding frequency-packet inner product. -/
theorem endpointShearedGramMatrix_apply
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (j k : R) :
    endpointShearedGramMatrix χ residue x j k =
      inner ℂ (endpointFrequencyPacket χ residue x j)
        (endpointFrequencyPacket χ residue x k) := by
  rw [endpointShearedGramMatrix,
    endpointShearedDoubleTransform_eq_inner_frequencyPacket χ residue x hχstar]
  rw [show k - (k - j) = j by ring]

omit [Fintype R] in
/-- The unsheared matrix is literally mathlib's Gram matrix. -/
theorem endpointShearedGramMatrix_eq_gram
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) :
    endpointShearedGramMatrix χ residue x =
      Matrix.gram ℂ (endpointFrequencyPacket χ residue x) := by
  ext j k
  rw [Matrix.gram_apply]
  exact endpointShearedGramMatrix_apply χ residue x hχstar j k

/-- The endpoint-unsheared response matrix is positive semidefinite. -/
theorem endpointShearedGramMatrix_posSemidef
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) :
    (endpointShearedGramMatrix χ residue x).PosSemidef := by
  rw [endpointShearedGramMatrix_eq_gram χ residue x hχstar]
  exact Matrix.posSemidef_gram ℂ _

/-- A finite linear combination of frequency packets. -/
def endpointFrequencyPacketCombination
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E) (c : R → ℂ) : E :=
  ∑ j, c j • endpointFrequencyPacket χ residue x j

/-- Exact quadratic-form identity before reading the self-inner-product as a squared norm. -/
theorem endpointShearedGramMatrix_quadratic_eq_inner
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (c : R → ℂ) :
    (∑ j, ∑ k,
      star (c j) * endpointShearedGramMatrix χ residue x j k * c k) =
        inner ℂ (endpointFrequencyPacketCombination χ residue x c)
          (endpointFrequencyPacketCombination χ residue x c) := by
  classical
  simp_rw [endpointShearedGramMatrix_apply χ residue x hχstar]
  unfold endpointFrequencyPacketCombination
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  rw [starRingEnd_apply]
  ac_rfl

/-- The Gram quadratic form is exactly the squared norm of the packet combination. -/
theorem endpointShearedGramMatrix_quadratic_eq_norm_sq
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hχstar : ∀ t : R, star (χ t) = χ (-t)) (c : R → ℂ) :
    (∑ j, ∑ k,
      star (c j) * endpointShearedGramMatrix χ residue x j k * c k) =
        ((‖endpointFrequencyPacketCombination χ residue x c‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [endpointShearedGramMatrix_quadratic_eq_inner χ residue x hχstar]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Endpoint swap `b -> a - b` as an involutive permutation of the finite frequency ring. -/
def endpointSwapEquiv (a : R) : R ≃ R where
  toFun b := a - b
  invFun b := a - b
  left_inv b := by simp
  right_inv b := by simp

/-- An endpoint-swap-odd scalar channel annihilates every endpoint-swap-even response. -/
theorem sum_endpointSwapOdd_mul_even_eq_zero
    (a : R) (weight response : R → ℂ)
    (hodd : ∀ b, weight (a - b) = -weight b)
    (heven : ∀ b, response (a - b) = response b) :
    ∑ b, weight b * response b = 0 := by
  classical
  let e := endpointSwapEquiv a
  have hreindex :
      (∑ b, weight (a - b) * response (a - b)) =
        ∑ b, weight b * response b := by
    simpa [e, endpointSwapEquiv] using
      e.sum_comp (fun b => weight b * response b)
  have hneg :
      (∑ b, weight (a - b) * response (a - b)) =
        -(∑ b, weight b * response b) := by
    calc
      (∑ b, weight (a - b) * response (a - b)) =
          ∑ b, -(weight b * response b) := by
            apply Fintype.sum_congr
            intro b
            rw [hodd b, heven b]
            ring
      _ = -(∑ b, weight b * response b) := by
        rw [Finset.sum_neg_distrib]
  have hself : -(∑ b, weight b * response b) =
      ∑ b, weight b * response b := hneg.symm.trans hreindex
  exact neg_eq_self.mp hself

omit [Fintype R] in
/-- **Full real-Gram ridge parity.**  If all source Gram entries are real (equivalently, the
Hermitian Gram is also symmetric), then the complete sheared response is invariant under the
endpoint swap `b -> a - b`. -/
theorem endpointShearedDoubleTransform_endpointSwap
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hrealGram : ∀ m n, inner ℂ (x m) (x n) = inner ℂ (x n) (x m))
    (a b : R) :
    endpointShearedDoubleTransform χ residue x a b =
      endpointShearedDoubleTransform χ residue x a (a - b) := by
  classical
  calc
    endpointShearedDoubleTransform χ residue x a b =
        ∑ m, ∑ n,
          χ ((a - b) * residue m + b * residue n) * inner ℂ (x m) (x n) :=
      endpointShearedDoubleTransform_eq_separated χ residue x a b
    _ = ∑ m, ∑ n,
          χ ((a - b) * residue n + b * residue m) * inner ℂ (x n) (x m) := by
      exact Finset.sum_comm
    _ = ∑ m, ∑ n,
          χ ((a - (a - b)) * residue m + (a - b) * residue n) *
            inner ℂ (x m) (x n) := by
      apply Fintype.sum_congr
      intro m
      apply Fintype.sum_congr
      intro n
      rw [hrealGram n m]
      rw [show (a - b) * residue n + b * residue m =
          (a - (a - b)) * residue m + (a - b) * residue n by ring]
    _ = endpointShearedDoubleTransform χ residue x a (a - b) :=
      (endpointShearedDoubleTransform_eq_separated χ residue x a (a - b)).symm

omit [Fintype R] in
/-- The two endpoint ridges are equal under the real-Gram hypothesis. -/
theorem endpointShearedDoubleTransform_left_ridge_eq_right_ridge
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hrealGram : ∀ m n, inner ℂ (x m) (x n) = inner ℂ (x n) (x m))
    (a : R) :
    endpointShearedDoubleTransform χ residue x a 0 =
      endpointShearedDoubleTransform χ residue x a a := by
  simpa using endpointShearedDoubleTransform_endpointSwap χ residue x hrealGram a 0

/-- Every endpoint-swap-odd channel of a real-Gram sheared response vanishes exactly. -/
theorem sum_endpointSwapOdd_mul_endpointShearedDoubleTransform_eq_zero
    (χ : AddChar R ℂ) (residue : ι → R) (x : ι → E)
    (hrealGram : ∀ m n, inner ℂ (x m) (x n) = inner ℂ (x n) (x m))
    (a : R) (weight : R → ℂ) (hodd : ∀ b, weight (a - b) = -weight b) :
    ∑ b, weight b * endpointShearedDoubleTransform χ residue x a b = 0 := by
  apply sum_endpointSwapOdd_mul_even_eq_zero a weight
    (fun b => endpointShearedDoubleTransform χ residue x a b) hodd
  intro b
  exact (endpointShearedDoubleTransform_endpointSwap χ residue x hrealGram a b).symm

/-! ### Sharpness of the real-Gram hypothesis

Character unitarity and Hermitian symmetry of the Gram kernel do not by themselves identify the
two endpoint ridges.  A two-point complex source over `ZMod 2` separates them. -/

/-- The nontrivial additive character of `ZMod 2`. -/
def signAddChar : AddChar (ZMod 2) ℂ where
  toFun a := if a = 0 then 1 else -1
  map_zero_eq_one' := if_pos rfl
  map_add_eq_mul' := by
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    intro a b
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
      simp only [show ((0 : ZMod 2) + 0) = 0 from by decide,
        show ((0 : ZMod 2) + 1) = 1 from by decide,
        show ((1 : ZMod 2) + 0) = 1 from by decide,
        show ((1 : ZMod 2) + 1) = 0 from by decide] <;>
      norm_num [show ¬((1 : ZMod 2) = 0) from by decide]

@[simp]
theorem signAddChar_apply (a : ZMod 2) : signAddChar a = if a = 0 then 1 else -1 := rfl

/-- Residues of the two-point separating source. -/
def twoPointResidue : Fin 2 → ZMod 2 := ![0, 1]

/-- A two-point complex source whose Gram kernel is not real. -/
def twoPointSource : Fin 2 → ℂ := ![1, Complex.I]

theorem twoPoint_left_ridge :
    endpointShearedDoubleTransform signAddChar twoPointResidue twoPointSource 1 0 =
      2 * Complex.I := by
  simp only [endpointShearedDoubleTransform, Fin.sum_univ_two, twoPointResidue, twoPointSource,
    Matrix.cons_val_zero, Matrix.cons_val_one, signAddChar_apply,
    RCLike.inner_apply]
  norm_num [Complex.ext_iff]

theorem twoPoint_right_ridge :
    endpointShearedDoubleTransform signAddChar twoPointResidue twoPointSource 1 1 =
      -(2 * Complex.I) := by
  simp only [endpointShearedDoubleTransform, Fin.sum_univ_two, twoPointResidue, twoPointSource,
    Matrix.cons_val_zero, Matrix.cons_val_one, signAddChar_apply,
    RCLike.inner_apply]
  norm_num [Complex.ext_iff]

/-- **Sharpness.**  Without the real-Gram hypothesis the two endpoint ridges differ. -/
theorem twoPoint_left_ridge_ne_right_ridge :
    endpointShearedDoubleTransform signAddChar twoPointResidue twoPointSource 1 0 ≠
      endpointShearedDoubleTransform signAddChar twoPointResidue twoPointSource 1 1 := by
  rw [twoPoint_left_ridge, twoPoint_right_ridge]
  norm_num [Complex.ext_iff]

end RHTower
