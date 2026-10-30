import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateTools

/-!
# Piecewise certificates: the common piece matrix

For a constant matrix `X` the piece matrix is
`W(q) = E(q) − q⁶·8000(2q−3)²e^{-529q/50}·diag(ρ̃) + 8q⁷(2q−3)²·X`. If `W(q)` is positive
semidefinite then the native odd form at `c = B(1/q)y` is at least `−K(q)·8q(2q−3)²·yᵀXy`.
-/

open Polynomial
namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentralTail ThetaCuspOddFourCentralEntries ThetaCuspOddFourCentralBound
open ThetaCuspOddFourCertificateTools

/-- Expand a coefficient-list polynomial `∑_{e<n} c.getD e 0 * t^e` into its terms. -/
macro "poly_expand" : tactic =>
  `(tactic| simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ,
    List.getD_cons_zero])

/-- Expand a coefficient-list polynomial and normalize its numerals. -/
macro "poly_norm" : tactic => `(tactic| (poly_expand <;> norm_num))

/-- The piece matrix with compensation `X`. -/
def pieceW (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  centralEntryMat q i j -
    (if i = j then q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight i) else 0) +
    8*q^7*(2*q-3)^2*X i j

theorem bm_00 : basisMajorant 0 0 = 1 := rfl
theorem bm_01 : basisMajorant 0 1 = 1 := rfl
theorem bm_02 : basisMajorant 0 2 = 5/4 := rfl
theorem bm_03 : basisMajorant 0 3 = 5/4 := rfl
theorem bm_10 : basisMajorant 1 0 = 0 := rfl
theorem bm_11 : basisMajorant 1 1 = 1/72 := rfl
theorem bm_12 : basisMajorant 1 2 = 5/144 := rfl
theorem bm_13 : basisMajorant 1 3 = 5/96 := rfl
theorem bm_20 : basisMajorant 2 0 = 0 := rfl
theorem bm_21 : basisMajorant 2 1 = 0 := rfl
theorem bm_22 : basisMajorant 2 2 = 1/6912 := rfl
theorem bm_23 : basisMajorant 2 3 = 1/2304 := rfl
theorem bm_30 : basisMajorant 3 0 = 0 := rfl
theorem bm_31 : basisMajorant 3 1 = 0 := rfl
theorem bm_32 : basisMajorant 3 2 = 0 := rfl
theorem bm_33 : basisMajorant 3 3 = 1/1161216 := rfl

theorem tailWeight_0 : tailWeight 0 = ((10465499600:ℝ)/59049) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_1 : tailWeight 1 = ((4814744136400:ℝ)/531441) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_2 : tailWeight 2 = ((2570430941234500:ℝ)/4782969) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_3 : tailWeight 3 = ((3308571812705231500:ℝ)/129140163) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

/-- A positive semidefinite piece matrix bounds the native odd form below. -/
theorem nativeOddForm_ge_of_piece {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (X : Fin 4 → Fin 4 → ℝ) (y : Fin 4 → ℝ)
    (hW : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (thetaCuspSingleAtomReflectionScale 1 x) X i j) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x ≥
      -(4*q^2*Real.exp (x-2*q)*(8*q*(2*q-3)^2)*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j) := by
  intro q c
  have h := nativeOddForm_ge_central hq y
  have hq0 : 0 < q := by linarith
  have hsplit : (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q X i j) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j) -
        q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*∑ k : Fin 4, tailWeight k * y k^2) +
        8*q^7*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j := by
    simp only [pieceW, Fin.sum_univ_four, Fin.isValue, if_true]
    simp
    ring
  rw [hsplit] at hW
  have hK : 0 ≤ 4*q^2*Real.exp (x-2*q) := by positivity
  have hq6 : 0 < q^6 := by positivity
  have key : -(8*q*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j)/q^6 -
        8000*(2*q-3)^2*Real.exp (-(529/50)*q)*∑ k : Fin 4, tailWeight k * y k^2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hq6]
    nlinarith [hW]
  calc -(4*q^2*Real.exp (x-2*q)*(8*q*(2*q-3)^2)*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j)
      = 4*q^2*Real.exp (x-2*q)*(-(8*q*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left key hK).trans h


/-- Assembly of one entry from its component bounds. -/
theorem entry_assemble {W a1 a2 a3 a4 a5 a6 m1 m2 m5 A B t r1 r2 r3 r4 r5 r6 r7 R : ℝ}
    (hW : W = a1 + a2 + a3 + a4 + a5 + a6) (h1 : |a1 - m1| ≤ r1) (h2 : |a2 - m2| ≤ r2)
    (h3 : |a3| ≤ r3) (h4 : |a4| ≤ r4) (h5 : |a5 - m5| ≤ r5) (h6 : |a6| ≤ r6)
    (h7 : |m1 + m2 + m5 - (A + t*B)| ≤ r7) (hR : r1 + r2 + r3 + r4 + r5 + r6 + r7 ≤ R) :
    |W - (A + t*B)| ≤ R := by
  rw [hW]
  have e : a1 + a2 + a3 + a4 + a5 + a6 - (A + t*B) =
      (a1 - m1) + (a2 - m2) + a3 + a4 + (a5 - m5) + a6 + (m1 + m2 + m5 - (A + t*B)) := by ring
  rw [e]
  calc _ ≤ |a1 - m1| + |a2 - m2| + |a3| + |a4| + |a5 - m5| + |a6| + |m1 + m2 + m5 - (A + t*B)| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl
    _ ≤ _ := by linarith

/-- The affine rounding step: `|α + tβ| ≤ |α| + ρ|β|` on `|t| ≤ ρ`. -/
theorem affine_round {α β t ρ : ℝ} (ht : |t| ≤ ρ) : |α + t*β| ≤ |α| + ρ*|β| := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)

/-- A scaled affine model of a polynomial factor. -/
theorem scaled_affine {D d0 d1 rD X t : ℝ} (h : |D - d0 - d1*t| ≤ rD) :
    |D*X - (d0 + d1*t)*X| ≤ |X| * rD := by
  rw [show D*X - (d0 + d1*t)*X = (D - d0 - d1*t)*X by ring, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The symmetric `4 × 4` matrix with the given upper triangle. -/
def sym4 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![a00, a01, a02, a03], ![a01, a11, a12, a13], ![a02, a12, a22, a23], ![a03, a13, a23, a33]]

theorem sym4_00 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 0 0 = a00 := rfl
theorem sym4_01 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 0 1 = a01 := rfl
theorem sym4_02 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 0 2 = a02 := rfl
theorem sym4_03 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 0 3 = a03 := rfl
theorem sym4_10 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 1 0 = a01 := rfl
theorem sym4_11 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 1 1 = a11 := rfl
theorem sym4_12 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 1 2 = a12 := rfl
theorem sym4_13 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 1 3 = a13 := rfl
theorem sym4_20 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 2 0 = a02 := rfl
theorem sym4_21 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 2 1 = a12 := rfl
theorem sym4_22 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 2 2 = a22 := rfl
theorem sym4_23 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 2 3 = a23 := rfl
theorem sym4_30 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 3 0 = a03 := rfl
theorem sym4_31 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 3 1 = a13 := rfl
theorem sym4_32 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 3 2 = a23 := rfl
theorem sym4_33 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 3 3 = a33 := rfl

theorem sym4_symm (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) (i j : Fin 4) :
    sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 i j =
      sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pieceW_00 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 0 0 = centralNum11_00 q + 8*Real.exp (-3*q)*centralNum12_00 q +
      18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q -
      q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0) +
      8*q^7*(2*q-3)^2*X 0 0 := by
  rw [pieceW, if_pos rfl]; rfl

theorem pieceW_01 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 0 1 = centralNum11_01 q + 8*Real.exp (-3*q)*centralNum12_01 q +
      18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q +
      8*q^7*(2*q-3)^2*X 0 1 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_02 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 0 2 = centralNum11_02 q + 8*Real.exp (-3*q)*centralNum12_02 q +
      18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q +
      8*q^7*(2*q-3)^2*X 0 2 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_03 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 0 3 = centralNum11_03 q + 8*Real.exp (-3*q)*centralNum12_03 q +
      18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q +
      8*q^7*(2*q-3)^2*X 0 3 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_10 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 1 0 = centralNum11_01 q + 8*Real.exp (-3*q)*centralNum12_01 q +
      18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q +
      8*q^7*(2*q-3)^2*X 1 0 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_11 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 1 1 = centralNum11_11 q + 8*Real.exp (-3*q)*centralNum12_11 q +
      18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q -
      q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1) +
      8*q^7*(2*q-3)^2*X 1 1 := by
  rw [pieceW, if_pos rfl]; rfl

theorem pieceW_12 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 1 2 = centralNum11_12 q + 8*Real.exp (-3*q)*centralNum12_12 q +
      18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q +
      8*q^7*(2*q-3)^2*X 1 2 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_13 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 1 3 = centralNum11_13 q + 8*Real.exp (-3*q)*centralNum12_13 q +
      18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q +
      8*q^7*(2*q-3)^2*X 1 3 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_20 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 2 0 = centralNum11_02 q + 8*Real.exp (-3*q)*centralNum12_02 q +
      18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q +
      8*q^7*(2*q-3)^2*X 2 0 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_21 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 2 1 = centralNum11_12 q + 8*Real.exp (-3*q)*centralNum12_12 q +
      18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q +
      8*q^7*(2*q-3)^2*X 2 1 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_22 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 2 2 = centralNum11_22 q + 8*Real.exp (-3*q)*centralNum12_22 q +
      18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q -
      q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2) +
      8*q^7*(2*q-3)^2*X 2 2 := by
  rw [pieceW, if_pos rfl]; rfl

theorem pieceW_23 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 2 3 = centralNum11_23 q + 8*Real.exp (-3*q)*centralNum12_23 q +
      18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q +
      8*q^7*(2*q-3)^2*X 2 3 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_30 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 3 0 = centralNum11_03 q + 8*Real.exp (-3*q)*centralNum12_03 q +
      18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q +
      8*q^7*(2*q-3)^2*X 3 0 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_31 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 3 1 = centralNum11_13 q + 8*Real.exp (-3*q)*centralNum12_13 q +
      18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q +
      8*q^7*(2*q-3)^2*X 3 1 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_32 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 3 2 = centralNum11_23 q + 8*Real.exp (-3*q)*centralNum12_23 q +
      18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q +
      8*q^7*(2*q-3)^2*X 3 2 := by
  rw [pieceW, if_neg (by decide), sub_zero]; rfl

theorem pieceW_33 (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) :
    pieceW q X 3 3 = centralNum11_33 q + 8*Real.exp (-3*q)*centralNum12_33 q +
      18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q -
      q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3) +
      8*q^7*(2*q-3)^2*X 3 3 := by
  rw [pieceW, if_pos rfl]; rfl

theorem centralEntryMat_symm (q : ℝ) (i j : Fin 4) :
    centralEntryMat q i j = centralEntryMat q j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pieceW_symm {X : Fin 4 → Fin 4 → ℝ} (hX : ∀ i j, X i j = X j i) (q : ℝ) (i j : Fin 4) :
    pieceW q X i j = pieceW q X j i := by
  unfold pieceW
  rw [centralEntryMat_symm q i j, hX i j]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- A quadratic form with an explicit `LDLᵀ` factorization with nonnegative pivots. -/
theorem quadForm_nonneg_of_ldl {m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 : ℝ}
    (d0 d1 d2 d3 l10 l20 l30 l21 l31 l32 : ℝ)
    (h0 : 0 ≤ d0) (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (h3 : 0 ≤ d3)
    (e00 : m00 = d0) (e01 : m01 = d0*l10) (e02 : m02 = d0*l20) (e03 : m03 = d0*l30)
    (e11 : m11 = d0*l10^2 + d1) (e12 : m12 = d0*l10*l20 + d1*l21)
    (e13 : m13 = d0*l10*l30 + d1*l31) (e22 : m22 = d0*l20^2 + d1*l21^2 + d2)
    (e23 : m23 = d0*l20*l30 + d1*l21*l31 + d2*l32)
    (e33 : m33 = d0*l30^2 + d1*l31^2 + d2*l32^2 + d3) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 i j := by
  simp only [Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  have key : y 0 * y 0 * m00 + y 0 * y 1 * m01 + y 0 * y 2 * m02 + y 0 * y 3 * m03 +
      (y 1 * y 0 * m01 + y 1 * y 1 * m11 + y 1 * y 2 * m12 + y 1 * y 3 * m13) +
      (y 2 * y 0 * m02 + y 2 * y 1 * m12 + y 2 * y 2 * m22 + y 2 * y 3 * m23) +
      (y 3 * y 0 * m03 + y 3 * y 1 * m13 + y 3 * y 2 * m23 + y 3 * y 3 * m33) =
      d0*(y 0 + l10*y 1 + l20*y 2 + l30*y 3)^2 + d1*(y 1 + l21*y 2 + l31*y 3)^2 +
        d2*(y 2 + l32*y 3)^2 + d3*(y 3)^2 := by
    subst e00 e01 e02 e03 e11 e12 e13 e22 e23 e33; ring
  rw [key]; positivity

/-- **Piece criterion.** A symmetric `W` whose upper entries are `a + tb` up to `r` on `|t| ≤ ρ`
is positive semidefinite once both endpoint matrices, with the row radii removed from the
diagonal, are. -/
theorem pieceForm_nonneg {W : Fin 4 → Fin 4 → ℝ} (hWs : ∀ i j, W i j = W j i) {t ρ : ℝ}
    (hρ : 0 < ρ) (ht : |t| ≤ ρ)
    {a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 b00 b01 b02 b03 b11 b12 b13 b22 b23 b33
      r00 r01 r02 r03 r11 r12 r13 r22 r23 r33 : ℝ}
    (h00 : |W 0 0 - (a00 + t*b00)| ≤ r00) (h01 : |W 0 1 - (a01 + t*b01)| ≤ r01)
    (h02 : |W 0 2 - (a02 + t*b02)| ≤ r02) (h03 : |W 0 3 - (a03 + t*b03)| ≤ r03)
    (h11 : |W 1 1 - (a11 + t*b11)| ≤ r11) (h12 : |W 1 2 - (a12 + t*b12)| ≤ r12)
    (h13 : |W 1 3 - (a13 + t*b13)| ≤ r13) (h22 : |W 2 2 - (a22 + t*b22)| ≤ r22)
    (h23 : |W 2 3 - (a23 + t*b23)| ≤ r23) (h33 : |W 3 3 - (a33 + t*b33)| ≤ r33)
    (hp : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * sym4
      (a00 + ρ*b00 - (r00+r01+r02+r03)) (a01 + ρ*b01) (a02 + ρ*b02) (a03 + ρ*b03)
      (a11 + ρ*b11 - (r01+r11+r12+r13)) (a12 + ρ*b12) (a13 + ρ*b13)
      (a22 + ρ*b22 - (r02+r12+r22+r23)) (a23 + ρ*b23) (a33 + ρ*b33 - (r03+r13+r23+r33)) i j)
    (hm : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * sym4
      (a00 - ρ*b00 - (r00+r01+r02+r03)) (a01 - ρ*b01) (a02 - ρ*b02) (a03 - ρ*b03)
      (a11 - ρ*b11 - (r01+r11+r12+r13)) (a12 - ρ*b12) (a13 - ρ*b13)
      (a22 - ρ*b22 - (r02+r12+r22+r23)) (a23 - ρ*b23) (a33 - ρ*b33 - (r03+r13+r23+r33)) i j)
    (y : Fin 4 → ℝ) : 0 ≤ ∑ i, ∑ j, y i * y j * W i j := by
  refine quadForm_nonneg_of_endpoints W (sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33)
    (sym4 b00 b01 b02 b03 b11 b12 b13 b22 b23 b33) (sym4 r00 r01 r02 r03 r11 r12 r13 r22 r23 r33)
    hρ ht ?_ ?_ ?_ y
  · intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h02
    · exact h03
    · rw [hWs]; exact h01
    · exact h11
    · exact h12
    · exact h13
    · rw [hWs]; exact h02
    · rw [hWs]; exact h12
    · exact h22
    · exact h23
    · rw [hWs]; exact h03
    · rw [hWs]; exact h13
    · rw [hWs]; exact h23
    · exact h33
  · intro z
    have h := hp z
    simp only [Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33] at h ⊢
    linarith
  · intro z
    have h := hm z
    simp only [Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33] at h ⊢
    linarith

end
end RHTower.ThetaCuspOddFourPieces
