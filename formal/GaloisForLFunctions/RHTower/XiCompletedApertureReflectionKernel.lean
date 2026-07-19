import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

namespace RHTower

noncomputable section

/-- Completed Xi flux kernel at transverse aperture `u` and node displacement `x-y`. -/
def xiCompletedApertureOffDiagonalKernel (u x y : ℝ) : ℂ :=
  seamFluxCochain
    ((((1 / 2 : ℝ) + u : ℝ) : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I)

theorem xiCompletedApertureOffDiagonalKernel_swap
    (u x y : ℝ) :
    xiCompletedApertureOffDiagonalKernel u y x =
      (starRingEnd ℂ) (xiCompletedApertureOffDiagonalKernel u x y) := by
  rw [xiCompletedApertureOffDiagonalKernel,
    xiCompletedApertureOffDiagonalKernel]
  have harg :
      ((((1 / 2 : ℝ) + u : ℝ) : ℂ) + ((y - x : ℝ) : ℂ) * Complex.I) =
        (starRingEnd ℂ)
          ((((1 / 2 : ℝ) + u : ℝ) : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> push_cast <;> simp
  rw [harg, seamFluxCochain_conj]

theorem xiCompletedApertureOffDiagonalKernel_reflect
    (u x y : ℝ) :
    xiCompletedApertureOffDiagonalKernel (-u) x y =
      -xiCompletedApertureOffDiagonalKernel u y x := by
  rw [xiCompletedApertureOffDiagonalKernel,
    xiCompletedApertureOffDiagonalKernel]
  have harg :
      ((((1 / 2 : ℝ) + -u : ℝ) : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I) =
        1 - ((((1 / 2 : ℝ) + u : ℝ) : ℂ) +
          ((y - x : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  rw [harg, seamFluxCochain_reciprocity]

theorem xiCompletedApertureOffDiagonalKernel_center_swap_neg
    (x y : ℝ) :
    xiCompletedApertureOffDiagonalKernel 0 y x =
      -xiCompletedApertureOffDiagonalKernel 0 x y := by
  have h := xiCompletedApertureOffDiagonalKernel_reflect 0 y x
  simpa using h

theorem xiCompletedApertureOffDiagonalKernel_center_self
    (x : ℝ) :
    xiCompletedApertureOffDiagonalKernel 0 x x = 0 := by
  have h := xiCompletedApertureOffDiagonalKernel_center_swap_neg x x
  apply_fun (fun w : ℂ => w + xiCompletedApertureOffDiagonalKernel 0 x x) at h
  have htwo : (2 : ℂ) * xiCompletedApertureOffDiagonalKernel 0 x x = 0 := by
    simpa [two_mul] using h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Finite packet of the completed transverse-aperture kernel. -/
def xiCompletedAperturePacketMatrix {n : ℕ}
    (u : ℝ) (node : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => xiCompletedApertureOffDiagonalKernel u (node i) (node j)

/-- Any odd-dimensional skew-symmetric packet over `ℂ` is singular. -/
theorem det_eq_zero_of_odd_of_transpose_eq_neg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hodd : Odd (Fintype.card n))
    (hskew : A.transpose = -A) :
    A.det = 0 := by
  have hdet := congrArg Matrix.det hskew
  rw [Matrix.det_transpose, Matrix.det_neg, hodd.neg_one_pow, neg_one_mul] at hdet
  linear_combination hdet / 2

/-- At the functional-equation center, every finite completed aperture packet is
skew-symmetric. -/
theorem xiCompletedAperturePacketMatrix_center_transpose
    {n : ℕ} (node : Fin n → ℝ) :
    (xiCompletedAperturePacketMatrix 0 node).transpose =
      -xiCompletedAperturePacketMatrix 0 node := by
  ext i j
  simpa [Matrix.transpose_apply, xiCompletedAperturePacketMatrix] using
    xiCompletedApertureOffDiagonalKernel_center_swap_neg (node i) (node j)

/-- **All odd-detector center no-go.** Every odd-cardinality completed Xi aperture packet at the
functional-equation center has zero determinant. -/
theorem xiCompletedAperturePacketMatrix_center_det_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) (node : Fin n → ℝ) :
    (xiCompletedAperturePacketMatrix 0 node).det = 0 := by
  exact det_eq_zero_of_odd_of_transpose_eq_neg
    (xiCompletedAperturePacketMatrix 0 node)
    (by simpa using hn)
    (xiCompletedAperturePacketMatrix_center_transpose node)

/-- Leibniz formula for the determinant of a three-node complex kernel packet. -/
def complexThreePointDet (K : ℝ → ℝ → ℂ) (x y z : ℝ) : ℂ :=
  K x x * K y y * K z z +
    K x y * K y z * K z x +
    K x z * K y x * K z y -
    K x z * K y y * K z x -
    K x y * K y x * K z z -
    K x x * K y z * K z y

theorem complexThreePointDet_eq_zero_of_skew
    (K : ℝ → ℝ → ℂ)
    (hdiag : ∀ x, K x x = 0)
    (hskew : ∀ x y, K y x = -K x y)
    (x y z : ℝ) :
    complexThreePointDet K x y z = 0 := by
  rw [complexThreePointDet, hdiag x, hdiag y, hdiag z,
    hskew x z, hskew x y, hskew y z]
  ring

theorem complexThreePointDet_xiCompletedApertureOffDiagonalKernel_center
    (x y z : ℝ) :
    complexThreePointDet
      (xiCompletedApertureOffDiagonalKernel 0) x y z = 0 := by
  exact complexThreePointDet_eq_zero_of_skew
    (xiCompletedApertureOffDiagonalKernel 0)
    xiCompletedApertureOffDiagonalKernel_center_self
    xiCompletedApertureOffDiagonalKernel_center_swap_neg x y z

/-- Functional-equation aperture-even sector. -/
def xiCompletedApertureEvenKernel (u x y : ℝ) : ℂ :=
  xiCompletedApertureOffDiagonalKernel u x y +
    xiCompletedApertureOffDiagonalKernel (-u) x y

/-- Functional-equation aperture-odd sector. -/
def xiCompletedApertureOddKernel (u x y : ℝ) : ℂ :=
  xiCompletedApertureOffDiagonalKernel u x y -
    xiCompletedApertureOffDiagonalKernel (-u) x y

theorem xiCompletedApertureEvenKernel_eq_sub_swap
    (u x y : ℝ) :
    xiCompletedApertureEvenKernel u x y =
      xiCompletedApertureOffDiagonalKernel u x y -
        xiCompletedApertureOffDiagonalKernel u y x := by
  rw [xiCompletedApertureEvenKernel,
    xiCompletedApertureOffDiagonalKernel_reflect]
  ring

theorem xiCompletedApertureEvenKernel_swap_neg
    (u x y : ℝ) :
    xiCompletedApertureEvenKernel u y x =
      -xiCompletedApertureEvenKernel u x y := by
  rw [xiCompletedApertureEvenKernel_eq_sub_swap,
    xiCompletedApertureEvenKernel_eq_sub_swap]
  ring

theorem xiCompletedApertureEvenKernel_self
    (u x : ℝ) : xiCompletedApertureEvenKernel u x x = 0 := by
  rw [xiCompletedApertureEvenKernel_eq_sub_swap]
  ring

theorem complexThreePointDet_xiCompletedApertureEvenKernel
    (u x y z : ℝ) :
    complexThreePointDet (xiCompletedApertureEvenKernel u) x y z = 0 := by
  exact complexThreePointDet_eq_zero_of_skew
    (xiCompletedApertureEvenKernel u)
    (xiCompletedApertureEvenKernel_self u)
    (xiCompletedApertureEvenKernel_swap_neg u) x y z

/-- Every odd-cardinality packet in the aperture-even sector is singular, at every transverse
aperture. -/
theorem xiCompletedApertureEvenKernel_packet_det_eq_zero_of_odd
    {n : ℕ} (hn : Odd n) (u : ℝ) (node : Fin n → ℝ) :
    (Matrix.of (fun i j : Fin n =>
      xiCompletedApertureEvenKernel u (node i) (node j))).det = 0 := by
  apply det_eq_zero_of_odd_of_transpose_eq_neg _ (by simpa using hn)
  ext i j
  simpa [Matrix.transpose_apply] using
    xiCompletedApertureEvenKernel_swap_neg u (node i) (node j)

theorem xiCompletedApertureOddKernel_eq_add_swap
    (u x y : ℝ) :
    xiCompletedApertureOddKernel u x y =
      xiCompletedApertureOffDiagonalKernel u x y +
        xiCompletedApertureOffDiagonalKernel u y x := by
  rw [xiCompletedApertureOddKernel,
    xiCompletedApertureOffDiagonalKernel_reflect]
  ring

theorem xiCompletedApertureOddKernel_swap
    (u x y : ℝ) :
    xiCompletedApertureOddKernel u y x =
      xiCompletedApertureOddKernel u x y := by
  rw [xiCompletedApertureOddKernel_eq_add_swap,
    xiCompletedApertureOddKernel_eq_add_swap]
  ring

theorem xiCompletedApertureOddKernel_eq_two_re
    (u x y : ℝ) :
    xiCompletedApertureOddKernel u x y =
      ((2 * (xiCompletedApertureOffDiagonalKernel u x y).re : ℝ) : ℂ) := by
  rw [xiCompletedApertureOddKernel_eq_add_swap,
    xiCompletedApertureOffDiagonalKernel_swap]
  apply Complex.ext <;> simp
  ring

theorem xiCompletedApertureOddKernel_center
    (x y : ℝ) : xiCompletedApertureOddKernel 0 x y = 0 := by
  rw [xiCompletedApertureOddKernel_eq_add_swap,
    xiCompletedApertureOffDiagonalKernel_center_swap_neg]
  ring

end

end RHTower
