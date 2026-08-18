import GaloisForLFunctions.RHTower.XiWardCubicBoundaryTranslationSchurWall

/-!
# Bilateral cubic-Ward shared-ghost completion (W-H212)

Functional-equation and Schwarz orientations do not repair the literal unshifted source Loewner
kernel.  On two distinct positive real source nodes, even the bilateral `a,-a` packet has exact
negative determinant

`-16 a^2 (x-y)^2 / ((x^2-a^2)^2 (y^2-a^2)^2)`.

The failure has a sharp positive survivor.  Bilateral orientation collapses the packetwise Hardy
debt to one shared rank-one ghost:

`K_a = P_a P_aᴴ - G_a G_aᴴ`,

where `P_a(lambda)=2lambda/(lambda^2-a^2)` and
`G_a(lambda)=2a/(lambda^2-a^2)`.  Thus adding the independently specified shared ghost gives an
exact positive completion before finite source compression.  This avoids the cellwise companion
trace divergence, but it does not yet give the fixed primitive Euler budget: the positive column
is strictly amplified at every nonzero grade.  A completed source producer must therefore short
this one common ghost against an independent Gamma/polar channel without paying the amplified
positive corner.
-/

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Bilateral real-grade residual, retaining both functional-equation orientations. -/
def xiWardCubicBilateralUnshiftedResidualPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (lam : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  xiWardCubicUnshiftedReflectedResidualPickMatrix w lam +
    xiWardCubicUnshiftedReflectedResidualPickMatrix w (-lam)

set_option maxRecDepth 10000

/-- Complex form of the exact two-node bilateral determinant. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_det_two_complex
    {a x y : ℝ} (ha : 0 < a) (hx : a < x) (hy : a < y) :
    (xiWardCubicBilateralUnshiftedResidualPickMatrix
      ![(x : ℂ), (y : ℂ)] (a : ℂ)).det =
      -16 * (a : ℂ) ^ 2 * ((x : ℂ) - y) ^ 2 /
        (((x : ℂ) ^ 2 - a ^ 2) ^ 2 * ((y : ℂ) ^ 2 - a ^ 2) ^ 2) := by
  have hxa : (x : ℂ) - a ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hx))
  have hxp : (x : ℂ) + a ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < x + a))
  have hya : (y : ℂ) - a ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hy))
  have hyp : (y : ℂ) + a ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < y + a))
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (ha.trans hx))
  have hy0 : (y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (ha.trans hy))
  have hxy0 : (x : ℂ) + y ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < x + y))
  have hyx0 : (y : ℂ) + x ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < y + x))
  have hxd : (x : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (by nlinarith : x ^ 2 - a ^ 2 ≠ 0)
  have hyd : (y : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (by nlinarith : y ^ 2 - a ^ 2 ≠ 0)
  have h00 :
      xiWardCubicBilateralUnshiftedResidualPickMatrix
        ![(x : ℂ), (y : ℂ)] (a : ℂ) 0 0 =
        4 / ((x : ℂ) ^ 2 - (a : ℂ) ^ 2) := by
    apply (eq_div_iff hxd).2
    norm_num [xiWardCubicBilateralUnshiftedResidualPickMatrix,
      xiWardCubicUnshiftedReflectedResidualPickMatrix]
    field_simp [hxa, hxp, hx0]
    ring
  have h11 :
      xiWardCubicBilateralUnshiftedResidualPickMatrix
        ![(x : ℂ), (y : ℂ)] (a : ℂ) 1 1 =
        4 / ((y : ℂ) ^ 2 - (a : ℂ) ^ 2) := by
    apply (eq_div_iff hyd).2
    norm_num [xiWardCubicBilateralUnshiftedResidualPickMatrix,
      xiWardCubicUnshiftedReflectedResidualPickMatrix]
    field_simp [hya, hyp, hy0]
    ring
  have h01 :
      xiWardCubicBilateralUnshiftedResidualPickMatrix
        ![(x : ℂ), (y : ℂ)] (a : ℂ) 0 1 =
        4 * ((x : ℂ) * y - (a : ℂ) ^ 2) /
          (((x : ℂ) ^ 2 - a ^ 2) * ((y : ℂ) ^ 2 - a ^ 2)) := by
    apply (eq_div_iff (mul_ne_zero hxd hyd)).2
    norm_num [xiWardCubicBilateralUnshiftedResidualPickMatrix,
      xiWardCubicUnshiftedReflectedResidualPickMatrix]
    field_simp [hxa, hxp, hya, hyp, hxy0]
    ring
  have h10 :
      xiWardCubicBilateralUnshiftedResidualPickMatrix
        ![(x : ℂ), (y : ℂ)] (a : ℂ) 1 0 =
        4 * ((x : ℂ) * y - (a : ℂ) ^ 2) /
          (((x : ℂ) ^ 2 - a ^ 2) * ((y : ℂ) ^ 2 - a ^ 2)) := by
    apply (eq_div_iff (mul_ne_zero hxd hyd)).2
    norm_num [xiWardCubicBilateralUnshiftedResidualPickMatrix,
      xiWardCubicUnshiftedReflectedResidualPickMatrix]
    field_simp [hxa, hxp, hya, hyp, hxy0, hyx0]
    ring
  rw [Matrix.det_fin_two]
  rw [h00, h01, h10, h11]
  apply (eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hxd) (pow_ne_zero 2 hyd))).2
  field_simp [hxd, hyd]
  ring

/-- Real form of the exact two-node bilateral determinant. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_det_two
    {a x y : ℝ} (ha : 0 < a) (hx : a < x) (hy : a < y) :
    (xiWardCubicBilateralUnshiftedResidualPickMatrix
      ![(x : ℂ), (y : ℂ)] (a : ℂ)).det =
      ((-16 * a ^ 2 * (x - y) ^ 2 /
        ((x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2) : ℝ) : ℂ) := by
  rw [xiWardCubicBilateralUnshiftedResidualPickMatrix_det_two_complex ha hx hy]
  norm_cast

set_option maxRecDepth 1000

/-- Bilateral orientation is still indefinite on every distinct real two-node packet. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_not_posSemidef
    {a x y : ℝ} (ha : 0 < a) (hx : a < x) (hy : a < y) (hxy : x ≠ y) :
    ¬ (xiWardCubicBilateralUnshiftedResidualPickMatrix
      ![(x : ℂ), (y : ℂ)] (a : ℂ)).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  rw [xiWardCubicBilateralUnshiftedResidualPickMatrix_det_two ha hx hy] at hdet
  have hreal := (RCLike.nonneg_iff.mp hdet).1
  change 0 ≤ -16 * a ^ 2 * (x - y) ^ 2 /
    ((x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2) at hreal
  have hxa : 0 < x ^ 2 - a ^ 2 := by nlinarith
  have hya : 0 < y ^ 2 - a ^ 2 := by nlinarith
  have hxySq : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hneg : -16 * a ^ 2 * (x - y) ^ 2 /
      ((x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2) < 0 := by
    have hnum : -16 * a ^ 2 * (x - y) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos ha)) hxySq
    have hden : 0 < (x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2 :=
      mul_pos (sq_pos_of_pos hxa) (sq_pos_of_pos hya)
    exact div_neg_of_neg_of_pos hnum hden
  linarith

/-- Four FE--Schwarz orientations duplicate the bilateral real-grade packet. -/
def xiWardCubicFourOrientationUnshiftedResidualPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (lam : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  xiWardCubicBilateralUnshiftedResidualPickMatrix w lam +
    xiWardCubicBilateralUnshiftedResidualPickMatrix w lam

theorem xiWardCubicFourOrientationUnshiftedResidualPickMatrix_eq_two_smul
    {N : ℕ} (w : Fin N → ℂ) (lam : ℂ) :
    xiWardCubicFourOrientationUnshiftedResidualPickMatrix w lam =
      (2 : ℝ) • xiWardCubicBilateralUnshiftedResidualPickMatrix w lam := by
  ext i j
  simp [xiWardCubicFourOrientationUnshiftedResidualPickMatrix]
  ring

/-- The complete four-orientation packet inherits the bilateral Loewner obstruction. -/
theorem xiWardCubicFourOrientationUnshiftedResidualPickMatrix_not_posSemidef
    {a x y : ℝ} (ha : 0 < a) (hx : a < x) (hy : a < y) (hxy : x ≠ y) :
    ¬ (xiWardCubicFourOrientationUnshiftedResidualPickMatrix
      ![(x : ℂ), (y : ℂ)] (a : ℂ)).PosSemidef := by
  intro hfour
  rw [xiWardCubicFourOrientationUnshiftedResidualPickMatrix_eq_two_smul] at hfour
  have hbilateral := hfour.smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hcollapse :
      (1 / 2 : ℝ) •
          ((2 : ℝ) • xiWardCubicBilateralUnshiftedResidualPickMatrix
            ![(x : ℂ), (y : ℂ)] (a : ℂ)) =
        xiWardCubicBilateralUnshiftedResidualPickMatrix
          ![(x : ℂ), (y : ℂ)] (a : ℂ) := by
    rw [smul_smul]
    norm_num
  rw [hcollapse] at hbilateral
  exact xiWardCubicBilateralUnshiftedResidualPickMatrix_not_posSemidef
    ha hx hy hxy hbilateral

/-- Positive source column in the bilateral rank-two Krein factorization. -/
def xiWardCubicBilateralPositiveColumn {N : ℕ}
    (w : Fin N → ℝ) (a : ℝ) : Matrix (Fin N) (Fin 1) ℂ :=
  fun i _ => (2 * w i / (w i ^ 2 - a ^ 2) : ℝ)

/-- One shared ghost column replacing the nonsummable cellwise companion family. -/
def xiWardCubicBilateralSharedGhostColumn {N : ℕ}
    (w : Fin N → ℝ) (a : ℝ) : Matrix (Fin N) (Fin 1) ℂ :=
  fun i _ => (2 * a / (w i ^ 2 - a ^ 2) : ℝ)

/-- Bilateral orientation converts the complete Hardy debt into one prime-independent rank-one
ghost before any finite source packet is compressed. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_eq_credit_sub_sharedGhost
    {N : ℕ} {w : Fin N → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, a < w i) :
    xiWardCubicBilateralUnshiftedResidualPickMatrix
        (fun i => (w i : ℂ)) (a : ℂ) =
      xiWardCubicBilateralPositiveColumn w a *
          (xiWardCubicBilateralPositiveColumn w a)ᴴ -
        xiWardCubicBilateralSharedGhostColumn w a *
          (xiWardCubicBilateralSharedGhostColumn w a)ᴴ := by
  ext i j
  have hwi0 : 0 < w i := lt_of_le_of_lt ha (hw i)
  have hwj0 : 0 < w j := lt_of_le_of_lt ha (hw j)
  have hwima : (w i : ℂ) - a ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt (hw i)))
  have hwipa : (w i : ℂ) + a ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < w i + a))
  have hwjma : (w j : ℂ) - a ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt (hw j)))
  have hwjpa : (w j : ℂ) + a ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < w j + a))
  have hsum : (w i : ℂ) + w j ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos hwi0 hwj0))
  have hdi : (w i : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have hsquare : a ^ 2 < w i ^ 2 :=
      (sq_lt_sq₀ ha hwi0.le).2 (hw i)
    exact_mod_cast (ne_of_gt (sub_pos.mpr hsquare))
  have hdj : (w j : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have hsquare : a ^ 2 < w j ^ 2 :=
      (sq_lt_sq₀ ha hwj0.le).2 (hw j)
    exact_mod_cast (ne_of_gt (sub_pos.mpr hsquare))
  simp only [xiWardCubicBilateralUnshiftedResidualPickMatrix,
    xiWardCubicUnshiftedReflectedResidualPickMatrix, Matrix.add_apply,
    Matrix.sub_apply, Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, Matrix.conjTranspose_apply,
    xiWardCubicBilateralPositiveColumn,
    xiWardCubicBilateralSharedGhostColumn]
  norm_num
  field_simp [hwima, hwipa, hwjma, hwjpa, hsum, hdi, hdj]
  ring

/-- Exact positive completion: adding the independently specified shared ghost Gram leaves the
rank-one positive source credit. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_add_sharedGhost
    {N : ℕ} {w : Fin N → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, a < w i) :
    xiWardCubicBilateralUnshiftedResidualPickMatrix
          (fun i => (w i : ℂ)) (a : ℂ) +
        xiWardCubicBilateralSharedGhostColumn w a *
          (xiWardCubicBilateralSharedGhostColumn w a)ᴴ =
      xiWardCubicBilateralPositiveColumn w a *
        (xiWardCubicBilateralPositiveColumn w a)ᴴ := by
  rw [xiWardCubicBilateralUnshiftedResidualPickMatrix_eq_credit_sub_sharedGhost
    ha hw]
  abel

/-- The completed bilateral packet is positive semidefinite. -/
theorem xiWardCubicBilateralUnshiftedResidualPickMatrix_add_sharedGhost_posSemidef
    {N : ℕ} {w : Fin N → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, a < w i) :
    (xiWardCubicBilateralUnshiftedResidualPickMatrix
          (fun i => (w i : ℂ)) (a : ℂ) +
        xiWardCubicBilateralSharedGhostColumn w a *
          (xiWardCubicBilateralSharedGhostColumn w a)ᴴ).PosSemidef := by
  rw [xiWardCubicBilateralUnshiftedResidualPickMatrix_add_sharedGhost ha hw]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The positive credit is strictly amplified away from neutral grade.  Therefore the shared
ghost is not by itself a contraction into the grade-zero primitive source budget. -/
theorem xiWardCubicBilateralPositiveColumn_normSq_strictly_increases
    {lambda a : ℝ} (ha : 0 < a) (hala : a < lambda) :
    Complex.normSq (2 * lambda / lambda ^ 2 : ℝ) <
      Complex.normSq
        (xiWardCubicBilateralPositiveColumn (fun _ : Fin 1 => lambda) a 0 0) := by
  simp only [xiWardCubicBilateralPositiveColumn, Complex.normSq_ofReal]
  have hl0 : 0 < lambda := ha.trans hala
  have hden : 0 < lambda ^ 2 - a ^ 2 := by nlinarith
  have hleft : 0 < 2 * lambda / lambda ^ 2 := by positivity
  have hright : 0 < 2 * lambda / (lambda ^ 2 - a ^ 2) := by positivity
  have hlt : 2 * lambda / lambda ^ 2 <
      2 * lambda / (lambda ^ 2 - a ^ 2) := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hl0) hden]
    nlinarith [sq_pos_of_pos ha]
  have hsquare := (sq_lt_sq₀ hleft.le hright.le).2 hlt
  simpa [pow_two] using hsquare

end

end RHTower
