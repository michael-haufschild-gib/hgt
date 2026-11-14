import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGreenFormOfABoundWindowGrowsWithTheWindowAndAlongTheRefinementTower
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGreenMatrixOfTheMiddleIsNegativeOnlyAlongItsPotentialAndPositiveOnChargeFreePackets

/-!
# The continuum Green kernel is the limit of the tower and is negative only along the charge

The neutral part `M_D` of the dyadic middle is Weil's prime-free form on the step functions of
block size `D`, and refinement is an isometry `ι_m` with `ι_mᵀ M_{mD} ι_m = M_D`. The Green forms
`⟨ι_m w, G_{mD} ι_m w⟩` increase along the tower and are at most `5000 ‖w‖²`. Their limit is the
**continuum Green form** `𝔊_D` of the prime-free window, tested on the step functions of block
size `D`:

* **Existence** (`tendsto_towerGreen_factorial`, `towerGreen_le_continuumGreen`): along
  `D, 2!·D, 3!·D, …` the Green forms converge to `𝔊_D(w)`, which bounds every level of the tower.
* **One object at all block sizes** (`continuumGreen_refine`): `𝔊_{mD}(ι_m w) = 𝔊_D(w)`.
* **A quadratic form** (`continuumGreen_eq_form`): `𝔊_D(w) = ⟨w, 𝔊_D w⟩` for the symmetric
  matrix `continuumGreenMatrix D`, obtained by polarization.
* **Bounds** (`greenMatrix_form_le_continuumGreen`, `continuumGreen_le`): `G_D ⪯ 𝔊_D ⪯ 5000`.
* **The negative part in closed form** (`continuumGreen_add_charge_nonneg`,
  `continuumGreen_pos_of_sum_eq_zero`): with the depth
  `δ = γ + log 2π + 3 log 2 − 3 log 3` of a dyadic window,

    `𝔊_D(w) + (Σ w)² / (D δ) ≥ 0`, and `𝔊_D(w) ≥ ‖w‖² / (8 log 2D + 21) > 0` if `Σ w = 0`.

  The continuum Green kernel is the explicit constant kernel `−1/δ` (per unit of multiplicative
  length) plus a kernel that is positive on charge-free functions: it has at most one negative
  square, carried by the charge (`continuumGreen_nonneg_of_sum_eq_zero`).
* **The binding energy of the continuum** (`tendsto_bindingEnergy_factorial`): the binding
  energies along the tower converge to a limit in `[δ, 3]`.

The charge part is exact at every level, `(Σ ι_m w)² / (mD · N(1,1)) = (Σ w)² / (D · N(1,1))`,
because the flat packet of `(D, 2D]` is the refinement of the flat packet of `(1, 2]`.
-/

open Finset Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Refinement in coordinates -/

theorem refineStep_refineStep (n m : ℕ) (σ : ℕ → ℝ) :
    refineStep n (refineStep m σ) = refineStep (n * m) σ := by
  funext i
  simp only [refineStep]
  rw [Nat.div_div_eq_div_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), div_div,
    mul_comm (Real.sqrt (m : ℝ))]

theorem refineStep_one (σ : ℕ → ℝ) : refineStep 1 σ = σ := by
  funext i
  simp only [refineStep, Nat.div_one, Nat.cast_one, Real.sqrt_one, div_one]

theorem refineMatrix_mulVec_eq {m D : ℕ} (w : Fin D → ℝ) :
    refineMatrix m D *ᵥ w = fun i : Fin (m * D) => refineStep m (extendFin w) i := by
  funext i
  rw [← extendFin_refineMatrix_mulVec w i.2, extendFin_coe]

/-- A refined step function vanishes beyond the refined window. -/
theorem extendFin_refineStep {m D : ℕ} (hm : 1 ≤ m) (w : Fin D → ℝ) :
    extendFin (fun i : Fin (m * D) => refineStep m (extendFin w) i) =
      refineStep m (extendFin w) := by
  funext n
  by_cases hn : n < m * D
  · rw [extendFin, dif_pos hn]
  · have hD : ¬n / m < D := fun h =>
      hn (((Nat.div_lt_iff_lt_mul (by omega)).mp h).trans_eq (mul_comm D m))
    rw [extendFin, dif_neg hn, refineStep, extendFin, dif_neg hD, zero_div]

/-! ### The Green forms of the tower -/

/-- The Green form of the middle at block size `N` on the restriction of a step function. -/
def greenForm (N : ℕ) (σ : ℕ → ℝ) : ℝ :=
  (fun i : Fin N => σ i) ⬝ᵥ (greenMatrix N *ᵥ fun i : Fin N => σ i)

/-- The Green form at the level `m` of the tower over the block size `D`. -/
def towerGreen (D : ℕ) (σ : ℕ → ℝ) (m : ℕ) : ℝ := greenForm (m * D) (refineStep m σ)

theorem towerGreen_extendFin {D m : ℕ} (w : Fin D → ℝ) :
    towerGreen D (extendFin w) m =
      (refineMatrix m D *ᵥ w) ⬝ᵥ (greenMatrix (m * D) *ᵥ (refineMatrix m D *ᵥ w)) := by
  rw [towerGreen, greenForm, refineMatrix_mulVec_eq]

theorem towerGreen_one {D : ℕ} (w : Fin D → ℝ) :
    towerGreen D (extendFin w) 1 = w ⬝ᵥ (greenMatrix D *ᵥ w) := by
  have hw : (fun i : Fin D => extendFin w i) = w := funext fun i => extendFin_coe w i
  rw [towerGreen, one_mul, refineStep_one, greenForm, hw]

/-- **The Green forms increase along the tower.** -/
theorem towerGreen_le_mul {D : ℕ} (hD : 1 ≤ D) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (w : Fin D → ℝ) : towerGreen D (extendFin w) m ≤ towerGreen D (extendFin w) (n * m) := by
  have h := greenMatrix_form_le_refined (Nat.mul_pos hm hD) hn
    (fun i : Fin (m * D) => refineStep m (extendFin w) i)
  rw [refineMatrix_mulVec_eq, extendFin_refineStep hm, refineStep_refineStep] at h
  have h' : towerGreen D (extendFin w) m ≤
      greenForm (n * (m * D)) (refineStep (n * m) (extendFin w)) := h
  rw [← Nat.mul_assoc] at h'
  exact h'

theorem towerGreen_le {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m) (w : Fin D → ℝ) :
    towerGreen D (extendFin w) m ≤ 5000 * (w ⬝ᵥ w) := by
  rw [towerGreen_extendFin]
  exact greenMatrix_form_refined_le hD hm w

/-- The level `k` of the tower seen from the level `m`. -/
theorem towerGreen_refine {D m k : ℕ} (hm : 1 ≤ m) (w : Fin D → ℝ) :
    towerGreen (m * D) (extendFin (refineMatrix m D *ᵥ w)) k =
      towerGreen D (extendFin w) (k * m) := by
  rw [refineMatrix_mulVec_eq, extendFin_refineStep hm, towerGreen, towerGreen,
    refineStep_refineStep, ← Nat.mul_assoc]

/-! ### The continuum Green form -/

/-- **The Green form of the continuum** on the step functions of block size `D`: the limit of the
Green forms along the tower `D, 2!·D, 3!·D, …`. -/
def continuumGreen (D : ℕ) (w : Fin D → ℝ) : ℝ :=
  ⨆ k : ℕ, towerGreen D (extendFin w) k.factorial

theorem monotone_towerGreen_factorial {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    Monotone fun k : ℕ => towerGreen D (extendFin w) k.factorial :=
  monotone_nat_of_le_succ fun k => by
    rw [Nat.factorial_succ]
    exact towerGreen_le_mul hD (Nat.factorial_pos k) (by omega) w

theorem bddAbove_towerGreen_factorial {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    BddAbove (Set.range fun k : ℕ => towerGreen D (extendFin w) k.factorial) :=
  ⟨5000 * (w ⬝ᵥ w), by
    rintro _ ⟨k, rfl⟩
    exact towerGreen_le hD (Nat.factorial_pos k) w⟩

/-- **The Green forms of the tower converge.** -/
theorem tendsto_towerGreen_factorial {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    Tendsto (fun k : ℕ => towerGreen D (extendFin w) k.factorial) atTop
      (𝓝 (continuumGreen D w)) :=
  tendsto_atTop_ciSup (monotone_towerGreen_factorial hD w) (bddAbove_towerGreen_factorial hD w)

/-- Every level of the tower is below the continuum. -/
theorem towerGreen_le_continuumGreen {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m)
    (w : Fin D → ℝ) : towerGreen D (extendFin w) m ≤ continuumGreen D w := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hm (le_refl m)
  have hc1 : 1 ≤ c := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hc
    exact (Nat.factorial_pos m).ne' hc
  calc towerGreen D (extendFin w) m ≤ towerGreen D (extendFin w) (c * m) :=
        towerGreen_le_mul hD hm hc1 w
    _ = towerGreen D (extendFin w) m.factorial := by rw [hc, mul_comm]
    _ ≤ continuumGreen D w := le_ciSup (bddAbove_towerGreen_factorial hD w) m

theorem greenMatrix_form_le_continuumGreen {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    w ⬝ᵥ (greenMatrix D *ᵥ w) ≤ continuumGreen D w := by
  rw [← towerGreen_one]
  exact towerGreen_le_continuumGreen hD le_rfl w

theorem continuumGreen_le {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    continuumGreen D w ≤ 5000 * (w ⬝ᵥ w) :=
  ciSup_le fun k => towerGreen_le hD (Nat.factorial_pos k) w

/-- **One object at all block sizes**: the continuum Green form of a refined step function is the
continuum Green form of the step function. -/
theorem continuumGreen_refine {D : ℕ} (hD : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m) (w : Fin D → ℝ) :
    continuumGreen (m * D) (refineMatrix m D *ᵥ w) = continuumGreen D w := by
  apply le_antisymm
  · refine ciSup_le fun k => ?_
    rw [towerGreen_refine hm]
    exact towerGreen_le_continuumGreen hD (Nat.mul_pos (Nat.factorial_pos k) hm) w
  · refine ciSup_le fun k => ?_
    calc towerGreen D (extendFin w) k.factorial
        ≤ towerGreen D (extendFin w) (k.factorial * m) := by
          rw [mul_comm]
          exact towerGreen_le_mul hD (Nat.factorial_pos k) hm w
      _ = towerGreen (m * D) (extendFin (refineMatrix m D *ᵥ w)) k.factorial :=
          (towerGreen_refine hm w).symm
      _ ≤ continuumGreen (m * D) (refineMatrix m D *ᵥ w) :=
          le_ciSup (bddAbove_towerGreen_factorial (Nat.mul_pos hm hD) _) k

/-! ### The continuum Green form is a quadratic form -/

theorem single_form {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (i j : ι) :
    Pi.single i 1 ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

/-- The polarization of a function on vectors at two coordinates. -/
def quadPolar {ι : Type*} [DecidableEq ι] (q : (ι → ℝ) → ℝ) (i j : ι) : ℝ :=
  (q (Pi.single i 1 + Pi.single j 1) - q (Pi.single i 1) - q (Pi.single j 1)) / 2

/-- A quadratic form is the double sum of its polarization. -/
theorem form_eq_sum_quadPolar {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) (w : Fin D → ℝ) :
    w ⬝ᵥ (A *ᵥ w) =
      ∑ i, ∑ j, w i * w j * quadPolar (fun v => v ⬝ᵥ (A *ᵥ v)) i j := by
  have hpol : ∀ i j : Fin D, quadPolar (fun v => v ⬝ᵥ (A *ᵥ v)) i j = (A i j + A j i) / 2 :=
    fun i j => by
      simp only [quadPolar, Matrix.mulVec_add, dotProduct_add, add_dotProduct, single_form]
      ring
  have hswap : ∑ i, ∑ j, w i * w j * A j i = ∑ i, ∑ j, w i * w j * A i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hpol]
  rw [dotProduct_mulVec_eq_sum]
  have e : ∀ i j : Fin D, w i * w j * ((A i j + A j i) / 2) =
      (w i * w j * A i j + w i * w j * A j i) / 2 := fun i j => by ring
  simp only [e, ← Finset.sum_div, Finset.sum_add_distrib, hswap]
  ring

/-- The matrix of the continuum Green form. -/
def continuumGreenMatrix (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  fun i j => quadPolar (continuumGreen D) i j

theorem continuumGreenMatrix_symm (D : ℕ) (i j : Fin D) :
    continuumGreenMatrix D i j = continuumGreenMatrix D j i := by
  simp only [continuumGreenMatrix, quadPolar]
  rw [add_comm (Pi.single i 1 : Fin D → ℝ) (Pi.single j 1)]
  ring

/-- The level `m` of the tower as the form of the compressed Green matrix. -/
theorem towerGreen_eq_form {D m : ℕ} (w : Fin D → ℝ) :
    towerGreen D (extendFin w) m =
      w ⬝ᵥ (((refineMatrix m D)ᵀ * greenMatrix (m * D) * refineMatrix m D) *ᵥ w) := by
  rw [towerGreen_extendFin]
  symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w (refineMatrix m D)ᵀ,
    Matrix.vecMul_transpose]

/-- **The continuum Green form is the form of a symmetric matrix.** -/
theorem continuumGreen_eq_form {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    continuumGreen D w = w ⬝ᵥ (continuumGreenMatrix D *ᵥ w) := by
  have hq : ∀ k : ℕ, (fun v : Fin D → ℝ => towerGreen D (extendFin v) k.factorial) =
      fun v => v ⬝ᵥ (((refineMatrix k.factorial D)ᵀ * greenMatrix (k.factorial * D) *
        refineMatrix k.factorial D) *ᵥ v) := fun k => funext fun v => towerGreen_eq_form v
  have hP : ∀ i j : Fin D, Tendsto
      (fun k : ℕ => quadPolar (fun v => towerGreen D (extendFin v) k.factorial) i j) atTop
      (𝓝 (continuumGreenMatrix D i j)) := fun i j =>
    (((tendsto_towerGreen_factorial hD _).sub (tendsto_towerGreen_factorial hD _)).sub
      (tendsto_towerGreen_factorial hD _)).div_const 2
  have hsum : Tendsto (fun k : ℕ => towerGreen D (extendFin w) k.factorial) atTop
      (𝓝 (∑ i, ∑ j, w i * w j * continuumGreenMatrix D i j)) := by
    have e : (fun k : ℕ => towerGreen D (extendFin w) k.factorial) = fun k =>
        ∑ i, ∑ j, w i * w j * quadPolar (fun v => towerGreen D (extendFin v) k.factorial) i j :=
      funext fun k => by
        rw [hq k, towerGreen_eq_form, form_eq_sum_quadPolar]
    rw [e]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (hP i j).const_mul (w i * w j)
  rw [dotProduct_mulVec_eq_sum]
  exact tendsto_nhds_unique (tendsto_towerGreen_factorial hD w) hsum

/-! ### The negative part of the continuum Green kernel -/

/-- **The continuum Green form is negative only along the charge**: it is at least
`(Σ w)² / (D · N(1, 1))`, the charge term of every level of the tower. -/
theorem continuumGreen_ge_charge {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    (∑ i, w i) ^ 2 / (D * neutralBlock 1 1 1) ≤ continuumGreen D w :=
  (greenMatrix_form_ge_charge hD w).trans (greenMatrix_form_le_continuumGreen hD w)

/-- **The negative part in closed form**: `𝔊_D + 𝟙𝟙ᵀ/(D δ) ⪰ 0`, with the depth
`δ = γ + log 2π + 3 log 2 − 3 log 3` of a dyadic window. -/
theorem continuumGreen_add_charge_nonneg {D : ℕ} (hD : 1 ≤ D) (w : Fin D → ℝ) :
    0 ≤ continuumGreen D w + (∑ i, w i) ^ 2 / (D * dyadicDepth) := by
  have h := continuumGreen_ge_charge hD w
  rw [neutralBlock_one_one, mul_neg, div_neg] at h
  linarith

/-- **On charge-free functions the continuum Green form is positive definite**, with the floor of
the block size `D`. -/
theorem continuumGreen_pos_of_sum_eq_zero {D : ℕ} (hD : 1 ≤ D) {w : Fin D → ℝ}
    (hw : ∑ i, w i = 0) :
    w ⬝ᵥ w ≤ (8 * Real.log (2 * (D : ℝ)) + 21) * continuumGreen D w := by
  have h := greenMatrix_form_ge_of_sum_eq_zero hD hw
  have hpos : 0 < 8 * Real.log (2 * (D : ℝ)) + 21 := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  exact h.trans (mul_le_mul_of_nonneg_left (greenMatrix_form_le_continuumGreen hD w) hpos.le)

/-- **The continuum Green kernel has at most one negative square**: it is nonnegative on the
charge-free hyperplane. -/
theorem continuumGreen_nonneg_of_sum_eq_zero {D : ℕ} (hD : 1 ≤ D) {w : Fin D → ℝ}
    (hw : ∑ i, w i = 0) : 0 ≤ continuumGreen D w := by
  have h := continuumGreen_ge_charge hD w
  rw [hw] at h
  simpa using h

/-! ### The binding energy of the continuum -/

theorem monotone_bindingEnergy_factorial {D : ℕ} (hD : 1 ≤ D) :
    Monotone fun k : ℕ => bindingEnergy (k.factorial * D) :=
  monotone_nat_of_le_succ fun k => by
    rw [Nat.factorial_succ, Nat.mul_assoc]
    exact bindingEnergy_le_refined (Nat.mul_pos (Nat.factorial_pos k) hD) (by omega)

/-- **The binding energies along the tower converge** to a limit in `[δ, 3]`. -/
theorem tendsto_bindingEnergy_factorial {D : ℕ} (hD : 1 ≤ D) :
    ∃ μ : ℝ, dyadicDepth ≤ μ ∧ μ ≤ 3 ∧
      Tendsto (fun k : ℕ => bindingEnergy (k.factorial * D)) atTop (𝓝 μ) := by
  have hbdd : BddAbove (Set.range fun k : ℕ => bindingEnergy (k.factorial * D)) :=
    ⟨3, by
      rintro _ ⟨k, rfl⟩
      exact (bindingEnergy_lt_three (Nat.mul_pos (Nat.factorial_pos k) hD)).2.le⟩
  have hδ : dyadicDepth ≤ bindingEnergy (Nat.factorial 0 * D) := by
    have h := (bindingEnergy_lt_three (Nat.mul_pos (Nat.factorial_pos 0) hD)).1
    rwa [neutralBlock_one_one, neg_neg] at h
  refine ⟨⨆ k : ℕ, bindingEnergy (k.factorial * D), hδ.trans (le_ciSup hbdd 0),
    ciSup_le fun k => (bindingEnergy_lt_three (Nat.mul_pos (Nat.factorial_pos k) hD)).2.le,
    tendsto_atTop_ciSup (monotone_bindingEnergy_factorial hD) hbdd⟩

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
