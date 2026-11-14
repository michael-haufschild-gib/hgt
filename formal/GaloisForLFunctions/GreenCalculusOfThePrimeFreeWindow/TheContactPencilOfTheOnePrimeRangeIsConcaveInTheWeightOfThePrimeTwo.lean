import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGreenFormOfABoundWindowGrowsWithTheWindowAndAlongTheRefinementTower
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling

/-!
# The contact pencil of the one-prime range is concave in the weight of the prime two

Up to ratio three the primes enter a window only through the contact of `2` between the ends
and the two slivers of the dyadic middle. Weighting this contact by `t` gives the pencil
`P(t) = −𝒥 − t𝒞` of couplings (jets `𝒥`, contacts `𝒞`) and the Schur complement of the middle

  `S(t) = N_e − P(t)ᵀ G_D P(t) = N_e − 𝒥ᵀG_D𝒥 − 2t 𝒥ᵀG_D𝒞 − t² 𝒞ᵀG_D𝒞`

(`pencilSchur_form`): the jet form, the dipole and the contact form. `t = 1` is the window,
`t = 0` the window without primes, `t = −1` its sign twin.

* **Duality of the Green form** (`OneBoundState.inv_form_nonneg_iff`,
  `OneBoundState.inv_form_pos_of_dot_eq_zero`,
  `OneBoundState.inv_form_neg_of_pos_on_hyperplane`): for a form `M` with one bound state,
  `⟨w, M⁻¹w⟩ ≥ 0` iff the hyperplane `w^⊥` contains a nonzero vector of nonpositive energy;
  it is positive if `w ≠ 0` is orthogonal to a negative vector, and negative if `M` is positive
  on `w^⊥`. The mechanism is the positivity of `M` on the `M`-orthogonal complement of a
  negative vector (`OneBoundState.form_pos_of_orthogonal_neg`).
* **The contact form is nonnegative** (`contactGreen_nonneg`, `contactGreen_pos`): the contacts
  land in the slivers of the middle (`endContact_mulVec_bulk`), and throughout the one-prime
  range the bulk between the slivers has ratio at least `4/3` and binds. Hence
  `𝒞ᵀ G_D 𝒞 ⪰ 0` at every block size.
* **Concavity** (`pencilSchur_form_interp`, `pencilSchur_nonneg_of_mem_Icc`,
  `hermNegIndex_reweighted_eq_one_of_between`): `t ↦ ⟨e, S(t)e⟩` is concave. The weights of
  the prime two for which a window of the one-prime range holds exactly one bound state form
  an interval.
* **Opposite weights** (`pencilSchur_form_add_neg_le`, `pencilSchur_form_sub_neg`):
  `S(t) + S(−t) ⪯ 2 S(0)`, and `S(t) − S(−t)` is `−4t` times the dipole.
* **Windows of ratio three** (`not_pencilSchur_nonneg_and_neg`,
  `pencilSchur_weights_same_sign`, `not_hermNegIndex_eq_one_of_weight_nonpos`): the window
  without primes holds two bound states, so no two opposite weights are both admissible, all
  admissible weights have one sign, and the window `(R, 3R]` and a reweighting with a
  nonpositive weight of two never both hold exactly one bound state. A proof of one bound
  state on `(R, 3R]` has to use the sign of the dipole.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Duality of the Green form of a form with one bound state -/

section Duality

variable {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}

/-- **A form with one bound state is positive on the orthogonal complement of a negative
vector**, the complement taken for the form itself. -/
theorem OneBoundState.form_pos_of_orthogonal_neg (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) {y : ι → ℝ} (hy : y ⬝ᵥ (M *ᵥ ψ) = 0) (hy0 : y ≠ 0) :
    0 < y ⬝ᵥ (M *ᵥ y) := by
  have ha : φ ⬝ᵥ ψ ≠ 0 := fun h0 => by
    have h1 := h.floor ψ h0
    have h2 : 0 ≤ ψ ⬝ᵥ ψ := dotProduct_self_star_nonneg (v := ψ)
    linarith [mul_nonneg h.floor_pos.le h2]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (φ ⬝ᵥ ψ) = φ ⬝ᵥ y :=
    ⟨φ ⬝ᵥ y / (φ ⬝ᵥ ψ), div_mul_cancel₀ _ ha⟩
  -- `z = y − sψ` is orthogonal to the ground vector and `⟨y, My⟩ = ⟨z, Mz⟩ − s²⟨ψ, Mψ⟩`
  have hz : φ ⬝ᵥ (y - s • ψ) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hs, sub_self]
  have hfl := h.floor _ hz
  have hexp : (y - s • ψ) ⬝ᵥ (M *ᵥ (y - s • ψ)) =
      y ⬝ᵥ (M *ᵥ y) + s ^ 2 * (ψ ⬝ᵥ (M *ᵥ ψ)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_mulVec_symm h.symm ψ y, hy]
    ring
  rw [hexp] at hfl
  have hzz : 0 ≤ (y - s • ψ) ⬝ᵥ (y - s • ψ) := dotProduct_self_star_nonneg (v := y - s • ψ)
  have hs2 : 0 ≤ s ^ 2 * (-(ψ ⬝ᵥ (M *ᵥ ψ))) := mul_nonneg (sq_nonneg s) (neg_nonneg.mpr hψ.le)
  by_contra hneg
  rw [not_lt] at hneg
  have hz0 : (y - s • ψ) ⬝ᵥ (y - s • ψ) = 0 := by
    refine le_antisymm (le_of_not_gt fun hpos => ?_) hzz
    linarith [mul_pos h.floor_pos hpos]
  have h3 : s ^ 2 * (ψ ⬝ᵥ (M *ᵥ ψ)) = 0 := by
    rw [hz0, mul_zero] at hfl
    linarith
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp h3 with h1 | h1
    · exact (pow_eq_zero_iff two_ne_zero).mp h1
    · exact absurd h1 hψ.ne
  have hy' : y - s • ψ = 0 := dotProduct_self_eq_zero.mp hz0
  rw [hs0, zero_smul, sub_zero] at hy'
  exact hy0 hy'

variable [DecidableEq ι]

/-- The bilinear form of the inverse is symmetric. -/
theorem OneBoundState.inv_form_symm (h : OneBoundState M φ μ c) (x y : ι → ℝ) :
    x ⬝ᵥ (M⁻¹ *ᵥ y) = y ⬝ᵥ (M⁻¹ *ᵥ x) := by
  have h1 := dotProduct_mulVec_symm h.symm (M⁻¹ *ᵥ x) (M⁻¹ *ᵥ y)
  rw [h.mulVec_inv_mulVec, h.mulVec_inv_mulVec] at h1
  exact (dotProduct_comm _ _).trans (h1.symm.trans (dotProduct_comm _ _))

/-- The Green form along a line. -/
theorem OneBoundState.inv_form_add_smul (h : OneBoundState M φ μ c) (p q : ι → ℝ) (t : ℝ) :
    (p + t • q) ⬝ᵥ (M⁻¹ *ᵥ (p + t • q)) =
      p ⬝ᵥ (M⁻¹ *ᵥ p) + 2 * t * (p ⬝ᵥ (M⁻¹ *ᵥ q)) + t ^ 2 * (q ⬝ᵥ (M⁻¹ *ᵥ q)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [h.inv_form_symm q p]
  ring

/-- **The Green form is positive off a negative vector**: if `w ≠ 0` is orthogonal to a
negative vector of a form with one bound state, then `⟨w, M⁻¹w⟩ > 0`. -/
theorem OneBoundState.inv_form_pos_of_dot_eq_zero (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ : ψ ⬝ᵥ (M *ᵥ ψ) < 0) {w : ι → ℝ} (hw : ψ ⬝ᵥ w = 0) (hw0 : w ≠ 0) :
    0 < w ⬝ᵥ (M⁻¹ *ᵥ w) := by
  have hMu : M *ᵥ (M⁻¹ *ᵥ w) = w := h.mulVec_inv_mulVec w
  have hu : (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ ψ) = 0 := by
    rw [dotProduct_mulVec_symm h.symm, hMu, hw]
  have hu0 : M⁻¹ *ᵥ w ≠ 0 := fun h0 => hw0 (by rw [← hMu, h0, Matrix.mulVec_zero])
  have hpos := h.form_pos_of_orthogonal_neg hψ hu hu0
  rwa [hMu, dotProduct_comm] at hpos

/-- **The Green form is nonnegative off a vector of nonpositive energy.** -/
theorem OneBoundState.inv_form_nonneg_of_dot_eq_zero (h : OneBoundState M φ μ c) {ψ : ι → ℝ}
    (hψ0 : ψ ≠ 0) (hψ : ψ ⬝ᵥ (M *ᵥ ψ) ≤ 0) {w : ι → ℝ} (hw : ψ ⬝ᵥ w = 0) :
    0 ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) := by
  by_contra hneg
  rw [not_le] at hneg
  have hMu : M *ᵥ (M⁻¹ *ᵥ w) = w := h.mulVec_inv_mulVec w
  -- otherwise `M⁻¹w` is a negative vector, and `ψ` lies in its orthogonal complement
  have hu : (M⁻¹ *ᵥ w) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ w)) < 0 := by rwa [hMu, dotProduct_comm]
  have hψu : ψ ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ w)) = 0 := by rw [hMu, hw]
  linarith [h.form_pos_of_orthogonal_neg hu hψu hψ0]

/-- **The Green form is negative at `w` if the form is positive on the hyperplane `w^⊥`.** -/
theorem OneBoundState.inv_form_neg_of_pos_on_hyperplane (h : OneBoundState M φ μ c)
    {w : ι → ℝ} (hpos : ∀ y : ι → ℝ, y ≠ 0 → y ⬝ᵥ w = 0 → 0 < y ⬝ᵥ (M *ᵥ y)) :
    w ⬝ᵥ (M⁻¹ *ᵥ w) < 0 := by
  by_contra hge
  rw [not_lt] at hge
  have hMu : M *ᵥ (M⁻¹ *ᵥ w) = w := h.mulVec_inv_mulVec w
  have hφφ : φ ⬝ᵥ (M *ᵥ φ) = -μ := by
    rw [h.eig, dotProduct_smul, h.unit, smul_eq_mul, mul_one]
  rcases hge.eq_or_lt with h0 | hlt
  · -- `⟨w, M⁻¹w⟩ = 0`: the vector `M⁻¹w` (or the ground vector, if `w = 0`) has no energy
    by_cases hu0 : M⁻¹ *ᵥ w = 0
    · have hw0 : w = 0 := by rw [← hMu, hu0, Matrix.mulVec_zero]
      have hφ0 : φ ≠ 0 := fun hz => by
        have h1 := h.unit
        rw [hz, zero_dotProduct] at h1
        exact zero_ne_one h1
      have h1 := hpos φ hφ0 (by rw [hw0, dotProduct_zero])
      rw [hφφ] at h1
      linarith [h.depth_pos]
    · have h1 := hpos _ hu0 (by rw [dotProduct_comm]; exact h0.symm)
      rw [hMu, dotProduct_comm] at h1
      linarith
  · -- `⟨w, M⁻¹w⟩ > 0`: move the ground vector into the hyperplane along `M⁻¹w`
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t * (w ⬝ᵥ (M⁻¹ *ᵥ w)) = φ ⬝ᵥ w :=
      ⟨φ ⬝ᵥ w / (w ⬝ᵥ (M⁻¹ *ᵥ w)), div_mul_cancel₀ _ hlt.ne'⟩
    have hyw : (φ - t • (M⁻¹ *ᵥ w)) ⬝ᵥ w = 0 := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (M⁻¹ *ᵥ w) w, ht,
        sub_self]
    have hyM : (φ - t • (M⁻¹ *ᵥ w)) ⬝ᵥ (M *ᵥ (φ - t • (M⁻¹ *ᵥ w))) =
        -μ - t ^ 2 * (w ⬝ᵥ (M⁻¹ *ᵥ w)) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_mulVec_symm h.symm (M⁻¹ *ᵥ w) φ, hMu, hφφ,
        dotProduct_comm (M⁻¹ *ᵥ w) w, ← ht]
      ring
    have hneg : (φ - t • (M⁻¹ *ᵥ w)) ⬝ᵥ (M *ᵥ (φ - t • (M⁻¹ *ᵥ w))) < 0 := by
      rw [hyM]
      linarith [h.depth_pos, mul_nonneg (sq_nonneg t) hlt.le]
    by_cases hy0 : φ - t • (M⁻¹ *ᵥ w) = 0
    · rw [hy0, zero_dotProduct] at hneg
      exact lt_irrefl _ hneg
    · linarith [hpos _ hy0 hyw]

/-- **Duality of the Green form.** For a form with one bound state, `⟨w, M⁻¹w⟩ ≥ 0` iff the
hyperplane `w^⊥` contains a nonzero vector of nonpositive energy. -/
theorem OneBoundState.inv_form_nonneg_iff (h : OneBoundState M φ μ c) (w : ι → ℝ) :
    0 ≤ w ⬝ᵥ (M⁻¹ *ᵥ w) ↔
      ∃ ψ : ι → ℝ, ψ ≠ 0 ∧ ψ ⬝ᵥ w = 0 ∧ ψ ⬝ᵥ (M *ᵥ ψ) ≤ 0 := by
  constructor
  · intro hw
    by_contra hno
    refine absurd (h.inv_form_neg_of_pos_on_hyperplane fun y hy0 hyw => ?_) (not_lt.mpr hw)
    by_contra hle
    exact hno ⟨y, hy0, hyw, not_lt.mp hle⟩
  · rintro ⟨ψ, hψ0, hψw, hψ⟩
    exact h.inv_form_nonneg_of_dot_eq_zero hψ0 hψ hψw

/-- **One bound state of a two-block form over a middle with one bound state** is the
nonnegativity of the Schur complement of the middle. -/
theorem OneBoundState.hermNegIndex_fromBlocks_eq_one_iff {κ : Type*} [Fintype κ]
    [DecidableEq κ] (h : OneBoundState M φ μ c) (P : Matrix ι κ ℝ) {N : Matrix κ κ ℝ}
    (hN : ∀ x y, N x y = N y x) :
    hermNegIndex ((fromBlocks M P Pᵀ N).map (↑) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) = 1 ↔
      ∀ e : κ → ℝ, 0 ≤ e ⬝ᵥ ((N - Pᵀ * M⁻¹ * P) *ᵥ e) := by
  rw [hermNegIndex_fromBlocks_transpose h.symm h.isUnit P hN, h.hermNegIndex_eq_one,
    Nat.add_eq_left, hermNegIndex_eq_zero_iff_forall]

omit [DecidableEq ι] in
/-- **The inverse is positive off a bound principal submatrix**: on the nonzero vectors that
vanish on the coordinates of a principal submatrix which still has a bound state. -/
theorem inv_form_pos_of_comp_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M' : Matrix κ κ ℝ} {φ' : κ → ℝ} {μ' c' : ℝ} (h' : OneBoundState M' φ' μ' c') (f : ι → κ)
    (h : OneBoundState (M'.submatrix f f) φ μ c) {w : κ → ℝ} (hw : w ∘ f = 0) (hw0 : w ≠ 0) :
    0 < w ⬝ᵥ (M'⁻¹ *ᵥ w) := by
  refine h'.inv_form_pos_of_dot_eq_zero (ψ := inclusionMatrix f *ᵥ φ) ?_ ?_ hw0
  · rw [← dotProduct_transpose_mul_mul_mulVec, inclusionMatrix_transpose_mul_mul, h.eig,
      dotProduct_smul, h.unit, smul_eq_mul, mul_one]
    linarith [h.depth_pos]
  · rw [dotProduct_comm, dotProduct_mulVec_eq_transpose, inclusionMatrix_transpose_mulVec, hw,
      zero_dotProduct]

end Duality

/-- **The Green matrix of the dyadic middle is positive on its slivers**: on the nonzero
vectors that vanish on a sub-window `(D + s, D + s + J']` of ratio at least `4/3`. -/
theorem greenMatrix_pos_of_sliver {D s J' : ℕ} (hJ' : 1 ≤ J') (hs : s + J' ≤ D)
    (hbind : D + s ≤ 3 * J') {w : Fin D → ℝ} (hw : ∀ i : Fin J', w (shiftFin s hs i) = 0)
    (hw0 : w ≠ 0) : 0 < w ⬝ᵥ (greenMatrix D *ᵥ w) := by
  obtain ⟨ψ, ν, -, hT, -⟩ := exists_oneBoundState_neutralWindow_of_ratio (Q := 2)
    (R := D + s) hJ' (by omega) hbind le_rfl
  have hsub : OneBoundState ((primeFreeMiddle D).submatrix (shiftFin s hs) (shiftFin s hs))
      ψ ν (1 / 5000) := by
    rw [← neutralWindow_dyadic_eq 2 D, neutralWindow_submatrix_shiftFin]
    exact hT
  exact inv_form_pos_of_comp_eq_zero (oneBoundState_primeFreeMiddle (by omega))
    (shiftFin s hs) hsub (funext hw) hw0

/-! ### The jet form, the dipole and the contact form -/

/-- The Green form of the jets of the two ends. -/
def jetGreen (R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) : ℝ :=
  (endJet R a b *ᵥ e) ⬝ᵥ (greenMatrix (R + a) *ᵥ (endJet R a b *ᵥ e))

/-- **The dipole**: the Green pairing of the jets of the ends with their contacts. -/
def dipoleGreen (Q R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) : ℝ :=
  (endJet R a b *ᵥ e) ⬝ᵥ (greenMatrix (R + a) *ᵥ (endContact Q R a b *ᵥ e))

/-- The Green form of the contacts of the two ends. -/
def contactGreen (Q R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) : ℝ :=
  (endContact Q R a b *ᵥ e) ⬝ᵥ (greenMatrix (R + a) *ᵥ (endContact Q R a b *ᵥ e))

/-- The Schur complement of the dyadic middle in the window `(R, 2(R + a) + b]` with the
contacts weighted by `t`. -/
def pencilSchur (Q R a b : ℕ) (t : ℝ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  endForm Q R a b - (pencilCoupling Q R a b t)ᵀ * greenMatrix (R + a) * pencilCoupling Q R a b t

theorem pencilSchur_one (Q R a b : ℕ) : pencilSchur Q R a b 1 = overlapSchur Q R a b := by
  rw [pencilSchur, pencilCoupling_one, overlapSchur]

/-- **The normal form of the pencil**: the end form minus the jet form, the dipole and the
contact form. -/
theorem pencilSchur_form (Q R a b : ℕ) (hD : 1 ≤ R + a) (t : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e) =
      e ⬝ᵥ (endForm Q R a b *ᵥ e) - jetGreen R a b e - 2 * t * dipoleGreen Q R a b e -
        t ^ 2 * contactGreen Q R a b e := by
  have hM := oneBoundState_primeFreeMiddle hD
  have hmul : pencilCoupling Q R a b t *ᵥ e =
      -(endJet R a b *ᵥ e + t • (endContact Q R a b *ᵥ e)) := by
    rw [pencilCoupling, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, neg_add']
  rw [pencilSchur, Matrix.sub_mulVec, dotProduct_sub, dotProduct_transpose_mul_mul_mulVec, hmul,
    Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, greenMatrix,
    hM.inv_form_add_smul, jetGreen, dipoleGreen, contactGreen, greenMatrix]
  ring

/-- **The contacts of the ends land in the slivers of the middle**: the contact coupling
vanishes on the bulk, the blocks `⌈b/2⌉, …, R − a − 1` of the middle. -/
theorem endContact_mulVec_bulk (Q R a b : ℕ)
    (hs : (b + 1) / 2 + (R - a - (b + 1) / 2) ≤ R + a) (e : Fin a ⊕ Fin b → ℝ)
    (i : Fin (R - a - (b + 1) / 2)) :
    (endContact Q R a b *ᵥ e) (shiftFin ((b + 1) / 2) hs i) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  have h0 : endContact Q R a b (shiftFin ((b + 1) / 2) hs i) p = 0 :=
    endContact_eq_zero_of_bulk Q R a b _
      (by show b ≤ 2 * ((b + 1) / 2 + (i : ℕ)); omega)
      (by show R + a + ((b + 1) / 2 + (i : ℕ)) < 2 * R; have := i.2; omega) p
  rw [h0, zero_mul]

/-- **The contact form is nonnegative**: when the bulk of the middle between the two contact
slivers has ratio at least `4/3`, that is `2a + 2⌈b/2⌉ ≤ R`, the Green form of the contacts is
nonnegative at every block size. -/
theorem contactGreen_nonneg {Q R a b : ℕ} (hR : 1 ≤ R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R)
    (e : Fin a ⊕ Fin b → ℝ) : 0 ≤ contactGreen Q R a b e := by
  have hs : (b + 1) / 2 + (R - a - (b + 1) / 2) ≤ R + a := by omega
  exact greenMatrix_nonneg_of_sliver (D := R + a) (s := (b + 1) / 2)
    (J' := R - a - (b + 1) / 2) (by omega) hs (by omega) (endContact_mulVec_bulk Q R a b hs e)

/-- The contact form is positive on the end vectors with a contact. -/
theorem contactGreen_pos {Q R a b : ℕ} (hR : 1 ≤ R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R)
    {e : Fin a ⊕ Fin b → ℝ} (he : endContact Q R a b *ᵥ e ≠ 0) : 0 < contactGreen Q R a b e := by
  have hs : (b + 1) / 2 + (R - a - (b + 1) / 2) ≤ R + a := by omega
  exact greenMatrix_pos_of_sliver (D := R + a) (s := (b + 1) / 2)
    (J' := R - a - (b + 1) / 2) (by omega) hs (by omega) (endContact_mulVec_bulk Q R a b hs e)
    he

/-! ### Concavity -/

/-- **Between two weights the pencil exceeds its chord by the contact form.** -/
theorem pencilSchur_form_interp (Q R a b : ℕ) (hD : 1 ≤ R + a) (t₀ t₁ t : ℝ)
    (e : Fin a ⊕ Fin b → ℝ) :
    (t₁ - t₀) * (e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e)) =
      (t₁ - t) * (e ⬝ᵥ (pencilSchur Q R a b t₀ *ᵥ e)) +
        (t - t₀) * (e ⬝ᵥ (pencilSchur Q R a b t₁ *ᵥ e)) +
        (t - t₀) * (t₁ - t) * (t₁ - t₀) * contactGreen Q R a b e := by
  rw [pencilSchur_form Q R a b hD t, pencilSchur_form Q R a b hD t₀,
    pencilSchur_form Q R a b hD t₁]
  ring

/-- **The admissible weights form an interval**: if the pencil is nonnegative at two weights,
it is nonnegative between them. -/
theorem pencilSchur_nonneg_of_mem_Icc {Q R a b : ℕ} (hR : 1 ≤ R)
    (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) {t₀ t₁ t : ℝ}
    (h₀ : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b t₀ *ᵥ e))
    (h₁ : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b t₁ *ᵥ e))
    (ht₀ : t₀ ≤ t) (ht₁ : t ≤ t₁) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e) := by
  rcases ht₀.eq_or_lt with rfl | hlt
  · exact h₀ e
  have hpos : 0 < t₁ - t₀ := by linarith
  have hid := pencilSchur_form_interp Q R a b (by omega) t₀ t₁ t e
  have h3 : 0 ≤ (t - t₀) * (t₁ - t) * (t₁ - t₀) * contactGreen Q R a b e :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr ht₀) (sub_nonneg.mpr ht₁)) hpos.le)
      (contactGreen_nonneg hR hbulk e)
  have hge : (t₁ - t₀) * 0 ≤ (t₁ - t₀) * (e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e)) := by
    rw [hid, mul_zero]
    linarith [mul_nonneg (sub_nonneg.mpr ht₁) (h₀ e), mul_nonneg (sub_nonneg.mpr ht₀) (h₁ e)]
  exact le_of_mul_le_mul_left hge hpos

/-- **Opposite weights**: the pencil at `t` and at `−t` add up to at most twice the pencil
without primes. -/
theorem pencilSchur_form_add_neg_le {Q R a b : ℕ} (hR : 1 ≤ R)
    (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) (t : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e) + e ⬝ᵥ (pencilSchur Q R a b (-t) *ᵥ e) ≤
      2 * (e ⬝ᵥ (pencilSchur Q R a b 0 *ᵥ e)) := by
  rw [pencilSchur_form Q R a b (by omega) t, pencilSchur_form Q R a b (by omega) (-t),
    pencilSchur_form Q R a b (by omega) 0]
  nlinarith [mul_nonneg (sq_nonneg t) (contactGreen_nonneg (Q := Q) hR hbulk e)]

/-- **A weight and its opposite differ by the dipole.** -/
theorem pencilSchur_form_sub_neg (Q R a b : ℕ) (hD : 1 ≤ R + a) (t : ℝ)
    (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e) - e ⬝ᵥ (pencilSchur Q R a b (-t) *ᵥ e) =
      -(4 * t * dipoleGreen Q R a b e) := by
  rw [pencilSchur_form Q R a b hD t, pencilSchur_form Q R a b hD (-t)]
  ring

/-! ### Windows with reweighted contacts -/

/-- **One bound state of a window of the one-prime range with reweighted contacts** is the
nonnegativity of the pencil at the weight of the prime two. -/
theorem hermNegIndex_reweighted_eq_one_iff_pencilSchur {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b (ω 2) *ᵥ e) := by
  have hsymm : ∀ x y, endForm Q R a b x y = endForm Q R a b y x :=
    fromBlocks_symm (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
      (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b),
    reweightedWindow_submatrix_overlapEquiv_of_le_three_mul hR hQ h3 ω,
    (oneBoundState_primeFreeMiddle (by omega)).hermNegIndex_fromBlocks_eq_one_iff _ hsymm,
    pencilSchur, greenMatrix]

/-- **The weights of the prime two for which a window of the one-prime range holds exactly one
bound state form an interval.** -/
theorem hermNegIndex_reweighted_eq_one_of_between {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) {ω₀ ω₁ ω : ℕ → ℝ}
    (h₀ : hermNegIndex ((windowMatrix (reweightedNeutral ω₀ Q) R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1)
    (h₁ : hermNegIndex ((windowMatrix (reweightedNeutral ω₁ Q) R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1)
    (hle₀ : ω₀ 2 ≤ ω 2) (hle₁ : ω 2 ≤ ω₁ 2) :
    hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 := by
  have h3 : 2 * (R + a) + b ≤ 3 * R := by omega
  rw [hermNegIndex_reweighted_eq_one_iff_pencilSchur hR hQ h3] at h₀ h₁ ⊢
  exact pencilSchur_nonneg_of_mem_Icc hR hbulk h₀ h₁ hle₀ hle₁

/-! ### Windows of ratio three -/

/-- **On a window of ratio three the pencil has a negative direction at every weight in
`[−4, 0]`**, at every block size. -/
theorem exists_pencilSchur_neg {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) {t : ℝ} (ht1 : -4 ≤ t) (ht2 : t ≤ 0) :
    ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e) < 0 := by
  obtain ⟨e, he⟩ := exists_pencil_greenForm_gt (Q := Q) hR hQ h3 ht1 ht2
  refine ⟨e, ?_⟩
  rw [pencilSchur, greenMatrix,
    schur_form_eq_channels (oneBoundState_primeFreeMiddle (by omega)) _ _ e, ← greenPositive]
  linarith

/-- **A window of ratio three does not hold one bound state at two opposite weights of the
prime two**: the window without primes holds two. -/
theorem not_pencilSchur_nonneg_and_neg {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) (t : ℝ) :
    ¬((∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e)) ∧
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b (-t) *ᵥ e)) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨e, he⟩ := exists_pencilSchur_neg (Q := Q) hR hQ h3 (t := 0) (by norm_num) le_rfl
  linarith [pencilSchur_form_add_neg_le (Q := Q) hR hbulk t e, h₁ e, h₂ e]

/-- **The admissible weights of a window of ratio three have one sign.** -/
theorem pencilSchur_weights_same_sign {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) {t t' : ℝ}
    (h : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b t *ᵥ e))
    (h' : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b t' *ᵥ e)) : 0 < t * t' := by
  obtain ⟨e, he⟩ := exists_pencilSchur_neg (Q := Q) hR hQ h3 (t := 0) (by norm_num) le_rfl
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rcases lt_or_ge t' 0 with ht' | ht'
    · exact mul_pos_of_neg_of_neg ht ht'
    · exact absurd (pencilSchur_nonneg_of_mem_Icc hR hbulk h h' ht.le ht' e) (not_le.mpr he)
  · rw [ht] at h
    exact absurd (h e) (not_le.mpr he)
  · rcases lt_or_ge 0 t' with ht' | ht'
    · exact mul_pos ht ht'
    · exact absurd (pencilSchur_nonneg_of_mem_Icc hR hbulk h' h ht' ht.le e) (not_le.mpr he)

/-- **The window `(R, 3R]` and a reweighting with a nonpositive weight of the prime two never
both hold exactly one bound state.** Weakening the contact of two through zero or twisting its
sign, by any amount, is separated from the window by the window without primes. -/
theorem not_hermNegIndex_eq_one_of_weight_nonpos {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) (hbulk : 2 * a + 2 * ((b + 1) / 2) ≤ R) {ω : ℕ → ℝ}
    (hω : ω 2 ≤ 0) :
    ¬(hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 ∧
      hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (a + (R + a) + b)).map (↑) :
        Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1) := by
  rintro ⟨htrue, htwist⟩
  have h1 : ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (pencilSchur Q R a b 1 *ᵥ e) := by
    rw [pencilSchur_one]
    exact (hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b hR hQ).mp htrue
  have h2 := (hermNegIndex_reweighted_eq_one_iff_pencilSchur hR hQ (by omega) ω).mp htwist
  have h4 := pencilSchur_weights_same_sign hR hQ h3 hbulk h1 h2
  linarith

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
