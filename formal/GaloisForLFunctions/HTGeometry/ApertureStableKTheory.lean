import GaloisForLFunctions.HTGeometry.ApertureConeWinding
import GaloisForLFunctions.HTGeometry.FiniteUnitaryFundamentalGroup
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Stable `K₁` of the open-history ideal

The cone module computes `K₁(J_T)` with `1 × 1` unitaries.  Here `K₁(J_T)` is the stable group:
classes of unitaries of all matrix algebras `M_n(J_T⁺)`, `J_T⁺ = ℂ·1 + J_T`, where `u ∈ M_n` and
`v ∈ M_m` are identified when their corner stabilizations `u ⊕ 1`, `v ⊕ 1` in a common `M_k` are
joined by a path of unitaries; the product is block multiplication after stabilization.

* The symbol `t ↦ (λᵢⱼ + gᵢⱼ(t))` is a unital `*`-homomorphism `J_T⁺ → ℂ` for each aperture
  parameter `t`, so a unitary of `M_n(J_T⁺)` is a closed loop in `U(n)`, and conversely every closed
  loop of unitary matrices is the symbol of a unique unitary of `M_n(J_T⁺)`.
* Its **stable winding index** is the winding number of `t ↦ det(symbol)`; it is invariant under
  paths and stabilization, and additive.
* **Classification.** Free loops are homotopic to based ones by transporting the base point in the
  connected group `U(n)`; based loops with equal determinant are homotopic because the determinant
  classifies `π₁(U(n+1))`; and determinant loops of equal winding are homotopic in `ℂ^×`.  Hence
  two unitaries are stably homotopic exactly when their winding indices agree.
* **(SAC.8)** `K₁(J_T) ≃* ℤ`, and the connecting map `δ(n) = [exp(2πi n e_1)]` is an isomorphism;
  on a projection `P ∈ M_k(ℂ)` the exponential boundary `(1 − P) ⊗ 1 + P ⊗ exp(2πi e_1)` has class
  `δ(rank P)` (`det((1 − P) + zP) = z^{rank P}`).
* **(SAC.9), (SAC.10), (SAC.12)** `δ(1)` winds once; every scale lift gives `δ(1)`; the relative
  exponential `exp(2πi(e_c − e_d))` is trivial in the stable group.
* The `1 × 1` model of the cone module maps bijectively onto the stable group.
-/

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Block

variable (R : Type*) [Ring R]

/-- The coordinate inclusion `Fin n ↪ Fin m` as a `0/1` matrix `P`. -/
def cornerIncl (n m : ℕ) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

/-- The coordinate projection `Pᵀ`, written without transposition so that no commutativity of
the coefficients is needed. -/
def cornerProj (n m : ℕ) : Matrix (Fin n) (Fin m) R :=
  Matrix.of fun j i => if (i : ℕ) = j then 1 else 0

variable {R}

theorem cornerIncl_apply (n m : ℕ) (i : Fin m) (j : Fin n) :
    cornerIncl R n m i j = if (i : ℕ) = j then 1 else 0 := rfl

theorem cornerProj_apply (n m : ℕ) (j : Fin n) (i : Fin m) :
    cornerProj R n m j i = if (i : ℕ) = j then 1 else 0 := rfl

theorem cornerProj_mul_cornerIncl {n m : ℕ} (h : n ≤ m) :
    cornerProj R n m * cornerIncl R n m = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨a, lt_of_lt_of_le a.2 h⟩ : Fin m)]
  · simp only [cornerProj_apply, cornerIncl_apply, Matrix.one_apply, if_true, one_mul, Fin.val_inj]
  · intro i _ hi
    have : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    simp [cornerProj_apply, this]
  · simp

theorem cornerIncl_mul_cornerIncl {n m k : ℕ} (h : n ≤ m) :
    cornerIncl R m k * cornerIncl R n m = cornerIncl R n k := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j, lt_of_lt_of_le j.2 h⟩ : Fin m)]
  · simp [cornerIncl_apply]
  · intro l _ hl
    have : (l : ℕ) ≠ j := fun h' => hl (Fin.ext h')
    simp [cornerIncl_apply, this]
  · simp

theorem cornerProj_mul_cornerProj {n m k : ℕ} (h : n ≤ m) :
    cornerProj R n m * cornerProj R m k = cornerProj R n k := by
  ext j i
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j, lt_of_lt_of_le j.2 h⟩ : Fin m)]
  · simp [cornerProj_apply]
  · intro l _ hl
    have : (l : ℕ) ≠ j := fun h' => hl (Fin.ext h')
    simp [cornerProj_apply, this]
  · simp

theorem cornerIncl_self (n : ℕ) : cornerIncl R n n = 1 := by
  ext i j
  simp [cornerIncl_apply, Matrix.one_apply, Fin.val_inj]

theorem cornerProj_self (n : ℕ) : cornerProj R n n = 1 := by
  ext i j
  simp [cornerProj_apply, Matrix.one_apply, Fin.val_inj, eq_comm]

/-- The stabilization `u ↦ u ⊕ 1` of `M_n(R)` into `M_m(R)`: `P u Pᵀ + (1 − P Pᵀ)`. -/
def cornerEmbed (n m : ℕ) (u : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R :=
  cornerIncl R n m * u * cornerProj R n m + (1 - cornerIncl R n m * cornerProj R n m)

theorem cornerEmbed_mul {n m : ℕ} (h : n ≤ m) (u v : Matrix (Fin n) (Fin n) R) :
    cornerEmbed n m (u * v) = cornerEmbed n m u * cornerEmbed n m v := by
  set P : Matrix (Fin m) (Fin n) R := cornerIncl R n m
  set Q : Matrix (Fin n) (Fin m) R := cornerProj R n m
  have hPP : Q * P = 1 := cornerProj_mul_cornerIncl h
  have hQP : (1 - P * Q) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one, sub_self]
  have hPQ : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPP, Matrix.one_mul, sub_self]
  have hQQ : (1 - P * Q) * (1 - P * Q) = 1 - P * Q := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.zero_mul, sub_zero]
  unfold cornerEmbed
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hQQ]
  have h1 : P * u * Q * (P * v * Q) = P * (u * v) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hPP, Matrix.one_mul]
  have h2 : P * u * Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_assoc, hPQ, Matrix.mul_zero]
  have h3 : (1 - P * Q) * (P * v * Q) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.zero_mul, Matrix.zero_mul]
  rw [h1, h2, h3, add_zero, zero_add]

theorem cornerEmbed_one (n m : ℕ) : cornerEmbed n m (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [cornerEmbed]

theorem cornerEmbed_self (n : ℕ) (u : Matrix (Fin n) (Fin n) R) : cornerEmbed n n u = u := by
  simp [cornerEmbed, cornerIncl_self, cornerProj_self]

theorem cornerEmbed_cornerEmbed {n m k : ℕ} (h : n ≤ m) (u : Matrix (Fin n) (Fin n) R) :
    cornerEmbed m k (cornerEmbed n m u) = cornerEmbed n k u := by
  unfold cornerEmbed
  rw [← cornerIncl_mul_cornerIncl (R := R) (k := k) h, ← cornerProj_mul_cornerProj (R := R) (k := k) h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

theorem cornerIncl_mul_mul_cornerProj_apply (n m : ℕ) (u : Matrix (Fin n) (Fin n) R)
    (i j : Fin m) :
    (cornerIncl R n m * u * cornerProj R n m) i j =
      if h : (i : ℕ) < n ∧ (j : ℕ) < n then u ⟨i, h.1⟩ ⟨j, h.2⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) < n
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [Matrix.mul_apply, cornerProj_apply]
      by_cases hi : (i : ℕ) < n
      · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
        · simp [cornerIncl_apply, hi, hj]
        · intro l _ hl
          have : (i : ℕ) ≠ l := fun h' => hl (Fin.ext h'.symm)
          simp [cornerIncl_apply, this]
        · simp
      · have hz : ∀ l : Fin n, cornerIncl R n m i l = 0 := by
          intro l
          have : (i : ℕ) ≠ l := fun h' => hi (h' ▸ l.2)
          simp [cornerIncl_apply, this]
        simp [hz, hi]
    · intro l _ hl
      have : (j : ℕ) ≠ l := fun h' => hl (Fin.ext h'.symm)
      simp [cornerProj_apply, this]
    · simp
  · have hz : ∀ l : Fin n, cornerProj R n m l j = 0 := by
      intro l
      have : (j : ℕ) ≠ l := fun h' => hj (h' ▸ l.2)
      simp [cornerProj_apply, this]
    simp [hz, hj]

theorem cornerEmbed_apply (n m : ℕ) (u : Matrix (Fin n) (Fin n) R) (i j : Fin m) :
    cornerEmbed n m u i j =
      if h : (i : ℕ) < n ∧ (j : ℕ) < n then u ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by
  have h1 := cornerIncl_mul_mul_cornerProj_apply n m (1 : Matrix (Fin n) (Fin n) R) i j
  rw [Matrix.mul_one] at h1
  unfold cornerEmbed
  rw [Matrix.add_apply, Matrix.sub_apply, h1, cornerIncl_mul_mul_cornerProj_apply]
  by_cases h : (i : ℕ) < n ∧ (j : ℕ) < n
  · rw [dif_pos h, dif_pos h, dif_pos h]
    have h1' : (1 : Matrix (Fin n) (Fin n) R) ⟨i, h.1⟩ ⟨j, h.2⟩ =
        (1 : Matrix (Fin m) (Fin m) R) i j := by
      simp only [Matrix.one_apply, Fin.ext_iff]
    rw [h1', sub_self, add_zero]
  · rw [dif_neg h, dif_neg h, dif_neg h, zero_add, sub_zero, Matrix.one_apply]

section StarBlock

variable {R : Type*} [Ring R] [StarRing R]

theorem cornerIncl_conjTranspose (n m : ℕ) :
    (cornerIncl R n m).conjTranspose = cornerProj R n m := by
  ext j i
  simp only [Matrix.conjTranspose_apply, cornerIncl_apply, cornerProj_apply]
  split_ifs <;> simp

theorem cornerProj_conjTranspose (n m : ℕ) :
    (cornerProj R n m).conjTranspose = cornerIncl R n m := by
  ext i j
  simp only [Matrix.conjTranspose_apply, cornerIncl_apply, cornerProj_apply]
  split_ifs <;> simp

theorem star_cornerEmbed (n m : ℕ) (u : Matrix (Fin n) (Fin n) R) :
    star (cornerEmbed n m u) = cornerEmbed n m (star u) := by
  simp only [cornerEmbed, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    cornerIncl_conjTranspose, cornerProj_conjTranspose, Matrix.mul_assoc]

theorem cornerEmbed_mem_unitary {n m : ℕ} (h : n ≤ m) {u : Matrix (Fin n) (Fin n) R}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) R)) :
    cornerEmbed n m u ∈ unitary (Matrix (Fin m) (Fin m) R) := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [star_cornerEmbed, ← cornerEmbed_mul h, ← cornerEmbed_mul h, hu.1, hu.2, cornerEmbed_one]
  exact ⟨rfl, rfl⟩

end StarBlock

theorem cornerEmbed_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n m : ℕ)
    (u : Matrix (Fin n) (Fin n) R) :
    (cornerEmbed n m u).map f = cornerEmbed n m (u.map f) := by
  ext i j
  simp only [Matrix.map_apply, cornerEmbed_apply]
  split_ifs <;> simp

theorem continuous_cornerEmbed {R : Type*} [Ring R] [TopologicalSpace R] (n m : ℕ) :
    Continuous (cornerEmbed (R := R) n m) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cornerEmbed_apply]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const

/-- Stabilization does not change the determinant. -/
theorem det_cornerEmbed {R : Type*} [CommRing R] {n m : ℕ} (h : n ≤ m)
    (u : Matrix (Fin n) (Fin n) R) : (cornerEmbed n m u).det = u.det := by
  set e : Fin n ⊕ Fin (m - n) ≃ Fin m := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))
  have hre : Matrix.reindex e.symm e.symm (cornerEmbed n m u) = Matrix.fromBlocks u 0 0 1 := by
    ext (a | a) (b | b)
    · simp [e, cornerEmbed_apply]
    · simp [e, cornerEmbed_apply, Fin.ext_iff]
      omega
    · simp [e, cornerEmbed_apply, Fin.ext_iff]
      omega
    · simp [e, cornerEmbed_apply, Matrix.one_apply, Fin.ext_iff]
  rw [← Matrix.det_reindex_self e.symm, hre, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

end Block

/-- For a projection `P`, `det((1 − P) + zP) = z ^ rank P` (diagonalize `P`; its eigenvalues are
`0` and `1`). -/
theorem det_one_sub_add_smul_of_projection {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) (z : ℂ) :
    ((1 - P) + z • P).det = z ^ P.rank := by
  set U : Matrix (Fin k) (Fin k) ℂ := (hPh.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)
  set w : Fin k → ℂ := RCLike.ofReal ∘ hPh.eigenvalues
  have hspec : P = U * Matrix.diagonal w * star U := by
    have h := hPh.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hPh.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hPh.eigenvectorUnitary.2
  have hDP : star U * P * U = Matrix.diagonal w := by
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hD : Matrix.diagonal w * Matrix.diagonal w = Matrix.diagonal w := by
    rw [← hDP]
    calc star U * P * U * (star U * P * U) = star U * P * (U * star U) * P * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * (P * P) * U := by rw [hUU', Matrix.mul_one, Matrix.mul_assoc (star U)]
      _ = star U * P * U := by rw [hPP]
  have hw : ∀ i, w i * w i = w i := fun i => by
    have := congrFun (congrFun hD i) i
    simpa [Matrix.diagonal_mul_diagonal] using this
  have hw01 : ∀ i, hPh.eigenvalues i = 0 ∨ hPh.eigenvalues i = 1 := by
    intro i
    have h := hw i
    simp only [w, Function.comp_apply] at h
    have h' : hPh.eigenvalues i * hPh.eigenvalues i = hPh.eigenvalues i := by exact_mod_cast h
    rcases mul_eq_zero.mp (show hPh.eigenvalues i * (hPh.eigenvalues i - 1) = 0 by linarith) with
      h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hF : (1 - P) + z • P = U * Matrix.diagonal (fun i => 1 - w i + z * w i) * star U := by
    have hdiag : Matrix.diagonal (fun i => 1 - w i + z * w i) = 1 - Matrix.diagonal w + z • Matrix.diagonal w := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hdiag, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.sub_mul,
      hUU', Matrix.mul_smul, Matrix.smul_mul, ← hspec]
  rw [hF, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm (Matrix.det U), mul_assoc, ← Matrix.det_mul, hUU', Matrix.det_one,
    mul_one, hPh.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hfac : ∀ i, 1 - w i + z * w i = if hPh.eigenvalues i ≠ 0 then z else 1 := fun i => by
    rcases hw01 i with h | h <;> simp [w, h]
  simp only [hfac]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-! ## The unitization of the open-history ideal and its symbol evaluations -/

section Aperture

open _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)

/-- The unitization `J_T⁺ = ℂ·1 + J_T` of the open-history ideal, inside the unitization of the
corona. -/
def openUnitization : StarSubalgebra ℂ (Unitization ℂ (BoundaryCorona H)) where
  carrier := {x | x.snd ∈ openHistoryIdeal hT hcpt}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Unitization.snd_mul]
    exact add_mem (add_mem ((openHistoryIdeal hT hcpt).smul_mem _ hy)
      ((openHistoryIdeal hT hcpt).smul_mem _ hx)) (mul_mem hx hy)
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Unitization.snd_add]
    exact add_mem hx hy
  algebraMap_mem' c := by
    simp only [Set.mem_setOf_eq, Unitization.algebraMap_eq_inl, Unitization.snd_inl]
    exact zero_mem _
  star_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, Unitization.snd_star]
    exact star_mem hx

theorem mem_openUnitization {x : Unitization ℂ (BoundaryCorona H)} :
    x ∈ openUnitization hT hcpt ↔ x.snd ∈ openHistoryIdeal hT hcpt := Iff.rfl

variable (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

include hinj hH in
theorem symbolOf_add {x y : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt)
    (hy : y ∈ openHistoryIdeal hT hcpt) :
    symbolOf hT hcpt (x + y) = symbolOf hT hcpt x + symbolOf hT hcpt y := by
  have h : x + y = cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
      (symbolOf hT hcpt x + symbolOf hT hcpt y) := by
    rw [map_add, cfcₙHom_symbolOf hT hcpt hinj hH hx, cfcₙHom_symbolOf hT hcpt hinj hH hy]
  rw [h, symbolOf_cfcₙHom]

include hinj hH in
theorem symbolOf_mul {x y : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt)
    (hy : y ∈ openHistoryIdeal hT hcpt) :
    symbolOf hT hcpt (x * y) = symbolOf hT hcpt x * symbolOf hT hcpt y := by
  have h : x * y = cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
      (symbolOf hT hcpt x * symbolOf hT hcpt y) := by
    rw [map_mul, cfcₙHom_symbolOf hT hcpt hinj hH hx, cfcₙHom_symbolOf hT hcpt hinj hH hy]
  rw [h, symbolOf_cfcₙHom]

include hinj hH in
theorem symbolOf_smul (c : ℂ) {x : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt) :
    symbolOf hT hcpt (c • x) = c • symbolOf hT hcpt x := by
  have h : c • x = cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
      (c • symbolOf hT hcpt x) := by
    rw [map_smul, cfcₙHom_symbolOf hT hcpt hinj hH hx]
  rw [h, symbolOf_cfcₙHom]

include hinj hH in
theorem symbolOf_star {x : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt) :
    symbolOf hT hcpt (star x) = star (symbolOf hT hcpt x) := by
  have h : star x = cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
      (star (symbolOf hT hcpt x)) := by
    rw [map_star, cfcₙHom_symbolOf hT hcpt hinj hH hx]
  rw [h, symbolOf_cfcₙHom]

theorem symbolOf_zero : symbolOf hT hcpt (0 : BoundaryCorona H) = 0 := by
  have h : (0 : BoundaryCorona H) = cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) 0 :=
    (map_zero _).symm
  rw [h, symbolOf_cfcₙHom]

/-- Evaluation of the symbol `λ + g(t)` of `J_T⁺` at an aperture parameter `t`. -/
def openEval (t : ℝ) : openUnitization hT hcpt →⋆ₐ[ℂ] ℂ where
  toFun x := openLoop hT hcpt hinj hH x.1 t
  map_one' := by
    simp [openLoop, symbolOf_zero]
  map_mul' x y := by
    have hx : (x : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := x.2
    have hy : (y : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := y.2
    change openLoop hT hcpt hinj hH ((x : Unitization ℂ (BoundaryCorona H)) * y) t =
      openLoop hT hcpt hinj hH x t * openLoop hT hcpt hinj hH y t
    simp only [openLoop, Unitization.fst_mul, Unitization.snd_mul]
    rw [symbolOf_add hT hcpt hinj hH (add_mem ((openHistoryIdeal hT hcpt).smul_mem _ hy)
      ((openHistoryIdeal hT hcpt).smul_mem _ hx)) (mul_mem hx hy),
      symbolOf_add hT hcpt hinj hH ((openHistoryIdeal hT hcpt).smul_mem _ hy)
        ((openHistoryIdeal hT hcpt).smul_mem _ hx),
      symbolOf_smul hT hcpt hinj hH _ hy, symbolOf_smul hT hcpt hinj hH _ hx,
      symbolOf_mul hT hcpt hinj hH hx hy]
    simp only [ContinuousMapZero.coe_add, ContinuousMapZero.coe_smul, ContinuousMapZero.coe_mul,
      Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  map_zero' := by
    simp [openLoop, symbolOf_zero]
  map_add' x y := by
    have hx : (x : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := x.2
    have hy : (y : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := y.2
    change openLoop hT hcpt hinj hH ((x : Unitization ℂ (BoundaryCorona H)) + y) t =
      openLoop hT hcpt hinj hH x t + openLoop hT hcpt hinj hH y t
    simp only [openLoop, Unitization.fst_add, Unitization.snd_add]
    rw [symbolOf_add hT hcpt hinj hH hx hy]
    simp only [ContinuousMapZero.coe_add, Pi.add_apply]
    ring
  commutes' c := by
    change openLoop hT hcpt hinj hH (algebraMap ℂ (Unitization ℂ (BoundaryCorona H)) c) t = c
    simp [openLoop, Unitization.algebraMap_eq_inl, symbolOf_zero]
  map_star' x := by
    have hx : (x : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := x.2
    change openLoop hT hcpt hinj hH (star (x : Unitization ℂ (BoundaryCorona H))) t =
      star (openLoop hT hcpt hinj hH x t)
    simp only [openLoop, Unitization.fst_star, Unitization.snd_star]
    rw [symbolOf_star hT hcpt hinj hH hx]
    simp

theorem openEval_apply (t : ℝ) (x : openUnitization hT hcpt) :
    openEval hT hcpt hinj hH t x = openLoop hT hcpt hinj hH x.1 t := rfl

theorem openEval_zero (x : openUnitization hT hcpt) :
    openEval hT hcpt hinj hH 0 x = (x : Unitization ℂ (BoundaryCorona H)).fst := by
  rw [openEval_apply]
  unfold openLoop
  have hp0 : clampPoint hT hcpt hinj hH 0 = 0 := Subtype.ext (clampPoint_zero hT hcpt hinj hH)
  have hz : symbolOf hT hcpt (x : Unitization ℂ (BoundaryCorona H)).snd 0 = 0 :=
    (symbolOf hT hcpt _).map_zero'
  rw [hp0, hz, add_zero]

/-- The symbol of `J_T⁺` closes: `λ + g(1) = λ + g(0)`. -/
theorem openEval_one (x : openUnitization hT hcpt) :
    openEval hT hcpt hinj hH 1 x = openEval hT hcpt hinj hH 0 x := by
  have hk := symbolOf_mem_endpointKernel hT hcpt hinj hH x.2
  have hp0 : clampPoint hT hcpt hinj hH 0 = 0 := Subtype.ext (clampPoint_zero hT hcpt hinj hH)
  have hp1 : clampPoint hT hcpt hinj hH 1 = ⟨1, one_mem_quasispectrum_unitGerm hT hcpt hinj hH⟩ :=
    Subtype.ext (clampPoint_one hT hcpt hinj hH)
  have hz : symbolOf hT hcpt (x : Unitization ℂ (BoundaryCorona H)).snd 0 = 0 :=
    (symbolOf hT hcpt _).map_zero'
  rw [openEval_apply, openEval_apply]
  unfold openLoop
  rw [hp0, hp1, hz,
    show symbolOf hT hcpt (x : Unitization ℂ (BoundaryCorona H)).snd
      ⟨1, one_mem_quasispectrum_unitGerm hT hcpt hinj hH⟩ = 0 from hk]

theorem clamp_clamp (t : ℝ) : max 0 (min 1 (max 0 (min 1 t))) = max (0 : ℝ) (min 1 t) := by
  rcases le_total t 0 with h | h
  · rw [min_eq_right (h.trans zero_le_one), max_eq_left h, min_eq_right zero_le_one, max_self]
  · rcases le_total t 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h, min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right zero_le_one, min_self, max_eq_right zero_le_one]

theorem openEval_clamp (t : ℝ) (x : openUnitization hT hcpt) :
    openEval hT hcpt hinj hH (max 0 (min 1 t)) x = openEval hT hcpt hinj hH t x := by
  have hc : clampPoint hT hcpt hinj hH (max 0 (min 1 t)) = clampPoint hT hcpt hinj hH t := by
    apply Subtype.ext
    rw [clampPoint_val, clampPoint_val, clamp_clamp]
  rw [openEval_apply, openEval_apply]
  unfold openLoop
  rw [hc]

theorem continuous_openEval (x : openUnitization hT hcpt) :
    Continuous fun t => openEval hT hcpt hinj hH t x :=
  continuous_openLoop hT hcpt hinj hH x.1

/-- Joint continuity of the symbol along a continuous family in `J_T⁺`. -/
theorem continuous_openEval_family {X : Type*} [TopologicalSpace X]
    {f : X → openUnitization hT hcpt} (hf : Continuous f) :
    Continuous fun p : X × ℝ => openEval hT hcpt hinj hH p.2 (f p.1) := by
  have hval : Continuous fun x => ((f x : Unitization ℂ (BoundaryCorona H))) :=
    continuous_subtype_val.comp hf
  have hsym : Continuous fun x => symbolOf hT hcpt (f x : Unitization ℂ (BoundaryCorona H)).snd :=
    continuous_symbolOf_comp hT hcpt hinj hH (Unitization.continuous_snd.comp hval)
      fun x => (f x).2
  refine (Unitization.continuous_fst.comp (hval.comp continuous_fst)).add ?_
  exact continuous_eval.comp ((hsym.comp continuous_fst).prodMk
    ((continuous_clampPoint hT hcpt hinj hH).comp continuous_snd))

/-- The element `N(0) + (N − N(0))(e)` of `J_T⁺` carried by a closed loop `N`. -/
def ofLoop {N : ℝ → ℂ} (hN : Continuous N) (hcl : N 1 = N 0) : openUnitization hT hcpt :=
  ⟨unitaryOfLoop hT hcpt hN, by
    change (unitaryOfLoop hT hcpt hN).snd ∈ openHistoryIdeal hT hcpt
    rw [unitaryOfLoop_snd, openHistoryIdeal_eq_map hT hcpt hinj hH]
    refine ⟨loopSymbol hT hcpt hN, ?_, rfl⟩
    change N ((1 : ℂ).re) - N 0 = 0
    rw [Complex.one_re, hcl, sub_self]⟩

theorem openEval_ofLoop {N : ℝ → ℂ} (hN : Continuous N) (hcl : N 1 = N 0) (t : ℝ) :
    openEval hT hcpt hinj hH t (ofLoop hT hcpt hinj hH hN hcl) = N (max 0 (min 1 t)) :=
  openLoop_unitaryOfLoop hT hcpt hinj hH hN t

theorem ofLoop_congr {N N' : ℝ → ℂ} (hN : Continuous N) (hN' : Continuous N')
    (hcl : N 1 = N 0) (hcl' : N' 1 = N' 0) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, N t = N' t) :
    ofLoop hT hcpt hinj hH hN hcl = ofLoop hT hcpt hinj hH hN' hcl' := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have h0 : N 0 = N' 0 := h 0 ⟨le_rfl, zero_le_one⟩
  have hsym : loopSymbol hT hcpt hN = loopSymbol hT hcpt hN' := by
    ext p
    have hp : (p : ℂ) ∈ unitIntervalC := hσ ▸ p.2
    obtain ⟨t, ht, hpt⟩ := hp
    change N (p : ℂ).re - N 0 = N' (p : ℂ).re - N' 0
    rw [← hpt, Complex.ofReal_re, h t ht, h0]
  apply Subtype.ext
  change unitaryOfLoop hT hcpt hN = unitaryOfLoop hT hcpt hN'
  unfold unitaryOfLoop
  rw [hsym, h0]

theorem ofLoop_openEval (x : openUnitization hT hcpt) :
    ofLoop hT hcpt hinj hH (continuous_openEval hT hcpt hinj hH x)
      (openEval_one hT hcpt hinj hH x) = x := by
  have hJ : (x : Unitization ℂ (BoundaryCorona H)).snd ∈ openHistoryIdeal hT hcpt := x.2
  have h0 := openEval_zero hT hcpt hinj hH x
  apply Subtype.ext
  change unitaryOfLoop hT hcpt (continuous_openLoop hT hcpt hinj hH x.1) = x.1
  ext
  · rw [unitaryOfLoop_fst]; exact h0
  · rw [unitaryOfLoop_snd]
    have hsym : loopSymbol hT hcpt (continuous_openLoop hT hcpt hinj hH x.1) =
        symbolOf hT hcpt (x : Unitization ℂ (BoundaryCorona H)).snd := by
      ext p
      change openLoop hT hcpt hinj hH x.1 (p : ℂ).re - openLoop hT hcpt hinj hH x.1 0 = _
      rw [show openLoop hT hcpt hinj hH x.1 0 = _ from h0]
      unfold openLoop
      rw [clampPoint_of_mem hT hcpt hinj hH p]
      ring
    rw [hsym, cfcₙHom_symbolOf hT hcpt hinj hH hJ]

/-- An element of `J_T⁺` is determined by its symbol on the aperture interval. -/
theorem openUnitization_ext {x y : openUnitization hT hcpt}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, openEval hT hcpt hinj hH t x = openEval hT hcpt hinj hH t y) :
    x = y := by
  rw [← ofLoop_openEval hT hcpt hinj hH x, ← ofLoop_openEval hT hcpt hinj hH y]
  exact ofLoop_congr hT hcpt hinj hH _ _ _ _ h

theorem continuous_ofLoop_family {N : ℝ → ℝ → ℂ}
    (hN : Continuous fun p : ℝ × ℝ => N p.1 p.2) (hcl : ∀ σ, N σ 1 = N σ 0) :
    Continuous fun σ => ofLoop hT hcpt hinj hH (N := N σ)
      (hN.comp (continuous_const.prodMk continuous_id)) (hcl σ) :=
  (continuous_unitaryOfLoop_family hT hcpt hN).subtype_mk _

/-! ## Matrix symbols and the determinant winding -/

/-- The symbol `t ↦ (λᵢⱼ + gᵢⱼ(t))` of a matrix over `J_T⁺`. -/
def matrixLoop {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  u.map (openEval hT hcpt hinj hH t)

theorem matrixLoop_apply {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) (t : ℝ)
    (i j : Fin n) : matrixLoop hT hcpt hinj hH u t i j = openEval hT hcpt hinj hH t (u i j) := rfl

theorem matrixLoop_mul {n : ℕ} (u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt))
    (t : ℝ) :
    matrixLoop hT hcpt hinj hH (u * v) t =
      matrixLoop hT hcpt hinj hH u t * matrixLoop hT hcpt hinj hH v t :=
  Matrix.map_mul

theorem matrixLoop_star {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) (t : ℝ) :
    matrixLoop hT hcpt hinj hH (star u) t = star (matrixLoop hT hcpt hinj hH u t) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  exact Matrix.conjTranspose_map _ fun x => (map_star (openEval hT hcpt hinj hH t) x)

theorem matrixLoop_one {n : ℕ} (t : ℝ) :
    matrixLoop hT hcpt hinj hH (1 : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) t = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem matrixLoop_mem_unitaryGroup {n : ℕ}
    {u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) (t : ℝ) :
    matrixLoop hT hcpt hinj hH u t ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [← matrixLoop_star, ← matrixLoop_mul, ← matrixLoop_mul, hu.1, hu.2, matrixLoop_one]
  exact ⟨rfl, rfl⟩

theorem matrixLoop_one_eq_zero {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :
    matrixLoop hT hcpt hinj hH u 1 = matrixLoop hT hcpt hinj hH u 0 := by
  ext i j
  exact openEval_one hT hcpt hinj hH (u i j)

theorem matrixLoop_clamp {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt))
    (t : ℝ) : matrixLoop hT hcpt hinj hH u (max 0 (min 1 t)) = matrixLoop hT hcpt hinj hH u t := by
  ext i j
  exact openEval_clamp hT hcpt hinj hH t (u i j)

theorem continuous_matrixLoop_family {X : Type*} [TopologicalSpace X] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) (openUnitization hT hcpt)} (hf : Continuous f) :
    Continuous fun p : X × ℝ => matrixLoop hT hcpt hinj hH (f p.1) p.2 :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_openEval_family hT hcpt hinj hH
      ((continuous_apply j).comp ((continuous_apply i).comp hf))

theorem continuous_matrixLoop {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :
    Continuous (matrixLoop hT hcpt hinj hH u) :=
  continuous_pi fun i => continuous_pi fun j => continuous_openEval hT hcpt hinj hH (u i j)

theorem matrixLoop_cornerEmbed {n m : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt))
    (t : ℝ) :
    matrixLoop hT hcpt hinj hH (cornerEmbed n m u) t =
      cornerEmbed n m (matrixLoop hT hcpt hinj hH u t) := by
  ext i j
  simp only [matrixLoop_apply, cornerEmbed_apply]
  split_ifs <;> simp

/-- **The stable winding index**: the winding number of the determinant of the symbol. -/
def stableWinding {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : ℤ :=
  windingNumber (fun t => (matrixLoop hT hcpt hinj hH u t).det) 0 1

theorem det_ne_zero_of_mem_unitaryGroup {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) : A.det ≠ 0 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp hA)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem det_matrixLoop_isLoop {n : ℕ} {u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) :
    IsLoop (fun t => (matrixLoop hT hcpt hinj hH u t).det) 0 1 :=
  ⟨(continuous_matrixLoop hT hcpt hinj hH u).matrix_det,
    fun t => det_ne_zero_of_mem_unitaryGroup (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu t),
    by simp only [matrixLoop_one_eq_zero]⟩

/-- Homotopy invariance of the stable winding index. -/
theorem stableWinding_eq_of_joinedIn {n : ℕ}
    {u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (h : JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) u v) :
    stableWinding hT hcpt hinj hH u = stableWinding hT hcpt hinj hH v := by
  obtain ⟨γ, hγ⟩ := h
  have hmem : ∀ σ : ℝ, γ.extend σ ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :=
    fun σ => hγ _
  have hu := hmem 0
  have hv := hmem 1
  rw [Path.extend_zero] at hu
  rw [Path.extend_one] at hv
  have hc := continuous_matrixLoop_family hT hcpt hinj hH γ.extend.continuous
  refine (windingNumber_eq_iff_joined (det_matrixLoop_isLoop hT hcpt hinj hH hu)
    (det_matrixLoop_isLoop hT hcpt hinj hH hv)).mpr
      ⟨fun σ t => (matrixLoop hT hcpt hinj hH (γ.extend σ) t).det, hc.matrix_det,
        fun σ t => (det_matrixLoop_isLoop hT hcpt hinj hH (hmem σ)).nonzero t,
        fun σ => (det_matrixLoop_isLoop hT hcpt hinj hH (hmem σ)).closed,
        fun t => by simp only [Path.extend_zero], fun t => by simp only [Path.extend_one]⟩

/-- Additivity of the stable winding index. -/
theorem stableWinding_mul {n : ℕ} {u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)))
    (hv : v ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) :
    stableWinding hT hcpt hinj hH (u * v) =
      stableWinding hT hcpt hinj hH u + stableWinding hT hcpt hinj hH v := by
  unfold stableWinding
  simp only [matrixLoop_mul, Matrix.det_mul]
  exact windingNumber_mul (det_matrixLoop_isLoop hT hcpt hinj hH hu)
    (det_matrixLoop_isLoop hT hcpt hinj hH hv)

/-- Stabilization invariance of the stable winding index. -/
theorem stableWinding_cornerEmbed {n m : ℕ} (h : n ≤ m)
    (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :
    stableWinding hT hcpt hinj hH (cornerEmbed n m u) = stableWinding hT hcpt hinj hH u := by
  unfold stableWinding
  simp only [matrixLoop_cornerEmbed, det_cornerEmbed h]

/-! ## Matrices from closed matrix loops -/

/-- The matrix over `J_T⁺` carried by a closed matrix loop `N`. -/
def matrixOfLoop {n : ℕ} {N : ℝ → Matrix (Fin n) (Fin n) ℂ} (hN : Continuous N)
    (hcl : N 1 = N 0) : Matrix (Fin n) (Fin n) (openUnitization hT hcpt) :=
  Matrix.of fun i j => ofLoop hT hcpt hinj hH (N := fun t => N t i j)
    ((continuous_apply j).comp ((continuous_apply i).comp hN)) (congrArg (fun A => A i j) hcl)

theorem matrixLoop_matrixOfLoop {n : ℕ} {N : ℝ → Matrix (Fin n) (Fin n) ℂ} (hN : Continuous N)
    (hcl : N 1 = N 0) (t : ℝ) :
    matrixLoop hT hcpt hinj hH (matrixOfLoop hT hcpt hinj hH hN hcl) t = N (max 0 (min 1 t)) := by
  ext i j
  exact openEval_ofLoop hT hcpt hinj hH ((continuous_apply j).comp ((continuous_apply i).comp hN))
    (congrArg (fun A => A i j) hcl) t

theorem matrixOfLoop_congr {n : ℕ} {N N' : ℝ → Matrix (Fin n) (Fin n) ℂ} (hN : Continuous N)
    (hN' : Continuous N') (hcl : N 1 = N 0) (hcl' : N' 1 = N' 0)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, N t = N' t) :
    matrixOfLoop hT hcpt hinj hH hN hcl = matrixOfLoop hT hcpt hinj hH hN' hcl' := by
  refine Matrix.ext fun i j => ?_
  exact ofLoop_congr hT hcpt hinj hH (N := fun t => N t i j) (N' := fun t => N' t i j)
    ((continuous_apply j).comp ((continuous_apply i).comp hN))
    ((continuous_apply j).comp ((continuous_apply i).comp hN')) (congrArg (fun A => A i j) hcl)
    (congrArg (fun A => A i j) hcl') fun t ht => by simp only [h t ht]

/-- A matrix over `J_T⁺` is determined by its symbol on the aperture interval. -/
theorem matrix_ext_of_matrixLoop {n : ℕ} {u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, matrixLoop hT hcpt hinj hH u t = matrixLoop hT hcpt hinj hH v t) :
    u = v := by
  refine Matrix.ext fun i j => ?_
  exact openUnitization_ext hT hcpt hinj hH fun t ht => congrFun (congrFun (h t ht) i) j

theorem matrixOfLoop_matrixLoop {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :
    matrixOfLoop hT hcpt hinj hH (continuous_matrixLoop hT hcpt hinj hH u)
      (matrixLoop_one_eq_zero hT hcpt hinj hH u) = u := by
  refine Matrix.ext fun i j => ?_
  exact ofLoop_openEval hT hcpt hinj hH (u i j)

/-- A closed loop of unitary matrices carries a unitary over `J_T⁺`. -/
theorem matrixOfLoop_mem_unitary {n : ℕ} {N : ℝ → Matrix (Fin n) (Fin n) ℂ} (hN : Continuous N)
    (hcl : N 1 = N 0) (hu : ∀ t, N t ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixOfLoop hT hcpt hinj hH hN hcl ∈
      unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) := by
  rw [Unitary.mem_iff]
  constructor
  · refine matrix_ext_of_matrixLoop hT hcpt hinj hH fun t _ => ?_
    rw [matrixLoop_mul, matrixLoop_star, matrixLoop_matrixOfLoop, matrixLoop_one]
    exact (Unitary.mem_iff.mp (hu _)).1
  · refine matrix_ext_of_matrixLoop hT hcpt hinj hH fun t _ => ?_
    rw [matrixLoop_mul, matrixLoop_star, matrixLoop_matrixOfLoop, matrixLoop_one]
    exact (Unitary.mem_iff.mp (hu _)).2

/-- **Lifting a free homotopy of unitary loops.**  A jointly continuous family of closed loops of
unitary matrices joins the corresponding unitaries over `J_T⁺`. -/
theorem joinedIn_matrixOfLoop {n : ℕ} {Hm : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hc : Continuous fun p : ℝ × ℝ => Hm p.1 p.2)
    (hu : ∀ σ t, Hm σ t ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcl : ∀ σ, Hm σ 1 = Hm σ 0) :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _)
      (matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id)) (hcl 0))
      (matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id)) (hcl 1)) := by
  have hfam : Continuous fun σ => matrixOfLoop hT hcpt hinj hH
      (hc.comp (continuous_const.prodMk continuous_id) : Continuous (Hm σ)) (hcl σ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_ofLoop_family hT hcpt hinj hH (N := fun σ t => Hm σ t i j)
      ((continuous_apply j).comp ((continuous_apply i).comp hc))
      fun σ => congrArg (fun A => A i j) (hcl σ)
  let γ : Path (matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id))
      (hcl 0)) (matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id))
      (hcl 1)) :=
    { toFun := fun s => matrixOfLoop hT hcpt hinj hH
        (hc.comp (continuous_const.prodMk continuous_id) : Continuous (Hm (s : ℝ))) (hcl s)
      continuous_toFun := hfam.comp continuous_subtype_val
      source' := rfl
      target' := rfl }
  exact ⟨γ, fun s => matrixOfLoop_mem_unitary hT hcpt hinj hH
    (hc.comp (continuous_const.prodMk continuous_id)) (hcl s) fun t => hu s t⟩

/-- A free homotopy of the symbols joins two unitaries over `J_T⁺`. -/
theorem joinedIn_of_loopHomotopy {n : ℕ} {u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    {Hm : ℝ → ℝ → Matrix (Fin n) (Fin n) ℂ} (hc : Continuous fun p : ℝ × ℝ => Hm p.1 p.2)
    (hu : ∀ σ t, Hm σ t ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcl : ∀ σ, Hm σ 1 = Hm σ 0)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Hm 0 t = matrixLoop hT hcpt hinj hH u t)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Hm 1 t = matrixLoop hT hcpt hinj hH v t) :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) u v := by
  have e0 : matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id))
      (hcl 0) = u :=
    (matrixOfLoop_congr hT hcpt hinj hH _ (continuous_matrixLoop hT hcpt hinj hH u) (hcl 0)
      (matrixLoop_one_eq_zero hT hcpt hinj hH u) h0).trans
      (matrixOfLoop_matrixLoop hT hcpt hinj hH u)
  have e1 : matrixOfLoop hT hcpt hinj hH (hc.comp (continuous_const.prodMk continuous_id))
      (hcl 1) = v :=
    (matrixOfLoop_congr hT hcpt hinj hH _ (continuous_matrixLoop hT hcpt hinj hH v) (hcl 1)
      (matrixLoop_one_eq_zero hT hcpt hinj hH v) h1).trans
      (matrixOfLoop_matrixLoop hT hcpt hinj hH v)
  have h := joinedIn_matrixOfLoop hT hcpt hinj hH hc hu hcl
  rwa [e0, e1] at h

theorem matrixLoop_zero_mem_unitaryGroup {n : ℕ}
    {u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) :
    star (matrixLoop hT hcpt hinj hH u 0) * matrixLoop hT hcpt hinj hH u 0 = 1 :=
  (Unitary.mem_iff.mp (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu 0)).1

/-- The based loop `t ↦ F(t) F(0)*` of a unitary over `J_T⁺`. -/
def basedLoop {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :
    Matrix (Fin n) (Fin n) (openUnitization hT hcpt) :=
  matrixOfLoop hT hcpt hinj hH (N := fun t => matrixLoop hT hcpt hinj hH u t *
      star (matrixLoop hT hcpt hinj hH u 0))
    ((continuous_matrixLoop hT hcpt hinj hH u).mul continuous_const)
    (by simp only [matrixLoop_one_eq_zero])

theorem matrixLoop_basedLoop {n : ℕ} (u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    matrixLoop hT hcpt hinj hH (basedLoop hT hcpt hinj hH u) t =
      matrixLoop hT hcpt hinj hH u t * star (matrixLoop hT hcpt hinj hH u 0) := by
  rw [basedLoop, matrixLoop_matrixOfLoop, min_eq_right ht.2, max_eq_right ht.1]

theorem basedLoop_mem_unitary {n : ℕ} {u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) :
    basedLoop hT hcpt hinj hH u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) :=
  matrixOfLoop_mem_unitary hT hcpt hinj hH _ _ fun t =>
    mul_mem (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu t)
      (Unitary.star_mem (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu 0))

/-- **Every free unitary loop is homotopic to a based one**: transport the base point along a path
in the connected group `U(n)`. -/
theorem joinedIn_basedLoop {n : ℕ} {u : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt))) :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) u
      (basedLoop hT hcpt hinj hH u) := by
  set F := matrixLoop hT hcpt hinj hH u
  have hF0 : F 0 ∈ Matrix.unitaryGroup (Fin n) ℂ := matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu 0
  let Λ : Path (⟨F 0, hF0⟩ : Matrix.unitaryGroup (Fin n) ℂ) 1 := PathConnectedSpace.somePath _ _
  refine joinedIn_of_loopHomotopy hT hcpt hinj hH
    (Hm := fun σ t => F t * star (F 0) * ((Λ.extend σ : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ)) ?_ ?_ ?_ ?_ ?_
  · exact (((continuous_matrixLoop hT hcpt hinj hH u).comp continuous_snd).mul continuous_const).mul
      (continuous_subtype_val.comp (Λ.extend.continuous.comp continuous_fst))
  · exact fun σ t => mul_mem (mul_mem (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu t)
      (Unitary.star_mem hF0)) (Λ.extend σ).2
  · intro σ
    simp only [F, matrixLoop_one_eq_zero]
  · intro t _
    rw [Path.extend_zero, Matrix.mul_assoc]
    change F t * (star (F 0) * F 0) = F t
    rw [matrixLoop_zero_mem_unitaryGroup hT hcpt hinj hH hu, Matrix.mul_one]
  · intro t ht
    rw [Path.extend_one, matrixLoop_basedLoop hT hcpt hinj hH u ht]
    exact Matrix.mul_one _

/-- **Based unitary loops with equal determinant are homotopic** (determinant classifies
`π₁(U(n+1))`). -/
theorem joinedIn_of_based_det_eq {n : ℕ}
    {u v : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)))
    (hv : v ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)))
    (hu0 : matrixLoop hT hcpt hinj hH u 0 = 1) (hv0 : matrixLoop hT hcpt hinj hH v 0 = 1)
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (matrixLoop hT hcpt hinj hH u t).det = (matrixLoop hT hcpt hinj hH v t).det) :
    JoinedIn (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) : Set _)
      u v := by
  let U := Matrix.unitaryGroup (Fin (n + 1)) ℂ
  let mkPath : ∀ w : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt),
      w ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) →
      matrixLoop hT hcpt hinj hH w 0 = 1 → Path (1 : U) 1 := fun w hw hw0 =>
    { toFun := fun s => ⟨matrixLoop hT hcpt hinj hH w s,
        matrixLoop_mem_unitaryGroup hT hcpt hinj hH hw s⟩
      continuous_toFun := ((continuous_matrixLoop hT hcpt hinj hH w).comp
        continuous_subtype_val).subtype_mk _
      source' := Subtype.ext hw0
      target' := Subtype.ext ((matrixLoop_one_eq_zero hT hcpt hinj hH w).trans hw0) }
  have hdetPath : ((mkPath u hu hu0).map (finiteUnitaryDeterminant (Fin (n + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm =
      ((mkPath v hv hv0).map (finiteUnitaryDeterminant (Fin (n + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm := by
    ext s
    exact hdet s s.2
  have hpq : (mkPath u hu hu0).Homotopic (mkPath v hv hv0) :=
    (finiteUnitary_loops_homotopic_iff_det n _ _).mpr (by rw [hdetPath])
  obtain ⟨Φ⟩ := hpq
  have hproj0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) :=
    Set.projIcc_left zero_le_one
  have hproj1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) :=
    Set.projIcc_right zero_le_one
  refine joinedIn_of_loopHomotopy hT hcpt hinj hH
    (Hm := fun σ t => ((Φ (Set.projIcc 0 1 zero_le_one σ, Set.projIcc 0 1 zero_le_one t) : U) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ?_ (fun σ t => (Φ _).2) ?_ ?_ ?_
  · exact continuous_subtype_val.comp (Φ.continuous.comp
      ((continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd)))
  · intro σ
    simp only [hproj0, hproj1, Path.Homotopy.source, Path.Homotopy.target]
  · intro t ht
    simp only [hproj0, ContinuousMap.HomotopyWith.apply_zero, Set.projIcc_of_mem _ ht]
    rfl
  · intro t ht
    simp only [hproj1, ContinuousMap.HomotopyWith.apply_one, Set.projIcc_of_mem _ ht]
    rfl

/-- **Free unitary loops with equal determinant loops are homotopic.** -/
theorem joinedIn_of_det_eq {n : ℕ}
    {u v : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)))
    (hv : v ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)))
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (matrixLoop hT hcpt hinj hH u t).det = (matrixLoop hT hcpt hinj hH v t).det) :
    JoinedIn (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) : Set _)
      u v := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hbase : ∀ w : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt),
      w ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) →
      matrixLoop hT hcpt hinj hH (basedLoop hT hcpt hinj hH w) 0 = 1 := fun w hw => by
    rw [matrixLoop_basedLoop hT hcpt hinj hH w h0mem]
    exact (Unitary.mem_iff.mp (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hw 0)).2
  have hdet' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (matrixLoop hT hcpt hinj hH (basedLoop hT hcpt hinj hH u) t).det =
        (matrixLoop hT hcpt hinj hH (basedLoop hT hcpt hinj hH v) t).det := fun t ht => by
    rw [matrixLoop_basedLoop hT hcpt hinj hH u ht, matrixLoop_basedLoop hT hcpt hinj hH v ht,
      Matrix.det_mul, Matrix.det_mul, Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      hdet t ht, hdet 0 h0mem]
  exact ((joinedIn_basedLoop hT hcpt hinj hH hu).trans
    (joinedIn_of_based_det_eq hT hcpt hinj hH (basedLoop_mem_unitary hT hcpt hinj hH hu)
      (basedLoop_mem_unitary hT hcpt hinj hH hv) (hbase u hu) (hbase v hv) hdet')).trans
    (joinedIn_basedLoop hT hcpt hinj hH hv).symm

/-- The `1 × 1` matrix of a scalar. -/
def scalarMat (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => z

theorem det_scalarMat (z : ℂ) : (scalarMat z).det = z := Matrix.det_unique _

theorem scalarMat_mem_unitaryGroup {z : ℂ} (hz : (starRingEnd ℂ) z * z = 1) :
    scalarMat z ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;>
    simp [scalarMat, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j] <;>
    linear_combination hz

/-- The determinant of a unitary matrix has modulus one. -/
theorem conj_det_mul_det_of_mem_unitaryGroup {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) : (starRingEnd ℂ) A.det * A.det = 1 := by
  have h := congrArg Matrix.det (Unitary.mem_iff.mp hA).1
  rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one]
    at h

/-- The determinant normal form `diag(det u, 1, …, 1)` of a unitary over `J_T⁺`. -/
def detNormalForm {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt) :=
  matrixOfLoop hT hcpt hinj hH
    (N := fun t => cornerEmbed 1 (n + 1) (scalarMat (matrixLoop hT hcpt hinj hH u t).det))
    ((continuous_cornerEmbed 1 (n + 1)).comp (continuous_pi fun _ => continuous_pi fun _ =>
      (continuous_matrixLoop hT hcpt hinj hH u).matrix_det))
    (by simp only [matrixLoop_one_eq_zero])

theorem detNormalForm_mem_unitary {n : ℕ}
    {u : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt))) :
    detNormalForm hT hcpt hinj hH u ∈
      unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) :=
  matrixOfLoop_mem_unitary hT hcpt hinj hH _ _ fun t =>
    cornerEmbed_mem_unitary (Nat.le_add_left 1 n) (scalarMat_mem_unitaryGroup
      (conj_det_mul_det_of_mem_unitaryGroup (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hu t)))

theorem matrixLoop_detNormalForm {n : ℕ}
    (u : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    matrixLoop hT hcpt hinj hH (detNormalForm hT hcpt hinj hH u) t =
      cornerEmbed 1 (n + 1) (scalarMat (matrixLoop hT hcpt hinj hH u t).det) := by
  rw [detNormalForm, matrixLoop_matrixOfLoop, min_eq_right ht.2, max_eq_right ht.1]

/-- **Classification**: unitaries over `J_T⁺` of equal size and equal stable winding index are
joined by a path of unitaries. -/
theorem joinedIn_of_stableWinding_eq {n : ℕ}
    {u v : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hu : u ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)))
    (hv : v ∈ unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)))
    (h : stableWinding hT hcpt hinj hH u = stableWinding hT hcpt hinj hH v) :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) u v := by
  cases n with
  | zero =>
    rw [Subsingleton.elim u v]
    exact JoinedIn.refl hv
  | succ n =>
    have hdetNF : ∀ w : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt),
        ∀ t ∈ Set.Icc (0 : ℝ) 1, (matrixLoop hT hcpt hinj hH w t).det =
          (matrixLoop hT hcpt hinj hH (detNormalForm hT hcpt hinj hH w) t).det :=
      fun w t ht => by
        rw [matrixLoop_detNormalForm hT hcpt hinj hH w ht, det_cornerEmbed (Nat.le_add_left 1 n),
          det_scalarMat]
    have hu' := joinedIn_of_det_eq hT hcpt hinj hH hu (detNormalForm_mem_unitary hT hcpt hinj hH hu)
      (hdetNF u)
    have hv' := joinedIn_of_det_eq hT hcpt hinj hH hv (detNormalForm_mem_unitary hT hcpt hinj hH hv)
      (hdetNF v)
    -- a normalized scalar homotopy between the two determinant loops
    obtain ⟨Hh, hc, hnv, hloop, hH0, hH1⟩ := (windingNumber_eq_iff_joined
      (det_matrixLoop_isLoop hT hcpt hinj hH hu) (det_matrixLoop_isLoop hT hcpt hinj hH hv)).mp h
    set Nn : ℝ → ℝ → ℂ := fun σ t => Hh σ t / ((‖Hh σ t‖ : ℝ) : ℂ)
    have hNc : Continuous fun p : ℝ × ℝ => Nn p.1 p.2 :=
      hc.div (Complex.continuous_ofReal.comp hc.norm) fun p => by
        exact_mod_cast (norm_pos_iff.mpr (hnv p.1 p.2)).ne'
    have hNunit : ∀ σ t, (starRingEnd ℂ) (Nn σ t) * Nn σ t = 1 := fun σ t => by
      have hne : ((‖Hh σ t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr (hnv σ t)).ne'
      simp only [Nn, map_div₀, Complex.conj_ofReal]
      rw [div_mul_div_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        ← sq, div_self (by exact_mod_cast pow_ne_zero 2 hne)]
    have hNend : ∀ (w : Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)),
        w ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (openUnitization hT hcpt)) →
        ∀ σ, (∀ t, Hh σ t = (matrixLoop hT hcpt hinj hH w t).det) →
        ∀ t, Nn σ t = (matrixLoop hT hcpt hinj hH w t).det := fun w hw σ hσ t => by
      have h1 : ‖(matrixLoop hT hcpt hinj hH w t).det‖ = 1 :=
        norm_eq_one_of_conj_mul_self (conj_det_mul_det_of_mem_unitaryGroup
          (matrixLoop_mem_unitaryGroup hT hcpt hinj hH hw t))
      simp only [Nn, hσ t, h1, Complex.ofReal_one, div_one]
    have hmid := joinedIn_of_loopHomotopy hT hcpt hinj hH
      (u := detNormalForm hT hcpt hinj hH u) (v := detNormalForm hT hcpt hinj hH v)
      (Hm := fun σ t => cornerEmbed 1 (n + 1) (scalarMat (Nn σ t)))
      ((continuous_cornerEmbed 1 (n + 1)).comp (continuous_pi fun _ => continuous_pi fun _ => hNc))
      (fun σ t => cornerEmbed_mem_unitary (Nat.le_add_left 1 n)
        (scalarMat_mem_unitaryGroup (hNunit σ t)))
      (fun σ => by simp only [Nn, hloop σ])
      (fun t ht => by
        rw [matrixLoop_detNormalForm hT hcpt hinj hH u ht, hNend u hu 0 hH0 t])
      (fun t ht => by
        rw [matrixLoop_detNormalForm hT hcpt hinj hH v ht, hNend v hv 1 hH1 t])
    exact (hu'.trans hmid).trans hv'.symm

end Aperture

/-! ## Stable `K₁(J_T)` -/

section StableK₁

open _root_.RHTower

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)

theorem joinedIn_cornerEmbed {n m : ℕ} (h : n ≤ m)
    {x y : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hJ : JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) x y) :
    JoinedIn (unitary (Matrix (Fin m) (Fin m) (openUnitization hT hcpt)) : Set _)
      (cornerEmbed n m x) (cornerEmbed n m y) := by
  obtain ⟨γ, hγ⟩ := hJ
  exact ⟨{ toFun := fun s => cornerEmbed n m (γ s)
           continuous_toFun := (continuous_cornerEmbed n m).comp γ.continuous
           source' := by simp
           target' := by simp }, fun s => cornerEmbed_mem_unitary h (hγ s)⟩

theorem joinedIn_mul_unitary {n : ℕ} {x x' y y' : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hx : JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) x x')
    (hy : JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) y y') :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _)
      (x * y) (x' * y') := by
  obtain ⟨γ, hγ⟩ := hx
  obtain ⟨δ, hδ⟩ := hy
  exact ⟨{ toFun := fun s => γ s * δ s
           continuous_toFun := γ.continuous.mul δ.continuous
           source' := by simp
           target' := by simp }, fun s => mul_mem (hγ s) (hδ s)⟩

theorem joinedIn_star_unitary {n : ℕ} {x y : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)}
    (hJ : JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _) x y) :
    JoinedIn (unitary (Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) : Set _)
      (star x) (star y) := by
  obtain ⟨γ, hγ⟩ := hJ
  exact ⟨{ toFun := fun s => star (γ s)
           continuous_toFun := γ.continuous.star
           source' := by simp
           target' := by simp }, fun s => Unitary.star_mem (hγ s)⟩

/-- A representative of `K₁(J_T)`: a unitary of `M_n(J_T⁺)` for some size `n`. -/
structure StableUnitaryRep : Type u where
  /-- The matrix size. -/
  size : ℕ
  /-- The matrix over `J_T⁺`. -/
  mat : Matrix (Fin size) (Fin size) (openUnitization hT hcpt)
  mem : mat ∈ unitary (Matrix (Fin size) (Fin size) (openUnitization hT hcpt))

/-- Stable homotopy: two unitaries are related when their stabilizations to a common size are
joined by a path of unitaries. -/
def StableUnitaryRep.Rel (a b : StableUnitaryRep hT hcpt) : Prop :=
  ∃ k, ∃ (_ : a.size ≤ k) (_ : b.size ≤ k),
    JoinedIn (unitary (Matrix (Fin k) (Fin k) (openUnitization hT hcpt)) : Set _)
      (cornerEmbed a.size k a.mat) (cornerEmbed b.size k b.mat)

theorem StableUnitaryRep.rel_of_embed_eq {a b : StableUnitaryRep hT hcpt} (k : ℕ)
    (ha : a.size ≤ k) (hb : b.size ≤ k)
    (h : cornerEmbed a.size k a.mat = cornerEmbed b.size k b.mat) :
    StableUnitaryRep.Rel hT hcpt a b :=
  ⟨k, ha, hb, h ▸ JoinedIn.refl (cornerEmbed_mem_unitary ha a.mem)⟩

theorem StableUnitaryRep.rel_equivalence : Equivalence (StableUnitaryRep.Rel hT hcpt) where
  refl a := ⟨a.size, le_rfl, le_rfl, JoinedIn.refl (cornerEmbed_mem_unitary le_rfl a.mem)⟩
  symm := fun ⟨k, ha, hb, h⟩ => ⟨k, hb, ha, h.symm⟩
  trans := by
    rintro a b c ⟨k, ha, hb, h⟩ ⟨l, hb', hc, h'⟩
    refine ⟨max k l, ha.trans (le_max_left k l), hc.trans (le_max_right k l), ?_⟩
    have h1 := joinedIn_cornerEmbed hT hcpt (le_max_left k l) h
    have h2 := joinedIn_cornerEmbed hT hcpt (le_max_right k l) h'
    rw [cornerEmbed_cornerEmbed ha, cornerEmbed_cornerEmbed hb] at h1
    rw [cornerEmbed_cornerEmbed hb', cornerEmbed_cornerEmbed hc] at h2
    exact h1.trans h2

instance StableUnitaryRep.setoid : Setoid (StableUnitaryRep hT hcpt) :=
  ⟨StableUnitaryRep.Rel hT hcpt, StableUnitaryRep.rel_equivalence hT hcpt⟩

/-- **`K₁(J_T)`**: stable homotopy classes of unitaries of the matrix algebras `M_n(J_T⁺)`. -/
abbrev StableK₁ : Type u := Quotient (StableUnitaryRep.setoid hT hcpt)

/-! ### The group structure: block-diagonal multiplication -/

/-- The product of representatives, after stabilization to the larger size. -/
def StableUnitaryRep.mul (a b : StableUnitaryRep hT hcpt) : StableUnitaryRep hT hcpt where
  size := max a.size b.size
  mat := cornerEmbed a.size _ a.mat * cornerEmbed b.size _ b.mat
  mem := mul_mem (cornerEmbed_mem_unitary (le_max_left _ _) a.mem)
    (cornerEmbed_mem_unitary (le_max_right _ _) b.mem)

theorem StableUnitaryRep.cornerEmbed_mul (a b : StableUnitaryRep hT hcpt) (k : ℕ)
    (hk : max a.size b.size ≤ k) :
    cornerEmbed (StableUnitaryRep.mul hT hcpt a b).size k (StableUnitaryRep.mul hT hcpt a b).mat =
      cornerEmbed a.size k a.mat * cornerEmbed b.size k b.mat := by
  change cornerEmbed (max a.size b.size) k (cornerEmbed a.size _ a.mat * cornerEmbed b.size _ b.mat) = _
  rw [_root_.GaloisForLFunctions.HTGeometry.cornerEmbed_mul hk,
    cornerEmbed_cornerEmbed (le_max_left _ _), cornerEmbed_cornerEmbed (le_max_right _ _)]

theorem StableUnitaryRep.mul_rel {a a' b b' : StableUnitaryRep hT hcpt}
    (ha : StableUnitaryRep.Rel hT hcpt a a') (hb : StableUnitaryRep.Rel hT hcpt b b') :
    StableUnitaryRep.Rel hT hcpt (StableUnitaryRep.mul hT hcpt a b)
      (StableUnitaryRep.mul hT hcpt a' b') := by
  obtain ⟨k, hak, hak', hJa⟩ := ha
  obtain ⟨l, hbl, hbl', hJb⟩ := hb
  set K := max (max k l) (max (max a.size b.size) (max a'.size b'.size))
  have hkK : k ≤ K := (le_max_left k l).trans (le_max_left _ _)
  have hlK : l ≤ K := (le_max_right k l).trans (le_max_left _ _)
  have h1K : max a.size b.size ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have h2K : max a'.size b'.size ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, h1K, h2K, ?_⟩
  rw [StableUnitaryRep.cornerEmbed_mul hT hcpt a b K h1K,
    StableUnitaryRep.cornerEmbed_mul hT hcpt a' b' K h2K]
  have hA := joinedIn_cornerEmbed hT hcpt hkK hJa
  have hB := joinedIn_cornerEmbed hT hcpt hlK hJb
  rw [cornerEmbed_cornerEmbed hak, cornerEmbed_cornerEmbed hak'] at hA
  rw [cornerEmbed_cornerEmbed hbl, cornerEmbed_cornerEmbed hbl'] at hB
  exact joinedIn_mul_unitary hT hcpt hA hB

/-- The inverse of a representative: its adjoint. -/
def StableUnitaryRep.inv (a : StableUnitaryRep hT hcpt) : StableUnitaryRep hT hcpt where
  size := a.size
  mat := star a.mat
  mem := Unitary.star_mem a.mem

theorem StableUnitaryRep.inv_rel {a a' : StableUnitaryRep hT hcpt}
    (ha : StableUnitaryRep.Rel hT hcpt a a') :
    StableUnitaryRep.Rel hT hcpt (StableUnitaryRep.inv hT hcpt a)
      (StableUnitaryRep.inv hT hcpt a') := by
  obtain ⟨k, hak, hak', hJ⟩ := ha
  refine ⟨k, hak, hak', ?_⟩
  change JoinedIn _ (cornerEmbed a.size k (star a.mat)) (cornerEmbed a'.size k (star a'.mat))
  rw [← star_cornerEmbed, ← star_cornerEmbed]
  exact joinedIn_star_unitary hT hcpt hJ

/-- The neutral representative: the empty unitary. -/
def StableUnitaryRep.one : StableUnitaryRep hT hcpt where
  size := 0
  mat := 1
  mem := one_mem _

instance : Mul (StableK₁ hT hcpt) :=
  ⟨Quotient.map₂ (StableUnitaryRep.mul hT hcpt) fun _ _ ha _ _ hb =>
    StableUnitaryRep.mul_rel hT hcpt ha hb⟩

instance : Inv (StableK₁ hT hcpt) :=
  ⟨Quotient.map (StableUnitaryRep.inv hT hcpt) fun _ _ ha => StableUnitaryRep.inv_rel hT hcpt ha⟩

instance : One (StableK₁ hT hcpt) := ⟨Quotient.mk _ (StableUnitaryRep.one hT hcpt)⟩

theorem StableK₁.mk_mul (a b : StableUnitaryRep hT hcpt) :
    (⟦a⟧ : StableK₁ hT hcpt) * (⟦b⟧ : StableK₁ hT hcpt) =
      (⟦StableUnitaryRep.mul hT hcpt a b⟧ : StableK₁ hT hcpt) := rfl

theorem StableK₁.mk_inv (a : StableUnitaryRep hT hcpt) :
    (⟦a⟧ : StableK₁ hT hcpt)⁻¹ = (⟦StableUnitaryRep.inv hT hcpt a⟧ : StableK₁ hT hcpt) := rfl

theorem StableK₁.one_def :
    (1 : StableK₁ hT hcpt) = (⟦StableUnitaryRep.one hT hcpt⟧ : StableK₁ hT hcpt) := rfl

/-- **`K₁(J_T)` is a group** under block-diagonal multiplication. -/
instance : Group (StableK₁ hT hcpt) :=
  Group.ofLeftAxioms
    (fun x y z => by
      induction x using Quotient.inductionOn with | h a => ?_
      induction y using Quotient.inductionOn with | h b => ?_
      induction z using Quotient.inductionOn with | h c => ?_
      simp only [StableK₁.mk_mul]
      apply Quotient.sound
      have hab : max a.size b.size ≤ max (max a.size b.size) c.size := le_max_left _ _
      have hbc : max b.size c.size ≤ max a.size (max b.size c.size) := le_max_right _ _
      have hK : max (max a.size b.size) c.size = max a.size (max b.size c.size) := max_assoc _ _ _
      refine StableUnitaryRep.rel_of_embed_eq hT hcpt (max (max a.size b.size) c.size) le_rfl
        hK.ge ?_
      set K := max (max a.size b.size) c.size
      rw [StableUnitaryRep.cornerEmbed_mul hT hcpt (StableUnitaryRep.mul hT hcpt a b) c K le_rfl,
        StableUnitaryRep.cornerEmbed_mul hT hcpt a (StableUnitaryRep.mul hT hcpt b c) K hK.ge,
        StableUnitaryRep.cornerEmbed_mul hT hcpt a b K hab,
        StableUnitaryRep.cornerEmbed_mul hT hcpt b c K (hbc.trans hK.ge), Matrix.mul_assoc])
    (fun x => by
      induction x using Quotient.inductionOn with | h a => ?_
      rw [StableK₁.one_def, StableK₁.mk_mul]
      apply Quotient.sound
      refine StableUnitaryRep.rel_of_embed_eq hT hcpt (max 0 a.size) le_rfl (le_max_right _ _) ?_
      rw [StableUnitaryRep.cornerEmbed_mul hT hcpt (StableUnitaryRep.one hT hcpt) a (max 0 a.size)
        le_rfl]
      change cornerEmbed 0 _ (1 : Matrix (Fin 0) (Fin 0) _) * _ = _
      rw [cornerEmbed_one, Matrix.one_mul])
    (fun x => by
      induction x using Quotient.inductionOn with | h a => ?_
      rw [StableK₁.one_def, StableK₁.mk_inv, StableK₁.mk_mul]
      apply Quotient.sound
      refine StableUnitaryRep.rel_of_embed_eq hT hcpt (max a.size a.size) le_rfl
        (Nat.zero_le _) ?_
      rw [StableUnitaryRep.cornerEmbed_mul hT hcpt (StableUnitaryRep.inv hT hcpt a) a
        (max a.size a.size) le_rfl]
      change cornerEmbed a.size _ (star a.mat) * cornerEmbed a.size _ a.mat =
        cornerEmbed 0 _ (1 : Matrix (Fin 0) (Fin 0) _)
      rw [← _root_.GaloisForLFunctions.HTGeometry.cornerEmbed_mul (le_max_left _ _),
        Unitary.star_mul_self_of_mem a.mem, cornerEmbed_one, cornerEmbed_one])

/-! ### The winding isomorphism `K₁(J_T) ≅ ℤ` -/

variable (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

theorem StableUnitaryRep.winding_eq_of_rel {a b : StableUnitaryRep hT hcpt}
    (h : StableUnitaryRep.Rel hT hcpt a b) :
    stableWinding hT hcpt hinj hH a.mat = stableWinding hT hcpt hinj hH b.mat := by
  obtain ⟨k, ha, hb, hJ⟩ := h
  rw [← stableWinding_cornerEmbed hT hcpt hinj hH ha, ← stableWinding_cornerEmbed hT hcpt hinj hH hb]
  exact stableWinding_eq_of_joinedIn hT hcpt hinj hH hJ

theorem StableUnitaryRep.rel_of_winding_eq {a b : StableUnitaryRep hT hcpt}
    (h : stableWinding hT hcpt hinj hH a.mat = stableWinding hT hcpt hinj hH b.mat) :
    StableUnitaryRep.Rel hT hcpt a b :=
  ⟨max a.size b.size, le_max_left _ _, le_max_right _ _,
    joinedIn_of_stableWinding_eq hT hcpt hinj hH (cornerEmbed_mem_unitary (le_max_left _ _) a.mem)
      (cornerEmbed_mem_unitary (le_max_right _ _) b.mem) (by
        rw [stableWinding_cornerEmbed hT hcpt hinj hH (le_max_left _ _),
          stableWinding_cornerEmbed hT hcpt hinj hH (le_max_right _ _), h])⟩

/-- Two unitaries define the same class of `K₁(J_T)` exactly when they have the same stable
winding index. -/
theorem StableUnitaryRep.rel_iff {a b : StableUnitaryRep hT hcpt} :
    StableUnitaryRep.Rel hT hcpt a b ↔
      stableWinding hT hcpt hinj hH a.mat = stableWinding hT hcpt hinj hH b.mat :=
  ⟨StableUnitaryRep.winding_eq_of_rel hT hcpt hinj hH,
    StableUnitaryRep.rel_of_winding_eq hT hcpt hinj hH⟩

/-- The winding index on `K₁(J_T)`. -/
def stableK₁Winding : StableK₁ hT hcpt → ℤ :=
  Quotient.lift (fun a => stableWinding hT hcpt hinj hH a.mat) fun _ _ h =>
    StableUnitaryRep.winding_eq_of_rel hT hcpt hinj hH h

theorem stableK₁Winding_mk (a : StableUnitaryRep hT hcpt) :
    stableK₁Winding hT hcpt hinj hH ⟦a⟧ = stableWinding hT hcpt hinj hH a.mat := rfl

theorem stableK₁Winding_injective : Function.Injective (stableK₁Winding hT hcpt hinj hH) := by
  intro x y h
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound (StableUnitaryRep.rel_of_winding_eq hT hcpt hinj hH h)

theorem stableWinding_one {n : ℕ} :
    stableWinding hT hcpt hinj hH (1 : Matrix (Fin n) (Fin n) (openUnitization hT hcpt)) = 0 := by
  unfold stableWinding
  simp only [matrixLoop_one, Matrix.det_one]
  exact windingNumber_const one_ne_zero 0 1

theorem stableK₁Winding_one : stableK₁Winding hT hcpt hinj hH 1 = 0 :=
  stableWinding_one hT hcpt hinj hH

theorem stableK₁Winding_mul (x y : StableK₁ hT hcpt) :
    stableK₁Winding hT hcpt hinj hH (x * y) =
      stableK₁Winding hT hcpt hinj hH x + stableK₁Winding hT hcpt hinj hH y := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  rw [StableK₁.mk_mul, stableK₁Winding_mk, stableK₁Winding_mk, stableK₁Winding_mk]
  have hmat : (StableUnitaryRep.mul hT hcpt a b).mat =
      cornerEmbed a.size (StableUnitaryRep.mul hT hcpt a b).size a.mat *
        cornerEmbed b.size (StableUnitaryRep.mul hT hcpt a b).size b.mat := rfl
  have hm : (StableUnitaryRep.mul hT hcpt a b).size = max a.size b.size := rfl
  rw [hmat, stableWinding_mul hT hcpt hinj hH
      (cornerEmbed_mem_unitary (m := (StableUnitaryRep.mul hT hcpt a b).size)
        (hm ▸ le_max_left _ _) a.mem)
      (cornerEmbed_mem_unitary (m := (StableUnitaryRep.mul hT hcpt a b).size)
        (hm ▸ le_max_right _ _) b.mem),
    stableWinding_cornerEmbed hT hcpt hinj hH (m := (StableUnitaryRep.mul hT hcpt a b).size)
      (hm ▸ le_max_left _ _),
    stableWinding_cornerEmbed hT hcpt hinj hH (m := (StableUnitaryRep.mul hT hcpt a b).size)
      (hm ▸ le_max_right _ _)]

/-- The winding index as a group homomorphism `K₁(J_T) → ℤ`. -/
def stableK₁WindingHom : StableK₁ hT hcpt →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (stableK₁Winding hT hcpt hinj hH x)
  map_one' := by rw [stableK₁Winding_one]; rfl
  map_mul' x y := by rw [stableK₁Winding_mul]; rfl

include hinj hH in
/-- `K₁(J_T)` is abelian. -/
theorem stableK₁_mul_comm (x y : StableK₁ hT hcpt) : x * y = y * x :=
  stableK₁Winding_injective hT hcpt hinj hH (by
    rw [stableK₁Winding_mul, stableK₁Winding_mul, add_comm])

/-! ### `1 × 1` unitaries and the exponential connecting map -/

theorem oneByOne_mem_unitary {y : openUnitization hT hcpt}
    (hy : (y : Unitization ℂ (BoundaryCorona H)) ∈ unitary (Unitization ℂ (BoundaryCorona H))) :
    (Matrix.of fun _ _ => y : Matrix (Fin 1) (Fin 1) (openUnitization hT hcpt)) ∈
      unitary (Matrix (Fin 1) (Fin 1) (openUnitization hT hcpt)) := by
  have h1 : star y * y = 1 := Subtype.ext (Unitary.star_mul_self_of_mem hy)
  have h2 : y * star y = 1 := Subtype.ext (Unitary.mul_star_self_of_mem hy)
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j, h1, h2]

/-- The `1 × 1` representative of a unitary of `J̃_T`. -/
def oneByOneRep {x : Unitization ℂ (BoundaryCorona H)} (hx : x ∈ openHistoryUnitaries hT hcpt) :
    StableUnitaryRep hT hcpt where
  size := 1
  mat := Matrix.of fun _ _ => ⟨x, hx.2⟩
  mem := oneByOne_mem_unitary hT hcpt hx.1

theorem stableWinding_oneByOneRep {x : Unitization ℂ (BoundaryCorona H)}
    (hx : x ∈ openHistoryUnitaries hT hcpt) :
    stableWinding hT hcpt hinj hH (oneByOneRep hT hcpt hx).mat = openWinding hT hcpt hinj hH x := by
  unfold stableWinding openWinding
  congr 1
  funext t
  exact Matrix.det_unique (n := Fin 1)
    (matrixLoop hT hcpt hinj hH (oneByOneRep hT hcpt hx).mat t)

/-- The comparison map from the `1 × 1` model `π₀ U(J̃_T)` of the existing cone module. -/
def openK₁ToStable : OpenK₁ hT hcpt → StableK₁ hT hcpt :=
  Quotient.lift (fun x => (⟦oneByOneRep hT hcpt x.2⟧ : StableK₁ hT hcpt)) fun x y h =>
    Quotient.sound (StableUnitaryRep.rel_of_winding_eq hT hcpt hinj hH (by
      rw [stableWinding_oneByOneRep, stableWinding_oneByOneRep]
      exact openWinding_eq_of_joinedIn hT hcpt hinj hH ((joinedIn_iff_joined x.2 y.2).mpr h)))

theorem stableK₁Winding_openK₁ToStable (x : OpenK₁ hT hcpt) :
    stableK₁Winding hT hcpt hinj hH (openK₁ToStable hT hcpt hinj hH x) =
      openK₁Winding hT hcpt hinj hH x := by
  induction x using Quotient.inductionOn with | h x => ?_
  exact stableWinding_oneByOneRep hT hcpt hinj hH x.2

/-- **The connecting map** `δ : K₀(ℂ) = ℤ → K₁(J_T)`, `δ(n) = [exp(2πi n e_1)]`, the exponential of
the positive lift `e_1` of the endpoint unit. -/
def stableConnectingMap (n : ℤ) : StableK₁ hT hcpt :=
  ⟦oneByOneRep hT hcpt (boundaryExp_intSMul_mem hT hcpt hinj hH n)⟧

theorem stableK₁Winding_connectingMap (n : ℤ) :
    stableK₁Winding hT hcpt hinj hH (stableConnectingMap hT hcpt hinj hH n) = n := by
  rw [stableConnectingMap, stableK₁Winding_mk, stableWinding_oneByOneRep]
  exact openK₁Winding_connectingMap hT hcpt hinj hH n

theorem stableK₁Winding_bijective : Function.Bijective (stableK₁Winding hT hcpt hinj hH) :=
  ⟨stableK₁Winding_injective hT hcpt hinj hH, fun n =>
    ⟨stableConnectingMap hT hcpt hinj hH n, stableK₁Winding_connectingMap hT hcpt hinj hH n⟩⟩

/-- **(SAC.8) `K₁(J_T) ≅ ℤ`** as groups, by the stable winding index. -/
def stableK₁MulEquiv : StableK₁ hT hcpt ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective (stableK₁WindingHom hT hcpt hinj hH)
    (stableK₁Winding_bijective hT hcpt hinj hH)

theorem stableConnectingMap_add (m n : ℤ) :
    stableConnectingMap hT hcpt hinj hH (m + n) =
      stableConnectingMap hT hcpt hinj hH m * stableConnectingMap hT hcpt hinj hH n :=
  stableK₁Winding_injective hT hcpt hinj hH (by
    rw [stableK₁Winding_mul, stableK₁Winding_connectingMap, stableK₁Winding_connectingMap,
      stableK₁Winding_connectingMap])

/-- **(SAC.8), (SAC.9) The connecting map is an isomorphism** `ℤ ≅ K₁(J_T)` onto the stable
`K₁`, it is additive, and `δ(1)` winds once. -/
theorem stableConnectingMap_bijective :
    Function.Bijective (stableConnectingMap hT hcpt hinj hH) ∧
      stableK₁Winding hT hcpt hinj hH (stableConnectingMap hT hcpt hinj hH 1) = 1 := by
  have hleft : Function.LeftInverse (stableK₁Winding hT hcpt hinj hH)
      (stableConnectingMap hT hcpt hinj hH) := stableK₁Winding_connectingMap hT hcpt hinj hH
  refine ⟨⟨hleft.injective, fun x => ⟨stableK₁Winding hT hcpt hinj hH x,
    stableK₁Winding_injective hT hcpt hinj hH ?_⟩⟩, stableK₁Winding_connectingMap hT hcpt hinj hH 1⟩
  rw [stableK₁Winding_connectingMap]

/-- The `1 × 1` model of the cone module already computes the stable `K₁`. -/
theorem openK₁ToStable_bijective : Function.Bijective (openK₁ToStable hT hcpt hinj hH) := by
  refine ⟨fun x y h => openK₁Winding_injective hT hcpt hinj hH ?_, fun z => ?_⟩
  · rw [← stableK₁Winding_openK₁ToStable, ← stableK₁Winding_openK₁ToStable, h]
  · obtain ⟨x, hx⟩ := (connectingMap_bijective hT hcpt hinj hH).2.1.2
      (stableK₁Winding hT hcpt hinj hH z)
    exact ⟨x, stableK₁Winding_injective hT hcpt hinj hH (by
      rw [stableK₁Winding_openK₁ToStable, hx])⟩

/-- **(SAC.10) Polarization invariance in `K₁(J_T)`**: every scale lift `e_c` of the endpoint unit
has the same boundary class `δ(1)`. -/
theorem stable_boundaryExp_scaleGerm {c : ℝ} (hc : 0 < c) :
    (⟦oneByOneRep hT hcpt (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH hc).1⟧ :
      StableK₁ hT hcpt) = stableConnectingMap hT hcpt hinj hH 1 :=
  stableK₁Winding_injective hT hcpt hinj hH (by
    rw [stableK₁Winding_mk, stableWinding_oneByOneRep, stableK₁Winding_connectingMap]
    exact (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH hc).2)

theorem openWinding_one : openWinding hT hcpt hinj hH (1 : Unitization ℂ (BoundaryCorona H)) = 0 := by
  unfold openWinding
  have h : openLoop hT hcpt hinj hH (1 : Unitization ℂ (BoundaryCorona H)) = fun _ => 1 := by
    funext t
    simp [openLoop, symbolOf_zero]
  rw [h]
  exact windingNumber_const one_ne_zero 0 1

/-- **(SAC.12) The relative exponential is trivial in `K₁(J_T)`**: `[exp(2πi(e_c − e_d))] = 1`. -/
theorem stable_boundaryExp_sub {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (⟦oneByOneRep hT hcpt (boundaryExp_sub_mem hT hcpt hinj hH hc hd)⟧ : StableK₁ hT hcpt) = 1 :=
  stableK₁Winding_injective hT hcpt hinj hH (by
    rw [stableK₁Winding_mk, stableWinding_oneByOneRep, stableK₁Winding_one,
      openWinding_eq_of_joinedIn hT hcpt hinj hH (joinedIn_boundaryExp_sub hT hcpt hinj hH hc hd),
      openWinding_one])

/-! ### Projections: the exponential map on `K₀(ℂ)` -/

/-- The boundary unitary `exp(2πi e_1) ∈ J̃_T` of the endpoint unit, as an element of `J_T⁺`. -/
def unitBoundary : openUnitization hT hcpt :=
  ⟨boundaryExp (unitGerm hT hcpt), (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH one_pos).1.2⟩

/-- **The exponential boundary of a projection** `P ∈ M_k(ℂ)`:
`(1 − P) ⊗ 1 + P ⊗ exp(2πi e_1)`, the exponential `exp(2πi P ⊗ e_1)` of the self-adjoint lift
`P ⊗ e_1` of `P` along the endpoint quotient. -/
def projectionBoundary {k : ℕ} (P : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) (openUnitization hT hcpt) :=
  Matrix.of fun i j => algebraMap ℂ (openUnitization hT hcpt) ((1 - P) i j) +
    P i j • unitBoundary hT hcpt hinj hH

theorem matrixLoop_projectionBoundary {k : ℕ} (P : Matrix (Fin k) (Fin k) ℂ) (t : ℝ) :
    matrixLoop hT hcpt hinj hH (projectionBoundary hT hcpt hinj hH P) t =
      (1 - P) + openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) • P := by
  ext i j
  simp only [matrixLoop_apply, projectionBoundary, Matrix.of_apply, map_add, map_smul,
    AlgHomClass.commutes, Algebra.algebraMap_self, RingHom.id_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem conj_openEval_unitBoundary_mul (t : ℝ) :
    (starRingEnd ℂ) (openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH)) *
      openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) = 1 :=
  openLoop_conj_mul_self hT hcpt hinj hH
    (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH one_pos).1 t

theorem projectionBoundary_mem_unitary {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) :
    projectionBoundary hT hcpt hinj hH P ∈
      unitary (Matrix (Fin k) (Fin k) (openUnitization hT hcpt)) := by
  have key : ∀ t : ℝ, star ((1 - P) + openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) • P)
      * ((1 - P) + openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) • P) = 1 ∧
      ((1 - P) + openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) • P) *
        star ((1 - P) + openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) • P) = 1 := by
    intro t
    set z := openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH)
    have hz : (starRingEnd ℂ) z * z = 1 := conj_openEval_unitBoundary_mul hT hcpt hinj hH t
    have hz' : z * (starRingEnd ℂ) z = 1 := by rw [mul_comm]; exact hz
    have hs : star ((1 - P) + z • P) = (1 - P) + (starRingEnd ℂ) z • P := by
      rw [star_add, star_sub, star_one, star_smul, Matrix.star_eq_conjTranspose P, hPh.eq]
      rfl
    rw [hs]
    constructor
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hPP]
      linear_combination (norm := module) hz • P
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hPP]
      linear_combination (norm := module) hz' • P
  rw [Unitary.mem_iff]
  constructor
  · refine matrix_ext_of_matrixLoop hT hcpt hinj hH fun t _ => ?_
    rw [matrixLoop_mul, matrixLoop_star, matrixLoop_projectionBoundary, matrixLoop_one]
    exact (key t).1
  · refine matrix_ext_of_matrixLoop hT hcpt hinj hH fun t _ => ?_
    rw [matrixLoop_mul, matrixLoop_star, matrixLoop_projectionBoundary, matrixLoop_one]
    exact (key t).2

/-- The representative of the exponential boundary of a projection. -/
def projectionBoundaryRep {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ} (hPh : P.IsHermitian)
    (hPP : P * P = P) : StableUnitaryRep hT hcpt where
  size := k
  mat := projectionBoundary hT hcpt hinj hH P
  mem := projectionBoundary_mem_unitary hT hcpt hinj hH hPh hPP

theorem stableWinding_projectionBoundary {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ}
    (hPh : P.IsHermitian) (hPP : P * P = P) :
    stableWinding hT hcpt hinj hH (projectionBoundary hT hcpt hinj hH P) = P.rank := by
  unfold stableWinding
  simp only [matrixLoop_projectionBoundary, det_one_sub_add_smul_of_projection hPh hPP]
  have hL := openLoop_isLoop hT hcpt hinj hH
    (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH one_pos).1
  rw [show (fun t => openEval hT hcpt hinj hH t (unitBoundary hT hcpt hinj hH) ^ P.rank) =
      fun t => openLoop hT hcpt hinj hH (boundaryExp (unitGerm hT hcpt)) t ^ P.rank from rfl,
    windingNumber_pow hL]
  have h1 := (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH one_pos).2
  unfold openWinding at h1
  rw [h1, mul_one]

/-- **The exponential map on projections**: the boundary of the class of a projection `P` of
`M_k(ℂ)` is `δ(rank P)`.  In particular `δ` is the connecting map `K₀(ℂ) → K₁(J_T)` of the
endpoint sequence, with `K₀(ℂ) = ℤ` by rank. -/
theorem projectionBoundary_class {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ} (hPh : P.IsHermitian)
    (hPP : P * P = P) :
    (⟦projectionBoundaryRep hT hcpt hinj hH hPh hPP⟧ : StableK₁ hT hcpt) =
      stableConnectingMap hT hcpt hinj hH P.rank :=
  stableK₁Winding_injective hT hcpt hinj hH (by
    rw [stableK₁Winding_mk, stableK₁Winding_connectingMap]
    exact stableWinding_projectionBoundary hT hcpt hinj hH hPh hPP)

end StableK₁


end GaloisForLFunctions.HTGeometry
