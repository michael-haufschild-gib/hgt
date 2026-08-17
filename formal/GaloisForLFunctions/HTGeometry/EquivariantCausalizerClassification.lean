import Mathlib
import GaloisForLFunctions.HTGeometry.ConjugationEquivariantClassification

/-!
# Unitarily equivariant sesquilinear causalizers

Let `Φ` be a sesquilinear map from pairs of `r × n` complex matrices to `n × n` matrices which is
invariant under simultaneous left multiplication by `U(r)` and covariant under simultaneous right
multiplication by `U(n)`.  Left invariance contracts the row index: diagonal phase unitaries kill
pairings of different rows and permutation unitaries make the same-row pairing row-independent, so
`Φ X Y = L (Xᴴ Y)` for a single linear map `L` on `n × n` matrices.  Right covariance makes `L`
conjugation equivariant, so for `n ≥ 2` the classification of such maps applies and

`Φ X Y = a (Xᴴ Y) + b tr(Xᴴ Y) I`

with uniquely determined `a, b`.
-/

namespace GaloisForLFunctions.EquivariantCausalizer

open Matrix

variable {r n : ℕ}

theorem diagonal_mul_single_rect (w : Fin r → ℂ) (a : Fin r) (i : Fin n) (c : ℂ) :
    diagonal w * Matrix.single a i c = Matrix.single a i (w a * c) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · by_cases hk : a = k
    · subst hk
      simp
    · simp [hk]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hb
    exact absurd (Finset.mem_univ k) hb

theorem permMatrix_mul_single (σ : Equiv.Perm (Fin r)) (a : Fin r) (i : Fin n) (c : ℂ) :
    (Equiv.Perm.permMatrix ℂ σ) * Matrix.single a i c = Matrix.single (σ.symm a) i c := by
  ext k l
  simp only [Matrix.mul_apply, permMatrix_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single (σ k)]
  · by_cases hk : σ.symm a = k
    · subst hk
      simp
    · have : ¬ (a = σ k) := by
        intro hc
        exact hk (by rw [hc, Equiv.symm_apply_apply])
      simp [this, hk]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hb
    exact absurd (Finset.mem_univ (σ k)) hb

theorem mem_unitaryGroup_diagonal_rect (w : Fin r → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    diagonal w ∈ Matrix.unitaryGroup (Fin r) ℂ :=
  mem_unitaryGroup_diagonal w hw


section Sesquilinear

variable (Φ : Matrix (Fin r) (Fin n) ℂ →ₗ⋆[ℂ]
    (Matrix (Fin r) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
  (hleft : ∀ U ∈ Matrix.unitaryGroup (Fin r) ℂ, ∀ X Y, Φ (U * X) (U * Y) = Φ X Y)

include hleft in
/-- Left unitary invariance kills pairings of different rows. -/
theorem phi_diff_row_eq_zero {a b : Fin r} (hab : a ≠ b) (i j : Fin n) :
    Φ (Matrix.single a i 1) (Matrix.single b j 1) = 0 := by
  classical
  have hw : ∀ x : Fin r, ‖(if x = a then Complex.I else 1 : ℂ)‖ = 1 := by
    intro x
    by_cases h : x = a <;> simp [h]
  have hU := hleft (diagonal (fun x => if x = a then Complex.I else 1))
    (mem_unitaryGroup_diagonal _ hw) (Matrix.single a i 1) (Matrix.single b j 1)
  rw [diagonal_mul_single_rect, diagonal_mul_single_rect, if_pos rfl,
    if_neg (Ne.symm hab)] at hU
  rw [mul_one, mul_one] at hU
  rw [show Matrix.single a i Complex.I = Complex.I • Matrix.single a i (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]] at hU
  rw [map_smulₛₗ, LinearMap.smul_apply] at hU
  simp only [Complex.conj_I] at hU
  have hne : (-Complex.I : ℂ) ≠ 1 := by
    intro hc
    have := congrArg Complex.im hc
    simp at this
  have hz : (-Complex.I - 1) • (Φ (Matrix.single a i 1) (Matrix.single b j 1)) = 0 := by
    rw [sub_smul, hU, one_smul, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

include hleft in
/-- Left unitary invariance makes the same-row pairing independent of the row. -/
theorem phi_row_indep (a b : Fin r) (i j : Fin n) :
    Φ (Matrix.single a i 1) (Matrix.single a j 1)
      = Φ (Matrix.single b i 1) (Matrix.single b j 1) := by
  classical
  have hU := hleft (Equiv.Perm.permMatrix ℂ (Equiv.swap a b))
    (mem_unitaryGroup_permMatrix _) (Matrix.single a i 1) (Matrix.single a j 1)
  rw [permMatrix_mul_single, permMatrix_mul_single] at hU
  have hsym : (Equiv.swap a b).symm a = b := by simp
  rw [hsym] at hU
  exact hU.symm

end Sesquilinear


section Induced

variable (Φ : Matrix (Fin r) (Fin n) ℂ →ₗ⋆[ℂ]
    (Matrix (Fin r) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))

/-- The linear map on square matrices induced by a left-invariant sesquilinear pairing. -/
noncomputable def inducedMap (hr : 0 < r) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun A := ∑ i, ∑ j, A i j •
    Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1)
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => (Finset.smul_sum).symm)

theorem inducedMap_apply (hr : 0 < r) (A : Matrix (Fin n) (Fin n) ℂ) :
    inducedMap Φ hr A
      = ∑ i, ∑ j, A i j • Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1) := rfl

variable (hleft : ∀ U ∈ Matrix.unitaryGroup (Fin r) ℂ, ∀ X Y, Φ (U * X) (U * Y) = Φ X Y)

include hleft in
theorem phi_single_pair (hr : 0 < r) (X Y : Matrix (Fin r) (Fin n) ℂ)
    (a b : Fin r) (i j : Fin n) :
    Φ (Matrix.single a i (X a i)) (Matrix.single b j (Y b j))
      = if a = b then ((starRingEnd ℂ) (X a i) * Y b j) •
          Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1) else 0 := by
  have hX : Matrix.single a i (X a i) = (X a i) • Matrix.single a i (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hY : Matrix.single b j (Y b j) = (Y b j) • Matrix.single b j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hX, hY, map_smulₛₗ Φ, LinearMap.smul_apply, map_smul, smul_smul]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, phi_row_indep Φ hleft a ⟨0, hr⟩ i j]
  · rw [if_neg hab, phi_diff_row_eq_zero Φ hleft hab, smul_zero]

end Induced


theorem sum_comm₃' {M : Type*} [AddCommMonoid M] {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ b, ∑ a, F a b c := by
  calc (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

section Reduction

variable (Φ : Matrix (Fin r) (Fin n) ℂ →ₗ⋆[ℂ]
    (Matrix (Fin r) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
  (hleft : ∀ U ∈ Matrix.unitaryGroup (Fin r) ℂ, ∀ X Y, Φ (U * X) (U * Y) = Φ X Y)

include hleft in
/-- **Left unitary invariance contracts the row index.**  A left-invariant sesquilinear pairing is
a linear function of the Gram matrix `Xᴴ Y`. -/
theorem phi_eq_inducedMap (hr : 0 < r) (X Y : Matrix (Fin r) (Fin n) ℂ) :
    Φ X Y = inducedMap Φ hr (Xᴴ * Y) := by
  classical
  have key : ∀ (b : Fin r) (j : Fin n),
      (∑ a, ∑ i, Φ (Matrix.single a i (X a i)) (Matrix.single b j (Y b j)))
        = ∑ i, ((starRingEnd ℂ) (X b i) * Y b j) •
            Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1) := by
    intro b j
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ =>
      phi_single_pair Φ hleft hr X Y a b i j))]
    have hin : ∀ a : Fin r,
        (∑ i, if a = b then ((starRingEnd ℂ) (X a i) * Y b j) •
          Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1) else 0)
        = if a = b then (∑ i, ((starRingEnd ℂ) (X a i) * Y b j) •
          Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1)) else 0 := by
      intro a
      by_cases h : a = b <;> simp [h]
    rw [Finset.sum_congr rfl (fun a _ => hin a),
      Finset.sum_ite_eq' Finset.univ b (fun a => ∑ i, ((starRingEnd ℂ) (X a i) * Y b j) •
        Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1)),
      if_pos (Finset.mem_univ b)]
  conv_lhs => rw [matrix_eq_sum_single X, matrix_eq_sum_single Y]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => key b j))]
  have hrhs : inducedMap Φ hr (Xᴴ * Y)
      = ∑ i, ∑ j, ∑ b, ((starRingEnd ℂ) (X b i) * Y b j) •
          Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1) := by
    rw [inducedMap_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show (Xᴴ * Y) i j = ∑ b, (starRingEnd ℂ) (X b i) * Y b j by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply], Finset.sum_smul]
  rw [hrhs]
  exact sum_comm₃' (fun b j i => ((starRingEnd ℂ) (X b i) * Y b j) •
    Φ (Matrix.single ⟨0, hr⟩ i 1) (Matrix.single ⟨0, hr⟩ j 1))

end Reduction


section Equivariance

variable (Φ : Matrix (Fin r) (Fin n) ℂ →ₗ⋆[ℂ]
    (Matrix (Fin r) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
  (hleft : ∀ U ∈ Matrix.unitaryGroup (Fin r) ℂ, ∀ X Y, Φ (U * X) (U * Y) = Φ X Y)
  (hright : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X Y, Φ (X * V) (Y * V) = Vᴴ * Φ X Y * V)

theorem single_eq_gram (hr : 0 < r) (i j : Fin n) :
    Matrix.single i j (1 : ℂ)
      = (Matrix.single (⟨0, hr⟩ : Fin r) i (1 : ℂ))ᴴ *
        Matrix.single (⟨0, hr⟩ : Fin r) j (1 : ℂ) := by
  rw [Matrix.conjTranspose_single]
  rw [show (star (1 : ℂ)) = (1 : ℂ) by simp]
  rw [Matrix.single_mul_single_same]
  simp

include hleft hright in
theorem inducedMap_conj_gram (hr : 0 < r) {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (X Y : Matrix (Fin r) (Fin n) ℂ) :
    inducedMap Φ hr (Vᴴ * (Xᴴ * Y) * V) = Vᴴ * inducedMap Φ hr (Xᴴ * Y) * V := by
  have hXV : (X * V)ᴴ * (Y * V) = Vᴴ * (Xᴴ * Y) * V := by
    rw [Matrix.conjTranspose_mul]
    simp [Matrix.mul_assoc]
  calc inducedMap Φ hr (Vᴴ * (Xᴴ * Y) * V)
      = inducedMap Φ hr ((X * V)ᴴ * (Y * V)) := by rw [hXV]
    _ = Φ (X * V) (Y * V) := (phi_eq_inducedMap Φ hleft hr _ _).symm
    _ = Vᴴ * Φ X Y * V := hright V hV X Y
    _ = Vᴴ * inducedMap Φ hr (Xᴴ * Y) * V := by rw [phi_eq_inducedMap Φ hleft hr X Y]

include hleft hright in
theorem inducedMap_conj_single (hr : 0 < r) {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) (c : ℂ) :
    inducedMap Φ hr (Vᴴ * Matrix.single i j c * V)
      = Vᴴ * inducedMap Φ hr (Matrix.single i j c) * V := by
  have hc : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hc, single_eq_gram (r := r) hr i j]
  have hgram := inducedMap_conj_gram Φ hleft hright hr hV
    (Matrix.single (⟨0, hr⟩ : Fin r) i (1 : ℂ)) (Matrix.single (⟨0, hr⟩ : Fin r) j (1 : ℂ))
  rw [Matrix.mul_smul, Matrix.smul_mul, map_smul, hgram, map_smul, Matrix.mul_smul,
    Matrix.smul_mul]

include hleft hright in
/-- **The induced map is conjugation equivariant.** -/
theorem inducedMap_equivariant (hr : 0 < r) {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    inducedMap Φ hr (Vᴴ * A * V) = Vᴴ * inducedMap Φ hr A * V := by
  conv_lhs => rw [matrix_eq_sum_single A]
  conv_rhs => rw [matrix_eq_sum_single A]
  simp only [Matrix.mul_sum, Matrix.sum_mul, map_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    inducedMap_conj_single Φ hleft hright hr hV i j (A i j)))

end Equivariance


section PartOne

variable (Φ : Matrix (Fin r) (Fin n) ℂ →ₗ⋆[ℂ]
    (Matrix (Fin r) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ))
  (hleft : ∀ U ∈ Matrix.unitaryGroup (Fin r) ℂ, ∀ X Y, Φ (U * X) (U * Y) = Φ X Y)
  (hright : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X Y, Φ (X * V) (Y * V) = Vᴴ * Φ X Y * V)

include hleft hright in
/-- **Part I, existence.**  A left-invariant, right-covariant sesquilinear causalizer is an
affine combination of the Gram matrix and the isotropic trace term. -/
theorem exists_causalizer_coeffs (hr : 0 < r) (hn : 2 ≤ n) :
    ∃ a b : ℂ, ∀ X Y : Matrix (Fin r) (Fin n) ℂ,
      Φ X Y = a • (Xᴴ * Y) + b • ((Xᴴ * Y).trace • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  refine ⟨coeffA hn (inducedMap Φ hr), coeffB hn (inducedMap Φ hr), fun X Y => ?_⟩
  rw [phi_eq_inducedMap Φ hleft hr X Y]
  exact classification hn (inducedMap Φ hr)
    (fun V hV A => inducedMap_equivariant Φ hleft hright hr hV A) _

end PartOne

section Uniqueness

variable {r n : ℕ}

/-- **Part I, uniqueness.**  The two coefficients are determined by the causalizer. -/
theorem causalizer_coeffs_unique (hr : 0 < r) (hn : 2 ≤ n) {a b a' b' : ℂ}
    (h : ∀ X Y : Matrix (Fin r) (Fin n) ℂ,
      a • (Xᴴ * Y) + b • ((Xᴴ * Y).trace • (1 : Matrix (Fin n) (Fin n) ℂ))
        = a' • (Xᴴ * Y) + b' • ((Xᴴ * Y).trace • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    a = a' ∧ b = b' := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by
    intro hc
    have h2 := congrArg Fin.val hc
    simp only [hi0, hi1] at h2
    exact absurd h2 (by norm_num)
  set a0 : Fin r := ⟨0, hr⟩ with ha0
  -- off-diagonal test pins `a`
  have hoff := h (Matrix.single a0 i0 (1 : ℂ)) (Matrix.single a0 i1 (1 : ℂ))
  rw [← single_eq_gram hr i0 i1] at hoff
  have htr : (Matrix.single i0 i1 (1 : ℂ)).trace = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp only [Matrix.diag_apply, Matrix.single_apply]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hne (h1.trans h2.symm)
  rw [htr] at hoff
  simp only [zero_smul, smul_zero, add_zero] at hoff
  have hae : a = a' := by
    have hentry := congrFun (congrFun hoff i0) i1
    simpa [Matrix.single_apply] using hentry
  refine ⟨hae, ?_⟩
  -- diagonal test pins `b`
  have hdiag := h (Matrix.single a0 i0 (1 : ℂ)) (Matrix.single a0 i0 (1 : ℂ))
  rw [← single_eq_gram hr i0 i0] at hdiag
  have htr1 : (Matrix.single i0 i0 (1 : ℂ)).trace = 1 := by
    rw [Matrix.trace, Finset.sum_eq_single i0]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hk
      exact absurd (Finset.mem_univ i0) hk
  rw [htr1] at hdiag
  have hentry := congrFun (congrFun hdiag i1) i1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_smul, Matrix.single_apply,
    Matrix.one_apply_eq] at hentry
  rw [if_neg (fun hc : i0 = i1 ∧ i0 = i1 => hne hc.1)] at hentry
  simpa using hentry

end Uniqueness

end GaloisForLFunctions.EquivariantCausalizer
