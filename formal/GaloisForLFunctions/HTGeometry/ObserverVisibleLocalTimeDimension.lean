import GaloisForLFunctions.QuantumAlg.Util.QuantumFisher

/-!
# Observer-visible Hamiltonian directions and exact QFI rank

For a finite Hermitian generator family, the pure-state QFI is four times the
real Gram matrix of the centered generator actions.  This file exposes the
realification matrix and proves equality—not only an upper bound—between QFI
rank and the number of real projective directions visible to the input state.

This is the algebraic core of the observer-visible local-time obstruction.
No circuit-complexity, Gaussian-volume, or unproved no-shortcut statement is
introduced here.
-/

namespace QuantumAlg

open Matrix

variable {n : Type*} [Fintype n] {M : ℕ}

/-- Real and imaginary coordinates of the centered generator actions.
Its column rank is the real dimension of the projective Hamiltonian action
visible to the state. -/
noncomputable def centeredRealification (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) : Matrix (Sum n n) (Fin M) ℝ
  | Sum.inl i, a => (centered ψ (h a) i).re
  | Sum.inr i, a => (centered ψ (h a) i).im

/-- The Gram matrix of the realified centered actions is the real part of
their complex Gram matrix. -/
theorem centeredRealification_gram_apply (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (a b : Fin M) :
    ((centeredRealification ψ h)ᵀ * centeredRealification ψ h) a b =
      (star (centered ψ (h a)) ⬝ᵥ centered ψ (h b)).re := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_sum_type]
  simp only [centeredRealification, dotProduct, Complex.re_sum, Pi.star_apply,
    Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [neg_mul, sub_neg_eq_add, Finset.sum_add_distrib]

/-- Exact Gram factorization of the pure-state QFI. -/
theorem qfim_eq_four_smul_realification_gram {ψ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) {h : Fin M → Matrix n n ℂ}
    (hh : ∀ a, (h a)ᴴ = h a) :
    qfim ψ h = (4 : ℝ) •
      ((centeredRealification ψ h)ᵀ * centeredRealification ψ h) := by
  ext a b
  simp [qfim_apply, qCov_eq_inner_re hψ (hh a),
    centeredRealification_gram_apply]

/-- **Observer-visible rank identity.**  For Hermitian generators and a unit
state, QFI rank equals the real rank of the centered generator-action matrix. -/
theorem qfim_rank_eq_centeredRealification_rank {ψ : n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) {h : Fin M → Matrix n n ℂ}
    (hh : ∀ a, (h a)ᴴ = h a) :
    (qfim ψ h).rank = (centeredRealification ψ h).rank := by
  let A := centeredRealification ψ h
  let D : Matrix (Fin M) (Fin M) ℝ := (4 : ℝ) • 1
  have hD : IsUnit D.det := by
    simp [D]
  have hmul : D * (Aᵀ * A) = (4 : ℝ) • (Aᵀ * A) := by
    classical
    ext a b
    simp [D, Matrix.mul_apply, Matrix.one_apply]
  rw [qfim_eq_four_smul_realification_gram hψ hh, ← hmul,
    Matrix.rank_mul_eq_right_of_isUnit_det D (Aᵀ * A) hD,
    Matrix.rank_transpose_mul_self]

/-- Real-linear coefficient action through the centered generator vectors. -/
noncomputable def observerAction (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) : n → ℂ :=
  ∑ a, (x a : ℂ) • centered ψ (h a)

/-- Hamiltonian assembled from real coefficients in a Hermitian dictionary. -/
noncomputable def generatorCombination (h : Fin M → Matrix n n ℂ)
    (x : Fin M → ℝ) : Matrix n n ℂ :=
  ∑ a, (x a : ℂ) • h a

theorem centered_add (ψ : n → ℂ) (A B : Matrix n n ℂ) :
    centered ψ (A + B) = centered ψ A + centered ψ B := by
  ext i
  simp [centered, expval_add, Matrix.add_mulVec]
  ring

theorem centered_ofReal_smul (ψ : n → ℂ) (c : ℝ) (A : Matrix n n ℂ) :
    centered ψ ((c : ℂ) • A) = (c : ℂ) • centered ψ A := by
  ext i
  simp [centered, expval_smul, Matrix.smul_mulVec]
  ring

theorem centered_sum (ψ : n → ℂ) {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) :
    centered ψ (∑ i, A i) = ∑ i, centered ψ (A i) := by
  classical
  have aux : ∀ s : Finset ι,
      centered ψ (∑ i ∈ s, A i) = ∑ i ∈ s, centered ψ (A i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [centered, expval_zero]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, centered_add, ih]
  simpa using aux Finset.univ

/-- Centering commutes with assembly of a real Hamiltonian coefficient vector. -/
theorem centered_generatorCombination (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) :
    centered ψ (generatorCombination h x) = observerAction ψ h x := by
  simp [generatorCombination, observerAction, centered_sum, centered_ofReal_smul]

theorem centeredRealification_mulVec_apply_inl (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) (i : n) :
    (centeredRealification ψ h *ᵥ x) (Sum.inl i) =
      (observerAction ψ h x i).re := by
  simp [Matrix.mulVec, dotProduct, centeredRealification, observerAction,
    Complex.re_sum, Complex.mul_re]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem centeredRealification_mulVec_apply_inr (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) (i : n) :
    (centeredRealification ψ h *ᵥ x) (Sum.inr i) =
      (observerAction ψ h x i).im := by
  simp [Matrix.mulVec, dotProduct, centeredRealification, observerAction,
    Complex.im_sum, Complex.mul_im]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The realification has exactly the same coefficient kernel as the complex
observer-action map. -/
theorem centeredRealification_mulVec_eq_zero_iff (ψ : n → ℂ)
    (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) :
    centeredRealification ψ h *ᵥ x = 0 ↔ observerAction ψ h x = 0 := by
  constructor
  · intro hx
    funext i
    apply Complex.ext
    · simpa [centeredRealification_mulVec_apply_inl] using
        congrFun hx (Sum.inl i)
    · simpa [centeredRealification_mulVec_apply_inr] using
        congrFun hx (Sum.inr i)
  · intro hx
    funext i
    rcases i with i | i
    · rw [centeredRealification_mulVec_apply_inl, hx]
      rfl
    · rw [centeredRealification_mulVec_apply_inr, hx]
      rfl

/-- Vanishing centered action is exactly the statement that the state is an
eigenvector with eigenvalue equal to its expectation. -/
theorem centered_eq_zero_iff (ψ : n → ℂ) (A : Matrix n n ℂ) :
    centered ψ A = 0 ↔ A *ᵥ ψ = (expval ψ A) • ψ := by
  simp [centered, sub_eq_zero]

/-- A coefficient vector is invisible exactly when its assembled Hamiltonian
has the state as an eigenvector with eigenvalue equal to its expectation. -/
theorem centeredRealification_mulVec_eq_zero_iff_eigenvector
    (ψ : n → ℂ) (h : Fin M → Matrix n n ℂ) (x : Fin M → ℝ) :
    centeredRealification ψ h *ᵥ x = 0 ↔
      generatorCombination h x *ᵥ ψ =
        (expval ψ (generatorCombination h x)) • ψ := by
  rw [centeredRealification_mulVec_eq_zero_iff, ← centered_generatorCombination,
    centered_eq_zero_iff]

/-- **Fixed observer-channel codimension law.**  If a source subspace is sent
into a target observer channel, its dimension is at most nullity plus target
dimension. -/
theorem observerChannel_subspace_finrank_le
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] W) (U : Submodule ℝ V) (K : Submodule ℝ W)
    (hUK : ∀ x : U, T x.1 ∈ K) :
    Module.finrank ℝ U ≤
      Module.finrank ℝ (LinearMap.ker T) + Module.finrank ℝ K := by
  let F : U →ₗ[ℝ] K :=
    (T.domRestrict U).codRestrict K hUK
  let j : LinearMap.ker F →ₗ[ℝ] LinearMap.ker T :=
    { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker T => (z : V)) hxy
  have hker : Module.finrank ℝ (LinearMap.ker F) ≤
      Module.finrank ℝ (LinearMap.ker T) :=
    j.finrank_le_finrank_of_injective hj
  have hrange : Module.finrank ℝ (LinearMap.range F) ≤ Module.finrank ℝ K :=
    Submodule.finrank_le _
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  omega

/-- Rank form of the fixed observer-channel law:
`dim U + rank T <= dim V + dim K`. -/
theorem observerChannel_subspace_finrank_add_rank_le
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] W) (U : Submodule ℝ V) (K : Submodule ℝ W)
    (hUK : ∀ x : U, T x.1 ∈ K) :
    Module.finrank ℝ U + Module.finrank ℝ (LinearMap.range T) ≤
      Module.finrank ℝ V + Module.finrank ℝ K := by
  have hbound := observerChannel_subspace_finrank_le T U K hUK
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  omega

/-- Exact dimension of the preimage of an observer channel. -/
theorem observerChannel_preimage_finrank_eq
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] W) (K : Submodule ℝ W) :
    Module.finrank ℝ (K.comap T) =
      Module.finrank ℝ (LinearMap.ker T) +
        Module.finrank ℝ ((K ⊓ T.range) : Submodule ℝ W) := by
  let P : Submodule ℝ V := K.comap T
  let Q : Submodule ℝ W := K ⊓ T.range
  let F : P →ₗ[ℝ] Q :=
    (T.domRestrict P).codRestrict Q fun x => ⟨x.2, ⟨x.1, rfl⟩⟩
  have hFsurj : Function.Surjective F := by
    intro y
    rcases y.2.2 with ⟨x, hx⟩
    have hK : T x ∈ K := by rw [hx]; exact y.2.1
    let p : P := ⟨x, hK⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hx
  have hrange : LinearMap.range F = ⊤ := LinearMap.range_eq_top.mpr hFsurj
  have hker : LinearMap.ker F =
      (LinearMap.ker T).comap P.subtype := by
    simp [F, LinearMap.ker_domRestrict]
  have hkerLe : LinearMap.ker T ≤ P := by
    intro x hx
    change T x ∈ K
    rw [LinearMap.mem_ker.mp hx]
    exact K.zero_mem
  have hkerRank : Module.finrank ℝ (LinearMap.ker F) =
      Module.finrank ℝ (LinearMap.ker T) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hkerLe).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  rw [hrange, finrank_top, hkerRank] at hrn
  simpa [P, Q, add_comm] using hrn.symm

end QuantumAlg
