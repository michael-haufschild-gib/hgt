import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState

/-!
# The witness complement is positive

A Hermitian kernel `k` on a group with finite index `κ(k) = m` attains `m` on a finite
**witness family** `x` (`HeckeKreinToeplitz.exists_hermNegIndex_gram_eq_negIndex`). All negative
squares live on the witnesses:

* **Witness complement** (`hermQuad_nonneg_of_orthogonal_witness`). On any family `y`, a
  coefficient vector `c` that is `k`-orthogonal to every witness point,
  `Σ_b k(x_a⁻¹ y_b) c_b = 0`, has `hermQuad (gram k y) c ≥ 0`. Otherwise `c` and an
  `m`-dimensional negative subspace on `x` span an `(m + 1)`-dimensional negative subspace on
  `x ⊔ y` (`hermQuad_gram_sumElim`).
* **Escape** (`negIndex_eq_zero_or_top_of_escape`). If every pair of finite families `x, y` can
  be separated by a translate, `k(x_a⁻¹ t y_b) = 0`, then `κ(k) ∈ {0, ∞}`: the translate `t y` of
  any family lies in the witness complement and has the same Gram matrix as `y`.

The escape law is the non-commutative form of the zero-or-infinity law for axis-supported kernels
on `ℤ^S` (`ArithmeticKreinLangerTheory`). It is the engine of every zero-or-infinity law in this
programme: a support condition that translates can escape leaves no room for a finite nonzero
number of negative squares.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {G : Type*} [Group G]

/-- A **witness family** of `k`: its Gram matrix carries the whole index. -/
def IsWitness (k : G → ℂ) {ι : Type*} [Fintype ι] (x : ι → G) : Prop :=
  (hermNegIndex (gram k x) : ℕ∞) = negIndex k

theorem exists_isWitness {k : G → ℂ} (h : negIndex k < ⊤) :
    ∃ (n : ℕ) (x : Fin n → G), IsWitness k x :=
  exists_hermNegIndex_gram_eq_negIndex h

/-- The form on a joined family `x ⊔ y`, for a vector whose `y`-part is orthogonal to the points
of `x`: the cross terms vanish. -/
theorem hermQuad_gram_sumElim {k : G → ℂ} (hk : IsHermKernel k) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (x : ι → G) (y : κ → G) (w : ι → ℂ) (c : κ → ℂ)
    (horth : ∀ a, ∑ b, k ((x a)⁻¹ * y b) * c b = 0) :
    hermQuad (gram k (Sum.elim x y)) (Sum.elim w c) =
      hermQuad (gram k x) w + hermQuad (gram k y) c := by
  have hxy : ∑ a, ∑ b, conj (w a) * k ((x a)⁻¹ * y b) * c b = 0 := by
    refine sum_eq_zero fun a _ => ?_
    simp_rw [mul_assoc]
    rw [← mul_sum, horth a, mul_zero]
  have hyx : ∑ b, ∑ a, conj (c b) * k ((y b)⁻¹ * x a) * w a = 0 := by
    rw [Finset.sum_comm]
    refine sum_eq_zero fun a _ => ?_
    have h := congrArg conj (horth a)
    simp only [map_sum, map_mul, map_zero] at h
    calc ∑ b, conj (c b) * k ((y b)⁻¹ * x a) * w a
        = (∑ b, conj (k ((x a)⁻¹ * y b)) * conj (c b)) * w a := by
          rw [sum_mul]
          refine sum_congr rfl fun b _ => ?_
          rw [← hk, mul_inv_rev, inv_inv]
          ring
      _ = 0 := by rw [h, zero_mul]
  simp only [hermQuad_gram, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_add_distrib,
    hxy, hyx, add_zero, zero_add, Complex.add_re]

/-- **The witness complement is positive.** A coefficient vector orthogonal to every point of a
witness family has nonnegative form. -/
theorem hermQuad_nonneg_of_orthogonal_witness {k : G → ℂ} (hk : IsHermKernel k) {ι κ : Type*}
    [Fintype ι] [Fintype κ] {x : ι → G} (hx : IsWitness k x) (y : κ → G) (c : κ → ℂ)
    (horth : ∀ a, ∑ b, k ((x a)⁻¹ * y b) * c b = 0) : 0 ≤ hermQuad (gram k y) c := by
  by_contra hneg
  push Not at hneg
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-gram k x)
  set r := Module.finrank ℂ W
  set bW := Module.finBasis ℂ W
  let L : (Option (Fin r) → ℂ) →ₗ[ℂ] (ι ⊕ κ → ℂ) :=
    { toFun := fun β => Sum.elim (fun a => ∑ i, β (some i) * ((bW i : W) : ι → ℂ) a)
        (fun b => β none * c b)
      map_add' := fun β β' => by
        funext p
        cases p <;> simp [add_mul, sum_add_distrib]
      map_smul' := fun t β => by
        funext p
        cases p <;> simp [mul_assoc, mul_sum] }
  have hneg' : ∀ β, β ≠ 0 → hermQuad (gram k (Sum.elim x y)) (L β) < 0 := by
    intro β hβ
    set w : W := ∑ i, β (some i) • bW i
    have hw : ((w : W) : ι → ℂ) = fun a => ∑ i, β (some i) * ((bW i : W) : ι → ℂ) a := by
      funext a; simp [w, Finset.sum_apply]
    have horth' : ∀ a, ∑ b, k ((x a)⁻¹ * y b) * (β none • c) b = 0 := fun a => by
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ (β none)]
      rw [← mul_sum, horth a, mul_zero]
    have hLβ : L β = Sum.elim (w : ι → ℂ) (β none • c) := by
      rw [hw]; rfl
    rw [hLβ, hermQuad_gram_sumElim hk x y _ _ horth', ArithmeticCastelnuovoSeveri.hermQuad_smul]
    by_cases hw0 : (w : ι → ℂ) = 0
    · -- the witness part vanishes, so the coefficient of `c` does not
      have hβs : ∀ i, β (some i) = 0 := fun i =>
        Fintype.linearIndependent_iff.mp bW.linearIndependent (fun i => β (some i))
          (Subtype.ext hw0) i
      have hβn : β none ≠ 0 := by
        intro h0
        apply hβ
        funext o
        cases o with
        | none => exact h0
        | some i => exact hβs i
      rw [hw0]
      have : hermQuad (gram k x) 0 = 0 := by simp [hermQuad]
      rw [this, zero_add]
      exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hβn) hneg
    · have h1 := hW w w.2 hw0
      rw [hermQuad_neg] at h1
      nlinarith [Complex.normSq_nonneg (β none)]
  have h := card_le_hermNegIndex_of_forall_neg (gram k (Sum.elim x y)) L hneg'
  rw [Fintype.card_option, Fintype.card_fin] at h
  have h2 := (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex k (Sum.elim x y))
  rw [← hx, hermNegIndex, ← hrank] at h2
  norm_cast at h2
  omega

/-- On a witness complement the kernel is positive: the Gram matrix of a family all of whose
points are orthogonal to the witnesses has no negative square. -/
theorem hermQuad_nonneg_of_forall_orthogonal {k : G → ℂ} (hk : IsHermKernel k) {ι κ : Type*}
    [Fintype ι] [Fintype κ] {x : ι → G} (hx : IsWitness k x) (y : κ → G)
    (hy : ∀ a b, k ((x a)⁻¹ * y b) = 0) (c : κ → ℂ) : 0 ≤ hermQuad (gram k y) c :=
  hermQuad_nonneg_of_orthogonal_witness hk hx y c fun a => by simp [hy]

/-- **Escape.** If translates separate every pair of finite families, a finite index is zero. -/
theorem negIndex_eq_zero_of_escape {k : G → ℂ} (hk : IsHermKernel k) (hfin : negIndex k < ⊤)
    (hesc : ∀ (m n : ℕ) (x : Fin m → G) (y : Fin n → G),
      ∃ t : G, ∀ a b, k ((x a)⁻¹ * (t * y b)) = 0) :
    negIndex k = 0 := by
  obtain ⟨m, x, hx⟩ := exists_isWitness hfin
  refine negIndex_eq_zero_iff.mpr fun n y c => ?_
  obtain ⟨t, ht⟩ := hesc m n x y
  have := hermQuad_nonneg_of_forall_orthogonal hk hx (fun b => t * y b) ht c
  rwa [gram_mul_left] at this

/-- **The zero-or-infinity law of escape.** -/
theorem negIndex_eq_zero_or_top_of_escape {k : G → ℂ} (hk : IsHermKernel k)
    (hesc : ∀ (m n : ℕ) (x : Fin m → G) (y : Fin n → G),
      ∃ t : G, ∀ a b, k ((x a)⁻¹ * (t * y b)) = 0) :
    negIndex k = 0 ∨ negIndex k = ⊤ := by
  rcases eq_or_ne (negIndex k) ⊤ with h | h
  · exact Or.inr h
  · exact Or.inl (negIndex_eq_zero_of_escape hk (lt_top_iff_ne_top.mpr h) hesc)

end GaloisForLFunctions.AdelicKreinGeometry
