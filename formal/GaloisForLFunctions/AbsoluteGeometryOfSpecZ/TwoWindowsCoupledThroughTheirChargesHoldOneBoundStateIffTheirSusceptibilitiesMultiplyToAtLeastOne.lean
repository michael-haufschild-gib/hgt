import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePoleAddsOneNegativeSquareToTheBlockMatrixOfAWindow
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Two windows coupled through their charges hold one bound state iff their susceptibilities multiply to at least one

The neutral part of a window is a real symmetric form with one negative square, nonnegative
where a charge vanishes; a block and a far window couple by minus the product of their charges.
This file is the gluing lemma for that shape.

Let `A`, `B` be real symmetric forms and `u`, `v` charges with

* `A ≥ 0` on the kernel of `u` and `B ≥ 0` on the kernel of `v`;
* `A a = u`, `B b = v`, with the **susceptibilities** `α = u·a < 0` and `β = v·b < 0`.

Each form has one negative square, carried by `a` and by `b`. The **glued form** is
`A(x) + B(y) − 2 (u·x)(v·y)` (`glued`, `bilin_glued`). Then:

* if `αβ ≥ 1` the glued form has exactly one negative square (`hermNegIndex_glued_eq_one`): it
  is nonnegative on the hyperplane `u·x = α (v·y)` (`glued_nonneg_of_charge_eq`);
* if `αβ < 1` it has exactly two (`hermNegIndex_glued_eq_two`): it is negative on the plane of
  `a` and `b`, where it is `α s² − 2αβ st + β t²`.

In the coordinates `x = s a + x₀`, `y = t b + y₀` with `u·x₀ = 0 = v·y₀` the three parts are
orthogonal, so the glued form is the binary form above plus `A(x₀) + B(y₀)`; the binary form
has the determinant `αβ(1 − αβ)`.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Charges and the form of a symmetric matrix -/

section Forms

variable {ι : Type*} [Fintype ι]

/-- The charge `u·x` of a vector. -/
def chargeOf (u x : ι → ℝ) : ℝ := ∑ i, u i * x i

theorem chargeOf_sub_smul (u x a : ι → ℝ) (c s : ℝ) :
    chargeOf u (fun i => c * x i - s * a i) = c * chargeOf u x - s * chargeOf u a := by
  simp only [chargeOf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable {A : Matrix ι ι ℝ} {a u : ι → ℝ}

/-- If `A a = u`, the form pairs every vector with `a` through its charge. -/
theorem bilin_right_eq_chargeOf (hAa : ∀ i, ∑ j, A i j * a j = u i) (x : ι → ℝ) :
    bilin A x a = chargeOf u x := by
  simp only [bilin, chargeOf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hAa i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem bilin_left_eq_chargeOf (hA : ∀ i j, A i j = A j i)
    (hAa : ∀ i, ∑ j, A i j * a j = u i) (x : ι → ℝ) : bilin A a x = chargeOf u x := by
  rw [← bilin_right_eq_chargeOf hAa x]
  simp only [bilin]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hA j i]
    ring

/-- **The form on `c x − s a`** when `A a = u`:
`c² A(x) − 2cs (u·x) + s² (u·a)`. -/
theorem bilin_sub_smul (hA : ∀ i j, A i j = A j i) (hAa : ∀ i, ∑ j, A i j * a j = u i)
    (x : ι → ℝ) (c s : ℝ) :
    bilin A (fun i => c * x i - s * a i) (fun i => c * x i - s * a i) =
      c ^ 2 * bilin A x x - 2 * c * s * chargeOf u x + s ^ 2 * chargeOf u a := by
  have hexp : bilin A (fun i => c * x i - s * a i) (fun i => c * x i - s * a i) =
      c ^ 2 * bilin A x x - c * s * bilin A x a - c * s * bilin A a x + s ^ 2 * bilin A a a := by
    simp only [bilin, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, bilin_right_eq_chargeOf hAa x, bilin_left_eq_chargeOf hA hAa x,
    bilin_right_eq_chargeOf hAa a]
  ring

/-- A real family on whose span a real form is negative gives as many negative squares. -/
theorem card_le_hermNegIndex_of_real_neg {κ : Type*} [Fintype κ] (G : Matrix ι ι ℝ)
    (w : κ → ι → ℝ)
    (h : ∀ γ : κ → ℝ, γ ≠ 0 →
      bilin G (fun m => ∑ j, γ j * w j m) (fun m => ∑ j, γ j * w j m) < 0) :
    Fintype.card κ ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  let L : (κ → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun c m => ∑ j, c j * ((w j m : ℝ) : ℂ)
      map_add' := by
        intro c d
        funext m
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t c
        funext m
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  exact HeckeKreinToeplitz.card_le_hermNegIndex_of_forall_neg
    (G.map (↑) : Matrix ι ι ℂ) L
    (HeckeKreinToeplitz.hermQuad_complexify_neg (H := (G.map (↑) : Matrix ι ι ℂ))
      (fun i j => by simp) w fun γ hγ => by
        rw [HeckeKreinToeplitz.hermQuad_map_ofReal_real, dotProduct_mulVec_eq_bilin]
        exact h γ hγ)

/-- The Hermitian form of a real matrix is the sum of the real forms of the real and the
imaginary part. -/
theorem hermQuad_map_eq_bilin (G : Matrix ι ι ℝ) (c : ι → ℂ) :
    hermQuad (G.map (↑) : Matrix ι ι ℂ) c =
      bilin G (fun i => (c i).re) (fun i => (c i).re) +
        bilin G (fun i => (c i).im) (fun i => (c i).im) := by
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, dotProduct_mulVec_eq_bilin,
    dotProduct_mulVec_eq_bilin]

end Forms

/-! ### The glued form -/

section Glue

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Two forms coupled through minus the product of a charge of the first and a charge of the
second. -/
def glued (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  Matrix.of (Sum.elim (fun i => Sum.elim (A i) fun j => -(u i * v j))
    fun j => Sum.elim (fun i => -(u i * v j)) (B j))

variable (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ)

/-- **The glued form**: `A(x) + B(y) − 2 (u·x)(v·y)`. -/
theorem bilin_glued (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (glued A B u v) w w =
      bilin A (fun i => w (Sum.inl i)) (fun i => w (Sum.inl i)) +
        bilin B (fun j => w (Sum.inr j)) (fun j => w (Sum.inr j)) -
        2 * (chargeOf u (fun i => w (Sum.inl i)) * chargeOf v fun j => w (Sum.inr j)) := by
  have hcross : ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j) =
      chargeOf u (fun i => w (Sum.inl i)) * chargeOf v fun j => w (Sum.inr j) := by
    rw [chargeOf, chargeOf, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hcross' : ∑ j, ∑ i, w (Sum.inr j) * w (Sum.inl i) * (u i * v j) =
      chargeOf u (fun i => w (Sum.inl i)) * chargeOf v fun j => w (Sum.inr j) := by
    rw [Finset.sum_comm, ← hcross]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [bilin, glued, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    mul_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [hcross, hcross']
  ring

variable {A B u v} {a : ι₁ → ℝ} {b : ι₂ → ℝ}

/-- **The glued form is nonnegative on the hyperplane `u·x = α (v·y)`** when `β < 0` and
`αβ ≥ 1`. -/
theorem glued_nonneg_of_charge_eq (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hAa : ∀ i, ∑ j, A i j * a j = u i) (hBb : ∀ i, ∑ j, B i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin A x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin B y y)
    (hβ : chargeOf v b < 0) (hαβ : 1 ≤ chargeOf u a * chargeOf v b) (x : ι₁ → ℝ) (y : ι₂ → ℝ)
    (hxy : chargeOf u x = chargeOf u a * chargeOf v y) :
    0 ≤ bilin A x x + bilin B y y - 2 * (chargeOf u x * chargeOf v y) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = chargeOf u a := ⟨_, rfl⟩
  obtain ⟨β, hβ'⟩ : ∃ β : ℝ, β = chargeOf v b := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = chargeOf v y := ⟨_, rfl⟩
  rw [← hα, ← hβ'] at hαβ
  rw [← hβ'] at hβ
  rw [← hα, ← ht] at hxy
  -- the parts of `x` and `y` without charge
  have h1 := hApos (fun i => 1 * x i - t * a i) (by
    rw [chargeOf_sub_smul, hxy, ← hα]
    ring)
  have h2 := hBpos (fun j => β * y j - t * b j) (by
    rw [chargeOf_sub_smul, ← ht, ← hβ']
    ring)
  rw [bilin_sub_smul hA hAa, hxy, ← hα] at h1
  rw [bilin_sub_smul hB hBb, ← ht, ← hβ'] at h2
  rw [hxy, ← ht]
  have h3 : 0 ≤ β * (1 - α * β) * t ^ 2 :=
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hβ.le (by linarith)) (sq_nonneg t)
  have hβ2 : 0 < β ^ 2 := by nlinarith [mul_pos_of_neg_of_neg hβ hβ]
  by_contra hcon
  have hneg := mul_neg_of_pos_of_neg hβ2 (not_le.mp hcon)
  nlinarith [mul_nonneg hβ2.le h1]

/-- The form of the glued matrix on the plane of `a` and `b`. -/
theorem bilin_glued_plane (hAa : ∀ i, ∑ j, A i j * a j = u i)
    (hBb : ∀ i, ∑ j, B i j * b j = v i) (s t : ℝ) :
    bilin (glued A B u v) (Sum.elim (fun i => s * a i) fun j => t * b j)
        (Sum.elim (fun i => s * a i) fun j => t * b j) =
      chargeOf u a * s ^ 2 + 2 * (-(chargeOf u a * chargeOf v b)) * s * t +
        chargeOf v b * t ^ 2 := by
  have hA2 : bilin A (fun i => s * a i) (fun i => s * a i) = s ^ 2 * chargeOf u a := by
    rw [← bilin_right_eq_chargeOf hAa a]
    simp only [bilin, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hB2 : bilin B (fun j => t * b j) (fun j => t * b j) = t ^ 2 * chargeOf v b := by
    rw [← bilin_right_eq_chargeOf hBb b]
    simp only [bilin, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : chargeOf u (fun i => s * a i) = s * chargeOf u a := by
    simp only [chargeOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hv : chargeOf v (fun j => t * b j) = t * chargeOf v b := by
    simp only [chargeOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [bilin_glued]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA2, hB2, hu, hv]
  ring

/-- The functional `u·x − α (v·y)` on complex vectors. -/
def chargeFunctional (u : ι₁ → ℝ) (v : ι₂ → ℝ) (α : ℝ) : ((ι₁ ⊕ ι₂) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, (u i : ℂ) • (LinearMap.proj (Sum.inl i) : ((ι₁ ⊕ ι₂) → ℂ) →ₗ[ℂ] ℂ) -
    (α : ℂ) • ∑ j, (v j : ℂ) • (LinearMap.proj (Sum.inr j) : ((ι₁ ⊕ ι₂) → ℂ) →ₗ[ℂ] ℂ)

theorem chargeFunctional_apply (u : ι₁ → ℝ) (v : ι₂ → ℝ) (α : ℝ) (c : (ι₁ ⊕ ι₂) → ℂ) :
    chargeFunctional u v α c =
      ∑ i, (u i : ℂ) * c (Sum.inl i) - (α : ℂ) * ∑ j, (v j : ℂ) * c (Sum.inr j) := by
  simp [chargeFunctional, LinearMap.sum_apply]

theorem chargeFunctional_re (u : ι₁ → ℝ) (v : ι₂ → ℝ) (α : ℝ) (c : (ι₁ ⊕ ι₂) → ℂ) :
    (chargeFunctional u v α c).re = chargeOf u (fun i => (c (Sum.inl i)).re) -
      α * chargeOf v fun j => (c (Sum.inr j)).re := by
  rw [chargeFunctional_apply]
  simp [chargeOf, Complex.re_sum]

theorem chargeFunctional_im (u : ι₁ → ℝ) (v : ι₂ → ℝ) (α : ℝ) (c : (ι₁ ⊕ ι₂) → ℂ) :
    (chargeFunctional u v α c).im = chargeOf u (fun i => (c (Sum.inl i)).im) -
      α * chargeOf v fun j => (c (Sum.inr j)).im := by
  rw [chargeFunctional_apply]
  simp [chargeOf, Complex.im_sum]

/-- **Gluing with one bound state.** Let `A ≥ 0` on the kernel of `u`, `B ≥ 0` on the kernel of
`v`, `A a = u`, `B b = v`, with `α = u·a` and `β = v·b < 0`. If `αβ ≥ 1`, the glued form
`A(x) + B(y) − 2 (u·x)(v·y)` has exactly one negative square. -/
theorem hermNegIndex_glued_eq_one (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hAa : ∀ i, ∑ j, A i j * a j = u i) (hBb : ∀ i, ∑ j, B i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin A x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin B y y)
    (hβ : chargeOf v b < 0) (hαβ : 1 ≤ chargeOf u a * chargeOf v b) :
    hermNegIndex ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) = 1 := by
  have hα : chargeOf u a < 0 := by
    by_contra hcon
    have := mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hcon) hβ.le
    linarith
  refine le_antisymm ?_ ?_
  · -- nonnegative on the kernel of one functional
    have key : ∀ c : (ι₁ ⊕ ι₂) → ℂ,
        (∀ _ : Fin 1, chargeFunctional u v (chargeOf u a) c = 0) →
          0 ≤ hermQuad ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) c := by
      intro c hc
      have h0 := hc 0
      have hre := chargeFunctional_re u v (chargeOf u a) c
      have him := chargeFunctional_im u v (chargeOf u a) c
      rw [h0, Complex.zero_re] at hre
      rw [h0, Complex.zero_im] at him
      rw [hermQuad_map_eq_bilin, bilin_glued, bilin_glued]
      have h1 := glued_nonneg_of_charge_eq hA hB hAa hBb hApos hBpos hβ hαβ
        (fun i => (c (Sum.inl i)).re) (fun j => (c (Sum.inr j)).re) (by linarith)
      have h2 := glued_nonneg_of_charge_eq hA hB hAa hBb hApos hBpos hβ hαβ
        (fun i => (c (Sum.inl i)).im) (fun j => (c (Sum.inr j)).im) (by linarith)
      linarith
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
      (fun _ : Fin 1 => chargeFunctional u v (chargeOf u a)) key
    rwa [Fintype.card_fin] at h
  · -- negative on the line of `a`
    have h := card_le_hermNegIndex_of_real_neg (κ := Fin 1) (glued A B u v)
      (fun _ => Sum.elim a fun _ => 0) (by
        intro γ hγ
        have hγ0 : γ 0 ≠ 0 := fun h0 => hγ (funext fun i => by
          rw [Subsingleton.elim i 0, h0]
          rfl)
        have e : (fun m : ι₁ ⊕ ι₂ => ∑ j : Fin 1, γ j * (Sum.elim a (fun _ => (0 : ℝ)) m)) =
            Sum.elim (fun i => γ 0 * a i) fun j => 0 * b j := by
          funext m
          rw [Fin.sum_univ_one]
          cases m <;> simp
        rw [e, bilin_glued_plane hAa hBb]
        have := mul_neg_of_neg_of_pos hα (sq_pos_of_ne_zero hγ0)
        nlinarith)
    rwa [Fintype.card_fin] at h

/-- **Gluing with two bound states.** With the same forms, `α = u·a < 0`, `β = v·b < 0` and
`αβ < 1`, the glued form has exactly two negative squares. -/
theorem hermNegIndex_glued_eq_two (hAa : ∀ i, ∑ j, A i j * a j = u i)
    (hBb : ∀ i, ∑ j, B i j * b j = v i)
    (hApos : ∀ x, chargeOf u x = 0 → 0 ≤ bilin A x x)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin B y y)
    (hα : chargeOf u a < 0) (hβ : chargeOf v b < 0)
    (hαβ : chargeOf u a * chargeOf v b < 1) :
    hermNegIndex ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) = 2 := by
  refine le_antisymm ?_ ?_
  · -- nonnegative where both charges vanish
    have key : ∀ c : (ι₁ ⊕ ι₂) → ℂ,
        (∀ k : Fin 2, (![chargeFunctional u v 0,
          chargeFunctional (fun _ => 0) (fun j => -v j) 1] k) c = 0) →
          0 ≤ hermQuad ((glued A B u v).map (↑) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ) c := by
      intro c hc
      have h0 := hc 0
      have h1 := hc 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hure := chargeFunctional_re u v 0 c
      have huim := chargeFunctional_im u v 0 c
      have hvre := chargeFunctional_re (fun _ : ι₁ => 0) (fun j => -v j) 1 c
      have hvim := chargeFunctional_im (fun _ : ι₁ => 0) (fun j => -v j) 1 c
      rw [h0, Complex.zero_re, zero_mul, sub_zero] at hure
      rw [h0, Complex.zero_im, zero_mul, sub_zero] at huim
      rw [h1, Complex.zero_re] at hvre
      rw [h1, Complex.zero_im] at hvim
      have hv0 : ∀ y : ι₂ → ℝ, chargeOf (fun _ : ι₁ => (0 : ℝ)) (fun _ => (0 : ℝ)) -
          1 * chargeOf (fun j => -v j) y = chargeOf v y := fun y => by
        simp only [chargeOf, zero_mul, Finset.sum_const_zero, neg_mul, Finset.sum_neg_distrib]
        ring
      have hz : ∀ f : ι₁ → ℝ, chargeOf (fun _ : ι₁ => (0 : ℝ)) f = 0 := fun f => by
        simp [chargeOf]
      rw [hz] at hvre hvim
      have hvre' : chargeOf v (fun j => (c (Sum.inr j)).re) = 0 := by
        have := hv0 fun j => (c (Sum.inr j)).re
        rw [hz] at this
        linarith
      have hvim' : chargeOf v (fun j => (c (Sum.inr j)).im) = 0 := by
        have := hv0 fun j => (c (Sum.inr j)).im
        rw [hz] at this
        linarith
      rw [hermQuad_map_eq_bilin, bilin_glued, bilin_glued, ← hure, ← huim, hvre', hvim']
      have a1 := hApos _ hure.symm
      have a2 := hApos _ huim.symm
      have b1 := hBpos _ hvre'
      have b2 := hBpos _ hvim'
      linarith
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
      (fun k : Fin 2 => (![chargeFunctional u v 0,
        chargeFunctional (fun _ => 0) (fun j => -v j) 1] k)) key
    rwa [Fintype.card_fin] at h
  · -- negative on the plane of `a` and `b`
    have h := card_le_hermNegIndex_of_real_neg (κ := Fin 2) (glued A B u v)
      (![Sum.elim a fun _ => 0, Sum.elim (fun _ => 0) b]) (by
        intro γ hγ
        have e : (fun m : ι₁ ⊕ ι₂ => ∑ j : Fin 2, γ j *
            ((![Sum.elim a fun _ => (0 : ℝ), Sum.elim (fun _ => (0 : ℝ)) b] : Fin 2 → _) j m)) =
            Sum.elim (fun i => γ 0 * a i) fun j => γ 1 * b j := by
          funext m
          rw [Fin.sum_univ_two]
          cases m <;> simp
        rw [e, bilin_glued_plane hAa hBb]
        refine quad_neg_of_disc hα ?_ ?_
        · have h1 : 0 < chargeOf u a * chargeOf v b := mul_pos_of_neg_of_neg hα hβ
          nlinarith
        · by_contra hcon
          push Not at hcon
          refine hγ (funext fun i => ?_)
          fin_cases i
          · exact hcon.1
          · exact hcon.2)
    rwa [Fintype.card_fin] at h

end Glue

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
