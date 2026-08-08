import GaloisForLFunctions.HTGeometry.PlaneRiemannRelations

/-!
# Generalized Riemann relations for a two-generated period lattice

Rank two costs nothing in any complex dimension.  The imaginary part of a Hermitian form vanishes
on the diagonal and is antisymmetric, so on a subgroup with two generators the only constraint is a
single real number, `Im H (w1, w2)`, and a single positive rescaling of the form makes it an
integer.  The construction therefore needs no analytic input: any positive-definite Hermitian form
on the ambient space -- for instance the one supplied by an inner product -- may be used as the
seed.

`exists_hermitian_positive_integral_of_two_generators` packages the conclusion in the shape a
quasi-Abelian facet certificate requires.  Together with the complex-independent case this leaves
open only lattices of rank at least three that are complex-dependent.
-/

open ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

/-- Integrality of a biadditive real pairing propagates from generators to the whole subgroup. -/
theorem exists_int_of_mem_closure_of_biadditive {A : Type*} [AddCommGroup A]
    {B : A → A → ℝ} {s : Set A}
    (hl : ∀ u v w : A, B (u + v) w = B u w + B v w)
    (hr : ∀ u v w : A, B u (v + w) = B u v + B u w)
    (hgen : ∀ a ∈ s, ∀ b ∈ s, ∃ n : ℤ, B a b = (n : ℝ))
    {x y : A} (hx : x ∈ AddSubgroup.closure s) (hy : y ∈ AddSubgroup.closure s) :
    ∃ n : ℤ, B x y = (n : ℝ) := by
  have hzl : ∀ w : A, B 0 w = 0 := by
    intro w
    have h := hl 0 0 w
    rw [add_zero] at h
    linarith
  have hnl : ∀ u w : A, B (-u) w = -B u w := by
    intro u w
    have h := hl (-u) u w
    rw [neg_add_cancel, hzl] at h
    linarith
  have hzr : ∀ u : A, B u 0 = 0 := by
    intro u
    have h := hr u 0 0
    rw [add_zero] at h
    linarith
  have hnr : ∀ u w : A, B u (-w) = -B u w := by
    intro u w
    have h := hr u (-w) w
    rw [neg_add_cancel, hzr] at h
    linarith
  have step1 : ∀ b ∈ s, ∀ u ∈ AddSubgroup.closure s, ∃ n : ℤ, B u b = (n : ℝ) := by
    intro b hb u hu
    induction hu using AddSubgroup.closure_induction with
    | mem a ha => exact hgen a ha b hb
    | zero => exact ⟨0, by rw [hzl]; simp⟩
    | add p q _ _ hp hq =>
        obtain ⟨n, hn⟩ := hp
        obtain ⟨m, hm⟩ := hq
        exact ⟨n + m, by rw [hl, hn, hm]; push_cast; ring⟩
    | neg p _ hp =>
        obtain ⟨n, hn⟩ := hp
        exact ⟨-n, by rw [hnl, hn]; push_cast; ring⟩
  induction hy using AddSubgroup.closure_induction with
  | mem b hb => exact step1 b hb x hx
  | zero => exact ⟨0, by rw [hzr]; simp⟩
  | add p q _ _ hp hq =>
      obtain ⟨n, hn⟩ := hp
      obtain ⟨m, hm⟩ := hq
      exact ⟨n + m, by rw [hr, hn, hm]; push_cast; ring⟩
  | neg p _ hp =>
      obtain ⟨n, hn⟩ := hp
      exact ⟨-n, by rw [hnr, hn]; push_cast; ring⟩

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- A positive multiple of the inner product, written as a Hermitian form linear in its first
argument. -/
noncomputable def innerHermitian (c : ℝ) (x y : W) : ℂ := (c : ℂ) * inner ℂ y x

theorem innerHermitian_add_left (c : ℝ) (x y z : W) :
    innerHermitian c (x + y) z = innerHermitian c x z + innerHermitian c y z := by
  simp only [innerHermitian, inner_add_right, mul_add]

theorem innerHermitian_smul_left (c : ℝ) (a : ℂ) (x y : W) :
    innerHermitian c (a • x) y = a * innerHermitian c x y := by
  simp only [innerHermitian, inner_smul_right]
  ring

theorem innerHermitian_hermitian (c : ℝ) (x y : W) :
    innerHermitian c y x = star (innerHermitian c x y) := by
  simp only [innerHermitian, star_mul', Complex.star_def, Complex.conj_ofReal,
    inner_conj_symm]

theorem innerHermitian_self_re (c : ℝ) (x : W) :
    (innerHermitian c x x).re = c * ‖x‖ ^ 2 := by
  rw [innerHermitian, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    ← RCLike.re_to_complex, ← RCLike.im_to_complex, inner_self_eq_norm_sq, inner_self_im]
  ring

theorem innerHermitian_pos {c : ℝ} (hc : 0 < c) {x : W} (hx : x ≠ 0) :
    0 < (innerHermitian c x x).re := by
  rw [innerHermitian_self_re]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

theorem innerHermitian_im (c : ℝ) (x y : W) :
    (innerHermitian c x y).im = c * (inner ℂ y x : ℂ).im := by
  rw [innerHermitian]
  simp

theorem inner_self_im_eq_zero (x : W) : (inner ℂ x x : ℂ).im = 0 := by
  rw [← RCLike.im_to_complex]
  exact inner_self_im x

theorem inner_im_swap (x y : W) : (inner ℂ y x : ℂ).im = -(inner ℂ x y : ℂ).im := by
  have h : (inner ℂ y x : ℂ) = conj (inner ℂ x y : ℂ) := (inner_conj_symm y x).symm
  rw [h, Complex.conj_im]

/-- On the generating pair the imaginary part takes only three values. -/
theorem inner_im_pair_cases {ω₁ ω₂ a b : W}
    (ha : a = ω₁ ∨ a = ω₂) (hb : b = ω₁ ∨ b = ω₂) :
    (inner ℂ b a : ℂ).im = 0 ∨ (inner ℂ b a : ℂ).im = (inner ℂ ω₂ ω₁ : ℂ).im
      ∨ (inner ℂ b a : ℂ).im = -(inner ℂ ω₂ ω₁ : ℂ).im := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> subst h1 <;> subst h2
  · exact Or.inl (inner_self_im_eq_zero _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (inner_im_swap _ _))
  · exact Or.inl (inner_self_im_eq_zero _)

/-- **Generalized Riemann relations for every two-generated subgroup, in any complex dimension.** -/
theorem exists_innerHermitian_pos_integral (ω₁ ω₂ : W) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ AddSubgroup.closure ({ω₁, ω₂} : Set W),
      ∀ y ∈ AddSubgroup.closure ({ω₁, ω₂} : Set W),
        ∃ n : ℤ, (innerHermitian c x y).im = (n : ℝ) := by
  have hbi : ∀ c : ℝ, (∀ u v w : W, (innerHermitian c (u + v) w).im
        = (innerHermitian c u w).im + (innerHermitian c v w).im) ∧
      (∀ u v w : W, (innerHermitian c u (v + w)).im
        = (innerHermitian c u v).im + (innerHermitian c u w).im) := by
    intro c
    constructor
    · intro u v w
      rw [innerHermitian_add_left, Complex.add_im]
    · intro u v w
      simp only [innerHermitian_im, inner_add_left, Complex.add_im]
      ring
  rcases eq_or_ne ((inner ℂ ω₂ ω₁ : ℂ).im) 0 with hD0 | hD0
  · refine ⟨1, one_pos, fun x hx y hy =>
      exists_int_of_mem_closure_of_biadditive (B := fun u v : W => (innerHermitian 1 u v).im)
        (s := ({ω₁, ω₂} : Set W)) (hbi 1).1 (hbi 1).2 ?_ hx hy⟩
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    refine ⟨0, ?_⟩
    rw [innerHermitian_im]
    rcases inner_im_pair_cases ha hb with h | h | h
    · rw [h]; ring
    · rw [h, hD0]; ring
    · rw [h, hD0]; ring
  · refine ⟨|(inner ℂ ω₂ ω₁ : ℂ).im|⁻¹, by positivity, fun x hx y hy =>
      exists_int_of_mem_closure_of_biadditive
        (B := fun u v : W => (innerHermitian |(inner ℂ ω₂ ω₁ : ℂ).im|⁻¹ u v).im)
        (s := ({ω₁, ω₂} : Set W)) (hbi _).1 (hbi _).2 ?_ hx hy⟩
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rw [innerHermitian_im]
    rcases lt_or_gt_of_ne hD0 with hsign | hsign
    · rcases inner_im_pair_cases ha hb with h | h | h
      · exact ⟨0, by rw [h]; ring⟩
      · exact ⟨-1, by rw [h, abs_of_neg hsign]; push_cast; field_simp⟩
      · exact ⟨1, by rw [h, abs_of_neg hsign]; push_cast; field_simp⟩
    · rcases inner_im_pair_cases ha hb with h | h | h
      · exact ⟨0, by rw [h]; ring⟩
      · exact ⟨1, by rw [h, abs_of_pos hsign]; push_cast; field_simp⟩
      · exact ⟨-1, by rw [h, abs_of_pos hsign]; push_cast; field_simp⟩

/-- **The certificate shape.**  A two-generated period lattice satisfies the generalized Riemann
relations, in any complex dimension and with no analytic input. -/
theorem exists_hermitian_positive_integral_of_two_generators (ω₁ ω₂ : W) :
    ∃ H : W → W → ℂ,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ (a : ℂ) (x y), H (a • x) y = a * H x y) ∧
      (∀ x y, H y x = star (H x y)) ∧
      (∀ x, x ≠ 0 → 0 < (H x x).re) ∧
      (∀ x ∈ AddSubgroup.closure ({ω₁, ω₂} : Set W),
        ∀ y ∈ AddSubgroup.closure ({ω₁, ω₂} : Set W), ∃ n : ℤ, (H x y).im = (n : ℝ)) := by
  obtain ⟨c, hc, hint⟩ := exists_innerHermitian_pos_integral ω₁ ω₂
  exact ⟨innerHermitian c, innerHermitian_add_left c, innerHermitian_smul_left c,
    innerHermitian_hermitian c, fun x hx => innerHermitian_pos hc hx, hint⟩

end GaloisForLFunctions.HTGeometry
