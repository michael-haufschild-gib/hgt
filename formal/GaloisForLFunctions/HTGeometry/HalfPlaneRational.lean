import GaloisForLFunctions.HTGeometry.DigammaHalfTranslateIndependent

/-!
# Half-plane rational functions

A function is *half-plane rational* when it agrees with a quotient of polynomials on the right
half-plane, off a finite exceptional set and off the denominator's zeros.  This is the closure of
the rational functions under the bookkeeping that arises when a value relation is assembled from
finitely many simple fractions: sums, differences, constant multiples, and the substitution
`z ↦ 2z` all stay inside the class, and so does any function agreeing with a member off a finite
set.

Half-translate digamma independence is stated in this language: a `ℂ`-combination of the two digamma
modes carried by the archimedean factor is half-plane rational only when it is trivial.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Agreement with a quotient of polynomials on the right half-plane, off a finite set. -/
def IsHalfPlaneRational (f : ℂ → ℂ) : Prop :=
  ∃ (P Q : Polynomial ℂ) (T : Set ℂ), Q ≠ 0 ∧ T.Finite ∧
    ∀ z : ℂ, 0 < z.re → z ∉ T → Q.eval z ≠ 0 → f z = P.eval z / Q.eval z

theorem IsHalfPlaneRational.congr {f g : ℂ → ℂ} {T' : Set ℂ} (hT' : T'.Finite)
    (hfg : ∀ z : ℂ, 0 < z.re → z ∉ T' → f z = g z) (hg : IsHalfPlaneRational g) :
    IsHalfPlaneRational f := by
  obtain ⟨P, Q, T, hQ, hT, hrel⟩ := hg
  refine ⟨P, Q, T ∪ T', hQ, hT.union hT', fun z hz hzT hQz => ?_⟩
  simp only [Set.mem_union, not_or] at hzT
  rw [hfg z hz hzT.2]
  exact hrel z hz hzT.1 hQz

theorem isHalfPlaneRational_const (c : ℂ) : IsHalfPlaneRational (fun _ => c) := by
  refine ⟨C c, 1, ∅, one_ne_zero, Set.finite_empty, fun z _ _ _ => ?_⟩
  simp

theorem isHalfPlaneRational_simple (β : ℂ) :
    IsHalfPlaneRational (fun z => 1 / (z + β)) := by
  have hQ : (X + C β : Polynomial ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval (0 : ℂ)) h0
    have h2 := congrArg (Polynomial.eval (1 : ℂ)) h0
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_zero, zero_add] at h1 h2
    rw [h1] at h2
    norm_num at h2
  refine ⟨1, X + C β, ∅, hQ, Set.finite_empty, fun z _ _ _ => ?_⟩
  simp

theorem IsHalfPlaneRational.add {f g : ℂ → ℂ}
    (hf : IsHalfPlaneRational f) (hg : IsHalfPlaneRational g) :
    IsHalfPlaneRational (fun z => f z + g z) := by
  obtain ⟨P₁, Q₁, T₁, hQ₁, hT₁, h₁⟩ := hf
  obtain ⟨P₂, Q₂, T₂, hQ₂, hT₂, h₂⟩ := hg
  refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, T₁ ∪ T₂, mul_ne_zero hQ₁ hQ₂, hT₁.union hT₂,
    fun z hz hzT hQz => ?_⟩
  simp only [Set.mem_union, not_or] at hzT
  simp only [Polynomial.eval_mul] at hQz
  have hQ₁z : Q₁.eval z ≠ 0 := fun h0 => hQz (by rw [h0]; ring)
  have hQ₂z : Q₂.eval z ≠ 0 := fun h0 => hQz (by rw [h0]; ring)
  show f z + g z = _
  rw [h₁ z hz hzT.1 hQ₁z, h₂ z hz hzT.2 hQ₂z]
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  field_simp

theorem IsHalfPlaneRational.sub {f g : ℂ → ℂ}
    (hf : IsHalfPlaneRational f) (hg : IsHalfPlaneRational g) :
    IsHalfPlaneRational (fun z => f z - g z) := by
  obtain ⟨P₁, Q₁, T₁, hQ₁, hT₁, h₁⟩ := hf
  obtain ⟨P₂, Q₂, T₂, hQ₂, hT₂, h₂⟩ := hg
  refine ⟨P₁ * Q₂ - P₂ * Q₁, Q₁ * Q₂, T₁ ∪ T₂, mul_ne_zero hQ₁ hQ₂, hT₁.union hT₂,
    fun z hz hzT hQz => ?_⟩
  simp only [Set.mem_union, not_or] at hzT
  simp only [Polynomial.eval_mul] at hQz
  have hQ₁z : Q₁.eval z ≠ 0 := fun h0 => hQz (by rw [h0]; ring)
  have hQ₂z : Q₂.eval z ≠ 0 := fun h0 => hQz (by rw [h0]; ring)
  show f z - g z = _
  rw [h₁ z hz hzT.1 hQ₁z, h₂ z hz hzT.2 hQ₂z]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  field_simp

theorem IsHalfPlaneRational.neg {f : ℂ → ℂ} (hf : IsHalfPlaneRational f) :
    IsHalfPlaneRational (fun z => -f z) := by
  obtain ⟨P, Q, T, hQ, hT, hrel⟩ := hf
  refine ⟨-P, Q, T, hQ, hT, fun z hz hzT hQz => ?_⟩
  show -f z = _
  rw [hrel z hz hzT hQz]
  simp only [Polynomial.eval_neg]
  ring

theorem IsHalfPlaneRational.const_mul {f : ℂ → ℂ} (c : ℂ) (hf : IsHalfPlaneRational f) :
    IsHalfPlaneRational (fun z => c * f z) := by
  obtain ⟨P, Q, T, hQ, hT, hrel⟩ := hf
  refine ⟨C c * P, Q, T, hQ, hT, fun z hz hzT hQz => ?_⟩
  show c * f z = _
  rw [hrel z hz hzT hQz]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem isHalfPlaneRational_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ S, IsHalfPlaneRational (f i)) :
    IsHalfPlaneRational (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isHalfPlaneRational_const 0
  | insert i S hi ih =>
      have hmem : ∀ j ∈ S, IsHalfPlaneRational (f j) := fun j hj =>
        h j (Finset.mem_insert_of_mem hj)
      have hhead : IsHalfPlaneRational (f i) := h i (Finset.mem_insert_self i S)
      have := hhead.add (ih hmem)
      refine this.congr Set.finite_empty (fun z _ _ => ?_)
      rw [Finset.sum_insert hi]

theorem IsHalfPlaneRational.comp_two {f : ℂ → ℂ} (hf : IsHalfPlaneRational f) :
    IsHalfPlaneRational (fun z => f (2 * z)) := by
  classical
  obtain ⟨P, Q, T, hQ, hT, hrel⟩ := hf
  have hev : ∀ (R : Polynomial ℂ) (z : ℂ),
      (R.comp (C 2 * X)).eval z = R.eval (2 * z) := by
    intro R z
    simp [Polynomial.eval_comp]
  have hQ2 : Q.comp (C 2 * X) ≠ 0 := by
    intro h0
    refine hQ (Polynomial.funext fun w => ?_)
    have hz := congrArg (Polynomial.eval (w / 2)) h0
    rw [hev] at hz
    rw [show 2 * (w / 2) = w by ring] at hz
    simpa using hz
  have hTpre : ((fun z : ℂ => 2 * z) ⁻¹' T).Finite := by
    have hinj : Function.Injective (fun z : ℂ => 2 * z) := fun x y hxy => by
      have : (2 : ℂ) * x = 2 * y := hxy
      field_simp at this
      exact this
    exact Set.Finite.preimage hinj.injOn hT
  refine ⟨P.comp (C 2 * X), Q.comp (C 2 * X), (fun z : ℂ => 2 * z) ⁻¹' T, hQ2, hTpre,
    fun z hz hzT hQz => ?_⟩
  show f (2 * z) = _
  rw [hev Q z] at hQz
  rw [hev P z, hev Q z]
  refine hrel (2 * z) ?_ hzT hQz
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
  linarith

/-- **Half-translate digamma independence, half-plane-rational form.** -/
theorem digamma_half_translate_independent_of_halfPlaneRational {E O : ℂ}
    (h : IsHalfPlaneRational
      (fun z => E * Complex.digamma z + O * Complex.digamma (z + 1 / 2))) :
    E = 0 ∧ O = 0 := by
  obtain ⟨P, Q, T, hQ, hT, hrel⟩ := h
  exact digamma_half_translate_independent_of_quotient hQ hT hrel

/-- **Independence of the two archimedean digamma modes.** The combination
`E·ψ(s/2) + O·ψ((s+1)/2)` is half-plane rational only when both coefficients vanish. -/
theorem digamma_parity_modes_independent {E O : ℂ}
    (h : IsHalfPlaneRational
      (fun s => E * Complex.digamma (s / 2) + O * Complex.digamma ((s + 1) / 2))) :
    E = 0 ∧ O = 0 := by
  refine digamma_half_translate_independent_of_halfPlaneRational (E := E) (O := O) ?_
  have h2 := h.comp_two
  refine h2.congr Set.finite_empty (fun z _ _ => ?_)
  rw [show 2 * z / 2 = z by ring, show (2 * z + 1) / 2 = z + 1 / 2 by ring]

end GaloisForLFunctions.HTGeometry
