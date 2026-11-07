import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The parallelogram law of heights

Let `F` be a field of odd characteristic and `h = X³ + a X² + b X + c` a separable cubic over `F`. The twisted curve `h(T) Y² = h(X)` over `K = F(T)` has a group of points, and the height of a point is the degree of its
`X`-coordinate as a rational function of `T`. **The height obeys the exact parallelogram law**

  `ht(P + Q) + ht(P - Q) = 2 ht(P) + 2 ht(Q)`  (`height_parallelogram`).

There is no error term, because the curve is constant. The mechanism has three steps.

* The two numbers `X(P + Q)`, `X(P - Q)` are the roots of a quadratic whose coefficients are explicit biquadratic forms in `X(P)`, `X(Q)` (`crossRelations`): the addition law sees the twist only through the `X`-coordinates.
* The three forms have no common zero on `ℙ¹ × ℙ¹` over any field extension of `F`, since a common zero would be a double root of `h` (`forms_no_common_zero`). So they generate the unit ideal of `F[T]` (`forms_bezout`), and their top coefficients do not all vanish (`forms_top`).
* The product of two primitive linear forms is primitive, by Gauss (`pair_bezout`, `pair_top`). So the two triples of polynomials differ by a nonzero constant (`eq_const_mul_of_cross`), and they have the same maximal degree.

This is the theorem of the cube for `E × E` read on a function field, in the form used by Manin in his elementary proof of Hasse's theorem.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### The three forms -/

section Forms

variable {R : Type*} [CommRing R]

/-- The coefficient `(p₁ r₂ - p₂ r₁)²` of `Z²`. -/
def formA (p₁ r₁ p₂ r₂ : R) : R := (p₁ * r₂ - p₂ * r₁) ^ 2

/-- The coefficient of `-Z`. -/
def formB (a b c p₁ r₁ p₂ r₂ : R) : R :=
  2 * ((p₁ * p₂ + b * (r₁ * r₂)) * (p₁ * r₂ + p₂ * r₁) + 2 * a * (p₁ * p₂) * (r₁ * r₂) +
    2 * c * (r₁ * r₂) ^ 2)

/-- The constant coefficient. -/
def formC (a b c p₁ r₁ p₂ r₂ : R) : R :=
  (p₁ * p₂ - b * (r₁ * r₂)) ^ 2 - 4 * c * (r₁ * r₂) * (p₁ * r₂ + p₂ * r₁ + a * (r₁ * r₂))

end Forms

section NoCommonZero

variable {L : Type*} [Field L]

/-- **The forms have no common zero.** A common zero is a point where `h` and `h'` both vanish. -/
theorem forms_no_common_zero {a b c : L} (h2 : (2 : L) ≠ 0)
    (hsep : ∀ x : L, x ^ 3 + a * x ^ 2 + b * x + c = 0 → 3 * x ^ 2 + 2 * a * x + b ≠ 0)
    {p₁ r₁ p₂ r₂ : L} (h₁ : p₁ ≠ 0 ∨ r₁ ≠ 0) (h₂ : p₂ ≠ 0 ∨ r₂ ≠ 0)
    (hA : formA p₁ r₁ p₂ r₂ = 0) (hB : formB a b c p₁ r₁ p₂ r₂ = 0)
    (hC : formC a b c p₁ r₁ p₂ r₂ = 0) : False := by
  have hdet : p₁ * r₂ = p₂ * r₁ := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hA
    linear_combination this
  by_cases hr₁ : r₁ = 0
  · subst hr₁
    have hp₁ : p₁ ≠ 0 := h₁.resolve_right (by simp)
    have hr₂ : r₂ = 0 := by
      simpa [hp₁] using hdet
    subst hr₂
    have hp₂ : p₂ ≠ 0 := h₂.resolve_right (by simp)
    unfold formC at hC
    simp only [mul_zero, sub_zero, add_zero] at hC
    exact (pow_ne_zero 2 (mul_ne_zero hp₁ hp₂)) (by simpa using hC)
  · by_cases hr₂ : r₂ = 0
    · subst hr₂
      have hp₂ : p₂ ≠ 0 := h₂.resolve_right (by simp)
      have : p₂ * r₁ = 0 := by simpa using hdet.symm
      exact (mul_ne_zero hp₂ hr₁) this
    · set x := p₁ / r₁ with hx
      have hp₁ : p₁ = x * r₁ := by
        rw [hx]
        field_simp
      have hp₂ : p₂ = x * r₂ := by
        have : p₂ * r₁ = x * r₂ * r₁ := by
          rw [← hdet, hp₁]
          ring
        exact mul_right_cancel₀ hr₁ this
      have hrr : (r₁ * r₂) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hr₁ hr₂)
      have hBx : (r₁ * r₂) ^ 2 * (4 * (x ^ 3 + a * x ^ 2 + b * x + c)) = 0 := by
        rw [← hB, formB, hp₁, hp₂]
        ring
      have h4 : (4 : L) ≠ 0 := by
        rw [show (4 : L) = 2 * 2 by norm_num]
        exact mul_ne_zero h2 h2
      have hh : x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
        rcases mul_eq_zero.mp hBx with h | h
        · exact absurd h hrr
        · exact (mul_eq_zero.mp h).resolve_left h4
      have hCx : (r₁ * r₂) ^ 2 * ((x ^ 2 - b) ^ 2 - 4 * c * (2 * x + a)) = 0 := by
        rw [← hC, formC, hp₁, hp₂]
        ring
      have hC0 : (x ^ 2 - b) ^ 2 - 4 * c * (2 * x + a) = 0 :=
        (mul_eq_zero.mp hCx).resolve_left hrr
      have hder : (3 * x ^ 2 + 2 * a * x + b) ^ 2 = 0 := by
        linear_combination hC0 + (8 * x + 4 * a) * hh
      exact hsep x hh (pow_eq_zero_iff two_ne_zero |>.mp hder)

end NoCommonZero

/-! ### Top coefficients -/

section Top

variable {F : Type*} [Field F]

/-- `f` has degree at most `n`, and `α` is its coefficient at `n`. -/
def Top (f : F[X]) (n : ℕ) (α : F) : Prop := f.natDegree ≤ n ∧ f.coeff n = α

theorem Top.add {f g : F[X]} {n : ℕ} {α β : F} (hf : Top f n α) (hg : Top g n β) :
    Top (f + g) n (α + β) :=
  ⟨(natDegree_add_le _ _).trans (max_le hf.1 hg.1), by rw [coeff_add, hf.2, hg.2]⟩

theorem Top.sub {f g : F[X]} {n : ℕ} {α β : F} (hf : Top f n α) (hg : Top g n β) :
    Top (f - g) n (α - β) :=
  ⟨(natDegree_sub_le _ _).trans (max_le hf.1 hg.1), by rw [coeff_sub, hf.2, hg.2]⟩

theorem Top.mul {f g : F[X]} {m n k : ℕ} {α β : F} (hf : Top f m α) (hg : Top g n β) (hk : m + n = k) :
    Top (f * g) k (α * β) := by
  subst hk
  refine ⟨natDegree_mul_le.trans (add_le_add hf.1 hg.1), ?_⟩
  rw [coeff_mul_add_eq_of_natDegree_le hf.1 hg.1, hf.2, hg.2]

theorem Top.const (a : F) : Top (C a) 0 a := ⟨by simp, by simp⟩

theorem Top.ofNat2 : Top (2 : F[X]) 0 2 := by
  have h := Top.const (2 : F)
  rwa [map_ofNat] at h

theorem Top.ofNat4 : Top (4 : F[X]) 0 4 := by
  have h := Top.const (4 : F)
  rwa [map_ofNat] at h

theorem Top.congr_deg {f : F[X]} {m n : ℕ} {α : F} (hf : Top f m α) (h : m = n) : Top f n α := h ▸ hf

/-- The degree of the pair. -/
def pairDeg (p r : F[X]) : ℕ := max p.natDegree r.natDegree

theorem top_pair_left (p r : F[X]) : Top p (pairDeg p r) (p.coeff (pairDeg p r)) :=
  ⟨le_max_left _ _, rfl⟩

theorem top_pair_right (p r : F[X]) : Top r (pairDeg p r) (r.coeff (pairDeg p r)) :=
  ⟨le_max_right _ _, rfl⟩

/-- The pair of top coefficients of a nonzero pair is nonzero. -/
theorem top_pair_ne_zero {p r : F[X]} (h : p ≠ 0 ∨ r ≠ 0) :
    p.coeff (pairDeg p r) ≠ 0 ∨ r.coeff (pairDeg p r) ≠ 0 := by
  unfold pairDeg
  rcases le_total p.natDegree r.natDegree with hle | hle
  · rw [max_eq_right hle]
    by_cases hr : r = 0
    · subst hr
      have hp : p ≠ 0 := h.resolve_right (by simp)
      have hd : p.natDegree = 0 := by simpa using hle
      have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
      rw [leadingCoeff, hd] at hl
      left
      simpa using hl
    · right
      simpa [coeff_natDegree] using hr
  · rw [max_eq_left hle]
    by_cases hp : p = 0
    · subst hp
      have hr : r ≠ 0 := h.resolve_left (by simp)
      have hd : r.natDegree = 0 := by simpa using hle
      have hl : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr
      rw [leadingCoeff, hd] at hl
      right
      simpa using hl
    · left
      simpa [coeff_natDegree] using hp

/-- Three polynomials with degree at most `n`, one of whose top coefficients is nonzero. -/
def maxDeg (A B D : F[X]) : ℕ := max A.natDegree (max B.natDegree D.natDegree)

theorem maxDeg_eq_of_top {A B D : F[X]} {n : ℕ} {α β δ : F} (hA : Top A n α) (hB : Top B n β)
    (hD : Top D n δ) (h : α ≠ 0 ∨ β ≠ 0 ∨ δ ≠ 0) : maxDeg A B D = n := by
  apply le_antisymm (max_le hA.1 (max_le hB.1 hD.1))
  rcases h with h | h | h
  · have : n ≤ A.natDegree := le_natDegree_of_ne_zero (by rwa [hA.2])
    exact this.trans (le_max_left _ _)
  · have : n ≤ B.natDegree := le_natDegree_of_ne_zero (by rwa [hB.2])
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have : n ≤ D.natDegree := le_natDegree_of_ne_zero (by rwa [hD.2])
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

end Top

/-! ### Bezout -/

section Bezout

variable {F : Type*} [Field F]

/-- If no maximal ideal contains three polynomials, they generate the unit ideal. -/
theorem bezout_of_maximal {A B D : F[X]}
    (h : ∀ m : Ideal F[X], m.IsMaximal → ¬ (A ∈ m ∧ B ∈ m ∧ D ∈ m)) :
    ∃ x y z : F[X], x * A + y * B + z * D = 1 := by
  set I : Ideal F[X] := Ideal.span {A, B, D} with hI
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    exact h m hm ⟨hle (Ideal.subset_span (by simp)), hle (Ideal.subset_span (by simp)),
      hle (Ideal.subset_span (by simp))⟩
  have h1 : (1 : F[X]) ∈ I := by
    rw [htop]
    trivial
  rw [hI, Ideal.mem_span_insert] at h1
  obtain ⟨x, w, hw, hw1⟩ := h1
  rw [Ideal.mem_span_pair] at hw
  obtain ⟨y, z, rfl⟩ := hw
  exact ⟨x, y, z, by rw [hw1]; ring⟩

/-- A coprime pair is a nonzero vector modulo every maximal ideal. -/
theorem coprime_mod_ne {p r : F[X]} (h : IsCoprime p r) (m : Ideal F[X]) [m.IsMaximal] :
    Ideal.Quotient.mk m p ≠ 0 ∨ Ideal.Quotient.mk m r ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Ideal.Quotient.mk m) huv
  rw [map_add, map_mul, map_mul, hcon.1, hcon.2, mul_zero, mul_zero, add_zero, map_one] at h1
  exact zero_ne_one h1

/-- **Gauss: the product of two primitive linear forms is primitive.** -/
theorem pair_bezout {u₁ v₁ u₂ v₂ : F[X]} (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) :
    ∃ x y z : F[X], x * (v₁ * v₂) + y * (u₁ * v₂ + u₂ * v₁) + z * (u₁ * u₂) = 1 := by
  refine bezout_of_maximal fun m hm hall => ?_
  letI : Field (F[X] ⧸ m) := Ideal.Quotient.field m
  obtain ⟨h1, h2, h3⟩ := hall
  have e1 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have e2 := Ideal.Quotient.eq_zero_iff_mem.mpr h2
  have e3 := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  simp only [map_add, map_mul] at e1 e2 e3
  have c1 := coprime_mod_ne h₁ m
  have c2 := coprime_mod_ne h₂ m
  generalize Ideal.Quotient.mk m u₁ = a₁ at *
  generalize Ideal.Quotient.mk m v₁ = b₁ at *
  generalize Ideal.Quotient.mk m u₂ = a₂ at *
  generalize Ideal.Quotient.mk m v₂ = b₂ at *
  rcases mul_eq_zero.mp e1 with hb | hb
  · subst hb
    have ha₁ : a₁ ≠ 0 := c1.resolve_right (by simp)
    have hb₂ : b₂ = 0 := by simpa [ha₁] using e2
    have ha₂ : a₂ = 0 := by simpa [ha₁] using e3
    subst hb₂ ha₂
    simp at c2
  · subst hb
    have ha₂ : a₂ ≠ 0 := c2.resolve_right (by simp)
    have hb₁ : b₁ = 0 := by simpa [ha₂] using e2
    have ha₁ : a₁ = 0 := by simpa [ha₂] using e3
    subst hb₁ ha₁
    simp at c1

/-- The same at the place at infinity. -/
theorem pair_top {u₁ v₁ u₂ v₂ : F[X]} (h₁ : u₁ ≠ 0 ∨ v₁ ≠ 0) (h₂ : u₂ ≠ 0 ∨ v₂ ≠ 0) :
    maxDeg (v₁ * v₂) (u₁ * v₂ + u₂ * v₁) (u₁ * u₂) = pairDeg u₁ v₁ + pairDeg u₂ v₂ := by
  set d₁ := pairDeg u₁ v₁
  set d₂ := pairDeg u₂ v₂
  have tu₁ : Top u₁ d₁ _ := top_pair_left u₁ v₁
  have tv₁ : Top v₁ d₁ _ := top_pair_right u₁ v₁
  have tu₂ : Top u₂ d₂ _ := top_pair_left u₂ v₂
  have tv₂ : Top v₂ d₂ _ := top_pair_right u₂ v₂
  have c1 := top_pair_ne_zero h₁
  have c2 := top_pair_ne_zero h₂
  refine maxDeg_eq_of_top (tv₁.mul tv₂ rfl)
    ((tu₁.mul tv₂ rfl).add (tu₂.mul tv₁ (add_comm _ _))) (tu₁.mul tu₂ rfl) ?_
  generalize u₁.coeff (pairDeg u₁ v₁) = a₁ at *
  generalize v₁.coeff (pairDeg u₁ v₁) = b₁ at *
  generalize u₂.coeff (pairDeg u₂ v₂) = a₂ at *
  generalize v₂.coeff (pairDeg u₂ v₂) = b₂ at *
  by_contra hcon
  rw [not_or, not_or, not_not, not_not, not_not] at hcon
  obtain ⟨e1, e2, e3⟩ := hcon
  rcases mul_eq_zero.mp e1 with hb | hb
  · subst hb
    have ha₁ : a₁ ≠ 0 := c1.resolve_right (by simp)
    have hb₂ : b₂ = 0 := by simpa [ha₁] using e2
    have ha₂ : a₂ = 0 := by simpa [ha₁] using e3
    subst hb₂ ha₂
    simp at c2
  · subst hb
    have ha₂ : a₂ ≠ 0 := c2.resolve_right (by simp)
    have hb₁ : b₁ = 0 := by simpa [ha₂] using e2
    have ha₁ : a₁ = 0 := by simpa [ha₂] using e3
    subst hb₁ ha₁
    simp at c1

/-- **Two primitive proportional triples differ by a nonzero constant.** -/
theorem eq_const_mul_of_cross {A B D a₀ a₁ a₂ : F[X]}
    (hb : ∃ x y z : F[X], x * A + y * B + z * D = 1)
    (hb' : ∃ x y z : F[X], x * a₀ + y * a₁ + z * a₂ = 1)
    (h1 : A * a₁ = B * a₀) (h2 : A * a₂ = D * a₀) (h3 : B * a₂ = D * a₁) :
    ∃ c : F, c ≠ 0 ∧ A = C c * a₀ ∧ B = C c * a₁ ∧ D = C c * a₂ := by
  obtain ⟨x, y, z, h⟩ := hb
  obtain ⟨x', y', z', h'⟩ := hb'
  set w := x' * A + y' * B + z' * D with hw
  have eA : A = w * a₀ := by
    have : A = A * (x' * a₀ + y' * a₁ + z' * a₂) := by rw [h', mul_one]
    rw [this, hw]
    linear_combination y' * h1 + z' * h2
  have eB : B = w * a₁ := by
    have : B = B * (x' * a₀ + y' * a₁ + z' * a₂) := by rw [h', mul_one]
    rw [this, hw]
    linear_combination -x' * h1 + z' * h3
  have eD : D = w * a₂ := by
    have : D = D * (x' * a₀ + y' * a₁ + z' * a₂) := by rw [h', mul_one]
    rw [this, hw]
    linear_combination -x' * h2 - y' * h3
  have hunit : IsUnit w := by
    refine IsUnit.of_mul_eq_one (x * a₀ + y * a₁ + z * a₂) ?_
    calc w * (x * a₀ + y * a₁ + z * a₂) = x * (w * a₀) + y * (w * a₁) + z * (w * a₂) := by ring
      _ = 1 := by rw [← eA, ← eB, ← eD, h]
  obtain ⟨c, hc, hwc⟩ := Polynomial.isUnit_iff.mp hunit
  refine ⟨c, hc.ne_zero, ?_, ?_, ?_⟩
  · rw [hwc]; exact eA
  · rw [hwc]; exact eB
  · rw [hwc]; exact eD

theorem maxDeg_const_mul {A B D : F[X]} {c : F} (hc : c ≠ 0) :
    maxDeg (C c * A) (C c * B) (C c * D) = maxDeg A B D := by
  unfold maxDeg
  rw [natDegree_C_mul hc, natDegree_C_mul hc, natDegree_C_mul hc]

end Bezout

/-! ### The forms over `F[T]` -/

section FormsPoly

variable {F : Type*} [Field F] {a b c : F}

/-- The separable cubic. -/
def cubicPoly (a b c : F) : F[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c

theorem derivative_cubicPoly (a b c : F) :
    derivative (cubicPoly a b c) = C 3 * X ^ 2 + C 2 * C a * X + C b := by
  unfold cubicPoly
  simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X, zero_mul,
    mul_one, zero_add, add_zero]
  simp only [map_ofNat, Nat.cast_ofNat]
  ring

/-- The cubic has no double root in any extension of `F`. -/
theorem cubic_sep {L : Type*} [Field L] (ι : F →+* L)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c)))
    (x : L) (hx : x ^ 3 + ι a * x ^ 2 + ι b * x + ι c = 0) :
    3 * x ^ 2 + 2 * ι a * x + ι b ≠ 0 := by
  intro hd
  obtain ⟨u, v, huv⟩ := hcop
  have h1 := congrArg (eval₂ ι x) huv
  have e1 : eval₂ ι x (cubicPoly a b c) = x ^ 3 + ι a * x ^ 2 + ι b * x + ι c := by
    simp [cubicPoly, eval₂_add, eval₂_mul, eval₂_pow]
  have e2 : eval₂ ι x (derivative (cubicPoly a b c)) = 3 * x ^ 2 + 2 * ι a * x + ι b := by
    rw [derivative_cubicPoly]
    simp [eval₂_add, eval₂_mul, eval₂_pow, map_ofNat]
  rw [eval₂_add, eval₂_mul, eval₂_mul, e1, e2, hx, hd, mul_zero, mul_zero, add_zero, eval₂_one] at h1
  exact zero_ne_one h1

theorem map_formA {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p₁ r₁ p₂ r₂ : R) :
    f (formA p₁ r₁ p₂ r₂) = formA (f p₁) (f r₁) (f p₂) (f r₂) := by
  simp [formA]

theorem map_formB {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c p₁ r₁ p₂ r₂ : R) :
    f (formB a b c p₁ r₁ p₂ r₂) = formB (f a) (f b) (f c) (f p₁) (f r₁) (f p₂) (f r₂) := by
  simp [formB, map_ofNat]

theorem map_formC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c p₁ r₁ p₂ r₂ : R) :
    f (formC a b c p₁ r₁ p₂ r₂) = formC (f a) (f b) (f c) (f p₁) (f r₁) (f p₂) (f r₂) := by
  simp [formC, map_ofNat]

/-- **The three forms generate the unit ideal of `F[T]`.** -/
theorem forms_bezout (h2 : (2 : F) ≠ 0) (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c)))
    {p₁ r₁ p₂ r₂ : F[X]} (h₁ : IsCoprime p₁ r₁) (h₂ : IsCoprime p₂ r₂) :
    ∃ x y z : F[X], x * formA p₁ r₁ p₂ r₂ + y * formB (C a) (C b) (C c) p₁ r₁ p₂ r₂ +
      z * formC (C a) (C b) (C c) p₁ r₁ p₂ r₂ = 1 := by
  refine bezout_of_maximal fun m hm hall => ?_
  obtain ⟨hA, hB, hD⟩ := hall
  let φ := Ideal.Quotient.mk m
  have eA : formA (φ p₁) (φ r₁) (φ p₂) (φ r₂) = 0 := by
    rw [← map_formA]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hA
  have eB : formB (φ (C a)) (φ (C b)) (φ (C c)) (φ p₁) (φ r₁) (φ p₂) (φ r₂) = 0 := by
    rw [← map_formB]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hB
  have eD : formC (φ (C a)) (φ (C b)) (φ (C c)) (φ p₁) (φ r₁) (φ p₂) (φ r₂) = 0 := by
    rw [← map_formC]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hD
  have c1 := coprime_mod_ne h₁ m
  have c2 := coprime_mod_ne h₂ m
  letI hL : Field (F[X] ⧸ m) := Ideal.Quotient.field m
  let ι : F →+* (F[X] ⧸ m) := φ.comp C
  have h2' : (2 : F[X] ⧸ m) ≠ 0 := by
    have h0 : ι 2 ≠ 0 := (map_ne_zero ι).mpr h2
    rwa [map_ofNat] at h0
  refine forms_no_common_zero h2' (a := ι a) (b := ι b) (c := ι c) ?_ c1 c2 eA eB eD
  intro x hx
  exact cubic_sep ι hcop x hx

/-- **The three forms lose no degree at infinity.** -/
theorem forms_top (h2 : (2 : F) ≠ 0) (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c)))
    {p₁ r₁ p₂ r₂ : F[X]} (h₁ : p₁ ≠ 0 ∨ r₁ ≠ 0) (h₂ : p₂ ≠ 0 ∨ r₂ ≠ 0) :
    maxDeg (formA p₁ r₁ p₂ r₂) (formB (C a) (C b) (C c) p₁ r₁ p₂ r₂)
      (formC (C a) (C b) (C c) p₁ r₁ p₂ r₂) = 2 * pairDeg p₁ r₁ + 2 * pairDeg p₂ r₂ := by
  set d₁ := pairDeg p₁ r₁
  set d₂ := pairDeg p₂ r₂
  have tp₁ : Top p₁ d₁ _ := top_pair_left p₁ r₁
  have tr₁ : Top r₁ d₁ _ := top_pair_right p₁ r₁
  have tp₂ : Top p₂ d₂ _ := top_pair_left p₂ r₂
  have tr₂ : Top r₂ d₂ _ := top_pair_right p₂ r₂
  have c1 := top_pair_ne_zero h₁
  have c2 := top_pair_ne_zero h₂
  set α₁ := p₁.coeff (pairDeg p₁ r₁)
  set β₁ := r₁.coeff (pairDeg p₁ r₁)
  set α₂ := p₂.coeff (pairDeg p₂ r₂)
  set β₂ := r₂.coeff (pairDeg p₂ r₂)
  have tpp : Top (p₁ * p₂) (d₁ + d₂) (α₁ * α₂) := tp₁.mul tp₂ rfl
  have trr : Top (r₁ * r₂) (d₁ + d₂) (β₁ * β₂) := tr₁.mul tr₂ rfl
  have t12 : Top (p₁ * r₂) (d₁ + d₂) (α₁ * β₂) := tp₁.mul tr₂ rfl
  have t21 : Top (p₂ * r₁) (d₁ + d₂) (α₂ * β₁) := tp₂.mul tr₁ (add_comm _ _)
  have hdeg : 2 * d₁ + 2 * d₂ = (d₁ + d₂) + (d₁ + d₂) := by ring
  have tA : Top (formA p₁ r₁ p₂ r₂) (2 * d₁ + 2 * d₂) ((α₁ * β₂ - α₂ * β₁) ^ 2) := by
    unfold formA
    rw [pow_two, pow_two]
    exact (t12.sub t21).mul (t12.sub t21) hdeg.symm
  have tbrr : Top (C b * (r₁ * r₂)) (d₁ + d₂) (b * (β₁ * β₂)) := (Top.const b).mul trr (zero_add _)
  have tarr : Top (C a * (r₁ * r₂)) (d₁ + d₂) (a * (β₁ * β₂)) := (Top.const a).mul trr (zero_add _)
  have tB : Top (formB (C a) (C b) (C c) p₁ r₁ p₂ r₂) (2 * d₁ + 2 * d₂)
      (formB a b c α₁ β₁ α₂ β₂) := by
    unfold formB
    have s1 := (tpp.add tbrr).mul (t12.add t21) hdeg.symm
    have s2 : Top (2 * C a * (p₁ * p₂) * (r₁ * r₂)) (2 * d₁ + 2 * d₂) (2 * a * (α₁ * α₂) * (β₁ * β₂)) :=
      ((Top.ofNat2.mul (Top.const a) rfl).mul tpp (by simp)).mul trr hdeg.symm
    have s3 : Top (2 * C c * (r₁ * r₂) ^ 2) (2 * d₁ + 2 * d₂) (2 * c * (β₁ * β₂) ^ 2) := by
      rw [pow_two, pow_two]
      exact (Top.ofNat2.mul (Top.const c) rfl).mul (trr.mul trr rfl) (by rw [hdeg]; simp)
    exact Top.ofNat2.mul ((s1.add s2).add s3) (by simp)
  have tD : Top (formC (C a) (C b) (C c) p₁ r₁ p₂ r₂) (2 * d₁ + 2 * d₂)
      (formC a b c α₁ β₁ α₂ β₂) := by
    unfold formC
    have s1 : Top ((p₁ * p₂ - C b * (r₁ * r₂)) ^ 2) (2 * d₁ + 2 * d₂) ((α₁ * α₂ - b * (β₁ * β₂)) ^ 2) := by
      rw [pow_two, pow_two]
      exact (tpp.sub tbrr).mul (tpp.sub tbrr) hdeg.symm
    have s2 : Top (4 * C c * (r₁ * r₂) * (p₁ * r₂ + p₂ * r₁ + C a * (r₁ * r₂))) (2 * d₁ + 2 * d₂)
        (4 * c * (β₁ * β₂) * (α₁ * β₂ + α₂ * β₁ + a * (β₁ * β₂))) :=
      ((Top.ofNat4.mul (Top.const c) rfl).mul trr (by simp)).mul ((t12.add t21).add tarr) hdeg.symm
    exact s1.sub s2
  refine maxDeg_eq_of_top tA tB tD ?_
  by_contra hcon
  rw [not_or, not_or, not_not, not_not, not_not] at hcon
  obtain ⟨e1, e2, e3⟩ := hcon
  refine forms_no_common_zero h2 ?_ c1 c2 e1 e2 e3
  intro x hx
  exact cubic_sep (RingHom.id F) hcop x hx

end FormsPoly

/-! ### The addition law through the `X`-coordinates -/

section AdditionLaw

variable {L : Type*} [Field L] [DecidableEq L]

/-- The curve `Y² = X³ + α D X² + β D² X + γ D³`: the twist of `h(X) = X³ + α X² + β X + γ` by `D`. -/
def twistCurveOf (α β γ D : L) : WeierstrassCurve L := ⟨0, α * D, 0, β * D ^ 2, γ * D ^ 3⟩

variable {α β γ D : L}

omit [DecidableEq L] in
theorem twist_equation {x y : L} :
    (twistCurveOf α β γ D).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 + α * D * x ^ 2 + β * D ^ 2 * x + γ * D ^ 3 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [twistCurveOf]

omit [DecidableEq L] in
theorem twist_negY (x y : L) : (twistCurveOf α β γ D).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, twistCurveOf]

/-- **The sum and the product of `X(P + Q)` and `X(P - Q)`.** They depend on `X(P)`, `X(Q)` only. -/
theorem sum_product_of_X_ne (hD : D ≠ 0) {x₁ y₁ x₂ y₂ : L}
    (h₁ : (twistCurveOf α β γ D).toAffine.Equation x₁ y₁)
    (h₂ : (twistCurveOf α β γ D).toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    let W := (twistCurveOf α β γ D).toAffine
    let Z₁ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) / D
    let Z₂ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) / D
    (x₁ / D - x₂ / D) ^ 2 * (Z₁ + Z₂) = formB α β γ (x₁ / D) 1 (x₂ / D) 1 ∧
      (x₁ / D - x₂ / D) ^ 2 * (Z₁ * Z₂) = formC α β γ (x₁ / D) 1 (x₂ / D) 1 := by
  intro W Z₁ Z₂
  rw [twist_equation] at h₁ h₂
  obtain ⟨X₁, rfl⟩ : ∃ X₁, x₁ = D * X₁ := ⟨x₁ / D, by field_simp⟩
  obtain ⟨X₂, rfl⟩ : ∃ X₂, x₂ = D * X₂ := ⟨x₂ / D, by field_simp⟩
  have hδ : X₁ - X₂ ≠ 0 := sub_ne_zero.mpr fun h => hx (by rw [h])
  have hxd : D * X₁ - D * X₂ ≠ 0 := by
    rw [← mul_sub]
    exact mul_ne_zero hD hδ
  have hX₁ : D * X₁ / D = X₁ := by field_simp
  have hX₂ : D * X₂ / D = X₂ := by field_simp
  have hs₁ : W.slope (D * X₁) (D * X₂) y₁ y₂ = (y₁ - y₂) / (D * X₁ - D * X₂) :=
    WeierstrassCurve.Affine.slope_of_X_ne hx
  have hs₂ : W.slope (D * X₁) (D * X₂) y₁ (W.negY (D * X₂) y₂) =
      (y₁ - W.negY (D * X₂) y₂) / (D * X₁ - D * X₂) :=
    WeierstrassCurve.Affine.slope_of_X_ne hx
  have hneg : W.negY (D * X₂) y₂ = -y₂ := twist_negY _ _
  have hZ₁ : Z₁ = (y₁ - y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂) := by
    simp only [Z₁, W, WeierstrassCurve.Affine.addX]
    rw [hs₁]
    simp only [twistCurveOf]
    field_simp
    ring
  have hZ₂ : Z₂ = (y₁ + y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂) := by
    simp only [Z₂, W, WeierstrassCurve.Affine.addX]
    rw [hs₂, hneg]
    simp only [twistCurveOf]
    field_simp
    ring
  have hy₁ : y₁ ^ 2 = D ^ 3 * (X₁ ^ 3 + α * X₁ ^ 2 + β * X₁ + γ) := by
    rw [h₁]
    ring
  have hy₂ : y₂ ^ 2 = D ^ 3 * (X₂ ^ 3 + α * X₂ ^ 2 + β * X₂ + γ) := by
    rw [h₂]
    ring
  set h₁' := X₁ ^ 3 + α * X₁ ^ 2 + β * X₁ + γ with hh₁
  set h₂' := X₂ ^ 3 + α * X₂ ^ 2 + β * X₂ + γ with hh₂
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have eP : (y₁ - y₂) ^ 2 * (y₁ + y₂) ^ 2 = D ^ 6 * (h₁' - h₂') ^ 2 := by
    have : (y₁ - y₂) ^ 2 * (y₁ + y₂) ^ 2 = (y₁ ^ 2 - y₂ ^ 2) ^ 2 := by ring
    rw [this, hy₁, hy₂]
    ring
  have eS : (y₁ - y₂) ^ 2 + (y₁ + y₂) ^ 2 = 2 * (D ^ 3 * (h₁' + h₂')) := by
    linear_combination 2 * hy₁ + 2 * hy₂
  rw [hZ₁, hZ₂, hX₁, hX₂]
  constructor
  · have e : (X₁ - X₂) ^ 2 * ((y₁ - y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂) +
        ((y₁ + y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂))) =
        ((y₁ - y₂) ^ 2 + (y₁ + y₂) ^ 2) / D ^ 3 - 2 * (α + X₁ + X₂) * (X₁ - X₂) ^ 2 := by
      field_simp
      ring
    rw [e, eS]
    unfold formB
    rw [hh₁, hh₂]
    field_simp
    ring
  · have e : (X₁ - X₂) ^ 2 * (((y₁ - y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂)) *
        ((y₁ + y₂) ^ 2 / (D ^ 3 * (X₁ - X₂) ^ 2) - (α + X₁ + X₂))) =
        ((y₁ - y₂) ^ 2 * (y₁ + y₂) ^ 2) / (D ^ 6 * (X₁ - X₂) ^ 2) -
          (α + X₁ + X₂) * (((y₁ - y₂) ^ 2 + (y₁ + y₂) ^ 2) / D ^ 3) +
          (α + X₁ + X₂) ^ 2 * (X₁ - X₂) ^ 2 := by
      field_simp
      ring
    rw [e, eP, eS]
    unfold formC
    have hfac : h₁' - h₂' = (X₁ - X₂) * (X₁ ^ 2 + X₁ * X₂ + X₂ ^ 2 + α * (X₁ + X₂) + β) := by
      rw [hh₁, hh₂]
      ring
    rw [hfac, hh₁, hh₂]
    field_simp
    ring

/-- **The duplication formula through the `X`-coordinate.** -/
theorem double_of_Y_ne (h2 : (2 : L) ≠ 0) (hD : D ≠ 0) {x y : L}
    (h : (twistCurveOf α β γ D).toAffine.Equation x y) (hy : y ≠ 0) :
    let W := (twistCurveOf α β γ D).toAffine
    let Z := W.addX x x (W.slope x x y y) / D
    formB α β γ (x / D) 1 (x / D) 1 * Z = formC α β γ (x / D) 1 (x / D) 1 := by
  intro W Z
  rw [twist_equation] at h
  obtain ⟨X, rfl⟩ : ∃ X, x = D * X := ⟨x / D, by field_simp⟩
  have hXd : D * X / D = X := by field_simp
  have hyne : y ≠ W.negY (D * X) y := by
    have hn : W.negY (D * X) y = -y := twist_negY _ _
    rw [hn]
    intro he
    have h0 : 2 * y = 0 := by linear_combination he
    exact (mul_ne_zero h2 hy) h0
  have hs : W.slope (D * X) (D * X) y y =
      (3 * (D * X) ^ 2 + 2 * (α * D) * (D * X) + β * D ^ 2 - 0 * y) / (y - W.negY (D * X) y) :=
    WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne
  have hn : W.negY (D * X) y = -y := twist_negY _ _
  have hy2 : y ^ 2 = D ^ 3 * (X ^ 3 + α * X ^ 2 + β * X + γ) := by
    rw [h]
    ring
  have hZ : Z = (3 * X ^ 2 + 2 * α * X + β) ^ 2 * D ^ 3 / (4 * y ^ 2) - α - 2 * X := by
    simp only [Z, W, WeierstrassCurve.Affine.addX]
    rw [hs, hn]
    simp only [twistCurveOf]
    field_simp
    ring
  rw [hXd, hZ, hy2]
  have hh : X ^ 3 + α * X ^ 2 + β * X + γ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy2
    exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)
  have h4 : (4 : L) ≠ 0 := by
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hB : formB α β γ X 1 X 1 = 4 * (X ^ 3 + α * X ^ 2 + β * X + γ) := by
    unfold formB
    ring
  have hC : formC α β γ X 1 X 1 = (3 * X ^ 2 + 2 * α * X + β) ^ 2 -
      (8 * X + 4 * α) * (X ^ 3 + α * X ^ 2 + β * X + γ) := by
    unfold formC
    ring
  rw [hB, hC]
  generalize X ^ 3 + α * X ^ 2 + β * X + γ = H at hh
  generalize 3 * X ^ 2 + 2 * α * X + β = E
  field_simp
  ring

end AdditionLaw

/-! ### The twisted curve over `F(T)` -/

section Twist

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] (a b c : F)

local notation "cast" => algebraMap F[X] (RatFunc F)

/-- `h(T)`, as an element of `F(T)`. -/
def twistD : RatFunc F := cast (cubicPoly a b c)

/-- **The twisted curve** `h(T) Y² = h(X)`, in Weierstrass form, with `x = h(T) X`. -/
def twistCurve : WeierstrassCurve (RatFunc F) :=
  twistCurveOf (cast (C a)) (cast (C b)) (cast (C c)) (twistD a b c)

/-- The `X`-coordinate of a point, as a primitive pair of polynomials. The origin is `(1, 0)`. -/
def xPair : (twistCurve a b c).toAffine.Point → F[X] × F[X]
  | .zero => (1, 0)
  | .some x _ _ => (RatFunc.num (x / twistD a b c), RatFunc.denom (x / twistD a b c))

/-- **The height of a point**: the degree of its `X`-coordinate. -/
def height (P : (twistCurve a b c).toAffine.Point) : ℕ := pairDeg (xPair a b c P).1 (xPair a b c P).2

variable {a b c}

theorem twistD_ne_zero : twistD a b c ≠ 0 := by
  unfold twistD
  rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
  intro h
  have hm : (cubicPoly a b c).Monic := by
    unfold cubicPoly
    monicity!
  exact hm.ne_zero h

theorem xPair_coprime (P : (twistCurve a b c).toAffine.Point) :
    IsCoprime (xPair a b c P).1 (xPair a b c P).2 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact isCoprime_one_left
  · exact RatFunc.isCoprime_num_denom _

theorem xPair_ne (P : (twistCurve a b c).toAffine.Point) :
    (xPair a b c P).1 ≠ 0 ∨ (xPair a b c P).2 ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨u, v, huv⟩ := xPair_coprime P
  rw [hcon.1, hcon.2] at huv
  simp at huv

theorem xPair_neg (P : (twistCurve a b c).toAffine.Point) : xPair a b c (-P) = xPair a b c P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem height_neg (P : (twistCurve a b c).toAffine.Point) : height a b c (-P) = height a b c P := by
  unfold height
  rw [xPair_neg]

/-- The relation between the pair and the coordinate. -/
theorem cast_num_eq (X : RatFunc F) : cast (RatFunc.num X) = X * cast (RatFunc.denom X) := by
  have h := RatFunc.num_div_denom X
  have hd : cast (RatFunc.denom X) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
    exact RatFunc.denom_ne_zero X
  rw [div_eq_iff hd] at h
  exact h

theorem cast_denom_ne (X : RatFunc F) : cast (RatFunc.denom X) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
  exact RatFunc.denom_ne_zero X

/-- The three forms are homogeneous of bidegree `(2, 2)`. -/
theorem formA_scale {L : Type*} [Field L] (X₁ X₂ r₁ r₂ : L) :
    formA (X₁ * r₁) r₁ (X₂ * r₂) r₂ = (r₁ * r₂) ^ 2 * formA X₁ 1 X₂ 1 := by
  unfold formA
  ring

theorem formB_scale {L : Type*} [Field L] (α β γ X₁ X₂ r₁ r₂ : L) :
    formB α β γ (X₁ * r₁) r₁ (X₂ * r₂) r₂ = (r₁ * r₂) ^ 2 * formB α β γ X₁ 1 X₂ 1 := by
  unfold formB
  ring

theorem formC_scale {L : Type*} [Field L] (α β γ X₁ X₂ r₁ r₂ : L) :
    formC α β γ (X₁ * r₁) r₁ (X₂ * r₂) r₂ = (r₁ * r₂) ^ 2 * formC α β γ X₁ 1 X₂ 1 := by
  unfold formC
  ring

/-- The cross relations of two triples. -/
def CrossRel (t s : F[X] × F[X] × F[X]) : Prop :=
  t.1 * s.2.1 = t.2.1 * s.1 ∧ t.1 * s.2.2 = t.2.2 * s.1 ∧ t.2.1 * s.2.2 = t.2.2 * s.2.1

/-- The triple of the two points `P`, `Q`. -/
def formTriple (a b c : F) (p₁ r₁ p₂ r₂ : F[X]) : F[X] × F[X] × F[X] :=
  (formA p₁ r₁ p₂ r₂, formB (C a) (C b) (C c) p₁ r₁ p₂ r₂, formC (C a) (C b) (C c) p₁ r₁ p₂ r₂)

/-- The triple of the product of two linear forms. -/
def pairTriple (u₁ v₁ u₂ v₂ : F[X]) : F[X] × F[X] × F[X] :=
  (v₁ * v₂, u₁ * v₂ + u₂ * v₁, u₁ * u₂)

theorem crossRel_of_cast {t s : F[X] × F[X] × F[X]}
    (h1 : cast t.1 * cast s.2.1 = cast t.2.1 * cast s.1)
    (h2 : cast t.1 * cast s.2.2 = cast t.2.2 * cast s.1)
    (h3 : cast t.2.1 * cast s.2.2 = cast t.2.2 * cast s.2.1) : CrossRel t s := by
  refine ⟨RatFunc.algebraMap_injective F ?_, RatFunc.algebraMap_injective F ?_,
    RatFunc.algebraMap_injective F ?_⟩
  · rw [map_mul, map_mul]
    exact h1
  · rw [map_mul, map_mul]
    exact h2
  · rw [map_mul, map_mul]
    exact h3

/-- The cast of the forms at two points with finite coordinates. -/
theorem cast_formTriple (x₁ x₂ : RatFunc F) :
    let X₁ := x₁
    let X₂ := x₂
    let R := (cast (RatFunc.denom X₁) * cast (RatFunc.denom X₂)) ^ 2
    cast (formA (RatFunc.num X₁) (RatFunc.denom X₁) (RatFunc.num X₂) (RatFunc.denom X₂)) =
        R * formA X₁ 1 X₂ 1 ∧
      cast (formB (C a) (C b) (C c) (RatFunc.num X₁) (RatFunc.denom X₁) (RatFunc.num X₂)
        (RatFunc.denom X₂)) = R * formB (cast (C a)) (cast (C b)) (cast (C c)) X₁ 1 X₂ 1 ∧
      cast (formC (C a) (C b) (C c) (RatFunc.num X₁) (RatFunc.denom X₁) (RatFunc.num X₂)
        (RatFunc.denom X₂)) = R * formC (cast (C a)) (cast (C b)) (cast (C c)) X₁ 1 X₂ 1 := by
  intro X₁ X₂ R
  refine ⟨?_, ?_, ?_⟩
  · rw [map_formA, cast_num_eq, cast_num_eq, formA_scale]
  · rw [map_formB, cast_num_eq, cast_num_eq, formB_scale]
  · rw [map_formC, cast_num_eq, cast_num_eq, formC_scale]

/-- With the origin as first point the triple is the square of the second. -/
theorem formTriple_zero_left (p r : F[X]) :
    formTriple a b c 1 0 p r = pairTriple p r p r := by
  simp only [formTriple, pairTriple, formA, formB, formC]
  ext1
  · ring
  · ext1
    · ring
    · ring

theorem formTriple_zero_right (p r : F[X]) :
    formTriple a b c p r 1 0 = pairTriple p r p r := by
  simp only [formTriple, pairTriple, formA, formB, formC]
  ext1
  · ring
  · ext1
    · ring
    · ring

theorem crossRel_self (t : F[X] × F[X] × F[X]) : CrossRel t t := by
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `(2 : F(T)) ≠ 0`. -/
theorem two_ne_zero_ratFunc (h2 : (2 : F) ≠ 0) : (2 : RatFunc F) ≠ 0 := by
  have h : (cast (C (2 : F))) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F), C_eq_zero]
    exact h2
  rwa [map_ofNat, map_ofNat] at h

/-- **Duplication in the triple.** -/
theorem crossRel_double (h2 : (2 : F) ≠ 0) (P : (twistCurve a b c).toAffine.Point)
    (hP : P ≠ 0) :
    CrossRel (formTriple a b c (xPair a b c P).1 (xPair a b c P).2 (xPair a b c P).1 (xPair a b c P).2)
      (pairTriple (xPair a b c (P + P)).1 (xPair a b c (P + P)).2 1 0) := by
  have h2K := two_ne_zero_ratFunc h2
  have hD := twistD_ne_zero (a := a) (b := b) (c := c)
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  set X := x / twistD a b c with hX
  have hcast := cast_formTriple (a := a) (b := b) (c := c) X X
  simp only at hcast
  obtain ⟨cA, cB, cC⟩ := hcast
  have hA0 : formA (RatFunc.num X) (RatFunc.denom X) (RatFunc.num X) (RatFunc.denom X) = 0 := by
    unfold formA
    ring
  have eP : xPair a b c (WeierstrassCurve.Affine.Point.some x y h) = (RatFunc.num X, RatFunc.denom X) := rfl
  rw [eP]
  by_cases hy : y = 0
  · -- a point of order two
    subst hy
    have hneg : (0 : RatFunc F) = (twistCurve a b c).toAffine.negY x 0 := by
      have := twist_negY (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) (D := twistD a b c) x (0 : RatFunc F)
      rw [neg_zero] at this
      exact this.symm
    have hadd : (WeierstrassCurve.Affine.Point.some x 0 h + WeierstrassCurve.Affine.Point.some x 0 h :
        (twistCurve a b c).toAffine.Point) = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hneg
    have e0 : xPair a b c (0 : (twistCurve a b c).toAffine.Point) = (1, 0) := rfl
    rw [hadd, e0]
    have heq := h.1
    have heq' := (twist_equation (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) (D := twistD a b c)).mp heq
    have hh : X ^ 3 + cast (C a) * X ^ 2 + cast (C b) * X + cast (C c) = 0 := by
      have hx : x = twistD a b c * X := by
        rw [hX]
        field_simp
      rw [hx] at heq'
      have h3 : (twistD a b c) ^ 3 ≠ 0 := pow_ne_zero 3 hD
      apply mul_left_cancel₀ h3
      linear_combination -heq'
    have hBzero : formB (C a) (C b) (C c) (RatFunc.num X) (RatFunc.denom X) (RatFunc.num X)
        (RatFunc.denom X) = 0 := by
      apply RatFunc.algebraMap_injective F
      rw [cB, map_zero]
      have : formB (cast (C a)) (cast (C b)) (cast (C c)) X 1 X 1 =
          4 * (X ^ 3 + cast (C a) * X ^ 2 + cast (C b) * X + cast (C c)) := by
        unfold formB
        ring
      rw [this, hh]
      ring
    refine ⟨?_, ?_, ?_⟩
    · simp only [formTriple, pairTriple]
      rw [hA0, hBzero]
      simp
    · simp only [formTriple, pairTriple]
      rw [hA0]
      simp
    · simp only [formTriple, pairTriple]
      rw [hBzero]
      simp
  · -- a point not of order two
    have hyne : y ≠ (twistCurve a b c).toAffine.negY x y := by
      have hn : (twistCurve a b c).toAffine.negY x y = -y :=
        twist_negY (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) (D := twistD a b c) x y
      rw [hn]
      intro he
      have h0 : 2 * y = 0 := by linear_combination he
      exact (mul_ne_zero h2K hy) h0
    have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hyne
    rw [hadd]
    set Z := (twistCurve a b c).toAffine.addX x x ((twistCurve a b c).toAffine.slope x x y y) /
      twistD a b c with hZ
    have hdbl : formB (cast (C a)) (cast (C b)) (cast (C c)) X 1 X 1 * Z =
        formC (cast (C a)) (cast (C b)) (cast (C c)) X 1 X 1 :=
      double_of_Y_ne h2K hD h.1 hy
    have hV := cast_num_eq Z
    refine crossRel_of_cast ?_ ?_ ?_
    · simp only [formTriple, pairTriple]
      rw [hA0]
      simp
    · simp only [formTriple, pairTriple]
      rw [hA0]
      simp
    · simp only [formTriple, pairTriple, xPair]
      rw [cB, cC]
      simp only [map_add, map_mul, map_one, map_zero]
      rw [hV, ← hdbl]
      ring

/-- The cross relations from the sum and the product of the two roots. -/
theorem crossRel_of_values {X₁ X₂ Z₁ Z₂ : RatFunc F}
    (hS : (X₁ - X₂) ^ 2 * (Z₁ + Z₂) = formB (cast (C a)) (cast (C b)) (cast (C c)) X₁ 1 X₂ 1)
    (hPr : (X₁ - X₂) ^ 2 * (Z₁ * Z₂) = formC (cast (C a)) (cast (C b)) (cast (C c)) X₁ 1 X₂ 1) :
    CrossRel (formTriple a b c (RatFunc.num X₁) (RatFunc.denom X₁) (RatFunc.num X₂) (RatFunc.denom X₂))
      (pairTriple (RatFunc.num Z₁) (RatFunc.denom Z₁) (RatFunc.num Z₂) (RatFunc.denom Z₂)) := by
  have hcast := cast_formTriple (a := a) (b := b) (c := c) X₁ X₂
  simp only at hcast
  obtain ⟨cA, cB, cC⟩ := hcast
  have hA1 : formA X₁ 1 X₂ 1 = (X₁ - X₂) ^ 2 := by
    unfold formA
    ring
  have hV₁ := cast_num_eq Z₁
  have hV₂ := cast_num_eq Z₂
  refine crossRel_of_cast ?_ ?_ ?_
  · simp only [formTriple, pairTriple]
    rw [cA, cB, hA1]
    simp only [map_add, map_mul]
    rw [hV₁, hV₂, ← hS]
    ring
  · simp only [formTriple, pairTriple]
    rw [cA, cC, hA1]
    simp only [map_add, map_mul]
    rw [hV₁, hV₂, ← hPr]
    ring
  · simp only [formTriple, pairTriple]
    rw [cB, cC]
    simp only [map_add, map_mul]
    rw [hV₁, hV₂, ← hS, ← hPr]
    ring

/-- **The cross relations**: `X(P + Q)` and `X(P - Q)` are the roots of the quadratic of the three forms at `X(P)`, `X(Q)`. -/
theorem crossRelations (h2 : (2 : F) ≠ 0) (P Q : (twistCurve a b c).toAffine.Point) :
    CrossRel (formTriple a b c (xPair a b c P).1 (xPair a b c P).2 (xPair a b c Q).1 (xPair a b c Q).2)
      (pairTriple (xPair a b c (P + Q)).1 (xPair a b c (P + Q)).2
        (xPair a b c (P - Q)).1 (xPair a b c (P - Q)).2) := by
  have h2K := two_ne_zero_ratFunc h2
  have hD := twistD_ne_zero (a := a) (b := b) (c := c)
  by_cases hP0 : P = 0
  · subst hP0
    rw [zero_add, zero_sub, xPair_neg]
    have e : xPair a b c (0 : (twistCurve a b c).toAffine.Point) = (1, 0) := rfl
    rw [e]
    simp only
    rw [formTriple_zero_left]
    exact crossRel_self _
  by_cases hQ0 : Q = 0
  · subst hQ0
    rw [add_zero, sub_zero]
    have e : xPair a b c (0 : (twistCurve a b c).toAffine.Point) = (1, 0) := rfl
    rw [e]
    simp only
    rw [formTriple_zero_right]
    exact crossRel_self _
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP0
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ0
  by_cases hx : x₁ = x₂
  · subst hx
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
    · subst hy
      rw [sub_self]
      have hd := crossRel_double h2 (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) hP0
      have e : xPair a b c (0 : (twistCurve a b c).toAffine.Point) = (1, 0) := rfl
      rw [e]
      exact hd
    · -- the second point is the opposite of the first
      have hQ : (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ : (twistCurve a b c).toAffine.Point) =
          -WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by
        have hy' : y₂ = (twistCurve a b c).toAffine.negY x₁ y₁ := by
          rw [hy, WeierstrassCurve.Affine.negY_negY]
        subst hy'
        rfl
      rw [hQ, add_neg_cancel, sub_neg_eq_add, xPair_neg]
      have hd := crossRel_double h2 (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) hP0
      have e : xPair a b c (0 : (twistCurve a b c).toAffine.Point) = (1, 0) := rfl
      rw [e]
      obtain ⟨d1, d2, d3⟩ := hd
      simp only [pairTriple, CrossRel] at d1 d2 d3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · linear_combination d1
      · linear_combination d2
      · linear_combination d3
  · -- the general position
    have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
    have hsub : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ - WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        (twistCurve a b c).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ _
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h₂) := by
      rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some]
    have hadd2 := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁)
      (h₂ := (WeierstrassCurve.Affine.nonsingular_neg x₂ y₂).mpr h₂) hx
    rw [hsub, hadd2, hadd]
    obtain ⟨hS, hPr⟩ := sum_product_of_X_ne (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) hD h₁.1 h₂.1 hx
    exact crossRel_of_values hS hPr

/-- **The exact parallelogram law of heights.** -/
theorem height_parallelogram (h2 : (2 : F) ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c)))
    (P Q : (twistCurve a b c).toAffine.Point) :
    height a b c (P + Q) + height a b c (P - Q) = 2 * height a b c P + 2 * height a b c Q := by
  obtain ⟨c1, c2, c3⟩ := crossRelations h2 P Q
  simp only [formTriple, pairTriple] at c1 c2 c3
  obtain ⟨k, hk, eA, eB, eD⟩ := eq_const_mul_of_cross
    (forms_bezout h2 hcop (xPair_coprime P) (xPair_coprime Q))
    (pair_bezout (xPair_coprime (P + Q)) (xPair_coprime (P - Q))) c1 c2 c3
  have h1 := forms_top (a := a) (b := b) (c := c) h2 hcop (xPair_ne P) (xPair_ne Q)
  have h3 := pair_top (xPair_ne (P + Q)) (xPair_ne (P - Q))
  rw [eA, eB, eD, maxDeg_const_mul hk, h3] at h1
  exact h1

end Twist

end GaloisForLFunctions.ArithmeticScatteringHolography

end
