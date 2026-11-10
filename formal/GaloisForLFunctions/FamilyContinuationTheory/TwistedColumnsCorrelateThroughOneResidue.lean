import Mathlib

/-!
# Twisted additive columns correlate through one residue

An additive column of modulus `d` is the finite Fourier transform
`A_f(m) = Σ_{x mod d} f(x) e(m x / d)` of a function `f` on `ℤ/d`, read on rows `m` modulo a
multiple `N` of `d`. For `f` a residue character this is the incomplete Gauss sum of the row `m`.

* **Correlation of two columns** (`sum_column_mul_conj_column`). For divisors `d₁, d₂` of `N` the
  correlation `Σ_m A_f(m) conj(A_g(m)) e(−m k / N)` is `N` times the sum of `f(x) conj(g(y))` over
  the pairs with `(N/d₁) x − (N/d₂) y = k`.
* **Coprime moduli** (`sum_column_mul_conj_column_of_coprime`). For `N = a b` with `a, b`
  coprime the pair is unique: the correlation is the single term
  `a b · f(k b⁻¹) conj(g(−k a⁻¹))`.
* **The dual form** (`sum_weight_mul_column_mul_conj_column`). A weighted second moment over the
  rows is the sum over the frequencies `k` of the transform of the weight times that single term:
  the additive Gram form of two columns is a multiplicative form in the frequency.
* **Exceptional frequencies** (`sum_column_mul_conj_column_of_exceptional`). For characters `χ, φ`
  and a frequency on which both are `1`, the correlation is `a b · χ(b⁻¹) conj(φ(−a⁻¹))`: it does
  not depend on the frequency. Summed over a set of such frequencies the terms add without
  cancellation (`sum_exceptional_correlation`).

For residue symbols of order `n` the exceptional frequencies are the `n`-th powers. Their
contribution to a second moment over a row ball shorter than the conductor of a pair is
therefore the number of such frequencies times the plain product of the two column sums; no
weight attached to the common divisors of the columns enters it.
-/

noncomputable section

open scoped ComplexConjugate
open Finset

namespace GaloisForLFunctions.FamilyContinuationTheory

/-- The lift `x ↦ (N/d)·x` of a residue modulo `d` to a residue modulo `N`. -/
def scaledLift (N d : ℕ) (x : ZMod d) : ZMod N := ((N / d * x.val : ℕ) : ZMod N)

/-- The additive column of `f` on `ℤ/d`, read on the rows modulo `N`. -/
def column {d N : ℕ} [NeZero d] (h : d ∣ N) (f : ZMod d → ℂ) (m : ZMod N) : ℂ :=
  ∑ x : ZMod d, f x * ZMod.stdAddChar (ZMod.castHom h (ZMod d) m * x)

/-- The transform of a row weight at a frequency. -/
def rowTransform {N : ℕ} [NeZero N] (W : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ m : ZMod N, W m * ZMod.stdAddChar (m * k)

/-- The standard character at a natural number. -/
theorem stdAddChar_natCast {N : ℕ} [NeZero N] (n : ℕ) :
    ZMod.stdAddChar ((n : ℕ) : ZMod N) =
      Complex.exp (2 * Real.pi * Complex.I * n / N) := by
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe, Int.cast_natCast]

/-- The character `e(m x / d)` on rows modulo `N` is `e(m · (N/d) x / N)`. -/
theorem stdAddChar_castHom_mul {d N : ℕ} [NeZero d] [NeZero N] (h : d ∣ N) (m : ZMod N)
    (x : ZMod d) :
    ZMod.stdAddChar (ZMod.castHom h (ZMod d) m * x) =
      ZMod.stdAddChar (m * scaledLift N d x) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hl : ZMod.castHom h (ZMod d) m * x = ((m.val * x.val : ℕ) : ZMod d) := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, Nat.cast_mul, ZMod.natCast_zmod_val x]
  have hr : m * scaledLift N d x = ((m.val * (N / d * x.val) : ℕ) : ZMod N) := by
    unfold scaledLift
    rw [Nat.cast_mul m.val, ZMod.natCast_zmod_val m]
  rw [hl, hr, stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_div h hd]
  field_simp

/-- Orthogonality of the rows. -/
theorem sum_stdAddChar_mul {N : ℕ} [NeZero N] (c : ZMod N) :
    ∑ m : ZMod N, ZMod.stdAddChar (m * c) = if c = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- **Correlation of two columns.** The correlation at the frequency `k` counts, with the
weights `f(x) conj(g(y))`, the pairs of residues whose lifts differ by `k`. -/
theorem sum_column_mul_conj_column {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂] [NeZero N]
    (h₁ : d₁ ∣ N) (h₂ : d₂ ∣ N) (f : ZMod d₁ → ℂ) (g : ZMod d₂ → ℂ) (k : ZMod N) :
    ∑ m : ZMod N, column h₁ f m * conj (column h₂ g m) * ZMod.stdAddChar (-(m * k)) =
      (N : ℂ) * ∑ x : ZMod d₁, ∑ y : ZMod d₂,
        if scaledLift N d₁ x - scaledLift N d₂ y = k then f x * conj (g y) else 0 := by
  have hterm : ∀ m : ZMod N, column h₁ f m * conj (column h₂ g m) * ZMod.stdAddChar (-(m * k)) =
      ∑ x : ZMod d₁, ∑ y : ZMod d₂, f x * conj (g y) *
        ZMod.stdAddChar (m * (scaledLift N d₁ x - scaledLift N d₂ y - k)) := by
    intro m
    unfold column
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul (starRingEnd ℂ), stdAddChar_castHom_mul h₁, stdAddChar_castHom_mul h₂,
      ← AddChar.map_neg_eq_conj, mul_sub, mul_sub, sub_eq_add_neg, sub_eq_add_neg,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases hk : scaledLift N d₁ x - scaledLift N d₂ y = k
  · rw [if_pos hk, if_pos (sub_eq_zero.mpr hk)]
    ring
  · rw [if_neg hk, if_neg fun h => hk (sub_eq_zero.mp h)]
    ring

/-- A residue modulo `a b`, `a` and `b` coprime, that vanishes modulo `a` and modulo `b` is
zero. -/
theorem eq_zero_of_castHom_eq_zero {a b : ℕ} [NeZero a] [NeZero b] (hab : a.Coprime b)
    (z : ZMod (a * b)) (h₁ : ZMod.castHom (dvd_mul_right a b) (ZMod a) z = 0)
    (h₂ : ZMod.castHom (dvd_mul_left b a) (ZMod b) z = 0) : z = 0 := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h₁ h₂
  rw [← ZMod.natCast_zmod_val z, ZMod.natCast_eq_zero_iff]
  exact hab.mul_dvd_of_dvd_of_dvd h₁ h₂

section Coprime

variable {a b : ℕ} [NeZero a] [NeZero b]

omit [NeZero b] in
/-- Modulo `a` the lift of the first column is multiplication by `b`. -/
theorem castHom_scaledLift_left (x : ZMod a) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) (scaledLift (a * b) a x) = (b : ZMod a) * x := by
  unfold scaledLift
  rw [Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero (NeZero.ne a)), map_natCast]
  push_cast
  rw [ZMod.natCast_zmod_val x]

omit [NeZero b] in
/-- Modulo `b` the lift of the first column vanishes. -/
theorem castHom_scaledLift_left_other (x : ZMod a) :
    ZMod.castHom (dvd_mul_left b a) (ZMod b) (scaledLift (a * b) a x) = 0 := by
  unfold scaledLift
  rw [Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero (NeZero.ne a)), map_natCast]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

omit [NeZero a] in
/-- Modulo `b` the lift of the second column is multiplication by `a`. -/
theorem castHom_scaledLift_right (y : ZMod b) :
    ZMod.castHom (dvd_mul_left b a) (ZMod b) (scaledLift (a * b) b y) = (a : ZMod b) * y := by
  unfold scaledLift
  rw [Nat.mul_div_cancel a (Nat.pos_of_ne_zero (NeZero.ne b)), map_natCast]
  push_cast
  rw [ZMod.natCast_zmod_val y]

omit [NeZero a] in
/-- Modulo `a` the lift of the second column vanishes. -/
theorem castHom_scaledLift_right_other (y : ZMod b) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) (scaledLift (a * b) b y) = 0 := by
  unfold scaledLift
  rw [Nat.mul_div_cancel a (Nat.pos_of_ne_zero (NeZero.ne b)), map_natCast]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

/-- The residue of the first column that a frequency selects. -/
def firstResidue (a b : ℕ) (k : ZMod (a * b)) : ZMod a :=
  ZMod.castHom (dvd_mul_right a b) (ZMod a) k * ((b : ℕ) : ZMod a)⁻¹

/-- The residue of the second column that a frequency selects. -/
def secondResidue (a b : ℕ) (k : ZMod (a * b)) : ZMod b :=
  -(ZMod.castHom (dvd_mul_left b a) (ZMod b) k) * ((a : ℕ) : ZMod b)⁻¹

/-- **One pair per frequency.** For coprime moduli the lifts of two residues differ by `k`
exactly for the pair `(k b⁻¹, −k a⁻¹)`. -/
theorem scaledLift_sub_eq_iff (hab : a.Coprime b) (x : ZMod a) (y : ZMod b)
    (k : ZMod (a * b)) :
    scaledLift (a * b) a x - scaledLift (a * b) b y = k ↔
      x = firstResidue a b k ∧ y = secondResidue a b k := by
  have hb : ((b : ℕ) : ZMod a) * ((b : ℕ) : ZMod a)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hab.symm
  have ha : ((a : ℕ) : ZMod b) * ((a : ℕ) : ZMod b)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one a hab
  constructor
  · intro h
    have h1 := congrArg (ZMod.castHom (dvd_mul_right a b) (ZMod a)) h
    have h2 := congrArg (ZMod.castHom (dvd_mul_left b a) (ZMod b)) h
    rw [map_sub, castHom_scaledLift_left, castHom_scaledLift_right_other, sub_zero] at h1
    rw [map_sub, castHom_scaledLift_left_other, castHom_scaledLift_right, zero_sub] at h2
    refine ⟨?_, ?_⟩
    · unfold firstResidue
      rw [← h1, mul_comm ((b : ℕ) : ZMod a) x, mul_assoc, hb, mul_one]
    · unfold secondResidue
      rw [← h2, neg_neg, mul_comm ((a : ℕ) : ZMod b) y, mul_assoc, ha, mul_one]
  · rintro ⟨rfl, rfl⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_castHom_eq_zero hab _ ?_ ?_
    · rw [map_sub, map_sub, castHom_scaledLift_left, castHom_scaledLift_right_other, sub_zero]
      unfold firstResidue
      rw [mul_comm _ (((b : ℕ) : ZMod a)⁻¹), ← mul_assoc, hb, one_mul, sub_self]
    · rw [map_sub, map_sub, castHom_scaledLift_left_other, castHom_scaledLift_right, zero_sub]
      unfold secondResidue
      rw [mul_comm _ (((a : ℕ) : ZMod b)⁻¹), ← mul_assoc, ha, one_mul, neg_neg, sub_self]

/-- **Coprime moduli: the correlation is one term.** -/
theorem sum_column_mul_conj_column_of_coprime (hab : a.Coprime b) (f : ZMod a → ℂ)
    (g : ZMod b → ℂ) (k : ZMod (a * b)) :
    ∑ m : ZMod (a * b), column (dvd_mul_right a b) f m *
        conj (column (dvd_mul_left b a) g m) * ZMod.stdAddChar (-(m * k)) =
      ((a * b : ℕ) : ℂ) * (f (firstResidue a b k) * conj (g (secondResidue a b k))) := by
  rw [sum_column_mul_conj_column]
  congr 1
  rw [Finset.sum_eq_single (firstResidue a b k), Finset.sum_eq_single (secondResidue a b k)]
  · rw [if_pos ((scaledLift_sub_eq_iff hab _ _ k).mpr ⟨rfl, rfl⟩)]
  · intro y _ hy
    exact if_neg fun h => hy ((scaledLift_sub_eq_iff hab _ _ k).mp h).2
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx
    exact Finset.sum_eq_zero fun y _ =>
      if_neg fun h => hx ((scaledLift_sub_eq_iff hab _ _ k).mp h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The weighted second moment of two columns, before the pairs are resolved. -/
theorem sum_weight_mul_column_mul_conj_column_aux (W : ZMod (a * b) → ℂ) (f : ZMod a → ℂ)
    (g : ZMod b → ℂ) :
    ∑ m : ZMod (a * b), W m * (column (dvd_mul_right a b) f m *
        conj (column (dvd_mul_left b a) g m)) =
      ∑ x : ZMod a, ∑ y : ZMod b, f x * conj (g y) *
        rowTransform W (scaledLift (a * b) a x - scaledLift (a * b) b y) := by
  have hterm : ∀ m : ZMod (a * b), W m * (column (dvd_mul_right a b) f m *
      conj (column (dvd_mul_left b a) g m)) =
      ∑ x : ZMod a, ∑ y : ZMod b, f x * conj (g y) *
        (W m * ZMod.stdAddChar (m * (scaledLift (a * b) a x - scaledLift (a * b) b y))) := by
    intro m
    unfold column
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul (starRingEnd ℂ), stdAddChar_castHom_mul (dvd_mul_right a b),
      stdAddChar_castHom_mul (dvd_mul_left b a), ← AddChar.map_neg_eq_conj, mul_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold rowTransform
  rw [Finset.mul_sum]

/-- The pairs of residues and the frequencies correspond one to one. -/
def pairEquivFrequency (hab : a.Coprime b) : ZMod a × ZMod b ≃ ZMod (a * b) where
  toFun p := scaledLift (a * b) a p.1 - scaledLift (a * b) b p.2
  invFun k := (firstResidue a b k, secondResidue a b k)
  left_inv p := by
    obtain ⟨h1, h2⟩ := (scaledLift_sub_eq_iff hab p.1 p.2 _).mp rfl
    exact Prod.ext h1.symm h2.symm
  right_inv k := (scaledLift_sub_eq_iff hab _ _ k).mpr ⟨rfl, rfl⟩

/-- **The dual form.** The weighted second moment of two coprime columns is a sum over the
frequencies: the transform of the weight times the single correlation term. -/
theorem sum_weight_mul_column_mul_conj_column (hab : a.Coprime b) (W : ZMod (a * b) → ℂ)
    (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    ∑ m : ZMod (a * b), W m * (column (dvd_mul_right a b) f m *
        conj (column (dvd_mul_left b a) g m)) =
      ∑ k : ZMod (a * b), rowTransform W k *
        (f (firstResidue a b k) * conj (g (secondResidue a b k))) := by
  rw [sum_weight_mul_column_mul_conj_column_aux, ← Finset.sum_product',
    Finset.univ_product_univ]
  refine Fintype.sum_equiv (pairEquivFrequency hab) _ _ fun p => ?_
  have hp := (pairEquivFrequency hab).left_inv p
  have h1 : firstResidue a b (pairEquivFrequency hab p) = p.1 := congrArg Prod.fst hp
  have h2 : secondResidue a b (pairEquivFrequency hab p) = p.2 := congrArg Prod.snd hp
  rw [h1, h2]
  show f p.1 * conj (g p.2) * rowTransform W (scaledLift (a * b) a p.1 -
    scaledLift (a * b) b p.2) = _
  rw [mul_comm]
  rfl

/-- The factor that two characters of coprime moduli leave at every frequency on which both
are `1`. -/
def reciprocityFactor (a b : ℕ) (χ : MulChar (ZMod a) ℂ) (φ : MulChar (ZMod b) ℂ) : ℂ :=
  χ (((b : ℕ) : ZMod a)⁻¹) * conj (φ (-(((a : ℕ) : ZMod b)⁻¹)))

/-- **Exceptional frequencies.** At a frequency on which both characters are `1` the
correlation of the two character columns is `a b` times the reciprocity factor. -/
theorem sum_column_mul_conj_column_of_exceptional (hab : a.Coprime b)
    (χ : MulChar (ZMod a) ℂ) (φ : MulChar (ZMod b) ℂ) (k : ZMod (a * b))
    (hχ : χ (ZMod.castHom (dvd_mul_right a b) (ZMod a) k) = 1)
    (hφ : φ (ZMod.castHom (dvd_mul_left b a) (ZMod b) k) = 1) :
    ∑ m : ZMod (a * b), column (dvd_mul_right a b) χ m *
        conj (column (dvd_mul_left b a) φ m) * ZMod.stdAddChar (-(m * k)) =
      ((a * b : ℕ) : ℂ) * reciprocityFactor a b χ φ := by
  rw [sum_column_mul_conj_column_of_coprime hab]
  congr 1
  unfold firstResidue secondResidue reciprocityFactor
  rw [map_mul, hχ, one_mul, neg_mul, ← mul_neg, map_mul, hφ, one_mul]

/-- **No cancellation among exceptional frequencies.** Summed over a set of frequencies on
which both characters are `1`, the correlations add up to the number of frequencies times
`a b` times the reciprocity factor. -/
theorem sum_exceptional_correlation (hab : a.Coprime b) (χ : MulChar (ZMod a) ℂ)
    (φ : MulChar (ZMod b) ℂ) (E : Finset (ZMod (a * b)))
    (hχ : ∀ k ∈ E, χ (ZMod.castHom (dvd_mul_right a b) (ZMod a) k) = 1)
    (hφ : ∀ k ∈ E, φ (ZMod.castHom (dvd_mul_left b a) (ZMod b) k) = 1) :
    ∑ k ∈ E, ∑ m : ZMod (a * b), column (dvd_mul_right a b) χ m *
        conj (column (dvd_mul_left b a) φ m) * ZMod.stdAddChar (-(m * k)) =
      (E.card : ℂ) * (((a * b : ℕ) : ℂ) * reciprocityFactor a b χ φ) := by
  rw [Finset.sum_congr rfl fun k hk =>
    sum_column_mul_conj_column_of_exceptional hab χ φ k (hχ k hk) (hφ k hk)]
  rw [Finset.sum_const, nsmul_eq_mul]

end Coprime

end GaloisForLFunctions.FamilyContinuationTheory
