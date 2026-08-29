import GaloisForLFunctions.HTGeometry.MahlerRatFuncEmbedding

/-!
# The `p`-perfect rational base of a Mahler equation

On `k(w)` the substitution `w ↦ w^p` is injective but **not surjective**, so it is not an
automorphism, and the automorphism-family criterion cannot take `k(w)` as its base.  The smallest
base on which the substitution is bijective is the union of the ramified towers
`k(w^(1/pⁿ))`, taken inside the Hahn field with rational exponents.  On that union the
substitution is an automorphism, and the union is still a field of *rational* functions, so the
lacunary formal solutions that obstruct telescoping remain outside it.

This file builds the tower and its union.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- Dividing rational exponents by `pⁿ`. -/
def qShrinkHom (p n : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (((p : ℚ) ^ n)⁻¹)

@[simp]
theorem qShrinkHom_apply (p n : ℕ) (γ : ℚ) : qShrinkHom p n γ = ((p : ℚ) ^ n)⁻¹ * γ := rfl

theorem qShrinkHom_injective {p : ℕ} (hp : 0 < p) (n : ℕ) :
    Function.Injective (qShrinkHom p n) := by
  intro γ δ h
  rw [qShrinkHom_apply, qShrinkHom_apply] at h
  have hpos : (0 : ℚ) < ((p : ℚ) ^ n)⁻¹ := by
    have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    positivity
  exact mul_left_cancel₀ (ne_of_gt hpos) h

theorem qShrinkHom_le_iff {p : ℕ} (hp : 0 < p) (n : ℕ) (γ δ : ℚ) :
    qShrinkHom p n γ ≤ qShrinkHom p n δ ↔ γ ≤ δ := by
  have hpos : (0 : ℚ) < ((p : ℚ) ^ n)⁻¹ := by
    have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    positivity
  rw [qShrinkHom_apply, qShrinkHom_apply]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hpos
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hpos)

/-- The `n`-th ramified level: rational functions of `w^(1/pⁿ)`, inside the Hahn field. -/
def ramifiedLevelHom (p : ℕ) (hp : 0 < p) (n : ℕ) : RatFunc k →+* HahnSeries ℚ k :=
  (HahnSeries.embDomainRingHom (qShrinkHom p n) (qShrinkHom_injective hp n)
    (qShrinkHom_le_iff hp n)).comp ratFuncToHahn

theorem ramifiedLevelHom_zero (p : ℕ) (hp : 0 < p) (r : RatFunc k) :
    ramifiedLevelHom p hp 0 r = ratFuncToHahn r := by
  show HahnSeries.embDomain _ (ratFuncToHahn r) = ratFuncToHahn r
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  have hid : ∀ δ : ℚ, qShrinkHom p 0 δ = δ := by
    intro δ
    rw [qShrinkHom_apply, pow_zero, inv_one, one_mul]
  have h := HahnSeries.embDomain_coeff (f := ⟨⟨qShrinkHom p 0, qShrinkHom_injective hp 0⟩,
    qShrinkHom_le_iff hp 0 _ _⟩) (x := ratFuncToHahn r) (a := γ)
  rw [show (⟨⟨qShrinkHom p 0, qShrinkHom_injective hp 0⟩, qShrinkHom_le_iff hp 0 _ _⟩ :
      ℚ ↪o ℚ) γ = γ from hid γ] at h
  exact h

/-- **Each level embeds in the next**: `w^(1/pⁿ)` is the `p`-th power of `w^(1/p^(n+1))`. -/
theorem ramifiedLevelHom_succ (p : ℕ) (hp : 1 < p) (n : ℕ) (r : RatFunc k) :
    ramifiedLevelHom p (by omega) n r
      = ramifiedLevelHom p (by omega) (n + 1) (ratFuncPow p (by omega) r) := by
  have key : ratFuncToHahn (ratFuncPow p (by omega : 0 < p) r)
      = HahnSeries.embDomain (⟨⟨qStretchHom p, qStretchHom_injective (by omega)⟩,
          qStretchHom_le_iff (by omega) _ _⟩ : ℚ ↪o ℚ) (ratFuncToHahn r) :=
    ratFuncToHahn_pow p hp r
  show HahnSeries.embDomain (⟨⟨qShrinkHom p n, qShrinkHom_injective (by omega) n⟩,
      qShrinkHom_le_iff (by omega) n _ _⟩ : ℚ ↪o ℚ) (ratFuncToHahn r)
    = HahnSeries.embDomain (⟨⟨qShrinkHom p (n + 1), qShrinkHom_injective (by omega) (n + 1)⟩,
      qShrinkHom_le_iff (by omega) (n + 1) _ _⟩ : ℚ ↪o ℚ)
      (ratFuncToHahn (ratFuncPow p (by omega : 0 < p) r))
  rw [key, embDomain_comp]
  congr 1
  refine RelEmbedding.ext fun γ => ?_
  show ((p : ℚ) ^ n)⁻¹ * γ = ((p : ℚ) ^ (n + 1))⁻¹ * ((p : ℚ) * γ)
  have hpne : ((p : ℚ)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this.ne'
  field_simp
  ring

/-- Raising a level-`m` element to level `m + d`. -/
theorem ramifiedLevelHom_add (p : ℕ) (hp : 1 < p) (m d : ℕ) (r : RatFunc k) :
    ramifiedLevelHom p (by omega) m r
      = ramifiedLevelHom p (by omega) (m + d) ((ratFuncPow p (by omega))^[d] r) := by
  induction d generalizing r m with
  | zero => simp
  | succ d ih =>
      rw [show m + (d + 1) = (m + 1) + d by omega, Function.iterate_succ_apply,
        ramifiedLevelHom_succ p hp m r]
      exact ih _ _

theorem exists_common_level (p : ℕ) (hp : 1 < p) (m n : ℕ) (r s : RatFunc k) :
    ∃ N : ℕ, ∃ r' s' : RatFunc k, m ≤ N ∧ n ≤ N ∧
      ramifiedLevelHom p (by omega) m r = ramifiedLevelHom p (by omega) N r' ∧
      ramifiedLevelHom p (by omega) n s = ramifiedLevelHom p (by omega) N s' := by
  refine ⟨max m n, (ratFuncPow p (by omega))^[max m n - m] r,
    (ratFuncPow p (by omega))^[max m n - n] s, le_max_left _ _, le_max_right _ _, ?_, ?_⟩
  · have h := ramifiedLevelHom_add p hp m (max m n - m) r
    rwa [show m + (max m n - m) = max m n by omega] at h
  · have h := ramifiedLevelHom_add p hp n (max m n - n) s
    rwa [show n + (max m n - n) = max m n by omega] at h

/-- **The `p`-perfect rational base**: the union of all ramified levels, a subfield of the Hahn
field on which the Mahler substitution is an automorphism. -/
def perfectBase (p : ℕ) (hp : 1 < p) : Subfield (HahnSeries ℚ k) where
  carrier := {x | ∃ n : ℕ, ∃ r : RatFunc k, ramifiedLevelHom p (by omega) n r = x}
  mul_mem' := by
    rintro x y ⟨m, r, rfl⟩ ⟨n, s, rfl⟩
    obtain ⟨N, r', s', -, -, hr, hs⟩ := exists_common_level p hp m n r s
    exact ⟨N, r' * s', by rw [map_mul, ← hr, ← hs]⟩
  one_mem' := ⟨0, 1, map_one _⟩
  add_mem' := by
    rintro x y ⟨m, r, rfl⟩ ⟨n, s, rfl⟩
    obtain ⟨N, r', s', -, -, hr, hs⟩ := exists_common_level p hp m n r s
    exact ⟨N, r' + s', by rw [map_add, ← hr, ← hs]⟩
  zero_mem' := ⟨0, 0, map_zero _⟩
  neg_mem' := by
    rintro x ⟨n, r, rfl⟩
    exact ⟨n, -r, map_neg _ _⟩
  inv_mem' := by
    rintro x ⟨n, r, rfl⟩
    exact ⟨n, r⁻¹, by rw [map_inv₀]⟩

@[simp]
theorem mem_perfectBase_iff (p : ℕ) (hp : 1 < p) (x : HahnSeries ℚ k) :
    x ∈ perfectBase p hp ↔ ∃ n : ℕ, ∃ r : RatFunc k, ramifiedLevelHom p (by omega) n r = x :=
  Iff.rfl

theorem ramifiedLevelHom_mem_perfectBase (p : ℕ) (hp : 1 < p) (n : ℕ) (r : RatFunc k) :
    ramifiedLevelHom p (by omega) n r ∈ perfectBase p hp := ⟨n, r, rfl⟩

/-- **The Mahler substitution lowers the level by one.** -/
theorem mahlerHom_ramifiedLevelHom (p : ℕ) (hp : 1 < p) (n : ℕ) (r : RatFunc k) :
    mahlerHom p (by omega) (ramifiedLevelHom p (by omega) (n + 1) r)
      = ramifiedLevelHom p (by omega) n r := by
  show HahnSeries.embDomain (⟨⟨qStretchHom p, qStretchHom_injective (by omega)⟩,
      qStretchHom_le_iff (by omega) _ _⟩ : ℚ ↪o ℚ)
      (HahnSeries.embDomain (⟨⟨qShrinkHom p (n + 1), qShrinkHom_injective (by omega) (n + 1)⟩,
        qShrinkHom_le_iff (by omega) (n + 1) _ _⟩ : ℚ ↪o ℚ) (ratFuncToHahn r))
    = HahnSeries.embDomain (⟨⟨qShrinkHom p n, qShrinkHom_injective (by omega) n⟩,
      qShrinkHom_le_iff (by omega) n _ _⟩ : ℚ ↪o ℚ) (ratFuncToHahn r)
  rw [embDomain_comp]
  congr 1
  refine RelEmbedding.ext fun γ => ?_
  show (p : ℚ) * (((p : ℚ) ^ (n + 1))⁻¹ * γ) = ((p : ℚ) ^ n)⁻¹ * γ
  have hpne : ((p : ℚ)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this.ne'
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
