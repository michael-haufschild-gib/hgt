import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Localizations at elements along divisibility

Let `R_a` and `R_b` be localizations of `R` at `a` and `b`, with an `R`-algebra map `R_a → R_b`
(so `a` becomes a unit in `R_b`), and suppose `b ∣ k a`.  Then the map behaves like the
localization map inverting `k`:

* every element of `R_b`, multiplied by a power of `k`, comes from `R_a`;
* an element of `R_a` that vanishes in `R_b` is killed by a power of `k`.

These are the two local properties of the restriction maps between basic open sets that make Čech
complexes of basic-open covers exact.
-/

namespace HTGeometry

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {a b k : R} [IsLocalization.Away a A] [IsLocalization.Away b B]

omit [IsLocalization.Away a A] in
/-- In a localization at `b`, an element dividing `b` is a unit. -/
theorem isUnit_algebraMap_of_dvd (hab : a ∣ b) : IsUnit (algebraMap R B a) :=
  isUnit_of_dvd_unit (map_dvd _ hab) (IsLocalization.Away.algebraMap_isUnit b)

/-- **A section over a smaller basic open is a restriction after multiplication by a power of the
extra equation**: if `a ∣ b ∣ k a`, every element of `R_b` times a power of `k` comes from `R_a`. -/
theorem exists_map_eq_pow_smul (φ : A →ₐ[R] B) (hab : a ∣ b) (hbk : b ∣ k * a) (y : B) :
    ∃ (n : ℕ) (x : A), φ x = k ^ n • y := by
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers b) y
  obtain ⟨c, hc⟩ := hbk
  refine ⟨n, IsLocalization.mk' A (r * c ^ n) (⟨a ^ n, n, rfl⟩ : Submonoid.powers a), ?_⟩
  have hu : IsUnit (algebraMap R B (a ^ n)) := by
    rw [map_pow]; exact (isUnit_algebraMap_of_dvd hab).pow n
  refine hu.mul_left_inj.mp ?_
  have h1 : φ (IsLocalization.mk' A (r * c ^ n) (⟨a ^ n, n, rfl⟩ : Submonoid.powers a))
      * algebraMap R B (a ^ n) = algebraMap R B (r * c ^ n) := by
    rw [← φ.commutes, ← map_mul, IsLocalization.mk'_spec, φ.commutes]
  rw [h1, Algebra.smul_def]
  simp only at hy
  have hcn : (algebraMap R B k * algebraMap R B a) ^ n = (algebraMap R B b * algebraMap R B c) ^ n := by
    rw [← map_mul, ← map_mul, hc]
  simp only [map_mul, map_pow] at hy ⊢
  linear_combination (-(algebraMap R B c) ^ n) * hy - y * hcn

/-- **A section over a smaller basic open restricting to zero is killed by a power of the extra
equation**: if `a ∣ b ∣ k a`, an element of `R_a` vanishing in `R_b` is killed by a power of `k`. -/
theorem exists_pow_smul_eq_zero (φ : A →ₐ[R] B) (hbk : b ∣ k * a) (x : A) (hx : φ x = 0) :
    ∃ n : ℕ, k ^ n • x = 0 := by
  obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hxr⟩ := IsLocalization.surj (Submonoid.powers a) x
  simp only at hxr
  have hr : algebraMap R B r = 0 := by
    rw [← φ.commutes, ← hxr, map_mul, hx, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b) B r).mp hr
  simp only at hj
  obtain ⟨c, hc⟩ := hbk
  refine ⟨j, ?_⟩
  have hu : IsUnit (algebraMap R A (a ^ j * a ^ m)) := by
    rw [map_mul, map_pow, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit a).pow j).mul
      ((IsLocalization.Away.algebraMap_isUnit a).pow m)
  refine (hu.mul_left_eq_zero).mp ?_
  have hcj : (algebraMap R A k * algebraMap R A a) ^ j = (algebraMap R A b * algebraMap R A c) ^ j := by
    rw [← map_mul, ← map_mul, hc]
  have hj' : algebraMap R A b ^ j * algebraMap R A r = 0 := by
    rw [← map_pow, ← map_mul, hj, map_zero]
  rw [Algebra.smul_def]
  simp only [map_mul, map_pow] at hxr ⊢
  linear_combination (algebraMap R A k * algebraMap R A a) ^ j * hxr
    + algebraMap R A r * hcj + algebraMap R A c ^ j * hj'




end HTGeometry
