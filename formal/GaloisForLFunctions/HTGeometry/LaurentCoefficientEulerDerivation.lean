import GaloisForLFunctions.HTGeometry.LaurentHasLead

/-!
# Coefficientwise and Euler derivations of formal Laurent series

For a field `K` over `ℂ` and a `ℂ`-derivation `D` of `K`, applying `D` to every coefficient is a
`ℂ`-derivation of `K((t))`; so is the Euler operator `t d/dt`, which multiplies the coefficient of
`tⁿ` by `n`.  Both preserve the vanishing below a degree, and their boundary coefficients are
`D c` and `d c`: the boundary-coefficient calculus `HasLead` is carried along.
-/

namespace GaloisForLFunctions.HTGeometry

namespace LaurentDerivation

variable {K : Type*} [Field K] [Algebra ℂ K]

attribute [local instance 2000] Algebra.toModule

theorem algebraMap_complex_laurent (c : ℂ) :
    algebraMap ℂ (LaurentSeries K) c = HahnSeries.C (algebraMap ℂ K c) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]

theorem coeff_algebraMap_mul (c : ℂ) (f : LaurentSeries K) (n : ℤ) :
    ((algebraMap ℂ (LaurentSeries K)) c * f).coeff n = (algebraMap ℂ K) c * f.coeff n := by
  rw [algebraMap_complex_laurent, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- `ℂ`-derivations of `K((t))`, with scalars acting through `algebraMap`.  The coefficientwise
module structure on `K((t))` is not definitionally the one induced by its `ℂ`-algebra structure,
so the scalar action is fixed here once and for all. -/
abbrev LaurentComplexDerivation (K : Type*) [Field K] [Algebra ℂ K] :=
  @Derivation ℂ (LaurentSeries K) (LaurentSeries K) _ _ _ _ _ Algebra.toModule

/-- The coefficientwise image of a derivation. -/
def coeffMap (D : Derivation ℂ K K) (f : LaurentSeries K) : LaurentSeries K where
  coeff := fun n => D (f.coeff n)
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [HahnSeries.support, Function.mem_support, ne_eq]
    intro h
    exact hn (by rw [h, map_zero])

@[simp]
theorem coeff_coeffMap (D : Derivation ℂ K K) (f : LaurentSeries K) (n : ℤ) :
    (coeffMap D f).coeff n = D (f.coeff n) := rfl

theorem support_coeffMap_subset (D : Derivation ℂ K K) (f : LaurentSeries K) :
    (coeffMap D f).support ⊆ f.support := by
  intro n hn
  simp only [HahnSeries.support, Function.mem_support, ne_eq, coeff_coeffMap] at hn ⊢
  intro h
  exact hn (by rw [h, map_zero])

theorem coeffMap_mul (D : Derivation ℂ K K) (f g : LaurentSeries K) :
    coeffMap D (f * g) = f * coeffMap D g + coeffMap D f * g := by
  refine HahnSeries.ext ?_
  funext n
  rw [coeff_coeffMap, HahnSeries.coeff_mul, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' g.isPWO_support (support_coeffMap_subset D g),
    HahnSeries.coeff_mul_left' f.isPWO_support (support_coeffMap_subset D f),
    ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Derivation.leibniz, coeff_coeffMap, coeff_coeffMap]
  simp only [smul_eq_mul]
  ring

/-- **The coefficientwise derivation** of formal Laurent series. -/
def coeffDerivation (D : Derivation ℂ K K) : LaurentComplexDerivation K where
  toFun := coeffMap D
  map_add' f g := by
    refine HahnSeries.ext ?_
    funext n
    simp
  map_smul' c f := by
    refine HahnSeries.ext ?_
    funext n
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, coeff_algebraMap_mul,
      coeff_coeffMap, coeff_coeffMap, coeff_algebraMap_mul, ← Algebra.smul_def,
      ← Algebra.smul_def, D.map_smul]
  map_one_eq_zero' := by
    change coeffMap D 1 = 0
    refine HahnSeries.ext ?_
    funext n
    rw [coeff_coeffMap, HahnSeries.coeff_one]
    split_ifs <;> simp
  leibniz' f g := by
    change coeffMap D (f * g) = f • coeffMap D g + g • coeffMap D f
    rw [coeffMap_mul]
    simp only [smul_eq_mul]
    ring

@[simp]
theorem coeff_coeffDerivation (D : Derivation ℂ K K) (f : LaurentSeries K) (n : ℤ) :
    (coeffDerivation D f).coeff n = D (f.coeff n) := rfl

/-- The Euler operator `t d/dt` on coefficients. -/
def eulerMap (f : LaurentSeries K) : LaurentSeries K where
  coeff := fun n => (n : K) * f.coeff n
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [HahnSeries.support, Function.mem_support, ne_eq]
    intro h
    exact hn (by rw [h, mul_zero])

omit [Algebra ℂ K] in
@[simp]
theorem coeff_eulerMap (f : LaurentSeries K) (n : ℤ) :
    (eulerMap f).coeff n = (n : K) * f.coeff n := rfl

omit [Algebra ℂ K] in
theorem support_eulerMap_subset (f : LaurentSeries K) :
    (eulerMap f).support ⊆ f.support := by
  intro n hn
  simp only [HahnSeries.support, Function.mem_support, ne_eq, coeff_eulerMap] at hn ⊢
  intro h
  exact hn (by rw [h, mul_zero])

omit [Algebra ℂ K] in
theorem eulerMap_mul (f g : LaurentSeries K) :
    eulerMap (f * g) = f * eulerMap g + eulerMap f * g := by
  refine HahnSeries.ext ?_
  funext n
  rw [coeff_eulerMap, HahnSeries.coeff_mul, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' g.isPWO_support (support_eulerMap_subset g),
    HahnSeries.coeff_mul_left' f.isPWO_support (support_eulerMap_subset f),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hp
  rw [coeff_eulerMap, coeff_eulerMap,
    show (n : K) = (p.1 : K) + (p.2 : K) by rw [← hsum]; push_cast; ring]
  ring

/-- **The Euler derivation** `t d/dt` of formal Laurent series. -/
def eulerDerivation : LaurentComplexDerivation K where
  toFun := eulerMap
  map_add' f g := by
    refine HahnSeries.ext ?_
    funext n
    simp only [coeff_eulerMap, HahnSeries.coeff_add]
    ring
  map_smul' c f := by
    refine HahnSeries.ext ?_
    funext n
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, coeff_algebraMap_mul,
      coeff_eulerMap, coeff_eulerMap, coeff_algebraMap_mul]
    ring
  map_one_eq_zero' := by
    change eulerMap 1 = 0
    refine HahnSeries.ext ?_
    funext n
    rw [coeff_eulerMap, HahnSeries.coeff_one]
    split_ifs with h
    · subst h
      simp
    · simp
  leibniz' f g := by
    change eulerMap (f * g) = f • eulerMap g + g • eulerMap f
    rw [eulerMap_mul]
    simp only [smul_eq_mul]
    ring

@[simp]
theorem coeff_eulerDerivation (f : LaurentSeries K) (n : ℤ) :
    (eulerDerivation f).coeff n = (n : K) * f.coeff n := rfl

end LaurentDerivation

/-! ## Boundary coefficients -/

open LaurentDerivation

variable {K : Type*} [Field K] [Algebra ℂ K]

theorem HasLead.coeffDerivation {D : Derivation ℂ K K} {f : LaurentSeries K} {d : ℤ} {c : K}
    (hf : HasLead f d c) : HasLead (coeffDerivation D f) d (D c) :=
  ⟨fun k hk => by rw [coeff_coeffDerivation, hf.1 k hk, map_zero],
    by rw [coeff_coeffDerivation, hf.2]⟩

theorem HasLead.euler {f : LaurentSeries K} {d : ℤ} {c : K} (hf : HasLead f d c) :
    HasLead (eulerDerivation f) d ((d : K) * c) :=
  ⟨fun k hk => by rw [coeff_eulerDerivation, hf.1 k hk, mul_zero],
    by rw [coeff_eulerDerivation, hf.2]⟩

/-- A multiple of the Euler derivation by a series of order at least zero contributes the constant
term times the degree. -/
theorem HasLead.mul_euler {a f : LaurentSeries K} {d : ℤ} {a₀ c : K}
    (ha : HasLead a 0 a₀) (hf : HasLead f d c) :
    HasLead (a * eulerDerivation f) d (a₀ * ((d : K) * c)) := by
  have h := ha.mul hf.euler
  rwa [zero_add] at h

/-- A multiple of the Euler derivation by a monomial `κ tᴺ` raises the degree by `N`. -/
theorem HasLead.single_mul_euler {f : LaurentSeries K} {d : ℤ} {c : K} (N : ℤ) (κ : K)
    (hf : HasLead f d c) :
    HasLead (HahnSeries.single N κ * eulerDerivation f) (d + N) (κ * ((d : K) * c)) := by
  have hs : HasLead (HahnSeries.single N κ : LaurentSeries K) N κ :=
    ⟨fun k hk => by rw [HahnSeries.coeff_single_of_ne (by omega)],
      by rw [HahnSeries.coeff_single_same]⟩
  have h := hs.mul hf.euler
  rwa [add_comm N d] at h

end GaloisForLFunctions.HTGeometry
