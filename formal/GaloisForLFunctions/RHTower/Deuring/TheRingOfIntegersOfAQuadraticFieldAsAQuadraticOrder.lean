import Mathlib

/-!
# The ring of integers of a quadratic field as a quadratic order

For a number field `K` of degree two there are integers `a, b` with `𝓞 K ≃ₐ[ℤ] ℤ[ω]`,
`ω² = a + bω` (`QuadraticAlgebra ℤ a b`), and `disc K = b² + 4a`
(`exists_quadraticAlgebra_equiv`).

* A commutative ring that is free of rank two over `ℤ` is `ℤ[ω]`
  (`exists_algEquiv_quadraticAlgebra`): the coordinates `(u, v)` of `1` are coprime (a common
  divisor `g` gives `1 = g x`, so `g² ∣ 1` by norms), and with `uA + vB = 1` the element
  `ω = −B e₀ + A e₁` completes `1` to a basis.
* The trace of `x + yω` is `2x + by`, so the trace form of the basis `1, ω` is
  `[[2, b], [b, b² + 2a]]` with determinant `b² + 4a` (`discr_quadraticAlgebra`).
-/

open NumberField

namespace GaloisForLFunctions.RHTower.Deuring

/-! ### Trace form and discriminant of `ℤ[ω]` -/

section QuadraticOrder

variable (a b : ℤ)

theorem qbasis_zero : QuadraticAlgebra.basis a b 0 = ⟨1, 0⟩ := by
  apply (QuadraticAlgebra.basis a b).repr.injective
  ext j
  rw [Module.Basis.repr_self, QuadraticAlgebra.basis_repr_apply]
  fin_cases j <;> simp

theorem qbasis_one : QuadraticAlgebra.basis a b 1 = ⟨0, 1⟩ := by
  apply (QuadraticAlgebra.basis a b).repr.injective
  ext j
  rw [Module.Basis.repr_self, QuadraticAlgebra.basis_repr_apply]
  fin_cases j <;> simp

/-- The trace of `x + yω` is `2x + by`: multiplication by it has matrix
`[[x, ay], [y, x + by]]` in the basis `1, ω`. -/
theorem trace_quadraticAlgebra (z : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) z = 2 * z.re + b * z.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b), Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, qbasis_zero, qbasis_one,
    QuadraticAlgebra.basis_repr_apply]
  show z.re * 1 + a * z.im * 0 + (z.re * 1 + z.im * 0 + b * z.im * 1) = 2 * z.re + b * z.im
  ring

/-- The discriminant of `ℤ[ω]`, `ω² = a + bω`, is `b² + 4a`. -/
theorem discr_quadraticAlgebra :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = b ^ 2 + 4 * a := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, qbasis_zero, qbasis_one,
    trace_quadraticAlgebra, QuadraticAlgebra.mk_mul_mk]
  ring

end QuadraticOrder

/-! ### Rings that are free of rank two over `ℤ` -/

section RankTwo

variable {O : Type*} [CommRing O]

theorem repr_pair (e : Module.Basis (Fin 2) ℤ O) (c₀ c₁ : ℤ) :
    e.repr (c₀ • e 0 + c₁ • e 1) = Finsupp.single 0 c₀ + Finsupp.single 1 c₁ := by
  rw [map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp

theorem repr_pair_zero (e : Module.Basis (Fin 2) ℤ O) (c₀ c₁ : ℤ) :
    e.repr (c₀ • e 0 + c₁ • e 1) 0 = c₀ := by
  rw [repr_pair]
  simp

theorem repr_pair_one (e : Module.Basis (Fin 2) ℤ O) (c₀ c₁ : ℤ) :
    e.repr (c₀ • e 0 + c₁ • e 1) 1 = c₁ := by
  rw [repr_pair]
  simp

/-- The coordinates of `1` in a `ℤ`-basis of a commutative ring are coprime: a common divisor
`g` gives `1 = g x`, and taking norms `g² ∣ 1`. -/
theorem exists_bezout_of_one_eq (e : Module.Basis (Fin 2) ℤ O) {u v : ℤ}
    (h1 : (1 : O) = u • e 0 + v • e 1) : ∃ A B : ℤ, u * A + v * B = 1 := by
  have hdvd : ∀ g : ℤ, g ∣ u → g ∣ v → IsUnit g := by
    rintro g ⟨u', rfl⟩ ⟨v', rfl⟩
    have hx : algebraMap ℤ O g * (u' • e 0 + v' • e 1) = 1 := by
      rw [eq_intCast (algebraMap ℤ O) g, h1]
      simp only [zsmul_eq_mul, Int.cast_mul]
      ring
    have hN : Algebra.norm ℤ (algebraMap ℤ O g) * Algebra.norm ℤ (u' • e 0 + v' • e 1) = 1 := by
      rw [← map_mul (Algebra.norm ℤ), hx]
      exact map_one (Algebra.norm ℤ)
    rw [Algebra.norm_algebraMap_of_basis e g, Fintype.card_fin] at hN
    exact (isUnit_pow_iff two_ne_zero).mp (isUnit_of_dvd_one ⟨_, hN.symm⟩)
  have hg : Int.gcd u v = 1 := by
    have hu := hdvd (Int.gcd u v) (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  refine ⟨Int.gcdA u v, Int.gcdB u v, ?_⟩
  have h := Int.gcd_eq_gcd_ab u v
  rw [hg] at h
  exact_mod_cast h.symm

/-- **A commutative ring that is free of rank two over `ℤ` is a quadratic order** `ℤ[ω]`,
`ω² = a + bω`. With `1 = u e₀ + v e₁` and `uA + vB = 1`, the element `ω = −B e₀ + A e₁` completes
`1` to a basis: `z₀ e₀ + z₁ e₁ = (A z₀ + B z₁) + (u z₁ − v z₀) ω`. -/
theorem exists_algEquiv_quadraticAlgebra (e : Module.Basis (Fin 2) ℤ O) :
    ∃ a b : ℤ, Nonempty (QuadraticAlgebra ℤ a b ≃ₐ[ℤ] O) := by
  have h1 : (1 : O) = e.repr 1 0 • e 0 + e.repr 1 1 • e 1 := by
    have h := e.sum_repr 1
    rw [Fin.sum_univ_two] at h
    exact h.symm
  generalize e.repr 1 0 = u at h1
  generalize e.repr 1 1 = v at h1
  obtain ⟨A, B, hAB⟩ := exists_bezout_of_one_eq e h1
  have hAB' : (u : O) * A + v * B = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hAB
  obtain ⟨ω, hω⟩ : ∃ ω : O, ω = (-B) • e 0 + A • e 1 := ⟨_, rfl⟩
  -- every element is an integer combination of 1 and ω
  have hdecomp : ∀ z : O, z = (A * e.repr z 0 + B * e.repr z 1) • (1 : O) +
      (u * e.repr z 1 - v * e.repr z 0) • ω := by
    intro z
    have hz := e.sum_repr z
    rw [Fin.sum_univ_two] at hz
    generalize e.repr z 0 = z₀ at hz ⊢
    generalize e.repr z 1 = z₁ at hz ⊢
    rw [← hz, hω, h1]
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination (-((z₀ : O) * e 0 + (z₁ : O) * e 1)) * hAB'
  obtain ⟨a, b, hω2⟩ : ∃ a b : ℤ, ω * ω = a • (1 : O) + b • ω := ⟨_, _, hdecomp (ω * ω)⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : QuadraticAlgebra ℤ a b →ₐ[ℤ] O,
      ∀ z, φ z = z.re • (1 : O) + z.im • ω := ⟨QuadraticAlgebra.lift ⟨ω, hω2⟩, fun _ => rfl⟩
  have hsurj : Function.Surjective φ := fun z =>
    ⟨⟨A * e.repr z 0 + B * e.repr z 1, u * e.repr z 1 - v * e.repr z 0⟩, by
      rw [hφ]
      exact (hdecomp z).symm⟩
  -- the combination x + yω has coordinates (xu − yB, xv + yA) in the given basis
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).mpr fun z hz => ?_
    rw [hφ] at hz
    have hcomb : z.re • (1 : O) + z.im • ω =
        (z.re * u - z.im * B) • e 0 + (z.re * v + z.im * A) • e 1 := by
      rw [hω, h1]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    rw [hcomb] at hz
    have h0' : z.re * u - z.im * B = 0 := by
      have h := repr_pair_zero e (z.re * u - z.im * B) (z.re * v + z.im * A)
      rw [hz, map_zero e.repr] at h
      exact h.symm
    have h1'' : z.re * v + z.im * A = 0 := by
      have h := repr_pair_one e (z.re * u - z.im * B) (z.re * v + z.im * A)
      rw [hz, map_zero e.repr] at h
      exact h.symm
    refine QuadraticAlgebra.ext ?_ ?_
    · show z.re = 0
      linear_combination A * h0' + B * h1'' - z.re * hAB
    · show z.im = 0
      linear_combination u * h1'' - v * h0' - z.im * hAB
  exact ⟨a, b, ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩⟩

end RankTwo

/-- **The ring of integers of a quadratic field is a quadratic order of the same discriminant**:
`𝓞 K ≃ₐ[ℤ] ℤ[ω]` with `ω² = a + bω` and `disc K = b² + 4a`. -/
theorem exists_quadraticAlgebra_equiv (K : Type*) [Field K] [NumberField K]
    (h2 : Module.finrank ℚ K = 2) :
    ∃ a b : ℤ, discr K = b ^ 2 + 4 * a ∧ Nonempty (QuadraticAlgebra ℤ a b ≃ₐ[ℤ] 𝓞 K) := by
  have hrank : Module.finrank ℤ (𝓞 K) = 2 := (RingOfIntegers.rank K).trans h2
  obtain ⟨a, b, ⟨ψ⟩⟩ :=
    exists_algEquiv_quadraticAlgebra (Module.finBasisOfFinrankEq ℤ (𝓞 K) hrank)
  refine ⟨a, b, ?_, ⟨ψ⟩⟩
  rw [← NumberField.discr_eq_discr K ((QuadraticAlgebra.basis a b).map ψ.toLinearEquiv),
    Module.Basis.coe_map, ← discr_quadraticAlgebra a b]
  exact (Algebra.discr_eq_discr_of_algEquiv _ ψ).symm

end GaloisForLFunctions.RHTower.Deuring
