import GaloisForLFunctions.HTGeometry.TensorSquareEqualizer
import GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple

/-!
# A semi-invariant solution solves the Riccati equation

A Galois-stable line in the solution space of a second-order difference equation says, in the tensor
square of the Picard--Vessiot ring, that the solution `y` and its shift satisfy
`y ⊗ σ y = σ y ⊗ y`.  That identity already forces `σ y = r y` with `r` in the base: apply a linear
functional taking the value one at `y` to the first factor.

Such a `y` is a unit — the ideal it generates is a `σ`-ideal, and the ring is `σ`-simple — so the
recurrence can be divided by it, and the ratio `r` solves the Riccati equation of the recurrence
over the base field.  A base Riccati solution is exactly a first-order right factor, so an equation
without one has no Galois-stable line.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- **A symmetric tensor square makes one element a base multiple of the other.** -/
theorem exists_eq_algebraMap_mul_of_tmul_comm [Nontrivial R] {y z : R} (hy : y ≠ 0)
    (h : y ⊗ₜ[K] z = z ⊗ₜ[K] y) : ∃ r : K, z = algebraMap K R r * y := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (V := R) K (x := y) hy
  set g : (R ⊗[K] R) →ₗ[K] R :=
    (TensorProduct.lid K R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id with hg
  have hval := congrArg g h
  simp only [hg, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, TensorProduct.lid_tmul, hf, one_smul] at hval
  refine ⟨f z, ?_⟩
  rw [Algebra.smul_def] at hval
  exact hval

/-- A nonzero hyperexponential element of a `σ`-simple ring is a unit. -/
theorem isUnit_of_sigma_eq_smul {σR : R ≃+* R} (hsimple : IsSigmaSimple σR)
    {y : R} (hy : y ≠ 0) {r : K} (hr : σR y = algebraMap K R r * y) : IsUnit y := by
  have hI : IsSigmaIdeal σR (Ideal.span {y}) := by
    intro x hx
    rw [Ideal.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    refine ⟨σR c * algebraMap K R r, ?_⟩
    rw [map_mul, hr]
    ring
  rcases hsimple _ hI with hbot | htop
  · exact absurd (Ideal.span_singleton_eq_bot.mp hbot) hy
  · rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton] at htop
    obtain ⟨u, hu⟩ := htop
    exact isUnit_iff_exists_inv.mpr ⟨u, hu.symm⟩

/-- **A hyperexponential solution solves the Riccati equation over the base.** -/
theorem riccati_of_sigma_eq_smul_without_simple [Nontrivial R]
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    {a₁ a₀ : K} {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y)
    {r : K} (hr : σR y = algebraMap K R r * y) :
    σK r * r = a₁ * r + a₀ := by
  have hsq : σR (σR y) = algebraMap K R (σK r * r) * y := by
    rw [hr, map_mul, hcompat, hr, map_mul]
    ring
  have hcomb : algebraMap K R (σK r * r) * y = algebraMap K R (a₁ * r + a₀) * y := by
    rw [← hsq, hrec, hr, map_add, map_mul]
    ring
  by_contra hne
  have hdiff : σK r * r - (a₁ * r + a₀) ≠ 0 := sub_ne_zero.mpr hne
  have huK : IsUnit (σK r * r - (a₁ * r + a₀)) := isUnit_iff_ne_zero.mpr hdiff
  have huR : IsUnit (algebraMap K R (σK r * r - (a₁ * r + a₀))) :=
    huK.map (algebraMap K R)
  have hzero : algebraMap K R (σK r * r - (a₁ * r + a₀)) * y = 0 := by
    rw [map_sub, sub_mul, hcomb, sub_self]
  have hyzero : y = 0 := huR.mul_left_cancel (by simpa using hzero)
  exact hy hyzero

/-- Compatibility wrapper retaining the earlier `σ`-simple interface. -/
theorem riccati_of_sigma_eq_smul [Nontrivial R] {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (_hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y)
    {r : K} (hr : σR y = algebraMap K R r * y) :
    σK r * r = a₁ * r + a₀ :=
  riccati_of_sigma_eq_smul_without_simple hcompat hy hrec hr

/-- A symmetric tensor solution produces a Riccati solution without a simplicity premise. -/
theorem exists_riccati_of_tmul_comm_without_simple [Nontrivial R]
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    {a₁ a₀ : K} {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y)
    (hsym : y ⊗ₜ[K] σR y = σR y ⊗ₜ[K] y) :
    ∃ r : K, σK r * r = a₁ * r + a₀ := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_mul_of_tmul_comm hy hsym
  exact ⟨r, riccati_of_sigma_eq_smul_without_simple hcompat hy hrec hr⟩

/-- **A semi-invariant solution produces a Riccati solution over the base.** -/
theorem exists_riccati_of_tmul_comm [Nontrivial R] {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} {y : R} (hy : y ≠ 0)
    (hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y)
    (hsym : y ⊗ₜ[K] σR y = σR y ⊗ₜ[K] y) :
    ∃ r : K, σK r * r = a₁ * r + a₀ := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_mul_of_tmul_comm hy hsym
  exact ⟨r, riccati_of_sigma_eq_smul hcompat hsimple hy hrec hr⟩

end

end GaloisForLFunctions.HTGeometry
