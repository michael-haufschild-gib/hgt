import GaloisForLFunctions.HTGeometry.NoncompactPeriodQuotient

/-!
# Generalized Riemann relations for a complex-independent period lattice

A quasi-Abelian period quotient must carry a positive-definite Hermitian form whose imaginary part
is integral on the period lattice.  When the lattice is the integral span of a complex basis the
form can be written down: declare that basis orthonormal.  Positive definiteness is then the sum of
squared coordinate moduli, and the imaginary part vanishes identically on the lattice, since lattice
coordinates are integers and the form of two integral vectors is a real integer.

`exists_hermitian_positive_integral_of_basis` packages the five clauses in exactly the shape a
quasi-Abelian facet certificate requires.
-/

open Finset Module

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : Type*} [Fintype ι]

/-- The Hermitian form making a given complex basis orthonormal. -/
noncomputable def basisHermitian (b : Basis ι ℂ W) (x y : W) : ℂ :=
  ∑ i, b.repr x i * star (b.repr y i)

theorem basisHermitian_add_left (b : Basis ι ℂ W) (x y z : W) :
    basisHermitian b (x + y) z = basisHermitian b x z + basisHermitian b y z := by
  simp only [basisHermitian, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem basisHermitian_smul_left (b : Basis ι ℂ W) (a : ℂ) (x y : W) :
    basisHermitian b (a • x) y = a * basisHermitian b x y := by
  simp only [basisHermitian, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem basisHermitian_hermitian (b : Basis ι ℂ W) (x y : W) :
    basisHermitian b y x = star (basisHermitian b x y) := by
  simp only [basisHermitian, star_sum, star_mul, star_star]

theorem basisHermitian_self_re (b : Basis ι ℂ W) (x : W) :
    (basisHermitian b x x).re = ∑ i, Complex.normSq (b.repr x i) := by
  have hterm : ∀ i : ι, b.repr x i * star (b.repr x i)
      = ((Complex.normSq (b.repr x i) : ℝ) : ℂ) := by
    intro i
    rw [Complex.star_def, Complex.mul_conj]
  simp only [basisHermitian, hterm]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-- **The form is positive definite.** -/
theorem basisHermitian_pos (b : Basis ι ℂ W) {x : W} (hx : x ≠ 0) :
    0 < (basisHermitian b x x).re := by
  rw [basisHermitian_self_re]
  have hrepr : b.repr x ≠ 0 := by
    intro hcon
    exact hx (by simpa using congrArg b.repr.symm hcon)
  obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hrepr (Finsupp.ext fun i => by simpa using hcon i)
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact Complex.normSq_pos.mpr hi

omit [Fintype ι] in
/-- Coordinates of a point of the integral lattice of a basis are integers. -/
theorem exists_int_repr_of_mem_closure (b : Basis ι ℂ W) {x : W}
    (hx : x ∈ AddSubgroup.closure (Set.range (b : ι → W))) (i : ι) :
    ∃ n : ℤ, b.repr x i = (n : ℂ) := by
  have hsub : AddSubgroup.closure (Set.range (b : ι → W)) ≤
      AddSubgroup.comap ((Finsupp.applyAddHom i).comp
        (b.repr.toLinearMap.toAddMonoidHom)) (AddSubgroup.zmultiples (1 : ℂ)) := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨j, rfl⟩
    simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
      AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe, Finsupp.applyAddHom_apply, Basis.repr_self]
    rw [AddSubgroup.mem_zmultiples_iff]
    by_cases hij : i = j
    · exact ⟨1, by simp [hij]⟩
    · exact ⟨0, by simp [hij]⟩
  have hmem := hsub hx
  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, Finsupp.applyAddHom_apply] at hmem
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, by rw [← hn]; simp⟩

/-- **The imaginary part vanishes on the integral lattice of the basis.** -/
theorem im_basisHermitian_eq_zero_of_mem_closure (b : Basis ι ℂ W) {x y : W}
    (hx : x ∈ AddSubgroup.closure (Set.range (b : ι → W)))
    (hy : y ∈ AddSubgroup.closure (Set.range (b : ι → W))) :
    (basisHermitian b x y).im = 0 := by
  have hterm : ∀ i : ι, (b.repr x i * star (b.repr y i)).im = 0 := by
    intro i
    obtain ⟨n, hn⟩ := exists_int_repr_of_mem_closure b hx i
    obtain ⟨m, hm⟩ := exists_int_repr_of_mem_closure b hy i
    rw [hn, hm, Complex.star_def, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]
  simp only [basisHermitian, Complex.im_sum, hterm, Finset.sum_const_zero]

/-- **Generalized Riemann relations for the integral span of a complex basis.**  Positive-definite
Hermitian form with integral imaginary part on the lattice, in the shape a quasi-Abelian facet
certificate requires. -/
theorem exists_hermitian_positive_integral_of_basis (b : Basis ι ℂ W) :
    ∃ H : W → W → ℂ,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ (a : ℂ) (x y), H (a • x) y = a * H x y) ∧
      (∀ x y, H y x = star (H x y)) ∧
      (∀ x, x ≠ 0 → 0 < (H x x).re) ∧
      (∀ x ∈ AddSubgroup.closure (Set.range (b : ι → W)),
        ∀ y ∈ AddSubgroup.closure (Set.range (b : ι → W)), ∃ n : ℤ, (H x y).im = (n : ℝ)) := by
  refine ⟨basisHermitian b, basisHermitian_add_left b, basisHermitian_smul_left b,
    basisHermitian_hermitian b, fun x hx => basisHermitian_pos b hx, ?_⟩
  intro x hx y hy
  exact ⟨0, by simpa using im_basisHermitian_eq_zero_of_mem_closure b hx hy⟩

end GaloisForLFunctions.HTGeometry
