import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph
import GaloisForLFunctions.HTGeometry.GramDeterminantDistance

/-!
# Concrete polynomials behind the `L²(μ)` monomial span

The abstract Gram–Schmidt vectors of the analytic monomials in `L²(μ)` are, almost everywhere, the
values of concrete polynomials.  This bridge turns the abstract least-squares norm `‖Φ_N‖²` into the
concrete integral `∫ |monic polynomial|² dμ`, the object on which the classical Szegő lower bound
(Jensen against the absolutely continuous part) operates.

* `coeFn_sum_smul_circleMonomialLp` — a finite `ℂ`-combination of monomials evaluates as the
  corresponding polynomial almost everywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

/-- **Abstract-to-concrete polynomial bridge.**  A finite `ℂ`-linear combination of the analytic
monomials in `L²(μ)` has, almost everywhere, the value of the corresponding polynomial. -/
theorem coeFn_sum_smul_circleMonomialLp (mu : Measure Circle) [IsFiniteMeasure mu]
    (s : Finset ℕ) (c : ℕ → ℂ) :
    ⇑(∑ i ∈ s, c i • circleMonomialLp mu i)
      =ᵐ[mu] fun z : Circle => ∑ i ∈ s, c i * (z : ℂ) ^ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 mu
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • circleMonomialLp mu a)
          (∑ i ∈ S, c i • circleMonomialLp mu i),
        Lp.coeFn_smul (c a) (circleMonomialLp mu a),
        circleMonomialLp_coeFn_ae mu a, ih] with z hadd hsmul hmono htail
      rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hmono, htail, Finset.sum_insert ha,
        smul_eq_mul]

/-- **The `L²(μ)` squared norm is the integral of the squared pointwise norm.**  This turns the
abstract Hilbert-space norm of a monomial combination into the concrete integral `∫ |p|² dμ` that the
classical Szegő lower bound bounds below. -/
theorem norm_sq_eq_integral_norm_sq (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    ‖f‖ ^ 2 = ∫ z : Circle, ‖f z‖ ^ 2 ∂mu := by
  have hint : (inner ℂ f f : ℂ) = ((∫ z : Circle, ‖f z‖ ^ 2 ∂mu : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [show ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) from (inner_self_eq_norm_sq f).symm, hint]
  simp

/-- **The monic OPUC element is a concrete monic polynomial.**  The Gram–Schmidt vector of the
analytic monomials at level `N` has, almost everywhere, the value of a monic degree-`N` polynomial
`zᴺ - ∑_{i<N} cᵢ zⁱ`. -/
theorem gramSchmidt_circleMonomial_coeFn_poly (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    ∃ c : ℕ → ℂ, ⇑(gramSchmidt ℂ (circleMonomialLp mu) N)
      =ᵐ[mu] fun z : Circle => (z : ℂ) ^ N - ∑ i ∈ Finset.range N, c i * (z : ℂ) ^ i := by
  classical
  set cm := circleMonomialLp mu with hcm
  have himg : cm '' Set.Iio N = Set.range (fun i : Fin N => cm (i : ℕ)) := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨↑i, i.2, rfl⟩
  have hmem : cm N - gramSchmidt ℂ cm N ∈
      Submodule.span ℂ (Set.range (fun i : Fin N => cm (i : ℕ))) := by
    have h := sub_gramSchmidt_mem_span cm N
    rwa [span_gramSchmidt_Iio ℂ cm N, himg] at h
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨cF, hcF⟩ := hmem
  set c : ℕ → ℂ := fun j => if h : j < N then cF ⟨j, h⟩ else 0 with hcdef
  have hsum_eq : ∑ i : Fin N, cF i • cm (i : ℕ) = ∑ j ∈ Finset.range N, c j • cm j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => c j • cm j) N]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    simp only [hcdef]
    rw [dif_pos i.2]
  refine ⟨c, ?_⟩
  have hgs : gramSchmidt ℂ cm N = cm N - ∑ j ∈ Finset.range N, c j • cm j := by
    rw [← hsum_eq, hcF]; abel
  rw [hgs]
  filter_upwards [Lp.coeFn_sub (cm N) (∑ j ∈ Finset.range N, c j • cm j),
    circleMonomialLp_coeFn_ae mu N,
    coeFn_sum_smul_circleMonomialLp mu (Finset.range N) c] with z h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- **The squared monic OPUC norm as a concrete polynomial integral.**  `‖Φ_N‖²_{L²(μ)}` equals
`∫ |monic degree-N polynomial|² dμ`.  This is the exact object on which the classical Szegő lower
bound operates. -/
theorem normSq_gramSchmidt_circleMonomial_eq_integral
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    ∃ c : ℕ → ℂ, ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ ^ 2
      = ∫ z : Circle, ‖(z : ℂ) ^ N - ∑ i ∈ Finset.range N, c i * (z : ℂ) ^ i‖ ^ 2 ∂mu := by
  obtain ⟨c, hc⟩ := gramSchmidt_circleMonomial_coeFn_poly mu N
  refine ⟨c, ?_⟩
  rw [norm_sq_eq_integral_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [hc] with z hz
  rw [hz]

end GaloisForLFunctions.HTGeometry
