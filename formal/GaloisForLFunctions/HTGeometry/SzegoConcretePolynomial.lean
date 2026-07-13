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
open scoped InnerProductSpace ComplexConjugate

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

/-- The monic degree-`N` polynomial `zᴺ - ∑_{i<N} cᵢ zⁱ`. -/
noncomputable def monicPoly (c : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  z ^ N - ∑ i ∈ Finset.range N, c i * z ^ i

/-- The reversed polynomial `1 - ∑_{i<N} conj(cᵢ) z^{N-i}`, analytic with value `1` at the origin
and equal modulus to `monicPoly` on the unit circle. -/
noncomputable def revPoly (c : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  1 - ∑ i ∈ Finset.range N, conj (c i) * z ^ (N - i)

/-- The reversed polynomial takes the value `1` at the origin. -/
theorem revPoly_zero (c : ℕ → ℂ) (N : ℕ) : revPoly c N 0 = 1 := by
  unfold revPoly
  have h : ∀ i ∈ Finset.range N, conj (c i) * (0 : ℂ) ^ (N - i) = 0 := fun i hi => by
    rw [zero_pow (Nat.sub_pos_of_lt (Finset.mem_range.mp hi)).ne', mul_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_const_zero, sub_zero]

/-- On the unit circle the reversed polynomial equals `zᴺ · conj(q z)`. -/
theorem revPoly_eq_on_circle (c : ℕ → ℂ) (N : ℕ) (z : Circle) :
    revPoly c N (z : ℂ) = (z : ℂ) ^ N * conj (monicPoly c N (z : ℂ)) := by
  have hz : (z : ℂ) * conj (z : ℂ) = 1 := by
    rw [Complex.mul_conj]; norm_cast
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]; norm_num
  have hpow : ∀ i, i ≤ N → (z : ℂ) ^ N * conj (z : ℂ) ^ i = (z : ℂ) ^ (N - i) := by
    intro i hi
    conv_lhs => rw [show (z : ℂ) ^ N = (z : ℂ) ^ (N - i) * (z : ℂ) ^ i from by
      rw [← pow_add, Nat.sub_add_cancel hi]]
    rw [mul_assoc, ← mul_pow, hz, one_pow, mul_one]
  unfold revPoly monicPoly
  rw [map_sub, map_pow, mul_sub, map_sum, Finset.mul_sum]
  congr 1
  · rw [← mul_pow, hz, one_pow]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [map_mul, map_pow, mul_left_comm, hpow i (Finset.mem_range.mp hi).le]

/-- The reversed polynomial has the same modulus as the monic polynomial on the unit circle. -/
theorem norm_revPoly_eq_on_circle (c : ℕ → ℂ) (N : ℕ) (z : Circle) :
    ‖revPoly c N (z : ℂ)‖ = ‖monicPoly c N (z : ℂ)‖ := by
  rw [revPoly_eq_on_circle, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul,
    RCLike.norm_conj]

/-- **The squared monic OPUC norm equals `∫ |q*|² dμ` for the value-`1`-at-origin reversed
polynomial.**  This is the form on which the classical Szegő inequality `∫|q*|²dμ ≥ |q*(0)|²·GM = GM`
operates (Jensen against the absolutely continuous part). -/
theorem normSq_gramSchmidt_circleMonomial_eq_integral_revPoly
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    ∃ c : ℕ → ℂ, ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ ^ 2
      = ∫ z : Circle, ‖revPoly c N (z : ℂ)‖ ^ 2 ∂mu := by
  obtain ⟨c, hc⟩ := normSq_gramSchmidt_circleMonomial_eq_integral mu N
  refine ⟨c, ?_⟩
  rw [hc]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [norm_revPoly_eq_on_circle, monicPoly]

end GaloisForLFunctions.HTGeometry
