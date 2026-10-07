import GaloisForLFunctions.HTGeometry.MeromorphicRationalPoleLift
import GaloisForLFunctions.HTGeometry.PolynomialPoleTransform
import GaloisForLFunctions.RHTower.XiEntireRational
import GaloisForLFunctions.RHTower.XiMeromorphicPolynomial

/-!
# Rational left factors over the global meromorphic plane

For every real exponential tilt of Xi, a coprime rational outer factor has
degree one. A finite outer pole gives an entire reciprocal coordinate;
polynomial reflection transports its equation without losing degree or
coprimality, and entire rational rigidity closes the argument.
-/

open Complex Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every rational left factor of tilted Xi over the meromorphic plane has degree one. -/
theorem xi_rational_plane_factor_max_natDegree_eq_one (a : ℝ) (p q : Polynomial ℂ)
    (hpq : IsCoprime p q) (x : MeromorphicPlane)
    (hrel : Polynomial.aeval x p = xiCubicParameterElement a * Polynomial.aeval x q) :
    max p.natDegree q.natDegree = 1 := by
  have hqx : Polynomial.aeval x q ≠ 0 := by
    intro he
    have hpz : Polynomial.aeval x p = 0 := by rw [hrel, he, mul_zero]
    exact (Polynomial.aeval_ne_zero_of_isCoprime hpq x).elim (fun hn => hn hpz) (fun hn => hn he)
  have hq : q ≠ 0 := by intro he; simp [he] at hqx
  by_cases hqdeg : q.natDegree = 0
  · have hqc := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have hc : q.coeff 0 ≠ 0 := by
      intro he
      rw [hqc, Polynomial.aeval_C, he, map_zero] at hqx
      exact hqx rfl
    have hmc : algebraMap ℂ MeromorphicPlane (q.coeff 0) ≠ 0 := by
      rwa [hqc, Polynomial.aeval_C] at hqx
    have he : Polynomial.aeval x (Polynomial.C (q.coeff 0)⁻¹ * p) = xiCubicParameterElement a := by
      rw [map_mul, Polynomial.aeval_C, map_inv₀, hrel]
      conv_lhs => arg 2; arg 2; rw [hqc, Polynomial.aeval_C]
      field_simp
    have hpdeg := xi_polynomial_plane_factor_natDegree_eq_one a _ x he
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hc)] at hpdeg
    simp [hpdeg, hqdeg]
  have hqpos := Nat.pos_of_ne_zero hqdeg
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root q (by
    rw [Polynomial.degree_eq_natDegree hq]
    exact_mod_cast (Nat.ne_of_gt hqpos))
  have hpb : p.eval b ≠ 0 := by
    have he := Polynomial.aeval_ne_zero_of_isCoprime hpq b
    simpa [Polynomial.coe_aeval_eq_eval, show q.eval b = 0 from hb] using he
  have hp : p ≠ 0 := by intro he; simp [he] at hpb
  have hx : x - algebraMap ℂ MeromorphicPlane b ≠ 0 := by
    intro he
    have hxb := sub_eq_zero.mp he
    have hz : algebraMap ℂ MeromorphicPlane (p.eval b) = 0 := by
      simpa only [hxb, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        show q.eval b = 0 from hb, map_zero, mul_zero] using hrel
    exact hpb ((algebraMap ℂ MeromorphicPlane).injective (hz.trans (map_zero _).symm))
  have hd := xiCubicParameter_differentiable a
  obtain ⟨h, hh, hhe⟩ := entire_reciprocal_lift_of_plane hd p q b hpb hb x hrel
  let y := ofMeromorphic h (fun z => (hh.analyticAt z).meromorphicAt)
  have hy : y ≠ 0 := by dsimp [y]; rw [hhe]; exact inv_ne_zero hx
  have hyx : y⁻¹ + algebraMap ℂ MeromorphicPlane b = x := by
    dsimp [y]
    rw [hhe, inv_inv]
    ring
  let N := max p.natDegree q.natDegree
  let A := polynomialPoleTransform p b N
  let B := polynomialPoleTransform q b N
  have hAB : IsCoprime A B := isCoprime_polynomialPoleTransform p q b hp hq hpq
  have hfield : Polynomial.aeval y A = xiCubicParameterElement a * Polynomial.aeval y B := by
    dsimp [A, B]
    rw [aeval_polynomialPoleTransform p b N (le_max_left _ _) y hy,
      aeval_polynomialPoleTransform q b N (le_max_right _ _) y hy, hyx, hrel]
    ring
  have hpoint : ∀ z : ℂ, A.eval (h z) =
      (xi z * Complex.exp (-(a : ℂ) * z)) * B.eval (h z) := by
    dsimp [y] at hfield
    rw [aeval_ofMeromorphic A, aeval_ofMeromorphic B,
      xiCubicParameterElement, ofMeromorphic_mul] at hfield
    have he := (ofMeromorphic_eq_iff _ _).mp hfield
    intro z
    have hv := ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (A.continuousAt.comp hh.continuous.continuousAt)
      (hd.continuous.continuousAt.mul (B.continuousAt.comp hh.continuous.continuousAt))).mp
        (he z)).eq_of_nhds
    exact hv
  have hAde := (xi_entire_rational_left_factor_degrees a A B hAB hh hpoint).2
  exact (natDegree_polynomialPoleTransform p b N (le_max_left _ _) hpb).symm.trans hAde

end RHTower
