import GaloisForLFunctions.HTGeometry.BivariateRootCovering
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatTimeSpreadsTheConfiguration

/-!
# Finite exceptional times for polynomial heat

The heat coefficients form a bivariate polynomial. Its resultant with the
spatial derivative specializes to the fibre resultant because heat preserves
degree. Initial separability makes this time polynomial nonzero. Its finite
zero set contains every collision, so each time has a punctured forward
interval of simple fibres, with no monic normalization required.
-/

open Polynomial Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- The polynomial heat family with time retained as a coefficient variable. -/
def polynomialHeatFamily (p : ℂ[X]) : ℂ[X][X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    C ((-X) ^ k * C ((k.factorial : ℂ)⁻¹)) *
      (derivative^[2 * k] p).map (C : ℂ →+* ℂ[X])

/-- Specializing the coefficient variable recovers the actual polynomial heat flow. -/
theorem biFibre_polynomialHeatFamily (p : ℂ[X]) (t : ℂ) :
    biFibre (polynomialHeatFamily p) t = heatFlow t p := by
  have hmap (q : ℂ[X]) :
      (q.map (C : ℂ →+* ℂ[X])).map (evalRingHom t) = q := by
    rw [Polynomial.map_map]
    have hhom : (evalRingHom t).comp (C : ℂ →+* ℂ[X]) = RingHom.id ℂ := by
      ext x
      simp only [RingHom.comp_apply, coe_evalRingHom, eval_C, RingHom.id_apply]
    rw [hhom, Polynomial.map_id]
  simp only [biFibre, polynomialHeatFamily, heatFlow, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, hmap]
  apply Finset.sum_congr rfl
  intro k _
  simp only [coe_evalRingHom, eval_mul, eval_pow, eval_neg, eval_X, eval_C,
    div_eq_mul_inv]

/-- Polynomial heat preserves degree and never annihilates a nonzero polynomial. -/
theorem heatFlow_degree_ne_zero {p : ℂ[X]} (hp : p ≠ 0) (t : ℂ) :
    (heatFlow t p).natDegree = p.natDegree ∧ heatFlow t p ≠ 0 := by
  have hc : (heatFlow t p).coeff p.natDegree ≠ 0 := by
    rw [coeff_heatFlow_top, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero (natDegree_heatFlow_le t p) hc,
    fun h => hc (by rw [h, coeff_zero])⟩

/-- The resultant in the spatial variable, viewed as a polynomial in heat time. -/
def polynomialHeatResultant (p : ℂ[X]) : ℂ[X] :=
  Polynomial.resultant (polynomialHeatFamily p) (polynomialHeatFamily p).derivative
    p.natDegree (p.natDegree - 1)

/-- The time resultant specializes to the full spatial resultant at every fibre. -/
theorem polynomialHeatResultant_eval {p : ℂ[X]} (hp : p ≠ 0) (t : ℂ) :
    (polynomialHeatResultant p).eval t =
      Polynomial.resultant (heatFlow t p) (heatFlow t p).derivative
        (heatFlow t p).natDegree (heatFlow t p).derivative.natDegree := by
  have h := Polynomial.resultant_map_map (f := polynomialHeatFamily p)
    (g := (polynomialHeatFamily p).derivative) (m := p.natDegree)
    (n := p.natDegree - 1) (evalRingHom t)
  have hm : (polynomialHeatFamily p).map (evalRingHom t) = heatFlow t p :=
    biFibre_polynomialHeatFamily p t
  rw [← Polynomial.derivative_map, hm] at h
  simpa only [polynomialHeatResultant, coe_evalRingHom, natDegree_derivative,
    (heatFlow_degree_ne_zero hp t).1] using h.symm

/-- Zero heat time is the identity. -/
theorem heatFlow_zero_time (p : ℂ[X]) : heatFlow 0 p = p := by
  rw [heatFlow, Finset.sum_eq_single 0]
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, C_1,
      mul_zero, Function.iterate_zero, id_eq, one_mul]
  · intro k _ hk
    simp only [neg_zero, zero_pow hk, zero_div, C_0, zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.succ_pos _))).elim

/-- An initially separable nonzero polynomial has only finitely many nonsimple heat fibres. -/
theorem finite_not_separable_heatFlow {p : ℂ[X]} (hp : p ≠ 0) (hs : p.Separable) :
    {t : ℂ | ¬ (heatFlow t p).Separable}.Finite := by
  let R := polynomialHeatResultant p
  have hR0 : R.eval 0 ≠ 0 := by
    dsimp only [R]
    rw [polynomialHeatResultant_eval hp, heatFlow_zero_time]
    exact Polynomial.resultant_ne_zero p p.derivative hs
  have hR : R ≠ 0 := by
    intro hz
    exact hR0 (by rw [hz, eval_zero])
  apply R.roots.toFinset.finite_toSet.subset
  intro t ht
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hR).mpr
  change R.eval t = 0
  dsimp only [R]
  rw [polynomialHeatResultant_eval hp]
  exact Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl (heatFlow_degree_ne_zero hp t).2, ht⟩

/-- Immediately after any real time, all sufficiently close fibres are separable. -/
theorem exists_separable_polynomial_heat_forward {p : ℂ[X]}
    (hp : p ≠ 0) (hs : p.Separable) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Ioo t (t + δ), (heatFlow (s : ℂ) p).Separable := by
  let E : Set ℝ := {s | ¬ (heatFlow (s : ℂ) p).Separable}
  have hE : E.Finite := (finite_not_separable_heatFlow hp hs).preimage
    Complex.ofReal_injective.injOn
  have hE' : (E \ {t}).Finite := hE.sdiff
  have hnear : ∀ᶠ s in 𝓝 t, s ∉ E \ {t} :=
    hE'.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, hδ, fun s hs' => ?_⟩
  have hd : dist s t < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs'.1)]
    linarith only [hs'.2]
  by_contra h
  exact hball hd ⟨h, by simpa only [mem_singleton_iff] using hs'.1.ne'⟩

#print axioms biFibre_polynomialHeatFamily
#print axioms polynomialHeatResultant_eval
#print axioms finite_not_separable_heatFlow
#print axioms exists_separable_polynomial_heat_forward

end
end GaloisForLFunctions.ArithmeticElectrostatics

