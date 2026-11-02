import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.ZeroExponentSplineNullseries
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineQuartets

/-!
# Exact spline quartets with zero exponent of convergence

The same sparse nullseries retains every positive inverse-power ordinate sum.
Finite sign and conjugation copies preserve this density bound and the exact
spline coefficients while their natural two-prime cone coupling stays bounded.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Finite sign and conjugation copies preserve inverse-power summability. -/
lemma summable_prescribedSplineQuartet_inverse_power {ι : Type*} (z : ι → ℂ)
    (him : ∀ i, 0 ≤ (z i).im) {ε : ℝ}
    (hs : Summable (fun i => (1+(z i).im)^(-ε))) :
    Summable (fun i : ι × Bool × Bool =>
      (1+|(prescribedSplineQuartetAtom z i).im|)^(-ε)) := by
  have hfin : Summable (fun _ : Bool × Bool => (1:ℝ)) := Summable.of_finite
  have hh := summable_mul_of_summable_norm hs.norm hfin.norm
  refine hh.congr ?_
  rintro ⟨i,b,c⟩
  cases b <;> cases c <;>
    simp [prescribedSplineQuartetAtom,abs_of_nonneg (him i)]

/-- Exact unit-multiplicity spline quartets have unattained positive width,
zero exponent of convergence, bounded natural two-prime cone coupling,
and at most twelve atoms per unit height interval. -/
theorem exists_two_prime_zero_exponent_prescribed_spline_cone_model {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ),
      Function.Injective z ∧ Function.Injective (prescribedSplineQuartetAtom z) ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧ (∀ i, 1 ≤ (z i).im) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, splineMomentCoefficient (z i) ≠ 0) ∧
      Summable (fun i => ‖splineMomentCoefficient (z i)‖) ∧
      (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2 ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3)) ∧
      (∀ T : ℝ, Nonempty ({i : ι × Bool × Bool //
        (prescribedSplineQuartetAtom z i).im ∈ Set.Icc T (T+1)} ↪ Fin 12)) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun i => (1+(z i).im)^(-ε))) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun i : ι × Bool × Bool =>
        (1+|(prescribedSplineQuartetAtom z i).im|)^(-ε))) ∧
      (∀ t : ℝ, Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i))) ∧
      (∀ t : PositiveCone (Real.log p) (Real.log q),
        HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t.val : ℂ)*z i)) 0) ∧
      (∀ m n : ℕ, ‖prescribedSplineQuartetKernel z (m*Real.log p+n*Real.log q)-
        prescribedSplineQuartetKernel z (m*Real.log p)-prescribedSplineQuartetKernel z (n*Real.log q)+
        prescribedSplineQuartetKernel z 0‖ ≤ 20) := by
  obtain ⟨ι,hι,z,hinj,hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hlocal,hinverse,hall,hzero⟩ :=
    exists_two_prime_zero_exponent_prescribed_spline_nullseries hp hq hpq hd hdD
  refine ⟨ι,hι,z,hinj,prescribedSplineQuartetAtom_injective hinj
    (fun i => hd.trans_le (hstrip i).1) (fun i => zero_lt_one.trans_le (him i)),
    hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hlocal,
    prescribedSplineQuartet_unit_interval_embedding z hlocal,hinverse,
    (fun ε hε => summable_prescribedSplineQuartet_inverse_power z
      (fun i => zero_le_one.trans (him i)) (hinverse ε hε)),hall,hzero,?_⟩
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  exact prescribed_spline_quartet_coupling_le_twenty z ha hb hs hmass
    (fun i => hd.le.trans (hstrip i).1) hzero

#print axioms summable_prescribedSplineQuartet_inverse_power
#print axioms exists_two_prime_zero_exponent_prescribed_spline_cone_model
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
