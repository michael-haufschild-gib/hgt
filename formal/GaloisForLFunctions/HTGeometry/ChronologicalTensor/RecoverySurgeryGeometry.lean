import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryWedge
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryInertia
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryHausdorff
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryFlow

/-!
# The complete geometric delayed-obstruction theorem

Every clause is attached to the explicit planar surgery domain and its actual
quotient norms. The family has a precisely delayed negative square, exact
Hankel inertia, strict adjacent curvature, Hausdorff convergence, and the same
thermal Mellin zero divisor. Arbitrarily small Hausdorff neighborhoods of the
positive-moment wedge contain nonrepresentable geometries passing any chosen
finite degree of square tests.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory Filter Topology Complex
open _root_.HTGeometry

theorem recoverySurgeryFamily_hausdorff_tendsto :
    Tendsto (fun j : ℕ => Metric.hausdorffDist
      (recoverySurgeryDomain ((2 : ℕ)^(j+4)-1)) recoveryWedge) atTop (𝓝 0) := by
  have h : ∀ j : ℕ, j ≤ (2 : ℕ)^(j+4)-1 := by
    intro j
    have hp := (j+4).lt_two_pow_self
    omega
  exact recoverySurgeryDomain_hausdorff_tendsto.comp (tendsto_atTop_mono h tendsto_id)

theorem recoverySurgery_full_geometric_theorem (j : ℕ) :
    let N := (2 : ℕ)^(j+4)
    let n := N-1
    let d := (2 : ℕ)^(j+3)
    IsCompact (recoverySurgeryDomain n) ∧
    (interior (recoverySurgeryDomain n)).Nonempty ∧
    ¬ Convex ℝ (recoverySurgeryDomain n) ∧
    (∀ p : ℝ × ℝ, p ∈ recoverySurgeryDomain n ↔
      ∀ i : Fin 6, 0 ≤ recoveryPlaneEval (recoverySurgeryConstraints n i) p) ∧
    (∀ p ∈ recoverySurgeryDomain n, ∀ q : Icc (0 : ℝ) 1,
      (q.val*p.1,q.val*p.2) ∈ recoverySurgeryDomain n) ∧
    (∀ k : Fin N, recoverySurgeryGap n k.val=recoveryWedgeActualGap k.val) ∧
    (recoverySurgeryCorePower n*recoveryWedgeActualGap N ≤ recoverySurgeryGap n N ∧
      recoverySurgeryGap n N ≤ recoverySurgeryHeight n*recoveryWedgeActualGap N) ∧
    (∀ k : Fin n, (recoverySurgeryGap n (k.val+1))^(2 : ℕ) <
      recoverySurgeryGap n k.val*recoverySurgeryGap n (k.val+2)) ∧
    (∃ P : ℝ[X], P.natDegree=d ∧ momentFunctional (recoverySurgeryMoment n) (P^(2 : ℕ)) < 0 ∧
      ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < d → 0 < momentFunctional (recoverySurgeryMoment n) (Q^(2 : ℕ))) ∧
    (sigPos (recoveryHankelForm n d)=d ∧ sigNeg (recoveryHankelForm n d)=1 ∧
      Module.finrank ℝ (recoveryHankelForm n d).radical=0) ∧
    (¬ ∃ μ : Measure ℝ, (∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ) ∧
      ∀ k : ℕ, recoverySurgeryMoment n k=∫ x, x^k ∂μ) ∧
    (Metric.hausdorffDist (recoverySurgeryDomain n) recoveryWedge ≤ 33/(32*(n+2 : ℝ)^(2 : ℕ))) ∧
    EqOn (mellin (recoverySurgeryResponseKernel n)) (fun s => -Complex.Gamma s*riemannZeta s)
      fusionMellinStrip ∧
    EqOn (analyticOrderAt (mellin (recoverySurgeryResponseKernel n)))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  let N := (2 : ℕ)^(j+4)
  let n := N-1
  have hp : 0 < N := by dsimp [N]; positivity
  have hn : n+1=N := Nat.sub_add_cancel (by omega)
  refine ⟨recoverySurgeryDomain_compact n,recoverySurgeryDomain_interior n,
    recoverySurgeryDomain_not_convex n,recoverySurgeryDomain_polynomial_inequalities n,
    ?_,?_,?_,recoverySurgeryGap_prefix_strict_logconvex n,
    recoverySurgery_dyadic_first_failure j,recoverySurgery_dyadic_inertia j,
    recoverySurgery_dyadic_no_measure j,recoverySurgeryDomain_hausdorff_bound n,
    recoverySurgeryResponseKernel_mellin n,recoverySurgeryResponseKernel_zeroMultiplicity n⟩
  · intro p hp q
    exact recoverySurgeryDomain_radial n p hp q.val q.property
  · intro k
    rw [recoveryWedgeActualGap_eq]
    exact recoverySurgeryGap_prefix n ⟨k.val,by rw [hn]; exact k.isLt⟩
  · rw [recoveryWedgeActualGap_eq]
    constructor
    · simpa only [hn] using recoverySurgeryGap_drop_lower n
    · simpa only [hn] using recoverySurgeryGap_drop_upper n

theorem recoverySurgery_arbitrarily_close_delayed_obstruction (r : ℕ) (ε : Ioi (0 : ℝ)) :
    ∃ j : ℕ,
      Metric.hausdorffDist (recoverySurgeryDomain ((2 : ℕ)^(j+4)-1)) recoveryWedge < ε.val ∧
      (∀ P : ℝ[X], P ≠ 0 → P.natDegree ≤ r →
        0 < momentFunctional (recoverySurgeryMoment ((2 : ℕ)^(j+4)-1)) (P^(2 : ℕ))) ∧
      ¬ ∃ μ : Measure ℝ, (∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ) ∧
        ∀ k : ℕ, recoverySurgeryMoment ((2 : ℕ)^(j+4)-1) k=∫ x, x^k ∂μ := by
  have hε := (tendsto_order.mp recoverySurgeryFamily_hausdorff_tendsto).2 ε.val ε.property
  obtain ⟨j,hj,hjr⟩ := (hε.and (eventually_ge_atTop r)).exists
  refine ⟨j,hj,?_,recoverySurgery_dyadic_no_measure j⟩
  intro P hP hd
  obtain ⟨Q,hQ,hneg,hsmall⟩ := recoverySurgery_dyadic_first_failure j
  apply hsmall P hP
  have hp := (j+3).lt_two_pow_self
  omega

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
