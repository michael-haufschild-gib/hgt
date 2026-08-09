import GaloisForLFunctions.HTGeometry.CauchyCoordinateHalfPlane
import GaloisForLFunctions.HTGeometry.DiscPolynomialDensity

/-!
# Runge approximation on a half-plane by one Cauchy coordinate

A function holomorphic on the right half-plane is, uniformly on every compact subset, a limit of
polynomials in the single Cauchy coordinate `z ↦ (z + a)⁻¹`.

The proof is the composition of the coordinate bricks: the coordinate carries the half-plane
bijectively onto a disc, holomorphy transports, a compact set lands in a strictly smaller disc, and
on a disc the Cauchy power series already approximates by polynomials.

* `HTGeometry.exists_partialSum_cauchyCoordinate_approx`.
-/

open Metric

namespace HTGeometry

/-- **Runge approximation on a half-plane by one Cauchy coordinate.**  For `f` holomorphic on
`{Re z > 0}` and `K` compact inside it, a partial sum of the Cauchy series of the transported
function, evaluated at the coordinate `(z + a)⁻¹ - 1/(2a)`, approximates `f` uniformly on `K`. -/
theorem exists_partialSum_cauchyCoordinate_approx {a : ℝ} (ha : 0 < a) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re}) {K : Set ℂ} (hK : IsCompact K)
    (hKsub : ∀ z ∈ K, 0 < z.re) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (Rn : NNReal) (G : ℂ → ℂ), ∀ z ∈ K,
      ‖f z - (cauchyPowerSeries G 0 (Rn : ℝ)).partialSum n
        ((z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ))‖ < ε := by
  classical
  set c : ℝ := 1 / (2 * a) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨ρ, hρ0, hρc, hρK⟩ := exists_radius_lt_of_isCompact_re_pos ha hK hKsub
  obtain ⟨R, hρR, hRc⟩ := exists_between hρc
  have hR0 : 0 ≤ R := le_trans hρ0 (le_of_lt hρR)
  set Rn : NNReal := ⟨R, hR0⟩ with hRn
  set ρn : NNReal := ⟨ρ, hρ0⟩ with hρn
  have hRcoe : (Rn : ℝ) = R := rfl
  have hρcoe : (ρn : ℝ) = ρ := rfl
  have hRnpos : 0 < Rn := by
    have hRpos : (0 : ℝ) < R := lt_of_le_of_lt hρ0 hρR
    rw [← NNReal.coe_pos, hRcoe]
    exact hRpos
  have hlt : ρn < Rn := by
    rw [← NNReal.coe_lt_coe, hρcoe, hRcoe]
    exact hρR
  set G : ℂ → ℂ := fun v => f ((v + (c : ℂ))⁻¹ - (a : ℂ)) with hG
  have hGdiff : DifferentiableOn ℂ G (closedBall (0 : ℂ) (Rn : ℝ)) := by
    intro v hv
    have hvnorm : ‖v‖ ≤ R := by
      have hb := mem_closedBall_zero_iff.1 hv
      rw [hRcoe] at hb
      exact hb
    have hmem : v + (c : ℂ) ∈ ball ((c : ℝ) : ℂ) c := by
      rw [mem_ball, Complex.dist_eq]
      have hred : v + (c : ℂ) - ((c : ℝ) : ℂ) = v := by ring
      rw [hred]
      exact lt_of_le_of_lt hvnorm hRc
    have houter := differentiableOn_transport_of_re_pos ha hf
    have hinner : DifferentiableAt ℂ (fun u : ℂ => u + (c : ℂ)) v := by fun_prop
    have hout : DifferentiableAt ℂ (fun w : ℂ => f (w⁻¹ - (a : ℂ))) (v + (c : ℂ)) :=
      houter.differentiableAt (isOpen_ball.mem_nhds hmem)
    exact ((hout.comp v hinner)).differentiableWithinAt
  have hmaps : Set.MapsTo (fun z : ℂ => (z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)) K
      (closedBall (0 : ℂ) (ρn : ℝ)) := by
    intro z hz
    rw [mem_closedBall_zero_iff, hρcoe]
    exact hρK z hz
  obtain ⟨n, hn⟩ := exists_partialSum_comp_approx hRnpos hGdiff hlt _ hmaps hε
  refine ⟨n, Rn, G, fun z hz => ?_⟩
  have hval := hn z hz
  have hzne : z + (a : ℂ) ≠ 0 := by
    intro hcon
    have hre : z.re + a = 0 := by
      have hc' := congrArg Complex.re hcon
      simpa using hc'
    have hp := hKsub z hz
    linarith
  have hGval : G ((z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)) = f z := by
    rw [hG]
    show f (((z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ) + (c : ℂ))⁻¹ - (a : ℂ)) = f z
    have hsimp : ((z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ) + (c : ℂ)) = (z + (a : ℂ))⁻¹ := by
      rw [hc]
      ring
    rw [hsimp, inv_inv]
    ring_nf
  rw [hGval] at hval
  exact hval

end HTGeometry
