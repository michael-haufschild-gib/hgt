import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# Projective rigidity of a shared clock observation

A family of channels can observe one common clock through a separable matrix

`T i j = clock i * response j`.

The matrix does not determine either factor absolutely: one may multiply the clock by a nonzero
scalar and divide every response by the same scalar.  Once one clock reading and one response are
nonzero, this is the only ambiguity.  Thus the clock is an identifiable projective observation
coordinate, not a temporal flow.

Genomics provenance: the noiseless core of gene-shared latent-time fixation in T. Li, Y. Wang,
G. Yang, and P. Zhou, *On the Mathematics of RNA Velocity II: Algorithmic Aspects*,
arXiv:2306.05707, is a positive rank-one factorization of the cell-by-gene time matrix.  The paper
fixes its remaining global scale by normalization.  The theorem below extracts the exact algebraic
identifiability law and applies it directly to the existing rank-one Gamma clock curvature.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A shared-clock observation matrix separates a common clock coordinate from
channel-specific response factors. -/
def sharedClockObservation {K : Type*} [Mul K] {I J : Type*}
    (clock : I → K) (response : J → K) : Matrix I J K :=
  fun i j ↦ clock i * response j

/-- **Projective shared-clock identifiability.**  Two nonzero factorizations of the same
shared-clock observation matrix differ by a unique global nonzero calibration. -/
theorem sharedClockObservation_factorization_unique_up_to_scale
    {K : Type*} [Field K] {I J : Type*}
    (clock clock' : I → K) (response response' : J → K)
    (i₀ : I) (j₀ : J)
    (hclock : clock i₀ ≠ 0) (hresponse : response j₀ ≠ 0)
    (hfactor : sharedClockObservation clock response =
      sharedClockObservation clock' response') :
    ∃! c : K, c ≠ 0 ∧
      clock' = (fun i ↦ c * clock i) ∧
      response' = (fun j ↦ c⁻¹ * response j) := by
  have hanchor := congrFun (congrFun hfactor i₀) j₀
  simp only [sharedClockObservation] at hanchor
  have hright : clock' i₀ * response' j₀ ≠ 0 := by
    rw [← hanchor]
    exact mul_ne_zero hclock hresponse
  have hclock' : clock' i₀ ≠ 0 := left_ne_zero_of_mul hright
  have hresponse' : response' j₀ ≠ 0 := right_ne_zero_of_mul hright
  let c : K := response j₀ / response' j₀
  have hc : c ≠ 0 := div_ne_zero hresponse hresponse'
  have hclockScale : clock' = fun i ↦ c * clock i := by
    funext i
    have hi := congrFun (congrFun hfactor i) j₀
    simp only [sharedClockObservation] at hi
    dsimp only [c]
    calc
      clock' i = (clock' i * response' j₀) / response' j₀ := by field_simp
      _ = (clock i * response j₀) / response' j₀ := by rw [← hi]
      _ = (response j₀ / response' j₀) * clock i := by field_simp
  have hresponseScale : response' = fun j ↦ c⁻¹ * response j := by
    funext j
    have hj := congrFun (congrFun hfactor i₀) j
    simp only [sharedClockObservation, hclockScale] at hj
    have hcancel : response j = c * response' j := by
      apply mul_left_cancel₀ hclock
      calc
        clock i₀ * response j = (c * clock i₀) * response' j := hj
        _ = clock i₀ * (c * response' j) := by ring
    calc
      response' j = c⁻¹ * (c * response' j) := by simp [hc]
      _ = c⁻¹ * response j := by rw [hcancel]
  refine ⟨c, ⟨hc, hclockScale, hresponseScale⟩, ?_⟩
  intro d hd
  have hd0 := congrFun hd.2.1 i₀
  have hc0 := congrFun hclockScale i₀
  apply mul_right_cancel₀ hclock
  rw [← hd0, ← hc0]

/-- **Gamma clock factorization rigidity.**  At every positive resolution, the exact Gamma
translation curvature determines both its highest-jet source functional and its factorial-tail
observation vector up to one unique global nonzero calibration. -/
theorem gammaClockCurvature_factorization_unique_up_to_scale
    (n : ℕ) (hn : 0 < n)
    (source : (Fin (n + 1) → ℂ) → ℂ) (boundary : Fin n → ℂ)
    (hfactor : ∀ a i, gammaClockCurvature n a i = source a * boundary i) :
    ∃! c : ℂ, c ≠ 0 ∧
      source = (fun a ↦ c * a (Fin.last n)) ∧
      boundary = (fun i ↦ c⁻¹ * gammaClockBoundaryVector n i) := by
  let anchor : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1
  have hsourceAnchor : anchor (Fin.last n) ≠ 0 := by
    simp [anchor]
  let boundaryAnchor : Fin n := ⟨0, hn⟩
  have hboundaryAnchor : gammaClockBoundaryVector n boundaryAnchor ≠ 0 := by
    simp [gammaClockBoundaryVector, boundaryAnchor, Nat.factorial_ne_zero]
  apply sharedClockObservation_factorization_unique_up_to_scale
    (fun a : Fin (n + 1) → ℂ ↦ a (Fin.last n)) source
    (gammaClockBoundaryVector n) boundary anchor boundaryAnchor
    hsourceAnchor hboundaryAnchor
  funext a i
  simp only [sharedClockObservation]
  calc
    a (Fin.last n) * gammaClockBoundaryVector n i =
        gammaClockCurvature n a i := by
      symm
      simpa only [Pi.smul_apply, smul_eq_mul] using
        congrFun (gammaClockCurvature_eq_outerProduct n a) i
    _ = source a * boundary i := hfactor a i

end

end GaloisForLFunctions.HTGeometry
