import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.QuantitativeGain.OperatorMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.SpectralDescent

/-! # A finite-angle improvement of the projective spectral contact -/
open Matrix NormedSpace
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where
local instance : NormedAlgebra ℚ (Mat I) := .restrictScalars ℚ ℂ _

/-- A centered generator with endpoint values ±d improves the squared
operator error by at least γ (d Im uₐ)²/64, where γ is the spectator
real-part separation. The angle depends only on those two numbers. -/
theorem spectral_contact_margin (u : I→ℂ) (hu : diagonal u ∈ unitary (Mat I))
    (a b : I) (hab : a≠b) (hconj : u b=star (u a)) (A : Mat I) (hA : A.IsHermitian)
    (hn : ‖A‖≤2) {ε γ d : ℝ} (hγ : 0≤γ) (hγ' : γ≤2)
    (hbase : (u a).re=1-ε^2/2) (hsep : ∀ j, j≠a → j≠b → (u a).re+γ≤(u j).re)
    (ha : A a a=(d:ℂ)) (hb : A b b=-(d:ℂ)) (hpos : 0≤(u a).im*d) (hbound : (u a).im*d≤4) :
    let c := (u a).im*d
    let t := γ*c/64
    ‖diagonal u-exp (t • (Complex.I • A))‖ ≤ Real.sqrt (ε^2-t*c) := by
  intro c t
  let Φ := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  let K := Complex.I • A
  let V := exp (t • K)
  have hK : ‖K‖≤2 := by simpa only [K,norm_smul,Complex.norm_I,one_mul] using hn
  have hsk : K ∈ skewAdjoint (Mat I) := by
    rw [skewAdjoint.mem_iff,show star K=star Complex.I • star A from star_smul _ _,show star A=A from hA.eq]
    simp [K]
  have hV : V ∈ unitary (Mat I) := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hsk)
  have hmin (j) : (u a).re≤(u j).re := by
    by_cases he : j=a
    · rw [he]
    by_cases he' : j=b
    · rw [he',hconj]; simp
    linarith only [hsep j he he',hγ]
  have hh := quadratic_operator_gain (Φ (diagonal u)) (Φ V) (Φ K) (onPair a b) ε γ c
    hγ hγ' hpos hbound (norm_apply_of_mem_unitary (Unitary.map_mem Φ hu))
    (norm_apply_of_mem_unitary (Unitary.map_mem Φ hV)) (by rwa [Matrix.l2_opNorm_toEuclideanCLM])
    (onPair_pythagoras a b) (fun v hv => hbase ▸ spectator_surplus u a b (u a).re γ hmin hsep v hv)
    (fun v => endpoint_variation_eq u A a b hab hconj ha hb (hA.apply b a).symm
      (onPair a b v) (onPair_off a b v))
  have hrem := rotation_remainder K hsk t
  have hsq : ‖K‖^2/2 ≤ 2 := by nlinarith only [sq_le_sq' (by linarith only [norm_nonneg K] : -(2:ℝ)≤‖K‖) hK]
  have he := hh (hrem.trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg t)))
  rwa [←map_sub,Matrix.l2_opNorm_toEuclideanCLM] at he

#print axioms spectral_contact_margin
end
end GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
