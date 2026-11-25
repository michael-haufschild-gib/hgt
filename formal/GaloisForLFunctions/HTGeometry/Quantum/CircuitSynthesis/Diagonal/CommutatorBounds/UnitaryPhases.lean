import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.SeparatedGaps
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.NearDiagonal
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator

/-! # Quantitative all-time synthesis near a separated diagonal Hamiltonian -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A unitary at distance b from its diagonal is within 2b of a
diagonal unitary. Each diagonal modulus differs from one by at most b,
by testing the discarded part on that coordinate vector. -/
theorem exists_diagonal_unitary (U : Matrix I I ℂ) (hU : U∈unitary (Matrix I I ℂ)) :
    ∃ w : I→ℂ, (∀ i, ‖w i‖=1) ∧ (∀ i j, U i i=U j j → w i=w j) ∧
      ‖U-diagonal w‖≤2*‖U-diagonal (fun i => U i i)‖ := by
  let z := fun i => U i i
  let D := diagonal z
  let w := fun i => Complex.exp (((z i).arg:ℂ)*Complex.I)
  have hw (i) : ‖w i‖=1 := Complex.norm_exp_ofReal_mul_I _
  let Φ := Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)
  have hb (i : I) : ‖z i-w i‖≤‖U-D‖ := by
    let v : EuclideanSpace ℂ I := EuclideanSpace.single i 1
    have hv : ‖v‖=1 := by simp only [v,PiLp.norm_single,Complex.norm_one]
    have hd : Φ D v=z i • v := by
      ext j
      change (D *ᵥ v.ofLp) j=z i*v j
      rw [Matrix.mulVec_diagonal]
      by_cases h : j=i
      · subst j; rfl
      · simp [v,EuclideanSpace.single,h,Ne.symm h]
    have hu : ‖Φ U v‖=1 := (norm_apply_of_mem_unitary (Unitary.map_mem Φ hU) v).trans hv
    have hu' : ‖Φ D v‖=‖z i‖ := by rw [hd,norm_smul,hv,mul_one]
    have hrad : ‖z i-w i‖=|‖z i‖-1| := by
      have he : ((‖z i‖:ℂ)-1)*w i=z i-w i := by rw [sub_mul,one_mul,Complex.norm_mul_exp_arg_mul_I]
      rw [←he,norm_mul,hw,mul_one,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [hrad,←hu',←hu]
    apply (abs_norm_sub_norm_le (Φ D v) (Φ U v)).trans
    rw [←ContinuousLinearMap.sub_apply,←map_sub]
    exact ((Φ (D-U)).le_opNorm v).trans_eq (by rw [hv,mul_one,Matrix.l2_opNorm_toEuclideanCLM,norm_sub_rev])
  have hdiag : ‖D-diagonal w‖≤‖U-D‖ := by
    rw [show D-diagonal w=diagonal (z-w) from (diagonal_sub ..).symm,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hb
  refine ⟨w,hw,fun i j h => congrArg (fun a : ℂ => Complex.exp ((a.arg:ℂ)*Complex.I)) h,
    (norm_sub_le_norm_sub_add_norm_sub U D (diagonal w)).trans ?_⟩
  linarith only [hdiag]

/-- All commuting unitaries use the same perturbation-to-gap ratio.
Equal diagonal entries yield equal approximating phases, which
preserves the support of a unitary on a physical subregister. -/
theorem commuting_diagonal_approximation (H U : Matrix I I ℂ) (hU : U∈unitary (Matrix I I ℂ))
    (hc : H*U=U*H) (d : I→ℝ) {g : ℝ} (hg : 0<g) (hsep : ∀ i j, i≠j → g≤|d i-d j|) :
    let Z := diagonal fun i => (d i:ℂ)
    ∃ w : I→ℂ, (∀ i, ‖w i‖=1) ∧ (∀ i j, U i i=U j j → w i=w j) ∧
      ‖U-diagonal w‖≤4*sqrt packConstant/g*‖H-Z‖ := by
  intro Z
  obtain ⟨w,hw,hf,hdiag⟩ := exists_diagonal_unitary U hU
  have he : Z*U-U*Z=(Z-H)*U-U*(Z-H) := by
    rw [sub_mul,mul_sub,hc]
    abel
  have hcomm : ‖Z*U-U*Z‖≤2*‖H-Z‖ := by
    rw [he]
    apply (norm_sub_le ..).trans
    rw [CStarRing.norm_mul_mem_unitary _ hU,CStarRing.norm_mem_unitary_mul _ hU,norm_sub_rev]; ring_nf
  have h := (offDiagonal_le_commutator d hg hsep U).trans
    (mul_le_mul_of_nonneg_left hcomm (div_nonneg (sqrt_nonneg _) hg.le))
  exact ⟨w,hw,hf,hdiag.trans ((mul_le_mul_of_nonneg_left h zero_le_two).trans_eq (by ring))⟩

/-- The all-time diagonal circuit cap holds at an error linear in the
perturbation divided by the gap, with no dimension factor. -/
theorem all_time_diagonal_approximation {N : ℕ} (hN : 2≤N) (H : selfAdjoint (Register N))
    (d : (Fin N→Bool)→ℝ) {g : ℝ} (hg : 0<g) (hsep : ∀ i j, i≠j → g≤|d i-d j|) (t : ℝ) :
    let Z := diagonal fun i => (d i:ℂ)
    HasProjectiveCircuitApproximation N (4*sqrt packConstant/g*‖H.val-Z‖)
      (2^N*(2*N+1)) (unitaryEvolution H.val t) := by
  intro Z
  obtain ⟨w,hw,_,hdiag⟩ := commuting_diagonal_approximation H.val _ (unitaryEvolution_mem_unitary H.property t)
    (unitaryEvolution_commutes_generator H.val t) d hg hsep
  obtain ⟨z,hz,C,hcost,hW⟩ := diagonal_phases hN w hw
  refine ⟨z,hz,C,hcost,?_⟩
  rw [←hW]
  exact hdiag

#print axioms all_time_diagonal_approximation
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds
