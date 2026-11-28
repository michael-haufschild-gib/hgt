import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.Capture
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.CircuitTrace

/-! # A circuit-independent spectral bound for a frozen base -/

open Matrix Finset Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
private abbrev Config (N : ℕ) := Fin N → Bool

/-- The base eigenphases multiply the actual circuit diagonal before the
Gaussian perturbation is integrated. Off-diagonal entries enter through the
loss of modulus of the diagonal entries. -/
def affineTracePrice (n s : ℕ) (h : Coeff n) (R : Finset (Config (n+2))) (w : R → ℝ)
    (q : ℕ) (a b t : ℝ) : ℝ :=
  let U := (generator h).2.isHermitian.eigenvectorUnitary
  let E := (generator h).2.isHermitian.eigenvalues
  let v (l : PathLabel n) (i : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l i.val
  ∑ j : atMostQuarterCircuitNet (n+2) s,
    ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g)
      (fun i => (U⁻¹*j.val*U).val i.val i.val*Complex.exp (((a*E i.val*t:ℝ):ℂ)*Complex.I)) (t*b) ^ q
      ∂fieldLaw n‖

/-- Conditional affine capture retains the individual signed moments of
the physical circuit net, including their phases at the unperturbed date. -/
theorem affine_circuit_twists (n s : ℕ) (h : Coeff n) (R : Finset (Config (n+2)))
    (w : R → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1)
    (q : ℕ) (a b t ε : ℝ) (hε : ε ≤ 3/4) :
    (1-(ε+1/4))^(2*q)*(fieldLaw n).real {g | weightedFit (generator h).2.isHermitian.eigenvectorUnitary R w s ε (fun i =>
        wave t (a*(generator h).2.isHermitian.eigenvalues i+b*localSlope h g i))} ≤
      affineTracePrice n s h R w q a b t := by
  classical
  let v (l : PathLabel n) (i : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l i.val
  let U := (generator h).2.isHermitian.eigenvectorUnitary
  let N := atMostQuarterCircuitNet (n+2) s
  let E := (generator h).2.isHermitian.eigenvalues
  let u (i : Config (n+2)) := Complex.exp (((a*E i*t:ℝ):ℂ)*Complex.I)
  have hu (i) : ‖u i‖=1 := by simp [u,Complex.norm_exp]
  let z (j : N) (i : R) := (U⁻¹*j.val*U).val i.val i.val*u i.val
  have hz (j : N) (i : R) : ‖z j i‖ ≤ 1 := by
    rw [show z j i=(U⁻¹*j.val*U).val i.val i.val*u i.val from rfl,norm_mul,hu,mul_one]
    exact (norm_entry_le_l2_opNorm _ i.val i.val).trans_eq
      (CStarRing.norm_of_mem_unitary (U⁻¹*j.val*U).2)
  let τ : ℝ := 1-(ε+1/4)
  have hτ : 0 ≤ τ := by dsimp only [τ]; linarith only [hε]
  have hsub : {g : Coeff n | weightedFit (generator h).2.isHermitian.eigenvectorUnitary R w s ε (fun i =>
        wave t (a*(generator h).2.isHermitian.eigenvalues i+b*localSlope h g i))} ⊆
      ⋃ j : N, {g | τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) (t*b)‖} := by
    intro g hg
    let e := localSlope h g
    let f (i : Config (n+2)) := Complex.exp (((e i*(t*b):ℝ):ℂ)*Complex.I)
    let d (i : Config (n+2)) := u i*f i
    have hd (i) : ‖d i‖=1 := by simp [d,hu,f,Complex.norm_exp]
    have he (i) : wave t (a*E i+b*e i)*d i=1 := by
      dsimp only [wave,d,u,f]
      rw [←Complex.exp_add,←Complex.exp_add]
      suffices hx : -(Complex.I*((t:ℂ)*↑(a*E i+b*e i))) +
          (↑(a*E i*t)*Complex.I+↑(e i*(t*b))*Complex.I) = 0 by rw [hx,Complex.exp_zero]
      push_cast
      ring
    obtain ⟨W,hW,ho⟩ := circuit_trace_witness U R w hw hsum (fun i => wave t (a*E i+b*e i))
      d hd he hg
    apply mem_iUnion.mpr
    refine ⟨⟨W,hW⟩,?_⟩
    change τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z ⟨W,hW⟩) (t*b)‖
    have hE (i : R) : fieldEnergy v g i=e i.val := rfl
    simpa only [τ,twistedFiniteSpectralAmplitude,z,d,f,hE,mul_assoc] using ho
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg hτ _)).trans
    (field_capture_twists w hw hsum v z hz q (t*b) hτ)

/-- Discarding all twist phases bounds every target by the same positive
kernel. The resulting sum depends only on local energy expectations. -/
theorem affine_trace_price_le (n s : ℕ) (h : Coeff n) (R : Finset (Config (n+2))) (w : R → ℝ)
    (hw : ∀ i, 0 ≤ w i) (q : ℕ) (a b t : ℝ) :
    let v (l : PathLabel n) (i : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l i.val
    affineTracePrice n s h R w q a b t ≤ atMostQuarterCircuitEntropyBound (n+2) s*slopeMoment w v q (t*b) := by
  intro v
  let U := (generator h).2.isHermitian.eigenvectorUnitary
  let N := atMostQuarterCircuitNet (n+2) s
  let E := (generator h).2.isHermitian.eigenvalues
  let z (j : N) (i : R) := (U⁻¹*j.val*U).val i.val i.val*Complex.exp (((a*E i.val*t:ℝ):ℂ)*Complex.I)
  have hz (j : N) (i : R) : ‖z j i‖ ≤ 1 := by
    simp only [z,norm_mul,Complex.norm_exp]
    simpa using (norm_entry_le_l2_opNorm (U⁻¹*j.val*U).val i.val i.val).trans_eq
      (CStarRing.norm_of_mem_unitary (U⁻¹*j.val*U).2)
  have hn : 0 ≤ slopeMoment w v q (t*b) := by
    unfold slopeMoment
    exact sum_nonneg fun p _ => sum_nonneg fun k _ =>
      mul_nonneg (fidelityReplicaMultiplicityWeight_nonneg hw p k) (Real.exp_pos _).le
  apply (sum_le_sum (s:=univ) (fun (j : N) _ => field_fidelity_moment_le hw v (hz j) q (t*b))).trans
  rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_coe]
  exact mul_le_mul_of_nonneg_right (atMostQuarterCircuitNet_card_real_le ..) hn

#print axioms affine_circuit_twists
#print axioms affine_trace_price_le
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
