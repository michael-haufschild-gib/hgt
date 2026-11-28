import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.CircuitDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit

/-! # Cancelling a common phase on a spectral subspace -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
private abbrev Config (N : ℕ) := Fin N → Bool

/-- Projective implementation of prescribed phases on every vector in a
coordinate subspace of an orthonormal frame. Leakage counts in the norm. -/
def frameCircuit {N : ℕ} (U : unitaryGroup (Config N) ℂ) (R : Finset (Config N))
    (s : ℕ) (ε : ℝ) (z : Config N → ℂ) : Prop :=
  ∃ V : unitaryGroup (Config N) ℂ, DiagonalSynthesis.Realizes s V.val ∧
    ‖((U⁻¹*V*U).val-diagonal z)*coordinateProjection R‖ ≤ ε

/-- A fit on a subspace composes with the inverse of a second fit when the
two ideal maps preserve that subspace. The gate counts and errors add. -/
theorem frameCircuit.relative {N s₁ s₂ : ℕ} {U : unitaryGroup (Config N) ℂ}
    {R : Finset (Config N)} {ε₁ ε₂ : ℝ} {z₁ z₂ d : Config N → ℂ}
    (h₁ : frameCircuit U R s₁ ε₁ z₁) (h₂ : frameCircuit U R s₂ ε₂ z₂)
    (hd : ∀ i, ‖d i‖ = 1) (hz : ∀ i, z₂ i * d i = z₁ i) :
    frameCircuit U R (s₂+s₁) (ε₁+ε₂) d := by
  obtain ⟨V₁,hV₁,h₁⟩ := h₁
  obtain ⟨V₂,hV₂,h₂⟩ := h₂
  refine ⟨V₂⁻¹*V₁,hV₂.adjoint.mul hV₁,?_⟩
  let A := U⁻¹*V₁*U
  let B := U⁻¹*V₂*U
  let P := coordinateProjection R
  let D := diagonal d
  have hD := StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general d hd
  have hcomm : D*P=P*D := (Matrix.commute_diagonal ..).eq
  have hmul : diagonal z₂*D=diagonal z₁ := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext hz)
  have hgroup : U⁻¹*(V₂⁻¹*V₁)*U=B⁻¹*A := by dsimp only [A,B]; group
  rw [hgroup,← CStarRing.norm_mem_unitary_mul _ B.2]
  change ‖B.val*(((B⁻¹).val*A.val-D)*P)‖ ≤ _
  have hcancel : B.val*(B⁻¹).val=1 := congrArg Subtype.val (mul_inv_cancel B)
  have he : B.val*(((B⁻¹).val*A.val-D)*P) =
      (A.val-diagonal z₁)*P - ((B.val-diagonal z₂)*P)*D := by
    rw [←mul_assoc B.val, mul_sub, ←mul_assoc B.val, hcancel, one_mul]
    rw [mul_assoc (B.val-diagonal z₂), ←hcomm, ←mul_assoc (B.val-diagonal z₂),
      sub_mul B.val (diagonal z₂), hmul]
    simp only [sub_mul]
    abel
  rw [he]
  apply (norm_sub_le ..).trans
  rw [CStarRing.norm_mul_mem_unitary _ hD]
  exact add_le_add h₁ h₂

/-- Local energy of the independent field in one base eigenstate. -/
def localSlope {n : ℕ} (h g : Coeff n) (j : Config (n+2)) :=
  ∑ i, g i * FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) i j

/-- The centered circuit test depends only on the base eigenframe, the
local Pauli expectations, and the independent phase displacement. -/
def centeredFit (n s : ℕ) (R : Finset (Config (n+2))) (L ε : ℝ) : Set (FieldPair n) :=
  {x | frameCircuit (generator (base x)).2.isHermitian.eigenvectorUnitary R s ε
    (fun j => wave L (localSlope (base x) (fun i => (x i).2) j))}

private theorem phase_mem {c : ℂ} (hc : ‖c‖=1) : c∈unitary ℂ := by
  have h : star c*c=1 := by rw [Complex.star_def,Complex.conj_mul',hc]; norm_num
  exact Unitary.mem_iff.mpr ⟨h,(mul_comm ..).trans h⟩

private theorem of_witness {N s : ℕ} (U : unitaryGroup (Config N) ℂ) (R : Finset (Config N))
    (ε : ℝ) (z : Config N → ℂ) (c : ℂ) (hc : ‖c‖=1) (C : TwoQubitCircuit N)
    (hs : C.gateCount ≤ s)
    (h : ‖(U.valᴴ*(c • C.eval.val)*U.val-diagonal z)*coordinateProjection R‖ ≤ ε) :
    frameCircuit U R s ε z := by
  let V : unitaryGroup (Config N) ℂ :=
    ⟨c • C.eval.val,Unitary.smul_mem_of_mem (phase_mem hc) C.eval.2⟩
  exact ⟨V,⟨c,hc,C,hs,rfl⟩,h⟩

private theorem to_frame {n s : ℕ} {a b T ε : ℝ} {R : Finset (Config (n+2))}
    {h g : Coeff n} (hx : (fun i => (h i,g i)) ∈ edgeFit n s R a b T ε) :
    frameCircuit (generator h).2.isHermitian.eigenvectorUnitary R s ε
      (fun j => wave T (a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h g j)) := by
  let x : FieldPair n := fun i => (h i,g i)
  let U := (generator h).2.isHermitian.eigenvectorUnitary
  have hz : (fun j => wave T (diagonalEnergy U (generator (rotated a b x)).val j)) =
      (fun j => wave T (a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h g j)) :=
    funext fun j => congrArg (wave T) (affine_energies a b x j)
  obtain ⟨c,hc,C,hsize,herr⟩ := hx
  rw [←hz]
  exact of_witness U R ε _ c hc C hsize herr

/-- For two fits around the same Hamiltonian, all unperturbed energies
cancel exactly. Only the difference of the two local slopes remains. -/
theorem centered_of_two_fits {n s : ℕ} (R : Finset (Config (n+2))) (a b T ε : ℝ)
    (h g k : Coeff n) (L : ℝ) (w : Coeff n)
    (hw : ∀ i, L*w i = T*b*(g i-k i))
    (hg : (fun i => (h i,g i)) ∈ edgeFit n s R a b T ε)
    (hk : (fun i => (h i,k i)) ∈ edgeFit n s R a b T ε) :
    (fun i => (h i,w i)) ∈ centeredFit n (s+s) R L (ε+ε) := by
  change frameCircuit (generator h).2.isHermitian.eigenvectorUnitary R (s+s) (ε+ε)
    (fun j => wave L (localSlope h w j))
  apply (to_frame hg).relative (to_frame hk)
  · intro i
    simp [wave,Complex.norm_exp]
  · intro j
    have hs : L*localSlope h w j=T*b*(localSlope h g j-localSlope h k j) := by
      simp only [localSlope,←sum_sub_distrib,mul_sum]
      apply sum_congr rfl
      intro i _
      rw [←sub_mul,←mul_assoc,hw,mul_assoc]
    unfold wave
    rw [←Complex.exp_add]
    apply congrArg Complex.exp
    have he : T*(a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h k j)+L*localSlope h w j =
        T*(a*(generator h).2.isHermitian.eigenvalues j+b*localSlope h g j) := by rw [hs]; ring
    have he' := congrArg ((↑) : ℝ → ℂ) he
    push_cast at he' ⊢
    linear_combination -Complex.I*he'

#print axioms centered_of_two_fits
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
