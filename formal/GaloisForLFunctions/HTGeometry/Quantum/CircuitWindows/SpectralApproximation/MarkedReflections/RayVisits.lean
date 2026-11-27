import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.RayAngle
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.PhysicalTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.FrozenChain

/-! # Which ray reflections are visited by the frozen Gaussian chain? -/
open Matrix Finset MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
open SpectralFilling.ReplicaOrders
open private reflection_mul from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.PhysicalTest
noncomputable section

private abbrev Mat (I : Type*) := Matrix I I ℂ
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

private theorem scalar_transfer (H : selfAdjoint (Mat I)) (g : I → ℂ) (t : ℝ) (z : ℂ)
    {δ : ℝ} (hd : 0≤δ) (h : ∀ b,
      ‖g b*Complex.exp (Complex.I*(H.2.isHermitian.eigenvalues b:ℂ)*(t:ℂ))-z‖≤δ) :
    let B := H.2.isHermitian.eigenvectorUnitary
    ‖z • unitaryEvolution H.val t-B.val*diagonal g*star B.val‖≤δ := by
  intro B
  let f b := Complex.exp (-(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues b:ℂ))))
  let p b := Complex.exp (Complex.I*(H.2.isHermitian.eigenvalues b:ℂ)*(t:ℂ))
  have hf (b : I) : ‖f b‖=1 := by simp [f,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  have hid (b : I) : p b*f b=1 := by
    dsimp only [p,f]
    rw [←Complex.exp_add,show Complex.I*(H.2.isHermitian.eigenvalues b:ℂ)*(t:ℂ)+
      -(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues b:ℂ)))=0 by ring,Complex.exp_zero]
  rw [unitaryEvolution_spectral H.2.isHermitian]
  change ‖z • (B.val*diagonal f*star B.val)-B.val*diagonal g*star B.val‖≤δ
  rw [←Matrix.smul_mul,←Matrix.mul_smul,←Matrix.diagonal_smul,←Matrix.sub_mul,←Matrix.mul_sub,
    l2_opNorm_unitary_conj_eq B.property,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hd).mpr
  intro b
  change ‖z*f b-g b‖≤δ
  calc _ = ‖(z-g b*p b)*f b‖ := by rw [sub_mul,mul_assoc,hid,mul_one]
       _ = ‖g b*p b-z‖ := by rw [norm_mul,hf,mul_one,norm_sub_rev]
       _ ≤ δ := h b

/-- From every origin a single measured spacing bounds the time needed
to approach the sign flip associated to any chosen energy level. -/
theorem gaussian_ray_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let B := H.2.isHermitian.eigenvectorUnitary
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ C : unitaryGroup (Fin K → Bool) ℂ, ∀ i j, ∀ δ > (0:ℝ), ∀ a : ℝ,
        ∃ t ∈ Set.Icc a (a+alignmentLength k E δ), ∃ z : ℂ, ‖z‖=1 ∧
          ‖z • unitaryEvolution H.val t-reflection C {j}‖≤δ+2*Real.sqrt (1-‖(B⁻¹*C).val i j‖^2) := by
  filter_upwards [gaussian_replica_phase_filling] with ω hw
  filter_upwards [hw] with k hk
  intro K u H B E C i j δ hd a
  let g := markSign {i}
  have hg b : ‖g b‖=1 := by by_cases h : b=i <;> simp [g,markSign,h]
  obtain ⟨t,ht,z,hz,he⟩ := hk δ hd a (g ∘ (qubitConfigFin K).symm) (fun b => hg _)
  have hloc := scalar_transfer H g t z hd.le (fun b => by
    simpa only [K,Function.comp_apply,Equiv.symm_apply_apply] using (he (qubitConfigFin (k+3) b)).le)
  let V := B⁻¹*C
  let X := B.val*diagonal g*star B.val
  have hc : reflection C {j}=B.val*reflection V {j}*star B.val := by
    rw [←reflection_mul,show B*V=C from mul_inv_cancel_left ..]
  have herr := ray_flip_bound V i j
  have hpos : 0≤1-‖V.val i j‖^2 := by linarith only [herr,sq_nonneg ‖diagonal g-reflection V {j}‖]
  have hsign : ‖X-reflection C {j}‖≤2*Real.sqrt (1-‖V.val i j‖^2) := by
    rw [hc,show X=B.val*diagonal g*star B.val from rfl,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq B.property]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hpos]
    simpa only [g,show (2:ℝ)^2=4 by norm_num] using herr
  exact ⟨t,ht,z,hz,(norm_sub_le_norm_sub_add_norm_sub _ X _).trans (add_le_add hloc hsign)⟩

/-- At any strict tolerance up to √2, a reflection about the specified
ray is visited arbitrarily late exactly when one energy eigenstate has
squared fidelity strictly above 1 − e²/4. -/
theorem gaussian_ray_visit_iff :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ C : unitaryGroup (Fin K → Bool) ℂ, ∀ j, ∀ e ∈ Set.Ioc (0:ℝ) (Real.sqrt 2),
        (∀ a : ℝ, ∃ t≥a, ∃ z : ℂ, ‖z‖=1 ∧ ‖z • unitaryEvolution H.val t-reflection C {j}‖<e) ↔
          ∃ i, 1-e^2/4 < ‖(H.2.isHermitian.eigenvectorUnitary⁻¹*C).val i j‖^2 := by
  filter_upwards [gaussian_ray_windows] with ω hw
  filter_upwards [hw] with k hk
  intro K u H C j e he
  constructor
  · intro hv
    obtain ⟨t,_,z,hz,ht⟩ := hv 0
    rcases ray_at_every_date H C j t z hz with hlarge | ⟨i,hi⟩
    · exact (he.2.not_gt (hlarge.trans_lt ht)).elim
    · let r := ‖z • unitaryEvolution H.val t-reflection C {j}‖
      have hr : 0≤r := norm_nonneg _
      have hsq : r^2<e^2 := (sq_lt_sq₀ hr he.1.le).mpr ht
      exact ⟨i,lt_of_lt_of_le (by change 1-e^2/4 < 1-r^2/4; linarith only [hsq]) hi⟩
  · rintro ⟨i,hi⟩ a
    let p := ‖(H.2.isHermitian.eigenvectorUnitary⁻¹*C).val i j‖^2
    let r := 2*Real.sqrt (1-p)
    have hp : 0≤1-p := by
      have h := (norm_entry_le_l2_opNorm (H.2.isHermitian.eigenvectorUnitary⁻¹*C).val i j).trans_eq
        (CStarRing.norm_of_mem_unitary (H.2.isHermitian.eigenvectorUnitary⁻¹*C).property)
      exact sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) h)
    have hrate : r<e := by
      apply (sq_lt_sq₀ (show 0≤r from mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) he.1.le).mp
      change (2*Real.sqrt (1-p))^2<e^2
      rw [mul_pow,Real.sq_sqrt hp]
      change 1-e^2/4<p at hi
      linarith only [hi]
    let δ := (e-r)/2
    obtain ⟨t,ht,z,hz,herr⟩ := hk C i j δ (half_pos (sub_pos.mpr hrate)) a
    refine ⟨t,ht.1,z,hz,?_⟩
    change _≤(e-r)/2+r at herr
    linarith only [herr,hrate]

#print axioms gaussian_ray_windows
#print axioms gaussian_ray_visit_iff
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
