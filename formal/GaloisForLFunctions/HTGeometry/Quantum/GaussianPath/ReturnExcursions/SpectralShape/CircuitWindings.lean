import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.WindingClasses
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory

/-! # Disorder exclusion of prescribed integer winding shapes across all circuit targets -/

open Matrix Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open AngularWindings.PhysicalTubes SharpOccupation
noncomputable section
private abbrev Index (n : ℕ) := Fin (n+2)→Bool
private abbrev Reg (n : ℕ) := Matrix (Index n) (Index n) ℂ
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- The lifted eigenphases of the actual operator fit to a laboratory unitary. -/
def windingFit {n : ℕ} (h : PathShell n) (W : unitary (Reg n)) (m : Index n → ℤ) (t ε : ℝ) : Prop :=
  let H := (isSelfAdjoint_pathHamiltonian h).isHermitian
  let C := H.eigenvectorUnitary⁻¹*W*H.eigenvectorUnitary
  t∈wordDates C (fun i => -H.eigenvalues i/(2*π)) (circuitTurns C) m (physicalArc ε) ε

/-- Every true fit admits an integer winding with its actual fitting global phase. -/
theorem laboratory_iff_winding {n : ℕ} (h : PathShell n) (W : unitary (Reg n)) (t : ℝ)
    {ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    t∈laboratoryDates ⟨pathHamiltonian h,isSelfAdjoint_pathHamiltonian h⟩ W ε ↔
      ∃ m : Index n → ℤ, windingFit h W m t ε := by
  rw [laboratoryDates_eq]
  exact date_iff_lift _ _ he

/-- Squared skewness of the centered integer winding, in angular units.
It is independent of the labeling of the energy levels. -/
def windingShape {n : ℕ} (m : Index n → ℤ) : ℝ :=
  shape (centered fun i => -(2*π)*(m i:ℝ))

/-- Removing the circuit's diagonal arguments costs at most half a turn per level. -/
theorem class_of_fit {n : ℕ} (h : PathShell n) (W : unitary (Reg n)) (m : Index n → ℤ)
    {t T ε : ℝ} (ht : T≤t) (hh : windingFit h W m t ε) :
    classHit (windingShape m) T (π*(1+physicalArc ε)) h := by
  let H := (isSelfAdjoint_pathHamiltonian h).isHermitian
  let C := H.eigenvectorUnitary⁻¹*W*H.eigenvectorUnitary
  let A (i) := -H.eigenvalues i/(2*π)
  let x := physicalArc ε
  obtain ⟨p,hp,_⟩ := hh
  refine ⟨fun i => -(2*π)*(m i:ℝ),rfl,t,ht,-(2*π)*p,?_⟩
  intro i
  let d := circuitTurns C i
  have hd : |d|≤1/2 := by
    dsimp only [d,circuitTurns]
    rw [abs_div,abs_of_pos two_pi_pos,div_le_iff₀ two_pi_pos]
    linarith only [Complex.abs_arg_le_pi (C.val i i)]
  let z := t*A i-(d+(m i:ℝ))-p
  have hz : |z|≤x/2 := hp i
  have heq : t*H.eigenvalues i-(-(2*π)*(m i:ℝ))-(-(2*π)*p)=-(2*π)*(z+d) := by
    dsimp only [z,A]
    field_simp [pi_ne_zero]
    ring
  rw [heq,abs_mul,abs_neg,abs_of_pos two_pi_pos]
  have hs := (abs_add_le z d).trans (add_le_add hz hd)
  change 2*π*|z+d|≤π*(1+x)
  linarith only [mul_le_mul_of_nonneg_left hs two_pi_pos.le]

/-- For every late visit to any laboratory circuit, all integer words in a
prescribed finite set of cubic shapes are excluded outside the stated probability.
The count is over distinct shapes, even if circuits and words vary with the draw. -/
theorem gaussian_circuit_winding_shapes :
    ∃ B : ℕ → Set PathPauliDisorder, (∀ n, MeasurableSet (B n)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉B n) ∧
      ∀ (n : ℕ) (F : Finset ℝ) (T ε r : ℝ), let K : ℝ := (n+2:ℕ)
        let x := π*(1+physicalArc ε)
        ε∈Ioo (0:ℝ) (sqrt 2) → 0<T → 0<r → 16*x≤T*sqrt K →
        16000*x*(sqrt (13*K))^5<T*((2/3)*r^6) →
        pathPauliDisorderLaw.real ({ω | ∃ t≥T, ∃ W : unitary (Reg n), ∃ m : Index n → ℤ,
          windingShape m∈F ∧ windingFit (pathPauliDisorderShell ω n) W m t ε} \ B n)≤(F.card:ℝ)*(12*r) := by
  obtain ⟨B,hB,hgood,hprice⟩ := physical_winding_classes
  refine ⟨B,hB,hgood,?_⟩
  intro n F T ε r K x he hT hr hres hcut
  have hx : 0≤x := mul_nonneg pi_pos.le (by linarith only [(physicalArc_spec he.1 he.2).1.1])
  apply le_trans _ (hprice n F T x r hT hx hr hres hcut)
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro ω ⟨⟨t,ht,W,m,hm,hf⟩,hbase⟩
  exact ⟨⟨windingShape m,hm,class_of_fit _ W m ht hf⟩,hbase⟩

#print axioms laboratory_iff_winding
#print axioms gaussian_circuit_winding_shapes
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
