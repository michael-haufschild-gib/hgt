import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates.GeneratorBounds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.UnitaryPhases
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection
import GaloisForLFunctions.HTGeometry.GaussianProductBoxFloor

/-! # Explicit Gaussian probability of a uniform-in-time diagonal circuit bound -/

open Set MeasureTheory ProbabilityTheory Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap
open PrescribedTimes DiagonalSynthesis.CommutatorBounds
noncomputable section

private def spacingScale (n : ℕ) : ℝ := 1/(3:ℝ)^(n+2)

private theorem scale_pos (n : ℕ) : 0<spacingScale n := by unfold spacingScale; positivity

private theorem carrier_box_center (n : ℕ) (l : PathLabel n) :
    |sepCarrier n (spacingScale n) 0 l|≤1 := by
  rcases l with ⟨i,p⟩|⟨a,b⟩
  · change |if p=2 then spacingScale n*3^(i:ℕ) else 0|≤1
    split
    · rw [abs_of_nonneg (mul_nonneg (scale_pos n).le (by positivity)),spacingScale,one_div,
        inv_mul_eq_div,div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) i.isLt.le
    · norm_num
  · change |if b=(2,2) then (0:ℝ) else 0|≤1
    simp

private theorem cube_cap (n : ℕ) (x : PrefixIndex n→ℝ) {δ : ℝ}
    (hx : ∀ i, |x i-sepCarrier n (spacingScale n) 0 (pathCoeffEquiv n i)|≤δ) (t : ℝ) :
    let N := n+2
    let d := Fintype.card (PrefixIndex n)
    pathGateDistance n (2^N*(2*N+1)) x t≤2*sqrt packConstant/spacingScale n*((d:ℝ)*δ) := by
  intro N d
  let A := spacingScale n
  let u := sepCarrier n A 0
  let D := fun i => pathDiagEnergy u i
  let Z := diagonal fun i => (D i:ℂ)
  have hsep (i j) (hij : i≠j) : 2*A≤|D i-D j| := by
    simpa only [mul_zero,zero_mul,sub_zero] using
      (abs_sub_pathDiagEnergy_sepCarrier_ge (n:=n) (A:=A) (b:=0) (scale_pos n).le le_rfl hij)
  let H := prefixGenerator n x
  have he : numberedGenerator n (fun i => u (pathCoeffEquiv n i))=Z :=
    (numberedGenerator_shell u).trans (pathHamiltonian_eq_diagonal u (sepCarrier_offDiag A 0))
  have hb : ‖H.val-Z‖≤(d:ℝ)*δ := by
    rw [←he]
    exact numberedGenerator_box _ _ hx
  have hA : 0<A := scale_pos n
  have hf := all_time_diagonal_approximation (show 2≤N by dsimp only [N]; omega)
    H D (mul_pos two_pos hA) hsep t
  have hratio : 4*sqrt packConstant/(2*A)=2*sqrt packConstant/A := by field_simp; ring
  apply ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hf).trans
  rw [hratio]
  exact mul_le_mul_of_nonneg_left hb (div_nonneg (mul_nonneg zero_le_two (sqrt_nonneg _)) hA.le)

/-- A cube around bounded onsite longitudinal fields has spectral
spacing at least twice 3⁻ᴺ at its center. Its entire orbit has a
diagonal circuit cap at an explicit error linear in the cube radius. -/
theorem gaussian_diagonal_cap_box (n : ℕ) {δ : ℝ} (hδ : 0<δ) (hδ₁ : δ≤1) :
    let N := n+2
    let d := Fintype.card (PrefixIndex n)
    let ε := 2*sqrt packConstant*(3:ℝ)^N*((d:ℝ)*δ)
    (_root_.HTGeometry.gaussianFloorConstant*(2*δ))^d ≤ pathPauliDisorderLaw.real
      {ω | ∀ t : ℝ, HasProjectiveCircuitApproximation N ε (2^N*(2*N+1))
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} := by
  intro N d ε
  let c := fun i => sepCarrier n (spacingScale n) 0 (pathCoeffEquiv n i)
  let B := Set.univ.pi fun i => Icc (c i-δ) (c i+δ)
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hmp : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hmeas : MeasurableSet B := MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hmass := _root_.HTGeometry.measure_pi_box_ge c (fun i => carrier_box_center n _) δ hδ hδ₁
  have hreal := ENNReal.toReal_mono (measure_ne_top μ B) hmass
  rw [ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg _root_.HTGeometry.gaussianFloorConstant_pos.le
    (mul_nonneg zero_le_two hδ.le)) _)] at hreal
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  apply (hreal.trans_eq (hmp.measureReal_preimage hmeas.nullMeasurableSet).symm).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω t
  have hbox (i) : |X ω i-c i|≤δ := by
    have hi : X ω i∈Icc (c i-δ) (c i+δ) := hω i (Set.mem_univ i)
    exact abs_le.mpr ⟨by linarith only [hi.1],by linarith only [hi.2]⟩
  have hh := cube_cap n (X ω) hbox t
  have he : 2*sqrt packConstant/spacingScale n*((d:ℝ)*δ)=ε := by
    simp only [spacingScale,one_div,div_eq_mul_inv,inv_inv,ε,N]
  change pathGateDistance n _ (X ω) t ≤ _ at hh
  rw [he,pathGateDistance,show numberedGenerator n (X ω)=_ from numberedGenerator_shell _] at hh
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh

#print axioms gaussian_diagonal_cap_box
end
end GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap
