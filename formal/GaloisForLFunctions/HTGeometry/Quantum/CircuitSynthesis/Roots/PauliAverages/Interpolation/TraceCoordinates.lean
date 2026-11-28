import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.Packets
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.PairAverages

/-! # Diagonal action of a trace-weighted Pauli bracket mean -/

open Matrix Finset Complex NormedSpace
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem phase_re (x : ℝ) : (phaseValue x).re=Real.cos x := by
  simp [phaseValue,Complex.exp_mul_I]

private theorem phase_im (x : ℝ) : (phaseValue x).im=Real.sin x := by
  simp [phaseValue,Complex.exp_mul_I]

/-- On energy level $i$, the bracket mean for the $l$-th circuit
power is twice $i$ times the mean sine of the pairwise angular gaps. -/
theorem trace_coordinates (V : unitary (Mat I)) (θ : I → ℝ) (l : ℕ) :
    let W := (packet V θ)^l
    let τ := W.trace/(Fintype.card I:ℂ)
    conj τ • W-τ • star W=inBasis V
      (diagonal fun i => ((2*sineReading θ l i:ℝ):ℂ)*Complex.I) := by
  intro W τ
  let p (i : I) := phaseValue (l*θ i)
  have hW : W=inBasis V (diagonal p) := packet_pow _ _ _
  have ht : τ=(∑ j, p j)/((Fintype.card I:ℝ):ℂ) := by
    simp only [τ,hW,inBasis_trace,Matrix.trace_diagonal,Complex.ofReal_natCast]
  have hr : τ.re=angleMean (fun j => Real.cos (l*θ j)) := by
    rw [ht,Complex.div_ofReal_re,Complex.re_sum]
    simp only [p,phase_re,angleMean]
  have hi : τ.im=angleMean (fun j => Real.sin (l*θ j)) := by
    rw [ht,Complex.div_ofReal_im,Complex.im_sum]
    simp only [p,phase_im,angleMean]
  rw [hW,inBasis_star,inBasis_smul,inBasis_smul,inBasis_sub]
  congr 1
  ext i j
  by_cases hij : i=j
  · subst j
    apply Complex.ext <;>
      simp [Matrix.smul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Complex.star_def,
        Complex.mul_re,Complex.mul_im,hr,hi,p,phase_re,phase_im,sineReading] <;> ring
  · simp [Matrix.smul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,hij,Ne.symm hij]

/-- Exponentiating one bracket multiplies each eigenvector by the
exponential of its own real sine reading. -/
theorem trace_exponential (V : unitary (Mat I)) (θ : I → ℝ) (l : ℕ) (t : ℝ) :
    let W := (packet V θ)^l
    let τ := W.trace/(Fintype.card I:ℂ)
    exp (t • (conj τ • W-τ • star W))=packet V (fun i => 2*t*sineReading θ l i) := by
  intro W τ
  rw [trace_coordinates V θ l]
  let E (i : I) := -2*sineReading θ l i
  have he : inBasis V (diagonal fun i => ((2*sineReading θ l i:ℝ):ℂ)*Complex.I)=
      (-Complex.I) • inBasis V (diagonal (fun i => (E i:ℂ))) := by
    rw [inBasis_smul]
    congr 1
    ext i j
    by_cases hij : i=j
    · subst j
      simp [E,Matrix.smul_apply]
      ring
    · simp [Matrix.smul_apply,hij]
  rw [he]
  change unitaryEvolution (inBasis V (diagonal (fun i => (E i:ℂ)))) t=_
  rw [inBasis,unitaryEvolution_conj_diagonal V.val V.2]
  unfold packet inBasis
  congr 2
  funext i
  unfold phaseValue
  congr 1
  simp [E]
  ring

#print axioms trace_exponential
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
