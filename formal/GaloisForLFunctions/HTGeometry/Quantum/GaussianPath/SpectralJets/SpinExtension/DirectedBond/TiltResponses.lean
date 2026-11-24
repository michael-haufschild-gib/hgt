import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.TiltProfile

/-! # Both endpoint derivatives distinguish odd and even bond responses -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- False selects the first derivative, true the second. -/
def jet : Bool → (ℂ→ℂ) → ℂ→ℂ
  | false,f => deriv f
  | true,f => deriv (deriv f)

def order : Bool→ℕ | false => 1 | true => 2

theorem jet_const_mul (j : Bool) (c : ℂ) (f : ℂ→ℂ) (t : ℂ) :
    jet j (fun v => c*f v) t=c*jet j f t := by
  cases j <;> simp only [jet,deriv_const_mul_field',deriv_const_mul_field]

theorem alignment_square (t : ℂ) : alignment t^2=(3/5:ℂ)^2*profile (-1) t := by
  rw [alignment_eq_div,div_pow,splitting_square,profile,Complex.cpow_neg_one,div_eq_mul_inv]

/-- No first or second endpoint reading annihilates either sector combination. -/
theorem jet_alignment_pow_ne (j m : Bool) : jet j (fun t => alignment t^order m) 0≠0 := by
  cases m with
  | false =>
    simp only [order,pow_one,alignment,jet_const_mul]
    apply mul_ne_zero (by norm_num)
    obtain ⟨h₁,h₂⟩ := profile_jet (-(1/2))
    cases j with
    | false => rw [jet,h₁]; norm_num
    | true => rw [jet,h₂]; norm_num
  | true =>
    simp only [order,alignment_square,jet_const_mul]
    apply mul_ne_zero (by norm_num)
    obtain ⟨h₁,h₂⟩ := profile_jet (-1)
    cases j with
    | false => rw [jet,h₁]; norm_num
    | true => rw [jet,h₂]; norm_num

theorem jet_splitting_ne (j : Bool) : jet j splitting 0≠0 := by
  cases j
  · exact splitting_nondegenerate.1
  · exact splitting_nondegenerate.2

#print axioms jet_alignment_pow_ne
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
