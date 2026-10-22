import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalKineticJets

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def amplitude : ℕ → Poly
  | 0 => 2
  | n+1 => t*pderiv Coord.J (amplitude n)+(t+C (9/4:ℂ))*amplitude n+
      C (3*(5/4:ℂ)^n)

theorem amplitude_pderiv_y (n : ℕ) : pderiv Coord.K (amplitude n)=0 := by
  induction n with
  | zero => simp [amplitude]
  | succ n ih =>
    simp only [amplitude,map_add,pderiv_mul]
    rw [GaloisForLFunctions.pderiv_comm Coord.K Coord.J (amplitude n),ih]
    simp [t,pderiv_X]

theorem delta_amplitude (n : ℕ) :
    delta (amplitude n)=t*pderiv Coord.J (amplitude n) := by
  simp [delta,amplitude_pderiv_y]

-- The entire constant seed is retained. No division by the terminal variable
-- is used, so the affine identity also holds on its zero plane.
theorem jet_affine (n : ℕ) :
    jet n=y*amplitude n-C (3*(5/4:ℂ)^n) := by
  induction n with
  | zero =>
    apply MvPolynomial.funext
    intro v
    norm_num [jet,amplitude]
    ring
  | succ n ih =>
    rw [jet,ih]
    unfold step
    rw [delta_sub,delta_mul,delta_y,delta_amplitude,delta_C]
    rw [amplitude,pow_succ]
    apply MvPolynomial.funext
    intro v
    simp only [map_add,map_sub,map_mul,map_one,map_zero,eval_C]
    ring

theorem native_jet_affine (n : ℕ) :
    pull (integerJet n)=C ((12:ℂ)^n)*
      (y*amplitude n-C (3*(5/4:ℂ)^n)) := by
  rw [pull_integerJet,jet_affine]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
