import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LongitudinalSpins.FieldPairs
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations.Involution
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance

/-! # A longitudinal Pauli field changes the sign of a transverse probe -/

open Matrix MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LongitudinalSpins
noncomputable section

private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
private abbrev Word (N : ℕ) := Fin N → Option (Fin 3)

/-- Evolving an odd Pauli probe in a commuting background reverses the
probe when its longitudinal field advances by a quarter turn. -/
theorem longitudinal_sign {N : ℕ} (P Q : Word N) (K : Reg N) (hc : Commute K (finitePauliMatrix P))
    (hs : finitePauliConjugationSign P Q = -1) {t : ℝ} (ht : t≠0) (x : ℝ) :
    let U (y : ℝ) := unitaryEvolution (K+(y:ℂ) • finitePauliMatrix P) t
    let f (y : ℝ) := U y*finitePauliMatrix Q*star (U y)
    f (x+π/(2*t))= -f x := by
  intro U f
  let Z := finitePauliMatrix P
  let X := finitePauliMatrix Q
  let d := π/(2*t)
  let J := (-Complex.I) • Z
  have hq : unitaryEvolution Z (π/2)=J := by
    unfold unitaryEvolution
    rw [←Complex.coe_smul,smul_smul,mul_comm]
    exact InvolutionRotation.quarter_exp _ (finitePauliMatrix_mul_self P)
  have hK : Commute (K+(x:ℂ) • Z) ((d:ℂ) • Z) :=
    (hc.add_left ((Commute.refl Z).smul_left (x:ℂ))).smul_right (d:ℂ)
  have ht' : d*t=π/2 := by dsimp only [d]; field_simp
  have hU : U (x+d)=U x*J := by
    change unitaryEvolution (K+((x+d:ℝ):ℂ) • Z) t = _
    rw [Complex.ofReal_add,add_smul,←add_assoc,unitaryEvolution_add_of_commuting hK,
      unitaryEvolution_scale_pauli P,ht',hq]
  have hZ : star Z=Z := finitePauliMatrix_isHermitian P
  have hZX : Z*X*Z= -X := by simpa only [hs,neg_one_smul] using finitePauliMatrix_conj P Q
  have hJ : J*X*star J= -X := by
    dsimp only [J]
    rw [star_smul,hZ,Complex.star_def,map_neg,Complex.conj_I,neg_neg,smul_mul_assoc,
      mul_smul_comm,smul_mul_assoc,smul_smul,hZX]
    simp
  change U (x+d)*X*star (U (x+d))= -(U x*X*star (U x))
  rw [hU,star_mul,show U x*J*X*(star J*star (U x))=U x*(J*X*star J)*star (U x) by
    simp only [mul_assoc],hJ,mul_neg,neg_mul]

/-- A standard Gaussian longitudinal field moves a transverse Pauli
probe by operator distance at least one with probability bounded below
uniformly in time and in the entire commuting background. -/
theorem gaussian_longitudinal_probe {N : ℕ} (P Q : Word N) (K : Reg N) (hc : Commute K (finitePauliMatrix P))
    (hs : finitePauliConjugationSign P Q= -1) {t : ℝ} (ht : 2≤t) :
    let U (y : ℝ) := unitaryEvolution (K+(y:ℂ) • finitePauliMatrix P) t
    gaussianDensityFloor/2 ≤ (gaussianReal 0 1).real
      {x : ℝ | 1≤‖finitePauliMatrix Q-U x*finitePauliMatrix Q*star (U x)‖} := by
  intro U
  have hpos : 0<t := (by norm_num : (0:ℝ)<2).trans_le ht
  have hU : Continuous U := continuous_unitaryEvolution.comp
    ((continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).prodMk continuous_const)
  apply gaussian_probe_moves (fun y => U y*finitePauliMatrix Q*star (U y))
    ((hU.mul continuous_const).mul hU.star) _ (CStarRing.norm_of_mem_unitary (finitePauliMatrix_mem_unitary Q))
    (d:=π/(2*t))
  · refine ⟨by positivity,(div_le_iff₀ (by positivity)).mpr ?_⟩
    linarith only [pi_lt_four,ht]
  · exact longitudinal_sign P Q K hc hs hpos.ne'

#print axioms gaussian_longitudinal_probe
end
end GaloisForLFunctions.HTGeometry.LongitudinalSpins
