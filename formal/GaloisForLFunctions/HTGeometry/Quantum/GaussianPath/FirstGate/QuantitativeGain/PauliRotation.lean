import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.QuantitativeGain.SpectralMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.CenteredWord
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-! # A single physical rotation for a whole set of spectral contacts -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance {N : ℕ} : CStarAlgebra (Reg N) where
local instance {N : ℕ} : NormedAlgebra ℚ (Reg N) := .restrictScalars ℚ ℂ _

/-- Fix the two extremal levels, their phases, and a lower bound γ on the
spectator separation. One rotation of the physical observable works at
all these contacts, with gain proportional to γ times the squared
difference of the two endpoint expectations. -/
theorem uniform_physical_rotation {N : ℕ} (V : Reg N) (hV : V∈unitary (Reg N))
    (P : selfAdjoint (Reg N)) (hP : ‖P.val‖≤1) (a b : Fin N→Bool) (hab : a≠b)
    (ε γ η : ℝ) (hγ : 0≤γ) (hγ' : γ≤2) (hη : 0≤η) (hη' : η≤1) :
    let B := star V*P.val*V
    let d := |(B a a).re-(B b b).re|/2
    let c := η*d
    ∃ θ : ℝ, ∃ z : ℂ, ‖z‖=1 ∧ ∀ u : (Fin N→Bool)→ℂ,
      diagonal u ∈ unitary (Reg N) → u b=star (u a) → (u a).im=η →
      (u a).re=1-ε^2/2 → (∀ j, j≠a → j≠b → (u a).re+γ≤(u j).re) →
      ‖V*diagonal u*star V-z • unitaryEvolution P.val θ‖ ≤ Real.sqrt (ε^2-(γ*c/64)*c) := by
  intro B d c
  let x := (B a a).re
  let y := (B b b).re
  let q := (x+y)/2
  let s : ℝ := if y<x then 1 else -1
  let A := (s:ℂ) • (B-(q:ℂ) • 1)
  let t := γ*c/64
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V P.2.isHermitian
  obtain ⟨hA,ha,hb,hs⟩ := centered_axis B hB a b
  have hBn : ‖B‖≤1 := by
    have hV' : star V∈unitary (Reg N) := Unitary.star_mem hV
    change ‖star V*P.val*V‖≤1
    simpa only [star_star] using (l2_opNorm_unitary_conj_eq hV' P.val).le.trans hP
  have hdiag (i) : |(B i i).re|≤1 := (Complex.abs_re_le_norm _).trans
    ((norm_entry_le_l2_opNorm B i i).trans hBn)
  obtain ⟨hxl,hxu⟩ := abs_le.mp (hdiag a)
  obtain ⟨hyl,hyu⟩ := abs_le.mp (hdiag b)
  have hq : |q|≤1 := abs_le.mpr ⟨by dsimp [q,x,y]; linarith only [hxl,hyl],
    by dsimp [q,x,y]; linarith only [hxu,hyu]⟩
  have hd : 0≤d := half_nonneg (abs_nonneg _)
  have hd' : d≤1 := by
    have hg : |(B a a).re-(B b b).re|≤2 :=
      abs_le.mpr ⟨by linarith only [hxl,hyu],by linarith only [hxu,hyl]⟩
    dsimp only [d]; linarith only [hg]
  have hAn : ‖A‖≤2 := by
    rw [show ‖A‖=‖B-(q:ℂ) • 1‖ by simp only [A,norm_smul,Complex.norm_real,Real.norm_eq_abs,hs,one_mul]]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,norm_one,mul_one]
    linarith only [hBn,hq]
  obtain ⟨z,hz,he⟩ := centered_eigenbasis_rotation V hV P q s t
  refine ⟨-t*s,z,hz,?_⟩
  intro u hu hcj him hbase hsep
  have hc : 0≤(u a).im*d := him ▸ mul_nonneg hη hd
  have hc' : (u a).im*d≤4 := by
    rw [him]
    exact (mul_le_mul hη' hd' hd (by norm_num)).trans (by norm_num)
  have hh := spectral_contact_margin u hu a b hab hcj A hA hAn hγ hγ' hbase hsep ha hb hc hc'
  rw [him] at hh
  rw [←he,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq hV]
  exact hh

#print axioms uniform_physical_rotation
end
end GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
