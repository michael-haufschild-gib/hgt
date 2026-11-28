import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.LocalizedMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.FirstReturn
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.PrincipalWeights
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # A fixed laboratory circuit on an elapsed observation window -/

open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
open AngularWindings.PhysicalTubes
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Holding the implementing circuit fixed preserves a relaxed operator
fit for this much physical time on either side of the contact. -/
def clearanceTime (H : selfAdjoint (Mat I)) : ℝ := (1/80)/(1+‖H.val‖)

omit [Nonempty I] in
private theorem clearance_pos (H : selfAdjoint (Mat I)) : 0<clearanceTime H := by
  unfold clearanceTime
  positivity

private theorem persistence (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) {v t : ℝ}
    (hf : v∈laboratoryDates H W (1/10)) (ht : t∈Icc v (v+clearanceTime H)) :
    t∈laboratoryDates H W (9/80) := by
  obtain ⟨z,hz,hfit⟩ := hf
  refine ⟨z,hz,?_⟩
  have hδ := (div_mul_cancel₀ (1/80:ℝ) (by positivity : (1:ℝ)+‖H.val‖≠0))
  change clearanceTime H*(1+‖H.val‖)=1/80 at hδ
  have hdist := norm_unitaryEvolution_time_sub_le H.2 t v
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at hdist
  have htime := mul_le_mul_of_nonneg_left (show t-v≤clearanceTime H by linarith only [ht.2]) (norm_nonneg H.val)
  have htri := dist_triangle (unitaryEvolution H.val t) (unitaryEvolution H.val v) (z • W.val)
  simp only [dist_eq_norm] at htri
  nlinarith only [htri,hdist,hfit,htime,hδ,(clearance_pos H).le]

/-- Principal-minor coefficients of the circuit adjoint in the Hamiltonian
eigenbasis. These coefficients are independent of observation time. -/
def circuitMinor (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (S : Finset I) : ℂ :=
  let V := H.2.isHermitian.eigenvectorUnitary
  ((star (V⁻¹*W*V).val).submatrix (Subtype.val : S → I) Subtype.val).det

omit [Fintype I] [DecidableEq I] [Nonempty I] in
private theorem prod_phase (E : I → ℝ) (t : ℝ) (S : Finset I) :
    (∏ i ∈ S, wave (-t*E i))=wave (-t*∑ i ∈ S, E i) := by
  simp only [wave,←Complex.exp_sum,←Finset.sum_mul,←Complex.ofReal_sum,Finset.mul_sum]

/-- An observed fit anywhere in the window enforces a signed sinc sum
whose arguments use solely the energy differences with large support. -/
theorem laboratory_window (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) {v a L : ℝ}
    (hv : v∈Icc a (a+L)) (hfit : v∈laboratoryDates H W (1/10)) (q r : ℕ) (hq : q≤Fintype.card I) :
    let w := L+clearanceTime H
    let B : ℝ := (Fintype.card I).choose q
    let d := min q (Fintype.card I-q)
    (clearanceTime H/w)*(B*(1-(9/80:ℝ)^2/2)^d)^2-B*(2^r*(3/2)^Fintype.card I) ≤
      windowSum (univ.powersetCard q) (circuitMinor H W) H.2.isHermitian.eigenvalues r a w := by
  intro w B d
  let l := (v-a)/w
  let u := (v+clearanceTime H-a)/w
  have hw : 0<w := add_pos_of_nonneg_of_pos (by linarith only [hv.1,hv.2]) (clearance_pos H)
  have hl : 0≤l := div_nonneg (sub_nonneg.mpr hv.1) hw.le
  have hlu : l≤u := by apply div_le_div_of_nonneg_right _ hw.le; linarith only [(clearance_pos H).le]
  have hu : u≤1 := (div_le_one hw).mpr (by dsimp only [w]; linarith only [hv.2])
  have hwidth : u-l=clearanceTime H/w := by dsimp only [u,l]; rw [←sub_div]; ring
  let V := H.2.isHermitian.eigenvectorUnitary
  let E := H.2.isHermitian.eigenvalues
  let F := (univ : Finset I).powersetCard q
  have hm (S : Finset I) : ‖circuitMinor H W S‖≤1 := principal_weight_le (V⁻¹*W*V)⁻¹ S
  have h := localized_floor F (circuitMinor H W) (fun S _ => hm S) E r a w l u
    ((B*(1-(9/80:ℝ)^2/2)^d)^2) hl hlu hu (by
      intro x hx
      let t := a+w*x
      have hx₁ := (div_le_iff₀ hw).mp hx.1
      have hx₂ := (le_div_iff₀ hw).mp hx.2
      have ht : t∈Icc v (v+clearanceTime H) := by
        dsimp only [t]; rw [mul_comm w x]; constructor <;> linarith only [hx₁,hx₂]
      have hh := laboratory_fit H W (persistence H W hfit ht) (by norm_num) q hq
      have hh' := pow_le_pow_left₀ (show 0≤B*(1-(9/80:ℝ)^2/2)^d from
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)) hh 2
      have hid : (∑ S ∈ F, circuitMinor H W S*wave (-t*∑ i ∈ S, E i))=
          subsetCharacter (star (V⁻¹*W*V).val) (fun i => wave (-t*E i)) q := by
        exact sum_congr rfl fun S _ => congrArg (circuitMinor H W S*·) (prod_phase E t S).symm
      rw [show (∑ S ∈ F, circuitMinor H W S*wave (-(a+w*x)*∑ i ∈ S, E i))=_ from hid]
      exact hh')
  simpa only [hwidth,F,card_powersetCard,card_univ,B,E] using h

#print axioms laboratory_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
