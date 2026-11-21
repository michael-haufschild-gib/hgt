import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius

/-! # Projective operator error between two simultaneous spectral evolutions -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section

private def phase (x : ℝ) : ℂ := Complex.exp (((-x:ℝ):ℂ)*Complex.I)

private theorem phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_norm (a : ℝ) : ‖phase a‖=1 := by simp [phase,Complex.norm_exp]

private theorem phase_evolution (t x : ℝ) :
    Complex.exp (-(Complex.I*((t:ℂ)*(x:ℂ))))=phase (t*x) := by
  unfold phase
  congr 1
  push_cast
  ring

private def packet {I : Type*} [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (x : I → ℝ) :=
  V*Matrix.diagonal (fun i => phase (x i))*star V

/-- A simultaneous winding approximation for the difference of two
phase packets yields the same uniform operator bound in any eigenbasis. -/
theorem packet_close {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (V : Matrix I I ℂ) (hV : V ∈ unitary (Matrix I I ℂ)) (x y : I → ℝ) (a : I)
    {r : ℝ} (hr : 0≤r) (hc : ∀ i, latticeClose (((x i-x a)-(y i-y a))/(2*π)) r) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖packet V x-z • packet V y‖ ≤ 2*π*r := by
  let z := phase (x a-y a)
  have hd : Matrix.diagonal (fun i => z*phase (y i))=z • Matrix.diagonal (fun i => phase (y i)) := by
    ext i j
    by_cases h : i=j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  have he : packet V x-z • packet V y=V*Matrix.diagonal (fun i => phase (x i)-z*phase (y i))*star V := by
    rw [←Matrix.diagonal_sub,hd,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
    rfl
  refine ⟨z,phase_norm _,?_⟩
  rw [he,l2_opNorm_unitary_conj_eq hV,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤2*π*r)).mpr
  intro i
  obtain ⟨m,hm⟩ := hc i
  change ‖phase (x i)-phase (x a-y a)*phase (y i)‖ ≤ _
  rw [←phase_add]
  have hh := norm_expI_sub_expI_le (-x i) (-(x a-y a+y i)) (-m)
  refine hh.trans ?_
  have hpi : 0<2*π := by positivity
  rw [show -x i - -(x a-y a+y i)-2*π*((-m:ℤ):ℝ) =
      -(2*π*(((x i-x a)-(y i-y a))/(2*π)-m)) by push_cast; field_simp; ring,
    abs_neg,abs_mul,abs_of_pos hpi]
  exact mul_le_mul_of_nonneg_left hm.le hpi.le

private theorem evolution_packet {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (V : Matrix I I ℂ) (hV : V ∈ unitary (Matrix I I ℂ)) (E : I → ℝ) (t : ℝ) :
    unitaryEvolution (V*Matrix.diagonal (fun i => (E i:ℂ))*star V) t=packet V (fun i => t*E i) := by
  rw [unitaryEvolution_conj_diagonal V hV E t]
  simp only [packet,phase_evolution]

private theorem square_conjugate {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (V : Matrix I I ℂ) (hV : V ∈ unitary (Matrix I I ℂ)) (E : I → ℝ) (b : ℝ) :
    (V*Matrix.diagonal (fun i => (E i:ℂ))*star V-(b:ℂ) • (1 : Matrix I I ℂ))^2 =
      V*Matrix.diagonal (fun i => (((E i-b)^2:ℝ):ℂ))*star V := by
  let D := Matrix.diagonal (fun i => ((E i-b:ℝ):ℂ))
  have hb : (b:ℂ) • (1 : Matrix I I ℂ) = V*Matrix.diagonal (fun _ : I => (b:ℂ))*star V := by
    rw [←smul_one_eq_diagonal_const,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,(Unitary.mem_iff.mp hV).2]
  have hs : V*Matrix.diagonal (fun i => (E i:ℂ))*star V-(b:ℂ) • (1 : Matrix I I ℂ) = V*D*star V := by
    rw [hb,←Matrix.sub_mul,←Matrix.mul_sub,←Matrix.diagonal_sub]
    simp only [D,Complex.ofReal_sub]
  rw [hs,sq]
  calc
    _ = V*(D*D)*star V := by
      simp only [mul_assoc]
      rw [←mul_assoc (star V) V _,(Unitary.mem_iff.mp hV).1,one_mul]
    _ = _ := by simp only [D,Matrix.diagonal_mul_diagonal,←sq,Complex.ofReal_pow]

/-- Winding control transverse to the physical generator gives approximation
by the actual time evolution of its shifted square. -/
theorem quadratic_close {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (b : ℝ) (a : I) {t β r : ℝ} (hr : 0≤r) :
    let E := hH.eigenvalues
    let F := fun i => (E i-b)^2
    (∀ i, latticeClose ((t*(E i-E a)-β*(F i-F a))/(2*π)) r) →
    ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution H t -
      z • unitaryEvolution ((H-(b:ℂ) • 1)^2) β‖ ≤ 2*π*r := by
  intro E F hc
  let V : Matrix I I ℂ := hH.eigenvectorUnitary
  have hV : V ∈ unitary (Matrix I I ℂ) := hH.eigenvectorUnitary.2
  have he : H=V*Matrix.diagonal (fun i => (E i:ℂ))*star V := isHermitian_eq_conj_diagonal hH
  have hf : (H-(b:ℂ) • 1)^2=V*Matrix.diagonal (fun i => (F i:ℂ))*star V := by
    conv_lhs => rw [he]
    exact square_conjugate V hV E b
  rw [hf,he,evolution_packet V hV E,evolution_packet V hV F]
  apply packet_close V hV _ _ a hr
  simpa only [mul_sub] using hc

#print axioms quadratic_close
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
