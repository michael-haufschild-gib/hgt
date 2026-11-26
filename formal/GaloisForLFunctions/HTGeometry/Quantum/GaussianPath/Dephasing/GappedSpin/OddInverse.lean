import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.NormalForm
import Mathlib.Topology.MetricSpace.Contracting

/-! # Inverting the commutator across two separated spin sectors -/

open Set
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private def bracket (W X : A) := W*X-X*W

private theorem bracket_norm (W X : A) : ‖bracket W X‖≤2*‖W‖*‖X‖ :=
  (norm_sub_le ..).trans ((add_le_add (norm_mul_le W X) (norm_mul_le X W)).trans_eq (by ring))

/-- A field coupling opposite spin sectors is an exact commutator.
The inverse costs at most the reciprocal of the gap between the bands,
regardless of multiplicities and spacings within either band. -/
theorem odd_commutator_inverse (Z W V : A) (hZ : Z*Z=1) (hn : ‖Z‖≤1)
    (hW : Z*W=W*Z) (hV : Z*V=-(V*Z)) {h : ℝ} (hg : ‖W‖<h) :
    ∃ X : A, (h • Z+W)*X-X*(h • Z+W)=V ∧
      ‖X‖≤‖V‖/(2*(h-‖W‖)) := by
  have hh := (norm_nonneg W).trans_lt hg
  let c := (2*h)⁻¹
  let q : ℝ≥0 := ⟨‖W‖/h,div_nonneg (norm_nonneg _) hh.le⟩
  have hc : 0<c := inv_pos.mpr (mul_pos two_pos hh)
  have hq : (q:ℝ)<1 := (div_lt_one hh).mpr hg
  let O := {X : A | Z*X=-(X*Z)}
  have hclosed : IsClosed O := isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const).neg
  letI : CompleteSpace O := hclosed.isComplete.completeSpace_coe
  let o : O := ⟨0,by simp [O]⟩
  letI : Nonempty O := ⟨o⟩
  have hb (X : O) : Z*bracket W X.val=-(bracket W X.val*Z) := by
    have ho : Z*X.val=-(X.val*Z) := X.property
    calc
      _ = W*(Z*X.val)-(Z*X.val)*W := by
        dsimp only [bracket]
        rw [mul_sub,←mul_assoc Z W,hW,mul_assoc W Z,←mul_assoc Z X.val]
      _ = _ := by simp only [ho,bracket,mul_neg,neg_mul,sub_mul,mul_assoc,hW]; abel
  let F : O→O := fun X => ⟨c • (Z*(V-bracket W X.val)),by
    let Y := V-bracket W X.val
    have hy : Z*Y=-(Y*Z) := by
      dsimp only [Y]; rw [mul_sub,sub_mul,hV,hb]; abel
    change Z*(c • (Z*Y))=-((c • (Z*Y))*Z)
    rw [mul_smul_comm,smul_mul_assoc,←smul_neg]
    exact congrArg (fun v : A => c • v) (calc
      Z*(Z*Y)=Z*(-(Y*Z)) := congrArg (Z*·) hy
      _ = -((Z*Y)*Z) := by rw [mul_neg,mul_assoc])⟩
  have hleft (Y : A) : ‖Z*Y‖≤‖Y‖ := (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) hn)
  have hcontr : ContractingWith q F := by
    refine ⟨(show q<1 from hq),LipschitzWith.of_dist_le_mul (fun X Y => ?_)⟩
    change dist ((F X).val) ((F Y).val)≤(q:ℝ)*dist X.val Y.val
    simp only [dist_eq_norm]
    change ‖c • (Z*(V-bracket W X.val))-c • (Z*(V-bracket W Y.val))‖≤(q:ℝ)*‖X.val-Y.val‖
    have he : (V-bracket W X.val)-(V-bracket W Y.val)=bracket W (Y.val-X.val) := by
      dsimp only [bracket]; noncomm_ring
    rw [←smul_sub,←mul_sub,he,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    apply (mul_le_mul_of_nonneg_left ((hleft _).trans (bracket_norm ..)) hc.le).trans_eq
    rw [norm_sub_rev Y.val X.val]
    dsimp only [c,q]; field_simp; ring
  let x := hcontr.fixedPoint F
  let X := x.val
  have hx : c • (Z*(V-bracket W X))=X := congrArg Subtype.val hcontr.fixedPoint_isFixedPt
  have hxZ : X*Z=-(Z*X) := by
    have ho : Z*X=-(X*Z) := x.property
    rw [ho,neg_neg]
  have hZX : Z*X=c • (V-bracket W X) := calc
    _ = Z*(c • (Z*(V-bracket W X))) := congrArg (Z*·) hx.symm
    _ = _ := by rw [mul_smul_comm,←mul_assoc Z Z,hZ,one_mul]
  have hsolve : (2*h) • (Z*X)=V-bracket W X := by
    rw [hZX,smul_smul,mul_inv_cancel₀ (mul_pos two_pos hh).ne',one_smul]
  refine ⟨X,?_,?_⟩
  · calc
      _ = (2*h) • (Z*X)+bracket W X := by
        rw [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hxZ,smul_neg,two_mul,add_smul]
        dsimp only [bracket]; abel
      _ = V := by rw [hsolve]; abel
  · have hd := hcontr.dist_fixedPoint_le o
    change dist (0:A) X≤dist (0:A) (F o).val/(1-(q:ℝ)) at hd
    simp only [dist_eq_norm] at hd
    change ‖(0:A)-X‖≤‖(0:A)-c • (Z*(V-bracket W 0))‖/(1-(q:ℝ)) at hd
    simp only [zero_sub,norm_neg,bracket,mul_zero,zero_mul,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hc] at hd
    refine hd.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hleft V) hc.le)
      (sub_nonneg.mpr hq.le)).trans_eq ?_)
    dsimp only [c,q]; field_simp [(sub_pos.mpr hg).ne',hh.ne']; ring

#print axioms odd_commutator_inverse
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin
