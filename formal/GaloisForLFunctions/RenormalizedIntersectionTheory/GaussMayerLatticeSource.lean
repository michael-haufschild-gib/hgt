import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerLatticeRenewal
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeSource
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeHeight
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerUnitEvenWordDeterminant
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaSeries

/-! The full positive-lattice source converges in the actual Mayer disc
algebra. Its denominator weights obey the literal Euclidean renewal map. -/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerLatticeRenewal
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerLatticeSource

private theorem re_lower {z : ℂ} (hz : z ∈ outer) : -(1/2 : ℝ) ≤ z.re := by
  have hr := (neg_le_abs (z-1).re).trans (Complex.abs_re_le_norm (z-1))
  have hd : ‖z-1‖ ≤ (3/2 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hz
  simp only [Complex.sub_re,Complex.one_re] at hr
  linarith only [hr,hd]

/-- Coordinates measuring the two distances from the boundary of the positive cone. -/
private def index (p : Cone) : ℕ × ℕ := (p.val.1-1,p.val.2-p.val.1-1)

private theorem index_injective : Function.Injective index := by
  intro p q he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change p.val.1-1=q.val.1-1 at h1
  change p.val.2-p.val.1-1=q.val.2-q.val.1-1 at h2
  have hp := p.property
  have hq := q.property
  apply Subtype.ext
  apply Prod.ext <;> omega

private theorem cone_floor (p : Cone) :
    (3/2 : ℝ)+barnesLattice (1/2) 1 (index p)=(p.val.2 : ℝ)-(p.val.1 : ℝ)/2 := by
  have hp := p.property
  have h1 : p.val.1-1+1=p.val.1 := by omega
  have h2 : p.val.2-p.val.1-1+1+p.val.1=p.val.2 := by omega
  have h1r := congrArg (fun n : ℕ => (n : ℝ)) h1
  have h2r := congrArg (fun n : ℕ => (n : ℝ)) h2
  push_cast at h1r h2r
  simp only [barnesLattice,index,mul_one]
  linarith only [h1r,h2r]

private theorem cone_floor_pos (p : Cone) : 0 < (p.val.2 : ℝ)-(p.val.1 : ℝ)/2 := by
  rw [← cone_floor]
  have h := barnesLattice_nonneg (o1 := 1/2) (o2 := 1) (by norm_num) (by norm_num) (index p)
  linarith only [h]

private theorem denominator_re_lower (p : Cone) {z : ℂ} (hz : z ∈ outer) :
    (p.val.2 : ℝ)-(p.val.1 : ℝ)/2 ≤ ((p.val.1 : ℂ)*z+p.val.2).re := by
  have h := mul_le_mul_of_nonneg_left (re_lower hz) (Nat.cast_nonneg p.val.1 : (0 : ℝ) ≤ p.val.1)
  simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  linarith only [h]

private theorem denominator_re_pos (p : Cone) {z : ℂ} (hz : z ∈ outer) :
    0 < ((p.val.1 : ℂ)*z+p.val.2).re :=
  (cone_floor_pos p).trans_le (denominator_re_lower p hz)

private theorem term_differentiableOn (w : ℂ) (p : Cone) :
    DifferentiableOn ℂ (fun z : ℂ => ((p.val.1 : ℂ)*z+p.val.2)^(-w)) outer := by
  intro z hz
  exact ((((hasDerivAt_id z).const_mul (p.val.1 : ℂ)).add_const (p.val.2 : ℂ)).cpow_const
    (c := -w) (Complex.mem_slitPlane_iff.mpr (Or.inl (denominator_re_pos p hz)))).differentiableAt.differentiableWithinAt

/-- A literal positive denominator power in the actual disc algebra. -/
def term (w : ℂ) (p : Cone) : DiscSpace :=
  ofHolomorphic (fun z => ((p.val.1 : ℂ)*z+p.val.2)^(-w))
    (term_differentiableOn w p).continuousOn
    ((term_differentiableOn w p).mono ball_subset_closedBall)

@[simp] theorem term_apply (w : ℂ) (p : Cone) (z : Disc) :
    (term w p).1 z=((p.val.1 : ℂ)*z.1+p.val.2)^(-w) := rfl

private theorem norm_term_le {w : ℂ} (hw : 0 ≤ w.re) (p : Cone) :
    ‖term w p‖ ≤ Real.exp (Real.pi*|w.im|)*
      ((3/2 : ℝ)+barnesLattice (1/2) 1 (index p))^(-w.re) := by
  have hbase : 0 ≤ (3/2 : ℝ)+barnesLattice (1/2) 1 (index p) := by
    rw [cone_floor]
    exact (cone_floor_pos p).le
  change ‖(term w p).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  rw [term_apply,cone_floor]
  exact (norm_cpow_neg_le_rpow hw (denominator_re_pos p z.property)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (cone_floor_pos p) (denominator_re_lower p z.property)
        (neg_nonpos.mpr hw)) (Real.exp_pos _).le)

/-- Absolute convergence holds in the uniform norm on the full Mayer disc. -/
theorem summable_norm_term {w : ℂ} (hw : 2 < w.re) : Summable (fun p : Cone => ‖term w p‖) := by
  have hb := summable_barnesLattice_rpow (o1 := 1/2) (o2 := 1) (c := 3/2)
    (by norm_num) (by norm_num) (by norm_num) hw
  have hs := (hb.comp_injective index_injective).mul_left (Real.exp (Real.pi*|w.im|))
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le (by linarith only [hw]))

/-- The convergent positive-cone sum, with no formal-series interpretation. -/
def coneSum (w : ℂ) : DiscSpace := ∑' p : Cone, term w p

theorem coneSum_apply {w : ℂ} (hw : 2 < w.re) (z : Disc) :
    (coneSum w).1 z=∑' p : Cone, ((p.val.1 : ℂ)*z.1+p.val.2)^(-w) := by
  exact ((evaluation z).hasSum (summable_norm_term hw).of_norm.hasSum).tsum_eq.symm

/-- Rectangular coordinates identify the real-period cone with the Barnes double zeta. -/
theorem coneSum_apply_real {w : ℂ} (hw : 2 < w.re) (z : Disc) (x : ℝ)
    (hz : z.1=(x : ℂ)) :
    (coneSum w).1 z=barnesDoubleZeta (1+x) 1 w ((2+x : ℝ) : ℂ) := by
  rw [coneSum_apply hw,← rectangleEquiv.tsum_eq
    (fun p : Cone => ((p.val.1 : ℂ)*z.1+p.val.2)^(-w)),barnesDoubleZeta]
  apply tsum_congr
  intro p
  rw [rectangleEquiv_apply,hz]
  congr 1
  simp only [barnesLattice,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_one,
    Complex.ofReal_ofNat,mul_one]
  ring

/-- Principal logarithms respect quotients of two points in the right half-plane. -/
private theorem cpow_quotient {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (v : ℂ) :
    a^v*(b/a)^v=b^v := by
  have ha0 : a ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at ha
  have hb0 : b ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at hb
  have hargA := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hargB := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have hlo : -Real.pi < (Complex.log b-Complex.log a).im := by
    simp only [Complex.sub_im,Complex.log_im]
    linarith only [hargA.2,hargB.1]
  have hhi : (Complex.log b-Complex.log a).im ≤ Real.pi := by
    simp only [Complex.sub_im,Complex.log_im]
    linarith only [hargA.1,hargB.2]
  have hexp : Complex.exp (Complex.log b-Complex.log a)=b/a := by
    rw [Complex.exp_sub,Complex.exp_log hb0,Complex.exp_log ha0]
  have hlog : Complex.log (b/a)=Complex.log b-Complex.log a := by
    rw [← hexp,Complex.log_exp hlo hhi]
  rw [Complex.cpow_def_of_ne_zero ha0,Complex.cpow_def_of_ne_zero (div_ne_zero hb0 ha0),
    Complex.cpow_def_of_ne_zero hb0,← Complex.exp_add,hlog]
  congr 1
  ring

/-- The actual branch action is exactly the positive Euclidean denominator action. -/
theorem branch_term {w : ℂ} (hw : 0 < w.re) (n : ℕ+) (p : Cone) :
    branch w hw n n.property (term w p)=term w (branchPair n p).val := by
  apply Subtype.ext
  ext z
  rw [branch_apply]
  have hz : ((n : ℂ)+z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num) (inverse_branch_inner n.property z.property)
  rw [plane_eq (term w p) ⟨_,hz⟩,term_apply,term_apply]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hza := re_lower z.property
  have ha : 0 < ((n : ℂ)+z.1).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    linarith only [hn,hza]
  have hb := denominator_re_pos (branchPair n p).val z.property
  have ha0 : (n : ℂ)+z.1 ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at ha
  have he : (p.val.1 : ℂ)*((n : ℂ)+z.1)⁻¹+p.val.2=
      ((p.val.2 : ℂ)*z.1+((n : ℕ)*p.val.2+p.val.1 : ℕ))/((n : ℂ)+z.1) := by
    push_cast
    field_simp [ha0]
    ring
  rw [he]
  exact cpow_quotient ha hb (-w)

/-- Evaluation of the actual transfer series in the disc Banach space. -/
private theorem regularized_apply_series {w : ℂ} (hw : 1 < w.re) (f : DiscSpace) :
    regularized w (zero_lt_one.trans hw) f=
      ∑' j : ℕ, branch w (zero_lt_one.trans hw) (j+1) (by omega) f := by
  rw [regularized_eq_tsum_branch hw]
  exact ((ContinuousLinearMap.apply ℂ DiscSpace f).hasSum
    (summable_norm_branch hw).of_norm.hasSum).tsum_eq.symm

/-- Renewal takes the whole positive cone exactly onto its nonmultiple rows. -/
theorem regularized_coneSum {w : ℂ} (hw : 2 < w.re) :
    regularized w (by linarith only [hw]) (coneSum w)=∑' p : NonmultipleCone, term w p.val := by
  have hsC := (summable_norm_term hw).of_norm
  have hsD : Summable (fun p : NonmultipleCone => term w p.val) :=
    hsC.comp_injective Subtype.val_injective
  have hsNP : Summable (fun p : ℕ+ × Cone => term w (renewalEquiv p).val) :=
    renewalEquiv.summable_iff.mpr hsD
  have he (n : ℕ+) : branch w (by linarith only [hw]) n n.property (coneSum w)=
      ∑' p : Cone, term w (branchPair n p).val := by
    have h := (branch w (by linarith only [hw]) n n.property).hasSum hsC.hasSum
    simp only [branch_term] at h
    exact h.tsum_eq.symm
  rw [regularized_apply_series (by linarith only [hw])]
  have hind := Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ =>
    branch w (show 0 < w.re by linarith only [hw]) n n.property (coneSum w))
  change (∑' j : ℕ, branch w (show 0 < w.re by linarith only [hw]) (j+1) (by omega)
    (coneSum w))=_ at hind
  rw [hind]
  simp only [he]
  exact hsNP.tsum_prod.symm.trans (renewalEquiv.tsum_eq (fun p : NonmultipleCone => term w p.val))

/-- The cone partitions into all multiple rays and the image of the branch renewal. -/
theorem coneSum_partition {w : ℂ} (hw : 2 < w.re) :
    coneSum w=(∑' x : ℕ+ × ℕ, term w (multiplePair x.1 x.2))+
      ∑' p : NonmultipleCone, term w p.val := by
  have hs : Summable (fun p : (ℕ+ × ℕ) ⊕ NonmultipleCone => term w (multipleNonmultipleEquiv p)) :=
    multipleNonmultipleEquiv.summable_iff.mpr (summable_norm_term hw).of_norm
  exact (multipleNonmultipleEquiv.tsum_eq (term w)).symm.trans
    ((hs.comp_injective Sum.inl_injective).tsum_sum (hs.comp_injective Sum.inr_injective))

/-- Every multiple ray is a scalar Dirichlet coefficient times one primitive boundary row. -/
theorem multiple_term (w : ℂ) (a : ℕ+) (k : ℕ) :
    term w (multiplePair a k)=(a : ℂ)^(-w) •
      MayerCoprimeSource.term w (MayerCoprimeRenewal.boundaryPair k) := by
  apply Subtype.ext
  ext z
  rw [term_apply]
  change ((a : ℂ)*z.1+((a : ℕ)*(k+2) : ℕ))^(-w)=
    (a : ℂ)^(-w)*(MayerCoprimeSource.term w (MayerCoprimeRenewal.boundaryPair k)).1 z
  rw [MayerCoprimeSource.term_apply]
  have ha : 0 < (a : ℂ).re := by exact_mod_cast a.property
  have hb := denominator_re_pos (multiplePair a k) z.property
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast a.property.ne'
  have he : ((a : ℂ)*z.1+((a : ℕ)*(k+2) : ℕ))/(a : ℂ)=
      (MayerCoprimeRenewal.boundaryPair k).val.1*z.1+
        (MayerCoprimeRenewal.boundaryPair k).val.2 := by
    simp only [MayerCoprimeRenewal.boundaryPair,Nat.cast_one]
    push_cast
    field_simp [ha0]
  have h := cpow_quotient ha hb (-w)
  change (a : ℂ)^(-w)*
    (((a : ℂ)*z.1+((a : ℕ)*(k+2) : ℕ))/(a : ℂ))^(-w)=_ at h
  rw [he] at h
  exact h.symm

private theorem zeta_pnat {w : ℂ} (hw : 1 < w.re) :
    (∑' a : ℕ+, (a : ℂ)^(-w))=riemannZeta w := by
  have he := Equiv.pnatEquivNat.symm.tsum_eq (fun a : ℕ+ => (a : ℂ)^(-w))
  change (∑' n : ℕ, ((n+1 : ℕ) : ℂ)^(-w))=_ at he
  rw [← he,zeta_eq_tsum_one_div_nat_add_one_cpow hw]
  simp only [Nat.cast_add,Nat.cast_one,Complex.cpow_neg,one_div]

private theorem summable_zeta_pnat {w : ℂ} (hw : 1 < w.re) :
    Summable (fun a : ℕ+ => (a : ℂ)^(-w)) := by
  have h := (Complex.summable_one_div_nat_cpow.mpr hw).comp_injective
    (show Function.Injective (fun a : ℕ+ => (a : ℕ)) from Subtype.val_injective)
  simpa only [Function.comp_def,Complex.cpow_neg,one_div] using! h

private theorem boundary_summable {w : ℂ} (hw : 2 < w.re) :
    Summable (fun k : ℕ => MayerCoprimeSource.term w (MayerCoprimeRenewal.boundaryPair k)) := by
  apply (MayerCoprimeSource.summable_norm_term hw).of_norm.comp_injective
  intro k l he
  have h := congrArg (fun p : MayerCoprimeRenewal.Cone => p.val.2) he
  change k+2=l+2 at h
  omega

/-- Missing multiple rays supply exactly the zeta-weighted constant-branch tail. -/
theorem multiple_sum {w : ℂ} (hw : 2 < w.re) :
    (∑' x : ℕ+ × ℕ, term w (multiplePair x.1 x.2))=
      riemannZeta w • (regularized w (by linarith only [hw]) (constant 1)-MayerCoprimeSource.endpoint w) := by
  have hs : Summable (fun p : (ℕ+ × ℕ) ⊕ NonmultipleCone => term w (multipleNonmultipleEquiv p)) :=
    multipleNonmultipleEquiv.summable_iff.mpr (summable_norm_term hw).of_norm
  have hsm := hs.comp_injective Sum.inl_injective
  change Summable (fun x : ℕ+ × ℕ => term w (multiplePair x.1 x.2)) at hsm
  let v : DiscSpace := ∑' k : ℕ, MayerCoprimeSource.term w (MayerCoprimeRenewal.boundaryPair k)
  have hinner (a : ℕ+) : (∑' k : ℕ, term w (multiplePair a k))=(a : ℂ)^(-w) • v := by
    have h := ((a : ℂ)^(-w) • ContinuousLinearMap.id ℂ DiscSpace).hasSum
      (boundary_summable hw).hasSum
    change HasSum (fun k => (a : ℂ)^(-w) •
      MayerCoprimeSource.term w (MayerCoprimeRenewal.boundaryPair k)) ((a : ℂ)^(-w) • v) at h
    simpa only [multiple_term] using h.tsum_eq
  have houter := ((ContinuousLinearMap.id ℂ ℂ).smulRight v).hasSum
    (summable_zeta_pnat (show 1 < w.re by linarith only [hw])).hasSum
  change HasSum (fun a : ℕ+ => (a : ℂ)^(-w) • v) ((∑' a : ℕ+, (a : ℂ)^(-w)) • v) at houter
  have hv : v=regularized w (by linarith only [hw]) (constant 1)-MayerCoprimeSource.endpoint w := by
    rw [MayerCoprimeSource.regularized_constant hw]
    change v=MayerCoprimeSource.endpoint w+v-MayerCoprimeSource.endpoint w
    abel
  rw [hsm.tsum_prod]
  simp only [hinner]
  rw [houter.tsum_eq,zeta_pnat (by linarith only [hw]),hv]

/-- Euclidean renewal of the full cone gives the exact arithmetic forcing term. -/
theorem cone_forcing {w : ℂ} (hw : 2 < w.re) :
    coneSum w-regularized w (by linarith only [hw]) (coneSum w)=
      riemannZeta w • (regularized w (by linarith only [hw]) (constant 1)-MayerCoprimeSource.endpoint w) := by
  rw [regularized_coneSum hw,coneSum_partition hw,multiple_sum hw]
  abel

/-- The actual zeta-cleared lattice response in its absolute-convergence chamber. -/
def response (w : ℂ) : DiscSpace :=
  riemannZeta w • (constant 1+MayerCoprimeSource.endpoint w)+(2 : ℂ) • coneSum w

/-- The full positive lattice cone solves the constant forcing equation with coefficient zeta. -/
theorem response_equation {w : ℂ} (hw : 2 < w.re) :
    response w-regularized w (by linarith only [hw]) (response w)=riemannZeta w • constant 1 := by
  have h0 : 0 < w.re := by linarith only [hw]
  have hr : regularized w h0 (MayerCancellation.response w)=MayerCoprimeSource.endpoint w := by
    rw [← source_eq h0,source,_root_.add_apply,_root_.smul_apply,
      MayerCancellation.projection_response,smul_zero,zero_add,MayerCancellation.remainder_response h0]
    rfl
  have he : regularized w h0 (MayerCoprimeSource.endpoint w)=
      regularized w h0 (constant 1)-MayerCoprimeSource.endpoint w := by
    rw [MayerCoprimeSource.endpoint,map_sub,hr]
    rfl
  have hq : regularized w h0 (coneSum w)=coneSum w-
      riemannZeta w • (regularized w h0 (constant 1)-MayerCoprimeSource.endpoint w) := by
    have h := cone_forcing hw
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact sub_eq_iff_eq_add.mp h |>.symm)
  rw [response,map_add,map_smul,map_smul,map_add,he,hq]
  module

/-- Uniqueness of the actual bounded inverse identifies the full lattice response with the
zeta-cleared primitive response. -/
theorem response_eq_green {w : ℂ} (hw : 2 < w.re) :
    response w=riemannZeta w • MayerCoprimeSource.green w := by
  have h0 : 0 < w.re := by linarith only [hw]
  have hD := MayerUnitOrbitDeterminant.determinant_ne_zero_on_closed_unit
    (w := w) (z := 1) hw (by simp)
  have hu : IsUnit (1-source w) := by
    by_contra hn
    apply hD
    apply (MayerFredholm.determinant_eq_zero_iff_not_isUnit h0 1).mpr
    simpa only [one_smul,← source_eq h0] using hn
  have hinv (f : DiscSpace) : Ring.inverse (1-source w) ((1-source w) f)=f :=
    congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f)
      (Ring.inverse_mul_cancel (1-source w) hu)
  have hj : Function.Injective (fun f : DiscSpace => (1-source w) f) := by
    intro f g he
    have h := congrArg (fun v : DiscSpace => Ring.inverse (1-source w) v) he
    simpa only [hinv] using h
  apply hj
  change response w-source w (response w)=
    riemannZeta w • MayerCoprimeSource.green w-source w (riemannZeta w • MayerCoprimeSource.green w)
  rw [source_eq h0,response_equation hw,map_smul,← smul_sub,MayerCoprimeSource.green_response hw]

/-- The lattice response has the exact non-primitive height count at zero. -/
theorem response_zero {w : ℂ} (hw : 2 < w.re) :
    (response w).1 zeroPoint=2*riemannZeta (w-1) := by
  have hz := riemannZeta_ne_zero_of_one_le_re (show 1 ≤ w.re by linarith only [hw])
  rw [response_eq_green hw]
  change riemannZeta w*(MayerCoprimeSource.green w).1 zeroPoint=_
  rw [MayerCoprimeHeight.green_zero hw]
  field_simp [hz]

#print axioms summable_norm_term
#print axioms coneSum_apply_real
#print axioms regularized_coneSum
#print axioms coneSum_partition
#print axioms multiple_term
#print axioms multiple_sum
#print axioms cone_forcing
#print axioms response_equation
#print axioms response_eq_green
#print axioms response_zero
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerLatticeSource

