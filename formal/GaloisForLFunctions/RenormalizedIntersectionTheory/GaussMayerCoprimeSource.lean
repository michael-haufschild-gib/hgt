import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeRenewal
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNegativeUnitCancellation
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaSeries

/-! The primitive positive-lattice source converges in the actual Mayer disc
algebra. Its denominator weights obey the literal Euclidean renewal map. -/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerCoprimeRenewal
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeSource

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

/-- A literal primitive denominator power in the actual disc algebra. -/
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

/-- The convergent primitive-cone sum, with no formal-series interpretation. -/
def coneSum (w : ℂ) : DiscSpace := ∑' p : Cone, term w p

theorem coneSum_apply {w : ℂ} (hw : 2 < w.re) (z : Disc) :
    (coneSum w).1 z=∑' p : Cone, ((p.val.1 : ℂ)*z.1+p.val.2)^(-w) := by
  exact ((evaluation z).hasSum (summable_norm_term hw).of_norm.hasSum).tsum_eq.symm

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

/-- The actual branch action is exactly the primitive Euclidean denominator action. -/
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

/-- Renewal takes the whole primitive cone exactly onto its deep rows. -/
theorem regularized_coneSum {w : ℂ} (hw : 2 < w.re) :
    regularized w (by linarith only [hw]) (coneSum w)=∑' p : DeepCone, term w p.val := by
  have hsC := (summable_norm_term hw).of_norm
  have hsD : Summable (fun p : DeepCone => term w p.val) :=
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
  exact hsNP.tsum_prod.symm.trans (renewalEquiv.tsum_eq (fun p : DeepCone => term w p.val))

/-- The boundary and deep rows partition the convergent primitive-cone sum. -/
theorem coneSum_boundary_deep {w : ℂ} (hw : 2 < w.re) :
    coneSum w=(∑' k : ℕ, term w (boundaryPair k))+(∑' p : DeepCone, term w p.val) := by
  have hs : Summable (fun p : ℕ ⊕ DeepCone => term w (boundaryDeepEquiv p)) :=
    boundaryDeepEquiv.summable_iff.mpr (summable_norm_term hw).of_norm
  exact (boundaryDeepEquiv.tsum_eq (term w)).symm.trans
    ((hs.comp_injective Sum.inl_injective).tsum_sum (hs.comp_injective Sum.inr_injective))

/-- The endpoint denominator, represented using the already admitted successor response. -/
def endpoint (w : ℂ) : DiscSpace := constant 1-MayerCancellation.response w

theorem endpoint_apply (w : ℂ) (z : Disc) : (endpoint w).1 z=(1+z.1)^(-w) := by
  change 1-(1-(1+z.1)^(-w))=_
  ring

private theorem branch_constant (w : ℂ) (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n) (z : Disc) :
    (branch w hw n hn (constant 1)).1 z=((n : ℂ)+z.1)^(-w) := by
  rw [branch_apply]
  have hz : ((n : ℂ)+z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num) (inverse_branch_inner hn z.property)
  rw [plane_eq (constant 1) ⟨_,hz⟩]
  change _*1=_
  rw [mul_one]

/-- The constant branch sum consists of the endpoint and the first-coordinate-one rows. -/
theorem regularized_constant {w : ℂ} (hw : 2 < w.re) :
    regularized w (by linarith only [hw]) (constant 1)=
      endpoint w+∑' k : ℕ, term w (boundaryPair k) := by
  have h1 : 1 < w.re := by linarith only [hw]
  have hseries := (ContinuousLinearMap.apply ℂ DiscSpace (constant 1)).hasSum
    (summable_norm_branch h1).of_norm.hasSum
  have hs : Summable (fun j : ℕ => branch w (zero_lt_one.trans h1) (j+1) (by omega) (constant 1)) :=
    hseries.summable
  rw [regularized_apply_series h1,hs.tsum_eq_zero_add]
  have hzero : branch w (zero_lt_one.trans h1) (0+1) (by omega) (constant 1)=endpoint w := by
    apply Subtype.ext
    ext z
    rw [branch_constant,endpoint_apply]
    norm_num
  have hsucc (k : ℕ) : branch w (zero_lt_one.trans h1) (k+1+1) (by omega) (constant 1)=
      term w (boundaryPair k) := by
    apply Subtype.ext
    ext z
    rw [branch_constant,term_apply]
    simp only [boundaryPair,Nat.cast_one,one_mul]
    congr 1
    push_cast
    ring
  rw [hzero]
  simp only [hsucc]

/-- The explicit primitive-cone Green source in the actual disc algebra. -/
def green (w : ℂ) : DiscSpace := constant 1+endpoint w+(2 : ℂ) • coneSum w

private theorem regularized_successor_response {w : ℂ} (hw : 0 < w.re) :
    regularized w hw (MayerCancellation.response w)=endpoint w := by
  rw [← source_eq hw,source,_root_.add_apply,_root_.smul_apply,
    MayerCancellation.projection_response,smul_zero,zero_add,MayerCancellation.remainder_response hw]
  rfl

/-- The actual primitive-cone source solves the constant forcing equation. -/
theorem green_response {w : ℂ} (hw : 2 < w.re) :
    green w-regularized w (by linarith only [hw]) (green w)=constant 1 := by
  have hE : regularized w (show 0 < w.re by linarith only [hw]) (endpoint w)=
      regularized w (show 0 < w.re by linarith only [hw]) (constant 1)-endpoint w := by
    rw [endpoint,map_sub,regularized_successor_response]
    rfl
  rw [green,map_add,map_add,map_smul,hE,regularized_coneSum hw,regularized_constant hw,
    coneSum_boundary_deep hw,smul_add]
  module

#print axioms regularized_coneSum
#print axioms coneSum_boundary_deep
#print axioms regularized_constant
#print axioms green_response
#print axioms summable_norm_term
#print axioms coneSum_apply
#print axioms branch_term

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeSource
