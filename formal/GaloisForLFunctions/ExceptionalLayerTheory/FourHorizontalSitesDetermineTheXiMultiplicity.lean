import GaloisForLFunctions.ExceptionalLayerTheory.ReadingXiMultiplicityFromArbitraryNearbySites
import GaloisForLFunctions.ExceptionalLayerTheory.TheOptimalSpacingOfFourHadamardReadings

/-!
# Four horizontal readings determine the ξ multiplicity

At a common vertical offset u, sample the real part of ξ′/ξ at horizontal
offsets −3h, −h, h, 3h. The nodal product about the marked point is real
and equals (u²+h²)(u²+9h²). The cubic divided difference therefore uses
only real data, rejects arbitrary quadratic calibration drift, and has
fourth-order bias uniformly as the stencil shrinks, even when the ratio
of horizontal to vertical displacement has no limit.
-/

noncomputable section
open Complex Filter Metric Finset Topology
open RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def site (p : ℂ) (u x : ℝ) := p+((x:ℂ)+(u:ℂ)*I)
private def cloud (p : ℂ) (u h : ℝ) : Finset ℂ :=
  {site p u (-3*h),site p u (-h),site p u h,site p u (3*h)}

private theorem site_inj (p : ℂ) (u : ℝ) : Function.Injective (site p u) := by
  intro x y h
  exact Complex.ofReal_injective ((add_left_inj _).mp ((add_right_inj _).mp h))

private theorem site_gap (p : ℂ) (u x y : ℝ) :
    site p u x-site p u y=((x-y:ℝ):ℂ) := by unfold site; push_cast; ring

private theorem norm_site (p : ℂ) (u x : ℝ) : dist (site p u x) p ≤ |x|+|u| := by
  rw [dist_eq_norm,site,add_sub_cancel_left]
  exact (norm_add_le ..).trans_eq (by rw [norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs])

private theorem sites_distinct {p : ℂ} {u h : ℝ} (h₀ : h≠0) :
    let a := site p u (-3*h)
    let b := site p u (-h)
    let c := site p u h
    let d := site p u (3*h)
    a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d := by
  dsimp only
  have hi := site_inj p u
  refine ⟨hi.ne ?_,hi.ne ?_,hi.ne ?_,hi.ne ?_,hi.ne ?_,hi.ne ?_⟩ <;>
    intro he <;> exact h₀ (by linarith only [he])

private theorem nodal_pair (p : ℂ) (u v : ℝ) :
    (p-site p u (-v))*(p-site p u v) = -((u^2+v^2:ℝ):ℂ) := by
  unfold site
  push_cast
  linear_combination (u:ℂ)^2 * I_sq

private theorem four_terms (a b c d : ℂ) (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) (f : ℂ → ℂ) :
    (∑ x ∈ ({a,b,c,d}:Finset ℂ), Lagrange.nodalWeight {a,b,c,d} id x*f x) =
      f a/((a-b)*(a-c)*(a-d))+f b/((b-a)*(b-c)*(b-d))+
      f c/((c-a)*(c-b)*(c-d))+f d/((d-a)*(d-b)*(d-c)) := by
  classical
  simp [Lagrange.nodalWeight,Finset.erase_insert_of_ne,hab,hac,had,hbc,hbd,hcd,hab.symm,hac.symm,had.symm,
    hbc.symm,hbd.symm,hcd.symm,div_eq_mul_inv] <;> ring

/-- Four readings of the actual logarithmic derivative. -/
def horizontalFourSiteReading (p : ℂ) (h u : ℝ) : ℝ :=
  let F := fun x => (logDeriv xi (site p u x)).re
  fourSiteReading h u (F (-3*h)) (F (-h)) (F h) (F (3*h))

private theorem four_site_as_barycentric (p : ℂ) {h : ℝ} (hh : h≠0) (u : ℝ) (f : ℂ → ℂ) :
    (barycentricResidue (cloud p u h) p f).re =
      fourSiteReading h u (f (site p u (-3*h))).re (f (site p u (-h))).re
        (f (site p u h)).re (f (site p u (3*h))).re := by
  classical
  let a := site p u (-3*h)
  let b := site p u (-h)
  let c := site p u h
  let d := site p u (3*h)
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ : a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d :=
    sites_distinct (p:=p) (u:=u) hh
  have hp : (∏ x ∈ cloud p u h, (p-x))=((u^2+h^2)*(u^2+9*h^2):ℝ) := by
    change (∏ x ∈ ({a,b,c,d}:Finset ℂ), (p-x))=_
    simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,
      hab,hac,had,hbc,hbd,hcd,or_self,not_false_eq_true]
    have hbc' := nodal_pair p u h
    have had' := nodal_pair p u (3*h)
    rw [show -(3*h)= -3*h by ring] at had'
    change (p-b)*(p-c)=_ at hbc'
    change (p-a)*(p-d)=_ at had'
    calc _ = ((p-b)*(p-c))*((p-a)*(p-d)) := by ring
         _ = _ := by rw [hbc',had']; push_cast; ring
  have hw : (∑ x ∈ cloud p u h,Lagrange.nodalWeight (cloud p u h) id x*f x) =
      (-f a+3*f b-3*f c+f d)/(48*(h:ℂ)^3) := by
    change (∑ x ∈ ({a,b,c,d}:Finset ℂ),Lagrange.nodalWeight {a,b,c,d} id x*f x)=_
    rw [four_terms a b c d hab hac had hbc hbd hcd f]
    have gap (v k : ℝ) :
        site p u (v*h)-site p u (k*h)=((v-k:ℝ):ℂ)*(h:ℂ) := by
      rw [site_gap,←Complex.ofReal_mul]; congr 1; ring
    dsimp only [a,b,c,d]
    simp_rw [show -h=(-1:ℝ)*h by ring]
    have gap₁ (v : ℝ) : site p u (v*h)-site p u h=((v-1:ℝ):ℂ)*(h:ℂ) := by simpa using gap v 1
    have gap₂ (v : ℝ) : site p u h-site p u (v*h)=((1-v:ℝ):ℂ)*(h:ℂ) := by simpa using gap 1 v
    simp only [gap,gap₁,gap₂]
    norm_num only [show (-3:ℝ)-(-1)= -2 by norm_num,show (-3:ℝ)-1= -4 by norm_num,
      show (-3:ℝ)-3= -6 by norm_num,show (-1:ℝ)-(-3)=2 by norm_num,show (-1:ℝ)-1= -2 by norm_num,
      show (-1:ℝ)-3= -4 by norm_num,show (1:ℝ)-(-3)=4 by norm_num,show (1:ℝ)-(-1)=2 by norm_num,
      show (1:ℝ)-3= -2 by norm_num,show (3:ℝ)-(-3)=6 by norm_num,show (3:ℝ)-(-1)=4 by norm_num,
      show (3:ℝ)-1=2 by norm_num,Complex.ofReal_neg,Complex.ofReal_ofNat]
    field_simp [show (h:ℂ)≠0 by exact_mod_cast hh] <;> ring
  let A := ((u^2+h^2)*(u^2+9*h^2))/(48*h^3)
  have he : barycentricResidue (cloud p u h) p f = (A:ℂ)*(f a-3*f b+3*f c-f d) := by
    rw [barycentricResidue,hp,hw]; dsimp only [A]; push_cast; ring
  rw [he,fourSiteReading]
  change _=A*((f a).re-3*(f b).re+3*(f c).re-(f d).re)
  simp [Complex.mul_re]

/-- Fourth-order deterministic bias on the four sites. All aspect
ratios use the same constants. -/
theorem horizontal_four_site_error (p : ℂ) :
    ∃ R C : ℝ, 0<R ∧ 0≤C ∧ ∀ h u : ℝ, h≠0 → 3*|h|+|u|<R →
      |horizontalFourSiteReading p h u-(hadamardOrder p:ℝ)| ≤
        C*((3*|h|+|u|)/(R-(3*|h|+|u|)))^4 := by
  classical
  obtain ⟨R,C,hR,hC,hbound⟩ := xi_residue_error_by_radius p
  refine ⟨R,C,hR,hC,?_⟩
  intro h u hh hr
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := sites_distinct (p:=p) (u:=u) hh
  have hcard : (cloud p u h).card=4 := by
    rw [cloud,Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨hab,hac,had⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨hbc,hbd⟩),
      Finset.card_pair hcd]
  have hne : p∉cloud p u h := by
    have hn (x : ℝ) (hx : x≠0) : p≠site p u x := by
      intro he
      have hr := congrArg Complex.re he
      simp only [site,Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,
        Complex.ofReal_re,mul_zero,zero_mul,sub_zero,add_zero] at hr
      exact hx (by linarith only [hr])
    simp only [cloud,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨hn _ (mul_ne_zero (by norm_num : (-3:ℝ)≠0) hh),hn _ (neg_ne_zero.mpr hh),hn h hh,
      hn _ (mul_ne_zero (by norm_num : (3:ℝ)≠0) hh)⟩
  have hs (x : ℂ) (hx : x∈cloud p u h) : dist x p≤3*|h|+|u| := by
    simp only [cloud,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> apply (norm_site _ _ _).trans <;>
      (try simp only [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<3)]) <;> linarith only [abs_nonneg h]
  have hb := hbound _ (by positivity) hr _ (Finset.card_pos.mp (by omega)) hne hs
  rw [hcard] at hb
  have hreal := (Complex.abs_re_le_norm (barycentricResidue (cloud p u h) p (logDeriv xi)-
    (hadamardOrder p:ℂ))).trans hb
  rw [Complex.sub_re,Complex.natCast_re,four_site_as_barycentric p hh] at hreal
  exact hreal

/-- The multiplicity limit tolerates arbitrary relative shrinking speeds
and horizontal/vertical signs. Horizontal spacing need only be eventually nonzero. -/
theorem four_horizontal_sites_recover_order (p : ℂ) {ι : Type*} {l : Filter ι} {u h : ι → ℝ}
    (hu : Tendsto u l (𝓝 0)) (hh : Tendsto h l (𝓝 0)) (hn : ∀ᶠ i in l, h i≠0) :
    Tendsto (fun i => horizontalFourSiteReading p (h i) (u i)) l (𝓝 (hadamardOrder p:ℝ)) := by
  obtain ⟨R,C,hR,_,hb⟩ := horizontal_four_site_error p
  have hd := (hh.abs.const_mul 3).add hu.abs
  simp only [abs_zero,mul_zero,add_zero] at hd
  have hg := (tendsto_const_nhds (x:=R)).sub hd
  rw [sub_zero] at hg
  have ht := ((hd.div hg hR.ne').pow 4).const_mul C
  simp only [zero_div,zero_pow (by decide : 4≠0),mul_zero] at ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [hn,hd.eventually_lt_const hR] with i hi hri
  exact hb _ _ hi hri

#print axioms horizontal_four_site_error
#print axioms four_horizontal_sites_recover_order
end GaloisForLFunctions.ExceptionalLayerTheory
