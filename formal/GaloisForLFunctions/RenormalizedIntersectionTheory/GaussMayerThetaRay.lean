import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeatRepresentation
import GaloisForLFunctions.HTGeometry.PerronRationalKernels

/-! The reciprocal-volume subtraction of the actual Gaussian theta ray has an
absolutely convergent Mellin transform in the open half-strip. Subtracting two
explicit cutoff powers from the modified theta kernel recovers completed zeta. -/

open Complex Set Filter MeasureTheory HurwitzZeta
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.HTGeometry
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaRay

/-- The actual positive Gaussian ray with its reciprocal-volume term removed. -/
def thetaRay (t : ℝ) : ℂ := ((thetaSum t : ℂ)-1-(t : ℂ)^(-1/2 : ℂ))/2

private def head (t : ℝ) : ℂ := (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t

private def tail (t : ℝ) : ℂ := ((t⁻¹ : ℝ) : ℂ)^(1/2 : ℂ)*head t⁻¹

private theorem head_hasMellin {u : ℂ} (hu : 0 < u.re) : HasMellin head u (1/u) := by
  have hr : -1 < (u-1).re := by simp; linarith only [hu]
  have heq : (fun t : ℝ => (t : ℂ)^(u-1) • head t)=
      (Ioo (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ)^(u-1)) := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · simp only [head,Set.indicator_of_mem ht,smul_eq_mul,mul_one]
    · simp only [head,Set.indicator_of_notMem ht,smul_zero]
  constructor
  · change IntegrableOn (fun t : ℝ => (t : ℂ)^(u-1) • head t) (Ioi 0)
    rw [heq]
    exact ((integrableOn_Ioo_cpow hr).integrable_indicator measurableSet_Ioo).integrableOn
  · change (∫ t in Ioi (0 : ℝ),(t : ℂ)^(u-1) • head t)=1/u
    rw [heq,setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_Ioo_cpow hr,sub_add_cancel]

private theorem tail_hasMellin {u : ℂ} (hu : u.re < 1/2) : HasMellin tail u (1/(1/2-u)) := by
  have hh : 0 < (-u+1/2).re := by simp; linarith only [hu]
  have h : MellinConvergent (fun t : ℝ => (t : ℂ)^(1/2 : ℂ) • head t) (-u) := by
    rw [MellinConvergent.cpow_smul]
    exact (head_hasMellin hh).1
  have hi := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => (t : ℂ)^(1/2 : ℂ) • head t) (s := u) (a := -1) (by norm_num)).mpr
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one] using h)
  constructor
  · unfold tail
    simpa only [Real.rpow_neg_one,smul_eq_mul] using! hi
  · have he := mellin_comp_inv (fun t : ℝ => (t : ℂ)^(1/2 : ℂ) • head t) u
    rw [mellin_cpow_smul,(head_hasMellin hh).2] at he
    simpa only [tail,smul_eq_mul,show -u+1/2=1/2-u by ring] using! he

private theorem tail_of_pos {t : ℝ} (ht : 0 < t) :
    tail t=(t : ℂ)^(-1/2 : ℂ)*head t⁻¹ := by
  rw [tail,Complex.ofReal_inv,Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm),← Complex.cpow_neg]
  congr 2
  ring

private theorem thetaRay_eq_modified {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    thetaRay t=((hurwitzEvenFEPair 0).f_modif t-head t-tail t)/2 := by
  have hp : ((t^(-1/2 : ℝ) : ℝ) : ℂ)=(t : ℂ)^(-1/2 : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    congr 1
    push_cast
    ring
  rw [thetaRay,thetaSum_eq_evenKernel ht,tail_of_pos ht]
  rcases lt_or_gt_of_ne ht1 with hs | hl
  · have hsmall : t ∈ Ioo (0 : ℝ) 1 := ⟨ht,hs⟩
    have hlarge : t ∉ Ioi (1 : ℝ) := not_lt.mpr hs.le
    have hi : 1 < t⁻¹ := by
      have hdiv : (1 : ℝ) < 1/t := (lt_div_iff₀ ht).mpr (by simpa only [one_mul] using hs)
      simpa only [one_div] using hdiv
    have hnot : t⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt.mpr hi.le) h.2
    simp [WeakFEPair.f_modif,head,hurwitzEvenFEPair,Function.comp_def,hsmall,hlarge,hnot]
    rw [← hp]
    ring
  · have hsmall : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt.mpr hl.le) h.2
    have hlarge : t ∈ Ioi (1 : ℝ) := hl
    have hinv : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht,by
      simpa only [one_div] using (div_lt_one ht).mpr hl⟩
    simp [WeakFEPair.f_modif,head,hurwitzEvenFEPair,Function.comp_def,hsmall,hlarge,hinv]

/-- Removing the reciprocal-volume term gives the actual completed zeta Mellin transform
in the open half-strip. -/
theorem thetaRay_hasMellin_completed {u : ℂ} (hu : 0 < u.re) (hu1 : u.re < 1/2) :
    HasMellin thetaRay u (completedRiemannZeta (2*u)) := by
  have hF : HasMellin (hurwitzEvenFEPair 0).f_modif u ((hurwitzEvenFEPair 0).Λ₀ u) :=
    ⟨((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin u).1,rfl⟩
  have hh := head_hasMellin hu
  have ht := tail_hasMellin hu1
  have hs1 := hasMellin_sub hF.1 hh.1
  have hs2 := hasMellin_sub hs1.1 ht.1
  have hm := hasMellin_const_smul hs2.1 (1/2 : ℂ)
  rw [hs2.2,hs1.2,hF.2,hh.2,ht.2] at hm
  have hval : (1/2 : ℂ) • ((hurwitzEvenFEPair 0).Λ₀ u-1/u-1/(1/2-u))=
      completedRiemannZeta (2*u) := by
    have he : completedRiemannZeta₀ (2*u)=(hurwitzEvenFEPair 0).Λ₀ u/2 := by
      rw [completedRiemannZeta₀,completedHurwitzZetaEven₀,show 2*u/2=u by ring]
    have hu0 : u ≠ 0 := by rintro rfl; norm_num at hu
    have hhalf : (1/2 : ℂ)-u ≠ 0 := by
      intro heq
      have hr := congrArg Complex.re heq
      norm_num at hr
      linarith only [hu1,hr]
    have htwo : (1 : ℂ)-2*u ≠ 0 := by
      intro heq
      have hr := congrArg Complex.re heq
      norm_num at hr
      linarith only [hu1,hr]
    rw [completedRiemannZeta_eq,he,smul_eq_mul]
    field_simp
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
  have hae : thetaRay =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (1/2 : ℂ) • ((hurwitzEvenFEPair 0).f_modif t-head t-tail t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hne] with t ht ht1
    rw [thetaRay_eq_modified ht ht1,smul_eq_mul]
    ring
  constructor
  · apply MeasureTheory.Integrable.congr hm.1
    filter_upwards [hae] with t ht
    rw [ht]
  · calc
      mellin thetaRay u=mellin
          (fun t => (1/2 : ℂ) • ((hurwitzEvenFEPair 0).f_modif t-head t-tail t)) u := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with t ht
        rw [ht]
      _ = _ := hm.2.trans hval

/-- The renormalized Gaussian ray has the exact Gamma–zeta transform with absolute convergence. -/
theorem thetaRay_hasMellin {u : ℂ} (hu : 0 < u.re) (hu1 : u.re < 1/2) :
    HasMellin thetaRay u (Gammaℝ (2*u)*riemannZeta (2*u)) := by
  have hpos : 0 < (2*u).re := by simp; linarith only [hu]
  have h0 : 2*u ≠ 0 := by intro he; rw [he] at hpos; simp at hpos
  have hG : Gammaℝ (2*u) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  have he : completedRiemannZeta (2*u)=Gammaℝ (2*u)*riemannZeta (2*u) := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  simpa only [he] using thetaRay_hasMellin_completed hu hu1

#print axioms thetaRay_hasMellin_completed
#print axioms thetaRay_hasMellin

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaRay
