import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.TwoClockResolvent
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.SplineResiduePhase

/-!
# Phase-coherent residue clusters

A first-order clock resolvent has nonnegative real part in the left
half-plane. Relative spline regularity bounds the negative error after
phase alignment, without any lower bound on spacing between atoms.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

lemma re_clockDefect_inverse_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {w : ℂ} (hw : w.re ≤ 0) : 0 ≤ ((clockDefect a b w)⁻¹).re := by
  have hea : Real.exp (a*w.re) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos ha hw)
  have heb : Real.exp (b*w.re) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos hb hw)
  have hrea : (Complex.exp ((a:ℂ)*w)).re ≤ Real.exp (a*w.re) := by
    simpa only [Complex.norm_exp,Complex.re_ofReal_mul] using Complex.re_le_norm (Complex.exp ((a:ℂ)*w))
  have hreb : (Complex.exp ((b:ℂ)*w)).re ≤ Real.exp (b*w.re) := by
    simpa only [Complex.norm_exp,Complex.re_ofReal_mul] using Complex.re_le_norm (Complex.exp ((b:ℂ)*w))
  have hden : 0 ≤ (clockDefect a b w).re := by
    simp only [clockDefect,Complex.sub_re,Complex.one_re,Complex.div_ofNat_re,Complex.add_re]
    linarith only [hea,heb,hrea,hreb]
  rw [Complex.inv_re]
  exact div_nonneg hden (Complex.normSq_nonneg _)

lemma norm_mul_clockDefect_inverse_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : ‖w‖ ≤ 1/(2*(a+b))) :
    ‖w‖*‖(clockDefect a b w)⁻¹‖ ≤ 4/(a+b) := by
  have hk : 0 < a+b := add_pos ha hb
  by_cases hzero : clockDefect a b w=0
  · rw [hzero,inv_zero,norm_zero,mul_zero]
    positivity
  have hden : 0 < ‖clockDefect a b w‖ := norm_pos_iff.mpr hzero
  rw [norm_inv,← div_eq_mul_inv,div_le_div_iff₀ hden hk]
  have hh := clockDefect_lower_near_zero ha hb hw
  nlinarith only [hh]

/-- Moving the center beyond the support boundary increases its distance
from every point whose real part lies inside that boundary. -/
lemma norm_sub_le_norm_boundary_center {z z₀ : ℂ} {D s : ℝ}
    (hz : z.re ≤ D) (hz₀ : z₀.re ≤ D) (hgap : D-z₀.re ≤ s) :
    ‖z-z₀‖ ≤ ‖z-((D+s:ℝ):ℂ)-(z₀.im:ℂ)*I‖ := by
  have hs : 0 ≤ s := (sub_nonneg.mpr hz₀).trans hgap
  have hprod : 0 ≤ (s+(D-z₀.re))*(s-(D-z₀.re)+2*(D-z.re)) := by
    apply mul_nonneg
    · linarith only [hs,hz₀]
    · linarith only [hgap,hz]
  have hsq : (z.re-z₀.re)^2 ≤ (z.re-(D+s))^2 := by
    nlinarith only [hprod]
  have hleft := Complex.normSq_eq_norm_sq (z-z₀)
  have hright := Complex.normSq_eq_norm_sq (z-((D+s:ℝ):ℂ)-(z₀.im:ℂ)*I)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,
    mul_one,sub_zero] at hleft hright
  nlinarith only [hsq,hleft,hright,norm_nonneg (z-z₀),
    norm_nonneg (z-((D+s:ℝ):ℂ)-(z₀.im:ℂ)*I)]

/-- Aligned nearby exact residues have only a bounded negative contribution
to the first-order resolvent, independently of the distance between atoms. -/
theorem exists_spline_cluster_re_lower {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z z₀ u w : ℂ,
      d ≤ z.re → z.re ≤ D → d ≤ z₀.re → z₀.re ≤ D →
      ‖u‖=1 → u*splineResidue a b z₀=(‖splineResidue a b z₀‖:ℂ) →
      w.re ≤ 0 → ‖z-z₀‖ ≤ ‖w‖ → ‖w‖ ≤ 1 → ‖w‖ ≤ 1/(2*(a+b)) →
      -(C*‖splineResidue a b z‖) ≤
        (u*splineResidue a b z*(clockDefect a b w)⁻¹).re := by
  obtain ⟨L,hL,hrel⟩ := exists_splineResidue_relative_lipschitz (D := D) ha hb hd
  have hk : 0 < a+b := add_pos ha hb
  refine ⟨L*(4/(a+b)),mul_pos hL (div_pos (by norm_num) hk),?_⟩
  intro z z₀ u w hzd hzD hz₀d hz₀D hu hphase hwre hdist hw1 hw
  have hdiff : ‖splineResidue a b z-splineResidue a b z₀‖ ≤
      L*‖splineResidue a b z‖*‖z-z₀‖ := by
    have hh := hrel z₀ z hz₀d hz₀D hzd hzD (by rw [norm_sub_rev]; exact hdist.trans hw1)
    simpa only [norm_sub_rev] using hh
  let R := (clockDefect a b w)⁻¹
  have hR : 0 ≤ R.re := re_clockDefect_inverse_nonneg ha.le hb.le hwre
  have hmain : 0 ≤ (u*splineResidue a b z₀*R).re := by
    rw [hphase,Complex.re_ofReal_mul]
    exact mul_nonneg (norm_nonneg _) hR
  have herr : ‖u*(splineResidue a b z-splineResidue a b z₀)*R‖ ≤
      L*(4/(a+b))*‖splineResidue a b z‖ := by
    rw [norm_mul,norm_mul,hu,one_mul]
    calc
      _ ≤ (L*‖splineResidue a b z‖*‖z-z₀‖)*‖R‖ :=
        mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ ≤ (L*‖splineResidue a b z‖*‖w‖)*‖R‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity)) (norm_nonneg _)
      _ = (L*‖splineResidue a b z‖)*(‖w‖*‖R‖) := by ring
      _ ≤ (L*‖splineResidue a b z‖)*(4/(a+b)) :=
        mul_le_mul_of_nonneg_left (norm_mul_clockDefect_inverse_le ha hb hw) (by positivity)
      _ = _ := by ring
  have hneg := Complex.re_le_norm (-(u*(splineResidue a b z-splineResidue a b z₀)*R))
  rw [Complex.neg_re,norm_neg] at hneg
  have he : u*splineResidue a b z*R=u*splineResidue a b z₀*R+
      u*(splineResidue a b z-splineResidue a b z₀)*R := by ring
  change -(L*(4/(a+b))*‖splineResidue a b z‖) ≤ (u*splineResidue a b z*R).re
  rw [he,Complex.add_re]
  linarith only [hmain,herr,hneg]

/-- A distinguished aligned atom is bounded by the total resolvent norm
plus any summable majorant for the other atoms' negative real parts. -/
lemma aligned_atom_le_sum_norm_add_error {ι : Type*} {f : ι → ℂ} {e : ι → ℝ}
    (hf : Summable f) (he : Summable e) (i : ι) (u : ℂ) (hu : ‖u‖=1)
    (hei : 0 ≤ e i) (hneg : ∀ j ≠ i, -(e j) ≤ (u*f j).re) :
    (u*f i).re ≤ ‖∑' j, f j‖+∑' j, e j := by
  have hs := (Complex.hasSum_re (hf.hasSum.mul_left u)).add he.hasSum
  have hle := hs.summable.le_tsum i (fun j hj => by linarith only [hneg j hj])
  rw [hs.tsum_eq] at hle
  have hr := Complex.re_le_norm (u*(∑' j, f j))
  rw [norm_mul,hu,one_mul] at hr
  linarith only [hle,hr,hei]

#print axioms norm_sub_le_norm_boundary_center
#print axioms exists_spline_cluster_re_lower
#print axioms aligned_atom_le_sum_norm_add_error
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
