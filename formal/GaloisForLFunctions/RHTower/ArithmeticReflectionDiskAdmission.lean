import GaloisForLFunctions.RHTower.ArithmeticReflectionErrorHeight
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing

/-!
# Simultaneous admission to the complete reflection-response disks

The actual critical logarithmic source plus the exact complex zero target has norm below
`4 / |Im s|` once `|Im s| ≥ 1`, without a zero condition. In the outer quarters of the open
strip, every source above height 1536 therefore satisfies both currently proved necessary
zero disks with explicit strict slack. Isolated zeros supply actual cofinal nonzero witnesses
on `Re s = 3/4`. These inequalities remain necessary at zeros; their simultaneous admission
supplies no separation in this region. The exact source balance is retained.
-/

open Complex Real Set Filter Topology
noncomputable section
namespace RHTower.DeletionMixedRefinement

/-- Actual full logarithmic response plus the exact complex zero target. -/
def reflectionDiskSource (s : ℂ) : ℂ :=
  criticalFullLogResponse s.im+
    (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
      1/(12*(star s+1)*(2-s)))

/-- Both quadratic factors retain at least the squared height. -/
theorem reflection_target_normSq_lower (s : ℂ) :
    |s.im|^4 ≤ Complex.normSq (star s*(1-star s)) := by
  have ha : |s.im|^2 ≤ Complex.normSq (star s) := by
    simp only [sq_abs,Complex.normSq_apply,Complex.star_def,Complex.conj_re,Complex.conj_im]
    nlinarith [sq_nonneg s.re]
  have hb : |s.im|^2 ≤ Complex.normSq (1-star s) := by
    simp only [sq_abs,Complex.normSq_apply,Complex.star_def,Complex.sub_re,Complex.one_re,
      Complex.conj_re,Complex.sub_im,Complex.one_im,Complex.conj_im]
    nlinarith [sq_nonneg (1-s.re)]
  rw [Complex.normSq_mul]
  calc |s.im|^4 = |s.im|^2*|s.im|^2 := by ring
       _ ≤ Complex.normSq (star s)*Complex.normSq (1-star s) :=
         mul_le_mul ha hb (sq_nonneg _) (Complex.normSq_nonneg _)

/-- The exact mean denominator retains two factors of the height. -/
theorem reflection_target_mean_norm_lower (s : ℂ) :
    12*|s.im|^2 ≤ ‖(12:ℂ)*(star s+1)*(2-s)‖ := by
  have ha : |s.im| ≤ ‖star s+1‖ := by
    simpa using Complex.abs_im_le_norm (star s+1)
  have hb : |s.im| ≤ ‖2-s‖ := by
    simpa using Complex.abs_im_le_norm (2-s)
  have h := mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
  norm_num only [norm_mul,Complex.norm_ofNat]
  nlinarith

/-- A height bound for the complete source, independent of any zero condition. -/
theorem norm_reflectionDiskSource_le {s : ℂ} (ht : 1 ≤ |s.im|) :
    ‖reflectionDiskSource s‖ ≤ 115/(36*|s.im|) := by
  have hu : 0 < |s.im| := by linarith
  have hu2 : |s.im| ≤ |s.im|^2 := by nlinarith
  have hu4 : |s.im|^2 ≤ |s.im|^4 := by nlinarith [sq_nonneg (|s.im|^2-1)]
  have hC := hu4.trans (reflection_target_normSq_lower s)
  have hC0 : 0 < Complex.normSq (star s*(1-star s)) := lt_of_lt_of_le (sq_pos_of_pos hu) hC
  have hmean := reflection_target_mean_norm_lower s
  have ha : ‖(((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I)‖ ≤ 1/|s.im| := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
      abs_div,abs_of_pos hC0]
    calc |s.im|/Complex.normSq (star s*(1-star s)) ≤ |s.im|/(|s.im|^2) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hu) hC
         _ = 1/|s.im| := by field_simp
  have hb : ‖1/((12:ℂ)*(star s+1)*(2-s))‖ ≤ 1/(12*|s.im|) := by
    rw [norm_div,norm_one]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hL := norm_criticalFullLogResponse_le_inverse_height (abs_pos.mp hu)
  unfold reflectionDiskSource
  calc ‖criticalFullLogResponse s.im +
        (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
          1/(12*(star s+1)*(2-s)))‖ ≤
        ‖criticalFullLogResponse s.im‖+
        ‖(((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I)‖+
        ‖1/((12:ℂ)*(star s+1)*(2-s))‖ :=
          (norm_add_le _ _).trans (by
            simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_left (norm_sub_le
              (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I)
              (1/((12:ℂ)*(star s+1)*(2-s)))) ‖criticalFullLogResponse s.im‖)
       _ ≤ 19/(9*|s.im|)+1/|s.im|+1/(12*|s.im|) := by linarith
       _ = 115/(36*|s.im|) := by ring

/-- Strict inverse-height enclosure of the actual source. -/
theorem norm_reflectionDiskSource_lt {s : ℂ} (ht : 1 ≤ |s.im|) :
    ‖reflectionDiskSource s‖ < 4/|s.im| := by
  apply (norm_reflectionDiskSource_le ht).trans_lt
  have hu : 0 < |s.im| := by linarith
  apply (div_lt_iff₀ (by positivity : 0 < 36*|s.im|)).mpr
  field_simp
  norm_num

/-- In an outer quarter of the strip, the canonical cubic cost is at least 256. -/
theorem reflectionCubicHeightCost_outer_lower {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hd : 1/4 ≤ |s.re-1/2|) :
    256 ≤ reflectionCubicHeightCost (1/2-|s.re-1/2|) := by
  have he : 0 < 1/2-|s.re-1/2| := by
    have := abs_lt.mpr (show -(1/2:ℝ) < s.re-1/2 ∧ s.re-1/2 < 1/2 from
      ⟨by linarith,by linarith⟩)
    linarith
  have hep : 1/2-|s.re-1/2| ≤ 1/4 := by linarith
  have hp := pow_le_pow_left₀ he.le hep 4
  have hb : (256:ℝ) ≤ 1/(1/2-|s.re-1/2|)^4 := by
    apply (le_div_iff₀ (pow_pos he 4)).mpr
    norm_num at hp
    nlinarith
  unfold reflectionCubicHeightCost
  have h2 : 0 ≤ 1/(4*(1+(1/2-|s.re-1/2|))^4) := by positivity
  have h3 : 0 ≤ 1/(6*(1+(1/2-|s.re-1/2|))^3) := by positivity
  linarith

/-- Strict admission to the height disk, with explicit positive slack, for all outer-quarter sources. -/
theorem reflection_height_disk_admission {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hd : 1/4 ≤ |s.re-1/2|) (ht : 1 ≤ |s.im|) :
    ‖reflectionDiskSource s‖+4/|s.im| <
      (s.re-1/2)^2*reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|) := by
  have hu : 0 < |s.im| := by linarith
  have hδ : (1:ℝ)/16 ≤ (s.re-1/2)^2 := by nlinarith [sq_abs (s.re-1/2)]
  have hB := reflectionCubicHeightCost_outer_lower hs hs' hd
  have hprod : (16:ℝ) ≤ (s.re-1/2)^2*reflectionCubicHeightCost (1/2-|s.re-1/2|) := by
    nlinarith
  calc ‖reflectionDiskSource s‖+4/|s.im| < 4/|s.im|+4/|s.im| :=
        by
          have h := norm_reflectionDiskSource_lt ht
          linarith only [h]
       _ = 8/|s.im| := by ring
       _ ≤ (s.re-1/2)^2*reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|) := by
        apply (le_div_iff₀ (by positivity : 0 < 2*|s.im|)).mpr
        calc 8/|s.im| *(2*|s.im|) = 16 := by field_simp; norm_num
             _ ≤ _ := hprod

/-- The older disk also admits every outer-quarter source above an explicit height. -/
theorem reflection_fixed_disk_admission {s : ℂ}
    (hd : 1/4 ≤ |s.re-1/2|) (ht : 1536 ≤ |s.im|) :
    ‖reflectionDiskSource s‖+1/384 < (s.re-1/2)^2/12 := by
  have hδ : (1:ℝ)/16 ≤ (s.re-1/2)^2 := by nlinarith [sq_abs (s.re-1/2)]
  have hb : 4/|s.im| ≤ (1:ℝ)/384 := by
    apply (div_le_iff₀ (by linarith : 0 < |s.im|)).mpr
    linarith
  have hsource := norm_reflectionDiskSource_lt (show 1 ≤ |s.im| by linarith)
  linarith

/-- At arbitrarily large heights, actual nonzeros on the line `Re(s)=3/4` satisfy both disks strictly. -/
theorem exists_nonzero_reflection_disks_admitted (T : ℝ) :
    ∃ s : ℂ, s.re=3/4 ∧ T<s.im ∧ 1536<s.im ∧ riemannZeta s≠0 ∧
      ‖reflectionDiskSource s‖+1/384 < (s.re-1/2)^2/12 ∧
      ‖reflectionDiskSource s‖+4/|s.im| <
        (s.re-1/2)^2*reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|) := by
  let w : ℂ := (3/4:ℂ)+((max T 1536:ℝ):ℂ)*Complex.I
  have hwre : w.re=3/4 := by simp [w]
  have hwim : w.im=max T 1536 := by simp [w]
  have hpunct := RHTower.eventually_riemannZeta_ne_zero_nhdsNE
    (show 0<w.re by rw [hwre]; norm_num) (show w.re<1 by rw [hwre]; norm_num)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let v : ℂ := w+((r/2:ℝ):ℂ)*Complex.I
  have hvre : v.re=3/4 := by simp [v,hwre]
  have hvim : v.im=max T 1536+r/2 := by simp [v,hwim]
  have hvw : v-w=((r/2:ℝ):ℂ)*Complex.I := by dsimp [v]; ring
  have hz : riemannZeta v≠0 := by
    refine hsub ⟨?_,?_⟩
    · rw [Metric.mem_ball,Complex.dist_eq,hvw,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_I,mul_one,abs_of_pos (half_pos hr)]
      linarith
    · change v≠w
      intro h
      have hi := congrArg Complex.im h
      rw [hvim,hwim] at hi
      linarith
  have hT : T<v.im := by rw [hvim]; linarith [le_max_left T (1536:ℝ)]
  have hvheight : 1536<v.im := by rw [hvim]; linarith [le_max_right T (1536:ℝ)]
  have hd : 1/4 ≤ |v.re-1/2| := by rw [hvre]; norm_num
  have ht : 1536 ≤ |v.im| := hvheight.le.trans (le_abs_self _)
  refine ⟨v,hvre,hT,hvheight,hz,reflection_fixed_disk_admission hd ht,?_⟩
  exact reflection_height_disk_admission (by rw [hvre]; norm_num)
    (by rw [hvre]; norm_num) hd (by linarith)

end RHTower.DeletionMixedRefinement
