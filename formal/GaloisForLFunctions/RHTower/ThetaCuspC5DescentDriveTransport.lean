import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectSturmTransport
/-! Curvature and finite-interval transport of the actual positive C5 source drive
J = 2 c' c'' - c c'''. Differentiating twice cancels the mixed sixth-jet
term. Complete source-defect growth gives a strict Sturm subsolution and
a finite growth comparison for the projective-potential difference.
The full coupled C5 compensation numerator remains a separate obligation. -/

namespace RHTower.ThetaCuspDefect
noncomputable section

def sourceDescentDrive (x : ℝ) : ℝ :=
  2*thetaCuspLogCurvatureJet x*thetaCuspLogCurvatureJetTwo x-
    thetaCuspLogCurvature x*thetaCuspLogCurvatureJetThree x

def sourceDescentDriveSlope (x : ℝ) : ℝ :=
  2*thetaCuspLogCurvatureJetTwo x^2+
    thetaCuspLogCurvatureJet x*thetaCuspLogCurvatureJetThree x+
    thetaCuspLogCurvature x*iteratedDeriv 6 thetaCuspLogSource x

def sourceDescentDriveCurvature (x : ℝ) : ℝ :=
  5*thetaCuspLogCurvatureJetTwo x*thetaCuspLogCurvatureJetThree x+
    thetaCuspLogCurvature x*iteratedDeriv 7 thetaCuspLogSource x

theorem hasDerivAt_sourceDescentDrive (x : ℝ) :
    HasDerivAt sourceDescentDrive (sourceDescentDriveSlope x) x := by
  have h3 : HasDerivAt thetaCuspLogCurvatureJetThree (-iteratedDeriv 6 thetaCuspLogSource x) x :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).neg
  have hd := (((hasDerivAt_thetaCuspLogCurvatureJet x).mul
    (hasDerivAt_thetaCuspLogCurvatureJetTwo x)).const_mul 2).sub
    ((hasDerivAt_thetaCuspLogCurvature x).mul h3)
  convert! hd using 1
  · funext y
    dsimp only [sourceDescentDrive,Pi.mul_apply,Pi.sub_apply]
    ring
  · unfold sourceDescentDriveSlope
    ring

theorem hasDerivAt_sourceDescentDriveSlope (x : ℝ) :
    HasDerivAt sourceDescentDriveSlope (sourceDescentDriveCurvature x) x := by
  have h3 : HasDerivAt thetaCuspLogCurvatureJetThree (-iteratedDeriv 6 thetaCuspLogSource x) x :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).neg
  have hd := ((((hasDerivAt_thetaCuspLogCurvatureJetTwo x).pow 2).const_mul 2).add
    ((hasDerivAt_thetaCuspLogCurvatureJet x).mul h3)).add
    ((hasDerivAt_thetaCuspLogCurvature x).mul (hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x))
  convert! hd using 1
  unfold sourceDescentDriveCurvature
  ring

theorem sourceDescentDrive_pos {x : ℝ} (hx : 0 < x) : 0 < sourceDescentDrive x := by
  have hp := projectiveEnergy_pos hx
  have hm := mul_pos (thetaCuspLogCurvatureJet_pos_of_pos hx) (thetaCuspLogCurvatureJetTwo_pos_all x)
  unfold sourceDescentDrive thetaCuspCompletedCurvatureProjectiveEnergy at *
  linarith only [hp,hm]

theorem sourceDescentDrive_eq_defect (x : ℝ) :
    sourceDescentDrive x =
      thetaCuspLogCurvatureJet x*(4*thetaCuspLogCurvature x+2*curvatureDefect x)+
        thetaCuspLogCurvature x*sourceDefectJet x := by
  unfold sourceDescentDrive curvatureDefect sourceDefectJet thetaCuspLogCurvature
    thetaCuspLogCurvatureJet thetaCuspLogCurvatureJetTwo thetaCuspLogCurvatureJetThree
  ring

theorem sourceDescentDrive_curvature_reserve {x : ℝ} (hx : 0 < x) :
    sourceDescentDriveCurvature x < 16*sourceDescentDrive x+
      thetaCuspLogCurvature x*(factorCurvature (thetaCuspLikelihoodCoordinate x)-32)*sourceDefectJet x := by
  have hb := curvatureDefect_pos hx.le
  have hv := thetaCuspLogCurvatureJet_pos_of_pos hx
  have hc := thetaCuspLogCurvature_pos x
  have hH : 0 < sourceDefectJet x := source_defect_pos hx
  have hG : 0 < factorCurvature (thetaCuspLikelihoodCoordinate x)*sourceDefectJet x-
      (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x) :=
    sub_pos.mpr (sourceDefect_curvature_upper hx)
  have he : 16*sourceDescentDrive x+
      thetaCuspLogCurvature x*(factorCurvature (thetaCuspLikelihoodCoordinate x)-32)*sourceDefectJet x-
        sourceDescentDriveCurvature x =
      12*thetaCuspLogCurvatureJet x*curvatureDefect x+5*curvatureDefect x*sourceDefectJet x+
        thetaCuspLogCurvature x*(factorCurvature (thetaCuspLikelihoodCoordinate x)*sourceDefectJet x-
          (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)) := by
    unfold sourceDescentDrive sourceDescentDriveCurvature curvatureDefect sourceDefectJet
      thetaCuspLogCurvature thetaCuspLogCurvatureJet thetaCuspLogCurvatureJetTwo thetaCuspLogCurvatureJetThree
    ring
  apply sub_pos.mp
  rw [he]
  positivity

theorem sourceDescentDrive_curvature_lt {x : ℝ} (hx : 0 < x) :
    sourceDescentDriveCurvature x < 18*thetaCuspLogCurvature x*sourceDescentDrive x := by
  let c := thetaCuspLogCurvature x
  let v := thetaCuspLogCurvatureJet x
  let b := curvatureDefect x
  let H := sourceDefectJet x
  let β := factorCurvature (thetaCuspLikelihoodCoordinate x)
  have hc : 0 < c := thetaCuspLogCurvature_pos x
  have hv : 0 < v := thetaCuspLogCurvatureJet_pos_of_pos hx
  have hb : 0 < b := curvatureDefect_pos hx.le
  have hH : 0 < H := source_defect_pos hx
  have hc18 : 0 < 18*c-16 := by linarith [sourceCurvature_gt_eighteen hx.le]
  have hf := factorLogSlope_neg (thetaCuspLikelihoodCoordinate_pos hx.le)
  have hβ : 0 < 18*c+16-β := by
    have hr := sourceSeamReserve_pos hx.le
    dsimp only [c,β]
    linarith only [hr,hf]
  have he : 18*c*sourceDescentDrive x-
      (16*sourceDescentDrive x+c*(β-32)*H) =
      v*((18*c-16)*(4*c+2*b))+c*H*(18*c+16-β) := by
    rw [sourceDescentDrive_eq_defect]
    dsimp only [c,v,b,H,β]
    ring
  have hp : 0 < 18*c*sourceDescentDrive x-
      (16*sourceDescentDrive x+c*(β-32)*H) := by
    rw [he]
    positivity
  exact (sourceDescentDrive_curvature_reserve hx).trans (sub_pos.mp hp)

theorem iteratedDeriv_two_sourceDescentDrive (x : ℝ) :
    iteratedDeriv 2 sourceDescentDrive x = sourceDescentDriveCurvature x := by
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv sourceDescentDrive=sourceDescentDriveSlope :=
    funext (fun y => (hasDerivAt_sourceDescentDrive y).deriv)
  rw [he]
  exact (hasDerivAt_sourceDescentDriveSlope x).deriv

theorem sourceDescentDrive_sturm_subsolution {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 sourceDescentDrive x < 18*thetaCuspLogCurvature x*sourceDescentDrive x := by
  rw [iteratedDeriv_two_sourceDescentDrive]
  exact sourceDescentDrive_curvature_lt hx


open Set

def sourceDescentPotential (x : ℝ) : ℝ :=
  (3/2:ℝ)*thetaCuspLogCurvatureJet x^2-thetaCuspLogCurvature x*thetaCuspLogCurvatureJetTwo x

theorem hasDerivAt_sourceDescentPotential (x : ℝ) :
    HasDerivAt sourceDescentPotential (sourceDescentDrive x) x := by
  have hd := (((hasDerivAt_thetaCuspLogCurvatureJet x).pow 2).const_mul (3/2:ℝ)).sub
    ((hasDerivAt_thetaCuspLogCurvature x).mul (hasDerivAt_thetaCuspLogCurvatureJetTwo x))
  convert! hd using 1
  unfold sourceDescentDrive
  ring

theorem sourceDescentPotential_strictMonoOn : StrictMonoOn sourceDescentPotential (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _
    exact (hasDerivAt_sourceDescentPotential x).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(hasDerivAt_sourceDescentPotential x).deriv]
    exact sourceDescentDrive_pos hx0

def sourceDescentGap (u s : ℝ) : ℝ := sourceDescentPotential (u+s)-sourceDescentPotential (u-s)
def sourceDescentGapSlope (u s : ℝ) : ℝ := sourceDescentDrive (u+s)+sourceDescentDrive (u-s)
def sourceDescentGapCurvature (u s : ℝ) : ℝ := sourceDescentDriveSlope (u+s)-sourceDescentDriveSlope (u-s)

theorem hasDerivAt_sourceDescentGap (u s : ℝ) :
    HasDerivAt (sourceDescentGap u) (sourceDescentGapSlope u s) s := by
  have hd := ((hasDerivAt_sourceDescentPotential (u+s)).comp s ((hasDerivAt_id s).const_add u)).sub
    ((hasDerivAt_sourceDescentPotential (u-s)).comp s ((hasDerivAt_id s).const_sub u))
  convert! hd using 1
  unfold sourceDescentGapSlope
  ring

theorem hasDerivAt_sourceDescentGapSlope (u s : ℝ) :
    HasDerivAt (sourceDescentGapSlope u) (sourceDescentGapCurvature u s) s := by
  have hd := ((hasDerivAt_sourceDescentDrive (u+s)).comp s ((hasDerivAt_id s).const_add u)).add
    ((hasDerivAt_sourceDescentDrive (u-s)).comp s ((hasDerivAt_id s).const_sub u))
  convert! hd using 1
  unfold sourceDescentGapCurvature
  ring

theorem sourceDescentGap_pos {u s : ℝ} (hs : 0 < s) (hsu : s ≤ u) : 0 < sourceDescentGap u s := by
  exact sub_pos.mpr (sourceDescentPotential_strictMonoOn (sub_nonneg.mpr hsu)
    (show 0 ≤ u+s by linarith) (by linarith))

private theorem sourceDescentGap_curvature_comparison {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    {s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    sourceDescentGapCurvature u s < 18*thetaCuspLogCurvature (u+t)*sourceDescentGap u s := by
  let k := 18*thetaCuspLogCurvature (u+t)
  have hd (x : ℝ) : HasDerivAt (fun y => sourceDescentDriveSlope y-k*sourceDescentPotential y)
      (sourceDescentDriveCurvature x-k*sourceDescentDrive x) x :=
    (hasDerivAt_sourceDescentDriveSlope x).sub ((hasDerivAt_sourceDescentPotential x).const_mul k)
  have hm : StrictAntiOn (fun x => sourceDescentDriveSlope x-k*sourceDescentPotential x) (Icc (u-t) (u+t)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro x _
      exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (u-t) (u+t) := by simpa only [interior_Icc] using hx
      have hx0 : 0 < x := by linarith [hx'.1]
      have hc := sourceCurvature_strictMonoOn.monotoneOn hx0.le (show 0 ≤ u+t by linarith) hx'.2.le
      have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤18))
        (sourceDescentDrive_pos hx0).le
      have hi := (sourceDescentDrive_curvature_lt hx0).trans_le hb
      rw [(hd x).deriv]
      dsimp only [k]
      exact sub_neg.mpr hi
  have hm' := hm (show u-s ∈ Icc (u-t) (u+t) by constructor <;> linarith)
    (show u+s ∈ Icc (u-t) (u+t) by constructor <;> linarith) (by linarith : u-s<u+s)
  dsimp only [k] at hm'
  unfold sourceDescentGapCurvature sourceDescentGap
  linarith only [hm']

private def radialComparison (k s : ℝ) : ℝ := s*Real.exp (k*s^2/6)
private def radialComparisonSlope (k s : ℝ) : ℝ := Real.exp (k*s^2/6)*(1+k*s^2/3)
private def radialComparisonCurvature (k s : ℝ) : ℝ := Real.exp (k*s^2/6)*(k*s+k^2*s^3/9)

private theorem hasDerivAt_radialComparison (k s : ℝ) :
    HasDerivAt (radialComparison k) (radialComparisonSlope k s) s := by
  have he := ((((hasDerivAt_id s).pow 2).const_mul k).div_const 6).exp
  convert! (hasDerivAt_id s).mul he using 1
  unfold radialComparisonSlope
  simp only [Pi.pow_apply,id_eq]
  ring

private theorem hasDerivAt_radialComparisonSlope (k s : ℝ) :
    HasDerivAt (radialComparisonSlope k) (radialComparisonCurvature k s) s := by
  have he := ((((hasDerivAt_id s).pow 2).const_mul k).div_const 6).exp
  have hg := ((((hasDerivAt_id s).pow 2).const_mul k).div_const 3).const_add 1
  convert! he.mul hg using 1
  unfold radialComparisonCurvature
  simp only [Pi.pow_apply,id_eq]
  ring

private def sourceDescentGapFlux (u k s : ℝ) : ℝ :=
  sourceDescentGapSlope u s*radialComparison k s-sourceDescentGap u s*radialComparisonSlope k s

private theorem hasDerivAt_sourceDescentGapFlux (u k s : ℝ) :
    HasDerivAt (sourceDescentGapFlux u k)
      (sourceDescentGapCurvature u s*radialComparison k s-
        sourceDescentGap u s*radialComparisonCurvature k s) s := by
  have hd := ((hasDerivAt_sourceDescentGapSlope u s).mul (hasDerivAt_radialComparison k s)).sub
    ((hasDerivAt_sourceDescentGap u s).mul (hasDerivAt_radialComparisonSlope k s))
  convert! hd using 1
  ring

theorem sourceDescentGap_finite_growth {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    t*(sourceDescentDrive (u+t)+sourceDescentDrive (u-t)) <
      (1+6*thetaCuspLogCurvature (u+t)*t^2)*
        (sourceDescentPotential (u+t)-sourceDescentPotential (u-t)) := by
  let k := 18*thetaCuspLogCurvature (u+t)
  have hk : 0 < k := mul_pos (by norm_num) (thetaCuspLogCurvature_pos (u+t))
  have hm : StrictAntiOn (sourceDescentGapFlux u k) (Icc 0 t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro s _
      exact (hasDerivAt_sourceDescentGapFlux u k s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      have hs0 : 0 < s := hs'.1
      have hY := sourceDescentGap_pos hs'.1 (hs'.2.le.trans htu)
      have hpsi : 0 < radialComparison k s := mul_pos hs'.1 (Real.exp_pos _)
      have hpsicurv : k*radialComparison k s ≤ radialComparisonCurvature k s := by
        have hp : 0 ≤ Real.exp (k*s^2/6)*(k^2*s^3/9) := by positivity
        unfold radialComparison radialComparisonCurvature
        nlinarith only [hp]
      have hYcurv := sourceDescentGap_curvature_comparison ht htu hs'.1 hs'.2.le
      have h1 := mul_lt_mul_of_pos_right hYcurv hpsi
      have h2 := mul_le_mul_of_nonneg_left hpsicurv hY.le
      rw [(hasDerivAt_sourceDescentGapFlux u k s).deriv]
      dsimp only [k] at h1 h2 ⊢
      nlinarith only [h1,h2]
  have hW := hm (show (0:ℝ) ∈ Icc 0 t by constructor <;> linarith)
    (show t ∈ Icc (0:ℝ) t by constructor <;> linarith) ht
  have h0 : sourceDescentGapFlux u k 0=0 := by
    simp [sourceDescentGapFlux,sourceDescentGap,radialComparison]
  rw [h0] at hW
  have he : sourceDescentGapFlux u k t =
      Real.exp (k*t^2/6)*(t*sourceDescentGapSlope u t-(1+k*t^2/3)*sourceDescentGap u t) := by
    unfold sourceDescentGapFlux radialComparison radialComparisonSlope
    ring
  rw [he] at hW
  have hn : t*sourceDescentGapSlope u t-(1+k*t^2/3)*sourceDescentGap u t < 0 := by
    by_contra h
    exact (not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt h))) hW
  dsimp only [sourceDescentGapSlope,sourceDescentGap,k] at hn
  nlinarith only [hn]


end
end RHTower.ThetaCuspDefect
