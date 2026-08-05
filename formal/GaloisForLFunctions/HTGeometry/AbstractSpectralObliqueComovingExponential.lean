import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExponential

/-!
# Oblique co-moving exponential phase transition

The unit-slope cone `|u| ≤ a` is not the natural boundary of massive absorption.  Introduce an
aperture velocity `v>0`.  If

`v|u| ≤ a - 1/2` and `1 < 4σv`,

then the exact positive rate

`κ(σ,v) = (σ - 1/(4v))/2`

controls both aperture and spectral height.  The proof has two universal geometric inputs.  For an
original point `R+iJ` and its mass image `M+iK`,

`(a-1/2)^2 + R^2 ≤ M^2`

and charge conservation gives

`4v|u||K| ≤ M`.

The second estimate spends only one quarter of the velocity-weighted massive height against
vertical growth.  The phase boundary `4σv=1` is therefore intrinsic, rather than a constant loss
from the earlier cone proof.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- Decay rate in the open oblique mass cone. -/
def obliqueComovingExponentialRate (σ v : ℝ) : ℝ :=
  (σ - 1 / (4 * v)) / 2

theorem obliqueComovingExponentialRate_pos
    {σ v : ℝ} (hv : 0 < v) (hphase : 1 < 4 * σ * v) :
    0 < obliqueComovingExponentialRate σ v := by
  unfold obliqueComovingExponentialRate
  have hv4 : 0 < 4 * v := by positivity
  have hfrac : 1 / (4 * v) < σ := by
    rw [div_lt_iff₀ hv4]
    nlinarith
  linarith

/-- The mass root dominates the Euclidean joint scale of spectral height and threshold-corrected
aperture. -/
theorem sq_sub_half_add_sq_re_le_sq_mass_re
    {a : ℝ} (ha : 2 ≤ a) (i : ι) :
    (a - 1 / 2) ^ 2 + (F.pt i).re ^ 2 ≤
      ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re ^ 2 := by
  let haHalf : 1 / 2 ≤ a := by linarith
  have hJ := F.abs_im_lt i
  have hJ2 : (F.pt i).im ^ 2 < 1 / 4 := by
    nlinarith [sq_abs (F.pt i).im, abs_nonneg ((F.pt i).im)]
  have hM2raw := re_le_sq_csqrtRe (F.massArg_re_pos haHalf i)
  rw [F.massArg_re] at hM2raw
  have hM2 :
      (F.pt i).re ^ 2 - (F.pt i).im ^ 2 + a ^ 2 ≤
        ((F.mass haHalf).pt i).re ^ 2 := by
    simpa only [F.mass_pt, csqrt_re] using hM2raw
  have hfinal :
      (a - 1 / 2) ^ 2 + (F.pt i).re ^ 2 ≤
        ((F.mass haHalf).pt i).re ^ 2 := by
    nlinarith
  simpa only using hfinal

/-- Linear form of the joint Euclidean lower bound. -/
theorem sub_half_add_re_le_two_mul_mass_re
    {a : ℝ} (ha : 2 ≤ a) (i : ι) :
    a - 1 / 2 + (F.pt i).re ≤
      2 * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (F.pt i).re
  let M : ℝ := ((F.mass haHalf).pt i).re
  have hA : 0 ≤ A := by dsimp only [A]; linarith
  have hR : 0 < R := F.re_pos i
  have hM : 0 ≤ M := by
    dsimp only [M]
    rw [F.mass_pt, csqrt_re]
    exact csqrtRe_nonneg (F.massArg a i)
  have hsq : A ^ 2 + R ^ 2 ≤ M ^ 2 := by
    dsimp only [A, R, M]
    simpa only using F.sq_sub_half_add_sq_re_le_sq_mass_re ha i
  have hfinal : A + R ≤ 2 * M := by
    nlinarith [sq_nonneg (A - R)]
  simpa only [A, R, M] using hfinal

/-- **Velocity-weighted transverse absorption.**  This is the exact inequality producing the
phase boundary `4σv=1`. -/
theorem four_mul_velocity_mul_abs_height_mul_abs_mass_im_le_mass_re
    {a v u : ℝ} (ha : 2 ≤ a) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (i : ι) :
    4 * v * |u| *
        |((F.mass (show 1 / 2 ≤ a by linarith)).pt i).im| ≤
      ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (F.pt i).re
  let J : ℝ := (F.pt i).im
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  have hA : 0 ≤ A := by dsimp only [A]; linarith
  have hR : 0 < R := F.re_pos i
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [F.mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg haHalf i
    linarith
  have hsq : A ^ 2 + R ^ 2 ≤ M ^ 2 := by
    dsimp only [A, R, M]
    simpa only using F.sq_sub_half_add_sq_re_le_sq_mass_re ha i
  have hprod := F.re_mul_im_mass haHalf i
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    simpa only [M, K, R, J, abs_mul, abs_of_pos hM, abs_of_pos hR] using habs
  have hJ : |J| ≤ 1 / 2 := (F.abs_im_lt i).le
  have hMK : M * |K| ≤ R / 2 := by
    rw [hprodAbs]
    nlinarith [mul_le_mul_of_nonneg_left hJ hR.le]
  have hscale :
      (4 * v * |u|) * (M * |K|) ≤ (4 * v * |u|) * (R / 2) :=
    mul_le_mul_of_nonneg_left hMK (by positivity)
  have hcone' : v * |u| ≤ A := by simpa only [A] using hcone
  have hconeR : 2 * (v * |u|) * R ≤ 2 * A * R := by
    have h := mul_le_mul_of_nonneg_right hcone' (show 0 ≤ 2 * R by positivity)
    nlinarith
  have hamgm : 2 * A * R ≤ A ^ 2 + R ^ 2 := by
    nlinarith [sq_nonneg (A - R)]
  have hmul : M * (4 * v * |u| * |K|) ≤ M * M := by
    nlinarith
  have hfinal : 4 * v * |u| * |K| ≤ M :=
    le_of_mul_le_mul_left hmul hM
  simpa only [K, M] using hfinal

/-- Pointwise exponential estimate in the open oblique mass cone. -/
theorem norm_mass_term_le_oblique_comoving_exponential
    {a σ v u : ℝ} (ha : 2 ≤ a) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2)
    (hphase : 1 < 4 * σ * v) (i : ι) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ ≤
      Real.exp (-(obliqueComovingExponentialRate σ v) * (a - 1 / 2)) *
        F.weight (obliqueComovingExponentialRate σ v) i := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let κ : ℝ := obliqueComovingExponentialRate σ v
  let A : ℝ := a - 1 / 2
  let R : ℝ := (F.pt i).re
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  have hκ : 0 < κ := obliqueComovingExponentialRate_pos hv hphase
  have hjoint : A + R ≤ 2 * M := by
    dsimp only [A, R, M]
    simpa only using F.sub_half_add_re_le_two_mul_mass_re ha i
  have htrans : 4 * v * |u| * |K| ≤ M := by
    dsimp only [K, M]
    simpa only using
      F.four_mul_velocity_mul_abs_height_mul_abs_mass_im_le_mass_re ha hv hcone i
  have hv4 : 0 < 4 * v := by positivity
  have huK : u * K ≤ M / (4 * v) := by
    calc
      u * K ≤ |u * K| := le_abs_self _
      _ = |u| * |K| := abs_mul _ _
      _ ≤ M / (4 * v) := by
        rw [le_div_iff₀ hv4]
        nlinarith
  have hdelta : 0 < σ - 1 / (4 * v) := by
    have hfrac : 1 / (4 * v) < σ := by
      rw [div_lt_iff₀ hv4]
      nlinarith
    linarith
  have hdecay : κ * (A + R) ≤ (σ - 1 / (4 * v)) * M := by
    dsimp only [κ, obliqueComovingExponentialRate]
    have hscale := mul_le_mul_of_nonneg_left hjoint
      (show 0 ≤ (σ - 1 / (4 * v)) / 2 by linarith)
    nlinarith
  have hfirst : -σ * M + u * K ≤ -(σ - 1 / (4 * v)) * M := by
    calc
      -σ * M + u * K ≤ -σ * M + M / (4 * v) := by
        simpa [add_comm] using add_le_add_left huK (-σ * M)
      _ = -(σ - 1 / (4 * v)) * M := by ring
  have hsecond : -(σ - 1 / (4 * v)) * M ≤ -κ * (A + R) := by
    linarith
  have hexponent : -σ * M + u * K ≤ -κ * A - κ * R := by
    calc
      -σ * M + u * K ≤ -(σ - 1 / (4 * v)) * M := hfirst
      _ ≤ -κ * (A + R) := hsecond
      _ = -κ * A - κ * R := by ring
  rw [(F.mass haHalf).norm_term, weight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  dsimp only [M, K, A, R] at hexponent
  linarith

/-- **Universal oblique co-moving extinction.**  It applies on every positive real-time line once
the aperture velocity lies in the open chamber `4σv>1`. -/
theorem norm_mass_traceC_le_oblique_comoving_exponential
    {a σ v u : ℝ} (ha : 2 ≤ a) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hσ : 0 < σ)
    (hphase : 1 < 4 * σ * v) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(obliqueComovingExponentialRate σ v) * (a - 1 / 2)) *
        F.traceReal (obliqueComovingExponentialRate σ v) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let κ : ℝ := obliqueComovingExponentialRate σ v
  have hκ : 0 < κ := obliqueComovingExponentialRate_pos hv hphase
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hσ
  refine le_trans
    (norm_tsum_le_tsum_norm ((F.mass haHalf).summable_norm_term hτ)) ?_
  rw [traceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun i => by
      simpa only [κ] using
        F.norm_mass_term_le_oblique_comoving_exponential ha hv hcone hphase i)
    ((F.mass haHalf).summable_norm_term hτ)
    ((F.summable_weight hκ).mul_left _)

end AbstractSpectralFamily

end


end HTGeometry
