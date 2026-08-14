import GaloisForLFunctions.RHTower.BarnesMellinPowIntegrand
import GaloisForLFunctions.RHTower.BarnesMellinResidues

/-!
# Residues of the weighted Mellin integrand

The entire factor `(-w)^m` is analytic at every pole, so it multiplies each residue by its value
there: the residue of `F_m` at a pole `p` is `(-p)^m` times the residue of `F`.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- The polynomial weight is entire. -/
theorem analyticAt_neg_pow (m : ℕ) (p : ℂ) : AnalyticAt ℂ (fun w : ℂ => (-w) ^ m) p :=
  (analyticAt_id.neg).pow m

/-- **The weighted integrand has a simple pole at every nonnegative integer.** -/
theorem barnesIntegrandPow_simplePole_at_nat {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ) (k : ℕ) :
    (fun w : ℂ => barnesIntegrandPow s x m w
        - ((-(k : ℂ)) ^ m * (((x : ℝ) : ℂ) ^ (-(k : ℂ))
            * riemannZeta (-(s : ℂ) * (k : ℂ))) * (-(-1) ^ k))
          / (w - (k : ℂ)))
      =O[nhdsWithin ((k : ℂ)) {((k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  have hζ : -(s : ℂ) * (k : ℂ) ≠ 1 := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re] at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hre]
  have hg : AnalyticAt ℂ (fun w : ℂ =>
      (-w) ^ m * (((x : ℝ) : ℂ) ^ (-w) * riemannZeta (-(s : ℂ) * w))) (k : ℂ) :=
    (analyticAt_neg_pow m _).mul
      ((analyticAt_const_cpow_neg hx _).mul (analyticAt_zetaComp hζ))
  have hh : (fun w : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      - (-(-1) ^ k) / (w - (k : ℂ)))
      =O[nhdsWithin ((k : ℂ)) {((k : ℂ))}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
    have hbase := GaloisForLFunctions.HTGeometry.isBigO_inv_sin_sub_inv_at_nat k
    refine hbase.neg_left.congr' ?_ Filter.EventuallyEq.rfl
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [div_eq_mul_inv]
    ring
  have hmain := GaloisForLFunctions.HTGeometry.isBigO_analytic_mul_simplePole hg hh
  refine hmain.congr' (Filter.Eventually.of_forall fun w => ?_) Filter.EventuallyEq.rfl
  simp only [barnesIntegrandPow, barnesIntegrand]
  ring

/-- **The weighted integrand has a simple pole at the pullback of the zeta pole.** -/
theorem barnesIntegrandPow_simplePole_at_zetaPole {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    {p : ℂ} (hp : -(s : ℂ) * p = 1) (hsin : Complex.sin ((Real.pi : ℂ) * p) ≠ 0) :
    (fun w : ℂ => barnesIntegrandPow s x m w
        - ((-p) ^ m * (((x : ℝ) : ℂ) ^ (-p)
            * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * p)))
            * (-(1 / (s : ℂ)))) / (w - p))
      =O[nhdsWithin p {p}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hmap : Filter.Tendsto (fun w : ℂ => -(s : ℂ) * w)
      (nhdsWithin p {p}ᶜ) (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Filter.Tendsto (fun w : ℂ => -(s : ℂ) * w) (nhds p) (nhds (-(s : ℂ) * p)) :=
        ((continuous_const.mul continuous_id)).tendsto _
      rw [hp] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hwne : w ≠ p := hw
      intro hcon
      simp only [Set.mem_singleton_iff] at hcon
      refine hwne (mul_left_cancel₀ (neg_ne_zero.mpr hsne) ?_)
      rw [hcon, hp]
  have hbase : (fun z : ℂ => riemannZeta z - 1 / (z - 1))
      =O[nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ] (fun _ : ℂ => (1 : ℂ)) :=
    tendsto_riemannZeta_sub_one_div.isBigO_one ℂ
  have hcomp := hbase.comp_tendsto hmap
  have hh : (fun w : ℂ => riemannZeta (-(s : ℂ) * w) - (-(1 / (s : ℂ))) / (w - p))
      =O[nhdsWithin p {p}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
    refine hcomp.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w - p ≠ 0 := sub_ne_zero.mpr hw
    have hden : -(s : ℂ) * w - 1 = -(s : ℂ) * (w - p) := by rw [mul_sub, hp]
    simp only [Function.comp_apply]
    rw [hden]
    congr 1
    field_simp
  have hg : AnalyticAt ℂ (fun w : ℂ => (-w) ^ m * (((x : ℝ) : ℂ) ^ (-w)
      * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)))) p :=
    (analyticAt_neg_pow m _).mul
      ((analyticAt_const_cpow_neg hx _).mul (analyticAt_reflectionKernel hsin))
  have hmain := GaloisForLFunctions.HTGeometry.isBigO_analytic_mul_simplePole hg hh
  refine hmain.congr' (Filter.Eventually.of_forall fun w => ?_) Filter.EventuallyEq.rfl
  simp only [barnesIntegrandPow, barnesIntegrand]
  ring

end

end RHTower
