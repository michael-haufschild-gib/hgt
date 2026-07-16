import GaloisForLFunctions.HTGeometry.StretchedExponentialMinimizerGap
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter Finset Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

/-- The fixed-shift real-power defect attached to a finitely supported coefficient packet. -/
def polynomialPowerFiniteDifference (β : ℝ) (d : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  d.sum fun r a => a * (x + r) ^ β

/-- The coefficient of the first surviving moment in a real-power finite difference. -/
def polynomialPowerDifferenceCoefficient (β : ℝ) (d : ℕ →₀ ℝ) (j : ℕ) : ℝ :=
  stretchedMoment d j * (descPochhammer ℝ j).eval β / (j.factorial : ℝ)

private def scaledPowerShift (β : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  (1 + (r : ℝ) * t) ^ β

private def scaledPowerTaylor (β : ℝ) (j r : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    ((descPochhammer ℝ k).eval β * (r : ℝ) ^ k / (k.factorial : ℝ)) * t ^ k

private lemma contDiffOn_scaledPowerShift (β : ℝ) (j r : ℕ) :
    ContDiffOn ℝ j (scaledPowerShift β r) (Ici 0) := by
  intro t ht
  have hbase : 1 + (r : ℝ) * t ≠ 0 := by
    have : 0 ≤ (r : ℝ) * t := mul_nonneg (Nat.cast_nonneg r) ht
    linarith
  exact (Real.contDiffAt_rpow_const_of_ne hbase).comp t
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)) |>.contDiffWithinAt

private lemma iteratedDerivWithin_scaledPowerShift_zero
    (β : ℝ) (j r : ℕ) :
    iteratedDerivWithin j (scaledPowerShift β r) (Ici 0) 0 =
      (descPochhammer ℝ j).eval β * (r : ℝ) ^ j := by
  let f : ℝ → ℝ := fun u => (1 + u) ^ β
  have hf : ContDiffOn ℝ j f (Ici 0) := by
    intro u hu
    have hu0 : 0 ≤ u := hu
    have hbase : 1 + u ≠ 0 := by linarith
    exact (Real.contDiffAt_rpow_const_of_ne hbase).comp u
      (contDiffAt_const.add contDiffAt_id) |>.contDiffWithinAt
  have hmaps : MapsTo (fun t : ℝ => (r : ℝ) * t) (Ici 0) (Ici 0) := by
    intro t ht
    exact mul_nonneg (Nat.cast_nonneg r) (show 0 ≤ t from ht)
  have hscale := iteratedDerivWithin_comp_const_smul
    (s := Set.Ici (0 : ℝ)) (x := (0 : ℝ)) (n := j) (f := f)
    (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0) (uniqueDiffOn_Ici 0) hf (r : ℝ) hmaps
  have hfat : ContDiffAt ℝ j f 0 := by
    have hinner : ContDiffAt ℝ j (fun u : ℝ => 1 + u) 0 :=
      contDiffAt_const.add contDiffAt_id
    have hout : ContDiffAt ℝ j (fun x : ℝ => x ^ β) 1 :=
      Real.contDiffAt_rpow_const_of_ne (x := (1 : ℝ)) (p := β) (n := j)
        (by norm_num : (1 : ℝ) ≠ 0)
    have hcomp : ContDiffAt ℝ j
        ((fun x : ℝ => x ^ β) ∘ (fun u : ℝ => 1 + u)) 0 :=
      ContDiffAt.comp (g := fun x : ℝ => x ^ β) (f := fun u : ℝ => 1 + u)
        0 (by simpa using hout) hinner
    simpa [f, Function.comp_def] using hcomp
  have hwithin : iteratedDerivWithin j f (Ici 0) 0 = iteratedDeriv j f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hfat self_mem_Ici
  have hshift := congrFun (iteratedDeriv_comp_const_add j (fun u : ℝ => u ^ β) 1) 0
  have hrpow : iteratedDeriv j (fun u : ℝ => u ^ β) 1 =
      (descPochhammer ℝ j).eval β := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
    simp
  change iteratedDerivWithin j (fun t : ℝ => f ((r : ℝ) * t)) (Ici 0) 0 = _
  rw [hscale]
  simp only [mul_zero, smul_eq_mul]
  rw [hwithin]
  change (r : ℝ) ^ j * iteratedDeriv j f 0 = _
  rw [show iteratedDeriv j f 0 = iteratedDeriv j (fun u : ℝ => u ^ β) 1 by
    simpa [f, add_comm] using hshift, hrpow]
  ring

private lemma taylorWithinEval_scaledPowerShift_zero
    (β : ℝ) (j r : ℕ) (t : ℝ) :
    taylorWithinEval (scaledPowerShift β r) j (Ici 0) 0 t =
      scaledPowerTaylor β j r t := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_scaledPowerShift_zero]
  simp only [sub_zero, smul_eq_mul]
  ring

private lemma scaledPowerShift_sub_taylor_isLittleO
    (β : ℝ) (j r : ℕ) :
    (fun t => scaledPowerShift β r t - scaledPowerTaylor β j r t)
      =o[𝓝[Ici 0] 0] fun t => t ^ j := by
  have h := taylor_isLittleO (convex_Ici (0 : ℝ)) self_mem_Ici
    (contDiffOn_scaledPowerShift β j r)
  simpa only [taylorWithinEval_scaledPowerShift_zero, sub_zero] using h

private lemma finsupp_sum_scaledPowerTaylor_eq
    (β : ℝ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0) (t : ℝ) :
    d.sum (fun r a => a * scaledPowerTaylor β j r t) =
      polynomialPowerDifferenceCoefficient β d j * t ^ j := by
  classical
  rw [Finsupp.sum]
  simp_rw [scaledPowerTaylor, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hjterm :
      (∑ r ∈ d.support,
          d r * (((descPochhammer ℝ j).eval β * (r : ℝ) ^ j /
            (j.factorial : ℝ)) * t ^ j)) =
        polynomialPowerDifferenceCoefficient β d j * t ^ j := by
    rw [polynomialPowerDifferenceCoefficient, stretchedMoment, Finsupp.sum]
    calc
      (∑ r ∈ d.support,
          d r * (((descPochhammer ℝ j).eval β * (r : ℝ) ^ j /
            (j.factorial : ℝ)) * t ^ j)) =
          (((descPochhammer ℝ j).eval β / (j.factorial : ℝ)) * t ^ j) *
            ∑ r ∈ d.support, d r * (r : ℝ) ^ j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              ring
      _ = ((∑ r ∈ d.support, d r * (r : ℝ) ^ j) *
          (descPochhammer ℝ j).eval β / (j.factorial : ℝ)) * t ^ j := by ring
  rw [← hjterm]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    have hkle : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkl : k < j := lt_of_le_of_ne hkle hkj
    have hsum : (∑ r ∈ d.support, d r * (r : ℝ) ^ k) = 0 := by
      simpa only [stretchedMoment, Finsupp.sum] using hcancel k hkl
    calc
      (∑ r ∈ d.support,
          d r * (((descPochhammer ℝ k).eval β * (r : ℝ) ^ k /
            (k.factorial : ℝ)) * t ^ k)) =
          (((descPochhammer ℝ k).eval β / (k.factorial : ℝ)) * t ^ k) *
            ∑ r ∈ d.support, d r * (r : ℝ) ^ k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              ring
      _ = 0 := by rw [hsum, mul_zero]
  · simp

private lemma scaledPowerPacket_sub_leading_isLittleO
    (β : ℝ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0) :
    (fun t => d.sum (fun r a => a * scaledPowerShift β r t) -
        polynomialPowerDifferenceCoefficient β d j * t ^ j)
      =o[𝓝[Ici 0] 0] fun t => t ^ j := by
  classical
  have hs :
      (fun t => d.sum (fun r a =>
        a * (scaledPowerShift β r t - scaledPowerTaylor β j r t)))
        =o[𝓝[Ici 0] 0] fun t => t ^ j := by
    simp only [Finsupp.sum]
    exact IsLittleO.sum fun r hr =>
      (scaledPowerShift_sub_taylor_isLittleO β j r).const_mul_left (d r)
  refine hs.congr_left (fun t => ?_)
  rw [← finsupp_sum_scaledPowerTaylor_eq β d j hcancel t]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private lemma polynomialPowerFiniteDifference_eq_scaled
    (β : ℝ) (d : ℕ →₀ ℝ) {x : ℝ} (hx : 0 < x) :
    polynomialPowerFiniteDifference β d x =
      x ^ β * d.sum (fun r a => a * scaledPowerShift β r x⁻¹) := by
  rw [polynomialPowerFiniteDifference, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hone : x + (r : ℝ) = x * (1 + (r : ℝ) * x⁻¹) := by
    field_simp
  have hfactor : 0 ≤ 1 + (r : ℝ) * x⁻¹ := by positivity
  rw [hone, Real.mul_rpow hx.le hfactor]
  simp only [scaledPowerShift]
  ring

/-- A fixed finite-difference packet with first nonzero moment `j` has the exact real-power
asymptotic prescribed by the `j`-th falling factorial of the exponent. -/
theorem polynomialPowerFiniteDifference_isEquivalent
    {β : ℝ} (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0)
    (hpoch : (descPochhammer ℝ j).eval β ≠ 0) :
    polynomialPowerFiniteDifference β d ~[atTop]
      fun x => polynomialPowerDifferenceCoefficient β d j * x ^ (β - j) := by
  let c := polynomialPowerDifferenceCoefficient β d j
  have hc : c ≠ 0 := by
    dsimp [c, polynomialPowerDifferenceCoefficient]
    exact div_ne_zero (mul_ne_zero hmoment hpoch) (by positivity)
  have hlocal := scaledPowerPacket_sub_leading_isLittleO β d j hcancel
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[Ici 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact inv_nonneg.mpr hx.le
  have hcomp := hlocal.comp_tendsto hinv
  have hscaled :
      (fun x : ℝ => x ^ β *
          (d.sum (fun r a => a * scaledPowerShift β r x⁻¹) - c * x⁻¹ ^ j))
        =o[atTop] fun x => x ^ β * x⁻¹ ^ j :=
    (isBigO_refl (fun x : ℝ => x ^ β) atTop).mul_isLittleO hcomp
  have heqLeft : polynomialPowerFiniteDifference β d =ᶠ[atTop]
      fun x => c * x ^ (β - j) +
        x ^ β * (d.sum (fun r a => a * scaledPowerShift β r x⁻¹) - c * x⁻¹ ^ j) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [polynomialPowerFiniteDifference_eq_scaled β d hx]
    have hpow : x ^ β * x⁻¹ ^ j = x ^ (β - j) := by
      rw [inv_pow, ← Real.rpow_natCast, ← div_eq_mul_inv, ← Real.rpow_sub hx]
    rw [← hpow]
    ring
  have hright : (fun x : ℝ => x ^ β * x⁻¹ ^ j) =ᶠ[atTop]
      fun x => x ^ (β - j) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [inv_pow, ← Real.rpow_natCast, ← div_eq_mul_inv, ← Real.rpow_sub hx]
  have hrem :
      (fun x : ℝ => x ^ β *
          (d.sum (fun r a => a * scaledPowerShift β r x⁻¹) - c * x⁻¹ ^ j))
        =o[atTop] fun x => c * x ^ (β - j) := by
    exact (hscaled.congr' EventuallyEq.rfl hright).const_mul_right hc
  have hmain : (fun x : ℝ => c * x ^ (β - j)) ~[atTop]
      fun x => c * x ^ (β - j) := IsEquivalent.refl
  exact (hmain.add_isLittleO hrem).congr_left (heqLeft.mono fun x hx => hx.symm)

/-- Below the exponent, the falling-factorial coefficient cannot vanish. -/
theorem descPochhammer_eval_ne_zero_of_natCast_lt
    {β : ℝ} {j : ℕ} (hjβ : (j : ℝ) < β) :
    (descPochhammer ℝ j).eval β ≠ 0 := by
  rw [descPochhammer_eval_eq_prod_range]
  exact Finset.prod_ne_zero_iff.mpr fun k hk => by
    have hklt : k < j := Finset.mem_range.mp hk
    have hkβ : (k : ℝ) < β := (Nat.cast_lt.mpr hklt).trans hjβ
    exact sub_ne_zero.mpr (ne_of_gt hkβ)

/-- If the first surviving moment lies below `β`, the corresponding real-power defect dominates
the logarithm.  This is the analytic obstruction used by the recurrent Prouhet lock. -/
theorem log_isLittleO_abs_polynomialPowerFiniteDifference
    {β : ℝ} (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0)
    (hjβ : (j : ℝ) < β) :
    Real.log =o[atTop] fun x => |polynomialPowerFiniteDifference β d x| := by
  have hpoch := descPochhammer_eval_ne_zero_of_natCast_lt hjβ
  let c := polynomialPowerDifferenceCoefficient β d j
  have hc : c ≠ 0 := by
    dsimp [c, polynomialPowerDifferenceCoefficient]
    exact div_ne_zero (mul_ne_zero hmoment hpoch) (by positivity)
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d j hcancel hmoment hpoch
  have hlogpow := isLittleO_log_rpow_atTop (sub_pos.mpr hjβ)
  have hloglead : Real.log =o[atTop] fun x => c * x ^ (β - j) :=
    hlogpow.const_mul_right hc
  have hlogdiff := hloglead.trans_isEquivalent (by simpa [c] using hequiv.symm)
  simpa only [Real.norm_eq_abs] using hlogdiff.norm_right

end

end GaloisForLFunctions
