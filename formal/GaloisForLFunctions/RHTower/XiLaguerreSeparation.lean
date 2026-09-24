import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Quantitative separation of an off-line pair under the first Laguerre inequality

`two_div_sq_le_of_laguerre_nonneg` says that wherever the first Laguerre inequality holds at the
ordinate `γ` of a conjugate pair of centred zeros `γ ∓ δ i`, the remaining divisor copies must
supply at least `2/δ²` to the inverse-square sum at `γ`.  That sum was left unestimated.

The estimate splits it.  A copy whose ordinate is further than `1` from `γ` contributes at most
twice its Lorentzian mass term, so the far part is at most `2·lorentzMass γ`.  A copy whose
ordinate is within `1` of `γ` contributes at most `d⁻²`, where `d` is any lower bound for the
distance from `γ` to the other copies' centred spectral points, and there are at most
`#{q : |Im ρ_q − γ| ≤ 1}` of them.  Both are `O(log(|γ| + 4))`, so

`2/δ² ≤ 16 (C + log(|γ| + 4)) (1 + d⁻²)`.

An off-line zero therefore cannot be closer to the critical line than the local zero separation
divided by the square root of the local zero density — wherever the first Laguerre inequality
holds.  Proving that inequality unconditionally is thus at least as hard as such a zero-free
neighbourhood of the critical line.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private theorem sep_spectral_re (q : XiZeroCopy) :
    (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint, Complex.mul_re]

/-- The inverse-square atoms with the pair's two copies removed. -/
private def sepTerm (γ : ℝ) (q₁ q₂ q : XiZeroCopy) : ℂ :=
  if q = q₁ ∨ q = q₂ then 0 else (((γ : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹

private theorem summable_sepTerm {γ : ℝ} (hγ : XiC (γ : ℂ) ≠ 0) (q₁ q₂ : XiZeroCopy) :
    Summable (sepTerm γ q₁ q₂) := by
  classical
  refine (summable_inv_sq_sub_xiSpectralPoint hγ).congr_cofinite ?_
  have hfin : ({q₁, q₂} : Set XiZeroCopy).Finite := (Set.finite_singleton q₂).insert q₁
  filter_upwards [hfin.compl_mem_cofinite] with q hq
  have h1 : q ≠ q₁ := fun h => hq (by simp [h])
  have h2 : q ≠ q₂ := fun h => hq (by simp [h])
  simp [sepTerm, h1, h2]

private theorem normSq_sub_spectral (γ : ℝ) (q : XiZeroCopy) :
    ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ)
      = (γ - (q.1 : ℂ).im) ^ (2 : ℕ) + (xiSpectralPoint q).im ^ (2 : ℕ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_sub,
    sep_spectral_re]
  ring

/-- The termwise bound: far copies are paid for by the Lorentzian mass, near copies by the
separation `d`. -/
private theorem re_sepTerm_le {γ d : ℝ} (hd : 0 < d) {q₁ q₂ : XiZeroCopy}
    (hsep : ∀ q : XiZeroCopy, q ≠ q₁ → q ≠ q₂ → d ≤ ‖(γ : ℂ) - xiSpectralPoint q‖)
    (F : Finset XiZeroCopy) (hF : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 → q ∈ F)
    (q : XiZeroCopy) :
    (sepTerm γ q₁ q₂ q).re
      ≤ 2 * lorentzMassTerm γ q + (if q ∈ F then 1 / d ^ (2 : ℕ) else 0) := by
  classical
  have hmass := lorentzMassTerm_nonneg γ q
  have hite : (0 : ℝ) ≤ (if q ∈ F then 1 / d ^ (2 : ℕ) else 0) := by
    split_ifs with h
    · positivity
    · exact le_rfl
  by_cases hq12 : q = q₁ ∨ q = q₂
  · rw [sepTerm, if_pos hq12]
    simp only [Complex.zero_re]
    linarith
  · have hne1 : q ≠ q₁ := fun h => hq12 (Or.inl h)
    have hne2 : q ≠ q₂ := fun h => hq12 (Or.inr h)
    have hbase : (sepTerm γ q₁ q₂ q).re ≤ 1 / ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) := by
      rw [sepTerm, if_neg hq12]
      calc (((((γ : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹)).re
          ≤ ‖(((γ : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹‖ := Complex.re_le_norm _
        _ = 1 / ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) := by
            rw [norm_inv, norm_pow, one_div]
    by_cases hnear : |(q.1 : ℂ).im - γ| ≤ 1
    · have hmem : q ∈ F := hF q hnear
      have hdle : d ≤ ‖(γ : ℂ) - xiSpectralPoint q‖ := hsep q hne1 hne2
      have hstep : 1 / ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) ≤ 1 / d ^ (2 : ℕ) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [hdle, hd]
      rw [if_pos hmem]
      linarith
    · have hfar : 1 < |(q.1 : ℂ).im - γ| := not_le.mp hnear
      have hsq : (1 : ℝ) < (γ - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have hid : |(q.1 : ℂ).im - γ| ^ (2 : ℕ) = (γ - (q.1 : ℂ).im) ^ (2 : ℕ) := by
          rw [sq_abs]; ring
        nlinarith [hfar, abs_nonneg ((q.1 : ℂ).im - γ), hid]
      have hnormsq := normSq_sub_spectral γ q
      have hge : (γ - (q.1 : ℂ).im) ^ (2 : ℕ) ≤ ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) := by
        rw [hnormsq]
        nlinarith [sq_nonneg ((xiSpectralPoint q).im)]
      have hpos : (0 : ℝ) < ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) := by linarith
      have hmassval : lorentzMassTerm γ q = 1 / (1 + (γ - (q.1 : ℂ).im) ^ (2 : ℕ)) := rfl
      have hden : (0 : ℝ) < 1 + (γ - (q.1 : ℂ).im) ^ (2 : ℕ) := by positivity
      have hstep : 1 / ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ) ≤ 2 * lorentzMassTerm γ q := by
        rw [hmassval, mul_one_div, ← sub_nonneg,
          div_sub_div _ _ (ne_of_gt hden) (ne_of_gt hpos)]
        refine div_nonneg ?_ (by positivity)
        nlinarith [hsq, hge]
      have hite0 : (0 : ℝ) ≤ (if q ∈ F then 1 / d ^ (2 : ℕ) else 0) := hite
      linarith

/-- **Quantitative separation.**  Wherever the first Laguerre inequality holds at the ordinate of a
conjugate pair of centred zeros `γ ∓ δ i`, the pair's distance `|δ|` to the critical line is
controlled by the local zero density and the separation `d` of the remaining copies. -/
theorem laguerre_offLine_separation {γ δ d : ℝ} (hδ : δ ≠ 0) (hd : 0 < d)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (hγ : XiC (γ : ℂ) ≠ 0)
    (hsep : ∀ q : XiZeroCopy, q ≠ q₁ → q ≠ q₂ → d ≤ ‖(γ : ℂ) - xiSpectralPoint q‖)
    (hL : 0 ≤ (deriv XiC γ ^ (2 : ℕ) - XiC γ * deriv (deriv XiC) γ).re) :
    2 / δ ^ (2 : ℕ)
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|γ| + 4)) * (1 + 1 / d ^ (2 : ℕ)) := by
  classical
  have hcorpus := two_div_sq_le_of_laguerre_nonneg hδ h12 h1 h2 hγ hL
  set F : Finset XiZeroCopy := (finite_xiOrdinateWindow 1 γ).toFinset with hFdef
  have hF : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 → q ∈ F := by
    intro q hq
    rw [hFdef, Set.Finite.mem_toFinset]
    exact hq
  have hsum := summable_sepTerm hγ q₁ q₂
  have hsumre : Summable (fun q : XiZeroCopy => (sepTerm γ q₁ q₂ q).re) :=
    hsum.mapL Complex.reCLM
  have hmajor : Summable (fun q : XiZeroCopy =>
      2 * lorentzMassTerm γ q + (if q ∈ F then 1 / d ^ (2 : ℕ) else 0)) := by
    refine ((summable_lorentzMassTerm γ).mul_left 2).add ?_
    refine summable_of_ne_finset_zero (s := F) ?_
    intro q hq
    rw [if_neg hq]
  have hle : (∑' q : XiZeroCopy, (sepTerm γ q₁ q₂ q).re)
      ≤ ∑' q : XiZeroCopy,
          (2 * lorentzMassTerm γ q + (if q ∈ F then 1 / d ^ (2 : ℕ) else 0)) :=
    Summable.tsum_le_tsum (fun q => re_sepTerm_le hd hsep F hF q) hsumre hmajor
  have hrhs : (∑' q : XiZeroCopy,
      (2 * lorentzMassTerm γ q + (if q ∈ F then 1 / d ^ (2 : ℕ) else 0)))
      = 2 * lorentzMass γ + (F.card : ℝ) * (1 / d ^ (2 : ℕ)) := by
    rw [Summable.tsum_add ((summable_lorentzMassTerm γ).mul_left 2)
      (summable_of_ne_finset_zero (s := F) (fun q hq => if_neg hq))]
    congr 1
    · rw [tsum_mul_left]
      rfl
    · rw [tsum_eq_sum (s := F) (fun q hq => if_neg hq), Finset.sum_congr rfl
        (fun q hq => if_pos hq), Finset.sum_const, nsmul_eq_mul]
  have hreeq : (∑' q : XiZeroCopy, sepTerm γ q₁ q₂ q).re
      = ∑' q : XiZeroCopy, (sepTerm γ q₁ q₂ q).re := Complex.re_tsum hsum
  have hcorpus' : 2 / δ ^ (2 : ℕ) ≤ ∑' q : XiZeroCopy, (sepTerm γ q₁ q₂ q).re := by
    rw [← hreeq]
    exact hcorpus
  have hcount : (F.card : ℝ) ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|γ| + 4)) := by
    have hnc : ((xiOrdinateWindow 1 γ).ncard : ℝ) = (F.card : ℝ) := by
      rw [hFdef, Set.ncard_eq_toFinset_card _ (finite_xiOrdinateWindow 1 γ)]
    rw [← hnc]
    exact ncard_xiOrdinateWindow_one_le_log γ
  have hmassbd := lorentzMass_le_log γ
  have hdpos : (0 : ℝ) < 1 / d ^ (2 : ℕ) := by positivity
  rw [hrhs] at hle
  nlinarith [hcorpus', hle, hcount, hmassbd, hdpos]

/-- The Lorentzian mass is strictly positive: the divisor is nonempty and every term is. -/
theorem lorentzMass_pos (t : ℝ) : 0 < lorentzMass t := by
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  have hterm : ∀ q : XiZeroCopy, 0 < lorentzMassTerm t q := by
    intro q
    unfold lorentzMassTerm
    positivity
  exact (summable_lorentzMassTerm t).tsum_pos (fun q => (hterm q).le) q₀ (hterm q₀)

/-- The log-scale appearing in the mass bound is strictly positive. -/
theorem xiLineTwoLogDerivConstant_add_log_pos (t : ℝ) :
    0 < xiLineTwoLogDerivConstant + Real.log (|t| + 4) := by
  have h1 := lorentzMass_pos t
  have h2 := lorentzMass_le_log t
  linarith

/-- **No isolated off-line pair near the critical line.**  Wherever the first Laguerre inequality
holds at the ordinate `γ` of a conjugate pair `γ ∓ δ i` whose distance to the critical line is below
the local scale `(16 (C + log(|γ| + 4)))^{-1/2}`, some further divisor copy lies within
`√(16 (C + log(|γ| + 4))) · |δ|` of `γ`. -/
theorem laguerre_offLine_has_companion {γ δ : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (hγ : XiC (γ : ℂ) ≠ 0)
    (hL : 0 ≤ (deriv XiC γ ^ (2 : ℕ) - XiC γ * deriv (deriv XiC) γ).re)
    (hsmall : δ ^ (2 : ℕ) * (16 * (xiLineTwoLogDerivConstant + Real.log (|γ| + 4))) < 1) :
    ∃ q : XiZeroCopy, q ≠ q₁ ∧ q ≠ q₂ ∧
      ‖(γ : ℂ) - xiSpectralPoint q‖ ^ (2 : ℕ)
        ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|γ| + 4)) * δ ^ (2 : ℕ) := by
  by_contra hcon
  push Not at hcon
  set L : ℝ := xiLineTwoLogDerivConstant + Real.log (|γ| + 4) with hLdef
  have hLpos : 0 < L := xiLineTwoLogDerivConstant_add_log_pos γ
  have hδsq : 0 < δ ^ (2 : ℕ) := by positivity
  set d : ℝ := Real.sqrt (16 * L) * |δ| with hddef
  have hdpos : 0 < d := by
    refine mul_pos (Real.sqrt_pos.mpr (by linarith)) ?_
    exact abs_pos.mpr hδ
  have hdsq : d ^ (2 : ℕ) = 16 * L * δ ^ (2 : ℕ) := by
    rw [hddef, mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 16 * L), sq_abs]
  have hsep : ∀ q : XiZeroCopy, q ≠ q₁ → q ≠ q₂ → d ≤ ‖(γ : ℂ) - xiSpectralPoint q‖ := by
    intro q hq1 hq2
    have hgt := hcon q hq1 hq2
    rw [← hdsq] at hgt
    nlinarith [hgt, hdpos, norm_nonneg ((γ : ℂ) - xiSpectralPoint q)]
  have hmain := laguerre_offLine_separation hδ hdpos h12 h1 h2 hγ hsep hL
  rw [← hLdef, hdsq] at hmain
  have hexpand : 16 * L * (1 + 1 / (16 * L * δ ^ (2 : ℕ))) = 16 * L + 1 / δ ^ (2 : ℕ) := by
    field_simp
  rw [hexpand] at hmain
  have hkey : 1 / δ ^ (2 : ℕ) ≤ 16 * L := by
    have h2d : (2 : ℝ) / δ ^ (2 : ℕ) = 1 / δ ^ (2 : ℕ) + 1 / δ ^ (2 : ℕ) := by ring
    rw [h2d] at hmain
    linarith
  rw [div_le_iff₀ hδsq] at hkey
  nlinarith [hkey, hsmall]

end

end RHTower
