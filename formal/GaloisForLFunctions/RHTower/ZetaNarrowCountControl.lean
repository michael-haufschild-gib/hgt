import GaloisForLFunctions.RHTower.ZetaNarrowLorentzMass
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalZeroSum

/-!
# Pointwise count control at scale `τ` under local RH

**Theorem** (`exists_abs_narrowMass_sub_le`). There is `t₀` such that for `t ≥ t₀`,
`(log t)^{40} ≤ x ≤ t^{1/8}` and `0 < τ ≤ ½`: if every zero with `|γ − t| ≤ t/2 + 2` lies on the
critical line, then

`|M_τ(t) − (τ/2) log(t/2π)| ≤ τ |D_x(½ + τ + it)| + (2x^{−τ}/(τ log x)) M_τ(t) + 2τ + 4τ Σ_ρ 1/((t/2)² + (t − γ)²)`,

with `M_τ` the narrow Lorentzian mass and `D_x` Selberg's smoothed von Mangoldt polynomial.

**Proof.**
* `M_τ ≈ τ Re ξ'/ξ(½ + τ + it)` (`abs_mul_re_logDeriv_xi_sub_narrowMass_le`).
* `Re ξ'/ξ = Re ζ'/ζ + ½ log(t/2π) + O(1)` (`abs_re_logDeriv_xi_sub_zeta_sub_log_le`).
* Selberg's explicit formula at height `t` (`exists_selberg_explicit_formula_at_height`): every zero
  `ρ` of its rectangle is on the line, so `|K_x(ρ − s)| ≤ 2x^{−τ}/(log x (τ² + (γ − t)²))`. With
  multiplicity this sums to at most `2x^{−τ}/(τ² log x) · M_τ(t)` (`sum_zeroMult_mul_le_tsum`).
-/

noncomputable section

open Complex Set Filter

namespace RHTower

open Sieve

/-- The divisor multiplicity of `ξ` at any point is its natural analytic order. -/
theorem toNat_divisor_xi_eq (w : ℂ) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) w) = (analyticOrderAt xi w).toNat := by
  rw [MeromorphicOn.divisor_apply xi_analyticOnNhd_univ.meromorphicOn (Set.mem_univ w),
    (xi_analyticOnNhd_univ w (Set.mem_univ _)).meromorphicOrderAt_eq]
  have hcoe : ((((analyticOrderAt xi w).toNat : ℕ) : ℕ∞)) = analyticOrderAt xi w :=
    ENat.coe_toNat (xi_orderAt_ne_top w)
  rw [← hcoe]
  simp

/-- **Zeros of `ζ` in the strip, with multiplicity, against zero copies.** For a finite set `Z` of
points of the open strip and `f ≥ 0` summable along the copies,
`Σ_{w ∈ Z} m(w) f(w) ≤ Σ_q f(ρ_q)`. -/
theorem sum_zeroMult_mul_le_tsum {Z : Finset ℂ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {f : ℂ → ℝ} (hf : ∀ w, 0 ≤ f w) (hs : Summable (fun q : XiZeroCopy => f (q.1 : ℂ))) :
    ∑ w ∈ Z, zeroMult w * f w ≤ ∑' q : XiZeroCopy, f (q.1 : ℂ) := by
  classical
  set P : ℂ → Prop := fun w => w ∈ (MeromorphicOn.divisor xi Set.univ).support with hP
  -- the multiplicity of `G` is the divisor multiplicity of `ξ`
  have hm : ∀ w ∈ Z, zeroMult w = (Int.toNat ((MeromorphicOn.divisor xi Set.univ) w) : ℝ) := by
    intro w hw
    rw [zeroMult, Sieve.analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip (hZ w hw),
      toNat_divisor_xi_eq]
  have hzero : ∀ w ∈ Z, ¬ P w → zeroMult w * f w = 0 := by
    intro w hw hPw
    have : (MeromorphicOn.divisor xi Set.univ) w = 0 := by
      simpa [hP, Function.mem_support] using hPw
    rw [hm w hw, this]; simp
  set Z' : Finset XiDivisorSupport := Z.subtype P with hZ'
  set S : Finset XiZeroCopy := Z'.sigma (fun _ => Finset.univ) with hS
  have hleft : ∑ w ∈ Z, zeroMult w * f w = ∑ q ∈ S, f (q.1 : ℂ) := by
    rw [hS, Finset.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hZ', Finset.sum_subtype_eq_sum_filter (p := P) (f := fun w =>
      (Int.toNat ((MeromorphicOn.divisor xi Set.univ) w) : ℝ) * f w)]
    rw [← Finset.sum_filter_add_sum_filter_not Z P]
    have h2 : ∑ w ∈ Z.filter (fun w => ¬ P w), zeroMult w * f w = 0 :=
      Finset.sum_eq_zero fun w hw => by
        rw [Finset.mem_filter] at hw
        exact hzero w hw.1 hw.2
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mem_filter] at hw
    rw [hm w hw.1]
  rw [hleft]
  exact hs.sum_le_tsum S fun q _ => hf _

/-- The Selberg kernel at an on-line zero seen from `½ + τ + it`. -/
theorem norm_selbergKernel_online_le {x τ t : ℝ} (hx : 1 < x) (hτ : 0 ≤ τ) {w : ℂ}
    (hw : w.re = 1 / 2) :
    ‖selbergKernel x (w - narrowPoint τ t)‖ ≤
      2 * Real.exp (-(τ * Real.log x)) / Real.log x * (1 / (τ ^ 2 + (w.im - t) ^ 2)) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have h := norm_selbergKernel_le_line hx (w - narrowPoint τ t)
  have hre : (w - narrowPoint τ t).re = -τ := by rw [Complex.sub_re, narrowPoint_re, hw]; ring
  have him : (w - narrowPoint τ t).im = w.im - t := by rw [Complex.sub_im, narrowPoint_im]
  rw [hre, him, show (-τ) ^ 2 = τ ^ 2 by ring, show -τ * Real.log x = -(τ * Real.log x) by ring,
    show 2 * -τ * Real.log x = -(2 * (τ * Real.log x)) by ring] at h
  refine h.trans ?_
  have he : Real.exp (-(2 * (τ * Real.log x))) ≤ Real.exp (-(τ * Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  set D := τ ^ 2 + (w.im - t) ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hnum : Real.exp (-(2 * (τ * Real.log x))) + Real.exp (-(τ * Real.log x)) ≤
      2 * Real.exp (-(τ * Real.log x)) := by linarith
  calc (Real.exp (-(2 * (τ * Real.log x))) + Real.exp (-(τ * Real.log x))) / (Real.log x * D)
      ≤ 2 * Real.exp (-(τ * Real.log x)) / (Real.log x * D) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 * Real.exp (-(τ * Real.log x)) / Real.log x * (1 / D) := by
        rw [div_mul_div_comm, mul_one]


/-- **Pointwise count control at scale `τ` under local RH.** -/
theorem exists_abs_narrowMass_sub_le :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ x : ℝ, Real.log t ^ (40 : ℕ) ≤ x → x ≤ t ^ ((1 : ℝ) / 8) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      (∀ q : XiZeroCopy, |(q.1 : ℂ).im - t| ≤ t / 2 + 2 → (q.1 : ℂ).re = 1 / 2) →
      |narrowMass τ t - τ * Real.log (t / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ t)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ t +
          2 * τ + 4 * τ * lorentzMassW (t / 2) t := by
  obtain ⟨K, hK, hEF⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hK)
  refine ⟨max t₁ 64, fun t ht x hx1 hx2 τ hτ0 hτ1 hloc => ?_⟩
  have ht64 : 64 ≤ t := le_trans (le_max_right _ _) ht
  have hlogt : 1 < Real.log t := by
    have := Real.log_le_log (by norm_num) (show (64 : ℝ) ≤ t from ht64)
    have h64 : (1 : ℝ) < Real.log 64 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hx : 1 < x := by
    have : 1 < Real.log t ^ (40 : ℕ) := one_lt_pow₀ hlogt (by norm_num)
    linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  obtain ⟨T₁, T₂, hT₁a, hT₁b, hT₂a, hT₂b, hform⟩ := hEF t ht64
  set s := narrowPoint τ t with hs
  have hsre : s.re = 1 / 2 + τ := narrowPoint_re τ t
  have hsim : s.im = t := narrowPoint_im τ t
  -- `ζ(s) ≠ 0`
  have hD1 : (1 : ℝ) ≤ t / 2 := by linarith
  have hloc' : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - t| ≤ t / 2 → (q.1 : ℂ).re = 1 / 2 :=
    fun q hq => hloc q (by linarith)
  have hxi : xi s ≠ 0 := xi_narrowPoint_ne_zero hτ0 (by linarith) hloc'
  have hζ : riemannZeta s ≠ 0 := by
    rcases lt_or_ge (1 / 2 + τ) 1 with hlt | hge
    · intro h0
      apply hxi
      exact (xi_zero_iff_zeta_zero_of_mem_strip (by rw [hsre]; linarith)
        (by rw [hsre]; linarith)).mpr h0
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; linarith)
  have hEFs := (hform x hx s (by rw [hsim, sub_self, abs_zero]; positivity)
    (by rw [hsre]; linarith) (by rw [hsre]; linarith) hζ).trans
    (ht₁ t (le_trans (le_max_left _ _) ht) x hx1 hx2)
  -- the zero sum
  set Z := selbergHeightZeros t T₁ T₂ with hZ
  have hZstrip : ∀ w ∈ Z, (0 < w.re ∧ w.re < 1) ∧ |w.im - t| ≤ t / 2 + 2 := by
    intro w hw
    rw [hZ, selbergHeightZeros, mem_zetaResidueUnitClosedRectangleZeros] at hw
    obtain ⟨hR, h0⟩ := hw
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hR
    have h16 : (16 : ℝ) ≤ 2 * t := by linarith
    have hσ := reflectedLeftAbscissa_pos h16
    have hσ2 : reflectedLeftAbscissa (2 * t) ≤ 2 := by
      have h1 := reflectedLeftAbscissa_le h16
      have hl2 := log_ge_of_sixteen_le h16
      have hp : 1 ≤ Real.log (2 * t) ^ (9 : ℕ) := one_le_pow₀ (by linarith)
      have h2 : 1 / (8 * Real.log (2 * t) ^ (9 : ℕ)) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add] at hre him
    rw [uIcc_of_le hσ2] at hre
    rw [uIcc_of_le (by linarith)] at him
    have hw1 : w ≠ 1 := by
      intro h1; rw [h1] at him; simp at him; linarith [him.1]
    have hζw : riemannZeta w = 0 := by
      have := h0
      rw [zetaResidueUnit, Function.update_of_ne hw1] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hw1
      · exact h
    have hlt1 : w.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hζw
    refine ⟨⟨by linarith [hre.1], hlt1⟩, ?_⟩
    rw [abs_le]; constructor <;> linarith [him.1, him.2]
  have hZline : ∀ w ∈ Z, w.re = 1 / 2 := by
    intro w hw
    obtain ⟨⟨h0, h1⟩, him⟩ := hZstrip w hw
    have hζw : riemannZeta w = 0 := by
      have := hw
      rw [hZ, selbergHeightZeros, mem_zetaResidueUnitClosedRectangleZeros] at this
      have hw1 : w ≠ 1 := fun h => by rw [h] at h1; simp at h1
      have h2 := this.2
      rw [zetaResidueUnit, Function.update_of_ne hw1] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (sub_eq_zero.mp h) hw1
      · exact h
    have hxiw : xi w = 0 := (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mpr hζw
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxiw
    have := hloc q (by rw [hq]; exact him)
    rwa [hq] at this
  set c : ℝ := 2 * Real.exp (-(τ * Real.log x)) / Real.log x with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hZsum : ‖∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
      selbergKernel x (w - s)‖ ≤ c * (narrowMass τ t / τ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ w ∈ Z, ‖((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
        selbergKernel x (w - s)‖ ≤ zeroMult w * (c * (1 / (τ ^ 2 + (w.im - t) ^ 2))) := by
      intro w hw
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (norm_selbergKernel_online_le hx hτ0.le (hZline w hw))
        (zeroMult_nonneg w)
    refine (Finset.sum_le_sum hpt).trans ?_
    have hconv := sum_zeroMult_mul_le_tsum (Z := Z) (fun w hw => (hZstrip w hw).1)
      (f := fun w => c * (1 / (τ ^ 2 + (w.im - t) ^ 2)))
      (fun w => by positivity)
      (by
        have := (summable_narrowMassTerm hτ0.le (by linarith) t).mul_left (c / τ ^ 2)
        refine this.congr fun q => ?_
        unfold narrowMassTerm
        have : (t - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - t) ^ 2 := by ring
        rw [this]; field_simp)
    refine hconv.trans (le_of_eq ?_)
    rw [narrowMass, div_eq_mul_inv, ← tsum_mul_right, ← tsum_mul_left]
    congr 1; funext q
    unfold narrowMassTerm
    have : (t - (q.1 : ℂ).im) ^ 2 = ((q.1 : ℂ).im - t) ^ 2 := by ring
    rw [this]; field_simp
  -- the three ingredients
  have hV1 := abs_mul_re_logDeriv_xi_sub_narrowMass_le hτ0 hτ1 hD1 hloc'
  have hV2 := abs_re_logDeriv_xi_sub_zeta_sub_log_le hτ0 hτ1 (by linarith) hζ
  rw [← hs] at hV1 hV2
  set A := logDeriv riemannZeta s
  set P := selbergVonMangoldtPoly x s
  set Zs := ∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s)
  have hReA : |A.re| ≤ ‖P‖ + ‖Zs‖ + 1 := by
    have h1 : |(A + P + Zs).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hEFs
    have h2 : |P.re| ≤ ‖P‖ := Complex.abs_re_le_norm _
    have h3 : |Zs.re| ≤ ‖Zs‖ := Complex.abs_re_le_norm _
    rw [Complex.add_re, Complex.add_re] at h1
    have := abs_le.mp h1
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  have hM0 := narrowMass_nonneg τ t
  have hτZ : τ * ‖Zs‖ ≤ c / τ * narrowMass τ t := by
    have := mul_le_mul_of_nonneg_left hZsum hτ0.le
    calc τ * ‖Zs‖ ≤ τ * (c * (narrowMass τ t / τ ^ 2)) := this
      _ = c / τ * narrowMass τ t := by field_simp
  have hcτ : c / τ = 2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) := by
    rw [hc]; field_simp
  rw [hcτ] at hτZ
  have hsplit : narrowMass τ t - τ * Real.log (t / (2 * Real.pi)) / 2 =
      (narrowMass τ t - τ * (logDeriv xi s).re) +
        τ * ((logDeriv xi s).re - A.re - Real.log (t / (2 * Real.pi)) / 2) + τ * A.re := by ring
  rw [hsplit]
  have e1 : |narrowMass τ t - τ * (logDeriv xi s).re| ≤ 4 * τ * lorentzMassW (t / 2) t := by
    rw [abs_sub_comm]; exact hV1
  have e2 : |τ * ((logDeriv xi s).re - A.re - Real.log (t / (2 * Real.pi)) / 2)| ≤ τ := by
    rw [abs_mul, abs_of_pos hτ0]; nlinarith
  have e3 : |τ * A.re| ≤ τ * (‖P‖ + ‖Zs‖ + 1) := by
    rw [abs_mul, abs_of_pos hτ0]; exact mul_le_mul_of_nonneg_left hReA hτ0.le
  calc |(narrowMass τ t - τ * (logDeriv xi s).re) +
        τ * ((logDeriv xi s).re - A.re - Real.log (t / (2 * Real.pi)) / 2) + τ * A.re|
      ≤ |narrowMass τ t - τ * (logDeriv xi s).re| +
        |τ * ((logDeriv xi s).re - A.re - Real.log (t / (2 * Real.pi)) / 2)| + |τ * A.re| :=
        abs_add_three _ _ _
    _ ≤ 4 * τ * lorentzMassW (t / 2) t + τ + τ * (‖P‖ + ‖Zs‖ + 1) := by linarith
    _ ≤ τ * ‖P‖ + 2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ t +
          2 * τ + 4 * τ * lorentzMassW (t / 2) t := by nlinarith

end RHTower
