import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDenjoyCarlemanProfiles
import GaloisForLFunctions.HeckeKreinToeplitz.EveryReceiverAtEveryWidthIsBoundedByTheIndex
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# The explicit schedules reach the whole index

The atomic families `Σ_{n≤N} x_n φ_κ(· − log n)` of a Gevrey profile `φ` at width `1/κ_N` decide RH
when the overlap `N/κ_N` beats `(log log κ_N)^s` (SSHA): their Weil Gram matrices are eventually
positive semidefinite iff there is no zero right of the critical line. Deciding is the statement
`κ = 0 ⟺ eventually index 0`. This file proves the stronger statement that the same schedules
**reach the index**: the negative index of the atomic Gram matrix at horizon `N` is at most
`κ(K_ζ)`, the number of right zeros, for every `N`, and at least every `m ≤ κ(K_ζ)` for all large
`N`. So the indices converge to `κ(K_ζ)`, finite or infinite.

* **Real tests** (`weilPair_real_eq`). On real `C²` compactly supported tests Weil's sesquilinear form
  is real and symmetric, hence the polarization of the quadratic form `Q = weilQuad`:
  `W(f, g) = (Q(f + g) − Q(f − g))/4`. Reality is the functional equation (the zero configuration
  is closed under `ρ ↦ ρ̄`), symmetry its Hermitian structure.
* **Two-sided continuity** (`tendsto_weilQuad_add`). For a fixed test `F` and perturbations `D_n`
  with sup bounds `e_n → 0` and Lévy bounds `synthLevy → 0`, `Q(F + D_n) → Q(F)`. The upper side is
  the perturbation bound of SSHA; the lower side is the same bound read from the base `F + D_n`,
  whose `L²`, Lévy and moment norms stay bounded.
* **Gram convergence** (`tendsto_weilGram_of_perturbation`). Translates of `F_i + D_{n,i}` have Weil
  Gram matrices converging entrywise to that of the `F_i`, by polarization.
-/

open MeasureTheory Set Filter Topology Finset Complex
open scoped ContDiff ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (weilGram cx cx_contDiff cx_hasCompactSupport)

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

/-- The von Mangoldt weight of the explicit formula. -/
local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Weil's form on real tests -/

/-- The diagonal Weil value of a real test is its quadratic form. -/
theorem weilFull_cx_self (h : ℝ → ℝ) :
    RHTower.weilFullFunctional Λw (EF.weilTest (cx h) (cx h)) = (weilQuad h : ℂ) :=
  Complex.ext rfl (by
    rw [ofReal_im]
    exact RHTower.WeilSpectral.im_weilFullFunctional_weilTest_self _ _)

/-- **Polarization on real tests**: `W(f, g) = (Q(f + g) − Q(f − g))/4`, a real number. -/
theorem weilPair_real_eq {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    RHTower.weilFullFunctional Λw (EF.weilTest (cx f) (cx g)) =
      (((weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4 : ℝ) : ℂ) := by
  have hF : ∀ i, ContDiff ℝ 2 (![cx f, cx g] i) := fun i => by
    fin_cases i
    · exact cx_contDiff hf
    · exact cx_contDiff hg
  have hFc : ∀ i, HasCompactSupport (![cx f, cx g] i) := fun i => by
    fin_cases i
    · exact cx_hasCompactSupport hfc
    · exact cx_hasCompactSupport hgc
  have hp := RHTower.OddResolvent.weilFullFunctional_finset_gram Λw univ ![(1 : ℂ), 1]
    ![cx f, cx g] hF hFc
  have hm := RHTower.OddResolvent.weilFullFunctional_finset_gram Λw univ ![(1 : ℂ), -1]
    ![cx f, cx g] hF hFc
  have hsp : (∑ i, ![(1 : ℂ), 1] i • ![cx f, cx g] i) = cx fun u => f u + g u := by
    funext u; simp [Fin.sum_univ_two, cx]
  have hsm : (∑ i, ![(1 : ℂ), -1] i • ![cx f, cx g] i) = cx fun u => f u - g u := by
    funext u; simp [Fin.sum_univ_two, cx, sub_eq_add_neg]
  rw [hsp, weilFull_cx_self] at hp
  rw [hsm, weilFull_cx_self] at hm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    map_one, map_neg, one_mul, mul_one, neg_mul, mul_neg, neg_neg] at hp hm
  -- the off-diagonal entries agree and are real
  have hfg : ContDiff ℝ 2 (cx f) := cx_contDiff hf
  have hgg : ContDiff ℝ 2 (cx g) := cx_contDiff hg
  have h10 : RHTower.weilFullFunctional Λw (EF.weilTest (cx g) (cx f)) =
      RHTower.weilFullFunctional Λw (EF.weilTest (cx f) (cx g)) := by
    rw [← RHTower.zeta_W_eq_weilFullFunctional_mixed hgg (cx_hasCompactSupport hgc) hfg
        (cx_hasCompactSupport hfc),
      ← RHTower.zeta_W_eq_weilFullFunctional_mixed hfg (cx_hasCompactSupport hfc) hgg
        (cx_hasCompactSupport hgc),
      ← ArithmeticCastelnuovoSeveri.W_conj_symm,
      ArithmeticOrientationGeometry.W_real_of_fes _
        ArithmeticCastelnuovoSeveri.fesSymmetric_zetaZeroConfig]
  rw [h10] at hp hm
  push_cast
  linear_combination (hm - hp) / 4

/-! ### Two-sided continuity of Weil's form under small perturbations -/

section Continuity

variable {F D : ℝ → ℝ} {R' : ℝ}

/-- `√(∫ (F + D)²) ≤ √(∫ F²) + √(∫ D²)`. -/
theorem sqrt_integral_sq_add_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (hD : Continuous D) (hDc : HasCompactSupport D) :
    Real.sqrt (∫ u, (F u + D u) ^ 2) ≤ Real.sqrt (∫ u, F u ^ 2) + Real.sqrt (∫ u, D u ^ 2) := by
  have h1 := integrable_sq_of_continuous hF hFc
  have h2 := integrable_sq_of_continuous hD hDc
  have h3 : Integrable fun u => F u * D u :=
    (hF.mul hD).integrable_of_hasCompactSupport hFc.mul_right
  have hcs := abs_integral_mul_le h1 h2 h3
  have he : ∫ u, (F u + D u) ^ 2 = (∫ u, F u ^ 2) + 2 * (∫ u, F u * D u) + ∫ u, D u ^ 2 := by
    have : (fun u => (F u + D u) ^ 2) = fun u => 1 * F u ^ 2 + 2 * (F u * D u) + D u ^ 2 := by
      funext u; ring
    rw [this, integral_lin3 h1 h3 h2]
    ring
  have hA := Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (F u))
  have hB := Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (D u))
  rw [Real.sqrt_le_left (by positivity), he]
  nlinarith [le_abs_self (∫ u, F u * D u), Real.sqrt_nonneg (∫ u, F u ^ 2),
    Real.sqrt_nonneg (∫ u, D u ^ 2)]

/-- `√(L(F + D)) ≤ √(L F) + √(L D)` for the Lévy energy `L`. -/
theorem sqrt_levyEnergy_add_le (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hD : ContDiff ℝ 2 D) (hDc : HasCompactSupport D) :
    Real.sqrt (levyEnergy fun u => F u + D u) ≤
      Real.sqrt (levyEnergy F) + Real.sqrt (levyEnergy D) := by
  have h := levyEnergy_add_le hF hFc hD hDc
  have hA := Real.sq_sqrt (levyEnergy_nonneg' F)
  have hB := Real.sq_sqrt (levyEnergy_nonneg' D)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- The pole moments of `F + D` move by at most `cosh(R′/2) ‖D‖₁` each. -/
theorem moments_add_le (hF : Continuous F) (hFc : HasCompactSupport F) (hD : Continuous D)
    (hDc : HasCompactSupport D) (hDR : SupportedIn R' D) :
    |RHTower.coshHalfMoment fun u => F u + D u| + |RHTower.sinhHalfMoment fun u => F u + D u| ≤
      |RHTower.coshHalfMoment F| + |RHTower.sinhHalfMoment F| +
        2 * (Real.cosh (R' / 2) * ∫ u, |D u|) := by
  have hc : Continuous fun u : ℝ => Real.cosh (u / 2) := by fun_prop
  have hs : Continuous fun u : ℝ => Real.sinh (u / 2) := by fun_prop
  have hiF : ∀ {φ : ℝ → ℝ}, Continuous φ → Integrable fun u => F u * φ u := fun hφ =>
    (hF.mul hφ).integrable_of_hasCompactSupport hFc.mul_right
  have hiD : ∀ {φ : ℝ → ℝ}, Continuous φ → Integrable fun u => D u * φ u := fun hφ =>
    (hD.mul hφ).integrable_of_hasCompactSupport hDc.mul_right
  have eC : RHTower.coshHalfMoment (fun u => F u + D u) =
      RHTower.coshHalfMoment F + ∫ u, D u * Real.cosh (u / 2) := by
    unfold RHTower.coshHalfMoment
    rw [← integral_add (hiF hc) (hiD hc)]
    congr 1; funext u; ring
  have eS : RHTower.sinhHalfMoment (fun u => F u + D u) =
      RHTower.sinhHalfMoment F + ∫ u, D u * Real.sinh (u / 2) := by
    unfold RHTower.sinhHalfMoment
    rw [← integral_add (hiF hs) (hiD hs)]
    congr 1; funext u; ring
  have bC := abs_moment_le hD hDc hDR hc fun u hu => abs_cosh_half_le hu
  have bS := abs_moment_le hD hDc hDR hs fun u hu => abs_sinh_half_le hu
  rw [eC, eS]
  have := abs_add_le (RHTower.coshHalfMoment F) (∫ u, D u * Real.cosh (u / 2))
  have := abs_add_le (RHTower.sinhHalfMoment F) (∫ u, D u * Real.sinh (u / 2))
  linarith

/-- The majorant of `weilErr` in terms of bounds `a, l, c` on the base norms. -/
def weilErrBound (a l c R e V : ℝ) : ℝ :=
  2 * |gammaHardyPhaseRate 0| * (2 * (a * (Real.sqrt (2 * R) * e)) + 2 * R * e ^ 2) +
    (2 * (l * Real.sqrt V) + V) +
    2 * primeMass R * (2 * (a * (Real.sqrt (2 * R) * e)) + 2 * R * e ^ 2) +
    4 * Real.cosh (R / 2) * c * (2 * R * e) +
    4 * Real.cosh (R / 2) ^ 2 * (2 * R * e) ^ 2

/-- `weilErr` is dominated by its majorant. -/
theorem weilErr_le_bound {G : ℝ → ℝ} {a l c R e V : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (hV : 0 ≤ V)
    (ha : Real.sqrt (∫ u, G u ^ 2) ≤ a) (hl : Real.sqrt (levyEnergy G) ≤ l)
    (hc : |RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G| ≤ c) :
    weilErr G R e V ≤ weilErrBound a l c R e V := by
  unfold weilErr weilErrBound
  have hP := primeMass_nonneg R
  have hch : 0 ≤ Real.cosh (R / 2) := (Real.cosh_pos _).le
  have h1 : Real.sqrt (∫ u, G u ^ 2) * (Real.sqrt (2 * R) * e) ≤ a * (Real.sqrt (2 * R) * e) :=
    mul_le_mul_of_nonneg_right ha (by positivity)
  have h2 : Real.sqrt (levyEnergy G) * Real.sqrt V ≤ l * Real.sqrt V :=
    mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg _)
  have h3 : 4 * Real.cosh (R / 2) * (|RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G|) *
      (2 * R * e) ≤ 4 * Real.cosh (R / 2) * c * (2 * R * e) := by
    have : 0 ≤ 2 * R * e := by positivity
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 4 * Real.cosh (R / 2))
    nlinarith
  have hg := abs_nonneg (gammaHardyPhaseRate 0)
  nlinarith

/-- The majorant vanishes with `e` and `V`. -/
theorem tendsto_weilErrBound (a l c R : ℝ) {e V : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hV : Tendsto V atTop (𝓝 0)) :
    Tendsto (fun n => weilErrBound a l c R (e n) (V n)) atTop (𝓝 0) := by
  unfold weilErrBound
  have hsV : Tendsto (fun n => Real.sqrt (V n)) atTop (𝓝 0) := by simpa using hV.sqrt
  have h := ((((((((he.const_mul (Real.sqrt (2 * R))).const_mul a).const_mul 2).add
    ((he.pow 2).const_mul (2 * R))).const_mul (2 * |gammaHardyPhaseRate 0|)).add
    (((hsV.const_mul l).const_mul 2).add hV)).add
    (((((he.const_mul (Real.sqrt (2 * R))).const_mul a).const_mul 2).add
    ((he.pow 2).const_mul (2 * R))).const_mul (2 * primeMass R))).add
    ((he.const_mul (2 * R)).const_mul (4 * Real.cosh (R / 2) * c))).add
    (((he.const_mul (2 * R)).pow 2).const_mul (4 * Real.cosh (R / 2) ^ 2))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  ring

/-- **Two-sided continuity of Weil's form.** If `D_n` are `C²` perturbations supported in
`[−R′, R′]` with `|D_n| ≤ e_n → 0` and Lévy bounds `synthLevy R′ e_n L_n k_n → 0`, then
`Q(F + D_n) → Q(F)`. -/
theorem tendsto_weilQuad_add (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hFR : SupportedIn R' F) (hR' : 0 ≤ R') {Dn : ℕ → ℝ → ℝ} {e LD k : ℕ → ℝ}
    (hD : ∀ᶠ n in atTop, ContDiff ℝ 2 (Dn n) ∧ SupportedIn R' (Dn n) ∧ (∀ u, |Dn n u| ≤ e n) ∧
      (∀ u v, |Dn n u - Dn n v| ≤ LD n * |u - v|) ∧ 1 ≤ k n)
    (he : Tendsto e atTop (𝓝 0)) (hV : Tendsto (fun n => synthLevy R' (e n) (LD n) (k n)) atTop (𝓝 0)) :
    Tendsto (fun n => weilQuad fun u => F u + Dn n u) atTop (𝓝 (weilQuad F)) := by
  set V := fun n => synthLevy R' (e n) (LD n) (k n)
  set a := Real.sqrt (∫ u, F u ^ 2) + 1
  set l := Real.sqrt (levyEnergy F) + 1
  set c := |RHTower.coshHalfMoment F| + |RHTower.sinhHalfMoment F| + 1
  -- the norms of `D_n` vanish
  have hsq : Tendsto (fun n => Real.sqrt (2 * R') * e n) atTop (𝓝 0) := by
    simpa using he.const_mul (Real.sqrt (2 * R'))
  have hsV : Tendsto (fun n => Real.sqrt (V n)) atTop (𝓝 0) := by simpa using hV.sqrt
  have hl1 : Tendsto (fun n => 2 * (Real.cosh (R' / 2) * (2 * R' * e n))) atTop (𝓝 0) := by
    simpa using ((he.const_mul (2 * R')).const_mul (Real.cosh (R' / 2))).const_mul 2
  have hev := hD.and ((hsq.eventually (gt_mem_nhds one_pos)).and
    ((hsV.eventually (gt_mem_nhds one_pos)).and (hl1.eventually (gt_mem_nhds one_pos))))
  -- upper and lower bounds
  have hup : ∀ᶠ n in atTop, weilQuad (fun u => F u + Dn n u) ≤
      weilQuad F + weilErr F R' (e n) (V n) := hD.mono fun n ⟨hD2, hDR, hDe, hDL, hk⟩ =>
    weilQuad_add_le_of_lip hF hFc hFR hD2 hDR hR' hDe hDL hk
  have hlow : ∀ᶠ n in atTop, weilQuad F - weilErrBound a l c R' (e n) (V n) ≤
      weilQuad (fun u => F u + Dn n u) := by
    filter_upwards [hev] with n ⟨⟨hD2, hDR, hDe, hDL, hk⟩, hs1, hv1, hm1⟩
    obtain ⟨hDc, hsqD, -, hLev, -, hN1⟩ := perturbation_norms hD2 hDR hR' hDe hDL hk
    have he0 : 0 ≤ e n := (abs_nonneg _).trans (hDe 0)
    have hV0 : 0 ≤ V n := (levyEnergy_nonneg' _).trans hLev
    set G : ℝ → ℝ := fun u => F u + Dn n u
    have hG2 : ContDiff ℝ 2 G := hF.add hD2
    have hGc : HasCompactSupport G := hFc.add hDc
    have hGR : SupportedIn R' G := supportedIn_add hFR hDR
    have hN2 : ContDiff ℝ 2 fun u => -Dn n u := hD2.neg
    have hNR : SupportedIn R' fun u => -Dn n u := fun u hu => by
      simp only [hDR u hu, neg_zero]
    have hNe : ∀ u, |-Dn n u| ≤ e n := fun u => by rw [abs_neg]; exact hDe u
    have hNL : ∀ u v, |-Dn n u - -Dn n v| ≤ LD n * |u - v| := fun u v => by
      rw [show -Dn n u - -Dn n v = -(Dn n u - Dn n v) by ring, abs_neg]; exact hDL u v
    have hbase := weilQuad_add_le_of_lip hG2 hGc hGR hN2 hNR hR' hNe hNL hk
    have hGF : (fun u => G u + -Dn n u) = F := by funext u; simp only [G]; ring
    rw [hGF] at hbase
    -- the base norms of `G = F + D_n` are bounded
    have ha : Real.sqrt (∫ u, G u ^ 2) ≤ a :=
      (sqrt_integral_sq_add_le hF.continuous hFc hD2.continuous hDc).trans
        (by simp only [a]; linarith)
    have hl : Real.sqrt (levyEnergy G) ≤ l := by
      refine (sqrt_levyEnergy_add_le hF hFc hD2 hDc).trans ?_
      have : Real.sqrt (levyEnergy (Dn n)) ≤ Real.sqrt (V n) := Real.sqrt_le_sqrt hLev
      simp only [l]; linarith
    have hc : |RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G| ≤ c := by
      refine (moments_add_le hF.continuous hFc hD2.continuous hDc hDR).trans ?_
      have : 2 * (Real.cosh (R' / 2) * ∫ u, |Dn n u|) ≤ 2 * (Real.cosh (R' / 2) * (2 * R' * e n)) :=
        by gcongr
      simp only [c]; linarith
    have := weilErr_le_bound hR' he0 hV0 ha hl hc
    linarith
  have hlim_up : Tendsto (fun n => weilQuad F + weilErr F R' (e n) (V n)) atTop
      (𝓝 (weilQuad F)) := by
    simpa using (tendsto_weilErr F R' he hV).const_add (weilQuad F)
  have hlim_low : Tendsto (fun n => weilQuad F - weilErrBound a l c R' (e n) (V n)) atTop
      (𝓝 (weilQuad F)) := by
    simpa using (tendsto_weilErrBound a l c R' he hV).const_sub (weilQuad F)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_low hlim_up hlow hup

end Continuity

/-! ### Convergence of Gram matrices of perturbed real families -/

section Gram

/-- `synthLevy` is homogeneous of degree two in `(e, L_D)`. -/
theorem synthLevy_two_mul (R e LD k : ℝ) :
    synthLevy R (2 * e) (2 * LD) k = 4 * synthLevy R e LD k := by
  unfold synthLevy; ring

/-- **Gram convergence.** Let `F_i` be real `C²` tests supported in `[−R′, R′]`, and let `A_{n,i}` be,
for large `n`, the translates by a common `c_n` of `F_i + D_{n,i}`, with perturbations obeying common
bounds `e_n → 0`, `synthLevy → 0`. Then the Weil Gram matrices of the `A_{n,·}` converge entrywise to
that of the `F_·`. -/
theorem tendsto_weilGram_of_perturbation {ι : Type*} {F : ι → ℝ → ℝ} {R' : ℝ} (hR' : 0 ≤ R')
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hFR : ∀ i, SupportedIn R' (F i)) {A : ℕ → ι → ℝ → ℝ} {Dn : ℕ → ι → ℝ → ℝ} {c : ℕ → ℝ}
    {e LD k : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, ∀ i, A n i = fun u => F i (u - c n) + Dn n i (u - c n))
    (hD : ∀ᶠ n in atTop, ∀ i, ContDiff ℝ 2 (Dn n i) ∧ SupportedIn R' (Dn n i) ∧
      (∀ u, |Dn n i u| ≤ e n) ∧ (∀ u v, |Dn n i u - Dn n i v| ≤ LD n * |u - v|) ∧ 1 ≤ k n)
    (he : Tendsto e atTop (𝓝 0)) (hV : Tendsto (fun n => synthLevy R' (e n) (LD n) (k n)) atTop (𝓝 0))
    (i j : ι) :
    Tendsto (fun n => weilGram Λw (fun a => cx (A n a)) i j) atTop
      (𝓝 (weilGram Λw (fun a => cx (F a)) i j)) := by
  -- the pair perturbations obey the doubled bounds
  have he2 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by simpa using he.const_mul 2
  have hV2 : Tendsto (fun n => synthLevy R' (2 * e n) (2 * LD n) (k n)) atTop (𝓝 0) := by
    simp_rw [synthLevy_two_mul]; simpa using hV.const_mul 4
  have hpair : ∀ s : ℝ, s = 1 ∨ s = -1 → Tendsto (fun n => weilQuad fun u =>
      (F i u + s * F j u) + (Dn n i u + s * Dn n j u)) atTop
      (𝓝 (weilQuad fun u => F i u + s * F j u)) := by
    intro s hs
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    have hsupp : SupportedIn R' fun u => F i u + s * F j u := fun u hu => by
      simp only [hFR i u hu, hFR j u hu, mul_zero, add_zero]
    refine tendsto_weilQuad_add ((hF i).add (contDiff_const.mul (hF j)))
      (hasCompactSupport_of_vanishes hsupp) hsupp hR' ?_ he2 hV2
    filter_upwards [hD] with n hn
    obtain ⟨hi2, hiR, hie, hiL, hk⟩ := hn i
    obtain ⟨hj2, hjR, hje, hjL, -⟩ := hn j
    refine ⟨hi2.add (contDiff_const.mul hj2), fun u hu => by
      simp only [hiR u hu, hjR u hu, mul_zero, add_zero], fun u => ?_, fun u v => ?_, hk⟩
    · calc |Dn n i u + s * Dn n j u| ≤ |Dn n i u| + |s| * |Dn n j u| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ 2 * e n := by rw [hs1]; linarith [hie u, hje u]
    · calc |Dn n i u + s * Dn n j u - (Dn n i v + s * Dn n j v)|
          = |(Dn n i u - Dn n i v) + s * (Dn n j u - Dn n j v)| := by ring_nf
        _ ≤ |Dn n i u - Dn n i v| + |s| * |Dn n j u - Dn n j v| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ 2 * LD n * |u - v| := by rw [hs1]; linarith [hiL u v, hjL u v]
  have hp := hpair 1 (Or.inl rfl)
  have hm := hpair (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hp hm
  -- the entries are polarizations
  have hlim : Tendsto (fun n => ((((weilQuad fun u => (F i u + F j u) + (Dn n i u + Dn n j u)) -
      (weilQuad fun u => (F i u - F j u) + (Dn n i u - Dn n j u))) / 4 : ℝ) : ℂ)) atTop
      (𝓝 ((((weilQuad fun u => F i u + F j u) - weilQuad fun u => F i u - F j u) / 4 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((hp.sub hm).div_const 4)
  rw [show weilGram Λw (fun a => cx (F a)) i j =
      RHTower.weilFullFunctional Λw (EF.weilTest (cx (F i)) (cx (F j))) from rfl,
    weilPair_real_eq (hF i) (hFc i) (hF j) (hFc j)]
  refine hlim.congr' ?_
  filter_upwards [hA, hD] with n hAn hDn
  obtain ⟨hi2, hiR, -, -, -⟩ := hDn i
  obtain ⟨hj2, hjR, -, -, -⟩ := hDn j
  have htr : ∀ G : ℝ → ℝ, SupportedIn R' G → HasCompactSupport fun u => G (u - c n) :=
    fun G hG => hasCompactSupport_of_vanishes (B := R' + |c n|) fun u hu => hG _ (by
      have := abs_sub_abs_le_abs_sub u (c n); linarith)
  have hAi2 : ContDiff ℝ 2 (A n i) := by
    rw [hAn i]; exact ((hF i).add hi2).comp (contDiff_id.sub contDiff_const)
  have hAj2 : ContDiff ℝ 2 (A n j) := by
    rw [hAn j]; exact ((hF j).add hj2).comp (contDiff_id.sub contDiff_const)
  have hAic : HasCompactSupport (A n i) := by
    rw [hAn i]; exact htr _ (supportedIn_add (hFR i) hiR)
  have hAjc : HasCompactSupport (A n j) := by
    rw [hAn j]; exact htr _ (supportedIn_add (hFR j) hjR)
  have e1 : (fun u => A n i u + A n j u) =
      fun u => (fun v => (F i v + F j v) + (Dn n i v + Dn n j v)) (u - c n) := by
    funext u; rw [hAn i, hAn j]; ring
  have e2 : (fun u => A n i u - A n j u) =
      fun u => (fun v => (F i v - F j v) + (Dn n i v - Dn n j v)) (u - c n) := by
    funext u; rw [hAn i, hAn j]; ring
  rw [show weilGram Λw (fun a => cx (A n a)) i j =
      RHTower.weilFullFunctional Λw (EF.weilTest (cx (A n i)) (cx (A n j))) from rfl,
    weilPair_real_eq hAi2 hAic hAj2 hAjc, e1, e2, weilQuad_comp_sub, weilQuad_comp_sub]

end Gram

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
