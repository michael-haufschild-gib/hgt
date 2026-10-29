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
* **Compression and the upper half** (`hermNegIndex_le_atomicGram`, `hermNegIndex_atomicGram_le`).
  The Gram matrix of finitely many real atomic tests at horizon `N` is a compression of the atomic
  Gram matrix, and HKT's receiver bound caps the latter by `κ(K_ζ)` at every width.
* **Sources** (`exists_spline_family`, `exists_gevrey_family`). The integer translates of the cubic
  spline carry every `m ≤ κ(K_ζ)`; mollifying them by the dilated profile keeps `m` negative squares
  (lower semicontinuity of the index) and makes them Gevrey of the profile's class.
* **Synthesis in Gram norm reaches the index** (`eventually_le_hermNegIndex_of_synthesis`). Any
  atomic synthesis of a negative family whose errors vanish in the synthesis norms makes the atomic
  Gram matrices carry its negative squares; the regularity class enters only through the synthesis.
* **Residue classes** (`eventually_le_hermNegIndex_atomicGram_residue`, `eventually_of_residues`).
  The Euler–Maclaurin synthesis lives on horizons `nB`, `B = blockSize R`; on the class
  `N = nB + ρ` the schedule `κ(· + ρ)` still has Gevrey overlap growth, the synthesized family is
  embedded at horizon `N`, and finitely many classes cover all large `N`.
* **The theorems** (`eventually_le_hermNegIndex_atomicGram`, `tendsto_hermNegIndex_atomicGram`,
  `dcProfile_atomicGram_reaches_index`). For a Gevrey-`s` profile and a schedule of Gevrey overlap
  growth the indices of the atomic Gram matrices converge to `κ(K_ζ)` in `ℕ∞`; for every `α > 1` the
  Denjoy–Carleman profile at width `(log log N)^α/N` does it.

This is a transfer statement: the topology of entrywise convergence of finite Gram matrices carries
the index from smooth tests to the atomic sections along the explicit schedule. It uses no
selectivity input; the upper half is a zero-side statement about `ζ`.
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
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
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
  have hA := Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (F u) : (0 : ℝ) ≤ ∫ u, F u ^ 2)
  have hB := Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (D u) : (0 : ℝ) ≤ ∫ u, D u ^ 2)
  rw [Real.sqrt_le_left (by positivity), he]
  nlinarith [le_abs_self (∫ u, F u * D u), Real.sqrt_nonneg (∫ u, F u ^ 2),
    Real.sqrt_nonneg (∫ u, D u ^ 2)]

/-- `√(L(F + D)) ≤ √(L F) + √(L D)` for the Lévy energy `L`. -/
theorem sqrt_levyEnergy_add_le (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hD : ContDiff ℝ 2 D) (hDc : HasCompactSupport D) :
    Real.sqrt (RHTower.levyEnergy fun u => F u + D u) ≤
      Real.sqrt (RHTower.levyEnergy F) + Real.sqrt (RHTower.levyEnergy D) := by
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
  2 * |RHTower.gammaHardyPhaseRate 0| * (2 * (a * (Real.sqrt (2 * R) * e)) + 2 * R * e ^ 2) +
    (2 * (l * Real.sqrt V) + V) +
    2 * primeMass R * (2 * (a * (Real.sqrt (2 * R) * e)) + 2 * R * e ^ 2) +
    4 * Real.cosh (R / 2) * c * (2 * R * e) +
    4 * Real.cosh (R / 2) ^ 2 * (2 * R * e) ^ 2

/-- `weilErr` is dominated by its majorant. -/
theorem weilErr_le_bound {G : ℝ → ℝ} {a l c R e V : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e)
    (ha : Real.sqrt (∫ u, G u ^ 2) ≤ a) (hl : Real.sqrt (RHTower.levyEnergy G) ≤ l)
    (hc : |RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G| ≤ c) :
    weilErr G R e V ≤ weilErrBound a l c R e V := by
  unfold weilErr weilErrBound
  have hP := primeMass_nonneg R
  have hch : 0 ≤ Real.cosh (R / 2) := (Real.cosh_pos _).le
  have h1 : Real.sqrt (∫ u, G u ^ 2) * (Real.sqrt (2 * R) * e) ≤ a * (Real.sqrt (2 * R) * e) :=
    mul_le_mul_of_nonneg_right ha (by positivity)
  have h2 : Real.sqrt (RHTower.levyEnergy G) * Real.sqrt V ≤ l * Real.sqrt V :=
    mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg _)
  have h3 : 4 * Real.cosh (R / 2) * (|RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G|) *
      (2 * R * e) ≤ 4 * Real.cosh (R / 2) * c * (2 * R * e) := by
    have : 0 ≤ 2 * R * e := by positivity
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 4 * Real.cosh (R / 2))
    nlinarith
  have hg := abs_nonneg (RHTower.gammaHardyPhaseRate 0)
  nlinarith

/-- The majorant vanishes with `e` and `V`. -/
theorem tendsto_weilErrBound (a l c R : ℝ) {e V : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hV : Tendsto V atTop (𝓝 0)) :
    Tendsto (fun n => weilErrBound a l c R (e n) (V n)) atTop (𝓝 0) := by
  unfold weilErrBound
  have hsV : Tendsto (fun n => Real.sqrt (V n)) atTop (𝓝 0) := by simpa using hV.sqrt
  have h := ((((((((he.const_mul (Real.sqrt (2 * R))).const_mul a).const_mul 2).add
    ((he.pow 2).const_mul (2 * R))).const_mul (2 * |RHTower.gammaHardyPhaseRate 0|)).add
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
  set l := Real.sqrt (RHTower.levyEnergy F) + 1
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
    have hl : Real.sqrt (RHTower.levyEnergy G) ≤ l := by
      refine (sqrt_levyEnergy_add_le hF hFc hD2 hDc).trans ?_
      have : Real.sqrt (RHTower.levyEnergy (Dn n)) ≤ Real.sqrt (V n) := Real.sqrt_le_sqrt hLev
      simp only [l]; linarith
    have hc : |RHTower.coshHalfMoment G| + |RHTower.sinhHalfMoment G| ≤ c := by
      refine (moments_add_le hF.continuous hFc hD2.continuous hDc hDR).trans ?_
      have : 2 * (Real.cosh (R' / 2) * ∫ u, |Dn n u|) ≤ 2 * (Real.cosh (R' / 2) * (2 * R' * e n)) :=
        by gcongr
      simp only [c]; linarith
    have := weilErr_le_bound (V := V n) hR' he0 ha hl hc
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
    weilPair_real_eq hAi2 hAic hAj2 hAjc, e1, e2]
  have t1 := weilQuad_comp_sub (fun v => F i v + F j v + (Dn n i v + Dn n j v)) (c n)
  have t2 := weilQuad_comp_sub (fun v => F i v - F j v + (Dn n i v - Dn n j v)) (c n)
  beta_reduce at t1 t2 ⊢
  rw [t1, t2]

end Gram

/-! ### Atomic Gram matrices -/

section Atomic

open ArithmeticElectrostatics (atomicTest contDiff_atomicTest)

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-- **The atomic Gram matrix** at horizon `N` of a real profile `ψ`: the Weil Gram matrix of the
translates `ψ(· − log n)`, `1 ≤ n ≤ N`. -/
def atomicGram (ψ : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  weilGram Λw fun a : Fin N => Tr (Real.log ((a : ℝ) + 1)) (cx ψ)

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ n ∈ Icc 1 N, f n = ∑ a : Fin N, f (a + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp

/-- An atomic test, as a complex test, is the combination of the atoms. -/
theorem cx_atomicTest_eq (N : ℕ) (x : ℕ → ℝ) (ψ : ℝ → ℝ) :
    cx (atomicTest N x ψ) =
      ∑ a : Fin N, ((x (a + 1) : ℝ) : ℂ) • Tr (Real.log ((a : ℝ) + 1)) (cx ψ) := by
  funext u
  simp only [cx, atomicTest, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ArithmeticCastelnuovoSeveri.translate]
  push_cast
  rw [sum_Icc_one_eq_sum_fin]
  push_cast
  rfl

/-- Extending an atomic test by zero coefficients does not change it. -/
theorem atomicTest_extend {N N' : ℕ} (h : N ≤ N') (x : ℕ → ℝ) (ψ : ℝ → ℝ) :
    atomicTest N x ψ = atomicTest N' (fun j => if j ≤ N then x j else 0) ψ := by
  funext u
  unfold atomicTest
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun j hj hjN => by
    have : ¬ j ≤ N := fun hle => hjN (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hle⟩)
    simp [this]]
  refine Finset.sum_congr rfl fun j hj => ?_
  beta_reduce
  rw [if_pos (Finset.mem_Icc.mp hj).2]

/-- **Compression.** The Weil Gram matrix of finitely many real atomic tests at horizon `N` has at
most as many negative squares as the atomic Gram matrix. -/
theorem hermNegIndex_le_atomicGram {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    {k : ℝ} (hk : 0 < k) {n N : ℕ} (x : Fin n → ℕ → ℝ) :
    hermNegIndex (weilGram Λw fun i => cx (atomicTest N (x i) (dilate k φ))) ≤
      hermNegIndex (atomicGram (dilate k φ) N) := by
  set X : Matrix (Fin N) (Fin n) ℂ := fun a i => ((x i (a + 1) : ℝ) : ℂ)
  have hψ : ContDiff ℝ 2 (dilate k φ) := contDiff_dilate hφ k
  have hψc : HasCompactSupport (dilate k φ) := hasCompactSupport_dilate_of hφ1 hk
  have hat : ∀ a : Fin N, ContDiff ℝ 2 (Tr (Real.log ((a : ℝ) + 1)) (cx (dilate k φ))) :=
    fun a => ArithmeticCastelnuovoSeveri.translate_contDiff (cx_contDiff hψ) _
  have hatc : ∀ a : Fin N, HasCompactSupport (Tr (Real.log ((a : ℝ) + 1)) (cx (dilate k φ))) :=
    fun a => ArithmeticCastelnuovoSeveri.translate_hasCompactSupport (cx_hasCompactSupport hψc) _
  have hA : ∀ i, ContDiff ℝ 2 (cx (atomicTest N (x i) (dilate k φ))) := fun i =>
    cx_contDiff (atomicTest_dilate_mem hφ hφ1 hk N (x i)).1
  have hAc : ∀ i, HasCompactSupport (cx (atomicTest N (x i) (dilate k φ))) := fun i =>
    cx_hasCompactSupport (atomicTest_dilate_mem hφ hφ1 hk N (x i)).2
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ X.mulVecLin fun y => ?_
  rw [Matrix.mulVecLin_apply, atomicGram,
    ArithmeticCastelnuovoSeveri.hermQuad_weilGram _ _ hat hatc,
    ArithmeticCastelnuovoSeveri.hermQuad_weilGram _ _ hA hAc]
  have key : (∑ a, conj (X.mulVec y a) • Tr (Real.log ((a : ℝ) + 1)) (cx (dilate k φ))) =
      ∑ i, conj (y i) • cx (atomicTest N (x i) (dilate k φ)) := by
    simp_rw [cx_atomicTest_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Complex.conj_ofReal, X]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [key]

/-- **The upper half.** At every width, the atomic Gram matrix has at most `κ(K_ζ)` negative
squares (HKT's uniform receiver bound). -/
theorem hermNegIndex_atomicGram_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    {k : ℝ} (hk : 0 < k) (N : ℕ) :
    (hermNegIndex (atomicGram (dilate k φ) N) : ℕ∞) ≤
      HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel :=
  HeckeKreinToeplitz.hermNegIndex_weilGram_le_negIndex_zetaKernel
    ⟨contDiff_dilate hφ k, hasCompactSupport_dilate_of hφ1 hk⟩ _

end Atomic

/-! ### The negative squares of the Weil kernel on real Gevrey families -/

section Source

open BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

theorem exists_le_of_le_iSup_nat {a : ℕ → ℕ} {m : ℕ} (h : (m : ℕ∞) ≤ ⨆ N, (a N : ℕ∞)) :
    ∃ N, m ≤ a N := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, Nat.zero_le _⟩
  have hlt : ((m - 1 : ℕ) : ℕ∞) < ⨆ N, (a N : ℕ∞) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hm one_pos) h
  obtain ⟨N, hN⟩ := lt_iSup_iff.mp hlt
  have : m - 1 < a N := by exact_mod_cast hN
  exact ⟨N, by omega⟩

/-- `SupportedIn` is monotone in the radius. -/
theorem supportedIn_mono {R R' : ℝ} {h : ℝ → ℝ} (hh : SupportedIn R h) (hR : R ≤ R') :
    SupportedIn R' h := fun u hu => hh u (lt_of_le_of_lt hR hu)

/-- The Weil Gram matrix of real `C²` compactly supported tests is Hermitian. -/
theorem weilGram_cx_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → ℝ → ℝ}
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i)) :
    (weilGram Λw fun i => cx (F i)).IsHermitian := by
  rw [ArithmeticCastelnuovoSeveri.weilGram_eq_zeroGram _ (fun i => cx_contDiff (hF i))
    fun i => cx_hasCompactSupport (hFc i)]
  exact ArithmeticCastelnuovoSeveri.zeroGram_isHermitian _ _

/-- **Real spline families carry the index**: for every `m ≤ κ(K_ζ)` some real translates
`B(· − log n)`, `n ≤ N`, of the cubic spline have a Weil Gram matrix with `m` negative squares. -/
theorem exists_spline_family {m : ℕ}
    (hm : (m : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∃ N : ℕ, m ≤ hermNegIndex (weilGram Λw fun i : Fin N =>
      cx fun u => cubicSpline (u - Real.log ((i : ℝ) + 1))) := by
  rw [HeckeKreinToeplitz.negIndex_zetaKernel,
    HeckeKreinToeplitz.negIndex_zetaKernel_eq_iSup_integerAtoms] at hm
  exact exists_le_of_le_iSup_nat hm

variable {φ : ℝ → ℝ} {A Bφ s : ℝ}

/-- **Gevrey families carry the index.** For every `m ≤ κ(K_ζ)` there are finitely many real
smooth tests supported in `[−R, R]`, of Gevrey class `s` with common constants, whose Weil Gram
matrix has `m` negative squares: mollify the spline family by the dilated profile. -/
theorem exists_gevrey_family (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hBφ : 0 ≤ Bφ) (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    {m : ℕ} (hm : (m : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∃ (n : ℕ) (G : Fin n → ℝ → ℝ) (R M b : ℝ), 0 ≤ R ∧ 0 ≤ M ∧ 0 ≤ b ∧
      (∀ i, ContDiff ℝ ∞ (G i)) ∧ (∀ i, SupportedIn R (G i)) ∧
      (∀ i l t, |iteratedDeriv l (G i) t| ≤ M * b ^ l * (l.factorial : ℝ) ^ s) ∧
      m ≤ hermNegIndex (weilGram Λw fun i => cx (G i)) := by
  obtain ⟨n, hn⟩ := exists_spline_family hm
  set B : Fin n → ℝ → ℝ := fun i u => cubicSpline (u - Real.log ((i : ℝ) + 1))
  have hB2 : ∀ i, ContDiff ℝ 2 (B i) := fun i =>
    contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)
  have hBc : ∀ i, HasCompactSupport (B i) := fun i =>
    hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight _)
  -- common support radius, sup bound and Lipschitz constant
  choose Ri Mi Li hRi hRiB hMiB hLiB using fun i => exists_test_bounds (hB2 i) (hBc i)
  set R := ∑ i, Ri i
  set M := ∑ i, |Mi i|
  set L := ∑ i, |Li i|
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => hRi i
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBR : ∀ i, SupportedIn R (B i) := fun i => supportedIn_mono (hRiB i)
    (Finset.single_le_sum (fun j _ => hRi j) (Finset.mem_univ i))
  have hBM : ∀ i t, |B i t| ≤ M := fun i t => (hMiB i t).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |Mi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  have hBL : ∀ i u v, |B i u - B i v| ≤ L * |u - v| := fun i u v => (hLiB i u v).trans
    (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun j => |Li j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) (abs_nonneg _))
  -- the mollified families converge to the spline family
  set A0 := ∫ s, |φ s|
  set A1 := ∫ s, |deriv φ s|
  obtain ⟨he, hV, -, -⟩ := tendsto_mollifyErr L A0 M A1 (R + 1)
  have hconv := tendsto_weilGram_of_perturbation (F := B) (R' := R + 1) (by linarith) hB2 hBc
    (fun i => supportedIn_mono (hBR i) (by linarith)) (A := fun r i => mollify (B i) φ r)
    (Dn := fun r i x => mollify (B i) φ r x - B i x) (c := fun _ => 0)
    (e := fun r : ℕ => L * (1 / (r : ℝ)) * A0) (LD := fun r : ℕ => M * ((r : ℝ) * A1) + L)
    (k := fun r : ℕ => (r : ℝ))
    (Eventually.of_forall fun r i => by funext u; simp only [sub_zero]; ring)
    (by
      filter_upwards [eventually_ge_atTop 1] with r hr i
      have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
      obtain ⟨h2, hR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint (hB2 i) (hBR i) (hBM i)
        (hBL i) hr'
      exact ⟨h2, hR, hsup, hlip, hr'⟩)
    he hV
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex (weilGram_cx_isHermitian hB2 hBc)
    hconv
  obtain ⟨r, hr, hr1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa using this
  refine ⟨n, fun i => mollify (B i) φ r, R + 1, M * A, Bφ * r, by linarith, mul_nonneg hM0 hA0,
    mul_nonneg hBφ hr0.le, fun i => contDiff_mollify hφ hφ1 (hB2 i).continuous hr0,
    fun i => mollify_supportedIn hφ1 (hBR i) hr1', fun i l t => ?_, hn.trans hr⟩
  have := abs_iteratedDeriv_mollify_le hφ hφ1 (hB2 i).continuous (hBM i) hr0 hA l t
  simpa only [mul_assoc] using this

end Source

/-! ### Synthesis along every residue class -/

section Schedules

open ArithmeticElectrostatics (atomicTest)

variable {φ : ℝ → ℝ} {A Bφ s : ℝ}

/-- Shifting the horizon keeps Gevrey overlap growth. -/
theorem overlapGrowthGevrey_shift {κ : ℕ → ℝ} (hκ : OverlapGrowthGevrey s κ) (ρ : ℕ) :
    OverlapGrowthGevrey s fun N => κ (N + ρ) := by
  have hsh : Tendsto (fun N : ℕ => N + ρ) atTop atTop := tendsto_add_atTop_nat ρ
  refine ⟨hκ.1.comp hsh, ?_⟩
  have hg := hκ.2.comp hsh
  have hK := hκ.1.comp hsh
  have hll : Tendsto (fun N => Real.log (Real.log (κ (N + ρ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hK)
  refine tendsto_atTop_mono' atTop ?_ (hg.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
  filter_upwards [hK.eventually_gt_atTop 0, hll.eventually_ge_atTop 1, eventually_ge_atTop ρ,
    eventually_ge_atTop 1, hg.eventually_ge_atTop 0] with N hk hl hNρ hN1 hg0
  simp only [Function.comp] at hg0 ⊢
  have hls : 0 < Real.log (Real.log (κ (N + ρ))) ^ s := Real.rpow_pos_of_pos (by linarith) s
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNρ' : (ρ : ℝ) ≤ N := by exact_mod_cast hNρ
  push_cast at hg0 ⊢
  have heq : (N : ℝ) / κ (N + ρ) / Real.log (Real.log (κ (N + ρ))) ^ s =
      (N : ℝ) / (N + ρ) * (((N : ℝ) + ρ) / κ (N + ρ) / Real.log (Real.log (κ (N + ρ))) ^ s) := by
    field_simp
  rw [heq]
  have hfrac : 1 / 2 ≤ (N : ℝ) / (N + ρ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  nlinarith

/-- If a property holds eventually along every residue class modulo `B`, it holds eventually. -/
theorem eventually_of_residues {P : ℕ → Prop} {B : ℕ} (hB : 0 < B)
    (h : ∀ ρ < B, ∀ᶠ n in atTop, P (n * B + ρ)) : ∀ᶠ N in atTop, P N := by
  have h' : ∀ ρ, ∃ n₀ : ℕ, ρ < B → ∀ n ≥ n₀, P (n * B + ρ) := fun ρ => by
    by_cases hρ : ρ < B
    · obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (h ρ hρ)
      exact ⟨n₀, fun _ => hn₀⟩
    · exact ⟨0, fun h => absurd h hρ⟩
  choose n₀ hn₀ using h'
  refine Filter.eventually_atTop.mpr ⟨(∑ ρ ∈ range B, n₀ ρ) * B, fun N hN => ?_⟩
  have hρ : N % B < B := Nat.mod_lt _ hB
  have h1 : n₀ (N % B) ≤ ∑ ρ ∈ range B, n₀ ρ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr hρ)
  have h2 : ∑ ρ ∈ range B, n₀ ρ ≤ N / B := (Nat.le_div_iff_mul_le hB).mpr hN
  have := hn₀ (N % B) hρ (N / B) (h1.trans h2)
  rwa [Nat.div_add_mod' N B] at this

/-- **Synthesis in Gram norm reaches the index.** Let finitely many real `C²` tests `G_i`, supported
in `[−R′, R′]`, carry `m` negative squares. Suppose that for large `j` the atomic tests at horizon
`H_j ≤ N_j` and width `1/k_j` with coefficients `X_{j,i}` are translates of `G_i + D_{j,i}`, with
perturbations obeying common bounds `e_j → 0` and `synthLevy R′ e_j L_j k_j → 0`. Then the atomic
Gram matrices at horizon `N_j` eventually carry `m` negative squares. The regularity class of the
profile enters only through the existence of such a synthesis. -/
theorem eventually_le_hermNegIndex_of_synthesis (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ)
    {n : ℕ} {G : Fin n → ℝ → ℝ} {R' : ℝ} (hR' : 0 ≤ R') (hG2 : ∀ i, ContDiff ℝ 2 (G i))
    (hGR : ∀ i, SupportedIn R' (G i)) {m : ℕ}
    (hm : m ≤ hermNegIndex (weilGram Λw fun i => cx (G i))) {H N : ℕ → ℕ}
    (hHN : ∀ j, H j ≤ N j) {k : ℕ → ℝ} (X : ℕ → Fin n → ℕ → ℝ) (Dn : ℕ → Fin n → ℝ → ℝ)
    (c e LD : ℕ → ℝ)
    (hsyn : ∀ᶠ j in atTop, 1 ≤ k j ∧ ∀ i,
      atomicTest (H j) (X j i) (dilate (k j) φ) = (fun u => G i (u - c j) + Dn j i (u - c j)) ∧
      ContDiff ℝ 2 (Dn j i) ∧ SupportedIn R' (Dn j i) ∧ (∀ u, |Dn j i u| ≤ e j) ∧
      ∀ u v, |Dn j i u - Dn j i v| ≤ LD j * |u - v|)
    (he : Tendsto e atTop (𝓝 0))
    (hV : Tendsto (fun j => synthLevy R' (e j) (LD j) (k j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, m ≤ hermNegIndex (atomicGram (dilate (k j) φ) (N j)) := by
  have hGc : ∀ i, HasCompactSupport (G i) := fun i => hasCompactSupport_of_vanishes (hGR i)
  have hconv := tendsto_weilGram_of_perturbation (F := G) hR' hG2 hGc hGR
    (A := fun j i => atomicTest (H j) (X j i) (dilate (k j) φ)) (Dn := Dn) (c := c) (e := e)
    (LD := LD) (k := k) (hsyn.mono fun j hj i => (hj.2 i).1)
    (hsyn.mono fun j hj i => by
      obtain ⟨-, h2, hR1, hsup, hlip⟩ := hj.2 i
      exact ⟨h2, hR1, hsup, hlip, hj.1⟩)
    he hV
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex (weilGram_cx_isHermitian hG2 hGc)
    hconv
  filter_upwards [hev, hsyn] with j hj hj2
  have hk0 : 0 < k j := by linarith [hj2.1]
  refine hm.trans (hj.trans ?_)
  have hext : (fun i => cx (atomicTest (H j) (X j i) (dilate (k j) φ))) =
      fun i => cx (atomicTest (N j) (fun l => if l ≤ H j then X j i l else 0)
        (dilate (k j) φ)) := by
    funext i; rw [atomicTest_extend (hHN j)]
  rw [hext]
  exact hermNegIndex_le_atomicGram hφ hφ1 hk0 _

/-- **One residue class.** Fix a Gevrey family carrying `m` negative squares, supported in
`[−R, R]`, and a residue `ρ` modulo `B = blockSize R`. Along `N = nB + ρ` the Euler–Maclaurin
synthesis of the family at level `n` and width `1/κ_N` converges in Gram matrix, so the atomic
Gram matrix at horizon `N` eventually carries `m` negative squares. -/
theorem eventually_le_hermNegIndex_atomicGram_residue (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthGevrey s κ) {n : ℕ} {G : Fin n → ℝ → ℝ} {R M b : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hb : 0 ≤ b) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (hGR : ∀ i, SupportedIn R (G i))
    (hGM : ∀ i l t, |iteratedDeriv l (G i) t| ≤ M * b ^ l * (l.factorial : ℝ) ^ s) {m : ℕ}
    (hm : m ≤ hermNegIndex (weilGram Λw fun i => cx (G i))) (ρ : ℕ) :
    ∀ᶠ j in atTop, m ≤ hermNegIndex (atomicGram (dilate (κ (j * blockSize R + ρ)) φ)
      (j * blockSize R + ρ)) := by
  set B := blockSize R
  have hB : 1 ≤ B := SpacingScaleHarmonicAnalysis.one_le_blockSize R
  have hκρ := overlapGrowthGevrey_shift hκ ρ
  set k : ℕ → ℝ := fun j => κ (j * B + ρ)
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa using this
  set A0 := ∫ s, |φ s|
  set Mseq : ℕ → ℝ := fun l => M * b ^ l * (l.factorial : ℝ) ^ s
  set Aseq : ℕ → ℝ := fun q => ∫ s, |iteratedDeriv q φ s|
  -- the synthesis at every level
  have hsyn : ∀ (j : ℕ) (i : Fin n), ∃ (x : ℕ → ℝ) (D : ℝ → ℝ), 2 ≤ j → 1 ≤ k j →
      atomicTest (j * B) x (dilate (k j) φ) =
          (fun u => G i (u - (Real.log j + R)) + D (u - (Real.log j + R))) ∧
        ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
        (∀ u, |D u| ≤ gevErr M b A Bφ s (k j) A0 (gevOrder (k j)) j) ∧
        ∀ u v, |D u - D v| ≤ emLip Mseq Aseq (k j) j * |u - v| := fun j i => by
    by_cases hj : 2 ≤ j ∧ 1 ≤ k j
    · obtain ⟨x, D, h⟩ := exists_gevreySynthesis hφ hφ1 hφint (hG i) (hGR i) hM hb hBφ hs
        (hGM i) hA hj.1 hj.2 (gevOrder (k j))
      exact ⟨x, D, fun _ _ => h⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose X Dn hXD using hsyn
  obtain ⟨he, hV⟩ := tendsto_gevrey (A0 := A0) hs hκρ hB (mul_nonneg hM hA0) hb hBφ Mseq Aseq
    (R + 1)
  have hk : Tendsto k atTop atTop := hκρ.1.comp
    (tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hB) tendsto_id)
  refine eventually_le_hermNegIndex_of_synthesis (hφ.of_le (natCast_le_infty 2)) hφ1
    (R' := R + 1) (by linarith) (fun i => (hG i).of_le (natCast_le_infty 2))
    (fun i => supportedIn_mono (hGR i) (by linarith)) hm (H := fun j => j * B)
    (N := fun j => j * B + ρ) (fun j => Nat.le_add_right _ ρ) X Dn (fun j => Real.log j + R)
    (fun j => gevErr M b A Bφ s (k j) A0 (gevOrder (k j)) j) (fun j => emLip Mseq Aseq (k j) j)
    ?_ he hV
  filter_upwards [eventually_ge_atTop 2, hk.eventually_ge_atTop 1] with j hj2 hk1
  exact ⟨hk1, fun i => hXD j i hj2 hk1⟩

/-- **The explicit schedules reach the index.** For a Gevrey profile of class `s` and a dilation
schedule of Gevrey overlap growth, every `m ≤ κ(K_ζ)` is eventually carried by the atomic Gram
matrices `Σ_{n≤N} x_n φ_{κ_N}(· − log n)`. -/
theorem eventually_le_hermNegIndex_atomicGram (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthGevrey s κ) {m : ℕ}
    (hm : (m : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∀ᶠ N in atTop, m ≤ hermNegIndex (atomicGram (dilate (κ N) φ) N) := by
  obtain ⟨n, G, R, M, b, hR, hM, hb, hG, hGR, hGM, hGm⟩ :=
    exists_gevrey_family hφ hφ1 hφint hBφ hA hm
  exact eventually_of_residues (SpacingScaleHarmonicAnalysis.one_le_blockSize R) fun ρ _ =>
    eventually_le_hermNegIndex_atomicGram_residue hφ hφ1 hφint hs hBφ hA hκ hR hM hb hG hGR hGM
      hGm ρ

/-- **The indices converge to the index of the Weil kernel**, finite or infinite. -/
theorem tendsto_hermNegIndex_atomicGram (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hs : 0 ≤ s) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * (q.factorial : ℝ) ^ s)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthGevrey s κ) :
    Tendsto (fun N => (hermNegIndex (atomicGram (dilate (κ N) φ) N) : ℕ∞)) atTop
      (𝓝 (HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · lift a to ℕ using ha.ne_top
    have : ((a + 1 : ℕ) : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel := by
      exact_mod_cast Order.add_one_le_of_lt ha
    filter_upwards [eventually_le_hermNegIndex_atomicGram hφ hφ1 hφint hs hBφ hA hκ this]
      with N hN
    exact_mod_cast Nat.lt_of_succ_le hN
  · filter_upwards [hκ.1.eventually_gt_atTop 0] with N hN
    exact lt_of_le_of_lt (hermNegIndex_atomicGram_le hφ2 hφ1 hN N) ha

/-- **The Denjoy–Carleman window reaches the index.** For every `α > 1` there is an odd `r` such
that the atomic Gram matrices of the Denjoy–Carleman profile `φ_r` at width `(log log N)^α/N` have
indices converging to `κ(K_ζ)`, the number of zeros of `ζ` right of the critical line. -/
theorem dcProfile_atomicGram_reaches_index {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ, Odd r ∧ Tendsto (fun N : ℕ => (hermNegIndex (atomicGram
      (dilate ((N : ℝ) / Real.log (Real.log N) ^ α) (dcProfile r)) N) : ℕ∞)) atTop
      (𝓝 (HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel)) := by
  set m := ⌈(α - 1)⁻¹⌉₊
  set r := 2 * m + 1
  have hr : Odd r := odd_two_mul_add_one m
  have hα1 : 0 < α - 1 := by linarith
  have hrpos : (0 : ℝ) < r := by positivity
  have hrs : (r : ℝ)⁻¹ < α - 1 := by
    have hm' : (α - 1)⁻¹ ≤ m := Nat.le_ceil _
    have : (α - 1)⁻¹ < (r : ℝ) := by
      simp only [r]; push_cast; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    rw [inv_lt_comm₀ hrpos hα1]; exact this
  refine ⟨r, hr, tendsto_hermNegIndex_atomicGram (contDiff_dcProfile r) (dcProfile_vanishesOff hr)
    (integral_dcProfile hr) (s := 1 + (r : ℝ)⁻¹) (by positivity) (by positivity)
    (integral_abs_iteratedDeriv_dcProfile_le hr)
    (overlapGrowthGevrey_loglog (by positivity) (by linarith))⟩

end Schedules

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
