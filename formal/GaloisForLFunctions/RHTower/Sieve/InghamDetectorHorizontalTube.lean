import GaloisForLFunctions.RHTower.Sieve.InghamDetectorFarRightBoundary
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization
import GaloisForLFunctions.HTGeometry.LogDerivativeFactor
import GaloisForLFunctions.RHTower.CofinalSeparatedHeight
import GaloisForLFunctions.RHTower.MinimumModulus

/-!
# Horizontal-tube control for the Ingham detector

Jensen factorization, finite zero avoidance, and Borel--Caratheodory control select
zero-free horizontal detector segments with polylogarithmic logarithmic derivative.
-/
open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

private theorem extracted_multiplicity_eq_divisor
    {f g : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfac : ∀ z : ℂ, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hgne : ∀ a ∈ T, g a ≠ 0) {a : ℂ} (haT : a ∈ T) (haU : a ∈ U) :
    MeromorphicOn.divisor f U a = (m a : ℤ) := by
  classical
  let q : ℂ → ℂ := fun z => (∏ b ∈ T.erase a, (z - b) ^ (m b)) * g z
  have hqA : AnalyticAt ℂ q a := by
    dsimp only [q]
    have hp : AnalyticAt ℂ (fun z : ℂ => ∏ b ∈ T.erase a, (z - b) ^ (m b)) a := by
      have hp0 : AnalyticAt ℂ (∏ b ∈ T.erase a,
          fun z : ℂ => (z - b) ^ (m b)) a := by
        apply Finset.analyticAt_prod
        intro b hb
        fun_prop
      refine hp0.congr ?_
      filter_upwards with z
      simp only [Finset.prod_apply]
    exact hp.mul (hg a (Set.mem_univ _))
  have hq0 : q a ≠ 0 := by
    dsimp only [q]
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro b hb
      exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm)
    · exact hgne a haT
  have hfactorfun : f = fun z => (z - a) ^ (m a) * q z := by
    funext z
    rw [hfac z]
    dsimp only [q]
    rw [← Finset.mul_prod_erase T (fun b => (z - b) ^ (m b)) haT]
    ring
  have hord : analyticOrderAt f a = (m a : ℕ∞) := by
    rw [hfactorfun]
    change analyticOrderAt
        ((fun z : ℂ => (z - a) ^ (m a)) * q) a = (m a : ℕ∞)
    rw [analyticOrderAt_mul
      (GaloisForLFunctions.HTGeometry.analyticAt_sub_pow a (m a) a) hqA,
      GaloisForLFunctions.HTGeometry.analyticOrderAt_sub_pow_self,
      hqA.analyticOrderAt_eq_zero.mpr hq0, add_zero]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf haU, hord]
  simp

private theorem exists_positive_zero_free_factor_closedBall
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hball : closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U)
    (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in nhds a, f z = 0) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (∀ a ∈ T, a ∈ closedBall c R) ∧
      (∀ a ∈ T, 1 ≤ m a) ∧
      ∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z := by
  classical
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zero_free_factor_closedBall
      hU hball hf hnz
  let S : Finset ℂ := T.filter fun a => 0 < m a
  have hST : S ⊆ T := Finset.filter_subset _ _
  refine ⟨S, m, g, hg, hgfree, ?_, ?_, ?_⟩
  · intro a ha
    exact hTmem a (hST ha)
  · intro a ha
    exact Finset.mem_filter.mp ha |>.2
  · intro z hz
    rw [hfac z hz]
    congr 1
    symm
    apply Finset.prod_subset hST
    intro a haT haS
    have hma : m a = 0 := by
      have : ¬ 0 < m a := by simpa only [S, Finset.mem_filter, haT, true_and] using haS
      omega
    rw [hma, pow_zero]

private theorem sum_multiplicity_le_finsum
    {D : ℂ → ℤ} (hDfinite : D.support.Finite) (hDnonneg : ∀ a, 0 ≤ D a)
    {T : Finset ℂ} {m : ℂ → ℕ} (hm : ∀ a ∈ T, D a = (m a : ℤ)) :
    ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ ((∑ᶠ a, D a : ℤ) : ℝ) := by
  classical
  let S : Finset ℂ := hDfinite.toFinset
  have hcast : ((∑ a ∈ T, m a : ℕ) : ℤ) = ∑ a ∈ T, D a := by
    push_cast
    exact Finset.sum_congr rfl fun a ha => (hm a ha).symm
  have hTunion : ∑ a ∈ T, D a ≤ ∑ a ∈ T ∪ S, D a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
    intro a haU haT
    exact hDnonneg a
  have hSunion : ∑ a ∈ S, D a = ∑ a ∈ T ∪ S, D a := by
    apply Finset.sum_subset Finset.subset_union_right
    intro a haU haS
    have haNotSupp : a ∉ D.support := by
      simpa only [S, hDfinite.mem_toFinset] using haS
    exact not_ne_iff.mp (by simpa only [Function.mem_support] using haNotSupp)
  have hfinsum : (∑ᶠ a, D a) = ∑ a ∈ S, D a := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    exact hDfinite.mem_toFinset.mpr ha
  have hInt : ((∑ a ∈ T, m a : ℕ) : ℤ) ≤ (∑ᶠ a, D a) := by
    rw [hcast, hfinsum, hSunion]
    exact hTunion
  exact_mod_cast hInt

private theorem exists_tube_factor_data
    {f : ℂ → ℂ} {c : ℂ} {Mf m0 L : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in nhds a, f z = 0)
    (hsphere : ∀ z ∈ sphere c 4, ‖f z‖ ≤ Mf)
    (hcenter : m0 ≤ ‖f c‖)
    (hmass : ((∑ᶠ u, MeromorphicOn.divisor f
        (closedBall c (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤ L) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g Set.univ ∧
      (∀ z ∈ closedBall c (15 / 4 : ℝ), g z ≠ 0) ∧
      (∀ a ∈ T, a ∈ closedBall c (15 / 4 : ℝ)) ∧
      (∀ a ∈ T, 1 ≤ m a) ∧
      (∀ z : ℂ, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z) ∧
      ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ L ∧
      (∀ z ∈ closedBall c 4,
        ‖g z‖ ≤ Mf / ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a)) ∧
      m0 / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a) ≤ ‖g c‖ := by
  classical
  obtain ⟨T, m, g, hg, hgfree, hTmem, hmpos, hfac⟩ :=
    exists_positive_zero_free_factor_closedBall isOpen_univ
      (Set.subset_univ _) hf (fun a _ => hnz a)
  let K : Set ℂ := closedBall c (15 / 4 : ℝ)
  let D : ℂ → ℤ := MeromorphicOn.divisor f K
  have hfK : AnalyticOnNhd ℂ f K := hf.mono (Set.subset_univ _)
  have hfOuter : AnalyticOnNhd ℂ f (closedBall c 4) := hf.mono (Set.subset_univ _)
  have hKsub : K ⊆ closedBall c 4 := closedBall_subset_closedBall (by norm_num)
  have hDfinite : D.support.Finite :=
    hfOuter.meromorphicOn.divisor_support_finite_of_subset
      (isCompact_closedBall c 4) hKsub
  have hDnonneg : ∀ a, 0 ≤ D a :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfK
  have hgne : ∀ a ∈ T, g a ≠ 0 := fun a ha => hgfree a (hTmem a ha)
  have hmult : ∀ a ∈ T, D a = (m a : ℤ) := by
    intro a ha
    exact extracted_multiplicity_eq_divisor hfK hg
      (fun z => hfac z (Set.mem_univ z)) hgne ha (hTmem a ha)
  have hNmass : ((∑ a ∈ T, m a : ℕ) : ℝ) ≤
      ((∑ᶠ a, D a : ℤ) : ℝ) :=
    sum_multiplicity_le_finsum hDfinite hDnonneg hmult
  have hNL : ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ L := by
    exact hNmass.trans (by simpa only [D, K] using hmass)
  let N : ℕ := ∑ a ∈ T, m a
  have hrootNorm : ∀ a ∈ T, ‖a - c‖ ≤ (15 : ℝ) / 4 := by
    intro a ha
    simpa only [mem_closedBall, dist_eq_norm] using hTmem a ha
  have hgsphere : ∀ z ∈ sphere c 4,
      ‖g z‖ ≤ Mf / ((1 : ℝ) / 4) ^ N := by
    intro z hz
    have hzNorm : ‖z - c‖ = 4 := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have hdist : ∀ a ∈ T, (1 : ℝ) / 4 ≤ ‖z - a‖ := by
      intro a ha
      have hrev := norm_sub_norm_le (z - c) (a - c)
      have hsub : (z - c) - (a - c) = z - a := by ring
      rw [hsub] at hrev
      linarith [hrootNorm a ha]
    have hprod : ((1 : ℝ) / 4) ^ N ≤ ∏ a ∈ T, ‖z - a‖ ^ (m a) := by
      have hpowProd : ((1 : ℝ) / 4) ^ N =
          ∏ a ∈ T, ((1 : ℝ) / 4) ^ (m a) := by
        exact (Finset.prod_pow_eq_pow_sum T m ((1 : ℝ) / 4)).symm
      rw [hpowProd]
      apply Finset.prod_le_prod
      · intro a ha
        positivity
      · intro a ha
        exact pow_le_pow_left₀ (by positivity) (hdist a ha) _
    have hnorm : ‖f z‖ = (∏ a ∈ T, ‖z - a‖ ^ (m a)) * ‖g z‖ := by
      rw [hfac z (Set.mem_univ z), norm_mul, norm_prod]
      congr 1
      exact Finset.prod_congr rfl fun a _ => norm_pow _ _
    have hstep : ((1 : ℝ) / 4) ^ N * ‖g z‖ ≤ ‖f z‖ := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    have hgap : 0 < ((1 : ℝ) / 4) ^ N := by positivity
    rw [le_div_iff₀ hgap]
    simpa only [mul_comm] using hstep.trans (hsphere z hz)
  have hgball : ∀ z ∈ closedBall c 4,
      ‖g z‖ ≤ Mf / ((1 : ℝ) / 4) ^ N := by
    exact RHTower.norm_le_on_closedBall_of_sphere (by norm_num)
      (fun z hz => hg z (Set.mem_univ z)) hgsphere
  have hprodCenter : (∏ a ∈ T, ‖c - a‖ ^ (m a)) ≤
      ((15 : ℝ) / 4) ^ N := by
    have hpowProd : ((15 : ℝ) / 4) ^ N =
        ∏ a ∈ T, ((15 : ℝ) / 4) ^ (m a) := by
      exact (Finset.prod_pow_eq_pow_sum T m ((15 : ℝ) / 4)).symm
    rw [hpowProd]
    apply Finset.prod_le_prod
    · intro a ha
      positivity
    · intro a ha
      have haNorm : ‖c - a‖ ≤ (15 : ℝ) / 4 := by
        rw [norm_sub_rev]
        exact hrootNorm a ha
      exact pow_le_pow_left₀ (norm_nonneg _) haNorm _
  have hnormCenter : ‖f c‖ = (∏ a ∈ T, ‖c - a‖ ^ (m a)) * ‖g c‖ := by
    rw [hfac c (Set.mem_univ c), norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun a _ => norm_pow _ _
  have hcenterStep : m0 ≤ ((15 : ℝ) / 4) ^ N * ‖g c‖ := by
    calc
      m0 ≤ ‖f c‖ := hcenter
      _ = (∏ a ∈ T, ‖c - a‖ ^ (m a)) * ‖g c‖ := hnormCenter
      _ ≤ ((15 : ℝ) / 4) ^ N * ‖g c‖ :=
        mul_le_mul_of_nonneg_right hprodCenter (norm_nonneg _)
  have hinnerPow : 0 < ((15 : ℝ) / 4) ^ N := by positivity
  have hgcenter : m0 / ((15 : ℝ) / 4) ^ N ≤ ‖g c‖ := by
    rw [div_le_iff₀ hinnerPow]
    simpa only [mul_comm] using hcenterStep
  exact ⟨T, m, g, hg, hgfree, hTmem, hmpos,
    fun z => hfac z (Set.mem_univ z), hNL, hgball, hgcenter⟩

private theorem norm_logDeriv_le_of_factor_data
    {f g : ℂ → ℂ} {c z : ℂ} {T : Finset ℂ} {m : ℂ → ℕ}
    {Mf m0 d : ℝ}
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hgfree : ∀ w ∈ closedBall c (15 / 4 : ℝ), g w ≠ 0)
    (hfac : ∀ w : ℂ, f w = (∏ a ∈ T, (w - a) ^ (m a)) * g w)
    (hgball : ∀ w ∈ closedBall c 4,
      ‖g w‖ ≤ Mf / ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a))
    (hm0 : 0 < m0)
    (hgcenter : m0 / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a) ≤ ‖g c‖)
    (hd : 0 < d) (hsep : ∀ a ∈ T, d ≤ ‖z - a‖)
    (hz : ‖z - c‖ ≤ (17 : ℝ) / 5) :
    ‖logDeriv f z‖ ≤
      ((∑ a ∈ T, m a : ℕ) : ℝ) / d +
        2 * (Real.log
          (((Mf / ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a)) /
            (m0 / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a)))) + 1) *
          ((7 : ℝ) / 2) /
          ((15 : ℝ) / 4 - (7 : ℝ) / 2) /
          ((7 : ℝ) / 2 - (17 : ℝ) / 5) := by
  let N : ℕ := ∑ a ∈ T, m a
  have hzne : ∀ a ∈ T, z ≠ a := by
    intro a ha hza
    subst z
    have := hsep a ha
    rw [sub_self, norm_zero] at this
    linarith
  have hsplit : logDeriv f z =
      (∑ a ∈ T, (m a : ℂ) / (z - a)) + logDeriv g z := by
    apply GaloisForLFunctions.HTGeometry.logDeriv_of_factor
      (U := ball c (15 / 4 : ℝ)) isOpen_ball
    · exact (hg.differentiableOn).mono (Set.subset_univ _)
    · intro w hw
      exact hgfree w (ball_subset_closedBall hw)
    · intro w hw
      exact hfac w
    · rw [mem_ball_iff_norm]
      linarith
    · exact hzne
  have hrational : ‖∑ a ∈ T, (m a : ℂ) / (z - a)‖ ≤
      ((∑ a ∈ T, m a : ℕ) : ℝ) / d := by
    push_cast
    exact GaloisForLFunctions.HTGeometry.norm_sum_multiplicity_div_le
      (T := T) (m := m) (z := z) (d := d) hd hsep
  have hM : ∀ w ∈ ball c (15 / 4 : ℝ),
      ‖g w‖ ≤ Mf / ((1 : ℝ) / 4) ^ N := by
    intro w hw
    apply hgball w
    exact closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hw)
  have hmco : 0 < m0 / ((15 : ℝ) / 4) ^ N := by positivity
  have hcofactor : ‖logDeriv g z‖ ≤
      2 * (Real.log
          (((Mf / ((1 : ℝ) / 4) ^ N) /
            (m0 / ((15 : ℝ) / 4) ^ N))) + 1) *
        ((7 : ℝ) / 2) /
        ((15 : ℝ) / 4 - (7 : ℝ) / 2) /
        ((7 : ℝ) / 2 - (17 : ℝ) / 5) := by
    rw [logDeriv_apply]
    exact GaloisForLFunctions.HTGeometry.norm_logDeriv_le
      (by norm_num) (by norm_num) (by norm_num)
      ((hg.differentiableOn).mono (Set.subset_univ _))
      (fun w hw => hgfree w (ball_subset_closedBall hw)) hM hmco hgcenter hz
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hrational hcofactor)

private theorem ne_zero_of_factor_data
    {f g : ℂ → ℂ} {z : ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {d : ℝ}
    (hfac : f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hg : g z ≠ 0) (hd : 0 < d)
    (hsep : ∀ a ∈ T, d ≤ ‖z - a‖) : f z ≠ 0 := by
  rw [hfac]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply pow_ne_zero
    exact sub_ne_zero.mpr fun hza => by
      have h := hsep a ha
      have hzero : ‖z - a‖ = 0 := by rw [hza, sub_self, norm_zero]
      rw [hzero] at h
      linarith
  · exact hg

private theorem exists_Ioo_add_one_separated_from_finset
    (F : Finset ℝ) (A delta : ℝ) (hdelta : 0 ≤ delta)
    (hsmall : 2 * F.card * delta < 1) :
    ∃ T ∈ Ioo A (A + 1), ∀ x ∈ F, delta ≤ |T - x| := by
  classical
  let E : Finset ℝ := F.image fun x => x - (A - 1)
  have hcard : E.card ≤ F.card := Finset.card_image_le
  have hsmallE : 2 * E.card * delta < 1 := by
    have hmul : 2 * E.card * delta ≤ 2 * F.card * delta := by
      gcongr
    exact hmul.trans_lt hsmall
  obtain ⟨R, hR, hsep⟩ := RHTower.exists_Ioo_two_mul_separated_from_finset
    E (T := 1) (by norm_num) hdelta hsmallE
  refine ⟨R + (A - 1), ?_, ?_⟩
  · norm_num at hR
    constructor <;> linarith [hR.1, hR.2]
  · intro x hx
    have hxE : x - (A - 1) ∈ E := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have h := hsep (x - (A - 1)) hxE
    convert h using 1
    all_goals ring_nf

theorem norm_inghamMollifier_le_nat_of_re_nonneg
    (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖inghamMollifier X s‖ ≤ (X : ℝ) :=
  norm_inghamMollifier_le_nat X hs

private theorem horizontalTube_geometry
    {X : ℕ} {tau : ℝ} (hX : 10 ≤ X)
    (htlow : (X : ℝ) / 2 ≤ |tau|) (hthigh : |tau| ≤ 2 * (X : ℝ))
    {z : ℂ} (hz : z ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) 4) :
    0 ≤ z.re ∧ z.re ≤ 8 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 3 * (X : ℝ) ∧
      ‖z - 1‖ ≤ 5 * (X : ℝ) := by
  have hdist : ‖z - ((4 : ℂ) + (tau : ℂ) * I)‖ ≤ 4 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hreabs : |z.re - 4| ≤ 4 := by
    have h := Complex.abs_re_le_norm (z - ((4 : ℂ) + (tau : ℂ) * I))
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at h
    exact h.trans hdist
  have himabs : |z.im - tau| ≤ 4 := by
    have h := Complex.abs_im_le_norm (z - ((4 : ℂ) + (tau : ℂ) * I))
    have hcim : ((4 : ℂ) + (tau : ℂ) * I).im = tau := by simp
    rw [sub_im, hcim] at h
    exact h.trans hdist
  have hrelo : 0 ≤ z.re := (abs_le.mp hreabs).1 |> fun h => by linarith
  have hrehi : z.re ≤ 8 := (abs_le.mp hreabs).2 |> fun h => by linarith
  have himhi0 : |z.im| ≤ |tau| + 4 := by
    calc
      |z.im| = |(z.im - tau) + tau| := by ring_nf
      _ ≤ |z.im - tau| + |tau| := abs_add_le _ _
      _ ≤ |tau| + 4 := by linarith
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have himhi : |z.im| ≤ 3 * (X : ℝ) := by linarith
  have himlo0 : |tau| ≤ |z.im| + 4 := by
    calc
      |tau| = |(tau - z.im) + z.im| := by ring_nf
      _ ≤ |tau - z.im| + |z.im| := abs_add_le _ _
      _ = |z.im - tau| + |z.im| := by rw [abs_sub_comm]
      _ ≤ |z.im| + 4 := by linarith
  have himlo : 1 ≤ |z.im| := by linarith
  have hre1 : |(z - 1).re| ≤ 7 := by
    simp only [sub_re, one_re]
    rw [abs_le]
    constructor <;> linarith
  have hnormsub := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have himsub : |(z - 1).im| = |z.im| := by simp
  rw [himsub] at hnormsub
  have hsub : ‖z - 1‖ ≤ 5 * (X : ℝ) := by linarith
  exact ⟨hrelo, hrehi, himlo, himhi, hsub⟩

theorem exists_norm_inghamDetector_horizontalTube_le :
    ∃ (C : ℝ) (Q : ℕ), 0 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∀ z ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) 4,
        ‖inghamDetector X z‖ ≤ C * (X : ℝ) ^ Q := by
  obtain ⟨Cz, N, hCz, hzeta⟩ := RHTower.exists_bound_norm_riemannZeta_strip 8
  let K : ℝ := 5 * Cz * 3 ^ N
  let C : ℝ := K * (10 + K)
  let Q : ℕ := 2 * N + 4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh z hz
  obtain ⟨hzre0, hzre8, hzim1, hzimX, hzsub⟩ :=
    horizontalTube_geometry hX htlow hthigh hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim1
  have hzetaBound : ‖riemannZeta z‖ ≤ Cz * |z.im| ^ N := by
    have hzrepr : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    simpa only [hzrepr] using hzeta z.re z.im (by rw [abs_of_nonneg hzre0]; exact hzre8) hzim1
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hzimPow : |z.im| ^ N ≤ (3 * (X : ℝ)) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) hzimX N
  have hG : ‖zetaResidueUnit z‖ ≤ K * (X : ℝ) ^ (N + 1) := by
    rw [zetaResidueUnit, Function.update_of_ne hz1, norm_mul]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤
          (5 * (X : ℝ)) * (Cz * |z.im| ^ N) :=
        mul_le_mul hzsub hzetaBound (norm_nonneg _) (by positivity)
      _ ≤ (5 * (X : ℝ)) * (Cz * (3 * (X : ℝ)) ^ N) := by gcongr
      _ = K * (X : ℝ) ^ (N + 1) := by
        rw [mul_pow, pow_succ]
        dsimp [K]
        ring
  have hM := norm_inghamMollifier_le_nat X hzre0
  have hA : ‖zetaResidueUnit z * inghamMollifier X z‖ ≤
      K * (X : ℝ) ^ (N + 2) := by
    rw [norm_mul]
    calc
      ‖zetaResidueUnit z‖ * ‖inghamMollifier X z‖ ≤
          (K * (X : ℝ) ^ (N + 1)) * (X : ℝ) :=
        mul_le_mul hG hM (norm_nonneg _) (by positivity)
      _ = K * (X : ℝ) ^ (N + 2) := by rw [pow_succ]; ring
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpowmono : (X : ℝ) ≤ (X : ℝ) ^ (N + 2) := by
    calc
      (X : ℝ) = (X : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (X : ℝ) ^ (N + 2) := pow_le_pow_right₀ hX1 (by omega)
  have hsecond : ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
      (10 + K) * (X : ℝ) ^ (N + 2) := by
    have htwo : 2 * ‖z - 1‖ ≤ 10 * (X : ℝ) := by linarith
    have hten : 10 * (X : ℝ) ≤ 10 * (X : ℝ) ^ (N + 2) := by
      exact mul_le_mul_of_nonneg_left hpowmono (by norm_num)
    calc
      ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
          2 * ‖z - 1‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := by
        calc
          _ ≤ ‖2 * (z - 1)‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := norm_sub_le _ _
          _ = 2 * ‖z - 1‖ + ‖zetaResidueUnit z * inghamMollifier X z‖ := by simp
      _ ≤ 10 * (X : ℝ) + K * (X : ℝ) ^ (N + 2) := by linarith
      _ ≤ 10 * (X : ℝ) ^ (N + 2) + K * (X : ℝ) ^ (N + 2) := by linarith
      _ = (10 + K) * (X : ℝ) ^ (N + 2) := by ring
  rw [inghamDetector, norm_mul]
  calc
    ‖zetaResidueUnit z * inghamMollifier X z‖ *
        ‖2 * (z - 1) - zetaResidueUnit z * inghamMollifier X z‖ ≤
      (K * (X : ℝ) ^ (N + 2)) * ((10 + K) * (X : ℝ) ^ (N + 2)) :=
        mul_le_mul hA hsecond (norm_nonneg _) (by positivity)
    _ = C * (X : ℝ) ^ Q := by
      dsimp [C, Q]
      rw [show 2 * N + 4 = (N + 2) + (N + 2) by omega, pow_add]
      ring

theorem one_half_le_norm_inghamDetector_four
    {X : ℕ} {tau : ℝ} (hX : 10 ≤ X)
    (htlow : (X : ℝ) / 2 ≤ |tau|) :
    (1 : ℝ) / 2 ≤ ‖inghamDetector X ((4 : ℂ) + (tau : ℂ) * I)‖ := by
  let s : ℂ := (4 : ℂ) + (tau : ℂ) * I
  let e : ℂ := riemannZeta s * inghamMollifier X s - 1
  have hX1N : 1 ≤ X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1N
  have he0 : ‖e‖ ≤ (X : ℝ) ^ (-2 : ℝ) / 2 := by
    simpa only [s, e] using norm_inghamMollifiedError_four_le hX1N tau
  have hpow : (X : ℝ) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have he : ‖e‖ ≤ (1 : ℝ) / 2 := by linarith
  have hepow : ‖e ^ 2‖ ≤ (1 : ℝ) / 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg e]
  have hclassical : (3 : ℝ) / 4 ≤ ‖1 - e ^ 2‖ := by
    have hone : (1 : ℝ) ≤ ‖1 - e ^ 2‖ + ‖e ^ 2‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 - e ^ 2) + e ^ 2‖ := by ring_nf
        _ ≤ ‖1 - e ^ 2‖ + ‖e ^ 2‖ := norm_add_le _ _
    linarith
  have htau1 : (1 : ℝ) ≤ |tau| := by
    have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hsub : (1 : ℝ) ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    have himEq : (s - 1).im = tau := by simp [s]
    rw [himEq] at him
    exact htau1.trans him
  have hgauge : (1 : ℝ) ≤ ‖(s - 1) ^ 2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg (s - 1)]
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    rw [him] at htau1
    norm_num at htau1
  rw [inghamDetector_eq_poleCleared X hs1, norm_mul]
  change (1 : ℝ) / 2 ≤ ‖(s - 1) ^ 2‖ * ‖1 - e ^ 2‖
  nlinarith [norm_nonneg (1 - e ^ 2)]

theorem exists_inghamDetector_horizontalTube_zeroMass_le_log :
    ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ((∑ᶠ u, MeromorphicOn.divisor (inghamDetector X)
          (closedBall ((4 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤
        Real.log ((C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2)) /
          Real.log ((4 : ℝ) / (15 / 4 : ℝ)) := by
  obtain ⟨C0, Q, hC0, henv⟩ := exists_norm_inghamDetector_horizontalTube_le
  let C : ℝ := C0 + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ Q := one_le_pow₀ hX1
  have hM1 : (1 : ℝ) ≤ C * (X : ℝ) ^ Q := by nlinarith
  have hsphere : ∀ z ∈ sphere ((4 : ℂ) + (tau : ℂ) * I) |(4 : ℝ)|,
      ‖inghamDetector X z‖ ≤ C * (X : ℝ) ^ Q := by
    intro z hz
    have hzball : z ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) 4 := by
      have := sphere_subset_closedBall hz
      norm_num at this ⊢
      exact this
    have h0 := henv hX htlow hthigh z hzball
    have hmul : C0 * (X : ℝ) ^ Q ≤ C * (X : ℝ) ^ Q := by
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    exact h0.trans hmul
  have hana : AnalyticOnNhd ℂ (inghamDetector X)
      (closedBall ((4 : ℂ) + (tau : ℂ) * I) |(4 : ℝ)|) :=
    (inghamDetector_analyticOnNhd_univ X).mono (Set.subset_univ _)
  have hmain := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds
    (c := (4 : ℂ) + (tau : ℂ) * I) (r := (15 / 4 : ℝ)) (R := 4)
    (M := C * (X : ℝ) ^ Q) (m := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) hM1 (by norm_num) hana
    (one_half_le_norm_inghamDetector_four hX htlow) hsphere
  have habs : |(15 / 4 : ℝ)| = (15 / 4 : ℝ) := by norm_num
  rw [habs] at hmain
  exact hmain

noncomputable def inghamDetectorTubeJensenBound
    (C : ℝ) (Q : ℕ) (X : ℕ) : ℝ :=
  Real.log ((C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2)) /
    Real.log ((4 : ℝ) / (15 / 4 : ℝ))

theorem exists_inghamDetector_horizontalTube_separated_height :
    ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧ ∀ {X : ℕ} {tau A : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ T ∈ Ioo A (A + 1),
        ∀ w ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ),
          inghamDetector X w = 0 →
            (4 * (inghamDetectorTubeJensenBound C Q X + 1))⁻¹ ≤ |T - w.im| := by
  classical
  obtain ⟨C, Q, hC, hcount⟩ :=
    exists_inghamDetector_horizontalTube_zeroMass_le_log
  refine ⟨C, Q, hC, ?_⟩
  intro X tau A hX htlow hthigh
  let c0 : ℂ := (4 : ℂ) + (tau : ℂ) * I
  let K : Set ℂ := closedBall c0 (15 / 4 : ℝ)
  let D := MeromorphicOn.divisor (inghamDetector X) K
  have hanaK : AnalyticOnNhd ℂ (inghamDetector X) K :=
    (inghamDetector_analyticOnNhd_univ X).mono (Set.subset_univ _)
  have hanaOuter : AnalyticOnNhd ℂ (inghamDetector X) (closedBall c0 4) :=
    (inghamDetector_analyticOnNhd_univ X).mono (Set.subset_univ _)
  have hKsub : K ⊆ closedBall c0 4 := by
    exact closedBall_subset_closedBall (by norm_num)
  have hDfinite : D.support.Finite := by
    exact hanaOuter.meromorphicOn.divisor_support_finite_of_subset
      (isCompact_closedBall c0 4) hKsub
  let F : Finset ℂ := hDfinite.toFinset
  have hDnonneg : ∀ w : ℂ, 0 ≤ D w :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanaK
  have hsupport : Function.support D ⊆ (F : Set ℂ) := by
    intro w hw
    exact hDfinite.mem_toFinset.mpr hw
  have hfinsum : (∑ᶠ w, D w) = ∑ w ∈ F, D w :=
    finsum_eq_sum_of_support_subset D hsupport
  have hcardInt : (F.card : ℤ) ≤ ∑ w ∈ F, D w := by
    calc
      (F.card : ℤ) = ∑ _w ∈ F, (1 : ℤ) := by simp
      _ ≤ ∑ w ∈ F, D w := by
        apply Finset.sum_le_sum
        intro w hw
        have hwSupp : w ∈ Function.support D := hDfinite.mem_toFinset.mp hw
        have hwne : D w ≠ 0 := by simpa [Function.mem_support] using hwSupp
        have hwnn := hDnonneg w
        omega
  let L : ℝ := inghamDetectorTubeJensenBound C Q X
  have hcountX : ((∑ᶠ w, D w : ℤ) : ℝ) ≤ L := by
    simpa only [D, K, c0, L, inghamDetectorTubeJensenBound] using
      hcount hX htlow hthigh
  have hcardR : (F.card : ℝ) ≤ ((∑ᶠ w, D w : ℤ) : ℝ) := by
    rw [hfinsum]
    exact_mod_cast hcardInt
  have hFL : (F.card : ℝ) ≤ L := hcardR.trans hcountX
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg F.card) hFL
  let E : Finset ℝ := F.image Complex.im
  have hEcard : E.card ≤ F.card := Finset.card_image_le
  let delta : ℝ := (4 * (L + 1))⁻¹
  have hden : 0 < 4 * (L + 1) := by positivity
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hsmall : 2 * E.card * delta < 1 := by
    have hEL : (E.card : ℝ) ≤ L := by
      exact (Nat.cast_le.mpr hEcard).trans hFL
    have hmul : 2 * (E.card : ℝ) ≤ 2 * L := by linarith
    dsimp only [delta]
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨T, hT, hsep⟩ :=
    exists_Ioo_add_one_separated_from_finset E A delta hdelta hsmall
  refine ⟨T, hT, ?_⟩
  intro w hw hzero
  have hneSome : ∃ z : ℂ, inghamDetector X z ≠ 0 := by
    refine ⟨c0, ?_⟩
    exact norm_ne_zero_iff.mp (ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (one_half_le_norm_inghamDetector_four hX htlow)))
  have hord : ∀ u : ↥K, meromorphicOrderAt (inghamDetector X) (u : ℂ) ≠ ⊤ := by
    intro u
    rw [(analyticAt_inghamDetector X u).meromorphicOrderAt_eq]
    simpa using inghamDetector_order_ne_top_of_exists_ne_zero X u hneSome
  have hzeroSupport : K ∩ inghamDetector X ⁻¹' {0} = Function.support D := by
    exact hanaK.meromorphicNFOn.zero_set_eq_divisor_support hord
  have hwSupp : w ∈ Function.support D := by
    rw [← hzeroSupport]
    exact ⟨hw, by simpa using hzero⟩
  have hwF : w ∈ F := hDfinite.mem_toFinset.mpr hwSupp
  have hwE : w.im ∈ E := Finset.mem_image.mpr ⟨w, hwF, rfl⟩
  simpa only [delta, L] using hsep w.im hwE

theorem inghamDetectorTubeJensenBound_nonneg
    {C : ℝ} {Q X : ℕ} (hC : 1 ≤ C) (hX : 1 ≤ X) :
    0 ≤ inghamDetectorTubeJensenBound C Q X := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (1 : ℝ) ≤ (X : ℝ) ^ Q := one_le_pow₀ hXR
  have harg : (1 : ℝ) ≤ (C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2) := by
    rw [div_eq_mul_inv]
    norm_num
    nlinarith
  have hnum : 0 ≤ Real.log ((C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2)) :=
    Real.log_nonneg harg
  have hden : 0 < Real.log ((4 : ℝ) / (15 / 4 : ℝ)) := by
    apply Real.log_pos
    norm_num
  exact div_nonneg hnum hden.le

theorem exists_inghamDetector_horizontalTube_factor_data :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g Set.univ ∧
        (∀ z ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ), g z ≠ 0) ∧
        (∀ a ∈ T, a ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) ∧
        (∀ a ∈ T, 1 ≤ m a) ∧
        (∀ z : ℂ, inghamDetector X z = (∏ a ∈ T, (z - a) ^ (m a)) * g z) ∧
        ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X ∧
        (∀ z ∈ closedBall ((4 : ℂ) + (tau : ℂ) * I) 4,
          ‖g z‖ ≤ (Ce * (X : ℝ) ^ Qe) /
            ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a)) ∧
        ((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a) ≤
          ‖g ((4 : ℂ) + (tau : ℂ) * I)‖ := by
  obtain ⟨Ce0, Qe, hCe0, henv⟩ := exists_norm_inghamDetector_horizontalTube_le
  obtain ⟨Cj, Qj, hCj, hcount⟩ :=
    exists_inghamDetector_horizontalTube_zeroMass_le_log
  let Ce : ℝ := Ce0 + 1
  have hCe : 1 ≤ Ce := by dsimp only [Ce]; linarith
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  let c0 : ℂ := (4 : ℂ) + (tau : ℂ) * I
  have hcenter := one_half_le_norm_inghamDetector_four hX htlow
  have hneSome : ∃ z : ℂ, inghamDetector X z ≠ 0 := by
    refine ⟨c0, ?_⟩
    exact norm_ne_zero_iff.mp (ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcenter))
  have hnz : ∀ a : ℂ, ¬ ∀ᶠ z in nhds a, inghamDetector X z = 0 := by
    intro a hevent
    exact (inghamDetector_order_ne_top_of_exists_ne_zero X a hneSome)
      (analyticOrderAt_eq_top.mpr hevent)
  have hsphere : ∀ z ∈ sphere c0 4,
      ‖inghamDetector X z‖ ≤ Ce * (X : ℝ) ^ Qe := by
    intro z hz
    have h0 := henv hX htlow hthigh z (sphere_subset_closedBall hz)
    exact h0.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [Ce]; linarith) (by positivity))
  have hmass : ((∑ᶠ u, MeromorphicOn.divisor (inghamDetector X)
      (closedBall c0 (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤
      inghamDetectorTubeJensenBound Cj Qj X := by
    simpa only [c0, inghamDetectorTubeJensenBound] using
      hcount hX htlow hthigh
  simpa only [c0] using exists_tube_factor_data
    (inghamDetector_analyticOnNhd_univ X) hnz hsphere hcenter hmass

private theorem horizontal_segment_mem_tube
    {x T tau : ℝ} (hx : x ∈ Icc (699 / 1000 : ℝ) 4)
    (hT : |T - tau| ≤ 1 / 2) :
    (x : ℂ) + (T : ℂ) * I ∈
      closedBall ((4 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ) := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * I
  let c0 : ℂ := (4 : ℂ) + (tau : ℂ) * I
  have hre : (z - c0).re = x - 4 := by simp [z, c0]
  have him : (z - c0).im = T - tau := by simp [z, c0]
  have hxabs : |x - 4| ≤ 3301 / 1000 := by
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  have hsquares : ‖z - c0‖ ^ 2 = (x - 4) ^ 2 + (T - tau) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hxSq : (x - 4) ^ 2 ≤ (3301 / 1000 : ℝ) ^ 2 :=
    by
      have h := (sq_le_sq₀ (abs_nonneg (x - 4))
        (by norm_num : (0 : ℝ) ≤ 3301 / 1000)).2 hxabs
      simpa only [sq_abs] using h
  have hTSq : (T - tau) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 :=
    by
      have h := (sq_le_sq₀ (abs_nonneg (T - tau))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hT
      simpa only [sq_abs] using h
  have hnorm : ‖z - c0‖ ≤ (15 : ℝ) / 4 := by
    have hn := norm_nonneg (z - c0)
    nlinarith
  simpa only [z, c0, mem_closedBall, dist_eq_norm] using hnorm

private theorem horizontal_segment_norm_le_seventeen_fifths
    {x T tau : ℝ} (hx : x ∈ Icc (699 / 1000 : ℝ) 4)
    (hT : |T - tau| ≤ 1 / 2) :
    ‖((x : ℂ) + (T : ℂ) * I) - ((4 : ℂ) + (tau : ℂ) * I)‖ ≤
      (17 : ℝ) / 5 := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * I
  let c0 : ℂ := (4 : ℂ) + (tau : ℂ) * I
  have hre : (z - c0).re = x - 4 := by simp [z, c0]
  have him : (z - c0).im = T - tau := by simp [z, c0]
  have hxabs : |x - 4| ≤ 3301 / 1000 := by
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  have hsquares : ‖z - c0‖ ^ 2 = (x - 4) ^ 2 + (T - tau) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hxSq : (x - 4) ^ 2 ≤ (3301 / 1000 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (x - 4))
      (by norm_num : (0 : ℝ) ≤ 3301 / 1000)).2 hxabs
    simpa only [sq_abs] using h
  have hTSq : (T - tau) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (T - tau))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hT
    simpa only [sq_abs] using h
  have hn := norm_nonneg (z - c0)
  dsimp only [z, c0] at hsquares hn ⊢
  nlinarith

noncomputable def inghamDetectorHorizontalLogDerivBound
    (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj X N : ℕ) : ℝ :=
  let L := inghamDetectorTubeJensenBound Cj Qj X
  let delta := (4 * (L + 1))⁻¹
  let Mf := Ce * (X : ℝ) ^ Qe
  (N : ℝ) / delta +
    2 * (Real.log
      (((Mf / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N))) + 1) *
      ((7 : ℝ) / 2) /
      ((15 : ℝ) / 4 - (7 : ℝ) / 2) /
      ((7 : ℝ) / 2 - (17 : ℝ) / 5)

noncomputable def inghamDetectorTubeJensenSlope (C : ℝ) (Q : ℕ) : ℝ :=
  (Real.log (2 * C) + (Q : ℝ)) / Real.log ((16 : ℝ) / 15)

noncomputable def inghamDetectorHorizontalPolylogConstant
    (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ) : ℝ :=
  let A := inghamDetectorTubeJensenSlope Cj Qj
  let E := Real.log (2 * Ce) + (Qe : ℝ) + A * Real.log 15
  4 * A * (A + 1) + 280 * (E + 1)

theorem inghamDetectorHorizontalLogDerivBound_le_polylog
    {Ce Cj : ℝ} {Qe Qj X N : ℕ}
    (hCe : 1 ≤ Ce) (hCj : 1 ≤ Cj) (hX : 1 ≤ X)
    (hNL : (N : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X) :
    inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N ≤
      inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj *
        (1 + Real.log X) ^ 2 := by
  let u : ℝ := 1 + Real.log X
  let L : ℝ := inghamDetectorTubeJensenBound Cj Qj X
  let A : ℝ := inghamDetectorTubeJensenSlope Cj Qj
  let E : ℝ := Real.log (2 * Ce) + (Qe : ℝ) + A * Real.log 15
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hXR
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hXR
  have hu1 : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu1
  have hlog2Cj0 : 0 ≤ Real.log (2 * Cj) := by
    apply Real.log_nonneg
    nlinarith
  have hlog2Ce0 : 0 ≤ Real.log (2 * Ce) := by
    apply Real.log_nonneg
    nlinarith
  have hden : 0 < Real.log ((16 : ℝ) / 15) := by
    apply Real.log_pos
    norm_num
  have hA0 : 0 ≤ A := by
    dsimp only [A, inghamDetectorTubeJensenSlope]
    exact div_nonneg (add_nonneg hlog2Cj0 (Nat.cast_nonneg _)) hden.le
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hnumEq : Real.log ((Cj * (X : ℝ) ^ Qj) / ((1 : ℝ) / 2)) =
      Real.log (2 * Cj) + (Qj : ℝ) * Real.log X := by
    rw [div_eq_mul_inv]
    norm_num
    rw [show Cj * (X : ℝ) ^ Qj * 2 = (2 * Cj) * (X : ℝ) ^ Qj by ring,
      Real.log_mul (by positivity) (pow_ne_zero _ hX0.ne'), Real.log_pow]
  have hnumLe : Real.log (2 * Cj) + (Qj : ℝ) * Real.log X ≤
      (Real.log (2 * Cj) + (Qj : ℝ)) * u := by
    have hconst : Real.log (2 * Cj) ≤ Real.log (2 * Cj) * u := by
      nlinarith
    have hq : (Qj : ℝ) * Real.log X ≤ (Qj : ℝ) * u := by
      gcongr
      dsimp only [u]
      linarith
    nlinarith
  have hL : L ≤ A * u := by
    dsimp only [L, inghamDetectorTubeJensenBound,
      A, inghamDetectorTubeJensenSlope]
    norm_num [hnumEq]
    rw [show (Real.log (2 * Cj) + (Qj : ℝ)) /
        Real.log ((16 : ℝ) / 15) * u =
        ((Real.log (2 * Cj) + (Qj : ℝ)) * u) /
          Real.log ((16 : ℝ) / 15) by ring]
    rw [div_le_div_iff_of_pos_right hden]
    exact hnumLe
  have hL0 : 0 ≤ L := by
    dsimp only [L, inghamDetectorTubeJensenBound]
    rw [hnumEq]
    norm_num
    exact div_nonneg
      (add_nonneg hlog2Cj0 (mul_nonneg (Nat.cast_nonneg _) hlogX0)) hden.le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNL' : (N : ℝ) ≤ L := by simpa only [L] using hNL
  have hNA : (N : ℝ) ≤ A * u := hNL'.trans hL
  have hL1 : L + 1 ≤ (A + 1) * u := by
    nlinarith
  have hlog15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
  have hratio :
      ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) =
          2 * Ce * (X : ℝ) ^ Qe * 15 ^ N := by
    have hpow : ((15 : ℝ) / 4) ^ N = ((1 : ℝ) / 4) ^ N * 15 ^ N := by
      rw [← mul_pow]
      congr 1
      ring
    field_simp
    rw [hpow]
  have hlogRatio : Real.log
      ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) =
      Real.log (2 * Ce) + (Qe : ℝ) * Real.log X + (N : ℝ) * Real.log 15 := by
    rw [hratio, Real.log_mul (by positivity)
      (pow_ne_zero _ (by norm_num : (15 : ℝ) ≠ 0)),
      Real.log_mul (by positivity) (pow_ne_zero _ hX0.ne'), Real.log_pow, Real.log_pow]
  have hlogRatioLe : Real.log
      ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) ≤ E * u := by
    rw [hlogRatio]
    have hc : Real.log (2 * Ce) ≤ Real.log (2 * Ce) * u := by nlinarith
    have hq : (Qe : ℝ) * Real.log X ≤ (Qe : ℝ) * u := by
      gcongr
      dsimp only [u]
      linarith
    have hn := mul_le_mul_of_nonneg_right hNA hlog15
    dsimp only [E]
    nlinarith
  have hlogOne : Real.log
      ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) + 1 ≤ (E + 1) * u := by
    nlinarith
  have hfirst : (N : ℝ) * 4 * (L + 1) ≤
      4 * A * (A + 1) * u ^ 2 := by
    calc
      (N : ℝ) * 4 * (L + 1) = 4 * (N : ℝ) * (L + 1) := by ring
      _ ≤ 4 * (A * u) * ((A + 1) * u) := by gcongr
      _ = 4 * A * (A + 1) * u ^ 2 := by ring
  have hsecond : 280 * (Real.log
      ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
        (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) + 1) ≤
      280 * (E + 1) * u ^ 2 := by
    calc
      280 * (Real.log
          ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
            (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) + 1) ≤
          280 * ((E + 1) * u) := by gcongr
      _ ≤ 280 * (E + 1) * u ^ 2 := by
        have huSq : u ≤ u ^ 2 := by nlinarith
        calc
          280 * ((E + 1) * u) = (280 * (E + 1)) * u := by ring
          _ ≤ (280 * (E + 1)) * u ^ 2 :=
            mul_le_mul_of_nonneg_left huSq (by positivity)
          _ = 280 * (E + 1) * u ^ 2 := by ring
  rw [show inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N =
      (N : ℝ) * 4 * (L + 1) +
        280 * (Real.log
          ((Ce * (X : ℝ) ^ Qe / ((1 : ℝ) / 4) ^ N) /
            (((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ N)) + 1) by
    dsimp only [inghamDetectorHorizontalLogDerivBound,
      L, inghamDetectorTubeJensenBound]
    rw [show (N : ℝ) / (4 *
        (Real.log (Cj * (X : ℝ) ^ Qj / ((1 : ℝ) / 2)) /
          Real.log ((4 : ℝ) / (15 / 4 : ℝ)) + 1))⁻¹ =
        (N : ℝ) * 4 *
          (Real.log (Cj * (X : ℝ) ^ Qj / ((1 : ℝ) / 2)) /
            Real.log ((4 : ℝ) / (15 / 4 : ℝ)) + 1) by
      rw [div_eq_mul_inv, inv_inv]
      ring]
    norm_num
    ring]
  change _ ≤ inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj * u ^ 2
  dsimp only [inghamDetectorHorizontalPolylogConstant]
  change _ ≤ (4 * A * (A + 1) + 280 * (E + 1)) * u ^ 2
  nlinarith

theorem exists_inghamDetector_horizontal_logDeriv_control :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 10 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2), ∃ N : ℕ,
        (N : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X ∧
        ∀ x ∈ Icc (699 / 1000 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
            ‖logDeriv (inghamDetector X) ((x : ℂ) + (T : ℂ) * I)‖ ≤
              inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N := by
  classical
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hfactor⟩ :=
    exists_inghamDetector_horizontalTube_factor_data
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  obtain ⟨Z, m, g, hg, hgfree, hZmem, hmpos, hfac, hNL, hgball, hgcenter⟩ :=
    hfactor hX htlow hthigh
  let L : ℝ := inghamDetectorTubeJensenBound Cj Qj X
  let N : ℕ := ∑ a ∈ Z, m a
  let E : Finset ℝ := Z.image Complex.im
  let delta : ℝ := (4 * (L + 1))⁻¹
  have hL0 : 0 ≤ L := by
    exact inghamDetectorTubeJensenBound_nonneg (Q := Qj) hCj
      (show 1 ≤ X by omega)
  have hZN : Z.card ≤ N := by
    calc
      Z.card = ∑ _a ∈ Z, 1 := by simp
      _ ≤ ∑ a ∈ Z, m a := Finset.sum_le_sum fun a ha => hmpos a ha
      _ = N := rfl
  have hEcard : E.card ≤ Z.card := Finset.card_image_le
  have hEL : (E.card : ℝ) ≤ L := by
    have hEN : E.card ≤ N := hEcard.trans hZN
    exact (Nat.cast_le.mpr hEN).trans (by simpa only [N, L] using hNL)
  have hden : 0 < 4 * (L + 1) := by positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hsmall : 2 * E.card * delta < 1 := by
    have hmul : 2 * (E.card : ℝ) ≤ 2 * L := by linarith
    dsimp only [delta]
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨T, hT, hsepE⟩ :=
    exists_Ioo_add_one_separated_from_finset E (tau - 1 / 2) delta hdelta.le hsmall
  have hTband : T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2) := by
    constructor <;> linarith [hT.1, hT.2]
  refine ⟨T, hTband, N, ?_, ?_⟩
  · simpa only [N, L] using hNL
  · intro x hx
    let z : ℂ := (x : ℂ) + (T : ℂ) * I
    let c0 : ℂ := (4 : ℂ) + (tau : ℂ) * I
    have hTtau : |T - tau| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hT.1, hT.2]
    have hzrho : ‖z - c0‖ ≤ (17 : ℝ) / 5 := by
      simpa only [z, c0] using
        horizontal_segment_norm_le_seventeen_fifths hx hTtau
    have hsepZ : ∀ a ∈ Z, delta ≤ ‖z - a‖ := by
      intro a ha
      have haE : a.im ∈ E := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      have hsepIm := hsepE a.im haE
      have himNorm := Complex.abs_im_le_norm (z - a)
      have him : (z - a).im = T - a.im := by simp [z]
      rw [him] at himNorm
      exact hsepIm.trans himNorm
    have hzK : z ∈ closedBall c0 (15 / 4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      exact hzrho.trans (by norm_num)
    have hdetne : inghamDetector X z ≠ 0 :=
      ne_zero_of_factor_data (hfac z)
        (hgfree z (by simpa only [c0] using hzK)) hdelta hsepZ
    have hpoint := norm_logDeriv_le_of_factor_data
      (f := inghamDetector X) (g := g) (c := c0) (z := z)
      (T := Z) (m := m) (Mf := Ce * (X : ℝ) ^ Qe)
      (m0 := (1 : ℝ) / 2) (d := delta)
      hg (by simpa only [c0] using hgfree) hfac
      (by simpa only [c0] using hgball) (by norm_num)
      (by simpa only [c0] using hgcenter) hdelta hsepZ hzrho
    refine ⟨by simpa only [z] using hdetne, ?_⟩
    simpa only [z, N, L, delta, inghamDetectorHorizontalLogDerivBound] using hpoint

theorem exists_inghamDetector_two_horizontal_edges_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc (699 / 1000 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
          ‖logDeriv (inghamDetector X) ((x : ℂ) + (T₁ : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ 2) ∧
        (∀ x ∈ Icc (699 / 1000 : ℝ) 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
          ‖logDeriv (inghamDetector X) ((x : ℂ) + (T₂ : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ 2) := by
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hcontrol⟩ :=
    exists_inghamDetector_horizontal_logDeriv_control
  let C : ℝ := inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj
  let K : ℝ := |C|
  have hK : 0 ≤ K := abs_nonneg C
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  let tau₁ : ℝ := -(X : ℝ) + 1 / 2
  let tau₂ : ℝ := (X : ℝ) - 3 / 2
  have htau₁abs : |tau₁| = (X : ℝ) - 1 / 2 := by
    rw [abs_of_nonpos (by dsimp only [tau₁]; linarith)]
    dsimp only [tau₁]
    ring
  have htau₂abs : |tau₂| = (X : ℝ) - 3 / 2 := by
    rw [abs_of_nonneg (by dsimp only [tau₂]; linarith)]
  have htau₁lo : (X : ℝ) / 2 ≤ |tau₁| := by rw [htau₁abs]; linarith
  have htau₁hi : |tau₁| ≤ 2 * (X : ℝ) := by rw [htau₁abs]; linarith
  have htau₂lo : (X : ℝ) / 2 ≤ |tau₂| := by rw [htau₂abs]; linarith
  have htau₂hi : |tau₂| ≤ 2 * (X : ℝ) := by rw [htau₂abs]; linarith
  obtain ⟨T₁, hT₁, N₁, hN₁, hbound₁⟩ := hcontrol hX htau₁lo htau₁hi
  obtain ⟨T₂, hT₂, N₂, hN₂, hbound₂⟩ := hcontrol hX htau₂lo htau₂hi
  have hT₁' : T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1) := by
    dsimp only [tau₁] at hT₁
    constructor <;> linarith [hT₁.1, hT₁.2]
  have hT₂' : T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1) := by
    dsimp only [tau₂] at hT₂
    constructor <;> linarith [hT₂.1, hT₂.2]
  refine ⟨T₁, hT₁', T₂, hT₂', ?_, ?_⟩
  · intro x hx
    obtain ⟨hne, hraw⟩ := hbound₁ x hx
    refine ⟨hne, hraw.trans ?_⟩
    have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
      (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N₁)
      hCe hCj (show 1 ≤ X by omega) hN₁
    have hCabs : C ≤ K := by dsimp only [K]; exact le_abs_self C
    have hsq : 0 ≤ (1 + Real.log X) ^ 2 := sq_nonneg _
    exact hpoly.trans (by
      simpa only [C] using mul_le_mul_of_nonneg_right hCabs hsq)
  · intro x hx
    obtain ⟨hne, hraw⟩ := hbound₂ x hx
    refine ⟨hne, hraw.trans ?_⟩
    have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
      (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N₂)
      hCe hCj (show 1 ≤ X by omega) hN₂
    have hCabs : C ≤ K := by dsimp only [K]; exact le_abs_self C
    have hsq : 0 ≤ (1 + Real.log X) ^ 2 := sq_nonneg _
    exact hpoly.trans (by
      simpa only [C] using mul_le_mul_of_nonneg_right hCabs hsq)

private theorem eventuallyEq_inghamDetector_factor
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    inghamDetector X =ᶠ[nhds s]
      (fun z => (z - 1) ^ 2 * inghamClassicalDetector X z) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  simpa only [inghamClassicalDetector] using
    inghamDetector_eq_poleCleared X (by simpa using hz)

private theorem inghamClassicalDetector_ne_zero_of_detector_ne_zero
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0) :
    inghamClassicalDetector X s ≠ 0 := by
  intro hh
  have hfactor := inghamDetector_eq_poleCleared X hs
  rw [show 1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2 =
      inghamClassicalDetector X s by rfl, hh, mul_zero] at hfactor
  exact hH hfactor

private theorem logDeriv_congr_of_eventuallyEq
    {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[nhds s] g) :
    logDeriv f s = logDeriv g s := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.self_of_nhds]

private theorem analyticAt_inghamClassicalDetector
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (inghamClassicalDetector X) s := by
  exact analyticAt_const.sub ((((analyticAt_riemannZeta_of_ne_one hs).mul
    (analyticAt_inghamMollifier X s)).sub analyticAt_const).pow 2)

private theorem logDeriv_inghamDetector_eq_gauge_add_classical
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0) :
    logDeriv (inghamDetector X) s =
      logDeriv (fun z : ℂ => (z - 1) ^ 2) s +
        logDeriv (inghamClassicalDetector X) s := by
  rw [logDeriv_congr_of_eventuallyEq
    (eventuallyEq_inghamDetector_factor X hs)]
  exact logDeriv_mul s
    (pow_ne_zero 2 (sub_ne_zero.mpr hs))
    (inghamClassicalDetector_ne_zero_of_detector_ne_zero X hs hH)
    ((analyticAt_id.sub analyticAt_const).pow 2).differentiableAt
    (analyticAt_inghamClassicalDetector X hs).differentiableAt

theorem norm_logDeriv_inghamClassicalDetector_le
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0)
    (him : 1 ≤ |s.im|) :
    ‖logDeriv (inghamClassicalDetector X) s‖ ≤
      ‖logDeriv (inghamDetector X) s‖ + 2 := by
  have hsplit :=
    logDeriv_inghamDetector_eq_gauge_add_classical X hs hH
  have hnormSub : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have himEq : (s - 1).im = s.im := by simp
    rw [himEq] at h
    exact him.trans h
  have hnormPos : 0 < ‖s - 1‖ := lt_of_lt_of_le one_pos hnormSub
  have hgauge : ‖logDeriv (fun z : ℂ => (z - 1) ^ 2) s‖ ≤ 2 := by
    rw [HTGeometry.logDeriv_sub_const_pow 2 hs, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hnormPos]
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * ‖s - 1‖ := mul_le_mul_of_nonneg_left hnormSub (by norm_num)
  have hclassEq : logDeriv (inghamClassicalDetector X) s =
      logDeriv (inghamDetector X) s - logDeriv (fun z : ℂ => (z - 1) ^ 2) s := by
    rw [hsplit]
    ring
  rw [hclassEq]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) hgauge)

end

end RHTower.Sieve
