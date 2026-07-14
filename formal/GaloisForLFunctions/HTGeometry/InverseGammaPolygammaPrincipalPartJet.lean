import GaloisForLFunctions.HTGeometry.InverseGammaPolygammaTowerLaws
import GaloisForLFunctions.HTGeometry.PolygammaShift
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor
import Mathlib.Analysis.Analytic.Order


/-!
# Complete inverse-Gamma polygamma principal-part jets

This module promotes the complete principal-part power law at inverse-Gamma poles.  It builds
the removable residue germ, identifies every pole grade with a power of that germ, computes the
first subleading coefficient and its order-independent curvature ratio, and constructs the
analytic inverse-branch interpolation together with its reciprocal-integer samples and exact
analytic-remainder asymptotic expansion.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable def polygammaRegularGerm (q m : ℕ) (u : ℂ) : ℂ :=
  iteratedDeriv q Complex.digamma (u + 1) -
    ∑ i ∈ Finset.range m,
      (-1 : ℂ) ^ q * (q.factorial : ℂ) /
        (u - (m : ℂ) + (i : ℂ)) ^ (q + 1)

theorem analyticAt_polygammaRegularGerm (q m : ℕ) :
    AnalyticAt ℂ (polygammaRegularGerm q m) 0 := by
  have hpolesOne : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have hpsi : (fun w : ℂ => deriv Complex.Gamma w / Complex.Gamma w) =
      Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  have hjet : AnalyticAt ℂ (iteratedDeriv q Complex.digamma) 1 := by
    rw [← hpsi]
    exact analyticAt_iteratedDeriv_logDeriv q 1 hpolesOne
  have hshift : AnalyticAt ℂ
      (fun u : ℂ => iteratedDeriv q Complex.digamma (u + 1)) 0 := by
    have hinner : AnalyticAt ℂ (fun u : ℂ => u + 1) 0 := by fun_prop
    have hjet' : AnalyticAt ℂ (iteratedDeriv q Complex.digamma)
        ((fun u : ℂ => u + 1) 0) := by
      simpa using hjet
    have hc := AnalyticAt.comp (f := fun u : ℂ => u + 1) (x := 0) hjet' hinner
    simpa [Function.comp_def] using hc
  have hsum : AnalyticAt ℂ
      (fun u : ℂ => ∑ i ∈ Finset.range m,
        (-1 : ℂ) ^ q * (q.factorial : ℂ) /
          (u - (m : ℂ) + (i : ℂ)) ^ (q + 1)) 0 := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hden : (0 : ℂ) - (m : ℂ) + (i : ℂ) ≠ 0 := by
      intro h
      have hcast : (i : ℂ) = (m : ℂ) := by linear_combination h
      have : i = m := by exact_mod_cast hcast
      omega
    exact analyticAt_const.div
      ((analyticAt_id.sub analyticAt_const).add analyticAt_const |>.pow (q + 1))
      (pow_ne_zero _ hden)
  exact hshift.sub hsum

theorem polygamma_eq_singular_add_regular (q m : ℕ) :
    (fun u : ℂ => iteratedDeriv q Complex.digamma (-(m : ℂ) + u)) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun u => (-1 : ℂ) ^ (q + 1) * (q.factorial : ℂ) / u ^ (q + 1) +
        polygammaRegularGerm q m u) := by
  have hball : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (by norm_num)
  filter_upwards [inter_mem_nhdsWithin _ hball, self_mem_nhdsWithin] with u hu hune
  have huBall : ‖u‖ < 1 / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hu.2
  have hu0 : u ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hune
  have hoff : ∀ p : ℕ, u - (m : ℂ) ≠ -(p : ℂ) := by
    intro p h
    have hueq : u = (m : ℂ) - (p : ℂ) := by linear_combination h
    by_cases hpm : p = m
    · subst p
      apply hu0
      rw [hueq]
      ring
    · have hnorm : ‖u‖ = |(m : ℝ) - (p : ℝ)| := by
        rw [hueq]
        rw [show (m : ℂ) - (p : ℂ) = (((m : ℝ) - (p : ℝ) : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
      have habs : (1 : ℝ) ≤ |(m : ℝ) - (p : ℝ)| := by
        rcases lt_or_gt_of_ne hpm with hlt | hgt
        · have hdiff : (1 : ℝ) ≤ (m : ℝ) - (p : ℝ) := by
            have hcast : (((p + 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
              exact_mod_cast (Nat.succ_le_iff.mpr hlt)
            push_cast at hcast
            linarith
          rw [abs_of_nonneg (by linarith)]
          exact hdiff
        · have hdiff : (1 : ℝ) ≤ (p : ℝ) - (m : ℝ) := by
            have hcast : (((m + 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.succ_le_iff.mpr hgt)
            push_cast at hcast
            linarith
          rw [abs_of_nonpos (by linarith)]
          linarith
      rw [hnorm] at huBall
      linarith
  have hshift := HTGeometry.iteratedDeriv_digamma_add_nat q (u - (m : ℂ)) hoff (m + 1)
  simp only [polygammaRegularGerm]
  rw [show u - (m : ℂ) + (m + 1 : ℕ) = u + 1 by push_cast; ring] at hshift
  rw [Finset.sum_range_succ] at hshift
  have hlast : u - (m : ℂ) + (m : ℂ) = u := by ring
  rw [hlast] at hshift
  rw [show -(m : ℂ) + u = u - (m : ℂ) by ring]
  linear_combination -hshift

theorem exists_inverseGammaResidueGerm
    {z₀ d : ℂ} {m : ℕ} (hm : 0 < m)
    (hGamma : Complex.Gamma z₀ = -(m : ℂ))
    (hGamma' : HasDerivAt Complex.Gamma d z₀) (hd : d ≠ 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0 = -1 / d ∧
      deriv R 0 = iteratedDeriv 2 Complex.Gamma z₀ / (2 * d ^ 2) ∧
      (fun t : ℂ => R t) =ᶠ[nhdsWithin 0 {0}ᶜ]
        (fun t => -t / (Complex.Gamma (z₀ + t) + (m : ℂ))) := by
  have hoff : ∀ p : ℕ, z₀ ≠ -(p : ℂ) := by
    intro p hp
    rw [hp, Complex.Gamma_neg_nat_eq_zero] at hGamma
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    exact hm0 (by linear_combination hGamma)
  let u : ℂ → ℂ := fun t => Complex.Gamma (z₀ + t) + (m : ℂ)
  have huAn : AnalyticAt ℂ u 0 := by
    have hinner : AnalyticAt ℂ (fun t : ℂ => z₀ + t) 0 := by fun_prop
    have hG : AnalyticAt ℂ Complex.Gamma ((fun t : ℂ => z₀ + t) 0) := by
      simpa using analyticAt_Gamma z₀ hoff
    exact (hG.comp hinner).add analyticAt_const
  have hu0 : u 0 = 0 := by
    simp [u, hGamma]
  have huDer : HasDerivAt u d 0 := by
    have hinner : HasDerivAt (fun t : ℂ => z₀ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add z₀
    have hGamma'' : HasDerivAt Complex.Gamma d (z₀ + (0 : ℂ)) := by
      simpa using hGamma'
    simpa [u] using (hGamma''.comp 0 hinner).add_const (m : ℂ)
  obtain ⟨V, hVAn, hUV⟩ := huAn.exists_eventuallyEq_sum_add_pow_mul 1
  have hUV' : u =ᶠ[nhds 0] (fun t : ℂ => t * V t) := by
    filter_upwards [hUV] with t ht
    rw [ht]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, hu0]
  have hV0 : V 0 = d := by
    have hprod : HasDerivAt (fun t : ℂ => t * V t) (V 0) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul hVAn.differentiableAt.hasDerivAt
    have hprodD : HasDerivAt (fun t : ℂ => t * V t) d 0 :=
      hUV'.hasDerivAt_iff.mp huDer
    exact hprod.unique hprodD
  have hu2 : iteratedDeriv 2 u 0 = iteratedDeriv 2 Complex.Gamma z₀ := by
    have hGshift : AnalyticAt ℂ (fun t : ℂ => Complex.Gamma (z₀ + t)) 0 := by
      have hinner : AnalyticAt ℂ (fun t : ℂ => z₀ + t) 0 := by fun_prop
      have hG : AnalyticAt ℂ Complex.Gamma ((fun t : ℂ => z₀ + t) 0) := by
        simpa using analyticAt_Gamma z₀ hoff
      exact hG.comp hinner
    change iteratedDeriv 2
      (fun t : ℂ => Complex.Gamma (z₀ + t) + (m : ℂ)) 0 = _
    change iteratedDeriv 2
      ((fun t : ℂ => Complex.Gamma (z₀ + t)) + (fun _ : ℂ => (m : ℂ))) 0 = _
    rw [iteratedDeriv_add (hGshift.contDiffAt.of_le le_top) contDiffAt_const]
    simp only [iteratedDeriv_const]
    rw [congrFun (iteratedDeriv_comp_const_add 2 Complex.Gamma z₀) 0]
    simp
  have hprod2 : iteratedDeriv 2 (fun t : ℂ => t * V t) 0 = 2 * deriv V 0 := by
    change iteratedDeriv 2 ((id : ℂ → ℂ) * V) 0 = _
    rw [iteratedDeriv_mul contDiffAt_id (hVAn.contDiffAt.of_le le_top)]
    have hid : iteratedDeriv 2 (id : ℂ → ℂ) 0 = 0 := by
      rw [show 2 = 0 + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
      simp
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_zero,
      iteratedDeriv_one, hid]
  have hVder : deriv V 0 = iteratedDeriv 2 Complex.Gamma z₀ / 2 := by
    have hEq2 := hUV'.iteratedDeriv_eq 2
    rw [hu2, hprod2] at hEq2
    rw [hEq2]
    ring
  let R : ℂ → ℂ := fun t => -1 / V t
  have hRAn : AnalyticAt ℂ R 0 := by
    exact analyticAt_const.neg.div hVAn (hV0.trans_ne hd)
  have hRder : deriv R 0 = iteratedDeriv 2 Complex.Gamma z₀ / (2 * d ^ 2) := by
    have hVhas := hVAn.differentiableAt.hasDerivAt
    have hRhas : HasDerivAt R (deriv V 0 / (V 0) ^ 2) 0 := by
      have h := (hVhas.inv (hV0.trans_ne hd)).neg
      have hfun : R = -V⁻¹ := by
        funext t
        simp [R, div_eq_mul_inv]
      rw [hfun]
      convert h using 1
      ring
    rw [hRhas.deriv, hVder, hV0]
    ring
  refine ⟨R, hRAn, by simp [R, hV0], hRder, ?_⟩
  have hVne : ∀ᶠ t in nhds 0, V t ≠ 0 := hVAn.continuousAt.eventually_ne (hV0.trans_ne hd)
  filter_upwards [hUV'.filter_mono nhdsWithin_le_nhds,
    hVne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hut hvt ht0
  have ht : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0
  change R t = -t / u t
  rw [hut]
  simp only [R]
  field_simp [ht, hvt]

theorem inverseGamma_polygamma_completePrincipalPartJet
    (q : ℕ) {z₀ d : ℂ} {m : ℕ} (hm : 0 < m)
    (hGamma : Complex.Gamma z₀ = -(m : ℂ))
    (hGamma' : HasDerivAt Complex.Gamma d z₀) (hd : d ≠ 0) :
    ∃ R A : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧ R 0 = -1 / d ∧
      deriv R 0 = iteratedDeriv 2 Complex.Gamma z₀ / (2 * d ^ 2) ∧
      AnalyticAt ℂ A 0 ∧
      (fun t : ℂ => t ^ (q + 1) *
          iteratedDeriv q Complex.digamma (Complex.Gamma (z₀ + t))) =ᶠ[nhdsWithin 0 {0}ᶜ]
        (fun t => (q.factorial : ℂ) * R t ^ (q + 1) + t ^ (q + 1) * A t) := by
  obtain ⟨R, hRAn, hR0, hRder, hR⟩ :=
    exists_inverseGammaResidueGerm hm hGamma hGamma' hd
  let u : ℂ → ℂ := fun t => Complex.Gamma (z₀ + t) + (m : ℂ)
  have hoff : ∀ p : ℕ, z₀ ≠ -(p : ℂ) := by
    intro p hp
    rw [hp, Complex.Gamma_neg_nat_eq_zero] at hGamma
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    exact hm0 (by linear_combination hGamma)
  have huAn : AnalyticAt ℂ u 0 := by
    have hinner : AnalyticAt ℂ (fun t : ℂ => z₀ + t) 0 := by fun_prop
    have hG : AnalyticAt ℂ Complex.Gamma ((fun t : ℂ => z₀ + t) 0) := by
      simpa using analyticAt_Gamma z₀ hoff
    exact (hG.comp hinner).add analyticAt_const
  have hu0 : u 0 = 0 := by simp [u, hGamma]
  have huDer : HasDerivAt u d 0 := by
    have hinner : HasDerivAt (fun t : ℂ => z₀ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add z₀
    have hGamma'' : HasDerivAt Complex.Gamma d (z₀ + (0 : ℂ)) := by
      simpa using hGamma'
    simpa [u] using (hGamma''.comp 0 hinner).add_const (m : ℂ)
  let A : ℂ → ℂ := fun t => polygammaRegularGerm q m (u t)
  have hAAn : AnalyticAt ℂ A 0 := by
    have hreg : AnalyticAt ℂ (polygammaRegularGerm q m) (u 0) := by
      rw [hu0]
      exact analyticAt_polygammaRegularGerm q m
    exact hreg.comp huAn
  refine ⟨R, A, hRAn, hR0, hRder, hAAn, ?_⟩
  have hutend := huDer.tendsto_nhdsNE hd
  rw [hu0] at hutend
  have houter := (polygamma_eq_singular_add_regular q m).comp_tendsto hutend
  filter_upwards [houter, hR] with t hout hRt
  have hut : -(m : ℂ) + u t = Complex.Gamma (z₀ + t) := by simp [u]
  simp only [Function.comp_apply] at hout
  rw [hut] at hout
  change t ^ (q + 1) * iteratedDeriv q Complex.digamma (Complex.Gamma (z₀ + t)) =
    (q.factorial : ℂ) * R t ^ (q + 1) + t ^ (q + 1) * A t
  rw [hout]
  change R t = -t / u t at hRt
  rw [hRt]
  simp only [A]
  have hpow : (-t / u t) ^ (q + 1) =
      (-1 : ℂ) ^ (q + 1) * t ^ (q + 1) / u t ^ (q + 1) := by
    rw [div_pow, neg_pow]
  rw [hpow]
  ring

theorem principalPartJetExtension_deriv_zero
    {q : ℕ} (hq : 1 ≤ q) {R A : ℂ → ℂ} {d e : ℂ} (hd : d ≠ 0)
    (hRAn : AnalyticAt ℂ R 0) (hR0 : R 0 = -1 / d)
    (hRder : deriv R 0 = e / (2 * d ^ 2)) (hAAn : AnalyticAt ℂ A 0) :
    deriv (fun t : ℂ => (q.factorial : ℂ) * R t ^ (q + 1) +
      t ^ (q + 1) * A t) 0 =
        ((q + 1).factorial : ℂ) / 2 * e * (-1 / d) ^ (q + 2) := by
  have hRhas : HasDerivAt R (deriv R 0) 0 := hRAn.differentiableAt.hasDerivAt
  have hfirst : HasDerivAt
      (fun t : ℂ => (q.factorial : ℂ) * R t ^ (q + 1))
      ((q.factorial : ℂ) * ((q + 1 : ℕ) : ℂ) * R 0 ^ q * deriv R 0) 0 := by
    have h := (hRhas.pow (q + 1)).const_mul (q.factorial : ℂ)
    convert h using 1
    rw [Nat.add_sub_cancel]
    ring
  have hq0 : q ≠ 0 := by omega
  have htpow : HasDerivAt (fun t : ℂ => t ^ (q + 1)) 0 0 := by
    convert hasDerivAt_pow (q + 1) (0 : ℂ) using 1
    simp [hq0]
  have hsecond : HasDerivAt (fun t : ℂ => t ^ (q + 1) * A t) 0 0 := by
    convert htpow.mul hAAn.differentiableAt.hasDerivAt using 1
    ring
  have hsum := hfirst.add hsecond
  have hfun : (fun t : ℂ => (q.factorial : ℂ) * R t ^ (q + 1) +
      t ^ (q + 1) * A t) =
      (fun t : ℂ => (q.factorial : ℂ) * R t ^ (q + 1)) +
        (fun t : ℂ => t ^ (q + 1) * A t) := rfl
  rw [hfun, hsum.deriv, hR0, hRder, Nat.factorial_succ]
  push_cast
  have hrhoSq : (-1 / d : ℂ) ^ 2 = 1 / d ^ 2 := by
    field_simp [hd]
  rw [show q + 2 = q + 2 by rfl, pow_add, hrhoSq]
  field_simp [hd]
  ring

/-- The first subleading Laurent coefficient in the inverse-Gamma polygamma tower. -/
noncomputable def polygammaTowerFirstSubleadingCoeff (d e : ℂ) (q : ℕ) : ℂ :=
  ((q + 1).factorial : ℂ) / 2 * e * (-1 / d) ^ (q + 2)

/-- The first subleading coefficient is the derivative of the analytic extension supplied by the
complete principal-part jet law. -/
theorem principalPartJetExtension_deriv_zero_eq_firstSubleadingCoeff
    {q : ℕ} (hq : 1 ≤ q) {R A : ℂ → ℂ} {d e : ℂ} (hd : d ≠ 0)
    (hRAn : AnalyticAt ℂ R 0) (hR0 : R 0 = -1 / d)
    (hRder : deriv R 0 = e / (2 * d ^ 2)) (hAAn : AnalyticAt ℂ A 0) :
    deriv (fun t : ℂ => (q.factorial : ℂ) * R t ^ (q + 1) +
      t ^ (q + 1) * A t) 0 = polygammaTowerFirstSubleadingCoeff d e q := by
  exact principalPartJetExtension_deriv_zero hq hd hRAn hR0 hRder hAAn

/-- The normalized first subleading pole grade is independent of the outer derivative order. -/
theorem polygammaTowerFirstSubleadingCoeff_ratio
    {d e : ℂ} (hd : d ≠ 0) (q : ℕ) :
    polygammaTowerFirstSubleadingCoeff d e q /
        (((q + 1 : ℕ) : ℂ) * polygammaTowerCoeff d q) = -e / (2 * d) := by
  have hfac : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero q
  have hq1 : ((q + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero q
  have hrho : (-1 / d : ℂ) ≠ 0 := div_ne_zero (by norm_num) hd
  have hden : (((q + 1 : ℕ) : ℂ) * polygammaTowerCoeff d q) ≠ 0 := by
    exact mul_ne_zero hq1 (mul_ne_zero hfac (pow_ne_zero (q + 1) hrho))
  apply (div_eq_iff hden).2
  simp only [polygammaTowerFirstSubleadingCoeff, polygammaTowerCoeff,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
  field_simp [hd, hfac, hq1]

/-- The analytic residue interpolation attached to a reciprocal-Gamma pole branch. -/
noncomputable def inverseGammaBranchResidueInterpolation {n : ℕ}
    (zn : ReciprocalGammaPoleBranch n) (x : ℂ) : ℂ :=
  -(x ^ 2) * deriv zn x

theorem analyticAt_inverseGammaBranchResidueInterpolation {n : ℕ}
    (zn : ReciprocalGammaPoleBranch n) :
    AnalyticAt ℂ (inverseGammaBranchResidueInterpolation zn) 0 := by
  exact (analyticAt_id.pow 2).neg.mul zn.analyticAt_zero.deriv

theorem ReciprocalGammaPoleBranch.gamma_value_on_punctured_neighborhood
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    (fun x : ℂ => Complex.Gamma (zn x)) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun x => -x⁻¹) := by
  filter_upwards [zn.right_inverse.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hmem
  have hx0 : x ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  calc
    Complex.Gamma (zn x) = ((Complex.Gamma (zn x))⁻¹)⁻¹ := (inv_inv _).symm
    _ = (-x)⁻¹ := congrArg Inv.inv hx
    _ = -x⁻¹ := by rw [inv_neg]

theorem ReciprocalGammaPoleBranch.residueInterpolation_eq_actual
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    ∀ᶠ x in nhdsWithin 0 {0}ᶜ,
      deriv Complex.Gamma (zn x) ≠ 0 ∧
        inverseGammaBranchResidueInterpolation zn x =
          -1 / deriv Complex.Gamma (zn x) := by
  have hcompDer :
      deriv (fun x : ℂ => (Complex.Gamma (zn x))⁻¹) =ᶠ[nhds 0]
        (fun _ : ℂ => -1) := by
    simpa using zn.right_inverse.deriv
  filter_upwards [zn.right_inverse.filter_mono nhdsWithin_le_nhds,
    hcompDer.filter_mono nhdsWithin_le_nhds,
    zn.analyticAt_zero.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hvalue hcompD hznAn hxmem
  have hx : x ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
  have hoff : ∀ p : ℕ, zn x ≠ -(p : ℂ) := by
    intro p hp
    rw [hp, Complex.Gamma_neg_nat_eq_zero, inv_zero] at hvalue
    exact hx (by linear_combination hvalue)
  have hGammaVal : Complex.Gamma (zn x) = -x⁻¹ := by
    calc
      Complex.Gamma (zn x) = ((Complex.Gamma (zn x))⁻¹)⁻¹ := (inv_inv _).symm
      _ = (-x)⁻¹ := congrArg Inv.inv hvalue
      _ = -x⁻¹ := by rw [inv_neg]
  have hcomp : deriv (fun x : ℂ => (Complex.Gamma (zn x))⁻¹) x =
      deriv (fun z : ℂ => (Complex.Gamma z)⁻¹) (zn x) * deriv zn x := by
    exact deriv_comp x Complex.differentiable_one_div_Gamma.differentiableAt
      hznAn.differentiableAt
  rw [hcomp, oneDivGamma_deriv_eq (zn x) hoff] at hcompD
  have hmaster : deriv Complex.Gamma (zn x) * x ^ 2 * deriv zn x = 1 := by
    rw [hGammaVal] at hcompD
    field_simp [hx] at hcompD
    linear_combination -hcompD
  have hd : deriv Complex.Gamma (zn x) ≠ 0 := by
    intro hd
    rw [hd, zero_mul, zero_mul] at hmaster
    norm_num at hmaster
  refine ⟨hd, ?_⟩
  simp only [inverseGammaBranchResidueInterpolation]
  apply (eq_div_iff hd).2
  linear_combination -hmaster

/-- The analytic interpolation of the order-`q` principal-part coefficient. -/
noncomputable def inverseGammaPolygammaCoeffInterpolation {n : ℕ}
    (zn : ReciprocalGammaPoleBranch n) (q : ℕ) (x : ℂ) : ℂ :=
  (q.factorial : ℂ) * inverseGammaBranchResidueInterpolation zn x ^ (q + 1)

theorem analyticAt_inverseGammaPolygammaCoeffInterpolation {n : ℕ}
    (zn : ReciprocalGammaPoleBranch n) (q : ℕ) :
    AnalyticAt ℂ (inverseGammaPolygammaCoeffInterpolation zn q) 0 := by
  exact analyticAt_const.mul
    ((analyticAt_inverseGammaBranchResidueInterpolation zn).pow (q + 1))

theorem ReciprocalGammaPoleBranch.polygammaCoeffInterpolation_eq_towerCoeff
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) (q : ℕ) :
    ∀ᶠ x in nhdsWithin 0 {0}ᶜ,
      inverseGammaPolygammaCoeffInterpolation zn q x =
        polygammaTowerCoeff (deriv Complex.Gamma (zn x)) q := by
  filter_upwards [zn.residueInterpolation_eq_actual] with x hx
  simp only [inverseGammaPolygammaCoeffInterpolation, polygammaTowerCoeff, hx.2]

/-- Reciprocal-integer points sufficiently close to zero sample the actual leading
principal-part limits of the inverse-Gamma polygamma tower. -/
theorem ReciprocalGammaPoleBranch.polygammaCoeffInterpolation_samples
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) (q : ℕ) :
    ∀ᶠ x in nhdsWithin 0 {0}ᶜ, ∀ m : ℕ, 0 < m → x = ((m : ℂ)⁻¹) →
      Tendsto
        (fun z : ℂ => (z - zn x) ^ (q + 1) *
          iteratedDeriv q Complex.digamma (Complex.Gamma z))
        (nhdsWithin (zn x) {zn x}ᶜ)
        (nhds (inverseGammaPolygammaCoeffInterpolation zn q x)) := by
  filter_upwards [zn.gamma_value_on_punctured_neighborhood,
    zn.residueInterpolation_eq_actual] with x hGamma hx
  intro m hm hxm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hGamma' : Complex.Gamma (zn x) = -(m : ℂ) := by
    calc
      Complex.Gamma (zn x) = -x⁻¹ := hGamma
      _ = -(m : ℂ) := by rw [hxm]; simp
  have hder : HasDerivAt Complex.Gamma (deriv Complex.Gamma (zn x)) (zn x) := by
    have hoff : ∀ p : ℕ, zn x ≠ -(p : ℂ) := by
      intro p hp
      rw [hp, Complex.Gamma_neg_nat_eq_zero] at hGamma'
      exact hm0 (by linear_combination hGamma')
    exact (analyticAt_Gamma (zn x) hoff).differentiableAt.hasDerivAt
  have hprincipal := polygamma_comp_Gamma_principalPart q m hGamma' hder hx.1
  simpa [inverseGammaPolygammaCoeffInterpolation, polygammaTowerCoeff, hx.2] using hprincipal

/-- The interpolated residue has the exact cubic expansion claimed by the inverse-branch law,
with an analytic quartic remainder. -/
theorem ReciprocalGammaPoleBranch.residueInterpolation_cubic
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    ∃ S : ℂ → ℂ, AnalyticAt ℂ S 0 ∧
      (fun x : ℂ => inverseGammaBranchResidueInterpolation zn x) =ᶠ[nhds 0]
        (fun x => reciprocalGammaBranchLinearCoeff n * x ^ 2 -
          2 * reciprocalGammaBranchQuadraticCoeff n * x ^ 3 + x ^ 4 * S x) := by
  obtain ⟨R, hRAn, hbranch⟩ := zn.taylor_two_with_cubic_remainder
  let S : ℂ → ℂ := fun x => -3 * R x - x * deriv R x
  have hSAn : AnalyticAt ℂ S 0 := by
    exact analyticAt_const.mul hRAn |>.sub (analyticAt_id.mul hRAn.deriv)
  refine ⟨S, hSAn, ?_⟩
  filter_upwards [hbranch.deriv, hRAn.eventually_analyticAt] with x hder hRx
  have hformula : deriv zn x =
      -reciprocalGammaBranchLinearCoeff n +
        2 * reciprocalGammaBranchQuadraticCoeff n * x +
          3 * x ^ 2 * R x + x ^ 3 * deriv R x := by
    rw [hder]
    have hRder : HasDerivAt R (deriv R x) x := hRx.differentiableAt.hasDerivAt
    have hright : HasDerivAt
        (fun x : ℂ => -(n : ℂ) - reciprocalGammaBranchLinearCoeff n * x +
          reciprocalGammaBranchQuadraticCoeff n * x ^ 2 + x ^ 3 * R x)
        (-reciprocalGammaBranchLinearCoeff n +
          2 * reciprocalGammaBranchQuadraticCoeff n * x +
            3 * x ^ 2 * R x + x ^ 3 * deriv R x) x := by
      convert (((hasDerivAt_const x (-(n : ℂ))).sub
          ((hasDerivAt_id x).const_mul (reciprocalGammaBranchLinearCoeff n))).add
            ((hasDerivAt_pow 2 x).const_mul
              (reciprocalGammaBranchQuadraticCoeff n))).add
                ((hasDerivAt_pow 3 x).mul hRder) using 1
      all_goals ring
    exact hright.deriv
  simp only [inverseGammaBranchResidueInterpolation, S]
  rw [hformula]
  ring

theorem reciprocalGammaBranchLinearCoeff_ne_zero (n : ℕ) :
    reciprocalGammaBranchLinearCoeff n ≠ 0 := by
  exact div_ne_zero (pow_ne_zero n (by norm_num)) (by
    exact_mod_cast Nat.factorial_ne_zero n)

/-- The coefficient interpolation has the exact analytic-remainder form of the card's large-sample
asymptotic expansion.  Substituting `x = 1/m` yields the displayed `m⁻²⁽q+1⁾` law. -/
theorem ReciprocalGammaPoleBranch.polygammaCoeffInterpolation_asymptotic
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) (q : ℕ) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧
      (fun x : ℂ => inverseGammaPolygammaCoeffInterpolation zn q x) =ᶠ[nhds 0]
        (fun x => (q.factorial : ℂ) * reciprocalGammaBranchLinearCoeff n ^ (q + 1) *
          x ^ (2 * (q + 1)) *
            (1 - (2 * ((q + 1 : ℕ) : ℂ) *
                reciprocalGammaBranchQuadraticCoeff n /
                  reciprocalGammaBranchLinearCoeff n) * x + x ^ 2 * U x)) := by
  obtain ⟨S, hSAn, hRho⟩ := zn.residueInterpolation_cubic
  let r : ℂ := reciprocalGammaBranchLinearCoeff n
  let A : ℂ := reciprocalGammaBranchQuadraticCoeff n
  let B : ℂ → ℂ := fun x => r - 2 * A * x + x ^ 2 * S x
  let F : ℂ → ℂ := fun x => B x ^ (q + 1)
  have hBAn : AnalyticAt ℂ B 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).add
      ((analyticAt_id.pow 2).mul hSAn)
  have hFAn : AnalyticAt ℂ F 0 := hBAn.pow (q + 1)
  have hBder : HasDerivAt B (-2 * A) 0 := by
    have hSder : HasDerivAt S (deriv S 0) 0 := hSAn.differentiableAt.hasDerivAt
    convert ((hasDerivAt_const (x := (0 : ℂ)) r).sub
      ((hasDerivAt_id (0 : ℂ)).const_mul (2 * A))).add
        ((hasDerivAt_pow 2 (0 : ℂ)).mul hSder) using 1
    all_goals simp
  have hF0 : F 0 = r ^ (q + 1) := by simp [F, B]
  have hFder : deriv F 0 = ((q + 1 : ℕ) : ℂ) * r ^ q * (-2 * A) := by
    have h := hBder.pow (q + 1)
    have h' : HasDerivAt F
        (((q + 1 : ℕ) : ℂ) * B 0 ^ (q + 1 - 1) * (-2 * A)) 0 := by
      simpa [F] using h
    rw [h'.deriv]
    rw [Nat.add_sub_cancel]
    norm_num [B]
  obtain ⟨T, hTAn, hTaylor⟩ := hFAn.exists_eventuallyEq_sum_add_pow_mul 2
  have hTaylor' : F =ᶠ[nhds 0]
      (fun x => r ^ (q + 1) -
        2 * ((q + 1 : ℕ) : ℂ) * r ^ q * A * x + x ^ 2 * T x) := by
    filter_upwards [hTaylor] with x hx
    rw [hx]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hF0, hFder]
    ring
  have hr : r ≠ 0 := by
    exact reciprocalGammaBranchLinearCoeff_ne_zero n
  let U : ℂ → ℂ := fun x => T x / r ^ (q + 1)
  have hUAn : AnalyticAt ℂ U 0 := by
    exact hTAn.div analyticAt_const (pow_ne_zero (q + 1) hr)
  refine ⟨U, hUAn, ?_⟩
  filter_upwards [hRho, hTaylor'] with x hRhoX hFX
  simp only [inverseGammaPolygammaCoeffInterpolation]
  rw [hRhoX]
  have hbase : r * x ^ 2 - 2 * A * x ^ 3 + x ^ 4 * S x = x ^ 2 * B x := by
    simp only [B]
    ring
  change (q.factorial : ℂ) *
      (r * x ^ 2 - 2 * A * x ^ 3 + x ^ 4 * S x) ^ (q + 1) = _
  rw [hbase, mul_pow]
  rw [show B x ^ (q + 1) = F x by rfl]
  rw [hFX, ← pow_mul]
  change (q.factorial : ℂ) * (x ^ (2 * (q + 1)) *
      (r ^ (q + 1) - 2 * ((q + 1 : ℕ) : ℂ) * r ^ q * A * x + x ^ 2 * T x)) =
    (q.factorial : ℂ) * r ^ (q + 1) * x ^ (2 * (q + 1)) *
      (1 - (2 * ((q + 1 : ℕ) : ℂ) * A / r) * x + x ^ 2 * U x)
  simp only [U]
  field_simp [hr, pow_ne_zero (q + 1) hr]
  ring

end GaloisForLFunctions
