import GaloisForLFunctions.HTGeometry.DirichletHalfPlaneSignRigidity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Real-analytic postcomposition sign rigidity for ordinary Dirichlet series

A nonconstant analytic scalar germ that is real on a real neighborhood cannot turn a real ordinary
Dirichlet series with a nonzero first nonconstant coefficient into a one-sign half-plane response
on all sufficiently far-right horizontal translates. The analytic germ has a finite positive
vanishing order at the constant coefficient. Quarter-phase twists of the first surviving Dirichlet
mode then force opposite imaginary signs on two fixed horizontal lines.

All results are local at the limiting constant coefficient and unconditional. No analytic
continuation, zero-free hypothesis, or Riemann-hypothesis input is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology LSeries

noncomputable section

theorem natCast_cpow_quarter_phase_pow
    (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k) :
    (((m : ℂ) ^ (((Real.pi / (2 * (k : ℝ) * Real.log m) : ℝ) : ℂ) * Complex.I)) ^ k) =
      Complex.I := by
  rw [← Complex.cpow_mul_nat]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
  rw [← Complex.natCast_log]
  have hlog : Real.log (m : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hm)).ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hprod : Real.log (m : ℝ) * (k : ℝ) ≠ 0 := mul_ne_zero hlog hk0
  have hprodC : (((Real.log (m : ℝ) * (k : ℝ) : ℝ) : ℂ) ≠ 0) :=
    Complex.ofReal_ne_zero.mpr hprod
  have hden : (((Real.log (m : ℝ) : ℝ) : ℂ) * (k : ℂ) ≠ 0) :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hlog) (Nat.cast_ne_zero.mpr hk.ne')
  have hden' : Complex.log (m : ℂ) * (k : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact hden
  have harg :
      ((Real.log (m : ℝ) : ℝ) : ℂ) *
          ((((Real.pi / (2 * (k : ℝ) * Real.log m) : ℝ) : ℂ) * Complex.I) * (k : ℂ)) =
        ((Real.pi : ℂ) / 2) * Complex.I := by
    push_cast
    field_simp [hprodC, hden]
    rw [div_self hden']
  rw [harg]
  exact Complex.exp_pi_div_two_mul_I

theorem natCast_cpow_neg_quarter_phase_pow
    (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k) :
    (((m : ℂ) ^ (-(((Real.pi / (2 * (k : ℝ) * Real.log m) : ℝ) : ℂ) * Complex.I))) ^ k) =
      -Complex.I := by
  rw [← Complex.cpow_mul_nat]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
  rw [← Complex.natCast_log]
  have hlog : Real.log (m : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hm)).ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hprod : Real.log (m : ℝ) * (k : ℝ) ≠ 0 := mul_ne_zero hlog hk0
  have hprodC : (((Real.log (m : ℝ) * (k : ℝ) : ℝ) : ℂ) ≠ 0) :=
    Complex.ofReal_ne_zero.mpr hprod
  have hden : (((Real.log (m : ℝ) : ℝ) : ℂ) * (k : ℂ) ≠ 0) :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hlog) (Nat.cast_ne_zero.mpr hk.ne')
  have hden' : Complex.log (m : ℂ) * (k : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact hden
  have harg :
      ((Real.log (m : ℝ) : ℝ) : ℂ) *
          ((-(((Real.pi / (2 * (k : ℝ) * Real.log m) : ℝ) : ℂ) * Complex.I)) * (k : ℂ)) =
        (-((Real.pi : ℂ) / 2)) * Complex.I := by
    push_cast
    field_simp [hprodC, hden]
    rw [div_self hden']
  rw [harg]
  simpa [neg_div] using Complex.exp_neg_pi_div_two_mul_I

theorem analyticAt_conj_comp_conj_local {H : ℂ → ℂ} {w : ℂ}
    (hH : AnalyticAt ℂ H ((starRingEnd ℂ) w)) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (H ((starRingEnd ℂ) z))) w := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hpull := (Complex.continuous_conj.tendsto w).eventually
    (analyticAt_iff_eventually_differentiableAt.mp hH)
  filter_upwards [hpull] with z hz
  have h := hz.conj_conj
  rwa [Complex.conj_conj] at h

theorem eventually_conj_symmetry_of_analyticAt_eventually_real
    {Phi : ℂ → ℂ} {c : ℂ}
    (hc : (starRingEnd ℂ) c = c)
    (hPhi : AnalyticAt ℂ Phi c)
    (hreal : ∀ᶠ x : ℝ in 𝓝 c.re, (Phi (x : ℂ)).im = 0) :
    ∀ᶠ z : ℂ in 𝓝 c,
      Phi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Phi z) := by
  have hcim : c.im = 0 := by
    have := congrArg Complex.im hc
    simp only [Complex.conj_im] at this
    linarith
  have hcreal : (c.re : ℂ) = c := by
    apply Complex.ext
    · simp
    · simpa using hcim.symm
  let PhiStar : ℂ → ℂ := fun z => (starRingEnd ℂ) (Phi ((starRingEnd ℂ) z))
  have hPhiStar : AnalyticAt ℂ PhiStar c := by
    dsimp [PhiStar]
    apply analyticAt_conj_comp_conj_local
    simpa [hc] using hPhi
  let path : ℝ → ℂ := fun x => c + ((x⁻¹ : ℝ) : ℂ)
  have hpath_nhds : Tendsto path atTop (𝓝 c) := by
    dsimp [path]
    simpa using tendsto_const_nhds.add tendsto_inv_atTop_zero.ofReal
  have hpath_ne : ∀ᶠ x : ℝ in atTop, path x ≠ c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [path]
    intro heq
    have hinv : (x⁻¹ : ℝ) = 0 := by
      have := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith
    exact (inv_ne_zero hx.ne').elim hinv
  have hpath_punct : Tendsto path atTop (𝓝[≠] c) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨hpath_nhds, tendsto_principal.2 (by simpa using hpath_ne)⟩
  have hrealPath : ∀ᶠ x : ℝ in atTop, (Phi (path x)).im = 0 := by
    have hcLim : Tendsto (fun _ : ℝ => c.re) atTop (𝓝 c.re) := tendsto_const_nhds
    have hrealarg : Tendsto (fun x : ℝ => c.re + x⁻¹) atTop (𝓝 c.re) := by
      simpa using hcLim.add tendsto_inv_atTop_zero
    have hpull := hrealarg.eventually hreal
    filter_upwards [hpull] with x hx
    have hpath_eq : path x = ((c.re + x⁻¹ : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [path]
      · simp [path, hcim]
    rw [hpath_eq]
    exact hx
  have heqPath : ∀ᶠ x : ℝ in atTop, Phi (path x) = PhiStar (path x) := by
    filter_upwards [hrealPath] with x hx
    have hvalue : Phi (path x) = (starRingEnd ℂ) (Phi (path x)) := by
      apply Complex.ext
      · simp
      · simp [hx]
    dsimp [PhiStar]
    have hpathreal : (starRingEnd ℂ) (path x) = path x := by
      simp [path, hc]
    rw [hpathreal]
    exact hvalue
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] c, Phi z = PhiStar z := by
    by_contra hnot
    have hnot' : ∀ᶠ z : ℂ in 𝓝[≠] c, Phi z ≠ PhiStar z :=
      (not_frequently.mp hnot)
    have hpull := hpath_punct.eventually hnot'
    obtain ⟨x, hx, hnx⟩ := (heqPath.and hpull).exists
    exact hnx hx
  have heq : ∀ᶠ z : ℂ in 𝓝 c, Phi z = PhiStar z :=
    (hPhi.frequently_eq_iff_eventually_eq hPhiStar).mp hfreq
  filter_upwards [heq] with z hz
  have hzstar := congrArg (starRingEnd ℂ) hz
  dsimp [PhiStar] at hzstar
  simpa only [Complex.conj_conj] using hzstar.symm

theorem exists_real_leading_factor
    {Phi : ℂ → ℂ} {c : ℂ}
    (hc : (starRingEnd ℂ) c = c)
    (hPhi : AnalyticAt ℂ Phi c)
    (hsym : ∀ᶠ z : ℂ in 𝓝 c,
      Phi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Phi z))
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 c, Phi z = Phi c) :
    ∃ (k : ℕ) (g : ℂ → ℂ),
      0 < k ∧ AnalyticAt ℂ g c ∧ g c ≠ 0 ∧ (g c).im = 0 ∧
        ∀ᶠ z : ℂ in 𝓝 c, Phi z - Phi c = (z - c) ^ k * g z := by
  let h : ℂ → ℂ := fun z => Phi z - Phi c
  have hh : AnalyticAt ℂ h c := hPhi.sub analyticAt_const
  have horder : analyticOrderAt h c ≠ ⊤ := by
    intro htop
    apply hnonconst
    have hz := analyticOrderAt_eq_top.mp htop
    filter_upwards [hz] with z hz
    exact sub_eq_zero.mp hz
  let k := analyticOrderNatAt h c
  obtain ⟨g, hg, hgc, hfactor⟩ := hh.analyticOrderAt_ne_top.mp horder
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hself : h c = (c - c) ^ k * g c := by
      simpa [k] using hfactor.self_of_nhds
    have : g c = 0 := by
      simpa [h, hk0] using hself.symm
    exact hgc this
  have hPhic : Phi c = (starRingEnd ℂ) (Phi c) := by
    simpa [hc] using hsym.self_of_nhds
  let gstar : ℂ → ℂ := fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) z))
  have hgstar : AnalyticAt ℂ gstar c := by
    dsimp [gstar]
    apply analyticAt_conj_comp_conj_local
    simpa [hc] using hg
  have hconj : Tendsto (starRingEnd ℂ) (𝓝 c) (𝓝 c) := by
    simpa [hc] using Complex.continuous_conj.tendsto c
  have hfactorConj :
      ∀ᶠ z : ℂ in 𝓝 c,
        h ((starRingEnd ℂ) z) = ((starRingEnd ℂ) z - c) ^ k * g ((starRingEnd ℂ) z) :=
    hconj.eventually hfactor
  have hfactor' :
      ∀ᶠ z : ℂ in 𝓝[≠] c, h z = (z - c) ^ k * g z :=
    hfactor.filter_mono inf_le_left
  have hfactorConj' :
      ∀ᶠ z : ℂ in 𝓝[≠] c,
        h ((starRingEnd ℂ) z) = ((starRingEnd ℂ) z - c) ^ k * g ((starRingEnd ℂ) z) :=
    hfactorConj.filter_mono inf_le_left
  have hsym' :
      ∀ᶠ z : ℂ in 𝓝[≠] c,
        Phi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Phi z) :=
    hsym.filter_mono inf_le_left
  have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] c, gstar z = g z := by
    filter_upwards [hfactor', hfactorConj', hsym', self_mem_nhdsWithin] with
      z hz hzconj hsymz hzne
    have hzne' : z ≠ c := by simpa using hzne
    have hconjne : (starRingEnd ℂ) z ≠ c := by
      intro heq
      have := congrArg (starRingEnd ℂ) heq
      simp only [Complex.conj_conj, hc] at this
      exact hzne' this
    have hbase : ((starRingEnd ℂ) z - c) ^ k ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hconjne)
    have hsymh : h ((starRingEnd ℂ) z) = (starRingEnd ℂ) (h z) := by
      dsimp [h]
      rw [hsymz, map_sub, ← hPhic]
    have hconjfactor :
        (starRingEnd ℂ) (h z) =
          ((starRingEnd ℂ) z - c) ^ k * (starRingEnd ℂ) (g z) := by
      rw [hz]
      simp only [map_mul, map_pow, map_sub, hc]
    have heq :
        ((starRingEnd ℂ) z - c) ^ k * g ((starRingEnd ℂ) z) =
          ((starRingEnd ℂ) z - c) ^ k * (starRingEnd ℂ) (g z) := by
      rw [← hzconj, hsymh, hconjfactor]
    have hgconj : g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z) :=
      mul_left_cancel₀ hbase heq
    dsimp [gstar]
    rw [hgconj, Complex.conj_conj]
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] c, gstar z = g z := hpunct.frequently
  have hevent : ∀ᶠ z : ℂ in 𝓝 c, gstar z = g z :=
    (hgstar.frequently_eq_iff_eventually_eq hg).mp hfreq
  have hgrealEq := hevent.self_of_nhds
  have hgim := congrArg Complex.im hgrealEq
  have hgreal : (g c).im = 0 := by
    dsimp [gstar] at hgim
    simp only [hc] at hgim
    linarith
  refine ⟨k, g, hk, hg, hgc, hgreal, ?_⟩
  filter_upwards [hfactor] with z hz
  simpa [h, k] using hz

theorem lseriesPeeledPowerTwist_eq_LSeries_sub_first
    (f : ℕ → ℝ) (n : ℕ) (a : ℂ) (x : ℝ)
    (hn : 1 ≤ n)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hs : LSeriesSummable (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a)) :
    LSeries
        (GaloisForLFunctions.lseriesPeeledCoeff
          (GaloisForLFunctions.lseriesPowerTwistCoeff
            (fun m => ((f m : ℝ) : ℂ)) a) n)
        (x : ℂ) =
      LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a) - (f 1 : ℂ) := by
  have htwist : LSeriesSummable
      (GaloisForLFunctions.lseriesPowerTwistCoeff (fun m => ((f m : ℝ) : ℂ)) a)
      (x : ℂ) :=
    (GaloisForLFunctions.LSeriesSummable_powerTwist _ _ _).2 hs
  rw [GaloisForLFunctions.LSeries_peeled_eq_sub_sum htwist n,
    GaloisForLFunctions.LSeries_powerTwist]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp [LSeries.term_of_ne_zero, GaloisForLFunctions.lseriesPowerTwistCoeff]
  · intro m hm hm1
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases m.eq_zero_or_pos with rfl | hmpos
    · simp [LSeries.term_zero]
    have hm2 : 2 ≤ m := by omega
    rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hmpos),
      GaloisForLFunctions.lseriesPowerTwistCoeff, hzero m hm2 hmn]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem tendsto_realLSeries_sub_first
    {f : ℕ → ℝ} (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤) :
    Tendsto
      (fun x : ℝ => LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a))
      atTop (𝓝 (f 1 : ℂ)) := by
  have hlim := LSeries.tendsto_atTop
    (GaloisForLFunctions.lseriesPowerTwistCoeff_abscissa_lt_top hf a)
  simpa [GaloisForLFunctions.LSeries_powerTwist,
    GaloisForLFunctions.lseriesPowerTwistCoeff] using hlim

theorem tendsto_rpow_mul_realLSeries_sub_first
    {f : ℕ → ℝ} (n : ℕ) (a : ℂ)
    (hn : 1 ≤ n)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0) :
    Tendsto
      (fun x : ℝ => (((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) *
        (LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a) - (f 1 : ℂ))))
      atTop (𝓝 ((f (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ a)) := by
  have hlim := GaloisForLFunctions.tendsto_cpow_mul_LSeries_peeled
    (f := GaloisForLFunctions.lseriesPowerTwistCoeff
      (fun m => ((f m : ℝ) : ℂ)) a) n
    (GaloisForLFunctions.lseriesPowerTwistCoeff_abscissa_lt_top hf a)
  apply hlim.congr'
  filter_upwards
      [GaloisForLFunctions.eventually_LSeriesSummable_sub_const hf a] with x hs
  rw [lseriesPeeledPowerTwist_eq_LSeries_sub_first f n a x hn hzero hs]
  have hpow : (((n + 1 : ℕ) : ℂ) ^ (x : ℂ)) =
      (((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ)) := by
    symm
    simpa using Complex.ofReal_cpow (Nat.cast_nonneg (n + 1)) x
  rw [hpow]

theorem tendsto_scaled_analytic_postcomposition
    {Phi D g : ℂ → ℂ} {r : ℝ → ℂ} {c q : ℂ} {k : ℕ}
    (hD : Tendsto (fun x : ℝ => D (x : ℂ)) atTop (𝓝 c))
    (hscaled : Tendsto (fun x : ℝ => r x * (D (x : ℂ) - c)) atTop (𝓝 q))
    (hg : AnalyticAt ℂ g c)
    (hfactor : ∀ᶠ z : ℂ in 𝓝 c, Phi z - Phi c = (z - c) ^ k * g z) :
    Tendsto
      (fun x : ℝ => (r x) ^ k * (Phi (D (x : ℂ)) - Phi c))
      atTop (𝓝 (q ^ k * g c)) := by
  have hgD : Tendsto (fun x : ℝ => g (D (x : ℂ))) atTop (𝓝 (g c)) :=
    hg.continuousAt.tendsto.comp hD
  have hlim := hscaled.pow k |>.mul hgD
  apply hlim.congr'
  filter_upwards [hD.eventually hfactor] with x hx
  rw [hx, mul_pow]
  ring

theorem eventually_realAnalyticPostcomp_realLSeries_opposite_signs
    {f : ℕ → ℝ} (n : ℕ)
    (hn : 1 ≤ n)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hfirst : f (n + 1) ≠ 0)
    {Phi : ℂ → ℂ}
    (hPhi : AnalyticAt ℂ Phi (f 1 : ℂ))
    (hsym : ∀ᶠ z : ℂ in 𝓝 (f 1 : ℂ),
      Phi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Phi z))
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 (f 1 : ℂ), Phi z = Phi (f 1 : ℂ)) :
    ∃ τ : ℝ, 0 < τ ∧
      (((∀ᶠ x : ℝ in atTop,
          0 < (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
            ((x : ℂ) - (τ : ℂ) * Complex.I))).im) ∧
        (∀ᶠ x : ℝ in atTop,
          (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
            ((x : ℂ) + (τ : ℂ) * Complex.I))).im < 0)) ∨
       ((∀ᶠ x : ℝ in atTop,
          (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
            ((x : ℂ) - (τ : ℂ) * Complex.I))).im < 0) ∧
        (∀ᶠ x : ℝ in atTop,
          0 < (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
            ((x : ℂ) + (τ : ℂ) * Complex.I))).im))) := by
  have hc : (starRingEnd ℂ) (f 1 : ℂ) = (f 1 : ℂ) := by simp
  obtain ⟨k, g, hk, hg, hgc, hgim, hfactor⟩ :=
    exists_real_leading_factor hc hPhi hsym hnonconst
  let τ : ℝ := Real.pi / (2 * (k : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))
  have hm : 2 ≤ n + 1 := by omega
  have hlog : 0 < Real.log ((n + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact div_pos Real.pi_pos (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk)) hlog)
  let a : ℂ := (τ : ℂ) * Complex.I
  let Dplus : ℂ → ℂ := fun z =>
    LSeries (fun m => ((f m : ℝ) : ℂ)) (z - a)
  let Dminus : ℂ → ℂ := fun z =>
    LSeries (fun m => ((f m : ℝ) : ℂ)) (z + a)
  let r : ℝ → ℂ := fun x => (((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ))
  have hDplus : Tendsto (fun x : ℝ => Dplus (x : ℂ)) atTop (𝓝 (f 1 : ℂ)) := by
    simpa [Dplus] using tendsto_realLSeries_sub_first (f := f) a hf
  have hDminus : Tendsto (fun x : ℝ => Dminus (x : ℂ)) atTop (𝓝 (f 1 : ℂ)) := by
    have h := tendsto_realLSeries_sub_first (f := f) (-a) hf
    simpa [Dminus] using h
  have hscaledPlus :
      Tendsto (fun x : ℝ => r x * (Dplus (x : ℂ) - (f 1 : ℂ))) atTop
        (𝓝 ((f (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ a)) := by
    simpa [r, Dplus] using
      tendsto_rpow_mul_realLSeries_sub_first n a hn hf hzero
  have hscaledMinus :
      Tendsto (fun x : ℝ => r x * (Dminus (x : ℂ) - (f 1 : ℂ))) atTop
        (𝓝 ((f (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-a))) := by
    have h := tendsto_rpow_mul_realLSeries_sub_first n (-a) hn hf hzero
    simpa [r, Dminus] using h
  have hcompPlus := tendsto_scaled_analytic_postcomposition
    (Phi := Phi) hDplus hscaledPlus hg hfactor
  have hcompMinus := tendsto_scaled_analytic_postcomposition
    (Phi := Phi) hDminus hscaledMinus hg hfactor
  let A : ℂ := (f (n + 1) : ℂ) ^ k * g (f 1 : ℂ)
  have hAne : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr hfirst)) hgc
  have hAim : A.im = 0 := by
    dsimp [A]
    have hpoweq : (f (n + 1) : ℂ) ^ k = (((f (n + 1)) ^ k : ℝ) : ℂ) := by
      norm_cast
    have hpowim : ((f (n + 1) : ℂ) ^ k).im = 0 := by
      exact (congrArg Complex.im hpoweq).trans (Complex.ofReal_im _)
    rw [Complex.mul_im]
    rw [hpowim, hgim]
    ring
  have hAre : A.re ≠ 0 := by
    intro hre
    apply hAne
    apply Complex.ext
    · simpa using hre
    · simpa using hAim
  have hphasePlus : (((n + 1 : ℕ) : ℂ) ^ a) ^ k = Complex.I := by
    dsimp [a, τ]
    exact natCast_cpow_quarter_phase_pow (n + 1) k hm hk
  have hphaseMinus : (((n + 1 : ℕ) : ℂ) ^ (-a)) ^ k = -Complex.I := by
    dsimp [a, τ]
    exact natCast_cpow_neg_quarter_phase_pow (n + 1) k hm hk
  have hlimitPlus :
      (((f (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ a) ^ k * g (f 1 : ℂ)).im =
        A.re := by
    rw [mul_pow, hphasePlus]
    dsimp [A]
    rw [Complex.mul_im, Complex.mul_re]
    simp [hgim]
  have hlimitMinus :
      (((f (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-a)) ^ k * g (f 1 : ℂ)).im =
        -A.re := by
    rw [mul_pow, hphaseMinus]
    dsimp [A]
    rw [Complex.mul_im, Complex.mul_re]
    simp [hgim]
  have himPlus := Complex.continuous_im.continuousAt.tendsto.comp hcompPlus
  have himMinus := Complex.continuous_im.continuousAt.tendsto.comp hcompMinus
  rw [hlimitPlus] at himPlus
  rw [hlimitMinus] at himMinus
  have hPhiCim : (Phi (f 1 : ℂ)).im = 0 := by
    have hreal : Phi (f 1 : ℂ) = (starRingEnd ℂ) (Phi (f 1 : ℂ)) := by
      simpa using hsym.self_of_nhds
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith
  have unscale_pos {D : ℂ → ℂ} {x : ℝ}
      (hx : 0 < ((r x) ^ k * (Phi (D (x : ℂ)) - Phi (f 1 : ℂ))).im) :
      0 < (Phi (D (x : ℂ))).im := by
    have hscale : 0 < ((((n + 1 : ℕ) : ℝ) ^ x) ^ k) :=
      pow_pos (Real.rpow_pos_of_pos (by positivity) x) k
    have hrpow : (r x) ^ k =
        ((((((n + 1 : ℕ) : ℝ) ^ x) ^ k : ℝ) : ℂ)) := by simp [r]
    rw [hrpow] at hx
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, hPhiCim, sub_zero, zero_mul, add_zero] at hx
    nlinarith
  have unscale_neg {D : ℂ → ℂ} {x : ℝ}
      (hx : ((r x) ^ k * (Phi (D (x : ℂ)) - Phi (f 1 : ℂ))).im < 0) :
      (Phi (D (x : ℂ))).im < 0 := by
    have hscale : 0 ≤ ((((n + 1 : ℕ) : ℝ) ^ x) ^ k) :=
      (pow_pos (Real.rpow_pos_of_pos (by positivity) x) k).le
    have hrpow : (r x) ^ k =
        ((((((n + 1 : ℕ) : ℝ) ^ x) ^ k : ℝ) : ℂ)) := by simp [r]
    rw [hrpow] at hx
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, hPhiCim, sub_zero, zero_mul, add_zero] at hx
    nlinarith
  refine ⟨τ, hτ, ?_⟩
  rcases lt_or_gt_of_ne hAre with hAneg | hApos
  · right
    constructor
    · filter_upwards [himPlus.eventually (eventually_lt_nhds hAneg)] with x hx
      simpa [Dplus, a] using unscale_neg (D := Dplus) hx
    · filter_upwards [himMinus.eventually (eventually_gt_nhds (neg_pos.mpr hAneg))] with x hx
      simpa [Dminus, a] using unscale_pos (D := Dminus) hx
  · left
    constructor
    · filter_upwards [himPlus.eventually (eventually_gt_nhds hApos)] with x hx
      simpa [Dplus, a] using unscale_pos (D := Dplus) hx
    · filter_upwards [himMinus.eventually (eventually_lt_nhds (neg_lt_zero.mpr hApos))] with x hx
      simpa [Dminus, a] using unscale_neg (D := Dminus) hx

def RealLSeriesPostcompHasOppositeHighLineSigns (f : ℕ → ℝ) (Phi : ℂ → ℂ) : Prop :=
  ∃ τ : ℝ, 0 < τ ∧
    (((∀ᶠ x : ℝ in atTop,
        0 < (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
          ((x : ℂ) - (τ : ℂ) * Complex.I))).im) ∧
      (∀ᶠ x : ℝ in atTop,
        (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
          ((x : ℂ) + (τ : ℂ) * Complex.I))).im < 0)) ∨
     ((∀ᶠ x : ℝ in atTop,
        (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
          ((x : ℂ) - (τ : ℂ) * Complex.I))).im < 0) ∧
      (∀ᶠ x : ℝ in atTop,
        0 < (Phi (LSeries (fun m => ((f m : ℝ) : ℂ))
          ((x : ℂ) + (τ : ℂ) * Complex.I))).im)))

theorem realLSeriesPostcomp_hasOppositeHighLineSigns_of_eventually_real
    {f : ℕ → ℝ} (n : ℕ)
    (hn : 1 ≤ n)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hfirst : f (n + 1) ≠ 0)
    {Phi : ℂ → ℂ}
    (hPhi : AnalyticAt ℂ Phi (f 1 : ℂ))
    (hreal : ∀ᶠ x : ℝ in 𝓝 (f 1), (Phi (x : ℂ)).im = 0)
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 (f 1 : ℂ), Phi z = Phi (f 1 : ℂ)) :
    RealLSeriesPostcompHasOppositeHighLineSigns f Phi := by
  have hc : (starRingEnd ℂ) (f 1 : ℂ) = (f 1 : ℂ) := by simp
  have hreal' : ∀ᶠ x : ℝ in 𝓝 ((f 1 : ℂ).re), (Phi (x : ℂ)).im = 0 := by
    simpa using hreal
  have hsym := eventually_conj_symmetry_of_analyticAt_eventually_real hc hPhi hreal'
  simpa [RealLSeriesPostcompHasOppositeHighLineSigns] using
    eventually_realAnalyticPostcomp_realLSeries_opposite_signs n hn hf hzero hfirst
      hPhi hsym hnonconst

end

end GaloisForLFunctions
