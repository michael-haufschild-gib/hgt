import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import GaloisForLFunctions.RHTower.ChiPhysicalStationaryKernel
import GaloisForLFunctions.RHTower.ZetaChiDualSpatialAmplitude
import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.NumberTheory.AbelSummation

/-!
# Full Gaussian prime rational saddles

Source AP PNT and scaled Abel summation give the smooth prime-band mean in every
fixed reduced residue class. The literal Gaussian cutoff and complete physical
chi kernel then give the rational saddle law, with every prime and both source
remainders retained. At frequency one half the full real integral is eventually
negative. No AP estimate, phase-independence law or cutoff regularity is assumed.
The theorem is for fixed rational frequency; growing-degree mixed moments and
the complete BAG target/cofactor error remain separate open problems.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower

def primeProfileCum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n

theorem scaledAbel_profile_error
    (c : ℕ → ℂ) (f f' : ℝ → ℂ) (ell : ℂ) {N L ε : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2)) (hf1 : f 1 = 0) (hf2 : f 2 = 0)
    (hfb : ∀ x ∈ Icc (1 : ℝ) 2, ‖f' x‖ ≤ L)
    (hA : ∀ x ∈ Icc N (2 * N), ‖primeProfileCum c x - ell * (x : ℂ)‖ ≤ ε * x) :
    ‖(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, f ((n : ℝ) / N) * c n) / (N : ℂ) -
      ell * (∫ x in (1 : ℝ)..2, f x)‖ ≤ 2 * L * ε := by
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  let g : ℝ → ℂ := fun x => f (x / N)
  let gp : ℝ → ℂ := fun x => (N : ℂ)⁻¹ * f' (x / N)
  have hmap : ∀ x ∈ Icc N (2 * N), x / N ∈ Icc (1 : ℝ) 2 := by
    intro x hx
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using hx.1),
      (div_le_iff₀ hN).mpr hx.2⟩
  have hg : ∀ x ∈ Icc N (2 * N), HasDerivAt g (gp x) x := by
    intro x hx
    have hh := (hf (x / N) (hmap x hx)).scomp x ((hasDerivAt_id x).div_const N)
    simpa only [g, gp, one_div, Complex.real_smul, Complex.ofReal_inv, Function.comp_def, id_eq] using hh
  have hgpc : ContinuousOn gp (Icc N (2 * N)) :=
    continuousOn_const.mul (hfc.comp (continuous_id.div_const N).continuousOn hmap)
  have hgp : IntervalIntegrable gp volume N (2 * N) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr hgpc.integrableOn_Icc
  have hderiv : IntegrableOn (deriv g) (Icc N (2 * N)) :=
    hgpc.integrableOn_Icc.congr_fun (fun x hx => (hg x hx).deriv.symm) measurableSet_Icc
  have hg1 : g N = 0 := by dsimp [g]; rw [div_self hN.ne', hf1]
  have hg2 : g (2 * N) = 0 := by dsimp [g]; rw [mul_div_cancel_right₀ _ hN.ne', hf2]
  have hab := sum_mul_eq_sub_sub_integral_mul c hN.le (by linarith : N ≤ 2 * N)
    (fun x hx => (hg x hx).differentiableAt) hderiv
  rw [hg1, hg2, zero_mul, zero_mul, sub_self, zero_sub,
    ← intervalIntegral.integral_of_le (by linarith : N ≤ 2 * N)] at hab
  have hdint : (∫ x in N..2 * N, deriv g x * primeProfileCum c x) =
      ∫ x in N..2 * N, gp x * primeProfileCum c x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change deriv g x * primeProfileCum c x = gp x * primeProfileCum c x
    rw [(hg x (by simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using hx)).deriv]
  change (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) =
    -(∫ x in N..2 * N, deriv g x * primeProfileCum c x) at hab
  rw [hdint] at hab
  have hgA : IntervalIntegrable (fun x => gp x * primeProfileCum c x) volume N (2 * N) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr
    exact integrableOn_mul_sum_Icc c hN.le hgpc.integrableOn_Icc
  have hgl : IntervalIntegrable (fun x => gp x * (ell * (x : ℂ))) volume N (2 * N) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : N ≤ 2 * N)).mpr
      (hgpc.mul (continuous_const.mul Complex.continuous_ofReal).continuousOn).integrableOn_Icc
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (u' := gp) (v := fun x : ℝ => (x : ℂ)) (v' := fun _ => (1 : ℂ))
    (fun x hx => hg x (by simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using hx))
    (fun x _ => Complex.ofRealCLM.hasDerivAt) hgp (intervalIntegrable_const)
  simp only [mul_one, hg1, hg2, zero_mul, sub_self, zero_sub] at hibp
  have hscale : (∫ x in N..2 * N, g x) = (N : ℂ) * ∫ x in (1 : ℝ)..2, f x := by
    dsimp only [g]
    rw [intervalIntegral.integral_comp_div _ hN.ne']
    simp only [div_self hN.ne', mul_div_cancel_right₀ _ hN.ne', Complex.real_smul]
  have hmain : (∫ x in N..2 * N, gp x * (ell * (x : ℂ))) =
      -(ell * (N : ℂ) * ∫ x in (1 : ℝ)..2, f x) := by
    simp_rw [show ∀ x : ℝ, gp x * (ell * (x : ℂ)) = ell * (gp x * (x : ℂ)) by intro x; ring]
    have he : (∫ x in N..2 * N, gp x * (x : ℂ)) =
        -((N : ℂ) * ∫ x in (1 : ℝ)..2, f x) := by
      rw [hscale] at hibp
      linear_combination hibp
    rw [intervalIntegral.integral_const_mul, he]
    ring
  have hdiff : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
      ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x) =
      -(∫ x in N..2 * N, gp x * (primeProfileCum c x - ell * (x : ℂ))) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hgA hgl, hab, hmain]
    ring
  have hb (x : ℝ) (hx : x ∈ Icc N (2 * N)) :
      ‖gp x * (primeProfileCum c x - ell * (x : ℂ))‖ ≤ 2 * L * ε := by
    have hxn : 0 ≤ x := hN.le.trans hx.1
    rw [norm_mul]
    have hgpbound : ‖gp x‖ ≤ L / N := by
      dsimp only [gp]
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hN.le]
      calc
        _ ≤ N⁻¹ * L := mul_le_mul_of_nonneg_left (hfb _ (hmap x hx)) (inv_nonneg.mpr hN.le)
        _ = _ := by ring
    calc
      _ ≤ (L / N) * (ε * x) := mul_le_mul hgpbound (hA x hx) (norm_nonneg _) (by positivity)
      _ ≤ (L / N) * (ε * (2 * N)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hx.2 hε) (by positivity)
      _ = _ := by field_simp
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * L * ε) (fun x hx => hb x (by
      simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using
        (show x ∈ uIcc N (2 * N) from uIoc_subset_uIcc hx)))
  have hwhole : ‖(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
      ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x)‖ ≤ (2 * L * ε) * N := by
    rw [hdiff, norm_neg]
    simpa only [show 2 * N - N = N by ring, abs_of_pos hN] using hint
  have heq : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, f ((n : ℝ) / N) * c n) / (N : ℂ) -
      ell * (∫ x in (1 : ℝ)..2, f x) =
      ((∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, g n * c n) -
        ell * (N : ℂ) * (∫ x in (1 : ℝ)..2, f x)) / (N : ℂ) := by
    dsimp only [g]
    field_simp [hNC]
  rw [heq, norm_div, Complex.norm_of_nonneg hN.le]
  exact (div_le_iff₀ hN).mpr hwhole

private theorem tendsto_scaledAbel_profile
    (c : ℕ → ℂ) (f f' : ℝ → ℂ) (ell : ℂ)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2)) (hf1 : f 1 = 0) (hf2 : f 2 = 0)
    (hlim : Tendsto (fun x : ℝ => primeProfileCum c x / (x : ℂ)) atTop (𝓝 ell)) :
    Tendsto (fun N : ℝ =>
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, f ((n : ℝ) / N) * c n) / (N : ℂ))
      atTop (𝓝 (ell * ∫ x in (1 : ℝ)..2, f x)) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 1 (by norm_num))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε / (2 * L + 1) := div_pos hε (by linarith)
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hlim (ε / (2 * L + 1)) hδ
  refine ⟨max X 1, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) ((le_max_right X 1).trans hN)
  have hA : ∀ x ∈ Icc N (2 * N),
      ‖primeProfileCum c x - ell * (x : ℂ)‖ ≤ (ε / (2 * L + 1)) * x := by
    intro x hx
    have hx0 : 0 < x := hNpos.trans_le hx.1
    have hh := hX x (((le_max_left X 1).trans hN).trans hx.1)
    rw [dist_eq_norm] at hh
    have he : primeProfileCum c x / (x : ℂ) - ell =
        (primeProfileCum c x - ell * (x : ℂ)) / (x : ℂ) := by
      field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']
    rw [he, norm_div, Complex.norm_of_nonneg hx0.le] at hh
    exact ((div_lt_iff₀ hx0).mp hh).le
  rw [dist_eq_norm]
  have hh := scaledAbel_profile_error c f f' ell hNpos hL0 hδ.le hf hfc hf1 hf2 hL hA
  refine hh.trans_lt ?_
  have he : 2 * L * (ε / (2 * L + 1)) = ε - ε / (2 * L + 1) := by field_simp; ring
  rw [he]
  linarith

/-- Prime logarithmic mass in one residue class; no progression estimate is an input. -/
def primeResidueLogCoefficient (q r n : ℕ) : ℂ :=
  if n.Prime ∧ n % q = r then (Real.log n : ℂ) else 0

private theorem primeProfileCum_residue_eq (q r : ℕ) (x : ℝ) :
    primeProfileCum (primeResidueLogCoefficient q r) x =
      ((∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        if p % q = r then Real.log p else 0 : ℝ) : ℂ) := by
  simp only [primeProfileCum, primeResidueLogCoefficient,
    Finset.sum_filter, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime <;> by_cases hr : n % q = r <;> simp [hp, hr]

/-- The source AP prime-number theorem gives each reduced class its exact density. -/
theorem tendsto_primeResidueLog_density {q r : ℕ}
    (hq : 1 ≤ q) (hr : r.Coprime q) (hrq : r < q) :
    Tendsto (fun x : ℝ => primeProfileCum (primeResidueLogCoefficient q r) x / (x : ℂ))
      atTop (𝓝 ((1 / (q.totient : ℝ) : ℝ) : ℂ)) := by
  have hh := (chebyshev_asymptotic_pnt hq hr hrq).div
    (Asymptotics.IsEquivalent.refl (l := atTop) (u := fun x : ℝ => x))
  have hc : (fun x : ℝ => (x / (q.totient : ℝ)) / x) =ᶠ[atTop]
      (fun _ => (1 / (q.totient : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hreal := (hh.congr_right hc).tendsto_const
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  funext x
  dsimp only [Function.comp_apply, Pi.div_apply]
  rw [primeProfileCum_residue_eq, Complex.ofReal_div]

/-- Smooth weighted AP density on a full scaled prime band, derived from the source PNT. -/
theorem tendsto_primeResidueLog_profile {q r : ℕ}
    (hq : 1 ≤ q) (hr : r.Coprime q) (hrq : r < q)
    (f f' : ℝ → ℂ)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2)) (hf1 : f 1 = 0) (hf2 : f 2 = 0) :
    Tendsto (fun N : ℝ =>
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        f ((n : ℝ) / N) * primeResidueLogCoefficient q r n) / (N : ℂ))
      atTop (𝓝 (((1 / (q.totient : ℝ) : ℝ) : ℂ) * ∫ x in (1 : ℝ)..2, f x)) :=
  tendsto_scaledAbel_profile _ _ _ _ hf hfc hf1 hf2 (tendsto_primeResidueLog_density hq hr hrq)

/-- The entire residue-restricted prime band; no phase-dependent subset is selected. -/
def primeResidueBand (q r : ℕ) (N : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun p => p.Prime ∧ p % q = r)

private theorem primeResidueBand_mem {q r p : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (hp : p ∈ primeResidueBand q r N) : p.Prime ∧ N < p ∧ (p : ℝ) ≤ 2 * N := by
  obtain ⟨hpI, hpr, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN, hp2N⟩ := Finset.mem_Ioc.mp hpI
  exact ⟨hpr, (Nat.floor_lt hN).mp hpN, (Nat.le_floor_iff (by linarith)).mp hp2N⟩

private theorem primeResidueBand_card_log_le {q r : ℕ} {N : ℝ} (hN : 1 < N) :
    (primeResidueBand q r N).card * Real.log N ≤ (2 * Real.log 4) * N := by
  let S := primeResidueBand q r N
  have hsub : S ⊆ (Finset.Icc 0 ⌊2 * N⌋₊).filter Nat.Prime := by
    intro p hp
    have hh := primeResidueBand_mem (by linarith : 0 ≤ N) hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      Nat.le_floor hh.2.2⟩, hh.1⟩
  calc
    _ = ∑ _p ∈ S, Real.log N := by simp [S]
    _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum fun p hp =>
      Real.log_le_log (by linarith) (primeResidueBand_mem (by linarith : 0 ≤ N) hp).2.1.le
    _ ≤ Chebyshev.theta (2 * N) := by
      rw [Chebyshev.theta_eq_sum_Icc]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
    _ ≤ _ := by simpa only [mul_assoc, mul_left_comm] using
      Chebyshev.theta_le_log4_mul_x (x := 2 * N) (by linarith)

private theorem norm_primeResidue_profile_unweight_error {q r : ℕ} {N B : ℝ}
    (hN : 1 < N) (hB : 0 ≤ B) (f : ℝ → ℂ)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, ‖f x‖ ≤ B) :
    ‖((Real.log N : ℂ) * ∑ p ∈ primeResidueBand q r N, f ((p : ℝ) / N)) / (N : ℂ) -
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        f ((n : ℝ) / N) * primeResidueLogCoefficient q r n) / (N : ℂ)‖ ≤
      (B * Real.log 2 * (2 * Real.log 4)) / Real.log N := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hsum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      f ((n : ℝ) / N) * primeResidueLogCoefficient q r n) =
      ∑ p ∈ primeResidueBand q r N, f ((p : ℝ) / N) * (Real.log p : ℂ) := by
    simp only [primeResidueBand, Finset.sum_filter, primeResidueLogCoefficient]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp
  rw [hsum, ← sub_div, Finset.mul_sum, ← Finset.sum_sub_distrib, norm_div,
    Complex.norm_of_nonneg hN0.le]
  have hterm (p : ℕ) (hp : p ∈ primeResidueBand q r N) :
      ‖(Real.log N : ℂ) * f ((p : ℝ) / N) - f ((p : ℝ) / N) * (Real.log p : ℂ)‖ ≤
        B * Real.log 2 := by
    have hpp := primeResidueBand_mem hN0.le hp
    have hscale : (p : ℝ) / N ∈ Icc (1 : ℝ) 2 :=
      ⟨(le_div_iff₀ hN0).mpr (by simpa using hpp.2.1.le),
        (div_le_iff₀ hN0).mpr hpp.2.2⟩
    have hloglo : Real.log N ≤ Real.log p := Real.log_le_log hN0 hpp.2.1.le
    have hloghi : Real.log p ≤ Real.log 2 + Real.log N := by
      have hh := Real.log_le_log (hN0.trans hpp.2.1) hpp.2.2
      rwa [Real.log_mul (by norm_num) hN0.ne'] at hh
    have he : (Real.log N : ℂ) * f ((p : ℝ) / N) - f ((p : ℝ) / N) * (Real.log p : ℂ) =
        f ((p : ℝ) / N) * ((Real.log N - Real.log p : ℝ) : ℂ) := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hloglo)]
    exact mul_le_mul (hf _ hscale) (by linarith) (by linarith) hB
  have hnorm := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  simp only [Finset.sum_const, nsmul_eq_mul] at hnorm
  have hc := primeResidueBand_card_log_le (q := q) (r := r) hN
  calc
    _ ≤ ((primeResidueBand q r N).card * (B * Real.log 2)) / N :=
      div_le_div_of_nonneg_right hnorm hN0.le
    _ ≤ _ := by
      apply (div_le_iff₀ hN0).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlog).mpr
      have hh := mul_le_mul_of_nonneg_left hc
        (mul_nonneg hB (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
      convert hh using 1 <;> ring

/-- The logarithmic weight can be removed on a fixed dyadic band without an AP error premise. -/
theorem tendsto_primeResidue_profile {q r : ℕ}
    (hq : 1 ≤ q) (hr : r.Coprime q) (hrq : r < q)
    (f f' : ℝ → ℂ)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2)) (hf1 : f 1 = 0) (hf2 : f 2 = 0) :
    Tendsto (fun N : ℝ => ((Real.log N : ℂ) *
      ∑ p ∈ primeResidueBand q r N, f ((p : ℝ) / N)) / (N : ℂ))
      atTop (𝓝 (((1 / (q.totient : ℝ) : ℝ) : ℂ) * ∫ x in (1 : ℝ)..2, f x)) := by
  have hcont : ContinuousOn f (Icc (1 : ℝ) 2) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (by norm_num))
  have hsmall : Tendsto (fun N : ℝ => (B * Real.log 2 * (2 * Real.log 4)) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
      : Tendsto (fun N : ℝ => (B * Real.log 2 * (2 * Real.log 4)) * (Real.log N)⁻¹) atTop (𝓝 (_ * 0)))
  have herr : Tendsto (fun N : ℝ => ((Real.log N : ℂ) *
      ∑ p ∈ primeResidueBand q r N, f ((p : ℝ) / N)) / (N : ℂ) -
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        f ((n : ℝ) / N) * primeResidueLogCoefficient q r n) / (N : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    exact norm_primeResidue_profile_unweight_error hN hB0 f hB
  have hh := herr.add (tendsto_primeResidueLog_profile hq hr hrq f f' hf hfc hf1 hf2)
  simpa only [sub_add_cancel, zero_add] using hh

/-- Full prime band, with no residue or phase deletion. -/
def primeProfileBand (N : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter Nat.Prime

/-- Every fixed periodic prime weight has its reduced-residue mean on the actual smooth band. -/
theorem tendsto_prime_periodic_profile {q : ℕ} (hq : 1 ≤ q) (w : ℕ → ℂ)
    (f f' : ℝ → ℂ)
    (hf : ∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f' (Icc (1 : ℝ) 2)) (hf1 : f 1 = 0) (hf2 : f 2 = 0) :
    Tendsto (fun N : ℝ => ((Real.log N : ℂ) *
      ∑ p ∈ primeProfileBand N, f ((p : ℝ) / N) * w (p % q)) / (N : ℂ))
      atTop (𝓝 (((∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), w r) /
        (q.totient : ℂ)) * ∫ x in (1 : ℝ)..2, f x)) := by
  let R := (Finset.range q).filter (fun r => r.Coprime q)
  have hsum := tendsto_finsetSum R (fun r hr =>
    (tendsto_primeResidue_profile hq (Finset.mem_filter.mp hr).2
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1) f f' hf hfc hf1 hf2).mul_const (w r))
  have hvalue : (∑ r ∈ R, (((1 / (q.totient : ℝ) : ℝ) : ℂ) *
      ∫ x in (1 : ℝ)..2, f x) * w r) =
      ((∑ r ∈ R, w r) / (q.totient : ℂ)) * ∫ x in (1 : ℝ)..2, f x := by
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [hvalue] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (q : ℝ)] with N hN
  have hN0 : 0 ≤ N := (Nat.cast_nonneg q).trans hN
  have hq0 : 0 < q := by omega
  have hmap : ∀ p ∈ primeProfileBand N, p % q ∈ R := by
    intro p hp
    obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hplo, _⟩ := Finset.mem_Ioc.mp hpI
    have hpN : N < p := (Nat.floor_lt hN0).mp hplo
    have hpq : q < p := by exact_mod_cast hN.trans_lt hpN
    have hcop : p.Coprime q := (hprime.coprime_iff_not_dvd).mpr (fun h =>
      (not_le_of_gt hpq) (Nat.le_of_dvd hq0 h))
    have hmod : (p % q).Coprime q := by
      rwa [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec] at hcop
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq0), hmod⟩
  have hfilter (r : ℕ) : (primeProfileBand N).filter (fun p => p % q = r) =
      primeResidueBand q r N := by
    ext p
    simp only [primeProfileBand, primeResidueBand, Finset.mem_filter, and_assoc]
  have hsplit : (∑ p ∈ primeProfileBand N, f ((p : ℝ) / N) * w (p % q)) =
      ∑ r ∈ R, (∑ p ∈ primeResidueBand q r N, f ((p : ℝ) / N)) * w r := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfilter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2.2]
  rw [hsplit, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  ring

open GaloisForLFunctions.RHTower

/-- The literal Gaussian cutoff, multiplied by the complete physical height window. -/
def primeGaussianProfile (x : ℝ) : ℂ :=
  (bagPhysicalHeightWindow x : ℂ) * smoothAFECutoff x

private theorem primeGaussianProfile_regular :
    (∀ x ∈ Icc (1 : ℝ) 2, HasDerivAt primeGaussianProfile (deriv primeGaussianProfile x) x) ∧
    ContinuousOn (deriv primeGaussianProfile) (Icc (1 : ℝ) 2) ∧
    primeGaussianProfile 1 = 0 ∧ primeGaussianProfile 2 = 0 := by
  have hc : ContDiffOn ℝ 2 primeGaussianProfile (Ioi (0 : ℝ)) :=
    ((Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff).contDiffOn).mul
      contDiffOn_smoothAFECutoff_pos
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hd : ContDiffOn ℝ 1 (deriv primeGaussianProfile) (Ioi (0 : ℝ)) :=
    hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  refine ⟨fun x hx => (hc.differentiableOn (by norm_num)).hasDerivAt
    (Ioi_mem_nhds (hsub hx)), hd.continuousOn.mono hsub, ?_, ?_⟩
  · unfold primeGaussianProfile
    rw [bagPhysicalHeightWindow.zero_of_le_dist (by
      change (1 / 2 : ℝ) ≤ dist 1 (3 / 2)
      norm_num [Real.dist_eq]), Complex.ofReal_zero, zero_mul]
  · unfold primeGaussianProfile
    rw [bagPhysicalHeightWindow.zero_of_le_dist (by
      change (1 / 2 : ℝ) ≤ dist 2 (3 / 2)
      norm_num [Real.dist_eq]), Complex.ofReal_zero, zero_mul]

/-- Exact rational saddle phase, with the numerator and denominator retained. -/
def primeRationalPhase (a q p : ℕ) : ℂ :=
  bourgainOscillation (2 * Real.pi * ((a : ℝ) / q) * p)

/-- The actual rational saddle phase depends only on the residue class. -/
theorem primeRationalPhase_mod (a : ℕ) {q : ℕ} (hq : 0 < q) (p : ℕ) :
    primeRationalPhase a q p = primeRationalPhase a q (p % q) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : 2 * Real.pi * ((a : ℝ) / q) * p =
      2 * Real.pi * ((a : ℝ) / q) * (p % q : ℕ) +
        (a * (p / q) : ℕ) * (2 * Real.pi) := by
    have hp : (p : ℝ) = (p % q : ℕ) + (q : ℝ) * (p / q : ℕ) := by
      exact_mod_cast (Nat.mod_add_div p q).symm
    rw [hp]
    push_cast
    field_simp
  unfold primeRationalPhase bourgainOscillation
  rw [he]
  have heC : I * ((2 * Real.pi * ((a : ℝ) / q) * (p % q : ℕ) +
      (a * (p / q) : ℕ) * (2 * Real.pi) : ℝ) : ℂ) =
      I * ((2 * Real.pi * ((a : ℝ) / q) * (p % q : ℕ) : ℝ) : ℂ) +
        (a * (p / q) : ℕ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
  rw [heC, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The full Gaussian prime band has the reduced-residue rational saddle mean. -/
theorem tendsto_primeGaussian_rational_profile (a : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℝ => ((Real.log N : ℂ) *
      ∑ p ∈ primeProfileBand N, primeGaussianProfile ((p : ℝ) / N) *
        primeRationalPhase a q p) / (N : ℂ)) atTop
      (𝓝 (((∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
        primeRationalPhase a q r) / (q.totient : ℂ)) *
          ∫ x in (1 : ℝ)..2, primeGaussianProfile x)) := by
  obtain ⟨hf, hfc, hf1, hf2⟩ := primeGaussianProfile_regular
  have hh := tendsto_prime_periodic_profile hq (primeRationalPhase a q)
    primeGaussianProfile (deriv primeGaussianProfile) hf hfc hf1 hf2
  apply hh.congr
  intro N
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  rw [primeRationalPhase_mod a (by omega : 0 < q) p]

/-- The entire Gaussian prime band at critical dual amplitude. -/
def primeGaussianChiField (xi N t : ℝ) : ℂ :=
  ∑ p ∈ primeProfileBand N, (smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ)) *
    Complex.exp (((Real.log (xi * p) * t : ℝ) : ℂ) * I)

/-- Literal full physical integral; no residue class or cutoff transition is removed. -/
def primeGaussianChiIntegral (xi N : ℝ) : ℂ :=
  ∫ t in (2 * Real.pi * xi * N)..2 * (2 * Real.pi * xi * N),
    (bagPhysicalHeightWindow (t / (2 * Real.pi * xi * N)) : ℂ) *
      zetaChi (linePt t) * primeGaussianChiField xi N t

private theorem physicalChiStationaryMain_one_prime {xi N p : ℝ}
    (hxi : 0 < xi) (hN : 0 < N) (hp : 0 < p) :
    smoothAFECutoff (p / N) / (Real.sqrt p : ℂ) *
      physicalChiStationaryMain (2 * Real.pi * xi * N) (2 * Real.pi * xi * p) 1 =
      ((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ) * primeGaussianProfile (p / N) *
        bourgainOscillation (2 * Real.pi * xi * p) := by
  have ha : 0 < 2 * Real.pi * xi * p := by positivity
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsp : (Real.sqrt p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hratio : (2 * Real.pi * xi * p) / (2 * Real.pi * xi * N) = p / N := by
    field_simp
  have hamp : (2 * Real.pi * xi * p) *
      Real.sqrt (2 * Real.pi / (2 * Real.pi * xi * p)) =
      2 * Real.pi * Real.sqrt xi * Real.sqrt p := by
    calc
      _ = Real.sqrt ((2 * Real.pi * xi * p) ^ 2 *
          (2 * Real.pi / (2 * Real.pi * xi * p))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
      _ = Real.sqrt ((2 * Real.pi) ^ 2 * xi * p) := by
        congr 1
        field_simp
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) hxi.le),
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi)]
  have hphase : bourgainOscillation (Real.pi / 4) *
      Complex.exp (I * ((2 * Real.pi * xi * p - Real.pi / 4 : ℝ) : ℂ)) =
      bourgainOscillation (2 * Real.pi * xi * p) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold physicalChiStationaryMain
  simp only [zpow_one, Int.cast_one, one_mul, hratio]
  have hampC := congrArg (fun x : ℝ => (x : ℂ)) hamp
  push_cast at hampC
  calc
    _ = (smoothAFECutoff (p / N) / (Real.sqrt p : ℂ)) *
        (bagPhysicalHeightWindow (p / N) : ℂ) *
        (((2 * Real.pi * xi * p : ℝ) : ℂ) *
          (Real.sqrt (2 * Real.pi / (2 * Real.pi * xi * p)) : ℂ)) *
        (bourgainOscillation (Real.pi / 4) *
          Complex.exp (I * ((2 * Real.pi * xi * p - Real.pi / 4 : ℝ) : ℂ))) := by ring
    _ = _ := by
      rw [hphase]
      push_cast
      rw [hampC]
      unfold primeGaussianProfile
      field_simp

theorem physicalChiGradeOne_second_error {T : ℝ} (hT : 0 < T) (Ce : ℝ) :
    (6 / Real.sqrt (1 / (100 * T))) * (52 / T) * Ce =
      (3120 * Ce) / Real.sqrt T := by
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100)]
  have h100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
  rw [h100]
  field_simp
  rw [Real.sq_sqrt hT.le]
  ring

theorem primeProfileBand_mem {N : ℝ} (hN : 0 ≤ N) {p : ℕ}
    (hp : p ∈ primeProfileBand N) : p.Prime ∧ N < p ∧ (p : ℝ) ≤ 2 * N := by
  obtain ⟨hi, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hi
  exact ⟨hprime, (Nat.floor_lt hN).mp hl, (Nat.le_floor_iff (by linarith)).mp hu⟩

private theorem primeProfileBand_card_le {N : ℝ} (hN : 0 ≤ N) :
    ((primeProfileBand N).card : ℝ) ≤ 2 * N := by
  have hc : (primeProfileBand N).card ≤ ⌊2 * N⌋₊ :=
    (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; exact Nat.sub_le _ _)
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by linarith))

/-- The complete stationary error is uniformly summable over the full Gaussian prime band. -/
theorem exists_primeGaussianChi_entry_error {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → 4 ≤ 2 * Real.pi * xi * N →
      ∀ p ∈ primeProfileBand N,
      ‖smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ) *
        (∫ t in (2 * Real.pi * xi * N)..2 * (2 * Real.pi * xi * N),
          (bagPhysicalHeightWindow (t / (2 * Real.pi * xi * N)) : ℂ) *
            (zetaChi (linePt t) * Complex.exp (((Real.log (xi * p) * t : ℝ) : ℂ) * I))) -
        ((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ) * primeGaussianProfile ((p : ℝ) / N) *
          bourgainOscillation (2 * Real.pi * xi * p)‖ ≤ C / N := by
  obtain ⟨Cm, Ce, hCm, hCe, hk⟩ := exists_complete_physical_chi_positiveGrade_kernel
  have hc : 0 < 2 * Real.pi * xi := by positivity
  refine ⟨(Cm + 3120 * Ce) / Real.sqrt (2 * Real.pi * xi), by positivity, ?_⟩
  intro N hN hT p hp
  obtain ⟨_, hpN, hp2N⟩ := primeProfileBand_mem hN.le hp
  have hp0 : (0 : ℝ) < p := hN.trans hpN
  have ha : 0 < 2 * Real.pi * xi * p := by positivity
  have hT0 : 0 < 2 * Real.pi * xi * N := by positivity
  have hr : (2 * Real.pi * xi * p) / (2 * Real.pi * xi * N) = (p : ℝ) / N := by field_simp
  have hrange : (2 * Real.pi * xi * p) / (2 * Real.pi * xi * N) ∈ Icc (1 / 2 : ℝ) 4 := by
    rw [hr]
    constructor
    · apply (le_div_iff₀ hN).mpr
      linarith
    · apply (div_le_iff₀ hN).mpr
      linarith
  have hlog : (2 * Real.pi * xi * p) / (2 * Real.pi) = xi * p := by field_simp
  have hh := hk _ _ hT ha hrange 1 (by norm_num)
  simp only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one, hlog] at hh
  rw [physicalChiGradeOne_second_error hT0] at hh
  have hfirst : (2 * Real.pi * xi * p) * Cm /
      ((2 * Real.pi * xi * p) * Real.sqrt (2 * Real.pi * xi * p)) ≤
      Cm / Real.sqrt (2 * Real.pi * xi * N) := by
    rw [mul_div_mul_left Cm _ ha.ne']
    exact div_le_div_of_nonneg_left hCm.le (by positivity)
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpN.le hc.le))
  have hb := hh.trans (add_le_add hfirst le_rfl)
  rw [← add_div] at hb
  rw [← physicalChiStationaryMain_one_prime hxi hN hp0, ← mul_sub, norm_mul]
  have hv : ‖smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ)‖ ≤ 1 / Real.sqrt N := by
    rw [norm_div, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (norm_smoothAFECutoff_le_one (div_pos hp0 hN))
      (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (Real.sqrt_le_sqrt hpN.le))
  calc
    _ ≤ (1 / Real.sqrt N) * ((Cm + 3120 * Ce) / Real.sqrt (2 * Real.pi * xi * N)) :=
      mul_le_mul hv hb (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hc.le]
      have hsN := Real.sq_sqrt hN.le
      have hnS : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      field_simp
      nlinarith

private theorem primeGaussianChiIntegral_eq_sum (xi N : ℝ) :
    primeGaussianChiIntegral xi N = ∑ p ∈ primeProfileBand N,
      (smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ)) *
        (∫ t in (2 * Real.pi * xi * N)..2 * (2 * Real.pi * xi * N),
          (bagPhysicalHeightWindow (t / (2 * Real.pi * xi * N)) : ℂ) *
            (zetaChi (linePt t) * Complex.exp (((Real.log (xi * p) * t : ℝ) : ℂ) * I))) := by
  let f : ℕ → ℝ → ℂ := fun p t =>
    (smoothAFECutoff ((p : ℝ) / N) / (Real.sqrt p : ℂ)) *
      ((bagPhysicalHeightWindow (t / (2 * Real.pi * xi * N)) : ℂ) *
        (zetaChi (linePt t) * Complex.exp (((Real.log (xi * p) * t : ℝ) : ℂ) * I)))
  have hc (p : ℕ) : Continuous (f p) := by
    have hh := continuous_zetaChiCriticalGradeIntegrand (1 : ℤ) (Real.log (xi * p))
    simp only [zpow_one] at hh
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const _))).mul hh)
  calc
    _ = ∫ t in (2 * Real.pi * xi * N)..2 * (2 * Real.pi * xi * N),
        ∑ p ∈ primeProfileBand N, f p t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [primeGaussianChiField, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [f]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun p _ => (hc p).intervalIntegrable _ _)]
      simp only [f, intervalIntegral.integral_const_mul]

/-- Both actual kernel remainders remain in one uniformly bounded total error. -/
theorem exists_primeGaussianChi_full_error {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → 4 ≤ 2 * Real.pi * xi * N →
      ‖primeGaussianChiIntegral xi N - ((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ) *
        ∑ p ∈ primeProfileBand N, primeGaussianProfile ((p : ℝ) / N) *
          bourgainOscillation (2 * Real.pi * xi * p)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_primeGaussianChi_entry_error hxi
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN hT
  rw [primeGaussianChiIntegral_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← mul_assoc (((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ))]
  have hs := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => hb N hN hT p hp))
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  refine hs.trans ?_
  calc
    _ ≤ (2 * N) * (C / N) := mul_le_mul_of_nonneg_right (primeProfileBand_card_le hN.le) (by positivity)
    _ = _ := by field_simp

/-- Full physical Gaussian prime saddle law at every fixed positive rational frequency.
The only parameters are positive integers; no analytic estimate is assumed. -/
theorem tendsto_primeGaussianChi_rational (a q : ℕ) (ha : 1 ≤ a) (hq : 1 ≤ q) :
    Tendsto (fun N : ℝ => (Real.log N : ℂ) *
      primeGaussianChiIntegral ((a : ℝ) / q) N / (N : ℂ)) atTop
      (𝓝 (((2 * Real.pi * Real.sqrt ((a : ℝ) / q) : ℝ) : ℂ) *
        ((∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), primeRationalPhase a q r) /
          (q.totient : ℂ)) * ∫ x in (1 : ℝ)..2, primeGaussianProfile x)) := by
  let xi : ℝ := (a : ℝ) / q
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hxi : 0 < xi := div_pos ha0 hq0
  have hc : 0 < 2 * Real.pi * xi := by positivity
  obtain ⟨C, hC, hb⟩ := exists_primeGaussianChi_full_error hxi
  have hsmall : Tendsto (fun N : ℝ => (Real.log N / N) * C) atTop (𝓝 0) := by
    simpa only [zero_mul, id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mul_const C
  have herr : Tendsto (fun N : ℝ => (Real.log N : ℂ) *
      (primeGaussianChiIntegral xi N - ((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ) *
        ∑ p ∈ primeProfileBand N, primeGaussianProfile ((p : ℝ) / N) *
          bourgainOscillation (2 * Real.pi * xi * p)) / (N : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (4 / (2 * Real.pi * xi))]
      with N hN hscale
    have hN0 : 0 < N := by linarith
    have hT : 4 ≤ 2 * Real.pi * xi * N := by
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hscale
    rw [norm_div, norm_mul, Complex.norm_of_nonneg (Real.log_nonneg hN.le),
      Complex.norm_of_nonneg hN0.le]
    calc
      _ ≤ (Real.log N * C) / N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb N hN0 hT) (Real.log_nonneg hN.le)) hN0.le
      _ = _ := by ring
  have hmain := (tendsto_primeGaussian_rational_profile a hq).const_mul
    (((2 * Real.pi * Real.sqrt xi : ℝ) : ℂ))
  have hsum := herr.add hmain
  simp only [zero_add, mul_assoc] at hsum ⊢
  apply hsum.congr
  intro N
  dsimp only [primeRationalPhase, xi]
  simp only [← mul_assoc]
  ring

/-- The complete Gaussian-window mass is strictly positive in its real direction. -/
theorem primeGaussianProfile_integral_re_pos :
    0 < (∫ x in (1 : ℝ)..2, primeGaussianProfile x).re := by
  have hc : ContinuousOn primeGaussianProfile (Icc (1 : ℝ) 2) := fun x hx =>
    (primeGaussianProfile_regular.1 x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable primeGaussianProfile volume 1 2 :=
    hc.intervalIntegrable_of_Icc (by norm_num : (1 : ℝ) ≤ 2)
  have hre : (∫ x in (1 : ℝ)..2, (primeGaussianProfile x).re) =
      (∫ x in (1 : ℝ)..2, primeGaussianProfile x).re := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.intervalIntegral_comp_comm hi
  rw [← hre]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Complex.continuous_re.comp_continuousOn hc).intervalIntegrable_of_Icc (by norm_num)) _ (by norm_num)
  intro x hx
  have hW : 0 < bagPhysicalHeightWindow x := by
    apply bagPhysicalHeightWindow.pos_of_mem_ball
    change dist x (3 / 2 : ℝ) < 1 / 2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hV := smoothAFECutoff_re_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hx.1)
  simpa only [Function.comp_apply, primeGaussianProfile, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hW hV

/-- Denominator two retains the negative prime saddle, instead of cancelling it. -/
theorem tendsto_primeGaussianChi_half :
    Tendsto (fun N : ℝ => (Real.log N : ℂ) *
      primeGaussianChiIntegral (1 / 2) N / (N : ℂ)) atTop
      (𝓝 (-(((2 * Real.pi * Real.sqrt (1 / 2) : ℝ) : ℂ) *
        ∫ x in (1 : ℝ)..2, primeGaussianProfile x))) := by
  have hp : primeRationalPhase 1 2 1 = -1 := by
    unfold primeRationalPhase bourgainOscillation
    convert Complex.exp_pi_mul_I using 1
    push_cast
    ring
  have hsum : (∑ r ∈ (Finset.range 2).filter (fun r => r.Coprime 2),
      primeRationalPhase 1 2 r) = -1 := by
    rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_succ]
    norm_num [hp]
  have hh := tendsto_primeGaussianChi_rational 1 2 (by norm_num) (by norm_num)
  simpa only [Nat.cast_one, Nat.cast_ofNat, hsum, show Nat.totient 2 = 1 by norm_num,
    div_one, mul_neg_one, neg_mul] using hh

/-- The actual complete half-frequency integral eventually has negative real part. -/
theorem eventually_primeGaussianChi_half_re_neg :
    ∀ᶠ N : ℝ in atTop, (primeGaussianChiIntegral (1 / 2) N).re < 0 := by
  have hA : 0 < 2 * Real.pi * Real.sqrt (1 / 2 : ℝ) := by positivity
  have hlimit : (-(((2 * Real.pi * Real.sqrt (1 / 2) : ℝ) : ℂ) *
      ∫ x in (1 : ℝ)..2, primeGaussianProfile x)).re < 0 := by
    simpa only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, neg_lt_zero] using mul_pos hA primeGaussianProfile_integral_re_pos
  have hh := (Complex.continuous_re.tendsto _).comp tendsto_primeGaussianChi_half
  have hneg := hh.eventually (gt_mem_nhds hlimit)
  filter_upwards [hneg, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have he : ((Real.log N : ℂ) * primeGaussianChiIntegral (1 / 2) N / (N : ℂ)).re =
      (Real.log N / N) * (primeGaussianChiIntegral (1 / 2) N).re := by
    rw [show (Real.log N : ℂ) * primeGaussianChiIntegral (1 / 2) N / (N : ℂ) =
      ((Real.log N / N : ℝ) : ℂ) * primeGaussianChiIntegral (1 / 2) N by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [Function.comp_apply] at hN
  rw [he] at hN
  by_contra hn
  have hh0 := mul_nonneg (div_pos hlog hN0).le (le_of_not_gt hn)
  linarith

end RHTower
