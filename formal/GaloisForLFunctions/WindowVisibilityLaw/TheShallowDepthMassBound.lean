import GaloisForLFunctions.WindowVisibilityLaw.CoherentClusterAndTiltAmplificationLaw
import GaloisForLFunctions.VerifiedHeightRungs.TheNormalizedSmoothingKeepsThePoles

/-!
# The shallow depth-mass bound under window positivity

**Theorem** (`windowPositiveAt_shallow_depth_mass_bound`). Let `Z` have at most `A₀ log(|t| + 3)` zeros in
unit windows, and let `WindowPositiveAt Z a`, `a ≥ 1`. Let `S` be a finite set of off-line zeros of depths
`ε_ρ > 0`, shallow (`ε_ρ a ≤ 1`) and coherent (`|γ_ρ − γ₀| ≤ ε_ρ/4`). If all other zeros have depth `≤ σ`,
`Σ_{ρ ∈ S} m_ρ ε_ρ² · a² ≤ 2²⁴ e^{2π} A₀ log(|γ₀| + 2¹⁴ eᵃ + 6) e^{2σa}`.

So at a shallow aperture the depth mass, not the count, is what positivity bounds, with no lattice structure on
the background. The test is `sinh(u/a)(a² − u²)₊^{5/2}`: its signal against a zero of depth `ε` is `≳ ε a⁷`, and
its `L²` mass is `≲ a¹¹`. Near zeros cost `(2a + 2π)` times the mass, because a unit-window count allows them to
cluster at the scale `1/a`; this is the single power of `a` separating this bound from the crystal law `k δ² a³ ≲ L`.
-/

open Complex MeasureTheory Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.VerifiedHeightRungs

/-- The odd test of the shallow regime. -/
def shallowTest (a : ℝ) : ℝ → ℝ := sinhTest a (1 / a)

theorem shallowTest_nonneg {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) : 0 ≤ shallowTest a u :=
  mul_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)) (sinhTestWeight_nonneg a u)

theorem shallowTest_mul_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ shallowTest a u * u := by
  rcases le_or_gt 0 u with hu | hu
  · exact mul_nonneg (shallowTest_nonneg ha hu) hu
  · have h := shallowTest_nonneg ha (u := -u) (by linarith only [hu])
    have hodd : shallowTest a (-u) = -shallowTest a u := sinhTest_odd a (1 / a) u
    rw [hodd] at h
    nlinarith only [h, hu]

/-- The signal against depth `ε` dominates `ε` times the first moment. -/
theorem le_integral_shallowTest_mul_sinh {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ε * ∫ u, shallowTest a u * u ≤ ∫ u, shallowTest a u * Real.sinh (ε * u) := by
  have hs : Continuous (shallowTest a) := (sinhTest_contDiff a (1 / a)).continuous
  have hcs : HasCompactSupport (shallowTest a) :=
    hasCompactSupport_of_support_subset_abs (sinhTest_supp ha.le)
  rw [← integral_const_mul]
  refine integral_mono
    (((hs.mul continuous_id).integrable_of_hasCompactSupport hcs.mul_right).const_mul ε)
    ((hs.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right) fun u => ?_
  change ε * (shallowTest a u * u) ≤ shallowTest a u * Real.sinh (ε * u)
  rcases le_or_gt 0 u with hu | hu
  · have h := Real.self_le_sinh_iff.mpr (mul_nonneg hε.le hu)
    have := mul_le_mul_of_nonneg_left h (shallowTest_nonneg ha hu)
    linarith only [this]
  · have hodd : shallowTest a (-u) = -shallowTest a u := sinhTest_odd a (1 / a) u
    have hs0 := shallowTest_nonneg ha (u := -u) (by linarith only [hu])
    have h := Real.self_le_sinh_iff.mpr (mul_nonneg hε.le (by linarith only [hu] : (0 : ℝ) ≤ -u))
    have := mul_le_mul_of_nonneg_left h hs0
    rw [hodd, mul_neg, Real.sinh_neg] at this
    nlinarith only [this]

/-- The first moment is at least `9 a⁷/1280`. -/
theorem le_integral_shallowTest_mul {a : ℝ} (ha : 0 < a) :
    9 / 1280 * a ^ 7 ≤ ∫ u, shallowTest a u * u := by
  have hs : Continuous (shallowTest a) := (sinhTest_contDiff a (1 / a)).continuous
  have hcs : HasCompactSupport (shallowTest a) :=
    hasCompactSupport_of_support_subset_abs (sinhTest_supp ha.le)
  have hint : Integrable fun u => shallowTest a u * u :=
    (hs.mul continuous_id).integrable_of_hasCompactSupport hcs.mul_right
  have h1 := setIntegral_le_integral (s := Icc (a / 4) (a / 2)) hint
    (Filter.Eventually.of_forall (shallowTest_mul_nonneg ha))
  have hc : ∀ u ∈ Icc (a / 4) (a / 2), 9 / 320 * a ^ 6 ≤ shallowTest a u * u := by
    intro u hu
    have hu0 : 0 ≤ u := by linarith only [hu.1, ha]
    have hw := sinhTestWeight_ge ha (u := u) (by rw [abs_of_nonneg hu0]; exact hu.2)
    have hsinh := Real.self_le_sinh_iff.mpr (show 0 ≤ 1 / a * u by positivity)
    have hua : a / 16 ≤ 1 / a * u * u := by
      have h : a ^ 2 / 16 ≤ u * u := by nlinarith only [hu.1, ha]
      have e : 1 / a * u * u = (u * u) / a := by field_simp
      rw [e, le_div_iff₀ ha]
      nlinarith only [h]
    have ha5 : (0 : ℝ) < a ^ 5 := by positivity
    have h2 : 1 / a * u * u ≤ Real.sinh (1 / a * u) * u := mul_le_mul_of_nonneg_right hsinh hu0
    have h3 : a / 16 * (9 / 20 * a ^ 5) ≤ Real.sinh (1 / a * u) * u * sinhTestWeight a u :=
      mul_le_mul (hua.trans h2) hw (by positivity) (mul_nonneg (hsinh.trans' (by positivity)) hu0)
    change _ ≤ Real.sinh (1 / a * u) * sinhTestWeight a u * u
    calc
      9 / 320 * a ^ 6 = a / 16 * (9 / 20 * a ^ 5) := by ring
      _ ≤ Real.sinh (1 / a * u) * u * sinhTestWeight a u := h3
      _ = _ := by ring
  have h2 := setIntegral_ge_of_const_le_real (μ := volume) (s := Icc (a / 4) (a / 2))
    measurableSet_Icc (by simp) hc hint.integrableOn
  have hvol : (volume : Measure ℝ).real (Icc (a / 4) (a / 2)) = a / 4 := by
    rw [Real.volume_real_Icc_of_le (by linarith only [ha])]
    ring
  rw [hvol] at h2
  calc
    9 / 1280 * a ^ 7 = 9 / 320 * a ^ 6 * (a / 4) := by ring
    _ ≤ _ := h2.trans h1

/-- `cosh 1 ≤ 2`. -/
theorem cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  have h := Real.cosh_le_exp_half_sq (1 : ℝ)
  have h2 : Real.exp (1 ^ 2 / 2) ≤ 2 := by
    have e : Real.exp (1 ^ 2 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 := Real.exp_one_lt_d9
    nlinarith only [e, h3, Real.exp_pos (1 ^ 2 / 2 : ℝ)]
  exact h.trans h2

/-- The `L²` mass of the shallow test. -/
theorem integral_norm_sq_modulatedTest_shallowTest_le (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ u, ‖modulatedTest γ₀ (shallowTest a) u‖ ^ 2 ≤ 8 * a ^ 11 := by
  have hpt : (fun u => ‖modulatedTest γ₀ (shallowTest a) u‖ ^ 2) = fun u => shallowTest a u ^ 2 := by
    funext u
    simp only [modulatedTest, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, one_mul, sq_abs]
  rw [hpt]
  have hb : ∀ u ∈ Icc (-a) a, shallowTest a u ^ 2 ≤ 4 * a ^ 10 := by
    intro u hu
    have hu' : |1 / a * u| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / a), one_div, inv_mul_le_iff₀ ha, mul_one]
      exact abs_le.mpr hu
    have h1 : |Real.sinh (1 / a * u)| ≤ 2 := by
      rw [Real.abs_sinh]
      refine (Real.sinh_lt_cosh _).le.trans (le_trans ?_ cosh_one_le_two)
      rw [Real.cosh_le_cosh, abs_abs, abs_one]
      exact hu'
    have h2 : |sinhTestWeight a u| ≤ a ^ 5 := by
      rw [abs_of_nonneg (sinhTestWeight_nonneg a u)]
      exact sinhTestWeight_le ha u
    have h3 : |shallowTest a u| ≤ 2 * a ^ 5 := by
      rw [shallowTest, sinhTest, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    rw [← sq_abs]
    calc
      |shallowTest a u| ^ 2 ≤ (2 * a ^ 5) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = _ := by ring
  have hout : ∀ u, u ∉ Icc (-a) a → shallowTest a u ^ 2 = 0 := by
    intro u hu
    by_contra h
    have h0 : shallowTest a u ≠ 0 := fun h' => h (by rw [h']; norm_num)
    exact hu (abs_le.mp (sinhTest_supp ha.le u h0))
  have h := integral_le_of_bound_on_Icc ha (fun u => sq_nonneg (shallowTest a u)) hb hout
  refine h.trans (le_of_eq ?_)
  ring

/-- The `C²` size of the shallow test. -/
theorem testNorm_shallowTest_le {a : ℝ} (ha : 1 ≤ a) : testNorm (shallowTest a) ≤ 128 * a ^ 6 := by
  have ha0 : 0 < a := by linarith only [ha]
  have h := testNorm_sinhTest_le ha0.le (show 0 ≤ 1 / a by positivity)
  have e : 1 / a * a = 1 := by field_simp
  rw [e] at h
  have hpoly : a ^ 5 + (1 / a) ^ 2 * a ^ 5 + 10 * (1 / a) * a ^ 4 + 20 * a ^ 3 ≤ 32 * a ^ 5 := by
    have e1 : (1 / a) ^ 2 * a ^ 5 = a ^ 3 := by field_simp
    have e2 : 10 * (1 / a) * a ^ 4 = 10 * a ^ 3 := by field_simp
    rw [e1, e2]
    have h35 : a ^ 3 ≤ a ^ 5 := pow_le_pow_right₀ ha (by norm_num)
    have h5 : 0 ≤ a ^ 5 := by positivity
    linarith only [h35, h5]
  refine h.trans ?_
  calc
    _ ≤ 2 * a * 2 * (32 * a ^ 5) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left cosh_one_le_two (by positivity)) hpoly
        ?_ (by positivity)
      have h3 : 0 ≤ a ^ 3 := by positivity
      have h4 : 0 ≤ a ^ 4 := by positivity
      have h5 : 0 ≤ a ^ 5 := by positivity
      positivity
    _ = _ := by ring

/-- **The shallow depth-mass bound.** Window positivity bounds the depth mass `Σ m_ρ ε_ρ²` of a shallow coherent
cluster by `≲ A₀ log(|γ₀| + eᵃ) e^{2σa}/a²`, on every configuration with unit-window Riemann–von Mangoldt counts. -/
theorem windowPositiveAt_shallow_depth_mass_bound (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a σ : ℝ} (ha : 1 ≤ a) (hσ : 0 ≤ σ) (hpos : WindowPositiveAt Z a)
    (S : Finset ℂ) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier) (hSpos : ∀ ρ ∈ S, 1 / 2 < ρ.re)
    (hSa : ∀ ρ ∈ S, (ρ.re - 1 / 2) * a ≤ 1) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ (ρ.re - 1 / 2) / 4)
    (hsea : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) :
    (∑ ρ ∈ S, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2) * a ^ 2 ≤
      2 ^ 24 * Real.exp (2 * π) * A₀ * Real.log (|γ₀| + 2 ^ 14 * Real.exp a + 6) *
        Real.exp (2 * σ * a) := by
  classical
  have ha0 : 0 < a := by linarith only [ha]
  obtain ⟨s, hs⟩ : ∃ s, s = shallowTest a := ⟨_, rfl⟩
  have hs_cd : ContDiff ℝ 2 s := by rw [hs]; exact sinhTest_contDiff a (1 / a)
  have hs_supp : ∀ u, s u ≠ 0 → |u| ≤ a := by rw [hs]; exact sinhTest_supp ha0.le
  have hs_odd : ∀ u, s (-u) = -s u := by rw [hs]; exact sinhTest_odd a (1 / a)
  have hs_nn : ∀ u, 0 ≤ u → 0 ≤ s u := by rw [hs]; exact fun u hu => shallowTest_nonneg ha0 hu
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∫ u, shallowTest a u * u := ⟨_, rfl⟩
  have hQlow : 9 / 1280 * a ^ 7 ≤ Q := by rw [hQ]; exact le_integral_shallowTest_mul ha0
  have ha7 : (0 : ℝ) < a ^ 7 := by positivity
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQlow
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 ^ 14 * Real.exp a := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    have := Real.one_le_exp ha0.le
    nlinarith only [this]
  have hSγR : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ R := fun ρ hρ => by
    have h1 := hSγ ρ hρ
    have h2 : ρ.re - 1 / 2 ≤ 1 := by
      have := hSa ρ hρ
      have h3 : 0 < ρ.re - 1 / 2 := by linarith only [hSpos ρ hρ]
      nlinarith only [this, h3, ha]
    linarith only [h1, h2, hR1]
  have hmain := re_W_modulatedTest_le_of_pairs Z hA₀ hloc (γ₀ := γ₀) ha0 hR0 hσ hs_cd hs_supp S hSc hSpos
    hSγR (fun ρ hρ h1 h2 _ => hsea ρ hρ h1 h2)
  have hzero : 0 ≤ (Z.W (modulatedTest γ₀ s) (modulatedTest γ₀ s)).re :=
    hpos _ (modulatedTest_contDiff γ₀ hs_cd) (tsupport_modulatedTest_subset γ₀ hs_supp)
  -- The cluster pays `(5/8) X Q²`.
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ ρ ∈ S, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hpair : ∑ ρ ∈ S, ((Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ).re +
      (Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) (reflect ρ)).re) ≤ -(5 / 8) * X * Q ^ 2 := by
    rw [hX, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    obtain ⟨ε, hε⟩ : ∃ ε, ε = ρ.re - 1 / 2 := ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; linarith only [hSpos ρ hρ]
    have hre : ρ.re = 1 / 2 + ε := by rw [hε]; ring
    have h1 := re_Wsummand_pair_modulatedTest_le Z γ₀ (hSc ρ hρ) hεpos hre hs_cd.continuous hs_supp hs_odd
      hs_nn (Or.inr ⟨by rw [hε]; exact hSa ρ hρ, by rw [hε]; exact hSγ ρ hρ⟩)
    have h2 : ε * Q ≤ ∫ u, s u * Real.sinh (ε * u) := by
      rw [hQ, hs]
      exact le_integral_shallowTest_mul_sinh ha0 hεpos
    have h3 := pow_le_pow_left₀ (mul_nonneg hεpos.le hQ0) h2 2
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left h3 hm
    rw [← hε]
    nlinarith only [h1, h4]
  -- The background.
  have hmass : ∫ u, ‖modulatedTest γ₀ s u‖ ^ 2 ≤ 8 * a ^ 11 := by
    rw [hs]
    exact integral_norm_sq_modulatedTest_shallowTest_le γ₀ ha0
  obtain ⟨Lg, hLg⟩ : ∃ Lg, Lg = Real.log (|γ₀| + R + 6) := ⟨_, rfl⟩
  have hL3 : Real.log (|γ₀| + 3) ≤ Lg := by
    rw [hLg]
    exact Real.log_le_log (by positivity) (by linarith only [hR0])
  have hL30 : 0 ≤ Real.log (|γ₀| + 3) := zero_le_one.trans (one_le_log_abs_add_three γ₀)
  have hLg0 : 0 ≤ Lg := hL30.trans hL3
  have hexpσ : 1 ≤ Real.exp (2 * σ * a) := Real.one_le_exp (by positivity)
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (2 * σ * a) := ⟨_, rfl⟩
  rw [← hE] at hexpσ
  obtain ⟨Eπ, hEπ⟩ : ∃ Eπ, Eπ = Real.exp (2 * π) := ⟨_, rfl⟩
  have hEπ0 : 0 < Eπ := by rw [hEπ]; positivity
  have hnearCost : 4 * A₀ * Lg * ((2 * a + 2 * π) * Eπ * E) * (∫ u, ‖modulatedTest γ₀ s u‖ ^ 2) ≤
      288 * Eπ * E * A₀ * Lg * a ^ 12 := by
    have h1 : 2 * a + 2 * π ≤ 9 * a := by
      have := Real.pi_lt_d2
      nlinarith only [this, ha]
    have hA₀0 : 0 ≤ A₀ := by linarith only [hA₀]
    have h2 : 0 ≤ 4 * A₀ * Lg * ((2 * a + 2 * π) * Eπ * E) := by positivity
    calc
      _ ≤ 4 * A₀ * Lg * ((2 * a + 2 * π) * Eπ * E) * (8 * a ^ 11) :=
        mul_le_mul_of_nonneg_left hmass h2
      _ ≤ 4 * A₀ * Lg * (9 * a * Eπ * E) * (8 * a ^ 11) := by
        gcongr
      _ = _ := by ring
  have hfarCost : 384 * A₀ * Real.log (|γ₀| + 3) * testNorm s ^ 2 * (Real.exp a / (1 + R)) ≤
      384 * A₀ * Lg * a ^ 12 := by
    have hT : testNorm s ^ 2 ≤ 2 ^ 14 * a ^ 12 := by
      have h := pow_le_pow_left₀ (testNorm_nonneg s) (by rw [hs]; exact testNorm_shallowTest_le ha) 2
      refine h.trans (le_of_eq ?_)
      ring
    have hfrac : 2 ^ 14 * (Real.exp a / (1 + R)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (by linarith only [hR0]), ← hRdef]
      linarith only
    have hA₀0 : 0 ≤ A₀ := by linarith only [hA₀]
    have hexp0 : 0 ≤ Real.exp a / (1 + R) := by positivity
    calc
      _ ≤ 384 * A₀ * Lg * (2 ^ 14 * a ^ 12) * (Real.exp a / (1 + R)) := by
        gcongr
      _ = 384 * A₀ * Lg * a ^ 12 * (2 ^ 14 * (Real.exp a / (1 + R))) := by ring
      _ ≤ 384 * A₀ * Lg * a ^ 12 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := mul_one _
  rw [← hE, ← hEπ, ← hLg] at hmain
  -- The balance.
  have hQ2 : a ^ 14 / 2 ^ 15 ≤ Q ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hQlow 2
    refine le_trans ?_ h
    have e : (9 / 1280 * a ^ 7) ^ 2 = 81 / 1638400 * a ^ 14 := by ring
    rw [e, div_eq_inv_mul]
    have : (0 : ℝ) ≤ a ^ 14 := by positivity
    exact mul_le_mul_of_nonneg_right (by norm_num) this
  have hbal : 5 / 8 * X * (a ^ 14 / 2 ^ 15) ≤ (288 * Eπ * E + 384) * A₀ * Lg * a ^ 12 := by
    have h := mul_le_mul_of_nonneg_left hQ2 (show 0 ≤ 5 / 8 * X by positivity)
    nlinarith only [h, hzero, hmain, hpair, hnearCost, hfarCost]
  have hEπ1 : 384 ≤ Eπ := by
    rw [hEπ]
    have h1 := Real.add_one_le_exp (2 * π)
    have h2 : Real.exp (2 * π) = Real.exp π * Real.exp π := by rw [two_mul, Real.exp_add]
    have h3 := Real.add_one_le_exp π
    have h4 := Real.pi_gt_three
    have h5 : (20 : ℝ) ≤ Real.exp π := by
      have h6 := Real.exp_one_gt_d9
      have h7 : Real.exp 3 ≤ Real.exp π := Real.exp_le_exp.mpr h4.le
      have h8 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h9 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith only [h6]) 3
      norm_num at h9
      linarith only [h7, h8, h9]
    nlinarith only [h2, h5]
  have hcoef : 288 * Eπ * E + 384 ≤ 289 * Eπ * E := by nlinarith only [hEπ1, hexpσ, hEπ0]
  have ha12 : (0 : ℝ) < a ^ 12 := by positivity
  have hA₀0 : 0 ≤ A₀ := by linarith only [hA₀]
  have hfinal : 5 / 8 * X * (a ^ 2 / 2 ^ 15) ≤ 289 * Eπ * E * A₀ * Lg := by
    have h1 : (288 * Eπ * E + 384) * A₀ * Lg * a ^ 12 ≤ 289 * Eπ * E * A₀ * Lg * a ^ 12 := by
      gcongr
    have h2 : 5 / 8 * X * (a ^ 2 / 2 ^ 15) * a ^ 12 ≤ 289 * Eπ * E * A₀ * Lg * a ^ 12 := by
      refine le_trans (le_of_eq ?_) (hbal.trans h1)
      ring
    exact le_of_mul_le_mul_right h2 ha12
  rw [← hX, ← hEπ, ← hE, ← hRdef, ← hLg]
  have hpos2 : 0 ≤ 289 * Eπ * E * A₀ * Lg := by positivity
  calc
    X * a ^ 2 = 8 / 5 * 2 ^ 15 * (5 / 8 * X * (a ^ 2 / 2 ^ 15)) := by ring
    _ ≤ 8 / 5 * 2 ^ 15 * (289 * Eπ * E * A₀ * Lg) := mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ ≤ 2 ^ 24 * (Eπ * E * A₀ * Lg) := by
      have h : 0 ≤ Eπ * E * A₀ * Lg := by positivity
      nlinarith only [h]
    _ = _ := by ring

end GaloisForLFunctions.WindowVisibilityLaw

end

#print axioms GaloisForLFunctions.WindowVisibilityLaw.windowPositiveAt_shallow_depth_mass_bound
