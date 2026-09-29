import GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.RHTower.FrequencySectorBlaschkeCompleteness

/-!
# Cofinite prime-clock totality of the Gamma coherent sectors

**Theorem PPTI-F.**  For every degree `k ≥ 1` and every finite set `S` of primes,

`closedSpan {ψ_{log p}^{(k)} : p ∉ S} = L²((0,∞), dr)`.

If `f` is orthogonal to all retained columns, the damped datum `φ(r) = r^{(k-1)/2} e^{-r/2} f(r)`
is square integrable and `⟨ψ_t^{(k)}, f⟩` is a nonzero multiple of its half-line Laplace transform
at `t - 1/2`.  The Laplace transform is bounded and holomorphic on translated half-planes and
vanishes at every retained `log p - 1/2`; the translated sector-Blaschke divergence of the cofinite
prime logarithms forces it to vanish on a real ray, analytic continuation makes it vanish on the
whole right half-plane, and Laplace injectivity gives `φ = 0`, hence `f = 0`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

theorem primeClock_pos (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
  Real.log_pos (by exact_mod_cast p.2.one_lt)

/-- `r^α e^{-r/2} ≤ 1 + 2ⁿ n!` for `0 ≤ α ≤ n` and `r > 0`. -/
theorem rpow_mul_exp_neg_half_le {α : ℝ} {n : ℕ} (hα0 : 0 ≤ α) (hαn : α ≤ n) {r : ℝ}
    (hr : 0 < r) : r ^ α * Real.exp (-(r / 2)) ≤ 1 + 2 ^ n * (n.factorial : ℝ) := by
  have he : Real.exp (-(r / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hf : (0 : ℝ) ≤ 2 ^ n * (n.factorial : ℝ) := by positivity
  rcases le_or_gt r 1 with h1 | h1
  · have hra : r ^ α ≤ 1 := Real.rpow_le_one hr.le h1 hα0
    nlinarith [Real.exp_pos (-(r / 2)), Real.rpow_nonneg hr.le α]
  · have hra : r ^ α ≤ r ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1.le hαn
    have hexp := Real.pow_div_factorial_le_exp (r / 2) (by linarith) n
    have hpow : r ^ n = 2 ^ n * (r / 2) ^ n := by rw [div_pow]; field_simp
    have hmul : Real.exp (r / 2) * Real.exp (-(r / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h2 : (r / 2) ^ n ≤ n.factorial * Real.exp (r / 2) := by
      have := (div_le_iff₀ hfpos).1 hexp
      linarith
    have hkey : r ^ n * Real.exp (-(r / 2)) ≤ 2 ^ n * (n.factorial : ℝ) := by
      rw [hpow]
      calc 2 ^ n * (r / 2) ^ n * Real.exp (-(r / 2))
          ≤ 2 ^ n * (n.factorial * Real.exp (r / 2)) * Real.exp (-(r / 2)) := by gcongr
        _ = 2 ^ n * n.factorial * (Real.exp (r / 2) * Real.exp (-(r / 2))) := by ring
        _ = 2 ^ n * n.factorial := by rw [hmul, mul_one]
    nlinarith [Real.exp_pos (-(r / 2))]

/-- The damped datum `φ(r) = r^{(k-1)/2} e^{-r/2} f(r)`. -/
def gammaDampedDatum (k : ℕ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r ^ (((k : ℝ) - 1) / 2) * Real.exp (-(r / 2)) : ℝ) : ℂ) * f r

theorem memLp_gammaDampedDatum {k : ℕ} (hk : k ≠ 0) (f : HalfLineL2) :
    MemLp (gammaDampedDatum k f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hα0 : (0 : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith
  have hαn : ((k : ℝ) - 1) / 2 ≤ (k : ℕ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine MemLp.of_le ((Lp.memLp f).const_mul ((1 + 2 ^ k * (k.factorial : ℝ) : ℝ) : ℂ)) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (Lp.memLp f).aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : (0 : ℝ) < r := hr
    rw [gammaDampedDatum, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hr'.le _) (Real.exp_pos _).le),
      Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (rpow_mul_exp_neg_half_le hα0 hαn hr) (norm_nonneg _)

/-- `⟨ψ_t^{(k)}, f⟩ = √((2t)^k/(k-1)!) · 𝓛φ(t - 1/2)`. -/
theorem inner_gammaCoherentVector_eq_laplaceRay (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t)
    (f : HalfLineL2) :
    ⟪gammaCoherentVector k ht, f⟫_ℂ =
      (Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ)) : ℂ) *
        laplaceRay (gammaDampedDatum k f) ((t : ℂ) - 1 / 2) := by
  rw [L2.inner_def, laplaceRay, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [gammaCoherentVector_ae k ht] with r hr
  rw [hr, RCLike.inner_apply, Complex.conj_ofReal, gammaDampedDatum, expRay,
    gammaCoherentProfile]
  have hexp : Complex.exp (-(((t : ℂ) - 1 / 2) * (r : ℝ))) =
      ((Real.exp (-(t * r)) / Real.exp (-(r / 2)) : ℝ) : ℂ) := by
    rw [← Real.exp_sub, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hne : Real.exp (-(r / 2)) ≠ 0 := (Real.exp_pos _).ne'
  push_cast
  field_simp

theorem sectorRootMap_one_re_gt {R : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    R < (sectorRootMap 1 R z).re := by
  rw [sectorRootMap, Nat.cast_one, inv_one, Complex.cpow_one, Complex.add_re, Complex.ofReal_re]
  linarith [diskToRight_re_pos hz]

/-- **Theorem PPTI-F, dual form.**  A vector orthogonal to every retained coherent column is
zero. -/
theorem eq_zero_of_forall_inner_gammaCoherentVector_eq_zero (k : ℕ) [NeZero k]
    (S : Finset Nat.Primes) (f : HalfLineL2)
    (h : ∀ p : Nat.Primes, p ∉ S → ⟪gammaCoherentVector k (primeClock_pos p), f⟫_ℂ = 0) :
    f = 0 := by
  set φ := gammaDampedDatum k f
  have hφ := memLp_gammaDampedDatum (NeZero.ne k) f
  have hL : ∀ p : Nat.Primes, p ∉ S → laplaceRay φ ((Real.log (p : ℝ) : ℂ) - 1 / 2) = 0 := by
    intro p hp
    have h1 := h p hp
    rw [inner_gammaCoherentVector_eq_laplaceRay] at h1
    have hc : (Real.sqrt ((2 * Real.log (p : ℝ)) ^ k / ((k - 1).factorial : ℝ)) : ℂ) ≠ 0 := by
      have := primeClock_pos p
      have : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
    exact (mul_eq_zero.1 h1).resolve_left hc
  have hdiff := differentiableOn_laplaceRay hφ
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticOnNhd ℂ (laplaceRay φ) {w : ℂ | 0 < w.re} := hdiff.analyticOnNhd hopen
  set H : ℂ → ℂ := fun w => laplaceRay φ (w - 1 / 2)
  have hcomplete := cofinitePrimeLog_strongSectorBlaschkeComplete S 1 zero_le_one 1 one_ne_zero
  have hray := frequency_zero_uniqueness_on_ray (n := 1) one_ne_zero 1 hcomplete (H := H)
    (fun R hR z hz => by
      have hre := sectorRootMap_one_re_gt (R := R) hz
      have hin : sectorRootMap 1 R z - 1 / 2 ∈ {w : ℂ | 0 < w.re} := by
        simp only [Set.mem_setOf_eq, Complex.sub_re]
        norm_num
        linarith
      have hsub : AnalyticAt ℂ (fun z => sectorRootMap 1 R z - 1 / 2) z :=
        (sectorRootMap_analyticOnNhd 1 R z hz).sub analyticAt_const
      exact AnalyticAt.comp (g := laplaceRay φ) (f := fun z => sectorRootMap 1 R z - 1 / 2)
        (hana _ hin) hsub)
    (fun R hR => ⟨max 1 (rayL2Norm φ), le_max_left _ _, fun z hz => by
      have hre := sectorRootMap_one_re_gt (R := R) hz
      have hw : (0 : ℝ) < (sectorRootMap 1 R z - 1 / 2).re := by
        simp only [Complex.sub_re]
        norm_num
        linarith
      have hb := norm_laplaceRay_le hφ hw
      have hsq : 1 ≤ Real.sqrt (2 * (sectorRootMap 1 R z - 1 / 2).re) := by
        rw [Real.one_le_sqrt]
        simp only [Complex.sub_re] at hw ⊢
        norm_num at hw ⊢
        linarith
      calc ‖H (sectorRootMap 1 R z)‖ ≤ rayL2Norm φ /
            Real.sqrt (2 * (sectorRootMap 1 R z - 1 / 2).re) := hb
        _ ≤ rayL2Norm φ := div_le_self (rayL2Norm_nonneg φ) hsq
        _ ≤ max 1 (rayL2Norm φ) := le_max_right _ _⟩)
    (fun i _ => hL i.1 i.2)
  have hzero_ray : ∀ n : ℕ, laplaceRay φ ((2 : ℂ) + ((n : ℝ) + 1)⁻¹) = 0 := by
    intro n
    have := hray (5 / 2 + ((n : ℝ) + 1)⁻¹) (by
      have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      linarith)
    simp only [H] at this
    convert this using 2
    push_cast
    ring
  have hfreq : ∃ᶠ w in 𝓝[≠] (2 : ℂ), laplaceRay φ w = 0 := by
    have htend : Tendsto (fun n : ℕ => (2 : ℂ) + (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝[≠] 2) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using (tendsto_const_nhds (x := (2 : ℂ))).add
          (Complex.continuous_ofReal.tendsto 0 |>.comp h0)
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
    exact htend.frequently (Frequently.of_forall fun n => by exact_mod_cast hzero_ray n)
  have hconn : IsPreconnected {w : ℂ | 0 < w.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn
    (by simp : (2 : ℂ) ∈ {w : ℂ | 0 < w.re}) hfreq
  have hφ0 := ae_eq_zero_of_laplaceRay_eq_zero hφ fun w hw => heq hw
  refine Lp.ext ?_
  have hf0 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), (f : ℝ → ℂ) r = 0 := by
    filter_upwards [hφ0, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
    have hr' : (0 : ℝ) < r := hrpos
    have hne : ((r ^ (((k : ℝ) - 1) / 2) * Real.exp (-(r / 2)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_pos (Real.rpow_pos_of_pos hr' _) (Real.exp_pos _)).ne'
    exact (mul_eq_zero.1 hr).resolve_left hne
  filter_upwards [hf0, Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with r h1 h2
  rw [h1, h2]
  rfl

/-- **Theorem PPTI-F (PPTI.30).**  Cofinite prime clocks are total in every coherent degree. -/
theorem gammaCoherent_primeClock_total (k : ℕ) [NeZero k] (S : Finset Nat.Primes) :
    (Submodule.span ℂ (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      gammaCoherentVector k (primeClock_pos p.1))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  refine eq_zero_of_forall_inner_gammaCoherentVector_eq_zero k S f fun p hp => ?_
  exact (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)

end GaloisForLFunctions.HTGeometry
