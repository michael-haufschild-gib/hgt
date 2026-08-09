import GaloisForLFunctions.HTGeometry.AnseloneKorevaarTranslationRank
import GaloisForLFunctions.HTGeometry.EntireExponentialCompositionDA
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA

/-!
# Active charge rank of a two-body dressing phase

A two-particle dressing produced from `N` additive one-particle charge profiles `q₁,…,q_N` by a
fixed bilinear form `Ω` has kernel `K(x,y) = ∑_{a,b} Ω_{ab} q_a(x) q_b(y)`, and boost invariance
makes it a function `Φ(x−y)` of the rapidity difference alone.  The *active charge rank* of `Φ` is
the least `N` admitting such a factorization.

* `translationSpan_le_span_of_bilinearChargeKernel` — every translate of `Φ` lies in the span of
  the charge profiles, so the translation rank is at most `N`.
* `finrank_translationSpan_le_of_bilinearChargeFactorization` — the numerical bound.
* `not_finiteDimensional_translationSpan_of_hypertranscendental` — if the elastic scattering
  function `S = ε·exp(i Φ)` is hypertranscendental then `Φ` has infinite translation rank: finite
  rank would make `Φ` an exponential polynomial, hence `S` differentially algebraic.
* `not_bilinearChargeFactorization_of_hypertranscendental` — consequently no finite bilinear
  charge dressing produces a hypertranscendental elastic phase.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators
open Filter Topology

/-! ## Finite bilinear charge dressings -/

/-- `Φ` admits a bilinear dressing by `N` additive charge profiles. -/
def BilinearChargeFactorization (Φ : ℝ → ℂ) (N : ℕ) : Prop :=
  ∃ (q : Fin N → ℝ → ℂ) (Ω : Fin N → Fin N → ℂ),
    ∀ x y : ℝ, Φ (x - y) = ∑ a, ∑ b, Ω a b * q a x * q b y

/-- **Theorem A.**  Every translate of a bilinearly dressed phase lies in the span of the charge
profiles. -/
theorem translationSpan_le_span_of_bilinearChargeKernel {N : ℕ} {Φ : ℝ → ℂ}
    {q : Fin N → ℝ → ℂ} {Ω : Fin N → Fin N → ℂ}
    (hK : ∀ x y : ℝ, Φ (x - y) = ∑ a, ∑ b, Ω a b * q a x * q b y) :
    translationSpan Φ ≤ Submodule.span ℂ (Set.range q) := by
  rw [translationSpan, Submodule.span_le]
  rintro u ⟨y, rfl⟩
  have hrow : realTranslate y Φ = ∑ a, (∑ b, Ω a b * q b y) • q a := by
    funext x
    rw [realTranslate_apply, hK x y]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  show realTranslate y Φ ∈ Submodule.span ℂ (Set.range q)
  rw [hrow]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem finiteDimensional_translationSpan_of_bilinearChargeFactorization {N : ℕ} {Φ : ℝ → ℂ}
    (h : BilinearChargeFactorization Φ N) : FiniteDimensional ℂ (translationSpan Φ) := by
  obtain ⟨q, Ω, hK⟩ := h
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range q)) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range q)
  exact Submodule.finiteDimensional_of_le (translationSpan_le_span_of_bilinearChargeKernel hK)

/-- **Theorem A, numerical form.**  Finite active charge rank `N` bounds the translation rank
by `N`. -/
theorem finrank_translationSpan_le_of_bilinearChargeFactorization {N : ℕ} {Φ : ℝ → ℂ}
    (h : BilinearChargeFactorization Φ N) : Module.finrank ℂ (translationSpan Φ) ≤ N := by
  classical
  obtain ⟨q, Ω, hK⟩ := h
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range q)) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range q)
  have hle := Submodule.finrank_mono (translationSpan_le_span_of_bilinearChargeKernel hK)
  refine le_trans hle ?_
  have hcard := finrank_span_le_card (R := ℂ) (Set.range q)
  refine le_trans hcard ?_
  rw [Set.toFinset_range]
  exact le_trans Finset.card_image_le (by simp)

/-! ## Differential algebraicity of entire exponential polynomials -/

theorem differentiallyAlgebraic_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    DifferentiallyAlgebraic (polyExpC P μ) := by
  have hcomm : polyExpC P μ = fun s => Complex.exp (μ * s) * P.eval s := by
    funext z
    rw [polyExpC_apply, mul_comm]
  rw [hcomm]
  exact differentiallyAlgebraic_cexp_mul_polynomial μ P

theorem differentiallyAlgebraic_of_mem_expPolySpaceC {G : ℂ → ℂ} (hG : G ∈ expPolySpaceC) :
    DifferentiallyAlgebraic G := by
  induction hG using Submodule.span_induction with
  | mem F hF => obtain ⟨p, rfl⟩ := hF; exact differentiallyAlgebraic_polyExpC p.1 p.2
  | zero =>
      have hz : (0 : ℂ → ℂ) = fun _ : ℂ => (0 : ℂ) := rfl
      rw [hz]
      exact differentiallyAlgebraic_const (0 : ℂ)
  | add F H hF hH ihF ihH =>
      have hFa := analyticOnNhd_of_mem_expPolySpaceC hF
      have hHa := analyticOnNhd_of_mem_expPolySpaceC hH
      exact differentiallyAlgebraic_add hFa hHa ihF ihH
  | smul c F hF ihF =>
      have hFa := analyticOnNhd_of_mem_expPolySpaceC hF
      have hsm : (c • F) = fun z : ℂ => c * F z := rfl
      rw [hsm]
      exact differentiallyAlgebraic_mul analyticOnNhd_const hFa
        (differentiallyAlgebraic_const c) ihF

/-! ## Entire functions agreeing on the real line -/

/-- **Identity theorem across the real axis.**  Two entire functions that agree at every real
point agree everywhere: the real points accumulate at the origin. -/
theorem eq_of_eqOn_real {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ))
    (hh : AnalyticOnNhd ℂ h (Set.univ : Set ℂ)) (hre : ∀ x : ℝ, g (x : ℂ) = h (x : ℂ)) :
    g = h := by
  have hreal : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcplx : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.tendsto' 0 0 (by simp)
      exact hc.comp hreal
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have hz : (1 / ((n : ℝ) + 1) : ℝ) = 0 := by exact_mod_cast hc
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = h z :=
    hcplx.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => hre _))
  funext z
  exact hg.eqOn_of_preconnected_of_frequently_eq hh isPreconnected_univ (Set.mem_univ 0) hfreq
    (Set.mem_univ z)

/-! ## Theorem C -/

/-- **Theorem C.**  If the elastic scattering function `S`, entire and equal to `ε·exp(i Φ)` on the
real rapidity axis, is hypertranscendental, then the continuous phase `Φ` has infinite translation
rank. -/
theorem not_finiteDimensional_translationSpan_of_hypertranscendental
    {Φ : ℝ → ℂ} (hΦ : Continuous Φ) {ε : ℂ} {S : ℂ → ℂ}
    (hS : AnalyticOnNhd ℂ S (Set.univ : Set ℂ))
    (hSre : ∀ x : ℝ, S (x : ℂ) = ε * Complex.exp (Complex.I * Φ x))
    (hHT : Hypertranscendental S) :
    ¬ FiniteDimensional ℂ (translationSpan Φ) := by
  intro hfin
  apply hHT
  have hΦexp : Φ ∈ expPolySpace :=
    (mem_expPolySpace_iff_finiteDimensional_translationSpan hΦ).2 hfin
  obtain ⟨G, hGmem, hGeq⟩ := exists_entire_extension hΦexp
  have hGan : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) := analyticOnNhd_of_mem_expPolySpaceC hGmem
  have hGDA : DifferentiallyAlgebraic G := differentiallyAlgebraic_of_mem_expPolySpaceC hGmem
  have hIGan : AnalyticOnNhd ℂ (fun z => Complex.I * G z) (Set.univ : Set ℂ) :=
    analyticOnNhd_const.mul hGan
  have hIGDA : DifferentiallyAlgebraic (fun z => Complex.I * G z) :=
    differentiallyAlgebraic_mul analyticOnNhd_const hGan
      (differentiallyAlgebraic_const Complex.I) hGDA
  have hexpDA : DifferentiallyAlgebraic (fun z => Complex.exp (Complex.I * G z)) :=
    differentiallyAlgebraic_cexp_comp hIGan hIGDA
  have hTan : AnalyticOnNhd ℂ (fun z => ε * Complex.exp (Complex.I * G z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_const.mul hIGan.cexp
  have hTDA : DifferentiallyAlgebraic (fun z => ε * Complex.exp (Complex.I * G z)) :=
    differentiallyAlgebraic_mul analyticOnNhd_const hIGan.cexp
      (differentiallyAlgebraic_const ε) hexpDA
  have hST : S = fun z => ε * Complex.exp (Complex.I * G z) := by
    refine eq_of_eqOn_real hS hTan ?_
    intro x
    rw [hSre x, hGeq x]
  rw [hST]
  exact hTDA

/-- **Theorem C, source form.**  A hypertranscendental elastic scattering function admits no finite
bilinear charge dressing of its phase. -/
theorem not_bilinearChargeFactorization_of_hypertranscendental
    {Φ : ℝ → ℂ} (hΦ : Continuous Φ) {ε : ℂ} {S : ℂ → ℂ}
    (hS : AnalyticOnNhd ℂ S (Set.univ : Set ℂ))
    (hSre : ∀ x : ℝ, S (x : ℂ) = ε * Complex.exp (Complex.I * Φ x))
    (hHT : Hypertranscendental S) (N : ℕ) :
    ¬ BilinearChargeFactorization Φ N := fun hfac =>
  not_finiteDimensional_translationSpan_of_hypertranscendental hΦ hS hSre hHT
    (finiteDimensional_translationSpan_of_bilinearChargeFactorization hfac)

end

end GaloisForLFunctions.HTGeometry
