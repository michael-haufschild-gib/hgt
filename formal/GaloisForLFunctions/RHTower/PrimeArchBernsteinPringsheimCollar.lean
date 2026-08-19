import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSusceptibility
import GaloisForLFunctions.HTGeometry.VivantiPringsheim
import GaloisForLFunctions.HTGeometry.SegmentAnalyticContinuation

/-!
# The Pringsheim collar transfer

The complex Abel susceptibility germ `χ(z) = ∑_n Π_n z^n` has the *real* Abel critical radius as
its complex radius of convergence, because its coefficients are nonnegative.  Vivanti--Pringsheim
therefore makes the positive boundary point `R_A` a genuine singularity of the germ.

Consequently a *coherent holomorphic continuation of the germ through the whole positive real
collar* `[r₀, 1)` — with `r₀ = 250000/251001` the corpus's unconditional lower bound for `R_A` —
forces `R_A = 1` and hence the Riemann hypothesis.  The endpoint `t = 1` is deliberately not part
of the hypothesis.
-/

open Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The complex Abel susceptibility germ. -/
def primeArchEndpointBernsteinSusceptibility : ℂ → ℂ :=
  realSeriesSum primeArchEndpointBernsteinPurity

theorem primeArchEndpointBernsteinPurity_nonneg (n : ℕ) :
    0 ≤ primeArchEndpointBernsteinPurity n :=
  bernsteinCoefficientPurity_nonneg _ n

/-- Inside the real Abel radius the complex germ converges absolutely. -/
theorem summable_susceptibility_of_norm_lt {R : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) {z : ℂ} (hz : ‖z‖ < R) :
    Summable (fun n : ℕ => (primeArchEndpointBernsteinPurity n : ℂ) * z ^ n) := by
  refine Summable.of_norm ((hR.2.1 ‖z‖ (norm_nonneg z) hz).congr fun n => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeArchEndpointBernsteinPurity_nonneg n)]

/-- Outside the real Abel radius the complex germ diverges. -/
theorem not_summable_susceptibility_of_lt_norm {R : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) {z : ℂ} (hz : R < ‖z‖) :
    ¬ Summable (fun n : ℕ => (primeArchEndpointBernsteinPurity n : ℂ) * z ^ n) := by
  intro hsum
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (R + ‖z‖) / 2 := ⟨_, rfl⟩
  have hRt : R < t := by rw [ht]; linarith
  have htz : t < ‖z‖ := by rw [ht]; linarith
  have ht0 : 0 ≤ t := by
    have := hR.1
    rw [ht]; linarith
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (le_of_lt hR.1) hz
  -- the terms tend to zero, hence are bounded
  have htend := hsum.tendsto_atTop_zero
  have hnormtend : Filter.Tendsto
      (fun n : ℕ => ‖(primeArchEndpointBernsteinPurity n : ℂ) * z ^ n‖) Filter.atTop (nhds 0) := by
    simpa using htend.norm
  obtain ⟨C, hC0⟩ := hnormtend.bddAbove_range
  have hC : ∀ n : ℕ, primeArchEndpointBernsteinPurity n * ‖z‖ ^ n ≤ C := by
    intro n
    have := hC0 (Set.mem_range_self n)
    rwa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeArchEndpointBernsteinPurity_nonneg n)] at this
  have hCnn : 0 ≤ C := by
    have h0 := hC 0
    have := primeArchEndpointBernsteinPurity_nonneg 0
    simpa using le_trans (by simpa using this) h0
  refine hR.2.2 t hRt ?_
  have hgeo : Summable (fun n : ℕ => C * (t / ‖z‖) ^ n) := by
    refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
    exact (div_lt_one hzpos).mpr htz
  refine hgeo.of_nonneg_of_le (fun n => by
    have := primeArchEndpointBernsteinPurity_nonneg n
    positivity) (fun n => ?_)
  have hzn : (0 : ℝ) < ‖z‖ ^ n := by positivity
  have hkey : primeArchEndpointBernsteinPurity n * t ^ n
      = (primeArchEndpointBernsteinPurity n * ‖z‖ ^ n) * (t / ‖z‖) ^ n := by
    rw [div_pow]
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_right (hC n) (by positivity)

/-- **Vivanti--Pringsheim for the Abel susceptibility.**  The positive boundary point of the
susceptibility germ is a genuine singularity. -/
theorem not_continuesAcross_susceptibility {R : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) :
    ¬ ContinuesAcross primeArchEndpointBernsteinSusceptibility (Metric.ball 0 R) (R : ℂ) :=
  not_continuesAcross_of_nonneg primeArchEndpointBernsteinPurity_nonneg hR.1 hR.2.1 hR.2.2

/-- **The collar hypothesis.**  One coherent holomorphic continuation of the susceptibility germ
through the whole positive real collar, starting from a point strictly inside the unconditional
lower radius.  The endpoint `1` is not required. -/
def PrimeArchBernsteinCollarContinuation : Prop :=
  ∃ (U : Set ℂ) (F : ℂ → ℂ) (z₀ : ℝ),
    IsOpen U ∧ AnalyticOnNhd ℂ F U ∧
    0 ≤ z₀ ∧ z₀ < 250000 / 251001 ∧
    (∀ t : ℝ, z₀ ≤ t → t < 1 → (t : ℂ) ∈ U) ∧
    F =ᶠ[nhds ((z₀ : ℝ) : ℂ)] primeArchEndpointBernsteinSusceptibility

theorem analyticOnNhd_susceptibility {R : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) :
    AnalyticOnNhd ℂ primeArchEndpointBernsteinSusceptibility (Metric.ball 0 R) := by
  refine analyticOnNhd_realSeriesSum hR.1 fun s hs0 hsR => ?_
  refine (hR.2.1 s hs0 hsR).congr fun n => ?_
  rw [abs_of_nonneg (primeArchEndpointBernsteinPurity_nonneg n)]

/-- **(4) The collar transfer.**  A coherent holomorphic continuation of the susceptibility germ
through the positive real collar implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_collarContinuation
    (h : PrimeArchBernsteinCollarContinuation) : RiemannHypothesis := by
  obtain ⟨U, F, z₀, hUopen, hFan, hz₀0, hz₀r, hUseg, hFagree⟩ := h
  obtain ⟨R, ⟨hRlow, hRle, hRcrit, hRHiff⟩, -⟩ :=
    existsUnique_primeArchEndpointBernsteinAbelCriticalRadius
  by_contra hnot
  have hRne : R ≠ 1 := fun hc => hnot (hRHiff.mpr hc)
  have hR1 : R < 1 := lt_of_le_of_ne hRle hRne
  have hz₀R : z₀ < R := lt_trans hz₀r hRlow
  have hRU : ((R : ℝ) : ℂ) ∈ U := hUseg R (le_of_lt hz₀R) hR1
  obtain ⟨ζ, hζ, hζU⟩ := Metric.isOpen_iff.mp hUopen _ hRU
  have hfan := analyticOnNhd_susceptibility hRcrit
  -- the interior endpoint of the propagation segment
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = R - (min ζ (R - z₀)) / 2 := ⟨_, rfl⟩
  have hminpos : 0 < min ζ (R - z₀) := lt_min hζ (by linarith)
  have hcR : c < R := by rw [hc]; linarith
  have hz₀c : z₀ ≤ c := by
    rw [hc]
    have h1 : min ζ (R - z₀) ≤ R - z₀ := min_le_right _ _
    linarith
  have hcζ : R - c < ζ := by
    rw [hc]
    have h1 : min ζ (R - z₀) ≤ ζ := min_le_left _ _
    linarith
  -- propagate the agreement along the real segment
  have hVopen : IsOpen (U ∩ Metric.ball (0 : ℂ) R) := hUopen.inter Metric.isOpen_ball
  have hseg : ∀ t : ℝ, t ∈ Set.Icc z₀ c → ((t : ℝ) : ℂ) ∈ U ∩ Metric.ball (0 : ℂ) R := by
    intro t ht
    refine ⟨hUseg t ht.1 (by linarith [ht.2]), ?_⟩
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans hz₀0 ht.1)]
    linarith [ht.2]
  have hprop : F =ᶠ[nhds ((c : ℝ) : ℂ)] primeArchEndpointBernsteinSusceptibility :=
    eventuallyEq_of_segment hVopen (hFan.mono Set.inter_subset_left)
      (hfan.mono Set.inter_subset_right) hz₀c hseg hFagree
  -- transfer to a two-sided neighbourhood of the boundary point
  set C : Set ℂ := Metric.ball ((R : ℝ) : ℂ) ζ ∩ Metric.ball (0 : ℂ) R with hC
  have hCconv : Convex ℝ C := (convex_ball _ _).inter (convex_ball _ _)
  have hcC : ((c : ℝ) : ℂ) ∈ C := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq,
        show ((c : ℝ) : ℂ) - ((R : ℝ) : ℂ) = (((c - R : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans hz₀0 hz₀c)]
      exact hcR
  have hEqC : Set.EqOn F primeArchEndpointBernsteinSusceptibility C :=
    (hFan.mono (fun z hz => hζU hz.1)).eqOn_of_preconnected_of_eventuallyEq
      (hfan.mono Set.inter_subset_right) hCconv.isPreconnected hcC hprop
  -- this is a continuation across the boundary point
  refine not_continuesAcross_susceptibility hRcrit ⟨F, hFan _ hRU, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds ((R : ℝ) : ℂ) hζ] with w hw hw2
  exact hEqC ⟨hw, hw2⟩

end

end RHTower
