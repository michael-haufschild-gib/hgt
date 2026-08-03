import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance

/-!
# Bohr coefficients of an absolutely convergent exponential series

An absolutely convergent series of unimodular characters is a uniform limit of trigonometric
polynomials, so it is continuous and Bohr almost periodic, and every Bohr coefficient is the limit
of the coefficients of the partial sums.  With pairwise distinct frequencies the coefficient at one
frequency of the family is exactly the corresponding term.

Consequently the phases of such a series are determined by the series: two phase assignments of the
same nonvanishing amplitude family which produce the same function are equal.  This is the
Bohr--Fourier uniqueness which makes an infinite frequency hull injective.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*}

/-- An absolutely convergent exponential series with real frequencies. -/
def expSeriesCarrier (a : ι → ℂ) (omega : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' i, a i * expChar (omega i) t

theorem summable_expSeries {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (omega : ι → ℝ) (t : ℝ) :
    Summable fun i => a i * expChar (omega i) t := by
  refine Summable.of_norm_bounded ha fun i => ?_
  rw [norm_mul, norm_expChar, mul_one]

theorem continuous_expSeriesCarrier {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (omega : ι → ℝ) :
    Continuous (expSeriesCarrier a omega) := by
  refine continuous_tsum (fun i => continuous_const.mul (continuous_expChar (omega i))) ha ?_
  intro i t
  rw [norm_mul, norm_expChar, mul_one]

/-- The tail of the series is uniformly small. -/
theorem norm_expSeriesCarrier_sub_partial_le {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (omega : ι → ℝ) (S : Finset ι) (t : ℝ) :
    ‖expSeriesCarrier a omega t - ∑ i ∈ S, a i * expChar (omega i) t‖
      ≤ ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ := by
  classical
  have hsum := summable_expSeries ha omega t
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hdiff : expSeriesCarrier a omega t - ∑ i ∈ S, a i * expChar (omega i) t
      = ∑' i : ((S : Set ι)ᶜ : Set ι), a i * expChar (omega i) t := by
    rw [expSeriesCarrier, ← hsplit]
    ring
  rw [hdiff]
  have hnorm : Summable fun i : ((S : Set ι)ᶜ : Set ι) => ‖a i * expChar (omega i) t‖ := by
    refine Summable.of_norm_bounded (ha.subtype _) fun i => ?_
    rw [norm_norm, norm_mul, norm_expChar, mul_one]
    exact le_of_eq rfl
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  refine Summable.tsum_le_tsum (fun i => ?_) hnorm (ha.subtype _)
  rw [norm_mul, norm_expChar, mul_one]

/-- Absolute convergence makes the tail sums arbitrarily small. -/
theorem exists_finset_tsum_compl_lt {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Finset ι, ∀ T : Finset ι, S ⊆ T → ∑' i : ((T : Set ι)ᶜ : Set ι), ‖a i‖ < ε := by
  classical
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp ha.hasSum ε hε
  refine ⟨S, fun T hT => ?_⟩
  have hsplit := ha.sum_add_tsum_compl (s := T)
  have hdist := hS T hT
  rw [Real.dist_eq, abs_lt] at hdist
  have htail : ∑' i : ((T : Set ι)ᶜ : Set ι), ‖a i‖
      = (∑' i, ‖a i‖) - ∑ i ∈ T, ‖a i‖ := by
    rw [← hsplit]
    ring
  rw [htail]
  linarith [hdist.1]

theorem isBohrAlmostPeriodic_expSeriesCarrier {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (omega : ι → ℝ) : HTGeometry.IsBohrAlmostPeriodic (expSeriesCarrier a omega) := by
  classical
  refine HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt ha hε
  refine ⟨fun t => ∑ i ∈ S, a i * expChar (omega i) t, ?_, fun t => ?_⟩
  · exact isBohrAlmostPeriodic_sum _ (fun i _ => continuous_const.mul (continuous_expChar _))
      (fun i _ => isBohrAlmostPeriodic_const_mul (a i) (isBohrAlmostPeriodic_expChar _))
  · exact le_of_lt (lt_of_le_of_lt (norm_expSeriesCarrier_sub_partial_le ha omega S t)
      (hS S le_rfl))

/-- **The Bohr coefficient of an absolutely convergent exponential series.**  At a frequency of the
family with pairwise distinct frequencies it is the corresponding amplitude. -/
theorem bohrCoefficient_expSeriesCarrier {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    {omega : ι → ℝ} (hinj : Function.Injective omega) (k : ι) :
    bohrCoefficient (expSeriesCarrier a omega) (omega k) = a k := by
  classical
  have hcarrierC := continuous_expSeriesCarrier ha omega
  have hcarrierA := isBohrAlmostPeriodic_expSeriesCarrier ha omega
  have hclose : ∀ ε : ℝ, 0 < ε →
      ‖bohrCoefficient (expSeriesCarrier a omega) (omega k) - a k‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt ha hε
    set S' : Finset ι := insert k S with hS'def
    have hsub : S ⊆ S' := Finset.subset_insert k S
    have hpartialC : Continuous fun t => ∑ i ∈ S', a i * expChar (omega i) t :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_expChar _)
    have hpartialA : HTGeometry.IsBohrAlmostPeriodic fun t => ∑ i ∈ S', a i * expChar (omega i) t :=
      isBohrAlmostPeriodic_sum _ (fun i _ => continuous_const.mul (continuous_expChar _))
        (fun i _ => isBohrAlmostPeriodic_const_mul (a i) (isBohrAlmostPeriodic_expChar _))
    have hcoefPartial : bohrCoefficient (fun t => ∑ i ∈ S', a i * expChar (omega i) t) (omega k)
        = a k := by
      rw [bohrCoefficient_sum_expChar]
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro i _ hik
        rw [if_neg (fun hcon => hik (hinj hcon))]
      · intro hk
        exact absurd (Finset.mem_insert_self k S) hk
    have hbound : ∀ t, ‖expSeriesCarrier a omega t - ∑ i ∈ S', a i * expChar (omega i) t‖ ≤ ε := by
      intro t
      exact le_of_lt (lt_of_le_of_lt (norm_expSeriesCarrier_sub_partial_le ha omega S' t)
        (hS S' hsub))
    have hlip := norm_bohrCoefficient_sub_le hcarrierC hcarrierA hpartialC hpartialA hbound
      (omega k)
    rwa [hcoefPartial] at hlip
  by_contra hne
  have hpos : 0 < ‖bohrCoefficient (expSeriesCarrier a omega) (omega k) - a k‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have := hclose (‖bohrCoefficient (expSeriesCarrier a omega) (omega k) - a k‖ / 2) (by positivity)
  linarith

/-- **Bohr--Fourier uniqueness of the phases.**  Two phase assignments of the same nonvanishing
amplitude family which produce the same exponential series are equal. -/
theorem expSeriesCarrier_phase_injective {a : ι → ℂ} {omega : ι → ℝ} {lam mu : ι → ℂ}
    (halam : Summable fun i => ‖a i * lam i‖) (hamu : Summable fun i => ‖a i * mu i‖)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega)
    (h : expSeriesCarrier (fun i => a i * lam i) omega
      = expSeriesCarrier (fun i => a i * mu i) omega) :
    lam = mu := by
  funext k
  have hlam := bohrCoefficient_expSeriesCarrier halam hinj k
  have hmu := bohrCoefficient_expSeriesCarrier hamu hinj k
  rw [h, hmu] at hlam
  exact mul_left_cancel₀ (hane k) hlam.symm


/-- **Decay at one end forces equal phases.**  If two phase-modulated carriers of the same
nonvanishing amplitude family differ by a function decaying at `+∞`, the phases coincide: the
difference is Bohr almost periodic, hence identically zero.

This is the disjointness mechanism of an almost periodic boundary: an orbit point which converges to
a boundary point can only do so by being that boundary point. -/
theorem expSeriesCarrier_phase_eq_of_tendsto_zero {a : ι → ℂ} {omega : ι → ℝ} {lam mu : ι → ℂ}
    (halam : Summable fun i => ‖a i * lam i‖) (hamu : Summable fun i => ‖a i * mu i‖)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega)
    (hzero : Filter.Tendsto
      (fun t : ℝ => expSeriesCarrier (fun i => a i * lam i) omega t
        - expSeriesCarrier (fun i => a i * mu i) omega t) Filter.atTop (nhds 0)) :
    lam = mu := by
  have hlamC := continuous_expSeriesCarrier halam omega
  have hmuC := continuous_expSeriesCarrier hamu omega
  have hlamA := isBohrAlmostPeriodic_expSeriesCarrier halam omega
  have hmuA := isBohrAlmostPeriodic_expSeriesCarrier hamu omega
  have hdiffA : HTGeometry.IsBohrAlmostPeriodic
      (fun t => expSeriesCarrier (fun i => a i * lam i) omega t
        - expSeriesCarrier (fun i => a i * mu i) omega t) :=
    isBohrAlmostPeriodic_sub hlamC hlamA hmuC hmuA
  have hvanish := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hdiffA hzero
  refine expSeriesCarrier_phase_injective halam hamu hane hinj ?_
  funext t
  exact sub_eq_zero.mp (hvanish t)

end

end GaloisForLFunctions
