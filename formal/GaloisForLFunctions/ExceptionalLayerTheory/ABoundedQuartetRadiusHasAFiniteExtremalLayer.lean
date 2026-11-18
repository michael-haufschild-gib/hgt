import GaloisForLFunctions.ExceptionalLayerTheory.IncommensurableTopOrdinatesExcludeTheQuartetRadius
import GaloisForLFunctions.ExceptionalLayerTheory.DistinctExtremalOrdinatesHaveDistinctQuarterStepPhases
import GaloisForLFunctions.RHTower.GaussHodgeVerticalExtraction
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise

/-!
# A bounded quartet radius and the extremal layer

A finite number of ordinates can share each sampled phase. The component of a
boundary increment at that phase is therefore analytic. An exact return on
all lattice translates of an open interval determines all its components.
-/

noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A summable discrete pencil with all moments zero has zero mass at each phase. -/
private theorem phase_mass_zero {ι : Type*} {c w : ι → ℂ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, ‖w i‖ = 1)
    (hm : ∀ k : ℕ, (∑' i, c i * w i ^ k) = 0) (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' i, if w i = z then c i else 0) = 0 := by
  classical
  let u := fun i => w i / z
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz.symm ▸ zero_lt_one)
  have hu (i : ι) : ‖u i‖ = 1 := by simp only [u, norm_div, hw, hz, div_self one_ne_zero]
  have hu1 (i : ι) : u i = 1 ↔ w i = z := div_eq_one_iff_eq hz0
  have hs (k : ℕ) : Summable (fun i => c i * u i ^ k) := by
    apply Summable.of_norm_bounded hc
    intro i
    rw [norm_mul, norm_pow, hu, one_pow, mul_one]
  have hm' (k : ℕ) : (∑' i, c i * u i ^ k) = 0 := by
    simp only [u, div_pow, ← mul_div_assoc, tsum_div_const, hm, zero_div]
  let A := fun (N : ℕ) (v : ℂ) => ((N : ℝ)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, v^k
  have hzero (N : ℕ) : (∑' i, c i * A N (u i)) = 0 := by
    calc _ = ((N : ℝ)⁻¹ : ℂ) * ∑' i, ∑ k ∈ Finset.range N, c i * u i^k := by
               rw [← tsum_mul_left]
               apply tsum_congr
               intro i
               simp only [A, ← Finset.mul_sum]
               ring
      _ = ((N : ℝ)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, ∑' i, c i * u i^k := by
            rw [Summable.tsum_finsetSum fun k _ => hs k]
      _ = 0 := by simp only [hm', Finset.sum_const_zero, mul_zero]
  have hpoint (i : ι) : Tendsto (fun N => c i * A N (u i)) atTop
      (𝓝 (if w i = z then c i else 0)) := by
    have h := (tendsto_complex_geom_cesaro_of_norm_eq_one (u i) (hu i)).const_mul (c i)
    by_cases he : w i = z
    · simpa only [A, if_pos he, if_pos ((hu1 i).mpr he), mul_one] using h
    · simpa only [A, if_neg he, if_neg (fun h => he ((hu1 i).mp h)), mul_zero] using h
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ i, ‖c i * A N (u i)‖ ≤ ‖c i‖ := by
    refine .of_forall fun N i => ?_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_cesaro_geom_le_one (hu i) N)
      (norm_nonneg (c i))).trans_eq (mul_one _)
  have hlim := tendsto_tsum_of_dominated_convergence hc hpoint hdom
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem char_time_add (ω t p : ℝ) :
    expChar ω (t+p) = expChar ω t * expChar ω p := by
  simp only [expChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem char_time_nat (ω p : ℝ) (n : ℕ) :
    expChar ω (n*p) = expChar ω p ^ n := by
  induction n with
  | zero => simp [expChar]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, char_time_add, ih, pow_succ]

/-- With finite occupied fibres for the sampled phases, vanishing on all lattice
translates of one open interval determines the entire exponential series. -/
private theorem zero_of_vanishing_on_translated_interval {ι : Type*}
    (a : ι → ℂ) (ω : ι → ℝ) (ha : Summable fun i => ‖a i‖) (p t₀ : ℝ)
    (hfinite : ∀ z : ℂ, {i | a i ≠ 0 ∧ expChar (ω i) p = z}.Finite)
    (hzero : ∀ᶠ t in 𝓝 t₀, ∀ n : ℕ, expSeriesCarrier a ω (t+n*p) = 0) :
    ∀ t, expSeriesCarrier a ω t = 0 := by
  classical
  let w := fun i => expChar (ω i) p
  have hsum (t : ℝ) : Summable fun i => ‖a i * expChar (ω i) t‖ := by
    simpa only [norm_mul, norm_expChar, mul_one] using ha
  have hpiece (z : ℂ) : ∀ t, (∑' i, if w i = z then a i * expChar (ω i) t else 0) = 0 := by
    let S := (hfinite z).toFinset
    have hform (t : ℝ) : (∑' i, if w i = z then a i * expChar (ω i) t else 0) =
        ∑ i ∈ S, a i * expChar (ω i) t := by
      rw [tsum_eq_sum (s := S) (fun j hj => by
        by_cases he : w j = z
        · have hz : a j = 0 := by
            by_contra hn
            exact hj ((hfinite z).mem_toFinset.mpr ⟨hn,he⟩)
          simp only [he, if_true, hz, zero_mul]
        · exact if_neg he)]
      apply Finset.sum_congr rfl
      intro j hj
      exact if_pos ((hfinite z).mem_toFinset.mp hj).2
    have hloc : (fun t => ∑ i ∈ S, a i * expChar (ω i) t) =ᶠ[𝓝 t₀] (fun _ => 0) := by
      filter_upwards [hzero] with t ht
      rw [← hform]
      by_cases hz : ‖z‖ = 1
      · apply phase_mass_zero (hsum t) (fun i => norm_expChar (ω i) p) _ z hz
        intro n
        simpa only [expSeriesCarrier, char_time_add, char_time_nat, w, mul_assoc] using ht n
      · apply tsum_eq_zero
        intro i
        exact if_neg fun h => hz (h ▸ norm_expChar (ω i) p)
    have hpoly : AnalyticOnNhd ℝ (fun t => ∑ i ∈ S, a i * expChar (ω i) t) Set.univ := by
      intro x _
      apply Finset.analyticAt_fun_sum
      intro i _
      unfold expChar
      fun_prop
    have hglobal := hpoly.eq_of_eventuallyEq analyticOnNhd_const hloc
    intro t
    exact (hform t).trans (congrFun hglobal t)
  intro t
  let f := fun i => a i * expChar (ω i) t
  have hf : Summable f := Summable.of_norm (hsum t)
  have hsub (z : ℂ) : (∑' i : {i // w i = z}, f i.val) = 0 := by
    rw [tsum_subtype]
    simpa only [Set.indicator, Set.mem_setOf_eq, f] using hpiece z t
  have hs := ((Equiv.sigmaFiberEquiv w).summable_iff (f := f)).mpr hf
  change ∑' i, f i = 0
  rw [← (Equiv.sigmaFiberEquiv w).tsum_eq f, hs.tsum_sigma]
  change (∑' z : ℂ, ∑' i : {i // w i = z}, f i.val) = 0
  simp only [hsub, tsum_zero]

/-- Finite phase fibres prevent independent sign choices on successive periods of |D|. -/
private theorem periodic_multiple_of_finite_phase_fibers {ι : Type*} {D : ℝ → ℝ}
    (hc : Continuous D) (a : ι → ℂ) (ω : ι → ℝ) (ha : Summable fun i => ‖a i‖)
    (hrep : ∀ t : ℝ, (D t : ℂ) = expSeriesCarrier a ω t) (p : ℝ)
    (hper : Function.Periodic (fun t => |D t|) p)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∀ t, |D (t+n*p)-D t| ≤ ε)
    (hfinite : ∀ z : ℂ, {i | a i ≠ 0 ∧ expChar (ω i) p = z}.Finite) :
    ∃ n : ℕ, 0 < n ∧ Function.Periodic D (n*p) := by
  classical
  by_cases h0 : ∀ t, D t = 0
  · exact ⟨1, Nat.one_pos, fun t => (h0 _).trans (h0 t).symm⟩
  push_neg at h0
  obtain ⟨t₀, h0⟩ := h0
  obtain ⟨n,hn,hclose⟩ := hreturn (|D t₀|/2) (half_pos (abs_pos.mpr h0))
  let b := fun i => a i * (expChar (ω i) (n*p)-1)
  have hb : Summable fun i => ‖b i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (ha.mul_right 2)
    rw [show ‖b i‖ = ‖a i‖ * ‖expChar (ω i) (n*p)-1‖ from norm_mul _ _]
    exact mul_le_mul_of_nonneg_left (by simpa only [norm_expChar, norm_one, one_add_one_eq_two]
      using norm_sub_le (expChar (ω i) (n*p)) 1) (norm_nonneg _)
  have hdiff (t : ℝ) : ((D (t+n*p)-D t : ℝ) : ℂ) = expSeriesCarrier b ω t := by
    rw [Complex.ofReal_sub, hrep, hrep]
    simp only [expSeriesCarrier]
    rw [← (summable_expSeries ha ω (t+n*p)).tsum_sub (summable_expSeries ha ω t)]
    apply tsum_congr
    intro i
    rw [char_time_add]
    dsimp only [b]
    ring
  have hbf (z : ℂ) : {i | b i ≠ 0 ∧ expChar (ω i) p = z}.Finite :=
    (hfinite z).subset fun i hi => ⟨fun h => hi.1 (by simp only [b,h,zero_mul]), hi.2⟩
  have hloc : ∀ᶠ t in 𝓝 t₀, |D t₀|/2 < |D t| :=
    hc.abs.continuousAt.eventually (lt_mem_nhds (half_lt_self (abs_pos.mpr h0)))
  have hzero : ∀ᶠ t in 𝓝 t₀, ∀ k : ℕ, expSeriesCarrier b ω (t+k*p) = 0 := by
    filter_upwards [hloc] with t ht
    intro k
    rw [← hdiff]
    apply Complex.ofReal_eq_zero.mpr
    apply sub_eq_zero.mpr
    have he := hper.nat_mul n (t+k*p)
    change |D (t+k*p+n*p)| = |D (t+k*p)| at he
    rcases abs_eq_abs.mp he with he | he
    · exact he
    · have h := hclose (t+k*p)
      rw [he, show -D (t+k*p) - D (t+k*p) = -(2*D (t+k*p)) by ring,
        abs_neg, abs_mul, abs_of_pos zero_lt_two, hper.nat_mul k t] at h
      linarith only [ht,h, abs_nonneg (D t)]
  refine ⟨n,hn,fun t => sub_eq_zero.mp (Complex.ofReal_eq_zero.mp ?_)⟩
  rw [hdiff]
  exact zero_of_vanishing_on_translated_interval b ω hb p t₀ hbf hzero t

end GaloisForLFunctions.ExceptionalLayerTheory
