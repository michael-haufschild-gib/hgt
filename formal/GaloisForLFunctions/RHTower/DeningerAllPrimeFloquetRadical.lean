import GaloisForLFunctions.RHTower.DeningerAllPrimeFloquetEnergy
import GaloisForLFunctions.RHTower.DeningerTomographyInjective

/-!
# The radical of the all-prime Floquet energy is zero

Each term of the energy is nonnegative, so a vanishing energy forces every term to vanish; a
continuous nonnegative integrand with zero integral vanishes on the open fundamental interval, and
continuity together with periodicity spreads that to the whole line.  Cofinal prime tomography then
forces the cochain itself to vanish.

* `continuous_eq_zero_of_intervalIntegral_normSq` : **zero energy on an interval kills a continuous
  function there.**
* `deningerPeriodizationSum_eq_zero_of_floquetTerm` : **a vanishing term kills the whole trace.**
* `deningerFloquetEnergy_eq_zero_iff` : **the radical of the all-prime energy is zero.**
-/

namespace RHTower

open SchwartzMap MeasureTheory Filter Topology

noncomputable section

/-- **A continuous function whose squared norm integrates to zero over an interval vanishes on its
interior.** -/
theorem continuous_eq_zero_of_intervalIntegral_normSq {f : ℝ → ℂ} (hf : Continuous f) {L : ℝ}
    (hL : 0 < L) (hzero : (∫ t in (0 : ℝ)..L, ‖f t‖ ^ 2) = 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) L, f t = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀, hne⟩ := hcon
  set g : ℝ → ℝ := fun t => ‖f t‖ ^ 2 with hg
  have hgcont : Continuous g := (hf.norm.pow 2)
  have hgnn : 0 ≤ g := fun t => by positivity
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) L) volume := by
    have := (hgcont.intervalIntegrable (μ := volume) (0 : ℝ) L)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le] at this
  have hgpos : 0 < g t₀ := by
    have : 0 < ‖f t₀‖ := norm_pos_iff.2 hne
    positivity
  -- an open set on which `g` is positive
  set U : Set ℝ := (g ⁻¹' Set.Ioi 0) ∩ Set.Ioo (0 : ℝ) L with hU
  have hUopen : IsOpen U := (hgcont.isOpen_preimage _ isOpen_Ioi).inter isOpen_Ioo
  have hUne : U.Nonempty := ⟨t₀, hgpos, ht₀⟩
  have hUsub : U ⊆ Function.support g ∩ Set.Ioc (0 : ℝ) L := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨ne_of_gt hx1, ⟨hx2.1, hx2.2.le⟩⟩
  have hUmeas : 0 < volume U := hUopen.measure_pos volume hUne
  have hsupp : MeasurableSet (Function.support g) :=
    (hgcont.isOpen_preimage _ isOpen_compl_singleton).measurableSet
  have hposint : 0 < ∫ t in Set.Ioc (0 : ℝ) L, g t := by
    rw [integral_pos_iff_support_of_nonneg (fun t => hgnn t) hint,
      Measure.restrict_apply hsupp]
    exact lt_of_lt_of_le hUmeas (measure_mono hUsub)
  rw [intervalIntegral.integral_of_le hL.le] at hzero
  exact absurd hzero (ne_of_gt hposint)

/-- **A vanishing Floquet term kills the whole prime trace.**  The trace vanishes on the open
fundamental interval, hence on its closure by continuity, hence everywhere by periodicity. -/
theorem deningerPeriodizationSum_eq_zero_of_floquetTerm {h : DeningerExpSchwartz} {q : ℕ}
    (hq : 2 ≤ q) (hterm : deningerFloquetTerm h q = 0) :
    ∀ t : ℝ, deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t = 0 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hqR
  have hLpos : 0 < Real.log q := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set S := deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) with hS
  have hcont : Continuous S := deningerPeriodizationSum_continuous (h := h) hLpos
  have hintzero : (∫ t in (0 : ℝ)..Real.log q, ‖S t‖ ^ 2) = 0 := by
    have hfac : ((q : ℝ) ^ 2)⁻¹ ≠ 0 := by positivity
    have := hterm
    rw [deningerFloquetTerm] at this
    exact (mul_eq_zero.1 this).resolve_left hfac
  have hIoo := continuous_eq_zero_of_intervalIntegral_normSq hcont hLpos hintzero
  -- spread to the closed interval
  have hIcc : ∀ t ∈ Set.Icc (0 : ℝ) (Real.log q), S t = 0 := by
    have hclosed : IsClosed {t : ℝ | S t = 0} := isClosed_eq hcont continuous_const
    have hsub : Set.Ioo (0 : ℝ) (Real.log q) ⊆ {t : ℝ | S t = 0} := hIoo
    have := hclosed.closure_subset_iff.2 hsub
    rwa [closure_Ioo (ne_of_lt hLpos)] at this
  -- spread to the line by periodicity
  intro t
  have hper : Function.Periodic S (Real.log q) := fun s =>
    deningerPeriodizationSum_periodic ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) s
  set n : ℤ := ⌊t / Real.log q⌋ with hn
  set s : ℝ := t - (n : ℝ) * Real.log q with hs
  have hsval : s = Real.log q * Int.fract (t / Real.log q) := by
    rw [hs, Int.fract, hn]
    field_simp
  have hs0 : 0 ≤ s := by
    rw [hsval]
    exact mul_nonneg hLpos.le (Int.fract_nonneg _)
  have hsL : s ≤ Real.log q := by
    rw [hsval]
    nlinarith [Int.fract_lt_one (t / Real.log q), Int.fract_nonneg (t / Real.log q)]
  have hshift : S (s + (n : ℝ) * Real.log q) = S s := hper.int_mul n s
  have hts : t = s + (n : ℝ) * Real.log q := by rw [hs]; ring
  rw [hts, hshift]
  exact hIcc s ⟨hs0, hsL⟩

/-- **The radical of the all-prime Floquet energy is zero.** -/
theorem deningerFloquetEnergy_eq_zero_iff (h : DeningerExpSchwartz) :
    deningerFloquetEnergy h = 0 ↔ h = 0 := by
  constructor
  · intro hzero
    have hterm : ∀ q : Nat.Primes, deningerFloquetTerm h (q : ℕ) = 0 := by
      intro q
      have hle : deningerFloquetTerm h (q : ℕ) ≤ deningerFloquetEnergy h :=
        (deningerFloquetTerm_summable h).le_tsum q
          fun j _ => deningerFloquetTerm_nonneg h j.2.one_lt.le
      have hnn := deningerFloquetTerm_nonneg h q.2.one_lt.le
      rw [hzero] at hle
      linarith
    have hcochain : ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) = 0 := by
      refine deningerCofinalPrimeTomography h.2 Nat.infinite_setOf_prime (fun p hp => hp) ?_
      intro p hp t
      exact deningerPeriodizationSum_eq_zero_of_floquetTerm (h := h) hp.two_le
        (hterm ⟨p, hp⟩) t
    exact Subtype.ext hcochain
  · rintro rfl
    have hzero : ∀ q : Nat.Primes, deningerFloquetTerm (0 : DeningerExpSchwartz) (q : ℕ) = 0 := by
      intro q
      have hper : ∀ t : ℝ, deningerPeriodizationSum
          (((0 : DeningerExpSchwartz) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log (q : ℕ)) t
          = 0 := by
        intro t
        rw [deningerPeriodizationSum]
        simp
      rw [deningerFloquetTerm]
      have hfun : (fun t : ℝ => ‖deningerPeriodizationSum
          (((0 : DeningerExpSchwartz) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log (q : ℕ)) t‖ ^ 2)
          = fun _ : ℝ => (0 : ℝ) := by
        funext t
        rw [hper t]
        simp
      rw [hfun]
      simp
    rw [deningerFloquetEnergy]
    rw [tsum_congr hzero]
    simp

end

end RHTower
