import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalLogarithmicWindows

/-!
# The total dual section height over a prime window

A single nonnegative sum at a common multiplicity controls all but a
power-saving number of prime pairs in a selected window. Exceptional
prime-window detection then bounds the real parts of the zeros.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality Zeta23
open ArithmeticScatteringHolography RenormalizedIntersectionTheory ArithmeticOrientationGeometry SquareRootThreshold

/-- Prime conductors in a logarithmic observation window. -/
def primeWindow (T : ℝ) : Finset ℕ :=
  (range (⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ |Real.log p - T| ≤ primeLogarithmicRadius T)

theorem mem_primeWindow {p : ℕ} {T : ℝ} :
    p ∈ primeWindow T ↔ p.Prime ∧ |Real.log p - T| ≤ primeLogarithmicRadius T := by
  rw [primeWindow, mem_filter]
  refine ⟨And.right, fun h => ⟨?_,h⟩⟩
  rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.exp_pos _).le]
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr h.1.pos
  apply (Real.log_le_iff_le_exp hp).mp
  linarith only [(abs_le.mp h.2).2]

/-- Sum of natural dual heights, normalized by the common multiplicity. -/
def windowDualMass (T : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ primeWindow T, (dualCount (m • primePair p) : ℝ) / (m : ℝ)^2

private def primeDeficit (p : ℕ) : ℝ := max (-integerProbe (p+1) (primePair p)) 0

private theorem tendsto_windowDualMass (T : ℝ) :
    Tendsto (windowDualMass T) atTop (𝓝 (∑ p ∈ primeWindow T, primeDeficit p)) := by
  unfold windowDualMass
  exact tendsto_finsetSum _ fun p _ => dualCount_tateLimit (primePair p)

/-- The total dual height has at most the exponent of the number of
possible conductor degrees, on arbitrarily late prime windows. -/
def primeWindowMassBound : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
    ∃ᶠ m : ℕ in atTop, windowDualMass T m ≤ Real.exp ((1+η)*T)

private theorem window_deficit_bound {T A : ℝ} (h : ∃ᶠ m : ℕ in atTop, windowDualMass T m ≤ A) :
    ∑ p ∈ primeWindow T, primeDeficit p ≤ A := by
  by_contra! hlt
  obtain ⟨m,hm,hm'⟩ := (h.and_eventually ((tendsto_windowDualMass T).eventually_const_lt hlt)).exists
  exact hm.not_gt hm'

private theorem late_window_shape : ∃ T₀ : ℝ, ∀ T ≥ T₀, primeLogarithmicRadius T ≤ T/2 := by
  apply eventually_atTop.mp
  filter_upwards [primeLogarithmicRadius_div_tendsto_zero.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/2), eventually_gt_atTop (0 : ℝ)] with T hr hT
  have hh := (div_lt_iff₀ hT).mp hr
  linarith only [hh]

/-- Markov's inequality on the common quadratic coefficient. -/
private theorem count_large_deficits {T σ : ℝ} (hshape : primeLogarithmicRadius T ≤ T/2)
    (hσ : 0 ≤ σ) (h : ∑ p ∈ primeWindow T, primeDeficit p ≤ Real.exp ((1+σ/4)*T)) :
    let E := (primeWindow T).filter (fun p : ℕ => (p : ℝ)^σ < primeDeficit p)
    (E.card : ℝ) ≤ Real.exp ((1-σ/4)*T) := by
  let E := (primeWindow T).filter (fun p : ℕ => (p : ℝ)^σ < primeDeficit p)
  change (E.card : ℝ) ≤ _
  have hsum : (E.card : ℝ) * Real.exp (σ*T/2) ≤ ∑ p ∈ primeWindow T, primeDeficit p := by
    calc (E.card : ℝ) * Real.exp (σ*T/2) = ∑ _p ∈ E, Real.exp (σ*T/2) := by simp
      _ ≤ ∑ p ∈ E, primeDeficit p := sum_le_sum fun p hp => by
        obtain ⟨hpW,hpD⟩ := mem_filter.mp hp
        obtain ⟨hpp,hw⟩ := mem_primeWindow.mp hpW
        apply le_trans _ hpD.le
        rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hpp.pos)]
        apply Real.exp_le_exp.mpr
        have hl : T/2 ≤ Real.log p := by linarith only [(abs_le.mp hw).1,hshape]
        linarith only [mul_le_mul_of_nonneg_right hl hσ]
      _ ≤ ∑ p ∈ primeWindow T, primeDeficit p :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => le_max_right _ _)
  have he : Real.exp ((1+σ/4)*T) = Real.exp ((1-σ/4)*T) * Real.exp (σ*T/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp ((hsum.trans h).trans_eq he)

private theorem width_of_windowDualMass (h : primeWindowMassBound) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1/2) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1/2 + σ := by
  apply (zeta_re_le_iff_prime_logarithmic_power_windows_off_finset hσ.le
    (δ := 1-σ/4) (by linarith) (by linarith)).mpr
  let D := 2*(splineSeries 0).re
  refine ⟨1+|D|,1,zero_le_one, fun U => ?_⟩
  obtain ⟨T₀,hshape⟩ := late_window_shape
  obtain ⟨T,hT,hm⟩ := h (σ/4) (by positivity) (max U T₀)
  let E := (primeWindow T).filter (fun p : ℕ => (p : ℝ)^σ < primeDeficit p)
  refine ⟨T,E,(le_max_left _ _).trans hT,?_,?_⟩
  · rw [one_mul]
    exact count_large_deficits (hshape T ((le_max_right _ _).trans hT)) hσ.le (window_deficit_bound hm)
  · intro p hp hE hw
    have hd : primeDeficit p ≤ (p : ℝ)^σ := le_of_not_gt fun hgt =>
      hE (mem_filter.mpr ⟨mem_primeWindow.mpr ⟨hp,hw⟩,hgt⟩)
    have hq : -(p : ℝ)^σ ≤ integerProbe (p+1) (primePair p) := by
      linarith only [(le_max_left (-integerProbe (p+1) (primePair p)) 0).trans hd]
    have hpσ : 1 ≤ (p : ℝ)^σ := Real.one_le_rpow (by exact_mod_cast hp.one_le) hσ.le
    have he : 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re =
        integerProbe (p+1) (primePair p) - D := by
      rw [← orbitCorr_eq_re_lagStructure_spline, orbitCorr_splineCycle_eq, integerProbe_primePair hp.pos]
      unfold D
      ring
    rw [he]
    calc -((1+|D|)*(p : ℝ)^σ) ≤ -(p : ℝ)^σ - |D| := by
           linarith only [mul_le_mul_of_nonneg_left hpσ (abs_nonneg D)]
         _ ≤ _ := sub_le_sub hq (le_abs_self _)

/-- Arbitrarily sparse common-multiplicity tests of the summed dual
heights suffice. No individual upper bound on each summand is required. -/
theorem riemannHypothesis_iff_primeWindowMassBound : RiemannHypothesis ↔ primeWindowMassBound := by
  constructor
  · intro h η hη U
    refine ⟨U,le_rfl,?_⟩
    have hl := tendsto_windowDualMass U
    have hz (p : ℕ) : primeDeficit p = 0 :=
      max_eq_right (neg_nonpos.mpr (riemannHypothesis_iff_integerProbes.mp h _ _))
    simp only [hz, sum_const_zero] at hl
    exact ((hl.eventually_lt_const (Real.exp_pos _)).mono fun _ hx => hx.le).frequently
  · intro h
    apply riemannHypothesis_of_forall_re_le
    intro ρ hρ
    by_contra! hρ'
    have hs : 0 < (ρ.re-1/2)/2 := by linarith only [hρ']
    have hs' : (ρ.re-1/2)/2 < 1/2 := by linarith only [(zetaZeroConfig.strip ρ hρ).2]
    linarith only [hρ', width_of_windowDualMass h hs hs' ρ hρ]

#print axioms riemannHypothesis_iff_primeWindowMassBound

end GaloisForLFunctions.CountingHolography.Sections
