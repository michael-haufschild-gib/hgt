import GaloisForLFunctions.RHTower.XiMassFullAdjacentPrimeGraph
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeCone
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore

/-!
# Full adjacent-prime connection current

Finite Abel summation leaves a terminal product of the Fourier profile with cumulative critical
prime mass.  The sharp unconditional Chebyshev-scale bound on that mass and any interior strip
shift deeper than one half force this terminal product to zero.  Hence the complete valuation-one
prime source is exactly the infinite cumulative-mass-weighted gradient current on the ordered
prime-log graph.

This is a connection-valued reconstruction, not a termwise majorant: absolute values of the
cumulative-mass-weighted gradient terms need not be uniformly summable in vertical height.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Terminal boundary flux in the adjacent-prime Abel decomposition. -/
def xiMassPrimeTerminalFlux (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiMassPrimeFourierProfile a τ N * xiMassPrimeCriticalPartialMass (N + 1)

/-- Cumulative-mass-weighted covariant gradient on one ordered prime-log edge. -/
def xiMassPrimeConnectionGradientAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  xiMassPrimeCriticalPartialMass (n + 1) *
    (xiMassPrimeFourierProfile a τ n -
      xiMassPrimeFourierProfile a τ (n + 1))

/-- Ordered improper connection current on the full prime-log path.  Order is intrinsic: no
unconditional summability claim is made. -/
def xiMassPrimeConnectionGradientLayer (a : ℝ) (τ : ℂ) : ℂ :=
  limUnder atTop (fun N : ℕ =>
    ∑ n ∈ Finset.range N, xiMassPrimeConnectionGradientAtom a τ n)

def XiMassPrimeConnectionGradientLineBound (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassPrimeConnectionGradientLayer a ((σ : ℂ) + u * I)‖ ≤ C

theorem norm_xiMassNthPrimeCriticalCoefficient_eq_atomWeight (n : ℕ) :
    ‖xiMassNthPrimeCriticalCoefficient n‖ =
      criticalMellinAtomWeight (nthPrimeSubtype n : ℕ) := by
  have hpne : (nthPrimeSubtype n : ℕ) ≠ 0 :=
    (nthPrimeSubtype n).prop.ne_zero
  have hcast := congrArg norm
    (criticalMellinAtomWeight_cast_eq_lSeriesTerm_half hpne)
  have hnonneg : 0 ≤ criticalMellinAtomWeight (nthPrimeSubtype n : ℕ) := by
    unfold criticalMellinAtomWeight
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      ArithmeticFunction.vonMangoldt_nonneg
  simpa [xiMassNthPrimeCriticalCoefficient, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnonneg] using hcast.symm

/-- Cumulative critical mass over the first `N+1` primes is dominated by the full critical
von-Mangoldt mass through the last prime. -/
theorem norm_xiMassPrimeCriticalPartialMass_succ_le (N : ℕ) :
    ‖xiMassPrimeCriticalPartialMass (N + 1)‖ ≤
      criticalMellinPrimeMass (Real.log (nthPrimeSubtype N : ℝ)) := by
  let P : ℕ := nthPrimeSubtype N
  have hinj : Function.Injective (fun n : ℕ => (nthPrimeSubtype n : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  have hsumImage :
      (∑ n ∈ Finset.range (N + 1),
          criticalMellinAtomWeight (nthPrimeSubtype n : ℕ)) =
        ∑ k ∈ (Finset.range (N + 1)).image
            (fun n : ℕ => (nthPrimeSubtype n : ℕ)),
          criticalMellinAtomWeight k := by
    rw [Finset.sum_image]
    exact hinj.injOn
  have hsubset :
      (Finset.range (N + 1)).image
          (fun n : ℕ => (nthPrimeSubtype n : ℕ)) ⊆ Finset.Icc 0 P := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, nthPrimeSubtype_strictMono.monotone (by omega)⟩
  have hfloor :
      ⌊Real.exp (Real.log (P : ℝ))⌋₊ = P := by
    rw [Real.exp_log (by simpa [P] using nthPrimeSubtype_pos N),
      Nat.floor_natCast]
  unfold xiMassPrimeCriticalPartialMass
  calc
    ‖∑ n ∈ Finset.range (N + 1), xiMassNthPrimeCriticalCoefficient n‖ ≤
        ∑ n ∈ Finset.range (N + 1),
          ‖xiMassNthPrimeCriticalCoefficient n‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (N + 1),
          criticalMellinAtomWeight (nthPrimeSubtype n : ℕ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact norm_xiMassNthPrimeCriticalCoefficient_eq_atomWeight n
    _ = ∑ k ∈ (Finset.range (N + 1)).image
          (fun n : ℕ => (nthPrimeSubtype n : ℕ)),
        criticalMellinAtomWeight k := hsumImage
    _ ≤ ∑ k ∈ Finset.Icc 0 P, criticalMellinAtomWeight k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => by
        unfold criticalMellinAtomWeight
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          ArithmeticFunction.vonMangoldt_nonneg)
    _ = criticalMellinPrimeMass (Real.log (nthPrimeSubtype N : ℝ)) := by
      rw [criticalMellinPrimeMass]
      rw [show (nthPrimeSubtype N : ℝ) = (P : ℝ) by rfl, hfloor]
      rfl

/-- Sharp pointwise terminal estimate.  Exponent is negative exactly when the strip shift is
deeper than the critical half-density. -/
theorem norm_xiMassPrimeTerminalFlux_le
    {a σ d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (u : ℝ) (N : ℕ) :
    ‖xiMassPrimeTerminalFlux a ((σ : ℂ) + u * I) N‖ ≤
      (21 * (∫ x : ℝ, Real.exp (-(σ * |x|))) * Real.exp (|u| * d)) *
        Real.exp (-(d - 1 / 2) * Real.log (nthPrimeSubtype N : ℝ)) := by
  let H : ℝ := Real.log (nthPrimeSubtype N : ℝ)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(σ * |x|))
  have hH : 0 ≤ H := by
    dsimp [H]
    exact Real.log_nonneg (by exact_mod_cast (nthPrimeSubtype N).prop.one_le)
  have hmass := norm_xiMassPrimeCriticalPartialMass_succ_le N
  have hmassSharp := criticalMellinPrimeMass_le_sqrt hH
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := σ) (d := d) (by linarith) hda hσ u H
  rw [xiMassPrimeTerminalFlux, norm_mul]
  change ‖xiMassPrimeFourierProfile a ((σ : ℂ) + ↑u * I) N‖ *
      ‖xiMassPrimeCriticalPartialMass (N + 1)‖ ≤ _
  have hprofile :
      ‖xiMassPrimeFourierProfile a ((σ : ℂ) + ↑u * I) N‖ ≤
        Real.exp (|u| * d - H * d) * J := by
    simpa [xiMassPrimeFourierProfile, H, J] using hF
  calc
    ‖xiMassPrimeFourierProfile a ((σ : ℂ) + ↑u * I) N‖ *
        ‖xiMassPrimeCriticalPartialMass (N + 1)‖ ≤
      (Real.exp (|u| * d - H * d) * J) *
        (21 * Real.exp (H / 2)) := by
      exact mul_le_mul hprofile (hmass.trans hmassSharp)
        (norm_nonneg _) (by positivity)
    _ = (21 * J * Real.exp (|u| * d)) *
        Real.exp (-(d - 1 / 2) * H) := by
      rw [show Real.exp (|u| * d - H * d) * J *
          (21 * Real.exp (H / 2)) =
        21 * J * (Real.exp (|u| * d - H * d) * Real.exp (H / 2)) by ring]
      rw [← Real.exp_add, show |u| * d - H * d + H / 2 =
        |u| * d + (-(d - 1 / 2) * H) by ring, Real.exp_add]
      ring
    _ = _ := by simp only [H, J]

/-- Terminal flux at infinity vanishes unconditionally. -/
theorem tendsto_xiMassPrimeTerminalFlux_zero
    {a σ d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (u : ℝ) :
    Tendsto (fun N : ℕ => xiMassPrimeTerminalFlux a ((σ : ℂ) + u * I) N)
      atTop (𝓝 0) := by
  let K : ℝ := 21 * (∫ x : ℝ, Real.exp (-(σ * |x|))) * Real.exp (|u| * d)
  have hpNat : Tendsto (fun N : ℕ => (nthPrimeSubtype N : ℕ)) atTop atTop :=
    nthPrimeSubtype_strictMono.tendsto_atTop
  have hpReal : Tendsto (fun N : ℕ => (nthPrimeSubtype N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpNat
  have hlog : Tendsto (fun N : ℕ => Real.log (nthPrimeSubtype N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpReal
  have harg : Tendsto
      (fun N : ℕ => -(d - 1 / 2) * Real.log (nthPrimeSubtype N : ℝ))
      atTop atBot := hlog.const_mul_atTop_of_neg (by linarith)
  have hexp : Tendsto
      (fun N : ℕ => Real.exp (-(d - 1 / 2) *
        Real.log (nthPrimeSubtype N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (by simpa [K] using hexp.const_mul K)
  exact Eventually.of_forall fun N => by
    simpa [K] using norm_xiMassPrimeTerminalFlux_le hdhalf hda hσ u N

/-- Finite source equals terminal flux plus connection-current prefix. -/
theorem sum_range_xiMassPrimeAtom_eq_terminal_add_connection
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) =
      xiMassPrimeTerminalFlux a τ N +
        ∑ n ∈ Finset.range N, xiMassPrimeConnectionGradientAtom a τ n := by
  simpa [xiMassPrimeTerminalFlux, xiMassPrimeConnectionGradientAtom] using
    sum_range_xiMassPrimeAtom_eq_graphFlux a τ (N + 1)

theorem tendsto_sum_range_xiMassNthPrimeCenteredAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ))
      atTop (𝓝 (xiMassValuationOnePrimeLayer a τ)) := by
  have hprime := summable_xiMassValuationOnePrimeAtom hhalf hda hτ
  have hseq : Summable (fun n : ℕ =>
      xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ)) :=
    hprime.comp_injective nthPrimeSubtype_injective
  have hlim := (hseq.hasSum_iff_tendsto_nat.mp hseq.hasSum).comp
    (tendsto_add_atTop_nat 1)
  have htsum := nthPrimeEquiv.tsum_eq
    (fun p : Nat.Primes => xiMassCenteredPrimeAtom a τ (p : ℕ))
  change (∑' n : ℕ, xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ)) =
    ∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p : ℕ) at htsum
  have htsum' :
      (∑' n : ℕ, xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ)) =
        xiMassValuationOnePrimeLayer a τ := by
    rw [xiMassValuationOnePrimeLayer]
    exact htsum
  rw [← htsum']
  simpa [Function.comp_def, nthPrimeEquiv] using hlim

/-- Ordered full-graph prefixes converge to the complete valuation-one source. -/
theorem tendsto_sum_range_xiMassPrimeConnectionGradientAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiMassPrimeConnectionGradientAtom a τ n)
      atTop (𝓝 (xiMassValuationOnePrimeLayer a τ)) := by
  have hsource := tendsto_sum_range_xiMassNthPrimeCenteredAtom hhalf hda hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hterminal := tendsto_xiMassPrimeTerminalFlux_zero
    hhalf hda hτ τ.im
  rw [hτform] at hterminal
  have hdiff := hsource.sub hterminal
  simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall fun N => by
    rw [sum_range_xiMassPrimeAtom_eq_terminal_add_connection]
    ring)

theorem xiMassPrimeConnectionGradientLayer_eq_valuationOne
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassPrimeConnectionGradientLayer a τ =
      xiMassValuationOnePrimeLayer a τ := by
  exact (tendsto_sum_range_xiMassPrimeConnectionGradientAtom
    hhalf hda hτ).limUnder_eq

theorem xiMassPrimeConnectionGradientLineBound_iff_valuationOne
    {a σ : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ) :
    XiMassPrimeConnectionGradientLineBound a σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  let d : ℝ := (a + 1 / 2) / 2
  have hhalf : 1 / 2 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  have heq (u : ℝ) :
      xiMassPrimeConnectionGradientLayer a ((σ : ℂ) + u * I) =
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) :=
    xiMassPrimeConnectionGradientLayer_eq_valuationOne hhalf hda (by simpa using hσ)
  constructor <;> rintro ⟨C, hC⟩ <;> exact ⟨C, fun u => by simpa [heq u] using hC u⟩

/-- Route T recut: RH is equivalent to boundedness of the exact full connection-gradient
current, with no terminal flux at infinity. -/
theorem riemannHypothesis_iff_xiMassPrimeConnectionGradientLineBound
    {a σ : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassPrimeConnectionGradientLineBound a σ := by
  let d : ℝ := (a + 1 / 2) / 2
  have hhalf : 1 / 2 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  exact (riemannHypothesis_iff_xiMassValuationOnePrimeLineBound hhalf hda hσ).trans
    (xiMassPrimeConnectionGradientLineBound_iff_valuationOne ha hσ).symm

end

end RHTower
