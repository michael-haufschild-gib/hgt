import GaloisForLFunctions.RHTower.XiMassFullAdjacentPrimeConnection
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Critical half-density gauge of the adjacent-prime connection

The ungauged adjacent-prime connection carries cumulative mass of square-root size.  Moving the
critical half-density from the arithmetic coefficient into the mass profile preserves every prime
atom exactly, but changes the ordered connection coordinate to the prime harmonic weight
`log p / p`.  Mertens' first theorem then makes cumulative connection mass logarithmic.

This is an exact conditioning theorem, not an RH estimate.  The conjugated profile carries the
opposite half-density radiation, so taking absolute values of its gradients can still lose the
required cancellation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Logarithmic coordinate of the `n`th ordered prime. -/
def xiMassNthPrimeLogHeight (n : ℕ) : ℝ :=
  Real.log (nthPrimeSubtype n : ℝ)

/-- Prime harmonic coefficient obtained after moving the critical half-density into the profile. -/
def xiMassNthPrimeHarmonicCoefficient (n : ℕ) : ℂ :=
  (Real.log (nthPrimeSubtype n : ℝ) / (nthPrimeSubtype n : ℝ) : ℝ)

/-- Mass Fourier profile in the critical half-density gauge. -/
def xiMassPrimeHalfDensityProfile (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (xiMassNthPrimeLogHeight n / 2) : ℝ) *
    xiMassPrimeFourierProfile a τ n

/-- Harmonic cumulative mass on the first `N` ordered primes. -/
def xiMassPrimeHarmonicPartialMass (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, xiMassNthPrimeHarmonicCoefficient n

/-- Terminal flux in the half-density-gauged Abel decomposition. -/
def xiMassPrimeHalfDensityTerminalFlux (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  xiMassPrimeHalfDensityProfile a τ N * xiMassPrimeHarmonicPartialMass (N + 1)

/-- Harmonic-mass-weighted edge gradient of the half-density profile. -/
def xiMassPrimeHalfDensityConnectionAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  xiMassPrimeHarmonicPartialMass (n + 1) *
    (xiMassPrimeHalfDensityProfile a τ n -
      xiMassPrimeHalfDensityProfile a τ (n + 1))

/-- Ordered improper half-density connection current. -/
def xiMassPrimeHalfDensityConnectionLayer (a : ℝ) (τ : ℂ) : ℂ :=
  limUnder atTop (fun N : ℕ =>
    ∑ n ∈ Finset.range N, xiMassPrimeHalfDensityConnectionAtom a τ n)

def XiMassPrimeHalfDensityConnectionLineBound (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassPrimeHalfDensityConnectionLayer a ((σ : ℂ) + u * I)‖ ≤ C

private theorem exp_half_primeLog_mul_harmonicCoefficient
    (n : ℕ) :
    Real.exp (xiMassNthPrimeLogHeight n / 2) *
        (Real.log (nthPrimeSubtype n : ℝ) / (nthPrimeSubtype n : ℝ)) =
      criticalMellinAtomWeight (nthPrimeSubtype n : ℕ) := by
  let p : ℝ := nthPrimeSubtype n
  have hp : 0 < p := nthPrimeSubtype_pos n
  have hexp : Real.exp (Real.log p) = p := Real.exp_log hp
  rw [criticalMellinAtomWeight, ArithmeticFunction.vonMangoldt_apply_prime
    (nthPrimeSubtype n).prop]
  change Real.exp (Real.log p / 2) * (Real.log p / p) =
    p ^ (-1 / 2 : ℝ) * Real.log p
  rw [Real.rpow_def_of_pos hp]
  calc
    Real.exp (Real.log p / 2) * (Real.log p / p) =
        Real.log p * (Real.exp (Real.log p / 2) / p) := by ring
    _ = Real.log p * Real.exp (-(Real.log p / 2)) := by
      apply congrArg (Real.log p * ·)
      apply (div_eq_iff hp.ne').2
      calc
        Real.exp (Real.log p / 2) =
            Real.exp (-(Real.log p / 2)) * Real.exp (Real.log p) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ = Real.exp (-(Real.log p / 2)) * p := by rw [hexp]
    _ = Real.exp (Real.log p * (-1 / 2)) * Real.log p := by
      rw [show -(Real.log p / 2) = Real.log p * (-1 / 2) by ring]
      ring

/-- The half-density gauge preserves every literal prime atom before summation. -/
theorem xiMassHarmonicCoefficient_mul_halfDensityProfile_eq_centeredAtom
    (a : ℝ) (τ : ℂ) (n : ℕ) :
    xiMassNthPrimeHarmonicCoefficient n *
        xiMassPrimeHalfDensityProfile a τ n =
      xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) := by
  have hcritical :=
    criticalMellinAtomWeight_cast_eq_lSeriesTerm_half
      (nthPrimeSubtype n).prop.ne_zero
  rw [xiMassNthPrimeHarmonicCoefficient, xiMassPrimeHalfDensityProfile,
    xiMassCenteredPrimeAtom, xiMassPrimeFourierProfile]
  rw [← hcritical]
  have hscale :
      ((Real.log (nthPrimeSubtype n : ℝ) /
          (nthPrimeSubtype n : ℝ) : ℝ) : ℂ) *
          ((Real.exp (xiMassNthPrimeLogHeight n / 2) : ℝ) : ℂ) =
        (criticalMellinAtomWeight (nthPrimeSubtype n : ℕ) : ℂ) := by
    exact_mod_cast (by
      rw [mul_comm]
      exact exp_half_primeLog_mul_harmonicCoefficient n)
  calc
    ((Real.log (nthPrimeSubtype n : ℝ) /
          (nthPrimeSubtype n : ℝ) : ℝ) : ℂ) *
        (((Real.exp (xiMassNthPrimeLogHeight n / 2) : ℝ) : ℂ) *
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype n : ℕ) : ℂ)) =
      (((Real.log (nthPrimeSubtype n : ℝ) /
          (nthPrimeSubtype n : ℝ) : ℝ) : ℂ) *
        ((Real.exp (xiMassNthPrimeLogHeight n / 2) : ℝ) : ℂ)) *
          stripFourier (xiMassAnalyticTest a τ)
            (Real.log (nthPrimeSubtype n : ℕ) : ℂ) := by ring
    _ = _ := by rw [hscale]

@[simp]
theorem norm_xiMassNthPrimeHarmonicCoefficient (n : ℕ) :
    ‖xiMassNthPrimeHarmonicCoefficient n‖ =
      Real.log (nthPrimeSubtype n : ℝ) / (nthPrimeSubtype n : ℝ) := by
  rw [xiMassNthPrimeHarmonicCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast (nthPrimeSubtype n).prop.one_le))
    (by positivity)

/-- Mertens-scale cumulative connection mass: logarithmic rather than square-root growth. -/
theorem norm_xiMassPrimeHarmonicPartialMass_succ_le (N : ℕ) :
    ‖xiMassPrimeHarmonicPartialMass (N + 1)‖ ≤
      Real.log (nthPrimeSubtype N : ℝ) +
        ((Real.log 4 + 4) + (8 + Mertens.mertensTail)) := by
  let P : ℕ := nthPrimeSubtype N
  let K : ℝ := (Real.log 4 + 4) + (8 + Mertens.mertensTail)
  have hinj : Function.Injective (fun n : ℕ => (nthPrimeSubtype n : ℕ)) :=
    nthPrimeSubtype_strictMono.injective
  have hsumImage :
      (∑ n ∈ Finset.range (N + 1),
          Real.log (nthPrimeSubtype n : ℝ) / (nthPrimeSubtype n : ℝ)) =
        ∑ p ∈ (Finset.range (N + 1)).image
            (fun n : ℕ => (nthPrimeSubtype n : ℕ)),
          Real.log p / (p : ℝ) := by
    rw [Finset.sum_image]
    exact hinj.injOn
  have hsubset :
      (Finset.range (N + 1)).image
          (fun n : ℕ => (nthPrimeSubtype n : ℕ)) ⊆
        (Finset.Icc 1 P).filter Nat.Prime := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(nthPrimeSubtype n).prop.one_le,
      nthPrimeSubtype_strictMono.monotone (by omega)⟩,
      (nthPrimeSubtype n).prop⟩
  have hnonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log p / (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Nat.cast_nonneg p)
  have hMertens := Mertens.mertens_first_prime P (nthPrimeSubtype N).prop.one_le
  have hMertensUpper :
      (∑ p ∈ Finset.Icc 1 P with p.Prime, Real.log p / (p : ℝ)) ≤
        Real.log P + K := by
    dsimp only [K]
    linarith [(abs_le.mp hMertens).2]
  unfold xiMassPrimeHarmonicPartialMass xiMassNthPrimeHarmonicCoefficient
  rw [← Complex.ofReal_sum]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (Finset.sum_nonneg fun n _ => hnonneg (nthPrimeSubtype n).prop)]
  calc
    (∑ n ∈ Finset.range (N + 1),
        Real.log (nthPrimeSubtype n : ℝ) / (nthPrimeSubtype n : ℝ)) =
      ∑ p ∈ (Finset.range (N + 1)).image
          (fun n : ℕ => (nthPrimeSubtype n : ℕ)),
        Real.log p / (p : ℝ) := hsumImage
    _ ≤ ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
        Real.log p / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ =>
        hnonneg (Finset.mem_filter.mp hp).2)
    _ ≤ Real.log P + K := by
      simpa only [Finset.sum_filter] using hMertensUpper
    _ = _ := by rfl

/-- Half-density profile has the expected critical radiation exponent. -/
theorem norm_xiMassPrimeHalfDensityProfile_le
    {a σ d : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hσ : 0 < σ)
    (u : ℝ) (N : ℕ) :
    ‖xiMassPrimeHalfDensityProfile a ((σ : ℂ) + u * I) N‖ ≤
      Real.exp (|u| * d - (d - 1 / 2) * xiMassNthPrimeLogHeight N) *
        (∫ x : ℝ, Real.exp (-σ * |x|)) := by
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := σ) (d := d) hd0 hda hσ u (xiMassNthPrimeLogHeight N)
  have hF' : ‖xiMassPrimeFourierProfile a ((σ : ℂ) + u * I) N‖ ≤
      Real.exp (|u| * d - xiMassNthPrimeLogHeight N * d) *
        (∫ x : ℝ, Real.exp (-σ * |x|)) := by
    simpa only [xiMassPrimeFourierProfile, xiMassNthPrimeLogHeight, neg_mul] using hF
  rw [xiMassPrimeHalfDensityProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (xiMassNthPrimeLogHeight N / 2) *
        ‖xiMassPrimeFourierProfile a ((σ : ℂ) + ↑u * I) N‖ ≤
      Real.exp (xiMassNthPrimeLogHeight N / 2) *
        (Real.exp (|u| * d - xiMassNthPrimeLogHeight N * d) *
          ∫ x : ℝ, Real.exp (-σ * |x|)) :=
      mul_le_mul_of_nonneg_left hF'
        (Real.exp_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Finite source equals half-density terminal flux plus harmonic connection prefix. -/
theorem sum_range_xiMassPrimeAtom_eq_halfDensityTerminal_add_connection
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) =
      xiMassPrimeHalfDensityTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiMassPrimeHalfDensityConnectionAtom a τ n := by
  have hAbel := complex_sum_range_by_parts_flux
    (xiMassPrimeHalfDensityProfile a τ)
    xiMassNthPrimeHarmonicCoefficient (N + 1)
  rw [show N + 1 - 1 = N by omega] at hAbel
  calc
    (∑ n ∈ Finset.range (N + 1),
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ)) =
      ∑ n ∈ Finset.range (N + 1),
        xiMassNthPrimeHarmonicCoefficient n *
          xiMassPrimeHalfDensityProfile a τ n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (xiMassHarmonicCoefficient_mul_halfDensityProfile_eq_centeredAtom
        a τ n).symm
    _ = _ := by
      simpa [xiMassPrimeHalfDensityTerminalFlux,
        xiMassPrimeHalfDensityConnectionAtom,
        xiMassPrimeHarmonicPartialMass] using hAbel

/-- Half-density terminal flux vanishes: polynomial Mertens mass loses to every legal interior
strip gap `d-1/2`. -/
theorem tendsto_xiMassPrimeHalfDensityTerminalFlux_zero
    {a σ d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ)
    (u : ℝ) :
    Tendsto (fun N : ℕ =>
      xiMassPrimeHalfDensityTerminalFlux a ((σ : ℂ) + u * I) N)
      atTop (nhds 0) := by
  let H : ℕ → ℝ := fun N => xiMassNthPrimeLogHeight N
  let K : ℝ := (Real.log 4 + 4) + (8 + Mertens.mertensTail)
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  let δ : ℝ := d - 1 / 2
  have hH : Tendsto H atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop)
  have hdecay : Tendsto (fun h : ℝ => (h + K) * Real.exp (-δ * h))
      atTop (nhds 0) := by
    have hlin := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ (by dsimp [δ]; linarith)
    have hexp : Tendsto (fun h : ℝ => Real.exp (-δ * h)) atTop (nhds 0) := by
      have harg : Tendsto (fun h : ℝ => -δ * h) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by dsimp [δ]; linarith)
      exact Real.tendsto_exp_atBot.comp harg
    have hsum := hlin.add (hexp.const_mul K)
    convert (by simpa only [zero_add, mul_zero] using hsum) using 1
    funext h
    rw [Real.rpow_one]
    ring
  have hmajor : Tendsto
      (fun N : ℕ =>
        (Real.exp (|u| * d) * J) * ((H N + K) * Real.exp (-δ * H N)))
      atTop (nhds 0) := by
    simpa using (hdecay.comp hH).const_mul (Real.exp (|u| * d) * J)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  exact Eventually.of_forall fun N => by
    rw [xiMassPrimeHalfDensityTerminalFlux, norm_mul]
    have hprofile := norm_xiMassPrimeHalfDensityProfile_le
      (d := d) (by linarith) hda hσ u N
    have hmass := norm_xiMassPrimeHarmonicPartialMass_succ_le N
    have hmass' : ‖xiMassPrimeHarmonicPartialMass (N + 1)‖ ≤ H N + K := by
      dsimp only [H, K, xiMassNthPrimeLogHeight]
      exact hmass
    have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
    calc
      ‖xiMassPrimeHalfDensityProfile a ((σ : ℂ) + ↑u * I) N‖ *
          ‖xiMassPrimeHarmonicPartialMass (N + 1)‖ ≤
        (Real.exp (|u| * d - δ * H N) * J) * (H N + K) := by
          exact mul_le_mul hprofile hmass' (norm_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) hJ)
      _ = (Real.exp (|u| * d) * J) *
          ((H N + K) * Real.exp (-δ * H N)) := by
        rw [show |u| * d - δ * H N = |u| * d + (-δ * H N) by ring,
          Real.exp_add]
        ring

/-- Ordered half-density connection prefixes reconstruct the full valuation-one source. -/
theorem tendsto_sum_range_xiMassPrimeHalfDensityConnectionAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiMassPrimeHalfDensityConnectionAtom a τ n)
      atTop (nhds (xiMassValuationOnePrimeLayer a τ)) := by
  have hsource := tendsto_sum_range_xiMassNthPrimeCenteredAtom hhalf hda hτ
  have hτform : ((τ.re : ℂ) + τ.im * I) = τ := by
    apply Complex.ext <;> simp
  have hterminal := tendsto_xiMassPrimeHalfDensityTerminalFlux_zero
    hhalf hda hτ τ.im
  rw [hτform] at hterminal
  have hdiff := hsource.sub hterminal
  simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall fun N => by
    rw [sum_range_xiMassPrimeAtom_eq_halfDensityTerminal_add_connection]
    ring)

theorem xiMassPrimeHalfDensityConnectionLayer_eq_valuationOne
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassPrimeHalfDensityConnectionLayer a τ =
      xiMassValuationOnePrimeLayer a τ := by
  exact (tendsto_sum_range_xiMassPrimeHalfDensityConnectionAtom
    hhalf hda hτ).limUnder_eq

theorem riemannHypothesis_iff_xiMassPrimeHalfDensityConnectionLineBound
    {a σ : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassPrimeHalfDensityConnectionLineBound a σ := by
  let d : ℝ := (a + 1 / 2) / 2
  have hhalf : 1 / 2 < d := by dsimp [d]; linarith
  have hda : d < a := by dsimp [d]; linarith
  rw [riemannHypothesis_iff_xiMassValuationOnePrimeLineBound hhalf hda hσ]
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun u => ?_⟩
  · have heq := xiMassPrimeHalfDensityConnectionLayer_eq_valuationOne
      hhalf hda (τ := ((σ : ℂ) + u * I)) (by simpa using hσ)
    simpa only [heq] using hC u
  · have heq := xiMassPrimeHalfDensityConnectionLayer_eq_valuationOne
      hhalf hda (τ := ((σ : ℂ) + u * I)) (by simpa using hσ)
    simpa only [heq] using hC u

end

end RHTower
