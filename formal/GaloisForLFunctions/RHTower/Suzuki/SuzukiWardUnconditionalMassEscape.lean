import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardAtomicContinuousLightWeld
import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtMass
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeOutgoingDilationFlux

/-!
# Unconditional escape of the Suzuki Ward light mass

The literal finite Suzuki wall is a positive sum of reflected light Gram energies.  Its previous
cofinal escape theorem assumed RH by comparing the prime wall with the completed Green response.
That assumption is unnecessary: a fixed dyadic block inside the wall already has PNT-scale mass.

For `M = N / 9`, every source index `M < n ≤ 2M` lies in the scale window
`N / 9 < n ≤ N / 4`.  On this window the outgoing coefficient is at least one sixth of the
critical half-density coefficient `Λ(n) / √n`.  The corpus dyadic PNT lower bound therefore forces
the full outgoing charge to `+∞`.

Consequences:

* total reporter-weighted wall-light mass diverges at every fixed height;
* at spectral center, positive and negative light legs each diverge separately;
* no finite absolute-energy cofinal completion exists, independently of RH.

Thus RH can only govern the renormalized displacement between co-divergent atomic and continuous
sectors.  Absolute Hilbert-energy convergence is structurally impossible before zero selection.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open ArithmeticFunction
open scoped BigOperators

private theorem outgoingBracket_ge_halfDensity
    {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hlo : A / 3 ≤ B) (hhi : B ≤ A / 2) :
    1 / (6 * B) ≤ 1 / A - B / A ^ (2 : ℕ) := by
  have hBA : 0 ≤ A - B := by linarith
  have hprod : A ^ (2 : ℕ) ≤ 6 * B * (A - B) := by
    have h1 : A / 3 * (A / 2) ≤ B * (A - B) :=
      mul_le_mul hlo (by linarith) (by positivity) hB.le
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  field_simp [hA.ne', hB.ne'] at hprod ⊢
  nlinarith

/-- A PNT dyadic block inside the natural aperture supplies an explicit lower bound for the
finite Suzuki outgoing charge. -/
theorem dyadicSqrtVonMangoldtMass_nat_div_nine_div_six_le_outgoingCharge
    {N : ℕ} (hN : 18 ≤ N) :
    RHTower.dyadicSqrtVonMangoldtMass ((N / 9 : ℕ) : ℝ) / 6 ≤
      unitRieszCoherentPrimeOutgoingCharge N := by
  let M : ℕ := N / 9
  have hM : 2 ≤ M := by
    dsimp [M]
    omega
  have hMN : 2 * M ≤ N := by
    dsimp [M]
    omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 18) hN)
  rw [unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm]
  calc
    RHTower.dyadicSqrtVonMangoldtMass ((N / 9 : ℕ) : ℝ) / 6 =
        ∑ n ∈ Finset.Ioc M (2 * M),
          vonMangoldt n / (6 * Real.sqrt n) := by
      have hfloor : ⌊2 * ((N / 9 : ℕ) : ℝ)⌋₊ = 2 * (N / 9) := by
        rw [show 2 * ((N / 9 : ℕ) : ℝ) = ((2 * (N / 9) : ℕ) : ℝ) by norm_num,
          Nat.floor_natCast]
      rw [RHTower.dyadicSqrtVonMangoldtMass]
      simp only [Nat.floor_natCast, hfloor]
      dsimp only [M]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ Finset.Ioc M (2 * M),
        vonMangoldt n *
          (1 / Real.sqrt (N : ℝ) - Real.sqrt (n : ℝ) / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnmem := Finset.mem_Ioc.mp hn
      have hnposNat : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
      have hNle9n : (N : ℝ) ≤ 9 * n := by
        exact_mod_cast (show N ≤ 9 * n by
          dsimp [M] at hnmem
          omega)
      have h4nleN : (4 : ℝ) * n ≤ N := by
        exact_mod_cast (show 4 * n ≤ N by omega)
      have hsqrtN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
      have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      have hlo : Real.sqrt N / 3 ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) hnpos.le]
        rw [div_pow, Real.sq_sqrt hNpos.le]
        norm_num
        linarith
      have hhi : Real.sqrt n ≤ Real.sqrt N / 2 := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · rw [div_pow, Real.sq_sqrt hNpos.le]
          norm_num
          linarith
      have hbr := outgoingBracket_ge_halfDensity hsqrtN hsqrtn hlo hhi
      rw [Real.sq_sqrt hNpos.le] at hbr
      calc
        vonMangoldt n / (6 * Real.sqrt n) =
            vonMangoldt n * (1 / (6 * Real.sqrt n)) := by ring
        _ ≤ vonMangoldt n *
            (1 / Real.sqrt (N : ℝ) - Real.sqrt (n : ℝ) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hbr vonMangoldt_nonneg
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        vonMangoldt n *
          (1 / Real.sqrt (N : ℝ) - Real.sqrt (n : ℝ) / (N : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnmem := Finset.mem_Ioc.mp hn
        exact Finset.mem_Icc.mpr ⟨hM.trans hnmem.1.le, hnmem.2.trans hMN⟩
      · intro n hn _
        have hnmem := Finset.mem_Icc.mp hn
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast hnmem.2
        have hsqrtle : Real.sqrt n ≤ Real.sqrt N := Real.sqrt_le_sqrt hnN
        have hsqrtN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
        have hdiv : Real.sqrt n / (N : ℝ) ≤ 1 / Real.sqrt N := by
          calc
            Real.sqrt n / (N : ℝ) ≤ Real.sqrt N / (N : ℝ) :=
              div_le_div_of_nonneg_right hsqrtle hNpos.le
            _ = 1 / Real.sqrt N := by
              field_simp [hsqrtN.ne']
              rw [Real.sq_sqrt hNpos.le]
        exact mul_nonneg vonMangoldt_nonneg (sub_nonneg.mpr hdiv)

/-- **Unconditional atomic escape.**  PNT forces finite positive Suzuki wall mass to escape before
any RH input or prime--Gamma cancellation. -/
theorem tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop :
    Tendsto unitRieszCoherentPrimeOutgoingCharge atTop atTop := by
  have hdiv : Tendsto (fun N : ℕ => N / 9) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hcast : Tendsto (fun N : ℕ => ((N / 9 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt ((N / 9 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hscale : Tendsto
      (fun N : ℕ => Real.sqrt ((N / 9 : ℕ) : ℝ) / 18) atTop atTop := by
    rw [tendsto_atTop] at hsqrt ⊢
    intro b
    filter_upwards [hsqrt (18 * b)] with N hN
    linarith
  have hdyadic := hcast.eventually RHTower.eventually_dyadicSqrtVonMangoldtMass_ge
  apply tendsto_atTop_mono' atTop _ hscale
  filter_upwards [hdyadic, eventually_ge_atTop (18 : ℕ)] with N hmass hN
  calc
    Real.sqrt ((N / 9 : ℕ) : ℝ) / 18 ≤
        RHTower.dyadicSqrtVonMangoldtMass ((N / 9 : ℕ) : ℝ) / 6 := by
      linarith
    _ ≤ unitRieszCoherentPrimeOutgoingCharge N :=
      dyadicSqrtVonMangoldtMass_nat_div_nine_div_six_le_outgoingCharge hN

private theorem tendsto_nat_add_two_atTop :
    Tendsto (fun N : ℕ => N + 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

/-- At every fixed wall height, total literal wall-light energy escapes unconditionally. -/
theorem tendsto_suzukiUnitRieszReporterWeightedWallLightMass_atTop
    (t : ℝ) :
    Tendsto (fun N : ℕ =>
      suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t) atTop atTop := by
  have hcharge : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop atTop :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop.comp tendsto_nat_add_two_atTop
  apply hcharge.congr'
  filter_upwards with N
  exact (suzukiUnitRieszReporterWeightedWallLightMass_eq_primeOutgoingCharge
    (by omega : 2 ≤ N + 2) t).symm

private theorem tendsto_outgoingCharge_div_two_atTop :
    Tendsto (fun N : ℕ => unitRieszCoherentPrimeOutgoingCharge N / 2) atTop atTop := by
  have hcharge := tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop
  rw [tendsto_atTop] at hcharge ⊢
  intro b
  filter_upwards [hcharge (2 * b)] with N hN
  linarith

/-- At spectral center, each forced light leg separately has infinite cofinal mass. -/
theorem tendsto_suzukiUnitRieszReporterWeighted_centerLightMasses_atTop :
    Tendsto (fun N : ℕ =>
        suzukiUnitRieszReporterWeightedPositiveLightMass N 0) atTop atTop ∧
      Tendsto (fun N : ℕ =>
        suzukiUnitRieszReporterWeightedNegativeLightMass N 0) atTop atTop := by
  constructor
  · apply tendsto_outgoingCharge_div_two_atTop.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact (suzukiUnitRieszReporterWeightedPositiveLightMass_zero_eq_prime_half hN).symm
  · apply tendsto_outgoingCharge_div_two_atTop.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact (suzukiUnitRieszReporterWeightedNegativeLightMass_zero_eq_prime_half hN).symm

private theorem no_finite_limit_of_tendsto_atTop
    {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) (L : ℝ) :
    ¬ Tendsto f atTop (𝓝 L) := by
  intro hL
  have hlarge : ∀ᶠ N in atTop, L + 1 ≤ f N :=
    (tendsto_atTop.1 hf) (L + 1)
  have hsmall : ∀ᶠ N in atTop, f N < L + 1 / 2 :=
    hL (Iio_mem_nhds (by norm_num : L < L + 1 / 2))
  rcases (hlarge.and hsmall).exists with ⟨N, hlargeN, hsmallN⟩
  linarith

/-- **Absolute-completion no-go.**  No finite-energy cofinal limit of the literal wall-light mass
exists, without assuming RH. -/
theorem no_finite_absolute_suzukiWallLightMassLimit
    (t wallLimit : ℝ) :
    ¬ Tendsto (fun N : ℕ =>
      suzukiUnitRieszReporterWeightedWallLightMass (N + 2) t)
      atTop (𝓝 wallLimit) :=
  no_finite_limit_of_tendsto_atTop
    (tendsto_suzukiUnitRieszReporterWeightedWallLightMass_atTop t) wallLimit

end GaloisForLFunctions.RHTower
