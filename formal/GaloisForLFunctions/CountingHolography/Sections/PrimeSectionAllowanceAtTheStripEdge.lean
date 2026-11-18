import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.FloorFreeArithmetic.TheTopTraceDeterminesTheTopLayer
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# An unconditional allowance for the two-graph sections

For the effective pair of degrees one and p, the discrepancy between the
logarithmic modulus and radius is smaller than ε√p times the squared
multiplicity at every sufficiently large degree and then every sufficiently
large multiplicity. The open strip has no zeros on its right edge, so the
spline trace normalized at that edge tends to zero.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Zeta23 SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticScatteringHolography RenormalizedIntersectionTheory

/-- Reverse the sign of the graph of degree one in the effective pair. -/
def primeDifference (p : ℕ) : Fin (p+1) → ℤ :=
  Pi.single (⟨p-1, by omega⟩ : Fin (p+1)) 1 - Pi.single 0 1

theorem primePair_add_difference (p : ℕ) :
    integerProbe (p+1) (primePair p) + integerProbe (p+1) (primeDifference p) =
      4 * (splineSeries 0).re := by
  rw [primePair, primeDifference, integerProbe_parallelogram]
  simp only [integerProbe_single, atomGram_eq_splineSeries, sub_self]
  ring

/-- Some signed pair of graphs of degrees one and a prime has strictly
positive quadratic section growth, unconditionally. -/
theorem exists_positive_prime_pair_or_difference :
    ∃ p : ℕ, p.Prime ∧ (0 < integerProbe (p+1) (primePair p) ∨
      0 < integerProbe (p+1) (primeDifference p)) := by
  by_contra! h
  have hRH : RiemannHypothesis := by
    apply riemannHypothesis_iff_bddBelow_primeDegrees'.mpr
    refine ⟨-(splineSeries 0).re, fun p hp => ?_⟩
    have he := primePair_add_difference p
    rw [integerProbe_primePair hp.pos] at he
    rw [orbitCorr_splineCycle_eq]
    linarith only [he, (h p hp).2]
  have hpos := riemannHypothesis_iff_integerProbes.mp hRH
  have hz : (splineSeries 0).re = 0 := by
    obtain ⟨h₁,h₂⟩ := h 2 Nat.prime_two
    linarith only [h₁,h₂,primePair_add_difference 2,hpos _ (primePair 2),hpos _ (primeDifference 2)]
  have hd {N : ℕ} (i : Fin N) : (atomGram N i i).re = 0 := by
    rw [atomGram_eq_splineSeries, sub_self, hz]
  have he {N : ℕ} (i j : Fin N) : (atomGram N i j).re = 0 := by
    let x : Fin N → ℤ := Pi.single i 1
    let y : Fin N → ℤ := Pi.single j 1
    have hp := integerProbe_parallelogram N x y
    have hx : integerProbe N x = 0 := (integerProbe_single _ _).trans (hd i)
    have hy : integerProbe N y = 0 := (integerProbe_single _ _).trans (hd j)
    have hxy : integerProbe N (x+y) = 0 := by
      linarith only [hp,hx,hy,hpos N (x+y),hpos N (x-y)]
    change integerProbe N (Pi.single i 1 + Pi.single j 1) = 0 at hxy
    rw [integerProbe_pair, hd, hd] at hxy
    linarith only [hxy]
  apply not_integerProbe_integerValued
  intro N a
  exact ⟨0, by simp [integerProbe_eq_sum, he]⟩

/-- The ordinary small-section height grows quadratically on at least
one of these two-atom rays, with no enlargement of its radius. -/
theorem exists_prime_pair_with_quadratic_sections :
    ∃ (p : ℕ) (a : Fin (p+1) → ℤ), p.Prime ∧ (a = primePair p ∨ a = primeDifference p) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, δ * (m : ℝ)^2 < splineCount (m • a) := by
  obtain ⟨p,hp,ha⟩ := exists_positive_prime_pair_or_difference
  obtain ⟨a,he,hq⟩ : ∃ a : Fin (p+1) → ℤ, (a = primePair p ∨ a = primeDifference p) ∧
      0 < integerProbe (p+1) a := by
    rcases ha with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  refine ⟨p,a,hp,he,integerProbe (p+1) a / 2,half_pos hq,?_⟩
  have ht := splineCount_tateLimit a
  rw [max_eq_left hq.le] at ht
  filter_upwards [ht.eventually_const_lt (half_lt_self hq), eventually_ge_atTop 1] with m hm hm1
  exact (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm

/-- The signed degree per squared multiplicity is little-o of the square
root of the second conductor. This applies to every positive degree. -/
theorem tendsto_primePair_degree_div_sqrt :
    Tendsto (fun p : ℕ => integerProbe (p+1) (primePair p) / Real.sqrt p) atTop (𝓝 0) := by
  have hstrip (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.re < 1/2 + 1/2 := by
    have hr : ρ.re < 1 := hρ.2.2
    linarith only [hr]
  have htop : TopDepth zetaZeroConfig (1/2) := fun z hz =>
    (le_abs_self _).trans (abs_re_le_of_traceCoeff_ne_zero_of_re_le
      (fun ρ hρ => (hstrip ρ hρ).le) (r := 3) hz)
  have ht := (FloorFreeArithmetic.tendsto_normTrace_zeta_zero_iff (by norm_num) htop).mpr
    (fun ρ hρ => (hstrip ρ hρ).ne)
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun p : ℕ => 2*(splineSeries 0).re / Real.sqrt p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hh := hc.add (ht.comp hl)
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hex : Real.exp ((1/2 : ℝ)*Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp', mul_comm]
  change _ + normTrace zetaZeroConfig (1/2) (Real.log p) = _
  rw [integerProbe_primePair hp, add_div, normTrace, ← orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_splineCycle_eq, Real.exp_neg, hex]
  ring

/-- On each sufficiently large pair, every sufficiently high multiple has
absolute degree below any prescribed positive multiple of √p times m². -/
theorem eventually_primePair_degree_allowance (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      |radius (m • primePair p) - Real.log (generator (m • primePair p) : ℝ)| <
        ε * Real.sqrt p * (m : ℝ)^2 := by
  have ht := tendsto_primePair_degree_div_sqrt.abs
  rw [abs_zero] at ht
  filter_upwards [ht.eventually_lt_const hε, eventually_ge_atTop 1] with p hp hp1
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp1)
  rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp] at hp
  have hm := (tendsto_splineDegree (primePair p)).abs.eventually_lt_const hp
  filter_upwards [hm, eventually_ge_atTop 1] with m hm hm1
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  rwa [abs_div, abs_of_pos hm2, div_lt_iff₀ hm2] at hm

#print axioms eventually_primePair_degree_allowance
#print axioms exists_prime_pair_with_quadratic_sections

/-- The sub-seven-eighths zero-free half-plane gives one power allowance
for the actual finite lattice at every positive second conductor. -/
theorem exists_sub_three_eighths_section_allowance :
    ∃ C : ℝ, ∀ p : ℕ, 0 < p → ∀ᶠ m : ℕ in atTop,
      |radius (m • primePair p) - Real.log (generator (m • primePair p) : ℝ)| <
        C * (p : ℝ)^(8999/24000 : ℝ) * (m : ℝ)^2 := by
  let σ : ℝ := 8999/24000
  have hσ : 0 ≤ σ := by norm_num [σ]
  obtain ⟨K,hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mpr
    ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths
  let D := |2*(splineSeries 0).re|
  refine ⟨D + 2*K + 1, fun p hp => ?_⟩
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hx : 1 ≤ (p : ℝ)^σ := Real.one_le_rpow (by exact_mod_cast hp) hσ
  have ht := hK (Real.log p) (Real.log_natCast_nonneg p)
  rw [orbitCorr_splineCycle_eq, mul_comm σ, ← Real.rpow_def_of_pos hp'] at ht
  have hq : |integerProbe (p+1) (primePair p)| < (D+2*K+1)*(p : ℝ)^σ := by
    rw [integerProbe_primePair hp]
    have h := abs_add_le (2*(splineSeries 0).re) (2*(splineSeries (Real.log p)).re)
    rw [abs_mul 2 (splineSeries (Real.log p)).re, abs_two] at h
    have hD : 0 ≤ D := abs_nonneg _
    change _ ≤ D + _ at h
    linarith only [h,ht,mul_le_mul_of_nonneg_left hx hD, hx]
  have hl := (tendsto_splineDegree (primePair p)).abs.eventually_lt_const hq
  filter_upwards [hl, eventually_ge_atTop 1] with m hm hm1
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  rwa [abs_div, abs_of_pos hm2, div_lt_iff₀ hm2] at hm

#print axioms exists_sub_three_eighths_section_allowance

end GaloisForLFunctions.CountingHolography.Sections
