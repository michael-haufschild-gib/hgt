import GaloisForLFunctions.BiScaleUncertainty.FoldedHyperbolicCellDefect
import GaloisForLFunctions.HTGeometry.CompactKernelRankOneDensity

/-!
# Actual odd sources attaining the coherent moment constant

Two symmetric tents avoid the zero of sinh and fold to a constant. Their
inverse hyperbolic images are actual compact continuous odd sources with
prescribed signed moment. They attain the exact coherent price and establish
log 2 as the best universal coefficient on the odd hyperbolic source class.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty.CoherentMomentAttainment
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual FoldedHyperbolicCellDefect
noncomputable section

private abbrev tent := GaloisForLFunctions.HTGeometry.tentReal 1
private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)

private theorem tent_formula (x : ℝ) : tent x = max 0 (1 - |x|) := by
  unfold tent GaloisForLFunctions.HTGeometry.tentReal
  rw [min_eq_right (by linarith [abs_nonneg x])]

private theorem tent_even (x : ℝ) : tent (-x) = tent x := by
  simp only [tent_formula, abs_neg]

private theorem tent_zero (x : ℝ) (hx : 1 ≤ |x|) : tent x = 0 :=
  GaloisForLFunctions.HTGeometry.tentReal_eq_zero hx

private theorem tent_right (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : tent x = 1 - x := by
  rw [tent_formula, abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]

private theorem tent_left (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : tent (x - 1) = x := by
  rw [tent_formula, abs_of_nonpos (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
  ring

/-- Symmetric tent profile, separated from the zero of the sinh multiplier. -/
def attainmentProfile (u : ℝ) : ℝ := (tent (u / d - 2) + tent (u / d + 2)) / 2

private theorem profile_continuous : Continuous attainmentProfile := by
  exact (((GaloisForLFunctions.HTGeometry.continuous_tentReal 1).comp
    ((continuous_id.div_const d).sub continuous_const)).add
    ((GaloisForLFunctions.HTGeometry.continuous_tentReal 1).comp
      ((continuous_id.div_const d).add continuous_const))).div_const 2

private theorem profile_even (u : ℝ) : attainmentProfile (-u) = attainmentProfile u := by
  unfold attainmentProfile
  rw [show -u / d - 2 = -(u / d + 2) by ring,
    show -u / d + 2 = -(u / d - 2) by ring, tent_even, tent_even, add_comm]

private theorem profile_zero_near (u : ℝ) (hu : |u| ≤ d) : attainmentProfile u = 0 := by
  have hb := abs_le.mp hu
  have hlo : -1 ≤ u / d := (le_div_iff₀ d_pos).mpr (by linarith)
  have hhi : u / d ≤ 1 := (div_le_iff₀ d_pos).mpr (by linarith)
  have hl : tent (u / d - 2) = 0 := tent_zero _ (by linarith [neg_le_abs (u / d - 2)])
  have hr : tent (u / d + 2) = 0 := tent_zero _ (by linarith [le_abs_self (u / d + 2)])
  simp [attainmentProfile, hl, hr]

private theorem profile_zero_far (u : ℝ) (hu : u ∉ Icc (-3 * d) (3 * d)) :
    attainmentProfile u = 0 := by
  have hh : u < -3 * d ∨ 3 * d < u := by simpa only [mem_Icc, not_and_or, not_le] using hu
  rcases hh with h | h
  · have hb : u / d < -3 := (div_lt_iff₀ d_pos).mpr (by linarith)
    have hl : tent (u / d - 2) = 0 := tent_zero _ (by linarith [neg_le_abs (u / d - 2)])
    have hr : tent (u / d + 2) = 0 := tent_zero _ (by linarith [neg_le_abs (u / d + 2)])
    simp [attainmentProfile, hl, hr]
  · have hb : 3 < u / d := (lt_div_iff₀ d_pos).mpr h
    have hl : tent (u / d - 2) = 0 := tent_zero _ (by linarith [le_abs_self (u / d - 2)])
    have hr : tent (u / d + 2) = 0 := tent_zero _ (by linarith [le_abs_self (u / d + 2)])
    simp [attainmentProfile, hl, hr]

private theorem source_continuous (a : ℝ) :
    Continuous (fun u => a * attainmentProfile u / Real.sinh (u / 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u = 0
  · subst u
    have hz : (fun u => a * attainmentProfile u / Real.sinh (u / 2)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by linarith [d_pos] : -d < (0 : ℝ)) d_pos] with v hv
      rw [profile_zero_near v (abs_le.mpr ⟨hv.1.le, hv.2.le⟩), mul_zero, zero_div]
    exact hz.continuousAt
  · exact (continuous_const.mul profile_continuous).continuousAt.div
      (Real.continuous_sinh.comp (continuous_id.div_const 2)).continuousAt
      (Real.sinh_ne_zero.mpr (div_ne_zero hu (by norm_num)))

/-- Explicit compact odd source with a prescribed constant folded sinh amplitude. -/
def attainingSource (a : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => a * attainmentProfile u / Real.sinh (u / 2), source_continuous a⟩, by
    apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-3 * d) (3 * d)) isCompact_Icc
    intro u hu
    by_contra hn
    exact hu (by simp [profile_zero_far u hn])⟩

theorem attainingSource_apply (a u : ℝ) :
    attainingSource a u = a * attainmentProfile u / Real.sinh (u / 2) := rfl

theorem attainingSource_odd (a u : ℝ) : attainingSource a (-u) = -attainingSource a u := by
  simp only [attainingSource_apply, profile_even, neg_div, Real.sinh_neg, div_neg]

theorem oddCompactSource_attainingSource (a : ℝ) : oddCompactSource (attainingSource a) = attainingSource a := by
  ext u
  change (attainingSource a u - attainingSource a (-u)) / 2 = attainingSource a u
  rw [attainingSource_odd]
  ring

/-- Inversion through the hyperbolic zero is exact because the constructed profile vanishes there. -/
theorem sinhCompact_attainingSource (a u : ℝ) :
    sinhCompact (1 / 2) (attainingSource a) u = a * attainmentProfile u := by
  change Real.sinh ((1 / 2 : ℝ) * u) * (a * attainmentProfile u / Real.sinh (u / 2)) = _
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  by_cases hu : u = 0
  · subst u
    simp [profile_zero_near 0 (by simpa using d_pos.le)]
  · field_simp [Real.sinh_ne_zero.mpr (div_ne_zero hu (by norm_num : (2 : ℝ) ≠ 0))]

private theorem profile_lattice_zero (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (k : ℤ)
    (hk : k ∉ ({-3, -2, 1, 2} : Finset ℤ)) : attainmentProfile (d * (x + k)) = 0 := by
  have ha : k ≤ 0 ∨ 3 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
  have hb : k ≤ -4 ∨ -1 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
  have hl : tent (x + k - 2) = 0 := by
    apply tent_zero
    rcases ha with h | h
    · have h' : (k : ℝ) ≤ 0 := by exact_mod_cast h
      linarith [neg_le_abs (x + k - 2), hx.2]
    · have h' : (3 : ℝ) ≤ k := by exact_mod_cast h
      linarith [le_abs_self (x + k - 2), hx.1]
  have hr : tent (x + k + 2) = 0 := by
    apply tent_zero
    rcases hb with h | h
    · have h' : (k : ℝ) ≤ -4 := by exact_mod_cast h
      linarith [neg_le_abs (x + k + 2), hx.2]
    · have h' : (-1 : ℝ) ≤ k := by exact_mod_cast h
      linarith [le_abs_self (x + k + 2), hx.1]
  rw [attainmentProfile, mul_div_cancel_left₀ _ d_pos.ne', hl, hr]
  norm_num

private theorem profile_lattice_sum (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∑ k ∈ ({-3, -2, 1, 2} : Finset ℤ), attainmentProfile (d * (x + k))) = 1 := by
  have hl5 : tent (x - 5) = 0 := tent_zero _ (by linarith [neg_le_abs (x - 5), hx.2])
  have hl4 : tent (x - 4) = 0 := tent_zero _ (by linarith [neg_le_abs (x - 4), hx.2])
  have hr3 : tent (x + 3) = 0 := tent_zero _ (by linarith [le_abs_self (x + 3), hx.1])
  have hr4 : tent (x + 4) = 0 := tent_zero _ (by linarith [le_abs_self (x + 4), hx.1])
  rw [Finset.sum_insert (by norm_num : (-3 : ℤ) ∉ ({-2, 1, 2} : Finset ℤ)),
    Finset.sum_insert (by norm_num : (-2 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    Finset.sum_insert (by norm_num : (1 : ℤ) ∉ ({2} : Finset ℤ)), Finset.sum_singleton]
  norm_num only [attainmentProfile, Int.cast_neg, Int.cast_ofNat, mul_div_cancel_left₀ _ d_pos.ne']
  rw [show x + -(3 : ℝ) - 2 = x - 5 by ring,
    show x + -(3 : ℝ) + 2 = x - 1 by ring,
    show x + -(2 : ℝ) - 2 = x - 4 by ring,
    show x + -(2 : ℝ) + 2 = x by ring,
    show x + (1 : ℝ) - 2 = x - 1 by ring,
    show x + (2 : ℝ) - 2 = x by ring,
    show x + (1 : ℝ) + 2 = x + 3 by ring,
    show x + (2 : ℝ) + 2 = x + 4 by ring,
    hl5, hl4, hr3, hr4, tent_left x hx, tent_right x hx]
  ring

/-- Exact constant fold: four actual tent cells, with zero contribution from every other index. -/
theorem cellFold_attainingSource (a : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) 1, cellFold (attainingSource a) x = a := by
  intro x hx
  rw [cellFold_apply]
  simp_rw [sinhCompact_attainingSource]
  rw [tsum_eq_sum (s := ({-3, -2, 1, 2} : Finset ℤ)) (by
    intro k hk
    rw [profile_lattice_zero x hx k hk, mul_zero])]
  rw [← Finset.mul_sum, profile_lattice_sum x hx, mul_one]

theorem cellMean_attainingSource (a : ℝ) : cellMean (attainingSource a) = a := by
  rw [← integral_cellFold]
  have he : (∫ x in (0 : ℝ)..1, cellFold (attainingSource a) x) = ∫ _x in (0 : ℝ)..1, a := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact cellFold_attainingSource a x hx
  rw [he, intervalIntegral.integral_const]
  simp

theorem moment_attainingSource (a : ℝ) :
    (∫ u, attainingSource a u * Real.sinh (u / 2)) = Real.log 2 * a := by
  have hm := cellMean_attainingSource a
  unfold cellMean at hm
  exact (div_eq_iff d_pos.ne').mp hm |>.trans (mul_comm a d)

theorem cellResidualEnergy_attainingSource (a : ℝ) : cellResidualEnergy (attainingSource a) = 0 := by
  apply (cellResidualEnergy_eq_zero_iff _).mpr
  rw [cellMean_attainingSource]
  exact cellFold_attainingSource a

/-- Exact coherent price, including every signed source correlation and filter pairing. -/
theorem exactBudget_attainingSource (a : ℝ) :
    localBudget (attainingSource a) - schurResidualGain (attainingSource a) = Real.log 2 * a ^ 2 := by
  have he := cellResidualEnergy_identity (attainingSource a)
  rw [oddCompactSource_attainingSource, cellResidualEnergy_attainingSource,
    moment_attainingSource, mul_zero] at he
  have hd := d_pos
  have hh : d * (localBudget (attainingSource a) - schurResidualGain (attainingSource a)) =
      d * (d * a ^ 2) := by nlinarith only [he]
  exact (mul_left_cancel₀ hd.ne') hh

theorem attainingSource_eq_zero_iff (a : ℝ) : attainingSource a = 0 ↔ a = 0 := by
  constructor
  · intro hf
    have hm := moment_attainingSource a
    simp only [hf, CompactlySupportedContinuousMap.zero_apply, zero_mul, integral_zero] at hm
    exact (mul_eq_zero.mp hm.symm).resolve_left d_pos.ne'
  · rintro rfl
    ext u
    simp [attainingSource_apply]

/-- The best universal coherent moment coefficient is exactly log 2, already attained by an actual odd source. -/
theorem coherent_moment_constant_iff (c : ℝ) :
    (∀ f : C_c(ℝ, ℝ), (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      c * (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f))) ↔ Real.log 2 ≤ c := by
  constructor
  · intro h
    have ht := h (attainingSource 1)
    rw [oddCompactSource_attainingSource, moment_attainingSource, exactBudget_attainingSource] at ht
    norm_num only [mul_one, one_pow] at ht
    have hd := d_pos
    nlinarith only [ht, hd]
  · intro hc f
    have he := cellResidualEnergy_identity f
    have hn := mul_nonneg (sq_nonneg d) (cellResidualEnergy_nonneg (oddCompactSource f))
    have hm : (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
        d * (localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)) := by
      linarith only [he, hn]
    have hC : 0 ≤ localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) :=
      nonneg_of_mul_nonneg_right ((sq_nonneg _).trans hm) d_pos
    exact hm.trans (mul_le_mul_of_nonneg_right hc hC)

/-- Full plastic transfer with the attained, explicitly evaluated moment penalty. -/
theorem plastic_attainingSource_bound (a : ℝ) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (attainingSource a) N (-y)) +
      plasticRemainderEnergy (attainingSource a) - 2 * (Real.log 2) ^ 2 * a ^ 2 ≤
        plasticCrossover (attainingSource a) := by
  have hp := odd_plasticCrossover_ge_optimized (attainingSource a) N
  rw [oddCompactSource_attainingSource, moment_attainingSource] at hp
  nlinarith only [hp]

end
end GaloisForLFunctions.BiScaleUncertainty.CoherentMomentAttainment
