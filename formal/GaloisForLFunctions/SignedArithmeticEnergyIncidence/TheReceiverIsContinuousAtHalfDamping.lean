import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheSourceOnTheCriticalLineIsZetaOverZeta
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheSourceIsTheDampedMoebiusResidueSeries
import GaloisForLFunctions.RHTower.BoseCumulantJets

/-!
# The receiver is continuous at half damping

The receiver orbit `u_η = C_η r`, `u_η(n) = P_η(n+1)/(n+1)` (`centeredOperator_reciprocal_eq_orbitCoord`),
converges in `ℓ²` to `u_{½}` as `η ↓ ½` (`orbit_l2_tendsto_half`): damping-summation of the residue
expansion `Σ_d μ(d) d^{−η} v_d` converges in the receiver norm at the half-damping threshold.  Its
positive twin `Σ_d d^{−ε} v_d` does the opposite: its horizon energies exceed every bound as
`ε ↓ ½` (`positiveTwin_energy_unbounded`).  Half damping is where the size-only reading of the
residue series breaks down, and the signed reading stays continuous there.

**Proof.**  For `½ < η, η' < 1` the orbit difference is the source difference at the integers, and
on `[N, N+1)` the floors do not move, so `‖u_η − u_{η'}‖² ≤ 8 ∫ (P_η − P_{η'})² x^{−2} + 4(ρ_η − ρ_{η'})²`
(`sum_sq_orbitCoord_sub_le`).  By Plancherel on `Re s = −½` the integral is the mean square of
`F_η − F_{η'}`, `F_η(t) = −ζ(½ + η − it)^{−1} ζ(½ − it)/(−½ + it)` (`integral_sq_sourceProfile_sub`).
As `η ↓ ½`, `F_η(t) → F_{½}(t)` for `t ≠ 0` because `ζ(1 − it) ≠ 0`, under the uniform domination
`|F_η(t)|² ≪ (1 + t²)^{−9/16}` of `exists_norm_mellin_sourceProfile_sq_le`; dominated convergence
gives `∫ |F_η − F_{½}|² → 0` (`tendsto_integral_sq_criticalSymbol_sub`).  The coordinates are
continuous in `η` (`continuousAt_orbitCoord`), so the bound passes to `η' ↓ ½`.

The signs of `μ` enter only through the non-vanishing of `ζ` on the `1`-line.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Coordinates and their continuity in the damping -/

/-- The orbit coordinate `u_η(n) = P_η(n+1)/(n+1)`. -/
def orbitCoord (η : ℝ) (n : ℕ) : ℝ := sourceProfile η ((n : ℝ) + 1) / ((n : ℝ) + 1)

theorem centeredOperator_reciprocal_eq_orbitCoord {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη reciprocalObservable n = orbitCoord η n := by
  rw [centeredOperator_reciprocal_apply, RHTower.pmPowerDampedCenteredDivisorPrefix_eq,
    orbitCoord, sourceProfile, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Nat.floor_natCast]
  rfl

/-- The density `ρ_η = 1/ζ(1+η)` is continuous in `η > 0`. -/
theorem continuousAt_density_re {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ContinuousAt (fun η => (RHTower.pmPowerDampedDivisorDensity η).re) η₀ := by
  have hz : ContinuousAt (fun η : ℝ => RHTower.realZetaSeries (1 + η)) η₀ :=
    ((RHTower.contDiffAt_realZetaSeries (by linarith) 0).continuousAt).comp
      (f := fun η : ℝ => 1 + η) (by fun_prop)
  have hz0 : RHTower.realZetaSeries (1 + η₀) ≠ 0 := (RHTower.realZetaSeries_pos (by linarith)).ne'
  refine (((continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) η₀).div hz hz0)).congr ?_
  filter_upwards [Ioi_mem_nhds hη₀] with η hη
  exact (pmPowerDampedDivisorDensity_re_eq hη).symm

/-- The prefix `A_η(m)` is continuous in `η`. -/
theorem continuous_arithmeticDampingPrefix (m : ℕ) :
    Continuous fun η : ℝ => arithmeticDampingPrefix η m := by
  unfold arithmeticDampingPrefix
  refine continuous_finsetSum _ fun j _ => ?_
  unfold RHTower.pmPowerDampedDivisorCoeff
  refine continuous_finsetSum _ fun d hd => continuous_const.mul ?_
  exact continuous_const.rpow continuous_neg fun _ =>
    Or.inl (Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)).ne'

theorem continuousAt_orbitCoord (n : ℕ) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ContinuousAt (fun η => orbitCoord η n) η₀ := by
  unfold orbitCoord sourceProfile
  exact ((((continuous_arithmeticDampingPrefix _).continuousAt).sub
    ((continuousAt_density_re hη₀).mul continuousAt_const)).div continuousAt_const
    (by positivity))

/-! ### From the integers to the half-line -/

/-- **The orbit difference against the source difference**:
`Σ_{n<T} (u_η − u_{η'})(n)² ≤ 8 ∫_0^∞ (P_η − P_{η'})² x^{−2} + 4 (ρ_η − ρ_{η'})²`. -/
theorem sum_sq_orbitCoord_sub_le (η η' : ℝ) (T : ℕ)
    (hint : IntegrableOn (fun x => (sourceProfile η x - sourceProfile η' x) ^ 2 / x ^ 2) (Ioi 0)) :
    ∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord η' n) ^ 2 ≤
      8 * (∫ x in Ioi (0 : ℝ), (sourceProfile η x - sourceProfile η' x) ^ 2 / x ^ 2) +
        4 * ((RHTower.pmPowerDampedDivisorDensity η).re -
          (RHTower.pmPowerDampedDivisorDensity η').re) ^ 2 := by
  set Δ := (RHTower.pmPowerDampedDivisorDensity η).re -
    (RHTower.pmPowerDampedDivisorDensity η').re with hΔ
  set f : ℝ → ℝ := fun x => (sourceProfile η x - sourceProfile η' x) ^ 2 / x ^ 2 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  set a : ℕ → ℝ := fun i => (i : ℝ) + 1 with ha
  have hii : ∀ i : ℕ, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i
    have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hint.mono_set fun x hx => lt_of_lt_of_le (by simp only [ha]; positivity) hx.1
  -- on `[N, N+1)` the difference moves linearly with slope `−Δ`
  have hpt : ∀ n : ℕ, ∀ x : ℝ, (n : ℝ) + 1 ≤ x → x < (n : ℝ) + 2 →
      (orbitCoord η n - orbitCoord η' n) ^ 2 ≤ 8 * f x + 2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    intro n x hx hx'
    have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hx0 : 0 < x := by linarith
    have hfl : ⌊x⌋₊ = ⌊(n : ℝ) + 1⌋₊ := by
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast,
        Nat.floor_eq_iff hx0.le]
      push_cast
      exact ⟨hx, by linarith⟩
    have e1 := sourceProfile_eq_of_floor_eq η hfl
    have e2 := sourceProfile_eq_of_floor_eq η' hfl
    set D := sourceProfile η ((n : ℝ) + 1) - sourceProfile η' ((n : ℝ) + 1) with hD
    have hDx : D = (sourceProfile η x - sourceProfile η' x) + Δ * (x - ((n : ℝ) + 1)) := by
      rw [hD, hΔ]; linarith
    have hsmall : (Δ * (x - ((n : ℝ) + 1))) ^ 2 ≤ Δ ^ 2 := by
      rw [mul_pow]
      have h0 : 0 ≤ x - ((n : ℝ) + 1) := by linarith
      have h1 : x - ((n : ℝ) + 1) ≤ 1 := by linarith
      nlinarith [sq_nonneg Δ, mul_le_mul h1 h1 h0 zero_le_one]
    have hD2 : D ^ 2 ≤ 2 * (sourceProfile η x - sourceProfile η' x) ^ 2 + 2 * Δ ^ 2 := by
      rw [hDx]
      nlinarith [add_sq_le_two (sourceProfile η x - sourceProfile η' x) (Δ * (x - ((n : ℝ) + 1)))]
    have hinv : 1 / ((n : ℝ) + 1) ^ 2 ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (pow_pos hx0 2)]
      nlinarith
    have hcoord : orbitCoord η n - orbitCoord η' n = D / ((n : ℝ) + 1) := by
      rw [orbitCoord, orbitCoord, hD, sub_div]
    rw [hcoord]
    calc (D / ((n : ℝ) + 1)) ^ 2 = D ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
          rw [div_pow, div_eq_mul_inv, one_div]
      _ ≤ (2 * (sourceProfile η x - sourceProfile η' x) ^ 2 + 2 * Δ ^ 2) *
            (1 / ((n : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_right hD2 (by positivity)
      _ = 2 * (sourceProfile η x - sourceProfile η' x) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) +
            2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by ring
      _ ≤ 2 * (sourceProfile η x - sourceProfile η' x) ^ 2 * (4 / x ^ 2) +
            2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by gcongr
      _ = 8 * f x + 2 * Δ ^ 2 / ((n : ℝ) + 1) ^ 2 := by simp only [hf]; ring
  -- integrate over `[N, N+1]` and sum
  have hpt' : ∀ n : ℕ, (orbitCoord η n - orbitCoord η' n) ^ 2 ≤
      8 * (∫ x in a n..a (n + 1), f x) + 2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hle : a n ≤ a (n + 1) := by simp only [ha]; push_cast; linarith
    have hlen : a (n + 1) - a n = 1 := by simp only [ha]; push_cast; ring
    have hmono : ∫ x in a n..a (n + 1),
        ((orbitCoord η n - orbitCoord η' n) ^ 2 - 2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        ∫ x in a n..a (n + 1), 8 * f x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const
        ((hii n).const_mul 8) fun x hx => ?_
      have hx1 : (n : ℝ) + 1 ≤ x := by have := hx.1.le; simp only [ha] at this; exact this
      have hx2 : x < (n : ℝ) + 2 := by
        have := hx.2; simp only [ha] at this; push_cast at this; linarith
      have := hpt n x hx1 hx2
      push_cast
      linarith
    rw [intervalIntegral.integral_const, hlen, one_smul, intervalIntegral.integral_const_mul]
      at hmono
    exact sub_le_iff_le_add.mp hmono
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := a) (n := T) fun i _ => hii i
  have h0T : a 0 ≤ a T := by simp only [ha]; push_cast; linarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)]
  have htail : ∫ x in a 0..a T, f x ≤ ∫ x in Ioi (0 : ℝ), f x := by
    rw [intervalIntegral.integral_of_le h0T]
    refine setIntegral_mono_set hint (ae_of_all _ fun x => hf0 x) ?_
    exact LE.le.eventuallyLE (show Ioc (a 0) (a T) ≤ Ioi (0 : ℝ) from fun x hx =>
      lt_trans (by simp only [ha]; norm_num) hx.1)
  have hinv := sum_range_inv_succ_sq_le_two T
  have hΔ0 : 0 ≤ Δ ^ 2 := sq_nonneg _
  calc ∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord η' n) ^ 2
      ≤ ∑ n ∈ Finset.range T, (8 * (∫ x in a n..a (n + 1), f x) +
          2 * Δ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum fun n _ => hpt' n
    _ = 8 * (∫ x in a 0..a T, f x) +
          2 * Δ ^ 2 * ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ 8 * (∫ x in Ioi (0 : ℝ), f x) + 2 * Δ ^ 2 * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
          (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = 8 * (∫ x in Ioi (0 : ℝ), f x) + 4 * Δ ^ 2 := by ring

/-! ### Plancherel for source differences -/

/-- The critical-line symbol `F_η(t) = −ζ(η − s)^{−1} ζ(−s)/s`, `s = −½ + it`. -/
def criticalSymbol (η t : ℝ) : ℂ :=
  -(riemannZeta ((η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)))⁻¹ *
    (riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I)) / (((-1 / 2 : ℝ) : ℂ) + t * I))

theorem sourceBound_nonneg {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) : 0 ≤ sourceBound η := by
  have h := (abs_sourceProfile_le_bound h0 h1 one_pos).1
  rw [Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

/-- The source obeys the two-sided bound at every exponent `½ < a ≤ η`. -/
theorem abs_sourceProfile_le_of_le {η a : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) (ha : 1 / 2 < a)
    (haη : a ≤ η) {x : ℝ} (hx : 0 < x) :
    |sourceProfile η x| ≤ sourceBound η * x ^ a ∧
      |sourceProfile η x| ≤ sourceBound η * x ^ (1 - a) := by
  obtain ⟨hb1, hb2⟩ := abs_sourceProfile_le_bound h0 h1 hx
  have hB := sourceBound_nonneg h0 h1
  rcases le_total x 1 with hx1 | hx1
  · exact ⟨hb1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx hx1 haη) hB),
      hb1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)) hB)⟩
  · exact ⟨hb2.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hB),
      hb2.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hB)⟩

/-- **Plancherel for a source difference**:
`∫_0^∞ (P_η − P_{η'})² x^{−2} = (1/2π) ∫ |F_η − F_{η'}|²` for `½ < η, η' < 1`. -/
theorem integral_sq_sourceProfile_sub {η η' : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (h0' : 1 / 2 < η') (h1' : η' < 1) :
    IntegrableOn (fun x => (sourceProfile η x - sourceProfile η' x) ^ 2 / x ^ 2) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), (sourceProfile η x - sourceProfile η' x) ^ 2 / x ^ 2 =
        1 / (2 * Real.pi) * ∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol η' t‖ ^ 2 := by
  set a := min η η' with ha
  have ha0 : 1 / 2 < a := lt_min h0 h0'
  have hb : ∀ x, 0 < x → |sourceProfile η x - sourceProfile η' x| ≤
      (sourceBound η + sourceBound η') * x ^ a ∧
      |sourceProfile η x - sourceProfile η' x| ≤ (sourceBound η + sourceBound η') * x ^ (1 - a) := by
    intro x hx
    obtain ⟨p1, p2⟩ := abs_sourceProfile_le_of_le h0 h1 ha0 (min_le_left η η') hx
    obtain ⟨q1, q2⟩ := abs_sourceProfile_le_of_le h0' h1' ha0 (min_le_right η η') hx
    refine ⟨(abs_sub _ _).trans ?_, (abs_sub _ _).trans ?_⟩ <;> rw [add_mul] <;> linarith
  have hmeas : Measurable fun x => sourceProfile η x - sourceProfile η' x :=
    (measurable_sourceProfile η).sub (measurable_sourceProfile η')
  obtain ⟨hint, heq⟩ := integral_sq_div_sq_eq_mellin hmeas ha0 (fun x hx => (hb x hx).1)
    (fun x hx => (hb x hx).2)
  refine ⟨hint, heq.trans ?_⟩
  congr 2
  funext t
  have hc1 := mellinConvergent_of_two_sided (measurable_sourceProfile η) h0
    (fun x hx => (abs_sourceProfile_le_bound h0 h1 hx).1)
    (fun x hx => (abs_sourceProfile_le_bound h0 h1 hx).2) t
  have hc2 := mellinConvergent_of_two_sided (measurable_sourceProfile η') h0'
    (fun x hx => (abs_sourceProfile_le_bound h0' h1' hx).1)
    (fun x hx => (abs_sourceProfile_le_bound h0' h1' hx).2) t
  have hsub := (hasMellin_sub hc1 hc2).2
  have e : (fun x : ℝ => ((sourceProfile η x - sourceProfile η' x : ℝ) : ℂ)) =
      fun x => (sourceProfile η x : ℂ) - (sourceProfile η' x : ℂ) := by
    funext x; push_cast; rfl
  rw [e, hsub, mellin_sourceProfile_eq h0, mellin_sourceProfile_eq h0']
  rfl

/-! ### Dominated convergence on the critical line -/

/-- `|t|^{3/4} log⁴|t| / t² ≤ 2·32⁴ (1 + t²)^{−9/16}` for `|t| ≥ 1`. -/
theorem critical_decay_le {t : ℝ} (ht : 1 ≤ |t|) :
    |t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2 ≤ 2 * 32 ^ 4 * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
  set a := |t| with hadef
  have ha0 : 0 < a := by linarith
  have ht2 : t ^ 2 = a ^ 2 := (sq_abs t).symm
  rw [ht2]
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg ht
  have hlog : Real.log a ≤ 32 * a ^ (1 / 32 : ℝ) := by
    have := Real.log_le_rpow_div ha0.le (by norm_num : (0 : ℝ) < 1 / 32)
    rw [div_div_eq_mul_div, div_one] at this
    linarith
  have hlog4 : Real.log a ^ 4 ≤ 32 ^ 4 * a ^ (1 / 8 : ℝ) := by
    calc Real.log a ^ 4 ≤ (32 * a ^ (1 / 32 : ℝ)) ^ 4 := pow_le_pow_left₀ hlog0 hlog 4
      _ = 32 ^ 4 * a ^ (1 / 8 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (a ^ (1 / 32 : ℝ)), ← Real.rpow_mul ha0.le]
        norm_num
  -- `a^{3/4} a^{1/8} / a² = (a²)^{−9/16}`
  have hexp : a ^ (3 / 4 : ℝ) * a ^ (1 / 8 : ℝ) / a ^ 2 = (a ^ 2) ^ (-(9 / 16 : ℝ)) := by
    rw [← Real.rpow_add ha0, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha0.le,
      ← Real.rpow_sub ha0]
    norm_num
  have hcmp : (a ^ 2) ^ (-(9 / 16 : ℝ)) ≤ 2 * (1 + a ^ 2) ^ (-(9 / 16 : ℝ)) := by
    have h2 : 1 + a ^ 2 ≤ 2 * a ^ 2 := by nlinarith
    have hm := Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num : -(9 / 16 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hm
    have h29 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(9 / 16 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), one_div]
      apply inv_anti₀ (by positivity)
      calc (2 : ℝ) ^ (9 / 16 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ (a ^ 2) ^ (-(9 / 16 : ℝ)) := by positivity
    nlinarith
  calc a ^ (3 / 4 : ℝ) * Real.log a ^ 4 / a ^ 2
      ≤ a ^ (3 / 4 : ℝ) * (32 ^ 4 * a ^ (1 / 8 : ℝ)) / a ^ 2 := by gcongr
    _ = 32 ^ 4 * (a ^ (3 / 4 : ℝ) * a ^ (1 / 8 : ℝ) / a ^ 2) := by ring
    _ = 32 ^ 4 * (a ^ 2) ^ (-(9 / 16 : ℝ)) := by rw [hexp]
    _ ≤ 32 ^ 4 * (2 * (1 + a ^ 2) ^ (-(9 / 16 : ℝ))) := by gcongr
    _ = 2 * 32 ^ 4 * (1 + a ^ 2) ^ (-(9 / 16 : ℝ)) := by ring

/-- **Uniform domination of the critical symbol** for `½ < η < 1`. -/
theorem exists_norm_sq_criticalSymbol_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η : ℝ, 1 / 2 < η → η < 1 → ∀ t : ℝ,
      ‖criticalSymbol η t‖ ^ 2 ≤ M * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨T₀, C₁, C₂, hT₀, hC₁, hC₂, hw⟩ := exists_norm_mellin_sourceProfile_sq_le
  refine ⟨C₁ * (1 + T₀ ^ 2) ^ (9 / 16 : ℝ) + C₂ * (2 * 32 ^ 4), by positivity,
    fun η h0 h1 t => ?_⟩
  have hsym : ‖criticalSymbol η t‖ ^ 2 =
      ‖mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    rw [mellin_sourceProfile_eq h0]; rfl
  have hg0 : 0 < (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by positivity
  rw [hsym]
  rcases le_total |t| T₀ with ht | ht
  · have hlow := (hw η h0 h1 t).1 ht
    have hT : (1 + T₀ ^ 2) ^ (-(9 / 16 : ℝ)) ≤ (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
      nlinarith [sq_abs t, abs_nonneg t]
    have hone : 1 ≤ (1 + T₀ ^ 2) ^ (9 / 16 : ℝ) * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
      calc (1 : ℝ) = (1 + T₀ ^ 2) ^ (9 / 16 : ℝ) * (1 + T₀ ^ 2) ^ (-(9 / 16 : ℝ)) := by
            rw [← Real.rpow_add (by positivity)]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
    calc _ ≤ C₁ := hlow
      _ ≤ C₁ * ((1 + T₀ ^ 2) ^ (9 / 16 : ℝ) * (1 + t ^ 2) ^ (-(9 / 16 : ℝ))) :=
          le_mul_of_one_le_right hC₁ hone
      _ ≤ (C₁ * (1 + T₀ ^ 2) ^ (9 / 16 : ℝ) + C₂ * (2 * 32 ^ 4)) *
            (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
          rw [← mul_assoc, add_mul]
          exact le_add_of_nonneg_right (by positivity)
  · have hhigh := (hw η h0 h1 t).2 ht
    have hdec := critical_decay_le (show (1 : ℝ) ≤ |t| by linarith)
    calc _ ≤ C₂ * (|t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2) := hhigh
      _ ≤ C₂ * (2 * 32 ^ 4 * (1 + t ^ 2) ^ (-(9 / 16 : ℝ))) :=
          mul_le_mul_of_nonneg_left hdec hC₂
      _ ≤ (C₁ * (1 + T₀ ^ 2) ^ (9 / 16 : ℝ) + C₂ * (2 * 32 ^ 4)) *
            (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
          rw [add_mul, ← mul_assoc C₂]
          exact le_add_of_nonneg_left (by positivity)

theorem integrable_critical_majorant :
    Integrable fun t : ℝ => (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := 9 / 8) (by simp; norm_num)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  norm_num

/-- The symbol is continuous in `t` for `η > ½`. -/
theorem continuous_criticalSymbol {η : ℝ} (h0 : 1 / 2 < η) : Continuous (criticalSymbol η) := by
  have hs : Continuous fun t : ℝ => ((-1 / 2 : ℝ) : ℂ) + t * I := by fun_prop
  have hz1 : ∀ t : ℝ, (η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun t h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hz2 : ∀ t : ℝ, -(((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun t h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hne : ∀ t : ℝ, riemannZeta ((η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) ≠ 0 := fun t =>
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hs0 : ∀ t : ℝ, ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this
  unfold criticalSymbol
  refine continuous_iff_continuousAt.2 fun t => ?_
  have c1 : ContinuousAt (fun t : ℝ => riemannZeta ((η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I))) t :=
    ((differentiableAt_riemannZeta (hz1 t)).continuousAt).comp (f := fun t : ℝ =>
      (η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  have c2 : ContinuousAt (fun t : ℝ => riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I))) t :=
    ((differentiableAt_riemannZeta (hz2 t)).continuousAt).comp (f := fun t : ℝ =>
      -(((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  exact ((c1.inv₀ (hne t)).neg).mul (c2.div hs.continuousAt (hs0 t))

/-- At `t ≠ 0` the symbol is continuous in `η` at half damping: `ζ(1 − it) ≠ 0`. -/
theorem continuousAt_criticalSymbol_half {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun η => criticalSymbol η t) (1 / 2) := by
  have hz1 : ((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun h => by
    have := congrArg Complex.im h; simp at this; exact ht this
  have hne : riemannZeta (((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
  unfold criticalSymbol
  have c1 : ContinuousAt (fun η : ℝ => riemannZeta ((η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)))
      (1 / 2) :=
    ((differentiableAt_riemannZeta hz1).continuousAt).comp (f := fun η : ℝ =>
      (η : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  exact ((c1.inv₀ hne).neg).mul continuousAt_const

theorem ae_ne_zero_real : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
  rw [ae_iff]; simpa using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)

/-- The half-damping symbol is continuous away from `t = 0`. -/
theorem continuousOn_criticalSymbol_half : ContinuousOn (criticalSymbol (1 / 2)) {(0 : ℝ)}ᶜ := by
  intro t ht
  have ht' : t ≠ 0 := ht
  have hz1 : ((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun h => by
    have := congrArg Complex.im h; simp at this; exact ht' this
  have hz2 : -(((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hne : riemannZeta (((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
  have hs0 : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  unfold criticalSymbol
  have c1 : ContinuousAt (fun t : ℝ =>
      riemannZeta (((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I))) t :=
    ((differentiableAt_riemannZeta hz1).continuousAt).comp (f := fun t : ℝ =>
      ((1 / 2 : ℝ) : ℂ) - (((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  have c2 : ContinuousAt (fun t : ℝ => riemannZeta (-(((-1 / 2 : ℝ) : ℂ) + t * I))) t :=
    ((differentiableAt_riemannZeta hz2).continuousAt).comp (f := fun t : ℝ =>
      -(((-1 / 2 : ℝ) : ℂ) + t * I)) (by fun_prop)
  exact (((c1.inv₀ hne).neg).mul (c2.div (by fun_prop) hs0)).continuousWithinAt

theorem aestronglyMeasurable_criticalSymbol {η : ℝ} (h0 : 1 / 2 ≤ η) :
    AEStronglyMeasurable (criticalSymbol η) volume := by
  rcases h0.lt_or_eq with h | h
  · exact (continuous_criticalSymbol h).aestronglyMeasurable
  · subst h
    have hm := continuousOn_criticalSymbol_half.aestronglyMeasurable (μ := volume)
      (measurableSet_singleton (0 : ℝ)).compl
    rwa [restrict_compl_singleton] at hm

/-- **The domination holds on `½ ≤ η < 1`** (at `η = ½` away from `t = 0`, by continuity). -/
theorem exists_norm_sq_criticalSymbol_le_of_half_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η : ℝ, 1 / 2 ≤ η → η < 1 → ∀ t : ℝ, t ≠ 0 →
      ‖criticalSymbol η t‖ ^ 2 ≤ M * (1 + t ^ 2) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨M, hM, hdom⟩ := exists_norm_sq_criticalSymbol_le
  refine ⟨M, hM, fun η h0 h1 t ht => ?_⟩
  rcases h0.lt_or_eq with h | h
  · exact hdom η h h1 t
  · subst h
    have hlim : Tendsto (fun η => criticalSymbol η t) (𝓝[>] (1 / 2)) (𝓝 (criticalSymbol (1 / 2) t)) :=
      (continuousAt_criticalSymbol_half ht).tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ((continuous_norm.tendsto _).comp hlim |>.pow 2) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with η hη
    exact hdom η hη.1 hη.2 t

theorem integrable_norm_sq_criticalSymbol_sub {η η' : ℝ} (h0 : 1 / 2 ≤ η) (h1 : η < 1)
    (h0' : 1 / 2 ≤ η') (h1' : η' < 1) :
    Integrable fun t : ℝ => ‖criticalSymbol η t - criticalSymbol η' t‖ ^ 2 := by
  obtain ⟨M, hM, hdom⟩ := exists_norm_sq_criticalSymbol_le_of_half_le
  refine Integrable.mono' ((integrable_critical_majorant.const_mul M).const_mul 4)
    (((aestronglyMeasurable_criticalSymbol h0).sub
      (aestronglyMeasurable_criticalSymbol h0')).norm.pow 2) ?_
  filter_upwards [ae_ne_zero_real] with t ht
  have e1 := hdom η h0 h1 t ht
  have e2 := hdom η' h0' h1' t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖criticalSymbol η t - criticalSymbol η' t‖ ^ 2
      ≤ (‖criticalSymbol η t‖ + ‖criticalSymbol η' t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    _ ≤ 2 * ‖criticalSymbol η t‖ ^ 2 + 2 * ‖criticalSymbol η' t‖ ^ 2 := by
        nlinarith [sq_nonneg (‖criticalSymbol η t‖ - ‖criticalSymbol η' t‖)]
    _ ≤ 4 * (M * (1 + t ^ 2) ^ (-(9 / 16 : ℝ))) := by linarith

/-- `∫ |F_η − F_{η'}|² ≤ 2 ∫ |F_η − F_{½}|² + 2 ∫ |F_{η'} − F_{½}|²`. -/
theorem integral_norm_sq_criticalSymbol_sub_le {η η' : ℝ} (h0 : 1 / 2 ≤ η) (h1 : η < 1)
    (h0' : 1 / 2 ≤ η') (h1' : η' < 1) :
    ∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol η' t‖ ^ 2 ≤
      2 * (∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ ^ 2) +
        2 * ∫ t : ℝ, ‖criticalSymbol η' t - criticalSymbol (1 / 2) t‖ ^ 2 := by
  have hh : (1 / 2 : ℝ) ≤ 1 / 2 := le_rfl
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have i1 := integrable_norm_sq_criticalSymbol_sub h0 h1 hh hh1
  have i2 := integrable_norm_sq_criticalSymbol_sub h0' h1' hh hh1
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine integral_mono (integrable_norm_sq_criticalSymbol_sub h0 h1 h0' h1')
    ((i1.const_mul 2).add (i2.const_mul 2)) fun t => ?_
  have e : criticalSymbol η t - criticalSymbol η' t =
      (criticalSymbol η t - criticalSymbol (1 / 2) t) -
        (criticalSymbol η' t - criticalSymbol (1 / 2) t) := by ring
  simp only
  rw [e]
  calc ‖(criticalSymbol η t - criticalSymbol (1 / 2) t) -
        (criticalSymbol η' t - criticalSymbol (1 / 2) t)‖ ^ 2
      ≤ (‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ +
          ‖criticalSymbol η' t - criticalSymbol (1 / 2) t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    _ ≤ _ := by
        nlinarith [sq_nonneg (‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ -
          ‖criticalSymbol η' t - criticalSymbol (1 / 2) t‖)]

/-- **The critical symbol converges in mean square as `η ↓ ½`.** -/
theorem tendsto_integral_sq_criticalSymbol_sub :
    Tendsto (fun η => ∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ ^ 2)
      (𝓝[>] (1 / 2)) (𝓝 0) := by
  obtain ⟨M, hM, hdom⟩ := exists_norm_sq_criticalSymbol_le_of_half_le
  have hev : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), η ∈ Ioo (1 / 2 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num)
  have hlim : ∀ t : ℝ, t ≠ 0 →
      Tendsto (fun η => criticalSymbol η t) (𝓝[>] (1 / 2)) (𝓝 (criticalSymbol (1 / 2) t)) :=
    fun t ht => (continuousAt_criticalSymbol_half ht).tendsto.mono_left nhdsWithin_le_nhds
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (1 / 2 : ℝ))
    (F := fun η t => ‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ ^ 2) (f := fun _ => 0)
    (fun t => 4 * (M * (1 + t ^ 2) ^ (-(9 / 16 : ℝ))))
    (by
      filter_upwards [hev] with η hη
      exact (((aestronglyMeasurable_criticalSymbol hη.1.le).sub
        (aestronglyMeasurable_criticalSymbol le_rfl)).norm.pow 2))
    (by
      filter_upwards [hev] with η hη
      filter_upwards [ae_ne_zero_real] with t ht
      have h1 := hdom η hη.1.le hη.2 t ht
      have h2 := hdom (1 / 2) le_rfl (by norm_num) t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ ^ 2
          ≤ (‖criticalSymbol η t‖ + ‖criticalSymbol (1 / 2) t‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
        _ ≤ 2 * ‖criticalSymbol η t‖ ^ 2 + 2 * ‖criticalSymbol (1 / 2) t‖ ^ 2 := by
            nlinarith [sq_nonneg (‖criticalSymbol η t‖ - ‖criticalSymbol (1 / 2) t‖)]
        _ ≤ 4 * (M * (1 + t ^ 2) ^ (-(9 / 16 : ℝ))) := by linarith)
    ((integrable_critical_majorant.const_mul M).const_mul 4)
    (by
      filter_upwards [ae_ne_zero_real] with t ht
      have h := ((continuous_norm.tendsto _).comp
        ((hlim t ht).sub (tendsto_const_nhds (x := criticalSymbol (1 / 2) t)))).pow 2
      simpa using h)
  simpa using hconv

/-! ### The receiver at half damping -/

/-- **The receiver is continuous at half damping**: `u_η → u_{½}` in `ℓ²` as `η ↓ ½`; for every
`ε > 0`, eventually `Σ_{n<T} (u_η − u_{½})(n)² ≤ ε` at every horizon `T`. -/
theorem orbit_l2_tendsto_half :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), ∀ T : ℕ,
      ∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord (1 / 2) n) ^ 2 ≤ ε := by
  intro ε hε
  set Φ : ℝ → ℝ := fun η => ∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol (1 / 2) t‖ ^ 2
    with hΦ
  set ρ : ℝ → ℝ := fun η => (RHTower.pmPowerDampedDivisorDensity η).re with hρ
  have hΦ0 := tendsto_integral_sq_criticalSymbol_sub
  have hρc : Tendsto ρ (𝓝[>] (1 / 2)) (𝓝 (ρ (1 / 2))) :=
    (continuousAt_density_re (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), η ∈ Ioo (1 / 2 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  set δ : ℝ := ε / (16 / Real.pi + 8) with hδ
  have hδ0 : 0 < δ := by positivity
  have hρδ : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), (ρ η - ρ (1 / 2)) ^ 2 < δ := by
    have h := ((hρc.sub (tendsto_const_nhds (x := ρ (1 / 2)))).pow 2)
    rw [sub_self, zero_pow two_ne_zero] at h
    exact h.eventually (gt_mem_nhds hδ0)
  filter_upwards [hev, hΦ0.eventually (gt_mem_nhds hδ0), hρδ] with η hη hΦη hρη
  intro T
  -- the horizon-`T` sum against every `η'` closer to `½`
  have hbound : ∀ᶠ η' in 𝓝[>] (1 / 2 : ℝ),
      ∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord η' n) ^ 2 ≤
        8 * (1 / (2 * Real.pi) * (2 * Φ η + 2 * Φ η')) + 4 * (ρ η - ρ η') ^ 2 := by
    filter_upwards [hev] with η' hη'
    obtain ⟨hint, heq⟩ := integral_sq_sourceProfile_sub hη.1 hη.2 hη'.1 hη'.2
    have hA := sum_sq_orbitCoord_sub_le η η' T hint
    rw [heq] at hA
    have hI := integral_norm_sq_criticalSymbol_sub_le hη.1.le hη.2 hη'.1.le hη'.2
    calc _ ≤ 8 * (1 / (2 * Real.pi) *
            ∫ t : ℝ, ‖criticalSymbol η t - criticalSymbol η' t‖ ^ 2) + 4 * (ρ η - ρ η') ^ 2 := hA
      _ ≤ _ := by gcongr
  -- let `η' ↓ ½`
  have hlimL : Tendsto (fun η' => ∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord η' n) ^ 2)
      (𝓝[>] (1 / 2)) (𝓝 (∑ n ∈ Finset.range T, (orbitCoord η n - orbitCoord (1 / 2) n) ^ 2)) :=
    tendsto_finsetSum _ fun n _ =>
      (tendsto_const_nhds.sub ((continuousAt_orbitCoord n (by norm_num)).tendsto.mono_left
        nhdsWithin_le_nhds)).pow 2
  have hlimR : Tendsto (fun η' => 8 * (1 / (2 * Real.pi) * (2 * Φ η + 2 * Φ η')) +
      4 * (ρ η - ρ η') ^ 2) (𝓝[>] (1 / 2))
      (𝓝 (8 * (1 / (2 * Real.pi) * (2 * Φ η + 2 * 0)) + 4 * (ρ η - ρ (1 / 2)) ^ 2)) :=
    (((tendsto_const_nhds.add (hΦ0.const_mul 2)).const_mul _).const_mul 8).add
      (((tendsto_const_nhds.sub hρc).pow 2).const_mul 4)
  have hle := le_of_tendsto_of_tendsto hlimL hlimR hbound
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsplit : 8 * (1 / (2 * Real.pi) * (2 * Φ η + 2 * 0)) + 4 * (ρ η - ρ (1 / 2)) ^ 2 =
      (8 / Real.pi) * Φ η + 4 * (ρ η - ρ (1 / 2)) ^ 2 := by field_simp; ring
  have hfin : (8 / Real.pi) * δ + 4 * δ ≤ ε := by
    rw [hδ]
    have e : (8 / Real.pi) * (ε / (16 / Real.pi + 8)) + 4 * (ε / (16 / Real.pi + 8)) = ε / 2 := by
      field_simp; ring
    linarith
  calc _ ≤ _ := hle
    _ = _ := hsplit
    _ ≤ (8 / Real.pi) * δ + 4 * δ := by gcongr
    _ ≤ ε := hfin

/-- The orbit at half damping is the `ℓ²` limit: `C_η r → C_{½} r` as `η ↓ ½`. -/
theorem centeredOperator_reciprocal_l2_tendsto_half :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), ∀ (hη : 0 < η) (T : ℕ),
      ∑ n ∈ Finset.range T, (arithmeticDampingCenteredOperator hη reciprocalObservable n -
        arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2)
          reciprocalObservable n) ^ 2 ≤ ε := by
  intro ε hε
  filter_upwards [orbit_l2_tendsto_half ε hε] with η h hη T
  simp only [centeredOperator_reciprocal_eq_orbitCoord]
  exact h T

/-! ### The positive twin blows up -/

theorem tendsto_positiveTwin_half (n : ℕ) :
    Tendsto (fun ε => positiveTwin ε n) (𝓝[>] (1 / 2)) (𝓝 (positiveTwin (1 / 2) n)) := by
  unfold positiveTwin
  refine tendsto_tsum_of_dominated_convergence (bound := fun d : ℕ => (d : ℝ) ^ (-(3 / 2 : ℝ)))
    (Real.summable_nat_rpow.mpr (by norm_num)) (fun d => ?_) ?_
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      refine (((continuous_const.rpow continuous_neg fun _ => Or.inl hd'.ne').tendsto
        (1 / 2)).mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with ε hε d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [Real.norm_eq_abs]
      exact (abs_rpow_mul_normalizedResidueProfile_le hd n).trans
        (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith [hε.1]))

/-- **The positive twin blows up at half damping**: for every `B`, eventually as `ε ↓ ½` some
horizon energy of `Σ_d d^{−ε} v_d` exceeds `B`. -/
theorem positiveTwin_energy_unbounded (B : ℝ) :
    ∀ᶠ ε in 𝓝[>] (1 / 2 : ℝ), ∃ T : ℕ, B < ∑ n ∈ Finset.range T, positiveTwin ε n ^ 2 := by
  have hns := not_summable_positiveTwin (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => sq_nonneg _).mp hns
  obtain ⟨T, hT⟩ := (htend.eventually (eventually_gt_atTop (B + 1))).exists
  have hlim : Tendsto (fun ε => ∑ n ∈ Finset.range T, positiveTwin ε n ^ 2) (𝓝[>] (1 / 2))
      (𝓝 (∑ n ∈ Finset.range T, positiveTwin (1 / 2) n ^ 2)) :=
    tendsto_finsetSum _ fun n _ => (tendsto_positiveTwin_half n).pow 2
  filter_upwards [hlim.eventually (eventually_gt_nhds (show B < _ by linarith))] with ε hε
  exact ⟨T, hε⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
