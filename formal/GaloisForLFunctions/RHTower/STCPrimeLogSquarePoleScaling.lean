import GaloisForLFunctions.RHTower.STCSourceWorkSeamEnergy
import GaloisForLFunctions.RHTower.STCGammaPrimeWallScaling

/-!
# Moving scaling at the prime log-square pole

For `Re z > 0` put `F(z) = Σ_p (log p)² p^{-1-z}`.  Near `z = 0`, `F(z) = z^{-2} + R(1+z)` with `R`
continuous at `1` (the pole of `-ζ'/ζ` and the prime-power correction).  Consequently, whenever
`w(v) → w₀` with `Re w₀ > 0`,

`v² F(v w(v)) → w₀^{-2}`   as `v → 0⁺`.

The phase-twisted depth-zero vectors `p^{iτ} b_u(p)` of `ℓ²(primes)` have inner products
`⟪p^{is} b_β, p^{it} b_α⟫ = F((α+β)/2 - i(t-s))`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-- **Laurent expansion at the pole.** `F(s) = (s-1)^{-2} + R(s)` near `s = 1`, `R` continuous at
`1`. -/
theorem primeLogSquareContinuation_laurent_one :
    ∃ R : ℂ → ℂ, ContinuousAt R 1 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), primeLogSquareContinuation s = ((s - 1) ^ 2)⁻¹ + R s := by
  obtain ⟨G, hG, hQ⟩ := primeLogCriticalContinuation_laurent_one
  have hQ' : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 →
      primeLogCriticalContinuation s = (s - 1)⁻¹ + G s := eventually_nhdsWithin_iff.mp hQ
  have hGd : ∀ᶠ s in 𝓝 (1 : ℂ), DifferentiableAt ℂ G s :=
    hG.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  refine ⟨fun s => -deriv G s, hG.deriv.continuousAt.neg, ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hQ'.eventually_nhds,
    nhdsWithin_le_nhds hGd] with s hs hnear hdG
  have hs' : s ≠ 1 := hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs'
  have hloc : primeLogCriticalContinuation =ᶠ[𝓝 s] fun z => (z - 1)⁻¹ + G z := by
    filter_upwards [hnear, isOpen_ne.mem_nhds hs'] with z hz hz'
    exact hz hz'
  have hinv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
    exact h1.inv hs1
  have hsum : HasDerivAt (fun z => (z - 1)⁻¹ + G z) (-1 / (s - 1) ^ 2 + deriv G s) s :=
    hinv.add hdG.hasDerivAt
  rw [primeLogSquareContinuation, hloc.deriv_eq, hsum.deriv]
  field_simp
  ring

/-- **Moving pole scaling.** If `w(v) → w₀` with `Re w₀ > 0`, then `v² F(v w(v)) → w₀^{-2}`. -/
theorem tendsto_sq_mul_primeLogSquareComplex {w : ℝ → ℂ} {w₀ : ℂ} (hw₀ : 0 < w₀.re)
    (hw : Tendsto w (𝓝[>] 0) (𝓝 w₀)) :
    Tendsto (fun v : ℝ => (v : ℂ) ^ 2 * primeLogSquareComplex (1 + v * w v)) (𝓝[>] 0)
      (𝓝 (w₀ ^ 2)⁻¹) := by
  obtain ⟨R, hR, hF⟩ := primeLogSquareContinuation_laurent_one
  have hw0 : w₀ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw₀; exact lt_irrefl _ hw₀
  have hre : ∀ᶠ v in 𝓝[>] (0 : ℝ), 0 < (w v).re :=
    (Complex.continuous_re.tendsto w₀).comp hw |>.eventually (eventually_gt_nhds hw₀)
  have hv0 : Tendsto (fun v : ℝ => (v : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun v : ℝ => (v : ℂ)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun v : ℝ => 1 + (v : ℂ) * w v) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using tendsto_const_nhds.add (hv0.mul hw)
    · filter_upwards [hre, self_mem_nhdsWithin] with v hv hvpos
      intro h
      simp only [Set.mem_singleton_iff, add_eq_left, mul_eq_zero, Complex.ofReal_eq_zero] at h
      rcases h with h | h
      · exact (ne_of_gt hvpos) h
      · rw [h, Complex.zero_re] at hv; exact lt_irrefl _ hv
  have hmain : Tendsto (fun v : ℝ => (w v ^ 2)⁻¹ + (v : ℂ) ^ 2 * R (1 + (v : ℂ) * w v))
      (𝓝[>] 0) (𝓝 ((w₀ ^ 2)⁻¹ + 0 ^ 2 * R 1)) := by
    refine ((hw.pow 2).inv₀ (pow_ne_zero 2 hw0)).add ((hv0.pow 2).mul ?_)
    exact hR.tendsto.comp (hs.mono_right nhdsWithin_le_nhds)
  rw [zero_pow two_ne_zero, zero_mul, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [hs.eventually hF, hre, self_mem_nhdsWithin] with v hFv hv hvpos
  have hvpos' : (0 : ℝ) < v := hvpos
  have hwv : w v ≠ 0 := fun h => by rw [h, Complex.zero_re] at hv; exact lt_irrefl _ hv
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hvpos'.ne'
  have hs1 : 1 < (1 + (v : ℂ) * w v).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  rw [← primeLogSquareContinuation_eq hs1, hFv, add_sub_cancel_left]
  field_simp

/-! ### Exponential forms of the prime amplitudes -/

theorem natCast_prime_cpow (p : Nat.Primes) (w : ℂ) :
    ((p : ℕ) : ℂ) ^ w = Complex.exp (w * (Real.log (p : ℕ) : ℂ)) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp, Complex.natCast_log, mul_comm]

theorem stcDepthZeroAmplitude_eq_exp (u : ℝ) (p : Nat.Primes) :
    stcDepthZeroAmplitude u p =
      Real.log (p : ℕ) * Real.exp (-((1 + u) / 2) * Real.log (p : ℕ)) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp
  refine (pow_left_inj₀ (stcDepthZeroAmplitude_pos u p).le (by positivity) two_ne_zero).mp ?_
  rw [stcDepthZeroAmplitude_sq, mul_pow, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (by linarith)]
  congr 2
  push_cast
  ring

/-- The prime log-square series term in exponential form. -/
theorem primeLogSquareComplex_eq_tsum_exp (s : ℂ) :
    primeLogSquareComplex s = ∑' p : Nat.Primes,
      (Real.log (p : ℕ) : ℂ) ^ 2 * Complex.exp (-s * (Real.log (p : ℕ) : ℂ)) := by
  unfold primeLogSquareComplex
  refine tsum_congr fun p => ?_
  rw [natCast_prime_cpow]

/-- **Twisted Gram.** `⟪p^{is} b_β, p^{it} b_α⟫ = F((α+β)/2 - i(t-s))` for `α, β > 0`. -/
theorem inner_stcVerticalPhaseTwist_stcBoundaryVec {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (s t : ℝ) :
    inner ℂ (stcVerticalPhaseTwist s (stcBoundaryVec β)) (stcVerticalPhaseTwist t (stcBoundaryVec α))
      = primeLogSquareComplex (1 + (((α + β) / 2 : ℝ) : ℂ) - ((t - s : ℝ) : ℂ) * Complex.I) := by
  rw [lp.inner_eq_tsum, primeLogSquareComplex_eq_tsum_exp]
  refine tsum_congr fun p => ?_
  change inner ℂ (((p : ℕ) : ℂ) ^ ((s : ℂ) * Complex.I) * (stcBoundaryVec β : Nat.Primes → ℂ) p)
    (((p : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) * (stcBoundaryVec α : Nat.Primes → ℂ) p) = _
  rw [stcBoundaryVec_apply hα, stcBoundaryVec_apply hβ, RCLike.inner_apply, natCast_prime_cpow,
    natCast_prime_cpow, stcDepthZeroAmplitude_eq_exp, stcDepthZeroAmplitude_eq_exp, map_mul,
    ← Complex.exp_conj, Complex.conj_ofReal]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  rw [show ∀ x y z w : ℂ, x * y * (z * w) = (y * w) * (x * z) from fun x y z w => by ring,
    ← Complex.exp_add]
  have e : ∀ A x y z : ℂ, A * Complex.exp x * (A * Complex.exp y) * Complex.exp z =
      A ^ 2 * Complex.exp (x + y + z) := by
    intro A x y z; rw [Complex.exp_add, Complex.exp_add]; ring
  rw [e]
  congr 2
  ring

/-- The untwisted Gram `⟪b_β, b_α⟫ = F((α+β)/2)`. -/
theorem inner_stcBoundaryVec {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    inner ℂ (stcBoundaryVec β) (stcBoundaryVec α)
      = primeLogSquareComplex (1 + (((α + β) / 2 : ℝ) : ℂ)) := by
  have h := inner_stcVerticalPhaseTwist_stcBoundaryVec hα hβ 0 0
  have htw : ∀ f : ℓ²P, stcVerticalPhaseTwist 0 f = f := by
    intro f; ext p
    change ((p : ℕ) : ℂ) ^ (((0 : ℝ) : ℂ) * Complex.I) * (f : Nat.Primes → ℂ) p = _
    simp
  rw [htw, htw] at h
  rw [h]
  simp

end

end RHTower
