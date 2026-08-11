import GaloisForLFunctions.RHTower.DeningerLatticeFrequency

/-!
# Accumulating zeros of the transform kill the cochain

On the real axis the Fourier–Laplace transform is the ordinary Fourier transform,
`ĥ(2πξ) = ℱh(ξ)`, so `ĥ ≡ 0` forces `h = 0` by Fourier inversion.

Since `ĥ` is entire, a sequence of nonzero frequencies converging to `0` at which `ĥ` vanishes is
already enough: the identity theorem propagates the vanishing to the whole plane.  This is the
mechanism of the cofinal tomography theorem — the lattice frequencies `2π/L_q` accumulate at `0`
precisely when the periods `L_q` are unbounded.

* `deningerFourierLaplace_real` : **`ĥ(2πξ) = ℱh(ξ)`.**
* `deningerSource_eq_zero_of_fourierLaplace_zero` : `ĥ ≡ 0` forces `h = 0`.
* `deningerSource_eq_zero_of_zeros_tendsto` : **accumulating zeros force `h = 0`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform Filter Topology

noncomputable section

/-- **On the real axis the Fourier–Laplace transform is the Fourier transform.** -/
theorem deningerFourierLaplace_real (h : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    deningerFourierLaplace h (((2 * Real.pi * ξ : ℝ) : ℂ)) = 𝓕 ((h : ℝ → ℂ)) ξ := by
  rw [deningerFourierLaplace, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (h : ℝ → ℂ) t * deningerLaplaceKernel (((2 * Real.pi * ξ : ℝ) : ℂ)) t
    = Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) • (h : ℝ → ℂ) t
  rw [deningerLaplaceKernel, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- Vanishing of the transform forces the cochain to vanish. -/
theorem deningerSource_eq_zero_of_fourierLaplace_zero {h : 𝓢(ℝ, ℂ)}
    (hzero : ∀ z : ℂ, deningerFourierLaplace h z = 0) : h = 0 := by
  have hfour : (𝓕 h : 𝓢(ℝ, ℂ)) = 0 := by
    refine SchwartzMap.ext fun ξ => ?_
    have hcoe : ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 ((h : ℝ → ℂ)) := SchwartzMap.fourier_coe h
    have hval : 𝓕 ((h : ℝ → ℂ)) ξ = 0 := by
      rw [← deningerFourierLaplace_real h ξ]
      exact hzero _
    have : ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ = 0 := by rw [hcoe]; exact hval
    simpa using this
  have hinv : (𝓕⁻ (𝓕 h) : 𝓢(ℝ, ℂ)) = h := fourierInv_fourier_eq h
  rw [hfour] at hinv
  rw [← hinv]
  simp

/-- **Accumulating zeros of the transform force the cochain to vanish.**  The transform is entire,
so the identity theorem propagates vanishing from a sequence of nonzero frequencies converging to
the origin. -/
theorem deningerSource_eq_zero_of_zeros_tendsto {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (z : ℕ → ℂ) (hzne : ∀ n, z n ≠ 0) (hztend : Tendsto z atTop (𝓝 0))
    (hzero : ∀ n, deningerFourierLaplace h (z n) = 0) : h = 0 := by
  have hdiff : Differentiable ℂ (deningerFourierLaplace h) :=
    deningerFourierLaplace_differentiable hh
  have hana : AnalyticOnNhd ℂ (deningerFourierLaplace h) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have htend : Tendsto z atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hztend, Eventually.of_forall fun n => hzne n⟩
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), deningerFourierLaplace h w = 0 :=
    htend.frequently ((Eventually.of_forall hzero).frequently)
  have hEq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hfreq
  exact deningerSource_eq_zero_of_fourierLaplace_zero fun w => hEq (Set.mem_univ w)

/-- **The cofinal tomography theorem.**  A cochain whose periodizations vanish along a family of
periods with `2π/L` accumulating at the origin is zero. -/
theorem deningerCofinalTomography {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (L : ℕ → ℝ) (hLpos : ∀ n, 0 < L n) (hLtend : Tendsto L atTop atTop)
    (hper : ∀ n, ∀ t : ℝ, deningerPeriodizationSum h (L n) t = 0) : h = 0 := by
  refine deningerSource_eq_zero_of_zeros_tendsto hh
    (fun n => ((2 * Real.pi * (1 : ℝ) / L n : ℝ) : ℂ)) (fun n => ?_) ?_ (fun n => ?_)
  · have hLn : 0 < L n := hLpos n
    have hne : (2 * Real.pi * (1 : ℝ) / L n) ≠ 0 := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      positivity
    simpa using hne
  · have hreal : Tendsto (fun n => 2 * Real.pi * (1 : ℝ) / L n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hLtend
    have hc : Tendsto (fun n => ((2 * Real.pi * (1 : ℝ) / L n : ℝ) : ℂ)) atTop
        (𝓝 (((0 : ℝ) : ℂ))) := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    rw [Complex.ofReal_zero] at hc
    exact hc
  · have hk := deningerFourierLaplace_vanishes_at_lattice hh (hLpos n) (hper n) 1
    simpa using hk

/-- **Cofinal prime tomography.**  A cochain whose `log q`-periodization vanishes for every prime in
an infinite set of primes is zero: the periods `log q` are unbounded, so the lattice frequencies
`2π/log q` accumulate at the origin. -/
theorem deningerCofinalPrimeTomography {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {Q : Set ℕ} (hQinf : Q.Infinite) (hQp : ∀ q ∈ Q, Nat.Prime q)
    (hper : ∀ q ∈ Q, ∀ t : ℝ, deningerPeriodizationSum h (Real.log q) t = 0) : h = 0 := by
  set e := Set.Infinite.natEmbedding Q hQinf with he
  set q : ℕ → ℕ := fun n => ((e n : Q) : ℕ) with hq
  have hmem : ∀ n, q n ∈ Q := fun n => (e n).2
  have hqinj : Function.Injective q := fun a b hab => e.injective (Subtype.ext hab)
  have hqtend : Tendsto q atTop atTop := by
    have hcof := hqinj.tendsto_cofinite
    rwa [Nat.cofinite_eq_atTop] at hcof
  have hone : ∀ n, (1 : ℝ) < (q n : ℝ) := by
    intro n
    have hp := hQp _ (hmem n)
    exact_mod_cast hp.one_lt
  refine deningerCofinalTomography hh (fun n => Real.log (q n)) (fun n => Real.log_pos (hone n))
    ?_ (fun n => hper (q n) (hmem n))
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hqtend)

/-- **Cross-prime compact traces are algebraically conservative modulo any subspace.**  If two
cochains have the same periodization on every prime circle of an infinite prime set, they are
equal; hence the induced map on any quotient is injective. -/
theorem deningerCofinalPrimeTomography_eq {h b : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (hb : b ∈ DeningerExpSchwartz) {Q : Set ℕ} (hQinf : Q.Infinite) (hQp : ∀ q ∈ Q, Nat.Prime q)
    (heq : ∀ q ∈ Q, ∀ t : ℝ, deningerPeriodizationSum h (Real.log q) t
      = deningerPeriodizationSum b (Real.log q) t) : h = b := by
  have hsub : h - b ∈ DeningerExpSchwartz := Submodule.sub_mem _ hh hb
  have hzero : h - b = 0 := by
    refine deningerCofinalPrimeTomography hsub hQinf hQp fun q hq t => ?_
    have hp := hQp q hq
    have hLpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [deningerPeriodizationSum_sub hh hb hLpos t, heq q hq t, sub_self]
  have := sub_eq_zero.1 hzero
  exact this

end

end RHTower
