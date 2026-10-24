import GaloisForLFunctions.SignedSuccessorArithmetic.TheSpectralHypercubeFormIsUnbounded
import GaloisForLFunctions.BezoutValuationIncidence.BezoutCouplingAndCrossDepthCancellation
import GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier

/-!
# The hypercube Dirichlet form is unbounded below half damping

Bézout–Valuation Incidence defines the hypercube Dirichlet form of the Ramanujan step vector
`v = f_r`,

  `Q_ε(P) = Σ_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{−1/2−ε} Φ_r(d₁/d₂)`,  `Φ_r(c) = Re⟨v, D_c v⟩`,

proves it nonnegative, and proves it bounded uniformly in squarefree `P` for `ε > 1/2`. Its uniform
boundedness for `0 < ε ≤ 1/2` was recorded as an open problem (BVI §7.5) and as a candidate entry
point of the successor input (review-2410, research topic 3).

This module settles the range `−1/2 ≤ ε < 1/2` in the negative, unconditionally:

1. **Spectral form of the profile.** Restricting `v` to the half line and applying the Mellin
   unitary, `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ` with `W = |𝓜v|² ≥ 0` integrable and
   `∫ W = Φ_r(1) > 0` (`dilationProfile_eq_integral`).
2. **Divisor expansion.** For `P = ∏_{p ∈ S} p`,
   `Σ_{d₁, d₂ ∣ P} μ(d₁)μ(d₂)(d₁d₂)^{−σ} cos(θ log(d₁/d₂)) = ∏_{p ∈ S} |1 − p^{−σ} e^{iθ log p}|²`
   (`hypercube_cos_sum_eq_eulerProductSq`), so `Q_ε(P) = ∫ W(ξ) ∏_{p ∈ S} |1 − p^{−σ+2πiξ}|² dξ`.
3. **Divergence.** By `TheSpectralHypercubeFormIsUnbounded` this is unbounded for `σ = 1/2 + ε < 1`
   (`hypercubeDilationDirichletForm_unbounded`).

The threshold `ε = 1/2` is the abscissa of absolute convergence of the Euler product and has
nothing to do with the zeros of `ζ`: the divergence is driven by the prime number theorem, that is
by the pole. Cross-depth cancellation of the hypercube form is therefore not a form of the
quasi-Riemann hypothesis; the finite form of `ζ(1+ε) ζ(1+ε)^{−1} = 1` that a receiver can use must
be cut by size, not by prime support.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Filter
open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
open scoped InnerProductSpace ArithmeticFunction.Moebius

section Profile

variable {r : ℕ} (hr : 1 < r)

/-- The Ramanujan step vector restricted to the half line. -/
noncomputable def stepHalfLine : HalfLineL2 :=
  ((Lp.memLp (pmRamanujanStepVector r hr)).restrict (Ioi (0 : ℝ))).toLp _

theorem pmRamanujanStepSource_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    pmRamanujanStepSource r x = 0 := by
  simp [pmRamanujanStepSource, stepFun, Nat.floor_of_nonpos hx, pmRamanujanPrimitive]

theorem stepVector_ae_eq :
    (pmRamanujanStepVector r hr : ℝ → ℂ) =ᵐ[volume] pmRamanujanStepSource r :=
  (memLp_pmRamanujanStepSource hr).coeFn_toLp

theorem stepHalfLine_ae_eq :
    (stepHalfLine hr : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] pmRamanujanStepSource r :=
  ((Lp.memLp (pmRamanujanStepVector r hr)).restrict (Ioi (0 : ℝ))).coeFn_toLp.trans
    (ae_restrict_of_ae (stepVector_ae_eq hr))

/-- The dilated step vector has representative `√c · g(c x)`. -/
theorem rayDilate_stepVector_ae_eq {c : ℝ} (hc : 0 < c) :
    (rayDilate c (pmRamanujanStepVector r hr) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt c : ℂ) * pmRamanujanStepSource r (c * x) := by
  rw [rayDilate_of_pos hc]
  filter_upwards [dilation_ae c hc (pmRamanujanStepVector r hr),
    (stepVector_ae_eq hr).comp_tendsto (realMul_quasiMeasurePreserving c hc.ne').tendsto_ae]
    with x h1 h2
  rw [h1]
  simp only [Function.comp_apply] at h2
  rw [h2]

/-- **The profile is a half-line inner product.** `⟨v, D_c v⟩ = ⟨v|₊, D_c v|₊⟩`. -/
theorem inner_stepVector_rayDilate {c : ℝ} (hc : 0 < c) :
    ⟪pmRamanujanStepVector r hr, rayDilate c (pmRamanujanStepVector r hr)⟫_ℂ =
      ⟪stepHalfLine hr, halfLineDilation c (stepHalfLine hr)⟫_ℂ := by
  set g := pmRamanujanStepSource r
  set g' : ℝ → ℂ := fun x => (Real.sqrt c : ℂ) * g (c * x)
  have hmem : MemLp g' 2 (volume.restrict (Ioi (0 : ℝ))) :=
    ((Lp.memLp (rayDilate c (pmRamanujanStepVector r hr))).ae_eq
      (rayDilate_stepVector_ae_eq hr hc)).restrict _
  have hdil : halfLineDilation c (stepHalfLine hr) = hmem.toLp g' :=
    halfLineDilation_eq_of_ae hc (stepHalfLine_ae_eq hr) hmem.coeFn_toLp fun _ _ => rfl
  rw [hdil, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hfull : ∫ x, ⟪(pmRamanujanStepVector r hr : ℝ → ℂ) x,
      (rayDilate c (pmRamanujanStepVector r hr) : ℝ → ℂ) x⟫_ℂ =
      ∫ x, (starRingEnd ℂ (g x)) * g' x := by
    refine integral_congr_ae ?_
    filter_upwards [stepVector_ae_eq hr, rayDilate_stepVector_ae_eq hr hc] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
    simp only [g, g']
    ring
  have hhalf : ∫ x in Ioi (0 : ℝ), ⟪(stepHalfLine hr : ℝ → ℂ) x, (hmem.toLp g' : ℝ → ℂ) x⟫_ℂ =
      ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ (g x)) * g' x := by
    refine integral_congr_ae ?_
    filter_upwards [stepHalfLine_ae_eq hr, hmem.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
    simp only [g]
    ring
  rw [hfull, hhalf, setIntegral_eq_integral_of_ae_compl_eq_zero]
  refine Eventually.of_forall fun x hx => ?_
  have hx0 : x ≤ 0 := not_lt.mp hx
  simp [g, pmRamanujanStepSource_eq_zero_of_nonpos hx0]

/-- The spectral weight of the step vector: `W(ξ) = |𝓜(v|₊)(ξ)|²`. -/
noncomputable def stepSpectralWeight (ξ : ℝ) : ℝ :=
  ‖(halfLineMellinUnitary (stepHalfLine hr) : ℝ → ℂ) ξ‖ ^ 2

theorem stepSpectralWeight_nonneg (ξ : ℝ) : 0 ≤ stepSpectralWeight hr ξ := by
  unfold stepSpectralWeight; positivity

theorem integrable_stepSpectralWeight : Integrable (stepSpectralWeight hr) := by
  have := (Lp.memLp (halfLineMellinUnitary (stepHalfLine hr))).integrable_norm_rpow
    (by norm_num) (by norm_num)
  rw [show stepSpectralWeight hr =
    fun ξ => ‖(halfLineMellinUnitary (stepHalfLine hr) : ℝ → ℂ) ξ‖ ^ 2 from rfl]
  simpa using this

/-- **Spectral form of the dilation profile.** `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ`. -/
theorem dilationProfile_eq_integral {c : ℝ} (hc : 0 < c) :
    pmRamanujanDilationProfile r hr c =
      ∫ ξ, stepSpectralWeight hr ξ * Real.cos (2 * Real.pi * (Real.log c * ξ)) := by
  rw [pmRamanujanDilationProfile, inner_stepVector_rayDilate hr hc, inner_halfLine_eq_integral,
    halfLineMellinUnitary_halfLineDilation]
  set F := (halfLineMellinUnitary (stepHalfLine hr) : ℝ → ℂ)
  have hcongr : (fun ξ => starRingEnd ℂ (F ξ) *
      (modulationMul (Real.log c) (halfLineMellinUnitary (stepHalfLine hr)) : ℝ → ℂ) ξ) =ᵐ[volume]
      fun ξ => ((stepSpectralWeight hr ξ : ℝ) : ℂ) * modulationSymbol (Real.log c) ξ := by
    filter_upwards [coeFn_modulationMul (Real.log c) (halfLineMellinUnitary (stepHalfLine hr))]
      with ξ h
    rw [h, stepSpectralWeight, ← mul_assoc, mul_comm (starRingEnd ℂ (F ξ)), mul_assoc,
      Complex.conj_mul', mul_comm]
    push_cast
    ring
  rw [integral_congr_ae hcongr]
  have hint : Integrable fun ξ => ((stepSpectralWeight hr ξ : ℝ) : ℂ) *
      modulationSymbol (Real.log c) ξ := by
    refine ((integrable_stepSpectralWeight hr).ofReal).mul_bdd
      (measurable_modulationSymbol _).aestronglyMeasurable (c := 1) (Eventually.of_forall ?_)
    intro ξ
    exact norm_modulationSymbol_le _ ξ
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [modulationSymbol, Complex.re_ofReal_mul]
  rw [Complex.exp_ofReal_mul_I_re]

end Profile

section Divisor

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The twisted power `d ↦ d^{−σ} e^{iθ log d}`, a multiplicative arithmetic function. -/
noncomputable def twistedPow (σ θ : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d = 0 then 0 else
    (((d : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((θ * Real.log d : ℝ) : ℂ) * Complex.I), by simp⟩

theorem twistedPow_apply {σ θ : ℝ} {d : ℕ} (hd : d ≠ 0) :
    twistedPow σ θ d =
      (((d : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((θ * Real.log d : ℝ) : ℂ) * Complex.I) := by
  simp [twistedPow, hd]

theorem isMultiplicative_twistedPow (σ θ : ℝ) : (twistedPow σ θ).IsMultiplicative := by
  refine ⟨by simp [twistedPow], fun {m n} _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [twistedPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [twistedPow]
  rw [twistedPow_apply (Nat.mul_ne_zero hm.ne' hn.ne'), twistedPow_apply hm.ne',
    twistedPow_apply hn.ne']
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  rw [mul_add, add_mul, Complex.exp_add]
  ring

theorem re_moebius_mul_twistedPow (σ θ : ℝ) {d : ℕ} (hd : d ≠ 0) :
    ((μ d : ℂ) * twistedPow σ θ d).re =
      moebiusReal d * (d : ℝ) ^ (-σ) * Real.cos (θ * Real.log d) := by
  rw [twistedPow_apply hd, moebiusReal, ← mul_assoc, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem im_moebius_mul_twistedPow (σ θ : ℝ) {d : ℕ} (hd : d ≠ 0) :
    ((μ d : ℂ) * twistedPow σ θ d).im =
      moebiusReal d * (d : ℝ) ^ (-σ) * Real.sin (θ * Real.log d) := by
  rw [twistedPow_apply hd, moebiusReal, ← mul_assoc, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem normSq_one_sub_twistedPow (σ θ : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Complex.normSq (1 - twistedPow σ θ p) = eulerFactorSq σ θ p := by
  rw [twistedPow_apply hp, Complex.normSq_apply, eulerFactorSq]
  simp only [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  linear_combination ((p : ℝ) ^ (-σ)) ^ 2 * Real.sin_sq_add_cos_sq (θ * Real.log p)

/-- `Σ_{d₁, d₂} c(d₁) c(d₂) cos(t(d₁) − t(d₂)) = (Σ c cos t)² + (Σ c sin t)²`. -/
theorem sum_sum_mul_cos_sub (D : Finset ℕ) (c t : ℕ → ℝ) :
    ∑ d₁ ∈ D, ∑ d₂ ∈ D, c d₁ * c d₂ * Real.cos (t d₁ - t d₂) =
      (∑ d ∈ D, c d * Real.cos (t d)) ^ 2 + (∑ d ∈ D, c d * Real.sin (t d)) ^ 2 := by
  simp_rw [Real.cos_sub, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
  ring

theorem squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hS p hp).prime.squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)

/-- **Divisor expansion.** For `P = ∏_{p ∈ S} p`,
`Σ_{d₁, d₂ ∣ P} μ(d₁)μ(d₂)(d₁d₂)^{−σ} cos(θ(log d₁ − log d₂)) = ∏_{p ∈ S} |1 − p^{−σ}e^{iθ log p}|²`. -/
theorem hypercube_cos_sum_eq_eulerProductSq (σ θ : ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d₁ ∈ (∏ p ∈ S, p).divisors, ∑ d₂ ∈ (∏ p ∈ S, p).divisors,
        (moebiusReal d₁ * (d₁ : ℝ) ^ (-σ)) * (moebiusReal d₂ * (d₂ : ℝ) ^ (-σ)) *
          Real.cos (θ * (Real.log d₁ - Real.log d₂)) = eulerProductSq σ θ S := by
  set P := ∏ p ∈ S, p
  have hsq := squarefree_prod_primes hS
  have hEuler := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree (twistedPow σ θ)
    (isMultiplicative_twistedPow σ θ) hsq
  rw [Nat.primeFactors_prod hS] at hEuler
  have hcos : ∀ d₁ d₂ : ℕ, Real.cos (θ * (Real.log d₁ - Real.log d₂)) =
      Real.cos (θ * Real.log d₁ - θ * Real.log d₂) := fun d₁ d₂ => by ring_nf
  simp_rw [hcos]
  have key := sum_sum_mul_cos_sub P.divisors (fun d => moebiusReal d * (d : ℝ) ^ (-σ))
    (fun d => θ * Real.log d)
  rw [key]
  have hre : ∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-σ) * Real.cos (θ * Real.log d) =
      (∑ d ∈ P.divisors, (μ d : ℂ) * twistedPow σ θ d).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun d hd =>
      (re_moebius_mul_twistedPow σ θ (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))).symm
  have him : ∑ d ∈ P.divisors, moebiusReal d * (d : ℝ) ^ (-σ) * Real.sin (θ * Real.log d) =
      (∑ d ∈ P.divisors, (μ d : ℂ) * twistedPow σ θ d).im := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun d hd =>
      (im_moebius_mul_twistedPow σ θ (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))).symm
  rw [hre, him, ← hEuler, sq, sq, ← Complex.normSq_apply, map_prod, eulerProductSq]
  exact Finset.prod_congr rfl fun p hp => normSq_one_sub_twistedPow σ θ (hS p hp).ne_zero

end Divisor

section Form

variable {r : ℕ} (hr : 1 < r)

theorem integrable_stepSpectralWeight_mul_cos (c : ℝ) :
    Integrable fun ξ => stepSpectralWeight hr ξ * Real.cos (2 * Real.pi * ξ * c) :=
  (integrable_stepSpectralWeight hr).mul_bdd
    (by fun_prop : Continuous fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * c)).aestronglyMeasurable
    (c := 1) (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **The hypercube form is a spectral integral of a partial Euler product.** For
`P = ∏_{p ∈ S} p` and `σ = 1/2 + ε`, `Q_ε(P) = ∫ W(ξ) ∏_{p ∈ S} |1 − p^{−σ+2πiξ}|² dξ`. -/
theorem hypercubeDilationDirichletForm_eq_integral (ε : ℝ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    hypercubeDilationDirichletForm ε (∏ p ∈ S, p) r hr =
      ∫ ξ, stepSpectralWeight hr ξ * eulerProductSq (1 / 2 + ε) (2 * Real.pi * ξ) S := by
  set P := ∏ p ∈ S, p
  set a : ℕ → ℝ := fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 + ε))
  set g : ℕ → ℕ → ℝ → ℝ := fun d₁ d₂ ξ => a d₁ * a d₂ *
    (stepSpectralWeight hr ξ * Real.cos (2 * Real.pi * ξ * (Real.log d₁ - Real.log d₂)))
  have hg : ∀ d₁ d₂, Integrable (g d₁ d₂) := fun d₁ d₂ =>
    (integrable_stepSpectralWeight_mul_cos hr _).const_mul _
  have hterm : ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
      moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
          (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
        pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) = ∫ ξ, g d₁ d₂ ξ := by
    intro d₁ hd₁ d₂ hd₂
    have h1 : (0 : ℝ) < d₁ := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
    have h2 : (0 : ℝ) < d₂ := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
    rw [dilationProfile_eq_integral hr (div_pos h1 h2), Real.log_div h1.ne' h2.ne',
      ← integral_const_mul, show (-(1 / 2 : ℝ) - ε) = -(1 / 2 + ε) by ring]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    have harg : 2 * Real.pi * ((Real.log d₁ - Real.log d₂) * ξ) =
        2 * Real.pi * ξ * (Real.log d₁ - Real.log d₂) := by ring
    simp only [g, a, harg]
  rw [hypercubeDilationDirichletForm,
    Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂]
  rw [Finset.sum_congr rfl fun d₁ _ =>
      (integral_finsetSum P.divisors fun d₂ _ => hg d₁ d₂).symm,
    ← integral_finsetSum P.divisors fun d₁ _ => integrable_finsetSum _ fun d₂ _ => hg d₁ d₂]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [← hypercube_cos_sum_eq_eulerProductSq (1 / 2 + ε) (2 * Real.pi * ξ) hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₂ _ => ?_
  simp only [g, a]
  ring

/-- The total spectral mass is the diagonal Gram: `∫ W = Φ_r(1) > 0`. -/
theorem integral_stepSpectralWeight_pos : 0 < ∫ ξ, stepSpectralWeight hr ξ := by
  have h := dilationProfile_eq_integral hr one_pos
  simp only [Real.log_one, zero_mul, mul_zero, Real.cos_zero, mul_one] at h
  rw [← h, pmRamanujanDilationProfile_one]
  exact pmRamanujanPrimitiveGram_pos hr

end Form

section Unbounded

/-- **The hypercube Dirichlet form is unbounded for `−1/2 ≤ ε < 1/2`.** For every Ramanujan modulus
`r > 1` and every bound `M` there is a squarefree `P` with `Q_ε(P) > M`. -/
theorem hypercubeDilationDirichletForm_unbounded {ε : ℝ} (hε0 : -(1 / 2) ≤ ε) (hε1 : ε < 1 / 2)
    {r : ℕ} (hr : 1 < r) (M : ℝ) :
    ∃ P : ℕ, Squarefree P ∧ M < hypercubeDilationDirichletForm ε P r hr := by
  set σ := 1 / 2 + ε
  have hσ0 : 0 ≤ σ := by simp only [σ]; linarith
  have hσ1 : σ < 1 := by simp only [σ]; linarith
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  set W := stepSpectralWeight hr
  -- rescale the spectral variable: `w(τ) = W(τ/(2π))`
  set w : ℝ → ℝ := fun τ => W ((2 * Real.pi)⁻¹ * τ)
  have hwi : Integrable w := (integrable_stepSpectralWeight hr).comp_mul_left' (by positivity)
  have hw0 : ∀ τ, 0 ≤ w τ := fun τ => stepSpectralWeight_nonneg hr _
  have hwtot : 0 < ∫ τ, w τ := by
    have := Measure.integral_comp_mul_left W (2 * Real.pi)⁻¹
    rw [inv_inv, abs_of_pos h2π, smul_eq_mul] at this
    rw [this]
    exact mul_pos h2π (integral_stepSpectralWeight_pos hr)
  have hscale : ∀ S : Finset ℕ, (∫ ξ, W ξ * eulerProductSq σ (2 * Real.pi * ξ) S) =
      (2 * Real.pi)⁻¹ * ∫ τ, w τ * eulerProductSq σ τ S := by
    intro S
    have := Measure.integral_comp_mul_left (fun τ => w τ * eulerProductSq σ τ S) (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr h2π), smul_eq_mul] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [w]
    rw [← mul_assoc, inv_mul_cancel₀ h2π.ne', one_mul]
  -- choose a side of the spectral line carrying mass
  have hsplit : (∫ τ in Ioi (0 : ℝ), w τ) + ∫ τ in Iic (0 : ℝ), w τ = ∫ τ, w τ := by
    rw [← compl_Ioi]; exact integral_add_compl measurableSet_Ioi hwi
  obtain ⟨S, hSp, hS⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      2 * Real.pi * (|M| + 1) ≤ ∫ τ, w τ * eulerProductSq σ τ S := by
    by_cases hpos : 0 < ∫ τ in Ioi (0 : ℝ), w τ
    · exact spectralHypercube_unbounded_of_integrable hσ0 hσ1 hwi hw0 hpos _
    · have hneg : 0 < ∫ τ in Ioi (0 : ℝ), w (-τ) := by
        rw [integral_comp_neg_Ioi, neg_zero]; linarith
      have hwi' : Integrable fun τ => w (-τ) := by
        simpa [neg_one_mul] using hwi.comp_mul_left' (show (-1 : ℝ) ≠ 0 by norm_num)
      obtain ⟨S, hSp, hS⟩ := spectralHypercube_unbounded_of_integrable hσ0 hσ1
        hwi' (fun τ => hw0 _) hneg (2 * Real.pi * (|M| + 1))
      refine ⟨S, hSp, hS.trans_eq ?_⟩
      have := Measure.integral_comp_mul_left (fun τ => w τ * eulerProductSq σ τ S) (-1)
      simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at this
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [eulerProductSq, eulerFactorSq_neg]
  refine ⟨∏ p ∈ S, p, squarefree_prod_primes hSp, ?_⟩
  rw [hypercubeDilationDirichletForm_eq_integral hr ε hSp, hscale S]
  have : (2 * Real.pi)⁻¹ * (2 * Real.pi * (|M| + 1)) = |M| + 1 := by field_simp
  have hmono := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr h2π.le)
  linarith [le_abs_self M]

end Unbounded

end GaloisForLFunctions.SignedSuccessorArithmetic
