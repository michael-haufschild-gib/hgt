import GaloisForLFunctions.PrimeTorusTheory.TheLogarithmOfAFibre
import GaloisForLFunctions.RHTower.SteinhausPrimeHolomorphic

/-!
# The hull over order-two points

The points of order two of the torus are the completely multiplicative `±1` functions. Two of them are named: the trivial point, whose fibre is `ζ`, and the Liouville point, whose fibre `ζ(2s)/ζ(s)` extends holomorphically to `Re s > ½` if and only if RH holds (`riemannHypothesis_iff_liouvilleFibre_extends`). Here is the typical one.

Put a fair coin on every prime: the phase of `p` is `0` or `½` with probability `½` each (`coin`, `signMeasure`), so the Steinhaus character `X_p = e^{2πi ω_p}` is `±1` (`ae_X_prime_sign`).

**Theorem** (`ae_signFibre_extends_zeroFree`). For almost every order-two point, the fibre `Σ_n X_n n^{−s}` extends to a zero-free analytic function on `Re s > ½`.

**Mechanism.** The prime sum `Σ_p X_p p^{−σ}` is a centred, bounded series of independent terms with variance `Σ_p p^{−2σ}`, so by Kolmogorov it converges almost surely at every `σ > ½` (`measure_coordSeriesConverges_sign`). Convergence at a point propagates holomorphically to the right, as in the Steinhaus model. The logarithm of the fibre is that sum plus the remainder `h`, which is analytic on `Re s > ½` (`TheLogarithmOfAFibre`). So the fibre is `exp` of an analytic function.

Among the order-two points the Liouville point is the one where every coin shows `½`. A typical order-two point extends zero-free to `Re s > ½`, and RH says that the Liouville point extends there too.
-/

open MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry
open _root_.RHTower.SteinhausModel

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

open GaloisForLFunctions.RHTower

/-- A fair coin on the phases `0` and `½`. -/
def coin : Measure ℝ := (2 : ENNReal)⁻¹ • (Measure.dirac 0 + Measure.dirac (1 / 2))

instance : IsProbabilityMeasure coin := by
  constructor
  rw [coin, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- Independent fair coins on all coordinates: the Haar measure of the order-two points. -/
def signMeasure : Measure Omega := Measure.infinitePi fun _ => coin

instance : IsProbabilityMeasure signMeasure := by
  unfold signMeasure
  infer_instance

theorem integral_coin {f : ℝ → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂coin = (f 0 + f (1 / 2)) / 2 := by
  have hi : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  rw [coin, integral_smul_measure, integral_add_measure (hi 0) (hi _), integral_dirac, integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  ring

/-- The prime terms are centred under the coin. -/
theorem integral_primeTerm_coin (σ : ℝ) (n : ℕ) : ∫ y, primeTerm σ n y ∂coin = 0 := by
  rw [integral_coin (measurable_primeTerm σ n) (norm_primeTerm_le σ n)]
  unfold primeTerm
  split_ifs
  · have h : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℝ) : ℂ)) = -1 := by
      rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℝ) : ℂ) = Real.pi * Complex.I by
        push_cast; ring]
      exact Complex.exp_pi_mul_I
    rw [h]
    simp
  · simp

/-- **Kolmogorov for coins.** The prime sum `Σ_p X_p p^{−σ}` converges almost surely for `σ > ½`. -/
theorem measure_coordSeriesConverges_sign {σ : ℝ} (hσ : 1 / 2 < σ) :
    signMeasure (coordSeriesConverges (primeTerm σ)) = 1 := by
  have hsq : ∀ n, ∫ y, ‖primeTerm σ n y‖ ^ 2 ∂coin = primeTermBound σ n ^ 2 := fun n => by
    simp only [norm_primeTerm_eq]
    simp
  have hsum : Summable fun n => ∫ y, ‖primeTerm σ n y‖ ^ 2 ∂coin := by
    simp only [hsq]
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (Real.summable_nat_rpow.mpr (by linarith : -(2 * σ) < -1))
    rw [primeTermBound]
    split_ifs
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
      rw [show σ * 2 = 2 * σ by ring]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact measure_coordSeriesConverges_eq_one (primeTerm σ) (fun _ : ℕ => coin) (c := primeTermBound σ)
    (measurable_primeTerm σ) (norm_primeTerm_le σ) (primeTermBound_nonneg σ)
    (integral_primeTerm_coin σ) hsum (fun _ => 0)

/-- The prime series converges at every rational cut past the half line, almost surely. -/
theorem ae_mem_primeHolomorphicEvent : ∀ᵐ ω ∂signMeasure, ω ∈ primeHolomorphicEvent := by
  have hae : ∀ᵐ ω ∂signMeasure, ∀ j : ℕ,
      ω ∈ coordSeriesConverges (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1))) := by
    rw [ae_all_iff]
    intro j
    have hmeas := measurableSet_coordSeriesConverges
      (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1))) (measurable_primeTerm _)
    have hone := measure_coordSeriesConverges_sign (σ := 1 / 2 + 1 / ((j : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith)
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hmeas).mpr hone
  filter_upwards [hae] with ω hω
  exact Set.mem_iInter.mpr hω

/-- Almost surely every phase is `0` or `½`. -/
theorem ae_coord_sign : ∀ᵐ ω ∂signMeasure, ∀ n, ω n = 0 ∨ ω n = 1 / 2 := by
  rw [ae_all_iff]
  intro n
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => coin) n
  have hS : MeasurableSet (({0, 1 / 2} : Set ℝ)ᶜ) :=
    ((measurableSet_singleton _).insert _).compl
  rw [ae_iff]
  have e : {ω : Omega | ¬(ω n = 0 ∨ ω n = 1 / 2)} = (fun ω : Omega => ω n) ⁻¹' ({0, 1 / 2} : Set ℝ)ᶜ := by
    ext ω
    simp
  rw [e]
  have h := hmp.measure_preimage hS.nullMeasurableSet
  unfold signMeasure
  rw [h, coin, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hS, Measure.dirac_apply' _ hS]
  simp

/-- Almost surely the point has order two: `X_p = ±1` at every prime. -/
theorem ae_X_prime_sign : ∀ᵐ ω ∂signMeasure, ∀ p, p.Prime → X p ω = 1 ∨ X p ω = -1 := by
  filter_upwards [ae_coord_sign] with ω hω p hp
  rw [X_prime_eq hp]
  rcases hω p with h | h
  · left
    rw [h]
    simp
  · right
    rw [h, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℝ) : ℂ) = Real.pi * Complex.I by
      push_cast; ring]
    exact Complex.exp_pi_mul_I

/-- The point `X(ω)` as a completely multiplicative function. -/
def signHom (ω : Omega) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else X n ω
  map_zero' := by simp
  map_one' := by simp [X_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp [hm, hn, X_mul hm hn]

theorem signHom_apply (ω : Omega) (n : ℕ) : signHom ω n = if n = 0 then 0 else X n ω := rfl

theorem norm_signHom_le (ω : Omega) (n : ℕ) : ‖signHom ω n‖ ≤ 1 := by
  rw [signHom_apply]
  split_ifs
  · simp
  · exact (norm_X n ω).le

theorem norm_signHom_prime (ω : Omega) : ∀ p, p.Prime → ‖signHom ω p‖ = 1 := fun p hp => by
  rw [signHom_apply, if_neg hp.ne_zero, norm_X]

/-- **The hull over a typical order-two point.** For almost every order-two point the fibre extends to a zero-free analytic function on `Re s > ½`. -/
theorem ae_signFibre_extends_zeroFree :
    ∀ᵐ ω ∂signMeasure, (∀ p, p.Prime → X p ω = 1 ∨ X p ω = -1) ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F rightHalf ∧
        (∀ s, 1 < s.re → F s = ∑' n, signHom ω n * (n : ℂ) ^ (-s)) ∧ ∀ s ∈ rightHalf, F s ≠ 0 := by
  filter_upwards [ae_X_prime_sign, ae_mem_primeHolomorphicEvent] with ω hsign hω
  refine ⟨hsign, ?_⟩
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hP : AnalyticOnNhd ℂ (dirichletSum (primePhaseCoeff ω)) rightHalf :=
    (differentiableOn_dirichletSum_primePhaseCoeff hω).analyticOnNhd hU
  set W : ℂ → ℂ := fun s => dirichletSum (primePhaseCoeff ω) s + hullRem s (signHom ω) with hW
  have hWa : AnalyticOnNhd ℂ W rightHalf := hP.add (analyticOnNhd_hullRem (norm_signHom_prime ω))
  refine ⟨fun s => Complex.exp (W s), fun s hs => (hWa s hs).cexp, fun s hs => ?_,
    fun s _ => Complex.exp_ne_zero _⟩
  have h1 : dirichletSum (primePhaseCoeff ω) s = ∑' p : Nat.Primes, eulerVar s (signHom ω) p := by
    rw [← (hasSum_primePhase_dirichletSum (ω := ω) hs).tsum_eq]
    refine tsum_congr fun p => ?_
    unfold eulerVar powCoeff
    rw [signHom_apply, if_neg p.2.ne_zero, mul_comm]
  simp only [hW]
  rw [h1]
  exact exp_tsum_eq_tsum (norm_signHom_le ω) (norm_signHom_prime ω) hs

end

end GaloisForLFunctions.PrimeTorusTheory
