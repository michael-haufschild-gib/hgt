import GaloisForLFunctions.BiScaleUncertainty.PacketEnergyPlancherel
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLift
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHarmonicCorrection

/-!
# The rectangle law and the divisor-averaged Chebyshev error

The exponential rectangle `e^{t/2} 1_{[0,a]}` (`polarRectangle a`) is the simplest producer test of
the field: its pairing with the signed prime–polar measure reads the raw Chebyshev error at the right
endpoint,

`pairing N (polarRectangle a) = (ψ(e^a) − e^a) + 1 − a`,  `0 ≤ a ≤ L`,

and a rectangle difference reads the block response of the renewal chain,

`pairing N (polarRectangle b − polarRectangle a) = e^{b/2} · blockResponse a b`.

The factorial lift `Σ_{j ≤ K} polarRectangle (log(K/j))` therefore pairs to the divisor average of the
Chebyshev error, and the hyperbola identity `Σ_{d ≤ K} ψ(⌊K/d⌋) = log K!` gives the exact law

`Σ_{j ≤ K} (ψ(K/j) − K/j) = log K! − K H_K`,  equivalently  `Σ_{j ≤ K} √(K/j) Ẽ(log(K/j)) = log K! − K H_K`.

This identifies the producer tests of the parallel factorial programme with explicit linear
functionals of the Chebyshev error in the receiver language of the hyperbolic gauge: every factorial
producer is a signed sum of rectangle readings `Ẽ(log(K/j))`, and its `O(log K/√K)` cancellation is
the Dirichlet-convolution identity `Λ ∗ 1 = log` seen through the signed prime–polar measure.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## Linearity of the pairing -/

theorem pairing_finsetSum {ι : Type*} (N : ℕ) (s : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ j ∈ s, IntegrableOn (fun x => polarDensity x * g j x) (Icc 0 (cutoff N))) :
    pairing N (fun t => ∑ j ∈ s, g j t) = ∑ j ∈ s, pairing N (g j) := by
  unfold pairing
  rw [Finset.sum_sub_distrib, ← integral_finsetSum s hg]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show polarDensity x * (∑ j ∈ s, g j x) = ∑ j ∈ s, polarDensity x * g j x
    rw [Finset.mul_sum]

theorem pairing_sub (N : ℕ) {g g' : ℝ → ℝ}
    (hg : IntegrableOn (fun x => polarDensity x * g x) (Icc 0 (cutoff N)))
    (hg' : IntegrableOn (fun x => polarDensity x * g' x) (Icc 0 (cutoff N))) :
    pairing N (fun t => g t - g' t) = pairing N g - pairing N g' := by
  unfold pairing
  show (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * (g (Real.log n) - g' (Real.log n))) -
    (∫ x in Icc 0 (cutoff N), polarDensity x * (g x - g' x)) = _
  have hi : (∫ x in Icc 0 (cutoff N), polarDensity x * (g x - g' x)) =
      (∫ x in Icc 0 (cutoff N), polarDensity x * g x) -
        ∫ x in Icc 0 (cutoff N), polarDensity x * g' x := by
    rw [← integral_sub hg hg']
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hs : (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * (g (Real.log n) - g' (Real.log n))) =
      ∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n * g (Real.log n) - primeWeight n * g' (Real.log n)) :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hs, Finset.sum_sub_distrib, hi]
  ring

/-! ## The rectangle law -/

theorem polarRectangle_eq_zero_of_lt {a x : ℝ} (hx : a < x) : polarRectangle a x = 0 :=
  Set.indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hx)) _

/-- **The rectangle law:** `pairing N (e^{t/2} 1_{[0,a]}) = (ψ(e^a) − e^a) + 1 − a`. -/
theorem pairing_polarRectangle (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ cutoff N) :
    pairing N (polarRectangle a) = logError a + 1 - a := by
  have hatom : (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * polarRectangle a (Real.log n)) =
      Chebyshev.psi (Real.exp a) := by
    rw [← step_eq N haL]
    unfold step
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hsq : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
    unfold polarRectangle primeWeight
    by_cases h : Real.log (n : ℝ) ≤ a
    · rw [Set.indicator_of_mem (show Real.log (n : ℝ) ∈ Icc 0 a from ⟨hlog0, h⟩), if_pos h,
        exp_half_log_eq_sqrt hn0]
      exact div_mul_cancel₀ _ hsq
    · rw [Set.indicator_of_notMem (fun hm => h hm.2), if_neg h, mul_zero]
  have hpolar : (∫ x in Icc 0 (cutoff N), polarDensity x * polarRectangle a x) =
      Real.exp a - 1 + a := by
    rw [← integral_polar_rectangle ha]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
      fun x hx => ?_).symm
    have hxL : cutoff N < x := by
      rcases hx with ⟨hx1, hx2⟩
      simp only [mem_Icc, not_and, not_le] at hx2
      exact hx2 hx1
    rw [polarRectangle_eq_zero_of_lt (lt_of_le_of_lt haL hxL), mul_zero]
  unfold pairing
  rw [hatom, hpolar]
  unfold logError
  ring

theorem integrableOn_polar_polarRectangle (N : ℕ) (a : ℝ) :
    IntegrableOn (fun x => polarDensity x * polarRectangle a x) (Icc 0 (cutoff N)) :=
  (integrable_polar_rectangle a).integrableOn

/-- **Rectangle differences read block responses:**
`pairing N (polarRectangle b − polarRectangle a) = e^{b/2} · blockResponse a b`. -/
theorem pairing_polarRectangle_sub (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbL : b ≤ cutoff N) :
    pairing N (fun t => polarRectangle b t - polarRectangle a t) =
      Real.exp (b / 2) * blockResponse a b := by
  rw [pairing_sub N (integrableOn_polar_polarRectangle N b) (integrableOn_polar_polarRectangle N a),
    pairing_polarRectangle N (ha.trans hab) hbL, pairing_polarRectangle N ha (hab.trans hbL)]
  unfold blockResponse logError
  have h : Real.exp (b / 2) * Real.exp (-b / 2) = 1 := by
    rw [← Real.exp_add, show b / 2 + -b / 2 = 0 by ring, Real.exp_zero]
  linear_combination (-((Chebyshev.psi (Real.exp b) - Chebyshev.psi (Real.exp a)) -
    (Real.exp b - Real.exp a) - (b - a))) * h

/-- The chain input of the renewal ladder is a normalized rectangle-difference reading. -/
theorem chainInput_eq_pairing_polarRectangle_sub (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {k : ℕ}
    (hk : (k + 1) * h ≤ cutoff N) :
    chainInput h k = Real.exp (-((k + 1) * h) / 2) *
      pairing N (fun t => polarRectangle ((k + 1) * h) t - polarRectangle (k * h) t) := by
  have hkh : 0 ≤ (k : ℝ) * h := by positivity
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  rw [pairing_polarRectangle_sub N hkh hle hk]
  unfold chainInput
  have : Real.exp (-((k + 1 : ℝ) * h) / 2) * Real.exp (((k : ℝ) + 1) * h / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  linear_combination (-(blockResponse (↑k * h) ((↑k + 1) * h))) * this

/-! ## The factorial lift as a divisor average of the Chebyshev error -/

theorem log_ratio_nonneg {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
    0 ≤ Real.log ((K : ℝ) / (j : ℝ)) := by
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  exact Real.log_nonneg ((le_div_iff₀ hj0).2 (by simpa using (show (j : ℝ) ≤ K by exact_mod_cast hjK)))

theorem log_ratio_le_log {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
    Real.log ((K : ℝ) / (j : ℝ)) ≤ Real.log (K : ℝ) := by
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 1 ≤ K by omega)
  exact Real.log_le_log (div_pos hK0 hj0) (div_le_self hK0.le (by exact_mod_cast hj1))

/-- **The factorial lift pairs to the divisor-averaged Chebyshev error.** -/
theorem pairing_factorialLift (N K : ℕ) (hK : Real.log (K : ℝ) ≤ cutoff N) :
    pairing N (factorialLift K) =
      ∑ j ∈ Finset.Icc 1 K,
        (logError (Real.log ((K : ℝ) / j)) + 1 - Real.log ((K : ℝ) / j)) := by
  unfold factorialLift
  rw [pairing_finsetSum N _ _ fun j _ => integrableOn_polar_polarRectangle N _]
  exact Finset.sum_congr rfl fun j hj =>
    pairing_polarRectangle N (log_ratio_nonneg hj) ((log_ratio_le_log hj).trans hK)

theorem chebyshev_psi_div_eq (K j : ℕ) :
    Chebyshev.psi ((K : ℝ) / (j : ℝ)) = RHTower.chebyshevPsi (K / j) := by
  rw [RHTower.chebyshevPsi_eq_psi]
  unfold Chebyshev.psi
  rw [Nat.floor_div_eq_div, Nat.floor_natCast]

theorem logError_log_ratio_eq {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
    logError (Real.log ((K : ℝ) / j)) = RHTower.chebyshevPsi (K / j) - (K : ℝ) / j := by
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 1 ≤ K by omega)
  unfold logError
  rw [Real.exp_log (div_pos hK0 hj0), chebyshev_psi_div_eq]

/-- **The divisor-averaged Chebyshev error law:** `Σ_{j≤K} (ψ(K/j) − K/j) = log K! − K H_K`. -/
theorem sum_logError_log_ratio_eq (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, logError (Real.log ((K : ℝ) / j))) =
      RHTower.floorSummatory RHTower.chebyshevPsi K - K * realHarmonic K := by
  rw [Finset.sum_congr rfl fun j hj => logError_log_ratio_eq hj, Finset.sum_sub_distrib]
  unfold RHTower.floorSummatory realHarmonic
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The same law for the normalized error: `Σ_{j≤K} √(K/j) Ẽ(log(K/j)) = log K! − K H_K`. -/
theorem sum_sqrt_mul_normalizedLogError_eq (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, Real.sqrt ((K : ℝ) / j) * normalizedLogError (Real.log ((K : ℝ) / j))) =
      RHTower.floorSummatory RHTower.chebyshevPsi K - K * realHarmonic K := by
  rw [← sum_logError_log_ratio_eq]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 1 ≤ K by omega)
  have hr : (0 : ℝ) < (K : ℝ) / j := div_pos hK0 hj0
  unfold normalizedLogError
  rw [← exp_half_log_eq_sqrt hr, ← mul_assoc, ← Real.exp_add]
  have : Real.log ((K : ℝ) / j) / 2 + -Real.log ((K : ℝ) / j) / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_mul]

/-- The factorial-lift pairing in closed form: `2 log K! − K log K − K H_K + K`. -/
theorem pairing_factorialLift_eq (N K : ℕ) (hK1 : 1 ≤ K) (hK : Real.log (K : ℝ) ≤ cutoff N) :
    pairing N (factorialLift K) =
      2 * RHTower.floorSummatory RHTower.chebyshevPsi K - K * Real.log K - K * realHarmonic K + K := by
  rw [pairing_factorialLift N K hK]
  have hsplit : (∑ j ∈ Finset.Icc 1 K,
      (logError (Real.log ((K : ℝ) / j)) + 1 - Real.log ((K : ℝ) / j))) =
      (∑ j ∈ Finset.Icc 1 K, logError (Real.log ((K : ℝ) / j))) + K -
        ∑ j ∈ Finset.Icc 1 K, Real.log ((K : ℝ) / j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hlog : (∑ j ∈ Finset.Icc 1 K, Real.log ((K : ℝ) / j)) =
      K * Real.log K - RHTower.floorSummatory RHTower.chebyshevPsi K := by
    rw [RHTower.floorSummatory_chebyshevPsi]
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have : ∀ j ∈ Finset.Icc 1 K, Real.log ((K : ℝ) / j) = Real.log K - Real.log j := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      exact Real.log_div hK0.ne' hj0.ne'
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
  rw [hsplit, sum_logError_log_ratio_eq, hlog]
  ring

/-- Consistency with the half-line pairing of the factorial programme: for `K < N + 2` the window
pairing equals the literal full pairing. -/
theorem pairing_factorialLift_eq_fullPairing (N K : ℕ) (hK : K < N + 2) :
    pairing N (factorialLift K) = fullPairing (factorialLift K) := by
  symm
  refine fullPairing_eq_pairing_of_tail (factorialLift K) N fun x hx => ?_
  refine factorialLift_eq_zero_of_log_lt K (lt_of_lt_of_le ?_ hx)
  unfold cutoff
  by_cases hK0 : K = 0
  · subst hK0
    simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_pos (by exact_mod_cast (show 1 < N + 2 by omega))
  · exact Real.log_lt_log (by exact_mod_cast Nat.pos_of_ne_zero hK0) (by exact_mod_cast hK)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
