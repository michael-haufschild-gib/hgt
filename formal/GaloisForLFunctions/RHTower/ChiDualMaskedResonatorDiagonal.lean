import GaloisForLFunctions.RHTower.PrimeWindowResonatorDiagonal
import GaloisForLFunctions.RHTower.ChiDualMaskedMeanSquare

/-!
# Actual Gaussian masked coefficients under a resonator

The literal physical dual carrier has an exact coefficient factorization. Its
product with any finite resonator retains every multiplicative collision in the
complex convolution. Source compact amplitude and reflected-row bounds cancel
the height factor in the prime-masked GCD/max diagonal estimate, uniformly at
every height in the full physical window. No physical off-diagonal cancellation
or positive self-target certificate is inferred from this coefficient estimate.
-/

open Complex Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Literal height-frozen coefficient of the actual masked spatial dual carrier. -/
def chiDualMaskedPhysicalCoefficient (s : ℂ) (N t : ℝ) (n : ℕ) : ℂ :=
  smoothAFECutoff ((n : ℝ) / N) * (zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1))

/-- Exact source amplitude normalization, including the common chi factor. -/
theorem chiDualMaskedPhysicalCoefficient_eq {N : ℝ} (hN : 0 < N)
    {n : ℕ} (hn : 0 < n) (s : ℂ) (t : ℝ) :
    chiDualMaskedPhysicalCoefficient s N t n =
      (zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)) *
        chiDualUnitSpatialAmplitude s ((n : ℝ) / N) := by
  have he := chiDualSpatialSlowAmplitude_eq s (x := (n : ℝ)) hN (by exact_mod_cast hn)
  simp only [chiDualSpatialSlowAmplitude, Complex.ofReal_natCast] at he
  unfold chiDualMaskedPhysicalCoefficient
  calc
    _ = zetaChi (s + (t : ℂ) * I) *
        (smoothAFECutoff ((n : ℝ) / N) * (n : ℂ) ^ (s - 1)) := by ring
    _ = _ := by rw [← he]; ring

/-- Exact physical carrier reconstruction from its coefficients. -/
theorem chiDualMaskedBlock_eq_physical_coefficients (s : ℂ) (N t : ℝ) (S : Finset ℕ) :
    (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) =
      zetaChiDualResonator S (chiDualMaskedPhysicalCoefficient s N t) t := by
  unfold zetaChiDualResonator
  apply Finset.sum_congr rfl
  intro n _
  unfold zetaChiDualInteriorAtom chiDualMaskedPhysicalCoefficient
  ring

/-- Multiplying the literal physical masked block by its resonator retains the
entire multiplicative convolution, including every repeated product frequency. -/
theorem chiDualMaskedBlock_mul_resonator_eq_conv (s : ℂ) (N t : ℝ)
    (S A : Finset ℕ) (d : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hA : ∀ a ∈ A, 0 < a) :
    zetaChiDualResonator A d t *
        (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) =
      zetaChiDualResonator (prodSupport A S)
        (dpolyComplexConv d (chiDualMaskedPhysicalCoefficient s N t) A S) t := by
  classical
  rw [chiDualMaskedBlock_eq_physical_coefficients]
  unfold zetaChiDualResonator
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ q ∈ A ×ˢ S, q.1 * q.2 ∈ prodSupport A S := fun q hq =>
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun q => (d q.1 * bourgainOscillation (t * Real.log q.1)) *
      (chiDualMaskedPhysicalCoefficient s N t q.2 * bourgainOscillation (t * Real.log q.2)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [dpolyComplexConv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqAS, hprod⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqa, hqn⟩ := Finset.mem_product.mp hqAS
  have hlog : Real.log ((q.1 * q.2 : ℕ) : ℝ) = Real.log q.1 + Real.log q.2 := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (hA q.1 hqa).ne')
      (by exact_mod_cast (hS q.2 hqn).ne')]
  have hphase : bourgainOscillation (t * Real.log q.1) *
      bourgainOscillation (t * Real.log q.2) = bourgainOscillation (t * Real.log k) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add, ← hprod, hlog]
    congr 1
    push_cast
    ring
  calc
    _ = (d q.1 * chiDualMaskedPhysicalCoefficient s N t q.2) *
        (bourgainOscillation (t * Real.log q.1) * bourgainOscillation (t * Real.log q.2)) := by ring
    _ = _ := by rw [hphase]

/-- Every actual chi-weighted masked spatial coefficient family obeys the complete
resonator-convolution GCD/max bound, uniformly on the compact disc and physical height window.
This controls the full coefficient diagonal; physical off-diagonal integrals remain separate. -/
theorem exists_chiDual_prime_mask_resonator_diagonal_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ t ∈ Icc (N : ℝ) (2 * N), ∀ S : Finset ℕ,
      (∀ n ∈ S, (N : ℝ) / 5 ≤ n ∧ (n : ℝ) ≤ 6 * N / 25) →
      ∀ H : ℕ, 1 ≤ H → H ^ 2 ≤ N → ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a ∧ a ≤ N / H) → ∀ d : ℕ → ℂ,
      (∑ k ∈ prodSupport A (primeWindowSupported S N H),
        ‖dpolyComplexConv d (chiDualMaskedPhysicalCoefficient s N t) A
          (primeWindowSupported S N H) k‖ ^ 2) * Real.log N ≤
        C * (1 + Real.log H) * ∑ a ∈ A, ∑ b ∈ A, ‖d a‖ * ‖d b‖ *
          ((Nat.gcd a b : ℝ) / (max a b : ℕ)) := by
  obtain ⟨C₀, hC₀, hunit⟩ := exists_chiDualUnitSpatialJets_bound c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨2 * C₀ ^ 2 * C₁ ^ 2 * Real.log 4, by positivity, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (1 : ℕ)] with N hrow hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  intro s hs t ht S hS H hH hHN A hA d
  have hn (n : ℕ) (hn : n ∈ S) : 0 < n ∧ n ≤ N := by
    have hb := hS n hn
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hN0 (by norm_num)) hb.1
    have hu : (n : ℝ) ≤ N := by linarith only [hb.2, hN0]
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hu⟩
  have hratio (n : ℕ) (hn : n ∈ S) : (n : ℝ) / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    have hb := hS n hn
    constructor
    · apply (le_div_iff₀ hN0).mpr
      linarith only [hb.1, hN0]
    · apply (div_le_iff₀ hN0).mpr
      linarith only [hb.2, hN0]
  let f : ℂ := zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)
  have hfac : ‖f‖ ^ 2 * N ≤ C₁ ^ 2 := by
    have hi : ‖f‖ * Real.sqrt N = ‖reflectedCompactGaussianRow s N t‖ := by
      dsimp only [f]
      have hpow : ‖(N : ℂ) ^ (s - 1)‖ = (N : ℝ) ^ (s.re - 1) := by
        simpa only [Complex.ofReal_natCast, Complex.sub_re, Complex.one_re] using
          Complex.norm_cpow_eq_rpow_re_of_pos hN0 (s - 1)
      rw [norm_mul, hpow, norm_reflectedCompactGaussianRow s hN0 t]
      have hp : (N : ℝ) ^ (s.re - 1) * Real.sqrt N = (N : ℝ) ^ (s.re - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
        congr 1
        ring
      calc
        _ = ‖zetaChi (s + (t : ℂ) * I)‖ * ((N : ℝ) ^ (s.re - 1) * Real.sqrt N) := by ring
        _ = _ := by rw [hp]
    have hsq := congrArg (fun x : ℝ => x ^ 2) hi
    rw [mul_pow, Real.sq_sqrt hN0.le] at hsq
    rw [hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hrow t ht s hs).1 2
  have hv (n : ℕ) (hm : n ∈ primeWindowSupported S N H) :
      ‖chiDualMaskedPhysicalCoefficient s N t n‖ ≤ ‖f‖ * C₀ := by
    have hnS := (Finset.mem_filter.mp hm).1
    rw [chiDualMaskedPhysicalCoefficient_eq hN0 (hn n hnS).1, norm_mul]
    exact mul_le_mul_of_nonneg_left (hunit s hs _ (hratio n hnS)).1 (norm_nonneg _)
  have he := sum_normSq_primeWindow_conv_mul_log_le hH hHN hn hA d
    (chiDualMaskedPhysicalCoefficient s N t) (by positivity : 0 ≤ ‖f‖ * C₀) hv
  apply he.trans
  have hlogH : 0 ≤ 1 + Real.log H := by
    have := Real.log_nonneg (by exact_mod_cast hH : (1 : ℝ) ≤ H)
    linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    _ = (2 * C₀ ^ 2 * Real.log 4 * (1 + Real.log H)) * (‖f‖ ^ 2 * N) := by ring
    _ ≤ (2 * C₀ ^ 2 * Real.log 4 * (1 + Real.log H)) * C₁ ^ 2 :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = _ := by ring

end RHTower
