import GaloisForLFunctions.ArithmeticCouplingTheory.TheShellDegreeHasAnExplicitRowBound
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionRetainsThePrimeDefect
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds

/-!
# Ordinary and harmonic moments in the complete form

Harmonic neutrality cancels the two-pole terms exactly. The center collar
retains an ordinary second moment, while the far replacement error costs
the harmonic second moment. The non-ratio form is bounded by its shell
degree, retaining the affine energy and its diagonal together.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  SelectiveMultiscaleArithmeticPositivity SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics ArithmeticLorentzianGeometry HTGeometry

/-- The packet norm is its literal harmonic second moment. -/
theorem packetVector_norm_sq (F : ℕ → ℝ) (N : ℕ) :
    ‖packetVector F N‖ ^ 2 = ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) := by
  rw [horizonProfileVector_norm_sq]
  exact sum_congr rfl fun n hn => atomAmplitude_sq (mem_Icc.mp hn).1 F

private theorem packet_extension {N n : ℕ} (hn : n ∈ Icc 1 N) (F : ℕ → ℝ) :
    primeHorizonExtension (packetVector F N) n = F n / Real.sqrt n := by
  simp only [primeHorizonExtension, hn, if_true]
  rfl

/-- The Euclidean pole coordinate is the harmonic mean of packet amplitudes. -/
theorem packetVector_harmonicSum (N : ℕ) (F : ℕ → ℝ) :
    harmonicSum N (primeHorizonExtension (packetVector F N)) =
      ∑ n ∈ Icc 1 N, F n / (n : ℝ) := by
  apply sum_congr rfl
  intro n hn
  rw [packet_extension hn, div_div, Real.mul_self_sqrt (Nat.cast_nonneg n)]

/-- Every pole replacement error vanishes exactly on a harmonic-neutral packet. -/
theorem poleError_packet_eq_zero (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F : ℕ → ℝ)
    (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) :
    ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (packetVector F N),
      packetVector F N⟫ = 0 := by
  change ⟪Matrix.toEuclideanLin (horizonKernelMatrix
    (fun n j => atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j) N)
      (packetVector F N), packetVector F N⟫ = 0
  rw [horizonKernelMatrix_inner]
  have hfactor :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension (packetVector F N) n *
          primeHorizonExtension (packetVector F N) j *
            (atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j)) =
      atomPoleErrorCoefficient φ c N *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension (packetVector F N) n *
            primeHorizonExtension (packetVector F N) j * arithmeticPoleKernel n j := by
    simp only [mul_sum]
    exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring
  rw [hfactor, arithmeticPoleKernel_quadratic_eq, packetVector_harmonicSum, hF]
  ring

private theorem abs_collar_packet_le (N : ℕ) (F : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      (F n / Real.sqrt n) * (F j / Real.sqrt j) * archimedeanCenterKernel n j| ≤
      ((harmonic N : ℝ) + 1) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        |(F n / Real.sqrt n) * (F j / Real.sqrt j) * archimedeanCenterKernel n j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
    _ = ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        |F n / Real.sqrt n| * |F j / Real.sqrt j| * archimedeanCenterKernel n j := by
      simp only [abs_mul, abs_of_nonneg (archimedeanCenterKernel_nonneg _ _)]
    _ ≤ ∑ n ∈ Icc 1 N,
        (n : ℝ) * ((harmonic N : ℝ) + 1) * |F n / Real.sqrt n| ^ 2 :=
      collar_quadratic_le_harmonic_diagonal N _
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
      rw [sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp [hn0]

/-- The center correction on neutral packets keeps the terminal ordinary moment. -/
theorem abs_center_packet_le {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 ≤ c)
    (N : ℕ) (F : ℕ → ℝ) (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (packetVector F N), packetVector F N⟫| ≤
      (c * ((harmonic N : ℝ) + 1) / N) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
  have hneutral : harmonicSum N (primeHorizonExtension (packetVector F N)) = 0 := by
    rw [packetVector_harmonicSum, hF]
  have hquad :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension (packetVector F N) n *
          primeHorizonExtension (packetVector F N) j * archimedeanCenterKernel n j) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        (F n / Real.sqrt n) * (F j / Real.sqrt j) * archimedeanCenterKernel n j :=
    sum_congr rfl fun n hn => sum_congr rfl fun j hj => by
      rw [packet_extension hn, packet_extension hj]
  rw [fullWeilCenterMatrix_inner_of_harmonicSum_zero _ _ hneutral, hquad,
    abs_mul, abs_neg, abs_of_nonneg (completeWeilPoleShift_nonneg φ hc),
    abs_div, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    _ ≤ c * ((((harmonic N : ℝ) + 1) * ∑ n ∈ Icc 1 N, F n ^ 2) / N) :=
      mul_le_mul (completeWeilPoleShift_le hφ hsupp hM hc)
        (div_le_div_of_nonneg_right (abs_collar_packet_le N F) (Nat.cast_nonneg N))
        (div_nonneg (abs_nonneg _) (Nat.cast_nonneg N)) hc
    _ = _ := by ring

/-- The separated replacement error is paid by the harmonic second moment. -/
theorem abs_separatedCross_packet_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (F : ℕ → ℝ) :
    |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N),
      packetVector F N⟫| ≤
      4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * c ^ 2 *
        ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) := by
  have h := norm_separatedCrossErrorMatrix_le hφ hsupp hM hc hN (packetVector F N)
  calc
    _ ≤ ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N)‖ *
        ‖packetVector F N‖ := abs_real_inner_le_norm _ _
    _ ≤ (4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * c ^ 2 * ‖packetVector F N‖) *
        ‖packetVector F N‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = (4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * c ^ 2) *
        ‖packetVector F N‖ ^ 2 := by ring
    _ = _ := by rw [packetVector_norm_sq]

/-- The affine energy and shell diagonal together cost at most the shell diagonal. -/
theorem abs_half_affine_sub_shell_le {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (N : ℕ) (F : ℕ → ℝ) :
    |(1 / 2) * affineDirichlet φ c N F -
      ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2| ≤
        ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2 := by
  have hidentity := sum_sum_mul_eq_degree_sub_dirichlet
    (univ : Finset (PrimeHorizonIndex N)) (nonRatioWeight φ c N)
      (nonRatioWeight_symm φ c N) (fun n => F n)
  change (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
    nonRatioWeight φ c N n j * F n * F j) =
      (∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2) -
        (1 / 2) * affineDirichlet φ c N F at hidentity
  rw [abs_sub_comm, ← hidentity]
  have hschur := finite_weighted_schur_row_potential
    (univ : Finset (PrimeHorizonIndex N)) (fun n => |F n|) (fun _ => 1)
      (nonRatioWeight φ c N) (fun _ _ => zero_lt_one)
      (fun n _ j _ => nonRatioWeight_nonneg hφ0 hsupp hM hc n j)
      (fun n _ j _ => nonRatioWeight_symm φ c N n j)
  simp only [div_one, mul_one, sq_abs] at hschur
  calc
    _ ≤ ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        |nonRatioWeight φ c N n j * F n * F j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
    _ = ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        |F n| * |F j| * nonRatioWeight φ c N n j := by
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro j _
      rw [abs_mul, abs_mul, abs_of_nonneg (nonRatioWeight_nonneg hφ0 hsupp hM hc n j)]
      ring
    _ ≤ ∑ n : PrimeHorizonIndex N,
        F n ^ 2 * ∑ j : PrimeHorizonIndex N, nonRatioWeight φ c N n j := hschur
    _ = _ := sum_congr rfl fun n _ => mul_comm _ _

/-- The shell degree retains the ordinary terminal moment without a conductor-separation premise. -/
theorem shell_packet_moments_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hcN : c ≤ N)
    (F : ℕ → ℝ) :
    (∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2) ≤
      2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c *
          (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
        (2 * Real.exp (3 / 2) * c * (Real.log N + 1) / N) *
          ∑ n ∈ Icc 1 N, F n ^ 2 := by
  have hterminal : (∑ n : PrimeHorizonIndex N, F n ^ 2 * (Real.log n + 1)) ≤
      (Real.log N + 1) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
    rw [sum_coe_sort (Icc 1 N) (fun n : ℕ => F n ^ 2 * (Real.log n + 1)), mul_sum]
    apply sum_le_sum
    intro n hn
    have hlog : Real.log n ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1)
        (by exact_mod_cast (mem_Icc.mp hn).2)
    exact (mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) (sq_nonneg _)).trans_eq
      (mul_comm _ _)
  have h := shellDegree_packet_payment_le hφ hsupp hM hc hcN F
  rw [sum_coe_sort (Icc 1 N) (fun n : ℕ => F n ^ 2 / (n : ℝ))] at h
  refine h.trans ?_
  have ht := mul_le_mul_of_nonneg_left hterminal
    (show 0 ≤ 2 * Real.exp (3 / 2) * c / (N : ℝ) by positivity)
  convert add_le_add_left ht
    (2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c *
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))) using 1 <;> ring

private theorem abs_selfFinitePart_le {c : ℝ} (hc : 1 ≤ c) (φ : ℝ → ℝ) :
    |completeWeilSelfFinitePart φ c| ≤ |completeWeilSelfFinitePart φ 1| + Real.log c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have heq : completeWeilSelfFinitePart φ c = completeWeilSelfFinitePart φ 1 - Real.log c := by
    unfold completeWeilSelfFinitePart
    simp only [mul_one, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc0.ne']
    ring
  rw [heq]
  simpa only [abs_of_nonneg (Real.log_nonneg hc)] using
    abs_sub (completeWeilSelfFinitePart φ 1) (Real.log c)

/-- The complete scalar diagonal costs a logarithmic overlap factor and harmonic square. -/
theorem abs_complete_packet_diagonal_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c) {N : ℕ}
    (hN : 1 ≤ N) (hcN : c ≤ N) (F : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) *
      (completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N +
        floorDefect N n - mertensRemainder (N / n))| ≤
      (|completeWeilSelfFinitePart φ 1| + Real.log c + Real.exp (1 / 2) / 2 +
        Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)) *
          ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hself : |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 :=
    (abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN hcN).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left
        ((div_le_one hN0).2 hcN) (by positivity : 0 ≤ Real.exp (1 / 2) / 2))
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |F n ^ 2 / (n : ℝ) *
        (completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N +
          floorDefect N n - mertensRemainder (N / n))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, (F n ^ 2 / (n : ℝ)) *
        (|completeWeilSelfFinitePart φ 1| + Real.log c + Real.exp (1 / 2) / 2 +
          Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)) := by
      apply sum_le_sum
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hnN := (mem_Icc.mp hn).2
      have hfloor : |floorDefect N n| ≤ Real.log 2 := by
        rw [abs_of_nonneg (floorDefect_nonneg hn1 hnN)]
        exact floorDefect_le_log_two hn1 hnN
      have hmert := abs_mertensRemainder_le ((Nat.one_le_div_iff hn1).2 hnN)
      rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      calc
        _ ≤ |completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N +
            floorDefect N n| + |mertensRemainder (N / n)| := abs_sub _ _
        _ ≤ (|completeWeilSelfFinitePart φ c| + |completeWeilSelfError φ c N| +
            |floorDefect N n|) + |mertensRemainder (N / n)| :=
          add_le_add (abs_add_three _ _ _) le_rfl
        _ ≤ _ := add_le_add
          (add_le_add (add_le_add (abs_selfFinitePart_le hc φ) hself) hfloor) hmert
    _ = _ := by rw [← sum_mul, mul_comm]

#print axioms poleError_packet_eq_zero
#print axioms abs_center_packet_le
#print axioms abs_separatedCross_packet_le
#print axioms abs_half_affine_sub_shell_le
#print axioms shell_packet_moments_le
#print axioms abs_complete_packet_diagonal_le

end GaloisForLFunctions.ArithmeticCouplingTheory
