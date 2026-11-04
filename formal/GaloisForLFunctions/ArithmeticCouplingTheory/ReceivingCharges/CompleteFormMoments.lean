import GaloisForLFunctions.ArithmeticCouplingTheory.TheShellDegreeHasAnExplicitRowBound
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionRetainsThePrimeDefect
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.NearOverlapMoments

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
  simp only [primeHorizonExtension, hn]
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
    abs_div, abs_of_nonneg (a := (N : ℝ)) (Nat.cast_nonneg N)]
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

/-- The affine term itself is at most four shell diagonals. -/
theorem affineDirichlet_le_four_shell {φ : ℝ → ℝ} (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (N : ℕ) (F : ℕ → ℝ) :
    affineDirichlet φ c N F ≤
      4 * ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2 := by
  have h := (abs_le.mp (abs_half_affine_sub_shell_le hφ0 hsupp hM hc N F)).2
  linarith only [h]

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
    have hlog1 : Real.log n + 1 ≤ Real.log N + 1 := by linarith only [hlog]
    exact (mul_le_mul_of_nonneg_left hlog1 (sq_nonneg (F n))).trans_eq (mul_comm _ _)
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
      (by
        have hw : c / (N : ℝ) ≤ 1 := (div_le_one hN0).2 hcN
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ Real.exp (1 / 2) / 2)))
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

/-- Every term of the complete form is retained in a two-moment error bound. -/
theorem exists_complete_packet_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ F : ℕ → ℝ, (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      |completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F| ≤
        (|completeWeilSelfFinitePart φ 1| + Real.log c + Real.exp (1 / 2) / 2 +
          Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant) +
          2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c +
          4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * c ^ 2) *
            (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
        ((2 * Real.exp (3 / 2) * c * (Real.log N + 1) +
          c * ((harmonic N : ℝ) + 1) +
          2 * CriticalArithmeticCorrelationTheory.linearNearRowRadius c ^ 2 *
            (Real.log N + C + c * (Real.log N + 2))) / N) *
              ∑ n ∈ Icc 1 N, F n ^ 2 := by
  obtain ⟨C, hC, hov⟩ := exists_abs_overlap_packet_le hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro c N hc hN hw F hF
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c ≤ N := (div_le_one hN0).1 (by linarith only [hw])
  have hshell := (abs_half_affine_sub_shell_le hφ0 hsupp hM hc0 N F).trans
    (shell_packet_moments_le hφ hsupp hM hc0 hcN F)
  have hdiag := abs_complete_packet_diagonal_le hφ hsupp hM hc hN hcN F
  have hcenter := abs_center_packet_le hφ.continuous hsupp hM hc0.le N F hF
  have hcross := abs_separatedCross_packet_le hφ hsupp hM hc0 hN F
  have hoverlap := hov c N hc hN hw F
  have heq := completeWeilEnergy_packetVector_at_every_overlap hφ hsupp hM hc0 hN F
  rw [poleError_packet_eq_zero φ c N F hF, add_zero] at heq
  have halgebra : completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F =
      ((1 / 2) * affineDirichlet φ c N F -
        ∑ n : PrimeHorizonIndex N, shellDegree φ c N n * F n ^ 2) +
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) *
        (completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N +
          floorDefect N n - mertensRemainder (N / n))) +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (packetVector F N), packetVector F N⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N),
        packetVector F N⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N), packetVector F N⟫ := by
    rw [heq]
    ring
  have htriangle (a b d e f : ℝ) :
      |a + b + d - e + f| ≤ |a| + |b| + |d| + |e| + |f| := by
    calc
      _ ≤ |a + b + d - e| + |f| := abs_add_le _ _
      _ ≤ (|a + b + d| + |e|) + |f| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (abs_add_three _ _ _) le_rfl) le_rfl
  rw [halgebra]
  refine (htriangle _ _ _ _ _).trans ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hshell hdiag) hcenter) hcross)
    hoverlap
  exact hsum.trans_eq (by ring)

private theorem diagonal_coefficient_le (D A X : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    D + Real.log c + A * c + X * c ^ 2 ≤ (|D| + 1 + |A| + |X|) * c ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hc2 : c ≤ c ^ 2 := by nlinarith only [mul_nonneg hc0.le (sub_nonneg.mpr hc)]
  have h12 : 1 ≤ c ^ 2 := hc.trans hc2
  have hD : D ≤ |D| * c ^ 2 := calc
    D ≤ |D| := le_abs_self D
    _ = |D| * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h12 (abs_nonneg D)
  have hlog := (Real.log_le_sub_one_of_pos hc0).trans ((sub_le_self c zero_le_one).trans hc2)
  have hA := (mul_le_mul_of_nonneg_right (le_abs_self A) hc0.le).trans
    (mul_le_mul_of_nonneg_left hc2 (abs_nonneg A))
  have hX := mul_le_mul_of_nonneg_right (le_abs_self X) (sq_nonneg c)
  nlinarith only [hD, hlog, hA, hX]

private theorem terminal_coefficient_le (B : ℝ) {C c L H : ℝ}
    (hC : 0 ≤ C) (hc : 1 ≤ c) (hL : 0 ≤ L) (hH : H ≤ 1 + L) :
    B * c * (L + 1) + c * (H + 1) +
      2 * CriticalArithmeticCorrelationTheory.linearNearRowRadius c ^ 2 *
        (L + C + c * (L + 2)) ≤
      (|B| + 2 + 8 * Real.exp 2 ^ 2 * (C + 3)) * c ^ 3 * (L + 1) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith only [sq_nonneg (c - 1), hc]
  have hc3 : c ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc2 hc0.le
    nlinarith only [h]
  have hL1 : 0 ≤ L + 1 := by linarith only [hL]
  have hcl1 : 1 ≤ c * (L + 1) := by
    have h := mul_nonneg hc0.le hL
    nlinarith only [h, hc]
  have hsmall : L + C + c * (L + 2) ≤ (C + 3) * c * (L + 1) := by
    have h1 : L ≤ c * (L + 1) := by
      have h := mul_nonneg (sub_nonneg.mpr hc) hL
      nlinarith only [h, hc]
    have h2 := mul_le_mul_of_nonneg_left hcl1 hC
    have h3 : c * (L + 2) ≤ 2 * c * (L + 1) := by
      have h := mul_nonneg hc0.le hL
      nlinarith only [h]
    nlinarith only [h1, h2, h3]
  have hB : B * c * (L + 1) ≤ |B| * c ^ 3 * (L + 1) :=
    mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (le_abs_self B) hc0.le).trans
        (mul_le_mul_of_nonneg_left hc3 (abs_nonneg B))) hL1
  have hcenter : c * (H + 1) ≤ 2 * c ^ 3 * (L + 1) := by
    calc
      _ ≤ c * (L + 2) := mul_le_mul_of_nonneg_left (by linarith only [hH]) hc0.le
      _ ≤ 2 * c * (L + 1) := by nlinarith only [mul_nonneg hc0.le hL]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc3 zero_le_two) hL1
  have hoverlap := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 2 * CriticalArithmeticCorrelationTheory.linearNearRowRadius c ^ 2 by positivity)
  unfold CriticalArithmeticCorrelationTheory.linearNearRowRadius at hoverlap ⊢
  nlinarith only [hB, hcenter, hoverlap]

/-- A uniform two-moment bound on the full neutral form, with every overlap term included. -/
theorem exists_complete_packet_two_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ F : ℕ → ℝ, (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      |completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F| ≤
        A * c ^ 2 * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
        (B * c ^ 3 * (Real.log N + 1) / N) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_complete_packet_moment_bound hφ hφ0 hsupp hM
  let D := |completeWeilSelfFinitePart φ 1| + Real.exp (1 / 2) / 2 +
    Real.log 2 + (Real.log 4 + 4 + Real.eulerMascheroniConstant)
  let X := 4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))
  let A₀ := 2 * (Real.log 4 + 4) * Real.exp (5 / 2)
  let B₀ := 2 * Real.exp (3 / 2)
  refine ⟨|D| + 1 + |A₀| + |X|, |B₀| + 2 + 8 * Real.exp 2 ^ 2 * (C + 3),
    by positivity, by positivity, ?_⟩
  intro c N hc hN hw F hF
  have hdiag := diagonal_coefficient_le D A₀ X hc
  have hterminal := terminal_coefficient_le B₀ hC hc (Real.log_natCast_nonneg N)
    (harmonic_le_one_add_log N)
  have hH0 : 0 ≤ ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) :=
    sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  have hO0 : 0 ≤ ∑ n ∈ Icc 1 N, F n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h := add_le_add (mul_le_mul_of_nonneg_right hdiag hH0)
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hterminal (Nat.cast_nonneg N)) hO0)
  refine (hbound c N hc hN hw F hF).trans ?_
  convert h using 1
  dsimp only [D, A₀, B₀, X]
  ring

#print axioms poleError_packet_eq_zero
#print axioms abs_center_packet_le
#print axioms abs_separatedCross_packet_le
#print axioms abs_half_affine_sub_shell_le
#print axioms shell_packet_moments_le
#print axioms abs_complete_packet_diagonal_le
#print axioms exists_complete_packet_moment_bound
#print axioms exists_complete_packet_two_moment_bound

end GaloisForLFunctions.ArithmeticCouplingTheory
