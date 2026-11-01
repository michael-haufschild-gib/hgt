import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.TerminalPrimeResiduals

/-!
# Separate prefix and terminal payments for the prime cross term

Conductor orthogonality removes the exact diagonal. Young's inequality then
charges the residual to two independently chosen mass reserves. The terminal
residual retains the harmonic length of that interval.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory SuccessorShellArithmetic
  SignedArithmeticHodgeTheory CriticalArithmeticCorrelationTheory
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics

private theorem packet_prime_residual_apply (R N : ℕ) (a : ℕ → ℝ)
    (idx : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (fullPrimeMatrix N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) -
      ∑ m ∈ Icc 1 R, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
        normalizedRamanujanHorizonVector m N) idx =
      (Real.sqrt (Real.log N))⁻¹ * ∑ m ∈ Icc 1 R, a m * ramanujanPrimeResidual m N idx := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) idx)
    (Matrix.toEuclideanLin (fullPrimeMatrix N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) -
      ∑ m ∈ Icc 1 R, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
        normalizedRamanujanHorizonVector m N) = _
  rw [map_sub, map_sum, map_sum, map_sum, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro m _
  rw [map_smul, map_smul, map_smul]
  change a m * Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) idx -
    a m * (Real.log N - ramanujanAdjunctionEnergy m) * normalizedRamanujanHorizonVector m N idx = _
  dsimp only [normalizedRamanujanHorizonVector]
  rw [map_smul]
  change a m * ((Real.sqrt (Real.log N))⁻¹ *
      Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) idx) -
    a m * (Real.log N - ramanujanAdjunctionEnergy m) *
      ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m idx) = _
  rw [fullPrimeMatrix_apply_ramanujanHorizonVector, ramanujanPrimeResidual]
  ring

private theorem two_abs_sum_mul_le {ι : Type*} (S : Finset ι) (r x : ι → ℝ)
    {t : ℝ} (ht : 0 < t) :
    2 * |∑ i ∈ S, r i * x i| ≤ (∑ i ∈ S, r i ^ 2) / t + t * ∑ i ∈ S, x i ^ 2 := by
  have hp (i : ι) : 2 * |r i * x i| ≤ r i ^ 2 / t + t * x i ^ 2 := by
    have he : r i ^ 2 / t + t * x i ^ 2 = (r i ^ 2 + t ^ 2 * x i ^ 2) / t := by
      field_simp [ht.ne']
    rw [he, le_div_iff₀ ht, abs_mul]
    have hh := sq_nonneg (|r i| - t * |x i|)
    nlinarith only [hh, sq_abs (r i), sq_abs (x i)]
  calc
    _ ≤ 2 * ∑ i ∈ S, |r i * x i| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) zero_le_two
    _ = ∑ i ∈ S, 2 * |r i * x i| := mul_sum _ _ _
    _ ≤ ∑ i ∈ S, (r i ^ 2 / t + t * x i ^ 2) := sum_le_sum fun i _ => hp i
    _ = _ := by rw [sum_add_distrib, ← sum_div, ← mul_sum]

private theorem sum_prefix_terminal {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, f n) = (∑ n ∈ Icc 1 M, f n) + ∑ n ∈ Ioc M N, f n := by
  have hs : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [hs, add_comm]
  exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm

/-- Prime cross terms use the strong prefix reserve and weak terminal reserve separately. -/
theorem exists_prime_cross_le_split_mass_reserves :
    ∃ C : ℝ, 0 < C ∧ ∀ {R M N : ℕ}, 2 ≤ R → 2 ≤ N → M ≤ N →
      ∀ a : ℕ → ℝ, ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w ∈ (conductorSubspace R N)ᗮ → ∀ s t : ℝ, 0 < s → 0 < t →
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (C * (1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
          532 * (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) / (Real.log N * s) +
        (C * (1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
          28 * (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) /
          (Real.log N * t) +
        s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) := by
  obtain ⟨C₀, hC₀, hfull⟩ := exists_primeResidual_packet_relative_log_sq_le
  obtain ⟨C₁, hC₁, hterminal⟩ := exists_primeResidual_packet_terminal_sq_le
  refine ⟨C₀ + C₁, by positivity, ?_⟩
  intro R M N hR hN hMN a w hw s t hs ht
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let d := ∑ m ∈ Icc 1 R, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
    normalizedRamanujanHorizonVector m N
  let r : ℕ → ℝ := fun n => (Real.sqrt (Real.log N))⁻¹ *
    ∑ m ∈ Icc 1 R, a m * ramanujanPrimeResidual m N n
  let x := primeHorizonExtension w
  let H := 1 + Real.log R
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let B := terminalPacketCost R M N
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hB : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hid : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ = ∑ n ∈ Icc 1 N, r n * x n := by
    have hd : d ∈ conductorSubspace R N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
    have hdw : ⟪d, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hd hw
    have he : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ =
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u - d, w⟫ := by
      rw [inner_sub_left, hdw, sub_zero]
    rw [he, EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ idx : PrimeHorizonIndex N, w idx *
      (Matrix.toEuclideanLin (fullPrimeMatrix N) u - d) idx) = _
    rw [← sum_coe_sort (Icc 1 N) (fun n => r n * x n)]
    apply sum_congr rfl
    intro idx _
    rw [packet_prime_residual_apply]
    dsimp only [r, x]
    rw [primeHorizonExtension_coe]
    ring
  have hsq (S : Finset ℕ) : (∑ n ∈ S, r n ^ 2) =
      (∑ n ∈ S, (∑ m ∈ Icc 1 R, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N := by
    rw [sum_div]
    apply sum_congr rfl
    intro n _
    dsimp only [r]
    rw [mul_pow, inv_pow, Real.sq_sqrt hL.le]
    ring
  have hres_full : (∑ n ∈ Icc 1 N, r n ^ 2) ≤
      ((C₀ + C₁) * H * A + 532 * H ^ 2 * E) / Real.log N := by
    rw [hsq]
    apply (hfull R N hR hN a).trans
    apply div_le_div_of_nonneg_right _ hL.le
    have hh : 0 ≤ C₁ * H * A := by positivity
    dsimp only [H, A, E] at hh ⊢
    linarith only [hh]
  have hres_tail : (∑ n ∈ Ioc M N, r n ^ 2) ≤
      ((C₀ + C₁) * H * A + 28 * H * B * E) / Real.log N := by
    rw [hsq]
    apply (hterminal R M N hR hN hMN a).trans
    apply div_le_div_of_nonneg_right _ hL.le
    have hact := primeActivityMass_le_log (by omega : 1 ≤ R)
    have hmul := mul_le_mul_of_nonneg_right hact
      (show 0 ≤ 2 * B * E by positivity)
    have hh : 0 ≤ C₀ * H * A := by positivity
    dsimp only [H, A, E, B] at hmul hh ⊢
    nlinarith only [hmul, hh]
  have hprefix_sq : (∑ n ∈ Icc 1 M, r n ^ 2) ≤ ∑ n ∈ Icc 1 N, r n ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) fun _ _ _ => sq_nonneg _
  have hp := two_abs_sum_mul_le (Icc 1 M) r x hs
  have ht' := two_abs_sum_mul_le (Ioc M N) r x ht
  have hfirst := div_le_div_of_nonneg_right (hprefix_sq.trans hres_full) hs.le
  have hsecond := div_le_div_of_nonneg_right hres_tail ht.le
  rw [hid, sum_prefix_terminal hMN]
  have habs := mul_le_mul_of_nonneg_left
    (abs_add_le (∑ n ∈ Icc 1 M, r n * x n) (∑ n ∈ Ioc M N, r n * x n)) zero_le_two
  change _ ≤ ((C₀ + C₁) * H * A + 532 * H ^ 2 * E) / (Real.log N * s) +
    ((C₀ + C₁) * H * A + 28 * H * B * E) / (Real.log N * t) +
    s * (∑ n ∈ Icc 1 M, x n ^ 2) + t * (∑ n ∈ Ioc M N, x n ^ 2)
  rw [div_div] at hfirst hsecond
  linarith only [habs, hp, ht', hfirst, hsecond]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_prime_cross_le_split_mass_reserves
