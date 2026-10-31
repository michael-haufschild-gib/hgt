import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.FullShellRows
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Complete-period mass pays full shell rows

Abel summation uses interval cancellation rather than a pointwise amplitude.
For a mean-zero periodic source, one complete period's absolute mass bounds
every interval sum. Full shell rows and their logarithmic variants inherit
this bound. Ramanujan Plancherel gives conductor costs m for the normalized
mode and 2m log m for the centered logarithmic divisor jet.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
noncomputable section

/-- A shifted interval has the same complete-period mass bound. -/
theorem abs_sum_Ico_periodic_le_period_mass
    {q : ℕ} (hq : 0 < q) (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ n ∈ range q, ψ n = 0) (A B : ℕ) :
    |∑ n ∈ Ico A B, ψ n| ≤ ∑ n ∈ range q, |ψ n| := by
  have hp : ∀ i, ψ (A + (i + q)) = ψ (A + i) := fun i => by
    simpa only [Nat.add_assoc] using hper (A + i)
  have hm : (∑ i ∈ range q, ψ (A + i)) = 0 :=
    (sum_range_shift_of_periodic ψ hper A).trans hmean
  have hmass := sum_range_shift_of_periodic (fun n => |ψ n|)
    (fun n => congrArg abs (hper n)) A
  rw [sum_Ico_eq_sum_range]
  exact (RenormalizedBiarithmeticGeometry.abs_sum_range_le_of_periodic hq hp hm (B - A)).trans_eq hmass

/-- Interval cancellation controls a smooth weighted lattice sum. -/
theorem abs_interval_bounded_lattice_sum_le_of_deriv
    (ψ : ℕ → ℝ) {P : ℝ} (hP : ∀ A B, |∑ n ∈ Ico A B, ψ n| ≤ P)
    {F F' : ℝ → ℝ} {M K : ℝ} (A L : ℕ)
    (hF : ∀ t ∈ Set.Icc (A : ℝ) (A + L), |F t| ≤ M)
    (hd : ∀ t ∈ Set.Icc (A : ℝ) (A + L), HasDerivAt F (F' t) t)
    (hK : ∀ t ∈ Set.Icc (A : ℝ) (A + L), |F' t| ≤ K) :
    |∑ i ∈ range L, F ((A : ℝ) + i) * ψ (A + i)| ≤ P * (M + L * K) := by
  apply abs_weighted_lattice_sum_le_of_deriv (fun i => ψ (A + i)) _ hF hd hK
  intro k _
  simpa only [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] using hP A (A + k)

theorem abs_shellPartnerKernel_sum_le_of_interval_bound
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (ψ : ℕ → ℝ) {P : ℝ} (hP : ∀ A B, |∑ n ∈ Ico A B, ψ n| ≤ P)
    {w A₁ : ℝ} (hw : 0 < w)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (A L : ℕ)
    (hleft : (ℓ : ℝ) / 2 ≤ A) (hright : (A : ℝ) + L ≤ 2 * ℓ) :
    |∑ i ∈ range L, shellPartnerKernel (atomDilate φ w) ℓ ((A : ℝ) + i) * ψ (A + i)| ≤
      P * ((∫ u, atomDilate φ w u ^ 2) / Real.sqrt ((ℓ : ℝ) / 2) +
        L * (((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ *
          ((∫ u, atomDilate φ w u ^ 2) + A₁))) := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ / 2 := by linarith only [hℓR]
  have hsub : Set.Icc (A : ℝ) (A + L) ⊆ Set.Icc ((ℓ : ℝ) / 2) (2 * ℓ) :=
    fun _ ht => ⟨hleft.trans ht.1, ht.2.trans hright⟩
  apply abs_interval_bounded_lattice_sum_le_of_deriv ψ hP A L
  · intro t ht
    have ht0 : 0 < t := hℓ0.trans_le (hsub ht).1
    have hβ : |bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ)| ≤
        ∫ u, atomDilate φ w u ^ 2 := by
      rw [bumpCorr_atomDilate_eq hw, abs_mul, abs_of_pos hw, integral_atomDilate_sq hw]
      exact mul_le_mul_of_nonneg_left
        (abs_bumpCorr_le hφ.continuous
          (HasCompactSupport.intro isCompact_Icc (fun u hu => hsupp u hu))
          ((Real.log t - Real.log ℓ) / w)) hw.le
    rw [shellPartnerKernel, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg t)]
    have hden : (Real.sqrt t)⁻¹ ≤ (Real.sqrt ((ℓ : ℝ) / 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hℓ0) (Real.sqrt_le_sqrt (hsub ht).1)
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul hden hβ (abs_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · intro t ht
    exact hasDerivAt_shellPartnerKernel hφ hsupp hw ℓ (hℓ0.trans_le (hsub ht).1)
  · intro t ht
    exact abs_deriv_shellPartnerKernel_le hφ hsupp hw hA₁ hℓ (hsub ht)

/-- The full row costs its interval-sum bound, with no pointwise amplitude factor. -/
theorem abs_full_shellPartnerKernel_sum_le_of_interval_bound
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    (ψ : ℕ → ℝ) {P : ℝ} (hP : ∀ A B, |∑ j ∈ Ico A B, ψ j| ≤ P)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        shellPartnerKernel (atomDilate φ w) n ℓ * ψ ℓ| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * P *
        (∫ u, atomDilate φ w u ^ 2) / n := by
  obtain ⟨_, hleft, _, _, hright, hAB, hlen⟩ := shellWindow_geometry hn hw hw4
  have hP0 : 0 ≤ P := by simpa using hP 0 0
  have hcells : (shellWindowLower n w : ℝ) +
      (shellWindowUpper n w - shellWindowLower n w : ℕ) = shellWindowUpper n w := by
    rw [Nat.cast_sub hAB]
    ring
  have hrow := abs_shellPartnerKernel_sum_le_of_interval_bound hφ hsupp ψ hP hw hA₁
    (by omega : 2 ≤ n) _ _ hleft (hcells.le.trans hright)
  rw [sum_shellPartnerKernel_eq_window hφ hsupp hw hw4 hn hnN, abs_mul,
    abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ poleVector n * (P * ((∫ u, atomDilate φ w u ^ 2) / Real.sqrt ((n : ℝ) / 2) +
        (shellWindowUpper n w - shellWindowLower n w : ℕ) *
          (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ *
            ((∫ u, atomDilate φ w u ^ 2) + A₁)))) :=
      mul_le_mul_of_nonneg_left hrow (by unfold poleVector; positivity)
    _ = P * (poleVector n * ((∫ u, atomDilate φ w u ^ 2) / Real.sqrt ((n : ℝ) / 2) +
        (shellWindowUpper n w - shellWindowLower n w : ℕ) *
          (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ *
            ((∫ u, atomDilate φ w u ^ 2) + A₁)))) := by ring
    _ ≤ P * ((2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) *
        (∫ u, atomDilate φ w u ^ 2) / n) :=
      mul_le_mul_of_nonneg_left
        (poleVector_window_variation_le hM hw hw4 hA₁0 (by omega : 2 ≤ n) hwn _ hlen) hP0
    _ = _ := by ring

/-- A logarithmic full row is paid by interval cancellation and one logarithm. -/
theorem abs_full_rowIntegrand_sum_le_of_interval_bound
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    (ψ : ℕ → ℝ) {P : ℝ} (hP : ∀ A B, |∑ j ∈ Ico A B, ψ j| ≤ P)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        rowIntegrand (atomDilate φ w) n ℓ * ψ ℓ| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * P *
        (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log (2 * n)) / n := by
  set A := shellWindowLower n w
  set L := shellWindowUpper n w - A
  set G := ∫ u, atomDilate φ w u ^ 2
  set D := 1 + Real.log (2 * n)
  set K := ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)
  obtain ⟨_, hleft, _, _, hright, hAB, hlen⟩ := shellWindow_geometry hn hw hw4
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hG0 : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hP0 : 0 ≤ P := by simpa using hP 0 0
  have hD0 : 0 ≤ D := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith only [hnR])
    dsimp only [D]
    linarith only [h]
  have hcells : (A : ℝ) + L = shellWindowUpper n w := by
    dsimp only [L]
    rw [Nat.cast_sub hAB]
    ring
  have hsub : Set.Icc (A : ℝ) (A + L) ⊆ Set.Icc ((n : ℝ) / 2) (2 * n) := by
    intro t ht
    exact ⟨hleft.trans ht.1, ht.2.trans (hcells.le.trans hright)⟩
  obtain ⟨hg, _, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hF (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :
      |rowIntegrand (atomDilate φ w) n t| ≤ D * G / Real.sqrt ((n : ℝ) / 2) := by
    have htI := hsub ht
    have ht1 : 1 ≤ t := by linarith only [htI.1, hnR]
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hlog : |Real.log t| ≤ D := by
      rw [abs_of_nonneg (Real.log_nonneg ht1)]
      have h := Real.log_le_log ht0 htI.2
      dsimp only [D]
      linarith only [h]
    have hinv : (Real.sqrt t)⁻¹ ≤ (Real.sqrt ((n : ℝ) / 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt htI.1)
    have hβ := abs_bumpCorr_le hg.continuous hgc (Real.log t - Real.log n)
    rw [rowIntegrand, abs_mul, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ (D * (Real.sqrt ((n : ℝ) / 2))⁻¹) * G :=
        mul_le_mul (mul_le_mul hlog hinv (by positivity) hD0) hβ (abs_nonneg _)
          (by positivity)
      _ = _ := by ring
  have hd (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :=
    hasDerivAt_rowIntegrand hφ hsupp hw n
      (show 0 < t from (by positivity : (0 : ℝ) < n / 2).trans_le (hsub ht).1)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :
      |((t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) *
          bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)))| ≤ D * K := by
    exact (abs_deriv_rowIntegrand_le hφ hsupp hw hA₁ (by omega : 2 ≤ n) (hsub ht)).trans_eq
      (by dsimp only [D, K, G]; ring)
  have hrow := abs_interval_bounded_lattice_sum_le_of_deriv ψ hP A L hF hd hb
  have hsum := sum_shellPartnerKernel_eq_window hφ hsupp hw hw4 hn hnN
    (fun ℓ => Real.log ℓ * ψ ℓ)
  have he : (∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
      rowIntegrand (atomDilate φ w) n ℓ * ψ ℓ) =
      ∑ i ∈ range L, rowIntegrand (atomDilate φ w) n ((A : ℝ) + i) * ψ (A + i) := by
    simpa only [rowIntegrand, shellPartnerKernel, Nat.cast_add,
      mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [he, abs_mul, abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ poleVector n * ((P) *
        (D * G / Real.sqrt ((n : ℝ) / 2) + L * (D * K))) :=
      mul_le_mul_of_nonneg_left hrow (by unfold poleVector; positivity)
    _ = (P * D) *
        (poleVector n * (G / Real.sqrt ((n : ℝ) / 2) + L * K)) := by ring
    _ ≤ (P * D) *
        ((2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * G / n) :=
      mul_le_mul_of_nonneg_left
        (poleVector_window_variation_le hM hw hw4 hA₁0 (by omega : 2 ≤ n) hwn L hlen)
        (by positivity)
    _ = _ := by dsimp only [D, G]; ring

/-- Ramanujan interval sums cost the conductor, without its totient amplitude. -/
theorem abs_sum_Ico_normalizedRamanujanMode_le {m : ℕ} (hm : 2 ≤ m) (A B : ℕ) :
    |∑ n ∈ Ico A B, normalizedRamanujanMode m n| ≤ (m : ℝ) := by
  have hm0 : 0 < m := by omega
  exact (abs_sum_Ico_periodic_le_period_mass hm0 (normalizedRamanujanMode m)
    (normalizedRamanujanMode_periodic hm0) (sum_range_normalizedRamanujanMode hm) A B).trans
      (sum_range_abs_normalizedRamanujanMode_le hm0)

/-- The centered divisor jet has a logarithmic conductor cost on every interval. -/
theorem abs_sum_Ico_centeredRamanujanJet_le {m : ℕ} (hm : 0 < m) (A B : ℕ) :
    |∑ n ∈ Ico A B, centeredRamanujanJet m n| ≤ 2 * m * Real.log m :=
  (abs_sum_Ico_periodic_le_period_mass hm (centeredRamanujanJet m)
    (centeredRamanujanJet_periodic m) (sum_range_centeredRamanujanJet hm) A B).trans
      (sum_range_abs_centeredRamanujanJet_le hm)

/-- A full Ramanujan shell row costs only its conductor. -/
theorem abs_fullRamanujanShellRow_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {m : ℕ} (hm : 2 ≤ m)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        shellPartnerKernel (atomDilate φ w) n ℓ * normalizedRamanujanMode m ℓ| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * m *
        (∫ u, atomDilate φ w u ^ 2) / n :=
  abs_full_shellPartnerKernel_sum_le_of_interval_bound hφ hsupp hM
    (normalizedRamanujanMode m) (abs_sum_Ico_normalizedRamanujanMode_le hm) hw hw4 hA₁0 hA₁ hn hnN hwn

/-- The logarithmic full Ramanujan row retains one index logarithm. -/
theorem abs_fullRamanujanLogShellRow_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {m : ℕ} (hm : 2 ≤ m)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        rowIntegrand (atomDilate φ w) n ℓ * normalizedRamanujanMode m ℓ| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * m *
        (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log (2 * n)) / n :=
  abs_full_rowIntegrand_sum_le_of_interval_bound hφ hsupp hM
    (normalizedRamanujanMode m) (abs_sum_Ico_normalizedRamanujanMode_le hm) hw hw4 hA₁0 hA₁ hn hnN hwn

/-- The full centered-jet row has cost at most twice the conductor times its logarithm. -/
theorem abs_fullCenteredJetShellRow_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {m : ℕ} (hm : 0 < m)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        shellPartnerKernel (atomDilate φ w) n ℓ * centeredRamanujanJet m ℓ| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * (2 * m * Real.log m) *
        (∫ u, atomDilate φ w u ^ 2) / n :=
  abs_full_shellPartnerKernel_sum_le_of_interval_bound hφ hsupp hM
    (centeredRamanujanJet m) (abs_sum_Ico_centeredRamanujanJet_le hm) hw hw4 hA₁0 hA₁ hn hnN hwn

#print axioms abs_sum_Ico_periodic_le_period_mass
#print axioms abs_full_shellPartnerKernel_sum_le_of_interval_bound
#print axioms abs_full_rowIntegrand_sum_le_of_interval_bound
#print axioms abs_fullRamanujanShellRow_le
#print axioms abs_fullRamanujanLogShellRow_le
#print axioms abs_fullCenteredJetShellRow_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
