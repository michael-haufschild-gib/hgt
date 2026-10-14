import GaloisForLFunctions.RHTower.MobiusRieszSquareSourceQuadrature
import GaloisForLFunctions.RHTower.MobiusDivisorOneSidedPowerGapBootstrap
import GaloisForLFunctions.RHTower.MobiusDivisorLowerStripPowerGapBootstrap
import GaloisForLFunctions.RHTower.SuzukiObserverJetPositiveCurvature
import GaloisForLFunctions.RHTower.SuzukiObserverJetLinearActionClassification
import GaloisForLFunctions.RHTower.SuzukiObserverJetBoundaryAsymptotics
import GaloisForLFunctions.RHTower.WeilLagPowerGapSampling

open scoped BigOperators
open Real Filter Topology
open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem weightedPrefix_eq_sum_observerJetMass (q : ℕ → ℝ) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) =
      ∑ k ∈ Finset.range (j + 1), observerJetMass q k := by
  have hd := observerJetDrift_eq_mass_mul_succ_sub_prefixSum q j
  have hsplit :
      (∑ k ∈ Finset.range (j + 1), ((j + 1 - k : ℕ) : ℝ) * q k) =
        ((j : ℝ) + 1) * observerJetMass q j - observerJetDrift q j := by
    rw [observerJetMass, observerJetDrift, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j + 1 := by
      have := Finset.mem_range.mp hk
      omega
    rw [Nat.cast_sub hkj]
    push_cast
    ring
  linarith

theorem observerJetSecondHistory_residual_eq_sum_mass_sub
    (q : ℕ → ℝ) (N j : ℕ) (hN : 1 ≤ N) (hjN : j + 1 ≤ N) :
    observerJetSecondHistory (observerJetResidual q N) j =
      ∑ k ∈ Finset.Ico (j + 1) N, (observerJetMass q N - observerJetMass q k) := by
  rw [observerJetResidual_history_eq_prefix_sub_mass_add_drift q N j hN hjN,
    weightedPrefix_eq_sum_observerJetMass q j,
    observerJetDrift_eq_mass_mul_succ_sub_prefixSum q N]
  have hsplit := Finset.sum_range_add_sum_Ico (observerJetMass q) (show j + 1 ≤ N + 1 by omega)
  have htop :
      (∑ k ∈ Finset.Ico (j + 1) (N + 1), observerJetMass q k) =
        (∑ k ∈ Finset.Ico (j + 1) N, observerJetMass q k) + observerJetMass q N :=
    Finset.sum_Ico_succ_top hjN (observerJetMass q)
  have hconst :
      (∑ k ∈ Finset.Ico (j + 1) N, (observerJetMass q N - observerJetMass q k)) =
        ((N - (j + 1) : ℕ) : ℝ) * observerJetMass q N -
          ∑ k ∈ Finset.Ico (j + 1) N, observerJetMass q k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hconst, ← hsplit, htop]
  rw [Nat.cast_sub hjN]
  push_cast
  ring

theorem observerJetMass_sub_eq_sum_Ico (q : ℕ → ℝ) {k N : ℕ} (hkN : k ≤ N) :
    observerJetMass q N - observerJetMass q k =
      ∑ i ∈ Finset.Ico (k + 1) (N + 1), q i := by
  unfold observerJetMass
  have hsplit := Finset.sum_range_add_sum_Ico q (show k + 1 ≤ N + 1 by omega)
  linarith

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Section 1: Unweighted Square-Sample One-Sided Strip Laws and Power-Gap Bootstrap -/

/-- Left-endpoint Chebyshev-free lower quadrature bound for the completed square-root
Abel moment at `N²` in terms of the unweighted square-sample sum `∑_{1 ≤ s < N} (ψ(s²) - s²)`. -/
theorem psiRemainder_squareSum_lower_quadrature {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) +
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) - ((N : ℝ) ^ 2 - 1) ≤
      mobiusDivisorSquareRootAbelMoment (N ^ 2) := by
  have hb := (mobiusDivisorSquareRootAbel_square_quadrature_bounds hN).1
  have heq : completedChebyshevSquareSampleMoment N =
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) +
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := by
    simp [completedChebyshevSquareSampleMoment, Finset.sum_add_distrib]
  linarith

/-- Right-endpoint Chebyshev-free upper quadrature bound for the completed square-root
Abel moment at `N²` in terms of the unweighted square-sample sum `∑_{1 ≤ s ≤ N} (ψ(s²) - s²)`. -/
theorem psiRemainder_squareSum_upper_quadrature {N : ℕ} (hN : 1 ≤ N) :
    mobiusDivisorSquareRootAbelMoment (N ^ 2) ≤
      (∑ s ∈ Finset.Icc 1 N, psiRemainder (s ^ 2)) +
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) + (N : ℝ) ^ 2 := by
  have hb := (mobiusDivisorSquareRootAbel_square_quadrature_bounds hN).2
  have he1 : psiRemainder 1 = -1 := by norm_num [psiRemainder, chebyshevPsi]
  have heq : completedChebyshevSquareSampleMoment N =
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) +
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := by
    simp [completedChebyshevSquareSampleMoment, Finset.sum_add_distrib]
  have htop : (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) + psiRemainder (N ^ 2) =
      ∑ s ∈ Finset.Icc 1 N, psiRemainder (s ^ 2) := by
    rw [← Finset.sum_Ico_succ_top hN (fun s => psiRemainder (s ^ 2))]
    rfl
  linarith

/-- Total quadratic quadrature bound between `mobiusDivisorSquareRootAbelMoment (N²)`
and the unweighted square-sample sum `∑_{1 ≤ s < N} (ψ(s²) - s²)`. -/
theorem abs_mobiusDivisorSquareRootAbel_sub_psiRemainder_squareSum_le {N : ℕ} (hN : 1 ≤ N) :
    |mobiusDivisorSquareRootAbelMoment (N ^ 2) -
        ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| ≤
      (9 + |2 * Real.eulerMascheroniConstant|) * (N : ℝ) ^ 2 := by
  have h1 := abs_mobiusDivisorSquareRootAbel_sub_squareSample_le hN
  have heq : completedChebyshevSquareSampleMoment N -
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) =
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := by
    simp [completedChebyshevSquareSampleMoment, Finset.sum_add_distrib]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hle : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    nlinarith
  have h2 : |completedChebyshevSquareSampleMoment N -
      ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| ≤
        |2 * Real.eulerMascheroniConstant| * (N : ℝ) ^ 2 := by
    rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
  calc
    |mobiusDivisorSquareRootAbelMoment (N ^ 2) -
        ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| =
      |(mobiusDivisorSquareRootAbelMoment (N ^ 2) - completedChebyshevSquareSampleMoment N) +
        (completedChebyshevSquareSampleMoment N -
          ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2))| := by ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment (N ^ 2) - completedChebyshevSquareSampleMoment N| +
        |completedChebyshevSquareSampleMoment N -
          ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| := abs_add_le _ _
    _ ≤ 9 * (N : ℝ) ^ 2 + |2 * Real.eulerMascheroniConstant| * (N : ℝ) ^ 2 :=
      add_le_add h1 h2
    _ = (9 + |2 * Real.eulerMascheroniConstant|) * (N : ℝ) ^ 2 := by ring

/-- Every `n ≥ 1` lies within `2 √n` of the preceding square `N² = (Nat.sqrt n)²`. -/
theorem exists_square_le_sub_le_two_mul_sqrt {n : ℕ} (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ N ^ 2 ≤ n ∧ (n : ℝ) - (N ^ 2 : ℕ) ≤ 2 * Real.sqrt n := by
  let N := Nat.sqrt n
  have hN1 : 1 ≤ N := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := Nat.sqrt_eq_zero.mp h0
    omega
  have hle : N ^ 2 ≤ n := by
    simpa only [sq] using Nat.sqrt_le n
  have hlt : n < (N + 1) ^ 2 := by
    simpa only [sq] using Nat.lt_succ_sqrt n
  have hgap_nat : n - N ^ 2 ≤ 2 * N := by
    have : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
    omega
  have hN_le_sqrt : (N : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg N)]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hle
  refine ⟨N, hN1, hle, ?_⟩
  have hgap_real : (n : ℝ) - (N ^ 2 : ℕ) ≤ 2 * (N : ℝ) := by
    rw [← Nat.cast_sub hle]
    exact_mod_cast hgap_nat
  linarith

/-- **Bootstrap-free one-sided lower strip law for the unweighted square-sample sum.** -/
theorem abs_re_sub_half_le_of_neg_rpow_le_psiRemainder_squareSum
    {M c : ℝ} {N₀ : ℕ} (hM : 0 ≤ M)
    (hlow : ∀ N : ℕ, N₀ ≤ N →
      -(M * (N : ℝ) ^ 2 + M * (N : ℝ) ^ (2 + 2 * c)) ≤
        ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let A : Set ℕ := {k : ℕ | ∃ N : ℕ, max 2 N₀ ≤ N ∧ k = N ^ 2}
  let B : ℝ := M + |2 * Real.eulerMascheroniConstant| + 1
  have hB : 0 ≤ B := by positivity
  refine abs_re_sub_half_le_of_sqrtGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    (A := A) (M := B) (c := c) (K := 2) (N₀ := (max 2 N₀) ^ 2) hB (by norm_num) ?_ ?_ q
  · rintro k ⟨N, hN, rfl⟩ _hk2
    have hN2 : 2 ≤ N := (le_max_left 2 N₀).trans hN
    have hN0 : N₀ ≤ N := (le_max_right 2 N₀).trans hN
    have hNpos : (0 : ℝ) < N := by positivity
    have hsq_pos : (0 : ℝ) < (N ^ 2 : ℕ) := by positivity
    have hq := psiRemainder_squareSum_lower_quadrature (by omega : 1 ≤ N)
    have hl := hlow N hN0
    have hgamma : -(|2 * Real.eulerMascheroniConstant| * (N : ℝ) ^ 2) ≤
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := by
      have h1 : -(|(N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant)|) ≤
          (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := neg_abs_le _
      have h2 : |(N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant)| ≤
          |2 * Real.eulerMascheroniConstant| * (N : ℝ) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hle : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        nlinarith
      linarith
    have hrpow : (N : ℝ) ^ (2 + 2 * c) = (N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ c := by
      rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hNpos.le,
        ← Real.rpow_add hNpos]
      ring_nf
    have hcomb : -(B + B * ((N ^ 2 : ℕ) : ℝ) ^ c) * ((N ^ 2 : ℕ) : ℝ) ≤
        mobiusDivisorSquareRootAbelMoment (N ^ 2) := by
      push_cast
      have hrc0 : 0 ≤ ((N : ℝ) ^ 2) ^ c := Real.rpow_nonneg (by positivity) c
      have hextra : 0 ≤ (|2 * Real.eulerMascheroniConstant| + 1) *
          ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ c) := by positivity
      dsimp only [B]
      nlinarith [hq, hl, hgamma, hrpow, hextra]
    exact (le_div_iff₀ hsq_pos).mpr hcomb
  · intro n hn
    let N := Nat.sqrt n
    have hle : N ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
    have hlt : n < (N + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
    have hN : max 2 N₀ ≤ N := by
      have hlt_sq : (max 2 N₀) ^ 2 < (N + 1) ^ 2 := lt_of_le_of_lt hn hlt
      nlinarith
    have hgap_nat : n - N ^ 2 ≤ 2 * N := by
      have : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
      omega
    have hN_le_sqrt : (N : ℝ) ≤ Real.sqrt n := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg N)]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hle)
    have hgap_real : (n : ℝ) - (N ^ 2 : ℕ) ≤ 2 * (N : ℝ) := by
      rw [← Nat.cast_sub hle]
      exact_mod_cast hgap_nat
    exact ⟨N ^ 2, ⟨N, hN, rfl⟩, hle, by linarith⟩

/-- **Power-gap transfer to squares.** -/
theorem exists_square_in_image_sub_le_rpow
    {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ}
    (_hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hA : ∀ N : ℕ, N₀ ≤ N → ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ))
    {n : ℕ} (hn : (max 1 N₀) ^ 2 ≤ n) :
    ∃ k ∈ (fun m : ℕ => m ^ 2) '' A,
      k ≤ n ∧ (n : ℝ) - k ≤ (2 * K + 2) * (n : ℝ) ^ (1 - δ / 2) := by
  let N := Nat.sqrt n
  have hN_sq_le : N ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
  have hlt : n < (N + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
  have hN_max : max 1 N₀ ≤ N := by
    have hlt_sq : (max 1 N₀) ^ 2 < (N + 1) ^ 2 := lt_of_le_of_lt hn hlt
    nlinarith
  have hN1 : 1 ≤ N := (le_max_left 1 N₀).trans hN_max
  have hN0 : N₀ ≤ N := (le_max_right 1 N₀).trans hN_max
  obtain ⟨m, hmA, hmN, hgap_m⟩ := hA N hN0
  have hm_sq_le : m ^ 2 ≤ n := (Nat.pow_le_pow_left hmN 2).trans hN_sq_le
  have hgap_N : (n : ℝ) - (N : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
    have hnat : n - N ^ 2 ≤ 2 * N := by
      have : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
      omega
    have hcast : (n : ℝ) - (N ^ 2 : ℕ) ≤ 2 * (N : ℝ) := by
      rw [← Nat.cast_sub hN_sq_le]
      exact_mod_cast hnat
    simpa only [Nat.cast_pow] using hcast
  have hm_le_N_real : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hN_pos : (0 : ℝ) < N := by positivity
  have hn_pos : (0 : ℝ) < n := by
    have : 1 ≤ n := (by nlinarith [hN1] : 1 ≤ N ^ 2).trans hN_sq_le
    positivity
  have hN_le_rpow : (N : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (Nat.cast_nonneg N)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN_sq_le)
  have hN_le_target : (N : ℝ) ≤ (n : ℝ) ^ (1 - δ / 2) := by
    refine hN_le_rpow.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    have : 1 ≤ n := (by nlinarith [hN1] : 1 ≤ N ^ 2).trans hN_sq_le
    exact_mod_cast this
  have hN_pow_le_target : (N : ℝ) ^ (2 - δ) ≤ (n : ℝ) ^ (1 - δ / 2) := by
    have hexp : 0 ≤ 2 - δ := by linarith
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le_rpow hexp
    rw [← Real.rpow_mul hn_pos.le] at h1
    convert h1 using 2
    ring
  have hdiff_sq : (N : ℝ) ^ 2 - (m : ℝ) ^ 2 ≤ 2 * K * (N : ℝ) ^ (2 - δ) := by
    calc
      (N : ℝ) ^ 2 - (m : ℝ) ^ 2 = ((N : ℝ) + m) * ((N : ℝ) - m) := by ring
      _ ≤ (2 * (N : ℝ)) * (K * (N : ℝ) ^ (1 - δ)) := by
        apply mul_le_mul (by linarith) hgap_m (by linarith) (by positivity)
      _ = 2 * K * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 - δ)) := by
        rw [Real.rpow_one]
        ring
      _ = 2 * K * (N : ℝ) ^ (2 - δ) := by
        rw [← Real.rpow_add hN_pos]
        ring_nf
  refine ⟨m ^ 2, ⟨m, hmA, rfl⟩, hm_sq_le, ?_⟩
  push_cast
  calc
    (n : ℝ) - (m : ℝ) ^ 2 = ((n : ℝ) - (N : ℝ) ^ 2) + ((N : ℝ) ^ 2 - (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) + 2 * K * (N : ℝ) ^ (2 - δ) := add_le_add hgap_N hdiff_sq
    _ ≤ 2 * (n : ℝ) ^ (1 - δ / 2) + 2 * K * (n : ℝ) ^ (1 - δ / 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hN_le_target (by norm_num))
        (mul_le_mul_of_nonneg_left hN_pow_le_target (by positivity))
    _ = (2 * K + 2) * (n : ℝ) ^ (1 - δ / 2) := by ring

/-- **Power-gap upper strip law for the unweighted square-sample sum.** -/
theorem abs_re_sub_half_le_of_powerGaps_psiRemainder_squareSum_le_rpow
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hup : ∀ m ∈ A, 2 ≤ m →
      (∑ s ∈ Finset.Ico 1 m, psiRemainder (s ^ 2)) ≤
        M * (m : ℝ) ^ 2 + M * (m : ℝ) ^ (2 + 2 * c))
    (hA : ∀ N : ℕ, N₀ ≤ N → ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let δ' : ℝ := min δ 1
  have hδ'0 : 0 < δ' := lt_min hδ zero_lt_one
  have hδ'1 : δ' ≤ 1 := min_le_right δ 1
  have hA' : ∀ N : ℕ, max 1 N₀ ≤ N →
      ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ') := by
    intro N hN
    obtain ⟨m, hmA, hmN, hgap⟩ := hA N ((le_max_right 1 N₀).trans hN)
    refine ⟨m, hmA, hmN, hgap.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (le_max_left 1 N₀).trans hN
    · have : δ' ≤ δ := min_le_left δ 1
      linarith
  let B : ℝ := M + 9 + |2 * Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by positivity
  refine abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (A := (fun m : ℕ => m ^ 2) '' A) (M := B) (c := c)
    (K := 2 * K + 2) (δ := δ' / 2) (N₀ := (max 1 N₀) ^ 2)
    hB (by linarith) (by positivity) ?_ ?_ q
  · rintro k ⟨m, hmA, rfl⟩ hk2
    change 2 ≤ m ^ 2 at hk2
    have hm2 : 2 ≤ m := by nlinarith
    have hm1 : 1 ≤ m := by omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hsq_pos : (0 : ℝ) < (m ^ 2 : ℕ) := by positivity
    have hq := (abs_le.mp (abs_mobiusDivisorSquareRootAbel_sub_psiRemainder_squareSum_le hm1)).2
    have hu := hup m hmA hm2
    have hrpow : (m : ℝ) ^ (2 + 2 * c) = (m : ℝ) ^ 2 * ((m : ℝ) ^ 2) ^ c := by
      rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul hm_pos.le,
        ← Real.rpow_add hm_pos]
      ring_nf
    have hcomb : mobiusDivisorSquareRootAbelMoment (m ^ 2) ≤
        (B + B * ((m ^ 2 : ℕ) : ℝ) ^ c) * ((m ^ 2 : ℕ) : ℝ) := by
      push_cast
      have hrc0 : 0 ≤ ((m : ℝ) ^ 2) ^ c := Real.rpow_nonneg (by positivity) c
      have hextra : 0 ≤ (9 + |2 * Real.eulerMascheroniConstant|) *
          ((m : ℝ) ^ 2 * ((m : ℝ) ^ 2) ^ c) := by positivity
      dsimp only [B]
      nlinarith [hq, hu, hrpow, hextra]
    exact (div_le_iff₀ hsq_pos).mpr hcomb
  · intro n hn
    have hn' : (max 1 (max 1 N₀)) ^ 2 ≤ n := by simpa using hn
    exact exists_square_in_image_sub_le_rpow hδ'0 hδ'1 hK hA' hn'

/-- **Power-gap lower strip law for the unweighted square-sample sum.** -/
theorem abs_re_sub_half_le_of_powerGaps_neg_rpow_le_psiRemainder_squareSum
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlow : ∀ m ∈ A, 2 ≤ m →
      -(M * (m : ℝ) ^ 2 + M * (m : ℝ) ^ (2 + 2 * c)) ≤
        ∑ s ∈ Finset.Ico 1 m, psiRemainder (s ^ 2))
    (hA : ∀ N : ℕ, N₀ ≤ N → ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let δ' : ℝ := min δ 1
  have hδ'0 : 0 < δ' := lt_min hδ zero_lt_one
  have hδ'1 : δ' ≤ 1 := min_le_right δ 1
  have hA' : ∀ N : ℕ, max 1 N₀ ≤ N →
      ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ') := by
    intro N hN
    obtain ⟨m, hmA, hmN, hgap⟩ := hA N ((le_max_right 1 N₀).trans hN)
    refine ⟨m, hmA, hmN, hgap.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (le_max_left 1 N₀).trans hN
    · have : δ' ≤ δ := min_le_left δ 1
      linarith
  let B : ℝ := M + 9 + |2 * Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by positivity
  refine abs_re_sub_half_le_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    (A := (fun m : ℕ => m ^ 2) '' A) (M := B) (c := c)
    (K := 2 * K + 2) (δ := δ' / 2) (N₀ := (max 1 N₀) ^ 2)
    hB (by linarith) (by positivity) ?_ ?_ q
  · rintro k ⟨m, hmA, rfl⟩ hk2
    change 2 ≤ m ^ 2 at hk2
    have hm2 : 2 ≤ m := by nlinarith
    have hm1 : 1 ≤ m := by omega
    have hm_pos : (0 : ℝ) < m := by positivity
    have hsq_pos : (0 : ℝ) < (m ^ 2 : ℕ) := by positivity
    have hq := (abs_le.mp (abs_mobiusDivisorSquareRootAbel_sub_psiRemainder_squareSum_le hm1)).1
    have hl := hlow m hmA hm2
    have hrpow : (m : ℝ) ^ (2 + 2 * c) = (m : ℝ) ^ 2 * ((m : ℝ) ^ 2) ^ c := by
      rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul hm_pos.le,
        ← Real.rpow_add hm_pos]
      ring_nf
    have hcomb : -(B + B * ((m ^ 2 : ℕ) : ℝ) ^ c) * ((m ^ 2 : ℕ) : ℝ) ≤
        mobiusDivisorSquareRootAbelMoment (m ^ 2) := by
      push_cast
      have hrc0 : 0 ≤ ((m : ℝ) ^ 2) ^ c := Real.rpow_nonneg (by positivity) c
      have hextra : 0 ≤ (9 + |2 * Real.eulerMascheroniConstant|) *
          ((m : ℝ) ^ 2 * ((m : ℝ) ^ 2) ^ c) := by positivity
      dsimp only [B]
      nlinarith [hq, hl, hrpow, hextra]
    exact (le_div_iff₀ hsq_pos).mpr hcomb
  · intro n hn
    have hn' : (max 1 (max 1 N₀)) ^ 2 ≤ n := by simpa using hn
    exact exists_square_in_image_sub_le_rpow hδ'0 hδ'1 hK hA' hn'

/-- **One-sided upper strip law for the unweighted square-sample sum.** -/
theorem abs_re_sub_half_le_of_psiRemainder_squareSum_le_rpow
    {M c : ℝ} {N₀ : ℕ} (hM : 0 ≤ M)
    (hup : ∀ N : ℕ, N₀ ≤ N →
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) ≤
        M * (N : ℝ) ^ 2 + M * (N : ℝ) ^ (2 + 2 * c))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let A : Set ℕ := {N : ℕ | N₀ ≤ N}
  exact abs_re_sub_half_le_of_powerGaps_psiRemainder_squareSum_le_rpow
    (A := A) (M := M) (c := c) (K := 0) (δ := 1 / 2) (N₀ := N₀)
    hM (by norm_num) (by norm_num) (fun m hm _hm2 => hup m hm)
    (fun N hN => ⟨N, hN, le_rfl, by simp⟩) q

/-- **RH is equivalent to a quadratic lower bound for the unweighted square-sample sum.** -/
theorem riemannHypothesis_iff_psiRemainder_squareSum_boundedBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(B * (N : ℝ) ^ 2) ≤ ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2) := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ :=
      riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow.mp hRH
    refine ⟨max 0 (-B) + 9 + |2 * Real.eulerMascheroniConstant|, fun N hN => ?_⟩
    have hsq : 2 ≤ N ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (N ^ 2 : ℕ) := by positivity
    have hb := (le_div_iff₀ hd).mp (hB (N ^ 2) hsq)
    have hq := (abs_le.mp (abs_mobiusDivisorSquareRootAbel_sub_psiRemainder_squareSum_le
      (by omega : 1 ≤ N))).2
    have hB_le : -B ≤ max 0 (-B) := le_max_right 0 (-B)
    push_cast at hb
    nlinarith
  · rintro ⟨B, hB⟩
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := abs_re_sub_half_le_of_neg_rpow_le_psiRemainder_squareSum
      (M := max 0 B) (c := 0) (N₀ := 2) (le_max_left 0 B) (fun N hN => ?_) q
    · rw [max_self] at h
      linarith [(abs_le.mp h).2]
    · have hB_le : B ≤ max 0 B := le_max_right 0 B
      have h0 : 0 ≤ max 0 B * (N : ℝ) ^ 2 := by positivity
      have hb := hB N hN
      rw [mul_zero, add_zero, Real.rpow_two]
      nlinarith

/-- **Power-gap sampling equivalence (upper and lower) for the unweighted square-sample sum.** -/
theorem riemannHypothesis_iff_psiRemainder_squareSum_bddAbove_of_powerGaps
    {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA : ∀ N : ℕ, N₀ ≤ N → ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ m ∈ A, 2 ≤ m →
        (∑ s ∈ Finset.Ico 1 m, psiRemainder (s ^ 2)) / ((m : ℝ) ^ 2) ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ := riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove.mp hRH
    refine ⟨B, fun m _hm hm2 => ?_⟩
    have hd : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    exact (div_le_iff₀ hd).mpr (hB m hm2)
  · rintro ⟨B, hB⟩
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := abs_re_sub_half_le_of_powerGaps_psiRemainder_squareSum_le_rpow
      (A := A) (M := max 0 B) (c := 0) (K := K) (δ := δ) (N₀ := N₀)
      (le_max_left 0 B) hδ hK (fun m hm hm2 => ?_) hA q
    · rw [max_self] at h
      linarith [(abs_le.mp h).2]
    · have hd : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
      have hb := (div_le_iff₀ hd).mp (hB m hm hm2)
      have hB_le : B ≤ max 0 B := le_max_right 0 B
      have h0 : 0 ≤ max 0 B * (m : ℝ) ^ 2 := by positivity
      rw [mul_zero, add_zero, Real.rpow_two]
      nlinarith

theorem riemannHypothesis_iff_psiRemainder_squareSum_bddBelow_of_powerGaps
    {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA : ∀ N : ℕ, N₀ ≤ N → ∃ m ∈ A, m ≤ N ∧ (N : ℝ) - m ≤ K * (N : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ m ∈ A, 2 ≤ m →
        -B ≤ (∑ s ∈ Finset.Ico 1 m, psiRemainder (s ^ 2)) / ((m : ℝ) ^ 2) := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ := riemannHypothesis_iff_psiRemainder_squareSum_boundedBelow.mp hRH
    refine ⟨B, fun m _hm hm2 => ?_⟩
    have hd : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    exact (le_div_iff₀ hd).mpr (by linarith [hB m hm2])
  · rintro ⟨B, hB⟩
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := abs_re_sub_half_le_of_powerGaps_neg_rpow_le_psiRemainder_squareSum
      (A := A) (M := max 0 B) (c := 0) (K := K) (δ := δ) (N₀ := N₀)
      (le_max_left 0 B) hδ hK (fun m hm hm2 => ?_) hA q
    · rw [max_self] at h
      linarith [(abs_le.mp h).2]
    · have hd : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
      have hb := (le_div_iff₀ hd).mp (hB m hm hm2)
      have hB_le : B ≤ max 0 B := le_max_right 0 B
      have h0 : 0 ≤ max 0 B * (m : ℝ) ^ 2 := by positivity
      rw [mul_zero, add_zero, Real.rpow_two]
      nlinarith

/-- **Arbitrary `m`-th power sampling for the unweighted square-sample sum (upper and lower).** -/
theorem riemannHypothesis_iff_psiRemainder_squareSum_pow_bddAbove
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
        (∑ s ∈ Finset.Ico 1 (j ^ m), psiRemainder (s ^ 2)) / (((j ^ m : ℕ) : ℝ) ^ 2) ≤ B := by
  let A : Set ℕ := Set.range (fun j : ℕ => j ^ m)
  have hδ : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (m - 1) := by positivity
  have hA : ∀ n : ℕ, 1 ≤ n →
      ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤
        ((m : ℝ) * (2 : ℝ) ^ (m - 1)) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hjle, hjgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hjle, hjgap⟩
  rw [riemannHypothesis_iff_psiRemainder_squareSum_bddAbove_of_powerGaps hδ hK hA]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun j hj => hB (j ^ m) ⟨j, rfl⟩ hj⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro k ⟨j, rfl⟩ hk
    exact hB j hk

theorem riemannHypothesis_iff_psiRemainder_squareSum_pow_bddBelow
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
        -B ≤ (∑ s ∈ Finset.Ico 1 (j ^ m), psiRemainder (s ^ 2)) / (((j ^ m : ℕ) : ℝ) ^ 2) := by
  let A : Set ℕ := Set.range (fun j : ℕ => j ^ m)
  have hδ : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (m - 1) := by positivity
  have hA : ∀ n : ℕ, 1 ≤ n →
      ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤
        ((m : ℝ) * (2 : ℝ) ^ (m - 1)) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hjle, hjgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hjle, hjgap⟩
  rw [riemannHypothesis_iff_psiRemainder_squareSum_bddBelow_of_powerGaps hδ hK hA]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun j hj => hB (j ^ m) ⟨j, rfl⟩ hj⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro k ⟨j, rfl⟩ hk
    exact hB j hk

/-! ## Section 2: Negative-History Observer-Jet Strip Law & Exact Prime-Free Bridge to `lagBracketSlope` -/

/-- Negative-history action for the completed source observer jet. -/
def completedSourceObserverJetNegativeHistoryAction (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3), max (-completedSourceObserverJetHistory M j) 0 /
    Real.sqrt (j + 1 : ℕ)

/-- Signed lower bound for `mobiusDivisorSquareRootAbelMoment M` in terms of the boundary
and the negative-history action. -/
theorem mobiusDivisorSquareRootAbelMoment_ge_boundary_sub_negativeHistory
    {M : ℕ} (hM : 3 ≤ M) :
    completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
      completedSourceObserverJetDrift M *
        (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) -
      (3 / 8 : ℝ) * completedSourceObserverJetNegativeHistoryAction M ≤
        mobiusDivisorSquareRootAbelMoment M := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM,
    completedSourceObserverJetNegativeHistoryAction, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have hk0 := (observerJetCurvature_completedRieszHarmonicClockRatio_pos j).le
  have hku := observerJetCurvature_completedRieszHarmonicClockRatio_le_three_eighths j
  have hneg : -max (-completedSourceObserverJetHistory M j) 0 ≤
      completedSourceObserverJetHistory M j := by
    linarith [le_max_left (-completedSourceObserverJetHistory M j) 0]
  calc
    -((3 / 8 : ℝ) * (max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ))) =
        -(max (-completedSourceObserverJetHistory M j) 0 * (3 / (8 * Real.sqrt (j + 1 : ℕ)))) := by
      ring
    _ ≤ -(max (-completedSourceObserverJetHistory M j) 0 *
          observerJetCurvature completedRieszHarmonicClockRatio j) := by
      exact neg_le_neg (mul_le_mul_of_nonneg_left hku (le_max_right _ _))
    _ = (-max (-completedSourceObserverJetHistory M j) 0) *
          observerJetCurvature completedRieszHarmonicClockRatio j := by ring
    _ ≤ completedSourceObserverJetHistory M j *
          observerJetCurvature completedRieszHarmonicClockRatio j :=
      mul_le_mul_of_nonneg_right hneg hk0

/-- Unconditional linear lower bound for the observer-jet mass--drift boundary. -/
theorem exists_completedSourceObserverJetBoundary_linear_lower :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      -(B * M) ≤ completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) := by
  let q := completedPrimePolarGammaHarmonicCharge
  let S : ℝ := ∑' k : ℕ, |q k|
  have hq : Summable q := summable_completedPrimePolarGammaHarmonicCharge
  have habs : Summable (fun k => |q k|) := by simpa only [Real.norm_eq_abs] using hq.norm
  have hS : 0 ≤ S := tsum_nonneg (fun _ => abs_nonneg _)
  have hfinite (N : ℕ) : (∑ k ∈ Finset.range (N + 1), |q k|) ≤ S :=
    habs.sum_le_tsum _ (fun _ _ => abs_nonneg _)
  have hmass (M : ℕ) : |completedSourceObserverJetMass M| ≤ S := by
    change |∑ k ∈ Finset.range (M - 2 + 1), q k| ≤ S
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hfinite (M - 2))
  have hdrift (M : ℕ) : |completedSourceObserverJetDrift M| ≤ (M : ℝ) * S := by
    change |∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * q k| ≤ (M : ℝ) * S
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ k ∈ Finset.range (M - 2 + 1), |(k : ℝ) * q k|) =
          ∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * |q k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ ∑ k ∈ Finset.range (M - 2 + 1), (M : ℝ) * |q k| := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact_mod_cast (show k ≤ M by have := Finset.mem_range.mp hk; omega)
      _ = (M : ℝ) * ∑ k ∈ Finset.range (M - 2 + 1), |q k| := by rw [Finset.mul_sum]
      _ ≤ (M : ℝ) * S := mul_le_mul_of_nonneg_left (hfinite (M - 2)) (Nat.cast_nonneg M)
  refine ⟨S * (|completedRieszHarmonicClockRatio 0| +
    |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0|),
    by positivity, fun M hM => ?_⟩
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hSM : S ≤ (M : ℝ) * S := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hMone hS
  have hmassTerm : -((M : ℝ) * S * |completedRieszHarmonicClockRatio 0|) ≤
      completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 := by
    have h1 := neg_abs_le (completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0)
    rw [abs_mul] at h1
    have h2 : |completedSourceObserverJetMass M| * |completedRieszHarmonicClockRatio 0| ≤
        (M : ℝ) * S * |completedRieszHarmonicClockRatio 0| :=
      (mul_le_mul_of_nonneg_right (hmass M) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hSM (abs_nonneg _))
    linarith
  have hdriftTerm :
      -((M : ℝ) * S * |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0|) ≤
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) := by
    have h1 := neg_abs_le (completedSourceObserverJetDrift M *
      (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0))
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right (hdrift M)
      (abs_nonneg (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0))
    linarith
  nlinarith only [hmassTerm, hdriftTerm]

/-- Unconditional lower bound for `mobiusDivisorSquareRootAbelMoment M` in terms of
`completedSourceObserverJetNegativeHistoryAction M`. -/
theorem exists_mobiusDivisorSquareRootAbel_lower_negativeHistory :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      -(B * M + (3 / 8 : ℝ) * completedSourceObserverJetNegativeHistoryAction M) ≤
        mobiusDivisorSquareRootAbelMoment M := by
  obtain ⟨B, hB, hboundary⟩ := exists_completedSourceObserverJetBoundary_linear_lower
  refine ⟨B, hB, fun M hM => ?_⟩
  linarith [mobiusDivisorSquareRootAbelMoment_ge_boundary_sub_negativeHistory hM, hboundary M hM]

/-- **Linear bound on the negative-history action implies RH.** -/
theorem riemannHypothesis_of_completedSourceObserverJetNegativeHistory_linear
    {C : ℝ} (hC : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetNegativeHistoryAction M ≤ C * M) : RiemannHypothesis := by
  obtain ⟨B, _, hB⟩ := exists_mobiusDivisorSquareRootAbel_lower_negativeHistory
  apply riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow.mpr
  refine ⟨-max |mobiusDivisorSquareRootAbelMoment 2 / 2| (B + (3 / 8 : ℝ) * max 0 C),
    fun M hM => ?_⟩
  by_cases hM2 : M = 2
  · subst M
    have hle : -(max |mobiusDivisorSquareRootAbelMoment 2 / 2| (B + (3 / 8 : ℝ) * max 0 C)) ≤
        -|mobiusDivisorSquareRootAbelMoment 2 / 2| := neg_le_neg (le_max_left _ _)
    exact hle.trans (by simpa using neg_abs_le (mobiusDivisorSquareRootAbelMoment 2 / 2))
  · have hM3 : 3 ≤ M := by omega
    have hMR : (0 : ℝ) < M := by positivity
    have hC' : completedSourceObserverJetNegativeHistoryAction M ≤ max 0 C * M := by
      exact (hC M hM3).trans (mul_le_mul_of_nonneg_right (le_max_right 0 C) hMR.le)
    have hlow : -(B + (3 / 8 : ℝ) * max 0 C) * (M : ℝ) ≤
        mobiusDivisorSquareRootAbelMoment M := by
      nlinarith [hB M hM3, hC']
    have hdiv : -(B + (3 / 8 : ℝ) * max 0 C) ≤ mobiusDivisorSquareRootAbelMoment M / M :=
      (le_div_iff₀ hMR).mpr hlow
    exact (neg_le_neg (le_max_right _ _)).trans hdiv

/-- **One-sided strip law for the positive observer-jet history action.** -/
theorem abs_re_sub_half_le_of_completedSourceObserverJetPositiveHistory_le_rpow
    {C c : ℝ} (_hC0 : 0 ≤ C)
    (hpos : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetPositiveHistoryAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  obtain ⟨K, hK2, hKle, hK0⟩ :
      ∃ K : ℝ, |mobiusDivisorSquareRootAbelMoment 2 / 2| ≤ K ∧
        B + (3 / 8 : ℝ) * C ≤ K ∧ 0 ≤ K :=
    ⟨max |mobiusDivisorSquareRootAbelMoment 2 / 2| (B + (3 / 8 : ℝ) * C),
      le_max_left _ _, le_max_right _ _,
      le_trans (abs_nonneg _) (le_max_left _ _)⟩
  refine abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow
    (C := K) (c := c) hK0 (fun M hM => ?_) q
  by_cases hM2 : M = 2
  · subst M
    have hle : mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) ≤ K := by
      calc mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ)
        _ = mobiusDivisorSquareRootAbelMoment 2 / 2 := by norm_num
        _ ≤ |mobiusDivisorSquareRootAbelMoment 2 / 2| := le_abs_self _
        _ ≤ K := hK2
    have hrc : 0 ≤ K * ((2 : ℕ) : ℝ) ^ c := mul_nonneg hK0 (Real.rpow_nonneg (by positivity) c)
    exact hle.trans (le_add_of_nonneg_right hrc)
  · clear hK2
    have hM3 : 3 ≤ M := by omega
    have hMR : (0 : ℝ) < M := by positivity
    have hrpow : (M : ℝ) ^ (1 + c) = (M : ℝ) ^ c * (M : ℝ) := by
      rw [Real.rpow_add hMR, Real.rpow_one, mul_comm]
    have hrc0 : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg hMR.le c
    have hCK : (3 / 8 : ℝ) * C ≤ K := by linarith [_hB0, hKle]
    have hcomb : mobiusDivisorSquareRootAbelMoment M ≤ (K + K * (M : ℝ) ^ c) * (M : ℝ) := by
      calc mobiusDivisorSquareRootAbelMoment M
        _ ≤ B * (M : ℝ) + (3 / 8 : ℝ) * (C * (M : ℝ) + C * (M : ℝ) ^ (1 + c)) := by
          linarith [hB M hM3, hpos M hM3]
        _ = (B + (3 / 8 : ℝ) * C) * (M : ℝ) + ((3 / 8 : ℝ) * C) * ((M : ℝ) ^ c * (M : ℝ)) := by
          rw [hrpow]; ring
        _ ≤ K * (M : ℝ) + K * ((M : ℝ) ^ c * (M : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_right hKle hMR.le)
            (mul_le_mul_of_nonneg_right hCK (mul_nonneg hrc0 hMR.le))
        _ = (K + K * (M : ℝ) ^ c) * (M : ℝ) := by ring
    exact (div_le_iff₀ hMR).mpr hcomb

/-- **One-sided strip law for the negative observer-jet history action.** -/
theorem abs_re_sub_half_le_of_completedSourceObserverJetNegativeHistory_le_rpow
    {C c : ℝ} (_hC0 : 0 ≤ C)
    (hneg : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetNegativeHistoryAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  obtain ⟨B, _hB0, hB⟩ := exists_mobiusDivisorSquareRootAbel_lower_negativeHistory
  obtain ⟨K, hK2, hKle, hK0⟩ :
      ∃ K : ℝ, |mobiusDivisorSquareRootAbelMoment 2 / 2| ≤ K ∧
        B + (3 / 8 : ℝ) * C ≤ K ∧ 0 ≤ K :=
    ⟨max |mobiusDivisorSquareRootAbelMoment 2 / 2| (B + (3 / 8 : ℝ) * C),
      le_max_left _ _, le_max_right _ _,
      le_trans (abs_nonneg _) (le_max_left _ _)⟩
  refine abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel
    (C := K) (c := c) hK0 (fun M hM => ?_) q
  by_cases hM2 : M = 2
  · subst M
    have hle : -K ≤ mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) := by
      calc -K
        _ ≤ -|mobiusDivisorSquareRootAbelMoment 2 / 2| := neg_le_neg hK2
        _ ≤ mobiusDivisorSquareRootAbelMoment 2 / 2 := neg_abs_le _
        _ = mobiusDivisorSquareRootAbelMoment 2 / (2 : ℕ) := by norm_num
    have hrc : 0 ≤ K * ((2 : ℕ) : ℝ) ^ c := mul_nonneg hK0 (Real.rpow_nonneg (by positivity) c)
    exact (neg_le_neg (le_add_of_nonneg_right hrc)).trans hle
  · clear hK2
    have hM3 : 3 ≤ M := by omega
    have hMR : (0 : ℝ) < M := by positivity
    have hrpow : (M : ℝ) ^ (1 + c) = (M : ℝ) ^ c * (M : ℝ) := by
      rw [Real.rpow_add hMR, Real.rpow_one, mul_comm]
    have hrc0 : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg hMR.le c
    have hCK : (3 / 8 : ℝ) * C ≤ K := by linarith [_hB0, hKle]
    have hup : (B + (3 / 8 : ℝ) * C) * (M : ℝ) + ((3 / 8 : ℝ) * C) * ((M : ℝ) ^ c * (M : ℝ)) ≤
        (K + K * (M : ℝ) ^ c) * (M : ℝ) := by
      calc (B + (3 / 8 : ℝ) * C) * (M : ℝ) + ((3 / 8 : ℝ) * C) * ((M : ℝ) ^ c * (M : ℝ))
        _ ≤ K * (M : ℝ) + K * ((M : ℝ) ^ c * (M : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_right hKle hMR.le)
            (mul_le_mul_of_nonneg_right hCK (mul_nonneg hrc0 hMR.le))
        _ = (K + K * (M : ℝ) ^ c) * (M : ℝ) := by ring
    have hcomb : -(K + K * (M : ℝ) ^ c) * (M : ℝ) ≤ mobiusDivisorSquareRootAbelMoment M := by
      calc -(K + K * (M : ℝ) ^ c) * (M : ℝ)
        _ = -((K + K * (M : ℝ) ^ c) * (M : ℝ)) := by ring
        _ ≤ -((B + (3 / 8 : ℝ) * C) * (M : ℝ) + ((3 / 8 : ℝ) * C) * ((M : ℝ) ^ c * (M : ℝ))) :=
          neg_le_neg hup
        _ = -(B * (M : ℝ) + (3 / 8 : ℝ) * (C * (M : ℝ) + C * (M : ℝ) ^ (1 + c))) := by
          rw [hrpow]; ring
        _ ≤ mobiusDivisorSquareRootAbelMoment M := by
          linarith [hB M hM3, hneg M hM3]
    exact (le_div_iff₀ hMR).mpr hcomb

/-- **Exact prime-free step cancellation between `completedPrimePolarGammaHarmonicCharge`
and `lagBracketSlope`.** -/
theorem completedPrimePolarGammaHarmonicCharge_sub_lagBracketSlope_diff (k : ℕ) :
    completedPrimePolarGammaHarmonicCharge k -
        (lagBracketSlope (k + 2) - lagBracketSlope (k + 1)) =
      2 * Real.eulerMascheroniConstant * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) -
        (1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))) := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  have hlag := lagBracketSlope_succ_sub (d := k + 1) (by omega)
  have hpsi : psiRemainder (k + 1) = Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1) := by
    rw [psiRemainder, chebyshevPsi_eq_psi]
    push_cast
    ring
  rw [completedPrimePolarGammaHarmonicCharge, hpsi]
  rw [show k + 1 + 1 = k + 2 by omega] at hlag
  push_cast at hlag
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at hlag
  rw [hlag]
  calc
    (Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1) + 2 * Real.eulerMascheroniConstant) *
          (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) -
        ((Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) +
          (1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)))) =
      (Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)) *
          ((1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) - 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) +
        2 * Real.eulerMascheroniConstant * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) -
        (1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))) := by ring
    _ = 2 * Real.eulerMascheroniConstant * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) -
        (1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))) := by
      rw [hgap, sub_self, mul_zero, zero_add]

theorem abs_completedPrimePolarGammaHarmonicCharge_sub_lagBracketSlope_diff_le (k : ℕ) :
    |completedPrimePolarGammaHarmonicCharge k -
        (lagBracketSlope (k + 2) - lagBracketSlope (k + 1))| ≤
      (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  have hgap0 : 0 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
    rw [hgap]
    positivity
  have hlog := abs_inv_succ_sub_log_le (d := k + 1) (by omega)
  push_cast at hlog
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring, ← hgap] at hlog
  rw [completedPrimePolarGammaHarmonicCharge_sub_lagBracketSlope_diff]
  calc
    |2 * Real.eulerMascheroniConstant * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) -
        (1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)))| ≤
      |2 * Real.eulerMascheroniConstant * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))| +
        |1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))| := abs_sub _ _
    _ = |2 * Real.eulerMascheroniConstant| * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) +
        |1 / ((k : ℝ) + 2) - Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))| := by
      rw [abs_mul, abs_of_nonneg hgap0]
    _ ≤ |2 * Real.eulerMascheroniConstant| * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) +
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := add_le_add le_rfl hlog
    _ = (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by ring

/-- Telescoping archimedean bound between `observerJetMass completedPrimePolarGammaHarmonicCharge`
increments and `lagBracketSlope` increments. -/
theorem abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le
    {k N : ℕ} (hkN : k ≤ N) :
    |(observerJetMass completedPrimePolarGammaHarmonicCharge N -
        observerJetMass completedPrimePolarGammaHarmonicCharge k) -
      (lagBracketSlope (N + 2) - lagBracketSlope (k + 2))| ≤
      (1 + |2 * Real.eulerMascheroniConstant|) *
        (1 / ((k : ℝ) + 2) - 1 / ((N : ℝ) + 2)) := by
  have hmass := observerJetMass_sub_eq_sum_Ico completedPrimePolarGammaHarmonicCharge hkN
  have hlag : lagBracketSlope (N + 2) - lagBracketSlope (k + 2) =
      ∑ i ∈ Finset.Ico (k + 1) (N + 1), (lagBracketSlope (i + 2) - lagBracketSlope (i + 1)) := by
    have htel := Finset.sum_Ico_sub (fun i : ℕ => lagBracketSlope (i + 1)) (show k + 1 ≤ N + 1 by omega)
    simpa only [show ∀ i : ℕ, i + 1 + 1 = i + 2 by intro i; omega] using htel.symm
  have hinv : 1 / ((k : ℝ) + 2) - 1 / ((N : ℝ) + 2) =
      ∑ i ∈ Finset.Ico (k + 1) (N + 1), (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
    have htel := Finset.sum_Ico_sub (fun i : ℕ => -1 / ((i : ℝ) + 1)) (show k + 1 ≤ N + 1 by omega)
    push_cast at htel
    calc
      1 / ((k : ℝ) + 2) - 1 / ((N : ℝ) + 2) =
        -1 / ((N : ℝ) + 1 + 1) - -1 / ((k : ℝ) + 1 + 1) := by ring
      _ = ∑ i ∈ Finset.Ico (k + 1) (N + 1), (-1 / ((i : ℝ) + 1 + 1) - -1 / ((i : ℝ) + 1)) :=
        htel.symm
      _ = ∑ i ∈ Finset.Ico (k + 1) (N + 1), (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hmass, hlag, ← Finset.sum_sub_distrib, hinv, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ =>
      abs_completedPrimePolarGammaHarmonicCharge_sub_lagBracketSlope_diff_le i)

/-- Exact representation of `completedSourceObserverJetHistory M j` as a tail sum of
`completedSourceObserverJetMass` increments. -/
theorem completedSourceObserverJetHistory_eq_sum_mass_sub
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3)) :
    completedSourceObserverJetHistory M j =
      ∑ k ∈ Finset.Ico (j + 1) (M - 2),
        (completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) := by
  have hj' : j < M - 3 := Finset.mem_range.mp hj
  unfold completedSourceObserverJetHistory completedSourceObserverJetMass
  rw [observerJetSecondHistory_residual_eq_sum_mass_sub
    completedPrimePolarGammaHarmonicCharge (M - 2) j (by omega) (by omega)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_sub_cancel]

/-- Tail history of `lagBracketSlope` matching `completedSourceObserverJetHistory M j`. -/
def lagBracketSlopeTailHistory (M j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico (j + 1) (M - 2), (lagBracketSlope M - lagBracketSlope (k + 2))

/-- Pointwise archimedean bound between `completedSourceObserverJetHistory M j` and
`lagBracketSlopeTailHistory M j`. -/
theorem abs_completedSourceObserverJetHistory_sub_lagBracketSlopeTailHistory_le
    {M j : ℕ} (hM : 3 ≤ M) (hj : j ∈ Finset.range (M - 3)) :
    |completedSourceObserverJetHistory M j - lagBracketSlopeTailHistory M j| ≤
      2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M := by
  rw [completedSourceObserverJetHistory_eq_sum_mass_sub hM hj,
    lagBracketSlopeTailHistory, ← Finset.sum_sub_distrib]
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico (j + 1) (M - 2)) :
      |(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
        (lagBracketSlope M - lagBracketSlope (k + 2))| ≤
      (1 + |2 * Real.eulerMascheroniConstant|) * (1 / Real.sqrt (k + 1 : ℕ)) := by
    have hk' : k < M - 2 := (Finset.mem_Ico.mp hk).2
    have h1 := abs_observerJetMass_completedHarmonic_sub_lagBracketSlope_sub_le
      (k := k) (N := M - 2) (by omega)
    rw [show M - 2 + 2 = M by omega] at h1
    change |(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
      (lagBracketSlope M - lagBracketSlope (k + 2))| ≤ _ at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hsub : 1 / ((k : ℝ) + 2) - 1 / ((M - 2 : ℕ) + 2 : ℝ) ≤ 1 / ((k : ℝ) + 2) := by
      have : (0 : ℝ) ≤ 1 / ((M - 2 : ℕ) + 2 : ℝ) := by positivity
      linarith
    refine hsub.trans ?_
    have hs : 0 < Real.sqrt (k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2) hs).mpr
    have hsq1 : Real.sqrt (k + 1 : ℕ) ≤ (k : ℝ) + 2 := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)]
      apply Real.sqrt_le_sqrt
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      nlinarith
    linarith
  have hsum_sqrt :
      (∑ k ∈ Finset.Ico (j + 1) (M - 2), (1 / Real.sqrt (k + 1 : ℕ))) ≤ 2 * Real.sqrt M := by
    have hsub : Finset.Ico (j + 1) (M - 2) ⊆ Finset.range M := by
      intro k hk
      rw [Finset.mem_range]
      have := (Finset.mem_Ico.mp hk).2
      omega
    calc
      (∑ k ∈ Finset.Ico (j + 1) (M - 2), (1 / Real.sqrt (k + 1 : ℕ))) ≤
          ∑ k ∈ Finset.range M, (1 / Real.sqrt (k + 1 : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 * Real.sqrt M := by
        have h := sum_one_div_sqrt_le M
        rw [sum_Icc_eq_sum_range_shift] at h
        simpa only using h
  calc
    |∑ k ∈ Finset.Ico (j + 1) (M - 2),
        ((completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
          (lagBracketSlope M - lagBracketSlope (k + 2)))| ≤
      ∑ k ∈ Finset.Ico (j + 1) (M - 2),
        |(completedSourceObserverJetMass M - completedSourceObserverJetMass (k + 2)) -
          (lagBracketSlope M - lagBracketSlope (k + 2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico (j + 1) (M - 2),
        (1 + |2 * Real.eulerMascheroniConstant|) * (1 / Real.sqrt (k + 1 : ℕ)) :=
      Finset.sum_le_sum hterm
    _ = (1 + |2 * Real.eulerMascheroniConstant|) *
        ∑ k ∈ Finset.Ico (j + 1) (M - 2), (1 / Real.sqrt (k + 1 : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 + |2 * Real.eulerMascheroniConstant|) * (2 * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hsum_sqrt (by positivity)
    _ = 2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M := by ring

/-- Positive-part and negative-part weighted tail actions of `lagBracketSlope`. -/
def lagBracketSlopePositiveTailAction (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3), max (lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

def lagBracketSlopeNegativeTailAction (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3), max (-lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)

private lemma abs_max_zero_sub_max_zero_le (a b : ℝ) :
    |max a 0 - max b 0| ≤ |a - b| := by
  rw [abs_le]
  have h1 : a - b ≤ |a - b| := le_abs_self (a - b)
  have h2 : -|a - b| ≤ a - b := neg_abs_le (a - b)
  have h0 : 0 ≤ |a - b| := abs_nonneg (a - b)
  constructor
  · have hb : max b 0 ≤ max a 0 + |a - b| :=
      max_le (by linarith [le_max_left a 0]) (by linarith [le_max_right a 0])
    linarith
  · have ha : max a 0 ≤ max b 0 + |a - b| :=
      max_le (by linarith [le_max_left b 0]) (by linarith [le_max_right b 0])
    linarith

/-- The positive observer-jet history action and `lagBracketSlopePositiveTailAction`
differ by at most `4 (1 + |2γ|) M`. -/
theorem abs_completedSourceObserverJetPositiveHistoryAction_sub_lagBracketSlope_le
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetPositiveHistoryAction M -
        lagBracketSlopePositiveTailAction M| ≤
      4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
  unfold completedSourceObserverJetPositiveHistoryAction lagBracketSlopePositiveTailAction
  rw [← Finset.sum_sub_distrib]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (M - 3)) :
      |max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
        max (lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)| ≤
      (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
        (1 / Real.sqrt (j + 1 : ℕ)) := by
    have hs : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hdiff := abs_completedSourceObserverJetHistory_sub_lagBracketSlopeTailHistory_le hM hj
    have hmax := abs_max_zero_sub_max_zero_le
      (completedSourceObserverJetHistory M j) (lagBracketSlopeTailHistory M j)
    rw [← sub_div, abs_div, abs_of_pos hs, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hmax.trans hdiff) (by positivity)
  have hsum_j :
      (∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ))) ≤ 2 * Real.sqrt M := by
    have hsub : Finset.range (M - 3) ⊆ Finset.range M :=
      Finset.range_mono (Nat.sub_le M 3)
    calc
      (∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ))) ≤
          ∑ j ∈ Finset.range M, (1 / Real.sqrt (j + 1 : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 * Real.sqrt M := by
        have h := sum_one_div_sqrt_le M
        rw [sum_Icc_eq_sum_range_shift] at h
        simpa only using h
  calc
    |∑ j ∈ Finset.range (M - 3),
        (max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
          max (lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ))| ≤
      ∑ j ∈ Finset.range (M - 3),
        |max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
          max (lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (M - 3),
        (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
          (1 / Real.sqrt (j + 1 : ℕ)) := Finset.sum_le_sum hterm
    _ = (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
        ∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) * (2 * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hsum_j (by positivity)
    _ = 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (Real.sqrt M * Real.sqrt M) := by ring
    _ = 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg M)]

/-- The negative observer-jet history action and `lagBracketSlopeNegativeTailAction`
differ by at most `4 (1 + |2γ|) M`. -/
theorem abs_completedSourceObserverJetNegativeHistoryAction_sub_lagBracketSlope_le
    {M : ℕ} (hM : 3 ≤ M) :
    |completedSourceObserverJetNegativeHistoryAction M -
        lagBracketSlopeNegativeTailAction M| ≤
      4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
  unfold completedSourceObserverJetNegativeHistoryAction lagBracketSlopeNegativeTailAction
  rw [← Finset.sum_sub_distrib]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (M - 3)) :
      |max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
        max (-lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)| ≤
      (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
        (1 / Real.sqrt (j + 1 : ℕ)) := by
    have hs : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hdiff := abs_completedSourceObserverJetHistory_sub_lagBracketSlopeTailHistory_le hM hj
    have hmax : |max (-completedSourceObserverJetHistory M j) 0 -
        max (-lagBracketSlopeTailHistory M j) 0| ≤
        |completedSourceObserverJetHistory M j - lagBracketSlopeTailHistory M j| := by
      have h := abs_max_zero_sub_max_zero_le
        (-completedSourceObserverJetHistory M j) (-lagBracketSlopeTailHistory M j)
      simpa only [neg_sub_neg, abs_sub_comm] using h
    rw [← sub_div, abs_div, abs_of_pos hs, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hmax.trans hdiff) (by positivity)
  have hsum_j :
      (∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ))) ≤ 2 * Real.sqrt M := by
    have hsub : Finset.range (M - 3) ⊆ Finset.range M :=
      Finset.range_mono (Nat.sub_le M 3)
    calc
      (∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ))) ≤
          ∑ j ∈ Finset.range M, (1 / Real.sqrt (j + 1 : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 * Real.sqrt M := by
        have h := sum_one_div_sqrt_le M
        rw [sum_Icc_eq_sum_range_shift] at h
        simpa only using h
  calc
    |∑ j ∈ Finset.range (M - 3),
        (max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
          max (-lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ))| ≤
      ∑ j ∈ Finset.range (M - 3),
        |max (-completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ) -
          max (-lagBracketSlopeTailHistory M j) 0 / Real.sqrt (j + 1 : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (M - 3),
        (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
          (1 / Real.sqrt (j + 1 : ℕ)) := Finset.sum_le_sum hterm
    _ = (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) *
        ∑ j ∈ Finset.range (M - 3), (1 / Real.sqrt (j + 1 : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * (1 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt M) * (2 * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hsum_j (by positivity)
    _ = 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (Real.sqrt M * Real.sqrt M) := by ring
    _ = 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg M)]

/-- **Linear bound on `lagBracketSlopePositiveTailAction` implies RH.** -/
theorem riemannHypothesis_of_lagBracketSlopePositiveTailAction_linear
    {C : ℝ} (hC : ∀ M : ℕ, 3 ≤ M → lagBracketSlopePositiveTailAction M ≤ C * M) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_completedSourceObserverJetPositiveHistory_linear
    (C := C + 4 * (1 + |2 * Real.eulerMascheroniConstant|))
  intro M hM
  have h1 := (abs_le.mp
    (abs_completedSourceObserverJetPositiveHistoryAction_sub_lagBracketSlope_le hM)).2
  have h2 := hC M hM
  linarith

/-- **Linear bound on `lagBracketSlopeNegativeTailAction` implies RH.** -/
theorem riemannHypothesis_of_lagBracketSlopeNegativeTailAction_linear
    {C : ℝ} (hC : ∀ M : ℕ, 3 ≤ M → lagBracketSlopeNegativeTailAction M ≤ C * M) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_completedSourceObserverJetNegativeHistory_linear
    (C := C + 4 * (1 + |2 * Real.eulerMascheroniConstant|))
  intro M hM
  have h1 := (abs_le.mp
    (abs_completedSourceObserverJetNegativeHistoryAction_sub_lagBracketSlope_le hM)).2
  have h2 := hC M hM
  linarith

/-- **One-sided strip law for `lagBracketSlopePositiveTailAction`.** -/
theorem abs_re_sub_half_le_of_lagBracketSlopePositiveTailAction_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hpos : ∀ M : ℕ, 3 ≤ M →
      lagBracketSlopePositiveTailAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let K : ℝ := C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)
  have hK0 : 0 ≤ K := by positivity
  refine abs_re_sub_half_le_of_completedSourceObserverJetPositiveHistory_le_rpow
    (C := K) (c := c) hK0 (fun M hM => ?_) q
  have h1 := (abs_le.mp
    (abs_completedSourceObserverJetPositiveHistoryAction_sub_lagBracketSlope_le hM)).2
  have h2 := hpos M hM
  have hrc : 0 ≤ (M : ℝ) ^ (1 + c) := Real.rpow_nonneg (Nat.cast_nonneg M) (1 + c)
  have h4 : 0 ≤ 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) ^ (1 + c) := by
    positivity
  change completedSourceObserverJetPositiveHistoryAction M ≤
    (C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)) * (M : ℝ) +
      (C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)) * (M : ℝ) ^ (1 + c)
  linarith

/-- **One-sided strip law for `lagBracketSlopeNegativeTailAction`.** -/
theorem abs_re_sub_half_le_of_lagBracketSlopeNegativeTailAction_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hneg : ∀ M : ℕ, 3 ≤ M →
      lagBracketSlopeNegativeTailAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c))
    (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  let K : ℝ := C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)
  have hK0 : 0 ≤ K := by positivity
  refine abs_re_sub_half_le_of_completedSourceObserverJetNegativeHistory_le_rpow
    (C := K) (c := c) hK0 (fun M hM => ?_) q
  have h1 := (abs_le.mp
    (abs_completedSourceObserverJetNegativeHistoryAction_sub_lagBracketSlope_le hM)).2
  have h2 := hneg M hM
  have h4 : 0 ≤ 4 * (1 + |2 * Real.eulerMascheroniConstant|) * (M : ℝ) ^ (1 + c) := by
    positivity
  change completedSourceObserverJetNegativeHistoryAction M ≤
    (C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)) * (M : ℝ) +
      (C + 4 * (1 + |2 * Real.eulerMascheroniConstant|)) * (M : ℝ) ^ (1 + c)
  linarith

end

end GaloisForLFunctions.RHTower
