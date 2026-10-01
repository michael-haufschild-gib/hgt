import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementBound
import GaloisForLFunctions.RHTower.SteinhausModel

open MeasureTheory Complex Finset
noncomputable section
namespace RHTower

/-- The complete coefficient-faithful complementary series with the reciprocal character. -/
def steinhausFullReflectedComplement (d tau N : ℝ) (ω : SteinhausModel.Omega) : ℂ :=
  ∑' n : ℕ, smoothAFEZetaRightComplementCoefficient d tau N n *
    starRingEnd ℂ (SteinhausModel.X (n + 1) ω)

/-- Absolute admission of the complete twisted complement at conductor-sized smoothing. -/
theorem summable_norm_steinhausReflectedComplement
    {d N tau : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hN : 1 ≤ N) (hNt : N ≤ tau) (htN : tau ≤ 2 * N) (ω : SteinhausModel.Omega) :
    Summable (fun n : ℕ => ‖smoothAFEZetaRightComplementCoefficient d tau N n *
      starRingEnd ℂ (SteinhausModel.X (n + 1) ω)‖) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_reflectedComplementCoefficient_le_conductor hd hdhalf
  have hmajor := (summable_smoothAFEZetaMajorant (p := (9 / 2 : ℝ)) (by norm_num)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hmajor
  simpa only [norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
    hbound N hN tau hNt htN n

/-- Uniform all-phase bound for the complete original complementary series. -/
theorem exists_norm_steinhausFullReflectedComplement_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ tau : ℝ, N ≤ tau → tau ≤ 2 * N →
      ∀ ω : SteinhausModel.Omega, ‖steinhausFullReflectedComplement d tau N ω‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_reflectedComplementCoefficient_le_conductor hd hdhalf
  let M := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  have hM : 0 ≤ M := tsum_nonneg (fun _ => by positivity)
  refine ⟨C * M, mul_nonneg hC hM, fun N hN tau hNt htN ω => ?_⟩
  have hnorm := summable_norm_steinhausReflectedComplement hd hdhalf hN hNt htN ω
  have hmajor := (summable_smoothAFEZetaMajorant (p := (9 / 2 : ℝ)) (by norm_num)).mul_left C
  calc
    _ ≤ ∑' n : ℕ, ‖smoothAFEZetaRightComplementCoefficient d tau N n *
          starRingEnd ℂ (SteinhausModel.X (n + 1) ω)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      apply hnorm.tsum_le_tsum _ hmajor
      intro n
      simpa only [norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
        hbound N hN tau hNt htN n
    _ = C * M := by rw [tsum_mul_left]

/-- A fixed cutoff controls the complete original complementary tail uniformly in all phases,
smoothing scales and heights in the conductor window. -/
theorem exists_norm_steinhausReflectedComplement_sub_head_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℝ, 1 ≤ N → ∀ tau : ℝ, N ≤ tau → tau ≤ 2 * N →
      ∀ ω : SteinhausModel.Omega, ∀ L : ℕ, 1 ≤ L →
      ‖(∑' n : ℕ, smoothAFEZetaRightComplementCoefficient d tau N n * starRingEnd ℂ (SteinhausModel.X (n + 1) ω)) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaRightComplementCoefficient d tau N n * starRingEnd ℂ (SteinhausModel.X (n + 1) ω)‖ ≤
        D *
          ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  obtain ⟨D, hD, hpoint⟩ :=
    exists_norm_reflectedComplementCoefficient_le_conductor hd hdhalf
  refine ⟨D, hD, fun N hN tau hNt htN ω L hL => ?_⟩
  let f : ℕ → ℂ := fun n =>
    smoothAFEZetaRightComplementCoefficient d tau N n * starRingEnd ℂ (SteinhausModel.X (n + 1) ω)
  let A : ℝ := D
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    have hbase := summable_smoothAFEZetaMajorant
      (p := (9 / 2 : ℝ)) (by norm_num)
    have hmajor : Summable (fun n : ℕ =>
        A * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) := hbase.mul_left A
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      dsimp only [f, A]
      simpa only [norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
        hpoint N hN tau hNt htN n) hmajor
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [show (fun n : ℕ =>
      smoothAFEZetaRightComplementCoefficient d tau N n * starRingEnd ℂ (SteinhausModel.X (n + 1) ω)) = f by rfl, heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hp : (-(9 / 2 : ℝ)) < -1 := by norm_num
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) := by
    have hbase := Real.summable_nat_rpow.mpr hp
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) :=
    hpow.mul_left A
  calc
    ‖∑' j : ℕ, f (j + L)‖ ≤
        ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ,
        A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun j => by
        have h := hpoint N hN tau hNt htN (j + L)
        have hcast :
            ((j + L : ℕ) : ℝ) + 1 = ((j + L + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast] at h
        rw [one_div, ← Real.rpow_neg (by positivity :
          (0 : ℝ) ≤ ((j + L + 1 : ℕ) : ℝ))] at h
        simpa only [f, A, norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one,
          Nat.cast_add, Nat.cast_one, add_assoc] using h)
        hnormTail hmajor
    _ = A * ∑' j : ℕ,
        (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ ((1 : ℝ) - 9 / 2) / ((9 : ℝ) / 2 - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le
          (show (1 : ℝ) < 9 / 2 by norm_num) hL)
        (by dsimp only [A]; positivity)
    _ = D *
        ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
      dsimp only [A]
      ring_nf

end RHTower
