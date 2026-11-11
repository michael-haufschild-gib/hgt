import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets

/-!
# Robust negative comb directions survive block averaging

The uniform limit of block-constant forms, combined with the block-average
inequality, transfers every direction with a fixed negative mass margin
to one fixed finite-dimensional space of step packets.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-- Uniform convergence of the block forms, measured in coefficient mass. -/
theorem eventually_packetForm_stepPacket_le_combForm
    {R J Q : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      B * packetForm Q (stepPacket R J σ) ≤
        combForm (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) +
          ε * ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 := by
  have hev := eventually_abs_combForm_nested_sub_le (s := range (J + 1))
    (x := fun j => R + j) (X := R + J) (Q := Q) hR (nested_bounds R J) hQ
    (η := ε / 4) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with B hB hB1 σ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB1
  have h := hB (nestedCoeff J σ)
  have hwin : (R + J) * B = R * B + B * J := by ring
  have hc : combForm (Ioc (R * B) (R * B + B * J)) (fun n => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n) =
      combForm (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) :=
    (combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn).symm
  rw [hwin, hc, ← stepPacket_eq_nested hR J σ] at h
  have hsq := sum_nestedCoeff_sq_le J σ
  have hlow : packetForm Q (stepPacket R J σ) - ε * ∑ j ∈ range J, σ j ^ 2 ≤
      combForm (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B := by
    have hl := (abs_le.mp h).1
    have he := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε / 4 by positivity)
    nlinarith only [hl, he]
  have hm := (le_div_iff₀ hB0).mp hlow
  rw [sum_blockFunction_sq (by omega) σ]
  nlinarith only [hm]

/-- For a fixed window and margin, a single block count transfers the full
comb form to step packets, uniformly over every coefficient vector. -/
theorem exists_block_transfer_to_stepPacket (K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ N : ℕ in atTop, 0 < N / R ∧ ∀ c : ℕ → ℝ,
      (N / R : ℕ) * packetForm (6 * K + 2)
        (stepPacket R ((6 * K + 1) * R)
          (blockMean (R * (N / R)) (N / R) ((6 * K + 1) * R)
            (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0))) ≤
      combForm (Ioc N (N + 3 * K * N)) c +
        η * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 := by
  obtain ⟨R, hR, hred⟩ := exists_blockSize_combForm_ge_blockMean (6 * K + 2) (half_pos hη)
  have hQ : R + (6 * K + 1) * R ≤ (6 * K + 2) * R := le_of_eq (by ring)
  have hev := eventually_packetForm_stepPacket_le_combForm hR hQ (half_pos hη)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hev
  refine ⟨R, hR, eventually_atTop.mpr ⟨R * (B₀ + 1), fun N hN => ?_⟩⟩
  have hB1 : B₀ + 1 ≤ N / R := (Nat.le_div_iff_mul_le hR).mpr (by rw [Nat.mul_comm]; exact hN)
  have hBpos : 0 < N / R := by omega
  refine ⟨hBpos, fun c => ?_⟩
  have hNle : R * (N / R) ≤ N := Nat.mul_div_le N R
  have hNlt : N ≤ R * (N / R) + R := by
    have := Nat.lt_mul_div_succ N hR
    linarith
  have hRB : R ≤ R * (N / R) := Nat.le_mul_of_pos_right R hBpos
  have hsub : Ioc N (N + 3 * K * N) ⊆
      Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)) := by
    refine Finset.Ioc_subset_Ioc hNle ?_
    have h1 := Nat.mul_le_mul_left (3 * K + 1) hNlt
    have h2 := Nat.mul_le_mul_left (3 * K + 1) hRB
    linarith
  have hform : combForm (Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)))
        (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0) =
      combForm (Ioc N (N + 3 * K * N)) c :=
    (combForm_of_subset hsub fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hsq : ∑ n ∈ Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)),
        (if n ∈ Ioc N (N + 3 * K * N) then c n else 0) ^ 2 =
      ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 := by
    rw [← Finset.sum_subset hsub fun n _ hn => by rw [if_neg hn]; ring]
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]
  have hdiv : R * (N / R) / R = N / R := Nat.mul_div_cancel_left (N / R) hR
  have h1 := hred (R * (N / R)) ((6 * K + 1) * R) hRB
    (by rw [hdiv]; exact le_of_eq (by ring))
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hdiv, hform, hsq] at h1
  have h2 := hB₀ (N / R) (by omega)
    (blockMean (R * (N / R)) (N / R) ((6 * K + 1) * R)
      (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0))
  have h3 := sum_blockMean_sq_le hBpos (R * (N / R)) ((6 * K + 1) * R)
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hsq] at h3
  have h4 := mul_le_mul_of_nonneg_left h3 (half_pos hη).le
  linarith only [h1, h2, h4]

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
