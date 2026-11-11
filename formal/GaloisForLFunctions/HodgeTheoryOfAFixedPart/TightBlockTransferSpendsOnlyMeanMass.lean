import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustCombDirectionsTransferToStepPackets

/-!
# Tight block transfer spends only mean mass

The block scale may be arbitrarily large. Padding `(N,QN]` into
`(Q-1)R+1` complete blocks loses only `1/R` in its ratio. Both the Schur
error and the uniform packet error are charged to block means, so every
negative direction survives in a slightly mass-shifted step form.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-- Arbitrarily fine fixed block scales retain the mean-only Schur error. -/
theorem exists_large_blockScale_combForm_ge_blockMean (Q R₀ : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, R₀ ≤ R ∧ 0 < R ∧
      ∀ N J : ℕ, R ≤ N → N + N / R * J ≤ Q * N → ∀ c : ℕ → ℝ,
        combForm (Ioc N (N + N / R * J))
            (fun n => blockMean N (N / R) J c (blockIndex N (N / R) n)) -
          ε * ∑ n ∈ Ioc N (N + N / R * J),
            blockMean N (N / R) J c (blockIndex N (N / R) n) ^ 2 ≤
        combForm (Ioc N (N + N / R * J)) c := by
  let E := 3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi) +
    crossConstant Q ^ 2 / ε
  let R := max R₀ ⌈Real.exp E⌉₊
  have hR : 0 < R := (Nat.ceil_pos.mpr (Real.exp_pos E)).trans_le (le_max_right _ _)
  have hlog : E ≤ Real.log (R : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hR)]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right R₀ ⌈Real.exp E⌉₊))
  refine ⟨R, le_max_left _ _, hR, fun N J hRN hQ c => ?_⟩
  have hB : 0 < N / R := Nat.div_pos hRN hR
  have hm := log_sub_row_ge (M := N / R * J) hR hRN hQ
  have hμ : crossConstant Q ^ 2 / ε ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * (N / R)) + 2 + ((N / R * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q) := by
    dsimp only [E] at hlog
    linarith only [hm, hlog]
  have h := combForm_blockFunction_add_ge hB (Nat.div_le_self _ _) hQ hε hμ
    (blockMean N (N / R) J c)
    (fun n => c n - blockMean N (N / R) J c (blockIndex N (N / R) n))
    (sum_filter_sub_blockMean hB N J c)
  have he : (fun n => blockMean N (N / R) J c (blockIndex N (N / R) n) +
      (c n - blockMean N (N / R) J c (blockIndex N (N / R) n))) = c := by
    funext n
    ring
  rwa [he] at h

/-- Tight padding and block convergence transfer the full comb into a
step form with an arbitrarily small error on mean mass alone. -/
theorem exists_tight_block_transfer (Q R₀ : ℕ) (hQ : 1 ≤ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, R₀ ≤ R ∧ 0 < R ∧ ∀ᶠ N : ℕ in atTop, 0 < N / R ∧
      ∀ c : ℕ → ℝ,
        let σ := blockMean (R * (N / R)) (N / R) ((Q - 1) * R + 1)
          (fun n => if n ∈ Ioc N (Q * N) then c n else 0)
        (N / R : ℕ) * (packetForm (Q + 1) (stepPacket R ((Q - 1) * R + 1) σ) -
          ε * ∑ j ∈ range ((Q - 1) * R + 1), σ j ^ 2) ≤ combForm (Ioc N (Q * N)) c := by
  obtain ⟨R, hR₀, hR, hred⟩ :=
    exists_large_blockScale_combForm_ge_blockMean (Q + 1) R₀ (half_pos hε)
  let J := (Q - 1) * R + 1
  have hRJ : R + J = Q * R + 1 := by
    calc R + J = ((Q - 1) + 1) * R + 1 := by dsimp only [J]; ring
      _ = Q * R + 1 := by rw [Nat.sub_add_cancel hQ]
  have hcap : R + J ≤ (Q + 1) * R := by rw [hRJ]; nlinarith only [hR]
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    (eventually_packetForm_stepPacket_le_combForm hR hcap (half_pos hε))
  refine ⟨R, hR₀, hR, eventually_atTop.mpr ⟨R * (B₀ + Q * R + 1), fun N hN => ?_⟩⟩
  have hBbig : B₀ + Q * R + 1 ≤ N / R :=
    (Nat.le_div_iff_mul_le hR).mpr (by rw [Nat.mul_comm]; exact hN)
  have hB : 0 < N / R := by omega
  refine ⟨hB, fun c => ?_⟩
  have hNle : R * (N / R) ≤ N := Nat.mul_div_le N R
  have hNlt : N ≤ R * (N / R) + R := by
    have h := Nat.lt_mul_div_succ N hR
    linarith only [h]
  have hsub : Ioc N (Q * N) ⊆ Ioc (R * (N / R)) (R * (N / R) + N / R * J) := by
    apply Finset.Ioc_subset_Ioc hNle
    have he : R * (N / R) + N / R * J = (N / R) * (Q * R + 1) := by
      rw [← hRJ]
      ring
    rw [he]
    have h := Nat.mul_le_mul_left Q hNlt
    nlinarith only [h, hBbig]
  let d := fun n => if n ∈ Ioc N (Q * N) then c n else 0
  let σ := blockMean (R * (N / R)) (N / R) J d
  have hform : combForm (Ioc (R * (N / R)) (R * (N / R) + N / R * J)) d =
      combForm (Ioc N (Q * N)) c :=
    (combForm_of_subset hsub fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hdiv : R * (N / R) / R = N / R := Nat.mul_div_cancel_left (N / R) hR
  have hRB : R ≤ R * (N / R) := Nat.le_mul_of_pos_right R hB
  have hcap' : R * (N / R) + N / R * J ≤ (Q + 1) * (R * (N / R)) := by
    nlinarith only [Nat.mul_le_mul_right (N / R) hcap]
  have h₁ := hred (R * (N / R)) J hRB (by rw [hdiv]; exact hcap') d
  rw [hdiv, hform] at h₁
  have h₂ := hB₀ (N / R) (by omega) σ
  rw [sum_blockFunction_sq hB σ] at h₂
  change combForm _ (fun n => σ (blockIndex _ _ n)) -
    (ε / 2) * ∑ n ∈ Ioc (R * (N / R)) (R * (N / R) + N / R * J),
      σ (blockIndex (R * (N / R)) (N / R) n) ^ 2 ≤ _ at h₁
  rw [sum_blockFunction_sq hB σ] at h₁
  change (N / R : ℕ) * (packetForm (Q + 1) (stepPacket R J σ) -
    ε * ∑ j ∈ range J, σ j ^ 2) ≤ _
  nlinarith only [h₁, h₂]

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
