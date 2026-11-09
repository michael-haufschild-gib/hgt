import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatorySublevelCover

/-!
# Exponentially shrinking covers of exceptional sampling bases

On a compact interval of positive bases, the times at level `n+1` occupy only linearly many
fixed-radius windows. Uniform local power-law covers therefore give linearly many balls with
exponentially shrinking radii for the bases at which that level is exponentially small.
-/

open Set Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Local finite sublevel covers become linear-cardinality, exponentially shrinking covers
of exceptional bases at each sampling level. -/
theorem exists_exponential_sampled_sublevel_covers {f : ℝ → ℂ} {k : ℕ} {r K p : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hp : 0 < p)
    (hsub : ∀ x ε : ℝ, 0 < ε → ∃ T : Finset ℝ, T.card ≤ k ∧
      ∀ y ∈ Ioo (x - r) (x + r), ‖f y‖ < ε → ∃ z ∈ T, |y - z| ≤ K * ε ^ p)
    {L U δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    ∃ M R b : ℝ, 0 < M ∧ 0 < R ∧ 0 < b ∧ ∀ n : ℕ,
      ∃ T : Finset ℝ, (T.card : ℝ) ≤ M * ((n : ℝ) + 1) ∧
        ∀ ℓ ∈ Icc L U, ‖f (((n : ℝ) + 1) * ℓ)‖ ≤
          Real.exp (-δ * (((n : ℝ) + 1) * ℓ)) →
          ∃ z ∈ T, |ℓ - z| ≤ R * Real.exp (-b * n) := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_gt (max (U / r) 0)
  have hBU : U < (B : ℝ) * r :=
    (div_lt_iff₀ hr).mp ((le_max_left _ _).trans_lt hB)
  let R : ℝ := K * (2 : ℝ) ^ p
  let b : ℝ := δ * L * p
  refine ⟨(B : ℝ) * k + 1, R, b, by positivity, by dsimp [R]; positivity,
    mul_pos (mul_pos hδ hL) hp, fun n => ?_⟩
  let ν : ℝ := (n : ℝ) + 1
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hν1 : 1 ≤ ν := by
    dsimp [ν]
    linarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  let ε : ℝ := 2 * Real.exp (-δ * (ν * L))
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose S hSc hScover using fun j : ℕ => hsub (((j : ℝ) + 1 / 2) * r) ε hε
  let V : Finset ℝ := (range ((n + 1) * B)).biUnion S
  let T : Finset ℝ := V.image (fun z => z / ν)
  have hcard : T.card ≤ ((n + 1) * B) * k := by
    calc T.card ≤ V.card := card_image_le
      _ ≤ ∑ j ∈ range ((n + 1) * B), (S j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ range ((n + 1) * B), k := sum_le_sum fun j _ => hSc j
      _ = ((n + 1) * B) * k := by simp
  refine ⟨T, ?_, fun ℓ hℓ hsmall => ?_⟩
  · have hcast : (T.card : ℝ) ≤ ν * B * k := by
      dsimp only [ν]
      exact_mod_cast hcard
    dsimp [ν] at hcast
    nlinarith only [hcast, show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  · have hℓ0 : 0 < ℓ := hL.trans_le hℓ.1
    let j : ℕ := ⌊ν * ℓ / r⌋₊
    have hleft : (j : ℝ) * r ≤ ν * ℓ :=
      (le_div_iff₀ hr).mp (Nat.floor_le (by positivity : 0 ≤ ν * ℓ / r))
    have hright : ν * ℓ < ((j : ℝ) + 1) * r :=
      (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (ν * ℓ / r))
    have hj : j < (n + 1) * B := by
      have hjR : (j : ℝ) < ν * B := by
        apply (mul_lt_mul_iff_left₀ hr).mp
        calc (j : ℝ) * r ≤ ν * ℓ := hleft
          _ ≤ ν * U := mul_le_mul_of_nonneg_left hℓ.2 hν.le
          _ < ν * ((B : ℝ) * r) := mul_lt_mul_of_pos_left hBU hν
          _ = (ν * B) * r := by ring
      dsimp only [ν] at hjR
      exact_mod_cast hjR
    have hwindow : ν * ℓ ∈ Ioo (((j : ℝ) + 1 / 2) * r - r)
        (((j : ℝ) + 1 / 2) * r + r) :=
      ⟨by nlinarith only [hleft, hr], by nlinarith only [hright, hr]⟩
    have hval : ‖f (ν * ℓ)‖ < ε := by
      have he : Real.exp (-δ * (ν * ℓ)) ≤ Real.exp (-δ * (ν * L)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
          (mul_le_mul_of_nonneg_left hℓ.1 hν.le) (neg_nonpos.mpr hδ.le))
      exact hsmall.trans_lt (he.trans_lt (by dsimp [ε]; linarith [Real.exp_pos (-δ * (ν * L))]))
    obtain ⟨z, hz, hdist⟩ := hScover j (ν * ℓ) hwindow hval
    refine ⟨z / ν, mem_image.mpr ⟨z, mem_biUnion.mpr ⟨j, mem_range.mpr hj, hz⟩, rfl⟩, ?_⟩
    have hscale : |ℓ - z / ν| = |ν * ℓ - z| / ν := by
      rw [show ℓ - z / ν = (ν * ℓ - z) / ν by field_simp,
        abs_div, abs_of_pos hν]
    have hradius : K * ε ^ p ≤ R * Real.exp (-b * n) := by
      dsimp [ε, R, b]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le, ← Real.exp_mul,
        ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      dsimp [ν]
      nlinarith only [mul_pos (mul_pos hδ hL) hp]
    rw [hscale]
    exact (div_le_self (abs_nonneg _) hν1).trans (hdist.trans hradius)

#print axioms exists_exponential_sampled_sublevel_covers

end GaloisForLFunctions.InfiniteRankWeilTheory
