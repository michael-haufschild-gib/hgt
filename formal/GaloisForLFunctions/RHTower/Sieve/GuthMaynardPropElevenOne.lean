import GaloisForLFunctions.RHTower.Sieve.GuthMaynardEnergySmallGcd
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardEnergyLargeGcd
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSelfBound

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 11.1: the energy bound

Let `D(t) = Σ_{N<n≤2N} b_n n^{it}` with `|b_n| ≤ 1`, and let `W` be a `1`-separated set in an
interval of length `T` with `|D(t)| ≥ N^σ` on `W`. If `T^{3/4} ≤ N ≤ T` (Guth–Maynard,
arXiv 2405.20552, Proposition 11.1), unconditionally:

`E(W) ⪅ |W| N^{4−4σ} + |W|^{21/8} T^{1/4} N^{1−2σ} + |W|³ N^{1−2σ}`.

Proof. Lemma 11.4 bounds `E(W)` by `N^{−2σ} Σ_{n₁,n₂ ∼ N} |R(n₁/n₂)|³`; split by `gcd ≤ N²/T`
(Lemma 11.8, `DT + N² = 2N²`) or `gcd ≥ N²/T` (Lemma 11.9). This gives
`E ≤ α + β E^{1/2}` with `α ⪅ N^{1−2σ}(|W|³ + T^{1/4}|W|^{21/8})` and `β ⪅ N^{2−2σ}|W|^{1/2}`, and
`E ≤ 2α + β²` (corpus `Sieve.le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul`).
-/

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-- The final collection of Proposition 11.1 over abstract reals: a bootstrap bound at the half
exponent is absorbed into the full one.  Split out to keep each declaration inside the default
elaboration budget. -/
theorem propElevenOne_collect {E K Tε Tε₁ Q₁ Q₂ Q₃ : ℝ} (hK : 0 ≤ K) (hTε : 0 ≤ Tε)
    (hTle : Tε₁ ≤ Tε) (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hQ₃ : 0 ≤ Q₃)
    (hboot : E ≤ 2 * K * Tε₁ * (Q₃ + Q₂) + 9 * K ^ 2 * Tε * Q₁) :
    E ≤ (2 * K + 9 * K ^ 2) * Tε * (Q₁ + Q₂ + Q₃) := by
  have h23 : (0 : ℝ) ≤ Q₃ + Q₂ := by linarith
  have hKK : 2 * K * Tε₁ ≤ 2 * K * Tε := by nlinarith
  have hstep : 2 * K * Tε₁ * (Q₃ + Q₂) ≤ 2 * K * Tε * (Q₃ + Q₂) :=
    mul_le_mul_of_nonneg_right hKK h23
  have t1 : (0 : ℝ) ≤ 2 * K * Tε * Q₁ := mul_nonneg (mul_nonneg (by linarith) hTε) hQ₁
  have t2 : (0 : ℝ) ≤ 9 * K ^ 2 * Tε * Q₂ := mul_nonneg (mul_nonneg (by positivity) hTε) hQ₂
  have t3 : (0 : ℝ) ≤ 9 * K ^ 2 * Tε * Q₃ := mul_nonneg (mul_nonneg (by positivity) hTε) hQ₃
  nlinarith [hboot, hstep, t1, t2, t3]

/-- **Guth–Maynard Proposition 11.1** (bound for the energy), unconditionally: for every `ε > 0`
there is `C ≥ 0` such that for `T ≥ 2`, `T^{3/4} ≤ N ≤ T`, `|b_n| ≤ 1` and every `1`-separated
`W ⊆ [T₀, T₀ + T]` with `|D(t)| ≥ N^σ` on `W`:
`E(W) ≤ C T^ε (|W| N^{4−4σ} + |W|^{21/8} T^{1/4} N^{1−2σ} + |W|³ N^{1−2σ})`. -/
theorem guthMaynard_prop111 {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (σ : ℝ) (W : Finset ℝ) (T T₀ : ℝ),
      2 ≤ T → T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicDirichletPoly N b t‖) →
      (additiveEnergy W : ℝ) ≤ C * T ^ ε *
        ((W.card : ℝ) * (N : ℝ) ^ (4 - 4 * σ) +
          (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) +
          (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ)) := by
  classical
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = ε / 2 := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  obtain ⟨C₈, hC₈, h118⟩ := guthMaynard_lemma118 hε₁0
  obtain ⟨C₉, hC₉, h119⟩ := guthMaynard_lemma119 hε₁0
  set c₄ := energyThirdMomentConst
  have hc₄ : 0 ≤ c₄ := energyThirdMomentConst_nonneg
  set K := c₄ * (2 * C₈ + C₉) with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨2 * K + 9 * K ^ 2, by positivity, fun N b σ W T T₀ hT hNT hNle hb hW hsep hD => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hNT
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set X : ℝ := (W.card : ℝ)
  set E : ℝ := (additiveEnergy W : ℝ)
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  set P := Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)
  set F : ℕ × ℕ → ℝ := fun p => ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3
  set D : ℝ := (N : ℝ) ^ 2 / T
  have hD0 : 0 ≤ D := by positivity
  have hDT : D * T = (N : ℝ) ^ 2 := by simp only [D]; field_simp
  -- Lemma 11.4
  have h114 := additiveEnergy_le_discreteThirdMoment hN1 hb hsep hD
  rw [← sum_product'] at h114
  -- split the third moment by the gcd
  have hsplit := sum_filter_add_sum_filter_not P
    (fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D) F
  have hsmall := h118 N W T T₀ D hT hN1 hD0 hW hsep
  rw [hDT] at hsmall
  have hlarge : ∑ p ∈ P.filter (fun p => ¬ ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D), F p ≤
      C₉ * T ^ ε₁ * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
        Real.sqrt E * Real.sqrt X * (N : ℝ) ^ 2) := by
    refine le_trans ?_ (h119 N W T T₀ hT hNT hNle hW hsep)
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
    obtain ⟨hpP, hpD⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpP, (lt_of_not_ge hpD).le⟩
  -- `E ≤ α + β √E`
  set sX := Real.sqrt X
  set sE := Real.sqrt E
  have hsX : 0 ≤ sX := Real.sqrt_nonneg _
  have hsE : 0 ≤ sE := Real.sqrt_nonneg _
  have hc : 0 ≤ (N : ℝ) ^ (-2 * σ) := by positivity
  have hTε₁ : 0 ≤ T ^ ε₁ := by positivity
  set α : ℝ := K * T ^ ε₁ * (N : ℝ) ^ (-2 * σ) * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ)) with hαdef
  set β : ℝ := 3 * K * T ^ ε₁ * (N : ℝ) ^ (-2 * σ) * sX * (N : ℝ) ^ 2 with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have hmain : E ≤ α + β * sE := by
    have hsum : ∑ p ∈ P, F p ≤ (2 * C₈ + C₉) * T ^ ε₁ *
        ((N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ)) + 3 * (sX * (N : ℝ) ^ 2) * sE) := by
      rw [← hsplit]
      have h1 : C₈ * T ^ ε₁ * ((N : ℝ) ^ 2 + (N : ℝ) ^ 2) * (sX * sE) =
          2 * C₈ * T ^ ε₁ * (sX * (N : ℝ) ^ 2 * sE) := by ring
      have h2 : C₉ * T ^ ε₁ * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
          sE * sX * (N : ℝ) ^ 2) = C₉ * T ^ ε₁ * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) *
            X ^ (21 / 8 : ℝ)) + C₉ * T ^ ε₁ * (sX * (N : ℝ) ^ 2 * sE) := by ring
      have hA : 0 ≤ T ^ ε₁ * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ)) := by
        positivity
      have hB : 0 ≤ T ^ ε₁ * (sX * (N : ℝ) ^ 2 * sE) := by positivity
      have hs' : ∑ p ∈ P.filter (fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D), F p ≤
          2 * C₈ * T ^ ε₁ * (sX * (N : ℝ) ^ 2 * sE) := by
        rw [← h1]; exact hsmall
      have hl' := hlarge
      rw [h2] at hl'
      nlinarith [mul_nonneg hC₈ hA, mul_nonneg hC₉ hB, mul_nonneg hC₈ hB]
    calc E ≤ c₄ * (N : ℝ) ^ (-2 * σ) * ∑ p ∈ P, F p := h114
      _ ≤ c₄ * (N : ℝ) ^ (-2 * σ) * ((2 * C₈ + C₉) * T ^ ε₁ *
            ((N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ)) +
              3 * (sX * (N : ℝ) ^ 2) * sE)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = α + β * sE := by rw [hαdef, hβdef, hKdef]; ring
  clear_value α β
  have hsq : sE ^ 2 ≤ 1 * E := by rw [one_mul, Real.sq_sqrt hE0]
  have hboot := Sieve.le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul hE0 hsE hβ0 zero_le_one
    hmain hsq
  -- the exponents
  have hpow1 : (N : ℝ) ^ (-2 * σ) * N = (N : ℝ) ^ (1 - 2 * σ) := by
    rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
  have hpow4 : ((N : ℝ) ^ (-2 * σ) * (N : ℝ) ^ 2) ^ 2 = (N : ℝ) ^ (4 - 4 * σ) := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (-2 * σ)), ← Real.rpow_mul hN0.le,
      ← pow_mul, ← Real.rpow_natCast (N : ℝ), ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have hTT : (T ^ ε₁) ^ 2 = T ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, hε₁]; push_cast; ring_nf
  have hTε₁ε : T ^ ε₁ ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hε₁]; linarith)
  have hsX2 : sX ^ 2 = X := Real.sq_sqrt hX0
  have hα : 2 * α = 2 * K * T ^ ε₁ * ((N : ℝ) ^ (1 - 2 * σ) * X ^ 3 +
      X ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ)) := by
    rw [hαdef, ← hpow1]; ring
  have hβ2 : β ^ 2 * 1 = 9 * K ^ 2 * (T ^ ε₁) ^ 2 * X * (N : ℝ) ^ (4 - 4 * σ) := by
    rw [hβdef, ← hpow4, ← hsX2]; ring
  rw [hα, hβ2, hTT] at hboot
  set Q₁ := X * (N : ℝ) ^ (4 - 4 * σ) with hQ₁def
  set Q₂ := X ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) with hQ₂def
  set Q₃ := X ^ 3 * (N : ℝ) ^ (1 - 2 * σ) with hQ₃def
  have hQ₁ : 0 ≤ Q₁ := by positivity
  have hQ₂ : 0 ≤ Q₂ := by positivity
  have hQ₃ : 0 ≤ Q₃ := by positivity
  have hTε : 0 ≤ T ^ ε := by positivity
  have hTε₁0 : (0 : ℝ) ≤ T ^ ε₁ := by positivity
  have e1 : (N : ℝ) ^ (1 - 2 * σ) * X ^ 3 = Q₃ := by rw [hQ₃def]; ring
  have e3 : 9 * K ^ 2 * T ^ ε * X * (N : ℝ) ^ (4 - 4 * σ) = 9 * K ^ 2 * T ^ ε * Q₁ := by
    rw [hQ₁def]; ring
  clear_value Q₁ Q₂ Q₃
  rw [e1, e3] at hboot
  exact propElevenOne_collect hK hTε hTε₁ε hQ₁ hQ₂ hQ₃ hboot

end

end RHTower.GuthMaynard
