import GaloisForLFunctions.RHTower.Sieve.CardLengthGapAll
import GaloisForLFunctions.RHTower.Sieve.RouteEMarkerHallLaw

/-!
# Reciprocal-marker Hall law at every positive subpower exponent

The marker construction only needs an auxiliary exponent strictly below the target exponent.
Using the all-positive-exponent window-gap theorem removes the former `1/2 < β` restriction and
gives the Hall capacity law for every fixed `0 < β < 1`.
-/

namespace RHTower.Sieve

open Finset Filter ArithmeticFunction

noncomputable section

/-- Twice the marker tile length fits inside any strictly larger positive subpower window. -/
theorem eventually_two_tileLen_le_all {β β' : ℝ} (hβ0 : 0 < β) (hββ' : β < β')
    (K₀ : ℕ) :
    ∀ᶠ Z : ℕ in atTop, ∀ u : ℕ, 0 < tileBase K₀ u → tileBase K₀ u ≤ Z →
      2 * ((tileLen β K₀ u : ℕ) : ℝ)
        ≤ ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) := by
  have hgap := eventually_cardLength_gap_all (β := β) (β' := β')
    (a := 8 + (2 : ℝ) ^ (K₀ + 3)) (b := 2) hβ0 hββ' (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hgap,
    eventually_ge_atTop 1] with Z hZgap hZ1
  intro u hpos hZ
  have hZR : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hZR0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (Z : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hZR
  have hCZ : (1 : ℝ) ≤ cardLength β (Z : ℝ) := one_le_cardLength hZR
  have hsplit : Real.sqrt ((Z : ℝ) * Real.log (Z : ℝ))
      = Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ)) := Real.sqrt_mul hZR0.le _
  have hbound := tileLen_le_bound (β := β) (K₀ := K₀) (u := u) (Z := Z) hβ0 hpos hZ
  have hceilge : Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)
      ≤ ((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  refine le_trans ?_ hceilge
  have hstep1 : 2 * ((tileLen β K₀ u : ℕ) : ℝ)
      ≤ (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) + 2 := by
    have hpow : (2 : ℝ) ^ (K₀ + 3) = 4 * (2 : ℝ) ^ (K₀ + 1) := by
      rw [show K₀ + 3 = (K₀ + 1) + 2 by ring, pow_add]
      ring
    rw [hsplit] at hbound
    rw [hpow]
    nlinarith [hbound]
  refine hstep1.trans ?_
  have habs : 8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3)
      ≤ (8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (K₀ + 3) := by positivity
    nlinarith [hCZ, hp]
  have hstep2 : (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
        * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) + 2
      ≤ Real.sqrt (Z : ℝ)
        * ((8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ)
          * Real.sqrt (Real.log (Z : ℝ)) + 2) := by
    have hmul : (8 * cardLength β (Z : ℝ) + (2 : ℝ) ^ (K₀ + 3))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ)))
        ≤ ((8 + (2 : ℝ) ^ (K₀ + 3)) * cardLength β (Z : ℝ))
          * (Real.sqrt (Z : ℝ) * Real.sqrt (Real.log (Z : ℝ))) := by
      refine mul_le_mul_of_nonneg_right habs ?_
      positivity
    nlinarith [hmul, hsq1]
  refine hstep2.trans ?_
  refine mul_le_mul_of_nonneg_left hZgap (by linarith [hsq1])

/-- The reciprocal-marker Hall law at every fixed positive subpower exponent. -/
theorem route_e_marker_hall_law_all {β' : ℝ} (hβ'0 : 0 < β') (hβ'1 : β' < 1)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (C : ℝ) :
    ∀ᶠ Z : ℕ in atTop,
      C * (((⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ : ℕ) : ℝ)
          / Real.log ((Z : ℕ) : ℝ))
        ≤ ((((Finset.Ioc Z
            (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊)).filter
              (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  set β : ℝ := β' / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hββ' : β < β' := by rw [hβdef]; linarith
  have hβ1 : β < 1 := hββ'.trans hβ'1
  obtain ⟨K₀, hK₀⟩ := exists_multiHarmConst_ge (max (4096 * C / squarefreeDensity) 1)
  have hharm : 0 < multiHarmConst K₀ :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hK₀)
  have hCle : C ≤ tileConst K₀ / 4 := by
    have h1 : 4096 * C / squarefreeDensity ≤ multiHarmConst K₀ :=
      le_trans (le_max_left _ _) hK₀
    rw [div_le_iff₀ hD] at h1
    rw [tileConst]
    linarith [h1]
  filter_upwards [tiled_count hβ0 hβ1 hσ K₀ hharm,
    eventually_two_tileLen_le_all hβ0 hββ' K₀,
    eventually_three_mul_ceil_le hβ'0 hβ'1,
    eventually_ge_atTop 2] with Z hcount htile h3 hZ2
  obtain ⟨u, hPu, hcov, hmain⟩ := hcount
  set H : ℕ := ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊ with hH
  have hPpos : 0 < tileBase K₀ u := by omega
  have h2t : 2 * tileLen β K₀ u ≤ H := by
    have hR := htile u hPpos hPu
    exact_mod_cast hR
  refine le_trans ?_ (hmain H h3 h2t)
  have hZR : (2 : ℝ) ≤ ((Z : ℕ) : ℝ) := by exact_mod_cast hZ2
  have hlogZ : (0 : ℝ) < Real.log ((Z : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ (H : ℝ) / Real.log ((Z : ℕ) : ℝ) := div_nonneg hHnn hlogZ.le
  exact mul_le_mul_of_nonneg_right hCle hnn

/-- Every positive subpower window carries at least as many positive-Möbius integers as primes. -/
theorem route_e_marker_hall_injection_all {β' : ℝ} (hβ'0 : 0 < β') (hβ'1 : β' < 1) :
    ∀ᶠ Z : ℕ in atTop,
      #{p ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) | p.Prime}
        ≤ #{n ∈ Finset.Ioc Z (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) |
              moebius n = 1} := by
  filter_upwards [route_e_marker_hall_law_all hβ'0 hβ'1 (Or.inl rfl) 17,
    eventually_card_primes_le_window β'] with Z hmark hprime
  have hR : ((#{p ∈ Finset.Ioc Z
      (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) | p.Prime} : ℕ) : ℝ)
      ≤ ((#{n ∈ Finset.Ioc Z
        (Z + ⌈Real.sqrt (Z : ℝ) * cardLength β' (Z : ℝ)⌉₊) |
          moebius n = 1} : ℕ) : ℝ) := le_trans hprime hmark
  exact_mod_cast hR

end

end RHTower.Sieve
