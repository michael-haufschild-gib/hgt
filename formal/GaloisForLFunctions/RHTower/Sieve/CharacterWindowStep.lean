import GaloisForLFunctions.RHTower.Sieve.CharacterWindowMass

/-!
# One window step for the character recursion

The window step, run on the source of a character: only the phases at the window's primes are free,
the proper prime powers of the window are already determined, and the moment problem cancels both
the Taylor image of the previous levels and those forced values.
-/

noncomputable section

open ArithmeticFunction GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

set_option maxHeartbeats 1000000 in
/-- **One character window step.** -/
theorem exists_character_window_step (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ (u : ℕ → ℂ) (K : ℝ), 0 ≤ K →
      (∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) →
      (∀ m : ℕ, m < J → ‖arithProfile (characterSource u) m x‖
        ≤ ((x ^ θ) ^ m / ((m.factorial : ℕ) : ℝ)) * K) →
      2 * (J : ℝ) * (2 ^ J * K + forcedMassBound θ x) ≤ primeWindowFloor J θ x →
      ∃ c : ℕ → ℂ, (∀ q ∈ windowPrimes x (x + x ^ θ), ‖c q‖ = 1) ∧
        ∀ j : ℕ, j < J →
          ‖arithProfile (characterSource
              (fun m => if m ∈ windowPrimes x (x + x ^ θ) then c m else u m)) j (x + x ^ θ)‖
            ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + x ^ θ)) := by
  classical
  have hθ0 : 0 < θ := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) (lt_trans halpha hαθ)
  obtain ⟨X₀, hX₀, hray⟩ := exists_prime_window_rayleigh J hJ halpha hαθ hθ1
  refine ⟨max X₀ 2, le_trans one_le_two (le_max_right _ _), ?_⟩
  intro x hx u K hK0 hu hstate hsmall
  have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hΔpos : 0 < (x ^ θ) := Real.rpow_pos_of_pos hxpos θ
  have hΔ1 : 1 ≤ (x ^ θ) := Real.one_le_rpow hx1 (le_of_lt hθ0)
  have hΔx : (x ^ θ) ≤ x := by
    calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hθ1)
      _ = x := Real.rpow_one x
  have hxy : x < (x + x ^ θ) := by linarith
  have hy1 : (1:ℝ) ≤ (x + x ^ θ) := by linarith
  have hysq : (x + x ^ θ) ≤ x ^ 2 := by
    have : x * x - x = x * (x - 1) := by ring
    nlinarith [hΔx, hx2]
  have himg : Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ = (windowPrimes x (x + x ^ θ)) := image_windowPrimeIndex x (x + x ^ θ)
  -- window primes exceed the square root of the right endpoint
  have hSprime : ∀ q ∈ (windowPrimes x (x + x ^ θ)), Nat.Prime q := fun q hq => (mem_windowPrimes.1 hq).2
  have hSsq : ∀ q ∈ (windowPrimes x (x + x ^ θ)), (x + x ^ θ) < (q : ℝ) ^ 2 := by
    intro q hq
    have hmem := Finset.mem_Ioc.1 (mem_windowPrimes.1 hq).1
    have hqx : x < (q : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hmem.1
      have h2 := Nat.lt_floor_add_one x
      linarith
    nlinarith [hqx, hxpos, hysq]
  -- the weights
  have hC : ∀ r, |(windowPrimeWeight x θ) r| ≤ Real.log (x + x ^ θ) := by
    intro r
    have hmem := windowPrimeIndex_mem x (x + x ^ θ) r
    have hprime := windowPrimeIndex_prime x (x + x ^ θ) r
    have hple : ((windowPrimeIndex x (x + x ^ θ)) r : ℝ) ≤ (x + x ^ θ) := by
      have h1 : (windowPrimeIndex x (x + x ^ θ)) r ≤ ⌊(x + x ^ θ)⌋₊ := (Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1).2
      have h2 : ((windowPrimeIndex x (x + x ^ θ)) r : ℝ) ≤ (⌊(x + x ^ θ)⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le (by linarith))
    have h2 : (2:ℝ) ≤ ((windowPrimeIndex x (x + x ^ θ)) r : ℝ) := by exact_mod_cast hprime.two_le
    have hlog0 : 0 ≤ Real.log ((windowPrimeIndex x (x + x ^ θ)) r) := Real.log_nonneg (by linarith)
    rw [windowPrimeWeight, abs_of_nonneg hlog0]
    exact Real.log_le_log (by linarith) hple
  have hC0 : 0 ≤ Real.log (x + x ^ θ) := Real.log_nonneg hy1
  -- the Rayleigh floor
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlam : 0 < primeWindowFloor J θ x := by
    rw [primeWindowFloor]
    have hUpos : 0 < unitCoeffConstSum J := unitCoeffConstSum_pos hJ
    have hfacpos : (0:ℝ) < (((J - 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J - 1)
    have hnum : (0:ℝ) < x ^ θ / (32768 * J) := by positivity
    have hden : (0:ℝ) < (J : ℝ) * (2 * ((J : ℝ) * (2 ^ (J - 1) /
        ((1 / (2 * (J : ℝ))) ^ (J - 1) * (((J - 1).factorial : ℕ) : ℝ)))) *
        unitCoeffConstSum J) ^ 2 := by positivity
    exact div_pos hnum hden
  have hquad : ∀ v : Fin J → ℝ,
      primeWindowFloor J θ x * (∑ i, v i ^ 2)
        ≤ v ⬝ᵥ (atomicHankel (windowPrimeWeight x θ) (windowNode (windowPrimeIndex x (x + x ^ θ)) x (x + x ^ θ)) J).mulVec v := by
    intro v
    exact hray x hxX₀ v
  -- the forced mass
  have hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊(x + x ^ θ)⌋₊ \ Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ,
      ‖characterSource u n‖ ≤ forcedMassBound θ x := by
    rw [himg]
    exact sum_norm_characterSource_forced_le hu hx2 hΔ1
  -- the size condition
  have hsize : (J : ℝ) * (∑ j : Fin J,
      ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ) (j : ℕ)‖ ^ 2)
      ≤ primeWindowFloor J θ x ^ 2 := by
    have hM0 : 0 ≤ forcedMassBound θ x := forcedMassBound_nonneg hx1
    have hterm : ∀ j : Fin J,
        ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ) (j : ℕ)‖
          ≤ 2 * (2 ^ J * K + forcedMassBound θ x) := by
      intro j
      have hj : (j : ℕ) < J := j.2
      have hstate' : ∀ m ≤ (j : ℕ), ‖arithProfile (characterSource u) m x‖
          ≤ (((x + x ^ θ) - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
        intro m hm
        have hyx : (x + x ^ θ) - x = x ^ θ := by
                    ring
        rw [hyx]
        exact hstate m (lt_of_le_of_lt hm hj)
      have hbound := norm_windowTargetPartial_le hx1 hxy hstate' hmass
      have hpow : (2:ℝ) ^ (j : ℕ) ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hj)
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      have hle : ‖windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ)
          (j : ℕ)‖ ≤ 2 ^ J * K + forcedMassBound θ x := by
        refine le_trans hbound ?_
        have : (2:ℝ) ^ (j : ℕ) * K ≤ 2 ^ J * K := mul_le_mul_of_nonneg_right hpow hK0
        linarith
      linarith
    have hsum : (∑ j : Fin J,
        ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ) (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2 := by
      calc (∑ j : Fin J,
            ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ)
              (j : ℕ)‖ ^ 2)
          ≤ ∑ _j : Fin J, (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hterm j) 2
        _ = (J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfinal : (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2)
        ≤ primeWindowFloor J θ x ^ 2 := by
      have hkey : ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x))) ^ 2
          ≤ primeWindowFloor J θ x ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        calc (J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x))
            = 2 * (J : ℝ) * (2 ^ J * K + forcedMassBound θ x) := by ring
          _ ≤ primeWindowFloor J θ x := hsmall
      calc (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2)
          = ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x))) ^ 2 := by ring
        _ ≤ primeWindowFloor J θ x ^ 2 := hkey
    calc (J : ℝ) * (∑ j : Fin J,
          ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) x (x + x ^ θ)
            (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBound θ x)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hJR)
      _ ≤ primeWindowFloor J θ x ^ 2 := hfinal
  obtain ⟨b, hb1, hb2⟩ := exists_window_phases_partial hJ (characterSource u) hx1 hxy
    (windowPrimeIndex_injective x (x + x ^ θ))
    (fun r => (mem_windowPrimes.1 (windowPrimeIndex_mem x (x + x ^ θ) r)).1) (windowPrimeWeight x θ) hC hC0 hlam hquad hsize
  refine ⟨phaseAssign (windowPrimeIndex x (x + x ^ θ)) b, ?_, ?_⟩
  · intro q hq
    have hex : ∃ r, (windowPrimeIndex x (x + x ^ θ)) r = q := by
      have : q ∈ Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ := by rw [himg]; exact hq
      obtain ⟨r, _, hr⟩ := Finset.mem_image.1 this
      exact ⟨r, hr⟩
    rw [phaseAssign, dif_pos hex]
    exact hb1 _
  · intro j hj
    have hbridge := arithProfile_characterSource_update (u := u) (c := phaseAssign (windowPrimeIndex x (x + x ^ θ)) b)
      (S := windowPrimes x (x + x ^ θ)) (y := x + x ^ θ) hSprime hSsq j (le_refl (x + x ^ θ))
      (by linarith)
    rw [hbridge]
    have hupdate : updateWindow (characterSource u) (windowPrimes x (x + x ^ θ))
        (fun n => phaseAssign (windowPrimeIndex x (x + x ^ θ)) b n * ((Real.log n : ℝ) : ℂ))
        = updateWindow (characterSource u) (Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ) (windowAssign (windowPrimeIndex x (x + x ^ θ)) b (windowPrimeWeight x θ)) := by
      funext n
      rw [updateWindow, updateWindow, himg]
      by_cases hmem : n ∈ (windowPrimes x (x + x ^ θ))
      · rw [if_pos hmem, if_pos hmem]
        have hex : ∃ r, (windowPrimeIndex x (x + x ^ θ)) r = n := by
          have hn : n ∈ Finset.image (windowPrimeIndex x (x + x ^ θ)) Finset.univ := by
            rw [himg]
            exact hmem
          obtain ⟨r, _, hr⟩ := Finset.mem_image.1 hn
          exact ⟨r, hr⟩
        rw [windowAssign_eq_phaseAssign (w := windowPrimeWeight x θ) (fun r => rfl) n,
          if_pos hex]
      · rw [if_neg hmem, if_neg hmem]
    rw [hupdate]
    have := hb2 ⟨j, hj⟩
    have hyx : (x + x ^ θ) - x = x ^ θ := by
            ring
    rw [hyx] at this
    exact this

set_option maxHeartbeats 1000000 in
/-- **One character window step.** -/
theorem exists_character_window_step_general (J : ℕ) (hJ : 0 < J) {α : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (halpha1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → 0 < L → x + L ≤ x ^ 2 → 4 * (J : ℝ) * (x + L) ^ α ≤ L →
      ∀ (u : ℕ → ℂ) (K : ℝ), 0 ≤ K →
      (∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) →
      (∀ m : ℕ, m < J → ‖arithProfile (characterSource u) m x‖
        ≤ ((L) ^ m / ((m.factorial : ℕ) : ℝ)) * K) →
      2 * (J : ℝ) * (2 ^ J * K + forcedMassBoundL x L) ≤ primeWindowFloorL J L →
      ∃ c : ℕ → ℂ, (∀ q ∈ windowPrimes x (x + L), ‖c q‖ = 1) ∧
        ∀ j : ℕ, j < J →
          ‖arithProfile (characterSource
              (fun m => if m ∈ windowPrimes x (x + L) then c m else u m)) j (x + L)‖
            ≤ ((L) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + L)) := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  obtain ⟨X₀, hX₀, hray⟩ := exists_prime_window_rayleigh_general J hJ halpha halpha1
  refine ⟨max X₀ 2, le_trans one_le_two (le_max_right _ _), ?_⟩
  intro x L hx hL hLx hLbig u K hK0 hu hstate hsmall
  have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hΔpos : 0 < L := hL
  have hΔ1 : 1 ≤ L := by
    have h1 : (1:ℝ) ≤ (x + L) ^ α := Real.one_le_rpow (by linarith) (le_of_lt hα0)
    have hJ1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    nlinarith [hLbig, h1, hJ1]
  have hxy : x < (x + L) := by linarith
  have hy1 : (1:ℝ) ≤ (x + L) := by linarith
  have hysq : (x + L) ≤ x ^ 2 := hLx
  have himg : Finset.image (windowPrimeIndex x (x + L)) Finset.univ = (windowPrimes x (x + L)) := image_windowPrimeIndex x (x + L)
  -- window primes exceed the square root of the right endpoint
  have hSprime : ∀ q ∈ (windowPrimes x (x + L)), Nat.Prime q := fun q hq => (mem_windowPrimes.1 hq).2
  have hSsq : ∀ q ∈ (windowPrimes x (x + L)), (x + L) < (q : ℝ) ^ 2 := by
    intro q hq
    have hmem := Finset.mem_Ioc.1 (mem_windowPrimes.1 hq).1
    have hqx : x < (q : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hmem.1
      have h2 := Nat.lt_floor_add_one x
      linarith
    nlinarith [hqx, hxpos, hysq]
  -- the weights
  have hC : ∀ r, |(windowPrimeWeightL x L) r| ≤ Real.log (x + L) := by
    intro r
    have hmem := windowPrimeIndex_mem x (x + L) r
    have hprime := windowPrimeIndex_prime x (x + L) r
    have hple : ((windowPrimeIndex x (x + L)) r : ℝ) ≤ (x + L) := by
      have h1 : (windowPrimeIndex x (x + L)) r ≤ ⌊(x + L)⌋₊ := (Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1).2
      have h2 : ((windowPrimeIndex x (x + L)) r : ℝ) ≤ (⌊(x + L)⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le (by linarith))
    have h2 : (2:ℝ) ≤ ((windowPrimeIndex x (x + L)) r : ℝ) := by exact_mod_cast hprime.two_le
    have hlog0 : 0 ≤ Real.log ((windowPrimeIndex x (x + L)) r) := Real.log_nonneg (by linarith)
    rw [windowPrimeWeightL, abs_of_nonneg hlog0]
    exact Real.log_le_log (by linarith) hple
  have hC0 : 0 ≤ Real.log (x + L) := Real.log_nonneg hy1
  -- the Rayleigh floor
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlam : 0 < primeWindowFloorL J L := by
    rw [primeWindowFloorL]
    have hden : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
    have hnum : (0:ℝ) < L / (32768 * J) := by positivity
    exact div_pos hnum hden
  have hquad : ∀ v : Fin J → ℝ,
      primeWindowFloorL J L * (∑ i, v i ^ 2)
        ≤ v ⬝ᵥ (atomicHankel (windowPrimeWeightL x L) (windowNode (windowPrimeIndex x (x + L)) x (x + L)) J).mulVec v := by
    intro v
    exact hray x L hxX₀ hL hLbig v
  -- the forced mass
  have hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊(x + L)⌋₊ \ Finset.image (windowPrimeIndex x (x + L)) Finset.univ,
      ‖characterSource u n‖ ≤ forcedMassBoundL x L := by
    rw [himg]
    exact sum_norm_characterSource_forced_le_L hu hx2 hΔ1
  -- the size condition
  have hsize : (J : ℝ) * (∑ j : Fin J,
      ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖ ^ 2)
      ≤ primeWindowFloorL J L ^ 2 := by
    have hM0 : 0 ≤ forcedMassBoundL x L := forcedMassBoundL_nonneg hx1 (le_of_lt hL)
    have hterm : ∀ j : Fin J,
        ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖
          ≤ 2 * (2 ^ J * K + forcedMassBoundL x L) := by
      intro j
      have hj : (j : ℕ) < J := j.2
      have hstate' : ∀ m ≤ (j : ℕ), ‖arithProfile (characterSource u) m x‖
          ≤ (((x + L) - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
        intro m hm
        have hyx : (x + L) - x = L := by
                    ring
        rw [hyx]
        exact hstate m (lt_of_le_of_lt hm hj)
      have hbound := norm_windowTargetPartial_le hx1 hxy hstate' hmass
      have hpow : (2:ℝ) ^ (j : ℕ) ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hj)
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      have hle : ‖windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
          (j : ℕ)‖ ≤ 2 ^ J * K + forcedMassBoundL x L := by
        refine le_trans hbound ?_
        have : (2:ℝ) ^ (j : ℕ) * K ≤ 2 ^ J * K := mul_le_mul_of_nonneg_right hpow hK0
        linarith
      linarith
    have hsum : (∑ j : Fin J,
        ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2 := by
      calc (∑ j : Fin J,
            ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
              (j : ℕ)‖ ^ 2)
          ≤ ∑ _j : Fin J, (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hterm j) 2
        _ = (J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfinal : (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2)
        ≤ primeWindowFloorL J L ^ 2 := by
      have hkey : ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L))) ^ 2
          ≤ primeWindowFloorL J L ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        calc (J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L))
            = 2 * (J : ℝ) * (2 ^ J * K + forcedMassBoundL x L) := by ring
          _ ≤ primeWindowFloorL J L := hsmall
      calc (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2)
          = ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L))) ^ 2 := by ring
        _ ≤ primeWindowFloorL J L ^ 2 := hkey
    calc (J : ℝ) * (∑ j : Fin J,
          ‖2 * windowTargetPartial (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
            (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + forcedMassBoundL x L)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hJR)
      _ ≤ primeWindowFloorL J L ^ 2 := hfinal
  obtain ⟨b, hb1, hb2⟩ := exists_window_phases_partial hJ (characterSource u) hx1 hxy
    (windowPrimeIndex_injective x (x + L))
    (fun r => (mem_windowPrimes.1 (windowPrimeIndex_mem x (x + L) r)).1) (windowPrimeWeightL x L) hC hC0 hlam hquad hsize
  refine ⟨phaseAssign (windowPrimeIndex x (x + L)) b, ?_, ?_⟩
  · intro q hq
    have hex : ∃ r, (windowPrimeIndex x (x + L)) r = q := by
      have : q ∈ Finset.image (windowPrimeIndex x (x + L)) Finset.univ := by rw [himg]; exact hq
      obtain ⟨r, _, hr⟩ := Finset.mem_image.1 this
      exact ⟨r, hr⟩
    rw [phaseAssign, dif_pos hex]
    exact hb1 _
  · intro j hj
    have hbridge := arithProfile_characterSource_update (u := u) (c := phaseAssign (windowPrimeIndex x (x + L)) b)
      (S := windowPrimes x (x + L)) (y := x + L) hSprime hSsq j (le_refl (x + L))
      (by linarith)
    rw [hbridge]
    have hupdate : updateWindow (characterSource u) (windowPrimes x (x + L))
        (fun n => phaseAssign (windowPrimeIndex x (x + L)) b n * ((Real.log n : ℝ) : ℂ))
        = updateWindow (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) (windowAssign (windowPrimeIndex x (x + L)) b (windowPrimeWeightL x L)) := by
      funext n
      rw [updateWindow, updateWindow, himg]
      by_cases hmem : n ∈ (windowPrimes x (x + L))
      · rw [if_pos hmem, if_pos hmem]
        have hex : ∃ r, (windowPrimeIndex x (x + L)) r = n := by
          have hn : n ∈ Finset.image (windowPrimeIndex x (x + L)) Finset.univ := by
            rw [himg]
            exact hmem
          obtain ⟨r, _, hr⟩ := Finset.mem_image.1 hn
          exact ⟨r, hr⟩
        rw [windowAssign_eq_phaseAssign (w := windowPrimeWeightL x L) (fun r => rfl) n,
          if_pos hex]
      · rw [if_neg hmem, if_neg hmem]
    rw [hupdate]
    have := hb2 ⟨j, hj⟩
    have hyx : (x + L) - x = L := by
            ring
    rw [hyx] at this
    exact this

theorem exists_character_window_step_general_full (J : ℕ) (hJ : 0 < J) {α : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (halpha1 : α < 1) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → 0 < L → x + L ≤ x ^ 2 → 4 * (J : ℝ) * (x + L) ^ α ≤ L →
      ∀ (u : ℕ → ℂ) (K Mq : ℝ), 0 ≤ K → (∀ t ∈ Set.Icc x (x + L), ‖dq t‖ ≤ Mq) →
      (∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) →
      (∀ m : ℕ, m < J → ‖arithJumpProfile dq (characterSource u) m x‖
        ≤ ((L) ^ m / ((m.factorial : ℕ) : ℝ)) * K) →
      2 * (J : ℝ) * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)) ≤ primeWindowFloorL J L →
      ∃ c : ℕ → ℂ, (∀ q ∈ windowPrimes x (x + L), ‖c q‖ = 1) ∧
        ∀ j : ℕ, j < J →
          ‖arithJumpProfile dq (characterSource
              (fun m => if m ∈ windowPrimes x (x + L) then c m else u m)) j (x + L)‖
            ≤ ((L) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + L)) := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  obtain ⟨X₀, hX₀, hray⟩ := exists_prime_window_rayleigh_general J hJ halpha halpha1
  refine ⟨max X₀ 2, le_trans one_le_two (le_max_right _ _), ?_⟩
  intro x L hx hL hLx hLbig u K Mq hK0 hdqb hu hstate hsmall
  have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hΔpos : 0 < L := hL
  have hMq0 : 0 ≤ Mq := le_trans (norm_nonneg _) (hdqb x ⟨le_rfl, by linarith⟩)
  have hΔ1 : 1 ≤ L := by
    have h1 : (1:ℝ) ≤ (x + L) ^ α := Real.one_le_rpow (by linarith) (le_of_lt hα0)
    have hJ1 : (1:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    nlinarith [hLbig, h1, hJ1]
  have hxy : x < (x + L) := by linarith
  have hy1 : (1:ℝ) ≤ (x + L) := by linarith
  have hysq : (x + L) ≤ x ^ 2 := hLx
  have himg : Finset.image (windowPrimeIndex x (x + L)) Finset.univ = (windowPrimes x (x + L)) := image_windowPrimeIndex x (x + L)
  -- window primes exceed the square root of the right endpoint
  have hSprime : ∀ q ∈ (windowPrimes x (x + L)), Nat.Prime q := fun q hq => (mem_windowPrimes.1 hq).2
  have hSsq : ∀ q ∈ (windowPrimes x (x + L)), (x + L) < (q : ℝ) ^ 2 := by
    intro q hq
    have hmem := Finset.mem_Ioc.1 (mem_windowPrimes.1 hq).1
    have hqx : x < (q : ℝ) := by
      have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hmem.1
      have h2 := Nat.lt_floor_add_one x
      linarith
    nlinarith [hqx, hxpos, hysq]
  -- the weights
  have hC : ∀ r, |(windowPrimeWeightL x L) r| ≤ Real.log (x + L) := by
    intro r
    have hmem := windowPrimeIndex_mem x (x + L) r
    have hprime := windowPrimeIndex_prime x (x + L) r
    have hple : ((windowPrimeIndex x (x + L)) r : ℝ) ≤ (x + L) := by
      have h1 : (windowPrimeIndex x (x + L)) r ≤ ⌊(x + L)⌋₊ := (Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1).2
      have h2 : ((windowPrimeIndex x (x + L)) r : ℝ) ≤ (⌊(x + L)⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le (by linarith))
    have h2 : (2:ℝ) ≤ ((windowPrimeIndex x (x + L)) r : ℝ) := by exact_mod_cast hprime.two_le
    have hlog0 : 0 ≤ Real.log ((windowPrimeIndex x (x + L)) r) := Real.log_nonneg (by linarith)
    rw [windowPrimeWeightL, abs_of_nonneg hlog0]
    exact Real.log_le_log (by linarith) hple
  have hC0 : 0 ≤ Real.log (x + L) := Real.log_nonneg hy1
  -- the Rayleigh floor
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlam : 0 < primeWindowFloorL J L := by
    rw [primeWindowFloorL]
    have hden : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
    have hnum : (0:ℝ) < L / (32768 * J) := by positivity
    exact div_pos hnum hden
  have hquad : ∀ v : Fin J → ℝ,
      primeWindowFloorL J L * (∑ i, v i ^ 2)
        ≤ v ⬝ᵥ (atomicHankel (windowPrimeWeightL x L) (windowNode (windowPrimeIndex x (x + L)) x (x + L)) J).mulVec v := by
    intro v
    exact hray x L hxX₀ hL hLbig v
  -- the forced mass
  have hmass : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊(x + L)⌋₊ \ Finset.image (windowPrimeIndex x (x + L)) Finset.univ,
      ‖characterSource u n‖ ≤ forcedMassBoundL x L := by
    rw [himg]
    exact sum_norm_characterSource_forced_le_L hu hx2 hΔ1
  -- the size condition
  have hsize : (J : ℝ) * (∑ j : Fin J,
      ‖2 * windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖ ^ 2)
      ≤ primeWindowFloorL J L ^ 2 := by
    have hM0 : 0 ≤ (forcedMassBoundL x L + Mq * L) :=
      add_nonneg (forcedMassBoundL_nonneg hx1 (le_of_lt hL)) (mul_nonneg hMq0 (le_of_lt hL))
    have hterm : ∀ j : Fin J,
        ‖2 * windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖
          ≤ 2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)) := by
      intro j
      have hj : (j : ℕ) < J := j.2
      have hstate' : ∀ m ≤ (j : ℕ), ‖arithJumpProfile dq (characterSource u) m x‖
          ≤ (((x + L) - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
        intro m hm
        have hyx : (x + L) - x = L := by
                    ring
        rw [hyx]
        exact hstate m (lt_of_le_of_lt hm hj)
      have hbound := norm_windowTargetFull_le hx1 hxy hdqb hstate' hmass
      have hLx' : x + L - x = L := by ring
      rw [hLx'] at hbound
      have hpow : (2:ℝ) ^ (j : ℕ) ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hj)
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      have hle : ‖windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
          (j : ℕ)‖ ≤ 2 ^ J * K + (forcedMassBoundL x L + Mq * L) := by
        refine le_trans hbound ?_
        have : (2:ℝ) ^ (j : ℕ) * K ≤ 2 ^ J * K := mul_le_mul_of_nonneg_right hpow hK0
        linarith
      linarith
    have hsum : (∑ j : Fin J,
        ‖2 * windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L) (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2 := by
      calc (∑ j : Fin J,
            ‖2 * windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
              (j : ℕ)‖ ^ 2)
          ≤ ∑ _j : Fin J, (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hterm j) 2
        _ = (J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfinal : (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2)
        ≤ primeWindowFloorL J L ^ 2 := by
      have hkey : ((J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)))) ^ 2
          ≤ primeWindowFloorL J L ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        calc (J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)))
            = 2 * (J : ℝ) * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)) := by ring
          _ ≤ primeWindowFloorL J L := hsmall
      calc (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2)
          = ((J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)))) ^ 2 := by ring
        _ ≤ primeWindowFloorL J L ^ 2 := hkey
    calc (J : ℝ) * (∑ j : Fin J,
          ‖2 * windowTargetFull dq (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) x (x + L)
            (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * ((J : ℝ) * (2 * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hJR)
      _ ≤ primeWindowFloorL J L ^ 2 := hfinal
  obtain ⟨b, hb1, hb2⟩ := exists_window_phases_partial_full hJ hdq (characterSource u) hx1 hxy
    (windowPrimeIndex_injective x (x + L))
    (fun r => (mem_windowPrimes.1 (windowPrimeIndex_mem x (x + L) r)).1) (windowPrimeWeightL x L) hC hC0 hlam hquad hsize
  refine ⟨phaseAssign (windowPrimeIndex x (x + L)) b, ?_, ?_⟩
  · intro q hq
    have hex : ∃ r, (windowPrimeIndex x (x + L)) r = q := by
      have : q ∈ Finset.image (windowPrimeIndex x (x + L)) Finset.univ := by rw [himg]; exact hq
      obtain ⟨r, _, hr⟩ := Finset.mem_image.1 this
      exact ⟨r, hr⟩
    rw [phaseAssign, dif_pos hex]
    exact hb1 _
  · intro j hj
    have hbridge := arithJumpProfile_characterSource_update (dq := dq) (u := u) (c := phaseAssign (windowPrimeIndex x (x + L)) b)
      (S := windowPrimes x (x + L)) (y := x + L) hSprime hSsq j (le_refl (x + L))
      (by linarith)
    rw [hbridge]
    have hupdate : updateWindow (characterSource u) (windowPrimes x (x + L))
        (fun n => phaseAssign (windowPrimeIndex x (x + L)) b n * ((Real.log n : ℝ) : ℂ))
        = updateWindow (characterSource u) (Finset.image (windowPrimeIndex x (x + L)) Finset.univ) (windowAssign (windowPrimeIndex x (x + L)) b (windowPrimeWeightL x L)) := by
      funext n
      rw [updateWindow, updateWindow, himg]
      by_cases hmem : n ∈ (windowPrimes x (x + L))
      · rw [if_pos hmem, if_pos hmem]
        have hex : ∃ r, (windowPrimeIndex x (x + L)) r = n := by
          have hn : n ∈ Finset.image (windowPrimeIndex x (x + L)) Finset.univ := by
            rw [himg]
            exact hmem
          obtain ⟨r, _, hr⟩ := Finset.mem_image.1 hn
          exact ⟨r, hr⟩
        rw [windowAssign_eq_phaseAssign (w := windowPrimeWeightL x L) (fun r => rfl) n,
          if_pos hex]
      · rw [if_neg hmem, if_neg hmem]
    rw [hupdate]
    have := hb2 ⟨j, hj⟩
    have hyx : (x + L) - x = L := by
            ring
    rw [hyx] at this
    exact this

end RHTower.Sieve

end
