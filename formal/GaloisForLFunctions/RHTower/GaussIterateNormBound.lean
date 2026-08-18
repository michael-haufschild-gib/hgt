import GaloisForLFunctions.RHTower.GaussTwoPieceL2Bound
import GaloisForLFunctions.RHTower.GaussPrimeScaleOperator

/-!
# The `L²` size of the iterated principal step

The class machinery stops one symbol short of the `m`-th iterate, because the spike exponent
would pass `1`.  That last symbol is a *bounded multiplication operator*, so its operator norm
suffices: the inner four factors of `R_n = B S B^(-2) S* B` keep the class, and the outer `B`
costs only `√p`.

The resulting bound is `‖R_I^m 1‖ ≤ C (1+I)^ρ` for every `ρ > 0` — an arbitrarily small power.
Together with `|σ_I|^m ≲ 1/I` this gives the column decay `‖G^m e_I‖ ≲ I^(-1+ρ)` that the
Hilbert–Schmidt tail of the singular-value comparison needs.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-! ## The tied class controls the norm up to a small power -/

theorem norm_le_of_tiedTwoPieceAmplitude {A θ B c ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hθ : 1 / 2 < θ) (hc : 1 / 2 < c) (hρ0 : 0 ≤ ρ) (hρ : 2 * c - 2 * θ ≤ 2 * ρ) {I : ℕ}
    {u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (h : TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
      (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)) :
    ‖u‖ ≤ Real.sqrt (2 * (A ^ 2 * intNatAbsPowTotal (2 * θ))
        + 2 * (B ^ 2 * intNatAbsPowTotal (2 * c))) * (1 + (I : ℝ)) ^ ρ := by
  have hIpos : (0 : ℝ) < 1 + (I : ℝ) := by positivity
  have hI1 : (1 : ℝ) ≤ 1 + (I : ℝ) := by
    have : (0 : ℝ) ≤ (I : ℝ) := by positivity
    linarith
  have hZθ : 0 ≤ intNatAbsPowTotal (2 * θ) := intNatAbsPowTotal_nonneg _
  have hZc : 0 ≤ intNatAbsPowTotal (2 * c) := intNatAbsPowTotal_nonneg _
  have hbase := norm_sq_le_of_twoPieceAmplitude hA (by positivity) hθ hc h
  -- convert the spike term
  have hspike : (B / (1 + (I : ℝ)) ^ θ) ^ 2 * (I : ℝ) ^ (2 * c)
      ≤ B ^ 2 * (1 + (I : ℝ)) ^ (2 * ρ) := by
    have h1 : (I : ℝ) ^ (2 * c) ≤ (1 + (I : ℝ)) ^ (2 * c) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hden : ((1 + (I : ℝ)) ^ θ) ^ 2 = (1 + (I : ℝ)) ^ (2 * θ) := by
      rw [← Real.rpow_natCast ((1 + (I : ℝ)) ^ θ) 2, ← Real.rpow_mul hIpos.le]
      congr 1
      push_cast
      ring
    have hd0 : (0 : ℝ) < (1 + (I : ℝ)) ^ (2 * θ) := Real.rpow_pos_of_pos hIpos _
    have hstep : (B / (1 + (I : ℝ)) ^ θ) ^ 2 * (I : ℝ) ^ (2 * c)
        ≤ B ^ 2 * (1 + (I : ℝ)) ^ (2 * c) / (1 + (I : ℝ)) ^ (2 * θ) := by
      have h2 : B ^ 2 * (I : ℝ) ^ (2 * c) ≤ B ^ 2 * (1 + (I : ℝ)) ^ (2 * c) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
      rw [div_pow, hden, div_mul_eq_mul_div, div_le_div_iff₀ hd0 hd0]
      nlinarith [h2, hd0.le]
    refine le_trans hstep ?_
    have hquot : (1 + (I : ℝ)) ^ (2 * c) / (1 + (I : ℝ)) ^ (2 * θ)
        = (1 + (I : ℝ)) ^ (2 * c - 2 * θ) := (Real.rpow_sub hIpos _ _).symm
    rw [mul_div_assoc, hquot]
    have hmono : (1 + (I : ℝ)) ^ (2 * c - 2 * θ) ≤ (1 + (I : ℝ)) ^ (2 * ρ) :=
      Real.rpow_le_rpow_of_exponent_le hI1 hρ
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hone : (1 : ℝ) ≤ (1 + (I : ℝ)) ^ (2 * ρ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hI1 (by linarith : (0 : ℝ) ≤ 2 * ρ)
    rwa [Real.rpow_zero] at h
  have hsq : ‖u‖ ^ 2
      ≤ (2 * (A ^ 2 * intNatAbsPowTotal (2 * θ)) + 2 * (B ^ 2 * intNatAbsPowTotal (2 * c)))
        * (1 + (I : ℝ)) ^ (2 * ρ) := by
    have hAZ : (0 : ℝ) ≤ A ^ 2 * intNatAbsPowTotal (2 * θ) := mul_nonneg (sq_nonneg A) hZθ
    have hbulk : 2 * (A ^ 2 * intNatAbsPowTotal (2 * θ))
        ≤ 2 * (A ^ 2 * intNatAbsPowTotal (2 * θ)) * (1 + (I : ℝ)) ^ (2 * ρ) := by
      nlinarith [hone, hAZ]
    have hsp : 2 * ((B / (1 + (I : ℝ)) ^ θ) ^ 2 * (I : ℝ) ^ (2 * c)
          * intNatAbsPowTotal (2 * c))
        ≤ 2 * (B ^ 2 * intNatAbsPowTotal (2 * c)) * (1 + (I : ℝ)) ^ (2 * ρ) := by
      have h := mul_le_mul_of_nonneg_right hspike hZc
      nlinarith [h]
    nlinarith [hbase, hbulk, hsp]
  have hfin : Real.sqrt (‖u‖ ^ 2) ≤ Real.sqrt
      ((2 * (A ^ 2 * intNatAbsPowTotal (2 * θ)) + 2 * (B ^ 2 * intNatAbsPowTotal (2 * c)))
        * (1 + (I : ℝ)) ^ (2 * ρ)) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg u)] at hfin
  refine le_trans hfin (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity)]
  congr 1
  have hrw : (1 + (I : ℝ)) ^ (2 * ρ) = ((1 + (I : ℝ)) ^ ρ) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + (I : ℝ)) ^ ρ) 2, ← Real.rpow_mul hIpos.le]
    congr 1
    push_cast
    ring
  rw [hrw, Real.sqrt_sq (Real.rpow_nonneg hIpos.le ρ)]

/-! ## The inner four factors of the principal step keep the class -/

set_option maxHeartbeats 1000000 in
/-- **The inner part of the principal step keeps the tied class.**  Dropping the outermost prime
symbol removes one `ε` of exponent loss *and* the constraint `c + 1/m < 1`: only the two inner
symbol steps need the spike exponent below one, and they see it at `c + 1/(2m)`. -/
theorem exists_gaussClass_principalStepInner (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {θ c ε : ℝ} (hc0 : 0 < c) (hcm : c + 1 / (2 * (m : ℝ)) < 1) (hθ1 : θ ≤ 1) (hε0 : 0 < ε)
    (h2ε : 2 * ε < θ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ (I : ℕ), 2 ≤ I →
      ∀ f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
          (fun j => fourierCoeff ((f : AddCircle (1 : ℝ) → ℂ)) j) →
      TwoPieceAmplitude A' (θ - 2 * ε) (B' / (1 + (I : ℝ)) ^ (θ - 2 * ε)) (c + 1 / (m : ℝ)) I
        (fun j => fourierCoeff ((gaussShiftedBlockDiag hm k p (I : ℤ)
          (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p (I : ℤ)
            (gaussPrimeScaleBlock hp f))) : AddCircle (1 : ℝ) → ℂ)) j) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hhalf : (1 : ℝ) / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by
    field_simp
    ring
  have hhalf0 : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  have hc1 : c < 1 := by linarith
  set c2 : ℝ := c + 1 / (2 * (m : ℝ)) with hc2def
  have hc20 : 0 < c2 := by rw [hc2def]; linarith
  have hc21 : c2 < 1 := by rw [hc2def]; exact hcm
  obtain ⟨A1, B1, hA1, hB1, hstep1⟩ := exists_gaussClass_primeScale_step hp hc0 hc1 hθ1 hε0
    (by linarith : ε < θ) A B hA hB
  set A2 : ℝ := Real.sqrt (1 + 2 * K) * A1 with hA2def
  set B2 : ℝ := (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (2 * A1 + B1) with hB2def
  have hA20 : 0 ≤ A2 := by rw [hA2def]; positivity
  have hB20 : 0 ≤ B2 := by
    rw [hB2def]
    have : (0 : ℝ) ≤ (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) := Real.rpow_nonneg (by positivity) _
    positivity
  obtain ⟨A3, B3, hA3, hB3, hstep3⟩ := exists_gaussClass_primeScaleInvSq_step hp hc20 hc21
    (by linarith : θ - ε ≤ 1) hε0 (by linarith : ε < θ - ε) A2 B2 hA20 hB20
  set A4 : ℝ := Real.sqrt (1 + 2 * K) * A3 with hA4def
  set B4 : ℝ := (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (2 * A3 + B3) with hB4def
  have hA40 : 0 ≤ A4 := by rw [hA4def]; positivity
  have hB40 : 0 ≤ B4 := by
    rw [hB4def]
    have : (0 : ℝ) ≤ (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) := Real.rpow_nonneg (by positivity) _
    positivity
  refine ⟨A4, B4, hA40, hB40, fun I hI f hf => ?_⟩
  have hI1 : 1 ≤ I := by omega
  have h1 := hstep1 I hI1 f hf
  have h2 := gaussClass_shiftedBlockOf_step hm k p hK hKb hA1 hB1
    (by linarith : (0 : ℝ) ≤ θ - ε) (by linarith : θ - ε ≤ 1) hc0 hI _ h1
  have h3 := hstep3 I hI1 _ h2
  have h4 := gaussClass_shiftedBlockDiag_step hm k p hK hKb hA3 hB3
    (by linarith : (0 : ℝ) ≤ θ - ε - ε) (by linarith : θ - ε - ε ≤ 1) hc20 hI _ h3
  have hθrw : θ - ε - ε = θ - 2 * ε := by ring
  have hcrw : c2 + 1 / (2 * (m : ℝ)) = c + 1 / (m : ℝ) := by
    rw [hc2def]
    linarith [hhalf]
  rw [hθrw, hcrw] at h4
  exact h4

/-! ## The `m`-th iterate grows slower than every power -/

set_option maxHeartbeats 2000000 in
/-- **The iterated principal step at the critical order is almost bounded.**  For every `ρ > 0`
there is a constant with `‖R_I^m 1‖ ≤ C (1+I)^ρ`. -/
theorem exists_norm_gaussPrincipalStep_pow_le (hm : 1 ≤ m) (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ I : ℕ, 2 ≤ I →
      ‖(gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ m)
          (fourierLp 2 (0 : ℤ))‖ ≤ Cn * (1 + (I : ℝ)) ^ ρ := by
  have hM2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm k p
  set c₀ : ℝ := min (ρ / 2) (1 / (4 * (m : ℝ))) with hc₀def
  set ε : ℝ := min (ρ / (2 * (3 * (m : ℝ) + 2))) (1 / (24 * (m : ℝ) ^ 2)) with hεdef
  have hc₀0 : 0 < c₀ := lt_min (by linarith) (by positivity)
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hc₀ρ : c₀ ≤ ρ / 2 := min_le_left _ _
  have hc₀m : c₀ ≤ 1 / (4 * (m : ℝ)) := min_le_right _ _
  have hερ : ε ≤ ρ / (2 * (3 * (m : ℝ) + 2)) := min_le_left _ _
  have hεm : ε ≤ 1 / (24 * (m : ℝ) ^ 2) := min_le_right _ _
  set r : ℕ := m - 1 with hrdef
  have hr : r + 1 = m := by omega
  have hrR : (r : ℝ) = (m : ℝ) - 1 := by
    have h : (r : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hr
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- numeric budget
  have h3M1 : (0 : ℝ) ≤ 3 * (m : ℝ) - 1 := by linarith
  have hkey1 : (3 * (m : ℝ) - 1) * ε ≤ 1 / 16 := by
    have h4 : (3 * (m : ℝ) - 1) * ε ≤ (3 * (m : ℝ) - 1) * (1 / (24 * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hεm h3M1
    have h5 : (3 * (m : ℝ) - 1) * (1 / (24 * (m : ℝ) ^ 2)) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hM2, sq_nonneg ((m : ℝ) - 2)]
    linarith
  have hkey2 : 2 * c₀ + 2 * ((3 * (m : ℝ) - 1) * ε) ≤ 2 * ρ := by
    have h4 : (3 * (m : ℝ) - 1) * ε
        ≤ (3 * (m : ℝ) - 1) * (ρ / (2 * (3 * (m : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hερ h3M1
    have hid : (3 * (m : ℝ) - 1) * (ρ / (2 * (3 * (m : ℝ) + 2)))
        = ((3 * (m : ℝ) - 1) * ρ) / (2 * (3 * (m : ℝ) + 2)) := by ring
    have h5 : ((3 * (m : ℝ) - 1) * ρ) / (2 * (3 * (m : ℝ) + 2)) ≤ ρ / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hρ.le, hM2]
    rw [hid] at h4
    linarith
  have hc₀half : c₀ < 1 / (2 * (m : ℝ)) := by
    have h1 : (1 : ℝ) / (4 * (m : ℝ)) < 1 / (2 * (m : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  -- the class hypotheses
  have hrc : c₀ + (r : ℝ) / (m : ℝ) < 1 := by
    rw [hrR]
    have hid : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by field_simp
    rw [hid]
    have h2 : (1 : ℝ) / (4 * (m : ℝ)) < 1 / (m : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have hrε : 3 * (r : ℝ) * ε < 1 := by
    have h1 : 3 * (r : ℝ) * ε ≤ (3 * (m : ℝ) - 1) * ε := by
      rw [hrR]
      nlinarith [hε0.le, hM2]
    linarith
  obtain ⟨A0, B0, hA0, hB0, hcl0⟩ := exists_gaussClass_principalStep_pow hm k p hp hK hKb
    hc₀0 hε0 r hrc hrε
  have hc0' : (0 : ℝ) < c₀ + (r : ℝ) / (m : ℝ) := by positivity
  have hcm' : c₀ + (r : ℝ) / (m : ℝ) + 1 / (2 * (m : ℝ)) < 1 := by
    rw [hrR]
    have hid : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by field_simp
    rw [hid]
    have hid2 : (1 : ℝ) / (2 * (m : ℝ)) = (1 / (m : ℝ)) / 2 := by
      field_simp
    rw [hid2]
    have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith [hc₀half, hid2]
  have hθ1' : (1 : ℝ) - 3 * (r : ℝ) * ε ≤ 1 := by nlinarith [hε0.le, hr0]
  have h2ε' : 2 * ε < 1 - 3 * (r : ℝ) * ε := by
    have h1 : 3 * (r : ℝ) * ε + 2 * ε ≤ (3 * (m : ℝ) - 1) * ε := by
      rw [hrR]
      nlinarith [hε0.le]
    linarith
  obtain ⟨A1, B1, hA1, hB1, hinner⟩ := exists_gaussClass_principalStepInner hm k p hp hK hKb
    (θ := 1 - 3 * (r : ℝ) * ε) (c := c₀ + (r : ℝ) / (m : ℝ)) (ε := ε)
    hc0' hcm' hθ1' hε0 h2ε' A0 B0 hA0 hB0
  -- the exponents for the `L²` bound
  set θ' : ℝ := 1 - 3 * (r : ℝ) * ε - 2 * ε with hθ'def
  set c' : ℝ := c₀ + (r : ℝ) / (m : ℝ) + 1 / (m : ℝ) with hc'def
  have hθ'half : (1 : ℝ) / 2 < θ' := by
    rw [hθ'def]
    have h1 : 3 * (r : ℝ) * ε + 2 * ε ≤ (3 * (m : ℝ) - 1) * ε := by
      rw [hrR]
      nlinarith [hε0.le]
    linarith
  have hc'half : (1 : ℝ) / 2 < c' := by
    rw [hc'def, hrR]
    have hid : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by field_simp
    rw [hid]
    linarith
  have hρbound : 2 * c' - 2 * θ' ≤ 2 * ρ := by
    rw [hc'def, hθ'def, hrR]
    have hid : ((m : ℝ) - 1) / (m : ℝ) = 1 - 1 / (m : ℝ) := by field_simp
    rw [hid]
    have hkey1' : 2 * c₀ + 2 * ((3 * (m : ℝ) - 1) * ε) ≤ 2 * ρ := hkey2
    nlinarith [hkey1', hrR]
  refine ⟨Real.sqrt (p : ℝ) * Real.sqrt (2 * (A1 ^ 2 * intNatAbsPowTotal (2 * θ'))
      + 2 * (B1 ^ 2 * intNatAbsPowTotal (2 * c'))), by positivity, fun I hI => ?_⟩
  have hXcl := hinner I hI _ (hcl0 I hI)
  have hXnorm := norm_le_of_tiedTwoPieceAmplitude hA1 hB1 hθ'half hc'half hρ.le hρbound hXcl
  set v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    (gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ r) (fourierLp 2 (0 : ℤ)) with hvdef
  set X : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockDiag hm k p (I : ℤ) (gaussPrimeScaleInvSqBlock hp
      (gaussShiftedBlockOf hm k p (I : ℤ) (gaussPrimeScaleBlock hp v))) with hXdef
  set W : ℝ := Real.sqrt (2 * (A1 ^ 2 * intNatAbsPowTotal (2 * θ'))
    + 2 * (B1 ^ 2 * intNatAbsPowTotal (2 * c'))) with hWdef
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hpow : (gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ m)
      = gaussPrincipalStepBlock hm k p hp (I : ℤ)
        * (gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ r) := by
    rw [← pow_succ', hr]
  have hstep : ‖gaussPrimeScaleBlock hp X‖ ≤ Real.sqrt (p : ℝ) * ‖X‖ := by
    refine le_trans ((gaussPrimeScaleBlock hp).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleBlock_le hp) (norm_nonneg _)
  have hXle : ‖X‖ ≤ W * (1 + (I : ℝ)) ^ ρ := hXnorm
  have hgoal : ‖gaussPrimeScaleBlock hp X‖ ≤ Real.sqrt (p : ℝ) * W * (1 + (I : ℝ)) ^ ρ := by
    refine le_trans hstep ?_
    have := mul_le_mul_of_nonneg_left hXle (Real.sqrt_nonneg ((p : ℝ)))
    calc Real.sqrt (p : ℝ) * ‖X‖ ≤ Real.sqrt (p : ℝ) * (W * (1 + (I : ℝ)) ^ ρ) := this
      _ = Real.sqrt (p : ℝ) * W * (1 + (I : ℝ)) ^ ρ := by ring
  rw [hpow]
  show ‖gaussPrincipalStepBlock hm k p hp (I : ℤ) v‖ ≤ _
  rw [gaussPrincipalStepBlock_apply]
  exact hgoal

end

end RHTower
