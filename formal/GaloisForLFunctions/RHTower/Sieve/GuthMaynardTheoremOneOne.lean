import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropAssembly
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneZeta
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropElevenTwo

/-!
# Guth–Maynard Theorem 1.1

The large values estimate

`R ⪅ N²V⁻² + N^{18/5}V⁻⁴ + T N^{12/5}V⁻⁴`

for a `1`-separated set of ordinates in an interval of length `T` on which a Dirichlet polynomial of
length `N` with coefficients bounded by one is at least `V`.

This module supplies the two `S`-bounds that the Proposition 3.1 assembly consumes — Proposition 6.1
for `ζ` at `(j, k) = (4, 2)` and Proposition 11.2 — and discharges the large values datum.  The
bookkeeping is: shrink `ε` so that the `T^{9ε}` of Proposition 6.1 fits inside `T^ε`, weaken the
separation hypothesis (`IsSeparated` is antitone in its parameter), and read the natural powers of
Proposition 6.1 as real powers.
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard

open Finset

noncomputable section

/-- `S₂` vanishes on the empty point set: every `I_m` is a triple sum over `W`. -/
theorem gmS2_empty (w : CGLRealSmoothBump) (N : ℝ) : gmS2 w N ∅ = 0 := by
  have h : ∀ m : {m : (ℤ × ℤ) × ℤ // gmS2Frequency m}, gmIm w N ∅ (m : (ℤ × ℤ) × ℤ) = 0 := by
    intro m
    simp [cubicTerm]
  rw [gmS2, tsum_congr h, tsum_zero]

/-- **Proposition 6.1 for `ζ`** in the shape the Proposition 3.1 assembly consumes, `j = 4`,
`k = 2`.  The middle exponent `2 − 1/(2k)` of `prop61_zeta` is `2 − 1/4` at `k = 2`. -/
theorem propSixOneBound_zeta : PropSixOneBound cglStandardBump.toCGLRealSmoothBump 4 2 := by
  intro ε hε
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = min (ε / 9) 1 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; exact lt_min (by positivity) one_pos
  have he1 : e ≤ 1 := by rw [hedef]; exact min_le_right _ _
  have he9 : 9 * e ≤ ε := by
    have : e ≤ ε / 9 := by rw [hedef]; exact min_le_left _ _
    linarith
  have heε : e ≤ ε := by linarith
  obtain ⟨C, hC, hbound⟩ :=
    prop61_zeta cglStandardBump.toCGLRealSmoothBump he0 he1 (k := 2) (by norm_num)
  refine ⟨C, hC, fun T N W hT hN hNT hWmem hsep => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hcard0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  -- the three bracket terms, in the real-power form of `PropSixOneBound`
  obtain ⟨Br, hBr⟩ : ∃ Br : ℝ, Br = (W.card : ℝ) ^ (2 : ℝ) * N ^ (2 : ℝ) +
      T * N * (W.card : ℝ) ^ (2 - 1 / ((4 : ℕ) : ℝ)) +
      N ^ (2 : ℝ) * (W.card : ℝ) ^ (2 - 3 / (4 * ((2 : ℕ) : ℝ))) *
        T ^ (1 / (2 * ((2 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hBr0 : 0 ≤ Br := by
    rw [hBr]
    have t1 : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 : ℝ) * N ^ (2 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hcard0 _) (Real.rpow_nonneg hN0.le _)
    have t2 : (0 : ℝ) ≤ T * N * (W.card : ℝ) ^ (2 - 1 / ((4 : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg hT0.le hN0.le) (Real.rpow_nonneg hcard0 _)
    have t3 : (0 : ℝ) ≤ N ^ (2 : ℝ) * (W.card : ℝ) ^ (2 - 3 / (4 * ((2 : ℕ) : ℝ))) *
        T ^ (1 / (2 * ((2 : ℕ) : ℝ))) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hcard0 _))
        (Real.rpow_nonneg hT0.le _)
    linarith
  rw [← hBr]
  rcases W.eq_empty_or_nonempty with hW0 | hWne
  · -- the empty set: both sides vanish
    subst hW0
    rw [gmS2_empty, norm_zero]
    have : (0 : ℝ) ≤ C * T ^ ε := mul_nonneg hC (Real.rpow_nonneg hT0.le _)
    exact mul_nonneg this hBr0
  -- weaken the separation and transport the membership
  have hsep' : IsSeparated (T ^ e) W :=
    hsep.mono (Real.rpow_le_rpow_of_exponent_le hT1 heε)
  have hmem' : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T := fun t ht => Set.mem_Icc.mp (hWmem t ht)
  have h := hbound T N W hT hN hNT hsep' hmem' hWne
  -- the natural powers of `prop61_zeta` are the real powers of `PropSixOneBound`
  have e2c : (W.card : ℝ) ^ (2 : ℕ) = (W.card : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast (W.card : ℝ) 2]; norm_num
  have e2N : N ^ (2 : ℕ) = N ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast N 2]; norm_num
  have ecast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have hbr' : N ^ (2 : ℕ) * (W.card : ℝ) ^ (2 : ℕ)
      + T * N * (W.card : ℝ) ^ (2 - 1 / (2 * ((2 : ℕ) : ℝ)))
      + N ^ (2 : ℕ) * (W.card : ℝ) ^ (2 - 3 / (4 * ((2 : ℕ) : ℝ)))
        * T ^ (1 / (2 * ((2 : ℕ) : ℝ))) = Br := by
    rw [hBr, e2c, e2N, ecast]
    norm_num
    ring
  rw [hbr'] at h
  -- absorb `T^{9e}` into `T^ε`
  have hpow : T ^ (9 * e) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 he9
  have hCB : (0 : ℝ) ≤ C * Br := mul_nonneg hC hBr0
  calc ‖gmS2 cglStandardBump.toCGLRealSmoothBump N W‖
      ≤ C * T ^ (9 * e) * Br := h
    _ ≤ C * T ^ ε * Br := by
        have := mul_le_mul_of_nonneg_left hpow hC
        nlinarith [hBr0, this]

/-- `S₃` vanishes on the empty point set. -/
theorem allNonzeroCubicSum_empty (w : CGLSmoothBump) (N : ℝ) :
    allNonzeroCubicSum w ∅ N = 0 := by
  rw [allNonzeroCubicSum]
  have h : ∀ m : ℤ × ℤ × ℤ,
      (if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then cubicTerm w ∅ N m.1 m.2.1 m.2.2 else 0)
        = 0 := by
    intro m; split <;> simp [cubicTerm]
  rw [tsum_congr h, tsum_zero]

/-- **Proposition 11.2** in the shape the Proposition 3.1 assembly consumes.  The assembly asks for
`T^ε`-separated point sets, which are in particular `1`-separated; the `T^{-100}` tail of
Proposition 11.2 is absorbed because the bracket is at least one on a nonempty point set. -/
theorem propElevenTwoBound_zeta : PropElevenTwoBound cglStandardBump.toCGLRealSmoothBump := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := guthMaynard_prop112 cglStandardBump.toCGLRealSmoothBump hε
  refine ⟨C + C, by linarith, fun N σ T b W hT hNT hNle hb hWmem hsep hD => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hcard0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hTε1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  obtain ⟨Br, hBr⟩ : ∃ Br : ℝ, Br = T ^ (2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) +
      T * W.card * (N : ℝ) ^ (3 - 2 * σ) +
      T * (W.card : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) := ⟨_, rfl⟩
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
    linarith
  have t1 : (0 : ℝ) ≤ T ^ (2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hcard0 _)
  have t2 : (0 : ℝ) ≤ T * W.card * (N : ℝ) ^ (3 - 2 * σ) :=
    mul_nonneg (mul_nonneg hT0.le hcard0) (Real.rpow_nonneg hN0.le _)
  have t3 : (0 : ℝ) ≤ T * (W.card : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) :=
    mul_nonneg (mul_nonneg hT0.le (Real.rpow_nonneg hcard0 _)) (Real.rpow_nonneg hN0.le _)
  have t4 : (0 : ℝ) ≤ T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hcard0 _))
      (Real.rpow_nonneg hN0.le _)
  have hBr0 : 0 ≤ Br := by rw [hBr]; linarith
  rw [← hBr]
  rcases W.eq_empty_or_nonempty with hW0 | hWne
  · subst hW0
    rw [allNonzeroCubicSum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hT0.le _)) hBr0
  have hsep1 : IsSeparated 1 W := hsep.mono hTε1
  have h := hbound N b σ W T hT hNT hNle hb hWmem hsep1 hD
  -- the first bracket term is at least one
  have hcard1 : (1 : ℝ) ≤ (W.card : ℝ) := by
    have : 1 ≤ W.card := Finset.card_pos.mpr hWne
    exact_mod_cast this
  have hBr1 : (1 : ℝ) ≤ Br := by
    have hA : (1 : ℝ) ≤ T ^ (2 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
    have hB : (1 : ℝ) ≤ (W.card : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hcard1 (by norm_num)
    have : (1 : ℝ) ≤ T ^ (2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) := one_le_mul_of_one_le_of_one_le hA hB
    rw [hBr]; linarith
  -- rewrite the natural powers of Proposition 11.2 as real powers
  have eT2 : T ^ (2 : ℕ) = T ^ (2 : ℝ) := by rw [← Real.rpow_natCast T 2]; norm_num
  have ec2 : (W.card : ℝ) ^ (2 : ℕ) = (W.card : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast (W.card : ℝ) 2]; norm_num
  have ec32 : (W.card : ℝ) * Real.sqrt (W.card : ℝ) = (W.card : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : (0 : ℝ) < (W.card : ℝ)), Real.rpow_one]
  have hbr' : T ^ (2 : ℕ) * W.card * Real.sqrt (W.card : ℝ) +
      T * W.card * (N : ℝ) ^ (3 - 2 * σ) +
      T * (W.card : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (3 / 2 - σ) +
      T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) = Br := by
    rw [hBr, eT2, ec2, ← ec32]; ring
  rw [hbr'] at h
  have habs : C * T ^ (-100 : ℝ) ≤ C * T ^ ε * Br := by
    have h1 : T ^ (-100 : ℝ) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have h2 : C * T ^ (-100 : ℝ) ≤ C * T ^ ε := mul_le_mul_of_nonneg_left h1 hC
    have h3 : C * T ^ ε ≤ C * T ^ ε * Br := by
      have : (0 : ℝ) ≤ C * T ^ ε := mul_nonneg hC (Real.rpow_nonneg hT0.le _)
      nlinarith [hBr1, this]
    linarith
  have : C * T ^ ε * Br + C * T ^ ε * Br = (C + C) * T ^ ε * Br := by ring
  linarith [h, habs, this]

/-- **Guth–Maynard Theorem 1.1**, unconditionally. -/
theorem guthMaynardLargeValuesBound_holds : GuthMaynardLargeValuesBound :=
  guthMaynardLargeValuesBound_of_S_bounds (le_refl 2) propSixOneBound_zeta propElevenTwoBound_zeta

end

end RHTower.GuthMaynard
