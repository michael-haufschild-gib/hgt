import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAmplitudeEnvelope

/-!
# Selected-factor cancellation in Menon's Case II

The common Case-II amplitude carries the selected factor to the power `sigma - 1`, while the
complementary Montgomery energy carries the erased product to the powers `1 - 2 * sigma` and
`2 - 2 * sigma`.  Multiplying by the reciprocal selected-factor power combines these into the
full Heath--Brown box scale.  Window relevance then replaces that scale by the physical lower
endpoint, with only the exact degree-three dyadic loss `2^(2 * 3) = 64`.
-/

namespace RHTower.Sieve

noncomputable section

/-- The selected factor cancels against the complementary energy, leaving only the full product
at exponent `2 - 2 * sigma`. -/
theorem menonHeathBrownCaseII_cancel_selectedFactor
    {F B G N A a sigma T : ℝ}
    (hB : 0 ≤ B) (hN : 0 < N) (hA : 0 < A) (ha : 0 < a)
    (hT : 0 ≤ T) (hsigma : 1 ≤ sigma)
    (hprod : a / 64 ≤ N * A)
    (h : F * (G * N ^ (sigma - 1)) ^ 2 ≤
      B * (T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma))) :
    F * G ^ 2 ≤
      B * (T / A + 1) * (a / 64) ^ (2 - 2 * sigma) := by
  have hNpow : 0 ≤ N ^ (2 - 2 * sigma) := Real.rpow_nonneg hN.le _
  have hscaled := mul_le_mul_of_nonneg_right h hNpow
  have hcancel : (N ^ (sigma - 1)) ^ 2 * N ^ (2 - 2 * sigma) = 1 := by
    rw [← Real.rpow_natCast (N ^ (sigma - 1)) 2, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    convert Real.rpow_zero N using 1
    ring_nf
  have hleft : F * (G * N ^ (sigma - 1)) ^ 2 * N ^ (2 - 2 * sigma) =
      F * G ^ 2 := by
    calc
      F * (G * N ^ (sigma - 1)) ^ 2 * N ^ (2 - 2 * sigma) =
          F * G ^ 2 * ((N ^ (sigma - 1)) ^ 2 * N ^ (2 - 2 * sigma)) := by ring
      _ = F * G ^ 2 := by rw [hcancel, mul_one]
  have hAshift : A ^ (1 - 2 * sigma) = A ^ (2 - 2 * sigma) / A := by
    rw [show 1 - 2 * sigma = (2 - 2 * sigma) - 1 by ring,
      Real.rpow_sub hA, Real.rpow_one]
  have hcombine :
      (T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma)) * N ^ (2 - 2 * sigma) =
        (T / A + 1) * (N * A) ^ (2 - 2 * sigma) := by
    rw [hAshift, Real.mul_rpow hN.le hA.le]
    field_simp
  have hbase : (N * A) ^ (2 - 2 * sigma) ≤ (a / 64) ^ (2 - 2 * sigma) := by
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hprod (by linarith)
  rw [hleft, mul_assoc, hcombine] at hscaled
  have hfac0 : 0 ≤ B * (T / A + 1) := mul_nonneg hB (by positivity)
  exact hscaled.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hfac0)

/-- Window relevance makes the common Case-II fibre bound uniform at the physical lower endpoint.
The complete `min(T,N^delta)` gain remains in `G`; no receiver branch or complementary power is
discarded. -/
theorem windowRelevant_menonHeathBrownCaseII_baseAmplitude_fibreBound
    {L X cells : ℕ} {a sigma Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    (ha : 0 < a) (hX : 1 ≤ X) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hbox : IsHeathBrownBoxWindowRelevant a X 3 label.box)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    (hreceiver :
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
        MenonHeathBrownCaseIIZetaOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
        MenonHeathBrownCaseIILogOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      MenonHeathBrownCaseIIDerivativeTwentySixBound
        L X cells S color sigma Δ Q T label)
    (hsigma : 1 ≤ sigma) :
    let N : ℝ :=
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let A : ℝ := (groupedDyadicLower q : ℝ)
    let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
    let G : ℝ := min T (N ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) *
      menonHeathBrownCaseIICoreThreshold L X Q
    ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) * G ^ 2 ≤
      (12 * W ^ 2 *
          (1 + Real.log (W * (X : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T / A + 1) * (a / 64) ^ (2 - 2 * sigma) := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
    i ∈ (Finset.univ.erase label.factor)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  let G : ℝ := min T (N ^ maynardDerivativeDeficit 26) /
      (5120 * maynardLongPolylogEnvelope X) *
    menonHeathBrownCaseIICoreThreshold L X Q
  let B : ℝ := 12 * W ^ 2 *
    (1 + Real.log (W * (X : ℝ))) ^
      (menonHeathBrownCaseIIComplementPolylogExponent + 2)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hA : 0 < A := by
    dsimp only [A]
    exact_mod_cast Nat.zero_lt_of_lt (one_le_groupedDyadicLower q)
  have hW : 1 ≤ W := by
    dsimp only [W, menonHeathBrownCaseIIComplementWidthConstant]
    norm_num
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ Real.log (W * (X : ℝ)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hW hXR)
    positivity
  have hprodNat :=
    groupedDyadicLower_heathBrownBoxFactorExponent_eq_factor_mul_complement
      label.box label.factor
  have hprodEq :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q) : ℝ) = N * A := by
    simpa only [N, A, q, I, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) hprodNat
  have hprodLower := windowRelevant_heathBrownBox_coreLower_gt hbox
  have hprod : a / 64 ≤ N * A := by
    rw [show (2 ^ (2 * 3) : ℝ) = 64 by norm_num, hprodEq] at hprodLower
    exact hprodLower.le
  have hraw := windowRelevant_menonHeathBrownCaseII_commonAmplitude_fibreBound
    hX hT hΔ hΔT hthreshold label hbox hkind hreceiver
  apply menonHeathBrownCaseII_cancel_selectedFactor
    hB hN hA ha (zero_le_one.trans hT) hsigma hprod
  simpa only [menonHeathBrownCaseIICommonAmplitude, N, I, q, A, W, G, B,
    mul_assoc] using hraw

end

end RHTower.Sieve
