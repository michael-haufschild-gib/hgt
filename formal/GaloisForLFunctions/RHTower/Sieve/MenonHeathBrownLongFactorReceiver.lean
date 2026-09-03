import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver
import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauFactor

/-!
# Menon's long Heath--Brown factor receiver

The first-derivative estimate is specialized to literal zeta and logarithm atoms of an arbitrary
Heath--Brown box.  Excising that atom and applying complementary Montgomery gives the exact
finite separated-frequency count, including all coefficient-energy and polylogarithmic factors.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A literal zeta atom above the ordinate height carries the full reciprocal-height saving. -/
theorem norm_heathBrownBoxFactorValue_zeta_le_over_height
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m i = .zeta)
    (hX : 1 ≤ X) {T sigma t : ℝ} (hT : 0 < T) (hsigma : 0 ≤ sigma)
    (hTt : T ≤ t) (htupper : t ≤ 2 * T)
    (hTN : T ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) :
    ‖heathBrownBoxFactorValue L X k box
        ((sigma : ℂ) + (t : ℝ) * Complex.I) i‖ ≤
      (6 * Real.pi + 1) / T *
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
          (1 - sigma) := by
  have hq := box.factorExponent_le_log_X_of_zeta_or_log i (Or.inl hkind)
  rcases i with i | i
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases i with i | i
    · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase] using
        norm_LSeries_zetaDyadicBlock_le_over_height hX hq hT hsigma hTt htupper hTN
    · simp [heathBrownBoxFactorKind] at hkind

/-- A literal logarithm atom above the ordinate height carries the same reciprocal-height saving,
with its single explicit logarithmic envelope. -/
theorem norm_heathBrownBoxFactorValue_log_le_over_height
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m i = .log)
    (hX : 1 ≤ X) {T sigma t : ℝ} (hT : 0 < T) (hsigma : 0 ≤ sigma)
    (hTt : T ≤ t) (htupper : t ≤ 2 * T)
    (hTN : T ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) :
    ‖heathBrownBoxFactorValue L X k box
        ((sigma : ℂ) + (t : ℝ) * Complex.I) i‖ ≤
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X / T *
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
          (1 - sigma) := by
  have hq := box.factorExponent_le_log_X_of_zeta_or_log i (Or.inr hkind)
  rcases i with i | i
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases i with i | i
    · simp [heathBrownBoxFactorKind] at hkind
    · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase] using
        norm_LSeries_logDyadicBlock_le_over_height hX hq hT hsigma hTt htupper hTN

/-- Long-zeta Case II receiver: the distinguished atom is discharged internally and the exact
erase-complement is paid by Montgomery mean square. -/
theorem derivativeExcised_montgomery_heathBrownBox_zeta_overHeight
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta) (hX : 1 ≤ X)
    {c : ℝ} (hc : 0 ≤ c)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    (hdelta : 0 < delta) (hH : 0 ≤ H)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ H)
    {D T0 alpha : ℝ} (hD : 0 < D) (hT0 : 0 < T0)
    (hordinate : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (hTN : T0 ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hlarge : ∀ r ∈ S, D ^ (alpha - c) ≤
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    let I := {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (S.card : ℝ) *
        (((T0 / (6 * Real.pi + 1)) * D ^ (alpha - c) *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            (c - 1)) ^ 2) ≤
      (H + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  apply derivativeExcised_montgomery_heathBrownBox_fixedPolylog box j hc hdelta hH
    hgap hband hD (by positivity) hT0 (by positivity)
  · intro r hr
    exact norm_heathBrownBoxFactorValue_zeta_le_over_height box j hkind hX hT0 hc
      (hordinate r hr).1 (hordinate r hr).2 hTN
  · exact hlarge

/-- Long-logarithm Case II receiver, with the sole logarithmic factor retained explicitly. -/
theorem derivativeExcised_montgomery_heathBrownBox_log_overHeight
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .log) (hX : 1 ≤ X)
    {c : ℝ} (hc : 0 ≤ c)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    (hdelta : 0 < delta) (hH : 0 ≤ H)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ H)
    {D T0 alpha : ℝ} (hD : 0 < D) (hT0 : 0 < T0)
    (hordinate : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (hTN : T0 ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hlarge : ∀ r ∈ S, D ^ (alpha - c) ≤
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    let C := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
    let I := {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (S.card : ℝ) *
        (((T0 / C) * D ^ (alpha - c) *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            (c - 1)) ^ 2) ≤
      (H + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  have hC : 0 < 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X :=
    mul_pos (mul_pos (by norm_num) (by positivity))
      (zero_lt_one.trans_le (one_le_maynardLongPolylogEnvelope X))
  apply derivativeExcised_montgomery_heathBrownBox_fixedPolylog box j hc hdelta hH
    hgap hband hD (by positivity) hT0 hC
  · intro r hr
    exact norm_heathBrownBoxFactorValue_log_le_over_height box j hkind hX hT0 hc
      (hordinate r hr).1 (hordinate r hr).2 hTN
  · exact hlarge

end


end RHTower.Sieve
