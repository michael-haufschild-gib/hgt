import GaloisForLFunctions.RHTower.ZetaTwoShiftContraction
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.RHTower.ProjectiveHorizonWardSeam
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth

/-!
# Paper certificate: the completed Möbius contraction has the reciprocal projective Ward connection

Formal certificate for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-squarefree-reciprocal-projective-transfer.md`.

Writing `s` for the complex Laplace parameter of the paper, the certified statements are

```text
(1)  tau_sigma(s) = zeta(2 sigma)/(zeta(sigma) zeta(s)) ,
(2)  c_sigma(s)   = zeta(2s)/zeta(2 sigma)  is holomorphic and nonvanishing on Re s > 1/2,
                    and |c_sigma(s)| <= 1 on Re s >= sigma,
(3)  M_sigma(s)   = c_sigma(s) tau_sigma(s) = 1/(zeta(sigma) Z_sq(s)) ,
(4)  X_sq(s)      = Xi(s)/zeta(2s) = C(s) Z_sq(s) ,
(5)  T_sigma(s)   = C(s)^{-1} M_sigma(s) = 1/(zeta(sigma) X_sq(s)) ,
(6)  2 dlog T_sigma = -2 X_sq'/X_sq = Q_sq ,
(7)  hence every source functional of the connection sees `Q_sq`; in particular the anti-causal
     component of `2 dlog T_sigma` is the anti-causal component of `Q_sq`.
(7a)/(7b) the safe correction is the Laplace multiplier of a positive average of logarithmic
     translation unitaries, hence a contraction, and its composition with the signed Möbius shift
     average is a contraction with multiplier `(3)`.
```

`Z_sq = squarefreePartition` and `Q_sq = completedSquarefreeFixedCurrent` are the corpus objects;
`C = archFactor` is the archimedean dressing of `Xi`.  No Xi zero or divisor packet enters.
-/

open Complex

noncomputable section
namespace RHTower

open GaloisForLFunctions

/-! ### A Dirichlet comparison bound -/

/-- On `Re s ≥ a > 1` the zeta values are dominated by the real value at the abscissa `a`. -/
theorem norm_riemannZeta_le_re_riemannZeta_ofReal
    {s : ℂ} {a : ℝ} (ha : 1 < a) (hs : a ≤ s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta (a : ℂ)).re := by
  have hsre : (1 : ℝ) < s.re := lt_of_lt_of_le ha hs
  have hare : (1 : ℝ) < ((a : ℂ)).re := by simpa using ha
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsre
    simp at hsre
    linarith
  have ha0 : (a : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hsumS : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    summable_one_div_nat_cpow.mpr hsre
  have hsumA : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (a : ℂ)) :=
    summable_one_div_nat_cpow.mpr ha
  have hzS : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
    zeta_eq_tsum_one_div_nat_cpow hsre
  have hzA : riemannZeta (a : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (a : ℂ) :=
    zeta_eq_tsum_one_div_nat_cpow hare
  have hterm : ∀ n : ℕ, ‖1 / (n : ℂ) ^ s‖ ≤ (1 / (n : ℂ) ^ (a : ℂ)).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Complex.zero_cpow hs0, Complex.zero_cpow ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hbase : ((n : ℂ)) ^ (a : ℂ) = (((n : ℝ) ^ a : ℝ) : ℂ) := by
        rw [ofReal_cpow (Nat.cast_nonneg n) a]
        push_cast
        ring
      have hre : (1 / (n : ℂ) ^ (a : ℂ)).re = 1 / (n : ℝ) ^ a := by
        rw [hbase, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [hre, norm_div, norm_one, norm_natCast_cpow_of_pos hn s]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos a)
        (Real.rpow_le_rpow_of_exponent_le hn1 hs)
  have hsumAre : Summable (fun n : ℕ => (1 / (n : ℂ) ^ (a : ℂ)).re) :=
    hsumA.mapL Complex.reCLM
  have hsumNorm : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumAre
  calc ‖riemannZeta s‖ = ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ := by rw [hzS]
    _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' n : ℕ, (1 / (n : ℂ) ^ (a : ℂ)).re :=
        Summable.tsum_mono hsumNorm hsumAre hterm
    _ = (riemannZeta (a : ℂ)).re := by rw [hzA, re_tsum hsumA]

/-! ### The paper objects in the complex Laplace parameter -/

/-- Card `(2)`: the squarefree higher-trace correction `c_sigma(s) = zeta(2s)/zeta(2 sigma)`. -/
def mobiusSafeCorrectionValue (sigma : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (2 * s) / riemannZeta (2 * (sigma : ℂ))

/-- Card `(1)`: the normalized signed Möbius Laplace multiplier. -/
def mobiusSignedSchurMultiplier (sigma : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (2 * (sigma : ℂ)) / (riemannZeta (sigma : ℂ) * riemannZeta s)

/-- Card `(3)`: the corrected transfer `M_sigma = c_sigma tau_sigma`. -/
def mobiusSquarefreeReciprocalTransferValue (sigma : ℝ) (s : ℂ) : ℂ :=
  mobiusSafeCorrectionValue sigma s * mobiusSignedSchurMultiplier sigma s

/-- Card `(4)`: the completed squarefree amplitude `X_sq(s) = Xi(s)/zeta(2s)`. -/
def completedSquarefreePartition (s : ℂ) : ℂ := xi s / riemannZeta (2 * s)

/-- Card `(5)`: the Gamma-completed Möbius transfer `T_sigma = C^{-1} M_sigma`. -/
def mobiusCompletedSquarefreeTransfer (sigma : ℝ) (s : ℂ) : ℂ :=
  (archFactor s)⁻¹ * mobiusSquarefreeReciprocalTransferValue sigma s

/-! ### Consistency with the already formalized real-frequency objects -/

theorem mobiusSafeCorrectionValue_eq_mobiusSquarefreeSafeCorrection (sigma x : ℝ) :
    mobiusSafeCorrectionValue sigma ((sigma + Real.pi * x : ℝ) : ℂ) =
      mobiusSquarefreeSafeCorrection sigma x := rfl

/-- Card `(1)`.  The already formalized causal Laplace multiplier of the signed Möbius shift is
exactly `tau_sigma`. -/
theorem infiniteMobiusLaplaceMultiplier_eq_mobiusSignedSchurMultiplier
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    infiniteMobiusLaplaceMultiplier sigma x =
      mobiusSignedSchurMultiplier sigma ((sigma + Real.pi * x : ℝ) : ℂ) :=
  infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigma hx

theorem mobiusSquarefreeReciprocalTransferValue_eq_transfer
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    mobiusSquarefreeReciprocalTransferValue sigma ((sigma + Real.pi * x : ℝ) : ℂ) =
      mobiusSquarefreeReciprocalTransfer sigma x := by
  rw [mobiusSquarefreeReciprocalTransferValue, mobiusSquarefreeReciprocalTransfer,
    mobiusSafeCorrectionValue_eq_mobiusSquarefreeSafeCorrection,
    infiniteMobiusLaplaceMultiplier_eq_mobiusSignedSchurMultiplier hsigma hx]

/-! ### Card `(2)`: the safe correction is holomorphic, nonvanishing, and contractive -/

private theorem two_mul_re {s : ℂ} : (2 * s).re = 2 * s.re := by simp

theorem differentiableAt_mobiusSafeCorrectionValue
    (sigma : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (mobiusSafeCorrectionValue sigma) s := by
  have h2 : 2 * s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [two_mul_re] at this
    simp at this
    linarith
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (differentiableAt_riemannZeta h2).comp s (by fun_prop)
  exact hcomp.div_const _

theorem mobiusSafeCorrectionValue_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : 1 / 2 < s.re) :
    mobiusSafeCorrectionValue sigma s ≠ 0 := by
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have h2sigma : 1 < (2 * (sigma : ℂ)).re := by
    rw [two_mul_re]
    simp
    linarith
  exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re h2)
    (riemannZeta_ne_zero_of_one_lt_re h2sigma)

/-- Card `(2)`, contractivity: on `Re s ≥ sigma` the safe correction has modulus at most one. -/
theorem norm_mobiusSafeCorrectionValue_le_one
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : sigma ≤ s.re) :
    ‖mobiusSafeCorrectionValue sigma s‖ ≤ 1 := by
  have hb : 1 < 2 * sigma := by linarith
  have hle : 2 * sigma ≤ (2 * s).re := by rw [two_mul_re]; linarith
  have hnum := norm_riemannZeta_le_re_riemannZeta_ofReal (a := 2 * sigma) hb hle
  have hcast : ((2 * sigma : ℝ) : ℂ) = 2 * (sigma : ℂ) := by push_cast; ring
  rw [hcast] at hnum
  have hden : (1 : ℝ) ≤ (riemannZeta (2 * (sigma : ℂ))).re := by
    have := one_le_re_riemannZeta_ofReal (2 * sigma) hb
    rwa [hcast] at this
  have hdenpos : (0 : ℝ) < (riemannZeta (2 * (sigma : ℂ))).re := by linarith
  have hnorm : (riemannZeta (2 * (sigma : ℂ))).re ≤ ‖riemannZeta (2 * (sigma : ℂ))‖ :=
    Complex.re_le_norm _
  have hnormpos : (0 : ℝ) < ‖riemannZeta (2 * (sigma : ℂ))‖ := by linarith
  rw [mobiusSafeCorrectionValue, norm_div, div_le_one hnormpos]
  linarith

/-! ### Cards `(3)`, `(4)`, `(5)` -/

/-- Card `(3)`.  The corrected transfer is the reciprocal completed squarefree partition, scaled by
the base normalization. -/
theorem mobiusSquarefreeReciprocalTransferValue_eq
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : 1 / 2 < s.re) (hz : riemannZeta s ≠ 0) :
    mobiusSquarefreeReciprocalTransferValue sigma s =
      (riemannZeta (sigma : ℂ) * squarefreePartition s)⁻¹ := by
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have h2sigma : 1 < (2 * (sigma : ℂ)).re := by
    rw [two_mul_re]; simp; linarith
  have hzs : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2
  have hz2sigma : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h2sigma
  rw [mobiusSquarefreeReciprocalTransferValue, mobiusSafeCorrectionValue,
    mobiusSignedSchurMultiplier, squarefreePartition]
  field_simp

/-- Card `(4)`.  The completed squarefree amplitude is the archimedean dressing times the raw
squarefree partition. -/
theorem completedSquarefreePartition_eq
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    completedSquarefreePartition s = archFactor s * squarefreePartition s := by
  rw [completedSquarefreePartition, squarefreePartition, xi_eq_archFactor_mul_zeta h0 h1 hG,
    mul_div_assoc]

/-- Card `(5)`.  The Gamma-completed transfer is the reciprocal completed squarefree amplitude. -/
theorem mobiusCompletedSquarefreeTransfer_eq
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : 1 / 2 < s.re) (h1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    mobiusCompletedSquarefreeTransfer sigma s =
      (riemannZeta (sigma : ℂ) * completedSquarefreePartition s)⁻¹ := by
  have hre : (0 : ℝ) < s.re := by linarith
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hArch : archFactor s ≠ 0 := archFactor_ne_zero h0 h1 hG
  have h2 : 1 < (2 * s).re := by rw [two_mul_re]; linarith
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2
  have hzs : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  rw [mobiusCompletedSquarefreeTransfer,
    mobiusSquarefreeReciprocalTransferValue_eq hsigma hs hz,
    completedSquarefreePartition_eq h0 h1 hG, squarefreePartition]
  field_simp

end RHTower

noncomputable section
namespace RHTower

open GaloisForLFunctions MeasureTheory

private theorem logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ}
    (h : f =ᶠ[nhds s] g) : logDeriv f s = logDeriv g s := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

private theorem div_mul_div_cancel_mid (A B C : ℂ) (hC : C ≠ 0) :
    A / C * (C / B) = A / B := by
  rcases eq_or_ne B 0 with hB | hB
  · subst hB; simp
  · field_simp

/-- The completed transfer as a single quotient, valid at every point. -/
theorem mobiusCompletedSquarefreeTransfer_eq_quotient
    {sigma : ℝ} (hsigma : 1 < sigma) :
    mobiusCompletedSquarefreeTransfer sigma =
      fun z : ℂ =>
        riemannZeta (2 * z) / (archFactor z * (riemannZeta (sigma : ℂ) * riemannZeta z)) := by
  have h2sigma : 1 < (2 * (sigma : ℂ)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith
  have hz2sigma : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h2sigma
  funext z
  rw [mobiusCompletedSquarefreeTransfer, mobiusSquarefreeReciprocalTransferValue,
    mobiusSafeCorrectionValue, mobiusSignedSchurMultiplier,
    div_mul_div_cancel_mid _ _ _ hz2sigma, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- The doubled-argument zeta has the doubled logarithmic derivative. -/
theorem logDeriv_riemannZeta_two_mul {s : ℂ} (h2 : 2 * s ≠ 1) :
    logDeriv (fun z : ℂ => riemannZeta (2 * z)) s = 2 * logDeriv riemannZeta (2 * s) := by
  have hchain := logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 2 * z)
    (differentiableAt_riemannZeta h2)
    (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)
  change logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
    logDeriv riemannZeta (2 * s) * deriv (fun z : ℂ => 2 * z) s at hchain
  have hderiv : deriv (fun z : ℂ => 2 * z) s = 2 := by simp
  rw [hderiv] at hchain
  linear_combination hchain

/-- **Card `(6)`.**  The doubled logarithmic connection of the completed Möbius transfer is exactly
the completed squarefree Ward current `Q_sq`. -/
theorem two_mul_logDeriv_mobiusCompletedSquarefreeTransfer
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : 1 < s.re) :
    2 * logDeriv (mobiusCompletedSquarefreeTransfer sigma) s =
      completedSquarefreeFixedCurrent s := by
  have hre : (0 : ℝ) < s.re := by linarith
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have h1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have h2re : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre2 := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re] at hre2
    linarith
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hArch : archFactor s ≠ 0 := archFactor_ne_zero h0 h1 hG
  have hzs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  have hzsigma : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hdArch : DifferentiableAt ℂ archFactor s :=
    (hasDerivAt_archFactor_of_re_pos hre).differentiableAt
  have hdZeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  have hdNum : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (differentiableAt_riemannZeta h2one).comp s (by fun_prop)
  have hdConstMul : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (sigma : ℂ) * riemannZeta z) s :=
    hdZeta.const_mul _
  have hdDen :
      DifferentiableAt ℂ (fun z : ℂ => archFactor z * (riemannZeta (sigma : ℂ) * riemannZeta z)) s :=
    hdArch.mul hdConstMul
  have hDen0 : archFactor s * (riemannZeta (sigma : ℂ) * riemannZeta s) ≠ 0 :=
    mul_ne_zero hArch (mul_ne_zero hzsigma hzs)
  have hConstMul0 : riemannZeta (sigma : ℂ) * riemannZeta s ≠ 0 := mul_ne_zero hzsigma hzs
  rw [mobiusCompletedSquarefreeTransfer_eq_quotient hsigma,
    logDeriv_div s hz2 hDen0 hdNum hdDen,
    logDeriv_mul s hArch hConstMul0 hdArch hdConstMul,
    logDeriv_const_mul (f := riemannZeta) s _ hzsigma,
    logDeriv_riemannZeta_two_mul h2one]
  simp only [completedSquarefreeFixedCurrent, squarefreeFixedCurrent,
    RHTower.infinitePrimeFlux]
  ring

/-- **Card `(6)`, reciprocal form.**  The same current is minus twice the logarithmic derivative of
the completed squarefree amplitude `X_sq`. -/
theorem neg_two_mul_logDeriv_completedSquarefreePartition
    {s : ℂ} (hs : 1 < s.re) :
    -2 * logDeriv completedSquarefreePartition s = completedSquarefreeFixedCurrent s := by
  have hre : (0 : ℝ) < s.re := by linarith
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have h1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hArch : archFactor s ≠ 0 := archFactor_ne_zero h0 h1 hG
  have hzs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hpart : squarefreePartition s ≠ 0 := squarefreePartition_ne_zero hs
  have hdArch : DifferentiableAt ℂ archFactor s :=
    (hasDerivAt_archFactor_of_re_pos hre).differentiableAt
  have hdPart : DifferentiableAt ℂ squarefreePartition s := differentiableAt_squarefreePartition hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : completedSquarefreePartition =ᶠ[nhds s]
      fun z : ℂ => archFactor z * squarefreePartition z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hzre : (1 : ℝ) < z.re := hz
    have hzpos : (0 : ℝ) < z.re := by linarith
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzpos; simp at hzpos
    have hz1 : z ≠ 1 := by intro h; rw [h] at hzre; simp at hzre
    have hzG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hzpos
    exact completedSquarefreePartition_eq hz0 hz1 hzG
  rw [logDeriv_congr_of_eventuallyEq heq, logDeriv_mul s hArch hpart hdArch hdPart]
  have hcur := neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent hs
  simp only [completedSquarefreeFixedCurrent]
  linear_combination (2 : ℂ) * hcur

/-- **Card `(7)`.**  Because the connection of the completed transfer is literally `Q_sq` on the
Euler half-plane, every source functional that only reads the connection there — in particular the
anti-causal Hardy projection producing `ell_E` — returns the same value on both. -/
theorem mobiusCompletedSquarefreeTransfer_connection_transport
    {alpha : Type*} {sigma : ℝ} (hsigma : 1 < sigma)
    (P : (ℂ → ℂ) → alpha)
    (hP : ∀ F G : ℂ → ℂ, Set.EqOn F G {s : ℂ | 1 < s.re} → P F = P G) :
    P (fun s => 2 * logDeriv (mobiusCompletedSquarefreeTransfer sigma) s) =
      P completedSquarefreeFixedCurrent :=
  hP _ _ fun _ hs => two_mul_logDeriv_mobiusCompletedSquarefreeTransfer hsigma hs

/-! ### Cards `(7a)`, `(7b)`: the safe correction as a positive translation average -/

/-- Card `(7a)`/`(7b)`.  The positive logarithmic-translation average with squared-zeta weights is a
contraction whose Laplace multiplier is the safe correction. -/
theorem mobiusSafeCorrection_is_positive_shift_average
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    ((∑' n : ℕ, zetaTwoBoundaryTerm sigma x n : ℝ) : ℂ) =
        mobiusSafeCorrectionValue sigma ((sigma + Real.pi * x : ℝ) : ℂ) ∧
      ∀ f : Lp ℂ 2 (volume : MeasureTheory.Measure ℝ),
        ‖zetaTwoShiftAverage sigma f‖ ≤ ‖f‖ :=
  ⟨ofReal_tsum_zetaTwoBoundaryTerm_eq_safeCorrection hsigma hx,
    fun f => norm_zetaTwoShiftAverage_le hsigma f⟩

/-- Card `(3)` at the operator level.  The pre-Gamma reciprocal squarefree operator is the
composition of two contractions and is therefore a contraction. -/
theorem norm_mobiusSquarefreeShiftContraction_le'
    {sigma : ℝ} (hsigma : 1 < sigma) (f : Lp ℂ 2 (volume : MeasureTheory.Measure ℝ)) :
    ‖mobiusSquarefreeShiftContraction sigma f‖ ≤ ‖f‖ :=
  norm_mobiusSquarefreeShiftContraction_le hsigma f

end RHTower
end
