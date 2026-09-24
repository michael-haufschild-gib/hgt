import GaloisForLFunctions.RHTower.EstermannKloostermanSaving
import GaloisForLFunctions.RHTower.EstermannPrincipalPart
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

/-!
# The ζ-content of the Kloosterman modes, and why the modulus mixing cannot see it

The polar decomposition `D(s,a/q) = q^{1−2s} ζ(s)² + q^{−s} R_a(s)` puts the whole `ζ`-content of
the family in a twist-independent term, so any weighted average over the units carries `ζ(s)²` with
coefficient `q^{1−2s}` times the total weight.  For the inverse twist at a prime modulus the total
weight is the Ramanujan value `−1`, so **every** nonzero Kloosterman mode carries exactly
`−q^{1−2s} ζ(s)²`, while the zero mode carries `φ(q) q^{1−2s} ζ(s)²`.

The modulus exponent of that content is `1 − 2σ`, which is `< 1/2` throughout `σ > 1/4` and is `0`
on the critical line.  Weil's bound for a nonzero mode has exponent `1/2`.  So on the critical line
the `ζ`-content of a mode lies a factor `√q` below the square-root-cancellation threshold that
Weil's theorem certifies: the modulus-aspect mixing controls the modes to an accuracy that is
coarser than their `ζ`-content, and therefore cannot constrain `ζ`.
-/

open Complex Finset
open RHTower.Sieve

namespace RHTower

noncomputable section

/-- **The Ramanujan value of the inverse twist.**  For a prime modulus and a nonzero frequency the
inverse twist sums to `−1` over the units. -/
theorem sum_units_stdAddChar_invTwist (p : ℕ) [Fact p.Prime] {b : ZMod p} (hb : b ≠ 0) :
    ∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) : ℂ) = -1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set u : (ZMod p)ˣ := Units.mk0 b hb with hu
  have hkey : ∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) : ℂ)
      = ∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((u * a⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [Units.val_mul, hu, Units.val_mk0, mul_comm]
  have hequiv : ∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((u * a⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ)
      = ∑ x : (ZMod p)ˣ, (ZMod.stdAddChar ((x : ZMod p)) : ℂ) :=
    Fintype.sum_equiv ((kloostermanUnitInvEquiv p).trans (kloostermanUnitMulEquiv p u)) _ _
      (fun a => rfl)
  rw [hkey, hequiv, sum_units_stdAddChar]

/-- **The ζ-content of a twist average.**  The `ζ²` part of any weighted average over the units is
the total weight times `q^{1−2s}`; the twist only enters the regular part. -/
theorem sum_weight_estermannZeta (q : ℕ) [NeZero q] (w : (ZMod q)ˣ → ℂ) {s : ℂ} (hs : s ≠ 1) :
    ∑ a : (ZMod q)ˣ, w a * estermannZeta q ((a : ZMod q)) s
      = (∑ a : (ZMod q)ˣ, w a) * ((q : ℂ) ^ (1 - 2 * s) * riemannZeta s ^ (2 : ℕ))
        + (q : ℂ) ^ (-s) *
            ∑ a : (ZMod q)ˣ, w a * estermannRegularPart q ((a : ZMod q)) s := by
  have h : ∀ a : (ZMod q)ˣ, w a * estermannZeta q ((a : ZMod q)) s
      = w a * ((q : ℂ) ^ (1 - 2 * s) * riemannZeta s ^ (2 : ℕ))
        + (q : ℂ) ^ (-s) * (w a * estermannRegularPart q ((a : ZMod q)) s) := by
    intro a
    rw [estermannZeta_eq_zetaSq_add a hs]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]

/-- **Every nonzero Kloosterman mode carries the same ζ-content.**  For a prime modulus and
`b ≠ 0` the `ζ²` part of the inverse-twist average is `−q^{1−2s} ζ(s)²`, independent of `b`. -/
theorem sum_invTwist_estermannZeta_zeta_content (p : ℕ) [Fact p.Prime] {b : ZMod p} (hb : b ≠ 0)
    {s : ℂ} (hs : s ≠ 1) :
    ∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) : ℂ) *
        estermannZeta p ((a : ZMod p)) s
      = -((p : ℂ) ^ (1 - 2 * s) * riemannZeta s ^ (2 : ℕ))
        + (p : ℂ) ^ (-s) * ∑ a : (ZMod p)ˣ,
            (ZMod.stdAddChar (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) : ℂ) *
              estermannRegularPart p ((a : ZMod p)) s := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [sum_weight_estermannZeta p _ hs, sum_units_stdAddChar_invTwist p hb]
  ring

/-- **The zero mode carries `φ(q)` copies of the ζ-content.** -/
theorem sum_estermannZeta_units_zeta_content (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    ∑ a : (ZMod q)ˣ, estermannZeta q ((a : ZMod q)) s
      = (Nat.totient q : ℂ) * ((q : ℂ) ^ (1 - 2 * s) * riemannZeta s ^ (2 : ℕ))
        + (q : ℂ) ^ (-s) * ∑ a : (ZMod q)ˣ, estermannRegularPart q ((a : ZMod q)) s := by
  have h := sum_weight_estermannZeta q (fun _ => (1 : ℂ)) hs
  simp only [one_mul] at h
  rw [h]
  congr 2
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]

/-- On the critical line the modulus factor of the ζ-content is trivial. -/
theorem norm_cpow_one_sub_two_mul (q : ℕ) (hq : 0 < q) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖(q : ℂ) ^ (1 - 2 * s)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  have hre : (1 - 2 * s).re = 0 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, hs]
    ring
  rw [hre, Real.rpow_zero]

/-- The modulus exponent of the ζ-content is strictly below the Weil exponent `1/2` throughout
`σ > 1/4`. -/
theorem zetaContent_modulus_lt_weil (q : ℕ) (hq : 1 ≤ q) {σ : ℝ} (hσ : 1 / 4 < σ) :
    (q : ℝ) ^ (1 - 2 * σ) < 2 * Real.sqrt q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hexp : (1 : ℝ) - 2 * σ ≤ 1 / 2 := by linarith
  have hmono : (q : ℝ) ^ (1 - 2 * σ) ≤ (q : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hexp
  have hsq : (q : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt q := (Real.sqrt_eq_rpow (q : ℝ)).symm
  have hpos : (0 : ℝ) < Real.sqrt q := by
    have : (0 : ℝ) < (q : ℝ) := by linarith
    exact Real.sqrt_pos.mpr this
  rw [hsq] at hmono
  linarith

/-- `‖ζ(s)²‖` never exceeds the divisor mass right of the abscissa. -/
theorem norm_riemannZeta_sq_le_divisorMass {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s ^ (2 : ℕ)‖ ≤ divisorMass s.re := by
  classical
  set f : ℕ → ℂ := fun n : ℕ => (n.divisors.card : ℂ) with hf
  have hmaj : ∀ N : ℕ, ‖LSeries.term f s N‖ ≤ (N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [hf]
    · have hnorm : ‖(N : ℂ) ^ s‖ = (N : ℝ) ^ s.re := Complex.norm_natCast_cpow_of_pos hN _
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      rw [LSeries.term_of_ne_zero (by omega : N ≠ 0), hf, norm_div, hnorm,
        Complex.norm_natCast, Real.rpow_neg hNpos.le, div_eq_mul_inv]
  have hsum : Summable (fun N : ℕ => (N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) :=
    summable_divisorCount_rpow hs
  have hns : Summable (fun N : ℕ => ‖LSeries.term f s N‖) :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) hmaj hsum
  have hzeta : riemannZeta s ^ (2 : ℕ) = LSeries f s :=
    (RHTower.Sieve.LSeries_card_divisors_eq_riemannZeta_sq hs).symm
  rw [hzeta, LSeries]
  calc ‖∑' N : ℕ, LSeries.term f s N‖ ≤ ∑' N : ℕ, ‖LSeries.term f s N‖ :=
        norm_tsum_le_tsum_norm hns
    _ ≤ ∑' N : ℕ, (N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hmaj hns hsum
    _ = divisorMass s.re := rfl

end

end RHTower
