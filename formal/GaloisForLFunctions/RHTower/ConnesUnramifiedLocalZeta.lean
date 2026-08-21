import GaloisForLFunctions.RHTower.ConnesTateLocalZeta

/-!
# The local Tate zeta integral of an unramified quasi-character

Appendix I (25)-(26) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

An unramified quasi-character of `k_v^*` is trivial on the units, hence a function of the
valuation alone: `Χ(a) = Χ(π)^{v(a)}`.  Its Tate zeta integral over the unit ball is therefore the
geometric series in `w = Χ(π) q^{-s}` — Connes' `(1 - Χ_{0,v}(π) q_v^{-s})^{-1}`, the local factor
of `L(Χ_0, s)`.  The special case `Χ = 1` is `(25)`; the general case is `(26)`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The shell profile of an unramified quasi-character on the unit ball. -/
def connesPadicUnitBallProfile (w : ℂ) : ℤ → ℂ :=
  fun m => if 0 ≤ m then w ^ m.toNat else 0

theorem connes_padic_unitBallProfile_summable {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun m : ℤ => ‖connesPadicUnitBallProfile w m‖ := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_geometric_of_lt_one (norm_nonneg w) hw).congr fun n => ?_
    rw [connesPadicUnitBallProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast, norm_pow]
  · refine summable_zero.congr fun n => ?_
    rw [connesPadicUnitBallProfile,
      if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1)), norm_zero]

/-- **Appendix I (25)/(26).**  The local Tate zeta integral of an unramified quasi-character over
the unit ball is the geometric sum `(1 - Χ(π) q^{-s})^{-1}`. -/
theorem connes_padic_unitBall_geometric {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ a, connesPadicRadial p (connesPadicUnitBallProfile w) a
        ∂fieldOnePadicMultiplicativeHaar p = (1 - w)⁻¹ := by
  rw [connes_padic_radial_integral p _ (connes_padic_unitBallProfile_summable hw)]
  have hsummable : Summable (connesPadicUnitBallProfile w) :=
    (connes_padic_unitBallProfile_summable hw).of_norm
  have hnat : Summable fun n : ℕ => connesPadicUnitBallProfile w (n : ℤ) :=
    hsummable.comp_injective (fun a b hab => by exact_mod_cast hab)
  have hneg : Summable fun n : ℕ => connesPadicUnitBallProfile w (-((n : ℤ) + 1)) := by
    refine summable_zero.congr fun n => ?_
    rw [connesPadicUnitBallProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hzero : (∑' n : ℕ, connesPadicUnitBallProfile w (-((n : ℤ) + 1))) = 0 := by
    have hfun : (fun n : ℕ => connesPadicUnitBallProfile w (-((n : ℤ) + 1)))
        = fun _ : ℕ => (0 : ℂ) := by
      funext n
      rw [connesPadicUnitBallProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
    rw [hfun, tsum_zero]
  have hpos : (∑' n : ℕ, connesPadicUnitBallProfile w (n : ℤ)) = (1 - w)⁻¹ := by
    have hcongr : (fun n : ℕ => connesPadicUnitBallProfile w (n : ℤ)) = fun n : ℕ => w ^ n := by
      funext n
      rw [connesPadicUnitBallProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
    rw [hcongr, tsum_geometric_of_norm_lt_one hw]
  rw [hzero, hpos, add_zero]

/-- **Appendix I (26).**  An unramified quasi-character is a power of its value at the
uniformizer: on the shell of valuation `n ≥ 0` it equals `Χ(π)^n`. -/
theorem connes_padic_unramified_pow (χ : ℚ_[p]ˣ →* ℂ)
    (hunit : ∀ u : ℤ_[p]ˣ,
      χ (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd (0 : ℤ), u)) = 1)
    (n : ℕ) (u : ℤ_[p]ˣ) :
    χ (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd ((n : ℤ)), u))
      = (χ (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd (1 : ℤ), (1 : ℤ_[p]ˣ)))) ^ n := by
  induction n with
  | zero => simpa using hunit u
  | succ k ih =>
    have hsplit : ((Multiplicative.ofAdd (((k : ℕ) + 1 : ℕ) : ℤ), u) :
          Multiplicative ℤ × ℤ_[p]ˣ)
        = (Multiplicative.ofAdd ((k : ℤ)), u) *
          (Multiplicative.ofAdd (1 : ℤ), (1 : ℤ_[p]ˣ)) := by
      refine Prod.ext ?_ ?_
      · show Multiplicative.ofAdd (((k : ℕ) + 1 : ℕ) : ℤ)
          = Multiplicative.ofAdd ((k : ℤ)) * Multiplicative.ofAdd (1 : ℤ)
        rw [← ofAdd_add]
        congr 1
      · show u = u * 1
        rw [mul_one]
    rw [hsplit, map_mul, map_mul, ih, pow_succ]

end

end GaloisForLFunctions.RHTower