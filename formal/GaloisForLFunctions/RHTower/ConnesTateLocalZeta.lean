import GaloisForLFunctions.RHTower.ConnesWeilPrimeSide
import GaloisForLFunctions.HTGeometry.EulerQGammaLocalFactor

/-!
# The local Tate zeta integral over the unit ball

Appendix I (25) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

With the multiplicative Haar measure normalized by `vol(R_v^*) = 1`, the local factor controlling
the absolute convergence of Tate's global integral `∫ f(x) Χ_0(x)|x|^s d^*x` is

  `∫_{R_v ∩ k_v^*} |x|^s d^*x = 1 + q^{-s} + q^{-2s} + … = (1 - q^{-s})^{-1}`,

so the convergence for `Re s > 1` is the same as for the zeta function.  The unit ball is the
union of the valuation shells `m ≥ 0`, on each of which `|x|^s` is the constant `q^{-ms}`.
Taking the product over the finite places of `ℚ` recovers the Riemann zeta function, which is
the identity `Δ_s = L(Χ_0, s) Δ'_s` of Lemma 1 in the shape in which the paper proves it.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The shell profile of `|x|^s` restricted to the unit ball. -/
def connesPadicUnitBallZetaProfile (s : ℂ) : ℤ → ℂ :=
  fun m => if 0 ≤ m then ((p : ℂ) ^ (-s)) ^ m.toNat else 0

/-- The Tate integrand `1_{R_v}(x)|x|^s` is the radial function of that profile. -/
theorem connesPadicUnitBallZeta_apply (s : ℂ) (a : ℚ_[p]ˣ) :
    Set.indicator {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1}
        (fun b : ℚ_[p]ˣ => ((‖(b : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a
      = connesPadicRadial p (connesPadicUnitBallZetaProfile p s) a := by
  have hprime : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  have hnorm : ‖(a : ℚ_[p])‖ = (p : ℝ) ^ (-(Padic.valuation (a : ℚ_[p]))) :=
    Padic.norm_eq_zpow_neg_valuation (Units.ne_zero a)
  set m : ℤ := Padic.valuation (a : ℚ_[p]) with hmdef
  by_cases hm : 0 ≤ m
  · have hmem : a ∈ {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1} := by
      show ‖(a : ℚ_[p])‖ ≤ 1
      rw [hnorm]
      exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
    rw [Set.indicator_of_mem hmem]
    show ((‖(a : ℚ_[p])‖ : ℝ) : ℂ) ^ s = connesPadicUnitBallZetaProfile p s m
    rw [connesPadicUnitBallZetaProfile, if_pos hm, hnorm,
      ← Real.rpow_intCast (p : ℝ) (-m),
      GaloisForLFunctions.HTGeometry.ofReal_rpow_cpow hppos (((-m : ℤ) : ℝ)) s,
      ← Complex.cpow_nat_mul]
    congr 1
    have htn : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
      have : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
      exact_mod_cast congrArg (fun k : ℤ => (k : ℂ)) this
    rw [htn]
    push_cast
    ring
  · have hgt : 1 < ‖(a : ℚ_[p])‖ := by
      rw [hnorm]
      exact one_lt_zpow₀ hp1 (by omega)
    have hnmem : a ∉ {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1} := by
      simp only [Set.mem_setOf_eq, not_le]
      exact hgt
    rw [Set.indicator_of_notMem hnmem]
    show (0 : ℂ) = connesPadicUnitBallZetaProfile p s m
    rw [connesPadicUnitBallZetaProfile, if_neg hm]

theorem connes_padic_unitBallZetaProfile_summable {s : ℂ} (hs : 0 < s.re) :
    Summable fun m : ℤ => ‖connesPadicUnitBallZetaProfile p s m‖ := by
  have hz : ‖((p : ℂ)) ^ (-s)‖ < 1 := connes_padic_norm_cpow_neg_lt_one p hs
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_geometric_of_lt_one (norm_nonneg _) hz).congr fun n => ?_
    have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    rw [connesPadicUnitBallZetaProfile, if_pos hnn, Int.toNat_natCast, norm_pow]
  · refine summable_zero.congr fun n => ?_
    rw [connesPadicUnitBallZetaProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1)),
      norm_zero]

/-- **Appendix I (25).**  With `vol(ℤ_p^*) = 1`, the local Tate zeta integral over the unit ball
is the local Euler factor `(1 - p^{-s})^{-1}`. -/
theorem connes_padic_tate_local_zeta {s : ℂ} (hs : 0 < s.re) :
    ∫ a : ℚ_[p]ˣ, Set.indicator {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1}
        (fun b : ℚ_[p]ˣ => ((‖(b : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a
      ∂fieldOnePadicMultiplicativeHaar p = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hz : ‖((p : ℂ)) ^ (-s)‖ < 1 := connes_padic_norm_cpow_neg_lt_one p hs
  have hfun : (fun a : ℚ_[p]ˣ => Set.indicator {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1}
      (fun b : ℚ_[p]ˣ => ((‖(b : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a)
      = connesPadicRadial p (connesPadicUnitBallZetaProfile p s) :=
    funext fun a => connesPadicUnitBallZeta_apply p s a
  rw [hfun, connes_padic_radial_integral p _ (connes_padic_unitBallZetaProfile_summable p hs)]
  have hsummable : Summable (connesPadicUnitBallZetaProfile p s) :=
    (connes_padic_unitBallZetaProfile_summable p hs).of_norm
  have hnat : Summable fun n : ℕ => connesPadicUnitBallZetaProfile p s (n : ℤ) :=
    hsummable.comp_injective (fun a b hab => by exact_mod_cast hab)
  have hneg : Summable fun n : ℕ => connesPadicUnitBallZetaProfile p s (-((n : ℤ) + 1)) := by
    refine summable_zero.congr fun n => ?_
    rw [connesPadicUnitBallZetaProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hzero : (∑' n : ℕ, connesPadicUnitBallZetaProfile p s (-((n : ℤ) + 1))) = 0 := by
    have : (fun n : ℕ => connesPadicUnitBallZetaProfile p s (-((n : ℤ) + 1)))
        = fun _ : ℕ => (0 : ℂ) := by
      funext n
      rw [connesPadicUnitBallZetaProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
    rw [this, tsum_zero]
  have hpos : (∑' n : ℕ, connesPadicUnitBallZetaProfile p s (n : ℤ))
      = (1 - (p : ℂ) ^ (-s))⁻¹ := by
    have hcongr : (fun n : ℕ => connesPadicUnitBallZetaProfile p s (n : ℤ))
        = fun n : ℕ => ((p : ℂ) ^ (-s)) ^ n := by
      funext n
      rw [connesPadicUnitBallZetaProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
    rw [hcongr, tsum_geometric_of_norm_lt_one hz]
  rw [hzero, hpos, add_zero]

/-- **Appendix I Lemma 1 for `k = ℚ`, `Χ_0 = 1`.**  The product over the finite places of the
local Tate zeta integrals over the unit balls is the Riemann zeta function. -/
theorem connes_tate_local_zeta_tprod {s : ℂ} (hs : 1 < s.re) :
    (∏' q : Nat.Primes,
        ∫ a : ℚ_[(q : ℕ)]ˣ, Set.indicator {b : ℚ_[(q : ℕ)]ˣ | ‖(b : ℚ_[(q : ℕ)])‖ ≤ 1}
            (fun b : ℚ_[(q : ℕ)]ˣ => ((‖(b : ℚ_[(q : ℕ)])‖ : ℝ) : ℂ) ^ s) a
          ∂fieldOnePadicMultiplicativeHaar (q : ℕ))
      = riemannZeta s := by
  rw [← riemannZeta_eulerProduct_tprod hs]
  exact tprod_congr fun q =>
    connes_padic_tate_local_zeta (q : ℕ) (lt_trans zero_lt_one hs)

end

end GaloisForLFunctions.RHTower
