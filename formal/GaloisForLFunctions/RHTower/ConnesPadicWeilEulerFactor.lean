import GaloisForLFunctions.RHTower.ConnesPadicWeilVonMangoldt

/-!
# The local Euler factor as a Weil term

Appendix II (10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The geometric radial profile `h(m) = w^m` for `m ≥ 1`, extended by zero, is the multiplicative
test function carried by the shells inside the unit ball.  Its local Weil term is the closed
geometric sum `w/(1-w)`; at `w = p^{-s}` this is `(p^s - 1)^{-1}`, the local Euler factor of
`-ζ'/ζ` up to the factor `log p` supplied by Connes' normalization `vol(ℤ_p^*) = log p`.
Summing these factors over the primes is the prime side of the explicit formula.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The geometric radial profile carried by the shells `‖u‖ = p^{-m}`, `m ≥ 1`. -/
def connesPadicGeomProfile (w : ℂ) : ℤ → ℂ :=
  fun m => if 0 < m then w ^ m.toNat else 0

@[simp] theorem connesPadicGeomProfile_zero (w : ℂ) : connesPadicGeomProfile w 0 = 0 := by
  simp [connesPadicGeomProfile]

theorem connesPadicGeomProfile_nonpos (w : ℂ) {m : ℤ} (hm : m ≤ 0) :
    connesPadicGeomProfile w m = 0 := by
  simp [connesPadicGeomProfile, not_lt.mpr hm]

theorem connesPadicGeomProfile_succ (w : ℂ) (n : ℕ) :
    connesPadicGeomProfile w ((n : ℤ) + 1) = w ^ (n + 1) := by
  have hpos : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have htn : ((n : ℤ) + 1).toNat = n + 1 := by omega
  simp [connesPadicGeomProfile, hpos, htn]

/-- The weighted geometric profile is absolutely summable over the shells. -/
theorem connes_padic_geomProfile_summable {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun m : ℤ =>
      ‖((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * connesPadicGeomProfile w m‖ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hgeom : Summable fun n : ℕ => ‖w‖ ^ n := summable_geometric_of_lt_one (norm_nonneg w) hw
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeom.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
      have htn : ((n : ℤ)).toNat = n := Int.toNat_natCast n
      have hmin : min 1 ((p : ℝ) ^ (n : ℤ)) = 1 :=
        min_eq_left (one_le_zpow₀ hp1.le hpos.le)
      simp only [connesPadicGeomProfile, if_pos hpos, htn, hmin]
      simp [norm_pow]
  · refine summable_zero.congr fun n => ?_
    have hle : -((n : ℤ) + 1) ≤ 0 := by omega
    rw [connesPadicGeomProfile_nonpos w hle, mul_zero, norm_zero]

/-- **The local Weil term of the geometric profile.**  It is the closed geometric sum
`w/(1-w)`. -/
theorem connes_padic_weil_geometric {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ a, connesPadicRadial p (connesPadicGeomProfile w) a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ)
        ∂fieldOnePadicMultiplicativeHaar p = w * (1 - w)⁻¹ := by
  rw [connes_padic_weil_radial_split p _ (connesPadicGeomProfile_zero w)
    (connes_padic_geomProfile_summable p hw)]
  have hneg : (∑' n : ℕ, (((p : ℝ) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) *
      connesPadicGeomProfile w (-((n : ℤ) + 1))) = 0 := by
    have hzero : (fun n : ℕ => (((p : ℝ) ^ (-((n : ℤ) + 1)) : ℝ) : ℂ) *
        connesPadicGeomProfile w (-((n : ℤ) + 1))) = fun _ : ℕ => (0 : ℂ) := by
      funext n
      rw [connesPadicGeomProfile_nonpos w (by omega : -((n : ℤ) + 1) ≤ 0), mul_zero]
    rw [hzero, tsum_zero]
  have hpos : (∑' n : ℕ, connesPadicGeomProfile w ((n : ℤ) + 1)) = w * (1 - w)⁻¹ := by
    have hcongr : (fun n : ℕ => connesPadicGeomProfile w ((n : ℤ) + 1))
        = fun n : ℕ => w * w ^ n := by
      funext n
      rw [connesPadicGeomProfile_succ]
      ring
    rw [hcongr, tsum_mul_left, tsum_geometric_of_norm_lt_one hw]
  rw [hpos, hneg, add_zero]

/-- The geometric ratio `p^{-s}` is a strict contraction on the right half-plane. -/
theorem connes_padic_norm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hprime : p.Prime := Fact.out
  rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- **Appendix II (10), Euler factor form.**  The local Weil term of the geometric profile with
ratio `p^{-s}` is the local Euler factor `(p^s - 1)^{-1}` of `-ζ'/ζ`; Connes' normalization
`vol(ℤ_p^*) = log p` supplies the missing `log p`, and the sum over primes of
`log p · (p^s - 1)^{-1}` is the von Mangoldt Dirichlet series. -/
theorem connes_padic_weil_eulerFactor {s : ℂ} (hs : 0 < s.re) :
    ∫ a, connesPadicRadial p (connesPadicGeomProfile ((p : ℂ) ^ (-s))) a *
        ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ) ∂fieldOnePadicMultiplicativeHaar p
      = ((p : ℂ) ^ s - 1)⁻¹ := by
  have hprime : p.Prime := Fact.out
  have hq : ((p : ℂ) ^ s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hprime.ne_zero))
  rw [connes_padic_weil_geometric p (connes_padic_norm_cpow_neg_lt_one p hs),
    Complex.cpow_neg, ← mul_inv]
  congr 1
  field_simp

end

end GaloisForLFunctions.RHTower
