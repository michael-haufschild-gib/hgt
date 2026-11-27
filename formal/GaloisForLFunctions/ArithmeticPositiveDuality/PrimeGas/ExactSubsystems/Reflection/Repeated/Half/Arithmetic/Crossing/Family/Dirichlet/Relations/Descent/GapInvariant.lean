import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.WellFounded
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.StabilizedSpectra
import GaloisForLFunctions.RHTower.GelfondSchneider

/-! # Algebraic shell ratios are preserved by normalized forcing -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real

private theorem algebraic_modulus {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ ‖z‖ := by
  have integral := isAlgebraic_iff_isIntegral.mp h
  have prod := integral.mul (integral.map (starRingEnd ℂ).toRatAlgHom)
  change IsIntegral ℚ (z*(starRingEnd ℂ) z) at prod
  rw [Complex.mul_conj,← Complex.sq_norm,Complex.ofReal_pow] at prod
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective).mp
    (IsIntegral.of_pow zero_lt_two prod).isAlgebraic

/-- The modulus of a specialized algebraic coordinate retains algebraicity
even if the forcing reverses the temperature or twists the shell ratio. -/
theorem gap_algebraic_transfer {t u : ℝ} (ht : 0<t) (hit : u ∈ accumulated t) (a b : ℕ+)
    (alg : IsAlgebraic ℚ (relativePower t a b)) : IsAlgebraic ℚ (relativePower u a b) := by
  obtain ⟨P,ne,root⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg
  obtain ⟨hu,m,hm,force⟩ := hit
  have signed (v : ℝ) (s : TorsionSpecialization m t v) : IsAlgebraic ℚ (relativePower v a b) := by
    obtain ⟨z,hz,mag⟩ := relative_root hm s a b P root
    rw [← mag]
    exact algebraic_modulus ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp ⟨P,ne,hz⟩)
  rcases (scaled_forcing_iff ht hu hm).mp force with pos | neg
  · exact signed u pos
  · have alg := (signed (-u) neg).inv
    simpa only [relativePower_exp,neg_mul,exp_neg,inv_inv] using alg

theorem mutual_gap_iff {t u : ℝ} (ht : 0<t) (hit : u ∈ mutualOrders t) (a b : ℕ+) :
    IsAlgebraic ℚ (relativePower t a b) ↔ IsAlgebraic ℚ (relativePower u a b) :=
  ⟨gap_algebraic_transfer ht hit.1 a b,gap_algebraic_transfer hit.1.1 hit.2 a b⟩

/-- A single nonconstant algebraic shell ratio excludes every nontrivial
algebraic multiplier, at every common rational dilation. -/
theorem algebraic_gap_multiplier_iff (a b : ℕ+) (gap : energy b<energy a) {t r : ℝ}
    (ht : 0<t) (hr : 0<r) (base : IsAlgebraic ℚ (relativePower t a b)) (alg : IsAlgebraic ℚ r) :
    r*t ∈ accumulated t ↔ r=1 := by
  constructor
  · intro hit
    by_cases irr : Irrational r
    · have xp : 1<relativePower t a b := by
        rw [relativePower_exp]; exact (one_lt_exp_iff).mpr (mul_pos ht (sub_pos.mpr gap))
      have transferred := gap_algebraic_transfer ht hit a b base
      have power : relativePower (r*t) a b=(relativePower t a b)^r := by
        rw [relativePower_exp,relativePower_exp,rpow_def_of_pos (exp_pos _),log_exp]
        congr 1; ring
      rw [power] at transferred
      exact (GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _ (zero_lt_one.trans xp) xp.ne'
        ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr base) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg)
        irr transferred).elim
    · obtain ⟨q,rfl⟩ := exists_rat_of_not_irrational irr
      obtain ⟨_,m,hm,force⟩ := hit
      rw [mul_assoc] at force
      have pos := mul_pos ht (Nat.cast_pos.mpr hm : 0<(m : ℝ))
      have rs := (resonant_nat_iff ht hm).mpr (resonant_of_finite ht (algebraic_gap_finite a b gap ht base))
      have one := ((rational_forces_iff pos q (Rat.cast_pos.mp hr)).mp force).resolve_right (not_not.mpr rs)
      rw [one,Rat.cast_one]
  · rintro rfl
    rw [one_mul]
    exact accumulated_self ht

#print axioms gap_algebraic_transfer
#print axioms mutual_gap_iff
#print axioms algebraic_gap_multiplier_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
