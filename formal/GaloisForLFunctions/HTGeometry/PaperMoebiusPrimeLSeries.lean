import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeTransport
import GaloisForLFunctions.RHTower.RetainedPrimeMobiusEulerIdentity

/-!
# Faithful Dirichlet series of the proven Möbius prime transport

The source is the actual scalar specialization of the core additive action.
Convergence is proved on the Euler half-plane, and the existing retained-prime
identity supplies the exact Euler factor. No cancellation or zero hypothesis
is supplied to these applications.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The algebra retraction is the existing literal p-free sequence restriction. -/
theorem paperPrimeConstantProjection_coe (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    ⇑(paperPrimeConstantProjection p f : ArithmeticFunction ℂ) =
      RHTower.primeFreeSourcePart (p : ℕ) f := by
  funext n
  exact paperPrimeConstantProjection_apply p f n

private theorem moebius_norm_le (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- The actual p-free Möbius source has uniformly bounded coefficients. -/
theorem paperMoebiusPrimeProjection_norm_le (p : Nat.Primes) (n : ℕ) :
    ‖(paperPrimeConstantProjection p
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) n‖ ≤ 1 := by
  rw [paperPrimeConstantProjection_apply]
  split_ifs
  · simp
  · simpa only [ArithmeticFunction.intCoe_apply] using moebius_norm_le n

/-- Absolute convergence of the p-free source is paid on the entire Euler half-plane. -/
theorem paperMoebiusPrimeProjection_LSeriesSummable (p : Nat.Primes)
    (s : {s : ℂ // 1 < s.re}) :
    LSeriesSummable
      (⇑(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => paperMoebiusPrimeProjection_norm_le p n) s.property

/-- Every scalar specialization of the genuine source flow is absolutely summable there. -/
theorem paperMoebiusPrimeTransport_LSeriesSummable (p : Nat.Primes) (t : ℂ)
    (s : {s : ℂ // 1 < s.re}) :
    LSeriesSummable (⇑(paperMoebiusPrimeTransport p t)) s := by
  rw [paperMoebiusPrimeTransport_eq]
  change LSeriesSummable
    ((fun n => (ArithmeticFunction.moebius n : ℂ)) - t •
      ⇑(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) s
  exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr s.property).sub
    ((paperMoebiusPrimeProjection_LSeriesSummable p s).smul t)

/-- The native retained-prime Euler identity applies to the actual algebraic projection. -/
theorem paperMoebiusPrimeProjection_LSeries_euler (p : Nat.Primes)
    (s : {s : ℂ // 1 < s.re}) :
    (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) *
      LSeries (⇑(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) s =
      (riemannZeta s)⁻¹ := by
  have h := RHTower.one_sub_cpow_mul_LSeries_retainedPrimeFree
    ∅ (fun _ => 1) p.property (by simp) s.property
  have hf : RHTower.retainedPrimeMobiusCoefficient ∅ (fun _ => 1) =
      ⇑(ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
    funext n
    simp [RHTower.retainedPrimeMobiusCoefficient, ArithmeticFunction.intCoe_apply]
  rw [hf, ← paperPrimeConstantProjection_coe] at h
  have hmu : LSeries (⇑(ArithmeticFunction.moebius : ArithmeticFunction ℂ)) s =
      (riemannZeta s)⁻¹ := RHTower.LSeries_moebius_eq_inv_riemannZeta s.property
  exact h.trans hmu

/-- Division uses the proved nonvanishing Euler factor, rather than an extra assumption. -/
theorem paperMoebiusPrimeProjection_LSeries (p : Nat.Primes)
    (s : {s : ℂ // 1 < s.re}) :
    LSeries (⇑(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) s =
      (riemannZeta s)⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) := by
  have he := RHTower.one_sub_primeCpow_neg_ne_zero
    (lt_trans zero_lt_one s.property) p
  apply (eq_div_iff he).mpr
  rw [mul_comm]
  exact paperMoebiusPrimeProjection_LSeries_euler p s

/-- The exact analytic formula belongs to the actual transported Dirichlet coefficients. -/
theorem paperMoebiusPrimeTransport_LSeries (p : Nat.Primes) (t : ℂ)
    (s : {s : ℂ // 1 < s.re}) :
    LSeries (⇑(paperMoebiusPrimeTransport p t)) s =
      ((1 - t - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) /
        (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))) * (riemannZeta s)⁻¹ := by
  rw [paperMoebiusPrimeTransport_eq]
  change LSeries
    ((fun n => (ArithmeticFunction.moebius n : ℂ)) - t •
      ⇑(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) s = _
  rw [LSeries_sub (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr s.property)
      ((paperMoebiusPrimeProjection_LSeriesSummable p s).smul t),
    LSeries_smul, RHTower.LSeries_moebius_eq_inv_riemannZeta s.property,
    paperMoebiusPrimeProjection_LSeries]
  have he := RHTower.one_sub_primeCpow_neg_ne_zero
    (lt_trans zero_lt_one s.property) p
  field_simp [he]
  ring

/-- Reciprocal transport is identified on the convergence domain for every scalar time. -/
theorem paperMoebiusPrimeTransport_LSeries_inv (p : Nat.Primes) (t : ℂ)
    (s : {s : ℂ // 1 < s.re}) :
    (LSeries (⇑(paperMoebiusPrimeTransport p t)) s)⁻¹ =
      riemannZeta s * (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) /
        (1 - t - ((p : ℕ) : ℂ) ^ (-(s : ℂ))) := by
  rw [paperMoebiusPrimeTransport_LSeries]
  by_cases hn : 1 - t - ((p : ℕ) : ℂ) ^ (-(s : ℂ)) = 0
  · simp [hn]
  · have he := RHTower.one_sub_primeCpow_neg_ne_zero
      (lt_trans zero_lt_one s.property) p
    have hz := riemannZeta_ne_zero_of_one_lt_re s.property
    field_simp [he, hn, hz]

end

end GaloisForLFunctions.HTGeometry
