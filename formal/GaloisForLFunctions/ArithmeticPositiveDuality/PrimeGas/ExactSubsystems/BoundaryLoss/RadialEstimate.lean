import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Envelope

/-! # A radial lower bound at imaginary temperatures in terms of the nonresonant modes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

/-- Prime modes whose boundary phase differs from that of the vacuum. -/
def nonresonantModes (P : Finset Nat.Primes) (z : ℂ) : Finset Nat.Primes :=
  P.filter (fun p => heat z (primePNat p) ≠ 1)

/-- Each selected mode contributes a single zero at the center. -/
def radialProduct (Q : Finset Nat.Primes) (z w : ℂ) : ℂ :=
  ∏ p ∈ Q, (heat (w-z) (primePNat p)-1)

private theorem heat_sub_one_ne {w : ℂ} (hw : 0 < w.re) (p : Nat.Primes) :
    heat w (primePNat p)-1 ≠ 0 := by
  intro h
  have hn := prime_heat_lt_one hw p
  rw [sub_eq_zero.mp h,norm_one] at hn
  exact lt_irrefl _ hn

theorem real_trace_norm_ge_one {ι κ : Type*} [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (x : ℝ) : 1 ≤ ‖finiteHeatTrace a (x:ℂ)‖ := by
  have he : finiteHeatTrace a (x:ℂ) = ((∑ i, ‖heat (x:ℂ) (a i)‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => real_heat_eq_norm (x:ℂ) (a i))
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  have hv := Finset.single_le_sum (fun (i : ι) (_ : i ∈ Finset.univ) => norm_nonneg (heat (x:ℂ) (a i)))
    (Finset.mem_univ (factorVacuum h))
  simpa only [factorVacuum_label h,heat,energy,PNat.val_ofNat, Nat.cast_one,Real.log_one,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,norm_one] using hv

theorem radialProduct_ne_zero (Q : Finset Nat.Primes) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    radialProduct Q z (z+(x:ℂ)) ≠ 0 := by
  simp only [radialProduct,add_sub_cancel_left]
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => heat_sub_one_ne (w := (x:ℂ)) hx p)

/-- Resonant modes cancel identically along the radius. Every remaining Euler denominator has modulus at most two. -/
theorem radial_trace_bound {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P))
    {z : ℂ} (hz : z.re = 0) {x : ℝ} (hx : 0 < x) :
    ‖radialProduct (nonresonantModes P z) z (z+(x:ℂ))‖ / 2^(nonresonantModes P z).card ≤
      ‖finiteHeatTrace a (z+(x:ℂ))‖ := by
  let Q := nonresonantModes P z
  let w := z+(x:ℂ)
  have hre : w.re = x := by simp [w,hz]
  have hw : 0 < w.re := hre.symm ▸ hx
  let f (p : Nat.Primes) := ‖1-heat (x:ℂ) (primePNat p)‖ / ‖1-heat w (primePNat p)‖
  have henv : eulerEnvelope P w = ∏ p ∈ Q, f p := by
    rw [eulerEnvelope,hre]
    symm
    apply Finset.prod_subset (Finset.filter_subset ..)
    intro p hp hn
    have he : heat z (primePNat p) = 1 := by
      by_contra he
      exact hn (Finset.mem_filter.mpr ⟨hp,he⟩)
    change f p = 1
    dsimp [f,w]
    rw [heat_add,he,one_mul,div_self]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (heat_sub_one_ne (w := (x:ℂ)) hx p))))
  have hprod : ‖radialProduct Q z w‖ / 2^Q.card ≤ eulerEnvelope P w := by
    rw [henv,radialProduct,norm_prod,← Finset.prod_const (s := Q) (2:ℝ),← Finset.prod_div_distrib]
    apply Finset.prod_le_prod (fun _ _ => div_nonneg (norm_nonneg _) (by positivity))
    intro p _
    change ‖heat ((z+(x:ℂ))-z) (primePNat p)-1‖/2 ≤ f p
    rw [add_sub_cancel_left,norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (heat_sub_one_ne hw p)))))
    have hd := norm_sub_le (1:ℂ) (heat w (primePNat p))
    rw [norm_one] at hd
    linarith only [hd,prime_heat_lt_one hw p]
  have hv := envelope_le_visibility P h ha hw
  rw [traceVisibility,hre] at hv
  exact hprod.trans (hv.trans (div_le_self (norm_nonneg _) (real_trace_norm_ge_one h x)))

#print axioms real_trace_norm_ge_one
#print axioms radialProduct_ne_zero
#print axioms radial_trace_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
