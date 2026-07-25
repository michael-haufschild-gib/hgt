import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Vanishing of exponential sums with real frequencies

A finite sum of exponentials with **distinct real** frequencies cannot tend to zero at `+∞` unless
every coefficient vanishes.  Each term has constant modulus, so decay is possible only through
cancellation, and cancellation cannot persist: translating by `tau` and subtracting the last term's
phase removes one frequency while preserving decay, so induction on the number of frequencies forces
every coefficient to zero.

The argument is elementary and integral-free — no mean-value, Bohr, or Diophantine input.  This is
the uniqueness statement that replaces general almost-periodicity theory when the functions in play
are generalized Dirichlet polynomials, as they are for jets of a Dirichlet series restricted to a
vertical line.
-/

open Complex Filter

namespace HTGeometry

/-- The unit-modulus exponential with real frequency `l`. -/
noncomputable def cis (l t : ℝ) : ℂ := Complex.exp (Complex.I * ((l * t : ℝ) : ℂ))

theorem norm_cis (l t : ℝ) : ‖cis l t‖ = 1 := by
  rw [cis, Complex.norm_exp]
  have : (Complex.I * ((l * t : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [this, Real.exp_zero]

theorem cis_add (l t u : ℝ) : cis l (t + u) = cis l t * cis l u := by
  rw [cis, cis, cis, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A single exponential with real frequency tends to zero only if its coefficient is zero. -/
theorem coeff_eq_zero_of_single (b : ℂ) (l : ℝ)
    (h : Tendsto (fun t : ℝ => b * cis l t) atTop (nhds 0)) : b = 0 := by
  have hconst : ∀ t : ℝ, ‖b * cis l t‖ = ‖b‖ := by
    intro t; rw [norm_mul, norm_cis, mul_one]
  have hnorm := ((continuous_norm (E := ℂ)).tendsto (0 : ℂ)).comp h
  rw [norm_zero] at hnorm
  simp only [Function.comp_def, hconst] at hnorm
  have := tendsto_nhds_unique hnorm tendsto_const_nhds
  simpa using this.symm

/-- **Exponential-sum vanishing.**  Pairwise distinct real frequencies and decay at `atTop` force
every coefficient to vanish. -/
theorem eq_zero_of_expSum_tendsto_zero :
    ∀ (n : ℕ) (lam : Fin n → ℝ) (b : Fin n → ℂ), Function.Injective lam →
      Tendsto (fun t : ℝ => ∑ i, b i * cis (lam i) t) atTop (nhds 0) → ∀ i, b i = 0 := by
  intro n
  induction n with
  | zero => intro lam b _ _ i; exact i.elim0
  | succ m ih =>
      intro lam b hinj h0
      set L : ℝ := lam (Fin.last m) with hL
      have hstep : ∀ tau : ℝ, ∀ i : Fin m,
          b i.castSucc * (cis (lam i.castSucc) tau - cis L tau) = 0 := by
        intro tau
        have hshift : Tendsto (fun t : ℝ => ∑ i, b i * cis (lam i) (t + tau))
            atTop (nhds 0) := by
          have := h0.comp (tendsto_atTop_add_const_right atTop tau tendsto_id)
          simpa [Function.comp_def] using this
        have hcomb : Tendsto
            (fun t : ℝ => (∑ i, b i * cis (lam i) (t + tau))
              - cis L tau * ∑ i, b i * cis (lam i) t) atTop (nhds 0) := by
          simpa using hshift.sub (h0.const_mul (cis L tau))
        have hrw : ∀ t : ℝ,
            (∑ i, b i * cis (lam i) (t + tau)) - cis L tau * ∑ i, b i * cis (lam i) t
            = ∑ i : Fin m, (b i.castSucc * (cis (lam i.castSucc) tau - cis L tau))
                * cis (lam i.castSucc) t := by
          intro t
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
            Fin.sum_univ_castSucc (f := fun i => b i * cis (lam i) (t + tau) -
              cis L tau * (b i * cis (lam i) t))]
          have hlast : b (Fin.last m) * cis L (t + tau)
              - cis L tau * (b (Fin.last m) * cis L t) = 0 := by
            rw [cis_add]; ring
          rw [← hL, hlast, add_zero]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [cis_add]; ring
        rw [tendsto_congr hrw] at hcomb
        exact ih (fun i => lam i.castSucc)
          (fun i => b i.castSucc * (cis (lam i.castSucc) tau - cis L tau))
          (fun i j hij => Fin.castSucc_injective m (hinj hij)) hcomb
      have hearly : ∀ i : Fin m, b i.castSucc = 0 := by
        intro i
        have hne : lam i.castSucc ≠ L := by
          intro heq
          exact absurd (hinj heq) (Fin.castSucc_lt_last i).ne
        set d : ℝ := lam i.castSucc - L with hd
        have hdne : d ≠ 0 := sub_ne_zero.mpr hne
        refine (mul_eq_zero.mp (hstep (Real.pi / d) i)).resolve_right ?_
        intro hzero
        have heq : cis (lam i.castSucc) (Real.pi / d) = cis L (Real.pi / d) :=
          sub_eq_zero.mp hzero
        rw [cis, cis, Complex.exp_eq_exp_iff_exists_int] at heq
        obtain ⟨k, hk⟩ := heq
        have him : lam i.castSucc * (Real.pi / d)
            = L * (Real.pi / d) + 2 * Real.pi * k := by
          have h := congrArg Complex.im hk
          have h' : lam i.castSucc * (Real.pi / d)
              = L * (Real.pi / d) + (k : ℝ) * (2 * Real.pi) := by
            simpa [Complex.mul_im, Complex.mul_re] using h
          linarith
        have hd' : d * (Real.pi / d) = Real.pi := by field_simp
        have hpi : Real.pi = 2 * Real.pi * k := by
          have hstep2 : (lam i.castSucc - L) * (Real.pi / d) = 2 * Real.pi * k := by
            ring_nf
            ring_nf at him
            linarith
          rw [← hd, hd'] at hstep2
          exact hstep2
        have hzero2 : Real.pi * (1 - 2 * k) = 0 := by ring_nf; linarith
        have h2k : (1 : ℝ) - 2 * k = 0 := by
          rcases mul_eq_zero.mp hzero2 with h | h
          · exact absurd h Real.pi_ne_zero
          · exact h
        have hint : (2 * k : ℤ) = 1 := by
          have : (2 : ℝ) * k = 1 := by linarith
          exact_mod_cast this
        omega
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hearly j
      · refine coeff_eq_zero_of_single (b (Fin.last m)) L ?_
        refine h0.congr fun t => ?_
        rw [Fin.sum_univ_castSucc]
        have hz : ∀ j : Fin m, b j.castSucc * cis (lam j.castSucc) t = 0 := by
          intro j; rw [hearly j, zero_mul]
        rw [Finset.sum_congr rfl fun j _ => hz j, Finset.sum_const_zero, zero_add, ← hL]

end HTGeometry
