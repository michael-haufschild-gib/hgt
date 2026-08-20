import GaloisForLFunctions.HTGeometry.QuasiPeriodDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.WeldCircleFaithfulness

/-!
# Two prime-log quasi-periods force differential algebraicity

The gauge reformulation of the prime-cocycle card produces a function reproduced up to constant
multipliers by the two translations `log p` and `log q`.  Those two steps are `ℚ`-independent by
unique factorisation and `ℝ`-dependent because both are real, which is exactly the hypothesis pair of
the corpus's quasi-period rank law.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

noncomputable section

/-- Two distinct prime logarithms are `ℚ`-independent in `ℂ`. -/
theorem linearIndependent_rat_primeLog_pair {p q : Nat.Primes} (hpq : p ≠ q) :
    LinearIndependent ℚ ![((Real.log (p : ℕ) : ℝ) : ℂ), ((Real.log (q : ℕ) : ℝ) : ℂ)] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hre : (s : ℝ) * Real.log (p : ℕ) + (t : ℝ) * Real.log (q : ℕ) = 0 := by
    have h := congrArg Complex.re hst
    simp only [Rat.smul_def, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, Complex.zero_re,
      mul_zero, sub_zero] at h
    linarith [h]
  -- clear denominators
  set n : ℤ := s.num * (t.den : ℤ) with hn
  set m : ℤ := t.num * (s.den : ℤ) with hm
  have hint : (n : ℝ) * Real.log (p : ℕ) + (m : ℝ) * Real.log (q : ℕ) = 0 := by
    have hs : (s : ℝ) = (s.num : ℝ) / (s.den : ℝ) := Rat.cast_def s
    have ht : (t : ℝ) = (t.num : ℝ) / (t.den : ℝ) := Rat.cast_def t
    have hsd : (s.den : ℝ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr s.den_nz
    have htd : (t.den : ℝ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr t.den_nz
    rw [hn, hm]
    push_cast
    rw [hs, ht] at hre
    field_simp at hre ⊢
    linarith [hre]
  -- the finitely supported integer charge
  set c : Nat.Primes →₀ ℤ := Finsupp.single p n + Finsupp.single q m with hc
  have hval : primeLogHom c = (n : ℝ) * Real.log (p : ℕ) + (m : ℝ) * Real.log (q : ℕ) := by
    rw [hc, map_add]
    simp only [primeLogHom, Finsupp.liftAddHom_apply_single, AddMonoidHom.mk'_apply]
    rw [zsmul_eq_mul, zsmul_eq_mul]
  have hzero : primeLogHom c = ((0 : ℤ) : ℝ) := by rw [hval, hint]; simp
  obtain ⟨-, hc0⟩ := primeLog_indep_mod_one c 0 (by rw [← primeLogHom_apply]; exact hzero)
  have hnp : n = 0 := by
    have := congrArg (fun d : Nat.Primes →₀ ℤ => d p) hc0
    rw [hc] at this
    simpa [Finsupp.single_apply, hpq] using this
  have hmq : m = 0 := by
    have := congrArg (fun d : Nat.Primes →₀ ℤ => d q) hc0
    rw [hc] at this
    simpa [Finsupp.single_apply, hpq.symm] using this
  constructor
  · have hsd : (s.den : ℤ) ≠ 0 := by exact_mod_cast s.den_nz
    have htd : (t.den : ℤ) ≠ 0 := by exact_mod_cast t.den_nz
    have : s.num = 0 := by
      rw [hn] at hnp
      exact (mul_eq_zero.mp hnp).resolve_right htd
    exact Rat.zero_iff_num_zero.mpr this
  · have hsd : (s.den : ℤ) ≠ 0 := by exact_mod_cast s.den_nz
    have : t.num = 0 := by
      rw [hm] at hmq
      exact (mul_eq_zero.mp hmq).resolve_right hsd
    exact Rat.zero_iff_num_zero.mpr this

/-- Two real numbers are `ℝ`-dependent in `ℂ` when one of them is nonzero. -/
private theorem not_linearIndependent_real_ofReal_pair {x y : ℝ} (hx : x ≠ 0) :
    ¬ LinearIndependent ℝ ![((x : ℝ) : ℂ), ((y : ℝ) : ℂ)] := by
  intro h
  rw [LinearIndependent.pair_iff] at h
  obtain ⟨-, h2⟩ := h y (-x) (by
    simp only [Complex.real_smul]
    push_cast
    ring)
  exact hx (neg_eq_zero.mp h2)

/-- **The two-shift quasi-period rank law at two prime logarithms.**  A differentiable function
reproduced up to constant multipliers by the translations `log p` and `log q` is differentially
algebraic — the step the gauge reformulation of the prime-cocycle card invokes. -/
theorem differentiallyAlgebraic_of_primeLog_quasiperiods {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    {p q : Nat.Primes} (hpq : p ≠ q) {a b : ℂ}
    (h₁ : ∀ z, f (z + ((Real.log (p : ℕ) : ℝ) : ℂ)) = a * f z)
    (h₂ : ∀ z, f (z + ((Real.log (q : ℕ) : ℝ) : ℂ)) = b * f z) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_quasiperiods_realDependent hd
    (linearIndependent_rat_primeLog_pair hpq) ?_ h₁ h₂
  refine not_linearIndependent_real_ofReal_pair ?_
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  exact ne_of_gt (Real.log_pos hp1)

end

end GaloisForLFunctions.HTGeometry
