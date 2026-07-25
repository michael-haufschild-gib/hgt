import Mathlib
import GaloisForLFunctions.HTGeometry.ShiftTwistDescent

/-!
# A shift defect with a single pole forces a polynomial antiderivative

Let `R = A / B` be a rational function over `C` in lowest terms and let

`g = R(X + 1) - R(X)`.

If `g` has all of its poles at the origin, then `B` is a unit: `R` is already a polynomial.

The mechanism is an extremal argument on the shift orbits of the poles.  Among the roots of `B`
choose `beta` of maximal real part and `gamma` of minimal real part.  Then `beta + 1` is not a root,
so `R(X+1)` is regular at `beta` while `R` is not: `beta` is a genuine pole of `g`.  Symmetrically
`gamma - 1` is not a root, so `gamma - 1` is a genuine pole of `g`.  If every pole of `g` is at the
origin this gives `beta = 0` and `gamma = 1`, contradicting `gamma.re <= beta.re`.

The consequence recorded at the end is the classical obstruction underlying Hölder's theorem: a
nonzero rational function with poles only at the origin and vanishing at infinity is never the shift
defect of a rational function.
-/

open Polynomial

namespace HTGeometry

/-- Coprimality makes the numerator nonvanishing at a root of the denominator. -/
theorem eval_num_ne_zero_of_isCoprime {A B : ℂ[X]} (hcop : IsCoprime A B)
    {b : ℂ} (hb : B.eval b = 0) : A.eval b ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  intro hA
  have := congrArg (fun p : ℂ[X] => p.eval b) huv
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hA, hb,
    mul_zero, zero_add, add_zero] at this
  exact one_ne_zero this.symm

/-- **The extremal shift-orbit obstruction, general shift.**  If the `h`-shift defect of `A / B` has
all its poles at the origin, then the denominator is trivial.  The extremal element of a shift orbit
is selected by the linear functional `z -> (z/h).re`, which increases by one along the orbit. -/
theorem denom_eq_one_of_shift_defect_pole_at_zero_gen
    {A B q : ℂ[X]} {h : ℂ} (hh : h ≠ 0) (hB : B.Monic) (hcop : IsCoprime A B) (m : ℕ)
    (hid : (A.comp (X + Polynomial.C h) * B - A * B.comp (X + Polynomial.C h)) * X ^ m
        = q * (B.comp (X + Polynomial.C h) * B)) :
    B = 1 := by
  classical
  by_contra hne
  have hdeg : 0 < B.natDegree := by
    rcases Nat.eq_zero_or_pos B.natDegree with h0 | hp
    · exact absurd (by
        have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hc1 : B.coeff 0 = 1 := by rw [← h0]; exact hB.coeff_natDegree
        rw [hC, hc1, Polynomial.C_1]) hne
    · exact hp
  have hBne : B ≠ 0 := hB.ne_zero
  set f : ℂ → ℝ := fun z => (z / h).re with hf
  have hfshift : ∀ z : ℂ, f (z + h) = f z + 1 := by
    intro z
    rw [hf]
    simp only [add_div, div_self hh, Complex.add_re, Complex.one_re]
  have hrootsNe : B.roots.toFinset.Nonempty := by
    obtain ⟨z, hz⟩ := Complex.exists_root (by
      exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg))
    exact ⟨z, by simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using hz⟩
  obtain ⟨beta, hbetaMem, hbetaMax⟩ := B.roots.toFinset.exists_max_image f hrootsNe
  obtain ⟨gamma, hgammaMem, hgammaMin⟩ := B.roots.toFinset.exists_min_image f hrootsNe
  have hbetaRoot : B.eval beta = 0 :=
    (Polynomial.mem_roots hBne).mp ((Multiset.mem_toFinset).mp hbetaMem)
  have hgammaRoot : B.eval gamma = 0 :=
    (Polynomial.mem_roots hBne).mp ((Multiset.mem_toFinset).mp hgammaMem)
  have hbeta1 : B.eval (beta + h) ≠ 0 := by
    intro hz
    have hmem : beta + h ∈ B.roots.toFinset := by
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using hz
    have := hbetaMax _ hmem
    rw [hfshift] at this
    linarith
  have hgamma1 : B.eval (gamma - h) ≠ 0 := by
    intro hz
    have hmem : gamma - h ∈ B.roots.toFinset := by
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using hz
    have hlt := hgammaMin _ hmem
    have hgs : f (gamma - h) + 1 = f gamma := by
      have hgt := hfshift (gamma - h)
      rw [sub_add_cancel] at hgt
      exact hgt.symm
    linarith
  have hAbeta : A.eval beta ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hbetaRoot
  have hAgamma : A.eval gamma ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hgammaRoot
  have hEvalBeta := congrArg (fun p : ℂ[X] => p.eval beta) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    hbetaRoot, mul_zero, zero_mul, zero_sub, sub_zero, mul_one] at hEvalBeta
  have hbeta0 : beta = 0 := by
    have hzero : A.eval beta * B.eval (beta + h) * beta ^ m = 0 := by
      linear_combination -hEvalBeta
    have hpow : beta ^ m = 0 := by
      rcases mul_eq_zero.mp hzero with hx | hx
      · exact absurd hx (mul_ne_zero hAbeta hbeta1)
      · exact hx
    exact pow_eq_zero_iff'.mp hpow |>.1
  have hgammaShift : B.eval ((gamma - h) + h) = 0 := by
    rw [sub_add_cancel]; exact hgammaRoot
  have hEvalGamma := congrArg (fun p : ℂ[X] => p.eval (gamma - h)) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    hgammaShift, mul_zero, zero_mul, sub_zero, mul_one] at hEvalGamma
  have hgamma0 : gamma - h = 0 := by
    have hzero : A.eval ((gamma - h) + h) * B.eval (gamma - h) * (gamma - h) ^ m = 0 := by
      linear_combination hEvalGamma
    rw [sub_add_cancel] at hzero
    have hpow : (gamma - h) ^ m = 0 := by
      rcases mul_eq_zero.mp hzero with hx | hx
      · exact absurd hx (mul_ne_zero hAgamma hgamma1)
      · exact hx
    exact pow_eq_zero_iff'.mp hpow |>.1
  have hgeq : f gamma ≤ f beta := hgammaMin _ hbetaMem
  have hg1 : gamma = h := sub_eq_zero.mp hgamma0
  rw [hbeta0, hg1] at hgeq
  rw [hf] at hgeq
  simp only [zero_div, Complex.zero_re, div_self hh, Complex.one_re] at hgeq
  linarith

/-- **The extremal shift-orbit obstruction.**  If the shift defect of `A / B` has all its poles at
the origin, then the denominator is trivial. -/
theorem denom_eq_one_of_shift_defect_pole_at_zero
    {A B q : ℂ[X]} (hB : B.Monic) (hcop : IsCoprime A B) (m : ℕ)
    (hid : (A.comp (X + 1) * B - A * B.comp (X + 1)) * X ^ m
        = q * (B.comp (X + 1) * B)) :
    B = 1 := by
  classical
  by_contra hne
  -- `B` is monic and not `1`, so it has positive degree and hence a root.
  have hdeg : 0 < B.natDegree := by
    rcases Nat.eq_zero_or_pos B.natDegree with h0 | h
    · exact absurd (by
        have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hc1 : B.coeff 0 = 1 := by rw [← h0]; exact hB.coeff_natDegree
        rw [hC, hc1, Polynomial.C_1]) hne
    · exact h
  have hBne : B ≠ 0 := hB.ne_zero
  have hrootsNe : B.roots.toFinset.Nonempty := by
    obtain ⟨z, hz⟩ := Complex.exists_root (by
      exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg))
    exact ⟨z, by simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using hz⟩
  obtain ⟨beta, hbetaMem, hbetaMax⟩ :=
    B.roots.toFinset.exists_max_image (fun z : ℂ => z.re) hrootsNe
  obtain ⟨gamma, hgammaMem, hgammaMin⟩ :=
    B.roots.toFinset.exists_min_image (fun z : ℂ => z.re) hrootsNe
  have hbetaRoot : B.eval beta = 0 := by
    have := (Multiset.mem_toFinset).mp hbetaMem
    exact (Polynomial.mem_roots hBne).mp this
  have hgammaRoot : B.eval gamma = 0 := by
    have := (Multiset.mem_toFinset).mp hgammaMem
    exact (Polynomial.mem_roots hBne).mp this
  -- `beta + 1` is not a root: its real part is strictly larger.
  have hbeta1 : B.eval (beta + 1) ≠ 0 := by
    intro h
    have hmem : beta + 1 ∈ B.roots.toFinset := by
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using h
    have := hbetaMax _ hmem
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  -- `gamma - 1` is not a root: its real part is strictly smaller.
  have hgamma1 : B.eval (gamma - 1) ≠ 0 := by
    intro h
    have hmem : gamma - 1 ∈ B.roots.toFinset := by
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots, hBne] using h
    have := hgammaMin _ hmem
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have hAbeta : A.eval beta ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hbetaRoot
  have hAgamma : A.eval gamma ≠ 0 := eval_num_ne_zero_of_isCoprime hcop hgammaRoot
  -- Evaluate the identity at `beta`.
  have hEvalBeta := congrArg (fun p : ℂ[X] => p.eval beta) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    hbetaRoot, mul_zero, zero_mul, zero_sub, sub_zero, mul_one] at hEvalBeta
  have hbeta0 : beta = 0 := by
    have hzero : A.eval beta * B.eval (beta + 1) * beta ^ m = 0 := by
      linear_combination -hEvalBeta
    have hpow : beta ^ m = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (mul_ne_zero hAbeta hbeta1)
      · exact h
    exact pow_eq_zero_iff'.mp hpow |>.1
  -- Evaluate the identity at `gamma - 1`.
  have hgammaShift : B.eval ((gamma - 1) + 1) = 0 := by
    rw [sub_add_cancel]; exact hgammaRoot
  have hEvalGamma := congrArg (fun p : ℂ[X] => p.eval (gamma - 1)) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    hgammaShift, mul_zero, zero_mul, sub_zero, mul_one] at hEvalGamma
  have hgamma0 : gamma - 1 = 0 := by
    have hzero : A.eval ((gamma - 1) + 1) * B.eval (gamma - 1) * (gamma - 1) ^ m = 0 := by
      linear_combination hEvalGamma
    rw [sub_add_cancel] at hzero
    have hpow : (gamma - 1) ^ m = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (mul_ne_zero hAgamma hgamma1)
      · exact h
    exact pow_eq_zero_iff'.mp hpow |>.1
  -- The two conclusions are incompatible with the choice of extremes.
  have hgeq : gamma.re ≤ beta.re := hgammaMin _ hbetaMem
  have hg1 : gamma = 1 := by
    have := sub_eq_zero.mp hgamma0
    exact this
  rw [hbeta0, hg1] at hgeq
  simp only [Complex.one_re, Complex.zero_re] at hgeq
  linarith

/-- **The obstruction underlying Hölder's theorem.**  A nonzero rational function whose poles are
all at the origin and which vanishes at infinity is never the shift defect of a rational function.

Here `q / X ^ m` with `q ≠ 0` and `deg q < m` is exactly such a function, and the hypothesis is the
cleared-denominator form of `R (X + 1) - R X = q / X ^ m` for `R = A / B` in lowest terms. -/
theorem no_rational_shift_antiderivative
    {A B q : ℂ[X]} (hB : B.Monic) (hcop : IsCoprime A B) {m : ℕ}
    (hq : q ≠ 0) (hqdeg : q.natDegree < m)
    (hid : (A.comp (X + 1) * B - A * B.comp (X + 1)) * X ^ m
        = q * (B.comp (X + 1) * B)) :
    False := by
  have hB1 : B = 1 := denom_eq_one_of_shift_defect_pole_at_zero hB hcop m hid
  subst hB1
  simp only [Polynomial.one_comp, mul_one, one_mul] at hid
  rcases eq_or_ne (A.comp (X + 1) - A) 0 with h0 | h0
  · rw [h0, zero_mul] at hid
    exact hq hid.symm
  · have hXm : (X : ℂ[X]) ^ m ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    have hdeg : m ≤ ((A.comp (X + 1) - A) * X ^ m).natDegree := by
      rw [Polynomial.natDegree_mul h0 hXm, Polynomial.natDegree_X_pow]
      omega
    rw [hid] at hdeg
    omega

/-- **A shift-invariant rational function is constant.**  This is the algebraic core of the
statement that the shift-invariants of a field of meromorphic functions are the constants. -/
theorem shift_invariant_rational_constant
    {A B : ℂ[X]} (hB : B.Monic) (hcop : IsCoprime A B)
    (hid : A.comp (X + 1) * B = A * B.comp (X + 1)) :
    B = 1 ∧ A.natDegree = 0 := by
  have hrel : shiftTwist (RingEquiv.refl ℂ) 1 A * B
      = (A + Polynomial.C (0 : ℂ) * B) * shiftTwist (RingEquiv.refl ℂ) 1 B := by
    simp only [shiftTwist_refl, Polynomial.C_0, zero_mul, add_zero, Polynomial.C_1]
    exact hid
  obtain ⟨hfixB, hfixA⟩ := shiftTwist_denom_fixed hB hcop hrel
  simp only [Polynomial.C_0, zero_mul, add_zero] at hfixA
  have hB1 : B = 1 := by
    by_contra hne
    have hdpos : 0 < B.natDegree := by
      rcases Nat.eq_zero_or_pos B.natDegree with h0 | h
      · exact absurd (by
          have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
          have hc1 : B.coeff 0 = 1 := by rw [← h0]; exact hB.coeff_natDegree
          rw [hC, hc1, Polynomial.C_1]) hne
      · exact h
    have hdef := defect_coeff_of_shiftTwist_eq hB hfixB rfl hdpos
    simp only [RingEquiv.refl_apply, sub_self, mul_one] at hdef
    have hz : (B.natDegree : ℂ) = 0 := by linear_combination hdef
    exact absurd (Nat.cast_eq_zero.mp hz) (by omega)
  refine ⟨hB1, ?_⟩
  by_contra hane
  have hapos : 0 < A.natDegree := Nat.pos_of_ne_zero hane
  have hAne : A ≠ 0 := fun h => by simp [h] at hapos
  have hcoeff := shiftTwist_coeff_sub_one (sigma := RingEquiv.refl ℂ) (c := (1 : ℂ))
    (P := A) rfl hapos
  rw [hfixA] at hcoeff
  simp only [RingEquiv.refl_apply, mul_one] at hcoeff
  have hzero : (A.natDegree : ℂ) * A.coeff A.natDegree = 0 := by linear_combination -hcoeff
  have hlead : A.coeff A.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hAne
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) hane
  · exact hlead h

/-- **Hölder's obstruction, general shift.** -/
theorem no_rational_shift_antiderivative_gen
    {A B q : ℂ[X]} {h : ℂ} (hh : h ≠ 0) (hB : B.Monic) (hcop : IsCoprime A B) {m : ℕ}
    (hq : q ≠ 0) (hqdeg : q.natDegree < m)
    (hid : (A.comp (X + Polynomial.C h) * B - A * B.comp (X + Polynomial.C h)) * X ^ m
        = q * (B.comp (X + Polynomial.C h) * B)) :
    False := by
  have hB1 : B = 1 := denom_eq_one_of_shift_defect_pole_at_zero_gen hh hB hcop m hid
  subst hB1
  simp only [Polynomial.one_comp, mul_one, one_mul] at hid
  rcases eq_or_ne (A.comp (X + Polynomial.C h) - A) 0 with h0 | h0
  · rw [h0, zero_mul] at hid
    exact hq hid.symm
  · have hXm : (X : ℂ[X]) ^ m ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    have hdeg : m ≤ ((A.comp (X + Polynomial.C h) - A) * X ^ m).natDegree := by
      rw [Polynomial.natDegree_mul h0 hXm, Polynomial.natDegree_X_pow]
      omega
    rw [hid] at hdeg
    omega

/-- **A shift-invariant rational function is constant, general shift.** -/
theorem shift_invariant_rational_constant_gen
    {A B : ℂ[X]} {h : ℂ} (hh : h ≠ 0) (hB : B.Monic) (hcop : IsCoprime A B)
    (hid : A.comp (X + Polynomial.C h) * B = A * B.comp (X + Polynomial.C h)) :
    B = 1 ∧ A.natDegree = 0 := by
  have hid0 : (A.comp (X + Polynomial.C h) * B - A * B.comp (X + Polynomial.C h)) * X ^ 0
      = 0 * (B.comp (X + Polynomial.C h) * B) := by
    rw [sub_eq_zero.mpr hid]
    simp
  have hB1 : B = 1 := denom_eq_one_of_shift_defect_pole_at_zero_gen hh hB hcop 0 hid0
  subst hB1
  refine ⟨rfl, ?_⟩
  simp only [Polynomial.one_comp, mul_one] at hid
  by_contra hane
  have hapos : 0 < A.natDegree := Nat.pos_of_ne_zero hane
  have hAne : A ≠ 0 := fun hz => by simp [hz] at hapos
  have hcoeff := shiftTwist_coeff_sub_one (sigma := RingEquiv.refl ℂ) (c := h) (P := A) rfl hapos
  rw [shiftTwist_refl, hid] at hcoeff
  simp only [RingEquiv.refl_apply] at hcoeff
  have hzero : (A.natDegree : ℂ) * h * A.coeff A.natDegree = 0 := by
    linear_combination -hcoeff
  have hlead : A.coeff A.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hAne
  rcases mul_eq_zero.mp hzero with hx | hx
  · rcases mul_eq_zero.mp hx with hy | hy
    · exact absurd (Nat.cast_eq_zero.mp hy) hane
    · exact hh hy
  · exact hlead hx

end HTGeometry
