import GaloisForLFunctions.RHTower.ReflectionCocycleCurvature

/-!
# Polynomial-exponent reflection cocycles are conductor-type

A reflection cocycle with *polynomial exponent* is a carrier of the shape `h(s) = exp(P(s))` for a
polynomial `P`.  Two constraints act on such a cocycle.

* **The reflection constraint.**  `P(s) + P(1−s) = c` for a constant `c`.  Recentred at the fixed
  point `s = 1/2` — writing `Q(u) = P(u + 1/2)` — this says `Q(u) + Q(−u) = c`, i.e. the even part of
  `Q` is the constant `c/2`.  Every even-degree coefficient of `Q` of positive degree therefore
  vanishes, and `Q` (hence `P`, recentred) is an odd polynomial plus a constant.

* **Polynomially bounded modulus on every vertical line.**  `|h(σ + it)| ≤ C_σ (2 + |t|)^{m_σ}`,
  equivalently `Re P(σ + it) ≤ K_σ · log(2 + |t|)` for each fixed `σ`.

These two constraints force `deg P ≤ 1`, so `h` is exactly a member of the conductor family
`exp(a(s − 1/2) + b)`.

**Mechanism.**  Suppose the recentred `Q` had odd degree `d ≥ 3` with leading coefficient `q ≠ 0`.
Restrict to the vertical line `Re s = x₀` and read the real part of `Q` as a real polynomial in the
height `t`.  Its two top real coefficients are governed by `q · I^d` (degree `d`, independent of the
line) and by `d · x₀ · q · I^{d−1}` (degree `d − 1`, activated by moving the line off centre; the
degree-`(d−1)` coefficient of `Q` itself is even and hence zero, so this is the whole contribution).

  * If `Im q ≠ 0`, the degree-`d` real coefficient `−(±1)·Im q` is nonzero already on the central
    line `x₀ = 0`: `Re Q` grows like `|t|^d`.
  * If `Im q = 0` (so `Re q ≠ 0`), the degree-`d` real part vanishes, but choosing `x₀ = ±1`
    activates the degree-`(d−1)` real coefficient `d · x₀ · (±1) · Re q ≠ 0`: `Re Q` grows like
    `|t|^{d−1} ≥ |t|^(2 : ℕ)`.

Either way `Re Q`, hence `Re P` on some vertical line, grows faster than any multiple of
`log(2 + |t|)`, contradicting the vertical bound.  Thus `deg P ≤ 1`.

**Consequence for the curvature invariant of `ReflectionCocycleCurvature`.**  Every polynomial-exponent
reflection cocycle satisfying the two constraints is curvature-flat: its logarithmic derivative is
constant, so `deriv (logDeriv h) = 0` (`cocycle_exponent_curvature_zero`).  Within zero-free
finite-order cocycle data the whole exponent tier is therefore conductor-type, and all reflection
curvature must originate in the divisor (Gamma-type) part of the carrier.
-/

noncomputable section

namespace RHTower

open Complex Polynomial

/-- Coefficients of a composition with the scaling `s ↦ c·s`.  Substituting `C c * X` into a
polynomial multiplies its `k`-th coefficient by `c^k`; this is additive in the polynomial and, on a
monomial `a·X^n`, reads off the single term `a·c^n·X^n`. -/
private theorem coeff_comp_C_mul_X (c : ℂ) (Q : Polynomial ℂ) (k : ℕ) :
    (Q.comp (Polynomial.C c * Polynomial.X)).coeff k = c ^ k * Q.coeff k := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial n a =>
      rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
          Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      split_ifs with h
      · subst h; ring
      · ring

/-- **Even-degree coefficients vanish under the reflection constraint.**  If `P(s) + P(1−s) = c`
identically, then the recentred polynomial `Q(u) = P(u + 1/2)`, i.e. `Q = P.comp (X + C 2⁻¹)`,
satisfies `Q(u) + Q(−u) = c`.  Its even part is thus the constant `c/2`, so every coefficient of `Q`
of positive even degree is zero. -/
theorem shifted_coeff_even_eq_zero {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    {k : ℕ} (hk : k ≠ 0) (hke : Even k) :
    (P.comp (Polynomial.X + Polynomial.C (2⁻¹ : ℂ))).coeff k = 0 := by
  set Q := P.comp (Polynomial.X + Polynomial.C (2⁻¹ : ℂ)) with hQdef
  have hQeval : ∀ u : ℂ, Q.eval u = P.eval (u + 2⁻¹) := by
    intro u
    rw [hQdef, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have hsum : ∀ u : ℂ, Q.eval u + Q.eval (-u) = c := by
    intro u
    rw [hQeval, hQeval]
    have h := hc (u + 2⁻¹)
    rw [show (1 : ℂ) - (u + 2⁻¹) = -u + 2⁻¹ from by ring] at h
    exact h
  have hpoly : Q + Q.comp (-Polynomial.X) - Polynomial.C c = 0 := by
    apply Polynomial.funext
    intro u
    simp only [Polynomial.eval_zero, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
    linear_combination hsum u
  have hcoeffneg : (Q.comp (-Polynomial.X)).coeff k = (-1) ^ k * Q.coeff k := by
    have hnegX : (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1) * Polynomial.X := by simp
    rw [hnegX]; exact coeff_comp_C_mul_X (-1) Q k
  have hck := congrArg (fun p => Polynomial.coeff p k) hpoly
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, hcoeffneg, Polynomial.coeff_C,
    Polynomial.coeff_zero] at hck
  rw [if_neg hk, Even.neg_one_pow hke] at hck
  have h2 : (2 : ℂ) * Q.coeff k = 0 := by linear_combination hck
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **A real polynomial of degree `≥ 2` with positive leading coefficient outgrows `log`.**  For any
slope `K` there is a height `s` with `K · log(2 + |s|) < S(s)`.  Subtracting the affine perturbation
`|K|·(2 + X)` leaves a polynomial of the same degree `≥ 2` and the same positive leading coefficient,
whose values tend to `+∞`; picking `s ≥ 1` large there, `S(s) > |K|·(2 + s) ≥ K · log(2 + s)` because
`log(2 + s) ≤ 2 + s`. -/
private theorem growth_lemma (S : Polynomial ℝ) (hS2 : 2 ≤ S.natDegree)
    (hSpos : 0 < S.leadingCoeff) (K : ℝ) : ∃ s : ℝ, K * Real.log (2 + |s|) < S.eval s := by
  set E : Polynomial ℝ := Polynomial.C (|K|) * (Polynomial.C 2 + Polynomial.X) with hEdef
  have h1 : (Polynomial.C 2 + Polynomial.X : Polynomial ℝ).natDegree = 1 := by
    rw [add_comm]; exact Polynomial.natDegree_X_add_C 2
  have hE_nd : E.natDegree ≤ 1 := by
    rw [hEdef]
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp only [Polynomial.natDegree_C, zero_add, h1, le_refl]
  set g : Polynomial ℝ := S - E with hgdef
  have hgN : g.coeff S.natDegree = S.leadingCoeff := by
    rw [hgdef, Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : E.natDegree < S.natDegree), sub_zero]
    exact Polynomial.coeff_natDegree
  have hgc : ∀ mm, S.natDegree < mm → g.coeff mm = 0 := by
    intro mm hmm
    rw [hgdef, Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hmm,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : E.natDegree < mm), sub_zero]
  have hgnd : g.natDegree = S.natDegree :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hgc)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hgN]; exact ne_of_gt hSpos))
  have hg_lead : 0 < g.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hgnd, hgN]; exact hSpos
  have hg_deg_pos : 0 < g.degree := by rw [← Polynomial.natDegree_pos_iff_degree_pos]; omega
  have htends : Filter.Tendsto (fun x => Polynomial.eval x g) Filter.atTop Filter.atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg g hg_deg_pos (le_of_lt hg_lead)
  have hev : ∀ᶠ x in Filter.atTop, 0 < Polynomial.eval x g ∧ (1 : ℝ) ≤ x :=
    (htends.eventually_gt_atTop 0).and (Filter.eventually_ge_atTop 1)
  obtain ⟨x, hxg, hx1⟩ := hev.exists
  refine ⟨x, ?_⟩
  have hgev : Polynomial.eval x g = S.eval x - |K| * (2 + x) := by
    rw [hgdef, Polynomial.eval_sub, hEdef, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have hxabs : |x| = x := abs_of_nonneg (by linarith)
  have hlog_le : Real.log (2 + x) ≤ 2 + x := Real.log_le_self (by linarith)
  have hlog_nn : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  rw [hxabs]
  have h1 : K * Real.log (2 + x) ≤ |K| * (2 + x) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) hlog_nn)
      (mul_le_mul_of_nonneg_left hlog_le (abs_nonneg K))
  have h2 : |K| * (2 + x) < S.eval x := by rw [hgev] at hxg; linarith
  linarith

/-- **Vertical real-part growth of an odd polynomial of degree `≥ 3`.**  If a polynomial `Q` has all
positive-even-degree coefficients zero and `natDegree Q ≥ 3`, then its degree `d` is odd, and there is
a vertical line `Re s = x₀` along which `Re Q(x₀ + it)` outgrows every multiple of `log(2 + |t|)`.

The two leading real coefficients of the height polynomial `t ↦ Re Q(x₀ + it)` are read from
`q · I^d` and `d · x₀ · q · I^{d−1}` (`q = leadingCoeff Q`); the degree-`(d−1)` coefficient of `Q`
itself is even, hence zero, so these are the only contributions.  When `Im q ≠ 0` the central line
gives degree `d`; when `Im q = 0` an off-centre line `x₀ = ±1` gives degree `d − 1`.  In both cases a
real polynomial of degree `≥ 2` with positive leading coefficient outgrows `log`. -/
theorem exists_vertical_re_growth {Q : Polynomial ℂ}
    (hodd : ∀ k, k ≠ 0 → Even k → Q.coeff k = 0)
    (hdeg : 3 ≤ Q.natDegree) :
    ∃ x₀ : ℝ, ∀ K : ℝ, ∃ t : ℝ,
      K * Real.log (2 + |t|) < (Q.eval ((x₀ : ℂ) + (t : ℂ) * Complex.I)).re := by
  set d := Q.natDegree with hd
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hd; omega
  set q := Q.leadingCoeff with hq
  have hq0 : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hcdd : Q.coeff d = q := by rw [hd, hq]; exact Polynomial.coeff_natDegree
  have hd_odd : Odd d := by
    rcases Nat.even_or_odd d with he | ho
    · exact absurd (by rw [← hcdd]; exact hodd d (by omega) he) hq0
    · exact ho
  obtain ⟨m, hm⟩ := hd_odd
  set ε : ℝ := (-1 : ℝ) ^ m with hε
  have hεne : ε ≠ 0 := by rw [hε]; exact pow_ne_zero m (by norm_num)
  have hId : Complex.I ^ d = (ε : ℂ) * Complex.I := by
    rw [hm, pow_succ, pow_mul, Complex.I_sq, hε]; push_cast; ring
  have hcd1 : Q.coeff (d - 1) = 0 :=
    hodd (d - 1) (by omega) (by rw [hm]; exact ⟨m, by omega⟩)
  -- The core substitution facts, uniform in the line `x₀`.
  have key : ∀ x₀ : ℝ, ∃ R : Polynomial ℝ, R.natDegree ≤ d ∧
      R.coeff d = -(ε * q.im) ∧ R.coeff (d - 1) = (d : ℝ) * ε * x₀ * q.re ∧
      (∀ t : ℝ, R.eval t = (Q.eval ((x₀ : ℂ) + (t : ℂ) * Complex.I)).re) := by
    intro x₀
    set b : ℂ := -(x₀ : ℂ) * Complex.I with hbdef
    set inner : Polynomial ℂ := Polynomial.C Complex.I * Polynomial.X + Polynomial.C (x₀ : ℂ)
      with hinnerdef
    set T : Polynomial ℂ := Q.comp inner with hTdef
    set W : Polynomial ℂ := Q.comp (Polynomial.C Complex.I * Polynomial.X) with hWdef
    have hI0 : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hinner_nd : inner.natDegree = 1 := by rw [hinnerdef]; exact Polynomial.natDegree_linear hI0
    have hTn : T.natDegree = d := by
      rw [hTdef, Polynomial.natDegree_comp, hinner_nd, mul_one, ← hd]
    have hWcoeff : ∀ j, W.coeff j = Complex.I ^ j * Q.coeff j := by
      intro j; rw [hWdef]; exact coeff_comp_C_mul_X Complex.I Q j
    have hCIX_nd : (Polynomial.C Complex.I * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X Complex.I hI0
    have hWn : W.natDegree = d := by
      rw [hWdef, Polynomial.natDegree_comp, hCIX_nd, mul_one, ← hd]
    -- `T` is a Taylor shift of `W`.
    have hbid : Complex.I * b = (x₀ : ℂ) := by
      rw [hbdef,
        show Complex.I * (-(x₀ : ℂ) * Complex.I) = -(x₀ : ℂ) * (Complex.I * Complex.I) from by ring,
        Complex.I_mul_I]; ring
    have hcompid :
        (Polynomial.C Complex.I * Polynomial.X).comp (Polynomial.X + Polynomial.C b) = inner := by
      rw [hinnerdef, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, mul_add,
        ← Polynomial.C_mul, hbid]
    have hTtaylor : Polynomial.taylor b W = T := by
      rw [Polynomial.taylor_apply, hWdef, Polynomial.comp_assoc, hcompid]
    -- Leading two coefficients of `T`.
    have hchoose : d.choose (d - 1) = d := by
      rw [Nat.choose_symm (by omega : 1 ≤ d), Nat.choose_one_right]
    have hTcd : T.coeff d = Complex.I ^ d * q := by
      have hnd : (Polynomial.hasseDeriv d W).natDegree < 1 := by
        have hle := Polynomial.natDegree_hasseDeriv_le W d
        rw [hWn, Nat.sub_self] at hle; omega
      rw [← hTtaylor, Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range' hnd b,
        Finset.sum_range_one, Polynomial.hasseDeriv_coeff]
      simp only [Nat.zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one]
      rw [hWcoeff d, hcdd]
    have hc0 : (Polynomial.hasseDeriv (d - 1) W).coeff 0 = 0 := by
      rw [Polynomial.hasseDeriv_coeff, Nat.zero_add, Nat.choose_self, hWcoeff (d - 1), hcd1,
        mul_zero, mul_zero]
    have hc1 : (Polynomial.hasseDeriv (d - 1) W).coeff 1 = (d : ℂ) * (Complex.I ^ d * q) := by
      rw [Polynomial.hasseDeriv_coeff, show 1 + (d - 1) = d from by omega, hchoose, hWcoeff d, hcdd]
    have hTcd1 : T.coeff (d - 1) = (d : ℂ) * Complex.I ^ d * q * b := by
      have hnd : (Polynomial.hasseDeriv (d - 1) W).natDegree < 2 := by
        have hle := Polynomial.natDegree_hasseDeriv_le W (d - 1)
        rw [hWn] at hle; omega
      rw [← hTtaylor, Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range' hnd b,
        Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
      ring
    -- Real height polynomial of `T`.
    set R : Polynomial ℝ :=
      ∑ j ∈ Finset.range (T.natDegree + 1), Polynomial.monomial j (T.coeff j).re with hRdef
    have hRcoeff : ∀ k, R.coeff k = (T.coeff k).re := by
      intro k
      rw [hRdef, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range (T.natDegree + 1)) k fun j => (T.coeff j).re]
      by_cases hk : k ∈ Finset.range (T.natDegree + 1)
      · rw [if_pos hk]
      · rw [if_neg hk]
        rw [Finset.mem_range, not_lt] at hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : T.natDegree < k), Complex.zero_re]
    have hRle : R.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro mm hmm
      rw [hRcoeff mm,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hTn]; exact hmm), Complex.zero_re]
    have hRd : R.coeff d = -(ε * q.im) := by
      rw [hRcoeff d, hTcd, hId]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hRd1 : R.coeff (d - 1) = (d : ℝ) * ε * x₀ * q.re := by
      rw [hRcoeff (d - 1), hTcd1, hId, hbdef]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im, Complex.neg_re,
        Complex.neg_im]
      ring
    refine ⟨R, hRle, hRd, hRd1, ?_⟩
    intro t
    have hev : R.eval t = (T.eval (t : ℂ)).re := by
      have hRle' : R.natDegree < T.natDegree + 1 := by omega
      rw [Polynomial.eval_eq_sum_range' hRle' t,
        Polynomial.eval_eq_sum_range' (Nat.lt_succ_self T.natDegree) (t : ℂ), Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hRcoeff i, show ((t : ℂ)) ^ i = (((t ^ i : ℝ)) : ℂ) from by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hev]
    congr 1
    rw [hTdef, Polynomial.eval_comp, hinnerdef, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    ring
  -- Case analysis on the imaginary part of the leading coefficient.
  by_cases hqim : q.im = 0
  · -- `Im q = 0`, so `Re q ≠ 0`; use an off-centre line `x₀ = ±1`, giving even degree `d − 1`.
    have hqre : q.re ≠ 0 := fun h => hq0 (Complex.ext_iff.mpr ⟨h, hqim⟩)
    set x₀ : ℝ := if 0 < ε * q.re then (1 : ℝ) else -1 with hx0
    refine ⟨x₀, fun K => ?_⟩
    obtain ⟨R, hRle, hRd, hRd1, hReval⟩ := key x₀
    have hRcd0 : R.coeff d = 0 := by rw [hRd, hqim, mul_zero, neg_zero]
    have hexq : 0 < ε * x₀ * q.re := by
      have hεqre : ε * q.re ≠ 0 := mul_ne_zero hεne hqre
      by_cases hpos : 0 < ε * q.re
      · rw [hx0, if_pos hpos, mul_one]; exact hpos
      · rw [hx0, if_neg hpos]
        have hlt : ε * q.re < 0 := lt_of_le_of_ne (not_lt.mp hpos) hεqre
        nlinarith [hlt]
    have hR_d1_pos : 0 < R.coeff (d - 1) := by
      rw [hRd1]
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      nlinarith [mul_pos hdpos hexq]
    have hRle' : R.natDegree ≤ d - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro mm hmm
      rcases (by omega : d = mm ∨ d < mm) with hmd | hmd
      · rw [← hmd]; exact hRcd0
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hRle hmd)
    have hRn : R.natDegree = d - 1 :=
      le_antisymm hRle' (Polynomial.le_natDegree_of_ne_zero (ne_of_gt hR_d1_pos))
    have hRlead : 0 < R.leadingCoeff := by
      rw [← Polynomial.coeff_natDegree, hRn]; exact hR_d1_pos
    obtain ⟨s, hs⟩ := growth_lemma R (by rw [hRn]; omega) hRlead K
    exact ⟨s, by rw [← hReval s]; exact hs⟩
  · -- `Im q ≠ 0`; the central line `x₀ = 0` already gives odd degree `d`.
    refine ⟨0, fun K => ?_⟩
    obtain ⟨R, hRle, hRd, -, hReval⟩ := key 0
    have hRcd_ne : R.coeff d ≠ 0 := by
      rw [hRd]; exact neg_ne_zero.mpr (mul_ne_zero hεne hqim)
    have hRn : R.natDegree = d :=
      le_antisymm hRle (Polynomial.le_natDegree_of_ne_zero hRcd_ne)
    have hRlead : R.leadingCoeff = -(ε * q.im) := by
      rw [← Polynomial.coeff_natDegree, hRn, hRd]
    by_cases hsign : 0 < R.leadingCoeff
    · obtain ⟨s, hs⟩ := growth_lemma R (by rw [hRn]; omega) hsign K
      exact ⟨s, by rw [← hReval s]; exact hs⟩
    · have hlt : R.leadingCoeff < 0 :=
        lt_of_le_of_ne (not_lt.mp hsign) (by rw [hRlead]; exact neg_ne_zero.mpr (mul_ne_zero hεne hqim))
      have hSnd : (R.comp (-Polynomial.X)).natDegree = d := by
        rw [Polynomial.natDegree_comp, hRn, Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one]
      have hSlead : (R.comp (-Polynomial.X)).leadingCoeff = R.leadingCoeff * (-1) ^ d := by
        rw [Polynomial.leadingCoeff_comp
          (by rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]; exact one_ne_zero),
          hRn, Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X]
      have hSpos : 0 < (R.comp (-Polynomial.X)).leadingCoeff := by
        rw [hSlead, Odd.neg_one_pow (⟨m, hm⟩ : Odd d), mul_neg_one]; exact neg_pos.mpr hlt
      have hSeval : ∀ s : ℝ, (R.comp (-Polynomial.X)).eval s = R.eval (-s) := by
        intro s
        rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
      obtain ⟨s, hs⟩ := growth_lemma (R.comp (-Polynomial.X)) (by rw [hSnd]; omega) hSpos K
      refine ⟨-s, ?_⟩
      rw [abs_neg, ← hReval (-s), ← hSeval s]
      exact hs

/-- **The reflection and vertical-growth constraints force `deg P ≤ 1`.**  With `P(s) + P(1−s) = c`
and `Re P(σ + it) ≤ K_σ · log(2 + |t|)` on every vertical line, the recentred polynomial
`Q = P.comp (X + C 2⁻¹)` has all positive-even-degree coefficients zero; were its degree `≥ 3` it
would exhibit vertical real-part growth beating every `log`, contradicting the bound.  Degree `2` is
excluded because the degree-`2` coefficient of `Q` is even, hence its would-be leading coefficient
vanishes.  Hence `natDegree P ≤ 1`. -/
theorem cocycle_exponent_rigidity {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    (hgrowth : ∀ σ : ℝ, ∃ K : ℝ, ∀ t : ℝ,
        (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ K * Real.log (2 + |t|)) :
    P.natDegree ≤ 1 := by
  by_contra hcon
  push Not at hcon
  set Q := P.comp (Polynomial.X + Polynomial.C (2⁻¹ : ℂ)) with hQdef
  have hQn : Q.natDegree = P.natDegree := by
    rw [hQdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hodd : ∀ k, k ≠ 0 → Even k → Q.coeff k = 0 := fun k hk hke =>
    shifted_coeff_even_eq_zero hc hk hke
  have hQ2 : Q.natDegree ≠ 2 := by
    intro h2
    have hlc0 : Q.leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, h2]; exact hodd 2 (by norm_num) (by norm_num)
    have : Q = 0 := Polynomial.leadingCoeff_eq_zero.mp hlc0
    rw [this] at h2; simp at h2
  have hQ3 : 3 ≤ Q.natDegree := by
    have h2 : 2 ≤ Q.natDegree := by rw [hQn]; omega
    omega
  obtain ⟨x₀, hx₀⟩ := exists_vertical_re_growth hodd hQ3
  have hQeq : ∀ t : ℝ,
      Q.eval ((x₀ : ℂ) + (t : ℂ) * Complex.I)
        = P.eval (((x₀ + 2⁻¹ : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [hQdef, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    congr 1; push_cast; ring
  obtain ⟨K₀, hK₀⟩ := hgrowth (x₀ + 2⁻¹)
  obtain ⟨t, ht⟩ := hx₀ K₀
  rw [hQeq t] at ht
  exact absurd (lt_of_lt_of_le ht (hK₀ t)) (lt_irrefl _)

/-- **Curvature flatness of a polynomial-exponent reflection cocycle.**  Under the reflection and
vertical-growth constraints `deg P ≤ 1`, so `P' = C (P.coeff 1)` is constant.  The logarithmic
derivative of `s ↦ exp(P(s))` is `P'(s) = P.coeff 1`, a constant function, whose derivative vanishes:
the cocycle carries no curvature. -/
theorem cocycle_exponent_curvature_zero {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    (hgrowth : ∀ σ : ℝ, ∃ K : ℝ, ∀ t : ℝ,
        (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ K * Real.log (2 + |t|)) :
    deriv (logDeriv fun s => Complex.exp (P.eval s)) = (0 : ℂ → ℂ) := by
  have hle : P.natDegree ≤ 1 := cocycle_exponent_rigidity hc hgrowth
  have hderiv : Polynomial.derivative P = Polynomial.C (P.coeff 1) := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hle]
    simp [Polynomial.derivative_X, Polynomial.derivative_C]
  have hlogeq : (logDeriv fun s => Complex.exp (P.eval s)) = fun _ => P.coeff 1 := by
    funext s
    have hHD : HasDerivAt (fun z => Complex.exp (P.eval z))
        (Complex.exp (P.eval s) * (Polynomial.derivative P).eval s) s :=
      (Complex.hasDerivAt_exp (P.eval s)).comp s (Polynomial.hasDerivAt P s)
    rw [logDeriv_apply, hHD.deriv, hderiv, Polynomial.eval_C, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]
  rw [hlogeq]; funext s; simp

/-- **A polynomial-exponent reflection cocycle is exactly a conductor.**  Under the two constraints,
`Q = P.comp (X + C 2⁻¹)` has degree `≤ 1`, so `Q(u) = a·u + b` with `a = Q.coeff 1`, `b = Q.coeff 0`.
Since `P(s) = Q(s − 1/2)`, the carrier is `exp(P(s)) = exp(a·(s − 1/2) + b)`: the conductor family. -/
theorem cocycle_exponent_eq_conductor_form {P : Polynomial ℂ} {c : ℂ}
    (hc : ∀ s : ℂ, P.eval s + P.eval (1 - s) = c)
    (hgrowth : ∀ σ : ℝ, ∃ K : ℝ, ∀ t : ℝ,
        (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ K * Real.log (2 + |t|)) :
    ∃ a b : ℂ, ∀ s : ℂ, Complex.exp (P.eval s) = Complex.exp (a * (s - 2⁻¹) + b) := by
  have hle : P.natDegree ≤ 1 := cocycle_exponent_rigidity hc hgrowth
  set Q := P.comp (Polynomial.X + Polynomial.C (2⁻¹ : ℂ)) with hQdef
  have hQle : Q.natDegree ≤ 1 := by
    rw [hQdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]; exact hle
  have hQform : Q = Polynomial.C (Q.coeff 1) * Polynomial.X + Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hQle
  refine ⟨Q.coeff 1, Q.coeff 0, fun s => ?_⟩
  have hPev : P.eval s = Q.eval (s - 2⁻¹) := by
    rw [hQdef, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    congr 1; ring
  rw [hPev]
  congr 1
  conv_lhs => rw [hQform]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]

end RHTower
