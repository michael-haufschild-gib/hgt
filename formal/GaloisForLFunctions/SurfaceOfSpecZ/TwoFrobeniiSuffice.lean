import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEveryGapSet

/-!
# Two Frobenii suffice

The degrees of one prime, `pᵃ`, alias every height `2πm/log p` (`TheGeometricDegreesAlias`): their
series `Σ_a (pᵃ)^{1−s} = (1 − p^{1−s})⁻¹` has the same simple pole at `s = 1` and at
`s = 1 + 2πim/log p`. The degrees of two primes, `pᵃqᵇ`, form a rank-two monoid with `O(log² x)`
elements up to `x`, and their series

  `Σ_{a,b} (pᵃqᵇ)^{1−s} = (1 − p^{1−s})⁻¹ (1 − q^{1−s})⁻¹`   (`wSeries_unitWeight`)

has a double pole at `s = 1`, while on `Re s = 1`, `s ≠ 1`, at most one factor is singular: `p^{−c} = 1`
and `q^{−c} = 1` force `c = 0` because `pᴹ ≠ qᴺ` (`not_both_resonant`). So the weight `n · 1_{n = pᵃqᵇ}`
is a sampling weight (`samplingWeight_unitWeight`), and:

* `onLine_of_bddBelow_twoPrimes_of_max`: for a tempered configuration without real zeros whose
  maximal real part is attained, `2 Re S(a log p + b log q) ≥ −K` for all `a, b ≥ 0` puts every zero
  on the line; with real zeros, the maximal real part is that of a real zero
  (`onLine_or_re_mem_of_bddBelow_twoPrimes`);
* `onLine_of_bddAbove_twoPrimes_of_max`: an upper bound does the same, real zeros included;
* for `ζ` a one-sided bound at the `pᵃqᵇ` leaves no deepest off-line zero
  (`exists_re_gt_of_bddBelow_twoPrimes`).

The surface's degree lattice `ℕ²` of the two Frobenii `Γ_p, Γ_q` samples the zeros; a single Frobenius
does not.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {p q : ℕ}

open Classical in
/-- The degrees `pᵃqᵇ` weighted by `n`, at `n = j + 1`. -/
def unitWeight (p q : ℕ) (j : ℕ) : ℝ :=
  if ∃ a b : ℕ, j + 1 = p ^ a * q ^ b then (j : ℝ) + 1 else 0

theorem unitWeight_nonneg (j : ℕ) : 0 ≤ unitWeight p q j := by
  unfold unitWeight; split_ifs <;> positivity

/-- The index of `pᵃqᵇ`. -/
def unitIndex (p q : ℕ) (ab : ℕ × ℕ) : ℕ := p ^ ab.1 * q ^ ab.2 - 1

theorem factorization_pow_mul_pow (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b : ℕ) :
    (p ^ a * q ^ b).factorization p = a ∧ (p ^ a * q ^ b).factorization q = b := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Nat.factorization_pow, Nat.factorization_pow, hp.factorization, hq.factorization]
  simp [hpq, Ne.symm hpq]

theorem unitIndex_add_one (hp : p.Prime) (hq : q.Prime) (ab : ℕ × ℕ) :
    unitIndex p q ab + 1 = p ^ ab.1 * q ^ ab.2 :=
  Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)))

theorem unitIndex_injective (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (unitIndex p q) := by
  intro x y hxy
  have h : p ^ x.1 * q ^ x.2 = p ^ y.1 * q ^ y.2 := by
    rw [← unitIndex_add_one hp hq x, ← unitIndex_add_one hp hq y, hxy]
  have hx := factorization_pow_mul_pow hp hq hpq x.1 x.2
  have hy := factorization_pow_mul_pow hp hq hpq y.1 y.2
  rw [h] at hx
  exact Prod.ext (hx.1.symm.trans hy.1) (hx.2.symm.trans hy.2)

theorem unitWeight_ne_zero {j : ℕ} (hj : unitWeight p q j ≠ 0) :
    ∃ ab, unitIndex p q ab = j := by
  unfold unitWeight at hj
  split_ifs at hj with h
  · obtain ⟨a, b, hab⟩ := h
    refine ⟨(a, b), ?_⟩
    show p ^ a * q ^ b - 1 = j
    rw [← hab, Nat.add_sub_cancel]
  · exact absurd rfl hj

theorem log_unitIndex_add_one (hp : p.Prime) (hq : q.Prime) (ab : ℕ × ℕ) :
    Real.log ((unitIndex p q ab : ℝ) + 1) = ab.1 * Real.log p + ab.2 * Real.log q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [show ((unitIndex p q ab : ℝ) + 1) = (p : ℝ) ^ ab.1 * (q : ℝ) ^ ab.2 by
      exact_mod_cast unitIndex_add_one hp hq ab,
    Real.log_mul (pow_pos hp0 _).ne' (pow_pos hq0 _).ne', Real.log_pow, Real.log_pow]

/-- The term of `pᵃqᵇ` is `(p^{1−s})ᵃ (q^{1−s})ᵇ`. -/
theorem unitTerm_eq (hp : p.Prime) (hq : q.Prime) (ab : ℕ × ℕ) (s : ℂ) :
    ((unitWeight p q (unitIndex p q ab) : ℝ) : ℂ) * ((unitIndex p q ab : ℂ) + 1) ^ (-s) =
      cexp ((Real.log p : ℂ) * (1 - s)) ^ ab.1 * cexp ((Real.log q : ℂ) * (1 - s)) ^ ab.2 := by
  have hpos : (0 : ℝ) < (unitIndex p q ab : ℝ) + 1 := by positivity
  have hw : ((unitWeight p q (unitIndex p q ab) : ℝ) : ℂ) =
      cexp ((Real.log ((unitIndex p q ab : ℝ) + 1) : ℝ) : ℂ) := by
    unfold unitWeight
    rw [if_pos ⟨ab.1, ab.2, unitIndex_add_one hp hq ab⟩, ← Complex.ofReal_exp, Real.exp_log hpos]
  rw [hw, natCast_add_one_cpow_eq, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, log_unitIndex_add_one hp hq ab]
  congr 1
  push_cast
  ring

theorem norm_cexp_log_mul_one_sub_lt (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖cexp ((Real.log p : ℂ) * (1 - s))‖ < 1 := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [Complex.norm_exp]
  have : ((Real.log p : ℂ) * (1 - s)).re = Real.log p * (1 - s.re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  rw [this]
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlp (by linarith))

theorem summable_unitTerm (hp : p.Prime) (hq : q.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable fun ab : ℕ × ℕ =>
      cexp ((Real.log p : ℂ) * (1 - s)) ^ ab.1 * cexp ((Real.log q : ℂ) * (1 - s)) ^ ab.2 := by
  have hX := norm_cexp_log_mul_one_sub_lt hp hs
  have hY := norm_cexp_log_mul_one_sub_lt hq hs
  exact summable_mul_of_summable_norm
    (f := fun a : ℕ => cexp ((Real.log p : ℂ) * (1 - s)) ^ a)
    (g := fun b : ℕ => cexp ((Real.log q : ℂ) * (1 - s)) ^ b)
    (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hX)
    (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hY)

theorem support_unitSeries_subset (s : ℂ) :
    Function.support (fun j : ℕ => (unitWeight p q j : ℂ) * ((j : ℂ) + 1) ^ (-s)) ⊆
      Set.range (unitIndex p q) := by
  intro j hj
  have : unitWeight p q j ≠ 0 := fun h0 => hj (by simp [h0])
  exact unitWeight_ne_zero this

theorem summable_unitSeries (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {s : ℂ}
    (hs : 1 < s.re) : Summable fun j : ℕ => (unitWeight p q j : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
  rw [← (unitIndex_injective hp hq hpq).summable_iff (fun j hj => by
    by_contra h0; exact hj (support_unitSeries_subset s h0))]
  exact (summable_unitTerm hp hq hs).congr fun ab => (unitTerm_eq hp hq ab s).symm

/-- **The series of the two-prime degrees.** -/
theorem wSeries_unitWeight (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {s : ℂ} (hs : 1 < s.re) :
    wSeries (unitWeight p q) s = (1 - cexp ((Real.log p : ℂ) * (1 - s)))⁻¹ *
      (1 - cexp ((Real.log q : ℂ) * (1 - s)))⁻¹ := by
  have hX := norm_cexp_log_mul_one_sub_lt hp hs
  have hY := norm_cexp_log_mul_one_sub_lt hq hs
  rw [← tsum_geometric_of_norm_lt_one hX, ← tsum_geometric_of_norm_lt_one hY,
    tsum_mul_tsum_of_summable_norm
      (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hX)
      (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hY),
    wSeries, ← (unitIndex_injective hp hq hpq).tsum_eq (support_unitSeries_subset s)]
  exact tsum_congr fun ab => unitTerm_eq hp hq ab s

/-- `p^{−c} = q^{−c} = 1` only for `c = 0`. -/
theorem not_both_resonant (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {c : ℂ} (hc : c ≠ 0) :
    ¬ (cexp (-(Real.log p : ℂ) * c) = 1 ∧ cexp (-(Real.log q : ℂ) * c) = 1) := by
  rintro ⟨h1, h2⟩
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h2
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  have key : ((n : ℂ) * Real.log q) * (2 * Real.pi * I) =
      ((m : ℂ) * Real.log p) * (2 * Real.pi * I) := by
    linear_combination (Real.log p : ℂ) * hm - (Real.log q : ℂ) * hn
  have keyC := mul_right_cancel₀ hπ key
  have keyR : (n : ℝ) * Real.log q = m * Real.log p := by exact_mod_cast keyC
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : (Real.log p : ℂ) * c = 0 := by
      have h := hn
      rw [Int.cast_zero, zero_mul] at h
      linear_combination -h
    rcases mul_eq_zero.mp this with h | h
    · exact hlp.ne' (by exact_mod_cast h)
    · exact hc h
  -- `|n| log q = |m| log p` gives `q^{|n|} = p^{|m|}`
  have habs : (n.natAbs : ℝ) * Real.log q = m.natAbs * Real.log p := by
    have := congrArg abs keyR
    rw [abs_mul, abs_mul, abs_of_pos hlq, abs_of_pos hlp] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact this
  have hpow : (q : ℝ) ^ n.natAbs = (p : ℝ) ^ m.natAbs := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hq0 _)) (Set.mem_Ioi.mpr (pow_pos hp0 _))
    rw [Real.log_pow, Real.log_pow, habs]
  have hpowN : q ^ n.natAbs = p ^ m.natAbs := by exact_mod_cast hpow
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
  have hM : 0 < m.natAbs := by
    by_contra h0
    push Not at h0
    have : m.natAbs = 0 := by omega
    rw [this, pow_zero] at hpowN
    exact absurd hpowN (Nat.one_lt_pow hN.ne' hq.one_lt).ne'
  have hdvd : p ∣ q ^ n.natAbs := by
    rw [hpowN]; exact dvd_pow_self p hM.ne'
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- One factor `(1 − P)/(1 − P u)`, `P = p^{1−σ}`, tends to `1` if `u = 1` and to `0` otherwise. -/
theorem tendsto_unitFactor {b : ℕ} (hb : 1 < b) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    Tendsto (fun σ : ℝ => (1 - cexp ((Real.log b : ℂ) * (1 - (σ : ℂ)))) /
      (1 - cexp ((Real.log b : ℂ) * (1 - (σ : ℂ))) * u)) (𝓝[>] 1)
      (𝓝 (if u = 1 then 1 else 0)) := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hE : Tendsto (fun σ : ℝ => cexp ((Real.log b : ℂ) * (1 - (σ : ℂ)))) (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous fun σ : ℝ => cexp ((Real.log b : ℂ) * (1 - (σ : ℂ))) := by fun_prop
    have := hc.tendsto 1
    simp only [Complex.ofReal_one, sub_self, mul_zero, Complex.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  split_ifs with hu1
  · subst hu1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hn : ‖cexp ((Real.log b : ℂ) * (1 - (σ : ℂ)))‖ < 1 := by
      rw [Complex.norm_exp]
      have : ((Real.log b : ℂ) * (1 - (σ : ℂ))).re = Real.log b * (1 - σ) := by
        rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      rw [this]
      exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlb (by linarith))
    have h1 : (1 : ℂ) - cexp ((Real.log b : ℂ) * (1 - (σ : ℂ))) ≠ 0 := by
      intro h0
      rw [show cexp ((Real.log b : ℂ) * (1 - (σ : ℂ))) = 1 by linear_combination -h0] at hn
      simp at hn
    rw [mul_one, div_self h1]
  · have hden : (1 : ℂ) - 1 * u ≠ 0 := by rw [one_mul]; exact sub_ne_zero.mpr (Ne.symm hu1)
    have h2 : Tendsto (fun σ : ℝ => (1 - cexp ((Real.log b : ℂ) * (1 - (σ : ℂ)))) /
        (1 - cexp ((Real.log b : ℂ) * (1 - (σ : ℂ))) * u)) (𝓝[>] 1) (𝓝 ((1 - 1) / (1 - 1 * u))) :=
      ((tendsto_const_nhds (x := (1 : ℂ))).sub hE).div
        ((tendsto_const_nhds (x := (1 : ℂ))).sub (hE.mul_const u)) hden
    rwa [sub_self, zero_div] at h2

theorem norm_cexp_neg_log_mul_le (hp : p.Prime) {c : ℂ} (hre : 0 ≤ c.re) :
    ‖cexp (-(Real.log p : ℂ) * c)‖ ≤ 1 := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [Complex.norm_exp]
  have : (-(Real.log p : ℂ) * c).re = -(Real.log p * c.re) := by
    rw [← Complex.ofReal_neg, Complex.re_ofReal_mul]; ring
  rw [this, Real.exp_le_one_iff]
  have := mul_nonneg hlp.le hre
  linarith

theorem inv_mul_inv_div_inv_mul_inv (A B C D : ℂ) : A⁻¹ * B⁻¹ / (C⁻¹ * D⁻¹) = C / A * (D / B) := by
  rw [div_eq_mul_inv, mul_inv, inv_inv, inv_inv]; ring

/-- **The degrees of two primes form a sampling set.** -/
theorem samplingWeight_unitWeight (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    SamplingWeight (unitWeight p q) := by
  have hreal : ∀ σ : ℝ, 1 < σ → wSum (unitWeight p q) σ =
      ((1 - Real.exp (Real.log p * (1 - σ))) * (1 - Real.exp (Real.log q * (1 - σ))))⁻¹ := by
    intro σ hσ
    apply Complex.ofReal_injective
    rw [ofReal_wSum, wSeries_unitWeight hp hq hpq (by simpa using hσ)]
    push_cast
    rw [mul_inv]
  refine ⟨unitWeight_nonneg, fun σ hσ => ?_, ?_, fun c hc hre => ?_⟩
  · -- summability on `σ > 1`
    have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
    refine Complex.summable_ofReal.mp ((summable_unitSeries hp hq hpq hs).congr fun j => ?_)
    rw [Complex.ofReal_mul, ofReal_add_one_rpow j (-σ)]
    push_cast
    ring
  · -- the double pole at `σ = 1`
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
    have hg : Tendsto (fun σ : ℝ => (1 - Real.exp (Real.log p * (1 - σ))) *
        (1 - Real.exp (Real.log q * (1 - σ)))) (𝓝[>] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous fun σ : ℝ => (1 - Real.exp (Real.log p * (1 - σ))) *
            (1 - Real.exp (Real.log q * (1 - σ))) := by fun_prop
        have := hc.tendsto 1
        simp only [sub_self, mul_zero, Real.exp_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        have hσ1 : 1 < σ := hσ
        have h1 : Real.exp (Real.log p * (1 - σ)) < 1 :=
          Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlp (by linarith))
        have h2 : Real.exp (Real.log q * (1 - σ)) < 1 :=
          Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlq (by linarith))
        exact Set.mem_Ioi.mpr (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2))
    refine (tendsto_inv_nhdsGT_zero.comp hg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [Function.comp_apply, hreal σ hσ]
  · -- off `s = 1` at most a simple pole
    have hlim := (tendsto_unitFactor hp.one_lt (norm_cexp_neg_log_mul_le hp hre)).mul
      (tendsto_unitFactor hq.one_lt (norm_cexp_neg_log_mul_le hq hre))
    have h0 : (if cexp (-(Real.log p : ℂ) * c) = 1 then (1 : ℂ) else 0) *
        (if cexp (-(Real.log q : ℂ) * c) = 1 then 1 else 0) = 0 := by
      have := not_both_resonant hp hq hpq hc
      split_ifs with h1 h2 <;> simp_all
    rw [h0] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ1
    rw [wSeries_unitWeight hp hq hpq hs, ofReal_wSum, wSeries_unitWeight hp hq hpq hs0]
    have hXc : cexp ((Real.log p : ℂ) * (1 - ((σ : ℂ) + c))) =
        cexp ((Real.log p : ℂ) * (1 - (σ : ℂ))) * cexp (-(Real.log p : ℂ) * c) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hYc : cexp ((Real.log q : ℂ) * (1 - ((σ : ℂ) + c))) =
        cexp ((Real.log q : ℂ) * (1 - (σ : ℂ))) * cexp (-(Real.log q : ℂ) * c) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hXc, hYc, inv_mul_inv_div_inv_mul_inv]

/-- A bound at the degrees `pᵃqᵇ` is a bound where the two-prime weight is nonzero. -/
theorem bound_of_unitWeight_ne_zero (hp : p.Prime) (hq : q.Prime) {Z : ZeroConfig}
    {P : ℝ → Prop}
    (hK : ∀ a b : ℕ, P (2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re)) :
    ∀ j : ℕ, unitWeight p q j ≠ 0 →
      P (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) := by
  intro j hj
  obtain ⟨ab, rfl⟩ := unitWeight_ne_zero hj
  rw [log_unitIndex_add_one hp hq ab]
  exact hK ab.1 ab.2

/-- **Two Frobenii sample every top layer**, from below. -/
theorem onLine_of_bddBelow_twoPrimes_of_max (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ a b : ℕ,
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_samplingWeight (samplingWeight_unitWeight hp hq hpq) Z hZ hnoreal hρ₀ hmax
    (bound_of_unitWeight_ne_zero hp hq (P := fun x => -K ≤ x) hK)

/-- With real zeros: the line, or a real zero of maximal real part. -/
theorem onLine_or_re_mem_of_bddBelow_twoPrimes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ a b : ℕ,
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ∨ (ρ₀.re : ℂ) ∈ Z.carrier :=
  onLine_or_re_mem_of_bddBelow_of_samplingWeight (samplingWeight_unitWeight hp hq hpq) Z hZ hρ₀
    hmax (bound_of_unitWeight_ne_zero hp hq (P := fun x => -K ≤ x) hK)

/-- **Two Frobenii sample every top layer**, from above, real zeros included. -/
theorem onLine_of_bddAbove_twoPrimes_of_max (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ a b : ℕ,
      2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_of_samplingWeight (samplingWeight_unitWeight hp hq hpq) Z hZ hρ₀ hmax
    (bound_of_unitWeight_ne_zero hp hq (P := fun x => x ≤ K) hK)

/-- **For `ζ`, a lower bound at the `pᵃqᵇ` leaves no deepest off-line zero.** -/
theorem exists_re_gt_of_bddBelow_twoPrimes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {K : ℝ}
    (hK : ∀ a b : ℕ, -K ≤
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hoff : 1 / 2 < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_of_samplingWeight (samplingWeight_unitWeight hp hq hpq)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ hoff hno
    (bound_of_unitWeight_ne_zero hp hq (P := fun x => -K ≤ x) hK)
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

end GaloisForLFunctions.SurfaceOfSpecZ
