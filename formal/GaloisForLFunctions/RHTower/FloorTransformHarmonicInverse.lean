import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

/-!
# The floor transform and its critically stable harmonic inverse

For an arithmetic weight `a` the floor transform of a profile is

`(T_a f)(N) = ∑_{d ≤ N} a(d) f(⌊N/d⌋)`.

Floor associativity `⌊⌊N/d⌋/e⌋ = ⌊N/(de)⌋` and hyperbola regrouping give the exact composition law
`T_a T_b = T_{a*b}` for Dirichlet convolution.  Since the harmonic weight `1/d` and the weight
`μ(d)/d` are Dirichlet inverses, the harmonic floor average

`Q(N) = ∑_{d ≤ N} R(⌊N/d⌋)/d`

has the exact inverse `R(N) = ∑_{d ≤ N} μ(d) Q(⌊N/d⌋)/d`, and the two inversions are stable at the
critical exponent: a square-root bound for one gives a square-root bound for the other, with the
absolutely convergent majorant `∑ d^{-3/2-ε}`.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The floor transform of a profile by an arithmetic weight. -/
def floorTransform (a f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, a d * f (N / d)

/-- The Dirichlet convolution of two real weights. -/
def dirichletConv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, a d * b (n / d)

/-- **(24.10) Floor transforms compose by Dirichlet convolution.** -/
theorem floorTransform_comp (a b f : ℕ → ℝ) (N : ℕ) :
    floorTransform a (floorTransform b f) N = floorTransform (dirichletConv a b) f N := by
  classical
  have hL : floorTransform a (floorTransform b f) N
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
        a x.1 * b x.2 * f (N / (x.1 * x.2)) := by
    have hstep : floorTransform a (floorTransform b f) N
        = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
            a d * b e * f (N / (d * e)) := by
      rw [floorTransform]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [floorTransform, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Nat.div_div_eq_div_mul]
      ring
    rw [hstep, Finset.sum_sigma']
  have hR : floorTransform (dirichletConv a b) f N
      = ∑ y ∈ (Finset.Icc 1 N).sigma (fun n => n.divisors),
        a y.2 * b (y.1 / y.2) * f (N / y.1) := by
    have hstep : floorTransform (dirichletConv a b) f N
        = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d) * f (N / n) := by
      rw [floorTransform]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [dirichletConv, Finset.sum_mul]
    rw [hstep, Finset.sum_sigma']
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨x.1 * x.2, x.1⟩ : (_ : ℕ) × ℕ))
    (j := fun y => (⟨y.2, y.1 / y.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hx
    have hdpos : 0 < d := hd1
    have hmul : d * e ≤ N := by
      have hstep := (Nat.le_div_iff_mul_le hdpos).1 heN
      calc d * e = e * d := Nat.mul_comm d e
        _ ≤ N := hstep
    have hone : 1 ≤ d * e :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨hone, hmul⟩, dvd_mul_right d e, by omega⟩
  · rintro ⟨n, d⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy
    obtain ⟨⟨hn1, hnN⟩, hdvd, hn0⟩ := hy
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨hdpos, le_trans (Nat.le_of_dvd (by omega) hdvd) hnN⟩, ?_, ?_⟩
    · exact (Nat.one_le_div_iff hdpos).2 (Nat.le_of_dvd (by omega) hdvd)
    · exact Nat.div_le_div_right hnN
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨⟨hd1, _⟩, _, _⟩ := hx
    simp [Nat.mul_div_cancel_left _ (show 0 < d from hd1)]
  · rintro ⟨n, d⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy
    obtain ⟨⟨hn1, _⟩, hdvd, hn0⟩ := hy
    simp [Nat.mul_div_cancel' hdvd]
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨⟨hd1, _⟩, _, _⟩ := hx
    simp [Nat.mul_div_cancel_left _ (show 0 < d from hd1)]

/-! ## The harmonic pair -/

theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
  classical
  have h : ((ArithmeticFunction.moebius * ↑ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n
      = (1 : ArithmeticFunction ℤ) n := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [← h, Nat.sum_divisorsAntidiagonal (f := fun x y => ArithmeticFunction.moebius x
    * (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) y)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  have hd0 : n / d ≠ 0 := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2)
    exact Nat.div_ne_zero_iff.2 ⟨hdpos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1⟩
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hd0]

/-- The harmonic weight `1/d`. -/
def harmonicWeight (d : ℕ) : ℝ := 1 / d

/-- The critically stable Möbius weight `μ(d)/d`. -/
def moebiusHarmonicWeight (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) / d

/-- The Kronecker weight at one. -/
def unitWeight (n : ℕ) : ℝ := if n = 1 then 1 else 0

/-- **(24.11) The harmonic and Möbius-harmonic weights are Dirichlet inverse.** -/
theorem dirichletConv_harmonic_moebius {n : ℕ} (hn : n ≠ 0) :
    dirichletConv harmonicWeight moebiusHarmonicWeight n = unitWeight n := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hterm : ∀ d ∈ n.divisors,
      harmonicWeight d * moebiusHarmonicWeight (n / d)
        = (1 / (n : ℝ)) * (ArithmeticFunction.moebius (n / d) : ℝ) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hnpos
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd.1
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hdpos.ne'
    have hqne : ((n / d : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hd.1) hdpos
      exact Nat.cast_ne_zero.2 this.ne'
    have hcast : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, hmul]
    rw [harmonicWeight, moebiusHarmonicWeight]
    field_simp
    rw [← hcast]
    ring
  rw [dirichletConv, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) :=
    Nat.sum_div_divisors n (fun d => (ArithmeticFunction.moebius d : ℝ))
  rw [hsum]
  have hint := sum_divisors_moebius n
  have hreal : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)
      = ((if n = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := by
    rw [← hint]
    push_cast
    rfl
  rw [hreal, unitWeight]
  by_cases h1 : n = 1
  · subst h1
    norm_num
  · simp [h1]

/-- The floor transform by the unit weight is the identity. -/
theorem floorTransform_unitWeight (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    floorTransform unitWeight f N = f N := by
  classical
  rw [floorTransform]
  have hsingle : ∑ d ∈ Finset.Icc 1 N, unitWeight d * f (N / d)
      = ∑ d ∈ Finset.Icc 1 N, if d = 1 then f N else 0 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [unitWeight]
    by_cases h1 : d = 1
    · subst h1
      simp
    · simp [h1]
  rw [hsingle, Finset.sum_ite_eq' (Finset.Icc 1 N) 1 (fun _ => f N)]
  simp [Finset.mem_Icc, hN]

/-- **(24.12)--(24.13) The harmonic floor average has an exact Möbius-harmonic inverse.** -/
theorem floorTransform_moebiusHarmonic_harmonic (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    floorTransform moebiusHarmonicWeight (floorTransform harmonicWeight f) N = f N := by
  classical
  have hcomp := floorTransform_comp moebiusHarmonicWeight harmonicWeight f N
  have hconv : ∀ n : ℕ, n ≠ 0 →
      dirichletConv moebiusHarmonicWeight harmonicWeight n = unitWeight n := by
    intro n hn
    rw [dirichletConv]
    have hsymm : ∑ d ∈ n.divisors, moebiusHarmonicWeight d * harmonicWeight (n / d)
        = ∑ d ∈ n.divisors, harmonicWeight d * moebiusHarmonicWeight (n / d) := by
      classical
      have hstep := (Nat.sum_div_divisors n
        (fun d => moebiusHarmonicWeight d * harmonicWeight (n / d))).symm
      rw [hstep]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Nat.mem_divisors] at hd
      rw [Nat.div_div_self hd.1 hd.2]
      ring
    rw [hsymm]
    have := dirichletConv_harmonic_moebius hn
    rw [dirichletConv] at this
    exact this
  have hfun : floorTransform (dirichletConv moebiusHarmonicWeight harmonicWeight) f N
      = floorTransform unitWeight f N := by
    rw [floorTransform, floorTransform]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    rw [hconv d (by omega)]
  rw [hcomp, hfun, floorTransform_unitWeight f hN]

/-! ## Critical stability -/

theorem abs_harmonicWeight_le {d : ℕ} (hd : 1 ≤ d) : |harmonicWeight d| ≤ 1 / d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [harmonicWeight, abs_of_nonneg (by positivity)]

theorem abs_moebiusHarmonicWeight_le {d : ℕ} (hd : 1 ≤ d) :
    |moebiusHarmonicWeight d| ≤ 1 / d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have hint := ArithmeticFunction.abs_moebius_le_one (n := d)
    have hcast : |(ArithmeticFunction.moebius d : ℝ)|
        = ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast hint
  rw [moebiusHarmonicWeight, abs_div, abs_of_pos hdpos]
  exact div_le_div_of_nonneg_right hmu hdpos.le

/-- **(24.14) Critical stability of the floor inversion.**  Any weight dominated by the harmonic
weight transfers a square-root bound with the absolutely convergent majorant `∑ d^{-3/2-ε}`. -/
theorem abs_floorTransform_le_of_weight {w Q : ℕ → ℝ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hw : ∀ d : ℕ, 1 ≤ d → |w d| ≤ 1 / d)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform w Q N|
      ≤ C * (N : ℝ) ^ (1 / 2 + ε) * ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(3 / 2 + ε)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNrpow : (0 : ℝ) < (N : ℝ) ^ (1 / 2 + ε) := Real.rpow_pos_of_pos hNpos _
  rw [floorTransform]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hdN⟩ := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hquot : 1 ≤ N / d := (Nat.one_le_div_iff hd1).2 hdN
  have hQd := hQ (N / d) hquot
  have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hrp : ((N / d : ℕ) : ℝ) ^ (1 / 2 + ε) ≤ ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
  have hsplit : ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε)
      = (N : ℝ) ^ (1 / 2 + ε) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹ := by
    rw [Real.div_rpow hNpos.le hdpos.le]
    ring
  have hpow : (1 / (d : ℝ)) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹ = (d : ℝ) ^ (-(3 / 2 + ε)) := by
    have hid : (d : ℝ) * (d : ℝ) ^ (1 / 2 + ε) = (d : ℝ) ^ (3 / 2 + ε) := by
      nth_rewrite 1 [show (d : ℝ) = (d : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hdpos]
      congr 1
      ring
    rw [Real.rpow_neg hdpos.le, one_div, ← mul_inv, hid]
  calc |w d * Q (N / d)| = |w d| * |Q (N / d)| := abs_mul _ _
    _ ≤ (1 / (d : ℝ)) * (C * ((N / d : ℕ) : ℝ) ^ (1 / 2 + ε)) := by
        refine mul_le_mul (hw d hd1) hQd (abs_nonneg _) (by positivity)
    _ ≤ (1 / (d : ℝ)) * (C * ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hC) (by positivity)
    _ = C * (N : ℝ) ^ (1 / 2 + ε) * ((1 / (d : ℝ)) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹) := by
        rw [hsplit]
        ring
    _ = C * (N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (-(3 / 2 + ε)) := by rw [hpow]

/-- The critical majorant is absolutely convergent. -/
theorem summable_criticalMajorant {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (fun d : ℕ => (d : ℝ) ^ (-(3 / 2 + ε))) := by
  have hstep : Summable (fun d : ℕ => ((d : ℝ) ^ (3 / 2 + ε))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by linarith)
  refine hstep.congr fun d => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg d)]

theorem abs_floorTransform_le_tsum_majorant {w Q : ℕ → ℝ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hw : ∀ d : ℕ, 1 ≤ d → |w d| ≤ 1 / d)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform w Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) := by
  have hsum := summable_criticalMajorant hε
  have hle : ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(3 / 2 + ε))
      ≤ ∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 + ε)) :=
    Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsum
  have hbase := abs_floorTransform_le_of_weight hC hε hw hQ hN
  have hNrpow : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hstep := mul_le_mul_of_nonneg_left hle (mul_nonneg hC hNrpow)
  refine hbase.trans (hstep.trans (le_of_eq ?_))
  ring

/-- **(24.14) The harmonic floor average obeys the critical bound of its profile.** -/
theorem abs_floorTransform_harmonic_le {Q : ℕ → ℝ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform harmonicWeight Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) :=
  abs_floorTransform_le_tsum_majorant hC hε (fun _ hd => abs_harmonicWeight_le hd) hQ hN

/-- **(24.14) The Möbius-harmonic inversion obeys the critical bound of its average.** -/
theorem abs_floorTransform_moebiusHarmonic_le {Q : ℕ → ℝ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform moebiusHarmonicWeight Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) :=
  abs_floorTransform_le_tsum_majorant hC hε (fun _ hd => abs_moebiusHarmonicWeight_le hd) hQ hN

end

end RHTower
