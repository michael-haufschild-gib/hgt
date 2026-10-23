import Mathlib

/-!
# The prime atoms against the two-pole density, in the lag variable

The prime side of the critical form reads a weight at the lags `log n` with the atoms `Λ(n)`, and
its polar counterpart reads the same weight against the density `e^s + 1 = 2 e^{s/2} cosh(s/2)`,
the sum of the densities of the two poles of the completed zeta function at `s = 1` and `s = 0`.
This file proves that the two cancel to the accuracy of the prime number theorem, exactly: for
every `C¹` weight `h` vanishing from a point on,

    Σ_n Λ(n) h(log n) − ∫_{s>0} (e^s + 1) h(s) ds = ∫_{s>0} E(s) h'(s) ds,

with the **two-pole Chebyshev defect** `E(s) = e^s + s − 1 − ψ(e^s)`
(`sum_vonMangoldt_sub_polar_eq_chebyshev`).

Two mechanisms.  *Lag Abel summation* (`sum_vonMangoldt_mul_eq_neg_integral`) writes the atom sum
as `−∫_{s>0} ψ(e^s) h'(s) ds`; it is a finite Fubini rather than a limit, since each term is
`−Λ(n) ∫_{s ≥ log n} h'` and the atoms at lags below `s` sum to `ψ(e^s)` exactly.  *The two-pole
comparison weight* `w(s) = e^s + s − 1`, the primitive of `e^s + 1` vanishing at the origin,
returns the polar density undifferentiated under integration by parts
(`integral_twoPoleWeight_mul_deriv`).  Subtracting leaves `E` as the only arithmetic residue.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

open FourierTransform Complex in
/-- Chebyshev's function read in the lag variable: `ψ(e^s) = Σ_{n ≤ e^s} Λ(n)`. -/
def lagChebyshev (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)

/-- The two-pole comparison weight `w(s) = e^s + s − 1`: the primitive, vanishing at the origin, of
the polar density `e^s + 1 = 2 e^{s/2} cosh(s/2)` of the Weil form in the lag variable. -/
def twoPoleWeight (s : ℝ) : ℝ := Real.exp s + s - 1

/-- The **two-pole Chebyshev defect** `E(s) = e^s + s − 1 − ψ(e^s)`: the excess of the prediction
of the two poles over the actual prime count, in the lag variable. -/
def chebyshevTwoPoleDefect (s : ℝ) : ℝ := twoPoleWeight s - lagChebyshev s

theorem twoPoleWeight_eq : twoPoleWeight = fun s => Real.exp s + s - 1 := rfl

theorem twoPoleWeight_zero : twoPoleWeight 0 = 0 := by simp [twoPoleWeight]

theorem hasDerivAt_twoPoleWeight (s : ℝ) : HasDerivAt twoPoleWeight (Real.exp s + 1) s := by
  rw [twoPoleWeight_eq]
  simpa using ((Real.hasDerivAt_exp s).add (hasDerivAt_id s)).sub_const 1

theorem continuous_twoPoleWeight : Continuous twoPoleWeight := by
  rw [twoPoleWeight_eq]; fun_prop

theorem measurable_lagChebyshev : Measurable lagChebyshev := by
  have : lagChebyshev = (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      (ArithmeticFunction.vonMangoldt k : ℝ)) ∘ (fun s : ℝ => ⌊Real.exp s⌋₊) := rfl
  rw [this]
  exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)

/-! ### The weight class: `C¹`, vanishing from `S` on -/

variable {h : ℝ → ℝ} {S : ℝ}

/-- Past the vanishing point the derivative vanishes too. -/
theorem deriv_eq_zero_of_vanishing (hvan : ∀ s, S ≤ s → h s = 0) {s : ℝ} (hs : S < s) :
    deriv h s = 0 := by
  have he : h =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_gt_nhds hs] with y hy using hvan y hy.le
  rw [he.deriv_eq, deriv_const]

/-- `deriv h` is integrable on `(0, ∞)`: continuous, and supported in `(0, S]`. -/
theorem integrableOn_Ioi_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) : IntegrableOn (deriv h) (Ioi (0:ℝ)) := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn (deriv h) (Ioc (0:ℝ) S) :=
    (hdc.integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (deriv h) (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => (deriv_eq_zero_of_vanishing hvan hx).symm) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  exact h1.union h2

/-- The tail integral of the derivative recovers the value: `∫_{s ≥ a} h' = −h a` for `a > 0`. -/
theorem integral_Ici_deriv (hh : ContDiff ℝ 1 h)
    (hvan : ∀ s, S ≤ s → h s = 0) (a : ℝ) :
    (∫ s in Ici a, deriv h s) = -h a := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  set M := max a S with hM
  have haM : a ≤ M := le_max_left _ _
  have hSM : S ≤ M := le_max_right _ _
  have hdisj : Disjoint (Icc a M) (Ioi M) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn (deriv h) (Icc a M) := hdc.integrableOn_Icc
  have h2 : IntegrableOn (deriv h) (Ioi M) :=
    (integrableOn_zero (μ := volume) (s := Ioi M)).congr_fun
      (fun x hx => (deriv_eq_zero_of_vanishing hvan (lt_of_le_of_lt hSM hx)).symm)
      measurableSet_Ioi
  have hzero : (∫ s in Ioi M, deriv h s) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => deriv_eq_zero_of_vanishing hvan (lt_of_le_of_lt hSM hx))]
    simp
  have hsub : (∫ s in Icc a M, deriv h s) = -h a := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haM,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hh.differentiable one_ne_zero x) (hdc.intervalIntegrable _ _),
      hvan M hSM, zero_sub]
  rw [← Set.Icc_union_Ioi_eq_Ici haM, setIntegral_union hdisj measurableSet_Ioi h1 h2, hzero,
    add_zero, hsub]

/-- The single-atom integral: the step at `a` against `h'` returns `−h a`. -/
theorem integral_Ioi_step_mul_deriv (hh : ContDiff ℝ 1 h)
    (hvan : ∀ s, S ≤ s → h s = 0) {a : ℝ} (ha : 0 < a) :
    (∫ s in Ioi (0:ℝ), (if a ≤ s then (1:ℝ) else 0) * deriv h s) = -h a := by
  have hind : ∀ s : ℝ, (if a ≤ s then (1:ℝ) else 0) * deriv h s
      = (Ici a).indicator (deriv h) s := by
    intro s
    by_cases hs : a ≤ s <;> simp [hs]
  have hinter : Ioi (0:ℝ) ∩ Ici a = Ici a :=
    Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le ha hx
  simp_rw [hind]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici, hinter]
  exact integral_Ici_deriv hh hvan a

/-- Integrability of a single step term on `(0, ∞)`. -/
theorem integrableOn_Ioi_step_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (c a : ℝ) :
    IntegrableOn (fun s => c * ((if a ≤ s then (1:ℝ) else 0) * deriv h s)) (Ioi (0:ℝ)) := by
  have hbase := (integrableOn_Ioi_deriv hh hS hvan).norm.const_mul |c|
  have hmeas : AEStronglyMeasurable
      (fun s => c * ((if a ≤ s then (1:ℝ) else 0) * deriv h s)) (volume.restrict (Ioi 0)) := by
    have : Measurable fun s : ℝ => if a ≤ s then (1:ℝ) else 0 :=
      measurable_const.ite measurableSet_Ici measurable_const
    exact (measurable_const.mul (this.mul (hh.continuous_deriv le_rfl).measurable)).aestronglyMeasurable
  refine hbase.mono' hmeas (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : a ≤ s
  · rw [if_pos hs, one_mul]
    simp [Real.norm_eq_abs]
  · rw [if_neg hs, zero_mul, mul_zero, norm_zero]
    positivity


/-! ### Lag Abel summation for an arbitrary arithmetic source

Nothing in the summation is special to the von Mangoldt weight: every arithmetic weight vanishing
at `0` and `1` has a lag prefix and a two-pole defect of its own, and the balance holds verbatim.
What distinguishes a source is therefore *not* the identity but the size of its own defect — the
comparison density `e^s + 1` is matched by a source exactly when its prefix is `e^s + s − 1`.
This is the audit instrument for the test models: the shifted pair, a Beurling system and the
Liouville twist all satisfy the same identity, with their own prefixes. -/

/-- The prefix of an arithmetic weight in the lag variable: `A(e^s) = Σ_{n ≤ e^s} a(n)`. -/
def lagPrefix (a : ℕ → ℝ) (s : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊, a k

/-- The two-pole defect of a source: the two-pole prediction minus the source's own prefix. -/
def lagSourceDefect (a : ℕ → ℝ) (s : ℝ) : ℝ := twoPoleWeight s - lagPrefix a s

theorem lagChebyshev_eq_lagPrefix :
    lagChebyshev = lagPrefix fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := rfl

theorem chebyshevTwoPoleDefect_eq_lagSourceDefect :
    chebyshevTwoPoleDefect = lagSourceDefect fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  rfl

/-- The atoms at lags `≤ s` sum to the prefix: an exact finite identity, no limit. -/
theorem lagPrefix_eq_sum_step (a : ℕ → ℝ) {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    lagPrefix a s
      = ∑ n ∈ Finset.range (N + 1), a n * (if Real.log n ≤ s then (1:ℝ) else 0) := by
  have hexp : (0:ℝ) ≤ Real.exp s := (Real.exp_pos s).le
  have hfl : ⌊Real.exp s⌋₊ ≤ N := by simpa using Nat.floor_mono hN
  have hsub : Finset.Icc 0 ⌊Real.exp s⌋₊ ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.2.trans hfl))
  have hout : ∀ k ∈ Finset.range (N + 1), k ∉ Finset.Icc 0 ⌊Real.exp s⌋₊ →
      a k * (if Real.log k ≤ s then (1:ℝ) else 0) = 0 := by
    intro k _ hk
    have hgt : ⌊Real.exp s⌋₊ < k := by
      rcases Nat.lt_or_ge ⌊Real.exp s⌋₊ k with hlt | hge
      · exact hlt
      · exact absurd (Finset.mem_Icc.mpr ⟨Nat.zero_le k, hge⟩) hk
    have hks : Real.exp s < (k : ℝ) := (Nat.floor_lt hexp).mp hgt
    have hns : ¬ Real.log k ≤ s := by
      have hlt : Real.log (Real.exp s) < Real.log k := Real.log_lt_log (Real.exp_pos s) hks
      rw [Real.log_exp] at hlt
      exact not_le.mpr hlt
    rw [if_neg hns, mul_zero]
  have hin : ∀ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
      a k = a k * (if Real.log k ≤ s then (1:ℝ) else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkle : (k : ℝ) ≤ Real.exp s := (Nat.le_floor_iff hexp).mp hk.2
    have hls : Real.log k ≤ s := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · simpa [h0] using hs
      · have hk0 : (0:ℝ) < k := by exact_mod_cast h0
        have hle := Real.log_le_log hk0 hkle
        rwa [Real.log_exp] at hle
    rw [if_pos hls, mul_one]
  rw [lagPrefix, ← Finset.sum_subset hsub hout]
  exact Finset.sum_congr rfl hin

theorem lagPrefix_mul_deriv_eq_sum (a : ℕ → ℝ)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) {s : ℝ} (hs : 0 < s) :
    lagPrefix a s * deriv h s
      = ∑ n ∈ Finset.range (N + 1), a n *
          ((if Real.log n ≤ s then (1:ℝ) else 0) * deriv h s) := by
  by_cases hsS : s ≤ S
  · rw [lagPrefix_eq_sum_step a hs.le ((Real.exp_le_exp.mpr hsS).trans hN), Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  · rw [deriv_eq_zero_of_vanishing hvan (not_le.mp hsS)]
    simp

theorem integrableOn_Ioi_lagPrefix_mul_deriv (a : ℕ → ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => lagPrefix a s * deriv h s) (Ioi (0:ℝ)) := by
  have hsum : IntegrableOn (fun s => ∑ n ∈ Finset.range (N + 1),
      a n * ((if Real.log n ≤ s then (1:ℝ) else 0) * deriv h s)) (Ioi (0:ℝ)) :=
    integrable_finsetSum _ fun n _ =>
      integrableOn_Ioi_step_mul_deriv hh hS hvan (a n) (Real.log n)
  exact hsum.congr_fun (fun s hs => (lagPrefix_mul_deriv_eq_sum a hvan hN hs).symm)
    measurableSet_Ioi

/-- **Lag Abel summation.** For a `C¹` weight vanishing from `S` on, the sum of an arithmetic
weight at the lags `log n` is an integral of its prefix against `−h'`.  Finite Fubini: each atom
contributes `−a(n) ∫_{s ≥ log n} h'`, and the atoms below `s` sum to the prefix exactly. -/
theorem sum_weight_mul_eq_neg_integral (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    ∑ n ∈ Finset.range (N + 1), a n * h (Real.log n)
      = -∫ s in Ioi (0:ℝ), lagPrefix a s * deriv h s := by
  have hint : (∫ s in Ioi (0:ℝ), lagPrefix a s * deriv h s)
      = ∑ n ∈ Finset.range (N + 1), ∫ s in Ioi (0:ℝ),
          a n * ((if Real.log n ≤ s then (1:ℝ) else 0) * deriv h s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => lagPrefix_mul_deriv_eq_sum a hvan hN hs)]
    exact integral_finsetSum _ fun n _ =>
      integrableOn_Ioi_step_mul_deriv hh hS hvan (a n) (Real.log n)
  rw [hint, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h1 : n ≤ 1
  · have hz : a n = 0 := by interval_cases n <;> simp [ha0, ha1]
    rw [hz]; simp
  · have h1' : 1 < n := not_le.mp h1
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast h1')
    rw [MeasureTheory.integral_const_mul, integral_Ioi_step_mul_deriv hh hvan hlog]
    ring

/-! ### The von Mangoldt instance -/

theorem lagChebyshev_eq_sum_step {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    lagChebyshev s
      = ∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (if Real.log n ≤ s then (1:ℝ) else 0) :=
  lagPrefix_eq_sum_step _ hs hN

theorem lagChebyshev_mul_deriv_eq_sum
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) {s : ℝ} (hs : 0 < s) :
    lagChebyshev s * deriv h s
      = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((if Real.log n ≤ s then (1:ℝ) else 0) * deriv h s) :=
  lagPrefix_mul_deriv_eq_sum _ hvan hN hs

theorem integrableOn_Ioi_lagChebyshev_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => lagChebyshev s * deriv h s) (Ioi (0:ℝ)) :=
  integrableOn_Ioi_lagPrefix_mul_deriv _ hh hS hvan hN

theorem sum_vonMangoldt_mul_eq_neg_integral (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n)
      = -∫ s in Ioi (0:ℝ), lagChebyshev s * deriv h s :=
  sum_weight_mul_eq_neg_integral _ (by simp) (by simp) hh hS hvan hN

/-! ### The two-pole comparison weight -/

/-- A continuous function vanishing past `S` integrates over `(0, ∞)` as an interval integral. -/
theorem integral_Ioi_eq_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f) (hS : 0 < S)
    (hv : ∀ s, S < s → f s = 0) : ∫ s in Ioi (0:ℝ), f s = ∫ s in (0:ℝ)..S, f s := by
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn f (Ioc (0:ℝ) S) :=
    (hf.integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn f (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => (hv x hx).symm) measurableSet_Ioi
  have hval2 : (∫ s in Ioi S, f s) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hv x hx)]; simp
  rw [intervalIntegral.integral_of_le hS.le, ← Set.Ioc_union_Ioi_eq_Ioi hS.le,
    setIntegral_union hdisj measurableSet_Ioi h1 h2, hval2, add_zero]

/-- **The two-pole weight returns the polar density.** Integration by parts against
`w(s) = e^s + s − 1`, whose derivative is the polar density `e^s + 1 = 2 e^{s/2} cosh(s/2)` and
which vanishes at the origin, carries `h'` back to `h`. -/
theorem integral_twoPoleWeight_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), twoPoleWeight s * deriv h s)
      = -∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hhc : Continuous h := hh.continuous
  have hA : (∫ s in Ioi (0:ℝ), twoPoleWeight s * deriv h s)
      = ∫ s in (0:ℝ)..S, twoPoleWeight s * deriv h s :=
    integral_Ioi_eq_intervalIntegral (continuous_twoPoleWeight.mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s)
      = ∫ s in (0:ℝ)..S, (Real.exp s + 1) * h s :=
    integral_Ioi_eq_intervalIntegral (by fun_prop) hS
      (fun s hs => by rw [hvan s hs.le, mul_zero])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := twoPoleWeight) (u' := fun s => Real.exp s + 1) (v := h) (v' := deriv h)
    (a := 0) (b := S)
    (fun x _ => hasDerivAt_twoPoleWeight x)
    (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    ((by fun_prop : Continuous fun s : ℝ => Real.exp s + 1).intervalIntegrable _ _)
    (hdc.intervalIntegrable _ _)
  rw [hA, hB, hparts, hvan S le_rfl, twoPoleWeight_zero]
  ring

/-- **The atoms of a source against the two-pole density.** For every `C¹` weight vanishing from
`S` on, the sum of an arithmetic weight at the lags `log n` and the integral of the polar density
against the weight differ by exactly the source's own two-pole defect tested against `h'`.  The
identity is universal; what is specific to a source is the size of its defect. -/
theorem sum_weight_sub_polar_eq_defect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hwi : IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioc (0:ℝ) S) :=
      (((continuous_twoPoleWeight.mul hdc).integrableOn_Icc (a := 0) (b := S))).mono_set
        Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hpi := integrableOn_Ioi_lagPrefix_mul_deriv a hh hS hvan hN
  have hsplit : (∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv h s)
      = (∫ s in Ioi (0:ℝ), twoPoleWeight s * deriv h s)
        - ∫ s in Ioi (0:ℝ), lagPrefix a s * deriv h s := by
    rw [← MeasureTheory.integral_sub hwi hpi]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
      simp [lagSourceDefect, sub_mul]
  rw [hsplit, integral_twoPoleWeight_mul_deriv hh hS hvan,
    sum_weight_mul_eq_neg_integral a ha0 ha1 hh hS hvan hN]
  ring

/-- **The prime atoms against the two-pole density.** The von Mangoldt instance: the prime side
and the pole plane cancel to the accuracy of the prime number theorem, with the two-pole
Chebyshev defect as the entire residue. -/
theorem sum_vonMangoldt_sub_polar_eq_chebyshev (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s :=
  sum_weight_sub_polar_eq_defect _ (by simp) (by simp) hh hS hvan hN



/-! ### The lag weight of a translate of a compact test

Every compactly supported `C¹` test `F` and every point `x` produce a lag weight
`h_x(s) = 2 e^{−s/2} F(x+s)`: the weight through which the prime atoms and the polar density act
on the translate of `F` by `x`.  Instantiating the balance at `h_x` gives the prime–polar
cancellation seen by one translate. -/

/-- The lag weight of the translate of `F` by `x`: `h_x(s) = 2 e^{−s/2} F(x+s)`. -/
def shiftLagWeight (F : ℝ → ℝ) (x s : ℝ) : ℝ := 2 * Real.exp (-s / 2) * F (x + s)

/-- Its derivative `h_x'(s) = 2 e^{−s/2} (F'(x+s) − ½ F(x+s))`. -/
def shiftLagWeightDeriv (F : ℝ → ℝ) (x s : ℝ) : ℝ :=
  2 * Real.exp (-s / 2) * (deriv F (x + s) - F (x + s) / 2)

variable {F : ℝ → ℝ}

theorem hasDerivAt_shiftLagWeight (hF : ContDiff ℝ 1 F) (x s : ℝ) :
    HasDerivAt (shiftLagWeight F x) (shiftLagWeightDeriv F x s) s := by
  have he : HasDerivAt (fun s : ℝ => 2 * Real.exp (-s / 2)) (2 * (Real.exp (-s / 2) * (-1 / 2))) s := by
    have := (((hasDerivAt_id s).neg.div_const 2).exp).const_mul (2 : ℝ)
    simpa using this
  have hf : HasDerivAt (fun s : ℝ => F (x + s)) (deriv F (x + s)) s :=
    HasDerivAt.comp_const_add x s ((hF.differentiable one_ne_zero (x + s)).hasDerivAt)
  have := he.mul hf
  refine this.congr_deriv ?_
  unfold shiftLagWeightDeriv
  ring

theorem contDiff_shiftLagWeight (hF : ContDiff ℝ 1 F) (x : ℝ) :
    ContDiff ℝ 1 (shiftLagWeight F x) := by
  unfold shiftLagWeight
  exact (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul
    (hF.comp (contDiff_const.add contDiff_id))

theorem deriv_shiftLagWeight (hF : ContDiff ℝ 1 F) (x s : ℝ) :
    deriv (shiftLagWeight F x) s = shiftLagWeightDeriv F x s :=
  (hasDerivAt_shiftLagWeight hF x s).deriv

/-- Past `2r + |x|` the translate leaves the support of `F`. -/
theorem shiftLagWeight_eq_zero {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (x : ℝ)
    {s : ℝ} (hs : 2 * r + |x| ≤ s) : shiftLagWeight F x s = 0 := by
  have hxs : r < x + s := by
    have : -|x| ≤ x := neg_abs_le x
    linarith
  rw [shiftLagWeight, hsupp (x + s) (by rwa [abs_of_pos (lt_trans hr hxs)]), mul_zero]

/-- `e^{−(log n)/2} = 1/√n`. -/
theorem exp_neg_half_log (hx : (0:ℝ) < x) : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg]
  ring_nf

/-- `(e^s + 1) · 2 e^{−s/2} = 4 cosh(s/2)`: the polar density in its hyperbolic form. -/
theorem polarDensity_mul_half_weight (s : ℝ) :
    (Real.exp s + 1) * (2 * Real.exp (-s / 2)) = 4 * Real.cosh (s / 2) := by
  rw [Real.cosh_eq]
  have h1 : Real.exp s * Real.exp (-s / 2) = Real.exp (s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(s / 2)) = Real.exp (-s / 2) := by ring_nf
  field_simp [← h2]
  nlinarith [h1, Real.exp_pos (s / 2), Real.exp_pos (-s / 2)]

/-- **The prime atoms against the two-pole density, on one translate of a compact test.**
For a `C¹` test supported in `[−r, r]`, every point `x` and every horizon `N ≥ e^{2r+|x|}`, the
prime atoms read at the lags `log n` and the polar density `4 cosh(s/2)` read against the same
translate differ by exactly the two-pole Chebyshev defect tested against the lag weight's
derivative.  The leading PNT terms of the two arithmetic channels cancel identically; `E` is the
whole residue. -/
theorem primeShift_sub_polarDensity_eq_chebyshev (hF : ContDiff ℝ 1 F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (x : ℝ) {N : ℕ} (hN : Real.exp (2 * r + |x|) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * F (x + Real.log n)))
        - ∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * F (x + s)
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * shiftLagWeightDeriv F x s := by
  have hS : 0 < 2 * r + |x| := by have := abs_nonneg x; linarith
  have hvan : ∀ s, 2 * r + |x| ≤ s → shiftLagWeight F x s = 0 :=
    fun s hs => shiftLagWeight_eq_zero hr hsupp x hs
  have hkey := sum_vonMangoldt_sub_polar_eq_chebyshev (contDiff_shiftLagWeight hF x) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_shiftLagWeight hF x s] :
        ∀ s ∈ Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv (shiftLagWeight F x) s
          = chebyshevTwoPoleDefect s * shiftLagWeightDeriv F x s)] at hkey
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [shiftLagWeight, exp_neg_half_log hn]
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [shiftLagWeight, ← mul_assoc, polarDensity_mul_half_weight, mul_assoc]


/-! ### The strip masses of the ledger

The global allocation charges each prime atom beyond the light cone to the mass of its own strip,
`m_n(F) = ∫_{log n − r}^{r} F²`, and what pays those masses is the open end of the allocation.  The
strip masses are the values at the lags `log n` of the `C¹` weight `m(s) = ∫_{s−r}^{r} F²`, so the
balance applies verbatim: the polar density pays the whole strip-mass cost, and the residue is the
two-pole Chebyshev defect. -/

/-- The strip mass at lag `s`: `m(s) = ∫_{s−r}^{r} F²`, the mass of the test on the strip the shift
`e^s` charges. -/
def stripMass (F : ℝ → ℝ) (r s : ℝ) : ℝ := ∫ y in (s - r)..r, F y ^ 2

theorem hasDerivAt_stripMass (hF : Continuous F) (r s : ℝ) :
    HasDerivAt (stripMass F r) (-(F (s - r)) ^ 2) s := by
  have hsq : Continuous fun y : ℝ => F y ^ 2 := hF.pow 2
  have hleft : HasDerivAt (fun u : ℝ => ∫ y in u..r, F y ^ 2) (-(F (s - r)) ^ 2) (s - r) := by
    have := intervalIntegral.integral_hasDerivAt_left
      (hsq.intervalIntegrable (s - r) r)
      (hsq.stronglyMeasurableAtFilter _ _) hsq.continuousAt
    simpa using this
  exact HasDerivAt.comp_sub_const s r hleft

theorem deriv_stripMass (hF : Continuous F) (r : ℝ) :
    deriv (stripMass F r) = fun s => -(F (s - r)) ^ 2 :=
  funext fun s => (hasDerivAt_stripMass hF r s).deriv

theorem contDiff_one_stripMass (hF : Continuous F) (r : ℝ) :
    ContDiff ℝ 1 (stripMass F r) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_stripMass hF r s).differentiableAt, ?_⟩
  rw [deriv_stripMass hF r]
  exact (hF.comp (continuous_id.sub continuous_const)).pow 2 |>.neg

/-- A continuous test vanishing outside `[−r, r]` vanishes at the endpoint. -/
theorem eq_zero_at_radius (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) : F r = 0 := by
  have h1 : Filter.Tendsto F (nhdsWithin r (Ioi r)) (nhds (F r)) :=
    (hF.continuousAt).continuousWithinAt
  have h2 : Filter.Tendsto F (nhdsWithin r (Ioi r)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hsupp y (by rwa [abs_of_pos (lt_trans hr hy)])).symm
  exact tendsto_nhds_unique h1 h2

/-- Past twice the aperture the strip is outside the support. -/
theorem stripMass_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {s : ℝ} (hs : 2 * r ≤ s) : stripMass F r s = 0 := by
  have hrs : r ≤ s - r := by linarith
  have hzero : ∀ y ∈ Set.uIcc (s - r) r, F y ^ 2 = 0 := by
    intro y hy
    rw [Set.uIcc_of_ge hrs] at hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, eq_zero_at_radius hF hr hsupp]; ring
    · rw [hsupp y (by rwa [abs_of_pos (lt_trans hr h)])]; ring
  rw [stripMass, intervalIntegral.integral_congr hzero]
  simp

/-- **The polar density pays the strip masses, to PNT accuracy.** For a continuous test supported
in `[−r, r]` the ledger's strip-mass cost `Σ_n 2Λ(n) n^{−1/2} m_n(F)` equals the polar integral of
the strip-mass profile plus the two-pole Chebyshev defect against its lag weight.  The first term
is explicit and arithmetic-free; the whole arithmetic content of the strip-mass side of the global
allocation is the second. -/
theorem stripMass_cost_eq_polar_add_chebyshev (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * stripMass F r (Real.log n)))
      = (∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * stripMass F r s)
        + ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
            (2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2)) := by
  set h : ℝ → ℝ := fun s => 2 * Real.exp (-s / 2) * stripMass F r s with hdef
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → h s = 0 := fun s hs => by
    rw [hdef]; simp [stripMass_eq_zero hF hr hsupp hs]
  have hcd : ContDiff ℝ 1 h :=
    (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul (contDiff_one_stripMass hF r)
  have hderiv : ∀ s, deriv h s
      = 2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2) := by
    intro s
    have he : HasDerivAt (fun s : ℝ => 2 * Real.exp (-s / 2))
        (2 * (Real.exp (-s / 2) * (-1 / 2))) s := by
      have := (((hasDerivAt_id s).neg.div_const 2).exp).const_mul (2 : ℝ)
      simpa using this
    have hprod := he.mul (hasDerivAt_stripMass hF r s)
    have hfun : h = (fun s : ℝ => 2 * Real.exp (-s / 2)) * stripMass F r := rfl
    rw [hfun]
    exact (hprod.congr_deriv (by ring : 2 * (Real.exp (-s / 2) * (-1 / 2)) * stripMass F r s
        + 2 * Real.exp (-s / 2) * -(F (s - r)) ^ 2
        = 2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2))).deriv
  have hkey := sum_vonMangoldt_sub_polar_eq_chebyshev hcd hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [hderiv s] :
        ∀ s ∈ Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s
          = chebyshevTwoPoleDefect s *
              (2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2)))] at hkey
  have hpolar : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s)
      = ∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * stripMass F r s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hdef]
    rw [← mul_assoc, polarDensity_mul_half_weight, mul_assoc]
  have hatoms : (∑ n ∈ Finset.range (N + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
      = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * stripMass F r (Real.log n)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      simp only [hdef]
      rw [exp_neg_half_log hn]
  rw [hatoms, hpolar] at hkey
  linarith [hkey]


/-! ### The balance is a two-way dictionary

In one direction the balance bounds the prime–polar imbalance of any weight by the Chebyshev
defect tested against `|h'|`.  In the other it is not vacuous: the tail weights of continuous
bumps realise every mollified value of the defect, so the imbalances of a test family determine
`E` itself. -/

/-- **The imbalance is bounded by the Chebyshev defect.** -/
theorem abs_sum_vonMangoldt_sub_polar_le (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s|
      ≤ ∫ s in Ioi (0:ℝ), |chebyshevTwoPoleDefect s * deriv h s| := by
  rw [sum_vonMangoldt_sub_polar_eq_chebyshev hh hS hvan hN]
  exact abs_integral_le_integral_abs

variable {φ : ℝ → ℝ}

/-- The tail weight of a bump: `h_φ(s) = ∫_s^S φ`, the `C¹` weight whose derivative is `−φ`. -/
def tailWeight (φ : ℝ → ℝ) (S s : ℝ) : ℝ := ∫ t in s..S, φ t

theorem hasDerivAt_tailWeight (hφ : Continuous φ) (S s : ℝ) :
    HasDerivAt (tailWeight φ S) (-φ s) s := by
  have h : HasDerivAt (fun u : ℝ => ∫ t in u..S, φ t) (-φ s) s := by
    simpa using intervalIntegral.integral_hasDerivAt_left
      (hφ.intervalIntegrable s S) (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  exact h

theorem contDiff_one_tailWeight (hφ : Continuous φ) (S : ℝ) :
    ContDiff ℝ 1 (tailWeight φ S) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_tailWeight hφ S s).differentiableAt, ?_⟩
  have : deriv (tailWeight φ S) = fun s => -φ s :=
    funext fun s => (hasDerivAt_tailWeight hφ S s).deriv
  rw [this]
  exact hφ.neg

theorem tailWeight_eq_zero (hφ0 : ∀ t, S ≤ t → φ t = 0) {s : ℝ} (hs : S ≤ s) :
    tailWeight φ S s = 0 := by
  have hzero : ∀ t ∈ Set.uIcc s S, φ t = 0 := by
    intro t ht
    rw [Set.uIcc_of_ge hs] at ht
    exact hφ0 t ht.1
  rw [tailWeight, intervalIntegral.integral_congr hzero]
  simp

/-- **The imbalance realises the mollified Chebyshev defect.** Tested on the tail weight of a
continuous bump supported below `S`, the prime–polar imbalance is exactly `−∫ E φ`: the balance
determines the defect against every test bump, so it is an identity with content in both
directions, not a one-sided estimate. -/
theorem sum_vonMangoldt_sub_polar_tailWeight (hφ : Continuous φ) (hS : 0 < S)
    (hφ0 : ∀ t, S ≤ t → φ t = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * tailWeight φ S (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * tailWeight φ S s
      = -∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * φ s := by
  have hkey := sum_vonMangoldt_sub_polar_eq_chebyshev (contDiff_one_tailWeight hφ S) hS
    (fun s hs => tailWeight_eq_zero hφ0 hs) hN
  rw [hkey, setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [(hasDerivAt_tailWeight hφ S s).deriv]; ring :
        ∀ s ∈ Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv (tailWeight φ S) s
          = -(chebyshevTwoPoleDefect s * φ s)),
    MeasureTheory.integral_neg]



/-! ### The horizon of an aperture, and the quiet zone below the first prime -/

theorem integrableOn_Ioi_twoPoleWeight_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioi (0:ℝ)) := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioc (0:ℝ) S) :=
    (((continuous_twoPoleWeight.mul hdc).integrableOn_Icc (a := 0) (b := S))).mono_set
      Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun s => twoPoleWeight s * deriv h s) (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  exact h1.union h2

theorem integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => chebyshevTwoPoleDefect s * deriv h s) (Ioi (0:ℝ)) := by
  refine ((integrableOn_Ioi_twoPoleWeight_mul_deriv hh hS hvan).sub
    (integrableOn_Ioi_lagChebyshev_mul_deriv hh hS hvan hN)).congr_fun
    (fun s _ => ?_) measurableSet_Ioi
  simp [chebyshevTwoPoleDefect, sub_mul]

/-- **The horizon law.** A weight vanishing from `S` on reads the Chebyshev defect only on
`(0, S]`: a test of aperture `r`, whose lag weight dies at `2r`, sees the defect at scales up to
`e^{2r}` and nothing beyond. -/
theorem integral_chebyshev_mul_deriv_eq_Ioc (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s)
      = ∫ s in Ioc (0:ℝ) S, chebyshevTwoPoleDefect s * deriv h s := by
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have hfull := integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hh hS hvan hN
  have hsub : Ioc (0:ℝ) S ⊆ Ioi (0:ℝ) := fun x hx => hx.1
  have h1 : IntegrableOn (fun s => chebyshevTwoPoleDefect s * deriv h s) (Ioc (0:ℝ) S) :=
    hfull.mono_set hsub
  have hzero : ∀ x ∈ Ioi S, chebyshevTwoPoleDefect x * deriv h x = 0 :=
    fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]
  have h2 : IntegrableOn (fun s => chebyshevTwoPoleDefect s * deriv h s) (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => (hzero x hx).symm) measurableSet_Ioi
  have hval2 : (∫ s in Ioi S, chebyshevTwoPoleDefect s * deriv h s) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hzero]; simp
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le, setIntegral_union hdisj measurableSet_Ioi h1 h2, hval2,
    add_zero]

theorem lagChebyshev_mono : Monotone lagChebyshev := by
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  exact Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.exp_le_exp.mpr hab))

theorem lagChebyshev_nonneg (s : ℝ) : 0 ≤ lagChebyshev s :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- **The quiet zone of the lag variable.** Below the first prime the Chebyshev count is empty, so
the defect is exactly the two-pole weight: the balance there is a statement about the two poles
alone and carries no arithmetic.  The arithmetic of the balance begins exactly at `s = log 2`. -/
theorem chebyshevTwoPoleDefect_eq_twoPoleWeight_of_lt_log_two {s : ℝ} (hs : s < Real.log 2) :
    chebyshevTwoPoleDefect s = twoPoleWeight s := by
  have hlt : Real.exp s < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 1 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  have hz : lagChebyshev s = 0 := by
    rw [lagChebyshev]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : k ≤ 1 := hk.2.trans hfl
    interval_cases k <;> simp
  rw [chebyshevTwoPoleDefect, hz, sub_zero]


/-! ### The bridge to the critical-scale receiver

The two-pole defect splits as `E(s) = (e^s − ψ(e^s)) + (s − 1)`, and the second piece integrates
against `h'` to elementary data.  What is left is the Chebyshev error `e^s − ψ(e^s)` itself — the
integrand of the critical-scale cancellation functional `D(T) = ∫_0^T (e^t − ψ(e^t)) dt`, whose
one-sided bound `D(T) ≤ B(1+T)e^{T/2}` at a single constant for every scale is equivalent to the
Riemann Hypothesis.  So the prime–polar imbalance of the incidence face and the critical-scale
receiver are one functional, read through `h'`. -/

/-- The Chebyshev error in the lag variable: `e^s − ψ(e^s)`. -/
def chebyshevError (s : ℝ) : ℝ := Real.exp s - lagChebyshev s

theorem chebyshevTwoPoleDefect_eq_error_add (s : ℝ) :
    chebyshevTwoPoleDefect s = chebyshevError s + (s - 1) := by
  rw [chebyshevTwoPoleDefect, chebyshevError, twoPoleWeight]; ring

/-- The elementary half: `∫_{s>0} (s − 1) h'(s) ds = h(0) − ∫_{s>0} h`. -/
theorem integral_linear_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), (s - 1) * deriv h s) = h 0 - ∫ s in Ioi (0:ℝ), h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hA : (∫ s in Ioi (0:ℝ), (s - 1) * deriv h s) = ∫ s in (0:ℝ)..S, (s - 1) * deriv h s :=
    integral_Ioi_eq_intervalIntegral ((continuous_id.sub continuous_const).mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), h s) = ∫ s in (0:ℝ)..S, h s :=
    integral_Ioi_eq_intervalIntegral hh.continuous hS (fun s hs => hvan s hs.le)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s - 1) (u' := fun _ : ℝ => (1:ℝ)) (v := h) (v' := deriv h) (a := 0) (b := S)
    (fun x _ => (hasDerivAt_id x).sub_const 1)
    (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    (continuous_const.intervalIntegrable _ _) (hdc.intervalIntegrable _ _)
  rw [hA, hB, hparts, hvan S le_rfl]
  simp

theorem integrableOn_Ioi_chebyshevError_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => chebyshevError s * deriv h s) (Ioi (0:ℝ)) := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hexp : IntegrableOn (fun s => Real.exp s * deriv h s) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => Real.exp s * deriv h s) (Ioc (0:ℝ) S) :=
      (((Real.continuous_exp.mul hdc).integrableOn_Icc (a := 0) (b := S))).mono_set
        Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => Real.exp s * deriv h s) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  refine (hexp.sub (integrableOn_Ioi_lagChebyshev_mul_deriv hh hS hvan hN)).congr_fun
    (fun s _ => ?_) measurableSet_Ioi
  simp [chebyshevError, sub_mul]

theorem integrableOn_Ioi_linear_mul_deriv (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    IntegrableOn (fun s => (s - 1) * deriv h s) (Ioi (0:ℝ)) := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn (fun s => (s - 1) * deriv h s) (Ioc (0:ℝ) S) :=
    ((((continuous_id.sub continuous_const).mul hdc).integrableOn_Icc (a := 0) (b := S))).mono_set
      Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun s => (s - 1) * deriv h s) (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  exact h1.union h2

/-- **The receiver bridge.** The prime–polar imbalance of any `C¹` lag weight is the Chebyshev
error `e^s − ψ(e^s)` tested against `h'`, plus two elementary terms.  The error is the integrand of
the critical-scale cancellation functional of the Riemann tower, so the incidence face's imbalance
and that receiver are the same arithmetic datum. -/
theorem sum_vonMangoldt_sub_polar_eq_chebyshevError (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = (∫ s in Ioi (0:ℝ), chebyshevError s * deriv h s) + h 0 - ∫ s in Ioi (0:ℝ), h s := by
  have hsplit : (∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s)
      = (∫ s in Ioi (0:ℝ), chebyshevError s * deriv h s)
        + ∫ s in Ioi (0:ℝ), (s - 1) * deriv h s := by
    rw [← MeasureTheory.integral_add (integrableOn_Ioi_chebyshevError_mul_deriv hh hS hvan hN)
      (integrableOn_Ioi_linear_mul_deriv hh hS hvan)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [chebyshevTwoPoleDefect_eq_error_add]
    ring
  rw [sum_vonMangoldt_sub_polar_eq_chebyshev hh hS hvan hN, hsplit,
    integral_linear_mul_deriv hh hS hvan]
  ring


/-! ### Second-order lag Abel summation

Summing by parts twice moves the weight's two derivatives onto a *ramp* sum: the atom at `log n`
is read through `(s − log n)_+`.  The ramp sum is the primitive `∫_0^s ψ(e^u) du` of Chebyshev's
function, so against the matching polar primitive the balance pairs `h''` with the primitive of
the Chebyshev error — the critical-scale cancellation functional itself. -/

/-- A continuous function vanishing past `S` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_of_vanishing {f : ℝ → ℝ} (hf : Continuous f) (hS : 0 < S)
    (hv : ∀ s, S < s → f s = 0) : IntegrableOn f (Ioi (0:ℝ)) := by
  have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have h1 : IntegrableOn f (Ioc (0:ℝ) S) :=
    (hf.integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn f (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun x hx => (hv x hx).symm) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
  exact h1.union h2

/-- Past the vanishing point of `h` the second derivative vanishes. -/
theorem deriv_deriv_eq_zero_of_vanishing (hvan : ∀ s, S ≤ s → h s = 0) {s : ℝ} (hs : S < s) :
    deriv (deriv h) s = 0 := by
  have he : deriv h =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact deriv_eq_zero_of_vanishing hvan hy
  rw [he.deriv_eq, deriv_const]

/-- **The single ramp integral.** For `a > 0`, `∫_{s>0} (s − a)_+ h''(s) ds = h a`. -/
theorem integral_Ioi_ramp_mul_deriv2 (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h))
    (hvan : ∀ s, S ≤ s → h s = 0) {a : ℝ} (ha : 0 < a) :
    (∫ s in Ioi (0:ℝ), max (s - a) 0 * deriv (deriv h) s) = h a := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  set M := max a S + 1 with hM
  have haM : a ≤ M := le_trans (le_max_left a S) (by linarith)
  have hSM : S < M := lt_of_le_of_lt (le_max_right a S) (by linarith)
  have hind : ∀ s : ℝ, max (s - a) 0 * deriv (deriv h) s
      = (Ici a).indicator (fun s => (s - a) * deriv (deriv h) s) s := by
    intro s
    simp only [Set.indicator_apply, Set.mem_Ici]
    by_cases hs : a ≤ s
    · rw [if_pos hs, max_eq_left (by linarith)]
    · rw [if_neg hs, max_eq_right (by linarith [not_le.mp hs]), zero_mul]
  have hinter : Ioi (0:ℝ) ∩ Ici a = Ici a :=
    Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le ha hx
  have hdisj : Disjoint (Icc a M) (Ioi M) := by
    rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
  have hzeroM : ∀ x ∈ Ioi M, (x - a) * deriv (deriv h) x = 0 :=
    fun x hx => by rw [deriv_deriv_eq_zero_of_vanishing hvan (lt_trans hSM hx), mul_zero]
  have h1 : IntegrableOn (fun s => (s - a) * deriv (deriv h) s) (Icc a M) :=
    ((continuous_id.sub continuous_const).mul hd2).integrableOn_Icc
  have h2 : IntegrableOn (fun s => (s - a) * deriv (deriv h) s) (Ioi M) :=
    (integrableOn_zero (μ := volume) (s := Ioi M)).congr_fun
      (fun x hx => (hzeroM x hx).symm) measurableSet_Ioi
  have hval2 : (∫ s in Ioi M, (s - a) * deriv (deriv h) s) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hzeroM]; simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s - a) (u' := fun _ : ℝ => (1:ℝ)) (v := deriv h) (v' := deriv (deriv h))
    (a := a) (b := M)
    (fun x _ => (hasDerivAt_id x).sub_const a)
    (fun x _ => (hh'.differentiable one_ne_zero x).hasDerivAt)
    (continuous_const.intervalIntegrable _ _) (hd2.intervalIntegrable _ _)
  have hderivM : deriv h M = 0 := deriv_eq_zero_of_vanishing hvan hSM
  have hftc : (∫ s in a..M, deriv h s) = -h a := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hh.differentiable one_ne_zero x)
      ((hh.continuous_deriv le_rfl).intervalIntegrable _ _), hvan M (le_of_lt hSM), zero_sub]
  simp_rw [hind]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici, hinter,
    ← Set.Icc_union_Ioi_eq_Ici haM, setIntegral_union hdisj measurableSet_Ioi h1 h2, hval2,
    add_zero, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le haM, hparts, hderivM]
  simp only [one_mul]
  rw [hftc]
  ring

/-- The ramp sum of the atoms below the horizon: `Σ_n Λ(n) (s − log n)_+`. -/
def rampSum (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * max (s - Real.log n) 0

/-- **Second-order lag Abel summation.** Two summations by parts read every atom through its ramp:
`Σ_n Λ(n) h(log n) = ∫_{s>0} (Σ_n Λ(n)(s − log n)_+) h''(s) ds`. -/
theorem sum_vonMangoldt_mul_eq_integral_rampSum (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n)
      = ∫ s in Ioi (0:ℝ), rampSum N s * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hterm : ∀ n : ℕ, IntegrableOn (fun s => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (max (s - Real.log n) 0 * deriv (deriv h) s)) (Ioi (0:ℝ)) := fun n =>
    integrableOn_Ioi_of_vanishing
      (continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).mul hd2))
      hS (fun x hx => by rw [deriv_deriv_eq_zero_of_vanishing hvan hx]; ring)
  have hpt : ∀ s : ℝ, rampSum N s * deriv (deriv h) s
      = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (max (s - Real.log n) 0 * deriv (deriv h) s) := by
    intro s
    rw [rampSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpt s),
    integral_finsetSum _ fun n _ => hterm n]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h1 : n ≤ 1
  · have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by interval_cases n <;> simp
    rw [hz]; simp
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast not_le.mp h1)
    rw [MeasureTheory.integral_const_mul, integral_Ioi_ramp_mul_deriv2 hh hh' hvan hlog]


/-- The polar ramp: the primitive of the two-pole weight vanishing at the origin,
`e^s + s²/2 − s − 1`. -/
def polarRamp (s : ℝ) : ℝ := Real.exp s + s ^ 2 / 2 - s - 1

theorem polarRamp_zero : polarRamp 0 = 0 := by simp [polarRamp]

theorem polarRamp_eq : polarRamp = fun s => Real.exp s + s ^ 2 / 2 - s - 1 := rfl

theorem hasDerivAt_polarRamp (s : ℝ) : HasDerivAt polarRamp (twoPoleWeight s) s := by
  rw [polarRamp_eq]
  have h := (((Real.hasDerivAt_exp s).add
    (((hasDerivAt_pow 2 s).div_const 2))).sub (hasDerivAt_id s)).sub_const 1
  refine h.congr_deriv ?_
  rw [twoPoleWeight]
  norm_num

theorem continuous_polarRamp : Continuous polarRamp := by
  rw [polarRamp_eq]; fun_prop

/-- The polar side in second-order form. -/
theorem integral_polarRamp_mul_deriv2 (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h))
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), polarRamp s * deriv (deriv h) s)
      = ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  set T := S + 1 with hT
  have hST : S < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA : (∫ s in Ioi (0:ℝ), polarRamp s * deriv (deriv h) s)
      = ∫ s in (0:ℝ)..T, polarRamp s * deriv (deriv h) s :=
    integral_Ioi_eq_intervalIntegral (continuous_polarRamp.mul hd2) hT0
      (fun s hs => by
        rw [deriv_deriv_eq_zero_of_vanishing hvan (lt_trans hST hs), mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), twoPoleWeight s * deriv h s)
      = ∫ s in (0:ℝ)..T, twoPoleWeight s * deriv h s :=
    integral_Ioi_eq_intervalIntegral (continuous_twoPoleWeight.mul hdc) hT0
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan (lt_trans hST hs), mul_zero])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := polarRamp) (u' := twoPoleWeight) (v := deriv h) (v' := deriv (deriv h))
    (a := 0) (b := T)
    (fun x _ => hasDerivAt_polarRamp x)
    (fun x _ => (hh'.differentiable one_ne_zero x).hasDerivAt)
    (continuous_twoPoleWeight.intervalIntegrable _ _) (hd2.intervalIntegrable _ _)
  have hderivT : deriv h T = 0 := deriv_eq_zero_of_vanishing hvan hST
  rw [hA, hparts, hderivT, polarRamp_zero, ← hB, integral_twoPoleWeight_mul_deriv hh hS hvan]
  ring

/-- **The second-order balance.** Against the second derivative of the weight, the prime–polar
imbalance is the ramp defect `polarRamp − rampSum`: the primitive of the polar density minus the
primitive of Chebyshev's function.  Up to the elementary `s²/2 − s`, that defect is the
critical-scale cancellation functional `∫_0^s (e^u − ψ(e^u)) du`. -/
theorem sum_vonMangoldt_sub_polar_eq_rampDefect (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), (rampSum N s - polarRamp s) * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hvan2 : ∀ s, S < s → deriv (deriv h) s = 0 :=
    fun s hs => deriv_deriv_eq_zero_of_vanishing hvan hs
  have hcr : Continuous (rampSum N) := by
    unfold rampSum
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hi1 : IntegrableOn (fun s => rampSum N s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hcr.mul hd2) hS (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hi2 : IntegrableOn (fun s => polarRamp s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_polarRamp.mul hd2) hS
      (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (rampSum N s - polarRamp s) * deriv (deriv h) s)
      = (∫ s in Ioi (0:ℝ), rampSum N s * deriv (deriv h) s)
        - ∫ s in Ioi (0:ℝ), polarRamp s * deriv (deriv h) s := by
    rw [← MeasureTheory.integral_sub hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  rw [hsplit, ← sum_vonMangoldt_mul_eq_integral_rampSum hh hh' hS hvan N,
    integral_polarRamp_mul_deriv2 hh hh' hS hvan]


/-! ### The ramp sum is the primitive of Chebyshev's function -/

/-- A step at `a > 0` integrates to the ramp `(s − a)_+`. -/
theorem integral_step_eq_ramp {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ u in (0:ℝ)..s, (if a ≤ u then (1:ℝ) else 0)) = max (s - a) 0 := by
  have hind : (fun u : ℝ => if a ≤ u then (1:ℝ) else 0)
      = (Ici a).indicator (fun _ => (1:ℝ)) := by
    funext u; simp only [Set.indicator_apply, Set.mem_Ici]
  have hset : Ioc (0:ℝ) s ∩ Ici a = Icc a s := by
    ext u
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le ha h1, h2⟩, h1⟩
  rw [intervalIntegral.integral_of_le hs, hind,
    MeasureTheory.setIntegral_indicator measurableSet_Ici, hset,
    MeasureTheory.setIntegral_const]
  simp [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']

theorem monotone_step (a : ℝ) : Monotone fun u : ℝ => if a ≤ u then (1:ℝ) else 0 := by
  intro x y hxy
  dsimp only
  by_cases hx : a ≤ x
  · rw [if_pos hx, if_pos (hx.trans hxy)]
  · rw [if_neg hx]; split_ifs <;> norm_num

/-- **The ramp sum is the primitive of Chebyshev's function:**
`Σ_n Λ(n)(s − log n)_+ = ∫_0^s ψ(e^u) du`. -/
theorem rampSum_eq_integral_lagChebyshev {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    rampSum N s = ∫ u in (0:ℝ)..s, lagChebyshev u := by
  have hcong : ∀ u ∈ Set.uIcc (0:ℝ) s, lagChebyshev u
      = ∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (if Real.log n ≤ u then (1:ℝ) else 0) := by
    intro u hu
    rw [Set.uIcc_of_le hs] at hu
    exact lagChebyshev_eq_sum_step hu.1 ((Real.exp_le_exp.mpr hu.2).trans hN)
  have hsum := intervalIntegral.integral_finsetSum (μ := volume) (a := (0:ℝ)) (b := s)
    (s := Finset.range (N + 1))
    (f := fun (n : ℕ) (u : ℝ) =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (if Real.log n ≤ u then (1:ℝ) else 0))
    (fun n _ => ((monotone_step (Real.log n)).intervalIntegrable).const_mul _)
  rw [intervalIntegral.integral_congr hcong, hsum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  by_cases h1 : n ≤ 1
  · have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by interval_cases n <;> simp
    rw [hz, zero_mul, zero_mul]
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast not_le.mp h1)
    rw [integral_step_eq_ramp hlog hs]

/-- The critical-scale cancellation functional `D(s) = ∫_0^s (e^u − ψ(e^u)) du`, whose one-sided
bound `D(T) ≤ B(1+T)e^{T/2}` at one constant for every scale is equivalent to the Riemann
Hypothesis. -/
def criticalScalePrefix (s : ℝ) : ℝ := ∫ u in (0:ℝ)..s, (Real.exp u - lagChebyshev u)

/-- **The ramp defect is the critical-scale functional.** `polarRamp − rampSum = D + s²/2 − s`. -/
theorem polarRamp_sub_rampSum {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    polarRamp s - rampSum N s = criticalScalePrefix s + s ^ 2 / 2 - s := by
  have hint1 : IntervalIntegrable Real.exp volume 0 s :=
    Real.continuous_exp.intervalIntegrable _ _
  have hint2 : IntervalIntegrable lagChebyshev volume 0 s :=
    lagChebyshev_mono.intervalIntegrable
  have hexp : (∫ u in (0:ℝ)..s, Real.exp u) = Real.exp s - 1 := by
    simp [integral_exp]
  rw [criticalScalePrefix, intervalIntegral.integral_sub hint1 hint2, hexp,
    ← rampSum_eq_integral_lagChebyshev hs hN, polarRamp]
  ring

/-- **The receiver-primitive form of the balance.** For a weight whose horizon `S` lies below
`log N`, the prime–polar imbalance pairs the second derivative of the weight against the
critical-scale functional itself:

    Σ_n Λ(n)h(log n) − ∫_{s>0}(e^s+1)h = −∫_{s>0} (D(s) + s²/2 − s) h''(s) ds .

The incidence face's imbalance and the critical-scale receiver of the Riemann tower are one
functional. -/
theorem sum_vonMangoldt_sub_polar_eq_criticalScalePrefix (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0)
    {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = -∫ s in Ioi (0:ℝ), (criticalScalePrefix s + s ^ 2 / 2 - s) * deriv (deriv h) s := by
  have hvan2 : ∀ s, S < s → deriv (deriv h) s = 0 :=
    fun s hs => deriv_deriv_eq_zero_of_vanishing hvan hs
  rw [sum_vonMangoldt_sub_polar_eq_rampDefect hh hh' hS hvan N, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hsmem => ?_
  by_cases hsS : s ≤ S
  · have hs0 : (0:ℝ) ≤ s := le_of_lt hsmem
    rw [← polarRamp_sub_rampSum hs0 ((Real.exp_le_exp.mpr hsS).trans hN)]
    ring
  · rw [hvan2 s (not_le.mp hsS)]
    ring


/-! ### The ledger computes the receiver

The double tail of a bump is a weight whose second derivative is that bump, so the imbalances of
the double-tail family realise every mollified value of `D(s) + s²/2 − s`.  The receiver is not
merely implied by the incidence ledger: the ledger measures it against arbitrary test bumps. -/

theorem continuous_tailWeight (hφ : Continuous φ) (S : ℝ) : Continuous (tailWeight φ S) :=
  (contDiff_one_tailWeight hφ S).continuous

/-- The double tail of a bump: `H(s) = ∫_s^S ∫_t^S φ`, the weight with `H'' = φ`. -/
def tailTailWeight (φ : ℝ → ℝ) (S s : ℝ) : ℝ := ∫ t in s..S, tailWeight φ S t

theorem hasDerivAt_tailTailWeight (hφ : Continuous φ) (S s : ℝ) :
    HasDerivAt (tailTailWeight φ S) (-(tailWeight φ S s)) s := by
  have h : HasDerivAt (fun u : ℝ => ∫ t in u..S, tailWeight φ S t) (-(tailWeight φ S s)) s := by
    simpa using intervalIntegral.integral_hasDerivAt_left
      ((continuous_tailWeight hφ S).intervalIntegrable s S)
      ((continuous_tailWeight hφ S).stronglyMeasurableAtFilter _ _)
      (continuous_tailWeight hφ S).continuousAt
  exact h

theorem deriv_tailTailWeight (hφ : Continuous φ) (S : ℝ) :
    deriv (tailTailWeight φ S) = fun s => -(tailWeight φ S s) :=
  funext fun s => (hasDerivAt_tailTailWeight hφ S s).deriv

theorem contDiff_one_tailTailWeight (hφ : Continuous φ) (S : ℝ) :
    ContDiff ℝ 1 (tailTailWeight φ S) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_tailTailWeight hφ S s).differentiableAt, ?_⟩
  rw [deriv_tailTailWeight hφ S]
  exact (continuous_tailWeight hφ S).neg

theorem contDiff_one_deriv_tailTailWeight (hφ : Continuous φ) (S : ℝ) :
    ContDiff ℝ 1 (deriv (tailTailWeight φ S)) := by
  rw [deriv_tailTailWeight hφ S]
  exact (contDiff_one_tailWeight hφ S).neg

theorem deriv_deriv_tailTailWeight (hφ : Continuous φ) (S s : ℝ) :
    deriv (deriv (tailTailWeight φ S)) s = φ s := by
  have hn : HasDerivAt (fun u : ℝ => -(tailWeight φ S u)) (-(-φ s)) s :=
    (hasDerivAt_tailWeight hφ S s).neg
  rw [deriv_tailTailWeight hφ S, hn.deriv, neg_neg]

theorem tailTailWeight_eq_zero (hφ0 : ∀ t, S ≤ t → φ t = 0) {s : ℝ} (hs : S ≤ s) :
    tailTailWeight φ S s = 0 := by
  have hzero : ∀ t ∈ Set.uIcc s S, tailWeight φ S t = 0 := by
    intro t ht
    rw [Set.uIcc_of_ge hs] at ht
    exact tailWeight_eq_zero hφ0 ht.1
  rw [tailTailWeight, intervalIntegral.integral_congr hzero]
  simp

/-- **The ledger measures the critical-scale functional.** On the double tail of a continuous bump
supported below `S`, the prime–polar imbalance is exactly `−∫ (D + s²/2 − s) φ`: every mollified
value of the receiver is an imbalance of the incidence ledger. -/
theorem sum_vonMangoldt_sub_polar_tailTailWeight (hφ : Continuous φ) (hS : 0 < S)
    (hφ0 : ∀ t, S ≤ t → φ t = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * tailTailWeight φ S (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * tailTailWeight φ S s
      = -∫ s in Ioi (0:ℝ), (criticalScalePrefix s + s ^ 2 / 2 - s) * φ s := by
  have hkey := sum_vonMangoldt_sub_polar_eq_criticalScalePrefix
    (contDiff_one_tailTailWeight hφ S) (contDiff_one_deriv_tailTailWeight hφ S) hS
    (fun s hs => tailTailWeight_eq_zero hφ0 hs) hN
  rw [hkey]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
    rw [deriv_deriv_tailTailWeight hφ S s]


/-! ### The strip-mass weight is sign-definite

The strip mass decreases in the lag, so its lag weight has a nonpositive derivative.  Against a
weight of one sign the balance becomes an inequality: the polar density overpays the strip masses
except where the Chebyshev count exceeds the two-pole prediction, that is except where
`ψ(x) > x + log x − 1`.  This localises the open end of the global allocation to a one-sided
Chebyshev bound. -/

/-- The lag weight of the strip masses: `2 e^{−s/2} m(s)`. -/
def lagStripWeight (F : ℝ → ℝ) (r s : ℝ) : ℝ := 2 * Real.exp (-s / 2) * stripMass F r s

theorem contDiff_one_lagStripWeight (hF : Continuous F) (r : ℝ) :
    ContDiff ℝ 1 (lagStripWeight F r) :=
  (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul (contDiff_one_stripMass hF r)

theorem deriv_lagStripWeight (hF : Continuous F) (r s : ℝ) :
    deriv (lagStripWeight F r) s
      = 2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2) := by
  have he : HasDerivAt (fun s : ℝ => 2 * Real.exp (-s / 2))
      (2 * (Real.exp (-s / 2) * (-1 / 2))) s := by
    have := (((hasDerivAt_id s).neg.div_const 2).exp).const_mul (2 : ℝ)
    simpa using this
  have hprod := he.mul (hasDerivAt_stripMass hF r s)
  have hfun : lagStripWeight F r = (fun s : ℝ => 2 * Real.exp (-s / 2)) * stripMass F r := rfl
  rw [hfun]
  exact (hprod.congr_deriv (by ring : 2 * (Real.exp (-s / 2) * (-1 / 2)) * stripMass F r s
      + 2 * Real.exp (-s / 2) * -(F (s - r)) ^ 2
      = 2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2))).deriv

theorem stripMass_nonneg (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (s : ℝ) : 0 ≤ stripMass F r s := by
  by_cases hs : s ≤ 2 * r
  · exact intervalIntegral.integral_nonneg (by linarith) fun u _ => sq_nonneg _
  · rw [stripMass_eq_zero hF hr hsupp (le_of_lt (not_le.mp hs))]

theorem lagStripWeight_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {s : ℝ} (hs : 2 * r ≤ s) : lagStripWeight F r s = 0 := by
  rw [lagStripWeight, stripMass_eq_zero hF hr hsupp hs, mul_zero]

/-- **The strip-mass lag weight decreases.** -/
theorem deriv_lagStripWeight_nonpos (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (s : ℝ) : deriv (lagStripWeight F r) s ≤ 0 := by
  rw [deriv_lagStripWeight hF r s]
  have h1 : (0:ℝ) ≤ (F (s - r)) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ stripMass F r s := stripMass_nonneg hF hr hsupp s
  have h3 : (0:ℝ) < Real.exp (-s / 2) := Real.exp_pos _
  nlinarith

theorem measurable_chebyshevTwoPoleDefect : Measurable chebyshevTwoPoleDefect :=
  continuous_twoPoleWeight.measurable.sub measurable_lagChebyshev

/-- The negative part of the defect is at most the Chebyshev count. -/
theorem negPart_chebyshevTwoPoleDefect_le {s : ℝ} (hs : 0 ≤ s) :
    max (-chebyshevTwoPoleDefect s) 0 ≤ lagChebyshev s := by
  have hexp : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
  refine max_le ?_ (lagChebyshev_nonneg s)
  rw [chebyshevTwoPoleDefect, twoPoleWeight]
  linarith

/-- **The polar density overpays the strip masses off the excess set.** Unconditionally, the
prime–polar imbalance of the strip-mass weight is at most the negative part of the two-pole
Chebyshev defect weighted by the weight's own decrease.  So the pole fails to pay a strip mass
only at scales where `ψ(x) > x + log x − 1`. -/
theorem balance_lagStripWeight_le (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * lagStripWeight F r (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * lagStripWeight F r s
      ≤ ∫ s in Ioi (0:ℝ),
          max (-chebyshevTwoPoleDefect s) 0 * (-deriv (lagStripWeight F r) s) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagStripWeight F r s = 0 :=
    fun s hs => lagStripWeight_eq_zero hF hr hsupp hs
  have hcd := contDiff_one_lagStripWeight hF r
  have hdc : Continuous (deriv (lagStripWeight F r)) := hcd.continuous_deriv le_rfl
  have hi1 := integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hcd hS hvan hN
  have hnegc : Continuous fun s => -deriv (lagStripWeight F r) s := hdc.neg
  have hnegvan : ∀ s, 2 * r < s → -deriv (lagStripWeight F r) s = 0 :=
    fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, neg_zero]
  have hbase : IntegrableOn (fun s => lagChebyshev (2 * r) * -deriv (lagStripWeight F r) s)
      (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_const.mul hnegc) hS
      (fun s hs => by rw [hnegvan s hs, mul_zero])
  have hmeas : AEStronglyMeasurable
      (fun s => max (-chebyshevTwoPoleDefect s) 0 * -deriv (lagStripWeight F r) s)
      (volume.restrict (Ioi (0:ℝ))) :=
    (((measurable_chebyshevTwoPoleDefect.neg).max measurable_const).mul
      hnegc.measurable).aestronglyMeasurable
  have hi2 : IntegrableOn (fun s =>
      max (-chebyshevTwoPoleDefect s) 0 * -deriv (lagStripWeight F r) s) (Ioi (0:ℝ)) := by
    refine hbase.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs0mem
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs0mem
    rcases le_or_gt s (2 * r) with hs | hs
    · have hnn : 0 ≤ -deriv (lagStripWeight F r) s := by
        have := deriv_lagStripWeight_nonpos hF hr hsupp s; linarith
      have hb : max (-chebyshevTwoPoleDefect s) 0 ≤ lagChebyshev (2 * r) :=
        le_trans (negPart_chebyshevTwoPoleDefect_le hs0) (lagChebyshev_mono hs)
      have hmax : (0:ℝ) ≤ max (-chebyshevTwoPoleDefect s) 0 := le_max_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmax hnn)]
      exact mul_le_mul_of_nonneg_right hb hnn
    · rw [hnegvan s hs]
      simp
  refine le_trans (le_of_eq (sum_vonMangoldt_sub_polar_eq_chebyshev hcd hS hvan hN)) ?_
  refine MeasureTheory.integral_mono hi1 hi2 fun s => ?_
  have hle : -chebyshevTwoPoleDefect s ≤ max (-chebyshevTwoPoleDefect s) 0 := le_max_left _ _
  have hnn : 0 ≤ -deriv (lagStripWeight F r) s := by
    have := deriv_lagStripWeight_nonpos hF hr hsupp s; linarith
  have heq : chebyshevTwoPoleDefect s * deriv (lagStripWeight F r) s
      = (-chebyshevTwoPoleDefect s) * (-deriv (lagStripWeight F r) s) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hle hnn


/-! ### The test-level balance

For a compactly supported `C¹` test the autocorrelation `A(t) = ∫ F(x)F(x+t) dx` is itself `C¹`,
with derivative the cross-correlation against `F'`.  Its half-weighted form `2 e^{−s/2} A(s)` is
therefore a lag weight, and the balance becomes a statement about the test: the prime side of the
critical form and the polar density paired with the autocorrelation differ by exactly the two-pole
Chebyshev defect against the test's lag weight. -/

/-- The autocorrelation `A(t) = ∫ F(x) F(x+t) dx`. -/
def autoCorrelation (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * F (x + t)

/-- The cross-correlation against the derivative, `∫ F(x) F'(x+t) dx`. -/
def crossCorrelation (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * deriv F (x + t)

variable {F : ℝ → ℝ}

theorem integrable_bound (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (M : ℝ) :
    Integrable (fun x => ‖F x‖ * M) :=
  (hF.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport hFc.norm.mul_right

/-- The autocorrelation is differentiable, with the cross-correlation as derivative. -/
theorem hasDerivAt_autoCorrelation (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (t : ℝ) :
    HasDerivAt (autoCorrelation F) (crossCorrelation F t) t := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous hdcont
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => F x * F (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => F x * deriv F (x + u))
    (x₀ := t) (bound := fun x => ‖F x‖ * M) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u =>
      (hFcont.mul (hFcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hFcont.mul (hFcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hFc.mul_right))
    ((hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _))
    (integrable_bound hF hFc M)
    (Filter.Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u ((hF.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul
        (F x))
  exact key.2

theorem continuous_crossCorrelation (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Continuous (crossCorrelation F) := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous hdcont
  refine continuous_of_dominated (bound := fun x => ‖F x‖ * M)
    (fun u => (hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (fun u => Filter.Eventually.of_forall fun x => ?_) (integrable_bound hF hFc M)
    (Filter.Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)
  · exact continuous_const.mul (hdcont.comp (continuous_const.add continuous_id))

theorem deriv_autoCorrelation (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    deriv (autoCorrelation F) = crossCorrelation F :=
  funext fun t => (hasDerivAt_autoCorrelation hF hFc t).deriv

theorem contDiff_one_autoCorrelation (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ContDiff ℝ 1 (autoCorrelation F) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_autoCorrelation hF hFc t).differentiableAt, ?_⟩
  rw [deriv_autoCorrelation hF hFc]
  exact continuous_crossCorrelation hF hFc

/-- Past twice the aperture the test and its translate have disjoint supports. -/
theorem autoCorrelation_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {t : ℝ} (ht : 2 * r ≤ t) : autoCorrelation F t = 0 := by
  have hz : ∀ x : ℝ, F x * F (x + t) = 0 := by
    intro x
    by_cases hx : r < |x|
    · rw [hsupp x hx, zero_mul]
    · have hxr : -r ≤ x := by
        have := abs_le.mp (not_lt.mp hx); linarith [this.1]
      have hge : r ≤ x + t := by linarith
      rcases eq_or_lt_of_le hge with h | h
      · rw [← h, eq_zero_at_radius hF hr hsupp, mul_zero]
      · rw [hsupp (x + t) (by rwa [abs_of_pos (lt_trans hr h)]), mul_zero]
  rw [autoCorrelation]
  simp [hz]

/-- The lag weight of a test: `2 e^{−s/2} A(s)`. -/
def lagTestWeight (F : ℝ → ℝ) (s : ℝ) : ℝ := 2 * Real.exp (-s / 2) * autoCorrelation F s

theorem contDiff_one_lagTestWeight (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ContDiff ℝ 1 (lagTestWeight F) :=
  (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul (contDiff_one_autoCorrelation hF hFc)

theorem deriv_lagTestWeight (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (s : ℝ) :
    deriv (lagTestWeight F) s
      = 2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2) := by
  have he : HasDerivAt (fun s : ℝ => 2 * Real.exp (-s / 2))
      (2 * (Real.exp (-s / 2) * (-1 / 2))) s := by
    have := (((hasDerivAt_id s).neg.div_const 2).exp).const_mul (2 : ℝ)
    simpa using this
  have hprod := he.mul (hasDerivAt_autoCorrelation hF hFc s)
  have hfun : lagTestWeight F = (fun s : ℝ => 2 * Real.exp (-s / 2)) * autoCorrelation F := rfl
  rw [hfun]
  exact (hprod.congr_deriv (by ring :
    2 * (Real.exp (-s / 2) * (-1 / 2)) * autoCorrelation F s
      + 2 * Real.exp (-s / 2) * crossCorrelation F s
      = 2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))).deriv

/-- **The test-level prime–polar balance.** For a compactly supported `C¹` test of aperture `r`
and any horizon `N ≥ e^{2r}`, the prime side read at the lags `log n` and the polar density paired
with the autocorrelation differ by exactly the two-pole Chebyshev defect against the test's lag
weight.  The two leading arithmetic channels of the critical form cancel identically; the whole
residue is `E`. -/
theorem testBalance (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - ∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_vonMangoldt_sub_polar_eq_chebyshev (contDiff_one_lagTestWeight hF hFc) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeight hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv (lagTestWeight F) s
          = chebyshevTwoPoleDefect s *
              (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)))] at hkey
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lagTestWeight, exp_neg_half_log hn]
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [lagTestWeight, ← mul_assoc, polarDensity_mul_half_weight, mul_assoc]


/-! ### The sharp aperture law past the aperture

Beyond the aperture the overlap of a test with its translate and the overlap of the translate with
the test occupy *disjoint* halves of the support, so the correlation is at most half the mass.  The
constant `½` is attained, by a test made of two copies of one bump at the spacing of the lag: the
per-lag reading of the prime side is closed at `½` and no estimate using one lag at a time can do
better. -/

/-- Splitting a test at the origin. -/
def leftPart (F : ℝ → ℝ) (x : ℝ) : ℝ := if x < 0 then F x else 0

/-- Splitting a test at the origin. -/
def rightPart (F : ℝ → ℝ) (x : ℝ) : ℝ := if 0 ≤ x then F x else 0

theorem leftPart_sq_add_rightPart_sq (F : ℝ → ℝ) (x : ℝ) :
    leftPart F x ^ 2 + rightPart F x ^ 2 = F x ^ 2 := by
  rw [leftPart, rightPart]
  by_cases h : x < 0
  · rw [if_pos h, if_neg (not_le.mpr h)]; ring
  · rw [if_neg h, if_pos (not_lt.mp h)]; ring

theorem measurable_leftPart (hF : Continuous F) : Measurable (leftPart F) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) hF.measurable measurable_const

theorem measurable_rightPart (hF : Continuous F) : Measurable (rightPart F) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) hF.measurable measurable_const

/-- Past the aperture the product factors through the two halves: the overlap lies entirely to the
left of the origin and its translate entirely to the right. -/
theorem mul_shift_eq_leftPart_mul_rightPart {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t) (x : ℝ) :
    F x * F (x + t) = leftPart F x * rightPart F (x + t) := by
  by_cases hz : F x * F (x + t) = 0
  · rw [hz]
    rcases mul_eq_zero.mp hz with h | h
    · rw [leftPart, h]; split_ifs <;> ring
    · rw [rightPart, h]; split_ifs <;> ring
  · have h1 : F x ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : F (x + t) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hx : |x| ≤ r := not_lt.mp fun h => h1 (hsupp x h)
    have hxt : |x + t| ≤ r := not_lt.mp fun h => h2 (hsupp (x + t) h)
    have hxneg : x < 0 := by
      have := (abs_le.mp hxt).2; linarith
    have hxtpos : 0 ≤ x + t := by
      have := (abs_le.mp hx).1; linarith
    rw [leftPart, rightPart, if_pos hxneg, if_pos hxtpos]

/-- **The half law.** For a continuous test supported in `[−r, r]` and every lag beyond the
aperture, the autocorrelation is at most half the mass. -/
theorem autoCorrelation_le_half (hF : Continuous F) (hFc : HasCompactSupport F) {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t) :
    autoCorrelation F t ≤ autoCorrelation F 0 / 2 := by
  have hsqeq : (fun x => F x ^ 2) = fun x => F x * F x := by funext x; ring
  have hsqF : Integrable fun x => F x ^ 2 := by
    rw [hsqeq]
    exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hbl : ∀ x, leftPart F x ^ 2 ≤ F x ^ 2 := fun x => by
    have := leftPart_sq_add_rightPart_sq F x; nlinarith [sq_nonneg (rightPart F x)]
  have hbr : ∀ x, rightPart F x ^ 2 ≤ F x ^ 2 := fun x => by
    have := leftPart_sq_add_rightPart_sq F x; nlinarith [sq_nonneg (leftPart F x)]
  have hil : Integrable fun x => leftPart F x ^ 2 := by
    refine hsqF.mono' ((measurable_leftPart hF).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbl x
  have hir : Integrable fun x => rightPart F x ^ 2 := by
    refine hsqF.mono' ((measurable_rightPart hF).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbr x
  have hirt : Integrable fun x => rightPart F (x + t) ^ 2 := by
    have := hir.comp_add_right t
    simpa using this
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hpt : ∀ x, 2 * (F x * F (x + t)) ≤ leftPart F x ^ 2 + rightPart F (x + t) ^ 2 := by
    intro x
    rw [mul_shift_eq_leftPart_mul_rightPart hsupp ht x]
    nlinarith [sq_nonneg (leftPart F x - rightPart F (x + t))]
  have hiadd : Integrable fun x => leftPart F x ^ 2 + rightPart F (x + t) ^ 2 := hil.add hirt
  have hmono := MeasureTheory.integral_mono (hprod.const_mul 2) hiadd (fun x => hpt x)
  rw [MeasureTheory.integral_const_mul] at hmono
  have htrans : (∫ x, rightPart F (x + t) ^ 2) = ∫ x, rightPart F x ^ 2 := by
    simpa using MeasureTheory.integral_add_right_eq_self (fun x => rightPart F x ^ 2) t
  have hsum : (∫ x, leftPart F x ^ 2) + ∫ x, rightPart F x ^ 2 = ∫ x, F x ^ 2 := by
    rw [← MeasureTheory.integral_add hil hir]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => leftPart_sq_add_rightPart_sq F x)
  have hA0 : autoCorrelation F 0 = ∫ x, F x ^ 2 := by
    rw [autoCorrelation]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + 0) = F x ^ 2
    rw [add_zero, sq]
  have hRHS : (∫ x, (leftPart F x ^ 2 + rightPart F (x + t) ^ 2)) = ∫ x, F x ^ 2 := by
    rw [MeasureTheory.integral_add hil hirt, htrans, hsum]
  rw [hRHS] at hmono
  rw [autoCorrelation, hA0]
  linarith


/-- Two copies of a bump of width `L`, separated by more than `L`, never overlap. -/
theorem mul_shift_eq_zero_of_bump {g : ℝ → ℝ} {L : ℝ}
    (hgsupp : ∀ y, y < 0 ∨ L < y → g y = 0) {d : ℝ} (hd : L < |d|) (y : ℝ) :
    g y * g (y + d) = 0 := by
  by_cases h1 : g y = 0
  · rw [h1, zero_mul]
  by_cases h2 : g (y + d) = 0
  · rw [h2, mul_zero]
  have hy : 0 ≤ y ∧ y ≤ L := by
    constructor
    · exact not_lt.mp fun h => h1 (hgsupp y (Or.inl h))
    · exact not_lt.mp fun h => h1 (hgsupp y (Or.inr h))
  have hyd : 0 ≤ y + d ∧ y + d ≤ L := by
    constructor
    · exact not_lt.mp fun h => h2 (hgsupp (y + d) (Or.inl h))
    · exact not_lt.mp fun h => h2 (hgsupp (y + d) (Or.inr h))
  exact absurd hd (not_lt.mpr (abs_le.mpr ⟨by linarith [hy.2, hyd.1], by linarith [hy.1, hyd.2]⟩))

/-- **The half law is attained.** Two copies of one bump of width `2r − t`, the first at the left
end of the window and the second a lag `t` further on, form a test of aperture `r` whose
autocorrelation at `t` is exactly half its mass.  So no per-lag estimate of the prime side can
improve on `½` beyond the aperture. -/
theorem autoCorrelation_half_attained {g : ℝ → ℝ} (hg : Continuous g) {r t : ℝ}
    (hr : 0 < r) (ht : r < t) (hgsupp : ∀ y, y < 0 ∨ 2 * r - t < y → g y = 0) :
    autoCorrelation (fun x => g (x + r) + g (x - (t - r))) t
      = autoCorrelation (fun x => g (x + r) + g (x - (t - r))) 0 / 2 := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 2 * r - t)) fun x hx => by
      rcases not_and_or.mp (fun h => hx (Set.mem_Icc.mpr h)) with h | h
      · exact hgsupp x (Or.inl (not_le.mp h))
      · exact hgsupp x (Or.inr (not_le.mp h))
  have hsq : Integrable fun x => g x * g x :=
    (hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right
  have hz1 : ∀ x : ℝ, g (x + r) * g (x + t + r) = 0 := fun x => by
    have h := mul_shift_eq_zero_of_bump hgsupp (d := t)
      (by rw [abs_of_pos (by linarith)]; linarith) (x + r)
    rw [show x + t + r = x + r + t by ring]; exact h
  have hz2 : ∀ x : ℝ, g (x - (t - r)) * g (x + r) = 0 := fun x => by
    have h := mul_shift_eq_zero_of_bump hgsupp (d := t)
      (by rw [abs_of_pos (by linarith)]; linarith) (x - (t - r))
    rw [show x + r = x - (t - r) + t by ring]; exact h
  have hz3 : ∀ x : ℝ, g (x - (t - r)) * g (x + t + r) = 0 := fun x => by
    have h := mul_shift_eq_zero_of_bump hgsupp (d := 2 * t)
      (by rw [abs_of_pos (by linarith)]; linarith) (x - (t - r))
    rw [show x + t + r = x - (t - r) + 2 * t by ring]; exact h
  have key : ∀ x : ℝ,
      (g (x + r) + g (x - (t - r))) * (g (x + t + r) + g (x + t - (t - r)))
        = g (x + r) * g (x + r) := by
    intro x
    rw [show x + t - (t - r) = x + r by ring]
    nlinarith [hz1 x, hz2 x, hz3 x]
  have key0 : ∀ x : ℝ,
      (g (x + r) + g (x - (t - r))) * (g (x + 0 + r) + g (x + 0 - (t - r)))
        = g (x + r) * g (x + r) + g (x - (t - r)) * g (x - (t - r)) := by
    intro x
    rw [show x + 0 + r = x + r by ring, show x + 0 - (t - r) = x - (t - r) by ring]
    nlinarith [hz2 x]
  have hAt : autoCorrelation (fun x => g (x + r) + g (x - (t - r))) t
      = ∫ x, g (x + r) * g (x + r) := by
    rw [autoCorrelation]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact key x
  have hi1 : Integrable fun x => g (x + r) * g (x + r) := by
    simpa using hsq.comp_add_right r
  have hi2 : Integrable fun x => g (x - (t - r)) * g (x - (t - r)) := by
    simpa using hsq.comp_sub_right (t - r)
  have hshift : (∫ x, g (x - (t - r)) * g (x - (t - r))) = ∫ x, g (x + r) * g (x + r) := by
    have h1 : (∫ x, g (x - (t - r)) * g (x - (t - r))) = ∫ x, g x * g x := by
      simpa using MeasureTheory.integral_sub_right_eq_self (fun x => g x * g x) (t - r)
    have h2 : (∫ x, g (x + r) * g (x + r)) = ∫ x, g x * g x := by
      simpa using MeasureTheory.integral_add_right_eq_self (fun x => g x * g x) r
    rw [h1, h2]
  have hA0 : autoCorrelation (fun x => g (x + r) + g (x - (t - r))) 0
      = 2 * ∫ x, g (x + r) * g (x + r) := by
    have hexp : autoCorrelation (fun x => g (x + r) + g (x - (t - r))) 0
        = ∫ x, (g (x + r) * g (x + r) + g (x - (t - r)) * g (x - (t - r))) := by
      rw [autoCorrelation]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key0)
    rw [hexp, MeasureTheory.integral_add hi1 hi2, hshift]
    ring
  rw [hAt, hA0]
  ring


/-! ### The bipartite reduction beyond the aperture

Past the aperture every lag pairs the left half of the test against the right half, so the whole
prime side beyond the aperture is one bilinear pairing of the two halves.  Its Gram matrix is the
autocorrelation of the *right half* alone, which lives on a window of half the diameter: only the
lag differences below `r` — the prime ratios below `e^{r}`, not `e^{2r}` — enter the bilinear
problem. -/

theorem abs_leftPart_le (F : ℝ → ℝ) (x : ℝ) : |leftPart F x| ≤ |F x| := by
  rw [leftPart]; split_ifs <;> simp

theorem abs_rightPart_le (F : ℝ → ℝ) (x : ℝ) : |rightPart F x| ≤ |F x| := by
  rw [rightPart]; split_ifs <;> simp

/-- The right half of a test of aperture `r` lives on `[0, r]`, so its autocorrelation dies past
`r`: the prime ratios the bilinear problem sees are bounded by `e^{r}`. -/
theorem autoCorrelation_rightPart_eq_zero {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) {s : ℝ}
    (hs : r < |s|) : autoCorrelation (rightPart F) s = 0 := by
  have hz : ∀ x : ℝ, rightPart F x * rightPart F (x + s) = 0 := by
    intro x
    by_cases h1 : rightPart F x = 0
    · rw [h1, zero_mul]
    by_cases h2 : rightPart F (x + s) = 0
    · rw [h2, mul_zero]
    have hx0 : 0 ≤ x := by
      by_contra hc
      exact h1 (by rw [rightPart, if_neg hc])
    have hxs0 : 0 ≤ x + s := by
      by_contra hc
      exact h2 (by rw [rightPart, if_neg hc])
    have hxF : F x ≠ 0 := fun h => h1 (by rw [rightPart, if_pos hx0, h])
    have hxsF : F (x + s) ≠ 0 := fun h => h2 (by rw [rightPart, if_pos hxs0, h])
    have hxr : x ≤ r := by
      have := not_lt.mp fun h => hxF (hsupp x h)
      exact le_trans (le_abs_self x) this
    have hxsr : x + s ≤ r := by
      have := not_lt.mp fun h => hxsF (hsupp (x + s) h)
      exact le_trans (le_abs_self _) this
    exact absurd hs (not_lt.mpr (abs_le.mpr ⟨by linarith, by linarith⟩))
  rw [autoCorrelation]
  simp [hz]

theorem integrable_rightPart_shift_mul (hF : Continuous F) (hFc : HasCompactSupport F)
    (a b : ℝ) : Integrable fun x => rightPart F (x + a) * rightPart F (x + b) := by
  have hbase : Integrable fun x => |F (x + a) * F (x + b)| :=
    (((hF.comp (continuous_id.add continuous_const)).mul
      (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      ((hFc.comp_homeomorph (Homeomorph.addRight a)).mul_right)).abs
  refine hbase.mono' (((measurable_rightPart hF).comp (measurable_id.add_const a)).mul
    ((measurable_rightPart hF).comp (measurable_id.add_const b))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul (abs_rightPart_le F (x + a)) (abs_rightPart_le F (x + b)) (abs_nonneg _)
    (abs_nonneg _)

theorem integral_rightPart_shift_mul (a b : ℝ) :
    (∫ x, rightPart F (x + a) * rightPart F (x + b)) = autoCorrelation (rightPart F) (b - a) := by
  rw [autoCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => rightPart F y * rightPart F (y + (b - a))) a
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show rightPart F (x + a) * rightPart F (x + b)
    = rightPart F (x + a) * rightPart F (x + a + (b - a))
  rw [show x + a + (b - a) = x + b by ring]

theorem integrable_leftPart_mul_rightPart_shift (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) {a : ℝ} (ha : r < a) :
    Integrable fun x => leftPart F x * rightPart F (x + a) := by
  have hc : Integrable fun x => F x * F (x + a) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  exact hc.congr (Filter.Eventually.of_forall fun x =>
    mul_shift_eq_leftPart_mul_rightPart hsupp ha x)

theorem autoCorrelation_eq_halves (hsupp : ∀ y, r < |y| → F y = 0) {a : ℝ} (ha : r < a) :
    autoCorrelation F a = ∫ x, leftPart F x * rightPart F (x + a) := by
  rw [autoCorrelation]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
    mul_shift_eq_leftPart_mul_rightPart hsupp ha x)

theorem integrable_leftPart_sq (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable fun x => leftPart F x ^ 2 := by
  have hsqeq : (fun x => F x ^ 2) = fun x => F x * F x := by funext x; ring
  have hsqF : Integrable fun x => F x ^ 2 := by
    rw [hsqeq]; exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  refine hsqF.mono' ((measurable_leftPart hF).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := abs_leftPart_le F x
  nlinarith [abs_nonneg (leftPart F x), abs_nonneg (F x), sq_abs (leftPart F x), sq_abs (F x)]

/-- **The bipartite reduction.** For lags beyond the aperture the prime side pairs the left half
of the test against the right half, so one Cauchy–Schwarz splits it into the mass of the left half
and the Gram form of the lag differences against the *right half's* autocorrelation — a form that
only sees lag differences below `r`, i.e. prime ratios below `e^{r}` rather than `e^{2r}`. -/
theorem two_mul_sum_lag_le_bipartite (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {T : Finset ℕ} {c lag : ℕ → ℝ}
    (hlag : ∀ n ∈ T, r < lag n) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ n ∈ T, c n * autoCorrelation F (lag n)
      ≤ ε * (∫ x, leftPart F x ^ 2)
        + ε⁻¹ * ∑ n ∈ T, ∑ m ∈ T,
            c n * c m * autoCorrelation (rightPart F) (lag m - lag n) := by
  classical
  set K : ℝ → ℝ := fun x => ∑ n ∈ T, c n * rightPart F (x + lag n) with hK
  have hil : Integrable fun x => leftPart F x ^ 2 := integrable_leftPart_sq hF hFc
  have hiK : Integrable fun x => K x * K x := by
    have heq : (fun x => K x * K x)
        = fun x => ∑ n ∈ T, ∑ m ∈ T,
            c n * c m * (rightPart F (x + lag n) * rightPart F (x + lag m)) := by
      funext x
      rw [hK]
      simp only
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [heq]
    exact integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
      (integrable_rightPart_shift_mul hF hFc (lag n) (lag m)).const_mul (c n * c m)
  have hiu : Integrable fun x => leftPart F x * K x := by
    have heq : (fun x => leftPart F x * K x)
        = fun x => ∑ n ∈ T, c n * (leftPart F x * rightPart F (x + lag n)) := by
      funext x
      rw [hK]
      simp only
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [heq]
    exact integrable_finsetSum _ fun n hn =>
      (integrable_leftPart_mul_rightPart_shift hF hFc hsupp (hlag n hn)).const_mul (c n)
  have hpair : ∑ n ∈ T, c n * autoCorrelation F (lag n) = ∫ x, leftPart F x * K x := by
    have heq : (fun x => leftPart F x * K x)
        = fun x => ∑ n ∈ T, c n * (leftPart F x * rightPart F (x + lag n)) := by
      funext x
      rw [hK]
      simp only
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [heq, integral_finsetSum _ fun n hn =>
      (integrable_leftPart_mul_rightPart_shift hF hFc hsupp (hlag n hn)).const_mul (c n)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [MeasureTheory.integral_const_mul, ← autoCorrelation_eq_halves hsupp (hlag n hn)]
  have hgram : (∫ x, K x * K x)
      = ∑ n ∈ T, ∑ m ∈ T, c n * c m * autoCorrelation (rightPart F) (lag m - lag n) := by
    have heq : (fun x => K x * K x)
        = fun x => ∑ n ∈ T, ∑ m ∈ T,
            c n * c m * (rightPart F (x + lag n) * rightPart F (x + lag m)) := by
      funext x
      rw [hK]
      simp only
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [heq, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
      (integrable_rightPart_shift_mul hF hFc (lag n) (lag m)).const_mul (c n * c m)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ =>
      (integrable_rightPart_shift_mul hF hFc (lag n) (lag m)).const_mul (c n * c m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_const_mul, integral_rightPart_shift_mul]
  have hpt : ∀ x : ℝ, 2 * (leftPart F x * K x)
      ≤ ε * leftPart F x ^ 2 + ε⁻¹ * (K x * K x) := by
    intro x
    rw [← sub_nonneg]
    have hid : ε * leftPart F x ^ 2 + ε⁻¹ * (K x * K x) - 2 * (leftPart F x * K x)
        = ε⁻¹ * (ε * leftPart F x - K x) ^ 2 := by
      field_simp
      ring
    rw [hid]
    positivity
  have hadd : Integrable fun x => ε * leftPart F x ^ 2 + ε⁻¹ * (K x * K x) :=
    (hil.const_mul ε).add (hiK.const_mul ε⁻¹)
  have hmono := MeasureTheory.integral_mono (hiu.const_mul 2) hadd hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  have hsplit : (∫ x, (ε * leftPart F x ^ 2 + ε⁻¹ * (K x * K x)))
      = ε * (∫ x, leftPart F x ^ 2) + ε⁻¹ * ∫ x, K x * K x := by
    rw [MeasureTheory.integral_add (hil.const_mul ε) (hiK.const_mul ε⁻¹),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsplit, hgram] at hmono
  rw [hpair]
  exact hmono


/-! ### The polar term is the pole plane

The polar density of the balance, paired with the autocorrelation, is exactly the hyperbolic pole
plane of the Weil form: the difference of the squares of the test's two half-exponential moments.
So the test-level balance is a statement about the two *arithmetic* channels of the critical form
— the prime channel and the pole plane — with the Chebyshev defect as the whole residue. -/

theorem autoCorrelation_neg (F : ℝ → ℝ) (t : ℝ) :
    autoCorrelation F (-t) = autoCorrelation F t := by
  rw [autoCorrelation, autoCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => F x * F (x + -t)) t
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + t) * F (x + t + -t) = F x * F (x + t)
  rw [show x + t + -t = x by ring, mul_comm]

/-- The two-variable integrand of the polar pairing has compact support. -/
theorem hasCompactSupport_polarPair {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1)) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(2 * r)) (b := 2 * r)).prod (isCompact_Icc (a := -r) (b := r)))
    fun p hp => ?_
  by_cases hx : r < |p.2|
  · rw [hsupp p.2 hx]; ring
  by_cases hxs : r < |p.2 + p.1|
  · rw [hsupp _ hxs]; ring
  exfalso
  refine hp ⟨?_, Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hx))⟩
  have h1 := abs_le.mp (not_lt.mp hx)
  have h2 := abs_le.mp (not_lt.mp hxs)
  exact Set.mem_Icc.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩

/-- **The polar pairing is the pole plane.** `∫ cosh(s/2) A(s) ds` is the difference of the
squares of the test's `cosh` and `sinh` moments. -/
theorem integral_cosh_mul_autoCorrelation (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    (∫ s, Real.cosh (s / 2) * autoCorrelation F s)
      = (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2 := by
  have hcont : Continuous fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1)) := by
    fun_prop
  have hint : Integrable
      (fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1))) :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_polarPair hsupp)
  have hvp : ((volume : Measure ℝ).prod volume) = (volume : Measure (ℝ × ℝ)) :=
    (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
  have hintprod : Integrable (Function.uncurry fun (s : ℝ) (x : ℝ) =>
      Real.cosh (s / 2) * (F x * F (x + s))) ((volume : Measure ℝ).prod volume) :=
    hvp ▸ hint
  have hswap := MeasureTheory.integral_integral_swap hintprod
  have hleft : (∫ s, Real.cosh (s / 2) * autoCorrelation F s)
      = ∫ s, ∫ x, Real.cosh (s / 2) * (F x * F (x + s)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Real.cosh (s / 2) * autoCorrelation F s = ∫ x, Real.cosh (s / 2) * (F x * F (x + s))
    rw [autoCorrelation, MeasureTheory.integral_const_mul]
  -- the inner integral in `s`, after translating, splits by the cosh subtraction formula
  have hinner : ∀ x : ℝ, (∫ s, Real.cosh (s / 2) * (F x * F (x + s)))
      = F x * (Real.cosh (x / 2) * (∫ u, F u * Real.cosh (u / 2))
          - Real.sinh (x / 2) * ∫ u, F u * Real.sinh (u / 2)) := by
    intro x
    have hco : Integrable fun u => F u * Real.cosh (u / 2) :=
      (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFc.mul_right
    have hsi : Integrable fun u => F u * Real.sinh (u / 2) :=
      (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFc.mul_right
    have htr := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u => Real.cosh ((u - x) / 2) * (F x * F u)) x
    have hstep : (∫ s, Real.cosh (s / 2) * (F x * F (x + s)))
        = ∫ u, Real.cosh ((u - x) / 2) * (F x * F u) := by
      rw [← htr]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show Real.cosh (s / 2) * (F x * F (x + s))
        = Real.cosh ((s + x - x) / 2) * (F x * F (s + x))
      rw [show s + x - x = s by ring, show x + s = s + x by ring]
    rw [hstep]
    have hexpand : ∀ u : ℝ, Real.cosh ((u - x) / 2) * (F x * F u)
        = F x * (Real.cosh (x / 2) * (F u * Real.cosh (u / 2))
            - Real.sinh (x / 2) * (F u * Real.sinh (u / 2))) := by
      intro u
      have : Real.cosh ((u - x) / 2)
          = Real.cosh (u / 2) * Real.cosh (x / 2) - Real.sinh (u / 2) * Real.sinh (x / 2) := by
        rw [show (u - x) / 2 = u / 2 - x / 2 by ring, Real.cosh_sub]
      rw [this]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (hco.const_mul _) (hsi.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hleft, hswap]
  have hco : Integrable fun u => F u * Real.cosh (u / 2) :=
    (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsi : Integrable fun u => F u * Real.sinh (u / 2) :=
    (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hfin : ∀ x : ℝ, F x * (Real.cosh (x / 2) * (∫ u, F u * Real.cosh (u / 2))
        - Real.sinh (x / 2) * ∫ u, F u * Real.sinh (u / 2))
      = (∫ u, F u * Real.cosh (u / 2)) * (F x * Real.cosh (x / 2))
        - (∫ u, F u * Real.sinh (u / 2)) * (F x * Real.sinh (x / 2)) := fun x => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfin),
    MeasureTheory.integral_sub (hco.const_mul _) (hsi.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring


/-- An even integrable function integrates to twice its integral over the positive half-line. -/
theorem integral_eq_two_mul_Ioi {g : ℝ → ℝ} (hg : Integrable g) (he : ∀ x, g (-x) = g x) :
    (∫ x, g x) = 2 * ∫ x in Ioi (0:ℝ), g x := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0:ℝ)) = Iio 0 := by
    ext x; simp
  have h1 : (∫ x in Iio (0:ℝ), g x) = ∫ y in Ioi (0:ℝ), g y := by
    have hpe := hneg.setIntegral_preimage_emb hemb g (Ioi (0:ℝ))
    rw [hpre] at hpe
    rw [← hpe]
    exact setIntegral_congr_fun measurableSet_Iio fun x _ => (he x).symm
  have h2 : (∫ x, g x) = (∫ x in Iio (0:ℝ), g x) + ∫ x in Ici (0:ℝ), g x := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Iio (a := (0:ℝ))) hg
    rw [show (Iio (0:ℝ))ᶜ = Ici (0:ℝ) by ext x; simp] at h
    exact h.symm
  have h3 : (∫ x in Ici (0:ℝ), g x) = ∫ x in Ioi (0:ℝ), g x :=
    MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [h2, h1, h3]; ring

theorem hasCompactSupport_autoCorrelation (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) : HasCompactSupport (autoCorrelation F) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * r)) (b := 2 * r)) fun t ht => ?_
  rcases lt_or_ge t 0 with h | h
  · rw [← autoCorrelation_neg]
    refine autoCorrelation_eq_zero hF hr hsupp ?_
    by_contra hc
    exact ht (Set.mem_Icc.mpr ⟨by linarith [not_le.mp hc], by linarith⟩)
  · refine autoCorrelation_eq_zero hF hr hsupp ?_
    by_contra hc
    exact ht (Set.mem_Icc.mpr ⟨by linarith, by linarith [not_le.mp hc]⟩)

/-- **The test-level balance in the pole plane.** The prime channel of the critical form and its
hyperbolic pole plane — the difference of the squares of the test's two half-exponential moments —
cancel to the accuracy of the prime number theorem, with the two-pole Chebyshev defect as the
entire residue. -/
theorem testBalance_poleplane (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
  have hAcs : HasCompactSupport (autoCorrelation F) :=
    hasCompactSupport_autoCorrelation hF.continuous hr hsupp
  have hg : Integrable fun s => Real.cosh (s / 2) * autoCorrelation F s :=
    (((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hAc)).integrable_of_hasCompactSupport
      hAcs.mul_left
  have heven : ∀ s : ℝ, Real.cosh (-s / 2) * autoCorrelation F (-s)
      = Real.cosh (s / 2) * autoCorrelation F s := by
    intro s
    rw [autoCorrelation_neg, show -s / 2 = -(s / 2) by ring, Real.cosh_neg]
  have hhalf := integral_eq_two_mul_Ioi hg heven
  have hpolar := integral_cosh_mul_autoCorrelation hF.continuous hFc hsupp
  have hfour : (∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s)
      = 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2) := by
    have hre : (∫ s in Ioi (0:ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s)
        = 4 * ∫ s in Ioi (0:ℝ), Real.cosh (s / 2) * autoCorrelation F s := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
    rw [hre, ← hpolar, hhalf]
    ring
  rw [← hfour]
  exact testBalance hF hFc hr hsupp hN


/-! ### Odd tests, and the explicit rate of the cost side

On an odd test the `cosh` moment vanishes, so the pole plane is `−(∫F sinh)²` and the balance puts
the prime side and the pole charge — the two cost terms of the incidence ledger — on the same
side.  Their sum is the Chebyshev functional, and bounding it against the weight gives the
unconditional rate: an explicit constant depending only on the test, times the size of the
Chebyshev defect below the horizon. -/

theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x) = 0 := by
  have h1 : (∫ x, f (-x)) = ∫ x, f x := integral_neg_eq_self f volume
  have h2 : (∫ x, f (-x)) = -∫ x, f x := by
    rw [← MeasureTheory.integral_neg]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hodd)
  linarith [h1, h2]

/-- **The ledger's cost side is the Chebyshev functional.** For an odd compact test the prime side
and the pole charge `2(∫F sinh(x/2))²` — the two nonnegative costs of the incidence ledger — sum
exactly to the two-pole Chebyshev defect against the test's lag weight. -/
theorem testBalance_odd (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        + 2 * (∫ x, F x * Real.sinh (x / 2)) ^ 2
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hcosh : (∫ x, F x * Real.cosh (x / 2)) = 0 := by
    refine integral_eq_zero_of_odd fun x => ?_
    rw [hodd x, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    ring
  have h := testBalance_poleplane hF hFc hr hsupp hN
  rw [hcosh] at h
  rw [← h]
  ring

/-- **The explicit rate of the cost side.** The arithmetic channels of the critical form are
bounded by the Chebyshev defect below the horizon, weighted by the test's own lag weight: every
improvement in the one-sided size of `ψ(x) − x − log x + 1` transfers directly into the ledger. -/
theorem abs_testBalance_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)|
      ≤ ∫ s in Ioi (0:ℝ), |chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))| := by
  rw [testBalance_poleplane hF hFc hr hsupp hN]
  exact abs_integral_le_integral_abs


/-! ### The selectivity audit: the shifted pair

The balance is universal, so what separates sources is the size of their own two-pole defect.  The
shifted pair `ζ(s−α)ζ(s+α)` carries the weight `Λ(n)(n^α + n^{−α})`, which dominates `2Λ(n)` at
every index; its prefix therefore exceeds twice Chebyshev's function and its two-pole defect falls
short of `ζ`'s by the whole Chebyshev count.  A comparison density calibrated to `ζ` is thus
displaced by a full `ψ` for the shifted pair: the two sources cannot share a two-pole
calibration. -/

/-- The von Mangoldt weight of the shifted pair `ζ(s−α)ζ(s+α)`. -/
def shiftedPairWeight (α : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ α + (n : ℝ) ^ (-α))

theorem shiftedPairWeight_zero (α : ℝ) : shiftedPairWeight α 0 = 0 := by
  simp [shiftedPairWeight]

theorem shiftedPairWeight_one (α : ℝ) : shiftedPairWeight α 1 = 0 := by
  simp [shiftedPairWeight]

/-- At every index the shifted pair's weight is at least twice the von Mangoldt weight. -/
theorem two_mul_vonMangoldt_le_shiftedPairWeight (α : ℝ) (n : ℕ) :
    2 * (ArithmeticFunction.vonMangoldt n : ℝ) ≤ shiftedPairWeight α n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · simp [h0, shiftedPairWeight]
  have hn : (0:ℝ) < n := by exact_mod_cast h0
  have ht : (0:ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn α
  have hinv : (n : ℝ) ^ (-α) = ((n : ℝ) ^ α)⁻¹ := Real.rpow_neg hn.le α
  have hsum : (2:ℝ) ≤ (n : ℝ) ^ α + (n : ℝ) ^ (-α) := by
    rw [hinv, ← sub_nonneg]
    have key : (n : ℝ) ^ α + ((n : ℝ) ^ α)⁻¹ - 2
        = ((n : ℝ) ^ α - 1) ^ 2 / (n : ℝ) ^ α := by
      field_simp
      ring
    rw [key]
    positivity
  have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  rw [shiftedPairWeight]
  nlinarith [hsum, hΛ]

theorem lagPrefix_mono_of_le {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) (s : ℝ) :
    lagPrefix a s ≤ lagPrefix b s :=
  Finset.sum_le_sum fun n _ => hab n

theorem lagPrefix_two_mul_vonMangoldt (s : ℝ) :
    lagPrefix (fun n => 2 * (ArithmeticFunction.vonMangoldt n : ℝ)) s = 2 * lagChebyshev s := by
  rw [lagPrefix, lagChebyshev, Finset.mul_sum]

/-- **The shifted pair's defect is displaced by a full Chebyshev count.** -/
theorem lagSourceDefect_shiftedPair_le (α : ℝ) (s : ℝ) :
    lagSourceDefect (shiftedPairWeight α) s ≤ chebyshevTwoPoleDefect s - lagChebyshev s := by
  have hle : lagPrefix (fun n => 2 * (ArithmeticFunction.vonMangoldt n : ℝ)) s
      ≤ lagPrefix (shiftedPairWeight α) s :=
    lagPrefix_mono_of_le (fun n => two_mul_vonMangoldt_le_shiftedPairWeight α n) s
  rw [lagPrefix_two_mul_vonMangoldt] at hle
  rw [lagSourceDefect, chebyshevTwoPoleDefect]
  linarith

/-- **The balance for the shifted pair.** The same identity holds with the shifted pair's own
defect: the mechanism is universal, the calibration is not. -/
theorem sum_shiftedPair_sub_polar_eq_defect (α : ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), shiftedPairWeight α n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), lagSourceDefect (shiftedPairWeight α) s * deriv h s :=
  sum_weight_sub_polar_eq_defect _ (shiftedPairWeight_zero α) (shiftedPairWeight_one α)
    hh hS hvan hN


/-! ### Source rigidity, and twists

The balance's residue is a *complete invariant* of the arithmetic source: two sources with the
same lag defect agree index by index.  So the identity, universal though it is, does not hold
"verbatim for another system" in any sense that loses information — a Beurling system with a
different weight has a different defect at some index.  Twisting by signs can only enlarge the
defect: among all weights dominated by `Λ`, the von Mangoldt weight is the one closest to the
two-pole calibration. -/

theorem lagPrefix_log_nat (a : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    lagPrefix a (Real.log m) = ∑ k ∈ Finset.Icc 0 m, a k := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [lagPrefix, Real.exp_log hm0, Nat.floor_natCast]

theorem lagPrefix_neg_one (a : ℕ → ℝ) : lagPrefix a (-1) = a 0 := by
  have hfl : ⌊Real.exp (-1 : ℝ)⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, Real.exp_lt_one_iff]
    norm_num
  rw [lagPrefix, hfl]
  simp

/-- **Source rigidity.** The lag prefix determines the source index by index, so the balance's
residue is a complete invariant: distinct arithmetic sources have distinct defects. -/
theorem eq_of_lagPrefix_eq {a b : ℕ → ℝ} (h : lagPrefix a = lagPrefix b) : a = b := by
  have hS : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, a k = ∑ k ∈ Finset.Icc 0 m, b k := by
    intro m
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have hm := congrFun h (-1 : ℝ)
      rw [lagPrefix_neg_one, lagPrefix_neg_one] at hm
      simpa using hm
    · have hm := congrFun h (Real.log m)
      rwa [lagPrefix_log_nat a h0, lagPrefix_log_nat b h0] at hm
  funext n
  cases n with
  | zero => simpa using hS 0
  | succ m =>
    have h1 := hS (m + 1)
    have h2 := hS m
    rw [Finset.sum_Icc_succ_top (Nat.zero_le _), Finset.sum_Icc_succ_top (Nat.zero_le _)] at h1
    linarith

/-- Distinct sources are separated by the balance. -/
theorem lagSourceDefect_ne_of_ne {a b : ℕ → ℝ} (hab : a ≠ b) :
    lagSourceDefect a ≠ lagSourceDefect b := by
  intro h
  refine hab (eq_of_lagPrefix_eq (funext fun s => ?_))
  have := congrFun h s
  rw [lagSourceDefect, lagSourceDefect] at this
  linarith

/-- **Twists only enlarge the defect.** Every weight dominated by `Λ` — a sign twist, a character
twist, a thinned Beurling weight — sits further from the two-pole calibration than `ζ` does. -/
theorem chebyshevTwoPoleDefect_le_lagSourceDefect {a : ℕ → ℝ}
    (ha : ∀ n, a n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) (s : ℝ) :
    chebyshevTwoPoleDefect s ≤ lagSourceDefect a s := by
  have hp := lagPrefix_mono_of_le ha s
  have hc : lagChebyshev s = lagPrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s :=
    congrFun lagChebyshev_eq_lagPrefix s
  rw [lagSourceDefect, chebyshevTwoPoleDefect, hc]
  linarith


/-! ### The lag weight of a test is explicitly bounded

Elementary Cauchy–Schwarz bounds the autocorrelation and the cross-correlation by the test's two
energies, so the lag weight of a test is at most `e^{−s/2}` times an explicit constant.  The
grading is then fully quantitative: the ledger's deficit at aperture `r` is the Chebyshev defect
against an exponentially damped weight of bounded total size. -/

theorem abs_autoCorrelation_le (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    |autoCorrelation F t| ≤ autoCorrelation F 0 := by
  have hsqeq : (fun x => F x ^ 2) = fun x => F x * F x := by funext x; ring
  have hsqF : Integrable fun x => F x ^ 2 := by
    rw [hsqeq]; exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hsqT : Integrable fun x => F (x + t) ^ 2 := by
    simpa using hsqF.comp_add_right t
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hA0 : autoCorrelation F 0 = ∫ x, F x ^ 2 := by
    rw [autoCorrelation]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + 0) = F x ^ 2
    rw [add_zero, sq]
  have hT : (∫ x, F (x + t) ^ 2) = ∫ x, F x ^ 2 := by
    simpa using MeasureTheory.integral_add_right_eq_self (fun x => F x ^ 2) t
  have hbound : ∀ x : ℝ, |F x * F (x + t)| ≤ (F x ^ 2 + F (x + t) ^ 2) / 2 := fun x => by
    rcases abs_cases (F x * F (x + t)) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
      nlinarith [sq_nonneg (F x - F (x + t)), sq_nonneg (F x + F (x + t))]
  have hmid : |∫ x, F x * F (x + t)| ≤ ∫ x, (F x ^ 2 + F (x + t) ^ 2) / 2 := by
    refine le_trans abs_integral_le_integral_abs ?_
    refine MeasureTheory.integral_mono hprod.abs (((hsqF.add hsqT)).div_const 2) fun x => ?_
    exact hbound x
  have hrhs : (∫ x, (F x ^ 2 + F (x + t) ^ 2) / 2) = ∫ x, F x ^ 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hsqF hsqT, hT]
    ring
  rw [autoCorrelation, hA0, ← hrhs]
  exact hmid

theorem abs_crossCorrelation_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (t : ℝ) :
    |crossCorrelation F t| ≤ (autoCorrelation F 0 + ∫ x, deriv F x ^ 2) / 2 := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hsqeq : (fun x => F x ^ 2) = fun x => F x * F x := by funext x; ring
  have hsqF : Integrable fun x => F x ^ 2 := by
    rw [hsqeq]; exact (hFcont.mul hFcont).integrable_of_hasCompactSupport hFc.mul_right
  have hdsqeq : (fun x => deriv F x ^ 2) = fun x => deriv F x * deriv F x := by funext x; ring
  have hsqD : Integrable fun x => deriv F x ^ 2 := by
    rw [hdsqeq]
    exact (hdcont.mul hdcont).integrable_of_hasCompactSupport hFc.deriv.mul_right
  have hsqDT : Integrable fun x => deriv F (x + t) ^ 2 := by
    simpa using hsqD.comp_add_right t
  have hprod : Integrable fun x => F x * deriv F (x + t) :=
    (hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hA0 : autoCorrelation F 0 = ∫ x, F x ^ 2 := by
    rw [autoCorrelation]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + 0) = F x ^ 2
    rw [add_zero, sq]
  have hT : (∫ x, deriv F (x + t) ^ 2) = ∫ x, deriv F x ^ 2 := by
    simpa using MeasureTheory.integral_add_right_eq_self (fun x => deriv F x ^ 2) t
  have hbound : ∀ x : ℝ, |F x * deriv F (x + t)| ≤ (F x ^ 2 + deriv F (x + t) ^ 2) / 2 :=
    fun x => by
      rcases abs_cases (F x * deriv F (x + t)) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;>
        nlinarith [sq_nonneg (F x - deriv F (x + t)), sq_nonneg (F x + deriv F (x + t))]
  have hmid : |∫ x, F x * deriv F (x + t)| ≤ ∫ x, (F x ^ 2 + deriv F (x + t) ^ 2) / 2 := by
    refine le_trans abs_integral_le_integral_abs ?_
    exact MeasureTheory.integral_mono hprod.abs ((hsqF.add hsqDT).div_const 2) hbound
  have hrhs : (∫ x, (F x ^ 2 + deriv F (x + t) ^ 2) / 2)
      = ((∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) / 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hsqF hsqDT, hT]
  rw [crossCorrelation, hA0]
  rw [hrhs] at hmid
  exact hmid

/-- **The lag weight of a test is exponentially damped with an explicit constant.** -/
theorem abs_lagTestWeight_deriv_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (s : ℝ) :
    |2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)|
      ≤ Real.exp (-s / 2) * (2 * autoCorrelation F 0 + ∫ x, deriv F x ^ 2) := by
  have hA := abs_autoCorrelation_le hF.continuous hFc s
  have hX := abs_crossCorrelation_le hF hFc s
  have hexp : (0:ℝ) < Real.exp (-s / 2) := Real.exp_pos _
  have hstep : |crossCorrelation F s - autoCorrelation F s / 2|
      ≤ (2 * autoCorrelation F 0 + ∫ x, deriv F x ^ 2) / 2 := by
    have h1 := abs_sub (crossCorrelation F s) (autoCorrelation F s / 2)
    have h2 : |autoCorrelation F s / 2| = |autoCorrelation F s| / 2 := by
      rw [abs_div]; simp
    calc |crossCorrelation F s - autoCorrelation F s / 2|
        ≤ |crossCorrelation F s| + |autoCorrelation F s / 2| := abs_sub _ _
      _ ≤ (autoCorrelation F 0 + ∫ x, deriv F x ^ 2) / 2 + autoCorrelation F 0 / 2 := by
          rw [h2]; linarith
      _ = (2 * autoCorrelation F 0 + ∫ x, deriv F x ^ 2) / 2 := by ring
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hexp]
  nlinarith [hstep, hexp.le, abs_nonneg (crossCorrelation F s - autoCorrelation F s / 2)]


/-! ### The aperture–lag ladder

At a general lag the points of the support reachable from one another by steps of `t` form chains
of at most `⌊2r/t⌋ + 1` points, and the extremal correlation along a chain of `k` points is the
top eigenvalue `cos(π/(k+1))` of the path.  The Schur weight realising it is the discrete sine on
the chain index, and it bounds the autocorrelation at every lag by the corresponding cosine. -/

/-- The chain index of a point at step `t`: which rung of the `t`-ladder it sits on. -/
def chainIndex (r t x : ℝ) : ℤ := ⌊(x + r) / t⌋

/-- Two more than the number of steps of the `t`-ladder across the aperture. -/
def chainRungs (r t : ℝ) : ℤ := ⌊2 * r / t⌋ + 2

/-- The discrete sine weight of the chain. -/
def chainWeight (r t x : ℝ) : ℝ :=
  max (Real.sin (Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ))) 0

theorem two_le_chainRungs {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 2 ≤ chainRungs r t := by
  have h : 0 ≤ ⌊2 * r / t⌋ := Int.floor_nonneg.mpr (by positivity)
  rw [chainRungs]; omega

theorem chainRungs_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : (0:ℝ) < (chainRungs r t : ℝ) := by
  have h := two_le_chainRungs hr ht
  have : (2:ℝ) ≤ (chainRungs r t : ℝ) := by exact_mod_cast h
  linarith

theorem chainIndex_add (r t x : ℝ) (ht : t ≠ 0) :
    chainIndex r t (x + t) = chainIndex r t x + 1 := by
  rw [chainIndex, chainIndex, show (x + t + r) / t = (x + r) / t + 1 by field_simp; ring,
    Int.floor_add_one]

theorem chainIndex_sub (r t x : ℝ) (ht : t ≠ 0) :
    chainIndex r t (x - t) = chainIndex r t x - 1 := by
  have h := chainIndex_add r t (x - t) ht
  rw [show x - t + t = x by ring] at h
  omega

theorem chainIndex_nonneg {r t x : ℝ} (ht : 0 < t) (hx : -r ≤ x) : 0 ≤ chainIndex r t x := by
  rw [chainIndex]
  exact Int.floor_nonneg.mpr (div_nonneg (by linarith) ht.le)

theorem chainIndex_le {r t x : ℝ} (ht : 0 < t) (hx : x ≤ r) :
    chainIndex r t x ≤ chainRungs r t - 2 := by
  have hdiv : (x + r) / t ≤ 2 * r / t := by
    rw [div_le_div_iff_of_pos_right ht]
    linarith
  rw [chainRungs, chainIndex]
  have := Int.floor_le_floor hdiv
  omega


theorem chainWeight_nonneg (r t x : ℝ) : 0 ≤ chainWeight r t x := le_max_right _ _

theorem chainWeight_eq_sin_of_mem {r t x : ℝ} (hr : 0 < r) (ht : 0 < t) (hx1 : -r ≤ x)
    (hx2 : x ≤ r) :
    chainWeight r t x
      = Real.sin (Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ)) := by
  have hN := chainRungs_pos hr ht
  have hj0 : (0:ℝ) ≤ (chainIndex r t x : ℝ) := by exact_mod_cast chainIndex_nonneg ht hx1
  have hjN : (chainIndex r t x : ℝ) ≤ (chainRungs r t : ℝ) - 2 := by
    exact_mod_cast chainIndex_le ht hx2
  have h1 : 0 < Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ) := by
    apply div_pos _ hN
    nlinarith [Real.pi_pos]
  have h2 : Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hN]
    nlinarith [Real.pi_pos]
  exact max_eq_left (Real.sin_pos_of_pos_of_lt_pi h1 h2).le

theorem chainWeight_pos_of_mem {r t x : ℝ} (hr : 0 < r) (ht : 0 < t) (hx1 : -r ≤ x)
    (hx2 : x ≤ r) : 0 < chainWeight r t x := by
  have hN := chainRungs_pos hr ht
  have hj0 : (0:ℝ) ≤ (chainIndex r t x : ℝ) := by exact_mod_cast chainIndex_nonneg ht hx1
  have hjN : (chainIndex r t x : ℝ) ≤ (chainRungs r t : ℝ) - 2 := by
    exact_mod_cast chainIndex_le ht hx2
  have h1 : 0 < Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ) := by
    apply div_pos _ hN
    nlinarith [Real.pi_pos]
  have h2 : Real.pi * ((chainIndex r t x : ℝ) + 1) / (chainRungs r t : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hN]
    nlinarith [Real.pi_pos]
  rw [chainWeight_eq_sin_of_mem hr ht hx1 hx2]
  exact Real.sin_pos_of_pos_of_lt_pi h1 h2

/-- **The three-term recursion of the chain weight.** -/
theorem chainWeight_add_add_sub {r t x : ℝ} (hr : 0 < r) (ht : 0 < t) (hx1 : -r ≤ x)
    (hx2 : x ≤ r) :
    chainWeight r t (x + t) + chainWeight r t (x - t)
      = 2 * Real.cos (Real.pi / (chainRungs r t : ℝ)) * chainWeight r t x := by
  have hN := chainRungs_pos hr ht
  set N : ℝ := (chainRungs r t : ℝ) with hNdef
  set j : ℝ := (chainIndex r t x : ℝ) with hjdef
  have hj0 : (0:ℝ) ≤ j := by rw [hjdef]; exact_mod_cast chainIndex_nonneg ht hx1
  have hjN : j ≤ N - 2 := by rw [hjdef, hNdef]; exact_mod_cast chainIndex_le ht hx2
  have hup : chainWeight r t (x + t) = Real.sin (Real.pi * (j + 2) / N) := by
    rw [chainWeight, chainIndex_add r t x ht.ne']
    push_cast
    rw [show ((chainIndex r t x : ℝ) + 1 + 1) = j + 2 by rw [hjdef]; ring]
    refine max_eq_left (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · apply div_nonneg _ hN.le
      nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
  have hdn : chainWeight r t (x - t) = Real.sin (Real.pi * j / N) := by
    rw [chainWeight, chainIndex_sub r t x ht.ne']
    push_cast
    rw [show ((chainIndex r t x : ℝ) - 1 + 1) = j by rw [hjdef]; ring]
    refine max_eq_left (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
    · apply div_nonneg _ hN.le
      nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
  have hmid : chainWeight r t x = Real.sin (Real.pi * (j + 1) / N) := by
    rw [chainWeight_eq_sin_of_mem hr ht hx1 hx2, hjdef, hNdef]
  rw [hup, hdn, hmid]
  have hA : Real.pi * (j + 2) / N = Real.pi * (j + 1) / N + Real.pi / N := by field_simp; ring
  have hB : Real.pi * j / N = Real.pi * (j + 1) / N - Real.pi / N := by field_simp; ring
  rw [hA, hB, Real.sin_add, Real.sin_sub]
  ring


theorem measurable_chainWeight (r t : ℝ) : Measurable (chainWeight r t) := by
  have hidx : Measurable (chainIndex r t) :=
    Int.measurable_floor.comp ((measurable_id.add_const r).div_const t)
  have hcast : Measurable fun x : ℝ => ((chainIndex r t x : ℝ)) :=
    (measurable_from_top (f := fun n : ℤ => (n : ℝ))).comp hidx
  exact ((Real.measurable_sin.comp
    (((hcast.add_const 1).const_mul Real.pi).div_const _)).max measurable_const)

/-- **The aperture–lag ladder.** For every continuous test supported in `[−r, r]` and every lag
`t > 0`, the autocorrelation is at most `cos(π/(⌊2r/t⌋ + 2))` times the mass.  Past the aperture
this is the sharp `½`; at a general lag it is the top eigenvalue of the path on the chain of
points the step `t` can reach inside the support. -/
theorem autoCorrelation_le_chainConstant (hF : Continuous F) (hFc : HasCompactSupport F)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hsupp : ∀ y, r < |y| → F y = 0) :
    autoCorrelation F t ≤ Real.cos (Real.pi / (chainRungs r t : ℝ)) * autoCorrelation F 0 := by
  set c : ℝ := Real.cos (Real.pi / (chainRungs r t : ℝ)) with hc
  set W : ℝ → ℝ := chainWeight r t with hW
  have hWnn : ∀ x, 0 ≤ W x := fun x => chainWeight_nonneg r t x
  have hmem : ∀ x : ℝ, F x ≠ 0 → -r ≤ x ∧ x ≤ r := by
    intro x hx
    have := not_lt.mp fun h => hx (hsupp x h)
    exact abs_le.mp this
  -- the Schur step
  have hpt : ∀ x : ℝ, 2 * (F x * F (x + t))
      ≤ W (x + t) / W x * F x ^ 2 + W x / W (x + t) * F (x + t) ^ 2 := by
    intro x
    by_cases hx : F x = 0
    · rw [hx]
      have : 0 ≤ W x / W (x + t) * F (x + t) ^ 2 :=
        mul_nonneg (div_nonneg (hWnn x) (hWnn (x + t))) (sq_nonneg _)
      simp only [zero_mul, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      nlinarith [this, mul_nonneg (div_nonneg (hWnn (x + t)) (hWnn x)) (sq_nonneg (0:ℝ))]
    by_cases hxt : F (x + t) = 0
    · rw [hxt]
      have : 0 ≤ W (x + t) / W x * F x ^ 2 :=
        mul_nonneg (div_nonneg (hWnn (x + t)) (hWnn x)) (sq_nonneg _)
      simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      nlinarith [this]
    · obtain ⟨h1, h2⟩ := hmem x hx
      obtain ⟨h3, h4⟩ := hmem (x + t) hxt
      have hWx : 0 < W x := chainWeight_pos_of_mem hr ht h1 h2
      have hWxt : 0 < W (x + t) := chainWeight_pos_of_mem hr ht h3 h4
      rw [← sub_nonneg]
      have hid : W (x + t) / W x * F x ^ 2 + W x / W (x + t) * F (x + t) ^ 2
          - 2 * (F x * F (x + t))
          = (W (x + t) * F x - W x * F (x + t)) ^ 2 / (W x * W (x + t)) := by
        field_simp
        ring
      rw [hid]
      positivity
  -- the recursion turns the two weights into the constant
  have hrec : ∀ x : ℝ, W (x + t) / W x * F x ^ 2 + W (x - t) / W x * F x ^ 2
      = 2 * c * F x ^ 2 := by
    intro x
    by_cases hx : F x = 0
    · rw [hx]; ring
    · obtain ⟨h1, h2⟩ := hmem x hx
      have hWx : 0 < W x := chainWeight_pos_of_mem hr ht h1 h2
      have hsum := chainWeight_add_add_sub hr ht h1 h2
      field_simp
      nlinarith [hsum, hWx]
  -- integrability
  have hsqeq : (fun x => F x ^ 2) = fun x => F x * F x := by funext x; ring
  have hsqF : Integrable fun x => F x ^ 2 := by
    rw [hsqeq]; exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hmA : Measurable fun x => W (x + t) / W x * F x ^ 2 :=
    (((measurable_chainWeight r t).comp (measurable_id.add_const t)).div
      (measurable_chainWeight r t)).mul (hF.measurable.pow_const 2)
  have hmG : Measurable fun x => W (x - t) / W x * F x ^ 2 :=
    (((measurable_chainWeight r t).comp (measurable_id.sub_const t)).div
      (measurable_chainWeight r t)).mul (hF.measurable.pow_const 2)
  have hAnn : ∀ x, 0 ≤ W (x + t) / W x * F x ^ 2 := fun x =>
    mul_nonneg (div_nonneg (hWnn _) (hWnn _)) (sq_nonneg _)
  have hGnn : ∀ x, 0 ≤ W (x - t) / W x * F x ^ 2 := fun x =>
    mul_nonneg (div_nonneg (hWnn _) (hWnn _)) (sq_nonneg _)
  have hdom : Integrable fun x => 2 * c * F x ^ 2 := hsqF.const_mul _
  have hiA : Integrable fun x => W (x + t) / W x * F x ^ 2 := by
    refine hdom.mono' hmA.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn x)]
    nlinarith [hrec x, hGnn x]
  have hiG : Integrable fun x => W (x - t) / W x * F x ^ 2 := by
    refine hdom.mono' hmG.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnn x)]
    nlinarith [hrec x, hAnn x]
  have hiB : Integrable fun x => W x / W (x + t) * F (x + t) ^ 2 := by
    have := hiG.comp_add_right t
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    show W (x + t - t) / W (x + t) * F (x + t) ^ 2 = W x / W (x + t) * F (x + t) ^ 2
    rw [show x + t - t = x by ring]
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  -- integrate
  have hiAB : Integrable fun x => W (x + t) / W x * F x ^ 2 + W x / W (x + t) * F (x + t) ^ 2 :=
    hiA.add hiB
  have hmono := MeasureTheory.integral_mono (hprod.const_mul 2) hiAB hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  have hsplitAB : (∫ x, (W (x + t) / W x * F x ^ 2 + W x / W (x + t) * F (x + t) ^ 2))
      = (∫ x, W (x + t) / W x * F x ^ 2) + ∫ x, W (x - t) / W x * F x ^ 2 := by
    rw [MeasureTheory.integral_add hiA hiB]
    congr 1
    have htr := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => W (y - t) / W y * F y ^ 2) t
    rw [← htr]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show W x / W (x + t) * F (x + t) ^ 2 = W (x + t - t) / W (x + t) * F (x + t) ^ 2
    rw [show x + t - t = x by ring]
  have hAG : (∫ x, W (x + t) / W x * F x ^ 2) + ∫ x, W (x - t) / W x * F x ^ 2
      = 2 * c * ∫ x, F x ^ 2 := by
    rw [← MeasureTheory.integral_add hiA hiG, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrec)
  rw [hsplitAB, hAG] at hmono
  have hA0 : autoCorrelation F 0 = ∫ x, F x ^ 2 := by
    rw [autoCorrelation]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + 0) = F x ^ 2
    rw [add_zero, sq]
  rw [autoCorrelation, hA0]
  linarith


/-! ### The price list of the per-lag reading

The ladder is sharp at every rung, so it is the exact resolution limit of any estimate of the
prime side that reads one lag at a time: the best such estimate is the atoms weighted by their
own ladder constants.  In defect coordinates the same statement is a quadratic decorrelation
floor at every lag. -/

/-- **The quadratic decorrelation floor.** Every test of aperture `r` decorrelates at least
quadratically in the lag: `A(0) − A(t) ≥ 2A(0)/(⌊2r/t⌋ + 2)²`. -/
theorem shiftDefect_ge_quadratic (hF : Continuous F) (hFc : HasCompactSupport F) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hsupp : ∀ y, r < |y| → F y = 0) :
    2 * autoCorrelation F 0 / ((chainRungs r t : ℝ)) ^ 2
      ≤ autoCorrelation F 0 - autoCorrelation F t := by
  have hN := chainRungs_pos hr ht
  have h2N : (2:ℝ) ≤ (chainRungs r t : ℝ) := by
    exact_mod_cast two_le_chainRungs hr ht
  have hA0 : 0 ≤ autoCorrelation F 0 := by
    have h := abs_autoCorrelation_le hF hFc 0
    have := abs_nonneg (autoCorrelation F 0)
    linarith [abs_autoCorrelation_le hF hFc 0, le_abs_self (autoCorrelation F 0)]
  -- the half-angle bound `1 − cos θ = 2 sin²(θ/2) ≥ 2(2θ/(2π))² = 2θ²/π²`
  have hu0 : (0:ℝ) ≤ Real.pi / (chainRungs r t : ℝ) / 2 := by positivity
  have hu1 : Real.pi / (chainRungs r t : ℝ) / 2 ≤ Real.pi / 2 := by
    rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    rw [div_le_iff₀ hN]
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hu0 hu1
  have hhalf : 1 - Real.cos (Real.pi / (chainRungs r t : ℝ))
      = 2 * Real.sin (Real.pi / (chainRungs r t : ℝ) / 2) ^ 2 := by
    have hd := Real.cos_two_mul (Real.pi / (chainRungs r t : ℝ) / 2)
    have hpy := Real.sin_sq_add_cos_sq (Real.pi / (chainRungs r t : ℝ) / 2)
    rw [show 2 * (Real.pi / (chainRungs r t : ℝ) / 2) = Real.pi / (chainRungs r t : ℝ) by ring]
      at hd
    linarith
  have hsin_nn : 0 ≤ Real.sin (Real.pi / (chainRungs r t : ℝ) / 2) :=
    le_trans (by positivity) hjordan
  have hlow : 2 / (chainRungs r t : ℝ) ^ 2
      ≤ 1 - Real.cos (Real.pi / (chainRungs r t : ℝ)) := by
    rw [hhalf]
    have hstep : 2 / Real.pi * (Real.pi / (chainRungs r t : ℝ) / 2) = 1 / (chainRungs r t : ℝ) := by
      field_simp
    rw [hstep] at hjordan
    have hsq : (1 / (chainRungs r t : ℝ)) ^ 2
        ≤ Real.sin (Real.pi / (chainRungs r t : ℝ) / 2) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hjordan
    have : (1 / (chainRungs r t : ℝ)) ^ 2 = 1 / (chainRungs r t : ℝ) ^ 2 := by
      rw [div_pow]; norm_num
    rw [this] at hsq
    have h2 : (2:ℝ) / (chainRungs r t : ℝ) ^ 2 = 2 * (1 / (chainRungs r t : ℝ) ^ 2) := by ring
    rw [h2]
    linarith
  have hlad := autoCorrelation_le_chainConstant hF hFc hr ht hsupp
  have : 2 * autoCorrelation F 0 / (chainRungs r t : ℝ) ^ 2
      = (2 / (chainRungs r t : ℝ) ^ 2) * autoCorrelation F 0 := by ring
  rw [this]
  nlinarith [hlow, hA0, hlad]

/-- **The price list.** The best bound on the prime side available to any estimate reading one
lag at a time: each atom weighted by its own ladder constant.  The ladder being attained at every
rung, no per-lag estimate improves on this. -/
theorem sum_atom_mul_autoCorrelation_le_ladder (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (T : Finset ℕ)
    (hT : ∀ n ∈ T, 2 ≤ n) :
    ∑ n ∈ T, (2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹) *
        autoCorrelation F (Real.log n)
      ≤ autoCorrelation F 0 * ∑ n ∈ T,
          (2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹) *
            Real.cos (Real.pi / (chainRungs r (Real.log n) : ℝ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 : 2 ≤ n := hT n hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hatom : 0 ≤ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹ := by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    positivity
  have hlad := autoCorrelation_le_chainConstant hF hFc hr hlog hsupp
  calc (2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹) *
        autoCorrelation F (Real.log n)
      ≤ (2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹) *
          (Real.cos (Real.pi / (chainRungs r (Real.log n) : ℝ)) * autoCorrelation F 0) :=
        mul_le_mul_of_nonneg_left hlad hatom
    _ = autoCorrelation F 0 * ((2 * (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹) *
          Real.cos (Real.pi / (chainRungs r (Real.log n) : ℝ))) := by ring


/-! ### Band tests see only the increment of the defect

A weight supported in a band bounded away from the origin has `∫ h' = 0`, so adding a constant to
the Chebyshev defect changes nothing: the balance on a band reads the *increment* of
`ψ(x) − x − log x` across the band, not its value.  Large absolute defect is invisible to a band
test; only its variation is charged. -/

theorem integral_Ioi_deriv_eq_zero (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) :
    (∫ s in Ioi (0:ℝ), deriv h s) = 0 := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  rw [integral_Ioi_eq_intervalIntegral hdc hS
    (fun s hs => deriv_eq_zero_of_vanishing hvan hs),
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hh.differentiable one_ne_zero x)
      (hdc.intervalIntegrable _ _), hvan S le_rfl, h0, sub_zero]

/-- **Gauge invariance on a band.** For a weight vanishing near the origin and past `S`, shifting
the Chebyshev defect by a constant does not change the balance's residue. -/
theorem integral_chebyshev_mul_deriv_add_const (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) {N : ℕ} (hN : Real.exp S ≤ N) (c : ℝ) :
    (∫ s in Ioi (0:ℝ), (chebyshevTwoPoleDefect s + c) * deriv h s)
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s := by
  have hiE := integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hh hS hvan hN
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hid : IntegrableOn (fun s => c * deriv h s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_const.mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (chebyshevTwoPoleDefect s + c) * deriv h s)
      = (∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s * deriv h s)
        + ∫ s in Ioi (0:ℝ), c * deriv h s := by
    rw [← MeasureTheory.integral_add hiE hid]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  have hzero : (∫ s in Ioi (0:ℝ), c * deriv h s) = 0 := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_deriv_eq_zero hh hS hvan h0, mul_zero]
  rw [hsplit, hzero, add_zero]

/-- **A band test charges only the variation of the defect.** For a weight vanishing near the
origin and past `S`, the balance's residue is the defect measured from any reference level. -/
theorem sum_vonMangoldt_sub_polar_eq_chebyshev_centred (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) {N : ℕ} (hN : Real.exp S ≤ N) (c : ℝ) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), (chebyshevTwoPoleDefect s - c) * deriv h s := by
  rw [sum_vonMangoldt_sub_polar_eq_chebyshev hh hS hvan hN,
    ← integral_chebyshev_mul_deriv_add_const hh hS hvan h0 hN (-c)]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring


/-! ### The band-localised dictionary

Putting the band restriction together with gauge invariance: a weight supported in `[s₁, s₂]`
sees only the atoms of the band, and charges exactly the band's own increments — the growth of
`e^s + s` against the growth of the source's prefix across the band. -/

theorem integrableOn_Ioi_lagSourceDefect_mul_deriv (a : ℕ → ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => lagSourceDefect a s * deriv h s) (Ioi (0:ℝ)) := by
  refine ((integrableOn_Ioi_twoPoleWeight_mul_deriv hh hS hvan).sub
    (integrableOn_Ioi_lagPrefix_mul_deriv a hh hS hvan hN)).congr_fun
    (fun s _ => ?_) measurableSet_Ioi
  simp [lagSourceDefect, sub_mul]

/-- Gauge invariance for an arbitrary source. -/
theorem integral_lagSourceDefect_mul_deriv_add_const (a : ℕ → ℝ) (hh : ContDiff ℝ 1 h)
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) {N : ℕ} (hN : Real.exp S ≤ N)
    (c : ℝ) :
    (∫ s in Ioi (0:ℝ), (lagSourceDefect a s + c) * deriv h s)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv h s := by
  have hiE := integrableOn_Ioi_lagSourceDefect_mul_deriv a hh hS hvan hN
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hid : IntegrableOn (fun s => c * deriv h s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_const.mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (lagSourceDefect a s + c) * deriv h s)
      = (∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv h s)
        + ∫ s in Ioi (0:ℝ), c * deriv h s := by
    rw [← MeasureTheory.integral_add hiE hid]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  have hzero : (∫ s in Ioi (0:ℝ), c * deriv h s) = 0 := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_deriv_eq_zero hh hS hvan h0, mul_zero]
  rw [hsplit, hzero, add_zero]

/-- A weight vanishing below `s₁` sees only the atoms above the band's foot. -/
theorem sum_weight_eq_band (a : ℕ → ℝ) {s₁ : ℝ} (hvan0 : ∀ s, s ≤ s₁ → h s = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * h (Real.log n)
      = ∑ n ∈ Finset.filter (fun n : ℕ => s₁ < Real.log n) (Finset.range (N + 1)), a n * h (Real.log n) := by
  refine (Finset.sum_filter_of_ne ?_).symm
  intro n _ hne
  by_contra hc
  exact hne (by rw [hvan0 _ (not_lt.mp hc), mul_zero])

/-- **The band-localised balance.** A weight supported in `[s₁, S]` charges the atoms of the band
against the band's own increments: the growth of the two-pole prediction minus the growth of the
source's prefix, measured from the foot of the band. -/
theorem sum_weight_band_sub_polar_eq_increment (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hvan0 : ∀ s, s ≤ s₁ → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.filter (fun n : ℕ => s₁ < Real.log n) (Finset.range (N + 1)), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), (lagSourceDefect a s - lagSourceDefect a s₁) * deriv h s := by
  have h0 : h 0 = 0 := hvan0 0 hs₁
  rw [← sum_weight_eq_band a hvan0 N, sum_weight_sub_polar_eq_defect a ha0 ha1 hh hS hvan hN,
    ← integral_lagSourceDefect_mul_deriv_add_const a hh hS hvan h0 hN (-(lagSourceDefect a s₁))]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring


/-! ### Second-order band tests see the receiver modulo linear functions

A band weight that vanishes to first order at both ends has `∫h'' = 0` and `∫ s h'' = 0`, so the
second-order balance is unchanged by adding any affine function to the receiver primitive.  A
second-order band test therefore charges the *curvature* of `D(s) = ∫_0^s(e^u − ψ(e^u))du` across
the band — neither its value nor its slope. -/

theorem deriv_eq_zero_of_vanishing_left {s₁ : ℝ} (hvan0 : ∀ s, s ≤ s₁ → h s = 0) {s : ℝ}
    (hs : s < s₁) : deriv h s = 0 := by
  have he : h =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_lt_nhds hs] with y hy using hvan0 y hy.le
  rw [he.deriv_eq, deriv_const]

theorem integral_Ioi_deriv_deriv_eq_zero (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (hd0 : deriv h 0 = 0) :
    (∫ s in Ioi (0:ℝ), deriv (deriv h) s) = 0 := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hST : S < S + 1 := by linarith
  have hT0 : (0:ℝ) < S + 1 := by linarith
  rw [integral_Ioi_eq_intervalIntegral hd2 hT0
      (fun s hs => deriv_deriv_eq_zero_of_vanishing hvan (lt_trans hST hs)),
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hh'.differentiable one_ne_zero x)
      (hd2.intervalIntegrable _ _), deriv_eq_zero_of_vanishing hvan hST, hd0, sub_zero]

/-- The first moment of the second derivative vanishes for a band weight. -/
theorem integral_Ioi_id_mul_deriv_deriv_eq_zero (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) :
    (∫ s in Ioi (0:ℝ), s * deriv (deriv h) s) = 0 := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  set T := S + 1 with hT
  have hST : S < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA : (∫ s in Ioi (0:ℝ), s * deriv (deriv h) s) = ∫ s in (0:ℝ)..T, s * deriv (deriv h) s :=
    integral_Ioi_eq_intervalIntegral (continuous_id.mul hd2) hT0
      (fun s hs => by
        rw [deriv_deriv_eq_zero_of_vanishing hvan (lt_trans hST hs), mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), deriv h s) = ∫ s in (0:ℝ)..T, deriv h s :=
    integral_Ioi_eq_intervalIntegral hdc hT0
      (fun s hs => deriv_eq_zero_of_vanishing hvan (lt_trans hST hs))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s) (u' := fun _ : ℝ => (1:ℝ)) (v := deriv h) (v' := deriv (deriv h))
    (a := 0) (b := T)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => (hh'.differentiable one_ne_zero x).hasDerivAt)
    (continuous_const.intervalIntegrable _ _) (hd2.intervalIntegrable _ _)
  have hderivT : deriv h T = 0 := deriv_eq_zero_of_vanishing hvan hST
  have hzero : (∫ s in Ioi (0:ℝ), deriv h s) = 0 := integral_Ioi_deriv_eq_zero hh hS hvan h0
  rw [hB] at hzero
  rw [hA, hparts, hderivT]
  simp only [one_mul, mul_zero, zero_mul, sub_zero, zero_sub]
  rw [hzero]
  ring

/-- **Second-order gauge invariance.** Adding an affine function to the receiver primitive leaves
the second-order balance unchanged, so a band test of second order charges only the curvature. -/
theorem integral_affine_mul_deriv_deriv_eq (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h))
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) (hd0 : deriv h 0 = 0)
    (P : ℝ → ℝ) (hP : IntegrableOn (fun s => P s * deriv (deriv h) s) (Ioi (0:ℝ)))
    (α β : ℝ) :
    (∫ s in Ioi (0:ℝ), (P s + (α * s + β)) * deriv (deriv h) s)
      = ∫ s in Ioi (0:ℝ), P s * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hiaff : IntegrableOn (fun s => (α * s + β) * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing
      (((continuous_const.mul continuous_id).add continuous_const).mul hd2) hS
      (fun s hs => by rw [deriv_deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (P s + (α * s + β)) * deriv (deriv h) s)
      = (∫ s in Ioi (0:ℝ), P s * deriv (deriv h) s)
        + ∫ s in Ioi (0:ℝ), (α * s + β) * deriv (deriv h) s := by
    rw [← MeasureTheory.integral_add hP hiaff]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  have hid : IntegrableOn (fun s => s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_id.mul hd2) hS
      (fun s hs => by rw [deriv_deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hconst : IntegrableOn (fun s => deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing hd2 hS
      (fun s hs => deriv_deriv_eq_zero_of_vanishing hvan hs)
  have haff : (∫ s in Ioi (0:ℝ), (α * s + β) * deriv (deriv h) s) = 0 := by
    have hre : (∫ s in Ioi (0:ℝ), (α * s + β) * deriv (deriv h) s)
        = α * (∫ s in Ioi (0:ℝ), s * deriv (deriv h) s)
          + β * ∫ s in Ioi (0:ℝ), deriv (deriv h) s := by
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_add (hid.const_mul α) (hconst.const_mul β)]
      exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
    rw [hre, integral_Ioi_id_mul_deriv_deriv_eq_zero hh hh' hS hvan h0,
      integral_Ioi_deriv_deriv_eq_zero hh' hS hvan hd0]
    ring
  rw [hsplit, haff, add_zero]


/-! ### The ledger of a band test is the curvature of the receiver

Putting the band restriction, the first-order gauge invariance and the second-order gauge
invariance together: a `C²` weight supported in a band bounded away from the origin reads the
prime side only through the atoms of its band, and charges that band only through the part of the
critical-scale functional that no affine recalibration can absorb. -/

theorem intervalIntegrable_criticalScaleIntegrand (a b : ℝ) :
    IntervalIntegrable (fun u => Real.exp u - lagChebyshev u) volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub lagChebyshev_mono.intervalIntegrable

theorem continuous_criticalScalePrefix : Continuous criticalScalePrefix :=
  intervalIntegral.continuous_primitive intervalIntegrable_criticalScaleIntegrand 0

theorem integrableOn_Ioi_criticalScalePrefix_mul_deriv_deriv (hh' : ContDiff ℝ 1 (deriv h))
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) :
    IntegrableOn (fun s => (criticalScalePrefix s + s ^ 2 / 2 - s) * deriv (deriv h) s)
      (Ioi (0:ℝ)) := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  refine integrableOn_Ioi_of_vanishing ?_ hS
    (fun s hs => by rw [deriv_deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  exact ((continuous_criticalScalePrefix.add
    ((continuous_pow 2).div_const 2)).sub continuous_id).mul hd2

/-- **The ledger of a band test is the curvature of the receiver.** For a `C²` weight supported
in `[s₁, S]` with `s₁ > 0`, the prime side of the band against the polar density is the
critical-scale functional tested by the weight's second derivative — and the answer is unchanged
by any affine recalibration of that functional, so only its curvature is charged. -/
theorem sum_vonMangoldt_band_eq_receiver_curvature (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {s₁ : ℝ}
    (hs₁ : 0 < s₁) (hvan0 : ∀ s, s ≤ s₁ → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) (α β : ℝ) :
    (∑ n ∈ Finset.filter (fun n : ℕ => s₁ < Real.log n) (Finset.range (N + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = -∫ s in Ioi (0:ℝ),
          (criticalScalePrefix s + s ^ 2 / 2 - s + (α * s + β)) * deriv (deriv h) s := by
  have h0 : h 0 = 0 := hvan0 0 hs₁.le
  have hd0 : deriv h 0 = 0 := deriv_eq_zero_of_vanishing_left hvan0 hs₁
  have hP := integrableOn_Ioi_criticalScalePrefix_mul_deriv_deriv hh' hS hvan
  rw [integral_affine_mul_deriv_deriv_eq hh hh' hS hvan h0 hd0 _ hP α β,
    ← sum_weight_eq_band (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hvan0 N]
  exact sum_vonMangoldt_sub_polar_eq_criticalScalePrefix hh hh' hS hvan hN


/-! ### The selectivity audit: the Liouville twist

The third test model.  Twisting the von Mangoldt weight by the Liouville sign gives a source
dominated by `Λ`, so by the twist law its defect exceeds `ζ`'s; the excess is exactly twice the
mass of the prime powers with an odd number of factors, which includes every prime.  With the
shifted pair on the other side, all three test models are separated from `ζ` by a full prime
count in the only quantity the balance sees. -/

/-- The Liouville-twisted von Mangoldt weight `λ(n)Λ(n)`. -/
def liouvilleTwistWeight (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ ArithmeticFunction.cardFactors n * (ArithmeticFunction.vonMangoldt n : ℝ)

theorem liouvilleTwistWeight_zero : liouvilleTwistWeight 0 = 0 := by
  simp [liouvilleTwistWeight]

theorem liouvilleTwistWeight_one : liouvilleTwistWeight 1 = 0 := by
  simp [liouvilleTwistWeight]

theorem liouvilleTwistWeight_le (n : ℕ) :
    liouvilleTwistWeight n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hsign : (-1 : ℝ) ^ ArithmeticFunction.cardFactors n ≤ 1 := by
    rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with he | ho
    · rw [he.neg_one_pow]
    · rw [ho.neg_one_pow]; norm_num
  rw [liouvilleTwistWeight]
  nlinarith [hsign, hΛ]

/-- **The balance for the Liouville twist.** -/
theorem sum_liouvilleTwist_sub_polar_eq_defect (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), liouvilleTwistWeight n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), lagSourceDefect liouvilleTwistWeight s * deriv h s :=
  sum_weight_sub_polar_eq_defect _ liouvilleTwistWeight_zero liouvilleTwistWeight_one
    hh hS hvan hN

/-- The exact excess of the Liouville twist's defect over `ζ`'s: twice the mass of the prime
powers with an odd number of prime factors. -/
theorem lagSourceDefect_liouville_sub (s : ℝ) :
    lagSourceDefect liouvilleTwistWeight s - chebyshevTwoPoleDefect s
      = ∑ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
          ((ArithmeticFunction.vonMangoldt k : ℝ) - liouvilleTwistWeight k) := by
  rw [lagSourceDefect, chebyshevTwoPoleDefect, lagChebyshev, lagPrefix, Finset.sum_sub_distrib]
  ring

/-- **The Liouville twist is separated from `ζ`.** -/
theorem chebyshevTwoPoleDefect_le_liouville (s : ℝ) :
    chebyshevTwoPoleDefect s ≤ lagSourceDefect liouvilleTwistWeight s :=
  chebyshevTwoPoleDefect_le_lagSourceDefect liouvilleTwistWeight_le s


/-! ### The citable estimates: approximation error, not size

The two gauge invariances turn the ledger's deficit into an *approximation error*.  At first
order it is bounded by the distance of the Chebyshev defect from any constant; at second order,
on a band, by the distance of the critical-scale functional from any affine function.  Taking the
best constant and the best affine fit, the deficit is the oscillation and the affine deviation of
the receiver across the band — never its size. -/

/-- **First-order estimate: the deficit is bounded by the distance of `E` from any level.** -/
theorem abs_residue_le_centred (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (h0 : h 0 = 0) {N : ℕ} (hN : Real.exp S ≤ N) (c : ℝ) :
    |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s|
      ≤ ∫ s in Ioi (0:ℝ), |chebyshevTwoPoleDefect s - c| * |deriv h s| := by
  rw [sum_vonMangoldt_sub_polar_eq_chebyshev_centred hh hS hvan h0 hN c]
  refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => abs_mul _ _

/-- **Second-order estimate: on a band the deficit is bounded by the distance of the
critical-scale functional from any affine function.** -/
theorem abs_residue_band_le_affine (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h))
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {s₁ : ℝ} (hs₁ : 0 < s₁)
    (hvan0 : ∀ s, s ≤ s₁ → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) (α β : ℝ) :
    |(∑ n ∈ Finset.filter (fun n : ℕ => s₁ < Real.log n) (Finset.range (N + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s|
      ≤ ∫ s in Ioi (0:ℝ),
          |criticalScalePrefix s + s ^ 2 / 2 - s + (α * s + β)| * |deriv (deriv h) s| := by
  rw [sum_vonMangoldt_band_eq_receiver_curvature hh hh' hS hvan hs₁ hvan0 hN α β, abs_neg]
  refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => abs_mul _ _


/-! ### The second-order calculus of a test

For a `C²` test the cross-correlation is itself differentiable, with the second cross-correlation
as derivative, so the lag weight of a test is `C²` and its second derivative is explicit.  The
second-order balance then applies to tests, and the receiver's curvature is paired with
`2e^{−s/2}(A'' − A' + ¼A)`. -/

/-- The second cross-correlation `∫ F(x) F''(x+t) dx`. -/
def secondCrossCorrelation (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * deriv (deriv F) (x + t)

theorem hasDerivAt_crossCorrelation (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) (t : ℝ) :
    HasDerivAt (crossCorrelation F) (secondCrossCorrelation F t) t := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.deriv.exists_bound_of_continuous hd2cont
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => F x * deriv F (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => F x * deriv (deriv F) (x + u))
    (x₀ := t) (bound := fun x => ‖F x‖ * M) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u =>
      (hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hFc.mul_right))
    ((hFcont.mul (hd2cont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _))
    (integrable_bound hF hFc M)
    (Filter.Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u
        ((hF'.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul (F x))
  exact key.2

theorem continuous_secondCrossCorrelation (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) : Continuous (secondCrossCorrelation F) := by
  have hFcont : Continuous F := hF.continuous
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.deriv.exists_bound_of_continuous hd2cont
  refine continuous_of_dominated (bound := fun x => ‖F x‖ * M)
    (fun u => (hFcont.mul (hd2cont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (fun u => Filter.Eventually.of_forall fun x => ?_) (integrable_bound hF hFc M)
    (Filter.Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)
  · exact continuous_const.mul (hd2cont.comp (continuous_const.add continuous_id))

theorem contDiff_one_crossCorrelation (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) : ContDiff ℝ 1 (crossCorrelation F) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_crossCorrelation hF hF' hFc t).differentiableAt, ?_⟩
  have hd : deriv (crossCorrelation F) = secondCrossCorrelation F :=
    funext fun t => (hasDerivAt_crossCorrelation hF hF' hFc t).deriv
  rw [hd]
  exact continuous_secondCrossCorrelation hF hF' hFc

/-- The lag weight of a `C²` test is `C¹` in its derivative. -/
theorem contDiff_one_deriv_lagTestWeight (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) : ContDiff ℝ 1 (deriv (lagTestWeight F)) := by
  have hd : deriv (lagTestWeight F)
      = fun s => 2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2) :=
    funext fun s => deriv_lagTestWeight hF hFc s
  rw [hd]
  exact (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul
    ((contDiff_one_crossCorrelation hF hF' hFc).sub
      ((contDiff_one_autoCorrelation hF hFc).div_const 2))

/-- **The second-order balance at the level of a test.** The prime channel and the pole plane of
a `C²` test, restricted to a band, are the curvature of the critical-scale receiver paired with
the test's own second-order lag weight. -/
theorem testBalance_band_receiver_curvature (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {s₁ : ℝ}
    (hs₁ : 0 < s₁) (hvan0 : ∀ s, s ≤ s₁ → lagTestWeight F s = 0) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) (α β : ℝ) :
    (∑ n ∈ Finset.filter (fun n : ℕ => s₁ < Real.log n) (Finset.range (N + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) * lagTestWeight F (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * lagTestWeight F s
      = -∫ s in Ioi (0:ℝ), (criticalScalePrefix s + s ^ 2 / 2 - s + (α * s + β)) *
          deriv (deriv (lagTestWeight F)) s := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  exact sum_vonMangoldt_band_eq_receiver_curvature (contDiff_one_lagTestWeight hF hFc)
    (contDiff_one_deriv_lagTestWeight hF hF' hFc) hS hvan hs₁ hvan0 hN α β


/-! ### The half-test obeys the ladder at half the aperture

For an odd test the right half is continuous and lives on `[0, r]`, a window of half the
diameter, so after centring it is a test of aperture `r/2` and the ladder applies to it with that
aperture.  The Gram matrix of the bipartite reduction — whose entries are the half-test's
autocorrelation at the lag differences — therefore decays by the ladder at `r/2`, twice as fast
as the full test's. -/

theorem autoCorrelation_translate (F : ℝ → ℝ) (c t : ℝ) :
    autoCorrelation (fun x => F (x + c)) t = autoCorrelation F t := by
  rw [autoCorrelation, autoCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => F y * F (y + t)) c
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + c) * F (x + t + c) = F (x + c) * F (x + c + t)
  rw [show x + t + c = x + c + t by ring]

theorem eq_zero_of_odd (hodd : ∀ x, F (-x) = -F x) : F 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

theorem continuous_rightPart_of_odd (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) :
    Continuous (rightPart F) := by
  have h0 : F 0 = 0 := eq_zero_of_odd hodd
  have heq : rightPart F = fun x => if (0:ℝ) ≤ x then F x else 0 := rfl
  rw [heq]
  exact Continuous.if_le hF continuous_const continuous_const continuous_id
    (fun x hx => by rw [← hx, h0])

/-- **The half-test ladder.** For an odd test of aperture `r` the right half obeys the ladder at
aperture `r/2`. -/
theorem autoCorrelation_rightPart_le_chainConstant (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hsupp : ∀ y, r < |y| → F y = 0) :
    autoCorrelation (rightPart F) t
      ≤ Real.cos (Real.pi / (chainRungs (r / 2) t : ℝ)) * autoCorrelation (rightPart F) 0 := by
  have hrc : Continuous (rightPart F) := continuous_rightPart_of_odd hF hodd
  set w : ℝ → ℝ := fun x => rightPart F (x + r / 2) with hw
  have hwc : Continuous w := hrc.comp (continuous_id.add continuous_const)
  have hwsupp : ∀ y, r / 2 < |y| → w y = 0 := by
    intro y hy
    show rightPart F (y + r / 2) = 0
    rcases lt_or_ge y 0 with hneg | hpos
    · have hy' : r / 2 < -y := by rwa [abs_of_neg hneg] at hy
      rw [rightPart, if_neg (not_le.mpr (by linarith : y + r / 2 < 0))]
    · have hy' : r / 2 < y := by rwa [abs_of_nonneg hpos] at hy
      rw [rightPart, if_pos (by linarith : (0:ℝ) ≤ y + r / 2)]
      exact hsupp _ (by rw [abs_of_pos (by linarith)]; linarith)
  have hwcs : HasCompactSupport w :=
    HasCompactSupport.intro (isCompact_Icc (a := -(r / 2)) (b := r / 2)) fun y hy => by
      refine hwsupp y ?_
      rcases not_and_or.mp (fun hc => hy (Set.mem_Icc.mpr hc)) with hc | hc
      · rw [abs_of_neg (by linarith [not_le.mp hc] : y < 0)]; linarith [not_le.mp hc]
      · rw [abs_of_pos (by linarith [not_le.mp hc] : 0 < y)]; linarith [not_le.mp hc]
  have hlad := autoCorrelation_le_chainConstant hwc hwcs (by linarith : (0:ℝ) < r / 2) ht hwsupp
  rwa [autoCorrelation_translate, autoCorrelation_translate] at hlad


/-! ### The Gram matrix of the bipartite reduction, bounded by the half-test ladder

Assembling: the bipartite reduction expresses the prime side beyond the aperture through the
Gram matrix of the half-test at the lag differences, and the half-test ladder bounds every
off-diagonal entry of that matrix.  The diagonal is the half-test's mass; every other entry is
damped by the ladder at aperture `r/2`. -/

/-- The half-test ladder for lags of either sign. -/
theorem autoCorrelation_rightPart_le_chainConstant_abs (hF : Continuous F)
    (hodd : ∀ x, F (-x) = -F x) {r t : ℝ} (hr : 0 < r) (ht : t ≠ 0)
    (hsupp : ∀ y, r < |y| → F y = 0) :
    autoCorrelation (rightPart F) t
      ≤ Real.cos (Real.pi / (chainRungs (r / 2) |t| : ℝ)) * autoCorrelation (rightPart F) 0 := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [← autoCorrelation_neg (rightPart F) t, abs_of_neg hneg]
    exact autoCorrelation_rightPart_le_chainConstant hF hodd hr (by linarith) hsupp
  · rw [abs_of_pos hpos]
    exact autoCorrelation_rightPart_le_chainConstant hF hodd hr hpos hsupp

/-- **The Gram bound.** Every entry of the bipartite Gram matrix is the half-test's mass on the
diagonal and ladder-damped off it. -/
theorem sum_gram_le_ladder (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {T : Finset ℕ} {c lag : ℕ → ℝ}
    (hc : ∀ n ∈ T, 0 ≤ c n) :
    ∑ n ∈ T, ∑ m ∈ T, c n * c m * autoCorrelation (rightPart F) (lag m - lag n)
      ≤ ∑ n ∈ T, ∑ m ∈ T, c n * c m *
          ((if lag m - lag n = 0 then (1:ℝ)
            else Real.cos (Real.pi / (chainRungs (r / 2) |lag m - lag n| : ℝ)))
            * autoCorrelation (rightPart F) 0) := by
  refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
  have hcc : 0 ≤ c n * c m := mul_nonneg (hc n hn) (hc m hm)
  refine mul_le_mul_of_nonneg_left ?_ hcc
  by_cases hz : lag m - lag n = 0
  · rw [if_pos hz, hz, one_mul]
  · rw [if_neg hz]
    exact autoCorrelation_rightPart_le_chainConstant_abs hF hodd hr hz hsupp


/-! ### Where the Gram damping bites

Two distinct integers below the horizon have logarithms separated by at least `1/N`, so most
lag differences of the prime side are far below the aperture and the ladder damps them not at
all.  The damping is effective exactly on the annulus `r/2 < |δ| ≤ r` of lag differences — prime
ratios between `e^{r/2}` and `e^{r}` — where the Gram entry is at most half the half-test's
mass.  That is the exact reach of the bipartite route, and it is where the cross-prime aggregate
can be improved without new arithmetic. -/

/-- **Logarithmic separation.** Distinct positive integers below `n` have logarithms at least
`1/n` apart. -/
theorem one_div_le_log_sub_log {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    1 / (n : ℝ) ≤ Real.log n - Real.log m := by
  have hn : (0:ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hmn
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hratio : (0:ℝ) < (m : ℝ) / n := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hm') (ne_of_gt hn)] at hlog
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have : (m : ℝ) / n ≤ 1 - 1 / n := by
    rw [div_le_iff₀ hn]
    field_simp
    linarith
  linarith

theorem chainRungs_eq_three {r δ : ℝ} (hr : 0 < r) (h1 : r / 2 < δ) (h2 : δ ≤ r) :
    chainRungs (r / 2) δ = 3 := by
  have hδ : 0 < δ := by linarith
  have hd1 : (1:ℝ) ≤ 2 * (r / 2) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hd2 : 2 * (r / 2) / δ < 2 := by
    rw [div_lt_iff₀ hδ]; linarith
  have : ⌊2 * (r / 2) / δ⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hd1
    · push_cast; linarith
  rw [chainRungs, this]
  norm_num

/-- On the annulus the Gram entry is at most half the half-test's mass. -/
theorem autoCorrelation_rightPart_le_half_of_annulus (hF : Continuous F)
    (hodd : ∀ x, F (-x) = -F x) {r t : ℝ} (hr : 0 < r) (h1 : r / 2 < t) (h2 : t ≤ r)
    (hsupp : ∀ y, r < |y| → F y = 0) :
    autoCorrelation (rightPart F) t ≤ autoCorrelation (rightPart F) 0 / 2 := by
  have ht : 0 < t := by linarith
  have hlad := autoCorrelation_rightPart_le_chainConstant hF hodd hr ht hsupp
  rw [chainRungs_eq_three hr h1 h2] at hlad
  have hcos : Real.cos (Real.pi / ((3:ℤ) : ℝ)) = 1 / 2 := by
    norm_num [Real.cos_pi_div_three]
  rw [hcos] at hlad
  linarith


/-! ### The arithmetic input: lag differences against integer differences

The Gram's remaining difficulty is the near-diagonal block, where the ladder does not act.  What
controls that block is the conversion between a lag difference and an integer difference: a small
lag difference forces the two integers to be close in the ordinary sense, by a factor equal to
their size.  On a dyadic window this says that the pairs contributing to the near-diagonal block
are those within `2Xδ` of each other. -/

/-- **Logarithmic separation, relative form.** -/
theorem sub_div_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have hb : (0:ℝ) < b := lt_of_lt_of_le ha hab
  have hratio : (0:ℝ) < a / b := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hlog
  have hdiv : a / b = 1 - (b - a) / b := by field_simp; ring
  rw [hdiv] at hlog
  linarith

/-- **A small lag difference forces a small integer difference.** -/
theorem abs_sub_le_of_abs_log_sub_le {a b M δ : ℝ} (ha : 0 < a) (hb : 0 < b) (haM : a ≤ M)
    (hbM : b ≤ M) (hδ : 0 ≤ δ) (hlog : |Real.log b - Real.log a| ≤ δ) :
    |b - a| ≤ M * δ := by
  rcases le_total a b with hab | hba
  · have hkey := sub_div_le_log_sub_log ha hab
    have hb0 : (0:ℝ) < b := hb
    have hle : Real.log b - Real.log a ≤ δ := le_trans (le_abs_self _) hlog
    have : (b - a) / b ≤ δ := le_trans hkey hle
    rw [div_le_iff₀ hb0] at this
    rw [abs_of_nonneg (by linarith)]
    nlinarith [hbM, hδ]
  · have hkey := sub_div_le_log_sub_log hb hba
    have ha0 : (0:ℝ) < a := ha
    have hle : Real.log a - Real.log b ≤ δ := by
      have := neg_le_of_abs_le hlog
      linarith
    have : (a - b) / a ≤ δ := le_trans hkey hle
    rw [div_le_iff₀ ha0] at this
    rw [abs_of_nonpos (by linarith)]
    nlinarith [haM, hδ]

/-- On a dyadic window a lag difference below `δ` means the integers are within `2Xδ`. -/
theorem abs_sub_le_of_dyadic_window {X : ℝ} (hX : 0 < X) {a b δ : ℝ} (ha1 : X < a)
    (ha2 : a ≤ 2 * X) (hb1 : X < b) (hb2 : b ≤ 2 * X) (hδ : 0 ≤ δ)
    (hlog : |Real.log b - Real.log a| ≤ δ) : |b - a| ≤ 2 * X * δ :=
  abs_sub_le_of_abs_log_sub_le (lt_trans hX ha1) (lt_trans hX hb1) ha2 hb2 hδ hlog


/-! ### Counting the near-diagonal block

The Gram's near-diagonal block is small: on a dyadic window, each row has at most
`2⌊2Xδ⌋ + 1` entries with lag gap below `δ`.  So the block the ladder cannot damp is a banded
matrix whose bandwidth is governed by the integer spacing, not by the number of atoms. -/

theorem card_lagClose_le {X : ℕ} {δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ) {n : ℕ}
    (hn : n ∈ Finset.Ioc X (2 * X)) :
    (Finset.filter (fun m : ℕ => |Real.log m - Real.log n| ≤ δ)
        (Finset.Ioc X (2 * X))).card
      ≤ 2 * ⌊2 * (X : ℝ) * δ⌋₊ + 1 := by
  classical
  set k : ℕ := ⌊2 * (X : ℝ) * δ⌋₊ with hk
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hsub : Finset.filter (fun m : ℕ => |Real.log m - Real.log n| ≤ δ)
      (Finset.Ioc X (2 * X)) ⊆ Finset.Icc (n - k) (n + k) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmlog⟩ := hm
    rw [Finset.mem_Ioc] at hn
    have hn1 : (X : ℝ) < n := by exact_mod_cast hn.1
    have hn2 : (n : ℝ) ≤ 2 * X := by exact_mod_cast hn.2
    have hm1' : (X : ℝ) < m := by exact_mod_cast hm1
    have hm2' : (m : ℝ) ≤ 2 * X := by exact_mod_cast hm2
    have habs := abs_sub_le_of_dyadic_window hXr hn1 hn2 hm1' hm2' hδ hmlog
    have hdist : ((if m ≤ n then n - m else m - n : ℕ) : ℝ) = |(m : ℝ) - n| := by
      by_cases hc : m ≤ n
      · rw [if_pos hc, Nat.cast_sub hc, abs_of_nonpos (by
          have : (m:ℝ) ≤ n := by exact_mod_cast hc
          linarith)]
        ring
      · rw [if_neg hc, Nat.cast_sub (le_of_lt (not_le.mp hc)), abs_of_nonneg (by
          have : (n:ℝ) ≤ m := by exact_mod_cast le_of_lt (not_le.mp hc)
          linarith)]
    have hle : (if m ≤ n then n - m else m - n : ℕ) ≤ k := by
      refine Nat.le_floor ?_
      rw [hdist]
      exact habs
    rw [Finset.mem_Icc]
    by_cases hc : m ≤ n
    · rw [if_pos hc] at hle
      exact ⟨by omega, by omega⟩
    · rw [if_neg hc] at hle
      exact ⟨by omega, by omega⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Icc]
  omega


/-! ### The Schur test for the bipartite Gram

A symmetric form with nonnegative weights is bounded by its largest absolute row sum times the
coefficient energy.  Applied to the bipartite Gram, this turns the prime side beyond the aperture
into an `ℓ²` statement: the atoms enter through `Σ c_n²`, and the only remaining datum is the
largest row sum of the half-test's correlations at the lag differences — a banded matrix with
ladder-damped tails by #31–#34. -/

/-- **The Schur test.** -/
theorem sum_mul_mul_le_rowSum {T : Finset ℕ} {c : ℕ → ℝ} {G : ℕ → ℕ → ℝ} {R : ℝ}
    (hc : ∀ n ∈ T, 0 ≤ c n) (hsym : ∀ n ∈ T, ∀ m ∈ T, |G n m| = |G m n|)
    (hR : ∀ n ∈ T, ∑ m ∈ T, |G n m| ≤ R) :
    ∑ n ∈ T, ∑ m ∈ T, c n * c m * G n m ≤ R * ∑ n ∈ T, c n ^ 2 := by
  have hstep : ∀ n ∈ T, ∀ m ∈ T,
      c n * c m * G n m ≤ (c n ^ 2 + c m ^ 2) / 2 * |G n m| := by
    intro n hn m hm
    have h1 : c n * c m * G n m ≤ c n * c m * |G n m| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hc n hn) (hc m hm))
    have h2 : c n * c m ≤ (c n ^ 2 + c m ^ 2) / 2 := by nlinarith [sq_nonneg (c n - c m)]
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  have hmain : ∑ n ∈ T, ∑ m ∈ T, c n * c m * G n m
      ≤ ∑ n ∈ T, ∑ m ∈ T, (c n ^ 2 + c m ^ 2) / 2 * |G n m| :=
    Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hstep n hn m hm
  have hsplit : ∑ n ∈ T, ∑ m ∈ T, (c n ^ 2 + c m ^ 2) / 2 * |G n m|
      = (∑ n ∈ T, ∑ m ∈ T, c n ^ 2 / 2 * |G n m|)
        + ∑ n ∈ T, ∑ m ∈ T, c m ^ 2 / 2 * |G n m| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hA : ∑ n ∈ T, ∑ m ∈ T, c n ^ 2 / 2 * |G n m| ≤ R / 2 * ∑ n ∈ T, c n ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [← Finset.mul_sum]
    have := hR n hn
    nlinarith [sq_nonneg (c n), this]
  have hB : ∑ n ∈ T, ∑ m ∈ T, c m ^ 2 / 2 * |G n m| ≤ R / 2 * ∑ n ∈ T, c n ^ 2 := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum]
    have hrow : ∑ n ∈ T, |G n m| ≤ R := by
      have := hR m hm
      calc ∑ n ∈ T, |G n m| = ∑ n ∈ T, |G m n| :=
            Finset.sum_congr rfl fun n hn => hsym n hn m hm
        _ ≤ R := this
    nlinarith [sq_nonneg (c m), hrow]
  have : (R / 2 * ∑ n ∈ T, c n ^ 2) + R / 2 * ∑ n ∈ T, c n ^ 2 = R * ∑ n ∈ T, c n ^ 2 := by
    ring
  linarith [hmain, hsplit ▸ hmain, hA, hB]

/-- **The `ℓ²` form of the prime side beyond the aperture.** -/
theorem two_mul_sum_lag_le_schur (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {T : Finset ℕ} {c lag : ℕ → ℝ}
    (hc : ∀ n ∈ T, 0 ≤ c n) (hlag : ∀ n ∈ T, r < lag n) {ε R : ℝ} (hε : 0 < ε)
    (hR : ∀ n ∈ T, ∑ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)| ≤ R) :
    2 * ∑ n ∈ T, c n * autoCorrelation F (lag n)
      ≤ ε * (∫ x, leftPart F x ^ 2) + ε⁻¹ * (R * ∑ n ∈ T, c n ^ 2) := by
  have hsym : ∀ n ∈ T, ∀ m ∈ T,
      |autoCorrelation (rightPart F) (lag m - lag n)|
        = |autoCorrelation (rightPart F) (lag n - lag m)| := by
    intro n _ m _
    rw [show lag n - lag m = -(lag m - lag n) by ring, autoCorrelation_neg]
  have hschur := sum_mul_mul_le_rowSum (T := T) (c := c)
    (G := fun n m => autoCorrelation (rightPart F) (lag m - lag n)) (R := R) hc hsym hR
  have hbip := two_mul_sum_lag_le_bipartite (c := c) hF hFc hsupp hlag hε
  have hεinv : 0 < ε⁻¹ := by positivity
  nlinarith [hbip, hschur, hεinv]


/-! ### The row sum, and the replacement hypothesis

The row sums of the bipartite Gram are supported on the lag-gap ball of radius `r`, so the Schur
constant is the half-test's mass times the bandwidth.  Because the ladder is one-sided it does
not shrink an *absolute* row sum, so the honest conclusion is a replacement hypothesis: a power
saving over the `ℓ¹` cost is equivalent to a bounded Schur constant for the prime-ratio
correlations, and nothing weaker about the test can supply it. -/

theorem hasCompactSupport_rightPart {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport (rightPart F) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := r)) fun y hy => ?_
  rcases not_and_or.mp (fun hc => hy (Set.mem_Icc.mpr hc)) with hc | hc
  · rw [rightPart, if_neg (by exact hc)]
  · rw [rightPart]
    by_cases h0 : (0:ℝ) ≤ y
    · rw [if_pos h0, hsupp y (by rw [abs_of_nonneg h0]; exact not_le.mp hc)]
    · rw [if_neg h0]

/-- **The row sum is carried by the lag-gap ball of radius `r`.** -/
theorem rowSum_le_bandwidth (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (T : Finset ℕ) (lag : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)|
      ≤ autoCorrelation (rightPart F) 0 *
          ((Finset.filter (fun m : ℕ => |lag m - lag n| ≤ r) T).card : ℝ) := by
  classical
  have hrc : Continuous (rightPart F) := continuous_rightPart_of_odd hF hodd
  have hrcs : HasCompactSupport (rightPart F) := hasCompactSupport_rightPart hsupp
  have hterm : ∀ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)|
      ≤ (if |lag m - lag n| ≤ r then autoCorrelation (rightPart F) 0 else 0) := by
    intro m _
    by_cases hc : |lag m - lag n| ≤ r
    · rw [if_pos hc]
      exact abs_autoCorrelation_le hrc hrcs _
    · rw [if_neg hc,
        autoCorrelation_rightPart_eq_zero hsupp (not_le.mp hc), abs_zero]
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The replacement hypothesis, proved sufficient.** A bounded Schur constant for the
prime-ratio correlations turns the prime side beyond the aperture into an `ℓ²` bound. -/
theorem two_mul_sum_lag_le_of_schurConstant (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) {T : Finset ℕ} {c lag : ℕ → ℝ}
    (hc : ∀ n ∈ T, 0 ≤ c n) (hlag : ∀ n ∈ T, r < lag n) {κ : ℝ}
    (hκ : ∀ n ∈ T, ∑ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)|
        ≤ κ * autoCorrelation (rightPart F) 0) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ n ∈ T, c n * autoCorrelation F (lag n)
      ≤ ε * (∫ x, leftPart F x ^ 2)
        + ε⁻¹ * (κ * autoCorrelation (rightPart F) 0 * ∑ n ∈ T, c n ^ 2) :=
  two_mul_sum_lag_le_schur hF hFc hsupp hc hlag hε hκ


/-! ### The Gram is multiplicatively Toeplitz

A lag difference of two atoms is the logarithm of their ratio, and two pairs give the same lag
difference exactly when they give the same ratio.  The bipartite Gram is therefore a function of
the *ratio* alone — the incidence structure of the integers read by the form — so its entries are
indexed by rationals and its multiplicities by the divisor structure of the window. -/

/-- Two pairs have the same lag difference exactly when they have the same ratio. -/
theorem log_sub_log_eq_iff {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.log a - Real.log b = Real.log c - Real.log d ↔ a * d = c * b := by
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  rw [← Real.log_div (ne_of_gt ha') (ne_of_gt hb'), ← Real.log_div (ne_of_gt hc') (ne_of_gt hd')]
  constructor
  · intro hlog
    have hpos1 : (0:ℝ) < (a : ℝ) / b := by positivity
    have hpos2 : (0:ℝ) < (c : ℝ) / d := by positivity
    have heq : (a : ℝ) / b = (c : ℝ) / d := by
      have h1 := Real.exp_log hpos1
      have h2 := Real.exp_log hpos2
      rw [← h1, ← h2, hlog]
    rw [div_eq_div_iff (ne_of_gt hb') (ne_of_gt hd')] at heq
    exact_mod_cast heq
  · intro hmul
    have heq : (a : ℝ) / b = (c : ℝ) / d := by
      rw [div_eq_div_iff (ne_of_gt hb') (ne_of_gt hd')]
      exact_mod_cast hmul
    rw [heq]

/-- **The Gram depends only on the ratio.** -/
theorem autoCorrelation_rightPart_ratio_eq {m n m' n' : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hm' : 0 < m') (hn' : 0 < n') (hratio : m * n' = m' * n) :
    autoCorrelation (rightPart F) (Real.log m - Real.log n)
      = autoCorrelation (rightPart F) (Real.log m' - Real.log n') := by
  rw [(log_sub_log_eq_iff hm hn hm' hn').mpr hratio]


/-! ### The multiplicity of a ratio

Since the Gram depends only on the ratio, its total weight is organised by multiplicity: the
pairs of a window realising a reduced ratio `a/b` are exactly the multiples `(ka, kb)`, so a
ratio of height `max(a,b)` occurs at most `Y / max(a,b)` times below `Y`.  The Gram's mass
therefore concentrates on ratios of small height — the divisor structure of the window controls
the bilinear form. -/

/-- **The ratio parametrisation.** Pairs with a given reduced ratio are the multiples of it. -/
theorem ratio_param {a b n m : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (h : n * b = m * a) :
    ∃ k, n = k * a ∧ m = k * b := by
  have hdvdnb : a ∣ n * b := ⟨m, by rw [h]; ring⟩
  have hdvd : a ∣ n := (Nat.Coprime.dvd_of_dvd_mul_right hab hdvdnb)
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, by rw [hk]; ring, ?_⟩
  have hcancel : a * (k * b) = a * m := by
    rw [hk] at h
    calc a * (k * b) = a * k * b := by ring
      _ = m * a := h
      _ = a * m := by ring
  exact (Nat.eq_of_mul_eq_mul_left ha hcancel).symm

/-- A reduced ratio of height `a` occurs at most `Y / a` times below `Y`: the first coordinates
of the pairs realising it are multiples of `a`. -/
theorem card_ratioFirsts_le {a b Y : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (S : Finset ℕ)
    (hS : ∀ n ∈ S, ∃ m, n * b = m * a) (hSY : ∀ n ∈ S, 1 ≤ n ∧ n ≤ Y) :
    S.card ≤ Y / a := by
  classical
  have hsub : S ⊆ Finset.image (fun k => k * a) (Finset.Icc 1 (Y / a)) := by
    intro n hn
    obtain ⟨m, hnm⟩ := hS n hn
    obtain ⟨hn1, hn2⟩ := hSY n hn
    obtain ⟨k, hk, -⟩ := ratio_param hab ha hnm
    refine Finset.mem_image.mpr ⟨k, ?_, hk.symm⟩
    rw [Finset.mem_Icc]
    constructor
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso; rw [h0, zero_mul] at hk; omega
      · exact h0
    · rw [Nat.le_div_iff_mul_le ha]
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans Finset.card_image_le (by simp [Nat.card_Icc])


/-! ### The optimised `ℓ²` bound

Optimising the free parameter of the bipartite split turns the two-term estimate into a single
geometric mean: the prime side beyond the aperture is at most the geometric mean of the left
half's mass and the Schur constant times the coefficient energy. -/

/-- Optimising a two-term bound over its free parameter. -/
theorem le_sqrt_mul_of_two_mul_le {P A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ ε : ℝ, 0 < ε → 2 * P ≤ ε * A + ε⁻¹ * B) : P ≤ Real.sqrt (A * B) := by
  rcases le_or_gt P 0 with hP | hP
  · exact le_trans hP (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · exfalso
    have hspec := h (B / (2 * P) + 1) (by positivity)
    rw [← hA0, mul_zero, zero_add] at hspec
    have hεpos : (0:ℝ) < B / (2 * P) + 1 := by positivity
    rw [inv_mul_eq_div] at hspec
    have hlt : B / (B / (2 * P) + 1) < 2 * P := by
      rw [div_lt_iff₀ hεpos]
      have hexp : 2 * P * (B / (2 * P) + 1) = B + 2 * P := by field_simp
      rw [hexp]
      linarith
    linarith
  · have hεpos : (0:ℝ) < P / A := by positivity
    have hspec := h (P / A) hεpos
    rw [inv_div] at hspec
    have hkey : P ^ 2 ≤ A * B := by
      have hmul : (P / A) * A = P := by field_simp
      have hmul2 : (A / P) * B = A * B / P := by field_simp
      rw [hmul, hmul2] at hspec
      rw [← sub_nonneg] at hspec
      have : 0 ≤ A * B / P - P := by linarith
      rw [sub_nonneg, le_div_iff₀ hP] at this
      nlinarith [this]
    exact (Real.le_sqrt hP.le (mul_nonneg hA hB)).mpr hkey

/-- **The optimised bipartite bound.** -/
theorem sum_lag_le_sqrt (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {T : Finset ℕ} {c lag : ℕ → ℝ}
    (hc : ∀ n ∈ T, 0 ≤ c n) (hlag : ∀ n ∈ T, r < lag n) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ n ∈ T, ∑ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)| ≤ R) :
    ∑ n ∈ T, c n * autoCorrelation F (lag n)
      ≤ Real.sqrt ((∫ x, leftPart F x ^ 2) * (R * ∑ n ∈ T, c n ^ 2)) := by
  refine le_sqrt_mul_of_two_mul_le ?_ ?_ fun ε hε => ?_
  · exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  · exact mul_nonneg hR0 (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact two_mul_sum_lag_le_schur hF hFc hsupp hc hlag hε hR


/-! ### Dilating the test is a change of source

Dilating a test by `λ` rescales its autocorrelation and moves the lags: the dilated test reads
the original one at the lags `λ log n = log n^λ`.  So a dilation of the test is exactly a passage
to the Beurling system whose generalised primes are the `λ`-th powers of the ordinary ones — and
by source rigidity that system has a different defect.  Dilation invariance of a positivity
statement would therefore be a statement about a whole family of sources, not about `ζ`. -/

/-- **The dilation law for the autocorrelation.** -/
theorem autoCorrelation_dilate {lam : ℝ} (hlam : 0 < lam) (F : ℝ → ℝ) (t : ℝ) :
    autoCorrelation (fun x => F (lam * x)) t = lam⁻¹ * autoCorrelation F (lam * t) := by
  rw [autoCorrelation, autoCorrelation]
  have hstep : (∫ x, F (lam * x) * F (lam * (x + t)))
      = ∫ x, (fun y => F y * F (y + lam * t)) (lam * x) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F (lam * x) * F (lam * (x + t)) = F (lam * x) * F (lam * x + lam * t)
    rw [show lam * (x + t) = lam * x + lam * t by ring]
  rw [hstep, MeasureTheory.Measure.integral_comp_mul_left
      (fun y => F y * F (y + lam * t)) lam, abs_of_pos (inv_pos.mpr hlam), smul_eq_mul]

/-- The dilated test's prime side reads the original test at the dilated lags. -/
theorem sum_lag_dilate {lam : ℝ} (hlam : 0 < lam) (F : ℝ → ℝ) (T : Finset ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ T, c n * autoCorrelation (fun x => F (lam * x)) (Real.log n)
      = lam⁻¹ * ∑ n ∈ T, c n * autoCorrelation F (lam * Real.log n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autoCorrelation_dilate hlam]
  ring

/-- The dilated lags are the logarithms of the generalised primes `n^λ`. -/
theorem lam_mul_log_eq_log_rpow {lam : ℝ} {n : ℕ} (hn : 0 < n) :
    lam * Real.log n = Real.log ((n : ℝ) ^ lam) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.log_rpow hn']


/-! ### The lag Gram form is a square

The full Gram form of a family of atoms is the squared norm of the superposition
`∑ cₙ F(· + tₙ)`, so it is nonnegative for every family of atoms, weights and lags — no arithmetic
input enters.  Positivity of the arithmetic side alone is therefore automatic, and all the content
of a positivity statement sits in the comparison with the polar side.  Splitting off the diagonal
turns the identity into the sharp lower bound `-A(0)·∑ cₙ²` for the off-diagonal sum, the exact
counterpart of the ladder and Schur upper bounds. -/

theorem integrable_shift_mul (hF : Continuous F) (hFc : HasCompactSupport F) (a b : ℝ) :
    Integrable fun x => F (x + a) * F (x + b) := by
  have h : Integrable fun x => F x * F (x + (b - a)) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  refine (h.comp_add_right a).congr (Filter.Eventually.of_forall fun x => ?_)
  show F (x + a) * F (x + a + (b - a)) = F (x + a) * F (x + b)
  rw [show x + a + (b - a) = x + b by ring]

theorem integral_shift_mul (a b : ℝ) :
    (∫ x, F (x + a) * F (x + b)) = autoCorrelation F (b - a) := by
  rw [autoCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => F y * F (y + (b - a))) a
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + a) * F (x + b) = F (x + a) * F (x + a + (b - a))
  rw [show x + a + (b - a) = x + b by ring]

/-- **The Gram form is a square.**  The double lag sum is the energy of the superposition. -/
theorem sum_gram_eq_integral_sq (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c t : ℕ → ℝ) :
    ∑ m ∈ T, ∑ n ∈ T, c m * c n * autoCorrelation F (t n - t m)
      = ∫ x, (∑ n ∈ T, c n * F (x + t n)) ^ 2 := by
  have hint2 : ∀ m : ℕ, ∀ n ∈ T,
      Integrable fun x => c m * c n * (F (x + t m) * F (x + t n)) :=
    fun m n _ => (integrable_shift_mul hF hFc (t m) (t n)).const_mul (c m * c n)
  have hint : ∀ m ∈ T,
      Integrable fun x => ∑ n ∈ T, c m * c n * (F (x + t m) * F (x + t n)) :=
    fun m _ => MeasureTheory.integrable_finsetSum T (hint2 m)
  have hexp : ∀ x : ℝ, (∑ n ∈ T, c n * F (x + t n)) ^ 2
      = ∑ m ∈ T, ∑ n ∈ T, c m * c n * (F (x + t m) * F (x + t n)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_finsetSum T hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_finsetSum T (hint2 m)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_shift_mul]

/-- The lag Gram form is nonnegative for every family of weights and lags. -/
theorem sum_gram_nonneg (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c t : ℕ → ℝ) :
    0 ≤ ∑ m ∈ T, ∑ n ∈ T, c m * c n * autoCorrelation F (t n - t m) := by
  rw [sum_gram_eq_integral_sq hF hFc]
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- Splitting the Gram form into its diagonal and its off-diagonal part. -/
theorem sum_gram_split (T : Finset ℕ) (c t : ℕ → ℝ) :
    ∑ m ∈ T, ∑ n ∈ T, c m * c n * autoCorrelation F (t n - t m)
      = autoCorrelation F 0 * ∑ m ∈ T, c m ^ 2
        + ∑ m ∈ T, ∑ n ∈ T.erase m, c m * c n * autoCorrelation F (t n - t m) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.add_sum_erase T _ hm]
  congr 1
  rw [sub_self]
  ring

/-- **The sharp lower bound for the off-diagonal lag sum.**  No arrangement of atoms can drive the
off-diagonal part below minus the diagonal energy. -/
theorem sum_gram_offDiag_ge (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c t : ℕ → ℝ) :
    -(autoCorrelation F 0 * ∑ m ∈ T, c m ^ 2)
      ≤ ∑ m ∈ T, ∑ n ∈ T.erase m, c m * c n * autoCorrelation F (t n - t m) := by
  have h := sum_gram_nonneg hF hFc T c t
  rw [sum_gram_split] at h
  linarith


/-! ### The displacement energy and its triangle law

`D(t) = A(0) − A(t)` is half the squared `L²` distance between a test and its translate, so it is
the square of a translation-invariant metric.  Subadditivity of that metric gives
`D(s+t) ≤ 2D(s) + 2D(t)`, and hence `D(2t) ≤ 4D(t)`: a test that is almost translation-invariant
at a lag is almost translation-invariant at twice the lag.  Read backwards, a lower bound on `D`
at a large lag forces a lower bound at every smaller dyadic lag, which is exactly what the
one-sided aperture law cannot supply by itself: the half law past the aperture now yields a
nontrivial gap at *half* the aperture, where no overlap argument applies. -/

/-- The displacement energy of a test at a lag. -/
def displacement (F : ℝ → ℝ) (t : ℝ) : ℝ := autoCorrelation F 0 - autoCorrelation F t

theorem autoCorrelation_zero_eq (F : ℝ → ℝ) : autoCorrelation F 0 = ∫ x, F x ^ 2 := by
  rw [autoCorrelation]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F x * F (x + 0) = F x ^ 2
  rw [add_zero, sq]

theorem integral_shift_sq (F : ℝ → ℝ) (t : ℝ) : (∫ x, F (x + t) ^ 2) = autoCorrelation F 0 := by
  rw [autoCorrelation_zero_eq]
  exact MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => F y ^ 2) t

theorem integrable_sq (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable fun x => F x ^ 2 :=
  ((hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right).congr
    (Filter.Eventually.of_forall fun _ => (sq _).symm)

theorem integrable_diff_sq (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    Integrable fun x => (F x - F (x + t)) ^ 2 := by
  have hc : Continuous fun x => F x - F (x + t) :=
    hF.sub (hF.comp (continuous_id.add continuous_const))
  have hs : HasCompactSupport fun x => F x - F (x + t) :=
    hFc.sub (hFc.comp_homeomorph (Homeomorph.addRight t))
  exact ((hc.mul hc).integrable_of_hasCompactSupport hs.mul_right).congr
    (Filter.Eventually.of_forall fun _ => (sq _).symm)

/-- **The displacement energy is half the squared distance to the translate.** -/
theorem two_mul_displacement_eq (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    2 * displacement F t = ∫ x, (F x - F (x + t)) ^ 2 := by
  have hsq := integrable_sq hF hFc
  have hsqt : Integrable fun x => F (x + t) ^ 2 := by
    simpa using hsq.comp_add_right t
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hexp : ∀ x : ℝ, (F x - F (x + t)) ^ 2
      = F x ^ 2 - 2 * (F x * F (x + t)) + F (x + t) ^ 2 := fun x => by ring
  have hpc : Integrable fun x => 2 * (F x * F (x + t)) := hprod.const_mul 2
  have hdiff : Integrable fun x => F x ^ 2 - 2 * (F x * F (x + t)) := hsq.sub hpc
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_add hdiff hsqt, MeasureTheory.integral_sub hsq hpc,
    MeasureTheory.integral_const_mul, integral_shift_sq]
  have ht : (∫ x, F x * F (x + t)) = autoCorrelation F t := rfl
  rw [← autoCorrelation_zero_eq, ht, displacement]
  ring

theorem displacement_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    0 ≤ displacement F t := by
  have he := two_mul_displacement_eq hF hFc t
  have hi : (0:ℝ) ≤ ∫ x, (F x - F (x + t)) ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  linarith

/-- **The triangle law for the displacement energy.** -/
theorem displacement_add_le (hF : Continuous F) (hFc : HasCompactSupport F) (s t : ℝ) :
    displacement F (s + t) ≤ 2 * displacement F s + 2 * displacement F t := by
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => (F y - F (y + t)) ^ 2) s
  have hvi : Integrable fun x => (F (x + s) - F (x + s + t)) ^ 2 := by
    simpa using (integrable_diff_sq hF hFc t).comp_add_right s
  have hpt : ∀ x : ℝ, (F x - F (x + (s + t))) ^ 2
      ≤ 2 * (F x - F (x + s)) ^ 2 + 2 * (F (x + s) - F (x + s + t)) ^ 2 := by
    intro x
    rw [show x + (s + t) = x + s + t by ring]
    nlinarith [sq_nonneg (F x - 2 * F (x + s) + F (x + s + t))]
  have hu2 : Integrable fun x => 2 * (F x - F (x + s)) ^ 2 :=
    (integrable_diff_sq hF hFc s).const_mul 2
  have hv2 : Integrable fun x => 2 * (F (x + s) - F (x + s + t)) ^ 2 := hvi.const_mul 2
  have hsum : Integrable fun x =>
      2 * (F x - F (x + s)) ^ 2 + 2 * (F (x + s) - F (x + s + t)) ^ 2 := hu2.add hv2
  have hmono := MeasureTheory.integral_mono (integrable_diff_sq hF hFc (s + t)) hsum hpt
  rw [MeasureTheory.integral_add hu2 hv2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hshift] at hmono
  have e1 := two_mul_displacement_eq hF hFc (s + t)
  have e2 := two_mul_displacement_eq hF hFc s
  have e3 := two_mul_displacement_eq hF hFc t
  linarith

/-- Doubling a lag multiplies the displacement energy by at most four. -/
theorem displacement_two_mul_le (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    displacement F (2 * t) ≤ 4 * displacement F t := by
  have h := displacement_add_le hF hFc t t
  rw [show t + t = 2 * t by ring] at h
  linarith

/-- The doubling law in terms of the autocorrelation. -/
theorem autoCorrelation_two_mul_ge (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    4 * autoCorrelation F t - 3 * autoCorrelation F 0 ≤ autoCorrelation F (2 * t) := by
  have h := displacement_two_mul_le hF hFc t
  simp only [displacement] at h
  linarith

/-- **A gap at half the aperture.**  Past the aperture the half law forces `D ≥ A(0)/2`; the
triangle law transports that gap down to half the aperture, where no overlap argument applies:
the autocorrelation there is at most `7/8` of the mass. -/
theorem autoCorrelation_le_seven_eighths (hF : Continuous F) (hFc : HasCompactSupport F)
    {r t : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < 2 * t) :
    autoCorrelation F t ≤ 7 * autoCorrelation F 0 / 8 := by
  have hhalf := autoCorrelation_le_half hF hFc hsupp ht
  have hdbl := autoCorrelation_two_mul_ge hF hFc t
  linarith


/-! ### Dyadic transport of the aperture gap

Iterating the doubling law gives `D(2ʲt) ≤ 4ʲ D(t)`, the exact square scaling along the dyadic
multiples of a lag.  Running it against the half law transports the gap past the aperture down to
*every* positive lag: at a lag `u` the autocorrelation is bounded away from the full mass by an
explicit factor depending only on how many doublings separate `u` from the aperture.  Below the
aperture no overlap argument gives anything, so this is the first quantitative statement there. -/

/-- Square scaling of the displacement energy along dyadic multiples of a lag. -/
theorem displacement_two_pow_le (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    ∀ j : ℕ, displacement F (2 ^ j * t) ≤ 4 ^ j * displacement F t := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := displacement_two_mul_le hF hFc (2 ^ j * t)
      have hre : (2:ℝ) ^ (j + 1) * t = 2 * (2 ^ j * t) := by ring
      have hpow : (4:ℝ) ^ (j + 1) = 4 * 4 ^ j := by ring
      rw [hre, hpow]
      linarith

/-- **A gap at every positive lag.**  If `u` reaches past the aperture after `j` doublings, the
autocorrelation at `u` falls short of the full mass by at least `1/(2·4ʲ)` of it. -/
theorem autoCorrelation_le_of_two_pow (hF : Continuous F) (hFc : HasCompactSupport F)
    {r u : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) {j : ℕ} (hj : r < 2 ^ j * u) :
    autoCorrelation F u ≤ autoCorrelation F 0 * (1 - 1 / (2 * 4 ^ j)) := by
  have hhalf := autoCorrelation_le_half hF hFc hsupp hj
  have hscale := displacement_two_pow_le hF hFc u j
  simp only [displacement] at hscale
  rw [mul_sub, mul_one, mul_one_div, le_sub_iff_add_le]
  have h1 : autoCorrelation F 0
      ≤ (autoCorrelation F 0 - autoCorrelation F u) * (2 * 4 ^ j) := by linarith
  have h2 : autoCorrelation F 0 / (2 * 4 ^ j) ≤ autoCorrelation F 0 - autoCorrelation F u :=
    (div_le_iff₀ (by positivity : (0:ℝ) < 2 * 4 ^ j)).mpr h1
  linarith

/-- Every positive lag is reached from the aperture by finitely many doublings, so the
autocorrelation is bounded away from the full mass at every positive lag. -/
theorem exists_gap_of_pos (hF : Continuous F) (hFc : HasCompactSupport F)
    {r u : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (hu : 0 < u) :
    ∃ j : ℕ, autoCorrelation F u ≤ autoCorrelation F 0 * (1 - 1 / (2 * 4 ^ j)) := by
  obtain ⟨j, hjr⟩ := pow_unbounded_of_one_lt (r / u) (by norm_num : (1:ℝ) < 2)
  exact ⟨j, autoCorrelation_le_of_two_pow hF hFc hsupp
    ((div_lt_iff₀ hu).mp hjr)⟩


/-! ### The quadratic aperture gap

Chaining `k` unit steps instead of doubling gives the sharp square law `D(kt) ≤ k²D(t)`, because
the displacement telescopes along the chain and the finite Cauchy–Schwarz inequality costs exactly
the length.  Against the half law this bounds the normalised autocorrelation of *any* test of
aperture `r` by `1 − u²/(8r²)` at every lag `0 < u ≤ r`: the translate family of a compactly
supported test has a universal quadratic spectral gap, with no hypothesis beyond the aperture. -/

theorem integrable_diff_sq_shift (hF : Continuous F) (hFc : HasCompactSupport F) (a t : ℝ) :
    Integrable fun x => (F (x + a) - F (x + a + t)) ^ 2 := by
  simpa using (integrable_diff_sq hF hFc t).comp_add_right a

theorem integral_diff_sq_shift (hF : Continuous F) (hFc : HasCompactSupport F) (a t : ℝ) :
    (∫ x, (F (x + a) - F (x + a + t)) ^ 2) = 2 * displacement F t := by
  rw [two_mul_displacement_eq hF hFc t]
  exact MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => (F y - F (y + t)) ^ 2) a

/-- **The square law for the displacement energy.**  Telescoping the displacement along a chain of
`k` equal steps and paying the finite Cauchy–Schwarz cost gives exactly the square of the length. -/
theorem displacement_nat_mul_le (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) (k : ℕ) :
    displacement F (k * t) ≤ k ^ 2 * displacement F t := by
  have hpt : ∀ x : ℝ, (F x - F (x + k * t)) ^ 2
      ≤ k * ∑ i ∈ Finset.range k, (F (x + i * t) - F (x + i * t + t)) ^ 2 := by
    intro x
    have hcong : ∀ i ∈ Finset.range k,
        F (x + (i : ℝ) * t) - F (x + ((i : ℕ) + 1 : ℕ) * t)
          = F (x + (i : ℝ) * t) - F (x + (i : ℝ) * t + t) := by
      intro i _
      push_cast
      rw [show x + ((i : ℝ) + 1) * t = x + (i : ℝ) * t + t by ring]
    have htel : ∑ i ∈ Finset.range k, (F (x + (i : ℝ) * t) - F (x + (i : ℝ) * t + t))
        = F x - F (x + k * t) := by
      rw [← Finset.sum_congr rfl hcong,
        Finset.sum_range_sub' (fun i : ℕ => F (x + (i : ℝ) * t)) k]
      norm_num
    rw [← htel]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
      (f := fun i : ℕ => F (x + (i : ℝ) * t) - F (x + (i : ℝ) * t + t))
    simpa using hcs
  have hint_sum : Integrable fun x =>
      ∑ i ∈ Finset.range k, (F (x + (i : ℝ) * t) - F (x + (i : ℝ) * t + t)) ^ 2 :=
    MeasureTheory.integrable_finsetSum _
      (fun i _ => integrable_diff_sq_shift hF hFc ((i : ℝ) * t) t)
  have hmono := MeasureTheory.integral_mono (integrable_diff_sq hF hFc ((k : ℝ) * t))
    (hint_sum.const_mul (k : ℝ)) hpt
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum (Finset.range k)
      (fun i _ => integrable_diff_sq_shift hF hFc ((i : ℝ) * t) t)] at hmono
  simp only [integral_diff_sq_shift hF hFc, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hmono
  have e1 := two_mul_displacement_eq hF hFc ((k : ℝ) * t)
  nlinarith [hmono, e1]

theorem autoCorrelation_zero_nonneg (F : ℝ → ℝ) : 0 ≤ autoCorrelation F 0 := by
  rw [autoCorrelation_zero_eq]
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- The aperture gap transported down a chain of `k` equal steps. -/
theorem autoCorrelation_le_of_nat_mul (hF : Continuous F) (hFc : HasCompactSupport F)
    {r u : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) {k : ℕ} (hk : r < k * u) :
    autoCorrelation F u ≤ autoCorrelation F 0 * (1 - 1 / (2 * k ^ 2)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have := le_of_abs_le (abs_autoCorrelation_le hF hFc u)
    simpa using this
  have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
  have hhalf := autoCorrelation_le_half hF hFc hsupp hk
  have hscale := displacement_nat_mul_le hF hFc u k
  simp only [displacement] at hscale
  rw [mul_sub, mul_one, mul_one_div, le_sub_iff_add_le]
  have h1 : autoCorrelation F 0
      ≤ (autoCorrelation F 0 - autoCorrelation F u) * (2 * (k : ℝ) ^ 2) := by linarith
  have h2 : autoCorrelation F 0 / (2 * (k : ℝ) ^ 2)
      ≤ autoCorrelation F 0 - autoCorrelation F u :=
    (div_le_iff₀ (by positivity : (0:ℝ) < 2 * (k : ℝ) ^ 2)).mpr h1
  linarith

/-- **The universal quadratic gap.**  For every test of aperture `r` and every lag `0 < u ≤ r`,
the normalised autocorrelation is at most `1 − u²/(8r²)`. -/
theorem autoCorrelation_le_quadratic (hF : Continuous F) (hFc : HasCompactSupport F)
    {r u : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (hu : 0 < u) (hur : u ≤ r) :
    autoCorrelation F u ≤ autoCorrelation F 0 * (1 - u ^ 2 / (8 * r ^ 2)) := by
  have hr : 0 < r := lt_of_lt_of_le hu hur
  set k : ℕ := ⌊r / u⌋₊ + 1 with hkdef
  have hkR : (k : ℝ) = (⌊r / u⌋₊ : ℝ) + 1 := by rw [hkdef]; push_cast; ring
  have hone : (1:ℝ) ≤ r / u := (one_le_div hu).mpr hur
  have hgt : r / u < (k : ℝ) := by rw [hkR]; exact Nat.lt_floor_add_one (r / u)
  have hk : r < (k : ℝ) * u := by
    rw [← div_lt_iff₀ hu]; exact hgt
  have hle : (k : ℝ) ≤ 2 * (r / u) := by
    have := Nat.floor_le (le_trans zero_le_one hone)
    rw [hkR]; linarith
  have hkpos : (0:ℝ) < (k : ℝ) := by rw [hkR]; positivity
  have hmain := autoCorrelation_le_of_nat_mul hF hFc hsupp hk
  have hA0 := autoCorrelation_zero_nonneg F
  have hku : (k : ℝ) * u ≤ 2 * r := by
    have : (k : ℝ) * u ≤ 2 * (r / u) * u := by nlinarith
    rwa [show 2 * (r / u) * u = 2 * r by field_simp] at this
  have hsq : ((k : ℝ) * u) ^ 2 ≤ (2 * r) ^ 2 := by nlinarith [mul_pos hkpos hu]
  have hfrac : u ^ 2 / (8 * r ^ 2) ≤ 1 / (2 * (k : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq]
  have hstep : autoCorrelation F 0 * (1 - 1 / (2 * (k : ℝ) ^ 2))
      ≤ autoCorrelation F 0 * (1 - u ^ 2 / (8 * r ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    linarith
  linarith


/-! ### The cross-prime aggregate

The cross-prime aggregate `Σ_{p ≠ q} w_p w_q A(log(q/p))` is the off-diagonal part of the Gram form
of the prime field `Φ(x) = Σ_p w_p F(x + log p)`, so it is the mean square of the prime Dirichlet
polynomial against the test's spectral measure minus its diagonal.  Two consequences come for free
from the square: the aggregate can never fall below minus the diagonal energy, so no cancellation
can make it exponentially negative; and for nonnegative weights the weighted Cauchy–Schwarz
inequality bounds it above by `A(0)((Σ_p w_p)² − Σ_p w_p²)`.  The upper bound is governed entirely
by the `ℓ¹` norm of the weight family: for the first-power Euler weights `log p/(p−1)` on
`p ≤ e^{2r}`, Mertens makes that norm `2r + O(1)`, so the aggregate is `O(r²)A(0)` — polynomial.
It is the half-power family `√p log p/(p−1)`, whose `ℓ¹` norm is exponential while its `ℓ²` norm
stays polynomial, for which the question is open. -/

/-- The prime field of a weight family: the superposition of translates of the test. -/
def primeField (F : ℝ → ℝ) (w : ℕ → ℝ) (P : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ P, w p * F (x + Real.log p)

theorem integrable_primeField_sq (hF : Continuous F) (hFc : HasCompactSupport F)
    (P : Finset ℕ) (w : ℕ → ℝ) : Integrable fun x => primeField F w P x ^ 2 := by
  have hexp : ∀ x : ℝ, (∑ m ∈ P, ∑ n ∈ P,
        w m * w n * (F (x + Real.log m) * F (x + Real.log n))) = primeField F w P x ^ 2 := by
    intro x
    rw [primeField, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  exact (MeasureTheory.integrable_finsetSum P fun m _ =>
    MeasureTheory.integrable_finsetSum P fun n _ =>
      (integrable_shift_mul hF hFc (Real.log m) (Real.log n)).const_mul (w m * w n)).congr
    (Filter.Eventually.of_forall hexp)

/-- **The aggregate is the mean square of the prime field minus its diagonal.** -/
theorem crossAggregate_eq_meanSquare (hF : Continuous F) (hFc : HasCompactSupport F)
    (P : Finset ℕ) (w : ℕ → ℝ) :
    ∑ p ∈ P, ∑ q ∈ P.erase p, w p * w q * autoCorrelation F (Real.log q - Real.log p)
      = (∫ x, primeField F w P x ^ 2) - autoCorrelation F 0 * ∑ p ∈ P, w p ^ 2 := by
  have hgram := sum_gram_eq_integral_sq hF hFc P w (fun n => Real.log n)
  have hsplit := sum_gram_split (F := F) P w (fun n => Real.log n)
  rw [hgram] at hsplit
  simp only [primeField]
  linarith

/-- **The aggregate cannot be exponentially negative.** -/
theorem crossAggregate_ge (hF : Continuous F) (hFc : HasCompactSupport F)
    (P : Finset ℕ) (w : ℕ → ℝ) :
    -(autoCorrelation F 0 * ∑ p ∈ P, w p ^ 2)
      ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, w p * w q * autoCorrelation F (Real.log q - Real.log p) :=
  sum_gram_offDiag_ge hF hFc P w (fun n => Real.log n)

/-- **The aggregate is bounded by the `ℓ¹` norm of the weights.**  For nonnegative weights the
mean square of the prime field is at most `(Σ w_p)²A(0)`. -/
theorem crossAggregate_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) :
    ∑ p ∈ P, ∑ q ∈ P.erase p, w p * w q * autoCorrelation F (Real.log q - Real.log p)
      ≤ autoCorrelation F 0 * ((∑ p ∈ P, w p) ^ 2 - ∑ p ∈ P, w p ^ 2) := by
  have hmaj : ∀ x : ℝ, primeField F w P x ^ 2
      ≤ (∑ p ∈ P, w p) * ∑ p ∈ P, w p * F (x + Real.log p) ^ 2 := by
    intro x
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P hw
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
  have hterm : ∀ p : ℕ, Integrable fun x => w p * F (x + Real.log p) ^ 2 := by
    intro p
    exact ((integrable_sq hF hFc).comp_add_right (Real.log p)).const_mul (w p)
  have hinner : Integrable fun x => ∑ p ∈ P, w p * F (x + Real.log p) ^ 2 :=
    MeasureTheory.integrable_finsetSum P fun p _ => hterm p
  have hmono := MeasureTheory.integral_mono (integrable_primeField_sq hF hFc P w)
    (hinner.const_mul (∑ p ∈ P, w p)) hmaj
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum P (fun p _ => hterm p)] at hmono
  have hcol : ∀ p ∈ P, (∫ x, w p * F (x + Real.log p) ^ 2) = w p * autoCorrelation F 0 := by
    intro p _
    rw [MeasureTheory.integral_const_mul, integral_shift_sq]
  rw [Finset.sum_congr rfl hcol, ← Finset.sum_mul] at hmono
  rw [crossAggregate_eq_meanSquare hF hFc P w]
  nlinarith [hmono]


/-! ### Realising a prescribed prefix, and what separates two sources

Differencing a prescribed prefix produces a source realising it, so together with the rigidity of
the prefix the assignment source ↦ prefix is a bijection onto the functions vanishing at the
origin: every ledger that a step prefix could describe is the ledger of an actual source.  The
selectivity question then has an exact answer: the ledgers of two sources differ by the pairing of
their *prefix difference* with the derivative of the test.  A perturbation of the prefix is read by
a test exactly through `∫ Δ h′`, so a model with a prescribed growth of its prefix is detected at
precisely that rate. -/

/-- The source realising a prescribed prefix, by differencing it. -/
def sourceOfPrefix (g : ℕ → ℝ) : ℕ → ℝ := fun n => if n = 0 then 0 else g n - g (n - 1)

theorem sum_sourceOfPrefix (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 0 N, sourceOfPrefix g k = g N - g 0 := by
  have key : ∀ M : ℕ, ∑ k ∈ Finset.range (M + 1), sourceOfPrefix g k = g M - g 0 := by
    intro M
    induction M with
    | zero => simp [sourceOfPrefix]
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [sourceOfPrefix, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        ring
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp
  rw [hIcc]
  exact key N

theorem lagPrefix_sourceOfPrefix (g : ℕ → ℝ) (s : ℝ) :
    lagPrefix (sourceOfPrefix g) s = g ⌊Real.exp s⌋₊ - g 0 :=
  sum_sourceOfPrefix g _

/-- **Every prefix is realised, by exactly one source.** -/
theorem existsUnique_source_of_prefix (g : ℕ → ℝ) :
    ∃! a : ℕ → ℝ, lagPrefix a = fun s => g ⌊Real.exp s⌋₊ - g 0 := by
  refine ⟨sourceOfPrefix g, funext (lagPrefix_sourceOfPrefix g), fun a ha => ?_⟩
  exact eq_of_lagPrefix_eq (ha.trans (funext (lagPrefix_sourceOfPrefix g)).symm)

/-- **What separates two sources.**  The ledgers of two sources differ by the pairing of their
prefix difference with the derivative of the test; the polar density cancels entirely. -/
theorem ledger_difference_eq (a b : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∑ n ∈ Finset.range (N + 1), b n * h (Real.log n)
      = ∫ s in Ioi (0:ℝ), (lagPrefix b s - lagPrefix a s) * deriv h s := by
  have ea := sum_weight_sub_polar_eq_defect a ha0 ha1 hh hS hvan hN
  have eb := sum_weight_sub_polar_eq_defect b hb0 hb1 hh hS hvan hN
  have hia := integrableOn_Ioi_lagSourceDefect_mul_deriv a hh hS hvan hN
  have hib := integrableOn_Ioi_lagSourceDefect_mul_deriv b hh hS hvan hN
  have hsub : (∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv h s)
      - (∫ s in Ioi (0:ℝ), lagSourceDefect b s * deriv h s)
      = ∫ s in Ioi (0:ℝ), (lagPrefix b s - lagPrefix a s) * deriv h s := by
    rw [← MeasureTheory.integral_sub hia hib]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [lagSourceDefect]
    ring
  linarith

/-- A bound on the prefix difference bounds the separation of the two ledgers. -/
theorem abs_ledger_difference_le (a b : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∑ n ∈ Finset.range (N + 1), b n * h (Real.log n)|
      ≤ ∫ s in Ioi (0:ℝ), |(lagPrefix b s - lagPrefix a s) * deriv h s| := by
  rw [ledger_difference_eq a b ha0 ha1 hb0 hb1 hh hS hvan hN]
  exact abs_integral_le_integral_abs


/-! ### The one-point cone: reading the weight index by index

When the admissible cone is a single weight, membership is not an inequality but an
identification.  The lag ledger supplies it: the prefix recovers the source index by index as a
difference of two of its values, and a perturbation at one index is read by a test exactly as the
test's value at that index's lag.  So the ledger separates every single-index perturbation, the
separating functional is evaluation at `log m`, and a test blind at that lag is blind to that
index — the exact replacement for a cone-membership proof. -/

/-- The source perturbed at a single index. -/
def singleIndexPerturb (a : ℕ → ℝ) (m : ℕ) (ε : ℝ) : ℕ → ℝ :=
  fun n => a n + if n = m then ε else 0

/-- **Reading the weight index by index.**  Consecutive prefix values differ by one atom. -/
theorem index_eq_prefix_sub (a : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    a (m + 1) = lagPrefix a (Real.log ((m + 1 : ℕ) : ℝ)) - lagPrefix a (Real.log (m : ℝ)) := by
  rw [lagPrefix_log_nat a (by omega : 1 ≤ m + 1), lagPrefix_log_nat a hm,
    Finset.sum_Icc_succ_top (Nat.zero_le _)]
  ring

/-- A single-index perturbation raises the prefix by a step at that index's lag. -/
theorem lagPrefix_singleIndexPerturb (a : ℕ → ℝ) (m : ℕ) (ε : ℝ) (s : ℝ) :
    lagPrefix (singleIndexPerturb a m ε) s
      = lagPrefix a s + if m ≤ ⌊Real.exp s⌋₊ then ε else 0 := by
  rw [lagPrefix, lagPrefix]
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
      singleIndexPerturb a m ε k = a k + if k = m then ε else 0 := fun k _ => rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.Icc 0 ⌊Real.exp s⌋₊) m (fun _ => ε)]
  simp

/-- A single-index perturbation is read by a test as the test's value at that index's lag. -/
theorem sum_singleIndexPerturb_sub (a : ℕ → ℝ) {m N : ℕ} (hmN : m ≤ N) (ε : ℝ) (g : ℝ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), singleIndexPerturb a m ε n * g (Real.log n))
        - ∑ n ∈ Finset.range (N + 1), a n * g (Real.log n)
      = ε * g (Real.log (m : ℝ)) := by
  rw [← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
      (fun b _ hb => by simp [singleIndexPerturb, hb])]
  simp only [singleIndexPerturb, if_true]
  ring

/-- **The step a single index makes in the ledger.**  Pairing the prefix step at `log m` with the
derivative of the test returns exactly the test's value there. -/
theorem integral_step_mul_deriv_eq (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {m : ℕ} (hm : 2 ≤ m) (ε : ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hmN : m ≤ N) (hN : Real.exp S ≤ N) :
    (∫ s in Ioi (0:ℝ), (if m ≤ ⌊Real.exp s⌋₊ then ε else 0) * deriv h s)
      = -(ε * h (Real.log (m : ℝ))) := by
  have hm0 : (0:ℕ) ≠ m := by omega
  have hm1 : (1:ℕ) ≠ m := by omega
  have hp0 : singleIndexPerturb a m ε 0 = 0 := by simp [singleIndexPerturb, ha0, hm0]
  have hp1 : singleIndexPerturb a m ε 1 = 0 := by simp [singleIndexPerturb, ha1, hm1]
  have hdiff := ledger_difference_eq (singleIndexPerturb a m ε) a hp0 hp1 ha0 ha1 hh hS hvan hN
  rw [sum_singleIndexPerturb_sub a hmN ε h] at hdiff
  have hint : (∫ s in Ioi (0:ℝ), (lagPrefix a s - lagPrefix (singleIndexPerturb a m ε) s)
        * deriv h s)
      = ∫ s in Ioi (0:ℝ), -((if m ≤ ⌊Real.exp s⌋₊ then ε else 0) * deriv h s) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [lagPrefix_singleIndexPerturb]
    ring
  rw [hint, MeasureTheory.integral_neg] at hdiff
  linarith

/-- **The ledger separates single-index perturbations exactly at the lags the test sees.** -/
theorem ledger_separates_singleIndex (a : ℕ → ℝ) {m N : ℕ} (hmN : m ≤ N) {ε : ℝ} (hε : ε ≠ 0)
    (g : ℝ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), singleIndexPerturb a m ε n * g (Real.log n))
        ≠ ∑ n ∈ Finset.range (N + 1), a n * g (Real.log n)
      ↔ g (Real.log (m : ℝ)) ≠ 0 := by
  rw [ne_eq, ← sub_eq_zero, sum_singleIndexPerturb_sub a hmN ε g, mul_eq_zero]
  simp [hε]


/-! ### The ledger of the Beurling system of `λ`-th powers

Reading a source at the lags `λ log n` is reading the Beurling system whose generalised integers
are the `λ`-th powers.  Its ledger is the original one reparametrised: the polar density becomes
`λ⁻¹(e^{s/λ} + 1)`, whose pole sits at `1/λ`, and the residue is the original defect read at the
scale `s/λ`.  The critical line of the `λ`-system is therefore at `1/(2λ)`, while the lag weight
`e^{−s/2}` of a fixed receiver stays put: no criterion calibrated to the half-line can be
invariant under dilating the test. -/

theorem contDiff_dilate (hh : ContDiff ℝ 1 h) (lam : ℝ) :
    ContDiff ℝ 1 fun s => h (lam * s) :=
  hh.comp (contDiff_const.mul contDiff_id)

theorem deriv_dilate (hh : ContDiff ℝ 1 h) (lam s : ℝ) :
    deriv (fun y => h (lam * y)) s = deriv h (lam * s) * lam := by
  have hinner : HasDerivAt (fun y : ℝ => lam * y) lam s := by
    simpa using (hasDerivAt_id s).const_mul lam
  exact (((hh.differentiable (by norm_num)).differentiableAt (x := lam * s)).hasDerivAt.comp s
    hinner).deriv

/-- **The dilated ledger.**  Reading the atoms at the lags `λ log n` is the balance of the
Beurling system of `λ`-th powers: the polar density has its pole at `1/λ` and the residue is the
source's own defect read at the scale `s/λ`. -/
theorem sum_weight_dilate_sub_polar_eq_defect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {lam : ℝ} (hlam : 0 < lam) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp (S / lam) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (lam * Real.log n))
        - ∫ s in Ioi (0:ℝ), lam⁻¹ * ((Real.exp (s / lam) + 1) * h s)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect a (s / lam) * deriv h s := by
  have hSl : 0 < S / lam := div_pos hS hlam
  have hvanl : ∀ s, S / lam ≤ s → h (lam * s) = 0 := by
    intro s hs
    exact hvan _ ((div_le_iff₀ hlam).mp hs |>.trans_eq (mul_comm s lam))
  have hbase := sum_weight_sub_polar_eq_defect a ha0 ha1 (contDiff_dilate hh lam) hSl hvanl hN
  have hpolar : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h (lam * s))
      = ∫ s in Ioi (0:ℝ), lam⁻¹ * ((Real.exp (s / lam) + 1) * h s) := by
    have hcv := integral_comp_mul_left_Ioi
      (fun u : ℝ => (Real.exp (u / lam) + 1) * h u) 0 hlam
    rw [mul_zero] at hcv
    rw [MeasureTheory.integral_const_mul, ← smul_eq_mul, ← hcv]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [mul_div_cancel_left₀ s (ne_of_gt hlam)]
  have hres : (∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv (fun y => h (lam * y)) s)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect a (s / lam) * deriv h s := by
    have hcv := integral_comp_mul_left_Ioi
      (fun u : ℝ => lagSourceDefect a (u / lam) * deriv h u) 0 hlam
    rw [mul_zero] at hcv
    have hleft : (∫ s in Ioi (0:ℝ), lagSourceDefect a s * deriv (fun y => h (lam * y)) s)
        = lam * ∫ s in Ioi (0:ℝ),
            (fun u : ℝ => lagSourceDefect a (u / lam) * deriv h u) (lam * s) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      show lagSourceDefect a s * deriv (fun y => h (lam * y)) s
        = lam * (lagSourceDefect a (lam * s / lam) * deriv h (lam * s))
      rw [deriv_dilate hh lam s, mul_div_cancel_left₀ s (ne_of_gt hlam)]
      ring
    rw [hleft, hcv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlam), one_mul]
  rw [← hpolar, ← hres]
  exact hbase


/-! ### The comparison principle for the ledger

Against a test whose lag weight is nonincreasing, the ledger reading is monotone in the prefix:
a source that has accumulated at least as much mass at every scale is read at least as high.  The
strip weight of a compactly supported test is such a weight, so the principle is not vacuous, and
it upgrades a domination of weights — a sign twist, a character twist, a thinned Beurling weight,
the shifted pair — from a statement about defects to a statement about the readings themselves. -/

/-- **Monotonicity of the reading in the prefix.** -/
theorem ledger_mono (a b : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0) (hb0 : b 0 = 0) (hb1 : b 1 = 0)
    (hpref : ∀ s, lagPrefix a s ≤ lagPrefix b s) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (hd : ∀ s, 0 < s → deriv h s ≤ 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
      ≤ ∑ n ∈ Finset.range (N + 1), b n * h (Real.log n) := by
  have hdiff := ledger_difference_eq a b ha0 ha1 hb0 hb1 hh hS hvan hN
  have hnp : (∫ s in Ioi (0:ℝ), (lagPrefix b s - lagPrefix a s) * deriv h s) ≤ 0 := by
    refine MeasureTheory.setIntegral_nonpos measurableSet_Ioi fun s hs => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hpref s]) (hd s hs)
  linarith

/-- A source dominated by `Λ` index by index is read no higher than `Λ` by a nonincreasing
lag weight. -/
theorem ledger_le_vonMangoldt (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (ha : ∀ n, a n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (hd : ∀ s, 0 < s → deriv h s ≤ 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
      ≤ ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n) :=
  ledger_mono a _ ha0 ha1 (by simp) (by simp) (fun s => lagPrefix_mono_of_le ha s) hh hS hvan hd hN


/-! ### The prime cost and the cross-prime aggregate are two moments of one field

The prime side of the balance is the inner product of the test with its own prime field, and the
cross-prime aggregate is the energy of that same field.  The `ℓ¹` prime cost and the aggregate are
therefore the first and second moments of a single object, and the elementary bound
`2⟨F, Φ⟩ ≤ t‖F‖² + t⁻¹‖Φ‖²` turns any bound on the aggregate into a bound on the prime cost at the
free parameter `t`.  A polynomial bound on the aggregate buys a polynomial prime cost. -/

theorem integrable_mul_primeField (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c : ℕ → ℝ) : Integrable fun x => F x * primeField F c T x := by
  have hexp : ∀ x : ℝ, (∑ n ∈ T, c n * (F x * F (x + Real.log n)))
      = F x * primeField F c T x := by
    intro x
    rw [primeField, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  exact (MeasureTheory.integrable_finsetSum T fun n _ =>
    ((hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right).const_mul (c n)).congr (Filter.Eventually.of_forall hexp)

/-- **The prime side is the test against its own prime field.** -/
theorem sum_lag_eq_integral_primeField (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ T, c n * autoCorrelation F (Real.log n) = ∫ x, F x * primeField F c T x := by
  have hexp : ∀ x : ℝ, (∑ n ∈ T, c n * (F x * F (x + Real.log n)))
      = F x * primeField F c T x := by
    intro x
    rw [primeField, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hint : ∀ n ∈ T, Integrable fun x => c n * (F x * F (x + Real.log n)) := fun n _ =>
    ((hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right).const_mul (c n)
  rw [← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_finsetSum T hint]
  exact Finset.sum_congr rfl fun n _ => by rw [MeasureTheory.integral_const_mul, autoCorrelation]

/-- The prime cost against the energy of the prime field, at a free parameter. -/
theorem two_mul_sum_lag_le_energy (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * ∑ n ∈ T, c n * autoCorrelation F (Real.log n)
      ≤ t * autoCorrelation F 0 + t⁻¹ * ∫ x, primeField F c T x ^ 2 := by
  have hpt : ∀ x : ℝ, 2 * (F x * primeField F c T x)
      ≤ t * F x ^ 2 + t⁻¹ * primeField F c T x ^ 2 := by
    intro x
    have key : t * (F x - primeField F c T x / t) ^ 2
        = t * F x ^ 2 - 2 * (F x * primeField F c T x) + t⁻¹ * primeField F c T x ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg ht.le (sq_nonneg (F x - primeField F c T x / t)), key]
  have hl : Integrable fun x => 2 * (F x * primeField F c T x) :=
    (integrable_mul_primeField hF hFc T c).const_mul 2
  have hr : Integrable fun x => t * F x ^ 2 + t⁻¹ * primeField F c T x ^ 2 :=
    ((integrable_sq hF hFc).const_mul t).add
      ((integrable_primeField_sq hF hFc T c).const_mul t⁻¹)
  have hmono := MeasureTheory.integral_mono hl hr hpt
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add ((integrable_sq hF hFc).const_mul t)
      ((integrable_primeField_sq hF hFc T c).const_mul t⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    ← autoCorrelation_zero_eq, ← sum_lag_eq_integral_primeField hF hFc T c] at hmono
  exact hmono

/-- **The bridge.**  A bound on the cross-prime aggregate bounds the prime cost. -/
theorem two_mul_sum_lag_le_aggregate (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (c : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * ∑ n ∈ T, c n * autoCorrelation F (Real.log n)
      ≤ t * autoCorrelation F 0
        + t⁻¹ * ((∑ p ∈ T, ∑ q ∈ T.erase p,
              c p * c q * autoCorrelation F (Real.log q - Real.log p))
            + autoCorrelation F 0 * ∑ p ∈ T, c p ^ 2) := by
  have h := two_mul_sum_lag_le_energy hF hFc T c ht
  rw [crossAggregate_eq_meanSquare hF hFc T c]
  linarith


/-! ### The pole plane factorises, and the pole-free hyperplanes

The difference of squares that the polar pairing produces is the product of the test's two
half-exponential moments, `(∫F e^{−x/2})(∫F e^{x/2})`.  So the pole plane is a rank-one readout in
each moment separately: it vanishes exactly on the union of the two hyperplanes where one moment
is zero, it is positive when the moments agree in sign and negative when they disagree, and on an
odd test — where the two moments are negatives of each other — it is minus a perfect square.  On a
pole-free test the balance reads the prime side with no polar subsidy at all. -/

/-- The test's descending half-exponential moment. -/
def expMomentNeg (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.exp (-x / 2)

/-- The test's ascending half-exponential moment. -/
def expMomentPos (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.exp (x / 2)

/-- **The pole plane is the product of the two half-exponential moments.** -/
theorem poleplane_eq_moment_mul (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2
      = expMomentNeg F * expMomentPos F := by
  have hc : Integrable fun x => F x * Real.cosh (x / 2) :=
    (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hs : Integrable fun x => F x * Real.sinh (x / 2) :=
    (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsub : (∫ x, F x * Real.cosh (x / 2)) - ∫ x, F x * Real.sinh (x / 2)
      = expMomentNeg F := by
    rw [← MeasureTheory.integral_sub hc hs, expMomentNeg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * Real.cosh (x / 2) - F x * Real.sinh (x / 2) = F x * Real.exp (-x / 2)
    rw [← mul_sub, Real.cosh_sub_sinh, ← neg_div]
  have hadd : (∫ x, F x * Real.cosh (x / 2)) + ∫ x, F x * Real.sinh (x / 2)
      = expMomentPos F := by
    rw [← MeasureTheory.integral_add hc hs, expMomentPos]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * Real.cosh (x / 2) + F x * Real.sinh (x / 2) = F x * Real.exp (x / 2)
    rw [← mul_add, Real.cosh_add_sinh]
  rw [← hsub, ← hadd]
  ring

/-- **The pole-free hyperplanes.**  The pole plane vanishes exactly when one of the two moments
does. -/
theorem poleplane_eq_zero_iff (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2 = 0
      ↔ expMomentNeg F = 0 ∨ expMomentPos F = 0 := by
  rw [poleplane_eq_moment_mul hF hFc, mul_eq_zero]

/-- On an odd test the two moments are negatives of each other. -/
theorem expMomentPos_odd (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) : expMomentPos F = -expMomentNeg F := by
  have hint : Integrable fun x => F x * Real.exp (-x / 2) :=
    (hF.mul (Real.continuous_exp.comp
      (continuous_neg.div_const 2))).integrable_of_hasCompactSupport hFc.mul_right
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun x => F x * Real.exp (-x / 2))
  rw [expMomentPos, expMomentNeg, ← hrefl, ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F x * Real.exp (x / 2) = -(F (-x) * Real.exp (-(-x) / 2))
  rw [hodd x, show -(-x) / 2 = x / 2 by ring]
  ring

/-- **The pole charge of an odd test is a perfect square.** -/
theorem poleplane_odd (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) :
    (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2
      = -expMomentNeg F ^ 2 := by
  rw [poleplane_eq_moment_mul hF hFc, expMomentPos_odd hF hFc hodd]
  ring

/-- **The balance on a pole-free test.**  With one half-exponential moment annihilated the prime
side is the Chebyshev residue outright, with no polar subsidy. -/
theorem testBalance_poleFree (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N)
    (hfree : expMomentNeg F = 0 ∨ expMomentPos F = 0) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hz := (poleplane_eq_zero_iff hF.continuous hFc).mpr hfree
  have hb := testBalance_poleplane hF hFc hr hsupp hN
  rw [hz] at hb
  linarith


/-! ### The receiver on the first two cells, exactly

The Chebyshev count is a step function of the lag, so the critical-scale functional is piecewise
elementary and its first cells can be written out.  Below `log 2` it is `e^s − 1`, the pure polar
contribution; on `[log 2, log 3)` the first atom switches on and subtracts a linear term
`(s − log 2)log 2`.  These are the exact values of the receiver at the apertures of the first
prime window. -/

theorem lagChebyshev_eq_zero_of_lt_log_two {s : ℝ} (hs : s < Real.log 2) : lagChebyshev s = 0 := by
  have hlt : Real.exp s < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 1 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  rw [lagChebyshev]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hk1 : k ≤ 1 := hk.2.trans hfl
  interval_cases k <;> simp

/-- On the second cell only the atom at `2` has switched on. -/
theorem lagChebyshev_eq_log_two {s : ℝ} (h1 : Real.log 2 ≤ s) (h2 : s < Real.log 3) :
    lagChebyshev s = Real.log 2 := by
  have hge : (2:ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hlt : Real.exp s < 3 := by
    have := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
  have hfl : ⌊Real.exp s⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · exact_mod_cast hge
    · exact_mod_cast hlt
  have hIcc : Finset.Icc 0 2 = Finset.range 3 := by ext k; simp; omega
  rw [lagChebyshev, hfl, hIcc]
  simp [Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- On an interval where the Chebyshev count is constant the critical-scale integrand is
elementary. -/
theorem integral_chebyshevError_of_const {a b c : ℝ} (hab : a ≤ b)
    (hc : ∀ u, a < u → u < b → lagChebyshev u = c) :
    (∫ u in a..b, (Real.exp u - lagChebyshev u))
      = (Real.exp b - Real.exp a) - c * (b - a) := by
  have hae : (∫ u in a..b, (Real.exp u - lagChebyshev u))
      = ∫ u in a..b, (Real.exp u - c) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (μ := (volume : Measure ℝ)) b)] with u hu hmem
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    rw [Set.uIoc_of_le hab] at hmem
    rw [hc u hmem.1 (lt_of_le_of_ne hmem.2 hu)]
  rw [hae, intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable a b)
    intervalIntegrable_const, integral_exp, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **The receiver on the quiet cell.**  Below the first prime the critical-scale functional is
the pure polar growth. -/
theorem criticalScalePrefix_first_cell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.log 2) :
    criticalScalePrefix s = Real.exp s - 1 := by
  rw [criticalScalePrefix,
    integral_chebyshevError_of_const hs0
      (fun u hu1 hu2 => lagChebyshev_eq_zero_of_lt_log_two (lt_of_lt_of_le hu2 hs))]
  simp

/-- **The receiver on the first prime cell.**  Past `log 2` the first atom subtracts a linear
term from the polar growth. -/
theorem criticalScalePrefix_second_cell {s : ℝ} (h1 : Real.log 2 ≤ s) (h2 : s < Real.log 3) :
    criticalScalePrefix s = Real.exp s - 1 - (s - Real.log 2) * Real.log 2 := by
  have hsplit : (∫ u in (0:ℝ)..s, (Real.exp u - lagChebyshev u))
      = (∫ u in (0:ℝ)..Real.log 2, (Real.exp u - lagChebyshev u))
        + ∫ u in (Real.log 2)..s, (Real.exp u - lagChebyshev u) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_criticalScaleIntegrand 0 (Real.log 2))
      (intervalIntegrable_criticalScaleIntegrand (Real.log 2) s)).symm
  have hfirst := criticalScalePrefix_first_cell (Real.log_nonneg (by norm_num)) le_rfl
  have hsecond := integral_chebyshevError_of_const h1
    (fun u hu1 hu2 => lagChebyshev_eq_log_two (le_of_lt hu1) (lt_trans hu2 h2))
  rw [criticalScalePrefix] at hfirst ⊢
  rw [hsplit, hfirst, hsecond, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  ring


/-! ### The receiver as an exact recursion over the integers

Between consecutive integer scales the Chebyshev count is frozen, so the critical-scale functional
advances by exactly one unit of polar growth minus the frozen count against the logarithmic gap:

    D(log(N+1)) = D(log N) + 1 − ψ(N)·log(1 + 1/N).

Unrolling it writes the receiver at every integer scale in closed form, as the scale minus a sum of
`ψ(k)log(1+1/k)`.  The Riemann Hypothesis is the one-sided bound `D(T) ≤ B(1+T)e^{T/2}` on this
sequence, so the receiver is a completely explicit discrete object. -/

theorem lagChebyshev_eq_on_cell {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (h1 : Real.log (N : ℝ) ≤ u) (h2 : u < Real.log ((N : ℝ) + 1)) :
    lagChebyshev u = ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hge : (N : ℝ) ≤ Real.exp u := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hNpos] at this
  have hlt : Real.exp u < (N : ℝ) + 1 := by
    have := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by linarith)] at this
  have hfl : ⌊Real.exp u⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]
    exact ⟨hge, by linarith⟩
  rw [lagChebyshev, hfl]

/-- **One step of the receiver.**  Across one integer cell the polar growth adds exactly one and
the frozen Chebyshev count subtracts the logarithmic gap. -/
theorem criticalScalePrefix_succ {N : ℕ} (hN : 1 ≤ N) :
    criticalScalePrefix (Real.log ((N : ℝ) + 1))
      = criticalScalePrefix (Real.log (N : ℝ)) + 1
        - (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
          * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hNpos (by linarith)
  have hsplit : (∫ u in (0:ℝ)..Real.log ((N : ℝ) + 1), (Real.exp u - lagChebyshev u))
      = (∫ u in (0:ℝ)..Real.log (N : ℝ), (Real.exp u - lagChebyshev u))
        + ∫ u in Real.log (N : ℝ)..Real.log ((N : ℝ) + 1), (Real.exp u - lagChebyshev u) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_criticalScaleIntegrand 0 (Real.log (N : ℝ)))
      (intervalIntegrable_criticalScaleIntegrand (Real.log (N : ℝ))
        (Real.log ((N : ℝ) + 1)))).symm
  have hcell := integral_chebyshevError_of_const hlog
    (fun u hu1 hu2 => lagChebyshev_eq_on_cell hN (le_of_lt hu1) hu2)
  rw [criticalScalePrefix, criticalScalePrefix, hsplit, hcell,
    Real.exp_log hNpos, Real.exp_log (by linarith : (0:ℝ) < (N : ℝ) + 1)]
  ring

/-- **The receiver in closed form at the integer scales.** -/
theorem criticalScalePrefix_log_natCast_succ (M : ℕ) :
    criticalScalePrefix (Real.log ((M : ℝ) + 1))
      = (M : ℝ) - ∑ k ∈ Finset.range M,
          (∑ j ∈ Finset.Icc 0 (k + 1), (ArithmeticFunction.vonMangoldt j : ℝ))
            * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
  induction M with
  | zero => simp [criticalScalePrefix]
  | succ M ih =>
      have hstep := criticalScalePrefix_succ (N := M + 1) (by omega)
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hstep
      rw [show ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 by push_cast; ring,
        show ((M : ℝ) + 1) + 1 = (M : ℝ) + 2 by ring] at *
      rw [hstep, ih, Finset.sum_range_succ]
      push_cast
      ring


/-! ### The receiver is sawtooth-convex, with the atoms as its kinks

On each integer cell the Chebyshev count is frozen, so the receiver is `e^u − ψ(N)u` up to a
constant: strictly convex, with slope `e^u − ψ(N)`.  At each integer scale the slope drops by
exactly the von Mangoldt atom there.  The receiver is therefore a piecewise strictly convex
function whose kinks *are* the arithmetic: the atoms can be read back off the corners of the
graph, which is the analytic form of source rigidity. -/

/-- The receiver on a whole integer cell. -/
theorem criticalScalePrefix_on_cell {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (h1 : Real.log (N : ℝ) ≤ s) (h2 : s ≤ Real.log ((N : ℝ) + 1)) :
    criticalScalePrefix s = criticalScalePrefix (Real.log (N : ℝ)) + (Real.exp s - N)
      - (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
        * (s - Real.log (N : ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hsplit : (∫ u in (0:ℝ)..s, (Real.exp u - lagChebyshev u))
      = (∫ u in (0:ℝ)..Real.log (N : ℝ), (Real.exp u - lagChebyshev u))
        + ∫ u in Real.log (N : ℝ)..s, (Real.exp u - lagChebyshev u) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_criticalScaleIntegrand 0 (Real.log (N : ℝ)))
      (intervalIntegrable_criticalScaleIntegrand (Real.log (N : ℝ)) s)).symm
  have hcell := integral_chebyshevError_of_const h1
    (fun u hu1 hu2 => lagChebyshev_eq_on_cell hN (le_of_lt hu1) (lt_of_lt_of_le hu2 h2))
  rw [criticalScalePrefix, criticalScalePrefix, hsplit, hcell, Real.exp_log hNpos]
  ring

/-- **The slope of the receiver inside a cell.** -/
theorem hasDerivAt_criticalScalePrefix_of_mem_cell {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (h1 : Real.log (N : ℝ) < s) (h2 : s < Real.log ((N : ℝ) + 1)) :
    HasDerivAt criticalScalePrefix
      (Real.exp s - ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) s := by
  set c : ℝ := ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) with hc
  set C : ℝ := criticalScalePrefix (Real.log (N : ℝ)) - N + c * Real.log (N : ℝ) with hC
  have hbase : HasDerivAt (fun u : ℝ => C + (Real.exp u - c * u)) (Real.exp s - c) s := by
    have := ((Real.hasDerivAt_exp s).sub ((hasDerivAt_id s).const_mul c)).const_add C
    simpa using this
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventually_of_mem
    (isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨h1, h2⟩)) fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := Set.mem_Ioo.mp hu
  rw [criticalScalePrefix_on_cell hN (le_of_lt hu1) (le_of_lt hu2), hC]
  ring

/-- **The kink is the atom.**  Across an integer scale the slope of the receiver drops by exactly
the von Mangoldt weight there. -/
theorem slope_jump_eq_vonMangoldt (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
        - ∑ k ∈ Finset.Icc 0 (N + 1), (ArithmeticFunction.vonMangoldt k : ℝ)
      = -(ArithmeticFunction.vonMangoldt (N + 1) : ℝ) := by
  rw [Finset.sum_Icc_succ_top (Nat.zero_le _)]
  ring


/-! ### The ledger calibrated to an arbitrary pole

Nothing in the balance is special to a pole at `1`: for every `ρ ≠ 0` the weight
`(e^{ρs} − 1)/ρ + s` has derivative `e^{ρs} + 1` and vanishes at the origin, so the same
integration by parts gives a ledger whose comparison density is `e^{ρs} + 1` and whose residue is
the source's defect against that calibration.  This is the ledger a Beurling system with its pole
off `1` must be read with, and at `ρ = 1` it is the two-pole weight. -/

/-- The polar weight calibrated to a pole at `ρ`. -/
def poleWeightAt (rho s : ℝ) : ℝ := (Real.exp (rho * s) - 1) / rho + s

theorem poleWeightAt_zero (rho : ℝ) : poleWeightAt rho 0 = 0 := by simp [poleWeightAt]

theorem poleWeightAt_one : poleWeightAt 1 = twoPoleWeight := by
  funext s
  simp [poleWeightAt, twoPoleWeight]
  ring

theorem continuous_poleWeightAt (rho : ℝ) : Continuous (poleWeightAt rho) := by
  unfold poleWeightAt
  fun_prop

theorem hasDerivAt_poleWeightAt {rho : ℝ} (hrho : rho ≠ 0) (s : ℝ) :
    HasDerivAt (poleWeightAt rho) (Real.exp (rho * s) + 1) s := by
  have hmul : HasDerivAt (fun u : ℝ => rho * u) rho s := by
    simpa using (hasDerivAt_id s).const_mul rho
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (rho * u)) (Real.exp (rho * s) * rho) s := hmul.exp
  have h2 : HasDerivAt (fun u : ℝ => (Real.exp (rho * u) - 1) / rho) (Real.exp (rho * s)) s := by
    have h3 := (h1.sub_const 1).div_const rho
    rwa [mul_div_assoc, div_self hrho, mul_one] at h3
  have h4 : HasDerivAt (fun u : ℝ => (Real.exp (rho * u) - 1) / rho + u)
      (Real.exp (rho * s) + 1) s := h2.add (hasDerivAt_id s)
  exact h4

/-- The defect of a source against the calibration at `ρ`. -/
def lagSourceDefectAt (rho : ℝ) (a : ℕ → ℝ) (s : ℝ) : ℝ := poleWeightAt rho s - lagPrefix a s

theorem integral_poleWeightAt_mul_deriv {rho : ℝ} (hrho : rho ≠ 0) (hh : ContDiff ℝ 1 h)
    (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), poleWeightAt rho s * deriv h s)
      = -∫ s in Ioi (0:ℝ), (Real.exp (rho * s) + 1) * h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hA : (∫ s in Ioi (0:ℝ), poleWeightAt rho s * deriv h s)
      = ∫ s in (0:ℝ)..S, poleWeightAt rho s * deriv h s :=
    integral_Ioi_eq_intervalIntegral ((continuous_poleWeightAt rho).mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), (Real.exp (rho * s) + 1) * h s)
      = ∫ s in (0:ℝ)..S, (Real.exp (rho * s) + 1) * h s :=
    integral_Ioi_eq_intervalIntegral (by fun_prop) hS
      (fun s hs => by rw [hvan s hs.le, mul_zero])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := poleWeightAt rho) (u' := fun s => Real.exp (rho * s) + 1) (v := h) (v' := deriv h)
    (a := 0) (b := S)
    (fun x _ => hasDerivAt_poleWeightAt hrho x)
    (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (rho * s) + 1).intervalIntegrable _ _)
    (hdc.intervalIntegrable _ _)
  rw [hA, hB, hparts, hvan S le_rfl, poleWeightAt_zero]
  ring

/-- **The balance at an arbitrary pole.** -/
theorem sum_weight_sub_polarAt_eq_defect {rho : ℝ} (hrho : rho ≠ 0) (a : ℕ → ℝ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp (rho * s) + 1) * h s
      = ∫ s in Ioi (0:ℝ), lagSourceDefectAt rho a s * deriv h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hwi : IntegrableOn (fun s => poleWeightAt rho s * deriv h s) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => poleWeightAt rho s * deriv h s) (Ioc (0:ℝ) S) :=
      (((continuous_poleWeightAt rho).mul hdc).integrableOn_Icc (a := 0) (b := S)).mono_set
        Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => poleWeightAt rho s * deriv h s) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hpi := integrableOn_Ioi_lagPrefix_mul_deriv a hh hS hvan hN
  have hsplit : (∫ s in Ioi (0:ℝ), lagSourceDefectAt rho a s * deriv h s)
      = (∫ s in Ioi (0:ℝ), poleWeightAt rho s * deriv h s)
        - ∫ s in Ioi (0:ℝ), lagPrefix a s * deriv h s := by
    rw [← MeasureTheory.integral_sub hwi hpi]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
      simp [lagSourceDefectAt, sub_mul]
  rw [hsplit, integral_poleWeightAt_mul_deriv hrho hh hS hvan,
    sum_weight_mul_eq_neg_integral a ha0 ha1 hh hS hvan hN]
  ring


/-! ### The modulus of continuity of the Gram entries

The difference of two autocorrelation values is the test paired with the difference of two of its
translates, so Cauchy–Schwarz against the displacement metric bounds it:

    |A(s) − A(t)| ≤ √(A(0)·2D(s − t)) .

The Gram entries therefore vary no faster than the square root of the displacement energy at the
separation of their lags.  Together with the quadratic gap this is a two-sided description of how
the Gram of the translate family moves with the lag. -/

theorem displacement_neg (F : ℝ → ℝ) (t : ℝ) : displacement F (-t) = displacement F t := by
  rw [displacement, displacement, autoCorrelation_neg]

theorem integrable_shift_diff_sq (hF : Continuous F) (hFc : HasCompactSupport F) (s t : ℝ) :
    Integrable fun x => (F (x + s) - F (x + t)) ^ 2 := by
  refine (integrable_diff_sq_shift hF hFc s (t - s)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show (F (x + s) - F (x + s + (t - s))) ^ 2 = (F (x + s) - F (x + t)) ^ 2
  rw [show x + s + (t - s) = x + t by ring]

theorem integral_shift_diff_sq (hF : Continuous F) (hFc : HasCompactSupport F) (s t : ℝ) :
    (∫ x, (F (x + s) - F (x + t)) ^ 2) = 2 * displacement F (t - s) := by
  rw [← integral_diff_sq_shift hF hFc s (t - s)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (F (x + s) - F (x + t)) ^ 2 = (F (x + s) - F (x + s + (t - s))) ^ 2
  rw [show x + s + (t - s) = x + t by ring]

theorem autoCorrelation_sub (hF : Continuous F) (hFc : HasCompactSupport F) (s t : ℝ) :
    autoCorrelation F s - autoCorrelation F t = ∫ x, F x * (F (x + s) - F (x + t)) := by
  have hps : Integrable fun x => F x * F (x + s) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hpt : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  rw [autoCorrelation, autoCorrelation, ← MeasureTheory.integral_sub hps hpt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F x * F (x + s) - F x * F (x + t) = F x * (F (x + s) - F (x + t))
  ring

theorem two_mul_autoCorrelation_sub_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (s t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * (autoCorrelation F s - autoCorrelation F t)
      ≤ ε * autoCorrelation F 0 + ε⁻¹ * (2 * displacement F (t - s)) := by
  have hpt : ∀ x : ℝ, 2 * (F x * (F (x + s) - F (x + t)))
      ≤ ε * F x ^ 2 + ε⁻¹ * (F (x + s) - F (x + t)) ^ 2 := by
    intro x
    have key : ε * (F x - (F (x + s) - F (x + t)) / ε) ^ 2
        = ε * F x ^ 2 - 2 * (F x * (F (x + s) - F (x + t)))
          + ε⁻¹ * (F (x + s) - F (x + t)) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hε.le (sq_nonneg (F x - (F (x + s) - F (x + t)) / ε)), key]
  have hdiff : Integrable fun x => F x * (F (x + s) - F (x + t)) := by
    have hps : Integrable fun x => F x * F (x + s) :=
      (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hFc.mul_right
    have hpt' : Integrable fun x => F x * F (x + t) :=
      (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hFc.mul_right
    refine (hps.sub hpt').congr (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + s) - F x * F (x + t) = F x * (F (x + s) - F (x + t))
    ring
  have hl : Integrable fun x => 2 * (F x * (F (x + s) - F (x + t))) := hdiff.const_mul 2
  have hr : Integrable fun x => ε * F x ^ 2 + ε⁻¹ * (F (x + s) - F (x + t)) ^ 2 :=
    ((integrable_sq hF hFc).const_mul ε).add
      ((integrable_shift_diff_sq hF hFc s t).const_mul ε⁻¹)
  have hmono := MeasureTheory.integral_mono hl hr hpt
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add ((integrable_sq hF hFc).const_mul ε)
      ((integrable_shift_diff_sq hF hFc s t).const_mul ε⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    ← autoCorrelation_zero_eq, integral_shift_diff_sq hF hFc s t,
    ← autoCorrelation_sub hF hFc s t] at hmono
  exact hmono

/-- **The Gram entries move no faster than the displacement metric.** -/
theorem abs_autoCorrelation_sub_le (hF : Continuous F) (hFc : HasCompactSupport F) (s t : ℝ) :
    |autoCorrelation F s - autoCorrelation F t|
      ≤ Real.sqrt (autoCorrelation F 0 * (2 * displacement F (s - t))) := by
  have hst : displacement F (t - s) = displacement F (s - t) := by
    rw [show t - s = -(s - t) by ring, displacement_neg]
  have hnn : 0 ≤ 2 * displacement F (s - t) := by
    have := displacement_nonneg hF hFc (s - t); linarith
  have h1 : autoCorrelation F s - autoCorrelation F t
      ≤ Real.sqrt (autoCorrelation F 0 * (2 * displacement F (s - t))) := by
    refine le_sqrt_mul_of_two_mul_le (autoCorrelation_zero_nonneg F) hnn fun ε hε => ?_
    have := two_mul_autoCorrelation_sub_le hF hFc s t hε
    rwa [hst] at this
  have h2 : autoCorrelation F t - autoCorrelation F s
      ≤ Real.sqrt (autoCorrelation F 0 * (2 * displacement F (s - t))) := by
    refine le_sqrt_mul_of_two_mul_le (autoCorrelation_zero_nonneg F) hnn fun ε hε => ?_
    exact two_mul_autoCorrelation_sub_le hF hFc t s hε
  exact abs_le.mpr ⟨by linarith, h1⟩


/-! ### The displacement energy of a regular test, from above

The aperture laws bound the displacement energy from below.  From above it is controlled by the
test's own regularity alone: a derivative bound `M` and an aperture `r` give
`2D(t) ≤ M²t²(2r + 2|t|)`, because the increment is at most `M|t|` pointwise and lives on an
interval of length `2r + 2|t|`.  With the modulus of continuity this makes the Gram entries
Lipschitz in the lag with an explicit constant — the quantitative form of the banded structure of
the near-diagonal block. -/

theorem abs_sub_shift_le (hF : ContDiff ℝ 1 F) {M : ℝ} (hM : ∀ x, |deriv F x| ≤ M) (x t : ℝ) :
    |F x - F (x + t)| ≤ M * |t| := by
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ F y :=
    fun y _ => hF.differentiable one_ne_zero y
  have hb : ∀ y ∈ (Set.univ : Set ℝ), ‖deriv F y‖ ≤ M := fun y _ => by
    rw [Real.norm_eq_abs]; exact hM y
  have hkey := convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff hb
    (Set.mem_univ (x + t)) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show x - (x + t) = -t by ring, abs_neg] at hkey
  exact hkey

/-- **The displacement energy of a regular test, from above.** -/
theorem two_mul_displacement_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r M : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hM : ∀ x, |deriv F x| ≤ M) (t : ℝ) :
    2 * displacement F t ≤ M ^ 2 * t ^ 2 * (2 * r + 2 * |t|) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set R : ℝ := r + |t| with hR
  have hRr : r ≤ R := by rw [hR]; linarith [abs_nonneg t]
  have hvanish : ∀ x ∉ Set.Icc (-R) R, (F x - F (x + t)) ^ 2 = 0 := by
    intro x hx
    have hcase : x < -R ∨ R < x := by
      rcases le_or_gt (-R) x with hge | hlt
      · refine Or.inr ?_
        by_contra hc
        exact hx (Set.mem_Icc.mpr ⟨hge, le_of_not_gt hc⟩)
      · exact Or.inl hlt
    rcases hcase with hx1 | hx1
    · have h1 : F x = 0 := by
        refine hsupp x ?_
        rw [abs_of_neg (by linarith [abs_nonneg t] : x < 0)]
        linarith [abs_nonneg t]
      have h2 : F (x + t) = 0 := by
        refine hsupp (x + t) ?_
        have hlt : x + t < -r := by
          have := le_abs_self t
          linarith
        rw [abs_of_neg (by linarith : x + t < 0)]
        linarith
      rw [h1, h2]; ring
    · have h1 : F x = 0 := by
        refine hsupp x ?_
        rw [abs_of_pos (by linarith [abs_nonneg t] : (0:ℝ) < x)]
        linarith [abs_nonneg t]
      have h2 : F (x + t) = 0 := by
        refine hsupp (x + t) ?_
        have hgt : r < x + t := by
          have := neg_abs_le t
          linarith
        rw [abs_of_pos (by linarith : (0:ℝ) < x + t)]
        linarith
      rw [h1, h2]; ring
  have hbound : ∀ x ∈ Set.Icc (-R) R, (F x - F (x + t)) ^ 2 ≤ M ^ 2 * t ^ 2 := by
    intro x _
    have h := abs_sub_shift_le hF hM x t
    have hsq : (F x - F (x + t)) ^ 2 ≤ (M * |t|) ^ 2 := by
      rw [← sq_abs (F x - F (x + t))]
      nlinarith [abs_nonneg (F x - F (x + t)), h]
    calc (F x - F (x + t)) ^ 2 ≤ (M * |t|) ^ 2 := hsq
      _ = M ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  have hRnn : (0:ℝ) ≤ R := le_trans hr.le hRr
  have hmono := MeasureTheory.setIntegral_mono_on
    ((integrable_diff_sq hF.continuous hFc t).integrableOn)
    (integrableOn_const (C := M ^ 2 * t ^ 2) (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    measurableSet_Icc hbound
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
    max_eq_left (by linarith : (0:ℝ) ≤ R - -R)] at hmono
  rw [two_mul_displacement_eq hF.continuous hFc t,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
  calc (∫ x in Set.Icc (-R) R, (F x - F (x + t)) ^ 2)
      ≤ (R - -R) * (M ^ 2 * t ^ 2) := hmono
    _ = M ^ 2 * t ^ 2 * (2 * r + 2 * |t|) := by rw [hR]; ring

/-- **The Gram entries are Lipschitz in the lag.** -/
theorem abs_autoCorrelation_sub_le_lipschitz (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r M : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hM : ∀ x, |deriv F x| ≤ M)
    (s t : ℝ) :
    |autoCorrelation F s - autoCorrelation F t|
      ≤ Real.sqrt (autoCorrelation F 0 * (M ^ 2 * (s - t) ^ 2 * (2 * r + 2 * |s - t|))) := by
  refine le_trans (abs_autoCorrelation_sub_le hF.continuous hFc s t) ?_
  refine Real.sqrt_le_sqrt ?_
  exact mul_le_mul_of_nonneg_left
    (two_mul_displacement_le hF hFc hr hsupp hM (s - t)) (autoCorrelation_zero_nonneg F)


/-! ### The horizon of the reading, and the unconditional cost

A test of aperture `r` sees no lag beyond `2r`, so the prime side is a *finite* sum that does not
depend on the horizon once the horizon passes `e^{2r}`: the ledger is genuinely local in the
scale.  Bounding each surviving term by the mass gives the unconditional cost of the prime side,
the `ℓ¹` prime cost against which every positivity statement of the programme is graded — the
rate `1` of the grading, before any arithmetic is used. -/

/-- **The reading has a horizon.**  Past `e^{2r}` the atoms contribute nothing. -/
theorem sum_lag_eq_of_horizon (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (c : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M)
    (hN : Real.exp (2 * r) ≤ N) :
    ∑ n ∈ Finset.range (M + 1), c n * autoCorrelation F (Real.log n)
      = ∑ n ∈ Finset.range (N + 1), c n * autoCorrelation F (Real.log n) := by
  have hsub : Finset.range (N + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsub fun n hn hnot => ?_).symm
  have hNn : N < n := by
    by_contra hc
    exact hnot (Finset.mem_range.mpr (by omega))
  have hNpos : (0:ℝ) < Real.exp (2 * r) := Real.exp_pos _
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le hNpos (le_trans hN (by exact_mod_cast hNn.le))
  have hlog : 2 * r ≤ Real.log n := by
    rw [← Real.log_exp (2 * r)]
    exact Real.log_le_log hNpos (le_trans hN (by exact_mod_cast hNn.le))
  rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero]

/-- **The unconditional cost of the prime side.**  Every surviving atom is read at most at the
full mass, so the cost is the `ℓ¹` weight of the atoms below the horizon times the mass. -/
theorem abs_sum_lag_le_l1 (hF : Continuous F) (hFc : HasCompactSupport F) (T : Finset ℕ)
    (c : ℕ → ℝ) :
    |∑ n ∈ T, c n * autoCorrelation F (Real.log n)|
      ≤ autoCorrelation F 0 * ∑ n ∈ T, |c n| := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  calc |c n| * |autoCorrelation F (Real.log n)|
      ≤ |c n| * autoCorrelation F 0 :=
        mul_le_mul_of_nonneg_left (abs_autoCorrelation_le hF hFc _) (abs_nonneg _)
    _ = autoCorrelation F 0 * |c n| := mul_comm _ _


/-! ### The bilinear Gram identity and Cauchy–Schwarz between fields

The same expansion that makes a single Gram form a square makes a cross Gram form an inner
product of two fields.  Cauchy–Schwarz then bounds the cross-aggregate of two weight families by
the geometric mean of their own energies: a family whose field has small energy cannot correlate
strongly with any other, whatever its arithmetic.  This is the tool for comparing an arithmetic
source with a model source at the level of the bilinear form that carries the rate. -/

theorem primeField_neg (F : ℝ → ℝ) (c : ℕ → ℝ) (P : Finset ℕ) (x : ℝ) :
    primeField F (fun n => -c n) P x = -primeField F c P x := by
  rw [primeField, primeField, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem integrable_primeField_mul (hF : Continuous F) (hFc : HasCompactSupport F)
    (P Q : Finset ℕ) (c d : ℕ → ℝ) :
    Integrable fun x => primeField F c P x * primeField F d Q x := by
  have hexp : ∀ x : ℝ, (∑ m ∈ P, ∑ n ∈ Q,
      c m * d n * (F (x + Real.log m) * F (x + Real.log n)))
      = primeField F c P x * primeField F d Q x := by
    intro x
    rw [primeField, primeField, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  exact (MeasureTheory.integrable_finsetSum P fun m _ =>
    MeasureTheory.integrable_finsetSum Q fun n _ =>
      (integrable_shift_mul hF hFc (Real.log m) (Real.log n)).const_mul (c m * d n)).congr
    (Filter.Eventually.of_forall hexp)

/-- **The cross Gram form is the inner product of the two fields.** -/
theorem sum_cross_gram_eq_integral (hF : Continuous F) (hFc : HasCompactSupport F)
    (P Q : Finset ℕ) (c d : ℕ → ℝ) :
    ∑ m ∈ P, ∑ n ∈ Q, c m * d n * autoCorrelation F (Real.log n - Real.log m)
      = ∫ x, primeField F c P x * primeField F d Q x := by
  have hint2 : ∀ m : ℕ, ∀ n ∈ Q,
      Integrable fun x => c m * d n * (F (x + Real.log m) * F (x + Real.log n)) :=
    fun m n _ => (integrable_shift_mul hF hFc (Real.log m) (Real.log n)).const_mul (c m * d n)
  have hint : ∀ m ∈ P, Integrable fun x =>
      ∑ n ∈ Q, c m * d n * (F (x + Real.log m) * F (x + Real.log n)) :=
    fun m _ => MeasureTheory.integrable_finsetSum Q (hint2 m)
  have hexp : ∀ x : ℝ, primeField F c P x * primeField F d Q x
      = ∑ m ∈ P, ∑ n ∈ Q, c m * d n * (F (x + Real.log m) * F (x + Real.log n)) := by
    intro x
    rw [primeField, primeField, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_finsetSum P hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_finsetSum Q (hint2 m)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_shift_mul]

theorem two_mul_integral_primeField_mul_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (P Q : Finset ℕ) (c d : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * ∫ x, primeField F c P x * primeField F d Q x
      ≤ ε * (∫ x, primeField F c P x ^ 2) + ε⁻¹ * ∫ x, primeField F d Q x ^ 2 := by
  have hpt : ∀ x : ℝ, 2 * (primeField F c P x * primeField F d Q x)
      ≤ ε * primeField F c P x ^ 2 + ε⁻¹ * primeField F d Q x ^ 2 := by
    intro x
    have key : ε * (primeField F c P x - primeField F d Q x / ε) ^ 2
        = ε * primeField F c P x ^ 2
          - 2 * (primeField F c P x * primeField F d Q x)
          + ε⁻¹ * primeField F d Q x ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hε.le
      (sq_nonneg (primeField F c P x - primeField F d Q x / ε)), key]
  have hl : Integrable fun x => 2 * (primeField F c P x * primeField F d Q x) :=
    (integrable_primeField_mul hF hFc P Q c d).const_mul 2
  have hr : Integrable fun x =>
      ε * primeField F c P x ^ 2 + ε⁻¹ * primeField F d Q x ^ 2 :=
    ((integrable_primeField_sq hF hFc P c).const_mul ε).add
      ((integrable_primeField_sq hF hFc Q d).const_mul ε⁻¹)
  have hmono := MeasureTheory.integral_mono hl hr hpt
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add ((integrable_primeField_sq hF hFc P c).const_mul ε)
      ((integrable_primeField_sq hF hFc Q d).const_mul ε⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-- **Cauchy–Schwarz between two weight families.** -/
theorem abs_sum_cross_gram_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (P Q : Finset ℕ) (c d : ℕ → ℝ) :
    |∑ m ∈ P, ∑ n ∈ Q, c m * d n * autoCorrelation F (Real.log n - Real.log m)|
      ≤ Real.sqrt ((∫ x, primeField F c P x ^ 2) * ∫ x, primeField F d Q x ^ 2) := by
  have hPnn : (0:ℝ) ≤ ∫ x, primeField F c P x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hQnn : (0:ℝ) ≤ ∫ x, primeField F d Q x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hup : (∫ x, primeField F c P x * primeField F d Q x)
      ≤ Real.sqrt ((∫ x, primeField F c P x ^ 2) * ∫ x, primeField F d Q x ^ 2) :=
    le_sqrt_mul_of_two_mul_le hPnn hQnn fun ε hε =>
      two_mul_integral_primeField_mul_le hF hFc P Q c d hε
  have hlow : -(∫ x, primeField F c P x * primeField F d Q x)
      ≤ Real.sqrt ((∫ x, primeField F c P x ^ 2) * ∫ x, primeField F d Q x ^ 2) := by
    have hneg : (∫ x, primeField F (fun n => -c n) P x * primeField F d Q x)
        = -∫ x, primeField F c P x * primeField F d Q x := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show primeField F (fun n => -c n) P x * primeField F d Q x
        = -(primeField F c P x * primeField F d Q x)
      rw [primeField_neg, neg_mul]
    have hsq : (∫ x, primeField F (fun n => -c n) P x ^ 2)
        = ∫ x, primeField F c P x ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show primeField F (fun n => -c n) P x ^ 2 = primeField F c P x ^ 2
      rw [primeField_neg, neg_sq]
    have := le_sqrt_mul_of_two_mul_le (by rw [hsq]; exact hPnn) hQnn
      (fun ε hε => two_mul_integral_primeField_mul_le hF hFc P Q (fun n => -c n) d hε)
    rwa [hneg, hsq] at this
  rw [sum_cross_gram_eq_integral hF hFc P Q c d]
  exact abs_le.mpr ⟨by linarith, hup⟩


/-! ### The whole balance is one inner product

Collecting the two sides, the ledger of a test is the test paired with a single field: the
arithmetic field of its translates at the prime lags, minus the rank-one polar field
`2(∫F e^{x/2})e^{−x/2}`.  The Chebyshev residue is exactly that pairing, so the tests with zero
residue are precisely those orthogonal to their own ledger field. -/

/-- The ledger field of a test: its arithmetic field minus the rank-one polar field. -/
def ledgerField (F : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  primeField F (fun n => 2 * (Real.sqrt n)⁻¹ * (ArithmeticFunction.vonMangoldt n : ℝ))
      (Finset.range (N + 1)) x
    - 2 * expMomentPos F * Real.exp (-x / 2)

theorem integral_mul_polarRankOne (F : ℝ → ℝ) :
    (∫ x, F x * (2 * expMomentPos F * Real.exp (-x / 2)))
      = 2 * expMomentPos F * expMomentNeg F := by
  rw [expMomentNeg, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F x * (2 * expMomentPos F * Real.exp (-x / 2))
    = 2 * expMomentPos F * (F x * Real.exp (-x / 2))
  ring

/-- **The balance as a single pairing.** -/
theorem testBalance_field (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∫ x, F x * ledgerField F N x)
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hprime : Integrable fun x => F x *
      primeField F (fun n => 2 * (Real.sqrt n)⁻¹ * (ArithmeticFunction.vonMangoldt n : ℝ))
        (Finset.range (N + 1)) x :=
    integrable_mul_primeField hF.continuous hFc _ _
  have hpolar : Integrable fun x => F x * (2 * expMomentPos F * Real.exp (-x / 2)) :=
    (hF.continuous.mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_neg.div_const 2)))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsplit : (∫ x, F x * ledgerField F N x)
      = (∫ x, F x *
          primeField F (fun n => 2 * (Real.sqrt n)⁻¹ * (ArithmeticFunction.vonMangoldt n : ℝ))
            (Finset.range (N + 1)) x)
        - ∫ x, F x * (2 * expMomentPos F * Real.exp (-x / 2)) := by
    rw [← MeasureTheory.integral_sub hprime hpolar]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * ledgerField F N x
      = F x * primeField F (fun n => 2 * (Real.sqrt n)⁻¹ *
            (ArithmeticFunction.vonMangoldt n : ℝ)) (Finset.range (N + 1)) x
        - F x * (2 * expMomentPos F * Real.exp (-x / 2))
    rw [ledgerField]
    ring
  rw [hsplit, integral_mul_polarRankOne F,
    ← sum_lag_eq_integral_primeField hF.continuous hFc]
  have hb := testBalance_poleplane hF hFc hr hsupp hN
  rw [poleplane_eq_moment_mul hF.continuous hFc] at hb
  rw [← hb]
  have hsum : ∑ n ∈ Finset.range (N + 1),
        2 * (Real.sqrt n)⁻¹ * (ArithmeticFunction.vonMangoldt n : ℝ) *
          autoCorrelation F (Real.log n)
      = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hsum]
  ring



/-! ### The tower discount, from below

The content of the tower laws is the fold defect `A(0) − A(log p)` at a prime lag.  The aperture
laws make it quantitative: at every positive lag the defect is at least the mass times
`min(u²/8r², ½)` — quadratic in the lag below the aperture, and a full half past it.  No test can
make its own tower discount small at a prime of moderate size. -/

/-- **The displacement energy from below, at every positive lag.** -/
theorem displacement_ge_min (hF : Continuous F) (hFc : HasCompactSupport F) {r u : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hu : 0 < u) :
    autoCorrelation F 0 * min (u ^ 2 / (8 * r ^ 2)) (1 / 2) ≤ displacement F u := by
  have hA0 := autoCorrelation_zero_nonneg F
  simp only [displacement]
  rcases le_or_gt u r with hle | hgt
  · have h := autoCorrelation_le_quadratic hF hFc hsupp hu hle
    have hstep : autoCorrelation F 0 * min (u ^ 2 / (8 * r ^ 2)) (1 / 2)
        ≤ autoCorrelation F 0 * (u ^ 2 / (8 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hA0
    nlinarith [h, hstep]
  · have h := autoCorrelation_le_half hF hFc hsupp hgt
    have hstep : autoCorrelation F 0 * min (u ^ 2 / (8 * r ^ 2)) (1 / 2)
        ≤ autoCorrelation F 0 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hA0
    nlinarith [h, hstep]

/-- **The tower discount at a prime lag is bounded below.** -/
theorem fold_defect_ge (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {p : ℕ} (hp : 2 ≤ p) :
    autoCorrelation F 0 * min (Real.log p ^ 2 / (8 * r ^ 2)) (1 / 2)
      ≤ autoCorrelation F 0 - autoCorrelation F (Real.log p) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp
  exact displacement_ge_min hF hFc hsupp (Real.log_pos hp1)


/-! ### The reduced cost side, with its gain

Weighting the prime lags by any nonnegative family and reading them through the test, the trivial
bound is the mass times the `ℓ¹` weight.  The tower discount improves it termwise: each prime `p`
is read at most at `A(0)(1 − min(log²p/8r², ½))`, so the cost side carries an explicit gain
determined by how the prime logarithms sit inside the aperture. -/

/-- **The reduced cost side.**  Each prime is read below the mass by its own tower discount. -/
theorem sum_weight_mul_autoCorrelation_le (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) :
    ∑ p ∈ P, w p * autoCorrelation F (Real.log p)
      ≤ autoCorrelation F 0
        * ∑ p ∈ P, w p * (1 - min (Real.log p ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hd := fold_defect_ge hF hFc hsupp (hP p hp)
  have hterm : autoCorrelation F (Real.log p)
      ≤ autoCorrelation F 0 * (1 - min (Real.log p ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
    nlinarith [hd]
  calc w p * autoCorrelation F (Real.log p)
      ≤ w p * (autoCorrelation F 0 * (1 - min (Real.log p ^ 2 / (8 * r ^ 2)) (1 / 2))) :=
        mul_le_mul_of_nonneg_left hterm (hw p hp)
    _ = autoCorrelation F 0 * (w p * (1 - min (Real.log p ^ 2 / (8 * r ^ 2)) (1 / 2))) := by ring


/-! ### The coupling graph between dyadic windows

Two dyadic windows `k` steps apart are coupled through the lag `k log 2`.  The aperture laws
describe that coupling completely: the edge weight is at most `A(0)(1 − min(k²log²2/8r², ½))`, and
it is exactly zero once `k log 2 ≥ 2r`.  So the coupling graph of a test of aperture `r` has
degree at most `2r/log 2`, with edge weights that fall off quadratically in the window distance
until they stop. -/

/-- The aperture laws in one statement: the correlation at a positive lag is below the mass by at
least the quadratic gap, or by a half past the aperture. -/
theorem autoCorrelation_le_min (hF : Continuous F) (hFc : HasCompactSupport F) {r u : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hu : 0 < u) :
    autoCorrelation F u ≤ autoCorrelation F 0 * (1 - min (u ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  have hd := displacement_ge_min hF hFc hsupp hu
  simp only [displacement] at hd
  nlinarith [hd]

/-- **The edge weight of the coupling graph.** -/
theorem window_coupling_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {k : ℕ} (hk : 1 ≤ k) :
    autoCorrelation F ((k : ℝ) * Real.log 2)
      ≤ autoCorrelation F 0
        * (1 - min (((k : ℝ) * Real.log 2) ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact autoCorrelation_le_min hF hFc hsupp (by nlinarith)

/-- **The coupling graph is banded.**  Windows farther apart than the aperture do not couple. -/
theorem window_coupling_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {k : ℕ} (hk : 2 * r ≤ (k : ℝ) * Real.log 2) :
    autoCorrelation F ((k : ℝ) * Real.log 2) = 0 :=
  autoCorrelation_eq_zero hF hr hsupp hk

/-- **The degree of the coupling graph.** -/
theorem window_degree_lt (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {k : ℕ}
    (hk : autoCorrelation F ((k : ℝ) * Real.log 2) ≠ 0) :
    (k : ℝ) * Real.log 2 < 2 * r := by
  by_contra hc
  exact hk (window_coupling_eq_zero hF hr hsupp (not_lt.mp hc))


/-! ### The ideal source: the two-pole calibration is achievable

Differencing the two-pole weight at the integer scales produces an integer-indexed source whose
prefix matches the calibration exactly at every integer, so its defect is a sawtooth that vanishes
there and never exceeds `1 + log 2` anywhere.  Its weights are `1 + log(1 + 1/(n−1))`, that is,
*every integer carries weight about one* — the pole at `1` as an arithmetic.  So an `O(1)` defect
is neither automatic nor impossible: the entire content of the Chebyshev ledger is that the
weight is `Λ`, whose prefix matches the same calibration although its atoms do not. -/

/-- The source realising the two-pole calibration at the integer scales. -/
def idealSource : ℕ → ℝ := sourceOfPrefix fun n => twoPoleWeight (Real.log (n : ℝ))

theorem twoPoleWeight_mono : Monotone twoPoleWeight := by
  intro a b hab
  simp only [twoPoleWeight]
  have := Real.exp_le_exp.mpr hab
  linarith

theorem twoPoleWeight_log_nat {n : ℕ} (hn : 1 ≤ n) :
    twoPoleWeight (Real.log (n : ℝ)) = (n : ℝ) + Real.log (n : ℝ) - 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [twoPoleWeight, Real.exp_log hn0]

/-- Every integer carries weight about one. -/
theorem idealSource_apply {n : ℕ} (hn : 2 ≤ n) :
    idealSource n = 1 + (Real.log (n : ℝ) - Real.log ((n : ℝ) - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1:ℕ) ≤ n := hn1
    push_cast [Nat.cast_sub this]
    ring
  rw [idealSource, sourceOfPrefix, if_neg (by omega : ¬ (n = 0)),
    twoPoleWeight_log_nat hn1, hsub,
    twoPoleWeight, Real.exp_log (by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith)]
  ring

theorem lagPrefix_idealSource (s : ℝ) :
    lagPrefix idealSource s = twoPoleWeight (Real.log (⌊Real.exp s⌋₊ : ℝ)) := by
  rw [idealSource, lagPrefix_sourceOfPrefix]
  simp [twoPoleWeight]

/-- **The defect of the ideal source is a bounded sawtooth.** -/
theorem abs_lagSourceDefect_idealSource_le {s : ℝ} (hs : 0 ≤ s) :
    |lagSourceDefect idealSource s| ≤ 1 + Real.log 2 := by
  set N : ℕ := ⌊Real.exp s⌋₊ with hNdef
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexp1)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hNlt : Real.exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogN : Real.log (N : ℝ) ≤ s := by
    have := Real.log_le_log hN0 hNle
    rwa [Real.log_exp] at this
  have hlogN1 : s < Real.log ((N : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos s) hNlt
    rwa [Real.log_exp] at this
  have hlower : 0 ≤ lagSourceDefect idealSource s := by
    rw [lagSourceDefect, lagPrefix_idealSource]
    have := twoPoleWeight_mono hlogN
    linarith
  have hgap : Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) ≤ Real.log 2 := by
    have h2N : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1:ℝ) ≤ N := by exact_mod_cast hN1
      linarith
    have hmul := Real.log_le_log (by linarith) h2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hN0)] at hmul
    linarith
  have hupper : lagSourceDefect idealSource s ≤ 1 + Real.log 2 := by
    rw [lagSourceDefect, lagPrefix_idealSource]
    have hmono := twoPoleWeight_mono (le_of_lt hlogN1)
    have hval : twoPoleWeight (Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1)
        + Real.log ((N : ℝ) + 1) - 1 := by
      rw [twoPoleWeight, Real.exp_log (by linarith)]
    have hvalN : twoPoleWeight (Real.log (N : ℝ)) = (N : ℝ) + Real.log (N : ℝ) - 1 :=
      twoPoleWeight_log_nat hN1
    rw [hvalN]
    rw [hval] at hmono
    linarith
  rw [abs_of_nonneg hlower]
  exact hupper


/-! ### What separates `ζ` from the ideal source

The ideal source's own ledger is uniformly `O(1)` against any test, and the difference between
`ζ`'s ledger and it is exactly the prime number theorem's error paired with the derivative of the
test.  The whole arithmetic content of the balance is that one difference. -/

theorem idealSource_zero : idealSource 0 = 0 := by
  rw [idealSource, sourceOfPrefix]
  simp

theorem idealSource_one : idealSource 1 = 0 := by
  rw [idealSource, sourceOfPrefix]
  simp

/-- **The ideal source's ledger is uniformly bounded.** -/
theorem abs_ledger_idealSource_le (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), idealSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s|
      ≤ (1 + Real.log 2) * ∫ s in Ioi (0:ℝ), |deriv h s| := by
  rw [sum_weight_sub_polar_eq_defect idealSource idealSource_zero idealSource_one hh hS hvan hN]
  refine le_trans abs_integral_le_integral_abs ?_
  have hint : IntegrableOn (fun s => |deriv h s|) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
    have h1 : IntegrableOn (fun s => |deriv h s|) (Ioc (0:ℝ) S) :=
      ((hdc.abs).integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => |deriv h s|) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, abs_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hmaj : ∀ s ∈ Ioi (0:ℝ),
      |lagSourceDefect idealSource s * deriv h s| ≤ (1 + Real.log 2) * |deriv h s| := by
    intro s hs
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_lagSourceDefect_idealSource_le (le_of_lt hs)) (abs_nonneg _)
  have hintabs : IntegrableOn (fun s => |lagSourceDefect idealSource s * deriv h s|)
      (Ioi (0:ℝ)) :=
    (integrableOn_Ioi_lagSourceDefect_mul_deriv idealSource hh hS hvan hN).abs
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_mono_on hintabs (hint.const_mul _) measurableSet_Ioi hmaj

/-- **What separates `ζ` from the ideal source** is exactly the prime number theorem's error. -/
theorem ledger_vonMangoldt_sub_ideal (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n))
        - ∑ n ∈ Finset.range (N + 1), idealSource n * h (Real.log n)
      = ∫ s in Ioi (0:ℝ),
          (twoPoleWeight (Real.log (⌊Real.exp s⌋₊ : ℝ)) - lagChebyshev s) * deriv h s := by
  rw [ledger_difference_eq _ idealSource (by simp) (by simp) idealSource_zero idealSource_one
    hh hS hvan hN]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [lagPrefix_idealSource, lagChebyshev_eq_lagPrefix]


/-! ### Every source's defect is a ledger reading

The mollified readout is not special to `Λ`: for an arbitrary source the ledger on the tail of a
bump returns `−∫ (defect)·φ` exactly, and on the double tail it returns the source's own
critical-scale functional.  With realisation and rigidity this closes the question of what the
ledger exposes: it exposes the defect as a distribution, and the defect determines the source
index by index. -/

/-- The critical-scale functional of an arbitrary source. -/
def sourceScalePrefix (a : ℕ → ℝ) (s : ℝ) : ℝ := ∫ u in (0:ℝ)..s, lagSourceDefect a u

/-- For `Λ` the source's critical-scale functional is the receiver plus the elementary half. -/
theorem sourceScalePrefix_vonMangoldt (s : ℝ) :
    sourceScalePrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s
      = criticalScalePrefix s + s ^ 2 / 2 - s := by
  have hsplit : (∫ u in (0:ℝ)..s,
        lagSourceDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) u)
      = (∫ u in (0:ℝ)..s, (Real.exp u - lagChebyshev u)) + ∫ u in (0:ℝ)..s, (u - 1) := by
    have hint2 : IntervalIntegrable (fun u : ℝ => u - 1) volume 0 s :=
      (continuous_id.sub continuous_const).intervalIntegrable 0 s
    rw [← intervalIntegral.integral_add (intervalIntegrable_criticalScaleIntegrand 0 s) hint2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show lagSourceDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) u
      = (Real.exp u - lagChebyshev u) + (u - 1)
    rw [← chebyshevTwoPoleDefect_eq_lagSourceDefect, chebyshevTwoPoleDefect, twoPoleWeight]
    ring
  rw [sourceScalePrefix, hsplit, criticalScalePrefix]
  have hlin : (∫ u in (0:ℝ)..s, (u - 1)) = s ^ 2 / 2 - s := by
    have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) s,
        HasDerivAt (fun y : ℝ => y ^ 2 / 2 - y) (u - 1) u := by
      intro u _
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) u u := by
        simpa using (hasDerivAt_pow 2 u).div_const 2
      have h2 : HasDerivAt (fun y : ℝ => y) 1 u := hasDerivAt_id u
      exact h1.sub h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_id.sub continuous_const).intervalIntegrable 0 s)]
    simp
  rw [hlin]
  ring

/-- **The mollified defect of an arbitrary source.** -/
theorem sum_weight_sub_polar_tailWeight (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hφ : Continuous φ) (hS : 0 < S) (hφ0 : ∀ t, S ≤ t → φ t = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * tailWeight φ S (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * tailWeight φ S s
      = -∫ s in Ioi (0:ℝ), lagSourceDefect a s * φ s := by
  have hkey := sum_weight_sub_polar_eq_defect a ha0 ha1 (contDiff_one_tailWeight hφ S) hS
    (fun s hs => tailWeight_eq_zero hφ0 hs) hN
  rw [hkey, setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [(hasDerivAt_tailWeight hφ S s).deriv]; ring :
        ∀ s ∈ Ioi (0:ℝ), lagSourceDefect a s * deriv (tailWeight φ S) s
          = -(lagSourceDefect a s * φ s)),
    MeasureTheory.integral_neg]

/-- Two sources with the same mollified defect against every bump have the same reading. -/
theorem ledger_eq_of_defect_integral_eq (a b : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hφ : Continuous φ) (hS : 0 < S)
    (hφ0 : ∀ t, S ≤ t → φ t = 0) {N : ℕ} (hN : Real.exp S ≤ N)
    (heq : (∫ s in Ioi (0:ℝ), lagSourceDefect a s * φ s)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect b s * φ s) :
    (∑ n ∈ Finset.range (N + 1), a n * tailWeight φ S (Real.log n))
      = ∑ n ∈ Finset.range (N + 1), b n * tailWeight φ S (Real.log n) := by
  have ha := sum_weight_sub_polar_tailWeight a ha0 ha1 hφ hS hφ0 hN
  have hb := sum_weight_sub_polar_tailWeight b hb0 hb1 hφ hS hφ0 hN
  rw [heq] at ha
  linarith


/-! ### The autocorrelation of an odd test has zero mass

Integrating the autocorrelation over all lags returns the square of the test's own integral, so on
an odd test it is zero.  An odd test with positive mass therefore has an autocorrelation that is
*negative somewhere*: the Gram kernel of the translate family is not a positive kernel, and the
prime side necessarily carries terms of both signs.  No argument that treats the prime side as a
sum of nonnegative contributions can work on the odd cone. -/

theorem hasCompactSupport_pair {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport fun p : ℝ × ℝ => F p.2 * F (p.2 + p.1) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(2 * r)) (b := 2 * r)).prod (isCompact_Icc (a := -r) (b := r)))
    fun p hp => ?_
  by_cases hx : r < |p.2|
  · rw [hsupp p.2 hx]; ring
  by_cases hxs : r < |p.2 + p.1|
  · rw [hsupp _ hxs]; ring
  exfalso
  refine hp ⟨?_, Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hx))⟩
  have h1 := abs_le.mp (not_lt.mp hx)
  have h2 := abs_le.mp (not_lt.mp hxs)
  exact Set.mem_Icc.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩

/-- **The total mass of the autocorrelation is the square of the test's integral.** -/
theorem integral_autoCorrelation (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) :
    (∫ t, autoCorrelation F t) = (∫ x, F x) ^ 2 := by
  have hcont : Continuous fun p : ℝ × ℝ => F p.2 * F (p.2 + p.1) := by fun_prop
  have hint : Integrable fun p : ℝ × ℝ => F p.2 * F (p.2 + p.1) :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_pair hsupp)
  have hvp : ((volume : Measure ℝ).prod volume) = (volume : Measure (ℝ × ℝ)) :=
    (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
  have hintprod : Integrable (Function.uncurry fun (s : ℝ) (x : ℝ) => F x * F (x + s))
      ((volume : Measure ℝ).prod volume) := hvp ▸ hint
  have hswap := MeasureTheory.integral_integral_swap hintprod
  have hF1 : Integrable F := hF.integrable_of_hasCompactSupport hFc
  have hinner : ∀ x : ℝ, (∫ s, F x * F (x + s)) = F x * ∫ u, F u := by
    intro x
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have htr := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ)) F x
    rw [← htr]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show F (x + s) = F (s + x)
    rw [add_comm]
  calc (∫ t, autoCorrelation F t) = ∫ s, ∫ x, F x * F (x + s) := rfl
    _ = ∫ x, ∫ s, F x * F (x + s) := hswap
    _ = ∫ x, F x * ∫ u, F u :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = (∫ x, F x) ^ 2 := by rw [MeasureTheory.integral_mul_const]; ring

/-- **The autocorrelation of an odd test has zero total mass.** -/
theorem integral_autoCorrelation_odd (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) :
    (∫ t, autoCorrelation F t) = 0 := by
  rw [integral_autoCorrelation hF hFc hsupp, integral_eq_zero_of_odd hodd]
  ring

/-- **An odd test's Gram kernel is not positive.**  Some lag is read negatively. -/
theorem exists_autoCorrelation_neg (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x)
    (hpos : 0 < autoCorrelation F 0) :
    ∃ t, autoCorrelation F t < 0 := by
  by_contra hcon
  have hc : ∀ t, 0 ≤ autoCorrelation F t := fun t => not_lt.mp fun h => hcon ⟨t, h⟩
  have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
  have hAcs : HasCompactSupport (autoCorrelation F) :=
    hasCompactSupport_autoCorrelation hF.continuous hr hsupp
  have hAi : Integrable (autoCorrelation F) := hAc.integrable_of_hasCompactSupport hAcs
  have hzero := integral_autoCorrelation_odd hF.continuous hFc hsupp hodd
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg hc hAi).mp hzero
  have heq : autoCorrelation F = 0 :=
    (Continuous.ae_eq_iff_eq (μ := (volume : Measure ℝ)) hAc continuous_const).mp hae
  rw [heq] at hpos
  simp at hpos


/-! ### How much negative mass an odd test must carry

The autocorrelation of an odd test is near its maximum on a window whose width is set by the
test's regularity, and its total mass is zero.  So outside that window it integrates to at least
the window's width times the mass, with a minus sign: an odd test must spend a definite amount of
negative correlation at the far lags.  That negative mass is what the prime side reads at the
large lags, and it is forced, not chosen. -/

/-- Near the origin the autocorrelation stays above half the mass. -/
theorem autoCorrelation_ge_half_of_mem (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r M δ : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hM : ∀ x, |deriv F x| ≤ M)
    (hδr : δ ≤ r) (hδM : 16 * M ^ 2 * δ ^ 2 * r ≤ autoCorrelation F 0)
    {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) :
    autoCorrelation F 0 / 2 ≤ autoCorrelation F t := by
  have hA0 := autoCorrelation_zero_nonneg F
  obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
  have habst : |t| ≤ δ := abs_le.mpr ⟨ht1, ht2⟩
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg t) habst
  have hlip := abs_autoCorrelation_sub_le_lipschitz hF hFc hr hsupp hM t 0
  rw [sub_zero] at hlip
  have hinner : autoCorrelation F 0 * (M ^ 2 * t ^ 2 * (2 * r + 2 * |t|))
      ≤ (autoCorrelation F 0 / 2) ^ 2 := by
    have ht2le : t ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs t]
      nlinarith [abs_nonneg t, habst]
    have habsr : |t| ≤ r := le_trans habst hδr
    have hfac : M ^ 2 * t ^ 2 * (2 * r + 2 * |t|) ≤ 4 * M ^ 2 * δ ^ 2 * r := by
      have hle4r : 2 * r + 2 * |t| ≤ 4 * r := by linarith
      have hstep1 : M ^ 2 * t ^ 2 * (2 * r + 2 * |t|) ≤ M ^ 2 * t ^ 2 * (4 * r) :=
        mul_le_mul_of_nonneg_left hle4r (by positivity)
      have hstep2 : M ^ 2 * t ^ 2 * (4 * r) ≤ M ^ 2 * δ ^ 2 * (4 * r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht2le (sq_nonneg M))
          (by linarith)
      linarith
    nlinarith [hA0, hfac, hδM]
  have hsqrt : Real.sqrt (autoCorrelation F 0 * (M ^ 2 * t ^ 2 * (2 * r + 2 * |t|)))
      ≤ autoCorrelation F 0 / 2 := by
    rw [show autoCorrelation F 0 / 2 = Real.sqrt ((autoCorrelation F 0 / 2) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hinner
  have := le_trans hlip hsqrt
  have hb := abs_le.mp this
  linarith [hb.1]

/-- **The forced negative mass of an odd test.** -/
theorem integral_compl_autoCorrelation_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r M δ : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hM : ∀ x, |deriv F x| ≤ M)
    (hodd : ∀ x, F (-x) = -F x) (hδ0 : 0 ≤ δ) (hδr : δ ≤ r)
    (hδM : 16 * M ^ 2 * δ ^ 2 * r ≤ autoCorrelation F 0) :
    (∫ t in (Set.Icc (-δ) δ)ᶜ, autoCorrelation F t) ≤ -(δ * autoCorrelation F 0) := by
  have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
  have hAcs : HasCompactSupport (autoCorrelation F) :=
    hasCompactSupport_autoCorrelation hF.continuous hr hsupp
  have hAi : Integrable (autoCorrelation F) := hAc.integrable_of_hasCompactSupport hAcs
  have hzero := integral_autoCorrelation_odd hF.continuous hFc hsupp hodd
  have hsplit := MeasureTheory.integral_add_compl
    (measurableSet_Icc (a := -δ) (b := δ)) hAi
  have hmono := MeasureTheory.setIntegral_mono_on
    (integrableOn_const (C := autoCorrelation F 0 / 2) (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    hAi.integrableOn measurableSet_Icc
    (fun t ht => autoCorrelation_ge_half_of_mem hF hFc hr hsupp hM hδr hδM ht)
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
    max_eq_left (by linarith : (0:ℝ) ≤ δ - -δ)] at hmono
  have hlow : δ * autoCorrelation F 0 ≤ ∫ t in Set.Icc (-δ) δ, autoCorrelation F t := by
    calc δ * autoCorrelation F 0 = (δ - -δ) * (autoCorrelation F 0 / 2) := by ring
      _ ≤ ∫ t in Set.Icc (-δ) δ, autoCorrelation F t := hmono
  linarith [hsplit, hzero, hlow]


/-! ### Which poles an integer-indexed system can calibrate

Between consecutive integers a source's prefix is frozen while the calibration at `ρ` keeps
growing, so the defect must absorb the whole increment of the calibration across the cell.  For
`ρ > 1` that increment is at least `N^{ρ−1}/2ρ`, which is unbounded: **no integer-indexed source
has a bounded defect against a pole beyond `1`.**  Together with the ideal source, which realises
the pole at `1` to `O(1)`, this says that `1` is exactly the largest pole an integer system can
calibrate — the arithmetic origin of the two-pole weight. -/

theorem exp_mul_log (ρ : ℝ) {x : ℝ} (hx : 0 < x) : Real.exp (ρ * Real.log x) = x ^ ρ := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

theorem lagPrefix_eq_on_half_cell (a : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    lagPrefix a (Real.log ((N : ℝ) + 1 / 2)) = lagPrefix a (Real.log (N : ℝ)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hfl1 : ⌊Real.exp (Real.log ((N : ℝ) + 1 / 2))⌋₊ = N := by
    rw [Real.exp_log (by linarith), Nat.floor_eq_iff (by linarith)]
    constructor <;> [linarith; (push_cast; linarith)]
  have hfl2 : ⌊Real.exp (Real.log (N : ℝ))⌋₊ = N := by
    rw [Real.exp_log hN0, Nat.floor_natCast]
  rw [lagPrefix, lagPrefix, hfl1, hfl2]

/-- The calibration's increment across half a cell. -/
theorem poleWeightAt_half_cell_ge {ρ : ℝ} (hρ : 1 ≤ ρ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (ρ - 1) / (2 * ρ)
      ≤ poleWeightAt ρ (Real.log ((N : ℝ) + 1 / 2)) - poleWeightAt ρ (Real.log (N : ℝ)) := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hx : (0:ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hpow : ∀ y : ℝ, 0 < y → y ^ ρ = y * y ^ (ρ - 1) := by
    intro y hy
    have h := Real.rpow_add hy 1 (ρ - 1)
    rw [show (1:ℝ) + (ρ - 1) = ρ by ring, Real.rpow_one] at h
    exact h
  have hmono : (N : ℝ) ^ (ρ - 1) ≤ ((N : ℝ) + 1 / 2) ^ (ρ - 1) :=
    Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
  have hnn : (0:ℝ) ≤ (N : ℝ) ^ (ρ - 1) := Real.rpow_nonneg hN0.le _
  have hdiff : (N : ℝ) ^ (ρ - 1) / 2 ≤ ((N : ℝ) + 1 / 2) ^ ρ - (N : ℝ) ^ ρ := by
    rw [hpow _ hx, hpow _ hN0]
    nlinarith [hmono, hnn, hN0]
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) :=
    Real.log_le_log hN0 (by linarith)
  have hval1 : poleWeightAt ρ (Real.log ((N : ℝ) + 1 / 2))
      = (((N : ℝ) + 1 / 2) ^ ρ - 1) / ρ + Real.log ((N : ℝ) + 1 / 2) := by
    rw [poleWeightAt, exp_mul_log ρ hx]
  have hval2 : poleWeightAt ρ (Real.log (N : ℝ))
      = ((N : ℝ) ^ ρ - 1) / ρ + Real.log (N : ℝ) := by
    rw [poleWeightAt, exp_mul_log ρ hN0]
  rw [hval1, hval2]
  have hdiv : (N : ℝ) ^ (ρ - 1) / (2 * ρ)
      ≤ (((N : ℝ) + 1 / 2) ^ ρ - 1) / ρ - ((N : ℝ) ^ ρ - 1) / ρ := by
    rw [div_sub_div_same, div_le_div_iff₀ (by linarith) hρ0]
    nlinarith [hdiff, hρ0]
  linarith

/-- **No integer source calibrates a pole beyond `1` to `O(1)`.** -/
theorem defect_half_cell_lower_bound (a : ℕ → ℝ) {ρ : ℝ} (hρ : 1 ≤ ρ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (ρ - 1) / (4 * ρ)
      ≤ max |lagSourceDefectAt ρ a (Real.log (N : ℝ))|
            |lagSourceDefectAt ρ a (Real.log ((N : ℝ) + 1 / 2))| := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hinc := poleWeightAt_half_cell_ge hρ hN
  have hpref := lagPrefix_eq_on_half_cell a hN
  have hdef : lagSourceDefectAt ρ a (Real.log ((N : ℝ) + 1 / 2))
      - lagSourceDefectAt ρ a (Real.log (N : ℝ))
      = poleWeightAt ρ (Real.log ((N : ℝ) + 1 / 2))
        - poleWeightAt ρ (Real.log (N : ℝ)) := by
    rw [lagSourceDefectAt, lagSourceDefectAt, hpref]
    ring
  set x := lagSourceDefectAt ρ a (Real.log (N : ℝ)) with hxdef
  set y := lagSourceDefectAt ρ a (Real.log ((N : ℝ) + 1 / 2)) with hydef
  have hsum : (N : ℝ) ^ (ρ - 1) / (2 * ρ) ≤ |x| + |y| := by
    have : (N : ℝ) ^ (ρ - 1) / (2 * ρ) ≤ y - x := by rw [hdef]; exact hinc
    have hb1 := neg_abs_le x
    have hb2 := le_abs_self y
    linarith
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  have h2 : (0:ℝ) < 2 * ρ := by linarith
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * ρ)]
  rw [div_le_iff₀ h2] at hsum
  have hprod : (|x| + |y|) * (2 * ρ) ≤ (max |x| |y| * 2) * (2 * ρ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith


/-! ### And which poles it can calibrate

For every `0 < ρ ≤ 1` the calibration at `ρ` *is* realisable by an integer source, with defect at
most `1/ρ + log 2`: differencing it at the integers works because `x ↦ x^ρ` is subadditive there.
With the previous dichotomy this settles the range completely — an integer-indexed system can
calibrate exactly the poles `ρ ≤ 1`, and `ρ = 1` is the extreme case, which is the two-pole
weight. -/

theorem poleWeightAt_mono {ρ : ℝ} (hρ : 0 < ρ) : Monotone (poleWeightAt ρ) := by
  intro a b hab
  simp only [poleWeightAt]
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hρ.le)
  have h2 : (Real.exp (ρ * a) - 1) / ρ ≤ (Real.exp (ρ * b) - 1) / ρ := by
    rw [div_le_div_iff₀ hρ hρ]
    nlinarith [h, hρ]
  linarith

/-- The source realising the calibration at `ρ` on the integer scales. -/
def idealSourceAt (ρ : ℝ) : ℕ → ℝ := sourceOfPrefix fun n => poleWeightAt ρ (Real.log (n : ℝ))

theorem lagPrefix_idealSourceAt (ρ : ℝ) (s : ℝ) :
    lagPrefix (idealSourceAt ρ) s = poleWeightAt ρ (Real.log (⌊Real.exp s⌋₊ : ℝ)) := by
  rw [idealSourceAt, lagPrefix_sourceOfPrefix]
  simp [poleWeightAt]

/-- **The calibration at every `ρ ≤ 1` is realisable to `O(1)`.** -/
theorem abs_lagSourceDefectAt_idealSourceAt_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {s : ℝ}
    (hs : 0 ≤ s) :
    |lagSourceDefectAt ρ (idealSourceAt ρ) s| ≤ 1 / ρ + Real.log 2 := by
  set N : ℕ := ⌊Real.exp s⌋₊ with hNdef
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexp1)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hNlt : Real.exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogN : Real.log (N : ℝ) ≤ s := by
    have := Real.log_le_log hN0 hNle
    rwa [Real.log_exp] at this
  have hlogN1 : s < Real.log ((N : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos s) hNlt
    rwa [Real.log_exp] at this
  have hlower : 0 ≤ lagSourceDefectAt ρ (idealSourceAt ρ) s := by
    rw [lagSourceDefectAt, lagPrefix_idealSourceAt]
    have := poleWeightAt_mono hρ hlogN
    linarith
  have hgap : Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) ≤ Real.log 2 := by
    have h2N : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1:ℝ) ≤ N := by exact_mod_cast hN1
      linarith
    have hmul := Real.log_le_log (by linarith) h2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hN0)] at hmul
    linarith
  have hrpow : ((N : ℝ) + 1) ^ ρ ≤ (N : ℝ) ^ ρ + 1 := by
    have h := Real.rpow_add_le_add_rpow (a := (N : ℝ)) (b := 1) hN0.le zero_le_one hρ.le hρ1
    rwa [Real.one_rpow] at h
  have hval1 : poleWeightAt ρ (Real.log ((N : ℝ) + 1))
      = (((N : ℝ) + 1) ^ ρ - 1) / ρ + Real.log ((N : ℝ) + 1) := by
    rw [poleWeightAt, exp_mul_log ρ (by linarith : (0:ℝ) < (N : ℝ) + 1)]
  have hval2 : poleWeightAt ρ (Real.log (N : ℝ))
      = ((N : ℝ) ^ ρ - 1) / ρ + Real.log (N : ℝ) := by
    rw [poleWeightAt, exp_mul_log ρ hN0]
  have hincr : poleWeightAt ρ (Real.log ((N : ℝ) + 1)) - poleWeightAt ρ (Real.log (N : ℝ))
      ≤ 1 / ρ + Real.log 2 := by
    rw [hval1, hval2]
    have hdiv : (((N : ℝ) + 1) ^ ρ - 1) / ρ - ((N : ℝ) ^ ρ - 1) / ρ ≤ 1 / ρ := by
      rw [div_sub_div_same, div_le_div_iff₀ hρ hρ]
      nlinarith [hrpow, hρ]
    linarith
  have hupper : lagSourceDefectAt ρ (idealSourceAt ρ) s ≤ 1 / ρ + Real.log 2 := by
    rw [lagSourceDefectAt, lagPrefix_idealSourceAt]
    have hmono := poleWeightAt_mono hρ (le_of_lt hlogN1)
    linarith
  rw [abs_of_nonneg hlower]
  exact hupper


/-! ### A large atom forces a large defect

Across an integer the prefix jumps by the atom while the calibration moves by at most
`½ + log 2`, so the defect must change by at least the atom minus that.  Hence the defect of any
source is at least half its largest atom, up to the universal constant: the ledger cannot hide an
atom, which is source rigidity made quantitative.  In particular a source with unbounded weights
has an unbounded defect. -/

theorem lagPrefix_jump (a : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    lagPrefix a (Real.log ((N : ℝ) + 1)) - lagPrefix a (Real.log ((N : ℝ) + 1 / 2))
      = a (N + 1) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hfl1 : ⌊Real.exp (Real.log ((N : ℝ) + 1))⌋₊ = N + 1 := by
    rw [Real.exp_log (by linarith), Nat.floor_eq_iff (by linarith)]
    constructor <;> push_cast <;> linarith
  have hfl2 : ⌊Real.exp (Real.log ((N : ℝ) + 1 / 2))⌋₊ = N := by
    rw [Real.exp_log (by linarith), Nat.floor_eq_iff (by linarith)]
    exact ⟨by linarith, by linarith⟩
  rw [lagPrefix, lagPrefix, hfl1, hfl2, Finset.sum_Icc_succ_top (Nat.zero_le _)]
  ring

theorem twoPoleWeight_jump_le {N : ℕ} (hN : 1 ≤ N) :
    twoPoleWeight (Real.log ((N : ℝ) + 1)) - twoPoleWeight (Real.log ((N : ℝ) + 1 / 2))
      ≤ 1 / 2 + Real.log 2 ∧
    0 ≤ twoPoleWeight (Real.log ((N : ℝ) + 1))
      - twoPoleWeight (Real.log ((N : ℝ) + 1 / 2)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hv1 : twoPoleWeight (Real.log ((N : ℝ) + 1))
      = ((N : ℝ) + 1) + Real.log ((N : ℝ) + 1) - 1 := by
    rw [twoPoleWeight, Real.exp_log (by linarith)]
  have hv2 : twoPoleWeight (Real.log ((N : ℝ) + 1 / 2))
      = ((N : ℝ) + 1 / 2) + Real.log ((N : ℝ) + 1 / 2) - 1 := by
    rw [twoPoleWeight, Real.exp_log (by linarith)]
  have hmono : Real.log ((N : ℝ) + 1 / 2) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hgap : Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + 1 / 2) ≤ Real.log 2 := by
    have hle : (N : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1 / 2) := by linarith
    have hmul := Real.log_le_log (by linarith) hle
    rw [Real.log_mul (by norm_num) (by linarith : ((N : ℝ) + 1 / 2) ≠ 0)] at hmul
    linarith
  exact ⟨by rw [hv1, hv2]; linarith, by rw [hv1, hv2]; linarith⟩

/-- **The ledger cannot hide an atom.** -/
theorem defect_ge_of_atom (a : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (|a (N + 1)| - (1 / 2 + Real.log 2)) / 2
      ≤ max |lagSourceDefect a (Real.log ((N : ℝ) + 1 / 2))|
            |lagSourceDefect a (Real.log ((N : ℝ) + 1))| := by
  obtain ⟨hup, hlow⟩ := twoPoleWeight_jump_le hN
  have hjump := lagPrefix_jump a hN
  set p : ℝ := twoPoleWeight (Real.log ((N : ℝ) + 1))
    - twoPoleWeight (Real.log ((N : ℝ) + 1 / 2)) with hp
  set x := lagSourceDefect a (Real.log ((N : ℝ) + 1 / 2)) with hxdef
  set y := lagSourceDefect a (Real.log ((N : ℝ) + 1)) with hydef
  have hdiff : y - x = p - a (N + 1) := by
    rw [hxdef, hydef, lagSourceDefect, lagSourceDefect, hp]
    linarith [hjump]
  have habsp : |p| ≤ 1 / 2 + Real.log 2 := by
    rw [abs_of_nonneg hlow]; exact hup
  have hbig : |a (N + 1)| - (1 / 2 + Real.log 2) ≤ |x| + |y| := by
    have h1 : |a (N + 1)| - |p| ≤ |a (N + 1) - p| := abs_sub_abs_le_abs_sub _ _
    have h2 : |a (N + 1) - p| = |y - x| := by rw [hdiff, abs_sub_comm]
    have h3 : |y - x| ≤ |y| + |x| := abs_sub _ _
    linarith
  have hmax : |x| + |y| ≤ 2 * max |x| |y| := by
    have h1 : |x| ≤ max |x| |y| := le_max_left _ _
    have h2 : |y| ≤ max |x| |y| := le_max_right _ _
    linarith
  linarith


/-! ### The Chebyshev defect is unbounded

The atoms of `ζ` are the logarithms of the primes, which are unbounded, so the defect cannot stay
bounded: for every height some scale reads past it.  The receiver's one-sided bound is therefore
a statement about the *rate* of that growth, never about boundedness. -/

theorem exists_abs_chebyshevTwoPoleDefect_gt (K : ℝ) :
    ∃ s : ℝ, K < |chebyshevTwoPoleDefect s| := by
  set C : ℝ := 2 * K + 1 / 2 + Real.log 2 with hC
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp C⌉₊ + 2)
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : Real.exp C < (p : ℝ) := by
    have h1 : Real.exp C ≤ (⌈Real.exp C⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp C⌉₊ + 2 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hple
    push_cast at h2
    linarith
  have hlogp : C < Real.log (p : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos C) hpR
    rwa [Real.log_exp] at this
  set N : ℕ := p - 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : N + 1 = p := by omega
  have hatom : (ArithmeticFunction.vonMangoldt (N + 1) : ℝ) = Real.log (p : ℝ) := by
    rw [hNp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hkey := defect_ge_of_atom (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hN1
  rw [hatom] at hkey
  have hlogpos : 0 < Real.log (p : ℝ) := by
    have h2 : (1:ℝ) < p := by exact_mod_cast hp2
    exact Real.log_pos h2
  rw [abs_of_pos hlogpos] at hkey
  have hgt : K < max |lagSourceDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (Real.log ((N : ℝ) + 1 / 2))|
        |lagSourceDefect (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (Real.log ((N : ℝ) + 1))| := by
    have : K < (Real.log (p : ℝ) - (1 / 2 + Real.log 2)) / 2 := by rw [hC] at hlogp; linarith
    linarith
  rw [← chebyshevTwoPoleDefect_eq_lagSourceDefect] at hgt
  rcases lt_max_iff.mp hgt with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩


/-! ### The universal calibration dictionary

Nothing in the balance depends on the shape of the calibration: for *any* continuously
differentiable `W` vanishing at the origin, the reading of a source against a test and the
integral of `W′` against the test differ by exactly `W − prefix`, tested on `h′`.  The two-pole
weight and the calibrations at an arbitrary pole are instances; so is any comparison density one
might wish to compare a source with. -/

theorem integral_calibration_mul_deriv {W w : ℝ → ℝ} (hW0 : W 0 = 0) (hWc : Continuous W)
    (hwc : Continuous w) (hWd : ∀ s, HasDerivAt W (w s) s)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), W s * deriv h s) = -∫ s in Ioi (0:ℝ), w s * h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hA : (∫ s in Ioi (0:ℝ), W s * deriv h s) = ∫ s in (0:ℝ)..S, W s * deriv h s :=
    integral_Ioi_eq_intervalIntegral (hWc.mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  have hB : (∫ s in Ioi (0:ℝ), w s * h s) = ∫ s in (0:ℝ)..S, w s * h s :=
    integral_Ioi_eq_intervalIntegral (hwc.mul hh.continuous) hS
      (fun s hs => by rw [hvan s hs.le, mul_zero])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := W) (u' := w) (v := h) (v' := deriv h) (a := 0) (b := S)
    (fun x _ => hWd x) (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    (hwc.intervalIntegrable _ _) (hdc.intervalIntegrable _ _)
  rw [hA, hB, hparts, hvan S le_rfl, hW0]
  ring

/-- **The dictionary for an arbitrary calibration.** -/
theorem sum_weight_sub_calibration_eq_defect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {W w : ℝ → ℝ} (hW0 : W 0 = 0) (hWc : Continuous W) (hwc : Continuous w)
    (hWd : ∀ s, HasDerivAt W (w s) s) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), w s * h s
      = ∫ s in Ioi (0:ℝ), (W s - lagPrefix a s) * deriv h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hwi : IntegrableOn (fun s => W s * deriv h s) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => W s * deriv h s) (Ioc (0:ℝ) S) :=
      (((hWc.mul hdc)).integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => W s * deriv h s) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hpi := integrableOn_Ioi_lagPrefix_mul_deriv a hh hS hvan hN
  have hsplit : (∫ s in Ioi (0:ℝ), (W s - lagPrefix a s) * deriv h s)
      = (∫ s in Ioi (0:ℝ), W s * deriv h s)
        - ∫ s in Ioi (0:ℝ), lagPrefix a s * deriv h s := by
    rw [← MeasureTheory.integral_sub hwi hpi]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [sub_mul]
  rw [hsplit, integral_calibration_mul_deriv hW0 hWc hwc hWd hh hS hvan,
    sum_weight_mul_eq_neg_integral a ha0 ha1 hh hS hvan hN]
  ring


/-! ### The calibration of a conjugate pair of poles

A pair of poles at `β ± iγ` contributes the real density `e^{βs}cos(γs)`; its primitive vanishing
at the origin is elementary, so the universal dictionary gives the ledger that a system with such
a pair must be read with.  This is the comparison density for a Beurling system carrying an
off-line zero, and it is the test model the selectivity audits ask for. -/

/-- The calibration of a conjugate pair of poles at `β ± iγ`, together with the reflected pole. -/
def oscWeight (β γ s : ℝ) : ℝ :=
  (Real.exp (β * s) * (β * Real.cos (γ * s) + γ * Real.sin (γ * s)) - β) / (β ^ 2 + γ ^ 2) + s

theorem oscWeight_zero (β γ : ℝ) : oscWeight β γ 0 = 0 := by
  simp [oscWeight]

theorem continuous_oscWeight (β γ : ℝ) : Continuous (oscWeight β γ) := by
  unfold oscWeight
  fun_prop

theorem hasDerivAt_oscWeight {β γ : ℝ} (h : 0 < β ^ 2 + γ ^ 2) (s : ℝ) :
    HasDerivAt (oscWeight β γ) (Real.exp (β * s) * Real.cos (γ * s) + 1) s := by
  have hmβ : HasDerivAt (fun u : ℝ => β * u) β s := by simpa using (hasDerivAt_id s).const_mul β
  have hmγ : HasDerivAt (fun u : ℝ => γ * u) γ s := by simpa using (hasDerivAt_id s).const_mul γ
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (β * u)) (Real.exp (β * s) * β) s := hmβ.exp
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (γ * u)) (-Real.sin (γ * s) * γ) s := hmγ.cos
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (γ * u)) (Real.cos (γ * s) * γ) s := hmγ.sin
  have hinner : HasDerivAt (fun u : ℝ => β * Real.cos (γ * u) + γ * Real.sin (γ * u))
      (β * (-Real.sin (γ * s) * γ) + γ * (Real.cos (γ * s) * γ)) s :=
    (hcos.const_mul β).add (hsin.const_mul γ)
  have hg := hexp.mul hinner
  have hid : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
  have hfull := ((hg.sub_const β).div_const (β ^ 2 + γ ^ 2)).add hid
  refine hfull.congr_deriv ?_
  field_simp
  ring

/-- **The balance against a conjugate pair of poles.** -/
theorem sum_weight_sub_oscPolar_eq_defect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {β γ : ℝ} (hβγ : 0 < β ^ 2 + γ ^ 2) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp (β * s) * Real.cos (γ * s) + 1) * h s
      = ∫ s in Ioi (0:ℝ), (oscWeight β γ s - lagPrefix a s) * deriv h s :=
  sum_weight_sub_calibration_eq_defect a ha0 ha1 (oscWeight_zero β γ)
    (continuous_oscWeight β γ) (by fun_prop) (hasDerivAt_oscWeight hβγ) hh hS hvan hN


/-! ### Odd tests with a nonnegative half read the far lags nonpositively

For an odd test the left half is the reflected negative of the right half, so past the aperture
the correlation is minus the *convolution* of the right half with itself.  If the right half is
nonnegative, that convolution is nonnegative and the correlation is nonpositive at every lag
beyond the aperture: all the atoms past the aperture are read with the favourable sign, for free.
The sign of the far prime side is therefore a property of the half-test's own sign pattern, not of
the arithmetic. -/

theorem leftPart_eq_neg_rightPart_neg (hodd : ∀ x, F (-x) = -F x) (x : ℝ) :
    leftPart F x = -rightPart F (-x) := by
  rw [leftPart, rightPart]
  by_cases hx : x < 0
  · rw [if_pos hx, if_pos (by linarith : (0:ℝ) ≤ -x), hodd x]
    ring
  · rw [if_neg hx]
    by_cases h0 : (0:ℝ) ≤ -x
    · have hx0 : x = 0 := by linarith [not_lt.mp hx]
      subst hx0
      rw [if_pos h0, neg_zero, eq_zero_of_odd hodd]
      ring
    · rw [if_neg h0]
      ring

/-- **Past the aperture an odd test's correlation is minus a convolution.** -/
theorem autoCorrelation_eq_neg_conv (hodd : ∀ x, F (-x) = -F x) {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t) :
    autoCorrelation F t = -∫ y, rightPart F y * rightPart F (t - y) := by
  rw [autoCorrelation_eq_halves hsupp ht]
  have hstep : (∫ x, leftPart F x * rightPart F (x + t))
      = ∫ x, -(rightPart F (-x) * rightPart F (t - -x)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show leftPart F x * rightPart F (x + t) = -(rightPart F (-x) * rightPart F (t - -x))
    rw [leftPart_eq_neg_rightPart_neg hodd x, show t - -x = x + t by ring]
    ring
  rw [hstep, MeasureTheory.integral_neg]
  congr 1
  exact MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun y => rightPart F y * rightPart F (t - y))

/-- **An odd test with a nonnegative right half reads every far lag nonpositively.** -/
theorem autoCorrelation_nonpos_of_odd_nonneg (hodd : ∀ x, F (-x) = -F x) {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hnn : ∀ x, 0 ≤ x → 0 ≤ F x) (ht : r < t) :
    autoCorrelation F t ≤ 0 := by
  have hrp : ∀ y : ℝ, 0 ≤ rightPart F y := by
    intro y
    rw [rightPart]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]; exact hnn y hy
    · rw [if_neg hy]
  rw [autoCorrelation_eq_neg_conv hodd hsupp ht, neg_nonpos]
  exact MeasureTheory.integral_nonneg fun y => mul_nonneg (hrp y) (hrp (t - y))


/-! ### For such tests the prime side truncates at the aperture

Nonnegative atoms past the aperture are read nonpositively, so the whole prime side of an odd test
with a nonnegative half is bounded by its part below the aperture.  The far arithmetic can only
help; what must be controlled is the finite stretch of atoms inside the aperture. -/

theorem sum_lag_le_truncated (hodd : ∀ x, F (-x) = -F x) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hnn : ∀ x, 0 ≤ x → 0 ≤ F x) (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) {M N : ℕ} (hMN : M ≤ N) (hM : Real.exp r ≤ M) :
    ∑ n ∈ Finset.range (N + 1), c n * autoCorrelation F (Real.log n)
      ≤ ∑ n ∈ Finset.range (M + 1), c n * autoCorrelation F (Real.log n) := by
  have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsplit := Finset.sum_sdiff (f := fun n => c n * autoCorrelation F (Real.log n)) hsub
  have hnonpos : ∑ n ∈ Finset.range (N + 1) \ Finset.range (M + 1),
      c n * autoCorrelation F (Real.log n) ≤ 0 := by
    refine Finset.sum_nonpos fun n hn => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hn
    have hMn : M < n := by omega
    have hMR : (M : ℝ) < n := by exact_mod_cast hMn
    have hlog : r < Real.log (n : ℝ) := by
      have hexp : Real.exp r < (n : ℝ) := lt_of_le_of_lt hM hMR
      have := Real.log_lt_log (Real.exp_pos r) hexp
      rwa [Real.log_exp] at this
    exact mul_nonpos_of_nonneg_of_nonpos (hc n)
      (autoCorrelation_nonpos_of_odd_nonneg hodd hsupp hnn hlog)
  linarith [hsplit, hnonpos]


/-! ### Why the calibration carries the reflected pole

The source that puts weight one on every integer has prefix `⌊e^s⌋ − 1`, so its two-pole defect is
`(e^s − ⌊e^s⌋) + s`: a bounded sawtooth *plus the scale itself*.  Pure integer density therefore
misses the calibration by exactly the reflected pole at the origin, and the `log n` correction in
the ideal source's weights is precisely the price of that term.  The `+ s` in `e^s + s − 1` is an
arithmetic fact about counting the integers, not a convention. -/

/-- The source of weight one at every integer from two on. -/
def allOnes : ℕ → ℝ := fun n => if 2 ≤ n then 1 else 0

theorem sum_allOnes {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 0 N, allOnes k = (N : ℝ) - 1 := by
  induction N with
  | zero => omega
  | succ M ih =>
      rcases Nat.eq_or_lt_of_le hN with h1 | h1
      · have hM : M = 0 := by omega
        subst hM
        rw [Finset.sum_Icc_succ_top (Nat.zero_le _), Finset.Icc_self, Finset.sum_singleton]
        simp [allOnes]
      · have hM1 : 1 ≤ M := by omega
        rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih hM1]
        have : allOnes (M + 1) = 1 := by
          rw [allOnes, if_pos (by omega)]
        rw [this]
        push_cast
        ring

theorem lagPrefix_allOnes {s : ℝ} (hs : 0 ≤ s) :
    lagPrefix allOnes s = (⌊Real.exp s⌋₊ : ℝ) - 1 := by
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ ⌊Real.exp s⌋₊ := Nat.le_floor (by exact_mod_cast hexp1)
  rw [lagPrefix, sum_allOnes hN1]

/-- **The defect of pure integer density is the sawtooth plus the scale.** -/
theorem lagSourceDefect_allOnes {s : ℝ} (hs : 0 ≤ s) :
    lagSourceDefect allOnes s = (Real.exp s - (⌊Real.exp s⌋₊ : ℝ)) + s := by
  rw [lagSourceDefect, lagPrefix_allOnes hs, twoPoleWeight]
  ring

/-- Pure integer density misses the calibration by the reflected pole. -/
theorem lagSourceDefect_allOnes_bounds {s : ℝ} (hs : 0 ≤ s) :
    s ≤ lagSourceDefect allOnes s ∧ lagSourceDefect allOnes s < s + 1 := by
  rw [lagSourceDefect_allOnes hs]
  have h1 : ((⌊Real.exp s⌋₊ : ℝ)) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have h2 : Real.exp s < (⌊Real.exp s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor <;> linarith


/-! ### Past the aperture the Gram is a convolution of the two halves

Reflecting the left half turns the far correlation into the convolution of the two halves of the
test.  Everything the prime side reads beyond the aperture is therefore a function of that single
convolution: two tests whose halves convolve alike are indistinguishable there, whatever else
differs.  The sign of the far reading is decided by the two halves' sign pattern. -/

/-- **The far Gram is a convolution.** -/
theorem autoCorrelation_eq_conv {r t : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t) :
    autoCorrelation F t = ∫ y, leftPart F (-y) * rightPart F (t - y) := by
  rw [autoCorrelation_eq_halves hsupp ht]
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun y => leftPart F (-y) * rightPart F (t - y))
  rw [← hrefl]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show leftPart F x * rightPart F (x + t) = leftPart F (- -x) * rightPart F (t - -x)
  rw [neg_neg, show t - -x = x + t by ring]

/-- If the two halves convolve nonnegatively the far reading is nonnegative. -/
theorem autoCorrelation_nonneg_of_halves {r t : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t)
    (hprod : ∀ y, 0 ≤ leftPart F (-y) * rightPart F (t - y)) :
    0 ≤ autoCorrelation F t := by
  rw [autoCorrelation_eq_conv hsupp ht]
  exact MeasureTheory.integral_nonneg hprod

/-- A test of one sign reads every far lag nonnegatively. -/
theorem autoCorrelation_nonneg_of_nonneg {r t : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (ht : r < t)
    (hnn : ∀ x, 0 ≤ F x) : 0 ≤ autoCorrelation F t := by
  refine autoCorrelation_nonneg_of_halves hsupp ht fun y => ?_
  have hl : 0 ≤ leftPart F (-y) := by
    rw [leftPart]
    by_cases h : -y < 0
    · rw [if_pos h]; exact hnn _
    · rw [if_neg h]
  have hr : 0 ≤ rightPart F (t - y) := by
    rw [rightPart]
    by_cases h : (0:ℝ) ≤ t - y
    · rw [if_pos h]; exact hnn _
    · rw [if_neg h]
  exact mul_nonneg hl hr


/-! ### The aggregate's Schur bound, with an explicit bandwidth

Only the pairs whose ratio lies inside the aperture contribute to the aggregate, so its Schur
constant is the mass times the largest number of partners a single index has.  That number is the
whole arithmetic input the bound needs: the cross-prime aggregate of any nonnegative weight family
is at most `A(0)·B·Σ w²`, where `B` counts partners within the aperture.  Open problem 8 is thus
reduced to counting prime ratios inside a window. -/

theorem autoCorrelation_eq_zero_abs (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {t : ℝ} (ht : 2 * r ≤ |t|) :
    autoCorrelation F t = 0 := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    exact autoCorrelation_eq_zero hF hr hsupp ht
  · rw [abs_of_neg h] at ht
    rw [← autoCorrelation_neg F t]
    exact autoCorrelation_eq_zero hF hr hsupp ht

open scoped Classical in
/-- **The aggregate is bounded by the mass times the aperture bandwidth.** -/
theorem aggregate_le_bandwidth (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) {B : ℝ}
    (hB : ∀ p ∈ P,
      (((P.filter fun q : ℕ => |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ 2 * r).card : ℕ) : ℝ) ≤ B) :
    ∑ p ∈ P, ∑ q ∈ P, w p * w q * autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))
      ≤ autoCorrelation F 0 * B * ∑ p ∈ P, w p ^ 2 := by
  have hA0 := autoCorrelation_zero_nonneg F
  refine sum_mul_mul_le_rowSum hw ?_ ?_
  · intro n _ m _
    rw [← autoCorrelation_neg F (Real.log (m : ℝ) - Real.log (n : ℝ)),
      show -(Real.log (m : ℝ) - Real.log (n : ℝ))
        = Real.log (n : ℝ) - Real.log (m : ℝ) by ring]
  · intro p hp
    have hzero : ∀ q ∈ P,
        q ∉ (P.filter fun q : ℕ => |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ 2 * r) →
        |autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))| = 0 := by
      intro q hq hnot
      have hgt : 2 * r ≤ |Real.log (q : ℝ) - Real.log (p : ℝ)| := by
        by_contra hc
        exact hnot (Finset.mem_filter.mpr ⟨hq, le_of_lt (not_le.mp hc)⟩)
      rw [autoCorrelation_eq_zero_abs hF hr hsupp hgt, abs_zero]
    have hrestrict :
        ∑ q ∈ P, |autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))|
          = ∑ q ∈ (P.filter fun q : ℕ => |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ 2 * r),
              |autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))| :=
      (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
    rw [hrestrict]
    have hterm : ∀ q ∈ (P.filter fun q : ℕ => |Real.log (q : ℝ) - Real.log (p : ℝ)| ≤ 2 * r),
        |autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))| ≤ autoCorrelation F 0 :=
      fun q _ => abs_autoCorrelation_le hF hFc _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hB p hp) hA0 |>.trans_eq (mul_comm _ _)


/-! ### The aggregate on a dyadic window

Inside a dyadic window the number of partners within the aperture is the banded count of the
near-diagonal block, so the aggregate is at most `A(0)(2⌊4Xr⌋+1)Σw²`.  Below the integer spacing
of the window there are no partners at all: for `2r < 1/2X` the aggregate is exactly diagonal —
the arithmetic of the window is invisible to a test that narrow. -/

theorem aggregate_dyadic_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {X : ℕ} (hX : 0 < X) (w : ℕ → ℝ)
    (hw : ∀ p ∈ Finset.Ioc X (2 * X), 0 ≤ w p) :
    ∑ p ∈ Finset.Ioc X (2 * X), ∑ q ∈ Finset.Ioc X (2 * X),
        w p * w q * autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))
      ≤ autoCorrelation F 0 * ((2 * ⌊2 * (X : ℝ) * (2 * r)⌋₊ + 1 : ℕ) : ℝ)
        * ∑ p ∈ Finset.Ioc X (2 * X), w p ^ 2 := by
  classical
  refine aggregate_le_bandwidth hF hFc hr hsupp _ w hw fun p hp => ?_
  exact_mod_cast card_lagClose_le hX (by linarith : (0:ℝ) ≤ 2 * r) hp

/-- **Below the window's integer spacing the aggregate is diagonal.** -/
theorem aggregate_dyadic_diagonal (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {X : ℕ} (hX : 0 < X)
    (hsmall : 2 * r < 1 / (2 * (X : ℝ))) (w : ℕ → ℝ) :
    ∑ p ∈ Finset.Ioc X (2 * X), ∑ q ∈ Finset.Ioc X (2 * X),
        w p * w q * autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))
      = autoCorrelation F 0 * ∑ p ∈ Finset.Ioc X (2 * X), w p ^ 2 := by
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hgap : ∀ p ∈ Finset.Ioc X (2 * X), ∀ q ∈ Finset.Ioc X (2 * X), p ≠ q →
      2 * r ≤ |Real.log (q : ℝ) - Real.log (p : ℝ)| := by
    intro p hp q hq hpq
    rw [Finset.mem_Ioc] at hp hq
    have hbig : ∀ m n : ℕ, X < m → m < n → n ≤ 2 * X →
        1 / (2 * (X : ℝ)) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
      intro m n hm hmn hn
      have h1 := one_div_le_log_sub_log (lt_trans hX hm) hmn
      have hn' : (n : ℝ) ≤ 2 * X := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by
        have : 0 < n := lt_trans (lt_trans hX hm) hmn
        exact_mod_cast this
      have : 1 / (2 * (X : ℝ)) ≤ 1 / (n : ℝ) := by
        apply one_div_le_one_div_of_le hnpos hn'
      linarith
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · have := hbig p q hp.1 hlt hq.2
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have := hbig q p hq.1 hgt hp.2
      rw [abs_of_nonpos (by linarith), neg_sub]
      linarith
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single_of_mem p hp (fun q hq hqp => ?_)]
  · rw [sub_self]
    ring
  · rw [autoCorrelation_eq_zero_abs hF hr hsupp (hgap p hp q hq (Ne.symm hqp)), mul_zero]


/-! ### The ledger of an arbitrary lag system

Nothing in the Abel summation needs the lags to be logarithms of integers.  For any finite family
of positive lags with arbitrary weights the same step decomposition gives the prefix and the same
balance against any calibration.  This is the ledger a Beurling system is read with directly, in
its own lags — the integer case is the instance `λ_n = log n`. -/

/-- The prefix of a lag system: the weight accumulated at lags below `s`. -/
def genPrefix (T : Finset ℕ) (μ lam : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ n ∈ T, μ n * (if lam n ≤ s then (1:ℝ) else 0)

theorem integrableOn_Ioi_genPrefix_mul_deriv (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) :
    IntegrableOn (fun s => genPrefix T μ lam s * deriv h s) (Ioi (0:ℝ)) := by
  have hbase := MeasureTheory.integrable_finsetSum T
    (fun n (_ : n ∈ T) => integrableOn_Ioi_step_mul_deriv hh hS hvan (μ n) (lam n))
  refine hbase.congr (Filter.Eventually.of_forall fun s => ?_)
  show (∑ n ∈ T, μ n * ((if lam n ≤ s then (1:ℝ) else 0) * deriv h s))
    = genPrefix T μ lam s * deriv h s
  rw [genPrefix, Finset.sum_mul]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Abel summation for an arbitrary lag system.** -/
theorem sum_gen_mul_eq_neg_integral (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 0 < lam n) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    (∑ n ∈ T, μ n * h (lam n)) = -∫ s in Ioi (0:ℝ), genPrefix T μ lam s * deriv h s := by
  have hterm : ∀ n ∈ T, IntegrableOn
      (fun s => μ n * ((if lam n ≤ s then (1:ℝ) else 0) * deriv h s)) (Ioi (0:ℝ)) :=
    fun n _ => integrableOn_Ioi_step_mul_deriv hh hS hvan (μ n) (lam n)
  have hsum : (∫ s in Ioi (0:ℝ), genPrefix T μ lam s * deriv h s)
      = ∑ n ∈ T, ∫ s in Ioi (0:ℝ),
          μ n * ((if lam n ≤ s then (1:ℝ) else 0) * deriv h s) := by
    rw [← MeasureTheory.integral_finsetSum T hterm]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    show genPrefix T μ lam s * deriv h s
      = ∑ n ∈ T, μ n * ((if lam n ≤ s then (1:ℝ) else 0) * deriv h s)
    rw [genPrefix, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hval : ∀ n ∈ T, (∫ s in Ioi (0:ℝ),
      μ n * ((if lam n ≤ s then (1:ℝ) else 0) * deriv h s)) = μ n * -h (lam n) := by
    intro n hn
    rw [MeasureTheory.integral_const_mul, integral_Ioi_step_mul_deriv hh hvan (hlam n hn)]
  rw [hsum, Finset.sum_congr rfl hval, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The balance for an arbitrary lag system against an arbitrary calibration.** -/
theorem sum_gen_sub_calibration_eq_defect (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 0 < lam n) {W w : ℝ → ℝ} (hW0 : W 0 = 0) (hWc : Continuous W)
    (hwc : Continuous w) (hWd : ∀ s, HasDerivAt W (w s) s) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    (∑ n ∈ T, μ n * h (lam n)) - ∫ s in Ioi (0:ℝ), w s * h s
      = ∫ s in Ioi (0:ℝ), (W s - genPrefix T μ lam s) * deriv h s := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hwi : IntegrableOn (fun s => W s * deriv h s) (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => W s * deriv h s) (Ioc (0:ℝ) S) :=
      (((hWc.mul hdc)).integrableOn_Icc (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => W s * deriv h s) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [deriv_eq_zero_of_vanishing hvan hx, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hpi := integrableOn_Ioi_genPrefix_mul_deriv T μ lam hh hS hvan
  have hsplit : (∫ s in Ioi (0:ℝ), (W s - genPrefix T μ lam s) * deriv h s)
      = (∫ s in Ioi (0:ℝ), W s * deriv h s)
        - ∫ s in Ioi (0:ℝ), genPrefix T μ lam s * deriv h s := by
    rw [← MeasureTheory.integral_sub hwi hpi]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [sub_mul]
  rw [hsplit, integral_calibration_mul_deriv hW0 hWc hwc hWd hh hS hvan,
    sum_gen_mul_eq_neg_integral T μ lam hlam hh hS hvan]
  ring


/-! ### A geometric Beurling system, read by the same ledger

Take the generalised integers `g^n` with the weights that make the prefix exactly `g^N − 1`.  In
the middle of each cell the calibration has already climbed to `g^{N+1/2}` while the prefix is
still `g^N`, so the defect is at least `(1 − g^{−1/2})e^s`: the ledger separates this system from
`ζ` at full strength, not at the prime-number-theorem level.  The extra poles of
`(1 − g^{−z})^{-1}` on the line through `1` are read at the size of the main term. -/

/-- The weights making a geometric system's prefix exactly `g^N − 1`. -/
def geoWeight (g : ℝ) : ℕ → ℝ := fun n => g ^ n - g ^ (n - 1)

/-- The lags of a geometric system. -/
def geoLag (g : ℝ) : ℕ → ℝ := fun n => (n : ℝ) * Real.log g

theorem sum_geoWeight (g : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, geoWeight g n = g ^ N - 1 := by
  induction N with
  | zero => omega
  | succ M ih =>
      rcases Nat.eq_or_lt_of_le hN with h1 | h1
      · have hM : M = 0 := by omega
        subst hM
        rw [Finset.Icc_self, Finset.sum_singleton, geoWeight]
        norm_num
      · have hM1 : 1 ≤ M := by omega
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih hM1, geoWeight]
        simp only [Nat.add_sub_cancel]
        ring

theorem genPrefix_geo {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) (((N : ℝ) + 1 / 2) * Real.log g)
      = g ^ N - 1 := by
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  have hcond : ∀ n : ℕ, geoLag g n ≤ ((N : ℝ) + 1 / 2) * Real.log g ↔ n ≤ N := by
    intro n
    rw [geoLag]
    constructor
    · intro hle
      have : (n : ℝ) ≤ (N : ℝ) + 1 / 2 := le_of_mul_le_mul_right (by linarith) hlog
      exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast (by linarith : (n : ℝ) < (N : ℝ) + 1))
    · intro hle
      have : (n : ℝ) ≤ N := by exact_mod_cast hle
      nlinarith
  have hrestrict : genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g)
      (((N : ℝ) + 1 / 2) * Real.log g) = ∑ n ∈ Finset.Icc 1 N, geoWeight g n := by
    rw [genPrefix]
    rw [← Finset.sum_subset hsub (fun x hx hnot => ?_)]
    · exact Finset.sum_congr rfl fun n hn => by
        rw [if_pos ((hcond n).mpr (Finset.mem_Icc.mp hn).2), mul_one]
    · rw [Finset.mem_Icc] at hx
      have hxN : ¬ x ≤ N := fun hc => hnot (Finset.mem_Icc.mpr ⟨hx.1, hc⟩)
      rw [if_neg (fun hc => hxN ((hcond x).mp hc)), mul_zero]
  rw [hrestrict, sum_geoWeight g hN]

/-- **The geometric system's defect is of the order of the main term.** -/
theorem geo_defect_ge {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    Real.exp (((N : ℝ) + 1 / 2) * Real.log g) - g ^ N
      ≤ twoPoleWeight (((N : ℝ) + 1 / 2) * Real.log g)
        - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g)
            (((N : ℝ) + 1 / 2) * Real.log g) := by
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hs : 0 ≤ ((N : ℝ) + 1 / 2) * Real.log g := by positivity
  rw [genPrefix_geo hg hN hNM, twoPoleWeight]
  linarith

/-- In the middle of a cell the defect is a fixed proportion of the main term. -/
theorem geo_defect_ge_exp {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (1 - 1 / Real.sqrt g) * Real.exp (((N : ℝ) + 1 / 2) * Real.log g)
      ≤ twoPoleWeight (((N : ℝ) + 1 / 2) * Real.log g)
        - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g)
            (((N : ℝ) + 1 / 2) * Real.log g) := by
  have hg0 : (0:ℝ) < g := by linarith
  have hsq : (0:ℝ) < Real.sqrt g := Real.sqrt_pos.mpr hg0
  have hexp : Real.exp (((N : ℝ) + 1 / 2) * Real.log g) = g ^ ((N : ℝ) + 1 / 2) :=
    exp_mul_log _ hg0
  have hsplit : g ^ ((N : ℝ) + 1 / 2) = g ^ N * Real.sqrt g := by
    rw [Real.rpow_add hg0, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hkey : (1 - 1 / Real.sqrt g) * Real.exp (((N : ℝ) + 1 / 2) * Real.log g)
      = Real.exp (((N : ℝ) + 1 / 2) * Real.log g) - g ^ N := by
    rw [hexp, hsplit]
    field_simp
  rw [hkey]
  exact geo_defect_ge hg hN hNM


/-! ### The geometric defect on a whole half-cell

The prefix is frozen across a whole cell, so the lower bound is not a single point's accident: on
the entire upper half of each cell the geometric system's defect is at least `(1 − g^{−1/2})e^s`.
A test supported there reads the gap at full strength. -/

theorem genPrefix_geo_cell {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℝ}
    (h1 : (N : ℝ) * Real.log g ≤ s) (h2 : s < ((N : ℝ) + 1) * Real.log g) :
    genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s = g ^ N - 1 := by
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  have hin : ∀ n : ℕ, n ≤ N → geoLag g n ≤ s := by
    intro n hn
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    have := mul_le_mul_of_nonneg_right this hlog.le
    rw [geoLag]
    linarith
  have hout : ∀ n : ℕ, ¬ n ≤ N → ¬ geoLag g n ≤ s := by
    intro n hn hle
    have hn1 : (N : ℝ) + 1 ≤ n := by
      have : N + 1 ≤ n := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hn1 hlog.le
    rw [geoLag] at hle
    linarith
  have hrestrict : genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s
      = ∑ n ∈ Finset.Icc 1 N, geoWeight g n := by
    rw [genPrefix]
    rw [← Finset.sum_subset hsub (fun x hx hnot => ?_)]
    · exact Finset.sum_congr rfl fun n hn => by
        rw [if_pos (hin n (Finset.mem_Icc.mp hn).2), mul_one]
    · rw [Finset.mem_Icc] at hx
      have hxN : ¬ x ≤ N := fun hc => hnot (Finset.mem_Icc.mpr ⟨hx.1, hc⟩)
      rw [if_neg (hout x hxN), mul_zero]
  rw [hrestrict, sum_geoWeight g hN]

/-- **The geometric defect on the upper half of a cell.** -/
theorem geo_defect_half_cell {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {s : ℝ}
    (h1 : ((N : ℝ) + 1 / 2) * Real.log g ≤ s) (h2 : s < ((N : ℝ) + 1) * Real.log g) :
    (1 - 1 / Real.sqrt g) * Real.exp s
      ≤ twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s := by
  have hg0 : (0:ℝ) < g := by linarith
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hsq : (0:ℝ) < Real.sqrt g := Real.sqrt_pos.mpr hg0
  have hlow : (N : ℝ) * Real.log g ≤ s := by nlinarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hlow
  have hexpmid : g ^ ((N : ℝ) + 1 / 2) ≤ Real.exp s := by
    rw [← exp_mul_log ((N : ℝ) + 1 / 2) hg0]
    exact Real.exp_le_exp.mpr h1
  have hsplit : g ^ ((N : ℝ) + 1 / 2) = g ^ N * Real.sqrt g := by
    rw [Real.rpow_add hg0, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hgN : g ^ N * Real.sqrt g ≤ Real.exp s := by rw [← hsplit]; exact hexpmid
  have hbound : g ^ N ≤ Real.exp s / Real.sqrt g := by
    rw [le_div_iff₀ hsq]
    exact hgN
  rw [genPrefix_geo_cell hg hN hNM hlow h2, twoPoleWeight]
  have hfield : (1 - 1 / Real.sqrt g) * Real.exp s
      = Real.exp s - Real.exp s / Real.sqrt g := by
    field_simp
  rw [hfield]
  linarith


/-! ### The reading separates the geometric system at full strength

A nonnegative bump supported on the upper half of a cell reads the geometric system's ledger
below the polar side by at least `(1 − g^{−1/2})∫e^sφ` — the size of the main term, not of a
prime-number-theorem error.  No calibration by `e^s + 1` can serve both `ζ` and a geometric
system. -/

theorem geo_reading_gap {g : ℝ} (hg : 1 < g) {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (hφ : Continuous φ) (hS : 0 < S) (hφ0 : ∀ t, S ≤ t → φ t = 0) (hφnn : ∀ t, 0 ≤ φ t)
    (hlow : ∀ t, t ≤ ((N : ℝ) + 1 / 2) * Real.log g → φ t = 0)
    (hhigh : ∀ t, ((N : ℝ) + 1) * Real.log g ≤ t → φ t = 0) :
    (∑ n ∈ Finset.Icc 1 M, geoWeight g n * tailWeight φ S (geoLag g n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * tailWeight φ S s
      ≤ -((1 - 1 / Real.sqrt g) * ∫ s in Ioi (0:ℝ), Real.exp s * φ s) := by
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hlam : ∀ n ∈ Finset.Icc 1 M, 0 < geoLag g n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have : (1:ℝ) ≤ n := by exact_mod_cast hn.1
    rw [geoLag]
    nlinarith
  have hhc : ContDiff ℝ 1 (tailWeight φ S) := contDiff_one_tailWeight hφ S
  have hhvan : ∀ s, S ≤ s → tailWeight φ S s = 0 := fun s hs => tailWeight_eq_zero hφ0 hs
  have hbal := sum_gen_sub_calibration_eq_defect (Finset.Icc 1 M) (geoWeight g) (geoLag g) hlam
    twoPoleWeight_zero continuous_twoPoleWeight (by fun_prop) hasDerivAt_twoPoleWeight
    hhc hS hhvan
  have hderiv : ∀ s ∈ Ioi (0:ℝ), deriv (tailWeight φ S) s = -φ s :=
    fun s _ => by rw [(hasDerivAt_tailWeight hφ S s).deriv]
  have hDi : IntegrableOn (fun s =>
      (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s)
        * deriv (tailWeight φ S) s) (Ioi (0:ℝ)) := by
    refine ((integrableOn_Ioi_twoPoleWeight_mul_deriv hhc hS hhvan).sub
      (integrableOn_Ioi_genPrefix_mul_deriv (Finset.Icc 1 M) (geoWeight g) (geoLag g)
        hhc hS hhvan)).congr_fun (fun s _ => ?_) measurableSet_Ioi
    show twoPoleWeight s * deriv (tailWeight φ S) s
        - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s * deriv (tailWeight φ S) s
      = (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s)
        * deriv (tailWeight φ S) s
    ring
  have hDiφ : IntegrableOn (fun s =>
      (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s) * φ s)
      (Ioi (0:ℝ)) := by
    refine (hDi.neg).congr_fun (fun s hs => ?_) measurableSet_Ioi
    show -((twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s)
        * deriv (tailWeight φ S) s)
      = (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s) * φ s
    rw [hderiv s hs]
    ring
  have hEi : IntegrableOn (fun s => (1 - 1 / Real.sqrt g) * (Real.exp s * φ s))
      (Ioi (0:ℝ)) := by
    have hdisj : Disjoint (Ioc (0:ℝ) S) (Ioi S) := by
      rw [Set.disjoint_left]; rintro x ⟨-, hx2⟩ hx3; exact absurd hx3 (not_lt.mpr hx2)
    have h1 : IntegrableOn (fun s => (1 - 1 / Real.sqrt g) * (Real.exp s * φ s))
        (Ioc (0:ℝ) S) :=
      ((continuous_const.mul (Real.continuous_exp.mul hφ)).integrableOn_Icc
        (a := 0) (b := S)).mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => (1 - 1 / Real.sqrt g) * (Real.exp s * φ s)) (Ioi S) :=
      (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
        (fun x hx => by rw [hφ0 x (le_of_lt hx), mul_zero, mul_zero]) measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hS.le]
    exact h1.union h2
  have hpt : ∀ s ∈ Ioi (0:ℝ), (1 - 1 / Real.sqrt g) * (Real.exp s * φ s)
      ≤ (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s) * φ s := by
    intro s _
    rcases eq_or_lt_of_le (hφnn s) with h0 | hpos
    · rw [← h0]
      ring_nf
      exact le_rfl
    · have h1 : ((N : ℝ) + 1 / 2) * Real.log g ≤ s := by
        by_contra hc
        exact absurd (hlow s (le_of_lt (not_le.mp hc))) (ne_of_gt hpos)
      have h2 : s < ((N : ℝ) + 1) * Real.log g := by
        by_contra hc
        exact absurd (hhigh s (not_lt.mp hc)) (ne_of_gt hpos)
      have hdef := geo_defect_half_cell hg hN hNM h1 h2
      calc (1 - 1 / Real.sqrt g) * (Real.exp s * φ s)
          = ((1 - 1 / Real.sqrt g) * Real.exp s) * φ s := by ring
        _ ≤ (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s) * φ s :=
            mul_le_mul_of_nonneg_right hdef (hφnn s)
  have hmono := MeasureTheory.setIntegral_mono_on hEi hDiφ measurableSet_Ioi hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  rw [hbal, setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => by rw [hderiv s hs]; ring :
        ∀ s ∈ Ioi (0:ℝ),
          (twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s)
              * deriv (tailWeight φ S) s
            = -((twoPoleWeight s - genPrefix (Finset.Icc 1 M) (geoWeight g) (geoLag g) s)
                * φ s)),
    MeasureTheory.integral_neg]
  linarith


/-! ### The spectral form of the Gram kernel

The autocorrelation is the convolution of the test with its reflection, so its Fourier transform
is the squared modulus of the test's.  That is the analytic source of every positivity in the
programme: the Gram kernel of the translate family is a positive-definite function, and the
arithmetic form is the prime Dirichlet polynomial measured against the nonnegative spectral
density `|F̂|²`. -/

open FourierTransform in
theorem fourier_ofReal_autoCorrelation_eq (hF : Continuous F) (hFc : HasCompactSupport F)
    (ξ : ℝ) :
    𝓕 (fun t => ((autoCorrelation F t : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ
        * 𝓕 (fun x => ((F (-x) : ℝ) : ℂ)) ξ := by
  have hint1 : Integrable fun x => ((F x : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hF).integrable_of_hasCompactSupport
      (hFc.comp_left (by simp))
  have hint2 : Integrable fun x => ((F (-x) : ℝ) : ℂ) := by
    simpa using hint1.comp_neg
  have hconv : (fun t => ((autoCorrelation F t : ℝ) : ℂ))
      = MeasureTheory.convolution (fun x => ((F x : ℝ) : ℂ))
          (fun x => ((F (-x) : ℝ) : ℂ)) (ContinuousLinearMap.mul ℂ ℂ)
          (MeasureSpace.volume) := by
    funext t
    rw [MeasureTheory.convolution]
    have hstep : ∀ y : ℝ, (ContinuousLinearMap.mul ℂ ℂ) ((F y : ℝ) : ℂ) ((F (-(t - y)) : ℝ) : ℂ)
        = ((F y * F (y - t) : ℝ) : ℂ) := by
      intro y
      rw [show -(t - y) = y - t by ring]
      push_cast
      rfl
    have hreal : autoCorrelation F t = ∫ a, F a * F (a - t) := by
      rw [← autoCorrelation_neg F t, autoCorrelation]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show F y * F (y + -t) = F y * F (y - t)
      rw [show y + -t = y - t by ring]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep), hreal]
    norm_cast
  rw [hconv]
  exact Real.fourier_mul_convolution_eq hint1 hint2 ξ


open FourierTransform in
/-- Reflecting a real test conjugates its Fourier transform. -/
theorem fourier_ofReal_neg (F : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun x => ((F (-x) : ℝ) : ℂ)) ξ
      = (starRingEnd ℂ) (𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  have hneg := MeasureTheory.integral_neg_eq_self (μ := (volume : Measure ℝ))
    (fun v : ℝ => (starRingEnd ℂ)
      (Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) • ((F v : ℝ) : ℂ)))
  rw [← hneg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) • ((F (-v) : ℝ) : ℂ)
    = (starRingEnd ℂ)
      (Complex.exp (((-2 * Real.pi * -v * ξ : ℝ) : ℂ) * Complex.I) • ((F (-v) : ℝ) : ℂ))
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  congr 1
  · congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

open FourierTransform in
/-- **The spectral density of the Gram kernel is `|F̂|²`.** -/
theorem fourier_ofReal_autoCorrelation_sq (hF : Continuous F) (hFc : HasCompactSupport F)
    (ξ : ℝ) :
    𝓕 (fun t => ((autoCorrelation F t : ℝ) : ℂ)) ξ
      = ((‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_ofReal_autoCorrelation_eq hF hFc ξ, fourier_ofReal_neg F ξ, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _


/-! ### The two-sided Laplace transform of the Gram kernel factorises

For every real `α` the pairing `∫ e^{αt}A(t)dt` is the product of the test's two exponential
moments at `∓α`.  The pole plane is the case `α = ±½` and the total mass is `α = 0`: one identity
covers every pole, and it says that the polar side of a ledger calibrated at any pole is a
rank-one readout of the test. -/

theorem hasCompactSupport_weightedPair (k : ℝ → ℝ) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport fun p : ℝ × ℝ => k p.1 * (F p.2 * F (p.2 + p.1)) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(2 * r)) (b := 2 * r)).prod (isCompact_Icc (a := -r) (b := r)))
    fun p hp => ?_
  by_cases hx : r < |p.2|
  · rw [hsupp p.2 hx]; ring
  by_cases hxs : r < |p.2 + p.1|
  · rw [hsupp _ hxs]; ring
  exfalso
  refine hp ⟨?_, Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hx))⟩
  have h1 := abs_le.mp (not_lt.mp hx)
  have h2 := abs_le.mp (not_lt.mp hxs)
  exact Set.mem_Icc.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩

/-- **The Laplace pairing of the Gram kernel is the product of two exponential moments.** -/
theorem integral_exp_mul_autoCorrelation (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (α : ℝ) :
    (∫ t, Real.exp (α * t) * autoCorrelation F t)
      = (∫ x, F x * Real.exp (-(α * x))) * ∫ x, F x * Real.exp (α * x) := by
  have hcont : Continuous fun p : ℝ × ℝ => Real.exp (α * p.1) * (F p.2 * F (p.2 + p.1)) := by
    fun_prop
  have hint : Integrable fun p : ℝ × ℝ => Real.exp (α * p.1) * (F p.2 * F (p.2 + p.1)) :=
    hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_weightedPair (fun u => Real.exp (α * u)) hsupp)
  have hvp : ((volume : Measure ℝ).prod volume) = (volume : Measure (ℝ × ℝ)) :=
    (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
  have hintprod : Integrable (Function.uncurry fun (s : ℝ) (x : ℝ) =>
      Real.exp (α * s) * (F x * F (x + s))) ((volume : Measure ℝ).prod volume) := hvp ▸ hint
  have hswap := MeasureTheory.integral_integral_swap hintprod
  have hmom : Integrable fun u => F u * Real.exp (α * u) :=
    (hF.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      ).integrable_of_hasCompactSupport hFc.mul_right
  have hleft : (∫ t, Real.exp (α * t) * autoCorrelation F t)
      = ∫ s, ∫ x, Real.exp (α * s) * (F x * F (x + s)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Real.exp (α * s) * autoCorrelation F s = ∫ x, Real.exp (α * s) * (F x * F (x + s))
    rw [autoCorrelation, MeasureTheory.integral_const_mul]
  have hinner : ∀ x : ℝ, (∫ s, Real.exp (α * s) * (F x * F (x + s)))
      = (F x * Real.exp (-(α * x))) * ∫ u, F u * Real.exp (α * u) := by
    intro x
    have htr := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u => Real.exp (α * (u - x)) * (F x * F u)) x
    have hstep : (∫ s, Real.exp (α * s) * (F x * F (x + s)))
        = ∫ u, Real.exp (α * (u - x)) * (F x * F u) := by
      rw [← htr]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show Real.exp (α * s) * (F x * F (x + s))
        = Real.exp (α * (s + x - x)) * (F x * F (s + x))
      rw [show s + x - x = s by ring, show x + s = s + x by ring]
    rw [hstep]
    have hexpand : ∀ u : ℝ, Real.exp (α * (u - x)) * (F x * F u)
        = (F x * Real.exp (-(α * x))) * (F u * Real.exp (α * u)) := by
      intro u
      rw [show α * (u - x) = α * u + -(α * x) by ring, Real.exp_add]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand),
      MeasureTheory.integral_const_mul]
  rw [hleft, hswap, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner),
    MeasureTheory.integral_mul_const]


/-! ### The half-line pole pairing at every pole

Averaging the two exponentials, the pairing of the Gram kernel with `cosh(αs)` over the positive
half-line is half the product of the test's two exponential moments.  At `α = ½` this is the pole
plane of the two-pole calibration; at a general `α` it is the pole plane a calibration at that
pole produces.  Every polar side is a rank-one readout of the test. -/

theorem integral_Ioi_cosh_mul_autoCorrelation (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (α : ℝ) :
    (∫ s in Ioi (0:ℝ), Real.cosh (α * s) * autoCorrelation F s)
      = 1 / 2 * ((∫ x, F x * Real.exp (-(α * x))) * ∫ x, F x * Real.exp (α * x)) := by
  have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
  have hAcs : HasCompactSupport (autoCorrelation F) :=
    hasCompactSupport_autoCorrelation hF.continuous hr hsupp
  have hg : Integrable fun s => Real.cosh (α * s) * autoCorrelation F s :=
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hAc
      ).integrable_of_hasCompactSupport hAcs.mul_left
  have heven : ∀ s : ℝ, Real.cosh (α * -s) * autoCorrelation F (-s)
      = Real.cosh (α * s) * autoCorrelation F s := by
    intro s
    rw [autoCorrelation_neg, show α * -s = -(α * s) by ring, Real.cosh_neg]
  have hhalf := integral_eq_two_mul_Ioi hg heven
  have hi1 : Integrable fun s => Real.exp (α * s) * autoCorrelation F s :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hAc
      ).integrable_of_hasCompactSupport hAcs.mul_left
  have hi2 : Integrable fun s => Real.exp (-α * s) * autoCorrelation F s :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hAc
      ).integrable_of_hasCompactSupport hAcs.mul_left
  have hdecomp : (∫ s, Real.cosh (α * s) * autoCorrelation F s)
      = 1 / 2 * ((∫ s, Real.exp (α * s) * autoCorrelation F s)
        + ∫ s, Real.exp (-α * s) * autoCorrelation F s) := by
    rw [← MeasureTheory.integral_add hi1 hi2, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Real.cosh (α * s) * autoCorrelation F s
      = 1 / 2 * (Real.exp (α * s) * autoCorrelation F s
        + Real.exp (-α * s) * autoCorrelation F s)
    rw [Real.cosh_eq, show -α * s = -(α * s) by ring]
    ring
  have hexp1 := integral_exp_mul_autoCorrelation hF.continuous hFc hsupp α
  have hexp2 := integral_exp_mul_autoCorrelation hF.continuous hFc hsupp (-α)
  simp only [neg_mul, neg_neg] at hexp2
  rw [hdecomp] at hhalf
  simp only [neg_mul] at hhalf
  rw [hexp1, hexp2] at hhalf
  linarith [hhalf]


/-! ### An odd test's pole pairing is nonpositive at every pole

On an odd test the two exponential moments are negatives of each other, so their product is minus
a square.  The pole pairing is therefore `−½(∫F e^{αx})²` at *every* `α`: whatever pole a
calibration is built around, its polar side never charges an odd test — it only pays. -/

theorem expMoment_odd (F : ℝ → ℝ) (hodd : ∀ x, F (-x) = -F x) (α : ℝ) :
    (∫ x, F x * Real.exp (-(α * x))) = -∫ x, F x * Real.exp (α * x) := by
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun x => F x * Real.exp (α * x))
  rw [← hrefl, ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F x * Real.exp (-(α * x)) = -(F (-x) * Real.exp (α * -x))
  rw [hodd x, show α * -x = -(α * x) by ring]
  ring

/-- **The pole pairing of an odd test is minus a square, at every pole.** -/
theorem integral_Ioi_cosh_mul_autoCorrelation_odd (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    (hodd : ∀ x, F (-x) = -F x) (α : ℝ) :
    (∫ s in Ioi (0:ℝ), Real.cosh (α * s) * autoCorrelation F s)
      = -(1 / 2 * (∫ x, F x * Real.exp (α * x)) ^ 2) := by
  rw [integral_Ioi_cosh_mul_autoCorrelation hF hFc hr hsupp α,
    expMoment_odd F hodd α]
  ring

theorem integral_Ioi_cosh_mul_autoCorrelation_odd_nonpos (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    (hodd : ∀ x, F (-x) = -F x) (α : ℝ) :
    (∫ s in Ioi (0:ℝ), Real.cosh (α * s) * autoCorrelation F s) ≤ 0 := by
  rw [integral_Ioi_cosh_mul_autoCorrelation_odd hF hFc hr hsupp hodd α]
  have := sq_nonneg (∫ x, F x * Real.exp (α * x))
  linarith


/-! ### The critical line of a pole at `ρ` is `ρ/2`

Reading the atoms with the weight `2e^{−ρs/2}A(s)` turns the calibration at `ρ` into a balance
whose polar side is exactly `2(∫Fe^{−ρx/2})(∫Fe^{ρx/2})`: the two exponentials of the comparison
density recombine into a `cosh` precisely at the normalisation `n^{−ρ/2}`.  The symmetry point of
a pole at `ρ` is therefore `ρ/2`, read off the balance rather than assumed. -/

/-- The lag weight normalised to a pole at `ρ`. -/
def lagTestWeightAt (ρ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * Real.exp (-(ρ * s) / 2) * autoCorrelation F s

theorem contDiff_one_lagTestWeightAt (ρ : ℝ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) : ContDiff ℝ 1 (lagTestWeightAt ρ F) :=
  (contDiff_const.mul (((contDiff_const.mul contDiff_id).neg.div_const 2).exp)).mul
    (contDiff_one_autoCorrelation hF hFc)

theorem deriv_lagTestWeightAt (ρ : ℝ) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (s : ℝ) :
    deriv (lagTestWeightAt ρ F) s
      = 2 * Real.exp (-(ρ * s) / 2) * (crossCorrelation F s - ρ / 2 * autoCorrelation F s) := by
  have hm : HasDerivAt (fun u : ℝ => -(ρ * u) / 2) (-ρ / 2) s := by
    have := ((hasDerivAt_id s).const_mul ρ).neg.div_const 2
    simpa using this
  have he : HasDerivAt (fun u : ℝ => 2 * Real.exp (-(ρ * u) / 2))
      (2 * (Real.exp (-(ρ * s) / 2) * (-ρ / 2))) s := hm.exp.const_mul 2
  have hprod := he.mul (hasDerivAt_autoCorrelation hF hFc s)
  have hfun : lagTestWeightAt ρ F
      = (fun s : ℝ => 2 * Real.exp (-(ρ * s) / 2)) * autoCorrelation F := rfl
  rw [hfun]
  exact (hprod.congr_deriv (by ring :
    2 * (Real.exp (-(ρ * s) / 2) * (-ρ / 2)) * autoCorrelation F s
      + 2 * Real.exp (-(ρ * s) / 2) * crossCorrelation F s
      = 2 * Real.exp (-(ρ * s) / 2)
          * (crossCorrelation F s - ρ / 2 * autoCorrelation F s))).deriv

/-- **The balance at a pole `ρ`, normalised at `ρ/2`.** -/
theorem testBalanceAt (ρ : ℝ) (hρ : ρ ≠ 0) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (n : ℝ) ^ (-ρ / 2) * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.exp (-(ρ / 2 * x))) * ∫ x, F x * Real.exp (ρ / 2 * x))
      = ∫ s in Ioi (0:ℝ), lagSourceDefectAt ρ
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeightAt ρ F s = 0 := fun s hs => by
    rw [lagTestWeightAt, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_weight_sub_polarAt_eq_defect hρ
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (by simp) (by simp)
    (contDiff_one_lagTestWeightAt ρ hF hFc) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeightAt ρ hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ),
          lagSourceDefectAt ρ (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s
              * deriv (lagTestWeightAt ρ F) s
            = lagSourceDefectAt ρ (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s
              * (2 * Real.exp (-(ρ * s) / 2)
                  * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)))] at hkey
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lagTestWeightAt]
      congr 2
      rw [show -(ρ * Real.log (n : ℝ)) / 2 = (-ρ / 2) * Real.log (n : ℝ) by ring,
        exp_mul_log _ hn]
  · have hpolar := integral_Ioi_cosh_mul_autoCorrelation hF hFc hr hsupp (ρ / 2)
    have hrw : (∫ s in Ioi (0:ℝ), (Real.exp (ρ * s) + 1) * lagTestWeightAt ρ F s)
        = ∫ s in Ioi (0:ℝ), 4 * (Real.cosh (ρ / 2 * s) * autoCorrelation F s) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [lagTestWeightAt, Real.cosh_eq]
      have hsplit : Real.exp (ρ / 2 * s) = Real.exp (ρ * s) * Real.exp (-(ρ * s) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hsplit2 : Real.exp (-(ρ / 2 * s)) = Real.exp (-(ρ * s) / 2) := by
        congr 1
        ring
      rw [hsplit, hsplit2]
      ring
    rw [hrw, MeasureTheory.integral_const_mul, hpolar]
    ring


/-! ### The odd balance at a pole `ρ`

On an odd test the polar term at `ρ` is minus a square, so the balance puts the prime side and
the pole charge on the same side: their sum is the residue of the calibration at `ρ`.  Bounding
that residue against the weight gives the rate at which a system with its pole at `ρ` is read. -/

theorem testBalanceAt_odd (ρ : ℝ) (hρ : ρ ≠ 0) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    (hodd : ∀ x, F (-x) = -F x) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (n : ℝ) ^ (-ρ / 2) * autoCorrelation F (Real.log n)))
        + 2 * (∫ x, F x * Real.exp (ρ / 2 * x)) ^ 2
      = ∫ s in Ioi (0:ℝ), lagSourceDefectAt ρ
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)) := by
  have hbal := testBalanceAt ρ hρ hF hFc hr hsupp hN
  rw [expMoment_odd F hodd (ρ / 2)] at hbal
  rw [← hbal]
  ring

theorem abs_testBalanceAt_odd_le (ρ : ℝ) (hρ : ρ ≠ 0) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    (hodd : ∀ x, F (-x) = -F x) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (n : ℝ) ^ (-ρ / 2) * autoCorrelation F (Real.log n)))
        + 2 * (∫ x, F x * Real.exp (ρ / 2 * x)) ^ 2|
      ≤ ∫ s in Ioi (0:ℝ), |lagSourceDefectAt ρ
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s))| := by
  rw [testBalanceAt_odd ρ hρ hF hFc hr hsupp hodd hN]
  exact abs_integral_le_integral_abs


/-! ### The capacity inequality is a statement about two moments

The pole term of the complete arithmetic energy, `½C(g)² − ½S(g)²` with `C(g) = ∫2cosh(u/2)g` and
`S(g) = ∫2sinh(u/2)g`, factorises as `2(∫ge^{−u/2})(∫ge^{u/2})`.  So the capacity inequality
`S(g)² ≤ 2M(g) + C(g)²` says exactly that the arithmetic part dominates minus that product, and on
an odd test — where the two moments are negatives — that it dominates twice a perfect square. -/

/-- The `cosh` moment of a test. -/
def coshMoment (g : ℝ → ℝ) : ℝ := ∫ u, 2 * Real.cosh (u / 2) * g u

/-- The `sinh` moment of a test. -/
def sinhMoment (g : ℝ → ℝ) : ℝ := ∫ u, 2 * Real.sinh (u / 2) * g u

theorem coshMoment_eq (g : ℝ → ℝ) : coshMoment g = 2 * ∫ u, g u * Real.cosh (u / 2) := by
  rw [coshMoment, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show 2 * Real.cosh (u / 2) * g u = 2 * (g u * Real.cosh (u / 2))
  ring

theorem sinhMoment_eq (g : ℝ → ℝ) : sinhMoment g = 2 * ∫ u, g u * Real.sinh (u / 2) := by
  rw [sinhMoment, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show 2 * Real.sinh (u / 2) * g u = 2 * (g u * Real.sinh (u / 2))
  ring

/-- **The pole term of the complete energy is the product of the two half-exponential
moments.** -/
theorem poleTerm_eq_moment_mul {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    1 / 2 * coshMoment g ^ 2 - 1 / 2 * sinhMoment g ^ 2
      = 2 * (expMomentNeg g * expMomentPos g) := by
  have h := poleplane_eq_moment_mul (F := g) hg hgc
  rw [coshMoment_eq, sinhMoment_eq]
  nlinarith [h]

/-- **The capacity inequality, restated.** -/
theorem capacity_iff {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (M : ℝ) :
    sinhMoment g ^ 2 ≤ 2 * M + coshMoment g ^ 2
      ↔ 0 ≤ M + 2 * (expMomentNeg g * expMomentPos g) := by
  have h := poleTerm_eq_moment_mul hg hgc
  constructor <;> intro hx <;> linarith

/-- On an odd test the capacity inequality is domination of a perfect square. -/
theorem capacity_odd_iff {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hodd : ∀ x, g (-x) = -g x) (M : ℝ) :
    sinhMoment g ^ 2 ≤ 2 * M + coshMoment g ^ 2 ↔ 2 * expMomentNeg g ^ 2 ≤ M := by
  rw [capacity_iff hg hgc M, expMomentPos_odd hg hgc hodd]
  constructor <;> intro hx <;> nlinarith [hx]


/-! ### The Mertens ledger

The Möbius source has no pole at `1` — its Dirichlet series is `1/ζ` — so the calibration it must
be read against is the reflected pole alone, `W(s) = s` with density `1`.  Its defect is then
`s − M(e^s)`, the Mertens function in the lag variable, and the receiver of that ledger is the
Mertens receiver: RH is `M(x) = O(x^{1/2+ε})`.  Below the first prime the defect is exactly the
scale. -/

/-- The Möbius source, with the unit atom at lag zero removed. -/
def moebiusSource : ℕ → ℝ :=
  fun n => if n ≤ 1 then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- The Mertens function in the lag variable, shifted by its unit atom. -/
def lagMertens (s : ℝ) : ℝ := lagPrefix moebiusSource s

theorem moebiusSource_zero : moebiusSource 0 = 0 := by
  rw [moebiusSource, if_pos (by omega)]

theorem moebiusSource_one : moebiusSource 1 = 0 := by
  rw [moebiusSource, if_pos (by omega)]

/-- **The Mertens balance.**  Against the reflected pole alone, the Möbius atoms leave the
Mertens defect as the entire residue. -/
theorem sum_moebius_sub_unit_eq_defect (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), moebiusSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), h s
      = ∫ s in Ioi (0:ℝ), (s - lagMertens s) * deriv h s := by
  have hbase := sum_weight_sub_calibration_eq_defect moebiusSource moebiusSource_zero
    moebiusSource_one (W := fun s : ℝ => s) (w := fun _ : ℝ => (1:ℝ)) rfl continuous_id
    continuous_const (fun s => hasDerivAt_id s) hh hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => by rw [one_mul] :
    ∀ s ∈ Ioi (0:ℝ), (1:ℝ) * h s = h s)] at hbase
  exact hbase

/-- Below the first prime the Mertens defect is exactly the scale. -/
theorem lagMertens_eq_zero_of_lt_log_two {s : ℝ} (hs : s < Real.log 2) : lagMertens s = 0 := by
  have hlt : Real.exp s < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 1 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  rw [lagMertens, lagPrefix]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [moebiusSource, if_pos (le_trans hk.2 hfl)]

theorem mertens_defect_quiet {s : ℝ} (hs : s < Real.log 2) : s - lagMertens s = s := by
  rw [lagMertens_eq_zero_of_lt_log_two hs, sub_zero]


/-! ### The Mertens defect: the trivial rate and the first cell

Each Möbius weight has modulus at most one, so the Mertens prefix never exceeds the count of
integers below the scale: the unconditional rate of the Mertens ledger is `e^s`, exactly as the
Chebyshev ledger's is.  On the first prime cell the prefix is `−1` and the defect is `s + 1`. -/

theorem abs_lagMertens_le (s : ℝ) : |lagMertens s| ≤ Real.exp s := by
  set N := ⌊Real.exp s⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hterm : ∀ k ∈ Finset.Icc 2 N, |moebiusSource k| ≤ 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [moebiusSource, if_neg (by omega)]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have hsplit : lagMertens s = ∑ k ∈ Finset.Icc 2 N, moebiusSource k := by
    rw [lagMertens, lagPrefix]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx hnot
      rw [Finset.mem_Icc] at hx
      have hx1 : x ≤ 1 := by
        by_contra hc
        exact hnot (Finset.mem_Icc.mpr ⟨by omega, hx.2⟩)
      rw [moebiusSource, if_pos hx1]
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
  have hle : (N + 1 - 2 : ℕ) ≤ N := by omega
  have hcast : ((N + 1 - 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
  linarith

/-- On the first prime cell the Mertens defect is `s + 1`. -/
theorem lagMertens_eq_neg_one {s : ℝ} (h1 : Real.log 2 ≤ s) (h2 : s < Real.log 3) :
    lagMertens s = -1 := by
  have hge : (2:ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hlt : Real.exp s < 3 := by
    have := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
  have hfl : ⌊Real.exp s⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by positivity)]
    exact ⟨by exact_mod_cast hge, by exact_mod_cast hlt⟩
  have hIcc : Finset.Icc 0 2 = Finset.range 3 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [lagMertens, lagPrefix, hfl, hIcc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, moebiusSource]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]


/-! ### The ledger of a real character twist

A twisted source `χ(n)Λ(n)` with a non-principal character has no pole at `1`, so like the Möbius
source it is read against the reflected pole alone: `W(s) = s`, density `1`.  Its defect is
`s − ψ(e^s, χ)`, the twisted Chebyshev function, and the receiver of that ledger is the
generalised Riemann hypothesis for that character.  Against the *two-pole* calibration the same
source is off by the whole polar term, which is the selectivity statement: a twist cannot share
`ζ`'s calibration. -/

/-- The source of a real character twist. -/
def twistSource (χ : ℕ → ℝ) : ℕ → ℝ :=
  fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℝ)

theorem twistSource_zero (χ : ℕ → ℝ) : twistSource χ 0 = 0 := by
  rw [twistSource]
  simp

theorem twistSource_one (χ : ℕ → ℝ) : twistSource χ 1 = 0 := by
  rw [twistSource]
  simp

/-- **The twisted balance.**  Against the reflected pole alone, the twisted atoms leave the
twisted Chebyshev defect as the entire residue. -/
theorem sum_twist_sub_unit_eq_defect (χ : ℕ → ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), twistSource χ n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), h s
      = ∫ s in Ioi (0:ℝ), (s - lagPrefix (twistSource χ) s) * deriv h s := by
  have hbase := sum_weight_sub_calibration_eq_defect (twistSource χ) (twistSource_zero χ)
    (twistSource_one χ) (W := fun s : ℝ => s) (w := fun _ : ℝ => (1:ℝ)) rfl continuous_id
    continuous_const (fun s => hasDerivAt_id s) hh hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => by rw [one_mul] :
    ∀ s ∈ Ioi (0:ℝ), (1:ℝ) * h s = h s)] at hbase
  exact hbase

/-- A character twist never exceeds the Chebyshev count. -/
theorem abs_lagPrefix_twist_le {χ : ℕ → ℝ} (hχ : ∀ n, |χ n| ≤ 1) (s : ℝ) :
    |lagPrefix (twistSource χ) s| ≤ lagChebyshev s := by
  rw [lagPrefix, lagChebyshev]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [twistSource, abs_mul,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := k))]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (hχ k)

/-- Below the first prime a twisted ledger's defect is exactly the scale. -/
theorem twist_defect_quiet {χ : ℕ → ℝ} (hχ : ∀ n, |χ n| ≤ 1) {s : ℝ} (hs : s < Real.log 2) :
    s - lagPrefix (twistSource χ) s = s := by
  have hb := abs_lagPrefix_twist_le hχ s
  rw [lagChebyshev_eq_zero_of_lt_log_two hs] at hb
  rw [abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)), sub_zero]


/-! ### The prime-only source and the prime-power correction

Dropping the higher prime powers gives the source of `θ`.  It is dominated by `Λ` index by index,
so its two-pole defect is larger than `ζ`'s by exactly the prime-power correction `ψ − θ`, which
is nonnegative and vanishes below the first square of a prime.  The ledger therefore sees the
higher prime powers as a nonnegative increment of the defect — the squares are a cost, never a
gain. -/

/-- The prime-only source: the atoms of `θ`. -/
def thetaSource : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) else 0

theorem thetaSource_zero : thetaSource 0 = 0 := by
  rw [thetaSource, if_neg Nat.not_prime_zero]

theorem thetaSource_one : thetaSource 1 = 0 := by
  rw [thetaSource, if_neg Nat.not_prime_one]

theorem thetaSource_le_vonMangoldt (n : ℕ) :
    thetaSource n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [thetaSource]
  by_cases hp : n.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rw [if_neg hp]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- **The balance for the prime-only source.** -/
theorem sum_theta_sub_polar_eq_defect (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), thetaSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), lagSourceDefect thetaSource s * deriv h s :=
  sum_weight_sub_polar_eq_defect thetaSource thetaSource_zero thetaSource_one hh hS hvan hN

/-- **The prime-power correction is the gap between the two defects, and it is nonnegative.** -/
theorem chebyshev_le_theta_defect (s : ℝ) :
    chebyshevTwoPoleDefect s ≤ lagSourceDefect thetaSource s :=
  chebyshevTwoPoleDefect_le_lagSourceDefect thetaSource_le_vonMangoldt s

theorem theta_defect_sub_chebyshev (s : ℝ) :
    lagSourceDefect thetaSource s - chebyshevTwoPoleDefect s
      = lagChebyshev s - lagPrefix thetaSource s := by
  rw [lagSourceDefect, chebyshevTwoPoleDefect, lagChebyshev_eq_lagPrefix]
  ring

/-- Below the first prime square the two sources agree. -/
theorem theta_defect_eq_chebyshev_of_lt_log_four {s : ℝ} (hs : s < Real.log 4) :
    lagSourceDefect thetaSource s = chebyshevTwoPoleDefect s := by
  have hlt : Real.exp s < 4 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 4)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 3 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
      (ArithmeticFunction.vonMangoldt k : ℝ) = thetaSource k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk3 : k ≤ 3 := le_trans hk.2 hfl
    interval_cases k
    · simp [thetaSource]
    · simp [thetaSource]
    · rw [thetaSource, if_pos Nat.prime_two,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    · rw [thetaSource, if_pos Nat.prime_three,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  have heq : lagChebyshev s = lagPrefix thetaSource s := by
    rw [lagChebyshev, lagPrefix]
    exact Finset.sum_congr rfl hterm
  have h := theta_defect_sub_chebyshev s
  rw [heq, sub_self] at h
  linarith


/-! ### Second-order summation for an arbitrary source

Two summations by parts read every atom of any source through its ramp, so each source has its own
ramp sum and the reading is the pairing of that ramp sum with the curvature of the test.  This is
the second-order dictionary, and it is what turns a receiver statement about `D` into a statement
about the ledger of an arbitrary source. -/

/-- The ramp sum of an arbitrary source. -/
def genRampSum (a : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n * max (s - Real.log n) 0

/-- **Second-order lag Abel summation for an arbitrary source.** -/
theorem sum_weight_mul_eq_integral_rampSum (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * h (Real.log n)
      = ∫ s in Ioi (0:ℝ), genRampSum a N s * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hterm : ∀ n : ℕ, IntegrableOn
      (fun s => a n * (max (s - Real.log n) 0 * deriv (deriv h) s)) (Ioi (0:ℝ)) := fun n =>
    integrableOn_Ioi_of_vanishing
      (continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).mul hd2))
      hS (fun x hx => by rw [deriv_deriv_eq_zero_of_vanishing hvan hx]; ring)
  have hpt : ∀ s : ℝ, genRampSum a N s * deriv (deriv h) s
      = ∑ n ∈ Finset.range (N + 1), a n * (max (s - Real.log n) 0 * deriv (deriv h) s) := by
    intro s
    rw [genRampSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpt s),
    integral_finsetSum _ fun n _ => hterm n]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h1 : n ≤ 1
  · have hz : a n = 0 := by interval_cases n <;> assumption
    rw [hz]; simp
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast not_le.mp h1)
    rw [MeasureTheory.integral_const_mul, integral_Ioi_ramp_mul_deriv2 hh hh' hvan hlog]


/-! ### The second-order balance for an arbitrary source

Pairing the source's own ramp sum against the polar ramp gives the curvature form of the balance
for every source: the reading minus the polar side is the ramp defect tested on `h″`.  Each source
therefore has its own critical-scale receiver, obtained from its ramp defect exactly as `D` is
obtained from `ζ`'s. -/

theorem sum_weight_sub_polar_eq_rampDefect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ), (genRampSum a N s - polarRamp s) * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hvan2 : ∀ s, S < s → deriv (deriv h) s = 0 :=
    fun s hs => deriv_deriv_eq_zero_of_vanishing hvan hs
  have hcr : Continuous (genRampSum a N) := by
    unfold genRampSum
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hi1 : IntegrableOn (fun s => genRampSum a N s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hcr.mul hd2) hS (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hi2 : IntegrableOn (fun s => polarRamp s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (continuous_polarRamp.mul hd2) hS
      (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (genRampSum a N s - polarRamp s) * deriv (deriv h) s)
      = (∫ s in Ioi (0:ℝ), genRampSum a N s * deriv (deriv h) s)
        - ∫ s in Ioi (0:ℝ), polarRamp s * deriv (deriv h) s := by
    rw [← MeasureTheory.integral_sub hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  rw [hsplit, ← sum_weight_mul_eq_integral_rampSum a ha0 ha1 hh hh' hS hvan N,
    integral_polarRamp_mul_deriv2 hh hh' hS hvan]


/-! ### Every source has its own critical-scale receiver

Integrating the defect gives each source a critical-scale functional, and the second-order
balance pairs exactly that functional against the curvature of the test.  For `ζ` it is
`D(s) + s²/2 − s`; for any source it is `∫₀^s (W − prefix)`.  The receiver is therefore not a
feature of `ζ` but of the ledger. -/

theorem genRampSum_eq_integral_step (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0) (N : ℕ)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ u in (0:ℝ)..s,
        ∑ n ∈ Finset.range (N + 1), a n * (if Real.log n ≤ u then (1:ℝ) else 0))
      = genRampSum a N s := by
  have hsum := intervalIntegral.integral_finsetSum (μ := volume) (a := (0:ℝ)) (b := s)
    (s := Finset.range (N + 1))
    (f := fun (n : ℕ) (u : ℝ) => a n * (if Real.log n ≤ u then (1:ℝ) else 0))
    (fun n _ => ((monotone_step (Real.log n)).intervalIntegrable).const_mul _)
  rw [hsum, genRampSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul]
  by_cases h1 : n ≤ 1
  · have hz : a n = 0 := by interval_cases n <;> assumption
    rw [hz, zero_mul, zero_mul]
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast not_le.mp h1)
    rw [integral_step_eq_ramp hlog hs]

/-- **The source's critical-scale functional is the ramp defect.** -/
theorem sourceScalePrefix_eq (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0) {N : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    sourceScalePrefix a s = polarRamp s - genRampSum a N s := by
  have hcong : ∀ u ∈ Set.uIcc (0:ℝ) s, lagSourceDefect a u
      = twoPoleWeight u
        - ∑ n ∈ Finset.range (N + 1), a n * (if Real.log n ≤ u then (1:ℝ) else 0) := by
    intro u hu
    rw [Set.uIcc_of_le hs] at hu
    rw [lagSourceDefect, lagPrefix_eq_sum_step a hu.1 ((Real.exp_le_exp.mpr hu.2).trans hN)]
  have hintw : IntervalIntegrable twoPoleWeight volume 0 s :=
    continuous_twoPoleWeight.intervalIntegrable _ _
  have hints : IntervalIntegrable
      (fun u => ∑ n ∈ Finset.range (N + 1), a n * (if Real.log n ≤ u then (1:ℝ) else 0))
      volume 0 s := by
    have hbase := IntervalIntegrable.sum (Finset.range (N + 1))
      (fun n (_ : n ∈ Finset.range (N + 1)) =>
        ((monotone_step (Real.log n)).intervalIntegrable
          (μ := volume) (a := (0:ℝ)) (b := s)).const_mul (a n))
    have hfun : (fun u : ℝ => ∑ n ∈ Finset.range (N + 1),
        a n * (if Real.log n ≤ u then (1:ℝ) else 0))
        = ∑ n ∈ Finset.range (N + 1),
          fun u : ℝ => a n * (if Real.log n ≤ u then (1:ℝ) else 0) := by
      funext u
      rw [Finset.sum_apply]
    rw [hfun]
    exact hbase
  have hpr : (∫ u in (0:ℝ)..s, twoPoleWeight u) = polarRamp s := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_polarRamp u) hintw,
      polarRamp_zero, sub_zero]
  rw [sourceScalePrefix, intervalIntegral.integral_congr hcong,
    intervalIntegral.integral_sub hintw hints, hpr,
    genRampSum_eq_integral_step a ha0 ha1 N hs]

/-- **The receiver form of the balance for an arbitrary source.** -/
theorem sum_weight_sub_polar_eq_sourceScalePrefix (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp s + 1) * h s
      = -∫ s in Ioi (0:ℝ), sourceScalePrefix a s * deriv (deriv h) s := by
  have hbase := sum_weight_sub_polar_eq_rampDefect a ha0 ha1 hh hh' hS hvan N
  rw [hbase, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rcases le_or_gt s S with hle | hgt
  · have hsN : Real.exp s ≤ N := le_trans (Real.exp_le_exp.mpr hle) hN
    rw [sourceScalePrefix_eq a ha0 ha1 (le_of_lt hs) hsN]
    ring
  · rw [deriv_deriv_eq_zero_of_vanishing hvan hgt]
    ring


/-! ### The second-order dictionary in full generality

Two integrations by parts on the calibration side and two summations by parts on the arithmetic
side give the curvature form of the balance for every source and every calibration: the reading
minus the comparison integral is the difference of the source's ramp sum and the calibration's
second primitive, paired with `h″`.  Every ledger in the theory is an instance. -/

theorem integral_secondPrimitive_mul_deriv2 {W w W₂ : ℝ → ℝ} (hW0 : W 0 = 0)
    (hWc : Continuous W) (hwc : Continuous w) (hWd : ∀ s, HasDerivAt W (w s) s)
    (hW20 : W₂ 0 = 0) (hW2c : Continuous W₂) (hW2d : ∀ s, HasDerivAt W₂ (W s) s)
    (hh : ContDiff ℝ 1 h) (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) :
    (∫ s in Ioi (0:ℝ), W₂ s * deriv (deriv h) s) = ∫ s in Ioi (0:ℝ), w s * h s := by
  have hvan' : ∀ s, S + 1 ≤ s → deriv h s = 0 :=
    fun s hs => deriv_eq_zero_of_vanishing hvan (by linarith)
  have h1 := integral_calibration_mul_deriv (h := deriv h) (S := S + 1) hW20 hW2c hWc hW2d
    hh' (by linarith) hvan'
  have h2 := integral_calibration_mul_deriv (h := h) (S := S) hW0 hWc hwc hWd hh hS hvan
  rw [h1, h2]
  ring

/-- **The second-order dictionary for an arbitrary source and calibration.** -/
theorem sum_weight_sub_calibration_eq_rampDefect (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {W w W₂ : ℝ → ℝ} (hW0 : W 0 = 0) (hWc : Continuous W) (hwc : Continuous w)
    (hWd : ∀ s, HasDerivAt W (w s) s) (hW20 : W₂ 0 = 0) (hW2c : Continuous W₂)
    (hW2d : ∀ s, HasDerivAt W₂ (W s) s) (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), w s * h s
      = ∫ s in Ioi (0:ℝ), (genRampSum a N s - W₂ s) * deriv (deriv h) s := by
  have hd2 : Continuous (deriv (deriv h)) := hh'.continuous_deriv le_rfl
  have hvan2 : ∀ s, S < s → deriv (deriv h) s = 0 :=
    fun s hs => deriv_deriv_eq_zero_of_vanishing hvan hs
  have hcr : Continuous (genRampSum a N) := by
    unfold genRampSum
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hi1 : IntegrableOn (fun s => genRampSum a N s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hcr.mul hd2) hS (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hi2 : IntegrableOn (fun s => W₂ s * deriv (deriv h) s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hW2c.mul hd2) hS
      (fun s hs => by rw [hvan2 s hs, mul_zero])
  have hsplit : (∫ s in Ioi (0:ℝ), (genRampSum a N s - W₂ s) * deriv (deriv h) s)
      = (∫ s in Ioi (0:ℝ), genRampSum a N s * deriv (deriv h) s)
        - ∫ s in Ioi (0:ℝ), W₂ s * deriv (deriv h) s := by
    rw [← MeasureTheory.integral_sub hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [sub_mul]
  rw [hsplit, ← sum_weight_mul_eq_integral_rampSum a ha0 ha1 hh hh' hS hvan N,
    integral_secondPrimitive_mul_deriv2 hW0 hWc hwc hWd hW20 hW2c hW2d hh hh' hS hvan]


/-! ### The Mertens receiver

Instantiating the general second-order dictionary at the Möbius source and the reflected-pole
calibration `W(s) = s`, whose second primitive is `s²/2`, gives the Mertens critical-scale
functional `∫₀^s (u − M(e^u)) du` as the receiver of that ledger.  The Riemann hypothesis is its
one-sided bound, exactly as `D` is for `ζ`. -/

theorem intervalIntegrable_stepSum (a : ℕ → ℝ) (N : ℕ) (s : ℝ) :
    IntervalIntegrable (fun u => ∑ n ∈ Finset.range (N + 1),
      a n * (if Real.log n ≤ u then (1:ℝ) else 0)) volume 0 s := by
  have hbase := IntervalIntegrable.sum (Finset.range (N + 1))
    (fun n (_ : n ∈ Finset.range (N + 1)) =>
      ((monotone_step (Real.log n)).intervalIntegrable
        (μ := volume) (a := (0:ℝ)) (b := s)).const_mul (a n))
  have hfun : (fun u : ℝ => ∑ n ∈ Finset.range (N + 1),
      a n * (if Real.log n ≤ u then (1:ℝ) else 0))
      = ∑ n ∈ Finset.range (N + 1),
        fun u : ℝ => a n * (if Real.log n ≤ u then (1:ℝ) else 0) := by
    funext u
    rw [Finset.sum_apply]
  rw [hfun]
  exact hbase

/-- The Mertens critical-scale functional. -/
def mertensScalePrefix (s : ℝ) : ℝ := ∫ u in (0:ℝ)..s, (u - lagMertens u)

theorem mertensScalePrefix_eq {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : Real.exp s ≤ N) :
    mertensScalePrefix s = s ^ 2 / 2 - genRampSum moebiusSource N s := by
  have hcong : ∀ u ∈ Set.uIcc (0:ℝ) s, u - lagMertens u
      = u - ∑ n ∈ Finset.range (N + 1),
          moebiusSource n * (if Real.log n ≤ u then (1:ℝ) else 0) := by
    intro u hu
    rw [Set.uIcc_of_le hs] at hu
    rw [lagMertens,
      lagPrefix_eq_sum_step moebiusSource hu.1 ((Real.exp_le_exp.mpr hu.2).trans hN)]
  have hintid : IntervalIntegrable (fun u : ℝ => u) volume 0 s :=
    continuous_id.intervalIntegrable _ _
  rw [mertensScalePrefix, intervalIntegral.integral_congr hcong,
    intervalIntegral.integral_sub hintid (intervalIntegrable_stepSum moebiusSource N s),
    genRampSum_eq_integral_step moebiusSource moebiusSource_zero moebiusSource_one N hs]
  congr 1
  rw [integral_id]
  ring

/-- **The receiver form of the Mertens balance.** -/
theorem sum_moebius_sub_unit_eq_mertensScalePrefix (hh : ContDiff ℝ 1 h)
    (hh' : ContDiff ℝ 1 (deriv h)) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), moebiusSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), h s
      = -∫ s in Ioi (0:ℝ), mertensScalePrefix s * deriv (deriv h) s := by
  have hbase := sum_weight_sub_calibration_eq_rampDefect moebiusSource moebiusSource_zero
    moebiusSource_one (W := fun s : ℝ => s) (w := fun _ : ℝ => (1:ℝ))
    (W₂ := fun s : ℝ => s ^ 2 / 2) rfl continuous_id continuous_const
    (fun s => hasDerivAt_id s) (by norm_num)
    (by fun_prop)
    (fun s => by simpa using (hasDerivAt_pow 2 s).div_const 2)
    hh hh' hS hvan N
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => by rw [one_mul] :
    ∀ s ∈ Ioi (0:ℝ), (1:ℝ) * h s = h s)] at hbase
  rw [hbase, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rcases le_or_gt s S with hle | hgt
  · have hsN : Real.exp s ≤ N := le_trans (Real.exp_le_exp.mpr hle) hN
    rw [mertensScalePrefix_eq (le_of_lt hs) hsN]
    ring
  · rw [deriv_deriv_eq_zero_of_vanishing hvan hgt]
    ring


/-! ### The Mertens receiver on the first two cells

Below the first prime the Mertens receiver is the pure reflected-pole growth `s²/2`; past `log 2`
the single atom `μ(2) = −1` adds the linear term `s − log 2`.  These are the exact values of the
Mertens receiver at the apertures of the first prime window. -/

theorem moebiusSource_two : moebiusSource 2 = -1 := by
  rw [moebiusSource, if_neg (by omega), ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  norm_num

theorem moebiusSource_three : moebiusSource 3 = -1 := by
  rw [moebiusSource, if_neg (by omega), ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  norm_num

theorem mertensScalePrefix_first_cell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.log 2) :
    mertensScalePrefix s = s ^ 2 / 2 := by
  have hexp : Real.exp s ≤ ((2 : ℕ) : ℝ) := by
    have := Real.exp_le_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  rw [mertensScalePrefix_eq hs0 hexp, genRampSum]
  have hzero : ∀ n ∈ Finset.range (2 + 1), moebiusSource n * max (s - Real.log n) 0 = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    interval_cases n
    · rw [moebiusSource_zero, zero_mul]
    · rw [moebiusSource_one, zero_mul]
    · rw [max_eq_right (by push_cast; linarith), mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

theorem mertensScalePrefix_second_cell {s : ℝ} (h1 : Real.log 2 ≤ s) (h2 : s < Real.log 3) :
    mertensScalePrefix s = s ^ 2 / 2 + (s - Real.log 2) := by
  have hs0 : 0 ≤ s := le_trans (Real.log_nonneg (by norm_num)) h1
  have hexp : Real.exp s ≤ ((3 : ℕ) : ℝ) := by
    have := Real.exp_le_exp.mpr (le_of_lt h2)
    rw [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
    exact_mod_cast this
  rw [mertensScalePrefix_eq hs0 hexp, genRampSum]
  have hterm : ∀ n ∈ Finset.range (3 + 1),
      moebiusSource n * max (s - Real.log n) 0
        = if n = 2 then -(s - Real.log 2) else 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    interval_cases n
    · rw [moebiusSource_zero, zero_mul]; norm_num
    · rw [moebiusSource_one, zero_mul]; norm_num
    · rw [moebiusSource_two, if_pos rfl, max_eq_left (by push_cast; linarith)]
      push_cast
      ring
    · rw [moebiusSource_three, if_neg (by omega),
        max_eq_right (by push_cast; linarith), mul_zero]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by omega))
      (fun b _ hb => by rw [if_neg hb])]
  rw [if_pos rfl]
  ring


/-! ### The pair correlation of two tests

Every statement about one test has a bilinear companion: the correlation of two tests, which is
the autocorrelation when they coincide, swaps under reflection of the lag, and polarises the
autocorrelation of a sum.  This is the infrastructure for pair arguments — comparing a test with
a model, or reading one half of a test against the other. -/

/-- The correlation of two tests at a lag. -/
def pairCorrelation (F G : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * G (x + t)

theorem pairCorrelation_self (F : ℝ → ℝ) : pairCorrelation F F = autoCorrelation F := rfl

theorem pairCorrelation_swap (F G : ℝ → ℝ) (t : ℝ) :
    pairCorrelation G F t = pairCorrelation F G (-t) := by
  rw [pairCorrelation, pairCorrelation]
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => F y * G (y + -t)) t
  rw [← hshift]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show G x * F (x + t) = F (x + t) * G (x + t + -t)
  rw [show x + t + -t = x by ring]
  ring

theorem integrable_pair_shift (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (t : ℝ) :
    Integrable fun x => F x * G (x + t) :=
  (hF.mul (hG.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    hFc.mul_right

/-- **Polarisation of the autocorrelation.** -/
theorem autoCorrelation_add (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) (t : ℝ) :
    autoCorrelation (fun x => F x + G x) t
      = autoCorrelation F t + autoCorrelation G t
        + (pairCorrelation F G t + pairCorrelation G F t) := by
  have h1 : Integrable fun x => F x * F (x + t) := integrable_pair_shift hF hFc hF t
  have h2 : Integrable fun x => F x * G (x + t) := integrable_pair_shift hF hFc hG t
  have h3 : Integrable fun x => G x * F (x + t) := integrable_pair_shift hG hGc hF t
  have h4 : Integrable fun x => G x * G (x + t) := integrable_pair_shift hG hGc hG t
  have hexp : ∀ x : ℝ, (F x + G x) * (F (x + t) + G (x + t))
      = F x * F (x + t) + F x * G (x + t) + (G x * F (x + t) + G x * G (x + t)) :=
    fun x => by ring
  rw [autoCorrelation]
  have h12 : Integrable fun x => F x * F (x + t) + F x * G (x + t) := h1.add h2
  have h34 : Integrable fun x => G x * F (x + t) + G x * G (x + t) := h3.add h4
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_add h12 h34,
    MeasureTheory.integral_add h1 h2, MeasureTheory.integral_add h3 h4]
  rw [autoCorrelation, autoCorrelation, pairCorrelation, pairCorrelation]
  ring


/-! ### The bilinear Gram of two tests

The cross Gram form built from two different tests is the inner product of their two fields.  So
comparing an arithmetic source read by one test with the same or another source read by a second
test is again an inner product of superpositions, and the whole Cauchy–Schwarz apparatus applies
across tests, not only within one. -/

theorem integrable_shift_mul_pair (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (a b : ℝ) :
    Integrable fun x => F (x + a) * G (x + b) := by
  have h : Integrable fun x => F x * G (x + (b - a)) := integrable_pair_shift hF hFc hG (b - a)
  refine (h.comp_add_right a).congr (Filter.Eventually.of_forall fun x => ?_)
  show F (x + a) * G (x + a + (b - a)) = F (x + a) * G (x + b)
  rw [show x + a + (b - a) = x + b by ring]

theorem integral_shift_mul_pair (F G : ℝ → ℝ) (a b : ℝ) :
    (∫ x, F (x + a) * G (x + b)) = pairCorrelation F G (b - a) := by
  rw [pairCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => F y * G (y + (b - a))) a
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + a) * G (x + b) = F (x + a) * G (x + a + (b - a))
  rw [show x + a + (b - a) = x + b by ring]

theorem integrable_primeField_mul_pair (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (P Q : Finset ℕ) (c d : ℕ → ℝ) :
    Integrable fun x => primeField F c P x * primeField G d Q x := by
  have hexp : ∀ x : ℝ, (∑ m ∈ P, ∑ n ∈ Q,
      c m * d n * (F (x + Real.log m) * G (x + Real.log n)))
      = primeField F c P x * primeField G d Q x := by
    intro x
    rw [primeField, primeField, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  exact (MeasureTheory.integrable_finsetSum P fun m _ =>
    MeasureTheory.integrable_finsetSum Q fun n _ =>
      (integrable_shift_mul_pair hF hFc hG (Real.log m) (Real.log n)).const_mul
        (c m * d n)).congr (Filter.Eventually.of_forall hexp)

/-- **The cross Gram form of two tests is the inner product of their fields.** -/
theorem sum_pair_gram_eq_integral (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (P Q : Finset ℕ) (c d : ℕ → ℝ) :
    ∑ m ∈ P, ∑ n ∈ Q, c m * d n * pairCorrelation F G (Real.log n - Real.log m)
      = ∫ x, primeField F c P x * primeField G d Q x := by
  have hint2 : ∀ m : ℕ, ∀ n ∈ Q,
      Integrable fun x => c m * d n * (F (x + Real.log m) * G (x + Real.log n)) :=
    fun m n _ => (integrable_shift_mul_pair hF hFc hG (Real.log m) (Real.log n)).const_mul
      (c m * d n)
  have hint : ∀ m ∈ P, Integrable fun x =>
      ∑ n ∈ Q, c m * d n * (F (x + Real.log m) * G (x + Real.log n)) :=
    fun m _ => MeasureTheory.integrable_finsetSum Q (hint2 m)
  have hexp : ∀ x : ℝ, primeField F c P x * primeField G d Q x
      = ∑ m ∈ P, ∑ n ∈ Q, c m * d n * (F (x + Real.log m) * G (x + Real.log n)) := by
    intro x
    rw [primeField, primeField, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_finsetSum P hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_finsetSum Q (hint2 m)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_shift_mul_pair]


/-! ### Cauchy–Schwarz across two tests

The cross Gram form of two tests is bounded by the geometric mean of the two field energies.  A
source whose field has small energy against one test cannot correlate strongly with any source
read by another test: the comparison between a source and a model is an inner product bound. -/

theorem two_mul_integral_primeField_mul_pair_le (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) (P Q : Finset ℕ) (c d : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    2 * ∫ x, primeField F c P x * primeField G d Q x
      ≤ ε * (∫ x, primeField F c P x ^ 2) + ε⁻¹ * ∫ x, primeField G d Q x ^ 2 := by
  have hpt : ∀ x : ℝ, 2 * (primeField F c P x * primeField G d Q x)
      ≤ ε * primeField F c P x ^ 2 + ε⁻¹ * primeField G d Q x ^ 2 := by
    intro x
    have key : ε * (primeField F c P x - primeField G d Q x / ε) ^ 2
        = ε * primeField F c P x ^ 2
          - 2 * (primeField F c P x * primeField G d Q x)
          + ε⁻¹ * primeField G d Q x ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hε.le
      (sq_nonneg (primeField F c P x - primeField G d Q x / ε)), key]
  have hl : Integrable fun x => 2 * (primeField F c P x * primeField G d Q x) :=
    (integrable_primeField_mul_pair hF hFc hG P Q c d).const_mul 2
  have hr : Integrable fun x =>
      ε * primeField F c P x ^ 2 + ε⁻¹ * primeField G d Q x ^ 2 :=
    ((integrable_primeField_sq hF hFc P c).const_mul ε).add
      ((integrable_primeField_sq hG hGc Q d).const_mul ε⁻¹)
  have hmono := MeasureTheory.integral_mono hl hr hpt
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add ((integrable_primeField_sq hF hFc P c).const_mul ε)
      ((integrable_primeField_sq hG hGc Q d).const_mul ε⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-- **Cauchy–Schwarz for the cross Gram of two tests.** -/
theorem abs_sum_pair_gram_le (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) (P Q : Finset ℕ)
    (c d : ℕ → ℝ) :
    |∑ m ∈ P, ∑ n ∈ Q, c m * d n * pairCorrelation F G (Real.log n - Real.log m)|
      ≤ Real.sqrt ((∫ x, primeField F c P x ^ 2) * ∫ x, primeField G d Q x ^ 2) := by
  have hPnn : (0:ℝ) ≤ ∫ x, primeField F c P x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hQnn : (0:ℝ) ≤ ∫ x, primeField G d Q x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hup : (∫ x, primeField F c P x * primeField G d Q x)
      ≤ Real.sqrt ((∫ x, primeField F c P x ^ 2) * ∫ x, primeField G d Q x ^ 2) :=
    le_sqrt_mul_of_two_mul_le hPnn hQnn fun ε hε =>
      two_mul_integral_primeField_mul_pair_le hF hFc hG hGc P Q c d hε
  have hneg : (∫ x, primeField F (fun n => -c n) P x * primeField G d Q x)
      = -∫ x, primeField F c P x * primeField G d Q x := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show primeField F (fun n => -c n) P x * primeField G d Q x
      = -(primeField F c P x * primeField G d Q x)
    rw [primeField_neg, neg_mul]
  have hsq : (∫ x, primeField F (fun n => -c n) P x ^ 2)
      = ∫ x, primeField F c P x ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show primeField F (fun n => -c n) P x ^ 2 = primeField F c P x ^ 2
    rw [primeField_neg, neg_sq]
  have hlow := le_sqrt_mul_of_two_mul_le (by rw [hsq]; exact hPnn) hQnn
    (fun ε hε => two_mul_integral_primeField_mul_pair_le hF hFc hG hGc P Q
      (fun n => -c n) d hε)
  rw [hneg, hsq] at hlow
  rw [sum_pair_gram_eq_integral hF hFc hG P Q c d]
  exact abs_le.mpr ⟨by linarith, hup⟩


/-! ### The logarithm source and its double pole

The source `a(n) = log n` has Dirichlet series `−ζ′`, with a *double* pole at `1`.  Its
calibration is therefore `(s−1)e^s + 1 + s/2`, whose density is `s e^s + ½`: the double pole
contributes `s e^s` and the reflected pole the constant `½`.  Unlike `ζ`'s, this source's defect
is the Stirling error, which is `O(s)` with no hypothesis — the ledger's difficulty is specific to
`Λ`, not to the method. -/

/-- The logarithm source. -/
def logSource : ℕ → ℝ := fun n => Real.log (n : ℝ)

theorem logSource_zero : logSource 0 = 0 := by
  rw [logSource]
  simp

theorem logSource_one : logSource 1 = 0 := by
  rw [logSource]
  simp

/-- The calibration of a double pole at `1` together with the reflected pole. -/
def logWeight (s : ℝ) : ℝ := (s - 1) * Real.exp s + 1 + s / 2

theorem logWeight_zero : logWeight 0 = 0 := by
  rw [logWeight]
  norm_num

theorem continuous_logWeight : Continuous logWeight := by
  unfold logWeight
  fun_prop

theorem hasDerivAt_logWeight (s : ℝ) :
    HasDerivAt logWeight (s * Real.exp s + 1 / 2) s := by
  have h1 : HasDerivAt (fun u : ℝ => (u - 1) * Real.exp u)
      (1 * Real.exp s + (s - 1) * Real.exp s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (Real.hasDerivAt_exp s)
  have h2 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have h3 : HasDerivAt (fun u : ℝ => (u - 1) * Real.exp u + 1 + u / 2)
      ((1 * Real.exp s + (s - 1) * Real.exp s) + 1 / 2) s := (h1.add_const 1).add h2
  exact h3.congr_deriv (by ring)

/-- **The balance for the logarithm source against its double-pole calibration.** -/
theorem sum_log_sub_doublePolar_eq_defect (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), logSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (s * Real.exp s + 1 / 2) * h s
      = ∫ s in Ioi (0:ℝ), (logWeight s - lagPrefix logSource s) * deriv h s :=
  sum_weight_sub_calibration_eq_defect logSource logSource_zero logSource_one logWeight_zero
    continuous_logWeight (by fun_prop) hasDerivAt_logWeight hh hS hvan hN

/-- Below the first prime the logarithm source has not switched on, so its defect is the
calibration itself. -/
theorem logSource_defect_quiet {s : ℝ} (hs : s < Real.log 2) :
    logWeight s - lagPrefix logSource s = logWeight s := by
  have hlt : Real.exp s < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 1 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  have hz : lagPrefix logSource s = 0 := by
    rw [lagPrefix]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : k ≤ 1 := le_trans hk.2 hfl
    interval_cases k
    · exact logSource_zero
    · exact logSource_one
  rw [hz, sub_zero]


/-! ### The Gram of a multiplicative tower is a banded Toeplitz form

The lags of a tower `p, p², p³, …` form an arithmetic progression, so the Gram of a tower depends
only on the difference of the exponents: it is a Toeplitz form.  It is positive semidefinite,
being a Gram form, and it is banded — entries vanish once the exponent gap exceeds `2r/log p` —
so its Schur constant is `A(0)(2⌊2r/L⌋+1)`.  That is the whole of the tower geometry a test can
see. -/

theorem progression_gram_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) (L : ℝ)
    (K : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ j ∈ K, ∑ k ∈ K, c j * c k * autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L) :=
  sum_gram_nonneg hF hFc K c (fun n => (n : ℝ) * L)

open scoped Classical in
/-- **The tower Gram is banded, with Schur constant `A(0)(2⌊2r/L⌋+1)`.** -/
theorem progression_gram_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {L : ℝ} (hL : 0 < L) (K : Finset ℕ)
    (c : ℕ → ℝ) (hc : ∀ n ∈ K, 0 ≤ c n) :
    ∑ j ∈ K, ∑ k ∈ K, c j * c k * autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)
      ≤ autoCorrelation F 0 * ((2 * ⌊2 * r / L⌋₊ + 1 : ℕ) : ℝ) * ∑ j ∈ K, c j ^ 2 := by
  set B : ℕ := ⌊2 * r / L⌋₊ with hB
  have hA0 := autoCorrelation_zero_nonneg F
  refine sum_mul_mul_le_rowSum hc ?_ ?_
  · intro n _ m _
    rw [← autoCorrelation_neg F ((m : ℝ) * L - (n : ℝ) * L),
      show -((m : ℝ) * L - (n : ℝ) * L) = (n : ℝ) * L - (m : ℝ) * L by ring]
  · intro j hj
    have hzero : ∀ k ∈ K, k ∉ Finset.Icc (j - B) (j + B) →
        |autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)| = 0 := by
      intro k _ hnot
      have hfar : B < k - j ∨ B < j - k := by
        rw [Finset.mem_Icc] at hnot
        omega
      have habs : 2 * r ≤ |(k : ℝ) * L - (j : ℝ) * L| := by
        have hkey : ((B : ℝ) + 1) * L ≤ |(k : ℝ) * L - (j : ℝ) * L| := by
          rcases hfar with hf | hf
          · have hkj : (B : ℝ) + 1 ≤ (k : ℝ) - (j : ℝ) := by
              have : B + 1 + j ≤ k := by omega
              have hc1 : ((B + 1 + j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
              push_cast at hc1
              linarith
            rw [abs_of_nonneg (by nlinarith)]
            nlinarith
          · have hkj : (B : ℝ) + 1 ≤ (j : ℝ) - (k : ℝ) := by
              have : B + 1 + k ≤ j := by omega
              have hc1 : ((B + 1 + k : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
              push_cast at hc1
              linarith
            rw [abs_of_nonpos (by nlinarith), neg_sub]
            nlinarith
        have hBlt : 2 * r / L < (B : ℝ) + 1 := Nat.lt_floor_add_one _
        have : 2 * r < ((B : ℝ) + 1) * L := by
          rw [div_lt_iff₀ hL] at hBlt
          linarith
        linarith
      rw [autoCorrelation_eq_zero_abs hF hr hsupp habs, abs_zero]
    have hrestrict : ∑ k ∈ K, |autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)|
        = ∑ k ∈ K.filter (fun k : ℕ => k ∈ Finset.Icc (j - B) (j + B)),
            |autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)| := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun k hk hnot => ?_).symm
      have hk' : k ∉ Finset.Icc (j - B) (j + B) := by
        intro hc2
        exact hnot (Finset.mem_filter.mpr ⟨hk, hc2⟩)
      exact hzero k hk hk'
    rw [hrestrict]
    have hterm : ∀ k ∈ K.filter (fun k : ℕ => k ∈ Finset.Icc (j - B) (j + B)),
        |autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)| ≤ autoCorrelation F 0 :=
      fun k _ => abs_autoCorrelation_le hF hFc _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (K.filter (fun k : ℕ => k ∈ Finset.Icc (j - B) (j + B))).card
        ≤ 2 * B + 1 := by
      refine le_trans (Finset.card_le_card (fun k hk => (Finset.mem_filter.mp hk).2)) ?_
      rw [Nat.card_Icc]
      omega
    have hcardR : ((K.filter (fun k : ℕ => k ∈ Finset.Icc (j - B) (j + B))).card : ℝ)
        ≤ ((2 * B + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    calc ((K.filter (fun k : ℕ => k ∈ Finset.Icc (j - B) (j + B))).card : ℝ)
          * autoCorrelation F 0
        ≤ ((2 * B + 1 : ℕ) : ℝ) * autoCorrelation F 0 :=
          mul_le_mul_of_nonneg_right hcardR hA0
      _ = autoCorrelation F 0 * ((2 * B + 1 : ℕ) : ℝ) := mul_comm _ _


/-! ### Towers coarser than the aperture, and the tower envelope

A tower whose step exceeds twice the aperture is invisible beyond its diagonal: the Gram is
exactly `A(0)Σc²`.  Below that threshold every off-diagonal entry is still discounted by the
quadratic gap at its own exponent difference, which is the tower envelope the discount laws
ask for. -/

theorem progression_gram_diagonal (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {L : ℝ} (hL : 2 * r < L) (K : Finset ℕ) (c : ℕ → ℝ) :
    ∑ j ∈ K, ∑ k ∈ K, c j * c k * autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)
      = autoCorrelation F 0 * ∑ j ∈ K, c j ^ 2 := by
  have hLpos : (0:ℝ) < L := by linarith
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single_of_mem j hj (fun k _ hkj => ?_)]
  · rw [sub_self]
    ring
  · have h1 : (1:ℝ) ≤ |(k : ℝ) - (j : ℝ)| := by
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · have hcast : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have heq : |(k : ℝ) * L - (j : ℝ) * L| = |(k : ℝ) - (j : ℝ)| * L := by
      rw [← sub_mul, abs_mul, abs_of_pos hLpos]
    have habs : 2 * r ≤ |(k : ℝ) * L - (j : ℝ) * L| := by
      rw [heq]
      nlinarith
    rw [autoCorrelation_eq_zero_abs hF hr hsupp habs, mul_zero]

/-- The aperture gap at a lag of either sign. -/
theorem autoCorrelation_le_min_abs (hF : Continuous F) (hFc : HasCompactSupport F) {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : t ≠ 0) :
    autoCorrelation F t ≤ autoCorrelation F 0 * (1 - min (t ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have h := autoCorrelation_le_min hF hFc hsupp habs
  rw [sq_abs] at h
  rcases le_or_gt 0 t with h0 | h0
  · rwa [abs_of_nonneg h0] at h
  · rw [abs_of_neg h0] at h
    rwa [autoCorrelation_neg] at h

/-- **The tower envelope.**  Each off-diagonal entry is discounted by the gap at its exponent
difference. -/
theorem progression_offdiag_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {L : ℝ} (hL : 0 < L) (K : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ n ∈ K, 0 ≤ c n) :
    ∑ j ∈ K, ∑ k ∈ K.erase j, c j * c k * autoCorrelation F ((k : ℝ) * L - (j : ℝ) * L)
      ≤ ∑ j ∈ K, ∑ k ∈ K.erase j, c j * c k * (autoCorrelation F 0
          * (1 - min (((k : ℝ) * L - (j : ℝ) * L) ^ 2 / (8 * r ^ 2)) (1 / 2))) := by
  refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hkK : k ∈ K := (Finset.mem_erase.mp hk).2
  have hne : (k : ℝ) * L - (j : ℝ) * L ≠ 0 := by
    intro hc0
    have : (k : ℝ) = (j : ℝ) := by
      have hsub : ((k : ℝ) - (j : ℝ)) * L = 0 := by rw [sub_mul]; linarith
      rcases mul_eq_zero.mp hsub with h | h
      · linarith
      · exact absurd h (ne_of_gt hL)
    exact hkj (by exact_mod_cast this)
  exact mul_le_mul_of_nonneg_left (autoCorrelation_le_min_abs hF hFc hsupp hne)
    (mul_nonneg (hc j hj) (hc k hkK))


/-! ### The other side of the Gram: how close to `−A(0)` a lag can be read

The sum `A(0) + A(t)` is half the squared norm of `F + F(·+t)`.  If it were small the test would
be nearly anti-periodic at the lag `t`, hence nearly periodic at `2t`, so the displacement energy
at `2t` would be small — which the aperture laws forbid.  That gives the companion of the
quadratic gap: at every nonzero lag the correlation stays a definite amount above `−A(0)`, and
the Gram entries are pinned quantitatively on both sides. -/

/-- The anti-displacement energy of a test at a lag. -/
def antiDisplacement (F : ℝ → ℝ) (t : ℝ) : ℝ := autoCorrelation F 0 + autoCorrelation F t

theorem integrable_add_sq (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    Integrable fun x => (F x + F (x + t)) ^ 2 := by
  have hc : Continuous fun x => F x + F (x + t) :=
    hF.add (hF.comp (continuous_id.add continuous_const))
  have hs : HasCompactSupport fun x => F x + F (x + t) :=
    hFc.add (hFc.comp_homeomorph (Homeomorph.addRight t))
  exact ((hc.mul hc).integrable_of_hasCompactSupport hs.mul_right).congr
    (Filter.Eventually.of_forall fun _ => (sq _).symm)

theorem two_mul_antiDisplacement_eq (hF : Continuous F) (hFc : HasCompactSupport F) (t : ℝ) :
    2 * antiDisplacement F t = ∫ x, (F x + F (x + t)) ^ 2 := by
  have hsq := integrable_sq hF hFc
  have hsqt : Integrable fun x => F (x + t) ^ 2 := by
    simpa using hsq.comp_add_right t
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hpc : Integrable fun x => 2 * (F x * F (x + t)) := hprod.const_mul 2
  have hadd : Integrable fun x => F x ^ 2 + 2 * (F x * F (x + t)) := hsq.add hpc
  have hexp : ∀ x : ℝ, (F x + F (x + t)) ^ 2
      = F x ^ 2 + 2 * (F x * F (x + t)) + F (x + t) ^ 2 := fun x => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_add hadd hsqt, MeasureTheory.integral_add hsq hpc,
    MeasureTheory.integral_const_mul, integral_shift_sq]
  have ht : (∫ x, F x * F (x + t)) = autoCorrelation F t := rfl
  rw [← autoCorrelation_zero_eq, ht, antiDisplacement]
  ring

/-- **Anti-periodicity at a lag forces periodicity at twice the lag.** -/
theorem displacement_two_mul_le_antiDisplacement (hF : Continuous F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    displacement F (2 * t) ≤ 4 * antiDisplacement F t := by
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => (F y + F (y + t)) ^ 2) t
  have hvi : Integrable fun x => (F (x + t) + F (x + t + t)) ^ 2 := by
    simpa using (integrable_add_sq hF hFc t).comp_add_right t
  have hpt : ∀ x : ℝ, (F x - F (x + 2 * t)) ^ 2
      ≤ 2 * (F x + F (x + t)) ^ 2 + 2 * (F (x + t) + F (x + t + t)) ^ 2 := by
    intro x
    rw [show x + 2 * t = x + t + t by ring]
    nlinarith [sq_nonneg (F x + 2 * F (x + t) + F (x + t + t))]
  have hu2 : Integrable fun x => 2 * (F x + F (x + t)) ^ 2 :=
    (integrable_add_sq hF hFc t).const_mul 2
  have hv2 : Integrable fun x => 2 * (F (x + t) + F (x + t + t)) ^ 2 := hvi.const_mul 2
  have hsum : Integrable fun x =>
      2 * (F x + F (x + t)) ^ 2 + 2 * (F (x + t) + F (x + t + t)) ^ 2 := hu2.add hv2
  have hmono := MeasureTheory.integral_mono (integrable_diff_sq hF hFc (2 * t)) hsum hpt
  rw [MeasureTheory.integral_add hu2 hv2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hshift] at hmono
  have e1 := two_mul_displacement_eq hF hFc (2 * t)
  have e2 := two_mul_antiDisplacement_eq hF hFc t
  linarith

/-- **The correlation stays a definite amount above `−A(0)` at every nonzero lag.** -/
theorem antiDisplacement_ge (hF : Continuous F) (hFc : HasCompactSupport F) {r t : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : 0 < t) :
    autoCorrelation F 0 * min ((2 * t) ^ 2 / (8 * r ^ 2)) (1 / 2) / 4
      ≤ antiDisplacement F t := by
  have hlow := displacement_ge_min hF hFc hsupp (by linarith : (0:ℝ) < 2 * t)
  have hup := displacement_two_mul_le_antiDisplacement hF hFc t
  linarith


/-! ### No two integers align the test

Distinct integers have logarithms separated by at least the reciprocal of the larger, so the
quadratic gap applies at every ratio: the Gram entry at the lag `log(n/m)` is below the mass by at
least `1/(8r²n²)` of it.  A test of fixed aperture cannot be nearly invariant under any ratio of
integers below its horizon. -/

theorem autoCorrelation_ratio_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    autoCorrelation F (Real.log (n : ℝ) - Real.log (m : ℝ))
      ≤ autoCorrelation F 0 * (1 - min ((1 / (n : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  have hA0 := autoCorrelation_zero_nonneg F
  have hn : (0:ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
    exact_mod_cast this
  have hgap := one_div_le_log_sub_log hm hmn
  have hinv : (0:ℝ) < 1 / (n : ℝ) := by positivity
  have hpos : 0 < Real.log (n : ℝ) - Real.log (m : ℝ) := lt_of_lt_of_le hinv hgap
  have hmain := autoCorrelation_le_min hF hFc hsupp hpos
  have hsq : (1 / (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ) - Real.log (m : ℝ)) ^ 2 := by
    nlinarith [hgap, hinv]
  have hdiv : (1 / (n : ℝ)) ^ 2 / (8 * r ^ 2)
      ≤ (Real.log (n : ℝ) - Real.log (m : ℝ)) ^ 2 / (8 * r ^ 2) := by
    have hnn : (0:ℝ) ≤ (8 * r ^ 2)⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsq hnn
  have hmono : min ((1 / (n : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2)
      ≤ min ((Real.log (n : ℝ) - Real.log (m : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2) :=
    min_le_min hdiv le_rfl
  nlinarith [hmain, hmono, hA0]


/-! ### A uniform discount for the aggregate below a horizon

All integers below a horizon `Y` have pairwise ratios separated by at least `1/Y` in the lag, so
every off-diagonal entry of the aggregate carries the same discount `min(1/(8r²Y²), ½)`.  The
`ℓ¹` bound for the cross-prime aggregate improves by exactly that factor. -/

theorem autoCorrelation_ratio_le_of_ne (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) {m n Y : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hmY : m ≤ Y) (hnY : n ≤ Y) :
    autoCorrelation F (Real.log (n : ℝ) - Real.log (m : ℝ))
      ≤ autoCorrelation F 0 * (1 - min ((1 / (Y : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2)) := by
  have hA0 := autoCorrelation_zero_nonneg F
  have hstep : ∀ k : ℕ, 0 < k → k ≤ Y →
      min ((1 / (Y : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2)
        ≤ min ((1 / (k : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2) := by
    intro k hk hkY
    refine min_le_min ?_ le_rfl
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hYR : (0:ℝ) < Y := by
      have : 0 < Y := lt_of_lt_of_le hk hkY
      exact_mod_cast this
    have hle : (1 / (Y : ℝ)) ≤ 1 / (k : ℝ) := by
      apply one_div_le_one_div_of_le hkR
      exact_mod_cast hkY
    have hsq : (1 / (Y : ℝ)) ^ 2 ≤ (1 / (k : ℝ)) ^ 2 := by
      have h0 : (0:ℝ) ≤ 1 / (Y : ℝ) := le_of_lt (by positivity)
      nlinarith
    have hnn : (0:ℝ) ≤ (8 * r ^ 2)⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsq hnn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hmain := autoCorrelation_ratio_le hF hFc hsupp hm hlt
    have hmono := hstep n hn hnY
    nlinarith [hmain, hmono, hA0]
  · have hmain := autoCorrelation_ratio_le hF hFc hsupp hn hgt
    have hmono := hstep m hm hmY
    rw [← autoCorrelation_neg F (Real.log (n : ℝ) - Real.log (m : ℝ)),
      show -(Real.log (n : ℝ) - Real.log (m : ℝ))
        = Real.log (m : ℝ) - Real.log (n : ℝ) by ring]
    nlinarith [hmain, hmono, hA0]

/-- **The aggregate with the uniform ratio discount.** -/
theorem crossAggregate_le_gap (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    {Y : ℕ} (hpos : ∀ p ∈ P, 0 < p) (hle : ∀ p ∈ P, p ≤ Y) :
    ∑ p ∈ P, ∑ q ∈ P.erase p, w p * w q * autoCorrelation F (Real.log (q : ℝ) - Real.log (p : ℝ))
      ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, w p * w q
          * (autoCorrelation F 0 * (1 - min ((1 / (Y : ℝ)) ^ 2 / (8 * r ^ 2)) (1 / 2))) := by
  refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
  have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
  have hqP : q ∈ P := (Finset.mem_erase.mp hq).2
  exact mul_le_mul_of_nonneg_left
    (autoCorrelation_ratio_le_of_ne hF hFc hsupp (hpos p hp) (hpos q hqP) (Ne.symm hqp)
      (hle p hp) (hle q hqP))
    (mul_nonneg (hw p hp) (hw q hqP))


/-! ### The first window: below `log 2 / 2` there is no arithmetic

A test whose aperture satisfies `2r < log 2` sees no prime lag at all, so its prime side vanishes
identically and the balance reduces to the pole plane against the quiet-zone defect.  The first
prime window is therefore not an approximation but an exact statement: below that aperture the
ledger is purely archimedean. -/

theorem sum_lag_vonMangoldt_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h2r : 2 * r < Real.log 2) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases h1 : n ≤ 1
  · have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by interval_cases n <;> simp
    rw [hz, zero_mul]
  · have hn2 : (2:ℝ) ≤ n := by
      have : 2 ≤ n := by omega
      exact_mod_cast this
    have hlog : 2 * r ≤ Real.log (n : ℝ) :=
      le_trans (le_of_lt h2r) (Real.log_le_log (by norm_num) hn2)
    rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero, mul_zero]

/-- **The balance in the first window.**  The pole plane alone equals the Chebyshev residue. -/
theorem testBalance_firstWindow (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (h2r : 2 * r < Real.log 2) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    -(2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2))
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hb := testBalance_poleplane hF hFc hr hsupp hN
  rw [sum_lag_vonMangoldt_eq_zero hF.continuous hr hsupp h2r N] at hb
  linarith


/-! ### The first prime window, exactly

Once the aperture passes `log 2 / 2` and before it reaches `log 3 / 2` the prime side consists of
the single atom at `2`: the balance is

    √2 · log 2 · A(log 2) − 2(pole plane) = Chebyshev residue .

This is the first prime window as an identity, with no approximation: one atom, one pole plane,
one residue. -/

theorem sum_lag_vonMangoldt_firstAtom (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h2 : 2 * r < Real.log 3) (N : ℕ) (hN2 : 2 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = Real.sqrt 2 * Real.log 2 * autoCorrelation F (Real.log 2) := by
  have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    field_simp [ne_of_gt hsqrt2]
    linarith [hsq]
  rw [Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by omega)) (fun b _ hb => ?_)]
  · have h2c : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, h2c]
    have hlog2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [hlog2, hinv]
    ring
  · by_cases h1 : b ≤ 1
    · have hz : (ArithmeticFunction.vonMangoldt b : ℝ) = 0 := by interval_cases b <;> simp
      rw [hz, zero_mul]
    · have hb3 : (3:ℝ) ≤ b := by
        have : 3 ≤ b := by omega
        exact_mod_cast this
      have hlog : 2 * r ≤ Real.log (b : ℝ) :=
        le_trans (le_of_lt h2) (Real.log_le_log (by norm_num) hb3)
      rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero, mul_zero]

/-- **The balance in the first prime window.** -/
theorem testBalance_firstAtom (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (h2 : 2 * r < Real.log 3) {N : ℕ}
    (hN2 : 2 ≤ N) (hN : Real.exp (2 * r) ≤ N) :
    Real.sqrt 2 * Real.log 2 * autoCorrelation F (Real.log 2)
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hb := testBalance_poleplane hF hFc hr hsupp hN
  rw [sum_lag_vonMangoldt_firstAtom hF.continuous hr hsupp h2 N hN2] at hb
  exact hb


/-! ### The first window's explicit bound

Inside the first prime window the aperture is below `log 2`, so the half law applies at the single
atom and the pole charge of an odd test is minus a square.  The residue is then bounded by an
explicit expression in the test's mass and its half-exponential moment alone — the first window
is completely scored. -/

theorem log_three_lt_two_mul_log_two : Real.log 3 < 2 * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_lt_log (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) < 4)
  linarith [h4]

/-- **The residue in the first prime window is explicitly bounded.** -/
theorem residue_firstAtom_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (h2 : 2 * r < Real.log 3)
    (hodd : ∀ x, F (-x) = -F x) {N : ℕ} (hN2 : 2 ≤ N) (hN : Real.exp (2 * r) ≤ N) :
    (∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)))
      ≤ Real.sqrt 2 * Real.log 2 * (autoCorrelation F 0 / 2)
        + 2 * expMomentNeg F ^ 2 := by
  have hrlog : r < Real.log 2 := by
    have := log_three_lt_two_mul_log_two
    linarith
  have hhalf := autoCorrelation_le_half hF.continuous hFc hsupp hrlog
  have hbal := testBalance_firstAtom hF hFc hr hsupp h2 hN2 hN
  have hpole := poleplane_odd hF.continuous hFc hodd
  have hsqrt2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcoef : (0:ℝ) ≤ Real.sqrt 2 * Real.log 2 := mul_nonneg hsqrt2 hlog2
  have hatom : Real.sqrt 2 * Real.log 2 * autoCorrelation F (Real.log 2)
      ≤ Real.sqrt 2 * Real.log 2 * (autoCorrelation F 0 / 2) :=
    mul_le_mul_of_nonneg_left hhalf hcoef
  rw [← hbal, hpole]
  linarith


/-! ### The second prime window

Between `log 3 / 2` and `log 4 / 2` the prime side is the two atoms at `2` and `3`.  The balance
is again an identity with a finite, completely explicit left-hand side. -/

theorem sum_lag_vonMangoldt_secondWindow (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h4 : 2 * r < Real.log 4) (N : ℕ) (hN3 : 3 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = 2 * (Real.sqrt 2)⁻¹ * Real.log 2 * autoCorrelation F (Real.log 2)
        + 2 * (Real.sqrt 3)⁻¹ * Real.log 3 * autoCorrelation F (Real.log 3) := by
  have hsub : Finset.Icc 2 3 ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  have hout : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.Icc 2 3 →
      (ArithmeticFunction.vonMangoldt x : ℝ) *
        (2 * (Real.sqrt x)⁻¹ * autoCorrelation F (Real.log x)) = 0 := by
    intro x _ hnot
    rw [Finset.mem_Icc] at hnot
    by_cases h1 : x ≤ 1
    · have hz : (ArithmeticFunction.vonMangoldt x : ℝ) = 0 := by interval_cases x <;> simp
      rw [hz, zero_mul]
    · have hx4 : (4:ℝ) ≤ x := by
        have : 4 ≤ x := by omega
        exact_mod_cast this
      have hlog : 2 * r ≤ Real.log (x : ℝ) :=
        le_trans (le_of_lt h4) (Real.log_le_log (by norm_num) hx4)
      rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero, mul_zero]
  rw [← Finset.sum_subset hsub hout,
    Finset.sum_Icc_succ_top (by omega : 2 ≤ 2 + 1), Finset.Icc_self, Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num
  ring


/-! ### The third prime window, where the first prime power enters

Between `log 4 / 2` and `log 5 / 2` a third atom appears, and it is not a prime: it is `4 = 2²`,
carrying the weight `Λ(4) = log 2` at the lag `log 4`.  This is the first aperture at which the
Chebyshev source and the prime-only source differ, and the difference is visible in the identity
itself. -/

theorem sum_lag_vonMangoldt_thirdWindow (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h5 : 2 * r < Real.log 5) (N : ℕ) (hN4 : 4 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = 2 * (Real.sqrt 2)⁻¹ * Real.log 2 * autoCorrelation F (Real.log 2)
        + 2 * (Real.sqrt 3)⁻¹ * Real.log 3 * autoCorrelation F (Real.log 3)
        + Real.log 2 * autoCorrelation F (Real.log 4) := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hsub : Finset.Icc 2 4 ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  have hout : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.Icc 2 4 →
      (ArithmeticFunction.vonMangoldt x : ℝ) *
        (2 * (Real.sqrt x)⁻¹ * autoCorrelation F (Real.log x)) = 0 := by
    intro x _ hnot
    rw [Finset.mem_Icc] at hnot
    by_cases h1 : x ≤ 1
    · have hz : (ArithmeticFunction.vonMangoldt x : ℝ) = 0 := by interval_cases x <;> simp
      rw [hz, zero_mul]
    · have hx5 : (5:ℝ) ≤ x := by
        have : 5 ≤ x := by omega
        exact_mod_cast this
      have hlog : 2 * r ≤ Real.log (x : ℝ) :=
        le_trans (le_of_lt h5) (Real.log_le_log (by norm_num) hx5)
      rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero, mul_zero]
  rw [← Finset.sum_subset hsub hout,
    Finset.sum_Icc_succ_top (by omega : 2 ≤ 3 + 1),
    Finset.sum_Icc_succ_top (by omega : 2 ≤ 2 + 1), Finset.Icc_self, Finset.sum_singleton]
  norm_num
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,
    show (4:ℕ) = 2 ^ 2 from rfl,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num
  ring


/-! ### The ledger of an arithmetic progression

Restricting the atoms to a residue class gives a source whose density is a fixed fraction of the
whole, so its calibration is the two-pole weight scaled by that fraction.  The balance holds for
every scale factor, and the defect is the progression's own error term: the receiver of this
ledger is the Riemann hypothesis for the corresponding Dirichlet characters. -/

/-- The scaled two-pole calibration. -/
def scaledTwoPoleWeight (c : ℝ) (s : ℝ) : ℝ := c * twoPoleWeight s

theorem scaledTwoPoleWeight_zero (c : ℝ) : scaledTwoPoleWeight c 0 = 0 := by
  rw [scaledTwoPoleWeight, twoPoleWeight_zero, mul_zero]

theorem hasDerivAt_scaledTwoPoleWeight (c : ℝ) (s : ℝ) :
    HasDerivAt (scaledTwoPoleWeight c) (c * (Real.exp s + 1)) s :=
  (hasDerivAt_twoPoleWeight s).const_mul c

/-- The atoms of `ψ(x; q, a)`. -/
def apSource (q a : ℕ) : ℕ → ℝ :=
  fun n => if n % q = a then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

theorem apSource_zero (q a : ℕ) : apSource q a 0 = 0 := by
  rw [apSource]
  by_cases h : 0 % q = a
  · rw [if_pos h]; simp
  · rw [if_neg h]

theorem apSource_one (q a : ℕ) : apSource q a 1 = 0 := by
  rw [apSource]
  by_cases h : 1 % q = a
  · rw [if_pos h]; simp
  · rw [if_neg h]

theorem apSource_le_vonMangoldt (q a : ℕ) (n : ℕ) :
    apSource q a n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [apSource]
  by_cases h : n % q = a
  · rw [if_pos h]
  · rw [if_neg h]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- **The balance for a residue class against a scaled two-pole calibration.** -/
theorem sum_ap_sub_scaledPolar_eq_defect (q a : ℕ) (c : ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), apSource q a n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), c * (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ),
          (scaledTwoPoleWeight c s - lagPrefix (apSource q a) s) * deriv h s :=
  sum_weight_sub_calibration_eq_defect (apSource q a) (apSource_zero q a) (apSource_one q a)
    (scaledTwoPoleWeight_zero c) (continuous_const.mul continuous_twoPoleWeight)
    (by fun_prop) (hasDerivAt_scaledTwoPoleWeight c) hh hS hvan hN

/-- A residue class never carries more than the whole Chebyshev count. -/
theorem lagPrefix_ap_le (q a : ℕ) (s : ℝ) :
    lagPrefix (apSource q a) s ≤ lagChebyshev s :=
  lagPrefix_mono_of_le (apSource_le_vonMangoldt q a) s


/-! ### The residue ledgers partition the Chebyshev ledger

Summing the residue classes recovers `Λ` index by index, hence the prefixes add to the Chebyshev
count.  So whenever the scale factors of the class calibrations sum to one, the class defects add
to exactly the Chebyshev defect: the ledger of `ζ` is the sum of the ledgers of the progressions,
with no cross terms. -/

theorem sum_apSource_eq {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∑ a ∈ Finset.range q, apSource q a n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hmem : n % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ hq)
  rw [Finset.sum_eq_single_of_mem (n % q) hmem (fun b _ hb => ?_)]
  · rw [apSource, if_pos rfl]
  · rw [apSource, if_neg (fun hc => hb hc.symm)]

theorem sum_lagPrefix_ap {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ∑ a ∈ Finset.range q, lagPrefix (apSource q a) s = lagChebyshev s := by
  rw [lagChebyshev]
  simp only [lagPrefix]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => sum_apSource_eq hq k

/-- **The class defects add to the Chebyshev defect.** -/
theorem sum_defect_ap {q : ℕ} (hq : 0 < q) (c : ℕ → ℝ)
    (hc : ∑ a ∈ Finset.range q, c a = 1) (s : ℝ) :
    ∑ a ∈ Finset.range q, (scaledTwoPoleWeight (c a) s - lagPrefix (apSource q a) s)
      = chebyshevTwoPoleDefect s := by
  rw [Finset.sum_sub_distrib, sum_lagPrefix_ap hq s]
  have hW : ∑ a ∈ Finset.range q, scaledTwoPoleWeight (c a) s
      = (∑ a ∈ Finset.range q, c a) * twoPoleWeight s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => rfl
  rw [hW, hc, one_mul, chebyshevTwoPoleDefect]


/-! ### The shifted pair, read at its own poles

`ζ(s−α)ζ(s+α)` has poles at `1+α` and `1−α`, so its calibration is the sum of the two pole
weights there.  Against that calibration the shifted pair's ledger is the balance it deserves;
against `ζ`'s two-pole weight it is off by the whole of `e^{(1+α)s}/(1+α)`, which is larger than
the main term.  The separation of the shifted pair from `ζ` is therefore not a
prime-number-theorem effect but a difference of pole position. -/

/-- The calibration of a pair of poles at `1 ± α`, with both reflected poles. -/
def pairCalibration (α : ℝ) (s : ℝ) : ℝ := poleWeightAt (1 + α) s + poleWeightAt (1 - α) s

theorem pairCalibration_zero (α : ℝ) : pairCalibration α 0 = 0 := by
  rw [pairCalibration, poleWeightAt_zero, poleWeightAt_zero, add_zero]

theorem continuous_pairCalibration (α : ℝ) : Continuous (pairCalibration α) :=
  (continuous_poleWeightAt _).add (continuous_poleWeightAt _)

theorem hasDerivAt_pairCalibration {α : ℝ} (h1 : 1 + α ≠ 0) (h2 : 1 - α ≠ 0) (s : ℝ) :
    HasDerivAt (pairCalibration α)
      (Real.exp ((1 + α) * s) + 1 + (Real.exp ((1 - α) * s) + 1)) s :=
  (hasDerivAt_poleWeightAt h1 s).add (hasDerivAt_poleWeightAt h2 s)

/-- **The balance for the shifted pair at its own poles.** -/
theorem sum_shiftedPair_sub_pairPolar_eq_defect (α : ℝ) (h1 : 1 + α ≠ 0) (h2 : 1 - α ≠ 0)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), shiftedPairWeight α n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ),
            (Real.exp ((1 + α) * s) + 1 + (Real.exp ((1 - α) * s) + 1)) * h s
      = ∫ s in Ioi (0:ℝ),
          (pairCalibration α s - lagPrefix (shiftedPairWeight α) s) * deriv h s :=
  sum_weight_sub_calibration_eq_defect (shiftedPairWeight α) (shiftedPairWeight_zero α)
    (shiftedPairWeight_one α) (pairCalibration_zero α) (continuous_pairCalibration α)
    (by fun_prop) (hasDerivAt_pairCalibration h1 h2) hh hS hvan hN

/-- The two calibrations differ by the whole of the shifted pole's growth. -/
theorem pairCalibration_sub_twoPoleWeight (α : ℝ) (s : ℝ) :
    pairCalibration α s - twoPoleWeight s
      = (Real.exp ((1 + α) * s) - 1) / (1 + α) + (Real.exp ((1 - α) * s) - 1) / (1 - α)
        + s - (Real.exp s - 1) := by
  rw [pairCalibration, poleWeightAt, poleWeightAt, twoPoleWeight]
  ring


/-! ### An odd test carries half its energy on each side

The two halves of a test split its mass, and for an odd test the reflection makes the two halves
carry exactly half each.  Every bipartite estimate that is stated in terms of the left half's
energy is therefore an estimate in terms of half the mass. -/

theorem integrable_rightPart_sq (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable fun x => rightPart F x ^ 2 := by
  refine (integrable_rightPart_shift_mul hF hFc 0 0).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show rightPart F (x + 0) * rightPart F (x + 0) = rightPart F x ^ 2
  rw [add_zero, sq]

theorem integral_halves_add (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∫ x, leftPart F x ^ 2) + ∫ x, rightPart F x ^ 2 = autoCorrelation F 0 := by
  rw [← MeasureTheory.integral_add (integrable_leftPart_sq hF hFc)
    (integrable_rightPart_sq hF hFc), autoCorrelation_zero_eq]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (leftPart_sq_add_rightPart_sq F))

theorem integral_leftPart_sq_eq_rightPart_sq (hodd : ∀ x, F (-x) = -F x) :
    (∫ x, leftPart F x ^ 2) = ∫ x, rightPart F x ^ 2 := by
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun x => rightPart F x ^ 2)
  rw [← hrefl]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show leftPart F x ^ 2 = rightPart F (-x) ^ 2
  rw [leftPart_eq_neg_rightPart_neg hodd x, neg_sq]

/-- **Each half of an odd test carries half the mass.** -/
theorem integral_leftPart_sq_eq_half (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) :
    (∫ x, leftPart F x ^ 2) = autoCorrelation F 0 / 2 := by
  have hadd := integral_halves_add hF hFc
  have heq := integral_leftPart_sq_eq_rightPart_sq (F := F) hodd
  linarith

theorem integral_rightPart_sq_eq_half (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) :
    (∫ x, rightPart F x ^ 2) = autoCorrelation F 0 / 2 := by
  have hadd := integral_halves_add hF hFc
  have heq := integral_leftPart_sq_eq_rightPart_sq (F := F) hodd
  linarith


/-! ### The optimised bipartite bound on an odd test

On an odd test the left half's energy is exactly half the mass, so the bipartite bound becomes an
estimate in the two quantities the programme actually grades: the mass of the test and the Schur
constant of the half-test's ratio correlations. -/

theorem sum_lag_le_sqrt_odd (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) {T : Finset ℕ}
    {c lag : ℕ → ℝ} (hc : ∀ n ∈ T, 0 ≤ c n) (hlag : ∀ n ∈ T, r < lag n) {R : ℝ}
    (hR0 : 0 ≤ R)
    (hR : ∀ n ∈ T, ∑ m ∈ T, |autoCorrelation (rightPart F) (lag m - lag n)| ≤ R) :
    ∑ n ∈ T, c n * autoCorrelation F (lag n)
      ≤ Real.sqrt (autoCorrelation F 0 / 2 * (R * ∑ n ∈ T, c n ^ 2)) := by
  have hbase := sum_lag_le_sqrt hF hFc hsupp hc hlag hR0 hR
  rwa [integral_leftPart_sq_eq_half hF hFc hodd] at hbase


/-! ### The ledger's leading rate is the prime number theorem

Dividing the defect by the main term, the elementary part of the calibration contributes nothing
in the limit, so the defect is `o(e^s)` exactly when the Chebyshev count is asymptotic to the
main term.  The leading rate of the ledger *is* the prime number theorem — the deeper rates are
what the receiver measures. -/

theorem tendsto_linear_div_exp :
    Filter.Tendsto (fun s : ℝ => (s - 1) / Real.exp s) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun s : ℝ => s ^ 1 * Real.exp (-s)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Filter.Tendsto (fun s : ℝ => s ^ 0 * Real.exp (-s)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  refine hsub.congr fun s => ?_
  rw [Real.exp_neg, pow_one, pow_zero]
  field_simp

/-- **`E(s) = o(e^s)` is the prime number theorem.** -/
theorem tendsto_chebyshevTwoPoleDefect_div_exp_iff :
    Filter.Tendsto (fun s => chebyshevTwoPoleDefect s / Real.exp s) Filter.atTop (nhds 0)
      ↔ Filter.Tendsto (fun s => lagChebyshev s / Real.exp s) Filter.atTop (nhds 1) := by
  have hsplit : ∀ s : ℝ, chebyshevTwoPoleDefect s / Real.exp s
      = 1 + (s - 1) / Real.exp s - lagChebyshev s / Real.exp s := by
    intro s
    rw [chebyshevTwoPoleDefect, twoPoleWeight]
    field_simp
    ring
  have hlin := tendsto_linear_div_exp
  constructor
  · intro hE
    have hE' : Filter.Tendsto
        (fun s => 1 + (s - 1) / Real.exp s - lagChebyshev s / Real.exp s)
        Filter.atTop (nhds 0) := hE.congr hsplit
    have hdiff := (Filter.Tendsto.const_add (1:ℝ) hlin).sub hE'
    rw [show (1:ℝ) + 0 - 0 = 1 by ring] at hdiff
    refine hdiff.congr fun s => ?_
    ring
  · intro hpsi
    have hcomb := (Filter.Tendsto.const_add (1:ℝ) hlin).sub hpsi
    rw [show (1:ℝ) + 0 - 1 = 0 by ring] at hcomb
    exact hcomb.congr fun s => (hsplit s).symm


/-! ### The same for the Mertens ledger

The reflected pole contributes nothing in the limit either, so the Mertens defect is `o(e^s)`
exactly when `M(x) = o(x)` — the Möbius form of the prime number theorem.  Both ledgers have the
prime number theorem as their leading rate, and differ only beyond it. -/

theorem tendsto_id_div_exp :
    Filter.Tendsto (fun s : ℝ => s / Real.exp s) Filter.atTop (nhds 0) := by
  refine (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).congr fun s => ?_
  rw [Real.exp_neg, pow_one]
  field_simp

/-- **The Mertens defect is `o(e^s)` exactly when `M(x) = o(x)`.** -/
theorem tendsto_mertensDefect_div_exp_iff :
    Filter.Tendsto (fun s => (s - lagMertens s) / Real.exp s) Filter.atTop (nhds 0)
      ↔ Filter.Tendsto (fun s => lagMertens s / Real.exp s) Filter.atTop (nhds 0) := by
  have hsplit : ∀ s : ℝ, (s - lagMertens s) / Real.exp s
      = s / Real.exp s - lagMertens s / Real.exp s := fun s => by
    rw [sub_div]
  have hlin := tendsto_id_div_exp
  constructor
  · intro hE
    have hE' : Filter.Tendsto (fun s => s / Real.exp s - lagMertens s / Real.exp s)
        Filter.atTop (nhds 0) := hE.congr hsplit
    have hdiff := hlin.sub hE'
    rw [sub_zero] at hdiff
    refine hdiff.congr fun s => ?_
    ring
  · intro hM
    have hcomb := hlin.sub hM
    rw [sub_zero] at hcomb
    exact hcomb.congr fun s => (hsplit s).symm


/-! ### Which calibrations an integer source can match

The obstruction is entirely the size of the calibration's increment across an integer cell.  If
those increments are bounded by `K`, differencing the calibration at the integers realises it with
defect at most `K`; and conversely, for *any* source the defect must absorb the increment across
each cell, since the prefix is frozen there.  So a calibration is matchable to `O(1)` by an
integer source exactly when its integer-cell increments are bounded — which is why a simple pole
at `1` works, a pole beyond `1` does not, and a double pole at `1` does not either. -/

/-- **Differencing a calibration realises it, with defect its largest cell increment.** -/
theorem abs_defect_sourceOfPrefix_le {W : ℝ → ℝ} (hWmono : Monotone W) (hW0 : W 0 = 0)
    {K : ℝ} (hK : ∀ N : ℕ, 1 ≤ N →
      W (Real.log ((N : ℝ) + 1)) - W (Real.log (N : ℝ)) ≤ K) {s : ℝ} (hs : 0 ≤ s) :
    |W s - lagPrefix (sourceOfPrefix fun n => W (Real.log (n : ℝ))) s| ≤ K := by
  set N : ℕ := ⌊Real.exp s⌋₊ with hNdef
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexp1)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hNlt : Real.exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogN : Real.log (N : ℝ) ≤ s := by
    have := Real.log_le_log hN0 hNle
    rwa [Real.log_exp] at this
  have hlogN1 : s < Real.log ((N : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos s) hNlt
    rwa [Real.log_exp] at this
  have hpref : lagPrefix (sourceOfPrefix fun n => W (Real.log (n : ℝ))) s
      = W (Real.log (N : ℝ)) := by
    rw [lagPrefix_sourceOfPrefix, Nat.cast_zero, Real.log_zero, hW0, sub_zero]
  rw [hpref, abs_of_nonneg (by linarith [hWmono hlogN])]
  have hup := hWmono (le_of_lt hlogN1)
  linarith [hK N hN1]

/-- **Conversely, every source's defect must absorb the cell increment.** -/
theorem cell_increment_le_two_mul_defect (a : ℕ → ℝ) (W : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    W (Real.log ((N : ℝ) + 1 / 2)) - W (Real.log (N : ℝ))
      ≤ 2 * max |W (Real.log (N : ℝ)) - lagPrefix a (Real.log (N : ℝ))|
              |W (Real.log ((N : ℝ) + 1 / 2)) - lagPrefix a (Real.log ((N : ℝ) + 1 / 2))| := by
  have hpref := lagPrefix_eq_on_half_cell a hN
  set x := W (Real.log (N : ℝ)) - lagPrefix a (Real.log (N : ℝ)) with hx
  set y := W (Real.log ((N : ℝ) + 1 / 2))
    - lagPrefix a (Real.log ((N : ℝ) + 1 / 2)) with hy
  have hdiff : y - x = W (Real.log ((N : ℝ) + 1 / 2)) - W (Real.log (N : ℝ)) := by
    rw [hx, hy, hpref]
    ring
  have hb1 := neg_abs_le x
  have hb2 := le_abs_self y
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  linarith


/-! ### The matchability criterion in action

The criterion classifies the calibrations an integer-indexed source can track.  A finite family
of simple poles in `(0,1]` is matchable, with defect the sum of the reciprocal exponents; the
reflected pole alone is matchable with defect `log 2`; and a *double* pole at `1` is not
matchable at all — its cell increment grows like `log N`, which is exactly the Stirling loss of
the logarithm source.  The criterion also holds verbatim for an arbitrary lag system: the defect
must absorb the calibration's increment across every gap. -/

/-- The increment of a simple-pole calibration across an integer cell. -/
theorem poleWeightAt_cell_increment_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    poleWeightAt ρ (Real.log ((N : ℝ) + 1)) - poleWeightAt ρ (Real.log (N : ℝ))
      ≤ 1 / ρ + Real.log 2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hgap : Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) ≤ Real.log 2 := by
    have h2N : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1:ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hmul := Real.log_le_log (by linarith) h2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hN0)] at hmul
    linarith
  have hrpow : ((N : ℝ) + 1) ^ ρ ≤ (N : ℝ) ^ ρ + 1 := by
    have h := Real.rpow_add_le_add_rpow (a := (N : ℝ)) (b := 1) hN0.le zero_le_one hρ.le hρ1
    rwa [Real.one_rpow] at h
  have hval1 : poleWeightAt ρ (Real.log ((N : ℝ) + 1))
      = (((N : ℝ) + 1) ^ ρ - 1) / ρ + Real.log ((N : ℝ) + 1) := by
    rw [poleWeightAt, exp_mul_log ρ (by linarith : (0:ℝ) < (N : ℝ) + 1)]
  have hval2 : poleWeightAt ρ (Real.log (N : ℝ))
      = ((N : ℝ) ^ ρ - 1) / ρ + Real.log (N : ℝ) := by
    rw [poleWeightAt, exp_mul_log ρ hN0]
  rw [hval1, hval2]
  have hdiv : (((N : ℝ) + 1) ^ ρ - 1) / ρ - ((N : ℝ) ^ ρ - 1) / ρ ≤ 1 / ρ := by
    rw [div_sub_div_same, div_le_div_iff₀ hρ hρ]
    nlinarith [hrpow, hρ]
  linarith

/-- A finite family of simple poles, as a calibration. -/
def multiPoleWeight (I : Finset ℕ) (c ρ : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ i ∈ I, c i * poleWeightAt (ρ i) s

theorem multiPoleWeight_zero (I : Finset ℕ) (c ρ : ℕ → ℝ) : multiPoleWeight I c ρ 0 = 0 := by
  rw [multiPoleWeight]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [poleWeightAt_zero, mul_zero]

theorem multiPoleWeight_mono {I : Finset ℕ} {c ρ : ℕ → ℝ} (hc : ∀ i ∈ I, 0 ≤ c i)
    (hρ : ∀ i ∈ I, 0 < ρ i) : Monotone (multiPoleWeight I c ρ) := by
  intro a b hab
  refine Finset.sum_le_sum fun i hi => ?_
  exact mul_le_mul_of_nonneg_left (poleWeightAt_mono (hρ i hi) hab) (hc i hi)

/-- **A finite family of simple poles in `(0,1]` is matchable by an integer source.** -/
theorem abs_defect_multiPole_le {I : Finset ℕ} {c ρ : ℕ → ℝ} (hc : ∀ i ∈ I, 0 ≤ c i)
    (hρ : ∀ i ∈ I, 0 < ρ i) (hρ1 : ∀ i ∈ I, ρ i ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    |multiPoleWeight I c ρ s
        - lagPrefix (sourceOfPrefix fun n => multiPoleWeight I c ρ (Real.log (n : ℝ))) s|
      ≤ ∑ i ∈ I, c i * (1 / ρ i + Real.log 2) := by
  refine abs_defect_sourceOfPrefix_le (multiPoleWeight_mono hc hρ)
    (multiPoleWeight_zero I c ρ) (fun N hN => ?_) hs
  rw [multiPoleWeight, multiPoleWeight, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left
    (poleWeightAt_cell_increment_le (hρ i hi) (hρ1 i hi) hN) (hc i hi)

/-- **The reflected pole alone is matchable with defect `log 2`.** -/
theorem abs_defect_reflectedPole_le {s : ℝ} (hs : 0 ≤ s) :
    |s - lagPrefix (sourceOfPrefix fun n => Real.log (n : ℝ)) s| ≤ Real.log 2 := by
  refine abs_defect_sourceOfPrefix_le (W := fun u : ℝ => u) monotone_id rfl (fun N hN => ?_) hs
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h2N : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hmul := Real.log_le_log (by linarith) h2N
  rw [Real.log_mul (by norm_num) (ne_of_gt hN0)] at hmul
  linarith

/-- **A double pole at `1` is not matchable:** its half-cell increment grows like `log N`. -/
theorem logWeight_half_cell_increment_ge {N : ℕ} (hN : 1 ≤ N) :
    (Real.log (N : ℝ) - 1) / 2
      ≤ logWeight (Real.log ((N : ℝ) + 1 / 2)) - logWeight (Real.log (N : ℝ)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hM1 : (0:ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hval1 : logWeight (Real.log ((N : ℝ) + 1 / 2))
      = (Real.log ((N : ℝ) + 1 / 2) - 1) * ((N : ℝ) + 1 / 2) + 1
        + Real.log ((N : ℝ) + 1 / 2) / 2 := by
    rw [logWeight, Real.exp_log hM1]
  have hval2 : logWeight (Real.log (N : ℝ))
      = (Real.log (N : ℝ) - 1) * (N : ℝ) + 1 + Real.log (N : ℝ) / 2 := by
    rw [logWeight, Real.exp_log hN0]
  have hmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) :=
    Real.log_le_log hN0 (by linarith)
  rw [hval1, hval2]
  nlinarith [hmono, hM1]

theorem defect_logWeight_ge (a : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (Real.log (N : ℝ) - 1) / 4
      ≤ max |logWeight (Real.log (N : ℝ)) - lagPrefix a (Real.log (N : ℝ))|
            |logWeight (Real.log ((N : ℝ) + 1 / 2))
              - lagPrefix a (Real.log ((N : ℝ) + 1 / 2))| := by
  have h1 := logWeight_half_cell_increment_ge hN
  have h2 := cell_increment_le_two_mul_defect a logWeight hN
  linarith

/-- **The criterion for an arbitrary lag system:** across a gap carrying no lag, the defect must
absorb the calibration's increment. -/
theorem gen_cell_increment_le_two_mul_defect (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ)
    {u v : ℝ} (huv : u ≤ v) (hgap : ∀ n ∈ T, lam n ≤ u ∨ v < lam n) :
    W v - W u
      ≤ 2 * max |W u - genPrefix T μ lam u| |W v - genPrefix T μ lam v| := by
  have hpref : genPrefix T μ lam v = genPrefix T μ lam u := by
    rw [genPrefix, genPrefix]
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases hgap n hn with hle | hgt
    · rw [if_pos (le_trans hle huv), if_pos hle]
    · rw [if_neg (not_le.mpr hgt), if_neg (not_le.mpr (lt_of_le_of_lt huv hgt))]
  set x := W u - genPrefix T μ lam u with hx
  set y := W v - genPrefix T μ lam v with hy
  have hdiff : y - x = W v - W u := by
    rw [hx, hy, hpref]
    ring
  have hb1 := neg_abs_le x
  have hb2 := le_abs_self y
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  linarith


/-! ### How fine a lag system must be to carry a pole at `1`

Across any interval carrying no lag the defect must absorb the calibration's increment, which for
the pole at `1` is at least `e^s(e^δ − 1)`.  So a lag system with bounded defect must place a lag
in every interval of length `δ` with `e^s(e^δ − 1) > 2K`: the pole at `1` *forces* the density of
the generalised primes.  The integers meet this exactly — their gap at scale `log N` gives
`e^s(e^δ − 1) = 1` — while a geometric system, whose gaps do not shrink, fails by a factor of the
main term. -/

/-- **The gap criterion for the pole at `1`.** -/
theorem defect_ge_of_gap (T : Finset ℕ) (μ lam : ℕ → ℝ) {s δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ n ∈ T, lam n ≤ s ∨ s + δ < lam n) :
    Real.exp s * (Real.exp δ - 1) / 2
      ≤ max |twoPoleWeight s - genPrefix T μ lam s|
            |twoPoleWeight (s + δ) - genPrefix T μ lam (s + δ)| := by
  have hincr : Real.exp s * (Real.exp δ - 1)
      ≤ twoPoleWeight (s + δ) - twoPoleWeight s := by
    rw [twoPoleWeight, twoPoleWeight, Real.exp_add]
    nlinarith [hδ]
  have hcrit := gen_cell_increment_le_two_mul_defect T μ lam twoPoleWeight
    (by linarith : s ≤ s + δ) hgap
  linarith

/-- **No weights on geometric lags can carry the pole at `1`.** -/
theorem geoLags_defect_ge (T : Finset ℕ) (μ : ℕ → ℝ) {g : ℝ} (hg : 1 < g) (N : ℕ) :
    g ^ N * (Real.sqrt g - 1) / 2
      ≤ max |twoPoleWeight ((N : ℝ) * Real.log g)
              - genPrefix T μ (geoLag g) ((N : ℝ) * Real.log g)|
            |twoPoleWeight (((N : ℝ) + 1 / 2) * Real.log g)
              - genPrefix T μ (geoLag g) (((N : ℝ) + 1 / 2) * Real.log g)| := by
  have hg0 : (0:ℝ) < g := by linarith
  have hlog : 0 < Real.log g := Real.log_pos hg
  have hsplit : ((N : ℝ) + 1 / 2) * Real.log g
      = (N : ℝ) * Real.log g + 1 / 2 * Real.log g := by ring
  have hgap : ∀ n ∈ T, geoLag g n ≤ (N : ℝ) * Real.log g
      ∨ (N : ℝ) * Real.log g + 1 / 2 * Real.log g < geoLag g n := by
    intro n _
    rcases le_or_gt n N with hle | hgt
    · left
      have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
      rw [geoLag]
      nlinarith
    · right
      have : (N : ℝ) + 1 ≤ (n : ℝ) := by
        have : N + 1 ≤ n := hgt
        exact_mod_cast this
      rw [geoLag]
      nlinarith
  have hbase := defect_ge_of_gap T μ (geoLag g) (by positivity) hgap
  rw [← hsplit] at hbase
  have hexpN : Real.exp ((N : ℝ) * Real.log g) = g ^ N := by
    rw [exp_mul_log _ hg0, Real.rpow_natCast]
  have hexph : Real.exp (1 / 2 * Real.log g) = Real.sqrt g := by
    rw [exp_mul_log _ hg0, Real.sqrt_eq_rpow]
  rw [hexpN, hexph] at hbase
  exact hbase

/-- **The integers meet the criterion exactly:** their gap at scale `log N` gives increment `1`. -/
theorem integer_gap_increment {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (Real.log (N : ℝ)) * (Real.exp (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) - 1)
      = 1 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  rw [Real.exp_sub, Real.exp_log hN0, Real.exp_log (by linarith : (0:ℝ) < (N : ℝ) + 1)]
  field_simp
  ring

/-- **A bounded defect forces a lag in every sufficiently long interval.** -/
theorem exists_lag_of_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) {s δ K : ℝ} (hδ : 0 ≤ δ)
    (hK1 : |twoPoleWeight s - genPrefix T μ lam s| ≤ K)
    (hK2 : |twoPoleWeight (s + δ) - genPrefix T μ lam (s + δ)| ≤ K)
    (hbig : 2 * K < Real.exp s * (Real.exp δ - 1)) :
    ∃ n ∈ T, s < lam n ∧ lam n ≤ s + δ := by
  by_contra hcon
  have hgap : ∀ n ∈ T, lam n ≤ s ∨ s + δ < lam n := by
    intro n hn
    rcases le_or_gt (lam n) s with hle | hgt
    · exact Or.inl hle
    · rcases le_or_gt (lam n) (s + δ) with hle2 | hgt2
      · exact absurd ⟨n, hn, hgt, hle2⟩ hcon
      · exact Or.inr hgt2
  have hlow := defect_ge_of_gap T μ lam hδ hgap
  have hmax : max |twoPoleWeight s - genPrefix T μ lam s|
      |twoPoleWeight (s + δ) - genPrefix T μ lam (s + δ)| ≤ K := max_le hK1 hK2
  linarith


/-! ### A bounded defect forces the generalised primes to be dense

Chaining the gap criterion along the scales `log(1 + 3Kj)`, each successive interval must contain
a lag, and the intervals are disjoint.  So a lag system holding its two-pole defect below `K` up
to the scale `log(1 + 3KJ)` must carry at least `J` lags: the counting function of any system
calibrating the pole at `1` is bounded below by `(e^S − 1)/3K`.  The density of the generalised
primes is not an input of the ledger but a consequence of it. -/

theorem card_ge_of_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) {K : ℝ} (hK : 0 < K) {J : ℕ}
    (hbound : ∀ s, 0 ≤ s → s ≤ Real.log (1 + 3 * K * (J : ℝ)) →
      |twoPoleWeight s - genPrefix T μ lam s| ≤ K) :
    J ≤ T.card := by
  classical
  set sc : ℕ → ℝ := fun j => Real.log (1 + 3 * K * (j : ℝ)) with hsc
  have hpos : ∀ j : ℕ, (0:ℝ) < 1 + 3 * K * (j : ℝ) := by
    intro j
    have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hone : ∀ j : ℕ, (1:ℝ) ≤ 1 + 3 * K * (j : ℝ) := by
    intro j
    have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hsnn : ∀ j : ℕ, 0 ≤ sc j := fun j => Real.log_nonneg (hone j)
  have hexp : ∀ j : ℕ, Real.exp (sc j) = 1 + 3 * K * (j : ℝ) :=
    fun j => Real.exp_log (hpos j)
  have hmono : ∀ j k : ℕ, j ≤ k → sc j ≤ sc k := by
    intro j k hjk
    refine Real.log_le_log (hpos j) ?_
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    nlinarith
  have hchoice : ∀ j : ℕ, j < J → ∃ n ∈ T, sc j < lam n ∧ lam n ≤ sc (j + 1) := by
    intro j hj
    have hδ : 0 ≤ sc (j + 1) - sc j := by linarith [hmono j (j + 1) (by omega)]
    have hsum : sc j + (sc (j + 1) - sc j) = sc (j + 1) := by ring
    have hb1 : |twoPoleWeight (sc j) - genPrefix T μ lam (sc j)| ≤ K :=
      hbound _ (hsnn j) (hmono j J (by omega))
    have hb2 : |twoPoleWeight (sc j + (sc (j + 1) - sc j))
        - genPrefix T μ lam (sc j + (sc (j + 1) - sc j))| ≤ K := by
      rw [hsum]
      exact hbound _ (hsnn (j + 1)) (hmono (j + 1) J (by omega))
    have hbig : 2 * K < Real.exp (sc j) * (Real.exp (sc (j + 1) - sc j) - 1) := by
      have hfac : Real.exp (sc j) * (Real.exp (sc (j + 1) - sc j) - 1)
          = Real.exp (sc (j + 1)) - Real.exp (sc j) := by
        rw [Real.exp_sub]
        field_simp
      rw [hfac, hexp, hexp]
      push_cast
      linarith
    obtain ⟨n, hnT, hn1, hn2⟩ := exists_lag_of_defect_le T μ lam hδ hb1 hb2 hbig
    exact ⟨n, hnT, hn1, by rwa [hsum] at hn2⟩
  choose! f hfT hf1 hf2 using hchoice
  have hinj : Set.InjOn f (Finset.range J : Finset ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : lam (f a) ≤ sc (a + 1) := hf2 a ha
      have h2 : sc b < lam (f b) := hf1 b hb
      have h3 : sc (a + 1) ≤ sc b := hmono (a + 1) b (by omega)
      rw [hab] at h1
      linarith
    · have h1 : lam (f b) ≤ sc (b + 1) := hf2 b hb
      have h2 : sc a < lam (f a) := hf1 a ha
      have h3 : sc (b + 1) ≤ sc a := hmono (b + 1) a (by omega)
      rw [hab] at h2
      linarith
  have hcard := Finset.card_le_card_of_injOn f
    (fun a ha => hfT a (Finset.mem_range.mp ha)) hinj
  rwa [Finset.card_range] at hcard


/-! ### The counting function is pinned on both sides, and the atoms must be small

The defect also bounds the count from above: the accumulated weight below a scale is at most the
calibration plus the defect, so a system whose atoms are all at least `m` can carry at most
`(W(s)+K)/m` lags below `s`.  Against the lower bound forced by the gap criterion this traps the
minimum atom size: a system calibrating the pole at `1` to within `K` cannot have all its atoms
much larger than `K`.  For `ζ` the atoms are `log p`, unbounded — which is the defect's
unboundedness seen from the density side. -/

open scoped Classical in
theorem card_filter_mul_le_of_defect (T : Finset ℕ) (μ lam : ℕ → ℝ) {K m s : ℝ}
    (hμ : ∀ n ∈ T, m ≤ μ n) (hb : |twoPoleWeight s - genPrefix T μ lam s| ≤ K) :
    ((T.filter (fun n : ℕ => lam n ≤ s)).card : ℝ) * m ≤ twoPoleWeight s + K := by
  have hrestrict : genPrefix T μ lam s = ∑ n ∈ T.filter (fun n : ℕ => lam n ≤ s), μ n := by
    rw [genPrefix, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hc : lam n ≤ s
    · rw [if_pos hc, if_pos hc, mul_one]
    · rw [if_neg hc, if_neg hc, mul_zero]
  have hlow : ((T.filter (fun n : ℕ => lam n ≤ s)).card : ℝ) * m
      ≤ ∑ n ∈ T.filter (fun n : ℕ => lam n ≤ s), μ n := by
    have h1 : ∑ _n ∈ T.filter (fun n : ℕ => lam n ≤ s), m
        ≤ ∑ n ∈ T.filter (fun n : ℕ => lam n ≤ s), μ n :=
      Finset.sum_le_sum fun n hn => hμ n (Finset.mem_filter.mp hn).1
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have habs := abs_le.mp hb
  rw [hrestrict] at habs
  linarith [hlow, habs.1]

/-- **The reflected pole forces only linear density.** -/
theorem gen_cell_increment_id (T : Finset ℕ) (μ lam : ℕ → ℝ) {u v : ℝ} (huv : u ≤ v)
    (hgap : ∀ n ∈ T, lam n ≤ u ∨ v < lam n) :
    v - u ≤ 2 * max |u - genPrefix T μ lam u| |v - genPrefix T μ lam v| :=
  gen_cell_increment_le_two_mul_defect T μ lam (fun s => s) huv hgap

/-- A system calibrating the reflected pole to within `K` has a lag in every interval longer
than `2K`. -/
theorem exists_lag_of_id_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) {u v K : ℝ} (huv : u ≤ v)
    (hK1 : |u - genPrefix T μ lam u| ≤ K) (hK2 : |v - genPrefix T μ lam v| ≤ K)
    (hbig : 2 * K < v - u) :
    ∃ n ∈ T, u < lam n ∧ lam n ≤ v := by
  by_contra hcon
  have hgap : ∀ n ∈ T, lam n ≤ u ∨ v < lam n := by
    intro n hn
    rcases le_or_gt (lam n) u with hle | hgt
    · exact Or.inl hle
    · rcases le_or_gt (lam n) v with hle2 | hgt2
      · exact absurd ⟨n, hn, hgt, hle2⟩ hcon
      · exact Or.inr hgt2
  have hlow := gen_cell_increment_id T μ lam huv hgap
  have hmax : max |u - genPrefix T μ lam u| |v - genPrefix T μ lam v| ≤ K := max_le hK1 hK2
  linarith

/-- **The atoms of a calibrating system cannot all be large.** -/
theorem min_atom_le_of_defect (T : Finset ℕ) (μ lam : ℕ → ℝ) {K m : ℝ} (hK : 0 < K) {J : ℕ}
    (hm : 0 ≤ m) (hμ : ∀ n ∈ T, m ≤ μ n)
    (hlam : ∀ n ∈ T, lam n ≤ Real.log (1 + 3 * K * (J : ℝ)))
    (hbound : ∀ s, 0 ≤ s → s ≤ Real.log (1 + 3 * K * (J : ℝ)) →
      |twoPoleWeight s - genPrefix T μ lam s| ≤ K) :
    (J : ℝ) * m ≤ twoPoleWeight (Real.log (1 + 3 * K * (J : ℝ))) + K := by
  classical
  have hcard := card_ge_of_defect_le T μ lam hK hbound
  have hfilter : T.filter (fun n : ℕ => lam n ≤ Real.log (1 + 3 * K * (J : ℝ))) = T := by
    refine Finset.filter_true_of_mem fun n hn => hlam n hn
  have hup := card_filter_mul_le_of_defect T μ lam (m := m) (s := Real.log (1 + 3 * K * (J : ℝ)))
    hμ (hbound _ (Real.log_nonneg (by
      have : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith)) le_rfl)
  rw [hfilter] at hup
  have hTJ : (J : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
  have hJm : (J : ℝ) * m ≤ (T.card : ℝ) * m := mul_le_mul_of_nonneg_right hTJ hm
  linarith


/-! ### The density a calibration forces is read off its own growth

The chain argument needs nothing about the calibration except that it climbs by more than `2K`
between consecutive scales.  So each pole position forces its own density of generalised primes:
the reflected pole alone forces linear density, a pole at `ρ` forces `x^ρ`, and the pole at `1`
forces `x`.  The exponent of the density is the position of the pole. -/

/-- **The chain criterion for an arbitrary calibration and scale sequence.** -/
theorem card_ge_of_defect_le_gen (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ) {K : ℝ}
    (sc : ℕ → ℝ) (hmono : Monotone sc) {J : ℕ}
    (hstep : ∀ j, j < J → 2 * K < W (sc (j + 1)) - W (sc j))
    (hbound : ∀ j, j ≤ J → |W (sc j) - genPrefix T μ lam (sc j)| ≤ K) :
    J ≤ T.card := by
  classical
  have hchoice : ∀ j : ℕ, j < J → ∃ n ∈ T, sc j < lam n ∧ lam n ≤ sc (j + 1) := by
    intro j hj
    by_contra hcon
    have hgap : ∀ n ∈ T, lam n ≤ sc j ∨ sc (j + 1) < lam n := by
      intro n hn
      rcases le_or_gt (lam n) (sc j) with hle | hgt
      · exact Or.inl hle
      · rcases le_or_gt (lam n) (sc (j + 1)) with hle2 | hgt2
        · exact absurd ⟨n, hn, hgt, hle2⟩ hcon
        · exact Or.inr hgt2
    have hcrit := gen_cell_increment_le_two_mul_defect T μ lam W
      (hmono (by omega : j ≤ j + 1)) hgap
    have hmax : max |W (sc j) - genPrefix T μ lam (sc j)|
        |W (sc (j + 1)) - genPrefix T μ lam (sc (j + 1))| ≤ K :=
      max_le (hbound j (by omega)) (hbound (j + 1) (by omega))
    linarith [hstep j hj]
  choose! f hfT hf1 hf2 using hchoice
  have hinj : Set.InjOn f (Finset.range J : Finset ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : lam (f a) ≤ sc (a + 1) := hf2 a ha
      have h2 : sc b < lam (f b) := hf1 b hb
      have h3 : sc (a + 1) ≤ sc b := hmono (by omega)
      rw [hab] at h1
      linarith
    · have h1 : lam (f b) ≤ sc (b + 1) := hf2 b hb
      have h2 : sc a < lam (f a) := hf1 a ha
      have h3 : sc (b + 1) ≤ sc a := hmono (by omega)
      rw [hab] at h2
      linarith
  have hcard := Finset.card_le_card_of_injOn f
    (fun a ha => hfT a (Finset.mem_range.mp ha)) hinj
  rwa [Finset.card_range] at hcard

/-- **The reflected pole forces linear density.** -/
theorem card_ge_of_id_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) {K : ℝ} (hK : 0 < K) {J : ℕ}
    (hbound : ∀ j, j ≤ J →
      |3 * K * (j : ℝ) - genPrefix T μ lam (3 * K * (j : ℝ))| ≤ K) :
    J ≤ T.card := by
  refine card_ge_of_defect_le_gen T μ lam (fun s => s) (fun j => 3 * K * (j : ℝ)) ?_ ?_ hbound
  · intro a b hab
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    nlinarith
  · intro j _
    push_cast
    linarith

/-- **A pole at `ρ` forces density `x^ρ`.** -/
theorem card_ge_of_poleAt_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) {K ρ : ℝ} (hK : 0 < K)
    (hρ : 0 < ρ) {J : ℕ}
    (hbound : ∀ j, j ≤ J →
      |poleWeightAt ρ (Real.log (1 + 3 * K * ρ * (j : ℝ)) / ρ)
        - genPrefix T μ lam (Real.log (1 + 3 * K * ρ * (j : ℝ)) / ρ)| ≤ K) :
    J ≤ T.card := by
  set sc : ℕ → ℝ := fun j => Real.log (1 + 3 * K * ρ * (j : ℝ)) / ρ with hsc
  have hcoef : (0:ℝ) ≤ 3 * K * ρ := by positivity
  have hpos : ∀ j : ℕ, (0:ℝ) < 1 + 3 * K * ρ * (j : ℝ) := by
    intro j
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have := mul_nonneg hcoef hj
    linarith
  have hmono : Monotone sc := by
    intro a b hab
    have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hmul : 3 * K * ρ * (a : ℝ) ≤ 3 * K * ρ * (b : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hcoef
    have hlog : Real.log (1 + 3 * K * ρ * (a : ℝ)) ≤ Real.log (1 + 3 * K * ρ * (b : ℝ)) :=
      Real.log_le_log (hpos a) (by linarith)
    rw [hsc]
    simp only []
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hlog (le_of_lt (inv_pos.mpr hρ))
  have hval : ∀ j : ℕ, poleWeightAt ρ (sc j) = 3 * K * (j : ℝ) + sc j := by
    intro j
    rw [poleWeightAt, hsc]
    have : ρ * (Real.log (1 + 3 * K * ρ * (j : ℝ)) / ρ)
        = Real.log (1 + 3 * K * ρ * (j : ℝ)) := by
      field_simp
    rw [this, Real.exp_log (hpos j)]
    field_simp
    ring
  refine card_ge_of_defect_le_gen T μ lam (poleWeightAt ρ) sc hmono ?_ hbound
  intro j _
  rw [hval, hval]
  have hstep : sc j ≤ sc (j + 1) := hmono (by omega)
  push_cast
  linarith


/-! ### Counting the atoms, not the indices

Indices carrying zero weight are invisible to the prefix, so the gap criterion really counts
*atoms*.  In that form it applies to `ζ` directly: a Chebyshev defect bounded by `K` up to the
scale `log(1+3KJ)` forces at least `J` prime powers below `1+3KJ`.  The density of the prime
powers is a consequence of the ledger's calibration, not an input to it. -/

theorem gen_cell_increment_le_two_mul_defect_supp (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ)
    {u v : ℝ} (huv : u ≤ v) (hgap : ∀ n ∈ T, μ n = 0 ∨ lam n ≤ u ∨ v < lam n) :
    W v - W u
      ≤ 2 * max |W u - genPrefix T μ lam u| |W v - genPrefix T μ lam v| := by
  have hpref : genPrefix T μ lam v = genPrefix T μ lam u := by
    rw [genPrefix, genPrefix]
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases hgap n hn with h0 | hle | hgt
    · rw [h0, zero_mul, zero_mul]
    · rw [if_pos (le_trans hle huv), if_pos hle]
    · rw [if_neg (not_le.mpr hgt), if_neg (not_le.mpr (lt_of_le_of_lt huv hgt))]
  set x := W u - genPrefix T μ lam u with hx
  set y := W v - genPrefix T μ lam v with hy
  have hdiff : y - x = W v - W u := by
    rw [hx, hy, hpref]
    ring
  have hb1 := neg_abs_le x
  have hb2 := le_abs_self y
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  linarith

open scoped Classical in
/-- **The chain criterion counts atoms.** -/
theorem card_support_ge_of_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ) {K : ℝ}
    (sc : ℕ → ℝ) (hmono : Monotone sc) {J : ℕ}
    (hstep : ∀ j, j < J → 2 * K < W (sc (j + 1)) - W (sc j))
    (hbound : ∀ j, j ≤ J → |W (sc j) - genPrefix T μ lam (sc j)| ≤ K) :
    J ≤ (T.filter (fun n : ℕ => μ n ≠ 0)).card := by
  have hchoice : ∀ j : ℕ, j < J →
      ∃ n ∈ T.filter (fun n : ℕ => μ n ≠ 0), sc j < lam n ∧ lam n ≤ sc (j + 1) := by
    intro j hj
    by_contra hcon
    have hgap : ∀ n ∈ T, μ n = 0 ∨ lam n ≤ sc j ∨ sc (j + 1) < lam n := by
      intro n hn
      by_cases h0 : μ n = 0
      · exact Or.inl h0
      · refine Or.inr ?_
        rcases le_or_gt (lam n) (sc j) with hle | hgt
        · exact Or.inl hle
        · rcases le_or_gt (lam n) (sc (j + 1)) with hle2 | hgt2
          · exact absurd ⟨n, Finset.mem_filter.mpr ⟨hn, h0⟩, hgt, hle2⟩ hcon
          · exact Or.inr hgt2
    have hcrit := gen_cell_increment_le_two_mul_defect_supp T μ lam W
      (hmono (by omega : j ≤ j + 1)) hgap
    have hmax : max |W (sc j) - genPrefix T μ lam (sc j)|
        |W (sc (j + 1)) - genPrefix T μ lam (sc (j + 1))| ≤ K :=
      max_le (hbound j (by omega)) (hbound (j + 1) (by omega))
    linarith [hstep j hj]
  choose! f hfT hf1 hf2 using hchoice
  have hinj : Set.InjOn f (Finset.range J : Finset ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : lam (f a) ≤ sc (a + 1) := hf2 a ha
      have h2 : sc b < lam (f b) := hf1 b hb
      have h3 : sc (a + 1) ≤ sc b := hmono (by omega)
      rw [hab] at h1
      linarith
    · have h1 : lam (f b) ≤ sc (b + 1) := hf2 b hb
      have h2 : sc a < lam (f a) := hf1 a ha
      have h3 : sc (b + 1) ≤ sc a := hmono (by omega)
      rw [hab] at h2
      linarith
  have hcard := Finset.card_le_card_of_injOn f
    (fun a ha => hfT a (Finset.mem_range.mp ha)) hinj
  rwa [Finset.card_range] at hcard

open scoped Classical in
/-- **A bounded Chebyshev defect forces many prime powers.** -/
theorem card_primePowers_ge_of_chebyshev_defect_le {K : ℝ} (hK : 0 < K) {J N : ℕ}
    (hN : 1 + 3 * K * (J : ℝ) ≤ (N : ℝ))
    (hbound : ∀ s, 0 ≤ s → s ≤ Real.log (1 + 3 * K * (J : ℝ)) →
      |chebyshevTwoPoleDefect s| ≤ K) :
    J ≤ ((Finset.range (N + 1)).filter
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0)).card := by
  set sc : ℕ → ℝ := fun j => Real.log (1 + 3 * K * (j : ℝ)) with hsc
  have hpos : ∀ j : ℕ, (0:ℝ) < 1 + 3 * K * (j : ℝ) := by
    intro j
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hone : ∀ j : ℕ, (1:ℝ) ≤ 1 + 3 * K * (j : ℝ) := by
    intro j
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hsnn : ∀ j : ℕ, 0 ≤ sc j := fun j => Real.log_nonneg (hone j)
  have hexp : ∀ j : ℕ, Real.exp (sc j) = 1 + 3 * K * (j : ℝ) :=
    fun j => Real.exp_log (hpos j)
  have hmono : Monotone sc := by
    intro a b hab
    refine Real.log_le_log (hpos a) ?_
    have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    nlinarith
  have hgenPrefix : ∀ j : ℕ, j ≤ J →
      genPrefix (Finset.range (N + 1)) (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => Real.log (n : ℝ)) (sc j) = lagChebyshev (sc j) := by
    intro j hj
    have hle : Real.exp (sc j) ≤ (N : ℝ) := by
      rw [hexp]
      have hjJ : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
      nlinarith
    rw [lagChebyshev_eq_lagPrefix,
      lagPrefix_eq_sum_step (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (hsnn j) hle]
    rfl
  refine card_support_ge_of_defect_le (K := K) (Finset.range (N + 1))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (fun n => Real.log (n : ℝ))
    twoPoleWeight sc hmono (fun j hj => ?_) (fun j hj => ?_)
  · rw [twoPoleWeight, twoPoleWeight, hexp, hexp]
    have hstep : sc j ≤ sc (j + 1) := hmono (by omega)
    push_cast
    linarith
  · rw [hgenPrefix j hj]
    have := hbound (sc j) (hsnn j) (hmono hj)
    rwa [chebyshevTwoPoleDefect] at this


/-! ### Parity: flipping one sign bounds that row

Flipping the sign of a single coefficient leaves the diagonal of the Gram form untouched and
reverses exactly the two off-diagonal strips through that index.  Since both the original and the
flipped Gram form are squares, the total coupling of any one index to all the others is at most
half the whole form.  No functional that is invariant under sign characters can see more than the
diagonal, and this is the exact amount of off-diagonal mass a single index can carry. -/

/-- Splitting a double sum off one index. -/
theorem gram_split_row (T : Finset ℕ) (G : ℕ → ℕ → ℝ) {m : ℕ} (hm : m ∈ T) :
    ∑ i ∈ T, ∑ j ∈ T, G i j
      = G m m + (∑ j ∈ T.erase m, G m j) + (∑ i ∈ T.erase m, G i m)
        + ∑ i ∈ T.erase m, ∑ j ∈ T.erase m, G i j := by
  calc ∑ i ∈ T, ∑ j ∈ T, G i j
      = (∑ j ∈ T, G m j) + ∑ i ∈ T.erase m, ∑ j ∈ T, G i j :=
        (Finset.add_sum_erase T (fun i => ∑ j ∈ T, G i j) hm).symm
    _ = (G m m + ∑ j ∈ T.erase m, G m j) + ∑ i ∈ T.erase m, ∑ j ∈ T, G i j := by
        rw [Finset.add_sum_erase T (fun j => G m j) hm]
    _ = (G m m + ∑ j ∈ T.erase m, G m j)
          + ∑ i ∈ T.erase m, (G i m + ∑ j ∈ T.erase m, G i j) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ =>
          (Finset.add_sum_erase T (fun j => G i j) hm).symm
    _ = G m m + (∑ j ∈ T.erase m, G m j) + (∑ i ∈ T.erase m, G i m)
          + ∑ i ∈ T.erase m, ∑ j ∈ T.erase m, G i j := by
        rw [Finset.sum_add_distrib]
        ring

/-- **One index carries at most half the Gram form.** -/
theorem gram_row_le_half (hF : Continuous F) (hFc : HasCompactSupport F) (T : Finset ℕ)
    (c t : ℕ → ℝ) {m : ℕ} (hm : m ∈ T) :
    (∑ j ∈ T.erase m, c m * c j * autoCorrelation F (t j - t m))
        + ∑ i ∈ T.erase m, c i * c m * autoCorrelation F (t m - t i)
      ≤ (∑ i ∈ T, ∑ j ∈ T, c i * c j * autoCorrelation F (t j - t i)) / 2 := by
  classical
  set d : ℕ → ℝ := fun k => (if k = m then (-1:ℝ) else 1) * c k with hd
  set G : ℕ → ℕ → ℝ := fun i j => c i * c j * autoCorrelation F (t j - t i) with hG
  set G' : ℕ → ℕ → ℝ := fun i j => d i * d j * autoCorrelation F (t j - t i) with hG'
  have hdm : d m = -c m := by
    rw [hd]
    simp
  have hdk : ∀ k : ℕ, k ≠ m → d k = c k := by
    intro k hk
    rw [hd]
    simp [hk]
  have hdiag : G' m m = G m m := by
    show d m * d m * autoCorrelation F (t m - t m)
      = c m * c m * autoCorrelation F (t m - t m)
    rw [hdm]
    ring
  have hrow : ∀ j ∈ T.erase m, G' m j = -G m j := by
    intro j hj
    show d m * d j * autoCorrelation F (t j - t m)
      = -(c m * c j * autoCorrelation F (t j - t m))
    rw [hdm, hdk j (Finset.mem_erase.mp hj).1]
    ring
  have hcol : ∀ i ∈ T.erase m, G' i m = -G i m := by
    intro i hi
    show d i * d m * autoCorrelation F (t m - t i)
      = -(c i * c m * autoCorrelation F (t m - t i))
    rw [hdm, hdk i (Finset.mem_erase.mp hi).1]
    ring
  have hrest : ∀ i ∈ T.erase m, ∀ j ∈ T.erase m, G' i j = G i j := by
    intro i hi j hj
    show d i * d j * autoCorrelation F (t j - t i)
      = c i * c j * autoCorrelation F (t j - t i)
    rw [hdk i (Finset.mem_erase.mp hi).1, hdk j (Finset.mem_erase.mp hj).1]
  have hsplitG := gram_split_row T G hm
  have hsplitG' := gram_split_row T G' hm
  rw [hdiag, Finset.sum_congr rfl hrow, Finset.sum_congr rfl hcol,
    Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (hrest i hi)),
    Finset.sum_neg_distrib, Finset.sum_neg_distrib] at hsplitG'
  have hnonneg : 0 ≤ ∑ i ∈ T, ∑ j ∈ T, G' i j := by
    have := sum_gram_nonneg hF hFc T d t
    exact this
  linarith [hsplitG, hsplitG', hnonneg]

/-- **A test sees no lag beyond its aperture, in any lag system.** -/
theorem sum_gen_lag_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 2 * r ≤ lam n) :
    ∑ n ∈ T, μ n * autoCorrelation F (lam n) = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [autoCorrelation_eq_zero hF hr hsupp (hlam n hn), mul_zero]

open scoped Classical in
/-- The reading of a lag system truncates to the lags inside the aperture. -/
theorem sum_gen_lag_eq_filter (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (T : Finset ℕ) (μ lam : ℕ → ℝ) :
    ∑ n ∈ T, μ n * autoCorrelation F (lam n)
      = ∑ n ∈ T.filter (fun n : ℕ => lam n < 2 * r), μ n * autoCorrelation F (lam n) := by
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_).symm
  have hge : 2 * r ≤ lam n := by
    by_contra hc
    exact hnot (Finset.mem_filter.mpr ⟨hn, lt_of_not_ge hc⟩)
  rw [autoCorrelation_eq_zero hF hr hsupp hge, mul_zero]


/-! ### Sampling at the midpoint halves the defect

Differencing a calibration at the integers forces the whole cell increment into the defect.
Sampling at the *midpoints* instead splits it: the resulting source's defect is bounded by the
larger of the two half-cell increments, which is about half the full one.  With the lower bound
from the matchability criterion this pins the optimal constant for an integer source up to the
half-cell/full-cell distinction. -/

/-- The source obtained by differencing a calibration at the cell midpoints. -/
def midpointSource (W : ℝ → ℝ) : ℕ → ℝ :=
  sourceOfPrefix fun n => if n = 0 then 0 else W (Real.log ((n : ℝ) + 1 / 2))

theorem lagPrefix_midpointSource (W : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    lagPrefix (midpointSource W) s = W (Real.log ((⌊Real.exp s⌋₊ : ℝ) + 1 / 2)) := by
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ ⌊Real.exp s⌋₊ := Nat.le_floor (by exact_mod_cast hexp1)
  rw [midpointSource, lagPrefix_sourceOfPrefix, if_pos rfl, if_neg (by omega), sub_zero]

/-- **The midpoint source's defect is at most the larger half-cell increment.** -/
theorem abs_defect_midpointSource_le {W : ℝ → ℝ} (hWmono : Monotone W) {K : ℝ}
    (hK1 : ∀ N : ℕ, 1 ≤ N →
      W (Real.log ((N : ℝ) + 1 / 2)) - W (Real.log (N : ℝ)) ≤ K)
    (hK2 : ∀ N : ℕ, 1 ≤ N →
      W (Real.log ((N : ℝ) + 1)) - W (Real.log ((N : ℝ) + 1 / 2)) ≤ K)
    {s : ℝ} (hs : 0 ≤ s) :
    |W s - lagPrefix (midpointSource W) s| ≤ K := by
  set N : ℕ := ⌊Real.exp s⌋₊ with hNdef
  have hexp1 : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexp1)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hNlt : Real.exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogN : Real.log (N : ℝ) ≤ s := by
    have := Real.log_le_log hN0 hNle
    rwa [Real.log_exp] at this
  have hlogN1 : s < Real.log ((N : ℝ) + 1) := by
    have := Real.log_lt_log (Real.exp_pos s) hNlt
    rwa [Real.log_exp] at this
  rw [lagPrefix_midpointSource W hs, ← hNdef]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hmono := hWmono hlogN
    linarith [hK1 N hN1]
  · have hmono := hWmono (le_of_lt hlogN1)
    linarith [hK2 N hN1]

/-! ### The structural calculus of lag systems

The prefix is additive in the weights, additive over a disjoint union of index sets, and
translating all lags translates the prefix in the scale.  Beyond the last lag a finite system's
prefix is frozen at its total mass, so its defect is the calibration itself: no finite system
calibrates an unbounded pole. -/

theorem genPrefix_shift (T : Finset ℕ) (μ lam : ℕ → ℝ) (τ s : ℝ) :
    genPrefix T μ (fun n => lam n + τ) s = genPrefix T μ lam (s - τ) := by
  rw [genPrefix, genPrefix]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : lam n ≤ s - τ
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by intro h; exact hc (by linarith)), if_neg hc]

theorem genPrefix_union {T₁ T₂ : Finset ℕ} (hdisj : Disjoint T₁ T₂) (μ lam : ℕ → ℝ) (s : ℝ) :
    genPrefix (T₁ ∪ T₂) μ lam s = genPrefix T₁ μ lam s + genPrefix T₂ μ lam s := by
  rw [genPrefix, genPrefix, genPrefix, Finset.sum_union hdisj]

theorem genPrefix_add (T : Finset ℕ) (μ₁ μ₂ lam : ℕ → ℝ) (s : ℝ) :
    genPrefix T (fun n => μ₁ n + μ₂ n) lam s
      = genPrefix T μ₁ lam s + genPrefix T μ₂ lam s := by
  rw [genPrefix, genPrefix, genPrefix, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem genPrefix_smul (T : Finset ℕ) (μ lam : ℕ → ℝ) (c s : ℝ) :
    genPrefix T (fun n => c * μ n) lam s = c * genPrefix T μ lam s := by
  rw [genPrefix, genPrefix, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Beyond its last lag a finite system's prefix is frozen.** -/
theorem genPrefix_eq_total (T : Finset ℕ) (μ lam : ℕ → ℝ) {s : ℝ}
    (hs : ∀ n ∈ T, lam n ≤ s) : genPrefix T μ lam s = ∑ n ∈ T, μ n := by
  rw [genPrefix]
  exact Finset.sum_congr rfl fun n hn => by rw [if_pos (hs n hn), mul_one]

theorem defect_beyond_horizon (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ) {s : ℝ}
    (hs : ∀ n ∈ T, lam n ≤ s) :
    W s - genPrefix T μ lam s = W s - ∑ n ∈ T, μ n := by
  rw [genPrefix_eq_total T μ lam hs]


/-! ### Any lag family realises its calibration up to its largest gap increment

Weighting each lag by the calibration's increment since the previous lag makes the prefix
telescope, so between two consecutive lags the defect is exactly the calibration's rise since the
last lag — at most the increment across that gap.  Together with the gap criterion this settles
the question completely: the best defect a lag family can achieve is, up to a factor two, the
largest increment of the calibration across its gaps.  For the pole at `1` that increment is
`e^{λ_{k+1}} − e^{λ_k}`, so the *generalised integers* must have bounded gaps — exactly the
property the ordinary integers have. -/

/-- The weights that make a lag family's prefix telescope to the calibration. -/
def gapSource (W : ℝ → ℝ) (lam : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then 0 else W (lam n) - W (lam (n - 1))

theorem sum_gapSource (W : ℝ → ℝ) (lam : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1), gapSource W lam n = W (lam K) - W (lam 0) := by
  induction K with
  | zero => simp [gapSource]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, gapSource, if_neg (by omega)]
      simp only [Nat.add_sub_cancel]
      ring

theorem genPrefix_gapSource (W : ℝ → ℝ) {lam : ℕ → ℝ} (hmono : Monotone lam) {M K : ℕ}
    (hKM : K < M) {s : ℝ} (h1 : lam K ≤ s) (h2 : s < lam (K + 1)) :
    genPrefix (Finset.range M) (gapSource W lam) lam s = W (lam K) - W (lam 0) := by
  have hsub : Finset.range (K + 1) ⊆ Finset.range M := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hout : ∀ x ∈ Finset.range M, x ∉ Finset.range (K + 1) →
      gapSource W lam x * (if lam x ≤ s then (1:ℝ) else 0) = 0 := by
    intro x _ hnot
    rw [Finset.mem_range] at hnot
    have hxK : K + 1 ≤ x := by omega
    have hlam : lam (K + 1) ≤ lam x := hmono hxK
    rw [if_neg (by linarith), mul_zero]
  rw [genPrefix, ← Finset.sum_subset hsub hout]
  have hin : ∀ x ∈ Finset.range (K + 1),
      gapSource W lam x * (if lam x ≤ s then (1:ℝ) else 0) = gapSource W lam x := by
    intro x hx
    rw [Finset.mem_range] at hx
    have hlam : lam x ≤ lam K := hmono (by omega)
    rw [if_pos (by linarith), mul_one]
  rw [Finset.sum_congr rfl hin, sum_gapSource]

/-- **Between two consecutive lags the defect is the calibration's rise since the last one.** -/
theorem abs_defect_gapSource_le {W : ℝ → ℝ} (hWmono : Monotone W) {lam : ℕ → ℝ}
    (hmono : Monotone lam) {M K : ℕ} (hKM : K < M) {s : ℝ}
    (h1 : lam K ≤ s) (h2 : s < lam (K + 1)) :
    |W s - genPrefix (Finset.range M) (gapSource W lam) lam s - W (lam 0)|
      ≤ W (lam (K + 1)) - W (lam K) := by
  rw [genPrefix_gapSource W hmono hKM h1 h2]
  have hlow := hWmono h1
  have hup := hWmono (le_of_lt h2)
  rw [abs_le]
  constructor <;> linarith

/-- For the pole at `1` the gap increment is the gap between the generalised integers. -/
theorem twoPoleWeight_gap_increment (lam : ℕ → ℝ) (k : ℕ) :
    twoPoleWeight (lam (k + 1)) - twoPoleWeight (lam k)
      = (Real.exp (lam (k + 1)) - Real.exp (lam k)) + (lam (k + 1) - lam k) := by
  rw [twoPoleWeight, twoPoleWeight]
  ring


/-! ### The Weil form of an arbitrary lag system

Reading a lag system through the test's own lag weight gives the balance in Weil's shape: the
atoms at the lags `λ_n` against the pole plane, with the system's defect as the residue.  The
pole plane is the same rank-one readout of the test as for `ζ`, because it depends only on the
calibration.  This is the explicit formula a Beurling system satisfies, in its own lags. -/

/-- **The Weil-shaped balance for an arbitrary lag system.** -/
theorem genTestBalance (T : Finset ℕ) (μ lam : ℕ → ℝ) (hlam : ∀ n ∈ T, 0 < lam n)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) :
    (∑ n ∈ T, μ n * (2 * Real.exp (-(lam n) / 2) * autoCorrelation F (lam n)))
        - 2 * ((∫ x, F x * Real.exp (-(1 / 2 * x))) * ∫ x, F x * Real.exp (1 / 2 * x))
      = ∫ s in Ioi (0:ℝ), (twoPoleWeight s - genPrefix T μ lam s) *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_gen_sub_calibration_eq_defect T μ lam hlam twoPoleWeight_zero
    continuous_twoPoleWeight (by fun_prop) hasDerivAt_twoPoleWeight
    (contDiff_one_lagTestWeight hF hFc) hS hvan
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeight hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), (twoPoleWeight s - genPrefix T μ lam s)
            * deriv (lagTestWeight F) s
          = (twoPoleWeight s - genPrefix T μ lam s)
            * (2 * Real.exp (-s / 2)
                * (crossCorrelation F s - autoCorrelation F s / 2)))] at hkey
  rw [← hkey]
  congr 1
  have hpolar := integral_Ioi_cosh_mul_autoCorrelation hF hFc hr hsupp (1 / 2)
  have hrw : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * lagTestWeight F s)
      = ∫ s in Ioi (0:ℝ), 4 * (Real.cosh (1 / 2 * s) * autoCorrelation F s) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [lagTestWeight, Real.cosh_eq]
    have h1 : Real.exp (1 / 2 * s) = Real.exp s * Real.exp (-s / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-(1 / 2 * s)) = Real.exp (-s / 2) := by
      congr 1
      ring
    rw [h1, h2]
    ring
  rw [hrw, MeasureTheory.integral_const_mul, hpolar]
  ring

/-! ### The field of an arbitrary lag system

The linear reading of a lag system is the test paired with the superposition of its translates,
exactly as for the primes.  Every bound that the field apparatus gives for the prime field
therefore applies to any lag system. -/

/-- The field of a lag system: the superposition of translates at its lags. -/
def lagField (F : ℝ → ℝ) (μ lam : ℕ → ℝ) (T : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ T, μ n * F (x + lam n)

theorem sum_gen_lag_eq_integral_field (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (μ lam : ℕ → ℝ) :
    ∑ n ∈ T, μ n * autoCorrelation F (lam n) = ∫ x, F x * lagField F μ lam T x := by
  have hexp : ∀ x : ℝ, (∑ n ∈ T, μ n * (F x * F (x + lam n))) = F x * lagField F μ lam T x := by
    intro x
    rw [lagField, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hint : ∀ n ∈ T, Integrable fun x => μ n * (F x * F (x + lam n)) := fun n _ =>
    ((hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right).const_mul (μ n)
  rw [← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_finsetSum T hint]
  exact Finset.sum_congr rfl fun n _ => by
    rw [MeasureTheory.integral_const_mul, autoCorrelation]


/-! ### Reading a lag system's defect, and recovering its atoms

On the tail of a bump the general balance returns `−∫(W − prefix)φ`, so the defect of any lag
system is a ledger reading.  And a prefix difference across an isolated lag returns exactly the
mass sitting there: the atoms of a lag system are recoverable from its prefix, which is rigidity
for Beurling systems.  Finally the Weil-shaped prime side is, as for the primes, the test paired
with the system's own field. -/

theorem sum_gen_sub_calibration_tailWeight (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 0 < lam n) {W w : ℝ → ℝ} (hW0 : W 0 = 0) (hWc : Continuous W)
    (hwc : Continuous w) (hWd : ∀ s, HasDerivAt W (w s) s) (hφ : Continuous φ) (hS : 0 < S)
    (hφ0 : ∀ t, S ≤ t → φ t = 0) :
    (∑ n ∈ T, μ n * tailWeight φ S (lam n))
        - ∫ s in Ioi (0:ℝ), w s * tailWeight φ S s
      = -∫ s in Ioi (0:ℝ), (W s - genPrefix T μ lam s) * φ s := by
  have hkey := sum_gen_sub_calibration_eq_defect T μ lam hlam hW0 hWc hwc hWd
    (contDiff_one_tailWeight hφ S) hS (fun s hs => tailWeight_eq_zero hφ0 hs)
  rw [hkey, setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [(hasDerivAt_tailWeight hφ S s).deriv]; ring :
        ∀ s ∈ Ioi (0:ℝ), (W s - genPrefix T μ lam s) * deriv (tailWeight φ S) s
          = -((W s - genPrefix T μ lam s) * φ s)),
    MeasureTheory.integral_neg]

open scoped Classical in
/-- **The atoms of a lag system are prefix jumps.** -/
theorem genPrefix_jump (T : Finset ℕ) (μ lam : ℕ → ℝ) {u ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n ∈ T, lam n ≤ u - ε ∨ u ≤ lam n) :
    genPrefix T μ lam u - genPrefix T μ lam (u - ε)
      = ∑ n ∈ T.filter (fun n : ℕ => lam n = u), μ n := by
  rw [genPrefix, genPrefix, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rcases hsep n hn with hlow | hhigh
  · rw [if_pos (by linarith), if_pos hlow, if_neg (by intro hc; linarith)]
    ring
  · rcases eq_or_lt_of_le hhigh with heq | hlt
    · rw [if_pos (le_of_eq heq.symm), if_neg (by linarith), if_pos heq.symm]
      ring
    · rw [if_neg (by linarith), if_neg (by linarith), if_neg (by intro hc; linarith)]
      ring

/-- **The Weil-shaped prime side of a lag system is the test against its own field.** -/
theorem sum_gen_weil_eq_integral_field (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (μ lam : ℕ → ℝ) :
    ∑ n ∈ T, μ n * (2 * Real.exp (-(lam n) / 2) * autoCorrelation F (lam n))
      = 2 * ∫ x, F x * lagField F (fun n => μ n * Real.exp (-(lam n) / 2)) lam T x := by
  have hbase := sum_gen_lag_eq_integral_field hF hFc T
    (fun n => μ n * Real.exp (-(lam n) / 2)) lam
  rw [← hbase, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring


/-! ### The whole field apparatus, for an arbitrary lag system

The Gram form of a lag system is the energy of its field, its cross-aggregate is bounded below by
minus the diagonal, and the linear reading is controlled by the field energy at a free parameter.
And the Weil-shaped balance holds at *any* pole, with the normalisation `e^{−ρλ/2}` and the pole
plane `2(∫Fe^{−ρx/2})(∫Fe^{ρx/2})`.  This is the explicit-formula machinery of the theory in its
most general form. -/

theorem integral_lagField_sq_eq (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (μ lam : ℕ → ℝ) :
    ∑ m ∈ T, ∑ n ∈ T, μ m * μ n * autoCorrelation F (lam n - lam m)
      = ∫ x, lagField F μ lam T x ^ 2 :=
  sum_gram_eq_integral_sq hF hFc T μ lam

theorem gen_crossAggregate_ge (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (μ lam : ℕ → ℝ) :
    -(autoCorrelation F 0 * ∑ n ∈ T, μ n ^ 2)
      ≤ ∑ m ∈ T, ∑ n ∈ T.erase m, μ m * μ n * autoCorrelation F (lam n - lam m) :=
  sum_gram_offDiag_ge hF hFc T μ lam

theorem two_mul_sum_gen_lag_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (T : Finset ℕ) (μ lam : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * ∑ n ∈ T, μ n * autoCorrelation F (lam n)
      ≤ t * autoCorrelation F 0 + t⁻¹ * ∫ x, lagField F μ lam T x ^ 2 := by
  have hid := sum_gen_lag_eq_integral_field hF hFc T μ lam
  have hsq : Integrable fun x => lagField F μ lam T x ^ 2 := by
    have hexp : ∀ x : ℝ, (∑ m ∈ T, ∑ n ∈ T, μ m * μ n * (F (x + lam m) * F (x + lam n)))
        = lagField F μ lam T x ^ 2 := by
      intro x
      rw [lagField, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
    exact (MeasureTheory.integrable_finsetSum T fun m _ =>
      MeasureTheory.integrable_finsetSum T fun n _ =>
        (integrable_shift_mul hF hFc (lam m) (lam n)).const_mul (μ m * μ n)).congr
      (Filter.Eventually.of_forall hexp)
  have hmul : Integrable fun x => F x * lagField F μ lam T x := by
    have hexp : ∀ x : ℝ, (∑ n ∈ T, μ n * (F x * F (x + lam n)))
        = F x * lagField F μ lam T x := by
      intro x
      rw [lagField, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    exact (MeasureTheory.integrable_finsetSum T fun n _ =>
      ((hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hFc.mul_right).const_mul (μ n)).congr (Filter.Eventually.of_forall hexp)
  have hpt : ∀ x : ℝ, 2 * (F x * lagField F μ lam T x)
      ≤ t * F x ^ 2 + t⁻¹ * lagField F μ lam T x ^ 2 := by
    intro x
    have key : t * (F x - lagField F μ lam T x / t) ^ 2
        = t * F x ^ 2 - 2 * (F x * lagField F μ lam T x)
          + t⁻¹ * lagField F μ lam T x ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg ht.le (sq_nonneg (F x - lagField F μ lam T x / t)), key]
  have hrsum : Integrable fun x => t * F x ^ 2 + t⁻¹ * lagField F μ lam T x ^ 2 :=
    ((integrable_sq hF hFc).const_mul t).add (hsq.const_mul t⁻¹)
  have hmono := MeasureTheory.integral_mono (hmul.const_mul 2) hrsum hpt
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add ((integrable_sq hF hFc).const_mul t) (hsq.const_mul t⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    ← autoCorrelation_zero_eq, ← hid] at hmono
  exact hmono

/-- **The Weil-shaped balance of a lag system at an arbitrary pole.** -/
theorem genTestBalanceAt (ρ : ℝ) (hρ : ρ ≠ 0) (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 0 < lam n) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) :
    (∑ n ∈ T, μ n * (2 * Real.exp (-(ρ * lam n) / 2) * autoCorrelation F (lam n)))
        - 2 * ((∫ x, F x * Real.exp (-(ρ / 2 * x))) * ∫ x, F x * Real.exp (ρ / 2 * x))
      = ∫ s in Ioi (0:ℝ), (poleWeightAt ρ s - genPrefix T μ lam s) *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeightAt ρ F s = 0 := fun s hs => by
    rw [lagTestWeightAt, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_gen_sub_calibration_eq_defect T μ lam hlam (poleWeightAt_zero ρ)
    (continuous_poleWeightAt ρ) (by fun_prop) (hasDerivAt_poleWeightAt hρ)
    (contDiff_one_lagTestWeightAt ρ hF hFc) hS hvan
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeightAt ρ hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), (poleWeightAt ρ s - genPrefix T μ lam s)
            * deriv (lagTestWeightAt ρ F) s
          = (poleWeightAt ρ s - genPrefix T μ lam s)
            * (2 * Real.exp (-(ρ * s) / 2)
                * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)))] at hkey
  rw [← hkey]
  congr 1
  have hpolar := integral_Ioi_cosh_mul_autoCorrelation hF hFc hr hsupp (ρ / 2)
  have hrw : (∫ s in Ioi (0:ℝ), (Real.exp (ρ * s) + 1) * lagTestWeightAt ρ F s)
      = ∫ s in Ioi (0:ℝ), 4 * (Real.cosh (ρ / 2 * s) * autoCorrelation F s) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [lagTestWeightAt, Real.cosh_eq]
    have h1 : Real.exp (ρ / 2 * s) = Real.exp (ρ * s) * Real.exp (-(ρ * s) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-(ρ / 2 * s)) = Real.exp (-(ρ * s) / 2) := by
      congr 1
      ring
    rw [h1, h2]
    ring
  rw [hrw, MeasureTheory.integral_const_mul, hpolar]
  ring


/-! ### The Weil form of a source is its receiver against the test's curvature

Pairing the second-order dictionary with the test's own lag weight puts the Weil-shaped balance
of *any* source in receiver form: the prime side minus the pole plane is minus the source's
critical-scale functional tested on the curvature of the lag weight.  For `ζ` this is the
critical-scale receiver; for any source it is that source's own. -/

theorem testBalance_receiver (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F)) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = -∫ s in Ioi (0:ℝ), sourceScalePrefix a s * deriv (deriv (lagTestWeight F)) s := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_weight_sub_polar_eq_sourceScalePrefix a ha0 ha1
    (contDiff_one_lagTestWeight hF hFc) (contDiff_one_deriv_lagTestWeight hF hF' hFc) hS hvan hN
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp [ha0]
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lagTestWeight, exp_neg_half_log hn]
  · have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
    have hAcs : HasCompactSupport (autoCorrelation F) :=
      hasCompactSupport_autoCorrelation hF.continuous hr hsupp
    have hg : Integrable fun s => Real.cosh (s / 2) * autoCorrelation F s :=
      (((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hAc)
        ).integrable_of_hasCompactSupport hAcs.mul_left
    have heven : ∀ s : ℝ, Real.cosh (-s / 2) * autoCorrelation F (-s)
        = Real.cosh (s / 2) * autoCorrelation F s := by
      intro s
      rw [autoCorrelation_neg, show -s / 2 = -(s / 2) by ring, Real.cosh_neg]
    have hhalf := integral_eq_two_mul_Ioi hg heven
    have hpolar := integral_cosh_mul_autoCorrelation hF.continuous hFc hsupp
    have hre : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * lagTestWeight F s)
        = 4 * ∫ s in Ioi (0:ℝ), Real.cosh (s / 2) * autoCorrelation F s := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [lagTestWeight, Real.cosh_eq]
      have h1 : Real.exp (s / 2) = Real.exp s * Real.exp (-s / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (-(s / 2)) = Real.exp (-s / 2) := by
        congr 1
        ring
      rw [h1, h2]
      ring
    rw [hre, ← hpolar, hhalf]
    ring

/-- **The odd receiver balance.**  On an odd test the pole plane is minus a square, so the prime
side and the pole charge are both costs. -/
theorem testBalance_receiver_odd (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F)) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        + 2 * expMomentNeg F ^ 2
      = -∫ s in Ioi (0:ℝ), sourceScalePrefix a s * deriv (deriv (lagTestWeight F)) s := by
  have hb := testBalance_receiver a ha0 ha1 hF hF' hFc hr hsupp hN
  rw [poleplane_odd hF.continuous hFc hodd] at hb
  rw [← hb]
  ring

/-- **The odd balance of a lag system at an arbitrary pole.** -/
theorem genTestBalanceAt_odd (ρ : ℝ) (hρ : ρ ≠ 0) (T : Finset ℕ) (μ lam : ℕ → ℝ)
    (hlam : ∀ n ∈ T, 0 < lam n) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) :
    (∑ n ∈ T, μ n * (2 * Real.exp (-(ρ * lam n) / 2) * autoCorrelation F (lam n)))
        + 2 * (∫ x, F x * Real.exp (ρ / 2 * x)) ^ 2
      = ∫ s in Ioi (0:ℝ), (poleWeightAt ρ s - genPrefix T μ lam s) *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)) := by
  have hb := genTestBalanceAt ρ hρ T μ lam hlam hF hFc hr hsupp
  rw [expMoment_odd F hodd (ρ / 2)] at hb
  rw [← hb]
  ring


/-! ### The Weil form of an arbitrary integer source

The first-order balance against the test's own lag weight holds for every source, with the same
rank-one pole plane: what changes from source to source is only its defect.  Instantiating gives
the Weil form of the prime-only source and, with the reflected-pole calibration, of the Möbius
source. -/

/-- **The Weil-shaped balance for an arbitrary source.** -/
theorem testBalance_source (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect a s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_weight_sub_polar_eq_defect a ha0 ha1
    (contDiff_one_lagTestWeight hF hFc) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeight hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), lagSourceDefect a s * deriv (lagTestWeight F) s
          = lagSourceDefect a s *
              (2 * Real.exp (-s / 2)
                * (crossCorrelation F s - autoCorrelation F s / 2)))] at hkey
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp [ha0]
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lagTestWeight, exp_neg_half_log hn]
  · have hAc : Continuous (autoCorrelation F) := (contDiff_one_autoCorrelation hF hFc).continuous
    have hAcs : HasCompactSupport (autoCorrelation F) :=
      hasCompactSupport_autoCorrelation hF.continuous hr hsupp
    have hg : Integrable fun s => Real.cosh (s / 2) * autoCorrelation F s :=
      (((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hAc)
        ).integrable_of_hasCompactSupport hAcs.mul_left
    have heven : ∀ s : ℝ, Real.cosh (-s / 2) * autoCorrelation F (-s)
        = Real.cosh (s / 2) * autoCorrelation F s := by
      intro s
      rw [autoCorrelation_neg, show -s / 2 = -(s / 2) by ring, Real.cosh_neg]
    have hhalf := integral_eq_two_mul_Ioi hg heven
    have hpolar := integral_cosh_mul_autoCorrelation hF.continuous hFc hsupp
    have hre : (∫ s in Ioi (0:ℝ), (Real.exp s + 1) * lagTestWeight F s)
        = 4 * ∫ s in Ioi (0:ℝ), Real.cosh (s / 2) * autoCorrelation F s := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [lagTestWeight, Real.cosh_eq]
      have h1 : Real.exp (s / 2) = Real.exp s * Real.exp (-s / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (-(s / 2)) = Real.exp (-s / 2) := by
        congr 1
        ring
      rw [h1, h2]
      ring
    rw [hre, ← hpolar, hhalf]
    ring

/-- **The Weil form of the prime-only source.** -/
theorem testBalance_theta (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        thetaSource n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect thetaSource s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) :=
  testBalance_source thetaSource thetaSource_zero thetaSource_one hF hFc hr hsupp hN

/-- **The Weil form of the Möbius source**, against the reflected pole alone. -/
theorem mertensTestBalance (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        moebiusSource n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - ∫ s in Ioi (0:ℝ), 2 * Real.exp (-s / 2) * autoCorrelation F s
      = ∫ s in Ioi (0:ℝ), (s - lagMertens s) *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_moebius_sub_unit_eq_defect (contDiff_one_lagTestWeight hF hFc) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeight hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), (s - lagMertens s) * deriv (lagTestWeight F) s
          = (s - lagMertens s) *
              (2 * Real.exp (-s / 2)
                * (crossCorrelation F s - autoCorrelation F s / 2)))] at hkey
  rw [← hkey]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h0 : n = 0
  · subst h0; simp [moebiusSource_zero]
  · have hn : (0:ℝ) < n := by
      have : 0 < n := Nat.pos_of_ne_zero h0
      exact_mod_cast this
    rw [lagTestWeight, exp_neg_half_log hn]


/-! ### Comparing sources at Weil level, and scoring a source by its defect

Subtracting two Weil-shaped balances cancels the pole plane entirely: two sources are compared by
the pairing of their prefix difference with the test weight, with no archimedean term at all.
And a source whose defect is majorised by `G` has its whole Weil form within `∫G|w|` of the pole
plane — so the ideal source is within `(1+log 2)∫|w|`, and pure integer density within
`∫(s+1)|w|`. -/

/-- **Comparing two sources at Weil level: the pole plane cancels.** -/
theorem testBalance_source_sub (a b : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - ∑ n ∈ Finset.range (N + 1),
            b n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n))
      = (∫ s in Ioi (0:ℝ), lagSourceDefect a s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)))
        - ∫ s in Ioi (0:ℝ), lagSourceDefect b s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have ha := testBalance_source a ha0 ha1 hF hFc hr hsupp hN
  have hb := testBalance_source b hb0 hb1 hF hFc hr hsupp hN
  linarith

/-- **Scoring a source by a majorant of its defect.** -/
theorem abs_testBalance_source_le (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {G : ℝ → ℝ} (hGc : Continuous G)
    (hdef : ∀ s, 0 < s → |lagSourceDefect a s| ≤ G s)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1),
          a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)|
      ≤ ∫ s in Ioi (0:ℝ), G s * |deriv (lagTestWeight F) s| := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hwc : Continuous (deriv (lagTestWeight F)) :=
    (contDiff_one_lagTestWeight hF hFc).continuous_deriv le_rfl
  have hintG : IntegrableOn (fun s => G s * |deriv (lagTestWeight F) s|) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hGc.mul hwc.abs) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, abs_zero, mul_zero])
  have hintD : IntegrableOn (fun s => |lagSourceDefect a s * deriv (lagTestWeight F) s|)
      (Ioi (0:ℝ)) := (integrableOn_Ioi_lagSourceDefect_mul_deriv a
        (contDiff_one_lagTestWeight hF hFc) hS hvan hN).abs
  have hpt : ∀ s ∈ Ioi (0:ℝ),
      |lagSourceDefect a s * deriv (lagTestWeight F) s|
        ≤ G s * |deriv (lagTestWeight F) s| := by
    intro s hs
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hdef s hs) (abs_nonneg _)
  have hmono := MeasureTheory.setIntegral_mono_on hintD hintG measurableSet_Ioi hpt
  rw [testBalance_source a ha0 ha1 hF hFc hr hsupp hN,
    setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeight hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), lagSourceDefect a s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))
          = lagSourceDefect a s * deriv (lagTestWeight F) s)]
  exact le_trans abs_integral_le_integral_abs hmono

/-- The ideal source's Weil form is within `(1 + log 2)∫|w|` of the pole plane. -/
theorem abs_testBalance_idealSource_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1),
          idealSource n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)|
      ≤ ∫ s in Ioi (0:ℝ), (1 + Real.log 2) * |deriv (lagTestWeight F) s| :=
  abs_testBalance_source_le idealSource idealSource_zero idealSource_one continuous_const
    (fun _ hs => abs_lagSourceDefect_idealSource_le (le_of_lt hs)) hF hFc hr hsupp hN


/-! ### The quiet zone is universal

Below `log 2` no source has switched on, so *every* source's defect is the calibration itself and
every source has the same ledger there.  On the next cell the only arithmetic visible is the
single weight `a(2)`.  And at aperture `r` the Weil form of any source involves only its weights
below `e^{2r}`: the ledger is local in the index as well as in the scale. -/

theorem lagSourceDefect_eq_twoPoleWeight_of_lt_log_two (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha1 : a 1 = 0) {s : ℝ} (hs : s < Real.log 2) :
    lagSourceDefect a s = twoPoleWeight s := by
  have hlt : Real.exp s < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hfl : ⌊Real.exp s⌋₊ ≤ 1 := by
    rcases le_or_gt (Real.exp s) 0 with h0 | h0
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h0 one_pos)]
    · exact Nat.lt_succ_iff.mp ((Nat.floor_lt h0.le).mpr (by norm_num; linarith))
  have hz : lagPrefix a s = 0 := by
    rw [lagPrefix]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : k ≤ 1 := le_trans hk.2 hfl
    interval_cases k
    · exact ha0
    · exact ha1
  rw [lagSourceDefect, hz, sub_zero]

/-- On the second cell the only arithmetic visible is the single weight `a(2)`. -/
theorem lagSourceDefect_second_cell (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    {s : ℝ} (h1 : Real.log 2 ≤ s) (h2 : s < Real.log 3) :
    lagSourceDefect a s = twoPoleWeight s - a 2 := by
  have hge : (2:ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hlt : Real.exp s < 3 := by
    have := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
  have hfl : ⌊Real.exp s⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by positivity)]
    exact ⟨by exact_mod_cast hge, by exact_mod_cast hlt⟩
  have hIcc : Finset.Icc 0 2 = Finset.range 3 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  have hpref : lagPrefix a s = a 2 := by
    rw [lagPrefix, hfl, hIcc]
    simp [Finset.sum_range_succ, ha0, ha1]
  rw [lagSourceDefect, hpref]

/-- **The Weil form of a source involves only its weights below `e^{2r}`.** -/
theorem testBalance_source_truncates (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N)
    (hM : Real.exp (2 * r) ≤ M) :
    (∑ n ∈ Finset.range (N + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = ∑ n ∈ Finset.range (M + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
  have hbase := sum_lag_eq_of_horizon hF hr hsupp
    (fun n => a n * (2 * (Real.sqrt n)⁻¹)) hMN hM
  have hL : ∀ K : ℕ, ∑ n ∈ Finset.range (K + 1),
      (fun n : ℕ => a n * (2 * (Real.sqrt n)⁻¹)) n * autoCorrelation F (Real.log n)
      = ∑ n ∈ Finset.range (K + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
    intro K
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [← hL N, ← hL M]
  exact hbase


/-! ### Polarisation: the Weil form is quadratic in the test

The prime side polarises through the pair correlation, and the two half-exponential moments are
linear in the test, so the pole plane polarises as `M₋(F)M₊(G) + M₋(G)M₊(F)`.  In particular the
pole-free locus is a genuine linear subspace of the test space, not merely a set. -/

theorem primeSide_add (hF : Continuous F) (hFc : HasCompactSupport F) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation (fun x => F x + G x) (Real.log n)))
      = (∑ n ∈ Finset.range (N + 1),
            a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        + (∑ n ∈ Finset.range (N + 1),
            a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation G (Real.log n)))
        + ∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ *
            (pairCorrelation F G (Real.log n) + pairCorrelation G F (Real.log n))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autoCorrelation_add hF hFc hG hGc]
  ring

theorem expMomentNeg_add (hF : Continuous F) (hFc : HasCompactSupport F) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    expMomentNeg (fun x => F x + G x) = expMomentNeg F + expMomentNeg G := by
  have hiF : Integrable fun x => F x * Real.exp (-x / 2) :=
    (hF.mul (Real.continuous_exp.comp
      (continuous_neg.div_const 2))).integrable_of_hasCompactSupport hFc.mul_right
  have hiG : Integrable fun x => G x * Real.exp (-x / 2) :=
    (hG.mul (Real.continuous_exp.comp
      (continuous_neg.div_const 2))).integrable_of_hasCompactSupport hGc.mul_right
  rw [expMomentNeg, expMomentNeg, expMomentNeg, ← MeasureTheory.integral_add hiF hiG]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (F x + G x) * Real.exp (-x / 2)
    = F x * Real.exp (-x / 2) + G x * Real.exp (-x / 2)
  ring

theorem expMomentPos_add (hF : Continuous F) (hFc : HasCompactSupport F) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    expMomentPos (fun x => F x + G x) = expMomentPos F + expMomentPos G := by
  have hiF : Integrable fun x => F x * Real.exp (x / 2) :=
    (hF.mul (Real.continuous_exp.comp
      (continuous_id.div_const 2))).integrable_of_hasCompactSupport hFc.mul_right
  have hiG : Integrable fun x => G x * Real.exp (x / 2) :=
    (hG.mul (Real.continuous_exp.comp
      (continuous_id.div_const 2))).integrable_of_hasCompactSupport hGc.mul_right
  rw [expMomentPos, expMomentPos, expMomentPos, ← MeasureTheory.integral_add hiF hiG]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (F x + G x) * Real.exp (x / 2)
    = F x * Real.exp (x / 2) + G x * Real.exp (x / 2)
  ring

/-- **The pole plane polarises.** -/
theorem poleplane_add (hF : Continuous F) (hFc : HasCompactSupport F) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    expMomentNeg (fun x => F x + G x) * expMomentPos (fun x => F x + G x)
      = expMomentNeg F * expMomentPos F + expMomentNeg G * expMomentPos G
        + (expMomentNeg F * expMomentPos G + expMomentNeg G * expMomentPos F) := by
  rw [expMomentNeg_add hF hFc hG hGc, expMomentPos_add hF hFc hG hGc]
  ring

/-- **The pole-free locus is a linear subspace of the test space.** -/
theorem expMomentNeg_eq_zero_add (hF : Continuous F) (hFc : HasCompactSupport F)
    {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (hFz : expMomentNeg F = 0) (hGz : expMomentNeg G = 0) :
    expMomentNeg (fun x => F x + G x) = 0 := by
  rw [expMomentNeg_add hF hFc hG hGc, hFz, hGz, add_zero]

theorem expMomentNeg_smul (F : ℝ → ℝ) (c : ℝ) :
    expMomentNeg (fun x => c * F x) = c * expMomentNeg F := by
  rw [expMomentNeg, expMomentNeg, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show c * F x * Real.exp (-x / 2) = c * (F x * Real.exp (-x / 2))
  ring


/-! ### The symmetries of the Weil form

The form is homogeneous of degree two in the test.  Translating the test leaves the correlation
untouched and scales the two half-exponential moments by reciprocal factors, so the pole plane —
and hence the whole Weil form — depends only on the translation class of the test.  Dilating the
test by `λ` turns it into the reading of the `λ`-power Beurling system at its own pole `1/λ`,
with the standard normalisation `n^{−1/2}` restored exactly. -/

theorem autoCorrelation_smul (F : ℝ → ℝ) (c t : ℝ) :
    autoCorrelation (fun x => c * F x) t = c ^ 2 * autoCorrelation F t := by
  rw [autoCorrelation, autoCorrelation, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show c * F x * (c * F (x + t)) = c ^ 2 * (F x * F (x + t))
  ring

theorem expMomentNeg_translate (F : ℝ → ℝ) (c : ℝ) :
    expMomentNeg (fun x => F (x + c)) = Real.exp (c / 2) * expMomentNeg F := by
  rw [expMomentNeg, expMomentNeg, ← MeasureTheory.integral_const_mul]
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun y => Real.exp (c / 2) * (F y * Real.exp (-y / 2))) c
  rw [← hshift]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + c) * Real.exp (-x / 2)
    = Real.exp (c / 2) * (F (x + c) * Real.exp (-(x + c) / 2))
  rw [show -(x + c) / 2 = -x / 2 + -(c / 2) by ring, Real.exp_add, Real.exp_neg]
  field_simp

theorem expMomentPos_translate (F : ℝ → ℝ) (c : ℝ) :
    expMomentPos (fun x => F (x + c)) = Real.exp (-(c / 2)) * expMomentPos F := by
  rw [expMomentPos, expMomentPos, ← MeasureTheory.integral_const_mul]
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun y => Real.exp (-(c / 2)) * (F y * Real.exp (y / 2))) c
  rw [← hshift]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + c) * Real.exp (x / 2)
    = Real.exp (-(c / 2)) * (F (x + c) * Real.exp ((x + c) / 2))
  rw [show (x + c) / 2 = x / 2 + c / 2 by ring, Real.exp_add, Real.exp_neg]
  field_simp

/-- **The pole plane is translation-invariant.** -/
theorem poleplane_translate (F : ℝ → ℝ) (c : ℝ) :
    expMomentNeg (fun x => F (x + c)) * expMomentPos (fun x => F (x + c))
      = expMomentNeg F * expMomentPos F := by
  rw [expMomentNeg_translate, expMomentPos_translate, Real.exp_neg]
  field_simp

/-- **Dilating the test is reading the `λ`-power system at the pole `1/λ`.** -/
theorem weil_dilation_covariance {lam : ℝ} (hlam : 0 < lam) (F : ℝ → ℝ) (T : Finset ℕ)
    (μ : ℕ → ℝ) (h1 : ∀ n ∈ T, 1 ≤ n) :
    (∑ n ∈ T, μ n * (2 * Real.exp (-(1 / lam * (lam * Real.log (n : ℝ))) / 2)
        * autoCorrelation F (lam * Real.log (n : ℝ))))
      = lam * ∑ n ∈ T, μ n * (2 * (Real.sqrt n)⁻¹
          * autoCorrelation (fun x => F (lam * x)) (Real.log (n : ℝ))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0:ℝ) < n := by
    have : 0 < n := h1 n hn
    exact_mod_cast this
  have hexp : Real.exp (-(1 / lam * (lam * Real.log (n : ℝ))) / 2) = (Real.sqrt n)⁻¹ := by
    rw [show -(1 / lam * (lam * Real.log (n : ℝ))) / 2 = -Real.log (n : ℝ) / 2 by
      field_simp]
    exact exp_neg_half_log hn0
  rw [hexp, autoCorrelation_dilate hlam F (Real.log (n : ℝ))]
  field_simp


/-! ### The Weil form sees only the correlation and the pole plane

The prime side is translation- and reflection-invariant because the correlation is, and the pole
plane is invariant because translation scales the two moments reciprocally while reflection swaps
them.  So the Weil functional is invariant under the affine symmetries of the line, and two tests
with the same correlation and the same pole plane give the same form: those two data are
everything the arithmetic sees. -/

theorem primeSide_translate (F : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) (c : ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation (fun x => F (x + c)) (Real.log n)))
      = ∑ n ∈ Finset.range (N + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autoCorrelation_translate]

theorem autoCorrelation_reflect (F : ℝ → ℝ) (t : ℝ) :
    autoCorrelation (fun x => F (-x)) t = autoCorrelation F t := by
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun y => F y * F (y + -t))
  show (∫ x, F (-x) * F (-(x + t))) = autoCorrelation F t
  rw [← autoCorrelation_neg F t]
  show (∫ x, F (-x) * F (-(x + t))) = ∫ y, F y * F (y + -t)
  rw [← hrefl]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (-x) * F (-(x + t)) = F (-x) * F (-x + -t)
  rw [show -(x + t) = -x + -t by ring]

theorem primeSide_reflect (F : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation (fun x => F (-x)) (Real.log n)))
      = ∑ n ∈ Finset.range (N + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autoCorrelation_reflect]

theorem expMomentNeg_reflect (F : ℝ → ℝ) :
    expMomentNeg (fun x => F (-x)) = expMomentPos F := by
  rw [expMomentNeg, expMomentPos]
  exact MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun y => F y * Real.exp (y / 2))

theorem expMomentPos_reflect (F : ℝ → ℝ) :
    expMomentPos (fun x => F (-x)) = expMomentNeg F := by
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun y => F y * Real.exp (-y / 2))
  rw [expMomentPos, expMomentNeg, ← hrefl]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (-x) * Real.exp (x / 2) = F (-x) * Real.exp (-(-x) / 2)
  rw [show -(-x) / 2 = x / 2 by ring]

/-- **The pole plane is reflection-invariant.** -/
theorem poleplane_reflect (F : ℝ → ℝ) :
    expMomentNeg (fun x => F (-x)) * expMomentPos (fun x => F (-x))
      = expMomentNeg F * expMomentPos F := by
  rw [expMomentNeg_reflect, expMomentPos_reflect]
  ring

/-- **Two tests with the same correlation and pole plane give the same Weil form.** -/
theorem testBalance_source_congr (a : ℕ → ℝ) (N : ℕ) {F G : ℝ → ℝ}
    (hA : autoCorrelation F = autoCorrelation G)
    (hM : (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2
      = (∫ x, G x * Real.cosh (x / 2)) ^ 2 - (∫ x, G x * Real.sinh (x / 2)) ^ 2) :
    (∑ n ∈ Finset.range (N + 1),
          a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = (∑ n ∈ Finset.range (N + 1),
            a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation G (Real.log n)))
        - 2 * ((∫ x, G x * Real.cosh (x / 2)) ^ 2
            - (∫ x, G x * Real.sinh (x / 2)) ^ 2) := by
  rw [hA, hM]


/-! ### The even and odd parts of a test do not interact

Reflecting the integration variable shows that the two mixed correlations of an even and an odd
function cancel, so the Gram kernel of a test is the sum of those of its even and odd parts.  The
pole plane splits the same way — it is the even part's squared moment minus the odd part's — and
therefore the whole Weil form is additive over the even/odd decomposition.  The odd sector is a
genuine direct summand of the theory, not an approximation to it. -/

/-- The even part of a test. -/
def evenPart (F : ℝ → ℝ) (x : ℝ) : ℝ := (F x + F (-x)) / 2

/-- The odd part of a test. -/
def oddPart (F : ℝ → ℝ) (x : ℝ) : ℝ := (F x - F (-x)) / 2

theorem evenPart_add_oddPart (F : ℝ → ℝ) (x : ℝ) : evenPart F x + oddPart F x = F x := by
  rw [evenPart, oddPart]
  ring

theorem evenPart_even (F : ℝ → ℝ) (x : ℝ) : evenPart F (-x) = evenPart F x := by
  rw [evenPart, evenPart, neg_neg]
  ring

theorem oddPart_odd (F : ℝ → ℝ) (x : ℝ) : oddPart F (-x) = -oddPart F x := by
  rw [oddPart, oddPart, neg_neg]
  ring

/-- **An even and an odd test have cancelling mixed correlations.** -/
theorem sym_pairCorrelation_even_odd {E O : ℝ → ℝ} (hE : ∀ x, E (-x) = E x)
    (hO : ∀ x, O (-x) = -O x) (t : ℝ) :
    pairCorrelation E O t + pairCorrelation O E t = 0 := by
  have hrefl := MeasureTheory.integral_neg_eq_self
    (μ := (volume : Measure ℝ)) (fun x => E x * O (x + t))
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun y => O (y - t) * E y) t
  have hEO : pairCorrelation E O t = -∫ x, O (x - t) * E x := by
    rw [pairCorrelation, ← hrefl]
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show E (-x) * O (-x + t) = -(O (x - t) * E x)
    rw [hE x, show -x + t = -(x - t) by ring, hO (x - t)]
    ring
  have hOE : pairCorrelation O E t = ∫ x, O (x - t) * E x := by
    rw [pairCorrelation, ← hshift]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show O x * E (x + t) = O (x + t - t) * E (x + t)
    rw [show x + t - t = x by ring]
  rw [hEO, hOE]
  ring

/-- **The Gram kernel splits over the even/odd decomposition.** -/
theorem autoCorrelation_even_odd_split (hF : Continuous F) (hFc : HasCompactSupport F)
    (t : ℝ) :
    autoCorrelation F t = autoCorrelation (evenPart F) t + autoCorrelation (oddPart F) t := by
  have hEc : Continuous (evenPart F) := by
    unfold evenPart
    exact ((hF.add (hF.comp continuous_neg)).div_const 2)
  have hOc : Continuous (oddPart F) := by
    unfold oddPart
    exact ((hF.sub (hF.comp continuous_neg)).div_const 2)
  have hFneg : HasCompactSupport fun x => F (-x) :=
    hFc.comp_homeomorph (Homeomorph.neg ℝ)
  have hEcs : HasCompactSupport (evenPart F) := by
    have h : HasCompactSupport ((fun y : ℝ => y / 2) ∘ (F + fun x => F (-x))) :=
      (hFc.add hFneg).comp_left (by simp)
    exact h
  have hOcs : HasCompactSupport (oddPart F) := by
    have h : HasCompactSupport ((fun y : ℝ => y / 2) ∘ (F - fun x => F (-x))) :=
      (hFc.sub hFneg).comp_left (by simp)
    exact h
  have hsum : autoCorrelation F t
      = autoCorrelation (fun x => evenPart F x + oddPart F x) t := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F x * F (x + t)
      = (evenPart F x + oddPart F x) * (evenPart F (x + t) + oddPart F (x + t))
    rw [evenPart_add_oddPart, evenPart_add_oddPart]
  rw [hsum, autoCorrelation_add hEc hEcs hOc hOcs,
    sym_pairCorrelation_even_odd (evenPart_even F) (oddPart_odd F) t, add_zero]

/-- On an even test the pole plane is a perfect square. -/
theorem expMomentNeg_even {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) :
    expMomentNeg F = expMomentPos F := by
  have h := expMomentNeg_reflect F
  rw [show (fun x => F (-x)) = F from funext heven] at h
  exact h


/-! ### The Weil form splits over the even/odd decomposition

The moments are linear, the odd part's moments are negatives of each other and the even part's
are equal, so the pole plane of any test is the even part's squared moment minus the odd part's.
With the splitting of the Gram kernel this makes the whole Weil form additive over the even/odd
decomposition: the even sector carries a positive pole charge, the odd sector a negative one, and
they do not interact. -/

theorem continuous_evenPart (hF : Continuous F) : Continuous (evenPart F) := by
  unfold evenPart
  exact (hF.add (hF.comp continuous_neg)).div_const 2

theorem continuous_oddPart (hF : Continuous F) : Continuous (oddPart F) := by
  unfold oddPart
  exact (hF.sub (hF.comp continuous_neg)).div_const 2

theorem hasCompactSupport_evenPart (hFc : HasCompactSupport F) :
    HasCompactSupport (evenPart F) := by
  have hFneg : HasCompactSupport fun x => F (-x) := hFc.comp_homeomorph (Homeomorph.neg ℝ)
  have h : HasCompactSupport ((fun y : ℝ => y / 2) ∘ (F + fun x => F (-x))) :=
    (hFc.add hFneg).comp_left (by simp)
  exact h

theorem hasCompactSupport_oddPart (hFc : HasCompactSupport F) :
    HasCompactSupport (oddPart F) := by
  have hFneg : HasCompactSupport fun x => F (-x) := hFc.comp_homeomorph (Homeomorph.neg ℝ)
  have h : HasCompactSupport ((fun y : ℝ => y / 2) ∘ (F - fun x => F (-x))) :=
    (hFc.sub hFneg).comp_left (by simp)
  exact h

theorem expMomentNeg_split (hF : Continuous F) (hFc : HasCompactSupport F) :
    expMomentNeg F = expMomentNeg (evenPart F) + expMomentNeg (oddPart F) := by
  have hfun : F = fun x => evenPart F x + oddPart F x :=
    funext fun x => (evenPart_add_oddPart F x).symm
  rw [show expMomentNeg F = expMomentNeg (fun x => evenPart F x + oddPart F x) by rw [← hfun]]
  exact expMomentNeg_add (continuous_evenPart hF) (hasCompactSupport_evenPart hFc)
    (continuous_oddPart hF) (hasCompactSupport_oddPart hFc)

theorem expMomentPos_split (hF : Continuous F) (hFc : HasCompactSupport F) :
    expMomentPos F = expMomentPos (evenPart F) + expMomentPos (oddPart F) := by
  have hfun : F = fun x => evenPart F x + oddPart F x :=
    funext fun x => (evenPart_add_oddPart F x).symm
  rw [show expMomentPos F = expMomentPos (fun x => evenPart F x + oddPart F x) by rw [← hfun]]
  exact expMomentPos_add (continuous_evenPart hF) (hasCompactSupport_evenPart hFc)
    (continuous_oddPart hF) (hasCompactSupport_oddPart hFc)

/-- **The pole plane in even/odd coordinates.** -/
theorem poleplane_even_odd (hF : Continuous F) (hFc : HasCompactSupport F) :
    expMomentNeg F * expMomentPos F
      = expMomentPos (evenPart F) ^ 2 - expMomentPos (oddPart F) ^ 2 := by
  have hE : expMomentNeg (evenPart F) = expMomentPos (evenPart F) :=
    expMomentNeg_even (evenPart_even F)
  have hO : expMomentPos (oddPart F) = -expMomentNeg (oddPart F) :=
    expMomentPos_odd (continuous_oddPart hF) (hasCompactSupport_oddPart hFc) (oddPart_odd F)
  have hO' : expMomentNeg (oddPart F) = -expMomentPos (oddPart F) := by linarith
  rw [expMomentNeg_split hF hFc, expMomentPos_split hF hFc, hE, hO']
  ring

/-- On an even test the pole plane is a nonnegative charge. -/
theorem poleplane_even_nonneg {E : ℝ → ℝ} (hE : ∀ x, E (-x) = E x) :
    0 ≤ expMomentNeg E * expMomentPos E := by
  rw [expMomentNeg_even hE]
  exact mul_self_nonneg _

/-- **The Weil form is additive over the even/odd decomposition.** -/
theorem weilForm_even_odd_split (hF : Continuous F) (hFc : HasCompactSupport F)
    (a : ℕ → ℝ) (N : ℕ) :
    ((∑ n ∈ Finset.range (N + 1),
          a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * (expMomentNeg F * expMomentPos F))
      = ((∑ n ∈ Finset.range (N + 1),
            a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation (evenPart F) (Real.log n)))
          - 2 * (expMomentNeg (evenPart F) * expMomentPos (evenPart F)))
        + ((∑ n ∈ Finset.range (N + 1),
              a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation (oddPart F) (Real.log n)))
            - 2 * (expMomentNeg (oddPart F) * expMomentPos (oddPart F))) := by
  have hprime : (∑ n ∈ Finset.range (N + 1),
        a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = (∑ n ∈ Finset.range (N + 1),
          a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation (evenPart F) (Real.log n)))
        + ∑ n ∈ Finset.range (N + 1),
          a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation (oddPart F) (Real.log n)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [autoCorrelation_even_odd_split hF hFc]
    ring
  have hE : expMomentNeg (evenPart F) = expMomentPos (evenPart F) :=
    expMomentNeg_even (evenPart_even F)
  have hO : expMomentPos (oddPart F) = -expMomentNeg (oddPart F) :=
    expMomentPos_odd (continuous_oddPart hF) (hasCompactSupport_oddPart hFc) (oddPart_odd F)
  have hpp := poleplane_even_odd hF hFc
  have hO' : expMomentNeg (oddPart F) = -expMomentPos (oddPart F) := by linarith
  rw [hprime, hpp, hE, hO']
  ring


/-! ### The positivity problem splits into the two sectors

Because the Weil form is additive over the even/odd decomposition and each part inherits the
aperture, positivity on all tests is exactly positivity on even tests together with positivity on
odd tests.  The two sectors can be attacked separately with no loss, which is what the programme's
concentration on the odd cone presumes. -/

/-- The Weil form of a source against a test. -/
def weilForm (a : ℕ → ℝ) (N : ℕ) (F : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), a n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
    - 2 * (expMomentNeg F * expMomentPos F)

theorem weilForm_split (hF : Continuous F) (hFc : HasCompactSupport F) (a : ℕ → ℝ) (N : ℕ) :
    weilForm a N F = weilForm a N (evenPart F) + weilForm a N (oddPart F) :=
  weilForm_even_odd_split hF hFc a N

theorem evenPart_supp {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    ∀ y, r < |y| → evenPart F y = 0 := by
  intro y hy
  rw [evenPart, hsupp y hy, hsupp (-y) (by rwa [abs_neg])]
  ring

theorem oddPart_supp {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) :
    ∀ y, r < |y| → oddPart F y = 0 := by
  intro y hy
  rw [oddPart, hsupp y hy, hsupp (-y) (by rwa [abs_neg])]
  ring

theorem contDiff_one_evenPart (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (evenPart F) := by
  unfold evenPart
  exact (hF.add (hF.comp contDiff_neg)).div_const 2

theorem contDiff_one_oddPart (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (oddPart F) := by
  unfold oddPart
  exact (hF.sub (hF.comp contDiff_neg)).div_const 2

/-- **Positivity on all tests is positivity on the even and the odd sectors.** -/
theorem weilForm_nonneg_iff (a : ℕ → ℝ) (N : ℕ) :
    (∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G → 0 ≤ weilForm a N G)
      ↔ ((∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G → (∀ x, G (-x) = G x) →
            0 ≤ weilForm a N G)
          ∧ ∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G → (∀ x, G (-x) = -G x) →
            0 ≤ weilForm a N G) := by
  constructor
  · intro h
    exact ⟨fun G hG hGc _ => h G hG hGc, fun G hG hGc _ => h G hG hGc⟩
  · rintro ⟨hev, hod⟩ G hG hGc
    have hsplit := weilForm_split hG hGc a N
    have h1 := hev (evenPart G) (continuous_evenPart hG) (hasCompactSupport_evenPart hGc)
      (evenPart_even G)
    have h2 := hod (oddPart G) (continuous_oddPart hG) (hasCompactSupport_oddPart hGc)
      (oddPart_odd G)
    linarith

/-- **The Chebyshev residue splits over the sectors too.** -/
theorem residue_even_odd_split (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∫ s in Ioi (0:ℝ), lagSourceDefect a s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)))
      = (∫ s in Ioi (0:ℝ), lagSourceDefect a s *
            (2 * Real.exp (-s / 2) * (crossCorrelation (evenPart F) s
              - autoCorrelation (evenPart F) s / 2)))
        + ∫ s in Ioi (0:ℝ), lagSourceDefect a s *
            (2 * Real.exp (-s / 2) * (crossCorrelation (oddPart F) s
              - autoCorrelation (oddPart F) s / 2)) := by
  have hbF := testBalance_source a ha0 ha1 hF hFc hr hsupp hN
  have hbE := testBalance_source a ha0 ha1 (contDiff_one_evenPart hF)
    (hasCompactSupport_evenPart hFc) hr (evenPart_supp hsupp) hN
  have hbO := testBalance_source a ha0 ha1 (contDiff_one_oddPart hF)
    (hasCompactSupport_oddPart hFc) hr (oddPart_supp hsupp) hN
  have hsplit := weilForm_split hF.continuous hFc a N
  rw [weilForm, weilForm, weilForm] at hsplit
  rw [poleplane_eq_moment_mul hF.continuous hFc] at hbF
  rw [poleplane_eq_moment_mul (continuous_evenPart hF.continuous)
    (hasCompactSupport_evenPart hFc)] at hbE
  rw [poleplane_eq_moment_mul (continuous_oddPart hF.continuous)
    (hasCompactSupport_oddPart hFc)] at hbO
  linarith


/-! ### The selectivity audit at Weil level

The three test models now have their own Weil-shaped balances, with the same pole plane and their
own defects, and each is compared with `ζ` by the pairing of the prefix difference alone.  The
sector masses add, so each sector carries at most the whole mass. -/

/-- **Pythagoras for the even/odd decomposition.** -/
theorem autoCorrelation_zero_split (hF : Continuous F) (hFc : HasCompactSupport F) :
    autoCorrelation F 0
      = autoCorrelation (evenPart F) 0 + autoCorrelation (oddPart F) 0 :=
  autoCorrelation_even_odd_split hF hFc 0

theorem autoCorrelation_oddPart_zero_le (hF : Continuous F) (hFc : HasCompactSupport F) :
    autoCorrelation (oddPart F) 0 ≤ autoCorrelation F 0 := by
  have hsplit := autoCorrelation_zero_split hF hFc
  have hE := autoCorrelation_zero_nonneg (evenPart F)
  linarith

/-- **The Weil form of the Liouville twist.** -/
theorem testBalance_liouville (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        liouvilleTwistWeight n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect liouvilleTwistWeight s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) :=
  testBalance_source liouvilleTwistWeight liouvilleTwistWeight_zero liouvilleTwistWeight_one
    hF hFc hr hsupp hN

/-- **The Weil form of the shifted pair.** -/
theorem testBalance_shiftedPair (α : ℝ) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
        shiftedPairWeight α n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)
      = ∫ s in Ioi (0:ℝ), lagSourceDefect (shiftedPairWeight α) s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) :=
  testBalance_source (shiftedPairWeight α) (shiftedPairWeight_zero α) (shiftedPairWeight_one α)
    hF hFc hr hsupp hN

/-- **`ζ` against the Liouville twist at Weil level:** the pole plane cancels. -/
theorem testBalance_vonMangoldt_sub_liouville (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - ∑ n ∈ Finset.range (N + 1),
            liouvilleTwistWeight n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n))
      = (∫ s in Ioi (0:ℝ), chebyshevTwoPoleDefect s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)))
        - ∫ s in Ioi (0:ℝ), lagSourceDefect liouvilleTwistWeight s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have h := testBalance_source_sub (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    liouvilleTwistWeight (by simp) (by simp) liouvilleTwistWeight_zero
    liouvilleTwistWeight_one hF hFc hr hsupp hN
  rw [← chebyshevTwoPoleDefect_eq_lagSourceDefect] at h
  exact h


/-! ### The forced density is scale-local

The chain argument places each of its lags inside the window it was built from, so the count it
produces is a count *in that window*.  Starting the chain at an arbitrary scale therefore forces
generalised primes in every window, not merely in total: a bounded defect is incompatible with a
gap anywhere. -/

open scoped Classical in
/-- **The chain criterion counts atoms inside the window it ranges over.** -/
theorem card_window_ge_of_defect_le (T : Finset ℕ) (μ lam : ℕ → ℝ) (W : ℝ → ℝ) {K : ℝ}
    (sc : ℕ → ℝ) (hmono : Monotone sc) {J : ℕ}
    (hstep : ∀ j, j < J → 2 * K < W (sc (j + 1)) - W (sc j))
    (hbound : ∀ j, j ≤ J → |W (sc j) - genPrefix T μ lam (sc j)| ≤ K) :
    J ≤ (T.filter (fun n : ℕ => μ n ≠ 0 ∧ sc 0 < lam n ∧ lam n ≤ sc J)).card := by
  have hchoice : ∀ j : ℕ, j < J →
      ∃ n ∈ T.filter (fun n : ℕ => μ n ≠ 0 ∧ sc 0 < lam n ∧ lam n ≤ sc J),
        sc j < lam n ∧ lam n ≤ sc (j + 1) := by
    intro j hj
    by_contra hcon
    have hgap : ∀ n ∈ T, μ n = 0 ∨ lam n ≤ sc j ∨ sc (j + 1) < lam n := by
      intro n hn
      by_cases h0 : μ n = 0
      · exact Or.inl h0
      · refine Or.inr ?_
        rcases le_or_gt (lam n) (sc j) with hle | hgt
        · exact Or.inl hle
        · rcases le_or_gt (lam n) (sc (j + 1)) with hle2 | hgt2
          · refine absurd ⟨n, Finset.mem_filter.mpr ⟨hn, h0,
              lt_of_le_of_lt (hmono (Nat.zero_le j)) hgt,
              le_trans hle2 (hmono (by omega : j + 1 ≤ J))⟩, hgt, hle2⟩ hcon
          · exact Or.inr hgt2
    have hcrit := gen_cell_increment_le_two_mul_defect_supp T μ lam W
      (hmono (by omega : j ≤ j + 1)) hgap
    have hmax : max |W (sc j) - genPrefix T μ lam (sc j)|
        |W (sc (j + 1)) - genPrefix T μ lam (sc (j + 1))| ≤ K :=
      max_le (hbound j (by omega)) (hbound (j + 1) (by omega))
    linarith [hstep j hj]
  choose! f hfT hf1 hf2 using hchoice
  have hinj : Set.InjOn f (Finset.range J : Finset ℕ) := by
    intro α hα β hβ hab
    rw [Finset.mem_coe, Finset.mem_range] at hα hβ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : lam (f α) ≤ sc (α + 1) := hf2 α hα
      have h2 : sc β < lam (f β) := hf1 β hβ
      have h3 : sc (α + 1) ≤ sc β := hmono (by omega)
      rw [hab] at h1
      linarith
    · have h1 : lam (f β) ≤ sc (β + 1) := hf2 β hβ
      have h2 : sc α < lam (f α) := hf1 α hα
      have h3 : sc (β + 1) ≤ sc α := hmono (by omega)
      rw [hab] at h2
      linarith
  have hcard := Finset.card_le_card_of_injOn f
    (fun α hα => hfT α (Finset.mem_range.mp hα)) hinj
  rwa [Finset.card_range] at hcard

/-- The scale sequence for a window starting at `S`, and its step for the pole at `1`. -/
theorem twoPole_window_step {K S : ℝ} (hK : 0 < K) (j : ℕ) :
    2 * K < twoPoleWeight (Real.log (Real.exp S + 3 * K * ((j : ℝ) + 1)))
      - twoPoleWeight (Real.log (Real.exp S + 3 * K * (j : ℝ))) := by
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hp0 : (0:ℝ) < Real.exp S + 3 * K * (j : ℝ) := by
    have := Real.exp_pos S
    nlinarith
  have hp1 : (0:ℝ) < Real.exp S + 3 * K * ((j : ℝ) + 1) := by
    have := Real.exp_pos S
    nlinarith
  have hlog : Real.log (Real.exp S + 3 * K * (j : ℝ))
      ≤ Real.log (Real.exp S + 3 * K * ((j : ℝ) + 1)) :=
    Real.log_le_log hp0 (by nlinarith)
  rw [twoPoleWeight, twoPoleWeight, Real.exp_log hp0, Real.exp_log hp1]
  linarith

theorem twoPole_window_mono {K S : ℝ} (hK : 0 < K) :
    Monotone (fun j : ℕ => Real.log (Real.exp S + 3 * K * (j : ℝ))) := by
  intro α β hab
  have hj : (0:ℝ) ≤ (α : ℝ) := Nat.cast_nonneg α
  have hp0 : (0:ℝ) < Real.exp S + 3 * K * (α : ℝ) := by
    have := Real.exp_pos S
    nlinarith
  have hcast : (α : ℝ) ≤ (β : ℝ) := by exact_mod_cast hab
  exact Real.log_le_log hp0 (by nlinarith)


/-! ### An atom-free interval forces a large defect

Across an interval carrying no atom the prefix is frozen while the calibration climbs by at least
the interval's length, so the defect must absorb it: a stretch of length `L` with no atom forces
a defect of at least `L/2` at one of its ends.  For `ζ` this says a prime-power gap below `x` is
visible in the Chebyshev defect at full size, and conversely a defect bounded by `K` forces a
prime power in every interval longer than `2K`. -/

theorem lagPrefix_eq_of_atomfree (a : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hfree : ∀ n : ℕ, u < (n : ℝ) → (n : ℝ) ≤ v → a n = 0) :
    lagPrefix a (Real.log v) = lagPrefix a (Real.log u) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hfu : ⌊Real.exp (Real.log u)⌋₊ = ⌊u⌋₊ := by rw [Real.exp_log hu]
  have hfv : ⌊Real.exp (Real.log v)⌋₊ = ⌊v⌋₊ := by rw [Real.exp_log hv]
  have hsub : Finset.Icc 0 ⌊u⌋₊ ⊆ Finset.Icc 0 ⌊v⌋₊ := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 (Nat.floor_le_floor huv)⟩
  rw [lagPrefix, lagPrefix, hfu, hfv]
  refine (Finset.sum_subset hsub fun x hx hnot => ?_).symm
  rw [Finset.mem_Icc] at hx
  have hxu : ⌊u⌋₊ < x := by
    by_contra hc
    exact hnot (Finset.mem_Icc.mpr ⟨hx.1, le_of_not_gt hc⟩)
  have h1 : u < (x : ℝ) := (Nat.floor_lt hu.le).mp hxu
  have h2 : (x : ℝ) ≤ v := by
    have hxv : (x : ℝ) ≤ (⌊v⌋₊ : ℝ) := by exact_mod_cast hx.2
    exact le_trans hxv (Nat.floor_le hv.le)
  exact hfree x h1 h2

/-- **An atom-free interval forces a defect of at least half its length.** -/
theorem defect_ge_of_atomfree (a : ℕ → ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hfree : ∀ n : ℕ, u < (n : ℝ) → (n : ℝ) ≤ v → a n = 0) :
    (v - u) / 2
      ≤ max |lagSourceDefect a (Real.log u)| |lagSourceDefect a (Real.log v)| := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hpref := lagPrefix_eq_of_atomfree a hu huv hfree
  have hincr : v - u ≤ twoPoleWeight (Real.log v) - twoPoleWeight (Real.log u) := by
    rw [twoPoleWeight, twoPoleWeight, Real.exp_log hu, Real.exp_log hv]
    have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu huv
    linarith
  set x := lagSourceDefect a (Real.log u) with hx
  set y := lagSourceDefect a (Real.log v) with hy
  have hdiff : y - x = twoPoleWeight (Real.log v) - twoPoleWeight (Real.log u) := by
    rw [hx, hy, lagSourceDefect, lagSourceDefect, hpref]
    ring
  have hb1 := neg_abs_le x
  have hb2 := le_abs_self y
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  linarith

/-- **A prime-power gap is visible in the Chebyshev defect at full size.** -/
theorem chebyshev_defect_ge_of_primePower_free {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hfree : ∀ n : ℕ, u < (n : ℝ) → (n : ℝ) ≤ v →
      (ArithmeticFunction.vonMangoldt n : ℝ) = 0) :
    (v - u) / 2
      ≤ max |chebyshevTwoPoleDefect (Real.log u)| |chebyshevTwoPoleDefect (Real.log v)| := by
  have h := defect_ge_of_atomfree (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hu huv hfree
  rwa [← chebyshevTwoPoleDefect_eq_lagSourceDefect] at h

/-- **A bounded Chebyshev defect forces a prime power in every long interval.** -/
theorem exists_primePower_of_chebyshev_defect_le {u L K : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (h1 : |chebyshevTwoPoleDefect (Real.log u)| ≤ K)
    (h2 : |chebyshevTwoPoleDefect (Real.log (u + L))| ≤ K) (hbig : 2 * K < L) :
    ∃ n : ℕ, u < (n : ℝ) ∧ (n : ℝ) ≤ u + L ∧ (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := by
  by_contra hcon
  have hfree : ∀ n : ℕ, u < (n : ℝ) → (n : ℝ) ≤ u + L →
      (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
    intro n hn1 hn2
    by_contra hc
    exact hcon ⟨n, hn1, hn2, hc⟩
  have hlow := chebyshev_defect_ge_of_primePower_free hu (by linarith : u ≤ u + L) hfree
  have hmax : max |chebyshevTwoPoleDefect (Real.log u)|
      |chebyshevTwoPoleDefect (Real.log (u + L))| ≤ K := max_le h1 h2
  have : u + L - u = L := by ring
  rw [this] at hlow
  linarith


/-! ### The gap principle at an arbitrary pole, and exact values at the first scales

Against a calibration at `ρ` an atom-free interval forces a defect of at least `(v^ρ−u^ρ)/2ρ`:
the heavier the pole, the more a gap costs.  At the first prime scales the Chebyshev defect can
be written out exactly — it is `1` at `log 2` and `2 − log 2` at `log 3`. -/

theorem defect_poleAt_ge_of_atomfree (a : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) {u v : ℝ} (hu : 0 < u)
    (huv : u ≤ v) (hfree : ∀ n : ℕ, u < (n : ℝ) → (n : ℝ) ≤ v → a n = 0) :
    (v ^ ρ - u ^ ρ) / (2 * ρ)
      ≤ max |lagSourceDefectAt ρ a (Real.log u)| |lagSourceDefectAt ρ a (Real.log v)| := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hpref := lagPrefix_eq_of_atomfree a hu huv hfree
  have hvalu : poleWeightAt ρ (Real.log u) = (u ^ ρ - 1) / ρ + Real.log u := by
    rw [poleWeightAt, exp_mul_log ρ hu]
  have hvalv : poleWeightAt ρ (Real.log v) = (v ^ ρ - 1) / ρ + Real.log v := by
    rw [poleWeightAt, exp_mul_log ρ hv]
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have hincr : (v ^ ρ - u ^ ρ) / ρ
      ≤ poleWeightAt ρ (Real.log v) - poleWeightAt ρ (Real.log u) := by
    rw [hvalu, hvalv]
    have : (v ^ ρ - 1) / ρ - (u ^ ρ - 1) / ρ = (v ^ ρ - u ^ ρ) / ρ := by
      field_simp
      ring
    linarith
  set x := lagSourceDefectAt ρ a (Real.log u) with hx
  set y := lagSourceDefectAt ρ a (Real.log v) with hy
  have hdiff : y - x = poleWeightAt ρ (Real.log v) - poleWeightAt ρ (Real.log u) := by
    rw [hx, hy, lagSourceDefectAt, lagSourceDefectAt, hpref]
    ring
  have hb1 := neg_abs_le x
  have hb2 := le_abs_self y
  have hmax1 : |x| ≤ max |x| |y| := le_max_left _ _
  have hmax2 : |y| ≤ max |x| |y| := le_max_right _ _
  have h2ρ : (0:ℝ) < 2 * ρ := by linarith
  rw [div_le_iff₀ hρ, ← hdiff] at hincr
  have hyx : y - x ≤ 2 * max |x| |y| := by linarith
  have hmul : (y - x) * ρ ≤ (2 * max |x| |y|) * ρ := mul_le_mul_of_nonneg_right hyx hρ.le
  rw [div_le_iff₀ h2ρ]
  linarith

/-- The Chebyshev defect at an integer scale. -/
theorem chebyshevTwoPoleDefect_log_nat {N : ℕ} (hN : 1 ≤ N) :
    chebyshevTwoPoleDefect (Real.log (N : ℝ))
      = (N : ℝ) + Real.log (N : ℝ) - 1
        - ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  rw [chebyshevTwoPoleDefect, twoPoleWeight, Real.exp_log hN0, lagChebyshev,
    Real.exp_log hN0, Nat.floor_natCast]

/-- **The Chebyshev defect at the first prime scale is exactly one.** -/
theorem chebyshevTwoPoleDefect_log_two : chebyshevTwoPoleDefect (Real.log 2) = 1 := by
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [chebyshevTwoPoleDefect, lagChebyshev_eq_log_two le_rfl hlt, twoPoleWeight,
    Real.exp_log (by norm_num : (0:ℝ) < 2)]
  ring


/-! ### The receiver's sign at the first scales

The Chebyshev defect is the whole calibration below `log 2`, equals `1` at `log 2` and `2 − log 2`
at `log 3`; and the critical-scale functional is strictly positive on the first two cells.  The
receiver starts positive, so any sign change it has is an arithmetic event, not a boundary
artefact. -/

theorem lagChebyshev_eq_log_six {s : ℝ} (h1 : Real.log 3 ≤ s) (h2 : s < Real.log 4) :
    lagChebyshev s = Real.log 2 + Real.log 3 := by
  have hge : (3:ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at this
  have hlt : Real.exp s < 4 := by
    have := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 4)] at this
  have hfl : ⌊Real.exp s⌋₊ = 3 := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · exact_mod_cast hge
    · exact_mod_cast hlt
  have hIcc : Finset.Icc 0 3 = Finset.range 4 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
    omega
  rw [lagChebyshev, hfl, hIcc]
  simp [Finset.sum_range_succ, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]

/-- **The Chebyshev defect at the second prime scale.** -/
theorem chebyshevTwoPoleDefect_log_three :
    chebyshevTwoPoleDefect (Real.log 3) = 2 - Real.log 2 := by
  have hlt : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [chebyshevTwoPoleDefect, lagChebyshev_eq_log_six le_rfl hlt, twoPoleWeight,
    Real.exp_log (by norm_num : (0:ℝ) < 3)]
  ring

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

theorem chebyshevTwoPoleDefect_log_three_pos :
    0 < chebyshevTwoPoleDefect (Real.log 3) := by
  rw [chebyshevTwoPoleDefect_log_three]
  linarith [log_two_le_one]

/-- The receiver is strictly positive on the quiet cell. -/
theorem criticalScalePrefix_pos_first_cell {s : ℝ} (hs0 : 0 < s) (hs : s ≤ Real.log 2) :
    0 < criticalScalePrefix s := by
  rw [criticalScalePrefix_first_cell (le_of_lt hs0) hs]
  have := Real.add_one_lt_exp (ne_of_gt hs0)
  linarith

/-- **The receiver is strictly positive on the first prime cell too.** -/
theorem criticalScalePrefix_pos_second_cell {s : ℝ} (h1 : Real.log 2 ≤ s)
    (h2 : s < Real.log 3) :
    0 < criticalScalePrefix s := by
  have hge : (2:ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
  have hgap : Real.log 3 - Real.log 2 ≤ 1 / 2 := by
    have hdiv : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hle := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3 / 2)
    rw [hdiv] at hle
    linarith
  have hlog2 := log_two_le_one
  have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [criticalScalePrefix_second_cell h1 h2]
  nlinarith [hge, hgap, hlog2, hlog2pos, h2]


/-! ### Propagating the receiver's positivity

On a cell the receiver loses at most the frozen Chebyshev count times the logarithmic gap, so
positivity propagates whenever that loss is below what the cell gains.  Since the loss is at most
`ψ(N)/N` and the gain is `1`, the propagation condition is exactly the prime number theorem with
a margin: the receiver's sign is a statement at PNT precision, which is why nothing cruder
decides it. -/

theorem criticalScalePrefix_pos_on_cell {N : ℕ} (hN : 1 ≤ N)
    (hloss : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
        * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      < criticalScalePrefix (Real.log (N : ℝ))) {s : ℝ}
    (h1 : Real.log (N : ℝ) ≤ s) (h2 : s ≤ Real.log ((N : ℝ) + 1)) :
    0 < criticalScalePrefix s := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hge : (N : ℝ) ≤ Real.exp s := by
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hN0] at this
  have hpsi : 0 ≤ ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) :=
    Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hgap : s - Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by linarith
  have hmul : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
      * (s - Real.log (N : ℝ))
      ≤ (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
        * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hpsi
  rw [criticalScalePrefix_on_cell hN h1 h2]
  linarith

/-- **Positivity propagates to the next integer scale.** -/
theorem criticalScalePrefix_succ_pos {N : ℕ} (hN : 1 ≤ N)
    (hstep : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
        * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      < 1 + criticalScalePrefix (Real.log (N : ℝ))) :
    0 < criticalScalePrefix (Real.log ((N : ℝ) + 1)) := by
  rw [criticalScalePrefix_succ hN]
  linarith

/-- The logarithmic gap is at most the reciprocal of the scale. -/
theorem log_gap_le_inv {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hdiv : Real.log (((N : ℝ) + 1) / (N : ℝ))
      = Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) :=
    Real.log_div (by linarith) (ne_of_gt hN0)
  have hle := Real.log_le_sub_one_of_pos
    (by positivity : (0:ℝ) < ((N : ℝ) + 1) / (N : ℝ))
  rw [hdiv] at hle
  have hval : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
    field_simp
    ring
  linarith

/-- **The propagation condition is the prime number theorem with a margin.** -/
theorem criticalScalePrefix_succ_pos_of_psi {N : ℕ} (hN : 1 ≤ N)
    (hstep : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) / (N : ℝ)
      < 1 + criticalScalePrefix (Real.log (N : ℝ))) :
    0 < criticalScalePrefix (Real.log ((N : ℝ) + 1)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hpsi : 0 ≤ ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) :=
    Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  refine criticalScalePrefix_succ_pos hN ?_
  have hgap := log_gap_le_inv hN
  have hmul : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
      * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      ≤ (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) * (1 / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hpsi
  have hdiv : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) * (1 / (N : ℝ))
      = (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) / (N : ℝ) := by
    field_simp
  linarith [hmul, hdiv ▸ hstep]


/-! ### Unconditional envelopes for the receiver at the integer scales

Each cell contributes at most one unit and at least `1 − ψ(N)/N`, so the receiver at the scale
`log(M+1)` lies between `M − Σ_{k<M} ψ(k+1)/(k+1)` and `M`.  Both envelopes are unconditional;
the whole question is how much of the upper envelope the prime counts eat. -/

theorem criticalScalePrefix_succ_ge {N : ℕ} (hN : 1 ≤ N) :
    criticalScalePrefix (Real.log (N : ℝ)) + 1
        - (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) / (N : ℝ)
      ≤ criticalScalePrefix (Real.log ((N : ℝ) + 1)) := by
  have hpsi : 0 ≤ ∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ) :=
    Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hgap := log_gap_le_inv hN
  have hmul : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ))
      * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      ≤ (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) * (1 / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap hpsi
  have hdiv : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) * (1 / (N : ℝ))
      = (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℝ)) / (N : ℝ) := by
    field_simp
  rw [criticalScalePrefix_succ hN]
  linarith [hdiv ▸ hmul]

/-- **The receiver never exceeds the scale count.** -/
theorem criticalScalePrefix_le_nat (M : ℕ) :
    criticalScalePrefix (Real.log ((M : ℝ) + 1)) ≤ (M : ℝ) := by
  induction M with
  | zero => simp [criticalScalePrefix]
  | succ M ih =>
      have hstep := criticalScalePrefix_succ (N := M + 1) (by omega)
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hstep
      have hpsi : 0 ≤ ∑ k ∈ Finset.Icc 0 (M + 1), (ArithmeticFunction.vonMangoldt k : ℝ) :=
        Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
      have hgapnn : 0 ≤ Real.log ((M : ℝ) + 1 + 1) - Real.log ((M : ℝ) + 1) := by
        have : (0:ℝ) < (M : ℝ) + 1 := by positivity
        linarith [Real.log_le_log this (by linarith : (M : ℝ) + 1 ≤ (M : ℝ) + 1 + 1)]
      have hmulnn : 0 ≤ (∑ k ∈ Finset.Icc 0 (M + 1), (ArithmeticFunction.vonMangoldt k : ℝ))
          * (Real.log ((M : ℝ) + 1 + 1) - Real.log ((M : ℝ) + 1)) :=
        mul_nonneg hpsi hgapnn
      have hgoal : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 1 + 1 := by push_cast; ring
      rw [hgoal]
      push_cast
      linarith [hstep, hmulnn, ih]

/-- **The receiver's unconditional lower envelope.** -/
theorem criticalScalePrefix_ge_sub (M : ℕ) :
    (M : ℝ) - ∑ k ∈ Finset.range M,
        (∑ j ∈ Finset.Icc 0 (k + 1), (ArithmeticFunction.vonMangoldt j : ℝ)) / ((k : ℝ) + 1)
      ≤ criticalScalePrefix (Real.log ((M : ℝ) + 1)) := by
  induction M with
  | zero => simp [criticalScalePrefix]
  | succ M ih =>
      have hstep := criticalScalePrefix_succ_ge (N := M + 1) (by omega)
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hstep
      rw [show ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 1 + 1 by push_cast; ring,
        Finset.sum_range_succ]
      push_cast
      linarith


/-! ### Trivial envelopes, unconditionally

Each von Mangoldt weight is at most the logarithm of its index, so the Chebyshev count below a
scale is at most the count of integers times the scale; and since the count is nonnegative the
receiver never exceeds the pure polar growth.  Integrating the two trivial bounds gives an
explicit unconditional window for the receiver at every scale. -/

/-- **The trivial Chebyshev bound, in the lag variable.** -/
theorem lagChebyshev_le {s : ℝ} (hs : 0 ≤ s) :
    lagChebyshev s ≤ (Real.exp s + 1) * s := by
  have hNle : ((⌊Real.exp s⌋₊ : ℝ)) ≤ Real.exp s :=
    Nat.floor_le (le_of_lt (Real.exp_pos s))
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊Real.exp s⌋₊,
      (ArithmeticFunction.vonMangoldt k : ℝ) ≤ s := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simpa using hs
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk0
      have hkle : (k : ℝ) ≤ Real.exp s := by
        have : (k : ℝ) ≤ (⌊Real.exp s⌋₊ : ℝ) := by exact_mod_cast hk.2
        linarith
      have hlog : Real.log (k : ℝ) ≤ s := by
        have := Real.log_le_log (by linarith : (0:ℝ) < k) hkle
        rwa [Real.log_exp] at this
      exact le_trans ArithmeticFunction.vonMangoldt_le_log hlog
  have hcard : lagChebyshev s ≤ ((Finset.Icc 0 ⌊Real.exp s⌋₊).card : ℝ) * s := by
    rw [lagChebyshev]
    have h1 := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hcardR : ((Finset.Icc 0 ⌊Real.exp s⌋₊).card : ℝ) ≤ Real.exp s + 1 := by
    rw [Nat.card_Icc]
    push_cast
    linarith
  calc lagChebyshev s ≤ ((Finset.Icc 0 ⌊Real.exp s⌋₊).card : ℝ) * s := hcard
    _ ≤ (Real.exp s + 1) * s := mul_le_mul_of_nonneg_right hcardR hs

/-- **The receiver never exceeds the pure polar growth.** -/
theorem criticalScalePrefix_le_exp {s : ℝ} (hs : 0 ≤ s) :
    criticalScalePrefix s ≤ Real.exp s - 1 := by
  have hmono : (∫ u in (0:ℝ)..s, (Real.exp u - lagChebyshev u))
      ≤ ∫ u in (0:ℝ)..s, Real.exp u := by
    refine intervalIntegral.integral_mono_on hs
      (intervalIntegrable_criticalScaleIntegrand 0 s)
      (Real.continuous_exp.intervalIntegrable 0 s) fun u _ => ?_
    have := lagChebyshev_nonneg u
    linarith
  have hexp : (∫ u in (0:ℝ)..s, Real.exp u) = Real.exp s - 1 := by
    simp [integral_exp]
  rw [criticalScalePrefix]
  linarith [hmono, hexp]

theorem integral_id_mul_exp (s : ℝ) :
    (∫ u in (0:ℝ)..s, u * Real.exp u) = (s - 1) * Real.exp s + 1 := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y) (u * Real.exp u) u := by
    intro u _
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 u := (hasDerivAt_id u).sub_const 1
    have h2 := h1.mul (Real.hasDerivAt_exp u)
    exact h2.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_id.mul Real.continuous_exp).intervalIntegrable 0 s)]
  simp

/-- **An explicit unconditional lower envelope for the receiver.** -/
theorem criticalScalePrefix_ge_explicit {s : ℝ} (hs : 0 ≤ s) :
    (Real.exp s - 1) - ((s - 1) * Real.exp s + 1) - s ^ 2 / 2
      ≤ criticalScalePrefix s := by
  have hmaj : ∀ u ∈ Set.Icc (0:ℝ) s,
      Real.exp u - (Real.exp u + 1) * u ≤ Real.exp u - lagChebyshev u := by
    intro u hu
    have := lagChebyshev_le hu.1
    linarith
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp u - (Real.exp u + 1) * u) volume 0 s :=
    (Real.continuous_exp.sub ((Real.continuous_exp.add continuous_const).mul
      continuous_id)).intervalIntegrable 0 s
  have hmono := intervalIntegral.integral_mono_on hs hint
    (intervalIntegrable_criticalScaleIntegrand 0 s) hmaj
  have hsplit : (∫ u in (0:ℝ)..s, (Real.exp u - (Real.exp u + 1) * u))
      = (Real.exp s - 1) - ((s - 1) * Real.exp s + 1) - s ^ 2 / 2 := by
    have hcong : ∀ u ∈ Set.uIcc (0:ℝ) s,
        Real.exp u - (Real.exp u + 1) * u = Real.exp u - u * Real.exp u - u := by
      intro u _
      ring
    rw [intervalIntegral.integral_congr hcong]
    have hi1 : IntervalIntegrable (fun u : ℝ => Real.exp u - u * Real.exp u) volume 0 s :=
      (Real.continuous_exp.sub (continuous_id.mul Real.continuous_exp)).intervalIntegrable 0 s
    have hi2 : IntervalIntegrable (fun u : ℝ => u) volume 0 s :=
      continuous_id.intervalIntegrable 0 s
    have hi3 : IntervalIntegrable (fun u : ℝ => Real.exp u) volume 0 s :=
      Real.continuous_exp.intervalIntegrable 0 s
    have hi4 : IntervalIntegrable (fun u : ℝ => u * Real.exp u) volume 0 s :=
      (continuous_id.mul Real.continuous_exp).intervalIntegrable 0 s
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_sub hi3 hi4,
      integral_id_mul_exp, integral_id]
    have hexp : (∫ u in (0:ℝ)..s, Real.exp u) = Real.exp s - 1 := by
      simp [integral_exp]
    rw [hexp]
    ring
  rw [criticalScalePrefix]
  linarith [hmono, hsplit]


/-! ### Two more sources, and where their poles sit

The squarefree indicator has density `6/π²`, so it is read against the two-pole weight scaled by
that factor; it is dominated index by index by pure integer density.  The higher prime powers
have prefix of order `√x`, so their pole sits at `1/2` and their ledger is the calibration there —
by the normalisation law their critical line is `1/4`, a quarter of the way, exactly as the pole
position dictates. -/

/-- The squarefree indicator as a source. -/
def squarefreeSource : ℕ → ℝ :=
  fun n => if n ≤ 1 then 0 else ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2

theorem squarefreeSource_zero : squarefreeSource 0 = 0 := by
  rw [squarefreeSource, if_pos (by omega)]

theorem squarefreeSource_one : squarefreeSource 1 = 0 := by
  rw [squarefreeSource, if_pos (by omega)]

theorem squarefreeSource_le_allOnes (n : ℕ) : squarefreeSource n ≤ allOnes n := by
  rw [squarefreeSource, allOnes]
  by_cases h : n ≤ 1
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    have hR : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast this
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℝ), sq_abs
      ((ArithmeticFunction.moebius n : ℤ) : ℝ)]

/-- **The squarefree ledger**, calibrated at the squarefree density. -/
theorem sum_squarefree_sub_scaledPolar_eq_defect (c : ℝ) (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), squarefreeSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), c * (Real.exp s + 1) * h s
      = ∫ s in Ioi (0:ℝ),
          (scaledTwoPoleWeight c s - lagPrefix squarefreeSource s) * deriv h s :=
  sum_weight_sub_calibration_eq_defect squarefreeSource squarefreeSource_zero
    squarefreeSource_one (scaledTwoPoleWeight_zero c)
    (continuous_const.mul continuous_twoPoleWeight) (by fun_prop)
    (hasDerivAt_scaledTwoPoleWeight c) hh hS hvan hN

theorem lagPrefix_squarefree_le (s : ℝ) :
    lagPrefix squarefreeSource s ≤ lagPrefix allOnes s :=
  lagPrefix_mono_of_le squarefreeSource_le_allOnes s

/-- The higher prime powers, as a source. -/
def higherPowerSource : ℕ → ℝ :=
  fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - thetaSource n

theorem higherPowerSource_nonneg (n : ℕ) : 0 ≤ higherPowerSource n := by
  rw [higherPowerSource]
  linarith [thetaSource_le_vonMangoldt n]

theorem higherPowerSource_zero : higherPowerSource 0 = 0 := by
  rw [higherPowerSource, thetaSource_zero]
  simp

theorem higherPowerSource_one : higherPowerSource 1 = 0 := by
  rw [higherPowerSource, thetaSource_one]
  simp

theorem lagPrefix_higherPower (s : ℝ) :
    lagPrefix higherPowerSource s = lagChebyshev s - lagPrefix thetaSource s := by
  rw [lagPrefix, lagPrefix, lagChebyshev, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- **The higher prime powers are read at the pole `1/2`.** -/
theorem sum_higherPower_sub_halfPolar_eq_defect (hh : ContDiff ℝ 1 h) (hS : 0 < S)
    (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ} (hN : Real.exp S ≤ N) :
    (∑ n ∈ Finset.range (N + 1), higherPowerSource n * h (Real.log n))
        - ∫ s in Ioi (0:ℝ), (Real.exp (1 / 2 * s) + 1) * h s
      = ∫ s in Ioi (0:ℝ),
          (poleWeightAt (1 / 2) s - lagPrefix higherPowerSource s) * deriv h s :=
  sum_weight_sub_polarAt_eq_defect (by norm_num) higherPowerSource higherPowerSource_zero
    higherPowerSource_one hh hS hvan hN


/-! ### The Weil form of an arbitrary source at an arbitrary pole

Every integer source has a Weil-shaped balance at every pole, with normalisation `n^{−ρ/2}` and
the pole plane `2(∫Fe^{−ρx/2})(∫Fe^{ρx/2})`.  For the higher prime powers the relevant pole is
`1/2`, so their normalisation is `n^{−1/4}` and their symmetry point is a quarter. -/

/-- **The Weil-shaped balance of an arbitrary source at the pole `ρ`.** -/
theorem testBalanceAt_source (ρ : ℝ) (hρ : ρ ≠ 0) (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), a n *
          (2 * (n : ℝ) ^ (-ρ / 2) * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.exp (-(ρ / 2 * x))) * ∫ x, F x * Real.exp (ρ / 2 * x))
      = ∫ s in Ioi (0:ℝ), lagSourceDefectAt ρ a s *
          (2 * Real.exp (-(ρ * s) / 2)
            * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)) := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeightAt ρ F s = 0 := fun s hs => by
    rw [lagTestWeightAt, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_weight_sub_polarAt_eq_defect hρ a ha0 ha1
    (contDiff_one_lagTestWeightAt ρ hF hFc) hS hvan hN
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeightAt ρ hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), lagSourceDefectAt ρ a s * deriv (lagTestWeightAt ρ F) s
          = lagSourceDefectAt ρ a s *
              (2 * Real.exp (-(ρ * s) / 2)
                * (crossCorrelation F s - ρ / 2 * autoCorrelation F s)))] at hkey
  rw [← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp [ha0]
    · have hn : (0:ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [lagTestWeightAt]
      congr 2
      rw [show -(ρ * Real.log (n : ℝ)) / 2 = (-ρ / 2) * Real.log (n : ℝ) by ring,
        exp_mul_log _ hn]
  · have hpolar := integral_Ioi_cosh_mul_autoCorrelation hF hFc hr hsupp (ρ / 2)
    have hrw : (∫ s in Ioi (0:ℝ), (Real.exp (ρ * s) + 1) * lagTestWeightAt ρ F s)
        = ∫ s in Ioi (0:ℝ), 4 * (Real.cosh (ρ / 2 * s) * autoCorrelation F s) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [lagTestWeightAt, Real.cosh_eq]
      have h1 : Real.exp (ρ / 2 * s) = Real.exp (ρ * s) * Real.exp (-(ρ * s) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (-(ρ / 2 * s)) = Real.exp (-(ρ * s) / 2) := by
        congr 1
        ring
      rw [h1, h2]
      ring
    rw [hrw, MeasureTheory.integral_const_mul, hpolar]
    ring

/-- **The Weil form of the higher prime powers, at their own pole `1/2`.** -/
theorem testBalanceAt_higherPower (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ Finset.range (N + 1), higherPowerSource n *
          (2 * (n : ℝ) ^ (-(1 / 2 : ℝ) / 2) * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.exp (-(1 / 2 / 2 * x)))
            * ∫ x, F x * Real.exp (1 / 2 / 2 * x))
      = ∫ s in Ioi (0:ℝ), lagSourceDefectAt (1 / 2) higherPowerSource s *
          (2 * Real.exp (-(1 / 2 * s) / 2)
            * (crossCorrelation F s - 1 / 2 / 2 * autoCorrelation F s)) :=
  testBalanceAt_source (1 / 2) (by norm_num) higherPowerSource higherPowerSource_zero
    higherPowerSource_one hF hFc hr hsupp hN

/-- The pole at `1/2` is matchable by an integer source with defect `2 + log 2`. -/
theorem abs_defect_halfPole_le {s : ℝ} (hs : 0 ≤ s) :
    |lagSourceDefectAt (1 / 2) (idealSourceAt (1 / 2)) s| ≤ 2 + Real.log 2 := by
  have h := abs_lagSourceDefectAt_idealSourceAt_le (ρ := 1 / 2) (by norm_num) (by norm_num) hs
  norm_num at h
  exact h


/-! ### Calibrations compose with the source

The prefix is additive in the source, so splitting a source splits its defect across any split of
the calibration.  For `ζ` this means the Chebyshev defect is the prime-only defect plus the
higher-power defect, against any decomposition of the two-pole weight — and the higher-power part
contributes nothing below the first prime square. -/

theorem lagPrefix_add (b c : ℕ → ℝ) (s : ℝ) :
    lagPrefix (fun n => b n + c n) s = lagPrefix b s + lagPrefix c s := by
  rw [lagPrefix, lagPrefix, lagPrefix, ← Finset.sum_add_distrib]

/-- **A split of the calibration splits the defect along a split of the source.** -/
theorem defect_split_calibration (b c : ℕ → ℝ) (Wb Wc : ℝ → ℝ) (s : ℝ) :
    (Wb s + Wc s) - lagPrefix (fun n => b n + c n) s
      = (Wb s - lagPrefix b s) + (Wc s - lagPrefix c s) := by
  rw [lagPrefix_add]
  ring

theorem thetaSource_add_higherPower (n : ℕ) :
    thetaSource n + higherPowerSource n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [higherPowerSource]
  ring

/-- **The Chebyshev defect splits into the prime-only and higher-power defects.** -/
theorem chebyshevTwoPoleDefect_split {Wb Wc : ℝ → ℝ}
    (hW : ∀ s, twoPoleWeight s = Wb s + Wc s) (s : ℝ) :
    chebyshevTwoPoleDefect s
      = (Wb s - lagPrefix thetaSource s) + (Wc s - lagPrefix higherPowerSource s) := by
  have hadd : (fun n => thetaSource n + higherPowerSource n)
      = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
    funext thetaSource_add_higherPower
  rw [chebyshevTwoPoleDefect, lagChebyshev_eq_lagPrefix, ← hadd, hW s,
    defect_split_calibration]

/-- Below the first prime square the higher powers contribute nothing. -/
theorem lagPrefix_higherPower_eq_zero_of_lt_log_four {s : ℝ} (hs : s < Real.log 4) :
    lagPrefix higherPowerSource s = 0 := by
  have h := theta_defect_eq_chebyshev_of_lt_log_four hs
  rw [lagSourceDefect, chebyshevTwoPoleDefect] at h
  rw [lagPrefix_higherPower]
  linarith


/-! ### The higher powers are invisible below the first prime square

The prime side is linear in the source, so `ζ`'s Weil form is the prime-only form plus the
higher-power form.  The higher powers' first atom sits at `4`, so below the aperture `log 4 / 2`
they contribute nothing at all and `ζ`'s Weil form coincides with `θ`'s. -/

theorem primeSide_source_add (b c : ℕ → ℝ) (F : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (b n + c n) * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = (∑ n ∈ Finset.range (N + 1),
            b n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        + ∑ n ∈ Finset.range (N + 1),
            c n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem higherPowerSource_eq_zero_of_le_three {n : ℕ} (hn : n ≤ 3) :
    higherPowerSource n = 0 := by
  rw [higherPowerSource]
  interval_cases n
  · rw [thetaSource_zero]; simp
  · rw [thetaSource_one]; simp
  · rw [thetaSource, if_pos Nat.prime_two,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    ring
  · rw [thetaSource, if_pos Nat.prime_three,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    ring

/-- **Below the aperture `log 4 / 2` the higher prime powers contribute nothing.** -/
theorem primeSide_higherPower_eq_zero (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h2r : 2 * r < Real.log 4) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        higherPowerSource n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n))) = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases h3 : n ≤ 3
  · rw [higherPowerSource_eq_zero_of_le_three h3, zero_mul]
  · have hn4 : (4:ℝ) ≤ n := by
      have : 4 ≤ n := by omega
      exact_mod_cast this
    have hlog : 2 * r ≤ Real.log (n : ℝ) :=
      le_trans (le_of_lt h2r) (Real.log_le_log (by norm_num) hn4)
    rw [autoCorrelation_eq_zero hF hr hsupp hlog, mul_zero, mul_zero]

/-- **Below that aperture `ζ`'s Weil form is the prime-only form.** -/
theorem primeSide_vonMangoldt_eq_theta (hF : Continuous F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) (h2r : 2 * r < Real.log 4) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = ∑ n ∈ Finset.range (N + 1),
          thetaSource n * (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) := by
  have hadd := primeSide_source_add thetaSource higherPowerSource F N
  have hzero := primeSide_higherPower_eq_zero hF hr hsupp h2r N
  have hcong : (∑ n ∈ Finset.range (N + 1), (thetaSource n + higherPowerSource n) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
      = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)) :=
    Finset.sum_congr rfl fun n _ => by rw [thetaSource_add_higherPower]
  rw [← hcong, hadd, hzero, add_zero]


/-! ### The unconditional rate, made explicit

Both trivial bounds together give an explicit envelope for the Chebyshev defect, and hence an
explicit unconditional bound for `ζ`'s whole Weil form in terms of the test's lag weight alone.
This is the rate `1` of the grading, written out: every positivity statement of the programme is
measured against it.  The prime-only source obeys the same envelope. -/

theorem abs_chebyshevTwoPoleDefect_le {s : ℝ} (hs : 0 ≤ s) :
    |chebyshevTwoPoleDefect s| ≤ Real.exp s + s + (Real.exp s + 1) * s := by
  have hup := lagChebyshev_le hs
  have hlow := lagChebyshev_nonneg s
  have hexp : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  rw [chebyshevTwoPoleDefect, twoPoleWeight, abs_le]
  constructor <;> linarith

/-- **The unconditional rate for `ζ`'s Weil form.** -/
theorem abs_weilForm_vonMangoldt_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ}
    (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (2 * (Real.sqrt n)⁻¹ * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2)|
      ≤ ∫ s in Ioi (0:ℝ),
          (Real.exp s + s + (Real.exp s + 1) * s) * |deriv (lagTestWeight F) s| := by
  refine abs_testBalance_source_le (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (by simp) (by simp) (by fun_prop) (fun s hs => ?_) hF hFc hr hsupp hN
  rw [← chebyshevTwoPoleDefect_eq_lagSourceDefect]
  exact abs_chebyshevTwoPoleDefect_le (le_of_lt hs)

theorem lagPrefix_thetaSource_nonneg (s : ℝ) : 0 ≤ lagPrefix thetaSource s := by
  rw [lagPrefix]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [thetaSource]
  by_cases hk : k.Prime
  · rw [if_pos hk]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.one_lt.le
    exact Real.log_nonneg hk1
  · rw [if_neg hk]

/-- The prime-only source obeys the same envelope. -/
theorem abs_lagSourceDefect_theta_le {s : ℝ} (hs : 0 ≤ s) :
    |lagSourceDefect thetaSource s| ≤ Real.exp s + s + (Real.exp s + 1) * s := by
  have hlow := lagPrefix_thetaSource_nonneg s
  have hup : lagPrefix thetaSource s ≤ (Real.exp s + 1) * s :=
    le_trans (lagPrefix_mono_of_le thetaSource_le_vonMangoldt s) (lagChebyshev_le hs)
  have hexp : (1:ℝ) ≤ Real.exp s := Real.one_le_exp hs
  rw [lagSourceDefect, twoPoleWeight, abs_le]
  constructor <;> linarith


/-! ### Reading at the wrong pole

Against a calibration at `ρ > 1` the Chebyshev count cannot keep up: its defect is at least
`(e^{ρs}−1)/ρ` minus an `O(s e^s)` term, so it grows like `e^{ρs}`.  The pole position is thus
pinned by the arithmetic at full strength, and the Weil form at any pole can be scored by a
majorant of the corresponding defect. -/

theorem integrableOn_Ioi_lagSourceDefectAt_mul_deriv (ρ : ℝ) (a : ℕ → ℝ)
    (hh : ContDiff ℝ 1 h) (hS : 0 < S) (hvan : ∀ s, S ≤ s → h s = 0) {N : ℕ}
    (hN : Real.exp S ≤ N) :
    IntegrableOn (fun s => lagSourceDefectAt ρ a s * deriv h s) (Ioi (0:ℝ)) := by
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have h1 : IntegrableOn (fun s => poleWeightAt ρ s * deriv h s) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing ((continuous_poleWeightAt ρ).mul hdc) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, mul_zero])
  refine (h1.sub (integrableOn_Ioi_lagPrefix_mul_deriv a hh hS hvan hN)).congr_fun
    (fun s _ => ?_) measurableSet_Ioi
  show poleWeightAt ρ s * deriv h s - lagPrefix a s * deriv h s
    = lagSourceDefectAt ρ a s * deriv h s
  rw [lagSourceDefectAt, sub_mul]

/-- **Scoring the Weil form at a pole by a majorant of the defect.** -/
theorem abs_testBalanceAt_source_le (ρ : ℝ) (hρ : ρ ≠ 0) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha1 : a 1 = 0) {G : ℝ → ℝ} (hGc : Continuous G)
    (hdef : ∀ s, 0 < s → |lagSourceDefectAt ρ a s| ≤ G s)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, r < |y| → F y = 0) {N : ℕ} (hN : Real.exp (2 * r) ≤ N) :
    |(∑ n ∈ Finset.range (N + 1), a n *
          (2 * (n : ℝ) ^ (-ρ / 2) * autoCorrelation F (Real.log n)))
        - 2 * ((∫ x, F x * Real.exp (-(ρ / 2 * x))) * ∫ x, F x * Real.exp (ρ / 2 * x))|
      ≤ ∫ s in Ioi (0:ℝ), G s * |deriv (lagTestWeightAt ρ F) s| := by
  have hS : (0:ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeightAt ρ F s = 0 := fun s hs => by
    rw [lagTestWeightAt, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hwc : Continuous (deriv (lagTestWeightAt ρ F)) :=
    (contDiff_one_lagTestWeightAt ρ hF hFc).continuous_deriv le_rfl
  have hintG : IntegrableOn (fun s => G s * |deriv (lagTestWeightAt ρ F) s|) (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_vanishing (hGc.mul hwc.abs) hS
      (fun s hs => by rw [deriv_eq_zero_of_vanishing hvan hs, abs_zero, mul_zero])
  have hintD : IntegrableOn
      (fun s => |lagSourceDefectAt ρ a s * deriv (lagTestWeightAt ρ F) s|) (Ioi (0:ℝ)) :=
    (integrableOn_Ioi_lagSourceDefectAt_mul_deriv ρ a
      (contDiff_one_lagTestWeightAt ρ hF hFc) hS hvan hN).abs
  have hpt : ∀ s ∈ Ioi (0:ℝ),
      |lagSourceDefectAt ρ a s * deriv (lagTestWeightAt ρ F) s|
        ≤ G s * |deriv (lagTestWeightAt ρ F) s| := by
    intro s hs
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hdef s hs) (abs_nonneg _)
  have hmono := MeasureTheory.setIntegral_mono_on hintD hintG measurableSet_Ioi hpt
  rw [testBalanceAt_source ρ hρ a ha0 ha1 hF hFc hr hsupp hN,
    setIntegral_congr_fun measurableSet_Ioi
      (fun s _ => by rw [deriv_lagTestWeightAt ρ hF hFc s] :
        ∀ s ∈ Ioi (0:ℝ), lagSourceDefectAt ρ a s *
            (2 * Real.exp (-(ρ * s) / 2)
              * (crossCorrelation F s - ρ / 2 * autoCorrelation F s))
          = lagSourceDefectAt ρ a s * deriv (lagTestWeightAt ρ F) s)]
  exact le_trans abs_integral_le_integral_abs hmono

/-- **Reading `ζ` at a pole beyond `1` costs a defect of order `e^{ρs}`.** -/
theorem lagSourceDefectAt_vonMangoldt_ge {ρ s : ℝ} (hs : 0 ≤ s) :
    (Real.exp (ρ * s) - 1) / ρ + s - (Real.exp s + 1) * s
      ≤ lagSourceDefectAt ρ (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s := by
  have hup := lagChebyshev_le hs
  rw [lagSourceDefectAt, poleWeightAt, ← lagChebyshev_eq_lagPrefix]
  linarith


/-! ### Pole covariance, window mass, and the hyperbola law

Three structural laws of the ledger.  First, the calibration weight is covariant under dilation of
the lag variable, which moves the pole, and the difference of two calibrations is independent of
the source: no ledger can be accurate at two distinct poles.  Second, the defect bound transfers
verbatim to the mass carried by a window.  Third, the prefix of a Dirichlet convolution is the
superposition of lag-translated prefixes of one factor weighted by the other -- the hyperbola
identity in lag coordinates -- so a calibration of one factor propagates to the convolution with
an `ℓ¹`-amplified error, and the Chebyshev ledger reads off the logarithm ledger. -/

/-- Dilating the lag variable by `λ` rescales the calibration weight and moves its pole from `ρ`
to `λρ`. -/
theorem poleWeightAt_dilate (rho lam s : ℝ) :
    poleWeightAt rho (lam * s) = lam * poleWeightAt (lam * rho) s := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp [poleWeightAt]
  rcases eq_or_ne rho 0 with rfl | hrho
  · simp [poleWeightAt]
  rw [poleWeightAt, poleWeightAt, show rho * (lam * s) = lam * rho * s by ring]
  field_simp

/-- **Pole-shift law**: moving the calibration pole changes every source's defect by the same
source-independent amount. -/
theorem lagSourceDefectAt_sub_lagSourceDefect (rho : ℝ) (a : ℕ → ℝ) (s : ℝ) :
    lagSourceDefectAt rho a s - lagSourceDefect a s
      = (Real.exp (rho * s) - 1) / rho - (Real.exp s - 1) := by
  simp only [lagSourceDefectAt, lagSourceDefect, poleWeightAt, twoPoleWeight]
  ring

/-- **Two-pole rigidity**: a ledger accurate to `C` against two calibrations pins the gap between
the two polar weights to `2C`.  Since the gap grows like `e^{ρ₁ s}` for `ρ₁ > ρ₂`, no source is
accurate at two distinct poles. -/
theorem abs_poleWeight_sub_le_of_two_poles (a : ℕ → ℝ) {rho1 rho2 s C : ℝ}
    (h1 : |lagSourceDefectAt rho1 a s| ≤ C) (h2 : |lagSourceDefectAt rho2 a s| ≤ C) :
    |(Real.exp (rho1 * s) - 1) / rho1 - (Real.exp (rho2 * s) - 1) / rho2| ≤ 2 * C := by
  have hkey : (Real.exp (rho1 * s) - 1) / rho1 - (Real.exp (rho2 * s) - 1) / rho2
      = lagSourceDefectAt rho1 a s - lagSourceDefectAt rho2 a s := by
    simp only [lagSourceDefectAt, poleWeightAt]; ring
  rw [hkey]
  calc |lagSourceDefectAt rho1 a s - lagSourceDefectAt rho2 a s|
      ≤ |lagSourceDefectAt rho1 a s| + |lagSourceDefectAt rho2 a s| := abs_sub _ _
    _ ≤ 2 * C := by linarith

/-- **Window mass law**: a defect bound at the two ends of a window controls the mass the ledger
carries inside it, to within `2C` of the polar prediction `e^t − e^s + (t − s)`. -/
theorem abs_window_mass_sub_le (a : ℕ → ℝ) {s t C : ℝ}
    (hs : |lagSourceDefect a s| ≤ C) (ht : |lagSourceDefect a t| ≤ C) :
    |(lagPrefix a t - lagPrefix a s) - (twoPoleWeight t - twoPoleWeight s)| ≤ 2 * C := by
  have hkey : (lagPrefix a t - lagPrefix a s) - (twoPoleWeight t - twoPoleWeight s)
      = lagSourceDefect a s - lagSourceDefect a t := by
    simp only [lagSourceDefect]; ring
  rw [hkey]
  calc |lagSourceDefect a s - lagSourceDefect a t|
      ≤ |lagSourceDefect a s| + |lagSourceDefect a t| := abs_sub _ _
    _ ≤ 2 * C := by linarith

/-- The window mass is the sum of the atoms the window actually contains. -/
theorem lagPrefix_sub_lagPrefix_eq_sum (a : ℕ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    lagPrefix a t - lagPrefix a s = ∑ n ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, a n := by
  have hfl : ⌊Real.exp s⌋₊ ≤ ⌊Real.exp t⌋₊ := Nat.floor_le_floor (Real.exp_le_exp.mpr hst)
  have hsub : Finset.Icc 0 ⌊Real.exp s⌋₊ ⊆ Finset.Icc 0 ⌊Real.exp t⌋₊ := by
    intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  have hdiff : Finset.Icc 0 ⌊Real.exp t⌋₊ \ Finset.Icc 0 ⌊Real.exp s⌋₊
      = Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊ := by
    ext k; simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [lagPrefix, lagPrefix, ← Finset.sum_sdiff hsub, hdiff]
  ring

/-- The atoms of a window carry the polar mass of the window up to twice the defect bound. -/
theorem abs_sum_Ioc_sub_le (a : ℕ → ℝ) {s t C : ℝ} (hst : s ≤ t)
    (hs : |lagSourceDefect a s| ≤ C) (ht : |lagSourceDefect a t| ≤ C) :
    |(∑ n ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, a n)
        - (Real.exp t - Real.exp s + (t - s))| ≤ 2 * C := by
  have hmass := abs_window_mass_sub_le a hs ht
  rw [lagPrefix_sub_lagPrefix_eq_sum a hst] at hmass
  have hw : twoPoleWeight t - twoPoleWeight s = Real.exp t - Real.exp s + (t - s) := by
    simp only [twoPoleWeight]; ring
  rwa [hw] at hmass

/-- The prefix of a source whose zeroth coefficient vanishes starts at index one. -/
theorem lagPrefix_eq_sum_Icc_one (b : ℕ → ℝ) (hb0 : b 0 = 0) (u : ℝ) :
    lagPrefix b u = ∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, b k := by
  rw [lagPrefix, show Finset.Icc 0 ⌊Real.exp u⌋₊ = insert 0 (Finset.Icc 1 ⌊Real.exp u⌋₊) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp), hb0, zero_add]

/-- Translating the lag variable by `log d` divides the horizon by `d`. -/
theorem floor_exp_sub_log (s : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    ⌊Real.exp (s - Real.log d)⌋₊ = ⌊Real.exp s⌋₊ / d := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
  rw [Real.exp_sub, Real.exp_log hd0, Nat.floor_div_natCast]

/-- Dirichlet convolution of two sources. -/
def dconv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ x ∈ n.divisorsAntidiagonal, a x.1 * b x.2

/-- The unit source of the Dirichlet algebra: the constant `1` off the origin. -/
def unitSource : ℕ → ℝ := fun n => if n = 0 then 0 else 1

theorem unitSource_zero : unitSource 0 = 0 := by simp [unitSource]

/-- Hyperbola swap for a Dirichlet convolution: each factorization `n = d·m` is counted once. -/
theorem sum_Icc_dconv (a b : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dconv a b n
      = ∑ d ∈ Finset.Icc 1 N, a d * ∑ m ∈ Finset.Icc 1 (N / d), b m := by
  have hexpand : ∑ n ∈ Finset.Icc 1 N, dconv a b n
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal), a x.2.1 * b x.2.2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun n _ => rfl
  have hcollapse : ∑ d ∈ Finset.Icc 1 N, a d * ∑ m ∈ Finset.Icc 1 (N / d), b m
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)), a x.1 * b x.2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun d _ => Finset.mul_sum ..
  rw [hexpand, hcollapse]
  apply Finset.sum_nbij' (i := fun x => ⟨x.2.1, x.2.2⟩) (j := fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hn, hdm⟩ := hx
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, hn0⟩ := hdm
    dsimp only at hprod hn0 hn ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    have hd0 : d ≠ 0 := by rintro rfl; rw [zero_mul] at hprod; omega
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hprod; omega
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · calc d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
        _ = n := hprod
        _ ≤ N := hn.2
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      calc m * d = n := by rw [mul_comm]; exact hprod
        _ ≤ N := hn.2
  · rintro ⟨d, m⟩ hy
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hy
    obtain ⟨hd, hm⟩ := hy
    dsimp only at hd hm ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    dsimp only
    have hdm : d * m ≤ N :=
      calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
        _ ≤ N := Nat.mul_div_le N d
    have hne : d * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    exact ⟨⟨by omega, hdm⟩, rfl, hne⟩
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hdm⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, -⟩ := hdm
    dsimp only at hprod ⊢
    subst hprod
    rfl
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨n, d, m⟩ _
    rfl

/-- **The hyperbola law in lag coordinates**: the ledger of a Dirichlet convolution is the
superposition of the lag-translated ledgers of one factor, weighted by the other.  Multiplicative
convolution becomes an additive translation average. -/
theorem lagPrefix_dconv (a b : ℕ → ℝ) (hb0 : b 0 = 0) (s : ℝ) :
    lagPrefix (dconv a b) s
      = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, a d * lagPrefix b (s - Real.log d) := by
  have hzero : dconv a b 0 = 0 := by simp [dconv, Nat.divisorsAntidiagonal_zero]
  rw [lagPrefix_eq_sum_Icc_one _ hzero s, sum_Icc_dconv]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [lagPrefix_eq_sum_Icc_one b hb0 (s - Real.log d), floor_exp_sub_log s hd.1]

/-- **Calibration propagates through convolution**: if one factor is calibrated by `w` to within
`C`, the convolution is calibrated by the superposed weight to within `C` times the `ℓ¹` mass of
the multiplier. -/
theorem abs_lagPrefix_dconv_sub_le (a b : ℕ → ℝ) (hb0 : b 0 = 0) {w : ℝ → ℝ} {C : ℝ}
    (hC : ∀ u, |lagPrefix b u - w u| ≤ C) (s : ℝ) :
    |lagPrefix (dconv a b) s
        - ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, a d * w (s - Real.log d)|
      ≤ C * ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, |a d| := by
  rw [lagPrefix_dconv a b hb0 s, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d _ => ?_)
  calc |a d * lagPrefix b (s - Real.log d) - a d * w (s - Real.log d)|
      = |a d| * |lagPrefix b (s - Real.log d) - w (s - Real.log d)| := by
        rw [← mul_sub, abs_mul]
    _ ≤ |a d| * C := mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
    _ = C * |a d| := mul_comm _ _

theorem lagPrefix_unitSource (u : ℝ) : lagPrefix unitSource u = (⌊Real.exp u⌋₊ : ℝ) := by
  have hone : ∀ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, unitSource k = 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [unitSource, if_neg (by omega : ¬ k = 0)]
  rw [lagPrefix_eq_sum_Icc_one unitSource unitSource_zero u,
    Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- The von Mangoldt source convolved with the unit source is the logarithm source. -/
theorem dconv_vonMangoldt_unitSource (n : ℕ) :
    dconv (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) unitSource n = Real.log n := by
  have hrw : dconv (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) unitSource n
      = (ArithmeticFunction.vonMangoldt
          * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [unitSource, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
  rw [hrw, ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply]

/-- **The Chebyshev ledger reads the logarithm ledger**: the prefix of `log` is the hyperbola
pairing of the von Mangoldt atoms against the horizon counts `⌊e^s/d⌋`. -/
theorem lagPrefix_log_eq_sum_vonMangoldt (s : ℝ) :
    lagPrefix (fun n : ℕ => Real.log n) s
      = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊,
          (ArithmeticFunction.vonMangoldt d : ℝ) * ((⌊Real.exp s⌋₊ / d : ℕ) : ℝ) := by
  have hfun : (fun n : ℕ => Real.log n)
      = dconv (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) unitSource :=
    funext fun n => (dconv_vonMangoldt_unitSource n).symm
  rw [hfun, lagPrefix_dconv _ _ unitSource_zero]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [lagPrefix_unitSource, floor_exp_sub_log s hd.1]


/-! ### Möbius inversion of the ledger

The unit source is calibrated by `e^u` to within one atom, so the hyperbola law turns a Dirichlet
convolution against it into the leading term `x·∑ a(d)/d`.  Inverting with the Möbius source
recovers any ledger from its summatory convolution, which specialises to the exact identities
`∑_{d ≤ x} μ(d)⌊x/d⌋ = 1`, `|∑_{d ≤ x} μ(d)/d| ≤ 1`, the divisor ledger `∑_{n ≤ x} τ(n) =
∑_{d ≤ x} ⌊x/d⌋`, and the closed form `ψ(x) = ∑_{d ≤ x} μ(d) log(⌊x/d⌋!)`. -/

/-- The unit source counts the horizon to within one atom. -/
theorem abs_lagPrefix_unitSource_sub_exp_le (u : ℝ) :
    |lagPrefix unitSource u - Real.exp u| ≤ 1 := by
  rw [lagPrefix_unitSource]
  have h1 : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have h2 : Real.exp u - 1 < (⌊Real.exp u⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  rw [abs_le]
  constructor <;> linarith

/-- **Leading term of a summatory convolution**: convolving with the unit source produces the
horizon times the Dirichlet tail, with error the `ℓ¹` mass of the multiplier. -/
theorem abs_lagPrefix_dconv_unitSource_sub_le (a : ℕ → ℝ) (s : ℝ) :
    |lagPrefix (dconv a unitSource) s
        - Real.exp s * ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, a d / d|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, |a d| := by
  have hmain := abs_lagPrefix_dconv_sub_le a unitSource unitSource_zero
    (w := Real.exp) (C := 1) abs_lagPrefix_unitSource_sub_exp_le s
  rw [one_mul] at hmain
  have hsum : ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, a d * Real.exp (s - Real.log d)
      = Real.exp s * ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, a d / d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd.1
    rw [Real.exp_sub, Real.exp_log hd0]
    field_simp
  rwa [hsum] at hmain

theorem sum_Icc_log_eq_log_factorial (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Real.log k = Real.log (Nat.factorial N) := by
  have hfac : ∏ i ∈ Finset.Icc 1 N, i = Nat.factorial N := by
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
        ring
  have hprod : ((Nat.factorial N : ℕ) : ℝ) = ∏ i ∈ Finset.Icc 1 N, (i : ℝ) := by
    rw [← Nat.cast_prod, hfac]
  rw [hprod, Real.log_prod (fun i hi => by
    rw [Finset.mem_Icc] at hi
    exact Nat.cast_ne_zero.mpr (by omega))]

/-- The logarithm ledger is the logarithm of the factorial of the horizon. -/
theorem lagPrefix_log_eq_log_factorial (s : ℝ) :
    lagPrefix (fun n : ℕ => Real.log n) s = Real.log (Nat.factorial ⌊Real.exp s⌋₊) := by
  rw [lagPrefix_eq_sum_Icc_one _ (by simp) s, sum_Icc_log_eq_log_factorial]

/-- Hyperbola swap against a weight evaluated at the product. -/
theorem sum_Icc_dconv_mul (a b f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dconv a b n * f n
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), a d * b m * f (d * m) := by
  have hexpand : ∑ n ∈ Finset.Icc 1 N, dconv a b n * f n
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal),
          a x.2.1 * b x.2.2 * f x.1 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun n _ => by rw [dconv, Finset.sum_mul]
  have hcollapse : ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), a d * b m * f (d * m)
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
          a x.1 * b x.2 * f (x.1 * x.2) := by
    rw [Finset.sum_sigma]
  rw [hexpand, hcollapse]
  apply Finset.sum_nbij' (i := fun x => ⟨x.2.1, x.2.2⟩) (j := fun y => ⟨y.1 * y.2, (y.1, y.2)⟩)
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hn, hdm⟩ := hx
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, hn0⟩ := hdm
    dsimp only at hprod hn0 hn ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
    dsimp only
    have hd0 : d ≠ 0 := by rintro rfl; rw [zero_mul] at hprod; omega
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hprod; omega
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · calc d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
        _ = n := hprod
        _ ≤ N := hn.2
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      calc m * d = n := by rw [mul_comm]; exact hprod
        _ ≤ N := hn.2
  · rintro ⟨d, m⟩ hy
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hy
    obtain ⟨hd, hm⟩ := hy
    dsimp only at hd hm ⊢
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    dsimp only
    have hdm : d * m ≤ N :=
      calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
        _ ≤ N := Nat.mul_div_le N d
    have hne : d * m ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    exact ⟨⟨by omega, hdm⟩, rfl, hne⟩
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hdm⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, -⟩ := hdm
    dsimp only at hprod ⊢
    subst hprod
    rfl
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨n, d, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hdm⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal] at hdm
    obtain ⟨hprod, -⟩ := hdm
    dsimp only at hprod ⊢
    subst hprod
    rfl

/-- **The pairing of a convolution lives on the product lattice**: testing a Dirichlet convolution
against a lag weight is the double sum of the weight at the sums of the lags. -/
theorem sum_lag_dconv (a b : ℕ → ℝ) (A : ℝ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dconv a b n * A (Real.log n)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          a d * b m * A (Real.log d + Real.log m) := by
  rw [sum_Icc_dconv_mul a b (fun n => A (Real.log n)) N]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hd hm
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_mul, Real.log_mul hd0 hm0]

theorem dconv_eq_mul_apply (F G : ArithmeticFunction ℝ) (n : ℕ) :
    dconv (fun k => F k) (fun k => G k) n = (F * G) n := (ArithmeticFunction.mul_apply).symm

theorem unitSource_eq_zeta :
    unitSource = fun k => (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) k := by
  funext k
  simp [unitSource, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]

/-- The Möbius source including its unit atom: the Dirichlet inverse of the unit source. -/
def fullMoebius : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)

theorem fullMoebius_zero : fullMoebius 0 = 0 := by simp [fullMoebius]

theorem abs_fullMoebius_le_one (n : ℕ) : |fullMoebius n| ≤ 1 := by
  rcases Int.abs_le_one_iff.mp (ArithmeticFunction.abs_moebius_le_one (n := n)) with h | h | h <;>
    simp [fullMoebius, h]

theorem fullMoebius_eq_moebius :
    fullMoebius = fun k => (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) k := by
  funext k
  simp [fullMoebius, ArithmeticFunction.intCoe_apply]

theorem one_le_floor_exp {s : ℝ} (hs : 0 ≤ s) : 1 ≤ ⌊Real.exp s⌋₊ :=
  Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp hs)

/-- **The Möbius ledger is exactly one**: the horizon counts weighted by `μ` collapse. -/
theorem sum_fullMoebius_floor {s : ℝ} (hs : 0 ≤ s) :
    ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊,
        fullMoebius d * ((⌊Real.exp s⌋₊ / d : ℕ) : ℝ) = 1 := by
  have hdc : dconv fullMoebius unitSource = fun n => if n = 1 then 1 else 0 := by
    funext n
    rw [fullMoebius_eq_moebius, unitSource_eq_zeta, dconv_eq_mul_apply,
      ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  have hL : lagPrefix (dconv fullMoebius unitSource) s = 1 := by
    rw [hdc, lagPrefix, Finset.sum_ite_eq' (Finset.Icc 0 ⌊Real.exp s⌋₊) 1 (fun _ => (1:ℝ)),
      if_pos (by rw [Finset.mem_Icc]; exact ⟨Nat.zero_le _, one_le_floor_exp hs⟩)]
  rw [lagPrefix_dconv fullMoebius unitSource unitSource_zero s] at hL
  rw [← hL]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [lagPrefix_unitSource, floor_exp_sub_log s hd.1]

/-- **The Möbius Dirichlet tail is bounded by one**, uniformly in the horizon. -/
theorem abs_sum_fullMoebius_div_le_one {s : ℝ} (hs : 0 ≤ s) :
    |∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, fullMoebius d / d| ≤ 1 := by
  set N := ⌊Real.exp s⌋₊ with hN
  have hN1 : 1 ≤ N := one_le_floor_exp hs
  have hid := sum_fullMoebius_floor hs
  rw [← hN] at hid
  set T : ℝ := ∑ d ∈ Finset.Icc 1 N, fullMoebius d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hT
  have hsplit : (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, fullMoebius d / d) = 1 + T := by
    rw [hT, Finset.mul_sum, ← hid, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd.1
    field_simp
    ring
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hterm : ∀ d ∈ Finset.Icc 2 N,
      |fullMoebius d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| ≤ 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hd.1
    have hfl : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hd0]
      exact_mod_cast Nat.div_mul_le_self N d
    have hfl2 : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have hsub := Nat.sub_one_lt_floor ((N : ℝ) / d)
      rwa [Nat.floor_div_natCast, Nat.floor_natCast] at hsub
    rw [abs_mul]
    calc |fullMoebius d| * |(N : ℝ) / d - ((N / d : ℕ) : ℝ)|
        ≤ 1 * 1 := by
          refine mul_le_mul (abs_fullMoebius_le_one d) ?_ (abs_nonneg _) zero_le_one
          rw [abs_le]; constructor <;> linarith
      _ = 1 := one_mul 1
  have hone : fullMoebius 1 * ((N : ℝ) / ((1 : ℕ) : ℝ) - ((N / 1 : ℕ) : ℝ)) = 0 := by
    norm_num
  have hTbound : |T| ≤ (N : ℝ) - 1 := by
    rw [hT, hins, Finset.sum_insert (by simp), hone, zero_add]
    calc |∑ d ∈ Finset.Icc 2 N, fullMoebius d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 2 N, |fullMoebius d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 2 N, (1:ℝ) := Finset.sum_le_sum hterm
      _ = (N : ℝ) - 1 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
            show N + 1 - 2 = N - 1 from by omega, Nat.cast_sub hN1, Nat.cast_one]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  rw [abs_le]
  constructor
  · nlinarith [abs_le.mp hTbound |>.1, abs_le.mp hTbound |>.2]
  · nlinarith [abs_le.mp hTbound |>.1, abs_le.mp hTbound |>.2]

/-- **Closed form of the Chebyshev ledger**: `ψ(x) = ∑_{d ≤ x} μ(d) log(⌊x/d⌋!)`. -/
theorem lagChebyshev_eq_sum_fullMoebius_log_factorial (s : ℝ) :
    lagChebyshev s = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊,
        fullMoebius d * Real.log (Nat.factorial (⌊Real.exp s⌋₊ / d)) := by
  have hlog : (fun n : ℕ => Real.log n)
      = fun k => (ArithmeticFunction.log : ArithmeticFunction ℝ) k :=
    funext fun k => (ArithmeticFunction.log_apply).symm
  have hdc : dconv fullMoebius (fun n : ℕ => Real.log n)
      = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
    funext n
    rw [fullMoebius_eq_moebius, hlog, dconv_eq_mul_apply,
      show ((↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          = ArithmeticFunction.log * (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) from
        mul_comm _ _,
      ArithmeticFunction.log_mul_moebius_eq_vonMangoldt]
  have hmain := lagPrefix_dconv fullMoebius (fun n : ℕ => Real.log n) (by simp) s
  rw [hdc] at hmain
  rw [lagChebyshev_eq_lagPrefix, hmain]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [lagPrefix_log_eq_log_factorial, floor_exp_sub_log s hd.1]

/-- **Möbius inversion of the ledger**: every source is recovered from its summatory convolution
by Möbius-weighted lag translations. -/
theorem lagPrefix_eq_sum_fullMoebius_dconv (a : ℕ → ℝ) (ha0 : a 0 = 0) (s : ℝ) :
    lagPrefix a s = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊,
        fullMoebius d * lagPrefix (dconv a unitSource) (s - Real.log d) := by
  have hb0 : dconv a unitSource 0 = 0 := by simp [dconv]
  obtain ⟨A, hA⟩ : ∃ A : ArithmeticFunction ℝ, a = fun k => A k := ⟨⟨a, ha0⟩, rfl⟩
  have key : dconv fullMoebius (dconv a unitSource) = a := by
    have h1 : dconv a unitSource
        = fun k => (A * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k := by
      funext k
      rw [hA, unitSource_eq_zeta, dconv_eq_mul_apply]
    funext n
    rw [h1, fullMoebius_eq_moebius, dconv_eq_mul_apply,
      show ((↑ArithmeticFunction.moebius : ArithmeticFunction ℝ)
            * (A * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)))
          = A * ((↑ArithmeticFunction.moebius : ArithmeticFunction ℝ)
            * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) from by ring,
      ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one, hA]
  conv_lhs => rw [← key]
  rw [lagPrefix_dconv fullMoebius (dconv a unitSource) hb0 s]

/-- The Möbius source of the Mertens ledger is the full Möbius source with its unit atom removed. -/
theorem fullMoebius_eq_moebiusSource_add (n : ℕ) :
    fullMoebius n = moebiusSource n + (if n = 1 then 1 else 0) := by
  match n with
  | 0 => simp [fullMoebius, moebiusSource]
  | 1 => simp [fullMoebius, moebiusSource]
  | (k + 2) => simp [fullMoebius, moebiusSource]

/-- Past the first atom the two Möbius ledgers differ by exactly the unit atom. -/
theorem lagPrefix_fullMoebius {s : ℝ} (hs : 0 ≤ s) :
    lagPrefix fullMoebius s = lagMertens s + 1 := by
  rw [lagMertens, lagPrefix, lagPrefix,
    Finset.sum_congr rfl (fun k _ => fullMoebius_eq_moebiusSource_add k),
    Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Icc 0 ⌊Real.exp s⌋₊) 1 (fun _ => (1:ℝ)),
    if_pos (by rw [Finset.mem_Icc]; exact ⟨Nat.zero_le _, one_le_floor_exp hs⟩)]

theorem card_divisorsAntidiagonal (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

theorem dconv_unitSource_self (n : ℕ) :
    dconv unitSource unitSource n = (n.divisors.card : ℝ) := by
  have hone : ∀ x ∈ n.divisorsAntidiagonal, unitSource x.1 * unitSource x.2 = 1 := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hx; exact hx.2 hx.1.symm
    have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; exact hx.2 hx.1.symm
    simp [unitSource, h1, h2]
  rw [dconv, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_divisorsAntidiagonal]

/-- **The divisor ledger is the sum of the horizon counts**: `∑_{n ≤ x} τ(n) = ∑_{d ≤ x} ⌊x/d⌋`. -/
theorem lagPrefix_divisorCount (s : ℝ) :
    lagPrefix (fun n : ℕ => (n.divisors.card : ℝ)) s
      = ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, ((⌊Real.exp s⌋₊ / d : ℕ) : ℝ) := by
  have hdc : dconv unitSource unitSource = fun n : ℕ => (n.divisors.card : ℝ) :=
    funext dconv_unitSource_self
  have hmain := lagPrefix_dconv unitSource unitSource unitSource_zero s
  rw [hdc] at hmain
  rw [hmain]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [lagPrefix_unitSource, floor_exp_sub_log s hd.1,
    show unitSource d = 1 from by simp only [unitSource, if_neg (by omega : ¬ d = 0)], one_mul]

/-- The divisor ledger is the harmonic ledger times the horizon, to within the horizon. -/
theorem abs_lagPrefix_divisorCount_sub_le (s : ℝ) :
    |lagPrefix (fun n : ℕ => (n.divisors.card : ℝ)) s
        - Real.exp s * ∑ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, (1:ℝ) / d|
      ≤ (⌊Real.exp s⌋₊ : ℝ) := by
  have hdc : dconv unitSource unitSource = fun n : ℕ => (n.divisors.card : ℝ) :=
    funext dconv_unitSource_self
  have hmain := abs_lagPrefix_dconv_unitSource_sub_le unitSource s
  rw [hdc] at hmain
  have hdiv : ∀ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, unitSource d / d = (1:ℝ) / d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [show unitSource d = 1 from by simp only [unitSource, if_neg (by omega : ¬ d = 0)]]
  have habs : ∀ d ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, |unitSource d| = 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [show unitSource d = 1 from by simp only [unitSource, if_neg (by omega : ¬ d = 0)],
      abs_one]
  rw [Finset.sum_congr rfl hdiv, Finset.sum_congr rfl habs, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, mul_one] at hmain
  simpa using hmain

/-! ### The Euler comb ledger

A squarefree comb `F − λF(· + a)` acts on the lag ledger as the second-order difference
`A ↦ (1+λ²)A − λ(A(· − a) + A(· + a))`, and after normalisation by `1 + λ²` this is the Euler
transform at weight `w = 2λ/(1+λ²)`.  The transform maps autocorrelations to autocorrelations, so
iterating it over a finite family of lags and reading the result at the origin telescopes into a
payment law: the first-power charge of each lag, measured in the ledger transformed by its
predecessors, is paid in full by the mass.  The admissible weights are exactly `w ≤ 1`, and every
prime-power Euler weight `Λ(n)/√n ≤ 2/e` is admissible, so the comb of a squarefree modulus can be
tuned to the prime side.  For two lags the price of the payment is explicit: the charges at the
ratio and product lags of the pair. -/

theorem autoCorrelation_const_mul (c : ℝ) (H : ℝ → ℝ) (t : ℝ) :
    autoCorrelation (fun x => c * H x) t = c ^ 2 * autoCorrelation H t := by
  rw [autoCorrelation, autoCorrelation, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show c * H x * (c * H (x + t)) = c ^ 2 * (H x * H (x + t))
  ring

/-- **The Euler factor is a second-order difference on the ledger.**  The comb `F − λF(· + a)`
has autocorrelation `(1+λ²)A − λ(A(· − a) + A(· + a))`. -/
theorem autoCorrelation_eulerFactor (hF : Continuous F) (hFc : HasCompactSupport F)
    (lam a t : ℝ) :
    autoCorrelation (fun x => F x - lam * F (x + a)) t
      = (1 + lam ^ 2) * autoCorrelation F t
        - lam * (autoCorrelation F (t - a) + autoCorrelation F (t + a)) := by
  have key : ∀ u v : ℝ, (∫ x, F (x + u) * F (x + v)) = autoCorrelation F (v - u) := by
    intro u v
    rw [autoCorrelation, ← MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure ℝ)) (fun x => F x * F (x + (v - u))) u]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F (x + u) * F (x + v) = F (x + u) * F (x + u + (v - u))
    rw [show x + u + (v - u) = x + v by ring]
  have h1 := integrable_shift_mul hF hFc 0 t
  have h2 := integrable_shift_mul hF hFc 0 (t + a)
  have h3 := integrable_shift_mul hF hFc a t
  have h4 := integrable_shift_mul hF hFc a (t + a)
  rw [autoCorrelation]
  have hexp : ∀ x, (F x - lam * F (x + a)) * (F (x + t) - lam * F (x + t + a))
      = F (x + 0) * F (x + t) + lam ^ 2 * (F (x + a) * F (x + (t + a)))
        - (lam * (F (x + 0) * F (x + (t + a))) + lam * (F (x + a) * F (x + t))) := by
    intro x
    rw [show x + t + a = x + (t + a) by ring, add_zero]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have e1 : (∫ x, (F (x + 0) * F (x + t) + lam ^ 2 * (F (x + a) * F (x + (t + a)))
        - (lam * (F (x + 0) * F (x + (t + a))) + lam * (F (x + a) * F (x + t)))))
      = (∫ x, (F (x + 0) * F (x + t) + lam ^ 2 * (F (x + a) * F (x + (t + a)))))
        - ∫ x, (lam * (F (x + 0) * F (x + (t + a))) + lam * (F (x + a) * F (x + t))) :=
    MeasureTheory.integral_sub (h1.add (h4.const_mul _)) ((h2.const_mul _).add (h3.const_mul _))
  have e2 : (∫ x, (F (x + 0) * F (x + t) + lam ^ 2 * (F (x + a) * F (x + (t + a)))))
      = (∫ x, F (x + 0) * F (x + t)) + ∫ x, lam ^ 2 * (F (x + a) * F (x + (t + a))) :=
    MeasureTheory.integral_add h1 (h4.const_mul _)
  have e3 : (∫ x, (lam * (F (x + 0) * F (x + (t + a))) + lam * (F (x + a) * F (x + t))))
      = (∫ x, lam * (F (x + 0) * F (x + (t + a)))) + ∫ x, lam * (F (x + a) * F (x + t)) :=
    MeasureTheory.integral_add (h2.const_mul _) (h3.const_mul _)
  have e4 : (∫ x, lam ^ 2 * (F (x + a) * F (x + (t + a))))
      = lam ^ 2 * ∫ x, F (x + a) * F (x + (t + a)) := MeasureTheory.integral_const_mul _ _
  have e5 : (∫ x, lam * (F (x + 0) * F (x + (t + a))))
      = lam * ∫ x, F (x + 0) * F (x + (t + a)) := MeasureTheory.integral_const_mul _ _
  have e6 : (∫ x, lam * (F (x + a) * F (x + t)))
      = lam * ∫ x, F (x + a) * F (x + t) := MeasureTheory.integral_const_mul _ _
  rw [e1, e2, e3, e4, e5, e6, key 0 t, key a (t + a), key 0 (t + a), key a t,
    show t - 0 = t by ring, show t + a - 0 = t + a by ring, show t + a - a = t by ring]
  ring

/-- The comb weight realizing the Euler weight `w ∈ (0,1]`. -/
def eulerLam (w : ℝ) : ℝ := (1 - Real.sqrt (1 - w ^ 2)) / w

theorem eulerLam_spec {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) :
    2 * eulerLam w / (1 + eulerLam w ^ 2) = w := by
  have hsq : (0:ℝ) ≤ 1 - w ^ 2 := by nlinarith
  set u := Real.sqrt (1 - w ^ 2) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hsq
  have hult : u < 1 := by nlinarith
  have hne : (1:ℝ) - u ≠ 0 := by linarith
  have hlam : eulerLam w = (1 - u) / w := rfl
  rw [hlam, div_pow]
  have h1 : 1 + (1 - u) ^ 2 / w ^ 2 = 2 * (1 - u) / w ^ 2 := by
    field_simp
    nlinarith
  rw [h1]
  field_simp

/-- **The comb cannot pay more than the mass**: every weight it realizes is at most one. -/
theorem two_mul_div_one_add_sq_le_one (lam : ℝ) : 2 * lam / (1 + lam ^ 2) ≤ 1 := by
  have hpos : (0:ℝ) < 1 + lam ^ 2 := by positivity
  rw [div_le_one hpos]
  nlinarith [sq_nonneg (lam - 1)]

/-- The normalized Euler transform of a lag ledger at weight `w` and lag `a`. -/
def eulerStep (w a : ℝ) (A : ℝ → ℝ) : ℝ → ℝ :=
  fun t => A t - (w / 2) * (A (t - a) + A (t + a))

theorem eulerStep_even {A : ℝ → ℝ} (hA : ∀ t, A (-t) = A t) (w a : ℝ) (t : ℝ) :
    eulerStep w a A (-t) = eulerStep w a A t := by
  rw [eulerStep, eulerStep, show -t - a = -(t + a) by ring, show -t + a = -(t - a) by ring,
    hA, hA, hA]
  ring

/-- One normalized factor of the Euler comb. -/
def eulerFactorFun (w a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (Real.sqrt (1 + eulerLam w ^ 2))⁻¹ * (F x - eulerLam w * F (x + a))

theorem eulerLam_zero : eulerLam 0 = 0 := by simp [eulerLam]

theorem continuous_eulerFactorFun (hF : Continuous F) (w a : ℝ) :
    Continuous (eulerFactorFun w a F) :=
  continuous_const.mul (hF.sub (continuous_const.mul
    (hF.comp (continuous_id.add continuous_const))))

theorem hasCompactSupport_eulerFactorFun (hFc : HasCompactSupport F) (w a : ℝ) :
    HasCompactSupport (eulerFactorFun w a F) :=
  (hFc.sub ((hFc.comp_homeomorph (Homeomorph.addRight a)).mul_left)).mul_left

/-- **The Euler transform is the correlation of one comb factor.** -/
theorem autoCorrelation_eulerFactorFun (hF : Continuous F) (hFc : HasCompactSupport F)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (a : ℝ) :
    autoCorrelation (eulerFactorFun w a F) = eulerStep w a (autoCorrelation F) := by
  rcases eq_or_lt_of_le hw0 with rfl | hw
  · have hid : eulerFactorFun 0 a F = F := by
      funext x
      rw [eulerFactorFun, eulerLam_zero]
      simp
    rw [hid]
    funext t
    simp [eulerStep]
  have hlam := eulerLam_spec hw hw1
  set lam := eulerLam w with hlamdef
  have hpos : (0:ℝ) < 1 + lam ^ 2 := by positivity
  have hc2 : ((Real.sqrt (1 + lam ^ 2))⁻¹) ^ 2 = (1 + lam ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos.le]
  funext t
  have hhalf : lam / (1 + lam ^ 2) = w / 2 := by rw [← hlam]; ring
  have hrw : eulerFactorFun w a F
      = fun x => (Real.sqrt (1 + lam ^ 2))⁻¹ * (F x - lam * F (x + a)) := rfl
  rw [hrw, autoCorrelation_const_mul, autoCorrelation_eulerFactor hF hFc, hc2, eulerStep]
  have expand : (1 + lam ^ 2)⁻¹ * ((1 + lam ^ 2) * autoCorrelation F t
      - lam * (autoCorrelation F (t - a) + autoCorrelation F (t + a)))
      = autoCorrelation F t
        - lam / (1 + lam ^ 2) * (autoCorrelation F (t - a) + autoCorrelation F (t + a)) := by
    field_simp
  rw [expand, hhalf]

/-- **The Euler transform preserves the autocorrelation cone.** -/
theorem exists_autoCorrelation_eulerStep (hF : Continuous F) (hFc : HasCompactSupport F)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (a : ℝ) :
    ∃ G : ℝ → ℝ, Continuous G ∧ HasCompactSupport G ∧
      autoCorrelation G = eulerStep w a (autoCorrelation F) :=
  ⟨eulerFactorFun w a F, continuous_eulerFactorFun hF w a,
    hasCompactSupport_eulerFactorFun hFc w a, autoCorrelation_eulerFactorFun hF hFc hw0 hw1 a⟩

/-- The ledger after a finite list of Euler transforms. -/
def eulerLedger : List (ℝ × ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | [], A => A
  | (w, a) :: L, A => eulerLedger L (eulerStep w a A)

/-- The total charge paid along the list: each lag in the ledger of its predecessors. -/
def eulerPayment : List (ℝ × ℝ) → (ℝ → ℝ) → ℝ
  | [], _ => 0
  | (w, a) :: L, A => w * A a + eulerPayment L (eulerStep w a A)

/-- The transformed ledger at the origin is the mass minus the payment. -/
theorem eulerLedger_zero_eq : ∀ (L : List (ℝ × ℝ)) {A : ℝ → ℝ}, (∀ t, A (-t) = A t) →
    eulerLedger L A 0 = A 0 - eulerPayment L A := by
  intro L
  induction L with
  | nil => intro A _; simp [eulerLedger, eulerPayment]
  | cons p L ih =>
      intro A hA
      obtain ⟨w, a⟩ := p
      rw [eulerLedger, eulerPayment, ih (eulerStep_even hA w a)]
      have h0 : eulerStep w a A 0 = A 0 - w * A a := by
        rw [eulerStep, zero_sub, zero_add, hA]
        ring
      rw [h0]
      ring

theorem eulerLedger_autoCorrelation_nonneg : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, Continuous H →
    HasCompactSupport H → (∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) →
    0 ≤ eulerLedger L (autoCorrelation H) 0 := by
  intro L
  induction L with
  | nil => intro H _ _ _; exact autoCorrelation_zero_nonneg H
  | cons p L ih =>
      intro H hH hHc hL
      obtain ⟨w, a⟩ := p
      obtain ⟨hw0, hw1⟩ := hL (w, a) (List.mem_cons_self ..)
      obtain ⟨G, hG, hGc, hGeq⟩ := exists_autoCorrelation_eulerStep hH hHc hw0 hw1 a
      rw [eulerLedger, ← hGeq]
      exact ih hG hGc (fun q hq => hL q (List.mem_cons_of_mem _ hq))

/-- **Sequential first-power payment.**  Along any finite list of lags with weights in `[0,1]`,
the charges measured in the successively transformed ledger are paid in full by the mass. -/
theorem eulerPayment_le_mass (hF : Continuous F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    eulerPayment L (autoCorrelation F) ≤ autoCorrelation F 0 := by
  have h1 := eulerLedger_autoCorrelation_nonneg L hF hFc hL
  have h2 := eulerLedger_zero_eq L (A := autoCorrelation F) (autoCorrelation_neg F)
  linarith

theorem eulerPayment_pair (A : ℝ → ℝ) (w1 a1 w2 a2 : ℝ) :
    eulerPayment [(w1, a1), (w2, a2)] A
      = w1 * A a1 + w2 * (A a2 - w1 / 2 * (A (a2 - a1) + A (a2 + a1))) := by
  simp [eulerPayment, eulerStep]

/-- **The ratio–product price of a two-lag payment.**  Paying two first-power charges costs the
charges at the ratio lag `a₂ − a₁` and the product lag `a₂ + a₁` of the pair. -/
theorem two_lag_payment_le (hF : Continuous F) (hFc : HasCompactSupport F)
    {w1 w2 a1 a2 : ℝ} (h1 : 0 ≤ w1) (h1' : w1 ≤ 1) (h2 : 0 ≤ w2) (h2' : w2 ≤ 1) :
    w1 * autoCorrelation F a1 + w2 * autoCorrelation F a2
      ≤ autoCorrelation F 0
        + w1 * w2 / 2 * (autoCorrelation F (a2 - a1) + autoCorrelation F (a2 + a1)) := by
  have hmain := eulerPayment_le_mass hF hFc [(w1, a1), (w2, a2)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨h1, h1'⟩
    · exact ⟨h2, h2'⟩)
  rw [eulerPayment_pair] at hmain
  nlinarith [hmain]

theorem log_le_div_exp_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := x / Real.exp 1) (by positivity)
  rw [Real.log_div (ne_of_gt hx) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- **Every prime-power Euler weight is admissible**: `Λ(n)/√n ≤ 2/e < 1`. -/
theorem vonMangoldtAtom_le_one (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlog : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have hsq : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt (by linarith)]
    ring
  have hle := log_le_div_exp_one hs
  rw [div_le_one hs]
  have hstep : 2 * Real.log (Real.sqrt n) ≤ 2 * (Real.sqrt n / Real.exp 1) := by linarith
  have hfin : 2 * (Real.sqrt n / Real.exp 1) ≤ Real.sqrt n := by
    rw [mul_div_assoc'] at hstep ⊢
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.exp 1)]
    nlinarith
  linarith [hlog, hsq ▸ hlog]

/-- **The prime side is payable by the comb**: the Euler weights of any finite list of
prime powers form an admissible weight list. -/
theorem eulerPayment_vonMangoldt_le_mass (hF : Continuous F) (hFc : HasCompactSupport F)
    (ns : List ℕ) :
    eulerPayment (ns.map fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n,
        Real.log n)) (autoCorrelation F) ≤ autoCorrelation F 0 := by
  refine eulerPayment_le_mass hF hFc _ ?_
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨n, -, rfl⟩ := hp
  exact ⟨div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _),
    vonMangoldtAtom_le_one n⟩

/-! ### The residual of the payment

The payment law is never tight.  Its deficit is the energy of the comb itself, and a comb factor
at a nonzero lag annihilates no compactly supported test but zero, so a nonzero test always keeps
a positive residual.  Unlike the Euler envelope of a prime tower, which a resonant train attains,
the payment law therefore carries information on every test. -/

/-- The Euler comb of a finite list of weighted lags. -/
def eulerComb : List (ℝ × ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | [], F => F
  | (w, a) :: L, F => eulerComb L (eulerFactorFun w a F)

theorem continuous_eulerComb : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, Continuous H →
    Continuous (eulerComb L H) := by
  intro L
  induction L with
  | nil => intro H hH; exact hH
  | cons p L ih =>
      intro H hH
      obtain ⟨w, a⟩ := p
      exact ih (continuous_eulerFactorFun hH w a)

theorem hasCompactSupport_eulerComb : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, HasCompactSupport H →
    HasCompactSupport (eulerComb L H) := by
  intro L
  induction L with
  | nil => intro H hH; exact hH
  | cons p L ih =>
      intro H hH
      obtain ⟨w, a⟩ := p
      exact ih (hasCompactSupport_eulerFactorFun hH w a)

theorem autoCorrelation_eulerComb : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, Continuous H →
    HasCompactSupport H → (∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) →
    autoCorrelation (eulerComb L H) = eulerLedger L (autoCorrelation H) := by
  intro L
  induction L with
  | nil => intro H _ _ _; rfl
  | cons p L ih =>
      intro H hH hHc hL
      obtain ⟨w, a⟩ := p
      obtain ⟨hw0, hw1⟩ := hL (w, a) (List.mem_cons_self ..)
      rw [eulerComb, eulerLedger,
        ih (continuous_eulerFactorFun hH w a) (hasCompactSupport_eulerFactorFun hHc w a)
          (fun q hq => hL q (List.mem_cons_of_mem _ hq)),
        autoCorrelation_eulerFactorFun hH hHc hw0 hw1 a]

/-- **The residual of the payment is the energy of the comb.** -/
theorem eulerPayment_residual (hF : Continuous F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    autoCorrelation F 0 - eulerPayment L (autoCorrelation F) = ∫ x, eulerComb L F x ^ 2 := by
  have h1 := eulerLedger_zero_eq L (A := autoCorrelation F) (autoCorrelation_neg F)
  have h2 := autoCorrelation_eulerComb L hF hFc hL
  rw [← h1, ← h2, autoCorrelation_zero_eq]

theorem exists_radius_of_hasCompactSupport (hFc : HasCompactSupport F) :
    ∃ r : ℝ, ∀ y, r < |y| → F y = 0 := by
  obtain ⟨r, hr⟩ := (hFc.isCompact.isBounded).subset_closedBall (0 : ℝ)
  refine ⟨r, fun y hy => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have hmem' := hr hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem'
  linarith

/-- A compactly supported solution of `H = λ H(· + a)` at a nonzero lag vanishes. -/
theorem eq_zero_of_eq_const_mul_shift {H : ℝ → ℝ} {lam a : ℝ} (ha : a ≠ 0) {r : ℝ}
    (hsupp : ∀ y, r < |y| → H y = 0) (heq : ∀ x, H x = lam * H (x + a)) : H = 0 := by
  have hiter : ∀ (n : ℕ) (x : ℝ), H x = lam ^ n * H (x + n * a) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [ih x, heq (x + k * a)]
        push_cast
        rw [show x + k * a + a = x + (k + 1) * a by ring]
        ring
  funext x
  have ha0 : 0 < |a| := abs_pos.mpr ha
  obtain ⟨n, hn⟩ := exists_nat_gt ((r + |x|) / |a|)
  have hbig : r < |x + n * a| := by
    have h1 : (r + |x|) < n * |a| := by
      rw [div_lt_iff₀ ha0] at hn
      linarith
    have h2 : |(n : ℝ) * a| ≤ |x + (n:ℝ) * a| + |x| := by
      calc |(n : ℝ) * a| = |(x + (n:ℝ) * a) - x| := by
            rw [show (x + (n:ℝ) * a) - x = (n:ℝ) * a by ring]
        _ ≤ |x + (n:ℝ) * a| + |x| := abs_sub _ _
    rw [abs_mul, Nat.abs_cast] at h2
    linarith
  rw [hiter n x, hsupp _ hbig, mul_zero]
  rfl

theorem eulerFactorFun_ne_zero (hFc : HasCompactSupport F) (hF0 : F ≠ 0) (w : ℝ) {a : ℝ}
    (ha : a ≠ 0) : eulerFactorFun w a F ≠ 0 := by
  intro hzero
  set lam := eulerLam w with hlamdef
  have hpos : (0:ℝ) < 1 + lam ^ 2 := by positivity
  have hc : (Real.sqrt (1 + lam ^ 2))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have heq : ∀ x, F x = lam * F (x + a) := by
    intro x
    have hx := congrFun hzero x
    rw [show eulerFactorFun w a F
        = fun x => (Real.sqrt (1 + lam ^ 2))⁻¹ * (F x - lam * F (x + a)) from rfl] at hx
    have h0 : F x - lam * F (x + a) = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h hc
      · exact h
    linarith
  obtain ⟨r, hr⟩ := exists_radius_of_hasCompactSupport hFc
  exact hF0 (eq_zero_of_eq_const_mul_shift ha hr heq)

theorem eulerComb_ne_zero : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, HasCompactSupport H → H ≠ 0 →
    (∀ p ∈ L, p.2 ≠ 0) → eulerComb L H ≠ 0 := by
  intro L
  induction L with
  | nil => intro H _ hH0 _; exact hH0
  | cons p L ih =>
      intro H hHc hH0 hL
      obtain ⟨w, a⟩ := p
      exact ih (hasCompactSupport_eulerFactorFun hHc w a)
        (eulerFactorFun_ne_zero hHc hH0 w (hL (w, a) (List.mem_cons_self ..)))
        (fun q hq => hL q (List.mem_cons_of_mem _ hq))

theorem eq_zero_of_integral_sq_eq_zero {G : ℝ → ℝ} (hGc : Continuous G)
    (hint : Integrable (fun x => G x ^ 2)) (hzero : (∫ x, G x ^ 2) = 0) : G = 0 := by
  have hae : (fun x => G x ^ 2) =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp hzero
  have hae2 : G =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  exact (Continuous.ae_eq_iff_eq volume hGc continuous_const).mp hae2

theorem integral_sq_pos_of_ne_zero {G : ℝ → ℝ} (hGc : Continuous G)
    (hGcs : HasCompactSupport G) (hG0 : G ≠ 0) : 0 < ∫ x, G x ^ 2 := by
  have hcs : HasCompactSupport (fun x => G x ^ 2) := by
    refine HasCompactSupport.intro hGcs.isCompact fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hint : Integrable (fun x => G x ^ 2) :=
    (hGc.pow 2).integrable_of_hasCompactSupport hcs
  have hnn : 0 ≤ ∫ x, G x ^ 2 := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · exact absurd (eq_zero_of_integral_sq_eq_zero hGc hint hzero.symm) hG0
  · exact hpos

/-- **The payment is strict.**  A nonzero test keeps a positive residual at every family of
nonzero lags: the first-power charges are never paid in full by the mass. -/
theorem eulerPayment_lt_mass (hF : Continuous F) (hFc : HasCompactSupport F) (hF0 : F ≠ 0)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 ≠ 0) :
    eulerPayment L (autoCorrelation F) < autoCorrelation F 0 := by
  have hpos : 0 < ∫ x, eulerComb L F x ^ 2 :=
    integral_sq_pos_of_ne_zero (G := eulerComb L F) (continuous_eulerComb L hF)
      (hasCompactSupport_eulerComb L hFc)
      (eulerComb_ne_zero L hFc hF0 (fun p hp => (hL p hp).2))
  have hres : autoCorrelation F 0 - eulerPayment L (autoCorrelation F)
      = ∫ x, eulerComb L F x ^ 2 :=
    eulerPayment_residual hF hFc L (fun p hp => (hL p hp).1)
  linarith

/-! ### The coherent decomposition of the first-power charge

The raw first-power charge of a family of lags differs from its sequential payment by an explicit
cross-charge: for each lag, the earlier lags read at the ratio lag `a_k − a_j` and the product lag
`a_k + a_j` of the pair, in the ledger transformed by their predecessors.  With the residual
identity this decomposes the charge exactly into mass, comb energy and cross-charges, which is the
coherent subtraction the prime side needs: at prime-power lags the cross terms sit precisely at
the ratio and product incidences of the pairs. -/

/-- The raw first-power charge of a weighted family of lags. -/
def eulerRaw (L : List (ℝ × ℝ)) (A : ℝ → ℝ) : ℝ := (L.map fun p => p.1 * A p.2).sum

/-- The ratio–product cross-charge of a weighted family of lags. -/
def eulerCross : List (ℝ × ℝ) → (ℝ → ℝ) → ℝ
  | [], _ => 0
  | (w, a) :: L, A =>
      (L.map fun q => q.1 * (w / 2) * (A (q.2 - a) + A (q.2 + a))).sum
        + eulerCross L (eulerStep w a A)

theorem eulerRaw_sub_eulerRaw_eulerStep (M : List (ℝ × ℝ)) (A : ℝ → ℝ) (w a : ℝ) :
    eulerRaw M A - eulerRaw M (eulerStep w a A)
      = (M.map fun q => q.1 * (w / 2) * (A (q.2 - a) + A (q.2 + a))).sum := by
  induction M with
  | nil => simp [eulerRaw]
  | cons q M ih =>
      simp only [eulerRaw, List.map_cons, List.sum_cons] at ih ⊢
      have hq : eulerStep w a A q.2 = A q.2 - (w / 2) * (A (q.2 - a) + A (q.2 + a)) := rfl
      rw [hq]
      linarith

/-- **The sequential payment is the raw charge minus the cross-charges.** -/
theorem eulerPayment_eq_raw_sub_cross : ∀ (L : List (ℝ × ℝ)) (A : ℝ → ℝ),
    eulerPayment L A = eulerRaw L A - eulerCross L A := by
  intro L
  induction L with
  | nil => intro A; simp [eulerPayment, eulerRaw, eulerCross]
  | cons p L ih =>
      intro A
      obtain ⟨w, a⟩ := p
      have hstep := eulerRaw_sub_eulerRaw_eulerStep L A w a
      rw [eulerPayment, eulerCross, ih (eulerStep w a A)]
      simp only [eulerRaw, List.map_cons, List.sum_cons] at hstep ⊢
      linarith

/-- **The first-power charges are paid by the mass and the cross-charges.** -/
theorem eulerRaw_le (hF : Continuous F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    eulerRaw L (autoCorrelation F)
      ≤ autoCorrelation F 0 + eulerCross L (autoCorrelation F) := by
  have h := eulerPayment_le_mass hF hFc L hL
  rw [eulerPayment_eq_raw_sub_cross] at h
  linarith

/-- **Exact decomposition of the first-power charge** into mass, comb energy and cross-charges. -/
theorem eulerRaw_eq (hF : Continuous F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    eulerRaw L (autoCorrelation F)
      = autoCorrelation F 0 - (∫ x, eulerComb L F x ^ 2) + eulerCross L (autoCorrelation F) := by
  have h := eulerPayment_residual hF hFc L hL
  rw [eulerPayment_eq_raw_sub_cross] at h
  linarith

/-- The Euler weights and lags of a list of prime powers. -/
def primeEulerList (ns : List ℕ) : List (ℝ × ℝ) :=
  ns.map fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n, Real.log n)

theorem eulerRaw_primeEulerList (A : ℝ → ℝ) (ns : List ℕ) :
    eulerRaw (primeEulerList ns) A
      = (ns.map fun n =>
          (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * A (Real.log n)).sum := by
  rw [eulerRaw, primeEulerList, List.map_map]
  rfl

/-- **The prime first-power charge against the mass and its ratio–product cross-charges.** -/
theorem prime_eulerRaw_le (hF : Continuous F) (hFc : HasCompactSupport F) (ns : List ℕ) :
    (ns.map fun n => (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        * autoCorrelation F (Real.log n)).sum
      ≤ autoCorrelation F 0 + eulerCross (primeEulerList ns) (autoCorrelation F) := by
  have hadm : ∀ p ∈ primeEulerList ns, 0 ≤ p.1 ∧ p.1 ≤ 1 := by
    intro p hp
    rw [primeEulerList, List.mem_map] at hp
    obtain ⟨n, -, rfl⟩ := hp
    exact ⟨div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _),
      vonMangoldtAtom_le_one n⟩
  have h := eulerRaw_le hF hFc (primeEulerList ns) hadm
  rwa [eulerRaw_primeEulerList] at h

/-! ### The spectral form of the lag ledger

The Gram kernel of a test is the cosine transform of the nonnegative spectral density `|F̂|²`:
the density is integrable because a `C¹` compactly supported test has `|F̂(ξ)| = O(1/|ξ|)`, so its
square is `O(1/ξ²)`.  Every weighted lag charge is therefore the pairing of the family's **symbol**
`S(ξ) = Σ_j w_j cos(2π a_j ξ)` against that density, and the charge per unit mass is bounded by the
supremum of the symbol.  This is the exact form of the resonance phenomenon: a test concentrates its
density where the symbol is largest, and no test does better. -/

open FourierTransform in
/-- The spectral density of a test: the squared modulus of its Fourier transform. -/
noncomputable def spectralDensity (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ^ 2

open FourierTransform Complex in
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) • f x‖ = ‖f x‖
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

open FourierTransform Complex in
theorem continuous_spectralDensity (hF : Continuous F) (hFc : HasCompactSupport F) :
    Continuous (spectralDensity F) :=
  ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
    ((Complex.continuous_ofReal.comp hF).integrable_of_hasCompactSupport
      (hFc.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp)))).norm.pow 2)

open FourierTransform Complex in
theorem integrable_spectralDensity (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    Integrable (spectralDensity F) := by
  have hFcc : Continuous (fun x => ((F x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hF.continuous
  have hFccs : HasCompactSupport (fun x => ((F x : ℝ) : ℂ)) :=
    hFc.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp)
  have hFci : Integrable (fun x => ((F x : ℝ) : ℂ)) :=
    hFcc.integrable_of_hasCompactSupport hFccs
  have hdc : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hderiv : deriv (fun x => ((F x : ℝ) : ℂ)) = fun x => ((deriv F x : ℝ) : ℂ) := by
    funext x
    have h : HasDerivAt F (deriv F x) x := (hF.differentiable (by norm_num) x).hasDerivAt
    exact h.ofReal_comp.deriv
  have hdFci : Integrable (deriv (fun x => ((F x : ℝ) : ℂ))) := by
    rw [hderiv]
    exact (Complex.continuous_ofReal.comp hdc).integrable_of_hasCompactSupport
      ((hFc.deriv).comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp))
  have hdiff : Differentiable ℝ (fun x => ((F x : ℝ) : ℂ)) := by
    intro x
    have h : HasDerivAt F (deriv F x) x := (hF.differentiable (by norm_num) x).hasDerivAt
    exact h.ofReal_comp.differentiableAt
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, B0 = ∫ x : ℝ, ‖((F x : ℝ) : ℂ)‖ := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℝ, B1 = ∫ x : ℝ, ‖deriv (fun y => ((F y : ℝ) : ℂ)) x‖ := ⟨_, rfl⟩
  have hB0nn : 0 ≤ B0 := hB0 ▸ integral_nonneg fun x => norm_nonneg _
  have hB1nn : 0 ≤ B1 := hB1 ▸ integral_nonneg fun x => norm_nonneg _
  have hsmall : ∀ ξ, spectralDensity F ξ ≤ B0 ^ 2 := by
    intro ξ
    have h := norm_fourier_le (fun x => ((F x : ℝ) : ℂ)) ξ
    rw [← hB0] at h
    have h0 : 0 ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ := norm_nonneg _
    rw [spectralDensity]
    nlinarith
  have hbig : ∀ ξ : ℝ, ξ ≠ 0 → spectralDensity F ξ ≤ B1 ^ 2 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
    intro ξ hξ
    have hfd : 𝓕 (deriv (fun x => ((F x : ℝ) : ℂ))) ξ
        = (2 * Real.pi * I * ξ) • 𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ := by
      rw [Real.fourier_deriv hFci hdiff hdFci]
    have hnorm : 2 * Real.pi * |ξ| * ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ≤ B1 := by
      have h := norm_fourier_le (deriv (fun x => ((F x : ℝ) : ℂ))) ξ
      rw [← hB1] at h
      rw [hfd, norm_smul] at h
      have : ‖(2 * Real.pi * I * (ξ : ℂ))‖ = 2 * Real.pi * |ξ| := by
        simp [abs_of_nonneg Real.pi_pos.le]
      rwa [this] at h
    have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
    have hpi : 0 < Real.pi := Real.pi_pos
    have h0 : 0 ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ := norm_nonneg _
    rw [spectralDensity, le_div_iff₀ (by positivity)]
    have hsq : (ξ : ℝ) ^ 2 = |ξ| ^ 2 := (sq_abs ξ).symm
    set X := ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ with hX
    have hsquared : (2 * Real.pi * |ξ| * X) * (2 * Real.pi * |ξ| * X) ≤ B1 * B1 :=
      mul_self_le_mul_self (by positivity) hnorm
    have hexpand : (2 * Real.pi * |ξ| * X) * (2 * Real.pi * |ξ| * X) = X ^ 2 * (4 * Real.pi ^ 2 * ξ ^ 2) := by
      rw [hsq]; ring
    have hB1sq : B1 * B1 = B1 ^ 2 := (sq B1).symm
    linarith [hsquared, hexpand, hB1sq]
  refine Integrable.mono' (g := fun ξ : ℝ => (2 * B0 ^ 2 + B1 ^ 2 / (2 * Real.pi ^ 2)) * (1 + ξ ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _)
    (((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      hFci).norm.pow 2).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [spectralDensity]; positivity :
    (0:ℝ) ≤ spectralDensity F ξ)]
  rcases le_or_gt |ξ| 1 with hle | hgt
  · have h1 : (1 : ℝ) + ξ ^ 2 ≤ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    have h2 : (1:ℝ)/2 ≤ (1 + ξ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hc : 0 ≤ 2 * B0 ^ 2 + B1 ^ 2 / (2 * Real.pi ^ 2) := by positivity
    have hstep : (2 * B0 ^ 2 + B1 ^ 2 / (2 * Real.pi ^ 2)) * (1 / 2)
        ≤ (2 * B0 ^ 2 + B1 ^ 2 / (2 * Real.pi ^ 2)) * (1 + ξ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 hc
    have hb1 : 0 ≤ B1 ^ 2 / (2 * Real.pi ^ 2) := by positivity
    linarith [hsmall ξ, hstep, hb1]
  · have hξ : ξ ≠ 0 := by
      intro h
      rw [h, abs_zero] at hgt
      linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsq1 : (1:ℝ) ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hinv : (1 + ξ ^ 2)⁻¹ ≥ 1 / (2 * ξ ^ 2) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hinvnn : 0 ≤ (1 + ξ ^ 2)⁻¹ := by positivity
    have hsd := hbig ξ hξ
    have hstep1 : B1 ^ 2 / (2 * Real.pi ^ 2) * (1 / (2 * ξ ^ 2))
        ≤ B1 ^ 2 / (2 * Real.pi ^ 2) * (1 + ξ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have hval : B1 ^ 2 / (2 * Real.pi ^ 2) * (1 / (2 * ξ ^ 2)) = B1 ^ 2 / (4 * Real.pi ^ 2 * ξ ^ 2) := by
      field_simp
      ring
    rw [hval] at hstep1
    have hstep2 : B1 ^ 2 / (2 * Real.pi ^ 2) * (1 + ξ ^ 2)⁻¹
        ≤ (2 * B0 ^ 2 + B1 ^ 2 / (2 * Real.pi ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
      have hb0 : 0 ≤ 2 * B0 ^ 2 := by positivity
      nlinarith [hinvnn]
    linarith [hsd, hstep1, hstep2]

/-- The autocorrelation of a compactly supported test has compact support. -/
theorem hasCompactSupport_autoCorrelation' (hF : Continuous F) (hFc : HasCompactSupport F) :
    HasCompactSupport (autoCorrelation F) := by
  obtain ⟨r, hr⟩ := exists_radius_of_hasCompactSupport hFc
  refine hasCompactSupport_autoCorrelation hF (r := max r 1)
    (lt_of_lt_of_le one_pos (le_max_right r 1)) fun y hy => hr y ?_
  exact lt_of_le_of_lt (le_max_left r 1) hy

open FourierTransform Complex in
theorem autoCorrelation_eq_integral_spectral (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (t : ℝ) :
    autoCorrelation F t = ∫ ξ : ℝ, Real.cos (2 * Real.pi * t * ξ) * spectralDensity F ξ := by
  have hAc : Continuous (fun t => ((autoCorrelation F t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (contDiff_one_autoCorrelation hF hFc).continuous
  have hAcs : HasCompactSupport (fun t => ((autoCorrelation F t : ℝ) : ℂ)) :=
    (hasCompactSupport_autoCorrelation' hF.continuous hFc).comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp)
  have hAi : Integrable (fun t => ((autoCorrelation F t : ℝ) : ℂ)) :=
    hAc.integrable_of_hasCompactSupport hAcs
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hFA : 𝓕 (fun t => ((autoCorrelation F t : ℝ) : ℂ))
      = fun ξ => ((spectralDensity F ξ : ℝ) : ℂ) := by
    funext ξ
    exact fourier_ofReal_autoCorrelation_sq hF.continuous hFc ξ
  have hFAi : Integrable (𝓕 (fun t => ((autoCorrelation F t : ℝ) : ℂ))) := by
    rw [hFA]
    exact hgi.ofReal
  have hinv := hAc.fourierInv_fourier_eq hAi hFAi
  have h1 : ((autoCorrelation F t : ℝ) : ℂ)
      = ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I) • ((spectralDensity F ξ : ℝ) : ℂ) := by
    have := congrFun hinv t
    rw [hFA] at this
    rw [← this, Real.fourierInv_eq']
    simp only [Real.inner_apply]
  have hgc : Continuous (spectralDensity F) :=
    ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      ((Complex.continuous_ofReal.comp hF.continuous).integrable_of_hasCompactSupport
        (hFc.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp)))).norm.pow 2)
  have hcint : Integrable (fun ξ : ℝ =>
      Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I) • ((spectralDensity F ξ : ℝ) : ℂ)) := by
    refine Integrable.mono' hgi.norm ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (by fun_prop : Continuous fun ξ : ℝ => 2 * Real.pi * (ξ * t))).mul continuous_const)).smul
        (Complex.continuous_ofReal.comp hgc)).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hre0 := Complex.reCLM.integral_comp_comm hcint
  have hre : (∫ ξ : ℝ, Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I)
        • ((spectralDensity F ξ : ℝ) : ℂ)).re
      = ∫ ξ : ℝ, (Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I)
        • ((spectralDensity F ξ : ℝ) : ℂ)).re := hre0.symm
  have hval : autoCorrelation F t
      = (∫ ξ : ℝ, Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I)
          • ((spectralDensity F ξ : ℝ) : ℂ)).re := by
    rw [← h1, Complex.ofReal_re]
  rw [hval, hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (Complex.exp (((2 * Real.pi * (ξ * t) : ℝ)) * I) * ((spectralDensity F ξ : ℝ) : ℂ)).re
    = Real.cos (2 * Real.pi * t * ξ) * spectralDensity F ξ
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, show 2 * Real.pi * (ξ * t) = 2 * Real.pi * t * ξ by ring]
  ring

/-- The symbol of a weighted lag family. -/
noncomputable def lagSymbol (L : List (ℝ × ℝ)) (ξ : ℝ) : ℝ :=
  (L.map fun p => p.1 * Real.cos (2 * Real.pi * p.2 * ξ)).sum

theorem continuous_lagSymbol (L : List (ℝ × ℝ)) : Continuous (lagSymbol L) := by
  induction L with
  | nil =>
      have h0 : lagSymbol [] = fun _ : ℝ => (0:ℝ) := by
        funext ξ
        simp [lagSymbol]
      rw [h0]
      exact continuous_const
  | cons p L ih =>
      have : lagSymbol (p :: L) = fun ξ => p.1 * Real.cos (2 * Real.pi * p.2 * ξ) + lagSymbol L ξ := by
        funext ξ
        rw [lagSymbol, List.map_cons, List.sum_cons, ← lagSymbol]
      rw [this]
      exact (continuous_const.mul (Real.continuous_cos.comp (by fun_prop))).add ih

theorem abs_lagSymbol_le (L : List (ℝ × ℝ)) (ξ : ℝ) :
    |lagSymbol L ξ| ≤ (L.map fun p => |p.1|).sum := by
  induction L with
  | nil => simp [lagSymbol]
  | cons p L ih =>
      rw [lagSymbol, List.map_cons, List.sum_cons, ← lagSymbol, List.map_cons, List.sum_cons]
      have hp : |p.1 * Real.cos (2 * Real.pi * p.2 * ξ)| ≤ |p.1| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      calc |p.1 * Real.cos (2 * Real.pi * p.2 * ξ) + lagSymbol L ξ|
          ≤ |p.1 * Real.cos (2 * Real.pi * p.2 * ξ)| + |lagSymbol L ξ| := abs_add_le _ _
        _ ≤ |p.1| + (L.map fun q => |q.1|).sum := by linarith [ih]

theorem integrable_lagSymbol_mul (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) :
    Integrable (fun ξ => lagSymbol L ξ * spectralDensity F ξ) := by
  refine Integrable.mono' ((integrable_spectralDensity hF hFc).norm.const_mul
    ((L.map fun p => |p.1|).sum)) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_lagSymbol L).mul
      (continuous_spectralDensity hF.continuous hFc)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_lagSymbol_le L ξ) (abs_nonneg _)

/-- **The first-power charge is the symbol against the spectral density.** -/
theorem eulerRaw_eq_integral_symbol (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) :
    eulerRaw L (autoCorrelation F) = ∫ ξ : ℝ, lagSymbol L ξ * spectralDensity F ξ := by
  induction L with
  | nil => simp [eulerRaw, lagSymbol]
  | cons p L ih =>
      obtain ⟨w, a⟩ := p
      have hsplit : ∀ ξ : ℝ, lagSymbol ((w, a) :: L) ξ * spectralDensity F ξ
          = w * (Real.cos (2 * Real.pi * a * ξ) * spectralDensity F ξ)
            + lagSymbol L ξ * spectralDensity F ξ := by
        intro ξ
        rw [lagSymbol, List.map_cons, List.sum_cons, ← lagSymbol]
        ring
      have hint1 : Integrable (fun ξ : ℝ => Real.cos (2 * Real.pi * a * ξ) * spectralDensity F ξ) := by
        have := integrable_lagSymbol_mul hF hFc [(1, a)]
        simpa [lagSymbol] using this
      have hint2 : Integrable (fun ξ : ℝ => lagSymbol L ξ * spectralDensity F ξ) :=
        integrable_lagSymbol_mul hF hFc L
      rw [eulerRaw, List.map_cons, List.sum_cons, ← eulerRaw, ih,
        autoCorrelation_eq_integral_spectral hF hFc a,
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
        MeasureTheory.integral_add (hint1.const_mul w) hint2,
        MeasureTheory.integral_const_mul]

/-- **Capacity bound**: the first-power charge is at most the sup of the symbol times the mass. -/
theorem eulerRaw_le_symbol_bound (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) {C : ℝ} (hC : ∀ ξ, lagSymbol L ξ ≤ C) :
    eulerRaw L (autoCorrelation F) ≤ C * autoCorrelation F 0 := by
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hmass : autoCorrelation F 0 = ∫ ξ : ℝ, spectralDensity F ξ := by
    rw [autoCorrelation_eq_integral_spectral hF hFc 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.cos (2 * Real.pi * 0 * ξ) * spectralDensity F ξ = spectralDensity F ξ
    rw [show 2 * Real.pi * 0 * ξ = 0 by ring, Real.cos_zero, one_mul]
  rw [eulerRaw_eq_integral_symbol hF hFc L, hmass, ← MeasureTheory.integral_const_mul]
  refine integral_mono (integrable_lagSymbol_mul hF hFc L) (hgi.const_mul C) fun ξ => ?_
  have hg : 0 ≤ spectralDensity F ξ := by rw [spectralDensity]; positivity
  exact mul_le_mul_of_nonneg_right (hC ξ) hg

/-! ### The comb acts diagonally in frequency

A comb factor multiplies the Fourier transform by `c(1 − λe^{2πiaξ})`, so it multiplies the
spectral density by `1 − w cos(2πaξ)` with `w = 2λ/(1+λ²)`.  The Euler ledger is therefore
diagonalised by the Fourier transform: an iterated comb multiplies the density by the product of
its factors, the payment is the deficit of that product against the density, and the admissibility
`w ≤ 1` is exactly the nonnegativity of the multiplier.  This is the conceptual content of the
payment law: it holds because a nonnegative multiplier cannot remove more than the whole mass. -/

open FourierTransform Complex in
theorem fourier_shift (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun x => f (x + a)) ξ = Complex.exp (((2 * Real.pi * a * ξ : ℝ)) * I) * 𝓕 f ξ := by
  have hmain : (∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • f v)
      = ∫ v : ℝ, Complex.exp (((-2 * Real.pi * (v + a) * ξ : ℝ)) * I) • f (v + a) :=
    (MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure ℝ)) (fun v => Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • f v) a).symm
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, hmain,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • f (v + a)
    = Complex.exp (((2 * Real.pi * a * ξ : ℝ)) * I)
      * (Complex.exp (((-2 * Real.pi * (v + a) * ξ : ℝ)) * I) • f (v + a))
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

open Complex in
theorem norm_one_sub_mul_exp_sq (lam θ : ℝ) :
    ‖(1 : ℂ) - (lam : ℂ) * Complex.exp ((θ : ℝ) * I)‖ ^ 2 = 1 + lam ^ 2 - 2 * lam * Real.cos θ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only [Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

variable {F : ℝ → ℝ}

open FourierTransform Complex in
theorem integrable_exp_smul {g : ℝ → ℂ} (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • g v) := by
  refine Integrable.mono' hg.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun v : ℝ => -2 * Real.pi * v * ξ)).mul
      continuous_const)).aestronglyMeasurable).smul hg.aestronglyMeasurable
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

open FourierTransform Complex in
theorem fourier_ofReal_eulerFactorFun (hF : Continuous F) (hFc : HasCompactSupport F)
    (w a ξ : ℝ) :
    𝓕 (fun x => ((eulerFactorFun w a F x : ℝ) : ℂ)) ξ
      = (((Real.sqrt (1 + eulerLam w ^ 2))⁻¹ : ℝ) : ℂ)
        * (((1 : ℂ) - (eulerLam w : ℂ) * Complex.exp (((2 * Real.pi * a * ξ : ℝ)) * I))
          * 𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ) := by
  have hGi : Integrable (fun x => ((F x : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hF).integrable_of_hasCompactSupport
      (hFc.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp))
  have hGai : Integrable (fun x => ((F (x + a) : ℝ) : ℂ)) := by
    have := hGi.comp_add_right a
    exact this
  have h1 := integrable_exp_smul hGi ξ
  have h2 := integrable_exp_smul hGai ξ
  have hpt : ∀ v : ℝ,
      Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • ((eulerFactorFun w a F v : ℝ) : ℂ)
        = (((Real.sqrt (1 + eulerLam w ^ 2))⁻¹ : ℝ) : ℂ)
            * (Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • ((F v : ℝ) : ℂ))
          - (((Real.sqrt (1 + eulerLam w ^ 2))⁻¹ * eulerLam w : ℝ) : ℂ)
            * (Complex.exp (((-2 * Real.pi * v * ξ : ℝ)) * I) • ((F (v + a) : ℝ) : ℂ)) := by
    intro v
    rw [eulerFactorFun]
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_sub (h1.const_mul _) (h2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    ← Real.fourier_real_eq_integral_exp_smul, ← Real.fourier_real_eq_integral_exp_smul,
    fourier_shift (fun x => ((F x : ℝ) : ℂ)) a ξ]
  push_cast
  ring

open FourierTransform Complex in
theorem spectralDensity_eulerFactorFun (hF : Continuous F) (hFc : HasCompactSupport F)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (a ξ : ℝ) :
    spectralDensity (eulerFactorFun w a F) ξ
      = (1 - w * Real.cos (2 * Real.pi * a * ξ)) * spectralDensity F ξ := by
  have hspec : 2 * eulerLam w / (1 + eulerLam w ^ 2) = w := by
    rcases eq_or_lt_of_le hw0 with rfl | hw
    · rw [eulerLam_zero]; norm_num
    · exact eulerLam_spec hw hw1
  have hpos : (0:ℝ) < 1 + eulerLam w ^ 2 := by positivity
  rw [spectralDensity, spectralDensity, fourier_ofReal_eulerFactorFun hF hFc w a ξ,
    norm_mul, norm_mul, mul_pow, mul_pow, norm_one_sub_mul_exp_sq,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (1 + eulerLam w ^ 2))⁻¹)]
  have hc2 : ((Real.sqrt (1 + eulerLam w ^ 2))⁻¹) ^ 2 = (1 + eulerLam w ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos.le]
  rw [hc2]
  have hkey : w * (1 + eulerLam w ^ 2) = 2 * eulerLam w := by
    rw [div_eq_iff (ne_of_gt hpos)] at hspec
    linarith [hspec]
  have hX : (0:ℝ) ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ^ 2 := by positivity
  field_simp
  linear_combination (Real.cos (2 * Real.pi * a * ξ) * ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ^ 2) * hkey

/-- The Euler multiplier of a weighted lag family. -/
noncomputable def eulerMultiplier (L : List (ℝ × ℝ)) (ξ : ℝ) : ℝ :=
  (L.map fun p => 1 - p.1 * Real.cos (2 * Real.pi * p.2 * ξ)).prod

theorem eulerMultiplier_nonneg (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) (ξ : ℝ) :
    0 ≤ eulerMultiplier L ξ := by
  induction L with
  | nil => simp [eulerMultiplier]
  | cons p L ih =>
      have hfac : 0 ≤ 1 - p.1 * Real.cos (2 * Real.pi * p.2 * ξ) := by
        obtain ⟨h0, h1⟩ := hL p (List.mem_cons_self ..)
        nlinarith [Real.cos_le_one (2 * Real.pi * p.2 * ξ), Real.neg_one_le_cos (2 * Real.pi * p.2 * ξ)]
      rw [eulerMultiplier, List.map_cons, List.prod_cons, ← eulerMultiplier]
      exact mul_nonneg hfac (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))

theorem contDiff_one_eulerFactorFun (hF : ContDiff ℝ 1 F) (w a : ℝ) :
    ContDiff ℝ 1 (eulerFactorFun w a F) :=
  contDiff_const.mul (hF.sub (contDiff_const.mul
    (hF.comp (contDiff_id.add contDiff_const))))

theorem contDiff_one_eulerComb : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, ContDiff ℝ 1 H →
    ContDiff ℝ 1 (eulerComb L H) := by
  intro L
  induction L with
  | nil => intro H hH; exact hH
  | cons p L ih =>
      intro H hH
      obtain ⟨w, a⟩ := p
      exact ih (contDiff_one_eulerFactorFun hH w a)

/-- **The Euler comb acts diagonally in frequency.** -/

theorem spectralDensity_eulerComb : ∀ (L : List (ℝ × ℝ)) {H : ℝ → ℝ}, Continuous H →
    HasCompactSupport H → (∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) → ∀ ξ : ℝ,
    spectralDensity (eulerComb L H) ξ = eulerMultiplier L ξ * spectralDensity H ξ := by
  intro L
  induction L with
  | nil => intro H _ _ _ ξ; simp [eulerComb, eulerMultiplier]
  | cons p L ih =>
      intro H hH hHc hL ξ
      obtain ⟨w, a⟩ := p
      obtain ⟨hw0, hw1⟩ := hL (w, a) (List.mem_cons_self ..)
      rw [eulerComb, ih (continuous_eulerFactorFun hH w a)
          (hasCompactSupport_eulerFactorFun hHc w a)
          (fun q hq => hL q (List.mem_cons_of_mem _ hq)) ξ,
        spectralDensity_eulerFactorFun hH hHc hw0 hw1 a ξ]
      simp only [eulerMultiplier, List.map_cons, List.prod_cons]
      ring

theorem eulerPayment_eq_integral_multiplier (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) :
    eulerPayment L (autoCorrelation F)
      = ∫ ξ : ℝ, (1 - eulerMultiplier L ξ) * spectralDensity F ξ := by
  have hres := eulerPayment_residual hF.continuous hFc L hL
  have hcombC1 : ContDiff ℝ 1 (eulerComb L F) := contDiff_one_eulerComb L hF
  have hcombCS : HasCompactSupport (eulerComb L F) := hasCompactSupport_eulerComb L hFc
  have hcos : ∀ (G : ℝ → ℝ), ContDiff ℝ 1 G → HasCompactSupport G →
      autoCorrelation G 0 = ∫ ξ : ℝ, spectralDensity G ξ := by
    intro G hG hGc
    rw [autoCorrelation_eq_integral_spectral hG hGc 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.cos (2 * Real.pi * 0 * ξ) * spectralDensity G ξ = spectralDensity G ξ
    rw [show 2 * Real.pi * 0 * ξ = 0 by ring, Real.cos_zero, one_mul]
  have h1 : (∫ x, eulerComb L F x ^ 2) = ∫ ξ : ℝ, spectralDensity (eulerComb L F) ξ := by
    rw [← autoCorrelation_zero_eq, hcos _ hcombC1 hcombCS]
  have hpt : ∀ ξ : ℝ,
      spectralDensity (eulerComb L F) ξ = eulerMultiplier L ξ * spectralDensity F ξ :=
    spectralDensity_eulerComb L hF.continuous hFc hL
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hmi : Integrable (fun ξ : ℝ => eulerMultiplier L ξ * spectralDensity F ξ) :=
    (integrable_spectralDensity hcombC1 hcombCS).congr
      (Filter.Eventually.of_forall hpt)
  have h2 : (∫ ξ : ℝ, spectralDensity (eulerComb L F) ξ)
      = ∫ ξ : ℝ, eulerMultiplier L ξ * spectralDensity F ξ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ ξ : ℝ, (1 - eulerMultiplier L ξ) * spectralDensity F ξ)
      = (∫ ξ : ℝ, spectralDensity F ξ) - ∫ ξ : ℝ, eulerMultiplier L ξ * spectralDensity F ξ := by
    rw [← MeasureTheory.integral_sub hgi hmi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  rw [hsplit, ← hcos F hF hFc, ← h2, ← h1]
  linarith [hres]

/-! ### How sharply a test can concentrate in frequency

The transform of a test supported in `[−r, r]` is Lipschitz with constant `2πr‖F‖₁`, so its
spectral density is Lipschitz with constant `4πr‖F‖₁²`: an aperture-`r` test cannot vary its
density faster than the aperture allows.  Consequently a window of half-width `δ` holds at most
`2δ(g(ξ₀) + 4πr‖F‖₁²δ)` of the mass, and the rest stays outside.  This is the quantitative form of
the resonance limit: a test can track a peak of the symbol only if the peak is wider than the
reciprocal aperture. -/

open Complex in
theorem norm_exp_mul_I_sub_one_le (t : ℝ) : ‖Complex.exp ((t : ℝ) * I) - 1‖ ≤ |t| := by
  have h1 : ‖Complex.exp ((t : ℝ) * I) - 1‖ ^ 2 = 2 - 2 * Real.cos t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h2 : ‖Complex.exp ((t : ℝ) * I) - 1‖ ^ 2 ≤ |t| ^ 2 := by
    rw [h1, sq_abs]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (abs_nonneg t)] at h3

open Complex in
theorem norm_exp_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp ((x : ℝ) * I) - Complex.exp ((y : ℝ) * I)‖ ≤ |x - y| := by
  have hfac : Complex.exp ((x : ℝ) * I) - Complex.exp ((y : ℝ) * I)
      = Complex.exp ((y : ℝ) * I) * (Complex.exp (((x - y : ℝ)) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    push_cast
    ring_nf
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_mul_I_sub_one_le (x - y)

variable {F : ℝ → ℝ}

open FourierTransform Complex in
theorem norm_fourier_sub_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (ξ ξ' : ℝ) :
    ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ - 𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖
      ≤ 2 * Real.pi * r * (∫ x : ℝ, |F x|) * |ξ - ξ'| := by
  have hGi : Integrable (fun x => ((F x : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hF).integrable_of_hasCompactSupport
      (hFc.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) (by simp))
  have hFi : Integrable fun x : ℝ => |F x| :=
    (hF.abs).integrable_of_hasCompactSupport (hFc.comp_left (g := fun y : ℝ => |y|) (by simp))
  have hxFi : Integrable fun x : ℝ => |x| * |F x| :=
    ((continuous_abs.mul hF.abs)).integrable_of_hasCompactSupport
      ((hFc.comp_left (g := fun y : ℝ => |y|) (by simp)).mul_left)
  have h1 := integrable_exp_smul hGi ξ
  have h2 := integrable_exp_smul hGi ξ'
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← MeasureTheory.integral_sub h1 h2]
  have hpt : ∀ x : ℝ,
      ‖Complex.exp (((-2 * Real.pi * x * ξ : ℝ)) * I) • ((F x : ℝ) : ℂ)
        - Complex.exp (((-2 * Real.pi * x * ξ' : ℝ)) * I) • ((F x : ℝ) : ℂ)‖
        ≤ 2 * Real.pi * |ξ - ξ'| * (|x| * |F x|) := by
    intro x
    rw [← sub_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_exp_mul_I_sub_le (-2 * Real.pi * x * ξ) (-2 * Real.pi * x * ξ')
    have habs : |(-2 * Real.pi * x * ξ) - (-2 * Real.pi * x * ξ')| = 2 * Real.pi * |x| * |ξ - ξ'| := by
      rw [show (-2 * Real.pi * x * ξ) - (-2 * Real.pi * x * ξ') = (-(2 * Real.pi * x)) * (ξ - ξ') by ring,
        abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le]
      norm_num
    rw [habs] at hb
    calc ‖Complex.exp (((-2 * Real.pi * x * ξ : ℝ)) * I) - Complex.exp (((-2 * Real.pi * x * ξ' : ℝ)) * I)‖
          * |F x| ≤ (2 * Real.pi * |x| * |ξ - ξ'|) * |F x| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = 2 * Real.pi * |ξ - ξ'| * (|x| * |F x|) := by ring
  calc ‖∫ x : ℝ, (Complex.exp (((-2 * Real.pi * x * ξ : ℝ)) * I) • ((F x : ℝ) : ℂ)
          - Complex.exp (((-2 * Real.pi * x * ξ' : ℝ)) * I) • ((F x : ℝ) : ℂ))‖
      ≤ ∫ x : ℝ, ‖Complex.exp (((-2 * Real.pi * x * ξ : ℝ)) * I) • ((F x : ℝ) : ℂ)
          - Complex.exp (((-2 * Real.pi * x * ξ' : ℝ)) * I) • ((F x : ℝ) : ℂ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, 2 * Real.pi * |ξ - ξ'| * (|x| * |F x|) := by
        refine MeasureTheory.integral_mono ((h1.sub h2).norm) (hxFi.const_mul _) hpt
    _ = 2 * Real.pi * |ξ - ξ'| * ∫ x : ℝ, |x| * |F x| := MeasureTheory.integral_const_mul _ _
    _ ≤ 2 * Real.pi * |ξ - ξ'| * (r * ∫ x : ℝ, |F x|) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono hxFi (hFi.const_mul r) fun x => ?_
        rcases le_or_gt |x| r with h | h
        · exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
        · rw [hsupp x h]
          simp
    _ = 2 * Real.pi * r * (∫ x : ℝ, |F x|) * |ξ - ξ'| := by ring

open FourierTransform Complex in
theorem abs_spectralDensity_sub_le (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 ≤ r) (hsupp : ∀ y, r < |y| → F y = 0) (ξ ξ' : ℝ) :
    |spectralDensity F ξ - spectralDensity F ξ'|
      ≤ 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * |ξ - ξ'| := by
  have hB : ∀ η : ℝ, ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) η‖ ≤ ∫ x : ℝ, |F x| := by
    intro η
    have h := norm_fourier_le (fun x => ((F x : ℝ) : ℂ)) η
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hBnn : (0:ℝ) ≤ ∫ x : ℝ, |F x| := le_trans (norm_nonneg _) (hB 0)
  have hlip := norm_fourier_sub_le hF hFc hsupp ξ ξ'
  have hab : |‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ - ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖|
      ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ - 𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖ :=
    abs_norm_sub_norm_le _ _
  rw [spectralDensity, spectralDensity]
  have hsq : ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ ^ 2 - ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖ ^ 2
      = (‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ - ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖)
        * (‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ + ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖) := by ring
  rw [hsq, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖
      + ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖)]
  calc |‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ - ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖|
        * (‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ + ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ'‖)
      ≤ (2 * Real.pi * r * (∫ x : ℝ, |F x|) * |ξ - ξ'|) * (2 * (∫ x : ℝ, |F x|)) := by
        refine mul_le_mul (le_trans hab hlip) (by linarith [hB ξ, hB ξ']) (by positivity)
          (by positivity)
    _ = 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * |ξ - ξ'| := by ring

theorem setIntegral_spectralDensity_le (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 ≤ r) (hsupp : ∀ y, r < |y| → F y = 0) (ξ₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ ξ in Set.Icc (ξ₀ - δ) (ξ₀ + δ), spectralDensity F ξ)
      ≤ 2 * δ * (spectralDensity F ξ₀ + 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ) := by
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hle : ∀ ξ ∈ Set.Icc (ξ₀ - δ) (ξ₀ + δ),
      spectralDensity F ξ ≤ spectralDensity F ξ₀ + 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ := by
    intro ξ hξ
    rw [Set.mem_Icc] at hξ
    have habs : |ξ - ξ₀| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith [hξ.1, hξ.2]
    have hlip := abs_spectralDensity_sub_le hF.continuous hFc hr hsupp ξ ξ₀
    have h1 : spectralDensity F ξ - spectralDensity F ξ₀ ≤ |spectralDensity F ξ - spectralDensity F ξ₀| :=
      le_abs_self _
    have h2 : 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * |ξ - ξ₀|
        ≤ 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ := by
      refine mul_le_mul_of_nonneg_left habs (by positivity)
    linarith
  have hvol : volume.real (Set.Icc (ξ₀ - δ) (ξ₀ + δ)) = 2 * δ := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc (∫ ξ in Set.Icc (ξ₀ - δ) (ξ₀ + δ), spectralDensity F ξ)
      ≤ ∫ _ξ in Set.Icc (ξ₀ - δ) (ξ₀ + δ),
          (spectralDensity F ξ₀ + 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ) :=
        MeasureTheory.setIntegral_mono_on hgi.integrableOn
          (continuous_const.integrableOn_Icc) measurableSet_Icc hle
    _ = 2 * δ * (spectralDensity F ξ₀ + 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ) := by
        rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]

/-- **Anti-concentration of the spectral density.** -/

theorem mass_outside_window_ge (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {r : ℝ}
    (hr : 0 ≤ r) (hsupp : ∀ y, r < |y| → F y = 0) (ξ₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    autoCorrelation F 0 - 2 * δ * (spectralDensity F ξ₀ + 4 * Real.pi * r * (∫ x : ℝ, |F x|) ^ 2 * δ)
      ≤ ∫ ξ in (Set.Icc (ξ₀ - δ) (ξ₀ + δ))ᶜ, spectralDensity F ξ := by
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hmass : autoCorrelation F 0 = ∫ ξ : ℝ, spectralDensity F ξ := by
    rw [autoCorrelation_eq_integral_spectral hF hFc 0]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.cos (2 * Real.pi * 0 * ξ) * spectralDensity F ξ = spectralDensity F ξ
    rw [show 2 * Real.pi * 0 * ξ = 0 by ring, Real.cos_zero, one_mul]
  have hsplit := MeasureTheory.integral_add_compl
    (measurableSet_Icc (a := ξ₀ - δ) (b := ξ₀ + δ)) hgi
  linarith [setIntegral_spectralDensity_le hF hFc hr hsupp ξ₀ hδ, hsplit, hmass]

/-! ### The polar side in spectral coordinates

The polar comparison `∫_0^T cosh(s/2)A(s)ds` of the prime side is, like the prime side itself, a
pairing against the spectral density: its symbol is the finite cosine moment of the polar density,
`K_T(b) = ∫_0^T cosh(s/2)cos(bs)ds`, which has the closed form below and is bounded by
`2 sinh(T/2) + cosh(T/2)` uniformly in `b`.  The whole prime–polar balance of the ledger is then a
single integral of the signed symbol `S(ξ) − 2K_T(2πξ)` against a nonnegative density. -/

/-- The finite cosine moment of the polar density. -/
noncomputable def coshCosKernel (T b : ℝ) : ℝ :=
  ((1 / 2) * Real.sinh (T / 2) * Real.cos (b * T)
    + b * Real.cosh (T / 2) * Real.sin (b * T)) / (1 / 4 + b ^ 2)

theorem integral_cosh_mul_cos (T b : ℝ) :
    (∫ s in (0:ℝ)..T, Real.cosh (s / 2) * Real.cos (b * s)) = coshCosKernel T b := by
  have hb : (0:ℝ) < 1 / 4 + b ^ 2 := by positivity
  have hderiv : ∀ s : ℝ, HasDerivAt (fun u : ℝ =>
      ((1 / 2) * Real.sinh (u / 2) * Real.cos (b * u)
        + b * Real.cosh (u / 2) * Real.sin (b * u)) / (1 / 4 + b ^ 2))
      (Real.cosh (s / 2) * Real.cos (b * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
    have h2 : HasDerivAt (fun u : ℝ => b * u) b s := by
      simpa using (hasDerivAt_id s).const_mul b
    have hsinh := h1.sinh
    have hcosh := h1.cosh
    have hcos := h2.cos
    have hsin := h2.sin
    have hnum := ((((hsinh.const_mul (1/2 : ℝ)).mul hcos).add
      ((hcosh.const_mul b).mul hsin))).div_const (1 / 4 + b ^ 2)
    have hval : (1 / 2 * (Real.cosh (s / 2) * (1 / 2)) * Real.cos (b * s)
        + 1 / 2 * Real.sinh (s / 2) * (-Real.sin (b * s) * b)
        + (b * (Real.sinh (s / 2) * (1 / 2)) * Real.sin (b * s)
          + b * Real.cosh (s / 2) * (Real.cos (b * s) * b))) / (1 / 4 + b ^ 2)
        = Real.cosh (s / 2) * Real.cos (b * s) := by
      rw [div_eq_iff (ne_of_gt hb)]
      ring
    rw [hval] at hnum
    exact hnum
  have hcont : IntervalIntegrable (fun s : ℝ => Real.cosh (s / 2) * Real.cos (b * s))
      MeasureTheory.volume 0 T :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)) |>.intervalIntegrable 0 T
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hcont, coshCosKernel]
  simp

theorem abs_coshCosKernel_le (T b : ℝ) (hT : 0 ≤ T) :
    |coshCosKernel T b| ≤ 2 * Real.sinh (T / 2) + Real.cosh (T / 2) := by
  have hden : (0:ℝ) < 1 / 4 + b ^ 2 := by positivity
  have hb : |b| ≤ 1 / 4 + b ^ 2 := by nlinarith [sq_nonneg (|b| - 1 / 2), sq_abs b]
  have hsinh : 0 ≤ Real.sinh (T / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hcosh : 0 < Real.cosh (T / 2) := Real.cosh_pos _
  rw [coshCosKernel, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h1 : |1 / 2 * Real.sinh (T / 2) * Real.cos (b * T)
      + b * Real.cosh (T / 2) * Real.sin (b * T)|
      ≤ 1 / 2 * Real.sinh (T / 2) + |b| * Real.cosh (T / 2) := by
    refine le_trans (abs_add_le _ _) ?_
    have ha : |1 / 2 * Real.sinh (T / 2) * Real.cos (b * T)| ≤ 1 / 2 * Real.sinh (T / 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * Real.sinh (T / 2))]
      nlinarith [Real.abs_cos_le_one (b * T), abs_nonneg (Real.cos (b * T))]
    have hbb : |b * Real.cosh (T / 2) * Real.sin (b * T)| ≤ |b| * Real.cosh (T / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hcosh]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
    linarith
  nlinarith [h1, hb, hcosh, hsinh, sq_nonneg b]

theorem integrable_coshCosKernel_mul (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ξ : ℝ => coshCosKernel T (2 * Real.pi * ξ) * spectralDensity F ξ) := by
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hgc : Continuous (spectralDensity F) := continuous_spectralDensity hF.continuous hFc
  have hKc : Continuous fun ξ : ℝ => coshCosKernel T (2 * Real.pi * ξ) := by
    have hden : Continuous fun ξ : ℝ => 1 / 4 + (2 * Real.pi * ξ) ^ 2 := by fun_prop
    have hne : ∀ ξ : ℝ, 1 / 4 + (2 * Real.pi * ξ) ^ 2 ≠ 0 := fun ξ => by positivity
    have hnum : Continuous fun ξ : ℝ =>
        1 / 2 * Real.sinh (T / 2) * Real.cos (2 * Real.pi * ξ * T)
          + 2 * Real.pi * ξ * Real.cosh (T / 2) * Real.sin (2 * Real.pi * ξ * T) := by fun_prop
    unfold coshCosKernel
    exact hnum.div hden hne
  refine Integrable.mono' (hgi.norm.const_mul (2 * Real.sinh (T / 2) + Real.cosh (T / 2)))
    (hKc.mul hgc).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_coshCosKernel_le T (2 * Real.pi * ξ) hT) (abs_nonneg _)

/-- **The prime–polar balance in spectral coordinates.** -/

theorem integral_cosh_mul_autoCorrelation_spectral (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..T, Real.cosh (s / 2) * autoCorrelation F s)
      = ∫ ξ : ℝ, coshCosKernel T (2 * Real.pi * ξ) * spectralDensity F ξ := by
  have hgi : Integrable (spectralDensity F) := integrable_spectralDensity hF hFc
  have hgc : Continuous (spectralDensity F) := continuous_spectralDensity hF.continuous hFc
  have hgnn : ∀ ξ, 0 ≤ spectralDensity F ξ := fun ξ => by rw [spectralDensity]; positivity
  have hcont : Continuous fun p : ℝ × ℝ =>
      Real.cosh (p.1 / 2) * Real.cos (2 * Real.pi * p.1 * p.2) * spectralDensity F p.2 :=
    ((Real.continuous_cosh.comp (continuous_fst.div_const 2)).mul
      (Real.continuous_cos.comp (by fun_prop))).mul (hgc.comp continuous_snd)
  have hcoshint : Integrable (fun s : ℝ => Real.cosh (s / 2)) (volume.restrict (Set.Ioc 0 T)) :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).integrableOn_Icc
      (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self
  have hprodint : Integrable (fun p : ℝ × ℝ =>
      Real.cosh (p.1 / 2) * Real.cos (2 * Real.pi * p.1 * p.2) * spectralDensity F p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod volume) := by
    refine Integrable.mono' (MeasureTheory.Integrable.mul_prod hcoshint hgi)
      hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |Real.cosh (p.1 / 2)| = Real.cosh (p.1 / 2) :=
      abs_of_nonneg ((Real.cosh_pos _).le)
    have h2 : |spectralDensity F p.2| = spectralDensity F p.2 := abs_of_nonneg (hgnn _)
    rw [h1, h2]
    have h3 : |Real.cos (2 * Real.pi * p.1 * p.2)| ≤ 1 := Real.abs_cos_le_one _
    have hc0 : 0 ≤ Real.cosh (p.1 / 2) := (Real.cosh_pos _).le
    have hg0 : 0 ≤ spectralDensity F p.2 := hgnn _
    calc Real.cosh (p.1 / 2) * |Real.cos (2 * Real.pi * p.1 * p.2)| * spectralDensity F p.2
        ≤ Real.cosh (p.1 / 2) * 1 * spectralDensity F p.2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc0) hg0
      _ = Real.cosh (p.1 / 2) * spectralDensity F p.2 := by ring
  rw [intervalIntegral.integral_of_le hT]
  have hinner : ∀ s : ℝ, Real.cosh (s / 2) * autoCorrelation F s
      = ∫ ξ : ℝ, Real.cosh (s / 2) * Real.cos (2 * Real.pi * s * ξ) * spectralDensity F ξ := by
    intro s
    rw [autoCorrelation_eq_integral_spectral hF hFc s, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => hinner s),
    MeasureTheory.integral_integral_swap hprodint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∫ s in Set.Ioc 0 T, Real.cosh (s / 2) * Real.cos (2 * Real.pi * s * ξ) * spectralDensity F ξ)
    = coshCosKernel T (2 * Real.pi * ξ) * spectralDensity F ξ
  rw [MeasureTheory.integral_mul_const]
  congr 1
  rw [← intervalIntegral.integral_of_le hT, ← integral_cosh_mul_cos T (2 * Real.pi * ξ)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show 2 * Real.pi * ξ * s = 2 * Real.pi * s * ξ by ring]

theorem prime_polar_balance_spectral (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (L : List (ℝ × ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    eulerRaw L (autoCorrelation F)
        - 2 * ∫ s in (0:ℝ)..T, Real.cosh (s / 2) * autoCorrelation F s
      = ∫ ξ : ℝ, (lagSymbol L ξ - 2 * coshCosKernel T (2 * Real.pi * ξ)) * spectralDensity F ξ := by
  have h1 := eulerRaw_eq_integral_symbol hF hFc L
  have h2 := integral_cosh_mul_autoCorrelation_spectral hF hFc hT
  have hint1 := integrable_lagSymbol_mul hF hFc L
  have hint2 := integrable_coshCosKernel_mul hF hFc hT
  have hsplit : (∫ ξ : ℝ, (lagSymbol L ξ - 2 * coshCosKernel T (2 * Real.pi * ξ)) * spectralDensity F ξ)
      = (∫ ξ : ℝ, lagSymbol L ξ * spectralDensity F ξ)
        - 2 * ∫ ξ : ℝ, coshCosKernel T (2 * Real.pi * ξ) * spectralDensity F ξ := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hint1 (hint2.const_mul 2)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  rw [hsplit, ← h1, ← h2]

/-! ### Where the pole pays, and whether a test can go there

On a finite lag window the polar symbol is not of one sign: it is nonnegative up to the first
quarter period and strictly negative at three quarters, so the pole pays only in the frequency
band `|ξ| ≤ 1/(8r)` of the window `T = 2r` and works against the test on an explicit band beyond
it.  An odd test cannot exploit the paying band: its spectral density vanishes quadratically at
the origin, so the mass it can place there is cubically small in the band width. -/

/-- Below the first quarter period the polar symbol is nonnegative. -/
theorem coshCosKernel_nonneg {T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) (hbT : b * T ≤ Real.pi / 2) :
    0 ≤ coshCosKernel T b := by
  have hsinh : 0 ≤ Real.sinh (T / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hcosh : 0 < Real.cosh (T / 2) := Real.cosh_pos _
  have hbT0 : 0 ≤ b * T := mul_nonneg hb hT
  have hcos : 0 ≤ Real.cos (b * T) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hbT⟩
  have hsin : 0 ≤ Real.sin (b * T) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hbT0 (by linarith [Real.pi_pos])
  have hden : (0:ℝ) < 1 / 4 + b ^ 2 := by positivity
  rw [coshCosKernel]
  positivity

/-- At three quarters of a period the polar symbol is strictly negative: on that band the pole
adds to the cost instead of paying it. -/
theorem coshCosKernel_neg {T : ℝ} (hT : 0 < T) :
    coshCosKernel T (3 * Real.pi / (2 * T)) < 0 := by
  set b := 3 * Real.pi / (2 * T) with hb
  have hbpos : 0 < b := by
    rw [hb]
    positivity
  have hbT : b * T = 3 * Real.pi / 2 := by
    rw [hb]
    field_simp
  have hcos : Real.cos (b * T) = 0 := by
    rw [hbT]
    have : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_pi]
    ring
  have hsin : Real.sin (b * T) = -1 := by
    rw [hbT]
    have : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [this, Real.sin_add_pi_div_two, Real.cos_pi]
  have hcosh : 0 < Real.cosh (T / 2) := Real.cosh_pos _
  have hden : (0:ℝ) < 1 / 4 + b ^ 2 := by positivity
  rw [coshCosKernel, hcos, hsin, div_neg_iff]
  right
  constructor
  · nlinarith [hbpos, hcosh]
  · exact hden

open FourierTransform Complex in
/-- An odd test has no spectral mass at the origin. -/
theorem fourier_ofReal_zero_of_odd (hodd : ∀ x, F (-x) = -F x) :
    𝓕 (fun x => ((F x : ℝ) : ℂ)) 0 = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ v : ℝ, Complex.exp (((-2 * Real.pi * v * 0 : ℝ)) * I) • ((F v : ℝ) : ℂ)
      = ((F v : ℝ) : ℂ) := by
    intro v
    rw [show (-2 * Real.pi * v * 0 : ℝ) = 0 by ring]
    simp
  have hre : (∫ a : ℝ, ((F a : ℝ) : ℂ)) = ((∫ a : ℝ, F a : ℝ) : ℂ) := integral_ofReal
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), hre,
    integral_eq_zero_of_odd hodd, Complex.ofReal_zero]

open FourierTransform Complex in
open FourierTransform Complex in
/-- An odd test's spectral density vanishes quadratically at the origin. -/
theorem spectralDensity_le_sq_of_odd (hF : Continuous F) (hFc : HasCompactSupport F) {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) (ξ : ℝ) :
    spectralDensity F ξ ≤ 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2 := by
  have hlip := norm_fourier_sub_le hF hFc hsupp ξ 0
  rw [fourier_ofReal_zero_of_odd hodd, sub_zero, sub_zero] at hlip
  have h0 : 0 ≤ ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ := norm_nonneg _
  have hexp : ((2 * Real.pi * r * (∫ x : ℝ, |F x|)) * |ξ|) * ((2 * Real.pi * r * (∫ x : ℝ, |F x|)) * |ξ|)
      = 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2 := by
    rw [← sq_abs ξ]
    ring
  rw [spectralDensity, sq]
  calc ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖ * ‖𝓕 (fun x => ((F x : ℝ) : ℂ)) ξ‖
      ≤ ((2 * Real.pi * r * (∫ x : ℝ, |F x|)) * |ξ|) * ((2 * Real.pi * r * (∫ x : ℝ, |F x|)) * |ξ|) :=
        mul_self_le_mul_self h0 hlip
    _ = 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2 := hexp

/-- The spectral mass an odd test can place in a window about the origin is cubically small. -/
theorem setIntegral_spectralDensity_le_of_odd (hF : Continuous F) (hFc : HasCompactSupport F)
    {r : ℝ} (hsupp : ∀ y, r < |y| → F y = 0) (hodd : ∀ x, F (-x) = -F x) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ ξ in Set.Icc (-δ) δ, spectralDensity F ξ)
      ≤ (8 / 3) * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * δ ^ 3 := by
  have hgc : Continuous (spectralDensity F) := continuous_spectralDensity hF hFc
  have hCcont : Continuous fun ξ : ℝ => 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2 := by
    fun_prop
  have hmono : (∫ ξ in Set.Icc (-δ) δ, spectralDensity F ξ)
      ≤ ∫ ξ in Set.Icc (-δ) δ, 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2 :=
    MeasureTheory.setIntegral_mono_on (hgc.integrableOn_Icc) (hCcont.integrableOn_Icc)
      measurableSet_Icc (fun ξ _ => spectralDensity_le_sq_of_odd hF hFc hsupp hodd ξ)
  have hval : (∫ ξ in Set.Icc (-δ) δ, 4 * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * ξ ^ 2)
      = (8 / 3) * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * δ ^ 3 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -δ ≤ δ),
      intervalIntegral.integral_const_mul, integral_pow]
    ring
  linarith [hmono, hval]

/-- For the window `T = 2r` the polar symbol is nonnegative on `|ξ| ≤ 1/(8r)`. -/
theorem coshCosKernel_nonneg_band {r ξ : ℝ} (hr : 0 < r) (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / (8 * r)) : 0 ≤ coshCosKernel (2 * r) (2 * Real.pi * ξ) := by
  refine coshCosKernel_nonneg (by linarith) (by positivity) ?_
  have hbT : 2 * Real.pi * ξ * (2 * r) = 4 * Real.pi * r * ξ := by ring
  rw [hbT]
  have hle : 4 * Real.pi * r * ξ ≤ 4 * Real.pi * r * (1 / (8 * r)) :=
    mul_le_mul_of_nonneg_left hξ (by positivity)
  have hval : 4 * Real.pi * r * (1 / (8 * r)) = Real.pi / 2 := by
    field_simp
    ring
  linarith

/-- **The pole's paying band is cubically small for an odd test.** -/
theorem setIntegral_spectralDensity_payingBand_le (hF : Continuous F)
    (hFc : HasCompactSupport F) {r : ℝ} (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0)
    (hodd : ∀ x, F (-x) = -F x) :
    (∫ ξ in Set.Icc (-(1 / (8 * r))) (1 / (8 * r)), spectralDensity F ξ)
      ≤ Real.pi ^ 2 * (∫ x : ℝ, |F x|) ^ 2 / (192 * r) := by
  have h := setIntegral_spectralDensity_le_of_odd hF hFc hsupp hodd
    (δ := 1 / (8 * r)) (by positivity)
  have hval : (8 / 3) * Real.pi ^ 2 * r ^ 2 * (∫ x : ℝ, |F x|) ^ 2 * (1 / (8 * r)) ^ 3
      = Real.pi ^ 2 * (∫ x : ℝ, |F x|) ^ 2 / (192 * r) := by
    field_simp
    ring
  linarith [h, hval]

#print axioms coshCosKernel_neg
#print axioms setIntegral_spectralDensity_payingBand_le
#print axioms spectralDensity_le_sq_of_odd

end GaloisForLFunctions.ArithmeticIncidencePositivity
