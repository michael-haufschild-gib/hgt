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
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _
      (fun i _ => integrable_diff_sq_shift hF hFc ((i : ℝ) * t) t)] at hmono
  simp only [integral_diff_sq_shift hF hFc, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hmono
  have e1 := two_mul_displacement_eq hF hFc ((k : ℝ) * t)
  nlinarith [hmono, e1]

theorem autoCorrelation_zero_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) :
    0 ≤ autoCorrelation F 0 := by
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
  have hA0 := autoCorrelation_zero_nonneg hF hFc
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

end GaloisForLFunctions.ArithmeticIncidencePositivity
