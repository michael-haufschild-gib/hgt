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
    rw [← hsq, mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrt2), mul_one]
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

end GaloisForLFunctions.ArithmeticIncidencePositivity

