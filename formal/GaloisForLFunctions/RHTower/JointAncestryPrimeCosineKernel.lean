import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAttainment
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity

/-!
# Large-prime JAS positivity as positivity against prime cosine kernels

For a finite set `P` of primes and a level `σ` let
`K_P(s) = ∏_{p ∈ P} (1 + p^{−σ} cosh((s − ½) log p))`.  On the critical line
`K_P(½ + iu) = ∏_{p ∈ P} (1 + p^{−σ} cos(u log p))`, which is positive for `σ > 0`
(`jasCosineKernel_critical`, `jasCosineKernel_critical_pos`).

* **Product tests are cosine tests** (`jasProductPositiveAbove_iff_jasCosinePositiveAbove`).  At every
  level `σ`, positivity of the Bernoulli product tests on the primes `p > X` is equivalent to
  `Re Σ_ρ K_P(ρ − it)/(ρ(1−ρ)) ≥ 0` for every finite set `P` of primes `> X` and every real `t`.
  At `z = r u` with `|u| = 1` the Bernoulli factor is `(1 − r)² + 2r(1 + (uA + ūB)/2)`
  (`jasBernoulliFactor_eq_unit`).  So a product test is a nonnegative combination of unit-modulus
  tests on the subsets of `P`.  The aggregate of unit-modulus tests is continuous in the phases.  By
  Kronecker's theorem the phases `(p^{it})_{p ∈ P}` are dense in the torus.  At `u_p = p^{it}` the
  unit factor is `1 + p^{−σ} cosh((ρ − it − ½) log p)` (`jasUnitFactor_kronecker`).
* **Capstone** (`riemannHypothesis_iff_exists_jasCosinePositiveAbove_one_and_quasi`).  RH holds iff
  two conditions hold.  First, for some `X`, the zero measure `Σ_ρ δ_ρ/(ρ(1−ρ))` is nonnegative
  against every vertical translate of every kernel `K_P` at `σ = 1`, with `P` a finite set of primes
  `> X`.  Second, some half-plane bound below `½` holds.
  Expanding the product gives
  `Σ_ρ K_P(ρ − it)/(ρ(1−ρ)) = Σ_{k ∈ {−1,0,1}^P} 2^{−|k|} e^{−σ⟨|k|, log p⟩} Φ(⟨k, log p⟩) e^{−it⟨k, log p⟩}`,
  with `Φ` the Weil lag function.  So the condition says that `Φ`, weighted by the symmetric walk
  with steps `± log p` of weight `p^{−σ}/2`, has a nonnegative Fourier transform at every
  frequency.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The prime cosine kernel `K_P(s) = ∏_{p ∈ P} (1 + p^{−σ} cosh((s − ½) log p))`. -/
def jasCosineKernel (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 + (Real.exp (-σ * Real.log p) : ℂ) * Complex.cosh ((s - 1 / 2) * (Real.log p : ℂ)))

/-- Nonnegativity of the zero measure against all vertical translates of the cosine kernels on
finite sets of primes `p > X`. -/
def JasCosinePositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ t : ℝ,
    0 ≤ (∑' q : XiZeroCopy, jasCosineKernel P σ ((q.1 : ℂ) - (t : ℂ) * I) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

/-- On the critical line the cosine kernel is the cosine product
`∏_{p ∈ P} (1 + p^{−σ} cos(u log p))`. -/
theorem jasCosineKernel_critical (P : Finset Nat.Primes) (σ u : ℝ) :
    jasCosineKernel P σ (1 / 2 + (u : ℂ) * I) =
      ((∏ p ∈ P, (1 + Real.exp (-σ * Real.log p) * Real.cos (u * Real.log p)) : ℝ) : ℂ) := by
  rw [jasCosineKernel, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [show (1 / 2 + (u : ℂ) * I - 1 / 2) * (Real.log p : ℂ) = ((u * Real.log p : ℝ) : ℂ) * I by
    push_cast; ring, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  push_cast
  ring

theorem jasCosineKernel_critical_pos (P : Finset Nat.Primes) {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    0 < ∏ p ∈ P, (1 + Real.exp (-σ * Real.log p) * Real.cos (u * Real.log p)) := by
  refine Finset.prod_pos fun p _ => ?_
  have h1 : Real.exp (-σ * Real.log p) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have h0 := Real.exp_pos (-σ * Real.log p)
  nlinarith [Real.neg_one_le_cos (u * Real.log p)]

/-! ## Unit-modulus factors -/

/-- The unit-modulus Bernoulli factor `1 + (uA + ūB)/2`. -/
def jasUnitFactor (A B u : ℂ) : ℂ := 1 + (u * A + conj u * B) / 2

/-- At `z = r u` with `u ū = 1` the Bernoulli factor is `(1 − r)² + 2r(1 + (uA + ūB)/2)`. -/
theorem jasBernoulliFactor_eq_unit (A B u : ℂ) (r : ℝ) (hu : u * conj u = 1) :
    jasBernoulliFactor A B ((r : ℂ) * u) =
      (((1 - r) ^ 2 : ℝ) : ℂ) + ((2 * r : ℝ) : ℂ) * jasUnitFactor A B u := by
  have h : (r : ℂ) * u * conj ((r : ℂ) * u) = (r : ℂ) ^ 2 := by
    rw [map_mul, Complex.conj_ofReal]
    calc (r : ℂ) * u * ((r : ℂ) * conj u) = (r : ℂ) ^ 2 * (u * conj u) := by ring
      _ = (r : ℂ) ^ 2 := by rw [hu, mul_one]
  rw [jasBernoulliFactor, h, jasUnitFactor, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- **The unit factor at the Kronecker point** `u_p = p^{it}` is
`1 + p^{−σ} cosh((ρ − it − ½) log p)`. -/
theorem jasUnitFactor_kronecker (q : ℂ) (σ t : ℝ) (p : Nat.Primes) :
    jasUnitFactor (jasHoloA (q + ((σ - 1 / 2 : ℝ) : ℂ)) p) (jasHoloB (q - ((σ - 1 / 2 : ℝ) : ℂ)) p)
        (cexp (((Real.log p * t : ℝ) : ℂ) * I)) =
      1 + (Real.exp (-σ * Real.log p) : ℂ) *
        Complex.cosh ((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ)) := by
  have hc : conj (cexp (((Real.log p * t : ℝ) : ℂ) * I)) =
      cexp (-(((Real.log p * t : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have h1 : cexp (((Real.log p * t : ℝ) : ℂ) * I) * jasHoloA (q + ((σ - 1 / 2 : ℝ) : ℂ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) *
        cexp (-((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ))) := by
    rw [jasHoloA, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : conj (cexp (((Real.log p * t : ℝ) : ℂ) * I)) * jasHoloB (q - ((σ - 1 / 2 : ℝ) : ℂ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) * cexp ((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ)) := by
    rw [hc, jasHoloB, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [jasUnitFactor, h1, h2, show Complex.cosh ((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ)) =
    (cexp ((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ)) +
      cexp (-((q - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ)))) / 2 from rfl]
  ring

theorem norm_jasUnitFactor_le {q : ℂ} {c : ℝ} (h0 : 0 < q.re) (h1 : q.re < 1)
    (p : Nat.Primes) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    ‖jasUnitFactor (jasHoloA (q + c) p) (jasHoloB (q - c) p) v‖ ≤
      1 + Real.exp (|c| * Real.log p) := by
  have hL := log_prime_pos p
  have hc := neg_abs_le c
  have hA : ‖jasHoloA (q + c) p‖ ≤ Real.exp (|c| * Real.log p) := by
    rw [norm_jasHoloA, Real.exp_le_exp, Complex.add_re, Complex.ofReal_re]
    nlinarith
  have hB : ‖jasHoloB (q - c) p‖ ≤ Real.exp (|c| * Real.log p) := by
    rw [norm_jasHoloB, Real.exp_le_exp, Complex.sub_re, Complex.ofReal_re]
    nlinarith
  have hvc : ‖conj v‖ ≤ 1 := by rwa [Complex.norm_conj]
  have hE := (Real.exp_pos (|c| * Real.log p)).le
  calc ‖jasUnitFactor (jasHoloA (q + c) p) (jasHoloB (q - c) p) v‖
      ≤ ‖(1 : ℂ)‖ + (‖v‖ * ‖jasHoloA (q + c) p‖ + ‖conj v‖ * ‖jasHoloB (q - c) p‖) / 2 := by
        rw [jasUnitFactor]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_div, Complex.norm_two]
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    _ ≤ 1 + (1 * Real.exp (|c| * Real.log p) + 1 * Real.exp (|c| * Real.log p)) / 2 := by
        rw [norm_one]
        gcongr
    _ = 1 + Real.exp (|c| * Real.log p) := by ring

/-- The unit-modulus aggregate term is dominated by `∏_{p ∈ T}(1 + p^{|σ−½|}) |w_ρ|`. -/
theorem norm_jasUnitAggregate_term_le (σ : ℝ) (T : Finset Nat.Primes)
    {v : Nat.Primes → ℂ} (hv : ∀ p, ‖v p‖ ≤ 1) (q : XiZeroCopy) :
    ‖(∏ p ∈ T, jasUnitFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (v p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (∏ p ∈ T, (1 + Real.exp (|σ - 1 / 2| * Real.log p))) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [div_eq_mul_one_div, norm_mul, norm_prod]
  gcongr with p
  exact norm_jasUnitFactor_le (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) p (hv p)

theorem summable_jasUnitAggregate (σ : ℝ) (T : Finset Nat.Primes)
    {v : Nat.Primes → ℂ} (hv : ∀ p, ‖v p‖ ≤ 1) :
    Summable fun q : XiZeroCopy => (∏ p ∈ T, jasUnitFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (v p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
  (summable_inv_mul_one_sub.norm.mul_left _).of_norm_bounded
    (norm_jasUnitAggregate_term_le σ T hv)

/-! ## Product tests and cosine tests -/

/-- **Product tests give cosine tests**: the product test at `z_p = p^{it}` is `2^{|P|}` times the
cosine test at `t`. -/
theorem JasProductPositiveAbove.cosinePositive {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ) :
    JasCosinePositiveAbove X σ := by
  intro P hP t
  have hB := h P hP fun p => cexp (((Real.log p * t : ℝ) : ℂ) * I)
  have hu : ∀ p : Nat.Primes, cexp (((Real.log p * t : ℝ) : ℂ) * I) *
      conj (cexp (((Real.log p * t : ℝ) : ℂ) * I)) = 1 := fun p => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hfac : ∀ q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (cexp (((Real.log p * t : ℝ) : ℂ) * I))) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        ((2 ^ P.card : ℝ) : ℂ) * (jasCosineKernel P σ ((q.1 : ℂ) - (t : ℂ) * I) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    have hp : ∀ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (cexp (((Real.log p * t : ℝ) : ℂ) * I)) =
        2 * (1 + (Real.exp (-σ * Real.log p) : ℂ) *
          Complex.cosh (((q.1 : ℂ) - (t : ℂ) * I - 1 / 2) * (Real.log p : ℂ))) := by
      intro p _
      have e := jasBernoulliFactor_eq_unit (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) _ 1 (hu p)
      rw [Complex.ofReal_one, one_mul, jasUnitFactor_kronecker] at e
      rw [e]
      push_cast
      ring
    rw [Finset.prod_congr rfl hp, Finset.prod_mul_distrib, Finset.prod_const, jasCosineKernel]
    push_cast
    ring
  simp_rw [hfac] at hB
  rw [tsum_mul_left, Complex.re_ofReal_mul] at hB
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hB

/-- **Unit-modulus tests from cosine tests.**  Kronecker's theorem steers the phases `p^{it}`,
`p ∈ T`, to any unit vector, and the aggregate is continuous in the phases. -/
theorem jasUnitAggregate_nonneg_of_cosinePositive {X : ℕ} {σ : ℝ}
    (h : JasCosinePositiveAbove X σ) (T : Finset Nat.Primes) (hT : ∀ p ∈ T, X < (p : ℕ))
    (u : Nat.Primes → ℂ) (hu : ∀ p, ‖u p‖ = 1) :
    0 ≤ (∑' q : XiZeroCopy, (∏ p ∈ T, jasUnitFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (u p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  classical
  obtain ⟨F, hFdef⟩ : ∃ F : (Nat.Primes → ℂ) → ℝ, F = fun v => (∑' q : XiZeroCopy,
      (∏ p ∈ T, jasUnitFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (v p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
    ⟨_, rfl⟩
  have hF : ∀ v, F v = (∑' q : XiZeroCopy,
      (∏ p ∈ T, jasUnitFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (v p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
    fun v => by rw [hFdef]
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Nat.Primes → ℂ), S = {v | ∀ p, ‖v p‖ ≤ 1} := ⟨_, rfl⟩
  have hcont : ContinuousOn F S := by
    rw [hFdef, hSdef]
    refine Complex.continuous_re.comp_continuousOn
      (continuousOn_tsum (fun q => Continuous.continuousOn ?_)
        (summable_inv_mul_one_sub.norm.mul_left _)
        fun q v hv => norm_jasUnitAggregate_term_le σ T hv q)
    refine Continuous.div_const (continuous_finsetProd _ fun p _ => ?_) _
    unfold jasUnitFactor
    fun_prop
  -- Kronecker approximation of the phase vector `u` on `T`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = T.sup fun p => (p : ℕ) := ⟨_, rfl⟩
  have hTN : ∀ p ∈ T, p ∈ GaloisForLFunctions.primesLE N := fun p hp => by
    rw [GaloisForLFunctions.mem_primesLE, hN]
    exact Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp
  have hK : ∀ n : ℕ, ∃ t : ℝ, ∀ p : GaloisForLFunctions.primesLE N,
      ‖GaloisForLFunctions.expChar (Real.log ((p : Nat.Primes) : ℕ)) t -
        cexp (((Complex.arg (u p) : ℝ) : ℂ) * I)‖ < 1 / ((n : ℝ) + 1) :=
    fun n => GaloisForLFunctions.primeTorus_kronecker_dense N (fun p => Complex.arg (u p))
      (by positivity)
  choose t ht using hK
  have huarg : ∀ p, cexp (((Complex.arg (u p) : ℝ) : ℂ) * I) = u p := fun p => by
    have := Complex.norm_mul_exp_arg_mul_I (u p)
    rwa [hu p, Complex.ofReal_one, one_mul] at this
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → Nat.Primes → ℂ, v = fun n p =>
      if p ∈ T then cexp (((Real.log p * t n : ℝ) : ℂ) * I) else u p := ⟨_, rfl⟩
  have hv_mem : ∀ n p, p ∈ T → v n p = cexp (((Real.log p * t n : ℝ) : ℂ) * I) :=
    fun n p hp => by rw [hvdef]; exact if_pos hp
  have hv_nmem : ∀ n p, p ∉ T → v n p = u p := fun n p hp => by rw [hvdef]; exact if_neg hp
  have hvS : ∀ n, v n ∈ S := fun n => by
    rw [hSdef]
    intro p
    by_cases hp : p ∈ T
    · rw [hv_mem n p hp, Complex.norm_exp_ofReal_mul_I]
    · rw [hv_nmem n p hp, hu p]
  have huS : u ∈ S := by rw [hSdef]; exact fun p => (hu p).le
  have hvlim : Tendsto v atTop (𝓝 u) := by
    refine tendsto_pi_nhds.mpr fun p => ?_
    by_cases hp : p ∈ T
    · refine Metric.tendsto_atTop.mpr fun ε hε => ?_
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
      refine ⟨M, fun n hn => ?_⟩
      have h1 := ht n ⟨p, hTN p hp⟩
      rw [GaloisForLFunctions.expChar, huarg] at h1
      rw [dist_eq_norm, hv_mem n p hp]
      calc ‖cexp (((Real.log p * t n : ℝ) : ℂ) * I) - u p‖ < 1 / ((n : ℝ) + 1) := h1
        _ ≤ 1 / ((M : ℝ) + 1) := by gcongr
        _ < ε := hM
    · rw [show (fun n => v n p) = fun _ => u p from funext fun n => hv_nmem n p hp]
      exact tendsto_const_nhds
  have hFv : ∀ n, 0 ≤ F (v n) := by
    intro n
    have heq : F (v n) = (∑' q : XiZeroCopy, jasCosineKernel T σ ((q.1 : ℂ) - (t n : ℂ) * I) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
      rw [hF]
      refine congrArg Complex.re (tsum_congr fun q => ?_)
      rw [jasCosineKernel]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hv_mem n p hp]
      exact jasUnitFactor_kronecker _ σ (t n) p
    rw [heq]
    exact h T hT (t n)
  have hlim : Tendsto (fun n => F (v n)) atTop (𝓝 (F u)) :=
    ((hcont u huS).tendsto).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hvlim, Eventually.of_forall hvS⟩)
  have := ge_of_tendsto hlim (Eventually.of_forall hFv)
  rwa [hF] at this

/-- **Cosine tests give product tests.**  A product test is a nonnegative combination of
unit-modulus tests on the subsets of `P`. -/
theorem jasProductPositiveAbove_of_cosinePositive {X : ℕ} {σ : ℝ}
    (h : JasCosinePositiveAbove X σ) : JasProductPositiveAbove X σ := by
  classical
  intro P hP z
  set r : Nat.Primes → ℝ := fun p => ‖z p‖ with hr
  set u : Nat.Primes → ℂ := fun p => cexp (((Complex.arg (z p) : ℝ) : ℂ) * I) with hudef
  have hu1 : ∀ p, ‖u p‖ = 1 := fun p => Complex.norm_exp_ofReal_mul_I _
  have huc : ∀ p, u p * conj (u p) = 1 := fun p => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1 p]
    norm_num
  have hz : ∀ p, z p = (r p : ℂ) * u p := fun p => (Complex.norm_mul_exp_arg_mul_I (z p)).symm
  set A : XiZeroCopy → Nat.Primes → ℂ := fun q p => jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p
  set B : XiZeroCopy → Nat.Primes → ℂ := fun q p => jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p
  set c : Finset Nat.Primes → ℝ := fun T =>
    (∏ p ∈ T, (1 - r p) ^ 2) * ∏ p ∈ P \ T, (2 * r p) with hcdef
  have hc0 : ∀ T, 0 ≤ c T := fun T =>
    mul_nonneg (Finset.prod_nonneg fun p _ => sq_nonneg _)
      (Finset.prod_nonneg fun p _ => mul_nonneg zero_le_two (norm_nonneg _))
  have hexp : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (A q p) (B q p) (z p)) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      ∑ T ∈ P.powerset, ((c T : ℝ) : ℂ) * ((∏ p ∈ P \ T, jasUnitFactor (A q p) (B q p) (u p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    have hfac : ∀ p, jasBernoulliFactor (A q p) (B q p) (z p) =
        (((1 - r p) ^ 2 : ℝ) : ℂ) + ((2 * r p : ℝ) : ℂ) * jasUnitFactor (A q p) (B q p) (u p) :=
      fun p => by rw [hz p]; exact jasBernoulliFactor_eq_unit _ _ _ _ (huc p)
    simp_rw [hfac]
    rw [Finset.prod_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_mul_distrib, hcdef]
    push_cast
    ring
  have hsum : ∀ T ∈ P.powerset, Summable fun q : XiZeroCopy => ((c T : ℝ) : ℂ) *
      ((∏ p ∈ P \ T, jasUnitFactor (A q p) (B q p) (u p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
    fun T _ => (summable_jasUnitAggregate σ (P \ T) fun p => (hu1 p).le).mul_left _
  have hgoal : (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (A q p) (B q p) (z p)) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re =
      ∑ T ∈ P.powerset, c T * (∑' q : XiZeroCopy,
        (∏ p ∈ P \ T, jasUnitFactor (A q p) (B q p) (u p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
    simp_rw [hexp]
    rw [Summable.tsum_finsetSum hsum, Complex.re_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tsum_mul_left, Complex.re_ofReal_mul]
  change 0 ≤ (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (A q p) (B q p) (z p)) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re
  rw [hgoal]
  refine Finset.sum_nonneg fun T _ => mul_nonneg (hc0 T) ?_
  exact jasUnitAggregate_nonneg_of_cosinePositive h (P \ T)
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) u hu1

/-- **Product tests are cosine tests.** -/
theorem jasProductPositiveAbove_iff_jasCosinePositiveAbove {X : ℕ} {σ : ℝ} :
    JasProductPositiveAbove X σ ↔ JasCosinePositiveAbove X σ :=
  ⟨JasProductPositiveAbove.cosinePositive, jasProductPositiveAbove_of_cosinePositive⟩

/-- **Cosine-kernel capstone.**  RH holds iff, for some `X`, the zero measure
`Σ_ρ δ_ρ/(ρ(1−ρ))` is nonnegative against every vertical translate of every prime cosine kernel
`K_P(s) = ∏_{p ∈ P} (1 + p^{−1} cosh((s − ½) log p))` over finite sets `P` of primes `> X`, and some
half-plane bound below `½` holds. -/
theorem riemannHypothesis_iff_exists_jasCosinePositiveAbove_one_and_quasi :
    RiemannHypothesis ↔ (∃ X : ℕ, JasCosinePositiveAbove X 1) ∧
      ∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  rw [riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi]
  constructor
  · rintro ⟨⟨X, hX⟩, hq⟩
    exact ⟨⟨X, hX.cosinePositive⟩, hq⟩
  · rintro ⟨⟨X, hX⟩, hq⟩
    exact ⟨⟨X, jasProductPositiveAbove_of_cosinePositive hX⟩, hq⟩

end

end RHTower
