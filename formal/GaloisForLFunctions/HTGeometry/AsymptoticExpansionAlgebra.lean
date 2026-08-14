import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The algebra of Poincaré asymptotic expansions at the origin

A function of a positive real variable admits a formal power series as a Poincaré asymptotic
expansion at `0` when every partial sum approximates it to the corresponding order.  Such expansions
add and multiply, and a function determines its expansion uniquely, so the assignment carries the
algebra of functions admitting an expansion into formal power series.

Consequently a polynomial identity between functions carrying expansions is an identity between the
expansions: an algebraic relation satisfied by an asymptotic family passes to the formal tail, even
when that tail diverges.  This is the transfer step of a Gevrey-slope argument, where an analytic
solution satisfies an algebraic differential equation and one needs the divergent formal series to
satisfy the same equation.
-/

open Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

/-- The filter of positive reals tending to the origin. -/
abbrev originRight : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)

/-- `φ` is a Poincaré asymptotic expansion of `F` at the origin from the right. -/
def IsAsymptoticExpansion (F : ℝ → ℂ) (φ : PowerSeries ℂ) : Prop :=
  ∀ N : ℕ, (fun t : ℝ => F t - ∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
    =O[originRight] fun t : ℝ => (t : ℂ) ^ N

/-! ### Elementary bounds -/

theorem eventually_norm_le_one : ∀ᶠ t : ℝ in originRight, ‖(t : ℂ)‖ ≤ 1 := by
  have h : ∀ᶠ t : ℝ in originRight, |t| < 1 := by
    have hball := Metric.ball_mem_nhds (0 : ℝ) one_pos
    filter_upwards [nhdsWithin_le_nhds hball] with t ht
    simpa [Real.dist_eq] using ht
  filter_upwards [h] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_of_lt ht

theorem isBigO_pow_one (m : ℕ) :
    (fun t : ℝ => (t : ℂ) ^ m) =O[originRight] fun _ : ℝ => (1 : ℂ) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_norm_le_one] with t ht
  rw [norm_pow, norm_one, mul_one]
  exact pow_le_one₀ (norm_nonneg _) ht

theorem isBigO_pow_le {N m : ℕ} (hm : N ≤ m) :
    (fun t : ℝ => (t : ℂ) ^ m) =O[originRight] fun t : ℝ => (t : ℂ) ^ N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_norm_le_one] with t ht
  rw [one_mul, pow_add, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ht

/-- A finite sum of functions dominated by `h` is dominated by `h`. -/
theorem isBigO_finsetSum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (h : ℝ → ℂ)
    (hg : ∀ i ∈ s, g i =O[originRight] h) :
    (fun t => ∑ i ∈ s, g i t) =O[originRight] h := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Asymptotics.isBigO_zero h originRight
  | insert a s ha ih =>
      have hfun : (fun t : ℝ => ∑ i ∈ insert a s, g i t)
          = fun t : ℝ => g a t + ∑ i ∈ s, g i t := by
        funext t
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

/-- A partial sum of an expansion is bounded near the origin. -/
theorem isBigO_partialSum_one (φ : PowerSeries ℂ) (N : ℕ) :
    (fun t : ℝ => ∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
      =O[originRight] fun _ : ℝ => (1 : ℂ) := by
  refine isBigO_finsetSum _ (fun k t => PowerSeries.coeff k φ * (t : ℂ) ^ k) _ ?_
  intro k _
  exact (isBigO_pow_one k).const_mul_left (PowerSeries.coeff k φ)

/-- A function with an expansion is bounded near the origin. -/
theorem IsAsymptoticExpansion.isBigO_one {F : ℝ → ℂ} {φ : PowerSeries ℂ}
    (hF : IsAsymptoticExpansion F φ) : F =O[originRight] fun _ : ℝ => (1 : ℂ) := by
  simpa using hF 0

/-! ### Uniqueness -/

/-- The zero function has only the zero expansion, so a function determines its expansion. -/
theorem eq_zero_of_isAsymptoticExpansion_zero {φ : PowerSeries ℂ}
    (h : IsAsymptoticExpansion (fun _ => 0) φ) : φ = 0 := by
  ext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      have hlow : ∀ k ∈ Finset.range m, PowerSeries.coeff k φ = 0 := by
        intro k hk
        simpa using ih k (Finset.mem_range.mp hk)
      have hsum : ∀ t : ℝ,
          (0 : ℂ) - ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k φ * (t : ℂ) ^ k
            = -(PowerSeries.coeff m φ * (t : ℂ) ^ m) := by
        intro t
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by rw [hlow k hk, zero_mul])]
        ring
      obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (h (m + 1))
      have hbound : ∀ᶠ t : ℝ in originRight, ‖PowerSeries.coeff m φ‖ ≤ C * t := by
        filter_upwards [hC, self_mem_nhdsWithin] with t ht htpos
        have htpos' : (0 : ℝ) < t := htpos
        rw [hsum t] at ht
        simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos'] at ht
        have htm : (0 : ℝ) < t ^ m := pow_pos htpos' m
        have ht' : ‖PowerSeries.coeff m φ‖ * t ^ m ≤ (C * t) * t ^ m := by
          rw [show (C * t) * t ^ m = C * t ^ (m + 1) by ring]
          exact ht
        exact le_of_mul_le_mul_right ht' htm
      have htend : Tendsto (fun t : ℝ => C * t) originRight (𝓝 0) := by
        have hbase : Tendsto (fun t : ℝ => C * t) (𝓝 (0 : ℝ)) (𝓝 (C * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at hbase
        exact hbase.mono_left nhdsWithin_le_nhds
      have hle : ‖PowerSeries.coeff m φ‖ ≤ 0 := ge_of_tendsto htend hbound
      simpa using norm_le_zero_iff.mp hle

/-! ### The algebra structure -/

theorem isAsymptoticExpansion_const (c : ℂ) :
    IsAsymptoticExpansion (fun _ => c) (PowerSeries.C c) := by
  intro N
  match N with
  | 0 => simpa using Asymptotics.isBigO_const_const c (one_ne_zero (α := ℂ)) originRight
  | (n + 1) =>
      have hsum : ∀ t : ℝ,
          c - ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k (PowerSeries.C c) * (t : ℂ) ^ k
            = 0 := by
        intro t
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk
          rw [PowerSeries.coeff_C, if_neg hk, zero_mul]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hmem
      simp only [hsum]
      exact Asymptotics.isBigO_zero _ _

theorem isAsymptoticExpansion_X :
    IsAsymptoticExpansion (fun t : ℝ => (t : ℂ)) (PowerSeries.X : PowerSeries ℂ) := by
  intro N
  match N with
  | 0 => simpa using isBigO_pow_one 1
  | 1 =>
      have hsum : ∀ t : ℝ,
          (t : ℂ) - ∑ k ∈ Finset.range 1,
              PowerSeries.coeff k (PowerSeries.X : PowerSeries ℂ) * (t : ℂ) ^ k = (t : ℂ) := by
        intro t
        simp
      simp only [hsum, pow_one]
      exact Asymptotics.isBigO_refl _ _
  | (n + 2) =>
      have hsum : ∀ t : ℝ,
          (t : ℂ) - ∑ k ∈ Finset.range (n + 2),
              PowerSeries.coeff k (PowerSeries.X : PowerSeries ℂ) * (t : ℂ) ^ k = 0 := by
        intro t
        rw [Finset.sum_eq_single 1]
        · simp
        · intro k _ hk
          rw [PowerSeries.coeff_X, if_neg hk, zero_mul]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
      simp only [hsum]
      exact Asymptotics.isBigO_zero _ _

theorem IsAsymptoticExpansion.add {F G : ℝ → ℂ} {φ ψ : PowerSeries ℂ}
    (hF : IsAsymptoticExpansion F φ) (hG : IsAsymptoticExpansion G ψ) :
    IsAsymptoticExpansion (fun t => F t + G t) (φ + ψ) := by
  intro N
  have hcomb : ∀ t : ℝ,
      (F t + G t) - ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ + ψ) * (t : ℂ) ^ k
        = (F t - ∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
          + (G t - ∑ k ∈ Finset.range N, PowerSeries.coeff k ψ * (t : ℂ) ^ k) := by
    intro t
    have hterm : ∀ k : ℕ, PowerSeries.coeff k (φ + ψ) * (t : ℂ) ^ k
        = PowerSeries.coeff k φ * (t : ℂ) ^ k + PowerSeries.coeff k ψ * (t : ℂ) ^ k := by
      intro k
      rw [map_add, add_mul]
    simp only [hterm, Finset.sum_add_distrib]
    ring
  simp only [hcomb]
  exact (hF N).add (hG N)

/-- The truncated Cauchy product, as a sum over the sub-diagonal square. -/
theorem sum_range_coeff_mul_eq (φ ψ : PowerSeries ℂ) (N : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k
      = ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N),
          PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
      (fun k => Finset.antidiagonal k) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr ?_
    intro p hpa hpb
    rw [Finset.mem_antidiagonal] at hpa hpb
    exact hab (hpa.symm.trans hpb)
  have hbi : (Finset.range N).biUnion (fun k => Finset.antidiagonal k)
      = (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 < N) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨k, hk, hpk⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨-, hlt⟩
      exact ⟨p.1 + p.2, hlt, rfl⟩
  calc ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k
      = ∑ k ∈ Finset.range N, ∑ p ∈ Finset.antidiagonal k,
          PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [PowerSeries.coeff_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_antidiagonal.mp hp]
    _ = ∑ p ∈ (Finset.range N).biUnion (fun k => Finset.antidiagonal k),
          PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2) :=
        (Finset.sum_biUnion hdisj).symm
    _ = _ := by rw [hbi]

theorem IsAsymptoticExpansion.mul {F G : ℝ → ℂ} {φ ψ : PowerSeries ℂ}
    (hF : IsAsymptoticExpansion F φ) (hG : IsAsymptoticExpansion G ψ) :
    IsAsymptoticExpansion (fun t => F t * G t) (φ * ψ) := by
  classical
  intro N
  have hkey : ∀ t : ℝ,
      (∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
          * (∑ k ∈ Finset.range N, PowerSeries.coeff k ψ * (t : ℂ) ^ k)
        - ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k
      = ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => ¬ (p.1 + p.2 < N)),
          PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2) := by
    intro t
    rw [sum_range_coeff_mul_eq φ ψ N t, Finset.sum_mul_sum, ← Finset.sum_product']
    have hterm : ∀ p : ℕ × ℕ,
        (PowerSeries.coeff p.1 φ * (t : ℂ) ^ p.1) * (PowerSeries.coeff p.2 ψ * (t : ℂ) ^ p.2)
          = PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2) := by
      intro p
      rw [pow_add]
      ring
    simp only [hterm]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N ×ˢ Finset.range N)
      (fun p => p.1 + p.2 < N)]
    ring
  have htail : (fun t : ℝ =>
      (∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
          * (∑ k ∈ Finset.range N, PowerSeries.coeff k ψ * (t : ℂ) ^ k)
        - ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k)
      =O[originRight] fun t : ℝ => (t : ℂ) ^ N := by
    simp only [hkey]
    refine isBigO_finsetSum _
      (fun (p : ℕ × ℕ) (t : ℝ) =>
        PowerSeries.coeff p.1 φ * PowerSeries.coeff p.2 ψ * (t : ℂ) ^ (p.1 + p.2)) _ ?_
    intro p hp
    have hge : N ≤ p.1 + p.2 := by
      have := (Finset.mem_filter.mp hp).2
      omega
    exact (isBigO_pow_le hge).const_mul_left _
  have hdecomp : ∀ t : ℝ,
      F t * G t - ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k
        = (F t - ∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k) * G t
          + (∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
            * (G t - ∑ k ∈ Finset.range N, PowerSeries.coeff k ψ * (t : ℂ) ^ k)
          + ((∑ k ∈ Finset.range N, PowerSeries.coeff k φ * (t : ℂ) ^ k)
              * (∑ k ∈ Finset.range N, PowerSeries.coeff k ψ * (t : ℂ) ^ k)
            - ∑ k ∈ Finset.range N, PowerSeries.coeff k (φ * ψ) * (t : ℂ) ^ k) := by
    intro t
    ring
  simp only [hdecomp]
  refine (Asymptotics.IsBigO.add ?_ ?_).add htail
  · simpa using (hF N).mul hG.isBigO_one
  · simpa using (isBigO_partialSum_one φ N).mul (hG N)

/-! ### Transfer of polynomial identities -/

/-- **A polynomial identity passes to the expansions.**  Evaluating a polynomial on functions that
carry asymptotic expansions gives a function whose expansion is that polynomial evaluated on the
expansions. -/
theorem IsAsymptoticExpansion.aeval {σ : Type*} {F : σ → ℝ → ℂ} {Φ : σ → PowerSeries ℂ}
    (h : ∀ i, IsAsymptoticExpansion (F i) (Φ i)) (P : MvPolynomial σ ℂ) :
    IsAsymptoticExpansion (fun t => MvPolynomial.aeval (fun i => F i t) P)
      (MvPolynomial.aeval Φ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hbase : (MvPolynomial.aeval Φ (MvPolynomial.C a) : PowerSeries ℂ)
          = PowerSeries.C a := by
        rw [MvPolynomial.aeval_C]
        rfl
      have hfun : (fun t : ℝ => MvPolynomial.aeval (fun i => F i t) (MvPolynomial.C a))
          = fun _ : ℝ => a := by
        funext t
        rw [MvPolynomial.aeval_C]
        rfl
      rw [hbase, hfun]
      exact isAsymptoticExpansion_const a
  | add p q hp hq =>
      have hfun : (fun t : ℝ => MvPolynomial.aeval (fun i => F i t) (p + q))
          = fun t : ℝ => MvPolynomial.aeval (fun i => F i t) p
            + MvPolynomial.aeval (fun i => F i t) q := by
        funext t
        rw [map_add]
      rw [hfun, map_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hfun : (fun t : ℝ => MvPolynomial.aeval (fun i => F i t) (p * MvPolynomial.X i))
          = fun t : ℝ => MvPolynomial.aeval (fun i => F i t) p * F i t := by
        funext t
        rw [map_mul, MvPolynomial.aeval_X]
      rw [hfun, map_mul, MvPolynomial.aeval_X]
      exact hp.mul (h i)

/-- **The formal tail satisfies every polynomial relation of the analytic family.**  If a polynomial
vanishes on a family of functions carrying asymptotic expansions, it vanishes on those expansions as
formal power series — even when they diverge. -/
theorem aeval_powerSeries_eq_zero_of_eq_zero {σ : Type*} {F : σ → ℝ → ℂ}
    {Φ : σ → PowerSeries ℂ} (h : ∀ i, IsAsymptoticExpansion (F i) (Φ i))
    {P : MvPolynomial σ ℂ}
    (hzero : ∀ t : ℝ, MvPolynomial.aeval (fun i => F i t) P = 0) :
    MvPolynomial.aeval Φ P = 0 := by
  have hexp := IsAsymptoticExpansion.aeval h P
  have hfun : (fun t : ℝ => MvPolynomial.aeval (fun i => F i t) P) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    exact hzero t
  rw [hfun] at hexp
  exact eq_zero_of_isAsymptoticExpansion_zero hexp

end GaloisForLFunctions.HTGeometry
