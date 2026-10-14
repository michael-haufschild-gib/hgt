import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeDetection
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel

/-!
# Constant-vector JAS tests detect a maximal off-line zero at every scale

Setting. Fix a finite set `P` of primes, a level `σ` and a constant test vector `z ∈ ℂ`. The JAS
product test is

`Re Σ_ρ ∏_{p∈P} (1 + z A_p(ρ) + z̄ B_p(ρ) + |z|²)/(ρ(1−ρ))`,

where `A_p(ρ) = p^{−σ} p^{−(ρ−½)}` and `B_p(ρ) = p^{−σ} p^{ρ−½}`. Dividing by `(1 + |z|²)^{|P|}`
gives the kernel `∏_p (1 + u A_p + ū B_p)` with `u = z/(1 + |z|²)`. Here `|u| ≤ ½` and the phase
of `u` is free.

**Theorem** (`eventually_not_jasConstProductPositiveOn_of_maximal_offLine`). Suppose a zero `ρ₀` off
the critical line has the largest distance `δ` from it, and `δ < σ < 1 + δ`. Then for every `X` and
every sufficiently large `N`, some constant vector gives a negative test on the primes in `(X, N]`.

The real-amplitude detection theorem needs the edge `N` of the prime range to turn the phase of
the dominant prime sum, so it gives negative tests only for infinitely many `N`. A complex constant
vector supplies the phase itself.

**Proof.** Let `ρ* = ½ + δ + iγ` be the dominant zero: largest distance, then smallest `|γ|`. Let
`S = Σ_{X<p≤N} p^{−(σ−δ−iγ)}` be its large prime sum and `ω = S/S̄`.

* The tests at `z` and `z̄` add up to the symmetrized aggregate `Σ_ρ (K_u(ρ) + K_ū(ρ))/(ρ(1−ρ))`.
* Its terms at `ρ*, ρ̄*, 1−ρ*, 1−ρ̄*` have equal real parts.
* At `ρ*` the two kernels are `e^{Y+e₁}` and `e^{Ȳω+e₂}`, where `ūS = Y` and the `e_i` are small.
* If `ω` is close to `1`, take `Y = R + iπ`. Both kernels are then close to `−e^R`, so
  `Re w (e^{Y+e₁} + e^{Ȳω+e₂}) ≤ −(Re w) e^R`, because `Re w > 0` for `w = 1/(ρ*(1−ρ*))`.
* Otherwise take `Y = R' + i(π − arg w)` with `R'` large. The first kernel is anti-aligned with `w`,
  and the second is smaller by the factor `e^{−R'(1 − Re ω)}`.

The other zeros are dominated:

* zeros at the same distance and larger height have prime sums smaller by the fixed ratio
  `|1 − s|/|1 − s'| < 1`;
* zeros closer to the line have prime sums `o(|S|)`.

**Capstones.**

* RH holds iff the zeros approach the line and, for some `X`, constant-vector positivity holds on
  `(X, N]` for infinitely many `N`
  (`riemannHypothesis_iff_zerosApproachLine_and_frequently_jasConstProductPositiveOn`).
* The same holds with "no off-line chain" in place of the large-height condition
  (`riemannHypothesis_iff_not_jasOffLineChain_and_frequently_jasConstProductPositiveOn`).
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## The normalized constant-vector factor -/

/-- `1 + u p^{−(σ + (s − ½))} + ū p^{−(σ − (s − ½))}`. -/
def jasConstFactor (σ : ℝ) (u : ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 + u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)) +
    conj u * cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ))

/-- The kernel `K_u(s) = ∏_{p ∈ P} (1 + u A_p(s) + ū B_p(s))`. -/
def jasConstKernel (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) : ℂ :=
  ∏ p ∈ P, jasConstFactor σ u p s

/-- The symmetrized term `(K_u(s) + K_ū(s))/(s(1 − s))`. -/
def jasConstPairTerm (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) : ℂ :=
  (jasConstKernel P σ u s + jasConstKernel P σ (conj u) s) / (s * (1 - s))

/-- The Bernoulli factor at `z` is `(1 + |z|²)` times the normalized factor at `u = z/(1 + |z|²)`. -/
theorem jasBernoulliFactor_eq_mul_jasConstFactor (σ : ℝ) (z : ℂ) (p : Nat.Primes) (s : ℂ) :
    jasBernoulliFactor (jasHoloA (s + (σ - 1 / 2 : ℝ)) p) (jasHoloB (s - (σ - 1 / 2 : ℝ)) p) z =
      ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * jasConstFactor σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) p s := by
  have hc : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne'
  have hzz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hA : jasHoloA (s + (σ - 1 / 2 : ℝ)) p =
      cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)) := by
    rw [jasHoloA]; congr 1; push_cast; ring
  have hB : jasHoloB (s - (σ - 1 / 2 : ℝ)) p =
      cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) := by
    rw [jasHoloB]; congr 1; push_cast; ring
  rw [jasBernoulliFactor, hA, hB, jasConstFactor, map_div₀, Complex.conj_ofReal, hzz]
  field_simp
  push_cast
  ring

theorem prod_jasBernoulliFactor_eq (P : Finset Nat.Primes) (σ : ℝ) (z s : ℂ) :
    ∏ p ∈ P, jasBernoulliFactor (jasHoloA (s + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB (s - (σ - 1 / 2 : ℝ)) p) z =
      ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ P.card * jasConstKernel P σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) s := by
  rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_eq_mul_jasConstFactor σ z p s,
    Finset.prod_mul_distrib, Finset.prod_const, jasConstKernel]

/-! ## Factor bounds -/

theorem jasConstFactor_sub_one (σ : ℝ) (u : ℂ) (p : Nat.Primes) (s : ℂ) :
    jasConstFactor σ u p s - 1 = u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)) +
      conj u * cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) := by
  rw [jasConstFactor]; ring

/-- `‖u A_p + ū B_p‖ ≤ 2 ‖u‖ p^{−(σ − |Re s − ½|)}`. -/
theorem norm_jasConstFactor_sub_one_le (σ : ℝ) (u : ℂ) (p : Nat.Primes) (s : ℂ) :
    ‖jasConstFactor σ u p s - 1‖ ≤ 2 * ‖u‖ * Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
  have hL := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < (p : ℕ))).le
  have h1 : ‖cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))‖ ≤
      Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
    rw [norm_cexp_neg_mul_log]
    refine Real.exp_le_exp.mpr ?_
    have : ((σ : ℂ) + (s - 1 / 2)).re = σ + (s.re - 1 / 2) := by simp
    rw [this]
    nlinarith [neg_abs_le (s.re - 1 / 2)]
  have h2 : ‖cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ))‖ ≤
      Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
    rw [norm_cexp_neg_mul_log]
    refine Real.exp_le_exp.mpr ?_
    have : ((σ : ℂ) - (s - 1 / 2)).re = σ - (s.re - 1 / 2) := by simp
    rw [this]
    nlinarith [le_abs_self (s.re - 1 / 2)]
  rw [jasConstFactor_sub_one]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h3 := mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg u)
  linarith

/-- `Σ_p (u A_p + ū B_p) = u W(σ + (s − ½)) + ū W(σ − (s − ½))`. -/
theorem sum_jasConstFactor_sub_one (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    ∑ p ∈ P, (jasConstFactor σ u p s - 1) =
      u * jasCpowSum P ((σ : ℂ) + (s - 1 / 2)) + conj u * jasCpowSum P ((σ : ℂ) - (s - 1 / 2)) := by
  simp_rw [jasConstFactor_sub_one]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, jasCpowSum, jasCpowSum]

theorem norm_jasConstKernel_le_exp (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    ‖jasConstKernel P σ u s‖ ≤ Real.exp (∑ p ∈ P, ‖jasConstFactor σ u p s - 1‖) := by
  rw [jasConstKernel, norm_prod, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  calc ‖jasConstFactor σ u p s‖ = ‖1 + (jasConstFactor σ u p s - 1)‖ := by ring_nf
    _ ≤ 1 + ‖jasConstFactor σ u p s - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_one]
    _ ≤ Real.exp ‖jasConstFactor σ u p s - 1‖ := by
        linarith [Real.add_one_le_exp ‖jasConstFactor σ u p s - 1‖]

/-- With every `‖u A_p + ū B_p‖ ≤ ½`, the kernel is `exp(Σ_p (u A_p + ū B_p) + R)` with
`‖R‖ ≤ Σ_p ‖u A_p + ū B_p‖²`. -/
theorem exists_jasConstKernel_eq_exp (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ)
    (h : ∀ p ∈ P, ‖jasConstFactor σ u p s - 1‖ ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ ∑ p ∈ P, ‖jasConstFactor σ u p s - 1‖ ^ 2 ∧
      jasConstKernel P σ u s = cexp (∑ p ∈ P, (jasConstFactor σ u p s - 1) + R) := by
  obtain ⟨R, hR, he⟩ := exists_prod_one_add_eq_exp P (fun p => jasConstFactor σ u p s - 1) h
  refine ⟨R, hR, ?_⟩
  rw [← he, jasConstKernel]
  exact Finset.prod_congr rfl fun p _ => by ring

/-! ## Symmetries -/

theorem jasConstFactor_one_sub (σ : ℝ) (u : ℂ) (p : Nat.Primes) (s : ℂ) :
    jasConstFactor σ u p (1 - s) = jasConstFactor σ (conj u) p s := by
  rw [jasConstFactor, jasConstFactor, Complex.conj_conj]
  have e1 : -((σ : ℂ) + (1 - s - 1 / 2)) = -((σ : ℂ) - (s - 1 / 2)) := by ring
  have e2 : -((σ : ℂ) - (1 - s - 1 / 2)) = -((σ : ℂ) + (s - 1 / 2)) := by ring
  rw [e1, e2]
  ring

theorem jasConstFactor_conj (σ : ℝ) (u : ℂ) (p : Nat.Primes) (s : ℂ) :
    jasConstFactor σ u p (conj s) = conj (jasConstFactor σ (conj u) p s) := by
  have e1 : conj (cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))) =
      cexp (-((σ : ℂ) + (conj s - 1 / 2)) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_conj]; congr 1
    simp only [map_neg, map_mul, map_add, map_sub, Complex.conj_ofReal, map_div₀, map_one,
      map_ofNat]
  have e2 : conj (cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ))) =
      cexp (-((σ : ℂ) - (conj s - 1 / 2)) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_conj]; congr 1
    simp only [map_neg, map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one,
      map_ofNat]
  rw [jasConstFactor, jasConstFactor, map_add, map_add, map_one, map_mul, map_mul,
    Complex.conj_conj, e1, e2]

theorem jasConstKernel_one_sub (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstKernel P σ u (1 - s) = jasConstKernel P σ (conj u) s := by
  rw [jasConstKernel, jasConstKernel]
  exact Finset.prod_congr rfl fun p _ => jasConstFactor_one_sub σ u p s

theorem jasConstKernel_conj (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstKernel P σ u (conj s) = conj (jasConstKernel P σ (conj u) s) := by
  rw [jasConstKernel, jasConstKernel, map_prod]
  exact Finset.prod_congr rfl fun p _ => jasConstFactor_conj σ u p s

theorem jasConstPairTerm_one_sub (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstPairTerm P σ u (1 - s) = jasConstPairTerm P σ u s := by
  rw [jasConstPairTerm, jasConstPairTerm, jasConstKernel_one_sub, jasConstKernel_one_sub,
    Complex.conj_conj]
  congr 1 <;> ring

theorem jasConstPairTerm_conj (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstPairTerm P σ u (conj s) = conj (jasConstPairTerm P σ u s) := by
  rw [jasConstPairTerm, jasConstPairTerm, jasConstKernel_conj, jasConstKernel_conj,
    Complex.conj_conj, map_div₀, map_add, map_mul, map_sub, map_one]
  congr 1
  ring

/-- The four zeros `½ ± z, ½ ± z̄` have symmetrized terms with equal real parts. -/
theorem re_jasConstPairTerm_eq_of_abs {P : Finset Nat.Primes} {σ : ℝ} {u s s₀ : ℂ}
    (hre : |s.re - 1 / 2| = |s₀.re - 1 / 2|) (him : |s.im| = |s₀.im|) :
    (jasConstPairTerm P σ u s).re = (jasConstPairTerm P σ u s₀).re := by
  have hcases : s = s₀ ∨ s = conj s₀ ∨ s = 1 - s₀ ∨ s = 1 - conj s₀ := by
    rcases abs_eq_abs.mp hre with h1 | h1 <;> rcases abs_eq_abs.mp him with h2 | h2
    · left; exact Complex.ext (by linarith) h2
    · right; left; exact Complex.ext (by simp; linarith) (by simp; linarith)
    · right; right; right; exact Complex.ext (by simp; linarith) (by simp; linarith)
    · right; right; left; exact Complex.ext (by simp; linarith) (by simp; linarith)
  rcases hcases with h | h | h | h <;> subst h
  · rfl
  · rw [jasConstPairTerm_conj, Complex.conj_re]
  · rw [jasConstPairTerm_one_sub]
  · rw [jasConstPairTerm_one_sub, jasConstPairTerm_conj, Complex.conj_re]

/-! ## The symmetrized test -/

/-- Every zero has `|Re ρ − ½| ≤ ½`, so `‖K_u(ρ)‖ ≤ exp(2‖u‖ Σ_p p^{−(σ−½)})`. -/
theorem norm_jasConstKernel_le_uniform (P : Finset Nat.Primes) (σ : ℝ) (u : ℂ) (q : XiZeroCopy) :
    ‖jasConstKernel P σ u (q.1 : ℂ)‖ ≤
      Real.exp (2 * ‖u‖ * ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p)) := by
  refine (norm_jasConstKernel_le_exp P σ u _).trans (Real.exp_le_exp.mpr ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => (norm_jasConstFactor_sub_one_le σ u p _).trans ?_
  have hd : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    rw [abs_le]; constructor <;> linarith
  exact mul_le_mul_of_nonneg_left
    (exp_neg_mul_log_prime_anti (show σ - 1 / 2 ≤ σ - |(q.1 : ℂ).re - 1 / 2| by linarith) p)
    (by positivity)

theorem summable_jasConstKernel_div (P : Finset Nat.Primes) (σ : ℝ) (u : ℂ) :
    Summable fun q : XiZeroCopy =>
      jasConstKernel P σ u (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left
    (Real.exp (2 * ‖u‖ * ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p)))) fun q => ?_
  rw [div_eq_mul_one_div, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_jasConstKernel_le_uniform P σ u q) (norm_nonneg _)

theorem jasConstPairTerm_eq_add (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    jasConstPairTerm P σ u s = jasConstKernel P σ u s / (s * (1 - s)) +
      jasConstKernel P σ (conj u) s / (s * (1 - s)) := by
  rw [jasConstPairTerm, add_div]

theorem summable_jasConstPairTerm (P : Finset Nat.Primes) (σ : ℝ) (u : ℂ) :
    Summable fun q : XiZeroCopy => jasConstPairTerm P σ u (q.1 : ℂ) := by
  refine ((summable_jasConstKernel_div P σ u).add
    (summable_jasConstKernel_div P σ (conj u))).congr fun q => ?_
  rw [jasConstPairTerm_eq_add]

/-- **Positivity at `z` and `z̄` makes the symmetrized aggregate at `u = z/(1 + |z|²)`
nonnegative.** -/
theorem re_tsum_jasConstPairTerm_nonneg {P : Finset Nat.Primes} {σ : ℝ}
    (h : JasConstProductPositiveOn P σ) (z : ℂ) :
    0 ≤ (∑' q : XiZeroCopy, jasConstPairTerm P σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re := by
  have key : ∀ y : ℂ, 0 ≤ (∑' q : XiZeroCopy,
      jasConstKernel P σ (y / ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
    intro y
    have h0 := h y
    have e : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor
        (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p) (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) y) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        (((1 + ‖y‖ ^ 2) ^ P.card : ℝ) : ℂ) *
          (jasConstKernel P σ (y / ((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ) /
            ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
      intro q
      rw [prod_jasBernoulliFactor_eq]
      push_cast
      ring
    simp only [e] at h0
    rw [tsum_mul_left, Complex.re_ofReal_mul] at h0
    exact nonneg_of_mul_nonneg_right h0 (by positivity)
  have hconj : conj (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) = conj z / ((1 + ‖conj z‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal, Complex.norm_conj]
  have h1 := key z
  have h2 := key (conj z)
  rw [← hconj] at h2
  have hs1 := summable_jasConstKernel_div P σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ))
  have hs2 := summable_jasConstKernel_div P σ (conj (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)))
  simp_rw [jasConstPairTerm_eq_add]
  rw [hs1.tsum_add hs2, Complex.add_re]
  linarith

/-! ## The dominant pair -/

/-- The radius of the second case of the anti-alignment lemma. -/
def pairRadius (c R₀ : ℝ) : ℝ := R₀ + 2 * (2 * Real.pi + 4) / (c / (8 * (R₀ + 4))) ^ 2

theorem le_pairRadius (c R₀ : ℝ) : R₀ ≤ pairRadius c R₀ := by
  rw [pairRadius]
  have : 0 ≤ 2 * (2 * Real.pi + 4) / (c / (8 * (R₀ + 4))) ^ 2 := by
    have := Real.pi_pos
    positivity
  linarith

/-- `Re(w e^x) ≥ Re w − 2‖w‖ ‖x‖` for `‖x‖ ≤ 1`. -/
theorem re_mul_cexp_ge {w x : ℂ} (hx : ‖x‖ ≤ 1) : w.re - 2 * ‖w‖ * ‖x‖ ≤ (w * cexp x).re := by
  have h1 := Complex.norm_exp_sub_one_le hx
  have e : (w * cexp x).re = w.re + (w * (cexp x - 1)).re := by
    rw [mul_sub, mul_one, Complex.sub_re]; ring
  have h2 : -(‖w‖ * (2 * ‖x‖)) ≤ (w * (cexp x - 1)).re := by
    have := Complex.abs_re_le_norm (w * (cexp x - 1))
    rw [norm_mul] at this
    have h3 : ‖w‖ * ‖cexp x - 1‖ ≤ ‖w‖ * (2 * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    linarith [neg_abs_le (w * (cexp x - 1)).re]
  linarith

/-- `Re ω = 1 − ‖ω − 1‖²/2` on the unit circle. -/
theorem re_eq_one_sub_norm_sub_one_sq {ω : ℂ} (hω : ‖ω‖ = 1) :
    ω.re = 1 - ‖ω - 1‖ ^ 2 / 2 := by
  have h1 : ‖ω‖ ^ 2 = ω.re * ω.re + ω.im * ω.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖ω - 1‖ ^ 2 = (ω.re - 1) * (ω.re - 1) + ω.im * ω.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp
  rw [hω] at h1
  rw [h2]
  nlinarith

/-- **Anti-alignment of a pair.**  Let `Re w > 0`, `‖ω‖ = 1` and `R₀ ≥ 0`, and put
`c = Re w/‖w‖`.  There are `R ∈ [R₀, pairRadius c R₀]` and `Y` with `‖Y‖ ≤ R + 2π` such that
`Re w (e^{Y+e₁} + e^{Ȳω+e₂}) ≤ −(Re w) e^R/4` whenever `‖e₁‖, ‖e₂‖ ≤ c/8`.  If `ω` is close to `1`
then `Y = R₀ + iπ`; otherwise `Y = R + i(π − arg w)` with `R = pairRadius c R₀`. -/
theorem exists_pair_antiAligned {w ω : ℂ} (hw : 0 < w.re) (hω : ‖ω‖ = 1) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    ∃ Y : ℂ, ∃ R : ℝ, R₀ ≤ R ∧ R ≤ pairRadius (w.re / ‖w‖) R₀ ∧ ‖Y‖ ≤ R + 2 * Real.pi ∧
      ∀ e₁ e₂ : ℂ, ‖e₁‖ ≤ w.re / ‖w‖ / 8 → ‖e₂‖ ≤ w.re / ‖w‖ / 8 →
        (w * (cexp (Y + e₁) + cexp (conj Y * ω + e₂))).re ≤ -(w.re * Real.exp R) / 4 := by
  have hwn : 0 < ‖w‖ := hw.trans_le (Complex.re_le_norm w)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = w.re / ‖w‖ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hwn]; exact Complex.re_le_norm w
  have hwc : w.re = c * ‖w‖ := by rw [hc]; field_simp
  rw [← hc]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c / (8 * (R₀ + 4)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  by_cases hB : ‖ω - 1‖ ≤ η
  · -- `ω` close to `1`: `Y = R₀ + iπ`
    refine ⟨(R₀ : ℂ) + (Real.pi : ℂ) * I, R₀, le_rfl, le_pairRadius _ _, ?_, ?_⟩
    · refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hR₀, Real.norm_of_nonneg hpi.le]
      linarith
    intro e₁ e₂ he₁ he₂
    have hY : cexp ((R₀ : ℂ) + (Real.pi : ℂ) * I + e₁) = -((Real.exp R₀ : ℝ) : ℂ) * cexp e₁ := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]; ring
    obtain ⟨x, hx⟩ : ∃ x : ℂ, x = ((R₀ : ℂ) - (Real.pi : ℂ) * I) * (ω - 1) + e₂ := ⟨_, rfl⟩
    have hconjY : conj ((R₀ : ℂ) + (Real.pi : ℂ) * I) = (R₀ : ℂ) - (Real.pi : ℂ) * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hZ : cexp (conj ((R₀ : ℂ) + (Real.pi : ℂ) * I) * ω + e₂) =
        -((Real.exp R₀ : ℝ) : ℂ) * cexp x := by
      rw [hconjY, show ((R₀ : ℂ) - (Real.pi : ℂ) * I) * ω + e₂ =
        ((R₀ : ℂ) - (Real.pi : ℂ) * I) + x by rw [hx]; ring, Complex.exp_add, Complex.exp_sub,
        Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
      field_simp
    have hRpi : ‖(R₀ : ℂ) - (Real.pi : ℂ) * I‖ ≤ R₀ + 4 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hR₀, Real.norm_of_nonneg hpi.le]
      linarith
    have hxn : ‖x‖ ≤ c / 4 := by
      rw [hx]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h1 : ‖(R₀ : ℂ) - (Real.pi : ℂ) * I‖ * ‖ω - 1‖ ≤ (R₀ + 4) * η :=
        mul_le_mul hRpi hB (norm_nonneg _) (by linarith)
      have h2 : (R₀ + 4) * η = c / 8 := by rw [hη]; field_simp
      linarith
    have hx1 : ‖x‖ ≤ 1 := by linarith
    have he1 : ‖e₁‖ ≤ 1 := by linarith
    have hr1 := re_mul_cexp_ge (w := w) he1
    have hr2 := re_mul_cexp_ge (w := w) hx1
    rw [hY, hZ]
    have e : w * (-((Real.exp R₀ : ℝ) : ℂ) * cexp e₁ + -((Real.exp R₀ : ℝ) : ℂ) * cexp x) =
        -((Real.exp R₀ : ℝ) : ℂ) * (w * cexp e₁ + w * cexp x) := by ring
    rw [e, neg_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.add_re]
    have hsum : w.re ≤ (w * cexp e₁).re + (w * cexp x).re := by
      have h3 : 2 * ‖w‖ * ‖e₁‖ ≤ 2 * ‖w‖ * (c / 8) :=
        mul_le_mul_of_nonneg_left he₁ (by positivity)
      have h4 : 2 * ‖w‖ * ‖x‖ ≤ 2 * ‖w‖ * (c / 4) :=
        mul_le_mul_of_nonneg_left hxn (by positivity)
      nlinarith
    have hE := Real.exp_pos R₀
    nlinarith [mul_le_mul_of_nonneg_left hsum hE.le]
  · -- `ω` away from `1`: `Y = R + i(π − arg w)`, `R = pairRadius c R₀`
    push Not at hB
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = pairRadius c R₀ := ⟨_, rfl⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi - w.arg := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Complex.arg_le_pi w]
    have hθ1 : θ ≤ 2 * Real.pi := by rw [hθ]; linarith [Complex.neg_pi_lt_arg w]
    have hRR₀ : R₀ ≤ R := hR ▸ le_pairRadius c R₀
    refine ⟨(R : ℂ) + (θ : ℂ) * I, R, hRR₀, hR.le, ?_, ?_⟩
    · refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (hR₀.trans hRR₀), Real.norm_of_nonneg hθ0]
      linarith
    intro e₁ e₂ he₁ he₂
    have he₁' : ‖e₁‖ ≤ 1 / 4 := by linarith
    have hmain := re_mul_cexp_antiAligned_le (w := w) R he₁'
    rw [← hθ] at hmain
    -- the second exponent has real part at most `R − 4 + 1/8`
    have hReω := re_eq_one_sub_norm_sub_one_sq hω
    have hgap : R * (η ^ 2 / 2) ≥ 2 * Real.pi + 4 := by
      have hRdef : R = R₀ + 2 * (2 * Real.pi + 4) / η ^ 2 := by rw [hR, pairRadius, ← hη]
      have hη2 : 0 < η ^ 2 := by positivity
      have : (2 * (2 * Real.pi + 4) / η ^ 2) * (η ^ 2 / 2) = 2 * Real.pi + 4 := by
        field_simp
      rw [hRdef]
      nlinarith [mul_nonneg hR₀ hη2.le]
    have hconjY : conj ((R : ℂ) + (θ : ℂ) * I) = (R : ℂ) - (θ : ℂ) * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hre2 : (conj ((R : ℂ) + (θ : ℂ) * I) * ω + e₂).re ≤ R - 3 := by
      rw [hconjY, Complex.add_re]
      have h1 : (((R : ℂ) - (θ : ℂ) * I) * ω).re = R * ω.re + θ * ω.im := by simp
      rw [h1]
      have him : θ * ω.im ≤ 2 * Real.pi := by
        have := Complex.abs_im_le_norm ω
        rw [hω] at this
        nlinarith [abs_le.mp this, le_abs_self ω.im]
      have hre : ω.re ≤ 1 - η ^ 2 / 2 := by
        rw [hReω]
        have : η ^ 2 ≤ ‖ω - 1‖ ^ 2 := by
          exact pow_le_pow_left₀ hη0.le hB.le 2
        linarith
      have he2r : e₂.re ≤ 1 / 8 := by
        have := Complex.re_le_norm e₂
        linarith
      have hRnn : 0 ≤ R := hR₀.trans hRR₀
      nlinarith [mul_le_mul_of_nonneg_left hre hRnn]
    have hsecond : ‖w * cexp (conj ((R : ℂ) + (θ : ℂ) * I) * ω + e₂)‖ ≤
        ‖w‖ * Real.exp R / 16 := by
      rw [norm_mul, Complex.norm_exp]
      have h3 : Real.exp ((conj ((R : ℂ) + (θ : ℂ) * I) * ω + e₂).re) ≤ Real.exp (R - 3) :=
        Real.exp_le_exp.mpr hre2
      have h4 : Real.exp (R - 3) ≤ Real.exp R / 16 := by
        rw [Real.exp_sub]
        have h16 : (16 : ℝ) ≤ Real.exp 3 := by
          have := Real.add_one_le_exp (3 : ℝ)
          have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          have h5 := Real.exp_one_gt_d9
          nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) h5.le 3]
        rw [div_le_div_iff₀ (Real.exp_pos 3) (by norm_num)]
        nlinarith [Real.exp_pos R]
      calc ‖w‖ * Real.exp _ ≤ ‖w‖ * Real.exp (R - 3) := mul_le_mul_of_nonneg_left h3 hwn.le
        _ ≤ ‖w‖ * (Real.exp R / 16) := mul_le_mul_of_nonneg_left h4 hwn.le
        _ = ‖w‖ * Real.exp R / 16 := by ring
    rw [mul_add, Complex.add_re]
    have h5 := Complex.re_le_norm (w * cexp (conj ((R : ℂ) + (θ : ℂ) * I) * ω + e₂))
    have h6 : w.re * Real.exp R ≤ ‖w‖ * Real.exp R :=
      mul_le_mul_of_nonneg_right (Complex.re_le_norm w) (Real.exp_pos R).le
    have hmain' : (w * cexp ((R : ℂ) + (θ : ℂ) * I + e₁)).re ≤ -(‖w‖ * Real.exp R) / 2 := hmain
    have hX : 0 ≤ ‖w‖ * Real.exp R := mul_nonneg hwn.le (Real.exp_pos R).le
    linarith

/-! ## Kernel bounds on a prime window -/

/-- `Σ_p ‖u A_p + ū B_p‖ ≤ 2‖u‖ S_β(N)` with `β = σ − |Re s − ½|`. -/
theorem sum_norm_jasConstFactor_sub_one_le (X N : ℕ) (σ : ℝ) (u s : ℂ) :
    ∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ u p s - 1‖ ≤
      2 * ‖u‖ * jasPrimeRpowSum (σ - |s.re - 1 / 2|) N := by
  calc ∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ u p s - 1‖
      ≤ ∑ p ∈ jasPrimeWindow X N,
          2 * ‖u‖ * Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) :=
        Finset.sum_le_sum fun p _ => norm_jasConstFactor_sub_one_le σ u p s
    _ = 2 * ‖u‖ * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ‖u‖ * jasPrimeRpowSum (σ - |s.re - 1 / 2|) N :=
        mul_le_mul_of_nonneg_left (sum_jasPrimeWindow_le_jasPrimeRpowSum X N _) (by positivity)

/-- At distance at most `δ` from the line, `Σ_p ‖u A_p + ū B_p‖ ≤ 2‖u‖ S_{σ−δ}(N)` and every
factor deviation is at most `2‖u‖`. -/
theorem jasConst_window_bounds {X N : ℕ} {σ δ α : ℝ} (hα : α = σ - δ) (hα0 : 0 < α) (u : ℂ)
    {s : ℂ} (hs : |s.re - 1 / 2| ≤ δ) :
    (∀ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ u p s - 1‖ ≤ 2 * ‖u‖) ∧
      ∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ u p s - 1‖ ≤ 2 * ‖u‖ * jasPrimeRpowSum α N := by
  have hβ : α ≤ σ - |s.re - 1 / 2| := by rw [hα]; linarith
  refine ⟨fun p _ => (norm_jasConstFactor_sub_one_le σ u p s).trans ?_, ?_⟩
  · have h1 := exp_neg_mul_log_prime_anti hβ p
    have h2 := exp_neg_mul_log_prime_le_one hα0.le p
    have h3 : Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) ≤ 1 := h1.trans h2
    nlinarith [norm_nonneg u]
  · refine (sum_norm_jasConstFactor_sub_one_le X N σ u s).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum fun p _ => ?_
    exact exp_neg_mul_log_prime_anti hβ (p : Nat.Primes)

/-- `Σ ‖x_p‖² ≤ (max ‖x_p‖) Σ ‖x_p‖`. -/
theorem sum_sq_le_of_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) {m : ℝ} (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hm : ∀ i ∈ s, x i ≤ m) : ∑ i ∈ s, x i ^ 2 ≤ m * ∑ i ∈ s, x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    rw [sq]; exact mul_le_mul_of_nonneg_right (hm i hi) (hx0 i hi)

theorem norm_jasConstPairTerm_le (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) {B : ℝ}
    (h1 : ‖jasConstKernel P σ u s‖ ≤ B) (h2 : ‖jasConstKernel P σ (conj u) s‖ ≤ B) :
    ‖jasConstPairTerm P σ u s‖ ≤ 2 * B * ‖1 / (s * (1 - s))‖ := by
  rw [jasConstPairTerm, div_eq_mul_one_div, norm_mul]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)

/-! ## The dominant zero -/

/-- **The dominant zero.**  Let `ρ* = ½ + δ + iγ`, `S = Σ_{p∈P} p^{−(α − iγ)}` with `α = σ − δ`,
`z₀ = conj(Y/S)` and `u₀ = z₀/(1 + ‖z₀‖²)`.  Then `K_{u₀}(ρ*) = e^{Y + e₁}` and
`K_{ū₀}(ρ*) = e^{Ȳ S/S̄ + e₂}` with `‖e_i‖ ≤ c/8`, so any bound for
`Re w (e^{Y+e₁} + e^{Ȳω+e₂})` bounds the symmetrized term at `ρ*`. -/
theorem re_jasConstPairTerm_dominant_le {P : Finset Nat.Primes} {σ δ α γ c a₀ B : ℝ}
    {q₁ Y S : ℂ} (hq₁ : q₁ = 1 / 2 + (δ : ℂ) + (γ : ℂ) * I) (hα : α = σ - δ) (hα0 : 0 < α)
    (hδ0 : 0 < δ) (hS : S = jasCpowSum P ((α : ℂ) - (γ : ℂ) * I)) (hS0 : S ≠ 0)
    (ha₀ : a₀ = ‖conj (Y / S)‖) (ha₀1 : 2 * a₀ ≤ 1 / 2)
    (hsq : 2 * a₀ * (2 * a₀ * ∑ p ∈ P, Real.exp (-α * Real.log p)) ≤ c / 24)
    (hsmall : a₀ * ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) ≤ c / 24)
    (hY : ‖Y‖ * a₀ ^ 2 ≤ c / 24)
    (hpair : ∀ e₁ e₂ : ℂ, ‖e₁‖ ≤ c / 8 → ‖e₂‖ ≤ c / 8 →
      (1 / (q₁ * (1 - q₁)) * (cexp (Y + e₁) + cexp (conj Y * (S / conj S) + e₂))).re ≤ B) :
    (jasConstPairTerm P σ (conj (Y / S) / ((1 + ‖conj (Y / S)‖ ^ 2 : ℝ) : ℂ)) q₁).re ≤ B := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = conj (Y / S) := ⟨_, rfl⟩
  rw [← hz₀] at ha₀ ⊢
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 + ‖z₀‖ ^ 2 := ⟨_, rfl⟩
  rw [← hc₀]
  have hc₀1 : 1 ≤ c₀ := by rw [hc₀]; nlinarith [norm_nonneg z₀]
  have hc₀0 : 0 < c₀ := by linarith
  have hc₀c : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀0.ne'
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℂ, u₀ = z₀ / (c₀ : ℂ) := ⟨_, rfl⟩
  rw [← hu₀]
  have ha₀0 : 0 ≤ a₀ := by rw [ha₀]; exact norm_nonneg _
  have hu₀n : ‖u₀‖ ≤ a₀ := by
    rw [hu₀, norm_div, Complex.norm_real, Real.norm_of_nonneg hc₀0.le, ← ha₀]
    exact div_le_self ha₀0 hc₀1
  have hcu₀n : ‖conj u₀‖ ≤ a₀ := by rw [Complex.norm_conj]; exact hu₀n
  have hconjS : conj S ≠ 0 := by rwa [map_ne_zero]
  -- the two prime sums of `ρ*`
  have hq₁re : |q₁.re - 1 / 2| = δ := by rw [hq₁]; simp [abs_of_pos hδ0]
  have hbig : (σ : ℂ) - (q₁ - 1 / 2) = (α : ℂ) - (γ : ℂ) * I := by
    rw [hq₁, hα]; push_cast; ring
  have hsmallre : ((σ : ℂ) + (q₁ - 1 / 2)).re = σ + δ := by rw [hq₁]; simp
  obtain ⟨S', hS'⟩ : ∃ S' : ℂ, S' = jasCpowSum P ((σ : ℂ) + (q₁ - 1 / 2)) := ⟨_, rfl⟩
  have hS'n : ‖S'‖ ≤ ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) := by
    rw [hS']; refine (norm_jasCpowSum_le P _).trans (le_of_eq ?_); rw [hsmallre]
  -- factor bounds for `u₀` and `ū₀`
  have hfac : ∀ v : ℂ, ‖v‖ ≤ a₀ →
      (∀ p ∈ P, ‖jasConstFactor σ v p q₁ - 1‖ ≤ 1 / 2) ∧
        ∑ p ∈ P, ‖jasConstFactor σ v p q₁ - 1‖ ^ 2 ≤ c / 24 := by
    intro v hv
    have hle : ∀ p ∈ P, ‖jasConstFactor σ v p q₁ - 1‖ ≤ 2 * a₀ := fun p _ => by
      refine (norm_jasConstFactor_sub_one_le σ v p q₁).trans ?_
      rw [hq₁re, ← hα]
      have := exp_neg_mul_log_prime_le_one hα0.le p
      nlinarith [norm_nonneg v, Real.exp_pos (-α * Real.log p)]
    have hsum : ∑ p ∈ P, ‖jasConstFactor σ v p q₁ - 1‖ ≤
        2 * a₀ * ∑ p ∈ P, Real.exp (-α * Real.log p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => (norm_jasConstFactor_sub_one_le σ v p q₁).trans ?_
      rw [hq₁re, ← hα]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    refine ⟨fun p hp => (hle p hp).trans ha₀1, ?_⟩
    refine (sum_sq_le_of_le P _ (fun p _ => norm_nonneg _) hle).trans ?_
    refine (mul_le_mul_of_nonneg_left hsum (by linarith)).trans hsq
  obtain ⟨hf1, hf2⟩ := hfac u₀ hu₀n
  obtain ⟨hg1, hg2⟩ := hfac (conj u₀) hcu₀n
  obtain ⟨R₁, hR₁, hK₁⟩ := exists_jasConstKernel_eq_exp P σ u₀ q₁ hf1
  obtain ⟨R₂, hR₂, hK₂⟩ := exists_jasConstKernel_eq_exp P σ (conj u₀) q₁ hg1
  rw [sum_jasConstFactor_sub_one, hbig, ← hS, ← hS'] at hK₁ hK₂
  rw [Complex.conj_conj] at hK₂
  -- the exponents
  have hcu₀S : conj u₀ * S = Y / (c₀ : ℂ) := by
    rw [hu₀, map_div₀, Complex.conj_ofReal, hz₀, Complex.conj_conj]
    field_simp
  have hu₀S : u₀ * S = conj Y * (S / conj S) / (c₀ : ℂ) := by
    rw [hu₀, hz₀, map_div₀]
    field_simp
  have hshrink : ∀ V : ℂ, ‖V / (c₀ : ℂ) - V‖ ≤ ‖V‖ * a₀ ^ 2 := by
    intro V
    have e : V / (c₀ : ℂ) - V = -(V * (((c₀ - 1) / c₀ : ℝ) : ℂ)) := by
      push_cast; field_simp; ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      have : 0 ≤ c₀ - 1 := by linarith
      positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : c₀ - 1 = a₀ ^ 2 := by rw [hc₀, ha₀]; ring
    rw [h1]
    exact div_le_self (by positivity) hc₀1
  have hnormω : ‖S / conj S‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hS0)]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℂ, e₁ = u₀ * S' + (Y / (c₀ : ℂ) - Y) + R₁ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ℂ,
      e₂ = conj u₀ * S' + (conj Y * (S / conj S) / (c₀ : ℂ) - conj Y * (S / conj S)) + R₂ :=
    ⟨_, rfl⟩
  have hK₁' : jasConstKernel P σ u₀ q₁ = cexp (Y + e₁) := by
    rw [hK₁, hcu₀S, he₁]; ring_nf
  have hK₂' : jasConstKernel P σ (conj u₀) q₁ = cexp (conj Y * (S / conj S) + e₂) := by
    rw [hK₂, hu₀S, he₂]; ring_nf
  have hsm1 : ‖u₀ * S'‖ ≤ c / 24 := by
    rw [norm_mul]
    exact (mul_le_mul hu₀n hS'n (norm_nonneg _) (by linarith [norm_nonneg u₀])).trans hsmall
  have hsm2 : ‖conj u₀ * S'‖ ≤ c / 24 := by
    rw [norm_mul]
    exact (mul_le_mul hcu₀n hS'n (norm_nonneg _) (by linarith [norm_nonneg u₀])).trans hsmall
  have he₁n : ‖e₁‖ ≤ c / 8 := by
    rw [he₁]
    have h1 := hshrink Y
    have h2 := hR₁.trans hf2
    calc ‖u₀ * S' + (Y / (c₀ : ℂ) - Y) + R₁‖
        ≤ ‖u₀ * S'‖ + ‖Y / (c₀ : ℂ) - Y‖ + ‖R₁‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ c / 8 := by linarith
  have he₂n : ‖e₂‖ ≤ c / 8 := by
    rw [he₂]
    have h1 := hshrink (conj Y * (S / conj S))
    rw [norm_mul, Complex.norm_conj, hnormω, mul_one] at h1
    have h2 := hR₂.trans hg2
    calc ‖conj u₀ * S' + (conj Y * (S / conj S) / (c₀ : ℂ) - conj Y * (S / conj S)) + R₂‖
        ≤ ‖conj u₀ * S'‖ + ‖conj Y * (S / conj S) / (c₀ : ℂ) - conj Y * (S / conj S)‖ + ‖R₂‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ c / 8 := by linarith
  have e : jasConstPairTerm P σ u₀ q₁ =
      1 / (q₁ * (1 - q₁)) * (cexp (Y + e₁) + cexp (conj Y * (S / conj S) + e₂)) := by
    rw [jasConstPairTerm, hK₁', hK₂']; ring
  rw [e]
  exact hpair e₁ e₂ he₁n he₂n

/-! ## Competitor bounds -/

/-- Uniform bounds at every zero for an amplitude `‖v‖ ≤ a₀`. -/
theorem jasConst_uniform_bounds {X N : ℕ} {σ δ α a₀ Λ₀ : ℝ} (hα : α = σ - δ) (hα0 : 0 < α)
    {v : ℂ} (hv : ‖v‖ ≤ a₀) (ha₀1 : 2 * a₀ ≤ 1 / 2) (hΛ : 2 * a₀ * jasPrimeRpowSum α N ≤ Λ₀)
    (hsq : 2 * a₀ * Λ₀ ≤ 1 / 12) {s : ℂ} (hs : |s.re - 1 / 2| ≤ δ) :
    (∀ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ v p s - 1‖ ≤ 1 / 2) ∧
      ∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ v p s - 1‖ ^ 2 ≤ 1 / 12 ∧
      ‖jasConstKernel (jasPrimeWindow X N) σ v s‖ ≤ Real.exp Λ₀ := by
  obtain ⟨hb1, hb2⟩ := jasConst_window_bounds (X := X) (N := N) hα hα0 v hs
  have hfac : ∀ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ v p s - 1‖ ≤ 2 * a₀ := fun p hp =>
    (hb1 p hp).trans (by linarith)
  have hS0 := jasPrimeRpowSum_nonneg α N
  have hsum : ∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ v p s - 1‖ ≤ Λ₀ := by
    have := mul_le_mul_of_nonneg_right hv hS0
    linarith
  refine ⟨fun p hp => (hfac p hp).trans ha₀1, ?_, ?_⟩
  · refine (sum_sq_le_of_le _ _ (fun p _ => norm_nonneg _) hfac).trans ?_
    have ha₀0 : 0 ≤ a₀ := (norm_nonneg v).trans hv
    have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * a₀ by linarith)
    linarith
  · exact (norm_jasConstKernel_le_exp _ σ v _).trans (Real.exp_le_exp.mpr hsum)

/-- A zero closer to the line has kernel at most `2`. -/
theorem norm_jasConstKernel_shallow_le {X N : ℕ} {σ : ℝ} {v s : ℂ}
    (h : 2 * ‖v‖ * jasPrimeRpowSum (σ - |s.re - 1 / 2|) N ≤ 1 / 48) :
    ‖jasConstKernel (jasPrimeWindow X N) σ v s‖ ≤ 2 := by
  refine (norm_jasConstKernel_le_exp _ σ v s).trans ?_
  have h2 : Real.exp (∑ p ∈ jasPrimeWindow X N, ‖jasConstFactor σ v p s - 1‖) ≤
      Real.exp (1 / 48) :=
    Real.exp_le_exp.mpr ((sum_norm_jasConstFactor_sub_one_le X N σ v s).trans h)
  have h3 : Real.exp (1 / 48 : ℝ) ≤ 2 := by
    calc Real.exp (1 / 48 : ℝ) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- A zero at the same distance has kernel at most `e^{B + 1}` when its large prime sum, times
`‖v‖`, is at most `B`. -/
theorem norm_jasConstKernel_sameDepth_le {P : Finset Nat.Primes} {σ δ α B : ℝ} {v s : ℂ}
    (hα : α = σ - δ) (hd : |s.re - 1 / 2| = δ)
    (hu : ∀ p ∈ P, ‖jasConstFactor σ v p s - 1‖ ≤ 1 / 2)
    (hR : ∑ p ∈ P, ‖jasConstFactor σ v p s - 1‖ ^ 2 ≤ 1 / 12)
    (hsmall : ‖v‖ * ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) ≤ 1 / 96)
    (hbig : ‖v‖ * ‖jasCpowSum P ((α : ℂ) - ((|s.im| : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖jasConstKernel P σ v s‖ ≤ Real.exp (B + 1) := by
  obtain ⟨Rq, hRq, hKq⟩ := exists_jasConstKernel_eq_exp P σ v s hu
  rw [sum_jasConstFactor_sub_one] at hKq
  rw [hKq, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_))
  have hpairq := norm_jasCpowSum_pair_le P (σ := σ) hd
  rw [← hα] at hpairq
  have h1 : ‖v * jasCpowSum P ((σ : ℂ) + (s - 1 / 2)) + conj v * jasCpowSum P ((σ : ℂ) - (s - 1 / 2))‖
      ≤ ‖v‖ * (‖jasCpowSum P ((α : ℂ) - ((|s.im| : ℝ) : ℂ) * I)‖ +
        ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    linarith
  rw [mul_add] at h1
  linarith [hRq.trans hR]

/-- **Competitors.**  A zero of `F` outside the dominant group has kernel at most
`2 + e^{(R + 2π)ρ₂ + 1}`, for `v ∈ {u₀, ū₀}`. -/
theorem norm_jasConstKernel_competitor_le {X N : ℕ} {σ δ α γ γ₁ ρ₂ R a₀ Λ₀ : ℝ} {v Y S : ℂ}
    {q : XiZeroCopy} (hα : α = σ - δ) (hα0 : 0 < α) (hv : ‖v‖ ≤ a₀) (ha₀S : a₀ * ‖S‖ = ‖Y‖)
    (hY : ‖Y‖ ≤ R + 2 * Real.pi) (hρ₂0 : 0 ≤ ρ₂) (ha₀1 : 2 * a₀ ≤ 1 / 2)
    (hΛ : 2 * a₀ * jasPrimeRpowSum α N ≤ Λ₀) (hsq : 2 * a₀ * Λ₀ ≤ 1 / 12)
    (hsmall : a₀ * jasPrimeRpowSum (σ + δ) N ≤ 1 / 96)
    (hmax : |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hgap : |(q.1 : ℂ).re - 1 / 2| = δ → |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|)
    (hnot : ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ))
    (hshallow : |(q.1 : ℂ).re - 1 / 2| < δ →
      2 * a₀ * jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ 1 / 48)
    (hdepth : |(q.1 : ℂ).re - 1 / 2| = δ → γ₁ ≤ |(q.1 : ℂ).im| →
      ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ ≤
        ρ₂ * ‖S‖) :
    ‖jasConstKernel (jasPrimeWindow X N) σ v (q.1 : ℂ)‖ ≤
      2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1) := by
  have ha₀0 : 0 ≤ a₀ := (norm_nonneg v).trans hv
  have hE := Real.exp_pos ((R + 2 * Real.pi) * ρ₂ + 1)
  rcases lt_or_eq_of_le hmax with hlt | hqd
  · have h1 : 2 * ‖v‖ * jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ 1 / 48 := by
      have := mul_le_mul_of_nonneg_right hv (jasPrimeRpowSum_nonneg (σ - |(q.1 : ℂ).re - 1 / 2|) N)
      linarith [hshallow hlt]
    have := norm_jasConstKernel_shallow_le (X := X) h1
    linarith
  · have hqi : γ₁ ≤ |(q.1 : ℂ).im| := by
      rcases hgap hqd with h | h
      · exact absurd ⟨hqd, h⟩ hnot
      · exact h
    obtain ⟨hu1, hu2, -⟩ := jasConst_uniform_bounds (X := X) (N := N) hα hα0 hv ha₀1 hΛ hsq hmax
    have hsm : ‖v‖ * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p) ≤ 1 / 96 := by
      have h1 := sum_jasPrimeWindow_le_jasPrimeRpowSum X N (σ + δ)
      have h2 := mul_le_mul hv h1 (Finset.sum_nonneg fun p (_ : p ∈ jasPrimeWindow X N) =>
        (Real.exp_pos (-(σ + δ) * Real.log p)).le) ha₀0
      linarith
    have hbig : ‖v‖ * ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ ≤
        (R + 2 * Real.pi) * ρ₂ := by
      calc ‖v‖ * ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖
          ≤ a₀ * (ρ₂ * ‖S‖) := mul_le_mul hv (hdepth hqd hqi) (norm_nonneg _) ha₀0
        _ = ρ₂ * ‖Y‖ := by rw [← ha₀S]; ring
        _ ≤ ρ₂ * (R + 2 * Real.pi) := mul_le_mul_of_nonneg_left hY hρ₂0
        _ = (R + 2 * Real.pi) * ρ₂ := mul_comm _ _
    have := norm_jasConstKernel_sameDepth_le hα hqd hu1 hu2 hsm hbig
    linarith

/-- **Assembly.**  A dominant group of equal real parts beats bounded competitors and a light
tail. -/
theorem jasConst_assemble {P : Finset Nat.Primes} {σ δ γ R R₀ W Bc Λ₀ ρ₂ : ℝ} {u₀ : ℂ}
    {q₁ : XiZeroCopy} {F : Finset XiZeroCopy} (hδ0 : 0 < δ) (hγ0 : 0 < γ)
    (hq₁ : (q₁.1 : ℂ) = 1 / 2 + (δ : ℂ) + (γ : ℂ) * I)
    (hw₁ : 0 < (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re)
    (hdom : (jasConstPairTerm P σ u₀ (q₁.1 : ℂ)).re ≤
      -((1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R) / 4)
    (hcomp : ∀ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ)),
      ‖jasConstPairTerm P σ u₀ (q.1 : ℂ)‖ ≤ 2 * Bc * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hall : ∀ q : XiZeroCopy, ‖jasConstPairTerm P σ u₀ (q.1 : ℂ)‖ ≤
      2 * Real.exp Λ₀ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hW : W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hRbig : 32 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1)) ≤
      (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R)
    (hBc : Bc = 2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1)) (hR₀R : R₀ ≤ R)
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
      (2 * Real.exp Λ₀) ≤ (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R₀ / 16)
    (hq₁F : q₁ ∈ F) :
    (∑' q : XiZeroCopy, jasConstPairTerm P σ u₀ (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R / 4 :=
    ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; positivity
  have hwsum : Summable fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    summable_inv_mul_one_sub.norm
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hq₁re : (q₁.1 : ℂ).re - 1 / 2 = δ := by rw [hq₁]; simp
  have hq₁im : (q₁.1 : ℂ).im = γ := by rw [hq₁]; simp
  have hq₁D : q₁ ∈ F.filter (fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ) :=
    Finset.mem_filter.mpr ⟨hq₁F, by rw [hq₁re, abs_of_pos hδ0], by rw [hq₁im, abs_of_pos hγ0]⟩
  refine re_tsum_neg_of_dominant (summable_jasConstPairTerm P σ u₀) F
    (fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ) hA ?_ ?_ ?_
  · rw [Complex.re_sum]
    have hDeq : ∀ q ∈ F.filter (fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ),
        (jasConstPairTerm P σ u₀ (q.1 : ℂ)).re = (jasConstPairTerm P σ u₀ (q₁.1 : ℂ)).re := by
      intro q hq
      obtain ⟨hqd, hqi⟩ := (Finset.mem_filter.mp hq).2
      exact re_jasConstPairTerm_eq_of_abs (by rw [hqd, hq₁re, abs_of_pos hδ0])
        (by rw [hqi, hq₁im, abs_of_pos hγ0])
    rw [Finset.sum_congr rfl hDeq, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = ((F.filter (fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧
        |(q.1 : ℂ).im| = γ)).card : ℝ) := ⟨_, rfl⟩
    rw [← hk]
    have hcard : (1 : ℝ) ≤ k := by rw [hk]; exact_mod_cast Finset.card_pos.mpr ⟨q₁, hq₁D⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (jasConstPairTerm P σ u₀ (q₁.1 : ℂ)).re := ⟨_, rfl⟩
    rw [← ht]
    have htA : t ≤ -A := by rw [ht, hAdef]; linarith only [hdom]
    have h1 : k * t ≤ k * (-A) := mul_le_mul_of_nonneg_left htA (by linarith only [hcard])
    have h2 : 0 ≤ (k - 1) * A := mul_nonneg (by linarith only [hcard]) hA.le
    have h3 : k * (-A) = -A - (k - 1) * A := by ring
    linarith only [h1, h2, h3]
  · refine (norm_sum_le _ _).trans ?_
    have hsum : ∑ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ)),
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W := by
      rw [hW]; exact hwsum.sum_le_tsum _ fun q _ => norm_nonneg _
    calc ∑ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ)),
          ‖jasConstPairTerm P σ u₀ (q.1 : ℂ)‖
        ≤ ∑ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ)),
          2 * Bc * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := Finset.sum_le_sum hcomp
      _ = 2 * Bc * ∑ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧
          |(q.1 : ℂ).im| = γ)), ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by rw [Finset.mul_sum]
      _ ≤ 2 * Bc * W := mul_le_mul_of_nonneg_left hsum (by linarith only [hBc0])
      _ ≤ A / 4 := by
          rw [hAdef]; rw [← hBc] at hRbig; linarith only [hRbig]
  · have hs1 : Summable (fun q : {x // x ∉ F} => ‖jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖) :=
      (summable_jasConstPairTerm P σ u₀).norm.subtype _
    have hs2 : Summable (fun q : {x // x ∉ F} =>
        2 * Real.exp Λ₀ * ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) :=
      (hwsum.mul_left _).subtype _
    have hER : Real.exp R₀ ≤ Real.exp R := Real.exp_le_exp.mpr hR₀R
    have hER' := mul_le_mul_of_nonneg_left hER hw₁.le
    calc ‖∑' q : {x // x ∉ F}, jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖
        ≤ ∑' q : {x // x ∉ F}, ‖jasConstPairTerm P σ u₀ (q.1.1 : ℂ)‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : {x // x ∉ F}, 2 * Real.exp Λ₀ * ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖ :=
          Summable.tsum_le_tsum (fun q => hall q.1) hs1 hs2
      _ = (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
          (2 * Real.exp Λ₀) := by rw [tsum_mul_left, mul_comm]
      _ ≤ A / 4 := by rw [hAdef]; linarith only [hFtail, hER']

/-! ## Assembly at one scale -/

/-- **The test at one scale.**  With all quantitative choices made, the symmetrized aggregate at
`u₀ = z₀/(1 + ‖z₀‖²)`, `z₀ = conj(Y/S)`, on the primes in `(X, N]` is negative. -/
theorem jasConst_tsum_neg_core {X N : ℕ} {σ δ α γ γ₁ ρ₂ Λ₀ W c R R₀ a₀ : ℝ}
    {Y S : ℂ} {q₁ : XiZeroCopy} {F : Finset XiZeroCopy}
    (hδ0 : 0 < δ) (hα : α = σ - δ) (hα0 : 0 < α) (hγ0 : 0 < γ)
    (hq₁ : (q₁.1 : ℂ) = 1 / 2 + (δ : ℂ) + (γ : ℂ) * I)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hgap : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|)
    (hS : S = jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - (γ : ℂ) * I)) (hS0 : S ≠ 0)
    (ha₀ : a₀ = ‖conj (Y / S)‖) (hY : ‖Y‖ ≤ R + 2 * Real.pi) (hρ₂0 : 0 ≤ ρ₂)
    (hc1 : c ≤ 1) (hw₁ : 0 < (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re)
    (hpair : ∀ e₁ e₂ : ℂ, ‖e₁‖ ≤ c / 8 → ‖e₂‖ ≤ c / 8 →
      (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ))) *
        (cexp (Y + e₁) + cexp (conj Y * (S / conj S) + e₂))).re ≤
        -((1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R) / 4)
    (hW : W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hRbig : 32 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1)) ≤
      (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R)
    (hR₀R : R₀ ≤ R)
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
      (2 * Real.exp Λ₀) ≤ (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R₀ / 16)
    (hq₁F : q₁ ∈ F) (ha₀1 : 2 * a₀ ≤ 1 / 2) (hsq : 2 * a₀ * Λ₀ ≤ c / 24)
    (hΛ : 2 * a₀ * jasPrimeRpowSum α N ≤ Λ₀)
    (hsmall : a₀ * jasPrimeRpowSum (σ + δ) N ≤ c / 96) (hYa : ‖Y‖ * a₀ ^ 2 ≤ c / 24)
    (hshallow : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      2 * a₀ * jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ 1 / 48)
    (hdepth : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ → γ₁ ≤ |(q.1 : ℂ).im| →
      ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ ≤
        ρ₂ * ‖S‖) :
    (∑' q : XiZeroCopy, jasConstPairTerm (jasPrimeWindow X N) σ
      (conj (Y / S) / ((1 + ‖conj (Y / S)‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℂ, u₀ = conj (Y / S) / ((1 + ‖conj (Y / S)‖ ^ 2 : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  rw [← hu₀]
  have ha₀0 : 0 ≤ a₀ := by rw [ha₀]; exact norm_nonneg _
  have hu₀n : ‖u₀‖ ≤ a₀ := by
    rw [hu₀, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← ha₀]
    exact div_le_self ha₀0 (by nlinarith [norm_nonneg (conj (Y / S))])
  have hcu₀n : ‖conj u₀‖ ≤ a₀ := by rw [Complex.norm_conj]; exact hu₀n
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hS0
  have ha₀S : a₀ * ‖S‖ = ‖Y‖ := by
    rw [ha₀, Complex.norm_conj, norm_div, div_mul_cancel₀ _ hSn.ne']
  have hc0 : 0 ≤ c := by
    have := mul_nonneg ha₀0 (jasPrimeRpowSum_nonneg (σ + δ) N)
    linarith
  have hsq12 : 2 * a₀ * Λ₀ ≤ 1 / 12 := by linarith
  have hsmall96 : a₀ * jasPrimeRpowSum (σ + δ) N ≤ 1 / 96 := by linarith
  -- the dominant zero
  have hsq' : 2 * a₀ * (2 * a₀ * ∑ p ∈ jasPrimeWindow X N, Real.exp (-α * Real.log p)) ≤
      c / 24 := by
    have h1 := sum_jasPrimeWindow_le_jasPrimeRpowSum X N α
    have h2 : 2 * a₀ * ∑ p ∈ jasPrimeWindow X N, Real.exp (-α * Real.log p) ≤ Λ₀ :=
      (mul_le_mul_of_nonneg_left h1 (by linarith)).trans hΛ
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * a₀ by linarith)
    linarith
  have hsmallP : a₀ * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p) ≤ c / 24 := by
    have h1 := sum_jasPrimeWindow_le_jasPrimeRpowSum X N (σ + δ)
    have := mul_le_mul_of_nonneg_left h1 ha₀0
    linarith
  have hdom : (jasConstPairTerm (jasPrimeWindow X N) σ u₀ (q₁.1 : ℂ)).re ≤
      -((1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).re * Real.exp R) / 4 := by
    rw [hu₀]
    exact re_jasConstPairTerm_dominant_le hq₁ hα hα0 hδ0 hS hS0 ha₀ ha₀1 hsq' hsmallP hYa hpair
  -- term bounds
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1) := ⟨_, rfl⟩
  have hcomp : ∀ q ∈ F.filter (fun q => ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ)),
      ‖jasConstPairTerm (jasPrimeWindow X N) σ u₀ (q.1 : ℂ)‖ ≤
        2 * Bc * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro q hq
    obtain ⟨hqF, hnot⟩ := Finset.mem_filter.mp hq
    rw [hBc]
    exact norm_jasConstPairTerm_le _ σ u₀ _
      (norm_jasConstKernel_competitor_le hα hα0 hu₀n ha₀S hY hρ₂0 ha₀1 hΛ hsq12 hsmall96
        (hmax q) (hgap q) hnot (hshallow q hqF) (hdepth q hqF))
      (norm_jasConstKernel_competitor_le hα hα0 hcu₀n ha₀S hY hρ₂0 ha₀1 hΛ hsq12 hsmall96
        (hmax q) (hgap q) hnot (hshallow q hqF) (hdepth q hqF))
  have hall : ∀ q : XiZeroCopy, ‖jasConstPairTerm (jasPrimeWindow X N) σ u₀ (q.1 : ℂ)‖ ≤
      2 * Real.exp Λ₀ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q =>
    norm_jasConstPairTerm_le _ σ u₀ _
      (jasConst_uniform_bounds hα hα0 hu₀n ha₀1 hΛ hsq12 (hmax q)).2.2
      (jasConst_uniform_bounds hα hα0 hcu₀n ha₀1 hΛ hsq12 (hmax q)).2.2
  exact jasConst_assemble hδ0 hγ0 hq₁ hw₁ hdom hcomp hall hW hRbig hBc hR₀R hFtail hq₁F

/-! ## Every large window -/

/-- A large exponent beats a fixed budget from `R₀` on:
`32 W (2 + e^{(R + 2π)ρ + 1}) ≤ c e^R` for every `R ≥ R₀`, when `c > 0`, `ρ < 1`. -/
theorem exists_large_exponent_forall {W c ρ : ℝ} (hc : 0 < c) (hρ : ρ < 1) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      32 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ + 1)) ≤ c * Real.exp R := by
  have hc' : 0 < 1 - ρ := by linarith
  have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (64 * W)
  have h2 := ((Real.tendsto_exp_neg_atTop_nhds_zero).comp
    (tendsto_id.const_mul_atTop hc')).const_mul (32 * W * Real.exp (2 * Real.pi * ρ + 1))
  have ht := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at ht
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (ht.eventually (ge_mem_nhds hc))
  refine ⟨max R₀ 0, le_max_right _ _, fun R hR => ?_⟩
  have hR' := hR₀ R ((le_max_left _ _).trans hR)
  simp only [Function.comp, id] at hR'
  have e1 : Real.exp ((R + 2 * Real.pi) * ρ + 1) =
      Real.exp R * (Real.exp (2 * Real.pi * ρ + 1) * Real.exp (-((1 - ρ) * R))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp R * Real.exp (-R) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc 32 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ + 1))
      = Real.exp R * (64 * W * Real.exp (-R) + 32 * W * Real.exp (2 * Real.pi * ρ + 1) *
          Real.exp (-((1 - ρ) * R))) := by rw [e1]; linear_combination (-64 * W) * e2
    _ ≤ Real.exp R * c := by gcongr
    _ = c * Real.exp R := mul_comm _ _

/-- `Re(1/(ρ(1−ρ))) > 0` for `ρ = ½ + δ + iγ` with `|δ| < ½`. -/
theorem re_one_div_mul_one_sub_pos {δ γ : ℝ} (hδ : |δ| < 1 / 2) :
    0 < (1 / ((1 / 2 + (δ : ℂ) + (γ : ℂ) * I) * (1 - (1 / 2 + (δ : ℂ) + (γ : ℂ) * I)))).re := by
  have hz : ((1 / 2 + (δ : ℂ) + (γ : ℂ) * I) * (1 - (1 / 2 + (δ : ℂ) + (γ : ℂ) * I))).re =
      1 / 4 - δ ^ 2 + γ ^ 2 := by simp; ring
  have hpos : 0 < 1 / 4 - δ ^ 2 + γ ^ 2 := by
    have := abs_lt.mp hδ
    nlinarith
  rw [one_div, Complex.inv_re]
  refine div_pos (by rw [hz]; exact hpos) (Complex.normSq_pos.mpr fun h => ?_)
  have := congrArg Complex.re h
  rw [hz, Complex.zero_re] at this
  linarith

/-! ### Numerical steps -/

theorem jasConst_amp_le {y s B E m : ℝ} (hy : 0 ≤ y) (hyB : y ≤ B)
    (hs : 3 / 4 * (E / m) ≤ s) (hE : 0 < E) (hm : 0 < m) : y / s ≤ 4 / 3 * B * m / E := by
  have hEm : 0 < 3 / 4 * (E / m) := by positivity
  have hs0 : 0 < s := hEm.trans_le hs
  have hB : 0 ≤ B := hy.trans hyB
  calc y / s ≤ B / s := div_le_div_of_nonneg_right hyB hs0.le
    _ ≤ B / (3 / 4 * (E / m)) := div_le_div_of_nonneg_left hB hEm hs
    _ = 4 / 3 * B * m / E := by field_simp

theorem jasConst_budget_le {a S E k B m : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 4 / 3 * B * m / E)
    (hS : S ≤ k * E) (hS0 : 0 ≤ S) (hE : 0 < E) (hB : 0 ≤ B * m * k) :
    2 * a * S ≤ 4 * B * m * k := by
  have h1 : a * S ≤ 4 / 3 * B * m / E * (k * E) := mul_le_mul ha hS hS0 (ha0.trans ha)
  have h2 : 4 / 3 * B * m / E * (k * E) = 4 / 3 * (B * m * k) := by field_simp
  nlinarith

theorem jasConst_kappa_bounds {κ c L B : ℝ} (hκ : κ = min (1 / 4) (c / (48 * (L + 1) * (B + 1))))
    (hc : 0 < c) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    κ ≤ 1 / 4 ∧ 2 * κ * L ≤ c / 24 ∧ B * κ ≤ c / 48 := by
  have h48 : 0 < 48 * (L + 1) * (B + 1) := by positivity
  have hκ2 : κ ≤ c / (48 * (L + 1) * (B + 1)) := by rw [hκ]; exact min_le_right _ _
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact le_min (by norm_num) (by positivity)
  have hk : κ * (48 * (L + 1) * (B + 1)) ≤ c := by
    have := mul_le_mul_of_nonneg_right hκ2 h48.le
    rwa [div_mul_cancel₀ _ h48.ne'] at this
  refine ⟨by rw [hκ]; exact min_le_left _ _, ?_, ?_⟩
  · nlinarith [mul_nonneg hκ0 hL, mul_nonneg (mul_nonneg hκ0 hL) hB, mul_nonneg hκ0 hB]
  · nlinarith [mul_nonneg hκ0 hL, mul_nonneg (mul_nonneg hκ0 hL) hB, mul_nonneg hκ0 hB]

theorem jasConst_eps2_le {a S' Sα ε₂ L c : ℝ} (ha : 0 ≤ a) (h3 : S' ≤ ε₂ * Sα)
    (hΛ : 2 * a * Sα ≤ L) (hε₂0 : 0 ≤ ε₂) (hε₂L : ε₂ * L ≤ c / 48) : 2 * a * S' ≤ c / 48 := by
  have h1 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * a by linarith)
  have h2 := mul_le_mul_of_nonneg_left hΛ hε₂0
  nlinarith

theorem jasConst_lower_le {s M d E m ε : ℝ} (hM : M = E / m) (htri : M - d ≤ s)
    (hd : d ≤ ε * E) (hm : 0 < m) : E / m * (1 - m * ε) ≤ s := by
  have e : E / m * (1 - m * ε) = E / m - ε * E := by field_simp
  rw [e]; rw [hM] at htri; linarith

theorem jasConst_depth_le {E m μ ρ₁ ρ₂ ε W' s : ℝ} (hE : 0 < E) (hm : 0 < m) (hμ : 0 < μ)
    (hρ₁ : ρ₁ = m / μ) (hρ₂ : ρ₂ = (1 + ρ₁) / 2) (hmε : m * ε = (1 - ρ₁) / 4)
    (hW' : W' ≤ E / μ + ε * E) (hs : E / m * (1 - m * ε) ≤ s) : W' ≤ ρ₂ * s := by
  have hEμ : E / μ = E / m * ρ₁ := by rw [hρ₁]; field_simp
  have hεE : ε * E = E / m * (m * ε) := by field_simp
  have hEm : 0 < E / m := by positivity
  have hscalar : ρ₁ + m * ε ≤ ρ₂ * (1 - m * ε) := by
    rw [hρ₂, hmε]; nlinarith [sq_nonneg (1 - ρ₁)]
  have hρ₂0 : 0 ≤ ρ₂ := by
    have : 0 < ρ₁ := by rw [hρ₁]; positivity
    rw [hρ₂]; linarith
  have h1 := mul_le_mul_of_nonneg_left hscalar hEm.le
  have h2 := mul_le_mul_of_nonneg_left hs hρ₂0
  rw [hEμ, hεE] at hW'
  nlinarith

/-- The same-depth competitors of `F` have large prime sums at most `ρ₂ ‖S‖`. -/
theorem jasConst_depth_all {X N : ℕ} {δ α γ₁ m₀ μ₁ ρ₁ ρ₂ ε E s : ℝ} {F : Finset XiZeroCopy}
    (hN2 : 2 ≤ N) (hE : E = jasMainScale α N) (hγ₁0 : 0 ≤ γ₁)
    (hm₀0 : 0 < m₀) (hμ₁ : μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2)) (hμ₁0 : 0 < μ₁)
    (hρ₁ : ρ₁ = m₀ / μ₁) (hρ₂ : ρ₂ = (1 + ρ₁) / 2) (hmε : m₀ * ε = (1 - ρ₁) / 4)
    (hs : E / m₀ * (1 - m₀ * ε) ≤ s)
    (h5 : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ →
      ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
        jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * E) :
    ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ → γ₁ ≤ |(q.1 : ℂ).im| →
      ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ ≤ ρ₂ * s := by
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  intro q hq hqd hqi
  have he := h5 q hq hqd
  rw [jasWindowSum_eq_jasCpowSum] at he
  have hMq : ‖jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ E / μ₁ := by
    rw [norm_jasMainTerm_eq α _ hN2, ← hE]
    refine div_le_div_of_nonneg_left hE0.le hμ₁0 ?_
    rw [hμ₁]
    exact Real.sqrt_le_sqrt (add_le_add le_rfl (pow_le_pow_left₀ hγ₁0 hqi 2))
  have hWq : ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ ≤
      E / μ₁ + ε * E := by
    have := norm_le_insert' (jasCpowSum (jasPrimeWindow X N)
      ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I))
      (jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N)
    linarith only [this, he, hMq]
  exact jasConst_depth_le hE0 hm₀0 hμ₁0 hρ₁ hρ₂ hmε hWq hs

/-- The numerical conditions of the core at amplitude `a₀ ≤ min(¼, c/(48(Λ₀+1)(BY+1)))`. -/
theorem jasConst_numeric {N : ℕ} {σ δ α c BY Λ₀ ε₂ κ a₀ E m₀ y : ℝ} {F : Finset XiZeroCopy}
    (hα1 : α < 1) (hE0 : 0 < E) (hm₀0 : 0 < m₀) (hc0 : 0 < c) (hc1 : c ≤ 1) (hBY0 : 0 ≤ BY)
    (hΛ₀ : Λ₀ = 4 * BY * m₀ * (1 / (1 - α) + 1)) (hε₂ : ε₂ = c / (48 * (Λ₀ + 1)))
    (hε₂Λ : ε₂ * Λ₀ ≤ c / 48) (hκ : κ = min (1 / 4) (c / (48 * (Λ₀ + 1) * (BY + 1))))
    (ha₀0 : 0 ≤ a₀) (ha₀le : a₀ ≤ 4 / 3 * BY * m₀ / E) (h4 : 4 / 3 * BY * m₀ / E ≤ κ)
    (hyBY : y ≤ BY)
    (h2 : jasPrimeRpowSum α N ≤ (1 / (1 - α) + 1) * E)
    (h3 : jasPrimeRpowSum (σ + δ) N ≤ ε₂ * jasPrimeRpowSum α N)
    (h5 : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) :
    2 * a₀ ≤ 1 / 2 ∧ 2 * a₀ * Λ₀ ≤ c / 24 ∧ 2 * a₀ * jasPrimeRpowSum α N ≤ Λ₀ ∧
      a₀ * jasPrimeRpowSum (σ + δ) N ≤ c / 96 ∧ y * a₀ ^ 2 ≤ c / 24 ∧
      ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
        2 * a₀ * jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ 1 / 48 := by
  have h1α : 0 < 1 - α := by linarith only [hα1]
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀]; positivity
  obtain ⟨hκ1, hκL, hκB⟩ := jasConst_kappa_bounds hκ hc0 hΛ₀0 hBY0
  have ha₀κ : a₀ ≤ κ := ha₀le.trans h4
  have hε₂0 : 0 ≤ ε₂ := by rw [hε₂]; positivity
  have hΛ : 2 * a₀ * jasPrimeRpowSum α N ≤ Λ₀ := by
    rw [hΛ₀]
    exact jasConst_budget_le ha₀0 ha₀le h2 (jasPrimeRpowSum_nonneg α N) hE0 (by positivity)
  refine ⟨by linarith only [ha₀κ, hκ1], ?_, hΛ, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right ha₀κ hΛ₀0
    linarith only [this, hκL]
  · have := jasConst_eps2_le ha₀0 h3 hΛ hε₂0 hε₂Λ
    linarith only [this]
  · have ha₀1' : a₀ ≤ 1 := by linarith only [ha₀κ, hκ1]
    have hY1 : y * a₀ ≤ BY := by
      have := mul_le_mul hyBY ha₀1' ha₀0 hBY0
      linarith only [this]
    have hY2 : y * a₀ ^ 2 ≤ BY * a₀ := by
      have := mul_le_mul_of_nonneg_right hY1 ha₀0
      have e : y * a₀ ^ 2 = y * a₀ * a₀ := by ring
      linarith only [this, e]
    have hY3 : BY * a₀ ≤ BY * κ := mul_le_mul_of_nonneg_left ha₀κ hBY0
    linarith only [hY2, hY3, hκB, hc0]
  · intro q hq hlt
    have := jasConst_eps2_le ha₀0 (h5 q hq hlt) hΛ hε₂0 hε₂Λ
    linarith only [this, hc1]

/-- **One window.**  All constants fixed and all asymptotic conditions met at `N`, positivity of
the constant-vector tests on `(X, N]` is contradictory. -/
theorem jasConst_not_pos_at {X N : ℕ} {σ δ α γ γ₁ c W m₀ μ₁ ρ₁ ρ₂ R₀ BY Λ₀ ε ε₂ κ : ℝ}
    {w₁ s₀ : ℂ} {q₁ : XiZeroCopy} {F : Finset XiZeroCopy}
    (hδ0 : 0 < δ) (hα : α = σ - δ) (hα0 : 0 < α) (hα1 : α < 1) (hγ0 : 0 < γ)
    (hq₁ : (q₁.1 : ℂ) = 1 / 2 + (δ : ℂ) + (γ : ℂ) * I)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hgap : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|)
    (hγγ₁ : γ < γ₁) (hw₁ : w₁ = 1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))) (hw₁re : 0 < w₁.re)
    (hc : c = w₁.re / ‖w₁‖) (hc1 : c ≤ 1)
    (hW : W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hm₀ : m₀ = Real.sqrt ((1 - α) ^ 2 + γ ^ 2)) (hm₀0 : 0 < m₀)
    (hμ₁ : μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2)) (hμ₁0 : 0 < μ₁)
    (hρ₁ : ρ₁ = m₀ / μ₁) (hρ₂ : ρ₂ = (1 + ρ₁) / 2) (hρ₂0 : 0 ≤ ρ₂)
    (hR₀0 : 0 ≤ R₀) (hR₀ : ∀ R : ℝ, R₀ ≤ R →
      32 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1)) ≤ w₁.re * Real.exp R)
    (hBY : BY = pairRadius c R₀ + 2 * Real.pi) (hBY0 : 0 ≤ BY)
    (hΛ₀ : Λ₀ = 4 * BY * m₀ * (1 / (1 - α) + 1))
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
      (2 * Real.exp Λ₀) ≤ w₁.re * Real.exp R₀ / 16)
    (hq₁F : q₁ ∈ F) (hmε : m₀ * ε = (1 - ρ₁) / 4)
    (hε₂ : ε₂ = c / (48 * (Λ₀ + 1))) (hε₂Λ : ε₂ * Λ₀ ≤ c / 48)
    (hκ : κ = min (1 / 4) (c / (48 * (Λ₀ + 1) * (BY + 1))))
    (hs₀ : s₀ = (α : ℂ) - (γ : ℂ) * I) (hN2 : 2 ≤ N)
    (h1 : ‖jasWindowSum X N s₀ - jasMainTerm s₀ N‖ ≤ ε * jasMainScale α N)
    (h2 : jasPrimeRpowSum α N ≤ (1 / (1 - α) + 1) * jasMainScale α N)
    (h3 : jasPrimeRpowSum (σ + δ) N ≤ ε₂ * jasPrimeRpowSum α N)
    (h4 : 4 / 3 * BY * m₀ / jasMainScale α N ≤ κ)
    (h5 : ∀ q ∈ F, (|(q.1 : ℂ).re - 1 / 2| < δ →
        jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) ∧
      (|(q.1 : ℂ).re - 1 / 2| = δ →
        ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
          jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * jasMainScale α N))
    (hpos : JasConstProductPositiveOn (jasPrimeWindow X N) σ) : False := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = jasMainScale α N := ⟨_, rfl⟩
  rw [← hE] at h1 h2 h4 h5
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - (γ : ℂ) * I) :=
    ⟨_, rfl⟩
  have hSW : jasWindowSum X N s₀ = S := by rw [hS, hs₀, jasWindowSum_eq_jasCpowSum]
  have hMn : ‖jasMainTerm s₀ N‖ = E / m₀ := by
    rw [hs₀, norm_jasMainTerm_eq α γ hN2, ← hE, ← hm₀]
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; positivity
  have ht4 : m₀ * ε ≤ 1 / 4 := by rw [hmε]; linarith only [hρ₁0]
  have hSlow : E / m₀ * (1 - m₀ * ε) ≤ ‖S‖ := by
    have htri := norm_sub_norm_le (jasMainTerm s₀ N) (jasWindowSum X N s₀)
    rw [norm_sub_rev, hSW] at htri
    rw [hSW] at h1
    exact jasConst_lower_le hMn (by linarith only [htri]) h1 hm₀0
  have hEm : 0 < E / m₀ := by positivity
  have hS34 : 3 / 4 * (E / m₀) ≤ ‖S‖ := by
    have := mul_le_mul_of_nonneg_left (show 3 / 4 ≤ 1 - m₀ * ε by linarith only [ht4]) hEm.le
    linarith only [this, hSlow]
  have hSn : 0 < ‖S‖ := lt_of_lt_of_le (by positivity) hS34
  have hS0 : S ≠ 0 := norm_pos_iff.mp hSn
  have hω : ‖S / conj S‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self hSn.ne']
  obtain ⟨Y, R, hR₀R, hRR₁, hY, hpair⟩ := exists_pair_antiAligned hw₁re hω hR₀0
  rw [← hc] at hRR₁ hpair
  have hYBY : ‖Y‖ ≤ BY := by rw [hBY]; linarith only [hRR₁, hY]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = ‖conj (Y / S)‖ := ⟨_, rfl⟩
  have ha₀eq : a₀ = ‖Y‖ / ‖S‖ := by rw [ha₀, Complex.norm_conj, norm_div]
  have ha₀0 : 0 ≤ a₀ := by rw [ha₀]; exact norm_nonneg _
  have ha₀le : a₀ ≤ 4 / 3 * BY * m₀ / E := by
    rw [ha₀eq]; exact jasConst_amp_le (norm_nonneg _) hYBY hS34 hE0 hm₀0
  have hc0 : 0 < c := by
    rw [hc]; exact div_pos hw₁re (hw₁re.trans_le (Complex.re_le_norm _))
  obtain ⟨ha₀1, hsq, hΛ, hsmall, hYa, hshallow⟩ := jasConst_numeric (F := F) hα1 hE0 hm₀0 hc0
    hc1 hBY0 hΛ₀ hε₂ hε₂Λ hκ ha₀0 ha₀le h4 hYBY h2 h3 fun q hq => (h5 q hq).1
  have hdepth := jasConst_depth_all (F := F) (δ := δ) hN2 hE (hγ0.le.trans hγγ₁.le) hm₀0 hμ₁
    hμ₁0 hρ₁ hρ₂ hmε hSlow fun q hq => (h5 q hq).2
  have hneg := jasConst_tsum_neg_core (X := X) (N := N) (R₀ := R₀) (F := F) hδ0 hα hα0 hγ0 hq₁
    hmax hgap hS hS0 ha₀ hY hρ₂0 hc1 (by rw [← hw₁]; exact hw₁re) (by rw [← hw₁]; exact hpair) hW
    (by rw [← hw₁]; exact hR₀ R hR₀R) hR₀R (by rw [← hw₁]; exact hFtail) hq₁F ha₀1 hsq hΛ hsmall
    hYa hshallow hdepth
  have hnn := re_tsum_jasConstPairTerm_nonneg hpos (conj (Y / S))
  linarith only [hneg, hnn]

/-- **A complex constant vector detects a maximal off-line zero at every scale.**  If a zero
`ρ₀` off the critical line has the largest distance `δ = |Re ρ₀ − ½|` from it among all zeros, and
`δ < σ < 1 + δ`, then for every `X` and every sufficiently large `N` the constant-vector JAS test on
the primes in `(X, N]` is negative for some `z ∈ ℂ`. -/
theorem eventually_not_jasConstProductPositiveOn_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) (X : ℕ) :
    ∀ᶠ N : ℕ in atTop, ¬ JasConstProductPositiveOn (jasPrimeWindow X N) σ := by
  classical
  obtain ⟨q₁, γ, γ₁, hγ0, hγγ₁, hq₁, hgap⟩ := exists_normalized_maximal_zero q₀ hoff
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax hσ0 hσ1 hq₁ hgap
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : δ < 1 / 2 := by
    have h1 := xiZeroCopy_re_lt_one q₁
    have h2 : (q₁.1 : ℂ).re = 1 / 2 + δ := by rw [hq₁]; simp
    linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = σ - δ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  -- the weight of the dominant zero
  obtain ⟨w₁, hw₁⟩ : ∃ w : ℂ, w = 1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ))) := ⟨_, rfl⟩
  have hw₁re : 0 < w₁.re := by
    rw [hw₁, hq₁]; exact re_one_div_mul_one_sub_pos (by rw [abs_of_pos hδ0]; exact hδ1)
  have hw₁n : 0 < ‖w₁‖ := hw₁re.trans_le (Complex.re_le_norm _)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = w₁.re / ‖w₁‖ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hw₁n]; exact Complex.re_le_norm _
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  -- main-term constants
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = Real.sqrt ((1 - α) ^ 2 + γ ^ 2) := ⟨_, rfl⟩
  have hm₀0 : 0 < m₀ := by rw [hm₀]; exact Real.sqrt_pos.mpr (by positivity)
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : ℝ, μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2) := ⟨_, rfl⟩
  have hm₀μ₁ : m₀ < μ₁ := by
    rw [hm₀, hμ₁]; exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  have hμ₁0 : 0 < μ₁ := hm₀0.trans hm₀μ₁
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = m₀ / μ₁ := ⟨_, rfl⟩
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁, div_lt_one hμ₁0]; exact hm₀μ₁
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; positivity
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (1 + ρ₁) / 2 := ⟨_, rfl⟩
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂]; linarith
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; linarith
  -- exponents and budgets
  obtain ⟨R₀, hR₀0, hR₀⟩ := exists_large_exponent_forall (W := W) hw₁re hρ₂1
  obtain ⟨BY, hBY⟩ : ∃ BY : ℝ, BY = pairRadius c R₀ + 2 * Real.pi := ⟨_, rfl⟩
  have hBY0 : 0 ≤ BY := by
    rw [hBY]; have := le_pairRadius c R₀; have := Real.pi_pos; linarith
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = 4 * BY * m₀ * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀]; positivity
  obtain ⟨F, hFtail, hq₁F⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) * (2 * Real.exp Λ₀) ≤
        w₁.re * Real.exp R₀ / 16 ∧ q₁ ∈ F := by
    have hpos : 0 < w₁.re * Real.exp R₀ / 16 / (2 * Real.exp Λ₀) := by positivity
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (gt_mem_nhds hpos)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, {q₁} ⊆ F := eventually_ge_atTop {q₁}
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    refine ⟨F, ?_, hF2 (Finset.mem_singleton_self q₁)⟩
    rw [lt_div_iff₀ (by positivity)] at hF1
    exact hF1.le
  -- tolerances
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 - ρ₁) / (4 * m₀) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by positivity)
  have hmε : m₀ * ε = (1 - ρ₁) / 4 := by rw [hε]; field_simp
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = c / (48 * (Λ₀ + 1)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂Λ : ε₂ * Λ₀ ≤ c / 48 := by
    rw [hε₂, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = min (1 / 4) (c / (48 * (Λ₀ + 1) * (BY + 1))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; exact lt_min (by norm_num) (by positivity)
  -- eventual conditions
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = (α : ℂ) - (γ : ℂ) * I := ⟨_, rfl⟩
  have hs₀re : s₀.re = α := by rw [hs₀]; simp
  have ev1 := eventually_norm_jasWindowSum_sub_main_le X (s := s₀) (by rw [hs₀re]; exact hα0)
    (by rw [hs₀re]; exact hα1) hε0
  have ev2 := eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos
  have ev3 := eventually_jasPrimeRpowSum_le hα1.le (show α < σ + δ by rw [hα]; linarith) hε₂0
  have hamp0 : Tendsto (fun N : ℕ => 4 / 3 * BY * m₀ / jasMainScale α N) atTop (𝓝 0) := by
    have := (tendsto_natLog_div_rpow_atTop h1α).const_mul (4 / 3 * BY * m₀)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    simp only [jasMainScale]
    rw [div_div_eq_mul_div, mul_div_assoc]
  have ev4 := hamp0.eventually (ge_mem_nhds hκ0)
  have ev5 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F,
      (|(q.1 : ℂ).re - 1 / 2| < δ →
        jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) ∧
      (|(q.1 : ℂ).re - 1 / 2| = δ →
        ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
          jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * jasMainScale α N) := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    refine Eventually.and ?_ ?_
    · by_cases hq : |(q.1 : ℂ).re - 1 / 2| < δ
      · filter_upwards [eventually_jasPrimeRpowSum_le hα1.le
          (show α < σ - |(q.1 : ℂ).re - 1 / 2| by rw [hα]; linarith) hε₂0] with N hN _ using hN
      · exact Eventually.of_forall fun N h => absurd h hq
    · have hre : ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I).re = α := by simp
      have h := eventually_norm_jasWindowSum_sub_main_le X
        (s := (α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) (by rw [hre]; exact hα0)
        (by rw [hre]; exact hα1) hε0
      filter_upwards [h] with N hN _
      rwa [hre] at hN
  filter_upwards [ev1, ev2, ev3, ev4, ev5, eventually_ge_atTop 2] with N h1 h2 h3 h4 h5 hN2
  intro hpos
  rw [hs₀re] at h1
  exact jasConst_not_pos_at hδ0 hα hα0 hα1 hγ0 hq₁ hmax hgap hγγ₁ hw₁ hw₁re hc hc1 hW hm₀ hm₀0
    hμ₁ hμ₁0 hρ₁ hρ₂ hρ₂0 hR₀0 hR₀ hBY hBY0 hΛ₀ hFtail hq₁F hmε hε₂ hε₂Λ hκ hs₀ hN2
    h1 h2 h3 h4 h5 hpos

/-! ## Capstones -/

/-- Under RH the constant-vector tests are positive on every initial window above some `X`. -/
theorem frequently_jasConstProductPositiveOn_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ X : ℕ, ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow X N) 1 := by
  obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one.mp hRH
  exact ⟨X, Frequently.of_forall fun N => hX.constOn fun p hp => (mem_jasPrimeWindow.mp hp).1⟩

/-- A maximal off-line zero excludes level-one constant-vector positivity on infinitely many
initial prime windows `(X, N]`. -/
theorem not_frequently_jasConstProductPositiveOn_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) (X : ℕ) :
    ¬ ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow X N) 1 := by
  intro hfr
  have hδ0 : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : |(q₀.1 : ℂ).re - 1 / 2| < 1 := by
    have h0 := xiZeroCopy_re_pos q₀
    have h1 := xiZeroCopy_re_lt_one q₀
    rw [abs_lt]; constructor <;> linarith
  have hev := eventually_not_jasConstProductPositiveOn_of_maximal_offLine q₀ hoff hmax (σ := 1)
    hδ1 (by linarith) X
  obtain ⟨N, hN, hN'⟩ := (hfr.and_eventually hev).exists
  exact hN' hN

/-- **RH ⟺ the zeros approach the line ∧ level-one constant-vector positivity on infinitely many
initial prime windows.**  The large-height condition supplies an attained largest distance from
the line whenever RH fails, and a complex constant vector then gives a negative test on every
sufficiently long window. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_frequently_jasConstProductPositiveOn :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧
      ∃ X : ℕ, ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow X N) 1 := by
  constructor
  · intro hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      frequently_jasConstProductPositiveOn_of_riemannHypothesis hRH⟩
  · rintro ⟨hZ, X, hfr⟩
    by_contra hRH
    obtain ⟨Θ, hΘ, q₀, hq₀, hmaxq⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have habs : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := fun q => by
      rw [LindelofSparse.spectral_im_eq, abs_sub_comm]
    have hq₀' : |(q₀.1 : ℂ).re - 1 / 2| = Θ := by rw [← habs]; exact hq₀
    have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₀'; linarith
    have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := fun q => by
      rw [hq₀', ← habs]; exact hmaxq q
    exact not_frequently_jasConstProductPositiveOn_of_maximal_offLine q₀ hoff hmax X hfr

/-- **RH ⟺ no off-line chain ∧ level-one constant-vector positivity on infinitely many initial
prime windows.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_frequently_jasConstProductPositiveOn :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧
      ∃ X : ℕ, ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow X N) 1 := by
  constructor
  · intro hRH
    refine ⟨fun ⟨⟨q, hq⟩, _⟩ => hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q),
      frequently_jasConstProductPositiveOn_of_riemannHypothesis hRH⟩
  · rintro ⟨hno, X, hfr⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    have hnot : ¬ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
        ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| :=
      fun h => hno ⟨⟨q₁, ne_of_gt hq₁⟩, h⟩
    push Not at hnot
    obtain ⟨q₀, hoff, hmax⟩ := hnot
    exact not_frequently_jasConstProductPositiveOn_of_maximal_offLine q₀ hoff hmax X hfr

end

end RHTower
