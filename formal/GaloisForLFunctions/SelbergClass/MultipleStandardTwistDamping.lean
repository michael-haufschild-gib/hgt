import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Damped multiple standard twists

This module formalizes the first analytic step in Kaczorowski--Perelli,
*Multiple standard twists of L-functions* (2026), equation (3.1). For an
arbitrary positive number of factors, positive exponents, and polynomially
bounded Dirichlet coefficients, the exponentially damped multiple twist is
absolutely summable at every point of `ℂ^N`.

No continuation provider is assumed. The proof uses the exact multiplicative
damping from the paper and proves its domination by a product of one-variable
super-polynomial majorants.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- A finite product of nonnegative summable families is summable on the full
finite Cartesian power. -/
theorem summable_pi_prod_nonneg :
    ∀ (N : ℕ) (ι : Type), ∀ f : Fin N → ι → ℝ,
      (∀ i n, 0 ≤ f i n) →
      (∀ i, Summable (f i)) →
      Summable (fun x : Fin N → ι => ∏ i, f i (x i)) := by
  intro N ι
  induction N with
  | zero =>
      intro f hf hsum
      exact Summable.of_finite
  | succ N ih =>
      intro f hf hsum
      let tail : Fin N → ι → ℝ := fun i => f i.succ
      have htail_nonneg : ∀ i n, 0 ≤ tail i n := fun i n => hf i.succ n
      have htail_sum : ∀ i, Summable (tail i) := fun i => hsum i.succ
      have htail : Summable (fun x : Fin N → ι => ∏ i, tail i (x i)) :=
        ih tail htail_nonneg htail_sum
      let g : ι × (Fin N → ι) → ℝ := fun p =>
        f 0 p.1 * ∏ i, tail i (p.2 i)
      have hg_nonneg : ∀ p, 0 ≤ g p := by
        intro p
        exact mul_nonneg (hf 0 p.1)
          (Finset.prod_nonneg fun i _ => htail_nonneg i (p.2 i))
      have hg : Summable g := by
        rw [summable_prod_of_nonneg hg_nonneg]
        constructor
        · intro n
          exact htail.mul_left (f 0 n)
        · simpa only [g, tsum_mul_left] using
            (hsum 0).mul_right (∑' x : Fin N → ι, ∏ i, tail i (x i))
      let e := Fin.consEquiv (fun _ : Fin (N + 1) => ι)
      have heq :
          (fun x : Fin (N + 1) → ι => ∏ i, f i (x i)) ∘ e = g := by
        funext p
        simp only [Function.comp_apply, e, Fin.consEquiv_apply, g, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ, tail]
      rw [← e.summable_iff, heq]
      exact hg

/-- Multiplicative damping dominates a product of coordinatewise dampings.
This is the exact estimate that converts the multiple series into a product of
one-variable summable majorants. -/
theorem exp_neg_prod_le_prod_exp_neg_div {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : ∀ i, 1 ≤ x i) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-c * ∏ i, x i) ≤ ∏ i, Real.exp (-(c / N) * x i) := by
  let P : ℝ := ∏ i, x i
  have hcoord : ∀ i, x i ≤ P := by
    intro i
    calc
      x i = ∏ j ∈ {i}, x j := by simp
      _ ≤ ∏ j ∈ Finset.univ, x j :=
        Finset.prod_le_prod_of_subset_of_one_le
          (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
          (fun j _ => zero_le_one.trans (hx j))
          (fun j _ _ => hx j)
      _ = P := rfl
  have hsum : (∑ i, x i) ≤ (N : ℝ) * P := by
    calc
      (∑ i, x i) ≤ ∑ _i : Fin N, P := Finset.sum_le_sum fun i _ => hcoord i
      _ = (N : ℝ) * P := by simp [mul_comm]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have havg : (∑ i, x i) / (N : ℝ) ≤ P := by
    rw [div_le_iff₀ hNR]
    simpa [mul_comm] using hsum
  have hscaled : (c / (N : ℝ)) * (∑ i, x i) ≤ c * P := by
    calc
      (c / (N : ℝ)) * (∑ i, x i) = c * ((∑ i, x i) / (N : ℝ)) := by ring
      _ ≤ c * P := mul_le_mul_of_nonneg_left havg hc
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  rw [← Finset.mul_sum]
  dsimp [P] at hscaled ⊢
  linarith

/-- Product `∏ n_ν ^ κ_ν` in the multiple standard-twist phase. -/
noncomputable def multipleIndexPower {N : ℕ} (κ : Fin N → ℝ)
    (n : Fin N → ℕ+) : ℝ :=
  ∏ i, ((n i : ℕ) : ℝ) ^ κ i

/-- Kaczorowski--Perelli damping parameter
`z_X(α) = 2πα(1/X + i)`. -/
noncomputable def multipleTwistDampingParameter (α X : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * (α : ℂ) * (((1 / X : ℝ) : ℂ) + I)

/-- One term of the damped multiple standard twist. -/
noncomputable def dampedMultipleStandardTwistTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : ℂ :=
  (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
    Complex.exp
      (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ))

/-- The damped multiple standard twist, defined by its full Cartesian sum. -/
noncomputable def dampedMultipleStandardTwist {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) : ℂ :=
  ∑' n : Fin N → ℕ+, dampedMultipleStandardTwistTerm a κ α X s n

/-- Exact norm of the exponential damping factor. -/
theorem norm_exp_multipleTwistDamping {N : ℕ} (κ : Fin N → ℝ) (α X : ℝ)
    (n : Fin N → ℕ+) :
    ‖Complex.exp
        (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ))‖ =
      Real.exp (-(2 * Real.pi * α / X) * multipleIndexPower κ n) := by
  rw [Complex.norm_exp]
  congr 1
  simp [multipleTwistDampingParameter]
  ring_nf
  simp

/-- **Global absolute convergence of the damped multiple standard twist.**
For every `s : ℂ^N`, positive damping parameters, positive twist exponents,
and polynomially bounded coefficients, the exact series from equation (3.1)
of Kaczorowski--Perelli is absolutely summable. -/
theorem summable_norm_dampedMultipleStandardTwistTerm {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℕ → ℂ) (C B κ : Fin N → ℝ)
    (ha : ∀ (i : Fin N) (n : ℕ+),
      ‖a i (n : ℕ)‖ ≤ C i * ((n : ℕ) : ℝ) ^ B i)
    (hκ : ∀ i, 0 < κ i) {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) :
    Summable fun n : Fin N → ℕ+ =>
      ‖dampedMultipleStandardTwistTerm a κ α X s n‖ := by
  let rate : ℝ := 2 * Real.pi * α / X
  have hrate : 0 < rate := by
    dsimp [rate]
    positivity
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    have h := ha i ⟨1, by omega⟩
    simpa using (le_trans (norm_nonneg (a i 1)) h)
  let major : Fin N → ℕ+ → ℝ := fun i n =>
    C i * ((n : ℕ) : ℝ) ^ (B i - (s i).re) *
      Real.exp (-(rate / N) * ((n : ℕ) : ℝ) ^ κ i)
  have hmajor_nonneg : ∀ i n, 0 ≤ major i n := by
    intro i n
    exact mul_nonneg (mul_nonneg (hC i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.exp_pos _).le
  have hmajor_sum : ∀ i, Summable (major i) := by
    intro i
    have hc : 0 < rate / (N : ℝ) := by positivity
    have hbase := HTGeometry.summable_rpow_mul_exp_neg_rpow
      (A := B i - (s i).re) hc (hκ i)
    have hscaled := hbase.mul_left (C i)
    rw [show major i = (fun n : ℕ+ =>
        C i * (((n : ℕ) : ℝ) ^ (B i - (s i).re) *
          Real.exp (-((rate / N) * ((n : ℕ) : ℝ) ^ κ i)))) by
      funext n
      dsimp [major]
      ring]
    change Summable ((fun n : ℕ =>
      C i * ((n : ℝ) ^ (B i - (s i).re) *
        Real.exp (-((rate / N) * (n : ℝ) ^ κ i)))) ∘ PNat.val)
    exact hscaled.comp_injective (i := PNat.val) (fun _ _ h => PNat.eq h)
  have hmajor : Summable fun n : Fin N → ℕ+ => ∏ i, major i (n i) :=
    summable_pi_prod_nonneg N ℕ+ major hmajor_nonneg hmajor_sum
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hnpos : ∀ i, (0 : ℝ) < ((n i : ℕ) : ℝ) := by
    intro i
    exact_mod_cast (n i).property
  have hcoeff : ∀ i,
      ‖a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ ≤
        C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re) := by
    intro i
    rw [norm_mul,
      Complex.norm_natCast_cpow_of_pos (n := (n i : ℕ)) (n i).property (-s i)]
    have hpow : (0 : ℝ) < ((n i : ℕ) : ℝ) ^ (-(s i).re) :=
      Real.rpow_pos_of_pos (hnpos i) _
    calc
      ‖a i (n i : ℕ)‖ * ((n i : ℕ) : ℝ) ^ (-s i).re
          = ‖a i (n i : ℕ)‖ * ((n i : ℕ) : ℝ) ^ (-(s i).re) := by
              rw [Complex.neg_re]
      _ ≤ (C i * ((n i : ℕ) : ℝ) ^ B i) *
          ((n i : ℕ) : ℝ) ^ (-(s i).re) :=
            mul_le_mul_of_nonneg_right (ha i (n i)) hpow.le
      _ = C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re) := by
            calc
              (C i * ((n i : ℕ) : ℝ) ^ B i) *
                    ((n i : ℕ) : ℝ) ^ (-(s i).re)
                  = C i * (((n i : ℕ) : ℝ) ^ B i *
                    ((n i : ℕ) : ℝ) ^ (-(s i).re)) := by ring
              _ = C i * ((n i : ℕ) : ℝ) ^ (B i + (-(s i).re)) := by
                    rw [Real.rpow_add (hnpos i)]
              _ = C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re) := by ring_nf
  have hdir :
      ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ ≤
        ∏ i, C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re) := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hcoeff i)
  have hexp := exp_neg_prod_le_prod_exp_neg_div hN
    (fun i => ((n i : ℕ) : ℝ) ^ κ i)
    (fun i => Real.one_le_rpow (by exact_mod_cast (n i).property) (hκ i).le) hrate.le
  rw [dampedMultipleStandardTwistTerm, norm_mul, norm_exp_multipleTwistDamping]
  calc
    ‖∏ i, a i (n i : ℕ) * ((n i : ℂ) ^ (-s i))‖ *
          Real.exp (-rate * multipleIndexPower κ n)
      ≤ (∏ i, C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re)) *
          Real.exp (-rate * multipleIndexPower κ n) :=
        mul_le_mul_of_nonneg_right hdir (Real.exp_pos _).le
    _ ≤ (∏ i, C i * ((n i : ℕ) : ℝ) ^ (B i - (s i).re)) *
          (∏ i, Real.exp (-(rate / N) * ((n i : ℕ) : ℝ) ^ κ i)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [multipleIndexPower] using hexp
        · exact Finset.prod_nonneg fun i _ =>
            mul_nonneg (hC i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ∏ i, major i (n i) := by
      rw [← Finset.prod_mul_distrib]

/-- Absolute convergence implies convergence of the complex-valued damped
multiple standard twist itself. -/
theorem summable_dampedMultipleStandardTwistTerm {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℕ → ℂ) (C B κ : Fin N → ℝ)
    (ha : ∀ (i : Fin N) (n : ℕ+),
      ‖a i (n : ℕ)‖ ≤ C i * ((n : ℕ) : ℝ) ^ B i)
    (hκ : ∀ i, 0 < κ i) {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (s : Fin N → ℂ) :
    Summable fun n : Fin N → ℕ+ =>
      dampedMultipleStandardTwistTerm a κ α X s n :=
  (summable_norm_dampedMultipleStandardTwistTerm hN a C B κ ha hκ hα hX s).of_norm

end GaloisForLFunctions.SelbergClass
