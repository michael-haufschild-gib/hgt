import GaloisForLFunctions.HTGeometry.AlgebraicRootGrowth

/-!
# Grouping a multivariate relation by the last variable

An algebraic relation among several quantities, written as a finite sum of monomials with
coefficients, becomes a polynomial relation in the last quantity once the monomials are grouped by
its exponent.  The grouped coefficients are the partial sums over each fibre, and they involve only
the other quantities.

This is the algebraic step of the Clunie induction: at a first algebraic dependence one regards the
relation as a polynomial in the dependent state, with coefficients built from the previous states,
and then applies the pointwise root estimate.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- The coefficient of `x_last ^ j` after grouping a monomial family by the last exponent. -/
noncomputable def groupedCoeff (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → ℂ)
    (x : Fin (k + 1) → ℂ) (j : ℕ) : ℂ :=
  ∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
    A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)

/-- **Grouping by the last exponent.**  A finite monomial sum equals the polynomial in the last
variable whose coefficients are the fibre sums. -/
theorem sum_eq_sum_groupedCoeff (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → ℂ)
    (x : Fin (k + 1) → ℂ) (N : ℕ) (hN : ∀ e ∈ S, e (Fin.last k) ≤ N) :
    ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i)
      = ∑ j ∈ Finset.range (N + 1), groupedCoeff S A x j * (x (Fin.last k)) ^ j := by
  classical
  have hmaps : ∀ e ∈ S, e (Fin.last k) ∈ Finset.range (N + 1) := by
    intro e he
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hN e he))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun e => A e * ∏ i, (x i) ^ (e i))]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [groupedCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro e he
  have hj : e (Fin.last k) = j := (Finset.mem_filter.mp he).2
  have hprod : ∏ i, (x i) ^ (e i)
      = (x (Fin.last k)) ^ (e (Fin.last k))
        * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i) :=
    (Finset.mul_prod_erase Finset.univ (fun i => (x i) ^ (e i)) (Finset.mem_univ _)).symm
  rw [hprod, hj]
  ring

/-- **The root estimate for a grouped multivariate relation.**  If a monomial relation vanishes and
the top grouped coefficient is nonzero, the last quantity is bounded by the normalised lower
coefficients. -/
theorem posLog_norm_last_le_of_relation {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (hrel : ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) = 0)
    (htop : groupedCoeff S A x N ≠ 0) :
    Real.posLog ‖x (Fin.last k)‖
      ≤ Real.posLog (∑ j ∈ Finset.range N, ‖groupedCoeff S A x j / groupedCoeff S A x N‖) := by
  classical
  have hgroup := sum_eq_sum_groupedCoeff S A x N hN
  rw [hgroup] at hrel
  exact posLog_norm_le_of_root hN1 htop hrel

/-- The same bound split across the lower coefficients. -/
theorem posLog_norm_last_le_sum {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (hrel : ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) = 0)
    (htop : groupedCoeff S A x N ≠ 0) :
    Real.posLog ‖x (Fin.last k)‖
      ≤ (∑ j ∈ Finset.range N,
          Real.posLog ‖groupedCoeff S A x j / groupedCoeff S A x N‖) + (N : ℝ) * Real.log 2 := by
  classical
  have hbase := posLog_norm_last_le_of_relation hN1 hN hrel htop
  have hsplit := posLog_sum_le (Finset.range N)
    (fun j => ‖groupedCoeff S A x j / groupedCoeff S A x N‖)
    (fun j _ => norm_nonneg _)
  rw [Finset.card_range] at hsplit
  linarith

/-! ## The weight of a grouped coefficient -/

/-- The positive logarithm of a finite product is at most the sum of the positive logarithms. -/
theorem posLog_prod_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    Real.posLog (∏ i ∈ s, y i) ≤ ∑ i ∈ s, Real.posLog (y i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.posLog]
  | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact le_trans Real.posLog_mul (by linarith [ih])

/-- The positive logarithm of a power grows at most linearly in the exponent. -/
theorem posLog_pow_le (y : ℝ) (n : ℕ) : Real.posLog (y ^ n) ≤ (n : ℝ) * Real.posLog y := by
  induction n with
  | zero => simp [Real.posLog]
  | succ m ih =>
      have hstep : Real.posLog (y ^ (m + 1)) ≤ Real.posLog y + Real.posLog (y ^ m) := by
        rw [pow_succ, mul_comm]
        exact Real.posLog_mul
      have : (((m : ℝ) + 1)) * Real.posLog y = Real.posLog y + (m : ℝ) * Real.posLog y := by ring
      push_cast
      linarith [hstep, ih]

/-- **The weight of a grouped coefficient.**  Each fibre sum is controlled by the weights of the
coefficients and of the other quantities, with one `log 2` per monomial. -/
theorem posLog_norm_groupedCoeff_le (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → ℂ)
    (x : Fin (k + 1) → ℂ) (j : ℕ) :
    Real.posLog ‖groupedCoeff S A x j‖
      ≤ (∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
          (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (S.card : ℝ) * Real.log 2 := by
  classical
  set T := S.filter (fun e => e (Fin.last k) = j) with hT
  have hnorm : ‖groupedCoeff S A x j‖
      ≤ ∑ e ∈ T, ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖ := by
    rw [groupedCoeff, ← hT]
    exact norm_sum_le _ _
  have hstep1 : Real.posLog ‖groupedCoeff S A x j‖
      ≤ Real.posLog (∑ e ∈ T, ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖) :=
    Real.posLog_le_posLog (norm_nonneg _) hnorm
  have hstep2 := posLog_sum_le T
    (fun e => ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖)
    (fun e _ => norm_nonneg _)
  have hterm : ∀ e ∈ T,
      Real.posLog ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖
        ≤ Real.posLog ‖A e‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖ := by
    intro e _
    have hsplit : ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖
        = ‖A e‖ * ∏ i ∈ Finset.univ.erase (Fin.last k), ‖x i‖ ^ (e i) := by
      rw [norm_mul, norm_prod]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [norm_pow]
    rw [hsplit]
    have h1 : Real.posLog (‖A e‖ * ∏ i ∈ Finset.univ.erase (Fin.last k), ‖x i‖ ^ (e i))
        ≤ Real.posLog ‖A e‖
          + Real.posLog (∏ i ∈ Finset.univ.erase (Fin.last k), ‖x i‖ ^ (e i)) := Real.posLog_mul
    have h2 : Real.posLog (∏ i ∈ Finset.univ.erase (Fin.last k), ‖x i‖ ^ (e i))
        ≤ ∑ i ∈ Finset.univ.erase (Fin.last k), Real.posLog (‖x i‖ ^ (e i)) :=
      posLog_prod_le _ _
    have h3 : ∑ i ∈ Finset.univ.erase (Fin.last k), Real.posLog (‖x i‖ ^ (e i))
        ≤ ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖ :=
      Finset.sum_le_sum fun i _ => posLog_pow_le _ _
    linarith
  have hsum : ∑ e ∈ T,
      Real.posLog ‖A e * ∏ i ∈ Finset.univ.erase (Fin.last k), (x i) ^ (e i)‖
      ≤ ∑ e ∈ T, (Real.posLog ‖A e‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖) :=
    Finset.sum_le_sum hterm
  have hcard : (T.card : ℝ) ≤ (S.card : ℝ) := by
    have : T.card ≤ S.card := Finset.card_filter_le _ _
    exact_mod_cast this
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmul : (T.card : ℝ) * Real.log 2 ≤ (S.card : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hcard hlog2
  linarith

/-! ## The Clunie estimate in one inequality -/

/-- The fibres below the top degree assemble into a sub-sum of the whole monomial family. -/
theorem sum_fibres_le {S : Finset (Fin (k + 1) → ℕ)} (N : ℕ) (g : (Fin (k + 1) → ℕ) → ℝ)
    (hg : ∀ e ∈ S, 0 ≤ g e) :
    ∑ j ∈ Finset.range N, ∑ e ∈ S.filter (fun e => e (Fin.last k) = j), g e
      ≤ ∑ e ∈ S, g e := by
  classical
  have hmaps : ∀ e ∈ S.filter (fun e => e (Fin.last k) < N),
      e (Fin.last k) ∈ Finset.range N := by
    intro e he
    exact Finset.mem_range.mpr (Finset.mem_filter.mp he).2
  have hfib : ∑ j ∈ Finset.range N, ∑ e ∈ S.filter (fun e => e (Fin.last k) = j), g e
      = ∑ e ∈ S.filter (fun e => e (Fin.last k) < N), g e := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    rw [Finset.filter_filter]
    have hjN : j < N := Finset.mem_range.mp hj
    refine Finset.filter_congr ?_
    intro e _
    have hiff : (e (Fin.last k) < N ∧ e (Fin.last k) = j) ↔ (e (Fin.last k) = j) := by
      constructor
      · rintro ⟨-, hjj⟩
        exact hjj
      · intro hjj
        exact ⟨by rw [hjj]; exact hjN, hjj⟩
    exact hiff.symm
  rw [hfib]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro e he _
  exact hg e he

/-- **The Clunie estimate.**  If a monomial relation among `x_0, …, x_last` vanishes and its top
grouped coefficient is nonzero, then the weight of the last quantity is bounded by the weights of the
coefficients, the weights of the other quantities, the reciprocal weight of the top coefficient, and
an explicit combinatorial constant. -/
theorem posLog_norm_last_le_weight {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (hrel : ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) = 0)
    (htop : groupedCoeff S A x N ≠ 0) :
    Real.posLog ‖x (Fin.last k)‖
      ≤ (∑ e ∈ S, (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (N : ℝ) * Real.posLog (1 / ‖groupedCoeff S A x N‖)
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  classical
  have hbase := posLog_norm_last_le_sum hN1 hN hrel htop
  have hratio : ∀ j, Real.posLog ‖groupedCoeff S A x j / groupedCoeff S A x N‖
      ≤ Real.posLog ‖groupedCoeff S A x j‖
        + Real.posLog (1 / ‖groupedCoeff S A x N‖) := by
    intro j
    have heq : ‖groupedCoeff S A x j / groupedCoeff S A x N‖
        = ‖groupedCoeff S A x j‖ * (1 / ‖groupedCoeff S A x N‖) := by
      rw [norm_div]
      ring
    rw [heq]
    exact Real.posLog_mul
  have hsum1 : ∑ j ∈ Finset.range N,
      Real.posLog ‖groupedCoeff S A x j / groupedCoeff S A x N‖
      ≤ ∑ j ∈ Finset.range N, (Real.posLog ‖groupedCoeff S A x j‖
          + Real.posLog (1 / ‖groupedCoeff S A x N‖)) :=
    Finset.sum_le_sum fun j _ => hratio j
  have hsum2 : ∑ j ∈ Finset.range N, (Real.posLog ‖groupedCoeff S A x j‖
        + Real.posLog (1 / ‖groupedCoeff S A x N‖))
      = (∑ j ∈ Finset.range N, Real.posLog ‖groupedCoeff S A x j‖)
        + (N : ℝ) * Real.posLog (1 / ‖groupedCoeff S A x N‖) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcoeff : ∀ j ∈ Finset.range N, Real.posLog ‖groupedCoeff S A x j‖
      ≤ (∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
          (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (S.card : ℝ) * Real.log 2 := fun j _ => posLog_norm_groupedCoeff_le S A x j
  have hsum3 : ∑ j ∈ Finset.range N, Real.posLog ‖groupedCoeff S A x j‖
      ≤ ∑ j ∈ Finset.range N, ((∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
            (Real.posLog ‖A e‖
              + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
          + (S.card : ℝ) * Real.log 2) :=
    Finset.sum_le_sum hcoeff
  have hsum4 : ∑ j ∈ Finset.range N, ((∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
        (Real.posLog ‖A e‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (S.card : ℝ) * Real.log 2)
      = (∑ j ∈ Finset.range N, ∑ e ∈ S.filter (fun e => e (Fin.last k) = j),
          (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (N : ℝ) * ((S.card : ℝ) * Real.log 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnn : ∀ e ∈ S, (0 : ℝ) ≤ Real.posLog ‖A e‖
      + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖ := by
    intro e _
    have h1 : (0 : ℝ) ≤ Real.posLog ‖A e‖ := Real.posLog_nonneg
    have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖ := by
      refine Finset.sum_nonneg fun i _ => ?_
      have hp : (0 : ℝ) ≤ Real.posLog ‖x i‖ := Real.posLog_nonneg
      positivity
    linarith
  have hsum5 := sum_fibres_le (S := S) N
    (fun e => Real.posLog ‖A e‖
      + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖) hnn
  linarith [hbase, hsum1, hsum2.le, hsum2.ge, hsum3, hsum4.le, hsum4.ge, hsum5]

/-! ## The Clunie contradiction -/

/-- The weight the Clunie estimate bounds the dependent state by. -/
noncomputable def clunieWeight (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → ℂ)
    (x : Fin (k + 1) → ℂ) (N : ℕ) : ℝ :=
  (∑ e ∈ S, (Real.posLog ‖A e‖
      + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
    + (N : ℝ) * Real.posLog (1 / ‖groupedCoeff S A x N‖)
    + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2

theorem posLog_norm_last_le_clunieWeight {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (hrel : ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) = 0)
    (htop : groupedCoeff S A x N ≠ 0) :
    Real.posLog ‖x (Fin.last k)‖ ≤ clunieWeight S A x N :=
  posLog_norm_last_le_weight hN1 hN hrel htop

/-- **A separated point admits no relation.**  If at some point the last quantity outgrows the
Clunie weight, then no monomial relation with nonvanishing top grouped coefficient can hold
there. -/
theorem sum_ne_zero_of_clunieWeight_lt {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (htop : groupedCoeff S A x N ≠ 0)
    (hsep : clunieWeight S A x N < Real.posLog ‖x (Fin.last k)‖) :
    ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) ≠ 0 := by
  intro hrel
  have := posLog_norm_last_le_clunieWeight hN1 hN hrel htop
  linarith

/-- **Growth separation forbids algebraic dependence.**  If at a single point the last state
outgrows the Clunie weight of a candidate relation whose top grouped coefficient does not vanish
there, then that relation cannot hold identically. -/
theorem not_forall_relation_of_separated {F : Fin (k + 1) → ℂ → ℂ}
    {A : (Fin (k + 1) → ℕ) → ℂ → ℂ} {S : Finset (Fin (k + 1) → ℕ)} {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ e ∈ S, e (Fin.last k) ≤ N) (z : ℂ)
    (htop : groupedCoeff S (fun e => A e z) (fun i => F i z) N ≠ 0)
    (hsep : clunieWeight S (fun e => A e z) (fun i => F i z) N
        < Real.posLog ‖F (Fin.last k) z‖) :
    ¬ (∀ w : ℂ, ∑ e ∈ S, A e w * ∏ i, (F i w) ^ (e i) = 0) := by
  intro hall
  exact sum_ne_zero_of_clunieWeight_lt hN1 hN htop hsep (hall z)

end GaloisForLFunctions.HTGeometry
