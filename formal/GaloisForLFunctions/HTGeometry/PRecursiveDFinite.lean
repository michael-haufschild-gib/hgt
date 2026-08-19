import Mathlib
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# P-recursive coefficient sequences have D-finite generating series

A sequence obeying a linear recurrence with polynomial coefficients has a generating power series
annihilated, up to a polynomial, by a linear differential operator with polynomial coefficients.

The mechanism avoids the Weyl algebra entirely.  Applying `X^m·(d/dX)^{m+j}` to a power series
multiplies its `(n+j)`-th coefficient by

```text
(n − m + 1)(n − m + 2)⋯(n + j) = risingPoly j (n) · fallingPoly m (n),
```

so the coefficient patterns realizable at shift `j` are exactly `risingPoly j` times the span of
the falling factorials — that is, `risingPoly j` times everything.  Multiplying the recurrence by
`risingPoly d` therefore makes every coefficient polynomial realizable simultaneously.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Falling and rising factorials -/

/-- The falling factorial `X(X−1)⋯(X−m+1)`. -/
def fallingPoly (m : ℕ) : Polynomial ℂ := ∏ s ∈ Finset.range m, (X - C (s : ℂ))

/-- The rising factorial `(X+1)(X+2)⋯(X+i)`. -/
def risingPoly (i : ℕ) : Polynomial ℂ := ∏ t ∈ Finset.range i, (X + C ((t : ℂ) + 1))

theorem fallingPoly_monic (m : ℕ) : (fallingPoly m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem risingPoly_monic (i : ℕ) : (risingPoly i).Monic := by
  refine monic_prod_of_monic _ _ fun (t : ℕ) _ => ?_
  have : (X + C ((t : ℂ) + 1)) = X - C (-((t : ℂ) + 1)) := by
    rw [map_neg, sub_neg_eq_add]
  rw [this]
  exact monic_X_sub_C _

theorem natDegree_fallingPoly (m : ℕ) : (fallingPoly m).natDegree = m := by
  have hne : ∀ s ∈ Finset.range m, ((X : Polynomial ℂ) - C ((s : ℂ))) ≠ 0 :=
    fun s _ => (monic_X_sub_C ((s : ℂ))).ne_zero
  rw [fallingPoly, natDegree_prod (Finset.range m) (fun s : ℕ => X - C ((s : ℂ))) hne]
  have hdeg : ∀ s ∈ Finset.range m, ((X : Polynomial ℂ) - C ((s : ℂ))).natDegree = 1 :=
    fun s _ => natDegree_X_sub_C _
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem risingPoly_ne_zero (i : ℕ) : risingPoly i ≠ 0 := (risingPoly_monic i).ne_zero

theorem eval_fallingPoly (m : ℕ) (w : ℂ) :
    (fallingPoly m).eval w = ∏ s ∈ Finset.range m, (w - (s : ℂ)) := by
  rw [fallingPoly, eval_prod]
  exact Finset.prod_congr rfl fun s _ => by simp

theorem eval_risingPoly (i : ℕ) (w : ℂ) :
    (risingPoly i).eval w = ∏ t ∈ Finset.range i, (w + ((t : ℂ) + 1)) := by
  rw [risingPoly, eval_prod]
  exact Finset.prod_congr rfl fun t _ => by simp

/-- **The splitting identity.**  A rising factorial of length `m + j` starting `m` steps back
factors as the rising factorial of length `j` times the falling factorial of length `m`. -/
theorem eval_risingPoly_add (m j : ℕ) (w : ℂ) :
    (risingPoly (m + j)).eval w
      = (risingPoly j).eval (w + m) * (fallingPoly m).eval (w + m) := by
  have hL : (risingPoly (m + j)).eval w
      = (∏ t ∈ Finset.range m, (w + ((t : ℂ) + 1)))
        * ∏ t ∈ Finset.range j, (w + (((m + t : ℕ) : ℂ) + 1)) := by
    rw [eval_risingPoly, Finset.prod_range_add]
  have hR1 : (risingPoly j).eval (w + m)
      = ∏ t ∈ Finset.range j, (w + (((m + t : ℕ) : ℂ) + 1)) := by
    rw [eval_risingPoly]
    exact Finset.prod_congr rfl fun t _ => by push_cast; ring
  have hR2 : (fallingPoly m).eval (w + m) = ∏ t ∈ Finset.range m, (w + ((t : ℂ) + 1)) := by
    rw [eval_fallingPoly, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun s hs => ?_
    have hsm : s < m := Finset.mem_range.mp hs
    have hcast : ((m - 1 - s : ℕ) : ℂ) = (m : ℂ) - 1 - (s : ℂ) := by
      push_cast [Nat.cast_sub (by omega : s ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    rw [hcast]
    ring
  rw [hL, hR1, hR2, mul_comm]

/-! ## The falling factorials span the polynomial ring -/

theorem degree_fallingPoly (m : ℕ) : (fallingPoly m).degree = m := by
  rw [degree_eq_natDegree (fallingPoly_monic m).ne_zero, natDegree_fallingPoly]

theorem fallingPoly_span : ∀ (n : ℕ) (f : Polynomial ℂ), f.natDegree ≤ n →
    f ∈ Submodule.span ℂ (Set.range fallingPoly) := by
  intro n
  induction n with
  | zero =>
      intro f hf
      have hC : f = C (f.coeff 0) := eq_C_of_natDegree_le_zero hf
      have h0 : fallingPoly 0 = 1 := by simp [fallingPoly]
      have hsm : f = (f.coeff 0) • fallingPoly 0 := by
        rw [h0]
        conv_lhs => rw [hC]
        rw [Polynomial.smul_eq_C_mul, mul_one]
      rw [hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ n ih =>
      intro f hf
      by_cases hd : f.natDegree ≤ n
      · exact ih f hd
      · have hdeg : f.natDegree = n + 1 := by omega
        have hf0 : f ≠ 0 := by
          intro h
          rw [h, natDegree_zero] at hdeg
          omega
        set c := f.leadingCoeff with hc
        have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hf0
        set g : Polynomial ℂ := f - C c * fallingPoly (n + 1) with hg
        have hdegF : f.degree = ((n + 1 : ℕ) : WithBot ℕ) := by
          rw [degree_eq_natDegree hf0, hdeg]
        have hdegP : (C c * fallingPoly (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
          rw [degree_mul, degree_C hc0, zero_add, degree_fallingPoly]
        have hlc : f.leadingCoeff = (C c * fallingPoly (n + 1)).leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_C, (fallingPoly_monic (n + 1)).leadingCoeff, mul_one]
        have hlt : g.degree < f.degree := by
          rw [hg]
          exact degree_sub_lt (hdegF.trans hdegP.symm) hf0 hlc
        have hgle : g.natDegree ≤ n := by
          rcases eq_or_ne g 0 with hgz | hgz
          · rw [hgz]; simp
          · have := natDegree_lt_natDegree hgz hlt
            omega
        have hgmem := ih g hgle
        have hfmem : f = g + c • (fallingPoly (n + 1)) := by
          rw [hg, Polynomial.smul_eq_C_mul]
          ring
        rw [hfmem]
        exact Submodule.add_mem _ hgmem
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨n + 1, rfl⟩))

theorem exists_fallingPoly_finsupp (f : Polynomial ℂ) :
    ∃ α : ℕ →₀ ℂ, (α.sum fun m a => a • fallingPoly m) = f :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (fallingPoly_span f.natDegree f le_rfl)


/-! ## Coefficients of the basic operators -/

theorem eval_risingPoly_succ (i : ℕ) (w : ℂ) :
    (risingPoly (i + 1)).eval w = (risingPoly i).eval w * (w + (i : ℂ) + 1) := by
  rw [eval_risingPoly, eval_risingPoly, Finset.prod_range_succ]
  ring

theorem coeff_iterate_derivative : ∀ (i : ℕ) (F : PowerSeries ℂ) (n : ℕ),
    PowerSeries.coeff n ((PowerSeries.derivative ℂ)^[i] F)
      = (risingPoly i).eval (n : ℂ) * PowerSeries.coeff (n + i) F := by
  intro i
  induction i with
  | zero =>
      intro F n
      simp [risingPoly]
  | succ i ih =>
      intro F n
      rw [Function.iterate_succ_apply, ih ((PowerSeries.derivative ℂ) F) n, PowerSeries.coeff_derivative,
        eval_risingPoly_succ]
      have hidx : n + i + 1 = n + (i + 1) := by omega
      rw [hidx]
      push_cast
      ring

theorem eval_fallingPoly_eq_zero_of_lt {m n : ℕ} (h : n < m) :
    (fallingPoly m).eval (n : ℂ) = 0 := by
  rw [eval_fallingPoly]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr h) (by simp)

/-- **The coefficient pattern of `X^m·(d/dX)^{m+j}`.** -/
theorem coeff_shiftOp (F : PowerSeries ℂ) (m j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ m * (PowerSeries.derivative ℂ)^[m + j] F)
      = (risingPoly j).eval (n : ℂ) * (fallingPoly m).eval (n : ℂ)
        * PowerSeries.coeff (n + j) F := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : m ≤ n
  · rw [if_pos h, coeff_iterate_derivative (m + j) F (n - m)]
    have hidx : n - m + (m + j) = n + j := by omega
    rw [hidx]
    have hcast : ((n - m : ℕ) : ℂ) + (m : ℂ) = (n : ℂ) := by
      push_cast [Nat.cast_sub h]
      ring
    rw [eval_risingPoly_add m j ((n - m : ℕ) : ℂ), hcast]
  · rw [if_neg h, eval_fallingPoly_eq_zero_of_lt (by omega)]
    ring


/-! ## P-recursive sequences -/

/-- A sequence is *P-recursive* when it obeys a nontrivial linear recurrence with polynomial
coefficients from some index on. -/
def PRecursive (b : ℕ → ℂ) : Prop :=
  ∃ (d N : ℕ) (q : ℕ → Polynomial ℂ), (∃ j, j ≤ d ∧ q j ≠ 0) ∧
    ∀ n : ℕ, N ≤ n → ∑ j ∈ Finset.range (d + 1), (q j).eval (n : ℂ) * b (n + j) = 0

/-- The cofactor turning `risingPoly j` into `risingPoly d`. -/
def risingCofactor (j d : ℕ) : Polynomial ℂ :=
  ∏ t ∈ Finset.Ico j d, (X + C ((t : ℂ) + 1))

theorem risingPoly_mul_cofactor {j d : ℕ} (h : j ≤ d) :
    risingPoly j * risingCofactor j d = risingPoly d := by
  rw [risingPoly, risingCofactor, risingPoly, Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact Finset.prod_Ico_consecutive _ (Nat.zero_le j) h

theorem risingCofactor_ne_zero (j d : ℕ) : risingCofactor j d ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun t _ => ?_
  intro hc
  have hcoeff := congrArg (fun p => Polynomial.coeff p 1) hc
  simp [Polynomial.coeff_one] at hcoeff


/-! ## The operator attached to a recurrence -/

/-- The power series `∑_{j,m} α_{j,m} · X^m · (d/dX)^{m+j} F`. -/
def opApply (d : ℕ) (α : ℕ → (ℕ →₀ ℂ)) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (d + 1), ∑ m ∈ (α j).support,
    PowerSeries.C (α j m) * (PowerSeries.X ^ m * (PowerSeries.derivative ℂ)^[m + j] F)

theorem coeff_opApply (d : ℕ) (α : ℕ → (ℕ →₀ ℂ)) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (opApply d α F)
      = ∑ j ∈ Finset.range (d + 1),
          (risingPoly j).eval (n : ℂ)
            * (∑ m ∈ (α j).support, α j m * (fallingPoly m).eval (n : ℂ))
            * PowerSeries.coeff (n + j) F := by
  rw [opApply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [PowerSeries.coeff_C_mul, coeff_shiftOp]
  ring

theorem eval_finsupp_sum (α : ℕ →₀ ℂ) (n : ℂ) :
    ((α.sum fun m a => a • fallingPoly m) : Polynomial ℂ).eval n
      = ∑ m ∈ α.support, α m * (fallingPoly m).eval n := by
  rw [Finsupp.sum, eval_finsetSum]
  exact Finset.sum_congr rfl fun m _ => by rw [Polynomial.smul_eq_C_mul, eval_mul, eval_C]

/-- **P-recursive coefficients give a polynomial-coefficient operator annihilating the series up
to a polynomial.** -/
theorem exists_opApply_eventually_zero (F : PowerSeries ℂ)
    (h : PRecursive (fun n => PowerSeries.coeff n F)) :
    ∃ (d N : ℕ) (α : ℕ → (ℕ →₀ ℂ)), (∃ j, j ≤ d ∧ α j ≠ 0) ∧
      ∀ n : ℕ, N ≤ n → PowerSeries.coeff n (opApply d α F) = 0 := by
  obtain ⟨d, N, q, ⟨j₀, hj₀d, hj₀⟩, hrec⟩ := h
  -- the shifted coefficient polynomials
  set g : ℕ → Polynomial ℂ := fun j => risingCofactor j d * q j with hg
  have hgrep : ∀ j, ∃ α : ℕ →₀ ℂ, (α.sum fun m a => a • fallingPoly m) = g j :=
    fun j => exists_fallingPoly_finsupp (g j)
  choose α hα using hgrep
  refine ⟨d, N, α, ⟨j₀, hj₀d, ?_⟩, ?_⟩
  · intro hzero
    have hgz : g j₀ = 0 := by rw [← hα j₀, hzero]; simp
    rw [hg] at hgz
    rcases mul_eq_zero.mp hgz with hc | hq
    · exact risingCofactor_ne_zero j₀ d hc
    · exact hj₀ hq
  · intro n hn
    rw [coeff_opApply]
    have hterm : ∀ j ∈ Finset.range (d + 1),
        (risingPoly j).eval (n : ℂ)
            * (∑ m ∈ (α j).support, α j m * (fallingPoly m).eval (n : ℂ))
            * PowerSeries.coeff (n + j) F
          = (risingPoly d).eval (n : ℂ) * ((q j).eval (n : ℂ)
              * PowerSeries.coeff (n + j) F) := by
      intro j hj
      have hjd : j ≤ d := by
        have := Finset.mem_range.mp hj
        omega
      rw [← eval_finsupp_sum (α j) (n : ℂ), hα j, hg]
      have : (risingPoly j).eval (n : ℂ) * (risingCofactor j d * q j).eval (n : ℂ)
          = (risingPoly d).eval (n : ℂ) * (q j).eval (n : ℂ) := by
        rw [eval_mul, ← mul_assoc, ← eval_mul, risingPoly_mul_cofactor hjd]
      rw [this]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hrec n hn, mul_zero]


/-! ## Taylor series of an entire function -/

theorem differentiable_iteratedDeriv {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    ∀ n, Differentiable ℂ (iteratedDeriv n h)
  | 0 => by simpa using hh
  | (n + 1) => by
      rw [iteratedDeriv_succ]
      exact (differentiable_iteratedDeriv hh n).deriv

theorem iteratedDeriv_id_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) : ∀ n : ℕ,
    iteratedDeriv (n + 1) (fun z : ℂ => z * h z)
      = fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z := by
  intro n
  induction n with
  | zero =>
      rw [iteratedDeriv_one]
      funext z
      have hd : HasDerivAt (fun z : ℂ => z * h z) (1 * h z + z * deriv h z) z :=
        (hasDerivAt_id z).mul (hh z).hasDerivAt
      rw [hd.deriv]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      have hdn : Differentiable ℂ (iteratedDeriv n h) := differentiable_iteratedDeriv hh n
      have hdn1 : Differentiable ℂ (iteratedDeriv (n + 1) h) :=
        differentiable_iteratedDeriv hh (n + 1)
      have hd : HasDerivAt (fun z : ℂ => ((n : ℂ) + 1) * iteratedDeriv n h z
            + z * iteratedDeriv (n + 1) h z)
          (((n : ℂ) + 1) * deriv (iteratedDeriv n h) z
            + (1 * iteratedDeriv (n + 1) h z + z * deriv (iteratedDeriv (n + 1) h) z)) z :=
        (((hdn z).hasDerivAt).const_mul _).add ((hasDerivAt_id z).mul ((hdn1 z).hasDerivAt))
      rw [hd.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      push_cast
      ring

theorem iteratedDeriv_id_mul_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => z * h z) 0 = ((n : ℂ) + 1) * iteratedDeriv n h 0 := by
  rw [iteratedDeriv_id_mul hh n]
  simp

/-- The Taylor series of a function at the origin. -/
def taylorSeries (G : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n G 0 / (n.factorial : ℂ)

theorem coeff_taylorSeries (G : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries G) = iteratedDeriv n G 0 / (n.factorial : ℂ) := by
  rw [taylorSeries, PowerSeries.coeff_mk]

theorem taylorSeries_id_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    taylorSeries (fun z : ℂ => z * h z) = PowerSeries.X * taylorSeries h := by
  ext n
  cases n with
  | zero => simp [coeff_taylorSeries]
  | succ n =>
      rw [coeff_taylorSeries, iteratedDeriv_id_mul_zero hh n, PowerSeries.coeff_succ_X_mul,
        coeff_taylorSeries]
      have hfac : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      have hne : ((n : ℂ) + 1) ≠ 0 := by
        have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      field_simp

theorem taylorSeries_deriv (h : ℂ → ℂ) :
    taylorSeries (deriv h) = (PowerSeries.derivative ℂ) (taylorSeries h) := by
  ext n
  rw [coeff_taylorSeries, PowerSeries.coeff_derivative, coeff_taylorSeries,
    ← iteratedDeriv_succ']
  have hfac : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hne : ((n : ℂ) + 1) ≠ 0 := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  field_simp


theorem contDiffAt_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (x : ℂ) :
    ContDiffAt ℂ (n : ℕ∞) f x := by
  have h := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  exact (h x (Set.mem_univ x)).contDiffAt.of_le (by exact_mod_cast le_top)

theorem taylorSeries_iteratedDeriv {h : ℂ → ℂ} (hh : Differentiable ℂ h) : ∀ i : ℕ,
    taylorSeries (iteratedDeriv i h) = ((PowerSeries.derivative ℂ))^[i] (taylorSeries h)
  | 0 => by simp
  | (i + 1) => by
      rw [Function.iterate_succ_apply', ← taylorSeries_iteratedDeriv hh i, iteratedDeriv_succ,
        taylorSeries_deriv]

theorem differentiable_pow_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => z ^ m * h z) :=
  ((differentiable_id.pow m)).mul hh

theorem taylorSeries_pow_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) : ∀ m : ℕ,
    taylorSeries (fun z : ℂ => z ^ m * h z) = PowerSeries.X ^ m * taylorSeries h
  | 0 => by simp
  | (m + 1) => by
      have hstep : (fun z : ℂ => z ^ (m + 1) * h z) = fun z : ℂ => z * (z ^ m * h z) := by
        funext z
        ring
      rw [hstep, taylorSeries_id_mul (differentiable_pow_mul hh m),
        taylorSeries_pow_mul hh m, pow_succ]
      ring

theorem taylorSeries_add {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    taylorSeries (fun z => f z + g z) = taylorSeries f + taylorSeries g := by
  ext n
  rw [coeff_taylorSeries, map_add, coeff_taylorSeries, coeff_taylorSeries]
  have hfun : (fun z : ℂ => f z + g z) = f + g := rfl
  rw [hfun, iteratedDeriv_add (contDiffAt_of_differentiable hf n 0)
    (contDiffAt_of_differentiable hg n 0)]
  ring

theorem taylorSeries_const_mul (c : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    taylorSeries (fun z => c * f z) = PowerSeries.C c * taylorSeries f := by
  ext n
  rw [coeff_taylorSeries, PowerSeries.coeff_C_mul, coeff_taylorSeries,
    iteratedDeriv_const_mul c (contDiffAt_of_differentiable hf n 0)]
  ring

theorem taylorSeries_zero : taylorSeries (fun _ : ℂ => 0) = 0 := by
  ext n
  rw [coeff_taylorSeries]
  simp

theorem taylorSeries_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℂ (f i)) :
    taylorSeries (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, taylorSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using taylorSeries_zero
  | insert a s ha ih =>
      have hfa : Differentiable ℂ (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Differentiable ℂ (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : Differentiable ℂ (fun z => ∑ i ∈ s, f i z) := by
        have h : Differentiable ℂ (∑ i ∈ s, f i) :=
          fun z => DifferentiableAt.sum fun i hi => (hfs i hi) z
        have hfun : (∑ i ∈ s, f i) = fun z : ℂ => ∑ i ∈ s, f i z := by
          funext z
          simp [Finset.sum_apply]
        rwa [hfun] at h
      have hrw : (fun z : ℂ => ∑ i ∈ insert a s, f i z)
          = fun z : ℂ => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hrw, taylorSeries_add hfa hsum, ih hfs, Finset.sum_insert ha]


/-! ## An entire function with finitely many Taylor coefficients is a polynomial -/

theorem entire_eq_zero_of_iteratedDeriv_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n : ℕ, iteratedDeriv n f 0 = 0) : ∀ z, f z = 0 := by
  have hanal : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hat : AnalyticAt ℂ f 0 := hanal 0 (Set.mem_univ 0)
  have htop : analyticOrderAt f 0 = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun n =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hat).mpr fun i _ => h i
  have hev : ∀ᶠ z in nhds (0 : ℂ), f z = 0 := analyticOrderAt_eq_top.mp htop
  intro z
  exact hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hev (Set.mem_univ z)

theorem taylorSeries_one : taylorSeries (fun _ : ℂ => (1 : ℂ)) = 1 := by
  ext n
  rw [coeff_taylorSeries]
  cases n with
  | zero => simp
  | succ n =>
      have hzero : iteratedDeriv (n + 1) (fun _ : ℂ => (1 : ℂ)) 0 = 0 := by
        rw [iteratedDeriv_succ']
        have : deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
          funext z
          simp
        rw [this]
        simp
      rw [hzero, zero_div, PowerSeries.coeff_one]
      simp

theorem taylorSeries_pow (m : ℕ) : taylorSeries (fun z : ℂ => z ^ m) = PowerSeries.X ^ m := by
  have hfun : (fun z : ℂ => z ^ m) = fun z : ℂ => z ^ m * (1 : ℂ) := by
    funext z
    ring
  rw [hfun, taylorSeries_pow_mul (differentiable_const (1 : ℂ)) m, taylorSeries_one, mul_one]

theorem exists_poly_of_taylorSeries_eventually_zero {Ψ : ℂ → ℂ} (hΨ : Differentiable ℂ Ψ)
    {N : ℕ} (h : ∀ n : ℕ, N ≤ n → PowerSeries.coeff n (taylorSeries Ψ) = 0) :
    ∃ P : Polynomial ℂ, ∀ z, Ψ z = P.eval z := by
  classical
  set P : Polynomial ℂ :=
    ∑ n ∈ Finset.range N, Polynomial.C (PowerSeries.coeff n (taylorSeries Ψ)) * X ^ n with hP
  refine ⟨P, ?_⟩
  have hPdiff : Differentiable ℂ (fun z : ℂ => P.eval z) := Polynomial.differentiable P
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n (taylorSeries (fun z : ℂ => P.eval z))
      = PowerSeries.coeff n (taylorSeries Ψ) := by
    intro n
    have hPfun : (fun z : ℂ => P.eval z)
        = fun z : ℂ => ∑ k ∈ Finset.range N,
            PowerSeries.coeff k (taylorSeries Ψ) * z ^ k := by
      funext z
      rw [hP, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun k _ => by simp
    rw [hPfun, taylorSeries_finsetSum (Finset.range N)
      (fun k => fun z : ℂ => PowerSeries.coeff k (taylorSeries Ψ) * z ^ k)
      (fun k _ => (differentiable_pow k).const_mul _)]
    rw [map_sum]
    have hterm : ∀ k ∈ Finset.range N,
        PowerSeries.coeff n (taylorSeries
            (fun z : ℂ => PowerSeries.coeff k (taylorSeries Ψ) * z ^ k))
          = if n = k then PowerSeries.coeff n (taylorSeries Ψ) else 0 := by
      intro k _
      rw [taylorSeries_const_mul _ (differentiable_pow k), taylorSeries_pow,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      split_ifs with hnk
      · subst hnk; ring
      · rw [mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hn : n < N
    · rw [Finset.sum_ite_eq (Finset.range N) n]
      rw [if_pos (Finset.mem_range.mpr hn)]
    · rw [Finset.sum_eq_zero, (h n (by omega)).symm]
      intro k hk
      exact if_neg (by intro hc; subst hc; exact hn (Finset.mem_range.mp hk))
  intro z
  have hdiff : ∀ n : ℕ, iteratedDeriv n (fun w : ℂ => Ψ w - P.eval w) 0 = 0 := by
    intro n
    have hsub : (fun w : ℂ => Ψ w - P.eval w) = Ψ - fun w : ℂ => P.eval w := rfl
    rw [hsub, iteratedDeriv_sub (contDiffAt_of_differentiable hΨ n 0)
      (contDiffAt_of_differentiable hPdiff n 0)]
    have hc := hcoeff n
    rw [coeff_taylorSeries (fun z : ℂ => P.eval z) n, coeff_taylorSeries Ψ n] at hc
    have hfac : ((n.factorial : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have heq : iteratedDeriv n (fun z : ℂ => P.eval z) 0 = iteratedDeriv n Ψ 0 := by
      field_simp at hc
      exact hc
    rw [heq]
    ring
  have hz := entire_eq_zero_of_iteratedDeriv_zero (hΨ.sub hPdiff) hdiff z
  rw [Pi.sub_apply] at hz
  linear_combination hz


/-! ## The analytic operator -/

/-- The analytic differential operator `∑_{j,m} α_{j,m} z^m (d/dz)^{m+j}` applied to `G`. -/
def opFun (d : ℕ) (α : ℕ → (ℕ →₀ ℂ)) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), ∑ m ∈ (α j).support,
    α j m * (z ^ m * iteratedDeriv (m + j) G z)

theorem differentiable_opTerm {G : ℂ → ℂ} (hG : Differentiable ℂ G) (c : ℂ) (m i : ℕ) :
    Differentiable ℂ (fun z : ℂ => c * (z ^ m * iteratedDeriv i G z)) :=
  (differentiable_pow_mul (differentiable_iteratedDeriv hG i) m).const_mul c

theorem differentiable_opInner {G : ℂ → ℂ} (hG : Differentiable ℂ G) (α : ℕ → (ℕ →₀ ℂ)) (j : ℕ) :
    Differentiable ℂ (fun z : ℂ => ∑ m ∈ (α j).support,
      α j m * (z ^ m * iteratedDeriv (m + j) G z)) := by
  have h : Differentiable ℂ (∑ m ∈ (α j).support,
      fun z : ℂ => α j m * (z ^ m * iteratedDeriv (m + j) G z)) :=
    fun z => DifferentiableAt.sum fun m _ => (differentiable_opTerm hG (α j m) m (m + j)) z
  have hfun : (∑ m ∈ (α j).support,
      fun z : ℂ => α j m * (z ^ m * iteratedDeriv (m + j) G z))
      = fun z : ℂ => ∑ m ∈ (α j).support, α j m * (z ^ m * iteratedDeriv (m + j) G z) := by
    funext z
    simp [Finset.sum_apply]
  rwa [hfun] at h

theorem differentiable_opFun {G : ℂ → ℂ} (hG : Differentiable ℂ G) (d : ℕ)
    (α : ℕ → (ℕ →₀ ℂ)) : Differentiable ℂ (opFun d α G) := by
  have h : Differentiable ℂ (∑ j ∈ Finset.range (d + 1),
      fun z : ℂ => ∑ m ∈ (α j).support, α j m * (z ^ m * iteratedDeriv (m + j) G z)) :=
    fun z => DifferentiableAt.sum fun j _ => (differentiable_opInner hG α j) z
  have hfun : (∑ j ∈ Finset.range (d + 1),
      fun z : ℂ => ∑ m ∈ (α j).support, α j m * (z ^ m * iteratedDeriv (m + j) G z))
      = opFun d α G := by
    funext z
    simp only [opFun, Finset.sum_apply]
  rwa [hfun] at h

theorem taylorSeries_opFun {G : ℂ → ℂ} (hG : Differentiable ℂ G) (d : ℕ) (α : ℕ → (ℕ →₀ ℂ)) :
    taylorSeries (opFun d α G) = opApply d α (taylorSeries G) := by
  have hshow : opFun d α G = fun z : ℂ => ∑ j ∈ Finset.range (d + 1), ∑ m ∈ (α j).support,
      α j m * (z ^ m * iteratedDeriv (m + j) G z) := rfl
  rw [hshow, opApply]
  rw [taylorSeries_finsetSum (Finset.range (d + 1))
      (fun j => fun z : ℂ => ∑ m ∈ (α j).support, α j m * (z ^ m * iteratedDeriv (m + j) G z))
      (fun j _ => differentiable_opInner hG α j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylorSeries_finsetSum (α j).support
    (fun m => fun z : ℂ => α j m * (z ^ m * iteratedDeriv (m + j) G z))
    (fun m _ => differentiable_opTerm hG (α j m) m (m + j))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [taylorSeries_const_mul _
      (differentiable_pow_mul (differentiable_iteratedDeriv hG (m + j)) m),
    taylorSeries_pow_mul (differentiable_iteratedDeriv hG (m + j)) m,
    taylorSeries_iteratedDeriv hG (m + j)]

/-- **P-recursive Taylor coefficients force a polynomial-coefficient differential relation.** -/
theorem exists_opFun_eq_polyEval {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (h : PRecursive (fun n => PowerSeries.coeff n (taylorSeries G))) :
    ∃ (d : ℕ) (α : ℕ → (ℕ →₀ ℂ)) (P : Polynomial ℂ), (∃ j, j ≤ d ∧ α j ≠ 0) ∧
      ∀ z, opFun d α G z = P.eval z := by
  obtain ⟨d, N, α, hne, hzero⟩ := exists_opApply_eventually_zero (taylorSeries G) h
  have hcoeff : ∀ n : ℕ, N ≤ n → PowerSeries.coeff n (taylorSeries (opFun d α G)) = 0 := by
    intro n hn
    rw [taylorSeries_opFun hG]
    exact hzero n hn
  obtain ⟨P, hP⟩ :=
    exists_poly_of_taylorSeries_eventually_zero (differentiable_opFun hG d α) hcoeff
  exact ⟨d, α, P, hne, hP⟩


/-! ## The differential-algebraicity conclusion -/

/-- **A polynomial-coefficient linear relation up to a polynomial makes a function differentially
algebraic.** -/
theorem differentiallyAlgebraic_of_opFun {G : ℂ → ℂ} {d : ℕ} {α : ℕ → (ℕ →₀ ℂ)}
    {P : Polynomial ℂ} (hne : ∃ j, j ≤ d ∧ α j ≠ 0)
    (hrel : ∀ z, opFun d α G z = P.eval z) :
    GaloisForLFunctions.DifferentiallyAlgebraic G := by
  classical
  obtain ⟨j₀, hj₀d, hj₀⟩ := hne
  obtain ⟨m₀, hm₀⟩ := Finsupp.support_nonempty_iff.mpr hj₀
  set M : ℕ := (Finset.range (d + 1)).sup (fun j => (α j).support.sup (fun m => m + j)) with hM
  have hle : ∀ j ∈ Finset.range (d + 1), ∀ m ∈ (α j).support, m + j ≤ M := by
    intro j hj m hm
    exact le_trans (Finset.le_sup (f := fun m => m + j) hm) (Finset.le_sup (s := Finset.range (d+1))
      (f := fun j => (α j).support.sup (fun m => m + j)) hj)
  have hj₀mem : j₀ ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  -- the index of the jet slot carrying the order `m + j` derivative
  set idx : ℕ → ℕ → Fin (M + 2) := fun j m => (((m + j : ℕ) : Fin (M + 1))).succ with hidx
  have hidxval : ∀ j ∈ Finset.range (d + 1), ∀ m ∈ (α j).support,
      (((m + j : ℕ) : Fin (M + 1)) : ℕ) = m + j := by
    intro j hj m hm
    exact Fin.val_cast_of_lt (by have := hle j hj m hm; omega)
  refine ⟨M, (∑ j ∈ Finset.range (d + 1), ∑ m ∈ (α j).support,
      MvPolynomial.C (α j m) * (MvPolynomial.X (0 : Fin (M + 2))) ^ m
        * MvPolynomial.X (idx j m))
      - Polynomial.aeval (MvPolynomial.X (0 : Fin (M + 2))) P, ?_, ?_⟩
  · -- nonvanishing
    intro hzero
    set μ : Fin (M + 2) →₀ ℕ :=
      Finsupp.single 0 m₀ + Finsupp.single (idx j₀ m₀) 1 with hμ
    have hidxne : (idx j₀ m₀) ≠ 0 := by
      rw [hidx]
      exact Fin.succ_ne_zero _
    have hcoeffP : MvPolynomial.coeff μ
        (Polynomial.aeval (MvPolynomial.X (0 : Fin (M + 2))) P) = 0 := by
      induction P using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, hp, hq, add_zero]
      | monomial n a =>
          rw [Polynomial.aeval_monomial]
          have : (algebraMap ℂ (MvPolynomial (Fin (M + 2)) ℂ)) a
              = MvPolynomial.C a := rfl
          rw [this, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
            MvPolynomial.coeff_monomial]
          refine if_neg fun hc => ?_
          have hsupp : (idx j₀ m₀) ∈ μ.support := by
            rw [hμ]
            simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
              Finsupp.single_apply]
            rw [if_neg (fun hc2 => hidxne hc2.symm)]
            omega
          rw [← hc] at hsupp
          have := Finsupp.support_single_subset hsupp
          simp at this
          exact hidxne this.symm
    sorry
  · intro z
    sorry

end GaloisForLFunctions.HTGeometry
