import GaloisForLFunctions.RHTower.PrimeLagPowerSavingLowerBound

/-!
# Bounded-complexity JAS product tests see only `sup Re ρ − ½`

The JAS product test on a finite set `P` of primes `p > X` at level `σ` is
`Re Σ_ρ w_ρ ∏_{p ∈ P} (1 + z_p A + z̄_p B + |z_p|²)`, with `A = p^{−(ρ+σ−½)}`, `B = p^{−(1−ρ+σ−½)}` and
`w_ρ = 1/(ρ(1−ρ))`.

**Theorem** (`jasProductAggregate_re_ge`).  If `|Re ρ − ½| ≤ σ` for every zero and
`ε_ρ = X^{−(σ−|Re ρ−½|)}`, the test value is at least
`∏(1 + |z_p|²) · (Φ(0) − Σ_ρ |w_ρ| ((1+ε_ρ)^{|P|} − 1))`.  Each factor is `(1 + |z|²)(1 + u)` with
`|u| ≤ |z|(|A| + |B|)/(1 + |z|²) ≤ ε_ρ`.  Under a half-plane `|Re ρ − ½| ≤ α` all `ε_ρ ≤ X^{−(σ−α)}`
(`jasProductAggregate_re_ge_of_halfPlane`).

Consequences.
* **Prime-budget producer** (`eventually_jasProductPositive_of_primeBudget`, unconditional).  For
  every `σ` and every `K`, once `X` is large, positivity holds on every finite set `P` of primes `> X`
  with `Σ_{p∈P} p^{−(σ−½)} ≤ K`.  The zero-sum bound `jasProductAggregate_re_ge_exp` needs no
  hypothesis; each zero's excess is `≤ exp(K X^{|Re ρ−½|−½}) − 1 → 0` and dominated convergence
  applies.  For `σ ≥ ½` this contains all sets of at most `K X^{σ−½}` primes
  (`eventually_jasProductPositiveAboveCard_of_le_mul_rpow`); for `σ > 3/2` it contains all sets.
* **Few-primes producer at every level.**  Under a half-plane `α ≤ σ`, positivity holds on every set
  of at most `c X^{σ−α}` primes `> X`, with `c = log(1 + Φ(0)/Σ|w_ρ|)`.  Unconditionally (`α = ½`)
  this holds for every `σ ≥ ½`.
* **Complexity–abscissa law** (`exists_jasProductPositiveAboveCard_iff`).  For a fixed number `k ≥ 1`
  of primes and a level `0 ≤ σ < ½`: positivity on all `k`-sets of large primes at level `σ` holds
  for some `X` if a half-plane `α < σ` holds, and it forces the half-plane `σ`.  So every bounded
  complexity has abscissa `sup Re ρ − ½`, the single-prime abscissa.  Off RH the unrestricted product
  abscissa is `sup Re ρ + ½`; the extra `1` comes only from sets whose size grows with `X`.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Product positivity on every set of at most `k` primes `p > X`. -/
def JasProductPositiveAboveCard (X : ℕ) (σ : ℝ) (k : ℕ) : Prop :=
  ∀ P : Finset Nat.Primes, P.card ≤ k → (∀ p ∈ P, X < (p : ℕ)) → ∀ z : Nat.Primes → ℂ,
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

theorem JasProductPositiveAbove.card {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ) (k : ℕ) :
    JasProductPositiveAboveCard X σ k := fun P _ hP z => h P hP z

/-! ## Elementary bounds -/

/-- `‖∏(1 + u_i) − 1‖ ≤ (1 + ε)^n − 1` when every `‖u_i‖ ≤ ε`. -/
theorem norm_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) {ε : ℝ}
    (hε : ∀ i ∈ s, ‖u i‖ ≤ ε) : ‖∏ i ∈ s, (1 + u i) - 1‖ ≤ (1 + ε) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h2 := hε a (Finset.mem_insert_self a s)
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans h2
    have h1 := ih (fun i hi => hε i (Finset.mem_insert_of_mem hi))
    have e : (1 + u a) * ∏ i ∈ s, (1 + u i) - 1 =
        (1 + u a) * (∏ i ∈ s, (1 + u i) - 1) + u a := by ring
    have h3 : ‖1 + u a‖ ≤ 1 + ε := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    rw [e]
    calc ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - 1) + u a‖
        ≤ ‖1 + u a‖ * ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (1 + ε) * ((1 + ε) ^ s.card - 1) + ε :=
          add_le_add (mul_le_mul h3 h1 (norm_nonneg _) (by linarith)) h2
      _ = (1 + ε) ^ (s.card + 1) - 1 := by ring

/-- A Bernoulli factor is `(1 + |z|²)(1 + u)` with `u = (zA + z̄B)/(1 + |z|²)`. -/
theorem jasBernoulliFactor_eq_mul (A B z : ℂ) :
    jasBernoulliFactor A B z = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) *
      (1 + (z * A + conj z * B) / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have h : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [mul_add, mul_one, mul_div_cancel₀ _ h, jasBernoulliFactor, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem norm_jasBernoulliRatio_le {A B z : ℂ} {ε : ℝ} (hA : ‖A‖ ≤ ε) (hB : ‖B‖ ≤ ε) :
    ‖(z * A + conj z * B) / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)‖ ≤ ε := by
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hε : 0 ≤ ε := (norm_nonneg _).trans hA
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_le_iff₀ hpos]
  have hz := norm_nonneg z
  calc ‖z * A + conj z * B‖ ≤ ‖z‖ * ε + ‖z‖ * ε := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact add_le_add (mul_le_mul_of_nonneg_left hA hz) (mul_le_mul_of_nonneg_left hB hz)
    _ ≤ ε * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖z‖ - 1)]

/-- Under `|Re ρ − ½| ≤ α`, `|p^{−(ρ+σ−½)}| ≤ p^{−(σ−α)}`. -/
theorem norm_jasHoloA_dressed_le_of_halfPlane {alpha : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ≤ Real.exp (-(σ - alpha) * Real.log p) := by
  rw [norm_jasHoloA]
  have h := (abs_le.mp (abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)).1
  have hL := log_prime_pos p
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.ofReal_re]
  nlinarith [mul_nonneg (show 0 ≤ (q.1 : ℂ).re - 1 / 2 + alpha by linarith) hL.le]

/-- Under `|Re ρ − ½| ≤ α`, `|p^{−(1−ρ+σ−½)}| ≤ p^{−(σ−α)}`. -/
theorem norm_jasHoloB_dressed_le_of_halfPlane {alpha : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p‖ ≤ Real.exp (-(σ - alpha) * Real.log p) := by
  rw [norm_jasHoloB]
  have h := (abs_le.mp (abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)).2
  have hL := log_prime_pos p
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.ofReal_re]
  nlinarith [mul_nonneg (show 0 ≤ alpha - ((q.1 : ℂ).re - 1 / 2) by linarith) hL.le]

/-! ## The lower bound -/

/-- `|p^{−(ρ+σ−½)}| ≤ p^{−(σ−|Re ρ−½|)}`. -/
theorem norm_jasHoloA_dressed_le_abs (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ≤
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) := by
  rw [norm_jasHoloA]
  have h := neg_abs_le ((q.1 : ℂ).re - 1 / 2)
  have hL := log_prime_pos p
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.ofReal_re]
  nlinarith [mul_nonneg (show 0 ≤ (q.1 : ℂ).re - 1 / 2 + |(q.1 : ℂ).re - 1 / 2| by linarith) hL.le]

/-- `|p^{−(1−ρ+σ−½)}| ≤ p^{−(σ−|Re ρ−½|)}`. -/
theorem norm_jasHoloB_dressed_le_abs (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p‖ ≤
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) := by
  rw [norm_jasHoloB]
  have h := le_abs_self ((q.1 : ℂ).re - 1 / 2)
  have hL := log_prime_pos p
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.ofReal_re]
  nlinarith [mul_nonneg (show 0 ≤ |(q.1 : ℂ).re - 1 / 2| - ((q.1 : ℂ).re - 1 / 2) by linarith) hL.le]

/-- **Product tests are controlled by a zero sum.**  If `|Re ρ − ½| ≤ σ` for every zero, then with
`ε_ρ = X^{−(σ−|Re ρ−½|)}` the product test value on `P` (primes `> X`) is at least
`∏(1 + |z_p|²) · (Φ(0) − Σ_ρ |w_ρ| ((1 + ε_ρ)^{|P|} − 1))`. -/
theorem jasProductAggregate_re_ge {σ : ℝ} (hσ : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ)
    {X : ℕ} (hX : 1 ≤ X) (P : Finset Nat.Primes) (hP : ∀ p ∈ P, X < (p : ℕ))
    (z : Nat.Primes → ℂ) :
    (∏ p ∈ P, (1 + ‖z p‖ ^ 2)) * (poleSharpConstant - ∑' q : XiZeroCopy,
      ((1 + Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X)) ^ P.card - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤
    (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨e, hedef⟩ : ∃ e : XiZeroCopy → ℝ, e = fun q =>
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∏ p ∈ P, (1 + ‖z p‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hfold : ∀ q : XiZeroCopy, ((1 + Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X)) ^
      P.card - 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = ((1 + e q) ^ P.card - 1) * ‖w q‖ :=
    fun q => by rw [hedef, hwdef]
  simp_rw [hfold]
  rw [← hCdef]
  have hC0 : 0 ≤ C := by rw [hCdef]; exact Finset.prod_nonneg fun _ _ => by positivity
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have he0 : ∀ q, 0 ≤ e q := fun q => by rw [hedef]; positivity
  have he1 : ∀ q, e q ≤ 1 := fun q => by
    rw [hedef]
    apply Real.exp_le_one_iff.mpr
    have := hσ q
    nlinarith
  have hd0 : ∀ q, 0 ≤ (1 + e q) ^ P.card - 1 := fun q => by
    have := one_le_pow₀ (show 1 ≤ 1 + e q by linarith [he0 q]) (n := P.card); linarith
  -- the per-prime ratios
  have hpX : ∀ q : XiZeroCopy, ∀ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤ e q := by
    intro q p hp
    rw [hedef]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log X ≤ Real.log (p : ℕ) :=
      Real.log_le_log hX0 (by exact_mod_cast (hP p hp).le)
    have := hσ q
    nlinarith
  obtain ⟨u, hudef⟩ : ∃ u : XiZeroCopy → Nat.Primes → ℂ, u = fun q p =>
      (z p * jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p +
        conj (z p) * jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) / ((1 + ‖z p‖ ^ 2 : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hu : ∀ q, ∀ p ∈ P, ‖u q p‖ ≤ e q := fun q p hp => by
    rw [hudef]
    exact norm_jasBernoulliRatio_le ((norm_jasHoloA_dressed_le_abs σ q p).trans (hpX q p hp))
      ((norm_jasHoloB_dressed_le_abs σ q p).trans (hpX q p hp))
  have hprod : ∀ q : XiZeroCopy, ∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) +
      (σ - 1 / 2 : ℝ)) p) (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p) =
      (C : ℂ) * ∏ p ∈ P, (1 + u q p) := by
    intro q
    rw [hCdef, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [jasBernoulliFactor_eq_mul, hudef]
  -- termwise lower bound
  have hterm : ∀ q : XiZeroCopy, C * ((w q).re - ((1 + e q) ^ P.card - 1) * ‖w q‖) ≤
      ((∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
    intro q
    have hE := norm_prod_one_add_sub_one_le P (u q) (hu q)
    obtain ⟨E, hEdef⟩ : ∃ E : ℂ, E = ∏ p ∈ P, (1 + u q p) - 1 := ⟨_, rfl⟩
    rw [← hEdef] at hE
    have e' : (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        (C : ℂ) * (w q + E * w q) := by
      rw [hprod q, hwdef]
      have : ∏ p ∈ P, (1 + u q p) = 1 + E := by rw [hEdef]; ring
      rw [this]
      ring
    rw [e', Complex.re_ofReal_mul, Complex.add_re]
    have h1 : -(((1 + e q) ^ P.card - 1) * ‖w q‖) ≤ (E * w q).re := by
      have := Complex.abs_re_le_norm (E * w q)
      rw [norm_mul] at this
      have h2 : ‖E‖ * ‖w q‖ ≤ ((1 + e q) ^ P.card - 1) * ‖w q‖ :=
        mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      linarith [neg_abs_le (E * w q).re]
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  -- summation
  have hsum := summable_jasBernoulliAggregate P (σ - 1 / 2) z
  have hw : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hw.norm
  have hwre : Summable fun q => (w q).re := Complex.reCLM.summable hw
  have hdw : Summable fun q => ((1 + e q) ^ P.card - 1) * ‖w q‖ := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hd0 q) (norm_nonneg _))
      (fun q => ?_) (hwn.mul_left ((1 + 1) ^ P.card - 1))
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := pow_le_pow_left₀ (by linarith [he0 q]) (show 1 + e q ≤ 1 + 1 by linarith [he1 q])
      P.card
    linarith
  have hlow : Summable fun q : XiZeroCopy => C * ((w q).re - ((1 + e q) ^ P.card - 1) * ‖w q‖) :=
    (hwre.sub hdw).mul_left C
  rw [Complex.re_tsum hsum]
  refine le_trans ?_ (hlow.tsum_le_tsum hterm (Complex.reCLM.summable hsum))
  rw [tsum_mul_left, hwre.tsum_sub hdw]
  have hR : ∑' q, (w q).re = poleSharpConstant := by
    rw [← Complex.re_tsum hw, hwdef]
    simp only
    rw [tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re]
  rw [hR]

/-- **Product tests are close to their diagonal on few primes.**  Under `|Re ρ − ½| ≤ α ≤ σ`, with
`ε = X^{−(σ−α)}`, the product test value on `P` (primes `> X`) is at least
`∏(1 + |z_p|²) · (Φ(0) − ((1+ε)^{|P|} − 1) Σ_ρ |w_ρ|)`. -/
theorem jasProductAggregate_re_ge_of_halfPlane {alpha σ : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (hσ : alpha ≤ σ) {X : ℕ} (hX : 1 ≤ X) (P : Finset Nat.Primes) (hP : ∀ p ∈ P, X < (p : ℕ))
    (z : Nat.Primes → ℂ) :
    (∏ p ∈ P, (1 + ‖z p‖ ^ 2)) * (poleSharpConstant -
      ((1 + Real.exp (-(σ - alpha) * Real.log X)) ^ P.card - 1) * lagWeightTotal) ≤
    (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hab : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ alpha :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  refine le_trans ?_ (jasProductAggregate_re_ge (fun q => (hab q).trans hσ) hX P hP z)
  have hC0 : 0 ≤ ∏ p ∈ P, (1 + ‖z p‖ ^ 2) := Finset.prod_nonneg fun _ _ => by positivity
  refine mul_le_mul_of_nonneg_left ?_ hC0
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hmono : ∀ q : XiZeroCopy,
      ((1 + Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X)) ^ P.card - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      ((1 + Real.exp (-(σ - alpha) * Real.log X)) ^ P.card - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro q
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X) ≤
        Real.exp (-(σ - alpha) * Real.log X) := by
      apply Real.exp_le_exp.mpr; have := hab q; nlinarith
    have := pow_le_pow_left₀ (by positivity) (add_le_add_right h1 1) P.card
    linarith
  have hS : Summable fun q : XiZeroCopy =>
      ((1 + Real.exp (-(σ - alpha) * Real.log X)) ^ P.card - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := summable_inv_mul_one_sub.norm.mul_left _
  have hS' : Summable fun q : XiZeroCopy =>
      ((1 + Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X)) ^ P.card - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg ?_ (norm_nonneg _)) hmono hS
    have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
      Real.log X) by linarith [Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log X)])
      (n := P.card)
    linarith
  have := hS'.tsum_le_tsum hmono hS
  rw [tsum_mul_left] at this
  have hW : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = lagWeightTotal := rfl
  rw [hW] at this
  linarith

/-- `Φ(0) ≤ Σ_ρ |w_ρ|`. -/
theorem poleSharpConstant_le_lagWeightTotal : poleSharpConstant ≤ lagWeightTotal := by
  have hw : Summable fun q : XiZeroCopy => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    summable_inv_mul_one_sub
  have h : poleSharpConstant = ∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
    rw [← Complex.re_tsum hw, tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re]
  rw [h, lagWeightTotal]
  exact (Complex.reCLM.summable hw).tsum_le_tsum (fun q => Complex.re_le_norm _) hw.norm

theorem lagWeightTotal_pos : 0 < lagWeightTotal :=
  poleSharpConstant_pos.trans_le poleSharpConstant_le_lagWeightTotal

/-- **Few-primes producer at every level.**  Under `|Re ρ − ½| ≤ α ≤ σ`, positivity holds on every
set of at most `k` primes `> X` whenever `((1 + X^{−(σ−α)})^k − 1) Σ|w_ρ| ≤ Φ(0)`. -/
theorem jasProductPositiveAboveCard_of_halfPlane {alpha σ : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (hσ : alpha ≤ σ) {X : ℕ} (hX : 1 ≤ X) {k : ℕ}
    (hk : ((1 + Real.exp (-(σ - alpha) * Real.log X)) ^ k - 1) * lagWeightTotal ≤
      poleSharpConstant) :
    JasProductPositiveAboveCard X σ k := by
  intro P hPk hP z
  refine le_trans ?_ (jasProductAggregate_re_ge_of_halfPlane hXi hσ hX P hP z)
  have hC0 : 0 ≤ ∏ p ∈ P, (1 + ‖z p‖ ^ 2) := Finset.prod_nonneg fun _ _ => by positivity
  refine mul_nonneg hC0 ?_
  have h1 : (1 + Real.exp (-(σ - alpha) * Real.log X)) ^ P.card ≤
      (1 + Real.exp (-(σ - alpha) * Real.log X)) ^ k :=
    pow_le_pow_right₀ (by linarith [Real.exp_pos (-(σ - alpha) * Real.log X)]) hPk
  have := mul_le_mul_of_nonneg_right (sub_le_sub_right h1 1) lagWeightTotal_nonneg
  linarith

/-- **Few-primes producer, counting form.**  Under `|Re ρ − ½| ≤ α ≤ σ`, positivity holds on every
set of at most `c X^{σ−α}` primes `> X`, where `c = log(1 + Φ(0)/Σ|w_ρ|)`. -/
theorem jasProductPositiveAboveCard_of_halfPlane_of_le {alpha σ : ℝ}
    (hXi : XiZeroHalfPlaneBound alpha) (hσ : alpha ≤ σ) {X : ℕ} (hX : 1 ≤ X) {k : ℕ}
    (hk : (k : ℝ) ≤ Real.log (1 + poleSharpConstant / lagWeightTotal) *
      Real.exp ((σ - alpha) * Real.log X)) :
    JasProductPositiveAboveCard X σ k := by
  refine jasProductPositiveAboveCard_of_halfPlane hXi hσ hX ?_
  have hW := lagWeightTotal_pos
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.exp (-(σ - alpha) * Real.log X) := ⟨_, rfl⟩
  rw [← hεdef]
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hEE : Real.exp ((σ - alpha) * Real.log X) * ε = 1 := by
    rw [hεdef, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hkε : (k : ℝ) * ε ≤ Real.log (1 + poleSharpConstant / lagWeightTotal) := by
    have := mul_le_mul_of_nonneg_right hk hε0
    rwa [mul_assoc, hEE, mul_one] at this
  have h1 : (1 + ε) ^ k ≤ Real.exp ((k : ℝ) * ε) := by
    rw [mul_comm, Real.exp_mul]
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ε]) k
  have h2 : Real.exp ((k : ℝ) * ε) ≤ 1 + poleSharpConstant / lagWeightTotal := by
    have hpos : 0 < 1 + poleSharpConstant / lagWeightTotal := by
      have := div_pos poleSharpConstant_pos hW; linarith
    calc Real.exp ((k : ℝ) * ε) ≤ Real.exp (Real.log (1 + poleSharpConstant / lagWeightTotal)) :=
          Real.exp_le_exp.mpr hkε
      _ = 1 + poleSharpConstant / lagWeightTotal := Real.exp_log hpos
  have h3 : ((1 + ε) ^ k - 1) * lagWeightTotal ≤ (poleSharpConstant / lagWeightTotal) *
      lagWeightTotal := mul_le_mul_of_nonneg_right (by linarith) hW.le
  rwa [div_mul_cancel₀ _ hW.ne'] at h3

/-- **Unconditional few-primes producer at every level `σ ≥ ½`**: positivity on every set of at
most `c X^{σ−½}` primes `> X`. -/
theorem jasProductPositiveAboveCard_half {σ : ℝ} (hσ : 1 / 2 ≤ σ) {X : ℕ} (hX : 1 ≤ X) {k : ℕ}
    (hk : (k : ℝ) ≤ Real.log (1 + poleSharpConstant / lagWeightTotal) *
      Real.exp ((σ - 1 / 2) * Real.log X)) :
    JasProductPositiveAboveCard X σ k := by
  have hXi : XiZeroHalfPlaneBound (1 / 2) := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := xiZeroCopy_re_lt_one q
    linarith
  exact jasProductPositiveAboveCard_of_halfPlane_of_le hXi hσ hX hk

/-- Under a half-plane `α < σ`, positivity on all `k`-sets holds above some `X`, for every `k`. -/
theorem exists_jasProductPositiveAboveCard_of_halfPlane {alpha σ : ℝ}
    (hXi : XiZeroHalfPlaneBound alpha) (hσ : alpha < σ) (k : ℕ) :
    ∃ X : ℕ, JasProductPositiveAboveCard X σ k := by
  have hW := lagWeightTotal_pos
  have hc : 0 < Real.log (1 + poleSharpConstant / lagWeightTotal) :=
    Real.log_pos (by have := div_pos poleSharpConstant_pos hW; linarith)
  have ht : Filter.Tendsto (fun X : ℕ => Real.log (1 + poleSharpConstant / lagWeightTotal) *
      Real.exp ((σ - alpha) * Real.log X)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun X : ℕ => Real.log X) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_exp_atTop.comp (h1.const_mul_atTop (by linarith))).const_mul_atTop hc
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    ((ht.eventually_ge_atTop (k : ℝ)).and (Filter.eventually_ge_atTop 1))
  exact ⟨X, jasProductPositiveAboveCard_of_halfPlane_of_le hXi hσ.le (hX X le_rfl).2
    (hX X le_rfl).1⟩

/-- Positivity on all sets of at most `k ≥ 1` primes includes the single-prime tests. -/
theorem JasProductPositiveAboveCard.singlePrime {X : ℕ} {σ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : JasProductPositiveAboveCard X σ k) : JasSinglePrimePositiveAbove X σ := by
  intro p hp z
  have := h {p} (by rw [Finset.card_singleton]; exact hk)
    (fun p' hp' => by rw [Finset.mem_singleton.mp hp']; exact hp) (fun _ => z)
  simpa only [Finset.prod_singleton] using this

/-- **Complexity–abscissa law.**  Fix `k ≥ 1` and a level `0 ≤ σ < ½`.  Positivity on all sets of
at most `k` large primes forces the half-plane `Re ρ ≤ ½ + σ`, and any half-plane `α < σ` gives it
above some `X`.  So bounded-complexity product tests have abscissa `sup Re ρ − ½`, the single-prime
abscissa. -/
theorem exists_jasProductPositiveAboveCard_iff {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) {k : ℕ}
    (hk : 1 ≤ k) :
    ((∃ X : ℕ, JasProductPositiveAboveCard X σ k) → XiZeroHalfPlaneBound σ) ∧
      (∀ alpha : ℝ, alpha < σ → XiZeroHalfPlaneBound alpha →
        ∃ X : ℕ, JasProductPositiveAboveCard X σ k) :=
  ⟨fun ⟨_, hX⟩ => xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove_sharp hσ0 hσ
      (hX.singlePrime hk),
    fun _ h1 hXi => exists_jasProductPositiveAboveCard_of_halfPlane hXi h1 k⟩

/-- **RH from bounded complexity.**  For each `k ≥ 1`: RH holds iff for some `X` the product tests
at level `0` hold on all sets of at most `k` primes `> X`. -/
theorem riemannHypothesis_iff_exists_jasProductPositiveAboveCard_zero {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ X : ℕ, JasProductPositiveAboveCard X 0 k := by
  constructor
  · intro hRH
    exact ⟨0, (JasDressedPSDAbove.productPositive fun S _ =>
      (jasDressedPSD_zero_of_riemannHypothesis hRH).on S).card k⟩
  · rintro ⟨X, hX⟩
    exact riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero.mpr ⟨X, hX.singlePrime hk⟩

/-! ## The prime-budget producer -/

/-- `‖∏(1 + u_i) − 1‖ ≤ exp(Σ‖u_i‖) − 1`. -/
theorem norm_prod_one_add_sub_one_le_exp {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∏ i ∈ s, (1 + u i) - 1‖ ≤ Real.exp (∑ i ∈ s, ‖u i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add]
    have e : (1 + u a) * ∏ i ∈ s, (1 + u i) - 1 =
        (1 + u a) * (∏ i ∈ s, (1 + u i) - 1) + u a := by ring
    have h3 : ‖1 + u a‖ ≤ Real.exp ‖u a‖ :=
      (norm_add_le _ _).trans (by rw [norm_one]; linarith [Real.add_one_le_exp ‖u a‖])
    rw [e]
    calc ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - 1) + u a‖
        ≤ ‖1 + u a‖ * ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ Real.exp ‖u a‖ * (Real.exp (∑ i ∈ s, ‖u i‖) - 1) + (Real.exp ‖u a‖ - 1) :=
          add_le_add (mul_le_mul h3 ih (norm_nonneg _) (Real.exp_pos _).le)
            (by linarith [Real.add_one_le_exp ‖u a‖])
      _ = Real.exp ‖u a‖ * Real.exp (∑ i ∈ s, ‖u i‖) - 1 := by ring

/-- **Unconditional zero-sum control.**  With `ε_{ρ,p} = p^{−(σ−|Re ρ−½|)}`, the product test value
on any finite set `P` of primes is at least `∏(1 + |z_p|²) · (Φ(0) − Σ_ρ |w_ρ| (exp(Σ_{p∈P} ε_{ρ,p}) − 1))`. -/
theorem jasProductAggregate_re_ge_exp {σ : ℝ} (P : Finset Nat.Primes) (z : Nat.Primes → ℂ) :
    (∏ p ∈ P, (1 + ‖z p‖ ^ 2)) * (poleSharpConstant - ∑' q : XiZeroCopy,
      (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤
    (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨e, hedef⟩ : ∃ e : XiZeroCopy → ℝ, e = fun q =>
      Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∏ p ∈ P, (1 + ‖z p‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hfold : ∀ q : XiZeroCopy, (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
      Real.log p)) - 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = e q * ‖w q‖ :=
    fun q => by rw [hedef, hwdef]
  simp_rw [hfold]
  rw [← hCdef]
  have hC0 : 0 ≤ C := by rw [hCdef]; exact Finset.prod_nonneg fun _ _ => by positivity
  have he0 : ∀ q, 0 ≤ e q := fun q => by
    rw [hedef]
    linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
      (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)).le)]
  -- a uniform bound for summability: `|Re ρ − ½| ≤ ½`
  have heB : ∀ q, e q ≤ Real.exp (∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p)) - 1 := by
    intro q
    rw [hedef]
    have hab : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have : ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
        ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p) :=
      Finset.sum_le_sum fun p _ => Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])
    linarith [Real.exp_le_exp.mpr this]
  obtain ⟨u, hudef⟩ : ∃ u : XiZeroCopy → Nat.Primes → ℂ, u = fun q p =>
      (z p * jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p +
        conj (z p) * jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) / ((1 + ‖z p‖ ^ 2 : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hu : ∀ q, ∀ p, ‖u q p‖ ≤ Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) :=
    fun q p => by
      rw [hudef]
      exact norm_jasBernoulliRatio_le (norm_jasHoloA_dressed_le_abs σ q p)
        (norm_jasHoloB_dressed_le_abs σ q p)
  have hprod : ∀ q : XiZeroCopy, ∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) +
      (σ - 1 / 2 : ℝ)) p) (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p) =
      (C : ℂ) * ∏ p ∈ P, (1 + u q p) := by
    intro q
    rw [hCdef, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [jasBernoulliFactor_eq_mul, hudef]
  have hterm : ∀ q : XiZeroCopy, C * ((w q).re - e q * ‖w q‖) ≤
      ((∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
    intro q
    have hE : ‖∏ p ∈ P, (1 + u q p) - 1‖ ≤ e q := by
      refine (norm_prod_one_add_sub_one_le_exp P (u q)).trans ?_
      rw [hedef]
      linarith [Real.exp_le_exp.mpr (Finset.sum_le_sum fun p (_ : p ∈ P) => hu q p)]
    obtain ⟨E, hEdef⟩ : ∃ E : ℂ, E = ∏ p ∈ P, (1 + u q p) - 1 := ⟨_, rfl⟩
    rw [← hEdef] at hE
    have e' : (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        (C : ℂ) * (w q + E * w q) := by
      rw [hprod q, hwdef]
      have : ∏ p ∈ P, (1 + u q p) = 1 + E := by rw [hEdef]; ring
      rw [this]
      ring
    rw [e', Complex.re_ofReal_mul, Complex.add_re]
    have h1 : -(e q * ‖w q‖) ≤ (E * w q).re := by
      have := Complex.abs_re_le_norm (E * w q)
      rw [norm_mul] at this
      have h2 : ‖E‖ * ‖w q‖ ≤ e q * ‖w q‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      linarith [neg_abs_le (E * w q).re]
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  have hsum := summable_jasBernoulliAggregate P (σ - 1 / 2) z
  have hw : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hw.norm
  have hwre : Summable fun q => (w q).re := Complex.reCLM.summable hw
  have hdw : Summable fun q => e q * ‖w q‖ :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (he0 q) (norm_nonneg _))
      (fun q => mul_le_mul_of_nonneg_right (heB q) (norm_nonneg _)) (hwn.mul_left _)
  have hlow : Summable fun q : XiZeroCopy => C * ((w q).re - e q * ‖w q‖) :=
    (hwre.sub hdw).mul_left C
  rw [Complex.re_tsum hsum]
  refine le_trans ?_ (hlow.tsum_le_tsum hterm (Complex.reCLM.summable hsum))
  rw [tsum_mul_left, hwre.tsum_sub hdw]
  have hR : ∑' q, (w q).re = poleSharpConstant := by
    rw [← Complex.re_tsum hw, hwdef]
    simp only
    rw [tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re]
  rw [hR]

/-- **Prime-budget producer.**  For every level `σ` and every budget `K`, once `X` is large,
product positivity holds on every finite set `P` of primes `> X` with `Σ_{p∈P} p^{−(σ−½)} ≤ K`.
Each zero sees `Σ_P p^{−(σ−|Re ρ−½|)} ≤ K X^{−(½−|Re ρ−½|)} → 0`; dominated convergence over the zeros
with bound `|w_ρ|(e^K − 1)`.  For `σ ≥ ½` this contains every set of at most `K X^{σ−½}` primes; for
`σ > 3/2` it contains every set, since `Σ_{p > X} p^{−(σ−½)} → 0`. -/
theorem eventually_jasProductPositive_of_primeBudget (σ K : ℝ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p) ≤ K → ∀ z : Nat.Primes → ℂ,
        0 ≤ (∑' q : XiZeroCopy,
          (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
            (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
            ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨K', hK'0, hKK'⟩ : ∃ K' : ℝ, 0 ≤ K' ∧ K ≤ K' := ⟨max K 0, le_max_right _ _, le_max_left _ _⟩
  have hab : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := fun q => by
    rw [abs_lt]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → XiZeroCopy → ℝ, f = fun (X : ℕ) (q : XiZeroCopy) =>
      ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
        (Real.exp (K' * Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X)) - 1) :=
    ⟨_, rfl⟩
  have hf0 : ∀ X q, 0 ≤ f X q := fun X q => by
    rw [hfdef]
    exact mul_nonneg (norm_nonneg _) (by linarith [Real.one_le_exp (mul_nonneg hK'0
      (Real.exp_pos ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X)).le)])
  have hlim : ∀ q : XiZeroCopy, Filter.Tendsto (fun X : ℕ => f X q) Filter.atTop (nhds 0) := by
    intro q
    have h1 : Filter.Tendsto (fun X : ℕ => Real.log X) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun X : ℕ => Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) *
        Real.log X)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg (by linarith [hab q]))
    have h2' : Filter.Tendsto (fun X : ℕ => K' * Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) *
        Real.log X)) Filter.atTop (nhds 0) := by simpa using h2.const_mul K'
    have h3 := ((Real.continuous_exp.tendsto 0).comp h2').sub_const 1
    have h4 := h3.const_mul ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
    rw [hfdef]
    simpa [Function.comp] using h4
  have hbd : ∀ X : ℕ, 1 ≤ X → ∀ q : XiZeroCopy,
      f X q ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * (Real.exp K' - 1) := by
    intro X hX q
    rw [hfdef]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
    have h1 : Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [hab q]) hlogX)
    have h2 : K' * Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X) ≤ K' := by nlinarith
    linarith [Real.exp_le_exp.mpr h2]
  have hbound : ∀ᶠ X : ℕ in Filter.atTop, ∀ q : XiZeroCopy,
      ‖f X q‖ ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * (Real.exp K' - 1) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with X hX q
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 X q)]
    exact hbd X hX q
  have hT := tendsto_tsum_of_dominated_convergence (summable_inv_mul_one_sub.norm.mul_right _)
    hlim hbound
  rw [tsum_zero] at hT
  filter_upwards [hT.eventually (gt_mem_nhds poleSharpConstant_pos), Filter.eventually_ge_atTop 1]
    with X hXf hX P hP hB z
  refine le_trans ?_ (jasProductAggregate_re_ge_exp (σ := σ) P z)
  refine mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) ?_
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hterm : ∀ q : XiZeroCopy,
      (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ f X q := by
    intro q
    rw [hfdef, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hη : 0 ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by linarith [hab q]
    have hp : ∀ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
        Real.exp (-(σ - 1 / 2) * Real.log p) *
          Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X) := by
      intro p hpP
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log X ≤ Real.log (p : ℕ) :=
        Real.log_le_log hX0 (by exact_mod_cast (hP p hpP).le)
      nlinarith
    have hsum : ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
        K' * Real.exp ((|(q.1 : ℂ).re - 1 / 2| - 1 / 2) * Real.log X) := by
      refine (Finset.sum_le_sum hp).trans ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hB.trans hKK') (Real.exp_pos _).le
    linarith [Real.exp_le_exp.mpr hsum]
  have hS : Summable (f X) := Summable.of_nonneg_of_le (hf0 X) (hbd X hX)
    (summable_inv_mul_one_sub.norm.mul_right _)
  have hS' : Summable fun q : XiZeroCopy =>
      (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg ?_ (norm_nonneg _)) hterm hS
    linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
      (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)).le)]
  linarith [hS'.tsum_le_tsum hterm hS]

/-- **The unconditional few-primes producer is superlinear in `X^{σ−½}`.**  For every `σ ≥ ½` and
every `K`, once `X` is large, positivity holds on every set of at most `K X^{σ−½}` primes `> X`.
Such a set has prime budget `Σ_{p∈P} p^{−(σ−½)} ≤ K`. -/
theorem eventually_jasProductPositiveAboveCard_of_le_mul_rpow {σ : ℝ} (hσ : 1 / 2 ≤ σ) (K : ℝ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ k : ℕ, (k : ℝ) ≤ K * Real.exp ((σ - 1 / 2) * Real.log X) →
      JasProductPositiveAboveCard X σ k := by
  filter_upwards [eventually_jasProductPositive_of_primeBudget σ K, Filter.eventually_ge_atTop 1]
    with X hXB hX k hk P hPk hP z
  refine hXB P hP ?_ z
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hp : ∀ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p) ≤ Real.exp (-(σ - 1 / 2) * Real.log X) :=
    fun p hpP => Real.exp_le_exp.mpr (by
      have := Real.log_le_log hX0 (by exact_mod_cast (hP p hpP).le : (X : ℝ) ≤ (p : ℕ))
      nlinarith)
  have hEE : Real.exp ((σ - 1 / 2) * Real.log X) * Real.exp (-(σ - 1 / 2) * Real.log X) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hcard : (P.card : ℝ) ≤ k := by exact_mod_cast hPk
  calc ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p)
      ≤ P.card * Real.exp (-(σ - 1 / 2) * Real.log X) := by
        simpa using Finset.sum_le_sum hp
    _ ≤ k * Real.exp (-(σ - 1 / 2) * Real.log X) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ K * Real.exp ((σ - 1 / 2) * Real.log X) * Real.exp (-(σ - 1 / 2) * Real.log X) :=
        mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
    _ = K := by rw [mul_assoc, hEE, mul_one]

end

end RHTower
