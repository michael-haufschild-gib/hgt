import GaloisForLFunctions.HTGeometry.PhysicalPullbackPeriodIncidenceComparison
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The critical completion of the physical arc comparison

The polynomial arc scale of the physical pullback embeds into the germs holomorphic on a
neighbourhood of the closed unit disc, which is the completion adapted to the period symbol: the
symbol has norm strictly below one, and the critical value one is the limit reached only along
periods of unbounded size.

On that completion the comparison with the powered period-incidence filtration is not merely
filtration preserving but exact.  For a nondiscrete period group the symbols accumulate at zero,
so a bound `‖f(w)‖ ≤ C‖w‖^n` along a vanishing sequence forces `f` to factor as `z^n g` with `g`
holomorphic; conversely such a factorization puts the evaluation vector in the range of the
order-`n` multiplier.  Hence contact order at the origin and membership in the powered incidence
scale determine one another, and the arc-contact Rees filtration is exactly the preimage of the
powered incidence filtration.

The completion also carries the genuine exponential clock `z ↦ exp(τ_j z) - 1`, not only its
linearization: each factor is `z` times a holomorphic unit with value `τ_j` at the origin, so a
coface product of `r` such factors has contact order exactly `r`, and its incidence image sits at
level `r` of the powered scale and no higher.
-/

open Filter
open scoped BigOperators Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

variable {L : Submodule ℤ ℂ}

/-! ## Vanishing sequences of period symbols -/

/-- For a nondiscrete period group the regularized symbols of nonzero periods accumulate at
zero. -/
theorem exists_nonzeroPeriod_weight_tendsto_zero (L : Submodule ℤ ℂ)
    (hL : ¬ DiscreteTopology L) :
    ∃ q : ℕ → NonzeroPeriod L,
      Tendsto (fun i => regularizedPeriodWeight (q i).1.1) atTop (𝓝 0) := by
  obtain ⟨p, hpL, hpne, hp0⟩ := exists_small_nonzero_of_not_discrete_intSubmodule L hL
  exact ⟨fun i => ⟨⟨p i, hpL i⟩, hpne i⟩, tendsto_regularizedPeriodWeight_zero hp0⟩

/-! ## Order detection along a vanishing sequence -/

/-- **Polynomial order detection.**  A polynomial whose values along a nonzero null sequence in the
closed unit disc are `O(|w|^n)` is divisible by `X^n`. -/
theorem X_pow_dvd_of_eval_bound {P : Polynomial ℂ} {C : ℝ} (hC : 0 ≤ C) {w : ℕ → ℂ}
    (hw0 : ∀ i, w i ≠ 0) (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwlim : Tendsto w atTop (𝓝 0)) :
    ∀ {n : ℕ}, (∀ i, ‖Polynomial.eval (w i) P‖ ≤ C * ‖w i‖ ^ n) →
      (Polynomial.X : Polynomial ℂ) ^ n ∣ P := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hb
      have hb' : ∀ i, ‖Polynomial.eval (w i) P‖ ≤ C * ‖w i‖ ^ n := fun i =>
        (hb i).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) (hw1 i) (Nat.le_succ n)) hC)
      obtain ⟨Q, hQ⟩ := ih hb'
      have hQb : ∀ i, ‖Polynomial.eval (w i) Q‖ ≤ C * ‖w i‖ := by
        intro i
        have hwn : (0 : ℝ) < ‖w i‖ ^ n := pow_pos (norm_pos_iff.mpr (hw0 i)) n
        have hev : ‖Polynomial.eval (w i) P‖ = ‖w i‖ ^ n * ‖Polynomial.eval (w i) Q‖ := by
          rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow]
        have hstep := hb i
        rw [hev] at hstep
        have heq : C * ‖w i‖ ^ (n + 1) = ‖w i‖ ^ n * (C * ‖w i‖) := by ring
        rw [heq] at hstep
        exact le_of_mul_le_mul_left hstep hwn
      have hlim : Tendsto (fun i => Polynomial.eval (w i) Q) atTop
          (𝓝 (Polynomial.eval 0 Q)) := ((Polynomial.continuous Q).tendsto 0).comp hwlim
      have hzero : Tendsto (fun i => Polynomial.eval (w i) Q) atTop (𝓝 0) := by
        refine squeeze_zero_norm hQb ?_
        simpa using (tendsto_const_nhds (x := C) (f := atTop (α := ℕ))).mul hwlim.norm
      have h0 : Polynomial.eval 0 Q = 0 := tendsto_nhds_unique hlim hzero
      obtain ⟨Q', hQ'⟩ :=
        (Polynomial.X_dvd_iff (f := Q)).mpr (by rw [Polynomial.coeff_zero_eq_eval_zero, h0])
      exact ⟨Q', by rw [hQ, hQ']; ring⟩

/-- **Holomorphic order detection.**  A function holomorphic on a disc about the origin whose
values along a nonzero null sequence are `O(|w|^n)` factors as `z^n` times a holomorphic
function. -/
theorem exists_differentiableOn_pow_factor_of_bound {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) {C : ℝ} (hC : 0 ≤ C) {w : ℕ → ℂ}
    (hw0 : ∀ i, w i ≠ 0) (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwR : ∀ i, w i ∈ Metric.ball (0 : ℂ) R)
    (hwlim : Tendsto w atTop (𝓝 0)) :
    ∀ {n : ℕ}, (∀ i, ‖f (w i)‖ ≤ C * ‖w i‖ ^ n) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) R, f z = z ^ n * g z := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_zero]; exact hR
  intro n
  induction n with
  | zero => intro _; exact ⟨f, hf, fun z _ => by rw [pow_zero, one_mul]⟩
  | succ n ih =>
      intro hb
      have hb' : ∀ i, ‖f (w i)‖ ≤ C * ‖w i‖ ^ n := fun i =>
        (hb i).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) (hw1 i) (Nat.le_succ n)) hC)
      obtain ⟨g, hg, hfg⟩ := ih hb'
      have hgb : ∀ i, ‖g (w i)‖ ≤ C * ‖w i‖ := by
        intro i
        have hwn : (0 : ℝ) < ‖w i‖ ^ n := pow_pos (norm_pos_iff.mpr (hw0 i)) n
        have hev : ‖f (w i)‖ = ‖w i‖ ^ n * ‖g (w i)‖ := by
          rw [hfg _ (hwR i), norm_mul, norm_pow]
        have hstep := hb i
        rw [hev] at hstep
        have heq : C * ‖w i‖ ^ (n + 1) = ‖w i‖ ^ n * (C * ‖w i‖) := by ring
        rw [heq] at hstep
        exact le_of_mul_le_mul_left hstep hwn
      have hgcont : ContinuousAt g 0 :=
        hg.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0mem)
      have hlim : Tendsto (fun i => g (w i)) atTop (𝓝 (g 0)) := hgcont.tendsto.comp hwlim
      have hzero : Tendsto (fun i => g (w i)) atTop (𝓝 0) := by
        refine squeeze_zero_norm hgb ?_
        simpa using (tendsto_const_nhds (x := C) (f := atTop (α := ℕ))).mul hwlim.norm
      have hg0 : g 0 = 0 := tendsto_nhds_unique hlim hzero
      refine ⟨dslope g 0, (Complex.differentiableOn_dslope
        (Metric.isOpen_ball.mem_nhds h0mem)).mpr hg, fun z hz => ?_⟩
      have hsplit : z * dslope g 0 z = g z := by
        have := sub_smul_dslope g 0 z
        rw [sub_zero, hg0, sub_zero, smul_eq_mul] at this
        exact this
      rw [hfg z hz, ← hsplit]
      ring

/-! ## Evaluation of the critical scale at the period symbol -/

/-- Evaluate a function bounded on the closed unit disc at the regularized period symbols. -/
def discEvalVector (L : Submodule ℤ ℂ) (f : ℂ → ℂ) {C : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ C) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q => f (regularizedPeriodWeight q.1.1),
    memℓp_infty ⟨C, by
      rintro _ ⟨q, rfl⟩
      exact hf _ (norm_regularizedPeriodWeight_le_one q.1.1)⟩⟩

@[simp] theorem discEvalVector_apply (L : Submodule ℤ ℂ) (f : ℂ → ℂ) {C : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ C) (q : NonzeroPeriod L) :
    discEvalVector L f hf q = f (regularizedPeriodWeight q.1.1) := rfl

/-- The polynomial arc scale sits inside the critical scale. -/
theorem discEvalVector_polynomial (L : Submodule ℤ ℂ) (P : Polynomial ℂ)
    (hP : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Polynomial.eval z P‖ ≤ ∑ i ∈ P.support, ‖P.coeff i‖) :
    discEvalVector L (fun z => Polynomial.eval z P) hP = arcEvalVector L P := rfl

/-- A germ holomorphic on a disc of radius larger than one is bounded on the closed unit disc. -/
theorem exists_bound_on_closedUnitBall {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ C := by
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    linarith
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  exact ⟨C, fun z hz => hC z (mem_closedBall_zero_iff.mpr hz)⟩

/-! ## Exactness of the comparison on the critical scale -/

/-- **The comparison is exact on the critical scale.**  For a nondiscrete period group the
evaluation of a germ holomorphic near the closed unit disc lies in the range of the order-`n`
powered period-incidence multiplier exactly when the germ has contact order at least `n` at the
origin. -/
theorem discEvalVector_mem_poweredRange_iff {R : ℝ} (hR : 1 < R)
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) {C : ℝ}
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ C) (n : ℕ) :
    discEvalVector L f hC ∈ Set.range (poweredPeriodIncidenceMultiplier L n) ↔
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) R, f z = z ^ n * g z := by
  have hRpos : (0 : ℝ) < R := lt_trans one_pos hR
  have hweightR : ∀ z : ℂ, regularizedPeriodWeight z ∈ Metric.ball (0 : ℂ) R := by
    intro z
    rw [mem_ball_zero_iff]
    exact lt_trans (norm_regularizedPeriodWeight_lt_one z) hR
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq⟩ := exists_nonzeroPeriod_weight_tendsto_zero L hL
    have hval : ∀ i, regularizedPeriodWeight (q i).1.1 ^ n * y (q i) =
        f (regularizedPeriodWeight (q i).1.1) := by
      intro i
      have := congrArg (fun v : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ => (v : _ → ℂ) (q i)) hy
      simpa [poweredPeriodIncidenceMultiplier_apply] using this
    refine exists_differentiableOn_pow_factor_of_bound hRpos hf (norm_nonneg y)
      (w := fun i => regularizedPeriodWeight (q i).1.1)
      (fun i => regularizedPeriodWeight_ne_zero (q i).2)
      (fun i => norm_regularizedPeriodWeight_le_one _)
      (fun i => hweightR _) hq (fun i => ?_)
    rw [← hval i, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by simp) y (q i))
      (by positivity)
  · rintro ⟨g, hg, hfg⟩
    obtain ⟨D, hD⟩ := exists_bound_on_closedUnitBall hR hg
    refine ⟨discEvalVector L g hD, ?_⟩
    ext q
    rw [poweredPeriodIncidenceMultiplier_apply, discEvalVector_apply, discEvalVector_apply]
    exact (hfg _ (hweightR _)).symm

/-- **The polynomial comparison is exact.**  A polynomial evaluates into the range of the order-`n`
powered period-incidence multiplier exactly when it is divisible by `λ^n`. -/
theorem arcEvalVector_mem_poweredRange_iff (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (n : ℕ) (P : Polynomial ℂ) :
    arcEvalVector L P ∈ Set.range (poweredPeriodIncidenceMultiplier L n) ↔
      (Polynomial.X : Polynomial ℂ) ^ n ∣ P := by
  refine ⟨fun hmem => ?_, arcEvalVector_mem_range_of_X_pow_dvd L n⟩
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨q, hq⟩ := exists_nonzeroPeriod_weight_tendsto_zero L hL
  have hval : ∀ i, regularizedPeriodWeight (q i).1.1 ^ n * y (q i) =
      Polynomial.eval (regularizedPeriodWeight (q i).1.1) P := by
    intro i
    have := congrArg (fun v : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ => (v : _ → ℂ) (q i)) hy
    simpa [poweredPeriodIncidenceMultiplier_apply] using this
  refine X_pow_dvd_of_eval_bound (norm_nonneg y)
    (w := fun i => regularizedPeriodWeight (q i).1.1)
    (fun i => regularizedPeriodWeight_ne_zero (q i).2)
    (fun i => norm_regularizedPeriodWeight_le_one _) hq (fun i => ?_)
  rw [← hval i, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by simp) y (q i)) (by positivity)

/-- **The arc-contact Rees filtration is exactly the preimage of the powered incidence
filtration.** -/
theorem mem_arcContactFiltration_iff_arcEval_mem_poweredRange {ι : Type*} [DecidableEq ι]
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) (τ : ι → ℂ) (k : ℕ)
    (P : MvPolynomial ι ℂ) :
    P ∈ arcContactFiltration τ k ↔
      arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
        Set.range (poweredPeriodIncidenceMultiplier L k) :=
  (mem_arcContactFiltration_iff τ k P).trans
    (arcEvalVector_mem_poweredRange_iff L hL k _).symm

/-- The squarefree annihilator is detected at level exactly `r`: its whole arc image lies in the
order-`r` scale, and a coface generator already leaves the order-`r+1` scale. -/
theorem veroneseIdeal_arcEval_poweredRange_exact {ι : Type*} [DecidableEq ι]
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0)
    {r : ℕ} {S : Finset ι} (hS : S.card = r) :
    (∀ P ∈ VeroneseIdeal.veroneseIdeal ℂ ι r,
        arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
          Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      arcEvalVector L (VeroneseIdeal.physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∉
        Set.range (poweredPeriodIncidenceMultiplier L (r + 1)) := by
  refine ⟨fun P hP => veroneseIdeal_arcEval_mem_poweredRange L τ hP, fun hmem => ?_⟩
  exact (VeroneseIdeal.physicalArcPullback_generator_ne_zero τ hτ hS).2
    ((arcEvalVector_mem_poweredRange_iff L hL (r + 1) _).mp hmem)

/-! ## The genuine exponential clock on the critical scale -/

/-- The holomorphic unit factor of `exp(t z) - 1`. -/
def expArcUnit (t : ℂ) : ℂ → ℂ := dslope (fun z => Complex.exp (t * z) - 1) 0

theorem differentiable_expArcSubOne (t : ℂ) :
    Differentiable ℂ fun z => Complex.exp (t * z) - 1 :=
  (Complex.differentiable_exp.comp (differentiable_id.const_mul t)).sub_const 1

theorem differentiable_expArcUnit (t : ℂ) : Differentiable ℂ (expArcUnit t) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).mpr
    (differentiable_expArcSubOne t).differentiableOn

/-- **The exponential clock factors.**  `exp(t z) - 1 = z U_t(z)` with `U_t` entire. -/
theorem mul_expArcUnit (t z : ℂ) : z * expArcUnit t z = Complex.exp (t * z) - 1 := by
  have h := sub_smul_dslope (fun z => Complex.exp (t * z) - 1) 0 z
  rw [sub_zero, smul_eq_mul] at h
  simpa [expArcUnit] using h

/-- **The unit value at the origin is the period.** -/
theorem expArcUnit_zero (t : ℂ) : expArcUnit t 0 = t := by
  have hderiv : HasDerivAt (fun z : ℂ => Complex.exp (t * z) - 1) t 0 := by
    have h1 : HasDerivAt (fun z : ℂ => t * z) t 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul t
    simpa using h1.cexp.sub_const 1
  rw [expArcUnit, dslope_same, hderiv.deriv]

/-- The genuine exponential coface product of a face `S`. -/
def exponentialCofaceProduct {ι : Type*} (τ : ι → ℂ) (S : Finset ι) : ℂ → ℂ :=
  fun z => ∏ j ∈ S, (Complex.exp (τ j * z) - 1)

/-- **Contact factorization of the exponential coface product.**  It is `z^{|S|}` times the
product of the holomorphic units. -/
theorem exponentialCofaceProduct_eq {ι : Type*} (τ : ι → ℂ) (S : Finset ι) (z : ℂ) :
    exponentialCofaceProduct τ S z = z ^ S.card * ∏ j ∈ S, expArcUnit (τ j) z := by
  calc exponentialCofaceProduct τ S z
      = ∏ j ∈ S, (z * expArcUnit (τ j) z) :=
        Finset.prod_congr rfl fun j _ => (mul_expArcUnit (τ j) z).symm
    _ = (∏ _j ∈ S, z) * ∏ j ∈ S, expArcUnit (τ j) z := Finset.prod_mul_distrib
    _ = z ^ S.card * ∏ j ∈ S, expArcUnit (τ j) z := by rw [Finset.prod_const]

theorem differentiable_exponentialCofaceProduct {ι : Type*} (τ : ι → ℂ) (S : Finset ι) :
    Differentiable ℂ (exponentialCofaceProduct τ S) :=
  Differentiable.fun_finsetProd fun j _ => differentiable_expArcSubOne (τ j)

theorem differentiable_expArcUnitProduct {ι : Type*} (τ : ι → ℂ) (S : Finset ι) :
    Differentiable ℂ fun z => ∏ j ∈ S, expArcUnit (τ j) z :=
  Differentiable.fun_finsetProd fun j _ => differentiable_expArcUnit (τ j)

theorem expArcUnitProduct_zero_ne_zero {ι : Type*} {τ : ι → ℂ} (hτ : ∀ j, τ j ≠ 0)
    (S : Finset ι) : (∏ j ∈ S, expArcUnit (τ j) 0) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [expArcUnit_zero]
  exact hτ j

/-- **A unit factorization blocks the next contact level.**  If `F = z^r G` near the origin with
`G` continuous and nonvanishing there, then `F` admits no factorization `z^{r+1} h` with `h`
continuous at the origin, provided the origin is approached by nonzero points of the disc. -/
theorem not_exists_pow_succ_factor_of_unit {R : ℝ} {F G : ℂ → ℂ} {r : ℕ}
    (hG : ContinuousAt G 0) (hG0 : G 0 ≠ 0)
    (hFG : ∀ z ∈ Metric.ball (0 : ℂ) R, F z = z ^ r * G z)
    {w : ℕ → ℂ} (hw0 : ∀ i, w i ≠ 0) (hwR : ∀ i, w i ∈ Metric.ball (0 : ℂ) R)
    (hwlim : Tendsto w atTop (𝓝 0)) :
    ¬ ∃ h : ℂ → ℂ, ContinuousAt h 0 ∧
        ∀ z ∈ Metric.ball (0 : ℂ) R, F z = z ^ (r + 1) * h z := by
  rintro ⟨h, hh, hFh⟩
  have hcancel : ∀ i, G (w i) = w i * h (w i) := by
    intro i
    have hpow : (w i) ^ r ≠ 0 := pow_ne_zero _ (hw0 i)
    have := (hFG _ (hwR i)).symm.trans (hFh _ (hwR i))
    rw [pow_succ, mul_assoc] at this
    exact mul_left_cancel₀ hpow this
  have hlimG : Tendsto (fun i => G (w i)) atTop (𝓝 (G 0)) := hG.tendsto.comp hwlim
  have hlimR : Tendsto (fun i => w i * h (w i)) atTop (𝓝 (0 * h 0)) :=
    hwlim.mul (hh.tendsto.comp hwlim)
  rw [zero_mul] at hlimR
  have : G 0 = 0 := by
    refine tendsto_nhds_unique hlimG ?_
    simpa only [hcancel] using hlimR
  exact hG0 this

/-- **The genuine exponential clock has contact order exactly `|S|`.**  With no vanishing period
the coface product of the true exponential factors sits at level `|S|` of the powered incidence
scale and no higher. -/
theorem exponentialCofaceProduct_poweredRange_exact {ι : Type*} {R : ℝ} (hR : 1 < R)
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) {τ : ι → ℂ} (hτ : ∀ j, τ j ≠ 0)
    (S : Finset ι) {C : ℝ}
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖exponentialCofaceProduct τ S z‖ ≤ C) :
    discEvalVector L (exponentialCofaceProduct τ S) hC ∈
        Set.range (poweredPeriodIncidenceMultiplier L S.card) ∧
      discEvalVector L (exponentialCofaceProduct τ S) hC ∉
        Set.range (poweredPeriodIncidenceMultiplier L (S.card + 1)) := by
  have hFdiff : DifferentiableOn ℂ (exponentialCofaceProduct τ S) (Metric.ball (0 : ℂ) R) :=
    (differentiable_exponentialCofaceProduct τ S).differentiableOn
  have hGdiff : DifferentiableOn ℂ (fun z => ∏ j ∈ S, expArcUnit (τ j) z)
      (Metric.ball (0 : ℂ) R) := (differentiable_expArcUnitProduct τ S).differentiableOn
  constructor
  · refine (discEvalVector_mem_poweredRange_iff hR L hL hFdiff hC S.card).mpr ?_
    exact ⟨_, hGdiff, fun z _ => exponentialCofaceProduct_eq τ S z⟩
  · intro hmem
    obtain ⟨g, hg, hfg⟩ :=
      (discEvalVector_mem_poweredRange_iff hR L hL hFdiff hC (S.card + 1)).mp hmem
    obtain ⟨q, hq⟩ := exists_nonzeroPeriod_weight_tendsto_zero L hL
    have hweightR : ∀ z : ℂ, regularizedPeriodWeight z ∈ Metric.ball (0 : ℂ) R := by
      intro z
      rw [mem_ball_zero_iff]
      exact lt_trans (norm_regularizedPeriodWeight_lt_one z) hR
    have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, norm_zero]; exact lt_trans one_pos hR
    refine not_exists_pow_succ_factor_of_unit
      (F := exponentialCofaceProduct τ S) (G := fun z => ∏ j ∈ S, expArcUnit (τ j) z)
      ((differentiable_expArcUnitProduct τ S).continuous.continuousAt)
      (expArcUnitProduct_zero_ne_zero hτ S)
      (fun z _ => exponentialCofaceProduct_eq τ S z)
      (w := fun i => regularizedPeriodWeight (q i).1.1)
      (fun i => regularizedPeriodWeight_ne_zero (q i).2)
      (fun i => hweightR _) hq ?_
    exact ⟨g, hg.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0mem), hfg⟩

/-! ## The critical comparison at order `r` -/

/-- **Source-natural exact comparison at order `r`.**  For a nondiscrete period source the
squarefree degree-`r` annihilator maps exactly onto level `r` of the powered period-incidence
filtration: its whole arc image lies in the order-`r` range, a coface generator is not in the
order-`r+1` range, the exact target of the level is the symbol `w^r` itself, and the source class
produces the half-density `|w|^{r/2}` as a closure-only section. -/
theorem veroneseIdeal_criticalComparison {ι : Type*} [DecidableEq ι]
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) {S : Finset ι} (hS : S.card = r) :
    (∀ P ∈ VeroneseIdeal.veroneseIdeal ℂ ι r,
        arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
          Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      arcEvalVector L (VeroneseIdeal.physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∉
        Set.range (poweredPeriodIncidenceMultiplier L (r + 1)) ∧
      poweredPeriodIncidenceExactTarget L r ∈
        Set.range (poweredPeriodIncidenceMultiplier L r) ∧
      (poweredPeriodIncidenceHalfDensity L r ∈
          closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        poweredPeriodIncidenceHalfDensity L r ∉
          Set.range (poweredPeriodIncidenceMultiplier L r)) :=
  ⟨(veroneseIdeal_arcEval_poweredRange_exact L hL τ hτ hS).1,
    (veroneseIdeal_arcEval_poweredRange_exact L hL τ hτ hS).2,
    poweredPeriodIncidenceExactTarget_mem_range L r,
    poweredPeriodIncidenceHalfDensity_closureOnly L hL r hr⟩

end

end GaloisForLFunctions
