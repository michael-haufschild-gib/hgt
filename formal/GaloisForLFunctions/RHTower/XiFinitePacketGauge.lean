import GaloisForLFunctions.RHTower.XiRationalQuartetGauge
import GaloisForLFunctions.RHTower.SpeiserCriticalPacketGauge

/-!
# Arbitrary finite off-critical packet implantation by a rational gauge

For a finite list of parameters `aⱼ ≠ 0`, `bⱼ > 0`, the centered real-even polynomial

```text
A(s) = ∏ⱼ (((s - 1/2) - aⱼ)² + bⱼ²) (((s - 1/2) + aⱼ)² + bⱼ²)
```

is invariant under `s ↦ 1 - s` and under conjugation, is strictly positive on the real axis, and
vanishes exactly on the prescribed quartets `1/2 ± aⱼ ± i bⱼ`.  Consequently `A · ξ` is entire,
carries both completed-xi symmetries, is nonvanishing on the real segment `(0,1)`, keeps the
order-one growth envelope, and has every prescribed off-critical zero.

This is the arbitrary-packet strengthening of the single-quartet countermodel in
`XiRationalQuartetGauge`.
-/

namespace RHTower

open Complex Polynomial
open scoped BigOperators

noncomputable section

variable {r : ℕ}

/-! ## The finite packet gauge -/

/-- The finite packet gauge: a product of centered quartic gauges. -/
def finitePacketGauge (a b : Fin r → ℝ) (s : ℂ) : ℂ :=
  ∏ j, centeredQuartetGauge (a j) (b j) s

theorem finitePacketGauge_one_sub (a b : Fin r → ℝ) (s : ℂ) :
    finitePacketGauge a b (1 - s) = finitePacketGauge a b s :=
  Finset.prod_congr rfl fun j _ => centeredQuartetGauge_one_sub (a j) (b j) s

theorem finitePacketGauge_conj (a b : Fin r → ℝ) (s : ℂ) :
    finitePacketGauge a b ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (finitePacketGauge a b s) := by
  rw [finitePacketGauge, finitePacketGauge, map_prod]
  exact Finset.prod_congr rfl fun j _ => centeredQuartetGauge_conj (a j) (b j) s

theorem finitePacketGauge_ofReal (a b : Fin r → ℝ) (σ : ℝ) :
    finitePacketGauge a b (σ : ℂ)
      = ((∏ j, ((((σ - 1 / 2) - a j) ^ (2 : ℕ) + (b j) ^ (2 : ℕ))
          * (((σ - 1 / 2) + a j) ^ (2 : ℕ) + (b j) ^ (2 : ℕ))) : ℝ) : ℂ) := by
  rw [finitePacketGauge, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun j _ => centeredQuartetGauge_ofReal (a j) (b j) σ

theorem finitePacketGauge_real_pos {a b : Fin r → ℝ} (hb : ∀ j, 0 < b j) (σ : ℝ) :
    0 < (finitePacketGauge a b (σ : ℂ)).re := by
  rw [finitePacketGauge_ofReal, Complex.ofReal_re]
  refine Finset.prod_pos fun j _ => ?_
  exact mul_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hb j)))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hb j)))

theorem finitePacketGauge_real_ne_zero {a b : Fin r → ℝ} (hb : ∀ j, 0 < b j) (σ : ℝ) :
    finitePacketGauge a b (σ : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.zero_re] at hre
  exact (ne_of_gt (finitePacketGauge_real_pos hb σ)) hre

theorem finitePacketGauge_quartetPoint (a b : Fin r → ℝ) (j : Fin r) :
    finitePacketGauge a b (quartetPoint (a j) (b j)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (centeredQuartetGauge_quartetPoint (a j) (b j))

theorem finitePacketGauge_analyticAt (a b : Fin r → ℝ) (s : ℂ) :
    AnalyticAt ℂ (finitePacketGauge a b) s := by
  unfold finitePacketGauge centeredQuartetGauge
  fun_prop

/-! ## The polynomial form -/

/-- The centered quartic gauge as a polynomial. -/
def centeredQuartetPoly (a b : ℝ) : Polynomial ℂ :=
  ((X - C ((1 : ℂ) / 2) - C ((a : ℝ) : ℂ)) ^ (2 : ℕ) + C (((b : ℝ) : ℂ) ^ (2 : ℕ))) *
    ((X - C ((1 : ℂ) / 2) + C ((a : ℝ) : ℂ)) ^ (2 : ℕ) + C (((b : ℝ) : ℂ) ^ (2 : ℕ)))

theorem centeredQuartetPoly_eval (a b : ℝ) (s : ℂ) :
    (centeredQuartetPoly a b).eval s = centeredQuartetGauge a b s := by
  simp only [centeredQuartetPoly, centeredQuartetGauge, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]

/-- The finite packet gauge as a polynomial. -/
def finitePacketPoly (a b : Fin r → ℝ) : Polynomial ℂ :=
  ∏ j, centeredQuartetPoly (a j) (b j)

theorem finitePacketPoly_eval (a b : Fin r → ℝ) (s : ℂ) :
    (finitePacketPoly a b).eval s = finitePacketGauge a b s := by
  rw [finitePacketPoly, Polynomial.eval_prod, finitePacketGauge]
  exact Finset.prod_congr rfl fun j _ => centeredQuartetPoly_eval (a j) (b j) s

theorem finitePacketPoly_ne_zero {a b : Fin r → ℝ} (hb : ∀ j, 0 < b j) :
    finitePacketPoly a b ≠ 0 := by
  intro h
  have hval : (finitePacketPoly a b).eval ((0 : ℝ) : ℂ) = 0 := by rw [h]; simp
  rw [finitePacketPoly_eval] at hval
  exact finitePacketGauge_real_ne_zero hb 0 hval

/-! ## The gauged completed xi -/

/-- Completed xi multiplied by the finite packet gauge. -/
def finitePacketGaugedXi (a b : Fin r → ℝ) (s : ℂ) : ℂ :=
  finitePacketGauge a b s * xi s

theorem finitePacketGaugedXi_analyticAt (a b : Fin r → ℝ) (s : ℂ) :
    AnalyticAt ℂ (finitePacketGaugedXi a b) s :=
  (finitePacketGauge_analyticAt a b s).mul (xi_analyticOnNhd_univ s (Set.mem_univ s))

theorem finitePacketGaugedXi_one_sub (a b : Fin r → ℝ) (s : ℂ) :
    finitePacketGaugedXi a b (1 - s) = finitePacketGaugedXi a b s := by
  rw [finitePacketGaugedXi, finitePacketGaugedXi, finitePacketGauge_one_sub, xi_one_sub]

theorem finitePacketGaugedXi_conj (a b : Fin r → ℝ) (s : ℂ) :
    finitePacketGaugedXi a b ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (finitePacketGaugedXi a b s) := by
  rw [finitePacketGaugedXi, finitePacketGaugedXi, finitePacketGauge_conj, xi_conj, map_mul]

theorem finitePacketGaugedXi_quartetPoint (a b : Fin r → ℝ) (j : Fin r) :
    finitePacketGaugedXi a b (quartetPoint (a j) (b j)) = 0 := by
  rw [finitePacketGaugedXi, finitePacketGauge_quartetPoint, zero_mul]

theorem finitePacketGaugedXi_real_anchor_ne_zero {a b : Fin r → ℝ} (hb : ∀ j, 0 < b j)
    {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    finitePacketGaugedXi a b (σ : ℂ) ≠ 0 := by
  refine mul_ne_zero (finitePacketGauge_real_ne_zero hb σ) ?_
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [Complex.zero_re] at hre
  exact (ne_of_gt (xi_pos_on_real_anchor h0 h1)) hre

/-- **The packet gauge keeps the order-one growth envelope.** -/
theorem finitePacketGaugedXi_orderOneEnvelope {a b : Fin r → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖xi z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ z : ℂ, ‖finitePacketGaugedXi a b z‖
        ≤ Real.exp (C' * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨C', hC', hb'⟩ := RHTower.SpeiserGauge.orderOneEnvelope_mul_polynomial hC (finitePacketPoly a b) hbound
  refine ⟨C', hC', fun z => ?_⟩
  rw [finitePacketGaugedXi, ← finitePacketPoly_eval]
  exact hb' z

/-- **Arbitrary finite off-critical packet implantation.**  For every finite list of quartet
parameters there is an entire function with both completed-xi symmetries, nonvanishing on the real
segment `(0,1)`, whose zero set contains every prescribed off-critical quartet point, and which
differs from `ξ` only by multiplication by a nonzero real-even polynomial. -/
theorem exists_xi_symmetric_entire_finitePacket_countermodel
    (a b : Fin r → ℝ) (ha : ∀ j, a j ≠ 0) (hb : ∀ j, 0 < b j) :
    ∃ F : ℂ → ℂ, ∃ P : Polynomial ℂ,
      P ≠ 0 ∧
      (∀ s, F s = P.eval s * xi s) ∧
      (∀ s, AnalyticAt ℂ F s) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) ∧
      (∀ σ : ℝ, 0 < σ → σ < 1 → F (σ : ℂ) ≠ 0) ∧
      (∀ j, F (quartetPoint (a j) (b j)) = 0 ∧
        (quartetPoint (a j) (b j)).re ≠ 1 / 2) := by
  refine ⟨finitePacketGaugedXi a b, finitePacketPoly a b, finitePacketPoly_ne_zero hb, ?_,
    finitePacketGaugedXi_analyticAt a b, finitePacketGaugedXi_one_sub a b,
    finitePacketGaugedXi_conj a b, ?_, ?_⟩
  · intro s
    rw [finitePacketGaugedXi, finitePacketPoly_eval]
  · intro σ h0 h1
    exact finitePacketGaugedXi_real_anchor_ne_zero hb h0 h1
  · intro j
    exact ⟨finitePacketGaugedXi_quartetPoint a b j, quartetPoint_off_critical (ha j)⟩

/-! ## The polynomial factor does not lower the order -/

open Filter in
/-- A nonzero polynomial is bounded below outside a large disc. -/
theorem exists_radius_norm_polynomial_ge {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → c ≤ ‖P.eval z‖ := by
  rcases eq_or_lt_of_le (Nat.zero_le P.natDegree) with hdeg | hdeg
  · obtain ⟨u, hu⟩ := Polynomial.natDegree_eq_zero.mp hdeg.symm
    have hune : u ≠ 0 := by
      intro h
      exact hP (by rw [← hu, h, map_zero])
    exact ⟨‖u‖, norm_pos_iff.mpr hune, 0, fun z _ => by rw [← hu]; simp⟩
  · have hdeg' : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
    have htend : Tendsto (fun z : ℂ => ‖P.eval z‖) (Filter.cocompact ℂ) atTop :=
      Polynomial.tendsto_norm_atTop P hdeg' tendsto_norm_cocompact_atTop
    have hev : ∀ᶠ z in Filter.cocompact ℂ, (1 : ℝ) ≤ ‖P.eval z‖ :=
      htend.eventually_ge_atTop 1
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop (E := ℂ),
      Filter.eventually_comap] at hev
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hev
    exact ⟨1, one_pos, R, fun z hz => hR ‖z‖ hz z rfl⟩

/-- **The packet gauge does not lower the growth of `ξ`.**  Outside a large disc the gauged
function dominates a fixed positive multiple of `ξ`, so every lower growth bound — in particular
the exact order one — is inherited. -/
theorem finitePacketGaugedXi_norm_ge {a b : Fin r → ℝ} (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      c * ‖xi z‖ ≤ ‖finitePacketGaugedXi a b z‖ := by
  obtain ⟨c, hc, R, hR⟩ := exists_radius_norm_polynomial_ge (finitePacketPoly_ne_zero hb)
  refine ⟨c, hc, R, fun z hz => ?_⟩
  rw [finitePacketGaugedXi, ← finitePacketPoly_eval, norm_mul]
  exact mul_le_mul_of_nonneg_right (hR z hz) (norm_nonneg _)


end

end RHTower
