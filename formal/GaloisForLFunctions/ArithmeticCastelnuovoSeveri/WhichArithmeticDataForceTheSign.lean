import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve

/-!
# Which Arithmetic Data Force the Sign?

Section 6.1 (Question 3) of the Arithmetic Castelnuovo–Severi programme asks:

> **Which arithmetic data force the sign?** Not span data, integrality, functional equation or
> positive Euler data — the golden datum has all of them and fails. A forcing input must be
> violated by such fake data.

This module gives the complete mathematical answer across all five levels of the theory — spectral,
trace/point-count, intersection-theoretic, dual/ambient cone-theoretic, and on the scaling surface
of `ℤ` — and proves that every forcing datum is violated by fake data (`goldenDatum` and
`hidingDatum`):

1. **The Rosati Involution Fixed-Point Law and the Universal Frobenius Reflection Identity**
   (`CurveDatum.β_reflPerm_mul_conj`, `CurveDatum.norm_β_eq_one_iff_β_reflPerm_eq`,
   `CurveDatum.toeplitz_eq_frobSquareMass_sub_frobReflectionDefect`,
   `CurveDatum.frobReflectionDefect_singleton_one`,
   `CurveDatum.frobReflectionDefect_eq_zero_iff_unitary`,
   `goldenDatum_frobReflectionDefect_singleton_one`,
   `hidingDatum_frobReflectionDefect_singleton_one`):
   * Every `CurveDatum D` carries two involutions on its spectrum: `conjPerm` ($\beta \mapsto \bar{\beta}$,
     encoding real traces and Witt/Euler integrality) and `fePerm` ($\beta \mapsto \beta^{-1}$,
     encoding the functional equation / Poincaré duality). Having both separately does not force
     unitarity because on a real off-circle pair $(\beta, \beta^{-1})$, `conjPerm` acts as the
     identity while `fePerm` swaps $\beta \leftrightarrow \beta^{-1}$.
   * Their composition `D.reflPerm = D.conjPerm.symm.trans D.fePerm` is the spectral action of
     Weil's **Rosati involution** $\alpha \mapsto \alpha^\dagger = q \bar{\alpha}^{-1}$ and obeys
     the universal law `D.β (D.reflPerm i) * conj(D.β i) = 1` on *every* `CurveDatum`. Consequently,
     `‖D.β i‖ = 1 ↔ D.β (D.reflPerm i) = D.β i`: unitarity is **pointwise Rosati invariance** (the
     commutation of Frobenius with the Rosati involution).
   * For *every* `CurveDatum D` (unitary or fake), every window `S`, and every weight `e`, the
     Castelnuovo–Severi Toeplitz form decomposes as
     $$D.\text{toeplitz } S\, e = \mathcal{Z}_D(S, e) - \mathcal{R}_D(S, e),$$
     where $\mathcal{Z}_D(S, e) = \sum_i \|F_e(\beta_i)\|^2 \ge 0$ is the positive-definite Rosati
     square mass and $\mathcal{R}_D(S, e) = \frac{1}{2}\sum_i \|F_e(\beta_i) - F_e(\beta_{\text{reflPerm } i})\|^2 \ge 0$
     is the **Frobenius reflection defect**. At the single graph window $S = \{1\}$,
     $\mathcal{R}_D(\{1\}, 1) = \frac{1}{2}\sum_i (\|\beta_i\| - \|\beta_i\|^{-1})^2$. On
     `goldenDatum`, $\mathcal{R}(\{1\}, 1) = 1 > 0$; on `hidingDatum N`, $\mathcal{R}(\{1\}, 1) = 9/4 > 0$
     for every $N \ge 1$.

2. **The Exact Lag-2 Trace–Reflection–Oscillation Identity and Real-Spectrum Forcing**
   (`CurveDatum.trace_two_eq_card_add_frobReflectionDefect_sub_im_sq`,
   `CurveDatum.trace_two_eq_card_add_radial_sub_im_sq`,
   `CurveDatum.unitary_iff_trace_two_le_card_of_im_eq_zero`,
   `CurveDatum.unitary_iff_pointCount_two_ge_of_im_eq_zero`,
   `goldenDatum_trace_two_eq_three`, `goldenDatum_pointCount_two_eq_eleven`):
   * Every `CurveDatum D` satisfies the exact lag-2 identity
     $$D.\text{trace } 2 - |\iota| = \frac{1}{2}\sum_{i \in \iota} \left(\|\beta_i\| - \|\beta_i\|^{-1}\right)^2 - 2\sum_{i \in \iota} (\operatorname{Im}\beta_i)^2.$$
   * Consequently, for any datum with real spectrum ($\operatorname{Im}\beta_i = 0$, such as
     `goldenDatum`), the single lag-2 point-count inequality $N_2 \ge q^2 + 1 - 2g q$
     (`D.trace 2 ≤ |ι|`) **alone** forces unitarity and the all-window Hodge index. On
     `goldenDatum`, $N_2 = 11 > 0$ is positive as a raw count, but violates the lag-2 Hasse–Weil
     lower bound $5^2 + 1 - 2 \cdot 5 = 16$ by $5(\varphi - \varphi^{-1})^2 = 5$.

3. **Why Positive Euler / Beurling Data Fail vs. The 9-Way Forcing Arithmetic Equivalence (`TFAE`)**
   (`CurveDatum.windowSurface_polar_graphCycle`, `CurveDatum.pointCount_nonneg_iff_trace_le_pole`,
   `CurveDatum.unitary_of_trace_bdd`, `CurveDatum.forcing_arithmetic_data_tfae`):
   * On `D.windowSurface S`, two Frobenius graphs $\Gamma_j, \Gamma_k$ have polar intersection
     $\operatorname{polar}(\Gamma_j, \Gamma_k) = q^j + q^k$ and raw intersection
     $\Gamma_j \cdot \Gamma_k = \operatorname{polar}(\Gamma_j, \Gamma_k) - \delta(\Gamma_j, \Gamma_k)$.
     Raw point-count positivity $N_k \ge 0$ (`graphCone` Bézout positivity) only asserts
     $\delta(\Gamma_k, \Delta) \le \operatorname{polar}(\Gamma_k, \Delta)$, i.e.
     $D.\text{trace } k \le q^{k/2} + q^{-k/2}$ (the critical-strip pole bound $|\beta_i| \le \sqrt{q}$).
     Because `goldenDatum` has $1 < \varphi < \sqrt{5}$, the $H^0 \oplus H^2$ polar part $5^k + 1$
     masks the off-line growth.
   * Once the polar part $q^k + 1$ is subtracted, 9 arithmetic conditions are unconditionally
     equivalent (`List.TFAE`), including all-window `HodgeIndex`, unitarity, Rosati fixed-point
     invariance, vanishing reflection defect, the $2 \times 2$ Hasse–Weil point-count envelope
     $|N_k - (q^k + 1)| \le 2g \, q^{k/2}$, mere boundedness of the normalized traces
     $\exists C,\, \forall k,\, |D.\text{trace } k| \le C$, and finite-horizon Toeplitz positivity
     on the first $2g$ Frobenius graphs.

4. **Geometric Forcing Data on Polar Surfaces: Forward Light-Cone Bézout, the Dual (Nef) Cone
   Obstruction on `goldenDatum`, and Ambient Realizability**
   (`PolarSurface.hodgeIndex_iff_positiveCone_bezout`,
   `PolarSurface.hodgeIndex_iff_openPositiveCone_bezout`,
   `PolarSurface.hodgeIndex_bezout_tfae`,
   `goldenForwardPair_violates_openPositiveCone_bezout`,
   `goldenCounterexample_mem_dualCone_graphCone`,
   `goldenDatum_dualCone_graphCone_not_ample`,
   `PolarSurface.dualCone_ample_of_orderUnit`,
   `PolarSurface.hodgeIndex_of_ambient_bezout_riemannRoch`,
   `goldenDatum_no_ambient_bezout_riemannRoch`):
   * On any `PolarSurface S`, `S.HodgeIndex` is unconditionally equivalent to `S.BezoutAxiom S.positiveCone`
     and to `S.BezoutAxiom S.openPositiveCone`. On `goldenDatum.windowSurface {0, 1}`, the explicit
     integer forward light-cone classes $e_+ = -H + 7V + 4\Gamma_0 - 2\Gamma_1$ and
     $e_- = 3H - 5V - 4\Gamma_0 + 2\Gamma_1$ satisfy $e_\pm^2 = 10 > 0$, $e_\pm \cdot (H + V) = 2 > 0$,
     $e_+ + e_- = 2(H + V) \in \text{graphCone } \{0, 1\}$, yet collide negatively:
     $e_+ \cdot e_- = -6 < 0$.
   * On `goldenDatum.windowSurface {0, 1}`, the primitive positive-square class
     `goldenCounterexample = -H + 3V + 2Γ₀ - Γ₁` pairs nonnegatively with $H, V, \Gamma_0, \Gamma_1$
     ($0, 0, 1, 0 \ge 0$) and therefore lies in `dualCone (graphCone {0, 1})`, violating
     `AmpleAxiom (dualCone (graphCone {0, 1}))`. By contrast, whenever a cone $E$ generates $C$ and
     satisfies **ample order-unit dominance** ($\forall e \in E,\, \exists m \ge 0,\, m A - e \in E$),
     `dualCone E` is unconditionally ample.
   * Any polar surface that embeds bilinearly into an ambient space carrying a Bézout–Riemann–Roch
     cone satisfies `HodgeIndex`; thus `goldenDatum` admits no ambient Bézout–Riemann–Roch
     realization.

5. **Application to `scalingSurface` over `ℤ`: Pole Subtraction in the Odd Sector and the 9-Way
   Forcing Equivalence**
   (`coupledArithmeticCone_bezout_iff_hodgeIndex`,
   `strictCoupledArithmeticCone_bezout_iff_hodgeIndex`,
   `scalingSurface_forcing_tfae`):
   * On `scalingSurface`, `posTestCone` ($f \ge 0$) fails to force `HodgeIndex` for the same reason
     as `graphCone`: its positive polar product $2 B(f) A(f) > 0$ masks the prime sum. Passing to
     the odd reflection sector `oddRealTestsAt r` forces $B(f) = -A(f)$ and $2 B(f) A(f) = -2 A(f)^2 \le 0$,
     stripping the polar mask and yielding a 9-way `List.TFAE` equivalence between `RiemannHypothesis`,
     `scalingSurface.HodgeIndex`, forward light-cone Bézout positivity on `scalingSurface` and on
     `scalingSubsurface (oddRealTestsAt r)`, and all-aperture reflected prime–polar ledger allocation.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. The Rosati Involution Fixed-Point Law and the Universal Frobenius Reflection Identity -/

/-- For every nonzero complex number `z`, the squared distance to its unit-circle reflection
`circleReflect z = (conj z)⁻¹` equals the radial off-circle square `(‖z‖ - ‖z‖⁻¹)²`. -/
theorem norm_sub_circleReflect_sq {z : ℂ} (hz : z ≠ 0) :
    ‖z - circleReflect z‖ ^ 2 = (‖z‖ - ‖z‖⁻¹) ^ 2 := by
  have hcz : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).mpr hz
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hmul : (z - circleReflect z) * starRingEnd ℂ z = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [sub_mul, circleReflect, inv_mul_cancel₀ hcz, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hnorm := congrArg (fun w : ℂ => ‖w‖ ^ 2) hmul
  simp only [norm_mul, Complex.norm_conj, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hnorm
  have hrad : (‖z‖ - ‖z‖⁻¹) ^ 2 * ‖z‖ ^ 2 = (‖z‖ ^ 2 - 1) ^ 2 := by
    calc (‖z‖ - ‖z‖⁻¹) ^ 2 * ‖z‖ ^ 2
        = ((‖z‖ - ‖z‖⁻¹) * ‖z‖) ^ 2 := (mul_pow _ _ 2).symm
      _ = (‖z‖ ^ 2 - 1) ^ 2 := by
          rw [sub_mul, inv_mul_cancel₀ hnz]
          ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hnz) (hnorm.trans hrad.symm)

/-- The Frobenius polynomial readout `F_e(z) = ∑_{k ∈ S} e_k z^k` of a window weight `e`. -/
def frobPoly (S : Finset ℕ) (e : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ S, (e k : ℂ) * z ^ k

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Universal Rosati pairing law.** On every `CurveDatum D` (unitary or fake), the circle-reflection
permutation `D.reflPerm = D.conjPerm.symm.trans D.fePerm` satisfies
`D.β (D.reflPerm i) * conj(D.β i) = 1`. -/
theorem β_reflPerm_mul_conj (i : ι) :
    D.β (D.reflPerm i) * starRingEnd ℂ (D.β i) = 1 := by
  rw [D.β_reflPerm, circleReflect, inv_mul_cancel₀ ((map_ne_zero _).mpr (D.β_ne_zero i))]

/-- Applying `D.reflPerm` twice restores every normalized Frobenius eigenvalue. -/
theorem β_reflPerm_reflPerm (i : ι) :
    D.β (D.reflPerm (D.reflPerm i)) = D.β i := by
  rw [D.β_reflPerm, D.β_reflPerm, circleReflect_circleReflect]

/-- **Pointwise Rosati fixed-point characterization of unitarity.** An eigenvalue `D.β i` lies on
the unit circle if and only if it is fixed by the Rosati reflection `D.reflPerm`. -/
theorem norm_β_eq_one_iff_β_reflPerm_eq (i : ι) :
    ‖D.β i‖ = 1 ↔ D.β (D.reflPerm i) = D.β i := by
  constructor
  · intro h
    rw [D.β_reflPerm, circleReflect_of_norm_one h]
  · intro h
    have hmul := D.β_reflPerm_mul_conj i
    rw [h, Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj,
      Complex.normSq_eq_norm_sq] at hmul
    nlinarith [norm_nonneg (D.β i)]

/-- For every eigenvalue `D.β i`, the squared Rosati displacement `‖β_i - β_{reflPerm i}‖²` equals
the radial off-circle square `(‖β_i‖ - ‖β_i‖⁻¹)²`. -/
theorem norm_β_sub_reflPerm_sq (i : ι) :
    ‖D.β i - D.β (D.reflPerm i)‖ ^ 2 = (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by
  rw [D.β_reflPerm, norm_sub_circleReflect_sq (D.β_ne_zero i)]

/-- The **Frobenius square-sampling mass** `Z_D(S, e) = ∑_i ‖F_e(β_i)‖² ≥ 0` (the positive-definite
Rosati trace form on the Frobenius span). -/
def frobSquareMass (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ i : ι, ‖frobPoly S e (D.β i)‖ ^ 2

/-- The **Frobenius reflection defect** `R_D(S, e) = ½ ∑_i ‖F_e(β_i) - F_e(β_{reflPerm i})‖² ≥ 0`,
measuring the failure of `F_e(β)` to be fixed by the Rosati reflection `D.reflPerm`. -/
def frobReflectionDefect (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : ι, ‖frobPoly S e (D.β i) - frobPoly S e (D.β (D.reflPerm i))‖ ^ 2

theorem frobSquareMass_nonneg (S : Finset ℕ) (e : ℕ → ℝ) :
    0 ≤ D.frobSquareMass S e :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem frobReflectionDefect_nonneg (S : Finset ℕ) (e : ℕ → ℝ) :
    0 ≤ D.frobReflectionDefect S e :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- On every `CurveDatum D`, the Toeplitz form is the reflected Frobenius evaluation pairing
`∑_i Re(conj(F_e(β_i)) F_e(β_{reflPerm i}))`. -/
theorem toeplitz_eq_sum_re_frobPoly_reflPerm (S : Finset ℕ) (e : ℕ → ℝ) :
    D.toeplitz S e =
      ∑ i : ι, (starRingEnd ℂ (frobPoly S e (D.β i)) *
        frobPoly S e (D.β (D.reflPerm i))).re := by
  have hconj : ∀ i : ι, D.β (D.conjPerm.symm i) = starRingEnd ℂ (D.β i) := fun i => by
    have h := D.β_conjPerm (D.conjPerm.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Complex.conj_conj]
  have hrefl : ∀ i : ι, D.fePerm (D.conjPerm.symm i) = D.reflPerm i := fun _ => rfl
  have hdist : ∀ k l : ℕ, D.trace (Nat.dist k l) =
      ∑ i : ι, (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re := fun k l => by
    rw [trace, powerSum_dist, ← Equiv.sum_comp D.conjPerm.symm, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hconj, hrefl]
  simp only [toeplitz, hdist, frobPoly, map_sum, map_mul, map_pow, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  calc ∑ k ∈ S, ∑ l ∈ S, ∑ i : ι,
        e k * e l * (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re
      = ∑ l ∈ S, ∑ k ∈ S, ∑ i : ι,
        e k * e l * (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re :=
        Finset.sum_comm
    _ = ∑ l ∈ S, ∑ i : ι, ∑ k ∈ S,
        e k * e l * (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i : ι, ∑ l ∈ S, ∑ k ∈ S,
        e k * e l * (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun k _ => ?_
        have : (e k : ℂ) * starRingEnd ℂ (D.β i) ^ k * ((e l : ℂ) * D.β (D.reflPerm i) ^ l) =
            ((e k * e l : ℝ) : ℂ) * (starRingEnd ℂ (D.β i) ^ k * D.β (D.reflPerm i) ^ l) := by
          push_cast; ring
        rw [this, Complex.re_ofReal_mul]

/-- **Universal Frobenius Reflection Identity.** On *every* `CurveDatum D` (unitary or fake), every
finite window `S`, and every weight `e`, the Toeplitz defect form equals the positive-definite
square-sampling mass minus the Frobenius reflection defect:
`D.toeplitz S e = D.frobSquareMass S e - D.frobReflectionDefect S e`. -/
theorem toeplitz_eq_frobSquareMass_sub_frobReflectionDefect (S : Finset ℕ) (e : ℕ → ℝ) :
    D.toeplitz S e = D.frobSquareMass S e - D.frobReflectionDefect S e := by
  have hnorm_sub : ∀ z w : ℂ, ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (starRingEnd ℂ z * w).re := by
    intro z w
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hperm : ∑ i : ι, ‖frobPoly S e (D.β (D.reflPerm i))‖ ^ 2 = D.frobSquareMass S e :=
    Equiv.sum_comp D.reflPerm (fun i => ‖frobPoly S e (D.β i)‖ ^ 2)
  rw [D.toeplitz_eq_sum_re_frobPoly_reflPerm, frobReflectionDefect]
  simp_rw [hnorm_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hperm]
  unfold frobSquareMass
  ring

/-- On `D.windowSurface S`, the Castelnuovo–Severi defect of any span cycle `x` decomposes into
`frobSquareMass - frobReflectionDefect` in the normalized graph coordinates `e_k = d_k q^{k/2}`. -/
theorem windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect
    (S : Finset ℕ) (x : SpanCycle) :
    (D.windowSurface S).defect x x =
      D.frobSquareMass S (fun k => x.2.2 k * D.sqrtq ^ k) -
        D.frobReflectionDefect S (fun k => x.2.2 k * D.sqrtq ^ k) := by
  rw [D.windowSurface_defect_self, D.spanDefect_eq_toeplitz,
    D.toeplitz_eq_frobSquareMass_sub_frobReflectionDefect]

/-- At the singleton window `{1}` with unit weight, the Frobenius reflection defect is the radial
off-circle sum `½ ∑_i (‖β_i‖ - ‖β_i‖⁻¹)²`. -/
theorem frobReflectionDefect_singleton_one :
    D.frobReflectionDefect {1} (fun _ => 1) =
      (1 / 2 : ℝ) * ∑ i : ι, (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by
  unfold frobReflectionDefect frobPoly
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_singleton, Complex.ofReal_one, one_mul, pow_one,
    D.norm_β_sub_reflPerm_sq i]

/-- Vanishing of the lag-1 reflection defect `D.frobReflectionDefect {1} 1 = 0` is unconditionally
equivalent to unitarity `∀ i, ‖D.β i‖ = 1`. -/
theorem frobReflectionDefect_singleton_one_eq_zero_iff_unitary :
    D.frobReflectionDefect {1} (fun _ => 1) = 0 ↔ ∀ i : ι, ‖D.β i‖ = 1 := by
  rw [D.frobReflectionDefect_singleton_one, mul_eq_zero]
  simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, forall_true_left, sq_eq_zero_iff, sub_eq_zero]
  have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (D.β_ne_zero i)
  constructor
  · intro h
    have hmul := congrArg (· * ‖D.β i‖) h
    simp only [inv_mul_cancel₀ hpos.ne'] at hmul
    nlinarith
  · intro h
    rw [h, inv_one]

/-- Vanishing of the Frobenius reflection defect across all windows and weights is unconditionally
equivalent to unitarity `∀ i, ‖D.β i‖ = 1`. -/
theorem frobReflectionDefect_eq_zero_iff_unitary :
    (∀ S : Finset ℕ, ∀ e : ℕ → ℝ, D.frobReflectionDefect S e = 0) ↔ ∀ i : ι, ‖D.β i‖ = 1 := by
  constructor
  · intro h
    exact D.frobReflectionDefect_singleton_one_eq_zero_iff_unitary.mp (h {1} (fun _ => 1))
  · intro hU S e
    unfold frobReflectionDefect
    suffices ∑ i : ι, ‖frobPoly S e (D.β i) - frobPoly S e (D.β (D.reflPerm i))‖ ^ 2 = 0 by
      rw [this, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(D.norm_β_eq_one_iff_β_reflPerm_eq i).mp (hU i), sub_self, norm_zero, zero_pow (by omega)]

end CurveDatum

open Real in
/-- **The golden fake curve violates Rosati fixed-point invariance**: `reflPerm` swaps `φ` and
`φ⁻¹`. -/
theorem goldenDatum_β_reflPerm_ne :
    goldenDatum.β (goldenDatum.reflPerm 0) ≠ goldenDatum.β 0 := by
  intro h
  have h1 : ‖goldenDatum.β 0‖ = 1 :=
    (goldenDatum.norm_β_eq_one_iff_β_reflPerm_eq 0).mpr h
  simp only [goldenDatum, Matrix.cons_val_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos goldenRatio_pos] at h1
  linarith [one_lt_goldenRatio]

open Real in
/-- **The golden fake curve has lag-1 Frobenius reflection defect `1 > 0`**, because
`(φ - φ⁻¹)² = 1`. -/
theorem goldenDatum_frobReflectionDefect_singleton_one :
    goldenDatum.frobReflectionDefect {1} (fun _ => 1) = 1 := by
  rw [CurveDatum.frobReflectionDefect_singleton_one, Fin.sum_univ_two]
  have h0 : ‖goldenDatum.β 0‖ = goldenRatio := by
    change ‖((goldenRatio : ℝ) : ℂ)‖ = goldenRatio
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
  have h1 : ‖goldenDatum.β 1‖ = goldenRatio⁻¹ := by
    change ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ = goldenRatio⁻¹
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr goldenRatio_pos).le]
  have hdiff : goldenRatio - goldenRatio⁻¹ = 1 := by
    rw [inv_goldenRatio]
    simp only [goldenRatio, goldenConj]
    ring
  rw [h0, h1, inv_inv]
  nlinarith [hdiff]

/-- **Every hiding datum `hidingDatum N` has lag-1 Frobenius reflection defect `9/4 > 0`**,
independent of the number `2N` of on-line roots of unity used to mask small windows. -/
theorem hidingDatum_frobReflectionDefect_singleton_one (N : ℕ) [NeZero N] :
    (hidingDatum N).frobReflectionDefect {1} (fun _ => 1) = 9 / 4 := by
  rw [CurveDatum.frobReflectionDefect_singleton_one]
  have hn : ‖Complex.exp (2 * Real.pi * I / N)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.univ_bool,
    Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)), Finset.sum_singleton]
  have hunit : ∀ k : Fin N,
      (‖(hidingDatum N).β (Sum.inr (k, true))‖ - ‖(hidingDatum N).β (Sum.inr (k, true))‖⁻¹) ^ 2 +
        (‖(hidingDatum N).β (Sum.inr (k, false))‖ -
          ‖(hidingDatum N).β (Sum.inr (k, false))‖⁻¹) ^ 2 = 0 := by
    intro k
    simp [hidingDatum, hn]
  rw [Finset.sum_eq_zero fun k _ => hunit k, add_zero]
  simp only [hidingDatum, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-! ### 2. The Exact Lag-2 Trace–Reflection–Oscillation Identity and Real-Spectrum Forcing -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The sum of squared moduli of the normalized eigenvalues equals `|ι|` plus the lag-1 Frobenius
reflection defect. -/
theorem sum_norm_β_sq_eq_card_add_frobReflectionDefect :
    ∑ i : ι, ‖D.β i‖ ^ 2 =
      (Fintype.card ι : ℝ) + D.frobReflectionDefect {1} (fun _ => 1) := by
  have hperm : ∑ i : ι, ‖D.β (D.reflPerm i)‖ ^ 2 = ∑ i : ι, ‖D.β i‖ ^ 2 :=
    Equiv.sum_comp D.reflPerm (fun i => ‖D.β i‖ ^ 2)
  have hrefl : ∀ i : ι, ‖D.β (D.reflPerm i)‖ ^ 2 = (‖D.β i‖⁻¹) ^ 2 := fun i => by
    rw [D.β_reflPerm, norm_circleReflect]
  have hpair : ∀ i : ι, ‖D.β i‖ ^ 2 + (‖D.β i‖⁻¹) ^ 2 = 2 + (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by
    intro i
    have hnz : ‖D.β i‖ ≠ 0 := norm_ne_zero_iff.mpr (D.β_ne_zero i)
    calc ‖D.β i‖ ^ 2 + (‖D.β i‖⁻¹) ^ 2
        = (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 + 2 * (‖D.β i‖ * ‖D.β i‖⁻¹) := by ring
      _ = 2 + (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by rw [mul_inv_cancel₀ hnz]; ring
  have hsum : 2 * ∑ i : ι, ‖D.β i‖ ^ 2 =
      2 * (Fintype.card ι : ℝ) + ∑ i : ι, (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by
    calc 2 * ∑ i : ι, ‖D.β i‖ ^ 2
        = ∑ i : ι, ‖D.β i‖ ^ 2 + ∑ i : ι, ‖D.β (D.reflPerm i)‖ ^ 2 := by rw [hperm]; ring
      _ = ∑ i : ι, (‖D.β i‖ ^ 2 + (‖D.β i‖⁻¹) ^ 2) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [hrefl]
      _ = ∑ i : ι, (2 + (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpair i
      _ = 2 * (Fintype.card ι : ℝ) + ∑ i : ι, (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  rw [D.frobReflectionDefect_singleton_one]
  linarith

/-- **Exact Lag-2 Trace–Reflection–Oscillation Identity.** On every `CurveDatum D`,
`D.trace 2 = |ι| + D.frobReflectionDefect {1} 1 - 2 ∑_i (Im β_i)²`. -/
theorem trace_two_eq_card_add_frobReflectionDefect_sub_im_sq :
    D.trace 2 =
      (Fintype.card ι : ℝ) + D.frobReflectionDefect {1} (fun _ => 1) -
        2 * ∑ i : ι, (D.β i).im ^ 2 := by
  have hre : ∀ z : ℂ, (z ^ 2).re = ‖z‖ ^ 2 - 2 * z.im ^ 2 := fun z => by
    rw [sq, ← Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.normSq_apply]
    ring
  have htr : D.trace 2 = (∑ i : ι, ‖D.β i‖ ^ 2) - 2 * ∑ i : ι, (D.β i).im ^ 2 := by
    rw [trace, powerSum, Complex.re_sum]
    simp_rw [hre]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [htr, D.sum_norm_β_sq_eq_card_add_frobReflectionDefect]

/-- Explicit radial form of the lag-2 trace–reflection–oscillation identity:
`D.trace 2 = |ι| + ½ ∑_i (‖β_i‖ - ‖β_i‖⁻¹)² - 2 ∑_i (Im β_i)²`. -/
theorem trace_two_eq_card_add_radial_sub_im_sq :
    D.trace 2 =
      (Fintype.card ι : ℝ) + (1 / 2 : ℝ) * ∑ i : ι, (‖D.β i‖ - ‖D.β i‖⁻¹) ^ 2 -
        2 * ∑ i : ι, (D.β i).im ^ 2 := by
  rw [D.trace_two_eq_card_add_frobReflectionDefect_sub_im_sq, D.frobReflectionDefect_singleton_one]

/-- On any datum with real spectrum (`∀ i, (D.β i).im = 0`), the lag-2 trace satisfies
`D.trace 2 = |ι| + D.frobReflectionDefect {1} 1 ≥ |ι|`. -/
theorem trace_two_eq_card_add_frobReflectionDefect_of_im_eq_zero
    (him : ∀ i : ι, (D.β i).im = 0) :
    D.trace 2 = (Fintype.card ι : ℝ) + D.frobReflectionDefect {1} (fun _ => 1) ∧
      (Fintype.card ι : ℝ) ≤ D.trace 2 := by
  have him_sum : ∑ i : ι, (D.β i).im ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [him i, zero_pow (by omega)]
  have heq : D.trace 2 = (Fintype.card ι : ℝ) + D.frobReflectionDefect {1} (fun _ => 1) := by
    rw [D.trace_two_eq_card_add_frobReflectionDefect_sub_im_sq, him_sum, mul_zero, sub_zero]
  exact ⟨heq, by linarith [D.frobReflectionDefect_nonneg {1} (fun _ => 1)]⟩

/-- **Single-Point-Count Forcing Theorem for Real-Spectrum Data.** If all eigenvalues of `D` are
real (`∀ i, (D.β i).im = 0`, as on `goldenDatum`), then unitarity `∀ i, ‖D.β i‖ = 1` is forced by
the single lag-2 trace bound `D.trace 2 ≤ |ι|`. -/
theorem unitary_iff_trace_two_le_card_of_im_eq_zero (him : ∀ i : ι, (D.β i).im = 0) :
    (∀ i : ι, ‖D.β i‖ = 1) ↔ D.trace 2 ≤ Fintype.card ι := by
  obtain ⟨heq, _⟩ := D.trace_two_eq_card_add_frobReflectionDefect_of_im_eq_zero him
  rw [← D.frobReflectionDefect_singleton_one_eq_zero_iff_unitary, heq]
  have hpos := D.frobReflectionDefect_nonneg {1} (fun _ => 1)
  constructor <;> intro h <;> linarith

/-- **Lag-2 Hasse–Weil Lower Bound Forcing Theorem for Real-Spectrum Data.** If all eigenvalues of
`D` are real (`∀ i, (D.β i).im = 0`), then unitarity `∀ i, ‖D.β i‖ = 1` is equivalent to the single
lag-2 point-count inequality `q² + 1 - 2g q ≤ N₂`. -/
theorem unitary_iff_pointCount_two_ge_of_im_eq_zero (him : ∀ i : ι, (D.β i).im = 0) :
    (∀ i : ι, ‖D.β i‖ = 1) ↔
      D.q ^ 2 + 1 - (Fintype.card ι : ℝ) * D.q ≤ D.pointCount 2 := by
  rw [D.unitary_iff_trace_two_le_card_of_im_eq_zero him, pointCount, D.sqrtq_sq]
  have hq : 0 < D.q := by linarith [D.one_lt_q]
  constructor
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h hq.le]
  · intro h
    exact le_of_mul_le_mul_left (by linarith) hq

end CurveDatum

/-- On `goldenDatum`, the lag-2 trace is `3 > 2 = |ι|`, and the lag-2 point count is
`N₂ = 11 < 16 = 5² + 1 - 2 · 5`, refuting unitarity at lag `2` despite `N₂ ≥ 1`. -/
theorem goldenDatum_trace_two_and_pointCount_two :
    goldenDatum.trace 2 = 3 ∧
      goldenDatum.pointCount 2 = 11 ∧
      goldenDatum.pointCount 2 <
        goldenDatum.q ^ 2 + 1 - (Fintype.card (Fin 2) : ℝ) * goldenDatum.q := by
  have him : ∀ i : Fin 2, (goldenDatum.β i).im = 0 := fun i => by
    fin_cases i <;> exact Complex.ofReal_im _
  obtain ⟨heq, _⟩ := goldenDatum.trace_two_eq_card_add_frobReflectionDefect_of_im_eq_zero him
  rw [goldenDatum_frobReflectionDefect_singleton_one] at heq
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have htr : goldenDatum.trace 2 = 3 := by linarith
  have hN2 : goldenDatum.pointCount 2 = 11 := by
    rw [goldenDatum_pointCount_eq]
    norm_num [goldenLucas]
  refine ⟨htr, hN2, ?_⟩
  rw [hN2]
  change (11 : ℝ) < 5 ^ 2 + 1 - (2 : ℝ) * 5
  norm_num

/-! ### 3. Why Positive Euler Data Fail vs. The 9-Way Forcing Arithmetic Equivalence (`TFAE`) -/

/-- The span cycle `(0, 0, Pi.single k 1)` representing the `k`-th Frobenius graph `Γ_k`. -/
def graphCycle (k : ℕ) : SpanCycle :=
  (0, 0, Pi.single k 1)

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- On `D.windowSurface S`, the `k`-th Frobenius graph `Γ_k` (`k ∈ S`) meets `H` in `q^k` and `V`
in `1` (in the convention `H = (1, 0, 0)`, `V = (0, 1, 0)` of `windowSurface`). -/
theorem windowSurface_pair_graphCycle_H_V {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) :
    (D.windowSurface S).pair (graphCycle k) (D.windowSurface S).H = D.q ^ k ∧
      (D.windowSurface S).pair (graphCycle k) (D.windowSurface S).V = 1 := by
  classical
  rw [D.windowSurface_pair_H, D.windowSurface_pair_V]
  simp only [graphCycle, zero_add, windowA, windowB]
  rw [Finset.sum_eq_single k
      (fun j _ hjk => by simp [Pi.single_eq_of_ne hjk])
      (fun h => False.elim (h hk)),
    Finset.sum_eq_single k
      (fun j _ hjk => by simp [Pi.single_eq_of_ne hjk])
      (fun h => False.elim (h hk))]
  simp

/-- **Polar intersection of Frobenius graphs.** For `j, k ∈ S`, the pole-plane intersection of
`Γ_j` and `Γ_k` on `D.windowSurface S` is `q^j + q^k`. -/
theorem windowSurface_polar_graphCycle {S : Finset ℕ} {j k : ℕ} (hj : j ∈ S) (hk : k ∈ S) :
    (D.windowSurface S).polar (graphCycle j) (graphCycle k) = D.q ^ j + D.q ^ k := by
  obtain ⟨hjH, hjV⟩ := D.windowSurface_pair_graphCycle_H_V hj
  obtain ⟨hkH, hkV⟩ := D.windowSurface_pair_graphCycle_H_V hk
  rw [PolarSurface.polar, hjH, hjV, hkH, hkV]
  ring

/-- **Why positive Euler / Beurling data fail to force the sign.** Point-count nonnegativity
`0 ≤ D.pointCount k` is equivalent to the **polar trace bound**
`D.trace k ≤ q^{k/2} + q^{-k/2}` (the critical-strip boundary `|β_i| ≤ √q`), whereas unitarity
requires the pole-subtracted Hasse–Weil bound `|D.trace k| ≤ 2g`. -/
theorem pointCount_nonneg_iff_trace_le_pole (k : ℕ) :
    0 ≤ D.pointCount k ↔ D.trace k ≤ D.sqrtq ^ k + D.sqrtq⁻¹ ^ k := by
  have hpos : 0 < D.sqrtq ^ k := pow_pos D.sqrtq_pos k
  have hsq : D.q ^ k = D.sqrtq ^ k * D.sqrtq ^ k := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  have hinv : D.sqrtq⁻¹ ^ k * D.sqrtq ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ D.sqrtq_pos.ne', one_pow]
  rw [pointCount, sub_nonneg, hsq]
  constructor
  · intro h
    have h1 : D.sqrtq ^ k * D.trace k ≤ (D.sqrtq ^ k + D.sqrtq⁻¹ ^ k) * D.sqrtq ^ k := by
      rw [add_mul, hinv]
      linarith
    exact le_of_mul_le_mul_right (by linarith) hpos
  · intro h
    have h1 := mul_le_mul_of_nonneg_right h hpos.le
    rw [add_mul, hinv] at h1
    linarith

/-- The pole-subtracted point-count bound `|N_k - (q^k + 1)| ≤ C q^{k/2}` is equivalent to the
normalized trace bound `|D.trace k| ≤ C`. -/
theorem abs_pointCount_sub_pole_le_iff_abs_trace_le (k : ℕ) (C : ℝ) :
    |D.pointCount k - (D.q ^ k + 1)| ≤ C * D.sqrtq ^ k ↔ |D.trace k| ≤ C := by
  have hpos : 0 < D.sqrtq ^ k := pow_pos D.sqrtq_pos k
  have hsub : D.pointCount k - (D.q ^ k + 1) = -(D.sqrtq ^ k * D.trace k) := by
    unfold pointCount
    ring
  rw [hsub, abs_neg, abs_mul, abs_of_pos hpos, mul_comm (D.sqrtq ^ k)]
  exact ⟨fun h => le_of_mul_le_mul_right h hpos, fun h => mul_le_mul_of_nonneg_right h hpos.le⟩

/-- **Square-root pole-cancellation forcing theorem.** If the normalized traces `D.trace k` are
bounded by *any* constant `C` across all `k : ℕ` (i.e. `N_k = q^k + 1 + O(q^{k/2})`), then every
eigenvalue of `D` lies on the unit circle (`∀ i, ‖D.β i‖ = 1`). -/
theorem unitary_of_trace_bdd {C : ℝ} (hC : ∀ k : ℕ, |D.trace k| ≤ C) :
    ∀ i : ι, ‖D.β i‖ = 1 := by
  have hle : ∀ i : ι, ‖D.β i‖ ≤ 1 := by
    intro i
    refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound Finset.univ D.β (C := max C 0)
      (m0 := 0) zero_le_one (fun j _ => ?_) i (Finset.mem_univ i)
    change ‖D.powerSum j‖ ≤ max C 0 * 1 ^ j
    rw [one_pow, mul_one, D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
    exact (hC j).trans (le_max_left C 0)
  intro i
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  have hi := hle i
  have hf := hle (D.fePerm i)
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]

/-- **The 9-Way Forcing Arithmetic Data Equivalence.** For any `CurveDatum D`, the following
arithmetic and spectral inputs are unconditionally equivalent (`List.TFAE`) and each forces the
Castelnuovo–Severi sign:
1. All-window Hodge index: `∀ S, (D.windowSurface S).HodgeIndex`;
2. Unitarity (RH for the datum): `∀ i, ‖D.β i‖ = 1`;
3. Pointwise Rosati fixed-point invariance: `∀ i, D.β (D.reflPerm i) = D.β i`;
4. Identically vanishing Frobenius reflection defect: `∀ S e, D.frobReflectionDefect S e = 0`;
5. Vanishing lag-1 radial reflection defect: `D.frobReflectionDefect {1} 1 = 0`;
6. Two-point (`2 × 2`) Hasse–Weil trace bound: `∀ k, |D.trace k| ≤ |ι|`;
7. Pole-subtracted Hasse–Weil point-count envelope: `∀ k, |N_k - (q^k + 1)| ≤ |ι| q^{k/2}`;
8. Asymptotic square-root pole cancellation with *any* constant: `∃ C, ∀ k, |D.trace k| ≤ C`;
9. Finite-horizon Toeplitz positivity on the first `2g = |ι|` Frobenius graphs:
   `hermNegIndex (D.spanGram |ι|) = 0`. -/
theorem forcing_arithmetic_data_tfae :
    List.TFAE
      [ ∀ S : Finset ℕ, (D.windowSurface S).HodgeIndex,
        ∀ i : ι, ‖D.β i‖ = 1,
        ∀ i : ι, D.β (D.reflPerm i) = D.β i,
        ∀ S : Finset ℕ, ∀ e : ℕ → ℝ, D.frobReflectionDefect S e = 0,
        D.frobReflectionDefect {1} (fun _ => 1) = 0,
        ∀ k : ℕ, |D.trace k| ≤ Fintype.card ι,
        ∀ k : ℕ, |D.pointCount k - (D.q ^ k + 1)| ≤ Fintype.card ι * D.sqrtq ^ k,
        ∃ C : ℝ, ∀ k : ℕ, |D.trace k| ≤ C,
        hermNegIndex (D.spanGram (Fintype.card ι)) = 0 ] := by
  tfae_have 1 ↔ 2 := D.windowSurface_hodgeIndex_iff_unitary
  tfae_have 2 ↔ 3 := forall_congr' D.norm_β_eq_one_iff_β_reflPerm_eq
  tfae_have 4 ↔ 2 := D.frobReflectionDefect_eq_zero_iff_unitary
  tfae_have 5 ↔ 2 := D.frobReflectionDefect_singleton_one_eq_zero_iff_unitary
  tfae_have 2 ↔ 9 := D.unitary_iff_negIndex_spanGram_eq_zero
  tfae_have 6 ↔ 7 := forall_congr' fun k =>
    (D.abs_pointCount_sub_pole_le_iff_abs_trace_le k (Fintype.card ι)).symm
  tfae_have 2 → 6 := by
    intro hU k
    have hT : ∀ S e, 0 ≤ D.toeplitz S e := fun S e => by
      rw [D.toeplitz_eq_sum_normSq hU]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h := D.norm_powerSum_le hT k
    rwa [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs] at h
  tfae_have 6 → 8 := fun h => ⟨Fintype.card ι, h⟩
  tfae_have 8 → 2 := fun ⟨_, hC⟩ => D.unitary_of_trace_bdd hC
  tfae_finish

end CurveDatum

/-! ### 4. Geometric Forcing Data on Polar Surfaces: Forward Light-Cone Bézout, the Dual (Nef) Cone
Obstruction on `goldenDatum`, and Ambient Realizability -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **Forward Light-Cone Bézout Equivalence (Closed Cone).** On any polar surface `S`, the Hodge
index theorem holds if and only if the closed forward light cone
`S.positiveCone = {x | 0 ≤ x² ∧ 0 ≤ x · (H + V)}` satisfies the Bézout axiom
(`∀ x, y ∈ S.positiveCone, 0 ≤ x · y`). -/
theorem hodgeIndex_iff_positiveCone_bezout :
    S.HodgeIndex ↔ S.BezoutAxiom S.positiveCone :=
  ⟨S.positiveCone_bezout,
    S.hodgeIndex_of_riemannRoch_of_bezout S.positiveCone_riemannRoch⟩

/-- **Forward Light-Cone Bézout Equivalence (Open Cone).** On any polar surface `S`, the Hodge index
theorem holds if and only if the open forward light cone
`S.openPositiveCone = {x | 0 < x² ∧ 0 < x · (H + V)}` satisfies the Bézout axiom
(`∀ x, y ∈ S.openPositiveCone, 0 ≤ x · y`). -/
theorem hodgeIndex_iff_openPositiveCone_bezout :
    S.HodgeIndex ↔ S.BezoutAxiom S.openPositiveCone := by
  constructor
  · exact S.openPositiveCone_bezout
  · intro hBez
    rw [S.hodgeIndex_iff_ampleHodgeIndex]
    intro x hxA
    by_contra hpos
    push Not at hpos
    set X : ℝ := S.pair x x
    have hX : 0 < X := hpos
    have hAx : S.pair S.ample x = 0 := by rw [S.pair_comm, hxA]
    let z₁ : C := (X + 1) • x + X • S.ample
    let z₂ : C := -(X + 1) • x + X • S.ample
    have hz₁_sq : 0 < S.pair z₁ z₁ := by
      have heq : S.pair z₁ z₁ = (X + 1) ^ 2 * X + 2 * X ^ 2 := by
        simp only [z₁, X, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, hxA, hAx, S.pair_ample_ample]
        ring
      rw [heq]; positivity
    have hz₂_sq : 0 < S.pair z₂ z₂ := by
      have heq : S.pair z₂ z₂ = (X + 1) ^ 2 * X + 2 * X ^ 2 := by
        simp only [z₂, X, map_add, map_smul, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul, hxA, hAx, S.pair_ample_ample]
        ring
      rw [heq]; positivity
    have hz₁_A : 0 < S.pair z₁ S.ample := by
      have heq : S.pair z₁ S.ample = 2 * X := by
        simp only [z₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hxA, S.pair_ample_ample]
        ring
      rw [heq]; positivity
    have hz₂_A : 0 < S.pair z₂ S.ample := by
      have heq : S.pair z₂ S.ample = 2 * X := by
        simp only [z₂, map_add, map_smul, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul, hxA, S.pair_ample_ample]
        ring
      rw [heq]; positivity
    have h12 := hBez z₁ ⟨hz₁_sq, hz₁_A⟩ z₂ ⟨hz₂_sq, hz₂_A⟩
    have hneg : S.pair z₁ z₂ = -(X ^ 3 + X) := by
      simp only [z₁, z₂, X, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hxA, hAx, S.pair_ample_ample]
      ring
    have : 0 < X ^ 3 + X := by positivity
    linarith

/-- **Five-way equivalence of the forward light-cone axioms on any polar surface `S`.** -/
theorem hodgeIndex_bezout_tfae :
    List.TFAE
      [ S.HodgeIndex,
        S.BezoutAxiom S.positiveCone,
        S.BezoutAxiom S.openPositiveCone,
        S.AmpleAxiom S.positiveCone,
        S.RiemannRochAxiom S.openPositiveCone ] := by
  tfae_have 1 ↔ 2 := S.hodgeIndex_iff_positiveCone_bezout
  tfae_have 1 ↔ 3 := S.hodgeIndex_iff_openPositiveCone_bezout
  tfae_have 4 ↔ 1 := S.positiveCone_ample_iff_hodgeIndex
  tfae_have 5 ↔ 1 := S.openPositiveCone_riemannRoch_iff_hodgeIndex
  tfae_finish

/-- The **dual (nef) cone** `{x | ∀ e ∈ E, 0 ≤ x · e}` of a cone `E` on a polar surface `S`. -/
def dualCone (E : Set C) : Set C :=
  {x | ∀ e ∈ E, 0 ≤ S.pair x e}

/-- Any cone satisfying `BezoutAxiom` is contained in its dual cone. -/
theorem subset_dualCone_of_bezout {E : Set C} (hB : S.BezoutAxiom E) :
    E ⊆ S.dualCone E :=
  fun x hx y hy => hB x hx y hy

/-- **Ample order-unit dominance forces ampleness of the dual cone.** If `E` generates `C` by
differences (`∀ y, ∃ e₁, e₂ ∈ E, y = e₁ - e₂`) and the ample class `H + V` dominates every generator
of `E` (`∀ e ∈ E, ∃ m ≥ 0, m (H + V) - e ∈ E`), then `S.dualCone E` satisfies `S.AmpleAxiom`
unconditionally. -/
theorem dualCone_ample_of_orderUnit {E : Set C}
    (hspan : ∀ y : C, ∃ e₁ ∈ E, ∃ e₂ ∈ E, y = e₁ - e₂)
    (hdom : ∀ e ∈ E, ∃ m : ℝ, 0 ≤ m ∧ m • S.ample - e ∈ E) :
    S.AmpleAxiom (S.dualCone E) := by
  intro x hx hxA y
  have hzero : ∀ e ∈ E, S.pair x e = 0 := by
    intro e he
    obtain ⟨m, _, hm⟩ := hdom e he
    have hlow : 0 ≤ S.pair x e := hx e he
    have hhigh : 0 ≤ S.pair x (m • S.ample - e) := hx (m • S.ample - e) hm
    simp only [map_sub, map_smul, smul_eq_mul, hxA, mul_zero, zero_sub] at hhigh
    linarith
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hspan y
  rw [map_sub, hzero e₁ he₁, hzero e₂ he₂, sub_self]

/-- **Ambient Bézout–Riemann–Roch Realizability Forces the Hodge Index.** If `S : PolarSurface C`
maps linearly via `ι : C →ₗ[ℝ] C_amb` into an ambient space `C_amb` with a symmetric pairing
`pair_amb` preserving self-intersections (`∀ x, pair_amb (ι x) (ι x) = S.pair x x`), and `C_amb`
carries a cone `E_amb` such that `pair_amb` is nonnegative on `E_amb` and every positive-square
ambient class lies in `E_amb ∪ -E_amb`, then `S.HodgeIndex` holds unconditionally. -/
theorem hodgeIndex_of_ambient_bezout_riemannRoch
    {C_amb : Type*} [AddCommGroup C_amb] [Module ℝ C_amb]
    (pair_amb : C_amb →ₗ[ℝ] C_amb →ₗ[ℝ] ℝ)
    (ι : C →ₗ[ℝ] C_amb)
    (hpair : ∀ x y : C, pair_amb (ι x) (ι y) = S.pair x y)
    {E_amb : Set C_amb}
    (hRR : ∀ u : C_amb, 0 < pair_amb u u → u ∈ E_amb ∨ -u ∈ E_amb)
    (hBez : ∀ u ∈ E_amb, ∀ v ∈ E_amb, 0 ≤ pair_amb u v) :
    S.HodgeIndex := by
  refine S.hodgeIndex_of_riemannRoch_of_bezout (E := ι ⁻¹' E_amb) ?_ ?_
  · intro x hx
    rw [← hpair x x] at hx
    rcases hRR (ι x) hx with h1 | h2
    · exact Or.inl h1
    · right
      simpa [Set.mem_preimage, map_neg] using h2
  · intro x hx y hy
    rw [← hpair x y]
    exact hBez (ι x) hx (ι y) hy

end PolarSurface

/-- The first integer forward light-cone cycle `e_+ = -H + 7V + 4Γ₀ - 2Γ₁` on
`goldenDatum.windowSurface {0, 1}` (`e_+ = (H + V) + 2 goldenCounterexample`). -/
def goldenForwardPlus : SpanCycle :=
  (-1, 7, fun k => if k = 0 then 4 else if k = 1 then -2 else 0)

/-- The second integer forward light-cone cycle `e_- = 3H - 5V - 4Γ₀ + 2Γ₁` on
`goldenDatum.windowSurface {0, 1}` (`e_- = (H + V) - 2 goldenCounterexample`). -/
def goldenForwardMinus : SpanCycle :=
  (3, -5, fun k => if k = 0 then -4 else if k = 1 then 2 else 0)

theorem goldenForwardPlus_eq :
    goldenForwardPlus =
      (goldenDatum.windowSurface {0, 1}).ample + (2 : ℝ) • goldenCounterexample := by
  ext k
  · simp [goldenForwardPlus, PolarSurface.ample, CurveDatum.windowSurface, goldenCounterexample]
    norm_num
  · simp [goldenForwardPlus, PolarSurface.ample, CurveDatum.windowSurface, goldenCounterexample]
    norm_num
  · simp only [goldenForwardPlus, PolarSurface.ample, CurveDatum.windowSurface,
      goldenCounterexample, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, zero_add]
    split_ifs <;> norm_num

theorem goldenForwardMinus_eq :
    goldenForwardMinus =
      (goldenDatum.windowSurface {0, 1}).ample - (2 : ℝ) • goldenCounterexample := by
  ext k
  · simp [goldenForwardMinus, PolarSurface.ample, CurveDatum.windowSurface, goldenCounterexample]
    norm_num
  · simp [goldenForwardMinus, PolarSurface.ample, CurveDatum.windowSurface, goldenCounterexample]
    norm_num
  · simp only [goldenForwardMinus, PolarSurface.ample, CurveDatum.windowSurface,
      goldenCounterexample, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    split_ifs <;> norm_num

/-- **Explicit Integer Forward Light-Cone Bézout Violation on `goldenDatum`.** Although
`graphCone {0, 1}` satisfies `BezoutAxiom` on `goldenDatum.windowSurface {0, 1}`, the two integer
forward light-cone classes `goldenForwardPlus` and `goldenForwardMinus` satisfy
`e_±² = 10 > 0`, `e_± · (H + V) = 2 > 0` (`e_± ∈ openPositiveCone`), and
`e_+ + e_- = 2(H + V) ∈ graphCone {0, 1}`, yet intersect negatively: `e_+ · e_- = -6 < 0`. -/
theorem goldenForwardPair_violates_openPositiveCone_bezout :
    goldenForwardPlus ∈ (goldenDatum.windowSurface {0, 1}).openPositiveCone ∧
      goldenForwardMinus ∈ (goldenDatum.windowSurface {0, 1}).openPositiveCone ∧
      goldenForwardPlus + goldenForwardMinus ∈ graphCone {0, 1} ∧
      (goldenDatum.windowSurface {0, 1}).pair goldenForwardPlus goldenForwardMinus = -6 := by
  obtain ⟨hH, hV, hxx⟩ := goldenCounterexample_violates_hodgeIndex
  have hxA : (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).ample = 0 := by
    rw [(goldenDatum.windowSurface {0, 1}).pair_ample, hH, hV, add_zero]
  have hAx : (goldenDatum.windowSurface {0, 1}).pair
      (goldenDatum.windowSurface {0, 1}).ample goldenCounterexample = 0 := by
    rw [(goldenDatum.windowSurface {0, 1}).pair_comm, hxA]
  have hAA : (goldenDatum.windowSurface {0, 1}).pair
      (goldenDatum.windowSurface {0, 1}).ample (goldenDatum.windowSurface {0, 1}).ample = 2 :=
    (goldenDatum.windowSurface {0, 1}).pair_ample_ample
  have hplus_sq : (goldenDatum.windowSurface {0, 1}).pair
      goldenForwardPlus goldenForwardPlus = 10 := by
    rw [goldenForwardPlus_eq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hAA, hxA, hAx, hxx]
    norm_num
  have hminus_sq : (goldenDatum.windowSurface {0, 1}).pair
      goldenForwardMinus goldenForwardMinus = 10 := by
    rw [goldenForwardMinus_eq]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hAA, hxA, hAx, hxx]
    norm_num
  have hplus_A : (goldenDatum.windowSurface {0, 1}).pair
      goldenForwardPlus (goldenDatum.windowSurface {0, 1}).ample = 2 := by
    rw [goldenForwardPlus_eq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hAA, hxA]
    norm_num
  have hminus_A : (goldenDatum.windowSurface {0, 1}).pair
      goldenForwardMinus (goldenDatum.windowSurface {0, 1}).ample = 2 := by
    rw [goldenForwardMinus_eq]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hAA, hxA]
    norm_num
  have hcross : (goldenDatum.windowSurface {0, 1}).pair
      goldenForwardPlus goldenForwardMinus = -6 := by
    rw [goldenForwardPlus_eq, goldenForwardMinus_eq]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hAA, hxA, hAx, hxx]
    norm_num
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, hcross⟩
  refine ⟨by norm_num [goldenForwardPlus, goldenForwardMinus],
    by norm_num [goldenForwardPlus, goldenForwardMinus], fun k _ => ?_⟩
  simp only [goldenForwardPlus, goldenForwardMinus, Prod.snd_add, Pi.add_apply]
  split_ifs <;> norm_num

/-- **The Dual (Nef) Cone Obstruction on `goldenDatum`.** The primitive positive-square cycle
`goldenCounterexample = -H + 3V + 2Γ₀ - Γ₁` pairs nonnegatively with every cycle in
`graphCone {0, 1}` (`x · H = 0`, `x · V = 0`, `x · Γ₀ = 1`, `x · Γ₁ = 0`) and hence lies in
`dualCone (graphCone {0, 1})`. -/
theorem goldenCounterexample_mem_dualCone_graphCone :
    goldenCounterexample ∈
      (goldenDatum.windowSurface {0, 1}).dualCone (graphCone {0, 1}) := by
  rintro y ⟨hy1, hy2, hyd⟩
  have hq : goldenDatum.q = 5 := rfl
  have hN0 : goldenDatum.pointCount 0 = 0 := by
    rw [goldenDatum_pointCount_eq]; norm_num [goldenLucas]
  have hN1 : goldenDatum.pointCount 1 = 1 := by
    rw [goldenDatum_pointCount_eq]; norm_num [goldenLucas]
  have hy0 : 0 ≤ y.2.2 0 := hyd 0 (by simp)
  have hy1' : 0 ≤ y.2.2 1 := hyd 1 (by simp)
  have heq : (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample y = y.2.2 0 := by
    simp only [CurveDatum.windowSurface, CurveDatum.windowPair_apply, CurveDatum.windowPairFun,
      goldenCounterexample, CurveDatum.windowA, windowB, CurveDatum.windowGraph,
      CurveDatum.graphPair]
    rw [Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one]
    simp only [Finset.sum_pair zero_ne_one, Nat.dist_self, Nat.dist_zero_left, Nat.dist_zero_right]
    norm_num [hq, hN0, hN1]
    ring
  linarith

/-- Consequently, on `goldenDatum.windowSurface {0, 1}`, the dual (nef) cone of `graphCone {0, 1}`
violates `AmpleAxiom`. -/
theorem goldenDatum_dualCone_graphCone_not_ample :
    ¬ (goldenDatum.windowSurface {0, 1}).AmpleAxiom
        ((goldenDatum.windowSurface {0, 1}).dualCone (graphCone {0, 1})) := by
  intro hA
  obtain ⟨hH, hV, hxx⟩ := goldenCounterexample_violates_hodgeIndex
  have hxA : (goldenDatum.windowSurface {0, 1}).pair goldenCounterexample
      (goldenDatum.windowSurface {0, 1}).ample = 0 := by
    rw [(goldenDatum.windowSurface {0, 1}).pair_ample, hH, hV, add_zero]
  have h0 := hA goldenCounterexample goldenCounterexample_mem_dualCone_graphCone hxA
    goldenCounterexample
  linarith

/-- **`goldenDatum` has no ambient Bézout–Riemann–Roch realization.** There is no ambient vector
space `C_amb` with a bilinear pairing `pair_amb`, pairing-preserving linear map
`ι : SpanCycle →ₗ[ℝ] C_amb`, and Bézout–Riemann–Roch cone `E_amb ⊆ C_amb`. -/
theorem goldenDatum_no_ambient_bezout_riemannRoch
    {C_amb : Type*} [AddCommGroup C_amb] [Module ℝ C_amb]
    (pair_amb : C_amb →ₗ[ℝ] C_amb →ₗ[ℝ] ℝ)
    (ι : SpanCycle →ₗ[ℝ] C_amb)
    (hpair : ∀ x y : SpanCycle,
      pair_amb (ι x) (ι y) = (goldenDatum.windowSurface {0, 1}).pair x y)
    {E_amb : Set C_amb}
    (hRR : ∀ u : C_amb, 0 < pair_amb u u → u ∈ E_amb ∨ -u ∈ E_amb)
    (hBez : ∀ u ∈ E_amb, ∀ v ∈ E_amb, 0 ≤ pair_amb u v) :
    False := by
  have hH : (goldenDatum.windowSurface {0, 1}).HodgeIndex :=
    (goldenDatum.windowSurface {0, 1}).hodgeIndex_of_ambient_bezout_riemannRoch
      pair_amb ι hpair hRR hBez
  obtain ⟨h1, h2, h3⟩ := goldenCounterexample_violates_hodgeIndex
  have hle := hH goldenCounterexample h1 h2
  linarith

/-! ### 5. Application to `scalingSurface` over `ℤ`: Pole Subtraction in the Odd Sector and the
9-Way Forcing Equivalence -/

/-- On any test submodule `V ≤ realTests`, `coupledArithmeticCone V` satisfies `BezoutAxiom` on
`scalingSubsurface V` if and only if `(scalingSubsurface V).HodgeIndex` holds. -/
theorem coupledArithmeticCone_bezout_iff_hodgeIndex (V : Submodule ℝ realTests) :
    (scalingSubsurface V).BezoutAxiom (coupledArithmeticCone V) ↔
      (scalingSubsurface V).HodgeIndex := by
  rw [coupledArithmeticCone_eq_positiveCone]
  exact (scalingSubsurface V).hodgeIndex_iff_positiveCone_bezout.symm

/-- On any test submodule `V ≤ realTests`, `strictCoupledArithmeticCone V` satisfies `BezoutAxiom`
on `scalingSubsurface V` if and only if `(scalingSubsurface V).HodgeIndex` holds. -/
theorem strictCoupledArithmeticCone_bezout_iff_hodgeIndex (V : Submodule ℝ realTests) :
    (scalingSubsurface V).BezoutAxiom (strictCoupledArithmeticCone V) ↔
      (scalingSubsurface V).HodgeIndex := by
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact (scalingSubsurface V).hodgeIndex_iff_openPositiveCone_bezout.symm

/-- **The 9-Way Forcing Equivalence on the Scaling Surface of `ℤ`.** On `scalingSurface`, the
following statements are unconditionally equivalent (`List.TFAE`):
1. `RiemannHypothesis`;
2. `rightZeros zetaZeroConfig = ∅` (exact `100%` of the nontrivial zeros of `ζ` on the critical line);
3. `scalingSurface.HodgeIndex`;
4. `scalingSurface.BezoutAxiom scalingSurface.positiveCone` (forward light-cone Bézout positivity);
5. `scalingSurface.BezoutAxiom scalingSurface.openPositiveCone` (open forward light-cone Bézout
   positivity);
6. `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).HodgeIndex` (pole-cancelled odd-sector Hodge
   index at all degrees);
7. `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (coupledArithmeticCone (oddRealTestsAt r))`;
8. `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (strictCoupledArithmeticCone (oddRealTestsAt r))`;
9. All-aperture reflected prime–polar ledger allocation on `oddRealTestsAt r`. -/
theorem scalingSurface_forcing_tfae :
    List.TFAE
      [ RiemannHypothesis,
        rightZeros zetaZeroConfig = ∅,
        scalingSurface.HodgeIndex,
        scalingSurface.BezoutAxiom scalingSurface.positiveCone,
        scalingSurface.BezoutAxiom scalingSurface.openPositiveCone,
        ∀ r : ℝ, 0 < r → (scalingSubsurface (oddRealTestsAt r)).HodgeIndex,
        ∀ r : ℝ, 0 < r →
          (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
            (coupledArithmeticCone (oddRealTestsAt r)),
        ∀ r : ℝ, 0 < r →
          (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
            (strictCoupledArithmeticCone (oddRealTestsAt r)),
        ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
          reflectedPrimePolarCost (f.1 : ℝ → ℝ) r ≤
            surplusPool (aperturePlateau r R) (f.1 : ℝ → ℝ) +
              crossingPotentialTerm (aperturePlateau r R) (f.1 : ℝ → ℝ) +
              gaugeRemainder (aperturePlateau r R) (f.1 : ℝ → ℝ) ] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_rightZeros_zeta_eq_empty
  tfae_have 3 ↔ 1 := scalingSurface_hodgeIndex_iff
  tfae_have 3 ↔ 4 := scalingSurface.hodgeIndex_iff_positiveCone_bezout
  tfae_have 3 ↔ 5 := scalingSurface.hodgeIndex_iff_openPositiveCone_bezout
  tfae_have 2 ↔ 6 := rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex
  tfae_have 6 ↔ 7 := forall₂_congr fun r _ =>
    (coupledArithmeticCone_bezout_iff_hodgeIndex (oddRealTestsAt r)).symm
  tfae_have 6 ↔ 8 := forall₂_congr fun r _ =>
    (strictCoupledArithmeticCone_bezout_iff_hodgeIndex (oddRealTestsAt r)).symm
  tfae_have 2 ↔ 9 := rightZeros_zeta_eq_empty_iff_forall_odd_reflectedPrimePolarAllocation
  tfae_finish

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
