import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The projection formula and the regulator anomaly

The power map `[t] : z ↦ z^t` is the Hecke correspondence of the characteristic circle. Its fibre
over `z^t` is the coset `μ_t · z`, and the factorization `z^t − w^t = ∏_{ω ∈ μ_t} (z − ω w)` makes it
a correspondence for the archimedean pairing.

* **Projection formula** (`sum_log_norm_sub_mul_nthRoots`): `Σ_{ω ∈ μ_t} log |z − ω w| = log |z^t − w^t|`.
  Pairing a point with a fibre of `[t]` is pairing the images.
* **Regularized projection formula** (`sum_circleKernel_fibre`): for the Abel kernel
  `k_r(z, w) = −log |1 − r z w̄|`, `Σ_{ω ∈ μ_t} k_r(ω z, w) = k_{r^t}(z^t, w^t)`. The correspondence
  maps the regulator `r` to `r^t`. For cycles (`cycleEnergy_pullback`): the energy of the pullback of
  a cycle at radius `r` is `t` times the energy of the cycle at radius `r^t`.
* **The regulator anomaly** (`tendsto_log_one_sub_pow_sub_log_one_sub`,
  `tendsto_renormalized_pullback_sub`): `(1 − r^t)/(1 − r) → t`, so the counterterm `log(1/(1 − r))`
  is not preserved: the renormalized energy of a pulled-back cycle is `t` times the renormalized
  energy of the cycle minus `t log t` times its mass. The anomaly per point is `log t`, the logarithm
  of the number of points of `ker [t] = μ_t`; it is the log-discriminant of the fibre per point
  (`Σ_{ω ≠ 1} log |1 − ω| = log t`, AET `sum_log_norm_one_sub_nthRoots`).
-/

noncomputable section

open Finset Polynomial Complex Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### Factorizations over a fibre -/

/-- `∏_{ω ∈ μ_t} (z − ω w) = z^t − w^t`. -/
theorem prod_sub_mul_nthRoots {t : ℕ} (ht : 0 < t) (z w : ℂ) :
    ∏ ω ∈ nthRootsFinset t (1 : ℂ), (z - ω * w) = z ^ t - w ^ t := by
  have hζ := Complex.isPrimitiveRoot_exp t ht.ne'
  have h := congrArg (eval z) (X_pow_sub_C_eq_prod hζ ht (rfl : w ^ t = w ^ t))
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
  rw [h, nthRootsFinset_eq_image ht hζ, prod_image fun i hi j hj hij =>
    hζ.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij]

/-- `∏_{ω ∈ μ_t} (1 − ω x) = 1 − x^t`. -/
theorem prod_one_sub_mul_nthRoots {t : ℕ} (ht : 0 < t) (x : ℂ) :
    ∏ ω ∈ nthRootsFinset t (1 : ℂ), (1 - ω * x) = 1 - x ^ t := by
  rw [prod_sub_mul_nthRoots ht, one_pow]

theorem card_nthRoots_one {t : ℕ} (ht : 0 < t) : (nthRootsFinset t (1 : ℂ)).card = t :=
  (Complex.isPrimitiveRoot_exp t ht.ne').card_nthRootsFinset

theorem pow_eq_one_of_mem_nthRoots {t : ℕ} (ht : 0 < t) {ω : ℂ}
    (hω : ω ∈ nthRootsFinset t (1 : ℂ)) : ω ^ t = 1 :=
  (mem_nthRootsFinset ht 1).mp hω

/-! ### The projection formula -/

/-- **The projection formula.** If `z^t ≠ w^t`, the archimedean pairing of `z` with the fibre `μ_t w`
of `[t]` is the pairing of the images: `Σ_{ω ∈ μ_t} log |z − ω w| = log |z^t − w^t|`. -/
theorem sum_log_norm_sub_mul_nthRoots {t : ℕ} (ht : 0 < t) {z w : ℂ} (h : z ^ t ≠ w ^ t) :
    ∑ ω ∈ nthRootsFinset t (1 : ℂ), Real.log ‖z - ω * w‖ = Real.log ‖z ^ t - w ^ t‖ := by
  have hprod := prod_sub_mul_nthRoots ht z w
  have hne : ∀ ω ∈ nthRootsFinset t (1 : ℂ), ‖z - ω * w‖ ≠ 0 := by
    intro ω hω h0
    rw [norm_eq_zero] at h0
    exact sub_ne_zero.mpr h (hprod ▸ prod_eq_zero hω h0)
  rw [← Real.log_prod hne, ← norm_prod, hprod]

/-! ### The regularized pairing and its projection formula -/

/-- The Abel-regularized archimedean pairing `k_r(z, w) = −log |1 − r z w̄|` of two points. -/
def circleKernel (r : ℝ) (z w : ℂ) : ℝ := -Real.log ‖1 - (r : ℂ) * (z * conj w)‖

theorem circleKernel_ofReal_pow (r : ℝ) (t : ℕ) (z w : ℂ) :
    circleKernel (r ^ t) (z ^ t) (w ^ t) = -Real.log ‖1 - ((r : ℂ) * (z * conj w)) ^ t‖ := by
  simp only [circleKernel, map_pow, mul_pow, Complex.ofReal_pow]

/-- **Regularized projection formula.** On the closed disc, the Abel pairing of the fibre `μ_t z`
with `w` at radius `r` is the pairing of `z^t` with `w^t` at radius `r^t`. -/
theorem sum_circleKernel_fibre {t : ℕ} (ht : 0 < t) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∑ ω ∈ nthRootsFinset t (1 : ℂ), circleKernel r (ω * z) w =
      circleKernel (r ^ t) (z ^ t) (w ^ t) := by
  set x : ℂ := (r : ℂ) * (z * conj w)
  have hx : ‖x‖ < 1 := by
    have : ‖x‖ = r * (‖z‖ * ‖w‖) := by
      simp [x, Complex.norm_real, Real.norm_of_nonneg hr0]
    rw [this]
    calc r * (‖z‖ * ‖w‖) ≤ r * 1 :=
          mul_le_mul_of_nonneg_left (mul_le_one₀ hz (norm_nonneg w) hw) hr0
      _ < 1 := by linarith
  have hterm : ∀ ω ∈ nthRootsFinset t (1 : ℂ), circleKernel r (ω * z) w =
      -Real.log ‖1 - ω * x‖ := by
    intro ω _
    simp only [circleKernel, x]
    ring_nf
  have hne : ∀ ω ∈ nthRootsFinset t (1 : ℂ), ‖1 - ω * x‖ ≠ 0 := by
    intro ω hω h0
    have hωn : ‖ω‖ = 1 := norm_eq_one_of_mem_nthRoots ht hω
    have : ‖ω * x‖ < 1 := by rw [norm_mul, hωn, one_mul]; exact hx
    rw [norm_eq_zero, sub_eq_zero] at h0
    rw [← h0, norm_one] at this
    exact lt_irrefl _ this
  rw [sum_congr rfl hterm, sum_neg_distrib, ← Real.log_prod hne, ← norm_prod,
    prod_one_sub_mul_nthRoots ht, circleKernel_ofReal_pow]

/-! ### Cycles -/

variable {ι : Type*}

/-- The Abel energy `Σ_{i,j} x_i x_j k_r(z_i, z_j)` of the weighted point cycle `Σ x_i δ_{z_i}`. -/
def cycleEnergy (r : ℝ) (s : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, x i * x j * circleKernel r (z i) (z j)

/-- The pullback of `Σ x_i δ_{z_i^t}` under `[t]`: the cycle `Σ_i x_i Σ_{ω ∈ μ_t} δ_{ω z_i}`. -/
def pullbackPoint (z : ι → ℂ) (p : ι × ℂ) : ℂ := p.2 * z p.1

/-- **The pullback multiplies the energy by the degree and moves the regulator.** For points on the
closed disc, the energy at radius `r` of the pulled-back cycle is `t` times the energy at radius
`r^t` of the cycle of images. -/
theorem cycleEnergy_pullback {t : ℕ} (ht : 0 < t) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset ι) {z : ι → ℂ} (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) (x : ι → ℝ) :
    cycleEnergy r (s ×ˢ nthRootsFinset t (1 : ℂ)) (pullbackPoint z) (fun p => x p.1) =
      t * cycleEnergy (r ^ t) s (fun i => z i ^ t) x := by
  simp only [cycleEnergy, pullbackPoint, sum_product, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  -- the inner fibre over `ω'` reduces to radius `r^t`
  have hfib : ∀ ω' ∈ nthRootsFinset t (1 : ℂ),
      ∑ ω ∈ nthRootsFinset t (1 : ℂ), x i * x j * circleKernel r (ω * z i) (ω' * z j) =
        x i * x j * circleKernel (r ^ t) (z i ^ t) (z j ^ t) := by
    intro ω' hω'
    have hω'n : ‖ω' * z j‖ ≤ 1 := by
      rw [norm_mul, norm_eq_one_of_mem_nthRoots ht hω', one_mul]; exact hz j hj
    rw [← mul_sum, sum_circleKernel_fibre ht hr0 hr1 (hz i hi) hω'n, mul_pow,
      pow_eq_one_of_mem_nthRoots ht hω', one_mul]
  rw [sum_comm, sum_congr rfl hfib, sum_const, card_nthRoots_one ht, nsmul_eq_mul]

/-! ### The regulator anomaly -/

/-- **The regulator anomaly.** `log(1 − r^t) − log(1 − r) → log t` as `r → 1⁻`: the correspondence
`[t]` shifts the counterterm `log(1/(1 − r))` by `log t = log #ker [t]`. -/
theorem tendsto_log_one_sub_pow_sub_log_one_sub {t : ℕ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => Real.log (1 - r ^ t) - Real.log (1 - r)) (𝓝[<] 1)
      (𝓝 (Real.log t)) := by
  have hgeom : Tendsto (fun r : ℝ => ∑ i ∈ range t, r ^ i) (𝓝[<] 1) (𝓝 (t : ℝ)) := by
    have hc : Continuous (fun r : ℝ => ∑ i ∈ range t, r ^ i) := by fun_prop
    have := hc.tendsto 1
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlog := (Real.continuousAt_log (Nat.cast_ne_zero.mpr ht.ne')).tendsto.comp hgeom
  refine hlog.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have h1r : 0 < 1 - r := by linarith [hr.2]
  have hpos : 0 < ∑ i ∈ range t, r ^ i :=
    sum_pos (fun i _ => pow_pos hr.1 i) (nonempty_range_iff.mpr ht.ne')
  have hfac : 1 - r ^ t = (∑ i ∈ range t, r ^ i) * (1 - r) := by
    have := geom_sum_mul r t
    linarith
  simp only [Function.comp, hfac, Real.log_mul hpos.ne' h1r.ne']
  ring

/-- **The renormalized anomaly of a pullback.** For points on the closed disc, the renormalized
energy of the pulled-back cycle (counterterm `log(1/(1 − r))` per point of mass `x_i²`) differs from
`t` times the renormalized energy of the cycle of images by `−t log t Σ x_i²` in the limit. -/
theorem tendsto_renormalized_pullback_sub {t : ℕ} (ht : 0 < t) (s : Finset ι) {z : ι → ℂ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) (x : ι → ℝ) :
    Tendsto (fun r : ℝ =>
        (cycleEnergy r (s ×ˢ nthRootsFinset t (1 : ℂ)) (pullbackPoint z) (fun p => x p.1) +
            Real.log (1 - r) * ∑ p ∈ s ×ˢ nthRootsFinset t (1 : ℂ), x p.1 ^ 2) -
          t * (cycleEnergy (r ^ t) s (fun i => z i ^ t) x +
            Real.log (1 - r ^ t) * ∑ i ∈ s, x i ^ 2)) (𝓝[<] 1)
      (𝓝 (-((t : ℝ) * Real.log t * ∑ i ∈ s, x i ^ 2))) := by
  have hmass : ∑ p ∈ s ×ˢ nthRootsFinset t (1 : ℂ), x p.1 ^ 2 = t * ∑ i ∈ s, x i ^ 2 := by
    rw [sum_product]
    simp only [sum_const, card_nthRoots_one ht, nsmul_eq_mul, ← mul_sum]
  have hlim := (tendsto_log_one_sub_pow_sub_log_one_sub ht).const_mul
    (-((t : ℝ) * ∑ i ∈ s, x i ^ 2))
  rw [show -((t : ℝ) * Real.log t * ∑ i ∈ s, x i ^ 2) =
    -((t : ℝ) * ∑ i ∈ s, x i ^ 2) * Real.log t by ring]
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  rw [cycleEnergy_pullback ht hr.1.le hr.2 s hz x, hmass]
  ring
