import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeStrictStability

/-!
# A finite free Hermite–Biehler theorem for genus-one canonical products

Let `(z_i)` be a countable family of nonzero points with `Σ 1/|z_i|² < ∞`, all in the closed upper
half-plane, with `Σ Im(1/z_i)` absolutely convergent, and let `a ∈ ℂ` satisfy the drift condition

`Im a + Σ_i Im(1/z_i) ≥ 0`.

**Theorem.** Every reversed Jensen polynomial of `g(w) = e^{aw} Π_i E₁(w/z_i)` has all its roots in
the closed lower half-plane.

The finite partial products are `e^{w(a + Σ_F 1/z_i)} Π_F (1 − w/z_i)`: the linear pieces have their
reversed Jensen roots `d/z_i` in `Im ≤ 0`, Walsh keeps their finite free product there, and the
exponential translates by `−(a + Σ_F 1/z_i)`. The Taylor coefficients converge and the polynomial
Hurwitz lemma passes the bound `Im ≤ −Im a − Σ_F Im(1/z_i)` to the limit. This is the finite free
form of the Pólya–Levin class; the Riemann case (R26) is the shifted canonical product of `Ξ`.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- The genus-one factor `E₁(w/z) = (1 − w/z) e^{w/z}` has Taylor series `(1 − X/z)·e^{X/z}`. -/
theorem taylorPS_weierstrassE1_div (z : ℂ) :
    taylorPS (fun w => weierstrassE1 (w / z)) =
      ((1 - C (1 / z) * X : ℂ[X]) : PowerSeries ℂ) * expSeries (1 / z) := by
  rw [show (fun w => weierstrassE1 (w / z)) =
      (fun w => (1 - C (1 / z) * X : ℂ[X]).eval w) * (fun w => Complex.exp ((1 / z) * w)) from
    funext fun w => by
      simp only [weierstrassE1, Pi.mul_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
      ring_nf,
    taylorPS_mul (Polynomial.differentiable _) (by fun_prop), taylorPS_polynomial, taylorPS_exp]

/-- The partial products `e^{aw} Π_F E₁(w/z_i)`. -/
def polyaPartialProduct {ι : Type*} (z : ι → ℂ) (a : ℂ) (F : Finset ι) (w : ℂ) : ℂ :=
  Complex.exp (a * w) * ∏ i ∈ F, weierstrassE1 (w / z i)

theorem taylorPS_polyaPartialProduct {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (a : ℂ)
    (F : Finset ι) :
    taylorPS (polyaPartialProduct z a F) =
      ((∏ i ∈ F, (1 - C (1 / z i) * X) : ℂ[X]) : PowerSeries ℂ) *
        expSeries (a + ∑ i ∈ F, 1 / z i) := by
  rw [show polyaPartialProduct z a F = (fun w => Complex.exp (a * w)) *
      (fun w => ∏ i ∈ F, weierstrassE1 (w / z i)) from rfl,
    taylorPS_mul (by fun_prop) (by unfold weierstrassE1; fun_prop), taylorPS_exp,
    taylorPS_prod F (fun i w => weierstrassE1 (w / z i)) (fun i => by unfold weierstrassE1; fun_prop),
    Finset.prod_congr rfl fun i _ => taylorPS_weierstrassE1_div (z i),
    Finset.prod_mul_distrib, prod_expSeries]
  rw [show ((∏ i ∈ F, (1 - C (1 / z i) * X) : ℂ[X]) : PowerSeries ℂ) =
      ∏ i ∈ F, ((1 - C (1 / z i) * X : ℂ[X]) : PowerSeries ℂ) by
    simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]]
  rw [mul_comm (expSeries a), mul_assoc, expSeries_add, add_comm]

theorem im_le_of_isRoot_jensenRev_polyaPartialProduct {ι : Type*} [DecidableEq ι] {z : ι → ℂ}
    (hz : ∀ i, 0 ≤ (z i).im) (a : ℂ) (F : Finset ι) {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (taylorPS (polyaPartialProduct z a F))).IsRoot x) :
    x.im ≤ -(a + ∑ i ∈ F, 1 / z i).im := by
  rw [taylorPS_polyaPartialProduct, mul_comm, jensenRev_expSeries_mul, IsRoot, eval_comp,
    eval_add, eval_X, eval_C] at hx
  have hr := im_le_zero_of_isRoot_jensenRev_prod_linear F (fun i => 1 / z i) (fun i _ => by
    rw [one_div, Complex.inv_im]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hz i)) (Complex.normSq_nonneg _)) hd hx
  rw [add_im] at hr
  linarith

/-- **Finite free Hermite–Biehler theorem for genus-one canonical products.** -/
theorem im_le_zero_of_isRoot_jensenRev_polya {ι : Type*} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, 0 ≤ (z i).im)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (him : Summable fun i => (1 / z i).im)
    {a : ℂ} (hdrift : 0 ≤ a.im + ∑' i, (1 / z i).im) (d : ℕ) {x : ℂ}
    (hx : (jensenRev d (taylorPS fun w => Complex.exp (a * w) *
      canonicalProductE1Indexed z w)).IsRoot x) : x.im ≤ 0 := by
  classical
  haveI : Countable ι := by
    have h := hsq.countable_support
    have hsupp : Function.support (fun i => 1 / ‖z i‖ ^ (2 : ℕ)) = Set.univ :=
      Set.eq_univ_of_forall fun i => by
        simp only [Function.mem_support, one_div, ne_eq, inv_eq_zero, pow_eq_zero_iff',
          norm_eq_zero, hz0 i, false_and, not_false_eq_true]
    rw [hsupp] at h
    exact Set.countable_univ_iff.1 h
  set g : ℂ → ℂ := fun w => Complex.exp (a * w) * canonicalProductE1Indexed z w
  have hprod := canonicalProductE1Indexed_hasProdLocallyUniformlyOn z hz0 hsq
  have hconv : TendstoLocallyUniformlyOn (fun F => polyaPartialProduct z a F) g atTop Set.univ := by
    have hP : TendstoLocallyUniformlyOn (fun (F : Finset ι) w => ∏ i ∈ F, weierstrassE1 (w / z i))
        (canonicalProductE1Indexed z) atTop Set.univ := hprod
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ] at hP ⊢
    intro K hKs hK
    obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn
      (by fun_prop : Continuous fun w => Complex.exp (a * w)).continuousOn
    set M := max M₀ 0
    have hM : ∀ w ∈ K, ‖Complex.exp (a * w)‖ ≤ M := fun w hw => (hM₀ w hw).trans (le_max_left _ _)
    have hM0 : 0 ≤ M := le_max_right _ _
    have hP' := hP K hKs hK
    rw [Metric.tendstoUniformlyOn_iff] at hP' ⊢
    intro ε hε
    filter_upwards [hP' (ε / (M + 1)) (by positivity)] with F hF w hw
    have h1 := hF w hw
    rw [dist_eq_norm] at h1 ⊢
    simp only [g, polyaPartialProduct]
    rw [← mul_sub, norm_mul]
    calc ‖Complex.exp (a * w)‖ * ‖canonicalProductE1Indexed z w - ∏ i ∈ F,
          weierstrassE1 (w / z i)‖ ≤ M * (ε / (M + 1)) :=
          mul_le_mul (hM w hw) h1.le (norm_nonneg _) hM0
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hdiff : ∀ F, Differentiable ℂ (polyaPartialProduct z a F) := fun F => by
    unfold polyaPartialProduct weierstrassE1; fun_prop
  have hcoeff : ∀ k, Tendsto (fun F => PowerSeries.coeff k (taylorPS (polyaPartialProduct z a F)))
      atTop (𝓝 (PowerSeries.coeff k (taylorPS g))) := fun k => by
    have h := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ hconv
      (Eventually.of_forall fun F => (hdiff F).differentiableOn) k (Set.mem_univ 0)
    simpa only [taylorPS, PowerSeries.coeff_mk] using h.div_const _
  have hg0 : PowerSeries.coeff 0 (taylorPS g) = 1 := by
    simp [taylorPS, g, canonicalProductE1Indexed, weierstrassE1_zero]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    rw [IsRoot, jensenRev_eq_sum] at hx
    simp [hg0] at hx
  obtain ⟨Fseq, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  have hL : jensenRev d (taylorPS g) ≠ 0 := jensenRev_ne_zero (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]; exact one_ne_zero)
  have hτ : Tendsto (fun n => -(a + ∑ i ∈ Fseq n, 1 / z i).im) atTop
      (𝓝 (-(a.im + ∑' i, (1 / z i).im))) := by
    have := (him.hasSum.comp hF).const_add a.im
    refine (this.neg).congr fun n => ?_
    simp only [Function.comp_def, add_im, Complex.im_sum]
  have hle := im_le_of_tendsto_coeff (P := fun n => jensenRev d (taylorPS
    (polyaPartialProduct z a (Fseq n)))) (fun n => natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _) hL (fun j => ?_) hτ
    (Eventually.of_forall fun n y hy => im_le_of_isRoot_jensenRev_polyaPartialProduct hz a
      (Fseq n) hd hy) hx
  · linarith
  · rcases le_or_gt j d with hj | hj
    · simp only [coeff_jensenRev d _ hj]
      exact ((hcoeff (d - j)).comp hF).mul_const _
    · simp only [coeff_jensenRev_of_lt d _ hj]
      exact tendsto_const_nhds

/-- **Genus-one entire functions.** If an entire function of order at most one has its Hadamard
factorization `f = e^{az+b} Π E₁(z/z_q)` with every zero in the closed upper half-plane, summable
`Σ Im(1/z_q)` and drift `Im a + Σ Im(1/z_q) ≥ 0`, then every root of every reversed Jensen
polynomial of `f` lies in the closed lower half-plane. -/
theorem im_le_zero_of_isRoot_jensenRev_genusOne {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hf0 : f 0 ≠ 0) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {a b : ℂ} (hfac : ∀ z, f z = Complex.exp (a * z + b) * OrderOneHadamard.hadamardProduct f z)
    (hz : ∀ q, 0 ≤ (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f q).im)
    (him : Summable fun q => (1 / GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f q).im)
    (hdrift : 0 ≤ a.im + ∑' q, (1 / GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f q).im)
    (d : ℕ) {x : ℂ} (hx : (jensenRev d (taylorPS f)).IsRoot x) : x.im ≤ 0 := by
  have hfun : f = fun w => Complex.exp b * (Complex.exp (a * w) *
      canonicalProductE1Indexed (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f) w) := by
    funext w
    rw [hfac w, OrderOneHadamard.hadamardProduct, ← mul_assoc, ← Complex.exp_add, add_comm b]
  have htay : taylorPS f = PowerSeries.C (Complex.exp b) * taylorPS (fun w => Complex.exp (a * w) *
      canonicalProductE1Indexed (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f) w) := by
    rw [show taylorPS f = taylorPS (fun w => Complex.exp b * (Complex.exp (a * w) *
      canonicalProductE1Indexed (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint f) w)) from
      congrArg taylorPS hfun]
    ext k
    simp only [taylorPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, iteratedDeriv_const_mul_field]
    ring
  rw [htay, jensenRev_C_mul, IsRoot, eval_mul, eval_C] at hx
  exact im_le_zero_of_isRoot_jensenRev_polya
    (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint_ne_zero hf hf0) hz
    (OrderOneHadamard.summable_inv_sq_zeroCopyPoint hK hf hf0 hbound) him hdrift d
    ((mul_eq_zero.1 hx).resolve_left (Complex.exp_ne_zero b))

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.im_le_zero_of_isRoot_jensenRev_polya
#print axioms FiniteFreeProbability.im_le_zero_of_isRoot_jensenRev_genusOne
