import GaloisForLFunctions.FiniteFreeProbability.KernelJensenRoots
import GaloisForLFunctions.FiniteFreeProbability.GenusOneStabilityClassification
import GaloisForLFunctions.FiniteFreeProbability.BackwardHeatJensenNonRealRootCount

/-!
# The bulk of the Jensen roots cannot see non-real zeros

For `τ > 0` the backward heat flow `H_{−τ}` of `Ξ` has infinitely many non-real zeros (Newman's conjecture,
proved in the corpus), and it is the transform of a hyperbolic kernel.

**Theorem.** For every `τ > 0`, with `N_d` the number of non-real roots of `R_d(H_{−τ})`:

* `H_{−τ}` has a non-real zero;
* `N_d/d → 0`: almost all roots of `R_d(H_{−τ})` are real;
* `N_d → ∞`: each non-real zero of `H_{−τ}` attracts a non-real root.

So the statement "almost all Jensen roots are real" holds for functions with non-real zeros: it cannot imply
RH, and neither can any argument that uses only `0 ≤ g ≤ Φ` and the size of `g`. `N_d = o(d)` is the bulk
statement; RH is the statement `N_d = 0`, and it is carried by the `o(d)` outliers.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

variable {g : ℝ → ℝ}

/-- The derivatives of the transform of a kernel are the transforms of its moments. -/
theorem iteratedDeriv_cosTransform (hg : SuperExpKernel g) (k : ℕ) :
    iteratedDeriv k (cosTransform g) = expTransform fun x => (g x : ℂ) * (I * x) ^ k := by
  have hcont : ∀ k : ℕ, Continuous fun x : ℝ => (g x : ℂ) * (I * x) ^ k := fun k => by
    have := hg.continuous
    fun_prop
  have hint : ∀ (k : ℕ) (c : ℝ), Integrable fun x : ℝ =>
      ‖(g x : ℂ) * (I * x) ^ k‖ * Real.exp (c * |x|) := fun k => by
    induction k with
    | zero =>
      intro c
      refine (hg.integrable_mul_exp c).congr (Eventually.of_forall fun x => ?_)
      simp only [pow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.nonneg x)]
    | succ k ih =>
      intro c
      have h := integrable_mul_poly (G := fun x : ℝ => (g x : ℂ) * (I * x) ^ k) ih (hcont k) c
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [pow_succ, mul_assoc]
  induction k with
  | zero =>
    funext z
    simp [cosTransform, expTransform]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [(hasDerivAt_expTransform (hcont k) (hint k) z).deriv]
    unfold expTransform
    congr 1
    funext x
    ring

/-- The reversed Jensen polynomials of the transform are those of the kernel. -/
theorem jensenRev_taylorPS_cosTransform (hg : SuperExpKernel g) (d : ℕ) :
    jensenRev d (taylorPS (cosTransform g)) = kernelJensen g d := by
  rw [jensenRev_eq_sum, kernelJensen, momentJensen]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hder : iteratedDeriv k (cosTransform g) 0 = I ^ k * (kernelMoment g k : ℂ) := by
    rw [iteratedDeriv_cosTransform hg, expTransform, kernelMoment, ← integral_complex_ofReal,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, mul_pow]
    push_cast
    ring
  have hdesc : (d.descFactorial k : ℂ) = (d.choose k : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [taylorPS, PowerSeries.coeff_mk, hder, hdesc]
  congr 1
  field_simp

theorem riemannHeat_neg_eq_cosTransform (τ : ℝ) :
    riemannHeat (-τ) = cosTransform fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2) := rfl

theorem jensenRev_taylorPS_riemannHeat_neg {τ : ℝ} (hτ : 0 ≤ τ) (d : ℕ) :
    jensenRev d (taylorPS (riemannHeat (-τ))) =
      kernelJensen (fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2)) d := by
  rw [riemannHeat_neg_eq_cosTransform]
  exact jensenRev_taylorPS_cosTransform (superExpKernel_mul_exp_neg_sq hτ) d

/-- **Almost all roots of `R_d(H_{−τ})` are real.** -/
theorem tendsto_card_nonreal_roots_riemannHeat_neg {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d (taylorPS (riemannHeat (-τ)))).roots.filter
        fun x => x.im ≠ 0) : ℝ) / d) atTop (𝓝 0) := by
  simp_rw [jensenRev_taylorPS_riemannHeat_neg hτ]
  exact (hyperbolicKernel_heat hτ).tendsto_card_nonreal_roots_div

/-- **Every non-real zero is seen, with distinct roots.** If `T` is a finite set of non-real zeros of
`Σ f_k u^k`, then for large `d` the polynomial `R_d(f)` has at least `|T|` roots `x` satisfying any property
implied by `Im x · Im z < 0` for `z ∈ T`. -/
theorem eventually_le_card_roots_of_zeros {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k)
    (hf0 : f 0 ≠ 0) {T : Finset ℂ} (hT : ∀ z ∈ T, ∑' k, f k * z ^ k = 0) (hne : ∀ z ∈ T, z.im ≠ 0)
    {p : ℂ → Prop} [DecidablePred p] (hp : ∀ z ∈ T, ∀ x : ℂ, x.im * z.im < 0 → p x) :
    ∀ᶠ d : ℕ in atTop, T.card ≤ Multiset.card ((jensenRev d (PowerSeries.mk f)).roots.filter p) := by
  -- a common radius: discs off the real axis and pairwise disjoint
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∀ z ∈ T, r < |z.im|) ∧ ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * r < ‖z - w‖ := by
    have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    refine (Filter.eventually_all_finset T).2 (fun z hz => ?_) |>.and
      ((Filter.eventually_all_finset T).2 fun z hz => (Filter.eventually_all_finset T).2
        fun w hw => ?_)
    · have him : 0 < |z.im| := abs_pos.2 (hne z hz)
      exact hr0.eventually (gt_mem_nhds him)
    · by_cases hzw : z = w
      · exact Eventually.of_forall fun _ h => absurd hzw h
      · have hpos : 0 < ‖z - w‖ / 2 := by
          have := norm_pos_iff.2 (sub_ne_zero.2 hzw)
          positivity
        filter_upwards [hr0.eventually (gt_mem_nhds hpos)] with r hr _
        linarith
  obtain ⟨r, ⟨hrT, hrdisj⟩, hrpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hrpos' : 0 < r := hrpos
  have hev : ∀ᶠ d : ℕ in atTop, ∀ z ∈ T, ∃ u ∈ ball z r, scaledJensen f d u = 0 :=
    (Filter.eventually_all_finset T).2 fun z hz =>
      eventually_exists_zero_scaledJensen hf hf0 (hT z hz) hrpos'
  filter_upwards [hev, eventually_gt_atTop 0] with d hd hdpos
  set P := jensenRev d (PowerSeries.mk f)
  have hP : P ≠ 0 := by
    have hc : PowerSeries.constantCoeff (PowerSeries.mk f) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
      exact hf0
    exact jensenRev_ne_zero hc
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hdpos.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  choose! u hu hu0 using hd
  have hne0 : ∀ z ∈ T, u z ≠ 0 := fun z hz h0 => by
    have h1 := hu0 z hz
    rw [h0, scaledJensen_zero] at h1
    exact hf0 h1
  have hsign : ∀ z ∈ T, 0 < (u z).im * z.im := fun z hz => by
    have hwz := hu z hz
    rw [mem_ball, dist_eq_norm] at hwz
    have h1 : |(u z - z).im| ≤ ‖u z - z‖ := Complex.abs_im_le_norm _
    rw [sub_im] at h1
    have h2 := abs_lt.1 (lt_of_le_of_lt h1 (hwz.trans (hrT z hz)))
    rcases lt_or_gt_of_ne (hne z hz) with hneg | hpos
    · rw [abs_of_neg hneg] at h2
      exact mul_pos_of_neg_of_neg (by linarith [h2.2]) hneg
    · rw [abs_of_pos hpos] at h2
      exact mul_pos (by linarith [h2.1]) hpos
  have hle : T.card ≤ (P.roots.toFinset.filter p).card := by
    refine Finset.card_le_card_of_injOn (fun z => (d : ℂ) / u z) (fun z hz => ?_)
      (fun z hz z' hz' h => ?_)
    · have hroot : P.IsRoot ((d : ℂ) / u z) := by
        have h := eval_jensenRev_div f hdpos (hne0 z hz)
        rw [hu0 z hz, mul_zero] at h
        exact h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Multiset.mem_toFinset]
      refine ⟨(mem_roots hP).2 hroot, hp z hz _ ?_⟩
      have hns : 0 < Complex.normSq (u z) := Complex.normSq_pos.2 (hne0 z hz)
      have him : ((d : ℂ) / u z).im = -((d : ℝ) * (u z).im / Complex.normSq (u z)) := by
        rw [Complex.div_im]
        simp only [natCast_im, zero_mul, natCast_re, zero_div, zero_sub]
      rw [him]
      have hprod := hsign z hz
      have : -((d : ℝ) * (u z).im / Complex.normSq (u z)) * z.im =
          -((d : ℝ) / Complex.normSq (u z) * ((u z).im * z.im)) := by ring
      rw [this]
      have : 0 < (d : ℝ) / Complex.normSq (u z) * ((u z).im * z.im) := by positivity
      linarith
    · have hue : u z = u z' := by
        have h' : (d : ℂ) / u z = (d : ℂ) / u z' := h
        have h1 := hne0 z hz
        have h2 := hne0 z' hz'
        have h3 := (div_eq_div_iff h1 h2).1 h'
        exact (mul_left_cancel₀ hdC h3).symm
      by_contra hzz
      have h1 := hu z hz
      have h2 := hu z' hz'
      rw [mem_ball, dist_eq_norm] at h1 h2
      have hdis := hrdisj z hz z' hz' hzz
      have htri : ‖z - z'‖ ≤ ‖u z - z‖ + ‖u z - z'‖ := by
        calc ‖z - z'‖ = ‖(u z - z') - (u z - z)‖ := by ring_nf
          _ ≤ ‖u z - z'‖ + ‖u z - z‖ := norm_sub_le _ _
          _ = _ := by ring
      rw [hue] at h1 htri
      linarith
  refine hle.trans ?_
  rw [← Multiset.toFinset_filter]
  exact Multiset.toFinset_card_le _

/-- **Every non-real zero is seen.** For `τ > 0` and every `M`, for all large `d`, `R_d(H_{−τ})` has at least
`M` non-real roots. -/
theorem eventually_le_card_nonreal_roots_riemannHeat_neg {τ : ℝ} (hτ : 0 < τ) (M : ℕ) :
    ∀ᶠ d : ℕ in atTop, M ≤ Multiset.card
      ((jensenRev d (taylorPS (riemannHeat (-τ)))).roots.filter fun x => x.im ≠ 0) := by
  set F := riemannHeat (-τ)
  have hFd : Differentiable ℂ F := (superExpKernel_mul_exp_neg_sq hτ.le).differentiable
  have hsum : ∀ u, HasSum (fun k => taylorCoeff F k * u ^ k) (F u) := hasSum_taylorCoeff hFd
  have hf0 : taylorCoeff F 0 ≠ 0 := by
    have h := (hsum 0).tsum_eq
    rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])] at h
    simp only [pow_zero, mul_one] at h
    rw [h]
    exact riemannHeat_neg_zero_ne hτ.le
  obtain ⟨T, hTs, hTcard⟩ := (riemannHeat_neg_nonreal_zeros_infinite hτ).exists_subset_card_eq M
  have h := eventually_le_card_roots_of_zeros (T := T)
    (summable_norm_mul_pow_of_summable fun u => (hsum u).summable) hf0
    (fun z hz => by rw [(hsum z).tsum_eq]; exact (hTs hz).1) (fun z hz => (hTs hz).2)
    (p := fun x => x.im ≠ 0) (fun z _ x hx h0 => by rw [h0, zero_mul] at hx; exact lt_irrefl _ hx)
  rw [mk_taylorCoeff, hTcard] at h
  exact h

/-- **The bulk is blind.** For `τ > 0`: `H_{−τ}` has a non-real zero, the proportion of non-real roots of
`R_d(H_{−τ})` tends to `0`, and their number tends to infinity. -/
theorem bulk_blind_riemannHeat_neg {τ : ℝ} (hτ : 0 < τ) :
    (∃ z : ℂ, riemannHeat (-τ) z = 0 ∧ z.im ≠ 0) ∧
    Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d (taylorPS (riemannHeat (-τ)))).roots.filter
        fun x => x.im ≠ 0) : ℝ) / d) atTop (𝓝 0) ∧
    ∀ M : ℕ, ∀ᶠ d : ℕ in atTop, M ≤ Multiset.card
      ((jensenRev d (taylorPS (riemannHeat (-τ)))).roots.filter fun x => x.im ≠ 0) :=
  ⟨not_real_rooted_of_neg (neg_lt_zero.2 hτ), tendsto_card_nonreal_roots_riemannHeat_neg hτ.le,
    eventually_le_card_nonreal_roots_riemannHeat_neg hτ⟩

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.bulk_blind_riemannHeat_neg
