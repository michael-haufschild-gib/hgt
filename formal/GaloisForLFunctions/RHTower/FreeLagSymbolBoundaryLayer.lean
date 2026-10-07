import GaloisForLFunctions.RHTower.FreeLagTraceCertificateObstruction

/-!
# The boundary layer of the free-lag all-prime symbol

Let `S_a(ξ) = W(ξ) - 2 Σ_{2 ≤ n ≤ e^{2a}} Λ(n) n^{-1/2} (cos(2π log n ξ) - cos(4π a ξ))` be the
all-prime restricted Weil symbol with the free-lag correction, and `R_a` the optimal two-pole
residual.  On the frequency scale `ξ = t/(4πa)`:

* `a e^{-a} S_a(t/(4πa)) → -4 t sin t`, uniformly for `t` in compact sets
  (`tendstoUniformlyOn_scaled_freeLagSymbol`);
* `R_a(ω)/(2a) → 1`, uniformly in `ω` (`tendstoUniformly_optimalResidual_div`).

So at aperture `a` the symbol has the exact profile `-(e^a/a)·4t sin t` on the scale `1/a`, and
the pole-vanishing plane waves keep their full mass `2a` there.

**Mechanism.**  The prime number theorem gives `Σ_{n ≤ x} Λ(n)/√n = 2√x + o(√x)`
(`tendsto_sum_vonMangoldt_div_sqrt`) by Abel summation, so the prime mass `M₀(b)` is `~ 2e^b`.  The
layer-cake identity `M₁(a) = ∫₀^{2a} M₀(s/2) ds` for the hinge moment
`M₁(a) = Σ Λ(n) n^{-1/2}(2a - log n)` then gives `M₁(a) ~ 4e^a` (`tendsto_primeHinge_div_exp`).
With `h_n = (t/2a)(2a - log n)` the argument of each prime cosine is `t - h_n`, and
`|cos(t - h) - cos t - h sin t| ≤ (3/2)h²` (`abs_cos_sub_sub_cos_sub_mul_sin_le`).  Hence
`S_a(t/(4πa)) = W - (t/a) sin t·M₁(a) + E` with `|E| ≤ (3t²/4a²) M₂(a)`, and `M₂(a) ≤ 16C e^a`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.FreeLagTrace

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The prime number theorem with the weight `n^{-1/2}` -/

theorem chebyshevPsiReal_eq_psi (x : ℝ) : chebyshevPsiReal x = Chebyshev.psi x := by
  rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
  congr 1
  ext n
  simp

/-- `ψ(x)/x → 1`. -/
theorem tendsto_psi_div : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  tendsto_chebyshevPsiReal_div.congr fun x => by rw [chebyshevPsiReal_eq_psi]

/-- For every `ε > 0` there is `B ≥ 0` with `|ψ(t) - t| ≤ εt + B` for all `t ≥ 0`. -/
theorem exists_abs_psi_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ ε * t + B := by
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.mp tendsto_psi_div ε hε
  set Y₁ := max Y 1 with hY₁
  have hY₁1 : 1 ≤ Y₁ := le_max_right _ _
  have hB : 0 ≤ Chebyshev.psi Y₁ + Y₁ := by linarith [Chebyshev.psi_nonneg Y₁]
  refine ⟨Chebyshev.psi Y₁ + Y₁, hB, fun t ht => ?_⟩
  by_cases htY : Y₁ ≤ t
  · have ht0 : 0 < t := by linarith
    have hd := hY t (le_trans (le_max_left _ _) htY)
    rw [Real.dist_eq] at hd
    have hval : Chebyshev.psi t - t = (Chebyshev.psi t / t - 1) * t := by field_simp
    rw [hval, abs_mul, abs_of_pos ht0]
    have := mul_le_mul_of_nonneg_right hd.le ht0.le
    nlinarith
  · have htY' : t ≤ Y₁ := (lt_of_not_ge htY).le
    have h1 : Chebyshev.psi t ≤ Chebyshev.psi Y₁ := Chebyshev.psi_mono htY'
    have h2 := Chebyshev.psi_nonneg t
    rw [abs_le]
    constructor <;> nlinarith

private theorem rpow_neg_three_halves_mul {t : ℝ} (ht : 0 < t) :
    t ^ (-(1 / 2 : ℝ) - 1) * t = t ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_add_one ht.ne']
  ring_nf

private theorem continuousOn_rpow_Icc (r : ℝ) (x : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ r) (Icc 1 x) := fun t ht =>
  (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt

private theorem integrableOn_rpow_Ioc (r : ℝ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ r) (Ioc 1 x) :=
  ((continuousOn_rpow_Icc r x).integrableOn_Icc).mono_set Ioc_subset_Icc_self

private theorem integrableOn_rpow_mul_psi (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) (Ioc 1 x) := by
  refine Integrable.mono' (g := fun _ => Chebyshev.psi x) (integrableOn_const (by simp))
    (((continuousOn_rpow_Icc _ x).aestronglyMeasurable measurableSet_Icc).mono_set
      Ioc_subset_Icc_self |>.mul Chebyshev.psi_mono.measurable.aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : t ^ (-(1 / 2 : ℝ) - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)
  have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn (Chebyshev.psi_nonneg t))]
  calc t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t ≤ 1 * Chebyshev.psi t :=
        mul_le_mul_of_nonneg_right h1 (Chebyshev.psi_nonneg t)
    _ ≤ Chebyshev.psi x := by rw [one_mul]; exact Chebyshev.psi_mono ht.2

private theorem integral_rpow_neg_half {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt x - 2 := by
  rw [← intervalIntegral.integral_of_le hx, integral_rpow (Or.inl (by norm_num)),
    Real.sqrt_eq_rpow, Real.one_rpow]
  norm_num
  ring

private theorem integral_rpow_neg_three_halves {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) = 2 - 2 * x ^ (-(1 / 2 : ℝ)) := by
  have hnot : (0 : ℝ) ∉ uIcc 1 x := by
    rw [uIcc_of_le hx]; intro h; linarith [h.1]
  rw [← intervalIntegral.integral_of_le hx,
    integral_rpow (Or.inr ⟨by norm_num, hnot⟩), Real.one_rpow]
  norm_num
  ring

/-- **`Σ_{n ≤ x} Λ(n)/√n ~ 2√x`.** -/
theorem tendsto_sum_vonMangoldt_div_sqrt :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.sqrt n) / Real.sqrt x) atTop
      (𝓝 2) := by
  -- the endpoint term
  have hA : Tendsto (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Chebyshev.psi x / Real.sqrt x) atTop
      (𝓝 1) := by
    refine tendsto_psi_div.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have e : x ^ (-(1 / 2 : ℝ)) / x ^ (1 / 2 : ℝ) = x⁻¹ := by
      rw [← Real.rpow_sub hx, ← Real.rpow_neg_one]
      norm_num
    rw [hs, mul_div_right_comm, e, div_eq_mul_inv, mul_comm]
  -- the integral term
  have hB : Tendsto (fun x : ℝ =>
      ((1 / 2) * ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) / Real.sqrt x) atTop
      (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨B, hB0, hB⟩ := exists_abs_psi_sub_le (half_pos hε)
    -- eventually `(B + 1)/√x < ε/2`
    have hev : ∀ᶠ x : ℝ in atTop, (B + 1) / Real.sqrt x < ε / 2 := by
      have ht : Tendsto (fun x : ℝ => (B + 1) / Real.sqrt x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop)
      exact ht (Iio_mem_nhds (half_pos hε))
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
    refine ⟨max X₀ 1, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := by linarith
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hint_f := integrableOn_rpow_mul_psi x
    have hint_g : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 1 x) :=
      integrableOn_rpow_Ioc _ x
    have hint_h : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1)) (Ioc 1 x) :=
      integrableOn_rpow_Ioc _ x
    -- `(1/2) ∫ t^{-3/2} ψ - (√x - 1) = (1/2) ∫ t^{-3/2} (ψ - t)`
    have hdiff : (1 / 2) * (∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) -
        (Real.sqrt x - 1) = (1 / 2) * ∫ t in Ioc 1 x,
          (t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t - t ^ (-(1 / 2 : ℝ))) := by
      rw [integral_sub hint_f hint_g, integral_rpow_neg_half hx1]
      ring
    have hbound : |∫ t in Ioc 1 x,
        (t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t - t ^ (-(1 / 2 : ℝ)))| ≤
        ∫ t in Ioc 1 x, (ε / 2 * t ^ (-(1 / 2 : ℝ)) + B * t ^ (-(1 / 2 : ℝ) - 1)) := by
      rw [← Real.norm_eq_abs]
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine setIntegral_mono_on (hint_f.sub hint_g).norm
        ((hint_g.const_mul _).add (hint_h.const_mul _)) measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
      have hval : t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t - t ^ (-(1 / 2 : ℝ)) =
          t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - t) := by
        rw [mul_sub, rpow_neg_three_halves_mul ht0]
      rw [Real.norm_eq_abs, hval, abs_mul, abs_of_nonneg hrnn]
      calc t ^ (-(1 / 2 : ℝ) - 1) * |Chebyshev.psi t - t| ≤
            t ^ (-(1 / 2 : ℝ) - 1) * (ε / 2 * t + B) :=
            mul_le_mul_of_nonneg_left (hB t ht0.le) hrnn
        _ = ε / 2 * t ^ (-(1 / 2 : ℝ)) + B * t ^ (-(1 / 2 : ℝ) - 1) := by
            rw [mul_add, ← mul_assoc, mul_comm (t ^ (-(1 / 2 : ℝ) - 1)) (ε / 2), mul_assoc,
              rpow_neg_three_halves_mul ht0]
            ring
    have heval : ∫ t in Ioc 1 x, (ε / 2 * t ^ (-(1 / 2 : ℝ)) + B * t ^ (-(1 / 2 : ℝ) - 1)) =
        ε / 2 * (2 * Real.sqrt x - 2) + B * (2 - 2 * x ^ (-(1 / 2 : ℝ))) := by
      rw [integral_add (hint_g.const_mul _) (hint_h.const_mul _), integral_const_mul,
        integral_const_mul, integral_rpow_neg_half hx1, integral_rpow_neg_three_halves hx1]
    have hxr : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hkey : |(1 / 2) * (∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) -
        Real.sqrt x| ≤ ε / 2 * Real.sqrt x + B + 1 := by
      set J := ∫ t in Ioc 1 x, (t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t - t ^ (-(1 / 2 : ℝ)))
        with hJ
      have h1 : (1 / 2) * (∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) -
          Real.sqrt x = (1 / 2) * J - 1 := by
        rw [← hdiff]; ring
      rw [h1]
      have hJb : |J| ≤ ε / 2 * (2 * Real.sqrt x - 2) + B * (2 - 2 * x ^ (-(1 / 2 : ℝ))) := by
        rw [← heval]; exact hbound
      rw [abs_le] at hJb ⊢
      constructor <;> nlinarith
    rw [Real.dist_eq]
    have hval : ((1 / 2) * ∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) * Chebyshev.psi t) /
        Real.sqrt x - 1 = ((1 / 2) * (∫ t in Ioc 1 x, t ^ (-(1 / 2 : ℝ) - 1) *
          Chebyshev.psi t) - Real.sqrt x) / Real.sqrt x := by
      field_simp
    rw [hval, abs_div, abs_of_pos hsx, div_lt_iff₀ hsx]
    have hX := hX₀ x (le_trans (le_max_left _ _) hx)
    rw [div_lt_iff₀ hsx] at hX
    linarith
  have h := hA.add hB
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
  refine h.congr fun x => ?_
  rw [sum_vonMangoldt_div_sqrt_eq x, add_div]

/-! ## The prime mass and the hinge moment -/

private theorem primeMass_eq_sum_Icc_zero (b : ℝ) :
    primeMass b = ∑ n ∈ Finset.Icc 0 ⌊Real.exp (2 * b)⌋₊, Λ n / Real.sqrt n := by
  unfold primeMass primeCutoff
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
  · rw [Finset.mem_Icc] at hn ⊢
    omega
  · rw [Finset.mem_Icc] at hn hn'
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp

/-- **`M₀(b) ~ 2e^b`.** -/
theorem tendsto_primeMass_div_exp :
    Tendsto (fun b : ℝ => primeMass b / Real.exp b) atTop (𝓝 2) := by
  have hexp : Tendsto (fun b : ℝ => Real.exp (2 * b)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine (tendsto_sum_vonMangoldt_div_sqrt.comp hexp).congr fun b => ?_
  simp only [Function.comp, primeMass_eq_sum_Icc_zero]
  rw [show 2 * b = b + b by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos b).le]

private theorem primeMass_half' (s : ℝ) :
    primeMass (s / 2) = ∑ n ∈ Finset.Icc 2 ⌊Real.exp s⌋₊, Λ n / Real.sqrt n := by
  simp only [primeMass, primeCutoff, show 2 * (s / 2) = s by ring]

private theorem weight_nonneg' (n : ℕ) : 0 ≤ Λ n / Real.sqrt n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem monotone_primeMass_half : Monotone fun s : ℝ => primeMass (s / 2) := by
  intro s t hst
  simp only [primeMass_half']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => weight_nonneg' n
  exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (Real.exp_le_exp.mpr hst))

/-- One layer: `2a - L = ∫₀^{2a} 1[L ≤ s] ds` for `0 ≤ L ≤ 2a`. -/
private theorem layer_integral_one {a L : ℝ} (hL : 0 ≤ L) (hLa : L ≤ 2 * a) :
    ∫ s in (0 : ℝ)..(2 * a), (Ici L).indicator (fun _ => (1 : ℝ)) s = 2 * a - L := by
  have h0 : (0 : ℝ) ≤ 2 * a := hL.trans hLa
  rw [intervalIntegral.integral_of_le h0, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : (Ici L ∩ Ioc 0 (2 * a) : Set ℝ) =ᵐ[volume] (Ioc L (2 * a) : Set ℝ) := by
    rcases hL.eq_or_lt with hL0 | hL0
    · subst hL0
      have : Ici (0 : ℝ) ∩ Ioc 0 (2 * a) = Ioc 0 (2 * a) := by
        ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc]; constructor
        · rintro ⟨_, h⟩; exact h
        · rintro h; exact ⟨h.1.le, h⟩
      rw [this]
    · have : Ici L ∩ Ioc 0 (2 * a) = Icc L (2 * a) := by
        ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]; constructor
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hL0.trans_le h1, h2⟩
      rw [this]
      exact Ioc_ae_eq_Icc.symm
  rw [setIntegral_congr_set hset, setIntegral_const, Real.volume_real_Ioc_of_le hLa, smul_eq_mul,
    mul_one]

/-- **Layer-cake identity for the hinge moment.**  `M₁(a) = ∫₀^{2a} M₀(s/2) ds`. -/
theorem primeHinge_eq_layerCake {a : ℝ} (ha : 0 ≤ a) :
    primeHinge a = ∫ s in (0 : ℝ)..(2 * a), primeMass (s / 2) := by
  have hcut : ∀ s ∈ Icc (0 : ℝ) (2 * a), primeMass (s / 2) =
      ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) s := by
    intro s hs
    rw [primeMass_half']
    have hsub : Finset.Icc 2 ⌊Real.exp s⌋₊ ⊆ Finset.Icc 2 (primeCutoff a) := by
      apply Finset.Icc_subset_Icc le_rfl
      exact Nat.floor_le_floor (Real.exp_le_exp.mpr hs.2)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hle : Real.log n ≤ s := by
        have h1 : (n : ℝ) ≤ Real.exp s :=
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (Real.exp_pos s).le)
        calc Real.log n ≤ Real.log (Real.exp s) := Real.log_le_log hnpos h1
          _ = s := Real.log_exp s
      rw [indicator_of_mem (show s ∈ Ici (Real.log n) from hle), mul_one]
    · intro n hn hn'
      have hnot : ¬ Real.log n ≤ s := by
        intro hle
        apply hn'
        rw [Finset.mem_Icc] at hn ⊢
        refine ⟨hn.1, Nat.le_floor ?_⟩
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
          _ ≤ Real.exp s := Real.exp_le_exp.mpr hle
      rw [indicator_of_notMem (show s ∉ Ici (Real.log n) from hnot), mul_zero]
  have h0 : (0 : ℝ) ≤ 2 * a := by linarith
  have hEq : ∫ s in (0 : ℝ)..(2 * a), primeMass (s / 2) =
      ∫ s in (0 : ℝ)..(2 * a), ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le h0] at hs
      exact hcut s hs
  rw [hEq, intervalIntegral.integral_finsetSum]
  · unfold primeHinge
    refine Finset.sum_congr rfl fun n hn => ?_
    have hlog0 : 0 ≤ Real.log n := by
      rw [Finset.mem_Icc] at hn
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    rw [intervalIntegral.integral_const_mul,
      layer_integral_one hlog0 (log_le_two_mul_of_mem hn)]
  · intro n _
    refine IntervalIntegrable.const_mul ?_ _
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr ?_
    exact ((continuous_const.integrableOn_Icc (a := 0) (b := 2 * a)).mono_set
      Ioc_subset_Icc_self).indicator measurableSet_Ici

private theorem integral_two_exp_half (a : ℝ) :
    ∫ s in (0 : ℝ)..(2 * a), 2 * Real.exp (s / 2) = 4 * (Real.exp a - 1) := by
  have hd : ∀ s ∈ uIcc 0 (2 * a), HasDerivAt (fun s : ℝ => 4 * Real.exp (s / 2))
      (2 * Real.exp (s / 2)) s := by
    intro s _
    have he : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s :=
      ((hasDerivAt_id s).div_const 2).exp.congr_deriv (by simp)
    exact (he.const_mul 4).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => 2 * Real.exp (s / 2)).intervalIntegrable _ _)]
  simp only [zero_div, Real.exp_zero]
  rw [show 2 * a / 2 = a by ring]
  ring

/-- **`M₁(a) ~ 4e^a`.** -/
theorem tendsto_primeHinge_div_exp :
    Tendsto (fun a : ℝ => primeHinge a / Real.exp a) atTop (𝓝 4) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `|M₀(s/2) - 2e^{s/2}| ≤ (ε/4) e^{s/2} + B` on `s ≥ 0`
  have hM := tendsto_primeMass_div_exp
  obtain ⟨b₀, hb₀⟩ := Metric.tendsto_atTop.mp hM (ε / 4) (by positivity)
  set b₁ := max b₀ 0 with hb₁
  set B := primeMass b₁ + 2 * Real.exp b₁ with hBdef
  have hB0 : 0 ≤ B := by
    have := primeMass_nonneg b₁
    positivity
  have hpt : ∀ s, 0 ≤ s → |primeMass (s / 2) - 2 * Real.exp (s / 2)| ≤
      ε / 4 * Real.exp (s / 2) + B := by
    intro s hs
    by_cases hsb : b₁ ≤ s / 2
    · have hd := hb₀ (s / 2) (le_trans (le_max_left _ _) hsb)
      rw [Real.dist_eq] at hd
      have hep := Real.exp_pos (s / 2)
      have hval : primeMass (s / 2) - 2 * Real.exp (s / 2) =
          (primeMass (s / 2) / Real.exp (s / 2) - 2) * Real.exp (s / 2) := by field_simp
      rw [hval, abs_mul, abs_of_pos hep]
      nlinarith [mul_le_mul_of_nonneg_right hd.le hep.le]
    · have hsb' : s / 2 ≤ b₁ := (lt_of_not_ge hsb).le
      have h1 : primeMass (s / 2) ≤ primeMass b₁ := by
        have := monotone_primeMass_half (show s ≤ 2 * b₁ by linarith)
        simpa [show 2 * b₁ / 2 = b₁ by ring] using this
      have h2 : Real.exp (s / 2) ≤ Real.exp b₁ := Real.exp_le_exp.mpr hsb'
      have h3 := primeMass_nonneg (s / 2)
      have h4 := Real.exp_pos (s / 2)
      rw [abs_le]
      constructor <;> nlinarith
  -- eventually the constant terms are small
  have hlin : Tendsto (fun a : ℝ => (2 * a * B + 4) / Real.exp a) atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => a * Real.exp (-a)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 : Tendsto (fun a : ℝ => Real.exp (-a)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h3 := (h1.const_mul (2 * B)).add (h2.const_mul 4)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun a => ?_
    rw [Real.exp_neg]
    field_simp
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (hlin (Iio_mem_nhds (half_pos hε)))
  refine ⟨max a₀ 0, fun a ha => ?_⟩
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) ha
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have hea := Real.exp_pos a
  have hint1 : IntervalIntegrable (fun s : ℝ => primeMass (s / 2)) volume 0 (2 * a) :=
    monotone_primeMass_half.intervalIntegrable
  have hint2 : IntervalIntegrable (fun s : ℝ => 2 * Real.exp (s / 2)) volume 0 (2 * a) :=
    (by fun_prop : Continuous fun s : ℝ => 2 * Real.exp (s / 2)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun s : ℝ => ε / 4 * Real.exp (s / 2) + B) volume 0 (2 * a) :=
    (by fun_prop : Continuous fun s : ℝ => ε / 4 * Real.exp (s / 2) + B).intervalIntegrable _ _
  have hdiff : |primeHinge a - 4 * (Real.exp a - 1)| ≤ ε / 2 * (Real.exp a - 1) + 2 * a * B := by
    rw [primeHinge_eq_layerCake ha0, ← integral_two_exp_half a,
      ← intervalIntegral.integral_sub hint1 hint2]
    refine (intervalIntegral.abs_integral_le_integral_abs h2a).trans ?_
    have hmono : ∫ s in (0 : ℝ)..(2 * a), |primeMass (s / 2) - 2 * Real.exp (s / 2)| ≤
        ∫ s in (0 : ℝ)..(2 * a), (ε / 4 * Real.exp (s / 2) + B) :=
      intervalIntegral.integral_mono_on h2a (hint1.sub hint2).abs hint3
        fun s hs => hpt s hs.1
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s : ℝ => ε / 4 * Real.exp (s / 2)).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
    have h := integral_two_exp_half a
    have hc : ∫ s in (0 : ℝ)..(2 * a), ε / 4 * Real.exp (s / 2) =
        ε / 8 * ∫ s in (0 : ℝ)..(2 * a), 2 * Real.exp (s / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext s; ring
    rw [hc, h]
    ring
  have hsmall : (2 * a * B + 4) / Real.exp a < ε / 2 := ha₀ a (le_trans (le_max_left _ _) ha)
  rw [div_lt_iff₀ hea] at hsmall
  rw [Real.dist_eq, show primeHinge a / Real.exp a - 4 =
    (primeHinge a - 4 * (Real.exp a - 1) - 4) / Real.exp a by field_simp; ring,
    abs_div, abs_of_pos hea, div_lt_iff₀ hea]
  have h1 := abs_sub (primeHinge a - 4 * (Real.exp a - 1)) 4
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h1
  nlinarith

/-! ## The symbol on the scale `1/a` -/

/-- `|cos(t - h) - cos t - h sin t| ≤ (3/2) h²`. -/
theorem abs_cos_sub_sub_cos_sub_mul_sin_le (t h : ℝ) :
    |Real.cos (t - h) - Real.cos t - h * Real.sin t| ≤ 3 / 2 * h ^ 2 := by
  have hlow := cos_sub_sub_cos_ge t h
  have hup := cos_sub_sub_cos_ge (t - h) (-h)
  rw [show t - h - -h = t by ring] at hup
  have hlip : |Real.sin (t - h) - Real.sin t| ≤ |h| := by
    have := Real.abs_sin_sub_sin_le (t - h) t
    rwa [show t - h - t = -h by ring, abs_neg] at this
  have hprod : h * (Real.sin (t - h) - Real.sin t) ≤ h ^ 2 := by
    calc h * (Real.sin (t - h) - Real.sin t) ≤ |h * (Real.sin (t - h) - Real.sin t)| :=
          le_abs_self _
      _ = |h| * |Real.sin (t - h) - Real.sin t| := abs_mul _ _
      _ ≤ |h| * |h| := mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
      _ = h ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg h]

/-- **The symbol on the scale `ξ = t/(4πa)`.**
`S_a(t/(4πa)) = W(t/(4πa)) - (t/a) sin t · M₁(a) + E`, `|E| ≤ (3t²/4a²) M₂(a)`. -/
theorem abs_freeLagSymbol_scaled_sub_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |freeLagSymbol a (t / (4 * Real.pi * a)) -
        (archimedeanWeilSymbol (t / (4 * Real.pi * a)) - t / a * Real.sin t * primeHinge a)| ≤
      3 * t ^ 2 / (4 * a ^ 2) * primeSecondMoment a := by
  have hpi := Real.pi_pos
  set ξ := t / (4 * Real.pi * a) with hξ
  set h : ℕ → ℝ := fun n => t / (2 * a) * (2 * a - Real.log n) with hh
  have harg : ∀ n : ℕ, 2 * Real.pi * Real.log n * ξ = t - h n := by
    intro n
    simp only [hξ, hh]
    field_simp
    ring
  have hfull : 2 * Real.pi * (2 * a) * ξ = t := by
    simp only [hξ]
    field_simp
    ring
  have hexp : freeLagSymbol a ξ - (archimedeanWeilSymbol ξ - t / a * Real.sin t * primeHinge a) =
      -2 * ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Real.cos (t - h n) - Real.cos t - h n * Real.sin t) := by
    have hM1 : t / a * Real.sin t * primeHinge a =
        2 * ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n * (h n * Real.sin t) := by
      unfold primeHinge
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hh]
      field_simp
    unfold freeLagSymbol
    simp only [harg, hfull]
    rw [hM1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      show ∀ x y z : ℝ, x - y - (x - z) = z - y by intros; ring, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hbound : |∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
      (Real.cos (t - h n) - Real.cos t - h n * Real.sin t)| ≤
      ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n * (3 / 2 * h n ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul, abs_of_nonneg (weight_nonneg' n)]
    exact mul_le_mul_of_nonneg_left (abs_cos_sub_sub_cos_sub_mul_sin_le t (h n)) (weight_nonneg' n)
  have hM2 : ∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n * (3 / 2 * h n ^ 2) =
      3 * t ^ 2 / (8 * a ^ 2) * primeSecondMoment a := by
    unfold primeSecondMoment
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hh]
    field_simp
    ring
  rw [hexp, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  calc 2 * |∑ n ∈ Finset.Icc 2 (primeCutoff a), Λ n / Real.sqrt n *
        (Real.cos (t - h n) - Real.cos t - h n * Real.sin t)|
      ≤ 2 * (3 * t ^ 2 / (8 * a ^ 2) * primeSecondMoment a) := by
        rw [← hM2]; exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = 3 * t ^ 2 / (4 * a ^ 2) * primeSecondMoment a := by ring

/-- **The sharp boundary layer.**  `a e^{-a} S_a(t/(4πa)) → -4 t sin t`, uniformly for
`|t| ≤ T`. -/
theorem tendstoUniformlyOn_scaled_freeLagSymbol (T : ℝ) :
    TendstoUniformlyOn
      (fun a t => a * Real.exp (-a) * freeLagSymbol a (t / (4 * Real.pi * a)))
      (fun t => -(4 * t * Real.sin t)) atTop (Icc (-T) T) := by
  have hpi := Real.pi_pos
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) continuous_archimedeanWeilSymbol.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set T₁ := max T 0 with hT₁
  have hT₁0 : 0 ≤ T₁ := le_max_right _ _
  -- three vanishing terms
  have h1 : Tendsto (fun a : ℝ => a * Real.exp (-a) * |K|) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).mul_const |K|
    simpa using this
  have h2 : Tendsto (fun a : ℝ => T₁ * |primeHinge a / Real.exp a - 4|) atTop (𝓝 0) := by
    have h := (tendsto_primeHinge_div_exp.sub_const 4).abs.const_mul T₁
    simpa using h
  have h3 : Tendsto (fun a : ℝ => 12 * chebyshevConst * T₁ ^ 2 / a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hev := ((h1.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).and
    ((h2.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))).and
      (h3.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))))).and
    (eventually_ge_atTop (max 1 (T₁ / (4 * Real.pi))))
  filter_upwards [hev] with a ⟨⟨ha1, ha2, ha3⟩, ha4⟩ t ht
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) ha4)
  have hea := Real.exp_pos a
  have htT : |t| ≤ T₁ := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, le_max_left T 0]
  -- the archimedean argument stays in `[-1, 1]`
  have hξ : t / (4 * Real.pi * a) ∈ Icc (-1 : ℝ) 1 := by
    have hden : 0 < 4 * Real.pi * a := by positivity
    have hle : T₁ ≤ 4 * Real.pi * a := by
      have := le_trans (le_max_right _ _) ha4
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have : |t / (4 * Real.pi * a)| ≤ 1 := by
      rw [abs_div, abs_of_pos hden, div_le_one hden]; linarith
    exact ⟨by linarith [neg_abs_le (t / (4 * Real.pi * a))],
      by linarith [le_abs_self (t / (4 * Real.pi * a))]⟩
  have hW : |archimedeanWeilSymbol (t / (4 * Real.pi * a))| ≤ |K| :=
    (hK _ hξ).trans (le_abs_self K)
  have hE := abs_freeLagSymbol_scaled_sub_le ha0 t
  have hM2 : primeSecondMoment a ≤ 16 * chebyshevConst * Real.exp a := by
    have := primeSecondMoment_le ha0.le
    have hC := chebyshevConst_pos
    nlinarith
  have hM2nn : 0 ≤ primeSecondMoment a :=
    Finset.sum_nonneg fun n _ => mul_nonneg (weight_nonneg' n) (sq_nonneg _)
  set S := freeLagSymbol a (t / (4 * Real.pi * a))
  set W := archimedeanWeilSymbol (t / (4 * Real.pi * a))
  have hsin : |t * Real.sin t| ≤ T₁ := by
    rw [abs_mul]
    calc |t| * |Real.sin t| ≤ T₁ * 1 :=
          mul_le_mul htT (Real.abs_sin_le_one t) (abs_nonneg _) hT₁0
      _ = T₁ := mul_one _
  -- decomposition of the scaled symbol
  have hdecomp : a * Real.exp (-a) * S - -(4 * t * Real.sin t) =
      a * Real.exp (-a) * W - t * Real.sin t * (primeHinge a / Real.exp a - 4) +
        a * Real.exp (-a) * (S - (W - t / a * Real.sin t * primeHinge a)) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [Real.dist_eq, abs_sub_comm, hdecomp]
  have hea' : 0 < a * Real.exp (-a) := mul_pos ha0 (Real.exp_pos _)
  have t1 : |a * Real.exp (-a) * W| ≤ a * Real.exp (-a) * |K| := by
    rw [abs_mul, abs_of_pos hea']; exact mul_le_mul_of_nonneg_left hW hea'.le
  have t2 : |t * Real.sin t * (primeHinge a / Real.exp a - 4)| ≤
      T₁ * |primeHinge a / Real.exp a - 4| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hsin (abs_nonneg _)
  have t3 : |a * Real.exp (-a) * (S - (W - t / a * Real.sin t * primeHinge a))| ≤
      12 * chebyshevConst * T₁ ^ 2 / a := by
    rw [abs_mul, abs_of_pos hea']
    have hstep : a * Real.exp (-a) * |S - (W - t / a * Real.sin t * primeHinge a)| ≤
        a * Real.exp (-a) * (3 * t ^ 2 / (4 * a ^ 2) * (16 * chebyshevConst * Real.exp a)) := by
      refine mul_le_mul_of_nonneg_left (hE.trans ?_) hea'.le
      exact mul_le_mul_of_nonneg_left hM2 (by positivity)
    have heq : a * Real.exp (-a) * (3 * t ^ 2 / (4 * a ^ 2) * (16 * chebyshevConst * Real.exp a)) =
        12 * chebyshevConst * t ^ 2 / a := by
      rw [Real.exp_neg]; field_simp; ring
    have ht2 : t ^ 2 ≤ T₁ ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) htT 2
    have hC := chebyshevConst_pos
    refine hstep.trans (le_of_eq heq |>.trans ?_)
    gcongr
  calc |a * Real.exp (-a) * W - t * Real.sin t * (primeHinge a / Real.exp a - 4) +
        a * Real.exp (-a) * (S - (W - t / a * Real.sin t * primeHinge a))|
      ≤ |a * Real.exp (-a) * W| + |t * Real.sin t * (primeHinge a / Real.exp a - 4)| +
          |a * Real.exp (-a) * (S - (W - t / a * Real.sin t * primeHinge a))| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := lt_of_le_of_lt t1 ha1
        have := lt_of_le_of_lt t2 ha2
        have := lt_of_le_of_lt t3 ha3
        linarith
    _ = ε := by ring

/-! ## The residual on the scale `1/a` -/

theorem optimalResidual_le {a : ℝ} (ha : 0 < a) (ω : ℝ) : optimalResidual a ω ≤ 2 * a := by
  unfold optimalResidual
  have h1 := self_add_sinh_pos ha
  have h2 := sinh_sub_self_pos ha
  have h3 : 0 ≤ poleCosCoshIntegral a ω ^ 2 / (a + Real.sinh a) := by positivity
  have h4 : 0 ≤ poleSinSinhIntegral a ω ^ 2 / (Real.sinh a - a) := by positivity
  linarith

/-- **Pole-vanishing plane waves keep their full mass.**  `R_a(ω)/(2a) → 1` uniformly in `ω`. -/
theorem tendstoUniformly_optimalResidual_div :
    TendstoUniformly (fun a ω => optimalResidual a ω / (2 * a)) (fun _ => (1 : ℝ)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (max 7 (64 / ε)), eventually_gt_atTop (64 / ε)] with
    a ha hgt ω
  have ha7 : 7 ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : 0 < a := by linarith
  have hlo := optimalResidual_ge ha7 ω
  have hhi := optimalResidual_le ha0 ω
  have h2a : 0 < 2 * a := by linarith
  rw [Real.dist_eq, abs_sub_comm, show optimalResidual a ω / (2 * a) - 1 =
    (optimalResidual a ω - 2 * a) / (2 * a) by field_simp, abs_div, abs_of_pos h2a,
    div_lt_iff₀ h2a]
  have hε64 : 64 < ε * a := by rwa [div_lt_iff₀ hε, mul_comm] at hgt
  have hab : |optimalResidual a ω - 2 * a| ≤ 64 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith

end RHTower.FreeLagTrace
