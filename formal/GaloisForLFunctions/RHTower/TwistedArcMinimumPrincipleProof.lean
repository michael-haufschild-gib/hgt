import GaloisForLFunctions.RHTower.WhittakerStreamCorner
import GaloisForLFunctions.RHTower.ModularArcGrowingModePositivity
import GaloisForLFunctions.RHTower.TwistedArcMomentPositiveRH
import GaloisForLFunctions.HTGeometry.ModularHalfDomainStreamMinimumPrinciple

/-!
# The twisted arc minimum principle holds

**Theorem** (`twistedArcMinimumPrinciple_holds`).  No finite combination `F = Σ_{i<N} a_i M_i` of
the twisted arc moments `M_i(u) = ∫ g_u(x) cos(2π(i+2)x) dx` is strictly positive on the whole
closed bottom arc `u ∈ [−½, ½]`.

Consequently (`riemannHypothesis_iff_primeBlindPositive_unconditional`), the Riemann hypothesis is
equivalent to prime-blind positivity, with no further hypothesis.

Proof.  Suppose `F ≥ δ > 0` on the arc.

1. *Stream certificate.*  Pair `F` with the nonnegative clamped Legendre kernels `k_c`
   (`0 < c ≤ ½`).  By `TwistedArcStreamMoment`, `∫₀^{1/2} F k_c/√y = 4 (2G(½) − G(c)/c)`, where
   `G(c) = Σ a_i (1 − c²) S_{k_i}(c)` is the arc flux.  Since `F ≥ δ` and `∫ k_c ≥ (½ − c)c²/(3/2)`,
   `2G(½) − G(c)/c ≥ (δ/6)(½ − c) c²`.
2. *The stream function* `ψ = Σ a_i y K₁(k_i y) sin(k_i x)` solves the stream equation, vanishes on
   both walls of the half fundamental domain, decays at the cusp, and its ray derivative at the arc
   point over `c` is `G(c)`.
3. If `G(½) ≤ 0`, then `G(c) < 0` on `(0, ½)`, so the minimum principle gives `ψ ≥ 0`; the lowest
   sine mode of `ψ` changes sign on `[0, ½]`, so every `a_i` vanishes and `F = 0`.
4. If `G(½) > 0`, apply the minimum principle to `Z = ψ − 2G(½) x`, whose ray derivative
   `G(c) − 2G(½)c` is negative: `Z ≥ −G(½) = Z(½, ·)`.  Hence `∂_x Z(½, y) ≤ 0` for `y > √3/2`
   with equality at the corner, so `∂_y ∂_x ψ(ρ) ≤ 0`.  But the certificate makes `G(c)/c` increase
   strictly into `½`, so `G'(½) > 2G(½)`, and `∂_y ∂_x ψ(ρ) = √3 (G'(½) − 2G(½)) > 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### One-sided derivative tests -/

theorem hasDerivAt_nonpos_of_left_ge {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h : ∀ᶠ t in 𝓝[<] a, f a ≤ f t) : d ≤ 0 := by
  have hs : Tendsto (slope f a) (𝓝[<] a) (𝓝 d) :=
    hf.tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_lt ht)
  refine le_of_tendsto hs ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht (ht' : t < a)
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem hasDerivAt_nonpos_of_right_le {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h : ∀ᶠ t in 𝓝[>] a, f t ≤ f a) : d ≤ 0 := by
  have hs : Tendsto (slope f a) (𝓝[>] a) (𝓝 d) :=
    hf.tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  refine le_of_tendsto hs ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht (ht' : a < t)
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem le_hasDerivAt_of_left {f : ℝ → ℝ} {a d κ : ℝ} (hf : HasDerivAt f d a)
    (h : ∀ᶠ t in 𝓝[<] a, κ * (a - t) ≤ f a - f t) : κ ≤ d := by
  have hs : Tendsto (slope f a) (𝓝[<] a) (𝓝 d) :=
    hf.tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht => ne_of_lt ht)
  refine ge_of_tendsto hs ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht (ht' : t < a)
  rw [slope_def_field, le_div_iff_of_neg (by linarith)]
  linarith

/-! ### The lowest mode -/

variable {N : ℕ}

theorem sin_streamFreq_quarter (i : ℕ) :
    Real.sin (streamFreq i * (1 / (4 * ((i : ℝ) + 2)))) = 1 := by
  have : streamFreq i * (1 / (4 * ((i : ℝ) + 2))) = Real.pi / 2 := by
    unfold streamFreq arcFreq; push_cast; field_simp; ring
  rw [this, Real.sin_pi_div_two]

theorem sin_streamFreq_three_quarter (i : ℕ) :
    Real.sin (streamFreq i * (3 / (4 * ((i : ℝ) + 2)))) = -1 := by
  have : streamFreq i * (3 / (4 * ((i : ℝ) + 2))) = Real.pi / 2 + Real.pi := by
    unfold streamFreq arcFreq; push_cast; field_simp; ring
  rw [this, Real.sin_add_pi, Real.sin_pi_div_two]

theorem streamFreq_sub_ge {i j : ℕ} (h : i < j) : 2 * Real.pi ≤ streamFreq j - streamFreq i := by
  unfold streamFreq arcFreq
  have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
  push_cast
  nlinarith [Real.pi_pos]

/-- **A nonnegative stream function has no modes.** -/
theorem eq_zero_of_whStream_nonneg (a : Fin N → ℝ)
    (h : ∀ x y, 0 ≤ x → x ≤ 1 / 2 → 1 ≤ y → 0 ≤ whStream a x y) : ∀ i, a i = 0 := by
  by_contra hne
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hne
  set S := Finset.univ.filter fun i : Fin N => a i ≠ 0 with hS
  have hSne : S.Nonempty := ⟨i₁, by simp [hS, hi₁]⟩
  set i₀ := S.min' hSne with hi₀
  have hai₀ : a i₀ ≠ 0 := by
    have := S.min'_mem hSne; simp only [hS, Finset.mem_filter] at this; exact this.2
  have hlow : ∀ i, i < i₀ → a i = 0 := by
    intro i hi
    by_contra hai
    have : i₀ ≤ i := S.min'_le i (by simp [hS, hai])
    exact absurd hi (not_lt.mpr this)
  set k₀ := streamFreq i₀ with hk₀
  have hk₀pos : 0 < k₀ := streamFreq_pos _
  set B := ∑ i, |a i| with hB
  -- the bound on the higher modes
  have hhigh : ∀ x y, 1 ≤ y → |whStream a x y - a i₀ * modeStream k₀ x y| ≤
      B * Real.exp (-(2 * Real.pi * y)) * (y * kMoment 1 (k₀ * y)) := by
    intro x y hy
    have hy0 : 0 < y := by linarith
    have hsplit : whStream a x y - a i₀ * modeStream k₀ x y =
        ∑ i ∈ Finset.univ.erase i₀, a i * modeStream (streamFreq i) x y := by
      unfold whStream
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      ring
    rw [hsplit]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.univ.erase i₀, |a i * modeStream (streamFreq i) x y|
        ≤ ∑ i ∈ Finset.univ.erase i₀, |a i| * (Real.exp (-(2 * Real.pi * y)) *
            (y * kMoment 1 (k₀ * y))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hlt | hgt
          · rw [hlow i hlt]; simp
          · have hki : 2 * Real.pi ≤ streamFreq i - k₀ := streamFreq_sub_ge (by exact_mod_cast hgt)
            have hK := kMoment_le_exp_mul 1 (mul_pos hk₀pos hy0)
              (show k₀ * y ≤ streamFreq i * y by nlinarith [Real.pi_pos])
            have hexp : Real.exp (-(streamFreq i * y - k₀ * y)) ≤ Real.exp (-(2 * Real.pi * y)) :=
              Real.exp_le_exp.mpr (by nlinarith)
            unfold modeStream
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hy0, abs_of_nonneg (kMoment_nonneg _ _)]
            have hs := Real.abs_sin_le_one (streamFreq i * x)
            have hK0 := kMoment_nonneg 1 (k₀ * y)
            calc |a i| * (y * kMoment 1 (streamFreq i * y) * |Real.sin (streamFreq i * x)|)
                ≤ |a i| * (y * (Real.exp (-(streamFreq i * y - k₀ * y)) *
                    kMoment 1 (k₀ * y)) * 1) := by
                  gcongr
              _ ≤ |a i| * (y * (Real.exp (-(2 * Real.pi * y)) * kMoment 1 (k₀ * y)) * 1) := by
                  gcongr
              _ = _ := by ring
      _ ≤ ∑ i, |a i| * (Real.exp (-(2 * Real.pi * y)) * (y * kMoment 1 (k₀ * y))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun i _ _ =>
            mul_nonneg (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (by linarith) (kMoment_nonneg _ _)))
      _ = B * Real.exp (-(2 * Real.pi * y)) * (y * kMoment 1 (k₀ * y)) := by
          rw [hB, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  -- choose a height where the higher modes are smaller than the lowest one
  have hA : 0 < |a i₀| := abs_pos.mpr hai₀
  have ht : Tendsto (fun y : ℝ => B * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 2 * Real.pi * y) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
  obtain ⟨Y, hY⟩ := (ht.eventually (gt_mem_nhds hA)).exists_forall_of_atTop
  set y := max Y 1 with hy
  have hy1 : 1 ≤ y := le_max_right _ _
  have hyY : Y ≤ y := le_max_left _ _
  have hEy := hY y hyY
  have hy0 : 0 < y := by linarith
  have hP : 0 < y * kMoment 1 (k₀ * y) := mul_pos hy0 (kMoment_pos_of_pos 1 (mul_pos hk₀pos hy0))
  have hn : (0 : ℝ) < (i₀ : ℝ) + 2 := by positivity
  have hx1 : 1 / (4 * ((i₀ : ℝ) + 2)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hx3 : 3 / (4 * ((i₀ : ℝ) + 2)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hplus := h _ y (by positivity) hx1 hy1
  have hminus := h _ y (by positivity) hx3 hy1
  have b1 := hhigh (1 / (4 * ((i₀ : ℝ) + 2))) y hy1
  have b3 := hhigh (3 / (4 * ((i₀ : ℝ) + 2))) y hy1
  have e1 : modeStream k₀ (1 / (4 * ((i₀ : ℝ) + 2))) y = y * kMoment 1 (k₀ * y) := by
    unfold modeStream; rw [hk₀, sin_streamFreq_quarter]; ring
  have e3 : modeStream k₀ (3 / (4 * ((i₀ : ℝ) + 2))) y = -(y * kMoment 1 (k₀ * y)) := by
    unfold modeStream; rw [hk₀, sin_streamFreq_three_quarter]; ring
  rw [e1] at b1
  rw [e3] at b3
  rw [abs_le] at b1 b3
  -- `a i₀ ≥ −ε` and `a i₀ ≤ ε` with `ε < |a i₀|`, after dividing by the positive mode
  have hlo : -(B * Real.exp (-(2 * Real.pi * y))) * (y * kMoment 1 (k₀ * y)) ≤
      a i₀ * (y * kMoment 1 (k₀ * y)) := by nlinarith [b1.2]
  have hhi : a i₀ * (y * kMoment 1 (k₀ * y)) ≤
      B * Real.exp (-(2 * Real.pi * y)) * (y * kMoment 1 (k₀ * y)) := by nlinarith [b3.2]
  have hlo' := le_of_mul_le_mul_right hlo hP
  have hhi' := le_of_mul_le_mul_right hhi hP
  rcases le_or_gt 0 (a i₀) with h0 | h0
  · rw [abs_of_nonneg h0] at hA hEy
    linarith
  · rw [abs_of_neg h0] at hEy
    linarith

/-! ### The theorem -/

theorem continuous_twArcMoment_arcClamp (n : ℕ) :
    Continuous fun u : ℝ => twArcMoment n (arcClamp u) :=
  (continuous_twArcMoment n).comp (continuous_projIcc (a := (-1 / 2 : ℝ)) (b := 1 / 2)
    (h := by norm_num))

theorem continuousOn_legendreArcWeight {c : ℝ} :
    ContinuousOn (fun u => legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u))
      (uIcc 0 (1 / 2)) := by
  rw [uIcc_of_le (by norm_num)]
  intro u hu
  have hy : 0 < modularArcHeight u := modularArcHeight_pos ⟨by linarith [hu.1], hu.2⟩
  have hs : Real.sqrt (modularArcHeight u) ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  refine (continuousOn_legendreKernel_half u hu).div ?_ hs
  exact (Real.continuous_sqrt.comp (by unfold modularArcHeight; fun_prop)).continuousWithinAt

/-- **The twisted arc minimum principle.** -/
theorem twistedArcMinimumPrinciple_holds : TwistedArcMinimumPrinciple := by
  intro N a hpos
  set F : ArcParam → ℝ := fun u => ∑ i, a i * twArcMoment i u with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun i _ => (continuous_twArcMoment i).const_mul _
  have hne : (univ : Set ArcParam).Nonempty := ⟨⟨0, by norm_num, by norm_num⟩, mem_univ _⟩
  obtain ⟨u₀, -, hu₀⟩ := isCompact_univ.exists_isMinOn hne hFc.continuousOn
  set δ := F u₀ with hδdef
  have hδ : 0 < δ := hpos u₀
  have hFδ : ∀ u, δ ≤ F u := fun u => hu₀ (mem_univ u)
  set G := arcStreamFlux a with hGdef
  -- the stream certificate
  have hcert : ∀ c, 0 < c → c ≤ 1 / 2 →
      δ / 6 * ((1 / 2 - c) * c ^ 2) ≤ 2 * G (1 / 2) - G c / c := by
    intro c hc hc2
    set w : ℝ → ℝ := fun u => legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u) with hw
    have hwc : ContinuousOn w (uIcc 0 (1 / 2)) := continuousOn_legendreArcWeight
    have hint : ∀ i : Fin N, IntervalIntegrable (fun u => twArcMoment i (arcClamp u) * w u)
        volume 0 (1 / 2) := fun i =>
      ((continuous_twArcMoment_arcClamp i).continuousOn.mul hwc).intervalIntegrable
    have hI : ∫ u in (0 : ℝ)..(1 / 2), F (arcClamp u) * w u = 4 * (2 * G (1 / 2) - G c / c) := by
      have hsum : ∀ u, F (arcClamp u) * w u = ∑ i, a i * (twArcMoment i (arcClamp u) * w u) := by
        intro u
        simp only [hF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [hsum]
      rw [intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul (a i)]
      simp_rw [intervalIntegral.integral_const_mul]
      have hmom : ∀ i : Fin N, ∫ u in (0 : ℝ)..(1 / 2), twArcMoment i (arcClamp u) * w u =
          4 * ((3 / 2) * arcWhittakerSlope (streamFreq i) (1 / 2) -
            (1 - c ^ 2) * arcWhittakerSlope (streamFreq i) c / c) := fun i =>
        integral_twArcMoment_mul_legendreKernel i hc hc2
      simp_rw [hmom]
      simp only [hGdef, arcStreamFlux, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlow : δ * ∫ u in (0 : ℝ)..(1 / 2), legendreKernel (1 / 2) c u ≤
        ∫ u in (0 : ℝ)..(1 / 2), F (arcClamp u) * w u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun u hu => ?_
      · exact ((continuousOn_legendreKernel_half (c := c)).mono (by
          rw [uIcc_of_le (by norm_num)])).intervalIntegrable.const_mul δ
      · exact ((hFc.comp continuous_projIcc).continuousOn.mul hwc).intervalIntegrable
      · have hy : 0 < modularArcHeight u := modularArcHeight_pos ⟨by linarith [hu.1], hu.2⟩
        have hy1 : modularArcHeight u ≤ 1 := by
          unfold modularArcHeight
          rw [Real.sqrt_le_one]; nlinarith [sq_nonneg u]
        have hs0 : 0 < Real.sqrt (modularArcHeight u) := Real.sqrt_pos.mpr hy
        have hs1 : Real.sqrt (modularArcHeight u) ≤ 1 := Real.sqrt_le_one.mpr hy1
        have hk := legendreKernel_nonneg hc hc2 (by norm_num) hu.1 hu.2
        have hkw : legendreKernel (1 / 2) c u ≤ w u := by
          simp only [hw]
          rw [le_div_iff₀ hs0]
          nlinarith
        have hF' := hFδ (arcClamp u)
        calc δ * legendreKernel (1 / 2) c u ≤ δ * w u := mul_le_mul_of_nonneg_left hkw hδ.le
          _ ≤ F (arcClamp u) * w u := mul_le_mul_of_nonneg_right hF' (hk.trans hkw)
    have hK := integral_legendreKernel_ge hc hc2 (by norm_num : (1 / 2 : ℝ) < 1)
    have hKd := mul_le_mul_of_nonneg_left hK hδ.le
    rw [hI] at hlow
    have : δ * ((1 / 2 - c) * c ^ 2 / (3 * (1 / 2))) = δ / 6 * ((1 / 2 - c) * c ^ 2) * 4 := by ring
    linarith
  have hhalf : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have habs : ∀ x : ℝ, 0 < x → x < 1 / 2 → |x| < 1 := fun x hx hx2 => by
    rw [abs_of_pos hx]; linarith
  -- the flux is below `2G(½) x` on the open arc
  have hflux : ∀ x, 0 < x → x < 1 / 2 → G x < 2 * G (1 / 2) * x := by
    intro x hx hx2
    have h1 := hcert x hx hx2.le
    have h2 : 0 < δ / 6 * ((1 / 2 - x) * x ^ 2) := by
      have : 0 < 1 / 2 - x := by linarith
      positivity
    have h3 : G x / x < 2 * G (1 / 2) := by linarith
    rwa [div_lt_iff₀ hx] at h3
  rcases le_or_gt (G (1 / 2)) 0 with hG | hG
  · -- `G(½) ≤ 0`: the stream function is nonnegative
    have hψ : ∀ x y, 0 ≤ x → x ≤ 1 / 2 → 1 ≤ y → 0 ≤ whStream a x y := by
      intro x y hx hx2 hy
      refine le_of_halfDomainStreamMinimum (Zx := whStreamX a) (Zxx := whStreamXX a)
        (Zy := whStreamY a) (Zyy := whStreamYY a)
        (fun x y _ => hasDerivAt_whStream_x a x y) (fun x y _ => hasDerivAt_whStreamX_x a x y)
        (fun x y hy => hasDerivAt_whStream_y a x hy) (fun x y hy => hasDerivAt_whStreamY_y a x hy)
        (fun x y _ => whStream_pde a x y) (continuousOn_whStream a)
        (fun y _ => (whStream_zero a y).ge) (fun y _ => (whStream_half a y).ge) ?_ ?_
        hx hx2 (by linarith) (by nlinarith)
      · intro ε hε
        obtain ⟨Y, hY⟩ := exists_abs_whStream_le a hε
        exact ⟨Y, fun x y _ _ hy => by have := hY x y hy; rw [abs_le] at this; linarith⟩
      · intro x hx hx2
        have hy := modularArcHeight_pos_of_abs_lt (habs x hx hx2)
        refine ⟨G x, by nlinarith [hflux x hx hx2], ?_⟩
        have h := hasDerivAt_whStream_ray a x hy
        rw [whStream_ray_eq_flux a (habs x hx hx2)] at h
        exact h
    have hall := eq_zero_of_whStream_nonneg a hψ
    have h0 := hpos u₀
    simp [hall] at h0
  · -- `G(½) > 0`: the corner
    set l := 2 * G (1 / 2) with hl
    have hl0 : 0 < l := by rw [hl]; linarith
    have hlin : ∀ x : ℝ, HasDerivAt (fun s : ℝ => l * s) l x := fun x => by
      simpa using (hasDerivAt_id x).const_mul l
    have hZ : ∀ x y, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ y → 1 ≤ x ^ 2 + y ^ 2 →
        -G (1 / 2) ≤ whStream a x y - l * x := by
      intro x y hx hx2 hy0 hr
      refine le_of_halfDomainStreamMinimum (Z := fun x y => whStream a x y - l * x)
        (Zx := fun x y => whStreamX a x y - l) (Zxx := whStreamXX a) (Zy := whStreamY a)
        (Zyy := whStreamYY a)
        (fun x y _ => (hasDerivAt_whStream_x a x y).sub (hlin x))
        (fun x y _ => (hasDerivAt_whStreamX_x a x y).sub_const l)
        (fun x y hy => (hasDerivAt_whStream_y a x hy).sub_const _)
        (fun x y hy => hasDerivAt_whStreamY_y a x hy)
        (fun x y _ => whStream_pde a x y)
        ((continuousOn_whStream a).sub (by fun_prop)) ?_ ?_ ?_ ?_ hx hx2 hy0 hr
      · intro y _; simp only [whStream_zero]; linarith
      · intro y _; simp only [whStream_half]; rw [hl]; linarith
      · intro ε hε
        obtain ⟨Y, hY⟩ := exists_abs_whStream_le a hε
        refine ⟨Y, fun x y hx hx2 hy => ?_⟩
        have := hY x y hy
        rw [abs_le] at this
        have : l * x ≤ l * (1 / 2) := mul_le_mul_of_nonneg_left hx2 hl0.le
        rw [hl] at this ⊢
        linarith
      · intro x hx hx2
        have hy := modularArcHeight_pos_of_abs_lt (habs x hx hx2)
        refine ⟨G x - l * x, by rw [hl]; linarith [hflux x hx hx2], ?_⟩
        have h := hasDerivAt_whStream_ray a x hy
        rw [whStream_ray_eq_flux a (habs x hx hx2)] at h
        have hr : HasDerivAt (fun t : ℝ => l * ((1 + t) * x)) (l * x) 0 := by
          simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const x).const_mul l
        exact h.sub hr
    -- the wall: `∂_x Z(½, y) ≤ 0` above the corner
    have hy₀ := modularArcHeight_half_pos
    have hy₀2 := modularArcHeight_half_sq
    have hwall : ∀ y, modularArcHeight (1 / 2) < y → whStreamX a (1 / 2) y - l ≤ 0 := by
      intro y hy
      have hy0 : 0 < y := hy₀.trans hy
      have hd : HasDerivAt (fun s => whStream a s y - l * s) (whStreamX a (1 / 2) y - l) (1 / 2) :=
        (hasDerivAt_whStream_x a (1 / 2) y).sub (hlin _)
      refine hasDerivAt_nonpos_of_left_ge hd ?_
      have hy2 : 3 / 4 < y ^ 2 := by nlinarith
      have hev1 : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), 1 < s ^ 2 + y ^ 2 :=
        continuousAt_const.eventually_lt
          (by fun_prop : Continuous fun s : ℝ => s ^ 2 + y ^ 2).continuousAt
          (by nlinarith)
      have hev2 : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), 0 < s := lt_mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
        with s hs1 hs2 (hs3 : s < 1 / 2)
      have := hZ s y hs2.le hs3.le hy0.le hs1.le
      simp only [whStream_half]
      rw [hl] at this ⊢
      linarith
    have hφ0 : whStreamX a (1 / 2) (modularArcHeight (1 / 2)) - l = 0 := by
      rw [whStreamX_half_eq, hl, hGdef]; ring
    have hXY : whStreamXY a (1 / 2) (modularArcHeight (1 / 2)) ≤ 0 := by
      refine hasDerivAt_nonpos_of_right_le
        ((hasDerivAt_whStreamX_y a (1 / 2) hy₀).sub_const l) ?_
      filter_upwards [self_mem_nhdsWithin] with y (hy : modularArcHeight (1 / 2) < y)
      rw [hφ0]
      exact hwall y hy
    -- the certificate makes `G(c)/c` increase strictly into `½`
    have hH : HasDerivAt (fun c => G c / c)
        ((arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2) (1 / 2) :=
      (hasDerivAt_arcStreamFlux_half a).div (hasDerivAt_id _) (by norm_num)
    have hκ : δ / 96 ≤ (arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2 := by
      refine le_hasDerivAt_of_left hH ?_
      filter_upwards [Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with c hc
      have h1 := hcert c (by linarith [hc.1]) hc.2.le
      have hc2 : 1 / 16 ≤ c ^ 2 := by nlinarith [hc.1]
      have hd : 0 < 1 / 2 - c := by linarith [hc.2]
      have h2 : δ / 96 * (1 / 2 - c) ≤ δ / 6 * ((1 / 2 - c) * c ^ 2) := by
        have := mul_le_mul_of_nonneg_left hc2 (mul_nonneg (by positivity : (0 : ℝ) ≤ δ / 6) hd.le)
        nlinarith
      have h3 : G (1 / 2) / (1 / 2) = 2 * G (1 / 2) := by ring
      rw [h3]
      linarith
    have hpos' : 0 < arcStreamFluxSlope a - 2 * G (1 / 2) := by
      have : (arcStreamFluxSlope a * (1 / 2) - G (1 / 2) * 1) / (1 / 2) ^ 2 =
          2 * (arcStreamFluxSlope a - 2 * G (1 / 2)) := by ring
      rw [this] at hκ
      have : 0 < δ / 96 := by positivity
      linarith
    have hXY' := whStreamXY_half_eq a
    rw [← hGdef] at hXY'
    have : 0 < 2 * modularArcHeight (1 / 2) * (arcStreamFluxSlope a - 2 * G (1 / 2)) := by
      positivity
    linarith

/-- **The decay-class (N1) line witness exists.**  An even `h` with `h(1/x) = |x| h(x)`, `∫ h = 0`,
log profile `O(e^{−3|v|/2})`, strictly positive definite log profile, and
`∫ h′(x) sin(2πmx) dx = 0` for every integer `m ≥ 2`. -/
theorem exists_decayClass_fullLineWitness :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) :=
  exists_decayClass_fullLineWitness_of_twistedArcMinimumPrinciple twistedArcMinimumPrinciple_holds

/-- **The Riemann hypothesis is prime-blind positivity.** -/
theorem riemannHypothesis_iff_primeBlindPositive_unconditional :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive :=
  WeilSpectral.riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple
    twistedArcMinimumPrinciple_holds

end

end RHTower
