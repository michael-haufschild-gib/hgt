import GaloisForLFunctions.RHTower.DeBruijnHeatForwardRealZeros
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.HTGeometry.PolynomialRecessionLocallyUniform

/-!
# Local zero counts of `H_t` near a fixed heat time

* `tendstoLocallyUniformly_riemannHeat_nhds`: for `t > 0`, `H_s → H_t` locally uniformly as
  `s → t`, from the first-order time Taylor bound `‖H_{t+h} − H_t‖ ≤ C|h|`.
* `eventually_zeroSumBall_riemannHeat_eq`: every point `z₀` has arbitrarily small discs whose zero
  count (with multiplicity) for `H_s`, `s` near `t`, equals the multiplicity of `z₀` for `H_t`.
* `exists_ball_real_zeros_forward`: around a real zero of `H_t` there are discs in which, for all
  slightly later times, every zero of `H_s` is real.  The disc carries exactly `k` zeros with
  multiplicity (the order at `x₀`), and the forward local model exhibits `k` distinct real ones.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## Continuity in the heat time -/

/-- `H_s → H_t` locally uniformly as `s → t`, for `t > 0`. -/
theorem tendstoLocallyUniformly_riemannHeat_nhds {t : ℝ} (ht : 0 < t) :
    TendstoLocallyUniformly (fun s => riemannHeat s) (riemannHeat t) (𝓝 t) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set I := ∫ x, |x| ^ (2 * 1) * ‖heatWeight (t + 1) x‖ * Real.exp (|R| * |x|) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < min (min t 1) (ε / (I + 1)) := lt_min (lt_min ht one_pos) (by positivity)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs z hz
  rw [mem_ball, Real.dist_eq] at hs
  have hs1 : |s - t| < min t 1 := hs.trans_le (min_le_left _ _)
  have hs2 : |s - t| < ε / (I + 1) := hs.trans_le (min_le_right _ _)
  have hst : 0 ≤ t + (s - t) := by
    have := (abs_lt.mp (hs1.trans_le (min_le_left _ _))).1; linarith
  have hT := norm_riemannHeat_time_taylor_le ht.le (h := s - t) hst
    (hs1.le.trans (min_le_right _ _)) 1 z
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, mul_zero, iteratedDeriv_zero, add_sub_cancel, pow_one] at hT
  have hKle : (∫ x, |x| ^ (2 * 1) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) ≤ I := by
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith) _ _)
      (integrable_pow_mul_heatWeight (by linarith) _ _) fun x => ?_
    have him : |z.im| ≤ |R| := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_abs_self R))
    dsimp only
    gcongr
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖riemannHeat s z - riemannHeat t z‖
      ≤ (∫ x, |x| ^ (2 * 1) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) * |s - t| := hT
    _ ≤ I * (ε / (I + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-! ## Multiplicities -/

theorem analyticOrderAt_riemannHeat_ne_top {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    analyticOrderAt (riemannHeat t) z ≠ ⊤ :=
  analyticOrderAt_ne_top_of_ne_zero
    ((differentiable_riemannHeat ht).differentiableOn.analyticOnNhd isOpen_univ)
    (riemannHeat_zero_ne ht) z

theorem one_le_zeroMult_riemannHeat {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0) :
    1 ≤ zeroMult (riemannHeat t) z := by
  have han : AnalyticAt ℂ (riemannHeat t) z := (differentiable_riemannHeat ht).analyticAt z
  have hne := analyticOrderAt_riemannHeat_ne_top ht z
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (han.analyticOrderAt_eq_zero.mp hn.symm) hz
  rw [zeroMult, ← hn, ENat.toNat_coe]
  omega

theorem zeroMult_riemannHeat_eq_zero {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : riemannHeat t z ≠ 0) :
    zeroMult (riemannHeat t) z = 0 := by
  have han : AnalyticAt ℂ (riemannHeat t) z := (differentiable_riemannHeat ht).analyticAt z
  rw [zeroMult, han.analyticOrderAt_eq_zero.mpr hz]
  rfl

/-- The zeros of `H_t` are isolated. -/
theorem exists_ball_riemannHeat_ne_zero {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) :
    ∃ ρ > 0, ∀ w ∈ ball z₀ ρ, w ≠ z₀ → riemannHeat t w ≠ 0 := by
  have han : AnalyticAt ℂ (riemannHeat t) z₀ := (differentiable_riemannHeat ht).analyticAt z₀
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.mpr h) (analyticOrderAt_riemannHeat_ne_top ht z₀)
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ρ, hρ, hball⟩ := h
    exact ⟨ρ, hρ, fun w hw hne => hball (mem_ball.mp hw) hne⟩

/-! ## Stable local zero counts -/

/-- **Transfer of disc counts in the heat time.** If the circle `|z − c| = r` is zero-free for
`H_t` (`t > 0`), then for `s` near `t` it is zero-free for `H_s` and the disc counts agree. -/
theorem eventually_zeroSumBall_riemannHeat_eq_of_sphere {t : ℝ} (ht : 0 < t) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hsph : ∀ w ∈ sphere c r, riemannHeat t w ≠ 0) :
    ∀ᶠ s in 𝓝 t, zeroSumBall (riemannHeat s) c r = zeroSumBall (riemannHeat t) c r ∧
      ∀ w ∈ sphere c r, riemannHeat s w ≠ 0 := by
  have hdiff := differentiable_riemannHeat ht.le
  set F : ℝ → ℂ → ℂ := fun s => riemannHeat (max s (t / 2))
  have hF : ∀ s, Differentiable ℂ (F s) := fun s =>
    differentiable_riemannHeat (le_max_of_le_right (by linarith))
  have hev : ∀ᶠ s in 𝓝 t, max s (t / 2) = s :=
    (lt_mem_nhds (by linarith : t / 2 < t)).mono fun s hs => max_eq_left hs.le
  have hconv : TendstoLocallyUniformly F (riemannHeat t) (𝓝 t) :=
    tendstoLocallyUniformly_congr_eventually (tendstoLocallyUniformly_riemannHeat_nhds ht)
      (hev.mono fun s hs z => by simp only [F, hs])
  have htr := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hdiff hconv hr
    (by linarith : r < 2 * r) hsph
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (hdiff.continuous.norm.continuousOn)
  have hμ : 0 < ‖riemannHeat t w₀‖ := norm_pos_iff.mpr (hsph w₀ hw₀)
  have hunif := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp (tendstoLocallyUniformly_riemannHeat_nhds ht))
      _ (isCompact_sphere c r))) _ hμ
  filter_upwards [htr, hev, hunif] with s hs hs' hsu
  have : F s = riemannHeat s := by simp only [F, hs']
  refine ⟨by rw [← this, hs], fun w hw h0 => ?_⟩
  have h1 := hsu w hw
  rw [dist_eq_norm, h0, sub_zero] at h1
  exact (not_lt.mpr (hmin hw)) h1


/-- **Isolating discs.** For `t ≥ 0` and any `z₀`, there is `r₀ > 0` such that for every
`0 < r ≤ r₀` the circle `|z − z₀| = r` is zero-free for `H_t` and the disc count of `H_t` is the
multiplicity of `z₀`. -/
theorem exists_radius_zeroSumBall_riemannHeat_eq {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      (∀ w ∈ sphere z₀ r, riemannHeat t w ≠ 0) ∧
      zeroSumBall (riemannHeat t) z₀ r = (zeroMult (riemannHeat t) z₀ : ℂ) := by
  classical
  obtain ⟨ρ, hρ, hiso⟩ := exists_ball_riemannHeat_ne_zero ht z₀
  refine ⟨ρ / 2, by positivity, fun r hr hrρ => ?_⟩
  have hsph : ∀ w ∈ sphere z₀ r, riemannHeat t w ≠ 0 := by
    intro w hw
    have hwr : dist w z₀ = r := mem_sphere.mp hw
    refine hiso w (mem_ball.mpr (by linarith)) ?_
    intro hwz
    rw [hwz, dist_self] at hwr
    linarith
  have hdiff := differentiable_riemannHeat ht
  refine ⟨hsph, ?_⟩
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) hdiff.differentiableOn hsph
  rw [hsum]
  have hZsub : Z ⊆ {z₀} := by
    intro w hw
    have hwb := hZball w hw
    have hw0 := (hZzero w hwb).mpr hw
    by_contra hne
    exact hiso w (mem_ball.mpr ((mem_ball.mp hwb).trans (by linarith)))
      (by simpa using hne) hw0
  by_cases hz : riemannHeat t z₀ = 0
  · have hZ : Z = {z₀} := Finset.Subset.antisymm hZsub (Finset.singleton_subset_iff.mpr
      ((hZzero z₀ (mem_ball_self hr)).mp hz))
    rw [hZ, Finset.sum_singleton]
  · have hZ : Z = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      have := Finset.mem_singleton.mp (hZsub hw)
      subst this
      exact hz ((hZzero w (hZball w hw)).mpr hw)
    rw [hZ, Finset.sum_empty, zeroMult_riemannHeat_eq_zero ht hz]
    simp

/-- **Stable local counts.** For `t > 0` and any `z₀`, there is `r₀ > 0` such that for every
`0 < r ≤ r₀` the circle `|z − z₀| = r` is zero-free for `H_t`, the disc count of `H_t` is the
multiplicity of `z₀`, and the disc count of `H_s` equals it for all `s` near `t`. -/
theorem eventually_zeroSumBall_riemannHeat_eq {t : ℝ} (ht : 0 < t) (z₀ : ℂ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ →
      (∀ w ∈ sphere z₀ r, riemannHeat t w ≠ 0) ∧
      zeroSumBall (riemannHeat t) z₀ r = (zeroMult (riemannHeat t) z₀ : ℂ) ∧
      ∀ᶠ s in 𝓝 t, zeroSumBall (riemannHeat s) z₀ r = (zeroMult (riemannHeat t) z₀ : ℂ) ∧
        ∀ w ∈ sphere z₀ r, riemannHeat s w ≠ 0 := by
  obtain ⟨r₀, hr₀, h⟩ := exists_radius_zeroSumBall_riemannHeat_eq ht.le z₀
  refine ⟨r₀, hr₀, fun r hr hrr => ?_⟩
  obtain ⟨hsph, hcount⟩ := h r hr hrr
  refine ⟨hsph, hcount, ?_⟩
  filter_upwards [eventually_zeroSumBall_riemannHeat_eq_of_sphere ht hr hsph] with s hs
  exact ⟨by rw [hs.1, hcount], hs.2⟩

/-! ## Real zeros stay real forward in time -/

/-- **Real zeros stay real.** For `t > 0` and a real point `x₀` there is `r₀ > 0` such
that for every `0 < r ≤ r₀` there is `δ > 0` with: for `t < s < t + δ`, every zero of `H_s` in the
disc `|z − x₀| < r` is real. -/
theorem exists_ball_real_zeros_forward {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ δ > 0, ∀ s, t < s → s < t + δ →
      ∀ w ∈ ball (x₀ : ℂ) r, riemannHeat s w = 0 → w.im = 0 := by
  classical
  obtain ⟨r₀, hr₀, hstable⟩ := eventually_zeroSumBall_riemannHeat_eq ht (x₀ : ℂ)
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  obtain ⟨hsph, hcount, hev⟩ := hstable r hr hrr₀
  -- the order `k` of the zero
  set k := zeroMult (riemannHeat t) x₀ with hk
  have han : AnalyticAt ℂ (riemannHeat t) x₀ := (differentiable_riemannHeat ht.le).analyticAt _
  have hord : analyticOrderAt (riemannHeat t) x₀ = (k : ℕ∞) := by
    rw [hk, zeroMult, ENat.coe_toNat (analyticOrderAt_riemannHeat_ne_top ht.le _)]
  obtain ⟨hvan, hka⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord
  obtain ⟨S, hS, q₁, hq₁, hreal⟩ := exists_real_zeros_forward ht.le hvan hka
  -- times close enough for both the count and the local model
  obtain ⟨δ₁, hδ₁, hδ₁ev⟩ := Metric.eventually_nhds_iff.mp hev
  set q₂ := min q₁ (r / (2 * S))
  have hq₂ : 0 < q₂ := lt_min hq₁ (by positivity)
  refine ⟨min δ₁ (q₂ ^ 2), lt_min hδ₁ (by positivity), fun s hts hst w hw hw0 => ?_⟩
  have hsq : s - t < q₂ ^ 2 := by linarith [min_le_right δ₁ (q₂ ^ 2)]
  obtain ⟨hcs, hsph_s⟩ :=
    hδ₁ev (y := s) (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [min_le_left δ₁ (q₂ ^ 2)])
  set q := Real.sqrt (s - t)
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hqq : q ≤ q₂ := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hsq.le
  have hsq' : t + q ^ 2 = s := by rw [Real.sq_sqrt (by linarith)]; ring
  obtain ⟨Y, hYcard, hY⟩ := hreal q hq (hqq.trans (min_le_left _ _))
  rw [hsq'] at hY
  have hqS : q * S ≤ r / 2 := by
    have := hqq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- the zero set of `H_s` in the disc
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) (differentiable_riemannHeat hs0).differentiableOn hsph_s
  rw [hcs] at hsum
  have hsumN : ∑ z ∈ Z, zeroMult (riemannHeat s) z = k := by
    have : ((∑ z ∈ Z, zeroMult (riemannHeat s) z : ℕ) : ℂ) = (k : ℂ) := by
      push_cast; exact hsum.symm
    exact_mod_cast this
  set Y' := Y.image (fun y : ℝ => (y : ℂ))
  have hY'card : Y'.card = k := by
    rw [Finset.card_image_of_injective _ Complex.ofReal_injective, hYcard]
  have hY'Z : Y' ⊆ Z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hyd, hy0⟩ := hY y hy
    have hyb : (y : ℂ) ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      linarith
    exact (hZzero _ hyb).mp hy0
  have hsplit := Finset.sum_sdiff hY'Z (f := fun z => zeroMult (riemannHeat s) z)
  have hY'sum : k ≤ ∑ z ∈ Y', zeroMult (riemannHeat s) z := by
    rw [← hY'card, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun z hz => one_le_zeroMult_riemannHeat hs0 ?_
    exact (hZzero z (hZball z (hY'Z hz))).mpr (hY'Z hz)
  have hrest : Z \ Y' = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    have h1 : 1 ≤ zeroMult (riemannHeat s) z :=
      one_le_zeroMult_riemannHeat hs0 ((hZzero z (hZball z (Finset.sdiff_subset hz))).mpr
        (Finset.sdiff_subset hz))
    have h2 := Finset.single_le_sum (f := fun z => zeroMult (riemannHeat s) z)
      (fun _ _ => Nat.zero_le _) hz
    omega
  have hwZ : w ∈ Z := (hZzero w hw).mp hw0
  have hwY : w ∈ Y' := by
    by_contra hn
    have : w ∈ Z \ Y' := Finset.mem_sdiff.mpr ⟨hwZ, hn⟩
    rw [hrest] at this
    exact Finset.notMem_empty _ this
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hwY
  exact Complex.ofReal_im y

end

end RHTower.DeBruijn
