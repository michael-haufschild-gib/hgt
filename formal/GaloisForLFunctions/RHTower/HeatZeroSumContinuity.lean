import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.RHTower.DeBruijnStripThreshold
import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound
import GaloisForLFunctions.HTGeometry.PolynomialRootSumSemicontinuity

/-!
# Continuity of localized heat-zero sums

Local multiplicity conservation controls continuous weights through
collisions. Clamping the heat parameter at zero includes the unheated
endpoint in the same compact-open convergence argument.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The zero sum with a real weight, counting analytic multiplicity. -/
def heatWeightedZeroSum (Ψ : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∑' z : ℂ, (zeroMult (riemannHeat t) z : ℝ) * Ψ z

/-- The clamped heat family is locally uniformly continuous at every
real parameter, including the endpoint of nonnegative heat time. -/
theorem tendstoLocallyUniformly_riemannHeat_clamped_nhds (t : ℝ) :
    TendstoLocallyUniformly (fun s : ℝ => riemannHeat (max s 0))
      (riemannHeat (max t 0)) (𝓝 t) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let A := ∫ x, |x| ^ (2 * 1) * ‖heatWeight (max t 0 + 1) x‖ * Real.exp (|R| * |x|)
  have hA : 0 ≤ A := integral_nonneg fun x => by positivity
  have ht0 : 0 ≤ max t 0 := le_max_right _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < min 1 (ε / (A + 1)) := lt_min one_pos (by positivity)
  have hcont : Continuous (fun s : ℝ => max s 0) := continuous_id.max continuous_const
  have hev : ∀ᶠ s : ℝ in 𝓝 t, |max s 0 - max t 0| < min 1 (ε / (A + 1)) := by
    have h := hcont.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (max t 0) hδ)
    simpa only [mem_ball, Real.dist_eq] using h
  filter_upwards [hev] with s hs z hz
  have hst : 0 ≤ max t 0 + (max s 0 - max t 0) := by
    rw [add_sub_cancel]
    exact le_max_right _ _
  have hT := norm_riemannHeat_time_taylor_le ht0 (h := max s 0 - max t 0) hst
    (hs.le.trans (min_le_left _ _)) 1 z
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, mul_zero, iteratedDeriv_zero, add_sub_cancel, pow_one] at hT
  have hKle : (∫ x, |x| ^ (2 * 1) * ‖heatWeight (max t 0 + 1) x‖ *
      Real.exp (|z.im| * |x|)) ≤ A := by
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith only [ht0]) _ _)
      (integrable_pow_mul_heatWeight (by linarith only [ht0]) _ _) fun x => ?_
    have him : |z.im| ≤ |R| := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_abs_self R))
    dsimp only
    gcongr
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖riemannHeat (max s 0) z - riemannHeat (max t 0) z‖
        ≤ (∫ x, |x| ^ (2 * 1) * ‖heatWeight (max t 0 + 1) x‖ *
            Real.exp (|z.im| * |x|)) * |max s 0 - max t 0| := hT
    _ ≤ A * (ε / (A + 1)) := by
      gcongr
      exact hs.le.trans (min_le_right _ _)
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith only [hε]

private theorem heatWeightedZeroSum_eq_sum_of_cover {Ψ : ℂ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) {Z : Finset ℂ}
    (hcover : ∀ z : ℂ, riemannHeat t z = 0 → Ψ z ≠ 0 → z ∈ Z) :
    heatWeightedZeroSum Ψ t = ∑ z ∈ Z, (zeroMult (riemannHeat t) z : ℝ) * Ψ z := by
  classical
  unfold heatWeightedZeroSum
  apply tsum_eq_sum
  intro z hz
  by_cases hf : riemannHeat t z = 0
  · have hΨ : Ψ z = 0 := by
      by_contra hΨ
      exact hz (hcover z hf hΨ)
    rw [hΨ, mul_zero]
  · rw [zeroMult_riemannHeat_eq_zero ht hf, Nat.cast_zero, zero_mul]

private theorem zero_clusters_exhaust_of_count_eq
    {S Z : Finset ℂ} {U : ℂ → Finset ℂ} {m n : ℂ → ℕ}
    (hsub : ∀ a ∈ S, U a ⊆ Z) (hdisj : (S : Set ℂ).PairwiseDisjoint U)
    (hcount : ∀ a ∈ S, ∑ z ∈ U a, m z = n a)
    (htotal : ∑ z ∈ Z, m z = ∑ a ∈ S, n a)
    (hpos : ∀ z ∈ Z, 1 ≤ m z) : Z = S.biUnion U := by
  classical
  have hUZ : S.biUnion U ⊆ Z := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := Finset.mem_biUnion.mp hz
    exact hsub a ha hza
  have hsumU : ∑ z ∈ S.biUnion U, m z = ∑ a ∈ S, n a := by
    rw [Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl hcount
  have hsumRest := Finset.sum_sdiff hUZ (f := m)
  have hempty : Z \ S.biUnion U = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    have h1 := hpos z (Finset.sdiff_subset hz)
    have h2 := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hz
    omega
  apply Finset.Subset.antisymm _ hUZ
  intro z hz
  by_contra hn
  have hmem : z ∈ Z \ S.biUnion U := Finset.mem_sdiff.mpr ⟨hz, hn⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty _ hmem

private theorem weighted_zero_clusters_error_le
    {S Z : Finset ℂ} {U : ℂ → Finset ℂ} {m n : ℂ → ℕ} {Ψ : ℂ → ℝ} {η : ℝ}
    (hZ : Z = S.biUnion U) (hdisj : (S : Set ℂ).PairwiseDisjoint U)
    (hcount : ∀ a ∈ S, ∑ z ∈ U a, m z = n a)
    (hosc : ∀ a ∈ S, ∀ z ∈ U a, |Ψ z - Ψ a| ≤ η) :
    |(∑ z ∈ Z, (m z : ℝ) * Ψ z) - ∑ a ∈ S, (n a : ℝ) * Ψ a| ≤
      η * ∑ a ∈ S, (n a : ℝ) := by
  classical
  have hterm (a : ℂ) (ha : a ∈ S) :
      (∑ z ∈ U a, (m z : ℝ) * Ψ z) - (n a : ℝ) * Ψ a =
        ∑ z ∈ U a, (m z : ℝ) * (Ψ z - Ψ a) := by
    symm
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum, hcount a ha]
  rw [hZ, Finset.sum_biUnion hdisj, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hterm]
  calc
    |∑ a ∈ S, ∑ z ∈ U a, (m z : ℝ) * (Ψ z - Ψ a)|
        ≤ ∑ a ∈ S, |∑ z ∈ U a, (m z : ℝ) * (Ψ z - Ψ a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S, ∑ z ∈ U a, (m z : ℝ) * η := by
      refine Finset.sum_le_sum fun a ha => (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun z hz => ?_
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hosc a ha z hz) (Nat.cast_nonneg _)
    _ = η * ∑ a ∈ S, (n a : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← Finset.sum_mul, ← Nat.cast_sum, hcount a ha, mul_comm]

private theorem continuous_heatWeightedZeroSum_clamped_of_support
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (R₀ : ℝ)
    (hsupport : ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, riemannHeat s z = 0 → R₀ ≤ ‖z‖ → Ψ z = 0) :
    Continuous (fun t : ℝ => heatWeightedZeroSum Ψ (max t 0)) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro t
  let a₀ := max t 0
  have ha₀ : 0 ≤ a₀ := le_max_right _ _
  have hf := differentiable_riemannHeat ha₀
  have hF (s : ℝ) := differentiable_riemannHeat (le_max_right s 0)
  have hconv := tendstoLocallyUniformly_riemannHeat_clamped_nhds t
  have hnotlocal (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, riemannHeat a₀ w = 0 :=
    fun h => analyticOrderAt_riemannHeat_ne_top ha₀ z (analyticOrderAt_eq_top.mpr h)
  obtain ⟨R, hRlo, _, hRsph⟩ := exists_radius_no_boundary_zero (c := (0 : ℂ))
    (hf.differentiableOn.analyticOnNhd isOpen_univ) hnotlocal (max 1 R₀)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hRlo)
  have hR₀ : R₀ ≤ R := (le_max_right _ _).trans hRlo
  have hrep (s : ℝ) (hs : 0 ≤ s) (Z : Finset ℂ)
      (hZ : ∀ z ∈ ball (0 : ℂ) R, riemannHeat s z = 0 ↔ z ∈ Z) :
      heatWeightedZeroSum Ψ s = ∑ z ∈ Z, (zeroMult (riemannHeat s) z : ℝ) * Ψ z := by
    apply heatWeightedZeroSum_eq_sum_of_cover hs
    intro z hz hΨz
    have hn : ‖z‖ < R₀ := lt_of_not_ge fun h => hΨz (hsupport s hs z hz h)
    have hb : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      exact hn.trans_le hR₀
    exact (hZ z hb).mp hz
  obtain ⟨S, hSb, hSz, hSs⟩ := exists_zeroSet_zeroSumBall hR
    (by linarith only [hR] : R < 2 * R) isOpen_univ (subset_univ _) hf.differentiableOn hRsph
  have hbase := hrep a₀ ha₀ S hSz
  change Tendsto (fun s : ℝ => heatWeightedZeroSum Ψ (max s 0)) (𝓝 t)
    (𝓝 (heatWeightedZeroSum Ψ a₀))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let N : ℝ := (∑ a ∈ S, zeroMult (riemannHeat a₀) a : ℕ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let η := ε / (N + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hηN : η * N < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith only [hε]
  obtain ⟨d, hd, hsep⟩ := exists_pos_sep S
  choose ρ₀ hρ₀ hisolate using fun a => exists_radius_zeroSumBall_riemannHeat_eq ha₀ a
  have hcont : ∀ a : ℂ, ∃ δ > 0, ∀ z, dist z a < δ → |Ψ z - Ψ a| < η := by
    intro a
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hΨ a η hη
    exact ⟨δ, hδ, fun z hz => by simpa only [Real.dist_eq] using h z hz⟩
  choose δ hδ hosc using hcont
  let r : ℂ → ℝ := fun a => min (min (ρ₀ a) (d / 3)) (min (δ a) ((R - dist a 0) / 2))
  have hr₀ (a : ℂ) : r a ≤ ρ₀ a := (min_le_left _ _).trans (min_le_left _ _)
  have hrd (a : ℂ) : r a ≤ d / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have hrδ (a : ℂ) : r a ≤ δ a := (min_le_right _ _).trans (min_le_left _ _)
  have hrR (a : ℂ) : r a ≤ (R - dist a 0) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hr : ∀ a ∈ S, 0 < r a := by
    intro a ha
    have hb := mem_ball.mp (hSb a ha)
    exact lt_min (lt_min (hρ₀ a) (by positivity)) (lt_min (hδ a) (by linarith only [hb]))
  have hinside : ∀ a ∈ S, ball a (r a) ⊆ ball (0 : ℂ) R := by
    intro a ha z hz
    have h1 := mem_ball.mp hz
    have h2 := mem_ball.mp (hSb a ha)
    have h3 := dist_triangle z a 0
    apply mem_ball.mpr
    linarith only [h1, h2, h3, hrR a]
  have hsmall : ∀ a ∈ S, ∀ᶠ s in 𝓝 t,
      zeroSumBall (riemannHeat (max s 0)) a (r a) = (zeroMult (riemannHeat a₀) a : ℂ) ∧
      ∀ z ∈ sphere a (r a), riemannHeat (max s 0) z ≠ 0 := by
    intro a ha
    obtain ⟨hsph, hcount⟩ := hisolate a (r a) (hr a ha) (hr₀ a)
    have he := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hf hconv (hr a ha)
      (by linarith only [hr a ha] : r a < 2 * r a) hsph
    have hn := eventually_ne_zero_on_sphere hf.continuous hconv (hr a ha).le hsph
    filter_upwards [he, hn] with s hs hn
    exact ⟨hs.trans hcount, hn⟩
  have hbig := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hf hconv hR
    (by linarith only [hR] : R < 2 * R) hRsph
  have hbigfree := eventually_ne_zero_on_sphere hf.continuous hconv hR.le hRsph
  filter_upwards [(Filter.eventually_all_finset S).mpr hsmall, hbig, hbigfree] with s hs hbig hfree
  let τ := max s 0
  have hτ : 0 ≤ τ := le_max_right _ _
  obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hR
    (by linarith only [hR] : R < 2 * R) isOpen_univ (subset_univ _)
    (differentiable_riemannHeat hτ).differentiableOn hfree
  have hnew := hrep τ hτ Z hZz
  let U : ℂ → Finset ℂ := fun a => Z.filter (fun z => z ∈ ball a (r a))
  have hUsub : ∀ a ∈ S, U a ⊆ Z := fun _ _ => Finset.filter_subset _ _
  have hUcount : ∀ a ∈ S, ∑ z ∈ U a, zeroMult (riemannHeat τ) z = zeroMult (riemannHeat a₀) a := by
    intro a ha
    obtain ⟨V, hVb, hVz, hVs⟩ := exists_zeroSet_zeroSumBall (hr a ha)
      (by linarith only [hr a ha] : r a < 2 * r a) isOpen_univ (subset_univ _)
      (differentiable_riemannHeat hτ).differentiableOn (hs a ha).2
    have hUV : U a = V := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzZ, hza⟩ := Finset.mem_filter.mp hz
        exact (hVz z hza).mp ((hZz z (hZb z hzZ)).mpr hzZ)
      · intro hz
        have hza := hVb z hz
        exact Finset.mem_filter.mpr ⟨(hZz z (hinside a ha hza)).mp
          ((hVz z hza).mpr hz), hza⟩
    rw [hUV]
    have hc : ((∑ z ∈ V, zeroMult (riemannHeat τ) z : ℕ) : ℂ) =
        (zeroMult (riemannHeat a₀) a : ℂ) := by
      push_cast
      exact hVs.symm.trans (hs a ha).1
    exact_mod_cast hc
  have hUdisj : (S : Set ℂ).PairwiseDisjoint U := by
    intro a ha a' ha' hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have h1 := mem_ball.mp (Finset.mem_filter.mp hz).2
    have h2 := mem_ball.mp (Finset.mem_filter.mp hz').2
    have h3 := dist_triangle a z a'
    rw [dist_comm a z] at h3
    have h4 := hsep a ha a' ha' hne
    linarith only [h1, h2, h3, h4, hrd a, hrd a', hd]
  have htotal : ∑ z ∈ Z, zeroMult (riemannHeat τ) z = ∑ a ∈ S, zeroMult (riemannHeat a₀) a := by
    have hc : ((∑ z ∈ Z, zeroMult (riemannHeat τ) z : ℕ) : ℂ) =
        ((∑ a ∈ S, zeroMult (riemannHeat a₀) a : ℕ) : ℂ) := by
      push_cast
      exact hZs.symm.trans (hbig.trans hSs)
    exact_mod_cast hc
  have hexhaust := zero_clusters_exhaust_of_count_eq hUsub hUdisj hUcount htotal
    (fun z hz => one_le_zeroMult_riemannHeat hτ ((hZz z (hZb z hz)).mpr hz))
  have hweight : ∀ a ∈ S, ∀ z ∈ U a, |Ψ z - Ψ a| ≤ η := by
    intro a _ z hz
    have hb := mem_ball.mp (Finset.mem_filter.mp hz).2
    exact (hosc a z (hb.trans_le (hrδ a))).le
  have he := weighted_zero_clusters_error_le hexhaust hUdisj hUcount hweight
  rw [Real.dist_eq, hnew, hbase]
  have he' : |(∑ z ∈ Z, (zeroMult (riemannHeat τ) z : ℝ) * Ψ z) -
      ∑ a ∈ S, (zeroMult (riemannHeat a₀) a : ℝ) * Ψ a| ≤ η * N := by
    simpa only [N, Nat.cast_sum] using he
  exact he'.trans_lt hηN

/-- Vertical energy localized by a horizontal weight, with full zero
multiplicity at every time. -/
def heatLocalizedVerticalEnergy (X : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => w (z.re - X) * z.im ^ 2) t

/-- A continuous compactly supported horizontal weight gives continuous
localized vertical energy, including the right-hand limit at time zero. -/
theorem continuousOn_heatLocalizedVerticalEnergy {w : ℝ → ℝ}
    (hw : Continuous w) (hcompact : HasCompactSupport w) (X : ℝ) :
    ContinuousOn (heatLocalizedVerticalEnergy X w) (Ici 0) := by
  obtain ⟨B, hB⟩ := hcompact.isCompact.isBounded.exists_norm_le
  have hΨ : Continuous (fun z : ℂ => w (z.re - X) * z.im ^ 2) := by fun_prop
  have hsupport : ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, riemannHeat s z = 0 →
      |X| + |B| + 1 ≤ ‖z‖ → w (z.re - X) * z.im ^ 2 = 0 := by
    intro s hs z hz hnorm
    by_cases hwz : w (z.re - X) = 0
    · rw [hwz, zero_mul]
    exfalso
    have hb := hB (z.re - X) ((subset_tsupport w) hwz)
    rw [Real.norm_eq_abs] at hb
    have hre := abs_add_le (z.re - X) X
    rw [sub_add_cancel] at hre
    have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs hz
    have hle := Complex.norm_le_abs_re_add_abs_im z
    have hBabs := le_abs_self B
    linarith only [hnorm, hb, hre, him, hle, hBabs]
  have hc := continuous_heatWeightedZeroSum_clamped_of_support hΨ (|X| + |B| + 1) hsupport
  refine hc.continuousOn.congr ?_
  intro t ht
  change heatWeightedZeroSum _ t = heatWeightedZeroSum _ (max t 0)
  rw [max_eq_left ht]

end

end RHTower.DeBruijn
