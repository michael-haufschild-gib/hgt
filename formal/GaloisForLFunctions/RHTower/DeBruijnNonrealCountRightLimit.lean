import GaloisForLFunctions.RHTower.DeBruijnNonrealCountFinitenessTransition
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.XiZeroCountingFunction

/-!
# The nonreal count of `H_t` as `t → 0⁺`

The nonreal zero count `N(t)` of the de Bruijn–Newman flow is right-continuous at `t = 0`:
* every finite set of nonreal zeros of `Ξ = H_0` survives, with multiplicity, for all small
  `t > 0`, by Hurwitz on isolating discs off the real axis;
* if `Ξ` has infinitely many nonreal zeros then `N(t) → ∞` as `t → 0⁺`;
* if `Ξ` has finitely many, `K` with multiplicity, then `N(t) = K` for all small `t > 0`
  (the upper bound is the finiteness transition).

Consequently RH holds iff `N(t) = 0` for all sufficiently small `t > 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

/-! ## Continuity at `t = 0` from the right -/

/-- `H_s → H_0` locally uniformly as `s → 0⁺` (the time is clamped at `0`, which changes nothing
for `s > 0`). -/
theorem tendstoLocallyUniformly_riemannHeat_max_zero :
    TendstoLocallyUniformly (fun s : ℝ => riemannHeat (max s 0)) (riemannHeat 0) (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set I := ∫ x, |x| ^ (2 * 1) * ‖heatWeight (0 + 1) x‖ * Real.exp (|R| * |x|) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < min 1 (ε / (I + 1)) := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs z hz
  obtain ⟨hs0, hs1⟩ := hs
  have hsabs : |s| = s := abs_of_pos hs0
  have hT := norm_riemannHeat_time_taylor_le (le_refl (0 : ℝ)) (h := s) (by linarith)
    (by rw [hsabs]; exact hs1.le.trans (min_le_left _ _)) 1 z
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_mul, zero_add, pow_one] at hT
  have hKle : (∫ x, |x| ^ (2 * 1) * ‖heatWeight (0 + 1) x‖ * Real.exp (|z.im| * |x|)) ≤ I := by
    refine integral_mono (integrable_pow_mul_heatWeight (by norm_num) _ _)
      (integrable_pow_mul_heatWeight (by norm_num) _ _) fun x => ?_
    have him : |z.im| ≤ |R| := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_abs_self R))
    dsimp only
    gcongr
  rw [max_eq_left hs0.le, dist_eq_norm, norm_sub_rev]
  rw [zero_add] at hKle
  calc ‖riemannHeat s z - riemannHeat 0 z‖
      ≤ (∫ x, |x| ^ (2 * 1) * ‖heatWeight 1 x‖ * Real.exp (|z.im| * |x|)) * |s| := hT
    _ ≤ I * (ε / (I + 1)) := by
        rw [hsabs]
        gcongr
        exact hs1.le.trans (min_le_right _ _)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-! ## Nonreal zeros of `Ξ` survive for small positive time -/

/-- **Lower semicontinuity at `t = 0`.** Every finite set of nonreal zeros of `H_0` is carried, with
multiplicity, by the nonreal count of `H_s` for all small `s > 0`. -/
theorem eventually_sum_zeroMult_le_nonrealZeroCount {E : Finset ℂ}
    (hE : ∀ e ∈ E, riemannHeat 0 e = 0 ∧ e.im ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∑ e ∈ E, zeroMult (riemannHeat 0) e ≤ nonrealZeroCount s := by
  classical
  choose ρ₀ hρ₀ hρ₀prop using fun e => exists_radius_zeroSumBall_riemannHeat_eq (le_refl (0 : ℝ)) e
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  set r : ℂ → ℝ := fun e => min (ρ₀ e) (min (|e.im| / 2) (d / 3)) with hrdef
  have hrpos : ∀ e ∈ E, 0 < r e := fun e he =>
    lt_min (hρ₀ e) (lt_min (by have := abs_pos.mpr (hE e he).2; linarith) (by linarith))
  have havoid : ∀ e ∈ E, ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e he w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have hr2 : r e ≤ |e.im| / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hpos := abs_pos.mpr (hE e he).2
    linarith
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set F : ℝ → ℂ → ℂ := fun s => riemannHeat (max s 0) with hFdef
  have hF : ∀ s, Differentiable ℂ (F s) := fun s => differentiable_riemannHeat (le_max_right _ _)
  have hdiff0 := differentiable_riemannHeat (le_refl (0 : ℝ))
  have hev : ∀ e ∈ E, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      zeroSumBall (F s) e (r e) = (zeroMult (riemannHeat 0) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), F s w ≠ 0 := by
    intro e he
    obtain ⟨hsph, hcount⟩ := hρ₀prop e (r e) (hrpos e he) (min_le_left _ _)
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hdiff0
      tendstoLocallyUniformly_riemannHeat_max_zero (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere hdiff0.continuous
      tendstoLocallyUniformly_riemannHeat_max_zero (hrpos e he).le hsph
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨by rw [hs1, hcount], hs2⟩
  filter_upwards [(Filter.eventually_all_finset E).mpr hev, self_mem_nhdsWithin] with s hs hs0
  have hFs : F s = riemannHeat s := by
    simp only [hFdef, max_eq_left (le_of_lt (Set.mem_Ioi.mp hs0))]
  exact (sum_le_nonrealZeroCount (Set.mem_Ioi.mp hs0) hrpos havoid hdisj
    (fun e he => by rw [← hFs]; exact (hs e he).2)
    (fun e he => by rw [← hFs]; exact (hs e he).1)).1

/-- If `Ξ` has infinitely many nonreal zeros, then `N(t) → ∞` as `t → 0⁺`. -/
theorem tendsto_nonrealZeroCount_atTop_of_infinite
    (hinf : {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Infinite) :
    Tendsto nonrealZeroCount (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨E, hEsub, hEcard⟩ := hinf.exists_subset_card_eq M
  filter_upwards [eventually_sum_zeroMult_le_nonrealZeroCount (E := E) fun e he => hEsub he]
    with s hs
  calc M = ∑ _e ∈ E, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hEcard]
    _ ≤ ∑ e ∈ E, zeroMult (riemannHeat 0) e :=
        Finset.sum_le_sum fun e he => one_le_zeroMult_riemannHeat le_rfl (hEsub he).1
    _ ≤ nonrealZeroCount s := hs

/-! ## Multiplicity copies and zero multiplicities of `Ξ` -/

theorem riemannHeat_zero_eq_XiC : riemannHeat 0 = XiC := by
  funext z
  rw [riemannHeat_zero, XiC, mul_comm I z]

theorem xiSpectralPoint_eq_iff (q q' : XiZeroCopy) :
    xiSpectralPoint q = xiSpectralPoint q' ↔ q.1 = q'.1 := by
  constructor
  · intro h
    rw [xiSpectralPoint, xiSpectralPoint] at h
    have h' := mul_right_cancel₀ (neg_ne_zero.mpr I_ne_zero) h
    exact Subtype.ext (sub_left_inj.mp h')
  · intro h
    rw [xiSpectralPoint, xiSpectralPoint, h]

/-- The multiplicity of `Ξ` at a centred zero is the number of its divisor copies. -/
theorem zeroMult_riemannHeat_zero_xiSpectralPoint (q : XiZeroCopy) :
    zeroMult (riemannHeat 0) (xiSpectralPoint q) =
      ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ)).toNat := by
  rw [riemannHeat_zero_eq_XiC, zeroMult, xiSpectralPoint, analyticOrderAt_XiC_centeredCoordinate,
    xi_divisor_apply_of_mem (Set.mem_univ _), Int.toNat_natCast]

/-- The number of nonreal multiplicity copies is the multiplicity sum over the nonreal zeros of
`Ξ`. -/
theorem card_nonrealCopies_eq_sum_zeroMult
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    hfin.toFinset.card =
      ∑ e ∈ hfin.toFinset.image xiSpectralPoint, zeroMult (riemannHeat 0) e := by
  classical
  rw [Finset.card_eq_sum_card_image xiSpectralPoint]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp he
  have hfib : {q ∈ hfin.toFinset | xiSpectralPoint q = xiSpectralPoint q₀} =
      ({q₀.1} : Finset XiDivisorSupport).sigma fun _ => Finset.univ := by
    ext q
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_sigma,
      Finset.mem_singleton, Finset.mem_univ, and_true]
    rw [xiSpectralPoint_eq_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h1 : xiSpectralPoint q = xiSpectralPoint q₀ := (xiSpectralPoint_eq_iff q q₀).mpr h
      rw [h1]
      exact (Set.Finite.mem_toFinset hfin).mp hq₀
  rw [hfib, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin,
    zeroMult_riemannHeat_zero_xiSpectralPoint]

/-! ## Right-continuity of the count -/

/-- **Right-continuity at `t = 0`, finite case.** If `Ξ` has finitely many nonreal zeros, `K` of
them with multiplicity, then `N(t) = K` for all sufficiently small `t > 0`. -/
theorem eventually_nonrealZeroCount_eq_of_finite
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), nonrealZeroCount s = hfin.toFinset.card := by
  have hE : ∀ e ∈ hfin.toFinset.image xiSpectralPoint, riemannHeat 0 e = 0 ∧ e.im ≠ 0 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    refine ⟨by rw [riemannHeat_zero_eq_XiC]; exact XiC_xiSpectralPoint_eq_zero q, ?_⟩
    exact (Set.Finite.mem_toFinset hfin).mp hq
  filter_upwards [eventually_sum_zeroMult_le_nonrealZeroCount hE, self_mem_nhdsWithin]
    with s hs hs0
  refine le_antisymm (nonrealZeroCount_le_of_finite_nonreal_zeros hfin (Set.mem_Ioi.mp hs0)) ?_
  rw [card_nonrealCopies_eq_sum_zeroMult hfin]
  exact hs

/-- **RH through the right limit of the count.** RH holds iff `H_t` has only real zeros for all
sufficiently small `t > 0`. -/
theorem riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero :
    RiemannHypothesis ↔ ∀ᶠ s in 𝓝[>] (0 : ℝ), nonrealZeroCount s = 0 := by
  constructor
  · intro hRH
    have hreal := riemannHypothesis_iff_riemannHeat_zero_real.mp hRH
    have hempty : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => hq ?_
      exact hreal _ (by rw [riemannHeat_zero_eq_XiC]; exact XiC_xiSpectralPoint_eq_zero q)
    have hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite := by
      rw [hempty]; exact Set.finite_empty
    filter_upwards [eventually_nonrealZeroCount_eq_of_finite hfin] with s hs
    rw [hs, Finset.card_eq_zero, Set.Finite.toFinset_eq_empty]
    exact hempty
  · intro h
    refine riemannHypothesis_iff_riemannHeat_zero_real.mpr fun z hz => ?_
    by_contra him
    have hlow := eventually_sum_zeroMult_le_nonrealZeroCount (E := {z})
      (fun e he => by rw [Finset.mem_singleton.mp he]; exact ⟨hz, him⟩)
    obtain ⟨s, hs1, hs2⟩ := (hlow.and h).exists
    rw [Finset.sum_singleton, hs2] at hs1
    exact absurd (one_le_zeroMult_riemannHeat le_rfl hz) (by omega)

/-- Finitely many nonreal zeros of `Ξ` give finitely many nonreal multiplicity copies. -/
theorem finite_nonrealCopies_of_finite_zeros
    (hZ : {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite := by
  refine (hZ.preimage' fun e _ => ?_).subset fun q hq => ⟨?_, hq⟩
  · rcases (xiSpectralPoint ⁻¹' {e}).eq_empty_or_nonempty with h | ⟨q₀, hq₀⟩
    · rw [h]
      exact Set.finite_empty
    · refine (Set.finite_range fun i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ))) =>
      (⟨q₀.1, i⟩ : XiZeroCopy)).subset fun q hq => ?_
      have hq' : xiSpectralPoint q = e := hq
      have hq₀' : xiSpectralPoint q₀ = e := hq₀
      have h1 : q.1 = q₀.1 := (xiSpectralPoint_eq_iff q q₀).mp (hq'.trans hq₀'.symm)
      obtain ⟨ρ, i⟩ := q
      simp only at h1
      subst h1
      exact ⟨i, rfl⟩
  · rw [riemannHeat_zero_eq_XiC]
    exact XiC_xiSpectralPoint_eq_zero q

/-- **Finitely many off-line zeros iff a bounded heat count.** `Ξ` has only finitely many nonreal
zeros iff the nonreal counts `N(t)`, `t > 0`, are uniformly bounded. -/
theorem finite_nonreal_zeros_iff_exists_nonrealZeroCount_le :
    {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite ↔
      ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M := by
  constructor
  · intro hZ
    have hfin := finite_nonrealCopies_of_finite_zeros hZ
    exact ⟨hfin.toFinset.card, fun t ht => nonrealZeroCount_le_of_finite_nonreal_zeros hfin ht⟩
  · rintro ⟨M, hM⟩
    by_contra hinf
    have h := (tendsto_nonrealZeroCount_atTop_of_infinite hinf).eventually_ge_atTop (M + 1)
    obtain ⟨s, hs1, hs2⟩ := (h.and self_mem_nhdsWithin).exists
    have := hM s hs2
    omega

end RHTower.DeBruijn
