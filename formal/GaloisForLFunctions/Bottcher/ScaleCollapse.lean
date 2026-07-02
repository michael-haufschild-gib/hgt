/-
# The scale collapse: ∀ρ-preconnectivity from one fundamental period

Pure plane topology.  Given a set `P` (the Julia pullback in linearizing coordinates) that is
invariant under the real multiplier `λ ≥ 2`, disjoint from the scale-closed sector
`{Re v > ‖v‖/2}`, and admitting sector connectors on ONE multiplicative period of scales, the
punctured-ball preconnectivity holds at ALL scales: every `{‖v‖ < ρ} ∖ P` is preconnected.
This is the ∀ρ-quantifier elimination that the dendrite-tip clause `htip` needs — the whole
point of the Koenigs linearization route.
-/
import GaloisForLFunctions.Bottcher.KoenigsLinearization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

open Complex Set Metric

namespace Bottcher

/-- Iterated multiplier invariance, staying inside the working scale. -/
theorem scale_inv_pow {P : Set ℂ} {lam ρ₀ : ℝ} (hlam : 2 ≤ lam) (hρ₀ : 0 < ρ₀)
    (hinv : ∀ v : ℂ, lam * ‖v‖ ≤ ρ₀ → (((lam : ℂ) * v ∈ P) ↔ v ∈ P)) :
    ∀ m : ℕ, ∀ v : ℂ, lam ^ m * ‖v‖ ≤ ρ₀ → ((((lam : ℝ) ^ m : ℝ) : ℂ) * v ∈ P ↔ v ∈ P) := by
  intro m
  induction m with
  | zero =>
      intro v _
      simp
  | succ k ih =>
      intro v hv
      have hlam0 : (0:ℝ) < lam := by linarith
      have hpow0 : (0:ℝ) < lam ^ k := pow_pos hlam0 k
      have h1 : lam ^ k * ‖v‖ ≤ ρ₀ := by
        have h2 : lam ^ k * ‖v‖ ≤ lam ^ (k+1) * ‖v‖ := by
          have h3 : lam ^ k ≤ lam ^ (k+1) := by
            apply pow_le_pow_right₀ (by linarith) (by omega)
          apply mul_le_mul_of_nonneg_right h3 (norm_nonneg v)
        linarith
      have h4 : lam * ‖(((lam : ℝ) ^ k : ℝ) : ℂ) * v‖ ≤ ρ₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
        calc lam * (lam ^ k * ‖v‖) = lam ^ (k+1) * ‖v‖ := by ring
          _ ≤ ρ₀ := hv
      have h5 := hinv ((((lam : ℝ) ^ k : ℝ) : ℂ) * v) h4
      have h6 : ((lam : ℂ)) * ((((lam : ℝ) ^ k : ℝ) : ℂ) * v)
          = ((((lam : ℝ) ^ (k+1) : ℝ) : ℂ) * v) := by
        push_cast
        ring
      rw [h6] at h5
      exact h5.trans (ih v h1)

/-- **The scale collapse.**  Sector connectors on one multiplicative period of scales, plus
multiplier invariance, give punctured-ball preconnectivity at every scale `ρ ≤ ρ₀`. -/
theorem preconnected_of_scale_connectors
    (P : Set ℂ) (lam ρ₀ : ℝ) (hlam : 2 ≤ lam) (hρ₀ : 0 < ρ₀)
    (hinv : ∀ v : ℂ, lam * ‖v‖ ≤ ρ₀ → (((lam : ℂ) * v ∈ P) ↔ v ∈ P))
    (hSP : ∀ v : ℂ, ‖v‖ ≤ ρ₀ → ‖v‖ / 2 < v.re → v ∉ P)
    (h0P : (0:ℂ) ∈ P)
    (hfund : ∀ r : ℝ, ρ₀ / lam ≤ r → r ≤ ρ₀ → ∀ v : ℂ, v ∉ P →
      r / lam ^ 2 ≤ ‖v‖ → ‖v‖ < r →
      ∃ C : Set ℂ, IsPreconnected C ∧ v ∈ C ∧ (∃ u ∈ C, ‖u‖ / 2 < u.re) ∧
        ∀ u ∈ C, u ∉ P ∧ ‖u‖ < r) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → IsPreconnected {v : ℂ | ‖v‖ < ρ ∧ v ∉ P} := by
  classical
  have hlam0 : (0:ℝ) < lam := by linarith
  -- Step 1: extend the connector supply to ALL scales r ≤ ρ₀ by one scaling jump.
  have hfund_all : ∀ r : ℝ, 0 < r → r ≤ ρ₀ → ∀ v : ℂ, v ∉ P →
      r / lam ^ 2 ≤ ‖v‖ → ‖v‖ < r →
      ∃ C : Set ℂ, IsPreconnected C ∧ v ∈ C ∧ (∃ u ∈ C, ‖u‖ / 2 < u.re) ∧
        ∀ u ∈ C, u ∉ P ∧ ‖u‖ < r := by
    intro r hr hrρ₀ v hvP hvlo hvhi
    -- find the least m with lam^m * r in the period [ρ₀/lam, ρ₀]
    have hex : ∃ m : ℕ, ρ₀ / lam ≤ lam ^ m * r := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (ρ₀ / lam / r) (by linarith : (1:ℝ) < lam)
      exact ⟨m, by
        rw [div_lt_iff₀ hr] at hm
        linarith⟩
    set m := Nat.find hex with hmdef
    have hmspec : ρ₀ / lam ≤ lam ^ m * r := Nat.find_spec hex
    have hmtop : lam ^ m * r ≤ ρ₀ := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0]
        simpa using hrρ₀
      · have hprev : ¬ (ρ₀ / lam ≤ lam ^ (m - 1) * r) := Nat.find_min hex (by omega)
        push Not at hprev
        have h1 : lam ^ m = lam * lam ^ (m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h1, mul_assoc]
        calc lam * (lam ^ (m - 1) * r) ≤ lam * (ρ₀ / lam) := by
              apply mul_le_mul_of_nonneg_left (le_of_lt hprev) (le_of_lt hlam0)
          _ = ρ₀ := by field_simp
    -- the scaled point in the period shell
    set V : ℂ := ((lam ^ m : ℝ) : ℂ) * v with hVdef
    have hpow0 : (0:ℝ) < lam ^ m := pow_pos hlam0 m
    have hVnorm : ‖V‖ = lam ^ m * ‖v‖ := by
      rw [hVdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
    have hVP : V ∉ P := by
      intro hcon
      have h2 : lam ^ m * ‖v‖ ≤ ρ₀ := by
        calc lam ^ m * ‖v‖ ≤ lam ^ m * r := by
              apply mul_le_mul_of_nonneg_left (le_of_lt hvhi) (le_of_lt hpow0)
          _ ≤ ρ₀ := hmtop
      exact hvP ((scale_inv_pow hlam hρ₀ hinv m v h2).mp hcon)
    have hVlo : (lam ^ m * r) / lam ^ 2 ≤ ‖V‖ := by
      rw [hVnorm]
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hvlo
      nlinarith [pow_pos hlam0 m, pow_pos hlam0 2]
    have hVhi : ‖V‖ < lam ^ m * r := by
      rw [hVnorm]
      apply mul_lt_mul_of_pos_left hvhi hpow0
    obtain ⟨C, hCpre, hVC, ⟨u₀, hu₀C, hu₀sec⟩, hCprop⟩ :=
      hfund (lam ^ m * r) hmspec hmtop V hVP hVlo hVhi
    -- scale the connector back down
    refine ⟨(fun u => ((lam ^ m : ℝ) : ℂ)⁻¹ * u) '' C, ?_, ?_, ?_, ?_⟩
    · apply hCpre.image
      exact (continuous_const.mul continuous_id).continuousOn
    · refine ⟨V, hVC, ?_⟩
      rw [hVdef]
      have h3 : (((lam ^ m : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast ne_of_gt hpow0
      field_simp
    · refine ⟨((lam ^ m : ℝ) : ℂ)⁻¹ * u₀, ⟨u₀, hu₀C, rfl⟩, ?_⟩
      have h4 : ‖((lam ^ m : ℝ) : ℂ)⁻¹ * u₀‖ = (lam ^ m)⁻¹ * ‖u₀‖ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
      have h5 : (((lam ^ m : ℝ) : ℂ)⁻¹ * u₀).re = (lam ^ m)⁻¹ * u₀.re := by
        have h6 : (((lam ^ m : ℝ) : ℂ))⁻¹ = (((lam ^ m)⁻¹ : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [h6, Complex.re_ofReal_mul]
      rw [h4, h5]
      have h7 : (0:ℝ) < (lam ^ m)⁻¹ := by positivity
      calc (lam ^ m)⁻¹ * ‖u₀‖ / 2 = (lam ^ m)⁻¹ * (‖u₀‖ / 2) := by ring
        _ < (lam ^ m)⁻¹ * u₀.re := by
            apply mul_lt_mul_of_pos_left hu₀sec h7
    · rintro u ⟨w, hwC, rfl⟩
      obtain ⟨hwP, hwr⟩ := hCprop w hwC
      constructor
      · intro hcon
        have h8 : lam ^ m * ‖((lam ^ m : ℝ) : ℂ)⁻¹ * w‖ ≤ ρ₀ := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
          have h9 : lam ^ m * ((lam ^ m)⁻¹ * ‖w‖) = ‖w‖ := by
            field_simp
          rw [h9]
          calc ‖w‖ ≤ lam ^ m * r := le_of_lt hwr
            _ ≤ ρ₀ := hmtop
        have h10 := (scale_inv_pow hlam hρ₀ hinv m _ h8).mpr hcon
        have h11 : (((lam ^ m : ℝ) : ℂ)) * (((lam ^ m : ℝ) : ℂ)⁻¹ * w) = w := by
          have h12 : (((lam ^ m : ℝ) : ℂ)) ≠ 0 := by
            exact_mod_cast ne_of_gt hpow0
          field_simp
        rw [h11] at h10
        exact hwP h10
      · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
        rw [inv_mul_lt_iff₀ hpow0]
        calc ‖w‖ < lam ^ m * r := hwr
          _ = lam ^ m * r := rfl
  -- Step 2: the union argument at scale ρ
  intro ρ hρ hρρ₀
  set S : Set ℂ := {v : ℂ | ‖v‖ < ρ ∧ v ∉ P} with hSdef
  set B : Set ℂ := {v : ℂ | ‖v‖ < ρ ∧ ‖v‖ / 2 < v.re} with hBdef
  have hBS : B ⊆ S := by
    rintro v ⟨h1, h2⟩
    exact ⟨h1, hSP v (by linarith) h2⟩
  have hBconv : Convex ℝ B := by
    have h3 : B = {v : ℂ | ‖v‖ < ρ} ∩ {v : ℂ | ‖v‖ / 2 < v.re} := rfl
    rw [h3]
    apply Convex.inter _ sector_convex
    have h4 : {v : ℂ | ‖v‖ < ρ} = Metric.ball 0 ρ := by
      ext v
      simp [Metric.mem_ball, dist_zero_right]
    rw [h4]
    exact convex_ball 0 ρ
  have hb₀ : ((ρ/2 : ℝ) : ℂ) ∈ B := by
    constructor
    · show ‖((ρ/2 : ℝ) : ℂ)‖ < ρ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show ‖((ρ/2 : ℝ) : ℂ)‖ / 2 < ((ρ/2 : ℝ) : ℂ).re
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
        Complex.ofReal_re]
      linarith
  -- every point of S admits a preconnected subset of S containing it and meeting B
  have hconn : ∀ v ∈ S, ∃ C : Set ℂ, C ⊆ S ∧ IsPreconnected C ∧ v ∈ C ∧ (C ∩ B).Nonempty := by
    rintro v ⟨hvρ, hvP⟩
    by_cases hvsec : ‖v‖ / 2 < v.re
    · exact ⟨B, hBS, hBconv.isPreconnected, ⟨hvρ, hvsec⟩, ⟨_, hb₀, hb₀⟩⟩
    · -- v is not in the sector; in particular v ≠ 0 would still be fine, but we need ‖v‖ > 0
      have hv0 : v ≠ 0 := by
        rintro rfl
        exact hvP h0P
      have hvnorm : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
      -- choose the working scale
      rcases le_or_gt (ρ / lam ^ 2) ‖v‖ with hcase | hcase
      · -- outer shell: scale ρ directly
        obtain ⟨C, hCpre, hvC, ⟨u₀, hu₀C, hu₀sec⟩, hCprop⟩ :=
          hfund_all ρ hρ hρρ₀ v hvP hcase hvρ
        refine ⟨C, ?_, hCpre, hvC, ⟨u₀, hu₀C, (hCprop u₀ hu₀C).2, hu₀sec⟩⟩
        intro u huC
        exact ⟨(hCprop u huC).2, (hCprop u huC).1⟩
      · -- inner: scale lam * ‖v‖
        have hr : (0:ℝ) < lam * ‖v‖ := by positivity
        have hrρ₀ : lam * ‖v‖ ≤ ρ₀ := by
          have h5 : lam * ‖v‖ < lam * (ρ / lam ^ 2) := by
            apply mul_lt_mul_of_pos_left hcase hlam0
          have h6 : lam * (ρ / lam ^ 2) = ρ / lam := by
            field_simp
          rw [h6] at h5
          have h7 : ρ / lam ≤ ρ := by
            rw [div_le_iff₀ hlam0]
            nlinarith
          linarith
        have hlo : (lam * ‖v‖) / lam ^ 2 ≤ ‖v‖ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        have hhi : ‖v‖ < lam * ‖v‖ := by nlinarith
        obtain ⟨C, hCpre, hvC, ⟨u₀, hu₀C, hu₀sec⟩, hCprop⟩ :=
          hfund_all (lam * ‖v‖) hr hrρ₀ v hvP hlo hhi
        have hsub : ∀ u ∈ C, ‖u‖ < ρ := by
          intro u huC
          have h8 := (hCprop u huC).2
          have h9 : lam * ‖v‖ < lam * (ρ / lam ^ 2) := by
            apply mul_lt_mul_of_pos_left hcase hlam0
          have h10 : lam * (ρ / lam ^ 2) = ρ / lam := by
            field_simp
          rw [h10] at h9
          have h11 : ρ / lam ≤ ρ := by
            rw [div_le_iff₀ hlam0]
            nlinarith
          linarith
        refine ⟨C, ?_, hCpre, hvC, ⟨u₀, hu₀C, hsub u₀ hu₀C, hu₀sec⟩⟩
        intro u huC
        exact ⟨hsub u huC, (hCprop u huC).1⟩
  -- assemble via pairwise common preconnected subsets through B
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨Cx, hCxS, hCxpre, hxCx, ⟨bx, hbxCx, hbxB⟩⟩ := hconn x hx
  obtain ⟨Cy, hCyS, hCypre, hyCy, ⟨by', hbyCy, hbyB⟩⟩ := hconn y hy
  refine ⟨(Cx ∪ B) ∪ Cy, ?_, ?_, ?_, ?_⟩
  · apply Set.union_subset (Set.union_subset hCxS hBS) hCyS
  · exact Set.mem_union_left _ (Set.mem_union_left _ hxCx)
  · exact Set.mem_union_right _ hyCy
  · have h1 : IsPreconnected (Cx ∪ B) :=
      IsPreconnected.union bx hbxCx hbxB hCxpre hBconv.isPreconnected
    apply IsPreconnected.union by' _ hbyCy h1 hCypre
    exact Set.mem_union_right _ hbyB

end Bottcher

namespace Bottcher

/-- **The linearizer is a local homeomorphism at the fixed point**: injective on a small disk,
with nonvanishing derivative there, and mapping open subsets to open sets.  The coordinate
transfer toolkit for the tip clause. -/
theorem koenigsFun_localHomeo {c β : ℂ} (hβ : β ^ 2 + c = β) (hlam2 : 2 ≤ ‖2 * β‖) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 64 ∧
      Set.InjOn (koenigsFun c β) (Metric.ball 0 r) ∧
      (∀ s : Set ℂ, s ⊆ Metric.ball 0 r → IsOpen s → IsOpen (koenigsFun c β '' s)) := by
  classical
  have hψan := koenigsFun_analyticOnNhd hβ hlam2
  have hψ0 : AnalyticAt ℂ (koenigsFun c β) 0 :=
    hψan 0 (Metric.mem_ball_self (by norm_num))
  have hd0 : HasDerivAt (koenigsFun c β) 1 0 := koenigsFun_hasDerivAt_zero hβ hlam2
  have hstrict : HasStrictDerivAt (koenigsFun c β) 1 0 := by
    have h1 := hψ0.hasStrictDerivAt
    rwa [hd0.deriv] at h1
  -- the left inverse gives injectivity near 0
  have hinj_ev := HasStrictDerivAt.eventually_left_inverse hstrict
    (by norm_num : (1:ℂ) ≠ 0)
  -- the derivative is analytic, equals 1 at 0, hence nonzero nearby
  have hderiv_an : AnalyticOnNhd ℂ (deriv (koenigsFun c β)) (Metric.ball (0:ℂ) (1/32)) :=
    hψan.deriv
  have hderiv_cont : ContinuousAt (deriv (koenigsFun c β)) 0 :=
    (hderiv_an 0 (Metric.mem_ball_self (by norm_num))).continuousAt
  have hderiv_ne : ∀ᶠ v in nhds (0:ℂ), deriv (koenigsFun c β) v ≠ 0 := by
    have h2 : deriv (koenigsFun c β) 0 = 1 := hd0.deriv
    have h3 : ({(0:ℂ)}ᶜ : Set ℂ) ∈ nhds (deriv (koenigsFun c β) 0) := by
      rw [h2]
      exact compl_singleton_mem_nhds (by norm_num)
    have h4 := hderiv_cont.preimage_mem_nhds h3
    filter_upwards [h4] with v hv
    simpa using hv
  -- extract a working radius
  obtain ⟨r₁, hr₁, hr₁inj⟩ := Metric.eventually_nhds_iff_ball.mp hinj_ev
  obtain ⟨r₂, hr₂, hr₂ne⟩ := Metric.eventually_nhds_iff_ball.mp hderiv_ne
  set r : ℝ := min (min r₁ r₂) (1/64) with hrdef
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) (by norm_num)
  refine ⟨r, hr0, min_le_right _ _, ?_, ?_⟩
  · -- injectivity via the left inverse
    intro x hx y hy hxy
    have hx1 : x ∈ Metric.ball (0:ℂ) r₁ :=
      Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hx
    have hy1 : y ∈ Metric.ball (0:ℂ) r₁ :=
      Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hy
    have h5 := hr₁inj x hx1
    have h6 := hr₁inj y hy1
    rw [← h5, ← h6, hxy]
  · -- open mapping via per-point strict derivative and map_nhds_eq
    intro s hs hso
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨v, hvs, rfl⟩
    have hvball : v ∈ Metric.ball (0:ℂ) (1/32) := by
      have h7 := hs hvs
      rw [Metric.mem_ball, dist_zero_right] at h7 ⊢
      have h8 : r ≤ 1/64 := min_le_right _ _
      linarith
    have hvan : AnalyticAt ℂ (koenigsFun c β) v := hψan v hvball
    have hvderiv : deriv (koenigsFun c β) v ≠ 0 := by
      apply hr₂ne
      exact Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_right _ _)) (hs hvs)
    have hvstrict : HasStrictDerivAt (koenigsFun c β) (deriv (koenigsFun c β) v) v :=
      hvan.hasStrictDerivAt
    have hmap := hvstrict.map_nhds_eq hvderiv
    rw [← hmap]
    exact Filter.image_mem_map (hso.mem_nhds hvs)

end Bottcher
