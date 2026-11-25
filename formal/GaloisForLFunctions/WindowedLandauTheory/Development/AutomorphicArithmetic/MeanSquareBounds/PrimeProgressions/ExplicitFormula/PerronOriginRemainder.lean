import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiDivisorContour
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.WideZeroLocations
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroWindow

/-! The regular part at the origin is controlled by the reciprocal distances to low primitive zeros. -/

open Complex DirichletCharacter Filter Finset Metric Topology

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem erase_origin_sum {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {Z : Finset ℂ}
    (hZ : 0 ∈ Z ↔ f 0 = 0) (s : ℂ) :
    (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) =
      (analyticOrderNatAt f 0 : ℂ) / s +
        ∑ ρ ∈ Z.erase 0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
  classical
  by_cases h : 0 ∈ Z
  · calc
      _ = (∑ ρ ∈ Z.erase 0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) +
          (analyticOrderNatAt f 0 : ℂ) / (s - 0) := (sum_erase_add Z _ h).symm
      _ = _ := by rw [sub_zero, add_comm]
  · have h₀ : f 0 ≠ 0 := fun e => h (hZ.mpr e)
    rw [erase_eq_of_notMem h, analyticOrderNatAt, hf.analyticOrderAt_eq_zero.mpr h₀]
    simp

private theorem norm_local_sum_at_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {Z : Finset ℂ}
    (hZ : (Z : Set ℂ) = {ρ ∈ closedBall (2 : ℂ) (341 / 125) | entireCharacterL χ ρ = 0}) :
    ‖∑ ρ ∈ Z.erase 0, (analyticOrderNatAt (entireCharacterL χ) ρ : ℂ) / (0 - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ)) +
        ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖ := by
  classical
  let E := Z.erase 0
  let B := E.filter fun ρ => |ρ.im| < 1
  let D := E.filter fun ρ => ¬ |ρ.im| < 1
  have hB : ∀ ρ ∈ B, ρ ∈ primitiveInteriorZeros χ 1 := by
    intro ρ hρ
    have hz := (mem_erase.mp (mem_filter.mp hρ).1).2
    change ρ ∈ (Z : Set ℂ) at hz
    rw [hZ] at hz
    have hh := entireCharacterL_zero_mem_strip_or_zero (t := 0) hχ (by simpa using hz.1) hz.2
    have hs := hh.resolve_right (mem_erase.mp (mem_filter.mp hρ).1).1
    have hs₁ : ρ ≠ 1 := fun e => by norm_num [e] at hs
    exact ⟨(entireCharacterL_eq_zero_iff hs₁).1 hz.2, hs, (mem_filter.mp hρ).2⟩
  have hfin := primitiveInteriorZeros_finite hχ 1
  have hD : D ⊆ Z := fun _ h => (mem_erase.mp (mem_filter.mp h).1).2
  let w (ρ : ℂ) : ℝ := (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ) / ‖ρ‖
  have hsmall : ∑ ρ ∈ B, w ρ ≤
      ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖ := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (sum_congr rfl (g := fun ρ => (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖) ?_).le.trans
      (sum_le_sum_of_subset_of_nonneg (fun ρ hρ => hfin.mem_toFinset.mpr (hB ρ hρ)) (fun _ _ _ => by positivity))
    intro ρ hρ
    have hr := (hB ρ hρ).2.1.2
    have hs : ρ ≠ 1 := fun e => by norm_num [e] at hr
    dsimp only [w]
    rw [analyticOrderNatAt_entireCharacterL hs]
  have hlarge : ∑ ρ ∈ D, w ρ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ) := by
    refine (sum_le_sum (g := fun ρ => (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ)) ?_).trans
      (sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => Nat.cast_nonneg _))
    intro ρ hρ
    have hm : 1 ≤ ‖ρ‖ := (le_of_not_gt (mem_filter.mp hρ).2).trans (abs_im_le_norm ρ)
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one hm).trans_eq (div_one _)
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_div, Complex.norm_natCast, zero_sub, norm_neg]
  change ∑ ρ ∈ E, w ρ ≤ _
  rw [← sum_filter_add_sum_filter_not E (fun ρ => |ρ.im| < 1)]
  exact (add_le_add hsmall hlarge).trans_eq (add_comm _ _)

/-- The possible simple zero at the origin contributes a single pole to the logarithmic derivative. -/
theorem primitive_logDeriv_near_origin :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∃ (m : ℕ) (h : ℂ → ℂ), m ≤ 1 ∧ AnalyticAt ℂ h 0 ∧
        (logDeriv χ.LFunction =ᶠ[𝓝[≠] (0 : ℂ)] fun s => (m : ℂ) / s + h s) ∧
        ‖h 0‖ ≤ C * (Real.log (2 * (N : ℝ)) +
          ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖) := by
  obtain ⟨C, hC, H⟩ := entireCharacterL_partial_fraction
  refine ⟨2 * C + 3, by positivity, ?_⟩
  intro N _ χ hχ
  classical
  let f := entireCharacterL χ
  let L := Real.log (2 * (N : ℝ))
  let W := ∑ᶠ ρ ∈ primitiveInteriorZeros χ 1, (analyticOrderNatAt χ.LFunction ρ : ℝ) / ‖ρ‖
  have hW : 0 ≤ W := finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  have ha := (differentiable_entireCharacterL χ).analyticAt
  have ht : analyticOrderAt f 0 ≠ ⊤ := entireCharacterL_order_ne_top
  obtain ⟨g, hg, he⟩ := RiemannGaussian.AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic (ha 0) ht
  let m := analyticOrderNatAt f 0
  have hm : m ≤ 1 := by
    by_cases h : f 0 = 0
    · have hz := (entireCharacterL_eq_zero_iff (χ := χ) (s := 0) (by norm_num)).1 h
      dsimp only [m, f]
      rw [analyticOrderNatAt_entireCharacterL (by norm_num : (0 : ℂ) ≠ 1)]
      exact (eq_zero_and_order_of_primitive_zero_left hχ (by norm_num) (by norm_num) hz).2.le
    · unfold m analyticOrderNatAt
      rw [(ha 0).analyticOrderAt_eq_zero.mpr h]
      simp
  let P (s : ℂ) := if χ = 1 then 1 / (s - 1) else 0
  have hP : AnalyticAt ℂ P 0 := by
    dsimp only [P]
    split_ifs
    · exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
    · exact analyticAt_const
  have hpunct : ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s ≠ 0 :=
    (ha 0).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz => ht (analyticOrderAt_eq_top.mpr hz)
  have hone : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 1 :=
    (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds
  refine ⟨m, fun s => g s - P s, hm, hg.sub hP, ?_, ?_⟩
  · filter_upwards [he, hpunct, hone] with s he hs h₁
    have hn : χ.LFunction s ≠ 0 := fun e => hs ((entireCharacterL_eq_zero_iff h₁).2 e)
    change logDeriv f s = (m : ℂ) / (s - 0) + g s at he
    rw [logDeriv_entireCharacterL h₁ hn, sub_zero] at he
    change logDeriv χ.LFunction s + P s = _ at he
    linear_combination he
  · obtain ⟨Z, hZ, hZmass, hpf⟩ := H N χ 0
    simp only [ofReal_zero, zero_mul, add_zero, abs_zero, zero_add, mul_comm (N : ℝ) 2] at hZ hZmass hpf
    let V (s : ℂ) := ∑ ρ ∈ Z.erase 0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
    have hV : AnalyticAt ℂ V 0 := by
      refine Finset.analyticAt_fun_sum _ (fun ρ hρ => analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_)
      exact sub_ne_zero.mpr (Ne.symm (mem_erase.mp hρ).1)
    have hmem : 0 ∈ Z ↔ f 0 = 0 := by
      change (0 : ℂ) ∈ (Z : Set ℂ) ↔ _
      rw [hZ]
      norm_num [mem_closedBall, Complex.dist_eq, f]
    have hball : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ closedBall (2 : ℂ) (51 / 20) := by
      have h₀ : (0 : ℂ) ∈ ball (2 : ℂ) (51 / 20) := by norm_num [mem_ball, Complex.dist_eq]
      exact nhdsWithin_le_nhds (mem_of_superset (isOpen_ball.mem_nhds h₀) ball_subset_closedBall)
    have hsub : ‖g 0 - V 0‖ ≤ C * L := by
      have hlim : Tendsto (fun s : ℂ => ‖g s - V s‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖g 0 - V 0‖) :=
        (hg.continuousAt.sub hV.continuousAt).norm.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [he, hball, hpunct] with s hs hb hn
      have hh := hpf s hb hn
      change logDeriv f s = (m : ℂ) / (s - 0) + g s at hs
      rw [erase_origin_sum (ha 0) hmem] at hh
      change ‖logDeriv f s - ((m : ℂ) / s + V s)‖ ≤ _ at hh
      rw [hs, sub_zero, add_sub_add_left_eq_sub] at hh
      exact hh
    have hv := norm_local_sum_at_zero hχ hZ
    have hnormg : ‖g 0‖ ≤ 2 * C * L + W := by
      have e := norm_add_le (g 0 - V 0) (V 0)
      rw [sub_add_cancel] at e
      exact e.trans ((add_le_add hsub (hv.trans (add_le_add hZmass (le_refl W)))).trans_eq (by ring))
    have hnormP : ‖P 0‖ ≤ 1 := by dsimp only [P]; split_ifs <;> simp
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
    have hL : (1 / 2 : ℝ) ≤ L :=
      (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        (Real.log_le_log (by norm_num) (by linarith only [hN]))
    refine (norm_sub_le _ _).trans ((add_le_add hnormg hnormP).trans ?_)
    nlinarith only [hL, hW, mul_nonneg hC.le hW]

end QH.PrimeProgressions
