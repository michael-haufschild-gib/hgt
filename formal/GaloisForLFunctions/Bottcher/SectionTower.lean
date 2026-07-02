/-
# The Böttcher section tower: anchor

A **tower section** on a round annulus is an analytic, odd, injective section of the Böttcher
level structure: `G_c ∘ T = log ‖·‖`, the functional equation `T(w²) = T(w)² + c` (where both
sides live in the annulus), and the unit winding of `T∘circle` about `0`.  These are exactly the
invariants that propagate down the inverse-branch sqrt-chain and, at the bottom, produce the deep
radicand and its odd loop for `ExtendedNonSquare.q62_disconnected_of_towerData`.

This file defines the structure and constructs the **far anchor** from the far-field analytic
inverse `ψ` of `φ_c` (`FarFieldUnivalence.exists_analytic_inverse_far` +
`BottcherFarFieldSurjective.exists_bottcher_far_preimage`): the level identity from
`norm_bottcherCoord`, oddness from `bottcherCoord_neg`, the FE from `bottcherCoord_quadratic`,
injectivity from `φ ∘ ψ = id`, and the winding from the dog-on-a-leash lemma against the round
circle (`ψ` is within distance `1` of the identity far out).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.TowerCertificates
import GaloisForLFunctions.Bottcher.AnnulusRoot
import GaloisForLFunctions.Bottcher.FarFieldInverseFE
import GaloisForLFunctions.Bottcher.BottcherAsymptotic
import GaloisForLFunctions.Bottcher.BottcherFarFieldSurjective

open Complex Set Filter Metric

namespace Bottcher

/-- A **tower section** on the annulus `{rlo < ‖w‖ < rhi}`: analytic, level-true, odd, satisfying
the Böttcher functional equation, injective, with unit winding of every circle image about `0`. -/
structure TowerSection (c : ℂ) (rlo rhi : ℝ) where
  T : ℂ → ℂ
  an : AnalyticOnNhd ℂ T (annulusSet rlo rhi)
  level : ∀ w ∈ annulusSet rlo rhi, greenFunctionDyn c (T w) = Real.log ‖w‖
  odd : ∀ w ∈ annulusSet rlo rhi, T (-w) = -T w
  fe : ∀ w : ℂ, w ∈ annulusSet rlo rhi → w ^ 2 ∈ annulusSet rlo rhi →
    T (w ^ 2) = (T w) ^ 2 + c
  inj : Set.InjOn T (annulusSet rlo rhi)
  dne : ∀ w ∈ annulusSet rlo rhi, deriv T w ≠ 0
  wind : ∀ r : ℝ, rlo < r → r < rhi →
    (∫ θ in (0:ℝ)..(2 * Real.pi), (T (circleMap 0 r θ))⁻¹
      * (deriv T (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)))
      = 2 * (Real.pi : ℂ) * Complex.I

/-- **The far anchor.**  There is a radius `Ra` (above `1` and above the critical Böttcher modulus
`e^{G_c(0)}`) such that on every annulus `{Ra < ‖w‖ < rhi}` the far-field inverse `ψ` of `φ_c` is
a tower section. -/
theorem exists_tower_anchor (c : ℂ) :
    ∃ Ra Rinj : ℝ, 1 < Ra ∧ Real.exp (greenFunctionDyn c 0) < Ra ∧
      Set.InjOn (bottcherCoord c) {z : ℂ | Rinj < ‖z‖} ∧
      ∀ rhi : ℝ, Ra < rhi → ∃ S : TowerSection c Ra rhi,
        (∀ w ∈ annulusSet Ra rhi,
          bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
        (∀ z : ℂ, Real.log Ra < greenFunctionDyn c z →
          greenFunctionDyn c z < Real.log rhi → z ∈ S.T '' annulusSet Ra rhi) := by
  classical
  have hmax2 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
  have hmaxc : ‖c‖ ≤ max 2 ‖c‖ := le_max_right _ _
  -- asymptotic closeness threshold for `φ − id`
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, ∀ z : ℂ, M₁ < ‖z‖ → ‖bottcherCoord c z - z‖ < 1 := by
    have h := (tendsto_bottcherCoord_sub_id c).eventually
      (Metric.ball_mem_nhds (0:ℂ) one_pos)
    rw [← comap_norm_atTop, eventually_comap] at h
    obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp h
    refine ⟨M₁, fun z hz => ?_⟩
    have := hM₁ ‖z‖ (le_of_lt hz) z rfl
    rwa [dist_zero_right] at this
  set R : ℝ := 2 * max 2 ‖c‖ + 16 * ‖c‖ + 17 + max M₁ 0 with hRdef
  have hR1 : 2 * max 2 ‖c‖ < R := by
    rw [hRdef]; nlinarith [norm_nonneg c, le_max_right M₁ 0]
  have hRM₁ : M₁ < R := by
    rw [hRdef]
    nlinarith [norm_nonneg c, le_max_left M₁ 0]
  have hR17 : (17:ℝ) ≤ R := by
    rw [hRdef]; nlinarith [norm_nonneg c, le_max_right M₁ 0]
  have hRc : 16 * ‖c‖ + 17 ≤ R := by
    rw [hRdef]; nlinarith [norm_nonneg c, le_max_right M₁ 0]
  have hR2 : 16 * ‖c‖ < R ^ 2 := by nlinarith [norm_nonneg c]
  have hRpos : (0:ℝ) < R := by linarith
  have hmaxR : max 2 ‖c‖ < R := by
    rw [hRdef]; nlinarith [norm_nonneg c, le_max_right M₁ 0]
  obtain ⟨ψ, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far hR1 hR2
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  set R₁ : ℝ := max R' 1 with hR₁def
  -- the deep witness
  have hwit : ∀ v : ℂ, R₁ < ‖v‖ →
      ∃ z : ℂ, R < ‖z‖ ∧ bottcherCoord c z = v ∧ ψ v = z := by
    intro v hv
    obtain ⟨z, hz, hzeq⟩ := hRpre v (lt_of_le_of_lt (le_max_left _ _) hv)
    exact ⟨z, hz, hzeq, by rw [← hzeq]; exact hψleft z hz⟩
  -- pointwise facts at deep arguments
  have hcrude : ∀ z : ℂ, R < ‖z‖ → ‖c‖ ≤ ‖z‖ ∧ 2 < ‖z‖ := by
    intro z hz
    constructor
    · linarith [le_trans hmaxc hmaxR.le]
    · linarith [le_trans hmax2 hmaxR.le]
  have hGψ : ∀ v : ℂ, R₁ < ‖v‖ → greenFunctionDyn c (ψ v) = Real.log ‖v‖ := by
    intro v hv
    obtain ⟨z, hz, hzeq, hψv⟩ := hwit v hv
    obtain ⟨hc', h2'⟩ := hcrude z hz
    have hK : z ∉ filledJulia c := not_mem_filledJulia hc' h2'
    rw [hψv]
    unfold greenFunctionDyn
    rw [if_neg hK, ← hzeq, norm_bottcherCoord hc' h2']
    unfold bottcherModulus
    rw [Real.log_exp]
  have hψnear : ∀ v : ℂ, R₁ < ‖v‖ → ‖ψ v - v‖ < 1 := by
    intro v hv
    obtain ⟨z, hz, hzeq, hψv⟩ := hwit v hv
    rw [hψv, ← hzeq]
    have := hM₁ z (lt_trans hRM₁ hz)
    calc ‖z - bottcherCoord c z‖ = ‖bottcherCoord c z - z‖ := norm_sub_rev _ _
      _ < 1 := this
  have hψanv : ∀ v : ℂ, R₁ < ‖v‖ → AnalyticAt ℂ ψ v := by
    intro v hv
    obtain ⟨z, hz, hzeq, _⟩ := hwit v hv
    rw [← hzeq]
    exact hψan z hz
  have hψdne : ∀ v : ℂ, R₁ < ‖v‖ → deriv ψ v ≠ 0 := by
    intro v hv
    obtain ⟨z, hz, hzeq, _⟩ := hwit v hv
    -- ψ ∘ φ = id near z, so the chain rule forces deriv ψ (φ z) ≠ 0
    have hφan : AnalyticAt ℂ (bottcherCoord c) z := by
      have h1 : z ∈ escapeOpen c := by
        show max 2 ‖c‖ < ‖z‖
        exact lt_trans hmaxR hz
      exact (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) z h1
    have hφd : HasDerivAt (bottcherCoord c) (deriv (bottcherCoord c) z) z :=
      hφan.differentiableAt.hasDerivAt
    have hψd : HasDerivAt ψ (deriv ψ (bottcherCoord c z)) (bottcherCoord c z) := by
      have := (hψan z hz).differentiableAt.hasDerivAt
      exact this
    have hcomp : HasDerivAt (ψ ∘ bottcherCoord c)
        (deriv ψ (bottcherCoord c z) * deriv (bottcherCoord c) z) z :=
      HasDerivAt.comp z hψd hφd
    have hidev : (ψ ∘ bottcherCoord c) =ᶠ[nhds z] id := by
      have hopen : IsOpen {x : ℂ | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hz] with x hx
      exact hψleft x hx
    have hid : HasDerivAt (ψ ∘ bottcherCoord c) 1 z := by
      have h1 : HasDerivAt (id : ℂ → ℂ) 1 z := hasDerivAt_id z
      exact h1.congr_of_eventuallyEq hidev
    have huniq := hcomp.unique hid
    intro h0
    rw [hzeq] at huniq
    rw [h0] at huniq
    simp at huniq
  have hψinj : ∀ v₁ : ℂ, R₁ < ‖v₁‖ → ∀ v₂ : ℂ, R₁ < ‖v₂‖ → ψ v₁ = ψ v₂ → v₁ = v₂ := by
    intro v₁ hv₁ v₂ hv₂ h
    obtain ⟨z₁, hz₁, hzeq₁, hψv₁⟩ := hwit v₁ hv₁
    obtain ⟨z₂, hz₂, hzeq₂, hψv₂⟩ := hwit v₂ hv₂
    rw [hψv₁, hψv₂] at h
    rw [← hzeq₁, ← hzeq₂, h]
  have hψodd : ∀ v : ℂ, R₁ < ‖v‖ → ψ (-v) = -ψ v := by
    intro v hv
    obtain ⟨z, hz, hzeq, hψv⟩ := hwit v hv
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    have hneg : bottcherCoord c (-z) = -v := by
      rw [bottcherCoord_neg hz0, hzeq]
    have hnz : R < ‖(-z : ℂ)‖ := by rwa [norm_neg]
    rw [← hneg, hψleft _ hnz, hψv]
  have hψfe : ∀ v : ℂ, R₁ < ‖v‖ → ψ (v ^ 2) = (ψ v) ^ 2 + c := by
    intro v hv
    obtain ⟨z, hz, hzeq, hψv⟩ := hwit v hv
    obtain ⟨hc', h2'⟩ := hcrude z hz
    have hfz : bottcherCoord c (quadratic c z) = v ^ 2 := by
      rw [bottcherCoord_quadratic hc' h2', hzeq]
    have hfzdeep : R < ‖quadratic c z‖ := by
      unfold quadratic
      have h1 : ‖z ^ 2 + c‖ ≥ ‖z‖ ^ 2 - ‖c‖ := by
        have h2 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
          calc ‖z ^ 2‖ = ‖(z ^ 2 + c) + (-c)‖ := by ring_nf
            _ ≤ ‖z ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
            _ = ‖z ^ 2 + c‖ + ‖c‖ := by rw [norm_neg]
        rw [norm_pow] at h2
        linarith
      nlinarith [norm_nonneg c]
    rw [← hfz, hψleft _ hfzdeep, hψv]
    rfl
  -- the anchor radius
  -- the Green bound on the crude ball (for the norm-from-level argument)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ w : ℂ, ‖w‖ ≤ max 2 ‖c‖ → greenFunctionDyn c w ≤ Cb := by
    have hcpt : IsCompact {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} := by
      have h1 : {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} = Metric.closedBall 0 (max 2 ‖c‖) := by
        ext w
        simp [Metric.mem_closedBall, dist_zero_right]
      rw [h1]
      exact isCompact_closedBall 0 _
    rcases {w : ℂ | ‖w‖ ≤ max 2 ‖c‖}.eq_empty_or_nonempty with hbe | hbne
    · exact ⟨0, fun w hw => absurd (show w ∈ {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} from hw)
        (by rw [hbe]; exact Set.notMem_empty w)⟩
    obtain ⟨w₀, _, hw₀max⟩ := hcpt.exists_isMaxOn hbne
      (continuous_greenFunctionDyn c).continuousOn
    exact ⟨greenFunctionDyn c w₀, fun w hw => hw₀max hw⟩
  set Ra : ℝ := max (max (R₁ + 1) ((R + 1) * Real.exp 1))
    (max (max 2 (Real.exp (greenFunctionDyn c 0) + 1)) (Real.exp Cb + 1)) with hRadef
  have hexp1 : (1:ℝ) < Real.exp 1 := by
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hRa1 : (1:ℝ) < Ra := lt_of_lt_of_le one_lt_two
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
  have hRaR₁ : R₁ < Ra := by
    have h1 : R₁ + 1 ≤ max (R₁ + 1) ((R + 1) * Real.exp 1) := le_max_left _ _
    have h2 : max (R₁ + 1) ((R + 1) * Real.exp 1) ≤ Ra := le_max_left _ _
    linarith
  have hRaG : Real.exp (greenFunctionDyn c 0) < Ra := by
    have h1 : Real.exp (greenFunctionDyn c 0) + 1
        ≤ max 2 (Real.exp (greenFunctionDyn c 0) + 1) := le_max_right _ _
    have h2 : max 2 (Real.exp (greenFunctionDyn c 0) + 1)
        ≤ max (max 2 (Real.exp (greenFunctionDyn c 0) + 1)) (Real.exp Cb + 1) :=
      le_max_left _ _
    have h3 : max (max 2 (Real.exp (greenFunctionDyn c 0) + 1)) (Real.exp Cb + 1) ≤ Ra :=
      le_max_right _ _
    linarith
  have hRaRe : (R + 1) * Real.exp 1 ≤ Ra :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hRaCb : Real.exp Cb + 1 ≤ Ra :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Ra, R, hRa1, hRaG, bottcherCoord_injOn_far hR1 hR2, ?_⟩
  intro rhi hrhi
  have hdeep : ∀ w ∈ annulusSet Ra rhi, R₁ < ‖w‖ := by
    intro w hw
    exact lt_of_lt_of_le hRaR₁ (le_of_lt hw.1)
  refine ⟨⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun w hw => hψanv w (hdeep w hw)
  · exact fun w hw => hGψ w (hdeep w hw)
  · exact fun w hw => hψodd w (hdeep w hw)
  · exact fun w hw _ => hψfe w (hdeep w hw)
  · intro w₁ h₁ w₂ h₂ h
    exact hψinj w₁ (hdeep w₁ h₁) w₂ (hdeep w₂ h₂) h
  · exact fun w hw => hψdne w (hdeep w hw)
  · intro r hr hrhi'
    have hrpos : (0:ℝ) < r := lt_trans (by linarith) hr
    have hr1 : (1:ℝ) < r := lt_trans hRa1 hr
    have hcircdeep : ∀ θ : ℝ, R₁ < ‖circleMap 0 r θ‖ := by
      intro θ
      have hnorm : ‖circleMap 0 r θ‖ = r := by
        simp [circleMap, Complex.norm_exp, abs_of_pos hrpos]
      rw [hnorm]
      linarith
    -- annulus analyticity for the section loop
    have hcircann : ∀ θ : ℝ, circleMap 0 r θ ∈ annulusSet (R₁) (r + 1) := by
      intro θ
      have hnorm : ‖circleMap 0 r θ‖ = r := by
        simp [circleMap, Complex.norm_exp, abs_of_pos hrpos]
      constructor
      · rw [hnorm]; linarith
      · rw [hnorm]; linarith
    have hψann : AnalyticOnNhd ℂ ψ (annulusSet R₁ (r + 1)) := by
      intro v hv
      exact hψanv v hv.1
    -- the leash against the round circle
    set gLoop : C1Loop := sectionLoop hψann hcircann with hgdef
    have hle : ∀ θ : ℝ, ‖gLoop.γ θ - (circleLoop r).γ θ‖ < ‖(circleLoop r).γ θ - 0‖ := by
      intro θ
      have h1 : gLoop.γ θ = ψ (circleMap 0 r θ) := rfl
      have h2 : (circleLoop r).γ θ = circleMap 0 r θ := rfl
      have hnorm : ‖circleMap 0 r θ‖ = r := by
        simp [circleMap, Complex.norm_exp, abs_of_pos hrpos]
      rw [h1, h2, sub_zero, hnorm]
      calc ‖ψ (circleMap 0 r θ) - circleMap 0 r θ‖ < 1 := hψnear _ (hcircdeep θ)
        _ < r := hr1
    have hwind0 : windInt gLoop 0 = windInt (circleLoop r) 0 :=
      windInt_eq_of_leash (circleLoop r) gLoop 0 hle
    have hcirc0 : windInt (circleLoop r) 0 = 2 * (Real.pi : ℂ) * Complex.I := by
      apply windInt_circleLoop hrpos
      rw [norm_zero]
      exact hrpos
    have hraw : windInt gLoop 0
        = ∫ θ in (0:ℝ)..(2 * Real.pi), (ψ (circleMap 0 r θ))⁻¹
            * (deriv ψ (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      show (gLoop.γ θ - 0)⁻¹ * gLoop.γ' θ = _
      rw [sub_zero]
      rfl
    rw [← hraw, hwind0, hcirc0]
  · intro w hw
    obtain ⟨z, hz, hzeq, hψv⟩ := hwit w (hdeep w hw)
    refine ⟨?_, ?_, ?_⟩
    · show bottcherCoord c (ψ w) = w
      rw [hψv, hzeq]
    · show ψ w ∈ escapeOpen c
      rw [hψv]
      show max 2 ‖c‖ < ‖z‖
      exact lt_trans hmaxR hz
    · show R < ‖ψ w‖
      rw [hψv]
      exact hz
  · -- band surjectivity: every band-level point is a section value
    intro z hz1 hz2
    -- the point is far: its level exceeds the crude-ball bound, so the crude estimate applies
    have hzK : z ∉ filledJulia c := by
      intro hcon
      have h1 : greenFunctionDyn c z = 0 := (greenFunctionDyn_eq_zero_iff c z).mpr hcon
      rw [h1] at hz1
      have h2 : (0:ℝ) < Real.log Ra := Real.log_pos hRa1
      linarith
    have hznotball : max 2 ‖c‖ < ‖z‖ := by
      by_contra hcon
      push Not at hcon
      have h1 := hCb z hcon
      have h2 : Real.log Ra ≤ Cb := by linarith
      have h3 : Ra ≤ Real.exp Cb := by
        calc Ra = Real.exp (Real.log Ra) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp Cb := Real.exp_le_exp.mpr h2
      linarith
    have hcrude := greenFunctionDyn_le_crude
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hznotball))
      (lt_of_le_of_lt (le_max_left _ _) hznotball)
    have hzR : R < ‖z‖ := by
      have h1 : Real.log Ra - 1 ≤ Real.log ‖z‖ := by linarith
      have h2 : Real.log ((R + 1) * Real.exp 1) ≤ Real.log Ra :=
        Real.log_le_log (by positivity) hRaRe
      have h3 : Real.log ((R + 1) * Real.exp 1) = Real.log (R + 1) + 1 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
      have h4 : Real.log (R + 1) ≤ Real.log ‖z‖ := by
        rw [h3] at h2
        linarith
      have hz2' : (2:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hznotball
      have h5 : R + 1 ≤ ‖z‖ := by
        calc R + 1 = Real.exp (Real.log (R + 1)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp (Real.log ‖z‖) := Real.exp_le_exp.mpr h4
          _ = ‖z‖ := Real.exp_log (by linarith)
      linarith
    -- the Böttcher value of z is in the annulus, and ψ pulls it back to z
    have hnormφ : ‖bottcherCoord c z‖ = Real.exp (greenFunctionDyn c z) := by
      rw [norm_bottcherCoord
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hznotball))
        (lt_of_le_of_lt (le_max_left _ _) hznotball)]
      unfold bottcherModulus
      congr 1
      unfold greenFunctionDyn
      rw [if_neg hzK]
    have hφann : bottcherCoord c z ∈ annulusSet Ra rhi := by
      constructor
      · rw [hnormφ]
        calc Ra = Real.exp (Real.log Ra) := (Real.exp_log (by linarith)).symm
          _ < Real.exp (greenFunctionDyn c z) := Real.exp_lt_exp.mpr hz1
      · rw [hnormφ]
        calc Real.exp (greenFunctionDyn c z) < Real.exp (Real.log rhi) :=
              Real.exp_lt_exp.mpr hz2
          _ = rhi := Real.exp_log (by linarith)
    exact ⟨bottcherCoord c z, hφann, hψleft z hzR⟩

end Bottcher
