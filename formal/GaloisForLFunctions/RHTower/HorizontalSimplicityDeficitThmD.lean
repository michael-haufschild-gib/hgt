import GaloisForLFunctions.RHTower.HorizontalSimplicityDeficitSeam
import GaloisForLFunctions.RHTower.HorizontalTradeoffWindowDeficit

/-!
# Theorem D with horizontal overlap deficits

For the Montgomery–Taylor window at fixed `λ ∈ (0,1)` and every `ε > 0`, for all large `T`,

`(HD(λ) − ε) N(T,2T) ≤ N_iso(δ; T, 2T) + (L/24) Σ_{T−√T < γ ≤ 2T+√T, β > ½} (β − ½) + (2/L) N(I′)`

with `L = λ log(T/2π)` (`thmD_horizontal_deficit_lam_abstract`).  Here `N_iso(δ; T, 2T)` counts
the simple critical zeros with ordinate in `(T, 2T]` having no off-line zero on their horizontal
line within distance `δ` of the critical line.  At `δ = 1/2` these are the simple critical zeros
with no off-line zero on their horizontal line at all.

The window deficit `1 − 2J²/(I₀I₂) ≤ εL/24 + 2w/L` (`phiD_window_deficit_le`) feeds
`seam_horizontal_deficit`, and Zeta23's endgame `thmD_count_of_seam` does the rest.
-/

open Complex Finset
open Zeta23 Zeta23.ZeroSide

namespace RHTower

noncomputable section

open Filter Asymptotics Topology Real RHLinalg Zeta23.ThmD Zeta23.Assembly

/-- The overlap deficit bound for the Theorem D window of `P` at height `T`. -/
theorem atD_overlapRatio_deficit {P : Params} (hP : P.Valid) (T : ℝ) (hL : 0 < P.L T)
    (hLw : 24 * P.w * Real.exp 25 ≤ P.L T) (hc : Continuous ((P.atD T).phi T)) {ε : ℝ}
    (hε : 0 < ε) :
    1 - overlapRatio (P.atD T) T ε ≤ 1 / 24 * (ε * (P.atD T).L T) + 2 * P.w / P.L T := by
  have hφ := Params.atD_phi_valid T hP
  rw [hφ] at hc
  have h := phiD_window_deficit_le hP T hL hLw hc hε
  simp only [overlapRatio, Params.atD_L, hφ]
  linarith

/-- **Theorem D with horizontal deficits, abstract.** -/
theorem thmD_horizontal_deficit_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) (δ : ℝ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ)
        ≤ NisoH Z δ T (2 * T) + 1 / 24 * P.L T * offMoment Z (T - D0 T) (2 * T + D0 T)
          + 2 * P.w / P.L T * (Z.NIprime T : ℝ) := by
  refine thmD_count_of_seam Z H P hP hlam aT bT JT trG trG2 hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE (fun T => (NisoH Z δ T (2 * T) : ℝ)
      + 1 / 24 * P.L T * offMoment Z (T - D0 T) (2 * T + D0 T)
      + 2 * P.w / P.L T * (Z.NIprime T : ℝ)) ?_
  have hlam0 := hP.lam_pos
  have hLw : ∀ᶠ T in atTop, 24 * P.w * Real.exp 25 ≤ P.L T :=
    (Assembly.tendsto_L_atTop P hlam0).eventually (eventually_ge_atTop _)
  filter_upwards [hTail, hId, ha, eventually_ge_atTop (0:ℝ), eventually_l_pos, eventually_w8 hP,
    hLw] with T hTl hid ha2 hT0 hl h8 hLwT
  have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
  have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
  have hW := admWindow_params hP h8
  have hcD : Continuous ((P.atD T).phi T) := by
    rw [Params.atD_phi_valid T hP]; exact hW.contDiff.continuous
  have hsuppD : ∀ u, (P.atD T).L T / 2 ≤ |u| → (P.atD T).phi T u = 0 := by
    intro u hu; rw [Params.atD_phi_valid T hP]; exact hW.support u hu
  have hκ : 0 ≤ 2 * P.w / P.L T := by
    have := hP.one_le_w; positivity
  exact seam_horizontal_deficit (Z := Z) hT0 (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos hcD hsuppD δ (by norm_num : (0:ℝ) ≤ 1 / 24) hκ
    (fun ε hε => atD_overlapRatio_deficit hP T hLpos hLwT hcD hε)

/-- Fixed `λ ∈ (0,1)`, abstract zero configuration with the paper's inputs. -/
theorem thmD_horizontal_deficit_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1) (δ : ℝ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (Z.N T (2 * T) : ℝ)
        ≤ NisoH Z δ T (2 * T) + 1 / 24 * P.L T * offMoment Z (T - D0 T) (2 * T + D0 T)
          + 2 * P.w / P.L T * (Z.NIprime T : ℝ) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_horizontal_deficit_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀
    hNII hGzGp hId hcalE δ
  simpa only [HD, one_div] using h

end

end RHTower
