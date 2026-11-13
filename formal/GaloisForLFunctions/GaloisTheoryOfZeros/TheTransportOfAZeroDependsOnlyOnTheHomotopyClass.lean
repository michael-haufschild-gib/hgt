import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportsOverForwardTimesFormAGroup
import Mathlib.Topology.Homotopy.Lifting

/-!
# The transport of a zero depends only on the homotopy class of the path

The simple zeros of the heat family form the smooth part of the heat cover,
`simpleZeros = {(τ, z) : H_τ(z) = 0, H_τ'(z) ≠ 0}`.

* **The smooth part is a separated local homeomorphism over the times.** Near a simple zero the
  cover is the graph of a continuous function of the time, and all zeros on the graph are simple
  (`exists_simple_zero_chart`). So the time `(τ, z) ↦ τ` is a local homeomorphism from the smooth
  part to `ℂ` (`isLocalHomeomorph_simpleZeroTime`).
* **Homotopy invariance.** Let `F u`, `0 ≤ u ≤ 1`, be a continuous family of paths of times
  with common ends, and let every `F u` carry a lift through simple zeros that starts at `z₀`.
  Then all lifts end at the same zero (`lift_end_eq_of_homotopy`). The paths may cross branch
  times: only the zeros on the lifts have to be simple.
* A loop whose straight contraction to its base point carries such lifts of `z₀` transports
  `z₀` to itself (`transports_self_of_contraction`).

Consequences over forward times off the branch times:

* the transport along a path depends only on its homotopy class (`transports_of_homotopy`);
* a loop in a convex set of forward times without branch times transports every zero to itself
  (`transports_self_of_convex`).
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The smooth part of the heat cover -/

/-- The simple zeros of the heat family: the smooth part of the heat cover. -/
def simpleZeros : Set (ℂ × ℂ) :=
  {q | complexHeat q.1 q.2 = 0 ∧ deriv (complexHeat q.1) q.2 ≠ 0}

/-- The time of a simple zero. -/
def simpleZeroTime (q : simpleZeros) : ℂ := q.1.1

theorem continuous_simpleZeroTime : Continuous simpleZeroTime :=
  continuous_fst.comp continuous_subtype_val

/-- **The chart of a simple zero consists of simple zeros.** Near a simple zero `(τ₀, z₀)` there
are an open set `W` of times and a continuous `ζ` on `W` such that for `τ ∈ W` the point `ζ(τ)`
is a simple zero of `H_τ` and the only zero of `H_τ` in a fixed disc around `z₀`. -/
theorem exists_simple_zero_chart {τ₀ z₀ : ℂ} (h0 : complexHeat τ₀ z₀ = 0)
    (h1 : deriv (complexHeat τ₀) z₀ ≠ 0) :
    ∃ W : Set ℂ, IsOpen W ∧ τ₀ ∈ W ∧ ∃ ρ > 0, ∃ ζ : ℂ → ℂ, ContinuousOn ζ W ∧ ζ τ₀ = z₀ ∧
      ∀ τ ∈ W, ζ τ ∈ ball z₀ ρ ∧ complexHeat τ (ζ τ) = 0 ∧ deriv (complexHeat τ) (ζ τ) ≠ 0 ∧
        ∀ z ∈ ball z₀ ρ, complexHeat τ z = 0 → z = ζ τ := by
  obtain ⟨δ, hδ, ρ, hρ, ζ, hζc, hζ0, hchart⟩ := exists_zero_chart h0 h1
  have hN : IsOpen {p : ℂ × ℂ | deriv (complexHeat p.1) p.2 ≠ 0} :=
    isOpen_ne_fun continuous_deriv_complexHeat continuous_const
  have hpair : ContinuousOn (fun τ => (τ, ζ τ)) (ball τ₀ δ) := continuousOn_id.prodMk hζc
  refine ⟨ball τ₀ δ ∩ (fun τ => (τ, ζ τ)) ⁻¹' {p : ℂ × ℂ | deriv (complexHeat p.1) p.2 ≠ 0},
    hpair.isOpen_inter_preimage isOpen_ball hN, ⟨mem_ball_self hδ, ?_⟩, ρ, hρ, ζ,
    hζc.mono inter_subset_left, hζ0, fun τ hτ => ?_⟩
  · show deriv (complexHeat τ₀) (ζ τ₀) ≠ 0
    rw [hζ0]
    exact h1
  · obtain ⟨h2, h3, h4⟩ := hchart τ hτ.1
    exact ⟨h2, h3, hτ.2, h4⟩

/-- **The smooth part of the heat cover is a local homeomorphism over the times.** -/
theorem isLocalHomeomorph_simpleZeroTime : IsLocalHomeomorph simpleZeroTime := by
  refine IsLocalHomeomorph.mk _ fun q => ?_
  obtain ⟨W, hWo, hτW, ρ, hρ, ζ, hζc, -, hchart⟩ := exists_simple_zero_chart q.2.1 q.2.2
  have hsec : ∀ τ ∈ W, ((τ, ζ τ) : ℂ × ℂ) ∈ simpleZeros := fun τ hτ =>
    ⟨(hchart τ hτ).2.1, (hchart τ hτ).2.2.1⟩
  classical
  -- the section of the chart, extended by a constant outside `W`
  obtain ⟨inv, hinv⟩ : ∃ inv : ℂ → simpleZeros,
      ∀ τ (h : τ ∈ W), inv τ = ⟨(τ, ζ τ), hsec τ h⟩ :=
    ⟨fun τ => if h : τ ∈ W then ⟨(τ, ζ τ), hsec τ h⟩ else q, fun τ h => dif_pos h⟩
  have hcinv : ContinuousOn inv W := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun τ : W => ((τ : ℂ), ζ τ) :=
      continuous_subtype_val.prodMk (continuousOn_iff_continuous_restrict.1 hζc)
    exact (h1.subtype_mk fun τ : W => hsec τ τ.2).congr fun τ => (hinv τ τ.2).symm
  refine ⟨{ toFun := fun x : simpleZeros => x.1.1
            invFun := inv
            source := {x : simpleZeros | x.1.1 ∈ W ∧ x.1.2 ∈ ball q.1.2 ρ}
            target := W
            map_source' := fun x hx => hx.1
            map_target' := fun τ hτ => by
              rw [hinv τ hτ]
              exact ⟨hτ, (hchart τ hτ).1⟩
            left_inv' := fun x hx => by
              rw [hinv _ hx.1]
              exact Subtype.ext (Prod.ext rfl ((hchart _ hx.1).2.2.2 _ hx.2 x.2.1).symm)
            right_inv' := fun τ hτ => by rw [hinv τ hτ]
            continuousOn_toFun := continuous_simpleZeroTime.continuousOn
            continuousOn_invFun := hcinv
            open_source := (hWo.preimage (continuous_fst.comp continuous_subtype_val)).inter
              (isOpen_ball.preimage (continuous_snd.comp continuous_subtype_val))
            open_target := hWo }, ⟨hτW, mem_ball_self hρ⟩, fun _ _ => rfl⟩

/-! ## Homotopy invariance -/

/-- **Homotopy invariance of the continuation.** Let `F u`, `u ∈ [0, 1]`, be a continuous family
of paths of times with the same two ends, and `w u` a lift of `F u` through simple zeros, all
lifts starting at the same zero. Then all lifts end at the same zero. -/
theorem lift_end_eq_of_homotopy {F : ℝ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1)) {a b z₀ : ℂ}
    (hF0 : ∀ u ∈ Icc (0 : ℝ) 1, F u 0 = a) (hF1 : ∀ u ∈ Icc (0 : ℝ) 1, F u 1 = b)
    {w : ℝ → ℝ → ℂ} (hw : ∀ u ∈ Icc (0 : ℝ) 1, IsZeroLift (F u) 1 (w u))
    (hw0 : ∀ u ∈ Icc (0 : ℝ) 1, w u 0 = z₀)
    (hsimple : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      deriv (complexHeat (F u s)) (w u s) ≠ 0) :
    ∀ u ∈ Icc (0 : ℝ) 1, w u 1 = w 0 1 := by
  have hI : ∀ x : unitInterval, (x : ℝ) ∈ Icc (0 : ℝ) 1 := fun x => x.2
  -- the family of lifts as a map of the square into the smooth part of the cover
  have hmem : ∀ st : unitInterval × unitInterval,
      ((F st.2 st.1, w st.2 st.1) : ℂ × ℂ) ∈ simpleZeros := fun st =>
    ⟨(hw st.2 (hI _)).zero st.1 (hI _), hsimple st.2 (hI _) st.1 (hI _)⟩
  obtain ⟨g, hg⟩ : ∃ g : unitInterval × unitInterval → simpleZeros,
      ∀ st, (g st).1 = (F st.2 st.1, w st.2 st.1) := ⟨fun st => ⟨_, hmem st⟩, fun _ => rfl⟩
  have hswap : Continuous fun st : unitInterval × unitInterval => ((st.2 : ℝ), (st.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hfc : Continuous fun st : unitInterval × unitInterval => F st.2 st.1 :=
    hF.comp_continuous hswap fun st => ⟨hI st.2, hI st.1⟩
  have hlift : simpleZeroTime ∘ g = ⇑(⟨_, hfc⟩ : C(unitInterval × unitInterval, ℂ)) := by
    funext st
    show (g st).1.1 = F st.2 st.1
    rw [hg]
  -- the lifts start at one point
  have hc0 : Continuous fun u : unitInterval => g (0, u) := by
    have h : (fun u : unitInterval => g (0, u)) = fun _ => g (0, 0) := by
      funext u
      refine Subtype.ext ?_
      rw [hg, hg]
      exact congrArg₂ Prod.mk ((hF0 u (hI u)).trans (hF0 _ (hI 0)).symm)
        ((hw0 u (hI u)).trans (hw0 _ (hI 0)).symm)
    rw [h]
    exact continuous_const
  -- each lift is continuous
  have hcA : ∀ u : unitInterval, Continuous fun s : unitInterval => g (s, u) := by
    intro u
    have h1 : Continuous fun s : unitInterval => F u s :=
      hF.comp_continuous (continuous_const.prodMk continuous_subtype_val) fun s => ⟨hI u, hI s⟩
    have h2 : Continuous fun s : unitInterval => w u s :=
      (hw u (hI u)).continuousOn.comp_continuous continuous_subtype_val hI
    have h3 : Continuous fun s : unitInterval => (g (s, u)).1 := by
      have h : (fun s : unitInterval => (g (s, u)).1) = fun s : unitInterval => (F u s, w u s) :=
        funext fun s => hg (s, u)
      rw [h]
      exact h1.prodMk h2
    exact IsInducing.subtypeVal.continuous_iff.2 h3
  -- hence the family is continuous on the square, and its ends lie in one discrete fibre
  have hgc : Continuous g := isLocalHomeomorph_simpleZeroTime.continuous_lift
    (T2Space.isSeparatedMap _) _ hlift hc0 hcA
  have hconst := (T2Space.isSeparatedMap simpleZeroTime).const_of_comp
    isLocalHomeomorph_simpleZeroTime.isLocallyInjective
    (hgc.comp (Continuous.prodMk_right (1 : unitInterval))) (fun u u' => by
      show (g (1, u)).1.1 = (g (1, u')).1.1
      rw [hg, hg]
      exact (hF1 u (hI u)).trans (hF1 u' (hI u')).symm)
  intro u hu
  have h : (g (1, ⟨u, hu⟩)).1.2 = (g (1, 0)).1.2 :=
    congrArg (fun q : simpleZeros => q.1.2) (hconst ⟨u, hu⟩ 0)
  rw [hg, hg] at h
  exact h

/-! ## Contraction of a loop -/

/-- The straight contraction of a path to the point `c`. -/
def contractPath (γ : ℝ → ℂ) (c : ℂ) (u s : ℝ) : ℂ := ((1 - u : ℝ) : ℂ) * γ s + (u : ℂ) * c

theorem contractPath_zero (γ : ℝ → ℂ) (c : ℂ) (s : ℝ) : contractPath γ c 0 s = γ s := by
  simp [contractPath]

theorem contractPath_one (γ : ℝ → ℂ) (c : ℂ) (s : ℝ) : contractPath γ c 1 s = c := by
  simp [contractPath]

theorem contractPath_of_eq {γ : ℝ → ℂ} {c : ℂ} {s : ℝ} (h : γ s = c) (u : ℝ) :
    contractPath γ c u s = c := by
  rw [contractPath, h]
  push_cast
  ring

theorem continuousOn_contractPath {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (c : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => contractPath γ c p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => γ p.2) (Icc 0 1 ×ˢ Icc 0 1) :=
    hγ.comp continuous_snd.continuousOn fun p hp => hp.2
  have h2 : Continuous fun p : ℝ × ℝ => ((1 - p.1 : ℝ) : ℂ) := by fun_prop
  have h3 : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * c := by fun_prop
  exact (h2.continuousOn.mul h1).add h3.continuousOn

theorem continuousOn_contractPath_right {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (c : ℂ)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : ContinuousOn (contractPath γ c u) (Icc 0 1) :=
  (continuousOn_contractPath hγ c).comp (continuous_const.prodMk continuous_id).continuousOn
    fun _ hs => ⟨hu, hs⟩

/-- **A loop whose contraction carries lifts of `z₀` transports `z₀` to itself.** Let `γ` be a
loop of times. If every loop of the straight contraction of `γ` to its base point carries a lift
through simple zeros that starts at `z₀`, then the lift along `γ` ends at `z₀`. -/
theorem transports_self_of_contraction {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hloop : γ 1 = γ 0) {z₀ : ℂ}
    (hlift : ∀ u ∈ Icc (0 : ℝ) 1, ∃ w : ℝ → ℂ, IsZeroLift (contractPath γ (γ 0) u) 1 w ∧
      w 0 = z₀ ∧ ∀ s ∈ Icc (0 : ℝ) 1,
        deriv (complexHeat (contractPath γ (γ 0) u s)) (w s) ≠ 0) :
    Transports γ z₀ z₀ := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  choose! w hw using hlift
  have hend := lift_end_eq_of_homotopy (F := contractPath γ (γ 0))
    (continuousOn_contractPath hγ _) (a := γ 0) (b := γ 0)
    (fun u _ => contractPath_of_eq rfl u) (fun u _ => contractPath_of_eq hloop u)
    (fun u hu => (hw u hu).1) (fun u hu => (hw u hu).2.1) (fun u hu => (hw u hu).2.2) 1 h11
  -- the lift of the constant path is constant
  have hconst : w 1 1 = z₀ := by
    have hz : complexHeat (γ 0) z₀ = 0 := by
      have := (hw 1 h11).1.zero 0 h01
      rwa [(hw 1 h11).2.1, contractPath_one] at this
    have hc : IsZeroLift (contractPath γ (γ 0) 1) 1 fun _ => z₀ :=
      ⟨continuousOn_const, fun s _ => by
        rw [contractPath_one]
        exact hz⟩
    exact IsZeroLift.eqOn (continuousOn_contractPath_right hγ _ h11) (hw 1 h11).1 hc
      (hw 1 h11).2.1 (hw 1 h11).2.2 h11
  refine ⟨w 0, ⟨(hw 0 h01).1.continuousOn, fun s hs => ?_⟩, (hw 0 h01).2.1, ?_⟩
  · have := (hw 0 h01).1.zero s hs
    rwa [contractPath_zero] at this
  · rw [← hend, hconst]

/-! ## Forward times -/

/-- **Transport depends only on the homotopy class.** Two forward paths that are homotopic with
fixed ends through forward times off the branch times transport every zero to the same zero. -/
theorem transports_of_homotopy {F : ℝ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hpos : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, 0 < (F u s).re)
    (hb : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F u s ∉ branchTimes) {a b : ℂ}
    (hF0 : ∀ u ∈ Icc (0 : ℝ) 1, F u 0 = a) (hF1 : ∀ u ∈ Icc (0 : ℝ) 1, F u 1 = b) {z₀ z₁ : ℂ}
    (h : Transports (F 0) z₀ z₁) : Transports (F 1) z₀ z₁ := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hpath : ∀ u ∈ Icc (0 : ℝ) 1, IsForwardPath (F u) := fun u hu =>
    ⟨hF.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hs => ⟨hu, hs⟩,
      hpos u hu, hb u hu⟩
  have hz₀ : complexHeat a z₀ = 0 := by
    have := h.zero_left
    rwa [hF0 0 h01] at this
  have hlift : ∀ u ∈ Icc (0 : ℝ) 1, ∃ w : ℝ → ℂ, IsZeroLift (F u) 1 w ∧ w 0 = z₀ :=
    fun u hu => exists_isZeroLift_of_re_pos (hpath u hu).continuousOn (hpos u hu) (hb u hu)
      (by rw [hF0 u hu]; exact hz₀)
  choose! w hw using hlift
  have hend := lift_end_eq_of_homotopy hF hF0 hF1 (fun u hu => (hw u hu).1)
    (fun u hu => (hw u hu).2) (fun u hu s hs =>
      deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hb u hu s hs) ((hw u hu).1.zero s hs))
    1 h11
  have h0 : w 0 1 = z₁ :=
    (hpath 0 h01).transports_unique ⟨w 0, (hw 0 h01).1, (hw 0 h01).2, rfl⟩ h
  exact ⟨w 1, (hw 1 h11).1, (hw 1 h11).2, hend.trans h0⟩

/-- **No monodromy over a convex set of forward times without branch times.** A loop in such a
set transports every zero to itself. -/
theorem transports_self_of_convex {U : Set ℂ} (hU : Convex ℝ U) (hpos : ∀ τ ∈ U, 0 < τ.re)
    (hb : ∀ τ ∈ U, τ ∉ branchTimes) {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hγU : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ U) (hloop : γ 1 = γ 0) {z₀ : ℂ}
    (h0 : complexHeat (γ 0) z₀ = 0) : Transports γ z₀ z₀ := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, contractPath γ (γ 0) u s ∈ U := by
    intro u hu s hs
    have := hU (hγU s hs) (hγU 0 h01) (sub_nonneg.2 hu.2) hu.1 (by ring : (1 - u) + u = 1)
    rw [Complex.real_smul, Complex.real_smul] at this
    exact this
  refine transports_self_of_contraction hγ hloop fun u hu => ?_
  obtain ⟨w, hw, hw0⟩ := exists_isZeroLift_of_re_pos (continuousOn_contractPath_right hγ _ hu)
    (fun s hs => hpos _ (hmem u hu s hs)) (fun s hs => hb _ (hmem u hu s hs))
    (by rw [contractPath_of_eq rfl]; exact h0)
  exact ⟨w, hw, hw0, fun s hs =>
    deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hb _ (hmem u hu s hs)) (hw.zero s hs)⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
