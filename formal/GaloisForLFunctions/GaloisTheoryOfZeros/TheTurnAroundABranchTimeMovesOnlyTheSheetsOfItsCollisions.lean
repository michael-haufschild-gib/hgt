import GaloisForLFunctions.GaloisTheoryOfZeros.EveryForwardMonodromyMovesFinitelyManyZeros
import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundAForwardBranchTimeIsANontrivialForwardMonodromy

/-!
# The turn around a branch time moves only the sheets of its collisions

The turn around a forward time `τ₀` is the transport along the circle `τ₀ + r²e^{2πis}`. On the
Hermite sheets of a collision `(τ₀, ζ)` it is the reflection `Z_ρ ↦ Z_{−ρ}`. This file determines
the turn on the whole fibre, for all small radii.

* **Zeros under a section return** (`transports_self_of_section`). A loop inside a convex set of
  times over which a continuous family of simple zeros is given transports the zero of the
  family to itself: the family lifts the contraction of the loop.
* **The turn** (`exists_forall_turnAction`). For all small `r`, every zero of `H_{τ₀+r²}` is
  transported to itself, or it is a sheet `Z_ρ(r)` of a collision of order `≥ 2` at the time
  `τ₀` and is transported to `Z_{−ρ}(r)`. Three regions: the far zeros return by the trap; a
  zero near a simple zero of `H_τ₀` lies on its chart; a zero near a multiple zero of `H_τ₀` is
  one of its sheets; and near the remaining compact part of a disc `H_τ` has no zero for `τ`
  near `τ₀`.
* **A simple central collision** (`eventually_turn_flip`). If `H_τ₀` has a double zero at the
  centre and no other multiple zero, the turn exchanges one zero `w ≠ 0` with `−w` and fixes
  every other zero: it is the sign flip of one pair. At every base time the forward monodromy
  group then contains the sign flip of exactly one pair
  (`exists_mem_forwardMonodromy_flip_one_pair`).
-/

open Complex Filter Topology Set Metric
open RHTower GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {τ₀ : ℂ}

/-! ## Small radii -/

theorem eventually_nhdsGT_of_exists_Ioo {P : ℝ → Prop}
    (h : ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε, P r) : ∀ᶠ r in 𝓝[>] (0 : ℝ), P r := by
  obtain ⟨ε, hε, h⟩ := h
  exact eventually_of_mem (Ioo_mem_nhdsGT hε) h

theorem exists_Ioo_of_eventually_nhdsGT {P : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P r) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε, P r := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun r hr => hsub hr⟩

theorem eventually_sq_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ r : ℝ in 𝓝[>] 0, r ^ 2 < δ := by
  have h : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (continuous_pow 2 : Continuous fun r : ℝ => r ^ 2).tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  exact h.eventually (gt_mem_nhds hδ)

theorem tendsto_add_ofReal_sq (τ₀ : ℂ) :
    Tendsto (fun r : ℝ => τ₀ + (r : ℂ) ^ 2) (𝓝[>] 0) (𝓝 τ₀) := by
  have h : Continuous fun r : ℝ => τ₀ + (r : ℂ) ^ 2 := by fun_prop
  have h1 := h.tendsto 0
  simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h1
  exact h1.mono_left nhdsWithin_le_nhds

/-! ## Zeros under a section return -/

/-- **A loop under a section of simple zeros.** Let `f` be a continuous family of simple zeros
over a convex set `U` of times. A loop in `U` transports the zero `f (γ 0)` to itself. -/
theorem transports_self_of_section {U : Set ℂ} (hU : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U)
    (hzero : ∀ τ ∈ U, complexHeat τ (f τ) = 0 ∧ deriv (complexHeat τ) (f τ) ≠ 0) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 1)) (hγU : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ U) (hloop : γ 1 = γ 0) :
    Transports γ (f (γ 0)) (f (γ 0)) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, contractPath γ (γ 0) u s ∈ U := by
    intro u hu s hs
    have := hU (hγU s hs) (hγU 0 h01) (sub_nonneg.2 hu.2) hu.1 (by ring : (1 - u) + u = 1)
    rw [Complex.real_smul, Complex.real_smul] at this
    exact this
  refine transports_self_of_contraction hγ hloop fun u hu =>
    ⟨fun s => f (contractPath γ (γ 0) u s),
      ⟨hf.comp (continuousOn_contractPath_right hγ _ hu) fun s hs => hmem u hu s hs,
        fun s hs => (hzero _ (hmem u hu s hs)).1⟩, ?_, fun s hs => (hzero _ (hmem u hu s hs)).2⟩
  show f (contractPath γ (γ 0) u 0) = f (γ 0)
  rw [contractPath_of_eq rfl]

/-! ## The three regions -/

/-- **The far zeros return under small turns.** -/
theorem eventually_turn_transports_self_of_far (hτ₀ : 0 < τ₀.re) :
    ∃ R : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → R ≤ ‖z‖ →
      Transports (turnPath τ₀ r) z z := by
  obtain ⟨R, hR⟩ := exists_forall_transports_self_of_far (t₀ := τ₀.re / 2) (‖τ₀‖ + 1)
    (half_pos hτ₀) (N := 1) one_pos
  refine ⟨R, ?_⟩
  filter_upwards [eventually_sq_lt (half_pos hτ₀),
    eventually_sq_lt (show (0 : ℝ) < 1 / 24 by norm_num)] with r hr1 hr2 z hz hfar
  have hr0 : 0 ≤ r ^ 2 := sq_nonneg r
  refine hR (turnPath τ₀ r) (continuous_turnPath τ₀ r).continuousOn
    (by rw [turnPath_one, turnPath_zero]) (fun s _ => ⟨?_, ?_⟩) (fun s _ s' _ _ => ?_) z
    (by rw [turnPath_zero]; exact hz) hfar
  · have h1 := Complex.abs_re_le_norm (turnPath τ₀ r s - τ₀)
    rw [norm_turnPath_sub, Complex.sub_re] at h1
    linarith [(abs_le.1 h1).1]
  · have h1 : ‖turnPath τ₀ r s‖ ≤ ‖τ₀‖ + ‖turnPath τ₀ r s - τ₀‖ := by
      have h2 := norm_add_le τ₀ (turnPath τ₀ r s - τ₀)
      rwa [add_sub_cancel] at h2
    rw [norm_turnPath_sub] at h1
    linarith
  · have h1 : turnPath τ₀ r s - turnPath τ₀ r s' =
        (turnPath τ₀ r s - τ₀) - (turnPath τ₀ r s' - τ₀) := by ring
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_turnPath_sub, norm_turnPath_sub]
    linarith

/-- **Near a simple zero of `H_τ₀` the turn fixes every zero.** -/
theorem eventually_turn_transports_self_of_simple {ζ : ℂ} (h0 : complexHeat τ₀ ζ = 0)
    (h1 : deriv (complexHeat τ₀) ζ ≠ 0) :
    ∃ ρ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      Transports (turnPath τ₀ r) z z := by
  obtain ⟨W, hW, hτW, ρ, hρ, f, hf, -, hchart⟩ := exists_simple_zero_chart h0 h1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW τ₀ hτW
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [eventually_sq_lt hδ] with r hr z hz hzero
  have hmem : ∀ s : ℝ, turnPath τ₀ r s ∈ ball τ₀ δ := fun s => by
    rw [mem_ball, dist_eq_norm, norm_turnPath_sub]
    exact hr
  have hbase : τ₀ + (r : ℂ) ^ 2 ∈ W := by
    have h2 := hball (hmem 0)
    rwa [turnPath_zero] at h2
  have hzf : z = f (turnPath τ₀ r 0) := by
    rw [turnPath_zero]
    exact (hchart _ hbase).2.2.2 z hz hzero
  have h2 := transports_self_of_section (convex_ball τ₀ δ) (hf.mono hball)
    (fun τ hτ => ⟨(hchart τ (hball hτ)).2.1, (hchart τ (hball hτ)).2.2.1⟩)
    (continuous_turnPath τ₀ r).continuousOn (fun s _ => hmem s)
    (by rw [turnPath_one, turnPath_zero])
  rwa [← hzf] at h2

/-- **Near a collision the turn is the Hermite reflection of all its sheets.** For small `r` the
zeros of `H_{τ₀+r²}` in a fixed disc around `ζ` are the sheets `Z_ρ(r)`, and the turn carries
`Z_ρ(r)` to `Z_{−ρ}(r)`. -/
theorem eventually_turn_transports_sheets {ζ : ℂ} {m : ℕ} (hc : IsCollision τ₀ ζ m) :
    ∃ ρ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      ∃ ρ' : ℂ, heatModelFwd m ρ' = 0 ∧ z = collisionZero τ₀ ζ m ρ' r ∧
        Transports (turnPath τ₀ r) z (collisionZero τ₀ ζ m (-ρ') r) := by
  obtain ⟨ρ, hρ, -, hev⟩ := exists_ball_zeros_eq_sheets hc
  refine ⟨ρ, hρ, ?_⟩
  have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ↔
      ∃ ρ' : ℂ, heatModelFwd m ρ' = 0 ∧ z = collisionZero τ₀ ζ m ρ' r :=
    eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + s ^ 2) z = 0 ↔
        ∃ ρ' : ℂ, heatModelFwd m ρ' = 0 ∧ z = collisionZero τ₀ ζ m ρ' s)
      (hev.mono fun s hs => hs.1))
  -- the profile has finitely many roots, so the turn acts on all sheets for small radii
  have hfin : {ρ' : ℂ | heatModelFwd m ρ' = 0}.Finite := by
    have hset : {ρ' : ℂ | heatModelFwd m ρ' = 0} =
        (fun x : ℝ => (x : ℂ)) '' (profileRoots m : Set ℝ) := by
      ext ρ'
      simp only [mem_setOf_eq, mem_image, Finset.mem_coe]
      exact heatModelFwd_eq_zero_iff
    rw [hset]
    exact (Finset.finite_toSet _).image _
  have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ ρ' ∈ {ρ' : ℂ | heatModelFwd m ρ' = 0},
      Transports (turnPath τ₀ r) (collisionZero τ₀ ζ m ρ' r) (collisionZero τ₀ ζ m (-ρ') r) :=
    (eventually_all_finite hfin).2 fun ρ' hρ' =>
      eventually_nhdsGT_of_exists_Ioo (hc.exists_transports_turn hρ')
  filter_upwards [h1, h2] with r hr1 hr2 z hz hzero
  obtain ⟨ρ', hρ', rfl⟩ := (hr1 z hz).1 hzero
  exact ⟨ρ', hρ', rfl, hr2 ρ' hρ'⟩

/-! ## The turn on the whole fibre -/

/-- The action of the turn of radius `r²` around `τ₀` on a zero `z` of `H_{τ₀+r²}`: the zero
returns, or it is a sheet of a collision of order `≥ 2` at the time `τ₀` and goes to the opposite
sheet. -/
def TurnAction (τ₀ : ℂ) (r : ℝ) (z : ℂ) : Prop :=
  Transports (turnPath τ₀ r) z z ∨
    ∃ (ζ : ℂ) (m : ℕ) (ρ : ℂ), 2 ≤ m ∧ IsCollision τ₀ ζ m ∧ heatModelFwd m ρ = 0 ∧
      z = collisionZero τ₀ ζ m ρ r ∧
        Transports (turnPath τ₀ r) z (collisionZero τ₀ ζ m (-ρ) r)

theorem exists_ball_eventually_turnAction {ζ : ℂ} (h0 : complexHeat τ₀ ζ = 0) :
    ∃ ρ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      TurnAction τ₀ r z := by
  by_cases h1 : deriv (complexHeat τ₀) ζ = 0
  · obtain ⟨m, hm, hc⟩ := exists_isCollision_two_le h0 h1
    obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_sheets hc
    exact ⟨ρ, hρ, hev.mono fun r hr z hz hzero => by
      obtain ⟨ρ', hρ', hz', hT⟩ := hr z hz hzero
      exact Or.inr ⟨ζ, m, ρ', hm, hc, hρ', hz', hT⟩⟩
  · obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_self_of_simple h0 h1
    exact ⟨ρ, hρ, hev.mono fun r hr z hz hzero => Or.inl (hr z hz hzero)⟩

/-- **The turn around a forward time, on the whole fibre.** For all small `r`, the turn of radius
`r²` around `τ₀` fixes every zero of `H_{τ₀+r²}` that is not a sheet of a collision of order
`≥ 2` at the time `τ₀`, and carries each such sheet `Z_ρ(r)` to `Z_{−ρ}(r)`. -/
theorem eventually_turnAction (hτ₀ : 0 < τ₀.re) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      TurnAction τ₀ r z := by
  obtain ⟨R, hfar⟩ := eventually_turn_transports_self_of_far hτ₀
  have hloc : ∀ ζ : ℂ, ∃ ρ > 0, complexHeat τ₀ ζ = 0 → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → TurnAction τ₀ r z := by
    intro ζ
    by_cases h0 : complexHeat τ₀ ζ = 0
    · obtain ⟨ρ, hρ, h⟩ := exists_ball_eventually_turnAction h0
      exact ⟨ρ, hρ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h h0⟩
  choose ρ hρ hP using hloc
  have hfin := finite_zeros_closedBall τ₀ R
  -- outside the discs around the zeros of `H_τ₀`, the disc of radius `R` carries no zero of
  -- `H_τ` for `τ` near `τ₀`
  have hC : IsCompact (closedBall (0 : ℂ) R \
      ⋃ ζ ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0}, ball ζ (ρ ζ)) :=
    (isCompact_closedBall 0 R).diff (isOpen_biUnion fun _ _ => isOpen_ball)
  have hfree : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ closedBall (0 : ℂ) R \
      ⋃ ζ ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0}, ball ζ (ρ ζ),
      complexHeat τ z ≠ 0 := by
    refine hC.eventually_forall_of_forall_eventually fun z hz => ?_
    have hz0 : complexHeat τ₀ z ≠ 0 := fun h => hz.2
      (mem_biUnion (show z ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0} from
        ⟨hz.1, h⟩) (mem_ball_self (hρ z)))
    exact continuous_complexHeat.continuousAt.eventually_ne hz0
  have hfree' := (tendsto_add_ofReal_sq τ₀).eventually hfree
  have hnear := (eventually_all_finite hfin).2 fun ζ hζ => hP ζ hζ.2
  filter_upwards [hfar, hfree', hnear] with r hr1 hr2 hr3 z hzero
  by_cases hzR : R ≤ ‖z‖
  · exact Or.inl (hr1 z hzero hzR)
  · have hzb : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 (not_le.1 hzR).le
    by_contra hcon
    refine hr2 z ⟨hzb, fun hmem => hcon ?_⟩ hzero
    obtain ⟨ζ, hζ, hzζ⟩ := mem_iUnion₂.1 hmem
    exact hr3 ζ hζ z hzζ hzero

/-- **The turn around a forward time**, for the radii below a threshold. -/
theorem exists_forall_turnAction (hτ₀ : 0 < τ₀.re) :
    ∃ r₀ > 0, ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      TurnAction τ₀ r z :=
  exists_Ioo_of_eventually_nhdsGT (eventually_turnAction hτ₀)

/-! ## A simple central collision -/

/-- **The turn around a simple central collision is the sign flip of one pair.** Let `H_τ₀` have
a double zero at the centre and no other multiple zero. For all small `r` the turn exchanges one
zero `w ≠ 0` of `H_{τ₀+r²}` with `−w` and fixes every other zero. -/
theorem eventually_turn_flip (hτ₀ : 0 < τ₀.re) (hcen : IsCollision τ₀ 0 2)
    (honly : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 → ζ = 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ w : ℂ, w ≠ 0 ∧ complexHeat (τ₀ + (r : ℂ) ^ 2) w = 0 ∧
      Transports (turnPath τ₀ r) w (-w) ∧ Transports (turnPath τ₀ r) (-w) w ∧
        ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → z ≠ w → z ≠ -w →
          Transports (turnPath τ₀ r) z z := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- the two roots `±√2` of the profile of order two
  have hρ₊ : heatModelFwd 2 ((Real.sqrt 2 : ℝ) : ℂ) = 0 :=
    heatModelFwd_eq_zero_iff.2 ⟨Real.sqrt 2, by rw [profileRoots_two]; simp, rfl⟩
  have hρ₋ : heatModelFwd 2 (-((Real.sqrt 2 : ℝ) : ℂ)) = 0 :=
    heatModelFwd_eq_zero_iff.2
      ⟨-Real.sqrt 2, by rw [profileRoots_two]; simp, Complex.ofReal_neg _⟩
  have hroots : ∀ ρ' : ℂ, heatModelFwd 2 ρ' = 0 →
      ρ' = ((Real.sqrt 2 : ℝ) : ℂ) ∨ ρ' = -((Real.sqrt 2 : ℝ) : ℂ) := by
    intro ρ' h
    obtain ⟨x, hx, rfl⟩ := heatModelFwd_eq_zero_iff.1 h
    rw [profileRoots_two, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Complex.ofReal_neg _)
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ -((Real.sqrt 2 : ℝ) : ℂ) := by
    intro h
    have h2 : (2 : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hs2.ne' (Complex.ofReal_eq_zero.1 h3)
  -- at the centre the opposite sheet is the negative sheet
  have hrefl : ∀ᶠ r in 𝓝[>] (0 : ℝ), -collisionZero τ₀ 0 2 ((Real.sqrt 2 : ℝ) : ℂ) r =
      collisionZero τ₀ 0 2 (-((Real.sqrt 2 : ℝ) : ℂ)) r := by
    have h := collisionZero_reflect hcen hρ₊
    rw [neg_zero] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => -collisionZero τ₀ 0 2 ((Real.sqrt 2 : ℝ) : ℂ) s =
        collisionZero τ₀ 0 2 (-((Real.sqrt 2 : ℝ) : ℂ)) s)
      (h.filter_mono nhdsWithin_le_nhds))
  have hdist : ∀ᶠ r in 𝓝[>] (0 : ℝ), collisionZero τ₀ 0 2 ((Real.sqrt 2 : ℝ) : ℂ) r ≠
      collisionZero τ₀ 0 2 (-((Real.sqrt 2 : ℝ) : ℂ)) r :=
    eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => collisionZero τ₀ 0 2 ((Real.sqrt 2 : ℝ) : ℂ) s ≠
        collisionZero τ₀ 0 2 (-((Real.sqrt 2 : ℝ) : ℂ)) s)
      (collisionZero_ne hcen hρ₊ hρ₋ hne))
  have ht₊ := eventually_nhdsGT_of_exists_Ioo (hcen.exists_transports_turn hρ₊)
  have ht₋ := eventually_nhdsGT_of_exists_Ioo (hcen.exists_transports_turn hρ₋)
  filter_upwards [eventually_turnAction hτ₀, hrefl, hdist, ht₊, ht₋] with r hact hr1 hr2 hr3 hr4
  rw [neg_neg, ← hr1] at hr4
  rw [← hr1] at hr2 hr3
  refine ⟨collisionZero τ₀ 0 2 ((Real.sqrt 2 : ℝ) : ℂ) r, fun hw => hr2 ?_, ?_, hr3, hr4,
    fun z hz hzw hzw' => ?_⟩
  · rw [hw, neg_zero]
  · have h := hr3.zero_left
    rwa [turnPath_zero] at h
  · rcases hact z hz with h | ⟨ζ, m, ρ', -, hc, hρ', hzeq, -⟩
    · exact h
    · exfalso
      have hζ : ζ = 0 := honly ζ
        (by have h := hc.vanish 0 (by omega); rwa [iteratedDeriv_zero] at h)
        (by have h := hc.vanish 1 (by omega); rwa [iteratedDeriv_one] at h)
      subst hζ
      have hm2 : m = 2 := by
        have h1 := isCollision_iff_analyticOrderAt.1 hc
        have h2 := isCollision_iff_analyticOrderAt.1 hcen
        rw [h1] at h2
        exact_mod_cast h2
      subst hm2
      rcases hroots ρ' hρ' with rfl | rfl
      · exact hzw hzeq
      · exact hzw' (hzeq.trans hr1.symm)

/-- **The sign flip of one pair is a forward monodromy.** If at some forward time `τ₀` the family
has a double zero at the centre and no other multiple zero, then at every base time the forward
monodromy group contains an element that exchanges one zero `p ≠ 0` with `−p` and fixes every
other zero. -/
theorem exists_mem_forwardMonodromy_flip_one_pair (hτ₀ : 0 < τ₀.re) (hcen : IsCollision τ₀ 0 2)
    (honly : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 → ζ = 0) {τ : ℂ}
    (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {z : ℂ // complexHeat τ z = 0}, p.1 ≠ 0 ∧
      σ p = fibreNeg τ p ∧ ∀ q, q ≠ p → q ≠ fibreNeg τ p → σ q = q := by
  obtain ⟨r₁, hr₁, hfwd⟩ := exists_isForwardPath_turnPath hτ₀
  obtain ⟨r₂, hr₂, hflip⟩ := exists_Ioo_of_eventually_nhdsGT (eventually_turn_flip hτ₀ hcen honly)
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  obtain ⟨r, hrI₁, hrI₂⟩ : ∃ r, r ∈ Ioo (0 : ℝ) r₁ ∧ r ∈ Ioo (0 : ℝ) r₂ :=
    ⟨min r₁ r₂ / 2, ⟨by positivity, by linarith [min_le_left r₁ r₂]⟩,
      ⟨by positivity, by linarith [min_le_right r₁ r₂]⟩⟩
  have hγ := hfwd r hrI₁
  obtain ⟨w, hw0, hwz, hT₊, -, hfix⟩ := hflip r hrI₂
  obtain ⟨δ, hδ, hδ0, hδ1, σ, hσ, hact⟩ :=
    hγ.exists_mem_forwardMonodromy_of_loop (by rw [turnPath_one, turnPath_zero]) hτ hb
  -- `p` is the transport of `w` to the base time
  obtain ⟨z₁, hz₁⟩ := hδ.exists_transports (z₀ := w) (by rw [hδ0, turnPath_zero]; exact hwz)
  have hz₁0 : complexHeat τ z₁ = 0 := by
    have h := hz₁.zero_right
    rwa [hδ1] at h
  obtain ⟨e, he⟩ := hδ.exists_fibreEquiv (τ := δ 0) rfl hδ1
  refine ⟨σ, hσ, ⟨z₁, hz₁0⟩, fun h0 => hw0 ?_, Subtype.ext ?_, fun q hq hq' => ?_⟩
  · -- `z₁ = 0` would give `w = −w`
    have h0' : z₁ = 0 := h0
    have h1 : Transports δ (-w) z₁ := by
      have h2 := hz₁.neg
      have h3 : -z₁ = z₁ := by rw [h0', neg_zero]
      rwa [h3] at h2
    have h2 : w = -w := hδ.transports_injective hz₁ h1
    have h3 : (2 : ℂ) * w = 0 := by linear_combination h2
    exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
  · exact hδ.transports_unique (hact w (-w) hT₊ ⟨z₁, hz₁0⟩ hz₁) hz₁.neg
  · -- every other zero of the base fibre comes from a zero that the turn fixes
    have hzq : Transports δ (e.symm q).1 q.1 := by
      have h := he (e.symm q)
      rwa [e.apply_symm_apply] at h
    have hz0 : complexHeat (τ₀ + (r : ℂ) ^ 2) (e.symm q).1 = 0 := by
      have h := (e.symm q).2
      rwa [hδ0, turnPath_zero] at h
    have hzw : (e.symm q).1 ≠ w := by
      intro h
      rw [h] at hzq
      exact hq (Subtype.ext (hδ.transports_unique hzq hz₁))
    have hzw' : (e.symm q).1 ≠ -w := by
      intro h
      rw [h] at hzq
      exact hq' (Subtype.ext (hδ.transports_unique hzq hz₁.neg))
    exact Subtype.ext (hδ.transports_unique (hact _ _ (hfix _ hz0 hzw hzw') q hzq) hzq)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
