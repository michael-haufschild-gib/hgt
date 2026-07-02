/-
# The co-component winding certificate

A level-`λ` loop does not wind around points of any sublevel component whose closure it avoids:
the component connects through a boundary point (at level exactly `λ`, off the loop) to the
superlevel set — open mapping of the local Green conjugate produces superlevel points in every
ball around it — and the superlevel set is connected and unbounded, where winding dies by size.
This localizes deep-lobe loops: precritical points of the second parameter sitting in co-branches
are certified unwound, which is the vanishing input of the iterate monodromy sums.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.PolyWinding
import GaloisForLFunctions.Bottcher.GreenSuperlevel
import GaloisForLFunctions.Bottcher.GreenPullback
import GaloisForLFunctions.Bottcher.CoverConstruction

open Complex Set Filter Metric

namespace Bottcher

/-- **The co-component certificate.**  If a `C¹` loop runs at exact Green level `λ > 0` and
avoids the closure of the sublevel component of `p`, then it does not wind around `p`. -/
theorem windInt_eq_zero_of_sublevel_cocomponent (c : ℂ) (ℓ : C1Loop) {lam : ℝ} (hlam : 0 < lam)
    (hper : Function.Periodic ℓ.γ (2 * Real.pi))
    (hloop : ∀ θ : ℝ, greenFunctionDyn c (ℓ.γ θ) = lam)
    {p : ℂ} (hpG : greenFunctionDyn c p < lam)
    (hC : ∀ z ∈ closure (connectedComponentIn {w : ℂ | greenFunctionDyn c w < lam} p),
      ℓ.Avoids z) :
    windInt ℓ p = 0 := by
  classical
  set L : Set ℂ := {w : ℂ | greenFunctionDyn c w < lam} with hLdef
  have hLopen : IsOpen L := isOpen_lt (continuous_greenFunctionDyn c) continuous_const
  have hpL : p ∈ L := hpG
  set C : Set ℂ := connectedComponentIn L p with hCdef
  have hCopen : IsOpen C := hLopen.connectedComponentIn
  have hCconn : IsConnected C := (isConnected_connectedComponentIn_iff).mpr hpL
  have hpC : p ∈ C := mem_connectedComponentIn hpL
  have hCL : C ⊆ L := connectedComponentIn_subset L p
  -- the sublevel is bounded
  have hLbdd : ∀ z ∈ L, ‖z‖ ≤ max (‖c‖ + 3) (Real.exp (lam + 2)) := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have h1 := green_far_gt c lam z hcon
    exact absurd hz (by simp only [hLdef, mem_setOf_eq]; linarith)
  -- a boundary point of the component
  have hbd : ∃ x, x ∈ closure C ∧ x ∉ C := by
    by_contra hcon
    push Not at hcon
    have hclosed : IsClosed C := by
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm
      · intro x hx
        exact hcon x hx
      · exact subset_closure
    have hclopen : IsClopen C := ⟨hclosed, hCopen⟩
    have huniv : C = univ := hclopen.eq_univ hCconn.nonempty
    have h1 : ((max (‖c‖ + 3) (Real.exp (lam + 2)) + 1 : ℝ) : ℂ) ∈ C := by
      rw [huniv]
      trivial
    have h2 := hLbdd _ (hCL h1)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith
  obtain ⟨x, hxcl, hxC⟩ := hbd
  -- the boundary point has level exactly lam
  have hxle : greenFunctionDyn c x ≤ lam := by
    have h1 : closure C ⊆ closure L := closure_mono hCL
    have h2 := h1 hxcl
    have h3 : closure L ⊆ {w : ℂ | greenFunctionDyn c w ≤ lam} := by
      apply closure_minimal
      · intro w hw
        exact le_of_lt (show greenFunctionDyn c w < lam from hw)
      · exact isClosed_le (continuous_greenFunctionDyn c) continuous_const
    exact h3 h2
  have hxeq : greenFunctionDyn c x = lam := by
    rcases lt_or_eq_of_le hxle with h1 | h1
    · exfalso
      have hxL : x ∈ L := h1
      have hunion : IsPreconnected (C ∪ {x}) := by
        apply IsPreconnected.subset_closure hCconn.isPreconnected
        · exact subset_union_left
        · apply union_subset subset_closure
          intro z hz
          rw [mem_singleton_iff] at hz
          subst hz
          exact hxcl
      have hsub : C ∪ {x} ⊆ C := by
        rw [hCdef]
        apply IsPreconnected.subset_connectedComponentIn hunion
        · exact Or.inl hpC
        · apply union_subset hCL
          intro z hz
          rw [mem_singleton_iff] at hz
          subst hz
          exact hxL
      exact hxC (hsub (Or.inr rfl))
    · exact h1
  -- the loop avoids a ball around the boundary point
  have hxavoid : ℓ.Avoids x := hC x hxcl
  have himgcl : IsClosed (ℓ.γ '' Set.Icc (0:ℝ) (2 * Real.pi)) := ℓ.isCompact_image.isClosed
  have hximg : x ∉ ℓ.γ '' Set.Icc (0:ℝ) (2 * Real.pi) := by
    rintro ⟨θ, _, hθ⟩
    exact hxavoid θ hθ
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (himgcl.isOpen_compl.mem_nhds hximg)
  -- superlevel points in every ball around x: open mapping of the local Green conjugate
  have hxK : x ∉ filledJulia c := by
    intro hcon
    have h1 : greenFunctionDyn c x = 0 := (greenFunctionDyn_eq_zero_iff c x).mpr hcon
    rw [hxeq] at h1
    linarith
  obtain ⟨r, F, hr0, hFan, hFre⟩ := exists_local_greenConjugate_basin hxK
  -- shrink to stay in the basin and in the loop-free ball
  have hbasin_open : IsOpen (filledJulia c)ᶜ := (isClosed_filledJulia c).isOpen_compl
  obtain ⟨r₁, hr₁0, hr₁⟩ := Metric.isOpen_iff.mp hbasin_open x hxK
  set ρ : ℝ := min (min r r₁) δ with hρdef
  have hρ0 : 0 < ρ := by
    apply lt_min (lt_min hr0 hr₁0) hδ0
  have hρr : ρ ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρr₁ : ρ ≤ r₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρδ : ρ ≤ δ := min_le_right _ _
  -- Green agrees with greenLimit on the small ball
  have hGrB : ∀ w ∈ ball x ρ, greenFunctionDyn c w = (F w).re := by
    intro w hw
    have hwK : w ∉ filledJulia c := hr₁ (mem_of_mem_of_subset hw
      (Metric.ball_subset_ball hρr₁))
    have h1 : greenFunctionDyn c w = greenLimit c w := by
      unfold greenFunctionDyn
      rw [if_neg hwK]
    rw [h1, ← hFre (mem_of_mem_of_subset hw (Metric.ball_subset_ball hρr))]
  -- F is nonconstant on the small ball: it meets C where the level drops
  obtain ⟨y₀, hy₀C, hy₀B⟩ : ∃ y₀, y₀ ∈ C ∧ y₀ ∈ ball x ρ := by
    have h1 := Metric.mem_closure_iff.mp hxcl ρ hρ0
    obtain ⟨y₀, hy₀C, hy₀d⟩ := h1
    exact ⟨y₀, hy₀C, by rwa [Metric.mem_ball, dist_comm]⟩
  have hFne : F y₀ ≠ F x := by
    intro hcon
    have h1 := hGrB y₀ hy₀B
    have h2 := hGrB x (Metric.mem_ball_self hρ0)
    have h3 : greenFunctionDyn c y₀ < lam := hCL hy₀C
    rw [h1, hcon, ← h2, hxeq] at h3
    exact lt_irrefl _ h3
  -- open mapping: the image of the small ball is open around F x
  have hFanB : AnalyticOnNhd ℂ F (ball x ρ) :=
    hFan.mono (Metric.ball_subset_ball hρr)
  have hFopen : IsOpen (F '' ball x ρ) := by
    rcases hFanB.is_constant_or_isOpen (convex_ball x ρ).isPreconnected with hconst | hopen
    · exfalso
      obtain ⟨v, hv⟩ := hconst
      have h1 := hv y₀ hy₀B
      have h2 := hv x (Metric.mem_ball_self hρ0)
      rw [h1, h2] at hFne
      exact hFne rfl
    · exact hopen _ (Set.Subset.refl _) isOpen_ball
  -- a superlevel point in the ball
  obtain ⟨y, hyB, hyG⟩ : ∃ y ∈ ball x ρ, lam < greenFunctionDyn c y := by
    have h1 : F x ∈ F '' ball x ρ := ⟨x, Metric.mem_ball_self hρ0, rfl⟩
    obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hFopen _ h1
    have h2 : F x + (ε / 2 : ℝ) ∈ F '' ball x ρ := by
      apply hε
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    obtain ⟨y, hyB, hyF⟩ := h2
    refine ⟨y, hyB, ?_⟩
    have h3 := hGrB y hyB
    have h4 := hGrB x (Metric.mem_ball_self hρ0)
    rw [h3, hyF]
    have h5 : (F x + ((ε / 2 : ℝ) : ℂ)).re = (F x).re + ε / 2 := by
      simp [Complex.add_re]
    rw [h5, ← h4, hxeq]
    linarith
  -- assemble the connector
  set S : Set ℂ := (C ∪ ball x ρ) ∪ {w : ℂ | lam < greenFunctionDyn c w} with hSdef
  have hSp : p ∈ S := Or.inl (Or.inl hpC)
  have hSconn : IsPreconnected S := by
    have h1 : IsConnected (C ∪ ball x ρ) := by
      apply IsConnected.union ⟨y₀, hy₀C, hy₀B⟩ hCconn
      exact ⟨⟨x, Metric.mem_ball_self hρ0⟩, (convex_ball x ρ).isPreconnected⟩
    have h2 : IsConnected ((C ∪ ball x ρ) ∪ {w : ℂ | lam < greenFunctionDyn c w}) := by
      apply IsConnected.union ⟨y, Or.inr hyB, hyG⟩ h1
      exact isConnected_green_superlevel c hlam
    exact h2.isPreconnected
  have hSavoid : ∀ z ∈ S, ℓ.Avoids z := by
    rintro z (hz | hz)
    · rcases hz with hz | hz
      · intro θ hθ
        have h1 := hloop θ
        rw [hθ] at h1
        have h2 : greenFunctionDyn c z < lam := hCL hz
        linarith
      · intro θ hθ
        -- reduce θ into the fundamental period, then the δ-ball avoidance bites
        obtain ⟨θ', hθ'I, hθ'eq⟩ : ∃ θ' ∈ Set.Ico (0:ℝ) (2 * Real.pi), ℓ.γ θ = ℓ.γ θ' := by
          refine ⟨2 * Real.pi * Int.fract (θ / (2 * Real.pi)), ⟨?_, ?_⟩, ?_⟩
          · have h0 := Int.fract_nonneg (θ / (2 * Real.pi))
            nlinarith [Real.pi_pos]
          · have h1 := Int.fract_lt_one (θ / (2 * Real.pi))
            nlinarith [Real.pi_pos]
          · have h2 := hper.sub_int_mul_eq (n := ⌊θ / (2 * Real.pi)⌋) (x := θ)
            rw [← h2]
            congr 1
            rw [Int.fract]
            have hπ : 2 * Real.pi ≠ 0 := by positivity
            field_simp
        have h1 : ℓ.γ θ' ∈ ℓ.γ '' Set.Icc (0:ℝ) (2 * Real.pi) :=
          ⟨θ', ⟨hθ'I.1, le_of_lt hθ'I.2⟩, rfl⟩
        have h2 : z ∈ ball x δ := mem_of_mem_of_subset hz (Metric.ball_subset_ball hρδ)
        have h3 := hδ h2
        rw [hθ] at hθ'eq
        rw [hθ'eq] at h3
        exact h3 h1
    · intro θ hθ
      have h1 := hloop θ
      rw [hθ] at h1
      have h2 : lam < greenFunctionDyn c z := hz
      linarith
  have hSunb : ∀ R : ℝ, ∃ z ∈ S, R < ‖z‖ := by
    intro R
    set t : ℝ := max R (max (‖c‖ + 3) (Real.exp (lam + 2))) + 1 with htdef
    refine ⟨((t : ℝ) : ℂ), ?_, ?_⟩
    · right
      show lam < greenFunctionDyn c ((t : ℝ) : ℂ)
      apply green_far_gt c lam
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by
        have h1 : (0:ℝ) ≤ max R (max (‖c‖ + 3) (Real.exp (lam + 2))) :=
          le_trans (by positivity : (0:ℝ) ≤ ‖c‖ + 3)
            (le_trans (le_max_left _ _) (le_max_right _ _))
        linarith)]
      have h2 : max (‖c‖ + 3) (Real.exp (lam + 2)) ≤ max R (max (‖c‖ + 3) (Real.exp (lam + 2))) :=
        le_max_right _ _
      linarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by
        have h1 : (0:ℝ) ≤ max R (max (‖c‖ + 3) (Real.exp (lam + 2))) :=
          le_trans (by positivity : (0:ℝ) ≤ ‖c‖ + 3)
            (le_trans (le_max_left _ _) (le_max_right _ _))
        linarith)]
      have h3 : R ≤ max R (max (‖c‖ + 3) (Real.exp (lam + 2))) := le_max_left _ _
      linarith
  exact windInt_eq_zero_of_unbounded_connector ℓ hSconn hSavoid hSunb hSp

end Bottcher
