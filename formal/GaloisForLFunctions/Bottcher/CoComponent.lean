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
import GaloisForLFunctions.Bottcher.TowerCertificates
import GaloisForLFunctions.Bottcher.AnnulusRoot
import GaloisForLFunctions.Bottcher.SectionTowerStep
import GaloisForLFunctions.Bottcher.BottcherTowerScaffold
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

namespace Bottcher

/-- **The collar dichotomy.**  A depth-`k` lobe circle at radius `r` has an `SL`-parametrized
transversal collar: every sublevel point near the loop lies in the image of the inner band, hence
in the loop's own sublevel component.  Consequently the closure of any OTHER sublevel component
avoids the loop, and the co-component certificate applies verbatim. -/
theorem windInt_lobe_eq_zero_of_ne_component {c : ℂ} {ra rb : ℝ} {k : ℕ}
    (hra1 : 1 < ra) (_hrb : ra < rb)
    {SL : ℂ → ℂ} (hSLan : AnalyticOnNhd ℂ SL (annulusSet ra rb))
    (hSLlev : ∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k)
    (hSLdne : ∀ v ∈ annulusSet ra rb, deriv SL v ≠ 0)
    {r : ℝ} (hr1 : ra < r) (hr2 : r < rb)
    {p : ℂ} (hpG : greenFunctionDyn c p < Real.log r / 2 ^ k)
    (hne : connectedComponentIn {w : ℂ | greenFunctionDyn c w < Real.log r / 2 ^ k} p ≠
      connectedComponentIn {w : ℂ | greenFunctionDyn c w < Real.log r / 2 ^ k}
        (SL (((ra + r) / 2 : ℝ) : ℂ))) :
    windInt (sectionLoop hSLan (circleMap_mem_annulusSet
      (by linarith : (0:ℝ) < r) hr1 hr2)) p = 0 := by
  classical
  set lam : ℝ := Real.log r / 2 ^ k with hlamdef
  have hrapos : (0:ℝ) < ra := by linarith
  have hlam : 0 < lam := by
    rw [hlamdef]
    apply div_pos (Real.log_pos (by linarith)) (by positivity)
  set ℓ : C1Loop := sectionLoop hSLan (circleMap_mem_annulusSet
    (by linarith : (0:ℝ) < r) hr1 hr2) with hℓdef
  have hper : Function.Periodic ℓ.γ (2 * Real.pi) := by
    intro θ
    show SL (circleMap 0 r (θ + 2 * Real.pi)) = SL (circleMap 0 r θ)
    rw [periodic_circleMap 0 r θ]
  have hloop : ∀ θ : ℝ, greenFunctionDyn c (ℓ.γ θ) = lam := by
    intro θ
    show greenFunctionDyn c (SL (circleMap 0 r θ)) = lam
    rw [hSLlev _ (circleMap_mem_annulusSet (by linarith) hr1 hr2 θ)]
    congr 1
    simp [circleMap, abs_of_pos (show (0:ℝ) < r by linarith)]
  apply windInt_eq_zero_of_sublevel_cocomponent c ℓ hlam hper hloop hpG
  -- the closure of p's component avoids the loop, by the collar dichotomy
  intro z hzcl θ hθ
  -- z is the loop point SL (circleMap 0 r θ); the SL-image of the band is open around it
  set V : Set ℂ := SL '' annulusSet ra rb with hVdef
  have hVopen : IsOpen V := isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) hSLan hSLdne
  have hzV : z ∈ V := by
    rw [← hθ]
    exact ⟨circleMap 0 r θ, circleMap_mem_annulusSet (by linarith) hr1 hr2 θ, rfl⟩
  -- a component point inside the collar
  have hmem : (V ∩ connectedComponentIn {w : ℂ | greenFunctionDyn c w < lam} p).Nonempty := by
    exact mem_closure_iff.mp hzcl V hVopen hzV
  obtain ⟨y, hyV, hyC⟩ := hmem
  obtain ⟨v, hv, rfl⟩ := hyV
  -- the collar point is in the inner band
  have hyG : greenFunctionDyn c (SL v) < lam := by
    have h0 : SL v ∈ {w : ℂ | greenFunctionDyn c w < lam} :=
      connectedComponentIn_subset {w : ℂ | greenFunctionDyn c w < lam} p hyC
    exact h0
  have hvin : v ∈ annulusSet ra r := by
    refine ⟨hv.1, ?_⟩
    have h1 := hSLlev v hv
    rw [h1] at hyG
    have h2 : Real.log ‖v‖ < Real.log r := by
      have h3 : (0:ℝ) < (2:ℝ) ^ k := by positivity
      rw [hlamdef] at hyG
      exact (div_lt_div_iff_of_pos_right h3).mp hyG
    have h4 : (0:ℝ) < ‖v‖ := lt_trans (by linarith) hv.1
    calc ‖v‖ = Real.exp (Real.log ‖v‖) := (Real.exp_log h4).symm
      _ < Real.exp (Real.log r) := Real.exp_lt_exp.mpr h2
      _ = r := Real.exp_log (by linarith)
  -- the inner-band image is connected, inside the sublevel, and contains the anchor
  set v₀ : ℂ := (((ra + r) / 2 : ℝ) : ℂ) with hv₀def
  have hv₀ : v₀ ∈ annulusSet ra r := by
    constructor <;> rw [hv₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < (ra + r) / 2)]
    · linarith
    · linarith
  have hinner_sub : SL '' annulusSet ra r ⊆ {w : ℂ | greenFunctionDyn c w < lam} := by
    rintro w ⟨u, hu, rfl⟩
    have h1 : u ∈ annulusSet ra rb := ⟨hu.1, lt_trans hu.2 hr2⟩
    show greenFunctionDyn c (SL u) < lam
    rw [hSLlev u h1, hlamdef]
    apply div_lt_div_of_pos_right _ (by positivity)
    · exact Real.log_lt_log (lt_trans (by linarith) hu.1) hu.2
  have hinner_conn : IsPreconnected (SL '' annulusSet ra r) :=
    ((isConnected_annulus (by linarith : (0:ℝ) < ra) hr1).image _
      ((hSLan.mono (fun u hu => ⟨hu.1, lt_trans hu.2 hr2⟩)).continuousOn)).isPreconnected
  -- the collar point and the anchor share a component
  have hcomp1 : SL '' annulusSet ra r ⊆
      connectedComponentIn {w : ℂ | greenFunctionDyn c w < lam} (SL v₀) := by
    apply IsPreconnected.subset_connectedComponentIn hinner_conn
    · exact ⟨v₀, hv₀, rfl⟩
    · exact hinner_sub
  have hyC0 : SL v ∈ connectedComponentIn {w : ℂ | greenFunctionDyn c w < lam} (SL v₀) :=
    hcomp1 ⟨v, hvin, rfl⟩
  -- so p's component is the anchor's — contradiction
  have heq1 := connectedComponentIn_eq hyC
  have heq2 := connectedComponentIn_eq hyC0
  exact hne (heq1.trans heq2.symm)

end Bottcher
