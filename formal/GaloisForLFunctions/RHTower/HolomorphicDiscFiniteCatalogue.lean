import GaloisForLFunctions.Bottcher.MontelNormal

open Complex Metric Set Filter Topology BoundedContinuousFunction
noncomputable section
namespace RHTower

/-- Cauchy equicontinuity on every strictly smaller disc, with the actual positive
gap rather than a half-radius restriction. -/
theorem equicontinuous_holomorphic_disc_family {ι : Type*} {f : ι → ℂ → ℂ}
    {c : ℂ} {r ρ C : ℝ} (hrρ : r < ρ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c ρ))
    (hbd : ∀ i, ∀ z ∈ ball c ρ, ‖f i z‖ ≤ C) :
    Equicontinuous (fun (i : ι) (z : closedBall c r) => f i z.1) := by
  have hgap : 0 < ρ - r := sub_pos.mpr hrρ
  have hsub : closedBall c r ⊆ ball c ρ := closedBall_subset_ball hrρ
  have hderiv (i : ι) (z : ℂ) (hz : z ∈ closedBall c r) :
      ‖deriv (f i) z‖ ≤ 2 * C / (ρ - r) := by
    have hlocal : ball z (ρ - r) ⊆ ball c ρ := by
      intro w hw
      have hwz : dist w z < ρ - r := hw
      have hzc : dist z c ≤ r := hz
      have htri := dist_triangle w z c
      change dist w c < ρ
      linarith
    exact Bottcher.norm_deriv_le_of_bounded_on_ball hgap ((hf i).mono hlocal)
      (fun w hw => hbd i w (hlocal hw)) z (mem_ball_self (by positivity))
  have hdiff (i : ι) (z : ℂ) (hz : z ∈ closedBall c r) : HasDerivAt (f i) (deriv (f i) z) z :=
    ((hf i).differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasDerivAt
  have hlip (i : ι) {z w : ℂ} (hz : z ∈ closedBall c r) (hw : w ∈ closedBall c r) :
      ‖f i z - f i w‖ ≤ (2 * C / (ρ - r)) * ‖z - w‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hdiff i x hx).hasDerivWithinAt) (hderiv i) (convex_closedBall c r) hw hz
  refine Metric.equicontinuous_of_continuity_modulus (fun d => (2 * C / (ρ - r)) * d) ?_ _ ?_
  · have hcont : Continuous (fun d : ℝ => (2 * C / (ρ - r)) * d) := continuous_const.mul continuous_id
    simpa using hcont.tendsto 0
  · intro x y i
    rw [Complex.dist_eq, Subtype.dist_eq, Complex.dist_eq]
    exact hlip i x.property y.property

/-- A uniformly bounded holomorphic family has finitely many actual members
approximating every member uniformly on the inner closed disc. -/
theorem exists_finite_holomorphic_disc_catalogue {ι : Type*} (f : ι → ℂ → ℂ)
    {c : ℂ} {r ρ C : ℝ} (hrρ : r < ρ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c ρ))
    (hbd : ∀ i, ∀ z ∈ ball c ρ, ‖f i z‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset ι, ∀ i : ι, ∃ j ∈ T, ∀ z ∈ closedBall c r, ‖f i z - f j z‖ < ε := by
  classical
  haveI : CompactSpace (closedBall c r) := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hsub : closedBall c r ⊆ ball c ρ := closedBall_subset_ball hrρ
  let cmap : ι → C(closedBall c r, ℂ) := fun i =>
    ⟨(closedBall c r).restrict (f i), ((hf i).continuousOn.mono hsub).restrict⟩
  let bcf : ι → (closedBall c r →ᵇ ℂ) := fun i => mkOfCompact (cmap i)
  let A : Set (closedBall c r →ᵇ ℂ) := Set.range bcf
  have hequi := equicontinuous_holomorphic_disc_family hrρ hf hbd
  have hsec (a : A) : bcf a.property.choose = (a : closedBall c r →ᵇ ℂ) := a.property.choose_spec
  have hcoe : ((↑) : A → closedBall c r → ℂ) =
      (fun (i : ι) (z : closedBall c r) => f i z.1) ∘ (fun a : A => a.property.choose) := by
    funext a z
    exact (DFunLike.congr_fun (hsec a) z).symm
  have hAeq : Equicontinuous ((↑) : A → closedBall c r → ℂ) := by
    rw [hcoe]
    exact hequi.comp _
  have hin (g : closedBall c r →ᵇ ℂ) (z : closedBall c r) (hg : g ∈ A) :
      g z ∈ closedBall (0 : ℂ) C := by
    obtain ⟨i, rfl⟩ := hg
    rw [mem_closedBall, dist_zero_right]
    exact hbd i z (hsub z.property)
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C) (isCompact_closedBall _ _) A hin hAeq
  obtain ⟨U, hUA, hUf, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcompact hε
  letI := hUf.fintype
  let idx : U → ι := fun u => (hUA u.property).choose
  have hidx (u : U) : bcf (idx u) = (u : closedBall c r →ᵇ ℂ) := (hUA u.property).choose_spec
  refine ⟨Finset.univ.image idx, ?_⟩
  intro i
  obtain ⟨u, hu, hdist⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_range_self i))
  refine ⟨idx ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩, ?_⟩
  intro z hz
  have hdist' : dist (bcf i) (bcf (idx ⟨u, hu⟩)) < ε := by
    rw [hidx ⟨u, hu⟩]
    exact hdist
  have hpoint : ‖f i z - f (idx ⟨u, hu⟩) z‖ ≤ dist (bcf i) (bcf (idx ⟨u, hu⟩)) := by
    simpa [bcf, cmap, mkOfCompact_apply, Complex.dist_eq] using
      BoundedContinuousFunction.dist_coe_le_dist (f := bcf i) (g := bcf (idx ⟨u, hu⟩))
        (⟨z, hz⟩ : closedBall c r)
  exact hpoint.trans_lt hdist'

end RHTower
