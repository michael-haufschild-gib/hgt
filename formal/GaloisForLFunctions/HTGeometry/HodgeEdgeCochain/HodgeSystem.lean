import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Coercivity
import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Attractor
import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.HarmonicFibre

/-!
# The two-field system on the divergence-free edge space

This file instantiates the abstract theory of `Energy.lean`, `GlobalExistence.lean`,
`Attractor.lean` and `HarmonicFibre.lean` on the actual phase space of Boudourides,
*Hodge Coercivity and Global Dynamics in Two-Field Edge-Cochain Systems with MHD-Type
Cancellation* (arXiv:2608.19360): the divergence-free edge-cochain space `V = ker d₀*` with the
degree-one Hodge Laplacian as dissipative operator.

## Main results

* `hodgeOp` — `Δ₁` restricted to `V`, as a continuous operator on `V`.
* `exists_pos_coercive_hodgeOp` — **Theorem 1** transported to `V`.
* `hodgeSystem` — the paper's system as an `AdmissibleSystem`, hence a semiflow with a compact
  global attractor whenever the harmonic space is trivial.
* `hodge_exists_global_solution` — **Lemma 2** for the paper's system.
* `hodge_energy_identity` — **Theorem 2** for the paper's system.
* `hodge_unforced_decay` — **Theorem 4** for the paper's system.
* `hodge_absorbing_ball`, `hodge_attractor_*` — **Theorem 3** for the paper's system.
-/

open Set
open scoped InnerProductSpace

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

section HodgeSystem

variable {C0 C1 C2 : Type*}
  [NormedAddCommGroup C0] [InnerProductSpace ℝ C0] [FiniteDimensional ℝ C0]
  [NormedAddCommGroup C1] [InnerProductSpace ℝ C1] [FiniteDimensional ℝ C1]
  [NormedAddCommGroup C2] [InnerProductSpace ℝ C2] [FiniteDimensional ℝ C2]

/-- The Hodge Laplacian restricted to the divergence-free space, as a linear map on `V`. -/
noncomputable def hodgeRestrict (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0) :
    ↥(divFree d0) →ₗ[ℝ] ↥(divFree d0) where
  toFun v := ⟨hodgeLaplacian d0 d1 (v : C1), hodgeLaplacian_mem_divFree d0 d1 hdd v.2⟩
  map_add' := by intro x y; ext; simp
  map_smul' := by intro c x; ext; simp

/-- `Δ₁|_V` as a continuous operator on the divergence-free space. -/
noncomputable def hodgeOp (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0) :
    ↥(divFree d0) →L[ℝ] ↥(divFree d0) :=
  LinearMap.toContinuousLinearMap (hodgeRestrict d0 d1 hdd)

@[simp] theorem hodgeOp_coe (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (v : ↥(divFree d0)) :
    ((hodgeOp d0 d1 hdd v : ↥(divFree d0)) : C1) = hodgeLaplacian d0 d1 (v : C1) := rfl

theorem inner_hodgeOp (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (v : ↥(divFree d0)) :
    ⟪hodgeOp d0 d1 hdd v, v⟫_ℝ = ⟪hodgeLaplacian d0 d1 (v : C1), (v : C1)⟫_ℝ :=
  Submodule.coe_inner _ _ _

theorem inner_hodgeOp_nonneg (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (v : ↥(divFree d0)) : 0 ≤ ⟪hodgeOp d0 d1 hdd v, v⟫_ℝ := by
  rw [inner_hodgeOp]
  exact inner_hodgeLaplacian_self_nonneg d0 d1 _

/-- **Theorem 1 on the phase space.**  The Hodge coercivity criterion, read on `V` itself. -/
theorem exists_pos_coercive_hodgeOp (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hharm : harmonic d0 d1 = ⊥) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : ↥(divFree d0), lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪hodgeOp d0 d1 hdd v, v⟫_ℝ := by
  obtain ⟨lam, hlam, hb⟩ := (hodge_coercive_iff_harmonic_eq_bot d0 d1).mp hharm
  refine ⟨lam, hlam, fun v => ?_⟩
  rw [inner_hodgeOp]
  exact hb (v : C1) v.2

/-- The paper's system, packaged as an `AdmissibleSystem` on `V`. -/
noncomputable def hodgeSystem (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)) (hB : IsCancelling B)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) (f g : ↥(divFree d0)) :
    AdmissibleSystem ↥(divFree d0) where
  A := hodgeOp d0 d1 hdd
  B := B
  nu := nu
  eta := eta
  f := f
  g := g
  cancelling := hB
  nonneg := inner_hodgeOp_nonneg d0 d1 hdd
  nu_pos := hnu
  eta_pos := heta

/-- **Lemma 2 for the paper's system.**  Global existence on the divergence-free edge space. -/
theorem hodge_exists_global_solution (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    {B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hB : IsCancelling B)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) (f g u₀ h₀ : ↥(divFree d0)) :
    ∃ u h : ℝ → ↥(divFree d0), u 0 = u₀ ∧ h 0 = h₀ ∧
      IsSolutionOn (hodgeOp d0 d1 hdd) B nu eta f g u h (Ici 0) :=
  exists_isSolutionOn_Ici hB (inner_hodgeOp_nonneg d0 d1 hdd) hnu.le heta.le u₀ h₀

/-- **Theorem 2 for the paper's system.** -/
theorem hodge_energy_identity (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    {B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hB : IsCancelling B)
    {nu eta : ℝ} {f g : ↥(divFree d0)} {u h : ℝ → ↥(divFree d0)} {t : ℝ}
    (hu : HasDerivAt u (velocityField (hodgeOp d0 d1 hdd) B nu f (u t) (h t)) t)
    (hh : HasDerivAt h (magneticField (hodgeOp d0 d1 hdd) B eta g (u t) (h t)) t) :
    HasDerivAt (energy u h)
      (2 * (-(dissipation (hodgeOp d0 d1 hdd) nu eta u h t) + forcingPower f g u h t)) t :=
  hasDerivAt_energy hB hu hh

/-- **Theorem 4 for the paper's system.**  On a complex with trivial harmonic space every
unforced solution decays at the exponential rate `2β = 2 min(ν,η) λ*`. -/
theorem hodge_unforced_decay (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hharm : harmonic d0 d1 = ⊥)
    {B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hB : IsCancelling B)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) {u h : ℝ → ↥(divFree d0)} {T : ℝ}
    (hsol : IsSolutionOn (hodgeOp d0 d1 hdd) B nu eta 0 0 u h (Icc 0 T)) :
    ∃ beta : ℝ, 0 < beta ∧ ∀ t ∈ Icc (0 : ℝ) T,
      energy u h t ≤ energy u h 0 * Real.exp (-(2 * beta) * t) := by
  obtain ⟨lam, hlam, hcoe⟩ := exists_pos_coercive_hodgeOp d0 d1 hdd hharm
  exact ⟨decayRate nu eta lam, decayRate_pos hnu heta hlam,
    energy_le_unforced_of_coercive hB hcoe hnu heta hlam hsol⟩

/-- **Theorem 3 for the paper's system (positive invariance).** -/
theorem hodge_absorbing_ball (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hharm : harmonic d0 d1 = ⊥)
    {B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hB : IsCancelling B)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) {f g : ↥(divFree d0)}
    {u h : ℝ → ↥(divFree d0)} {T : ℝ}
    (hsol : IsSolutionOn (hodgeOp d0 d1 hdd) B nu eta f g u h (Icc 0 T)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ R : ℝ,
      Real.sqrt (‖f‖ ^ (2 : ℕ) + ‖g‖ ^ (2 : ℕ)) / decayRate nu eta lam < R → energy u h 0 ≤ R ^ (2 : ℕ) →
      ∀ t ∈ Icc (0 : ℝ) T, energy u h t ≤ R ^ (2 : ℕ) := by
  obtain ⟨lam, hlam, hcoe⟩ := exists_pos_coercive_hodgeOp d0 d1 hdd hharm
  exact ⟨lam, hlam, fun R hR h0 =>
    absorbing_ball_positively_invariant hB hcoe hnu heta hlam hsol hR h0⟩

/-- **Theorem 3 for the paper's system.**  On a complex with trivial harmonic space the
divergence-free edge-cochain system generates a semiflow whose energy balls of radius `R > F/β`
are positively invariant and which possesses a nonempty compact invariant global attractor
`A = ω(B_R)`. -/
theorem hodge_compact_global_attractor (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hdd : d1 ∘ₗ d0 = 0) (hharm : harmonic d0 d1 = ⊥)
    {B : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hB : IsCancelling B)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) (f g : ↥(divFree d0)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ R : ℝ,
      Real.sqrt (‖f‖ ^ (2 : ℕ) + ‖g‖ ^ (2 : ℕ)) / decayRate nu eta lam < R →
      ((hodgeSystem d0 d1 hdd B hB hnu heta f g).attractor R).Nonempty ∧
        IsCompact ((hodgeSystem d0 d1 hdd B hB hnu heta f g).attractor R) ∧
        IsInvariant (hodgeSystem d0 d1 hdd B hB hnu heta f g).flow
          ((hodgeSystem d0 d1 hdd B hB hnu heta f g).attractor R) ∧
        (hodgeSystem d0 d1 hdd B hB hnu heta f g).attractor R
          ⊆ AdmissibleSystem.energyBall ↥(divFree d0) R ∧
        ∀ t : ℝ, 0 ≤ t → MapsTo (fun x => (hodgeSystem d0 d1 hdd B hB hnu heta f g).orbit x t)
          (AdmissibleSystem.energyBall ↥(divFree d0) R)
          (AdmissibleSystem.energyBall ↥(divFree d0) R) := by
  obtain ⟨lam, hlam, hcoe⟩ := exists_pos_coercive_hodgeOp d0 d1 hdd hharm
  refine ⟨lam, hlam, fun R hR => ?_⟩
  set S := hodgeSystem d0 d1 hdd B hB hnu heta f g with hS
  have hcoeS : ∀ v : ↥(divFree d0), lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪S.A v, v⟫_ℝ := hcoe
  have hRS : Real.sqrt (‖S.f‖ ^ (2 : ℕ) + ‖S.g‖ ^ (2 : ℕ)) / decayRate S.nu S.eta lam < R := hR
  exact ⟨S.attractor_nonempty hcoeS hlam hRS, S.isCompact_attractor hcoeS hlam hRS,
    S.isInvariant_attractor R, S.attractor_subset hcoeS hlam hRS,
    fun t ht => S.energyBall_mapsTo hcoeS hlam hRS ht⟩

/-! ## The harmonic fibre structure on `V` (§5) -/

/-- The harmonic subspace, read inside the phase space `V`. -/
noncomputable def harmSub (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    Submodule ℝ ↥(divFree d0) := (harmonic d0 d1).comap (divFree d0).subtype

theorem mem_harmSub (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (w : ↥(divFree d0)) :
    w ∈ harmSub d0 d1 ↔ (w : C1) ∈ harmonic d0 d1 := Iff.rfl

/-- The harmonic projector `Q` on `V`. -/
noncomputable def harmProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    ↥(divFree d0) →L[ℝ] ↥(divFree d0) := (harmSub d0 d1).starProjection

/-- The complementary projector `P₀ = I - Q` on `V`. -/
noncomputable def compProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    ↥(divFree d0) →L[ℝ] ↥(divFree d0) := (harmSub d0 d1)ᗮ.starProjection

theorem compProj_symm (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (x y : ↥(divFree d0)) :
    ⟪compProj d0 d1 x, y⟫_ℝ = ⟪x, compProj d0 d1 y⟫_ℝ :=
  Submodule.inner_starProjection_left_eq_right _ _ _

theorem compProj_idem (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (x : ↥(divFree d0)) :
    compProj d0 d1 (compProj d0 d1 x) = compProj d0 d1 x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

theorem harmProj_compProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (x : ↥(divFree d0)) :
    harmProj d0 d1 (compProj d0 d1 x) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.starProjection_apply_mem _ _)

theorem harmProj_add_compProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (x : ↥(divFree d0)) :
    harmProj d0 d1 x + compProj d0 d1 x = x :=
  Submodule.starProjection_add_starProjection_orthogonal _

/-- The Hodge Laplacian kills the harmonic component. -/
theorem hodgeOp_harmProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (x : ↥(divFree d0)) : hodgeOp d0 d1 hdd (harmProj d0 d1 x) = 0 := by
  have hmem : (harmProj d0 d1 x : ↥(divFree d0)) ∈ harmSub d0 d1 :=
    Submodule.starProjection_apply_mem _ _
  have : hodgeLaplacian d0 d1 ((harmProj d0 d1 x : ↥(divFree d0)) : C1) = 0 := hmem
  ext
  simpa using this

/-- The range of the Hodge Laplacian is orthogonal to the harmonic space. -/
theorem harmProj_hodgeOp (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (x : ↥(divFree d0)) : harmProj d0 d1 (hodgeOp d0 d1 hdd x) = 0 := by
  refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hw0 : hodgeLaplacian d0 d1 ((w : ↥(divFree d0)) : C1) = 0 := hw
  have : ⟪(w : C1), hodgeLaplacian d0 d1 ((x : ↥(divFree d0)) : C1)⟫_ℝ = 0 := by
    rw [← inner_hodgeLaplacian_left d0 d1 (w : C1) ((x : ↥(divFree d0)) : C1), hw0,
      inner_zero_left]
  simpa [Submodule.coe_inner] using this

theorem compProj_hodgeOp (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    (x : ↥(divFree d0)) :
    compProj d0 d1 (hodgeOp d0 d1 hdd x) = hodgeOp d0 d1 hdd (compProj d0 d1 x) := by
  have h1 : harmProj d0 d1 (hodgeOp d0 d1 hdd x) + compProj d0 d1 (hodgeOp d0 d1 hdd x)
      = hodgeOp d0 d1 hdd x := harmProj_add_compProj d0 d1 _
  rw [harmProj_hodgeOp d0 d1 hdd x, zero_add] at h1
  have h2 : harmProj d0 d1 x + compProj d0 d1 x = x := harmProj_add_compProj d0 d1 x
  have h3 : hodgeOp d0 d1 hdd (harmProj d0 d1 x) + hodgeOp d0 d1 hdd (compProj d0 d1 x)
      = hodgeOp d0 d1 hdd x := by rw [← map_add, h2]
  rw [hodgeOp_harmProj d0 d1 hdd x, zero_add] at h3
  rw [h1, h3]

/-- **Theorem 1 on `V₀`.**  The complementary space is always coercive. -/
theorem exists_pos_coercive_compProj (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    (hdd : d1 ∘ₗ d0 = 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v ∈ Set.range (compProj d0 d1 : ↥(divFree d0) → ↥(divFree d0)),
      lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪hodgeOp d0 d1 hdd v, v⟫_ℝ := by
  obtain ⟨lam, hlam, hb⟩ := exists_pos_coercive_on_divFreeComplement d0 d1
  refine ⟨lam, hlam, ?_⟩
  rintro _ ⟨x, rfl⟩
  set v := compProj d0 d1 x with hv
  have hmemV : (v : C1) ∈ divFree d0 := v.2
  have hperp : (v : C1) ∈ (harmonic d0 d1)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hwV : w ∈ divFree d0 := harmonic_le_divFree d0 d1 hw
    have hwsub : (⟨w, hwV⟩ : ↥(divFree d0)) ∈ harmSub d0 d1 := hw
    have hvperp : v ∈ (harmSub d0 d1)ᗮ := Submodule.starProjection_apply_mem _ _
    have := (Submodule.mem_orthogonal _ v).mp hvperp ⟨w, hwV⟩ hwsub
    simpa [Submodule.coe_inner] using this
  rw [inner_hodgeOp]
  exact hb (v : C1) ⟨hmemV, hperp⟩

/-- **Theorem 5 for the paper's system.**  With the harmonic-decoupled interaction the harmonic
components are conserved and the complementary components decay to zero at the rate `2β₊`; hence
every unforced trajectory on the affine fibre converges to its harmonic label. -/
theorem hodge_fibre_theorem (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (hdd : d1 ∘ₗ d0 = 0)
    {Bt : ↥(divFree d0) →L[ℝ] ↥(divFree d0) →L[ℝ] ↥(divFree d0)} (hBt : IsCancelling Bt)
    {nu eta : ℝ} (hnu : 0 < nu) (heta : 0 < eta) {u h : ℝ → ↥(divFree d0)} {T : ℝ}
    (hsol : IsSolutionOn (hodgeOp d0 d1 hdd) (decoupled (compProj d0 d1) Bt) nu eta 0 0 u h
      (Icc 0 T)) :
    ∃ betaPlus : ℝ, 0 < betaPlus ∧
      (∀ t ∈ Icc (0 : ℝ) T, harmProj d0 d1 (u t) = harmProj d0 d1 (u 0)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, harmProj d0 d1 (h t) = harmProj d0 d1 (h 0)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖u t - harmProj d0 d1 (u 0)‖ ^ (2 : ℕ) + ‖h t - harmProj d0 d1 (h 0)‖ ^ (2 : ℕ)
          ≤ (‖u 0 - harmProj d0 d1 (u 0)‖ ^ (2 : ℕ) + ‖h 0 - harmProj d0 d1 (h 0)‖ ^ (2 : ℕ))
            * Real.exp (-(2 * betaPlus) * t) := by
  obtain ⟨lam, hlam, hcoe⟩ := exists_pos_coercive_compProj d0 d1 hdd
  have hconst := harmonic_component_const (Q := harmProj d0 d1)
    (harmProj_compProj d0 d1) (harmProj_hodgeOp d0 d1 hdd) (by simp) (by simp) hsol
  refine ⟨decayRate nu eta lam, decayRate_pos hnu heta hlam, hconst.1, hconst.2, ?_⟩
  exact fibre_converges (compProj_idem d0 d1) (compProj_hodgeOp d0 d1 hdd)
    (harmProj_compProj d0 d1) (harmProj_hodgeOp d0 d1 hdd) (harmProj_add_compProj d0 d1)
    (compProj_symm d0 d1) hBt hcoe hnu heta hlam hsol

end HodgeSystem

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
