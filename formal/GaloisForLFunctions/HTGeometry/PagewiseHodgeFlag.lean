import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The Hodge flag of a law-history page family

A family of bounded operators `d r : K →L C` generates two survivor flags: the kernel flag
`kerFlag`, with `K_{r+1} = K_r ∩ ker d_r`, and the cokernel flag `cokerFlag`, with
`C_{r+1} = C_r ∩ (d_r K_r)^⊥`.  Under the standing hypotheses that each image `d_r K_r` is closed
and lies in `C_r`, the two flags split orthogonally page by page: the positive death layer is
`K_r ∩ K_{r+1}^⊥` and the negative death layer is exactly `d_r K_r = C_r ∩ C_{r+1}^⊥`.

The page differential restricts to a bounded bijection between the two death layers, which
therefore has a positive reduced minimum modulus, and the two flags reconstruct the ambient
spaces as orthogonal sums of death layers and a stable survivor.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

noncomputable section

variable {𝕜 K C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup C] [InnerProductSpace 𝕜 C]

/-- The kernel-side survivor flag: `K_{r+1} = K_r ∩ ker d_r`. -/
def kerFlag (d : ℕ → (K →L[𝕜] C)) : ℕ → Submodule 𝕜 K
  | 0 => ⊤
  | (r + 1) => kerFlag d r ⊓ LinearMap.ker (d r : K →ₗ[𝕜] C)

/-- The negative death layer: the image of the current kernel survivor. -/
def deathImage (d : ℕ → (K →L[𝕜] C)) (r : ℕ) : Submodule 𝕜 C :=
  Submodule.map (d r : K →ₗ[𝕜] C) (kerFlag d r)

/-- The cokernel-side survivor flag: `C_{r+1} = C_r ∩ (d_r K_r)^⊥`. -/
def cokerFlag (d : ℕ → (K →L[𝕜] C)) : ℕ → Submodule 𝕜 C
  | 0 => ⊤
  | (r + 1) => cokerFlag d r ⊓ (deathImage d r)ᗮ

/-- The positive death layer: the part of the current kernel survivor that dies on this page. -/
def deathPos (d : ℕ → (K →L[𝕜] C)) (r : ℕ) : Submodule 𝕜 K :=
  kerFlag d r ⊓ (kerFlag d (r + 1))ᗮ

theorem isClosed_kerFlag (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    IsClosed ((kerFlag d r : Submodule 𝕜 K) : Set K) := by
  induction r with
  | zero => simp [kerFlag]
  | succ r ih =>
    show IsClosed ((kerFlag d r : Set K)
      ∩ ((LinearMap.ker (d r : K →ₗ[𝕜] C) : Submodule 𝕜 K) : Set K))
    exact ih.inter (ContinuousLinearMap.isClosed_ker (d r))

theorem isClosed_cokerFlag (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    IsClosed ((cokerFlag d r : Submodule 𝕜 C) : Set C) := by
  induction r with
  | zero => simp [cokerFlag]
  | succ r ih =>
    show IsClosed ((cokerFlag d r : Set C) ∩ (((deathImage d r)ᗮ : Submodule 𝕜 C) : Set C))
    exact ih.inter (deathImage d r).isClosed_orthogonal

instance instCompleteSpaceKerFlag [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    CompleteSpace (kerFlag d r) :=
  (isClosed_kerFlag d r).completeSpace_coe

instance instCompleteSpaceCokerFlag [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    CompleteSpace (cokerFlag d r) :=
  (isClosed_cokerFlag d r).completeSpace_coe

theorem kerFlag_antitone (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    kerFlag d (r + 1) ≤ kerFlag d r := inf_le_left

theorem cokerFlag_antitone (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    cokerFlag d (r + 1) ≤ cokerFlag d r := inf_le_left

theorem kerFlag_le (d : ℕ → (K →L[𝕜] C)) {r s : ℕ} (h : r ≤ s) :
    kerFlag d s ≤ kerFlag d r := by
  induction s with
  | zero => rw [Nat.le_zero.mp h]
  | succ s ih =>
    rcases Nat.lt_or_ge r (s + 1) with hlt | hge
    · exact (kerFlag_antitone d s).trans (ih (by omega))
    · rw [show r = s + 1 by omega]

theorem deathPos_le_kerFlag (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    deathPos d r ≤ kerFlag d r := inf_le_left

/-- **The kernel flag splits page by page.** -/
theorem deathPos_sup_kerFlag [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    deathPos d r ⊔ kerFlag d (r + 1) = kerFlag d r := by
  rw [deathPos, sup_comm, inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (kerFlag_antitone d r)

/-- The positive death layer is annihilated by the page differential only at zero. -/
theorem eq_zero_of_mem_deathPos_of_apply_eq_zero (d : ℕ → (K →L[𝕜] C)) {r : ℕ} {x : K}
    (hx : x ∈ deathPos d r) (hd : d r x = 0) : x = 0 := by
  have hmem : x ∈ kerFlag d (r + 1) := ⟨hx.1, hd⟩
  have := hx.2 x hmem
  simpa using inner_self_eq_zero.mp this

/-- The page differential maps the positive death layer onto the negative one. -/
theorem map_deathPos [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    Submodule.map (d r : K →ₗ[𝕜] C) (deathPos d r) = deathImage d r := by
  apply le_antisymm
  · exact Submodule.map_mono (deathPos_le_kerFlag d r)
  · rintro y ⟨x, hx, rfl⟩
    rw [← deathPos_sup_kerFlag d r] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨u, hu, ?_⟩
    have hv0 : d r v = 0 := hv.2
    simp only [LinearMap.map_add, ContinuousLinearMap.coe_coe, hv0, add_zero]

/-! ## The cokernel flag under the standing hypotheses -/

theorem cokerFlag_le (d : ℕ → (K →L[𝕜] C)) {r s : ℕ} (h : r ≤ s) :
    cokerFlag d s ≤ cokerFlag d r := by
  induction s with
  | zero => rw [Nat.le_zero.mp h]
  | succ s ih =>
    rcases Nat.lt_or_ge r (s + 1) with hlt | hge
    · exact (cokerFlag_antitone d s).trans (ih (by omega))
    · rw [show r = s + 1 by omega]

theorem cokerFlag_succ_le_orthogonal (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    cokerFlag d (r + 1) ≤ (deathImage d r)ᗮ := inf_le_right

/-- **The cokernel flag splits page by page.** -/
theorem deathImage_sup_cokerFlag [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C))
    (hle : deathImage d r ≤ cokerFlag d r) :
    deathImage d r ⊔ cokerFlag d (r + 1) = cokerFlag d r := by
  haveI : CompleteSpace (deathImage d r) := hcl.completeSpace_coe
  rw [show cokerFlag d (r + 1) = (deathImage d r)ᗮ ⊓ cokerFlag d r from inf_comm _ _]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle

/-- **The negative death layer is the relative complement of the next cokernel survivor.** -/
theorem cokerFlag_inf_orthogonal [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C))
    (hle : deathImage d r ≤ cokerFlag d r) :
    cokerFlag d r ⊓ (cokerFlag d (r + 1))ᗮ = deathImage d r := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp ((deathImage_sup_cokerFlag d r hcl hle) ▸ hx.1)
    have hba : ⟪b, a⟫_𝕜 = 0 := inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ b).mp
      (cokerFlag_succ_le_orthogonal d r hb) a ha)
    have hbx : ⟪b, a + b⟫_𝕜 = 0 := hx.2 b hb
    have : ⟪b, b⟫_𝕜 = 0 := by
      rw [inner_add_right, hba, zero_add] at hbx
      exact hbx
    rw [inner_self_eq_zero.mp this, add_zero]
    exact ha
  · refine le_inf hle ?_
    intro y hy
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact inner_eq_zero_symm.mp
      ((Submodule.mem_orthogonal _ z).mp (cokerFlag_succ_le_orthogonal d r hz) y hy)

/-! ## Orthogonality of the death layers -/

theorem inner_deathPos_eq_zero (d : ℕ → (K →L[𝕜] C)) {r s : ℕ} (hrs : r < s)
    {x y : K} (hx : x ∈ deathPos d r) (hy : y ∈ deathPos d s) : ⟪y, x⟫_𝕜 = 0 :=
  (Submodule.mem_orthogonal _ x).mp hx.2 y (kerFlag_le d hrs (deathPos_le_kerFlag d s hy))

theorem inner_deathPos_kerFlag_eq_zero (d : ℕ → (K →L[𝕜] C)) {r m : ℕ} (hrm : r < m)
    {x y : K} (hx : x ∈ deathPos d r) (hy : y ∈ kerFlag d m) : ⟪y, x⟫_𝕜 = 0 :=
  (Submodule.mem_orthogonal _ x).mp hx.2 y (kerFlag_le d hrm hy)

theorem inner_deathImage_eq_zero (d : ℕ → (K →L[𝕜] C)) {r s : ℕ} (hrs : r < s)
    (hle : ∀ t, deathImage d t ≤ cokerFlag d t)
    {x y : C} (hx : x ∈ deathImage d r) (hy : y ∈ deathImage d s) : ⟪y, x⟫_𝕜 = 0 := by
  have hy' : y ∈ cokerFlag d (r + 1) := cokerFlag_le d hrs (hle s hy)
  exact inner_eq_zero_symm.mp
    ((Submodule.mem_orthogonal _ y).mp (cokerFlag_succ_le_orthogonal d r hy') x hx)

theorem inner_deathImage_cokerFlag_eq_zero (d : ℕ → (K →L[𝕜] C)) {r m : ℕ} (hrm : r < m)
    {x y : C} (hx : x ∈ deathImage d r) (hy : y ∈ cokerFlag d m) : ⟪x, y⟫_𝕜 = 0 :=
  (Submodule.mem_orthogonal _ y).mp
    (cokerFlag_succ_le_orthogonal d r (cokerFlag_le d hrm hy)) x hx

/-! ## Orthogonal reconstruction -/

/-- **Kernel-side reconstruction (PHF.9).** -/
theorem sup_deathPos_sup_kerFlag [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (m : ℕ) :
    (Finset.range m).sup (deathPos d) ⊔ kerFlag d m = ⊤ := by
  induction m with
  | zero => simp [kerFlag]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm (deathPos d m), sup_assoc,
      deathPos_sup_kerFlag d m, ih]

/-- **Cokernel-side reconstruction (PHF.9).** -/
theorem sup_deathImage_sup_cokerFlag [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C))
    (hle : ∀ r, deathImage d r ≤ cokerFlag d r) :
    (Finset.range m).sup (deathImage d) ⊔ cokerFlag d m = ⊤ := by
  induction m with
  | zero => simp [cokerFlag]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm (deathImage d m), sup_assoc,
      deathImage_sup_cokerFlag d m (hcl m) (hle m), ih]

/-! ## The page bijection and its reduced minimum modulus -/

theorem isClosed_deathPos (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    IsClosed ((deathPos d r : Submodule 𝕜 K) : Set K) := by
  show IsClosed ((kerFlag d r : Set K) ∩ (((kerFlag d (r + 1))ᗮ : Submodule 𝕜 K) : Set K))
  exact (isClosed_kerFlag d r).inter (kerFlag d (r + 1)).isClosed_orthogonal

instance instCompleteSpaceDeathPos [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    CompleteSpace (deathPos d r) :=
  (isClosed_deathPos d r).completeSpace_coe

/-- The page differential restricted to its positive death layer. -/
def deathMap [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) : deathPos d r →L[𝕜] deathImage d r :=
  ContinuousLinearMap.codRestrict ((d r).comp (deathPos d r).subtypeL) (deathImage d r)
    (fun x => by
      rw [← map_deathPos]
      exact ⟨x.1, x.2, rfl⟩)

@[simp] theorem deathMap_coe [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) (x : deathPos d r) :
    ((deathMap d r x : deathImage d r) : C) = d r (x : K) := rfl

theorem deathMap_injective [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    Function.Injective (deathMap d r) := by
  intro x y hxy
  refine Subtype.ext ?_
  have h0 : d r ((x : K) - (y : K)) = 0 := by
    rw [map_sub]
    have := congrArg (fun z : deathImage d r => (z : C)) hxy
    simp only [deathMap_coe] at this
    rw [this, sub_self]
  have hmem : (x : K) - (y : K) ∈ deathPos d r := Submodule.sub_mem _ x.2 y.2
  exact sub_eq_zero.mp (eq_zero_of_mem_deathPos_of_apply_eq_zero d hmem h0)

theorem deathMap_surjective [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    Function.Surjective (deathMap d r) := by
  intro y
  obtain ⟨x, hx, hxy⟩ : (y : C) ∈ Submodule.map (d r : K →ₗ[𝕜] C) (deathPos d r) := by
    rw [map_deathPos]
    exact y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- **Positive reduced minimum modulus (PHF.8).**  The page differential is bounded below on its
positive death layer. -/
theorem exists_pos_deathGap [CompleteSpace K] [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ deathPos d r, γ * ‖x‖ ≤ ‖d r x‖ := by
  haveI : CompleteSpace (deathImage d r) := hcl.completeSpace_coe
  have hker : LinearMap.ker (deathMap d r : deathPos d r →ₗ[𝕜] deathImage d r) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (deathMap_injective d r)
  have hran : LinearMap.range (deathMap d r : deathPos d r →ₗ[𝕜] deathImage d r) = ⊤ :=
    LinearMap.range_eq_top.mpr (deathMap_surjective d r)
  set e := ContinuousLinearEquiv.ofBijective (deathMap d r) hker hran with he
  refine ⟨(‖(e.symm : deathImage d r →L[𝕜] deathPos d r)‖ + 1)⁻¹, by positivity, ?_⟩
  intro x hx
  set N := ‖(e.symm : deathImage d r →L[𝕜] deathPos d r)‖ with hN
  have hNnn : (0 : ℝ) ≤ N := norm_nonneg _
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have hsymm : ‖(⟨x, hx⟩ : deathPos d r)‖ ≤ N * ‖deathMap d r ⟨x, hx⟩‖ := by
    conv_lhs => rw [show (⟨x, hx⟩ : deathPos d r) = e.symm (e ⟨x, hx⟩) from (e.symm_apply_apply _).symm]
    exact (e.symm : deathImage d r →L[𝕜] deathPos d r).le_opNorm _
  have hxn : ‖(⟨x, hx⟩ : deathPos d r)‖ = ‖x‖ := rfl
  have hdn : ‖deathMap d r ⟨x, hx⟩‖ = ‖d r x‖ := rfl
  rw [hxn, hdn] at hsymm
  rw [inv_mul_le_iff₀ hpos]
  nlinarith [norm_nonneg (d r x), norm_nonneg x]

/-! ## Page pairing (PHF.12) -/

/-- The positive death layer realizes the page quotient of the kernel flag. -/
def deathPosEquivKerQuot [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (r : ℕ) :
    deathPos d r ≃ₗ[𝕜]
      (kerFlag d r ⧸ Submodule.comap (kerFlag d r).subtype (kerFlag d (r + 1))) := by
  refine LinearEquiv.ofBijective
    ((Submodule.comap (kerFlag d r).subtype (kerFlag d (r + 1))).mkQ.comp
      (Submodule.inclusion (deathPos_le_kerFlag d r))) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : (Submodule.comap (kerFlag d r).subtype (kerFlag d (r + 1))).mkQ
        (Submodule.inclusion (deathPos_le_kerFlag d r) x) = 0 := LinearMap.mem_ker.mp hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    have hx1 : (x : K) ∈ kerFlag d (r + 1) := h0
    exact Subtype.ext (eq_zero_of_mem_deathPos_of_apply_eq_zero d x.2
      (LinearMap.mem_ker.mp hx1.2))
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    have hy : (y : K) ∈ deathPos d r ⊔ kerFlag d (r + 1) := by
      rw [deathPos_sup_kerFlag d r]
      exact y.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨a, ha⟩, ?_⟩
    show (Submodule.comap (kerFlag d r).subtype (kerFlag d (r + 1))).mkQ
        ⟨a, deathPos_le_kerFlag d r ha⟩ = Submodule.Quotient.mk y
    rw [Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    show a - (y : K) ∈ kerFlag d (r + 1)
    have hsub : a - (y : K) = -b := by
      rw [← hab]
      abel
    rw [hsub]
    exact Submodule.neg_mem _ hb

/-- The negative death layer realizes the page quotient of the cokernel flag. -/
def deathImageEquivCokerQuot [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C))
    (hle : deathImage d r ≤ cokerFlag d r) :
    deathImage d r ≃ₗ[𝕜]
      (cokerFlag d r ⧸ Submodule.comap (cokerFlag d r).subtype (cokerFlag d (r + 1))) := by
  refine LinearEquiv.ofBijective
    ((Submodule.comap (cokerFlag d r).subtype (cokerFlag d (r + 1))).mkQ.comp
      (Submodule.inclusion hle)) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : (Submodule.comap (cokerFlag d r).subtype (cokerFlag d (r + 1))).mkQ
        (Submodule.inclusion hle x) = 0 := LinearMap.mem_ker.mp hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    have hx1 : (x : C) ∈ cokerFlag d (r + 1) := h0
    have hxx : ⟪(x : C), (x : C)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ (x : C)).mp (cokerFlag_succ_le_orthogonal d r hx1) (x : C) x.2
    exact Subtype.ext (inner_self_eq_zero.mp hxx)
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    have hy : (y : C) ∈ deathImage d r ⊔ cokerFlag d (r + 1) := by
      rw [deathImage_sup_cokerFlag d r hcl hle]
      exact y.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨a, ha⟩, ?_⟩
    show (Submodule.comap (cokerFlag d r).subtype (cokerFlag d (r + 1))).mkQ
        ⟨a, hle ha⟩ = Submodule.Quotient.mk y
    rw [Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    show a - (y : C) ∈ cokerFlag d (r + 1)
    have hsub : a - (y : C) = -b := by
      rw [← hab]
      abel
    rw [hsub]
    exact Submodule.neg_mem _ hb

/-- **The page bijection.**  The page differential is a topological isomorphism from the positive
death layer onto the negative one. -/
def deathEquiv [CompleteSpace K] [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (r : ℕ)
    (hcl : IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C)) :
    deathPos d r ≃L[𝕜] deathImage d r :=
  haveI : CompleteSpace (deathImage d r) := hcl.completeSpace_coe
  ContinuousLinearEquiv.ofBijective (deathMap d r)
    (LinearMap.ker_eq_bot.mpr (deathMap_injective d r))
    (LinearMap.range_eq_top.mpr (deathMap_surjective d r))

/-! ## Orthogonal conservation (PHF.11) -/

theorem exists_death_decomposition [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (m : ℕ) (x : K) :
    ∃ (f : ℕ → K) (z : K), (∀ r, r < m → f r ∈ deathPos d r) ∧ z ∈ kerFlag d m
      ∧ x = (∑ r ∈ Finset.range m, f r) + z := by
  induction m with
  | zero => exact ⟨fun _ => 0, x, fun r hr => absurd hr (Nat.not_lt_zero r), trivial, by simp⟩
  | succ m ih =>
    obtain ⟨f, z, hf, hz, hx⟩ := ih
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((deathPos_sup_kerFlag d m) ▸ hz)
    refine ⟨Function.update f m a, b, ?_, hb, ?_⟩
    · intro r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · rw [Function.update_of_ne (by omega)]
        exact hf r hlt
      · subst heq
        rw [Function.update_self]
        exact ha
    · have hsum : ∑ r ∈ Finset.range m, Function.update f m a r
          = ∑ r ∈ Finset.range m, f r :=
        Finset.sum_congr rfl fun r hr =>
          Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hr)) _ _
      rw [Finset.sum_range_succ, Function.update_self, hsum, hx, ← hab]
      abel

theorem norm_sq_death_decomposition [CompleteSpace K] (d : ℕ → (K →L[𝕜] C)) (m : ℕ) :
    ∀ (f : ℕ → K) (z : K), (∀ r, r < m → f r ∈ deathPos d r) → z ∈ kerFlag d m →
      ‖(∑ r ∈ Finset.range m, f r) + z‖ * ‖(∑ r ∈ Finset.range m, f r) + z‖
        = (∑ r ∈ Finset.range m, ‖f r‖ * ‖f r‖) + ‖z‖ * ‖z‖ := by
  induction m with
  | zero => intro f z _ _; simp
  | succ m ih =>
    intro f z hf hz
    have hfm : f m ∈ deathPos d m := hf m (by omega)
    have hzm : z ∈ kerFlag d (m + 1) := hz
    have horth : ⟪f m, z⟫_𝕜 = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ (f m)).mp hfm.2 z hzm)
    have hsplit : ‖f m + z‖ * ‖f m + z‖ = ‖f m‖ * ‖f m‖ + ‖z‖ * ‖z‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f m) z horth
    have hzin : f m + z ∈ kerFlag d m :=
      Submodule.add_mem _ (deathPos_le_kerFlag d m hfm) (kerFlag_antitone d m hzm)
    have hrw : (∑ r ∈ Finset.range (m + 1), f r) + z
        = (∑ r ∈ Finset.range m, f r) + (f m + z) := by
      rw [Finset.sum_range_succ]
      abel
    rw [hrw, ih f (f m + z) (fun r hr => hf r (by omega)) hzin, hsplit,
      Finset.sum_range_succ]
    ring

theorem exists_deathImage_decomposition [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (m : ℕ)
    (hcl : ∀ r, IsClosed ((deathImage d r : Submodule 𝕜 C) : Set C))
    (hle : ∀ r, deathImage d r ≤ cokerFlag d r) (x : C) :
    ∃ (f : ℕ → C) (z : C), (∀ r, r < m → f r ∈ deathImage d r) ∧ z ∈ cokerFlag d m
      ∧ x = (∑ r ∈ Finset.range m, f r) + z := by
  induction m with
  | zero => exact ⟨fun _ => 0, x, fun r hr => absurd hr (Nat.not_lt_zero r), trivial, by simp⟩
  | succ m ih =>
    obtain ⟨f, z, hf, hz, hx⟩ := ih
    have hzs : z ∈ deathImage d m ⊔ cokerFlag d (m + 1) := by
      rw [deathImage_sup_cokerFlag d m (hcl m) (hle m)]
      exact hz
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzs
    refine ⟨Function.update f m a, b, ?_, hb, ?_⟩
    · intro r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · rw [Function.update_of_ne (by omega)]
        exact hf r hlt
      · subst heq
        rw [Function.update_self]
        exact ha
    · have hsum : ∑ r ∈ Finset.range m, Function.update f m a r
          = ∑ r ∈ Finset.range m, f r :=
        Finset.sum_congr rfl fun r hr =>
          Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hr)) _ _
      rw [Finset.sum_range_succ, Function.update_self, hsum, hx, ← hab]
      abel

theorem norm_sq_deathImage_decomposition [CompleteSpace C] (d : ℕ → (K →L[𝕜] C)) (m : ℕ)
    (hle : ∀ r, deathImage d r ≤ cokerFlag d r) :
    ∀ (f : ℕ → C) (z : C), (∀ r, r < m → f r ∈ deathImage d r) → z ∈ cokerFlag d m →
      ‖(∑ r ∈ Finset.range m, f r) + z‖ * ‖(∑ r ∈ Finset.range m, f r) + z‖
        = (∑ r ∈ Finset.range m, ‖f r‖ * ‖f r‖) + ‖z‖ * ‖z‖ := by
  induction m with
  | zero => intro f z _ _; simp
  | succ m ih =>
    intro f z hf hz
    have hfm : f m ∈ deathImage d m := hf m (by omega)
    have horth : ⟪f m, z⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ z).mp (cokerFlag_succ_le_orthogonal d m hz) (f m) hfm
    have hsplit : ‖f m + z‖ * ‖f m + z‖ = ‖f m‖ * ‖f m‖ + ‖z‖ * ‖z‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f m) z horth
    have hzin : f m + z ∈ cokerFlag d m :=
      Submodule.add_mem _ (hle m hfm) (cokerFlag_antitone d m hz)
    have hrw : (∑ r ∈ Finset.range (m + 1), f r) + z
        = (∑ r ∈ Finset.range m, f r) + (f m + z) := by
      rw [Finset.sum_range_succ]
      abel
    rw [hrw, ih f (f m + z) (fun r hr => hf r (by omega)) hzin, hsplit, Finset.sum_range_succ]
    ring

end

end GaloisForLFunctions.HTGeometry
