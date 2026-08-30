import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Split-recovery formation capital

The least Hilbert--Schmidt energy needed to factor a defect `X : U → H` through a source
formation `W : K → H`.  Post-recovery capital never increases, injective (in particular split)
recovery preserves it exactly, and every strict improvement is the erasure of a nonzero
formation residual by the recovery kernel.

The minimizing factor is produced explicitly as `(ker W)ᗮ.starProjection ∘L B₀` for any
factorization `B₀`; no completeness of the Hilbert--Schmidt operator space is used.
-/

open scoped BigOperators ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap

variable {𝕜 K H H' H'' U : Type*} [RCLike 𝕜]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] [CompleteSpace H']
  [NormedAddCommGroup H''] [InnerProductSpace 𝕜 H''] [CompleteSpace H'']
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]

/-! ## Abstract formation capital -/

/-- `(RCN.3)`  The Hilbert--Schmidt factorizations of a defect `X` through a source `W`. -/
def formationFactorizations (W : K →L[𝕜] H) (X : U →L[𝕜] H) : Set (U →L[𝕜] K) :=
  {B | IsHilbertSchmidt B ∧ W ∘L B = X}

/-- `(RCN.3)`  The extended formation capital, `+∞` when no factorization exists. -/
def formationCapital (W : K →L[𝕜] H) (X : U →L[𝕜] H) : ℝ≥0∞ :=
  ⨅ B ∈ formationFactorizations W X, ENNReal.ofReal (hsNormSq B)

omit [CompleteSpace K] [CompleteSpace H] in
theorem formationCapital_le_of_mem {W : K →L[𝕜] H} {X : U →L[𝕜] H} {B : U →L[𝕜] K}
    (hB : B ∈ formationFactorizations W X) :
    formationCapital W X ≤ ENNReal.ofReal (hsNormSq B) :=
  iInf₂_le _ hB

omit [CompleteSpace H] in
omit [CompleteSpace K] [CompleteSpace H'] in
theorem formationCapital_mono {W : K →L[𝕜] H} {X : U →L[𝕜] H} {W' : K →L[𝕜] H'}
    {X' : U →L[𝕜] H'} (h : formationFactorizations W X ⊆ formationFactorizations W' X') :
    formationCapital W' X' ≤ formationCapital W X :=
  le_iInf₂ fun _ hB => formationCapital_le_of_mem (h hB)

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
theorem formationCapital_congr {W : K →L[𝕜] H} {X : U →L[𝕜] H} {W' : K →L[𝕜] H'}
    {X' : U →L[𝕜] H'} (h : formationFactorizations W X = formationFactorizations W' X') :
    formationCapital W X = formationCapital W' X' :=
  le_antisymm (formationCapital_mono h.ge) (formationCapital_mono h.le)

omit [CompleteSpace K] [CompleteSpace H] in
theorem formationCapital_eq_top_iff {W : K →L[𝕜] H} {X : U →L[𝕜] H} :
    formationCapital W X = ⊤ ↔ formationFactorizations W X = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨B, hB⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hle := formationCapital_le_of_mem hB
    rw [h, top_le_iff] at hle
    exact ENNReal.ofReal_ne_top hle
  · intro h
    simp [formationCapital, h]

/-! ## The minimizing factor -/

/-- The kernel of a bounded operator is orthogonally complemented. -/
instance hasOrthogonalProjection_ker (W : K →L[𝕜] H) :
    (LinearMap.ker (W : K →ₗ[𝕜] H)).HasOrthogonalProjection := by
  haveI : CompleteSpace ((LinearMap.ker (W : K →ₗ[𝕜] H)) : Submodule 𝕜 K) :=
    W.isClosed_ker.completeSpace_coe
  infer_instance

/-- The orthogonal projection onto the coimage `(ker W)ᗮ`. -/
def coimageProjection (W : K →L[𝕜] H) : K →L[𝕜] K :=
  (LinearMap.ker (W : K →ₗ[𝕜] H))ᗮ.starProjection

omit [CompleteSpace H] in
theorem coimageProjection_mem (W : K →L[𝕜] H) (k : K) :
    coimageProjection W k ∈ (LinearMap.ker (W : K →ₗ[𝕜] H))ᗮ :=
  Submodule.starProjection_apply_mem _ k

omit [CompleteSpace H] in
theorem norm_coimageProjection_le (W : K →L[𝕜] H) (k : K) :
    ‖coimageProjection W k‖ ≤ ‖k‖ :=
  Submodule.norm_starProjection_apply_le _ k

omit [CompleteSpace H] in
/-- For an injective source the coimage projection is the identity. -/
theorem coimageProjection_eq_self_of_injective {W : K →L[𝕜] H} (hW : Function.Injective W) (k : K) :
    coimageProjection W k = k := by
  refine Submodule.starProjection_eq_self_iff.mpr ?_
  rw [Submodule.mem_orthogonal']
  intro u hu
  have hu0 : u = 0 := hW (by simpa using LinearMap.mem_ker.mp hu)
  simp [hu0]

omit [CompleteSpace H] in
/-- Composing with the coimage projection does not change the image. -/
theorem comp_coimageProjection (W : K →L[𝕜] H) (k : K) :
    W (coimageProjection W k) = W k := by
  have h0 : k - coimageProjection W k ∈ (LinearMap.ker (W : K →ₗ[𝕜] H))ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  rw [Submodule.orthogonal_orthogonal] at h0
  have := LinearMap.mem_ker.mp h0
  simp only [ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at this
  exact this.symm

/-! ## The minimizing factor -/

/-- The corrected factor: any factorization projected onto the coimage of the source. -/
def minimalFactor (W : K →L[𝕜] H) (B : U →L[𝕜] K) : U →L[𝕜] K :=
  coimageProjection W ∘L B

omit [CompleteSpace H] in
theorem minimalFactor_mem {W : K →L[𝕜] H} {X : U →L[𝕜] H} {B : U →L[𝕜] K}
    (hB : B ∈ formationFactorizations W X) :
    minimalFactor W B ∈ formationFactorizations W X := by
  refine ⟨hB.1.comp_left _, ?_⟩
  refine ContinuousLinearMap.ext fun u => ?_
  have h1 : W (coimageProjection W (B u)) = W (B u) := comp_coimageProjection W (B u)
  have h2 : (W ∘L B) u = X u := by rw [hB.2]
  simpa [minimalFactor] using h1.trans h2

omit [CompleteSpace H] in
/-- The corrected factor is Hilbert--Schmidt-orthogonal to every null factor. -/
theorem hsInner_minimalFactor_eq_zero {W : K →L[𝕜] H} {B C : U →L[𝕜] K}
    (hC : W ∘L C = 0) : hsInner (minimalFactor W B) C = 0 := by
  have hz : ∀ i, inner 𝕜 (minimalFactor W B (hsBasis 𝕜 U i)) (C (hsBasis 𝕜 U i)) = 0 := by
    intro i
    have hker : C (hsBasis 𝕜 U i) ∈ LinearMap.ker (W : K →ₗ[𝕜] H) := by
      have : (W ∘L C) (hsBasis 𝕜 U i) = 0 := by rw [hC]; rfl
      simpa [LinearMap.mem_ker] using this
    exact (Submodule.mem_orthogonal' _ _).mp (coimageProjection_mem W _) _ hker
  rw [hsInner]
  simp only [hz]
  exact tsum_zero

omit [CompleteSpace H] in
/-- **§2, attainment.**  Whenever a factorization exists, the corrected factor realizes the
formation capital. -/
theorem formationCapital_eq_of_mem {W : K →L[𝕜] H} {X : U →L[𝕜] H} {B : U →L[𝕜] K}
    (hB : B ∈ formationFactorizations W X) :
    formationCapital W X = ENNReal.ofReal (hsNormSq (minimalFactor W B)) := by
  refine le_antisymm (formationCapital_le_of_mem (minimalFactor_mem hB)) ?_
  refine le_iInf₂ fun B' hB' => ?_
  have hM := minimalFactor_mem hB
  have hdiff : W ∘L (B' - minimalFactor W B) = 0 := by
    rw [ContinuousLinearMap.comp_sub, hB'.2, hM.2, sub_self]
  have hHS : IsHilbertSchmidt (B' - minimalFactor W B) := hB'.1.sub hM.1
  have horth := hsInner_minimalFactor_eq_zero (B := B) (C := B' - minimalFactor W B) hdiff
  have hpyth := hsNormSq_add_eq_of_hsInner_eq_zero hM.1 hHS horth
  rw [show minimalFactor W B + (B' - minimalFactor W B) = B' by abel] at hpyth
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hpyth]
  linarith [hsNormSq_nonneg (B' - minimalFactor W B)]

theorem hsInner_sub_left {S₁ S₂ T : U →L[𝕜] K} (h₁ : IsHilbertSchmidt S₁)
    (h₂ : IsHilbertSchmidt S₂) (hT : IsHilbertSchmidt T) :
    hsInner (S₁ - S₂) T = hsInner S₁ T - hsInner S₂ T := by
  have hneg : hsInner (-S₂) T = -hsInner S₂ T := by
    have h := hsInner_smul_left (-1 : 𝕜) S₂ T
    rw [neg_one_smul] at h
    rw [h]
    simp
  rw [sub_eq_add_neg, hsInner_add_left h₁ h₂.neg hT, hneg, sub_eq_add_neg]

omit [CompleteSpace H] in
/-- **§2, uniqueness.**  Two factorizations orthogonal to every null factor coincide. -/
theorem minimalFactor_unique {W : K →L[𝕜] H} {X : U →L[𝕜] H} {B₁ B₂ : U →L[𝕜] K}
    (h₁ : B₁ ∈ formationFactorizations W X) (h₂ : B₂ ∈ formationFactorizations W X)
    (o₁ : ∀ C : U →L[𝕜] K, W ∘L C = 0 → hsInner B₁ C = 0)
    (o₂ : ∀ C : U →L[𝕜] K, W ∘L C = 0 → hsInner B₂ C = 0) :
    B₁ = B₂ := by
  have hdiff : W ∘L (B₁ - B₂) = 0 := by
    rw [ContinuousLinearMap.comp_sub, h₁.2, h₂.2, sub_self]
  have hHS : IsHilbertSchmidt (B₁ - B₂) := h₁.1.sub h₂.1
  have hzero : hsInner (B₁ - B₂) (B₁ - B₂) = 0 := by
    rw [hsInner_sub_left h₁.1 h₂.1 hHS, o₁ _ hdiff, o₂ _ hdiff, sub_zero]
  have : hsNormSq (B₁ - B₂) = 0 := by
    rw [← hsInner_self_re hHS, hzero, map_zero]
  exact sub_eq_zero.mp ((hsNormSq_eq_zero_iff hHS).mp this)

/-! ## Theorem 3.1: recovery monotonicity and the exact kernel formula -/

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- `(RCN.11)`  After recovery the factorization constraint is exactness modulo `ker R`. -/
theorem formationFactorizations_comp (W : K →L[𝕜] H) (X : U →L[𝕜] H) (R : H →L[𝕜] H') :
    formationFactorizations (R ∘L W) (R ∘L X)
      = {B : U →L[𝕜] K | IsHilbertSchmidt B ∧ R ∘L (W ∘L B - X) = 0} := by
  ext B
  simp only [formationFactorizations, Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [ContinuousLinearMap.comp_sub, sub_eq_zero, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- Every exact factorization is admissible after recovery. -/
theorem formationFactorizations_subset_comp (W : K →L[𝕜] H) (X : U →L[𝕜] H) (R : H →L[𝕜] H') :
    formationFactorizations W X ⊆ formationFactorizations (R ∘L W) (R ∘L X) := by
  rintro B ⟨hHS, hB⟩
  exact ⟨hHS, by rw [ContinuousLinearMap.comp_assoc, hB]⟩

omit [CompleteSpace H] in
omit [CompleteSpace K] [CompleteSpace H'] in
/-- **Theorem 3.1, `(RCN.5)`.**  Post-recovery formation capital never increases. -/
theorem formationCapital_comp_le (W : K →L[𝕜] H) (X : U →L[𝕜] H) (R : H →L[𝕜] H') :
    formationCapital (R ∘L W) (R ∘L X) ≤ formationCapital W X :=
  formationCapital_mono (formationFactorizations_subset_comp W X R)

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- **Theorem 3.1 I, `(RCN.6)`.**  An injective recovery leaves the factorization set itself
unchanged. -/
theorem formationFactorizations_comp_of_injective (W : K →L[𝕜] H) (X : U →L[𝕜] H)
    {R : H →L[𝕜] H'} (hR : Function.Injective R) :
    formationFactorizations (R ∘L W) (R ∘L X) = formationFactorizations W X := by
  ext B
  refine ⟨fun hB => ⟨hB.1, ?_⟩, fun hB => formationFactorizations_subset_comp W X R hB⟩
  refine ContinuousLinearMap.ext fun u => hR ?_
  have := congrFun (congrArg (fun (T : U →L[𝕜] H') => (T : U → H')) hB.2) u
  simpa using this

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- **Theorem 3.1 I, `(RCN.6)`.**  Injective recovery is capital-neutral. -/
theorem formationCapital_comp_of_injective (W : K →L[𝕜] H) (X : U →L[𝕜] H)
    {R : H →L[𝕜] H'} (hR : Function.Injective R) :
    formationCapital (R ∘L W) (R ∘L X) = formationCapital W X :=
  formationCapital_congr (formationFactorizations_comp_of_injective W X hR)

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- **Theorem 3.1 II, `(RCN.7)`.**  A split recovery is capital-neutral. -/
theorem formationCapital_comp_of_leftInverse (W : K →L[𝕜] H) (X : U →L[𝕜] H)
    {R : H →L[𝕜] H'} {Q : H' →L[𝕜] H} (hQR : Q ∘L R = ContinuousLinearMap.id 𝕜 H) :
    formationCapital (R ∘L W) (R ∘L X) = formationCapital W X := by
  refine formationCapital_comp_of_injective W X (fun x y hxy => ?_)
  have hx : Q (R x) = x := by rw [← ContinuousLinearMap.comp_apply, hQR]; rfl
  have hy : Q (R y) = y := by rw [← ContinuousLinearMap.comp_apply, hQR]; rfl
  rw [← hx, ← hy, hxy]

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- **Theorem 3.1 III, `(RCN.8)`, `(RCN.9)`.**  Every strict capital improvement erases a nonzero
formation residual through the recovery kernel. -/
theorem kernelErasure_of_formationCapital_lt (W : K →L[𝕜] H) (X : U →L[𝕜] H) {R : H →L[𝕜] H'}
    (hlt : formationCapital (R ∘L W) (R ∘L X) < formationCapital W X) :
    ¬ Function.Injective R
      ∧ ∃ B ∈ formationFactorizations (R ∘L W) (R ∘L X),
          W ∘L B - X ≠ 0 ∧ ENNReal.ofReal (hsNormSq B) < formationCapital W X := by
  refine ⟨fun hR => absurd (formationCapital_comp_of_injective W X hR) hlt.ne, ?_⟩
  rw [formationCapital, iInf_lt_iff] at hlt
  obtain ⟨B, hB⟩ := hlt
  rw [iInf_lt_iff] at hB
  obtain ⟨hmemB, hlt'⟩ := hB
  refine ⟨B, hmemB, ?_, hlt'⟩
  intro hres
  have hmem : B ∈ formationFactorizations W X := ⟨hmemB.1, by rwa [sub_eq_zero] at hres⟩
  exact absurd (formationCapital_le_of_mem hmem) (not_le.mpr hlt')

omit [CompleteSpace H] in
omit [CompleteSpace K] [CompleteSpace H'] [CompleteSpace H''] in
/-- **Theorem 3.1 IV, `(RCN.10)`.**  Serial recovery obeys a data-processing chain. -/
theorem formationCapital_serial_le (W : K →L[𝕜] H) (X : U →L[𝕜] H) (R₁ : H →L[𝕜] H')
    (R₂ : H' →L[𝕜] H'') :
    formationCapital (R₂ ∘L R₁ ∘L W) (R₂ ∘L R₁ ∘L X) ≤ formationCapital (R₁ ∘L W) (R₁ ∘L X)
      ∧ formationCapital (R₁ ∘L W) (R₁ ∘L X) ≤ formationCapital W X :=
  ⟨formationCapital_comp_le _ _ R₂, formationCapital_comp_le W X R₁⟩

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] [CompleteSpace H''] in
/-- **Theorem 3.1 IV, equality case.**  Two injective recoveries compose to a capital isometry. -/
theorem formationCapital_serial_of_injective (W : K →L[𝕜] H) (X : U →L[𝕜] H) {R₁ : H →L[𝕜] H'}
    {R₂ : H' →L[𝕜] H''} (h₁ : Function.Injective R₁) (h₂ : Function.Injective R₂) :
    formationCapital (R₂ ∘L R₁ ∘L W) (R₂ ∘L R₁ ∘L X) = formationCapital W X := by
  rw [formationCapital_comp_of_injective _ _ h₂, formationCapital_comp_of_injective W X h₁]

/-! ## Functional-equation capital isometry -/

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- `(RCN.13)`  A bounded linear isomorphism of the carrier is a formation-capital isometry. -/
theorem formationCapital_equivTransport (W : K →L[𝕜] H) (X : U →L[𝕜] H) (A : H ≃L[𝕜] H') :
    formationCapital ((A : H →L[𝕜] H') ∘L W) ((A : H →L[𝕜] H') ∘L X) = formationCapital W X :=
  formationCapital_comp_of_injective W X A.injective

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] [CompleteSpace H''] in
/-- `(RCN.15)`  The functional equation lifts through every common split recovery kernel as a
formation-capital isometry. -/
theorem formationCapital_fe_split (W : K →L[𝕜] H) (X : U →L[𝕜] H) (A : H ≃L[𝕜] H')
    {E : H' →L[𝕜] H''} {Q : H'' →L[𝕜] H'} (hQE : Q ∘L E = ContinuousLinearMap.id 𝕜 H') :
    formationCapital (E ∘L (A : H →L[𝕜] H') ∘L W) (E ∘L (A : H →L[𝕜] H') ∘L X)
      = formationCapital W X := by
  rw [formationCapital_comp_of_leftInverse _ _ hQE, formationCapital_equivTransport]

/-! ## The recovered Gramian -/

/-- `(RCN.18)`  The Gramian of the recovered source formation. -/
def recoveredGramian (W : K →L[𝕜] H) (R : H →L[𝕜] H') : H' →L[𝕜] H' :=
  R ∘L (W ∘L ContinuousLinearMap.adjoint W) ∘L ContinuousLinearMap.adjoint R

theorem inner_recoveredGramian (W : K →L[𝕜] H) (R : H →L[𝕜] H') (y : H') :
    inner 𝕜 y (recoveredGramian W R y)
      = inner 𝕜 (ContinuousLinearMap.adjoint W (ContinuousLinearMap.adjoint R y))
          (ContinuousLinearMap.adjoint W (ContinuousLinearMap.adjoint R y)) := by
  simp only [recoveredGramian, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left]

/-- `(RCN.18)`  On the closed recovered carrier the recovered Gramian is injective whenever the
source Gramian is. -/
theorem eq_zero_of_inner_recoveredGramian_eq_zero (W : K →L[𝕜] H) (R : H →L[𝕜] H')
    (hG : Function.Injective (W ∘L ContinuousLinearMap.adjoint W)) {y : H'}
    (hy : y ∈ closure (Set.range R)) (h0 : inner 𝕜 y (recoveredGramian W R y) = (0 : 𝕜)) :
    y = 0 := by
  have hWadj : ContinuousLinearMap.adjoint W (ContinuousLinearMap.adjoint R y) = 0 :=
    inner_self_eq_zero.mp ((inner_recoveredGramian W R y).symm.trans h0)
  have hRadj : ContinuousLinearMap.adjoint R y = 0 := by
    refine hG ?_
    simp [ContinuousLinearMap.comp_apply, hWadj]
  have hperp : ∀ x : H, inner 𝕜 y (R x) = (0 : 𝕜) := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_left, hRadj, inner_zero_left]
  have hclosed : IsClosed {z : H' | inner 𝕜 y z = (0 : 𝕜)} :=
    isClosed_eq (by fun_prop) continuous_const
  have hsub : closure (Set.range R) ⊆ {z : H' | inner 𝕜 y z = (0 : 𝕜)} :=
    hclosed.closure_subset_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hperp x)
  exact inner_self_eq_zero.mp (hsub hy)

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] in
/-- `(RCN.19)`  A common injective recovery preserves the least source work exactly. -/
theorem formationCapital_recovered (W : K →L[𝕜] H) (X : U →L[𝕜] H) {R : H →L[𝕜] H'}
    (hR : Function.Injective R) :
    formationCapital (R ∘L W) (R ∘L X) = formationCapital W X :=
  formationCapital_comp_of_injective W X hR

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] [CompleteSpace H''] in
/-- `(RCN.19a)`  Infinite capital is preserved: common recovery can move the atomic-refinement
wall but cannot regularize it. -/
theorem formationCapital_eq_top_fe_split_iff (W : K →L[𝕜] H) (X : U →L[𝕜] H) (A : H ≃L[𝕜] H')
    {E : H' →L[𝕜] H''} {Q : H'' →L[𝕜] H'} (hQE : Q ∘L E = ContinuousLinearMap.id 𝕜 H') :
    formationCapital (E ∘L (A : H →L[𝕜] H') ∘L W) (E ∘L (A : H →L[𝕜] H') ∘L X) = ⊤
      ↔ formationCapital W X = ⊤ := by
  rw [formationCapital_fe_split W X A hQE]

/-! ## Selection consequence -/

omit [CompleteSpace K] [CompleteSpace H] [CompleteSpace H'] [CompleteSpace H''] in
/-- `(RCN.27)`  Bounded formation capital is invariant under functional-equation transport
followed by a common split recovery, so neither operation can supply a missing bounded-capital
premise. -/
theorem iSup_formationCapital_fe_split {ι : Type*} (W : K →L[𝕜] H) (X : ι → (U →L[𝕜] H))
    (A : H ≃L[𝕜] H') {E : H' →L[𝕜] H''} {Q : H'' →L[𝕜] H'}
    (hQE : Q ∘L E = ContinuousLinearMap.id 𝕜 H') :
    (⨆ n, formationCapital (E ∘L (A : H →L[𝕜] H') ∘L W) (E ∘L (A : H →L[𝕜] H') ∘L X n))
      = ⨆ n, formationCapital W (X n) :=
  iSup_congr fun n => formationCapital_fe_split W (X n) A hQE

/-! ## Sharp countermodel: noninjective recovery can erase all capital -/

namespace RecoveryCountermodel

/-- The one-dimensional index carrier. -/
abbrev Src : Type := EuclideanSpace ℂ (Fin 1)

/-- The two-dimensional formation carrier. -/
abbrev Tgt : Type := EuclideanSpace ℂ (Fin 2)

/-- `(RCN.25)`  The defect points along the second coordinate. -/
def defect : Src →L[ℂ] Tgt :=
  (EuclideanSpace.proj (0 : Fin 1)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))

/-- `(RCN.25)`  The recovery kernel forgets the second coordinate. -/
def recovery : Tgt →L[ℂ] Src :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))

/-- The canonical Hilbert basis of the index carrier. -/
noncomputable def srcBasis : HilbertBasis (Fin 1) ℂ Src :=
  (EuclideanSpace.basisFun (Fin 1) ℂ).toHilbertBasis

theorem srcBasis_apply (i : Fin 1) : srcBasis i = EuclideanSpace.single i (1 : ℂ) := by
  simp [srcBasis, OrthonormalBasis.coe_toHilbertBasis]

theorem defect_srcBasis : defect (srcBasis 0) = EuclideanSpace.single (1 : Fin 2) (1 : ℂ) := by
  rw [srcBasis_apply, defect]
  simp

theorem isHilbertSchmidt_defect : IsHilbertSchmidt defect :=
  isHilbertSchmidt_of_summable srcBasis (Summable.of_finite)

theorem hsNormSq_defect : hsNormSq defect = 1 := by
  rw [hsNormSq_eq isHilbertSchmidt_defect srcBasis, tsum_fintype, Fin.sum_univ_one,
    defect_srcBasis, PiLp.norm_single]
  norm_num

/-- `(RCN.26)`  Before recovery the defect costs one unit of formation capital. -/
theorem formationCapital_defect :
    formationCapital (ContinuousLinearMap.id ℂ Tgt) defect = 1 := by
  have hmem : defect ∈ formationFactorizations (ContinuousLinearMap.id ℂ Tgt) defect :=
    ⟨isHilbertSchmidt_defect, ContinuousLinearMap.ext fun v => rfl⟩
  rw [formationCapital_eq_of_mem hmem]
  have hmin : minimalFactor (ContinuousLinearMap.id ℂ Tgt) defect = defect :=
    ContinuousLinearMap.ext fun v =>
      coimageProjection_eq_self_of_injective (W := ContinuousLinearMap.id ℂ Tgt)
        Function.injective_id (defect v)
  rw [hmin, hsNormSq_defect]
  simp

/-- `(RCN.26)`  The recovery kills the defect. -/
theorem recovery_comp_defect : recovery ∘L defect = 0 :=
  ContinuousLinearMap.ext fun v => by
    simp [recovery, defect]

/-- `(RCN.26)`  After the noninjective recovery the capital is zero. -/
theorem formationCapital_recovery_defect :
    formationCapital (recovery ∘L ContinuousLinearMap.id ℂ Tgt)
      (recovery ∘L defect) = 0 := by
  refine le_antisymm ?_ bot_le
  have hmem : (0 : Src →L[ℂ] Tgt)
      ∈ formationFactorizations (recovery ∘L ContinuousLinearMap.id ℂ Tgt) (recovery ∘L defect) := by
    refine ⟨isHilbertSchmidt_zero, ?_⟩
    rw [recovery_comp_defect, ContinuousLinearMap.comp_zero]
  have := formationCapital_le_of_mem hmem
  simpa [hsNormSq] using this

/-- `(RCN.26)`  A noninjective recovery strictly decreases the formation capital: the apparent
gain is exactly the erasure of the second coordinate. -/
theorem formationCapital_recovery_lt :
    formationCapital (recovery ∘L ContinuousLinearMap.id ℂ Tgt) (recovery ∘L defect)
      < formationCapital (ContinuousLinearMap.id ℂ Tgt) defect := by
  rw [formationCapital_recovery_defect, formationCapital_defect]
  exact zero_lt_one

end RecoveryCountermodel

end

end GaloisForLFunctions.HTGeometry
