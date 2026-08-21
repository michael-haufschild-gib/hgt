import GaloisForLFunctions.HTGeometry.TernaryFormationComplex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Duality, Hodge carrier, equivariance and selection for the formation charge

The symmetric formation charge of three subspaces has a perfect dual pairing with the annihilator
distributivity quotient; over a real or complex inner-product space it has a positive harmonic
carrier; it is transported by every linear automorphism, so a functional-equation involution can
fix the observer while acting by `-1` on the charge; the fused Gram nullity of two legs exceeds
the sum of the local nullities by exactly the charge; and a coherent noncontracting history of
charges has bounded cofinal action only if it vanishes identically.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Equivariance -/

section Equivariance

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem map_formationCore (A : V ≃ₗ[K] V) (U W Z : Submodule K V) :
    Submodule.map (A : V →ₗ[K] V) (formationCore U W Z)
      = formationCore (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
        (Z.map (A : V →ₗ[K] V)) := by
  rw [formationCore, formationCore, Submodule.map_inf _ A.injective, Submodule.map_sup]

theorem map_formationBoundary (A : V ≃ₗ[K] V) (U W Z : Submodule K V) :
    Submodule.map (A : V →ₗ[K] V) (formationBoundary U W Z)
      = formationBoundary (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
        (Z.map (A : V →ₗ[K] V)) := by
  rw [formationBoundary, formationBoundary, Submodule.map_sup,
    Submodule.map_inf _ A.injective, Submodule.map_inf _ A.injective]

/-- **`(TFIM.29)`–`(TFIM.30)`.**  Every linear automorphism transports the formation charge. -/
def formationChargeEquivOfAut (A : V ≃ₗ[K] V) (U W Z : Submodule K V) :
    FormationCharge U W Z ≃ₗ[K]
      FormationCharge (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
        (Z.map (A : V →ₗ[K] V)) := by
  refine LinearEquiv.ofBijective
    (subQuotMap (A : V →ₗ[K] V) (le_of_eq (map_formationCore A U W Z))
      (le_of_eq (map_formationBoundary A U W Z))) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    have h0 : Submodule.Quotient.mk
        (⟨A (x : V), le_of_eq (map_formationCore A U W Z) ⟨(x : V), x.2, rfl⟩⟩ :
          ↥(formationCore (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
            (Z.map (A : V →ₗ[K] V)))) = 0 := hq
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : A (x : V)
        ∈ formationBoundary (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
          (Z.map (A : V →ₗ[K] V)) := h0
    rw [← map_formationBoundary A U W Z] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hxy : (x : V) = y := A.injective hyx.symm ▸ rfl
    rw [Submodule.Quotient.mk_eq_zero]
    show (x : V) ∈ formationBoundary U W Z
    rw [hxy]
    exact hy
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    have hx : (x : V) ∈ Submodule.map (A : V →ₗ[K] V) (formationCore U W Z) := by
      rw [map_formationCore]
      exact x.2
    obtain ⟨v, hv, hvx⟩ := hx
    refine ⟨Submodule.Quotient.mk ⟨v, hv⟩, ?_⟩
    show Submodule.Quotient.mk (⟨A v, _⟩ :
      ↥(formationCore (U.map (A : V →ₗ[K] V)) (W.map (A : V →ₗ[K] V))
        (Z.map (A : V →ₗ[K] V)))) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hvx

end Equivariance

/-! ## Cofinal properness selection (Theorem 9.1) -/

section CofinalProperness

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]

/-- **Theorem 9.1 `(TFIM.43)`.**  A coherent noncontracting charge history has bounded cofinal
action exactly when it vanishes identically. -/
theorem bddAbove_cofinalAction_iff (j : ∀ n, H n → H (n + 1)) (h : ∀ n, H n)
    (hnc : ∀ n x, ‖x‖ ≤ ‖j n x‖) (hcoh : ∀ n, h (n + 1) = j n (h n))
    (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n)
    (hdiv : ∀ m : ℕ, ¬ BddAbove (Set.range fun N => ∑ n ∈ Finset.Ico m (N + 1), a n)) :
    BddAbove (Set.range fun N => ∑ n ∈ Finset.range (N + 1), a n * ‖h n‖ ^ 2)
      ↔ ∀ n, h n = 0 := by
  have hmono : ∀ m n, m ≤ n → ‖h m‖ ≤ ‖h n‖ := by
    intro m n hmn
    induction n with
    | zero =>
      rw [Nat.le_zero.mp hmn]
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (by rw [hcoh n]; exact hnc n (h n))
      · rw [show m = n + 1 by omega]
  constructor
  · intro hbd
    by_contra hne
    push Not at hne
    obtain ⟨m, hm⟩ := hne
    have hmn : 0 < ‖h m‖ := norm_pos_iff.mpr hm
    have hmpos : 0 < ‖h m‖ ^ 2 := by positivity
    obtain ⟨M, hM⟩ := hbd
    refine hdiv m ⟨M / ‖h m‖ ^ 2, ?_⟩
    rintro y ⟨N, rfl⟩
    simp only []
    rcases Nat.lt_or_ge N m with hlt | hge
    · have hempty : Finset.Ico m (N + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      have hMnn : (0 : ℝ) ≤ M := by
        have h0 := hM (Set.mem_range_self 0)
        have : (0 : ℝ) ≤ ∑ n ∈ Finset.range 1, a n * ‖h n‖ ^ 2 := by
          refine Finset.sum_nonneg fun n _ => ?_
          have := (hpos n).le
          positivity
        linarith
      positivity
    · have hsub : Finset.Ico m (N + 1) ⊆ Finset.range (N + 1) := by
        intro x hx
        rw [Finset.mem_range]
        exact (Finset.mem_Ico.mp hx).2
      have hbound : (∑ n ∈ Finset.Ico m (N + 1), a n) * ‖h m‖ ^ 2
          ≤ ∑ n ∈ Finset.range (N + 1), a n * ‖h n‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine le_trans (Finset.sum_le_sum (fun n hn => ?_))
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
            have := (hpos n).le
            positivity))
        have hmn : m ≤ n := (Finset.mem_Ico.mp hn).1
        have hnorm : ‖h m‖ ^ 2 ≤ ‖h n‖ ^ 2 := by
          have := hmono m n hmn
          nlinarith [norm_nonneg (h m), norm_nonneg (h n)]
        exact mul_le_mul_of_nonneg_left hnorm (hpos n).le
      have hle := hM (Set.mem_range_self N)
      rw [le_div_iff₀ hmpos]
      linarith
  · intro hzero
    refine ⟨0, ?_⟩
    rintro y ⟨N, rfl⟩
    refine le_of_eq ?_
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [hzero n, norm_zero]
    ring

end CofinalProperness

/-! ## Reporter duality (Theorem 5.1) -/

section Duality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Quotients by submodules of a subspace of the dual space.  The general submodule-quotient
instance is not found by unification through `Module.Dual`, so it is registered here. -/
instance dualSubmoduleHasQuotient (S : Submodule K (Module.Dual K V)) :
    HasQuotient ↥S (Submodule K ↥S) := @Submodule.hasQuotient K ↥S _ _ _

/-- A functional annihilating the smaller submodule restricts to the subquotient. -/
def annihilatorToDual (D E : Submodule K V) :
    ↥E.dualAnnihilator →ₗ[K]
      Module.Dual K (↥D ⧸ Submodule.comap D.subtype E) where
  toFun φ := Submodule.liftQ _ ((φ : Module.Dual K V).comp D.subtype) (by
    intro x hx
    exact (Submodule.mem_dualAnnihilator _).mp φ.2 (x : V) hx)
  map_add' φ ψ := by
    refine Submodule.linearMap_qext _ ?_
    ext x
    rfl
  map_smul' c φ := by
    refine Submodule.linearMap_qext _ ?_
    ext x
    rfl

@[simp] theorem annihilatorToDual_mk (D E : Submodule K V) (φ : ↥E.dualAnnihilator) (x : ↥D) :
    annihilatorToDual D E φ (Submodule.Quotient.mk x) = (φ : Module.Dual K V) (x : V) := rfl

theorem ker_annihilatorToDual (D E : Submodule K V) :
    LinearMap.ker (annihilatorToDual D E)
      = Submodule.comap E.dualAnnihilator.subtype D.dualAnnihilator := by
  ext φ
  constructor
  · intro hφ
    have h0 : annihilatorToDual D E φ = 0 := hφ
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    intro x hx
    have := congrArg (fun f : Module.Dual K (↥D ⧸ Submodule.comap D.subtype E) =>
      f (Submodule.Quotient.mk ⟨x, hx⟩)) h0
    simpa using this
  · intro hφ
    rw [LinearMap.mem_ker]
    refine Submodule.linearMap_qext _ ?_
    ext x
    have hx := (Submodule.mem_dualAnnihilator _).mp hφ (x : V) x.2
    exact hx

theorem annihilatorToDual_surjective (D E : Submodule K V) (hED : E ≤ D) :
    Function.Surjective (annihilatorToDual D E) := by
  intro ψ
  obtain ⟨g, hg⟩ := (ψ.comp (Submodule.comap D.subtype E).mkQ).exists_extend
  have hgD : ∀ x : ↥D, g (x : V) = ψ (Submodule.Quotient.mk x) := by
    intro x
    have hc := congrArg (fun f : ↥D →ₗ[K] K => f x) hg
    exact hc
  have hgE : g ∈ E.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hz : (Submodule.Quotient.mk (⟨x, hED hx⟩ : ↥D)
        : ↥D ⧸ Submodule.comap D.subtype E) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hgD ⟨x, hED hx⟩, hz, map_zero]
  refine ⟨⟨g, hgE⟩, ?_⟩
  refine Submodule.linearMap_qext _ ?_
  ext x
  exact hgD x

/-- **Reporter duality for a nested pair.**  The dual of a subquotient is the corresponding
subquotient of annihilators. -/
def subQuotDualEquiv (D E : Submodule K V) (hED : E ≤ D) :
    (↥E.dualAnnihilator ⧸
        Submodule.comap E.dualAnnihilator.subtype D.dualAnnihilator)
      ≃ₗ[K] Module.Dual K (↥D ⧸ Submodule.comap D.subtype E) :=
  (Submodule.quotEquivOfEq _ _ (ker_annihilatorToDual D E).symm).trans
    ((annihilatorToDual D E).quotKerEquivOfSurjective
      (annihilatorToDual_surjective D E hED))

variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem dualAnnihilator_formationBoundary (U W Z : Submodule K V) :
    (formationBoundary U W Z).dualAnnihilator
      = (U.dualAnnihilator ⊔ W.dualAnnihilator) ⊓ (U.dualAnnihilator ⊔ Z.dualAnnihilator) := by
  rw [formationBoundary, Submodule.dualAnnihilator_sup_eq,
    Subspace.dualAnnihilator_inf_eq, Subspace.dualAnnihilator_inf_eq]

omit [FiniteDimensional K V] in
theorem dualAnnihilator_formationCore (U W Z : Submodule K V) :
    (formationCore U W Z).dualAnnihilator
      = U.dualAnnihilator ⊔ (W.dualAnnihilator ⊓ Z.dualAnnihilator) := by
  rw [formationCore, Subspace.dualAnnihilator_inf_eq, Submodule.dualAnnihilator_sup_eq]

/-- **Theorem 5.1 `(TFIM.24)`.**  The dual of the formation charge is the annihilator
distributivity quotient: reporter loss and relation birth are perfect duals. -/
def formationChargeDualEquiv (U W Z : Submodule K V) :
    (↥((U.dualAnnihilator ⊔ W.dualAnnihilator) ⊓ (U.dualAnnihilator ⊔ Z.dualAnnihilator)) ⧸
        Submodule.comap ((U.dualAnnihilator ⊔ W.dualAnnihilator)
            ⊓ (U.dualAnnihilator ⊔ Z.dualAnnihilator)).subtype
          (U.dualAnnihilator ⊔ (W.dualAnnihilator ⊓ Z.dualAnnihilator)))
      ≃ₗ[K] Module.Dual K (FormationCharge U W Z) :=
  (subQuotCongr (dualAnnihilator_formationBoundary U W Z).symm
      (dualAnnihilator_formationCore U W Z).symm).trans
    (subQuotDualEquiv (formationCore U W Z) (formationBoundary U W Z)
      (formationBoundary_le_core U W Z))

end Duality

/-! ## The positive Hodge carrier (Theorem 6.1) -/

section Hodge

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For nested closed subspaces, the relative orthogonal complement realizes the subquotient:
each class has a unique harmonic representative. -/
def relCompEquivSubQuot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] (h : N ≤ M) :
    ↥(M ⊓ Nᗮ) ≃ₗ[𝕜] (↥M ⧸ Submodule.comap M.subtype N) := by
  refine LinearEquiv.ofBijective
    ((Submodule.comap M.subtype N).mkQ.comp
      (Submodule.inclusion (inf_le_left : M ⊓ Nᗮ ≤ M))) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : Submodule.Quotient.mk (⟨(x : E), x.2.1⟩ : ↥M) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hN : (x : E) ∈ N := h0
    have hxx : ⟪(x : E), (x : E)⟫_𝕜 = 0 := (Submodule.mem_orthogonal N (x : E)).mp x.2.2 _ hN
    exact Subtype.ext (inner_self_eq_zero.mp hxx)
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    have hsplit : (y : E) - N.starProjection (y : E) ∈ M ⊓ Nᗮ := by
      refine ⟨Submodule.sub_mem _ y.2 (h (N.starProjection_apply_mem (y : E))), ?_⟩
      exact N.sub_starProjection_mem_orthogonal (v := (y : E))
    refine ⟨⟨(y : E) - N.starProjection (y : E), hsplit⟩, ?_⟩
    show Submodule.Quotient.mk
      (⟨(y : E) - N.starProjection (y : E), hsplit.1⟩ : ↥M) = Submodule.Quotient.mk y
    refine (Submodule.Quotient.eq _).mpr ?_
    show ((y : E) - N.starProjection (y : E)) - (y : E) ∈ N
    have hn : ((y : E) - N.starProjection (y : E)) - (y : E) = -(N.starProjection (y : E)) := by
      abel
    rw [hn]
    exact Submodule.neg_mem _ (N.starProjection_apply_mem (y : E))

variable {A B C : Type*}
  [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [FiniteDimensional 𝕜 A]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  [NormedAddCommGroup C] [InnerProductSpace 𝕜 C] [FiniteDimensional 𝕜 C]

/-- **`(TFIM.25)`.**  The degree-one Hodge Laplacian of a two-step complex. -/
def hodgeLaplacian (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] C) : B →ₗ[𝕜] B :=
  d₂ ∘ₗ LinearMap.adjoint d₂ + LinearMap.adjoint d₁ ∘ₗ d₁

/-- The Laplacian quadratic form is the sum of two squares. -/
theorem re_inner_hodgeLaplacian_self (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] C) (x : B) :
    RCLike.re ⟪hodgeLaplacian d₂ d₁ x, x⟫_𝕜
      = ‖LinearMap.adjoint d₂ x‖ ^ 2 + ‖d₁ x‖ ^ 2 := by
  have h1 : ⟪d₂ (LinearMap.adjoint d₂ x), x⟫_𝕜
      = ⟪LinearMap.adjoint d₂ x, LinearMap.adjoint d₂ x⟫_𝕜 :=
    (LinearMap.adjoint_inner_right d₂ (LinearMap.adjoint d₂ x) x).symm
  have h2 : ⟪LinearMap.adjoint d₁ (d₁ x), x⟫_𝕜 = ⟪d₁ x, d₁ x⟫_𝕜 :=
    LinearMap.adjoint_inner_left d₁ x (d₁ x)
  show RCLike.re ⟪d₂ (LinearMap.adjoint d₂ x) + LinearMap.adjoint d₁ (d₁ x), x⟫_𝕜 = _
  rw [inner_add_left, map_add, h1, h2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

/-- **Theorem 6.1 `(TFIM.26)`.**  The harmonic space is the cycles orthogonal to the boundaries. -/
theorem ker_hodgeLaplacian (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] C) :
    LinearMap.ker (hodgeLaplacian d₂ d₁)
      = LinearMap.ker d₁ ⊓ (LinearMap.range d₂)ᗮ := by
  apply le_antisymm
  · intro x hx
    have h0 : hodgeLaplacian d₂ d₁ x = 0 := hx
    have hq := re_inner_hodgeLaplacian_self d₂ d₁ x
    rw [h0, inner_zero_left, map_zero] at hq
    have hn1 := norm_nonneg (LinearMap.adjoint d₂ x)
    have hn2 := norm_nonneg (d₁ x)
    have hd1 : ‖d₁ x‖ = 0 := by nlinarith
    have hd2 : ‖LinearMap.adjoint d₂ x‖ = 0 := by nlinarith
    refine ⟨norm_eq_zero.mp hd1, ?_⟩
    rw [LinearMap.orthogonal_range]
    exact norm_eq_zero.mp hd2
  · intro x hx
    have h1 : d₁ x = 0 := hx.1
    have h2 : LinearMap.adjoint d₂ x = 0 := by
      have := hx.2
      rw [LinearMap.orthogonal_range] at this
      exact this
    show d₂ (LinearMap.adjoint d₂ x) + LinearMap.adjoint d₁ (d₁ x) = 0
    rw [h1, h2, map_zero, map_zero, add_zero]

/-- **Theorem 6.1.**  The harmonic space realizes the first homology of the complex. -/
def harmonicEquivHomology (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] C)
    (h : LinearMap.range d₂ ≤ LinearMap.ker d₁) :
    ↥(LinearMap.ker (hodgeLaplacian d₂ d₁))
      ≃ₗ[𝕜] (↥(LinearMap.ker d₁) ⧸
        Submodule.comap (LinearMap.ker d₁).subtype (LinearMap.range d₂)) :=
  (LinearEquiv.ofEq _ _ (ker_hodgeLaplacian d₂ d₁)).trans
    (relCompEquivSubQuot (LinearMap.ker d₁) (LinearMap.range d₂) h)

/-- **`(TFIM.27)`.**  The harmonic projector has rank the formation charge. -/
theorem finrank_relComp_eq_finrank_subQuot {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (M N : Submodule 𝕜 E) [N.HasOrthogonalProjection] (h : N ≤ M) :
    Module.finrank 𝕜 ↥(M ⊓ Nᗮ)
      = Module.finrank 𝕜 (↥M ⧸ Submodule.comap M.subtype N) :=
  (relCompEquivSubQuot M N h).finrank_eq

/-- **`(TFIM.28)`.**  The nested projection difference is the projection onto the relative
complement, so the metric never changes the charge rank or its zero locus. -/
theorem range_starProjection_relComp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (M N : Submodule 𝕜 E) [(M ⊓ Nᗮ).HasOrthogonalProjection] :
    LinearMap.range ((M ⊓ Nᗮ).starProjection : E →ₗ[𝕜] E) = M ⊓ Nᗮ :=
  Submodule.range_starProjection _

end Hodge

/-! ## Fused Fisher nullity (Theorem 8.1) -/

section Fisher

variable {𝕜 : Type*} [RCLike 𝕜] {V Y : Type*}
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]

/-- **`(TFIM.36)`.**  The Gram operator of an observed leg. -/
def gramOp (L : V →ₗ[𝕜] Y) (A : Submodule 𝕜 V) : ↥A →ₗ[𝕜] ↥A :=
  LinearMap.adjoint (L.domRestrict A) ∘ₗ L.domRestrict A

/-- **`(TFIM.37)`.**  The Gram kernel is the observed kernel of the leg. -/
theorem ker_gramOp (L : V →ₗ[𝕜] Y) (A : Submodule 𝕜 V) :
    LinearMap.ker (gramOp L A) = LinearMap.ker (L.domRestrict A) :=
  LinearMap.ker_adjoint_comp_self _

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 Y] in
theorem finrank_ker_domRestrict (L : V →ₗ[𝕜] Y) (A : Submodule 𝕜 V) :
    Module.finrank 𝕜 (LinearMap.ker (L.domRestrict A))
      = Module.finrank 𝕜 ↥(A ⊓ LinearMap.ker L) := by
  rw [LinearMap.ker_domRestrict, ← Submodule.map_comap_subtype A (LinearMap.ker L)]
  exact (Submodule.equivMapOfInjective A.subtype (Submodule.injective_subtype A) _).finrank_eq

/-- **Theorem 8.1 `(TFIM.38)`.**  Two locally identifiable Gaussian legs can fuse into a
nonidentifiable model, with missing rank exactly the ternary formation charge. -/
theorem finrank_ker_gramOp_sup (L : V →ₗ[𝕜] Y) (W Z : Submodule 𝕜 V) :
    (Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊔ Z))) : ℤ)
      = (Module.finrank 𝕜 (LinearMap.ker (gramOp L W)) : ℤ)
        + (Module.finrank 𝕜 (LinearMap.ker (gramOp L Z)) : ℤ)
        - (Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊓ Z))) : ℤ)
        + (Module.finrank 𝕜 (FormationCharge (LinearMap.ker L) W Z) : ℤ) := by
  have hslack := finrank_formationCharge_eq_nullity_slack L W Z
  have hW : Module.finrank 𝕜 (LinearMap.ker (gramOp L W))
      = Module.finrank 𝕜 ↥(W ⊓ LinearMap.ker L) := by
    rw [ker_gramOp, finrank_ker_domRestrict]
  have hZ : Module.finrank 𝕜 (LinearMap.ker (gramOp L Z))
      = Module.finrank 𝕜 ↥(Z ⊓ LinearMap.ker L) := by
    rw [ker_gramOp, finrank_ker_domRestrict]
  have hS : Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊔ Z)))
      = Module.finrank 𝕜 ↥((W ⊔ Z) ⊓ LinearMap.ker L) := by
    rw [ker_gramOp, finrank_ker_domRestrict]
  have hI : Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊓ Z)))
      = Module.finrank 𝕜 ↥((W ⊓ Z) ⊓ LinearMap.ker L) := by
    rw [ker_gramOp, finrank_ker_domRestrict]
  omega

/-- **Theorem 8.1 `(TFIM.39)`.**  With both legs identifiable, the fused Gram nullity is exactly
the formation charge. -/
theorem finrank_ker_gramOp_sup_of_disjoint (L : V →ₗ[𝕜] Y) (W Z : Submodule 𝕜 V)
    (hW : Disjoint W (LinearMap.ker L)) (hZ : Disjoint Z (LinearMap.ker L)) :
    Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊔ Z)))
      = Module.finrank 𝕜 (FormationCharge (LinearMap.ker L) W Z) := by
  have hmain := finrank_ker_gramOp_sup L W Z
  have hWz : Module.finrank 𝕜 (LinearMap.ker (gramOp L W)) = 0 := by
    rw [ker_gramOp, finrank_ker_domRestrict, disjoint_iff.mp hW, finrank_bot]
  have hZz : Module.finrank 𝕜 (LinearMap.ker (gramOp L Z)) = 0 := by
    rw [ker_gramOp, finrank_ker_domRestrict, disjoint_iff.mp hZ, finrank_bot]
  have hIz : Module.finrank 𝕜 (LinearMap.ker (gramOp L (W ⊓ Z))) = 0 := by
    rw [ker_gramOp, finrank_ker_domRestrict]
    have : (W ⊓ Z) ⊓ LinearMap.ker L = ⊥ := by
      rw [← le_bot_iff, ← disjoint_iff.mp hW]
      exact inf_le_inf_right _ inf_le_left
    rw [this, finrank_bot]
  omega

end Fisher

/-! ## The functional-equation-fixed countermodel (§7) -/

section Countermodel

variable (k : Type*) [Field k]

/-- The first axis of `k × k`. -/
def firstAxis : Submodule k (k × k) := Submodule.span k {((1 : k), (0 : k))}

theorem firstAxis_inf_diagLine : firstAxis k ⊓ diagLine k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨u, v⟩ ⟨hA, hB⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hA
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hB
  have hv0 : (0 : k) = v := by
    have h := congrArg Prod.snd hc
    simpa using h
  have he2 : e = v := by
    have h := congrArg Prod.snd he
    simpa using h
  have he1 : e = u := by
    have h := congrArg Prod.fst he
    simpa using h
  have hu : u = 0 := by rw [← he1, he2, ← hv0]
  have hv : v = 0 := hv0.symm
  simp [hu, hv]

theorem firstAxis_inf_axisLine : firstAxis k ⊓ axisLine k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨u, v⟩ ⟨hA, hB⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hA
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hB
  have hv0 : (0 : k) = v := by
    have h := congrArg Prod.snd hc
    simpa using h
  have hu0 : (0 : k) = u := by
    have h := congrArg Prod.fst he
    simpa using h
  simp [← hu0, ← hv0]

theorem diagLine_sup_axisLine : diagLine k ⊔ axisLine k = ⊤ := by
  rw [Submodule.eq_top_iff']
  rintro ⟨u, v⟩
  refine Submodule.mem_sup.mpr ⟨u • ((1 : k), (1 : k)),
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
    (v - u) • ((0 : k), (1 : k)),
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
  refine Prod.ext ?_ ?_
  · show u * 1 + (v - u) * 0 = u
    ring
  · show u * 1 + (v - u) * 1 = v
    ring

/-- **`(TFIM.32)`.**  The formation charge of the three lines is the first axis. -/
def countermodelChargeEquiv :
    FormationCharge (firstAxis k) (diagLine k) (axisLine k) ≃ₗ[k] ↥(firstAxis k) := by
  refine (Submodule.quotEquivOfEqBot _ ?_).trans (LinearEquiv.ofEq _ _ ?_)
  · show (formationBoundary (firstAxis k) (diagLine k) (axisLine k)).comap
      (formationCore (firstAxis k) (diagLine k) (axisLine k)).subtype = ⊥
    rw [show formationBoundary (firstAxis k) (diagLine k) (axisLine k) = ⊥ from by
      show (firstAxis k ⊓ diagLine k) ⊔ (firstAxis k ⊓ axisLine k) = ⊥
      rw [firstAxis_inf_diagLine, firstAxis_inf_axisLine, sup_idem],
      Submodule.comap_bot, Submodule.ker_subtype]
  · show formationCore (firstAxis k) (diagLine k) (axisLine k) = firstAxis k
    rw [formationCore, diagLine_sup_axisLine, inf_top_eq]

/-- The functional-equation involution `(TFIM.34)`. -/
def counterInvolutionMap : (k × k) →ₗ[k] (k × k) :=
  ((LinearMap.snd k k k) - (LinearMap.fst k k k)).prod (LinearMap.snd k k k)

@[simp] theorem counterInvolutionMap_apply (p : k × k) :
    counterInvolutionMap k p = (p.2 - p.1, p.2) := rfl

theorem counterInvolutionMap_involutive :
    (counterInvolutionMap k).comp (counterInvolutionMap k) = LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  refine Prod.ext ?_ ?_
  · show p.2 - (p.2 - p.1) = p.1
    ring
  · rfl

/-- The functional-equation involution as an automorphism. -/
def counterInvolution : (k × k) ≃ₗ[k] (k × k) :=
  LinearEquiv.ofLinear (counterInvolutionMap k) (counterInvolutionMap k)
    (counterInvolutionMap_involutive k) (counterInvolutionMap_involutive k)

/-- **`(TFIM.35)`.**  The observer is exactly fixed by the involution. -/
theorem snd_comp_counterInvolution :
    (LinearMap.snd k k k).comp (counterInvolutionMap k) = LinearMap.snd k k k := by
  refine LinearMap.ext fun p => ?_
  rfl

theorem map_counterInvolution_firstAxis :
    Submodule.map (counterInvolutionMap k) (firstAxis k) = firstAxis k := by
  rw [firstAxis, Submodule.map_span, Set.image_singleton]
  have hv : counterInvolutionMap k ((1 : k), (0 : k)) = (-1 : k) • ((1 : k), (0 : k)) := by
    refine Prod.ext ?_ ?_
    · show (0 : k) - 1 = -1 * 1
      ring
    · show (0 : k) = -1 * 0
      ring
  rw [hv]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 (-1 : k) (by simp)) _

theorem map_counterInvolution_diagLine :
    Submodule.map (counterInvolutionMap k) (diagLine k) = axisLine k := by
  rw [diagLine, axisLine, Submodule.map_span, Set.image_singleton]
  congr 1
  refine Set.singleton_eq_singleton_iff.mpr (Prod.ext ?_ ?_)
  · show (1 : k) - 1 = 0
    ring
  · rfl

theorem map_counterInvolution_axisLine :
    Submodule.map (counterInvolutionMap k) (axisLine k) = diagLine k := by
  rw [diagLine, axisLine, Submodule.map_span, Set.image_singleton]
  congr 1
  refine Set.singleton_eq_singleton_iff.mpr (Prod.ext ?_ ?_)
  · show (1 : k) - 0 = 1
    ring
  · rfl

/-- **§7 countermodel.**  The involution fixes the observer exactly, exchanges the two legs, fixes
the recovery kernel, and acts by `-1` on the nonzero formation charge: functional-equation
symmetry is information-neutral, not selective. -/
theorem countermodel_functional_equation_neutral :
    (counterInvolutionMap k).comp (counterInvolutionMap k) = LinearMap.id
      ∧ (LinearMap.snd k k k).comp (counterInvolutionMap k) = LinearMap.snd k k k
      ∧ Submodule.map (counterInvolutionMap k) (firstAxis k) = firstAxis k
      ∧ Submodule.map (counterInvolutionMap k) (diagLine k) = axisLine k
      ∧ Submodule.map (counterInvolutionMap k) (axisLine k) = diagLine k
      ∧ Module.finrank k (FormationCharge (firstAxis k) (diagLine k) (axisLine k)) = 1 := by
  refine ⟨counterInvolutionMap_involutive k, snd_comp_counterInvolution k,
    map_counterInvolution_firstAxis k, map_counterInvolution_diagLine k,
    map_counterInvolution_axisLine k, ?_⟩
  rw [(countermodelChargeEquiv k).finrank_eq, firstAxis]
  exact finrank_span_singleton (by simp)

end Countermodel

end

end GaloisForLFunctions.HTGeometry
