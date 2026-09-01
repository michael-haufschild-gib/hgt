import GaloisForLFunctions.HTGeometry.ObserverClockInteractionAnomaly

/-!
# Lower-triangular observer-clock representation

Marginal recovery and anchored interaction split every joint observable into a two-level state.
Scale-only clock multiplication preserves the interaction sector, so its matrix in this splitting
is lower triangular.  Both diagonal blocks compose multiplicatively; the anomaly block obeys an
exact cocycle and commuting clock changes satisfy a flat-square identity.  Marginal recurrence
closes in the lifted state exactly when the anomaly vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- Canonical row-plus-column recovery projection. -/
def productMarginalRecoveryPart
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  productRowPart A B f + productColumnPart A B f

theorem productMarginalRecoveryPart_add_interaction
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productMarginalRecoveryPart A B f +
      productAnchoredInteractionPart A B f = f := by
  exact product_decompose_row_column_anchored A B f

theorem productMarginalRecoveryPart_add
    (A B : Type*) [One A] [One B]
    (f g : FullValueSubtype (A × B) → ℂ) :
    productMarginalRecoveryPart A B (f + g) =
      productMarginalRecoveryPart A B f +
        productMarginalRecoveryPart A B g := by
  funext x
  simp [productMarginalRecoveryPart, productRowPart, productColumnPart]
  ring

theorem productMarginalRecoveryPart_eq_zero_of_mem_anchored
    (A B : Type*) [One A] [One B]
    (q : FullValueSubtype (A × B) → ℂ)
    (hq : q ∈ productAnchoredInteractionSubmodule A B) :
    productMarginalRecoveryPart A B q = 0 := by
  funext x
  simp [productMarginalRecoveryPart, productRowPart, productColumnPart,
    hq.1 x.1.1, hq.1 1, hq.2 x.1.2]

theorem productAnchoredInteractionPart_eq_self_of_mem_anchored
    (A B : Type*) [One A] [One B]
    (q : FullValueSubtype (A × B) → ℂ)
    (hq : q ∈ productAnchoredInteractionSubmodule A B) :
    productAnchoredInteractionPart A B q = q := by
  have hdecomp := productMarginalRecoveryPart_add_interaction A B q
  rw [productMarginalRecoveryPart_eq_zero_of_mem_anchored A B q hq,
    zero_add] at hdecomp
  exact hdecomp

theorem productAnchoredInteractionPart_idempotent
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productAnchoredInteractionPart A B
        (productAnchoredInteractionPart A B f) =
      productAnchoredInteractionPart A B f :=
  productAnchoredInteractionPart_eq_self_of_mem_anchored A B _
    (productAnchoredInteractionPart_mem A B f)

theorem observerClockMultiplier_add_observable
    {A B : Type*} (rate : A → ℂ)
    (f g : FullValueSubtype (A × B) → ℂ) :
    observerClockMultiplier rate (f + g) =
      observerClockMultiplier rate f + observerClockMultiplier rate g := by
  funext x
  simp [observerClockMultiplier]
  ring

theorem observerClockMultiplier_mul_rate
    {A B : Type*} (rate₁ rate₂ : A → ℂ)
    (f : FullValueSubtype (A × B) → ℂ) :
    observerClockMultiplier (rate₁ * rate₂) f =
      observerClockMultiplier rate₁ (observerClockMultiplier rate₂ f) := by
  funext x
  simp [observerClockMultiplier]
  ring

/-- Scale-only clock multiplication preserves the anchored interaction sector. -/
theorem observerClockMultiplier_mem_anchored
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (q : FullValueSubtype (A × B) → ℂ)
    (hq : q ∈ productAnchoredInteractionSubmodule A B) :
    observerClockMultiplier rate q ∈ productAnchoredInteractionSubmodule A B := by
  constructor
  · intro a
    simp [observerClockMultiplier, hq.1 a]
  · intro b
    simp [observerClockMultiplier, hq.2 b]

/-- Marginal block of a clock transport. -/
def observerClockMarginalTransport
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  productMarginalRecoveryPart A B (observerClockMultiplier rate f)

/-- Off-diagonal anomaly block of a clock transport. -/
def observerClockAnomalyTransport
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  productAnchoredInteractionPart A B (observerClockMultiplier rate f)

/-- Diagonal transport of the pre-existing interaction sector. -/
def observerClockInteractionTransport
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  observerClockMultiplier rate (productAnchoredInteractionPart A B f)

/-- Every clock transport splits exactly into observed marginal and lifted interaction history. -/
theorem observerClockTransport_decompose
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockMarginalTransport A B rate f +
      observerClockAnomalyTransport A B rate f =
        observerClockMultiplier rate f := by
  exact productMarginalRecoveryPart_add_interaction A B
    (observerClockMultiplier rate f)

/-- A closed marginal observer has a closed lifted history exactly when its anomaly vanishes. -/
theorem observerClock_closed_marginal_lift_iff_anomaly_zero
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ)
    (hclosed : observerClockMarginalTransport A B rate f = f) :
    observerClockMultiplier rate f = f ↔
      observerClockAnomalyTransport A B rate f = 0 := by
  have hdecomp := observerClockTransport_decompose A B rate f
  rw [hclosed] at hdecomp
  constructor
  · intro hlift
    funext x
    have hx := congrFun hdecomp x
    have hliftx := congrFun hlift x
    simp only [Pi.add_apply] at hx
    change observerClockAnomalyTransport A B rate f x = 0
    calc
      observerClockAnomalyTransport A B rate f x =
          observerClockMultiplier rate f x - f x := by linear_combination hx
      _ = 0 := sub_eq_zero.mpr hliftx
  · intro hanomaly
    rw [hanomaly, add_zero] at hdecomp
    exact hdecomp.symm

/-- Upper-right block vanishes: interactions never flow back into marginals. -/
theorem observerClockMarginalTransport_interaction_eq_zero
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockMarginalTransport A B rate
        (productAnchoredInteractionPart A B f) = 0 := by
  apply productMarginalRecoveryPart_eq_zero_of_mem_anchored
  exact observerClockMultiplier_mem_anchored A B rate _
    (productAnchoredInteractionPart_mem A B f)

/-- On the anchored sector, anomaly extraction is the identity after clock transport. -/
theorem observerClockAnomalyTransport_interaction_eq
    (A B : Type*) [One A] [One B]
    (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockAnomalyTransport A B rate
        (productAnchoredInteractionPart A B f) =
      observerClockInteractionTransport A B rate f := by
  apply productAnchoredInteractionPart_eq_self_of_mem_anchored
  exact observerClockMultiplier_mem_anchored A B rate _
    (productAnchoredInteractionPart_mem A B f)

/-- Marginal diagonal block composes multiplicatively. -/
theorem observerClockMarginalTransport_mul
    (A B : Type*) [One A] [One B]
    (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockMarginalTransport A B (rate₁ * rate₂) f =
      observerClockMarginalTransport A B rate₁
        (observerClockMarginalTransport A B rate₂ f) := by
  simp only [observerClockMarginalTransport]
  rw [observerClockMultiplier_mul_rate]
  have hdecomp := productMarginalRecoveryPart_add_interaction A B
    (observerClockMultiplier rate₂ f)
  conv_lhs =>
    rw [← hdecomp]
  rw [observerClockMultiplier_add_observable,
    productMarginalRecoveryPart_add]
  have hzero : productMarginalRecoveryPart A B
      (observerClockMultiplier rate₁
        (productAnchoredInteractionPart A B
          (observerClockMultiplier rate₂ f))) = 0 :=
    productMarginalRecoveryPart_eq_zero_of_mem_anchored A B _
      (observerClockMultiplier_mem_anchored A B rate₁ _
        (productAnchoredInteractionPart_mem A B (observerClockMultiplier rate₂ f)))
  rw [hzero, add_zero]

/-- Interaction diagonal block composes multiplicatively. -/
theorem observerClockInteractionTransport_mul
    (A B : Type*) [One A] [One B]
    (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockInteractionTransport A B (rate₁ * rate₂) f =
      observerClockInteractionTransport A B rate₁
        (observerClockInteractionTransport A B rate₂ f) := by
  simp only [observerClockInteractionTransport]
  rw [observerClockMultiplier_mul_rate]
  have hq : observerClockMultiplier rate₂
      (productAnchoredInteractionPart A B f) ∈
        productAnchoredInteractionSubmodule A B :=
    observerClockMultiplier_mem_anchored A B rate₂ _
      (productAnchoredInteractionPart_mem A B f)
  rw [productAnchoredInteractionPart_eq_self_of_mem_anchored A B _ hq]

/-- Exact off-diagonal cocycle for composed observer clocks. -/
theorem observerClockAnomalyTransport_mul_cocycle
    (A B : Type*) [One A] [One B]
    (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockAnomalyTransport A B (rate₁ * rate₂) f =
      observerClockAnomalyTransport A B rate₁
          (observerClockMarginalTransport A B rate₂ f) +
        observerClockInteractionTransport A B rate₁
          (observerClockAnomalyTransport A B rate₂ f) := by
  simp only [observerClockAnomalyTransport, observerClockMarginalTransport,
    observerClockInteractionTransport]
  rw [observerClockMultiplier_mul_rate]
  have hdecomp := productMarginalRecoveryPart_add_interaction A B
    (observerClockMultiplier rate₂ f)
  conv_lhs =>
    rw [← hdecomp]
  rw [observerClockMultiplier_add_observable,
    productAnchoredInteractionPart_add]
  have hout : productAnchoredInteractionPart A B
      (observerClockMultiplier rate₁
        (productAnchoredInteractionPart A B
          (observerClockMultiplier rate₂ f))) =
      observerClockMultiplier rate₁
        (productAnchoredInteractionPart A B
          (observerClockMultiplier rate₂ f)) :=
    productAnchoredInteractionPart_eq_self_of_mem_anchored A B _
      (observerClockMultiplier_mem_anchored A B rate₁ _
        (productAnchoredInteractionPart_mem A B (observerClockMultiplier rate₂ f)))
  rw [hout, productAnchoredInteractionPart_idempotent]

/-- Flat clock-square identity: two commuting clock changes have exactly cancelling block
curvature. -/
theorem observerClockAnomalyTransport_flat
    (A B : Type*) [One A] [One B]
    (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ) :
    observerClockAnomalyTransport A B rate₁
          (observerClockMarginalTransport A B rate₂ f) +
        observerClockInteractionTransport A B rate₁
          (observerClockAnomalyTransport A B rate₂ f) =
      observerClockAnomalyTransport A B rate₂
          (observerClockMarginalTransport A B rate₁ f) +
        observerClockInteractionTransport A B rate₂
          (observerClockAnomalyTransport A B rate₁ f) := by
  rw [← observerClockAnomalyTransport_mul_cocycle,
    ← observerClockAnomalyTransport_mul_cocycle]
  rw [mul_comm]

/-- Canonical recovery always lands in the row-plus-column marginal sector. -/
theorem productMarginalRecoveryPart_mem_marginal
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productMarginalRecoveryPart A B f ∈
      productMarginalObservableSubmodule A B := by
  exact Submodule.mem_sup.mpr
    ⟨productRowPart A B f, productRowPart_mem_fst A B f,
      productColumnPart A B f, productColumnPart_mem_snd A B f, rfl⟩

/-- Marginal recovery fixes every marginal observable. -/
theorem productMarginalRecoveryPart_eq_self_of_mem_marginal
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ)
    (hf : f ∈ productMarginalObservableSubmodule A B) :
    productMarginalRecoveryPart A B f = f := by
  have hq :=
    (mem_productMarginalObservableSubmodule_iff_anchoredInteractionPart_eq_zero
      A B f).mp hf
  have hdecomp := productMarginalRecoveryPart_add_interaction A B f
  rw [hq, add_zero] at hdecomp
  exact hdecomp

/-- Canonical marginal recovery is an idempotent projection. -/
theorem productMarginalRecoveryPart_idempotent
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productMarginalRecoveryPart A B
        (productMarginalRecoveryPart A B f) =
      productMarginalRecoveryPart A B f :=
  productMarginalRecoveryPart_eq_self_of_mem_marginal A B _
    (productMarginalRecoveryPart_mem_marginal A B f)

/-- Image of canonical recovery is exactly the marginal sector. -/
theorem range_productMarginalRecoveryPart
    (A B : Type*) [One A] [One B] :
    Set.range (productMarginalRecoveryPart A B) =
      (productMarginalObservableSubmodule A B :
        Set (FullValueSubtype (A × B) → ℂ)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact productMarginalRecoveryPart_mem_marginal A B g
  · intro hf
    exact ⟨f, productMarginalRecoveryPart_eq_self_of_mem_marginal A B f hf⟩

/-- Image of anchored extraction is exactly the anchored interaction sector. -/
theorem range_productAnchoredInteractionPart
    (A B : Type*) [One A] [One B] :
    Set.range (productAnchoredInteractionPart A B) =
      (productAnchoredInteractionSubmodule A B :
        Set (FullValueSubtype (A × B) → ℂ)) := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    exact productAnchoredInteractionPart_mem A B f
  · intro hq
    exact ⟨q, productAnchoredInteractionPart_eq_self_of_mem_anchored A B q hq⟩

/-- Marginal and anchored sectors are complementary and span the full joint-observable space. -/
theorem productMarginalAnchored_complementary
    (A B : Type*) [One A] [One B] :
    Disjoint (productMarginalObservableSubmodule A B)
        (productAnchoredInteractionSubmodule A B) ∧
      productMarginalObservableSubmodule A B ⊔
          productAnchoredInteractionSubmodule A B = ⊤ := by
  obtain ⟨hdisjoint, hsup⟩ :=
    productAnchoredInteractionSubmodule_isCompl A B
  refine ⟨hdisjoint, ?_⟩
  calc
    productMarginalObservableSubmodule A B ⊔
        productAnchoredInteractionSubmodule A B =
      ClassInvariantRestricted
        (productFstSetoid A B ⊓ productSndSetoid A B) := hsup
    _ = ⊤ := classInvariantRestricted_product_inf_eq_top A B

/-- Marginal recovery commutes with scalar multiplication. -/
theorem productMarginalRecoveryPart_smul
    (A B : Type*) [One A] [One B] (c : ℂ)
    (f : FullValueSubtype (A × B) → ℂ) :
    productMarginalRecoveryPart A B (c • f) =
      c • productMarginalRecoveryPart A B f := by
  funext x
  simp [productMarginalRecoveryPart, productRowPart, productColumnPart]
  ring

/-- A constant clock is scalar multiplication on the full joint-observable space. -/
theorem observerClockMultiplier_const
    {A B : Type*} (c : ℂ)
    (f : FullValueSubtype (A × B) → ℂ) :
    observerClockMultiplier (fun _ : A => c) f = c • f := by
  funext x
  simp [observerClockMultiplier]

/-- Constant clocks act by the same scalar on the marginal diagonal block. -/
theorem observerClockMarginalTransport_const_of_mem_marginal
    (A B : Type*) [One A] [One B] (c : ℂ)
    (f : FullValueSubtype (A × B) → ℂ)
    (hf : f ∈ productMarginalObservableSubmodule A B) :
    observerClockMarginalTransport A B (fun _ => c) f = c • f := by
  rw [observerClockMarginalTransport, observerClockMultiplier_const,
    productMarginalRecoveryPart_smul,
    productMarginalRecoveryPart_eq_self_of_mem_marginal A B f hf]

/-- Constant clocks create no off-diagonal anomaly from marginal input. -/
theorem observerClockAnomalyTransport_const_of_mem_marginal
    (A B : Type*) [One A] [One B] (c : ℂ)
    (f : FullValueSubtype (A × B) → ℂ)
    (hf : f ∈ productMarginalObservableSubmodule A B) :
    observerClockAnomalyTransport A B (fun _ => c) f = 0 := by
  exact constantObserverClock_informationNeutral A B c f hf

/-- Constant clocks act by the same scalar on the interaction diagonal block. -/
theorem observerClockInteractionTransport_const_of_mem_anchored
    (A B : Type*) [One A] [One B] (c : ℂ)
    (q : FullValueSubtype (A × B) → ℂ)
    (hq : q ∈ productAnchoredInteractionSubmodule A B) :
    observerClockInteractionTransport A B (fun _ => c) q = c • q := by
  rw [observerClockInteractionTransport,
    productAnchoredInteractionPart_eq_self_of_mem_anchored A B q hq,
    observerClockMultiplier_const]

/-- Zero-argument certificate for canonical two-level recovery, the lower-triangular clock
representation, its exact anomaly cocycle and flat square, recurrence/lift separation, and the
constant-clock diagonal gauge law. -/
theorem observerClockTriangularRepresentation_completion_certificate :
    (∀ (A B : Type*) [One A] [One B]
      (f : FullValueSubtype (A × B) → ℂ),
      productMarginalRecoveryPart A B f +
        productAnchoredInteractionPart A B f = f) ∧
    (∀ (A B : Type*) [One A] [One B],
      Set.range (productMarginalRecoveryPart A B) =
          (productMarginalObservableSubmodule A B : Set _) ∧
      Set.range (productAnchoredInteractionPart A B) =
          (productAnchoredInteractionSubmodule A B : Set _) ∧
      Disjoint (productMarginalObservableSubmodule A B)
          (productAnchoredInteractionSubmodule A B) ∧
      productMarginalObservableSubmodule A B ⊔
          productAnchoredInteractionSubmodule A B = ⊤) ∧
    (∀ (A B : Type*) [One A] [One B]
      (rate : A → ℂ) (q : FullValueSubtype (A × B) → ℂ),
      q ∈ productAnchoredInteractionSubmodule A B →
        observerClockMultiplier rate q ∈
          productAnchoredInteractionSubmodule A B) ∧
    (∀ (A B : Type*) [One A] [One B]
      (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ),
      observerClockMarginalTransport A B rate f +
        observerClockAnomalyTransport A B rate f =
          observerClockMultiplier rate f) ∧
    (∀ (A B : Type*) [One A] [One B]
      (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ),
      observerClockMarginalTransport A B (rate₁ * rate₂) f =
        observerClockMarginalTransport A B rate₁
          (observerClockMarginalTransport A B rate₂ f) ∧
      observerClockInteractionTransport A B (rate₁ * rate₂) f =
        observerClockInteractionTransport A B rate₁
          (observerClockInteractionTransport A B rate₂ f) ∧
      observerClockAnomalyTransport A B (rate₁ * rate₂) f =
        observerClockAnomalyTransport A B rate₁
            (observerClockMarginalTransport A B rate₂ f) +
          observerClockInteractionTransport A B rate₁
            (observerClockAnomalyTransport A B rate₂ f)) ∧
    (∀ (A B : Type*) [One A] [One B]
      (rate₁ rate₂ : A → ℂ) (f : FullValueSubtype (A × B) → ℂ),
      observerClockAnomalyTransport A B rate₁
            (observerClockMarginalTransport A B rate₂ f) +
          observerClockInteractionTransport A B rate₁
            (observerClockAnomalyTransport A B rate₂ f) =
        observerClockAnomalyTransport A B rate₂
            (observerClockMarginalTransport A B rate₁ f) +
          observerClockInteractionTransport A B rate₂
            (observerClockAnomalyTransport A B rate₁ f)) ∧
    (∀ (A B : Type*) [One A] [One B]
      (rate : A → ℂ) (f : FullValueSubtype (A × B) → ℂ),
      observerClockMarginalTransport A B rate f = f →
        (observerClockMultiplier rate f = f ↔
          observerClockAnomalyTransport A B rate f = 0)) ∧
    (∀ (A B : Type*) [One A] [One B] (c : ℂ),
      (∀ (f : FullValueSubtype (A × B) → ℂ),
        f ∈ productMarginalObservableSubmodule A B →
          observerClockMarginalTransport A B (fun _ => c) f = c • f ∧
          observerClockAnomalyTransport A B (fun _ => c) f = 0) ∧
      ∀ (q : FullValueSubtype (A × B) → ℂ),
        q ∈ productAnchoredInteractionSubmodule A B →
          observerClockInteractionTransport A B (fun _ => c) q = c • q) := by
  exact ⟨productMarginalRecoveryPart_add_interaction,
    fun A B _ _ => ⟨range_productMarginalRecoveryPart A B,
      range_productAnchoredInteractionPart A B,
      (productMarginalAnchored_complementary A B).1,
      (productMarginalAnchored_complementary A B).2⟩,
    fun A B _ _ rate q => observerClockMultiplier_mem_anchored A B rate q,
    observerClockTransport_decompose,
    fun A B _ _ rate₁ rate₂ f =>
      ⟨observerClockMarginalTransport_mul A B rate₁ rate₂ f,
        observerClockInteractionTransport_mul A B rate₁ rate₂ f,
        observerClockAnomalyTransport_mul_cocycle A B rate₁ rate₂ f⟩,
    observerClockAnomalyTransport_flat,
    fun A B _ _ rate f =>
      observerClock_closed_marginal_lift_iff_anomaly_zero A B rate f,
    fun A B _ _ c =>
      ⟨fun f hf =>
          ⟨observerClockMarginalTransport_const_of_mem_marginal A B c f hf,
            observerClockAnomalyTransport_const_of_mem_marginal A B c f hf⟩,
        fun q hq =>
          observerClockInteractionTransport_const_of_mem_anchored A B c q hq⟩⟩

end

end GaloisForLFunctions.HTGeometry
