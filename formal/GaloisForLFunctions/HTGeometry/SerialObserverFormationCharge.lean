import GaloisForLFunctions.HTGeometry.FiniteLawHistoryMachine
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Serial observer formation charge

For composable linear observations `V --L--> Y --M--> Z` and two source subspaces `A, B ⊆ V`, the
observer-created overlap `O_T(A,B) = (T A ∩ T B) / T(A ∩ B)` measures the formation interference
manufactured by `T`.  Serial composition is governed by a canonical five-term exact sequence

`0 → E_M(L;A,B) → O_L(A,B) → O_{M∘L}(A,B) → O_M(L A, L B) → 0`,

where `E_M(L;A,B) = (ker M ∩ (L A ∩ L B)) / (ker M ∩ L(A ∩ B))` is the upstream charge erased by
the second observer.  In finite dimensions the sequence gives the exact charge budget
`o_{ML} = o_L − e_M + o_M`, a classification of information-neutral lifts, a dual reporter
sequence, and a telescoping law along arbitrary serial chains.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {k : Type u} [Field k]

/-! ## Subquotients -/

section SubQuot

variable {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

/-- A linear map carrying one nested pair of submodules into another induces a map of
subquotients. -/
def subQuotMap (f : W →ₗ[k] W') {N D : Submodule k W} {N' D' : Submodule k W'}
    (hN : Submodule.map f N ≤ N') (hD : Submodule.map f D ≤ D') :
    (N ⧸ Submodule.comap N.subtype D) →ₗ[k] (N' ⧸ Submodule.comap N'.subtype D') :=
  Submodule.mapQ _ _ ((f.domRestrict N).codRestrict N' fun x => hN ⟨(x : W), x.2, rfl⟩)
    (by
      intro x hx
      exact hD ⟨(x : W), hx, rfl⟩)

@[simp] theorem subQuotMap_mk (f : W →ₗ[k] W') {N D : Submodule k W} {N' D' : Submodule k W'}
    (hN : Submodule.map f N ≤ N') (hD : Submodule.map f D ≤ D') (x : N) :
    subQuotMap f hN hD (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨f (x : W), hN ⟨(x : W), x.2, rfl⟩⟩ :=
  rfl

theorem finrank_subQuot [FiniteDimensional k W] {N D : Submodule k W} (h : D ≤ N) :
    Module.finrank k (N ⧸ Submodule.comap N.subtype D) + Module.finrank k D
      = Module.finrank k N := by
  have hq := Submodule.finrank_quotient_add_finrank (Submodule.comap N.subtype D)
  have he : Module.finrank k (Submodule.comap N.subtype D) = Module.finrank k D :=
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  omega

end SubQuot

/-! ## Observer-created overlap and erased charge -/

variable {V : Type v} [AddCommGroup V] [Module k V]
  {Y : Type w} [AddCommGroup Y] [Module k Y]
  {Z : Type x} [AddCommGroup Z] [Module k Z]

/-- Numerator of the observer-created overlap: the intersection of the two observed images. -/
def overlapNum (L : V →ₗ[k] Y) (A B : Submodule k V) : Submodule k Y :=
  Submodule.map L A ⊓ Submodule.map L B

/-- Denominator of the observer-created overlap: the observed intersection. -/
def overlapDen (L : V →ₗ[k] Y) (A B : Submodule k V) : Submodule k Y :=
  Submodule.map L (A ⊓ B)

theorem overlapDen_le (L : V →ₗ[k] Y) (A B : Submodule k V) :
    overlapDen L A B ≤ overlapNum L A B :=
  le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)

/-- **The observer-created formation overlap** `O_L(A,B) = (L A ∩ L B) / L(A ∩ B)`. -/
abbrev ObserverOverlap (L : V →ₗ[k] Y) (A B : Submodule k V) : Type w :=
  overlapNum L A B ⧸ Submodule.comap (overlapNum L A B).subtype (overlapDen L A B)

/-- Numerator of the erased charge. -/
def erasureNum (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) : Submodule k Y :=
  LinearMap.ker M ⊓ overlapNum L A B

/-- Denominator of the erased charge. -/
def erasureDen (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) : Submodule k Y :=
  LinearMap.ker M ⊓ overlapDen L A B

theorem erasureDen_le (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    erasureDen M L A B ≤ erasureNum M L A B :=
  inf_le_inf_left _ (overlapDen_le L A B)

/-- **The upstream charge erased by the second observer.** -/
abbrev ErasedCharge (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) : Type w :=
  erasureNum M L A B ⧸
    Submodule.comap (erasureNum M L A B).subtype (erasureDen M L A B)

/-! ## The five-term sequence -/

theorem map_overlapNum_le (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Submodule.map M (overlapNum L A B) ≤ overlapNum (M.comp L) A B := by
  rw [overlapNum, overlapNum, Submodule.map_comp, Submodule.map_comp]
  exact le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right)

theorem map_overlapDen_eq (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Submodule.map M (overlapDen L A B) = overlapDen (M.comp L) A B := by
  rw [overlapDen, overlapDen, Submodule.map_comp]

theorem overlapNum_comp_eq (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    overlapNum (M.comp L) A B = overlapNum M (Submodule.map L A) (Submodule.map L B) := by
  rw [overlapNum, overlapNum, Submodule.map_comp, Submodule.map_comp]

theorem overlapDen_comp_le (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    overlapDen (M.comp L) A B ≤ overlapDen M (Submodule.map L A) (Submodule.map L B) := by
  rw [overlapDen, overlapDen, Submodule.map_comp]
  exact Submodule.map_mono (overlapDen_le L A B)

/-- `(SOF.7)`, first map: an erased class is an upstream overlap class. -/
def erasedToOverlap (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    ErasedCharge M L A B →ₗ[k] ObserverOverlap L A B :=
  subQuotMap LinearMap.id
    (by rw [Submodule.map_id]; exact inf_le_right)
    (by rw [Submodule.map_id]; exact inf_le_right)

/-- `(SOF.7)`, second map: the downstream observer pushes upstream overlap forward. -/
def overlapPush (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    ObserverOverlap L A B →ₗ[k] ObserverOverlap (M.comp L) A B :=
  subQuotMap M (map_overlapNum_le M L A B) (le_of_eq (map_overlapDen_eq M L A B))

/-- `(SOF.7)`, third map: the composite overlap surjects onto the newly created overlap. -/
def overlapProject (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    ObserverOverlap (M.comp L) A B →ₗ[k]
      ObserverOverlap M (Submodule.map L A) (Submodule.map L B) :=
  subQuotMap LinearMap.id
    (by rw [Submodule.map_id]; exact le_of_eq (overlapNum_comp_eq M L A B))
    (by rw [Submodule.map_id]; exact overlapDen_comp_le M L A B)

theorem erasureNum_le (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    erasureNum M L A B ≤ overlapNum L A B := inf_le_right

theorem erasureDen_le' (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    erasureDen M L A B ≤ overlapDen L A B := inf_le_right

@[simp] theorem erasedToOverlap_mk (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V)
    (x : erasureNum M L A B) :
    erasedToOverlap M L A B (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨(x : Y), erasureNum_le M L A B x.2⟩ := rfl

@[simp] theorem overlapPush_mk (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V)
    (y : overlapNum L A B) :
    overlapPush M L A B (Submodule.Quotient.mk y)
      = Submodule.Quotient.mk
        ⟨M (y : Y), map_overlapNum_le M L A B ⟨(y : Y), y.2, rfl⟩⟩ := rfl

@[simp] theorem overlapProject_mk (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V)
    (z : overlapNum (M.comp L) A B) :
    overlapProject M L A B (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk
        ⟨(z : Z), le_of_eq (overlapNum_comp_eq M L A B) z.2⟩ := rfl

/-! ## Exactness (Theorem 2.1) -/

theorem erasedToOverlap_injective (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Injective (erasedToOverlap M L A B) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  rw [LinearMap.mem_ker, erasedToOverlap_mk] at hq
  have h0 : (Submodule.Quotient.mk
      (⟨(x : Y), erasureNum_le M L A B x.2⟩ : overlapNum L A B)
        : ObserverOverlap L A B) = 0 := hq
  rw [Submodule.Quotient.mk_eq_zero] at h0
  have hden : (x : Y) ∈ overlapDen L A B := h0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x.2.1, hden⟩

theorem range_erasedToOverlap (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    LinearMap.range (erasedToOverlap M L A B) = LinearMap.ker (overlapPush M L A B) := by
  apply le_antisymm
  · rintro q ⟨p, rfl⟩
    induction p using Submodule.Quotient.induction_on with | _ x => ?_
    rw [LinearMap.mem_ker, erasedToOverlap_mk, overlapPush_mk, Submodule.Quotient.mk_eq_zero]
    have hx0 : M (x : Y) = 0 := x.2.1
    show M (x : Y) ∈ overlapDen (M.comp L) A B
    rw [hx0]
    exact Submodule.zero_mem _
  · intro q hq
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    have h0 : overlapPush M L A B (Submodule.Quotient.mk y) = 0 := hq
    rw [overlapPush_mk, Submodule.Quotient.mk_eq_zero] at h0
    have hmem : M (y : Y) ∈ overlapDen (M.comp L) A B := h0
    rw [← map_overlapDen_eq M L A B] at hmem
    obtain ⟨y0, hy0, hMy0⟩ := hmem
    have hw : (y : Y) - y0 ∈ erasureNum M L A B := by
      refine ⟨?_, ?_⟩
      · show M ((y : Y) - y0) = 0
        rw [map_sub, hMy0, sub_self]
      · exact Submodule.sub_mem _ y.2 (overlapDen_le L A B hy0)
    refine ⟨Submodule.Quotient.mk ⟨(y : Y) - y0, hw⟩, ?_⟩
    rw [erasedToOverlap_mk]
    show Submodule.Quotient.mk
      (⟨(y : Y) - y0, erasureNum_le M L A B hw⟩ : overlapNum L A B)
      = Submodule.Quotient.mk y
    refine (Submodule.Quotient.eq _).mpr ?_
    show ((y : Y) - y0) - (y : Y) ∈ overlapDen L A B
    have hsub : ((y : Y) - y0) - (y : Y) = -y0 := by abel
    rw [hsub]
    exact Submodule.neg_mem _ hy0

theorem range_overlapPush (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    LinearMap.range (overlapPush M L A B) = LinearMap.ker (overlapProject M L A B) := by
  apply le_antisymm
  · rintro q ⟨p, rfl⟩
    induction p using Submodule.Quotient.induction_on with | _ y => ?_
    rw [LinearMap.mem_ker, overlapPush_mk, overlapProject_mk, Submodule.Quotient.mk_eq_zero]
    show M (y : Y) ∈ overlapDen M (Submodule.map L A) (Submodule.map L B)
    exact ⟨(y : Y), y.2, rfl⟩
  · intro q hq
    induction q using Submodule.Quotient.induction_on with | _ z => ?_
    have h0 : overlapProject M L A B (Submodule.Quotient.mk z) = 0 := hq
    rw [overlapProject_mk, Submodule.Quotient.mk_eq_zero] at h0
    have hmem : (z : Z) ∈ overlapDen M (Submodule.map L A) (Submodule.map L B) := h0
    obtain ⟨y, hy, hMy⟩ := hmem
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    rw [overlapPush_mk]
    show Submodule.Quotient.mk
      (⟨M y, map_overlapNum_le M L A B ⟨y, hy, rfl⟩⟩ : overlapNum (M.comp L) A B)
      = Submodule.Quotient.mk z
    refine (Submodule.Quotient.eq _).mpr ?_
    show M y - (z : Z) ∈ overlapDen (M.comp L) A B
    rw [hMy, sub_self]
    exact Submodule.zero_mem _

theorem overlapProject_surjective (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Surjective (overlapProject M L A B) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ z => ?_
  have hz : (z : Z) ∈ overlapNum (M.comp L) A B := by
    rw [overlapNum_comp_eq]
    exact z.2
  refine ⟨Submodule.Quotient.mk ⟨(z : Z), hz⟩, ?_⟩
  rw [overlapProject_mk]

/-- **Theorem 2.1 `(SOF.6)`.**  The five-term serial observer formation sequence is exact. -/
theorem serialObserver_exact (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Injective (erasedToOverlap M L A B)
      ∧ LinearMap.range (erasedToOverlap M L A B) = LinearMap.ker (overlapPush M L A B)
      ∧ LinearMap.range (overlapPush M L A B) = LinearMap.ker (overlapProject M L A B)
      ∧ Function.Surjective (overlapProject M L A B) :=
  ⟨erasedToOverlap_injective M L A B, range_erasedToOverlap M L A B,
    range_overlapPush M L A B, overlapProject_surjective M L A B⟩

/-! ## Neutrality and vanishing classification -/

theorem subQuot_forall_eq_zero_iff {W : Type*} [AddCommGroup W] [Module k W]
    (N D : Submodule k W) :
    (∀ q : N ⧸ Submodule.comap N.subtype D, q = 0) ↔ N ≤ D := by
  constructor
  · intro h x hx
    have := h (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h q
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [Submodule.Quotient.mk_eq_zero]
    exact h x.2

theorem overlapPush_injective_iff (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Injective (overlapPush M L A B) ↔ erasureNum M L A B ≤ erasureDen M L A B := by
  rw [← subQuot_forall_eq_zero_iff, ← LinearMap.ker_eq_bot, ← range_erasedToOverlap]
  constructor
  · intro h q
    have : erasedToOverlap M L A B q ∈ LinearMap.range (erasedToOverlap M L A B) := ⟨q, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact erasedToOverlap_injective M L A B (by rw [this, map_zero])
  · intro h
    rw [Submodule.eq_bot_iff]
    rintro y ⟨q, rfl⟩
    rw [h q, map_zero]

theorem overlapPush_surjective_iff (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Surjective (overlapPush M L A B)
      ↔ overlapNum M (Submodule.map L A) (Submodule.map L B)
        ≤ overlapDen M (Submodule.map L A) (Submodule.map L B) := by
  rw [← subQuot_forall_eq_zero_iff, ← LinearMap.range_eq_top, range_overlapPush]
  constructor
  · intro h q
    obtain ⟨p, rfl⟩ := overlapProject_surjective M L A B q
    have hp : p ∈ LinearMap.ker (overlapProject M L A B) := by
      rw [h]
      trivial
    exact hp
  · intro h
    rw [Submodule.eq_top_iff']
    intro p
    rw [LinearMap.mem_ker]
    exact h _

/-- **Theorem 4.1 `(SOF.18)`.**  The lift is information-neutral exactly when no upstream charge
is erased and no downstream charge is created. -/
theorem overlapPush_bijective_iff (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Bijective (overlapPush M L A B)
      ↔ erasureNum M L A B = erasureDen M L A B
        ∧ overlapNum M (Submodule.map L A) (Submodule.map L B)
          = overlapDen M (Submodule.map L A) (Submodule.map L B) := by
  rw [Function.Bijective, overlapPush_injective_iff, overlapPush_surjective_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_antisymm h1 (erasureDen_le M L A B),
      le_antisymm h2 (overlapDen_le M (Submodule.map L A) (Submodule.map L B))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_eq h1, le_of_eq h2⟩

/-- **Corollary 4.2 `(SOF.19)`.**  A downstream observer faithful on the two upstream images
transports formation charge information-neutrally. -/
theorem overlapPush_bijective_of_disjoint (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V)
    (hdisj : Disjoint (LinearMap.ker M) (Submodule.map L A ⊔ Submodule.map L B)) :
    Function.Bijective (overlapPush M L A B) := by
  rw [overlapPush_bijective_iff]
  constructor
  · refine le_antisymm ?_ (erasureDen_le M L A B)
    intro y hy
    have hy0 : y ∈ LinearMap.ker M ⊓ (Submodule.map L A ⊔ Submodule.map L B) :=
      ⟨hy.1, (le_sup_left : Submodule.map L A ≤ _) hy.2.1⟩
    rw [disjoint_iff] at hdisj
    rw [hdisj, Submodule.mem_bot] at hy0
    rw [hy0]
    exact Submodule.zero_mem _
  · refine le_antisymm ?_ (overlapDen_le M (Submodule.map L A) (Submodule.map L B))
    rintro z ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvz⟩⟩
    have hdiff : u - v ∈ LinearMap.ker M ⊓ (Submodule.map L A ⊔ Submodule.map L B) := by
      refine ⟨?_, Submodule.sub_mem _ ((le_sup_left : Submodule.map L A ≤ _) hu)
        ((le_sup_right : Submodule.map L B ≤ _) hv)⟩
      show M (u - v) = 0
      rw [map_sub, hvz, sub_self]
    rw [disjoint_iff] at hdisj
    rw [hdisj, Submodule.mem_bot, sub_eq_zero] at hdiff
    exact ⟨u, ⟨hu, hdiff ▸ hv⟩, rfl⟩

/-- **Corollary 4.3 `(SOF.20)`.**  The composite charge vanishes exactly when no downstream
charge is created and every upstream class is erased. -/
theorem overlap_comp_trivial_iff (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    (∀ q : ObserverOverlap (M.comp L) A B, q = 0)
      ↔ (∀ q : ObserverOverlap M (Submodule.map L A) (Submodule.map L B), q = 0)
        ∧ Function.Surjective (erasedToOverlap M L A B) := by
  constructor
  · intro h
    refine ⟨fun q => ?_, ?_⟩
    · obtain ⟨p, rfl⟩ := overlapProject_surjective M L A B q
      rw [h p, map_zero]
    · intro q
      have hq : q ∈ LinearMap.ker (overlapPush M L A B) := by
        rw [LinearMap.mem_ker]
        exact h _
      rw [← range_erasedToOverlap] at hq
      exact hq
  · rintro ⟨h1, h2⟩ q
    have hq : q ∈ LinearMap.ker (overlapProject M L A B) := by
      rw [LinearMap.mem_ker]
      exact h1 _
    rw [← range_overlapPush] at hq
    obtain ⟨r, rfl⟩ := hq
    obtain ⟨e, rfl⟩ := h2 r
    have hker : erasedToOverlap M L A B e ∈ LinearMap.ker (overlapPush M L A B) := by
      rw [← range_erasedToOverlap]
      exact ⟨e, rfl⟩
    exact hker

/-! ## The dual reporter sequence (Theorem 5.1) -/

/-- **Theorem 5.1 `(SOF.21)`.**  The dual sequence of reporters is exact. -/
theorem serialObserver_dual_exact (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    Function.Injective ((overlapProject M L A B).dualMap)
      ∧ LinearMap.range ((overlapProject M L A B).dualMap)
        = LinearMap.ker ((overlapPush M L A B).dualMap)
      ∧ LinearMap.range ((overlapPush M L A B).dualMap)
        = LinearMap.ker ((erasedToOverlap M L A B).dualMap)
      ∧ Function.Surjective ((erasedToOverlap M L A B).dualMap) := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (overlapProject_surjective M L A B), ?_, ?_,
    LinearMap.dualMap_surjective_of_injective (erasedToOverlap_injective M L A B)⟩
  · rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, ← range_overlapPush]
  · rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range, ← range_erasedToOverlap]

/-! ## The exact charge budget -/

/-- Dimension of the observer-created overlap. -/
def overlapRank (L : V →ₗ[k] Y) (A B : Submodule k V) : ℕ :=
  Module.finrank k (ObserverOverlap L A B)

/-- Dimension of the erased charge. -/
def erasedRank (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) : ℕ :=
  Module.finrank k (ErasedCharge M L A B)

theorem overlapRank_add_finrank [FiniteDimensional k Y] (L : V →ₗ[k] Y) (A B : Submodule k V) :
    overlapRank L A B + Module.finrank k (overlapDen L A B)
      = Module.finrank k (overlapNum L A B) :=
  finrank_subQuot (overlapDen_le L A B)

theorem erasedRank_add_finrank [FiniteDimensional k Y] (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y)
    (A B : Submodule k V) :
    erasedRank M L A B + Module.finrank k (erasureDen M L A B)
      = Module.finrank k (erasureNum M L A B) :=
  finrank_subQuot (erasureDen_le M L A B)

theorem overlapRank_eq_zero_of_le [FiniteDimensional k Y] (L : V →ₗ[k] Y) (A B : Submodule k V)
    (h : overlapNum L A B ≤ overlapDen L A B) : overlapRank L A B = 0 := by
  have hEq : overlapDen L A B = overlapNum L A B := le_antisymm (overlapDen_le L A B) h
  have hh := overlapRank_add_finrank L A B
  rw [hEq] at hh
  omega

theorem erasedRank_eq_zero_of_le [FiniteDimensional k Y] (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y)
    (A B : Submodule k V) (h : erasureNum M L A B ≤ erasureDen M L A B) :
    erasedRank M L A B = 0 := by
  have hEq : erasureDen M L A B = erasureNum M L A B := le_antisymm (erasureDen_le M L A B) h
  have hh := erasedRank_add_finrank M L A B
  rw [hEq] at hh
  omega

section FiniteDim

variable [FiniteDimensional k V] [FiniteDimensional k Y] [FiniteDimensional k Z]

omit [FiniteDimensional k V] in
/-- **Corollary 3.1 `(SOF.14)`.**  The exact charge budget: composite charge is upstream charge
minus erased charge plus newly created charge. -/
theorem overlapRank_comp (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    (overlapRank (M.comp L) A B : ℤ)
      = (overlapRank L A B : ℤ) - (erasedRank M L A B : ℤ)
        + (overlapRank M (Submodule.map L A) (Submodule.map L B) : ℤ) := by
  have e1 : Module.finrank k (ObserverOverlap L A B) = overlapRank L A B := rfl
  have e2 : Module.finrank k (ObserverOverlap (M.comp L) A B) = overlapRank (M.comp L) A B := rfl
  have e3 : Module.finrank k (ErasedCharge M L A B) = erasedRank M L A B := rfl
  have h1 : Module.finrank k (LinearMap.range (erasedToOverlap M L A B))
      = erasedRank M L A B :=
    (LinearEquiv.ofInjective _ (erasedToOverlap_injective M L A B)).finrank_eq.symm
  have h2 := LinearMap.finrank_range_add_finrank_ker (overlapPush M L A B)
  have h3 := LinearMap.finrank_range_add_finrank_ker (overlapProject M L A B)
  rw [← range_erasedToOverlap] at h2
  rw [← range_overlapPush] at h3
  have h4 : Module.finrank k (LinearMap.range (overlapProject M L A B))
      = overlapRank M (Submodule.map L A) (Submodule.map L B) := by
    rw [LinearMap.range_eq_top.mpr (overlapProject_surjective M L A B), finrank_top]
    rfl
  omega

/-- **Corollary 3.2 `(SOF.15)`.**  Observer-created overlap is the submodularity slack of the
observed rank function. -/
theorem overlapRank_eq_slack (L : V →ₗ[k] Y) (A B : Submodule k V) :
    (overlapRank L A B : ℤ)
      = (Module.finrank k (Submodule.map L A) : ℤ)
        + (Module.finrank k (Submodule.map L B) : ℤ)
        - (Module.finrank k (Submodule.map L (A ⊔ B)) : ℤ)
        - (Module.finrank k (Submodule.map L (A ⊓ B)) : ℤ) := by
  have h1 := overlapRank_add_finrank L A B
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.map L A) (Submodule.map L B)
  rw [← Submodule.map_sup] at h2
  have hnum : overlapNum L A B = Submodule.map L A ⊓ Submodule.map L B := rfl
  have hden : overlapDen L A B = Submodule.map L (A ⊓ B) := rfl
  rw [hnum, hden] at h1
  omega

/-- **Corollary 3.2 `(SOF.16)`.**  The serial chain rule for submodularity slack. -/
theorem slack_chain_rule (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V) :
    (Module.finrank k (Submodule.map (M.comp L) A) : ℤ)
        + (Module.finrank k (Submodule.map (M.comp L) B) : ℤ)
        - (Module.finrank k (Submodule.map (M.comp L) (A ⊔ B)) : ℤ)
        - (Module.finrank k (Submodule.map (M.comp L) (A ⊓ B)) : ℤ)
      = ((Module.finrank k (Submodule.map L A) : ℤ)
          + (Module.finrank k (Submodule.map L B) : ℤ)
          - (Module.finrank k (Submodule.map L (A ⊔ B)) : ℤ)
          - (Module.finrank k (Submodule.map L (A ⊓ B)) : ℤ))
        - (erasedRank M L A B : ℤ)
        + ((Module.finrank k (Submodule.map M (Submodule.map L A)) : ℤ)
          + (Module.finrank k (Submodule.map M (Submodule.map L B)) : ℤ)
          - (Module.finrank k
              (Submodule.map M (Submodule.map L A ⊔ Submodule.map L B)) : ℤ)
          - (Module.finrank k
              (Submodule.map M (Submodule.map L A ⊓ Submodule.map L B)) : ℤ)) := by
  have h1 := overlapRank_eq_slack (M.comp L) A B
  have h2 := overlapRank_eq_slack L A B
  have h3 := overlapRank_eq_slack M (Submodule.map L A) (Submodule.map L B)
  have h4 := overlapRank_comp M L A B
  omega

omit [FiniteDimensional k V] [FiniteDimensional k Y] [FiniteDimensional k Z] in
theorem overlapRank_comp_of_bijective (M : Y →ₗ[k] Z) (L : V →ₗ[k] Y) (A B : Submodule k V)
    (h : Function.Bijective (overlapPush M L A B)) :
    overlapRank (M.comp L) A B = overlapRank L A B :=
  ((LinearEquiv.ofBijective (overlapPush M L A B) h).finrank_eq).symm

end FiniteDim

theorem overlapRank_id_eq_zero [FiniteDimensional k V] (A B : Submodule k V) :
    overlapRank (LinearMap.id : V →ₗ[k] V) A B = 0 := by
  refine overlapRank_eq_zero_of_le _ A B ?_
  intro y hy
  refine ⟨y, ⟨?_, ?_⟩, rfl⟩
  · obtain ⟨u, hu, rfl⟩ := hy.1
    exact hu
  · obtain ⟨u, hu, rfl⟩ := hy.2
    exact hu

/-! ## Serial chains -/

section Serial

variable {W : ℕ → Type v} [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
  [∀ n, FiniteDimensional k (W n)]

theorem overlapRank_id (A B : Submodule k (W 0)) :
    overlapRank (LinearMap.id : W 0 →ₗ[k] W 0) A B = 0 :=
  overlapRank_id_eq_zero A B

/-- **Theorem 8.1 `(SOF.28)`.**  Serial telescoping of formation charge. -/
theorem serial_telescoping (a : ∀ n, W n →ₗ[k] W (n + 1)) (A B : Submodule k (W 0)) (N : ℕ) :
    (overlapRank (totalTransport a N) A B : ℤ)
      = ∑ j ∈ Finset.range N,
        ((overlapRank (a j) (Submodule.map (totalTransport a j) A)
            (Submodule.map (totalTransport a j) B) : ℤ)
          - (erasedRank (a j) (totalTransport a j) A B : ℤ)) := by
  induction N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, totalTransport, transport_self]
    exact_mod_cast overlapRank_id A B
  | succ N ih =>
    have hstep : totalTransport a (N + 1) = (a N).comp (totalTransport a N) :=
      transport_step a (Nat.zero_le N)
    rw [hstep, overlapRank_comp, ih, Finset.sum_range_succ]
    ring

omit [∀ (n : ℕ), FiniteDimensional k (W n)] in
/-- **Corollary 8.2 `(SOF.29)`.**  A tower of neutral stages cannot change formation charge. -/
theorem overlapRank_stable_of_neutral (a : ∀ n, W n →ₗ[k] W (n + 1)) (A B : Submodule k (W 0))
    (j₀ : ℕ) : ∀ N : ℕ, j₀ ≤ N →
      (∀ j, j₀ ≤ j → j < N →
        Function.Bijective (overlapPush (a j) (totalTransport a j) A B)) →
      overlapRank (totalTransport a N) A B = overlapRank (totalTransport a j₀) A B := by
  intro N
  induction N with
  | zero =>
    intro h _
    rw [Nat.le_zero.mp h]
  | succ N ih =>
    intro hle hneut
    rcases Nat.lt_or_ge j₀ (N + 1) with hlt | hge
    · have hj : j₀ ≤ N := by omega
      have hstep : totalTransport a (N + 1) = (a N).comp (totalTransport a N) :=
        transport_step a (Nat.zero_le N)
      rw [hstep, overlapRank_comp_of_bijective _ _ _ _ (hneut N hj (by omega))]
      exact ih hj fun j h1 h2 => hneut j h1 (by omega)
    · rw [show j₀ = N + 1 by omega]

end Serial

/-! ## Sharp countermodels -/

section Countermodels

variable (k)

/-- The diagonal line in `k × k`. -/
def diagLine : Submodule k (k × k) := Submodule.span k {((1 : k), (1 : k))}

/-- The second axis in `k × k`. -/
def axisLine : Submodule k (k × k) := Submodule.span k {((0 : k), (1 : k))}

theorem diagLine_inf_axisLine : diagLine k ⊓ axisLine k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨u, v⟩ ⟨hA, hB⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hA
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hB
  have hc1 : c = u := by
    have h1 := congrArg Prod.fst hc
    simpa using h1
  have hc2 : c = v := by
    have h2 := congrArg Prod.snd hc
    simpa using h2
  have he1 : (0 : k) = u := by
    have h3 := congrArg Prod.fst he
    simpa using h3
  have hu : u = 0 := he1.symm
  have hv : v = 0 := by
    rw [← hc2, hc1]
    exact hu
  simp [hu, hv]

theorem span_one_eq_top : Submodule.span k {(1 : k)} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_span_singleton]
  exact ⟨x, by simp⟩

theorem map_snd_diagLine :
    Submodule.map (LinearMap.snd k k k) (diagLine k) = ⊤ := by
  rw [diagLine, Submodule.map_span, ← span_one_eq_top k]
  congr 1
  ext y
  simp

theorem map_snd_axisLine :
    Submodule.map (LinearMap.snd k k k) (axisLine k) = ⊤ := by
  rw [axisLine, Submodule.map_span, ← span_one_eq_top k]
  congr 1
  ext y
  simp

/-- The two distinct lines are identified by the second-coordinate observer: one unit of
formation charge is created. -/
theorem overlapRank_snd_lines : overlapRank (LinearMap.snd k k k) (diagLine k) (axisLine k) = 1 := by
  have hnum : overlapNum (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊤ := by
    show Submodule.map (LinearMap.snd k k k) (diagLine k)
      ⊓ Submodule.map (LinearMap.snd k k k) (axisLine k) = ⊤
    rw [map_snd_diagLine, map_snd_axisLine, inf_top_eq]
  have hden : overlapDen (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊥ := by
    show Submodule.map (LinearMap.snd k k k) (diagLine k ⊓ axisLine k) = ⊥
    rw [diagLine_inf_axisLine, Submodule.map_bot]
  have h := overlapRank_add_finrank (LinearMap.snd k k k) (diagLine k) (axisLine k)
  rw [hnum, hden, finrank_bot, finrank_top, Module.finrank_self] at h
  omega

/-- An injective observer creates no charge of its own. -/
theorem overlapRank_id_top : overlapRank (LinearMap.id : k →ₗ[k] k) ⊤ ⊤ = 0 := by
  refine overlapRank_eq_zero_of_le _ _ _ ?_
  intro y _
  exact ⟨y, ⟨trivial, trivial⟩, rfl⟩

theorem erasedRank_id [FiniteDimensional k Y] (L : V →ₗ[k] Y) (A B : Submodule k V) :
    erasedRank (LinearMap.id : Y →ₗ[k] Y) L A B = 0 := by
  refine erasedRank_eq_zero_of_le _ _ _ _ ?_
  rintro y ⟨hy, -⟩
  have hy0 : y = 0 := hy
  rw [hy0]
  exact Submodule.zero_mem _

/-- **`(SOF.24)`, pure erasure.**  The zero observer erases the whole upstream charge. -/
theorem erasedRank_zero_snd :
    erasedRank (0 : k →ₗ[k] k) (LinearMap.snd k k k) (diagLine k) (axisLine k) = 1 := by
  have hnum : erasureNum (0 : k →ₗ[k] k) (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊤ := by
    show LinearMap.ker (0 : k →ₗ[k] k)
      ⊓ overlapNum (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊤
    rw [LinearMap.ker_zero]
    have hnum2 : overlapNum (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊤ := by
      show Submodule.map (LinearMap.snd k k k) (diagLine k)
        ⊓ Submodule.map (LinearMap.snd k k k) (axisLine k) = ⊤
      rw [map_snd_diagLine, map_snd_axisLine, inf_top_eq]
    rw [hnum2, top_inf_eq]
  have hden : erasureDen (0 : k →ₗ[k] k) (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊥ := by
    show LinearMap.ker (0 : k →ₗ[k] k)
      ⊓ overlapDen (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊥
    have hden2 : overlapDen (LinearMap.snd k k k) (diagLine k) (axisLine k) = ⊥ := by
      show Submodule.map (LinearMap.snd k k k) (diagLine k ⊓ axisLine k) = ⊥
      rw [diagLine_inf_axisLine, Submodule.map_bot]
    rw [hden2, inf_bot_eq]
  have h := erasedRank_add_finrank (0 : k →ₗ[k] k) (LinearMap.snd k k k)
    (diagLine k) (axisLine k)
  rw [hnum, hden, finrank_bot, finrank_top, Module.finrank_self] at h
  omega

/-- **`(SOF.24)`.**  The composite of the two-line observer with the zero observer creates no
charge: the composite looks exact only because everything upstream was destroyed. -/
theorem overlapRank_zero_comp_snd :
    overlapRank ((0 : k →ₗ[k] k).comp (LinearMap.snd k k k)) (diagLine k) (axisLine k) = 0 := by
  refine overlapRank_eq_zero_of_le _ _ _ ?_
  rintro y ⟨⟨u, hu, rfl⟩, -⟩
  have h0 : ((0 : k →ₗ[k] k).comp (LinearMap.snd k k k)) u = 0 := rfl
  rw [h0]
  exact Submodule.zero_mem _

theorem overlapRank_zero_top : overlapRank (0 : k →ₗ[k] k) ⊤ ⊤ = 0 := by
  refine overlapRank_eq_zero_of_le _ _ _ ?_
  rintro y ⟨⟨u, -, rfl⟩, -⟩
  have h0 : (0 : k →ₗ[k] k) u = 0 := rfl
  rw [h0]
  exact Submodule.zero_mem _

theorem erasedRank_snd_id :
    erasedRank (LinearMap.snd k k k) (LinearMap.id : (k × k) →ₗ[k] (k × k))
      (diagLine k) (axisLine k) = 0 := by
  refine erasedRank_eq_zero_of_le _ _ _ _ ?_
  rintro y ⟨hy1, hy2⟩
  refine ⟨hy1, ?_⟩
  have hmem : y ∈ diagLine k ⊓ axisLine k := by
    obtain ⟨u, hu, rfl⟩ := hy2.1
    obtain ⟨v, hv, hvy⟩ := hy2.2
    have huv : v = u := hvy
    exact ⟨hu, huv ▸ hv⟩
  exact ⟨y, hmem, rfl⟩

/-- **`(SOF.23)`, neutral transport.**  A faithful downstream observer transports the whole
upstream charge: `1 = 1 − 0 + 0`. -/
theorem countermodel_neutral_transport :
    overlapRank (LinearMap.snd k k k) (diagLine k) (axisLine k) = 1
      ∧ erasedRank (LinearMap.id : k →ₗ[k] k) (LinearMap.snd k k k)
          (diagLine k) (axisLine k) = 0
      ∧ overlapRank (LinearMap.id : k →ₗ[k] k)
          (Submodule.map (LinearMap.snd k k k) (diagLine k))
          (Submodule.map (LinearMap.snd k k k) (axisLine k)) = 0
      ∧ overlapRank ((LinearMap.id : k →ₗ[k] k).comp (LinearMap.snd k k k))
          (diagLine k) (axisLine k) = 1 := by
  refine ⟨overlapRank_snd_lines k,
    erasedRank_id k (LinearMap.snd k k k) (diagLine k) (axisLine k),
    overlapRank_id_eq_zero _ _, ?_⟩
  rw [LinearMap.id_comp]
  exact overlapRank_snd_lines k

/-- **`(SOF.24)`, pure erasure.**  The composite looks exact only because the whole upstream
charge was destroyed: `0 = 1 − 1 + 0`. -/
theorem countermodel_pure_erasure :
    overlapRank (LinearMap.snd k k k) (diagLine k) (axisLine k) = 1
      ∧ erasedRank (0 : k →ₗ[k] k) (LinearMap.snd k k k) (diagLine k) (axisLine k) = 1
      ∧ overlapRank (0 : k →ₗ[k] k)
          (Submodule.map (LinearMap.snd k k k) (diagLine k))
          (Submodule.map (LinearMap.snd k k k) (axisLine k)) = 0
      ∧ overlapRank ((0 : k →ₗ[k] k).comp (LinearMap.snd k k k))
          (diagLine k) (axisLine k) = 0 := by
  refine ⟨overlapRank_snd_lines k, erasedRank_zero_snd k, ?_, overlapRank_zero_comp_snd k⟩
  rw [map_snd_diagLine, map_snd_axisLine]
  exact overlapRank_zero_top k

/-- **`(SOF.25)`, pure downstream generation.**  An exact upstream formation becomes nonexact
after the second observation: `1 = 0 − 0 + 1`. -/
theorem countermodel_pure_generation :
    overlapRank (LinearMap.id : (k × k) →ₗ[k] (k × k)) (diagLine k) (axisLine k) = 0
      ∧ erasedRank (LinearMap.snd k k k) (LinearMap.id : (k × k) →ₗ[k] (k × k))
          (diagLine k) (axisLine k) = 0
      ∧ overlapRank (LinearMap.snd k k k)
          (Submodule.map (LinearMap.id : (k × k) →ₗ[k] (k × k)) (diagLine k))
          (Submodule.map (LinearMap.id : (k × k) →ₗ[k] (k × k)) (axisLine k)) = 1
      ∧ overlapRank ((LinearMap.snd k k k).comp (LinearMap.id : (k × k) →ₗ[k] (k × k)))
          (diagLine k) (axisLine k) = 1 := by
  refine ⟨overlapRank_id_eq_zero _ _, erasedRank_snd_id k, ?_, ?_⟩
  · rw [Submodule.map_id, Submodule.map_id]
    exact overlapRank_snd_lines k
  · rw [LinearMap.comp_id]
    exact overlapRank_snd_lines k

end Countermodels

end

end GaloisForLFunctions.HTGeometry
