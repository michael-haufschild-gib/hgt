import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CoframeAnomalyRank

/-!
# Coframe extension nonerasure and the flat split counterexample

Closed coframes extending through a chain comparison keep every finite marked-prime family
independent modulo target boundaries. Consequently a connecting morphism whose composite with the
comparison vanishes has zero intersection with the finite prime span. A split comparison has zero
connecting morphism. The final section gives the hostile counterexample: an identity-boundary
direct sum with zero connection is flat and primewise split, but every marked prime chain is a
boundary.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section CoframeExtension

variable {k : Type*} [Field k]
variable {C E I : Type*}
variable [AddCommGroup C] [Module k C]
variable [AddCommGroup E] [Module k E]
variable [AddCommGroup I] [Module k I]
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Theorem 3.2, coefficient form: closed coframes extending through `T` prevent every nonzero
finite marked combination from becoming a target boundary. -/
theorem coframeExtension_nonerasure
    {T : C →ₗ[k] E} {u : F → C}
    {φ : F → (C →ₗ[k] k)} {φhat : F → (E →ₗ[k] k)}
    {Be : Submodule k E}
    (hu : CoframeNormalized u φ)
    (hpres : ∀ ℓ, (φhat ℓ).comp T = φ ℓ)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ))
    {a : F → k} (ha : T (∑ p, a p • u p) ∈ Be) :
    a = 0 :=
  transported_independent hu hpres hφhat ha

/-- Homological form of Theorem 3.2: transported marked cycles are linearly independent in the
quotient by target boundaries. -/
theorem coframeExtension_quotient_linearIndependent
    {T : C →ₗ[k] E} {u : F → C}
    {φ : F → (C →ₗ[k] k)} {φhat : F → (E →ₗ[k] k)}
    {Be : Submodule k E}
    (hu : CoframeNormalized u φ)
    (hpres : ∀ ℓ, (φhat ℓ).comp T = φ ℓ)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) :
    LinearIndependent k
      (fun p ↦ Be.mkQ (T (u p)) : F → E ⧸ Be) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hmk : Be.mkQ (T (∑ p, a p • u p)) = 0 := by
    simpa using ha
  have ha0 : a = 0 :=
    coframeExtension_nonerasure hu hpres hφhat (by
      exact (Submodule.Quotient.mk_eq_zero Be).mp hmk)
  simpa using congrFun ha0 i

/-- The finite marked-prime span, presented as the range of its synthesis map. -/
def finitePrimeSpan (u : F → C) : Submodule k C :=
  LinearMap.range (Fintype.linearCombination k u)

/-- Corollary 3.2a: exactness and a preserved coframe force the connecting image to have zero
intersection with the finite marked-prime span. -/
theorem connectingRange_inf_finitePrimeSpan_eq_bot
    {T : C →ₗ[k] E} {u : F → C}
    {φ : F → (C →ₗ[k] k)} {φhat : F → (E →ₗ[k] k)}
    (hu : CoframeNormalized u φ)
    (hpres : ∀ ℓ, (φhat ℓ).comp T = φ ℓ)
    (δ : I →ₗ[k] C) (hexact : T.comp δ = 0) :
    LinearMap.range δ ⊓ finitePrimeSpan u = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases hx.1 with ⟨y, rfl⟩
  rcases hx.2 with ⟨a, ha⟩
  have hTδ : T (δ y) = 0 := by
    have h := congrArg (fun f : I →ₗ[k] E ↦ f y) hexact
    simpa using h
  have hTsum : T (∑ p, a p • u p) = 0 := by
    change T ((Fintype.linearCombination k u) a) = 0
    rw [ha, hTδ]
  have ha0 : a = 0 :=
    coframeExtension_nonerasure hu hpres (fun _ ↦ bot_le)
      (Be := (⊥ : Submodule k E)) (by simpa using hTsum)
  rw [ha0] at ha
  simpa using ha.symm

/-- A split short exact sequence has zero connecting morphism. -/
theorem connectingMap_eq_zero_of_retraction
    (i : C →ₗ[k] E) (r : E →ₗ[k] C)
    (hri : r.comp i = LinearMap.id)
    (δ : I →ₗ[k] C) (hexact : i.comp δ = 0) :
    δ = 0 := by
  ext y
  have hleft := congrArg (fun f : C →ₗ[k] C ↦ f (δ y)) hri
  have hzero := congrArg (fun f : I →ₗ[k] E ↦ f y) hexact
  calc
    δ y = r (i (δ y)) := by simpa using hleft.symm
    _ = r 0 := by rw [show i (δ y) = 0 by simpa using hzero]
    _ = 0 := map_zero r

end CoframeExtension

section FlatSplitCounterexample

variable {k P : Type*} [Field k]

/-- Primewise direct-sum carrier of the hostile flat/split counterexample. -/
abbrev FlatSplitPrimeChains := P →₀ k

/-- Identity boundary: every marked prime chain is exact. -/
noncomputable def flatSplitPrimeBoundary : FlatSplitPrimeChains (k := k) (P := P) →ₗ[k]
    FlatSplitPrimeChains (k := k) (P := P) :=
  LinearMap.id

/-- Zero connection on the primewise split carrier. -/
noncomputable def flatSplitPrimeConnection : FlatSplitPrimeChains (k := k) (P := P) →ₗ[k]
    FlatSplitPrimeChains (k := k) (P := P) :=
  0

@[simp] theorem flatSplitPrimeConnection_flat :
    (flatSplitPrimeConnection (k := k) (P := P)).comp
        (flatSplitPrimeConnection (k := k) (P := P)) = 0 := by
  rfl

theorem flatSplitPrimeBoundary_surjective :
    Function.Surjective (flatSplitPrimeBoundary (k := k) (P := P)) :=
  fun x ↦ ⟨x, rfl⟩

/-- Counterexample 3.1: every marked prime basis cycle is a boundary despite zero connection and
the completely split prime-coordinate carrier. -/
theorem flatSplitPrimeBasis_mem_boundary
    [DecidableEq P] (p : P) :
    Finsupp.single p (1 : k) ∈
      LinearMap.range (flatSplitPrimeBoundary (k := k) (P := P)) :=
  ⟨Finsupp.single p 1, rfl⟩

/-- Strong form of Counterexample 3.1: every finite prime combination is a boundary. -/
theorem flatSplitPrimeCombination_mem_boundary
    (x : FlatSplitPrimeChains (k := k) (P := P)) :
    x ∈ LinearMap.range (flatSplitPrimeBoundary (k := k) (P := P)) :=
  ⟨x, rfl⟩

end FlatSplitCounterexample

end HTGeometry.ConstraintMotiveRelativity
