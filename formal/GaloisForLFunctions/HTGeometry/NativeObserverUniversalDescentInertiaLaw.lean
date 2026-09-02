import GaloisForLFunctions.HTGeometry.NativeObserverDescentEffectivityLaw
import GaloisForLFunctions.HTGeometry.NegativeIndexRankBound

/-!
# Native observer descent, pointed-fibre exactness, and Stokes inertia

This file completes the exact infrastructure of the native-observer law.  Set observers receive
the full coimage/descent/effectivity/serial/parallel package.  A pointed-set long exact sequence
interface retains every degree and the `pi₀` endpoint without silently upgrading pointed-set
exactness to group exactness.  Finally, the Stokes port theorem uses the actual maximal negative
index and full bilinear radical.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w h

section SetObserver

variable {X : Type u} {O : Type v} {Z : Type w}

/-- The native Set effectivity comparison is bijective exactly for surjective observers. -/
theorem observerEffectivityMap_bijective_iff_surjective (q : X → O) :
    Function.Bijective (observerEffectivityMap q) ↔ Function.Surjective q := by
  constructor
  · intro he o
    obtain ⟨xbar, hxbar⟩ := he.2 o
    induction xbar using Quotient.inductionOn with
    | _ x =>
      exact ⟨x, (observerEffectivityMap_coimageMap q x).symm.trans hxbar⟩
  · exact observerEffectivityMap_bijective_of_surjective q

/-- All exact Set-level clauses of universal native observation in one theorem, with no
surjectivity, injectivity, or separation assumption. -/
theorem nativeSetObserver_descent_effectivity_serial_parallel
    (q : X → O) (chi : X → Z) {O' : Type*} (f : O → O')
    {I : Type*} [Fintype I] {Oi : I → Type*} (qi : ∀ i, X → Oi i) (x y : X) :
    ((∃! b : ObserverCoimage q → Z, chi = b ∘ observerCoimageMap q) ↔
        ∀ a b, q a = q b → chi a = chi b) ∧
      ((∃ d : O → Z, chi = d ∘ q) ↔
        ∃ b : ObserverCoimage q → Z,
          chi = b ∘ observerCoimageMap q ∧
            ∃ d : O → Z, b = d ∘ observerEffectivityMap q) ∧
      (Function.Bijective (observerEffectivityMap q) ↔ Function.Surjective q) ∧
      (q x = q y → f (q x) = f (q y)) ∧
      ((fun i => qi i x) = (fun i => qi i y) ↔ ∀ i, qi i x = qi i y) := by
  exact ⟨observerCoimage_descendedMap_existsUnique q chi,
    observer_factorization_iff_descend_and_extend q chi,
    observerEffectivityMap_bijective_iff_surjective q,
    observerKernel_serial_mono q f,
    observerKernel_parallel_iff qi x y⟩

end SetObserver

/-! ### Pointed homotopy-fibre exactness interface -/

/-- Exactness at a pointed set: the image of the incoming map is precisely the fibre of the
outgoing map over the distinguished point.  This definition applies unchanged at `pi₀`. -/
def PointedExactAt {A B C : Type*} (c₀ : C) (incoming : A → B) (outgoing : B → C) : Prop :=
  ∀ b, outgoing b = c₀ ↔ ∃ a, incoming a = b

/-- Typed long exact sequence carried by a pointed homotopy fibre.  For every `n`, it records
`pi_(n+1)(O) → pi_n(F) → pi_n(X) → pi_n(O)`, exact at all three middle positions.
At `n=0`, `exactAtSource` is literally pointed-set exactness. -/
structure PointedFibreLongExactSequence where
  observer : ℕ → Type h
  fibre : ℕ → Type h
  source : ℕ → Type h
  observerBase : ∀ n, observer n
  fibreBase : ∀ n, fibre n
  sourceBase : ∀ n, source n
  boundary : ∀ n, observer (n + 1) → fibre n
  fibreToSource : ∀ n, fibre n → source n
  sourceToObserver : ∀ n, source n → observer n
  exactAtFibre : ∀ n, PointedExactAt (sourceBase n) (boundary n) (fibreToSource n)
  exactAtSource : ∀ n, PointedExactAt (observerBase n) (fibreToSource n) (sourceToObserver n)
  exactAtObserverSucc : ∀ n,
    PointedExactAt (fibreBase n) (sourceToObserver (n + 1)) (boundary n)

namespace PointedFibreLongExactSequence

/-- Every consecutive pair in the fibre long exact sequence composes to the relevant basepoint,
including the pointed-set `pi₀` pair. -/
theorem consecutive_maps_to_base (E : PointedFibreLongExactSequence) :
    (∀ n x, E.fibreToSource n (E.boundary n x) = E.sourceBase n) ∧
      (∀ n x, E.sourceToObserver n (E.fibreToSource n x) = E.observerBase n) ∧
      (∀ n x, E.boundary n (E.sourceToObserver (n + 1) x) = E.fibreBase n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x
    exact (E.exactAtFibre n (E.boundary n x)).2 ⟨x, rfl⟩
  · intro n x
    exact (E.exactAtSource n (E.fibreToSource n x)).2 ⟨x, rfl⟩
  · intro n x
    exact (E.exactAtObserverSucc n (E.sourceToObserver (n + 1) x)).2 ⟨x, rfl⟩

/-- The degree-zero segment is retained as pointed-set exactness, not group exactness. -/
theorem piZero_exact (E : PointedFibreLongExactSequence) :
    PointedExactAt (E.observerBase 0) (E.fibreToSource 0) (E.sourceToObserver 0) :=
  E.exactAtSource 0

end PointedFibreLongExactSequence

/-! ### Exact Stokes inertia bound -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Full radical of a real bilinear form. -/
def bilinearRadical (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Submodule ℝ V := LinearMap.ker Q

/-- Negative-definiteness of a bilinear form on a subspace. -/
def BilinearNegativeOn (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (W : Submodule ℝ V) : Prop :=
  ∀ v ∈ W, v ≠ 0 → Q v v < 0

/-- Set of dimensions of negative-definite subspaces. -/
def bilinearNegativeDimensions [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Set ℕ :=
  {n | ∃ W : Submodule ℝ V, BilinearNegativeOn Q W ∧ Module.finrank ℝ W = n}

/-- Negative index: maximal dimension of a negative-definite subspace. -/
noncomputable def bilinearNegativeIndex [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℕ :=
  sSup (bilinearNegativeDimensions Q)

theorem bilinearNegativeDimensions_nonempty [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (bilinearNegativeDimensions Q).Nonempty := by
  refine ⟨0, ⊥, ?_, by simp⟩
  intro v hv hne
  simp at hv
  exact (hne hv).elim

theorem bilinearNegativeDimensions_bddAbove [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    BddAbove (bilinearNegativeDimensions Q) := by
  refine ⟨Module.finrank ℝ V, ?_⟩
  rintro n ⟨W, hW, rfl⟩
  exact Submodule.finrank_le W

theorem exists_negativeCarrier_finrank_eq_index [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∃ W : Submodule ℝ V,
      BilinearNegativeOn Q W ∧ Module.finrank ℝ W = bilinearNegativeIndex Q := by
  exact Nat.sSup_mem (bilinearNegativeDimensions_nonempty Q)
    (bilinearNegativeDimensions_bddAbove Q)

/-- Exact finite-dimensional Stokes port data.  Positivity is required only on the vertical
kernel, exactly as in the paper theorem. -/
structure StokesPortData (V : Type*) [AddCommGroup V] [Module ℝ V] (r : ℕ) where
  port : V →ₗ[ℝ] (Fin r → ℝ)
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symmetric : ∀ x y, form x y = form y x
  positiveOnVertical : ∀ v, port v = 0 → v ≠ 0 → 0 < form v v

theorem stokes_negativeSubspace_add_radical_le_rank
    [FiniteDimensional ℝ V] {r : ℕ} (D : StokesPortData V r)
    (W : Submodule ℝ V) (hW : BilinearNegativeOn D.form W) :
    Module.finrank ℝ W + Module.finrank ℝ (bilinearRadical D.form) ≤
      Module.finrank ℝ D.port.range := by
  let R : Submodule ℝ V := bilinearRadical D.form
  have hWR : Disjoint W R := by
    rw [disjoint_iff]
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    by_contra hne
    have hneg := hW v hv.1 hne
    have hrad : D.form v = 0 := hv.2
    have hzero : D.form v v = 0 := by rw [hrad]; rfl
    rw [hzero] at hneg
    exact (lt_irrefl 0) hneg
  have hsupKer : Disjoint (W ⊔ R) D.port.ker := by
    rw [disjoint_iff]
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    by_contra hne
    rcases (Submodule.mem_sup.mp hv.1) with ⟨w, hw, z, hz, hwz⟩
    have hDz : D.form z = 0 := hz
    have hwz0 : D.form w z = 0 := by
      rw [D.symmetric w z, hDz]
      rfl
    have hQ : D.form v v = D.form w w := by
      rw [← hwz]
      simp only [map_add]
      rw [hDz]
      simp [hwz0]
    have hnonpos : D.form w w ≤ 0 := by
      by_cases hw0 : w = 0
      · rw [hw0]
        simp
      · exact (hW w hw hw0).le
    have hpos : 0 < D.form v v := D.positiveOnVertical v hv.2 hne
    rw [hQ] at hpos
    exact (not_lt_of_ge hnonpos) hpos
  have hdimSup : Module.finrank ℝ W + Module.finrank ℝ R =
      Module.finrank ℝ ↥(W ⊔ R) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W R
    rw [disjoint_iff.mp hWR] at h
    simpa using h.symm
  have hdimKer : Module.finrank ℝ ↥(W ⊔ R) + Module.finrank ℝ D.port.ker ≤
      Module.finrank ℝ V := by
    have hsup : Module.finrank ℝ ((W ⊔ R) ⊔ D.port.ker : Submodule ℝ V) ≤
        Module.finrank ℝ V := Submodule.finrank_le _
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ R) D.port.ker
    rw [disjoint_iff.mp hsupKer] at h
    have heq : Module.finrank ℝ ↥(W ⊔ R) + Module.finrank ℝ D.port.ker =
        Module.finrank ℝ ((W ⊔ R) ⊔ D.port.ker : Submodule ℝ V) := by
      simpa using h.symm
    rw [heq]
    exact hsup
  have hrankNull := LinearMap.finrank_range_add_finrank_ker D.port
  change Module.finrank ℝ W + Module.finrank ℝ R ≤ Module.finrank ℝ D.port.range
  rw [hdimSup]
  omega

/-- Sharp Stokes inertia law:
`ind₋(Q) + dim Rad(Q) ≤ rank(M) ≤ r`. -/
theorem stokes_negativeIndex_add_radical_le_rank
    [FiniteDimensional ℝ V] {r : ℕ} (D : StokesPortData V r) :
    bilinearNegativeIndex D.form + Module.finrank ℝ (bilinearRadical D.form) ≤
        Module.finrank ℝ D.port.range ∧
      Module.finrank ℝ D.port.range ≤ r := by
  obtain ⟨W, hW, hdim⟩ := exists_negativeCarrier_finrank_eq_index D.form
  constructor
  · rw [← hdim]
    exact stokes_negativeSubspace_add_radical_le_rank D W hW
  · calc
      Module.finrank ℝ D.port.range ≤ Module.finrank ℝ (Fin r → ℝ) :=
        Submodule.finrank_le D.port.range
      _ = r := Module.finrank_fin_fun ℝ

end

end GaloisForLFunctions.HTGeometry
