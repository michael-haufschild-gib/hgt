import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.ObserverDescent

/-!
# Native observer descent and effectivity

Set-level coimage infrastructure makes the kernel-pair descent, target-effectivity, serial
postprocessing, and finite parallel-observer clauses completely explicit.  The imported native
categorical module supplies universal effective descent and its base-change/composition laws.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

section SetObserver

variable {X : Type u} {O : Type v} {Z : Type w}

/-- Kernel relation of an observer. -/
def observerKernelSetoid (q : X → O) : Setoid X where
  r x y := q x = q y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun hxy hyz => hxy.trans hyz⟩

/-- Native set-level coimage of an observer. -/
def ObserverCoimage (q : X → O) := Quotient (observerKernelSetoid q)

/-- Canonical quotient map into observer coimage. -/
def observerCoimageMap (q : X → O) : X → ObserverCoimage q :=
  Quotient.mk (observerKernelSetoid q)

/-- Effective comparison from observer coimage to declared target. -/
def observerEffectivityMap (q : X → O) : ObserverCoimage q → O :=
  Quotient.lift q fun _ _ h => h

@[simp]
theorem observerEffectivityMap_coimageMap (q : X → O) (x : X) :
    observerEffectivityMap q (observerCoimageMap q x) = q x :=
  by simp [observerEffectivityMap, observerCoimageMap]

/-- A charge constant on the full kernel pair has its canonical descended coimage map. -/
def observerDescendedMap (q : X → O) (chi : X → Z)
    (hchi : ∀ x y, q x = q y → chi x = chi y) : ObserverCoimage q → Z :=
  Quotient.lift chi fun _ _ h => hchi _ _ h

@[simp]
theorem observerDescendedMap_coimageMap (q : X → O) (chi : X → Z)
    (hchi : ∀ x y, q x = q y → chi x = chi y) (x : X) :
    observerDescendedMap q chi hchi (observerCoimageMap q x) = chi x :=
  by simp [observerDescendedMap, observerCoimageMap]

/-- Exact kernel-pair/Čech descent criterion, including uniqueness on the coimage. -/
theorem observerCoimage_descendedMap_existsUnique (q : X → O) (chi : X → Z) :
    (∃! b : ObserverCoimage q → Z, chi = b ∘ observerCoimageMap q) ↔
      ∀ x y, q x = q y → chi x = chi y := by
  constructor
  · rintro ⟨b, hb, -⟩ x y hxy
    rw [hb]
    change b (Quotient.mk (observerKernelSetoid q) x) =
      b (Quotient.mk (observerKernelSetoid q) y)
    exact congrArg b (Quotient.sound hxy)
  · intro hchi
    refine ⟨observerDescendedMap q chi hchi, ?_, ?_⟩
    · funext x
      simp [observerDescendedMap, observerCoimageMap]
    · intro b hb
      funext xbar
      refine Quotient.inductionOn xbar fun x => ?_
      simpa [observerDescendedMap, observerCoimageMap] using (congrFun hb x).symm

/-- Factorization through the declared target is descent to coimage plus extension across the
effectivity comparison. -/
theorem observer_factorization_iff_descend_and_extend (q : X → O) (chi : X → Z) :
    (∃ d : O → Z, chi = d ∘ q) ↔
      ∃ b : ObserverCoimage q → Z,
        chi = b ∘ observerCoimageMap q ∧
          ∃ d : O → Z, b = d ∘ observerEffectivityMap q := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨d ∘ observerEffectivityMap q, ?_, d, rfl⟩
    funext x
    simp [observerEffectivityMap, observerCoimageMap]
  · rintro ⟨b, hb, d, rfl⟩
    refine ⟨d, ?_⟩
    rw [hb]
    funext x
    simp [observerEffectivityMap, observerCoimageMap]

/-- In `Set`, an effective epimorphism is a surjection: the effectivity comparison is bijective. -/
theorem observerEffectivityMap_bijective_of_surjective (q : X → O)
    (hq : Function.Surjective q) : Function.Bijective (observerEffectivityMap q) := by
  constructor
  · intro xbar ybar hxy
    refine Quotient.inductionOn₂ xbar ybar (fun x y hxy => ?_) hxy
    exact Quotient.sound hxy
  · intro o
    obtain ⟨x, rfl⟩ := hq o
    exact ⟨observerCoimageMap q x, observerEffectivityMap_coimageMap q x⟩

/-- Effective set observers make full coherent descent sufficient for target factorization. -/
theorem observer_factorization_of_surjective_of_kernel_coherent (q : X → O) (chi : X → Z)
    (hq : Function.Surjective q) (hchi : ∀ x y, q x = q y → chi x = chi y) :
    ∃ d : O → Z, chi = d ∘ q := by
  let e : ObserverCoimage q ≃ O := Equiv.ofBijective (observerEffectivityMap q)
    (observerEffectivityMap_bijective_of_surjective q hq)
  refine ⟨observerDescendedMap q chi hchi ∘ e.symm, ?_⟩
  funext x
  symm
  change observerDescendedMap q chi hchi (e.symm (q x)) = chi x
  rw [← observerEffectivityMap_coimageMap q x]
  exact (congrArg (observerDescendedMap q chi hchi) (e.symm_apply_apply _)).trans
    (observerDescendedMap_coimageMap q chi hchi x)

/-- Serial postprocessing only enlarges the kernel relation. -/
theorem observerKernel_serial_mono (q : X → O) {O' : Type*} (f : O → O')
    {x y : X} (hxy : q x = q y) :
    f (q x) = f (q y) :=
  congrArg f hxy

/-- Natural coimage map induced by serial postprocessing. -/
def observerCoimagePostprocess (q : X → O) {O' : Type*} (f : O → O') :
    ObserverCoimage q → ObserverCoimage (f ∘ q) :=
  Quotient.map id fun _ _ h => observerKernel_serial_mono q f h

@[simp]
theorem observerCoimagePostprocess_coimageMap (q : X → O) {O' : Type*} (f : O → O')
    (x : X) :
    observerCoimagePostprocess q f (observerCoimageMap q x) =
      observerCoimageMap (f ∘ q) x :=
  by simp [observerCoimagePostprocess, observerCoimageMap]

/-- Equality under a finite parallel observer is exactly intersection of component kernel
relations. -/
theorem observerKernel_parallel_iff {I : Type*} [Fintype I]
    {Oi : I → Type*} (q : ∀ i, X → Oi i) (x y : X) :
    (fun i => q i x) = (fun i => q i y) ↔ ∀ i, q i x = q i y := by
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- Parallel refinement cannot lose distinctions already detected by any one component. -/
theorem observerKernel_parallel_subset_component {I : Type*} [Fintype I]
    {Oi : I → Type*} (q : ∀ i, X → Oi i) (i : I) {x y : X}
    (hxy : (fun j => q j x) = (fun j => q j y)) :
    q i x = q i y :=
  congrFun hxy i

end SetObserver

end GaloisForLFunctions.HTGeometry
