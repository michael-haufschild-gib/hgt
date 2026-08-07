import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Exact.Basic

/-!
# Filtered colimits of modules are exact

A stagewise exact sequence of directed systems stays exact in the direct limit: an element of the
limit killed by the second map comes from some stage, is killed there after moving far enough along
the system, and is therefore in the image of the first map at that stage.

* `directLimit_map_exact` : the direct limit of an exact sequence of directed systems is
  exact.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R ι : Type*} [Ring R] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {G G' G'' : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
  [∀ i, AddCommGroup (G'' i)] [∀ i, Module R (G'' i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
  {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}

/-- **A stagewise exact sequence of directed systems has exact direct limit.** -/
theorem directLimit_map_exact [DirectedSystem G' fun i j h => f' i j h]
    [DirectedSystem G'' fun i j h => f'' i j h]
    (g : ∀ i, G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (g' : ∀ i, G' i →ₗ[R] G'' i) (hg' : ∀ i j h, g' j ∘ₗ f' i j h = f'' i j h ∘ₗ g' i)
    (hexact : ∀ i, Function.Exact (g i) (g' i)) :
    Function.Exact (Module.DirectLimit.map (f := f) (f' := f') g hg)
      (Module.DirectLimit.map (f := f') (f' := f'') g' hg') := by
  intro ξ
  constructor
  · intro hξ
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
    rw [Module.DirectLimit.map_apply_of] at hξ
    obtain ⟨j, hij, hzero⟩ := Module.DirectLimit.of.zero_exact hξ
    have hstage : g' j (f' i j hij x) = 0 := by
      have := LinearMap.congr_fun (hg' i j hij) x
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hzero]
    obtain ⟨y, hy⟩ := ((hexact j) (f' i j hij x)).mp hstage
    refine ⟨Module.DirectLimit.of R ι G f j y, ?_⟩
    rw [Module.DirectLimit.map_apply_of, hy, Module.DirectLimit.of_f]
  · rintro ⟨η, rfl⟩
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of η
    rw [Module.DirectLimit.map_apply_of, Module.DirectLimit.map_apply_of]
    have hzero : g' i (g i y) = 0 := ((hexact i) (g i y)).mpr ⟨y, rfl⟩
    rw [hzero, map_zero]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {R ι : Type*} [Ring R] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {G G' : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}

/-- **A stagewise surjective map of directed systems has surjective direct limit.**  An element of
the limit comes from a stage, where it has a preimage. -/
theorem directLimit_map_surjective [DirectedSystem G' fun i j h => f' i j h]
    (g : ∀ i, G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hsurj : ∀ i, Function.Surjective (g i)) :
    Function.Surjective (Module.DirectLimit.map (f := f) (f' := f') g hg) := by
  intro ξ
  obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of ξ
  obtain ⟨x, hx⟩ := hsurj i y
  refine ⟨Module.DirectLimit.of R ι G f i x, ?_⟩
  rw [Module.DirectLimit.map_apply_of, hx]

/-- **A stagewise injective map of directed systems has injective direct limit.**  A class killed by
the map dies at some stage, where injectivity applies. -/
theorem directLimit_map_injective [DirectedSystem G fun i j h => f i j h]
    [DirectedSystem G' fun i j h => f' i j h]
    (g : ∀ i, G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hinj : ∀ i, Function.Injective (g i)) :
    Function.Injective (Module.DirectLimit.map (f := f) (f' := f') g hg) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
  rw [Module.DirectLimit.map_apply_of] at hξ
  obtain ⟨j, hij, hzero⟩ := Module.DirectLimit.of.zero_exact hξ
  have hstage : g j (f i j hij x) = 0 := by
    have hcongr := LinearMap.congr_fun (hg i j hij) x
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcongr
    rw [hcongr, hzero]
  have hxzero : f i j hij x = 0 := hinj j (by rw [hstage, map_zero])
  rw [← Module.DirectLimit.of_f (hij := hij), hxzero, map_zero]

end GaloisForLFunctions.HTGeometry
