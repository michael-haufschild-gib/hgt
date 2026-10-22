import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Real.Basic

/-!
# Arithmetic endpoints and the relative middle

The endpoint complex of a number field is `ℝ` in degree zero together with the two-term complex
`[P → D]` in degrees one and two, where `P` is the real Kummer space, `D` the real Arakelov
divisor space and the map is the principal-divisor map.  The Arakelov exact sequence
`0 → P → D → ℝ → 0` computes its cohomology: nothing in degree one, the degree line in degree
two.

Removing those endpoints from any three-term arithmetic complex leaves a relative object
concentrated in degree one.

* `deningerEndpointH1_eq_bot` and `deningerEndpointH2Equiv` are the endpoint cohomology.
* `DeningerConeLES` packages the long exact cohomology sequence of the cone triangle, and
  `deningerRelativeMiddle_eq_zero`, `deningerRelativeMiddleEquiv` prove that the cone has
  cohomology only in degree one, where it is the middle cohomology of the target.
-/

namespace RHTower

section EndpointComplex

variable {P D : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup D] [Module ℝ D]

/-- **Degree one.**  The endpoint complex is acyclic in degree one: the principal-divisor map is
injective. -/
theorem deningerEndpointH1_eq_bot (pr : P →ₗ[ℝ] D) (hinj : Function.Injective pr) :
    LinearMap.ker pr = ⊥ :=
  LinearMap.ker_eq_bot.mpr hinj

/-- **Degree two.**  The endpoint complex has degree-two cohomology the Arakelov degree line. -/
noncomputable def deningerEndpointH2Equiv (pr : P →ₗ[ℝ] D) (deg : D →ₗ[ℝ] ℝ)
    (hex : Function.Exact pr deg) (hsurj : Function.Surjective deg) :
    (D ⧸ LinearMap.range pr) ≃ₗ[ℝ] ℝ :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hex).symm).trans
    (deg.quotKerEquivOfSurjective hsurj)

/-- The degree-two cohomology class of a divisor is its Arakelov degree. -/
theorem deningerEndpointH2Equiv_mk (pr : P →ₗ[ℝ] D) (deg : D →ₗ[ℝ] ℝ)
    (hex : Function.Exact pr deg) (hsurj : Function.Surjective deg) (d : D) :
    deningerEndpointH2Equiv pr deg hex hsurj (Submodule.Quotient.mk d) = deg d := by
  simp [deningerEndpointH2Equiv]

end EndpointComplex

section RelativeMiddle

variable {A B M : ℤ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)]
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)]

/-- The long exact cohomology sequence of the cone triangle
`C_end → C_Den → C_mid → C_end[1]`: `A` is the cohomology of the endpoint complex, `B` that of
the target, `M` that of the cone. -/
structure DeningerConeLES (φ : ∀ i, A i →ₗ[ℝ] B i) (ψ : ∀ i, B i →ₗ[ℝ] M i)
    (δ : ∀ i, M i →ₗ[ℝ] A (i + 1)) : Prop where
  /-- Exactness at the target cohomology. -/
  exactB : ∀ i, Function.Exact (φ i) (ψ i)
  /-- Exactness at the cone cohomology. -/
  exactM : ∀ i, Function.Exact (ψ i) (δ i)
  /-- Exactness at the endpoint cohomology. -/
  exactA : ∀ i, Function.Exact (δ i) (φ (i + 1))

variable {φ : ∀ i, A i →ₗ[ℝ] B i} {ψ : ∀ i, B i →ₗ[ℝ] M i} {δ : ∀ i, M i →ₗ[ℝ] A (i + 1)}

/-- If the connecting map lands in a trivial group and the previous map is surjective, the cone
cohomology vanishes. -/
theorem deningerCone_eq_zero_of_surjective (h : DeningerConeLES φ ψ δ) (i : ℤ)
    (hsurj : Function.Surjective (φ i)) (hzero : Subsingleton (A (i + 1))) (m : M i) :
    m = 0 := by
  have hψ : ∀ b : B i, ψ i b = 0 := by
    intro b
    obtain ⟨a, rfl⟩ := hsurj b
    exact (h.exactB i).apply_apply_eq_zero a
  have hmem : m ∈ LinearMap.ker (δ i) := by
    simp [LinearMap.mem_ker, Subsingleton.elim (δ i m) 0]
  rw [LinearMap.exact_iff.mp (h.exactM i)] at hmem
  obtain ⟨b, rfl⟩ := hmem
  exact hψ b

/-- If both neighbours vanish, the cone cohomology vanishes. -/
theorem deningerCone_eq_zero_of_neighbours (h : DeningerConeLES φ ψ δ) (i : ℤ)
    (hB : Subsingleton (B i)) (hA : Subsingleton (A (i + 1))) (m : M i) : m = 0 := by
  have hmem : m ∈ LinearMap.ker (δ i) := by
    simp [LinearMap.mem_ker, Subsingleton.elim (δ i m) 0]
  rw [LinearMap.exact_iff.mp (h.exactM i)] at hmem
  obtain ⟨b, rfl⟩ := hmem
  rw [Subsingleton.elim b 0, map_zero]

/-- The middle comparison map of the cone sequence is injective when the endpoint cohomology
vanishes there. -/
theorem deningerCone_middle_injective (h : DeningerConeLES φ ψ δ) (i : ℤ)
    (hA : Subsingleton (A i)) : Function.Injective (ψ i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp (h.exactB i)]
  refine le_antisymm ?_ bot_le
  rintro _ ⟨a, rfl⟩
  rw [Submodule.mem_bot, Subsingleton.elim a 0, map_zero]

/-- If the previous cohomology vanishes and the next endpoint map is injective, the cone
cohomology vanishes. -/
theorem deningerCone_eq_zero_of_injective (h : DeningerConeLES φ ψ δ) (i : ℤ)
    (hB : Subsingleton (B i)) (hinj : Function.Injective (φ (i + 1))) (m : M i) : m = 0 := by
  have hδ : δ i m = 0 := by
    have hm : δ i m ∈ LinearMap.range (δ i) := ⟨m, rfl⟩
    rw [← LinearMap.exact_iff.mp (h.exactA i), LinearMap.ker_eq_bot.mpr hinj,
      Submodule.mem_bot] at hm
    exact hm
  have hmem : m ∈ LinearMap.ker (δ i) := by simp [LinearMap.mem_ker, hδ]
  rw [LinearMap.exact_iff.mp (h.exactM i)] at hmem
  obtain ⟨b, rfl⟩ := hmem
  rw [Subsingleton.elim b 0, map_zero]

/-- The middle comparison map of the cone sequence is surjective when the next endpoint map is
injective. -/
theorem deningerCone_middle_surjective (h : DeningerConeLES φ ψ δ) (i : ℤ)
    (hinj : Function.Injective (φ (i + 1))) : Function.Surjective (ψ i) := by
  have hδ : ∀ m : M i, δ i m = 0 := by
    intro m
    have : δ i m ∈ LinearMap.range (δ i) := ⟨m, rfl⟩
    rw [← LinearMap.exact_iff.mp (h.exactA i), LinearMap.ker_eq_bot.mpr hinj,
      Submodule.mem_bot] at this
    exact this
  intro m
  have hmem : m ∈ LinearMap.ker (δ i) := by simp [LinearMap.mem_ker, hδ m]
  rw [LinearMap.exact_iff.mp (h.exactM i)] at hmem
  exact hmem

/-- **Relative middle isolation, degree one.**  The cone cohomology in degree one is the middle
cohomology of the target. -/
noncomputable def deningerRelativeMiddleEquiv (h : DeningerConeLES φ ψ δ)
    (hA1 : Subsingleton (A 1)) (h2 : Function.Injective (φ 2)) :
    B 1 ≃ₗ[ℝ] M 1 :=
  LinearEquiv.ofBijective (ψ 1)
    ⟨deningerCone_middle_injective h 1 hA1,
      deningerCone_middle_surjective h 1 (by
        rw [show ((1 : ℤ) + 1) = 2 by norm_num]
        exact h2)⟩

/-- **Relative middle isolation, vanishing.**  Outside degree one the cone has no cohomology. -/
theorem deningerRelativeMiddle_eq_zero (h : DeningerConeLES φ ψ δ)
    (hA1 : Subsingleton (A 1)) (hA3 : Subsingleton (A 3))
    (h0 : Function.Bijective (φ 0)) (h2 : Function.Bijective (φ 2))
    (hAvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → Subsingleton (A i))
    (hBvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → Subsingleton (B i))
    (i : ℤ) (hi : i ≠ 1) (m : M i) : m = 0 := by
  rcases eq_or_ne i 0 with rfl | hi0
  · refine deningerCone_eq_zero_of_surjective h 0 h0.2 ?_ m
    rw [show ((0 : ℤ) + 1) = 1 by norm_num]
    exact hA1
  rcases eq_or_ne i 2 with rfl | hi2
  · refine deningerCone_eq_zero_of_surjective h 2 h2.2 ?_ m
    rw [show ((2 : ℤ) + 1) = 3 by norm_num]
    exact hA3
  refine deningerCone_eq_zero_of_injective h i (hBvan i hi0 hi hi2) ?_ m
  rcases eq_or_ne i (-1) with rfl | him1
  · rw [show ((-1 : ℤ) + 1) = 0 by norm_num]
    exact h0.1
  · have hs : Subsingleton (A (i + 1)) :=
      hAvan (i + 1) (by omega) (by omega) (by omega)
    intro a b _
    exact Subsingleton.elim a b

/-- Subsingleton form of the vanishing statement. -/
theorem deningerRelativeMiddle_subsingleton (h : DeningerConeLES φ ψ δ)
    (hA1 : Subsingleton (A 1)) (hA3 : Subsingleton (A 3))
    (h0 : Function.Bijective (φ 0)) (h2 : Function.Bijective (φ 2))
    (hAvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → Subsingleton (A i))
    (hBvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → Subsingleton (B i))
    (i : ℤ) (hi : i ≠ 1) : Subsingleton (M i) :=
  ⟨fun a b => by
    rw [deningerRelativeMiddle_eq_zero h hA1 hA3 h0 h2 hAvan hBvan i hi a,
      deningerRelativeMiddle_eq_zero h hA1 hA3 h0 h2 hAvan hBvan i hi b]⟩

end RelativeMiddle

end RHTower
