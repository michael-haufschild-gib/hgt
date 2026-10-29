import GaloisForLFunctions.HeckeKreinToeplitz.TheHeckeOrbitKernelOfAZeroConfiguration

/-!
# The archimedean completion carries the same index

The Hecke lattice `ℚ_{>0}` sits in its archimedean completion `ℝ_{>0}` (written `Multiplicative ℝ`
through the logarithm). The orbit kernel extends to it: `K_ℝ(e^s) = W(f, f(· − s))`
(`realOrbitKernel`), and its restriction to `ℚ_{>0}` is the Hecke orbit kernel
(`realOrbitKernel_comp_heckeLogScale`).

**The index is a property of the dense scales** (`negIndex_realOrbitKernel`,
`negIndex_realOrbitKernel_comp`). The index of `K_ℝ` is the number of right zeros the test sees, and
so is the index of its pullback along any homomorphism with dense scales: the continuous group, the
rational lattice and the sublattice of two primes all carry the same negative index. Passing from a
dense subgroup to the completion adds no negative square, and passing back loses none.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests zeroGram DenseShifts)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros orientationIndex_law)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- The orbit kernel on the archimedean completion `ℝ_{>0}`, in logarithmic coordinates. -/
def realOrbitKernel (Z : ZeroConfig) (f : ℝ → ℝ) : Multiplicative ℝ → ℂ :=
  fun v => Z.W (cx f) (shiftTest (Multiplicative.toAdd v) (cx f))

theorem realOrbitKernel_comp_heckeLogScale (Z : ZeroConfig) (f : ℝ → ℝ) :
    realOrbitKernel Z f ∘ heckeLogScale = orbitKernel Z f := rfl

theorem realOrbitKernel_eq (Z : ZeroConfig) (f : ℝ → ℝ) (v : Multiplicative ℝ) :
    realOrbitKernel Z f v = Z.W (shiftTest 0 (cx f)) (shiftTest (Multiplicative.toAdd v) (cx f)) := by
  rw [realOrbitKernel, show shiftTest 0 (cx f) = cx f from funext fun w => by
    simp [ArithmeticCastelnuovoSeveri.translate]]

theorem gram_realOrbitKernel (Z : ZeroConfig) (f : ℝ → ℝ) {ι : Type*} (x : ι → Multiplicative ℝ) :
    gram (realOrbitKernel Z f) x =
      zeroGram Z fun a => shiftTest (Multiplicative.toAdd (x a)) (cx f) := by
  ext a b
  simp only [gram, zeroGram]
  rw [realOrbitKernel_eq, W_shiftTest_shiftTest, W_shiftTest_shiftTest]
  refine tsum_congr fun ρ => ?_
  congr 2
  simp only [toAdd_mul, toAdd_inv]
  push_cast
  ring

theorem denseShifts_univ : DenseShifts (Set.range fun v : Multiplicative ℝ =>
    Multiplicative.toAdd v) := fun v _ ε hε => ⟨v, ⟨Multiplicative.ofAdd v, rfl⟩, by simpa using hε⟩

/-- The index of the archimedean orbit kernel is at most the number of seen right zeros. -/
theorem negIndex_realOrbitKernel_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : negIndex (realOrbitKernel Z f) ≤ (seenRightZeros Z f).encard := by
  classical
  rw [negIndex_le_iff]
  intro n x
  refine (Nat.cast_le.mpr (hermNegIndex_gram_le_image _ x)).trans ?_
  set s := univ.image x
  set S : Finset ℝ := s.image Multiplicative.toAdd
  let e : s ≃ S := Equiv.ofBijective (fun g => ⟨Multiplicative.toAdd (g : Multiplicative ℝ),
    mem_image_of_mem _ g.2⟩)
    ⟨fun a b hab => by
        have h := congrArg (fun z : S => (z : ℝ)) hab
        exact Subtype.ext (Multiplicative.toAdd.injective h),
      fun t => by
        obtain ⟨u, hu, ht⟩ := mem_image.mp t.2
        exact ⟨⟨u, hu⟩, Subtype.ext ht⟩⟩
  have hgram : gram (realOrbitKernel Z f) (fun g : s => (g : Multiplicative ℝ)) =
      (zeroGram Z fun t : S => shiftTest t (cx f)).submatrix e e := by
    rw [gram_realOrbitKernel]; rfl
  have hle : hermNegIndex (gram (realOrbitKernel Z f) fun g : s => (g : Multiplicative ℝ)) ≤
      hermNegIndex (zeroGram Z fun t : S => shiftTest t (cx f)) := by
    rw [hgram]
    exact hermNegIndex_le_of_hermQuad_eq _ _ (LinearMap.funLeft ℂ ℂ e.symm) fun c => by
      rw [hermQuad_submatrix_equiv]; rfl
  have hSD : (S : Set ℝ) ⊆ Set.range fun v : Multiplicative ℝ => Multiplicative.toAdd v :=
    fun t _ => ⟨Multiplicative.ofAdd t, rfl⟩
  exact (orientationIndex_law Z hZ hf denseShifts_univ _).mp ⟨S, hSD, hle⟩

/-- **The archimedean completion carries the index.** -/
theorem negIndex_realOrbitKernel (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : negIndex (realOrbitKernel Z f) = (seenRightZeros Z f).encard := by
  refine le_antisymm (negIndex_realOrbitKernel_le Z hZ hf) ?_
  rw [← negIndex_orbitKernel Z hZ hf, ← realOrbitKernel_comp_heckeLogScale]
  exact negIndex_comp_le _ _

/-- **Every group with dense scales carries the same index.** -/
theorem negIndex_realOrbitKernel_comp (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {K : Type*} [Group K] (φ : K →* Multiplicative ℝ)
    (hD : DenseShifts (Set.range fun h => Multiplicative.toAdd (φ h))) :
    negIndex (realOrbitKernel Z f ∘ φ) = (seenRightZeros Z f).encard := by
  refine le_antisymm ((negIndex_comp_le _ φ).trans (negIndex_realOrbitKernel_le Z hZ hf)) ?_
  refine ENat.forall_natCast_le_iff_le.mp fun m hm => ?_
  obtain ⟨S, hSD, hle⟩ := (orientationIndex_law Z hZ hf hD m).mpr hm
  choose y hy using fun t : S => hSD t.2
  have hgram : gram (realOrbitKernel Z f ∘ φ) y = zeroGram Z fun t : S => shiftTest t (cx f) := by
    have : gram (realOrbitKernel Z f ∘ φ) y = gram (realOrbitKernel Z f) (φ ∘ y) := by
      ext a b; simp [gram, map_mul, map_inv]
    rw [this, gram_realOrbitKernel]
    ext a b
    simp only [zeroGram, Function.comp_apply, hy]
  exact (Nat.cast_le.mpr (hgram ▸ hle)).trans (hermNegIndex_gram_le_negIndex _ y)

end GaloisForLFunctions.HeckeKreinToeplitz
