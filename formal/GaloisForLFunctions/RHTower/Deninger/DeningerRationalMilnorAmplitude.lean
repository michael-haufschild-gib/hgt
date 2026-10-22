import GaloisForLFunctions.RHTower.Deninger.DeningerMilnorRealShape
import GaloisForLFunctions.HTGeometry.MilnorKTateEuclid

/-!
# The two-term real Milnor amplitude over `ℚ`

Tate's computation of the tame kernel of `ℚ` makes `K_2^M(ℚ)` torsion, hence every higher Milnor
group torsion, hence every real Milnor group in degree at least two zero.  Together with the two
bottom pieces this is the two-term real amplitude over the rational field:

```text
π_q K^M_{ℚ,ℝ} = ℝ           (q = 0)
               = ℚ^× ⊗ ℝ    (q = 1)
               = 0           (q ≥ 2)
```

and consequently every product of two positive-degree real classes vanishes.
-/

namespace RHTower

open scoped TensorProduct
open GaloisForLFunctions.HTGeometry

/-- **The real Milnor group of `ℚ` vanishes in every degree at least two.** -/
theorem deningerRationalMilnorRealVanishing (k : ℕ) (t : MilnorKDeg ℚ (2 + k) ⊗[ℤ] ℝ) : t = 0 :=
  deningerMilnorDegTensorReal_eq_zero ℚ milnorKDegTwo_rat_torsion k t

/-- **Degree two over `ℚ` realifies to zero.** -/
theorem deningerRationalMilnorRealVanishing_two (t : MilnorKDeg ℚ 2 ⊗[ℤ] ℝ) : t = 0 :=
  deningerRationalMilnorRealVanishing 0 t

/-- **The two-term real Milnor amplitude over `ℚ`.**  Degree zero is `ℝ`, degree one is
`ℚ^× ⊗ ℝ`, and every degree at least two vanishes. -/
theorem deningerRationalMilnorAmplitude :
    Nonempty ((MilnorKDeg ℚ 0 ⊗[ℤ] ℝ) ≃ₗ[ℤ] ℝ) ∧
      Nonempty ((MilnorKDeg ℚ 1 ⊗[ℤ] ℝ) ≃ₗ[ℤ] (Additive ℚˣ ⊗[ℤ] ℝ)) ∧
      (∀ k : ℕ, ∀ t : MilnorKDeg ℚ (2 + k) ⊗[ℤ] ℝ, t = 0) :=
  ⟨⟨deningerMilnorDegZeroRealEquiv ℚ⟩, ⟨deningerMilnorDegOneRealEquiv ℚ⟩,
    deningerRationalMilnorRealVanishing⟩

end RHTower
