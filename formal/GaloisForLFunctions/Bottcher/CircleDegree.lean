/-
# `degZ` from a lift endpoint, and the standard circle generator

`degZ ⟦q⟧` is the integer index of a loop `q` in `ℂ*`. If `q` lifts to a path `L : I → ℂ` through the
exponential covering (`pexp ∘ L = q`) with `L 0 = 0`, then `degZ ⟦q⟧` is read directly off the endpoint:
`L 1 = m·2πi ⟹ degZ ⟦q⟧ = m`. The standard circle `s ↦ exp(2πi·s)` lifts to `s ↦ 2πi·s`, so it has
`degZ = 1` — the generator of `π₁(ℂ*)`. This is the computational core behind the `2ⁿ`-fold monodromy
of the escape-level tower.
-/
import GaloisForLFunctions.Bottcher.Pi1CMinusZero

open Topology unitInterval

namespace Pi1CMinusZero

/-- **`degZ` from a lift endpoint.** If a loop `q` lifts to `L : I → ℂ` (`pexp ∘ L = q`) starting at
`L 0 = 0` and ending at `L 1 = m·2πi`, then `degZ ⟦q⟧ = m`. -/
theorem degZ_eq_of_lift (q : Path one_cs one_cs) (L : C(I, ℂ)) (hL : pexp ∘ L = q)
    (h0 : L 0 = (e0 : ℂ)) (m : ℤ)
    (h1 : (L 1 : ℂ) = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    degZ ⟦q⟧ = m := by
  have hc : (degClass ⟦q⟧ : ℂ) = L 1 := degClass_eq_of_lift q L hL h0
  have hsp := degOfFiber_spec (degClass ⟦q⟧)
  rw [hc, h1] at hsp
  have hm : (m : ℂ) = (degOfFiber (degClass ⟦q⟧) : ℂ) := mul_right_cancel₀ twopiI_ne_zero hsp
  show fiberEquivInt (degClass ⟦q⟧) = m
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hm.symm

/-- The standard circle loop `s ↦ exp(2πi·s)` in `ℂ*`, based at `1`. -/
noncomputable def circleLoop : Path one_cs one_cs where
  toFun := fun s => pexp ((2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
  continuous_toFun := continuous_pexp.comp (by fun_prop)
  source' := by
    show pexp ((2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) = one_cs
    simp
  target' := by
    show pexp ((2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) = one_cs
    have h := pexp_zmul 1
    rw [Int.cast_one, one_mul] at h
    simpa using h

/-- **The standard circle has winding `1`** — the generator of `π₁(ℂ*)`. -/
theorem degZ_circleLoop : degZ ⟦circleLoop⟧ = 1 := by
  refine degZ_eq_of_lift circleLoop
    ⟨fun s => (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ), by fun_prop⟩ rfl ?_ 1 ?_
  · show (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ) = (e0 : ℂ)
    simp [e0]
  · show (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ) = ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    simp

/-- The `k`-fold circle loop `s ↦ exp(k·2πi·s)` in `ℂ*`, based at `1`. -/
noncomputable def circleLoopNat (k : ℕ) : Path one_cs one_cs where
  toFun := fun s => pexp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))
  continuous_toFun := continuous_pexp.comp (by fun_prop)
  source' := by
    show pexp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ)) = one_cs
    simp
  target' := by
    show pexp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) = one_cs
    have h := pexp_zmul (k : ℤ)
    rw [Int.cast_natCast] at h
    have : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [Set.Icc.coe_one, Complex.ofReal_one, mul_one]
    rw [this, mul_assoc] at *
    simpa [mul_assoc] using h

/-- **The `k`-fold circle has winding `k`.** -/
theorem degZ_circleLoopNat (k : ℕ) : degZ ⟦circleLoopNat k⟧ = (k : ℤ) := by
  refine degZ_eq_of_lift (circleLoopNat k)
    ⟨fun s => (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ), by fun_prop⟩ rfl ?_ (k : ℤ) ?_
  · show (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((0 : I) : ℝ) = (e0 : ℂ)
    simp [e0]
  · show (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)
      = ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    rw [Set.Icc.coe_one, Complex.ofReal_one, mul_one, Int.cast_natCast]

end Pi1CMinusZero
