import GaloisForLFunctions.HTGeometry.SteinbergSymbolCoboundary

/-!
# The Steinberg relation in torus-commutator form

The addition relation in the *first* argument, run at a decomposition `u + v = 1` of the unit, gives
a second expression for the same coboundary of `f(v) = ⟨1, v-1⟩`.  Comparing it with the expression
coming from the addition relation in the second argument cancels every Dennis–Stein symbol and every
Steinberg symbol, and leaves a relation among torus commutators alone:

```text
[ h_ij(U), h_ik(u⁻¹) ] · [ h_ij(w), h_ik(v⁻¹) ]  =  [ h_ij(w), h_ik(U) ] ,
      u + v = 1 ,   w = 1 + v b ,   U = 1 + u b w⁻¹ .
```

This is where the additivity `u + v = 1` enters the theory: it is the only step at which a unit is
split into two units, and it is exactly the hypothesis of the Steinberg relation `{u, 1-u} = 1`.
The relation above is that hypothesis transported into the commutator pairing of two torus elements
attached to different index pairs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Steinberg relation, expressed through commutators of torus elements.** -/
theorem torusCommutator_relation_of_add_one {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v : Rˣ) (huv : (u : R) + (v : R) = 1) (b : R) (w U : Rˣ)
    (hw : (w : R) = 1 + (v : R) * b)
    (hU : (U : R) = 1 + (u : R) * (b * (((w⁻¹ : Rˣ)) : R))) :
    torusCommutator hij hik U u⁻¹ * torusCommutator hij hik w v⁻¹
      = torusCommutator hij hik w U := by
  have hcw : (((w⁻¹ : Rˣ)) : R) * (w : R) = 1 := w.inv_mul
  have huu : (((u⁻¹ : Rˣ)) : R) * (u : R) = 1 := u.inv_mul
  have hvv : (((v⁻¹ : Rˣ)) : R) * (v : R) = 1 := v.inv_mul
  -- the product of the two units is `1 + b`
  have hUw : (((U * w : Rˣ)) : R) = 1 + b := by
    push_cast
    linear_combination (w : R) * hU + hw + ((u : R) * b) * hcw + b * huv
  -- the two Dennis–Stein symbols, normalised to first argument `1`
  have hs1 := dennisStein_scale hij hik hjk (u : R) (b * (((w⁻¹ : Rˣ)) : R)) U u⁻¹ hU
  have hs2 := dennisStein_scale hij hik hjk (v : R) b w v⁻¹ hw
  have e1 : (((u⁻¹ : Rˣ)) : R) * (u : R) = 1 := huu
  have e2 : (b * (((w⁻¹ : Rˣ)) : R)) * (((((u⁻¹ : Rˣ))⁻¹ : Rˣ)) : R) = (U : R) - 1 := by
    rw [inv_inv]
    linear_combination -hU
  have e3 : (((v⁻¹ : Rˣ)) : R) * (v : R) = 1 := hvv
  have e4 : b * (((((v⁻¹ : Rˣ))⁻¹ : Rˣ)) : R) = (w : R) - 1 := by
    rw [inv_inv]
    linear_combination -hw
  rw [e1, e2] at hs1
  rw [e3, e4] at hs2
  -- the addition relation in the first argument
  have hkey := dennisStein_add_left hij hik hjk (u : R) (v : R) b w U hw hU
  rw [huv, hs1, hs2] at hkey
  have hUw' : (((U * w : Rˣ)) : R) - 1 = b := by rw [hUw]; ring
  rw [← hUw'] at hkey
  -- the coboundary form of the same symbol
  have hcob := steinbergSymbol_eq_dennisSteinUnit_coboundary hij hik hjk U w
  rw [dennisSteinUnit, dennisSteinUnit, dennisSteinUnit, torusCommutator] at hcob
  -- centrality of the middle symbol
  have hwone : (w : R) = 1 + 1 * ((w : R) - 1) := by ring
  have hfc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij 1 ((w : R) - 1) w hwone
    (Ne.symm hik) (Ne.symm hjk))
  -- compare and cancel
  have hcomb := hkey.trans hcob.symm
  have hstep := mul_right_cancel hcomb
  rw [mul_assoc] at hstep
  have hstep2 := mul_left_cancel hstep
  rw [← mul_assoc, hfc, mul_assoc] at hstep2
  simp only [torusCommutator]
  exact mul_left_cancel hstep2

end GaloisForLFunctions.HTGeometry

end
