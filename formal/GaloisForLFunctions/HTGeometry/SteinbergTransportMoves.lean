import GaloisForLFunctions.HTGeometry.WeylTorusConjugation

/-!
# Transport moves for the three-index Steinberg relations

Moving a generator `x_ij(a)` past a generator sharing exactly one index costs one new generator, by
the chain relation `[x_ij(a), x_jk(b)] = x_ik(ab)`.  The four moves below are that relation and its
three inverse variants, written in the form used when normalising a word: the generator being
transported ends up on the right, and the newly created generator on the left.

```text
x_ij(a) x_jk(b)    = x_ik(ab)    x_jk(b)    x_ij(a)
x_ij(a) x_jk(b)⁻¹  = x_jk(b)⁻¹   x_ik(ab)⁻¹ x_ij(a)
x_ij(a) x_ki(c)    = x_kj(ca)⁻¹  x_ki(c)    x_ij(a)
x_ij(a) x_ki(c)⁻¹  = x_ki(c)⁻¹   x_kj(ca)   x_ij(a)
```

Together with the commuting cases — generators sharing a row or a column — these normalise any word
in the three root subgroups attached to a triple of indices, which is what the three-index
Dennis–Stein relation requires.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- Transport past a generator continuing the chain. -/
theorem steinbergX_move_right {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    steinbergX hij a * steinbergX hjk b
      = steinbergX hik (a * b) * steinbergX hjk b * steinbergX hij a := by
  have h := steinbergX_chain hij hjk hik a b
  calc steinbergX hij a * steinbergX hjk b
      = (steinbergX hij a * steinbergX hjk b * (steinbergX hij a)⁻¹
          * (steinbergX hjk b)⁻¹) * steinbergX hjk b * steinbergX hij a := by group
    _ = steinbergX hik (a * b) * steinbergX hjk b * steinbergX hij a := by rw [h]

omit [DecidableEq n] [Fintype n] in
/-- Transport past the inverse of a generator continuing the chain. -/
theorem steinbergX_move_right_inv {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    steinbergX hij a * (steinbergX hjk b)⁻¹
      = (steinbergX hjk b)⁻¹ * (steinbergX hik (a * b))⁻¹ * steinbergX hij a := by
  have h := steinbergX_move_right hij hjk hik a b
  have hconj : steinbergX hij a * steinbergX hjk b * (steinbergX hij a)⁻¹
      = steinbergX hik (a * b) * steinbergX hjk b := by
    rw [h]
    group
  have hinv : steinbergX hij a * (steinbergX hjk b)⁻¹ * (steinbergX hij a)⁻¹
      = (steinbergX hjk b)⁻¹ * (steinbergX hik (a * b))⁻¹ := by
    have := congrArg (fun g : SteinbergGroup R n => g⁻¹) hconj
    simpa [mul_inv_rev, ← mul_assoc] using this
  calc steinbergX hij a * (steinbergX hjk b)⁻¹
      = (steinbergX hij a * (steinbergX hjk b)⁻¹ * (steinbergX hij a)⁻¹)
        * steinbergX hij a := by group
    _ = (steinbergX hjk b)⁻¹ * (steinbergX hik (a * b))⁻¹ * steinbergX hij a := by rw [hinv]

omit [DecidableEq n] [Fintype n] in
/-- Transport past a generator preceding it in the chain. -/
theorem steinbergX_move_left {i j k : n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a c : R) :
    steinbergX hij a * steinbergX hki c
      = (steinbergX hkj (c * a))⁻¹ * steinbergX hki c * steinbergX hij a := by
  have h := steinbergX_chain hki hij hkj c a
  have h' : steinbergX hki c * steinbergX hij a
      = steinbergX hkj (c * a) * steinbergX hij a * steinbergX hki c := by
    calc steinbergX hki c * steinbergX hij a
        = (steinbergX hki c * steinbergX hij a * (steinbergX hki c)⁻¹
            * (steinbergX hij a)⁻¹) * steinbergX hij a * steinbergX hki c := by group
      _ = steinbergX hkj (c * a) * steinbergX hij a * steinbergX hki c := by rw [h]
  calc steinbergX hij a * steinbergX hki c
      = (steinbergX hkj (c * a))⁻¹
        * (steinbergX hkj (c * a) * steinbergX hij a * steinbergX hki c) := by group
    _ = (steinbergX hkj (c * a))⁻¹ * (steinbergX hki c * steinbergX hij a) := by rw [← h']
    _ = (steinbergX hkj (c * a))⁻¹ * steinbergX hki c * steinbergX hij a := by group

omit [DecidableEq n] [Fintype n] in
/-- Transport past the inverse of a generator preceding it in the chain. -/
theorem steinbergX_move_left_inv {i j k : n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a c : R) :
    steinbergX hij a * (steinbergX hki c)⁻¹
      = (steinbergX hki c)⁻¹ * steinbergX hkj (c * a) * steinbergX hij a := by
  have h := steinbergX_move_left hij hki hkj a c
  have hconj : steinbergX hij a * steinbergX hki c * (steinbergX hij a)⁻¹
      = (steinbergX hkj (c * a))⁻¹ * steinbergX hki c := by
    rw [h]
    group
  have hinv : steinbergX hij a * (steinbergX hki c)⁻¹ * (steinbergX hij a)⁻¹
      = (steinbergX hki c)⁻¹ * steinbergX hkj (c * a) := by
    have := congrArg (fun g : SteinbergGroup R n => g⁻¹) hconj
    simpa [mul_inv_rev, ← mul_assoc] using this
  calc steinbergX hij a * (steinbergX hki c)⁻¹
      = (steinbergX hij a * (steinbergX hki c)⁻¹ * (steinbergX hij a)⁻¹)
        * steinbergX hij a := by group
    _ = (steinbergX hki c)⁻¹ * steinbergX hkj (c * a) * steinbergX hij a := by rw [hinv]

end GaloisForLFunctions.HTGeometry

end
