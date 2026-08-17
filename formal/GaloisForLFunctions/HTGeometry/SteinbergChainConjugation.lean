import GaloisForLFunctions.HTGeometry.SteinbergTransportMoves

/-!
# The Bruhat pair as a conjugated three-index commutator

The opposite generator with a factorised parameter is a commutator of two generators attached to a
third index,

```text
x_ji(bc) = [ x_jk(b), x_ki(c) ] ,
```

and conjugation carries a commutator to the commutator of the conjugates.  Transporting `x_ij(a)`
across each factor by the chain relation therefore rewrites the Bruhat pair as

```text
x_ij(a) x_ji(bc) = [ x_ik(ab) x_jk(b) , x_kj(ca)⁻¹ x_ki(c) ] · x_ij(a) .
```

The right-hand side involves only the three root pairs of the triangle `i, j, k`, and the two
rank-one commutators hidden inside it — the `(i,k)` pair `x_ik(ab) / x_ki(c)` and the `(k,j)` pair
`x_kj(ca) / x_jk(b)` — carry the same unit `1 + abc` as the original `(i,j)` pair.  That coincidence
of units is the reason the three Dennis–Stein symbols of the three-index relation compare at all.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- **The Bruhat pair, rewritten on the triangle.** -/
theorem steinbergX_mul_opposite_chain {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) :
    steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = (steinbergX hik (a * b) * steinbergX hjk b)
          * ((steinbergX (Ne.symm hjk) (c * a))⁻¹ * steinbergX (Ne.symm hik) c)
          * (steinbergX hik (a * b) * steinbergX hjk b)⁻¹
          * ((steinbergX (Ne.symm hjk) (c * a))⁻¹ * steinbergX (Ne.symm hik) c)⁻¹
        * steinbergX hij a := by
  have hchain := steinbergX_chain hjk (Ne.symm hik) (Ne.symm hij) b c
  have hB : steinbergX hij a * steinbergX hjk b * (steinbergX hij a)⁻¹
      = steinbergX hik (a * b) * steinbergX hjk b := by
    rw [steinbergX_move_right hij hjk hik a b]
    group
  have hC : steinbergX hij a * steinbergX (Ne.symm hik) c * (steinbergX hij a)⁻¹
      = (steinbergX (Ne.symm hjk) (c * a))⁻¹ * steinbergX (Ne.symm hik) c := by
    rw [steinbergX_move_left hij (Ne.symm hik) (Ne.symm hjk) a c]
    group
  rw [← hchain, ← hB, ← hC]
  group

end GaloisForLFunctions.HTGeometry

end
