import GaloisForLFunctions.HTGeometry.SteinbergChainConjugation

/-!
# Isolating the two rank-one pairs of the triangle

The commutator produced by the chain conjugation is a word in the four generators

```text
P = x_ik(ab) ,   B = x_jk(b) ,   Q = x_kj(ca) ,   C = x_ki(c) ,
```

of which two pairs commute — `P` with `B` (same column `k`) and `Q` with `C` (same row `k`).  Those
two commutations alone reorder the word so that the `(i,k)` Bruhat pair `P C` stands isolated:

```text
[P B, Q⁻¹ C] = B · (P C) · (Q⁻¹ P⁻¹) · (B⁻¹ Q) · C⁻¹ .
```

The remaining factors are the mixed pair `Q⁻¹ P⁻¹`, which the chain relation turns into an
`(i,j)`-generator, and the `(k,j)` pair `B⁻¹ Q`.  So the whole Bruhat pair `x_ij(a) x_ji(bc)` is
expressed through one `(i,k)` rank-one pair, one `(k,j)` rank-one pair, and generators — which is the
shape the three-index Dennis–Stein relation compares.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- Two commuting pairs reorder a commutator so that one cross pair stands alone. -/
theorem commutator_shuffle_of_commuting {G : Type*} [Group G] {P B Q C : G}
    (hPB : P * B = B * P) (hQC : Q * C = C * Q) :
    (P * B) * (Q⁻¹ * C) * (P * B)⁻¹ * (Q⁻¹ * C)⁻¹
      = B * (P * C) * (Q⁻¹ * P⁻¹) * (B⁻¹ * Q) * C⁻¹ := by
  have h1 : Q⁻¹ * C = C * Q⁻¹ := by
    calc Q⁻¹ * C = Q⁻¹ * (C * Q) * Q⁻¹ := by group
      _ = Q⁻¹ * (Q * C) * Q⁻¹ := by rw [← hQC]
      _ = C * Q⁻¹ := by group
  have h2 : B⁻¹ * P⁻¹ = P⁻¹ * B⁻¹ := by
    have h := congrArg (fun g : G => g⁻¹) hPB
    simpa [mul_inv_rev] using h
  have h3 : C⁻¹ * Q = Q * C⁻¹ := by
    calc C⁻¹ * Q = C⁻¹ * (Q * C) * C⁻¹ := by group
      _ = C⁻¹ * (C * Q) * C⁻¹ := by rw [hQC]
      _ = Q * C⁻¹ := by group
  calc (P * B) * (Q⁻¹ * C) * (P * B)⁻¹ * (Q⁻¹ * C)⁻¹
      = P * B * (Q⁻¹ * C) * B⁻¹ * P⁻¹ * C⁻¹ * Q := by group
    _ = P * B * (C * Q⁻¹) * B⁻¹ * P⁻¹ * C⁻¹ * Q := by rw [h1]
    _ = (P * B) * C * Q⁻¹ * (B⁻¹ * P⁻¹) * C⁻¹ * Q := by group
    _ = (B * P) * C * Q⁻¹ * (P⁻¹ * B⁻¹) * C⁻¹ * Q := by rw [hPB, h2]
    _ = B * P * C * Q⁻¹ * P⁻¹ * B⁻¹ * (C⁻¹ * Q) := by group
    _ = B * P * C * Q⁻¹ * P⁻¹ * B⁻¹ * (Q * C⁻¹) := by rw [h3]
    _ = B * (P * C) * (Q⁻¹ * P⁻¹) * (B⁻¹ * Q) * C⁻¹ := by group

omit [DecidableEq n] [Fintype n] in
/-- **The Bruhat pair with the `(i,k)` rank-one pair isolated.** -/
theorem steinbergX_mul_opposite_triangle {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) :
    steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = steinbergX hjk b
        * (steinbergX hik (a * b) * steinbergX (Ne.symm hik) c)
        * ((steinbergX (Ne.symm hjk) (c * a))⁻¹ * (steinbergX hik (a * b))⁻¹)
        * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
        * (steinbergX (Ne.symm hik) c)⁻¹
        * steinbergX hij a := by
  have hPB : steinbergX hik (a * b) * steinbergX hjk b
      = steinbergX hjk b * steinbergX hik (a * b) :=
    steinbergX_commute_col hik hjk (a * b) b
  have hQC : steinbergX (Ne.symm hjk) (c * a) * steinbergX (Ne.symm hik) c
      = steinbergX (Ne.symm hik) c * steinbergX (Ne.symm hjk) (c * a) :=
    steinbergX_commute_row (Ne.symm hjk) (Ne.symm hik) (c * a) c
  rw [steinbergX_mul_opposite_chain hij hjk hik a b c,
    commutator_shuffle_of_commuting hPB hQC]

omit [DecidableEq n] [Fintype n] in
/-- **The triangle form with the mixed pair reordered.**  The two generators of different pairs are
exchanged at the cost of the single `(i,j)`-generator the chain relation produces. -/
theorem steinbergX_mul_opposite_triangle_reordered {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) :
    steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = steinbergX hjk b
        * (steinbergX hik (a * b) * steinbergX (Ne.symm hik) c)
        * (steinbergX hik (a * b))⁻¹
        * (steinbergX (Ne.symm hjk) (c * a))⁻¹
        * (steinbergX hij ((a * b) * (c * a)))⁻¹
        * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
        * (steinbergX (Ne.symm hik) c)⁻¹
        * steinbergX hij a := by
  have hS := steinbergX_chain hik (Ne.symm hjk) hij (a * b) (c * a)
  have hQP : (steinbergX (Ne.symm hjk) (c * a))⁻¹ * (steinbergX hik (a * b))⁻¹
      = (steinbergX hik (a * b))⁻¹ * (steinbergX (Ne.symm hjk) (c * a))⁻¹
        * (steinbergX hij ((a * b) * (c * a)))⁻¹ := by
    rw [← hS]
    group
  rw [steinbergX_mul_opposite_triangle hij hjk hik a b c, hQP]
  group

/-- **The triangle form with the `(i,k)` pair decomposed.**  Replacing the isolated rank-one pair by
its Bruhat decomposition extracts the Dennis–Stein symbol `⟨ab, c⟩` of the `(i,k)` pair, which is
central and therefore comes out in front; the two `(i,k)` generators that meet then merge. -/
theorem steinbergX_mul_opposite_triangle_bruhat {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * (steinbergX (Ne.symm hjk) (c * a))⁻¹
          * (steinbergX hij ((a * b) * (c * a)))⁻¹
          * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
          * (steinbergX (Ne.symm hik) c)⁻¹
          * steinbergX hij a) := by
  have hv' : (v : R) = 1 + (a * b) * c := hv
  have hbruhat := steinbergX_mul_opposite hik (a * b) c v
  have hDc := Subgroup.mem_center_iff.1
    (dennisStein_mem_center hik (a * b) c v hv' (Ne.symm hij) hjk)
  have hmerge : steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b))
        * (steinbergX hik (a * b))⁻¹
      = steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) := by
    rw [← steinbergX_neg, steinbergX_mul]
    congr 1
    ring
  calc steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = steinbergX hjk b * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * dennisStein hik (a * b) c v * steinbergTorus hik v
        * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b))
        * (steinbergX hik (a * b))⁻¹
        * (steinbergX (Ne.symm hjk) (c * a))⁻¹
        * (steinbergX hij ((a * b) * (c * a)))⁻¹
        * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
        * (steinbergX (Ne.symm hik) c)⁻¹
        * steinbergX hij a := by
        rw [steinbergX_mul_opposite_triangle_reordered hij hjk hik a b c, hbruhat]
        group
    _ = dennisStein hik (a * b) c v
        * (steinbergX hjk b * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R)))
        * steinbergTorus hik v
        * (steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b))
          * (steinbergX hik (a * b))⁻¹)
        * (steinbergX (Ne.symm hjk) (c * a))⁻¹
        * (steinbergX hij ((a * b) * (c * a)))⁻¹
        * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
        * (steinbergX (Ne.symm hik) c)⁻¹
        * steinbergX hij a := by
        rw [hDc (steinbergX hjk b * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R)))]
        group
    _ = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * (steinbergX (Ne.symm hjk) (c * a))⁻¹
          * (steinbergX hij ((a * b) * (c * a)))⁻¹
          * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
          * (steinbergX (Ne.symm hik) c)⁻¹
          * steinbergX hij a) := by
        rw [hmerge]
        group

/-- **The triangle form with both rank-one pairs decomposed.**  The `(k,j)` pair `x_kj(-ca) x_jk(-b)`
carries the same unit `1 + abc` as the other two, so its Dennis–Stein symbol `⟨-ca, -b⟩` is defined
for the same `v`; it too is central and comes out in front, and the two `(k,j)` generators that meet
merge. -/
theorem steinbergX_mul_opposite_triangle_two_symbols {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus (Ne.symm hjk) v
          * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by
  have hv2 : (v : R) = 1 + -(c * a) * -b := by rw [hv]; ring
  have hbruhat2 := steinbergX_mul_opposite (Ne.symm hjk) (-(c * a)) (-b) v
  have hD2c := Subgroup.mem_center_iff.1
    (dennisStein_mem_center (Ne.symm hjk) (-(c * a)) (-b) v hv2 hik hij)
  have hQS : steinbergX (Ne.symm hjk) (c * a) * steinbergX hij ((a * b) * (c * a))
      = steinbergX hij ((a * b) * (c * a)) * steinbergX (Ne.symm hjk) (c * a) :=
    steinbergX_commute_col (Ne.symm hjk) hij (c * a) ((a * b) * (c * a))
  have hQSinv : (steinbergX (Ne.symm hjk) (c * a))⁻¹
        * (steinbergX hij ((a * b) * (c * a)))⁻¹
      = (steinbergX hij ((a * b) * (c * a)))⁻¹
        * (steinbergX (Ne.symm hjk) (c * a))⁻¹ := by
    have h := congrArg (fun g : SteinbergGroup R n => g⁻¹) hQS
    simpa [mul_inv_rev, ← mul_assoc] using h.symm
  have hQi : (steinbergX (Ne.symm hjk) (c * a))⁻¹
      = steinbergX (Ne.symm hjk) (-(c * a)) := (steinbergX_neg _ _).symm
  have hBi : (steinbergX hjk b)⁻¹ = steinbergX hjk (-b) := (steinbergX_neg _ _).symm
  have hSi : (steinbergX hij ((a * b) * (c * a)))⁻¹
      = steinbergX hij (-((a * b) * (c * a))) := (steinbergX_neg _ _).symm
  have hCi : (steinbergX (Ne.symm hik) c)⁻¹
      = steinbergX (Ne.symm hik) (-c) := (steinbergX_neg _ _).symm
  have hmerge2 : steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a))
        * steinbergX (Ne.symm hjk) (c * a)
      = steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) :=
    steinbergX_mul _ _ _
  calc steinbergX hij a * steinbergX (Ne.symm hij) (b * c)
      = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * ((steinbergX (Ne.symm hjk) (c * a))⁻¹
            * (steinbergX hij ((a * b) * (c * a)))⁻¹)
          * ((steinbergX hjk b)⁻¹ * steinbergX (Ne.symm hjk) (c * a))
          * (steinbergX (Ne.symm hik) c)⁻¹
          * steinbergX hij a) := by
        rw [steinbergX_mul_opposite_triangle_bruhat hij hjk hik a b c v hv]
        group
    _ = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * (steinbergX (Ne.symm hjk) (-(c * a)) * steinbergX hjk (-b))
          * steinbergX (Ne.symm hjk) (c * a)
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by
        rw [hQSinv, hQi, hBi, hSi, hCi]
        group
    _ = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * (steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
            * (dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
              * steinbergTorus (Ne.symm hjk) v)
            * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a)))
          * steinbergX (Ne.symm hjk) (c * a)
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by
        rw [hbruhat2]
    _ = dennisStein hik (a * b) c v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
          * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
          * steinbergTorus (Ne.symm hjk) v
          * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a))
          * steinbergX (Ne.symm hjk) (c * a)
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by group
    _ = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus (Ne.symm hjk) v
          * (steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a))
            * steinbergX (Ne.symm hjk) (c * a))
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by
        rw [hD2c (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R)))]
        group
    _ = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
          * steinbergX hij (-((a * b) * (c * a)))
          * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
          * steinbergTorus (Ne.symm hjk) v
          * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
          * steinbergX (Ne.symm hik) (-c)
          * steinbergX hij a) := by
        rw [hmerge2]

/-- The unipotent-and-torus remainder of the triangle normal form: everything that survives after
the two Dennis–Stein symbols have been extracted. -/
def triangleRemainder {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) : SteinbergGroup R n :=
  steinbergX hjk b
    * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
    * steinbergTorus hik v
    * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
    * steinbergX hij (-((a * b) * (c * a)))
    * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
    * steinbergTorus (Ne.symm hjk) v
    * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
    * steinbergX (Ne.symm hik) (-c)
    * steinbergX hij a

/-- **The three-index Dennis–Stein relation, in closed form.**  The symbol of the `(i,j)` pair is the
product of the symbols of the `(i,k)` and `(k,j)` pairs with an explicit correction built from the
remainder and the outer factors of the `(i,j)` Bruhat decomposition. -/
theorem dennisStein_triangle_relation {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    dennisStein hij a (b * c) v
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * ((steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R)))⁻¹
          * triangleRemainder hij hjk hik a b c v
          * (steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a))⁻¹
          * (steinbergTorus hij v)⁻¹) := by
  have hv' : (v : R) = 1 + (a * b) * c := hv
  have hv2 : (v : R) = 1 + -(c * a) * -b := by rw [hv]; ring
  have hD1c := Subgroup.mem_center_iff.1
    (dennisStein_mem_center hik (a * b) c v hv' (Ne.symm hij) hjk)
  have hD2c := Subgroup.mem_center_iff.1
    (dennisStein_mem_center (Ne.symm hjk) (-(c * a)) (-b) v hv2 hik hij)
  have hD12 : ∀ g : SteinbergGroup R n,
      g * (dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v)
        = (dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v) * g := by
    intro g
    calc g * (dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v)
        = (g * dennisStein hik (a * b) c v) * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v := by
          group
      _ = (dennisStein hik (a * b) c v * g) * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v := by
          rw [hD1c g]
      _ = dennisStein hik (a * b) c v * (g * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v) := by
          group
      _ = dennisStein hik (a * b) c v * (dennisStein (Ne.symm hjk) (-(c * a)) (-b) v * g) := by
          rw [hD2c g]
      _ = (dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v) * g := by
          group
  have heq : steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R))
        * (dennisStein hij a (b * c) v * steinbergTorus hij v)
        * steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a)
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * triangleRemainder hij hjk hik a b c v := by
    rw [← steinbergX_mul_opposite hij a (b * c) v, triangleRemainder]
    exact steinbergX_mul_opposite_triangle_two_symbols hij hjk hik a b c v hv
  calc dennisStein hij a (b * c) v
      = (steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R)))⁻¹
        * (steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R))
          * (dennisStein hij a (b * c) v * steinbergTorus hij v)
          * steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a))
        * (steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a))⁻¹
        * (steinbergTorus hij v)⁻¹ := by group
    _ = (steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R)))⁻¹
        * (dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v)
        * triangleRemainder hij hjk hik a b c v
        * (steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a))⁻¹
        * (steinbergTorus hij v)⁻¹ := by
        rw [heq]
        group
    _ = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * ((steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R)))⁻¹
          * triangleRemainder hij hjk hik a b c v
          * (steinbergX hij ((((v⁻¹ : Rˣ)) : R) * a))⁻¹
          * (steinbergTorus hij v)⁻¹) := by
        rw [hD12 ((steinbergX (Ne.symm hij) ((b * c) * (((v⁻¹ : Rˣ)) : R)))⁻¹)]
        group

end GaloisForLFunctions.HTGeometry

end
