import GaloisForLFunctions.HTGeometry.SteinbergTriangleNormalForm

/-!
# Torus weights of the other two pairs of a triangle

The six weights of `h_ij(u)` on the root subgroups of a triple `i, j, k` are already available.
Relabelling them gives the weights of the tori of the two *other* pairs, `h_ik` and `h_kj`, on all
six root subgroups.  Writing `d` for the diagonal the torus represents, every weight is the same
rule `x_pq(s) ↦ x_pq(d_p s d_q⁻¹)`:

```text
h_ik(v) :  d_i = v ,  d_k = v⁻¹ ,  d_j = 1 ,
h_kj(v) :  d_k = v ,  d_j = v⁻¹ ,  d_i = 1 .
```

These are the moves that push a torus factor through a word in the triangle, which is what putting a
word of the Steinberg group of rank two into normal form requires.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
variable {i j k : n}

/-! ## The torus of the pair `(i,k)` -/

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_ik (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (a : R) :
    steinbergTorus hik v * steinbergX hik a * (steinbergTorus hik v)⁻¹
      = steinbergX hik (((v : Rˣ) : R) * a * ((v : Rˣ) : R)) :=
  steinbergTorus_conj_self hik hij (Ne.symm hjk) v a

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_ij (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (a : R) :
    steinbergTorus hik v * steinbergX hij a * (steinbergTorus hik v)⁻¹
      = steinbergX hij (((v : Rˣ) : R) * a) :=
  steinbergTorus_conj_first hik hij (Ne.symm hjk) v a

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_ji (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (d : R) :
    steinbergTorus hik v * steinbergX (Ne.symm hij) d * (steinbergTorus hik v)⁻¹
      = steinbergX (Ne.symm hij) (d * (((v⁻¹ : Rˣ)) : R)) :=
  steinbergTorus_conj_col hik hij (Ne.symm hjk) v d

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_kj (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (c : R) :
    steinbergTorus hik v * steinbergX (Ne.symm hjk) c * (steinbergTorus hik v)⁻¹
      = steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * c) :=
  steinbergTorus_conj_row hik hij (Ne.symm hjk) v c

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_jk (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (b : R) :
    steinbergTorus hik v * steinbergX hjk b * (steinbergTorus hik v)⁻¹
      = steinbergX hjk (b * ((v : Rˣ) : R)) :=
  steinbergTorus_conj_second hik hij (Ne.symm hjk) v b

omit [DecidableEq n] [Fintype n] in
theorem torus_ik_conj_ki (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (b : R) :
    steinbergTorus hik v * steinbergX (Ne.symm hik) b * (steinbergTorus hik v)⁻¹
      = steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * b * (((v⁻¹ : Rˣ)) : R)) :=
  steinbergTorus_conj_transpose hik hij (Ne.symm hjk) v b

/-! ## The torus of the pair `(k,j)` -/

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_kj (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (a : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hjk) a
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX (Ne.symm hjk) (((v : Rˣ) : R) * a * ((v : Rˣ) : R)) :=
  steinbergTorus_conj_self (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v a

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_ki (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (a : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hik) a
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX (Ne.symm hik) (((v : Rˣ) : R) * a) :=
  steinbergTorus_conj_first (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v a

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_ik (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (d : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX hik d
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX hik (d * (((v⁻¹ : Rˣ)) : R)) :=
  steinbergTorus_conj_col (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v d

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_ji (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (c : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hij) c
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX (Ne.symm hij) ((((v⁻¹ : Rˣ)) : R) * c) :=
  steinbergTorus_conj_row (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v c

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_ij (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (b : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX hij b
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX hij (b * ((v : Rˣ) : R)) :=
  steinbergTorus_conj_second (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v b

omit [DecidableEq n] [Fintype n] in
theorem torus_kj_conj_jk (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) (b : R) :
    steinbergTorus (Ne.symm hjk) v * steinbergX hjk b
        * (steinbergTorus (Ne.symm hjk) v)⁻¹
      = steinbergX hjk ((((v⁻¹ : Rˣ)) : R) * b * (((v⁻¹ : Rˣ)) : R)) :=
  steinbergTorus_conj_transpose (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij) v b

/-! ## Pushing the first torus through the triangle remainder -/

omit [DecidableEq n] [Fintype n] in
/-- **The `(i,k)` torus moves to the right through the three generators that follow it** in the
triangle remainder, picking up its weight on each. -/
theorem triangleRemainder_push_ik (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) :
    triangleRemainder hij hjk hik a b c v
      = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergTorus hik v
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by
  have p1 : ∀ s : R, steinbergTorus hik v * steinbergX hik s
      = steinbergX hik (((v : Rˣ) : R) * s * ((v : Rˣ) : R)) * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_ik hij hjk hik v s]
    group
  have p2 : ∀ s : R, steinbergTorus hik v * steinbergX hij s
      = steinbergX hij (((v : Rˣ) : R) * s) * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_ij hij hjk hik v s]
    group
  have p3 : ∀ s : R, steinbergTorus hik v * steinbergX hjk s
      = steinbergX hjk (s * ((v : Rˣ) : R)) * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_jk hij hjk hik v s]
    group
  rw [triangleRemainder]
  calc steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus hik v
        * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b)
        * steinbergX hij (-((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a
      = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * (steinbergTorus hik v
          * steinbergX hik ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b))
        * steinbergX hij (-((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * (steinbergTorus hik v * steinbergX hij (-((a * b) * (c * a))))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by
        rw [p1]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * (steinbergTorus hik v * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R)))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by
        rw [p2]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergTorus hik v
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by
        rw [p3]
        group

omit [DecidableEq n] [Fintype n] in
/-- **The triangle remainder is a unipotent word followed by the two tori.**  Both tori are pushed
all the way to the right, each generator picking up the product of the two weights. -/
theorem triangleRemainder_unipotent_torus (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) :
    triangleRemainder hij hjk hik a b c v
      = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * (((v : Rˣ) : R) * -c)
            * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R)))
        * steinbergTorus hik v
        * steinbergTorus (Ne.symm hjk) v := by
  have q1 : ∀ s : R, steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hjk) s
      = steinbergX (Ne.symm hjk) (((v : Rˣ) : R) * s * ((v : Rˣ) : R))
        * steinbergTorus (Ne.symm hjk) v := by
    intro s
    rw [← torus_kj_conj_kj hij hjk hik v s]
    group
  have q2 : ∀ s : R, steinbergTorus hik v * steinbergX (Ne.symm hjk) s
      = steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * s) * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_kj hij hjk hik v s]
    group
  have q3 : ∀ s : R, steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hik) s
      = steinbergX (Ne.symm hik) (((v : Rˣ) : R) * s) * steinbergTorus (Ne.symm hjk) v := by
    intro s
    rw [← torus_kj_conj_ki hij hjk hik v s]
    group
  have q4 : ∀ s : R, steinbergTorus hik v * steinbergX (Ne.symm hik) s
      = steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * s * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_ki hij hjk hik v s]
    group
  have q5 : ∀ s : R, steinbergTorus (Ne.symm hjk) v * steinbergX hij s
      = steinbergX hij (s * ((v : Rˣ) : R)) * steinbergTorus (Ne.symm hjk) v := by
    intro s
    rw [← torus_kj_conj_ij hij hjk hik v s]
    group
  have q6 : ∀ s : R, steinbergTorus hik v * steinbergX hij s
      = steinbergX hij (((v : Rˣ) : R) * s) * steinbergTorus hik v := by
    intro s
    rw [← torus_ik_conj_ij hij hjk hik v s]
    group
  rw [triangleRemainder_push_ik hij hjk hik a b c v]
  calc steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergTorus hik v
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a)
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a
      = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergTorus hik v
        * (steinbergTorus (Ne.symm hjk) v
          * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a))
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * (steinbergTorus hik v
          * steinbergX (Ne.symm hjk) (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX (Ne.symm hik) (-c)
        * steinbergX hij a := by
        rw [q1]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergTorus hik v
        * (steinbergTorus (Ne.symm hjk) v * steinbergX (Ne.symm hik) (-c))
        * steinbergX hij a := by
        rw [q2]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * (steinbergTorus hik v * steinbergX (Ne.symm hik) (((v : Rˣ) : R) * -c))
        * steinbergTorus (Ne.symm hjk) v
        * steinbergX hij a := by
        rw [q3]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * (((v : Rˣ) : R) * -c)
            * (((v⁻¹ : Rˣ)) : R))
        * steinbergTorus hik v
        * (steinbergTorus (Ne.symm hjk) v * steinbergX hij a) := by
        rw [q4]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * (((v : Rˣ) : R) * -c)
            * (((v⁻¹ : Rˣ)) : R))
        * (steinbergTorus hik v * steinbergX hij (a * ((v : Rˣ) : R)))
        * steinbergTorus (Ne.symm hjk) v := by
        rw [q5]
        group
    _ = steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hik (((v : Rˣ) : R)
            * ((((v⁻¹ : Rˣ)) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * (((v⁻¹ : Rˣ)) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) ((((v⁻¹ : Rˣ)) : R)
            * (((v : Rˣ) : R) * ((((v⁻¹ : Rˣ)) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) ((((v⁻¹ : Rˣ)) : R) * (((v : Rˣ) : R) * -c)
            * (((v⁻¹ : Rˣ)) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R)))
        * steinbergTorus hik v
        * steinbergTorus (Ne.symm hjk) v := by
        rw [q6]
        group

end GaloisForLFunctions.HTGeometry

end
