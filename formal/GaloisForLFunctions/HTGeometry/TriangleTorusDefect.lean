import GaloisForLFunctions.HTGeometry.TriangleTorusWeights
import GaloisForLFunctions.HTGeometry.DennisSteinIndexTransport

/-!
# The torus defect of a triangle

The three tori of a triple of indices satisfy, on the matrix side,

```text
diag(v, 1, v⁻¹) · diag(1, v⁻¹, v) = diag(v, v⁻¹, 1) ,
```

that is `d_ik(v) · d_kj(v) = d_ij(v)`: the middle index cancels.  In the Steinberg group the
corresponding product need not be equal, and the discrepancy

```text
δ(v) = h_ik(v) · h_kj(v) · h_ij(v)⁻¹
```

lies in `K₂`.  This is the defect that survives when both tori of the triangle normal form are
pushed to the right and compared with the torus of the `(i,j)` Bruhat decomposition.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The middle index cancels in the product of two diagonal matrices of a triangle.** -/
theorem diagMatrix_mul_triangle {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) :
    (diagMatrix i k v : Matrix n n R) * diagMatrix k j v = diagMatrix i j v := by
  have hcv : (((v⁻¹ : Rˣ)) : R) * (v : R) = 1 := v.inv_mul
  have hkj : k ≠ j := Ne.symm hjk
  have e1 : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single k k 1 = 0 := by
    simp [hik]
  have e2 : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single j j 1 = 0 := by
    simp [hij]
  have e3 : (Matrix.single k k (1 : R) : Matrix n n R) * Matrix.single k k 1
      = Matrix.single k k 1 := by simp
  have e4 : (Matrix.single k k (1 : R) : Matrix n n R) * Matrix.single j j 1 = 0 := by
    simp [hkj]
  simp only [diagMatrix]
  rw [single_eq_smul i i ((v : R) - 1), single_eq_smul k k ((((v⁻¹ : Rˣ)) : R) - 1),
    single_eq_smul k k ((v : R) - 1), single_eq_smul j j ((((v⁻¹ : Rˣ)) : R) - 1)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, e1, e2, e3, e4, smul_zero, add_zero]
  match_scalars
  all_goals ring_nf
  all_goals linear_combination hcv

/-- The defect of the triangle of tori. -/
def torusTriangleDefect {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : Rˣ) :
    SteinbergGroup R n :=
  steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v * (steinbergTorus hij v)⁻¹

/-- **The torus defect lies in `K₂`.** -/
theorem torusTriangleDefect_mem_KTwo {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (v : Rˣ) : torusTriangleDefect hij hjk hik v ∈ KTwo R n := by
  rw [mem_KTwo_iff, torusTriangleDefect, map_mul, map_mul, map_inv,
    steinbergToGL_torus, steinbergToGL_torus, steinbergToGL_torus]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_one]
  have hval : ((diagUnit hik v : (Matrix n n R)ˣ) : Matrix n n R)
      * ((diagUnit (Ne.symm hjk) v : (Matrix n n R)ˣ) : Matrix n n R)
      = ((diagUnit hij v : (Matrix n n R)ˣ) : Matrix n n R) := by
    exact diagMatrix_mul_triangle hij hjk hik v
  rw [Units.val_mul, hval, Units.mul_inv]

/-- **The three-index relation with the correction in normal form.**  The correction is a single
unipotent word followed by the torus defect, which lies in `K₂`. -/
theorem dennisStein_triangle_relation_normal {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    dennisStein hij a (b * c) v
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * ((steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
          * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
          * torusTriangleDefect hij hjk hik v) := by
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
  have hinv : (steinbergX hij (((((v⁻¹ : Rˣ))) : R) * a))⁻¹ = steinbergX hij (-(((((v⁻¹ : Rˣ))) : R) * a)) :=
    (steinbergX_neg _ _).symm
  have hinner : (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * triangleRemainder hij hjk hik a b c v
        * (steinbergX hij (((((v⁻¹ : Rˣ))) : R) * a))⁻¹
        * (steinbergTorus hij v)⁻¹
      = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
        * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
        * torusTriangleDefect hij hjk hik v := by
    rw [triangleRemainder_unipotent_torus hij hjk hik a b c v, hinv, torusTriangleDefect]
    calc (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R)))
            * steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v)
          * steinbergX hij (-(((((v⁻¹ : Rˣ))) : R) * a))
          * (steinbergTorus hij v)⁻¹
        = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
          * steinbergTorus hik v
          * (steinbergTorus (Ne.symm hjk) v * steinbergX hij (-(((((v⁻¹ : Rˣ))) : R) * a)))
          * (steinbergTorus hij v)⁻¹ := by group
      _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
          * (steinbergTorus hik v * steinbergX hij (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
          * steinbergTorus (Ne.symm hjk) v
          * (steinbergTorus hij v)⁻¹ := by
          rw [q5]
          group
      _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
        * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
        * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
        * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
        * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
        * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
          * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
          * (steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v
            * (steinbergTorus hij v)⁻¹) := by
          rw [q6]
          group
  rw [dennisStein_triangle_relation hij hjk hik a b c v hv, hinner]

/-- **The three-index relation with the two diagonal generators merged.**  The last generator of the
remainder and the one produced by moving the outer factor through the tori are both `x_ij`, and their
parameters add to `a² b c v` — the `v - 1 = abc` of the unit is what collapses them. -/
theorem dennisStein_triangle_relation_merged {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    dennisStein hij a (b * c) v
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * ((steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
          * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
          * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
          * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
          * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R)))
          * steinbergX hij (a * a * (b * c) * ((v : Rˣ) : R))
          * torusTriangleDefect hij hjk hik v) := by
  have hcv : ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R) = 1 := v.inv_mul
  have hcoef : ((v : Rˣ) : R) * (a * ((v : Rˣ) : R)) + ((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)) = a * a * (b * c) * ((v : Rˣ) : R) := by
    linear_combination (-(a * ((v : Rˣ) : R))) * hcv + (a * ((v : Rˣ) : R)) * hv
  have hmerge : steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))) * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
      = steinbergX hij (a * a * (b * c) * ((v : Rˣ) : R)) := by
    rw [steinbergX_mul, hcoef]
  rw [dennisStein_triangle_relation_normal hij hjk hik a b c v hv]
  congr 1
  calc (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
          * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
          * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
          * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
          * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R))))
        * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R)))
        * torusTriangleDefect hij hjk hik v
      = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
          * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
          * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
          * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
          * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R)))
        * (steinbergX hij (((v : Rˣ) : R) * (a * ((v : Rˣ) : R)))
          * steinbergX hij (((v : Rˣ) : R) * (-(((((v⁻¹ : Rˣ))) : R) * a) * ((v : Rˣ) : R))))
        * torusTriangleDefect hij hjk hik v := by group
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * (steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hik (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R))
          * steinbergX hij (((v : Rˣ) : R) * -((a * b) * (c * a)))
          * steinbergX hjk (-b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R))
          * steinbergX (Ne.symm hjk) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)))
          * steinbergX (Ne.symm hik) (((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R)))
        * steinbergX hij (a * a * (b * c) * ((v : Rˣ) : R))
        * torusTriangleDefect hij hjk hik v := by rw [hmerge]

/-- **The three-index relation, fully simplified.**  Every coefficient of the correction is a
monomial: the unit `v` enters only through `v - 1 = abc`. -/
theorem dennisStein_triangle_relation_simplified {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    dennisStein hij a (b * c) v
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * ((steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
          * steinbergX hjk b
          * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))
          * steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R)))
          * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R)))
          * steinbergX hjk (-b)
          * steinbergX (Ne.symm hjk) (a * a * b * c * c)
          * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R)))
          * steinbergX hij (a * a * b * c * ((v : Rˣ) : R))
          * torusTriangleDefect hij hjk hik v) := by
  have hcv : ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R) = 1 := v.inv_mul
  rw [dennisStein_triangle_relation_merged hij hjk hik a b c v hv,
    show ((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * (a * b) - a * b) * ((v : Rˣ) : R) = -(a * a * b * b * c * ((v : Rˣ) : R)) from by
      linear_combination (a * b * ((v : Rˣ) : R)) * hcv - (a * b * ((v : Rˣ) : R)) * hv,
    show ((v : Rˣ) : R) * -((a * b) * (c * a)) = -(a * a * b * c * ((v : Rˣ) : R)) from by ring,
    show -b * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R) = -b from by linear_combination (-b) * hcv,
    show ((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * (((((v⁻¹ : Rˣ))) : R) * -(c * a) + c * a) * ((v : Rˣ) : R)) = a * a * b * c * c from by
      linear_combination (-(a * c * ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R)) - a * c + a * c * ((v : Rˣ) : R)) * hcv + (a * c) * hv,
    show ((((v⁻¹ : Rˣ))) : R) * (((v : Rˣ) : R) * -c) * ((((v⁻¹ : Rˣ))) : R) = -(c * ((((v⁻¹ : Rˣ))) : R)) from by
      linear_combination (-(c * ((((v⁻¹ : Rˣ))) : R))) * hcv,
    show a * a * (b * c) * ((v : Rˣ) : R) = a * a * b * c * ((v : Rˣ) : R) from by ring]
  group

omit [DecidableEq n] [Fintype n] in
/-- **The unipotent correction of the three-index relation is trivial.**  Three pairs of generators
cancel: the two `x_ik` because `a²bcv · b = a²b²cv`, the two `x_ji` because `(bc)v⁻¹ = b(cv⁻¹)`, and
the two `x_kj` because `(cv⁻¹)(a²bcv) = a²bc²`.  Everything else pairs off directly. -/
theorem triangleCorrection_eq_one {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) :
    (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
      * steinbergX hjk b * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hjk (-b) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) = 1 := by
  have hcv : ((((v⁻¹ : Rˣ))) : R) * ((v : Rˣ) : R) = 1 := v.inv_mul
  have hAinv : (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ = steinbergX (Ne.symm hij) (-((b * c) * ((((v⁻¹ : Rˣ))) : R))) := (steinbergX_neg _ _).symm
  have m1 : steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hjk (-b) = steinbergX hik ((-(a * a * b * c * ((v : Rˣ) : R))) * (-b)) * steinbergX hjk (-b) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) :=
    steinbergX_move_right hij hjk hik (-(a * a * b * c * ((v : Rˣ) : R))) (-b)
  have m2 : steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * steinbergX hik ((-(a * a * b * c * ((v : Rˣ) : R))) * (-b)) = 1 := by
    rw [steinbergX_mul, show -(a * a * b * b * c * ((v : Rˣ) : R)) + ((-(a * a * b * c * ((v : Rˣ) : R))) * (-b)) = 0 from by ring,
      steinbergX_zero]
  have m3 : steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hjk (-b) = (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ * steinbergX hjk (-b) * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) :=
    steinbergX_move_left (Ne.symm hik) hjk (Ne.symm hij) (c * ((((v⁻¹ : Rˣ))) : R)) (-b)
  have m4 : steinbergX hjk b * (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ = (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ * steinbergX hjk b := by
    rw [← steinbergX_neg]
    exact steinbergX_commute_row hjk (Ne.symm hij) b (-((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))
  have m5 : steinbergX (Ne.symm hij) (-((b * c) * ((((v⁻¹ : Rˣ))) : R))) * (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ = 1 := by
    rw [← steinbergX_neg, steinbergX_mul,
      show -((b * c) * ((((v⁻¹ : Rˣ))) : R)) + -((-b) * (c * ((((v⁻¹ : Rˣ))) : R))) = 0 from by ring, steinbergX_zero]
  have m6 : steinbergX hjk b * steinbergX hjk (-b) = 1 := by
    rw [steinbergX_mul, show b + -b = 0 from by ring, steinbergX_zero]
  have m7 : steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) = steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) :=
    steinbergX_commute_row (Ne.symm hjk) (Ne.symm hik) (a * a * b * c * c) (-(c * ((((v⁻¹ : Rˣ))) : R)))
  have m8 : steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) = (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) :=
    steinbergX_move_left hij (Ne.symm hik) (Ne.symm hjk) (-(a * a * b * c * ((v : Rˣ) : R))) (-(c * ((((v⁻¹ : Rˣ))) : R)))
  have m9 : steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ = (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) := by
    rw [← steinbergX_neg]
    exact steinbergX_commute_row (Ne.symm hik) (Ne.symm hjk) (c * ((((v⁻¹ : Rˣ))) : R)) (-((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))
  have m10 : steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) = 1 := by
    rw [steinbergX_mul, show c * ((((v⁻¹ : Rˣ))) : R) + -(c * ((((v⁻¹ : Rˣ))) : R)) = 0 from by ring, steinbergX_zero]
  have m11 : steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) = steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) :=
    steinbergX_commute_col hij (Ne.symm hjk) (-(a * a * b * c * ((v : Rˣ) : R))) (a * a * b * c * c)
  have m12 : steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) = 1 := by
    rw [steinbergX_mul, show -(a * a * b * c * ((v : Rˣ) : R)) + a * a * b * c * ((v : Rˣ) : R) = 0 from by ring,
      steinbergX_zero]
  have m13 : (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hjk) (a * a * b * c * c) = 1 := by
    rw [← steinbergX_neg, steinbergX_mul,
      show -((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))) + a * a * b * c * c = 0 from by linear_combination (-(a * a * b * c * c)) * hcv,
      steinbergX_zero]
  calc (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹
        * steinbergX hjk b * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hjk (-b) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R))
      = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * steinbergX hjk b * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * (steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hjk (-b)) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by group
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * steinbergX hjk b * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * (steinbergX hik ((-(a * a * b * c * ((v : Rˣ) : R))) * (-b)) * steinbergX hjk (-b) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R)))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [m1]
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * steinbergX hjk b * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * (steinbergX hik (-(a * a * b * b * c * ((v : Rˣ) : R))) * steinbergX hik ((-(a * a * b * c * ((v : Rˣ) : R))) * (-b))) * steinbergX hjk (-b) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        group
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * steinbergX hjk b * (steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hjk (-b)) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [m2]
        group
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * steinbergX hjk b * ((steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ * steinbergX hjk (-b) * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by rw [m3]
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * (steinbergX hjk b * (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹) * steinbergX hjk (-b) * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by group
    _ = (steinbergX (Ne.symm hij) ((b * c) * ((((v⁻¹ : Rˣ))) : R)))⁻¹ * ((steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹ * steinbergX hjk b) * steinbergX hjk (-b) * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by rw [m4]
    _ = (steinbergX (Ne.symm hij) (-((b * c) * ((((v⁻¹ : Rˣ))) : R))) * (steinbergX (Ne.symm hij) ((-b) * (c * ((((v⁻¹ : Rˣ))) : R))))⁻¹) * (steinbergX hjk b * steinbergX hjk (-b)) * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [hAinv]
        group
    _ = steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * (steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R)))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [m5, m6]
        group
    _ = steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * (steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R)))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [m7]
        group
    _ = steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * ((steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R)))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by rw [m8]
    _ = (steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by group
    _ = ((steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R))) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by rw [m9]
    _ = (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * (steinbergX (Ne.symm hik) (c * ((((v⁻¹ : Rˣ))) : R)) * steinbergX (Ne.symm hik) (-(c * ((((v⁻¹ : Rˣ))) : R)))) * (steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX (Ne.symm hjk) (a * a * b * c * c)) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by group
    _ = (steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * (steinbergX (Ne.symm hjk) (a * a * b * c * c) * steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R)))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R)) := by
        rw [m10, m11]
        group
    _ = ((steinbergX (Ne.symm hjk) ((-(c * ((((v⁻¹ : Rˣ))) : R))) * (-(a * a * b * c * ((v : Rˣ) : R)))))⁻¹ * steinbergX (Ne.symm hjk) (a * a * b * c * c)) * (steinbergX hij (-(a * a * b * c * ((v : Rˣ) : R))) * steinbergX hij (a * a * b * c * ((v : Rˣ) : R))) := by group
    _ = 1 := by
        rw [m12, m13]
        group

/-- **The three-index Dennis–Stein relation.**  For every unit `v` with `v = 1 + abc`,

```text
⟨a, bc⟩_ij = ⟨ab, c⟩_ik · ⟨-ca, -b⟩_kj · h_ik(v) h_kj(v) h_ij(v)⁻¹ .
```

The entire unipotent part of the correction cancels; what is left is the torus defect, which lies in
`K₂`.  This is `(D3)` in the normalisation of this tree. -/
theorem dennisStein_triangle {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b c : R) (v : Rˣ) (hv : (v : R) = 1 + a * b * c) :
    dennisStein hij a (b * c) v
      = dennisStein hik (a * b) c v * dennisStein (Ne.symm hjk) (-(c * a)) (-b) v
        * torusTriangleDefect hij hjk hik v := by
  rw [dennisStein_triangle_relation_simplified hij hjk hik a b c v hv,
    triangleCorrection_eq_one hij hjk hik a b c v, one_mul]

/-- The torus correction attached to one transport of a Dennis–Stein symbol. -/
def transportCorrection {i j : n} (hij : i ≠ j) (v : Rˣ) : SteinbergGroup R n :=
  steinbergTorus hij (-v) * (steinbergTorus hij (-1))⁻¹ * (steinbergTorus hij v)⁻¹

/-- **A symbol with second argument `1` is a product of torus elements.**  Specialising the
three-index relation at `c = 1` expresses `⟨ab, 1⟩` through the same symbol `⟨a,b⟩` read in two other
index pairs; transporting those back and cancelling leaves only tori. -/
theorem dennisStein_right_one_eq_torus {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hik (a * b) 1 v
      = (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
          * transportCorrection (Ne.symm hjk) v * torusTriangleDefect hij hjk hik v)⁻¹ := by
  have hv1 : (v : R) = 1 + a * b * 1 := by rw [hv]; ring
  have hv2 : (v : R) = 1 + (-a) * (-b) := by rw [hv]; ring
  have hvab : (v : R) = 1 + (a * b) * 1 := by rw [hv]; ring
  have hd3 := dennisStein_triangle hij hjk hik a b 1 v hv1
  rw [show (b * 1 : R) = b from by ring, show (-(1 * a) : R) = -a from by ring] at hd3
  have hr1 := dennisStein_index_reversal hij hik hjk a b v hv
  have ht2 := dennisStein_index_transport (Ne.symm hij) hjk hik (-a) (-b) v hv2
  rw [neg_neg, neg_neg] at ht2
  have hr3 := dennisStein_index_reversal hjk (Ne.symm hij) (Ne.symm hik) a b v hv
  have e1 : dennisStein (Ne.symm hij) (-a) (-b) v
      = dennisStein hij a b v * transportCorrection (Ne.symm hij) v := by
    rw [transportCorrection]
    calc dennisStein (Ne.symm hij) (-a) (-b) v
        = dennisStein (Ne.symm hij) (-a) (-b) v * steinbergTorus (Ne.symm hij) v
          * (steinbergTorus (Ne.symm hij) v)⁻¹ := by group
      _ = dennisStein hij a b v
          * (steinbergTorus (Ne.symm hij) (-v) * (steinbergTorus (Ne.symm hij) (-1))⁻¹)
          * (steinbergTorus (Ne.symm hij) v)⁻¹ := by rw [← hr1]
      _ = dennisStein hij a b v
          * (steinbergTorus (Ne.symm hij) (-v) * (steinbergTorus (Ne.symm hij) (-1))⁻¹
            * (steinbergTorus (Ne.symm hij) v)⁻¹) := by group
  have e2 : dennisStein hjk a b v
      = dennisStein (Ne.symm hij) (-a) (-b) v * transportCorrection hjk v := by
    rw [transportCorrection]
    calc dennisStein hjk a b v
        = dennisStein hjk a b v * steinbergTorus hjk v * (steinbergTorus hjk v)⁻¹ := by group
      _ = dennisStein (Ne.symm hij) (-a) (-b) v
          * (steinbergTorus hjk (-v) * (steinbergTorus hjk (-1))⁻¹)
          * (steinbergTorus hjk v)⁻¹ := by rw [← ht2]
      _ = dennisStein (Ne.symm hij) (-a) (-b) v
          * (steinbergTorus hjk (-v) * (steinbergTorus hjk (-1))⁻¹
            * (steinbergTorus hjk v)⁻¹) := by group
  have e3 : dennisStein (Ne.symm hjk) (-a) (-b) v
      = dennisStein hjk a b v * transportCorrection (Ne.symm hjk) v := by
    rw [transportCorrection]
    calc dennisStein (Ne.symm hjk) (-a) (-b) v
        = dennisStein (Ne.symm hjk) (-a) (-b) v * steinbergTorus (Ne.symm hjk) v
          * (steinbergTorus (Ne.symm hjk) v)⁻¹ := by group
      _ = dennisStein hjk a b v
          * (steinbergTorus (Ne.symm hjk) (-v) * (steinbergTorus (Ne.symm hjk) (-1))⁻¹)
          * (steinbergTorus (Ne.symm hjk) v)⁻¹ := by rw [← hr3]
      _ = dennisStein hjk a b v
          * (steinbergTorus (Ne.symm hjk) (-v) * (steinbergTorus (Ne.symm hjk) (-1))⁻¹
            * (steinbergTorus (Ne.symm hjk) v)⁻¹) := by group
  rw [e3, e2, e1] at hd3
  have hDc := Subgroup.mem_center_iff.1
    (dennisStein_mem_center hij a b v hv (Ne.symm hik) (Ne.symm hjk))
  have hflat : dennisStein hij a b v
      = dennisStein hij a b v * (dennisStein hik (a * b) 1 v
        * (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
          * transportCorrection (Ne.symm hjk) v * torusTriangleDefect hij hjk hik v)) := by
    calc dennisStein hij a b v
        = dennisStein hik (a * b) 1 v
          * (dennisStein hij a b v * transportCorrection (Ne.symm hij) v
            * transportCorrection hjk v * transportCorrection (Ne.symm hjk) v)
          * torusTriangleDefect hij hjk hik v := hd3
      _ = (dennisStein hik (a * b) 1 v * dennisStein hij a b v)
          * (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
            * transportCorrection (Ne.symm hjk) v * torusTriangleDefect hij hjk hik v) := by
          group
      _ = (dennisStein hij a b v * dennisStein hik (a * b) 1 v)
          * (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
            * transportCorrection (Ne.symm hjk) v * torusTriangleDefect hij hjk hik v) := by
          rw [hDc (dennisStein hik (a * b) 1 v)]
      _ = dennisStein hij a b v * (dennisStein hik (a * b) 1 v
          * (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
            * transportCorrection (Ne.symm hjk) v
            * torusTriangleDefect hij hjk hik v)) := by group
  have hone : dennisStein hik (a * b) 1 v
      * (transportCorrection (Ne.symm hij) v * transportCorrection hjk v
        * transportCorrection (Ne.symm hjk) v * torusTriangleDefect hij hjk hik v) = 1 := by
    refine (mul_left_cancel (a := dennisStein hij a b v) ?_).symm
    rw [mul_one]
    exact hflat
  rw [eq_inv_iff_mul_eq_one]
  exact hone

omit [DecidableEq n] [Fintype n] in
/-- **The transport correction is a Steinberg symbol.**  Writing `h(-v) = {-1, v} h(v) h(-1)` the
two torus factors cancel and only the symbol survives. -/
theorem transportCorrection_eq_steinbergSymbol {i j : n} (hij : i ≠ j) (v : Rˣ) :
    transportCorrection hij v = steinbergSymbol hij (-1) v := by
  have h := steinbergTorus_mul hij (-1 : Rˣ) v
  rw [show ((-1 : Rˣ) * v) = -v from by simp] at h
  rw [transportCorrection, h]
  group

/-- **A symbol with second argument `1`, through Steinberg symbols.**  The three transport
corrections are the symbols `{-1, v}` of the three index pairs. -/
theorem dennisStein_right_one_eq_symbols {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hik (a * b) 1 v
      = (steinbergSymbol (Ne.symm hij) (-1) v * steinbergSymbol hjk (-1) v
          * steinbergSymbol (Ne.symm hjk) (-1) v * torusTriangleDefect hij hjk hik v)⁻¹ := by
  rw [← transportCorrection_eq_steinbergSymbol (Ne.symm hij) v,
    ← transportCorrection_eq_steinbergSymbol hjk v,
    ← transportCorrection_eq_steinbergSymbol (Ne.symm hjk) v]
  exact dennisStein_right_one_eq_torus hij hjk hik a b v hv

end GaloisForLFunctions.HTGeometry

end
