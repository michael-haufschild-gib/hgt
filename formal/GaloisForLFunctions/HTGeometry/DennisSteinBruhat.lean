import GaloisForLFunctions.HTGeometry.DennisSteinSymbol

/-!
# Bruhat decomposition in the Steinberg group, and its obstruction

Over a field the product of two opposite elementary matrices factors as

```text
⎡1  a⎤ ⎡1  0⎤     ⎡ 1    0⎤ ⎡w  0  ⎤ ⎡1  a/w⎤
⎣0  1⎦ ⎣b  1⎦  =  ⎣ b/w  1⎦ ⎣0  1/w⎦ ⎣0   1 ⎦ ,        w = 1 + ab ,
```

the Bruhat decomposition of the big cell.  The same factorisation is attempted in the Steinberg
group, where the three factors are `x_ji(bw⁻¹)`, `h_ij(w)` and `x_ij(w⁻¹a)`.  It fails, and the
failure is exactly the Dennis–Stein symbol:

```text
x_ij(a) x_ji(b) = x_ji(b w⁻¹) · ⟨a,b⟩ · h_ij(w) · x_ij(w⁻¹ a) .
```

Since `⟨a,b⟩ ∈ K₂`, the decomposition holds on the nose in the elementary group and only in the
Steinberg group does the central correction appear.  This is the form in which the symbol enters
Matsumoto's presentation.

Specialising to `ab = 0`, where `w = 1`, the correction is the plain commutator of the two
generators, and the statement becomes: opposite elementary generators with vanishing product
commute modulo `K₂`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- The Dennis–Stein symbol times the torus element is the four-fold elementary product. -/
theorem dennisStein_mul_torus {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ) :
    dennisStein hij a b w * steinbergTorus hij w
      = steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R)))
        * steinbergX hij a
        * steinbergX (Ne.symm hij) b
        * steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a)) := by
  rw [dennisStein]
  group

omit [DecidableEq n] [Fintype n] in
/-- **Bruhat decomposition in the Steinberg group.**  The product of two opposite elementary
generators factors through the torus, with the Dennis–Stein symbol as the exact obstruction. -/
theorem steinbergX_mul_opposite {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ) :
    steinbergX hij a * steinbergX (Ne.symm hij) b
      = steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
        * (dennisStein hij a b w * steinbergTorus hij w)
        * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a) := by
  rw [dennisStein_mul_torus]
  rw [show steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
        * (steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R)))
          * steinbergX hij a * steinbergX (Ne.symm hij) b
          * steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a)))
        * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)
      = (steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
          * steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R))))
        * steinbergX hij a * steinbergX (Ne.symm hij) b
        * (steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a))
          * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)) by group]
  rw [steinbergX_mul, steinbergX_mul, add_neg_cancel, neg_add_cancel,
    steinbergX_zero, steinbergX_zero, one_mul, mul_one]

/-- **The Bruhat obstruction is central**, as soon as a third index is available. -/
theorem steinbergX_mul_opposite_center {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ)
    (hw : (w : R) = 1 + a * b) {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergX hij a * steinbergX (Ne.symm hij) b
      = steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
        * steinbergTorus hij w
        * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)
        * dennisStein hij a b w := by
  have hc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b w hw hhi hhj)
  rw [steinbergX_mul_opposite hij a b w]
  rw [show steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
        * (dennisStein hij a b w * steinbergTorus hij w)
        * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)
      = steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
        * (dennisStein hij a b w * (steinbergTorus hij w
            * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a))) by group]
  rw [← hc (steinbergTorus hij w * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a))]
  group

/-! ## The degenerate cell -/

omit [DecidableEq n] [Fintype n] in
/-- With `w = 1` the symbol is the plain commutator of the two opposite generators. -/
theorem dennisStein_one {i j : n} (hij : i ≠ j) (a b : R) :
    dennisStein hij a b (1 : Rˣ)
      = (steinbergX (Ne.symm hij) b)⁻¹ * steinbergX hij a
        * steinbergX (Ne.symm hij) b * (steinbergX hij a)⁻¹ := by
  have hb : (steinbergX (Ne.symm hij) b)⁻¹ = steinbergX (Ne.symm hij) (-b) :=
    (steinbergX_neg (Ne.symm hij) b).symm
  have ha : (steinbergX hij a)⁻¹ = steinbergX hij (-a) := (steinbergX_neg hij a).symm
  rw [dennisStein, steinbergTorus_one, hb, ha]
  simp only [inv_one, Units.val_one, mul_one, one_mul]

/-- **Opposite elementary generators with vanishing product commute modulo `K₂`.** -/
theorem commutator_opposite_mem_KTwo {i j : n} (hij : i ≠ j) (a b : R) (hab : a * b = 0) :
    (steinbergX (Ne.symm hij) b)⁻¹ * steinbergX hij a
        * steinbergX (Ne.symm hij) b * (steinbergX hij a)⁻¹ ∈ KTwo R n := by
  rw [← dennisStein_one hij a b]
  refine dennisStein_mem_KTwo hij a b (1 : Rˣ) ?_
  rw [hab, Units.val_one, add_zero]

/-- **The same commutator is central**, as soon as a third index is available. -/
theorem commutator_opposite_mem_center {i j : n} (hij : i ≠ j) (a b : R) (hab : a * b = 0)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    (steinbergX (Ne.symm hij) b)⁻¹ * steinbergX hij a
        * steinbergX (Ne.symm hij) b * (steinbergX hij a)⁻¹
      ∈ Subgroup.center (SteinbergGroup R n) := by
  rw [← dennisStein_one hij a b]
  refine dennisStein_mem_center hij a b (1 : Rˣ) ?_ hhi hhj
  rw [hab, Units.val_one, add_zero]

end GaloisForLFunctions.HTGeometry

end
