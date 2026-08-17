import GaloisForLFunctions.HTGeometry.SteinbergSymbolCoboundary

/-!
# The torus commutator pairing is multiplicative in its second argument

Rescaling the arguments of a Dennis–Stein symbol twice, by `t₁` and then by `t₂`, has the same
effect as rescaling once by `t₁ t₂`: the symbol reached is the same, because
`t₂(t₁ a) = (t₁t₂)a` and `(b t₁⁻¹)t₂⁻¹ = b (t₁t₂)⁻¹`.  Cancelling it leaves

```text
[ h_ij(w), h_ik(t₁ t₂) ] = [ h_ij(w), h_ik(t₂) ] · [ h_ij(w), h_ik(t₁) ] .
```

No property of the tori is used beyond the scaling relation; the symbol is only a vehicle, and any
`a`, `b` with `1 + ab = w` will do — the proof takes `a = w - 1`, `b = 1`, which exists for every
unit `w`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The commutator pairing is multiplicative in the second slot.** -/
theorem torusCommutator_mul_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w t₁ t₂ : Rˣ) :
    torusCommutator hij hik w (t₁ * t₂)
      = torusCommutator hij hik w t₂ * torusCommutator hij hik w t₁ := by
  have ht₁ : ((t₁ : Rˣ) : R) * (((t₁⁻¹ : Rˣ)) : R) = 1 := t₁.mul_inv
  have hw : (w : R) = 1 + ((w : R) - 1) * 1 := by ring
  have hw' : (w : R)
      = 1 + (((t₁ : Rˣ) : R) * ((w : R) - 1)) * (1 * (((t₁⁻¹ : Rˣ)) : R)) := by
    linear_combination (-((w : R) - 1)) * ht₁
  have h1 := dennisStein_scale hij hik hjk ((w : R) - 1) 1 w (t₁ * t₂) hw
  have h2 := dennisStein_scale hij hik hjk ((w : R) - 1) 1 w t₁ hw
  have h3 := dennisStein_scale hij hik hjk (((t₁ : Rˣ) : R) * ((w : R) - 1))
    (1 * (((t₁⁻¹ : Rˣ)) : R)) w t₂ hw'
  have efst : ((t₂ : Rˣ) : R) * (((t₁ : Rˣ) : R) * ((w : R) - 1))
      = (((t₁ * t₂ : Rˣ)) : R) * ((w : R) - 1) := by
    push_cast
    ring
  have esnd : (1 * (((t₁⁻¹ : Rˣ)) : R)) * (((t₂⁻¹ : Rˣ)) : R)
      = 1 * ((((t₁ * t₂)⁻¹ : Rˣ)) : R) := by
    rw [mul_inv]
    push_cast
    ring
  rw [efst, esnd] at h3
  rw [h3] at h2
  rw [h1] at h2
  have hcancel : dennisStein hij ((((t₁ * t₂ : Rˣ)) : R) * ((w : R) - 1))
        (1 * ((((t₁ * t₂)⁻¹ : Rˣ)) : R)) w
      * torusCommutator hij hik w (t₁ * t₂)
      = dennisStein hij ((((t₁ * t₂ : Rˣ)) : R) * ((w : R) - 1))
        (1 * ((((t₁ * t₂)⁻¹ : Rˣ)) : R)) w
      * (torusCommutator hij hik w t₂ * torusCommutator hij hik w t₁) := by
    rw [torusCommutator, torusCommutator, torusCommutator]
    rw [h2]
    group
  exact mul_left_cancel hcancel

omit [DecidableEq n] [Fintype n] in
/-- The pairing is trivial at `1`. -/
theorem torusCommutator_one_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (w : Rˣ) :
    torusCommutator hij hik w 1 = 1 := by
  rw [torusCommutator, steinbergTorus_one]
  group

/-- The pairing inverts the second argument. -/
theorem torusCommutator_inv_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w t : Rˣ) :
    torusCommutator hij hik w t⁻¹ = (torusCommutator hij hik w t)⁻¹ := by
  have h := torusCommutator_mul_right hij hik hjk w t t⁻¹
  rw [mul_inv_cancel, torusCommutator_one_right hij hik w] at h
  rw [eq_inv_iff_mul_eq_one, ← h]

/-! ## The pairing lands in `K₂` -/

/-- **Two diagonal matrices of a triangle commute.**  Both products are
`1 + E_ii(wt - 1) + E_jj(w⁻¹ - 1) + E_kk(t⁻¹ - 1)`. -/
theorem diagMatrix_commute {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (w t : Rˣ) :
    (diagMatrix i j w : Matrix n n R) * diagMatrix i k t
      = diagMatrix i k t * diagMatrix i j w := by
  have hji : j ≠ i := Ne.symm hij
  have hki : k ≠ i := Ne.symm hik
  have hkj : k ≠ j := Ne.symm hjk
  have e1 : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single i i 1
      = Matrix.single i i 1 := by simp
  have e2 : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single k k 1 = 0 := by simp [hik]
  have e3 : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single i i 1 = 0 := by simp [hji]
  have e4 : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single k k 1 = 0 := by simp [hjk]
  have e5 : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single j j 1 = 0 := by simp [hij]
  have e6 : (Matrix.single k k (1 : R) : Matrix n n R) * Matrix.single i i 1 = 0 := by simp [hki]
  have e7 : (Matrix.single k k (1 : R) : Matrix n n R) * Matrix.single j j 1 = 0 := by simp [hkj]
  simp only [diagMatrix]
  rw [single_eq_smul i i ((w : R) - 1), single_eq_smul j j ((((w⁻¹ : Rˣ)) : R) - 1),
    single_eq_smul i i ((t : R) - 1), single_eq_smul k k ((((t⁻¹ : Rˣ)) : R) - 1)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, e1, e2, e3, e4, e5, e6, e7, smul_zero, add_zero]
  match_scalars <;> ring

/-- **The commutator pairing lies in `K₂`.**  Its image is a commutator of two commuting diagonal
matrices. -/
theorem torusCommutator_mem_KTwo {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w t : Rˣ) : torusCommutator hij hik w t ∈ KTwo R n := by
  have hcomm : (diagUnit hij w : (Matrix n n R)ˣ) * diagUnit hik t
      = diagUnit hik t * diagUnit hij w := Units.ext (diagMatrix_commute hij hjk hik w t)
  rw [mem_KTwo_iff, torusCommutator, map_mul, map_mul, map_mul, map_inv, map_inv,
    steinbergToGL_torus, steinbergToGL_torus, hcomm]
  group

/-- **The pairing in the first slot, up to conjugation.**  The Steinberg symbol produced by splitting
`h_ij(w₁w₂)` is central and drops out, leaving one conjugated pairing and one plain one. -/
theorem torusCommutator_mul_left {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w₁ w₂ t : Rˣ) :
    torusCommutator hij hik (w₁ * w₂) t
      = steinbergTorus hij w₂ * torusCommutator hij hik w₁ t * (steinbergTorus hij w₂)⁻¹
        * torusCommutator hij hik w₂ t := by
  have hS := steinbergTorus_mul hij w₁ w₂
  have hSc := Subgroup.mem_center_iff.1
    (steinbergSymbol_mem_center hij w₁ w₂ (Ne.symm hik) (Ne.symm hjk))
  have hmove : ∀ g : SteinbergGroup R n,
      steinbergSymbol hij w₁ w₂ * g * (steinbergSymbol hij w₁ w₂)⁻¹ = g := by
    intro g
    rw [← hSc g]
    group
  rw [torusCommutator, torusCommutator, torusCommutator, hS]
  calc steinbergSymbol hij w₁ w₂ * steinbergTorus hij w₂ * steinbergTorus hij w₁
        * steinbergTorus hik t
        * (steinbergSymbol hij w₁ w₂ * steinbergTorus hij w₂ * steinbergTorus hij w₁)⁻¹
        * (steinbergTorus hik t)⁻¹
      = steinbergSymbol hij w₁ w₂
        * (steinbergTorus hij w₂ * steinbergTorus hij w₁ * steinbergTorus hik t
          * (steinbergTorus hij w₂ * steinbergTorus hij w₁)⁻¹)
        * (steinbergSymbol hij w₁ w₂)⁻¹ * (steinbergTorus hik t)⁻¹ := by group
    _ = (steinbergTorus hij w₂ * steinbergTorus hij w₁ * steinbergTorus hik t
          * (steinbergTorus hij w₂ * steinbergTorus hij w₁)⁻¹)
        * (steinbergTorus hik t)⁻¹ := by
        rw [hmove]
    _ = steinbergTorus hij w₂
        * (steinbergTorus hij w₁ * steinbergTorus hik t * (steinbergTorus hij w₁)⁻¹
          * (steinbergTorus hik t)⁻¹)
        * (steinbergTorus hij w₂)⁻¹
        * (steinbergTorus hij w₂ * steinbergTorus hik t * (steinbergTorus hij w₂)⁻¹
          * (steinbergTorus hik t)⁻¹) := by group

end GaloisForLFunctions.HTGeometry

end
