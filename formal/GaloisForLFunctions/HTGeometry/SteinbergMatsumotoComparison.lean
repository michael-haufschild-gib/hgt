import GaloisForLFunctions.HTGeometry.SteinbergMatsumotoRelation
import GaloisForLFunctions.HTGeometry.SteinbergTorusAction
import GaloisForLFunctions.HTGeometry.SteinbergTorusBilinear

/-!
# Matsumoto's cross-torus comparison

For three distinct indices, Matsumoto's bilinear Steinberg symbol is the cross-torus commutator.
The project originally contained two related but separate words:

```text
[h_ik(r), h_ij(s)]
and
h_ij(rs) h_ij(r)⁻¹ h_ij(s)⁻¹.
```

This file proves that they are exactly equal in the Steinberg group.  The proof follows the hint in
Weibel, *The K-book*, Exercise III.5.9: conjugate `h_ij(s)` by `h_ik(r)`.  Conjugating each root
generator gives `w_ij(s) ↦ w_ij(rs)` and `w_ij(-1) ↦ w_ij(-r)`; the elementary identity
`w_ij(-r) = w_ij(r)⁻¹` completes the calculation.

Together with a spare fourth index, the cross-pair centrality theorem turns this comparison into
genuine bilinearity of the existing `steinbergSymbol`.  The finite-rank spare-index condition is
explicit rather than being concealed by an illegitimate stable-range inference.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
/-- Conjugating one torus by a transverse torus is the Matsumoto torus-defect identity. -/
theorem steinbergTorus_conj_transverse {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r s : Rˣ) :
    steinbergTorus hik r * steinbergTorus hij s * (steinbergTorus hik r)⁻¹
      = steinbergTorus hij (r * s) * (steinbergTorus hij r)⁻¹ := by
  have hweyl : ∀ q : Rˣ,
      steinbergTorus hik r * steinbergWeyl hij q * (steinbergTorus hik r)⁻¹
        = steinbergWeyl hij (r * q) := by
    intro q
    have hfirst : steinbergTorus hik r * steinbergX hij (q : R)
        * (steinbergTorus hik r)⁻¹ = steinbergX hij ((r * q : Rˣ) : R) := by
      have h := steinbergTorus_conj_first hik hij (Ne.symm hjk) r (q : R)
      simpa only [Units.val_mul] using h
    have hcol : steinbergTorus hik r * steinbergX (Ne.symm hij) (-((q⁻¹ : Rˣ) : R))
        * (steinbergTorus hik r)⁻¹
        = steinbergX (Ne.symm hij) (-(((r * q)⁻¹ : Rˣ) : R)) := by
      have h := steinbergTorus_conj_col hik hij (Ne.symm hjk) r (-((q⁻¹ : Rˣ) : R))
      have hval : -((q⁻¹ : Rˣ) : R) * ((r⁻¹ : Rˣ) : R)
          = -(((r * q)⁻¹ : Rˣ) : R) := by
        rw [mul_inv_rev]
        push_cast
        ring
      rw [hval] at h
      exact h
    rw [steinbergWeyl]
    calc steinbergTorus hik r * (steinbergX hij (q : R)
          * steinbergX (Ne.symm hij) (-((q⁻¹ : Rˣ) : R)) * steinbergX hij (q : R))
          * (steinbergTorus hik r)⁻¹
        = (steinbergTorus hik r * steinbergX hij (q : R) * (steinbergTorus hik r)⁻¹)
          * (steinbergTorus hik r * steinbergX (Ne.symm hij) (-((q⁻¹ : Rˣ) : R))
            * (steinbergTorus hik r)⁻¹)
          * (steinbergTorus hik r * steinbergX hij (q : R) * (steinbergTorus hik r)⁻¹) := by group
      _ = steinbergX hij ((r * q : Rˣ) : R)
          * steinbergX (Ne.symm hij) (-(((r * q)⁻¹ : Rˣ) : R))
          * steinbergX hij ((r * q : Rˣ) : R) := by rw [hfirst, hcol]
  have hweylNeg : steinbergTorus hik r * steinbergWeyl hij (-1 : Rˣ)
      * (steinbergTorus hik r)⁻¹ = steinbergWeyl hij (-r) := by
    simpa using hweyl (-1 : Rˣ)
  rw [steinbergTorus]
  calc steinbergTorus hik r * (steinbergWeyl hij s * steinbergWeyl hij (-1 : Rˣ))
        * (steinbergTorus hik r)⁻¹
      = (steinbergTorus hik r * steinbergWeyl hij s * (steinbergTorus hik r)⁻¹)
        * (steinbergTorus hik r * steinbergWeyl hij (-1 : Rˣ) * (steinbergTorus hik r)⁻¹) := by group
    _ = steinbergWeyl hij (r * s) * steinbergWeyl hij (-r) := by rw [hweyl, hweylNeg]
    _ = (steinbergWeyl hij (r * s) * steinbergWeyl hij (-1 : Rˣ))
        * (steinbergWeyl hij r * steinbergWeyl hij (-1 : Rˣ))⁻¹ := by
      rw [steinbergWeyl_neg]
      group

omit [DecidableEq n] in
/-- **Matsumoto's comparison:** the cross-torus commutator is the torus section defect. -/
theorem torusCommutator_eq_steinbergSymbol {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r s : Rˣ) :
    torusCommutator hik hij r s = steinbergSymbol hij r s := by
  rw [torusCommutator, steinbergSymbol]
  rw [steinbergTorus_conj_transverse hij hik hjk]

/-- With a spare fourth index, the Steinberg symbol is multiplicative in its first slot. -/
theorem steinbergSymbol_mul_left_of_spare_index {i j k ℓ : n} [Fintype n]
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) (r₁ r₂ s : Rˣ) :
    steinbergSymbol hij (r₁ * r₂) s
      = steinbergSymbol hij r₁ s * steinbergSymbol hij r₂ s := by
  calc steinbergSymbol hij (r₁ * r₂) s = torusCommutator hik hij (r₁ * r₂) s :=
      (torusCommutator_eq_steinbergSymbol hij hik hjk (r₁ * r₂) s).symm
    _ = torusCommutator hik hij r₁ s * torusCommutator hik hij r₂ s :=
      torusCommutator_mul_left_bilinear hik hij (Ne.symm hjk) hℓi hℓk hℓj r₁ r₂ s
    _ = steinbergSymbol hij r₁ s * steinbergSymbol hij r₂ s := by
      rw [torusCommutator_eq_steinbergSymbol hij hik hjk,
        torusCommutator_eq_steinbergSymbol hij hik hjk]

/-- With a spare fourth index, the Steinberg symbol is multiplicative in its second slot. -/
theorem steinbergSymbol_mul_right_of_spare_index {i j k ℓ : n} [Fintype n]
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) (r s₁ s₂ : Rˣ) :
    steinbergSymbol hij r (s₁ * s₂)
      = steinbergSymbol hij r s₁ * steinbergSymbol hij r s₂ := by
  calc steinbergSymbol hij r (s₁ * s₂) = torusCommutator hik hij r (s₁ * s₂) :=
      (torusCommutator_eq_steinbergSymbol hij hik hjk r (s₁ * s₂)).symm
    _ = torusCommutator hik hij r s₁ * torusCommutator hik hij r s₂ :=
      torusCommutator_mul_right_bilinear hik hij (Ne.symm hjk) hℓi hℓk hℓj r s₁ s₂
    _ = steinbergSymbol hij r s₁ * steinbergSymbol hij r s₂ := by
      rw [torusCommutator_eq_steinbergSymbol hij hik hjk,
        torusCommutator_eq_steinbergSymbol hij hik hjk]

end GaloisForLFunctions.HTGeometry

end
