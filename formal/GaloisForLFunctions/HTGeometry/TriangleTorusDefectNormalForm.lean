import GaloisForLFunctions.HTGeometry.TriangleTorusDefect
import GaloisForLFunctions.HTGeometry.SteinbergMatsumotoComparison
import GaloisForLFunctions.HTGeometry.SteinbergWeylTriangle

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*}

/-- The three-index torus-triangle defect is a single-root Weyl-square cocycle.

This removes every mixed-root contribution from the Dennis--Stein right-one obstruction. -/
theorem torusTriangleDefect_weyl_square {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (v : Rˣ) :
    torusTriangleDefect hij hjk hik v = steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ)
      * steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hik v := by
  have hneg : steinbergWeyl hik (-1 : Rˣ) = (steinbergWeyl hik (1 : Rˣ))⁻¹ := by
    simpa using steinbergWeyl_neg hik (1 : Rˣ)
  have hB : ∀ q : Rˣ, steinbergWeyl (Ne.symm hjk) q
      = steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hij q * steinbergWeyl hik (1 : Rˣ) := by
    intro q
    calc steinbergWeyl (Ne.symm hjk) q
        = steinbergWeyl hik (-1 : Rˣ)
          * (steinbergWeyl hik (1 : Rˣ) * steinbergWeyl (Ne.symm hjk) q
            * steinbergWeyl hik (-1 : Rˣ)) * steinbergWeyl hik (1 : Rˣ) := by
          rw [hneg]
          group
      _ = steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hij q
          * steinbergWeyl hik (1 : Rˣ) := by
          rw [steinbergWeyl_triangle_mul hij hik hjk (1 : Rˣ) q]
          simp
  have hweyl : ∀ q : Rˣ,
      steinbergTorus hij v * steinbergWeyl hik q * (steinbergTorus hij v)⁻¹
        = steinbergWeyl hik (v * q) := by
    intro q
    have hfirst : steinbergTorus hij v * steinbergX hik (q : R)
        * (steinbergTorus hij v)⁻¹ = steinbergX hik ((v * q : Rˣ) : R) := by
      have h := steinbergTorus_conj_first hij hik hjk v (q : R)
      simpa only [Units.val_mul] using h
    have hcol : steinbergTorus hij v
        * steinbergX (Ne.symm hik) (-((q⁻¹ : Rˣ) : R)) * (steinbergTorus hij v)⁻¹
        = steinbergX (Ne.symm hik) (-(((v * q)⁻¹ : Rˣ) : R)) := by
      have h := steinbergTorus_conj_col hij hik hjk v (-((q⁻¹ : Rˣ) : R))
      have hval : -((q⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R)
          = -(((v * q)⁻¹ : Rˣ) : R) := by
        rw [mul_inv_rev]
        push_cast
        ring
      rw [hval] at h
      exact h
    rw [steinbergWeyl]
    calc steinbergTorus hij v * (steinbergX hik (q : R)
          * steinbergX (Ne.symm hik) (-((q⁻¹ : Rˣ) : R)) * steinbergX hik (q : R))
          * (steinbergTorus hij v)⁻¹
        = (steinbergTorus hij v * steinbergX hik (q : R) * (steinbergTorus hij v)⁻¹)
          * (steinbergTorus hij v * steinbergX (Ne.symm hik) (-((q⁻¹ : Rˣ) : R))
            * (steinbergTorus hij v)⁻¹)
          * (steinbergTorus hij v * steinbergX hik (q : R) * (steinbergTorus hij v)⁻¹) := by
          group
      _ = steinbergX hik ((v * q : Rˣ) : R)
          * steinbergX (Ne.symm hik) (-(((v * q)⁻¹ : Rˣ) : R))
          * steinbergX hik ((v * q : Rˣ) : R) := by
          rw [hfirst, hcol]
      _ = steinbergWeyl hik (v * q) := by rw [steinbergWeyl]
  have haction : steinbergTorus hij v * steinbergWeyl hik (1 : Rˣ)
      * (steinbergTorus hij v)⁻¹ = steinbergWeyl hik v := by
    simpa using hweyl (1 : Rˣ)
  have haction' : steinbergWeyl hij v * steinbergWeyl hij (-1 : Rˣ)
      * steinbergWeyl hik (1 : Rˣ) * (steinbergWeyl hij v * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hik v := by
    rw [← haction, steinbergTorus]
  rw [torusTriangleDefect, steinbergTorus, steinbergTorus, steinbergTorus,
    hB v, hB (-1 : Rˣ)]
  calc steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ)
        * (steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hij v * steinbergWeyl hik (1 : Rˣ)
          * (steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hij (-1 : Rˣ)
            * steinbergWeyl hik (1 : Rˣ)))
        * (steinbergWeyl hij v * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hik (-1 : Rˣ)
          * (steinbergWeyl hij v * steinbergWeyl hij (-1 : Rˣ)
            * steinbergWeyl hik (1 : Rˣ)
            * (steinbergWeyl hij v * steinbergWeyl hij (-1 : Rˣ))⁻¹) := by
          rw [hneg]
          group
    _ = steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hik (-1 : Rˣ)
          * steinbergWeyl hik v := by rw [haction']

end GaloisForLFunctions.HTGeometry
