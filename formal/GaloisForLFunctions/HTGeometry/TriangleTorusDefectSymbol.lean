import GaloisForLFunctions.HTGeometry.TriangleTorusDefectNormalForm
import GaloisForLFunctions.HTGeometry.SteinbergTorusAction

/-!
# The triangle torus defect is a Steinberg symbol

The Weyl-square normal form has one remaining rank-one factor.  The `−1` torus
acts trivially on both root subgroups in that factor, so it commutes with the Weyl
element.  Expanding the defining cocycle then identifies the whole triangle defect
with the inverse symbol `{v, −1}`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*}

/-- The `−1` torus centralizes every Weyl element of its root, with a spare index. -/
theorem steinbergTorus_neg_one_commutes_weyl {i j k : n} (hik : i ≠ k)
    (hij : i ≠ j) (hjk : j ≠ k) (v : Rˣ) :
    steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v
      = steinbergWeyl hik v * steinbergTorus hik (-1 : Rˣ) := by
  have hfirst : steinbergTorus hik (-1 : Rˣ) * steinbergX hik (v : R)
      * (steinbergTorus hik (-1 : Rˣ))⁻¹ = steinbergX hik (v : R) := by
    have h := steinbergTorus_conj_self hik hij (Ne.symm hjk) (-1 : Rˣ) (v : R)
    convert h using 1
    all_goals simp
  have hsecond : steinbergTorus hik (-1 : Rˣ)
      * steinbergX (Ne.symm hik) (-((v⁻¹ : Rˣ) : R))
      * (steinbergTorus hik (-1 : Rˣ))⁻¹
      = steinbergX (Ne.symm hik) (-((v⁻¹ : Rˣ) : R)) := by
    have h := steinbergTorus_conj_transpose hik hij (Ne.symm hjk) (-1 : Rˣ)
      (-((v⁻¹ : Rˣ) : R))
    convert h using 1
    all_goals simp
  have hconj : steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v
      * (steinbergTorus hik (-1 : Rˣ))⁻¹ = steinbergWeyl hik v := by
    rw [steinbergWeyl]
    calc steinbergTorus hik (-1 : Rˣ) * (steinbergX hik (v : R)
          * steinbergX (Ne.symm hik) (-((v⁻¹ : Rˣ) : R)) * steinbergX hik (v : R))
          * (steinbergTorus hik (-1 : Rˣ))⁻¹
        = (steinbergTorus hik (-1 : Rˣ) * steinbergX hik (v : R)
            * (steinbergTorus hik (-1 : Rˣ))⁻¹)
          * (steinbergTorus hik (-1 : Rˣ)
              * steinbergX (Ne.symm hik) (-((v⁻¹ : Rˣ) : R))
              * (steinbergTorus hik (-1 : Rˣ))⁻¹)
          * (steinbergTorus hik (-1 : Rˣ) * steinbergX hik (v : R)
              * (steinbergTorus hik (-1 : Rˣ))⁻¹) := by
          group
      _ = steinbergX hik (v : R) * steinbergX (Ne.symm hik) (-((v⁻¹ : Rˣ) : R))
          * steinbergX hik (v : R) := by rw [hfirst, hsecond]
      _ = steinbergWeyl hik v := by rw [steinbergWeyl]
  calc steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v
      = (steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v
          * (steinbergTorus hik (-1 : Rˣ))⁻¹) * steinbergTorus hik (-1 : Rˣ) := by group
    _ = steinbergWeyl hik v * steinbergTorus hik (-1 : Rˣ) := by rw [hconj]

/-- The three-index torus correction is the inverse single-root symbol `{v, −1}`. -/
theorem torusTriangleDefect_eq_symbol_inv {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (v : Rˣ) :
    torusTriangleDefect hij hjk hik v = (steinbergSymbol hik v (-1 : Rˣ))⁻¹ := by
  have hcomm := steinbergTorus_neg_one_commutes_weyl hik hij hjk v
  have hsymbol : (steinbergSymbol hik v (-1 : Rˣ))⁻¹
      = steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v * steinbergWeyl hik v := by
    rw [steinbergSymbol, steinbergTorus, steinbergTorus]
    have hmul : v * (-1 : Rˣ) = -v := by simp
    rw [hmul, steinbergWeyl_neg hik v]
    group
    change steinbergTorus hik (-1 : Rˣ)
        * (steinbergWeyl hik v * steinbergWeyl hik v)
      = steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v * steinbergWeyl hik v
    group
  rw [torusTriangleDefect_weyl_square, hsymbol]
  calc steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ)
        * steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hik v
      = steinbergWeyl hik v
          * (steinbergWeyl hik (-1 : Rˣ) * steinbergWeyl hik (-1 : Rˣ))
          * steinbergWeyl hik v := by group
    _ = steinbergWeyl hik v * steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v := by rfl
    _ = steinbergTorus hik (-1 : Rˣ) * steinbergWeyl hik v * steinbergWeyl hik v := by
      rw [← hcomm]

/-- The product of the two adjacent tori differs from the long-root torus by `{v, −1}`. -/
theorem steinbergTorus_triangle_mul {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (v : Rˣ) :
    steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v
      = (steinbergSymbol hik v (-1 : Rˣ))⁻¹ * steinbergTorus hij v := by
  have hdefect := torusTriangleDefect_eq_symbol_inv hij hjk hik v
  rw [torusTriangleDefect] at hdefect
  calc steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v
      = (steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v
          * (steinbergTorus hij v)⁻¹) * steinbergTorus hij v := by group
    _ = (steinbergSymbol hik v (-1 : Rˣ))⁻¹ * steinbergTorus hij v := by rw [hdefect]

/-- Moving the torus across a triangle introduces exactly the inverse symbol `{v, −1}`. -/
theorem steinbergTorus_triangle_transport {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (v : Rˣ) :
    steinbergTorus (Ne.symm hjk) v
      = (steinbergTorus hik v)⁻¹ * (steinbergSymbol hik v (-1 : Rˣ))⁻¹
        * steinbergTorus hij v := by
  have hmul := steinbergTorus_triangle_mul hij hjk hik v
  calc steinbergTorus (Ne.symm hjk) v
      = (steinbergTorus hik v)⁻¹
          * (steinbergTorus hik v * steinbergTorus (Ne.symm hjk) v) := by group
    _ = (steinbergTorus hik v)⁻¹ * ((steinbergSymbol hik v (-1 : Rˣ))⁻¹
          * steinbergTorus hij v) := by rw [hmul]

end GaloisForLFunctions.HTGeometry
