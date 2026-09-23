import GaloisForLFunctions.HTGeometry.GaussBonnetPlanarPartials

/-!
# Calculus rules for planar partial derivatives

Sum, product, quotient, constant and square-root rules for the coordinate partial derivatives `px`
and `py` of `GaussBonnetPlanarPartials`.  Each is obtained from the corresponding one-variable rule
applied to the coordinate slice, together with uniqueness of the derivative.
-/

open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

variable {A B : ℝ × ℝ → ℝ}

theorem px_const (c : ℝ) (u v : ℝ) : px (fun _ : ℝ × ℝ => c) (u, v) = 0 := by
  simp [px]

theorem py_const (c : ℝ) (u v : ℝ) : py (fun _ : ℝ × ℝ => c) (u, v) = 0 := by
  simp [py]

theorem px_add (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (u v : ℝ) :
    px (fun q => A q + B q) (u, v) = px A (u, v) + px B (u, v) :=
  (hasDerivAt_px (hA.add hB) u v).unique ((hasDerivAt_px hA u v).add (hasDerivAt_px hB u v))

theorem py_add (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (u v : ℝ) :
    py (fun q => A q + B q) (u, v) = py A (u, v) + py B (u, v) :=
  (hasDerivAt_py (hA.add hB) u v).unique ((hasDerivAt_py hA u v).add (hasDerivAt_py hB u v))

theorem px_neg (hA : ContDiff ℝ ∞ A) (u v : ℝ) :
    px (fun q => -A q) (u, v) = -px A (u, v) :=
  (hasDerivAt_px hA.neg u v).unique (hasDerivAt_px hA u v).neg

theorem py_neg (hA : ContDiff ℝ ∞ A) (u v : ℝ) :
    py (fun q => -A q) (u, v) = -py A (u, v) :=
  (hasDerivAt_py hA.neg u v).unique (hasDerivAt_py hA u v).neg

theorem px_mul (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (u v : ℝ) :
    px (fun q => A q * B q) (u, v) = px A (u, v) * B (u, v) + A (u, v) * px B (u, v) :=
  (hasDerivAt_px (hA.mul hB) u v).unique ((hasDerivAt_px hA u v).mul (hasDerivAt_px hB u v))

theorem py_mul (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (u v : ℝ) :
    py (fun q => A q * B q) (u, v) = py A (u, v) * B (u, v) + A (u, v) * py B (u, v) :=
  (hasDerivAt_py (hA.mul hB) u v).unique ((hasDerivAt_py hA u v).mul (hasDerivAt_py hB u v))

theorem px_div (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hne : ∀ q, B q ≠ 0) (u v : ℝ) :
    px (fun q => A q / B q) (u, v)
      = (px A (u, v) * B (u, v) - A (u, v) * px B (u, v)) / B (u, v) ^ (2 : ℕ) :=
  (hasDerivAt_px (hA.div hB hne) u v).unique
    ((hasDerivAt_px hA u v).div (hasDerivAt_px hB u v) (hne (u, v)))

theorem py_div (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hne : ∀ q, B q ≠ 0) (u v : ℝ) :
    py (fun q => A q / B q) (u, v)
      = (py A (u, v) * B (u, v) - A (u, v) * py B (u, v)) / B (u, v) ^ (2 : ℕ) :=
  (hasDerivAt_py (hA.div hB hne) u v).unique
    ((hasDerivAt_py hA u v).div (hasDerivAt_py hB u v) (hne (u, v)))

theorem px_sqrt (hA : ContDiff ℝ ∞ A) (hne : ∀ q, A q ≠ 0) (u v : ℝ) :
    px (fun q => Real.sqrt (A q)) (u, v) = px A (u, v) / (2 * Real.sqrt (A (u, v))) :=
  (hasDerivAt_px (hA.sqrt hne) u v).unique ((hasDerivAt_px hA u v).sqrt (hne (u, v)))

theorem py_sqrt (hA : ContDiff ℝ ∞ A) (hne : ∀ q, A q ≠ 0) (u v : ℝ) :
    py (fun q => Real.sqrt (A q)) (u, v) = py A (u, v) / (2 * Real.sqrt (A (u, v))) :=
  (hasDerivAt_py (hA.sqrt hne) u v).unique ((hasDerivAt_py hA u v).sqrt (hne (u, v)))

end GaloisForLFunctions.HTGeometry.GaussBonnet
