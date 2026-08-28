import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive

/-!
# Pole-side index anchors for half-plane Carathéodory kernels

The negative-square bookkeeping of Carathéodory kernels of rational Herglotz-type sums is
anchored by two one-pole facts.  The real part of a Cauchy atom `1/(u - z)` at `u` has the sign
of `u.re - z.re`: an atom with pole in the open left half plane is positive-real on the closed
right half plane, while an atom with pole in the open right half plane has strictly negative
real part — hence a strictly negative Carathéodory diagonal — at every node strictly between the
imaginary axis and the pole's abscissa.  Consequently a finite sum of Cauchy atoms with all
poles in the open left half plane has a positive semidefinite Carathéodory kernel on the right
half plane: the index-zero half of the dictionary, with no arithmetic input.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real part of a Cauchy atom is the abscissa gap over the squared distance. -/
theorem re_one_div_sub (w z : ℂ) :
    (1 / (w - z)).re = (w.re - z.re) / Complex.normSq (w - z) := by
  rw [one_div, Complex.inv_re, Complex.sub_re]

/-- Left-half-plane pole: the Cauchy atom is positive-real on the closed right half plane. -/
theorem re_one_div_sub_nonneg {w z : ℂ} (hz : z.re < 0) (hw : 0 ≤ w.re) :
    0 ≤ (1 / (w - z)).re := by
  rw [re_one_div_sub]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- **Right-half-plane pole detector, sign characterization.**  At distinct points the Cauchy
atom has strictly negative real part exactly when the node abscissa lies strictly left of the
pole abscissa: each right-half-plane pole is detected by a rank-one Carathéodory diagonal. -/
theorem re_one_div_sub_neg_iff {w z : ℂ} (hwz : w ≠ z) :
    (1 / (w - z)).re < 0 ↔ w.re < z.re := by
  rw [re_one_div_sub]
  have hpos : 0 < Complex.normSq (w - z) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hwz)
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hpos⟩

theorem re_one_div_sub_neg {w z : ℂ} (hwz : w ≠ z) (h : w.re < z.re) :
    (1 / (w - z)).re < 0 :=
  (re_one_div_sub_neg_iff hwz).mpr h

/-- A finite Cauchy-atom sum with all poles in the open left half plane is positive-real on the
open right half plane. -/
theorem re_lhpPoleSum_nonneg {n : ℕ} {z : Fin n → ℂ} (hz : ∀ j, (z j).re < 0)
    {u : ℂ} (hu : 0 < u.re) :
    0 ≤ ((∑ j, 1 / (u - z j)).re) := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => re_one_div_sub_nonneg (hz j) hu.le

/-- **Index-zero anchor.**  The Carathéodory kernel of a finite Cauchy-atom sum with all poles
in the open left half plane is positive semidefinite on the right half plane: stable pole
configurations carry no negative squares. -/
theorem isPSDKernel_lhpPoleSum {n : ℕ} {z : Fin n → ℂ} (hz : ∀ j, (z j).re < 0) :
    IsPSDKernel (fun x y : {u : ℂ // 0 < u.re} =>
      ((∑ j, 1 / ((x : ℂ) - z j)) + conj (∑ j, 1 / ((y : ℂ) - z j))) /
        ((x : ℂ) + conj (y : ℂ))) := by
  refine isPSDKernel_halfPlaneCaratheodory (fun u hu => ?_)
    (fun u hu => re_lhpPoleSum_nonneg hz hu)
  refine DifferentiableAt.fun_sum fun j _ => ?_
  have hne : u - z j ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at hre
    have := hz j
    linarith
  have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - z j)⁻¹) u :=
    (differentiableAt_fun_id.sub (differentiableAt_const (z j))).inv hne
  simpa [one_div] using hdiff

end

end GaloisForLFunctions.HTGeometry
