import GaloisForLFunctions.HTGeometry.BoundedSolutionDerivative

/-! A complex solution's value and second-derivative bounds control its actual first derivative. -/
open Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- Componentwise Landau control on a unit interval, with no phase or decay premise. -/
theorem norm_complex_deriv_le_of_bounded {f g h : ℝ → ℂ} {u C M : ℝ}
    (hf : ∀ t ∈ Icc u (u+1), HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc u (u+1), HasDerivAt g (h t) t)
    (hh : ContinuousOn h (Icc u (u+1)))
    (hC : ∀ t ∈ Icc u (u+1), ‖f t‖ ≤ C)
    (hM : ∀ t ∈ Icc u (u+1), ‖h t‖ ≤ M) : ‖g u‖ ≤ 4*C+M := by
  have hr := abs_deriv_le_of_bounded
    (fun t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht))
    (fun t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hg t ht))
    (Complex.continuous_re.comp_continuousOn hh)
    (fun t ht => (Complex.abs_re_le_norm _).trans (hC t ht))
    (fun t ht => (Complex.abs_re_le_norm _).trans (hM t ht))
  have hi := abs_deriv_le_of_bounded
    (fun t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht))
    (fun t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hg t ht))
    (Complex.continuous_im.comp_continuousOn hh)
    (fun t ht => (Complex.abs_im_le_norm _).trans (hC t ht))
    (fun t ht => (Complex.abs_im_le_norm _).trans (hM t ht))
  have hn := Complex.norm_le_abs_re_add_abs_im (g u)
  change |(g u).re| ≤ 2*C+M/2 at hr
  change |(g u).im| ≤ 2*C+M/2 at hi
  linarith

end
end GaloisForLFunctions.HTGeometry
