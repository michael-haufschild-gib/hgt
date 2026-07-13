import GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Translation invariance transports the meromorphic order through one period. -/
theorem periodic_meromorphicOrderAt_add_eq
    {f : ℂ → ℂ} {omega : ℂ} (hperiod : Function.Periodic f omega) (z : ℂ) :
    meromorphicOrderAt f (z + omega) = meromorphicOrderAt f z := by
  let g : ℂ → ℂ := fun w => w + omega
  have hg : AnalyticAt ℂ g z := by fun_prop
  have hg' : deriv g z ≠ 0 := by
    have hderiv : HasDerivAt g 1 z := by
      simpa [g] using (hasDerivAt_id z).add_const omega
    rw [hderiv.deriv]
    norm_num
  have hcomp : f ∘ g = f := by
    funext w
    exact hperiod w
  calc
    meromorphicOrderAt f (z + omega) = meromorphicOrderAt f (g z) := by rfl
    _ = meromorphicOrderAt (f ∘ g) z :=
      (meromorphicOrderAt_comp_of_deriv_ne_zero hg hg').symm
    _ = meromorphicOrderAt f z := by rw [hcomp]

/-- A quotient of entire functions is analytic wherever its denominator is nonzero; hence every
negative meromorphic order of the quotient lies on the denominator zero set. -/
theorem denominator_zero_of_quotient_meromorphicOrderAt_neg
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    {z : ℂ} (hpole : meromorphicOrderAt (fun w => -D w / C w) z < 0) :
    C z = 0 := by
  by_contra hCz
  have hCan : AnalyticAt ℂ C z :=
    (hC.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hDan : AnalyticAt ℂ D z :=
    (hD.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hqan : AnalyticAt ℂ (fun w => -D w / C w) z :=
    hDan.neg.div hCan hCz
  exact (not_lt_of_ge hqan.meromorphicOrderAt_nonneg) hpole

/-- **Minimal-type quotient aperiodicity.** If a quotient of entire functions has at least one
pole and its denominator has minimal exponential type, then the quotient has no nonzero complex
translation period. -/
theorem minimalType_quotient_aperiodic
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    {c p : ℂ} (hCc : C c ≠ 0)
    (hpole : meromorphicOrderAt (fun w => -D w / C w) p < 0) :
    ∀ omega : ℂ, omega ≠ 0 → ¬ Function.Periodic (fun w => -D w / C w) omega := by
  intro omega homega hperiod
  have hzero : ∀ n : ℕ, C (p + n • omega) = 0 := by
    intro n
    apply denominator_zero_of_quotient_meromorphicOrderAt_neg hCmin.1 hD
    have horder := periodic_meromorphicOrderAt_add_eq (hperiod.nsmul n) p
    rwa [horder]
  exact hCmin.no_arithmeticProgression_zeros hCc homega hzero

end
end GaloisForLFunctions.HTGeometry
