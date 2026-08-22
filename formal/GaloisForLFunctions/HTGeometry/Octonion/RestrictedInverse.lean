import GaloisForLFunctions.HTGeometry.Octonion.GeneratedSubalgebra

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The real-linear resolvent difference `R_s - L_q`. -/
def resolventDifference (s q x : RealOctonion) : RealOctonion :=
  rightAction s x - leftAction q x

theorem resolventDifference_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) :
    resolventDifference s q x ∈ generatedSubmodule s q := by
  unfold resolventDifference leftAction rightAction
  exact Submodule.sub_mem _
    (mul_mem_generatedSubmodule s q x s hx (s_mem_generatedSubmodule s q))
    (mul_mem_generatedSubmodule s q q x (q_mem_generatedSubmodule s q) hx)

theorem conjugate_resolventDifference_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) :
    resolventDifference (star s) q x ∈ generatedSubmodule s q := by
  unfold resolventDifference leftAction rightAction
  exact Submodule.sub_mem _
    (mul_mem_generatedSubmodule s q x (star s) hx (star_s_mem_generatedSubmodule s q))
    (mul_mem_generatedSubmodule s q q x (q_mem_generatedSubmodule s q) hx)

theorem quadratic_mem_generatedSubmodule (s q : RealOctonion) :
    quadratic s q ∈ generatedSubmodule s q := by
  unfold quadratic
  apply Submodule.add_mem
  · exact Submodule.sub_mem _
      (mul_mem_generatedSubmodule s q q q
        (q_mem_generatedSubmodule s q) (q_mem_generatedSubmodule s q))
      (mul_mem_generatedSubmodule s q (scalarEmbed (2 * s.1.re)) q
        (scalarEmbed_mem_generatedSubmodule s q _) (q_mem_generatedSubmodule s q))
  · exact scalarEmbed_mem_generatedSubmodule s q _

theorem star_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) : star x ∈ generatedSubmodule s q := by
  rw [star_eq_scalarEmbed_sub]
  exact Submodule.sub_mem _ (scalarEmbed_mem_generatedSubmodule s q _) hx

theorem inverse_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) : inverse x ∈ generatedSubmodule s q := by
  unfold inverse
  rw [scalarEmbed_mul]
  exact Submodule.smul_mem _ _ (star_mem_generatedSubmodule s q x hx)

theorem q_commutes_quadratic (s q : RealOctonion) :
    q * quadratic s q = quadratic s q * q := by
  unfold quadratic
  rw [mul_add, add_mul, mul_sub, sub_mul]
  have hq : q * (q * q) = (q * q) * q := IsAlternative.mul_alternative_left q q
  rw [hq]
  have htr : q * (scalarEmbed (2 * s.1.re) * q) =
      (scalarEmbed (2 * s.1.re) * q) * q := by
    rw [scalarEmbed_mul, mul_smul_comm, smul_mul_assoc]
  rw [htr]
  have hnorm : q * scalarEmbed (normSq s) = scalarEmbed (normSq s) * q := by
    rw [mul_scalarEmbed, scalarEmbed_mul]
  rw [hnorm]

theorem q_commutes_inverse_quadratic (s q : RealOctonion) :
    q * inverse (quadratic s q) = inverse (quadratic s q) * q := by
  rw [inverse, scalarEmbed_mul, mul_smul_comm, smul_mul_assoc]
  rw [star_eq_scalarEmbed_sub]
  simp only [mul_sub, sub_mul]
  rw [q_commutes_quadratic]
  have hscalar : q * scalarEmbed (2 * (quadratic s q).1.re) =
      scalarEmbed (2 * (quadratic s q).1.re) * q := by
    rw [mul_scalarEmbed, scalarEmbed_mul]
  rw [hscalar]

/-- The reverse product of the two resolvent differences on the Artin subalgebra. -/
theorem reverse_resolvent_factorization_of_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) :
    resolventDifference (star s) q (resolventDifference s q x) = quadratic s q * x := by
  have hs := s_mem_generatedSubmodule s q
  have hq := q_mem_generatedSubmodule s q
  have hsbar := star_s_mem_generatedSubmodule s q
  have hss : (x * s) * star s = x * (s * star s) :=
    sub_eq_zero.mp
      (associator_eq_zero_of_mem_generatedSubmodule s q x s (star s) hx hs hsbar)
  have hqxs : (q * x) * s = q * (x * s) :=
    sub_eq_zero.mp
      (associator_eq_zero_of_mem_generatedSubmodule s q q x s hq hx hs)
  have hqxsbar : (q * x) * star s = q * (x * star s) :=
    sub_eq_zero.mp
      (associator_eq_zero_of_mem_generatedSubmodule s q q x (star s) hq hx hsbar)
  have hnorm : x * (s * star s) = scalarEmbed (normSq s) * x := by
    rw [mul_star_self_eq_scalarEmbed, mul_scalarEmbed, scalarEmbed_mul]
  have htrace : q * (x * (star s + s)) =
      (scalarEmbed (2 * s.1.re) * q) * x := by
    rw [add_comm (star s) s, add_star_eq_scalarEmbed]
    calc
      q * (x * scalarEmbed (2 * s.1.re)) = q * ((2 * s.1.re) • x) := by
        rw [mul_scalarEmbed]
      _ = scalarEmbed (2 * s.1.re) * (q * x) := by
        rw [mul_smul_comm, scalarEmbed_mul]
      _ = (scalarEmbed (2 * s.1.re) * q) * x :=
        (scalarEmbed_associates _ _ _).symm
  have hcombine : q * (x * star s) + q * (x * s) = q * (x * (star s + s)) := by
    calc
      q * (x * star s) + q * (x * s) = q * (x * star s + x * s) := by
        rw [mul_add]
      _ = q * (x * (star s + s)) := by
        conv_rhs => rw [mul_add]
  unfold resolventDifference
  simp only [leftAction, rightAction, quadratic, sub_mul, mul_sub]
  calc
    (x * s) * star s - (q * x) * star s - (q * (x * s) - q * (q * x)) =
      x * (s * star s) - q * (x * star s) - q * (x * s) + q * (q * x) := by
        rw [hss, hqxsbar]
        abel
    _ = scalarEmbed (normSq s) * x - q * (x * (star s + s)) + (q * q) * x := by
      rw [hnorm, IsAlternative.mul_alternative_left]
      rw [← hcombine]
      abel
    _ = (q * q - scalarEmbed (2 * s.1.re) * q + scalarEmbed (normSq s)) * x := by
      rw [htrace, add_mul, sub_mul]
      abel

/-- Candidate for the inverse of `R_s - L_q` on the two-generated subalgebra. -/
def restrictedResolventInverse (s q x : RealOctonion) : RealOctonion :=
  inverse (quadratic s q) * resolventDifference (star s) q x

theorem restrictedResolventInverse_mem_generatedSubmodule (s q x : RealOctonion)
    (hx : x ∈ generatedSubmodule s q) :
    restrictedResolventInverse s q x ∈ generatedSubmodule s q := by
  unfold restrictedResolventInverse
  exact mul_mem_generatedSubmodule s q _ _
    (inverse_mem_generatedSubmodule s q _ (quadratic_mem_generatedSubmodule s q))
    (conjugate_resolventDifference_mem_generatedSubmodule s q x hx)

/-- First inverse identity underlying paper equation (8.7). -/
theorem resolventDifference_restrictedResolventInverse_apply (s q x : RealOctonion)
    (hquad : quadratic s q ≠ 0) (hx : x ∈ generatedSubmodule s q) :
    resolventDifference s q (restrictedResolventInverse s q x) = x := by
  have hquadmem := quadratic_mem_generatedSubmodule s q
  have hinv := inverse_mem_generatedSubmodule s q _ hquadmem
  have hbar := conjugate_resolventDifference_mem_generatedSubmodule s q x hx
  have hassoc1 : (inverse (quadratic s q) * resolventDifference (star s) q x) * s =
      inverse (quadratic s q) * (resolventDifference (star s) q x * s) :=
    sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q
      (inverse (quadratic s q)) (resolventDifference (star s) q x) s hinv hbar
      (s_mem_generatedSubmodule s q))
  have hassoc2 : q * (inverse (quadratic s q) * resolventDifference (star s) q x) =
      inverse (quadratic s q) * (q * resolventDifference (star s) q x) := by
    have hleft : q * (inverse (quadratic s q) * resolventDifference (star s) q x) =
        (q * inverse (quadratic s q)) * resolventDifference (star s) q x :=
      (sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q q
        (inverse (quadratic s q)) (resolventDifference (star s) q x)
        (q_mem_generatedSubmodule s q) hinv hbar)).symm
    have hright : (inverse (quadratic s q) * q) * resolventDifference (star s) q x =
        inverse (quadratic s q) * (q * resolventDifference (star s) q x) :=
      sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q
        (inverse (quadratic s q)) q (resolventDifference (star s) q x) hinv
        (q_mem_generatedSubmodule s q) hbar)
    rw [hleft, q_commutes_inverse_quadratic, hright]
  have hfactor : resolventDifference s q (resolventDifference (star s) q x) =
      quadratic s q * x := by
    simpa [resolventDifference, leftAction, rightAction] using
      uncorrected_resolvent_factorization_of_mem_generatedSubmodule s q x hx
  have hassoc3 : inverse (quadratic s q) * (quadratic s q * x) =
      (inverse (quadratic s q) * quadratic s q) * x := by
    exact (sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q
      (inverse (quadratic s q)) (quadratic s q) x hinv hquadmem hx)).symm
  change (inverse (quadratic s q) * resolventDifference (star s) q x) * s -
    q * (inverse (quadratic s q) * resolventDifference (star s) q x) = x
  rw [hassoc1, hassoc2, ← mul_sub]
  change inverse (quadratic s q) *
    resolventDifference s q (resolventDifference (star s) q x) = x
  rw [hfactor, hassoc3, inverse_mul _ hquad]
  simp

/-- Second inverse identity underlying paper equation (8.7). -/
theorem restrictedResolventInverse_resolventDifference_apply (s q x : RealOctonion)
    (hquad : quadratic s q ≠ 0) (hx : x ∈ generatedSubmodule s q) :
    restrictedResolventInverse s q (resolventDifference s q x) = x := by
  unfold restrictedResolventInverse
  have hquadmem := quadratic_mem_generatedSubmodule s q
  have hinv := inverse_mem_generatedSubmodule s q _ hquadmem
  have hfactor := reverse_resolvent_factorization_of_mem_generatedSubmodule s q x hx
  have hassoc : inverse (quadratic s q) * (quadratic s q * x) =
      (inverse (quadratic s q) * quadratic s q) * x := by
    exact (sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q
      (inverse (quadratic s q)) (quadratic s q) x hinv hquadmem hx)).symm
  rw [hfactor, hassoc, inverse_mul _ hquad]
  simp

/-- The resolvent difference restricted to the two-generated associative subalgebra. -/
def restrictedResolvent (s q : RealOctonion) :
    GeneratedSubalgebra s q → GeneratedSubalgebra s q := fun x =>
  ⟨resolventDifference s q x.1, resolventDifference_mem_generatedSubmodule s q x.1 x.2⟩

/-- The candidate restricted inverse, defined when the quadratic denominator is nonzero. -/
def restrictedResolventInverseMap (s q : RealOctonion) (_hquad : quadratic s q ≠ 0) :
    GeneratedSubalgebra s q → GeneratedSubalgebra s q := fun x =>
  ⟨restrictedResolventInverse s q x.1,
    restrictedResolventInverse_mem_generatedSubmodule s q x.1 x.2⟩

/-- Operator form of the first identity in paper equation (8.7). -/
theorem restrictedResolvent_comp_restrictedResolventInverse (s q : RealOctonion)
    (hquad : quadratic s q ≠ 0) :
    restrictedResolvent s q ∘ restrictedResolventInverseMap s q hquad = id := by
  funext x
  apply Subtype.ext
  exact resolventDifference_restrictedResolventInverse_apply s q x.1 hquad x.2

/-- Operator form of the second identity in paper equation (8.7). -/
theorem restrictedResolventInverse_comp_restrictedResolvent (s q : RealOctonion)
    (hquad : quadratic s q ≠ 0) :
    restrictedResolventInverseMap s q hquad ∘ restrictedResolvent s q = id := by
  funext x
  apply Subtype.ext
  exact restrictedResolventInverse_resolventDifference_apply s q x.1 hquad x.2

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
