import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure

/-!
# A single continued prime--Gamma source sequence gates RH

The continued-Cauchy closure theorem supplies an unconditional sequence of finite algebraic
prime--Gamma source vectors converging to the canonical Xi--Hurwitz orientation vector.  Continuity
of the Weil Hilbert quadratic form makes eventual nonnegativity along this one sequence sufficient
for RH.  Conversely, RH fixes critical-line reflection on every multiplicity copy, so the form is
nonnegative on the entire Hilbert carrier and hence on every term of the sequence.

This module does not prove the remaining source sign.  It shrinks its theorem interface from all
regular Cauchy points, or even the whole continued-source algebraic span, to one unconditional
countable sequence inside the domain where the continued prime--Gamma value formula is valid.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Under RH, critical-line reflection fixes each multiplicity-exact Xi zero copy. -/
theorem xiZeroCopyLineConjEquiv_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q = q := by
  have hfst : (xiZeroCopyLineConjEquiv q).1 = q.1 := by
    apply Subtype.ext
    change 1 - (starRingEnd ℂ) (q.1 : ℂ) = (q.1 : ℂ)
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
      linarith
    · simp
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun ρ : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) hfst)).2
  simp [xiZeroCopyLineConjEquiv, xiZeroCopyConjEquiv,
    xiZeroCopyReflectEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrRight,
    Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/-- Under RH the unconditional reflection quadratic form is nonnegative on every `ell²` vector,
not only on vectors represented by a test function. -/
theorem xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    0 ≤ xiWeilHilbertQuadratic v := by
  have hJ : xiWeilLineConjLp v = v := by
    apply Subtype.ext
    funext q
    rw [xiWeilLineConjLp_apply,
      xiZeroCopyLineConjEquiv_eq_of_riemannHypothesis hRH q]
  rw [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry_apply, hJ]
  exact (inner_self_nonneg (𝕜 := ℂ) (x := v))

/-- **One-sequence continued-source criterion.**  There is an unconditional sequence of finite
vectors in the continued prime--Gamma Cauchy source span which converges to the canonical
orientation vector and whose eventual Weil nonnegativity is equivalent to RH. -/
theorem exists_continuedCauchyCore_sequence_eventually_nonnegative_iff_riemannHypothesis :
    ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
      Tendsto V atTop (nhds xiHurwitzOrientationVector) ∧
      Tendsto (fun n => xiWeilHilbertQuadratic (V n)) atTop
        (nhds (-xiHurwitzOrientationEnergy)) ∧
      (RiemannHypothesis ↔
        ∀ᶠ n in atTop, 0 ≤ xiWeilHilbertQuadratic (V n)) := by
  obtain ⟨V, hVmem, hV, hQ⟩ :=
    xiHurwitzOrientationEnergy_continuedCauchy_reconstruction
  refine ⟨V, hVmem, hV, hQ, ?_⟩
  constructor
  · intro hRH
    exact Eventually.of_forall
      (fun n => xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH (V n))
  · intro hnonneg
    have hlimit : 0 ≤ -xiHurwitzOrientationEnergy :=
      ge_of_tendsto hQ hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr
    linarith [xiHurwitzOrientationEnergy_nonneg]

end


end RHTower
