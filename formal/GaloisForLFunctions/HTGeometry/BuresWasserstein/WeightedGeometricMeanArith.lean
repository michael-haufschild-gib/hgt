import GaloisForLFunctions.HTGeometry.BuresWasserstein.PowerMean

/-!
# Arithmetic–geometric mean inequality and the affine parameter law

Two structural properties of the weighted geometric mean, both obtained by conjugating away the
first argument:

* `X #_s Y ≤ (1-s) X + s Y` — the weighted arithmetic–geometric mean inequality, which is the
  scalar Bernoulli inequality `y^s ≤ (1-s) + s y` fed through the continuous functional calculus;
* `X #_s (X #_t Y) = X #_{t s} Y` — the affine law for the parameter, which is
  `(c^t)^s = c^{ts}`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {X Y : A}

/-- Conjugation preserves the Loewner order. -/
lemma conjugate_le_conjugate {c : A} (hc : IsSelfAdjoint c) {x y : A} (h : x ≤ y) :
    c * x * c ≤ c * y * c := by
  have hnn : (0 : A) ≤ c * (y - x) * c := nonneg_conjugate hc (sub_nonneg.mpr h)
  have hid : c * (y - x) * c = c * y * c - c * x * c := by noncomm_ring
  rw [hid] at hnn
  exact sub_nonneg.mp hnn

/-- **The weighted arithmetic–geometric mean inequality.** -/
theorem wgm_le_arith {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) :
    wgm s X Y ≤ (1 - s) • X + s • Y := by
  have hC : IsStrictlyPositive ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) :=
    conj_strictlyPositive hX hY
  have hspec : ∀ x ∈ spectrum ℝ ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)), 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg hC.nonneg hx
  have hg : Continuous (fun y : ℝ => ((y.toNNReal ^ s : ℝ≥0) : ℝ)) := by
    have heq : (fun y : ℝ => ((y.toNNReal ^ s : ℝ≥0) : ℝ)) = fun y : ℝ => (max y 0) ^ s := by
      funext y
      rw [NNReal.coe_rpow, Real.coe_toNNReal']
    rw [heq]
    exact (Real.continuous_rpow_const hs0).comp (continuous_id.max continuous_const)
  have hcmp : ∀ x ∈ spectrum ℝ ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)),
      ((x.toNNReal ^ s : ℝ≥0) : ℝ) ≤ (1 - s) + s * x := by
    intro x hx
    have hx0 := hspec x hx
    rw [NNReal.coe_rpow, Real.coe_toNNReal x hx0]
    have := rpow_le_one_add_mul_sub_one (x := x) (σ := s) hx0 hs0 hs1
    linarith
  have hmono := cfc_mono (R := ℝ) (a := (X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) hcmp
    hg.continuousOn (by fun_prop)
  have hL : cfc (fun y : ℝ => ((y.toNNReal ^ s : ℝ≥0) : ℝ))
      ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ))
      = ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) ^ s := by
    rw [CFC.rpow_def (a := (X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) (y := s),
      cfc_nnreal_eq_real (fun y : ℝ≥0 => y ^ s)
        ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) hC.nonneg]
  have hR : cfc (fun y : ℝ => (1 - s) + s * y)
      ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ))
      = (1 - s) • (1 : A) + s • ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) := by
    rw [cfc_const_add _ _ _ (by fun_prop), cfc_const_mul _ _ _ (by fun_prop), cfc_id' ℝ _,
      Algebra.algebraMap_eq_smul_one]
  rw [hL, hR] at hmono
  have hconj := conjugate_le_conjugate (c := (X ^ (1/2 : ℝ) : A)) (isSelfAdjoint_rpow X _) hmono
  rw [wgm_def]
  refine hconj.trans (le_of_eq ?_)
  have h1 : (X ^ (1/2 : ℝ) : A) * ((1 - s) • (1 : A)
        + s • ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ))) * X ^ (1/2 : ℝ)
      = (1 - s) • ((X ^ (1/2 : ℝ) : A) * X ^ (1/2 : ℝ))
        + s • ((X ^ (1/2 : ℝ) : A) * ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ))
          * X ^ (1/2 : ℝ)) := by
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [h1, rpow_half_mul_rpow_half hX, sandwich_peel hX Y]

/-- **The affine law for the parameter of the weighted geometric mean.** -/
theorem wgm_wgm {s t : ℝ} (ht : t ≠ 0) (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y) :
    wgm s X (wgm t X Y) = wgm (t * s) X Y := by
  have hC : IsStrictlyPositive ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) :=
    conj_strictlyPositive hX hY
  have hmid : (X ^ (-(1/2) : ℝ) : A) * wgm t X Y * X ^ (-(1/2) : ℝ)
      = ((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) ^ t := by
    rw [wgm_def]
    have hexp : (X ^ (-(1/2) : ℝ) : A)
        * ((X ^ (1/2 : ℝ) : A) * (((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) ^ t)
          * X ^ (1/2 : ℝ)) * X ^ (-(1/2) : ℝ)
        = ((X ^ (-(1/2) : ℝ) : A) * X ^ (1/2 : ℝ))
          * (((X ^ (-(1/2) : ℝ) : A) * Y * X ^ (-(1/2) : ℝ)) ^ t)
          * ((X ^ (1/2 : ℝ) : A) * X ^ (-(1/2) : ℝ)) := by noncomm_ring
    rw [hexp, rpow_neg_half_mul_rpow_half hX, rpow_half_mul_rpow_neg_half hX, one_mul, mul_one]
  rw [wgm_def, hmid, CFC.rpow_rpow _ t s ht hC, wgm_def]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
