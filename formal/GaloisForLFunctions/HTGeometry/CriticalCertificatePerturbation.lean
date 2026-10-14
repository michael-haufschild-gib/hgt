import GaloisForLFunctions.HTGeometry.ScalarCertificateGramCompletion
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Summable perturbations of the original critical certificate stream

The coefficients `sqrt(1+c_n²)` define an original certificate stream above the
constant-one reference. Its weight is never Hilbert–Schmidt. Square-summability
of the input coefficients instead gives bounded lineage products and the native
critical-mirage condition, retaining the original nonclosed-range phenomenon.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

def criticalCertificatePerturbation (a : CertStream) : CertStream where
  c n := Real.sqrt (1 + a.c n ^ 2)
  pos n := Real.sqrt_pos.mpr (by positivity)
  bound := Real.sqrt (1 + a.bound ^ 2)
  le_bound n := Real.sqrt_le_sqrt (add_le_add (le_refl 1)
    ((sq_le_sq₀ (a.pos n).le a.bound_pos.le).mpr (a.le_bound n)))

theorem criticalCertificatePerturbation_coefficient (a : CertStream) (n : ℕ) :
    (criticalCertificatePerturbation a).c n = Real.sqrt (1 + a.c n ^ 2) := rfl

theorem criticalCertificatePerturbation_sq (a : CertStream) (n : ℕ) :
    (criticalCertificatePerturbation a).c n ^ 2 = 1 + a.c n ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem one_le_criticalCertificatePerturbation (a : CertStream) (n : ℕ) :
    1 ≤ (criticalCertificatePerturbation a).c n :=
  Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg _))

theorem criticalCertificatePerturbation_excess_le (a : CertStream) (n : ℕ) :
    0 ≤ (criticalCertificatePerturbation a).c n - 1 ∧
      (criticalCertificatePerturbation a).c n - 1 ≤ a.c n ^ 2 / 2 := by
  have h := one_le_criticalCertificatePerturbation a n
  have hs := criticalCertificatePerturbation_sq a n
  constructor
  · linarith
  · nlinarith [sq_nonneg ((criticalCertificatePerturbation a).c n - 1)]

theorem criticalCertificatePerturbation_summable_excess (a : CertStream)
    (ha : Summable (fun n => a.c n ^ 2)) :
    Summable (fun n => (criticalCertificatePerturbation a).c n - 1) :=
  (ha.div_const 2).of_nonneg_of_le
    (fun n => (criticalCertificatePerturbation_excess_le a n).1)
    (fun n => (criticalCertificatePerturbation_excess_le a n).2)

theorem criticalCertificatePerturbation_coefficient_le_exp (a : CertStream) (n : ℕ) :
    (criticalCertificatePerturbation a).c n ≤ Real.exp (a.c n ^ 2 / 2) := by
  have h := (criticalCertificatePerturbation_excess_le a n).2
  linarith [Real.add_one_le_exp (a.c n ^ 2 / 2)]

theorem criticalCertificatePerturbation_certProd_lower (a : CertStream) (N : ℕ) :
    1 ≤ certProd (criticalCertificatePerturbation a).c N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [certProd_succ]
      have hc := one_le_criticalCertificatePerturbation a N
      nlinarith [mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hc)]

theorem criticalCertificatePerturbation_certProd_upper (a : CertStream) (N : ℕ) :
    certProd (criticalCertificatePerturbation a).c N ≤
      Real.exp ((∑ n ∈ Finset.range N, a.c n ^ 2) / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [certProd_succ]
      calc
        _ ≤ Real.exp ((∑ n ∈ Finset.range N, a.c n ^ 2) / 2) *
            Real.exp (a.c N ^ 2 / 2) :=
          mul_le_mul ih (criticalCertificatePerturbation_coefficient_le_exp a N)
            ((criticalCertificatePerturbation a).pos N).le (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]; congr 1; ring

theorem criticalCertificatePerturbation_certRecip_upper (a : CertStream) (N : ℕ) :
    certRecip (criticalCertificatePerturbation a).c N ≤ 1 :=
  (inv_le_one₀ (certProd_pos (criticalCertificatePerturbation a).pos N)).mpr
    (criticalCertificatePerturbation_certProd_lower a N)

theorem criticalCertificatePerturbation_certRecip_lower (a : CertStream)
    (ha : Summable (fun n => a.c n ^ 2)) (N : ℕ) :
    (Real.exp ((∑' n, a.c n ^ 2) / 2))⁻¹ ≤ certRecip (criticalCertificatePerturbation a).c N := by
  have hu : certProd (criticalCertificatePerturbation a).c N ≤
      Real.exp ((∑' n, a.c n ^ 2) / 2) :=
    (criticalCertificatePerturbation_certProd_upper a N).trans
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
        (ha.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _)) (by positivity)))
  simpa only [one_div, certRecip] using
    one_div_le_one_div_of_le (certProd_pos (criticalCertificatePerturbation a).pos N) hu

theorem criticalCertificatePerturbation_not_summable_recip (a : CertStream)
    (ha : Summable (fun n => a.c n ^ 2)) :
    ¬ Summable (fun n => certRecip (criticalCertificatePerturbation a).c n ^ 2) := by
  intro hs
  let δ := (Real.exp ((∑' n, a.c n ^ 2) / 2))⁻¹
  have hδ : 0 < δ := inv_pos.mpr (Real.exp_pos _)
  have hl : ∀ n, δ ^ 2 ≤ certRecip (criticalCertificatePerturbation a).c n ^ 2 := fun n =>
    (sq_le_sq₀ hδ.le (certRecip_pos (criticalCertificatePerturbation a).pos n).le).mpr
      (criticalCertificatePerturbation_certRecip_lower a ha n)
  have hz : δ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hs.tendsto_atTop_zero hl
  exact (not_le_of_gt (sq_pos_of_pos hδ)) hz

theorem criticalCertificatePerturbation_mirage (a : CertStream)
    (ha : IsHilbertSchmidt a.weight) : (criticalCertificatePerturbation a).IsCriticalMirage :=
  (criticalCertificatePerturbation a).isCriticalMirage_of_bounded
    (criticalCertificatePerturbation_not_summable_recip a
      ((scalarCertificate_weight_isHilbertSchmidt_iff a).mp ha))
    (criticalCertificatePerturbation_certRecip_upper a)

theorem criticalCertificatePerturbation_not_hilbertSchmidt (a : CertStream) :
    ¬ IsHilbertSchmidt (criticalCertificatePerturbation a).weight := by
  intro h
  have hs := (scalarCertificate_weight_isHilbertSchmidt_iff _).mp h
  have hl (n : ℕ) : 1 ≤ (criticalCertificatePerturbation a).c n ^ 2 := by
    rw [criticalCertificatePerturbation_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hz : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hs.tendsto_atTop_zero hl
  exact not_le_of_gt one_pos hz

end
end GaloisForLFunctions.HTGeometry
