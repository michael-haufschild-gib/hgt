import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rectangle Volterra transposition

An exact compact-null transposition for a two-variable Volterra primitive.
It is the analytic infrastructure needed to transpose the literal full angular
Goursat kernel; no source, kernel, or boundary datum is replaced.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

private theorem primitive_pair (f phi phip : ℝ → ℂ) (U : ℝ)
    (hf : Continuous f) (hp : Continuous phi) (hd : Continuous phip)
    (hder : ∀ u, HasDerivAt phi (phip u) u) (hU : phi U = 0) :
    (∫ u in (0 : ℝ)..U, (∫ a in (0 : ℝ)..u, f a) * phip u) =
      -(∫ u in (0 : ℝ)..U, f u * phi u) := by
  have hF (u : ℝ) : HasDerivAt (fun v => ∫ a in (0 : ℝ)..v, f a) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 u)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hc : Continuous (fun v => ∫ a in (0 : ℝ)..v, f a) :=
    continuous_iff_continuousAt.mpr (fun v => (hF v).continuousAt)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hc.continuousOn hp.continuousOn (fun u _ => hF u) (fun u _ => hder u)
    (hf.intervalIntegrable 0 U) (hd.intervalIntegrable 0 U)
  simpa only [hU, mul_zero, intervalIntegral.integral_same, zero_mul, sub_self, zero_sub] using h

private theorem double_primitive_pair (F : ℝ × ℝ → ℂ) (phi phip psi psip : ℝ → ℂ)
    (U V : ℝ) (hF : Continuous F) (hp : Continuous phi) (hpd : Continuous phip)
    (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hU : phi U = 0) (hV : psi V = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v) =
      ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * phi u * psi v := by
  have swap (u v : ℝ) :
      (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) =
        ∫ b in (0 : ℝ)..v, ∫ a in (0 : ℝ)..u, F (a, b) := by
    apply intervalIntegral_intervalIntegral_swap
    exact hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have c1 (u : ℝ) : Continuous (fun b => ∫ a in (0 : ℝ)..u, F (a, b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun b a : ℝ => F (a, b)) (hF.comp (continuous_snd.prodMk continuous_fst)) 0 u
  have one (u : ℝ) :
      (∫ b in (0 : ℝ)..V,
        (∫ a in (0 : ℝ)..u, ∫ c in (0 : ℝ)..b, F (a, c)) * phip u * psip b) =
        -phip u * (∫ b in (0 : ℝ)..V, (∫ a in (0 : ℝ)..u, F (a, b)) * psi b) := by
    simp_rw [swap]
    have h := primitive_pair (fun b => ∫ a in (0 : ℝ)..u, F (a, b)) psi psip V (c1 u)
      hs hsd hpsi hV
    have he : (fun b => (∫ c in (0 : ℝ)..b, ∫ a in (0 : ℝ)..u, F (a, c)) * phip u * psip b) =
        fun b => phip u * ((∫ c in (0 : ℝ)..b, ∫ a in (0 : ℝ)..u, F (a, c)) * psip b) := by
      funext b
      ring
    rw [he, intervalIntegral.integral_const_mul, h]
    ring
  have hc : Continuous (fun p : ℝ × ℝ =>
      -phip p.1 * (∫ a in (0 : ℝ)..p.1, F (a, p.2)) * psi p.2) := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : ℝ × ℝ => fun a => F (a, p.2))
      (hF.comp (continuous_snd.prodMk continuous_fst.snd)) continuous_fst
    exact (hpd.comp continuous_fst).neg.mul hh |>.mul (hs.comp continuous_snd)
  have he : (fun u => -phip u *
      (∫ v in (0 : ℝ)..V, (∫ a in (0 : ℝ)..u, F (a, v)) * psi v)) =
      fun u => ∫ v in (0 : ℝ)..V, -phip u * (∫ a in (0 : ℝ)..u, F (a, v)) * psi v := by
    funext u
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  simp_rw [one]
  rw [he]
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun u v : ℝ => -phip u * (∫ a in (0 : ℝ)..u, F (a, v)) * psi v)
    (a := 0) (b := U) (c := 0) (d := V)
    (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))]
  have inner (v : ℝ) :
      (∫ u in (0 : ℝ)..U, -phip u * (∫ a in (0 : ℝ)..u, F (a, v)) * psi v) =
        ∫ u in (0 : ℝ)..U, F (u, v) * phi u * psi v := by
    have h := primitive_pair (fun a => F (a, v)) phi phip U
      (hF.comp (continuous_id.prodMk continuous_const)) hp hpd hphi hU
    have he : (fun u => -phip u * (∫ a in (0 : ℝ)..u, F (a, v)) * psi v) =
        fun u => -((∫ a in (0 : ℝ)..u, F (a, v)) * phip u) * psi v := by
      funext u
      ring
    rw [he, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, h, neg_neg,
      intervalIntegral.integral_mul_const]
  simp_rw [inner]
  symm
  apply intervalIntegral_intervalIntegral_swap
  exact (((hF.mul (hp.comp continuous_fst)).mul (hs.comp continuous_snd)).continuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private theorem double_primitive_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    Continuous (fun p : ℝ × ℝ => ∫ a in (0 : ℝ)..p.1, ∫ b in (0 : ℝ)..p.2, F (a, b)) := by
  have hi : Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ b in (0 : ℝ)..p.1.2, F (p.2, b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : (ℝ × ℝ) × ℝ => fun b => F (p.2, b))
      (hF.comp (continuous_fst.snd.prodMk continuous_snd)) continuous_fst.snd
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun p : ℝ × ℝ => fun a => ∫ b in (0 : ℝ)..p.2, F (a, b)) hi continuous_fst

private theorem vertex_primitive_pair (Q : ℂ) (F : ℝ × ℝ → ℂ)
    (phi phip psi psip : ℝ → ℂ) (U V : ℝ) (hF : Continuous F)
    (hp : Continuous phi) (hpd : Continuous phip) (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hU : phi U = 0) (hV : psi V = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v) =
      Q * phi 0 * psi 0 + ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * phi u * psi v := by
  have hD := double_primitive_continuous F hF
  have h0 : Continuous (fun p : ℝ × ℝ => Q * phip p.1 * psip p.2) := by
    fun_prop
  have h1 : Continuous (fun p : ℝ × ℝ =>
      (∫ a in (0 : ℝ)..p.1, ∫ b in (0 : ℝ)..p.2, F (a, b)) * phip p.1 * psip p.2) :=
    (hD.mul (hpd.comp continuous_fst)).mul (hsd.comp continuous_snd)
  have he (u v : ℝ) :
      (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v =
        Q * phip u * psip v +
          (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v := by
    ring
  simp_rw [he]
  have split (u : ℝ) :
      (∫ v in (0 : ℝ)..V, Q * phip u * psip v +
        (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v) =
      (∫ v in (0 : ℝ)..V, Q * phip u * psip v) +
        ∫ v in (0 : ℝ)..V,
          (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v :=
    intervalIntegral.integral_add
      ((h0.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
      ((h1.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
  simp_rw [split]
  rw [intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => Q * phip u * psip v) h0 0 V).intervalIntegrable 0 U)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ =>
        (∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v) h1 0 V).intervalIntegrable 0 U),
    double_primitive_pair F phi phip psi psip U V hF hp hpd hs hsd hphi hpsi hU hV]
  congr 1
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hphi u) (hpd.intervalIntegrable 0 U),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hpsi v) (hsd.intervalIntegrable 0 V), hU, hV]
  ring

/-- Compact-null transposition of a literal rectangle Volterra representation. -/
theorem rectangle_volterra_transposition (K F : ℝ × ℝ → ℂ) (Q : ℂ) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hF : Continuous F)
    (hK : ∀ u v, 0 ≤ u → 0 ≤ v →
      K (u, v) = Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b))
    (phi phip psi psip : ℝ → ℂ)
    (hp : Continuous phi) (hpd : Continuous phip) (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hpU : phi U = 0) (hsV : psi V = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * phip u * psip v) =
      Q * phi 0 * psi 0 +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * phi u * psi v := by
  have hpair := vertex_primitive_pair Q F phi phip psi psip U V hF hp hpd hs hsd hphi hpsi hpU hsV
  have hleft : (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * phip u * psip v) =
      ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
        (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
    have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
    change K (u, v) * phip u * psip v =
      (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * phip u * psip v
    rw [hK u v hu0 hv0]
  rw [hleft, hpair]

end

end GaloisForLFunctions.HTGeometry
