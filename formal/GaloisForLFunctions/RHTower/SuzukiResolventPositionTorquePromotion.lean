import GaloisForLFunctions.RHTower.SuzukiStrongResolventLimit
import GaloisForLFunctions.RHTower.SuzukiWeilPositionTorqueCurvature
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Suzuki resolvent promotion to position torque

Suzuki's deficiency vectors solve

`(A_a - lambda) v₊ = exp(x)`,  `(A_a - lambda) v₋ = exp(-x)`.

Put `B = (A_a - rho)⁻¹`, `s = rho - lambda`, and

`F_s = (-lambda) (A_a - lambda)⁻¹
     = ((s-rho)x/(1+s x))(B)`.

Strong convergence `F_s → I` only gives the free defect profile.  The first nontrivial
coefficient is sharper.  On the operator domain `range B`,

`(s-rho)(F_s-I)Bv → -(I+rho B)v`.

Taking the real even--odd position pairing proves

`(-lambda)² Re ⟨c,[(A_a-lambda)⁻¹,X]o⟩
  → Re(⟨A_a o,Xc⟩-⟨A_a c,Xo⟩)`.

Thus the source-native Weil position torque is exactly the second coefficient of Suzuki's
large-negative-shift deficiency response.  No unbounded operator is postulated in Lean: operator
domain membership is expressed canonically as range membership for the bounded resolvent `B`.
All results are unconditional and use no numerical computation.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- Scaled negative-shift resolvent in the coordinate `B = (A-rho)⁻¹`. -/
def suzukiShiftedResolventScale
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (B : H →L[ℂ] H) (rho s : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) B

/-- First-order strong resolvent expansion on `range B`, the bounded-resolvent coordinate of
the operator domain.  If `B=(A-rho)⁻¹`, its limit is `-A(Bv)`. -/
theorem suzukiShiftedResolventScale_firstOrder_on_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) (hinj : Function.Injective B)
    {M rho : ℝ} (hspec : spectrum ℝ B ⊆ Set.Icc 0 M) (v : H) :
    Tendsto
      (fun s : ℝ =>
        (s - rho : ℂ) •
          ((suzukiShiftedResolventScale B rho s -
            ContinuousLinearMap.id ℂ H) (B v)))
      atTop
      (𝓝 (-((ContinuousLinearMap.id ℂ H +
        (rho : ℝ) • B) v))) := by
  let F : ℝ → H →L[ℂ] H := fun s =>
    suzukiShiftedResolventScale B rho s
  have hF :
      Tendsto (fun s : ℝ => F s v) atTop (𝓝 v) := by
    simpa only [F, suzukiShiftedResolventScale] using
      tendsto_resolventFamily_id (rho := rho) hsa hinj hspec v
  have hmap :
      Tendsto
        (fun s : ℝ => -((ContinuousLinearMap.id ℂ H +
          (rho : ℝ) • B) (F s v)))
        atTop
        (𝓝 (-((ContinuousLinearMap.id ℂ H +
          (rho : ℝ) • B) v))) := by
    exact ((ContinuousLinearMap.id ℂ H +
      (rho : ℝ) • B).continuous.continuousAt.tendsto.comp hF).neg
  refine hmap.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hden : ∀ x ∈ spectrum ℝ B, (0 : ℝ) < 1 + s * x := by
    intro x hx
    have hx0 : 0 ≤ x := (hspec hx).1
    nlinarith
  have hcont :
      ContinuousOn (fun x : ℝ => (s - rho) * x / (1 + s * x))
        (spectrum ℝ B) := by
    exact ContinuousOn.div (by fun_prop) (by fun_prop)
      fun x hx => (hden x hx).ne'
  have hone :
      (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H := by
    ext w
    simp
  have hoperator :
      (s - rho : ℝ) •
          ((F s - ContinuousLinearMap.id ℂ H) * B) =
        -(ContinuousLinearMap.id ℂ H + (rho : ℝ) • B) * F s := by
    have hleft :
        (F s - ContinuousLinearMap.id ℂ H) * B =
          cfc (fun x : ℝ =>
            ((s - rho) * x / (1 + s * x) - 1) * x) B := by
      rw [cfc_sub_one_mul_self
        (fun x : ℝ => (s - rho) * x / (1 + s * x)) B hsa hcont]
      simp only [F, suzukiShiftedResolventScale, hone]
    rw [hleft]
    have hg : ContinuousOn
        (fun x : ℝ =>
          ((s - rho) * x / (1 + s * x) - 1) * x)
        (spectrum ℝ B) :=
      (hcont.sub continuousOn_const).mul continuousOn_id
    rw [← cfc_const_mul (s - rho) _ B hg]
    have hbase :
        ContinuousLinearMap.id ℂ H + (rho : ℝ) • B =
          cfc (fun x : ℝ => 1 + rho * x) B := by
      rw [cfc_const_add (1 : ℝ) (fun x : ℝ => rho * x) B,
        cfc_const_mul_id rho B hsa]
      simp only [map_one, hone]
    rw [hbase]
    simp only [F, suzukiShiftedResolventScale]
    have hlin : ContinuousOn (fun x : ℝ => 1 + rho * x)
        (spectrum ℝ B) := by fun_prop
    rw [neg_mul,
      ← cfc_mul _ _ B hlin hcont,
      ← cfc_neg]
    apply cfc_congr
    intro x hx
    have hxden : 1 + s * x ≠ 0 := (hden x hx).ne'
    field_simp
    ring
  have hv :=
    (congrArg (fun T : H →L[ℂ] H => T v) hoperator).symm
  calc
    -((ContinuousLinearMap.id ℂ H + (rho : ℝ) • B) (F s v)) =
        (s - rho : ℝ) •
          ((F s - ContinuousLinearMap.id ℂ H) (B v)) := by
            simpa only [mul_apply_eq_comp, sub_apply,
              ContinuousLinearMap.id_apply, smul_apply, neg_apply] using hv
    _ = (s - rho : ℂ) •
          ((F s - ContinuousLinearMap.id ℂ H) (B v)) := by
            rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := H)]
            norm_cast

/-- The first nonzero large-negative-shift coefficient of Suzuki's real position-commutator
pairing is the operator-domain torque.  The two range vectors are the even and odd exponential
sources. -/
theorem suzukiShiftedResolventScale_positionTorque_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B X : H →L[ℂ] H}
    (hBsa : IsSelfAdjoint B) (hBinj : Function.Injective B)
    (hX : ContinuousLinearMap.adjoint X = X)
    {M rho : ℝ} (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (c₀ s₀ : H) :
    Tendsto
      (fun t : ℝ =>
        (t - rho) *
          ((inner ℂ
              (suzukiShiftedResolventScale B rho t (B c₀))
              (X (B s₀))).re -
            (inner ℂ
              (suzukiShiftedResolventScale B rho t (B s₀))
              (X (B c₀))).re))
      atTop
      (𝓝
        ((inner ℂ
            ((ContinuousLinearMap.id ℂ H + (rho : ℝ) • B) s₀)
            (X (B c₀))).re -
          (inner ℂ
            ((ContinuousLinearMap.id ℂ H + (rho : ℝ) • B) c₀)
            (X (B s₀))).re)) := by
  let F : ℝ → H →L[ℂ] H := fun t =>
    suzukiShiftedResolventScale B rho t
  let Aρ : H →L[ℂ] H :=
    ContinuousLinearMap.id ℂ H + (rho : ℝ) • B
  have hcvec :
      Tendsto
        (fun t : ℝ => (t - rho : ℂ) •
          ((F t - ContinuousLinearMap.id ℂ H) (B c₀)))
        atTop (𝓝 (-(Aρ c₀))) := by
    simpa only [F, Aρ] using
      suzukiShiftedResolventScale_firstOrder_on_range
        hBsa hBinj hspec c₀
  have hsvec :
      Tendsto
        (fun t : ℝ => (t - rho : ℂ) •
          ((F t - ContinuousLinearMap.id ℂ H) (B s₀)))
        atTop (𝓝 (-(Aρ s₀))) := by
    simpa only [F, Aρ] using
      suzukiShiftedResolventScale_firstOrder_on_range
        hBsa hBinj hspec s₀
  have hcpair :
      Tendsto
        (fun t : ℝ =>
          (inner ℂ
            ((t - rho : ℂ) •
              ((F t - ContinuousLinearMap.id ℂ H) (B c₀)))
            (X (B s₀))).re)
        atTop
        (𝓝 ((inner ℂ (-(Aρ c₀)) (X (B s₀))).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (Filter.Tendsto.inner hcvec tendsto_const_nhds)
  have hspair :
      Tendsto
        (fun t : ℝ =>
          (inner ℂ
            ((t - rho : ℂ) •
              ((F t - ContinuousLinearMap.id ℂ H) (B s₀)))
            (X (B c₀))).re)
        atTop
        (𝓝 ((inner ℂ (-(Aρ s₀)) (X (B c₀))).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (Filter.Tendsto.inner hsvec tendsto_const_nhds)
  have hdiff := hcpair.sub hspair
  have hcancel :
      (inner ℂ (B c₀) (X (B s₀))).re =
        (inner ℂ (B s₀) (X (B c₀))).re := by
    calc
      (inner ℂ (B c₀) (X (B s₀))).re =
          (inner ℂ (X (B c₀)) (B s₀)).re := by
            rw [← ContinuousLinearMap.adjoint_inner_right
              X (B c₀) (B s₀), hX]
      _ = (inner ℂ (B s₀) (X (B c₀))).re :=
        inner_re_symm (𝕜 := ℂ) _ _
  convert hdiff using 1
  · funext t
    simp only [F, inner_smul_left, map_sub,
      Complex.conj_ofReal, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, inner_sub_left, sub_apply,
      ContinuousLinearMap.id_apply]
    rw [hcancel]
    ring
  · simp only [Aρ, inner_neg_left, Complex.neg_re]
    ring

end

end GaloisForLFunctions.RHTower
