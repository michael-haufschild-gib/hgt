import GaloisForLFunctions.RHTower.ChiCubicNormalTransportJets

/-!
# Exact normal transport of the complete normalized cubic

The reciprocal phase conjugates the normalized normal operator to the
transport with proved uniform all-order moving-edge jets. Iteration is
proved for the literal coupled normalized weight, using its produced
regularity, and exact positive dilation attaches the original amplitude
with every cutoff, Gaussian and logarithmic factor retained.

Weighted Fourier control and complete shrinking-cone source cancellation
remain separate obligations. No analytic estimate is assumed here.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private abbrev E := BAGPhysicalSpace
private def U : Set E := {v | 0 < v 2}
private def ax (i : Fin 3) : E := EuclideanSpace.single i 1
private def D (i : Fin 3) (f : E → ℂ) (v : E) : ℂ := fderiv ℝ f v (ax i)
private def P (i : Fin 3) : E →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
/-- The reciprocal oscillation after exact physical dilation. -/
def bagCubicNormalizedReciprocalPhase (N : ℝ) (v : E) : ℂ :=
  Complex.exp ((2*Real.pi*Complex.I : ℂ)*(N : ℂ)*(v 0 : ℂ)*(v 1 : ℂ)/(v 2 : ℂ))/(v 2 : ℂ)
private abbrev K := bagCubicNormalizedReciprocalPhase
private def a (N : ℝ) : ℂ := (2*Real.pi*Complex.I : ℂ)*(N : ℂ)
private def b (N : ℝ) (v : E) : ℂ := a N*(v 0 : ℂ)/(v 2 : ℂ)

private theorem U_open : IsOpen U :=
  isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3)).continuous

private theorem smooth_D {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (i : Fin 3) :
    ContDiffOn ℝ ∞ (D i f) U :=
  (hf.fderiv_of_isOpen U_open (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem smooth_K (N : ℝ) : ContDiffOn ℝ ∞ (K N) U := by
  intro v hv
  have hp (i : Fin 3) : ContDiffAt ℝ ∞ (fun v : E => (v i : ℂ)) v := (P i).contDiff.contDiffAt
  have hr : (v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  simpa only [K, bagCubicNormalizedReciprocalPhase, a, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
    ((((contDiffAt_const (c := a N)).mul (hp 0)).mul (hp 1)).mul ((hp 2).inv hr)).cexp.mul ((hp 2).inv hr) |>.contDiffWithinAt

private theorem smooth_b (N : ℝ) : ContDiffOn ℝ ∞ (b N) U := by
  intro v hv
  change ContDiffWithinAt ℝ ∞ (fun w : E => a N*(w 0 : ℂ)/(w 2 : ℂ)) U v
  simpa only [div_eq_mul_inv] using!
    (((contDiffAt_const (c := a N)).mul (P 0).contDiff.contDiffAt).mul
      ((P 2).contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr (ne_of_gt hv)))).contDiffWithinAt

private theorem K_deriv (N : ℝ) {v : E} (hv : v ∈ U) :
    HasFDerivAt (K N)
      ((v 2 : ℂ)⁻¹ • (Complex.exp (a N*(v 0 : ℂ)*(v 1 : ℂ)/(v 2 : ℂ)) •
        ((v 2 : ℂ)⁻¹ • ((v 1 : ℂ) • (a N • P 0) + (a N*(v 0 : ℂ)) • P 1) -
          (a N*(v 0 : ℂ)*(v 1 : ℂ)/(v 2 : ℂ)^2) • P 2)) -
          (Complex.exp (a N*(v 0 : ℂ)*(v 1 : ℂ)/(v 2 : ℂ))/(v 2 : ℂ)^2) • P 2) v := by
  have hp (i : Fin 3) : HasFDerivAt (fun v : E => (v i : ℂ)) (P i) v := (P i).hasFDerivAt
  have hr : (v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  have hi := (hasDerivAt_inv hr).comp_hasFDerivAt v (hp 2)
  have hd := (((((hp 0).const_mul (a N)).mul (hp 1)).mul hi).cexp).mul hi
  convert! hd using 1
  ext w
  simp only [add_apply, sub_apply, smul_apply, Pi.mul_apply, Function.comp_apply, smul_eq_mul]
  simp only [div_eq_mul_inv]
  ring

private theorem K_D0 (N : ℝ) {v : E} (hv : v ∈ U) :
    D 0 (K N) v = a N*(v 1 : ℂ)/(v 2 : ℂ)*K N v := by
  unfold D
  rw [(K_deriv N hv).fderiv]
  simp [P, ax, K, bagCubicNormalizedReciprocalPhase, a]
  ring

private theorem K_D1 (N : ℝ) {v : E} (hv : v ∈ U) :
    D 1 (K N) v = b N v * K N v := by
  unfold D
  rw [(K_deriv N hv).fderiv]
  simp [P, ax, K, bagCubicNormalizedReciprocalPhase, b, a]
  ring

private theorem K_D2 (N : ℝ) {v : E} (hv : v ∈ U) :
    D 2 (K N) v = (-1/(v 2 : ℂ) - a N*(v 0 : ℂ)*(v 1 : ℂ)/(v 2 : ℂ)^2)*K N v := by
  have hr : (v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  unfold D
  rw [(K_deriv N hv).fderiv]
  simp [P, ax, K, bagCubicNormalizedReciprocalPhase, a]
  field_simp
  ring

private theorem b_D0 (N : ℝ) {v : E} (hv : v ∈ U) :
    D 0 (b N) v = a N/(v 2 : ℂ) := by
  have hr : (v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  have hp (i : Fin 3) : HasFDerivAt (fun v : E => (v i : ℂ)) (P i) v := (P i).hasFDerivAt
  have hd := ((hp 0).const_mul (a N)).mul ((hasDerivAt_inv hr).comp_hasFDerivAt v (hp 2))
  change fderiv ℝ (fun v : E => a N*(v 0 : ℂ)/(v 2 : ℂ)) v (ax 0) = _
  have hd' : HasFDerivAt (fun v : E => a N*(v 0 : ℂ)/(v 2 : ℂ))
      ((a N*(v 0 : ℂ)) • (-((v 2 : ℂ)^2)⁻¹ • P 2) + (v 2 : ℂ)⁻¹ • (a N • P 0)) v := by
    simpa only [div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! hd
  rw [hd'.fderiv]
  simp [P, ax, div_eq_mul_inv, mul_comm]

private theorem D_mul (i : Fin 3) {f g : E → ℂ} {v : E}
    (hf : DifferentiableAt ℝ f v) (hg : DifferentiableAt ℝ g v) :
    D i (fun w => f w*g w) v = D i f v*g v + f v*D i g v := by
  simp only [D, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

private theorem D_add (i : Fin 3) {f g : E → ℂ} {v : E}
    (hf : DifferentiableAt ℝ f v) (hg : DifferentiableAt ℝ g v) :
    D i (fun w => f w+g w) v = D i f v + D i g v := by
  simp only [D, fderiv_fun_add hf hg, add_apply]

private theorem D_congr (i : Fin 3) {f g : E → ℂ} {v : E} (he : f =ᶠ[𝓝 v] g) :
    D i f v = D i g v := by rw [D, D, he.fderiv_eq]

private theorem normal_conjugation (N : {r : ℝ // r ≠ 0}) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) {v : E} (hv : v ∈ U) :
    D 2 (fun w => K N.1 w*f w) v -
      (Complex.I/(2*Real.pi*(N.1 : ℂ))) * D 0 (D 1 (fun w => K N.1 w*f w)) v =
        K N.1 v * bagCubicNormalizedTransport (1/N.1) f v := by
  have hd {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U) {w : E} (hw : w ∈ U) :
      DifferentiableAt ℝ g w := (hg.contDiffAt (U_open.mem_nhds hw)).differentiableAt (by simp)
  have hK := smooth_K N.1
  have hb := smooth_b N.1
  have hD1 := smooth_D hf 1
  have he : D 1 (fun w => K N.1 w*f w) =ᶠ[𝓝 v]
      (fun w => b N.1 w*K N.1 w*f w+K N.1 w*D 1 f w) := by
    filter_upwards [U_open.mem_nhds hv] with w hw
    rw [D_mul 1 (hd hK hw) (hd hf hw), K_D1 N.1 hw]
  rw [D_congr 0 he, D_add 0 (hd ((hb.mul hK).mul hf) hv) (hd (hK.mul hD1) hv),
    D_mul 0 (hd (hb.mul hK) hv) (hd hf hv), D_mul 0 (hd hb hv) (hd hK hv),
    D_mul 0 (hd hK hv) (hd hD1 hv), D_mul 2 (hd hK hv) (hd hf hv),
    K_D0 N.1 hv, K_D2 N.1 hv, b_D0 N.1 hv]
  have hr : (v 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
  have hN : (N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr N.2
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change _ = K N.1 v*(D 2 f v + ((v 0/v 2 : ℝ) : ℂ)*D 0 f v +
    ((v 1/v 2 : ℝ) : ℂ)*D 1 f v + (-Complex.I/(2*Real.pi : ℂ)) • ((1/N.1 : ℝ) • D 0 (D 1 f) v))
  simp only [Complex.real_smul, smul_eq_mul]
  dsimp only [b, a]
  push_cast
  field_simp
  ring_nf
  have hi3 : Complex.I^3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  simp only [Complex.I_sq, hi3]
  ring

/-- The normalized normal differential operator at reciprocal scale. -/
def bagCubicNormalizedNormalOperator (N : ℝ) (f : E → ℂ) (v : E) : ℂ :=
  D 2 f v - (Complex.I/(2*Real.pi*(N : ℂ))) * D 0 (D 1 f) v

private theorem normal_congr (N : ℝ) {f g : E → ℂ} (he : EqOn f g U)
    {v : E} (hv : v ∈ U) :
    bagCubicNormalizedNormalOperator N f v = bagCubicNormalizedNormalOperator N g v := by
  have he' {w : E} (hw : w ∈ U) : f =ᶠ[𝓝 w] g :=
    Filter.mem_of_superset (U_open.mem_nhds hw) he
  have heD : D 1 f =ᶠ[𝓝 v] D 1 g := by
    filter_upwards [U_open.mem_nhds hv] with w hw
    exact D_congr 1 (he' hw)
  unfold bagCubicNormalizedNormalOperator
  rw [D_congr 2 (he' hv), D_congr 0 heD]

/-- Exact iterated conjugation for the ACTUAL coupled normalized weight.
Every derivative on the oscillation has been eliminated; the surviving
transport is the one with proved uniform all-order moving-edge jets. -/
theorem bagCubicNormalizedNormalOperator_iterate_actual (k : ℕ)
    (N : {r : ℝ // r ≠ 0})
    (δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)})
    (h : {r : ℝ // r ∈ Icc (0 : ℝ) 1})
    (v : {v : BAGPhysicalSpace // 0 < v 2}) :
    ((bagCubicNormalizedNormalOperator N.1)^[k]
      (fun w => bagCubicNormalizedReciprocalPhase N.1 w *
        bagCubicNormalizedPhysicalWeight δ.1 h.1 w)) v.1 =
      bagCubicNormalizedReciprocalPhase N.1 v.1 *
        ((bagCubicNormalizedTransport (1/N.1))^[k]
          (bagCubicNormalizedPhysicalWeight δ.1 h.1)) v.1 := by
  have he : ∀ j : ℕ, EqOn ((bagCubicNormalizedNormalOperator N.1)^[j]
      (fun w => K N.1 w * bagCubicNormalizedPhysicalWeight δ.1 h.1 w))
      (fun w => K N.1 w * ((bagCubicNormalizedTransport (1/N.1))^[j]
        (bagCubicNormalizedPhysicalWeight δ.1 h.1)) w) U := by
    intro j
    induction j with
    | zero => intro w hw; rfl
    | succ j ih =>
      intro w hw
      rw [Function.iterate_succ_apply']
      rw [normal_congr N.1 ih hw]
      exact (normal_conjugation N
        (bagCubicNormalizedTransport_iterate_contDiffOn j δ h (1/N.1)) hw).trans
          (by rw [Function.iterate_succ_apply'])
  exact he k v.2

/-- Exact dilation attaches the transported normalized weight to the ENTIRE
original physical amplitude, with all three logarithmic factors retained. -/
theorem bagCubicPhysicalAmplitude_normalized_phase_weight
    (N : {r : ℝ // 1 < r}) (H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)})
    (v : {v : BAGPhysicalSpace // 0 < v 2}) :
    bagCubicPhysicalAmplitude N.1 (bagCubicControlledBandCutoff N.1 H.1) (N.1 • v.1) =
      (2*Real.pi/(N.1*Real.log N.1^3) : ℂ) *
        bagCubicNormalizedReciprocalPhase N.1 v.1 *
          bagCubicNormalizedPhysicalWeight (H.1/N.1) (1/Real.log N.1) v.1 := by
  have hN : N.1 ≠ 0 := (lt_trans zero_lt_one N.2).ne'
  have hNC : (N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN
  have hL : (Real.log N.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos N.2).ne'
  have hr : (v.1 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt v.2)
  have hs (i : Fin 3) : bagCubicMellinSliceValue N.1
      (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*v.1 i) =
      bagCubicNormalizedSlice (H.1/N.1) (1/Real.log N.1) (v.1 i)/(Real.log N.1 : ℂ) := by
    apply (eq_div_iff hL).mpr
    simpa only [mul_comm] using bagCubicNormalizedSlice_eq_actual N H (v.1 i)
  have he : N.1*v.1 0*(N.1*v.1 1)/((N.1*v.1 2)*N.1) = v.1 0*v.1 1/v.1 2 := by
    field_simp
  have hk : (2*Real.pi*Complex.I : ℂ)*((N.1*v.1 0 : ℝ) : ℂ)*
      ((N.1*v.1 1 : ℝ) : ℂ)/((N.1*v.1 2 : ℝ) : ℂ) =
      (2*Real.pi*Complex.I : ℂ)*(N.1 : ℂ)*(v.1 0 : ℂ)*(v.1 1 : ℂ)/(v.1 2 : ℂ) := by
    push_cast
    field_simp
  rw [bagCubicPhysicalAmplitude_weight_phase]
  change (2*Real.pi : ℂ) *
    bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*v.1 0) *
    bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*v.1 1) *
    star (bagCubicMellinSliceValue N.1 (bagCubicControlledBandCutoff N.1 H.1) 0 (N.1*v.1 2)) *
    (bagPhysicalHeightWindow (N.1*v.1 0*(N.1*v.1 1)/((N.1*v.1 2)*N.1)) : ℂ) *
    bagCubicReciprocalPhase (N.1*v.1 0) (N.1*v.1 1) (N.1*v.1 2) = _
  rw [hs 0, hs 1, hs 2, he]
  simp only [bagCubicReciprocalPhase, hk, bagCubicNormalizedReciprocalPhase,
    bagCubicNormalizedPhysicalWeight, star_div₀, Complex.star_def, Complex.conj_ofReal]
  push_cast
  field_simp

end RHTower.BAGTrace
