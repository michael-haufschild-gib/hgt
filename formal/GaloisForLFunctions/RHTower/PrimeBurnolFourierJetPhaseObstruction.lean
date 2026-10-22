import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetClosure
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSymbol

/-!
# Position-square obstruction for the physical Fourier jet

Even Schwartz Gaussians with a quadratic unimodular phase and normalized dilation
exclude a position-square graph estimate for the actual weak Fourier jet. After
multiplication by the square of the dilation parameter, the proposed estimate has
positive constant left side and a continuous right side tending to zero.
-/

open Complex MeasureTheory Set Filter Topology
open scoped SchwartzMap Real
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private def jetPhase (x : ℝ) : ℂ := Complex.exp ((π*x^2 : ℝ)*Complex.I)

private theorem jetPhase_temperate : Function.HasTemperateGrowth jetPhase := by
  have hp : Function.HasTemperateGrowth (fun x : ℝ => π*x^2) := by fun_prop
  have hc := Function.Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_realCos.comp hp)
  have hs := Function.Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_realSin.comp hp)
  have he : jetPhase = (Complex.ofReal ∘ Real.cos ∘ fun x : ℝ => π*x^2) +
      (Complex.ofReal ∘ Real.sin ∘ fun x : ℝ => π*x^2) * (fun _ => Complex.I) := by
    funext x
    change Complex.exp ((π*x^2 : ℝ)*Complex.I) = _
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rfl
  rw [he]
  exact hc.add (hs.mul (Function.HasTemperateGrowth.const Complex.I))

private theorem jetPhase_norm (x : ℝ) : ‖jetPhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I (π*x^2)

private def jetChirp (φ : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ jetPhase φ

private theorem jetChirp_apply (φ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    jetChirp φ x = jetPhase x * φ x := by
  rw [jetChirp, SchwartzMap.smulLeftCLM_apply_apply jetPhase_temperate, smul_eq_mul]

private abbrev lp (φ : 𝓢(ℝ,ℂ)) : SoninL2 := φ.toLp 2 volume
private abbrev q2 (φ : 𝓢(ℝ,ℂ)) := mulXCLM (mulXCLM φ)

private theorem jetChirp_norm (φ : 𝓢(ℝ,ℂ)) : ‖lp (jetChirp φ)‖ = ‖lp φ‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  rw [jetChirp_apply, norm_mul, jetPhase_norm, one_mul]

private theorem jetChirp_q2 (φ : 𝓢(ℝ,ℂ)) : q2 (jetChirp φ) = jetChirp (q2 φ) := by
  ext x
  simp only [q2, mulXCLM_apply, jetChirp_apply]
  ring

private def jetScale (r : ℝ) (hr : 0 < r) (φ : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (Real.sqrt r : ℂ) • schwartzDilate φ hr.ne'

private theorem jetScale_apply (r : ℝ) (hr : 0 < r) (φ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    jetScale r hr φ x = (Real.sqrt r : ℂ) * φ (r*x) := rfl

private theorem jetScale_lp (r : ℝ) (hr : 0 < r) (φ : 𝓢(ℝ,ℂ)) :
    lp (jetScale r hr φ) = dilation r hr (lp φ) := by
  apply Lp.ext
  have hc := (φ.coeFn_toLp 2 volume).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [(jetScale r hr φ).coeFn_toLp 2 volume, dilation_ae r hr (lp φ), hc]
    with x hs hd hφ
  change (lp φ) (r*x) = φ (r*x) at hφ
  rw [hs, hd, hφ, jetScale_apply]

private theorem jetScale_q2 (r : ℝ) (hr : 0 < r) (φ : 𝓢(ℝ,ℂ)) :
    q2 (jetScale r hr φ) = (r : ℂ)⁻¹^2 • jetScale r hr (q2 φ) := by
  ext x
  simp only [q2, mulXCLM_apply, jetScale_apply, _root_.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

private def jetWave (r : ℝ) (hr : 0 < r) : 𝓢(ℝ,ℂ) :=
  jetChirp (jetScale r hr gaussianSchwartz)

private theorem jetWave_norm (r : ℝ) (hr : 0 < r) :
    ‖lp (jetWave r hr)‖ = ‖lp gaussianSchwartz‖ := by
  rw [jetWave, jetChirp_norm, jetScale_lp, (dilation r hr).norm_map]

private theorem jetWave_q2_norm (r : ℝ) (hr : 0 < r) :
    ‖lp (q2 (jetWave r hr))‖ = r⁻¹^2 * ‖lp (q2 gaussianSchwartz)‖ := by
  rw [jetWave, jetChirp_q2, jetChirp_norm, jetScale_q2]
  change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    ((r : ℂ)⁻¹^2 • jetScale r hr (q2 gaussianSchwartz))‖ = _
  rw [map_smul, norm_smul]
  change ‖(r : ℂ)⁻¹^2‖ * ‖lp (jetScale r hr (q2 gaussianSchwartz))‖ = _
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    jetScale_lp, (dilation r hr).norm_map]

private def jetExponent (r : ℝ) : ℂ := (π : ℂ)*(Complex.I-(r : ℂ)^2)

private theorem jetWave_apply (r : ℝ) (hr : 0 < r) (x : ℝ) :
    jetWave r hr x = (Real.sqrt r : ℂ) * Complex.exp (jetExponent r*(x : ℂ)^2) := by
  rw [jetWave, jetChirp_apply, jetScale_apply, gaussianSchwartz_eq_cexp]
  unfold jetPhase
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [jetExponent, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

private theorem jetWave_hasDerivAt (r : ℝ) (hr : 0 < r) (x : ℝ) :
    HasDerivAt (jetWave r hr) (2*jetExponent r*(x : ℂ)*jetWave r hr x) x := by
  have h := (((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (jetExponent r)).cexp.const_mul
    (Real.sqrt r : ℂ)
  have hf : (fun y : ℝ => (Real.sqrt r : ℂ) *
      Complex.exp (jetExponent r*(y : ℂ)^2)) = ⇑(jetWave r hr) := by
    funext y
    exact (jetWave_apply r hr y).symm
  change HasDerivAt (fun y : ℝ => (Real.sqrt r : ℂ) *
    Complex.exp (jetExponent r*(y : ℂ)^2)) _ x at h
  rw [hf] at h
  convert h using 1
  rw [jetWave_apply]
  simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one,
    Complex.ofReal_one, mul_one]
  ring

private theorem jetWave_deriv (r : ℝ) (hr : 0 < r) :
    derivSCLM (jetWave r hr) = (2*jetExponent r) • mulXCLM (jetWave r hr) := by
  ext x
  rw [derivSCLM_apply, (jetWave_hasDerivAt r hr x).deriv,
    _root_.smul_apply, mulXCLM_apply, smul_eq_mul, mul_assoc]

private theorem jetWave_deriv2 (r : ℝ) (hr : 0 < r) :
    derivSCLM (derivSCLM (jetWave r hr)) =
      (2*jetExponent r) • jetWave r hr + (4*(jetExponent r)^2) • q2 (jetWave r hr) := by
  ext x
  rw [jetWave_deriv, derivSCLM_apply]
  have h := (((hasDerivAt_id x).ofReal_comp.const_mul (2*jetExponent r)).mul
    (jetWave_hasDerivAt r hr x)).deriv
  have hf : ⇑((2*jetExponent r) • mulXCLM (jetWave r hr) : 𝓢(ℝ,ℂ)) =
      fun y : ℝ => (2*jetExponent r)*(y : ℂ)*jetWave r hr y := by
    funext y
    simp only [_root_.smul_apply, mulXCLM_apply, smul_eq_mul, mul_assoc]
  change deriv (fun y : ℝ => (2*jetExponent r)*(y : ℂ)*jetWave r hr y) x = _ at h
  rw [hf, h]
  simp only [add_apply, _root_.smul_apply, smul_eq_mul, q2, mulXCLM_apply,
    Complex.ofReal_one, id_eq]
  ring


private theorem jetWave_weak (r : ℝ) (hr : 0 < r) :
    burnolJetWeakTest (jetWave r hr) =
      (4*jetExponent r) • lp (jetWave r hr) +
      (8*(π : ℂ)^2+8*(jetExponent r)^2) • lp (q2 (jetWave r hr)) := by
  have he (φ : 𝓢(ℝ,ℂ)) :
      creationCLM (creationCLM φ) + annihilationCLM (annihilationCLM φ) =
        (8*(π : ℂ)^2) • q2 φ + (2 : ℂ) • derivSCLM (derivSCLM φ) := by
    simp only [creationCLM_eq, annihilationCLM_eq, map_sub, map_add, map_smul, q2]
    module
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (creationCLM (creationCLM (jetWave r hr)) + annihilationCLM (annihilationCLM (jetWave r hr))) = _
  rw [he, jetWave_deriv2, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  change (8*(π : ℂ)^2) • lp (q2 (jetWave r hr)) +
    (2 : ℂ) • ((2*jetExponent r) • lp (jetWave r hr) +
      (4*(jetExponent r)^2) • lp (q2 (jetWave r hr))) = _
  module

private theorem jetWave_even (r : ℝ) (hr : 0 < r) : lp (jetWave r hr) ∈ evenSubspace := by
  apply (mem_evenSubspace_iff _).mpr
  apply Lp.ext
  have hn := ((jetWave r hr).coeFn_toLp 2 volume).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (lp (jetWave r hr)), hn, (jetWave r hr).coeFn_toLp 2 volume]
    with x href hn hx
  change lp (jetWave r hr) (-x) = jetWave r hr (-x) at hn
  rw [href, hn, hx, jetWave_apply, jetWave_apply]
  simp only [Complex.ofReal_neg, neg_sq]

private theorem q2_gaussian_norm_pos : 0 < ‖lp (q2 gaussianSchwartz)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he : q2 gaussianSchwartz = 0 := SchwartzMap.injective_toLp 2 volume (by
    change lp (q2 gaussianSchwartz) = (SchwartzMap.toLpCLM ℂ ℂ 2 volume) 0
    rw [map_zero]
    exact h)
  have hh := congrArg (fun φ : 𝓢(ℝ,ℂ) => φ 1) he
  simp only [q2, mulXCLM_apply, Complex.ofReal_one, one_mul, zero_apply,
    gaussianSchwartz_apply, gaussReal, one_pow, mul_one] at hh
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hh

/-- Position-square control fails even after the physical input norm is added to the weak jet. -/
theorem burnolJetWeakTest_no_position_graph_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓢(ℝ,ℂ), lp φ ∈ evenSubspace →
      ‖lp (q2 φ)‖ ≤ C * (‖lp φ‖ + ‖burnolJetWeakTest φ‖) := by
  rintro ⟨C,hC,hbound⟩
  let a := ‖lp gaussianSchwartz‖
  let b := ‖lp (q2 gaussianSchwartz)‖
  have hs (r : ℝ) (hr : 0 < r) :
      b ≤ C*(r^2*a + r^2*‖4*jetExponent r‖*a +
        ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*b) := by
    have hw : ‖burnolJetWeakTest (jetWave r hr)‖ ≤
        ‖4*jetExponent r‖*a + ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*(r⁻¹^2*b) := by
      rw [jetWave_weak]
      have hh := norm_add_le ((4*jetExponent r) • lp (jetWave r hr))
        ((8*(π : ℂ)^2+8*(jetExponent r)^2) • lp (q2 (jetWave r hr)))
      rw [norm_smul, norm_smul, jetWave_norm, jetWave_q2_norm] at hh
      exact hh
    have h := (hbound (jetWave r hr) (jetWave_even r hr)).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right hw _) hC)
    rw [jetWave_q2_norm, jetWave_norm] at h
    have hi : r^2*r⁻¹^2 = 1 := by field_simp
    calc
      b = r^2*(r⁻¹^2*b) := by rw [← mul_assoc,hi,one_mul]
      _ ≤ r^2*(C*(a+(‖4*jetExponent r‖*a+
          ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*(r⁻¹^2*b)))) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg r)
      _ = C*(r^2*a+r^2*‖4*jetExponent r‖*a+
          ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*(r^2*r⁻¹^2)*b) := by ring
      _ = _ := by rw [hi]; ring
  have hz : 8*(π : ℂ)^2+8*(jetExponent 0)^2 = 0 := by
    simp only [jetExponent, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      mul_pow, Complex.I_sq]
    ring
  have hc : Continuous (fun r : ℝ => C*(r^2*a+r^2*‖4*jetExponent r‖*a+
      ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*b)) := by unfold jetExponent; fun_prop
  have hl : Tendsto (fun r : ℝ => C*(r^2*a+r^2*‖4*jetExponent r‖*a+
      ‖8*(π : ℂ)^2+8*(jetExponent r)^2‖*b)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add, hz, norm_zero, mul_zero]
      using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb : b ≤ 0 := ge_of_tendsto hl (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hs r hr)
  exact (not_le_of_gt q2_gaussian_norm_pos) hb

end RHTower
