import GaloisForLFunctions.RHTower.SuzukiDeBrangesRepresentation
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

noncomputable section

/-!
# Point evaluation and the sharp involution on `E K(Θ)`

The lift of a model-space element is its de Branges series.  Pairing the reproducing kernel of the
model space against the basis expansion evaluates the lift:

```text
(E F)(w) = E(w) ⟪k_w, F⟫,    Im w > 0,
```

so point evaluation above the axis is a bounded linear functional — the first de Branges axiom.

For the second, the involution `κ F = Θ conj F` is anti-unitary and sends each basis vector `F_γ` to
`-F_γ`, while each de Branges vector satisfies `V^♯ = -V` because `Ξ` is real on the real axis.  The
two signs cancel, so the lift of `κ F` is the sharp reflection of the lift of `F`, and `κ` preserves
the norm.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The entire representative of `E F` for `F` in the model space. -/
def suzukiDeBrangesLift (hRH : RiemannHypothesis) (F : Lp ℂ 2 (volume : Measure ℝ)) : ℂ → ℂ :=
  suzukiDeBrangesSeries fun ρ => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)

theorem summable_suzukiDeBrangesLiftCoef (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    Summable fun ρ : XiDivisorSupport => ‖(inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)‖ ^ 2 :=
  (hasSum_normSq_inner_suzukiFGammaFamily hRH hF).summable

theorem differentiable_suzukiDeBrangesLift (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    Differentiable ℂ (suzukiDeBrangesLift hRH F) :=
  differentiable_suzukiDeBrangesSeries hRH (summable_suzukiDeBrangesLiftCoef hRH hF)

theorem suzukiDeBrangesLift_div_ae (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    (fun x : ℝ => suzukiDeBrangesLift hRH F ((x : ℝ) : ℂ)
        / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      =ᵐ[volume] (F : ℝ → ℂ) :=
  suzukiDeBrangesSeries_div_ae hRH hF

theorem memDeBranges_suzukiDeBrangesLift (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    MemDeBranges (suzukiDeBrangesLift hRH F) :=
  memDeBranges_suzukiDeBrangesSeries hRH hF

theorem hasSum_suzukiDeBrangesLift (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) (z : ℂ) :
    HasSum (fun ρ : XiDivisorSupport => (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
        * suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) z)
      (suzukiDeBrangesLift hRH F z) :=
  (summable_deBrangesSeries_at hRH (summable_suzukiDeBrangesLiftCoef hRH hF) z).hasSum

/-! ## Point evaluation -/

/-- **Point evaluation above the axis.**  The lift is `E(w)` times the reproducing pairing. -/
theorem suzukiDeBrangesLift_apply (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    suzukiDeBrangesLift hRH F w
      = xiHedenmalmDeBrangesE w
        * (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) F : ℂ) := by
  have hE : xiHedenmalmDeBrangesE w ≠ 0 :=
    xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh hRH hw
  set k : Lp ℂ 2 (volume : Measure ℝ) := (memLp_suzukiModelKernel hRH hw).toLp
    (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) with hk
  have hbasis := (hasSum_smul_suzukiFGammaFamily hRH hF).map (innerSL ℂ k)
    (innerSL ℂ k).continuous
  have hbasis' : HasSum (fun ρ : XiDivisorSupport =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
        * suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w)
      (inner ℂ k F : ℂ) := by
    refine hbasis.congr_fun ?_
    intro ρ
    show _ = (innerSL ℂ k) ((inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) • suzukiFGammaFamily hRH ρ)
    rw [map_smul, smul_eq_mul]
    congr 1
    exact (inner_suzukiModelKernel_suzukiFGammaFamily hRH hw ρ).symm
  have hmul := hbasis'.mul_left (xiHedenmalmDeBrangesE w)
  have hcong : HasSum (fun ρ : XiDivisorSupport =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
        * suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w)
      (xiHedenmalmDeBrangesE w * (inner ℂ k F : ℂ)) := by
    refine hmul.congr_fun ?_
    intro ρ
    rw [suzukiDeBrangesVector_eq (XiC_xiRealSpectralPointSupport hRH ρ) hE]
    ring
  exact (hasSum_suzukiDeBrangesLift hRH hF w).unique hcong

/-- **(dB1) above the axis.**  Point evaluation of the lift is a bounded linear functional. -/
theorem norm_suzukiDeBrangesLift_le (hRH : RiemannHypothesis) {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    ‖suzukiDeBrangesLift hRH F w‖
      ≤ ‖xiHedenmalmDeBrangesE w‖
          * ‖(memLp_suzukiModelKernel hRH hw).toLp
              (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ))‖ * ‖F‖ := by
  rw [suzukiDeBrangesLift_apply hRH hw hF, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) _ _) (norm_nonneg _)

/-! ## Linearity -/

theorem suzukiDeBrangesLift_add (hRH : RiemannHypothesis)
    {F G : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace)
    (hG : G ∈ suzukiModelSpace) (z : ℂ) :
    suzukiDeBrangesLift hRH (F + G) z
      = suzukiDeBrangesLift hRH F z + suzukiDeBrangesLift hRH G z := by
  refine ((hasSum_suzukiDeBrangesLift hRH (Submodule.add_mem _ hF hG) z).unique ?_)
  refine ((hasSum_suzukiDeBrangesLift hRH hF z).add
    (hasSum_suzukiDeBrangesLift hRH hG z)).congr_fun ?_
  intro ρ
  rw [inner_add_right]
  ring

theorem suzukiDeBrangesLift_smul (hRH : RiemannHypothesis) (c : ℂ)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) (z : ℂ) :
    suzukiDeBrangesLift hRH (c • F) z = c * suzukiDeBrangesLift hRH F z := by
  refine ((hasSum_suzukiDeBrangesLift hRH (Submodule.smul_mem _ c hF) z).unique ?_)
  refine ((hasSum_suzukiDeBrangesLift hRH hF z).mul_left c).congr_fun ?_
  intro ρ
  rw [inner_smul_right]
  ring

/-! ## (dB2): the sharp involution -/

/-- The conjugate-linear involution `κ F = Θ conj F` is anti-unitary. -/
theorem inner_thetaMul_star (F G : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (thetaMul (star F)) (thetaMul (star G)) : ℂ) = (inner ℂ G F : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [thetaMul_coeFn (star F), thetaMul_coeFn (star G),
    MeasureTheory.Lp.coeFn_star F, MeasureTheory.Lp.coeFn_star G] with x h1 h2 h3 h4
  rw [RCLike.inner_apply, RCLike.inner_apply, h1, h2, h3, h4, Pi.star_apply, Pi.star_apply,
    map_mul]
  have hu := suzukiThetaSymbol_unimodular x
  simp only [starRingEnd_apply, star_star] at hu ⊢
  linear_combination ((F : ℝ → ℂ) x * star ((G : ℝ → ℂ) x)) * hu

theorem norm_thetaMul_star (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖thetaMul (star F)‖ = ‖F‖ := by
  have h := inner_thetaMul_star F F
  have h2 : ‖thetaMul (star F)‖ ^ 2 = ‖F‖ ^ 2 := by
    have hl := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (thetaMul (star F))
    have hr := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F
    rw [hl, hr] at h
    exact_mod_cast h
  nlinarith [norm_nonneg (thetaMul (star F)), norm_nonneg F, h2]

theorem thetaMul_star_mem_suzukiModelSpace {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hF : F ∈ suzukiModelSpace) : thetaMul (star F) ∈ suzukiModelSpace := by
  rw [mem_suzukiModelSpace_iff_conj] at hF ⊢
  refine ⟨hF.2, ?_⟩
  rw [thetaMul_star_thetaMul_star]
  exact hF.1

theorem inner_suzukiFGammaFamily_thetaMul_star (hRH : RiemannHypothesis)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (ρ : XiDivisorSupport) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) (thetaMul (star F)) : ℂ)
      = -(starRingEnd ℂ) (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) := by
  have hinv := thetaMul_star_thetaMul_star (suzukiFGammaFamily hRH ρ)
  calc (inner ℂ (suzukiFGammaFamily hRH ρ) (thetaMul (star F)) : ℂ)
      = (inner ℂ (thetaMul (star (thetaMul (star (suzukiFGammaFamily hRH ρ)))))
          (thetaMul (star F)) : ℂ) := by rw [hinv]
    _ = (inner ℂ F (thetaMul (star (suzukiFGammaFamily hRH ρ))) : ℂ) :=
          inner_thetaMul_star _ _
    _ = (inner ℂ F (-(suzukiFGammaFamily hRH ρ)) : ℂ) := by
          rw [suzukiFGammaFamily, thetaMul_star_suzukiFGammaLp]
    _ = -(inner ℂ F (suzukiFGammaFamily hRH ρ) : ℂ) := by rw [inner_neg_right]
    _ = -(starRingEnd ℂ) (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ) := by
          rw [← inner_conj_symm]

/-- The de Branges vectors are anti-invariant under the sharp involution. -/
theorem conj_suzukiDeBrangesVector_conj (γ : ℝ) (m : ℕ) (z : ℂ) :
    (starRingEnd ℂ) (suzukiDeBrangesVector γ m ((starRingEnd ℂ) z))
      = -suzukiDeBrangesVector γ m z := by
  have hγc : (starRingEnd ℂ) ((γ : ℝ) : ℂ) = ((γ : ℝ) : ℂ) := Complex.conj_ofReal γ
  have hd : (starRingEnd ℂ) (dslope XiC ((γ : ℝ) : ℂ) ((starRingEnd ℂ) z))
      = dslope XiC ((γ : ℝ) : ℂ) z := by
    by_cases hz : z = ((γ : ℝ) : ℂ)
    · subst hz
      rw [hγc, dslope_same, ← deriv_XiC_conj, hγc]
    · have hzc : (starRingEnd ℂ) z ≠ ((γ : ℝ) : ℂ) := by
        intro h
        exact hz (by rw [← Complex.conj_conj z, h, hγc])
      rw [dslope_of_ne _ hzc, dslope_of_ne _ hz, slope_def_field, slope_def_field,
        map_div₀, map_sub, map_sub, Complex.conj_conj, hγc, XiC_conj, Complex.conj_conj]
      congr 2
      rw [← XiC_conj, hγc]
  rw [suzukiDeBrangesVector, suzukiDeBrangesVector, map_mul, map_mul, Complex.conj_I,
    Complex.conj_ofReal, hd]
  ring

/-- **(dB2).**  The lift of the involution `κ F = Θ conj F` is the sharp reflection of the lift. -/
theorem suzukiDeBrangesLift_thetaMul_star (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) (z : ℂ) :
    suzukiDeBrangesLift hRH (thetaMul (star F)) z
      = (starRingEnd ℂ) (suzukiDeBrangesLift hRH F ((starRingEnd ℂ) z)) := by
  have hbase := hasSum_suzukiDeBrangesLift hRH hF ((starRingEnd ℂ) z)
  have hmap := hbase.map (starRingEnd ℂ) Complex.continuous_conj
  refine (hasSum_suzukiDeBrangesLift hRH (thetaMul_star_mem_suzukiModelSpace hF) z).unique ?_
  refine hmap.congr_fun ?_
  intro ρ
  simp only [Function.comp_apply, map_mul]
  rw [conj_suzukiDeBrangesVector_conj, inner_suzukiFGammaFamily_thetaMul_star hRH F ρ]
  ring


end RHTower
