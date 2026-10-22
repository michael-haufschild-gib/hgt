import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninCutoffTraceFormula
import GaloisForLFunctions.RHTower.SoninL2ShellNull
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The generic part of a cutoff pair is a traceless strict contraction

For the physical and Fourier cutoffs `P = P_Λ`, `P̂ = P̂_Λ` on `L²(ℝ)^ev`, Sonin projection `S` and
generic part `G = 1 - P - P̂ - S`:

* `G² + (P - P̂)² = 1 - S`, `G (P - P̂) = -(P - P̂) G`, `G S = S G = 0`;
* `G` has no eigenvalue `±1`: an eigenvector would satisfy `P v = P̂ v`, hence lie in `S` (value
  `1`) or in `ran P ∩ ran P̂ = 0` (value `-1`); being compact and self-adjoint, `‖G‖ < 1`;
* `Tr G = Tr G^{2k+1}` for every `k`, because `P - P̂` anticommutes with odd powers of `G`; letting
  `k → ∞` gives **`Tr G = 0`**.
-/

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable (Λ : ℝ)

local notation "Pc" => evenIndicatorCutoff Λ
local notation "Fc" => evenFourierCutoff Λ
local notation "Sc" => evenCentralSoninProjection Λ
local notation "Gc" => ccmSoninGenericPartAt Λ

theorem evenIndicatorCutoff_mul_self : Pc * Pc = Pc :=
  (evenIndicatorCutoff_idempotent Λ).eq

theorem evenFourierCutoff_mul_self : Fc * Fc = Fc := by
  rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  calc evenFourierTransform * Pc * evenFourierTransform *
        (evenFourierTransform * Pc * evenFourierTransform)
      = evenFourierTransform * Pc * (evenFourierTransform * evenFourierTransform) * Pc *
          evenFourierTransform := by noncomm_ring
    _ = evenFourierTransform * Pc * evenFourierTransform := by
      rw [evenFourierTransform_mul_self, mul_one, mul_assoc evenFourierTransform Pc Pc,
        evenIndicatorCutoff_mul_self]

theorem evenCentralSoninProjection_mul_self : Sc * Sc = Sc := by
  rw [evenCentralSoninProjection_eq_starProjection]
  exact (evenCentralSoninCarrier Λ).isIdempotentElem_starProjection.eq

theorem adjoint_ccmSoninGenericPartAt : ContinuousLinearMap.adjoint Gc = Gc := by
  have hP : IsSelfAdjoint Pc :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenIndicatorCutoff Λ)
  have hR : IsSelfAdjoint Fc :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenFourierCutoff Λ)
  have hS : IsSelfAdjoint Sc :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenCentralSoninProjection Λ)
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mp ((((IsSelfAdjoint.one _).sub hP).sub hR).sub hS)

theorem ccmSoninGenericPartAt_mul_soninProjection : Gc * Sc = 0 := by
  simp only [ccmSoninGenericPartAt, sub_mul, one_mul,
    evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection, evenCentralSoninProjection_mul_self]
  abel

/-- `G² + (P - P̂)² = 1 - S`. -/
theorem ccmSoninGenericPartAt_sq_add_sq :
    Gc * Gc + (Pc - Fc) * (Pc - Fc) = 1 - Sc := by
  simp only [ccmSoninGenericPartAt, sub_mul, mul_sub, one_mul, mul_one,
    evenIndicatorCutoff_mul_self, evenFourierCutoff_mul_self,
    evenCentralSoninProjection_mul_self, evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff]
  abel

/-- `G (P - P̂) + (P - P̂) G = 0`. -/
theorem ccmSoninGenericPartAt_anticommute :
    Gc * (Pc - Fc) + (Pc - Fc) * Gc = 0 := by
  simp only [ccmSoninGenericPartAt, sub_mul, mul_sub, one_mul, mul_one,
    evenIndicatorCutoff_mul_self, evenFourierCutoff_mul_self,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff,
    evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection]
  abel

/-- If `g` anticommutes with `x`, so does every odd power of `g`. -/
theorem odd_pow_anticommute_of_anticommute {R : Type*} [Ring R] {g x : R}
    (h : g * x + x * g = 0) (k : ℕ) : g ^ (2 * k + 1) * x + x * g ^ (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hid : ∀ p : R, g * (g * p) * x + x * (g * (g * p)) =
        g * g * (p * x + x * p) + ((x * g + g * x) * g - g * (g * x + x * g)) * p := by
      intro p; noncomm_ring
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ', pow_succ', hid, ih,
      add_comm (x * g), h]
    simp

/-! ## No eigenvalue `±1` and strict contraction -/

/-- Eigenvectors of `G` with eigenvalue `±1` vanish. -/
theorem ccmSoninGenericPartAt_eq_zero_of_eigen {v : evenSubspace} {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hv : Gc v = ε • v) : v = 0 := by
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hGG : Gc (Gc v) = v := by rw [hv, map_smul, hv, smul_smul, hεsq, one_smul]
  -- `S v = 0`, since `S G = 0` and `v = ε⁻¹ • G v`
  have hSG : Sc * Gc = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint (ccmSoninGenericPartAt_mul_soninProjection Λ)
    rw [ContinuousLinearMap.adjoint.map_zero] at h
    change ContinuousLinearMap.adjoint (Gc ∘L Sc) = 0 at h
    rw [ContinuousLinearMap.adjoint_comp, adjoint_ccmSoninGenericPartAt,
      adjoint_evenCentralSoninProjection] at h
    exact h
  have hSv : Sc v = 0 := by
    have h := congrArg (fun T => T (Gc v)) hSG
    change Sc (Gc (Gc v)) = 0 at h
    rwa [hGG] at h
  -- `(P - P̂)² v = 0`, hence `P v = P̂ v`
  have hX2 : (Pc - Fc) ((Pc - Fc) v) = 0 := by
    have h := congrArg (fun T => T v) (ccmSoninGenericPartAt_sq_add_sq Λ)
    change Gc (Gc v) + (Pc - Fc) ((Pc - Fc) v) = v - Sc v at h
    rw [hGG, hSv, sub_zero] at h
    simpa using congrArg (fun w => w - v) h
  have hXadj : ContinuousLinearMap.adjoint (Pc - Fc) = Pc - Fc := by
    rw [ContinuousLinearMap.adjoint.map_sub, adjoint_evenIndicatorCutoff,
      adjoint_evenFourierCutoff]
  have hX : (Pc - Fc) v = 0 := by
    have h : inner ℂ ((Pc - Fc) v) ((Pc - Fc) v) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hXadj, hX2, inner_zero_right]
    exact inner_self_eq_zero.mp h
  have hPF : Pc v = Fc v := sub_eq_zero.mp (by simpa using hX)
  have hG : Gc v = v - Pc v - Fc v - Sc v := rfl
  rcases hε with rfl | rfl
  · -- eigenvalue `1`: `P v = P̂ v = 0`, so `v` lies in the Sonin carrier and `S v = v = 0`
    have h2 : (2 : ℂ) • Pc v = 0 := by
      have := hv
      rw [hG, hSv, sub_zero, one_smul, ← hPF] at this
      rw [two_smul]
      have h' : -(Pc v + Pc v) = 0 := by
        calc -(Pc v + Pc v) = v - Pc v - Pc v - v := by abel
          _ = 0 := sub_eq_zero.mpr this
      exact neg_eq_zero.mp h'
    have hP0 : Pc v = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
    have hF0 : Fc v = 0 := hPF ▸ hP0
    have hmem : (v : SoninL2) ∈ centralSoninCarrier Λ := by
      refine ⟨?_, ?_⟩
      · have h := congrArg Subtype.val hP0
        change indicatorCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) v = 0 at h
        rwa [indicatorCutoff_eq_physicalForbidden_starProjection,
          Submodule.starProjection_apply_eq_zero_iff] at h
      · have h := congrArg Subtype.val hF0
        change fourierCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) v = 0 at h
        rwa [fourierCutoff_eq_fourierForbidden_starProjection,
          Submodule.starProjection_apply_eq_zero_iff] at h
    have hSself : Sc v = v := by
      apply Subtype.ext
      change centralSoninProjection Λ v = v
      exact (centralSoninCarrier Λ).starProjection_eq_self_iff.mpr hmem
    rw [← hSself, hSv]
  · -- eigenvalue `-1`: `P v = P̂ v = v`, so `v ∈ ran P ∩ ran P̂ = 0`
    have hPv : Pc v = v := by
      have := hv
      rw [hG, hSv, sub_zero, ← hPF] at this
      have h' : (2 : ℂ) • (v - Pc v) = 0 := by
        rw [smul_sub, two_smul, two_smul]
        calc v + v - (Pc v + Pc v) = v - Pc v - Pc v - (-1 : ℂ) • v := by
              rw [neg_one_smul]; abel
          _ = 0 := sub_eq_zero.mpr this
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_left two_ne_zero)).symm
    have hFv : Fc v = v := hPF ▸ hPv
    have hinf : (v : SoninL2) ∈ centralPhysicalForbidden Λ ⊓ centralFourierForbidden Λ := by
      refine ⟨?_, ?_⟩
      · have h := congrArg Subtype.val hPv
        change indicatorCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) v = v at h
        rw [indicatorCutoff_eq_physicalForbidden_starProjection] at h
        exact (Submodule.starProjection_eq_self_iff).mp h
      · have h := congrArg Subtype.val hFv
        change fourierCutoff (centralInterval Λ) (measurableSet_centralInterval Λ) v = v at h
        rw [fourierCutoff_eq_fourierForbidden_starProjection] at h
        exact (Submodule.starProjection_eq_self_iff).mp h
    have h0 : (v : SoninL2) = 0 := by
      have := physicalForbidden_inf_fourierForbidden_eq_bot Λ
      change centralPhysicalForbidden Λ ⊓ centralFourierForbidden Λ = ⊥ at this
      rw [this] at hinf
      exact (Submodule.mem_bot ℂ).mp hinf
    exact Subtype.ext h0

/-- `‖G‖ ≤ 1`, from `G² ≤ 1 - S`. -/
theorem norm_ccmSoninGenericPartAt_le_one : ‖Gc‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have hXadj : ContinuousLinearMap.adjoint (Pc - Fc) = Pc - Fc := by
    rw [ContinuousLinearMap.adjoint.map_sub, adjoint_evenIndicatorCutoff,
      adjoint_evenFourierCutoff]
  have key : Gc (Gc v) = v - Sc v - (Pc - Fc) ((Pc - Fc) v) := by
    have h := congrArg (fun T => T v) (ccmSoninGenericPartAt_sq_add_sq Λ)
    change Gc (Gc v) + (Pc - Fc) ((Pc - Fc) v) = v - Sc v at h
    rw [← h]
    abel
  have hG := ContinuousLinearMap.adjoint_inner_left Gc (Gc v) v
  rw [adjoint_ccmSoninGenericPartAt] at hG
  have hX := ContinuousLinearMap.adjoint_inner_left (Pc - Fc) ((Pc - Fc) v) v
  rw [hXadj] at hX
  have hS : 0 ≤ RCLike.re (inner ℂ v (Sc v)) := by
    have h := (evenCentralSoninCarrier Λ).re_inner_starProjection_nonneg v
    rw [inner_re_symm] at h
    rwa [evenCentralSoninProjection_eq_starProjection]
  have hre : ‖Gc v‖ ^ 2 = ‖v‖ ^ 2 - RCLike.re (inner ℂ v (Sc v)) - ‖(Pc - Fc) v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (Gc v), hG, key, inner_sub_right, inner_sub_right, ← hX,
      map_sub, map_sub, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  have hsq : ‖Gc v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hre]
    nlinarith [sq_nonneg ‖(Pc - Fc) v‖]
  have h1v : ‖Gc v‖ ≤ ‖v‖ := by
    nlinarith [norm_nonneg (Gc v), norm_nonneg v]
  simpa using h1v

/-- **`‖G‖ < 1`.** -/
theorem norm_ccmSoninGenericPartAt_lt_one (hΛ : 0 < Λ) : ‖Gc‖ < 1 := by
  by_contra hnot
  have hnorm : ‖Gc‖ = 1 := le_antisymm (norm_ccmSoninGenericPartAt_le_one Λ) (le_of_not_gt hnot)
  have hsymm : (Gc : evenSubspace →ₗ[ℂ] evenSubspace).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_ccmSoninGenericPartAt Λ))
  have hcpt : IsCompactOperator Gc :=
    (memSchattenClass_one_ccmSoninGenericPartAt hΛ).isCompactOperator zero_lt_one
  haveI : Nontrivial evenSubspace := evenSubspace_nontrivial
  obtain ⟨μ, hμspec, hμrad⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty Gc)
  have hμnorm : ‖μ‖ = 1 := by
    have hsrad := (ccmSoninGenericPartAt Λ).spectralRadius_eq_nnnorm hsymm.isSelfAdjoint
    rw [hsrad] at hμrad
    have h : ‖μ‖₊ = ‖Gc‖₊ := ENNReal.coe_injective hμrad
    calc ‖μ‖ = (‖μ‖₊ : ℝ) := rfl
      _ = (‖Gc‖₊ : ℝ) := congrArg (fun r : NNReal => (r : ℝ)) h
      _ = 1 := hnorm
  have hμne : μ ≠ 0 := fun h => by rw [h, norm_zero] at hμnorm; norm_num at hμnorm
  have hμeig : Module.End.HasEigenvalue (Gc : evenSubspace →ₗ[ℂ] evenSubspace) μ :=
    (hcpt.hasEigenvalue_iff_mem_spectrum hμne).mpr hμspec
  have hμreal : ((μ.re : ℝ) : ℂ) = μ := Complex.conj_eq_iff_re.mp (hsymm.conj_eigenvalue_eq_self hμeig)
  have hpm : μ = 1 ∨ μ = -1 := by
    have habs : |μ.re| = 1 := by
      rw [← hμreal, Complex.norm_real, Real.norm_eq_abs] at hμnorm
      exact hμnorm
    rcases abs_eq (zero_le_one) |>.mp habs with h | h
    · left; rw [← hμreal, h]; simp
    · right; rw [← hμreal, h]; simp
  obtain ⟨v, hv, hvne⟩ := hμeig.exists_hasEigenvector
  have hv' : Gc v = μ • v := by
    simpa [Module.End.mem_genEigenspace_one] using hv
  exact hvne (ccmSoninGenericPartAt_eq_zero_of_eigen Λ hpm hv')

/-! ## Tracelessness -/

theorem memSchattenClass_one_ccmSoninGenericPartAt_pow (hΛ : 0 < Λ) (n : ℕ) :
    MemSchattenClass 1 (Gc ^ (n + 1)) := by
  induction n with
  | zero => simpa using memSchattenClass_one_ccmSoninGenericPartAt hΛ
  | succ n ih =>
    rw [pow_succ']
    exact memSchattenClass_one_comp_left ih Gc

/-- `Tr G^{2k+1} = Tr G^{2k+3}`: the defect `G^{2k+1}(P - P̂)²` is traceless by anticommutation. -/
theorem opTrace_ccmSoninGenericPartAt_odd_pow_succ (hΛ : 0 < Λ) (k : ℕ) :
    opTrace (Gc ^ (2 * k + 1)) = opTrace (Gc ^ (2 * k + 3)) := by
  set X := Pc - Fc
  have hG : MemSchattenClass 1 (Gc ^ (2 * k + 1)) :=
    memSchattenClass_one_ccmSoninGenericPartAt_pow Λ hΛ (2 * k)
  have hanti : Gc ^ (2 * k + 1) * X + X * Gc ^ (2 * k + 1) = 0 :=
    odd_pow_anticommute_of_anticommute (ccmSoninGenericPartAt_anticommute Λ) k
  have hS : Gc ^ (2 * k + 1) * Sc = 0 := by
    rw [pow_succ, mul_assoc, ccmSoninGenericPartAt_mul_soninProjection, mul_zero]
  -- `G^{2k+1} = G^{2k+1}(1 - S) = G^{2k+3} + G^{2k+1} X²`
  have hp : Gc ^ (2 * k + 3) = Gc ^ (2 * k + 1) * (Gc * Gc) := by
    rw [show 2 * k + 3 = 2 * k + 1 + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc]
  have hsplit : Gc ^ (2 * k + 1) = Gc ^ (2 * k + 3) + Gc ^ (2 * k + 1) * X * X := by
    calc Gc ^ (2 * k + 1) = Gc ^ (2 * k + 1) * (1 - Sc) := by rw [mul_sub, mul_one, hS, sub_zero]
      _ = Gc ^ (2 * k + 1) * (Gc * Gc + X * X) := by rw [← ccmSoninGenericPartAt_sq_add_sq]
      _ = Gc ^ (2 * k + 3) + Gc ^ (2 * k + 1) * X * X := by rw [mul_add, hp, mul_assoc]
  have hGX : MemSchattenClass 1 (Gc ^ (2 * k + 1) * X) := memSchattenClass_one_comp_right hG X
  have hGXX : MemSchattenClass 1 (Gc ^ (2 * k + 1) * X * X) := memSchattenClass_one_comp_right hGX X
  have hXGX : MemSchattenClass 1 (X * (Gc ^ (2 * k + 1) * X)) := memSchattenClass_one_comp_left hGX X
  -- `G^{2k+1}X² + X G^{2k+1} X = 0`, and the two terms have equal traces by cyclicity
  have hzero : opTrace (Gc ^ (2 * k + 1) * X * X) = 0 := by
    have hcyc : opTrace (X * (Gc ^ (2 * k + 1) * X)) = opTrace (Gc ^ (2 * k + 1) * X * X) :=
      hGX.one_opTrace_comp_comm X
    have hsum : Gc ^ (2 * k + 1) * X * X + X * (Gc ^ (2 * k + 1) * X) = 0 := by
      rw [← mul_assoc X, ← add_mul, hanti, zero_mul]
    have h2 := congrArg opTrace hsum
    rw [opTrace_add_of_memSchattenClass_one hGXX hXGX, hcyc, opTrace_zero] at h2
    linear_combination h2 / 2
  have hG3 : MemSchattenClass 1 (Gc ^ (2 * k + 3)) :=
    memSchattenClass_one_ccmSoninGenericPartAt_pow Λ hΛ (2 * k + 2)
  conv_lhs => rw [hsplit]
  rw [opTrace_add_of_memSchattenClass_one hG3 hGXX, hzero, add_zero]

/-- **`Tr G = 0`.** -/
theorem opTrace_ccmSoninGenericPartAt (hΛ : 0 < Λ) : opTrace Gc = 0 := by
  have hG := memSchattenClass_one_ccmSoninGenericPartAt hΛ
  have heq : ∀ k : ℕ, opTrace Gc = opTrace (Gc ^ (2 * k + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, opTrace_ccmSoninGenericPartAt_odd_pow_succ Λ hΛ k,
        show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
  have hbound : ∀ k : ℕ, ‖opTrace Gc‖ ≤ ‖Gc‖ ^ (2 * k) * traceNorm evenSubspace Gc := by
    intro k
    rw [heq k]
    refine (norm_opTrace_le_traceNorm (memSchattenClass_one_ccmSoninGenericPartAt_pow Λ hΛ (2 * k))).trans ?_
    rw [pow_succ]
    refine (traceNorm_comp_left_le hG.one_summable_approxNumber _).trans ?_
    haveI : Nontrivial evenSubspace := evenSubspace_nontrivial
    have hpow : ‖Gc ^ (2 * k)‖ ≤ ‖Gc‖ ^ (2 * k) := by
      exact norm_pow_le (ccmSoninGenericPartAt Λ) (2 * k)
    exact mul_le_mul_of_nonneg_right hpow (traceNorm_nonneg _)
  have hlt := norm_ccmSoninGenericPartAt_lt_one Λ hΛ
  have htend : Filter.Tendsto (fun k : ℕ => ‖Gc‖ ^ (2 * k) * traceNorm evenSubspace Gc)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ‖Gc‖)
      (by nlinarith [norm_nonneg Gc])).mul_const (traceNorm evenSubspace Gc)
    simp only [zero_mul, pow_mul] at h ⊢
    exact h
  have hle : ‖opTrace Gc‖ ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hbound)
  exact norm_le_zero_iff.mp hle

end RHTower
