import GaloisForLFunctions.HTGeometry.QuantumChannelEnergyAugmentation
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Hausdorff convexity of quantum replica moments

If `C` is a Hilbert--Schmidt constraint channel and `T = C† C`, the normalized values

`Pₖ(C) = Re Tr(T^(k+1)) / Re Tr(T)^(k+1)`

are the replica moments of the density operator obtained by normalizing `T`.  The spectrum of a
density operator is contained in `[0, 1]`, so these values form a Hausdorff moment sequence.  This
file formalizes the complete complementary hierarchy: every finite-difference order is
nonnegative,

`0 ≤ ∑_{j=0}^r (-1)^j choose(r,j) Pₖ₊ⱼ`.

More generally, any effect-radius bound `‖C‖² ≤ R` gives the exact operator value relation

`D_{k,r} = Re Tr(T^(k+1) (R I - T)^r) ≥ 0`.

The proof constructs the positive complement square root `D = (R I - T)^(1/2)` and expresses
each weighted monomial trace as a squared Hilbert--Schmidt norm.  It therefore avoids spectral
decomposition and remains reusable for rectangular constraint channels on arbitrary complex
Hilbert spaces.

Physics provenance: Gagatsos--Karanikas--Kordas--Cerf derive exactly this all-order Hausdorff law
for density-operator replica moments in the quantum-optical replica method (Supplemental
Material, equations (32)--(37)), arXiv:1408.5062.  Higher density-matrix moments are multi-copy
quantum observables and their moment-matrix positivity gives quantum-state and entanglement
constraints; see Yu--Imai--Gühne, arXiv:2103.06897, and Elben et al., arXiv:2203.11374.
-/

open Filter Topology
open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem hsInner_self_eq_ofReal
    {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    {T : K →L[ℂ] L} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    ContinuousLinearMap.hsInner T T =
      (ContinuousLinearMap.hsNormSq T : ℂ) := by
  apply Complex.ext
  · exact ContinuousLinearMap.hsInner_self_re hT
  · rw [Complex.ofReal_im]
    change (∑' i, inner ℂ
      (T (ContinuousLinearMap.hsBasis ℂ K i))
      (T (ContinuousLinearMap.hsBasis ℂ K i))).im = 0
    rw [Complex.im_tsum
      (hT.summable_inner hT (ContinuousLinearMap.hsBasis ℂ K))]
    have hzero : (fun i => (inner ℂ
        (T (ContinuousLinearMap.hsBasis ℂ K i))
        (T (ContinuousLinearMap.hsBasis ℂ K i))).im) = fun _ => 0 := by
      funext i
      simpa using inner_self_im (𝕜 := ℂ)
        (T (ContinuousLinearMap.hsBasis ℂ K i))
    rw [hzero, tsum_zero]

@[simp] private theorem opTrace_zero
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    ContinuousLinearMap.opTrace (0 : K →L[ℂ] K) = 0 := by
  simp [ContinuousLinearMap.opTrace]

@[simp] private theorem hsNormSq_zero
    {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L] :
    ContinuousLinearMap.hsNormSq (0 : K →L[ℂ] L) = 0 := by
  simp [ContinuousLinearMap.hsNormSq]

/-- Left composition multiplies Hilbert--Schmidt energy by at most the squared operator norm.
This general ideal estimate was previously available only inside a Sonin implementation module. -/
theorem hsNormSq_comp_left_le_opNorm
    {K L M : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    {T : K →L[ℂ] L} (hT : ContinuousLinearMap.IsHilbertSchmidt T)
    (A : L →L[ℂ] M) :
    ContinuousLinearMap.hsNormSq (A ∘L T) ≤
      ‖A‖ ^ 2 * ContinuousLinearMap.hsNormSq T := by
  let b := ContinuousLinearMap.hsBasis ℂ K
  have hAT := hT.comp_left A
  rw [ContinuousLinearMap.hsNormSq_eq hAT b,
    ContinuousLinearMap.hsNormSq_eq hT b, ← tsum_mul_left]
  exact (hAT.summable b).tsum_le_tsum (fun i => by
    calc
      ‖(A ∘L T) (b i)‖ ^ 2 = ‖A (T (b i))‖ ^ 2 := by
        rw [ContinuousLinearMap.comp_apply]
      _ ≤ (‖A‖ * ‖T (b i)‖) ^ 2 := by
        gcongr
        exact A.le_opNorm _
      _ = ‖A‖ ^ 2 * ‖T (b i)‖ ^ 2 := by ring)
    ((hT.summable b).mul_left (‖A‖ ^ 2))

/-- Exact Hilbert--Schmidt quadratic expansion along a real scalar.  This is the operator-space
identity `||rS-T||² = r²||S||² - 2r Re⟨S,T⟩ + ||T||²`. -/
theorem hsNormSq_real_smul_sub_eq
    {S T : E →L[ℂ] F}
    (hS : ContinuousLinearMap.IsHilbertSchmidt S)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (r : ℝ) :
    ContinuousLinearMap.hsNormSq (((r : ℂ) • S) - T) =
      r ^ 2 * ContinuousLinearMap.hsNormSq S -
        2 * r * (ContinuousLinearMap.hsInner S T).re +
          ContinuousLinearMap.hsNormSq T := by
  let U : E →L[ℂ] F := (r : ℂ) • S
  let V : E →L[ℂ] F := -T
  have hU : ContinuousLinearMap.IsHilbertSchmidt U := hS.smul (r : ℂ)
  have hV : ContinuousLinearMap.IsHilbertSchmidt V := hT.neg
  have hD : ContinuousLinearMap.IsHilbertSchmidt (U + V) := hU.add hV
  have hUU : ContinuousLinearMap.hsInner U U =
      ((r ^ 2 : ℝ) : ℂ) * ContinuousLinearMap.hsInner S S := by
    dsimp only [U]
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
    ring
  have hUV : ContinuousLinearMap.hsInner U V =
      -(r : ℂ) * ContinuousLinearMap.hsInner S T := by
    dsimp only [U, V]
    rw [show (-T : E →L[ℂ] F) = (-1 : ℂ) • T by simp]
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
  have hVU : ContinuousLinearMap.hsInner V U =
      -(r : ℂ) * ContinuousLinearMap.hsInner T S := by
    dsimp only [U, V]
    rw [show (-T : E →L[ℂ] F) = (-1 : ℂ) • T by simp]
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
  have hVV : ContinuousLinearMap.hsInner V V =
      ContinuousLinearMap.hsInner T T := by
    dsimp only [V]
    rw [show (-T : E →L[ℂ] F) = (-1 : ℂ) • T by simp]
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
  have hpair : ContinuousLinearMap.hsInner (U + V) (U + V) =
      (ContinuousLinearMap.hsInner U U + ContinuousLinearMap.hsInner U V) +
        (ContinuousLinearMap.hsInner V U + ContinuousLinearMap.hsInner V V) := by
    calc
      ContinuousLinearMap.hsInner (U + V) (U + V) =
          ContinuousLinearMap.hsInner U (U + V) +
            ContinuousLinearMap.hsInner V (U + V) :=
        ContinuousLinearMap.hsInner_add_left hU hV hD
      _ = _ := by
        rw [ContinuousLinearMap.hsInner_add_right hU hU hV,
          ContinuousLinearMap.hsInner_add_right hV hU hV]
  have hcrossRe : (ContinuousLinearMap.hsInner T S).re =
      (ContinuousLinearMap.hsInner S T).re := by
    rw [ContinuousLinearMap.hsInner_conj_symm T S]
    simp
  have hSself : (ContinuousLinearMap.hsInner S S).re =
      ContinuousLinearMap.hsNormSq S :=
    ContinuousLinearMap.hsInner_self_re hS
  have hTself : (ContinuousLinearMap.hsInner T T).re =
      ContinuousLinearMap.hsNormSq T :=
    ContinuousLinearMap.hsInner_self_re hT
  rw [show (((r : ℂ) • S) - T) = U + V by
    simp only [U, V, sub_eq_add_neg]]
  calc
    ContinuousLinearMap.hsNormSq (U + V) =
        (ContinuousLinearMap.hsInner (U + V) (U + V)).re :=
      (ContinuousLinearMap.hsInner_self_re hD).symm
    _ = r ^ 2 * ContinuousLinearMap.hsNormSq S -
          2 * r * (ContinuousLinearMap.hsInner S T).re +
            ContinuousLinearMap.hsNormSq T := by
      rw [hpair, hUU, hUV, hVU, hVV]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, neg_zero, zero_mul, sub_zero, hcrossRe]
      rw [hSself, hTself]
      ring

/-- The `n`-th power column of the positive master effect `C† C`. -/
def quantumMasterEffectPowerColumn (C : E →L[ℂ] F) (n : ℕ) : E →L[ℂ] F :=
  C ∘L quantumChannelEffect C ^ n

theorem quantumMasterEffectPowerColumn_isHilbertSchmidt
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (n : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (quantumMasterEffectPowerColumn C n) :=
  hC.comp_right (quantumChannelEffect C ^ n)

/-- Pairings of master-effect power columns are Hankel trace moments. -/
theorem hsInner_quantumMasterEffectPowerColumn_eq_tracePower
    (C : E →L[ℂ] F) (m n : ℕ) :
    ContinuousLinearMap.hsInner
        (quantumMasterEffectPowerColumn C m)
        (quantumMasterEffectPowerColumn C n) =
      ContinuousLinearMap.opTrace (quantumChannelEffect C ^ (m + n + 1)) := by
  let T := quantumChannelEffect C
  let Vm := quantumMasterEffectPowerColumn C m
  let Vn := quantumMasterEffectPowerColumn C n
  have hT : ContinuousLinearMap.adjoint T = T :=
    adjoint_quantumChannelEffect C
  have hpow : ContinuousLinearMap.adjoint (T ^ m) = T ^ m := by
    change star (T ^ m) = T ^ m
    rw [star_pow]
    change ContinuousLinearMap.adjoint T ^ m = T ^ m
    rw [hT]
  calc
    ContinuousLinearMap.hsInner Vm Vn =
        ContinuousLinearMap.opTrace
          (ContinuousLinearMap.adjoint Vm ∘L Vn) := by
      rw [ContinuousLinearMap.opTrace_comp_eq_hsInner
        (ContinuousLinearMap.adjoint Vm) Vn,
        ContinuousLinearMap.adjoint_adjoint]
    _ = ContinuousLinearMap.opTrace (T ^ (m + n + 1)) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [Vm, Vn, quantumMasterEffectPowerColumn,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      rw [hpow]
      change (T ^ m) ((ContinuousLinearMap.adjoint C)
        (C ((T ^ n) x))) = (T ^ (m + n + 1)) x
      have henergy (y) : (ContinuousLinearMap.adjoint C) (C y) = T y := by
        rfl
      rw [henergy]
      change (T ^ m) (T ((T ^ n) x)) = (T ^ (m + n + 1)) x
      rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply]
      congr 1
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

/-- Real trace moment of the positive master effect, indexed so that degree zero is `Tr(C†C)`. -/
def quantumMasterEffectMoment (C : E →L[ℂ] F) (k : ℕ) : ℝ :=
  (ContinuousLinearMap.opTrace (quantumChannelEffect C ^ (k + 1))).re

/-- The total mass used to normalize the master effect. -/
def quantumMasterEffectMass (C : E →L[ℂ] F) : ℝ :=
  ContinuousLinearMap.hsNormSq C

/-- The normalized `(k+1)`-replica moment of the density operator associated to `C†C`. -/
def quantumMasterEffectReplicaMoment (C : E →L[ℂ] F) (k : ℕ) : ℝ :=
  quantumMasterEffectMoment C k / quantumMasterEffectMass C ^ (k + 1)

/-- Even master-effect moments are squared norms of rectangular power columns. -/
theorem quantumMasterEffectMoment_even_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (n : ℕ) :
    quantumMasterEffectMoment C (2 * n) =
      ContinuousLinearMap.hsNormSq (quantumMasterEffectPowerColumn C n) := by
  have hV := quantumMasterEffectPowerColumn_isHilbertSchmidt hC n
  rw [quantumMasterEffectMoment]
  calc
    (ContinuousLinearMap.opTrace
        (quantumChannelEffect C ^ (2 * n + 1))).re =
        (ContinuousLinearMap.hsInner
          (quantumMasterEffectPowerColumn C n)
          (quantumMasterEffectPowerColumn C n)).re := by
      rw [hsInner_quantumMasterEffectPowerColumn_eq_tracePower]
      congr 3
      omega
    _ = ContinuousLinearMap.hsNormSq
        (quantumMasterEffectPowerColumn C n) :=
      ContinuousLinearMap.hsInner_self_re hV

theorem quantumChannelEffect_pow_isHilbertSchmidt
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {n : ℕ} (hn : 0 < n) :
    ContinuousLinearMap.IsHilbertSchmidt (quantumChannelEffect C ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, ContinuousLinearMap.mul_def]
  exact (quantumChannelEffect_isHilbertSchmidt hC).comp_left
    (quantumChannelEffect C ^ m)

/-- Odd master-effect moments are squared norms of positive-effect powers. -/
theorem quantumMasterEffectMoment_odd_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (n : ℕ) :
    quantumMasterEffectMoment C (2 * n + 1) =
      ContinuousLinearMap.hsNormSq (quantumChannelEffect C ^ (n + 1)) := by
  let T := quantumChannelEffect C
  let S := T ^ (n + 1)
  have hS : ContinuousLinearMap.IsHilbertSchmidt S :=
    quantumChannelEffect_pow_isHilbertSchmidt hC (by omega)
  have hSad : ContinuousLinearMap.adjoint S = S := by
    change star (T ^ (n + 1)) = T ^ (n + 1)
    rw [star_pow]
    change ContinuousLinearMap.adjoint T ^ (n + 1) = T ^ (n + 1)
    rw [adjoint_quantumChannelEffect]
  rw [quantumMasterEffectMoment]
  calc
    (ContinuousLinearMap.opTrace (T ^ (2 * n + 1 + 1))).re =
        (ContinuousLinearMap.opTrace
          (ContinuousLinearMap.adjoint S ∘L S)).re := by
      rw [hSad]
      congr 2
      dsimp only [S]
      change T ^ (2 * n + 1 + 1) =
        (T ^ (n + 1)) ∘L (T ^ (n + 1))
      rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega,
        pow_add, ContinuousLinearMap.mul_def]
    _ = ContinuousLinearMap.hsNormSq S :=
      ContinuousLinearMap.re_opTrace_adjoint_comp_self hS

theorem quantumMasterEffectMoment_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    0 ≤ quantumMasterEffectMoment C k := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [quantumMasterEffectMoment_even_eq_hsNormSq hC]
    exact ContinuousLinearMap.hsNormSq_nonneg _
  · subst k
    rw [quantumMasterEffectMoment_odd_eq_hsNormSq hC]
    exact ContinuousLinearMap.hsNormSq_nonneg _

/-- **Replica-step effect contraction.**  Successive trace moments of `C†C` are controlled by
the squared operator norm of the channel.  This is the moment form of the Born/Kraus energy
ceiling and is independent of the Hilbert--Schmidt mass used for density normalization. -/
theorem quantumMasterEffectMoment_succ_le_sq_opNorm_mul
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    quantumMasterEffectMoment C (k + 1) ≤
      ‖C‖ ^ 2 * quantumMasterEffectMoment C k := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [quantumMasterEffectMoment_odd_eq_hsNormSq hC,
      quantumMasterEffectMoment_even_eq_hsNormSq hC]
    let V := quantumMasterEffectPowerColumn C n
    have hV : ContinuousLinearMap.IsHilbertSchmidt V :=
      quantumMasterEffectPowerColumn_isHilbertSchmidt hC n
    have hcomp := hsNormSq_comp_left_le_opNorm hV
      (ContinuousLinearMap.adjoint C)
    have hadjointNorm : ‖ContinuousLinearMap.adjoint C‖ = ‖C‖ := by
      exact (ContinuousLinearMap.adjoint :
        (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).norm_map C
    have hfactor : ContinuousLinearMap.adjoint C ∘L V =
        quantumChannelEffect C ^ (n + 1) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [V, quantumMasterEffectPowerColumn, quantumChannelEffect,
        ContinuousLinearMap.comp_apply, pow_succ', ContinuousLinearMap.mul_apply]
    rw [← hfactor]
    simpa only [hadjointNorm] using hcomp
  · subst k
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
      quantumMasterEffectMoment_even_eq_hsNormSq hC,
      quantumMasterEffectMoment_odd_eq_hsNormSq hC]
    let T := quantumChannelEffect C ^ (n + 1)
    have hT : ContinuousLinearMap.IsHilbertSchmidt T :=
      quantumChannelEffect_pow_isHilbertSchmidt hC (by omega)
    have hcomp := hsNormSq_comp_left_le_opNorm hT C
    have hfactor : C ∘L T = quantumMasterEffectPowerColumn C (n + 1) := by
      rfl
    rw [← hfactor]
    exact hcomp

/-- A channel bound `||C||² ≤ R` gives an aperture- or scale-independent replica-step bound
`M_(k+1) ≤ R M_k`. -/
theorem quantumMasterEffectMoment_succ_le_effectRadius_mul
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (k : ℕ) :
    quantumMasterEffectMoment C (k + 1) ≤ R * quantumMasterEffectMoment C k := by
  exact (quantumMasterEffectMoment_succ_le_sq_opNorm_mul hC k).trans
    (mul_le_mul_of_nonneg_right hR (quantumMasterEffectMoment_nonneg hC k))

theorem re_hsInner_quantumMasterEffectPowerColumn_succ
    (C : E →L[ℂ] F) (n : ℕ) :
    (ContinuousLinearMap.hsInner
        (quantumMasterEffectPowerColumn C n)
        (quantumMasterEffectPowerColumn C (n + 1))).re =
      quantumMasterEffectMoment C (2 * n + 1) := by
  rw [hsInner_quantumMasterEffectPowerColumn_eq_tracePower,
    quantumMasterEffectMoment]
  congr 3
  omega

theorem hsInner_quantumChannelEffect_powers_eq_tracePower
    (C : E →L[ℂ] F) (m n : ℕ) :
    ContinuousLinearMap.hsInner
        (quantumChannelEffect C ^ (m + 1))
        (quantumChannelEffect C ^ (n + 1)) =
      ContinuousLinearMap.opTrace
        (quantumChannelEffect C ^ (m + n + 2)) := by
  let T := quantumChannelEffect C
  have hadj : ContinuousLinearMap.adjoint (T ^ (m + 1)) = T ^ (m + 1) := by
    change star (T ^ (m + 1)) = T ^ (m + 1)
    rw [star_pow]
    change ContinuousLinearMap.adjoint T ^ (m + 1) = T ^ (m + 1)
    rw [adjoint_quantumChannelEffect]
  calc
    ContinuousLinearMap.hsInner (T ^ (m + 1)) (T ^ (n + 1)) =
        ContinuousLinearMap.opTrace
          ((T ^ (m + 1)) ∘L (T ^ (n + 1))) := by
      rw [ContinuousLinearMap.opTrace_comp_eq_hsInner, hadj]
    _ = ContinuousLinearMap.opTrace (T ^ (m + n + 2)) := by
      congr 1
      change T ^ (m + 1) * T ^ (n + 1) = T ^ (m + n + 2)
      rw [← pow_add]
      congr 1
      omega

theorem re_hsInner_quantumChannelEffect_powers_succ
    (C : E →L[ℂ] F) (n : ℕ) :
    (ContinuousLinearMap.hsInner
        (quantumChannelEffect C ^ (n + 1))
        (quantumChannelEffect C ^ (n + 2))).re =
      quantumMasterEffectMoment C (2 * n + 2) := by
  rw [hsInner_quantumChannelEffect_powers_eq_tracePower,
    quantumMasterEffectMoment]
  congr 3
  omega

/-- The unnormalized second complementary difference of the master-effect trace moments. -/
def quantumMasterEffectSecondDifference (C : E →L[ℂ] F) (k : ℕ) : ℝ :=
  quantumMasterEffectMass C ^ 2 * quantumMasterEffectMoment C k -
    2 * quantumMasterEffectMass C * quantumMasterEffectMoment C (k + 1) +
      quantumMasterEffectMoment C (k + 2)

/-- At even degree the complementary second difference is one rectangular power-column square. -/
theorem quantumMasterEffectSecondDifference_even_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (n : ℕ) :
    quantumMasterEffectSecondDifference C (2 * n) =
      ContinuousLinearMap.hsNormSq
        (((quantumMasterEffectMass C : ℝ) : ℂ) •
            quantumMasterEffectPowerColumn C n -
          quantumMasterEffectPowerColumn C (n + 1)) := by
  have hA := quantumMasterEffectPowerColumn_isHilbertSchmidt hC n
  have hB := quantumMasterEffectPowerColumn_isHilbertSchmidt hC (n + 1)
  rw [quantumMasterEffectSecondDifference,
    quantumMasterEffectMoment_even_eq_hsNormSq hC,
    quantumMasterEffectMoment_odd_eq_hsNormSq hC,
    show 2 * n + 2 = 2 * (n + 1) by omega,
    quantumMasterEffectMoment_even_eq_hsNormSq hC,
    hsNormSq_real_smul_sub_eq hA hB,
    re_hsInner_quantumMasterEffectPowerColumn_succ]
  rw [quantumMasterEffectMoment_odd_eq_hsNormSq hC n]

/-- At odd degree the complementary second difference is one positive-effect power square. -/
theorem quantumMasterEffectSecondDifference_odd_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (n : ℕ) :
    quantumMasterEffectSecondDifference C (2 * n + 1) =
      ContinuousLinearMap.hsNormSq
        (((quantumMasterEffectMass C : ℝ) : ℂ) •
            quantumChannelEffect C ^ (n + 1) -
          quantumChannelEffect C ^ (n + 2)) := by
  have hA := quantumChannelEffect_pow_isHilbertSchmidt hC (n := n + 1) (by omega)
  have hB := quantumChannelEffect_pow_isHilbertSchmidt hC (n := n + 2) (by omega)
  rw [quantumMasterEffectSecondDifference,
    quantumMasterEffectMoment_odd_eq_hsNormSq hC,
    show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
    quantumMasterEffectMoment_even_eq_hsNormSq hC,
    show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega,
    quantumMasterEffectMoment_odd_eq_hsNormSq hC,
    hsNormSq_real_smul_sub_eq hA hB,
    re_hsInner_quantumChannelEffect_powers_succ]
  rw [show 2 * n + 2 = 2 * (n + 1) by omega,
    quantumMasterEffectMoment_even_eq_hsNormSq hC (n + 1)]

/-- Every unnormalized second complementary difference is nonnegative. -/
theorem quantumMasterEffectSecondDifference_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    0 ≤ quantumMasterEffectSecondDifference C k := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [quantumMasterEffectSecondDifference_even_eq_hsNormSq hC]
    exact ContinuousLinearMap.hsNormSq_nonneg _
  · subst k
    rw [quantumMasterEffectSecondDifference_odd_eq_hsNormSq hC]
    exact ContinuousLinearMap.hsNormSq_nonneg _

/-- **Quantum Hausdorff convexity.**  Normalized density-operator replica moments have
nonnegative second complementary finite differences. -/
theorem quantumMasterEffectReplicaMoment_secondDifference_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    0 ≤ quantumMasterEffectReplicaMoment C k -
      2 * quantumMasterEffectReplicaMoment C (k + 1) +
        quantumMasterEffectReplicaMoment C (k + 2) := by
  by_cases hmass : quantumMasterEffectMass C = 0
  · have hCzero : C = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mp hmass
    subst C
    simp [quantumMasterEffectReplicaMoment, quantumMasterEffectMoment,
      quantumMasterEffectMass, quantumChannelEffect]
  · have hmassPos : 0 < quantumMasterEffectMass C :=
      lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg C) (Ne.symm hmass)
    have hdiff := quantumMasterEffectSecondDifference_nonneg hC k
    have heq :
        quantumMasterEffectReplicaMoment C k -
            2 * quantumMasterEffectReplicaMoment C (k + 1) +
              quantumMasterEffectReplicaMoment C (k + 2) =
          quantumMasterEffectSecondDifference C k /
            quantumMasterEffectMass C ^ (k + 3) := by
      rw [quantumMasterEffectReplicaMoment,
        quantumMasterEffectReplicaMoment,
        quantumMasterEffectReplicaMoment,
        quantumMasterEffectSecondDifference]
      simp only [pow_succ]
      field_simp
    rw [heq]
    exact div_nonneg hdiff (pow_nonneg hmassPos.le _)

def quantumMasterEffectComplement (R : ℝ) (C : E →L[ℂ] F) : E →L[ℂ] E :=
  (R : ℂ) • (1 : E →L[ℂ] E) - quantumChannelEffect C

theorem adjoint_quantumMasterEffectComplement (R : ℝ) (C : E →L[ℂ] F) :
    ContinuousLinearMap.adjoint (quantumMasterEffectComplement R C) =
      quantumMasterEffectComplement R C := by
  let adj : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint
  change adj ((R : ℂ) • (1 : E →L[ℂ] E) - quantumChannelEffect C) = _
  rw [map_sub adj, adj.map_smulₛₗ, ContinuousLinearMap.adjoint_one]
  rw [quantumMasterEffectComplement]
  have hstar : (starRingEnd ℂ) (R : ℂ) = (R : ℂ) := by simp
  rw [hstar]
  change (R : ℂ) • (1 : E →L[ℂ] E) -
      ContinuousLinearMap.adjoint (quantumChannelEffect C) =
    (R : ℂ) • (1 : E →L[ℂ] E) - quantumChannelEffect C
  rw [adjoint_quantumChannelEffect]

theorem quantumMasterEffectComplement_isPositive
    {C : E →L[ℂ] F} {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) :
    (quantumMasterEffectComplement R C).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨adjoint_quantumMasterEffectComplement R C, fun x => ?_⟩
  have hCx : ‖C x‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
    calc
      ‖C x‖ ^ 2 ≤ (‖C‖ * ‖x‖) ^ 2 := by
        gcongr
        exact C.le_opNorm x
      _ = ‖C‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ R * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hR (sq_nonneg ‖x‖)
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [quantumMasterEffectComplement, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, inner_smul_left, map_sub]
  rw [quantumChannelEffect, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  have hreC : RCLike.re ⟪C x, C x⟫_ℂ = ‖C x‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [hreC]
  simpa [pow_two, Complex.mul_re] using (sub_nonneg.mpr hCx)

theorem quantumMasterEffectComplement_nonneg
    {C : E →L[ℂ] F} {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) :
    0 ≤ quantumMasterEffectComplement R C := by
  simpa [ContinuousLinearMap.le_def] using
    quantumMasterEffectComplement_isPositive (C := C) hR

def quantumMasterEffectComplementSqrt (R : ℝ) (C : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (quantumMasterEffectComplement R C)

theorem quantumMasterEffectComplementSqrt_sq
    {C : E →L[ℂ] F} {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) :
    quantumMasterEffectComplementSqrt R C ^ 2 =
      quantumMasterEffectComplement R C := by
  exact CFC.sq_sqrt _ (quantumMasterEffectComplement_nonneg hR)

theorem quantumMasterEffectComplementSqrt_isSelfAdjoint
    (R : ℝ) (C : E →L[ℂ] F) :
    IsSelfAdjoint (quantumMasterEffectComplementSqrt R C) :=
  IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

theorem quantumChannelEffect_commute_complement (R : ℝ) (C : E →L[ℂ] F) :
    Commute (quantumChannelEffect C) (quantumMasterEffectComplement R C) := by
  change quantumChannelEffect C * quantumMasterEffectComplement R C =
    quantumMasterEffectComplement R C * quantumChannelEffect C
  simp [quantumMasterEffectComplement, mul_sub, sub_mul]

theorem quantumChannelEffect_commute_complementSqrt (R : ℝ) (C : E →L[ℂ] F) :
    Commute (quantumChannelEffect C) (quantumMasterEffectComplementSqrt R C) := by
  exact ((quantumChannelEffect_commute_complement R C).symm.cfcₙ_nnreal NNReal.sqrt).symm

private theorem commute_sandwich_pow
    {A : Type*} [Monoid A] {T D : A} (h : Commute T D) (p r : ℕ) :
    D ^ r * T ^ p * T * T ^ p * D ^ r =
      T ^ (2 * p + 1) * (D ^ 2) ^ r := by
  have hTp : T ^ p * T * T ^ p = T ^ (2 * p + 1) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  calc
    D ^ r * T ^ p * T * T ^ p * D ^ r =
        D ^ r * (T ^ p * T * T ^ p) * D ^ r := by
      simp only [mul_assoc]
    _ = D ^ r * T ^ (2 * p + 1) * D ^ r := by rw [hTp]
    _ = T ^ (2 * p + 1) * (D ^ r * D ^ r) := by
      rw [(h.symm.pow_pow r (2 * p + 1)).eq]
      simp only [mul_assoc]
    _ = T ^ (2 * p + 1) * D ^ (2 * r) := by
      rw [← pow_add]
      congr 2
      omega
    _ = T ^ (2 * p + 1) * (D ^ 2) ^ r := by
      rw [pow_mul]

private theorem commute_even_sandwich_pow
    {A : Type*} [Monoid A] {T D : A} (h : Commute T D) (p r : ℕ) :
    D ^ r * T ^ (p + 1) * T ^ (p + 1) * D ^ r =
      T ^ (2 * p + 2) * (D ^ 2) ^ r := by
  have hTp : T ^ (p + 1) * T ^ (p + 1) = T ^ (2 * p + 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    D ^ r * T ^ (p + 1) * T ^ (p + 1) * D ^ r =
        D ^ r * (T ^ (p + 1) * T ^ (p + 1)) * D ^ r := by
      simp only [mul_assoc]
    _ = D ^ r * T ^ (2 * p + 2) * D ^ r := by rw [hTp]
    _ = T ^ (2 * p + 2) * (D ^ r * D ^ r) := by
      rw [(h.symm.pow_pow r (2 * p + 2)).eq]
      simp only [mul_assoc]
    _ = T ^ (2 * p + 2) * D ^ (2 * r) := by
      rw [← pow_add]
      congr 2
      omega
    _ = T ^ (2 * p + 2) * (D ^ 2) ^ r := by
      rw [pow_mul]

/-- Real trace of `T^(k+1) (R I - T)^r`, where `T = C†C`. -/
def quantumMasterEffectWeightedMoment
    (R : ℝ) (C : E →L[ℂ] F) (k r : ℕ) : ℝ :=
  (ContinuousLinearMap.opTrace
    (quantumChannelEffect C ^ (k + 1) *
      quantumMasterEffectComplement R C ^ r)).re

/-- Rectangular square root of the weighted effect monomial at even moment degree. -/
def quantumMasterEffectWeightedPowerColumn
    (R : ℝ) (C : E →L[ℂ] F) (n r : ℕ) : E →L[ℂ] F :=
  C ∘L (quantumChannelEffect C ^ n *
    quantumMasterEffectComplementSqrt R C ^ r)

/-- Endomorphic square root of the weighted effect monomial at odd moment degree. -/
def quantumMasterEffectWeightedEffectPower
    (R : ℝ) (C : E →L[ℂ] F) (n r : ℕ) : E →L[ℂ] E :=
  quantumChannelEffect C ^ (n + 1) *
    quantumMasterEffectComplementSqrt R C ^ r

theorem quantumMasterEffectWeightedPowerColumn_isHilbertSchmidt
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (R : ℝ) (n r : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt
      (quantumMasterEffectWeightedPowerColumn R C n r) :=
  hC.comp_right _

theorem quantumMasterEffectWeightedEffectPower_isHilbertSchmidt
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (R : ℝ) (n r : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt
      (quantumMasterEffectWeightedEffectPower R C n r) :=
  (quantumChannelEffect_pow_isHilbertSchmidt hC (n := n + 1) (by omega)).comp_right _

theorem adjoint_comp_quantumMasterEffectWeightedPowerColumn
    {C : E →L[ℂ] F} {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (n r : ℕ) :
    ContinuousLinearMap.adjoint (quantumMasterEffectWeightedPowerColumn R C n r) ∘L
        quantumMasterEffectWeightedPowerColumn R C n r =
      quantumChannelEffect C ^ (2 * n + 1) *
        quantumMasterEffectComplement R C ^ r := by
  let T := quantumChannelEffect C
  let D := quantumMasterEffectComplementSqrt R C
  let B := quantumMasterEffectComplement R C
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    adjoint_quantumChannelEffect C
  have hDadj : ContinuousLinearMap.adjoint D = D :=
    quantumMasterEffectComplementSqrt_isSelfAdjoint R C
  have hcomm : Commute T D :=
    quantumChannelEffect_commute_complementSqrt R C
  have hsquare : D ^ 2 = B :=
    quantumMasterEffectComplementSqrt_sq hR
  have hAdjPow : ContinuousLinearMap.adjoint (T ^ n * D ^ r) =
      D ^ r * T ^ n := by
    change star (T ^ n * D ^ r) = D ^ r * T ^ n
    rw [star_mul, star_pow, star_pow]
    change ContinuousLinearMap.adjoint D ^ r *
      ContinuousLinearMap.adjoint T ^ n = D ^ r * T ^ n
    rw [hTadj, hDadj]
  change ContinuousLinearMap.adjoint (C ∘L (T ^ n * D ^ r)) ∘L
      (C ∘L (T ^ n * D ^ r)) = T ^ (2 * n + 1) * B ^ r
  rw [ContinuousLinearMap.adjoint_comp]
  rw [hAdjPow]
  change (D ^ r * T ^ n) * (ContinuousLinearMap.adjoint C ∘L C) *
      (T ^ n * D ^ r) = T ^ (2 * n + 1) * B ^ r
  change (D ^ r * T ^ n) * T * (T ^ n * D ^ r) =
      T ^ (2 * n + 1) * B ^ r
  calc
    (D ^ r * T ^ n) * T * (T ^ n * D ^ r) =
        D ^ r * T ^ n * T * T ^ n * D ^ r := by
      simp only [mul_assoc]
    _ = T ^ (2 * n + 1) * (D ^ 2) ^ r :=
      commute_sandwich_pow hcomm n r
    _ = T ^ (2 * n + 1) * B ^ r := by rw [hsquare]

theorem adjoint_comp_quantumMasterEffectWeightedEffectPower
    {C : E →L[ℂ] F} {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (n r : ℕ) :
    ContinuousLinearMap.adjoint (quantumMasterEffectWeightedEffectPower R C n r) ∘L
        quantumMasterEffectWeightedEffectPower R C n r =
      quantumChannelEffect C ^ (2 * n + 2) *
        quantumMasterEffectComplement R C ^ r := by
  let T := quantumChannelEffect C
  let D := quantumMasterEffectComplementSqrt R C
  let B := quantumMasterEffectComplement R C
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    adjoint_quantumChannelEffect C
  have hDadj : ContinuousLinearMap.adjoint D = D :=
    quantumMasterEffectComplementSqrt_isSelfAdjoint R C
  have hcomm : Commute T D :=
    quantumChannelEffect_commute_complementSqrt R C
  have hsquare : D ^ 2 = B :=
    quantumMasterEffectComplementSqrt_sq hR
  have hAdjPow : ContinuousLinearMap.adjoint (T ^ (n + 1) * D ^ r) =
      D ^ r * T ^ (n + 1) := by
    change star (T ^ (n + 1) * D ^ r) = D ^ r * T ^ (n + 1)
    rw [star_mul, star_pow, star_pow]
    change ContinuousLinearMap.adjoint D ^ r *
      ContinuousLinearMap.adjoint T ^ (n + 1) =
        D ^ r * T ^ (n + 1)
    rw [hTadj, hDadj]
  change ContinuousLinearMap.adjoint (T ^ (n + 1) * D ^ r) ∘L
      (T ^ (n + 1) * D ^ r) = T ^ (2 * n + 2) * B ^ r
  rw [hAdjPow]
  calc
    (D ^ r * T ^ (n + 1)) * (T ^ (n + 1) * D ^ r) =
        D ^ r * T ^ (n + 1) * T ^ (n + 1) * D ^ r := by
      simp only [mul_assoc]
    _ = T ^ (2 * n + 2) * (D ^ 2) ^ r :=
      commute_even_sandwich_pow hcomm n r
    _ = T ^ (2 * n + 2) * B ^ r := by rw [hsquare]

/-- Even weighted moments are squared Hilbert--Schmidt norms of rectangular columns. -/
theorem quantumMasterEffectWeightedMoment_even_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (n r : ℕ) :
    quantumMasterEffectWeightedMoment R C (2 * n) r =
      ContinuousLinearMap.hsNormSq
        (quantumMasterEffectWeightedPowerColumn R C n r) := by
  rw [quantumMasterEffectWeightedMoment]
  rw [← adjoint_comp_quantumMasterEffectWeightedPowerColumn hR n r]
  exact ContinuousLinearMap.re_opTrace_adjoint_comp_self
    (quantumMasterEffectWeightedPowerColumn_isHilbertSchmidt hC R n r)

/-- Odd weighted moments are squared Hilbert--Schmidt norms of endomorphic powers. -/
theorem quantumMasterEffectWeightedMoment_odd_eq_hsNormSq
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (n r : ℕ) :
    quantumMasterEffectWeightedMoment R C (2 * n + 1) r =
      ContinuousLinearMap.hsNormSq
        (quantumMasterEffectWeightedEffectPower R C n r) := by
  rw [quantumMasterEffectWeightedMoment]
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega]
  rw [← adjoint_comp_quantumMasterEffectWeightedEffectPower hR n r]
  exact ContinuousLinearMap.re_opTrace_adjoint_comp_self
    (quantumMasterEffectWeightedEffectPower_isHilbertSchmidt hC R n r)

/-- Every operator-weighted Hausdorff monomial has nonnegative trace. -/
theorem quantumMasterEffectWeightedMoment_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (k r : ℕ) :
    0 ≤ quantumMasterEffectWeightedMoment R C k r := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    rw [quantumMasterEffectWeightedMoment_even_eq_hsNormSq hC hR]
    exact ContinuousLinearMap.hsNormSq_nonneg _
  · subst k
    rw [quantumMasterEffectWeightedMoment_odd_eq_hsNormSq hC hR]
    exact ContinuousLinearMap.hsNormSq_nonneg _

private theorem opTrace_sub_eq_sub_of_summable_diag
    (S T : E →L[ℂ] E)
    (hS : Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
      (S (ContinuousLinearMap.hsBasis ℂ E i))))
    (hT : Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
      (T (ContinuousLinearMap.hsBasis ℂ E i)))) :
    ContinuousLinearMap.opTrace (S - T) =
      ContinuousLinearMap.opTrace S - ContinuousLinearMap.opTrace T := by
  unfold ContinuousLinearMap.opTrace
  calc
    ∑' i, inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
        ((S - T) (ContinuousLinearMap.hsBasis ℂ E i)) =
        ∑' i, (inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
          (S (ContinuousLinearMap.hsBasis ℂ E i)) -
          inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
            (T (ContinuousLinearMap.hsBasis ℂ E i))) := by
      exact tsum_congr fun i => by
        rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    _ = _ := hS.tsum_sub hT

private theorem opTrace_smul_eq
    (c : ℂ) (S : E →L[ℂ] E) :
    ContinuousLinearMap.opTrace (c • S) =
      c * ContinuousLinearMap.opTrace S := by
  unfold ContinuousLinearMap.opTrace
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by
    rw [ContinuousLinearMap.smul_apply, inner_smul_right]

theorem summable_inner_diag_quantumMasterEffectWeighted
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (R : ℝ) (k r : ℕ) :
    Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
      ((quantumChannelEffect C ^ (k + 1) *
        quantumMasterEffectComplement R C ^ r)
          (ContinuousLinearMap.hsBasis ℂ E i))) := by
  let T := quantumChannelEffect C
  let B := quantumMasterEffectComplement R C
  let A : E →L[ℂ] F := C ∘L (T ^ k * B ^ r)
  have hA : ContinuousLinearMap.IsHilbertSchmidt A := hC.comp_right _
  have hsum := ContinuousLinearMap.summable_inner_diag_comp
    hC.adjoint hA (ContinuousLinearMap.hsBasis ℂ E)
  have hfactor : ContinuousLinearMap.adjoint C ∘L A =
      T ^ (k + 1) * B ^ r := by
    change T * (T ^ k * B ^ r) = T ^ (k + 1) * B ^ r
    rw [← mul_assoc, ← pow_succ']
  exact hsum.congr fun i => by rw [hfactor]

theorem quantumMasterEffect_weightedOperator_succ
    (R : ℝ) (C : E →L[ℂ] F) (k r : ℕ) :
    quantumChannelEffect C ^ (k + 1) *
        quantumMasterEffectComplement R C ^ (r + 1) =
      (R : ℂ) •
          (quantumChannelEffect C ^ (k + 1) *
            quantumMasterEffectComplement R C ^ r) -
        quantumChannelEffect C ^ (k + 2) *
          quantumMasterEffectComplement R C ^ r := by
  let T := quantumChannelEffect C
  let B := quantumMasterEffectComplement R C
  change T ^ (k + 1) * B ^ (r + 1) =
    (R : ℂ) • (T ^ (k + 1) * B ^ r) - T ^ (k + 2) * B ^ r
  have hBpow : B ^ (r + 1) = B * B ^ r := pow_succ' B r
  have hTpow : T ^ (k + 1) * T = T ^ (k + 2) := by
    rw [← pow_succ]
  rw [hBpow, ← mul_assoc]
  rw [show B = (R : ℂ) • (1 : E →L[ℂ] E) - T by
    rfl]
  rw [mul_sub, sub_mul]
  simp only [mul_smul_comm, mul_one, smul_mul_assoc]
  rw [hTpow]

/-- Multiplication by the complement `R I - T` is exactly one scaled Hausdorff difference. -/
theorem quantumMasterEffectWeightedMoment_succ
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (R : ℝ) (k r : ℕ) :
    quantumMasterEffectWeightedMoment R C k (r + 1) =
      R * quantumMasterEffectWeightedMoment R C k r -
        quantumMasterEffectWeightedMoment R C (k + 1) r := by
  let A := quantumChannelEffect C ^ (k + 1) *
    quantumMasterEffectComplement R C ^ r
  let A' := quantumChannelEffect C ^ (k + 2) *
    quantumMasterEffectComplement R C ^ r
  have hA : Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
      (A (ContinuousLinearMap.hsBasis ℂ E i))) :=
    summable_inner_diag_quantumMasterEffectWeighted hC R k r
  have hA' : Summable (fun i => inner ℂ (ContinuousLinearMap.hsBasis ℂ E i)
      (A' (ContinuousLinearMap.hsBasis ℂ E i))) := by
    simpa only [A', show k + 1 + 1 = k + 2 by omega] using
      summable_inner_diag_quantumMasterEffectWeighted hC R (k + 1) r
  have htrace :
      ContinuousLinearMap.opTrace
          (quantumChannelEffect C ^ (k + 1) *
            quantumMasterEffectComplement R C ^ (r + 1)) =
        (R : ℂ) * ContinuousLinearMap.opTrace A -
          ContinuousLinearMap.opTrace A' := by
    rw [quantumMasterEffect_weightedOperator_succ]
    rw [opTrace_sub_eq_sub_of_summable_diag ((R : ℂ) • A) A'
      (hA.mul_left (R : ℂ)) hA']
    rw [opTrace_smul_eq (R : ℂ) A]
  have hre := congrArg Complex.re htrace
  simpa only [quantumMasterEffectWeightedMoment, A, A', Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    show k + 1 + 1 = k + 2 by omega] using hre

/-- Recursive `R`-scaled complementary difference of the master-effect trace moments. -/
def quantumMasterEffectScaledDifference
    (R : ℝ) (C : E →L[ℂ] F) (k : ℕ) : ℕ → ℝ
  | 0 => quantumMasterEffectMoment C k
  | r + 1 => R * quantumMasterEffectScaledDifference R C k r -
      quantumMasterEffectScaledDifference R C (k + 1) r

/-- The recursive scaled difference is the trace of the positive operator monomial
`T^(k+1) (R I - T)^r`. -/
theorem quantumMasterEffectScaledDifference_eq_weightedMoment
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (R : ℝ) (k r : ℕ) :
    quantumMasterEffectScaledDifference R C k r =
      quantumMasterEffectWeightedMoment R C k r := by
  induction r generalizing k with
  | zero =>
      simp [quantumMasterEffectScaledDifference,
        quantumMasterEffectWeightedMoment, quantumMasterEffectMoment]
  | succ r ih =>
      rw [quantumMasterEffectScaledDifference, ih k, ih (k + 1),
        ← quantumMasterEffectWeightedMoment_succ hC R k r]

/-- **All-order bounded-effect Hausdorff law.**  A channel radius `‖C‖² ≤ R` makes
every scaled complementary difference of the positive master-effect moments nonnegative. -/
theorem quantumMasterEffectScaledDifference_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    {R : ℝ} (hR : ‖C‖ ^ 2 ≤ R) (k r : ℕ) :
    0 ≤ quantumMasterEffectScaledDifference R C k r := by
  rw [quantumMasterEffectScaledDifference_eq_weightedMoment hC]
  exact quantumMasterEffectWeightedMoment_nonneg hC hR k r

/-- The operator-norm square of a Hilbert--Schmidt channel is at most its total HS mass. -/
theorem sq_opNorm_le_quantumMasterEffectMass
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    ‖C‖ ^ 2 ≤ quantumMasterEffectMass C := by
  have hop := ContinuousLinearMap.opNorm_le_hsNorm hC
  have hsquare : ‖C‖ ^ 2 ≤ ContinuousLinearMap.hsNorm C ^ 2 := by
    nlinarith [norm_nonneg C, ContinuousLinearMap.hsNorm_nonneg C]
  calc
    ‖C‖ ^ 2 ≤ ContinuousLinearMap.hsNorm C ^ 2 := hsquare
    _ = quantumMasterEffectMass C := by
      rw [ContinuousLinearMap.hsNorm,
        Real.sq_sqrt (ContinuousLinearMap.hsNormSq_nonneg C)]
      rfl

/-- Recursive complementary difference of the density-normalized replica moments. -/
def quantumMasterEffectReplicaDifference
    (C : E →L[ℂ] F) (k : ℕ) : ℕ → ℝ
  | 0 => quantumMasterEffectReplicaMoment C k
  | r + 1 => quantumMasterEffectReplicaDifference C k r -
      quantumMasterEffectReplicaDifference C (k + 1) r

theorem quantumMasterEffectReplicaDifference_eq_scaledDifference_div
    {C : E →L[ℂ] F} (hmass : quantumMasterEffectMass C ≠ 0) (k r : ℕ) :
    quantumMasterEffectReplicaDifference C k r =
      quantumMasterEffectScaledDifference (quantumMasterEffectMass C) C k r /
        quantumMasterEffectMass C ^ (k + r + 1) := by
  induction r generalizing k with
  | zero =>
      simp [quantumMasterEffectReplicaDifference,
        quantumMasterEffectScaledDifference, quantumMasterEffectReplicaMoment]
  | succ r ih =>
      rw [quantumMasterEffectReplicaDifference, ih k, ih (k + 1),
        quantumMasterEffectScaledDifference]
      field_simp [hmass]
      ring

/-- **Complete quantum Hausdorff positivity.**  Every density-operator replica sequence has
all complementary finite differences nonnegative. -/
theorem quantumMasterEffectReplicaDifference_nonneg
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C)
    (k r : ℕ) :
    0 ≤ quantumMasterEffectReplicaDifference C k r := by
  by_cases hmass : quantumMasterEffectMass C = 0
  · have hCzero : C = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mp hmass
    subst C
    have hzero : ∀ j, quantumMasterEffectReplicaDifference
        (0 : E →L[ℂ] F) j r = 0 := by
      intro j
      induction r generalizing j with
      | zero =>
          simp [quantumMasterEffectReplicaDifference,
            quantumMasterEffectReplicaMoment, quantumMasterEffectMoment,
            quantumMasterEffectMass, quantumChannelEffect]
      | succ r ih =>
          rw [quantumMasterEffectReplicaDifference, ih j, ih (j + 1), sub_self]
    rw [hzero k]
  · rw [quantumMasterEffectReplicaDifference_eq_scaledDifference_div hmass]
    exact div_nonneg
      (quantumMasterEffectScaledDifference_nonneg hC
        (sq_opNorm_le_quantumMasterEffectMass hC) k r)
      (pow_nonneg (ContinuousLinearMap.hsNormSq_nonneg C) _)

/-! ### Homogeneous replica log-convexity -/

/-- Real-part Cauchy--Schwarz in squared Hilbert--Schmidt form.  The proof uses the
nonnegativity of `||rS-T||²` at the minimizing real scalar, so no square-root manipulation is
needed. -/
theorem re_hsInner_sq_le_hsNormSq_mul
    {S T : E →L[ℂ] F}
    (hS : ContinuousLinearMap.IsHilbertSchmidt S)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    (ContinuousLinearMap.hsInner S T).re ^ 2 ≤
      ContinuousLinearMap.hsNormSq S * ContinuousLinearMap.hsNormSq T := by
  by_cases hSzero : ContinuousLinearMap.hsNormSq S = 0
  · have hzero : S = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff hS).mp hSzero
    subst S
    simp [ContinuousLinearMap.hsInner, ContinuousLinearMap.hsNormSq]
  · have hSpos : 0 < ContinuousLinearMap.hsNormSq S :=
      lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg S) (Ne.symm hSzero)
    let a := ContinuousLinearMap.hsNormSq S
    let b := (ContinuousLinearMap.hsInner S T).re
    let c := ContinuousLinearMap.hsNormSq T
    let r := b / a
    have hnonneg : 0 ≤
        ContinuousLinearMap.hsNormSq (((r : ℝ) : ℂ) • S - T) :=
      ContinuousLinearMap.hsNormSq_nonneg _
    rw [hsNormSq_real_smul_sub_eq hS hT] at hnonneg
    change 0 ≤ r ^ 2 * a - 2 * r * b + c at hnonneg
    change 0 < a at hSpos
    have hscaled : 0 ≤ a * (r ^ 2 * a - 2 * r * b + c) :=
      mul_nonneg hSpos.le hnonneg
    have hid :
        a * (r ^ 2 * a - 2 * r * b + c) = a * c - b ^ 2 := by
      dsimp only [r]
      field_simp [ne_of_gt hSpos]
      ring
    rw [hid] at hscaled
    change b ^ 2 ≤ a * c
    nlinarith

/-- **Quantum replica log-convexity.**  Consecutive trace powers of every positive
Hilbert--Schmidt master effect satisfy the homogeneous Hankel inequality
`M_(k+1)^2 ≤ M_k M_(k+2)`.  Unlike a Hausdorff finite difference, this relation is invariant
under rescaling the underlying channel. -/
theorem quantumMasterEffectMoment_logConvex
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    quantumMasterEffectMoment C (k + 1) ^ 2 ≤
      quantumMasterEffectMoment C k * quantumMasterEffectMoment C (k + 2) := by
  obtain ⟨n, h | h⟩ := Nat.even_or_odd' k
  · subst k
    have hA := quantumMasterEffectPowerColumn_isHilbertSchmidt hC n
    have hB := quantumMasterEffectPowerColumn_isHilbertSchmidt hC (n + 1)
    have hcs := re_hsInner_sq_le_hsNormSq_mul hA hB
    rw [re_hsInner_quantumMasterEffectPowerColumn_succ,
      ← quantumMasterEffectMoment_even_eq_hsNormSq hC n,
      ← quantumMasterEffectMoment_even_eq_hsNormSq hC (n + 1)] at hcs
    simpa only [show 2 * (n + 1) = 2 * n + 2 by omega] using hcs
  · subst k
    have hA := quantumChannelEffect_pow_isHilbertSchmidt hC
      (n := n + 1) (by omega)
    have hB := quantumChannelEffect_pow_isHilbertSchmidt hC
      (n := n + 2) (by omega)
    have hcs := re_hsInner_sq_le_hsNormSq_mul hA hB
    rw [re_hsInner_quantumChannelEffect_powers_succ,
      ← quantumMasterEffectMoment_odd_eq_hsNormSq hC n,
      ← quantumMasterEffectMoment_odd_eq_hsNormSq hC (n + 1)] at hcs
    simpa only [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega,
      show 2 * n + 2 = 2 * n + 1 + 1 by omega] using hcs

/-- Normalizing the master effect preserves adjacent replica log-convexity. -/
theorem quantumMasterEffectReplicaMoment_logConvex
    {C : E →L[ℂ] F} (hC : ContinuousLinearMap.IsHilbertSchmidt C) (k : ℕ) :
    quantumMasterEffectReplicaMoment C (k + 1) ^ 2 ≤
      quantumMasterEffectReplicaMoment C k *
        quantumMasterEffectReplicaMoment C (k + 2) := by
  by_cases hmass : quantumMasterEffectMass C = 0
  · have hCzero : C = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mp hmass
    subst C
    simp [quantumMasterEffectReplicaMoment, quantumMasterEffectMoment,
      quantumMasterEffectMass, quantumChannelEffect]
  · have hlog := quantumMasterEffectMoment_logConvex hC k
    rw [quantumMasterEffectReplicaMoment,
      quantumMasterEffectReplicaMoment,
      quantumMasterEffectReplicaMoment]
    calc
      (quantumMasterEffectMoment C (k + 1) /
          quantumMasterEffectMass C ^ (k + 1 + 1)) ^ 2 =
          quantumMasterEffectMoment C (k + 1) ^ 2 /
            (quantumMasterEffectMass C ^ (k + 1 + 1)) ^ 2 := by ring
      _ ≤ (quantumMasterEffectMoment C k *
            quantumMasterEffectMoment C (k + 2)) /
          (quantumMasterEffectMass C ^ (k + 1 + 1)) ^ 2 :=
        div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ = (quantumMasterEffectMoment C k /
            quantumMasterEffectMass C ^ (k + 1)) *
          (quantumMasterEffectMoment C (k + 2) /
            quantumMasterEffectMass C ^ (k + 2 + 1)) := by
        field_simp [hmass]
        ring

/-- Adjacent log-convexity is closed under coordinatewise limits.  This packages the exact
topological step needed when a projectively normalized source moment sequence converges to a
target sequence. -/
theorem logConvex_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {m : ι → ℕ → ℝ} {target : ℕ → ℝ}
    (k : ℕ)
    (hlim : ∀ j, Tendsto (fun i => m i j) l (nhds (target j)))
    (hlog : ∀ i, m i (k + 1) ^ 2 ≤ m i k * m i (k + 2)) :
    target (k + 1) ^ 2 ≤ target k * target (k + 2) := by
  exact le_of_tendsto_of_tendsto
    ((hlim (k + 1)).pow 2)
    ((hlim k).mul (hlim (k + 2)))
    (Filter.Eventually.of_forall hlog)

end

end HTGeometry
