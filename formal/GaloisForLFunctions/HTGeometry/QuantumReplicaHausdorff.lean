import GaloisForLFunctions.HTGeometry.QuantumChannelEnergyAugmentation

/-!
# Hausdorff convexity of quantum replica moments

If `C` is a Hilbert--Schmidt constraint channel and `T = C† C`, the normalized values

`Pₖ(C) = Re Tr(T^(k+1)) / Re Tr(T)^(k+1)`

are the replica moments of the density operator obtained by normalizing `T`.  The spectrum of a
density operator is contained in `[0, 1]`, so these values form a Hausdorff moment sequence.  This
file formalizes the first genuinely new complementary constraint beyond monotonicity: every
second complementary finite difference is nonnegative,

`0 ≤ Pₖ - 2 Pₖ₊₁ + Pₖ₊₂`.

The proof stays below spectral calculus.  Before normalization, the difference is exactly the
squared Hilbert--Schmidt norm of a difference of consecutive power columns (for even `k`) or
consecutive positive-effect powers (for odd `k`).  It is therefore reusable for rectangular
constraint channels on arbitrary complex Hilbert spaces.

Physics provenance: higher density-matrix moments are multi-copy quantum observables, and
positivity constraints on moment sequences are used as quantum-state and entanglement witnesses;
see A. Elben et al., *Nature Reviews Physics* 5 (2023), 9--24, arXiv:2203.11374, and
A. Neven et al., *npj Quantum Information* 7 (2021), 152, arXiv:2103.07443.
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
    push_cast
    ring
  have hUV : ContinuousLinearMap.hsInner U V =
      -(r : ℂ) * ContinuousLinearMap.hsInner S T := by
    dsimp only [U, V]
    change ContinuousLinearMap.hsInner ((r : ℂ) • S) ((-1 : ℂ) • T) = _
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
    ring
  have hVU : ContinuousLinearMap.hsInner V U =
      -(r : ℂ) * ContinuousLinearMap.hsInner T S := by
    dsimp only [U, V]
    change ContinuousLinearMap.hsInner ((-1 : ℂ) • T) ((r : ℂ) • S) = _
    rw [ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    simp
    ring
  have hVV : ContinuousLinearMap.hsInner V V =
      ContinuousLinearMap.hsInner T T := by
    dsimp only [V]
    change ContinuousLinearMap.hsInner ((-1 : ℂ) • T) ((-1 : ℂ) • T) = _
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
        Complex.neg_re, zero_mul, sub_zero, ContinuousLinearMap.hsInner_self_re hS,
        ContinuousLinearMap.hsInner_self_re hT, hcrossRe]
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
  ring

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
  rw [quantumMasterEffectMoment_even_eq_hsNormSq hC (n + 1)]
  ring

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
