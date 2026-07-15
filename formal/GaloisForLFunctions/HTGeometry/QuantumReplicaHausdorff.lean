import GaloisForLFunctions.HTGeometry.QuantumChannelEnergyAugmentation
import GaloisForLFunctions.HTGeometry.QuantumMasterEffectPurity

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
    simp [U, ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    push_cast
    ring
  have hUV : ContinuousLinearMap.hsInner U V =
      -(r : ℂ) * ContinuousLinearMap.hsInner S T := by
    simp [U, V,
      ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    ring
  have hVU : ContinuousLinearMap.hsInner V U =
      -(r : ℂ) * ContinuousLinearMap.hsInner T S := by
    simp [U, V,
      ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    ring
  have hVV : ContinuousLinearMap.hsInner V V =
      ContinuousLinearMap.hsInner T T := by
    simp [V,
      ContinuousLinearMap.hsInner_smul_left,
      ContinuousLinearMap.hsInner_smul_right]
    ring
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
  change ContinuousLinearMap.hsNormSq (U + V) = _
  calc
    ContinuousLinearMap.hsNormSq (U + V) =
        (ContinuousLinearMap.hsInner (U + V) (U + V)).re :=
      (ContinuousLinearMap.hsInner_self_re hD).symm
    _ = r ^ 2 * ContinuousLinearMap.hsNormSq S -
          2 * r * (ContinuousLinearMap.hsInner S T).re +
            ContinuousLinearMap.hsNormSq T := by
      rw [hpair, hUU, hUV, hVU, hVV]
      simp only [map_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        neg_re, zero_mul, sub_zero, ContinuousLinearMap.hsInner_self_re hS,
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
      ring
    rw [heq]
    exact div_nonneg hdiff (pow_nonneg hmassPos.le _)

end

end HTGeometry
