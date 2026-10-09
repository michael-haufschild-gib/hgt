import GaloisForLFunctions.HTGeometry.ConeKernelCrossedProduct
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Full = reduced for `ℝ`: the regular representation of `C*(ℝ)` is faithful

The full group C⋆-algebra `C*(ℝ)` is the enveloping C⋆-algebra of `(C_c(ℝ), ⋆)` for the `L¹` norm.
For every `L¹`-bounded `*`-representation `π` of `C_c(ℝ)` on a Hilbert space and every `G`,
`‖π(G)‖ ≤ ‖C_G‖`, where `C_G = G ⋆ ·` is the convolution operator on `L²(ℝ)`
(`norm_le_norm_op_of_convL1Bounded`):

* `h = G* ⋆ G` gives the self-adjoint `π(h) = π(G)* π(G)`, so `‖π(h)‖^{2^j} = ‖π(h^{⋆2^j})‖`;
* `h^{⋆m}` is supported in `[-mw, mw]` (`convProfilePow_supportedIn`), so by Cauchy–Schwarz
  `‖h^{⋆m}‖₁ ≤ √(2mw) ‖h^{⋆m}‖₂` (`integral_norm_le_sqrt_mul_norm_cc2`);
* `h^{⋆m} = C_h(h^{⋆(m-1)})` in `L²` (`op_conv_cc2`), so `‖h^{⋆m}‖₂ ≤ ‖C_h‖^{m-1} ‖h‖₂`;
* Bernoulli's inequality: a ratio `‖π(h)‖ / ‖C_h‖ > 1` would make `r^m` beat `√m`; hence
  `‖π(G)‖² = ‖π(h)‖ ≤ ‖C_h‖ = ‖C_G‖²`.

Consequently the regular representation of `C*(ℝ)` is isometric (`norm_convRegular`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open BandKernel

/-! ## Convolution powers: support growth and the `L²` recursion -/

/-- `G` vanishes off `[-W, W]`. -/
def SupportedIn (G : C_c(ℝ, ℂ)) (W : ℝ) : Prop := ∀ s, W < |s| → G s = 0

theorem convProfile_apply (G₁ G₂ : C_c(ℝ, ℂ)) (s : ℝ) :
    convProfile G₁ G₂ s = ∫ y, G₁ (s - y) * G₂ y := by
  change (conv G₁ * conv G₂).toFun (s, 0) = _
  rw [mul_apply]
  congr 1
  funext y
  rw [conv_toFun, conv_toFun, sub_zero]

theorem SupportedIn.convProfile {G₁ G₂ : C_c(ℝ, ℂ)} {W₁ W₂ : ℝ} (h₁ : SupportedIn G₁ W₁)
    (h₂ : SupportedIn G₂ W₂) : SupportedIn (convProfile G₁ G₂) (W₁ + W₂) := fun s hs => by
  rw [convProfile_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  change G₁ (s - y) * G₂ y = 0
  by_cases hy : W₂ < |y|
  · rw [h₂ y hy, mul_zero]
  · push Not at hy
    have : W₁ < |s - y| := by
      have := abs_sub_abs_le_abs_sub s y
      linarith
    rw [h₁ _ this, zero_mul]

theorem exists_supportedIn (G : C_c(ℝ, ℂ)) : ∃ W, 0 ≤ W ∧ SupportedIn G W := by
  obtain ⟨R, hR⟩ := G.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun s hs => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hmem
  linarith [le_max_left R 0]

/-- The convolution operator of `G₁` sends the profile `G₂` to `G₁ ⋆ G₂`. -/
theorem op_conv_cc2 (G₁ G₂ : C_c(ℝ, ℂ)) :
    (conv G₁).op (cc2 G₂) = cc2 (convProfile G₁ G₂) := by
  apply Lp.ext
  filter_upwards [(conv G₁).op_ae (cc2 G₂), cc2_ae (convProfile G₁ G₂)] with x h1 h2
  rw [h1, h2, convProfile_apply]
  refine integral_congr_ae ?_
  filter_upwards [cc2_ae G₂] with y hy
  rw [conv_toFun, hy]

/-- **Cauchy–Schwarz on the support**: `‖G‖₁ ≤ √(2W) ‖G‖₂`. -/
theorem integral_norm_le_sqrt_mul_norm_cc2 {G : C_c(ℝ, ℂ)} {W : ℝ} (hW : 0 ≤ W)
    (hG : SupportedIn G W) : ∫ s, ‖G s‖ ≤ Real.sqrt (2 * W) * ‖cc2 G‖ := by
  set I := Icc (-W) W
  have hind : ∀ s, ‖G s‖ = I.indicator (fun _ => (1 : ℝ)) s * ‖G s‖ := fun s => by
    by_cases hs : s ∈ I
    · rw [indicator_of_mem hs, one_mul]
    · rw [indicator_of_notMem hs, zero_mul, hG s ?_, norm_zero]
      by_contra h
      push Not at h
      exact hs (abs_le.mp h)
  have hwi : Integrable (I.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hind2 : ∀ s, I.indicator (fun _ => (1 : ℝ)) s * ‖G s‖ ^ 2 = ‖G s‖ ^ 2 := fun s => by
    rw [sq, ← mul_assoc, ← hind]
  have hsq : Integrable fun s => I.indicator (fun _ => (1 : ℝ)) s * ‖G s‖ ^ 2 := by
    simp_rw [hind2]
    refine (G.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -W) (b := W)) fun s hs => ?_)
    have hs' : W < |s| := by
      by_contra h
      push Not at h
      exact hs (abs_le.mp h)
    change ‖G s‖ ^ 2 = 0
    rw [hG s hs', norm_zero]
    norm_num
  have hCS := sq_integral_weighted_le (μ := volume) (w := I.indicator fun _ => (1 : ℝ))
    (g := fun s => ‖G s‖) (fun s => indicator_nonneg (fun _ _ => zero_le_one) s)
    hwi.aestronglyMeasurable G.continuous.norm.aestronglyMeasurable hwi hsq
  simp_rw [← hind, hind2] at hCS
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, Measure.real,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), ← KernelAlg.norm_cc2_sq,
    show W - -W = 2 * W by ring] at hCS
  have h0 : 0 ≤ ∫ s, ‖G s‖ := integral_nonneg fun _ => norm_nonneg _
  calc ∫ s, ‖G s‖ = Real.sqrt ((∫ s, ‖G s‖) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (2 * W * ‖cc2 G‖ ^ 2) := Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (2 * W) * ‖cc2 G‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The convolution powers `g^{⋆(n+1)}`. -/
def convProfilePow (g : C_c(ℝ, ℂ)) : ℕ → C_c(ℝ, ℂ)
  | 0 => g
  | n + 1 => convProfile g (convProfilePow g n)

theorem convProfilePow_supportedIn {g : C_c(ℝ, ℂ)} {w : ℝ} (hg : SupportedIn g w) (n : ℕ) :
    SupportedIn (convProfilePow g n) (((n + 1 : ℕ) : ℝ) * w) := by
  induction n with
  | zero => simpa [convProfilePow] using hg
  | succ n ih =>
    have h := hg.convProfile ih
    have he : w + ((n + 1 : ℕ) : ℝ) * w = ((n + 1 + 1 : ℕ) : ℝ) * w := by push_cast; ring
    rw [he] at h
    exact h

/-- **The `L²` norms of convolution powers grow at most like the operator norm.** -/
theorem norm_cc2_convProfilePow_le (g : C_c(ℝ, ℂ)) (n : ℕ) :
    ‖cc2 (convProfilePow g n)‖ ≤ ‖(conv g).op‖ ^ n * ‖cc2 g‖ := by
  induction n with
  | zero => simp [convProfilePow]
  | succ n ih =>
    change ‖cc2 (convProfile g (convProfilePow g n))‖ ≤ _
    rw [← op_conv_cc2, pow_succ', mul_assoc]
    exact ((conv g).op.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem norm_op_conv_star_mul (G : C_c(ℝ, ℂ)) :
    ‖(conv (convProfile (starProfile G) G)).op‖ = ‖(conv G).op‖ ^ 2 := by
  rw [← conv_mul_conv, ← star_conv, op_mul, op_star]
  exact (ContinuousLinearMap.norm_adjoint_comp_self _).trans (sq _).symm

/-- A convolution kernel as an element of the convolution algebra. -/
def convElem (G : C_c(ℝ, ℂ)) : convKernels := ⟨conv G, ⟨G, rfl⟩⟩

theorem convElem_mul (G₁ G₂ : C_c(ℝ, ℂ)) :
    convElem G₁ * convElem G₂ = convElem (convProfile G₁ G₂) :=
  Subtype.ext (conv_mul_conv G₁ G₂)

theorem star_convElem (G : C_c(ℝ, ℂ)) : star (convElem G) = convElem (starProfile G) :=
  Subtype.ext (star_conv G)

theorem convL1Norm_convElem (G : C_c(ℝ, ℂ)) : convL1Norm (convElem G) = ∫ s, ‖G s‖ :=
  convL1Norm_conv G

section Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Full = reduced for `ℝ`.**  Every `L¹`-bounded `*`-representation of the convolution algebra
`(C_c(ℝ), ⋆)` is dominated by the regular representation: `‖π(G)‖ ≤ ‖G ⋆ ·‖_{B(L²)}`.

For `h = G* ⋆ G` the operator `π(h) = π(G)* π(G)` is self-adjoint, so
`‖π(G)‖^{2·2^j} = ‖π(h^{⋆2^j})‖ ≤ ‖h^{⋆2^j}‖₁`.  The power `h^{⋆m}` is supported in `[-mw, mw]`, so
Cauchy–Schwarz gives `‖h^{⋆m}‖₁ ≤ √(2mw) ‖h^{⋆m}‖₂ ≤ √(2mw) ‖C_h‖^{m-1} ‖h‖₂`; the factor `√m`
cannot beat a geometric ratio `> 1`, so `‖π(h)‖ ≤ ‖C_h‖ = ‖C_G‖²`. -/
theorem norm_le_norm_op_of_convL1Bounded (π : convKernels →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : ∀ K, ‖π K‖ ≤ convL1Norm K) (K : convKernels) :
    ‖π K‖ ≤ ‖(K : BandKernel).op‖ := by
  obtain ⟨_, ⟨G, rfl⟩⟩ := K
  change ‖π (convElem G)‖ ≤ _
  set g := convProfile (starProfile G) G
  have hh : convElem g = star (convElem G) * convElem G := by
    rw [star_convElem, convElem_mul]
  set A := π (convElem g)
  have hpow : ∀ n, π (convElem (convProfilePow g n)) = A ^ (n + 1) := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]; rfl
    | succ n ih =>
      change π (convElem (convProfile g (convProfilePow g n))) = _
      rw [← convElem_mul, map_mul, ih]
      exact (pow_succ' A (n + 1)).symm
  have hA : ‖A‖ = ‖π (convElem G)‖ ^ 2 := by
    change ‖π (convElem g)‖ = _
    rw [hh, map_mul, map_star]
    exact CStarRing.norm_star_mul_self.trans (sq _).symm
  have hAsa : IsSelfAdjoint A := by
    change IsSelfAdjoint (π (convElem g))
    rw [hh]
    exact (IsSelfAdjoint.star_mul_self (convElem G)).map π
  set b := ‖(conv g).op‖
  have hb : b = ‖(conv G).op‖ ^ 2 := norm_op_conv_star_mul G
  obtain ⟨w, hw0, hgw⟩ := exists_supportedIn g
  set c := ‖cc2 g‖
  have key : ∀ j : ℕ, ‖A‖ ^ (2 ^ j) ≤
      Real.sqrt (2 * (((2 ^ j : ℕ) : ℝ) * w)) * (b ^ (2 ^ j - 1) * c) := by
    intro j
    have hm : 2 ^ j - 1 + 1 = 2 ^ j := Nat.sub_add_cancel Nat.one_le_two_pow
    rw [← hAsa.norm_pow_two_pow j, ← hm, ← hpow]
    refine (hπ _).trans ?_
    rw [convL1Norm_convElem]
    refine (integral_norm_le_sqrt_mul_norm_cc2 (by positivity) (convProfilePow_supportedIn hgw _)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_cc2_convProfilePow_le g _) (Real.sqrt_nonneg _)
  have hAb : ‖A‖ ≤ b := by
    by_contra hlt
    push Not at hlt
    rcases (norm_nonneg _ : (0 : ℝ) ≤ b).eq_or_lt with hb0 | hbpos
    · have h1 := key 1
      have hb0' : b = 0 := hb0.symm
      rw [hb0'] at h1 hlt
      norm_num at h1
      rw [h1, norm_zero] at hlt
      exact lt_irrefl _ hlt
    · set r := ‖A‖ / b
      have hr : 1 < r := (one_lt_div hbpos).mpr hlt
      set D := Real.sqrt (2 * w) * c / b
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((D / (r - 1)) ^ 2) (by norm_num : (1 : ℝ) < 2)
      have hk := key j
      set N : ℕ := 2 ^ j
      have hN1 : 1 ≤ N := Nat.one_le_two_pow
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hNr : ((N : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast [N]; ring
      -- `‖A‖^N = r^N b^N` and cancel `b^(N-1)`
      have hAeq : ‖A‖ = r * b := by rw [div_mul_cancel₀ _ hbpos.ne']
      have hbN : b ^ N = b ^ (N - 1) * b := by
        rw [← pow_succ, Nat.sub_add_cancel hN1]
      have hcancel : r ^ N * b ≤ Real.sqrt (2 * ((N : ℝ) * w)) * c := by
        have hpos : 0 < b ^ (N - 1) := pow_pos hbpos _
        rw [hAeq, mul_pow, hbN] at hk
        have : r ^ N * b * b ^ (N - 1) ≤ Real.sqrt (2 * ((N : ℝ) * w)) * c * b ^ (N - 1) := by
          calc r ^ N * b * b ^ (N - 1) = r ^ N * (b ^ (N - 1) * b) := by ring
            _ ≤ _ := hk
            _ = _ := by ring
        exact le_of_mul_le_mul_right this hpos
      have hbern : 1 + (N : ℝ) * (r - 1) ≤ r ^ N := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ r - 1 by linarith) N
        rwa [add_sub_cancel] at this
      have hsqrtN : Real.sqrt (2 * ((N : ℝ) * w)) = Real.sqrt (2 * w) * Real.sqrt N := by
        rw [show 2 * ((N : ℝ) * w) = (2 * w) * N by ring, Real.sqrt_mul (by positivity)]
      have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
      have hsNpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
      -- `√N (r - 1) < D`
      have hlt1 : Real.sqrt N * (r - 1) < D := by
        have h2 : (N : ℝ) * (r - 1) * b < Real.sqrt (2 * w) * Real.sqrt N * c := by
          calc (N : ℝ) * (r - 1) * b < r ^ N * b := by
                exact mul_lt_mul_of_pos_right (by linarith) hbpos
            _ ≤ Real.sqrt (2 * ((N : ℝ) * w)) * c := hcancel
            _ = Real.sqrt (2 * w) * Real.sqrt N * c := by rw [hsqrtN]
        have h3 : Real.sqrt N * (Real.sqrt N * (r - 1) * b) <
            Real.sqrt N * (Real.sqrt (2 * w) * c) := by
          calc Real.sqrt N * (Real.sqrt N * (r - 1) * b)
              = Real.sqrt N * Real.sqrt N * (r - 1) * b := by ring
            _ = (N : ℝ) * (r - 1) * b := by rw [hsN]
            _ < Real.sqrt (2 * w) * Real.sqrt N * c := h2
            _ = Real.sqrt N * (Real.sqrt (2 * w) * c) := by ring
        have h4 := lt_of_mul_lt_mul_left h3 hsNpos.le
        rw [lt_div_iff₀ hbpos]
        linarith
      -- but `D / (r - 1) < √N`
      have hlt2 : D / (r - 1) < Real.sqrt N := by
        rw [hNr]
        exact Real.lt_sqrt_of_sq_lt hj
      have hr1 : 0 < r - 1 := by linarith
      rw [div_lt_iff₀ hr1] at hlt2
      linarith
  rw [hA, hb] at hAb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp hAb

end Spectral

/-! ## `C*(ℝ)` is represented faithfully on `L²(ℝ)` -/

theorem norm_toEnvelope_conv_le (K : convKernels) :
    ‖toEnvelope convKernels convL1Norm K‖ ≤ ‖(K : BandKernel).op‖ :=
  EnvFamily.norm_le_of_forall_le (norm_nonneg _) fun ρ =>
    norm_le_norm_op_of_convL1Bounded ρ.π ρ.bound K

/-- **Full = reduced for `ℝ`**: the regular representation of the full group C⋆-algebra `C*(ℝ)` by
convolution operators on `L²(ℝ)` is isometric. -/
theorem norm_convRegular (y : RealGroupCStar) : ‖convRegular y‖ = ‖y‖ := by
  have hcore : ∀ K : convKernels, ‖convRegular (toEnvelope convKernels convL1Norm K)‖ =
      ‖toEnvelope convKernels convL1Norm K‖ := fun K =>
    le_antisymm (convRegularRep.norm_le_envelope K)
      ((norm_toEnvelope_conv_le K).trans (le_of_eq (congrArg norm (convRegular_toEnvelope K).symm)))
  have h := (toEnvelope_dense convKernels convL1Norm).equalizer
    (continuous_norm.comp continuous_convRegular) continuous_norm (funext hcore)
  exact congrFun h y

theorem convRegular_injective : Function.Injective convRegular := by
  intro y z h
  have := norm_convRegular (y - z)
  rw [map_sub, h, sub_self, norm_zero] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this.symm)

end GaloisForLFunctions.HTGeometry
