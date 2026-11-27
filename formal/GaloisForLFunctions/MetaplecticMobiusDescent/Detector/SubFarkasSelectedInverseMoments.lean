import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1CoreColumnEnergy
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SubFarkasDetectorRowCounts
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# Sub-`16799/19200` selected inverse-marked moments via Stage-1 complete-factor selection

Propagates the Stage-1 core column energy bound (`stage1_core_normalized_column_energy`) from
`Stage1CoreColumnEnergy` through the initial Poisson-reflection, dyadic window, Fourier-overlap,
assigned-slot deletion, and moving-profile dictionary chain to establish `MomentsSub16799` across
all dyadic scales `1 / 2 ≤ d ≤ 5 / 6` and fiber inverse lengths `69 / 100 ≤ F.r ≤ 19 / 26` with
selected width `∑ s ∈ selected, F.widths s < 269 / 500 - (69 / 125) * F.r`.

Key structural features:
* Setting `r_param := rr + Aslot + 7 * η₀ + 5 * η_core` at row norm exponent `m := 1 + D.t / 2`
  eliminates the left range `r_param < 17 / 25` identically (`69 / 100 > 17 / 25`), dispatches
  `17 / 25 ≤ r_param ≤ 19 / 26` to `stage1_core_normalized_column_energy`, and dispatches
  `19 / 26 < r_param` to `canonical_marked_energy_exists` with positive margin `D.t / 4` across the
  entire closed interval `69 / 100 ≤ r ≤ 19 / 26`.
* In the overlap Fourier integral over `t : ℝ`, frequencies `|t| ≤ (1 / (8 * π)) * Z_dual ^ τ_dual`
  keep `|(z - 2 π i t).im| ≤ (3 / 4) * Z_dual ^ τ_dual`, while frequencies `|t| > T_cut` are
  absorbed pointwise into `(1 + ‖t‖) ^ (2 * N_tail)` via the unconditional Stage-0 row bound at
  `m_big = 10` without splitting the integral.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace SubFarkasSelectedInverseMoments

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CubicSieve CenteredMomentFourier
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment InverseMoment
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerSourceMask
open InverseInitialEnergyCallerEmpty InverseInitialPhysicalReassembly
open InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState InverseInitialEnergyCallerState
open InverseInitialCanonicalEnergy InverseInitialHighFrequencyTail InverseInitialPhysicalLimit
open InverseInitialDyadicAssembly InverseInitialProfileBounds
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialOverlapFourier InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialExcludedGeometry InverseInitialMarkedAssignedGeometry
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseMarkedPhysicalRows
open DetectorDictionaryInverseClippedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorAdaptiveCutoff ProbePhysical ProbeHighRowFamily
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands Parameters
open JointLogSeparation SubSevenEighthsHighTransport
open Stage1DualSixthFreeEnergy Stage1CoreColumnEnergy
open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.Budget

local notation "O" => Eisenstein.O

/-! ### Part I: Algebraic, radical-norm, subtype-reindex, and Stage-1 child margin helpers -/

/-- Multiplying `primeProfile V D ζ P` (`P ≠ 0`, `D > 0`) by `kernelLogPhase (-t) (log (N(P) / D))`
shifts the complex exponent from `ζ` to `ζ - 2 π i t`, preserving `.re` and shifting `.im`. -/
lemma primeProfile_mul_kernelLogPhase (V : ℝ → ℂ) {D_sc : ℝ} (hD : 0 < D_sc)
    (ζ : ℂ) (t : ℝ) {P : Ideal O} (hP : P ≠ 0) :
    let ζ_t : ℂ := ζ - ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
    primeProfile V D_sc ζ P * kernelLogPhase (-t) (Real.log ((P.absNorm : ℝ) / D_sc)) =
      primeProfile V D_sc ζ_t P ∧
    ζ_t.re = ζ.re ∧
    |ζ_t.im| ≤ |ζ.im| + 2 * Real.pi * |t| := by
  intro ζ_t
  have hP_pos : 0 < (P.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  let x : ℝ := (P.absNorm : ℝ) / D_sc
  have hx_pos : 0 < x := div_pos hP_pos hD
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold primeProfile
    change V x * (x : ℂ) ^ (ζ - 1) * kernelLogPhase (-t) (Real.log x) =
      V x * (x : ℂ) ^ (ζ_t - 1)
    rw [mul_assoc, Complex.cpow_def_of_ne_zero hx_ne, Complex.cpow_def_of_ne_zero hx_ne,
      ← Complex.ofReal_log hx_pos.le, kernelLogPhase, ← Complex.exp_add]
    exact congrArg (fun z => V x * Complex.exp z) (by dsimp only [ζ_t]; push_cast; ring)
  · simp [ζ_t]
  · have him : ζ_t.im = ζ.im - 2 * Real.pi * t := by simp [ζ_t]
    rw [him]
    calc |ζ.im - 2 * Real.pi * t|
        ≤ |ζ.im| + |2 * Real.pi * t| := abs_sub _ _
      _ = |ζ.im| + 2 * Real.pi * |t| := by
          rw [abs_mul, abs_of_pos (mul_pos zero_lt_two Real.pi_pos)]

/-- Since `I ≤ I.radical`, `I.radical ∣ I`, so `(I.radical.absNorm : ℝ) ≤ (I.absNorm : ℝ)`. -/
lemma radical_absNorm_le_self {m₀ : O} (hm₀ : m₀ ≠ 0) :
    (Ideal.absNorm (Ideal.span {m₀} : Ideal O).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m₀} : Ideal O) : ℝ) := by
  have hI0 : (Ideal.span {m₀} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hm₀
  exact (divisor_norm_bounds hI0 (Ideal.dvd_iff_le.mpr Ideal.le_radical)).2

/-- Reindexing `normalizedColumnEnergy` from `subslots : Finset ↥selected` to
`subslots.image Subtype.val : Finset (Fin N)` preserves both the energy and the width sum. -/
lemma normalizedColumnEnergy_subtype_image
    {ι : Type} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (pool : Finset ι) (Ψ : O →* ℂ) (m₀ : O)
    {N : ℕ} (selected : Finset (Fin N)) (subslots : Finset ↥selected)
    (lists_full : Fin N → Finset ι) (a : Fin N → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (weight : Ideal O → ℝ)
    (W : ℝ → ℂ) (X U F : ℝ) (w_fn : Fin N → ℝ) :
    normalizedColumnEnergy p hg pool Ψ m₀ subslots
      (fun s : ↥selected => lists_full s.val) (fun s : ↥selected => a s.val)
      labels rows weight W X U F =
    normalizedColumnEnergy p hg pool Ψ m₀ (subslots.image Subtype.val)
      lists_full a labels rows weight W X U F ∧
    (∑ j ∈ subslots.image Subtype.val, w_fn j) = ∑ s ∈ subslots, w_fn s.val := by
  have hinj : Set.InjOn (Subtype.val : ↥selected → Fin N) subslots :=
    fun _ _ _ _ h => Subtype.ext h
  have hpm : primeMark (subslots.image Subtype.val) lists_full a =
      primeMark subslots (fun s : ↥selected => lists_full s.val) (fun s : ↥selected => a s.val) := by
    funext A; unfold primeMark
    exact Finset.prod_image hinj
  refine ⟨?_, Finset.sum_image hinj⟩
  unfold normalizedColumnEnergy finiteCanonicalMarkedRow
  rw [hpm]

/-- Monotonicity of `Moments` in the moment exponent `εm` when `1 ≤ U` and `0 ≤ C`. -/
lemma moments_mono_eps {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C height εm₁ εm₂ : ℝ} (hU : 1 ≤ U) (hC : 0 ≤ C) (hε : εm₁ ≤ εm₂)
    (hm : Moments F Δ c κ C height εm₁) :
    Moments F Δ c κ C height εm₂ where
  inverse_raw := hm.inverse_raw
  inverse_marked sel hsel hc1 hc2 n hn s hs t ht :=
    (hm.inverse_marked sel hsel hc1 hc2 n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by linarith only [hε])) hC)
  plain_marked sel hsel hc j k hjk s hs t ht :=
    (hm.plain_marked sel hsel hc j k hjk s hs t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by linarith only [hε])) hC)
  plain_unmarked j k hjk s hs t ht :=
    (hm.plain_unmarked j k hjk s hs t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by linarith only [hε])) hC)

/-- Pure real-arithmetic Stage-1 initial-window child certificate at `m = 1 + t₀ / 2`,
`η₀ = τ₀ = t₀ / 10000`, `η_core = t₀ / 1000`: verifies `r_param ≥ 17 / 25`, `Q ≤ 3`, and splits
between the Stage-1 core range `r_param ≤ 19 / 26` and the `u = 0` Stage-0 range `r_param > 19 / 26`. -/
lemma stage1_initial_child_arithmetic
    {t₀ r_orig_in rr z_all G Aslot z_S₀ D_val B θ v H Q : ℝ}
    (ht₀_pos : 0 < t₀) (ht₀_sm : t₀ ≤ 1 / 100000000)
    (hr0 : 69 / 100 ≤ r_orig_in) (hr1 : r_orig_in ≤ 19 / 26)
    (hrr_lo : r_orig_in - t₀ / 10000 ≤ rr) (hrr_hi : rr ≤ r_orig_in)
    (hz_all_hi : z_all ≤ stage1Line r_orig_in)
    (hG0 : 0 ≤ G) (hA0 : 0 ≤ Aslot) (hzS0 : 0 ≤ z_S₀)
    (hz_part : z_all = z_S₀ + G + Aslot)
    (hD_eq : D_val = rr + z_all - 2 * G)
    (hP_lo : -2 * (t₀ / 10000) ≤ B - θ)
    (hQ_hi : Q ≤ (B - θ) + G + 3 * (t₀ / 10000))
    (hclip_hi : max 0 (D_val - B - v) - (D_val - B - v) ≤ 3 * (t₀ / 10000))
    (_hV0 : 0 ≤ θ + v + 2 * (t₀ / 10000))
    (hM0 : 0 ≤ θ + H + 2 * (t₀ / 10000))
    (hM_init : θ + H + 2 * (t₀ / 10000) ≤
      initialM (1 + t₀ / 2) rr z_all G (B - θ) (t₀ / 10000) (t₀ / 10000)) :
    let η₀ : ℝ := t₀ / 10000
    let η_core : ℝ := t₀ / 1000
    let N₀ : ℝ := max 0 (columnCenter D_val B v)
    let V₀ : ℝ := θ + v + 2 * η₀
    let M₀ : ℝ := θ + H + 2 * η₀
    let r_param : ℝ := rr + Aslot + 7 * η₀ + 5 * η_core
    let pad_init : ℝ := 7 * η₀ + 5 * η_core
    17 / 25 ≤ r_param ∧
    0 ≤ pad_init ∧ pad_init ≤ t₀ ∧
    N₀ + V₀ ≤ 3 ∧ M₀ ≤ N₀ + V₀ ∧ M₀ ≤ 8 ∧ N₀ + V₀ ≤ 8 ∧
    M₀ ≤ 2 * (N₀ + V₀) - 1 + 21 * η_core ∧
    z_S₀ ≤ stage1Line r_param + pad_init ∧
    (N₀ + V₀) - z_S₀ + 5 * η_core ≤ r_param ∧
    (r_param ≤ 19 / 26 →
      Q ≤ 3 ∧
      (-(53 / 12500 : ℝ) - t₀ / 100) ≤ (N₀ + V₀) - M₀ - Q - (z_S₀ + η_core) ∧
      (1 / 5 : ℝ) ≤ 4 * (N₀ + V₀) - 3 * M₀ - 6 * (z_S₀ + η_core)) ∧
    (19 / 26 < r_param →
      CanonicalMargins (N₀ + V₀) M₀ Q (z_S₀ + η₀) (t₀ / 4)) := by
  intro η₀ η_core N₀ V₀ M₀ r_param pad_init
  let δclip : ℝ := N₀ - (D_val - B - v)
  have hδ0 : 0 ≤ δclip := by dsimp only [N₀, δclip]; unfold columnCenter; exact sub_nonneg.mpr (le_max_right _ _)
  have hNV_eq : N₀ + V₀ = rr + z_all - 2 * G - (B - θ) + δclip + 2 * η₀ := by
    dsimp only [N₀, V₀, δclip]; rw [hD_eq]; ring
  have hM_expand : M₀ ≤ 2 * (rr + z_all - 2 * G) - (1 + t₀ / 2) - 2 * (B - θ) + 7 * η₀ := by
    unfold initialM at hM_init
    dsimp only [M₀, η₀] at hM_init ⊢
    linarith only [hM_init]
  have hhr_17 : 17 / 25 ≤ r_param := by
    dsimp only [r_param, η₀, η_core] at hrr_lo ⊢
    linarith only [hr0, hrr_lo, hA0, ht₀_pos]
  have hpad0 : 0 ≤ pad_init := by dsimp only [pad_init, η₀, η_core]; positivity
  have hpad_t : pad_init ≤ t₀ := by dsimp only [pad_init, η₀, η_core]; linarith only [ht₀_pos]
  have hz_all_max : z_all ≤ 1964 / 12500 := by
    unfold stage1Line at hz_all_hi; linarith only [hz_all_hi, hr0]
  have hNV_le2 : N₀ + V₀ ≤ 2 := by
    have hδ_hi : δclip ≤ 3 * (t₀ / 10000) := by dsimp only [N₀, δclip]; unfold columnCenter; exact hclip_hi
    dsimp only [η₀] at hP_lo hNV_eq ⊢
    linarith only [hNV_eq, hrr_hi, hr1, hz_all_max, hG0, hP_lo, hδ_hi, ht₀_sm, ht₀_pos]
  have hM_2NV : M₀ ≤ 2 * (N₀ + V₀) - 1 + 21 * η_core := by
    dsimp only [η₀, η_core] at hNV_eq hM_expand ⊢
    linarith only [hNV_eq, hM_expand, hδ0, ht₀_pos]
  have hM_NV : M₀ ≤ N₀ + V₀ := by
    dsimp only [η₀] at hNV_eq hM_expand hP_lo ⊢
    linarith only [hNV_eq, hM_expand, hrr_hi, hr1, hz_all_max, hG0, hP_lo, hδ0, ht₀_sm, ht₀_pos]
  have hz_line : z_S₀ ≤ stage1Line r_param + pad_init := by
    unfold stage1Line at hz_all_hi ⊢
    dsimp only [r_param, pad_init, η₀, η_core]
    linarith only [hz_all_hi, hz_part, hG0, hA0, hrr_hi, ht₀_pos]
  have hNV_r : (N₀ + V₀) - z_S₀ + 5 * η_core ≤ r_param := by
    have hδ_hi : δclip ≤ 3 * (t₀ / 10000) := by dsimp only [N₀, δclip]; unfold columnCenter; exact hclip_hi
    dsimp only [r_param, η₀, η_core] at hP_lo hNV_eq ⊢
    linarith only [hNV_eq, hz_part, hG0, hP_lo, hδ_hi]
  have hc2_base : (1 / 5 : ℝ) ≤ 4 * (N₀ + V₀) - 3 * M₀ - 6 * (z_S₀ + η_core) := by
    dsimp only [η₀, η_core] at hNV_eq hM_expand hP_lo ⊢
    linarith only [hNV_eq, hM_expand, hz_part, hrr_hi, hr1, hz_all_max, hG0, hA0, hP_lo, hδ0, ht₀_sm, ht₀_pos]
  have hc1_lower : (1 + t₀ / 2) - rr - Aslot - 2 * z_S₀ + δclip - 9 * η₀ ≤
      (N₀ + V₀) - M₀ - Q - z_S₀ := by
    dsimp only [η₀] at hNV_eq hM_expand hQ_hi ⊢
    linarith only [hNV_eq, hM_expand, hQ_hi, hz_part, ht₀_pos]
  refine ⟨hhr_17, hpad0, hpad_t, by linarith only [hNV_le2], hM_NV,
    by linarith only [hM_NV, hNV_le2], by linarith only [hNV_le2],
    hM_2NV, hz_line, hNV_r, ?_, ?_⟩
  · intro hrp_hi
    have hr_69 : 69 / 100 ≤ r_param := by
      dsimp only [r_param, η₀, η_core] at hrr_lo ⊢
      linarith only [hr0, hrr_lo, hA0, ht₀_pos]
    have hline_min : -53 / 12500 ≤ 1 - r_param - 2 * stage1Line r_param := by
      unfold stage1Line; linarith only [hr_69]
    have hc1_s1 : (-(53 / 12500 : ℝ) - t₀ / 100) ≤ (N₀ + V₀) - M₀ - Q - (z_S₀ + η_core) := by
      dsimp only [r_param, pad_init, η₀, η_core] at hc1_lower hz_line hline_min ⊢
      linarith only [hc1_lower, hz_line, hline_min, hδ0, ht₀_pos]
    have hQ3 : Q ≤ 3 := by
      dsimp only [M₀, η₀, η_core] at hc1_s1 hM0
      linarith only [hc1_s1, hNV_le2, hM0, hzS0, ht₀_sm, ht₀_pos]
    exact ⟨hQ3, hc1_s1, hc2_base⟩
  · intro hrp_gt
    have hsum_s0 : rr + Aslot + 2 * z_S₀ ≤ 1 + 7 * η₀ + 5 * η_core := by
      unfold stage1Line at hz_all_hi
      dsimp only [r_param] at hrp_gt
      linarith only [hz_all_hi, hz_part, hG0, hrp_gt, hrr_hi, hr1]
    unfold CanonicalMargins
    refine ⟨?_, ?_⟩
    · dsimp only [η₀, η_core] at hc1_lower hsum_s0 ⊢
      linarith only [hc1_lower, hsum_s0, hδ0, ht₀_pos]
    · dsimp only [η₀, η_core] at hc2_base ⊢
      linarith only [hc2_base, ht₀_sm, ht₀_pos]

/-! ### Part II: Single-window and dyadic physical block bounds on `[69/100, 19/26]` -/

/-- Single-`fresh` child `normalizedColumnEnergy` bound on `(Finset.univ \ assigned) \ J_drop`
(`Finset.univ : Finset ↥selected`), dispatching `r_param ≤ 19 / 26` to
`stage1_core_normalized_column_energy` and `19 / 26 < r_param` to `canonical_marked_energy_exists`. -/
private theorem stage1_single_child_energy
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (fresh : 𝓢(ℝ, ℂ)) {af bf : ℝ} (haf : 0 < af) (hab : af ≤ bf)
    (hsf : Function.support (fresh : ℝ → ℂ) ⊆ Set.Icc af bf) :
    let η₀ : ℝ := D.t / 10000
    ∃ (τ_dual B_ch : ℝ) (deg_ch : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_ch ∧
      ∀ data : RowData, ∃ C_ch U_ch : ℝ, 0 < C_ch ∧ 2 ≤ U_ch ∧
      ∀ U : ℝ, U_ch ≤ U →
      ∀ Dpool : ℕ, B_ch * U ^ (10 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
        fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
      let p := poolPrimary F_pool
      let hg := poolPrimary_good F_pool hFa
      let base := elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_orig_in rr D_val B v θ H : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      ∀ (assigned : Finset ↥selected) (J_drop J_other : Finset ↥selected),
        J_drop ⊆ Finset.univ \ assigned → J_other ⊆ Finset.univ \ assigned →
      let z_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      D_val = rr + assignedCenter Finset.univ z_sel - 2 * assignedCenter assigned z_sel →
      -2 * η₀ ≤ B - θ →
      max 0 (D_val - B - v) - (D_val - B - v) ≤ 3 * η₀ →
      0 ≤ θ + v + 2 * η₀ → 0 ≤ θ + H + 2 * η₀ →
      θ + H + 2 * η₀ ≤ initialM (1 + D.t / 2) rr (assignedCenter Finset.univ z_sel)
        (assignedCenter assigned z_sel) (B - θ) η₀ η₀ →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ selected, lists_full j = poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (selected : Set (Fin D.N)).PairwiseDisjoint lists_full →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ selected, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      ∀ (Ψ : O →* ℂ) (j_el : O) (t_id : Ideal O),
        CanonicalCoefficientClass.IsBaseRayTwist base Ψ →
        (∀ u, ‖Ψ u‖ ≤ 1) →
        j_el * primaryIdealGenerator t_id ≠ 0 →
        0 ≤ fullPunctureWidth U t_id j_el →
        ‖ringComplex (j_el * primaryIdealGenerator t_id)‖ ^ 2 = U ^ (fullPunctureWidth U t_id j_el) →
        fullPunctureWidth U t_id j_el ≤ (B - θ) + assignedCenter assigned z_sel + 3 * η₀ →
      ∀ (s : ℝ),
        let F_norm : ℝ := max 0 (columnCenter D_val B v) + (θ + v)
        normalizedColumnEnergy p hg Finset.univ Ψ (j_el * primaryIdealGenerator t_id)
          ((Finset.univ \ assigned) \ J_drop) (fun x : ↥selected => lists_full x.val)
          (fun x : ↥selected => a x.val)
          (CanonicalRowCompletion.idealRange (U ^ (θ + v + 2 * η₀))) (nonzeroChildFrequencyBall 1 (U ^ (θ + H + 2 * η₀)))
          (fun f => ((idealDivisors f).card : ℝ) ^ (J_drop.card + J_other.card + 1))
          (childLogTest fresh s) (U ^ (max 0 (columnCenter D_val B v))) U F_norm ≤
          (C_ch * U ^ (F_norm + (4 * η₀ + 13 * D.t))) * (1 + ‖s‖) ^ (2 * deg_ch) := by
  intro η₀
  have ht_pos : 0 < D.t := D.t_pos
  have ht_sm : D.t ≤ 1 / 100000000 := D.t_small
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; positivity
  obtain ⟨τ_dual, B_core, deg_core, hτ_pos, hτ_le_d, hBcore1, hcore_all⟩ :=
    stage1_core_normalized_column_energy hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb F_dual
      (fresh : ℝ → ℂ) haf (haf.trans_le hab).le hsf (fresh.smooth ⊤) 3 (by norm_num)
  obtain ⟨deg_0, B_0, _hB0_1, hm0_all⟩ :=
    canonical_marked_energy_exists 8 8 (D.t / 4) D.t (by norm_num) (by norm_num)
      (by positivity) ht_pos D.N fresh af bf haf (haf.trans_le hab).le hsf
  let deg_ch : ℕ := max deg_core deg_0
  let B_ch : ℝ := max B_core B_0
  refine ⟨τ_dual, B_ch, deg_ch, hτ_pos, by rw [← ht_eq]; exact hτ_le_d, hBcore1.trans (le_max_left _ _), ?_⟩
  intro data
  obtain ⟨hq_per, _, hbase1, hbase_per⟩ := raw_conjugate_base_gates data
  obtain ⟨C_core, U_core, hC_core, hUcore2, hcore⟩ := hcore_all data
  obtain ⟨C_0, U_0, hC_0, _hU0_1, hm0⟩ := hm0_all _ hq_per
  have hev_2N : ∀ᶠ U : ℝ in atTop, (2 : ℝ) ^ D.N ≤ U ^ η₀ :=
    (tendsto_rpow_atTop hη₀_pos).eventually (eventually_ge_atTop ((2 : ℝ) ^ D.N))
  obtain ⟨U_2N, hU_2N⟩ := eventually_atTop.mp hev_2N
  let U_ch : ℝ := max U_core (max U_0 U_2N)
  have hUch2 : 2 ≤ U_ch := hUcore2.trans (le_max_left _ _)
  let C_ch : ℝ := C_core + C_0
  refine ⟨C_ch, U_ch, add_pos hC_core hC_0, hUch2, ?_⟩
  intro U hU Dpool hDpool q_per F_pool hFa p hg base
    d_outer r_orig_in rr D_val B v θ H
    hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi selected hz_sel_hi assigned J_drop J_other hJ₁ hJ₂
    z_sel Z_slot Z_dual hD_eq hP_lo hclip_hi hV0 hM0 hM_init hlarge_Z
    lists_full hlists_full hdisj_sel ζ_base hζ_re hζ_im a ha_eq
    Ψ j_el t_id hΨ_base hΨ1 hm_ne hQ0 hm_norm_eq hQ_hi s F_norm
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU1 : 1 < U := by have h2 := hUch2.trans hU; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have h2N_η₀ : (2 : ℝ) ^ D.N ≤ U ^ η₀ :=
    hU_2N U (((le_max_right _ _).trans (le_max_right _ _)).trans hU)
  let slots : Finset ↥selected := Finset.univ \ assigned
  let subslots : Finset ↥selected := slots \ J_drop
  let S₀ : Finset (Fin D.N) := subslots.image Subtype.val
  have hS₀_sub_sel : S₀ ⊆ selected := fun j hj => by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hj; exact x.property
  have hz_pos : ∀ x : ↥selected, 0 ≤ z_sel x :=
    fun x => div_nonneg (D.slots_bounds x.val).1.le hd_pos.le
  have hz_all_eq : assignedCenter Finset.univ z_sel = ∑ j ∈ selected, D.ell j / d_outer := by
    dsimp only [assignedCenter, z_sel]; exact Finset.sum_coe_sort selected (fun j => D.ell j / d_outer)
  have himg := normalizedColumnEnergy_subtype_image p hg Finset.univ Ψ
    (j_el * primaryIdealGenerator t_id) selected subslots lists_full a
    (CanonicalRowCompletion.idealRange (U ^ (θ + v + 2 * η₀))) (nonzeroChildFrequencyBall 1 (U ^ (θ + H + 2 * η₀)))
    (secondLabelWeight D.N) (childLogTest fresh s)
    (U ^ (max 0 (columnCenter D_val B v))) U (max 0 (columnCenter D_val B v) + (θ + v + 2 * η₀))
    (fun j => D.ell j / d_outer)
  have hz_part : assignedCenter Finset.univ z_sel =
      (∑ j ∈ S₀, D.ell j / d_outer) + assignedCenter assigned z_sel + ∑ x ∈ J_drop, z_sel x := by
    have h1 : (∑ x ∈ subslots, z_sel x) + (∑ x ∈ J_drop, z_sel x) = ∑ x ∈ slots, z_sel x :=
      Finset.sum_sdiff hJ₁
    have h2 : (∑ x ∈ slots, z_sel x) + (∑ x ∈ assigned, z_sel x) = ∑ x : ↥selected, z_sel x :=
      Finset.sum_sdiff (Finset.subset_univ assigned)
    have himg2 := himg.2
    dsimp only [assignedCenter, z_sel] at h1 h2 himg2 ⊢
    linarith only [h1, h2, himg2]
  have harith := stage1_initial_child_arithmetic ht_pos ht_sm hr0 hr1
    (by simpa only [η₀] using hrr_lo) hrr_hi (hz_all_eq.trans_le hz_sel_hi)
    (Finset.sum_nonneg (fun x _ => hz_pos x))
    (Finset.sum_nonneg (fun x _ => hz_pos x))
    (Finset.sum_nonneg (fun j _ => div_nonneg (D.slots_bounds j).1.le hd_pos.le))
    hz_part hD_eq hP_lo hQ_hi hclip_hi hV0 hM0 hM_init
  let N₀ : ℝ := max 0 (columnCenter D_val B v)
  let V₀ : ℝ := θ + v + 2 * η₀
  let M₀ : ℝ := θ + H + 2 * η₀
  have hslots_card : slots.card ≤ D.N :=
    ((Finset.card_le_univ slots).trans_eq (Fintype.card_coe selected)).trans
      ((Finset.card_le_univ selected).trans_eq (Fintype.card_fin D.N))
  have hlabels_adm : ∀ f ∈ CanonicalRowCompletion.idealRange (U ^ V₀),
      CanonicalQuadraticSieve.Admissible f ∧ (f.absNorm : ℝ) ≤ U ^ V₀ :=
    fun f hf => ⟨(admissible_iff_native f).mpr (CanonicalRowCompletion.mem_idealRange.mp hf).1,
      (CanonicalRowCompletion.mem_idealRange.mp hf).2⟩
  have hwt : ∀ f ∈ CanonicalRowCompletion.idealRange (U ^ V₀),
      ((idealDivisors f).card : ℝ) ^ (J_drop.card + J_other.card + 1) ≤ secondLabelWeight D.N f :=
    fun f hf => assigned_label_weight_le slots J_drop J_other D.N hslots_card hJ₁ hJ₂ f
      (hlabels_adm f hf).1.1
  rcases le_or_gt (rr + (∑ x ∈ J_drop, z_sel x) + 7 * η₀ + 5 * (D.t / 1000)) (19 / 26) with hrp_le | hrp_gt
  · obtain ⟨hQ3, hc1_s1, hc2_s1⟩ := harith.2.2.2.2.2.2.2.2.2.2.1 hrp_le
    have hDp_core : B_core * U ^ (2 * (3 : ℝ) + 4) ≤ (Dpool : ℝ) := by
      rw [show (2 * (3 : ℝ) + 4 : ℝ) = (10 : ℝ) by ring]
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hU_pos.le _)).trans hDpool
    rw [normalization_change p hg Finset.univ Ψ (j_el * primaryIdealGenerator t_id) subslots
      (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val)
      (CanonicalRowCompletion.idealRange (U ^ V₀)) (nonzeroChildFrequencyBall 1 (U ^ M₀))
      (fun f => ((idealDivisors f).card : ℝ) ^ (J_drop.card + J_other.card + 1))
      (childLogTest fresh s) (U ^ N₀) U F_norm (N₀ + V₀) hU_pos]
    have hle_wt := energy_range_weight_le p hg Finset.univ Ψ (j_el * primaryIdealGenerator t_id)
      subslots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val)
      (CanonicalRowCompletion.idealRange (U ^ V₀)) (nonzeroChildFrequencyBall 1 (U ^ M₀))
      (nonzeroChildFrequencyBall 1 (U ^ M₀))
      (fun f => ((idealDivisors f).card : ℝ) ^ (J_drop.card + J_other.card + 1))
      (secondLabelWeight D.N)
      (childLogTest fresh s) (U ^ N₀) U (N₀ + V₀) (Finset.Subset.refl _)
      (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) hwt
    have hm_abs : (Ideal.absNorm (Ideal.span {j_el * primaryIdealGenerator t_id}) : ℝ) ≤ U ^ (3 : ℝ) := by
      rw [← ringComplex_norm_sq_eq_absNorm_span, hm_norm_eq]
      exact Real.rpow_le_rpow_of_exponent_le hU1.le hQ3
    have hrad_abs : (Ideal.absNorm (Ideal.span {j_el * primaryIdealGenerator t_id} : Ideal O).radical : ℝ) ≤
        U ^ (fullPunctureWidth U t_id j_el) :=
      (radical_absNorm_le_self hm_ne).trans_eq
        ((ringComplex_norm_sq_eq_absNorm_span _).symm.trans hm_norm_eq)
    have hcore_b := hcore U ((le_max_left _ _).trans hU) Dpool hDp_core
      hd_lo hd_hi harith.1 hrp_le harith.2.1 (by rw [ht_eq]; exact harith.2.2.1)
      (le_max_left _ _) hV0 hM0 harith.2.2.2.1 harith.2.2.2.2.1
      (by rw [ht_eq]; exact harith.2.2.2.2.2.2.2.1)
      S₀ harith.2.2.2.2.2.2.2.2.1 (by rw [ht_eq]; exact harith.2.2.2.2.2.2.2.2.2.1)
      (by rw [ht_eq]; exact hc1_s1) (by rw [ht_eq]; exact hc2_s1)
      (fun j hj => hlarge_Z j (hS₀_sub_sel hj))
      lists_full (fun j hj => hlists_full j (hS₀_sub_sel hj))
      (fun i hi j hj hij => hdisj_sel (hS₀_sub_sel hi) (hS₀_sub_sel hj) hij)
      ζ_base hζ_re hζ_im a (fun j hj => ha_eq j (hS₀_sub_sel hj))
      (CanonicalRowCompletion.idealRange (U ^ V₀))
      (fun f hf => ⟨admissible_supported (hlabels_adm f hf).1, (hlabels_adm f hf).1.2.1, (hlabels_adm f hf).2⟩)
      Ψ (j_el * primaryIdealGenerator t_id) hΨ_base hΨ1 hm_ne hm_abs hrad_abs s
    rw [ht_eq] at hcore_b
    have hchild_bridge :
        normalizedColumnEnergy p hg Finset.univ Ψ (j_el * primaryIdealGenerator t_id)
          subslots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val)
          (CanonicalRowCompletion.idealRange (U ^ V₀)) (nonzeroChildFrequencyBall 1 (U ^ M₀))
          (secondLabelWeight D.N) (childLogTest fresh s) (U ^ N₀) U (N₀ + V₀) ≤
        C_core * U ^ (N₀ + V₀ + 13 * D.t) * (1 + ‖s‖) ^ (2 * deg_core) := by
      rw [himg.1, InverseInitialOriginalHeight.child_eq_normTwisted]
      exact hcore_b
    have hshift : (N₀ + V₀) - F_norm = 2 * η₀ := by dsimp only [N₀, V₀, F_norm]; ring
    rw [hshift]
    have hexp_eq : U ^ (2 * η₀) * (C_core * U ^ (N₀ + V₀ + 13 * D.t) * (1 + ‖s‖) ^ (2 * deg_core)) =
        (C_core * U ^ (F_norm + (4 * η₀ + 13 * D.t))) * (1 + ‖s‖) ^ (2 * deg_core) := by
      have hrp : U ^ (2 * η₀) * U ^ (N₀ + V₀ + 13 * D.t) = U ^ (F_norm + (4 * η₀ + 13 * D.t)) := by
        rw [← Real.rpow_add hU_pos]
        exact congrArg (fun x : ℝ => U ^ x) (by dsimp only [N₀, V₀, F_norm]; ring)
      calc _ = C_core * (U ^ (2 * η₀) * U ^ (N₀ + V₀ + 13 * D.t)) * (1 + ‖s‖) ^ (2 * deg_core) := by ring
        _ = _ := by rw [hrp]
    refine (mul_le_mul_of_nonneg_left (hle_wt.trans hchild_bridge) (Real.rpow_nonneg hU_pos.le _)).trans ?_
    rw [hexp_eq]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by dsimp only [C_ch]; linarith only [hC_0]) (Real.rpow_nonneg hU_pos.le _))
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg s))
        (Nat.mul_le_mul_left 2 (le_max_left _ _)))
      (pow_nonneg (add_nonneg zero_le_one (norm_nonneg s)) _)
      (mul_nonneg (add_pos hC_core hC_0).le (Real.rpow_nonneg hU_pos.le _))
  · have hcm_sub := harith.2.2.2.2.2.2.2.2.2.2.2 hrp_gt
    have hDp_0 : B_0 * U ^ ((8 : ℝ) + 1) ≤ (Dpool : ℝ) := by
      have hpow : U ^ ((8 : ℝ) + 1) ≤ U ^ (10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hU1.le (by norm_num)
      exact (mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg hU_pos.le _)
        (zero_le_one.trans (hBcore1.trans (le_max_left _ _)))).trans hDpool
    have hsub_card : subslots.card ≤ D.N :=
      (Finset.card_le_card Finset.sdiff_subset).trans hslots_card
    have hdisj_sub : (subslots : Set ↥selected).PairwiseDisjoint (fun x : ↥selected => lists_full x.val) :=
      fun x _ y _ hxy => hdisj_sel x.property y.property (fun hv => hxy (Subtype.ext hv))
    have hH_prod_sub : (∏ x ∈ subslots, 2 * Z_slot x.val) ≤
        U ^ ((∑ j ∈ S₀, D.ell j / d_outer) + η₀) := by
      rw [himg.2]; dsimp only [Z_slot]
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hU_pos,
        add_comm _ η₀, Real.rpow_add hU_pos]
      exact mul_le_mul_of_nonneg_right
        ((pow_le_pow_right₀ one_le_two hsub_card).trans h2N_η₀)
        (Real.rpow_nonneg hU_pos.le _)
    have hlists_sub : ∀ x ∈ subslots, 1 ≤ 2 * Z_slot x.val ∧
        (∀ P ∈ lists_full x.val, (P.val.absNorm : ℝ) ≤ 2 * Z_slot x.val) ∧
        (∀ P ∈ lists_full x.val, ‖a x.val P‖ ≤ 1) := by
      intro x _
      have h1 := Real.one_le_rpow hU1.le (div_nonneg (D.slots_bounds x.val).1.le hd_pos.le)
      refine ⟨by linarith only [h1], fun P hP => ?_, fun P hP => ?_⟩
      · have hPL : P.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
          rw [hlists_full x.val x.property] at hP; exact (Finset.mem_filter.mp hP).2
        exact (livePrime_data F_dual.modulus ⊤ F_dual.W 1 2 (Z_slot x.val)
          (Real.rpow_pos_of_pos hU_pos _) F_dual.complex_support P.val hPL).2.2.2
      · have hPL : P.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
          rw [hlists_full x.val x.property] at hP; exact (Finset.mem_filter.mp hP).2
        have hd_l := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot x.val)
          (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
          (hlarge_Z x.val x.property) P.val hPL
        rw [ha_eq x.val x.property P hP, norm_div, norm_star, ← norm_star (primeProfile _ _ _ _), ← norm_div]
        exact hd_l.2.2.2.2
    have hmom0 := hm0 U (((le_max_left _ _).trans (le_max_right _ _)).trans hU) Dpool hDp_0
      subslots hsub_card (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => 2 * Z_slot x.val)
      (fun x : ↥selected => a x.val) hdisj_sub
      (fun x hx => (hlists_sub x hx).1)
      (fun x hx => (hlists_sub x hx).2.1)
      (fun x hx => (hlists_sub x hx).2.2)
      ((∑ j ∈ S₀, D.ell j / d_outer) + η₀)
      (add_nonneg (Finset.sum_nonneg (fun j _ => div_nonneg (D.slots_bounds j).1.le hd_pos.le)) hη₀_pos.le)
      hH_prod_sub base hbase1 hbase_per
    have hrk := initial_child_from_rank p hg Finset.univ base Ψ subslots subslots
      (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val) fresh
      U 8 8 ((∑ j ∈ S₀, D.ell j / d_outer) + η₀) (D.t / 4) D.t C_0
      N₀ (θ + v) M₀ (fullPunctureWidth U t_id j_el) η₀ D.N deg_0
      (j_el * primaryIdealGenerator t_id) hU1 hΨ_base hm_ne
      (le_max_left _ _) hV0 hM0 hQ0
      harith.2.2.2.2.2.1 harith.2.2.2.2.2.2.1
      hcm_sub hm_norm_eq (Finset.Subset.refl _)
      (CanonicalRowCompletion.idealRange (U ^ V₀)) hlabels_adm (nonzeroChildFrequencyBall 1 (U ^ M₀))
      (Finset.Subset.refl _)
      (fun f => ((idealDivisors f).card : ℝ) ^ (J_drop.card + J_other.card + 1))
      (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) hwt s hmom0
    refine hrk.trans ?_
    have hexp_le : U ^ (F_norm + D.t + 4 * η₀) ≤ U ^ (F_norm + (4 * η₀ + 13 * D.t)) :=
      Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [ht_pos])
    exact mul_le_mul
      (mul_le_mul (by dsimp only [C_ch]; linarith only [hC_core]) hexp_le
        (Real.rpow_nonneg hU_pos.le _) (add_pos hC_core hC_0).le)
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg s))
        (Nat.mul_le_mul_left 2 (le_max_right _ _)))
      (pow_nonneg (add_nonneg zero_le_one (norm_nonneg s)) _)
      (mul_nonneg (add_pos hC_core hC_0).le (Real.rpow_nonneg hU_pos.le _))

/-! ### Part III: Initial window, dyadic sum, finite physical, and row-sum propagation -/

/-- Stage-1 counterpart of `InverseInitialRetainedPhysical.retained_physical_bound` at
`m = 1 + D.t / 2`, `η₀ = D.t / 10000`, `π = D.t / 100`, `cap = 9`. -/
private theorem retained_physical_bound_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (W₁ W₂ : ℝ → ℂ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀) (hs₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (Vlog : Fin 6 → ℝ → ℂ) (Mlog : Fin 6 → ℝ)
    (hVlog : ∀ i, ContDiff ℝ ∞ (Vlog i)) (hSlog : ∀ i, HasCompactSupport (Vlog i))
    (hMlog : ∀ i, 0 ≤ Mlog i) (hbox : ∀ i y, Vlog i y ≠ 0 → |y| ≤ Mlog i)
    (ω₁ ω₂ : ℝ → ℂ) {lo b : ℝ} (hlo : 0 < lo) (hb : 1 ≤ b)
    (hω₁ : Function.support ω₁ ⊆ Set.Icc lo b) (hω₂ : Function.support ω₂ ⊆ Set.Icc lo b)
    (hd₁ : ContDiff ℝ ∞ ω₁) (hd₂ : ContDiff ℝ ∞ ω₂) :
    let η₀ : ℝ := D.t / 10000
    let m_row : ℝ := 1 + D.t / 2
    let π_loss : ℝ := D.t / 100
    ∃ (τ_dual B_tree : ℝ) (deg : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_tree ∧
      ∀ data : RowData, ∃ C_p U_p : ℝ, 0 < C_p ∧ 2 ≤ U_p ∧
      ∀ U : ℝ, U_p ≤ U →
      ∀ Dpool : ℕ, B_tree * U ^ (10 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
        fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
      let p := poolPrimary F_pool
      let hg := poolPrimary_good F_pool hFa
      let base := elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_orig_in rr D_val B v θ H R : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
        R ≤ 12 → R = B - θ + 2 * η₀ →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      ∀ (assigned : Finset ↥selected),
      let z_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      D_val = rr + assignedCenter Finset.univ z_sel - 2 * assignedCenter assigned z_sel →
      max 0 (columnCenter D_val B v) - columnCenter D_val B v ≤ 3 * η₀ →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ selected, lists_full j = poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (selected : Set (Fin D.N)).PairwiseDisjoint lists_full →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ selected, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      ∀ (S : Finset (Source (ι := primePool F_pool) 0)),
        (∀ x ∈ S, x.divisor ⊆ x.common) → (∀ x ∈ S, x.frequency ≠ 0) →
      ∀ (j_el : O) (c₁ c₂ θ₁ θ₂ : ℝ), 0 < c₁ → 0 < c₂ →
        BlockSupport p (pointSource Finset.univ S) W₁ W₂ ω₁ ω₂ Vlog U D_val B v θ H c₁ c₂ θ₁ θ₂ →
        (∀ t ∈ quotientSet p S, (t.absNorm : ℝ) ≤ U ^ R) →
      ∀ (w : Source (ι := primePool F_pool) 0 → ℂ), (∀ x ∈ S, ‖w x‖ ≤ 1) →
        (∀ x ∈ S,
          (initialChild (toTuple p (sectorSource
            (unitSector p (poolPrimary_ne_zero F_pool hFa)
              (InverseInitialRayAttachment.poolPrimary_primary F_pool hFa) (sourcePoint x ∅ ∅)) x))).2.1 ∈
              CanonicalRowCompletion.idealRange (U ^ (θ + v + 2 * η₀)) ∧
          (initialChild (toTuple p (sectorSource
            (unitSector p (poolPrimary_ne_zero F_pool hFa)
              (InverseInitialRayAttachment.poolPrimary_primary F_pool hFa) (sourcePoint x ∅ ∅)) x))).2.2 ∈
              nonzeroChildFrequencyBall 1 (U ^ (θ + H + 2 * η₀))) →
        (∀ t ∈ quotientSet p S,
          -2 * η₀ ≤ B - θ ∧
          j_el * primaryIdealGenerator t ≠ 0 ∧
          0 ≤ θ + v + 2 * η₀ ∧ 0 ≤ θ + H + 2 * η₀ ∧
          0 ≤ fullPunctureWidth U t j_el ∧
          ‖ringComplex (j_el * primaryIdealGenerator t)‖ ^ 2 = U ^ (fullPunctureWidth U t j_el) ∧
          fullPunctureWidth U t j_el ≤ (B - θ) + assignedCenter assigned z_sel + 3 * η₀ ∧
          θ + H + 2 * η₀ ≤ initialM m_row rr (assignedCenter Finset.univ z_sel)
            (assignedCenter assigned z_sel) (B - θ) η₀ η₀) →
        ‖physicalBlock p hg (pointSource Finset.univ S) (w ∘ erasePoint) base j_el
          (primeMark (Finset.univ \ assigned) (fun x : ↥selected => lists_full x.val)
            (fun x : ↥selected => a x.val))
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ U D_val m_row‖ ≤
          C_p * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) *
            ((1 + ‖θ₁‖) ^ InverseClippingProfiles.momentOrder (4 * deg) *
              (1 + ‖θ₂‖) ^ InverseClippingProfiles.momentOrder (4 * deg)) := by
  intro η₀ m_row π_loss
  have ht_pos : 0 < D.t := D.t_pos
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; positivity
  obtain ⟨fresh₁, fresh₂, ⟨af₁, bf₁, haf₁, hab₁, _, hs₁f⟩, ⟨af₂, bf₂, haf₂, hab₂, _, hs₂f⟩, hphysical⟩ :=
    InverseInitialEnergyCallerReference.actual_physical_reference_bound
      W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ Vlog Mlog hVlog hSlog hMlog hbox
      ω₁ ω₂ lo b hlo hb hω₁ hω₂ hd₁ hd₂
  obtain ⟨τ_d1, B_1, deg_1, hτ_p1, hτ_le1, hB1_1, hm₁_all⟩ :=
    stage1_single_child_energy hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      fresh₁ haf₁ hab₁ (subset_closure.trans hs₁f)
  obtain ⟨τ_d2, B_2, deg_2, hτ_p2, _hτ_le2, hB2_1, hm₂_all⟩ :=
    stage1_single_child_energy hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      fresh₂ haf₂ hab₂ (subset_closure.trans hs₂f)
  let τ_dual : ℝ := min τ_d1 τ_d2
  let B_tree : ℝ := B_1 + B_2
  let deg : ℕ := deg_1 + deg_2
  obtain ⟨Cp, hCp, hphys⟩ := hphysical deg D.N 12 π_loss (by norm_num) (by dsimp only [π_loss]; positivity)
  refine ⟨τ_dual, B_tree, deg, lt_min hτ_p1 hτ_p2,
    (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_two).trans hτ_le1,
    by dsimp only [B_tree]; linarith only [hB1_1, hB2_1], ?_⟩
  intro data
  obtain ⟨_, _, hbase1, _⟩ := raw_conjugate_base_gates data
  obtain ⟨C₁, U₁, hC₁, hU₁_2, hm₁⟩ := hm₁_all data
  obtain ⟨C₂, U₂, hC₂, _hU₂_2, hm₂⟩ := hm₂_all data
  refine ⟨Cp * (C₁ + C₂), max U₁ U₂, mul_pos hCp (add_pos hC₁ hC₂), hU₁_2.trans (le_max_left _ _), ?_⟩
  intro U hU Dpool hDpool q_per F_pool hFa p hg base
    d_outer r_orig_in rr D_val B v θ H R
    hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi hR_12 hReq selected hz_sel_hi assigned
    z_sel Z_slot Z_dual hD_eq hclip hlarge_Z lists_full hlists_full hdisj_sel
    ζ_base hζ_re hζ_im a ha_eq S hdiv hf j_el c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw hchild hstate
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU1 : 1 < U := by have h2 := (hU₁_2.trans (le_max_left _ _)).trans hU; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hZd_ge1 : 1 ≤ Z_dual :=
    Real.one_le_rpow hU1.le (div_nonneg (by norm_num) (by linarith only [hd_lo]))
  have hD₁ : B_1 * U ^ (10 : ℝ) ≤ (Dpool : ℝ) :=
    (mul_le_mul_of_nonneg_right (by dsimp only [B_tree]; linarith only [hB2_1])
      (Real.rpow_nonneg hU_pos.le _)).trans hDpool
  have hD₂ : B_2 * U ^ (10 : ℝ) ≤ (Dpool : ℝ) :=
    (mul_le_mul_of_nonneg_right (by dsimp only [B_tree]; linarith only [hB1_1])
      (Real.rpow_nonneg hU_pos.le _)).trans hDpool
  let slots : Finset ↥selected := Finset.univ \ assigned
  have hslots_card : slots.card ≤ D.N :=
    ((Finset.card_le_univ slots).trans_eq (Fintype.card_coe selected)).trans
      ((Finset.card_le_univ selected).trans_eq (Fintype.card_fin D.N))
  have ha_norm : ∀ x ∈ slots, ∀ q ∈ lists_full x.val, ‖a x.val q‖ ≤ 1 := by
    intro x _ q hq
    have hqL : q.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
      rw [hlists_full x.val x.property] at hq; exact (Finset.mem_filter.mp hq).2
    have hd_l := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot x.val)
      (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
      (hlarge_Z x.val x.property) q.val hqL
    rw [ha_eq x.val x.property q hq, norm_div, norm_star, ← norm_star (primeProfile _ _ _ _), ← norm_div]
    exact hd_l.2.2.2.2
  have hbound := hphys p (poolPrimary_ne_zero F_pool hFa) (poolPrimary_coprime F_pool hFa) hg
    (InverseInitialRayAttachment.poolPrimary_injective F_pool hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F_pool hFa) (poolPrimary_odd F_pool hFa)
    S hdiv hf Finset.univ base hbase1 j_el slots hslots_card
    (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val) ha_norm
    U D_val B v θ H R m_row η₀ hU1 hR_12 (mul_nonneg hη₀_pos.le (Real.log_pos hU1).le)
    c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw
    (CanonicalRowCompletion.idealRange (U ^ (θ + v + 2 * η₀))) (nonzeroChildFrequencyBall 1 (U ^ (θ + H + 2 * η₀)))
    (fun f hf => ((admissible_iff_native f).mpr (CanonicalRowCompletion.mem_idealRange.mp hf).1).1)
    (fun k hk => (child_ball_neg _ k).mpr hk) hchild
    (max 0 (columnCenter D_val B v) + (θ + v)) (C₁ + C₂) (4 * η₀ + 13 * D.t)
    (add_pos hC₁ hC₂).le hclip (by unfold columnCenter; ring) hReq
    (fun s ρ J₁ hJ₁ J₂ hJ₂ t ht => by
      obtain ⟨hP_lo, hm_ne, hV0, hM0, hQ0, hm_norm, hQ_hi, hM_init⟩ := hstate t ht
      have hJ₁_sub : J₁ ⊆ slots := Finset.mem_powerset.mp hJ₁
      have hJ₂_sub : J₂ ⊆ slots := Finset.mem_powerset.mp hJ₂
      have hclip' : max 0 (D_val - B - v) - (D_val - B - v) ≤ 3 * η₀ := by
        simpa only [columnCenter] using hclip
      have hζ1 : |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d1 :=
        hζ_im.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_left _ _)) (by norm_num))
      have hζ2 : |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d2 :=
        hζ_im.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_right _ _)) (by norm_num))
      have hleft := hm₁ U ((le_max_left _ _).trans hU) Dpool hD₁
        hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi selected hz_sel_hi assigned J₁ J₂ hJ₁_sub hJ₂_sub
        hD_eq hP_lo hclip' hV0 hM0 hM_init hlarge_Z lists_full hlists_full hdisj_sel
        ζ_base hζ_re hζ1 a ha_eq (secondRayMinus base ρ) j_el t
        ((show CanonicalCoefficientClass.IsBaseRayTwist base base from Or.inl rfl).secondMinus ρ)
        (fun u => (secondRayMinus_norm_le base ρ u).trans (hbase1 u))
        hm_ne hQ0 hm_norm hQ_hi s
      have hright0 := hm₂ U ((le_max_right _ _).trans hU) Dpool hD₂
        hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi selected hz_sel_hi assigned J₂ J₁ hJ₂_sub hJ₁_sub
        hD_eq hP_lo hclip' hV0 hM0 hM_init hlarge_Z lists_full hlists_full hdisj_sel
        ζ_base hζ_re hζ2 a ha_eq (secondRayPlus base ρ) j_el t
        ((show CanonicalCoefficientClass.IsBaseRayTwist base base from Or.inl rfl).secondPlus ρ)
        (fun u => (secondRayPlus_norm_le base ρ u).trans (hbase1 u))
        hm_ne hQ0 hm_norm hQ_hi s
      have hwt_comm : (fun f : Ideal O => ((idealDivisors f).card : ℝ) ^ (J₂.card + J₁.card + 1)) =
          (fun f : Ideal O => ((idealDivisors f).card : ℝ) ^ (J₁.card + J₂.card + 1)) := by
        funext f; rw [Nat.add_comm J₂.card J₁.card]
      rw [hwt_comm] at hright0
      refine ⟨hleft.trans ?_, hright0.trans ?_⟩
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by linarith only [hC₂]) (Real.rpow_nonneg hU_pos.le _))
          (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg s))
            (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)))
          (pow_nonneg (add_nonneg zero_le_one (norm_nonneg s)) _)
          (mul_nonneg (add_pos hC₁ hC₂).le (Real.rpow_nonneg hU_pos.le _))
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by linarith only [hC₁]) (Real.rpow_nonneg hU_pos.le _))
          (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg s))
            (Nat.mul_le_mul_left 2 (Nat.le_add_left _ _)))
          (pow_nonneg (add_nonneg zero_le_one (norm_nonneg s)) _)
          (mul_nonneg (add_pos hC₁ hC₂).le (Real.rpow_nonneg hU_pos.le _)))
  refine hbound.trans_eq ?_
  rw [show m_row + 11 * η₀ + π_loss + (4 * η₀ + 13 * D.t) =
      m_row + 15 * η₀ + π_loss + 13 * D.t by ring]
  ring

/-- Stage-1 counterpart of `InverseInitialRetainedWindow.retained_window_bound` at `cutoff`
(`lo = 1 / 4`, `hi = 1`), `m = 1 + D.t / 2`, `η₀ = τ₀ = D.t / 10000`, `π = D.t / 100`. -/
private theorem retained_window_bound_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (W₁ W₂ : ℝ → ℂ) {a₀ b₀ bcap : ℝ} (ha₀ : 0 < a₀) (hbcap : 1 ≤ bcap)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀) (hs₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) (Φ : 𝓢(ℝ, ℂ)) :
    let η₀ : ℝ := D.t / 10000
    let m_row : ℝ := 1 + D.t / 2
    let π_loss : ℝ := D.t / 100
    ∃ (τ_dual B_tree Tclip : ℝ) (deg : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_tree ∧ 0 ≤ Tclip ∧
      ∀ data : RowData, ∃ C_w U_w : ℝ, 0 < C_w ∧ 2 ≤ U_w ∧
      ∀ U : ℝ, U_w ≤ U →
      (4 : ℝ) ≤ U ^ η₀ → Tclip ≤ 3 * η₀ * Real.log U →
      ∀ Dpool : ℕ, B_tree * U ^ (10 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
        fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
      let p := poolPrimary F_pool
      let hg := poolPrimary_good F_pool hFa
      let base := elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_orig_in rr D_val B v θ H : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
        B - θ + 2 * η₀ ≤ 12 →
        radialCenter m_row H θ D_val B ≤ 4 * η₀ + η₀ →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      ∀ (assigned : Finset ↥selected),
      let z_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      D_val = rr + assignedCenter Finset.univ z_sel - 2 * assignedCenter assigned z_sel →
      ∀ (qelem : ↥selected → O) (primeW : ↥selected → ℝ → ℂ),
        (∀ i ∈ assigned, qelem i ≠ 0) →
        (∀ i ∈ assigned, Function.support (primeW i) ⊆ Set.Icc 1 2) →
        (∀ i ∈ assigned, primeW i ((Ideal.absNorm (Ideal.span {qelem i}) : ℝ) / U ^ (z_sel i)) ≠ 0) →
        ((2 : ℝ) ^ assigned.card ≤ U ^ η₀) →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ selected, lists_full j = poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (selected : Set (Fin D.N)).PairwiseDisjoint lists_full →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ selected, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      ∀ (S : Finset (Source (ι := primePool F_pool) 0)),
        (∀ x ∈ S, x.divisor ⊆ x.common) → (∀ x ∈ S, x.frequency ≠ 0) →
      ∀ (c₁ c₂ θ₁ θ₂ : ℝ), 1 ≤ c₁ → c₁ ≤ bcap → 1 ≤ c₂ → c₂ ≤ bcap →
      ∀ (w : Source (ι := primePool F_pool) 0 → ℂ), (∀ x ∈ S, ‖w x‖ ≤ 1) →
        ‖physicalBlock p hg
          (pointSource Finset.univ (windowSource p S InverseInitialDyadicAssembly.cutoff U D_val B v θ H))
          (w ∘ erasePoint) base (assignedElement assigned qelem)
          (primeMark (Finset.univ \ assigned) (fun x : ↥selected => lists_full x.val)
            (fun x : ↥selected => a x.val))
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ U D_val m_row‖ ≤
          C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) *
            ((1 + ‖θ₁‖) ^ InverseClippingProfiles.momentOrder (4 * deg) *
              (1 + ‖θ₂‖) ^ InverseClippingProfiles.momentOrder (4 * deg)) := by
  intro η₀ m_row π_loss
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; have := D.t_pos; positivity
  obtain ⟨fresh, Vlog, Mlog, af, bf, haf, _hab, _hfc, hfs, hM, hVc, hVs, hwindow⟩ :=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂
      (fun _ : Fin 4 => (1 / 4 : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (fun _ => by norm_num) (fun _ => by norm_num)
  have hfs' : Function.support (fresh : ℝ → ℂ) ⊆ Set.Icc af (max 1 bf) :=
    fun x hx => ⟨(hfs (subset_closure hx)).1, (hfs (subset_closure hx)).2.trans (le_max_right _ _)⟩
  obtain ⟨τ_dual, B_tree, deg, hτ_pos, hτ_le, hBtree1, hbound_all⟩ :=
    retained_physical_bound_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      W₁ W₂ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i => Vlog i) Mlog
      (fun i => (Vlog i).smooth ⊤) hVc hM (fun i y hy => abs_le.mpr (hVs i hy))
      fresh fresh haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
  refine ⟨τ_dual, B_tree, Real.log (max 1 bf), deg, hτ_pos, hτ_le, hBtree1,
    Real.log_nonneg (le_max_left _ _), ?_⟩
  intro data
  obtain ⟨C_p, U_p, hC_p, hUp2, hbound⟩ := hbound_all data
  refine ⟨C_p, U_p, hC_p, hUp2, ?_⟩
  intro U hU hpow4 hlog Dpool hDpool q_per F_pool hFa p hg base
    d_outer r_orig_in rr D_val B v θ H
    hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi hR_12 hrad selected hz_sel_hi assigned
    z_sel Z_slot Z_dual hD_eq qelem primeW hqe hprimeW hprimeLive hprodj
    hlarge_Z lists_full hlists_full hdisj_sel ζ_base hζ_re hζ_im a ha_eq
    S hdiv hf c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hp := poolPrimary_ne_zero F_pool hFa
  have hcop := poolPrimary_coprime F_pool hFa
  have hprimary := InverseInitialRayAttachment.poolPrimary_primary F_pool hFa
  have hU1 : 1 < U := by have h2 := hUp2.trans hU; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hψ : ∀ i : Fin 4, Function.support (InverseInitialDyadicAssembly.cutoff i) ⊆ Set.Icc (1 / 4 : ℝ) 1 :=
    fun i x hx => Set.Ioo_subset_Icc_self (cutoff_support i hx)
  have h1_η₀ : (1 : ℝ) ≤ U ^ η₀ := Real.one_le_rpow hU1.le hη₀_pos.le
  have hlo_η₀ : U ^ (-η₀) ≤ (1 / 4 : ℝ) := by
    rw [Real.rpow_neg hU_pos.le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hpow4
  let Sw := windowSource p S InverseInitialDyadicAssembly.cutoff U D_val B v θ H
  let Sc := coprimeSource p Sw
  have hdivw : ∀ x ∈ Sw, x.divisor ⊆ x.common := fun x hx => hdiv x (Finset.mem_filter.mp hx).1
  have hfw : ∀ x ∈ Sw, x.frequency ≠ 0 := fun x hx => hf x (Finset.mem_filter.mp hx).1
  have hdivc : ∀ x ∈ Sc, x.divisor ⊆ x.common := fun x hx => hdivw x (Finset.mem_filter.mp hx).1
  have hfc' : ∀ x ∈ Sc, x.frequency ≠ 0 := fun x hx => hfw x (Finset.mem_filter.mp hx).1
  have hswhole := hwindow p hp Finset.univ S hdiv hf InverseInitialDyadicAssembly.cutoff hψ U D_val B v θ H c₁ c₂ θ₁ θ₂
    hU_pos hc₁ hbc₁ hc₂ hbc₂
  have hpoint : pointSource Finset.univ Sc ⊆ pointSource Finset.univ Sw := fun x hx => by
    obtain ⟨y, hy, hm⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y, (Finset.mem_filter.mp hy).1, hm⟩
  have hsupport : BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i => Vlog i) U D_val B v θ H c₁ c₂ θ₁ θ₂ :=
    ⟨fun x hx => hswhole.1 x (hpoint hx), fun x hx => hswhole.2.1 x (hpoint hx),
      fun x hx => hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty : physicalBlock p hg (pointSource Finset.univ Sc) (w ∘ erasePoint) base
      (assignedElement assigned qelem)
      (primeMark (Finset.univ \ assigned) (fun x : ↥selected => lists_full x.val)
        (fun x : ↥selected => a x.val))
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ U D_val m_row = 0
  · rw [hempty, norm_zero]; positivity
  have hclip := (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w ∘ erasePoint) base (assignedElement assigned qelem)
    (primeMark (Finset.univ \ assigned) (fun x : ↥selected => lists_full x.val)
      (fun x : ↥selected => a x.val)) W₁ W₂ fresh fresh (fun i => Vlog i) Φ
    U D_val B v θ H m_row c₁ c₂ θ₁ θ₂ af (max 1 bf) η₀ hU1 (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt : quotientSet p Sc ⊆ quotientSet p Sw :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hret_bound : ∀ t ∈ quotientSet p (retained p S (fun _ => 1)
      (InverseInitialDyadicAssembly.cutoff 0) (InverseInitialDyadicAssembly.cutoff 1) U B θ),
      (t.absNorm : ℝ) ≤ U ^ (B - θ + 2 * η₀) :=
    fun t ht => retained_quotient_bound p hp S (fun _ => 1)
      (InverseInitialDyadicAssembly.cutoff 0) (InverseInitialDyadicAssembly.cutoff 1)
      (1 / 4) 1 (1 / 4) 1 U B θ η₀ hU_pos (hψ 0) (hψ 1) h1_η₀ hlo_η₀ hdiv t ht
  have hn : ∀ t ∈ quotientSet p Sc, (t.absNorm : ℝ) ≤ U ^ (B - θ + 2 * η₀) :=
    fun t ht => hret_bound t
      (window_quotient_subset_retained p S InverseInitialDyadicAssembly.cutoff U D_val B v θ H (hqt ht))
  have hje : assignedElement assigned qelem ≠ 0 := Finset.prod_ne_zero_iff.mpr hqe
  have hprod_b : (∏ _i ∈ assigned, (2 : ℝ)) ≤ U ^ η₀ := by
    simpa only [Finset.prod_const] using hprodj
  have hnj := assigned_norm_power assigned qelem z_sel (fun _ => 1) (fun _ => 2) primeW U η₀
    hU_pos hprimeW hprimeLive hprod_b
  have hM_init : θ + H + 2 * η₀ ≤ initialM m_row rr (assignedCenter Finset.univ z_sel)
      (assignedCenter assigned z_sel) (B - θ) η₀ η₀ :=
    physical_row_width_le m_row rr (assignedCenter Finset.univ z_sel)
      (assignedCenter assigned z_sel) B θ H η₀ η₀ (hD_eq ▸ hrad)
  have hstate : ∀ t ∈ quotientSet p Sc,
      -2 * η₀ ≤ B - θ ∧
      assignedElement assigned qelem * primaryIdealGenerator t ≠ 0 ∧
      0 ≤ θ + v + 2 * η₀ ∧ 0 ≤ θ + H + 2 * η₀ ∧
      0 ≤ fullPunctureWidth U t (assignedElement assigned qelem) ∧
      ‖ringComplex (assignedElement assigned qelem * primaryIdealGenerator t)‖ ^ 2 =
        U ^ (fullPunctureWidth U t (assignedElement assigned qelem)) ∧
      fullPunctureWidth U t (assignedElement assigned qelem) ≤
        (B - θ) + assignedCenter assigned z_sel + 3 * η₀ ∧
      θ + H + 2 * η₀ ≤ initialM m_row rr (assignedCenter Finset.univ z_sel)
        (assignedCenter assigned z_sel) (B - θ) η₀ η₀ := by
    intro t ht
    have ht_w := hqt ht
    have hret_t := window_quotient_subset_retained p S InverseInitialDyadicAssembly.cutoff U D_val B v θ H ht_w
    have hP_lo : -2 * η₀ ≤ B - θ := by
      have hn_r := (nonempty_radius p hp (retained p S (fun _ => 1)
        (InverseInitialDyadicAssembly.cutoff 0) (InverseInitialDyadicAssembly.cutoff 1) U B θ)
        U (B - θ) η₀ hU1 ⟨t, hret_t⟩ hret_bound).2
      linarith only [hn_r]
    obtain ⟨hm, hQ0, hnorm, hQ⟩ := retained_full_puncture p hp hprimary S InverseInitialDyadicAssembly.cutoff D_val v H
      (1 / 4) 1 (1 / 4) 1 U B θ η₀ (assignedCenter assigned z_sel) hU1
      (hψ 0) (hψ 1) h1_η₀ hlo_η₀ hdiv (assignedElement assigned qelem) hje hnj ht_w
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp ht_w
    obtain ⟨hV0, hM0⟩ := live_widths_nonnegative p hp hprimary S InverseInitialDyadicAssembly.cutoff
      (fun _ => 1 / 4) (fun _ => 1) hψ U D_val B v θ H η₀ hU1 (fun _ => h1_η₀)
      hx (hf x (Finset.mem_filter.mp hx).1)
    exact ⟨hP_lo, hm, hV0, hM0, hQ0, hnorm, hQ, hM_init⟩
  exact hbound U hU Dpool hDpool hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi hR_12 rfl
    selected hz_sel_hi assigned hD_eq hclip hlarge_Z lists_full hlists_full hdisj_sel
    ζ_base hζ_re hζ_im a ha_eq Sc hdivc hfc' (assignedElement assigned qelem)
    c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx => hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (fun x hx => InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg
      (poolPrimary_odd F_pool hFa) hprimary S hdiv hf InverseInitialDyadicAssembly.cutoff (fun _ => 1 / 4) (fun _ => 1)
      hψ U D_val B v θ H η₀ hU_pos (fun _ => h1_η₀) x hx _)
    hstate

/-- Stage-1 dyadic sum, high-mass tail, zero-mode, and finite-row assembly (`m = 1 + D.t / 2`,
`cap = 9`), bounding `∑ u ∈ rows, ‖U^(-D/2) * inputConjugateRow ... u‖^2` by
`C * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ degree) ^ 2`. -/
private theorem original_input_rows_bound_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (W : ℝ → ℂ) {a₀ b₀ bcap B₀ : ℝ} (ha₀ : 0 < a₀) (hbcap : 1 ≤ bcap)
    (hs : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (hB₀ : 0 ≤ B₀) (hb : ∀ x, ‖W x‖ ≤ B₀)
    (Φ : 𝓢(ℝ, ℂ)) (hΦ : ∀ x, 0 ≤ (Φ x).re) (hone : ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ x = 1) :
    let η₀ : ℝ := D.t / 10000
    let m_row : ℝ := 1 + D.t / 2
    ∃ (τ_dual B_tree : ℝ) (deg_in : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_tree ∧
      ∀ data : RowData, ∃ C_in U_in : ℝ, 0 < C_in ∧ 2 ≤ U_in ∧
      ∀ U : ℝ, U_in ≤ U →
      ∀ Dpool : ℕ, B_tree * U ^ (10 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
        fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
      let p := poolPrimary F_pool
      let hg := poolPrimary_good F_pool hFa
      let base := elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_orig_in rr D_val : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      ∀ (assigned : Finset ↥selected),
      let z_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      D_val = rr + assignedCenter Finset.univ z_sel - 2 * assignedCenter assigned z_sel →
      ∀ (qelem : ↥selected → O) (primeW : ↥selected → ℝ → ℂ),
        (∀ i ∈ assigned, qelem i ≠ 0) →
        (∀ i ∈ assigned, Function.support (primeW i) ⊆ Set.Icc 1 2) →
        (∀ i ∈ assigned, primeW i ((Ideal.absNorm (Ideal.span {qelem i}) : ℝ) / U ^ (z_sel i)) ≠ 0) →
        ((2 : ℝ) ^ assigned.card ≤ U ^ η₀) →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ selected, lists_full j = poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (selected : Set (Fin D.N)).PairwiseDisjoint lists_full →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ selected, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      ∀ (rows : Finset O), (∀ u ∈ rows, ‖ringComplex u‖ ^ 2 ≤ U ^ m_row) →
      ∀ (θ : ℝ),
        (∑ u ∈ rows, ‖((U ^ (-D_val / 2) : ℝ) : ℂ) *
          inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ base
            (assignedElement assigned qelem) 1 1
            (initialTest p (primeMark (Finset.univ \ assigned)
              (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
              (childLogTest W θ) U D_val) u‖ ^ 2) ≤
          C_in * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_in) ^ 2 := by
  intro η₀ m_row
  have ht_pos : 0 < D.t := D.t_pos
  have ht_sm : D.t ≤ 1 / 100000000 := D.t_small
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; positivity
  let π_loss : ℝ := D.t / 100
  let loss : ℝ := D.t / 100
  have hloss_pos : 0 < loss := by dsimp only [loss]; positivity
  have hsstar : Function.support (fun x => star (W x)) ⊆ Set.Icc a₀ b₀ :=
    fun x hx => hs (by simpa only [Function.mem_support, star_ne_zero] using hx)
  have hbStar : ∀ x, ‖star (W x)‖ ≤ B₀ := fun x => by simpa only [norm_star] using hb x
  obtain ⟨τ_dual, B_tree, Tclip, deg, hτ_pos, hτ_le, hBtree1, _hTclip, hwin_all⟩ :=
    retained_window_bound_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      (fun x => star (W x)) W ha₀ hbcap hsstar hs (Complex.conjCLE.contDiff.comp hW) hW Φ
  have hb_pos : 0 < max 1 b₀ := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨A_card, hA_card, hcount⟩ :=
    retained_card_subpower (max 1 b₀) 9 (4 * η₀ + η₀) loss hb_pos (by norm_num)
      (by positivity) hloss_pos
  obtain ⟨ss, Ct, _hCt, htail⟩ :=
    InverseInitialDyadicTailBound.actual_high_mass_tail (2 * (9 : ℝ) + 2) 1 η₀ hη₀_pos
  let tailC : ℝ := Ct * B₀ * B₀ * ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC : 0 ≤ tailC := by dsimp only [tailC]; positivity
  obtain ⟨Cz, hCz, hzero⟩ := InverseInitialZeroMode.physical_marked_zero_bound
    loss 9 (max 1 b₀) B₀ hloss_pos (by norm_num) hb_pos hB₀ Φ
  have hpowers : ∀ᶠ Z : ℝ in atTop, (4 : ℝ) ≤ Z ^ η₀ :=
    (tendsto_rpow_atTop hη₀_pos).eventually (eventually_ge_atTop 4)
  have hlogs : ∀ᶠ Z : ℝ in atTop, Tclip ≤ 3 * η₀ * Real.log Z := by
    filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (Tclip / (3 * η₀)))] with Z hZ
    exact ((div_le_iff₀ (by positivity : 0 < 3 * η₀)).mp hZ).trans_eq (mul_comm _ _)
  have hevent := window_exponent_eventual_upper (max 1 b₀) 1 hb_pos zero_lt_one
  have hev_64 : ∀ᶠ Z : ℝ in atTop, max 1 b₀ ≤ Z ∧ 64 * (max 1 b₀) ^ 2 ≤ Z ^ η₀ :=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη₀_pos).eventually (eventually_ge_atTop (64 * (max 1 b₀) ^ 2)))
  obtain ⟨Zaux, haux⟩ := eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and (hevent.and hev_64))))
  let deg_in : ℕ := InverseClippingProfiles.momentOrder (4 * deg)
  refine ⟨τ_dual, B_tree, deg_in, hτ_pos, hτ_le, hBtree1, ?_⟩
  intro data
  obtain ⟨_, _, hbase1, _⟩ := raw_conjugate_base_gates data
  obtain ⟨C_w, U_w, hC_w, hUw2, hwin⟩ := hwin_all data
  let C_in : ℝ := A_card * C_w + tailC + Cz
  refine ⟨C_in, max U_w Zaux, by dsimp only [C_in]; positivity, hUw2.trans (le_max_left _ _), ?_⟩
  intro U hU Dpool hDpool q_per F_pool hFa p hg base
    d_outer r_orig_in rr D_val hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi
    selected hz_sel_hi assigned z_sel Z_slot Z_dual hD_eq
    qelem primeW hqe hprimeW hprimeLive hprodj hlarge_Z lists_full hlists_full hdisj_sel
    ζ_base hζ_re hζ_im a ha_eq rows hrows θ
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hp := poolPrimary_ne_zero F_pool hFa
  have hcop := poolPrimary_coprime F_pool hFa
  have hinj := InverseInitialRayAttachment.poolPrimary_injective F_pool hFa
  have hodd := poolPrimary_odd F_pool hFa
  have hprim := InverseInitialRayAttachment.poolPrimary_primary F_pool hFa
  have hUw' : U_w ≤ U := (le_max_left _ _).trans hU
  obtain ⟨hcU, hpow4, hlog, hexp, hbU, h64⟩ := haux U ((le_max_right _ _).trans hU)
  have hU1 : 1 < U := by have h2 := hUw2.trans hUw'; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hz_pos : ∀ x : ↥selected, 0 ≤ z_sel x :=
    fun x => div_nonneg (D.slots_bounds x.val).1.le hd_pos.le
  have hz_all_hi : assignedCenter Finset.univ z_sel ≤ 1964 / 12500 := by
    have heq : assignedCenter Finset.univ z_sel = ∑ j ∈ selected, D.ell j / d_outer :=
      Finset.sum_coe_sort selected (fun j => D.ell j / d_outer)
    rw [heq]; unfold stage1Line at hz_sel_hi; linarith only [hz_sel_hi, hr0]
  have hG0 : 0 ≤ assignedCenter assigned z_sel := Finset.sum_nonneg (fun i _ => hz_pos i)
  have hG_le : assignedCenter assigned z_sel ≤ assignedCenter Finset.univ z_sel :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hz_pos i)
  have hD_hi : D_val ≤ 9 := by linarith only [hD_eq, hrr_hi, hr1, hz_all_hi, hG0]
  have hD_lo : -9 ≤ D_val := by
    dsimp only [η₀] at hrr_lo
    linarith only [hD_eq, hrr_lo, hr0, hz_all_hi, hG_le, ht_sm, ht_pos]
  have hm_pos : 0 ≤ m_row := by dsimp only [m_row]; positivity
  have hsize : max 1 b₀ * U ^ D_val ≤ U ^ (2 * (9 : ℝ) + 2) := by
    calc max 1 b₀ * U ^ D_val
        ≤ U * U ^ D_val := mul_le_mul_of_nonneg_right hbU (Real.rpow_nonneg hU_pos.le _)
      _ = U ^ (D_val + 1) := by rw [mul_comm, ← Real.rpow_add_one hU_pos.ne']
      _ ≤ U ^ (2 * (9 : ℝ) + 2) := Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [hD_hi])
  let slots : Finset ↥selected := Finset.univ \ assigned
  have hdis_slots : (slots : Set ↥selected).PairwiseDisjoint (fun x : ↥selected => lists_full x.val) :=
    fun x _ y _ hxy => hdisj_sel x.property y.property (fun hv => hxy (Subtype.ext hv))
  have ha_norm : ∀ x ∈ slots, ∀ q ∈ lists_full x.val, ‖a x.val q‖ ≤ 1 := by
    intro x _ q hq
    have hqL : q.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
      rw [hlists_full x.val x.property] at hq; exact (Finset.mem_filter.mp hq).2
    have hd_l := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot x.val)
      (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
      (hlarge_Z x.val x.property) q.val hqL
    rw [ha_eq x.val x.property q hq, norm_div, norm_star, ← norm_star (primeProfile _ _ _ _), ← norm_div]
    exact hd_l.2.2.2.2
  have hs_cl : Function.support (clippedSource W 1 θ) ⊆ Set.Iic (max 1 b₀) :=
    fun x hx => (clipped_support_upper W a₀ b₀ 1 θ ha₀ le_rfl hs hx).trans (le_max_right 1 b₀)
  have hs_cls : Function.support (clippedSource (fun x => star (W x)) 1 (-θ)) ⊆ Set.Iic (max 1 b₀) :=
    fun x hx => (clipped_support_upper _ a₀ b₀ 1 (-θ) ha₀ le_rfl hsstar hx).trans (le_max_right 1 b₀)
  have hconj : (fun x => star (clippedSource W 1 θ x)) =
      clippedSource (fun x => star (W x)) 1 (-θ) := funext (clippedSource_conjugate W 1 θ)
  let E_fin : ℝ := (A_card * C_w + tailC) * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) *
    (1 + ‖θ‖) ^ (2 * deg_in)
  have hn_nz := nonzero_frequency_norm_le p hp hcop hg hinj hodd hprim Finset.univ base
    (assignedElement assigned qelem)
    (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
    (clippedSource W 1 θ) Φ U D_val m_row E_fin hU_pos (by
      intro freqT hzero_f
      rw [hconj]
      let S := finiteSource (Finset.univ : Finset (primePool F_pool)) freqT
      have hdiv_S := finiteSource_divisor (Finset.univ : Finset (primePool F_pool)) freqT
      have hf_S := finiteSource_nonzero (Finset.univ : Finset (primePool F_pool)) freqT hzero_f
      obtain ⟨T, hT, hfreqcap⟩ := exists_source_frequency_cap p S
      have hsplit := actual_physical_retained_tail p hp hcop hg hprim Finset.univ S hdiv_S hf_S
        (fun _ => 1) base (assignedElement assigned qelem)
        (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
        (clippedSource (fun x => star (W x)) 1 (-θ)) (clippedSource W 1 θ) Φ
        U D_val m_row (max 1 b₀) T (4 * η₀ + η₀) hU1 hs_cls hs_cl hfreqcap
      simp only [Function.comp_def] at hsplit ⊢
      rw [hsplit]
      apply (norm_add_le _ _).trans
      let Sc := cappedSource p S (fun _ => 1) (physicalCaps (max 1 b₀) U D_val T)
      have hdivc : ∀ x ∈ Sc, x.divisor ⊆ x.common := fun x hx => hdiv_S x (Finset.mem_filter.mp hx).1
      have hfc : ∀ x ∈ Sc, x.frequency ≠ 0 := fun x hx => hf_S x (Finset.mem_filter.mp hx).1
      have hwin_k : ∀ k ∈ retainedWindows (fun _ => 1) (physicalCaps (max 1 b₀) U D_val T)
          U D_val m_row (4 * η₀ + η₀),
          ‖windowBlock p hg Finset.univ Sc (fun _ => 1) base (assignedElement assigned qelem)
            (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
            (clippedSource (fun x => star (W x)) 1 (-θ)) (clippedSource W 1 θ) Φ
            U D_val m_row (fun i => (k i).val)‖ ≤
            C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) * (1 + ‖θ‖) ^ (2 * deg_in) := by
        intro k hk
        have hsize_pos : 0 < max 1 b₀ * U ^ D_val := mul_pos hb_pos (Real.rpow_pos_of_pos hU_pos D_val)
        have h0 := hexp.2 (max 1 b₀ * U ^ D_val) D_val hsize_pos le_rfl (k 0).val (k 0).property
        have h1 := hexp.2 (max 1 b₀ * U ^ D_val) D_val hsize_pos le_rfl (k 1).val (k 1).property
        have hw_b := hwin U hUw' hpow4 hlog Dpool hDpool (v := exponent U (k 2).val)
          hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi
          (by linarith only [h0.2, h1.1, hD_hi, ht_sm]) (Finset.mem_filter.mp hk).2
          selected hz_sel_hi assigned hD_eq qelem primeW hqe hprimeW hprimeLive hprodj
          hlarge_Z lists_full hlists_full hdisj_sel ζ_base hζ_re hζ_im a ha_eq
          Sc hdivc hfc 1 1 (-θ) θ le_rfl hbcap le_rfl hbcap
          (fun x => 1 * outerCutoff InverseInitialDyadicAssembly.cutoff
            (sourceRelative p x U D_val (exponent U (k 0).val)
              (exponent U (k 2).val) (exponent U (k 1).val) (exponent U (k 3).val)))
          (fun x _ => by
            rw [one_mul]
            have hmul {x₁ x₂ : ℝ} (ha₁ : x₁ ≤ 1) (hb₀ : 0 ≤ x₂) (hb₁ : x₂ ≤ 1) : x₁ * x₂ ≤ 1 :=
              (mul_le_of_le_one_left hb₀ ha₁).trans hb₁
            unfold outerCutoff; simp only [norm_mul]
            exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity) (cutoff_norm_le _ _))
              (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _))
        have hrhs_eq : C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) *
            ((1 + ‖-θ‖) ^ deg_in * (1 + ‖θ‖) ^ deg_in) =
          C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) * (1 + ‖θ‖) ^ (2 * deg_in) := by
          rw [norm_neg, ← pow_add, Nat.two_mul]
        unfold windowBlock
        exact hw_b.trans_eq hrhs_eq
      have hret_sum : ‖∑ k ∈ retainedWindows (fun _ => 1) (physicalCaps (max 1 b₀) U D_val T)
            U D_val m_row (4 * η₀ + η₀),
          windowBlock p hg Finset.univ Sc (fun _ => 1) base (assignedElement assigned qelem)
            (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
            (clippedSource (fun x => star (W x)) 1 (-θ)) (clippedSource W 1 θ) Φ
            U D_val m_row (fun i => (k i).val)‖ ≤
          A_card * C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) *
            (1 + ‖θ‖) ^ (2 * deg_in) := by
        apply (norm_sum_le _ _).trans ((Finset.sum_le_sum hwin_k).trans _)
        rw [Finset.sum_const, nsmul_eq_mul]
        calc _ ≤ (A_card * U ^ loss) *
              (C_w * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t) * (1 + ‖θ‖) ^ (2 * deg_in)) :=
            mul_le_mul_of_nonneg_right (hcU D_val m_row (4 * η₀ + η₀) T hD_hi hm_pos le_rfl hT)
              (by positivity)
          _ = _ := by
              rw [Real.rpow_add hU_pos (m_row + 15 * η₀ + π_loss + 13 * D.t) loss]; ring
      have ht_b := htail p hp hcop hg hinj hodd hprim base hbase1
        (assignedElement assigned qelem) slots
        (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val)
        hdis_slots ha_norm
        (clippedSource (fun x => star (W x)) 1 (-θ)) (clippedSource W 1 θ) Φ
        U D_val m_row η₀ (max 1 b₀) 1 B₀ B₀ hU1 hη₀_pos.le hb_pos h64 (by norm_num) hsize
        (by dsimp only [m_row]; linarith only [ht_pos])
        (by dsimp only [m_row]; linarith only [hD_lo, ht_sm])
        zero_le_one hB₀ hB₀ (clipped_bound _ B₀ hbStar 1 (-θ)) (clipped_bound W B₀ hb 1 θ)
        hs_cls hs_cl Finset.univ Sc (fun _ => 1)
        (fun _ _ => Finset.subset_univ _) (fun _ _ => Finset.subset_univ _)
        hdivc hfc (fun _ _ => by norm_num) (fun _ => 1) (physicalCaps (max 1 b₀) U D_val T)
        (fun _ => by norm_num) (fun x hx => (Finset.mem_filter.mp hx).2)
      have hpow_t : U ^ (-1 : ℝ) ≤ U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) :=
        Real.rpow_le_rpow_of_exponent_le hU1.le
          (by dsimp only [m_row, η₀, π_loss, loss]; linarith only [ht_pos])
      have hht1 : 1 ≤ (1 + ‖θ‖) ^ (2 * deg_in) := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg θ))
      have ht_b' : Ct * 1 * B₀ * B₀ * ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ * U ^ (-1 : ℝ) ≤
          tailC * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) * (1 + ‖θ‖) ^ (2 * deg_in) := by
        dsimp only [tailC]
        calc _ = Ct * B₀ * B₀ * ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ * U ^ (-1 : ℝ) := by ring
          _ ≤ (Ct * B₀ * B₀ * ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) *
                U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) :=
              mul_le_mul_of_nonneg_left hpow_t htailC
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hht1
      exact (add_le_add hret_sum (ht_b.trans ht_b')).trans_eq (by dsimp only [E_fin]; ring))
  have hz0 := hzero p hp hcop hg hinj hodd hprim Finset.univ base hbase1
    (assignedElement assigned qelem) slots
    (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val)
    hdis_slots ha_norm (clippedSource W 1 θ) (clipped_bound W B₀ hb 1 θ) hs_cl
    U D_val m_row hU1.le hD_hi
  have hr_le := InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ base
    (assignedElement assigned qelem)
    (initialTest p (primeMark slots (fun x : ↥selected => lists_full x.val)
      (fun x : ↥selected => a x.val)) (childLogTest W θ) U D_val)
    ((U ^ (-D_val / 2) : ℝ) : ℂ) Φ hΦ hone (U ^ m_row) (Real.rpow_pos_of_pos hU_pos _) rows hrows
  refine hr_le.trans ?_
  rw [InverseInitialProfileBounds.childLogTest_eq_clipped]
  rw [original_input_zero_nonzero p hp hcop hg hinj hodd hprim Finset.univ base
    (assignedElement assigned qelem)
    (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
    (clippedSource W 1 θ) Φ U D_val m_row hU_pos]
  apply (norm_add_le _ _).trans
  have hht1 : 1 ≤ (1 + ‖θ‖) ^ (2 * deg_in) := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg θ))
  have hz0' : Cz * U ^ (m_row + loss) ≤
      Cz * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) * (1 + ‖θ‖) ^ (2 * deg_in) := by
    calc Cz * U ^ (m_row + loss)
        ≤ Cz * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hU1.le
              (by dsimp only [η₀, π_loss]; linarith only [ht_pos])) hCz.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hht1
  change ‖physicalFrequency p hg Finset.univ base (assignedElement assigned qelem)
    (primeMark slots (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => a x.val))
    (clippedSource W 1 θ) Φ U D_val m_row 0‖ + _ ≤ _
  have htot := (add_le_add (hz0.trans hz0') hn_nz).trans_eq
    (by dsimp only [E_fin, C_in]; ring :
      Cz * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) * (1 + ‖θ‖) ^ (2 * deg_in) + E_fin =
      C_in * U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) * (1 + ‖θ‖) ^ (2 * deg_in))
  refine htot.trans ?_
  have hexp_14 : U ^ (m_row + 15 * η₀ + π_loss + 13 * D.t + loss) ≤ U ^ (1 + 14 * D.t) :=
    Real.rpow_le_rpow_of_exponent_le hU1.le
      (by dsimp only [m_row, η₀, π_loss, loss]; linarith only [ht_pos])
  rw [show ((1 + ‖θ‖) ^ deg_in) ^ 2 = (1 + ‖θ‖) ^ (2 * deg_in) by rw [← pow_mul, Nat.mul_comm]]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp_14 (by dsimp only [C_in]; positivity))
    (pow_nonneg (add_nonneg zero_le_one (norm_nonneg θ)) _)

/-! ### Part IV: Overlap Fourier `t`-absorption, deleted sources, and `MomentsSub16799` -/

private lemma primeMark_congr_on {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
    (I : Finset σ) (L : σ → Finset ι) (f₁ f₂ : σ → ι → ℂ)
    (hf : ∀ i ∈ I, ∀ q ∈ L i, f₁ i q = f₂ i q) (A : Finset ι) :
    primeMark I L f₁ A = primeMark I L f₂ A := by
  unfold primeMark primeSlot
  refine Finset.prod_congr rfl fun i hi => Finset.sum_congr rfl fun q hq => ?_
  by_cases hqA : q ∈ A
  · simp only [if_pos hqA, hf i hi q hq]
  · simp only [if_neg hqA]

/-- Stage-1 overlap Fourier energy bound: absorbs `-2 π i t` into `ζ_base` on
`|t| ≤ (1 / (8 * π)) * Z_dual ^ τ_dual` and absorbs `|t| > (1 / (8 * π)) * Z_dual ^ τ_dual`
pointwise via `original_input_rows_fourier_bound` at `m_big = 10` without splitting the integral. -/
private theorem original_fourier_energy_bound_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (g : 𝓢(ℝ, ℂ)) (W : ℝ → ℂ) {a₀ b₀ bcap B₀ : ℝ} (ha₀ : 0 < a₀) (hbcap : 1 ≤ bcap)
    (hs : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (hB₀ : 0 ≤ B₀) (hb : ∀ x, ‖W x‖ ≤ B₀)
    (Φ : 𝓢(ℝ, ℂ)) (hΦ : ∀ x, 0 ≤ (Φ x).re) (hone : ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ x = 1) :
    let η₀ : ℝ := D.t / 10000
    let m_row : ℝ := 1 + D.t / 2
    ∃ (τ_dual B_tree : ℝ) (deg_f : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_tree ∧
      ∀ data : RowData, ∃ C_f U_f : ℝ, 0 < C_f ∧ 2 ≤ U_f ∧
      ∀ U : ℝ, U_f ≤ U →
      ∀ Dpool : ℕ, B_tree * U ^ (13 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
        fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
      let p := poolPrimary F_pool
      let hg := poolPrimary_good F_pool hFa
      let base := elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_orig_in rr D_val : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      ∀ (assigned : Finset ↥selected),
      let z_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      D_val = rr + assignedCenter Finset.univ z_sel - 2 * assignedCenter assigned z_sel →
      ∀ (qelem : ↥selected → O) (primeW : ↥selected → ℝ → ℂ),
        (∀ i ∈ assigned, qelem i ≠ 0) →
        (∀ i ∈ assigned, Function.support (primeW i) ⊆ Set.Icc 1 2) →
        (∀ i ∈ assigned, primeW i ((Ideal.absNorm (Ideal.span {qelem i}) : ℝ) / U ^ (z_sel i)) ≠ 0) →
        ((2 : ℝ) ^ assigned.card ≤ U ^ η₀) →
        ((2 : ℝ) ^ (Finset.univ \ assigned).card ≤ U ^ η₀) →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ selected, lists_full j = poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (selected : Set (Fin D.N)).PairwiseDisjoint lists_full →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (1 / 2 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ selected, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      ∀ (rows : Finset O), (∀ u ∈ rows, ‖ringComplex u‖ ^ 2 ≤ U ^ m_row) →
      ∀ (xj θ : ℝ),
        (∑ u ∈ rows, ‖∫ t : ℝ, density (frequencyTwist g θ) xj t *
          (((U ^ (-D_val / 2) : ℝ) : ℂ) *
            inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ base
              (assignedElement assigned qelem) 1 1
              (initialTest p (primeMark (Finset.univ \ assigned)
                (fun x : ↥selected => lists_full x.val)
                (fun x : ↥selected => fun q =>
                  a x.val q * kernelLogPhase (-t) (Real.log ((q.val.absNorm : ℝ) / Z_slot x.val))))
                (childLogTest W t) U D_val) u)‖ ^ 2) ≤
          C_f * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 := by
  intro η₀ m_row
  have ht_pos : 0 < D.t := D.t_pos
  have ht_sm : D.t ≤ 1 / 100000000 := D.t_small
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; positivity
  have hη₀_1 : η₀ ≤ 1 := by dsimp only [η₀]; linarith only [ht_sm]
  have hη₀_50 : η₀ ≤ (1 : ℝ) / 50 := by dsimp only [η₀]; linarith only [ht_sm]
  obtain ⟨τ_dual, B_t1, deg_1, hτ_pos, hτ_le, hBt1_1, hin_all⟩ :=
    original_input_rows_bound_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      W ha₀ hbcap hs hW hB₀ hb Φ hΦ hone
  obtain ⟨deg_2, B_t2, _hBt2_1, hbig_all⟩ :=
    InverseInitialTotalRows.original_input_rows_fourier_bound
      W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
      12 1 (1 / 4) (1 / 4) η₀ η₀ (1 / 4)
      (by norm_num) zero_lt_one (by norm_num) (by norm_num)
      hη₀_pos hη₀_1 hη₀_50 hη₀_pos hη₀_50 (by norm_num) D.N
  let N_tail : ℕ := ⌈(5 : ℝ) / τ_dual⌉₊ + 1
  let deg_pt : ℕ := max deg_1 (deg_2 + N_tail)
  obtain ⟨Cm, _hCm, hmeasure⟩ :=
    InverseInitialOverlapHeight.twisted_polynomial_measure_energy g deg_pt
  let B_tree : ℝ := max B_t1 B_t2
  let deg_f : ℕ := deg_pt + (volume : Measure ℝ).integrablePower
  refine ⟨τ_dual, B_tree, deg_f, hτ_pos, hτ_le, hBt1_1.trans (le_max_left _ _), ?_⟩
  intro data
  obtain ⟨hq_per, _, hbase1, hbase_per⟩ := raw_conjugate_base_gates data
  obtain ⟨C₁, U₁, hC₁, hU₁_2, hin⟩ := hin_all data
  obtain ⟨C₂, U₂, hC₂, _hU₂_1, hbig⟩ := hbig_all (deletedPeriod (basePeriod data)) hq_per
  let C_pt : ℝ := C₁ + C₂ * (8 * Real.pi) ^ (2 * N_tail)
  have hCpt_pos : 0 < C_pt := add_pos hC₁ (mul_pos hC₂ (pow_pos (by positivity) _))
  refine ⟨(Cm + 1) * C_pt, max U₁ U₂, mul_pos (by linarith only [_hCm]) hCpt_pos,
    hU₁_2.trans (le_max_left _ _), ?_⟩
  intro U hU Dpool hDpool q_per F_pool hFa p hg base
    d_outer r_orig_in rr D_val hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi
    selected hz_sel_hi assigned z_sel Z_slot Z_dual hD_eq
    qelem primeW hqe hprimeW hprimeLive hprodj hprod_rem
    hlarge_Z lists_full hlists_full hdisj_sel ζ_base hζ_re hζ_im a ha_eq rows hrows xj θ
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU1 : 1 < U := by have h2 := (hU₁_2.trans (le_max_left _ _)).trans hU; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hDp1 : B_t1 * U ^ (10 : ℝ) ≤ (Dpool : ℝ) := by
    have hp10 : U ^ (10 : ℝ) ≤ U ^ (13 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1.le (by norm_num)
    exact (mul_le_mul (le_max_left _ _) hp10 (Real.rpow_nonneg hU_pos.le _)
      (zero_le_one.trans (hBt1_1.trans (le_max_left _ _)))).trans hDpool
  have hDp2 : B_t2 * U ^ ((12 : ℝ) + 1) ≤ (Dpool : ℝ) := by
    rw [show ((12 : ℝ) + 1 : ℝ) = (13 : ℝ) by ring]
    exact (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hU_pos.le _)).trans hDpool
  let y_log : ↥selected → primePool F_pool → ℝ :=
    fun x q => Real.log ((q.val.absNorm : ℝ) / Z_slot x.val)
  let φ : O → ℝ → ℂ := fun u t =>
    ((U ^ (-D_val / 2) : ℝ) : ℂ) *
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ base
        (assignedElement assigned qelem) 1 1
        (initialTest p (primeMark (Finset.univ \ assigned)
          (fun x : ↥selected => lists_full x.val)
          (fun x : ↥selected => fun q => a x.val q * kernelLogPhase (-t) (y_log x q)))
          (childLogTest W t) U D_val) u
  have hpt_all : ∀ t : ℝ, (∑ u ∈ rows, ‖φ u t‖ ^ 2) ≤
      (C_pt * U ^ (1 + 14 * D.t)) * ((1 + ‖t‖) ^ deg_pt) ^ 2 := by
    intro t
    have h1t : 1 ≤ 1 + ‖t‖ := le_add_of_nonneg_right (norm_nonneg t)
    by_cases ht_cut : |t| ≤ (1 / (8 * Real.pi)) * Z_dual ^ τ_dual
    · let ζ_t : ℂ := ζ_base - ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
      let a_t : Fin D.N → primePool F_pool → ℂ :=
        fun j q => primeProfile F_dual.W (Z_slot j) ζ_t q.val / star (idealCoeff (deletedBase data) q.val)
      have hζt_re : ζ_t.re = 17 / 50 := by simp [ζ_t, hζ_re]
      have hζt_im : |ζ_t.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual := by
        have him : ζ_t.im = ζ_base.im - 2 * Real.pi * t := by simp [ζ_t]
        rw [him]
        have hpi_pos : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos
        have h2pi_t : |2 * Real.pi * t| ≤ (1 / 4 : ℝ) * Z_dual ^ τ_dual := by
          rw [abs_mul, abs_of_pos hpi_pos]
          have hmul := mul_le_mul_of_nonneg_left ht_cut hpi_pos.le
          have heq : 2 * Real.pi * ((1 / (8 * Real.pi)) * Z_dual ^ τ_dual) =
              (1 / 4 : ℝ) * Z_dual ^ τ_dual := by field_simp [Real.pi_pos.ne']; ring
          linarith only [hmul, heq]
        have habs := abs_sub ζ_base.im (2 * Real.pi * t)
        linarith only [habs, hζ_im, h2pi_t]
      have hpm_eq : primeMark (Finset.univ \ assigned)
          (fun x : ↥selected => lists_full x.val)
          (fun x : ↥selected => fun q => a x.val q * kernelLogPhase (-t) (y_log x q)) =
        primeMark (Finset.univ \ assigned)
          (fun x : ↥selected => lists_full x.val)
          (fun x : ↥selected => a_t x.val) := by
        ext A; refine primeMark_congr_on _ _ _ _ (fun x _ q hq => ?_) A
        have hqL : q.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
          rw [hlists_full x.val x.property] at hq; exact (Finset.mem_filter.mp hq).2
        have hq_ne : q.val ≠ 0 := (livePrime_data F_dual.modulus ⊤ F_dual.W 1 2 (Z_slot x.val)
          (Real.rpow_pos_of_pos hU_pos _) F_dual.complex_support q.val hqL).1.ne_zero
        have hsh := (primeProfile_mul_kernelLogPhase F_dual.W
          (Real.rpow_pos_of_pos hU_pos (D.ell x.val / d_outer)) ζ_base t hq_ne).1
        dsimp only [y_log, a_t, ζ_t] at hsh ⊢
        rw [ha_eq x.val x.property q hq, div_mul_eq_mul_div, hsh]
      have hb_low := hin U ((le_max_left _ _).trans hU) Dpool hDp1
        hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi selected hz_sel_hi assigned hD_eq
        qelem primeW hqe hprimeW hprimeLive hprodj hlarge_Z lists_full hlists_full hdisj_sel
        ζ_t hζt_re hζt_im a_t (fun _ _ _ _ => rfl) rows hrows t
      dsimp only [φ]
      rw [hpm_eq]
      refine hb_low.trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (by dsimp only [C_pt]; linarith only [mul_pos hC₂ (pow_pos (by positivity : (0 : ℝ) < 8 * Real.pi) (2 * N_tail))])
          (Real.rpow_nonneg hU_pos.le _))
        (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ h1t (le_max_left _ _)) 2)
        (sq_nonneg _)
        (mul_nonneg hCpt_pos.le (Real.rpow_nonneg hU_pos.le _))
    · have ht_gt : (1 / (8 * Real.pi)) * Z_dual ^ τ_dual < |t| := lt_of_not_ge ht_cut
      have hz_pos : ∀ x : ↥selected, 0 ≤ z_sel x :=
        fun x => div_nonneg (D.slots_bounds x.val).1.le hd_pos.le
      have hz_all_hi : assignedCenter Finset.univ z_sel ≤ 1964 / 12500 := by
        have heq : assignedCenter Finset.univ z_sel = ∑ j ∈ selected, D.ell j / d_outer :=
          Finset.sum_coe_sort selected (fun j => D.ell j / d_outer)
        rw [heq]; unfold stage1Line at hz_sel_hi; linarith only [hz_sel_hi, hr0]
      have hG_le : assignedCenter assigned z_sel ≤ assignedCenter Finset.univ z_sel :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hz_pos i)
      have hcard_all : (Finset.univ : Finset ↥selected).card ≤ D.N :=
        (Finset.card_univ.trans (Fintype.card_coe selected)).trans_le
          ((Finset.card_le_univ selected).trans_eq (Fintype.card_fin D.N))
      have hdis_all : ((Finset.univ : Finset ↥selected) : Set ↥selected).PairwiseDisjoint
          (fun x : ↥selected => lists_full x.val) :=
        fun x _ y _ hxy => hdisj_sel x.property y.property (fun hv => hxy (Subtype.ext hv))
      have hlists_rem : ∀ x ∈ (Finset.univ : Finset ↥selected) \ assigned,
          1 ≤ 2 * Z_slot x.val ∧
          (∀ P ∈ lists_full x.val, (P.val.absNorm : ℝ) ≤ 2 * Z_slot x.val) ∧
          (∀ P ∈ lists_full x.val, ‖a x.val P‖ ≤ 1) := by
        intro x _
        have h1 := Real.one_le_rpow hU1.le (hz_pos x)
        refine ⟨by linarith only [h1], fun P hP => ?_, fun P hP => ?_⟩
        · have hPL : P.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
            rw [hlists_full x.val x.property] at hP; exact (Finset.mem_filter.mp hP).2
          exact (livePrime_data F_dual.modulus ⊤ F_dual.W 1 2 (Z_slot x.val)
            (Real.rpow_pos_of_pos hU_pos _) F_dual.complex_support P.val hPL).2.2.2
        · have hPL : P.val ∈ livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot x.val) := by
            rw [hlists_full x.val x.property] at hP; exact (Finset.mem_filter.mp hP).2
          have hd_l := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot x.val)
            (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
            (hlarge_Z x.val x.property) P.val hPL
          rw [ha_eq x.val x.property P hP, norm_div, norm_star, ← norm_star (primeProfile _ _ _ _), ← norm_div]
          exact hd_l.2.2.2.2
      have hH_rem : (∏ x ∈ (Finset.univ : Finset ↥selected) \ assigned, 2 * Z_slot x.val) ≤
          U ^ (assignedCenter (Finset.univ \ assigned) z_sel + η₀) := by
        dsimp only [Z_slot, z_sel, assignedCenter]
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hU_pos,
          add_comm _ η₀, Real.rpow_add hU_pos]
        exact mul_le_mul_of_nonneg_right hprod_rem (Real.rpow_nonneg hU_pos.le _)
      have hb_big := hbig U ((le_max_right _ _).trans hU) Dpool hDp2
        Finset.univ assigned (Finset.subset_univ _) hcard_all
        (fun x : ↥selected => lists_full x.val) (fun x : ↥selected => 2 * Z_slot x.val)
        (fun x : ↥selected => a x.val) hdis_all
        (fun x hx => (hlists_rem x hx).1)
        (fun x hx => (hlists_rem x hx).2.1)
        (fun x hx => (hlists_rem x hx).2.2)
        qelem z_sel (fun _ => 1) (fun _ => 2) primeW (fun x _ => hz_pos x) hqe hprimeW hprimeLive
        base hbase1 hbase_per D_val 10 rr (by norm_num) (by norm_num)
        (by dsimp only [η₀] at hrr_lo; linarith only [hD_eq, hrr_lo, hr0, hz_all_hi, hG_le, ht_sm, ht_pos])
        (by simpa only [Finset.prod_const] using hprodj) hH_rem hD_eq
        (by linarith only [hrr_hi, hr1, hz_all_hi])
        (by linarith only [hrr_hi, hr1, hz_all_hi])
        (by linarith only [hrr_hi, hr1, hz_all_hi, hη₀_1])
        rows (fun u hu => (hrows u hu).trans
          (Real.rpow_le_rpow_of_exponent_le hU1.le (by dsimp only [m_row]; linarith only [ht_sm])))
        y_log t
      have hU_le_Zd : U ^ τ_dual ≤ 8 * Real.pi * (1 + ‖t‖) := by
        have h32 : 1 ≤ 3 / (2 * d_outer) := (le_div_iff₀ (by linarith only [hd_lo])).mpr (by linarith only [hd_hi])
        have hUZ : U ^ τ_dual ≤ Z_dual ^ τ_dual :=
          Real.rpow_le_rpow hU_pos.le
            ((Real.rpow_one U).symm.le.trans (Real.rpow_le_rpow_of_exponent_le hU1.le h32)) hτ_pos.le
        have h8t : Z_dual ^ τ_dual ≤ 8 * Real.pi * |t| := by
          have hm := mul_le_mul_of_nonneg_left ht_gt.le (by positivity : (0 : ℝ) ≤ 8 * Real.pi)
          have heq : 8 * Real.pi * ((1 / (8 * Real.pi)) * Z_dual ^ τ_dual) = Z_dual ^ τ_dual := by
            field_simp [Real.pi_pos.ne']
          linarith only [hm, heq]
        have habs_le : |t| ≤ 1 + ‖t‖ := by rw [Real.norm_eq_abs]; linarith only []
        exact hUZ.trans (h8t.trans (mul_le_mul_of_nonneg_left habs_le (by positivity)))
      have h10_le : 10 ≤ τ_dual * (2 * N_tail : ℕ) := by
        have hceil : (5 : ℝ) / τ_dual ≤ (N_tail : ℝ) := by
          dsimp only [N_tail]; push_cast; linarith only [Nat.le_ceil ((5 : ℝ) / τ_dual)]
        have hm := (div_le_iff₀ hτ_pos).mp hceil
        push_cast; linarith only [hm]
      have hU10_tail : U ^ (10 : ℝ) ≤ (8 * Real.pi) ^ (2 * N_tail) * ((1 + ‖t‖) ^ N_tail) ^ 2 := by
        calc U ^ (10 : ℝ)
            ≤ U ^ (τ_dual * (2 * N_tail : ℕ)) := Real.rpow_le_rpow_of_exponent_le hU1.le h10_le
          _ = (U ^ τ_dual) ^ (2 * N_tail) := by rw [Real.rpow_mul hU_pos.le, Real.rpow_natCast]
          _ ≤ (8 * Real.pi * (1 + ‖t‖)) ^ (2 * N_tail) :=
              pow_le_pow_left₀ (Real.rpow_nonneg hU_pos.le _) hU_le_Zd (2 * N_tail)
          _ = (8 * Real.pi) ^ (2 * N_tail) * ((1 + ‖t‖) ^ N_tail) ^ 2 := by
              rw [mul_pow, show (1 + ‖t‖) ^ (2 * N_tail) = ((1 + ‖t‖) ^ N_tail) ^ 2 by
                rw [Nat.mul_comm, pow_mul]]
      have hU_exp_big : U ^ ((10 : ℝ) + 15 * η₀ + 1 / 4 + 1 / 4 + 1 / 4) ≤
          U ^ (1 + 14 * D.t) * ((8 * Real.pi) ^ (2 * N_tail) * ((1 + ‖t‖) ^ N_tail) ^ 2) := by
        have h11 : U ^ ((10 : ℝ) + 15 * η₀ + 1 / 4 + 1 / 4 + 1 / 4) ≤ U ^ (1 : ℝ) * U ^ (10 : ℝ) := by
          rw [← Real.rpow_add hU_pos]
          exact Real.rpow_le_rpow_of_exponent_le hU1.le (by dsimp only [η₀]; linarith only [ht_sm])
        exact h11.trans (mul_le_mul
          (Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [ht_pos]))
          hU10_tail (Real.rpow_nonneg hU_pos.le _) (Real.rpow_nonneg hU_pos.le _))
      refine hb_big.trans ?_
      calc C₂ * U ^ ((10 : ℝ) + 15 * η₀ + 1 / 4 + 1 / 4 + 1 / 4) * ((1 + ‖t‖) ^ deg_2) ^ 2
          ≤ C₂ * (U ^ (1 + 14 * D.t) * ((8 * Real.pi) ^ (2 * N_tail) * ((1 + ‖t‖) ^ N_tail) ^ 2)) *
              ((1 + ‖t‖) ^ deg_2) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU_exp_big hC₂.le) (sq_nonneg _)
        _ = (C₂ * (8 * Real.pi) ^ (2 * N_tail)) * U ^ (1 + 14 * D.t) *
              (((1 + ‖t‖) ^ (deg_2 + N_tail)) ^ 2) := by
            rw [pow_add]; ring
        _ ≤ (C_pt * U ^ (1 + 14 * D.t)) * ((1 + ‖t‖) ^ deg_pt) ^ 2 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right (by dsimp only [C_pt]; linarith only [hC₁])
                (Real.rpow_nonneg hU_pos.le _))
              (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ h1t (le_max_right _ _)) 2)
              (sq_nonneg _)
              (mul_nonneg hCpt_pos.le (Real.rpow_nonneg hU_pos.le _))
  have ht_meas := hmeasure θ xj (fun u : rows => φ u.val) (C_pt * U ^ (1 + 14 * D.t))
    (mul_nonneg hCpt_pos.le (Real.rpow_nonneg hU_pos.le _))
    (fun u => InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ base (assignedElement assigned qelem) u.val
      (Finset.univ \ assigned) (fun x : ↥selected => lists_full x.val)
      (fun x : ↥selected => a x.val) y_log W U D_val xj)
    (fun t => (Finset.sum_coe_sort rows (fun u => ‖φ u t‖ ^ 2)).le.trans (hpt_all t))
  apply (Finset.sum_coe_sort rows
    (fun u => ‖∫ t : ℝ, density (frequencyTwist g θ) xj t * φ u t‖ ^ 2)).symm.le.trans
  refine ht_meas.trans ?_
  have hh0 : 0 ≤ C_pt * U ^ (1 + 14 * D.t) * (1 + ‖θ‖) ^ (2 * deg_f) := by positivity
  have he := mul_le_mul_of_nonneg_right (by linarith only [] : Cm ≤ Cm + 1) hh0
  convert he using 1 <;> simp only [deg_f, pow_mul, pow_two, mul_pow] <;> ring

/-- Fixed-`Dpool` Stage-1 residual tuple step: transfers `original_fourier_energy_bound_sub16799`
across `original_tuples_excluded_fourier` with `F_pool` introduced once as a parameter. -/
private theorem deleted_residual_tuple_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (W : ℝ → ℂ) {ao bo : ℝ} (hao : 0 < ao)
    (hsW : Function.support W ⊆ Set.Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (W_fr : 𝓢(ℝ, ℂ)) {A_fr B_fr Bnorm_fr : ℝ} (hA_fr : 0 < A_fr)
    (hs_fr : Function.support (W_fr : ℝ → ℂ) ⊆ Set.Icc A_fr B_fr)
    (hBn_fr : 0 ≤ Bnorm_fr) (hWb_fr : ∀ x, ‖W_fr x‖ ≤ Bnorm_fr)
    (hFresh : ∀ {σ : Type} [DecidableEq σ] (I : Finset σ), I.card ≤ D.N →
      ∀ V : ℝ → ℂ, Function.support V ⊆ Set.Icc ao bo →
      ∀ (y : σ → ℝ) (yj yc : ℝ), (∀ i ∈ I, y i ∈ Set.Icc 1 2) →
        yj ∈ Set.Icc 1 ((2 : ℝ) ^ D.N) → 0 < yc → V (yj * yc / ∏ i ∈ I, y i) ≠ 0 → W_fr yc = 1) :
    let η₀ : ℝ := D.t / 10000
    ∃ (τ_dual B_tree : ℝ) (deg_f : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧ 1 ≤ B_tree ∧
      ∀ data : RowData, ∃ C_f U_f : ℝ, 0 < C_f ∧ 2 ≤ U_f ∧
      ∀ U : ℝ, U_f ≤ U → (2 : ℝ) ^ D.N ≤ U ^ η₀ →
      ∀ Dpool : ℕ, B_tree * U ^ (13 : ℝ) ≤ (Dpool : ℝ) →
      let q_per := deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      ∀ {d_outer r_orig_in rr : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
        r_orig_in - η₀ ≤ rr → rr ≤ r_orig_in →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      let ell_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      let L_sel : ↥selected → Finset (Ideal O) :=
        fun s => livePrimes F_dual.modulus ⊤ F_dual.W 2 (U ^ (ell_sel s))
      (((Finset.univ : Finset ↥selected) : Set ↥selected).PairwiseDisjoint L_sel) →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < U ^ (D.ell j / d_outer)) →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (1 / 2 : ℝ) * Z_dual ^ τ_dual →
      let coeff_del : ↥selected → Ideal O → ℂ :=
        fun s P => star (primeProfile F_dual.W (U ^ (ell_sel s)) ζ_base P) / idealCoeff (deletedBase data) P
      ∀ (J : Finset ↥selected) (x_asgn : Assigned L_sel J),
        CanonicalQuadraticSieve.Admissible (assignedIdeal L_sel J x_asgn) →
        tupleColumns (originalOutside (originalSource U rr bo) (reflectionExcludedPrimes q_per))
          ((Finset.univ \ J).pi L_sel)
          (fun t => assignedIdeal L_sel J x_asgn * survivingProduct (Finset.univ \ J) t)
          (assignedIdeal L_sel J x_asgn) ⊆ F_pool →
      ∀ rows : Finset O, (∀ u ∈ rows, ‖ringComplex u‖ ^ 2 ≤ U) →
      ∀ θ : ℝ,
        (∑ u ∈ rows, (1 : ℝ) * ‖remainingPolynomial (originalSource U rr bo) L_sel J x_asgn
          coeff_del (idealCoeff (deletedBase data)).toMonoidHom
          (childLogTest W θ) U rr (∑ s : ↥selected, ell_sel s)
          (∑ s ∈ J, ell_sel s) u‖ ^ 2) ≤
          C_f * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 := by
  intro η₀
  have ht_pos : 0 < D.t := D.t_pos
  let W_star : ℝ → ℂ := fun x => star (W x)
  have hs_star : Function.support W_star ⊆ Set.Icc ao bo :=
    fun x hx => hsW (by simpa only [W_star, Function.mem_support, star_ne_zero] using hx)
  have hW_star : ContDiff ℝ ∞ W_star := Complex.conjCLE.contDiff.comp hW
  obtain ⟨τ_dual, B_tree, deg_f, hτ_pos, hτ_le, hBtree1, hf_all⟩ :=
    original_fourier_energy_bound_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      (kernelLogSource W_star ao bo hao hs_star hW_star)
      (W_fr : ℝ → ℂ) hA_fr le_rfl hs_fr (W_fr.smooth ⊤) hBn_fr hWb_fr
      DetectorDictionaryInverseMarkedPadding.radialMajorant
      DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
      DetectorDictionaryInverseMarkedPadding.radialMajorant_one
  refine ⟨τ_dual, B_tree, deg_f, hτ_pos, hτ_le, hBtree1, ?_⟩
  intro data
  obtain ⟨_hq_per, hqset, _hbase1, _hbase_per⟩ := raw_conjugate_base_gates data
  obtain ⟨C_f, U_f, hC_f, hUf2, hfour⟩ := hf_all data
  refine ⟨C_f, U_f, hC_f, hUf2, ?_⟩
  intro U hUf' h2N_η₀ Dpool hDp13 q_per F_pool
    d_outer r_orig_in rr hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi
    selected hz_sel_hi ell_sel Z_dual L_sel
    hdis_live hlarge_Z ζ_base hζ_re hζ_im coeff_del J x_asgn hj_adm hcover rows hrows θ
  have hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
    (reflectionExcludedPrimes_bad q_per)
  letI : ∀ i : primePool F_pool, (Ideal.span {poolPrimary F_pool i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F_pool hFa i]; infer_instance
  let p := poolPrimary F_pool
  let hg := poolPrimary_good F_pool hFa
  have hU1 : 1 < U := by have h2 := hUf2.trans hUf'; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  let χ_del : Ideal O →* ℂ := (idealCoeff (deletedBase data)).toMonoidHom
  have hcard_sel : Fintype.card ↥selected ≤ D.N :=
    (Fintype.card_coe selected).trans_le ((Finset.card_le_univ selected).trans_eq (Fintype.card_fin D.N))
  have hg_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P ≠ 0 ∧ ‖idealCoeff (deletedBase data) P‖ = 1 ∧
      ‖coeff_del s P‖ ≤ 1 :=
    fun s P hP => deleted_source_live_prime F_dual data F_dual.modulus ⊤ _
      (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
      (hlarge_Z s.val s.property) P hP
  have hsupp_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s → Supported P :=
    fun s P hP => deletedBase_supported data P (hg_live s P hP).2.2.1
  have hratio_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      ((P.absNorm : ℝ) / U ^ (ell_sel s)) ∈ Set.Icc (1 : ℝ) 2 :=
    fun _ _ hP => F_dual.complex_support (Finset.mem_filter.mp hP).2
  have hout_q : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) P :=
    fun s P hP => by dsimp only [q_per]; rw [hqset]; exact (hg_live s P hP).2.1
  have hzero_out : ∀ I : Ideal O,
      ¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q_per) I →
      conjugateIdealCharacter χ_del I = 0 :=
    fun I hI => raw_conjugate_zero_outside data I (by dsimp only [q_per] at hI; simpa only [hqset] using hI)
  let j_id : Ideal O := assignedIdeal L_sel J x_asgn
  have hP_adm := remaining_tuple_admissible L_sel (fun s P hP => (hg_live s P hP).1)
    hsupp_live hdis_live J x_asgn
  have hcop_rem := remaining_tuple_coprime L_sel (fun s P hP => (hg_live s P hP).1) hdis_live J
  have hPE_rem := remaining_tuple_outside L_sel (reflectionExcludedPrimes q_per)
    (reflectionExcludedPrimes_prime q_per) hout_q J x_asgn
  let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
  let lists_full : Fin D.N → Finset (primePool F_pool) :=
    fun j => poolList F_pool (livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))
  let a_full : Fin D.N → primePool F_pool → ℂ :=
    fun j q => primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)
  have hdisj_full : (selected : Set (Fin D.N)).PairwiseDisjoint lists_full := by
    intro j₁ hj₁ j₂ hj₂ hjne
    have hd12 := hdis_live (Finset.mem_univ (⟨j₁, hj₁⟩ : ↥selected))
      (Finset.mem_univ (⟨j₂, hj₂⟩ : ↥selected)) (fun he => hjne (congrArg Subtype.val he))
    refine Finset.disjoint_left.mpr fun q hq1 hq2 => ?_
    exact (Finset.disjoint_left.mp hd12) (Finset.mem_filter.mp hq1).2 (Finset.mem_filter.mp hq2).2
  have hcard_J : J.card ≤ D.N := (Finset.card_le_univ J).trans hcard_sel
  have hcard_rem : (Finset.univ \ J).card ≤ D.N := (Finset.card_le_univ _).trans hcard_sel
  let D_val : ℝ := rr + assignedCenter Finset.univ ell_sel - 2 * assignedCenter J ell_sel
  have hrows_m : ∀ u ∈ rows, ‖ringComplex u‖ ^ 2 ≤ U ^ (1 + D.t / 2) := fun u hu =>
    (hrows u hu).trans ((Real.rpow_one U).symm.le.trans
      (Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [ht_pos])))
  have hf_b := hfour U hUf' Dpool hDp13 hd_lo hd_hi hr0 hr1 hrr_lo hrr_hi
    selected hz_sel_hi J rfl (assignedGenerator L_sel J x_asgn) (fun _ => F_dual.W)
    (assignedGenerator_ne_zero L_sel J x_asgn (fun s _ P hP => (hg_live s P hP).1.ne_zero))
    (fun _ _ => F_dual.complex_support)
    (assignedGenerator_window_live L_sel J x_asgn U ell_sel (fun _ => F_dual.W)
      (fun _ _ _ hP => (Finset.mem_filter.mp hP).2))
    ((pow_le_pow_right₀ one_le_two hcard_J).trans h2N_η₀)
    ((pow_le_pow_right₀ one_le_two hcard_rem).trans h2N_η₀)
    hlarge_Z lists_full (fun _ _ => rfl) hdisj_full ζ_base hζ_re hζ_im a_full (fun _ _ _ _ => rfl)
    rows hrows_m (Real.log ((j_id.absNorm : ℝ) / U ^ (assignedCenter J ell_sel))) (-θ)
  have hsum_sdiff : ∑ s ∈ Finset.univ \ J, ell_sel s =
      (∑ s : ↥selected, ell_sel s) - (∑ s ∈ J, ell_sel s) := by
    have hh := Finset.sum_sdiff (Finset.subset_univ J) (f := ell_sel)
    linarith only [hh]
  have hspan_j : Ideal.span {assignedElement J (assignedGenerator L_sel J x_asgn)} = j_id :=
    assignedElement_span L_sel J x_asgn
  have hgj : Ideal.span {primaryIdealGenerator j_id} =
      Ideal.span {assignedElement J (assignedGenerator L_sel J x_asgn)} :=
    (CenteredMomentSourceRow.primary_span_supported j_id (admissible_supported hj_adm)).trans hspan_j.symm
  have hjratio := assigned_ratio_interval L_sel J x_asgn U hU_pos ell_sel D.N hcard_J
    (fun s _ => hratio_live s)
  have hid : ∀ u : O,
      (∑ t ∈ (Finset.univ \ J).pi L_sel,
        (∏ i ∈ (Finset.univ \ J).attach, star (coeff_del i.val (t i.val i.property))) *
        residualNormalizedPolynomial (originalSource U rr bo)
          (j_id * survivingProduct (Finset.univ \ J) t) j_id (conjugateIdealCharacter χ_del)
          (fun _ => 1) (childLogTest W_star (-θ)) U rr
          (∑ s : ↥selected, ell_sel s) (∑ s ∈ J, ell_sel s) u) =
      ∫ t : ℝ, density (frequencyTwist (kernelLogSource W_star ao bo hao hs_star hW_star) (-θ))
        (Real.log ((j_id.absNorm : ℝ) / U ^ (assignedCenter J ell_sel))) t *
        (((U ^ (-D_val / 2) : ℝ) : ℂ) *
          inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ
            (elementCharacter (conjugateIdealCharacter χ_del))
            (assignedElement J (assignedGenerator L_sel J x_asgn)) 1 1
            (initialTest p (primeMark (Finset.univ \ J) (fun s : ↥selected => lists_full s.val)
              (fun s : ↥selected => fun q =>
                a_full s.val q * kernelLogPhase (-t) (Real.log ((q.val.absNorm : ℝ) / Z_slot s.val))))
              (childLogTest (W_fr : ℝ → ℂ) t) U D_val) u) := by
    intro u
    have hh := InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest W_star (-θ)) (W_fr : ℝ → ℂ) ao bo hao
      ((InverseInitialOriginalHeight.child_support W_star (-θ)).trans hs_star)
      (InverseInitialOriginalHeight.child_smooth W_star ao bo hao hs_star hW_star (-θ))
      (reflectionExcludedPrimes q_per) (reflectionExcludedPrimes_prime q_per)
      (Finset.univ \ J) L_sel (fun s _ P hP => (hg_live s P hP).1)
      (fun s P => star (coeff_del s P)) j_id hj_adm.1 hP_adm hcop_rem hPE_rem
      (conjugateIdealCharacter χ_del) hzero_out u U rr
      (∑ s : ↥selected, ell_sel s) (∑ s ∈ J, ell_sel s) hU_pos ell_sel
      (fun _ => 1) (fun _ => 2) hsum_sdiff 1 ((2 : ℝ) ^ D.N) hjratio
      (fun s _ P hP _ => hratio_live s P hP)
      (fun v yj yc hv hyj hyc hn => hFresh (Finset.univ \ J) hcard_rem W_star hs_star
        v yj yc hv hyj hyc (InverseInitialOriginalHeight.child_support W_star (-θ) hn))
      F_pool (fun I hI => (admissible_iff_native I).mpr (hFa I hI))
      (fun I hI => (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.2) hcover
    rw [hh, InverseInitialOriginalHeight.kernelLogSource_child W_star ao bo hao hs_star hW_star (-θ)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have ha_star : (fun s : ↥selected => fun q : primePool F_pool =>
        star (coeff_del s q.val) * kernelLogPhase (-t) (Real.log (slotRatio U ell_sel s q.val))) =
      (fun s : ↥selected => fun q : primePool F_pool =>
        a_full s.val q * kernelLogPhase (-t) (Real.log ((q.val.absNorm : ℝ) / Z_slot s.val))) := by
      funext s q
      dsimp only [coeff_del, a_full, slotRatio, ell_sel, Z_slot]
      rw [star_div₀, star_star]
    have hD_sum : rr + (∑ s : ↥selected, ell_sel s) - 2 * (∑ s ∈ J, ell_sel s) = D_val := rfl
    have hJ_sum : (∑ s ∈ J, ell_sel s) = assignedCenter J ell_sel := rfl
    have hL_pool : (fun i : ↥selected => poolList F_pool (L_sel i)) =
        (fun s : ↥selected => lists_full s.val) := rfl
    rw [ha_star, hD_sum, hJ_sum, hL_pool,
      InverseInitialInputReindex.input_puncture_span p hg Finset.univ
        (elementCharacter (conjugateIdealCharacter χ_del))
        (primaryIdealGenerator j_id) (assignedElement J (assignedGenerator L_sel J x_asgn)) hgj]
  have hchild_star : (fun x => star (childLogTest W θ x)) = childLogTest W_star (-θ) :=
    childLogTest_conjugate W θ
  have hsum_eq : (∑ u ∈ rows, (1 : ℝ) * ‖remainingPolynomial (originalSource U rr bo) L_sel J x_asgn
      coeff_del χ_del (childLogTest W θ) U rr (∑ s : ↥selected, ell_sel s)
      (∑ s ∈ J, ell_sel s) u‖ ^ 2) =
    ∑ u ∈ rows, ‖∫ t : ℝ, density (frequencyTwist (kernelLogSource W_star ao bo hao hs_star hW_star) (-θ))
      (Real.log ((j_id.absNorm : ℝ) / U ^ (assignedCenter J ell_sel))) t *
      (((U ^ (-D_val / 2) : ℝ) : ℂ) *
        inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ
          (elementCharacter (conjugateIdealCharacter χ_del))
          (assignedElement J (assignedGenerator L_sel J x_asgn)) 1 1
          (initialTest p (primeMark (Finset.univ \ J) (fun s : ↥selected => lists_full s.val)
            (fun s : ↥selected => fun q =>
              a_full s.val q * kernelLogPhase (-t) (Real.log ((q.val.absNorm : ℝ) / Z_slot s.val))))
            (childLogTest (W_fr : ℝ → ℂ) t) U D_val) u)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [one_mul, remainingPolynomial_original_pi, hchild_star]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hid u)
  have hrhs_neg : C_f * U ^ (1 + 14 * D.t) * ((1 + ‖-θ‖) ^ deg_f) ^ 2 =
      C_f * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 := by
    rw [norm_neg]
  exact hsum_eq.le.trans (hf_b.trans_eq hrhs_neg)

/-- Stage-1 counterpart of `DetectorDictionaryInverseMarkedReference.deleted_source_energy` across
`1 / 2 ≤ d_outer ≤ 5 / 6` and `69 / 100 ≤ r_orig_in ≤ 19 / 26` with `∑ j ∈ selected, D.ell j / d_outer ≤ stage1Line r_orig_in`. -/
private theorem deleted_source_energy_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (W : ℝ → ℂ) {ao bo : ℝ} (hao : 0 < ao) (hab : ao ≤ bo)
    (hsW : Function.support W ⊆ Set.Icc ao bo) (hW : ContDiff ℝ ∞ W) :
    ∃ (τ_dual : ℝ) (deg_del : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧
      ∀ data : RowData, ∃ C_del U_del : ℝ, 0 < C_del ∧ 1 < U_del ∧
      ∀ U : ℝ, U_del ≤ U →
      ∀ {d_outer r_orig_in : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        69 / 100 ≤ r_orig_in → r_orig_in ≤ 19 / 26 →
      ∀ (selected : Finset (Fin D.N)),
        (∑ j ∈ selected, D.ell j / d_outer) ≤ stage1Line r_orig_in →
      let ell_sel : ↥selected → ℝ := fun s => D.ell s.val / d_outer
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      (((Finset.univ : Finset ↥selected) : Set ↥selected).PairwiseDisjoint
        (fun s : ↥selected => livePrimes F_dual.modulus ⊤ F_dual.W 2 (U ^ (ell_sel s)))) →
      (∀ j ∈ selected, ((deletedBase data).modulus.absNorm : ℝ) < U ^ (D.ell j / d_outer)) →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (1 / 2 : ℝ) * Z_dual ^ τ_dual →
      ∀ j_div ∈ idealDivisors (∏ P ∈ excluded data, P),
      ∀ rows : Finset O, (∀ u ∈ rows, ‖ringComplex u‖ ^ 2 ≤ U) →
      ∀ θ : ℝ,
        (∑ u ∈ rows, ‖deletedSelectedSource data F_dual.modulus ⊤ (childLogTest W θ)
          (fun _ => F_dual.W) U (shiftedExponent data U r_orig_in j_div) 0 0 bo
          (fun _ => 2) ell_sel (fun _ => ζ_base) u‖ ^ 2) ≤
          C_del * U ^ (1 + 15 * D.t) * ((1 + ‖θ‖) ^ deg_del) ^ 2 := by
  have ht_pos : 0 < D.t := D.t_pos
  let η₀ : ℝ := D.t / 10000
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; positivity
  obtain ⟨W_fr, A_fr, B_fr, Bnorm_fr, hA_fr, _hAB_fr, hBn_fr, _hWc_fr, hWs_fr, hWb_fr, hFresh⟩ :=
    InverseInitialUniformFresh.exists_uniform_fresh D.N ao bo hao hab
  have hs_fr : Function.support (W_fr : ℝ → ℂ) ⊆ Set.Icc A_fr B_fr :=
    (subset_tsupport (W_fr : ℝ → ℂ)).trans hWs_fr
  obtain ⟨τ_dual, B_tree, deg_f, hτ_pos, hτ_le, hBtree1, hres_all⟩ :=
    deleted_residual_tuple_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      W hao hsW hW W_fr hA_fr hs_fr hBn_fr hWb_fr hFresh
  have hev_2N : ∀ᶠ U : ℝ in atTop, (2 : ℝ) ^ D.N ≤ U ^ η₀ :=
    (tendsto_rpow_atTop hη₀_pos).eventually (eventually_ge_atTop ((2 : ℝ) ^ D.N))
  obtain ⟨U_2N, hU_2N⟩ := eventually_atTop.mp hev_2N
  let A_asgn : ℝ := ((2 : ℝ) ^ D.N * DetectorDictionaryInverseAssignedCount.assignedConstant D.N 2) ^ 2
  have hA_asgn : 0 < A_asgn := sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos D.N (by norm_num)))
  refine ⟨τ_dual, deg_f, hτ_pos, hτ_le, ?_⟩
  intro data
  obtain ⟨_hq_per, hqset, _hbase1, _hbase_per⟩ := raw_conjugate_base_gates data
  obtain ⟨C_f, U_f, hC_f, hUf2, hres_data⟩ := hres_all data
  obtain ⟨Ushift, hshift⟩ := eventually_atTop.mp (marked_shift_eventually data η₀ hη₀_pos)
  let U_del : ℝ := max U_f (max U_2N Ushift)
  have hUdel2 : 2 ≤ U_del := hUf2.trans (le_max_left _ _)
  refine ⟨A_asgn * C_f, U_del, mul_pos hA_asgn hC_f, by linarith only [hUdel2], ?_⟩
  intro U hU d_outer r_orig_in hd_lo hd_hi hr0 hr1 selected hz_sel_hi
    ell_sel Z_dual hdis_live hlarge_Z ζ_base hζ_re hζ_im j_div hj_div rows hrows θ
  have hUf' : U_f ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 < U := by have h2 := hUf2.trans hUf'; linarith only [h2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have h2N_η₀ : (2 : ℝ) ^ D.N ≤ U ^ η₀ :=
    hU_2N U (((le_max_left _ _).trans (le_max_right _ _)).trans hU)
  have hjshift := (hshift U (((le_max_right _ _).trans (le_max_right _ _)).trans hU)).2 j_div hj_div r_orig_in
  let rr : ℝ := shiftedExponent data U r_orig_in j_div
  let L_sel : ↥selected → Finset (Ideal O) :=
    fun s => livePrimes F_dual.modulus ⊤ F_dual.W 2 (U ^ (ell_sel s))
  let coeff_del : ↥selected → Ideal O → ℂ :=
    fun s P => star (primeProfile F_dual.W (U ^ (ell_sel s)) ζ_base P) / idealCoeff (deletedBase data) P
  let χ_del : Ideal O →* ℂ := (idealCoeff (deletedBase data)).toMonoidHom
  have hcard_sel : Fintype.card ↥selected ≤ D.N :=
    (Fintype.card_coe selected).trans_le ((Finset.card_le_univ selected).trans_eq (Fintype.card_fin D.N))
  have hg_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P ≠ 0 ∧ ‖idealCoeff (deletedBase data) P‖ = 1 ∧
      ‖coeff_del s P‖ ≤ 1 :=
    fun s P hP => deleted_source_live_prime F_dual data F_dual.modulus ⊤ _
      (Real.rpow_pos_of_pos hU_pos _) ζ_base (by rw [hζ_re]; norm_num)
      (hlarge_Z s.val s.property) P hP
  have hsupp_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s → Supported P :=
    fun s P hP => deletedBase_supported data P (hg_live s P hP).2.2.1
  have hnorm_live : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      (P.absNorm : ℝ) ≤ 2 * U ^ (ell_sel s) :=
    fun _ _ hP => (div_le_iff₀ (Real.rpow_pos_of_pos hU_pos _)).mp
      (F_dual.complex_support (Finset.mem_filter.mp hP).2).2
  have hout_q : ∀ (s : ↥selected) (P : Ideal O), P ∈ L_sel s →
      InverseInitialExcludedPool.outside (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) P :=
    fun s P hP => by rw [hqset]; exact (hg_live s P hP).2.1
  let E_rem : ℝ := C_f * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2
  have hE_rem0 : 0 ≤ E_rem := by dsimp only [E_rem]; positivity
  have hadm_assigned : ∀ (J : Finset ↥selected) (x_asgn : Assigned L_sel J),
      CanonicalQuadraticSieve.Admissible (assignedIdeal L_sel J x_asgn) := by
    intro J x_asgn
    apply tuple_admissible (fun i : ↥J => L_sel i.val)
      (fun i P hP => (hg_live i.val P hP).1) (fun i => hsupp_live i.val) _ x_asgn
    intro i _ k _ hik
    exact hdis_live (Finset.mem_univ _) (Finset.mem_univ _) (fun he => hik (Subtype.ext he))
  have hres : ∀ (J : Finset ↥selected) (x_asgn : Assigned L_sel J),
      (∑ u ∈ rows, (1 : ℝ) * ‖remainingPolynomial (originalSource U rr bo) L_sel J x_asgn
        coeff_del χ_del (childLogTest W θ) U rr (∑ s : ↥selected, ell_sel s)
        (∑ s ∈ J, ell_sel s) u‖ ^ 2) ≤ E_rem := by
    intro J x_asgn
    have hP_adm := remaining_tuple_admissible L_sel (fun s P hP => (hg_live s P hP).1)
      hsupp_live hdis_live J x_asgn
    have hPE_rem := remaining_tuple_outside L_sel
      (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
      (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) hout_q J x_asgn
    obtain ⟨Dpool, hfloor_12, hcover⟩ := InverseInitialResidualPool.exists_original_complete_pool
      (deletedPeriod (basePeriod data)) U rr bo 12 B_tree hU_pos (zero_le_one.trans hBtree1)
      ((Finset.univ \ J).pi L_sel)
      (fun t => assignedIdeal L_sel J x_asgn * survivingProduct (Finset.univ \ J) t)
      (assignedIdeal L_sel J x_asgn)
      hP_adm (fun _ _ => dvd_mul_right _ _) hPE_rem
    have hDp13 : B_tree * U ^ (13 : ℝ) ≤ (Dpool : ℝ) := by
      simpa only [show ((12 : ℝ) + 1 : ℝ) = (13 : ℝ) by ring] using hfloor_12
    exact hres_data U hUf' h2N_η₀ Dpool hDp13 hd_lo hd_hi hr0 hr1 hjshift.1 hjshift.2.1
      selected hz_sel_hi hdis_live hlarge_Z ζ_base hζ_re hζ_im J x_asgn (hadm_assigned J x_asgn)
      hcover rows hrows θ
  have hb_all := original_energy_with_assigned_count D.N one_le_two hU1.le hcard_sel
    (originalSource U rr bo) L_sel (fun s P hP => (hg_live s P hP).1) hdis_live ell_sel
    (fun s P hP => ⟨(hg_live s P hP).1.ne_zero, hnorm_live s P hP⟩)
    coeff_del (fun s P hP => (hg_live s P hP).2.2.2.2) χ_del
    hadm_assigned
    (fun _ _ => idealCoeff_norm_le_one (deletedBase data) _)
    (childLogTest W θ) rr (∑ s : ↥selected, ell_sel s) rows
    (fun _ => 1) (fun _ => zero_le_one) E_rem hE_rem0 hres
  have hb_rhs : ((2 : ℝ) ^ D.N * DetectorDictionaryInverseAssignedCount.assignedConstant D.N 2) ^ 2 * E_rem ≤
      (A_asgn * C_f) * U ^ (1 + 15 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 := by
    dsimp only [A_asgn, E_rem]
    calc ((2 : ℝ) ^ D.N * DetectorDictionaryInverseAssignedCount.assignedConstant D.N 2) ^ 2 *
            (C_f * U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2)
        = (((2 : ℝ) ^ D.N * DetectorDictionaryInverseAssignedCount.assignedConstant D.N 2) ^ 2 * C_f) *
            U ^ (1 + 14 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 := by ring
      _ ≤ (((2 : ℝ) ^ D.N * DetectorDictionaryInverseAssignedCount.assignedConstant D.N 2) ^ 2 * C_f) *
            U ^ (1 + 15 * D.t) * ((1 + ‖θ‖) ^ deg_f) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [ht_pos]))
              (mul_pos hA_asgn hC_f).le)
            (sq_nonneg _)
  have hb_tot := hb_all.trans hb_rhs
  simpa only [deletedSelectedSource_tuple, one_mul, L_sel, coeff_del, χ_del, rr] using hb_tot

private lemma livePrimes_congr_modulus {M₁ M₂ : Ideal O} (hM : M₁ = M₂)
    (W : ℝ → ℂ) (b Z : ℝ) :
    livePrimes M₁ ⊤ W b Z = livePrimes M₂ ⊤ W b Z := by
  subst hM; rfl

private lemma deletedSelectedSource_congr_modulus {ι : Type} [Fintype ι]
    (data : RowData) {M₁ M₂ : Ideal O} [h₁ : NeZero M₁] [h₂ : NeZero M₂] (hM : M₁ = M₂)
    (W : ℝ → ℂ) (V : ι → ℝ → ℂ) (Z r σ freq bW : ℝ) (b ell : ι → ℝ) (ζ : ι → ℂ) (u : O) :
    deletedSelectedSource data M₁ ⊤ W V Z r σ freq bW b ell ζ u =
    deletedSelectedSource data M₂ ⊤ W V Z r σ freq bW b ell ζ u := by
  subst hM
  have hi : h₁ = h₂ := Subsingleton.elim _ _
  subst hi; rfl

/-- Moving-profile Stage-1 selected inverse-marked bound across all fibers of a source batch on
`1 / 2 ≤ d ≤ 5 / 6` and `69 / 100 ≤ F.r ≤ 19 / 26` with `∑ s ∈ selected, F.widths s < stage1Line F.r`. -/
theorem source_batch_selected_inverse_marked_sub16799
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (S : ProbeFinalAssembly.SourceData D)
    (hmod : S.modulus = F_dual.modulus)
    (hW_eq : S.W = F_dual.W) :
    ∃ (τ_dual : ℝ) (J_sel : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D.t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        1 < Z ∧ ∀ d : ℝ, 1 / 2 ≤ d → d ≤ 5 / 6 →
        ∀ (a ε tstar T allowance : ℝ) (i : ℕ)
          (B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
            (Z ^ d) a ε tstar T allowance i),
          B.data = sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
          B.profile = (fun _ x => (S.w x : ℂ)) → B.upper = (fun _ => 2) →
          B.widths = (fun s => D.ell s / d) →
          ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ (1 / 2 : ℝ) * ((Z ^ d) ^ (3 / (2 * d))) ^ τ_dual →
          B.external = (fun _ => z) →
        ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
        ∀ height : ℝ, 0 ≤ height →
        let F := B.fiber bin label left right hne
        69 / 100 ≤ F.r → F.r ≤ 19 / 26 →
        ∀ selected : Finset (Fin D.N), selected ⊆ F.slots →
          (∑ s ∈ selected, F.widths s) < 269 / 500 - (69 / 125) * F.r →
        ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (-height) height,
          (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) true
            ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
            ((Z ^ d) ^ F.r) s t * F.physicalProduct selected u‖ ^ 2) ≤
            (C * (1 + height) ^ J_sel) * (Z ^ d) ^ (1 + 15 * D.t) := by
  let Label := Sum Bool (RayQuotient.Characters S.modulus ⊤)
  letI : Fintype Label := Fintype.ofFinite _
  let W_ref : ℝ → ℂ := (referenceWindow : ℝ → ℂ)
  have hs_ref : Function.support W_ref ⊆ Set.Icc (1 / 18 : ℝ) (13 / 4) :=
    fun x hx => referenceWindow_support (subset_tsupport _ hx)
  have hsor (b : Bool) : Function.support (orientedProfile b W_ref) ⊆ Set.Icc (1 / 18 : ℝ) (13 / 4) := by
    cases b
    · exact hs_ref
    · exact fun x hx => hs_ref (Function.mem_support.mpr fun h0 => hx (by simp [orientedProfile, h0]))
  have hWor (b : Bool) : ContDiff ℝ ∞ (orientedProfile b W_ref) := by
    cases b
    · exact referenceWindow.smooth ⊤
    · exact Complex.conjCLE.contDiff.comp (referenceWindow.smooth ⊤)
  obtain ⟨τ_f, deg_f, hτ_pf, hτ_lef, hdel_f⟩ :=
    deleted_source_energy_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      (orientedProfile false W_ref) (by norm_num) (by norm_num) (hsor false) (hWor false)
  obtain ⟨τ_t, deg_t, hτ_pt, _hτ_let, hdel_t⟩ :=
    deleted_source_energy_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual emb hemb F_dual
      (orientedProfile true W_ref) (by norm_num) (by norm_num) (hsor true) (hWor true)
  let τ_dual : ℝ := min τ_f τ_t
  let Jref : ℕ := deg_f + deg_t
  obtain ⟨J_sel, Cfourier, hCfourier, hfourier⟩ :=
    DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨τ_dual, J_sel, lt_min hτ_pf hτ_pt,
    (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_two).trans hτ_lef, ?_⟩
  intro η
  let data := sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C_f U_f hC_f hU_f hb_f using fun label : Label => hdel_f (data label)
  choose C_t U_t hC_t _hU_t hb_t using fun label : Label => hdel_t (data label)
  let C_lbl : Label → ℝ := fun l =>
    (((idealDivisors (∏ P ∈ excluded (data l), P)).card : ℝ) + 1) ^ 2 * (C_f l + C_t l)
  have hCl_pos : ∀ l : Label, 0 < C_lbl l := fun l => by
    dsimp only [C_lbl]; have := hC_f l; have := hC_t l; positivity
  let Csum : ℝ := 1 + ∑ l : Label, C_lbl l
  have hCsum_pos : 0 < Csum := by
    have h0 := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hCl_pos l).le)
    dsimp only [Csum]; linarith only [h0]
  have hCl_le : ∀ l : Label, C_lbl l ≤ Csum := fun l => by
    have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCl_pos j).le) (Finset.mem_univ l)
    dsimp only [Csum]; linarith only [he]
  have hscale : ∀ᶠ Z : ℝ in atTop, ∀ l : Label, ∀ d : ℝ, (1 / 200 : ℝ) ≤ d →
      max (U_f l) (U_t l) ≤ Z ^ d :=
    Filter.eventually_all.mpr fun l =>
      HeckeDetectorDyadicGeometry.uniform_scale_threshold (1 / 200) (max (U_f l) (U_t l)) (by norm_num)
  refine ⟨Cfourier * Csum, mul_pos hCfourier hCsum_pos, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hscale,
    deleted_large_eventually data D.ell (fun s => (D.slots_bounds s).1),
    sourceMoment_fiber_prime_geometry_eventually S.modulus ⊤ le_top S η D.t D.t_pos]
    with Z hZ1 hsc hlarge hgeom
  refine ⟨hZ1, ?_⟩
  intro d hd_lo hd_hi a ε tstar T allowance i B hdata hprofile0 hupper hwidths
    z hz_re hz_im hext bin label left right hne height hheight F hr0 hr1
    selected hselected hcap n hn s hs t ht
  have hd_200 : (1 / 200 : ℝ) ≤ d := by linarith only [hd_lo]
  have hd_pos : 0 < d := by linarith only [hd_lo]
  let U : ℝ := Z ^ d
  have hU1 : 1 < U := Real.one_lt_rpow hZ1 hd_pos
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hZd_ge1 : 1 ≤ U ^ (3 / (2 * d)) :=
    Real.one_le_rpow hU1.le (div_nonneg (by norm_num) (by linarith only [hd_lo]))
  have hB_prof : B.profile = (fun _ => (S.W : ℝ → ℂ)) := by
    rw [hprofile0]; funext j x; exact (S.complex_eq x).symm
  have hfd : F.rowData = data label := by change B.data label = data label; rw [hdata]
  have hfp (j : Fin D.N) : (F.profile j : ℝ → ℂ) = (F_dual.W : ℝ → ℂ) := by
    change B.profile j = (F_dual.W : ℝ → ℂ); rw [hB_prof, hW_eq]
  have hfu (j : Fin D.N) : F.upper j = 2 := by change B.upper j = 2; rw [hupper]
  have hfw (j : Fin D.N) : F.widths j = D.ell j / d := by change B.widths j = _; rw [hwidths]
  have hfe (j : Fin D.N) : F.external j = z := by change B.external j = z; rw [hext]
  have hz_sel_le : (∑ j ∈ selected, D.ell j / d) ≤ stage1Line F.r := by
    have heq : (∑ j ∈ selected, D.ell j / d) = ∑ j ∈ selected, F.widths j :=
      Finset.sum_congr rfl fun j _ => (hfw j).symm
    rw [heq]; unfold stage1Line; linarith only [hcap]
  have hdis_sel : (((Finset.univ : Finset ↥selected) : Set ↥selected).PairwiseDisjoint
      (fun s : ↥selected => livePrimes F_dual.modulus ⊤ F_dual.W 2 (U ^ (D.ell s.val / d)))) := by
    intro j _ k _ hjk
    have hd_jk := (hgeom.2 d hd_200 a ε tstar T allowance i B hdata hprofile0 hupper hwidths
      (fun s => by rw [hext]; exact hz_re) bin label left right hne).1 j.val k.val
      (fun he => hjk (Subtype.ext he))
    rwa [hfp j.val, hfp k.val, hfu j.val, hfu k.val, hfw j.val, hfw k.val,
      livePrimes_congr_modulus hmod, livePrimes_congr_modulus hmod] at hd_jk
  have hlarge_sel : ∀ j ∈ selected, ((deletedBase (data label)).modulus.absNorm : ℝ) < U ^ (D.ell j / d) :=
    fun j _ => hlarge.2 d hd_pos label j
  have hslots_supp : ∀ s_idx ∈ selected, ∀ x, F.profile s_idx x ≠ 0 → x ∈ Set.Icc (1 : ℝ) (F.upper s_idx) := by
    intro s_idx _ x hx; rw [hfp s_idx] at hx; rw [hfu s_idx]; exact F_dual.complex_support hx
  have hlarge_fib : ∀ s_idx ∈ selected,
      ((deletedBase F.rowData).modulus.absNorm : ℝ) < 1 * U ^ (F.widths s_idx) := by
    intro s_idx hs_i; rw [hfd, one_mul, hfw s_idx]; exact hlarge_sel s_idx hs_i
  have href : ∀ v : ℝ,
      (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        (U ^ F.r) 0 0 * F.physicalProduct selected u‖ ^ 2) ≤
      (Csum * U ^ (1 + 15 * D.t)) * (1 + ‖v‖) ^ (2 * Jref) := by
    intro v
    have hphys := fiber_child_rows_le_deleted_sources F selected W_ref v (13 / 4) (fun _ => 1) hU1
      (fun x hx => (hs_ref hx).2) hslots_supp hlarge_fib
    rw [hfd] at hphys
    let rows_O : Finset O := F.rows.image (fun u => u.val)
    have hsum_O (fn : O → ℝ) : (∑ u ∈ rows_O, fn u) = ∑ u ∈ F.rows, fn u.val :=
      Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)
    have hrows_O : ∀ u ∈ rows_O, ‖ringComplex u‖ ^ 2 ≤ U := by
      intro u hu; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      rw [ringComplex_norm_sq_eq_absNorm_span]; exact F.row_norm w hw
    let Tbad := idealDivisors (∏ P ∈ excluded (data label), P)
    have hprof_eq : (fun s : ↥selected => F.profile s.val) = (fun _ => (F_dual.W : ℝ → ℂ)) :=
      funext fun s => hfp s.val
    have hup_eq : (fun s : ↥selected => F.upper s.val) = (fun _ => 2) := funext fun s => hfu s.val
    have hwid_eq : (fun s : ↥selected => F.widths s.val) = (fun s : ↥selected => D.ell s.val / d) :=
      funext fun s => hfw s.val
    have hext_eq : (fun s : ↥selected => F.external s.val) = (fun _ => z) := funext fun s => hfe s.val
    have hU_max := hsc label d hd_200
    have hterm : ∀ j_div ∈ Tbad,
        (∑ u ∈ F.rows, ‖deletedSelectedSource (data label) S.modulus ⊤
          (childLogTest (orientedProfile F.reverse W_ref) (orientedFrequency F.reverse v))
          (fun s : ↥selected => F.profile s.val) U (shiftedExponent (data label) U F.r j_div)
          0 0 (13 / 4) (fun s : ↥selected => F.upper s.val) (fun s : ↥selected => F.widths s.val)
          (fun s : ↥selected => F.external s.val) u.val‖ ^ 2) ≤
        (C_f label + C_t label) * U ^ (1 + 15 * D.t) * ((1 + ‖v‖) ^ Jref) ^ 2 := by
      intro j_div hj_div
      simp only [deletedSelectedSource_congr_modulus (data label) hmod]
      rw [hprof_eq, hup_eq, hwid_eq, hext_eq, ← hsum_O (fun w : O =>
        ‖deletedSelectedSource (data label) F_dual.modulus ⊤
          (childLogTest (orientedProfile F.reverse W_ref) (orientedFrequency F.reverse v))
          (fun _ : ↥selected => (F_dual.W : ℝ → ℂ)) U (shiftedExponent (data label) U F.r j_div)
          0 0 (13 / 4) (fun _ : ↥selected => 2) (fun s : ↥selected => D.ell s.val / d)
          (fun _ : ↥selected => z) w‖ ^ 2)]
      have hnorm_v : ‖orientedFrequency F.reverse v‖ = ‖v‖ := by
        cases F.reverse <;> simp [orientedFrequency]
      cases hrev : F.reverse
      · have hz_f : |z.im| ≤ (1 / 2 : ℝ) * (U ^ (3 / (2 * d))) ^ τ_f :=
          hz_im.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_left _ _)) (by norm_num))
        have hb0 := hb_f label U ((le_max_left _ _).trans hU_max) hd_lo hd_hi hr0 hr1
          selected hz_sel_le hdis_sel hlarge_sel z hz_re hz_f j_div hj_div rows_O hrows_O
          (orientedFrequency false v)
        have hn0 : ‖orientedFrequency false v‖ = ‖v‖ := by simp [orientedFrequency]
        rw [hn0] at hb0
        exact hb0.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right (by linarith only [hC_t label]) (Real.rpow_nonneg hU_pos.le _))
          (pow_le_pow_left₀ (by positivity)
            (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) (Nat.le_add_right _ _)) 2)
          (sq_nonneg _)
          (mul_nonneg (add_pos (hC_f label) (hC_t label)).le (Real.rpow_nonneg hU_pos.le _)))
      · have hz_t : |z.im| ≤ (1 / 2 : ℝ) * (U ^ (3 / (2 * d))) ^ τ_t :=
          hz_im.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_right _ _)) (by norm_num))
        have hb1 := hb_t label U ((le_max_right _ _).trans hU_max) hd_lo hd_hi hr0 hr1
          selected hz_sel_le hdis_sel hlarge_sel z hz_re hz_t j_div hj_div rows_O hrows_O
          (orientedFrequency true v)
        have hn1 : ‖orientedFrequency true v‖ = ‖v‖ := by simp [orientedFrequency]
        rw [hn1] at hb1
        exact hb1.trans (mul_le_mul
          (mul_le_mul_of_nonneg_right (by linarith only [hC_f label]) (Real.rpow_nonneg hU_pos.le _))
          (pow_le_pow_left₀ (by positivity)
            (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) (Nat.le_add_left _ _)) 2)
          (sq_nonneg _)
          (mul_nonneg (add_pos (hC_f label) (hC_t label)).le (Real.rpow_nonneg hU_pos.le _)))
    have hsum_bad := hphys.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _))
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_bad
    have hcard_sq : (Tbad.card : ℝ) * ((Tbad.card : ℝ) *
        ((C_f label + C_t label) * U ^ (1 + 15 * D.t) * ((1 + ‖v‖) ^ Jref) ^ 2)) ≤
        (Csum * U ^ (1 + 15 * D.t)) * (1 + ‖v‖) ^ (2 * Jref) := by
      have h1 : (Tbad.card : ℝ) ^ 2 ≤ ((Tbad.card : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith only []) 2
      have h2 : (Tbad.card : ℝ) ^ 2 * (C_f label + C_t label) ≤ Csum :=
        (mul_le_mul_of_nonneg_right h1 (add_pos (hC_f label) (hC_t label)).le).trans (hCl_le label)
      rw [show ((1 + ‖v‖) ^ Jref) ^ 2 = (1 + ‖v‖) ^ (2 * Jref) by rw [← pow_mul, Nat.mul_comm]]
      calc _ = ((Tbad.card : ℝ) ^ 2 * (C_f label + C_t label)) * U ^ (1 + 15 * D.t) *
              (1 + ‖v‖) ^ (2 * Jref) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hU_pos.le _))
            (pow_nonneg (add_nonneg zero_le_one (norm_nonneg v)) _)
    exact hsum_bad.trans hcard_sq
  have hh := hfourier F selected hU_pos (Csum * U ^ (1 + 15 * D.t))
    (mul_nonneg hCsum_pos.le (Real.rpow_nonneg hU_pos.le _)) href n hn s hs height t hheight ht
  convert hh using 1 <;> ring

/-- Combined Stage-0 (`d' < 1 / 2` via `counts_0`) and Stage-1 (`1 / 2 ≤ d' ≤ 5 / 6` via `counts_1`
at `εm = 15 * D.t`) unconditional source-moment supply with a **single** height exponent `τ`
chosen simultaneously for all moment fields and `τ_dual`. -/
theorem subFarkas_source_moments_combined
    (hβ : (16799 / 19200 : ℝ) < HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (ht_eq : D_dual.t = D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh subDelta D.t / 200)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (F : ProbeFinalAssembly.SourceData D)
    (hmod : F.modulus = F_dual.modulus)
    (hW_eq : F.W = F_dual.W)
    (counts_0 : CountParameters F.modulus ⊤ D.t)
    (counts_1 : CountParametersSub16799 F.modulus ⊤ (15 * D.t)) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧ 4 * τ < (1 / 200) * D.cost ∧ τ < D.t ∧
      2 * τ ≤ D.t ∧ τ * (2 + 4 * D.eps) < D.t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z' : ℝ in atTop,
        SourceMomentBound F counts_0 η Z' τ (C * Z' ^ D.t) (Z' ^ (2 * τ)) ∧
        ∀ rows : Finset FreeRow, ∀ d' a : ℝ,
          1 / 2 ≤ d' → d' ≤ 5 / 6 → 51 / 100 < a → a ≤ 1 →
          (∀ u ∈ rows, u.val ≠ 1 ∧ Z' ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
            (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
            rowNorm u ≤ Z' ^ (d' - D.t)) →
          ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ Z' ^ (2 * τ) →
            SourceMomentsAtSub16799 F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
              (fun _ y => (F.w y : ℂ)) Z' d' a D.ε τ (5 / 6) 2 D.t D.t i z subDelta
              (if 2 * a - 1 ≤ 5 / 6 then counts_1.cB else counts_1.cH)
              (if 2 * a - 1 ≤ 5 / 6 then counts_1.kB else counts_1.kH)
              (C * Z' ^ D.t) (Z' ^ (2 * τ)) (15 * D.t) := by
  have hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta := by linarith only [hβ]
  have hβ_hi : HeckeZeroSupremum.beta ≤ 7 / 8 :=
    HeckeCommonProbe.beta_le_seven_eighths ProbeFinalAssemblyUnconditional.common_probe
  have ht_pos : 0 < D.t := D.t_pos
  let Label := Sum Bool (RayQuotient.Characters F.modulus ⊤)
  letI : Fintype Label := Fintype.ofFinite _
  have hcert : ∀ bΦ : ℝ, 0 < bΦ →
      CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
        (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ 0 1 (33 / 50) (33 / 50) 2
        (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
        (CenteredMomentDetectorPlainMomentParameters.stageError D)
        (CenteredMomentEnergyWidthSchedule.count 2
          (CenteredMomentDetectorPlainMomentParameters.stageError D)) := by
    intro bΦ hbΦ
    have hp := CenteredMomentDetectorPlainMomentParameters.fixed_parameters D
    have hsubD : subDelta = 1 / 100000000 := rfl
    exact CenteredMomentEnergyCertifiedExistence.terminal_certificate (α := Fin D.N)
      F.modulus ⊤ le_top (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ 0 1
      (33 / 50) (33 / 50) 2
      (CenteredMomentDetectorPlainMomentParameters.kappaPlain D)
      (CenteredMomentDetectorPlainMomentParameters.stageError D)
      (by norm_num) (CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F)
      (Complex.conjCLE.contDiff.comp (F.W.smooth (⊤ : ℕ∞)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num)
      hp.2.2.2.2.1.le hp.2.2.1 hβ51
      (by unfold CenteredMomentDetectorPlainMomentParameters.kappaPlain; linarith)
  obtain ⟨hp, hz⟩ := plain_inputs F hcert
  let mesh := detectorMesh subDelta D.t
  have hmesh : 0 < mesh := detectorMesh_pos subDelta_pos D.t_pos
  obtain ⟨J_0, hJ_0, hmom_0⟩ := source_moments F counts_0 mesh hmesh hfine hp hz
  obtain ⟨Jr_B, hraw_B⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles
    counts_1.cB counts_1.kB counts_1.cB_pos counts_1.kB_pos
  obtain ⟨Jr_H, hraw_H⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles
    counts_1.cH counts_1.kH counts_1.cH_pos counts_1.kH_pos
  obtain ⟨Jim, him⟩ := ProbeDetectorInverseMarkedField.source_batch_inverse_marked F.modulus ⊤ le_top F
  obtain ⟨Jm, hm⟩ := ProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine F mesh hmesh hfine hp
  obtain ⟨Ju, hu⟩ := ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hz
  obtain ⟨τ_dual, J_sel, hτ_dual_pos, _hτ_dual_le, hsel_all⟩ :=
    source_batch_selected_inverse_marked_sub16799 hβ51 D D_dual ht_eq h2000_eps h2000_e hfine_dual
      emb hemb F_dual F hmod hW_eq
  let J_nat : ℕ := Jr_B + Jr_H + Jim + Jm + Ju + J_sel
  let J_big : ℝ := J_0 + (J_nat : ℝ) + 8 / τ_dual + 1
  have hJ_big : 0 ≤ J_big := by dsimp only [J_big]; positivity
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτJ, hτeps⟩ := D.height_choice J_big hJ_big
  have hτ2 : 2 * τ ≤ D.t := by nlinarith only [hτJ, hτ, hJ_big]
  have hτ1 : τ ≤ 1 := by linarith only [hτt, D.t_small]
  have h2τ_le_dual : 2 * τ ≤ τ_dual / 4 := by
    have h1 : 2 * τ * (8 / τ_dual) ≤ D.t := by
      have hle : 8 / τ_dual ≤ J_big := by
        dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat; linarith only [hJ_0, this]
      have hm := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 * τ)
      linarith only [hm, hτJ, hτ]
    have h2 : 2 * τ * (8 / τ_dual) ≤ 1 := h1.trans (D.t_small.trans (by norm_num))
    have h3 := (div_le_iff₀ hτ_dual_pos).mp (by rwa [← mul_div_assoc] at h2 : (2 * τ * 8) / τ_dual ≤ 1)
    linarith only [h3, hτ_dual_pos]
  refine ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, ?_⟩
  intro η
  obtain ⟨C₀, hC₀, hb₀_all⟩ := hmom_0 η
  let data_η := sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η
  choose CrB_l hCrB_l hb_rawB using fun l : Label => hraw_B (data_η l)
  choose CrH_l hCrH_l hb_rawH using fun l : Label => hraw_H (data_η l)
  let Cr : ℝ := 1 + (∑ l : Label, CrB_l l) + ∑ l : Label, CrH_l l
  have hCr_pos : 0 < Cr := by
    have h1 := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hCrB_l l).le)
    have h2 := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hCrH_l l).le)
    dsimp only [Cr]; linarith only [h1, h2]
  have hCrB_le (l : Label) : CrB_l l ≤ Cr := by
    have h1 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCrB_l j).le) (Finset.mem_univ l)
    have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCrH_l j).le)
    dsimp only [Cr]; linarith only [h1, h2]
  have hCrH_le (l : Label) : CrH_l l ≤ Cr := by
    have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCrB_l j).le)
    have h2 := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hCrH_l j).le) (Finset.mem_univ l)
    dsimp only [Cr]; linarith only [h1, h2]
  obtain ⟨Cim, hCim, him_η⟩ := him η
  obtain ⟨Cm, hCm, hm_η⟩ := hm η
  obtain ⟨Cu, hCu, hu_η⟩ := hu η
  obtain ⟨Csel, hCsel, hsel_η⟩ := hsel_all η
  let C_sum : ℝ := C₀ + Cr + Cim + Cm + Cu + Csel
  let C_tot : ℝ := C_sum * (2 : ℝ) ^ J_big
  have hCtot_pos : 0 < C_tot := by dsimp only [C_tot, C_sum]; positivity
  refine ⟨C_tot, hCtot_pos, ?_⟩
  filter_upwards [hb₀_all τ hτ hτ1, him_η, hm_η, hu_η, hsel_η,
    (tendsto_rpow_atTop (div_pos hτ_dual_pos (by norm_num : (0 : ℝ) < 4))).eventually
      (eventually_ge_atTop (2 : ℝ))] with Z' hb₀ him_z hm_z hu_z hsel_z h2_qtr
  have hZ1 : 1 < Z' := him_z.1
  have hZp : 0 < Z' := zero_lt_one.trans hZ1
  have h2τ_J0 : 2 * τ * (1 + J_0) ≤ D.t := by
    have hle : 1 + J_0 ≤ J_big := by
      dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat
      have : 0 ≤ 8 / τ_dual := by positivity
      linarith only [this, ‹0 ≤ (J_nat : ℝ)›]
    nlinarith only [hle, hτJ, hτ]
  have hb₀_abs : SourceMomentBound F counts_0 η Z' τ (C_tot * Z' ^ D.t) (Z' ^ (2 * τ)) := by
    have h1 := polynomial_height_absorption C₀ Z' τ J_0 D.t hC₀.le hZ1.le hτ.le hJ_0
      (by linarith only [h2τ_J0])
    have h2 : C₀ * (2 : ℝ) ^ J_0 ≤ C_tot := by
      dsimp only [C_tot, C_sum]
      exact mul_le_mul (by linarith only [hCr_pos, hCim, hCm, hCu, hCsel])
        (Real.rpow_le_rpow_of_exponent_le one_le_two (by
          dsimp only [J_big]; have := Nat.cast_nonneg (α := ℝ) J_nat
          have : 0 ≤ 8 / τ_dual := by positivity
          linarith only [this, ‹0 ≤ (J_nat : ℝ)›]))
        (Real.rpow_nonneg zero_le_two _) (by positivity)
    exact hb₀.mono_constant hZp.le (h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hZp.le _)))
  refine ⟨hb₀_abs, ?_⟩
  intro rows d' a hd_lo hd_hi _ha _ha1 hrows i z hz_re hz_im
    q B hB_sub hdata hrev _hslots hwidths hprof hupper hext _hmesh _hbin _hfam
    bin label left right hne
  let height : ℝ := Z' ^ (2 * τ)
  have hh0 : 0 ≤ height := Real.rpow_nonneg hZp.le _
  have hh1 : 1 ≤ height := Real.one_le_rpow hZ1.le (by positivity)
  have hpow_nat (K : ℕ) (hK : K ≤ J_nat) :
      (1 + height) ^ K ≤ (2 : ℝ) ^ J_big * Z' ^ D.t := by
    have h2J : 2 * τ * (J_nat : ℝ) ≤ D.t := by
      have hle : (J_nat : ℝ) ≤ J_big := by
        dsimp only [J_big]; have : 0 ≤ 8 / τ_dual := by positivity
        linarith only [hJ_0, this]
      nlinarith only [hle, hτJ, hτ]
    calc (1 + height) ^ K
        ≤ (1 + height) ^ J_nat := pow_le_pow_right₀ (by linarith only [hh0]) hK
      _ ≤ (2 * height) ^ J_nat := pow_le_pow_left₀ (by positivity) (by linarith only [hh1]) J_nat
      _ = (2 : ℝ) ^ (J_nat : ℝ) * Z' ^ (2 * τ * (J_nat : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_natCast (Z' ^ (2 * τ)),
            ← Real.rpow_mul hZp.le]
      _ ≤ (2 : ℝ) ^ J_big * Z' ^ D.t :=
          mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le one_le_two (by
              dsimp only [J_big]; have : 0 ≤ 8 / τ_dual := by positivity
              linarith only [hJ_0, this]))
            (Real.rpow_le_rpow_of_exponent_le hZ1.le h2J)
            (Real.rpow_nonneg hZp.le _) (Real.rpow_nonneg zero_le_two _)
  have hcoef_le {c : ℝ} {K : ℕ} (hc0 : 0 ≤ c) (hc : c ≤ C_sum) (hK : K ≤ J_nat) :
      c * (1 + height) ^ K ≤ C_tot * Z' ^ D.t := by
    calc c * (1 + height) ^ K
        ≤ C_sum * ((2 : ℝ) ^ J_big * Z' ^ D.t) :=
          mul_le_mul hc (hpow_nat K hK) (pow_nonneg (by positivity) _)
            (by dsimp only [C_sum]; positivity)
      _ = C_tot * Z' ^ D.t := by dsimp only [C_tot]; ring
  have hd_200 : (1 / 200 : ℝ) ≤ d' := by linarith only [hd_lo]
  have hU1 : 1 < Z' ^ d' := Real.one_lt_rpow hZ1 (by linarith only [hd_lo])
  have hUp : 0 < Z' ^ d' := zero_lt_one.trans hU1
  let F_fib := B.fiber bin label left right hne
  have hfd : F_fib.rowData = data_η label := by change B.data label = data_η label; rw [hdata]
  have hrows_lo : ∀ u ∈ rows, Z' ^ (1 / 100 : ℝ) ≤ rowNorm u := fun u hu => (hrows u hu).2.1
  have him_val := him_z.2 d' hd_200 a D.ε (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hdata hprof hupper hwidths
    (fun s => by rw [hext]; exact hz_re) bin label left right hne height hh0
  have hmarked := hm_z.2 rows hrows_lo d' hd_200 a (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hB_sub hdata hprof hwidths
    (fun s => by rw [hupper]) (fun s => by rw [hext]; exact hz_re)
    bin label left right hne height hh0 (fun s => by rw [hext]; exact hz_im)
  have hunmarked := hu_z.2 rows hrows_lo d' hd_200 a (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hB_sub hdata hprof hwidths
    bin label left right hne height hh0
  have hbase_Dt : Moments F_fib subDelta
      (if 2 * a - 1 ≤ 5 / 6 then counts_1.cB else counts_1.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts_1.kB else counts_1.kH)
      (C_tot * Z' ^ D.t) height D.t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn σ hσ t ht
      rw [hfd]
      split_ifs with hδ56
      · have hpB := hb_rawB label F_fib.reverse n hn (Z' ^ d') hUp
          (cutoffSub16799 (2 * a - 1) q) F_fib.r σ hσ height t hh0 ht
        have hcB : CrB_l label * (1 + height) ^ Jr_B ≤ C_tot * Z' ^ D.t :=
          hcoef_le (hCrB_l label).le
            (by dsimp only [C_sum]; linarith only [hCrB_le label, hC₀, hCim, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega)
        exact ⟨ProbeFinalAssembly.rawMoment_mono_constant hpB.1 hcB,
          ProbeFinalAssembly.rawMoment_mono_constant hpB.2 hcB⟩
      · have hpH := hb_rawH label F_fib.reverse n hn (Z' ^ d') hUp
          (cutoffSub16799 (2 * a - 1) q) F_fib.r σ hσ height t hh0 ht
        have hcH : CrH_l label * (1 + height) ^ Jr_H ≤ C_tot * Z' ^ D.t :=
          hcoef_le (hCrH_l label).le
            (by dsimp only [C_sum]; linarith only [hCrH_le label, hC₀, hCim, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega)
        exact ⟨ProbeFinalAssembly.rawMoment_mono_constant hpH.1 hcH,
          ProbeFinalAssembly.rawMoment_mono_constant hpH.2 hcH⟩
    · intro sel hsel hc1 hc2 n hn σ hσ t ht
      exact (him_val sel hsel hc1 hc2 n hn σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCim.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCm, hCu, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
    · intro sel hsel hc j k hjk σ hσ t ht
      exact (hmarked sel hsel hc j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCm.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCu, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
    · intro j k hjk σ hσ t ht
      exact (hunmarked j k hjk σ hσ t ht).1.trans
        (mul_le_mul_of_nonneg_right
          (hcoef_le hCu.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCm, hCsel])
            (by dsimp only [J_nat]; omega))
          (Real.rpow_nonneg hUp.le _))
  have hz_im_dual : |z.im| ≤ (1 / 2 : ℝ) * ((Z' ^ d') ^ (3 / (2 * d'))) ^ τ_dual := by
    have h1 : Z' ^ (2 * τ) ≤ Z' ^ (τ_dual / 4) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le h2τ_le_dual
    have h2 : 2 * Z' ^ (τ_dual / 4) ≤ Z' ^ τ_dual := by
      have hprod : 2 * Z' ^ (τ_dual / 4) ≤ Z' ^ (τ_dual / 4) * Z' ^ (τ_dual / 4) :=
        mul_le_mul_of_nonneg_right h2_qtr (Real.rpow_nonneg hZp.le _)
      rw [← Real.rpow_add hZp, show τ_dual / 4 + τ_dual / 4 = τ_dual / 2 by ring] at hprod
      exact hprod.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hτ_dual_pos]))
    have h3 : Z' ^ τ_dual ≤ ((Z' ^ d') ^ (3 / (2 * d'))) ^ τ_dual := by
      have h32 : 1 ≤ 3 / (2 * d') := (le_div_iff₀ (by linarith only [hd_lo])).mpr (by linarith only [hd_hi])
      have hZ_le : Z' ≤ (Z' ^ d') ^ (3 / (2 * d')) := by
        rw [← Real.rpow_mul hZp.le, show d' * (3 / (2 * d')) = (3 / 2 : ℝ) by
          field_simp [(by linarith only [hd_lo] : d' ≠ 0)]]
        exact (Real.rpow_one Z').symm.le.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num))
      exact Real.rpow_le_rpow hZp.le hZ_le hτ_dual_pos.le
    linarith only [hz_im, h1, h2, h3]
  refine ⟨moments_mono_eps hU1.le (by positivity) (by linarith only [ht_pos]) hbase_Dt, ?_⟩
  intro hr0 hr1 selected hselected hcap n hn s hs t ht
  have hs_val := hsel_z.2 d' hd_lo hd_hi a D.ε (cutoffSub16799 (2 * a - 1) q) (Z' ^ τ)
    ((Z' ^ d') ^ (τ / (2 * (5 / 6)))) i B hdata hprof hupper hwidths z hz_re hz_im_dual hext
    bin label left right hne height hh0 hr0 hr1 selected hselected hcap n hn s hs t ht
  exact hs_val.trans (mul_le_mul_of_nonneg_right
    (hcoef_le hCsel.le (by dsimp only [C_sum]; linarith only [hC₀, hCr_pos, hCim, hCm, hCu])
      (by dsimp only [J_nat]; omega))
    (Real.rpow_nonneg hUp.le _))

end SubFarkasSelectedInverseMoments

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
