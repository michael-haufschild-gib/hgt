import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1ParentPoissonEnergy

/-!
# Stage-1 core column energy on `69/100 ≤ r ≤ 19/26`

This module completes the Stage-1 descent by combining the `q0`-stripped Pass-2 recursion on cube
bins with `ell + V ≥ 3 / 500` (`Stage1B0StrippedAndTinyCubeBins`) and the dual sixth-power-free
factored `parentPoisson` bound at `Q = {0}` on tiny cube bins `0 ≤ ell + V < 3 / 500`
(`Stage1ParentPoissonEnergy`):

1. **Padded & list-punctured sixth-power-free factored energy
   (`dual_sixth_free_factored_energy_lists_sdiff_padded`):**
   Extends `dual_sixth_free_factored_energy` to `∑ j ∈ T', D.ell j / d_outer ≤ z_T_cap + pad_T`
   (by peeling a greedy subset `T_keep ⊆ T'` within `z_T_cap` and bounding `T' \ T_keep` pointwise
   via `canonicalPrimeAmplitude_norm_sq_le_trivial`) and to sub-lists `lists_sub j ⊆ lists_full j`
   missing at most `M_drop` primes per slot (by expanding `slotCharSum` differences across
   `T'' ⊆ T_keep`).

2. **Uniform `principalWindow` Fourier log-separation
   (`principalWindow_markedRadial_fourier_l2_le_factored`):**
   Constructs a single `(negative, t)`-independent Schwartz cutoff `wFresh` for
   `principalWindow om a₀ b₀ ha₀ hs negative t` with polynomial `(1 + ‖t‖)` growth via
   `frequencyTwist_fourier_moment`.

3. **Cell-summed `globalPriorityOriginalEnergy` at `Q = {0}` (`dual_qzero_cell_energy`),
   sharp sextic label transfer (`qzero_sextic_label_transfer_sharp`), tiny-bin bound
   (`tiny_cube_bin_qzero_cauchy`), and Stage-1 core column energy
   (`stage1_core_normalized_column_energy`).**
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1CoreColumnEnergy

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open CubicSieve CenteredMomentFourier
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment InverseMoment
open InverseSecondPrincipalCaller InverseFirstPriorityParents InversePrioritySecondSource
open InversePrincipalEnergy UniqueFactorizationMonoid SecondPassIntegration
open InverseInitialArithmetic RayFourExpansion
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialDetectorSource
open InverseInitialPhysicalSlots InverseInitialRawDictionary
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawConjugateGates InverseInitialExcludedPeriod
open InverseInitialConjugateEnergy CanonicalCoefficientClass
open ProbeFinalAssembly ProbeHighRowFamily ProbeFinalAssemblyCertifiedBands
open SubSevenEighthsHighTransport
open GaloisForLFunctions.FamilyContinuationTheory.Budget
open Stage1CubeBins Stage1DualRowMoments Stage1ReciprocityAndUnpuncture
open Stage1DualSixthFreeEnergy Stage1ParentPoissonEnergy
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstSecondHeightCost
open CompletedHeight JointLogSeparation IdealDivisorBound

local notation "O" => Eisenstein.O

/-! ### Part I: Greedy slot-sum peeling and bounded-puncture `slotCharSum` expansion -/

private lemma mem_filter_of {α : Type*} {s : Finset α} {P : α → Prop} {inst : DecidablePred P}
    {x : α} (h : x ∈ @Finset.filter α P inst s) : x ∈ s ∧ P x :=
  (@Finset.mem_filter α P inst s x).mp h

private lemma sum_filter_norm_sq_mul {α : Type*} (s : Finset α) (f : α → ℂ) (g : α → ℝ)
    {inst : DecidablePred (fun x => f x ≠ 0)} :
    (∑ x ∈ s, ‖f x‖ ^ 2 * g x) =
      ∑ x ∈ @Finset.filter α (fun x => f x ≠ 0) inst s, ‖f x‖ ^ 2 * g x := by
  letI : DecidablePred (fun x => f x ≠ 0) := inst
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs with hx
  · rfl
  · rw [Classical.not_not.mp hx, norm_zero, zero_pow two_ne_zero, zero_mul]

/-- Greedy subset peeling: if `∑ j ∈ T', w j ≤ C_cap + pad` with `0 ≤ w j ≤ mesh`, `0 ≤ mesh`,
`0 ≤ C_cap`, and `0 ≤ pad`, there exists `K ⊆ T'` with `∑ j ∈ K, w j ≤ C_cap` and
`∑ j ∈ T' \ K, w j ≤ pad + mesh`. -/
lemma exists_subset_sum_le_and_sdiff_le {α : Type*} [DecidableEq α]
    (T' : Finset α) (w : α → ℝ) {mesh C_cap pad : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hw0 : ∀ j ∈ T', 0 ≤ w j) (hw_hi : ∀ j ∈ T', w j ≤ mesh)
    (hC0 : 0 ≤ C_cap) (hpad0 : 0 ≤ pad)
    (hsum : (∑ j ∈ T', w j) ≤ C_cap + pad) :
    ∃ K : Finset α, K ⊆ T' ∧ (∑ j ∈ K, w j) ≤ C_cap ∧ (∑ j ∈ T' \ K, w j) ≤ pad + mesh := by
  induction T' using Finset.induction_on generalizing pad with
  | empty =>
    exact ⟨∅, Finset.Subset.rfl, by simpa using hC0, by simpa using add_nonneg hpad0 hmesh0⟩
  | @insert a s ha ih =>
    have hwa0 : 0 ≤ w a := hw0 a (Finset.mem_insert_self a s)
    have hwa_hi : w a ≤ mesh := hw_hi a (Finset.mem_insert_self a s)
    have hws0 : ∀ j ∈ s, 0 ≤ w j := fun j hj => hw0 j (Finset.mem_insert_of_mem hj)
    have hws_hi : ∀ j ∈ s, w j ≤ mesh := fun j hj => hw_hi j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha] at hsum
    by_cases hs_le : (∑ j ∈ s, w j) ≤ C_cap
    · by_cases hins_le : w a + (∑ j ∈ s, w j) ≤ C_cap
      · refine ⟨insert a s, Finset.Subset.rfl, ?_, ?_⟩
        · rwa [Finset.sum_insert ha]
        · rw [Finset.sdiff_self, Finset.sum_empty]; exact add_nonneg hpad0 hmesh0
      · refine ⟨s, Finset.subset_insert a s, hs_le, ?_⟩
        have hsdiff : insert a s \ s = {a} := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.1.resolve_right h.2, fun h => ⟨Or.inl h, h ▸ ha⟩⟩
        rw [hsdiff, Finset.sum_singleton]
        linarith only [hwa_hi, hpad0]
    · have hs_gt : C_cap < ∑ j ∈ s, w j := not_le.mp hs_le
      have hpad' : 0 ≤ pad - w a := by linarith only [hs_gt, hsum]
      obtain ⟨K, hKs, hK_sum, hK_sdiff⟩ := ih hws0 hws_hi hpad' (by linarith only [hsum])
      have haK : a ∉ K := fun hm => ha (hKs hm)
      have hsdiff_ins : insert a s \ K = insert a (s \ K) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨fun h => h.1.elim Or.inl (fun hxs => Or.inr ⟨hxs, h.2⟩),
          fun h => h.elim (fun hxa => ⟨Or.inl hxa, hxa ▸ haK⟩) (fun hx => ⟨Or.inr hx.1, hx.2⟩)⟩
      refine ⟨K, hKs.trans (Finset.subset_insert a s), hK_sum, ?_⟩
      rw [hsdiff_ins, Finset.sum_insert (fun hm => ha (Finset.sdiff_subset hm))]
      linarith only [hK_sdiff]

/-- Product-of-differences identity `∏ j ∈ T, (M j - Δ j) = ∑ S ∈ T.powerset, (∏ j ∈ S, M j) * (∏ j ∈ T \ S, (-Δ j))`. -/
lemma prod_sub_eq_sum_powerset {α : Type*} [DecidableEq α] (T : Finset α) (M Δ : α → ℂ) :
    (∏ j ∈ T, (M j - Δ j)) =
      ∑ S ∈ T.powerset, (∏ j ∈ S, M j) * (∏ j ∈ T \ S, (-Δ j)) := by
  have heq : (∏ j ∈ T, (M j - Δ j)) = ∏ j ∈ T, (M j + (-Δ j)) :=
    Finset.prod_congr rfl (fun _ _ => sub_eq_add_neg _ _)
  rw [heq, Finset.prod_add]

/-- Extending `dual_sixth_free_factored_energy` to:
1. `lists_sub j ⊆ lists_full j` missing at most `M_drop` primes per slot (`((lists_full j \ lists_sub j).card : ℝ) ≤ M_drop`), and
2. `∑ j ∈ T', D.ell j / d_outer ≤ z_T_cap + pad_T` (`0 ≤ z_T_cap`, `0 ≤ pad_T`). -/
theorem dual_sixth_free_factored_energy_lists_sdiff_padded
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {af bf B_w : ℝ} (haf : 0 < af) (habf : af ≤ bf) (hBw0 : 0 ≤ B_w)
    (hs_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    (M_drop : ℕ) :
    ∃ (τ_dual : ℝ) (J_sf : ℕ), 0 < τ_dual ∧ 2 * τ_dual ≤ D_dual.t ∧
      ∀ data : RowData, ∃ C_sfp U_sfp : ℝ, 0 < C_sfp ∧ 1 < U_sfp ∧
      ∀ U : ℝ, U_sfp ≤ U →
      ∀ (Dpool : ℕ),
      let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
        fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
      let base := InverseInitialRayAttachment.elementCharacter
        (InverseInitialConjugateEnergy.conjugateIdealCharacter
          (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r θ ell z_Jv x6 V₀ z_J z_coll pad_T X' : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r → r ≤ 19 / 26 →
        0 ≤ θ → θ ≤ 1 →
        0 ≤ ell → ell ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell →
        0 ≤ x6 → 0 ≤ V₀ → 0 ≤ z_J → 0 ≤ z_coll → 0 ≤ pad_T →
      let u_sel := θ * stage1Width r
      let H_th := (1 - θ) * 1 + θ * stage1DualScale r
      let z_rem_th := (1 - θ) * ((1 - r) / 2) + θ * stage1RemWidth r
      let H_free := H_th - 6 * ell - 6 * x6
      let r_unm := r - V₀ - 3 * ell + z_Jv - z_coll
      let z_T_cap := z_rem_th - z_Jv - z_J - z_coll
      0 ≤ z_T_cap →
      (-D_dual.t) ≤ H_free →
      0 < X' → X' ≤ U ^ r_unm →
      bf * X' ≤ (Dpool : ℝ) →
      ∀ (T' : Finset (Fin D.N)), (∑ j ∈ T', D.ell j / d_outer) ≤ z_T_cap + pad_T →
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      (∀ j ∈ T', 2 * Z_slot j ≤ (Dpool : ℝ)) →
      (∀ j ∈ T', ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full lists_sub : Fin D.N → Finset (primePool F_pool))
        (a : Fin D.N → primePool F_pool → ℂ),
      (∀ j ∈ T', lists_full j = InverseInitialCommonLists.poolList F_pool
        (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
      (∀ j ∈ T', lists_sub j ⊆ lists_full j) →
      (∀ j ∈ T', ((lists_full j \ lists_sub j).card : ℝ) ≤ (M_drop : ℝ)) →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 →
      (∀ j ∈ T', ∀ q ∈ lists_full j,
        a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val)) →
      let Z_dual := U ^ (3 / (2 * d_outer))
      ∀ (S_free : Finset FreeRow), (∀ u ∈ S_free, rowNorm u ≤ U ^ (max 0 H_free)) →
      ∀ s : ℝ,
        |(ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I).im| ≤ Z_dual ^ τ_dual →
      let a_tw : Fin D.N → primePool F_pool → ℂ := fun j q =>
        a j q * kernelLogPhase s (Real.log (‖ringComplex (poolPrimary F_pool q)‖ ^ 2 / Z_slot j))
      (∑ u ∈ S_free, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool)
            (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
            Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
            lists_sub a_tw base j u.val‖ ^ 2) ≤
        C_sfp * U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
  obtain ⟨τ_dual, J_sf, hτ_pos, hτ_le, hsf_all⟩ :=
    dual_sixth_free_factored_energy hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb F_dual
      wFresh haf habf hBw0 hs_w hBw
  refine ⟨τ_dual, J_sf, hτ_pos, hτ_le, ?_⟩
  intro data
  obtain ⟨C_sf, U_sf, hC_sf, hU_sf1, hsf⟩ := hsf_all data
  let C_drop : ℝ := ((max 1 (M_drop : ℝ)) ^ 2) ^ D.N
  let C_sfp : ℝ := (4 : ℝ) ^ D.N * C_drop * (9604 : ℝ) ^ D.N * C_sf
  have hC_sfp : 0 < C_sfp := by dsimp only [C_sfp, C_drop]; positivity
  refine ⟨C_sfp, U_sf, hC_sfp, hU_sf1, ?_⟩
  intro U hU Dpool q_per F_pool hFa base
    d_outer r θ ell z_Jv x6 V₀ z_J z_coll pad_T X'
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0 hpad0
    u_sel H_th z_rem_th H_free r_unm z_T_cap hzT_cap0 hHf_lo hX' hX'_le hDpool_X
    T' hzT_sum Z_slot hDpool_Z hlarge_Z lists_full lists_sub a hlists_full hlists_sub hcard_diff
    ζ_base hζ_re ha_eq Z_dual S_free hS_norm s hζ_tw_im a_tw
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  have hU1 : 1 < U := hU_sf1.trans_le hU
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hZ_pos : ∀ j : Fin D.N, 0 < Z_slot j := fun j => Real.rpow_pos_of_pos hU_pos _
  have hZ_ge1 : ∀ j : Fin D.N, 1 ≤ Z_slot j := fun j =>
    Real.one_le_rpow hU1.le (div_nonneg (D.slots_bounds j).1.le hd_pos.le)
  have hbase_norm : ∀ x, ‖base x‖ ≤ 1 := by
    intro x
    dsimp only [base]
    unfold InverseInitialRayAttachment.elementCharacter InverseInitialConjugateEnergy.conjugateIdealCharacter
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, norm_star]
    exact idealCoeff_norm_le_one (deletedBase data) _
  -- Step 1: Expand `lists_sub j = lists_full j \ (lists_full j \ lists_sub j)` over `T'' ⊆ T'`!
  have ha_tw_norm : ∀ j ∈ T', ∀ q ∈ lists_full j, ‖a_tw j q‖ ≤ 1 := by
    intro j hj q hq
    have hqL : q.val ∈ InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j) := by
      rw [hlists_full j hj] at hq
      exact (Finset.mem_filter.mp hq).2
    have hd_live := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot j) (hZ_pos j)
      ζ_base (by linarith only [hζ_re]) (hlarge_Z j hj) q.val hqL
    dsimp only [a_tw]
    rw [norm_mul, kernelLogPhase_norm, mul_one, ha_eq j hj q hq, norm_div, norm_star,
      ← norm_star (primeProfile _ _ _ _), ← norm_div]
    exact hd_live.2.2.2.2
  let χ_pool := fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j)
  let M_slot : FreeRow → Fin D.N → ℂ := fun u j =>
    slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists_full a_tw base j u.val
  let Δ_slot : FreeRow → Fin D.N → ℂ := fun u j =>
    slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
      (fun i => lists_full i \ lists_sub i) a_tw base j u.val
  have hslot_sub : ∀ u : FreeRow, ∀ j ∈ T',
      slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists_sub a_tw base j u.val =
        M_slot u j - Δ_slot u j := by
    intro u j hj
    dsimp only [M_slot, Δ_slot]
    unfold slotCharSum
    dsimp only
    rw [eq_sub_iff_add_eq, add_comm, Finset.sum_sdiff (hlists_sub j hj)]
  have hΔ_norm : ∀ u : FreeRow, ∀ j ∈ T', ‖-Δ_slot u j‖ ≤ max 1 (M_drop : ℝ) := by
    intro u j hj
    rw [norm_neg]
    dsimp only [Δ_slot]
    unfold slotCharSum
    calc ‖∑ q ∈ lists_full j \ lists_sub j,
            a_tw j q * base (poolPrimary F_pool q) * star (primeSubsetRow (poolPrimary F_pool) χ_pool {q} u.val)‖
        ≤ ∑ q ∈ lists_full j \ lists_sub j,
            ‖a_tw j q * base (poolPrimary F_pool q) * star (primeSubsetRow (poolPrimary F_pool) χ_pool {q} u.val)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _q ∈ lists_full j \ lists_sub j, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul, norm_mul, norm_star]
          have h1 := ha_tw_norm j hj q (Finset.sdiff_subset hq)
          have h2 := hbase_norm (poolPrimary F_pool q)
          have h3 := primeSubsetRow_norm_le_one (poolPrimary F_pool) χ_pool {q} u.val
          exact (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
      _ = ((lists_full j \ lists_sub j).card : ℝ) := by simp
      _ ≤ (M_drop : ℝ) := hcard_diff j hj
      _ ≤ max 1 (M_drop : ℝ) := le_max_right _ _
  -- Step 2: For any `T'' ⊆ T'`, bound the `lists_full` sum via `dual_factored_product_eq_dyadic` + greedy `T_keep ⊆ T''`!
  let w_slot : Fin D.N → ℝ := fun j => D.ell j / d_outer
  have hw0 : ∀ j ∈ T', 0 ≤ w_slot j := fun j _ => div_nonneg (D.slots_bounds j).1.le hd_pos.le
  have hmesh_le : ∀ j ∈ T', w_slot j ≤ D_dual.t := by
    intro j _
    dsimp only [w_slot]
    have hell_dual := (D_dual.slots_bounds (emb j)).2.2
    rw [hemb j] at hell_dual
    rw [div_le_iff₀ hd_pos]
    nlinarith only [hell_dual, hd_lo, D_dual.t_pos]
  have hT''_bound : ∀ T'' ∈ T'.powerset,
      (∑ u ∈ S_free, (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T'', M_slot u j‖ ^ 2) ≤
      (9604 : ℝ) ^ D.N * C_sf *
        U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
    intro T'' hT''_mem
    have hT''_sub : T'' ⊆ T' := Finset.mem_powerset.mp hT''_mem
    have hbf_supp : ∀ y, wFresh y ≠ 0 → y ≤ bf := fun y hy => (hs_w hy).2
    let ζ_tw : ℂ := ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I
    have hζ_tw_re : ζ_tw.re = 17 / 50 := by
      dsimp only [ζ_tw]; simp [hζ_re]
    have hdyad_eq : ∀ u ∈ S_free,
        (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
          ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
              (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
            ∏ j ∈ T'', M_slot u j‖ ^ 2 =
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T'', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
      intro u _
      exact dual_factored_product_eq_dyadic F_dual data Dpool wFresh hbf_supp s hX' hDpool_X
        T'' Z_slot (fun j _ => hZ_pos j) (fun j hj => hDpool_Z j (hT''_sub hj))
        (fun j hj => hlarge_Z j (hT''_sub hj)) ζ_base (by linarith only [hζ_re])
        lists_full a (fun j hj => hlists_full j (hT''_sub hj))
        (fun j hj => ha_eq j (hT''_sub hj)) u
    rw [Finset.sum_congr rfl hdyad_eq]
    have hT''_sum : (∑ j ∈ T'', w_slot j) ≤ z_T_cap + pad_T :=
      (Finset.sum_le_sum_of_subset_of_nonneg hT''_sub (fun j hj _ => hw0 j hj)).trans hzT_sum
    obtain ⟨T_keep, hTk_sub, hTk_sum, hTk_sdiff⟩ :=
      exists_subset_sum_le_and_sdiff_le T'' w_slot D_dual.t_pos.le
        (fun j hj => hw0 j (hT''_sub hj)) (fun j hj => hmesh_le j (hT''_sub hj))
        hzT_cap0 hpad0 hT''_sum
    have hFW_norm : ∀ x, ‖F_dual.W x‖ ≤ 1 := by
      intro x; rw [F_dual.complex_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (F_dual.bounded x).1]
      exact (F_dual.bounded x).2
    have hpeel_pt : ∀ u ∈ S_free,
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T'', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 ≤
        ((9604 : ℝ) ^ D.N * U ^ (pad_T + D_dual.t)) *
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
      intro u _
      have hunion : T_keep ∪ (T'' \ T_keep) = T'' := Finset.union_sdiff_of_subset hTk_sub
      have hdisj : Disjoint T_keep (T'' \ T_keep) := Finset.disjoint_sdiff
      conv_lhs => rw [← hunion, Finset.prod_union hdisj, ← mul_assoc]
      rw [norm_mul, mul_pow]
      rw [mul_comm ((9604 : ℝ) ^ D.N * U ^ (pad_T + D_dual.t))]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [norm_prod, ← Finset.prod_pow]
      have hcard_sd : (T'' \ T_keep).card ≤ D.N :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin D.N)
      calc (∏ j ∈ T'' \ T_keep,
              ‖HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2)
          ≤ ∏ j ∈ T'' \ T_keep, (9604 * Z_slot j) :=
            Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ =>
              canonicalPrimeAmplitude_norm_sq_le_trivial F_dual.modulus ⊤ F_dual.W
                F_dual.complex_support hFW_norm (hZ_ge1 j) (by linarith only [hζ_tw_re]) u.val)
        _ = (9604 : ℝ) ^ (T'' \ T_keep).card * ∏ j ∈ T'' \ T_keep, Z_slot j := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ (9604 : ℝ) ^ D.N * U ^ (pad_T + D_dual.t) := by
            apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard_sd) _
              (Finset.prod_nonneg (fun j _ => (hZ_pos j).le)) (by positivity)
            dsimp only [Z_slot]
            rw [← Real.rpow_sum_of_pos hU_pos]
            exact Real.rpow_le_rpow_of_exponent_le hU1.le hTk_sdiff
    have hsf_keep := hsf U hU hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0
      hHf_lo hX' hX'_le T_keep hTk_sum S_free hS_norm ζ_tw hζ_tw_re hζ_tw_im s
    calc (∑ u ∈ S_free,
            ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                (childLogTest wFresh s) X' 0 0 *
              ∏ j ∈ T'', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2)
        ≤ ((9604 : ℝ) ^ D.N * U ^ (pad_T + D_dual.t)) *
            ∑ u ∈ S_free,
              ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
                  (childLogTest wFresh s) X' 0 0 *
                ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
                  F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_le_sum hpeel_pt
      _ ≤ ((9604 : ℝ) ^ D.N * U ^ (pad_T + D_dual.t)) *
            (C_sf * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t) * (1 + |s|) ^ (2 * J_sf)) :=
            mul_le_mul_of_nonneg_left hsf_keep (by positivity)
      _ = (9604 : ℝ) ^ D.N * C_sf *
            (U ^ (pad_T + D_dual.t) * U ^ (1 - 3 * ell - 5 * u_sel - x6 + 6 * D_dual.t)) *
            (1 + |s|) ^ (2 * J_sf) := by ring
      _ = _ := by
            rw [← Real.rpow_add hU_pos]
            congr 2; congr 1; ring
  -- Step 3: Pointwise Cauchy-Schwarz over `T'' ∈ T'.powerset` and sum-swap with `u ∈ S_free`!
  have hcard_T' : T'.card ≤ D.N := (Finset.card_le_univ T').trans_eq (Fintype.card_fin D.N)
  have hcard_pow : (T'.powerset.card : ℝ) ≤ (2 : ℝ) ^ D.N := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hcard_T'
  have hpt_u : ∀ u ∈ S_free,
      (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
            lists_sub a_tw base j u.val‖ ^ 2 ≤
      (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
        (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
          ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
              (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
            ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
    intro u _
    let A_pol := inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
      (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val
    have hprod_eq : (∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
        lists_sub a_tw base j u.val) =
        ∑ T'' ∈ T'.powerset, (∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)) := by
      rw [Finset.prod_congr rfl (hslot_sub u), prod_sub_eq_sum_powerset]
    change (X' * ∏ j ∈ T', Z_slot j)⁻¹ * ‖A_pol * _‖ ^ 2 ≤ _
    rw [hprod_eq, Finset.mul_sum]
    have hcs := norm_sum_sq_le_card_sum_norm_sq T'.powerset
      (fun T'' => A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j))))
    have hXprod_inv_nn : 0 ≤ (X' * ∏ j ∈ T', Z_slot j)⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hX'.le (Finset.prod_nonneg (fun j _ => (hZ_pos j).le)))
    calc (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖∑ T'' ∈ T'.powerset, A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)))‖ ^ 2
        ≤ (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ((T'.powerset.card : ℝ) * ∑ T'' ∈ T'.powerset,
              ‖A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hXprod_inv_nn
      _ ≤ (2 : ℝ) ^ D.N * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
              ‖(A_pol * ∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j))‖ ^ 2 := by
          rw [mul_left_comm, Finset.mul_sum]
          apply mul_le_mul hcard_pow _ (Finset.sum_nonneg (fun _ _ => mul_nonneg hXprod_inv_nn (sq_nonneg _)))
            (by positivity)
          apply Finset.sum_le_sum
          intro T'' _; rw [mul_assoc]
      _ ≤ (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro T'' hT''
          have hT''_sub : T'' ⊆ T' := Finset.mem_powerset.mp hT''
          have hunion : T'' ∪ (T' \ T'') = T' := Finset.union_sdiff_of_subset hT''_sub
          have hdisj : Disjoint T'' (T' \ T'') := Finset.disjoint_sdiff
          have hZ_split : (X' * ∏ j ∈ T', Z_slot j)⁻¹ =
              (X' * ∏ j ∈ T'', Z_slot j)⁻¹ * (∏ j ∈ T' \ T'', Z_slot j)⁻¹ := by
            conv_lhs => rw [← hunion, Finset.prod_union hdisj, ← mul_assoc, mul_inv]
          have hZ_sd_inv1 : (∏ j ∈ T' \ T'', Z_slot j)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (Finset.one_le_prod (fun j _ => hZ_ge1 j))
          have hΔ_prod_le : ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2 ≤ C_drop := by
            rw [norm_prod, ← Finset.prod_pow]
            have hc_sd : (T' \ T'').card ≤ D.N :=
              (Finset.card_le_univ _).trans_eq (Fintype.card_fin D.N)
            calc (∏ j ∈ T' \ T'', ‖-Δ_slot u j‖ ^ 2)
                ≤ ∏ _j ∈ T' \ T'', (max 1 (M_drop : ℝ)) ^ 2 :=
                  Finset.prod_le_prod (fun _ _ => sq_nonneg _)
                    (fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hΔ_norm u j (Finset.sdiff_subset hj)) 2)
              _ = ((max 1 (M_drop : ℝ)) ^ 2) ^ (T' \ T'').card := by rw [Finset.prod_const]
              _ ≤ C_drop := pow_le_pow_right₀ (one_le_pow₀ (le_max_left 1 _)) hc_sd
          rw [hZ_split, norm_mul, mul_pow]
          calc ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * (∏ j ∈ T' \ T'', Z_slot j)⁻¹) *
                  (‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2 * ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2)
              = ((∏ j ∈ T' \ T'', Z_slot j)⁻¹ * ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2) *
                  ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by ring
            _ ≤ (1 * C_drop) *
                  ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by
                  apply mul_le_mul (mul_le_mul hZ_sd_inv1 hΔ_prod_le (sq_nonneg _) zero_le_one) le_rfl
                    (mul_nonneg (inv_nonneg.mpr (mul_nonneg hX'.le
                      (Finset.prod_nonneg (fun j _ => (hZ_pos j).le)))) (sq_nonneg _))
                    (by dsimp only [C_drop]; positivity)
            _ = C_drop * ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by ring
  calc _ ≤ ∑ u ∈ S_free, (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
              ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
                  (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
                ∏ j ∈ T'', M_slot u j‖ ^ 2 := Finset.sum_le_sum hpt_u
    _ = (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset, ∑ u ∈ S_free,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
              ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
                  (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
                ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (2 : ℝ) ^ D.N * C_drop * ∑ _T'' ∈ T'.powerset,
            ((9604 : ℝ) ^ D.N * C_sf *
              U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hT''_bound) (by dsimp only [C_drop]; positivity)
    _ ≤ (2 : ℝ) ^ D.N * C_drop * ((2 : ℝ) ^ D.N *
            ((9604 : ℝ) ^ D.N * C_sf *
              U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_left _ (by dsimp only [C_drop]; positivity)
          exact mul_le_mul_of_nonneg_right hcard_pow (by positivity)
    _ = C_sfp * U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
          dsimp only [C_sfp]
          rw [show (4 : ℝ) ^ D.N = (2 : ℝ) ^ D.N * (2 : ℝ) ^ D.N by rw [← mul_pow]; norm_num]
          ring

/-- Coarse `s`-uniform `L^2` bound for `lists_sub j ⊆ lists_full j` missing at most `M_drop` primes
per slot, pairing `dual_factored_product_eq_dyadic` and `dual_factored_coarse_bound` over `T'' ⊆ T'`. -/
theorem dual_factored_coarse_bound_lists_sdiff
    {Δ : ℝ} {D D_dual : Parameters.HighData Δ} (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (wFresh : 𝓢(ℝ, ℂ)) {bf B_w : ℝ} (hbf0 : 0 < bf) (hBw0 : 0 ≤ B_w)
    (hbf : ∀ y, wFresh y ≠ 0 → y ≤ bf) (hBw : ∀ y, ‖wFresh y‖ ≤ B_w)
    (M_drop : ℕ) (data : RowData) (Dpool : ℕ)
    {U X' : ℝ} (hU1 : 1 ≤ U) (hX' : 0 < X') (hX'_hi : X' ≤ U ^ (2 : ℝ)) (hDpool_X : bf * X' ≤ (Dpool : ℝ))
    (T' : Finset (Fin D.N))
    (Z_slot : Fin D.N → ℝ) (hZ1 : ∀ j ∈ T', 1 ≤ Z_slot j) (hZ_hi : ∀ j ∈ T', Z_slot j ≤ U)
    (hDpool_Z : ∀ j ∈ T', 2 * Z_slot j ≤ (Dpool : ℝ))
    (hlarge_Z : ∀ j ∈ T', ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j)
    (ζ_base : ℂ) (hζ_re : ζ_base.re ≤ 1)
    (lists_full lists_sub : Fin D.N → Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)))
    (a : Fin D.N → primePool (CanonicalRowCompletion.outsideSquarefreeIdeals
      (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool) → ℂ)
    (hlists_full : ∀ j ∈ T', lists_full j = InverseInitialCommonLists.poolList
      (CanonicalRowCompletion.outsideSquarefreeIdeals
        (reflectionExcludedPrimes (InverseInitialExcludedPeriod.deletedPeriod (basePeriod data))) Dpool)
      (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j)))
    (hlists_sub : ∀ j ∈ T', lists_sub j ⊆ lists_full j)
    (hcard_diff : ∀ j ∈ T', ((lists_full j \ lists_sub j).card : ℝ) ≤ (M_drop : ℝ))
    (ha_eq : ∀ j ∈ T', ∀ q ∈ lists_full j,
      a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val / star (idealCoeff (deletedBase data) q.val))
    (S_free : Finset FreeRow) (hS_norm : ∀ u ∈ S_free, rowNorm u ≤ U ^ (2 : ℝ))
    (s : ℝ) :
    let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
    let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
    let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
      (reflectionExcludedPrimes_bad q_per)
    letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
      fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
    let base := InverseInitialRayAttachment.elementCharacter
      (InverseInitialConjugateEnergy.conjugateIdealCharacter
        (idealCoeff (deletedBase data)).toMonoidHom)
    let a_tw : Fin D.N → primePool F_pool → ℂ := fun j q =>
      a j q * kernelLogPhase s (Real.log (‖ringComplex (poolPrimary F_pool q)‖ ^ 2 / Z_slot j))
    (∑ u ∈ S_free, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
      ‖inputConjugateRow (poolPrimary F_pool)
          (fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j))
          Finset.univ base 1 1 1
          (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
        ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
          lists_sub a_tw base j u.val‖ ^ 2) ≤
      (4 : ℝ) ^ D.N * ((max 1 (M_drop : ℝ)) ^ 2) ^ D.N *
        (49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ D.N + 1) *
        U ^ ((D.N : ℝ) + 10) := by
  intro q_per F_pool hFa base a_tw
  letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
    fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
  let C_drop : ℝ := ((max 1 (M_drop : ℝ)) ^ 2) ^ D.N
  let C_c0 : ℝ := 49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ D.N + 1
  have hZ_pos : ∀ j ∈ T', 0 < Z_slot j := fun j hj => zero_lt_one.trans_le (hZ1 j hj)
  have hbase_norm : ∀ x, ‖base x‖ ≤ 1 := by
    intro x; dsimp only [base]
    unfold InverseInitialRayAttachment.elementCharacter InverseInitialConjugateEnergy.conjugateIdealCharacter
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, norm_star]
    exact idealCoeff_norm_le_one (deletedBase data) _
  have ha_tw_norm : ∀ j ∈ T', ∀ q ∈ lists_full j, ‖a_tw j q‖ ≤ 1 := by
    intro j hj q hq
    have hqL : q.val ∈ InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j) := by
      rw [hlists_full j hj] at hq; exact (mem_filter_of hq).2
    have hd_live := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot j) (hZ_pos j hj)
      ζ_base hζ_re (hlarge_Z j hj) q.val hqL
    dsimp only [a_tw]
    rw [norm_mul, kernelLogPhase_norm, mul_one, ha_eq j hj q hq, norm_div, norm_star,
      ← norm_star (primeProfile _ _ _ _), ← norm_div]
    exact hd_live.2.2.2.2
  let χ_pool := fun j => complexSexticChar (Ideal.span {poolPrimary F_pool j}) (poolPrimary_good F_pool hFa j)
  let M_slot : FreeRow → Fin D.N → ℂ := fun u j =>
    slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists_full a_tw base j u.val
  let Δ_slot : FreeRow → Fin D.N → ℂ := fun u j =>
    slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
      (fun i => lists_full i \ lists_sub i) a_tw base j u.val
  have hslot_sub : ∀ u : FreeRow, ∀ j ∈ T',
      slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa) lists_sub a_tw base j u.val =
        M_slot u j - Δ_slot u j := by
    intro u j hj; dsimp only [M_slot, Δ_slot]; unfold slotCharSum; dsimp only
    rw [eq_sub_iff_add_eq, add_comm, Finset.sum_sdiff (hlists_sub j hj)]
  have hΔ_norm : ∀ u : FreeRow, ∀ j ∈ T', ‖-Δ_slot u j‖ ≤ max 1 (M_drop : ℝ) := by
    intro u j hj; rw [norm_neg]; dsimp only [Δ_slot]; unfold slotCharSum
    calc _ ≤ ∑ q ∈ lists_full j \ lists_sub j,
            ‖a_tw j q * base (poolPrimary F_pool q) * star (primeSubsetRow (poolPrimary F_pool) χ_pool {q} u.val)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _q ∈ lists_full j \ lists_sub j, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro q hq
          rw [norm_mul, norm_mul, norm_star]
          have h1 := ha_tw_norm j hj q (Finset.sdiff_subset hq)
          have h2 := hbase_norm (poolPrimary F_pool q)
          have h3 := primeSubsetRow_norm_le_one (poolPrimary F_pool) χ_pool {q} u.val
          exact (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
      _ = ((lists_full j \ lists_sub j).card : ℝ) := by simp
      _ ≤ max 1 (M_drop : ℝ) := (hcard_diff j hj).trans (le_max_right _ _)
  have hcard_T' : T'.card ≤ D.N := (Finset.card_le_univ T').trans_eq (Fintype.card_fin D.N)
  have hcard_pow : (T'.powerset.card : ℝ) ≤ (2 : ℝ) ^ D.N := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hcard_T'
  have hT''_coarse : ∀ T'' ∈ T'.powerset,
      (∑ u ∈ S_free, (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T'', M_slot u j‖ ^ 2) ≤ C_c0 * U ^ ((D.N : ℝ) + 10) := by
    intro T'' hT''_mem
    have hT''_sub : T'' ⊆ T' := Finset.mem_powerset.mp hT''_mem
    let ζ_tw : ℂ := ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I
    have hζ_tw_re : ζ_tw.re ≤ 1 := by dsimp only [ζ_tw]; simp [hζ_re]
    have hdyad_eq : ∀ u ∈ S_free,
        (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
          ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
              (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
            ∏ j ∈ T'', M_slot u j‖ ^ 2 =
        ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
            (childLogTest wFresh s) X' 0 0 *
          ∏ j ∈ T'', HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
            F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
      intro u _
      exact dual_factored_product_eq_dyadic F_dual data Dpool wFresh hbf s hX' hDpool_X
        T'' Z_slot (fun j hj => hZ_pos j (hT''_sub hj)) (fun j hj => hDpool_Z j (hT''_sub hj))
        (fun j hj => hlarge_Z j (hT''_sub hj)) ζ_base hζ_re lists_full a
        (fun j hj => hlists_full j (hT''_sub hj)) (fun j hj => ha_eq j (hT''_sub hj)) u
    rw [Finset.sum_congr rfl hdyad_eq]
    exact dual_factored_coarse_bound F_dual wFresh hbf0 hBw0 hbf hBw D.N data hU1 hX' hX'_hi
      T'' ((Finset.card_le_card hT''_sub).trans hcard_T') Z_slot
      (fun j hj => hZ1 j (hT''_sub hj)) (fun j hj => hZ_hi j (hT''_sub hj))
      ζ_tw hζ_tw_re S_free hS_norm s
  have hpt_u : ∀ u ∈ S_free,
      (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
            lists_sub a_tw base j u.val‖ ^ 2 ≤
      (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
        (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
          ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
              (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
            ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
    intro u _
    let A_pol := inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
      (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val
    have hprod_eq : (∏ j ∈ T', slotCharSum (poolPrimary F_pool) (poolPrimary_good F_pool hFa)
        lists_sub a_tw base j u.val) =
        ∑ T'' ∈ T'.powerset, (∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)) := by
      rw [Finset.prod_congr rfl (hslot_sub u), prod_sub_eq_sum_powerset]
    change (X' * ∏ j ∈ T', Z_slot j)⁻¹ * ‖A_pol * _‖ ^ 2 ≤ _
    rw [hprod_eq, Finset.mul_sum]
    have hcs := norm_sum_sq_le_card_sum_norm_sq T'.powerset
      (fun T'' => A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j))))
    have hXprod_inv_nn : 0 ≤ (X' * ∏ j ∈ T', Z_slot j)⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hX'.le (Finset.prod_nonneg (fun j hj => (hZ_pos j hj).le)))
    calc (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖∑ T'' ∈ T'.powerset, A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)))‖ ^ 2
        ≤ (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ((T'.powerset.card : ℝ) * ∑ T'' ∈ T'.powerset,
              ‖A_pol * ((∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j)))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hXprod_inv_nn
      _ ≤ (2 : ℝ) ^ D.N * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
              ‖(A_pol * ∏ j ∈ T'', M_slot u j) * (∏ j ∈ T' \ T'', (-Δ_slot u j))‖ ^ 2 := by
          rw [mul_left_comm, Finset.mul_sum]
          apply mul_le_mul hcard_pow _ (Finset.sum_nonneg (fun _ _ => mul_nonneg hXprod_inv_nn (sq_nonneg _)))
            (by positivity)
          apply Finset.sum_le_sum; intro T'' _; rw [mul_assoc]
      _ ≤ (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro T'' hT''
          have hT''_sub : T'' ⊆ T' := Finset.mem_powerset.mp hT''
          have hunion : T'' ∪ (T' \ T'') = T' := Finset.union_sdiff_of_subset hT''_sub
          have hdisj : Disjoint T'' (T' \ T'') := Finset.disjoint_sdiff
          have hZ_split : (X' * ∏ j ∈ T', Z_slot j)⁻¹ =
              (X' * ∏ j ∈ T'', Z_slot j)⁻¹ * (∏ j ∈ T' \ T'', Z_slot j)⁻¹ := by
            conv_lhs => rw [← hunion, Finset.prod_union hdisj, ← mul_assoc, mul_inv]
          have hZ_sd_inv1 : (∏ j ∈ T' \ T'', Z_slot j)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (Finset.one_le_prod (fun j hj => hZ1 j (Finset.sdiff_subset hj)))
          have hΔ_prod_le : ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2 ≤ C_drop := by
            rw [norm_prod, ← Finset.prod_pow]
            have hc_sd : (T' \ T'').card ≤ D.N :=
              (Finset.card_le_univ _).trans_eq (Fintype.card_fin D.N)
            calc (∏ j ∈ T' \ T'', ‖-Δ_slot u j‖ ^ 2)
                ≤ ∏ _j ∈ T' \ T'', (max 1 (M_drop : ℝ)) ^ 2 :=
                  Finset.prod_le_prod (fun _ _ => sq_nonneg _)
                    (fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hΔ_norm u j (Finset.sdiff_subset hj)) 2)
              _ = ((max 1 (M_drop : ℝ)) ^ 2) ^ (T' \ T'').card := by rw [Finset.prod_const]
              _ ≤ C_drop := pow_le_pow_right₀ (one_le_pow₀ (le_max_left 1 _)) hc_sd
          rw [hZ_split, norm_mul, mul_pow]
          calc ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * (∏ j ∈ T' \ T'', Z_slot j)⁻¹) *
                  (‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2 * ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2)
              = ((∏ j ∈ T' \ T'', Z_slot j)⁻¹ * ‖∏ j ∈ T' \ T'', (-Δ_slot u j)‖ ^ 2) *
                  ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by ring
            _ ≤ (1 * C_drop) *
                  ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by
                  apply mul_le_mul (mul_le_mul hZ_sd_inv1 hΔ_prod_le (sq_nonneg _) zero_le_one) le_rfl
                    (mul_nonneg (inv_nonneg.mpr (mul_nonneg hX'.le
                      (Finset.prod_nonneg (fun j hj => (hZ_pos j (hT''_sub hj)).le)))) (sq_nonneg _))
                    (by dsimp only [C_drop]; positivity)
            _ = C_drop * ((X' * ∏ j ∈ T'', Z_slot j)⁻¹ * ‖A_pol * ∏ j ∈ T'', M_slot u j‖ ^ 2) := by ring
  calc _ ≤ ∑ u ∈ S_free, (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
              ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
                  (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
                ∏ j ∈ T'', M_slot u j‖ ^ 2 := Finset.sum_le_sum hpt_u
    _ = (2 : ℝ) ^ D.N * C_drop * ∑ T'' ∈ T'.powerset, ∑ u ∈ S_free,
            (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
              ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
                  (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
                ∏ j ∈ T'', M_slot u j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (2 : ℝ) ^ D.N * C_drop * ∑ _T'' ∈ T'.powerset, (C_c0 * U ^ ((D.N : ℝ) + 10)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hT''_coarse) (by dsimp only [C_drop]; positivity)
    _ ≤ (2 : ℝ) ^ D.N * C_drop * ((2 : ℝ) ^ D.N * (C_c0 * U ^ ((D.N : ℝ) + 10))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_left _ (by dsimp only [C_drop]; positivity)
          exact mul_le_mul_of_nonneg_right hcard_pow (by dsimp only [C_c0]; positivity)
    _ = _ := by
          dsimp only [C_drop, C_c0]
          rw [show (4 : ℝ) ^ D.N = (2 : ℝ) ^ D.N * (2 : ℝ) ^ D.N by rw [← mul_pow]; norm_num]
          ring

/-! ### Part II: Uniform `principalWindow` Fourier log-separation -/

/-- Uniform `(negative, t)`-independent `wFresh` Fourier log-separation on `markedRadial` for
`principalWindow om a₀ b₀ ha₀ hs negative t`, with polynomial `(1 + ‖t‖)` growth via
`frequencyTwist_fourier_moment`. -/
theorem principalWindow_markedRadial_fourier_l2_le_factored
    (om : 𝓢(ℝ, ℂ)) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hs : Function.support (om : ℝ → ℂ) ⊆ Set.Icc a₀ b₀) (K : ℕ) :
    ∃ (wFresh : 𝓢(ℝ, ℂ)) (af bf B_w : ℝ),
      0 < af ∧ af ≤ bf ∧ 0 ≤ B_w ∧
      Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf ∧
      (∀ x, ‖wFresh x‖ ≤ B_w) ∧
      ∀ (deg N_tail : ℕ), ∃ C_four : ℝ, 0 < C_four ∧
      ∀ (negative : Bool) (t : ℝ)
        {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
        (p : ι → O), (∀ i, p i ≠ 0) → ∀ [∀ i, (Ideal.span {p i}).IsMaximal],
        Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})) →
        ∀ (hg : ∀ i, lambda ∉ Ideal.span {p i}), Function.Injective p →
        ∀ (pool : Finset ι) (Ψ₀ : O →* ℂ), (∀ u, ‖Ψ₀ u‖ ≤ 1) →
        ∀ (S_rem : Finset σ), S_rem.card ≤ K →
        ∀ (lists : σ → Finset ι), (∀ i ∈ S_rem, lists i ⊆ pool) →
        (S_rem : Set σ).PairwiseDisjoint lists →
        ∀ (a : σ → ι → ℂ), (∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a i q‖ ≤ 1) →
        ∀ (Z_slot : σ → ℝ), (∀ i ∈ S_rem, 1 ≤ Z_slot i) →
        (∀ i ∈ S_rem, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2) →
        (∀ i ∈ S_rem, ∀ q ∈ lists i, ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot i) →
        ∀ (S_w : Finset O) {X S_cut B_low B_triv : ℝ},
        0 < X → 0 ≤ S_cut → 0 ≤ B_low → 0 ≤ B_triv →
        let X₀ := X / ∏ i ∈ S_rem, Z_slot i
        let a_tw : ℝ → σ → ι → ℂ := fun s i q =>
          a i q * kernelLogPhase s (Real.log (‖ringComplex (p q)‖ ^ 2 / Z_slot i))
        (∀ s : ℝ, |s| ≤ S_cut → ∀ T' : Finset σ, T' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
          X' ≤ X₀ / (∏ i ∈ S_rem \ T', Z_slot i) →
          (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
                pool Ψ₀ 1 1 1 (fun U => childLogTest wFresh s (primeProductNorm p U / X')) w *
              ∏ j ∈ T', slotCharSum p hg lists (a_tw s) Ψ₀ j w‖ ^ 2) ≤
            B_low * (1 + |s|) ^ (2 * deg)) →
        (∀ s : ℝ, ∀ T' : Finset σ, T' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
          X' ≤ X₀ / (∏ i ∈ S_rem \ T', Z_slot i) →
          (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
            ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
                pool Ψ₀ 1 1 1 (fun U => childLogTest wFresh s (primeProductNorm p U / X')) w *
              ∏ j ∈ T', slotCharSum p hg lists (a_tw s) Ψ₀ j w‖ ^ 2) ≤ B_triv) →
        (∑ w ∈ S_w, X⁻¹ *
          ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            pool Ψ₀ 1 1 1
            (markedRadial p S_rem lists a ∅ (principalWindow om a₀ b₀ ha₀ hs negative t) X) w‖ ^ 2) ≤
          C_four * (1 + ‖t‖) ^ (2 * (deg + N_tail + (volume : Measure ℝ).integrablePower)) *
            (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) := by
  obtain ⟨wFresh, af, bf, B_w, haf, habf, hBw, _, htsup, hBw_norm, hFresh⟩ :=
    InverseInitialUniformFresh.exists_uniform_fresh K a₀ b₀ ha₀ hab₀
  have hsup_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf :=
    (subset_tsupport (wFresh : ℝ → ℂ)).trans htsup
  refine ⟨wFresh, af, bf, B_w, haf, habf, hBw, hsup_w, hBw_norm, ?_⟩
  intro deg N_tail
  let J_tot : ℕ := deg + N_tail
  let g_pos : 𝓢(ℝ, ℂ) := kernelLogSource (om : ℝ → ℂ) a₀ b₀ ha₀ hs (om.smooth ⊤)
  let g_neg : 𝓢(ℝ, ℂ) := conjugateProfile g_pos
  obtain ⟨C_pos, hC_pos, hft_pos⟩ := frequencyTwist_fourier_moment J_tot g_pos
  obtain ⟨C_neg, hC_neg, hft_neg⟩ := frequencyTwist_fourier_moment J_tot g_neg
  let C_ft : ℝ := C_pos + C_neg + 1
  let C_four : ℝ := C_ft ^ 2 * (307330 : ℝ) ^ K
  refine ⟨C_four, by dsimp only [C_four, C_ft]; positivity, ?_⟩
  intro negative t ι σ _ _ p hp _ hcop hg hinj_p pool Ψ₀ hΨ1 S_rem hK lists hlists_pool hdisj
    a ha Z_slot hZ1 hZ_lo hZ_hi S_w X S_cut B_low B_triv hX hS_cut hB_low hB_triv
    X₀ a_tw hlow htriv
  let V : 𝓢(ℝ, ℂ) := principalWindow om a₀ b₀ ha₀ hs negative t
  have hsV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a₀ b₀ := by
    rw [principalWindow_support]; exact hs
  let g : 𝓢(ℝ, ℂ) := if negative then frequencyTwist g_neg (-t) else frequencyTwist g_pos t
  have hg_apply : ∀ u : ℝ, g u = V (Real.exp u) := by
    intro u
    dsimp only [g, V]
    rw [principalWindow_apply]
    cases negative
    · simp only [Bool.false_eq_true, ite_false, frequencyTwist_apply, g_pos,
        kernelLogSource_apply, normTwistedSource, Real.log_exp]
    · simp only [ite_true, frequencyTwist_apply, g_neg, conjugateProfile_apply,
        normTwistedSource, Real.log_exp]
      rw [kernelLogSource_apply]
  have hint_wt : Integrable (fun s : ℝ => (1 + ‖s‖) ^ J_tot * ‖(𝓕 g) s‖) :=
    CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g) J_tot
  let I_wt : ℝ := ∫ s : ℝ, (1 + ‖s‖) ^ J_tot * ‖(𝓕 g) s‖
  have hI_wt_nn : 0 ≤ I_wt := integral_nonneg (fun _ => by positivity)
  have hI_wt_le : I_wt ≤ C_ft * (1 + ‖t‖) ^ (J_tot + (volume : Measure ℝ).integrablePower) := by
    dsimp only [I_wt, g]
    cases negative
    · simp only [Bool.false_eq_true, ite_false]
      exact (hft_pos t).trans (mul_le_mul_of_nonneg_right
        (by dsimp only [C_ft]; linarith only [hC_neg]) (by positivity))
    · simp only [ite_true]
      have hh := hft_neg (-t)
      rw [norm_neg] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (by dsimp only [C_ft]; linarith only [hC_pos]) (by positivity))
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  have hZprod_pos : 0 < ∏ i ∈ S_rem, Z_slot i :=
    Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i hi))
  have hX₀_pos : 0 < X₀ := div_pos hX hZprod_pos
  have hX_eq : X₀ * ∏ i ∈ S_rem, Z_slot i = X := div_mul_cancel₀ X hZprod_pos.ne'
  have hfour_pt (w : O) :
      inputConjugateRow p χ pool Ψ₀ 1 1 1
        (markedRadial p S_rem lists a ∅ V X) w =
      ∫ s : ℝ, (𝓕 g) s *
        disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w := by
    have hmr_eq : markedRadial p S_rem lists a ∅ V X =
        (fun S => InverseMoment.primeMark S_rem lists a S * V (primeProductNorm p S / X)) := by
      funext S; simp [markedRadial]
    rw [hmr_eq, inputConjugateRow_markedRadial_eq_tuple_sum p hg pool Ψ₀ 1 S_rem lists hlists_pool
      hdisj a V X w]
    have htup_int (tup : ∀ i : S_rem, lists i.val) :
        ((tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            primeCoprimeMask p (tuplePrimeSet tup) 1 *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
            (fun U => V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X)) w) =
        ∫ s : ℝ, (𝓕 g) s *
          ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
            inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
              (fun U => childLogTest wFresh s (primeProductNorm p U / X₀)) w) := by
      have hmask1 : primeCoprimeMask p (tuplePrimeSet tup) 1 = 1 := by
        rw [primeCoprimeMask_indicator, if_pos]
        intro j _ hdvd
        exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top
          (Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hdvd))
      rw [hmask1, mul_one]
      have hnorm_tup : primeProductNorm p (tuplePrimeSet tup) =
          ∏ i : S_rem, ‖ringComplex (p (tup i).val)‖ ^ 2 := by
        unfold primeProductNorm tuplePrimeSet
        rw [map_prod, norm_prod, Finset.prod_pow, Finset.prod_image (fun i₁ _ i₂ _ he => by
          by_contra hne
          exact Finset.disjoint_left.mp (hdisj i₁.property i₂.property (fun hv => hne (Subtype.ext hv)))
            (tup i₁).property (he ▸ (tup i₂).property))]
      let rat : S_rem → ℝ := fun i => ‖ringComplex (p (tup i).val)‖ ^ 2 / Z_slot i.val
      have hrat_bounds (i : S_rem) : rat i ∈ Set.Icc (1 : ℝ) 2 := by
        have hZi := zero_lt_one.trans_le (hZ1 i.val i.property)
        exact ⟨(one_le_div hZi).mpr (hZ_lo i.val i.property (tup i).val (tup i).property),
          (div_le_iff₀ hZi).mpr (hZ_hi i.val i.property (tup i).val (tup i).property)⟩
      let yj : ℝ := ∏ i : S_rem, rat i
      have hyj_pos : 0 < yj := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hrat_bounds i).1)
      have hyj_Icc : yj ∈ Set.Icc (1 : ℝ) ((2 : ℝ) ^ K) := by
        refine ⟨Finset.one_le_prod (fun i _ => (hrat_bounds i).1), ?_⟩
        calc (∏ i : S_rem, rat i)
            ≤ ∏ _i : S_rem, (2 : ℝ) := Finset.prod_le_prod (fun i _ => zero_le_one.trans (hrat_bounds i).1)
              (fun i _ => (hrat_bounds i).2)
          _ = (2 : ℝ) ^ S_rem.card := by simp
          _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hK
      have hyj_eq : primeProductNorm p (tuplePrimeSet tup) = yj * ∏ i ∈ S_rem, Z_slot i := by
        rw [hnorm_tup]; dsimp only [yj, rat]
        rw [Finset.prod_div_distrib, ← Finset.prod_coe_sort S_rem Z_slot]
        have hZp' : (∏ i : S_rem, Z_slot i.val) ≠ 0 := by
          rw [Finset.prod_coe_sort S_rem Z_slot]; exact hZprod_pos.ne'
        exact (div_mul_cancel₀ _ hZp').symm
      have hphase_tup (s : ℝ) :
          tupleCoeff (a_tw s) tup = tupleCoeff a tup * kernelLogPhase s (Real.log yj) := by
        unfold tupleCoeff; dsimp only [a_tw]; rw [Finset.prod_mul_distrib]; congr 1
        rw [Real.log_prod (fun i _ => (zero_lt_one.trans_le (hrat_bounds i).1).ne')]
        have hkp : ∀ (S_f : Finset S_rem),
            (∏ i ∈ S_f, kernelLogPhase s (Real.log (rat i))) =
              kernelLogPhase s (∑ i ∈ S_f, Real.log (rat i)) := by
          intro S_f
          induction S_f using Finset.induction_on with
          | empty => simp [kernelLogPhase]
          | @insert x₀ s₀ hx₀ ih =>
            rw [Finset.prod_insert hx₀, Finset.sum_insert hx₀, ih]
            unfold kernelLogPhase; rw [← Complex.exp_add]; congr 1; push_cast; ring
        exact hkp Finset.univ
      have hV_U (U : Finset ι) :
          V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X) =
            ∫ s : ℝ, (𝓕 g) s *
              (kernelLogPhase s (Real.log yj) * childLogTest wFresh s (primeProductNorm p U / X₀)) := by
        have hpnorm_pos : 0 < primeProductNorm p U := by
          unfold primeProductNorm; rw [map_prod]
          exact sq_pos_of_pos (norm_pos_iff.mpr
            (Finset.prod_ne_zero_iff.mpr (fun j _ => ringComplex_ne_zero (hp j))))
        let yc : ℝ := primeProductNorm p U / X₀
        have hyc_pos : 0 < yc := div_pos hpnorm_pos hX₀_pos
        have harg_eq : (primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X = yj * yc := by
          rw [hyj_eq, ← hX_eq]; dsimp only [yc]; field_simp [hX₀_pos.ne', hZprod_pos.ne']
        rw [harg_eq]
        have hw_cut : V (yj * yc) = wFresh yc * V (yj * yc) := by
          by_cases hV0 : V (yj * yc) = 0
          · simp [hV0]
          · have hw1 := hFresh (∅ : Finset Unit) (Nat.zero_le K) (V : ℝ → ℂ) hsV
              (fun _ => 1) yj yc (by simp) hyj_Icc hyc_pos (by simpa using hV0)
            rw [hw1, one_mul]
        have hg_val : V (yj * yc) = g (Real.log yc + Real.log yj) := by
          rw [hg_apply, Real.exp_add, Real.exp_log hyc_pos, Real.exp_log hyj_pos, mul_comm]
        rw [hw_cut, hg_val, JointLogSeparation.schwartz_phase_inversion g (Real.log yc + Real.log yj),
          ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with s
        dsimp only [yc]
        unfold childLogTest kernelLogPhase
        rw [show (((2 * Real.pi * s * (Real.log (primeProductNorm p U / X₀) + Real.log yj) : ℝ) : ℂ) * Complex.I) =
            (((2 * Real.pi * s * Real.log (primeProductNorm p U / X₀) : ℝ) : ℂ) * Complex.I) +
              (((2 * Real.pi * s * Real.log yj : ℝ) : ℂ) * Complex.I) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [initial_input_row p hg]
      unfold supportConjugateSum
      simp_rw [hV_U]
      let c_tup : ℂ := tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
        star (primeSubsetRow p χ (tuplePrimeSet tup) w)
      let f_U : Finset ι → ℝ → ℂ := fun U s =>
        (𝓕 g) s * (c_tup * (supportMobius U *
          (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
            (kernelLogPhase s (Real.log yj) * childLogTest wFresh s (primeProductNorm p U / X₀))) *
          star (primeSubsetRow p χ U w)))
      have hf_int (U : Finset ι) : Integrable (f_U U) := by
        let K_U : ℂ := c_tup * (supportMobius U * Ψ₀ (∏ i ∈ U, p i) *
          primeCoprimeMask p U 1 * wFresh (primeProductNorm p U / X₀) *
          star (primeSubsetRow p χ U w))
        have hcont : Continuous (fun s : ℝ =>
            K_U * kernelLogPhase s (Real.log yj) *
              kernelLogPhase s (Real.log (primeProductNorm p U / X₀))) := by
          unfold kernelLogPhase; fun_prop
        have heq_f : f_U U = fun s => (𝓕 g) s *
            (K_U * kernelLogPhase s (Real.log yj) *
              kernelLogPhase s (Real.log (primeProductNorm p U / X₀))) := by
          funext s; dsimp only [f_U, K_U, childLogTest]; ring
        rw [heq_f]
        refine ((𝓕 g).integrable.norm.mul_const ‖K_U‖).mono'
          ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
        filter_upwards with s
        rw [norm_mul, norm_mul, norm_mul, kernelLogPhase_norm,
          kernelLogPhase_norm, mul_one, mul_one]
      have hlhs_eq :
          c_tup * (∑ U ∈ (pool \ tuplePrimeSet tup).powerset,
            supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              ∫ s : ℝ, (𝓕 g) s * (kernelLogPhase s (Real.log yj) *
                childLogTest wFresh s (primeProductNorm p U / X₀))) *
              star (primeSubsetRow p χ U w)) =
          ∑ U ∈ (pool \ tuplePrimeSet tup).powerset, ∫ s : ℝ, f_U U s := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro U _
        have hfU_pull : (fun s : ℝ => f_U U s) =
            fun s : ℝ => (c_tup * supportMobius U * Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              star (primeSubsetRow p χ U w)) *
              ((𝓕 g) s * (kernelLogPhase s (Real.log yj) *
                childLogTest wFresh s (primeProductNorm p U / X₀))) := by
          funext s; dsimp only [f_U]; ring
        rw [hfU_pull, integral_const_mul]; ring
      change c_tup * _ = _
      rw [hlhs_eq, ← integral_finsetSum _ (fun U _ => hf_int U)]
      apply integral_congr_ae; filter_upwards with s
      rw [initial_input_row p hg]; unfold supportConjugateSum
      rw [hphase_tup s]; dsimp only [f_U, c_tup]; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    change (-1 : ℂ) ^ S_rem.card *
        ∑ tup : (∀ i : S_rem, lists i.val),
          ((tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            primeCoprimeMask p (tuplePrimeSet tup) 1 *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
            (fun U => V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X)) w) = _
    simp_rw [htup_int]
    let G_tup : (∀ i : S_rem, lists i.val) → ℝ → ℂ := fun tup s =>
      (𝓕 g) s * ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
          star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
        inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
          (fun U => childLogTest wFresh s (primeProductNorm p U / X₀)) w)
    have hG_int (tup : ∀ i : S_rem, lists i.val) : Integrable (G_tup tup) := by
      have hexp : G_tup tup = fun s =>
          ∑ U ∈ (pool \ tuplePrimeSet tup).powerset,
            (𝓕 g) s * ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
              (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                childLogTest wFresh s (primeProductNorm p U / X₀)) *
                star (primeSubsetRow p χ U w))) := by
        funext s; dsimp only [G_tup]; rw [initial_input_row p hg]
        unfold supportConjugateSum; simp only [Finset.mul_sum]; rfl
      rw [hexp]; apply integrable_finsetSum; intro U _
      have hcont : Continuous (fun s : ℝ =>
          (tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
            (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              childLogTest wFresh s (primeProductNorm p U / X₀)) *
              star (primeSubsetRow p χ U w))) := by
        dsimp only [a_tw]; unfold tupleCoeff childLogTest kernelLogPhase; fun_prop
      refine ((𝓕 g).integrable.norm.mul_const B_w).mono'
        ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
      filter_upwards with s
      rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have htc1 : ‖tupleCoeff (a_tw s) tup‖ ≤ 1 := tupleCoeff_norm_le_one
        (fun i hi q hq => by dsimp only [a_tw]; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact ha i hi q hq) tup
      have hcw : ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
        unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw_norm _
      have hp1 : ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ ≤ 1 := hΨ1 _
      have hp2 : ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w)‖ ≤ 1 := by
        rw [norm_star]; exact primeSubsetRow_norm_le_one p χ _ w
      have hm1 : ‖supportMobius U‖ = 1 := supportMobius_norm U
      have hp3 : ‖Ψ₀ (∏ i ∈ U, p i)‖ ≤ 1 := hΨ1 _
      have hm2 : ‖primeCoprimeMask p U 1‖ ≤ 1 := by
        rw [primeCoprimeMask_indicator]; split_ifs <;> norm_num
      have hp4 : ‖star (primeSubsetRow p χ U w)‖ ≤ 1 := by
        rw [norm_star]; exact primeSubsetRow_norm_le_one p χ U w
      change ‖(tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
          star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
        (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
          childLogTest wFresh s (primeProductNorm p U / X₀)) *
          star (primeSubsetRow p χ U w))‖ ≤ B_w
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hm1, one_mul]
      have h_lhs : ‖tupleCoeff (a_tw s) tup‖ * ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ *
          ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w)‖ ≤ 1 :=
        (mul_le_mul (mul_le_mul htc1 hp1 (norm_nonneg _) zero_le_one) hp2
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
      have h_mid : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
          ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w :=
        (mul_le_mul ((mul_le_mul hp3 hm2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hcw
          (norm_nonneg _) zero_le_one).trans_eq (one_mul B_w)
      have h_rhs : (‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
          ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖) *
          ‖star (primeSubsetRow p χ U w)‖ ≤ B_w :=
        (mul_le_mul h_mid hp4 (norm_nonneg _) hBw).trans_eq (mul_one B_w)
      exact (mul_le_mul h_lhs h_rhs (by positivity) zero_le_one).trans_eq (one_mul B_w)
    change (-1 : ℂ) ^ S_rem.card * ∑ tup : (∀ i : S_rem, lists i.val), ∫ s : ℝ, G_tup tup s = _
    rw [← integral_finsetSum _ (fun tup _ => hG_int tup), ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with s
    unfold disjTupleSum; dsimp only [G_tup]; rw [← Finset.mul_sum]; ring
  let E_tot : ℝ := (307330 : ℝ) ^ K * (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail))
  have hE_tot_nn : 0 ≤ E_tot := by dsimp only [E_tot]; positivity
  have hpt_s (s : ℝ) :
      (∑ w ∈ S_w, X⁻¹ *
        ‖disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w‖ ^ 2) ≤
        E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by
    have ha_s : ∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a_tw s i q‖ ≤ 1 := by
      intro i hi q hq; dsimp only [a_tw]
      rw [norm_mul, kernelLogPhase_norm, mul_one]; exact ha i hi q hq
    have hb_s : ∀ y, childLogTest wFresh s y ≠ 0 → y ≤ bf := fun y hy =>
      (hsup_w (InverseInitialOriginalHeight.child_support wFresh s hy)).2
    have hpow_K : (307330 : ℝ) ^ S_rem.card ≤ (307330 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num) hK
    by_cases hs_le : |s| ≤ S_cut
    · have hB_s : 0 ≤ B_low * (1 + |s|) ^ (2 * deg) := by positivity
      have hd := disjTupleSum_l2_le_factored_sharp p hp hg hinj_p pool ∅ Ψ₀ hΨ1 S_rem ∅
        (Finset.disjoint_empty_right S_rem) lists (by simpa using hlists_pool) (by simpa using hdisj)
        (a_tw s) ha_s Z_slot (by simpa using hZ1) hZ_lo hZ_hi (childLogTest wFresh s) hb_s
        S_w hB_s X₀ hX₀_pos
        (fun T' hT' X' hX' hX'_le => by
          simpa [Finset.union_empty] using hlow s hs_le T' (by simpa using hT') X' hX'
            (by simpa using hX'_le))
      simp only [Finset.sdiff_empty, Finset.union_empty, Finset.prod_empty, mul_one,
        Finset.card_empty, pow_zero, hX_eq] at hd
      have h1 : (1 + |s|) ^ (2 * deg) ≤ ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        rw [Real.norm_eq_abs, ← pow_mul]
        exact pow_le_pow_right₀ (by linarith [abs_nonneg s]) (by dsimp only [J_tot]; omega)
      calc _ ≤ (307330 : ℝ) ^ S_rem.card * (B_low * (1 + |s|) ^ (2 * deg)) := hd
        _ ≤ (307330 : ℝ) ^ K * ((B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2) := by
            apply mul_le_mul hpow_K _ hB_s (by positivity)
            exact mul_le_mul (le_add_of_nonneg_right (by positivity)) h1 (by positivity) (by positivity)
        _ = E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by dsimp only [E_tot]; ring
    · have hs_gt : S_cut < |s| := not_le.mp hs_le
      have hd := disjTupleSum_l2_le_factored_sharp p hp hg hinj_p pool ∅ Ψ₀ hΨ1 S_rem ∅
        (Finset.disjoint_empty_right S_rem) lists (by simpa using hlists_pool) (by simpa using hdisj)
        (a_tw s) ha_s Z_slot (by simpa using hZ1) hZ_lo hZ_hi (childLogTest wFresh s) hb_s
        S_w hB_triv X₀ hX₀_pos
        (fun T' hT' X' hX' hX'_le => by
          simpa [Finset.union_empty] using htriv s T' (by simpa using hT') X' hX'
            (by simpa using hX'_le))
      simp only [Finset.sdiff_empty, Finset.union_empty, Finset.prod_empty, mul_one,
        Finset.card_empty, pow_zero, hX_eq] at hd
      have hcut_pow : (1 + S_cut) ^ (2 * N_tail) ≤ ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        rw [Real.norm_eq_abs, ← pow_mul]
        calc (1 + S_cut) ^ (2 * N_tail)
            ≤ (1 + |s|) ^ (2 * N_tail) := pow_le_pow_left₀ (by linarith) (by linarith) _
          _ ≤ (1 + |s|) ^ (J_tot * 2) := pow_le_pow_right₀ (by linarith [abs_nonneg s])
              (by dsimp only [J_tot]; omega)
      have hcut_pos : 0 < (1 + S_cut) ^ (2 * N_tail) := pow_pos (by linarith) _
      have htriv_le : B_triv ≤ (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2 := by
        calc B_triv = (B_triv / (1 + S_cut) ^ (2 * N_tail)) * (1 + S_cut) ^ (2 * N_tail) :=
              (div_mul_cancel₀ B_triv hcut_pos.ne').symm
          _ ≤ (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2 :=
              mul_le_mul (le_add_of_nonneg_left hB_low) hcut_pow hcut_pos.le (by positivity)
      calc _ ≤ (307330 : ℝ) ^ S_rem.card * B_triv := hd
        _ ≤ (307330 : ℝ) ^ K * ((B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) * ((1 + ‖s‖) ^ J_tot) ^ 2) :=
            mul_le_mul hpow_K htriv_le hB_triv (by positivity)
        _ = E_tot * ((1 + ‖s‖) ^ J_tot) ^ 2 := by dsimp only [E_tot]; ring
  let h_wt : ℝ → ℝ := fun s => (1 + ‖s‖) ^ J_tot
  let b_meas : ℝ → ℂ := fun s => (𝓕 g) s * (h_wt s : ℂ)
  let f_meas : S_w → ℝ → ℂ := fun w s =>
    (((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w.val) / (h_wt s : ℂ)
  have hh_pos (s : ℝ) : 0 < h_wt s := by dsimp only [h_wt]; positivity
  have hb_norm (s : ℝ) : ‖b_meas s‖ = h_wt s * ‖(𝓕 g) s‖ := by
    dsimp only [b_meas]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s), mul_comm]
  have hb_int : Integrable (fun s => ‖b_meas s‖) := by simpa only [hb_norm] using hint_wt
  have hbf_eq (w : S_w) (s : ℝ) : b_meas s * f_meas w s =
      ((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((𝓕 g) s * disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w.val) := by
    dsimp only [b_meas, f_meas]
    have hn : (h_wt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh_pos s).ne'
    field_simp [hn]
  have hbf_int (w : S_w) : Integrable (fun s => b_meas s * f_meas w s) := by
    simp_rw [hbf_eq w]
    apply Integrable.const_mul
    unfold disjTupleSum; simp only [Finset.mul_sum]; apply integrable_finsetSum; intro tup _
    simp_rw [initial_input_row p hg]; unfold supportConjugateSum; simp only [Finset.mul_sum]
    apply integrable_finsetSum; intro U _
    have hcont : Continuous (fun s : ℝ =>
        (-1 : ℂ) ^ S_rem.card *
          ((tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)) *
            (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
              childLogTest wFresh s (primeProductNorm p U / X₀)) *
              star (primeSubsetRow p χ U w.val)))) := by
      dsimp only [a_tw]; unfold tupleCoeff childLogTest kernelLogPhase; fun_prop
    refine ((𝓕 g).integrable.norm.mul_const B_w).mono'
      ((𝓕 g).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
    filter_upwards with s
    rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have htc1 : ‖tupleCoeff (a_tw s) tup‖ ≤ 1 := tupleCoeff_norm_le_one
      (fun i hi q hq => by dsimp only [a_tw]; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact ha i hi q hq) tup
    have hcw : ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w := by
      unfold childLogTest; rw [norm_mul, kernelLogPhase_norm, mul_one]; exact hBw_norm _
    have hp1 : ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ ≤ 1 := hΨ1 _
    have hp2 : ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)‖ ≤ 1 := by
      rw [norm_star]; exact primeSubsetRow_norm_le_one p χ _ w.val
    have hm1 : ‖supportMobius U‖ = 1 := supportMobius_norm U
    have hp3 : ‖Ψ₀ (∏ i ∈ U, p i)‖ ≤ 1 := hΨ1 _
    have hm2 : ‖primeCoprimeMask p U 1‖ ≤ 1 := by
      rw [primeCoprimeMask_indicator]; split_ifs <;> norm_num
    have hp4 : ‖star (primeSubsetRow p χ U w.val)‖ ≤ 1 := by
      rw [norm_star]; exact primeSubsetRow_norm_le_one p χ U w.val
    change ‖(tupleCoeff (a_tw s) tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
        star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)) *
      (supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
        childLogTest wFresh s (primeProductNorm p U / X₀)) *
        star (primeSubsetRow p χ U w.val))‖ ≤ B_w
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hm1, one_mul]
    have h1 : ‖tupleCoeff (a_tw s) tup‖ * ‖Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j)‖ *
        ‖star (primeSubsetRow p χ (tuplePrimeSet tup) w.val)‖ ≤ 1 :=
      (mul_le_mul (mul_le_mul htc1 hp1 (norm_nonneg _) zero_le_one) hp2
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
    have h2 : ‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
        ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖ ≤ B_w :=
      (mul_le_mul ((mul_le_mul hp3 hm2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hcw
        (norm_nonneg _) zero_le_one).trans_eq (one_mul B_w)
    have h3 : (‖Ψ₀ (∏ i ∈ U, p i)‖ * ‖primeCoprimeMask p U 1‖ *
        ‖childLogTest wFresh s (primeProductNorm p U / X₀)‖) *
        ‖star (primeSubsetRow p χ U w.val)‖ ≤ B_w :=
      (mul_le_mul h2 hp4 (norm_nonneg _) hBw).trans_eq (mul_one B_w)
    exact (mul_le_mul h1 h3 (by positivity) zero_le_one).trans_eq (one_mul B_w)
  have hX_sq : ∀ z : ℂ, ‖((X ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * z‖ ^ 2 = X⁻¹ * ‖z‖ ^ 2 := by
    intro z
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hX _), ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hX.le]
    norm_num [Real.rpow_neg_one]
  have hf_energy (s : ℝ) : (∑ w : S_w, ‖f_meas w s‖ ^ 2) ≤ E_tot := by
    have hsum_eq : (∑ w : S_w, ‖f_meas w s‖ ^ 2) =
        (∑ w ∈ S_w, X⁻¹ *
          ‖disjTupleSum p hg pool S_rem lists (a_tw s) Ψ₀ (childLogTest wFresh s) X₀ w‖ ^ 2) /
          (h_wt s) ^ 2 := by
      rw [← Finset.sum_coe_sort S_w, Finset.sum_div]
      apply Finset.sum_congr rfl; intro w _
      simp only [f_meas, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s),
        div_pow, hX_sq]
    rw [hsum_eq, div_le_iff₀ (sq_pos_of_pos (hh_pos s))]
    exact hpt_s s
  have hcme := InverseMoment.common_measure_energy volume b_meas f_meas E_tot
    hE_tot_nn hb_int hbf_int hf_energy
  have hlhs_cme :
      (∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1 (markedRadial p S_rem lists a ∅ V X) w‖ ^ 2) =
        ∑ w : S_w, ‖∫ s : ℝ, b_meas s * f_meas w s‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S_w]
    apply Finset.sum_congr rfl; intro w _
    simp_rw [hbf_eq w]
    rw [integral_const_mul, hX_sq, ← hfour_pt w.val]
  rw [hlhs_cme]
  have hb_int_eq : (∫ s : ℝ, ‖b_meas s‖) = I_wt := by
    simp_rw [hb_norm]; rfl
  have hI_sq : I_wt ^ 2 ≤ C_ft ^ 2 * (1 + ‖t‖) ^ (2 * (J_tot + (volume : Measure ℝ).integrablePower)) := by
    have hsq := pow_le_pow_left₀ hI_wt_nn hI_wt_le 2
    rwa [mul_pow, ← pow_mul, Nat.mul_comm] at hsq
  calc (∑ w : S_w, ‖∫ s : ℝ, b_meas s * f_meas w s‖ ^ 2)
      ≤ E_tot * (∫ s : ℝ, ‖b_meas s‖) ^ 2 := hcme
    _ = E_tot * I_wt ^ 2 := by rw [hb_int_eq]
    _ ≤ E_tot * (C_ft ^ 2 * (1 + ‖t‖) ^ (2 * (J_tot + (volume : Measure ℝ).integrablePower))) :=
        mul_le_mul_of_nonneg_left hI_sq hE_tot_nn
    _ = C_four * (1 + ‖t‖) ^ (2 * (deg + N_tail + (volume : Measure ℝ).integrablePower)) *
          (B_low + B_triv / (1 + S_cut) ^ (2 * N_tail)) := by
        dsimp only [C_four, E_tot, J_tot]; ring

/-! ### Part III: Sharp `Q = {0}` sextic label transfer via `sexticTuple_fiber_card_le` -/

/-- Sharp one-`Z ^ u_act` `4 × 3 = 12` sextic label transfer on `Q = {0}`:
log-separating `normTwistedSource om ξ` with a uniform `wFresh` makes the `{0}` child row
independent of `tup` (except through `w = (∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z`), so grouping
`(tup, z) ↦ w` via `sexticTuple_fiber_card_le` avoids the second factor of `∏ i ∈ U_cand, Z_slot i`! -/
theorem qzero_sextic_label_transfer_sharp
    (om : 𝓢(ℝ, ℂ)) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀)
    (hs : Function.support (om : ℝ → ℂ) ⊆ Set.Icc a₀ b₀) (K : ℕ) :
    ∃ (wFresh : 𝓢(ℝ, ℂ)) (af bf : ℝ),
      0 < af ∧ af ≤ bf ∧
      Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf ∧
      ∀ (deg : ℕ), ∃ C_tr : ℝ, 0 < C_tr ∧
      ∀ (ξ : ℝ) {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
        (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
        (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
        (_hinj_p : Function.Injective p)
        (pool : Finset ι) (labels : Finset (Ideal O))
        (Ψ : O →* ℂ), (∀ u, ‖Ψ u‖ ≤ 1) →
        ∀ (m : O) (S_v U_cand : Finset σ), U_cand ⊆ S_v → U_cand.card ≤ K →
        ∀ (lists : σ → Finset ι), (∀ i ∈ S_v, lists i ⊆ pool) →
        (S_v : Set σ).PairwiseDisjoint lists →
        ∀ (a : σ → ι → ℂ), (∀ i ∈ S_v, ∀ q ∈ lists i, ‖a i q‖ ≤ 1) →
        ∀ (Z_slot : σ → ℝ), (∀ i ∈ U_cand, 1 ≤ Z_slot i) →
        (∀ i ∈ U_cand, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2) →
        (∀ i ∈ U_cand, ∀ q ∈ lists i, ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot i) →
        ∀ {C_div eps_div : ℝ}, 0 < C_div → 0 ≤ eps_div →
        (∀ I : Ideal O, I ≠ 0 → ((idealDivisors I).card : ℝ) ≤ C_div * (Ideal.absNorm I : ℝ) ^ eps_div) →
        ∀ {X K_rad K_out B_out : ℝ}, 0 < X → 0 < K_rad → 0 ≤ B_out →
        let P_U := ∏ i ∈ U_cand, Z_slot i
        let X_out := X / P_U
        2 * ((2 : ℝ) ^ K * P_U) ^ 4 * K_rad ≤ K_out →
        (∀ s : ℝ,
          rowFamilyEnergy labels
            (fun I w => varyingReopenedRow p hg pool {0} (fun _ => 1) Ψ m (cubicIdealGenerator I)
              (fun v N => primeMark (S_v \ U_cand) lists a (N ∪ v.support) *
                normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N / X_out)) w) K_out ≤
            B_out * (1 + ‖s‖) ^ (2 * deg)) →
        rowFamilyEnergy labels
            (fun I z => varyingReopenedRow p hg pool {0} (fun _ => 1) Ψ m (cubicIdealGenerator I)
              (fun v T => primeMark S_v lists a (T ∪ v.support) *
                normTwistedSource (om : ℝ → ℂ) ξ (primeProductNorm p T / X)) z) K_rad ≤
          C_tr * C_div * (2 * K_out) ^ eps_div * P_U * B_out *
            (1 + ‖ξ‖) ^ (2 * (deg + (volume : Measure ℝ).integrablePower)) := by
  obtain ⟨wFresh, af, bf, B_w, haf, habf, hBw0, _, htsup, hBw_norm, hFresh⟩ :=
    InverseInitialUniformFresh.exists_uniform_fresh K a₀ b₀ ha₀ hab₀
  have hsup_w : Function.support (wFresh : ℝ → ℂ) ⊆ Set.Icc af bf :=
    (subset_tsupport (wFresh : ℝ → ℂ)).trans htsup
  refine ⟨wFresh, af, bf, haf, habf, hsup_w, ?_⟩
  intro deg
  let g₀ : 𝓢(ℝ, ℂ) := kernelLogSource (om : ℝ → ℂ) a₀ b₀ ha₀ hs (om.smooth ⊤)
  obtain ⟨C_ft0, hC_ft0, hft⟩ := frequencyTwist_fourier_moment deg g₀
  let C_ft : ℝ := C_ft0 + 1
  let C_tr : ℝ := C_ft ^ 2 * (98 : ℝ) ^ K
  refine ⟨C_tr, by dsimp only [C_tr, C_ft]; positivity, ?_⟩
  intro ξ ι σ _ _ p hp _ hcop hg hinj hc hpr hinj_p pool labels Ψ hΨ1 m S_v U_cand hU hU_card
    lists hlists_pool hdisj a ha Z_slot hZ1 hZ_lo hZ_hi C_div eps_div hC_div heps_div hdiv_le
    X K_rad K_out B_out hX hK_rad hB_out P_U X_out hK_out hrow_s
  have hPU_ge1 : 1 ≤ P_U := Finset.one_le_prod (fun i hi => hZ1 i hi)
  have hPU_pos : 0 < P_U := zero_lt_one.trans_le hPU_ge1
  have hX_out_pos : 0 < X_out := div_pos hX hPU_pos
  have hX_eq : X_out * P_U = X := div_mul_cancel₀ X hPU_pos.ne'
  have hK_out_pos : 0 < K_out := lt_of_lt_of_le (by positivity) hK_out
  have hdisj_U : (U_cand : Set σ).PairwiseDisjoint lists :=
    fun i hi j hj hij => hdisj (hU hi) (hU hj) hij
  let g_ξ : 𝓢(ℝ, ℂ) := frequencyTwist g₀ ξ
  have hs_ξ : Function.support (normTwistedSource (om : ℝ → ℂ) ξ) ⊆ Set.Icc a₀ b₀ :=
    (normTwistedSource_support (om : ℝ → ℂ) ξ).trans hs
  have hg_ξ_apply : ∀ u : ℝ, g_ξ u = normTwistedSource (om : ℝ → ℂ) ξ (Real.exp u) := by
    intro u
    dsimp only [g_ξ, g₀]
    simp only [frequencyTwist_apply, kernelLogSource_apply, normTwistedSource, Real.log_exp]
  have hchild_eq_nt : ∀ (s y : ℝ), childLogTest (wFresh : ℝ → ℂ) s y =
      normTwistedSource (wFresh : ℝ → ℂ) s y := by
    intro s y; simp only [childLogTest, normTwistedSource, mul_comm]
  -- Step 1: Pointwise integral representation via `varyingReopenedRow_sextic_label_transfer` at `Q = {0}`!
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  let F_s : ℝ → Ideal O → O → ℂ := fun s I w =>
    varyingReopenedRow p hg pool {0} (fun _ => 1) Ψ m (cubicIdealGenerator I)
      (fun v N => primeMark (S_v \ U_cand) lists a (N ∪ v.support) *
        normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N / X_out)) w
  let yj_tup : (∀ i : U_cand, lists i.val) → ℝ :=
    fun tup => primeProductNorm p (tuplePrimeSet tup) / P_U
  let γ_tup : ℝ → Ideal O → O → (∀ i : U_cand, lists i.val) → ℂ := fun s I z tup =>
    tupleCoeff a tup *
      secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup) *
      kernelLogPhase s (Real.log (yj_tup tup))
  have hyj_bounds : ∀ tup : (∀ i : U_cand, lists i.val),
      0 < yj_tup tup ∧ yj_tup tup ∈ Set.Icc (1 : ℝ) ((2 : ℝ) ^ K) ∧
      primeProductNorm p (tuplePrimeSet tup) = yj_tup tup * P_U := by
    intro tup
    have hnorm_tup : primeProductNorm p (tuplePrimeSet tup) =
        ∏ i : U_cand, ‖ringComplex (p (tup i).val)‖ ^ 2 := by
      unfold primeProductNorm tuplePrimeSet
      rw [map_prod, norm_prod, Finset.prod_pow, Finset.prod_image (fun i₁ _ i₂ _ he => by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj_U i₁.property i₂.property (fun hv => hne (Subtype.ext hv)))
          (tup i₁).property (he ▸ (tup i₂).property))]
    let rat : U_cand → ℝ := fun i => ‖ringComplex (p (tup i).val)‖ ^ 2 / Z_slot i.val
    have hrat_b (i : U_cand) : rat i ∈ Set.Icc (1 : ℝ) 2 := by
      have hZi := zero_lt_one.trans_le (hZ1 i.val i.property)
      exact ⟨(one_le_div hZi).mpr (hZ_lo i.val i.property (tup i).val (tup i).property),
        (div_le_iff₀ hZi).mpr (hZ_hi i.val i.property (tup i).val (tup i).property)⟩
    have hyj_eq_rat : yj_tup tup = ∏ i : U_cand, rat i := by
      dsimp only [yj_tup, rat, P_U]
      rw [hnorm_tup, Finset.prod_div_distrib, Finset.prod_coe_sort U_cand Z_slot]
    have hyj_pos : 0 < yj_tup tup := by
      rw [hyj_eq_rat]; exact Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hrat_b i).1)
    refine ⟨hyj_pos, ?_, div_mul_cancel₀ _ hPU_pos.ne' |>.symm⟩
    rw [hyj_eq_rat]
    refine ⟨Finset.one_le_prod (fun i _ => (hrat_b i).1), ?_⟩
    calc (∏ i : U_cand, rat i)
        ≤ ∏ _i : U_cand, (2 : ℝ) := Finset.prod_le_prod (fun i _ => zero_le_one.trans (hrat_b i).1)
          (fun i _ => (hrat_b i).2)
      _ = (2 : ℝ) ^ U_cand.card := by simp
      _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hU_card
  have hpt_int (I : Ideal O) (z : O) :
      varyingReopenedRow p hg pool {0} (fun _ => 1) Ψ m (cubicIdealGenerator I)
        (fun v T => primeMark S_v lists a (T ∪ v.support) *
          normTwistedSource (om : ℝ → ℂ) ξ (primeProductNorm p T / X)) z =
      ∫ s : ℝ, (𝓕 g_ξ) s * ∑ tup : (∀ i : U_cand, lists i.val),
        γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) := by
    have hq0_pool : ∀ v ∈ ({0} : Finset (ι →₀ ℕ)), v.support ⊆ pool := by
      intro v hv; rw [Finset.mem_singleton.mp hv]; simp
    have htr := varyingReopenedRow_sextic_label_transfer p hp hcop hg hpr pool {0} hq0_pool
      (fun _ => 1) (fun _ => 1) Ψ m (cubicIdealGenerator I) z
      (normTwistedSource (om : ℝ → ℂ) ξ) X S_v U_cand hU lists hlists_pool hdisj a
    simp only [div_one] at htr
    rw [htr]
    -- Collapse `J_hit ∈ U_cand.powerset` to `J_hit = ∅` since `(0 : ι →₀ ℕ).support = ∅`.
    rw [Finset.sum_eq_single ∅]
    · -- Equivalence `(U_cand \ ∅ : Finset σ) = U_cand` via `Finset.sdiff_empty`.
      have hsdiff0 : U_cand \ ∅ = U_cand := Finset.sdiff_empty
      rw [hsdiff0]
      -- Rewrite each `tup` summand as an `s`-integral!
      have htup_eq (tup : ∀ i : U_cand, lists i.val) :
          (tupleCoeff a tup *
            secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)) *
          varyingReopenedRow p hg pool {0}
            (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                primeMark ∅ lists a v.support * 1 else 0)
            Ψ m (cubicIdealGenerator I)
            (fun v N => primeMark (S_v \ U_cand) lists a (N ∪ v.support) *
              normTwistedSource (om : ℝ → ℂ) ξ
                (primeProductNorm p N / (X / primeProductNorm p (tuplePrimeSet tup))))
            ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) =
          ∫ s : ℝ, (𝓕 g_ξ) s *
            (γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)) := by
        obtain ⟨hyj_pos, hyj_Icc, hyj_eq⟩ := hyj_bounds tup
        let w' := (∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z
        let c₀ : ℂ := tupleCoeff a tup *
          secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)
        have hN_int (N : Finset ι) :
            normTwistedSource (om : ℝ → ℂ) ξ
                (primeProductNorm p N / (X / primeProductNorm p (tuplePrimeSet tup))) =
              ∫ s : ℝ, (𝓕 g_ξ) s *
                (kernelLogPhase s (Real.log (yj_tup tup)) *
                  normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N / X_out)) := by
          have hpN_pos : 0 < primeProductNorm p N := by
            unfold primeProductNorm; rw [map_prod]
            exact sq_pos_of_pos (norm_pos_iff.mpr
              (Finset.prod_ne_zero_iff.mpr (fun j _ => ringComplex_ne_zero (hp j))))
          let yc : ℝ := primeProductNorm p N / X_out
          have hyc_pos : 0 < yc := div_pos hpN_pos hX_out_pos
          have harg : primeProductNorm p N / (X / primeProductNorm p (tuplePrimeSet tup)) =
              yj_tup tup * yc := by
            rw [hyj_eq, ← hX_eq]; dsimp only [yc]
            field_simp [hX_out_pos.ne', hPU_pos.ne', hyj_pos.ne']
          rw [harg]
          have hw_cut : normTwistedSource (om : ℝ → ℂ) ξ (yj_tup tup * yc) =
              wFresh yc * normTwistedSource (om : ℝ → ℂ) ξ (yj_tup tup * yc) := by
            by_cases h0 : normTwistedSource (om : ℝ → ℂ) ξ (yj_tup tup * yc) = 0
            · simp [h0]
            · have hw1 := hFresh (∅ : Finset Unit) (Nat.zero_le K)
                (normTwistedSource (om : ℝ → ℂ) ξ) hs_ξ (fun _ => 1) (yj_tup tup) yc
                (by simp) hyj_Icc hyc_pos (by simpa using h0)
              rw [hw1, one_mul]
          have hg_val : normTwistedSource (om : ℝ → ℂ) ξ (yj_tup tup * yc) =
              g_ξ (Real.log yc + Real.log (yj_tup tup)) := by
            rw [hg_ξ_apply, Real.exp_add, Real.exp_log hyc_pos, Real.exp_log hyj_pos, mul_comm]
          rw [hw_cut, hg_val,
            JointLogSeparation.schwartz_phase_inversion g_ξ (Real.log yc + Real.log (yj_tup tup)),
            ← integral_const_mul]
          apply integral_congr_ae; filter_upwards with s
          simp_rw [← hchild_eq_nt]
          dsimp only [yc]
          unfold childLogTest kernelLogPhase
          rw [show (((2 * Real.pi * s * (Real.log (primeProductNorm p N / X_out) + Real.log (yj_tup tup)) : ℝ) : ℂ) * Complex.I) =
              (((2 * Real.pi * s * Real.log (primeProductNorm p N / X_out) : ℝ) : ℂ) * Complex.I) +
                (((2 * Real.pi * s * Real.log (yj_tup tup) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
            Complex.exp_add]
          ring
        unfold varyingReopenedRow
        simp only [Finset.sum_singleton, Finsupp.support_zero, Finsupp.coe_zero,
          Finset.disjoint_empty_right, ite_true, primeMark, Finset.prod_empty, one_mul,
          Finset.union_empty]
        let C_base : Finset ι → ℂ := fun N =>
          canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
            (primeMark (S_v \ U_cand) lists a) N *
          (multiplicityRow p hg pool 0 w' ^ 3 * primeSubsetRow p χ N w')
        have hcoeff_split : ∀ (N : Finset ι) (H : Finset ι → ℂ),
            canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
              (fun S => primeMark (S_v \ U_cand) lists a S * H S) N *
            (multiplicityRow p hg pool 0 w' ^ 3 * primeSubsetRow p χ N w') =
            C_base N * H N := by
          intro N H; dsimp only [C_base, χ]; unfold canonicalSourceCoefficient; ring
        let f_N : Finset ι → ℝ → ℂ := fun N s =>
          (𝓕 g_ξ) s * (c₀ * kernelLogPhase s (Real.log (yj_tup tup)) *
            (C_base N * normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N / X_out)))
        have hfN_int (N : Finset ι) : Integrable (f_N N) := by
          let K_N : ℂ := c₀ * C_base N * wFresh (primeProductNorm p N / X_out)
          have hcont : Continuous (fun s : ℝ =>
              K_N * kernelLogPhase s (Real.log (yj_tup tup)) *
                kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
            unfold kernelLogPhase; fun_prop
          have heq_f : f_N N = fun s => (𝓕 g_ξ) s *
              (K_N * kernelLogPhase s (Real.log (yj_tup tup)) *
                kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
            funext s; dsimp only [f_N, K_N]; unfold normTwistedSource; ring
          rw [heq_f]
          refine ((𝓕 g_ξ).integrable.norm.mul_const ‖K_N‖).mono'
            ((𝓕 g_ξ).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
          filter_upwards with s
          rw [norm_mul, norm_mul, norm_mul, kernelLogPhase_norm, kernelLogPhase_norm, mul_one, mul_one]
        have hlhs_N :
            c₀ * ∑ N ∈ pool.powerset,
              canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
                (fun S => primeMark (S_v \ U_cand) lists a S *
                  normTwistedSource (om : ℝ → ℂ) ξ
                    (primeProductNorm p S / (X / primeProductNorm p (tuplePrimeSet tup)))) N *
              (multiplicityRow p hg pool 0 w' ^ 3 * primeSubsetRow p χ N w') =
            ∑ N ∈ pool.powerset, ∫ s : ℝ, f_N N s := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro N _
          rw [hcoeff_split N, hN_int N]
          have hpull : f_N N = fun s => (c₀ * C_base N) *
              ((𝓕 g_ξ) s * (kernelLogPhase s (Real.log (yj_tup tup)) *
                normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N / X_out))) := by
            funext s; dsimp only [f_N]; ring
          rw [← mul_assoc c₀ (C_base N), ← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun s => by rw [hpull]))
        have hlhs_fold :
            c₀ * ∑ x ∈ pool.powerset,
              canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
                (fun N => (∏ x_1 ∈ S_v \ U_cand, primeSlot (lists x_1) (a x_1) N) *
                  normTwistedSource (om : ℝ → ℂ) ξ
                    (primeProductNorm p N / (X / primeProductNorm p (tuplePrimeSet tup)))) x *
              (multiplicityRow p hg pool 0 ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) ^ 3 *
                primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) x
                  ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)) =
            ∑ N ∈ pool.powerset, ∫ s : ℝ, f_N N s := hlhs_N
        rw [hlhs_fold, ← integral_finsetSum _ (fun N _ => hfN_int N)]
        apply integral_congr_ae; filter_upwards with s
        dsimp only [γ_tup, F_s, c₀, w', f_N]
        unfold varyingReopenedRow
        simp only [Finset.sum_singleton, Finsupp.support_zero, Finsupp.coe_zero,
          Finset.union_empty, one_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro N _
        have hcs := hcoeff_split N (fun S => normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p S / X_out))
        dsimp only [w', χ] at hcs
        rw [show (fun N_1 => primeMark (S_v \ U_cand) lists a N_1 *
              normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p N_1 / X_out)) =
            (fun S => primeMark (S_v \ U_cand) lists a S *
              normTwistedSource (wFresh : ℝ → ℂ) s (primeProductNorm p S / X_out)) from rfl]
        linear_combination (𝓕 g_ξ) s * c₀ * kernelLogPhase s (Real.log (yj_tup tup)) * (-hcs)
      simp_rw [htup_eq]
      -- Pull `∫ s` across `∑ tup : ∀ i : U_cand, lists i.val`!
      let H_tup : (∀ i : U_cand, lists i.val) → ℝ → ℂ := fun tup s =>
        (𝓕 g_ξ) s * (γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z))
      have hH_int (tup : ∀ i : U_cand, lists i.val) : Integrable (H_tup tup) := by
        let w' := (∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z
        let c₀ : ℂ := tupleCoeff a tup *
          secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)
        let C_base : Finset ι → ℂ := fun N =>
          canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
            (primeMark (S_v \ U_cand) lists a) N *
          (multiplicityRow p hg pool 0 w' ^ 3 * primeSubsetRow p χ N w')
        have hexp : H_tup tup = fun s => ∑ N ∈ pool.powerset,
            (𝓕 g_ξ) s * ((c₀ * C_base N * wFresh (primeProductNorm p N / X_out)) *
              kernelLogPhase s (Real.log (yj_tup tup)) *
              kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
          funext s; dsimp only [H_tup, γ_tup, F_s, c₀, w', C_base, χ]
          unfold varyingReopenedRow canonicalSourceCoefficient normTwistedSource
          simp only [Finset.sum_singleton, Finsupp.support_zero, Finsupp.coe_zero,
            Finset.union_empty, one_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [hexp]; apply integrable_finsetSum; intro N _
        let K_N : ℂ := c₀ * C_base N * wFresh (primeProductNorm p N / X_out)
        have hcont : Continuous (fun s : ℝ =>
            K_N * kernelLogPhase s (Real.log (yj_tup tup)) *
              kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
          unfold kernelLogPhase; fun_prop
        refine ((𝓕 g_ξ).integrable.norm.mul_const ‖K_N‖).mono'
          ((𝓕 g_ξ).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
        filter_upwards with s
        change ‖(𝓕 g_ξ) s * (K_N * _ * _)‖ ≤ _
        rw [norm_mul, norm_mul, norm_mul, kernelLogPhase_norm, kernelLogPhase_norm, mul_one, mul_one]
      change (∑ tup : (∀ i : U_cand, lists i.val), ∫ s : ℝ, H_tup tup s) = _
      rw [← integral_finsetSum _ (fun tup _ => hH_int tup)]
      apply integral_congr_ae; filter_upwards with s
      dsimp only [H_tup]; rw [Finset.mul_sum]
    · intro J_hit hJp hne
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      apply Finset.sum_eq_zero; intro tup _
      unfold varyingReopenedRow
      rw [Finset.sum_singleton]
      have hpm0 : primeMark J_hit lists a ∅ = 0 := by
        unfold primeMark
        apply Finset.prod_eq_zero hi₀
        simp [primeSlot]
      simp only [Finsupp.support_zero, Finset.disjoint_empty_right, ite_true, mul_one,
        hpm0, zero_mul, Finset.sum_const_zero, mul_zero]
    · intro hnot
      exact (hnot (Finset.empty_mem_powerset _)).elim
  -- Step 2: For each `s : ℝ`, bound the `(I, z)`-weighted `L^2` sum via Cauchy-Schwarz + `sexticTuple_fiber_card_le`!
  have hcard_tup_le : ((Finset.univ : Finset (∀ i : U_cand, lists i.val)).card : ℝ) ≤
      (98 : ℝ) ^ K * P_U := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_coe, Nat.cast_prod]
    rw [Finset.prod_coe_sort U_cand (fun i => ((lists i).card : ℝ))]
    have hcard_i : ∀ i ∈ U_cand, ((lists i).card : ℝ) ≤ 98 * Z_slot i := by
      intro i hi
      have hcard_img : (lists i).card = ((lists i).image p).card :=
        (Finset.card_image_of_injOn (fun _ _ _ _ he => hinj_p he)).symm
      rw [hcard_img]
      have h2Z1 : 1 ≤ 2 * Z_slot i := by linarith [hZ1 i hi]
      have hc49 := card_finset_norm_sq_le_49_mul ((lists i).image p) h2Z1 (by
        intro x hx; obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
        exact hZ_hi i hi q hq)
      linarith only [hc49]
    calc (∏ i ∈ U_cand, ((lists i).card : ℝ))
        ≤ ∏ i ∈ U_cand, (98 * Z_slot i) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) hcard_i
      _ = (98 : ℝ) ^ U_cand.card * P_U := by
          dsimp only [P_U]; rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ (98 : ℝ) ^ K * P_U :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hU_card) hPU_pos.le
  let D₀ := (firstFrequencyDisk (2 * K_rad)).erase 0
  let D₁ := (firstFrequencyDisk (2 * K_out)).erase 0
  let E_s_base : ℝ := (98 : ℝ) ^ K * C_div * (2 * K_out) ^ eps_div * P_U * B_out
  have hEs_nn : 0 ≤ E_s_base := by dsimp only [E_s_base]; positivity
  have hpt_s_energy (s : ℝ) :
      (∑ I ∈ labels, ∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
        ‖∑ tup : (∀ i : U_cand, lists i.val),
          γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2) ≤
      E_s_base * ((1 + ‖s‖) ^ deg) ^ 2 := by
    have hγ_norm : ∀ (I : Ideal O) (z : O) (tup : ∀ i : U_cand, lists i.val),
        ‖γ_tup s I z tup‖ ≤ 1 := by
      intro I z tup
      dsimp only [γ_tup]
      rw [norm_mul, norm_mul, kernelLogPhase_norm, mul_one]
      have htc := tupleCoeff_norm_le_one (fun i hi => ha i (hU hi)) tup
      have hpre : ‖secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)‖ ≤ 1 := by
        have hh := Stage1CubeBins.supportMobius_secondPreColumn_norm_le_one p hp hg hinj hc Ψ hΨ1
          m (cubicIdealGenerator I) z (tuplePrimeSet tup)
        rwa [norm_mul, supportMobius_norm, one_mul] at hh
      exact (mul_le_mul htc hpre (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hI_sum : ∀ I ∈ labels,
        (∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
          ‖∑ tup : (∀ i : U_cand, lists i.val),
            γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2) ≤
        ((98 : ℝ) ^ K * P_U) * (C_div * (2 * K_out) ^ eps_div) *
          ∑ w ∈ D₁, (rowMajorant (‖ringComplex w‖ ^ 2 / K_out)).re * ‖F_s s I w‖ ^ 2 := by
      intro I _
      have hz_cs : ∀ z ∈ D₀,
          ‖∑ tup : (∀ i : U_cand, lists i.val),
            γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2 ≤
          ((98 : ℝ) ^ K * P_U) * ∑ tup : (∀ i : U_cand, lists i.val),
            ‖F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2 := by
        intro z _
        calc _ ≤ ((Finset.univ : Finset (∀ i : U_cand, lists i.val)).card : ℝ) *
                ∑ tup : (∀ i : U_cand, lists i.val),
                  ‖γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2 :=
              norm_sum_sq_le_card_sum_norm_sq Finset.univ _
          _ ≤ ((98 : ℝ) ^ K * P_U) * ∑ tup : (∀ i : U_cand, lists i.val),
                ‖F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2 := by
              apply mul_le_mul hcard_tup_le _
                (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
              apply Finset.sum_le_sum; intro tup _
              rw [norm_mul, mul_pow]
              exact mul_le_of_le_one_left (sq_nonneg _)
                (pow_le_one₀ (norm_nonneg _) (hγ_norm I z tup))
      -- Map `tz = (tup, z) ∈ Finset.univ ×ˢ D₀` to `φ tz := (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 * tz.2 ∈ D₁`!
      let φ : (∀ i : U_cand, lists i.val) × O → O :=
        fun tz => (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 * tz.2
      have hmaps_D₁ : ∀ tz ∈ (Finset.univ ×ˢ D₀ : Finset ((∀ i : U_cand, lists i.val) × O)),
          φ tz ∈ D₁ ∧ (rowMajorant (‖ringComplex tz.2‖ ^ 2 / K_rad)).re ≤
            (rowMajorant (‖ringComplex (φ tz)‖ ^ 2 / K_out)).re := by
        intro tz htz
        have hz_mem : tz.2 ∈ D₀ := (Finset.mem_product.mp htz).2
        have hz_ne : tz.2 ≠ 0 := (Finset.mem_erase.mp hz_mem).1
        have hz_norm : ‖ringComplex tz.2‖ ^ 2 ≤ 2 * K_rad :=
          (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp hz_mem).2
        have hg_ne : (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 ≠ 0 :=
          pow_ne_zero 4 (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j))
        have hw_ne : φ tz ≠ 0 := mul_ne_zero hg_ne hz_ne
        obtain ⟨_, hyj_Icc, hyj_eq⟩ := hyj_bounds tz.1
        have hgnorm : ‖ringComplex ((∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4)‖ ^ 2 ≤
            ((2 : ℝ) ^ K * P_U) ^ 4 := by
          have h1 : ‖ringComplex (∏ j ∈ tuplePrimeSet tz.1, p j)‖ ^ 2 =
              primeProductNorm p (tuplePrimeSet tz.1) := by
            unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
          rw [map_pow, norm_pow, ← pow_mul, show 4 * 2 = 2 * 4 by decide, pow_mul, h1, hyj_eq]
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_right hyj_Icc.2 hPU_pos.le) 4
        have hw_le_Kout : ‖ringComplex (φ tz)‖ ^ 2 ≤ K_out := by
          dsimp only [φ]
          rw [map_mul, norm_mul, mul_pow]
          calc ‖ringComplex ((∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4)‖ ^ 2 * ‖ringComplex tz.2‖ ^ 2
              ≤ ((2 : ℝ) ^ K * P_U) ^ 4 * (2 * K_rad) :=
                mul_le_mul hgnorm hz_norm (sq_nonneg _) (by positivity)
            _ = 2 * ((2 : ℝ) ^ K * P_U) ^ 4 * K_rad := by ring
            _ ≤ K_out := hK_out
        have hw_D₁ : φ tz ∈ D₁ := Finset.mem_erase.mpr ⟨hw_ne,
          (mem_firstFrequencyDisk _ _).mpr (hw_le_Kout.trans (by linarith only [hK_out_pos]))⟩
        have hrm_w : (rowMajorant (‖ringComplex (φ tz)‖ ^ 2 / K_out)).re = 1 := by
          rw [rowMajorant_one _ (div_nonneg (sq_nonneg _) hK_out_pos.le)
            ((div_le_one hK_out_pos).mpr hw_le_Kout), Complex.one_re]
        have hrm_z : (rowMajorant (‖ringComplex tz.2‖ ^ 2 / K_rad)).re ≤ 1 := by
          change sieveBump (‖ringComplex tz.2‖ ^ 2 / K_rad) ≤ 1
          exact sieveBump.le_one
        exact ⟨hw_D₁, hrm_z.trans_eq hrm_w.symm⟩
      calc (∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
              ‖∑ tup : (∀ i : U_cand, lists i.val),
                γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2)
          ≤ ∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
              (((98 : ℝ) ^ K * P_U) * ∑ tup : (∀ i : U_cand, lists i.val),
                ‖F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2) :=
            Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hz_cs z hz) (rowMajorant_nonneg _))
        _ = ((98 : ℝ) ^ K * P_U) * ∑ tz ∈ (Finset.univ ×ˢ D₀ : Finset ((∀ i : U_cand, lists i.val) × O)),
              (rowMajorant (‖ringComplex tz.2‖ ^ 2 / K_rad)).re * ‖F_s s I (φ tz)‖ ^ 2 := by
            rw [Finset.sum_product, Finset.sum_comm, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro z _
            rw [← mul_left_comm, Finset.mul_sum]
        _ ≤ ((98 : ℝ) ^ K * P_U) * ∑ tz ∈ (Finset.univ ×ˢ D₀ : Finset ((∀ i : U_cand, lists i.val) × O)),
              (rowMajorant (‖ringComplex (φ tz)‖ ^ 2 / K_out)).re * ‖F_s s I (φ tz)‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum (fun tz htz => mul_le_mul_of_nonneg_right (hmaps_D₁ tz htz).2 (sq_nonneg _))
        _ = ((98 : ℝ) ^ K * P_U) * ∑ w ∈ D₁,
              ((((Finset.univ ×ˢ D₀ : Finset ((∀ i : U_cand, lists i.val) × O)).filter (fun tz => φ tz = w)).card : ℝ) *
                ((rowMajorant (‖ringComplex w‖ ^ 2 / K_out)).re * ‖F_s s I w‖ ^ 2)) := by
            congr 1
            rw [← Finset.sum_fiberwise_of_maps_to (fun tz htz => (hmaps_D₁ tz htz).1)]
            apply Finset.sum_congr rfl; intro w _
            have hconst : ∀ tz ∈ (Finset.univ ×ˢ D₀).filter (fun tz => φ tz = w),
                (rowMajorant (‖ringComplex (φ tz)‖ ^ 2 / K_out)).re * ‖F_s s I (φ tz)‖ ^ 2 =
                  (rowMajorant (‖ringComplex w‖ ^ 2 / K_out)).re * ‖F_s s I w‖ ^ 2 := by
              intro tz htz; rw [(Finset.mem_filter.mp htz).2]
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((98 : ℝ) ^ K * P_U) * ((C_div * (2 * K_out) ^ eps_div) *
              ∑ w ∈ D₁, (rowMajorant (‖ringComplex w‖ ^ 2 / K_out)).re * ‖F_s s I w‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro w hw
            have hw_ne : w ≠ 0 := (Finset.mem_erase.mp hw).1
            have hw_norm : ‖ringComplex w‖ ^ 2 ≤ 2 * K_out :=
              (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp hw).2
            have hfib := sexticTuple_fiber_card_le p hp hcop hdisj_U D₀ hw_ne
            have hdiv_w := hdiv_le (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw_ne)
            rw [← ringComplex_norm_sq_eq_absNorm_span] at hdiv_w
            have hfib_le : (((Finset.univ ×ˢ D₀).filter (fun tz => φ tz = w)).card : ℝ) ≤
                C_div * (2 * K_out) ^ eps_div :=
              hfib.trans (hdiv_w.trans (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (sq_nonneg _) hw_norm heps_div) hC_div.le))
            exact mul_le_mul_of_nonneg_right hfib_le
              (mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _))
        _ = _ := by ring
    calc _ ≤ ∑ I ∈ labels, ((98 : ℝ) ^ K * P_U) * (C_div * (2 * K_out) ^ eps_div) *
              ∑ w ∈ D₁, (rowMajorant (‖ringComplex w‖ ^ 2 / K_out)).re * ‖F_s s I w‖ ^ 2 :=
          Finset.sum_le_sum hI_sum
      _ = ((98 : ℝ) ^ K * P_U * C_div * (2 * K_out) ^ eps_div) *
            rowFamilyEnergy labels (F_s s) K_out := by
          rw [← Finset.mul_sum, ← rowFamilyEnergy_eq_sum labels (F_s s) K_out hK_out_pos]
          ring
      _ ≤ ((98 : ℝ) ^ K * P_U * C_div * (2 * K_out) ^ eps_div) *
            (B_out * (1 + ‖s‖) ^ (2 * deg)) :=
          mul_le_mul_of_nonneg_left (hrow_s s) (by positivity)
      _ = E_s_base * ((1 + ‖s‖) ^ deg) ^ 2 := by
          rw [Nat.mul_comm 2 deg, pow_mul]; dsimp only [E_s_base]; ring
  -- Step 3: Integrate `s : ℝ` via `InverseMoment.common_measure_energy` on `labels ×ˢ D₀`!
  let idx_set := labels ×ˢ D₀
  let h_wt : ℝ → ℝ := fun s => (1 + ‖s‖) ^ deg
  have hh_pos (s : ℝ) : 0 < h_wt s := by dsimp only [h_wt]; positivity
  let b_meas : ℝ → ℂ := fun s => (𝓕 g_ξ) s * (h_wt s : ℂ)
  let wt_iz : Ideal O × O → ℂ := fun iz =>
    ((Real.sqrt ((rowMajorant (‖ringComplex iz.2‖ ^ 2 / K_rad)).re) : ℝ) : ℂ)
  have hwt_sq (iz : Ideal O × O) : ‖wt_iz iz‖ ^ 2 = (rowMajorant (‖ringComplex iz.2‖ ^ 2 / K_rad)).re := by
    dsimp only [wt_iz]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (rowMajorant_nonneg _)]
  let f_meas_raw : Ideal O × O → ℝ → ℂ := fun iz s =>
    (wt_iz iz * ∑ tup : (∀ i : U_cand, lists i.val),
      γ_tup s iz.1 iz.2 tup * F_s s iz.1 ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * iz.2)) /
      (h_wt s : ℂ)
  let f_meas : idx_set → ℝ → ℂ := fun iz => f_meas_raw iz.val
  have hb_norm (s : ℝ) : ‖b_meas s‖ = h_wt s * ‖(𝓕 g_ξ) s‖ := by
    dsimp only [b_meas]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s), mul_comm]
  have hb_int : Integrable (fun s => ‖b_meas s‖) := by
    simpa only [hb_norm] using CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g_ξ) deg
  have hbf_eq (iz : idx_set) (s : ℝ) : b_meas s * f_meas iz s =
      wt_iz iz.val * ((𝓕 g_ξ) s * ∑ tup : (∀ i : U_cand, lists i.val),
        γ_tup s iz.val.1 iz.val.2 tup * F_s s iz.val.1 ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * iz.val.2)) := by
    dsimp only [b_meas, f_meas, f_meas_raw]
    have hn : (h_wt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hh_pos s).ne'
    field_simp [hn]
  have hbf_int (iz : idx_set) : Integrable (fun s => b_meas s * f_meas iz s) := by
    simp_rw [hbf_eq iz]
    apply Integrable.const_mul
    simp_rw [Finset.mul_sum]; apply integrable_finsetSum; intro tup _
    let I := iz.val.1
    let z := iz.val.2
    let w' := (∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z
    let c₀ : ℂ := tupleCoeff a tup *
      secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)
    let C_base : Finset ι → ℂ := fun N =>
      canonicalSourceCoefficient p hg Ψ m (cubicIdealGenerator I)
        (primeMark (S_v \ U_cand) lists a) N *
      (multiplicityRow p hg pool 0 w' ^ 3 * primeSubsetRow p χ N w')
    have hexp : (fun s => (𝓕 g_ξ) s * (γ_tup s I z tup * F_s s I w')) =
        fun s => ∑ N ∈ pool.powerset,
          (𝓕 g_ξ) s * ((c₀ * C_base N * wFresh (primeProductNorm p N / X_out)) *
            kernelLogPhase s (Real.log (yj_tup tup)) *
            kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
      funext s; dsimp only [γ_tup, F_s, c₀, w', C_base, χ]
      unfold varyingReopenedRow canonicalSourceCoefficient normTwistedSource
      simp only [Finset.sum_singleton, Finsupp.support_zero, Finsupp.coe_zero,
        Finset.union_empty, one_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    change Integrable (fun s => (𝓕 g_ξ) s * (γ_tup s I z tup * F_s s I w'))
    rw [hexp]; apply integrable_finsetSum; intro N _
    let K_N : ℂ := c₀ * C_base N * wFresh (primeProductNorm p N / X_out)
    have hcont : Continuous (fun s : ℝ =>
        K_N * kernelLogPhase s (Real.log (yj_tup tup)) *
          kernelLogPhase s (Real.log (primeProductNorm p N / X_out))) := by
      unfold kernelLogPhase; fun_prop
    refine ((𝓕 g_ξ).integrable.norm.mul_const ‖K_N‖).mono'
      ((𝓕 g_ξ).continuous.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
    filter_upwards with s
    change ‖(𝓕 g_ξ) s * (K_N * _ * _)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, kernelLogPhase_norm, kernelLogPhase_norm, mul_one, mul_one]
  have hf_energy (s : ℝ) : (∑ iz : idx_set, ‖f_meas iz s‖ ^ 2) ≤ E_s_base := by
    have hsum_eq : (∑ iz : idx_set, ‖f_meas iz s‖ ^ 2) =
        (∑ I ∈ labels, ∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
          ‖∑ tup : (∀ i : U_cand, lists i.val),
            γ_tup s I z tup * F_s s I ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2) /
          (h_wt s) ^ 2 := by
      change (∑ iz : idx_set, ‖f_meas_raw iz.val s‖ ^ 2) = _
      rw [Finset.sum_coe_sort idx_set (fun iz => ‖f_meas_raw iz s‖ ^ 2), Finset.sum_product, Finset.sum_div]
      apply Finset.sum_congr rfl; intro I _
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro z _
      dsimp only [f_meas_raw]
      have hnorm_hwt : ‖(h_wt s : ℂ)‖ = h_wt s := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh_pos s)]
      rw [norm_div, norm_mul, hnorm_hwt, div_pow, mul_pow, hwt_sq (I, z)]
    rw [hsum_eq, div_le_iff₀ (sq_pos_of_pos (hh_pos s))]
    exact hpt_s_energy s
  have hcme := InverseMoment.common_measure_energy volume b_meas f_meas E_s_base
    hEs_nn hb_int hbf_int hf_energy
  rw [rowFamilyEnergy_eq_sum labels _ K_rad hK_rad]
  have hlhs_eq :
      (∑ I ∈ labels, ∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
        ‖varyingReopenedRow p hg pool {0} (fun _ => 1) Ψ m (cubicIdealGenerator I)
          (fun v T => primeMark S_v lists a (T ∪ v.support) *
            normTwistedSource (om : ℝ → ℂ) ξ (primeProductNorm p T / X)) z‖ ^ 2) =
      ∑ iz : idx_set, ‖∫ s : ℝ, b_meas s * f_meas iz s‖ ^ 2 := by
    let g_iz : Ideal O × O → ℝ := fun iz =>
      ‖∫ s : ℝ, wt_iz iz * ((𝓕 g_ξ) s * ∑ tup : (∀ i : U_cand, lists i.val),
        γ_tup s iz.1 iz.2 tup * F_s s iz.1 ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * iz.2))‖ ^ 2
    have hrhs_eq : (∑ iz : idx_set, ‖∫ s : ℝ, b_meas s * f_meas iz s‖ ^ 2) =
        ∑ iz ∈ idx_set, g_iz iz := by
      have hcongr : ∀ iz : idx_set, ‖∫ s : ℝ, b_meas s * f_meas iz s‖ ^ 2 = g_iz iz.val := by
        intro iz; simp_rw [hbf_eq iz]; rfl
      simp_rw [hcongr]
      exact Finset.sum_coe_sort idx_set g_iz
    rw [hrhs_eq, Finset.sum_product]
    apply Finset.sum_congr rfl; intro I _
    apply Finset.sum_congr rfl; intro z _
    dsimp only [g_iz]
    rw [integral_const_mul, norm_mul, mul_pow, hwt_sq (I, z), ← hpt_int I z]
  rw [hlhs_eq]
  have hb_int_le : (∫ s : ℝ, ‖b_meas s‖) ≤ C_ft * (1 + ‖ξ‖) ^ (deg + (volume : Measure ℝ).integrablePower) := by
    simp_rw [hb_norm]
    exact (hft ξ).trans (mul_le_mul_of_nonneg_right (by dsimp only [C_ft]; linarith only []) (by positivity))
  have hb_int_nn : 0 ≤ ∫ s : ℝ, ‖b_meas s‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hb_sq : (∫ s : ℝ, ‖b_meas s‖) ^ 2 ≤
      C_ft ^ 2 * (1 + ‖ξ‖) ^ (2 * (deg + (volume : Measure ℝ).integrablePower)) := by
    have hsq := pow_le_pow_left₀ hb_int_nn hb_int_le 2
    rwa [mul_pow, ← pow_mul, Nat.mul_comm] at hsq
  calc (∑ iz : idx_set, ‖∫ s : ℝ, b_meas s * f_meas iz s‖ ^ 2)
      ≤ E_s_base * (∫ s : ℝ, ‖b_meas s‖) ^ 2 := hcme
    _ ≤ E_s_base * (C_ft ^ 2 * (1 + ‖ξ‖) ^ (2 * (deg + (volume : Measure ℝ).integrablePower))) :=
        mul_le_mul_of_nonneg_left hb_sq hEs_nn
    _ = C_tr * C_div * (2 * K_out) ^ eps_div * P_U * B_out *
          (1 + ‖ξ‖) ^ (2 * (deg + (volume : Measure ℝ).integrablePower)) := by
        dsimp only [C_tr, E_s_base]; ring

/-! ### Part IV: Cell-summed `globalPriorityOriginalEnergy` at `Q = {0}` -/

section DualQZeroCellEnergy

open InverseFirstGlobalCaps InverseFirstGlobalParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource
open InverseMomentFirstOriginalProfile InverseMomentFirstLiveCaps
open InverseMomentFirstSecondHeightCost InverseMomentFirstChildWindows
open IdealDivisorBound CompletedHeight Stage1DualRowMoments Stage1ReciprocityAndUnpuncture
open Stage1DualSixthFreeEnergy Stage1ParentPoissonEnergy Stage1CubeBins
open SubSevenEighthsHighTransport ProbeFinalAssemblyCertifiedBands

/-- Structural decomposition and dyadic bounds for elements of
`labelParentCell p pool {0} (fun _ _ => 1) k.1 k.2.1 k.2.2` at `Q = {0}`:
every `x` has `x.cube = ⟨0, 0, ∅, ∅⟩`, `x.firstDivisor ⊆ x.firstCommon`, cube-related dyadic
exponents equal to `0`, and `x` is uniquely determined by
`((x.firstCommon, x.firstDivisor), x.quotientSupport)`. -/
lemma qzero_labelParentCell_data
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (k : JointKey) {U η : ℝ} (hU : 1 < U) (h2 : 2 ≤ U ^ η) :
    let cell := labelParentCell p pool {0} (fun _ _ => 1) k.1 k.2.1 k.2.2
    (∀ x ∈ cell,
      x.cube = ⟨0, 0, ∅, ∅⟩ ∧
      x.firstDivisor ⊆ x.firstCommon ∧
      x.firstCommon ⊆ pool ∧
      x.quotientSupport ⊆ pool ∧
      dyadicExponent U (k.1 0) = 0 ∧
      dyadicExponent U (k.1 1) = 0 ∧
      dyadicExponent U (k.1 4) = 0 ∧
      dyadicExponent U k.2.2 = 0 ∧
      (U ^ dyadicExponent U (k.1 2) ≤ primeProductNorm p x.firstCommon ∧
        primeProductNorm p x.firstCommon ≤ U ^ (dyadicExponent U (k.1 2) + η)) ∧
      (U ^ dyadicExponent U (k.1 3) ≤ primeProductNorm p x.firstDivisor ∧
        primeProductNorm p x.firstDivisor ≤ U ^ (dyadicExponent U (k.1 3) + η)) ∧
      (U ^ dyadicExponent U k.2.1 ≤ primeProductNorm p x.quotientSupport ∧
        primeProductNorm p x.quotientSupport ≤ U ^ (dyadicExponent U k.2.1 + η))) ∧
    Set.InjOn (fun x : Source ι 0 => ((x.firstCommon, x.firstDivisor), x.quotientSupport)) cell := by
  intro cell
  have hexp1 : dyadicExponent U (InverseSecondSourceBlocks.dyadIndex 1) = 0 := by
    have hb := actual_dyadic_exponent_cap U η 1 0 hU h2 le_rfl (by simp)
    exact le_antisymm hb.2 hb.1
  have hcell_mem : ∀ x ∈ cell,
      x.cube = ⟨0, 0, ∅, ∅⟩ ∧
      x.firstDivisor ⊆ x.firstCommon ∧
      x.firstCommon ⊆ pool ∧
      x.quotientSupport ⊆ pool ∧
      dyadicExponent U (k.1 0) = 0 ∧
      dyadicExponent U (k.1 1) = 0 ∧
      dyadicExponent U (k.1 4) = 0 ∧
      dyadicExponent U k.2.2 = 0 ∧
      (U ^ dyadicExponent U (k.1 2) ≤ primeProductNorm p x.firstCommon ∧
        primeProductNorm p x.firstCommon ≤ U ^ (dyadicExponent U (k.1 2) + η)) ∧
      (U ^ dyadicExponent U (k.1 3) ≤ primeProductNorm p x.firstDivisor ∧
        primeProductNorm p x.firstDivisor ≤ U ^ (dyadicExponent U (k.1 3) + η)) ∧
      (U ^ dyadicExponent U k.2.1 ≤ primeProductNorm p x.quotientSupport ∧
        primeProductNorm p x.quotientSupport ≤ U ^ (dyadicExponent U k.2.1 + η)) := by
    intro x hx
    have hlb := labelParentCell_bounds p hp pool {0} (fun _ _ => 1) k.1 k.2.1 k.2.2 U η hU h2 x hx
    have hpc := hlb.1
    have hj_eq : InverseSecondSourceBlocks.dyadIndex (jNorm p (toOriginal x)) = k.2.2 :=
      (Finset.mem_filter.mp hx).2
    obtain ⟨o, ho, D, hD_pow, _hs, hfill⟩ :=
      (mem_parentCell p pool {0} (fun _ _ => 1) k.1 k.2.1 x).mp hpc
    have ho_mem : o ∈ firstOriginalOuter pool {0} := (Finset.mem_filter.mp ho).1
    have hog : outerGate p k.1 o := (Finset.mem_filter.mp ho).2
    obtain ⟨hrcf, hC_pow, hD0_pow⟩ := (mem_firstOriginalOuter pool {0} o).mp ho_mem
    obtain ⟨hl0, hr0, hadm⟩ := (mem_reopenedCubeFamily {0} o.1).mp hrcf
    rw [Finset.mem_singleton] at hl0 hr0
    have hsup0 : o.1.support = ∅ := by
      unfold CubeCoordinates.support; simp [hl0, hr0]
    have hld0 : o.1.leftDivisor = ∅ := Finset.subset_empty.mp (hsup0 ▸ hadm.1)
    have hrd0 : o.1.rightDivisor = ∅ := Finset.subset_empty.mp (hsup0 ▸ hadm.2)
    have ho1_eq : o.1 = ⟨0, 0, ∅, ∅⟩ := by
      ext <;> simp [hl0, hr0, hld0, hrd0]
    have hcube_eq : x.cube = ⟨0, 0, ∅, ∅⟩ := by
      rw [← hfill]; exact ho1_eq
    have hcps0 : cubePrincipalSupport o.1.support o.1.leftExponent o.1.rightExponent
        o.1.leftBit o.1.rightBit = ∅ := by
      rw [hsup0]; simp [cubePrincipalSupport]
    have hD0_sub : x.firstDivisor ⊆ x.firstCommon := by
      rw [← hfill]
      change o.2.2 ⊆ o.2.1
      have hsub := Finset.mem_powerset.mp hD0_pow
      rwa [hcps0, Finset.union_empty] at hsub
    have hC_sub : x.firstCommon ⊆ pool := by
      rw [← hfill]
      exact (Finset.mem_powerset.mp hC_pow).trans Finset.sdiff_subset
    have hD_sub : x.quotientSupport ⊆ pool := by
      rw [← hfill]
      exact Finset.mem_powerset.mp hD_pow
    have hon0 : InverseFirstGlobalCaps.outerNorms p o 0 = 1 := by
      unfold InverseFirstGlobalCaps.outerNorms; simp [hsup0, aLabel, primeProduct]
    have hon1 : InverseFirstGlobalCaps.outerNorms p o 1 = 1 := by
      unfold InverseFirstGlobalCaps.outerNorms; simp [hsup0, aLabel, primeProduct]
    have hon4 : InverseFirstGlobalCaps.outerNorms p o 4 = 1 := by
      unfold InverseFirstGlobalCaps.outerNorms; simp [hsup0, cubeActiveSupport, primeProductNorm]
    have hjn1 : jNorm p (toOriginal x) = 1 := by
      rw [← hfill, toOriginal_fill, toOriginal_ofOriginal]
      unfold jNorm; simp [hsup0, jLabel, primeProduct]
    have hk0 : k.1 0 = InverseSecondSourceBlocks.dyadIndex 1 := by
      have h := hog 0; rw [hon0] at h; exact h.symm
    have hk1 : k.1 1 = InverseSecondSourceBlocks.dyadIndex 1 := by
      have h := hog 1; rw [hon1] at h; exact h.symm
    have hk4 : k.1 4 = InverseSecondSourceBlocks.dyadIndex 1 := by
      have h := hog 4; rw [hon4] at h; exact h.symm
    have hkj : k.2.2 = InverseSecondSourceBlocks.dyadIndex 1 := by
      rw [hjn1] at hj_eq; exact hj_eq.symm
    have hid_b := parentCell_ideal_bounds p hp pool {0} (fun _ _ => 1) k.1 k.2.1 U η hU h2 x hpc
    have hnm_b := parentCell_norm_bounds p hp pool {0} (fun _ _ => 1) k.1 k.2.1 U η hU h2 x hpc
    have hD0_norm : U ^ dyadicExponent U (k.1 3) ≤ primeProductNorm p x.firstDivisor ∧
        primeProductNorm p x.firstDivisor ≤ U ^ (dyadicExponent U (k.1 3) + η) := by
      have h3 := hid_b.2.1
      rwa [sourceIdeal_norm p x.firstDivisor] at h3
    have hD_norm : U ^ dyadicExponent U k.2.1 ≤ primeProductNorm p x.quotientSupport ∧
        primeProductNorm p x.quotientSupport ≤ U ^ (dyadicExponent U k.2.1 + η) := by
      have hq := hnm_b.2.2
      rwa [hnm_b.2.1] at hq
    exact ⟨hcube_eq, hD0_sub, hC_sub, hD_sub,
      by rw [hk0, hexp1], by rw [hk1, hexp1], by rw [hk4, hexp1], by rw [hkj, hexp1],
      hid_b.1, hD0_norm, hD_norm⟩
  refine ⟨hcell_mem, ?_⟩
  intro x₁ hx₁ x₂ hx₂ heq
  have hc1 := (hcell_mem x₁ hx₁).1
  have hc2 := (hcell_mem x₂ hx₂).1
  have h12 := Prod.ext_iff.mp (Prod.ext_iff.mp heq).1
  have hq := (Prod.ext_iff.mp heq).2
  apply InverseFirstPriorityParents.Source.ext
  · exact hc1.trans hc2.symm
  · exact h12.1
  · exact h12.2
  · exact hq
  · exact funext (fun i => Fin.elim0 i)

/-- When `primeMark J lists_v a E ≠ 0` on pairwise-disjoint slot lists `lists_v` with prime norms
at least `U ^ (D.ell i / d_outer)` (`1 / 2 ≤ d_outer ≤ 5 / 6`) and `primeProductNorm p E ≤ U ^ B_E`,
the extracted slot width satisfies `∑ i ∈ J, D.ell i / d_outer ≤ B_E` and `‖primeMark J lists_v a E‖`
is bounded by a constant depending only on `(B_E, D.rmin, J.card)`. -/
lemma qzero_primeMark_hit_bound
    {Δ : ℝ} (D : Parameters.HighData Δ)
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (J : Finset (Fin D.N)) (lists_v : Fin D.N → Finset ι)
    (hdisj : (J : Set (Fin D.N)).PairwiseDisjoint lists_v)
    (a : Fin D.N → ι → ℂ) (ha : ∀ i ∈ J, ∀ q ∈ lists_v i, ‖a i q‖ ≤ 1)
    {U d_outer B_E : ℝ} (hU : 1 < U) (hd_lo : 1 / 2 ≤ d_outer) (hd_hi : d_outer ≤ 5 / 6)
    (_hB0 : 0 ≤ B_E)
    (hZ_lo : ∀ i ∈ J, ∀ q ∈ lists_v i, U ^ (D.ell i / d_outer) ≤ ‖ringComplex (p q)‖ ^ 2)
    (E : Finset ι) (hE_norm : primeProductNorm p E ≤ U ^ B_E)
    (hne : primeMark J lists_v a E ≠ 0) :
    let c_min := (21 / 20 : ℝ) * D.rmin
    (∑ i ∈ J, D.ell i / d_outer) ≤ B_E ∧
      ‖primeMark J lists_v a E‖ ≤ ((⌈B_E / c_min⌉₊ + 1 : ℕ) : ℝ) ^ J.card := by
  intro c_min
  have hU_pos : 0 < U := zero_lt_one.trans hU
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have hrmin_pos : 0 < D.rmin := D.rmin_pos
  have hc_min_pos : 0 < c_min := by dsimp only [c_min]; positivity
  have hnonempty : ∀ i ∈ J, (lists_v i ∩ E).Nonempty := by
    intro i hi
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    unfold primeMark
    apply Finset.prod_eq_zero hi
    unfold primeSlot
    have h0 : ∀ q ∈ lists_v i, (if q ∈ E then a i q else 0) = 0 := by
      intro q hq
      by_cases hqE : q ∈ E
      · exact False.elim (Finset.notMem_empty q (hempty ▸ Finset.mem_inter.mpr ⟨hq, hqE⟩))
      · simp [hqE]
    exact Finset.sum_eq_zero h0
  let pick : J → ι := fun i => Classical.choose (hnonempty i.val i.property)
  have hpick_mem : ∀ i : J, pick i ∈ lists_v i.val ∧ pick i ∈ E := fun i =>
    Finset.mem_inter.mp (Classical.choose_spec (hnonempty i.val i.property))
  have hpick_inj : Function.Injective pick := by
    intro i₁ i₂ heq
    by_contra hne_i
    have hne_val : i₁.val ≠ i₂.val := fun h => hne_i (Subtype.ext h)
    exact Finset.disjoint_left.mp (hdisj i₁.property i₂.property hne_val)
      (hpick_mem i₁).1 (heq ▸ (hpick_mem i₂).1)
  let E_sub : Finset ι := Finset.univ.image pick
  have hE_sub : E_sub ⊆ E := by
    intro q hq; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq; exact (hpick_mem i).2
  have hp_norm_ge1 : ∀ q : ι, 1 ≤ ‖ringComplex (p q)‖ ^ 2 :=
    fun q => SchwartzPlanePoisson.one_le_eisenstein_norm_sq (p q) (hp q)
  have hpN_le : ∀ F ⊆ E, primeProductNorm p F ≤ primeProductNorm p E := by
    intro F hF
    unfold primeProductNorm
    rw [map_prod, norm_prod, ← Finset.prod_pow, map_prod, norm_prod, ← Finset.prod_pow,
      ← Finset.prod_sdiff hF]
    exact le_mul_of_one_le_left (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      (Finset.one_le_prod (fun q _ => hp_norm_ge1 q))
  have hz_le : (∑ i ∈ J, D.ell i / d_outer) ≤ B_E := by
    have hrpow_le : U ^ (∑ i ∈ J, D.ell i / d_outer) ≤ U ^ B_E := by
      rw [Real.rpow_sum_of_pos hU_pos, ← Finset.prod_coe_sort J]
      calc (∏ i : J, U ^ (D.ell i.val / d_outer))
          ≤ ∏ i : J, ‖ringComplex (p (pick i))‖ ^ 2 :=
            Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hU_pos.le _)
              (fun i _ => hZ_lo i.val i.property (pick i) (hpick_mem i).1)
        _ = primeProductNorm p E_sub := by
            dsimp only [E_sub]; unfold primeProductNorm
            rw [map_prod, norm_prod, ← Finset.prod_pow,
              Finset.prod_image (fun _ _ _ _ h => hpick_inj h)]
        _ ≤ primeProductNorm p E := hpN_le E_sub hE_sub
        _ ≤ U ^ B_E := hE_norm
    exact (Real.rpow_le_rpow_left_iff hU).mp hrpow_le
  refine ⟨hz_le, ?_⟩
  let M_hit : ℝ := ((⌈B_E / c_min⌉₊ + 1 : ℕ) : ℝ)
  have hslot_le : ∀ i ∈ J, ‖primeSlot (lists_v i) (a i) E‖ ≤ M_hit := by
    intro i hi
    have hc_le : c_min ≤ D.ell i / d_outer := by
      have h78 : (7 / 8 : ℝ) * D.rmin ≤ D.ell i := (D.slots_bounds i).2.1
      rw [le_div_iff₀ hd_pos]
      dsimp only [c_min]
      nlinarith only [h78, hd_hi, hrmin_pos]
    have hcard_inter : (((lists_v i ∩ E).card : ℕ) : ℝ) ≤ M_hit := by
      have hrpow_int : U ^ ((((lists_v i ∩ E).card : ℕ) : ℝ) * c_min) ≤ U ^ B_E := by
        rw [mul_comm, Real.rpow_mul hU_pos.le, Real.rpow_natCast]
        calc (U ^ c_min) ^ (lists_v i ∩ E).card
            = ∏ _q ∈ lists_v i ∩ E, U ^ c_min := (Finset.prod_const _).symm
          _ ≤ ∏ q ∈ lists_v i ∩ E, ‖ringComplex (p q)‖ ^ 2 := by
              apply Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hU_pos.le _)
              intro q hq
              exact (Real.rpow_le_rpow_of_exponent_le hU.le hc_le).trans
                (hZ_lo i hi q (Finset.mem_inter.mp hq).1)
          _ = primeProductNorm p (lists_v i ∩ E) := by
              unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
          _ ≤ primeProductNorm p E := hpN_le (lists_v i ∩ E) Finset.inter_subset_right
          _ ≤ U ^ B_E := hE_norm
      have hmul_le : (((lists_v i ∩ E).card : ℕ) : ℝ) * c_min ≤ B_E :=
        (Real.rpow_le_rpow_left_iff hU).mp hrpow_int
      have hdiv_le : (((lists_v i ∩ E).card : ℕ) : ℝ) ≤ B_E / c_min :=
        (le_div_iff₀ hc_min_pos).mpr hmul_le
      have hceil : B_E / c_min ≤ (⌈B_E / c_min⌉₊ : ℝ) := Nat.le_ceil _
      dsimp only [M_hit]; push_cast; linarith only [hdiv_le, hceil]
    unfold primeSlot
    rw [Finset.sum_ite_mem]
    calc ‖∑ q ∈ lists_v i ∩ E, a i q‖
        ≤ ∑ q ∈ lists_v i ∩ E, ‖a i q‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ lists_v i ∩ E, (1 : ℝ) :=
          Finset.sum_le_sum (fun q hq => ha i hi q (Finset.mem_inter.mp hq).1)
      _ = (((lists_v i ∩ E).card : ℕ) : ℝ) := by simp
      _ ≤ M_hit := hcard_inter
  unfold primeMark
  rw [norm_prod]
  calc (∏ i ∈ J, ‖primeSlot (lists_v i) (a i) E‖)
      ≤ ∏ _i ∈ J, M_hit := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hslot_le
    _ = M_hit ^ J.card := Finset.prod_const _

/-- Pointwise slice bound for `parentPoisson` on a `Q = {0}` parent cell: eliminates `(C₀, D₀)` via
`fresh_input_parent_mask`, `inputConjugateRow_old_divisor_mask`, and `inputConjugateRow_q0_clean`,
and bounds `‖globalPriorityOuter‖ ≤ coefficientBound` and `‖rowMajorant‖ ≤ 1`. -/
lemma parentPoisson_qzero_slice_le
    {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (cell : Finset (Source ι 0))
    (hcell0 : ∀ x ∈ cell, x.cube = ⟨0, 0, ∅, ∅⟩ ∧ x.firstDivisor ⊆ x.firstCommon)
    (kq : ℕ) (negative : Bool)
    (extra_b : CubeCoordinates ι → Finset ι)
    (hextra_b : extra_b = if negative then (fun q => q.rightExponent.support)
      else (fun q => q.leftExponent.support))
    (Ψ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ u‖ ≤ 1) (m : O)
    (S_rem J : Finset σ) (lists_v : σ → Finset ι) (a : σ → ι → ℂ)
    (omega_b : 𝓢(ℝ, ℂ)) {lo_o hi_o : ℝ} (hlo_o : 0 < lo_o)
    (hs_ob : Function.support (omega_b : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o)
    (X_col t_ht Y_cell : ℝ) (hX_col_pos : 0 < X_col) (hY_cell_pos : 0 < Y_cell)
    (ray : RayCharacter × RayCharacter) (core : FirstCoreIndex) :
    (∑ x ∈ cell,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x => (‖commonSelector p (fun _ => 1) kq x.quotientSupport‖ : ℂ)) x *
      (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
      parentPoisson p hp hg hinj pool negative Ψ m S_rem J
        (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)).re ≤
    coefficientBound * ∑ x ∈ cell,
      ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
        (‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j)) pool
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
            (m * ∏ i ∈ x.quotientSupport, p i) 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅
              (principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht) X_col) 0‖ ^ 2 +
          ∑ z ∈ (rowMajorantBall Y_cell).erase 0,
            ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j)) pool
              (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
              (m * ∏ i ∈ x.quotientSupport, p i) 1 1
              (markedRadial p (S_rem \ J) lists_v a ∅
                (principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht) X_col)
              (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2) := by
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  let V_win : 𝓢(ℝ, ℂ) := principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht
  let χ_p := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  have hcb_pos : 0 < coefficientBound := coefficientBound_pos
  have hextr_eq : ∀ x ∈ cell,
      wholeExtractedSupport (fun x' => extra_b x'.cube) negative x =
        x.firstCommon ∪ x.quotientSupport := by
    intro x hx
    rw [wholeExtractedSupport, extractedSupport, (hcell0 x hx).1, hextra_b]
    cases negative <;> simp
  have houter_norm : ∀ x ∈ cell,
      ‖globalPriorityOuter p hg negative Ψ m ray core
        (fun x' => (‖commonSelector p (fun _ => 1) kq x'.quotientSupport‖ : ℂ)) x‖ ≤
      coefficientBound := by
    intro x _
    unfold globalPriorityOuter
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hsel := live_selector_norm_le_one p (fun _ => (1 : ℂ)) (by simp) kq x.quotientSupport
    have hpo := priorityOuter_norm p hg x.cube negative Ψ m (fun _ => 1) ray core
      x.quotientSupport (by simp) (hΨ1 _)
    exact (mul_le_mul hsel hpo (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc _ ≤ ‖∑ x ∈ cell,
              globalPriorityOuter p hg negative Ψ m ray core
                (fun x => (‖commonSelector p (fun _ => 1) kq x.quotientSupport‖ : ℂ)) x *
              (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
              parentPoisson p hp hg hinj pool negative Ψ m S_rem J
                (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖ :=
          Complex.re_le_norm _
    _ ≤ ∑ x ∈ cell,
          ‖globalPriorityOuter p hg negative Ψ m ray core
              (fun x => (‖commonSelector p (fun _ => 1) kq x.quotientSupport‖ : ℂ)) x *
            (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
            parentPoisson p hp hg hinj pool negative Ψ m S_rem J
              (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖ :=
          norm_sum_le _ _
    _ = ∑ x ∈ cell,
          ‖globalPriorityOuter p hg negative Ψ m ray core
              (fun x => (‖commonSelector p (fun _ => 1) kq x.quotientSupport‖ : ℂ)) x *
            (‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 : ℝ) *
            parentPoisson p hp hg hinj pool negative Ψ m S_rem J
              (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖ := by
          apply Finset.sum_congr rfl; intro x hx
          rw [hextr_eq x hx]
    _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro x hx
          obtain ⟨hcube0, hDC⟩ := hcell0 x hx
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have ho1 := houter_norm x hx
          have hpp_eq := parentPoisson_eq_rowMajorantBall_sum p hp hg hinj hc x
            extra_b pool negative Ψ m S_rem J lists_v a omega_b lo_o hi_o hlo_o hs_ob
            X_col t_ht Y_cell hX_col_pos hY_cell_pos ray core
          have hz_clean : ∀ z : O,
              inputConjugateRow p χ_p pool Ψ₀
                (secondParentPuncture p m (parent p x)) (secondParentLabel p (parent p x))
                (secondParentDivisor p (parent p x))
                (markedRadial p (S_rem \ J)
                  (residualLists p negative (fun i => lists_v i \ extra_b x.cube) (parent p x))
                  a ∅ V_win X_col) z =
              inputConjugateRow p χ_p pool Ψ₀
                (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                (gcdElement p x.firstCommon x.firstDivisor * z) := by
            intro z
            have hq_par : (parent p x).quotient = InverseInitialArithmetic.sourceIdeal p x.quotientSupport := rfl
            rw [← fresh_input_parent_mask p hg (parent p x) pool x.quotientSupport hq_par Ψ₀ m _ z]
            have hb0_1 : b0Label p (parent p x).cube.support
                (fun i => (parent p x).cube.leftExponent i + (parent p x).cube.rightExponent i)
                (parent p x).cube.leftBit (parent p x).cube.rightBit = 1 := by
              change b0Label p x.cube.support _ _ _ = 1
              rw [hcube0]; simp [CubeCoordinates.support, b0Label, primeProduct]
            have hlbl_eq : secondParentLabel p (parent p x) = ∏ i ∈ x.firstCommon, p i := by
              change (∏ i ∈ x.firstCommon, p i) * jLabel p x.cube.support _ _ _ = _
              rw [hcube0]; simp [CubeCoordinates.support, jLabel, primeProduct]
            have hdiv_eq : secondParentDivisor p (parent p x) = ∏ i ∈ x.firstDivisor, p i := rfl
            have hres_eq : residualLists p negative (fun i => lists_v i \ extra_b x.cube) (parent p x) =
                fun i => lists_v i \ (x.firstCommon ∪ x.quotientSupport) := by
              funext i; unfold residualLists; rw [quotientSupport_parent p hinj x]
              change (lists_v i \ extra_b x.cube) \
                (((if negative then x.cube.rightDivisor else x.cube.leftDivisor) ∪ x.firstCommon) ∪
                  x.quotientSupport) = _
              rw [hcube0, hextra_b]
              cases negative <;> simp
            rw [hb0_1, mul_one, hlbl_eq, hdiv_eq, hres_eq,
              ← inputConjugateRow_old_divisor_mask p hg pool Ψ₀
                (m * ∏ i ∈ x.quotientSupport, p i) (∏ i ∈ x.firstCommon, p i)
                (∏ i ∈ x.firstDivisor, p i) _ z]
            exact inputConjugateRow_q0_clean p hcop hg pool Ψ₀ m hDC x.quotientSupport
              (S_rem \ J) lists_v a V_win X_col z
          have hpp_norm : ‖parentPoisson p hp hg hinj pool negative Ψ m S_rem J
              (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖ ≤
              ‖inputConjugateRow p χ_p pool Ψ₀
                  (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                  (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2 +
                ∑ z ∈ (rowMajorantBall Y_cell).erase 0,
                  ‖inputConjugateRow p χ_p pool Ψ₀
                    (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                    (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                    (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2 := by
            rw [hpp_eq]
            calc _ ≤ ∑ z ∈ rowMajorantBall Y_cell,
                      ‖rowMajorant (‖ringComplex z‖ ^ 2 / Y_cell) *
                        (‖inputConjugateRow p χ_p pool Ψ₀
                          (secondParentPuncture p m (parent p x)) (secondParentLabel p (parent p x))
                          (secondParentDivisor p (parent p x))
                          (markedRadial p (S_rem \ J)
                            (residualLists p negative (fun i => lists_v i \ extra_b x.cube) (parent p x))
                            a ∅ V_win X_col) z‖ ^ 2 : ℝ)‖ := norm_sum_le _ _
              _ ≤ ∑ z ∈ rowMajorantBall Y_cell,
                    ‖inputConjugateRow p χ_p pool Ψ₀
                      (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                      (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                      (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2 := by
                  apply Finset.sum_le_sum; intro z _
                  rw [hz_clean z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
                  have hrm1 : ‖rowMajorant (‖ringComplex z‖ ^ 2 / Y_cell)‖ ≤ 1 := by
                    rw [rowMajorant, sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
                      abs_of_nonneg sieveBump.nonneg]
                    exact sieveBump.le_one
                  exact mul_le_of_le_one_left (sq_nonneg _) hrm1
              _ ≤ _ := by
                  by_cases h0_mem : (0 : O) ∈ rowMajorantBall Y_cell
                  · rw [← Finset.add_sum_erase _ _ h0_mem, mul_zero]
                  · have h_eq : (rowMajorantBall Y_cell).erase 0 = rowMajorantBall Y_cell := by
                      ext z; simp only [Finset.mem_erase, and_iff_right_iff_imp]
                      rintro hz rfl; exact h0_mem hz
                    rw [h_eq]; exact le_add_of_nonneg_left (sq_nonneg _)
          calc ‖globalPriorityOuter p hg negative Ψ m ray core
                  (fun x => (‖commonSelector p (fun _ => 1) kq x.quotientSupport‖ : ℂ)) x‖ *
                ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
                ‖parentPoisson p hp hg hinj pool negative Ψ m S_rem J
                  (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖
              ≤ coefficientBound * ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
                  ‖parentPoisson p hp hg hinj pool negative Ψ m S_rem J
                    (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right ho1 (sq_nonneg _)) (norm_nonneg _)
            _ ≤ _ := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpp_norm (sq_nonneg _)) hcb_pos.le

/-- Combinatorial decomposition of `cell_J` over `(CD_set, D_set)` and `gcdElement` fibers on an
abstract index type `ι`, avoiding unfolding concrete prime pools during `Finset.image` and
`Finset.filter` reasoning. -/
private lemma cell_J_z0_and_gcd_fiber_bound
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (cell_J : Finset (Source ι 0))
    (hinj_J : Set.InjOn (fun x : Source ι 0 =>
      ((x.firstCommon, x.firstDivisor), x.quotientSupport)) cell_J)
    (hDC_J : ∀ x ∈ cell_J, x.firstDivisor ⊆ x.firstCommon)
    (U B_c δ_c t_q η τ Lcap t_dual ε_div C_div Y_cell W_exp C_hit B_om : ℝ)
    (hU1 : 1 < U) (hBc_0 : 0 ≤ B_c) (hBc_hi : B_c ≤ 3 * Lcap + 15 * η + τ) (htq_0 : 0 ≤ t_q)
    (hη_pos : 0 < η) (hη1 : η ≤ 1) (_hτ_pos : 0 < τ) (hτ1 : τ ≤ 1)
    (hLcap : 1 ≤ Lcap) (ht_pos : 0 < t_dual)
    (hε_div : 0 < ε_div) (hε_div_eq : ε_div = t_dual / (80 * (6 * Lcap + 30)))
    (hC_div : 0 < C_div)
    (hdiv_le : ∀ I : Ideal O, I ≠ 0 →
      ((idealDivisors I).card : ℝ) ≤ C_div * (I.absNorm : ℝ) ^ ε_div)
    (hY_cell_pos : 0 < Y_cell) (hW_exp_le1 : W_exp ≤ 1)
    (hY_W_eq : U ^ (2 * B_c - δ_c + 2 * η) * Y_cell = U ^ W_exp)
    (hnorms_J : ∀ x ∈ cell_J,
      primeProductNorm p x.firstCommon ≤ U ^ (B_c + η) ∧
      U ^ δ_c ≤ primeProductNorm p x.firstDivisor ∧
      primeProductNorm p x.quotientSupport ≤ U ^ (t_q + η))
    (hChit_pos : 0 < C_hit)
    (w_pm : Source ι 0 → ℝ) (hw_pm_le : ∀ x ∈ cell_J, w_pm x ≤ C_hit)
    (g_z0 : Source ι 0 → ℝ) (hg_z0_nn : ∀ x ∈ cell_J, 0 ≤ g_z0 x)
    (hg_z0_le : ∀ x ∈ cell_J, g_z0 x ≤ B_om ^ 2)
    (g_row : Finset ι → O → ℝ) (hg_row_nn : ∀ D_q w, 0 ≤ g_row D_q w)
    (K_W : ℝ) (hKW_nn : 0 ≤ K_W)
    (hD_sum_W : ∀ D_q : Finset ι, primeProductNorm p D_q ≤ U ^ (t_q + η) →
      (∑ w ∈ (firstFrequencyDisk (2 * U ^ W_exp)).erase 0, g_row D_q w) ≤ K_W) :
    (∑ x ∈ cell_J, w_pm x * g_z0 x) ≤
      C_hit * (49 * 49 * C_div * (2 : ℝ) ^ ε_div * B_om ^ 2) *
        U ^ (B_c + t_q + 2 * η + t_dual / 4) ∧
    (∑ x ∈ cell_J, w_pm x *
      ∑ z ∈ (rowMajorantBall Y_cell).erase 0,
        g_row x.quotientSupport (gcdElement p x.firstCommon x.firstDivisor * z)) ≤
      C_hit * (49 * U ^ (t_q + η)) *
        ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) * K_W) := by
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  let CD_set : Finset (Finset ι × Finset ι) :=
    cell_J.image (fun x => (x.firstCommon, x.firstDivisor))
  let D_set : Finset (Finset ι) :=
    cell_J.image (fun x => x.quotientSupport)
  have hCD_DC : ∀ cd ∈ CD_set, cd.2 ⊆ cd.1 := by
    intro cd hcd; obtain ⟨x, hxJ, rfl⟩ := Finset.mem_image.mp hcd
    exact hDC_J x hxJ
  have hCD_norms : ∀ cd ∈ CD_set,
      primeProductNorm p cd.1 ≤ U ^ (B_c + η) ∧ U ^ δ_c ≤ primeProductNorm p cd.2 := by
    intro cd hcd; obtain ⟨x, hxJ, rfl⟩ := Finset.mem_image.mp hcd
    exact ⟨(hnorms_J x hxJ).1, (hnorms_J x hxJ).2.1⟩
  have hD_norms : ∀ D_q ∈ D_set, primeProductNorm p D_q ≤ U ^ (t_q + η) := by
    intro D_q hDq; obtain ⟨x, hxJ, rfl⟩ := Finset.mem_image.mp hDq
    exact (hnorms_J x hxJ).2.2
  have hprod_p_inj : Function.Injective (fun F : Finset ι => ∏ i ∈ F, p i) := by
    intro F₁ F₂ heq
    apply span_finset_prod_injective p hp hcop
    dsimp only
    rw [← SchwartzPlanePoisson.span_finset_prime_product,
      ← SchwartzPlanePoisson.span_finset_prime_product]
    exact congrArg (fun x => Ideal.span {x}) heq
  have hcard_D_set : (D_set.card : ℝ) ≤ 49 * U ^ (t_q + η) := by
    rw [← Finset.card_image_of_injOn (fun _ _ _ _ h => hprod_p_inj h)]
    exact card_finset_norm_sq_le_49_mul (D_set.image (fun F => ∏ i ∈ F, p i))
      (Real.one_le_rpow hU1.le (by linarith only [htq_0, hη_pos]))
      (fun y hy => by
        obtain ⟨D_q, hDq, rfl⟩ := Finset.mem_image.mp hy
        have h1 : ‖ringComplex (∏ i ∈ D_q, p i)‖ ^ 2 = primeProductNorm p D_q := by
          unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
        rw [h1]; exact hD_norms D_q hDq)
  have hcard_CD_set : (CD_set.card : ℝ) ≤
      49 * C_div * (2 : ℝ) ^ ε_div * U ^ (B_c + η + t_dual / 4) := by
    let C_only : Finset (Finset ι) := CD_set.image Prod.fst
    have hcard_C : (C_only.card : ℝ) ≤ 49 * U ^ (B_c + η) := by
      rw [← Finset.card_image_of_injOn (fun _ _ _ _ h => hprod_p_inj h)]
      exact card_finset_norm_sq_le_49_mul (C_only.image (fun F => ∏ i ∈ F, p i))
        (Real.one_le_rpow hU1.le (by linarith only [hBc_0, hη_pos]))
        (fun y hy => by
          obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨cd, hcd, rfl⟩ := Finset.mem_image.mp hC₀
          have h1 : ‖ringComplex (∏ i ∈ cd.1, p i)‖ ^ 2 = primeProductNorm p cd.1 := by
            unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
          rw [h1]; exact (hCD_norms cd hcd).1)
    have hfib_C : ∀ C₀ ∈ C_only,
        (((CD_set.filter (fun cd => cd.1 = C₀)).card : ℕ) : ℝ) ≤
          C_div * (2 : ℝ) ^ ε_div * U ^ (t_dual / 4) := by
      intro C₀ hC₀
      obtain ⟨cd₀, hcd₀, rfl⟩ := Finset.mem_image.mp hC₀
      let I_C : Ideal O := Ideal.span {∏ i ∈ cd₀.1, p i}
      have hIC_ne : I_C ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      let φ_D : Finset ι × Finset ι → Ideal O :=
        fun cd => ∏ i ∈ cd.2, Ideal.span {p i}
      have hmaps : ∀ cd ∈ CD_set.filter (fun cd => cd.1 = cd₀.1), φ_D cd ∈ idealDivisors I_C := by
        intro cd hcd
        have hcd_mem := (Finset.mem_filter.mp hcd).1
        have hc_eq : cd.1 = cd₀.1 := (Finset.mem_filter.mp hcd).2
        have hsub : cd.2 ⊆ cd₀.1 := hc_eq ▸ hCD_DC cd hcd_mem
        rw [mem_idealDivisors hIC_ne]
        dsimp only [φ_D, I_C]
        rw [← SchwartzPlanePoisson.span_finset_prime_product,
          Ideal.span_singleton_dvd_span_singleton_iff_dvd]
        exact Finset.prod_dvd_prod_of_subset cd.2 cd₀.1 p hsub
      have hinj_D : Set.InjOn φ_D (CD_set.filter (fun cd => cd.1 = cd₀.1)) := by
        intro cd₁ h₁ cd₂ h₂ hφ
        have hc1 : cd₁.1 = cd₀.1 := (Finset.mem_filter.mp h₁).2
        have hc2 : cd₂.1 = cd₀.1 := (Finset.mem_filter.mp h₂).2
        exact Prod.ext (hc1.trans hc2.symm) (span_finset_prod_injective p hp hcop hφ)
      have hc_le : (((CD_set.filter (fun cd => cd.1 = cd₀.1)).card : ℕ) : ℝ) ≤
          ((idealDivisors I_C).card : ℝ) := by
        exact_mod_cast Finset.card_le_card_of_injOn φ_D hmaps hinj_D
      have hd_bound := hdiv_le I_C hIC_ne
      have hIC_norm : (I_C.absNorm : ℝ) ≤ 2 * U ^ (3 * Lcap + 16 * η + τ) := by
        dsimp only [I_C]
        rw [← ringComplex_norm_sq_eq_absNorm_span]
        have h1 : ‖ringComplex (∏ i ∈ cd₀.1, p i)‖ ^ 2 = primeProductNorm p cd₀.1 := by
          unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
        rw [h1]
        exact (hCD_norms cd₀ hcd₀).1.trans
          ((Real.rpow_le_rpow_of_exponent_le hU1.le
            (show B_c + η ≤ 3 * Lcap + 16 * η + τ by linarith only [hBc_hi, hη_pos])).trans
            (by linarith [Real.rpow_pos_of_pos hU_pos (3 * Lcap + 16 * η + τ)]))
      have hrp_IC : (I_C.absNorm : ℝ) ^ ε_div ≤ (2 : ℝ) ^ ε_div * U ^ (t_dual / 4) := by
        calc (I_C.absNorm : ℝ) ^ ε_div
            ≤ (2 * U ^ (3 * Lcap + 16 * η + τ)) ^ ε_div :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hIC_norm hε_div.le
          _ = (2 : ℝ) ^ ε_div * U ^ ((3 * Lcap + 16 * η + τ) * ε_div) := by
              rw [Real.mul_rpow zero_le_two (Real.rpow_nonneg hU_pos.le _),
                ← Real.rpow_mul hU_pos.le]
          _ ≤ (2 : ℝ) ^ ε_div * U ^ (t_dual / 4) := by
              apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg zero_le_two _)
              apply Real.rpow_le_rpow_of_exponent_le hU1.le
              have hden : 3 * Lcap + 16 * η + τ ≤ 6 * Lcap + 30 := by
                linarith only [hLcap, hη1, hτ1]
              have hmul := mul_le_mul_of_nonneg_right hden hε_div.le
              have heq : (6 * Lcap + 30) * ε_div = t_dual / 80 := by
                rw [hε_div_eq]; field_simp
              linarith only [hmul, heq, ht_pos]
      exact hc_le.trans (hd_bound.trans
        ((mul_le_mul_of_nonneg_left hrp_IC hC_div.le).trans_eq (mul_assoc _ _ _).symm))
    have hcard_sum : (CD_set.card : ℝ) = ∑ _cd ∈ CD_set, (1 : ℝ) := by simp
    rw [hcard_sum, ← Finset.sum_fiberwise_of_maps_to (g := Prod.fst)
      (fun cd hcd => Finset.mem_image_of_mem Prod.fst hcd)]
    calc (∑ C₀ ∈ C_only, ∑ _cd ∈ CD_set.filter (fun cd => cd.1 = C₀), (1 : ℝ))
        ≤ ∑ _C₀ ∈ C_only, (C_div * (2 : ℝ) ^ ε_div * U ^ (t_dual / 4)) := by
          apply Finset.sum_le_sum; intro C₀ hC₀
          simpa using hfib_C C₀ hC₀
      _ = (C_only.card : ℝ) * (C_div * (2 : ℝ) ^ ε_div * U ^ (t_dual / 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (49 * U ^ (B_c + η)) * (C_div * (2 : ℝ) ^ ε_div * U ^ (t_dual / 4)) :=
          mul_le_mul_of_nonneg_right hcard_C
            (mul_nonneg (mul_nonneg hC_div.le (Real.rpow_nonneg zero_le_two _))
              (Real.rpow_nonneg hU_pos.le _))
      _ = 49 * C_div * (2 : ℝ) ^ ε_div * (U ^ (B_c + η) * U ^ (t_dual / 4)) := by ring
      _ = 49 * C_div * (2 : ℝ) ^ ε_div * U ^ (B_c + η + t_dual / 4) := by
          rw [← Real.rpow_add hU_pos]
  have hcard_cellJ : (cell_J.card : ℝ) ≤
      49 * 49 * C_div * (2 : ℝ) ^ ε_div * U ^ (B_c + t_q + 2 * η + t_dual / 4) := by
    have hmaps_prod : ∀ x ∈ cell_J,
        ((x.firstCommon, x.firstDivisor), x.quotientSupport) ∈ CD_set ×ˢ D_set :=
      fun x hxJ => Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ hxJ, Finset.mem_image_of_mem _ hxJ⟩
    have hc_prod : (cell_J.card : ℝ) ≤ (CD_set.card : ℝ) * (D_set.card : ℝ) := by
      have hnat := (Finset.card_le_card_of_injOn _ hmaps_prod hinj_J).trans_eq
        (Finset.card_product CD_set D_set)
      exact_mod_cast hnat
    calc (cell_J.card : ℝ)
        ≤ (49 * C_div * (2 : ℝ) ^ ε_div * U ^ (B_c + η + t_dual / 4)) *
            (49 * U ^ (t_q + η)) :=
          hc_prod.trans (mul_le_mul hcard_CD_set hcard_D_set
            (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC_div.le)
              (Real.rpow_nonneg zero_le_two _)) (Real.rpow_nonneg hU_pos.le _)))
      _ = 49 * 49 * C_div * (2 : ℝ) ^ ε_div *
            (U ^ (B_c + η + t_dual / 4) * U ^ (t_q + η)) := by ring
      _ = _ := by
          rw [← Real.rpow_add hU_pos]
          exact congrArg (fun x : ℝ => 49 * 49 * C_div * (2 : ℝ) ^ ε_div * U ^ x) (by ring)
  -- Part 1: `z = 0` sum bound!
  have hz0_part : (∑ x ∈ cell_J, w_pm x * g_z0 x) ≤
      C_hit * (49 * 49 * C_div * (2 : ℝ) ^ ε_div * B_om ^ 2) *
        U ^ (B_c + t_q + 2 * η + t_dual / 4) := by
    calc (∑ x ∈ cell_J, w_pm x * g_z0 x)
        ≤ ∑ _x ∈ cell_J, (C_hit * B_om ^ 2) :=
          Finset.sum_le_sum (fun x hxJ =>
            mul_le_mul (hw_pm_le x hxJ) (hg_z0_le x hxJ) (hg_z0_nn x hxJ) hChit_pos.le)
      _ = (cell_J.card : ℝ) * (C_hit * B_om ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (49 * 49 * C_div * (2 : ℝ) ^ ε_div * U ^ (B_c + t_q + 2 * η + t_dual / 4)) *
            (C_hit * B_om ^ 2) :=
          mul_le_mul_of_nonneg_right hcard_cellJ (mul_nonneg hChit_pos.le (sq_nonneg _))
      _ = _ := by ring
  -- Part 2: `z ∈ B_nz` sum bound via `gcdElement` fiber map!
  let B_nz : Finset O := (rowMajorantBall Y_cell).erase 0
  let W_ball : Finset O := (firstFrequencyDisk (2 * U ^ W_exp)).erase 0
  have hgcd_maps : ∀ cd ∈ CD_set, ∀ z ∈ B_nz,
      gcdElement p cd.1 cd.2 * z ∈ W_ball := by
    intro cd hcd z hz
    have hz_ne : z ≠ 0 := (Finset.mem_erase.mp hz).1
    have hz_ball : z ∈ rowMajorantBall Y_cell := (Finset.mem_erase.mp hz).2
    have hz_norm : ‖ringComplex z‖ ^ 2 ≤ 2 * Y_cell := by
      change z ∈ (finite_norm_sublevel (Real.sqrt (2 * Y_cell))).toFinset at hz_ball
      rw [Set.Finite.mem_toFinset] at hz_ball
      have hle : ‖ringComplex z‖ ≤ Real.sqrt (2 * Y_cell) := hz_ball
      calc ‖ringComplex z‖ ^ 2 ≤ (Real.sqrt (2 * Y_cell)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = 2 * Y_cell := Real.sq_sqrt (by linarith only [hY_cell_pos])
    have hw_ne : gcdElement p cd.1 cd.2 * z ≠ 0 :=
      mul_ne_zero (gcdElement_ne_zero p hp cd.1 cd.2) hz_ne
    have hgcd_id := gcdElement_norm_sq p (hCD_DC cd hcd)
    obtain ⟨hC_hi, hD0_lo⟩ := hCD_norms cd hcd
    have hgcd_le : ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 ≤ U ^ (2 * B_c - δ_c + 2 * η) := by
      have hmul_le : ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 * U ^ δ_c ≤
          U ^ (2 * (B_c + η)) := by
        calc ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 * U ^ δ_c
            ≤ ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 * primeProductNorm p cd.2 :=
              mul_le_mul_of_nonneg_left hD0_lo (sq_nonneg _)
          _ = (primeProductNorm p cd.1) ^ 2 := hgcd_id
          _ ≤ (U ^ (B_c + η)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hC_hi 2
          _ = U ^ (2 * (B_c + η)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hU_pos.le]
              exact congrArg (fun x : ℝ => U ^ x) (by ring)
      have hdiv : ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 ≤ U ^ (2 * (B_c + η)) / U ^ δ_c :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hU_pos _)).mpr hmul_le
      refine hdiv.trans_eq ?_
      rw [← Real.rpow_sub hU_pos]
      exact congrArg (fun x : ℝ => U ^ x) (by ring)
    refine Finset.mem_erase.mpr ⟨hw_ne, (mem_firstFrequencyDisk _ _).mpr ?_⟩
    rw [map_mul, norm_mul, mul_pow]
    calc ‖ringComplex (gcdElement p cd.1 cd.2)‖ ^ 2 * ‖ringComplex z‖ ^ 2
        ≤ U ^ (2 * B_c - δ_c + 2 * η) * (2 * Y_cell) :=
          mul_le_mul hgcd_le hz_norm (sq_nonneg _) (Real.rpow_nonneg hU_pos.le _)
      _ = 2 * (U ^ (2 * B_c - δ_c + 2 * η) * Y_cell) := by ring
      _ = 2 * U ^ W_exp := by rw [hY_W_eq]
  have hgcd_fib_le : ∀ w ∈ W_ball,
      ((((CD_set ×ˢ B_nz).filter (fun t => gcdElement p t.1.1 t.1.2 * t.2 = w)).card : ℕ) : ℝ) ≤
        C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4) := by
    intro w hw
    have hw_ne : w ≠ 0 := (Finset.mem_erase.mp hw).1
    have hw_norm : ‖ringComplex w‖ ^ 2 ≤ 2 * U ^ W_exp :=
      (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp hw).2
    have hfib := gcdElement_fiber_card_le p hp hcop CD_set hCD_DC B_nz hw_ne
    have hd_w := hdiv_le (Ideal.span {w}) (Ideal.span_singleton_eq_bot.not.mpr hw_ne)
    rw [← ringComplex_norm_sq_eq_absNorm_span] at hd_w
    have hw_2U : ‖ringComplex w‖ ^ 2 ≤ 2 * U :=
      hw_norm.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hU1.le hW_exp_le1).trans_eq (Real.rpow_one U))
        zero_le_two)
    have hrp : (‖ringComplex w‖ ^ 2) ^ ε_div ≤ (2 : ℝ) ^ ε_div * U ^ ε_div := by
      calc (‖ringComplex w‖ ^ 2) ^ ε_div
          ≤ (2 * U) ^ ε_div := Real.rpow_le_rpow (sq_nonneg _) hw_2U hε_div.le
        _ = (2 : ℝ) ^ ε_div * U ^ ε_div := Real.mul_rpow zero_le_two hU_pos.le
    have hd_sq : ((idealDivisors (Ideal.span {w})).card : ℝ) ^ 2 ≤
        (C_div * ((2 : ℝ) ^ ε_div * U ^ ε_div)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (hd_w.trans (mul_le_mul_of_nonneg_left hrp hC_div.le)) 2
    have h2ε_le : 2 * ε_div ≤ t_dual / 4 := by
      rw [hε_div_eq]
      have hden : (80 * (6 * Lcap + 30) : ℝ) ≥ 8 := by linarith only [hLcap]
      have : 2 * (t_dual / (80 * (6 * Lcap + 30))) ≤ 2 * (t_dual / 8) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left ht_pos.le (by norm_num) hden) zero_le_two
      linarith only [this]
    calc _ ≤ (C_div * ((2 : ℝ) ^ ε_div * U ^ ε_div)) ^ 2 := hfib.trans hd_sq
      _ = C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (2 * ε_div) := by
          rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ε_div),
            ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast (U ^ ε_div),
            ← Real.rpow_mul hU_pos.le]
          norm_num; ring_nf
      _ ≤ C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hU1.le h2ε_le)
            (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg zero_le_two _))
  let f_cd_D : (Finset ι × Finset ι) × Finset ι → ℝ := fun p_x =>
    ∑ z ∈ B_nz, g_row p_x.2 (gcdElement p p_x.1.1 p_x.1.2 * z)
  have hsub_prod : cell_J.image (fun x => ((x.firstCommon, x.firstDivisor), x.quotientSupport)) ⊆
      CD_set ×ˢ D_set := by
    intro y hy; obtain ⟨x, hxJ, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hxJ, Finset.mem_image_of_mem _ hxJ⟩
  have hcell_to_prod :
      (∑ x ∈ cell_J, w_pm x * f_cd_D ((x.firstCommon, x.firstDivisor), x.quotientSupport)) ≤
      C_hit * ∑ D_q ∈ D_set, ∑ cd ∈ CD_set, f_cd_D (cd, D_q) := by
    calc _ ≤ ∑ x ∈ cell_J, C_hit *
              f_cd_D ((x.firstCommon, x.firstDivisor), x.quotientSupport) :=
          Finset.sum_le_sum (fun x hxJ => mul_le_mul_of_nonneg_right (hw_pm_le x hxJ)
            (Finset.sum_nonneg (fun _ _ => hg_row_nn _ _)))
      _ = C_hit * ∑ y ∈ cell_J.image (fun x => ((x.firstCommon, x.firstDivisor), x.quotientSupport)),
            f_cd_D y := by
          rw [← Finset.mul_sum, Finset.sum_image hinj_J]
      _ ≤ C_hit * ∑ y ∈ CD_set ×ˢ D_set, f_cd_D y :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub_prod
              (fun _ _ _ => Finset.sum_nonneg (fun _ _ => hg_row_nn _ _)))
            hChit_pos.le
      _ = C_hit * ∑ D_q ∈ D_set, ∑ cd ∈ CD_set, f_cd_D (cd, D_q) := by
          rw [Finset.sum_product, Finset.sum_comm]
  have hCD_z_to_W : ∀ D_q ∈ D_set,
      (∑ cd ∈ CD_set, f_cd_D (cd, D_q)) ≤
      (C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) *
        ∑ w ∈ W_ball, g_row D_q w := by
    intro D_q _
    dsimp only [f_cd_D]
    rw [← Finset.sum_product']
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun t : (Finset ι × Finset ι) × O => gcdElement p t.1.1 t.1.2 * t.2)
      (fun t ht => hgcd_maps t.1 (Finset.mem_product.mp ht).1 t.2 (Finset.mem_product.mp ht).2),
      Finset.mul_sum]
    apply Finset.sum_le_sum; intro w hw
    have hconst : ∀ t ∈ (CD_set ×ˢ B_nz).filter (fun t => gcdElement p t.1.1 t.1.2 * t.2 = w),
        g_row D_q (gcdElement p t.1.1 t.1.2 * t.2) = g_row D_q w :=
      fun t ht => by rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hgcd_fib_le w hw) (hg_row_nn D_q w)
  have hnz_part :
      (∑ x ∈ cell_J, w_pm x * ∑ z ∈ B_nz,
        g_row x.quotientSupport (gcdElement p x.firstCommon x.firstDivisor * z)) ≤
      C_hit * (49 * U ^ (t_q + η)) *
        ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) * K_W) := by
    have hcoeff_nn : 0 ≤ C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg zero_le_two _))
        (Real.rpow_nonneg hU_pos.le _)
    calc _ ≤ C_hit * ∑ D_q ∈ D_set, ∑ cd ∈ CD_set, f_cd_D (cd, D_q) := hcell_to_prod
      _ ≤ C_hit * ∑ _D_q ∈ D_set,
            ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) * K_W) := by
          apply mul_le_mul_of_nonneg_left _ hChit_pos.le
          apply Finset.sum_le_sum; intro D_q hDq
          exact (hCD_z_to_W D_q hDq).trans
            (mul_le_mul_of_nonneg_left (hD_sum_W D_q (hD_norms D_q hDq)) hcoeff_nn)
      _ = C_hit * ((D_set.card : ℝ) *
            ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) * K_W)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C_hit * ((49 * U ^ (t_q + η)) *
            ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (t_dual / 4)) * K_W)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcard_D_set (mul_nonneg hcoeff_nn hKW_nn))
            hChit_pos.le
      _ = _ := by ring
  exact ⟨hz0_part, hnz_part⟩

/-- Unpunctured subslot energy bound for a single Schwartz window `omega_b` and orientation
`negative`, combining `exists_bad12_base_transfer_on_pool`,
`principalWindow_markedRadial_fourier_l2_le_factored`,
`dual_sixth_free_factored_energy_lists_sdiff_padded`, and
`dual_factored_coarse_bound_lists_sdiff`. -/
private theorem dual_qzero_unpunc_single_omega
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (omega_b : 𝓢(ℝ, ℂ)) {lo_o hi_o : ℝ} (hlo_o : 0 < lo_o) (hlh_o : lo_o ≤ hi_o)
    (hs_ob : Function.support (omega_b : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o)
    (negative : Bool) (M_drop : ℕ) (Lcap η τ : ℝ) (hLcap : 1 ≤ Lcap)
    (hη_pos : 0 < η) (hτ_pos : 0 < τ) :
    ∃ (τ_d B_p : ℝ) (deg_w : ℕ),
      0 < τ_d ∧ 2 * τ_d ≤ D_dual.t ∧ 2 ≤ B_p ∧
      ∀ data : RowData, ∃ C_unp U_unp : ℝ, 0 < C_unp ∧ 2 ≤ U_unp ∧
      ∀ U : ℝ, U_unp ≤ U →
      ∀ Dpool : ℕ, B_p * U ^ (Lcap + 2) ≤ (Dpool : ℝ) →
      let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
        fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
      let p := poolPrimary F_pool
      let hp := poolPrimary_ne_zero F_pool hFa
      let hcop := poolPrimary_coprime F_pool hFa
      let hg := poolPrimary_good F_pool hFa
      let hinj : Function.Injective (fun j : primePool F_pool => Ideal.span {p j}) :=
        fun j₁ j₂ h => Subtype.ext (by dsimp only [p] at h; simpa only [poolPrimary_span F_pool hFa] using h)
      let base := InverseInitialRayAttachment.elementCharacter
        (InverseInitialConjugateEnergy.conjugateIdealCharacter
          (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T B_c t_q x6 X_col : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r_param → r_param ≤ 19 / 26 →
        0 ≤ θ_s → θ_s ≤ 1 →
        0 ≤ ell_in → ell_in ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell_in →
        0 ≤ V₀ → 0 ≤ pad_T → 0 ≤ B_c → 0 ≤ t_q → 0 ≤ x6 →
      let u_act := θ_s * stage1Width r_param
      let z_rem_th := (1 - θ_s) * ((1 - r_param) / 2) + θ_s * stage1RemWidth r_param
      let r_new := F_p - V₀ - 3 * ell_in - u_act
      let H_free := (1 - 6 * u_act) - 6 * ell_in - 6 * x6
      r_new ≤ Lcap → 0 < H_free → X_col = U ^ (r_new - B_c - t_q) →
      ∀ (S_rem J : Finset (Fin D.N)), J ⊆ S_rem →
        (∑ i ∈ J, D.ell i / d_outer) ≤ B_c + t_q + 2 * η →
        (∑ i ∈ S_rem, D.ell i / d_outer) ≤ z_rem_th - z_Jv + pad_T →
        F_p - ((∑ i ∈ S_rem, D.ell i / d_outer) + u_act + z_Jv) + 2 * η ≤ r_param →
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      (∀ j ∈ S_rem, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full lists_v : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ S_rem, lists_full j = InverseInitialCommonLists.poolList F_pool
          (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (∀ j ∈ S_rem, lists_v j ⊆ lists_full j) →
        (∀ j ∈ S_rem, ((lists_full j \ lists_v j).card : ℝ) ≤ (M_drop : ℝ)) →
        (S_rem : Set (Fin D.N)).PairwiseDisjoint lists_v →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ S_rem, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val /
            star (idealCoeff (deletedBase data) q.val)) →
      (∀ j ∈ S_rem, ∀ q ∈ lists_v j,
        Z_slot j ≤ ‖ringComplex (p q)‖ ^ 2 ∧ ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot j ∧ ‖a j q‖ ≤ 1) →
      ∀ (Ψ₀ : O →* ℂ), CanonicalCoefficientClass.IsBaseRayTwist base Ψ₀ → (∀ u, ‖Ψ₀ u‖ ≤ 1) →
      ∀ (U0_set : Finset FreeRow), (∀ u₀ ∈ U0_set, rowNorm u₀ ≤ 2 * U ^ (H_free - 17 * η - τ)) →
      ∀ (t_ht : ℝ) (S'' : Finset (Fin D.N)), S'' ⊆ S_rem \ J →
      ∀ (X₁ : ℝ), 0 < X₁ → X₁ * (∏ i ∈ (S_rem \ J) \ S'', Z_slot i) ≤ X_col →
        (∑ u₀ ∈ U0_set, X₁⁻¹ *
          ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            Finset.univ Ψ₀ 1 1 1
            (fun U_set => primeMark S'' lists_v a U_set *
              principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht
                (primeProductNorm p U_set / X₁)) u₀.val‖ ^ 2) ≤
        C_unp * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) *
          (1 + ‖t_ht‖) ^ (2 * deg_w) := by
  obtain ⟨wFresh, af, bf, B_w, haf, habf, hBw0, hs_w, hBw, hfour⟩ :=
    principalWindow_markedRadial_fourier_l2_le_factored omega_b hlo_o hlh_o hs_ob D.N
  obtain ⟨τ_d, J_sf, hτ_p, hτ_le, hsf_all⟩ :=
    dual_sixth_free_factored_energy_lists_sdiff_padded hβ51 D D_dual h2000_eps h2000_e
      hfine_dual emb hemb F_dual wFresh haf habf hBw0 hs_w hBw M_drop
  let N_tail : ℕ := ⌈((D.N : ℝ) + 20 + 6 * Lcap) / τ_d⌉₊ + 1
  obtain ⟨C_four, hC_f, hfour⟩ := hfour J_sf N_tail
  let deg_w : ℕ := J_sf + N_tail + (volume : Measure ℝ).integrablePower
  let B_p : ℝ := max 2 bf + 2
  have hBp2 : 2 ≤ B_p := by dsimp only [B_p]; linarith [le_max_left 2 bf]
  have hbf_pos : 0 < bf := haf.trans_le habf
  refine ⟨τ_d, B_p, deg_w, hτ_p, hτ_le, hBp2, ?_⟩
  intro data
  obtain ⟨C_sf, U_sf, hC_sf, hU_sf, hsf⟩ := hsf_all data
  have hev_norm : ∀ᶠ U : ℝ in atTop, (373248 : ℝ) ≤ U ^ (17 * η) :=
    (tendsto_rpow_atTop (by positivity : 0 < 17 * η)).eventually (eventually_ge_atTop 373248)
  have hev_pi : ∀ᶠ U : ℝ in atTop, 32 * Real.pi ≤ U ^ (τ_d / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < τ_d / 2)).eventually (eventually_ge_atTop (32 * Real.pi))
  obtain ⟨U_n0, hU_n0⟩ := eventually_atTop.mp (hev_norm.and hev_pi)
  let U_unp : ℝ := max 2 (max U_sf U_n0)
  have hU_unp2 : 2 ≤ U_unp := le_max_left _ _
  let C_cr : ℝ := (4 : ℝ) ^ D.N * ((max 1 (M_drop : ℝ)) ^ 2) ^ D.N *
    (49 * bf * (B_w * 49 * (1 + bf) ^ 2) ^ 2 * (9604 : ℝ) ^ D.N + 1)
  have hCcr_nn : 0 ≤ C_cr :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (sq_nonneg _) _))
      (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hbf_pos.le) (sq_nonneg _))
        (pow_nonneg (by norm_num) _)) zero_le_one)
  let C_unp : ℝ := 4 * C_four * (C_sf + C_cr + 1)
  have hC_unp_pos : 0 < C_unp :=
    mul_pos (mul_pos (by norm_num) hC_f)
      (add_pos_of_nonneg_of_pos (add_nonneg hC_sf.le hCcr_nn) zero_lt_one)
  refine ⟨C_unp, U_unp, hC_unp_pos, hU_unp2, ?_⟩
  intro U hU Dpool hDpool q_per F_pool hFa p hp hcop hg hinj base
    d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T B_c t_q x6 X_col
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0 hpad0 hBc_0 htq_0 hx6_0
    u_act z_rem_th r_new H_free hrn_hi hHf_pos hX_col_eq
    S_rem J hJ_sub hzJ_act_le hz_Srem hFp_r Z_slot Z_dual hlarge_Z
    lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
    ζ_base hζ_re hζ_im a ha_eq hlists_v_b Ψ₀ hΨ₀_base hΨ₀_norm
    U0_set hU0_norm t_ht S'' hS'' X₁ hX₁ hX₁_le
  letI : ∀ i : primePool F_pool, (Ideal.span {p i}).IsMaximal :=
    fun i => by dsimp only [p]; rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU2 : 2 ≤ U := hU_unp2.trans hU
  have hU1 : 1 < U := by linarith only [hU2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have ht_pos : 0 < D_dual.t := D_dual.t_pos
  obtain ⟨h373, h32pi⟩ := hU_n0 U (((le_max_right _ _).trans (le_max_right _ _)).trans hU)
  have hZ_slot_ge1 : ∀ j : Fin D.N, 1 ≤ Z_slot j :=
    fun j => Real.one_le_rpow hU1.le (div_nonneg (D.slots_bounds j).1.le hd_pos.le)
  have hZ_slot_pos : ∀ j : Fin D.N, 0 < Z_slot j := fun j => zero_lt_one.trans_le (hZ_slot_ge1 j)
  have hZ_slot_hi : ∀ j : Fin D.N, Z_slot j ≤ U := by
    intro j; dsimp only [Z_slot]
    have hle1 : D.ell j / d_outer ≤ 1 := by
      have h200 : D.ell j ≤ (1 / 200 : ℝ) * D.t := (D.slots_bounds j).2.2
      have hts : D.t ≤ 1 / 100000000 := D.t_small
      rw [div_le_one hd_pos]; linarith only [h200, hts, hd_lo]
    exact (Real.rpow_le_rpow_of_exponent_le hU1.le hle1).trans_eq (Real.rpow_one U)
  have hS''_rem : S'' ⊆ S_rem := hS''.trans Finset.sdiff_subset
  have hS''_card : S''.card ≤ D.N :=
    (Finset.card_le_univ S'').trans_eq (Fintype.card_fin D.N)
  have hHf_lo : -D_dual.t ≤ H_free := by linarith only [hHf_pos, ht_pos]
  have hmax_Hf : max 0 H_free = H_free := max_eq_right hHf_pos.le
  obtain ⟨idx_bad, hbad_tr⟩ := exists_bad12_base_transfer_on_pool (σ := Fin D.N) q_per Dpool base Ψ₀ hΨ₀_base
  let S_free : Finset FreeRow := U0_set.image (fun u₀ => (bad12FreeSplit idx_bad u₀).1)
  have hS_free_norm : ∀ u ∈ S_free, rowNorm u ≤ U ^ max 0 H_free := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
    have hhi := (bad12_freeRow_transfer idx_bad u₀).2.2.1
    have hu₀_b := hU0_norm u₀ hu₀
    rw [hmax_Hf]
    calc rowNorm (bad12FreeSplit idx_bad u₀).1
        ≤ 186624 * (2 * U ^ (H_free - 17 * η - τ)) :=
          hhi.trans (mul_le_mul_of_nonneg_left hu₀_b (by norm_num))
      _ = 373248 * U ^ (H_free - 17 * η - τ) := by ring
      _ ≤ U ^ (17 * η) * U ^ (H_free - 17 * η - τ) :=
          mul_le_mul_of_nonneg_right h373 (Real.rpow_nonneg hU_pos.le _)
      _ = U ^ (H_free - τ) := by
          rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
      _ ≤ U ^ H_free := Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [hτ_pos])
  have hw0_u : 0 ≤ u_act := by
    dsimp only [u_act]; apply mul_nonneg hθ0
    unfold stage1Width stage1Line; linarith only [hr0, hr1]
  have hS_free_norm2 : ∀ u ∈ S_free, rowNorm u ≤ U ^ (2 : ℝ) := by
    intro u hu
    have h1 := hS_free_norm u hu; rw [hmax_Hf] at h1
    have hHf2 : H_free ≤ 2 := by dsimp only [H_free]; linarith only [hw0_u, hell0, hx6_0]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hU1.le hHf2)
  let z_J_act : ℝ := ∑ i ∈ J, D.ell i / d_outer
  have hzJ_act0 : 0 ≤ z_J_act :=
    Finset.sum_nonneg (fun i _ => div_nonneg (D.slots_bounds i).1.le hd_pos.le)
  let X₀_in : ℝ := X₁ / ∏ i ∈ S'', Z_slot i
  let Δ_BC : ℝ := B_c + t_q + 2 * η - z_J_act
  have hΔ_BC0 : 0 ≤ Δ_BC := sub_nonneg.mpr hzJ_act_le
  let V₀_eff : ℝ := V₀ + Δ_BC
  have hV₀_eff0 : 0 ≤ V₀_eff := add_nonneg hV0 hΔ_BC0
  have hX₀_le_unm : X₀_in ≤ U ^ (r_param - V₀_eff - 3 * ell_in + z_Jv - 0) := by
    have hprod_SremJ : (∏ i ∈ S'', Z_slot i) * (∏ i ∈ (S_rem \ J) \ S'', Z_slot i) =
        ∏ i ∈ S_rem \ J, Z_slot i :=
      Finset.prod_union Finset.disjoint_sdiff |>.symm.trans
        (congrArg (fun F => ∏ i ∈ F, Z_slot i) (Finset.union_sdiff_of_subset hS''))
    have hX₀_mul : X₀_in * (∏ i ∈ S_rem \ J, Z_slot i) ≤ X_col := by
      dsimp only [X₀_in]
      rw [← hprod_SremJ, ← mul_assoc,
        div_mul_cancel₀ _ (Finset.prod_pos (fun i _ => hZ_slot_pos i)).ne']
      exact hX₁_le
    have hZ_remJ_eq : (∏ i ∈ S_rem \ J, Z_slot i) =
        U ^ ((∑ i ∈ S_rem, D.ell i / d_outer) - z_J_act) := by
      dsimp only [Z_slot, z_J_act]; rw [← Real.rpow_sum_of_pos hU_pos]
      apply congrArg (fun x : ℝ => U ^ x)
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_sdiff hJ_sub
    rw [hZ_remJ_eq, hX_col_eq] at hX₀_mul
    have hdiv_le := (le_div_iff₀ (Real.rpow_pos_of_pos hU_pos _)).mpr hX₀_mul
    rw [← Real.rpow_sub hU_pos] at hdiv_le
    refine hdiv_le.trans (Real.rpow_le_rpow_of_exponent_le hU1.le ?_)
    dsimp only [r_new, V₀_eff, Δ_BC]; linarith only [hFp_r]
  have hz_rem_Jv_pos : 0 ≤ z_rem_th - z_Jv := by
    have hz_rem_lo : (7 / 52 : ℝ) - 121 / 12500 ≤ z_rem_th := by
      dsimp only [z_rem_th]; unfold stage1RemWidth stage1Width stage1Line
      nlinarith only [hr0, hr1, hθ0, hθ1]
    linarith only [hz_rem_lo, hJv, hell1]
  let z_J_in : ℝ := min z_J_act (z_rem_th - z_Jv)
  have hzJ_in0 : 0 ≤ z_J_in := le_min hzJ_act0 hz_rem_Jv_pos
  have hzT_cap0 : 0 ≤ z_rem_th - z_Jv - z_J_in - 0 := by
    have hle : z_J_in ≤ z_rem_th - z_Jv := min_le_right _ _
    linarith only [hle]
  have hzT'_sum_le : ∀ T' : Finset (Fin D.N), T' ⊆ S'' →
      (∑ j ∈ T', D.ell j / d_outer) ≤ (z_rem_th - z_Jv - z_J_in - 0) + pad_T := by
    intro T' hT'
    have hT'_sub : T' ⊆ S_rem \ J := hT'.trans hS''
    have hdisj_TJ : Disjoint T' J :=
      Finset.disjoint_left.mpr (fun i hiT hiJ => (Finset.mem_sdiff.mp (hT'_sub hiT)).2 hiJ)
    have hun_sub : T' ∪ J ⊆ S_rem :=
      Finset.union_subset (hT'_sub.trans Finset.sdiff_subset) hJ_sub
    have hsum_TJ : (∑ j ∈ T', D.ell j / d_outer) + z_J_act ≤ ∑ i ∈ S_rem, D.ell i / d_outer := by
      dsimp only [z_J_act]; rw [← Finset.sum_union hdisj_TJ]
      exact Finset.sum_le_sum_of_subset_of_nonneg hun_sub
        (fun i _ _ => div_nonneg (D.slots_bounds i).1.le hd_pos.le)
    dsimp only [z_J_in]
    rcases le_total z_J_act (z_rem_th - z_Jv) with hle_zJ | hge_zJ
    · rw [min_eq_left hle_zJ]; linarith only [hsum_TJ, hz_Srem]
    · rw [min_eq_right hge_zJ]; linarith only [hsum_TJ, hz_Srem, hge_zJ]
  let χ_p := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  have hbad_sum_le : ∀ (s : ℝ) (T' : Finset (Fin D.N)) (X' : ℝ),
      0 < X' →
      let a_tw : Fin D.N → primePool F_pool → ℂ := fun j q =>
        a j q * kernelLogPhase s (Real.log (‖ringComplex (p q)‖ ^ 2 / Z_slot j))
      (∑ u₀ ∈ U0_set, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow p χ_p Finset.univ Ψ₀ 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm p U_set / X')) u₀.val *
          ∏ j ∈ T', slotCharSum p hg lists_v a_tw Ψ₀ j u₀.val‖ ^ 2) ≤
      4 * ∑ u ∈ S_free, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow p χ_p Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm p U_set / X')) u.val *
          ∏ j ∈ T', slotCharSum p hg lists_v a_tw base j u.val‖ ^ 2 := by
    intro s T' X' hX' a_tw
    let term_u : FreeRow → ℝ := fun u =>
      (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow p χ_p Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm p U_set / X')) u.val *
          ∏ j ∈ T', slotCharSum p hg lists_v a_tw base j u.val‖ ^ 2
    have hterm_nn : ∀ u, 0 ≤ term_u u := fun u =>
      mul_nonneg (inv_nonneg.mpr (mul_nonneg hX'.le
        (Finset.prod_nonneg (fun j _ => (hZ_slot_pos j).le)))) (sq_nonneg _)
    have heq_u0 : ∀ u₀ ∈ U0_set,
        (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
          ‖inputConjugateRow p χ_p Finset.univ Ψ₀ 1 1 1
              (fun U_set => childLogTest wFresh s (primeProductNorm p U_set / X')) u₀.val *
            ∏ j ∈ T', slotCharSum p hg lists_v a_tw Ψ₀ j u₀.val‖ ^ 2 =
        term_u (bad12FreeSplit idx_bad u₀).1 := by
      intro u₀ _; dsimp only [term_u]
      rw [(hbad_tr u₀).1 Finset.univ _,
        Finset.prod_congr rfl (fun j _ => (hbad_tr u₀).2 lists_v a_tw j)]
    rw [Finset.sum_congr rfl heq_u0,
      ← Finset.sum_fiberwise_of_maps_to (g := fun u₀ => (bad12FreeSplit idx_bad u₀).1)
        (fun u₀ hu₀ => Finset.mem_image_of_mem (fun u₀ => (bad12FreeSplit idx_bad u₀).1) hu₀),
      Finset.mul_sum]
    apply Finset.sum_le_sum; intro u _
    have hconst : ∀ u₀ ∈ U0_set.filter (fun u₀ => (bad12FreeSplit idx_bad u₀).1 = u),
        term_u (bad12FreeSplit idx_bad u₀).1 = term_u u :=
      fun _ hu₀ => congrArg term_u (mem_filter_of hu₀).2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (bad12FreeSplit_fiber_card_le idx_bad U0_set u) (hterm_nn u)
  have hX₀_Lcap : X₀_in ≤ U ^ Lcap := by
    have h1 : X₀_in ≤ X₁ :=
      div_le_self hX₁.le (Finset.one_le_prod (fun i _ => hZ_slot_ge1 i))
    have h2 : X₁ ≤ X_col :=
      (le_mul_of_one_le_right hX₁.le (Finset.one_le_prod (fun i _ => hZ_slot_ge1 i))).trans hX₁_le
    have h3 : X_col ≤ U ^ Lcap := by
      rw [hX_col_eq]
      exact Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [hrn_hi, hBc_0, htq_0])
    exact h1.trans (h2.trans h3)
  have hX₀_U2 : X₀_in ≤ U ^ (2 : ℝ) :=
    hX₀_le_unm.trans (Real.rpow_le_rpow_of_exponent_le hU1.le
      (by linarith only [hr1, hV₀_eff0, hJv, hell0]))
  have hDpool_Z : ∀ j ∈ S'', 2 * Z_slot j ≤ (Dpool : ℝ) := by
    intro j _
    calc 2 * Z_slot j ≤ 2 * U := mul_le_mul_of_nonneg_left (hZ_slot_hi j) zero_le_two
      _ ≤ B_p * U ^ (Lcap + 2) :=
          mul_le_mul hBp2 ((Real.rpow_one U).symm.trans_le
            (Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [hLcap])))
            hU_pos.le (by linarith only [hBp2])
      _ ≤ (Dpool : ℝ) := hDpool
  let S_cut : ℝ := (1 / (32 * Real.pi)) * Z_dual ^ τ_d
  have hS_cut0 : 0 ≤ S_cut := mul_nonneg (by positivity) (Real.rpow_nonneg (Real.rpow_nonneg hU_pos.le _) _)
  have hZd_ge_U : U ≤ Z_dual := by
    dsimp only [Z_dual]
    exact (Real.rpow_one U).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hU1.le
      ((one_le_div (by positivity)).mpr (by linarith only [hd_hi])))
  have hScut_lower : U ^ (τ_d / 2) ≤ 1 + S_cut := by
    have hZd_τ : U ^ τ_d ≤ Z_dual ^ τ_d := Real.rpow_le_rpow hU_pos.le hZd_ge_U hτ_p.le
    have hsplit_τ : U ^ τ_d = U ^ (τ_d / 2) * U ^ (τ_d / 2) := by
      rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
    have h32_le : 32 * Real.pi * U ^ (τ_d / 2) ≤ Z_dual ^ τ_d :=
      (mul_le_mul_of_nonneg_right h32pi (Real.rpow_nonneg hU_pos.le _)).trans
        (hsplit_τ.symm.le.trans hZd_τ)
    have hdiv_32 : U ^ (τ_d / 2) ≤ S_cut := by
      dsimp only [S_cut]; rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]; exact h32_le
    linarith only [hdiv_32]
  have htail_U_le : U ^ ((D.N : ℝ) + 10) / (1 + S_cut) ^ (2 * N_tail) ≤
      U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) := by
    have hden_ge : U ^ ((D.N : ℝ) + 20 + 6 * Lcap) ≤ (1 + S_cut) ^ (2 * N_tail) := by
      calc U ^ ((D.N : ℝ) + 20 + 6 * Lcap)
          ≤ U ^ ((τ_d / 2) * (2 * (N_tail : ℝ))) := by
            apply Real.rpow_le_rpow_of_exponent_le hU1.le
            have hceil : ((D.N : ℝ) + 20 + 6 * Lcap) / τ_d ≤ (N_tail : ℝ) := by
              dsimp only [N_tail]; push_cast
              have hc := Nat.le_ceil (((D.N : ℝ) + 20 + 6 * Lcap) / τ_d)
              linarith only [hc]
            have hm := (div_le_iff₀ hτ_p).mp hceil
            have heq_nt : (τ_d / 2) * (2 * (N_tail : ℝ)) = (N_tail : ℝ) * τ_d := by ring
            linarith only [hm, heq_nt]
        _ = (U ^ (τ_d / 2)) ^ (2 * N_tail) := by
            rw [← Real.rpow_natCast (U ^ (τ_d / 2)), ← Real.rpow_mul hU_pos.le]; push_cast; rfl
        _ ≤ (1 + S_cut) ^ (2 * N_tail) := pow_le_pow_left₀ (Real.rpow_nonneg hU_pos.le _) hScut_lower _
    have hdiv_le : U ^ ((D.N : ℝ) + 10) / (1 + S_cut) ^ (2 * N_tail) ≤
        U ^ ((D.N : ℝ) + 10 - ((D.N : ℝ) + 20 + 6 * Lcap)) := by
      rw [Real.rpow_sub hU_pos]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hU_pos.le _)
        (Real.rpow_pos_of_pos hU_pos _) hden_ge
    refine hdiv_le.trans (Real.rpow_le_rpow_of_exponent_le hU1.le ?_)
    have hx6_le1 : x6 ≤ 1 := by dsimp only [H_free] at hHf_pos; linarith only [hHf_pos, hell0, hw0_u]
    have hw1 : u_act ≤ 121 / 12500 := by
      dsimp only [u_act]
      have hsw : stage1Width r_param ≤ 121 / 12500 := by
        unfold stage1Width stage1Line; linarith only [hr0, hr1]
      nlinarith only [hθ0, hθ1, hsw]
    linarith only [hLcap, hell1, hw1, hx6_le1, hpad0, ht_pos]
  have hm_rem : markedRadial p S'' lists_v a ∅
      (principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht) X₁ =
      fun U_set => primeMark S'' lists_v a U_set *
        principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht
          (primeProductNorm p U_set / X₁) := by
    funext U_set; unfold markedRadial; simp only [Finset.empty_union]
  simp_rw [← hm_rem]
  have hf_app := hfour negative t_ht p hp hcop hg
    (fun j₁ j₂ h => hinj (congrArg (fun x => Ideal.span {x}) h)) Finset.univ Ψ₀ hΨ₀_norm
    S'' hS''_card lists_v (fun _ _ => Finset.subset_univ _)
    (fun i hi j hj hij => hdisj_v (hS''_rem hi) (hS''_rem hj) hij)
    a (fun i hi q hq => (hlists_v_b i (hS''_rem hi) q hq).2.2)
    Z_slot (fun i _ => hZ_slot_ge1 i)
    (fun i hi q hq => (hlists_v_b i (hS''_rem hi) q hq).1)
    (fun i hi q hq => (hlists_v_b i (hS''_rem hi) q hq).2.1)
    (U0_set.image Subtype.val) hX₁ hS_cut0
    (mul_nonneg (by norm_num) (mul_nonneg hC_sf.le (Real.rpow_nonneg hU_pos.le _)))
    (mul_nonneg (by norm_num) (mul_nonneg hCcr_nn (Real.rpow_nonneg hU_pos.le _)))
    (fun s hs_cut T' hT' X' hX' hX'_le => by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      have hX'_X₀ : X' ≤ X₀_in :=
        hX'_le.trans (div_le_self (div_nonneg hX₁.le
          (Finset.prod_nonneg (fun i _ => (hZ_slot_pos i).le)))
          (Finset.one_le_prod (fun i _ => hZ_slot_ge1 i)))
      have hDp_X' : bf * X' ≤ (Dpool : ℝ) := by
        have hbf_Bp : bf ≤ B_p := by dsimp only [B_p]; have hm := le_max_right (2 : ℝ) bf; linarith only [hm]
        have hUL : U ^ Lcap ≤ U ^ (Lcap + 2) := Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [])
        exact (mul_le_mul hbf_Bp ((hX'_X₀.trans hX₀_Lcap).trans hUL)
          hX'.le (by linarith only [hBp2])).trans hDpool
      have hζ_tw_im : |(ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I).im| ≤ Z_dual ^ τ_d := by
        have h2pi_s : |2 * Real.pi * s| ≤ (1 / 16 : ℝ) * Z_dual ^ τ_d := by
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
          calc 2 * Real.pi * |s| ≤ 2 * Real.pi * S_cut :=
                mul_le_mul_of_nonneg_left hs_cut (by positivity)
            _ = (1 / 16 : ℝ) * Z_dual ^ τ_d := by
                dsimp only [S_cut]; field_simp [Real.pi_ne_zero]; ring
        have him_eq : (ζ_base + ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I).im =
            ζ_base.im + 2 * Real.pi * s := by simp
        rw [him_eq]
        have htri := (abs_add_le ζ_base.im (2 * Real.pi * s)).trans (add_le_add hζ_im h2pi_s)
        have hZd_pos : 0 < Z_dual ^ τ_d :=
          Real.rpow_pos_of_pos (hU_pos.trans_le hZd_ge_U) τ_d
        linarith only [htri, hZd_pos]
      have hsf_app := hsf U (((le_max_left _ _).trans (le_max_right _ _)).trans hU) Dpool
        hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6_0 hV₀_eff0 hzJ_in0 le_rfl hpad0
        hzT_cap0 hHf_lo hX' (hX'_X₀.trans hX₀_le_unm) hDp_X'
        T' (hzT'_sum_le T' hT')
        (fun j hj => hDpool_Z j (hT' hj))
        (fun j hj => hlarge_Z j (hS''_rem (hT' hj)))
        lists_full lists_v a
        (fun j hj => hlists_full j (hS''_rem (hT' hj)))
        (fun j hj => hlists_v j (hS''_rem (hT' hj)))
        (fun j hj => hcard_diff j (hS''_rem (hT' hj)))
        ζ_base hζ_re (fun j hj => ha_eq j (hS''_rem (hT' hj)))
        S_free hS_free_norm s hζ_tw_im
      exact ((hbad_sum_le s T' X' hX').trans
        (mul_le_mul_of_nonneg_left hsf_app (by norm_num))).trans_eq (by ring))
    (fun s T' hT' X' hX' hX'_le => by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
      have hX'_X₀ : X' ≤ X₀_in :=
        hX'_le.trans (div_le_self (div_nonneg hX₁.le
          (Finset.prod_nonneg (fun i _ => (hZ_slot_pos i).le)))
          (Finset.one_le_prod (fun i _ => hZ_slot_ge1 i)))
      have hDp_X' : bf * X' ≤ (Dpool : ℝ) := by
        have hbf_Bp : bf ≤ B_p := by dsimp only [B_p]; have hm := le_max_right (2 : ℝ) bf; linarith only [hm]
        have hUL : U ^ Lcap ≤ U ^ (Lcap + 2) := Real.rpow_le_rpow_of_exponent_le hU1.le (by linarith only [])
        exact (mul_le_mul hbf_Bp ((hX'_X₀.trans hX₀_Lcap).trans hUL)
          hX'.le (by linarith only [hBp2])).trans hDpool
      have hcr := dual_factored_coarse_bound_lists_sdiff F_dual wFresh hbf_pos hBw0
        (fun y hy => (hs_w hy).2) hBw M_drop data Dpool
        hU1.le hX' (hX'_X₀.trans hX₀_U2) hDp_X' T' Z_slot
        (fun j _ => hZ_slot_ge1 j) (fun j _ => hZ_slot_hi j)
        (fun j hj => hDpool_Z j (hT' hj))
        (fun j hj => hlarge_Z j (hS''_rem (hT' hj)))
        ζ_base (by rw [hζ_re]; norm_num) lists_full lists_v a
        (fun j hj => hlists_full j (hS''_rem (hT' hj)))
        (fun j hj => hlists_v j (hS''_rem (hT' hj)))
        (fun j hj => hcard_diff j (hS''_rem (hT' hj)))
        (fun j hj => ha_eq j (hS''_rem (hT' hj)))
        S_free hS_free_norm2 s
      exact ((hbad_sum_le s T' X' hX').trans
        (mul_le_mul_of_nonneg_left hcr (by norm_num))).trans_eq (by ring))
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hf_app
  calc _ ≤ C_four * (1 + ‖t_ht‖) ^ (2 * deg_w) *
            (4 * C_sf * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) +
              (4 * C_cr * U ^ ((D.N : ℝ) + 10)) / (1 + S_cut) ^ (2 * N_tail)) := hf_app
    _ ≤ C_four * (1 + ‖t_ht‖) ^ (2 * deg_w) *
          (4 * C_sf * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) +
            4 * C_cr * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hC_f.le (pow_nonneg (add_nonneg zero_le_one (norm_nonneg t_ht)) _))
        apply add_le_add_left
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left htail_U_le (mul_nonneg (by norm_num) hCcr_nn)
    _ ≤ C_unp * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) *
          (1 + ‖t_ht‖) ^ (2 * deg_w) := by
        dsimp only [C_unp]
        have hnn : 0 ≤ 4 * C_four * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) *
            (1 + ‖t_ht‖) ^ (2 * deg_w) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC_f.le)
            (Real.rpow_nonneg hU_pos.le _)) (pow_nonneg (add_nonneg zero_le_one (norm_nonneg t_ht)) _)
        linarith only [hnn]

/-- Nonzero frequency ball `W_ball` energy bound for a single Schwartz window `omega_b` and
orientation `negative`, factoring `w ∈ W_ball` into `(u₀, A)` via `exists_rowMap_eq`, grouping by
dyadic shell `k_A` and ideal `A`, unpuncturing via
`inputConjugateRow_markedRadial_unpuncture_total_scale`, and invoking
`dual_qzero_unpunc_single_omega`. -/
private theorem dual_qzero_W_ball_single_omega
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (omega_b : 𝓢(ℝ, ℂ)) {lo_o hi_o : ℝ} (hlo_o : 0 < lo_o) (hlh_o : lo_o ≤ hi_o)
    (hs_ob : Function.support (omega_b : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o)
    (negative : Bool) (M_drop : ℕ) (Lcap η τ : ℝ) (hLcap : 1 ≤ Lcap)
    (hη_pos : 0 < η) (hη1 : η ≤ 1) (hτ_pos : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ (τ_d B_p : ℝ) (deg_w : ℕ),
      0 < τ_d ∧ 2 * τ_d ≤ D_dual.t ∧ 2 ≤ B_p ∧
      ∀ data : RowData, ∃ C_W U_W : ℝ, 0 < C_W ∧ 2 ≤ U_W ∧
      ∀ U : ℝ, U_W ≤ U → 2 ≤ U ^ η →
      ∀ Dpool : ℕ, B_p * U ^ (Lcap + 2) ≤ (Dpool : ℝ) →
      let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
        fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
      let p := poolPrimary F_pool
      let hp := poolPrimary_ne_zero F_pool hFa
      let hcop := poolPrimary_coprime F_pool hFa
      let hg := poolPrimary_good F_pool hFa
      let base := InverseInitialRayAttachment.elementCharacter
        (InverseInitialConjugateEnergy.conjugateIdealCharacter
          (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T B_c t_q X_col : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r_param → r_param ≤ 19 / 26 →
        0 ≤ θ_s → θ_s ≤ 1 →
        0 ≤ ell_in → ell_in ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell_in →
        0 ≤ V₀ → 0 ≤ pad_T → 0 ≤ B_c → 0 ≤ t_q → t_q ≤ 3 * Lcap + 15 * η + τ →
      let u_act := θ_s * stage1Width r_param
      let z_rem_th := (1 - θ_s) * ((1 - r_param) / 2) + θ_s * stage1RemWidth r_param
      let r_new := F_p - V₀ - 3 * ell_in - u_act
      let W_exp := (1 - 6 * u_act) - 6 * ell_in - 17 * η - τ
      r_new ≤ Lcap → X_col = U ^ (r_new - B_c - t_q) →
      ∀ (S_rem J : Finset (Fin D.N)), J ⊆ S_rem →
        (∑ i ∈ J, D.ell i / d_outer) ≤ B_c + t_q + 2 * η →
        (∑ i ∈ S_rem, D.ell i / d_outer) ≤ z_rem_th - z_Jv + pad_T →
        F_p - ((∑ i ∈ S_rem, D.ell i / d_outer) + u_act + z_Jv) + 2 * η ≤ r_param →
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      (∀ j ∈ S_rem, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full lists_v : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ S_rem, lists_full j = InverseInitialCommonLists.poolList F_pool
          (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (∀ j ∈ S_rem, lists_v j ⊆ lists_full j) →
        (∀ j ∈ S_rem, ((lists_full j \ lists_v j).card : ℝ) ≤ (M_drop : ℝ)) →
        (S_rem : Set (Fin D.N)).PairwiseDisjoint lists_v →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ S_rem, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val /
            star (idealCoeff (deletedBase data) q.val)) →
      (∀ j ∈ S_rem, ∀ q ∈ lists_v j,
        Z_slot j ≤ ‖ringComplex (p q)‖ ^ 2 ∧ ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot j ∧ ‖a j q‖ ≤ 1) →
      ∀ (Ψ₀ : O →* ℂ), CanonicalCoefficientClass.IsBaseRayTwist base Ψ₀ → (∀ u, ‖Ψ₀ u‖ ≤ 1) →
      ∀ (m : O), m ≠ 0 → ‖ringComplex m‖ ^ 2 ≤ U ^ (2 * Lcap) →
      ∀ (t_ht : ℝ) (D_q : Finset (primePool F_pool)), primeProductNorm p D_q ≤ U ^ (t_q + η) →
        (∑ w ∈ (firstFrequencyDisk (2 * U ^ W_exp)).erase 0,
          ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            Finset.univ Ψ₀ (m * ∏ i ∈ D_q, p i) 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅
              (principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht) X_col) w‖ ^ 2) ≤
        C_W * X_col * U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (15 / 2 : ℝ) * D_dual.t) *
          (1 + ‖t_ht‖) ^ (2 * deg_w) := by
  obtain ⟨τ_d, B_p, deg_w, hτ_p, hτ_le, hBp2, hunp_all⟩ :=
    dual_qzero_unpunc_single_omega hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb
      F_dual omega_b hlo_o hlh_o hs_ob negative M_drop Lcap η τ hLcap hη_pos hτ_pos
  let ε_div : ℝ := D_dual.t / (80 * (6 * Lcap + 30))
  have hε_div : 0 < ε_div := by dsimp only [ε_div]; have := D_dual.t_pos; positivity
  obtain ⟨C_div, hC_div, hdiv_le⟩ := ideal_divisor_small_power ε_div hε_div
  obtain ⟨C_log, hC_log, hlog_le⟩ := log_fourth_small_power 1 (D_dual.t / 4) (by have := D_dual.t_pos; positivity)
  have hCdiv10_pos : 0 < C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div) :=
    mul_pos (pow_pos hC_div 10) (Real.rpow_pos_of_pos zero_lt_two _)
  refine ⟨τ_d, B_p, deg_w, hτ_p, hτ_le, hBp2, ?_⟩
  intro data
  obtain ⟨C_unp, U_unp, hC_unp, hU_unp2, hunp⟩ := hunp_all data
  let C_W : ℝ := C_log * 512 * (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp
  have hCW_pos : 0 < C_W := mul_pos (mul_pos (mul_pos hC_log (by norm_num)) hCdiv10_pos) hC_unp
  refine ⟨C_W, U_unp, hCW_pos, hU_unp2, ?_⟩
  intro U hU h2_η Dpool hDpool q_per F_pool hFa p hp hcop hg base
    d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T B_c t_q X_col
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0 hpad0 hBc_0 htq_0 htq_hi
    u_act z_rem_th r_new W_exp hrn_hi hX_col_eq
    S_rem J hJ_sub hzJ_act_le hz_Srem hFp_r Z_slot Z_dual hlarge_Z
    lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
    ζ_base hζ_re hζ_im a ha_eq hlists_v_b Ψ₀ hΨ₀_base hΨ₀_norm m hm_ne hm_norm t_ht D_q hDq_norm
  letI : ∀ i : primePool F_pool, (Ideal.span {p i}).IsMaximal :=
    fun i => by dsimp only [p]; rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU2 : 2 ≤ U := hU_unp2.trans hU
  have hU1 : 1 < U := by linarith only [hU2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have ht_pos : 0 < D_dual.t := D_dual.t_pos
  have hX_col_pos : 0 < X_col := by rw [hX_col_eq]; exact Real.rpow_pos_of_pos hU_pos _
  have hZ_slot_ge1 : ∀ j : Fin D.N, 1 ≤ Z_slot j :=
    fun j => Real.one_le_rpow hU1.le (div_nonneg (D.slots_bounds j).1.le hd_pos.le)
  have hw0_u : 0 ≤ u_act := by
    dsimp only [u_act]; apply mul_nonneg hθ0
    unfold stage1Width stage1Line; linarith only [hr0, hr1]
  have hW_exp_le1 : W_exp ≤ 1 := by dsimp only [W_exp]; linarith only [hw0_u, hell0, hη_pos, hτ_pos]
  let W_ball : Finset O := (firstFrequencyDisk (2 * U ^ W_exp)).erase 0
  let V_win : 𝓢(ℝ, ℂ) := principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht
  let χ_p := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  let wt_t : ℝ := (1 + ‖t_ht‖) ^ (2 * deg_w)
  have hwt_pos : 0 < wt_t := pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg t_ht)) _
  by_cases hW_ne : W_ball.Nonempty
  swap
  · change (∑ w ∈ W_ball, _) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hW_ne, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCW_pos.le hX_col_pos.le)
      (Real.rpow_nonneg hU_pos.le _)) hwt_pos.le
  let split_w : W_ball → FreeRow × NonzeroIdeal := fun w =>
    Classical.choose (exists_rowMap_eq (Finset.mem_erase.mp w.property).1)
  have hsplit_eq : ∀ w : W_ball, rowMap (split_w w) = w.val := fun w =>
    Classical.choose_spec (exists_rowMap_eq (Finset.mem_erase.mp w.property).1)
  have hsplit_inj : Function.Injective split_w := by
    intro w₁ w₂ heq; apply Subtype.ext; rw [← hsplit_eq w₁, ← hsplit_eq w₂, heq]
  have hsplit_norm : ∀ w : W_ball,
      rowNorm (split_w w).1 * ((split_w w).2.val.absNorm : ℝ) ^ 6 = ‖ringComplex w.val‖ ^ 2 := by
    intro w
    have hsp : Ideal.span {w.val} = Ideal.span {(split_w w).1.val} * (split_w w).2.val ^ 6 := by
      rw [← hsplit_eq w, ← rowMap_span]
    have hn := congrArg (fun I : Ideal O => (I.absNorm : ℝ)) hsp
    simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow,
      ← ringComplex_norm_sq_eq_absNorm_span, rowNorm] using hn.symm
  let k_A : W_ball → ℕ := fun w =>
    InverseSecondSourceBlocks.dyadIndex ((split_w w).2.val.absNorm : ℝ)
  let K_A_set : Finset ℕ := Finset.univ.image k_A
  have hKA_card : (K_A_set.card : ℝ) ≤ C_log * U ^ (D_dual.t / 4) := by
    have hkA_le : ∀ k_idx ∈ K_A_set, (k_idx : ℝ) ≤ Real.log U / Real.log 2 := by
      intro k_idx hk_idx
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hk_idx
      have hA_ge1 : 1 ≤ ((split_w w).2.val.absNorm : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr (split_w w).2.property)
      have hds := (InverseSecondSourceBlocks.dyadIndex_bounds _ hA_ge1).1
      have hds_eq : InverseSecondSourceBlocks.dyadScale (k_A w) = (2 : ℝ) ^ (k_A w) := rfl
      have hu_ge1 : 1 ≤ rowNorm (split_w w).1 := by
        unfold rowNorm
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr
            (Ideal.span_singleton_eq_bot.not.mpr (split_w w).1.property.1))
      have hw_le_U6 : ‖ringComplex w.val‖ ^ 2 ≤ U ^ (6 : ℝ) := by
        have hw_n : ‖ringComplex w.val‖ ^ 2 ≤ 2 * U ^ W_exp :=
          (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp w.property).2
        have h2U : 2 * U ^ W_exp ≤ U * U := by
          calc 2 * U ^ W_exp ≤ U * U ^ (1 : ℝ) :=
                mul_le_mul hU2 (Real.rpow_le_rpow_of_exponent_le hU1.le hW_exp_le1)
                  (Real.rpow_nonneg hU_pos.le _) hU_pos.le
            _ = U * U := by rw [Real.rpow_one]
        have hUU : U * U = U ^ (2 : ℝ) := by
          calc U * U = U ^ (1 : ℝ) * U ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = U ^ (2 : ℝ) := by rw [← Real.rpow_add hU_pos]; norm_num
        exact (hw_n.trans h2U).trans (hUU.le.trans (Real.rpow_le_rpow_of_exponent_le hU1.le (by norm_num)))
      have h2k_le : ((2 : ℝ) ^ (k_A w)) ^ 6 ≤ U ^ (6 : ℝ) := by
        calc ((2 : ℝ) ^ (k_A w)) ^ 6
            ≤ ((split_w w).2.val.absNorm : ℝ) ^ 6 :=
              pow_le_pow_left₀ (pow_nonneg zero_le_two _) (hds_eq ▸ hds) 6
          _ ≤ rowNorm (split_w w).1 * ((split_w w).2.val.absNorm : ℝ) ^ 6 :=
              le_mul_of_one_le_left (pow_nonneg (Nat.cast_nonneg _) _) hu_ge1
          _ = ‖ringComplex w.val‖ ^ 2 := hsplit_norm w
          _ ≤ U ^ (6 : ℝ) := hw_le_U6
      have h2k_U : (2 : ℝ) ^ (k_A w) ≤ U := by
        have h6 : ((2 : ℝ) ^ (k_A w)) ^ (6 : ℝ) ≤ U ^ (6 : ℝ) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (k_A w)) 6]; exact h2k_le
        exact (Real.rpow_le_rpow_iff (pow_nonneg zero_le_two _) hU_pos.le (by norm_num : (0 : ℝ) < 6)).mp h6
      have hlog2 := Real.log_le_log (pow_pos zero_lt_two _) h2k_U
      rw [Real.log_pow] at hlog2
      exact (le_div_iff₀ (Real.log_pos one_lt_two)).mpr hlog2
    let N_max : ℕ := ⌊Real.log U / Real.log 2⌋₊
    have hsub_range : K_A_set ⊆ Finset.range (N_max + 1) := fun k_idx hk =>
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor (hkA_le k_idx hk)))
    have hcard_nat : (K_A_set.card : ℝ) ≤ (N_max : ℝ) + 1 := by
      exact_mod_cast (Finset.card_le_card hsub_range).trans_eq (Finset.card_range (N_max + 1))
    have hNmax_le : (N_max : ℝ) + 1 ≤ 1 + 2 * Real.log U := by
      have hf : (N_max : ℝ) ≤ Real.log U / Real.log 2 :=
        Nat.floor_le (div_nonneg (Real.log_nonneg hU1.le) (Real.log_pos one_lt_two).le)
      have hlog2_gt : (1 / 2 : ℝ) ≤ Real.log 2 := by have hl2 := Real.log_two_gt_d9; linarith only [hl2]
      have hdiv2 : Real.log U / Real.log 2 ≤ 2 * Real.log U := by
        rw [div_le_iff₀ (Real.log_pos one_lt_two)]
        have hl0 : 0 ≤ Real.log U := Real.log_nonneg hU1.le
        nlinarith only [hl0, hlog2_gt]
      linarith only [hf, hdiv2]
    have h1log4 : 1 + 2 * Real.log U ≤ (1 + 1 * Real.log U) ^ 4 := by
      have hx : 0 ≤ Real.log U := Real.log_nonneg hU1.le
      have hdiff : (1 + 1 * Real.log U) ^ 4 - (1 + 2 * Real.log U) =
          2 * Real.log U + 6 * (Real.log U) ^ 2 + 4 * (Real.log U) ^ 3 + (Real.log U) ^ 4 := by ring
      have hnn : 0 ≤ 2 * Real.log U + 6 * (Real.log U) ^ 2 + 4 * (Real.log U) ^ 3 + (Real.log U) ^ 4 :=
        add_nonneg (add_nonneg (add_nonneg (mul_nonneg zero_le_two hx)
          (mul_nonneg (by norm_num) (pow_nonneg hx 2)))
          (mul_nonneg (by norm_num) (pow_nonneg hx 3))) (pow_nonneg hx 4)
      linarith only [hdiff, hnn]
    exact (hcard_nat.trans hNmax_le).trans (h1log4.trans (hlog_le U hU2))
  let d_D : O := ∏ i ∈ D_q, p i
  have hd_D_ne : d_D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let B_shell : ℝ := 512 * (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp *
    X_col * U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (29 / 4 : ℝ) * D_dual.t) * wt_t
  have hshell_bound : ∀ k_idx ∈ K_A_set,
      (∑ w ∈ Finset.univ.filter (fun w : W_ball => k_A w = k_idx),
        ‖inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
          (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w.val‖ ^ 2) ≤ B_shell := by
    intro k_idx hk_idx
    obtain ⟨w_rep, _, hk_rep⟩ := Finset.mem_image.mp hk_idx
    let x6 : ℝ := dyadicExponent U k_idx
    have hA_rep_ge1 : 1 ≤ ((split_w w_rep).2.val.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (split_w w_rep).2.property)
    have hx6_0 : 0 ≤ x6 := by
      have hb := first_dyadic_bounds U η ((split_w w_rep).2.val.absNorm : ℝ) hU1 h2_η hA_rep_ge1
      dsimp only [x6]; rw [← hk_rep]; exact hb.1
    let H_free : ℝ := (1 - 6 * u_act) - 6 * ell_in - 6 * x6
    let W_k := Finset.univ.filter (fun w : W_ball => k_A w = k_idx)
    have hWk_bounds : ∀ w ∈ W_k,
        U ^ x6 ≤ ((split_w w).2.val.absNorm : ℝ) ∧
        ((split_w w).2.val.absNorm : ℝ) ≤ 2 * U ^ x6 ∧
        rowNorm (split_w w).1 ≤ 2 * U ^ (H_free - 17 * η - τ) := by
      intro w hw
      have hkeq : k_A w = k_idx := (mem_filter_of hw).2
      have hA1 : 1 ≤ ((split_w w).2.val.absNorm : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr (split_w w).2.property)
      have hdb : InverseSecondSourceBlocks.dyadScale (k_A w) ≤ ((split_w w).2.val.absNorm : ℝ) ∧
          ((split_w w).2.val.absNorm : ℝ) < 2 * InverseSecondSourceBlocks.dyadScale (k_A w) :=
        InverseSecondSourceBlocks.dyadIndex_bounds _ hA1
      rw [hkeq, ← rpow_dyadicExponent U hU1 k_idx] at hdb
      have hw_norm : ‖ringComplex w.val‖ ^ 2 ≤ 2 * U ^ W_exp :=
        (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp w.property).2
      have hu_le : rowNorm (split_w w).1 * (U ^ x6) ^ 6 ≤ 2 * U ^ W_exp := by
        calc rowNorm (split_w w).1 * (U ^ x6) ^ 6
            ≤ rowNorm (split_w w).1 * ((split_w w).2.val.absNorm : ℝ) ^ 6 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg hU_pos.le _) hdb.1 6)
                (Nat.cast_nonneg _)
          _ = ‖ringComplex w.val‖ ^ 2 := hsplit_norm w
          _ ≤ 2 * U ^ W_exp := hw_norm
      have h6x6 : (U ^ x6) ^ 6 = U ^ (6 * x6) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hU_pos.le]
        exact congrArg (fun x : ℝ => U ^ x) (by ring)
      rw [h6x6] at hu_le
      have hu_div : rowNorm (split_w w).1 ≤ (2 * U ^ W_exp) / U ^ (6 * x6) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hU_pos _)).mpr hu_le
      refine ⟨hdb.1, hdb.2.le, hu_div.trans_eq ?_⟩
      rw [mul_div_assoc, ← Real.rpow_sub hU_pos]
      exact congrArg (fun x : ℝ => 2 * U ^ x) (by dsimp only [W_exp, H_free]; ring)
    have hw_rep_mem : w_rep ∈ W_k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_rep⟩
    have hHf_pos : 0 < H_free := by
      have hu1 : 1 ≤ rowNorm (split_w w_rep).1 := by
        unfold rowNorm
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr
            (Ideal.span_singleton_eq_bot.not.mpr (split_w w_rep).1.property.1))
      have h2rp : 1 ≤ U ^ η * U ^ (H_free - 17 * η - τ) :=
        hu1.trans ((hWk_bounds w_rep hw_rep_mem).2.2.trans
          (mul_le_mul_of_nonneg_right h2_η (Real.rpow_nonneg hU_pos.le _)))
      rw [← Real.rpow_add hU_pos, ← Real.rpow_zero U, Real.rpow_le_rpow_left_iff hU1] at h2rp
      linarith only [h2rp, hη_pos, hτ_pos]
    let A_set : Finset (Ideal O) := W_k.image (fun w => (split_w w).2.val)
    have hA_card : (A_set.card : ℝ) ≤ 512 * U ^ x6 := by
      have hc := EisensteinLatticeCount.finite_ideal_count_real A_set (2 * U ^ x6)
        (by have h1 := Real.one_le_rpow hU1.le hx6_0; linarith only [h1])
        (fun I hI => by obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hI; exact (split_w w).2.property)
        (fun I hI => by obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI; exact (hWk_bounds w hw).2.1)
      linarith only [hc, Real.rpow_pos_of_pos hU_pos x6]
    let B_Afib : ℝ := (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp *
      X_col * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + (29 / 4 : ℝ) * D_dual.t) * wt_t
    have hAfib_bound : ∀ A_id ∈ A_set,
        (∑ w ∈ W_k.filter (fun w => (split_w w).2.val = A_id),
          ‖inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w.val‖ ^ 2) ≤ B_Afib := by
      intro A_id hAid
      obtain ⟨w_a, hw_a, hAid_eq⟩ := Finset.mem_image.mp hAid
      have hAid_ne : A_id ≠ 0 := hAid_eq ▸ (split_w w_a).2.property
      have hAid_norm : (A_id.absNorm : ℝ) ≤ 2 * U ^ x6 := hAid_eq ▸ (hWk_bounds w_a hw_a).2.1
      let g_A : O := cubicIdealGenerator A_id
      have hgA_ne : g_A ≠ 0 := cubicIdealGenerator_ne_zero A_id hAid_ne
      let m' : O := (m * d_D) * g_A
      have hm'_ne : m' ≠ 0 := mul_ne_zero (mul_ne_zero hm_ne hd_D_ne) hgA_ne
      let P_punc : Finset (primePool F_pool) := Finset.univ.filter (fun q => p q ∣ m')
      have hpunc_1024 : (1024 : ℝ) ^ P_punc.card ≤
          C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div) * U ^ (D_dual.t / 4) := by
        have hp10 := puncture_card_pow_1024_le_divisors p hp hcop Finset.univ hm'_ne
        have hd_m := hdiv_le (Ideal.span {m'}) (Ideal.span_singleton_eq_bot.not.mpr hm'_ne)
        have hm'_norm : ((Ideal.span {m'}).absNorm : ℝ) ≤ 2 * U ^ (6 * Lcap + 30) := by
          rw [← ringComplex_norm_sq_eq_absNorm_span]
          dsimp only [m']; rw [map_mul, map_mul, norm_mul, norm_mul, mul_pow, mul_pow]
          have hdD_n : ‖ringComplex d_D‖ ^ 2 ≤ U ^ (t_q + η) := by
            have h1 : ‖ringComplex d_D‖ ^ 2 = primeProductNorm p D_q := by
              dsimp only [d_D]; unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
            rw [h1]; exact hDq_norm
          have hgA_n : ‖ringComplex g_A‖ ^ 2 = (A_id.absNorm : ℝ) := by
            dsimp only [g_A]; rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
          have hx6_le1 : x6 ≤ 1 := by dsimp only [H_free] at hHf_pos; linarith only [hHf_pos, hell0, hw0_u]
          calc ‖ringComplex m‖ ^ 2 * ‖ringComplex d_D‖ ^ 2 * ‖ringComplex g_A‖ ^ 2
              ≤ U ^ (2 * Lcap) * U ^ (t_q + η) * (2 * U ^ x6) := by
                rw [hgA_n]
                exact mul_le_mul (mul_le_mul hm_norm hdD_n (sq_nonneg _) (Real.rpow_nonneg hU_pos.le _))
                  hAid_norm (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hU_pos.le _) (Real.rpow_nonneg hU_pos.le _))
            _ = 2 * U ^ (2 * Lcap + (t_q + η) + x6) := by
                rw [← Real.rpow_add hU_pos, mul_left_comm _ 2, ← Real.rpow_add hU_pos]
            _ ≤ 2 * U ^ (6 * Lcap + 30) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1.le
                  (by linarith only [htq_hi, hLcap, hη1, hτ1, hx6_le1])) zero_le_two
        have hrp_m : ((Ideal.span {m'}).absNorm : ℝ) ^ ε_div ≤
            (2 : ℝ) ^ ε_div * U ^ ((6 * Lcap + 30) * ε_div) :=
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hm'_norm hε_div.le).trans_eq
            (by rw [Real.mul_rpow zero_le_two (Real.rpow_nonneg hU_pos.le _), ← Real.rpow_mul hU_pos.le])
        have hd10 : ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 10 ≤
            (C_div * ((2 : ℝ) ^ ε_div * U ^ ((6 * Lcap + 30) * ε_div))) ^ 10 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (hd_m.trans (mul_le_mul_of_nonneg_left hrp_m hC_div.le)) 10
        calc (1024 : ℝ) ^ P_punc.card
            ≤ (C_div * ((2 : ℝ) ^ ε_div * U ^ ((6 * Lcap + 30) * ε_div))) ^ 10 := hp10.trans hd10
          _ = C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div) * U ^ (10 * ((6 * Lcap + 30) * ε_div)) := by
              rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ε_div),
                ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast (U ^ _),
                ← Real.rpow_mul hU_pos.le]
              norm_num; ring_nf
          _ ≤ C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div) * U ^ (D_dual.t / 4) := by
              apply mul_le_mul_of_nonneg_left _ hCdiv10_pos.le
              apply Real.rpow_le_rpow_of_exponent_le hU1.le
              have heq : 10 * ((6 * Lcap + 30) * ε_div) = D_dual.t / 8 := by
                dsimp only [ε_div]; field_simp; ring
              linarith only [heq, ht_pos]
      let W_kA := W_k.filter (fun w => (split_w w).2.val = A_id)
      let U0_set : Finset FreeRow := W_kA.image (fun w => (split_w w).1)
      have hU0_inj : Set.InjOn (fun w : W_ball => (split_w w).1) W_kA := by
        intro w₁ h₁ w₂ h₂ he1
        exact hsplit_inj (Prod.ext he1 (Subtype.ext ((mem_filter_of h₁).2.trans (mem_filter_of h₂).2.symm)))
      have hU0_norm : ∀ u₀ ∈ U0_set, rowNorm u₀ ≤ 2 * U ^ (H_free - 17 * η - τ) := by
        intro u₀ hu₀; obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.mp hu₀
        exact (hWk_bounds w (mem_filter_of hwA).1).2.2
      have hw_punc_eq : ∀ w ∈ W_kA,
          inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w.val =
          inputConjugateRow p χ_p (Finset.univ \ P_punc) Ψ₀ 1 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) (split_w w).1.val := by
        intro w hwA
        have hw_eq : w.val = (split_w w).1.val * g_A ^ 6 := by
          have hrm := (hsplit_eq w).symm; unfold rowMap at hrm
          rwa [(mem_filter_of hwA).2] at hrm
        rw [hw_eq, inputConjugateRow_mul_sixth_pow p hg Finset.univ Ψ₀ (m * d_D) 1 1 _
          (split_w w).1.val g_A]
        exact (inputConjugateRow_puncture_eq_sdiff_and_card_le p hg hp hcop Finset.univ Ψ₀
          hm'_ne _ (split_w w).1.val).1
      have hsum_to_U0 :
          (∑ w ∈ W_kA,
            ‖inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
              (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w.val‖ ^ 2) =
          X_col * ∑ u₀ ∈ U0_set, X_col⁻¹ *
            ‖inputConjugateRow p χ_p (Finset.univ \ P_punc) Ψ₀ 1 1 1
              (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) u₀.val‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_image hU0_inj]
        apply Finset.sum_congr rfl; intro w hwA
        rw [hw_punc_eq w hwA, ← mul_assoc, mul_inv_cancel₀ hX_col_pos.ne', one_mul]
      let B_sup : ℝ := C_unp * U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) * wt_t
      have hB_sup0 : 0 ≤ B_sup :=
        mul_nonneg (mul_nonneg hC_unp.le (Real.rpow_nonneg hU_pos.le _)) hwt_pos.le
      have hV_win_hi : ∀ y, V_win y ≠ 0 → y ≤ hi_o := by
        intro y hy
        have hsV : Function.support (V_win : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o := by
          dsimp only [V_win]; rw [principalWindow_support]; exact hs_ob
        exact (hsV hy).2
      have hm_top : markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col =
          fun U_set => primeMark (S_rem \ J) lists_v a U_set *
            V_win (primeProductNorm p U_set / X_col) := by
        funext U_set; unfold markedRadial; simp only [Finset.empty_union]
      have hunp_tot := inputConjugateRow_markedRadial_unpuncture_total_scale p hp hg
        Finset.univ P_punc Ψ₀ hΨ₀_norm (S_rem \ J) lists_v
        (fun i hi j hj hij => hdisj_v (Finset.sdiff_subset hi) (Finset.sdiff_subset hj) hij)
        a (fun i hi q hq => (hlists_v_b i (Finset.sdiff_subset hi) q hq).2.2)
        Z_slot (fun i _ => hZ_slot_ge1 i)
        (fun i hi q hq => (hlists_v_b i (Finset.sdiff_subset hi) q hq).1)
        V_win hV_win_hi (U0_set.image Subtype.val) hB_sup0 hX_col_pos
        (fun S'' hS'' X₁ hX₁ hX₁_le => by
          rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
          exact hunp U hU Dpool hDpool hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0
            hpad0 hBc_0 htq_0 hx6_0 hrn_hi hHf_pos hX_col_eq S_rem J hJ_sub hzJ_act_le hz_Srem
            hFp_r hlarge_Z lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
            ζ_base hζ_re hζ_im a ha_eq hlists_v_b Ψ₀ hΨ₀_base hΨ₀_norm U0_set hU0_norm
            t_ht S'' hS'' X₁ hX₁ hX₁_le)
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h), ← hm_top] at hunp_tot
      rw [hsum_to_U0]
      calc X_col * ∑ u₀ ∈ U0_set, X_col⁻¹ *
              ‖inputConjugateRow p χ_p (Finset.univ \ P_punc) Ψ₀ 1 1 1
                (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) u₀.val‖ ^ 2
          ≤ X_col * ((1024 : ℝ) ^ P_punc.card * B_sup) :=
            mul_le_mul_of_nonneg_left hunp_tot hX_col_pos.le
        _ ≤ X_col * ((C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div) * U ^ (D_dual.t / 4)) * B_sup) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpunc_1024 hB_sup0) hX_col_pos.le
        _ = B_Afib := by
            dsimp only [B_Afib, B_sup]
            have hrp_eq : U ^ (D_dual.t / 4) *
                U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t) =
                U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + (29 / 4 : ℝ) * D_dual.t) := by
              rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
            calc _ = (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp *
                      X_col * (U ^ (D_dual.t / 4) *
                        U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + 7 * D_dual.t)) * wt_t := by ring
              _ = _ := by rw [hrp_eq]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : W_ball => (split_w w).2.val)
      (fun w hw => Finset.mem_image_of_mem (fun w : W_ball => (split_w w).2.val) hw)]
    calc _ ≤ ∑ _A ∈ A_set, B_Afib := Finset.sum_le_sum hAfib_bound
      _ = (A_set.card : ℝ) * B_Afib := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (512 * U ^ x6) * B_Afib :=
          mul_le_mul_of_nonneg_right hA_card
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCdiv10_pos.le hC_unp.le) hX_col_pos.le)
              (Real.rpow_nonneg hU_pos.le _)) hwt_pos.le)
      _ = B_shell := by
          dsimp only [B_Afib, B_shell]
          have hrp_x6 : U ^ x6 *
              U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + (29 / 4 : ℝ) * D_dual.t) =
              U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (29 / 4 : ℝ) * D_dual.t) := by
            rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
          calc _ = 512 * (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp *
                    X_col * (U ^ x6 *
                      U ^ (1 - 3 * ell_in - 5 * u_act - x6 + pad_T + (29 / 4 : ℝ) * D_dual.t)) * wt_t := by ring
            _ = _ := by rw [hrp_x6]
  have hW_attach :
      (∑ w ∈ W_ball,
        ‖inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
          (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w‖ ^ 2) =
      ∑ w : W_ball,
        ‖inputConjugateRow p χ_p Finset.univ Ψ₀ (m * d_D) 1 1
          (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w.val‖ ^ 2 :=
    (Finset.sum_coe_sort W_ball _).symm
  change (∑ w ∈ W_ball, _) ≤ _
  rw [hW_attach, ← Finset.sum_fiberwise_of_maps_to (g := k_A)
    (fun w _ => Finset.mem_image_of_mem k_A (Finset.mem_univ w))]
  calc _ ≤ ∑ _k ∈ K_A_set, B_shell := Finset.sum_le_sum hshell_bound
    _ = (K_A_set.card : ℝ) * B_shell := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C_log * U ^ (D_dual.t / 4)) * B_shell :=
        mul_le_mul_of_nonneg_right hKA_card
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCdiv10_pos.le)
            hC_unp.le) hX_col_pos.le) (Real.rpow_nonneg hU_pos.le _)) hwt_pos.le)
    _ = _ := by
        dsimp only [B_shell, C_W]
        have hrp_k : U ^ (D_dual.t / 4) *
            U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (29 / 4 : ℝ) * D_dual.t) =
            U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (15 / 2 : ℝ) * D_dual.t) := by
          rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
        calc _ = (C_log * 512 * (C_div ^ 10 * (2 : ℝ) ^ (10 * ε_div)) * C_unp) *
                  X_col * (U ^ (D_dual.t / 4) *
                    U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (29 / 4 : ℝ) * D_dual.t)) * wt_t := by ring
          _ = _ := by rw [hrp_k]

/-- **Cell-summed `globalPriorityOriginalEnergy` at `Q = {0}` (`dual_qzero_cell_energy`):**
Bounds the weighted `globalPriorityOriginalEnergy` over `labelParentCell p Finset.univ {0}` for
both `negative = true` and `negative = false` uniformly across all live keys `k` and heights
`z_ht : Frequency × (Fin 9 → ℝ)`. -/
theorem dual_qzero_cell_energy
    (hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (D D_dual : Parameters.HighData subDelta)
    (h2000_eps : 2000 * D_dual.ε ≤ D_dual.t)
    (h2000_e : 2000 * D_dual.e ≤ D_dual.t)
    (hfine_dual : ∀ k, D_dual.ell k ≤ detectorMesh subDelta D_dual.t / 200)
    (emb : Fin D.N ↪ Fin D_dual.N)
    (hemb : ∀ j, D_dual.ell (emb j) = (2 / 3 : ℝ) * D.ell j)
    (F_dual : ProbeFinalAssembly.SourceData D_dual)
    (om_outer : 𝓢(ℝ, ℂ)) {b_out : ℝ} (hb_out : ∀ y, om_outer y ≠ 0 → y ≤ b_out)
    (omega₁ omega₂ : 𝓢(ℝ, ℂ)) {lo_o hi_o : ℝ} (hlo_o : 0 < lo_o) (hlh_o : lo_o ≤ hi_o)
    (hs_o1 : Function.support (omega₁ : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o)
    (hs_o2 : Function.support (omega₂ : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o)
    (M_drop : ℕ) (Lcap η τ : ℝ) (hLcap : 1 ≤ Lcap)
    (hη_pos : 0 < η) (hη1 : η ≤ 1) (hτ_pos : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ (τ_dual B_pool : ℝ) (deg_cell : ℕ),
      0 < τ_dual ∧ 2 * τ_dual ≤ D_dual.t ∧ 1 ≤ B_pool ∧
      ∀ data : RowData, ∃ C_cell U_cell : ℝ, 0 < C_cell ∧ 2 ≤ U_cell ∧
      ∀ U : ℝ, U_cell ≤ U →
      2 ≤ U ^ η → b_out ≤ U ^ η →
      ∀ Dpool : ℕ, B_pool * U ^ (Lcap + 2) ≤ (Dpool : ℝ) →
      let q_per := InverseInitialExcludedPeriod.deletedPeriod (basePeriod data)
      let F_pool := CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q_per) Dpool
      let hFa := CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q_per) Dpool
        (reflectionExcludedPrimes_bad q_per)
      letI : ∀ j : primePool F_pool, (Ideal.span {poolPrimary F_pool j}).IsMaximal :=
        fun j => by rw [poolPrimary_span F_pool hFa j]; infer_instance
      let p := poolPrimary F_pool
      let hp := poolPrimary_ne_zero F_pool hFa
      let hcop := poolPrimary_coprime F_pool hFa
      let hg := poolPrimary_good F_pool hFa
      let hinj : Function.Injective (fun j : primePool F_pool => Ideal.span {p j}) :=
        fun j₁ j₂ h => Subtype.ext (by dsimp only [p] at h; simpa only [poolPrimary_span F_pool hFa] using h)
      let base := InverseInitialRayAttachment.elementCharacter
        (InverseInitialConjugateEnergy.conjugateIdealCharacter
          (idealCoeff (deletedBase data)).toMonoidHom)
      ∀ {d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T : ℝ},
        1 / 2 ≤ d_outer → d_outer ≤ 5 / 6 →
        17 / 25 ≤ r_param → r_param ≤ 19 / 26 →
        0 ≤ θ_s → θ_s ≤ 1 →
        0 ≤ ell_in → ell_in ≤ 3 / 500 →
        0 ≤ z_Jv → z_Jv ≤ ell_in →
        0 ≤ V₀ → 0 ≤ F_p → F_p ≤ Lcap → 0 ≤ pad_T →
      let u_act := θ_s * stage1Width r_param
      let z_rem_th := (1 - θ_s) * ((1 - r_param) / 2) + θ_s * stage1RemWidth r_param
      let r_new := F_p - V₀ - 3 * ell_in - u_act
      let M_new := (2 * F_p - 1 + 30 * η + 2 * τ) + 4 * u_act + η
      (-η) ≤ r_new → r_new ≤ Lcap → 0 ≤ M_new → M_new ≤ Lcap →
      ∀ (S_rem : Finset (Fin D.N)),
        (∑ i ∈ S_rem, D.ell i / d_outer) ≤ z_rem_th - z_Jv + pad_T →
        F_p - ((∑ i ∈ S_rem, D.ell i / d_outer) + u_act + z_Jv) + 2 * η ≤ r_param →
      let Z_slot : Fin D.N → ℝ := fun j => U ^ (D.ell j / d_outer)
      let Z_dual : ℝ := U ^ (3 / (2 * d_outer))
      (∀ j ∈ S_rem, ((deletedBase data).modulus.absNorm : ℝ) < Z_slot j) →
      ∀ (lists_full lists_v : Fin D.N → Finset (primePool F_pool)),
        (∀ j ∈ S_rem, lists_full j = InverseInitialCommonLists.poolList F_pool
          (InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j))) →
        (∀ j ∈ S_rem, lists_v j ⊆ lists_full j) →
        (∀ j ∈ S_rem, ((lists_full j \ lists_v j).card : ℝ) ≤ (M_drop : ℝ)) →
        (S_rem : Set (Fin D.N)).PairwiseDisjoint lists_v →
      ∀ (ζ_base : ℂ), ζ_base.re = 17 / 50 → |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_dual →
      ∀ (a : Fin D.N → primePool F_pool → ℂ),
        (∀ j ∈ S_rem, ∀ q ∈ lists_full j,
          a j q = primeProfile F_dual.W (Z_slot j) ζ_base q.val /
            star (idealCoeff (deletedBase data) q.val)) →
      ∀ (labels : Finset (Ideal O)), (∀ I ∈ labels, I ≠ 0) →
      ∀ (β : Ideal O → (primePool F_pool →₀ ℕ) → ℂ) (Ψ : O →* ℂ) (m : O),
        CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀ u, ‖Ψ u‖ ≤ 1) →
        m ≠ 0 → ‖ringComplex m‖ ^ 2 ≤ U ^ (2 * Lcap) →
      ∀ (ξ_out : ℝ),
      let mark := fun (v : primePool F_pool →₀ ℕ) U_set =>
        primeMark S_rem lists_v a (v.support ∪ U_set)
      let Y_src := U ^ (2 * Lcap + 15 * η + τ)
      let cutoff := fun (q : CubeCoordinates (primePool F_pool)) C (_I : Ideal O) D_set =>
        firstDyadicRadius p q C D_set U M_new r_new 0 V₀ η τ
      let W_src := fun y => normTwistedSource (om_outer : ℝ → ℂ) ξ_out (y / U ^ r_new)
      let source := firstGlobalRetainedSource p (firstOriginalOuter Finset.univ {0})
        (fun _ => labels) (fun x => x.1) Y_src
      let keys := liveJointKeys p source Finset.univ
        (sourceSummand p hp hg β cutoff Ψ m mark W_src rowMajorant (U ^ M_new))
      ∀ k ∈ keys, ∀ z_ht : Frequency × (Fin 9 → ℝ), ∀ negative : Bool,
        let omega_b : 𝓢(ℝ, ℂ) := if negative then omega₁ else omega₂
        let idx_b : Fin 9 := if negative then 7 else 8
        let idx_a : Fin 6 := if negative then 0 else 1
        let extra_b : CubeCoordinates (primePool F_pool) → Finset (primePool F_pool) :=
          if negative then (fun q => q.rightExponent.support) else (fun q => q.leftExponent.support)
        (U ^ (firstKappa M_new r_new 0 V₀ (dyadicExponent U (k.1 3))
            (dyadicExponent U (k.1 idx_a)) (dyadicExponent U (k.1 2)) (dyadicExponent U (k.1 4))) *
          Real.exp ((9 / 2 : ℝ) * (η * Real.log U))) *
        globalPriorityOriginalEnergy p hg hp hinj extra_b Finset.univ
          (labelParentCell p Finset.univ {0} (fun _ _ => 1) k.1 k.2.1 k.2.2)
          (fun x => (‖commonSelector p (fun _ => 1) k.2.1 x.quotientSupport‖ : ℂ))
          negative Ψ m S_rem lists_v a omega_b
          ((physicalScales (U ^ r_new) k.1 k.2.1) idx_b)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z_ht.1 z_ht.2 idx_b)
          (firstCellRadius U M_new r_new 0 V₀ η τ k.1 k.2.2) ≤
        C_cell * U ^ (F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t) *
          (tripleHeight (firstDegree deg_cell) z_ht.1 *
            coordinateHeight (firstDegree deg_cell) z_ht.2) := by
  obtain ⟨τ_d1, B_p1, deg_w1, hτ_p1, hτ_le1, hBp1_2, hW_all1⟩ :=
    dual_qzero_W_ball_single_omega hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb
      F_dual omega₁ hlo_o hlh_o hs_o1 true M_drop Lcap η τ hLcap hη_pos hη1 hτ_pos hτ1
  obtain ⟨τ_d2, B_p2, deg_w2, hτ_p2, hτ_le2, _hBp2_2, hW_all2⟩ :=
    dual_qzero_W_ball_single_omega hβ51 D D_dual h2000_eps h2000_e hfine_dual emb hemb
      F_dual omega₂ hlo_o hlh_o hs_o2 false M_drop Lcap η τ hLcap hη_pos hη1 hτ_pos hτ1
  let τ_dual : ℝ := min τ_d1 τ_d2
  have hτ_dual_pos : 0 < τ_dual := lt_min hτ_p1 hτ_p2
  have hτ_dual_le : 2 * τ_dual ≤ D_dual.t := by
    have hle : τ_dual ≤ τ_d1 := min_le_left _ _; linarith only [hle, hτ_le1]
  let B_pool : ℝ := max B_p1 B_p2
  have hBp1 : 1 ≤ B_pool := by have hm := le_max_left B_p1 B_p2; linarith only [hBp1_2, hm]
  let deg_cell : ℕ := max deg_w1 deg_w2
  let ε_div : ℝ := D_dual.t / (80 * (6 * Lcap + 30))
  have hε_div : 0 < ε_div := by dsimp only [ε_div]; have := D_dual.t_pos; positivity
  obtain ⟨C_div, hC_div, hdiv_le⟩ := ideal_divisor_small_power ε_div hε_div
  let B_om1 : ℝ := SchwartzMap.seminorm ℝ 0 0 omega₁
  have hB_om1 : ∀ x : ℝ, ‖omega₁ x‖ ≤ B_om1 := fun x => by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      SchwartzMap.norm_le_seminorm ℝ omega₁ x
  let B_om2 : ℝ := SchwartzMap.seminorm ℝ 0 0 omega₂
  have hB_om2 : ∀ x : ℝ, ‖omega₂ x‖ ≤ B_om2 := fun x => by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      SchwartzMap.norm_le_seminorm ℝ omega₂ x
  let B_om : ℝ := max 1 (max B_om1 B_om2)
  have hB_om0 : 0 < B_om := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨τ_dual, B_pool, deg_cell, hτ_dual_pos, hτ_dual_le, hBp1, ?_⟩
  intro data
  obtain ⟨C_W1, U_W1, hC_W1, hU_W1, hW1⟩ := hW_all1 data
  obtain ⟨C_W2, U_W2, hC_W2, _hU_W2, hW2⟩ := hW_all2 data
  let U_cell : ℝ := max U_W1 U_W2
  have hU_cell2 : 2 ≤ U_cell := hU_W1.trans (le_max_left _ _)
  let C_W_max : ℝ := max C_W1 C_W2
  have hCW_max_pos : 0 < C_W_max := hC_W1.trans_le (le_max_left _ _)
  let c_min : ℝ := (21 / 20 : ℝ) * D.rmin
  let B_E_max : ℝ := 6 * Lcap + 35
  let C_hit : ℝ := (((⌈B_E_max / c_min⌉₊ + 1 : ℕ) : ℝ) ^ 2) ^ D.N
  have hChit_pos : 0 < C_hit := pow_pos (pow_pos (by exact_mod_cast Nat.succ_pos _) 2) D.N
  let N_ray_core : ℝ := (Fintype.card (RayCharacter × RayCharacter) : ℝ) *
    (Fintype.card FirstCoreIndex : ℝ) * (2 : ℝ) ^ D.N
  have hNrc_nn : 0 ≤ N_ray_core :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg zero_le_two _)
  let C_outer : ℝ := (firstCoreMassBound + 1) * (2 : ℝ) ^ D.N * N_ray_core *
    coefficientBound * C_hit
  have hCouter_nn : 0 ≤ C_outer :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (add_nonneg firstCoreMassBound_nonneg zero_le_one) (pow_nonneg zero_le_two _)) hNrc_nn)
      coefficientBound_pos.le) hChit_pos.le
  let C_z0_part : ℝ := 49 * 49 * C_div * (2 : ℝ) ^ ε_div * B_om ^ 2
  have hCz0_pos : 0 < C_z0_part :=
    mul_pos (mul_pos (mul_pos (by norm_num) hC_div) (Real.rpow_pos_of_pos zero_lt_two _))
      (pow_pos hB_om0 2)
  have hCdiv2_pos : 0 < C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) :=
    mul_pos (pow_pos hC_div 2) (Real.rpow_pos_of_pos zero_lt_two _)
  let C_nz_part : ℝ := 49 * (C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div)) * C_W_max
  have hCnz_pos : 0 < C_nz_part := mul_pos (mul_pos (by norm_num) hCdiv2_pos) hCW_max_pos
  let C_cell : ℝ := C_outer * (C_z0_part + C_nz_part) + 1
  have hCcell_pos : 0 < C_cell :=
    add_pos_of_nonneg_of_pos (mul_nonneg hCouter_nn (add_pos hCz0_pos hCnz_pos).le) zero_lt_one
  refine ⟨C_cell, U_cell, hCcell_pos, hU_cell2, ?_⟩
  intro U hU h2_η hb_out_η Dpool hDpool
    q_per F_pool hFa p hp hcop hg hinj base
    d_outer r_param θ_s ell_in z_Jv V₀ F_p pad_T
    hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0 hFp0 hFp_L hpad0
    u_act z_rem_th r_new M_new hrn_lo hrn_hi hMn_lo hMn_hi
    S_rem hz_Srem hFp_r Z_slot Z_dual hlarge_Z
    lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
    ζ_base hζ_re hζ_im a ha_eq labels hlabels β Ψ m hΨ_base hΨ1 hm_ne hm_norm ξ_out
    mark Y_src cutoff W_src source keys k hk z_ht negative omega_b idx_b idx_a extra_b
  letI : ∀ i : primePool F_pool, (Ideal.span {p i}).IsMaximal :=
    fun i => by dsimp only [p]; rw [poolPrimary_span F_pool hFa i]; infer_instance
  have hU2 : 2 ≤ U := hU_cell2.trans hU
  have hU1 : 1 < U := by linarith only [hU2]
  have hU_pos : 0 < U := zero_lt_one.trans hU1
  have hd_pos : 0 < d_outer := by linarith only [hd_lo]
  have ht_pos : 0 < D_dual.t := D_dual.t_pos
  let cell := labelParentCell p Finset.univ {0} (fun _ _ => 1) k.1 k.2.1 k.2.2
  have hw_one : 1 ≤ tripleHeight (firstDegree deg_cell) z_ht.1 *
      coordinateHeight (firstDegree deg_cell) z_ht.2 :=
    first_weight_one_le (firstDegree deg_cell) z_ht
  have hw_pos : 0 < tripleHeight (firstDegree deg_cell) z_ht.1 *
      coordinateHeight (firstDegree deg_cell) z_ht.2 :=
    zero_lt_one.trans_le hw_one
  by_cases hcell_ne : cell.Nonempty
  swap
  · have hce : labelParentCell p Finset.univ {0} (fun _ _ => 1) k.1 k.2.1 k.2.2 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcell_ne
    rw [hce]; unfold globalPriorityOriginalEnergy
    simp only [Finset.sum_empty, Complex.zero_re, Finset.sum_const_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hCcell_pos.le (Real.rpow_nonneg hU_pos.le _)) hw_pos.le
  obtain ⟨x₀, hx₀⟩ := hcell_ne
  obtain ⟨hcell_data, hcell_inj⟩ := qzero_labelParentCell_data p hp Finset.univ k hU1 h2_η
  obtain ⟨_, _, _, _, hk0_z, hk1_z, hk4_z, hkj_z, _, _, _⟩ := hcell_data x₀ hx₀
  have hidx_a_z : dyadicExponent U (k.1 idx_a) = 0 := by
    dsimp only [idx_a]; cases negative <;> [exact hk1_z; exact hk0_z]
  have hlive_caps := InverseMoment.original_live_exponent_caps p hp hcop hg Finset.univ {0} labels
    β cutoff Ψ m mark (om_outer : ℝ → ℂ) rowMajorant (U ^ M_new) U r_new 0 Lcap η τ ξ_out b_out
    hU1 h2_η (by linarith only [hLcap]) hrn_hi (by linarith only [hLcap]) hη_pos.le hτ_pos.le hb_out_η
    (fun v hv => by
      rw [Finset.mem_singleton.mp hv]
      simp only [Finsupp.support_zero, primeProduct, Finset.prod_empty, map_one, norm_one, one_pow]
      exact Real.one_le_rpow hU1.le (by linarith only [hη_pos]))
    hlabels hb_out k hk
  let B_c : ℝ := dyadicExponent U (k.1 2)
  let δ_c : ℝ := dyadicExponent U (k.1 3)
  let t_q : ℝ := dyadicExponent U k.2.1
  have hBc_0 : 0 ≤ B_c := (hlive_caps.1 2).1
  have hBc_hi : B_c ≤ 3 * Lcap + 15 * η + τ := (hlive_caps.1 2).2
  have hδc_0 : 0 ≤ δ_c := (hlive_caps.1 3).1
  have htq_0 : 0 ≤ t_q := hlive_caps.2.1.1
  have htq_hi : t_q ≤ 3 * Lcap + 15 * η + τ := hlive_caps.2.1.2
  let X_col : ℝ := (physicalScales (U ^ r_new) k.1 k.2.1) idx_b
  have hX_col_eq : X_col = U ^ (r_new - B_c - t_q) := by
    dsimp only [X_col, idx_b]
    cases negative
    · simp only [Bool.false_eq_true, ite_false]
      change U ^ r_new / (InverseSecondSourceBlocks.dyadScale (k.1 1) *
        InverseSecondSourceBlocks.dyadScale (k.1 2) *
        InverseSecondSourceBlocks.dyadScale k.2.1) = _
      rw [raw_column_exponent U r_new hU1, hk1_z, sub_zero]
    · simp only [ite_true]
      change U ^ r_new / (InverseSecondSourceBlocks.dyadScale (k.1 0) *
        InverseSecondSourceBlocks.dyadScale (k.1 2) *
        InverseSecondSourceBlocks.dyadScale k.2.1) = _
      rw [raw_column_exponent U r_new hU1, hk0_z, sub_zero]
  have hX_col_pos : 0 < X_col := by rw [hX_col_eq]; exact Real.rpow_pos_of_pos hU_pos _
  have hW_src_le : ∀ y, W_src y ≠ 0 → y ≤ b_out * U ^ r_new := by
    intro y hy
    have hom_ne : om_outer (y / U ^ r_new) ≠ 0 := fun hz => hy (by simp [W_src, normTwistedSource, hz])
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hU_pos _)).mp (hb_out _ hom_ne)
  have hcol_live : B_c + t_q ≤ r_new + η := by
    have hsc := original_live_column_scale p hp hcop hg Finset.univ {0} labels Y_src β cutoff
      Ψ m mark W_src rowMajorant (U ^ M_new) (U ^ r_new) b_out (Real.rpow_pos_of_pos hU_pos _)
      hW_src_le k hk
    have h1 : 1 ≤ X_col * b_out := by
      dsimp only [X_col, idx_b]; cases negative <;> [exact hsc.2; exact hsc.1]
    have h2 : X_col * b_out ≤ U ^ (r_new - B_c - t_q + η) := by
      rw [hX_col_eq, Real.rpow_add hU_pos]
      exact mul_le_mul_of_nonneg_left hb_out_η (Real.rpow_nonneg hU_pos.le _)
    have h3 : 0 ≤ r_new - B_c - t_q + η := by
      have hrp := h1.trans h2
      rwa [← Real.rpow_zero U, Real.rpow_le_rpow_left_iff hU1] at hrp
    linarith only [h3]
  let Y_cell : ℝ := firstCellRadius U M_new r_new 0 V₀ η τ k.1 k.2.2
  let H_th : ℝ := 1 - 6 * u_act
  let Y_exp : ℝ := 2 * r_new - 2 * B_c - M_new + 2 * V₀ + δ_c + 12 * η + τ
  have hY_exp_eq : Y_exp = H_th - 6 * ell_in - 2 * B_c + δ_c - 19 * η - τ := by
    dsimp only [Y_exp, r_new, M_new, H_th]; ring
  have hY_cell_eq : Y_cell = U ^ Y_exp := by
    dsimp only [Y_cell]; unfold firstCellRadius firstPhysicalHeight
    rw [hkj_z]
    exact congrArg (fun x : ℝ => U ^ x) (by dsimp only [Y_exp, B_c, δ_c]; ring)
  have hY_cell_pos : 0 < Y_cell := by rw [hY_cell_eq]; exact Real.rpow_pos_of_pos hU_pos _
  have hY_exp_nn : 0 ≤ Y_exp := by
    have h1 := first_live_cell_radius_one p hp hcop hg Finset.univ {0} labels
      Y_src U M_new r_new 0 V₀ η τ β Ψ m mark W_src rowMajorant (U ^ M_new) hlabels k hk
    change 1 ≤ Y_cell at h1
    rwa [hY_cell_eq, ← Real.rpow_zero U, Real.rpow_le_rpow_left_iff hU1] at h1
  let kappa_val : ℝ := firstKappa M_new r_new 0 V₀ δ_c (dyadicExponent U (k.1 idx_a)) B_c
    (dyadicExponent U (k.1 4))
  have hkappa_eq : kappa_val = M_new - 2 * r_new - V₀ - δ_c + B_c := by
    dsimp only [kappa_val]; rw [hidx_a_z, hk4_z]; unfold firstKappa; ring
  let pref_U : ℝ := U ^ kappa_val * Real.exp ((9 / 2 : ℝ) * (η * Real.log U))
  have hpref_eq : pref_U = U ^ (kappa_val + (9 / 2 : ℝ) * η) := by
    dsimp only [pref_U]
    rw [Real.rpow_add hU_pos, Real.rpow_def_of_pos hU_pos ((9 / 2 : ℝ) * η)]
    exact congrArg (fun x : ℝ => U ^ kappa_val * Real.exp x) (by ring)
  have hpref_pos : 0 < pref_U := by rw [hpref_eq]; exact Real.rpow_pos_of_pos hU_pos _
  have hZ_slot_pos : ∀ j : Fin D.N, 0 < Z_slot j :=
    fun j => Real.rpow_pos_of_pos hU_pos _
  have hlists_bounds : ∀ j ∈ S_rem, ∀ q ∈ lists_full j,
      Z_slot j ≤ ‖ringComplex (p q)‖ ^ 2 ∧ ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot j ∧
        ‖a j q‖ ≤ 1 := by
    intro j hj q hq
    have hqL : q.val ∈ InverseInitialPhysicalSlots.livePrimes F_dual.modulus ⊤ F_dual.W 2 (Z_slot j) := by
      rw [hlists_full j hj] at hq; exact (mem_filter_of hq).2
    have hlpd := livePrime_data F_dual.modulus ⊤ F_dual.W 1 2 (Z_slot j)
      (hZ_slot_pos j) F_dual.complex_support q.val hqL
    have hd_live := deleted_source_live_prime F_dual data F_dual.modulus ⊤ (Z_slot j)
      (hZ_slot_pos j) ζ_base (by rw [hζ_re]; norm_num) (hlarge_Z j hj) q.val hqL
    have hspan_q : ‖ringComplex (p q)‖ ^ 2 = (q.val.absNorm : ℝ) := by
      dsimp only [p]; rw [ringComplex_norm_sq_eq_absNorm_span, poolPrimary_span F_pool hFa q]
    have ha_n : ‖a j q‖ ≤ 1 := by
      rw [ha_eq j hj q hq, norm_div, norm_star, ← norm_star (primeProfile _ _ _ _), ← norm_div]
      exact hd_live.2.2.2.2
    exact ⟨hspan_q ▸ (one_mul (Z_slot j) ▸ hlpd.2.2.1), hspan_q ▸ hlpd.2.2.2, ha_n⟩
  have hlists_v_b : ∀ j ∈ S_rem, ∀ q ∈ lists_v j,
      Z_slot j ≤ ‖ringComplex (p q)‖ ^ 2 ∧ ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot j ∧ ‖a j q‖ ≤ 1 :=
    fun j hj q hq => hlists_bounds j hj q (hlists_v j hj hq)
  have hSrem_card : S_rem.card ≤ D.N :=
    (Finset.card_le_univ S_rem).trans_eq (Fintype.card_fin D.N)
  let t_ht : ℝ := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z_ht.1 z_ht.2 idx_b
  have hht_deg : (1 + ‖t_ht‖) ^ (2 * deg_cell) ≤
      tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2 := by
    have h1 : (1 + ‖firstHeight negative z_ht‖) ^ (2 * deg_cell) ≤
        (1 + ‖firstHeight negative z_ht‖) ^ (firstDegree deg_cell) := by
      apply pow_le_pow_right₀ (add_nonneg zero_le_one (norm_nonneg (firstHeight negative z_ht)))
      unfold firstDegree InverseClippingProfiles.momentOrder; omega
    exact h1.trans (first_height_cost deg_cell negative z_ht)
  have hZd_ge1 : 1 ≤ Z_dual :=
    Real.one_le_rpow hU1.le (div_nonneg (by norm_num) (by positivity))
  let E_target : ℝ := U ^ (F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t) *
    (tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2)
  have hE_target_pos : 0 < E_target := mul_pos (Real.rpow_pos_of_pos hU_pos _) hw_pos
  have hslice_bound : ∀ (ray : RayCharacter × RayCharacter) (core : FirstCoreIndex),
      ∀ J ∈ S_rem.powerset,
        pref_U * (∑ x ∈ cell,
          globalPriorityOuter p hg negative Ψ m ray core
            (fun x => (‖commonSelector p (fun _ => 1) k.2.1 x.quotientSupport‖ : ℂ)) x *
          (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
          parentPoisson p hp hg hinj Finset.univ negative Ψ m S_rem J
            (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)).re ≤
        coefficientBound * C_hit * (C_z0_part + C_nz_part) * E_target := by
    intro ray core J hJ_pow
    have hJ_sub : J ⊆ S_rem := Finset.mem_powerset.mp hJ_pow
    let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    have hΨ₀_base : CanonicalCoefficientClass.IsBaseRayTwist base Ψ₀ := hΨ_base.firstCore _ _ _
    have hΨ₀_norm : ∀ u, ‖Ψ₀ u‖ ≤ 1 :=
      fun u => (firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ1 u)
    let hs_ob : Function.support (omega_b : ℝ → ℂ) ⊆ Set.Icc lo_o hi_o := by
      dsimp only [omega_b]; cases negative <;> [exact hs_o2; exact hs_o1]
    let V_win : 𝓢(ℝ, ℂ) := principalWindow omega_b lo_o hi_o hlo_o hs_ob negative t_ht
    let χ_p := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
    let cell_J := cell.filter (fun x => primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport) ≠ 0)
    have hre_le0 := parentPoisson_qzero_slice_le p hp hcop hg hinj (poolPrimary_odd F_pool hFa)
      Finset.univ cell (fun x hx => ⟨(hcell_data x hx).1, (hcell_data x hx).2.1⟩) k.2.1 negative
      extra_b rfl Ψ hΨ1 m S_rem J lists_v a omega_b (lo_o := lo_o) (hi_o := hi_o) hlo_o hs_ob
      X_col t_ht Y_cell hX_col_pos hY_cell_pos ray core
    have hre_le : (∑ x ∈ cell,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x => (‖commonSelector p (fun _ => 1) k.2.1 x.quotientSupport‖ : ℂ)) x *
        (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
        parentPoisson p hp hg hinj Finset.univ negative Ψ m S_rem J
          (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)).re ≤
        coefficientBound * ∑ x ∈ cell_J,
          ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
            (‖inputConjugateRow p χ_p Finset.univ Ψ₀
                (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2 +
              ∑ z ∈ (rowMajorantBall Y_cell).erase 0,
                ‖inputConjugateRow p χ_p Finset.univ Ψ₀
                  (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                  (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                  (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2) := by
      rw [← sum_filter_norm_sq_mul cell
        (fun x => primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport))]
      exact hre_le0
    by_cases hcellJ_ne : cell_J.Nonempty
    swap
    · have hcb_pos := coefficientBound_pos
      have hceJ : cell_J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcellJ_ne
      rw [hceJ, Finset.sum_empty, mul_zero] at hre_le
      calc _ ≤ pref_U * 0 := mul_le_mul_of_nonneg_left hre_le hpref_pos.le
        _ = 0 := mul_zero _
        _ ≤ _ := mul_nonneg (mul_nonneg (mul_nonneg hcb_pos.le hChit_pos.le)
            (add_nonneg hCz0_pos.le hCnz_pos.le)) hE_target_pos.le
    obtain ⟨x₁, hx₁⟩ := hcellJ_ne
    have hdisj_J : (J : Set (Fin D.N)).PairwiseDisjoint lists_v :=
      fun i hi j hj hij => hdisj_v (hJ_sub hi) (hJ_sub hj) hij
    have hpN_union_le : ∀ x ∈ cell,
        primeProductNorm p (x.firstCommon ∪ x.quotientSupport) ≤ U ^ (B_c + t_q + 2 * η) := by
      intro x hx
      have hd := hcell_data x hx
      have hp_ge1 : ∀ q : primePool F_pool, 1 ≤ ‖ringComplex (p q)‖ ^ 2 :=
        fun q => SchwartzPlanePoisson.one_le_eisenstein_norm_sq (p q) (hp q)
      have hsub_prod : primeProductNorm p (x.firstCommon ∪ x.quotientSupport) ≤
          primeProductNorm p x.firstCommon * primeProductNorm p x.quotientSupport := by
        have hun : x.firstCommon ∪ (x.quotientSupport \ x.firstCommon) =
            x.firstCommon ∪ x.quotientSupport := Finset.union_sdiff_self_eq_union
        rw [← hun, primeProductNorm_union p _ _ Finset.disjoint_sdiff]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        unfold primeProductNorm
        have hsub_q : x.quotientSupport \ x.firstCommon ⊆ x.quotientSupport := Finset.sdiff_subset
        rw [map_prod, norm_prod, ← Finset.prod_pow, map_prod, norm_prod, ← Finset.prod_pow,
          ← Finset.prod_sdiff hsub_q]
        exact le_mul_of_one_le_left (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
          (Finset.one_le_prod (fun q _ => hp_ge1 q))
      calc primeProductNorm p (x.firstCommon ∪ x.quotientSupport)
          ≤ primeProductNorm p x.firstCommon * primeProductNorm p x.quotientSupport := hsub_prod
        _ ≤ U ^ (B_c + η) * U ^ (t_q + η) :=
            mul_le_mul hd.2.2.2.2.2.2.2.2.1.2 hd.2.2.2.2.2.2.2.2.2.2.2
              (sq_nonneg _) (Real.rpow_nonneg hU_pos.le _)
        _ = U ^ (B_c + t_q + 2 * η) := by
            rw [← Real.rpow_add hU_pos]; exact congrArg (fun x : ℝ => U ^ x) (by ring)
    have hBE_le_max : B_c + t_q + 2 * η ≤ B_E_max := by
      dsimp only [B_E_max]; linarith only [hBc_hi, htq_hi, hη1, hτ1]
    have hhit_x₁ := qzero_primeMark_hit_bound D p hp J lists_v hdisj_J a
      (fun i hi q hq => (hlists_v_b i (hJ_sub hi) q hq).2.2)
      (U := U) (d_outer := d_outer) (B_E := B_c + t_q + 2 * η) hU1 hd_lo hd_hi
      (by linarith only [hBc_0, htq_0, hη_pos])
      (fun i hi q hq => (hlists_v_b i (hJ_sub hi) q hq).1)
      (x₁.firstCommon ∪ x₁.quotientSupport)
      (hpN_union_le x₁ (mem_filter_of hx₁).1)
      (mem_filter_of hx₁).2
    have hzJ_act_le : (∑ i ∈ J, D.ell i / d_outer) ≤ B_c + t_q + 2 * η := hhit_x₁.1
    have hpm_sq_le : ∀ x ∈ cell_J,
        ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 ≤ C_hit := by
      intro x hxJ
      have hh := qzero_primeMark_hit_bound D p hp J lists_v hdisj_J a
        (fun i hi q hq => (hlists_v_b i (hJ_sub hi) q hq).2.2)
        (U := U) (d_outer := d_outer) (B_E := B_E_max) hU1 hd_lo hd_hi
        (by dsimp only [B_E_max]; linarith only [hLcap])
        (fun i hi q hq => (hlists_v_b i (hJ_sub hi) q hq).1)
        (x.firstCommon ∪ x.quotientSupport)
        ((hpN_union_le x (mem_filter_of hxJ).1).trans
          (Real.rpow_le_rpow_of_exponent_le hU1.le hBE_le_max))
        (mem_filter_of hxJ).2
      have hcard_J : J.card ≤ D.N := (Finset.card_le_card hJ_sub).trans hSrem_card
      have hbase_ge1 : 1 ≤ ((⌈B_E_max / c_min⌉₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hpow_le : (((⌈B_E_max / c_min⌉₊ + 1 : ℕ) : ℝ) ^ J.card) ^ 2 ≤ C_hit := by
        dsimp only [C_hit]; rw [← pow_mul, Nat.mul_comm, pow_mul]
        exact pow_le_pow_right₀ (one_le_pow₀ hbase_ge1) hcard_J
      exact (pow_le_pow_left₀ (norm_nonneg _) hh.2 2).trans hpow_le
    have hz0_term_le : ∀ x ∈ cell_J,
        ‖inputConjugateRow p χ_p Finset.univ Ψ₀
          (m * ∏ i ∈ x.quotientSupport, p i) 1 1
          (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2 ≤ B_om ^ 2 := by
      intro x _
      rw [inputConjugateRow_at_zero p hg Finset.univ Ψ₀ _ 1 1 _]
      unfold markedRadial; simp only [Finset.empty_union]
      have hpm_le1 : ‖primeMark (S_rem \ J) lists_v a ∅‖ ≤ 1 := by
        by_cases hne_rem : (S_rem \ J).Nonempty
        · obtain ⟨i₀, hi₀⟩ := hne_rem
          have h0 : primeMark (S_rem \ J) lists_v a ∅ = 0 := by
            unfold primeMark; apply Finset.prod_eq_zero hi₀; simp [primeSlot]
          rw [h0, norm_zero]; exact zero_le_one
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne_rem]; simp [primeMark]
      have hV_le : ‖V_win (primeProductNorm p ∅ / X_col)‖ ≤ B_om := by
        dsimp only [V_win, omega_b]; rw [principalWindow_norm]
        cases negative
        · simp only [Bool.false_eq_true, ite_false]
          exact (hB_om2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
        · simp only [ite_true]
          exact (hB_om1 _).trans ((le_max_left _ _).trans (le_max_right _ _))
      rw [norm_mul, mul_pow]
      exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hpm_le1)
        (pow_le_pow_left₀ (norm_nonneg _) hV_le 2) (sq_nonneg _) zero_le_one).trans_eq (one_mul _)
    let B_nz : Finset O := (rowMajorantBall Y_cell).erase 0
    let W_exp : ℝ := H_th - 6 * ell_in - 17 * η - τ
    let W_ball : Finset O := (firstFrequencyDisk (2 * U ^ W_exp)).erase 0
    have hW_exp_le1 : W_exp ≤ 1 := by
      dsimp only [W_exp, H_th]
      have hw0 : 0 ≤ u_act := by
        dsimp only [u_act]; apply mul_nonneg hθ0
        unfold stage1Width stage1Line; linarith only [hr0, hr1]
      linarith only [hw0, hell0, hη_pos, hτ_pos]
    have hY_W_eq : U ^ (2 * B_c - δ_c + 2 * η) * Y_cell = U ^ W_exp := by
      rw [hY_cell_eq, ← Real.rpow_add hU_pos]
      exact congrArg (fun x : ℝ => U ^ x) (by dsimp only [W_exp]; rw [hY_exp_eq]; ring)
    let K_W_val : ℝ := C_W_max * X_col *
      U ^ (1 - 3 * ell_in - 5 * u_act + pad_T + (15 / 2 : ℝ) * D_dual.t) *
      (tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2)
    have hKW_val_nn : 0 ≤ K_W_val :=
      mul_nonneg (mul_nonneg (mul_nonneg hCW_max_pos.le hX_col_pos.le)
        (Real.rpow_nonneg hU_pos.le _)) hw_pos.le
    have hD_sum_W : ∀ D_q : Finset (primePool F_pool),
        primeProductNorm p D_q ≤ U ^ (t_q + η) →
        (∑ w ∈ W_ball,
          ‖inputConjugateRow p χ_p Finset.univ Ψ₀
            (m * ∏ i ∈ D_q, p i) 1 1
            (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w‖ ^ 2) ≤ K_W_val := by
      intro D_q hDq_norm
      dsimp only [V_win, omega_b, W_ball]
      cases negative
      · simp only [Bool.false_eq_true, ite_false]
        have hDp2 : B_p2 * U ^ (Lcap + 2) ≤ (Dpool : ℝ) :=
          (mul_le_mul_of_nonneg_right (le_max_right B_p1 B_p2) (Real.rpow_nonneg hU_pos.le _)).trans hDpool
        have hζ2 : |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d2 :=
          hζ_im.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_right _ _)) (by norm_num))
        have hb2 := hW2 U ((le_max_right _ _).trans hU) h2_η Dpool hDp2
          hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0 hpad0 hBc_0 htq_0 htq_hi
          hrn_hi hX_col_eq S_rem J hJ_sub hzJ_act_le hz_Srem hFp_r hlarge_Z
          lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
          ζ_base hζ_re hζ2 a ha_eq hlists_v_b Ψ₀ hΨ₀_base hΨ₀_norm m hm_ne hm_norm t_ht D_q hDq_norm
        have hdeg2 : (1 + ‖t_ht‖) ^ (2 * deg_w2) ≤
            tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2 :=
          (pow_le_pow_right₀ (add_nonneg zero_le_one (norm_nonneg t_ht))
            (Nat.mul_le_mul_left 2 (le_max_right deg_w1 deg_w2))).trans hht_deg
        refine hb2.trans ?_; dsimp only [K_W_val]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right C_W1 C_W2) hX_col_pos.le)
            (Real.rpow_nonneg hU_pos.le _))
          hdeg2 (pow_nonneg (add_nonneg zero_le_one (norm_nonneg t_ht)) _)
          (mul_nonneg (mul_nonneg hCW_max_pos.le hX_col_pos.le) (Real.rpow_nonneg hU_pos.le _))
      · simp only [ite_true]
        have hDp1 : B_p1 * U ^ (Lcap + 2) ≤ (Dpool : ℝ) :=
          (mul_le_mul_of_nonneg_right (le_max_left B_p1 B_p2) (Real.rpow_nonneg hU_pos.le _)).trans hDpool
        have hζ1 : |ζ_base.im| ≤ (3 / 4 : ℝ) * Z_dual ^ τ_d1 :=
          hζ_im.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZd_ge1 (min_le_left _ _)) (by norm_num))
        have hb1 := hW1 U ((le_max_left _ _).trans hU) h2_η Dpool hDp1
          hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hV0 hpad0 hBc_0 htq_0 htq_hi
          hrn_hi hX_col_eq S_rem J hJ_sub hzJ_act_le hz_Srem hFp_r hlarge_Z
          lists_full lists_v hlists_full hlists_v hcard_diff hdisj_v
          ζ_base hζ_re hζ1 a ha_eq hlists_v_b Ψ₀ hΨ₀_base hΨ₀_norm m hm_ne hm_norm t_ht D_q hDq_norm
        have hdeg1 : (1 + ‖t_ht‖) ^ (2 * deg_w1) ≤
            tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2 :=
          (pow_le_pow_right₀ (add_nonneg zero_le_one (norm_nonneg t_ht))
            (Nat.mul_le_mul_left 2 (le_max_left deg_w1 deg_w2))).trans hht_deg
        refine hb1.trans ?_; dsimp only [K_W_val]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C_W1 C_W2) hX_col_pos.le)
            (Real.rpow_nonneg hU_pos.le _))
          hdeg1 (pow_nonneg (add_nonneg zero_le_one (norm_nonneg t_ht)) _)
          (mul_nonneg (mul_nonneg hCW_max_pos.le hX_col_pos.le) (Real.rpow_nonneg hU_pos.le _))
    have hcell_data_J : ∀ x ∈ cell_J,
        x.firstDivisor ⊆ x.firstCommon ∧
        primeProductNorm p x.firstCommon ≤ U ^ (B_c + η) ∧
        U ^ δ_c ≤ primeProductNorm p x.firstDivisor ∧
        primeProductNorm p x.quotientSupport ≤ U ^ (t_q + η) := by
      intro x hxJ
      have hd := hcell_data x (mem_filter_of hxJ).1
      exact ⟨hd.2.1, hd.2.2.2.2.2.2.2.2.1.2, hd.2.2.2.2.2.2.2.2.2.1.1,
        hd.2.2.2.2.2.2.2.2.2.2.2⟩
    have hinj_J : Set.InjOn (fun x : Source (primePool F_pool) 0 =>
        ((x.firstCommon, x.firstDivisor), x.quotientSupport)) cell_J :=
      fun x₁ h₁ x₂ h₂ heq => hcell_inj (mem_filter_of h₁).1 (mem_filter_of h₂).1 heq
    obtain ⟨hz0_raw, hnz_raw⟩ := cell_J_z0_and_gcd_fiber_bound p hp hcop cell_J hinj_J
      (fun x hxJ => (hcell_data_J x hxJ).1)
      U B_c δ_c t_q η τ Lcap D_dual.t ε_div C_div Y_cell W_exp C_hit B_om
      hU1 hBc_0 hBc_hi htq_0 hη_pos hη1 hτ_pos hτ1 hLcap ht_pos hε_div rfl hC_div hdiv_le
      hY_cell_pos hW_exp_le1 hY_W_eq (fun x hxJ => (hcell_data_J x hxJ).2) hChit_pos
      (fun x => ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2) hpm_sq_le
      (fun x => ‖inputConjugateRow p χ_p Finset.univ Ψ₀
        (m * ∏ i ∈ x.quotientSupport, p i) 1 1
        (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2)
      (fun _ _ => sq_nonneg _) hz0_term_le
      (fun D_q w => ‖inputConjugateRow p χ_p Finset.univ Ψ₀
        (m * ∏ i ∈ D_q, p i) 1 1
        (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) w‖ ^ 2)
      (fun _ _ => sq_nonneg _) K_W_val hKW_val_nn hD_sum_W
    have hz0_sum_le :
        pref_U * (∑ x ∈ cell_J,
          ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
            ‖inputConjugateRow p χ_p Finset.univ Ψ₀
              (m * ∏ i ∈ x.quotientSupport, p i) 1 1
              (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2) ≤
        C_hit * C_z0_part * E_target := by
      have hexp_z0 : (kappa_val + (9 / 2 : ℝ) * η) + (B_c + t_q + 2 * η + D_dual.t / 4) ≤
          F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t := by
        rw [hkappa_eq]
        dsimp only [Y_exp, r_new] at hY_exp_nn hcol_live ⊢
        have hw0 : 0 ≤ u_act := by
          dsimp only [u_act]; apply mul_nonneg hθ0
          unfold stage1Width stage1Line; linarith only [hr0, hr1]
        linarith only [hY_exp_nn, hcol_live, hBc_0, hell0, hw0, hη_pos, hτ_pos, hpad0, ht_pos]
      calc _ ≤ U ^ (kappa_val + (9 / 2 : ℝ) * η) *
                (C_hit * (49 * 49 * C_div * (2 : ℝ) ^ ε_div * B_om ^ 2) *
                  U ^ (B_c + t_q + 2 * η + D_dual.t / 4)) := by
              rw [← hpref_eq]; exact mul_le_mul_of_nonneg_left hz0_raw hpref_pos.le
        _ = C_hit * C_z0_part *
              U ^ ((kappa_val + (9 / 2 : ℝ) * η) + (B_c + t_q + 2 * η + D_dual.t / 4)) := by
              dsimp only [C_z0_part]; rw [Real.rpow_add hU_pos]; ring
        _ ≤ C_hit * C_z0_part * U ^ (F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_z0)
                (mul_nonneg hChit_pos.le hCz0_pos.le)
        _ ≤ C_hit * C_z0_part * E_target := by
              dsimp only [E_target]; rw [← mul_assoc]
              exact le_mul_of_one_le_right
                (mul_nonneg (mul_nonneg hChit_pos.le hCz0_pos.le) (Real.rpow_nonneg hU_pos.le _))
                hw_one
    have hnz_sum_le :
        pref_U * (∑ x ∈ cell_J,
          ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
            ∑ z ∈ B_nz,
              ‖inputConjugateRow p χ_p Finset.univ Ψ₀
                (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2) ≤
        C_hit * C_nz_part * E_target := by
      have hexp_nz : (kappa_val + (9 / 2 : ℝ) * η) + (t_q + η) + D_dual.t / 4 +
          (r_new - B_c - t_q) + (1 - 3 * ell_in - 5 * u_act + pad_T + (15 / 2 : ℝ) * D_dual.t) ≤
          F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t := by
        rw [hkappa_eq]; dsimp only [M_new, r_new]
        linarith only [hδc_0, hη_pos, hτ_pos, ht_pos]
      calc _ ≤ U ^ (kappa_val + (9 / 2 : ℝ) * η) *
                (C_hit * (49 * U ^ (t_q + η)) *
                  ((C_div ^ 2 * (2 : ℝ) ^ (2 * ε_div) * U ^ (D_dual.t / 4)) * K_W_val)) := by
              rw [← hpref_eq]; exact mul_le_mul_of_nonneg_left hnz_raw hpref_pos.le
        _ = C_hit * C_nz_part *
              U ^ ((kappa_val + (9 / 2 : ℝ) * η) + (t_q + η) + D_dual.t / 4 +
                (r_new - B_c - t_q) + (1 - 3 * ell_in - 5 * u_act + pad_T + (15 / 2 : ℝ) * D_dual.t)) *
              (tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2) := by
              dsimp only [K_W_val, C_nz_part]
              rw [hX_col_eq, Real.rpow_add hU_pos, Real.rpow_add hU_pos,
                Real.rpow_add hU_pos, Real.rpow_add hU_pos]
              ring
        _ ≤ C_hit * C_nz_part * E_target := by
              dsimp only [E_target]; rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_le hU1.le hexp_nz)
                  (mul_nonneg hChit_pos.le hCnz_pos.le))
                hw_pos.le
    have hcb_pos := coefficientBound_pos
    calc pref_U * _
        ≤ pref_U * (coefficientBound * ∑ x ∈ cell_J,
            ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
              (‖inputConjugateRow p χ_p Finset.univ Ψ₀
                  (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                  (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2 +
                ∑ z ∈ B_nz,
                  ‖inputConjugateRow p χ_p Finset.univ Ψ₀
                    (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                    (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                    (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hre_le hpref_pos.le
      _ = coefficientBound * (pref_U * ∑ x ∈ cell_J,
            ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
              ‖inputConjugateRow p χ_p Finset.univ Ψ₀
                (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col) 0‖ ^ 2 +
          pref_U * ∑ x ∈ cell_J,
            ‖primeMark J lists_v a (x.firstCommon ∪ x.quotientSupport)‖ ^ 2 *
              ∑ z ∈ B_nz,
                ‖inputConjugateRow p χ_p Finset.univ Ψ₀
                  (m * ∏ i ∈ x.quotientSupport, p i) 1 1
                  (markedRadial p (S_rem \ J) lists_v a ∅ V_win X_col)
                  (gcdElement p x.firstCommon x.firstDivisor * z)‖ ^ 2) := by
          simp_rw [mul_add, Finset.sum_add_distrib, mul_add]; ring
      _ ≤ coefficientBound * (C_hit * C_z0_part * E_target + C_hit * C_nz_part * E_target) :=
          mul_le_mul_of_nonneg_left (add_le_add hz0_sum_le hnz_sum_le) hcb_pos.le
      _ = coefficientBound * C_hit * (C_z0_part + C_nz_part) * E_target := by ring
  have hcb_pos := coefficientBound_pos
  let B_slice : ℝ := coefficientBound * C_hit * (C_z0_part + C_nz_part) * E_target
  have hB_slice_nn : 0 ≤ B_slice :=
    mul_nonneg (mul_nonneg (mul_nonneg hcb_pos.le hChit_pos.le)
      (add_nonneg hCz0_pos.le hCnz_pos.le)) hE_target_pos.le
  let S_inner : ℝ := ∑ ray : RayCharacter × RayCharacter, ∑ core : FirstCoreIndex,
    ∑ J ∈ S_rem.powerset,
      (∑ x ∈ cell,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x => (‖commonSelector p (fun _ => 1) k.2.1 x.quotientSupport‖ : ℂ)) x *
        (‖primeMark J lists_v a (wholeExtractedSupport (fun x => extra_b x.cube) negative x)‖ ^ 2 : ℝ) *
        parentPoisson p hp hg hinj Finset.univ negative Ψ m S_rem J
          (fun i => lists_v i \ extra_b x.cube) a omega_b X_col t_ht Y_cell ray core (parent p x)).re
  change pref_U * (firstCoreMassBound * (2 : ℝ) ^ S_rem.card * S_inner) ≤ _
  have h2S_le : (2 : ℝ) ^ S_rem.card ≤ (2 : ℝ) ^ D.N := pow_le_pow_right₀ one_le_two hSrem_card
  have hpow_card : (S_rem.powerset.card : ℝ) ≤ (2 : ℝ) ^ D.N := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]; exact h2S_le
  have hmc_le : firstCoreMassBound ≤ firstCoreMassBound + 1 := by linarith only []
  have hsum_rcJ : pref_U * S_inner ≤ N_ray_core * B_slice := by
    dsimp only [S_inner]; rw [Finset.mul_sum]
    calc _ ≤ ∑ _ray : RayCharacter × RayCharacter,
              ((Fintype.card FirstCoreIndex : ℝ) * (2 : ℝ) ^ D.N * B_slice) := by
            apply Finset.sum_le_sum; intro ray _; rw [Finset.mul_sum]
            calc _ ≤ ∑ _core : FirstCoreIndex, ((2 : ℝ) ^ D.N * B_slice) := by
                    apply Finset.sum_le_sum; intro core _; rw [Finset.mul_sum]
                    calc _ ≤ ∑ _J ∈ S_rem.powerset, B_slice :=
                            Finset.sum_le_sum (hslice_bound ray core)
                      _ = (S_rem.powerset.card : ℝ) * B_slice := by
                          rw [Finset.sum_const, nsmul_eq_mul]
                      _ ≤ _ := mul_le_mul_of_nonneg_right hpow_card hB_slice_nn
              _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [N_ray_core]; ring
  calc pref_U * (firstCoreMassBound * (2 : ℝ) ^ S_rem.card * S_inner)
      = firstCoreMassBound * (2 : ℝ) ^ S_rem.card * (pref_U * S_inner) := by ring
    _ ≤ (firstCoreMassBound + 1) * (2 : ℝ) ^ D.N * (N_ray_core * B_slice) := by
        have h1 : firstCoreMassBound * (2 : ℝ) ^ S_rem.card ≤
            (firstCoreMassBound + 1) * (2 : ℝ) ^ D.N :=
          mul_le_mul hmc_le h2S_le (pow_nonneg zero_le_two _)
            (add_nonneg firstCoreMassBound_nonneg zero_le_one)
        by_cases hneg_s : pref_U * S_inner ≤ 0
        · exact (mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg firstCoreMassBound_nonneg (pow_nonneg zero_le_two _)) hneg_s).trans
            (mul_nonneg (mul_nonneg (add_nonneg firstCoreMassBound_nonneg zero_le_one) (pow_nonneg zero_le_two _))
              (mul_nonneg hNrc_nn hB_slice_nn))
        · exact mul_le_mul h1 hsum_rcJ (le_of_not_ge hneg_s)
            (mul_nonneg (add_nonneg firstCoreMassBound_nonneg zero_le_one) (pow_nonneg zero_le_two _))
    _ = C_outer * (C_z0_part + C_nz_part) * E_target := by dsimp only [C_outer, B_slice]; ring
    _ ≤ C_cell * U ^ (F_p + 45 * η + 3 * τ + pad_T + 8 * D_dual.t) *
          (tripleHeight (firstDegree deg_cell) z_ht.1 * coordinateHeight (firstDegree deg_cell) z_ht.2) := by
        dsimp only [C_cell, E_target]; rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only []) (Real.rpow_nonneg hU_pos.le _))
          hw_pos.le

end DualQZeroCellEnergy

end Stage1CoreColumnEnergy

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
