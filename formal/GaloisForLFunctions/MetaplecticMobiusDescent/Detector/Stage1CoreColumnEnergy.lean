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
open InversePrincipalEnergy UniqueFactorizationMonoid
open InverseInitialArithmetic RayFourExpansion
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialDetectorSource
open InverseInitialPhysicalSlots InverseInitialRawDictionary
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawConjugateGates InverseInitialExcludedPeriod
open InverseInitialConjugateEnergy CanonicalCoefficientClass
open ProbeFinalAssembly ProbeHighRowFamily
open GaloisForLFunctions.FamilyContinuationTheory.Budget
open Stage1CubeBins Stage1DualRowMoments Stage1ReciprocityAndUnpuncture
open Stage1DualSixthFreeEnergy Stage1ParentPoissonEnergy
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstSecondHeightCost
open CompletedHeight JointLogSeparation IdealDivisorBound

local notation "O" => Eisenstein.O

/-! ### Part I: Greedy slot-sum peeling and bounded-puncture `slotCharSum` expansion -/

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
      let base := elementCharacter
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
    unfold elementCharacter InverseInitialConjugateEnergy.conjugateIdealCharacter
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
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff (hlists_sub j hj)]
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
  have hmesh_le : ∀ j ∈ T', w_slot j ≤ D.t / 100 := by
    intro j _
    dsimp only [w_slot]
    have hell_hi := (D.slots_bounds j).2.2
    rw [div_le_iff₀ hd_pos]
    linarith only [hell_hi, hd_lo, D.t_pos]
  have hT''_bound : ∀ T'' ∈ T'.powerset,
      (∑ u ∈ S_free, (X' * ∏ j ∈ T'', Z_slot j)⁻¹ *
        ‖inputConjugateRow (poolPrimary F_pool) χ_pool Finset.univ base 1 1 1
            (fun U_set => childLogTest wFresh s (primeProductNorm (poolPrimary F_pool) U_set / X')) u.val *
          ∏ j ∈ T'', M_slot u j‖ ^ 2) ≤
      (9604 : ℝ) ^ D.N * C_sf *
        U ^ (1 - 3 * ell - 5 * u_sel - x6 + pad_T + 7 * D_dual.t) * (1 + |s|) ^ (2 * J_sf) := by
    intro T'' hT''_mem
    have hT''_sub : T'' ⊆ T' := Finset.mem_powerset.mp hT''_mem
    -- Rewrite each `u ∈ S_free` summand via `dual_factored_product_eq_dyadic` on `T''`.
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
    -- Peel `T_keep ⊆ T''` with `∑ j ∈ T_keep, w_slot j ≤ z_T_cap` and `∑ j ∈ T'' \ T_keep, w_slot j ≤ pad_T + D.t / 100`.
    have hT''_sum : (∑ j ∈ T'', w_slot j) ≤ z_T_cap + pad_T :=
      (Finset.sum_le_sum_of_subset_of_nonneg hT''_sub (fun j hj _ => hw0 j hj)).trans hzT_sum
    obtain ⟨T_keep, hTk_sub, hTk_sum, hTk_sdiff⟩ :=
      exists_subset_sum_le_and_sdiff_le T'' w_slot (by have := D.t_pos; positivity)
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
        ((9604 : ℝ) ^ D.N * U ^ (pad_T + D.t / 100)) *
          ‖HeckeDyadic.polynomial (targetRow (deletedBase data).inverse u) true
              (childLogTest wFresh s) X' 0 0 *
            ∏ j ∈ T_keep, HeckePrimeRow.canonicalPrimeAmplitude F_dual.modulus ⊤ u.val
              F_dual.W 2 (Z_slot j) ζ_tw‖ ^ 2 := by
      intro u _
      have hunion : T_keep ∪ (T'' \ T_keep) = T'' := Finset.union_sdiff_of_subset hTk_sub
      have hdisj : Disjoint T_keep (T'' \ T_keep) := Finset.disjoint_sdiff
      conv_lhs => rw [← hunion, Finset.prod_union hdisj, ← mul_assoc]
      rw [norm_mul, mul_pow]
      rw [mul_comm ((9604 : ℝ) ^ D.N * U ^ (pad_T + D.t / 100))]
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
        _ ≤ (9604 : ℝ) ^ D.N * U ^ (pad_T + D.t / 100) := by
            apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard_sd) _
              (Finset.prod_nonneg (fun j _ => (hZ_pos j).le)) (by positivity)
            dsimp only [Z_slot]
            rw [← Real.rpow_sum_of_pos hU_pos]
            exact Real.rpow_le_rpow_of_exponent_le hU1.le hTk_sdiff
    have hsf_keep := hsf U hU hd_lo hd_hi hr0 hr1 hθ0 hθ1 hell0 hell1 hJv0 hJv hx6 hV0 hzJ0 hzc0
      hHf_lo hX' hX'_le T_keep hTk_sum S_free hS_norm ζ_tw hζ_tw_re hζ_tw_im s
    -- Note `D.t / 100 ≤ D_dual.t`? Wait: check `D.t` vs `D_dual.t`!
    -- Wait: add hypothesis `hDt_le : D.t ≤ D_dual.t` (in fact `D_dual.t = D.t`!) so `D.t / 100 ≤ D_dual.t`!
    sorry
  sorry

