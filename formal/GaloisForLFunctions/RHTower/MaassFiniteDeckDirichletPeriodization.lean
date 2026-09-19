import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletCentral
import GaloisForLFunctions.HTGeometry.ModularDirichletFormSmoothApprox
import GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost

/-!
# Central-compatible vector periodization for finite-deck Maass forms

A finite-deck equivariant field must be fixed by the central deck action because
`-I` fixes every point of the upper half-plane.  This file constructs its exact
periodization from compactly supported, central-fixed vector seeds in the open
modular fundamental domain.  It proves the periodization is `C¹`, deck
equivariant, and belongs to the finite-deck Dirichlet pre-domain; consequently
the seed's central-fixed L² class lies in the range of the closed form
inclusion.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff Classical
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

def seedCentralFixed (N : ℕ) (ψ : ℍ → DeckSpace N) : Prop :=
  ∀ z : ℍ, finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z) = ψ z

def deckPeriodize (N : ℕ) (ψ : ℍ → DeckSpace N) (z : ℍ) : DeckSpace N :=
  if h : ∃ γ : SL2Z, γ • z ∈ fdo then
    finiteRegularUnitary (QuotientGroup.mk h.choose⁻¹ : Deck N) (ψ (h.choose • z))
  else 0

/-- Assemble scalar chart coordinates into the finite-deck Euclidean coefficient space. -/
def vectorOfCoordinates {N : ℕ} (P : Deck N → ℂ → ℂ) (w : ℂ) : DeckSpace N :=
  WithLp.toLp 2 fun q => P q w

@[simp] theorem vectorOfCoordinates_apply {N : ℕ} (P : Deck N → ℂ → ℂ) (w : ℂ) (q : Deck N) :
    vectorOfCoordinates P w q = P q w := rfl

theorem contDiff_vectorOfCoordinates {N : ℕ} {P : Deck N → ℂ → ℂ}
    (hP : ∀ q, ContDiff ℝ 1 (P q)) : ContDiff ℝ 1 (vectorOfCoordinates P) := by
  change ContDiff ℝ 1 (fun w => WithLp.toLp 2 fun q => P q w)
  exact contDiff_piLp' 2 hP

/-- Smooth approximation on a compact chart set, simultaneously in every finite-deck coordinate. -/
theorem exists_contDiff_uniform_approx_vector {N : ℕ} {s : Set ℂ} (hs : IsCompact s)
    {G : ℂ → DeckSpace N} (hG : ContinuousOn G s) {η : ℝ} (hη : 0 < η) :
    ∃ P : ℂ → DeckSpace N, ContDiff ℝ 1 P ∧ ∀ x ∈ s, ‖G x - P x‖ < η := by
  let c : ℝ := Fintype.card (Deck N)
  let δ : ℝ := η / (c + 1)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hc1 : 0 < c + 1 := by linarith
  have hδ : 0 < δ := div_pos hη hc1
  have hcoord : ∀ q : Deck N, ContinuousOn (fun w => G w q) s := by
    intro q
    exact (EuclideanSpace.proj q).continuous.continuousOn.comp hG fun _ _ => mem_univ _
  choose P hP hPerr using fun q => exists_contDiff_uniform_approx hs (hcoord q) hδ
  refine ⟨vectorOfCoordinates P, contDiff_vectorOfCoordinates hP, ?_⟩
  intro x hx
  have hsq : ∀ q : Deck N, ‖G x q - P q x‖ ^ 2 < δ ^ 2 := by
    intro q
    have hnonneg : 0 ≤ ‖G x q - P q x‖ := norm_nonneg _
    nlinarith [hPerr q x hx]
  have hsum : ∑ q : Deck N, ‖G x q - P q x‖ ^ 2 < η ^ 2 := by
    calc
      ∑ q : Deck N, ‖G x q - P q x‖ ^ 2 < ∑ _q : Deck N, δ ^ 2 :=
        Finset.sum_lt_sum (fun q _ => (hsq q).le) ⟨1, Finset.mem_univ _, hsq 1⟩
      _ = c * δ ^ 2 := by simp [c]
      _ < η ^ 2 := by
        have hcSq : c < (c + 1) ^ 2 := by nlinarith
        have hcDiv : c / (c + 1) ^ 2 < 1 := (div_lt_one₀ (sq_pos_of_pos hc1)).mpr hcSq
        have hηSq : 0 < η ^ 2 := sq_pos_of_pos hη
        calc
          c * δ ^ 2 = (c / (c + 1) ^ 2) * η ^ 2 := by
            dsimp [δ]
            field_simp
          _ < 1 * η ^ 2 := (mul_lt_mul_of_pos_right hcDiv hηSq)
          _ = η ^ 2 := one_mul _
  have hnormsq : ‖G x - vectorOfCoordinates P x‖ ^ 2 =
      ∑ q : Deck N, ‖G x q - P q x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro q _
    rfl
  nlinarith [norm_nonneg (G x - vectorOfCoordinates P x), sq_nonneg η]

/-- Pointwise orthogonal averaging onto the central deck-fixed coefficient sector. -/
def centralizeSeed (N : ℕ) (ψ : ℍ → DeckSpace N) (z : ℍ) : DeckSpace N :=
  (2 : ℂ)⁻¹ • (ψ z + finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z))

private theorem deckCentral_square (N : ℕ) :
    (QuotientGroup.mk (-1 : SL2Z) : Deck N) * QuotientGroup.mk (-1 : SL2Z) = 1 := by
  rw [← QuotientGroup.mk_mul (CongruenceSubgroup.Gamma (N + 1))]
  simp

private theorem finiteRegular_deckCentral_square (N : ℕ) (v : DeckSpace N) :
    finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
      (finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) v) = v := by
  rw [← LinearIsometryEquiv.trans_apply, ← finiteRegularUnitary_mul, deckCentral_square]
  ext q
  simp [finiteRegularUnitary_apply]

theorem seedCentralFixed_centralizeSeed (N : ℕ) (ψ : ℍ → DeckSpace N) :
    seedCentralFixed N (centralizeSeed N ψ) := by
  intro z
  unfold centralizeSeed
  calc
    finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
        ((2 : ℂ)⁻¹ • (ψ z + finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
          (ψ z))) = (2 : ℂ)⁻¹ • (finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
            (ψ z) + finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
              (finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z))) := by
        simp only [map_smul, map_add]
    _ = (2 : ℂ)⁻¹ • (finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z) + ψ z) := by
      rw [finiteRegular_deckCentral_square]
    _ = (2 : ℂ)⁻¹ • (ψ z + finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z)) := by
      congr 1
      exact add_comm _ _

theorem isChartC1_add_vec {N : ℕ} {F G : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (hG : IsChartC1 G) : IsChartC1 (F + G) := by
  unfold IsChartC1
  change ContDiffOn ℝ 1 (chartFun F + chartFun G) upperSet
  exact hF.add hG

theorem isChartC1_smul_vec {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) (c : ℂ) : IsChartC1 (c • F) := by
  unfold IsChartC1
  change ContDiffOn ℝ 1 (c • chartFun F) upperSet
  exact ContDiffOn.const_smul c hF

theorem isChartC1_centralizeSeed {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) : IsChartC1 (centralizeSeed N ψ) := by
  change IsChartC1 ((2 : ℂ)⁻¹ • (ψ + fun z =>
    finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (ψ z)))
  apply isChartC1_smul_vec
  apply isChartC1_add_vec hψ
  let L : DeckSpace N →L[ℝ] DeckSpace N :=
    ((finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  unfold IsChartC1
  change ContDiffOn ℝ 1 (L ∘ chartFun ψ) upperSet
  exact L.contDiff.comp_contDiffOn hψ

theorem hasCompactSupport_centralizeSeed {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hs : HasCompactSupport ψ) : HasCompactSupport (centralizeSeed N ψ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun z hz => by_contra fun h => hz (by
      unfold centralizeSeed
      rw [image_eq_zero_of_notMem_tsupport h, map_zero]
      simp))
    (isClosed_tsupport ψ))

theorem tsupport_centralizeSeed_subset {N : ℕ} (ψ : ℍ → DeckSpace N) :
    tsupport (centralizeSeed N ψ) ⊆ tsupport ψ :=
  closure_minimal (fun z hz => by_contra fun h => hz (by
    unfold centralizeSeed
    rw [image_eq_zero_of_notMem_tsupport h, map_zero]
    simp)) (isClosed_tsupport ψ)

/-- Central averaging on the finite-deck L² carrier. -/
def centralizeL2 (N : ℕ) : DeckL2 N →L[ℂ] DeckL2 N :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ (DeckL2 N) + deckCentralL2 N)

theorem centralizeL2_fixed {N : ℕ} (v : deckCentralFixedL2 N) :
    centralizeL2 N v = v := by
  have hv : deckCentralL2 N (v : DeckL2 N) = v := by
    have hv0 := v.property
    change deckCentralL2 N (v : DeckL2 N) - v = 0 at hv0
    exact sub_eq_zero.mp hv0
  unfold centralizeL2
  change (2 : ℂ)⁻¹ • ((v : DeckL2 N) + deckCentralL2 N v) = v
  rw [hv]
  module

theorem centralizeSeedMemLp {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : MemLp ψ 2 cellMeasure) : MemLp (centralizeSeed N ψ) 2 cellMeasure := by
  have hR : MemLp (fun z => finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
      (ψ z)) 2 cellMeasure := by
    simpa [deckCentralCoeff] using hψ.continuousLinearMap_comp (deckCentralCoeff N)
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).mpr
    ((hψ.add hR).const_smul ((2 : ℂ)⁻¹))
  unfold centralizeSeed
  simp only [Pi.smul_apply, Pi.add_apply]

theorem deckCentralL2_toDeckL2 {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : MemLp ψ 2 cellMeasure) :
    deckCentralL2 N (toDeckL2 ψ hψ) =
      toDeckL2 (fun z => deckCentralCoeff N (ψ z))
        (hψ.continuousLinearMap_comp (deckCentralCoeff N)) := by
  apply Lp.ext
  filter_upwards [
    (deckCentralCoeff N).coeFn_compLpL (toDeckL2 ψ hψ),
    MemLp.coeFn_toLp hψ,
    MemLp.coeFn_toLp (hψ.continuousLinearMap_comp (deckCentralCoeff N))] with z hcoeff hψlp hRlp
  change (((deckCentralCoeff N).compLpL 2 cellMeasure) (toDeckL2 ψ hψ)) z = _
  rw [hcoeff]
  change (deckCentralCoeff N) ((MemLp.toLp ψ hψ) z) =
    (MemLp.toLp (fun z => deckCentralCoeff N (ψ z)) _) z
  rw [hψlp, hRlp]

theorem centralizeL2_toDeckL2 {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : MemLp ψ 2 cellMeasure) :
    centralizeL2 N (toDeckL2 ψ hψ) =
      toDeckL2 (centralizeSeed N ψ) (centralizeSeedMemLp hψ) := by
  unfold centralizeL2
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    deckCentralL2_toDeckL2]
  rw [← toDeckL2_add hψ (hψ.continuousLinearMap_comp (deckCentralCoeff N))]
  rw [← toDeckL2_smul]
  apply toDeckL2_congr _ _
  apply Filter.EventuallyEq.of_eq
  funext z
  unfold centralizeSeed
  rfl

theorem norm_deckCentralL2_le (N : ℕ) (v : DeckL2 N) :
    ‖deckCentralL2 N v‖ ≤ ‖v‖ := by
  change ‖((deckCentralCoeff N).compLpL 2 cellMeasure) v‖ ≤ ‖v‖
  calc
    ‖((deckCentralCoeff N).compLpL 2 cellMeasure) v‖ ≤ ‖deckCentralCoeff N‖ * ‖v‖ :=
      (deckCentralCoeff N).norm_compLp_le v
    _ = ‖v‖ := by simp [deckCentralCoeff]

theorem norm_centralizeL2_le (N : ℕ) (v : DeckL2 N) :
    ‖centralizeL2 N v‖ ≤ ‖v‖ := by
  classical
  by_cases hnontriv : Nontrivial (DeckL2 N)
  · letI := hnontriv
    have hRop : ‖deckCentralL2 N‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound (f := deckCentralL2 N) (by norm_num)
      intro w
      simpa using norm_deckCentralL2_le N w
    have hPop : ‖centralizeL2 N‖ ≤ 1 := by
      unfold centralizeL2
      calc
        ‖(2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ (DeckL2 N) + deckCentralL2 N)‖ ≤
            ‖(2 : ℂ)⁻¹‖ * ‖ContinuousLinearMap.id ℂ (DeckL2 N) + deckCentralL2 N‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖ContinuousLinearMap.id ℂ (DeckL2 N)‖ + ‖deckCentralL2 N‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_add_le _ _) (norm_nonneg _)
        _ ≤ 1 := by
          rw [show ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ by norm_num,
            ContinuousLinearMap.norm_id]
          nlinarith
    calc
      ‖centralizeL2 N v‖ ≤ ‖centralizeL2 N‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hPop (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  · haveI : Subsingleton (DeckL2 N) := not_nontrivial_iff_subsingleton.mp hnontriv
    have hv : centralizeL2 N v = v := Subsingleton.elim _ _
    rw [hv]

theorem norm_sub_centralizeL2_le {N : ℕ} (v : DeckL2 N) (w : deckCentralFixedL2 N) :
    ‖centralizeL2 N v - w‖ ≤ ‖v - w‖ := by
  calc
    ‖centralizeL2 N v - w‖ = ‖centralizeL2 N v - centralizeL2 N w‖ := by
      rw [centralizeL2_fixed w]
    _ = ‖centralizeL2 N (v - w)‖ := by rw [map_sub]
    _ ≤ ‖v - w‖ := norm_centralizeL2_le N _

private theorem choose_eq_of_mul_inv_eq_one {a γ : SL2Z} (h : a * γ⁻¹ = 1) : a = γ := by
  calc
    a = (a * γ⁻¹) * γ := by group
    _ = γ := by rw [h, one_mul]

private theorem choose_eq_neg_of_mul_inv_eq_neg_one {a γ : SL2Z}
    (h : a * γ⁻¹ = -1) : a = -γ := by
  calc
    a = (a * γ⁻¹) * γ := by group
    _ = (-1 : SL2Z) * γ := by rw [h]
    _ = -γ := by rw [neg_one_mul]

private theorem neg_inv_eq (γ : SL2Z) : (-γ)⁻¹ = γ⁻¹ * (-1 : SL2Z) := by
  rw [inv_neg, mul_neg, mul_one]

theorem deckPeriodize_eq_of_mem (N : ℕ) (ψ : ℍ → DeckSpace N)
    (hψ : seedCentralFixed N ψ) {z : ℍ} {γ : SL2Z} (hγ : γ • z ∈ fdo) :
    deckPeriodize N ψ z =
      finiteRegularUnitary (QuotientGroup.mk γ⁻¹ : Deck N) (ψ (γ • z)) := by
  unfold deckPeriodize
  have hz : ∃ δ : SL2Z, δ • z ∈ fdo := ⟨γ, hγ⟩
  rw [dif_pos hz]
  let a : SL2Z := (Exists.choose hz)
  have ha : a • z ∈ fdo := Exists.choose_spec hz
  change finiteRegularUnitary (QuotientGroup.mk a⁻¹ : Deck N) (ψ (a • z)) = _
  have htransport : (a * γ⁻¹) • (γ • z) ∈ fdo := by
    rw [smul_smul, inv_mul_cancel_right]
    exact ha
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hγ htransport with h | h
  · have haeq : a = γ := choose_eq_of_mul_inv_eq_one h
    simp [haeq]
  · have haeq : a = -γ := choose_eq_neg_of_mul_inv_eq_neg_one h
    rw [haeq, neg_inv_eq]
    rw [SL_neg_smul]
    ext q
    simp only [finiteRegularUnitary_apply]
    have hc := congrArg (fun v : DeckSpace N => v (q * QuotientGroup.mk γ⁻¹)) (hψ (γ • z))
    change ψ (γ • z) ((q * QuotientGroup.mk γ⁻¹) * QuotientGroup.mk (-1 : SL2Z)) =
      ψ (γ • z) (q * QuotientGroup.mk γ⁻¹) at hc
    have hmk : (QuotientGroup.mk (γ⁻¹ * (-1 : SL2Z)) : Deck N) =
        QuotientGroup.mk γ⁻¹ * QuotientGroup.mk (-1 : SL2Z) := by
      exact QuotientGroup.mk_mul (CongruenceSubgroup.Gamma (N + 1)) _ _
    rw [hmk]
    simpa only [mul_assoc] using hc

theorem deckPeriodize_equivariant (N : ℕ) (ψ : ℍ → DeckSpace N)
    (hψ : seedCentralFixed N ψ) (δ : SL2Z) (z : ℍ) :
    deckPeriodize N ψ (δ • z) =
      finiteRegularUnitary (QuotientGroup.mk δ : Deck N) (deckPeriodize N ψ z) := by
  by_cases hz : ∃ γ : SL2Z, γ • z ∈ fdo
  · obtain ⟨γ, hγ⟩ := hz
    have hδ : (γ * δ⁻¹) • (δ • z) ∈ fdo := by
      rw [smul_smul, inv_mul_cancel_right]
      exact hγ
    rw [deckPeriodize_eq_of_mem N ψ hψ hδ,
      deckPeriodize_eq_of_mem N ψ hψ hγ]
    have hinv : (γ * δ⁻¹)⁻¹ = δ * γ⁻¹ := by group
    rw [hinv, QuotientGroup.mk_mul (CongruenceSubgroup.Gamma (N + 1))]
    rw [finiteRegularUnitary_mul]
    have hmove : (γ * δ⁻¹) • (δ • z) = γ • z := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [hmove]
    rfl
  · have hδ : ¬ ∃ γ : SL2Z, γ • (δ • z) ∈ fdo := by
      rintro ⟨γ, hγ⟩
      apply hz
      refine ⟨γ * δ, ?_⟩
      rw [mul_smul]
      exact hγ
    unfold deckPeriodize
    rw [dif_neg hz, dif_neg hδ, map_zero]

theorem deckPeriodize_eq_zero_of_forall (N : ℕ) (ψ : ℍ → DeckSpace N) {z : ℍ}
    (h : ∀ γ : SL2Z, γ • z ∉ tsupport ψ) : deckPeriodize N ψ z = 0 := by
  unfold deckPeriodize
  split_ifs with hz
  · rw [image_eq_zero_of_notMem_tsupport (h hz.choose), map_zero]
  · rfl

theorem isChartC1_comp_smul_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) (γ : SL2Z) : IsChartC1 (fun z => ψ (γ • z)) := by
  unfold IsChartC1
  have hcomp : ContDiffOn ℝ 1 (chartFun ψ ∘ moebiusChart γ) upperSet :=
    hψ.comp (contDiffOn_moebiusChart γ) (fun w hw => moebiusChart_mem_upperSet γ hw)
  refine hcomp.congr fun w hw => ?_
  show ψ (γ • ofComplex w) = ψ (ofComplex (moebiusChart γ w))
  rw [ofComplex_apply_of_im_pos hw]
  have h := moebiusChart_coe γ ⟨w, hw⟩
  rw [show moebiusChart γ w = ((γ • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) from h, ofComplex_apply]

theorem isChartC1_regular_apply {N : ℕ} (g : Deck N) {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) : IsChartC1 (fun z => finiteRegularUnitary g (ψ z)) := by
  let L : DeckSpace N →L[ℝ] DeckSpace N :=
    ((finiteRegularUnitary g).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  change ContDiffOn ℝ 1 (L ∘ chartFun ψ) upperSet
  exact L.contDiff.comp_contDiffOn hψ

theorem continuous_of_isChartC1 {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) : Continuous ψ := by
  have h : ψ = chartFun ψ ∘ UpperHalfPlane.coe := by
    funext z
    simp [chartFun, ofComplex_apply]
  rw [h]
  exact ((ContDiffOn.continuousOn hψ).comp_continuous continuous_coe fun z => z.im_pos)

theorem continuous_hypGradX_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) : Continuous (hypGradX ψ) := by
  have hd := ContDiffOn.continuousOn_fderiv_of_isOpen hψ isOpen_upperSet le_rfl
  have hd1 : ContinuousOn (fun w => fderiv ℝ (chartFun ψ) w 1) upperSet :=
    hd.clm_apply continuousOn_const
  have h1 : Continuous fun z : ℍ => fderiv ℝ (chartFun ψ) (z : ℂ) 1 :=
    hd1.comp_continuous continuous_coe fun z => z.im_pos
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul h1

theorem continuous_hypGradY_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) : Continuous (hypGradY ψ) := by
  have hd := ContDiffOn.continuousOn_fderiv_of_isOpen hψ isOpen_upperSet le_rfl
  have hdI : ContinuousOn (fun w => fderiv ℝ (chartFun ψ) w Complex.I) upperSet :=
    hd.clm_apply continuousOn_const
  have h1 : Continuous fun z : ℍ => fderiv ℝ (chartFun ψ) (z : ℂ) Complex.I :=
    hdI.comp_continuous continuous_coe fun z => z.im_pos
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul h1

theorem chartDeriv_congr_of_eqOn_vec {N : ℕ} {u₁ u₂ : ℍ → DeckSpace N} {O : Set ℍ}
    (hO : IsOpen O) (h : EqOn u₁ u₂ O) (v : ℂ) {z : ℍ} (hz : z ∈ O) :
    chartDeriv u₁ v z = chartDeriv u₂ v z := by
  unfold chartDeriv
  have hev : chartFun u₁ =ᶠ[nhds (z : ℂ)] chartFun u₂ := by
    have hmem : UpperHalfPlane.coe '' O ∈ nhds (z : ℂ) :=
      (isOpenEmbedding_coe.isOpenMap _ hO).mem_nhds ⟨z, hz, rfl⟩
    filter_upwards [hmem] with w hw
    obtain ⟨z', hz', rfl⟩ := hw
    show u₁ (ofComplex (z' : ℂ)) = u₂ (ofComplex (z' : ℂ))
    rw [ofComplex_apply]
    exact h hz'
  rw [hev.fderiv_eq]

theorem hypGradX_congr_of_eqOn_vec {N : ℕ} {u₁ u₂ : ℍ → DeckSpace N} {O : Set ℍ}
    (hO : IsOpen O) (h : EqOn u₁ u₂ O) {z : ℍ} (hz : z ∈ O) :
    hypGradX u₁ z = hypGradX u₂ z := by
  unfold hypGradX
  rw [chartDeriv_congr_of_eqOn_vec hO h 1 hz]

theorem hypGradY_congr_of_eqOn_vec {N : ℕ} {u₁ u₂ : ℍ → DeckSpace N} {O : Set ℍ}
    (hO : IsOpen O) (h : EqOn u₁ u₂ O) {z : ℍ} (hz : z ∈ O) :
    hypGradY u₁ z = hypGradY u₂ z := by
  unfold hypGradY
  rw [chartDeriv_congr_of_eqOn_vec hO h Complex.I hz]

theorem hypGradX_zero (N : ℕ) (z : ℍ) :
    hypGradX (fun _ : ℍ => (0 : DeckSpace N)) z = 0 := by
  unfold hypGradX chartDeriv chartFun
  change (z.im : ℂ) • fderiv ℝ (fun _ : ℂ => (0 : DeckSpace N)) (z : ℂ) 1 = 0
  rw [fderiv_const_apply]
  simp

theorem hypGradY_zero (N : ℕ) (z : ℍ) :
    hypGradY (fun _ : ℍ => (0 : DeckSpace N)) z = 0 := by
  unfold hypGradY chartDeriv chartFun
  change (z.im : ℂ) • fderiv ℝ (fun _ : ℂ => (0 : DeckSpace N)) (z : ℂ) Complex.I = 0
  rw [fderiv_const_apply]
  simp

theorem hypGradX_eq_zero_of_notMem_tsupport_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    {z : ℍ} (hz : z ∉ tsupport ψ) : hypGradX ψ z = 0 := by
  have h := hypGradX_congr_of_eqOn_vec (u₂ := fun _ => 0) (isClosed_tsupport ψ).isOpen_compl
    (fun z' hz' => image_eq_zero_of_notMem_tsupport hz') hz
  rw [h, hypGradX_zero]

theorem hypGradY_eq_zero_of_notMem_tsupport_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    {z : ℍ} (hz : z ∉ tsupport ψ) : hypGradY ψ z = 0 := by
  have h := hypGradY_congr_of_eqOn_vec (u₂ := fun _ => 0) (isClosed_tsupport ψ).isOpen_compl
    (fun z' hz' => image_eq_zero_of_notMem_tsupport hz') hz
  rw [h, hypGradY_zero]

theorem hasCompactSupport_hypGradX_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hs : HasCompactSupport ψ) : HasCompactSupport (hypGradX ψ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun _ hz => by_contra fun h => hz (hypGradX_eq_zero_of_notMem_tsupport_vec h))
    (isClosed_tsupport ψ))

theorem hasCompactSupport_hypGradY_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hs : HasCompactSupport ψ) : HasCompactSupport (hypGradY ψ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun _ hz => by_contra fun h => hz (hypGradY_eq_zero_of_notMem_tsupport_vec h))
    (isClosed_tsupport ψ))

theorem isChartC1_deckPeriodize {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ) (hK : tsupport ψ ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) : IsChartC1 (deckPeriodize N ψ) := by
  unfold IsChartC1
  apply contDiffOn_of_locally_contDiffOn
  intro w hw
  set z₀ : ℍ := ⟨w, hw⟩ with hz₀
  by_cases hcase : ∃ γ : SL2Z, γ • z₀ ∈ fdo
  · obtain ⟨γ, hγ⟩ := hcase
    refine ⟨UpperHalfPlane.coe '' ((fun z : ℍ => γ • z) ⁻¹' fdo),
      isOpenEmbedding_coe.isOpenMap _ (isOpen_fdo.preimage (continuous_modular_smul γ)),
      ⟨z₀, hγ, rfl⟩, ?_⟩
    have hc := isChartC1_regular_apply (QuotientGroup.mk γ⁻¹ : Deck N)
      (isChartC1_comp_smul_vec hψ γ)
    refine (ContDiffOn.mono hc inter_subset_left).congr ?_
    rintro w' ⟨_, z, hz, rfl⟩
    show deckPeriodize N ψ (ofComplex (z : ℂ)) =
      finiteRegularUnitary (QuotientGroup.mk γ⁻¹ : Deck N) (ψ (γ • ofComplex (z : ℂ)))
    rw [ofComplex_apply, deckPeriodize_eq_of_mem N ψ hcentral hz]
  · push Not at hcase
    have hKc : IsCompact (tsupport ψ) := hs
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds z₀
    set S := {γ : SL2Z | ((γ • ·) '' L ∩ tsupport ψ).Nonempty} with hS
    have hSf : S.Finite := finite_modular_smul_inter hLc hKc
    set U : Set ℍ := interior L ∩ ⋂ γ ∈ S, (fun z : ℍ => γ • z) ⁻¹' (tsupport ψ)ᶜ with hU
    have hUopen : IsOpen U :=
      isOpen_interior.inter (hSf.isOpen_biInter fun γ _ =>
        (isClosed_tsupport ψ).isOpen_compl.preimage (continuous_modular_smul γ))
    have hz₀U : z₀ ∈ U := by
      refine ⟨mem_interior_iff_mem_nhds.mpr hLn, mem_iInter₂.mpr fun γ _ => ?_⟩
      intro h
      exact hcase γ (hK h)
    have hzero : ∀ z ∈ U, deckPeriodize N ψ z = 0 := by
      intro z hz
      apply deckPeriodize_eq_zero_of_forall
      intro γ hγK
      by_cases hγS : γ ∈ S
      · exact (mem_iInter₂.mp hz.2 γ hγS) hγK
      · exact hγS ⟨γ • z, ⟨z, interior_subset hz.1, rfl⟩, hγK⟩
    refine ⟨UpperHalfPlane.coe '' U, isOpenEmbedding_coe.isOpenMap _ hUopen,
      ⟨z₀, hz₀U, rfl⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : DeckSpace N))).congr ?_
    rintro w' ⟨_, z, hzU, rfl⟩
    show deckPeriodize N ψ (ofComplex (z : ℂ)) = 0
    rw [ofComplex_apply]
    exact hzero z hzU

theorem deckPeriodize_eq_of_mem_fdo (N : ℕ) (ψ : ℍ → DeckSpace N)
    (hψ : seedCentralFixed N ψ) {z : ℍ} (hz : z ∈ fdo) :
    deckPeriodize N ψ z = ψ z := by
  rw [deckPeriodize_eq_of_mem N ψ hψ (γ := 1) (by simpa using hz)]
  ext q
  simp only [finiteRegularUnitary_apply, inv_one, QuotientGroup.mk_one, mul_one, one_smul]

theorem norm_deckPeriodize_le {N : ℕ} {ψ : ℍ → DeckSpace N} {C : ℝ}
    (hC : ∀ z, ‖ψ z‖ ≤ C) (hC0 : 0 ≤ C) (z : ℍ) :
    ‖deckPeriodize N ψ z‖ ≤ C := by
  unfold deckPeriodize
  split_ifs
  · simpa using hC _
  · simpa using hC0

theorem memLp_vec_of_continuous_of_bound {N : ℕ} {u : ℍ → DeckSpace N}
    (hu : Continuous u) {C : ℝ} (hC : ∀ᵐ z ∂cellMeasure, ‖u z‖ ≤ C) :
    MemLp u 2 cellMeasure :=
  MemLp.of_bound hu.aestronglyMeasurable C hC

def deckPeriodizePre (N : ℕ) (ψ : ℍ → DeckSpace N) (hψ : IsChartC1 ψ)
    (hs : HasCompactSupport ψ) (hK : tsupport ψ ⊆ fdo) (hcentral : seedCentralFixed N ψ) :
    formPreDomain N :=
  ⟨deckPeriodize N ψ, isChartC1_deckPeriodize hψ hs hK hcentral,
    deckPeriodize_equivariant N ψ hcentral, by
      obtain ⟨C, hC⟩ := (continuous_of_isChartC1 hψ).bounded_above_of_compact_support hs
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ⟨Complex.I, by simp⟩)
      exact memLp_vec_of_continuous_of_bound
        (continuous_of_isChartC1 (isChartC1_deckPeriodize hψ hs hK hcentral))
        (ae_of_all _ (norm_deckPeriodize_le hC hC0)), by
      obtain ⟨C, hC⟩ := (continuous_hypGradX_vec hψ).bounded_above_of_compact_support
        (hasCompactSupport_hypGradX_vec hs)
      refine memLp_vec_of_continuous_of_bound (C := C)
        (continuous_hypGradX_vec (isChartC1_deckPeriodize hψ hs hK hcentral)) ?_
      filter_upwards [ae_mem_fdo] with z hz
      rw [hypGradX_congr_of_eqOn_vec isOpen_fdo
        (fun z' hz' => deckPeriodize_eq_of_mem_fdo N ψ hcentral hz') hz]
      exact hC z, by
      obtain ⟨C, hC⟩ := (continuous_hypGradY_vec hψ).bounded_above_of_compact_support
        (hasCompactSupport_hypGradY_vec hs)
      refine memLp_vec_of_continuous_of_bound (C := C)
        (continuous_hypGradY_vec (isChartC1_deckPeriodize hψ hs hK hcentral)) ?_
      filter_upwards [ae_mem_fdo] with z hz
      rw [hypGradY_congr_of_eqOn_vec isOpen_fdo
        (fun z' hz' => deckPeriodize_eq_of_mem_fdo N ψ hcentral hz') hz]
      exact hC z⟩

theorem memLp_of_isChartC1_of_hasCompactSupport_vec {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ) : MemLp ψ 2 cellMeasure := by
  obtain ⟨C, hC⟩ := (continuous_of_isChartC1 hψ).bounded_above_of_compact_support hs
  exact memLp_vec_of_continuous_of_bound (continuous_of_isChartC1 hψ) (ae_of_all _ hC)

/-- The L² class of a pointwise central-fixed compact seed in the correct carrier. -/
def seedCentralL2 {N : ℕ} (ψ : ℍ → DeckSpace N) (hψ : IsChartC1 ψ)
    (hs : HasCompactSupport ψ) (hcentral : seedCentralFixed N ψ) : deckCentralFixedL2 N :=
  ⟨toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs), by
    change deckCentralL2 N (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) -
      toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs) = 0
    apply sub_eq_zero.mpr
    apply Lp.ext
    filter_upwards [
      (deckCentralCoeff N).coeFn_compLpL
        (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)),
      MemLp.coeFn_toLp (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)] with z hcoeff hψlp
    change (((deckCentralCoeff N).compLpL 2 cellMeasure)
      (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs))) z =
        (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) z
    rw [hcoeff]
    change finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
      ((MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) z) =
        (MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) z
    rw [hψlp]
    exact hcentral z⟩

theorem toDeckL2_mem_range_formInclusionCentral {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ) (hK : tsupport ψ ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) :
    (seedCentralL2 ψ hψ hs hcentral) ∈
      Set.range (formInclusionCentral N) := by
  refine ⟨toFormDomain N (deckPeriodizePre N ψ hψ hs hK hcentral), ?_⟩
  apply Subtype.ext
  change formInclusion N (toFormDomain N (deckPeriodizePre N ψ hψ hs hK hcentral)) =
    toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)
  rw [formInclusion_toFormDomain]
  show toDeckL2 (deckPeriodize N ψ) (formPreDomain.memLp (deckPeriodizePre N ψ hψ hs hK hcentral)) = _
  exact toDeckL2_congr _ _ (by
    filter_upwards [ae_mem_fdo] with z hz
    exact deckPeriodize_eq_of_mem_fdo N ψ hcentral hz)

theorem centralizeL2_mem_range_formInclusion {N : ℕ} {ψ : ℍ → DeckSpace N}
    (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ) (hK : tsupport ψ ⊆ fdo) :
    centralizeL2 N (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) ∈
      Set.range (formInclusion N) := by
  rw [centralizeL2_toDeckL2]
  obtain ⟨u, hu⟩ := toDeckL2_mem_range_formInclusionCentral
    (isChartC1_centralizeSeed hψ) (hasCompactSupport_centralizeSeed hs)
    (tsupport_centralizeSeed_subset ψ |>.trans hK) (seedCentralFixed_centralizeSeed N ψ)
  refine ⟨u, ?_⟩
  exact congrArg Subtype.val hu

/-- Any compact interior vector approximation to a central target transfers, after central
averaging, to an equally good approximation from the completed finite-deck form. -/
theorem exists_formInclusion_approx_of_interior {N : ℕ} (w : deckCentralFixedL2 N)
    {ψ : ℍ → DeckSpace N} (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ fdo) {ε : ℝ}
    (happrox : ‖toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs) - w‖ < ε) :
    ∃ u : FormDomain N, ‖formInclusion N u - w‖ < ε := by
  obtain ⟨u, hu⟩ := centralizeL2_mem_range_formInclusion hψ hs hK
  refine ⟨u, ?_⟩
  rw [hu]
  exact lt_of_le_of_lt (norm_sub_centralizeL2_le
    (toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)) w) happrox

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
