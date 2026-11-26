import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.RankEnergyExistence
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SubFarkasBudgetCertificates

/-!
# Stage-1 `q0`-stripped Pass-2 children and sextic-invariant tiny cube bins

This module upgrades the Stage-1 descent on `[69/100, 19/26]` where `1 - r₀ - 2 z` can dip to
`-53/12500`:

1. **Inclusion-exclusion stripping of `q0` (`b0Label`) on Pass-2 child columns:**
   In `ChildBounds`, `actualSecondInheritedRadicalPuncture m γ` factors into a `q0`-free radical
   puncture `strippedRadicalPuncture m γ` (bounded by `Z^(Q + t + g - θ + 3η)`, independent of
   `ell`) together with the squarefree prime set `B₀ ⊆ pool` dividing `γ.q0` (`|γ.q0| ≤ Z^(ell + η)`).
   Expanding `primeCoprimeMask` over `E ⊆ B₀` via `secondPreColumn_union` and
   `secondChildSum_marked_fixed_pool` absorbs `∏ i ∈ E, p i` into the child label `f` while
   rescaling the child column by `1 / primeProductNorm p E`, preserving `childF` and eliminating
   `ell` from `Q'`. Consequently every Pass-2 child gains `+(ell + V)` in its canonical margin,
   closing all cube bins with `ell + V ≥ 3 / 500`.

2. **`4 × 3 = 12` sextic-invariance label transfer on tiny cube bins (`ell + V < 3 / 500`):**
   For any prime set `V_tup` disjoint from `v.support`, replacing `z` by `(∏ j ∈ V_tup, p j)^4 * z`
   leaves `multiplicityRow p hg B v z ^ 3` invariant because `(χ_i(a)^4)^3 = (χ_i(a)^6)^2 = 1`
   on units modulo `p i`. Extracting a slot subset `U_cand` of width `u_total ≈ 33/2000` and
   splitting `U_cand` into cube-support hits `J_hit` (`z_hit ≤ ell + η`) and miss-branch tuples on
   `U_free = U_cand \ J_hit` (`u_free = u_total - z_hit ≥ 21/2000`) shifts `N' = N - u_free` and
   `M' = M + 4 u_free` while keeping `v ∈ Q` coherent inside Pass 1 (`original_dyadic_full_energy`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open scoped SchwartzMap ContDiff

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1CubeBins

open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open UniqueFactorizationMonoid
open CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open InverseMoment InverseMomentFirstLabelCell InverseMomentFirstChildWindows
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open InverseFirstPriorityParents InverseFirstGlobalCaps CanonicalCoefficientClass
open InverseInitialArithmetic IdealDivisorBound

local notation "O" => Eisenstein.O

/-! ### Part I: `4 × 3 = 12` sextic invariance of `multiplicityRow ... ^ 3` -/

section SexticInvariance

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
/-- A maximal prime ideal `span {p i}` does not divide the product over a disjoint prime set. -/
lemma not_dvd_prod_of_not_mem {V : Finset ι} {i : ι} (hiV : i ∉ V) :
    ¬ (p i ∣ ∏ j ∈ V, p j) := by
  intro hdvd
  have hmem : ∏ j ∈ V, p j ∈ Ideal.span {p i} := Ideal.mem_span_singleton.mpr hdvd
  clear hdvd
  have hprime : (Ideal.span {p i}).IsPrime := inferInstance
  have hex : ∃ j ∈ V, p j ∈ Ideal.span {p i} := by
    induction V using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty] at hmem
      exact False.elim (hprime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem))
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj] at hmem
      rcases hprime.mem_or_mem hmem with hjp | hsp
      · exact ⟨j, Finset.mem_insert_self j s, hjp⟩
      · obtain ⟨k, hk, hkp⟩ := ih (fun hi => hiV (Finset.mem_insert_of_mem hi)) hsp
        exact ⟨k, Finset.mem_insert_of_mem hk, hkp⟩
  obtain ⟨j, hjV, hjp⟩ := hex
  have hij : j ≠ i := fun h => hiV (h ▸ hjV)
  have hcop_ji : IsCoprime (Ideal.span {p j}) (Ideal.span {p i}) := hcop hij
  have hle : Ideal.span {p j} ≤ Ideal.span {p i} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hjp)
  have htop : Ideal.span {p i} = ⊤ := by
    have hsup : Ideal.span {p j} ⊔ Ideal.span {p i} = Ideal.span {p i} := sup_eq_right.mpr hle
    rw [← hsup]
    exact Ideal.isCoprime_iff_sup_eq.mp hcop_ji
  exact hprime.ne_top htop

omit [DecidableEq ι] in
/-- Sixth power of `complexSexticChar` on a non-zero residue class is `1`. -/
lemma complexSexticChar_pow_six_of_not_dvd (i : ι) {a : O} (ha : ¬ (p i ∣ a)) :
    complexSexticChar (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) a) ^ 6 = 1 := by
  letI : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field (Ideal.span {p i})
  have hne : Ideal.Quotient.mk (Ideal.span {p i}) a ≠ 0 := by
    intro hz
    exact ha (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {p i}) a) := isUnit_iff_ne_zero.mpr hne
  rw [← MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0),
    (complexSexticChar_powers (Ideal.span {p i}) (hg i)).2.2]
  exact MulChar.one_apply hu

include hcop in
/-- `4 × 3 = 12` sextic invariance: shifting `z ↦ (∏ j ∈ V, p j)^4 * z` leaves
`multiplicityRow p hg B v z ^ 3` unchanged whenever `V` misses `{i ∈ B | v i ≠ 0}`. -/
theorem multiplicityRow_cube_fourth_power_invariant
    (B V : Finset ι) (v : ι → ℕ) (z : O)
    (hdisj : ∀ i ∈ B, v i ≠ 0 → i ∉ V) :
    multiplicityRow p hg B v ((∏ j ∈ V, p j) ^ 4 * z) ^ 3 =
      multiplicityRow p hg B v z ^ 3 := by
  unfold multiplicityRow
  rw [← Finset.prod_pow B 3, ← Finset.prod_pow B 3]
  apply Finset.prod_congr rfl
  intro i hiB
  rw [← pow_mul, ← pow_mul]
  by_cases hvi : v i = 0
  · simp [hvi]
  · have hiV : i ∉ V := hdisj i hiB hvi
    have hndvd : ¬ (p i ∣ ∏ j ∈ V, p j) := not_dvd_prod_of_not_mem p hcop hiV
    have h6 := complexSexticChar_pow_six_of_not_dvd p hg i hndvd
    set χ := complexSexticChar (Ideal.span {p i}) (hg i)
    set u := Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ V, p j)
    set w := Ideal.Quotient.mk (Ideal.span {p i}) z
    have hmk : Ideal.Quotient.mk (Ideal.span {p i}) ((∏ j ∈ V, p j) ^ 4 * z) = u ^ 4 * w := by
      simp [u, w]
    rw [hmk, map_mul, map_pow, mul_pow, ← pow_mul]
    have hexp : 4 * (v i * 3) = 6 * (2 * v i) := by ring
    rw [hexp, pow_mul, h6, one_pow, one_mul]

end SexticInvariance

/-! ### Part II: Inclusion-exclusion stripping of `q0` on `finiteCanonicalMarkedRow` -/

section Q0Stripping

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
/-- Coprimality mask against a squarefree prime product `∏ i ∈ B₀, p i` is `[Disjoint S B₀]`. -/
lemma primeCoprimeMask_prime_finset_prod (S B₀ : Finset ι) :
    primeCoprimeMask p S (∏ i ∈ B₀, p i) = if Disjoint S B₀ then 1 else 0 := by
  rw [primeCoprimeMask_indicator]
  have hiff : (∀ j ∈ S, ¬ (p j ∣ ∏ i ∈ B₀, p i)) ↔ Disjoint S B₀ := by
    rw [Finset.disjoint_left]
    constructor
    · intro hall j hjS hjB
      exact hall j hjS (Finset.dvd_prod_of_mem p hjB)
    · intro hdisj j hjS
      exact not_dvd_prod_of_not_mem p hcop (hdisj hjS)
  by_cases hd : Disjoint S B₀
  · rw [if_pos hd, if_pos (hiff.mpr hd)]
  · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]

/-- Binomial inclusion-exclusion for `[Disjoint S B₀]` over `E ∈ B₀.powerset` with `E ⊆ S`. -/
lemma disjoint_indicator_eq_sum_supportMobius (S B₀ : Finset ι) :
    (if Disjoint S B₀ then (1 : ℂ) else 0) =
      ∑ E ∈ B₀.powerset, if E ⊆ S then supportMobius E else 0 := by
  have hsum : (∑ E ∈ (S ∩ B₀).powerset, supportMobius E) =
      if Disjoint S B₀ then (1 : ℂ) else 0 := by
    unfold supportMobius
    have hbin := add_pow (-1 : ℂ) (1 : ℂ) (S ∩ B₀).card
    rw [Finset.sum_powerset]
    have hbin' : (∑ k ∈ Finset.range ((S ∩ B₀).card + 1),
        ∑ E ∈ Finset.powersetCard k (S ∩ B₀), (-1 : ℂ) ^ E.card) =
        (-1 + 1 : ℂ) ^ (S ∩ B₀).card := by
      rw [hbin]
      apply Finset.sum_congr rfl
      intro k _
      calc
        (∑ E ∈ Finset.powersetCard k (S ∩ B₀), (-1 : ℂ) ^ E.card)
          = ∑ _E ∈ Finset.powersetCard k (S ∩ B₀), (-1 : ℂ) ^ k :=
            Finset.sum_congr rfl (fun E hE => by rw [(Finset.mem_powersetCard.mp hE).2])
        _ = ((S ∩ B₀).card.choose k : ℂ) * (-1 : ℂ) ^ k := by
            rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        _ = (-1 : ℂ) ^ k * 1 ^ ((S ∩ B₀).card - k) * ((S ∩ B₀).card.choose k : ℂ) := by ring
    rw [hbin', neg_add_cancel]
    by_cases hd : Disjoint S B₀
    · rw [if_pos hd, Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, pow_zero]
    · have hne : (S ∩ B₀).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hd
      rw [if_neg hd, zero_pow (Finset.Nonempty.card_pos hne).ne']
  rw [← hsum]
  have hcongr : (∑ E ∈ (S ∩ B₀).powerset, supportMobius E) =
      ∑ E ∈ (S ∩ B₀).powerset, (if E ⊆ S then supportMobius E else 0) := by
    apply Finset.sum_congr rfl
    intro E hE
    rw [if_pos (Finset.subset_inter_iff.mp (Finset.mem_powerset.mp hE)).1]
  rw [hcongr]
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.inter_subset_right)
  intro E hEB hnot
  rw [Finset.mem_powerset, Finset.subset_inter_iff] at hnot
  exact if_neg (fun hES => hnot ⟨hES, Finset.mem_powerset.mp hEB⟩)

/-- Reindexing `{S ⊆ F | E ⊆ S}` as `E ∪ N` for `N ∈ (F \ E).powerset`. -/
lemma sum_powerset_filter_subset_eq {β : Type*} [AddCommMonoid β]
    (F E : Finset ι) (hEF : E ⊆ F) (g : Finset ι → β) :
    (∑ S ∈ F.powerset, if E ⊆ S then g S else 0) =
      ∑ N ∈ (F \ E).powerset, g (E ∪ N) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun S _ => S \ E) ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl E))
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_filter] at hS₁ hS₂
    calc S₁ = E ∪ (S₁ \ E) := (Finset.union_sdiff_of_subset hS₁.2).symm
      _ = E ∪ (S₂ \ E) := by rw [heq]
      _ = S₂ := Finset.union_sdiff_of_subset hS₂.2
  · intro N hN
    have hNF : N ⊆ F \ E := Finset.mem_powerset.mp hN
    have hd : Disjoint E N :=
      Finset.disjoint_left.mpr (fun i hiE hiN => (Finset.mem_sdiff.mp (hNF hiN)).2 hiE)
    refine ⟨E ∪ N, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset hEF (hNF.trans Finset.sdiff_subset)), Finset.subset_union_left⟩, ?_⟩
    exact Finset.union_sdiff_cancel_left hd
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [Finset.union_sdiff_of_subset hS.2]

include hp hcop in
/-- Exact Möbius inclusion-exclusion of a squarefree puncture factor `∏ i ∈ B₀, p i` inside
`finiteCanonicalMarkedRow`, shifting `∏ i ∈ E, p i` into the label `f` and rescaling `X` by
`1 / primeProductNorm p E` while keeping the stripped puncture `m_strip`. -/
theorem finiteCanonicalMarkedRow_q0_split
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B₀ : Finset ι) (hB₀ : B₀ ⊆ F) (Ψ : O →* ℂ) (m_strip f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ (m_strip * ∏ i ∈ B₀, p i) f k slots lists a W X =
      ∑ E ∈ B₀.powerset, ∑ J ∈ slots.powerset,
        (supportMobius E * secondPreColumn p hg Ψ m_strip f 1 1 k (fun _ => 1) E *
          primeMark J lists a E) *
        finiteCanonicalMarkedRow p hg F Ψ m_strip (f * ∏ i ∈ E, p i) k
          (slots \ J) lists a W (X / primeProductNorm p E) := by
  have hcop_elem : Pairwise (Function.onFun IsCoprime p) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)
  have hp1 (T : Finset ι) :
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T 1 = 1 := by
    simp [primeSubsetRow]
  let H : Finset ι → ℂ := fun U => primeMark slots lists a U * W (primeProductNorm p U / X)
  have hrow : finiteCanonicalMarkedRow p hg F Ψ (m_strip * ∏ i ∈ B₀, p i) f k slots lists a W X =
      ∑ E ∈ B₀.powerset, supportMobius E * secondPreColumn p hg Ψ m_strip f 1 1 k (fun _ => 1) E *
        secondChildSum p hg F E Ψ m_strip 1 f 1 1 k H := by
    unfold finiteCanonicalMarkedRow fixedChildRow
    calc
      (∑ S ∈ F.powerset, secondChildColumn p hg Ψ (m_strip * ∏ i ∈ B₀, p i) f k H S)
        = ∑ S ∈ F.powerset, (∑ E ∈ B₀.powerset, if E ⊆ S then supportMobius E else 0) *
            secondChildColumn p hg Ψ m_strip f k H S := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← disjoint_indicator_eq_sum_supportMobius S B₀,
            ← primeCoprimeMask_prime_finset_prod p hcop S B₀]
          unfold secondChildColumn
          rw [FirstPassCubeLabels.mask_mul p hg S m_strip (∏ i ∈ B₀, p i)]
          ring
      _ = ∑ E ∈ B₀.powerset, supportMobius E *
            ∑ S ∈ F.powerset, if E ⊆ S then secondChildColumn p hg Ψ m_strip f k H S else 0 := by
          simp only [Finset.sum_mul, ite_mul, zero_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro E _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          split_ifs <;> ring
      _ = ∑ E ∈ B₀.powerset, supportMobius E *
            ∑ N ∈ (F \ E).powerset, secondChildColumn p hg Ψ m_strip f k H (E ∪ N) := by
          apply Finset.sum_congr rfl
          intro E hE
          rw [sum_powerset_filter_subset_eq F E ((Finset.mem_powerset.mp hE).trans hB₀)]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro E _
          have hunion (N : Finset ι) (hN : N ∈ (F \ E).powerset) :
              secondChildColumn p hg Ψ m_strip f k H (E ∪ N) =
                secondPreColumn p hg Ψ m_strip f 1 1 k (fun _ => 1) E *
                  secondChildColumn p hg Ψ (m_strip * 1) (f * 1 * ∏ i ∈ E, p i) (1 * 1 * k)
                    (fun U => H (E ∪ U)) N := by
            have hd : Disjoint E N := Finset.disjoint_left.mpr
              (fun i hiE hiN => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiE)
            have hp0 := secondPreColumn_union p hg hp hcop_elem hpr Ψ m_strip 1 f 1 1 k H E N hd
            have eqL : secondPreColumn p hg Ψ (m_strip * (1 * 1)) f 1 1 k H (E ∪ N) =
                secondChildColumn p hg Ψ m_strip f k H (E ∪ N) := by
              simp only [secondPreColumn, secondChildColumn, mul_one, hp1, star_one]
            rw [← eqL, hp0]
            simp only [mul_one]
          rw [Finset.sum_congr rfl hunion, ← Finset.mul_sum, ← mul_assoc]
          rfl
  rw [hrow]
  apply Finset.sum_congr rfl
  intro E _
  have hsplit := secondChildSum_marked_fixed_pool p hg F E ∅ Ψ m_strip 1 f 1 1 k slots lists a W X
  simp only [Finset.empty_union, Finset.sdiff_empty, mul_one, one_mul] at hsplit
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

omit [DecidableEq ι] in
/-- `secondPreColumn` at `E` vanishes whenever any `i ∈ E` divides `f`. -/
lemma secondPreColumn_zero_of_dvd (Ψ : O →* ℂ) (m_strip f k : O) (E : Finset ι)
    {i : ι} (hiE : i ∈ E) (hdvd : p i ∣ f) :
    secondPreColumn p hg Ψ m_strip f 1 1 k (fun _ => 1) E = 0 := by
  have hrow0 : primeSubsetRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j)) E f = 0 := by
    unfold primeSubsetRow
    apply Finset.prod_eq_zero hiE
    have hmem : Ideal.Quotient.mk (Ideal.span {p i}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd)
    rw [hmem, MulChar.map_zero]
  simp only [secondPreColumn, hrow0, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul]

include hp in
/-- Norm bound `‖supportMobius E * secondPreColumn ... E‖ ≤ 1` for `‖Ψ‖ ≤ 1`. -/
lemma supportMobius_secondPreColumn_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m_strip f k : O) (E : Finset ι) :
    ‖supportMobius E * secondPreColumn p hg Ψ m_strip f 1 1 k (fun _ => 1) E‖ ≤ 1 := by
  have hcol := secondColumnCoefficient_norm_one_of_good p hp hinj hg hc E
  have hm := primeCoprimeMask_norm_le_one p E m_strip
  have hr (x : O) := primeSubsetRow_norm_le_one p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) E x
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star,
    supportMobius_norm, hcol, one_mul, mul_one]
  calc
    ‖Ψ (∏ i ∈ E, p i)‖ * ‖primeCoprimeMask p E m_strip‖ *
      ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) E f‖ ^ 4 *
      ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) E 1‖ *
      ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) E 1‖ *
      ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) E k‖
      ≤ 1 * 1 * 1 ^ 4 * 1 * 1 * 1 := by
        gcongr <;> first | exact hΨ _ | exact hm | exact hr _
    _ = 1 := by norm_num

/-- `q0`-free radical puncture of an `OuterTriple`: keeps `m * g_quotient` and `γ.residual`
while omitting `γ.q0`. -/
def strippedRadicalPuncture (m : O) (γ : OuterTriple) : O :=
  cubicIdealGenerator ((Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual).radical)

/-- The prime subset of `pool` dividing `γ.q0` and coprime to `strippedRadicalPuncture m γ`. -/
def q0ResidualPrimes (pool : Finset ι) (m : O) (γ : OuterTriple) : Finset ι :=
  pool.filter (fun i => Ideal.span {p i} ∣ γ.q0 ∧ ¬ (p i ∣ strippedRadicalPuncture m γ))

include hp in
/-- `strippedRadicalPuncture` is non-zero and its norm is bounded without `γ.q0` (`ell`). -/
theorem strippedRadicalPuncture_bounds
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (_hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Oˣ) (m : O) (hm : m ≠ 0) :
    let γ := (actualSecondChild p u v x).1
    strippedRadicalPuncture m γ ≠ 0 ∧
      ‖ringComplex (strippedRadicalPuncture m γ)‖ ^ 2 ≤
        (Ideal.absNorm (Ideal.span {m} : Ideal O).radical : ℝ) *
          (Ideal.absNorm x.quotient : ℝ) *
          primeProductNorm p (x.second.sourceCommon \ x.second.divisor) := by
  intro γ
  have hmg : m * cubicIdealGenerator x.quotient ≠ 0 :=
    mul_ne_zero hm (cubicIdealGenerator_ne_zero x.quotient ht)
  have hIm : (Ideal.span {m * cubicIdealGenerator x.quotient} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr hmg
  have hres_eq : γ.residual = sourceIdeal p (x.second.sourceCommon \ x.second.divisor) := rfl
  have hquot_eq : γ.quotient = x.quotient := rfl
  have hres0 : γ.residual ≠ 0 := by rw [hres_eq]; exact sourceIdeal_ne_zero p hp _
  have hprod0 : Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual ≠ 0 := by
    rw [hquot_eq]; exact mul_ne_zero hIm hres0
  have hrad0 : (Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual).radical ≠ 0 := by
    intro hr
    exact hprod0 (le_antisymm (hr ▸ Ideal.le_radical) bot_le)
  refine ⟨cubicIdealGenerator_ne_zero _ hrad0, ?_⟩
  rw [strippedRadicalPuncture, ringComplex_norm_sq_eq_absNorm_span,
    span_cubicIdealGenerator, hquot_eq, hres_eq]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ) = primeProductNorm p S := by
    simpa only [sourceIdeal, primeProductNorm, map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ S, p i)).symm
  rw [← hn (x.second.sourceCommon \ x.second.divisor)]
  have h1 : ((Ideal.span {m * cubicIdealGenerator x.quotient} *
      sourceIdeal p (x.second.sourceCommon \ x.second.divisor)).radical.absNorm : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m * cubicIdealGenerator x.quotient}).radical : ℝ) *
        (Ideal.absNorm (sourceIdeal p (x.second.sourceCommon \ x.second.divisor)) : ℝ) := by
    simpa only [mul_one, map_one, Nat.cast_one] using
      radical_product_norm_le (Ideal.span {m * cubicIdealGenerator x.quotient}) 1 1
        (sourceIdeal p (x.second.sourceCommon \ x.second.divisor))
        hIm one_ne_zero (sourceIdeal_ne_zero p hp _) Ideal.le_radical
  have h2 : (Ideal.absNorm (Ideal.span {m * cubicIdealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal O).radical : ℝ) * (Ideal.absNorm x.quotient : ℝ) := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_cubicIdealGenerator]
    simpa only [mul_one, map_one, Nat.cast_one] using
      radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
        (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))

include hp hcop in
omit [DecidableEq σ] in
/-- Replacing `actualSecondInheritedRadicalPuncture m γ` by
`strippedRadicalPuncture m γ * ∏ i ∈ q0ResidualPrimes pool m γ, p i` preserves the coprimality
mask on `pool`, hence leaves `finiteCanonicalMarkedRow` identically unchanged. -/
theorem finiteCanonicalMarkedRow_eq_stripped_q0
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Oˣ) (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (hm : m ≠ 0)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let γ := (actualSecondChild p u v x).1
    finiteCanonicalMarkedRow p hg pool Ψ (actualSecondInheritedRadicalPuncture m γ)
        f k slots lists a W X =
      finiteCanonicalMarkedRow p hg pool Ψ
        (strippedRadicalPuncture m γ * ∏ i ∈ q0ResidualPrimes p pool m γ, p i)
        f k slots lists a W X := by
  intro γ
  have hmg : m * cubicIdealGenerator x.quotient ≠ 0 :=
    mul_ne_zero hm (cubicIdealGenerator_ne_zero x.quotient ht)
  have hquot_eq : γ.quotient = x.quotient := rfl
  have hres_eq : γ.residual = sourceIdeal p (x.second.sourceCommon \ x.second.divisor) := rfl
  have hq0_eq : γ.q0 = Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i + x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit} := rfl
  have hspan_full : Ideal.span {actualSecondPuncture (m * cubicIdealGenerator γ.quotient) γ} =
      (Ideal.span {m * cubicIdealGenerator γ.quotient} : Ideal O) * γ.q0 * γ.residual := by
    rw [hquot_eq, hres_eq, hq0_eq]
    rw [← actual_second_puncture_span p hp hpr x hE u v (m * cubicIdealGenerator x.quotient)]
    simp only [← Ideal.span_singleton_mul_span_singleton,
      secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span, sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
  have hdiv_iff (i : ι) (hi : i ∈ pool) :
      (p i ∣ actualSecondInheritedRadicalPuncture m γ) ↔
        (p i ∣ strippedRadicalPuncture m γ * ∏ j ∈ q0ResidualPrimes p pool m γ, p j) := by
    have hprime : (Ideal.span {p i}).IsPrime := inferInstance
    have hrad_mem : ∀ (I : Ideal O), I ≠ 0 →
        (p i ∣ cubicIdealGenerator I.radical ↔ I ≤ Ideal.span {p i}) := by
      intro I _hI0
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_le_iff_mem,
        span_cubicIdealGenerator]
      exact ⟨fun hle => Ideal.le_radical.trans hle,
        fun hle => hprime.radical_le_iff.mpr hle⟩
    have hfull0 : ((Ideal.span {m * cubicIdealGenerator γ.quotient} : Ideal O) * γ.q0 * γ.residual) ≠ 0 := by
      rw [hquot_eq, hres_eq, hq0_eq]
      exact mul_ne_zero (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hmg)
        (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)))
        (sourceIdeal_ne_zero p hp _)
    have hstrip0 : ((Ideal.span {m * cubicIdealGenerator γ.quotient} : Ideal O) * γ.residual) ≠ 0 := by
      rw [hquot_eq, hres_eq]
      exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hmg) (sourceIdeal_ne_zero p hp _)
    have hL : (p i ∣ actualSecondInheritedRadicalPuncture m γ) ↔
        ((Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual ≤ Ideal.span {p i}) ∨
          (γ.q0 ≤ Ideal.span {p i})) := by
      change (p i ∣ cubicIdealGenerator
        (Ideal.span {actualSecondPuncture (m * cubicIdealGenerator γ.quotient) γ}).radical) ↔ _
      rw [hspan_full, hrad_mem _ hfull0]
      constructor
      · intro hle
        have hmul : (Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual) * γ.q0 ≤
            Ideal.span {p i} := by
          calc _ = Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.q0 * γ.residual := by ring
            _ ≤ Ideal.span {p i} := hle
        exact hprime.mul_le.mp hmul
      · rintro (h1 | h2)
        · calc Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.q0 * γ.residual
              = (Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual) * γ.q0 := by ring
            _ ≤ Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.residual := Ideal.mul_le_right
            _ ≤ Ideal.span {p i} := h1
        · calc Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.q0 * γ.residual
              ≤ Ideal.span {m * cubicIdealGenerator γ.quotient} * γ.q0 := Ideal.mul_le_right
            _ ≤ γ.q0 := Ideal.mul_le_left
            _ ≤ Ideal.span {p i} := h2
    have hR : (p i ∣ strippedRadicalPuncture m γ * ∏ j ∈ q0ResidualPrimes p pool m γ, p j) ↔
        ((p i ∣ strippedRadicalPuncture m γ) ∨ (i ∈ q0ResidualPrimes p pool m γ)) := by
      rw [← Ideal.mem_span_singleton, hprime.mul_mem_iff_mem_or_mem,
        Ideal.mem_span_singleton, Ideal.mem_span_singleton]
      refine or_congr Iff.rfl ⟨fun hd => ?_, fun hm => Finset.dvd_prod_of_mem p hm⟩
      by_contra hni
      exact not_dvd_prod_of_not_mem p hcop hni hd
    rw [hL, hR, strippedRadicalPuncture, hrad_mem _ hstrip0]
    simp only [q0ResidualPrimes, Finset.mem_filter, hi, true_and, Ideal.dvd_iff_le,
      strippedRadicalPuncture, hrad_mem _ hstrip0]
    tauto
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  have hUP : U ⊆ pool := Finset.mem_powerset.mp hU
  have hmask : primeCoprimeMask p U (actualSecondInheritedRadicalPuncture m γ) =
      primeCoprimeMask p U (strippedRadicalPuncture m γ * ∏ j ∈ q0ResidualPrimes p pool m γ, p j) := by
    simp only [primeCoprimeMask_indicator]
    have hall : (∀ i ∈ U, ¬ p i ∣ actualSecondInheritedRadicalPuncture m γ) ↔
        (∀ i ∈ U, ¬ p i ∣ strippedRadicalPuncture m γ * ∏ j ∈ q0ResidualPrimes p pool m γ, p j) :=
      forall₂_congr (fun i hiU => not_congr (hdiv_iff i (hUP hiU)))
    by_cases h1 : ∀ i ∈ U, ¬ p i ∣ actualSecondInheritedRadicalPuncture m γ
    · rw [if_pos h1, if_pos (hall.mp h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hall.mpr h2))]
  simp only [secondChildColumn, hmask]

include hp hcop in
/-- Product and cardinality bounds on `q0ResidualPrimes`: its prime product divides `b0Label`,
so `primeProductNorm p B₀ ≤ B` and `(2 : ℝ) ^ B₀.card ≤ #(idealDivisors γ.q0)`. -/
theorem q0ResidualPrimes_bounds
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Oˣ)
    (pool : Finset ι) (m : O) (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖ ^ 2 ≤ B)
    (h2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖ ^ 2 ≤ B) :
    let γ := (actualSecondChild p u v x).1
    let B₀ := q0ResidualPrimes p pool m γ
    γ.q0 ≠ 0 ∧ (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
      primeProductNorm p B₀ ≤ B ∧
      (2 : ℝ) ^ B₀.card ≤ ((idealDivisors γ.q0).card : ℝ) := by
  intro γ B₀
  have hq0_eq : γ.q0 = Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i + x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit} := rfl
  have hq0_ne : γ.q0 ≠ 0 := by
    rw [hq0_eq]
    exact Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hq0_norm : (Ideal.absNorm γ.q0 : ℝ) ≤ B :=
    actual_second_q0_cube_bound p hp x u v B hB h1 h2
  have hdvd : sourceIdeal p B₀ ∣ γ.q0 := by
    rw [sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
    have hcop_pair : (B₀ : Set ι).Pairwise (fun i j => IsCoprime (Ideal.span {p i}) (Ideal.span {p j})) :=
      fun i _ j _ hij => hcop hij
    exact Finset.prod_dvd_of_coprime hcop_pair (fun i hi => (Finset.mem_filter.mp hi).2.1)
  have hnorm_le : primeProductNorm p B₀ ≤ B := by
    have hn : (Ideal.absNorm (sourceIdeal p B₀) : ℝ) = primeProductNorm p B₀ := by
      simpa only [sourceIdeal, primeProductNorm, map_prod] using
        (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ B₀, p i)).symm
    rw [← hn]
    have hnat : Ideal.absNorm (sourceIdeal p B₀) ≤ Ideal.absNorm γ.q0 :=
      Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hq0_ne))
        (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd))
    exact (Nat.cast_le.mpr hnat).trans hq0_norm
  have hcard_le : (2 : ℝ) ^ B₀.card ≤ ((idealDivisors γ.q0).card : ℝ) := by
    have hinj_on : Set.InjOn (sourceIdeal p) B₀.powerset := by
      intro E₁ _hE₁ E₂ _hE₂ (heq : sourceIdeal p E₁ = sourceIdeal p E₂)
      ext i
      constructor
      · intro hi₁
        have hle : sourceIdeal p E₂ ≤ Ideal.span {p i} := by
          rw [← heq, sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
          exact Ideal.prod_le_inf.trans (Finset.inf_le hi₁)
        by_contra hi₂
        have hc : IsCoprime (sourceIdeal p E₂) (Ideal.span {p i}) := by
          rw [sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
          exact IsCoprime.prod_left (fun j hj => hcop (fun hij => hi₂ (hij ▸ hj)))
        have htop : Ideal.span {p i} = ⊤ := by
          rw [← sup_eq_right.mpr hle]
          exact Ideal.isCoprime_iff_sup_eq.mp hc
        exact (inferInstance : (Ideal.span {p i}).IsPrime).ne_top htop
      · intro hi₂
        have hle : sourceIdeal p E₁ ≤ Ideal.span {p i} := by
          rw [heq, sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
          exact Ideal.prod_le_inf.trans (Finset.inf_le hi₂)
        by_contra hi₁
        have hc : IsCoprime (sourceIdeal p E₁) (Ideal.span {p i}) := by
          rw [sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
          exact IsCoprime.prod_left (fun j hj => hcop (fun hij => hi₁ (hij ▸ hj)))
        have htop : Ideal.span {p i} = ⊤ := by
          rw [← sup_eq_right.mpr hle]
          exact Ideal.isCoprime_iff_sup_eq.mp hc
        exact (inferInstance : (Ideal.span {p i}).IsPrime).ne_top htop
    have hmem : ∀ E ∈ B₀.powerset, sourceIdeal p E ∈ idealDivisors γ.q0 := by
      intro E hE
      have hEB : E ⊆ B₀ := Finset.mem_powerset.mp hE
      have hdE : sourceIdeal p E ∣ sourceIdeal p B₀ := by
        rw [sourceIdeal, sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product,
          SchwartzPlanePoisson.span_finset_prime_product]
        exact Finset.prod_dvd_prod_of_subset E B₀ (fun i => Ideal.span {p i}) hEB
      exact (mem_idealDivisors hq0_ne).mpr (hdE.trans hdvd)
    have hcard_nat : B₀.powerset.card ≤ (idealDivisors γ.q0).card :=
      Finset.card_le_card_of_injOn (sourceIdeal p) hmem hinj_on
    rw [Finset.card_powerset] at hcard_nat
    exact_mod_cast hcard_nat
  exact ⟨hq0_ne, hq0_norm, hnorm_le, hcard_le⟩

end Q0Stripping

/-! ### Part III: Label algebra and `q0`-stripped `ChildBounds` when `ell + V ≥ 3 / 500` -/

section Q0StrippedChildBounds

variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Multiplication by a principal ideal `span {g}` (`g ≠ 0`) is injective on `Ideal O`. -/
lemma span_singleton_mul_injective {g : O} (hg0 : g ≠ 0) :
    Function.Injective (fun I : Ideal O => (Ideal.span {g} : Ideal O) * I) := by
  have hmem_iff : ∀ (I : Ideal O) (z : O),
      z ∈ (Ideal.span {g} : Ideal O) * I ↔ ∃ y ∈ I, g * y = z := by
    intro I z
    constructor
    · intro hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro r hr y hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hr
        exact ⟨c * y, I.mul_mem_left c hy, by ring⟩
      · rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, mul_add g y₁ y₂⟩
    · rintro ⟨y, hy, rfl⟩
      exact Submodule.mul_mem_mul (Ideal.subset_span rfl) hy
  intro I₁ I₂ (heq : (Ideal.span {g} : Ideal O) * I₁ = (Ideal.span {g} : Ideal O) * I₂)
  ext x
  constructor
  · intro hx
    have hgx : g * x ∈ (Ideal.span {g} : Ideal O) * I₂ := by
      rw [← heq]
      exact (hmem_iff I₁ (g * x)).mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hgy⟩ := (hmem_iff I₂ (g * x)).mp hgx
    exact (mul_left_cancel₀ hg0 hgy) ▸ hy
  · intro hx
    have hgx : g * x ∈ (Ideal.span {g} : Ideal O) * I₁ := by
      rw [heq]
      exact (hmem_iff I₂ (g * x)).mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hgy⟩ := (hmem_iff I₁ (g * x)).mp hgx
    exact (mul_left_cancel₀ hg0 hgy) ▸ hy

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- Multiplication by `sourceIdeal p E` is injective on `Ideal O`. -/
lemma sourceIdeal_mul_injective (E : Finset ι) :
    Function.Injective (fun I : Ideal O => sourceIdeal p E * I) :=
  span_singleton_mul_injective (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- Multiplying a non-zero ideal `I` by `sourceIdeal p E` only increases `secondLabelWeight`. -/
lemma secondLabelWeight_le_sourceIdeal_mul (K : ℕ) (E : Finset ι) {I : Ideal O} (hI : I ≠ 0) :
    secondLabelWeight K I ≤ secondLabelWeight K (sourceIdeal p E * I) := by
  have hEI : sourceIdeal p E * I ≠ 0 := mul_ne_zero (sourceIdeal_ne_zero p hp E) hI
  have hsub : idealDivisors I ⊆ idealDivisors (sourceIdeal p E * I) := by
    intro D hD
    exact (mem_idealDivisors hEI).mpr
      (dvd_mul_of_dvd_right ((mem_idealDivisors hI).mp hD) (sourceIdeal p E))
  have hcard : ((idealDivisors I).card : ℝ) ≤ ((idealDivisors (sourceIdeal p E * I)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (9 + 4 * K)

/-- Multiplying a squarefree ideal `J` by a coprime maximal prime ideal `span {q}` (`q ≠ 0`)
preserves `Squarefree`. -/
lemma squarefree_span_prime_mul {q : O} (hq0 : q ≠ 0) [hmax : (Ideal.span {q} : Ideal O).IsMaximal]
    {J : Ideal O} (hJ : Squarefree J) (hcop_qJ : IsCoprime (Ideal.span {q}) J) :
    Squarefree ((Ideal.span {q} : Ideal O) * J) := by
  let P : Ideal O := Ideal.span {q}
  have hPprime : Prime P := Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hq0) hmax.isPrime
  intro X hX
  obtain ⟨Y, hY⟩ := hX
  by_cases hPX : P ∣ X
  · obtain ⟨Z, rfl⟩ := hPX
    have heq : P * J = P * (P * (Z * Z * Y)) := by
      calc P * J = P * Z * (P * Z) * Y := hY
        _ = P * (P * (Z * Z * Y)) := by ring
    have hJe : J = P * (Z * Z * Y) := span_singleton_mul_injective hq0 heq
    have hPJ : P ∣ J := ⟨Z * Z * Y, hJe⟩
    have hle : J ≤ P := Ideal.dvd_iff_le.mp hPJ
    have htop : P = ⊤ := by
      rw [← sup_eq_left.mpr hle]
      exact Ideal.isCoprime_iff_sup_eq.mp hcop_qJ
    exact False.elim (hmax.ne_top htop)
  · have hPXY : P ∣ X * (X * Y) := ⟨J, by rw [← mul_assoc, ← hY]⟩
    have hPY : P ∣ X * Y := (hPprime.dvd_or_dvd hPXY).resolve_left hPX
    have hPY' : P ∣ Y := (hPprime.dvd_or_dvd hPY).resolve_left hPX
    obtain ⟨W, rfl⟩ := hPY'
    have heq : P * J = P * (X * X * W) := by
      calc P * J = X * X * (P * W) := hY
        _ = P * (X * X * W) := by ring
    have hJe : J = X * X * W := span_singleton_mul_injective hq0 heq
    exact hJ X ⟨W, hJe⟩

include hp hcop hg in
/-- If `Admissible I` and no `i ∈ E` divides `primaryIdealGenerator I`, then `sourceIdeal p E * I`
is `Admissible`, its primary generator is `primaryIdealGenerator I * ∏ i ∈ E, p i`, and its norm
is `primeProductNorm p E * I.absNorm`. -/
theorem admissible_sourceIdeal_mul
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (E : Finset ι) {I : Ideal O} (hI : CanonicalQuadraticSieve.Admissible I)
    (hndvd : ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I)) :
    CanonicalQuadraticSieve.Admissible (sourceIdeal p E * I) ∧
      primaryIdealGenerator (sourceIdeal p E * I) = primaryIdealGenerator I * ∏ i ∈ E, p i ∧
      (Ideal.absNorm (sourceIdeal p E * I) : ℝ) = primeProductNorm p E * (Ideal.absNorm I : ℝ) := by
  have hIsupp : Supported I := ⟨hI.1, hI.2.2⟩
  have hgen0 : primaryIdealGenerator I ≠ 0 :=
    primaryIdealGenerator_ne_zero_of_good_factors I hI.1 (fun P hP => (hI.2.2 P hP).1)
  have hspanI : Ideal.span {primaryIdealGenerator I} = I :=
    (primaryIdealGenerator_spec I hgen0).1
  have hcop_i (i : ι) (hiE : i ∈ E) : IsCoprime (Ideal.span {p i}) I := by
    rw [← hspanI]
    exact prime_span_coprime_of_not_mem p i (primaryIdealGenerator I)
      (fun hmem => hndvd i hiE (Ideal.mem_span_singleton.mp hmem))
  have hsq : Squarefree (sourceIdeal p E * I) := by
    suffices ∀ S : Finset ι, (∀ i ∈ S, IsCoprime (Ideal.span {p i}) I) →
        Squarefree (sourceIdeal p S * I) from this E hcop_i
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have he1 : sourceIdeal p ∅ = 1 := by simp [sourceIdeal]
      rw [he1, one_mul]
      exact hI.2.1
    | @insert i s his ih =>
      intro hall
      have hprod : sourceIdeal p (insert i s) * I = Ideal.span {p i} * (sourceIdeal p s * I) := by
        rw [sourceIdeal, sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product,
          SchwartzPlanePoisson.span_finset_prime_product, Finset.prod_insert his, mul_assoc]
      rw [hprod]
      have hcop_is : IsCoprime (Ideal.span {p i}) (sourceIdeal p s) := by
        rw [sourceIdeal, SchwartzPlanePoisson.span_finset_prime_product]
        exact IsCoprime.prod_right (fun j hj => hcop (fun hij => his (hij ▸ hj)))
      exact squarefree_span_prime_mul (hp i)
        (ih (fun j hj => hall j (Finset.mem_insert_of_mem hj)))
        (IsCoprime.mul_right hcop_is (hall i (Finset.mem_insert_self i s)))
  have hsupp : Supported (sourceIdeal p E * I) := by
    rw [supported_mul_iff]
    exact ⟨canonical_source_ideal_supported p hp hg hc E, hIsupp⟩
  have hadm : CanonicalQuadraticSieve.Admissible (sourceIdeal p E * I) :=
    ⟨hsupp.1, hsq, hsupp.2⟩
  have hgen_eq : primaryIdealGenerator (sourceIdeal p E * I) =
      primaryIdealGenerator I * ∏ i ∈ E, p i := by
    rw [primaryIdealGenerator_mul, sourceIdeal_gen p hp hpr E, mul_comm]
  have hnorm_eq : (Ideal.absNorm (sourceIdeal p E * I) : ℝ) =
      primeProductNorm p E * (Ideal.absNorm I : ℝ) := by
    have hnE : (Ideal.absNorm (sourceIdeal p E) : ℝ) = primeProductNorm p E := by
      simpa only [sourceIdeal, primeProductNorm, map_prod] using
        (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ E, p i)).symm
    rw [map_mul, Nat.cast_mul, hnE]
  exact ⟨hadm, hgen_eq, hnorm_eq⟩

/-- Cauchy-Schwarz on a finite sum of complex numbers: `‖∑ u ∈ s, f u‖ ^ 2 ≤ s.card * ∑ u ∈ s, ‖f u‖ ^ 2`. -/
lemma norm_sum_sq_le_card_sum_norm_sq {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ u ∈ s, f u‖ ^ 2 ≤ (s.card : ℝ) * ∑ u ∈ s, ‖f u‖ ^ 2 := by
  calc
    ‖∑ u ∈ s, f u‖ ^ 2 ≤ (∑ u ∈ s, ‖f u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ = (∑ u ∈ s, (1 : ℝ) * ‖f u‖) ^ 2 := by simp only [one_mul]
    _ ≤ (∑ _u ∈ s, (1 : ℝ) ^ 2) * ∑ u ∈ s, ‖f u‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun u => ‖f u‖)
    _ = (s.card : ℝ) * ∑ u ∈ s, ‖f u‖ ^ 2 := by simp

include hp in
omit [DecidableEq σ] in
/-- `normalizedColumnEnergy` vanishes when `X > 0` and `1 / X > hi` for a test supported in `[lo, hi]`. -/
lemma normalizedColumnEnergy_zero_of_scale_small
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) {hi X : ℝ} (hX : 0 < X)
    (hW : ∀ y, W y ≠ 0 → y ≤ hi) (hsmall : hi * X < 1) (Z F : ℝ) :
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D W X Z F = 0 := by
  unfold normalizedColumnEnergy
  apply Finset.sum_eq_zero
  intro f _
  suffices ∑ k ∈ rows, ‖((Z ^ (-F / 2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator f) k slots lists a W X‖ ^ 2 = 0 by
    rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro k _
  have hrow0 : finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator f) k slots lists a W X = 0 := by
    rw [finiteCanonicalMarkedRow_test_sum]
    apply Finset.sum_eq_zero
    intro U _
    have hU1 : 1 ≤ primeProductNorm p U := primeProductNorm_ge_one p hp U
    have hgt : hi < primeProductNorm p U / X := (lt_div_iff₀ hX).mpr (hsmall.trans_le hU1)
    have hW0 : W (primeProductNorm p U / X) = 0 := by
      by_contra hne
      exact not_le_of_gt hgt (hW _ hne)
    rw [hW0, mul_zero]
  rw [hrow0, mul_zero, norm_zero, sq, zero_mul]

/-- Sharpened child margin after stripping `q0` (`ell`): replacing `Q + ell + t + g - θ + 4η` by
`Q_strip ≤ Q + t + g - θ + 3η` preserves `+(ell + V)` in the first canonical margin! -/
theorem stripped_child_margins
    {F M Q Q_strip z ell A t g theta V j delta eta c₁ c₂ c_out : ℝ}
    (h₁ : c₁ ≤ F - M - Q - z)
    (h₂ : c₂ ≤ 4 * F - 3 * M - 6 * z)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (_heta : 0 ≤ eta)
    (hQ : Q_strip ≤ Q + t + g - theta + 3 * eta)
    (hc₁ : c_out ≤ c₁ + ell + V - 4 * eta)
    (hc₂ : c_out ≤ c₂ - 7 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q_strip z c_out := by
  unfold childF childM decrease
  constructor <;> linarith

private lemma sum_comm_lbls_EJ {α β γ δ : Type*}
    (sI : Finset α) (sk : Finset β) (sE : Finset γ) (sJ : Finset δ)
    (w : α → ℝ) (c : ℝ) (F : α → β → γ → δ → ℝ) :
    (∑ I ∈ sI, w I * ∑ k ∈ sk, c * ∑ E ∈ sE, ∑ J ∈ sJ, F I k E J) =
      c * ∑ E ∈ sE, ∑ J ∈ sJ, ∑ I ∈ sI, w I * ∑ k ∈ sk, F I k E J := by
  have h1 : (∑ I ∈ sI, w I * ∑ k ∈ sk, c * ∑ E ∈ sE, ∑ J ∈ sJ, F I k E J) =
      ∑ I ∈ sI, ∑ E ∈ sE, ∑ J ∈ sJ, c * (w I * ∑ k ∈ sk, F I k E J) := by
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.mul_sum]
    calc
      (∑ k ∈ sk, w I * (c * ∑ E ∈ sE, ∑ J ∈ sJ, F I k E J))
        = ∑ k ∈ sk, ∑ E ∈ sE, ∑ J ∈ sJ, c * (w I * F I k E J) := by
            apply Finset.sum_congr rfl
            intro k _
            simp only [Finset.mul_sum, mul_left_comm]
      _ = ∑ E ∈ sE, ∑ k ∈ sk, ∑ J ∈ sJ, c * (w I * F I k E J) := Finset.sum_comm
      _ = ∑ E ∈ sE, ∑ J ∈ sJ, ∑ k ∈ sk, c * (w I * F I k E J) :=
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ E ∈ sE, ∑ J ∈ sJ, c * (w I * ∑ k ∈ sk, F I k E J) := by
            apply Finset.sum_congr rfl
            intro E _
            apply Finset.sum_congr rfl
            intro J _
            simp only [Finset.mul_sum]
  rw [h1, Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.mul_sum]

include hp hcop hg in
/-- `q0`-stripped `ChildBounds`: given `CanonicalRankMoments` for `(ω₁, ω₂)` and their
`canonical_clipped_uniform` companions `(ω₁_clip, ω₂_clip)` at margin `c_out`, every cube bin
whose parent satisfies `c₁ + ell + V - 4η ≥ c_out` and `c₂ - 7η ≥ c_out` satisfies `ChildBounds`
with `q0` (`b0Label`) stripped! -/
theorem childBounds_of_q0_stripped_rank_moments
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (base Ψ : O →* ℂ) (hΨbase : IsBaseRayTwist base Ψ) (hΨ1 : ∀ u, ‖Ψ u‖ ≤ 1)
    (m : O) (hm : m ≠ 0)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (K degree : ℕ)
    (hlists : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ i ∈ slots, ∀ q ∈ lists i, ‖a i q‖ ≤ 1) (hK : slots.card ≤ K)
    (ω₁ ω₂ ω₁_clip ω₂_clip : 𝓢(ℝ, ℂ))
    {af₁ bf₁ af₂ bf₂ C_clip₁ C_clip₂ : ℝ}
    (haf₁ : 0 < af₁) (hsω₁ : Function.support (ω₁ : ℝ → ℂ) ⊆ Set.Icc af₁ bf₁)
    (haf₂ : 0 < af₂) (hsω₂ : Function.support (ω₂ : ℝ → ℂ) ⊆ Set.Icc af₂ bf₂)
    (hC_clip₁ : 0 < C_clip₁) (hC_clip₂ : 0 < C_clip₂)
    (hclip₁ : ∀ (Ξ : O →* ℂ) (m_s : O) (sub : Finset σ) (lbls : Finset (Ideal O))
      (rws : Finset O) (Z_c F_c E_c : ℝ) (c_sc : ℝ) (s_ht : ℝ),
      1 ≤ c_sc → c_sc ≤ max 1 bf₁ → 0 ≤ E_c →
      (∀ s', normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
        (childLogTest ω₁_clip s') 1 Z_c F_c ≤ E_c * (1 + ‖s'‖) ^ (2 * degree)) →
      normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
        (clippedTest ω₁ c_sc s_ht) 1 Z_c F_c ≤ C_clip₁ * E_c * (1 + ‖s_ht‖) ^ (2 * degree))
    (hclip₂ : ∀ (Ξ : O →* ℂ) (m_s : O) (sub : Finset σ) (lbls : Finset (Ideal O))
      (rws : Finset O) (Z_c F_c E_c : ℝ) (c_sc : ℝ) (s_ht : ℝ),
      1 ≤ c_sc → c_sc ≤ max 1 bf₂ → 0 ≤ E_c →
      (∀ s', normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
        (childLogTest ω₂_clip s') 1 Z_c F_c ≤ E_c * (1 + ‖s'‖) ^ (2 * degree)) →
      normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
        (clippedTest ω₂ c_sc s_ht) 1 Z_c F_c ≤ C_clip₂ * E_c * (1 + ‖s_ht‖) ^ (2 * degree))
    {C_div eps_div : ℝ} (hC_div : 0 < C_div) (heps_div : 0 ≤ eps_div)
    (hdiv_pow : ∀ I : Ideal O, I ≠ 0 → ((idealDivisors I).card : ℝ) ^ 4 ≤ C_div * (Ideal.absNorm I : ℝ) ^ eps_div)
    (Z M r ell V eta tau window b cutoff Qwidth z c₁ c₂ c_out eps A : ℝ)
    (hZ : 1 < Z) (heta : 0 ≤ eta) (hbin : 2 ≤ Z ^ eta) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hb : 1 ≤ b) (hbt : b ≤ Z ^ (6 * eta)) (hwindow : Real.exp window ≤ Z ^ (4 * eta))
    (hbf₁Z : max 1 bf₁ ≤ Z ^ eta) (hbf₂Z : max 1 bf₂ ≤ Z ^ eta)
    (hterminal : cutoff ≤ ell + V) (hsmall : eta ≤ cutoff / 16)
    (h₁_p : c₁ ≤ (r + 3 * ell + V) - M - Qwidth - z)
    (h₂_p : c₂ ≤ 4 * (r + 3 * ell + V) - 3 * M - 6 * z)
    (hc₁_out : c_out ≤ c₁ + ell + V - 4 * eta)
    (hc₂_out : c_out ≤ c₂ - 7 * eta)
    (hpuncture : (Ideal.absNorm (Ideal.span {m} : Ideal O).radical : ℝ) ≤ Z ^ Qwidth)
    (hQ : ∀ v ∈ Q, ‖ringComplex (primeProduct p v.support v)‖ ^ 2 ≤ Z ^ (ell + eta))
    (hA : 0 ≤ A)
    (hm₁ : CanonicalRankMoments p hg pool base slots lists a ω₁
      Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree)
    (hm₂ : CanonicalRankMoments p hg pool base slots lists a ω₂
      Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree)
    (hm₁_c : CanonicalRankMoments p hg pool base slots lists a ω₁_clip
      Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree)
    (hm₂_c : CanonicalRankMoments p hg pool base slots lists a ω₂_clip
      Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree) :
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b (eps + eps_div * (ell + eta))
      ((4 : ℝ) ^ K * C_div * max (C_clip₁ * max 1 bf₁ ^ 2) (max (C_clip₂ * max 1 bf₂ ^ 2) 1) * A)
      K degree := by
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  intro ray core assigned hass
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase₀ : IsBaseRayTwist base Ψ₀ := hΨbase.firstCore _ _ _
  have hΨ₀1 : ∀ u, ‖Ψ₀ u‖ ≤ 1 := fun u => (firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ1 u)
  have hstate := source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hlabels := source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  have hsrc_cond : ActualSecondSourceConditions p S :=
    source_valid p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b
  have hsrc_freq : ∀ x ∈ S, x.second.frequency ≠ 0 :=
    source_frequency_ne_zero p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  have hnum := retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative assigned lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
  let C_max := max (C_clip₁ * max 1 bf₁ ^ 2) (max (C_clip₂ * max 1 bf₂ ^ 2) 1)
  have hC_max1 : 1 ≤ C_max := (le_max_right _ _).trans (le_max_right _ _)
  have hbranch : ∀ (Ξ : O →* ℂ) (hΞbase : IsBaseRayTwist base Ξ) (hΞ1 : ∀ u, ‖Ξ u‖ ≤ 1)
      (w0 wc : 𝓢(ℝ, ℂ)) (af bf C_c : ℝ)
      (_haf : 0 < af) (hsw0 : Function.support (w0 : ℝ → ℂ) ⊆ Set.Icc af bf)
      (hCc : 0 < C_c) (hbfZ : max 1 bf ≤ Z ^ eta)
      (hCc_le : C_c * max 1 bf ^ 2 ≤ C_max)
      (hclip : ∀ (m_s : O) (sub : Finset σ) (lbls : Finset (Ideal O))
        (rws : Finset O) (Z_c F_c E_c c_sc s_ht : ℝ),
        1 ≤ c_sc → c_sc ≤ max 1 bf → 0 ≤ E_c →
        (∀ s', normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
          (childLogTest wc s') 1 Z_c F_c ≤ E_c * (1 + ‖s'‖) ^ (2 * degree)) →
        normalizedColumnEnergy p hg pool Ξ m_s sub lists a lbls rws (secondLabelWeight K)
          (clippedTest w0 c_sc s_ht) 1 Z_c F_c ≤ C_c * E_c * (1 + ‖s_ht‖) ^ (2 * degree))
      (hm_un : CanonicalRankMoments p hg pool base slots lists a w0
        Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree)
      (hm_cl : CanonicalRankMoments p hg pool base slots lists a wc
        Z (M - 3 * cutoff / 2) (r + 3 * ell + V + 16 * eta) z c_out eps A K degree)
      (d : BlockIndex) (hdcell : d ∈ keys p S) (s_ht : ℝ)
      (J_sub : Finset σ) (_hJ_sub : J_sub ∈ (slots \ assigned).powerset)
      (γ : OuterTriple) (hγ : γ ∈ actualSecondTriples p 1 1 (cell p S d)),
      normalizedColumnEnergy p hg pool Ξ (actualSecondInheritedRadicalPuncture m γ)
        ((slots \ assigned) \ J_sub) lists a ((actualCellLabels p S d).filter Squarefree)
        (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
        (secondLabelWeight K) (childLogTest w0 s_ht)
        (Z ^ (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
        (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d) ≤
      ((4 : ℝ) ^ K * C_div * C_max * A) *
        Z ^ (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d +
          (eps + eps_div * (ell + eta))) * (1 + ‖s_ht‖) ^ (2 * degree) := by
    intro Ξ hΞbase hΞ1 w0 wc af bf C_c _haf hsw0 hCc hbfZ hCc_le hclip hm_un hm_cl d hdcell s_ht J_sub _hJ_sub γ hγ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
    have hxs : x ∈ S := cell_subset p S d hx
    have st := hstate d hdcell
    let sub := (slots \ assigned) \ J_sub
    have hsub_slots : sub ⊆ slots := Finset.sdiff_subset.trans Finset.sdiff_subset
    let m_strip := strippedRadicalPuncture m (actualSecondChild p 1 1 x).1
    let B₀ := q0ResidualPrimes p pool m (actualSecondChild p 1 1 x).1
    have hB₀_sub : B₀ ⊆ pool := Finset.filter_subset _ _
    obtain ⟨hm_strip0, hm_strip_norm⟩ := strippedRadicalPuncture_bounds p hp x
      (hsrc_cond.second_divisor x hxs) (hsrc_cond.quotient_nonzero x hxs) 1 1 m hm
    have hG_x := (actual_cell_norm_centers p hp S hsrc_freq d x hx Z eta hZ heta hbin 0).2
    have hD_x := (actual_cell_norm_centers p hp S hsrc_freq d x hx Z eta hZ heta hbin 1).1
    have hx_cube1 : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖ ^ 2 ≤ Z ^ (ell + eta) :=
      (hnum x hxs).1
    have hx_cube2 : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖ ^ 2 ≤ Z ^ (ell + eta) :=
      (hnum x hxs).2.1
    have hx_quot : (Ideal.absNorm x.quotient : ℝ) ≤ Z ^ (exponent Z l + eta) :=
      (hnum x hxs).2.2.2.2.1
    obtain ⟨hq0_ne, hq0_norm, _hB₀_norm, hB₀_card⟩ :=
      q0ResidualPrimes_bounds p hp hcop x 1 1 pool m (Z ^ (ell + eta)) (Real.rpow_pos_of_pos hz0 _).le
        hx_cube1 hx_cube2
    let Q_strip := Real.logb Z (‖ringComplex m_strip‖ ^ 2)
    have hQ_strip_nonneg : 0 ≤ Q_strip :=
      Real.logb_nonneg hZ (SchwartzPlanePoisson.one_le_eisenstein_norm_sq m_strip hm_strip0)
    have hQ_strip_pow : ‖ringComplex m_strip‖ ^ 2 = Z ^ Q_strip :=
      (Real.rpow_logb hz0 (ne_of_gt hZ) (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hm_strip0)))).symm
    have hres_pow : primeProductNorm p (x.second.sourceCommon \ x.second.divisor) ≤
        Z ^ (secondCellExponent Z d 0 - secondCellExponent Z d 1 + 2 * eta) :=
      second_residual_norm_power_bound p hp _ _ (hsrc_cond.second_divisor x hxs)
        Z (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hz0
        (by simpa only [outerNorms, Matrix.cons_val_zero] using hG_x)
        (by simpa only [outerNorms, Matrix.cons_val_one, Matrix.cons_val_zero] using hD_x)
    have hQ_strip_le : Q_strip ≤ Qwidth + exponent Z l + secondCellExponent Z d 0 - secondCellExponent Z d 1 + 3 * eta := by
      apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hm_strip0)))).mpr
      calc
        ‖ringComplex m_strip‖ ^ 2
          ≤ (Z ^ Qwidth * Z ^ (exponent Z l + eta)) *
              Z ^ (secondCellExponent Z d 0 - secondCellExponent Z d 1 + 2 * eta) := by
            apply hm_strip_norm.trans
            have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon \ x.second.divisor)).le
            gcongr
        _ = Z ^ (Qwidth + exponent Z l + secondCellExponent Z d 0 - secondCellExponent Z d 1 + 3 * eta) := by
            rw [← Real.rpow_add hz0, ← Real.rpow_add hz0]
            congr 1; ring
    let N_in := max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d)
    let V_in := actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d
    let F_in := actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d
    let M_in := actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d
    let lbls := (actualCellLabels p S d).filter Squarefree
    let rws := nonzeroChildFrequencyBall 1 (Z ^ M_in)
    have hgt_center : -2 * eta ≤ secondCellExponent Z d 0 - secondCellExponent Z d 1 :=
      actual_second_common_center p hp x (hsrc_cond.second_divisor x hxs)
        Z (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
        (by simpa only [outerNorms, Matrix.cons_val_zero] using hG_x)
        (by simpa only [outerNorms, Matrix.cons_val_one, Matrix.cons_val_zero] using hD_x)
    have hF_in_margin : CanonicalMargins F_in M_in Q_strip z c_out := by
      change CanonicalMargins
        (actualCellTotalExponent Z (Z ^ (r - columnA Z k negative - exponent Z (k 2) - exponent Z l))
          (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta) Q_strip z c_out
      rw [actual_cell_total_transition Z r ell V (columnA Z k negative) (exponent Z (k 2))
        (exponent Z l) (exponent Z j) eta d hZ]
      exact stripped_child_margins h₁_p h₂_p
        (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV (dyadic_exponent_nonneg Z hZ _)
        hgt_center
        (by unfold actualCellClipping; have := le_max_right 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d); linarith)
        heta hQ_strip_le hc₁_out hc₂_out
    have hEJ_bound : ∀ E ∈ B₀.powerset, ∀ J ∈ sub.powerset,
        (∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
          if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
            ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
              finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
          else 0) ≤
        C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree) := by
      intro E _hE J _hJ
      let e_E := Real.logb Z (primeProductNorm p E)
      have he_E0 : 0 ≤ e_E := Real.logb_nonneg hZ (primeProductNorm_ge_one p hp E)
      have he_Epow : Z ^ e_E = primeProductNorm p E :=
        Real.rpow_logb hz0 (ne_of_gt hZ) (primeProductNorm_pos p hp E)
      have hX_E : Z ^ N_in / primeProductNorm p E = Z ^ (N_in - e_E) := by
        rw [← he_Epow, ← Real.rpow_sub hz0]
      let lbls_cop := lbls.filter (fun I => ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I))
      let lbls' := lbls_cop.image (fun I => sourceIdeal p E * I)
      have hlbls'_adm : ∀ I' ∈ lbls', CanonicalQuadraticSieve.Admissible I' ∧
          (Ideal.absNorm I' : ℝ) ≤ Z ^ (V_in + e_E) := by
        intro I' hI'
        obtain ⟨I, hI_mem, rfl⟩ := Finset.mem_image.mp hI'
        obtain ⟨hI_lbl, hI_nd⟩ := Finset.mem_filter.mp hI_mem
        have hI_adm := actual_cell_labels_admissible p hp hg hc S d I hI_lbl
        obtain ⟨hadm', _, hnorm'⟩ := admissible_sourceIdeal_mul p hp hcop hg hc hpr E hI_adm hI_nd
        refine ⟨hadm', ?_⟩
        rw [hnorm', ← he_Epow, mul_comm, Real.rpow_add hz0]
        exact mul_le_mul_of_nonneg_right ((hlabels.2 d I hI_lbl).2.2) (Real.rpow_nonneg hz0.le _)
      have hsum_le_energy :
          (∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
            if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
              ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                  (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
            else 0) ≤
          normalizedColumnEnergy p hg pool Ξ m_strip (sub \ J) lists a lbls' rws
            (secondLabelWeight K) (childLogTest w0 s_ht) (Z ^ (N_in - e_E)) Z F_in := by
        rw [hX_E]
        calc
          _ = ∑ I ∈ lbls_cop, secondLabelWeight K I * ∑ k_r ∈ rws,
                ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                  finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                    (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ (N_in - e_E))‖ ^ 2 := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro I _
              by_cases hnd : ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I)
              · simp only [if_pos hnd]
              · simp only [if_neg hnd, Finset.sum_const_zero, mul_zero]
          _ ≤ ∑ I ∈ lbls_cop, secondLabelWeight K (sourceIdeal p E * I) * ∑ k_r ∈ rws,
                ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                  finiteCanonicalMarkedRow p hg pool Ξ m_strip
                    (primaryIdealGenerator (sourceIdeal p E * I)) k_r
                    (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ (N_in - e_E))‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro I hI_mem
              obtain ⟨hI_lbl, hI_nd⟩ := Finset.mem_filter.mp hI_mem
              have hI_adm := actual_cell_labels_admissible p hp hg hc S d I hI_lbl
              obtain ⟨_, hgen_eq, _⟩ := admissible_sourceIdeal_mul p hp hcop hg hc hpr E hI_adm hI_nd
              rw [hgen_eq]
              exact mul_le_mul_of_nonneg_right
                (secondLabelWeight_le_sourceIdeal_mul p hp K E hI_adm.1)
                (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          _ = normalizedColumnEnergy p hg pool Ξ m_strip (sub \ J) lists a lbls' rws
                (secondLabelWeight K) (childLogTest w0 s_ht) (Z ^ (N_in - e_E)) Z F_in := by
              unfold normalizedColumnEnergy
              exact (Finset.sum_image (fun I₁ _ I₂ _ he => sourceIdeal_mul_injective p hp E he)).symm
      apply hsum_le_energy.trans
      let N_E := N_in - e_E
      have hNE_sum : N_E + (V_in + e_E) = F_in := by dsimp [N_E, F_in, actualCellTotalExponent, N_in, V_in]; ring
      by_cases hN_nonneg : 0 ≤ N_E
      · have hm_app := hm_un Ξ hΞbase m_strip hm_strip0 N_E (V_in + e_E) M_in Q_strip
          hN_nonneg (add_nonneg st.2.1 he_E0) st.2.2.2.1 hQ_strip_nonneg
          (by linarith [st.2.2.2.2]) (by rw [hNE_sum]; linarith [st.2.2.1, heta])
          (by rwa [hNE_sum]) hQ_strip_pow (sub \ J) (Finset.sdiff_subset.trans hsub_slots)
          lbls' hlbls'_adm s_ht
        rw [hNE_sum] at hm_app
        exact hm_app.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hA hC_max1) (Real.rpow_nonneg hz0.le _))
          (by positivity))
      · have hN_neg : N_E < 0 := not_le.mp hN_nonneg
        by_cases hsmall_E : max 1 bf * Z ^ N_E < 1
        · have hw0_hi : ∀ y, childLogTest w0 s_ht y ≠ 0 → y ≤ max 1 bf := by
            intro y hy
            exact (hsw0 ((mul_ne_zero_iff.mp hy).1)).2.trans (le_max_right 1 bf)
          rw [normalizedColumnEnergy_zero_of_scale_small p hp hg pool Ξ m_strip (sub \ J) lists a
            lbls' rws (secondLabelWeight K) (childLogTest w0 s_ht) (Real.rpow_pos_of_pos hz0 N_E)
            hw0_hi hsmall_E Z F_in]
          positivity
        · have hge1 : 1 ≤ max 1 bf * Z ^ N_E := not_lt.mp hsmall_E
          have hmax0 : max 0 N_E = 0 := max_eq_left hN_neg.le
          have hc_ge1 : 1 ≤ Z ^ (-N_E) := Real.one_le_rpow hZ.le (by linarith)
          have hc_le_bf : Z ^ (-N_E) ≤ max 1 bf := by
            have hp_pos : 0 < Z ^ N_E := Real.rpow_pos_of_pos hz0 N_E
            rw [Real.rpow_neg hz0.le]
            exact (inv_le_iff_one_le_mul₀ hp_pos).mpr hge1
          have h_negNE_eta : -N_E ≤ eta :=
            (Real.rpow_le_rpow_left_iff hZ).mp (hc_le_bf.trans hbfZ)
          have hVE_eq : V_in + e_E = F_in + (-N_E) := by linarith [hNE_sum]
          have hVE_cap : 0 + (V_in + e_E) ≤ r + 3 * ell + V + 16 * eta := by
            linarith [st.2.2.1, h_negNE_eta]
          have hVE_margin : CanonicalMargins (0 + (V_in + e_E)) M_in Q_strip z c_out := by
            obtain ⟨hm1, hm2⟩ := hF_in_margin
            constructor <;> linarith
          have hnorm_clip :
              normalizedColumnEnergy p hg pool Ξ m_strip (sub \ J) lists a lbls' rws
                (secondLabelWeight K) (childLogTest w0 s_ht) (Z ^ N_E) Z F_in =
              Z ^ (V_in + e_E - F_in) *
                normalizedColumnEnergy p hg pool Ξ m_strip (sub \ J) lists a lbls' rws
                  (secondLabelWeight K) (clippedTest w0 (Z ^ (-N_E)) s_ht) 1 Z (V_in + e_E) := by
            have hc1 := columnEnergy_normalization p hg pool Ξ m_strip (sub \ J) lists a
              lbls' rws (secondLabelWeight K) (childLogTest w0 s_ht) (Z ^ N_E) hz0 F_in
            have hc2 := initial_columnEnergy_clipping_normalized p hg hp pool Ξ m_strip (sub \ J) lists a
              lbls' rws (secondLabelWeight K) w0 hz0 N_E (V_in + e_E) s_ht
            rw [hmax0, zero_sub, zero_add, Real.rpow_zero] at hc2
            apply mul_left_cancel₀ (Real.rpow_pos_of_pos hz0 F_in).ne'
            rw [← hc1, hc2, ← mul_assoc, ← Real.rpow_add hz0, show F_in + (V_in + e_E - F_in) = V_in + e_E by ring]
          rw [hnorm_clip]
          have hclipped := hclip m_strip (sub \ J) lbls' rws Z (V_in + e_E)
            (A * Z ^ (V_in + e_E + eps)) (Z ^ (-N_E)) s_ht hc_ge1 hc_le_bf
            (mul_nonneg hA (Real.rpow_nonneg hz0.le _)) (fun s' => by
              simpa only [zero_add, Real.rpow_zero] using
                hm_cl Ξ hΞbase m_strip hm_strip0 0 (V_in + e_E) M_in Q_strip
                  le_rfl (add_nonneg st.2.1 he_E0) st.2.2.2.1 hQ_strip_nonneg
                  (by linarith [st.2.2.2.2]) hVE_cap hVE_margin hQ_strip_pow
                  (sub \ J) (Finset.sdiff_subset.trans hsub_slots) lbls' hlbls'_adm s')
          have hdiff : V_in + e_E - F_in = -N_E := by linarith [hNE_sum]
          calc
            Z ^ (V_in + e_E - F_in) *
                normalizedColumnEnergy p hg pool Ξ m_strip (sub \ J) lists a lbls' rws
                  (secondLabelWeight K) (clippedTest w0 (Z ^ (-N_E)) s_ht) 1 Z (V_in + e_E)
              ≤ Z ^ (-N_E) * (C_c * (A * Z ^ (F_in + (-N_E) + eps)) * (1 + ‖s_ht‖) ^ (2 * degree)) := by
                rw [hdiff, ← hVE_eq]
                exact mul_le_mul_of_nonneg_left hclipped (Real.rpow_nonneg hz0.le _)
            _ = (C_c * (Z ^ (-N_E)) ^ 2) * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree) := by
                rw [show F_in + (-N_E) + eps = (-N_E) + (F_in + eps) by ring, Real.rpow_add hz0]
                ring
            _ ≤ C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree) := by
                have hsq_le : C_c * (Z ^ (-N_E)) ^ 2 ≤ C_max :=
                  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg hz0.le _) hc_le_bf 2) hCc.le).trans hCc_le
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq_le hA) (Real.rpow_nonneg hz0.le _))
                  (by positivity)
    have hcard_sub : (sub.powerset.card : ℝ) ≤ (2 : ℝ) ^ K := by
      rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) ((Finset.card_le_card hsub_slots).trans hK)
    have hcard_B₀ : (B₀.powerset.card : ℝ) = (2 : ℝ) ^ B₀.card := by
      rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    have hpointwise : ∀ I ∈ lbls, ∀ k_r ∈ rws,
        ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
          finiteCanonicalMarkedRow p hg pool Ξ
            (actualSecondInheritedRadicalPuncture m (actualSecondChild p 1 1 x).1)
            (primaryIdealGenerator I) k_r sub lists a (childLogTest w0 s_ht) (Z ^ N_in)‖ ^ 2 ≤
        ((2 : ℝ) ^ K * ((2 : ℝ) ^ B₀.card) ^ 3) *
          ∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
            if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
              ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                finiteCanonicalMarkedRow p hg pool Ξ m_strip
                  (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                  (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
            else 0 := by
      intro I _hI k_r _hk_r
      rw [finiteCanonicalMarkedRow_eq_stripped_q0 p hp hcop hg hpr x
        (hsrc_cond.second_divisor x hxs) (hsrc_cond.quotient_nonzero x hxs) 1 1 pool Ξ m
        (primaryIdealGenerator I) k_r hm sub lists a (childLogTest w0 s_ht) (Z ^ N_in)]
      rw [finiteCanonicalMarkedRow_q0_split p hp hcop hg hpr pool B₀ hB₀_sub Ξ m_strip
        (primaryIdealGenerator I) k_r sub lists a (childLogTest w0 s_ht) (Z ^ N_in)]
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum, ← Finset.sum_product']
      apply (norm_sum_sq_le_card_sum_norm_sq (B₀.powerset ×ˢ sub.powerset) _).trans
      rw [Finset.card_product, Nat.cast_mul, hcard_B₀, Finset.sum_product]
      have hcard_prod : (2 : ℝ) ^ B₀.card * (sub.powerset.card : ℝ) ≤
          (2 : ℝ) ^ K * (2 : ℝ) ^ B₀.card :=
        mul_comm ((2 : ℝ) ^ B₀.card) (sub.powerset.card : ℝ) ▸
          mul_le_mul_of_nonneg_right hcard_sub (by positivity)
      calc
        ((2 : ℝ) ^ B₀.card * (sub.powerset.card : ℝ)) *
            ∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
              ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                ((supportMobius E * secondPreColumn p hg Ξ m_strip (primaryIdealGenerator I) 1 1 k_r (fun _ => 1) E *
                    primeMark J lists a E) *
                  finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                    (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E))‖ ^ 2
          ≤ ((2 : ℝ) ^ K * (2 : ℝ) ^ B₀.card) *
              ∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
                ((2 : ℝ) ^ B₀.card) ^ 2 *
                  (if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
                    ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                      finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                        (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
                  else 0) := by
            apply mul_le_mul hcard_prod _ (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by positivity)
            apply Finset.sum_le_sum
            intro E hE
            apply Finset.sum_le_sum
            intro J hJ
            by_cases hnd : ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I)
            · rw [if_pos hnd]
              have hpre1 := supportMobius_secondPreColumn_norm_le_one p hp hg hinj hc Ξ hΞ1
                m_strip (primaryIdealGenerator I) k_r E
              have hJsub : J ⊆ slots := (Finset.mem_powerset.mp hJ).trans hsub_slots
              have hpm := primeMark_norm_le_divisor_count J lists a E
                (fun i hi j hj hij => hlists (hJsub hi) (hJsub hj) hij)
                (fun i hi => ha i (hJsub hi))
              have hEcard : (2 : ℝ) ^ E.card ≤ (2 : ℝ) ^ B₀.card :=
                pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.mem_powerset.mp hE))
              have hcoef_le : ‖supportMobius E * secondPreColumn p hg Ξ m_strip (primaryIdealGenerator I) 1 1 k_r (fun _ => 1) E *
                  primeMark J lists a E‖ ≤ (2 : ℝ) ^ B₀.card := by
                rw [norm_mul]
                exact (mul_le_mul hpre1 (hpm.trans hEcard) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
              have hrew : ((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                  ((supportMobius E * secondPreColumn p hg Ξ m_strip (primaryIdealGenerator I) 1 1 k_r (fun _ => 1) E *
                      primeMark J lists a E) *
                    finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                      (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)) =
                  (supportMobius E * secondPreColumn p hg Ξ m_strip (primaryIdealGenerator I) 1 1 k_r (fun _ => 1) E *
                      primeMark J lists a E) *
                    (((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                      finiteCanonicalMarkedRow p hg pool Ξ m_strip (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                        (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)) := by ring
              rw [hrew, norm_mul, mul_pow]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hcoef_le 2) (sq_nonneg _)
            · rw [if_neg hnd, mul_zero]
              push Not at hnd
              obtain ⟨i, hiE, hdvd⟩ := hnd
              rw [secondPreColumn_zero_of_dvd p hg Ξ m_strip (primaryIdealGenerator I) k_r E hiE hdvd]
              simp
        _ = _ := by
            simp_rw [← Finset.mul_sum]
            ring
    have hdiv_B₀ : ((2 : ℝ) ^ B₀.card) ^ 4 ≤ C_div * Z ^ (eps_div * (ell + eta)) := by
      calc
        ((2 : ℝ) ^ B₀.card) ^ 4
          ≤ ((idealDivisors (actualSecondChild p 1 1 x).1.q0).card : ℝ) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hB₀_card 4
        _ ≤ C_div * ((Ideal.absNorm (actualSecondChild p 1 1 x).1.q0 : ℝ)) ^ eps_div :=
            hdiv_pow _ hq0_ne
        _ ≤ C_div * (Z ^ (ell + eta)) ^ eps_div :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hq0_norm heps_div) hC_div.le
        _ = C_div * Z ^ (eps_div * (ell + eta)) := by
            rw [← Real.rpow_mul hz0.le, mul_comm (ell + eta) eps_div]
    unfold normalizedColumnEnergy
    calc
      (∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
          ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
            finiteCanonicalMarkedRow p hg pool Ξ
              (actualSecondInheritedRadicalPuncture m (actualSecondChild p 1 1 x).1)
              (primaryIdealGenerator I) k_r sub lists a (childLogTest w0 s_ht) (Z ^ N_in)‖ ^ 2)
        ≤ ∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
            ((2 : ℝ) ^ K * ((2 : ℝ) ^ B₀.card) ^ 3) *
              ∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
                if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
                  ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                    finiteCanonicalMarkedRow p hg pool Ξ m_strip
                      (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                      (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
                else 0 := by
          apply Finset.sum_le_sum
          intro I hI
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (hpointwise I hI))
            (by unfold secondLabelWeight; positivity)
      _ = ((2 : ℝ) ^ K * ((2 : ℝ) ^ B₀.card) ^ 3) *
            ∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
              ∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
                if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
                  ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                    finiteCanonicalMarkedRow p hg pool Ξ m_strip
                      (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                      (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
                else 0 :=
          sum_comm_lbls_EJ lbls rws B₀.powerset sub.powerset (secondLabelWeight K) _ _
      _ ≤ ((2 : ℝ) ^ K * ((2 : ℝ) ^ B₀.card) ^ 3) *
            ((2 : ℝ) ^ B₀.card * (2 : ℝ) ^ K *
              (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (∑ E ∈ B₀.powerset, ∑ J ∈ sub.powerset,
                ∑ I ∈ lbls, secondLabelWeight K I * ∑ k_r ∈ rws,
                  if ∀ i ∈ E, ¬ (p i ∣ primaryIdealGenerator I) then
                    ‖((Z ^ (-F_in / 2) : ℝ) : ℂ) *
                      finiteCanonicalMarkedRow p hg pool Ξ m_strip
                        (primaryIdealGenerator I * ∏ i ∈ E, p i) k_r
                        (sub \ J) lists a (childLogTest w0 s_ht) (Z ^ N_in / primeProductNorm p E)‖ ^ 2
                  else 0)
              ≤ ∑ _E ∈ B₀.powerset, ∑ _J ∈ sub.powerset,
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)) :=
                Finset.sum_le_sum (fun E hE => Finset.sum_le_sum (fun J hJ => hEJ_bound E hE J hJ))
            _ = (2 : ℝ) ^ B₀.card * (sub.powerset.card : ℝ) *
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)) := by
                simp only [Finset.sum_const, nsmul_eq_mul, hcard_B₀]
                ring
            _ ≤ (2 : ℝ) ^ B₀.card * (2 : ℝ) ^ K *
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcard_sub (by positivity))
                  (by positivity)
      _ ≤ ((4 : ℝ) ^ K * C_div * C_max * A) *
            Z ^ (F_in + (eps + eps_div * (ell + eta))) * (1 + ‖s_ht‖) ^ (2 * degree) := by
          have h4K : (2 : ℝ) ^ K * (2 : ℝ) ^ K = (4 : ℝ) ^ K := by
            rw [← mul_pow]; norm_num
          have hpow4 : ((2 : ℝ) ^ B₀.card) ^ 3 * (2 : ℝ) ^ B₀.card = ((2 : ℝ) ^ B₀.card) ^ 4 := by
            ring
          calc
            ((2 : ℝ) ^ K * ((2 : ℝ) ^ B₀.card) ^ 3) *
                ((2 : ℝ) ^ B₀.card * (2 : ℝ) ^ K *
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)))
              = ((2 : ℝ) ^ K * (2 : ℝ) ^ K) * (((2 : ℝ) ^ B₀.card) ^ 3 * (2 : ℝ) ^ B₀.card) *
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)) := by ring
            _ ≤ (4 : ℝ) ^ K * (C_div * Z ^ (eps_div * (ell + eta))) *
                  (C_max * A * Z ^ (F_in + eps) * (1 + ‖s_ht‖) ^ (2 * degree)) := by
                rw [h4K, hpow4]
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hdiv_B₀ (by positivity))
                  (by positivity)
            _ = ((4 : ℝ) ^ K * C_div * C_max * A) *
                  (Z ^ (F_in + eps) * Z ^ (eps_div * (ell + eta))) * (1 + ‖s_ht‖) ^ (2 * degree) := by ring
            _ = _ := by
                rw [← Real.rpow_add hz0]
                congr 2; ring
  constructor
  · intro zz d hdcell s_ht J₁ hJ₁ γ hγ
    exact hbranch (secondRayMinus Ψ₀ zz) (hbase₀.secondMinus zz)
      (fun u => (secondRayMinus_norm_le Ψ₀ zz u).trans (hΨ₀1 u))
      ω₁ ω₁_clip af₁ bf₁ C_clip₁ haf₁ hsω₁ hC_clip₁ hbf₁Z (le_max_left _ _)
      (hclip₁ (secondRayMinus Ψ₀ zz)) hm₁ hm₁_c d hdcell s_ht J₁ hJ₁ γ hγ
  · intro zz d hdcell s_ht J₂ hJ₂ γ hγ
    exact hbranch (secondRayPlus Ψ₀ zz) (hbase₀.secondPlus zz)
      (fun u => (secondRayPlus_norm_le Ψ₀ zz u).trans (hΨ₀1 u))
      ω₂ ω₂_clip af₂ bf₂ C_clip₂ haf₂ hsω₂ hC_clip₂ hbf₂Z ((le_max_left _ _).trans (le_max_right _ _))
      (hclip₂ (secondRayPlus Ψ₀ zz)) hm₂ hm₂_c d hdcell s_ht J₂ hJ₂ γ hγ

end Q0StrippedChildBounds

/-! ### Part IV: `4 × 3 = 12` sextic label transfer on `varyingReopenedRow` for tiny cube bins -/

section TinyCubeBinLabelTransfer

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Prime set attached to a tuple `tup : ∀ i : U_free, lists i.val`. -/
def tuplePrimeSet {U_free : Finset σ} {lists : σ → Finset ι}
    (tup : ∀ i : U_free, lists i.val) : Finset ι :=
  (Finset.univ : Finset U_free).image (fun i => (tup i).val)

/-- Tuple coefficient `∏ i : U_free, a i.val (tup i).val`. -/
def tupleCoeff {U_free : Finset σ} {lists : σ → Finset ι}
    (a : σ → ι → ℂ) (tup : ∀ i : U_free, lists i.val) : ℂ :=
  ∏ i : U_free, a i.val (tup i).val

omit [DecidableEq ι] [DecidableEq σ] in
lemma tupleCoeff_norm_le_one {U_free : Finset σ} {lists : σ → Finset ι}
    {a : σ → ι → ℂ} (ha : ∀ i ∈ U_free, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (tup : ∀ i : U_free, lists i.val) :
    ‖tupleCoeff a tup‖ ≤ 1 := by
  unfold tupleCoeff
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun i _ => ha i.val i.property (tup i).val (tup i).property)

omit [DecidableEq ι] [DecidableEq σ] in
/-- Under pairwise disjointness of `lists` on `U_free`, `i ↦ (tup i).val` is injective. -/
lemma tuplePrimeSet_injective {U_free : Finset σ} {lists : σ → Finset ι}
    (hdisj : (U_free : Set σ).PairwiseDisjoint lists)
    (tup : ∀ i : U_free, lists i.val) :
    Function.Injective (fun i : U_free => (tup i).val) := by
  intro i₁ i₂ (heq : (tup i₁).val = (tup i₂).val)
  by_contra hne
  have hdis := hdisj i₁.property i₂.property (fun hv => hne (Subtype.ext hv))
  have hm₂ : (tup i₁).val ∈ lists i₂.val := by rw [heq]; exact (tup i₂).property
  exact Finset.disjoint_left.mp hdis (tup i₁).property hm₂

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma tuplePrimeSet_prod {U_free : Finset σ} {lists : σ → Finset ι}
    (hdisj : (U_free : Set σ).PairwiseDisjoint lists)
    (tup : ∀ i : U_free, lists i.val) :
    ∏ j ∈ tuplePrimeSet tup, p j = ∏ i : U_free, p (tup i).val :=
  Finset.prod_image (fun _ _ _ _ heq => tuplePrimeSet_injective hdisj tup heq)

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- If `primeMark J_hit lists a v.support ≠ 0` and every `q ∈ lists i` (`i ∈ J_hit`) has norm at
least `L_slot i`, then `∏ i ∈ J_hit, L_slot i ≤ ‖ringComplex (primeProduct p v.support v)‖ ^ 2`. -/
lemma primeMark_cube_hit_zero_of_norm_gt
    (J_hit : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (hdisj : (J_hit : Set σ).PairwiseDisjoint lists)
    (L_slot : σ → ℝ) (hL_nonneg : ∀ i ∈ J_hit, 0 ≤ L_slot i)
    (hL : ∀ i ∈ J_hit, ∀ q ∈ lists i, L_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (v : ι →₀ ℕ)
    (hgt : ‖ringComplex (primeProduct p v.support v)‖ ^ 2 < ∏ i ∈ J_hit, L_slot i) :
    primeMark J_hit lists a v.support = 0 := by
  by_contra hne
  unfold primeMark at hne
  have hall : ∀ i ∈ J_hit, ∃ q ∈ lists i, q ∈ v.support := by
    intro i hi
    have hslot_ne : primeSlot (lists i) (a i) v.support ≠ 0 :=
      fun hz => hne (Finset.prod_eq_zero hi hz)
    unfold primeSlot at hslot_ne
    obtain ⟨q, hq_mem, hq_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hslot_ne
    refine ⟨q, hq_mem, ?_⟩
    by_contra hnv
    exact hq_ne (if_neg hnv)
  choose qf hqf_list hqf_supp using hall
  let S_hit : Finset ι := J_hit.attach.image (fun i => qf i.val i.property)
  have hinj_qf : ∀ i₁ ∈ J_hit.attach, ∀ i₂ ∈ J_hit.attach,
      qf i₁.val i₁.property = qf i₂.val i₂.property → i₁ = i₂ := by
    intro i₁ _ i₂ _ heq
    by_contra hne_i
    have hd := hdisj i₁.property i₂.property (fun hv => hne_i (Subtype.ext hv))
    have hm₂ : qf i₁.val i₁.property ∈ lists i₂.val := by
      rw [heq]; exact hqf_list i₂.val i₂.property
    exact Finset.disjoint_left.mp hd (hqf_list i₁.val i₁.property) hm₂
  have hS_sub : S_hit ⊆ v.support := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hqf_supp i.val i.property
  have hdvd : (∏ q ∈ S_hit, p q) ∣ primeProduct p v.support v := by
    calc
      (∏ q ∈ S_hit, p q) ∣ ∏ q ∈ S_hit, p q ^ v q := by
        apply Finset.prod_dvd_prod_of_dvd
        intro q hq
        have hvq : 1 ≤ v q := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (hS_sub hq))
        simpa only [pow_one] using pow_dvd_pow (p q) hvq
      _ ∣ ∏ q ∈ v.support, p q ^ v q :=
        Finset.prod_dvd_prod_of_subset S_hit v.support (fun q => p q ^ v q) hS_sub
  have hpv0 : primeProduct p v.support v ≠ 0 := primeProduct_ne_zero p hp v.support v
  have hle_norm : ‖ringComplex (∏ q ∈ S_hit, p q)‖ ^ 2 ≤ ‖ringComplex (primeProduct p v.support v)‖ ^ 2 :=
    element_norm_le_of_dvd hpv0 hdvd
  have hprod_ge : (∏ i ∈ J_hit, L_slot i) ≤ ‖ringComplex (∏ q ∈ S_hit, p q)‖ ^ 2 := by
    rw [Finset.prod_image hinj_qf, map_prod, norm_prod, ← Finset.prod_pow]
    rw [← Finset.prod_attach J_hit L_slot]
    exact Finset.prod_le_prod (fun i _ => hL_nonneg i.val i.property)
      (fun i _ => hL i.val i.property _ (hqf_list i.val i.property))
  exact not_lt_of_ge (hprod_ge.trans hle_norm) hgt

private lemma sum_comm_vT_Jtup {α β γ : Type*} {δ : γ → Type*} [∀ g, Fintype (δ g)]
    (sQ : Finset α) (sP : Finset β) (sU : Finset γ)
    (F : α → β → ∀ g : γ, δ g → ℂ) :
    (∑ v ∈ sQ, ∑ T ∈ sP, ∑ J ∈ sU, ∑ tup : δ J, F v T J tup) =
      ∑ J ∈ sU, ∑ tup : δ J, ∑ v ∈ sQ, ∑ T ∈ sP, F v T J tup := by
  have h1 : (∑ v ∈ sQ, ∑ T ∈ sP, ∑ J ∈ sU, ∑ tup : δ J, F v T J tup) =
      ∑ v ∈ sQ, ∑ J ∈ sU, ∑ tup : δ J, ∑ T ∈ sP, F v T J tup := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J _
    exact Finset.sum_comm
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  exact Finset.sum_comm

include hp hcop hg in
/-- Exact `4 × 3 = 12` sextic-invariance label transfer on `varyingReopenedRow`:
for `U_cand ⊆ slots`, expanding `U_cand` into hit subsets `J_hit ⊆ U_cand` of `v.support` and
miss-branch tuples `tup : ∀ i : U_cand \ J_hit, lists i.val` shifts `z ↦ (∏ j ∈ V_tup, p j)^4 * z`
and `X ↦ X / primeProductNorm p V_tup` while keeping `∑ v ∈ Q` coherent inside `varyingReopenedRow`! -/
theorem varyingReopenedRow_sextic_label_transfer
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ_pool : ∀ v ∈ Q, v.support ⊆ pool)
    (β : (ι →₀ ℕ) → ℂ) (n_cube : (ι →₀ ℕ) → ℝ)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (X : ℝ)
    (slots U_cand : Finset σ) (hU : U_cand ⊆ slots)
    (lists : σ → Finset ι) (hlists_pool : ∀ i ∈ slots, lists i ⊆ pool)
    (hdisj : (slots : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) :
    varyingReopenedRow p hg pool Q β Ψ m f
        (fun v T => primeMark slots lists a (T ∪ v.support) *
          W (primeProductNorm p T / (X / n_cube v))) z =
      ∑ J_hit ∈ U_cand.powerset,
        ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
          (tupleCoeff a tup *
            secondPreColumn p hg Ψ m f 1 1 z (fun _ => 1) (tuplePrimeSet tup)) *
          varyingReopenedRow p hg pool Q
            (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                primeMark J_hit lists a v.support * β v else 0)
            Ψ m f
            (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
              W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
            ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) := by
  have hcop_elem : Pairwise (Function.onFun IsCoprime p) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)
  have hp1 (T : Finset ι) :
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T 1 = 1 := by
    simp [primeSubsetRow]
  -- Step 1: Expand primeMark U_cand on each (v, T)
  have hmark_split (v : ι →₀ ℕ) (T : Finset ι) :
      primeMark slots lists a (T ∪ v.support) =
        ∑ J_hit ∈ U_cand.powerset,
          primeMark J_hit lists a v.support *
          ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
            tupleCoeff a tup *
            (if Disjoint (tuplePrimeSet tup) v.support ∧ tuplePrimeSet tup ⊆ T then 1 else 0) *
            primeMark (slots \ U_cand) lists a (T ∪ v.support) := by
    have hslots_union : slots = U_cand ∪ (slots \ U_cand) := (Finset.union_sdiff_of_subset hU).symm
    have hslots_disj : Disjoint U_cand (slots \ U_cand) := Finset.disjoint_sdiff
    have hpm_u : primeMark slots lists a (T ∪ v.support) =
        primeMark U_cand lists a (T ∪ v.support) * primeMark (slots \ U_cand) lists a (T ∪ v.support) := by
      unfold primeMark
      rw [hslots_union, Finset.prod_union hslots_disj]
      rw [← hslots_union]
    rw [hpm_u]
    have hslot_add (i : σ) :
        primeSlot (lists i) (a i) (T ∪ v.support) =
          primeSlot (lists i) (a i) v.support +
            ∑ q ∈ lists i, if q ∉ v.support ∧ q ∈ T then a i q else 0 := by
      unfold primeSlot
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hqv : q ∈ v.support
      · simp [hqv]
      · by_cases hqT : q ∈ T <;> simp [hqv, hqT]
    have hprod_U : primeMark U_cand lists a (T ∪ v.support) =
        ∑ J_hit ∈ U_cand.powerset,
          primeMark J_hit lists a v.support *
            ∏ i ∈ U_cand \ J_hit, (∑ q ∈ lists i, if q ∉ v.support ∧ q ∈ T then a i q else 0) := by
      unfold primeMark
      calc
        (∏ i ∈ U_cand, primeSlot (lists i) (a i) (T ∪ v.support))
          = ∏ i ∈ U_cand, (primeSlot (lists i) (a i) v.support +
              ∑ q ∈ lists i, if q ∉ v.support ∧ q ∈ T then a i q else 0) :=
            Finset.prod_congr rfl (fun i _ => hslot_add i)
        _ = ∑ J_hit ∈ U_cand.powerset,
              (∏ i ∈ J_hit, primeSlot (lists i) (a i) v.support) *
                ∏ i ∈ U_cand \ J_hit, (∑ q ∈ lists i, if q ∉ v.support ∧ q ∈ T then a i q else 0) := by
            rw [Finset.prod_add]
    rw [hprod_U, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J_hit _
    let U_free := U_cand \ J_hit
    have hpi_sum :
        (∏ i ∈ U_free, ∑ q ∈ lists i, if q ∉ v.support ∧ q ∈ T then a i q else 0) =
          ∑ tup : (∀ i : U_free, lists i.val),
            tupleCoeff a tup *
              (if Disjoint (tuplePrimeSet tup) v.support ∧ tuplePrimeSet tup ⊆ T then 1 else 0) := by
      rw [← Finset.prod_coe_sort U_free]
      have hinner (i : U_free) :
          (∑ q ∈ lists i.val, if q ∉ v.support ∧ q ∈ T then a i.val q else 0) =
            ∑ q : lists i.val, if q.val ∉ v.support ∧ q.val ∈ T then a i.val q.val else 0 :=
        (Finset.sum_coe_sort (lists i.val) _).symm
      simp_rw [hinner]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro tup _
      have hcond_iff : (∀ i : U_free, (tup i).val ∉ v.support ∧ (tup i).val ∈ T) ↔
          (Disjoint (tuplePrimeSet tup) v.support ∧ tuplePrimeSet tup ⊆ T) := by
        simp only [tuplePrimeSet, Finset.disjoint_left, Finset.subset_iff,
          Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
        exact forall_and
      by_cases hc_all : ∀ i : U_free, (tup i).val ∉ v.support ∧ (tup i).val ∈ T
      · rw [if_pos (hcond_iff.mp hc_all), mul_one]
        unfold tupleCoeff
        exact Finset.prod_congr rfl (fun i _ => if_pos (hc_all i))
      · rw [if_neg (fun h => hc_all (hcond_iff.mpr h)), mul_zero]
        push Not at hc_all
        obtain ⟨i₀, hi₀⟩ := hc_all
        apply Finset.prod_eq_zero (Finset.mem_univ i₀)
        exact if_neg (by tauto)
    rw [hpi_sum, mul_assoc, Finset.sum_mul]
  -- Step 2: Substitute hmark_split into varyingReopenedRow and commute sums
  rw [varyingReopenedRow_integrand]
  calc
    (∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow p hg pool v z ^ 3 *
          canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z) *
        (primeMark slots lists a (T ∪ v.support) * W (primeProductNorm p T / (X / n_cube v))))
      = ∑ J_hit ∈ U_cand.powerset,
          ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
            tupleCoeff a tup *
            ∑ v ∈ Q, if Disjoint (tuplePrimeSet tup) v.support then
              (primeMark J_hit lists a v.support * β v) *
              multiplicityRow p hg pool v z ^ 3 *
              ∑ T ∈ pool.powerset,
                if tuplePrimeSet tup ⊆ T then
                  secondChildColumn p hg Ψ m f z (fun _ => 1) T *
                  (primeMark (slots \ U_cand) lists a (T ∪ v.support) *
                    W (primeProductNorm p T / (X / n_cube v)))
                else 0
            else 0 := by
        have hstep1 :
            (∑ v ∈ Q, ∑ T ∈ pool.powerset,
              β v * (multiplicityRow p hg pool v z ^ 3 *
                canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
                primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z) *
              (primeMark slots lists a (T ∪ v.support) * W (primeProductNorm p T / (X / n_cube v)))) =
            ∑ v ∈ Q, ∑ T ∈ pool.powerset, ∑ J_hit ∈ U_cand.powerset,
              ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
                β v * (multiplicityRow p hg pool v z ^ 3 *
                  canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
                  primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z) *
                (primeMark J_hit lists a v.support *
                  (tupleCoeff a tup *
                    (if Disjoint (tuplePrimeSet tup) v.support ∧ tuplePrimeSet tup ⊆ T then 1 else 0) *
                    primeMark (slots \ U_cand) lists a (T ∪ v.support)) *
                  W (primeProductNorm p T / (X / n_cube v))) := by
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro T _
          rw [hmark_split v T]
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [hstep1, sum_comm_vT_Jtup]
        apply Finset.sum_congr rfl
        intro J_hit _
        apply Finset.sum_congr rfl
        intro tup _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hdv : Disjoint (tuplePrimeSet tup) v.support
        · rw [if_pos hdv, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          by_cases hsubT : tuplePrimeSet tup ⊆ T
          · simp only [hdv, hsubT, and_self, ↓reduceIte, canonicalSourceCoefficient, secondChildColumn]
            ring
          · simp [hdv, hsubT]
        · rw [if_neg hdv, mul_zero]
          apply Finset.sum_eq_zero
          intro T _
          simp [hdv]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro J_hit _
        apply Finset.sum_congr rfl
        intro tup _
        let U_free := U_cand \ J_hit
        let V_tup := tuplePrimeSet tup
        have hU_free_sub : U_free ⊆ slots := Finset.sdiff_subset.trans hU
        have hV_pool : V_tup ⊆ pool := by
          intro q hq
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
          exact hlists_pool i.val (hU_free_sub i.property) (tup i).property
        have hdisj_rem : ∀ i ∈ slots \ U_cand, Disjoint (lists i) V_tup := by
          intro i hi
          rw [Finset.disjoint_left]
          intro q hq_i hq_V
          obtain ⟨j, _, hqj⟩ := Finset.mem_image.mp hq_V
          have hij_ne : i ≠ j.val := fun he =>
            (Finset.mem_sdiff.mp hi).2 (he ▸ (Finset.mem_sdiff.mp j.property).1)
          have hm_j : q ∈ lists j.val := by rw [← hqj]; exact (tup j).property
          exact Finset.disjoint_left.mp
            (hdisj (Finset.mem_sdiff.mp hi).1 (hU_free_sub j.property) hij_ne)
            hq_i hm_j
        -- Rewrite inner v-sum to match varyingReopenedRow at ((∏ j ∈ V_tup, p j)^4 * z)
        rw [varyingReopenedRow_integrand]
        rw [mul_assoc (tupleCoeff a tup)]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hvQ
        by_cases hdv : Disjoint V_tup v.support
        · have hdv' : Disjoint (tuplePrimeSet tup) v.support := hdv
          rw [if_pos hdv, if_pos hdv']
          -- Transform T-sum by reindexing T = V_tup ∪ N, restoring pool, and transferring label -> z
          have hT_eq :
              (∑ T ∈ pool.powerset,
                if V_tup ⊆ T then
                  secondChildColumn p hg Ψ m f z (fun _ => 1) T *
                  (primeMark (slots \ U_cand) lists a (T ∪ v.support) *
                    W (primeProductNorm p T / (X / n_cube v)))
                else 0) =
              secondPreColumn p hg Ψ m f 1 1 z (fun _ => 1) V_tup *
                ∑ N ∈ pool.powerset,
                  secondChildColumn p hg Ψ m f ((∏ j ∈ V_tup, p j) ^ 4 * z)
                    (fun _ => 1) N *
                  (primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                    W (primeProductNorm p N / ((X / primeProductNorm p V_tup) / n_cube v))) := by
            rw [sum_powerset_filter_subset_eq pool V_tup hV_pool]
            have hN_term (N : Finset ι) (hN : N ∈ (pool \ V_tup).powerset) :
                secondChildColumn p hg Ψ m f z (fun _ => 1) (V_tup ∪ N) *
                  (primeMark (slots \ U_cand) lists a ((V_tup ∪ N) ∪ v.support) *
                    W (primeProductNorm p (V_tup ∪ N) / (X / n_cube v))) =
                secondPreColumn p hg Ψ m f 1 1 z (fun _ => 1) V_tup *
                  secondChildColumn p hg Ψ m (f * ∏ j ∈ V_tup, p j) z
                    (fun U => primeMark (slots \ U_cand) lists a (U ∪ v.support) *
                      W (primeProductNorm p U / ((X / primeProductNorm p V_tup) / n_cube v))) N := by
              have hdVN : Disjoint V_tup N := Finset.disjoint_left.mpr
                (fun i hiV hiN => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiV)
              have hp0 := secondPreColumn_union p hg hp hcop_elem hpr Ψ m 1 f 1 1 z (fun _ => 1) V_tup N hdVN
              have eqL : secondPreColumn p hg Ψ (m * (1 * 1)) f 1 1 z (fun _ => 1) (V_tup ∪ N) =
                  secondChildColumn p hg Ψ m f z (fun _ => 1) (V_tup ∪ N) := by
                simp only [secondPreColumn, secondChildColumn, mul_one, hp1, star_one]
              rw [← eqL, hp0]
              simp only [mul_one, one_mul]
              -- Disjointness of lists (slots \ U_cand) from V_tup removes V_tup from primeMark
              have hpm_eq : primeMark (slots \ U_cand) lists a ((V_tup ∪ N) ∪ v.support) =
                  primeMark (slots \ U_cand) lists a (N ∪ v.support) := by
                unfold primeMark
                apply Finset.prod_congr rfl
                intro i hi
                unfold primeSlot
                apply Finset.sum_congr rfl
                intro q hqL
                have hqV : q ∉ V_tup := Finset.disjoint_left.mp (hdisj_rem i hi) hqL
                simp only [Finset.mem_union, hqV, false_or]
              have hscale_eq : primeProductNorm p (V_tup ∪ N) / (X / n_cube v) =
                  primeProductNorm p N / ((X / primeProductNorm p V_tup) / n_cube v) := by
                rw [primeProductNorm_union p V_tup N hdVN]
                have hpV_ne : primeProductNorm p V_tup ≠ 0 := (primeProductNorm_pos p hp V_tup).ne'
                field_simp [hpV_ne]
              rw [hpm_eq, hscale_eq]
              unfold secondChildColumn
              ring
            rw [Finset.sum_congr rfl hN_term, ← Finset.mul_sum]
            congr 1
            -- Restore pool \ V_tup to pool at label f * ∏ j ∈ V_tup, p j, then transfer to z
            have hkill : ∀ i ∈ V_tup, m * (f * ∏ j ∈ V_tup, p j) ∈ Ideal.span {p i} := fun i hi =>
              Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) f) m)
            have hrestore := fixedChildRow_restore_killed_pool p hg pool V_tup Ψ m (f * ∏ j ∈ V_tup, p j) z
              (fun U => primeMark (slots \ U_cand) lists a (U ∪ v.support) *
                W (primeProductNorm p U / ((X / primeProductNorm p V_tup) / n_cube v))) hkill
            unfold fixedChildRow at hrestore
            rw [hrestore]
            apply Finset.sum_congr rfl
            intro N _
            rw [mul_comm f (∏ j ∈ V_tup, p j), secondChildColumn_label_transfer p hg Ψ m (∏ j ∈ V_tup, p j) f z]
            unfold secondChildColumn
            ring
          -- Apply 4 × 3 = 12 sextic invariance to multiplicityRow ... v z ^ 3
          have hmult : multiplicityRow p hg pool v z ^ 3 =
              multiplicityRow p hg pool v ((∏ j ∈ V_tup, p j) ^ 4 * z) ^ 3 := by
            symm
            apply multiplicityRow_cube_fourth_power_invariant p hcop hg pool V_tup v z
            intro i _ hvi hiV
            exact Finset.disjoint_left.mp hdv hiV (Finsupp.mem_support_iff.mpr hvi)
          rw [hT_eq, hmult]
          dsimp only [V_tup]
          simp only [Finset.mul_sum, canonicalSourceCoefficient, secondChildColumn, one_mul, mul_one]
          apply Finset.sum_congr rfl
          intro N _
          ring
        · have hdv' : ¬ Disjoint (tuplePrimeSet tup) v.support := hdv
          rw [if_neg hdv, if_neg hdv']
          simp only [zero_mul, mul_zero, Finset.sum_const_zero]

omit [DecidableEq ι] [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- Shifting `z ↦ g * z` (`g ≠ 0`) inside `rowFamilyEnergy` at radius `K` is bounded by
`rowFamilyEnergy` at radius `K' ≥ 2 * ‖ringComplex g‖ ^ 2 * K`. -/
theorem rowFamilyEnergy_shift_mul
    (labels : Finset (Ideal O)) (P : Ideal O → O → ℂ)
    {g : O} (hg0 : g ≠ 0) {K K' : ℝ} (hK : 0 < K)
    (hK' : 2 * ‖ringComplex g‖ ^ 2 * K ≤ K') :
    rowFamilyEnergy labels (fun I z => P I (g * z)) K ≤
      rowFamilyEnergy labels P K' := by
  have hg_one : 1 ≤ ‖ringComplex g‖ ^ 2 := SchwartzPlanePoisson.one_le_eisenstein_norm_sq g hg0
  have hK'_pos : 0 < K' := (by nlinarith [hg_one, hK] : 0 < 2 * ‖ringComplex g‖ ^ 2 * K).trans_le hK'
  rw [rowFamilyEnergy_eq_sum labels _ K hK, rowFamilyEnergy_eq_sum labels P K' hK'_pos]
  apply Finset.sum_le_sum
  intro I _
  let D₀ := (firstFrequencyDisk (2 * K)).erase 0
  let D₁ := (firstFrequencyDisk (2 * K')).erase 0
  have hmap_mem : ∀ z ∈ D₀, g * z ∈ D₁ := by
    intro z hz
    obtain ⟨hz0, hz_disk⟩ := Finset.mem_erase.mp hz
    have hznorm : ‖ringComplex z‖ ^ 2 ≤ 2 * K :=
      (CanonicalLogEnergy.mem_firstFrequencyDisk (2 * K) z).mp hz_disk
    refine Finset.mem_erase.mpr ⟨mul_ne_zero hg0 hz0, ?_⟩
    apply (CanonicalLogEnergy.mem_firstFrequencyDisk (2 * K') (g * z)).mpr
    rw [map_mul, norm_mul, mul_pow]
    calc
      ‖ringComplex g‖ ^ 2 * ‖ringComplex z‖ ^ 2
        ≤ ‖ringComplex g‖ ^ 2 * (2 * K) :=
          mul_le_mul_of_nonneg_left hznorm (sq_nonneg _)
      _ = 2 * ‖ringComplex g‖ ^ 2 * K := by ring
      _ ≤ K' := hK'
      _ ≤ 2 * K' := by linarith [hK'_pos]
  have hterm_le : ∀ z ∈ D₀,
      (rowMajorant (‖ringComplex z‖ ^ 2 / K)).re * ‖P I (g * z)‖ ^ 2 ≤
        (rowMajorant (‖ringComplex (g * z)‖ ^ 2 / K')).re * ‖P I (g * z)‖ ^ 2 := by
    intro z hz
    obtain ⟨_hz0, hz_disk⟩ := Finset.mem_erase.mp hz
    have hznorm : ‖ringComplex z‖ ^ 2 ≤ 2 * K :=
      (CanonicalLogEnergy.mem_firstFrequencyDisk (2 * K) z).mp hz_disk
    have hle1 : (rowMajorant (‖ringComplex z‖ ^ 2 / K)).re ≤ 1 := by
      change sieveBump (‖ringComplex z‖ ^ 2 / K) ≤ 1
      exact sieveBump.le_one
    have hratio1 : ‖ringComplex (g * z)‖ ^ 2 / K' ≤ 1 := by
      apply (div_le_one hK'_pos).mpr
      rw [map_mul, norm_mul, mul_pow]
      calc
        ‖ringComplex g‖ ^ 2 * ‖ringComplex z‖ ^ 2
          ≤ ‖ringComplex g‖ ^ 2 * (2 * K) :=
            mul_le_mul_of_nonneg_left hznorm (sq_nonneg _)
        _ = 2 * ‖ringComplex g‖ ^ 2 * K := by ring
        _ ≤ K' := hK'
    have heq1 : (rowMajorant (‖ringComplex (g * z)‖ ^ 2 / K')).re = 1 := by
      rw [rowMajorant_one _ (div_nonneg (sq_nonneg _) hK'_pos.le) hratio1, Complex.one_re]
    rw [heq1]
    exact mul_le_mul_of_nonneg_right hle1 (sq_nonneg _)
  calc
    (∑ z ∈ D₀, (rowMajorant (‖ringComplex z‖ ^ 2 / K)).re * ‖P I (g * z)‖ ^ 2)
      ≤ ∑ z ∈ D₀, (rowMajorant (‖ringComplex (g * z)‖ ^ 2 / K')).re * ‖P I (g * z)‖ ^ 2 :=
        Finset.sum_le_sum hterm_le
    _ = ∑ w ∈ D₀.image (fun z => g * z), (rowMajorant (‖ringComplex w‖ ^ 2 / K')).re * ‖P I w‖ ^ 2 :=
        (Finset.sum_image (fun _ _ _ _ he => mul_left_cancel₀ hg0 he)).symm
    _ ≤ ∑ w ∈ D₁, (rowMajorant (‖ringComplex w‖ ^ 2 / K')).re * ‖P I w‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          exact hmap_mem z hz
        · intro w _ _
          exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

private lemma sum_comm_four {α β γ : Type*} {δ : γ → Type*} [∀ g, Fintype (δ g)]
    (sI : Finset α) (sD : Finset β) (sJ : Finset γ)
    (w : β → ℝ) (c0 : ℝ) (c : γ → ℝ) (F : ∀ g : γ, δ g → α → β → ℝ) :
    (∑ I ∈ sI, ∑ z ∈ sD, w z * (c0 * ∑ J ∈ sJ, c J * ∑ tup : δ J, F J tup I z)) =
      c0 * ∑ J ∈ sJ, c J * ∑ tup : δ J, ∑ I ∈ sI, ∑ z ∈ sD, w z * F J tup I z := by
  have h1 : (∑ I ∈ sI, ∑ z ∈ sD, w z * (c0 * ∑ J ∈ sJ, c J * ∑ tup : δ J, F J tup I z)) =
      ∑ I ∈ sI, ∑ J ∈ sJ, ∑ tup : δ J, c0 * (c J * ∑ z ∈ sD, w z * F J tup I z) := by
    apply Finset.sum_congr rfl
    intro I _
    calc
      (∑ z ∈ sD, w z * (c0 * ∑ J ∈ sJ, c J * ∑ tup : δ J, F J tup I z))
        = ∑ z ∈ sD, ∑ J ∈ sJ, ∑ tup : δ J, c0 * (c J * (w z * F J tup I z)) := by
            apply Finset.sum_congr rfl
            intro z _
            simp only [Finset.mul_sum, mul_assoc, mul_left_comm]
      _ = ∑ J ∈ sJ, ∑ z ∈ sD, ∑ tup : δ J, c0 * (c J * (w z * F J tup I z)) := Finset.sum_comm
      _ = ∑ J ∈ sJ, ∑ tup : δ J, ∑ z ∈ sD, c0 * (c J * (w z * F J tup I z)) :=
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ J ∈ sJ, ∑ tup : δ J, c0 * (c J * ∑ z ∈ sD, w z * F J tup I z) := by
            apply Finset.sum_congr rfl
            intro J _
            apply Finset.sum_congr rfl
            intro tup _
            simp only [Finset.mul_sum]
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tup _
  simp only [Finset.mul_sum]

include hp hcop hg in
/-- Energy bound for `varyingReopenedRow` under `4 × 3 = 12` sextic label transfer:
vanishing all `J_hit` whose slot lower-norm product exceeds `B_cube` and applying Cauchy-Schwarz
over surviving `J_hit` and `tup : ∀ i : U_cand \ J_hit, lists i.val` bounds `rowFamilyEnergy` at
`K` by a sum of `rowFamilyEnergy` terms at `K'_tup` and column scale `X / primeProductNorm p V_tup`. -/
theorem rowFamilyEnergy_sextic_label_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ_pool : ∀ v ∈ Q, v.support ⊆ pool)
    (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n_cube : (ι →₀ ℕ) → ℝ)
    (Ψ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (W : ℝ → ℂ) (X K_rad : ℝ) (hK_rad : 0 < K_rad)
    (slots U_cand : Finset σ) (hU : U_cand ⊆ slots)
    (lists : σ → Finset ι) (hlists_pool : ∀ i ∈ slots, lists i ⊆ pool)
    (hdisj : (slots : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ slots, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (L_slot : σ → ℝ) (B_cube : ℝ)
    (hL_nonneg : ∀ i ∈ U_cand, 0 ≤ L_slot i)
    (hL_bound : ∀ i ∈ U_cand, ∀ q ∈ lists i, L_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (hQ_B : ∀ v ∈ Q, ‖ringComplex (primeProduct p v.support v)‖ ^ 2 ≤ B_cube)
    (K_out : ∀ J_hit : Finset σ, (∀ i : (U_cand \ J_hit : Finset σ), lists i.val) → ℝ)
    (hK_out : ∀ J_hit ∈ U_cand.powerset.filter (fun J => ∏ i ∈ J, L_slot i ≤ B_cube),
      ∀ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
        2 * (primeProductNorm p (tuplePrimeSet tup)) ^ 4 * K_rad ≤ K_out J_hit tup) :
    let validHits := U_cand.powerset.filter (fun J_hit => ∏ i ∈ J_hit, L_slot i ≤ B_cube)
    rowFamilyEnergy labels
        (fun I z => varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
          (fun v T => primeMark slots lists a (T ∪ v.support) *
            W (primeProductNorm p T / (X / n_cube v))) z) K_rad ≤
      (validHits.card : ℝ) * ∑ J_hit ∈ validHits,
        (∏ i ∈ U_cand \ J_hit, ((lists i).card : ℝ)) *
          ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
            rowFamilyEnergy labels
              (fun I z' => varyingReopenedRow p hg pool Q
                (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                    primeMark J_hit lists a v.support * β I v else 0)
                Ψ m (cubicIdealGenerator I)
                (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                  W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
                z') (K_out J_hit tup) := by
  intro validHits
  -- Pointwise norm-squared bound for each (I, z)
  have hpt (I : Ideal O) (z : O) :
      ‖varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
          (fun v T => primeMark slots lists a (T ∪ v.support) *
            W (primeProductNorm p T / (X / n_cube v))) z‖ ^ 2 ≤
        (validHits.card : ℝ) * ∑ J_hit ∈ validHits,
          (∏ i ∈ U_cand \ J_hit, ((lists i).card : ℝ)) *
            ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
              ‖varyingReopenedRow p hg pool Q
                (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                    primeMark J_hit lists a v.support * β I v else 0)
                Ψ m (cubicIdealGenerator I)
                (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                  W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
                ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2 := by
    rw [varyingReopenedRow_sextic_label_transfer p hp hcop hg hpr pool Q hQ_pool (β I) n_cube
      Ψ m (cubicIdealGenerator I) z W X slots U_cand hU lists hlists_pool hdisj a]
    -- Restrict U_cand.powerset to validHits
    have hrestrict :
        (∑ J_hit ∈ U_cand.powerset,
          ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
            (tupleCoeff a tup *
              secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)) *
            varyingReopenedRow p hg pool Q
              (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                  primeMark J_hit lists a v.support * β I v else 0)
              Ψ m (cubicIdealGenerator I)
              (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
              ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)) =
        ∑ J_hit ∈ validHits,
          ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
            (tupleCoeff a tup *
              secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)) *
            varyingReopenedRow p hg pool Q
              (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                  primeMark J_hit lists a v.support * β I v else 0)
              Ψ m (cubicIdealGenerator I)
              (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
              ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro J_hit hJp hnot
      have hgt_B : B_cube < ∏ i ∈ J_hit, L_slot i := by
        by_contra hle
        exact hnot (Finset.mem_filter.mpr ⟨hJp, not_lt.mp hle⟩)
      have hJU : J_hit ⊆ U_cand := Finset.mem_powerset.mp hJp
      apply Finset.sum_eq_zero
      intro tup _
      have hcoef0 : (fun v => if Disjoint (tuplePrimeSet tup) v.support then
          primeMark J_hit lists a v.support * β I v else 0) = (fun v => if v ∈ Q then 0 else
            if Disjoint (tuplePrimeSet tup) v.support then primeMark J_hit lists a v.support * β I v else 0) := by
        funext v
        by_cases hvQ : v ∈ Q
        · rw [if_pos hvQ]
          have hpm0 := primeMark_cube_hit_zero_of_norm_gt p hp J_hit lists a
            (fun i hi j hj hij => hdisj (hU (hJU hi)) (hU (hJU hj)) hij)
            L_slot (fun i hi => hL_nonneg i (hJU hi))
            (fun i hi => hL_bound i (hJU hi)) v ((hQ_B v hvQ).trans_lt hgt_B)
          simp [hpm0]
        · rw [if_neg hvQ]
      have hrow0 : varyingReopenedRow p hg pool Q
          (fun v => if Disjoint (tuplePrimeSet tup) v.support then
              primeMark J_hit lists a v.support * β I v else 0)
          Ψ m (cubicIdealGenerator I)
          (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
            W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
          ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z) = 0 := by
        rw [varyingReopenedRow_integrand]
        apply Finset.sum_eq_zero
        intro v hvQ
        have hpm0 := primeMark_cube_hit_zero_of_norm_gt p hp J_hit lists a
          (fun i hi j hj hij => hdisj (hU (hJU hi)) (hU (hJU hj)) hij)
          L_slot (fun i hi => hL_nonneg i (hJU hi))
          (fun i hi => hL_bound i (hJU hi)) v ((hQ_B v hvQ).trans_lt hgt_B)
        simp [hpm0]
      rw [hrow0, mul_zero]
    rw [hrestrict]
    apply (norm_sum_sq_le_card_sum_norm_sq validHits _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro J_hit _
    let U_free := U_cand \ J_hit
    have hU_free_sub : U_free ⊆ slots := Finset.sdiff_subset.trans hU
    apply (norm_sum_sq_le_card_sum_norm_sq Finset.univ _).trans
    have hcard_tup : ((Finset.univ : Finset (∀ i : U_free, lists i.val)).card : ℝ) =
        ∏ i ∈ U_free, ((lists i).card : ℝ) := by
      rw [Finset.card_univ, Fintype.card_pi, Finset.prod_coe_sort]
      simp [Nat.cast_prod]
    rw [hcard_tup]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    apply Finset.sum_le_sum
    intro tup _
    have htc := tupleCoeff_norm_le_one (fun i hi => ha i (hU_free_sub hi)) tup
    have hpre : ‖secondPreColumn p hg Ψ m (cubicIdealGenerator I) 1 1 z (fun _ => 1) (tuplePrimeSet tup)‖ ≤ 1 := by
      have hh := supportMobius_secondPreColumn_norm_le_one p hp hg hinj hc Ψ hΨ1
        m (cubicIdealGenerator I) z (tuplePrimeSet tup)
      rwa [norm_mul, supportMobius_norm, one_mul] at hh
    rw [norm_mul, mul_pow]
    exact (mul_le_of_le_one_left (sq_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (by rw [norm_mul]; exact (mul_le_mul htc hpre (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))).trans (le_refl _)
  -- Sum hpt over labels and firstFrequencyDisk, commute sums, and apply rowFamilyEnergy_shift_mul
  rw [rowFamilyEnergy_eq_sum labels _ K_rad hK_rad]
  let D₀ := (firstFrequencyDisk (2 * K_rad)).erase 0
  calc
    (∑ I ∈ labels, ∑ z ∈ D₀,
        (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
          ‖varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
            (fun v T => primeMark slots lists a (T ∪ v.support) *
              W (primeProductNorm p T / (X / n_cube v))) z‖ ^ 2)
      ≤ ∑ I ∈ labels, ∑ z ∈ D₀,
          (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re *
            ((validHits.card : ℝ) * ∑ J_hit ∈ validHits,
              (∏ i ∈ U_cand \ J_hit, ((lists i).card : ℝ)) *
                ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
                  ‖varyingReopenedRow p hg pool Q
                    (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                        primeMark J_hit lists a v.support * β I v else 0)
                    Ψ m (cubicIdealGenerator I)
                    (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                      W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
                    ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)‖ ^ 2) :=
        Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
          (fun z _ => mul_le_mul_of_nonneg_left (hpt I z) (rowMajorant_nonneg _)))
    _ = (validHits.card : ℝ) * ∑ J_hit ∈ validHits,
          (∏ i ∈ U_cand \ J_hit, ((lists i).card : ℝ)) *
            ∑ tup : (∀ i : (U_cand \ J_hit : Finset σ), lists i.val),
              rowFamilyEnergy labels
                (fun I z => varyingReopenedRow p hg pool Q
                  (fun v => if Disjoint (tuplePrimeSet tup) v.support then
                      primeMark J_hit lists a v.support * β I v else 0)
                  Ψ m (cubicIdealGenerator I)
                  (fun v N => primeMark (slots \ U_cand) lists a (N ∪ v.support) *
                    W (primeProductNorm p N / ((X / primeProductNorm p (tuplePrimeSet tup)) / n_cube v)))
                  ((∏ j ∈ tuplePrimeSet tup, p j) ^ 4 * z)) K_rad := by
        rw [sum_comm_four labels D₀ validHits
          (fun z => (rowMajorant (‖ringComplex z‖ ^ 2 / K_rad)).re)
          (validHits.card : ℝ)
          (fun J_hit => ∏ i ∈ U_cand \ J_hit, ((lists i).card : ℝ))]
        congr 1
        apply Finset.sum_congr rfl
        intro J_hit _
        congr 1
        apply Finset.sum_congr rfl
        intro tup _
        exact (rowFamilyEnergy_eq_sum labels _ K_rad hK_rad).symm
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro J_hit hJ_hit
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        apply Finset.sum_le_sum
        intro tup _
        let g := (∏ j ∈ tuplePrimeSet tup, p j) ^ 4
        have hg0 : g ≠ 0 := pow_ne_zero 4 (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j))
        have hgnorm : ‖ringComplex g‖ ^ 2 = (primeProductNorm p (tuplePrimeSet tup)) ^ 4 := by
          have h1 : ‖ringComplex (∏ j ∈ tuplePrimeSet tup, p j)‖ ^ 2 = primeProductNorm p (tuplePrimeSet tup) := by
            unfold primeProductNorm
            rw [map_prod, norm_prod, ← Finset.prod_pow]
          dsimp [g]
          rw [map_pow, norm_pow, ← pow_mul, show 4 * 2 = 2 * 4 by decide, pow_mul, h1]
        apply rowFamilyEnergy_shift_mul labels _ hg0 hK_rad
        rw [hgnorm]
        exact hK_out J_hit hJ_hit tup

/-! ### Part V: Finite-sum `parentPoisson` identity and conductor radical bound for tiny bins -/

include hp hg in
/-- Finite-sum formula for `parentPoisson` on `rowMajorantBall Y`: for `y = parent p x`,
`parentPoisson` equals the finite `rowMajorantBall Y` sum of `‖inputConjugateRow‖^2`. -/
theorem parentPoisson_eq_rowMajorantBall_sum
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (x : Source ι Jo) (extra : CubeCoordinates ι → Finset ι)
    (pool : Finset ι) (negative : Bool) (Ψ : O →* ℂ) (m : O)
    (slots J : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (om : 𝓢(ℝ, ℂ)) (lo hi : ℝ) (hlo : 0 < lo) (hs : Function.support om ⊆ Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (ray : RayCharacter × RayCharacter) (core : FirstCoreIndex) :
    let y := parent p x
    let χ_ray := if negative then ray.1 else ray.2
    let Ψ₀ := firstCoreTwist negative χ_ray Ψ core
    let res_lists := residualLists p negative (fun i => lists i \ extra x.cube) y
    let H₀ := markedRadial p (slots \ J) res_lists a ∅ (principalWindow om lo hi hlo hs negative t) X
    parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i => lists i \ extra x.cube)
        a om X t Y ray core y =
      ∑ z ∈ rowMajorantBall Y,
        rowMajorant (‖ringComplex z‖ ^ 2 / Y) *
          (‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
            pool Ψ₀ (secondParentPuncture p m y) (secondParentLabel p y)
            (secondParentDivisor p y) H₀ z‖ ^ 2 : ℝ) := by
  intro y χ_ray Ψ₀ res_lists H₀
  have hD_avoid : ∀ i ∈ slots \ J, Disjoint (res_lists i) (quotientSupport p y) := by
    intro i _
    exact residual_lists_avoid _ _ _ i
  have hq : y.quotient = sourceIdeal p (quotientSupport p y) := by
    change sourceIdeal p x.quotientSupport = sourceIdeal p (quotientSupport p (parent p x))
    rw [quotientSupport_parent p hinj]
  let H_core := firstCoreTest (primeMark (slots \ J) res_lists a) (fun u => om (Real.exp u))
    (columnLog p (primeProductNorm p (quotientSupport p y) * X)) negative (-t) (quotientSupport p y)
  let m₀ := (m * b0Label p y.cube.support
    (fun i => y.cube.leftExponent i + y.cube.rightExponent i)
    y.cube.leftBit y.cube.rightBit) * ∏ i ∈ quotientSupport p y, p i
  have he (z : O) :
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ₀ m₀ (secondParentLabel p y) (secondParentDivisor p y) H_core z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ₀ (secondParentPuncture p m y) (secondParentLabel p y)
        (secondParentDivisor p y) H₀ z := by
    calc
      _ = inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
            pool Ψ₀ m₀ (secondParentLabel p y) (secondParentDivisor p y) H₀ z := by
          unfold inputConjugateRow supportConjugateSum
          apply Finset.sum_congr rfl
          intro U _
          exact firstCoreTest_coefficient p hp hg hinj (slots \ J) res_lists a (quotientSupport p y) U
            hD_avoid om lo hi hlo hs negative X t hX Ψ₀ _ _ _
      _ = _ := fresh_input_parent_mask p hg y pool (quotientSupport p y) hq Ψ₀ m H₀ z
  unfold parentPoisson
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY := hY)]
  rw [← inputConjugateRow_smoothed_second_poisson p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp hinj
    (fun i => complexSexticChar_ne_one _ (hg i)) _ _ _ _ _ _ _ _ hY]
  change (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) *
    (‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      pool Ψ₀ m₀ (secondParentLabel p y) (secondParentDivisor p y) H_core z‖ ^ 2 : ℝ)) = _
  rw [tsum_congr (fun z => by rw [he z])]
  exact rowMajorant_tsum_eq_sum _ Y hY

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- Radical conductor bound for `(secondParentLabel p (parent p x))^4 * secondParentDivisor p (parent p x)`:
every prime dividing `c₀^4 * d` divides `(∏ i ∈ x.firstCommon, p i) * b0Label * jLabel`, so its
radical norm is bounded by `primeProductNorm p x.firstCommon * ‖b0Label‖^2 * ‖jLabel‖^2`! -/
theorem secondParent_conductor_radical_bound
    {Jo : ℕ} (x : Source ι Jo) (hx : SourceValid p x) :
    let y := parent p x
    let c₀ := secondParentLabel p y
    let d := secondParentDivisor p y
    let b₀ := b0Label p x.cube.support
      (fun i => x.cube.leftExponent i + x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    let j₀ := jLabel p x.cube.support
      (fun i => x.cube.leftExponent i + x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    c₀ ^ 4 * d ≠ 0 ∧
      (Ideal.absNorm (Ideal.span {c₀ ^ 4 * d} : Ideal O).radical : ℝ) ≤
        primeProductNorm p x.firstCommon * ‖ringComplex b₀‖ ^ 2 * ‖ringComplex j₀‖ ^ 2 := by
  intro y c₀ d b₀ j₀
  have hc₀_eq : c₀ = (∏ i ∈ x.firstCommon, p i) * j₀ := rfl
  have hd_eq : d = ∏ i ∈ x.firstDivisor, p i := rfl
  have hpC0 : (∏ i ∈ x.firstCommon, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hb₀0 : b₀ ≠ 0 := primeProduct_ne_zero p hp _ _
  have hj₀0 : j₀ ≠ 0 := primeProduct_ne_zero p hp _ _
  have hd0 : d ≠ 0 := by rw [hd_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hc₀0 : c₀ ≠ 0 := by rw [hc₀_eq]; exact mul_ne_zero hpC0 hj₀0
  have hprod0 : c₀ ^ 4 * d ≠ 0 := mul_ne_zero (pow_ne_zero 4 hc₀0) hd0
  refine ⟨hprod0, ?_⟩
  let g := (∏ i ∈ x.firstCommon, p i) * b₀ * j₀
  have hg0 : g ≠ 0 := mul_ne_zero (mul_ne_zero hpC0 hb₀0) hj₀0
  have hIg0 : (Ideal.span {g} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hg0
  -- Every prime dividing c₀ ^ 4 * d divides g, so c₀ ^ 4 * d ∣ g ^ 5 and span {g} ≤ (span {c₀ ^ 4 * d}).radical.
  have hdvd_d : d ∣ (∏ i ∈ x.firstCommon, p i) * (j₀ * b₀) := by
    rw [hd_eq]
    have hd1 : (∏ i ∈ x.firstDivisor, p i) ∣ ∏ i ∈ x.firstCommon ∪ x.cube.support, p i :=
      Finset.prod_dvd_prod_of_subset x.firstDivisor (x.firstCommon ∪ x.cube.support) p hx.first_divisor
    rw [Finset.prod_union hx.common_disjoint] at hd1
    have hd2 : (∏ i ∈ x.cube.support, p i) ∣ j₀ * b₀ :=
      cubeRadical_dvd_jLabel_b0 p x.cube.support
        (fun i => x.cube.leftExponent i + x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit x.cube.support_pos
    exact hd1.trans (mul_dvd_mul_left _ hd2)
  have hdvd_c : c₀ ∣ g := by
    dsimp [g]
    rw [hc₀_eq]
    exact ⟨b₀, by ring⟩
  have hdvd_g5 : c₀ ^ 4 * d ∣ g ^ 5 := by
    have hd_g : d ∣ g := hdvd_d.trans ⟨1, by dsimp [g]; ring⟩
    calc c₀ ^ 4 * d ∣ g ^ 4 * g := mul_dvd_mul (pow_dvd_pow_of_dvd hdvd_c 4) hd_g
      _ = g ^ 5 := by ring
  have hle_rad : (Ideal.span {g} : Ideal O) ≤ (Ideal.span {c₀ ^ 4 * d} : Ideal O).radical := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨5, Ideal.mem_span_singleton.mpr hdvd_g5⟩
  have hnat : Ideal.absNorm (Ideal.span {c₀ ^ 4 * d} : Ideal O).radical ≤
      Ideal.absNorm (Ideal.span {g} : Ideal O) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hIg0))
      (Ideal.absNorm_dvd_absNorm_of_le hle_rad)
  calc
    (Ideal.absNorm (Ideal.span {c₀ ^ 4 * d} : Ideal O).radical : ℝ)
      ≤ (Ideal.absNorm (Ideal.span {g} : Ideal O) : ℝ) := by exact_mod_cast hnat
    _ = ‖ringComplex g‖ ^ 2 := (ringComplex_norm_sq_eq_absNorm_span g).symm
    _ = primeProductNorm p x.firstCommon * ‖ringComplex b₀‖ ^ 2 * ‖ringComplex j₀‖ ^ 2 := by
        dsimp [g]
        rw [map_mul, map_mul, norm_mul, norm_mul, mul_pow, mul_pow]
        rfl

end TinyCubeBinLabelTransfer

end Stage1CubeBins

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

