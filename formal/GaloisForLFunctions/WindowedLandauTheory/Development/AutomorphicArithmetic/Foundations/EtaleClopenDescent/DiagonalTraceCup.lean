import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalGlobalClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TraceTensorCoefficient
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedLeftCechCup

/-! Pairing the diagonal cocycle with a regular left cocycle gives a
logarithmic cocycle. Its top collapse is the left Čech edge. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V₀" => ExteriorDifferentials k E p
local notation "W₀" => ExteriorDifferentials k E q
local notation "K₀" => ChartPair d ⊕ₗ DiagonalIndex d
local notation "A₀" => (fun J : Finset (Fin (d + 1)) => regularExteriorLattice (rB k E x J) p)

private theorem sum_singleton_prefix {ι M : Type} [LinearOrder ι] [AddCommMonoid M]
    (v : Finset ι → M) (hv : v ∅ = 0) (I : Finset ι) :
    (∑ i ∈ I, if (I.filter (· ≤ i)).card = 1 then v (I.filter (i ≤ ·)) else 0) = v I := by
  by_cases hI : I.Nonempty
  · let i := I.min' hI
    have hi : i ∈ I := Finset.min'_mem _ _
    have hp : I.filter (· ≤ i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun hj => le_antisymm hj.2 (Finset.min'_le _ _ hj.1), ?_⟩
      rintro rfl
      exact ⟨hi, le_rfl⟩
    have hq : I.filter (i ≤ ·) = I :=
      Finset.filter_true_of_mem fun j hj => Finset.min'_le _ _ hj
    rw [Finset.sum_eq_single_of_mem i hi, hp, hq, Finset.card_singleton, if_pos rfl]
    intro j hj hji
    have hne : (I.filter (· ≤ j)).card ≠ 1 := by
      intro he
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp he
      have hi₀ : i ∈ I.filter (· ≤ j) := Finset.mem_filter.mpr ⟨hi, Finset.min'_le _ _ hj⟩
      have hj₀ : j ∈ I.filter (· ≤ j) := Finset.mem_filter.mpr ⟨hj, le_rfl⟩
      rw [hu] at hi₀ hj₀
      exact hji ((Finset.mem_singleton.mp hj₀).trans (Finset.mem_singleton.mp hi₀).symm)
    rw [if_neg hne]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.sum_empty, hv]

private theorem weighted_left_cup_terms {k S E M N : Type}
    [Field k] [CommRing S] [Algebra k S]
    [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {d m : ℕ}
    (T : WeightedChartSystem k d S E) (U : WeightedChartSystem k d S N)
    (A : Finset (Fin (d + 1)) → Submodule k M)
    (n : DiagonalIndex d → ℕ × ℕ) (z : DiagonalIndex d → S)
    (μ : E →ₗ[k] M →ₗ[k] N)
    (c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) → E)
    (a : Finset (Fin (d + 1)) → M)
    (haC : ∀ I, a I = 0 ∨ I.Nonempty ∧ I.card = m + 1 ∧ a I ∈ A I)
    (hcC : ∀ I J L, c (uni (uni I J) L) = 0 ∨
      I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = (d : ℤ) + 2 ∧
        c (uni (uni I J) L) ∈ T.scaledCoefficients n I J L)
    (hcoeff : ∀ {I J P Q L}, P.Nonempty → J.Nonempty → P ⊆ I → Q ⊆ I →
      c (uni (uni P J) L) ∈ T.scaledCoefficients n P J L → a Q ∈ A Q →
      μ (c (uni (uni P J) L)) (a Q) ∈ U.scaledCoefficients n I J L) :
    weightedLeftCup μ m c a ∈ (U.complex n z).C ((d : ℤ) + m + 2) := by
  refine acx_mem_terms_iff.mpr fun s => ?_
  obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  rw [weightedLeftCup_apply, cechCup_apply]
  apply zsmul_mem
  refine Submodule.sum_mem _ fun i hi => ?_
  let P := I.filter (· ≤ i)
  let Q := I.filter (i ≤ ·)
  rcases haC Q with ha₀ | ⟨_, haD, haQ⟩
  · rw [ha₀, map_zero]
    exact zero_mem _
  rcases hcC P J L with hc₀ | ⟨hP, hJ, hcD, hcP⟩
  · rw [hc₀, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  have hPI : P ⊆ I := Finset.filter_subset _ _
  have hI := hP.mono hPI
  have hsum := card_filter_le_add_card_filter_ge I i hi
  have hdeg : ((uni (uni I J) L).card : ℤ) = (d : ℤ) + m + 2 := by
    rw [card_uni, card_uni]
    change P.card + Q.card = I.card + 1 at hsum
    omega
  rw [if_pos hdeg, lft_uni, rgt_uni, mixedCoefficients, lft_uni, rgt_uni, if_pos ⟨hI, hJ⟩]
  exact hcoeff hP hJ hPI (Finset.filter_subset _ _) hcP haQ

/-- The cup preserves the bound on the number of weight indices. -/
theorem weightedLeftCup_level {k E M N : Type} [Field k]
    [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {d m : ℕ}
    (μ : E →ₗ[k] M →ₗ[k] N)
    (c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) → E)
    (a : Finset (Fin (d + 1)) → M)
    (hL : Lev rightIndices (· ≤ (d : ℤ)) c) :
    Lev rightIndices (· ≤ (d : ℤ)) (weightedLeftCup μ m c a) := by
  intro s hnd
  obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  have hcard : (((uni (uni I J) L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
    congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices (uni I J) L)
  have hlt : (d : ℤ) < L.card := lt_of_not_ge (fun h => hnd (hcard.symm ▸ h))
  rw [weightedLeftCup_apply, cechCup_apply]
  apply smul_eq_zero_of_right
  refine Finset.sum_eq_zero fun i _ => ?_
  let P := I.filter (· ≤ i)
  have hp : (((uni (uni P J) L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
    congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices (uni P J) L)
  have he := hL (uni (uni P J) L) (fun h => (not_le_of_gt hlt) (hp ▸ h))
  rw [he, map_zero, LinearMap.zero_apply]

private theorem diagonal_trace_scaled_mem (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    {I J P Q : Finset (Fin (d + 1))} (L : Finset (DiagonalIndex d))
    (hP : P.Nonempty) (hJ : J.Nonempty) (hPI : P ⊆ I) (hQI : Q ⊆ I)
    (w : V₀) (hw : w ∈ A₀ Q) (t : W₀ ⊗[k] V₀) :
    let T := diagonalChartSystem (E := E) h.pd q p
    let U := logarithmicChartSystem (E := E) h.pd p
    let n := fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ)
    t ∈ T.scaledCoefficients n P J L →
    traceWedgeTensorCoefficient (F := F) τ t w ∈ U.scaledCoefficients n I J L := by
  intro T U n ht
  have hc := T.scaledCoefficients_mono (diagonalChartSystem_good (E := E) h.pd q p)
    n hP hJ hPI (by rfl) L ht
  obtain ⟨u, hu, he⟩ := hc
  have hμ := h.traceWedgeTensorCoefficient_mem τ hτ hpq hw hu
  have hIQ : I ∪ Q = I := Finset.union_eq_left.mpr hQI
  rw [hIQ] at hμ
  let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
  refine ⟨μ u w, hμ, ?_⟩
  let s : F ⊗[k] F := ((∏ l ∈ L, U.weightUnit n (chartIndex I) (chartIndex J) l : (F ⊗[k] F)ˣ) : F ⊗[k] F)
  have hu' : T.act s u = t := he
  have hact : μ (T.act s u) w = U.act s (μ u w) :=
    traceWedgeTensorCoefficient_action τ s u w
  exact hact.symm.trans (congrArg (fun t => μ t w) hu')

private theorem weighted_column_term {k S E : Type} [Field k] [CommRing S] [Algebra k S]
    [AddCommGroup E] [Module k E] {d : ℕ}
    (T : WeightedChartSystem k d S E) (n : DiagonalIndex d → ℕ × ℕ) (z : DiagonalIndex d → S)
    {c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) → E} (hc : c ∈ (T.complex n z).C ((d : ℤ) + 2))
    (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d)) :
    c (uni (uni I J) L) = 0 ∨
      I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = (d : ℤ) + 2 ∧
        c (uni (uni I J) L) ∈ T.scaledCoefficients n I J L := by
  have he := acx_mem_terms_iff.mp hc (uni (uni I J) L)
  simp only [card_uni, mixedCoefficients, lft_uni, rgt_uni] at he
  split_ifs at he with hdeg hIJ
  · exact Or.inr ⟨hIJ.1, hIJ.2, hdeg, he⟩
  · exact Or.inl ((Submodule.mem_bot k).mp he)
  · exact Or.inl ((Submodule.mem_bot k).mp he)

/-- The trace cup of diagonal and Čech cocycles is a logarithmic cocycle. -/
theorem IsFinCover.traceCup_diagonal_mem_cycles (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d) {m : ℕ}
    {c : Finset K₀ → W₀ ⊗[k] V₀} {a : Finset (Fin (d + 1)) → V₀}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2))
    (ha : a ∈ (cech A₀).Z (m : ℤ)) :
    let U := logarithmicChartSystem (E := E) h.pd p
    weightedLeftCup (traceWedgeTensorCoefficient (F := F) τ) m c a ∈
      (U.complex (fun _ => (1, 1)) U.homogeneousMinor).Z ((d : ℤ) + m + 2) := by
  intro U
  let T := diagonalChartSystem (E := E) h.pd q p
  let z := T.homogeneousMinor
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
  let v := weightedLeftCup μ m c a
  have haC (I : Finset (Fin (d + 1))) :
      a I = 0 ∨ I.Nonempty ∧ I.card = m + 1 ∧ a I ∈ A₀ I := by
    have he := Submodule.mem_pi.mp ha.1 I (Set.mem_univ I)
    split_ifs at he with hI
    · exact Or.inr ⟨hI.1, by omega, he⟩
    · exact Or.inl ((Submodule.mem_bot k).mp he)
  have hcC := weighted_column_term T n z hc.1
  have hV : wd (U.weights z) v = 0 :=
    wd_weightedLeftCup_eq_zero T U z μ m c a hc.2
      (fun J L => (hcC ∅ J L).resolve_right (by simp)) ha.2
      (fun I hI => (haC I).resolve_right (fun h' => hI h'.2.1))
      (fun l t b => (traceWedgeTensorCoefficient_action τ (z l) t b).symm)
  have hterm : v ∈ (U.complex n z).C ((d : ℤ) + m + 2) :=
    weighted_left_cup_terms T U A₀ n z μ c a haC hcC fun {I J P Q L} hP hJ hPI hQI ht hw =>
      diagonal_trace_scaled_mem h τ hτ hpq L hP hJ hPI hQI (a Q) hw (c (uni (uni P J) L)) ht
  exact ⟨hterm, hV⟩

/-- The top-weight part of a diagonal column is supported on pairs of singleton charts. -/
theorem weightedColumn_top_zero {k S E : Type} [Field k] [CommRing S] [Algebra k S]
    [AddCommGroup E] [Module k E] {d : ℕ}
    (T : WeightedChartSystem k d S E) (n : DiagonalIndex d → ℕ × ℕ) (z : DiagonalIndex d → S)
    {c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) → E} (hc : c ∈ (T.complex n z).C ((d : ℤ) + 2))
    (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d))
    (hLD : L.card = d) (hIJ : ¬ (I.card = 1 ∧ J.card = 1)) :
    c (uni (uni I J) L) = 0 := by
  rcases weighted_column_term T n z hc I J L with he | ⟨hI, hJ, hC, _⟩
  · exact he
  · have hI' := Finset.card_pos.mpr hI
    have hJ' := Finset.card_pos.mpr hJ
    exact (hIJ (by rw [hLD] at hC; omega)).elim

/-- Top components of the trace cup collapse to the left edge with the same scalar weight. -/
theorem traceCup_collapse (τ : DR k E →ₗ[E] E) {m : ℕ}
    {c : Finset K₀ → W₀ ⊗[k] V₀} {a : Finset (Fin (d + 1)) → V₀}
    (ha₀ : a ∅ = 0) (kap : Finset (DiagonalIndex d) → F)
    (hs : ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d → ∀ b : V₀,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
          (-1 : ℤ) ^ d • (kap L • b))
    (hz : ∀ I J L, L.card = d → ¬ (I.card = 1 ∧ J.card = 1) → c (uni (uni I J) L) = 0)
    (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)) (hL : L.card = d) :
    collapseLogarithmicTensor (k := k) (F := F) p
      (weightedLeftCup (traceWedgeTensorCoefficient (F := F) τ) m c a (uni B L)) =
      (-1 : ℤ) ^ (m * (d + 1) + d) • (kap L • edge1 a B) := by
  let μ : (W₀ ⊗[k] V₀) →ₗ[k] V₀ →ₗ[k] (F ⊗[k] V₀) :=
    traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
  let f : F ⊗[k] V₀ →ₗ[k] V₀ := collapseLogarithmicTensor p
  have hc (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)) (hL : L.card = d) (b : V₀) :
      f (μ (c (uni (uni {i} {j}) L)) b) = (-1 : ℤ) ^ d • (kap L • b) :=
    (collapseLogarithmicTensor_traceWedgeTensorCoefficient (F := F) (p := p) (q := q)
      τ (c (uni (uni {i} {j}) L)) b).trans (hs i j L hL b)
  change f (weightedLeftCup μ m c a (uni B L)) = _
  obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
  rw [weightedLeftCup_apply, cechCup_apply, map_zsmul, map_sum, hL, edge1, lft_uni, rgt_uni]
  have hentry (P Q : Finset (Fin (d + 1))) :
      f (μ (c (uni (uni P J) L)) (a Q)) =
        if P.card = 1 ∧ J.card = 1 then (-1 : ℤ) ^ d • (kap L • a Q) else 0 := by
    by_cases h : P.card = 1 ∧ J.card = 1
    · rw [if_pos h]
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h.1
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h.2
      exact hc i j L hL (a Q)
    · rw [if_neg h, hz P J L hL h, map_zero, LinearMap.zero_apply, map_zero]
  simp only [hentry]
  by_cases hJ : J.card = 1
  · let b (Q : Finset (Fin (d + 1))) : V₀ := (-1 : ℤ) ^ d • (kap L • a Q)
    have hb : b ∅ = 0 := by simp only [b, ha₀, smul_zero]
    simp only [hJ, and_true, if_true]
    have hsum := sum_singleton_prefix b hb I
    rw [show (∑ i ∈ I, if (I.filter (· ≤ i)).card = 1 then
      (-1 : ℤ) ^ d • (kap L • a (I.filter (i ≤ ·))) else 0) = b I from hsum]
    dsimp only [b]
    rw [smul_smul, ← pow_add, add_comm 1 d]
  · simp only [hJ, and_false, if_false, Finset.sum_const_zero, smul_zero]

end GlobalTheory.PD
