import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import GaloisForLFunctions.HTGeometry.ThermodynamicMobileTailBounds
import GaloisForLFunctions.HTGeometry.ThermodynamicPathFieldSelection

/-!
# Mobile prefix/tail reference for one thermodynamic path field

At shell index `K`, split a finite path before physical site `4K`.  The selected Hamiltonian is
kept exactly on the early prefix; the nested diagonal center is kept exactly on the late tail.
This module identifies the retained coefficients and isolates the single crossing edge.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance instCStarAlgebraMatrixMobile
    {d : Type*} [Fintype d] [DecidableEq d] : CStarAlgebra (Matrix d d ℂ) where

/-- Physical sites strictly before the mobile cut `4K`. -/
def mobileInitialPathSites (k K : ℕ) : Finset (Fin (k + 3)) :=
  Finset.univ.filter fun s => s.val < 4 * K

/-- Physical sites at or after the mobile cut `4K`. -/
def mobileTailPathSites (k K : ℕ) : Finset (Fin (k + 3)) :=
  Finset.univ.filter fun s => 4 * K ≤ s.val

@[simp] theorem mem_mobileInitialPathSites_iff {k K : ℕ} {s : Fin (k + 3)} :
    s ∈ mobileInitialPathSites k K ↔ s.val < 4 * K := by
  simp [mobileInitialPathSites]

@[simp] theorem mem_mobileTailPathSites_iff {k K : ℕ} {s : Fin (k + 3)} :
    s ∈ mobileTailPathSites k K ↔ 4 * K ≤ s.val := by
  simp [mobileTailPathSites]

theorem mobileInitialPathSites_disjoint_mobileTailPathSites (k K : ℕ) :
    Disjoint (mobileInitialPathSites k K) (mobileTailPathSites k K) := by
  rw [Finset.disjoint_left]
  intro s hs hst
  simp only [mem_mobileInitialPathSites_iff] at hs
  simp only [mem_mobileTailPathSites_iff] at hst
  omega

theorem pathWordSupportedIn_mobileInitial_onsite_iff
    {k K : ℕ} (s : Fin (k + 3)) (q : Fin 3) :
    PathWordSupportedIn (mobileInitialPathSites k K) (Sum.inl (s, q)) ↔
      s.val < 4 * K := by
  constructor
  · intro h
    by_contra hs
    have hsout : s ∉ mobileInitialPathSites k K := by simp; omega
    have hz := h s hsout
    simp [pathWord, onsiteWord] at hz
  · intro hs v hv
    rw [pathWord, onsiteWord]
    split_ifs with hvs
    · subst v
      exact absurd (by simpa using hs) hv
    · rfl

theorem pathWordSupportedIn_mobileTail_onsite_iff
    {k K : ℕ} (s : Fin (k + 3)) (q : Fin 3) :
    PathWordSupportedIn (mobileTailPathSites k K) (Sum.inl (s, q)) ↔
      4 * K ≤ s.val := by
  constructor
  · intro h
    by_contra hs
    have hsout : s ∉ mobileTailPathSites k K := by simp; omega
    have hz := h s hsout
    simp [pathWord, onsiteWord] at hz
  · intro hs v hv
    rw [pathWord, onsiteWord]
    split_ifs with hvs
    · subst v
      exact absurd (by simpa using hs) hv
    · rfl

theorem pathWordSupportedIn_mobileInitial_edge_iff
    {k K : ℕ} (e : Fin (k + 2)) (ab : Fin 3 × Fin 3) :
    PathWordSupportedIn (mobileInitialPathSites k K) (Sum.inr (e, ab)) ↔
      e.val + 1 < 4 * K := by
  constructor
  · intro h
    by_contra he
    have hsout : e.succ ∉ mobileInitialPathSites k K := by simp; omega
    have hz := h e.succ hsout
    have hne : e.succ ≠ e.castSucc := by
      intro hc
      have := congrArg Fin.val hc
      simp at this
    simp [pathWord, couplingWord, hne] at hz
  · intro he v hv
    rw [pathWord, couplingWord]
    split_ifs with hvleft hvright
    · subst v
      exact absurd (by simp; omega) hv
    · subst v
      exact absurd (by simp; omega) hv
    · rfl

theorem pathWordSupportedIn_mobileTail_edge_iff
    {k K : ℕ} (e : Fin (k + 2)) (ab : Fin 3 × Fin 3) :
    PathWordSupportedIn (mobileTailPathSites k K) (Sum.inr (e, ab)) ↔
      4 * K ≤ e.val := by
  constructor
  · intro h
    by_contra he
    have hsout : e.castSucc ∉ mobileTailPathSites k K := by simp; omega
    have hz := h e.castSucc hsout
    simp [pathWord, couplingWord] at hz
  · intro he v hv
    rw [pathWord, couplingWord]
    split_ifs with hvleft hvright
    · subst v
      exact absurd (by simp; omega) hv
    · subst v
      exact absurd (by simp; omega) hv
    · rfl

theorem pathPacketReferenceCoeff_mobile_onsite
    {k K : ℕ} (u center : PathShell (k + 1))
    (s : Fin (k + 3)) (q : Fin 3) :
    pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
        u center (Sum.inl (s, q)) =
      if s.val < 4 * K then u (Sum.inl (s, q)) else center (Sum.inl (s, q)) := by
  simp only [pathPacketReferenceCoeff,
    pathWordSupportedIn_mobileInitial_onsite_iff,
    pathWordSupportedIn_mobileTail_onsite_iff]
  by_cases hs : s.val < 4 * K
  · have htail : ¬4 * K ≤ s.val := by omega
    simp [hs, htail]
  · have htail : 4 * K ≤ s.val := by omega
    simp [hs, htail]

theorem pathPacketReferenceCoeff_mobile_edge
    {k K : ℕ} (u center : PathShell (k + 1))
    (e : Fin (k + 2)) (ab : Fin 3 × Fin 3) :
    pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
        u center (Sum.inr (e, ab)) =
      (if e.val + 1 < 4 * K then u (Sum.inr (e, ab)) else 0) +
        (if 4 * K ≤ e.val then center (Sum.inr (e, ab)) else 0) := by
  simp only [pathPacketReferenceCoeff,
    pathWordSupportedIn_mobileInitial_edge_iff,
    pathWordSupportedIn_mobileTail_edge_iff]

theorem abs_mobile_onsite_coefficient_error_le
    {k K : ℕ} {p center radius : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - center i| ≤ radius i)
    (s : Fin (k + 3)) (q : Fin 3) :
    |infinitePathPrefixShell k p (Sum.inl (s, q)) -
        pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
          (infinitePathPrefixShell k p) (infinitePathPrefixShell k center)
          (Sum.inl (s, q))| ≤
      if 4 * K ≤ s.val then radius (Sum.inl (s.val, q)) else 0 := by
  rw [pathPacketReferenceCoeff_mobile_onsite]
  by_cases hs : s.val < 4 * K
  · have htail : ¬4 * K ≤ s.val := by omega
    simp [hs, htail]
  · have htail : 4 * K ≤ s.val := by omega
    simp only [if_neg hs, if_pos htail]
    exact hp (Sum.inl (s.val, q))

theorem abs_mobile_edge_coefficient_error_le
    {k K : ℕ} {p center radius : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - center i| ≤ radius i)
    (e : Fin (k + 2)) (ab : Fin 3 × Fin 3) :
    |infinitePathPrefixShell k p (Sum.inr (e, ab)) -
        pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
          (infinitePathPrefixShell k p) (infinitePathPrefixShell k center)
          (Sum.inr (e, ab))| ≤
      if 4 * K ≤ e.val + 1 then
        radius (Sum.inr (e.val, ab)) +
          if e.val + 1 = 4 * K then |center (Sum.inr (e.val, ab))| else 0
      else 0 := by
  rw [pathPacketReferenceCoeff_mobile_edge]
  by_cases hearly : e.val + 1 < 4 * K
  · have hnot : ¬4 * K ≤ e.val + 1 := by omega
    have htail : ¬4 * K ≤ e.val := by omega
    simp [hearly, hnot, htail]
  · have hlate : 4 * K ≤ e.val + 1 := by omega
    by_cases htail : 4 * K ≤ e.val
    · have hcross : e.val + 1 ≠ 4 * K := by omega
      simp only [if_neg hearly, if_pos htail, zero_add, if_pos hlate, if_neg hcross, add_zero]
      exact hp (Sum.inr (e.val, ab))
    · have hcross : e.val + 1 = 4 * K := by omega
      simp only [if_neg hearly, if_neg htail, add_zero, sub_zero, if_pos hlate,
        if_pos hcross]
      calc
        |p (Sum.inr (e.val, ab))| =
            |(p (Sum.inr (e.val, ab)) - center (Sum.inr (e.val, ab))) +
              center (Sum.inr (e.val, ab))| := by ring_nf
        _ ≤ |p (Sum.inr (e.val, ab)) - center (Sum.inr (e.val, ab))| +
              |center (Sum.inr (e.val, ab))| := abs_add_le _ _
        _ ≤ radius (Sum.inr (e.val, ab)) +
              |center (Sum.inr (e.val, ab))| :=
          add_le_add (hp (Sum.inr (e.val, ab))) le_rfl

theorem nestedInfiniteEdgeWeight_nonneg (e : ℕ) : 0 ≤ nestedInfiniteEdgeWeight e := by
  unfold nestedInfiniteEdgeWeight
  split_ifs <;> positivity

theorem infinitePathPrefixShell_nestedCenter_isDiag (k : ℕ) :
    ∀ l : PathLabel (k + 1), ¬IsDiagLabel l →
      infinitePathPrefixShell k nestedInfinitePathCenter l = 0 := by
  intro l hl
  rcases l with sq | eab
  · simp only [IsDiagLabel] at hl ⊢
    simp [infinitePathPrefixShell, pathLabelToInfinite, nestedInfinitePathCenter, hl]
  · simp only [IsDiagLabel] at hl ⊢
    simp [infinitePathPrefixShell, pathLabelToInfinite, nestedInfinitePathCenter, hl]

theorem sum_axis_infinitePathRadius_onsite (s : ℕ) :
    ∑ q : Fin 3, infinitePathRadius (Sum.inl (s, q)) =
      3 / (1000000 * (((s + 1 : ℕ) : ℝ) ^ 2)) := by
  simp [infinitePathRadius]
  field_simp

theorem sum_axes_infinitePathRadius_edge (e : ℕ) :
    ∑ ab : Fin 3 × Fin 3, infinitePathRadius (Sum.inr (e, ab)) =
      9 / (1000000 * (((e + 1 : ℕ) : ℝ) ^ 2)) := by
  simp [infinitePathRadius]
  field_simp

theorem sum_axes_abs_nestedInfinitePathCenter_edge (e : ℕ) :
    ∑ ab : Fin 3 × Fin 3, |nestedInfinitePathCenter (Sum.inr (e, ab))| =
      nestedInfiniteEdgeWeight e / 4 := by
  rw [Finset.sum_eq_single (((2 : Fin 3), (2 : Fin 3)))]
  · rw [nestedInfinitePathCenter, if_pos rfl,
      abs_of_nonneg (div_nonneg (nestedInfiniteEdgeWeight_nonneg e) (by norm_num))]
  · intro ab hab hne
    simp [nestedInfinitePathCenter, hne]
  · simp

/-- Coordinate majorant: perturbation tail plus center coefficient on the single crossing edge. -/
def mobilePathCoefficientMajorant
    (k K : ℕ) (center radius : InfinitePathLabel → ℝ) : ℝ :=
  (∑ s : Fin (k + 3), ∑ q : Fin 3,
      if 4 * K ≤ s.val then radius (Sum.inl (s.val, q)) else 0) +
    ∑ e : Fin (k + 2), ∑ ab : Fin 3 × Fin 3,
      if 4 * K ≤ e.val + 1 then
        radius (Sum.inr (e.val, ab)) +
          if e.val + 1 = 4 * K then |center (Sum.inr (e.val, ab))| else 0
      else 0

theorem sum_abs_mobile_packetReference_error_le_majorant
    {k K : ℕ} {p center radius : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - center i| ≤ radius i) :
    (∑ l : PathLabel (k + 1),
      |infinitePathPrefixShell k p l -
        pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
          (infinitePathPrefixShell k p) (infinitePathPrefixShell k center) l|) ≤
      mobilePathCoefficientMajorant k K center radius := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold mobilePathCoefficientMajorant
  apply add_le_add
  · exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun q _ =>
      abs_mobile_onsite_coefficient_error_le hp s q
  · exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun ab _ =>
      abs_mobile_edge_coefficient_error_le hp e ab

def mobileOnsiteRadiusMass (k K : ℕ) : ℝ :=
  ∑ s : Fin (k + 3),
    if 4 * K < s.val + 1 then
      3 / (1000000 * (((s.val + 1 : ℕ) : ℝ) ^ 2)) else 0

def mobileEdgeRadiusMass (k K : ℕ) : ℝ :=
  ∑ e : Fin (k + 2),
    if 4 * K - 1 < e.val + 1 then
      9 / (1000000 * (((e.val + 1 : ℕ) : ℝ) ^ 2)) else 0

def mobileCrossingCenterMass (k K : ℕ) : ℝ :=
  ∑ e : Fin (k + 2),
    if e.val + 1 = 4 * K then nestedInfiniteEdgeWeight e.val / 4 else 0

theorem mobilePathCoefficientMajorant_nested_eq
    {k K : ℕ} (hK : 1 ≤ K) :
    mobilePathCoefficientMajorant k K nestedInfinitePathCenter infinitePathRadius =
      mobileOnsiteRadiusMass k K + mobileEdgeRadiusMass k K +
        mobileCrossingCenterMass k K := by
  have hcut : 0 < 4 * K := by omega
  unfold mobilePathCoefficientMajorant mobileOnsiteRadiusMass mobileEdgeRadiusMass
    mobileCrossingCenterMass
  have hOn :
      (∑ s : Fin (k + 3), ∑ q : Fin 3,
        if 4 * K ≤ s.val then infinitePathRadius (Sum.inl (s.val, q)) else 0) =
      ∑ s : Fin (k + 3),
        if 4 * K < s.val + 1 then
          3 / (1000000 * (((s.val + 1 : ℕ) : ℝ) ^ 2)) else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases htail : 4 * K ≤ s.val
    · have htail' : 4 * K < s.val + 1 := by omega
      simp [htail, htail', sum_axis_infinitePathRadius_onsite]
    · have htail' : ¬4 * K < s.val + 1 := by omega
      simp [htail, htail']
  rw [hOn]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hlate : 4 * K ≤ e.val + 1
  · have hlate' : 4 * K - 1 < e.val + 1 := by omega
    simp only [if_pos hlate, Finset.sum_add_distrib]
    rw [sum_axes_infinitePathRadius_edge]
    by_cases hcross : e.val + 1 = 4 * K
    · simp [hcross, sum_axes_abs_nestedInfinitePathCenter_edge]
    · simp [hlate', hcross]
  · have hlate' : ¬4 * K - 1 < e.val + 1 := by omega
    have hcross : e.val + 1 ≠ 4 * K := by omega
    simp [hlate, hlate', hcross]

theorem mobileOnsiteRadiusMass_le
    {k K : ℕ} (hK : 1 ≤ K) (hsize : 4 * K ≤ k + 3) :
    mobileOnsiteRadiusMass k K ≤ 3 / (1000000 * ((4 * K : ℕ) : ℝ)) := by
  exact StaticLocalLaboratoryComplexityGrowthLaw.sum_fin_succ_inv_square_over_million_le
    (k + 3) (4 * K) 3 (by norm_num) (by omega) hsize

theorem mobileEdgeRadiusMass_le
    {k K : ℕ} (hK : 1 ≤ K) (hsize : 4 * K - 1 ≤ k + 2) :
    mobileEdgeRadiusMass k K ≤ 9 / (1000000 * ((4 * K - 1 : ℕ) : ℝ)) := by
  exact StaticLocalLaboratoryComplexityGrowthLaw.sum_fin_succ_inv_square_over_million_le
    (k + 2) (4 * K - 1) 9 (by norm_num) (by omega) hsize

theorem mobileCrossingCenterMass_eq
    {k K : ℕ} (hK : 1 ≤ K) (hsize : 4 * K - 1 < k + 2) :
    mobileCrossingCenterMass k K = nestedInfiniteEdgeWeight (4 * K - 1) / 4 := by
  let e₀ : Fin (k + 2) := ⟨4 * K - 1, hsize⟩
  unfold mobileCrossingCenterMass
  rw [Finset.sum_eq_single e₀]
  · simp [e₀]
    omega
  · intro e he hne
    have hcross : e.val + 1 ≠ 4 * K := by
      intro hc
      apply hne
      apply Fin.ext
      dsimp [e₀]
      omega
    simp [hcross]
  · simp

theorem nestedInfiniteEdgeWeight_mobileCrossing
    {K : ℕ} (hK : 1 ≤ K) :
    nestedInfiniteEdgeWeight (4 * K - 1) =
      1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) := by
  unfold nestedInfiniteEdgeWeight
  have hodd : ¬Even (4 * K - 1) := by
    rintro ⟨r, hr⟩
    omega
  rw [if_neg hodd]
  have hdiv : (4 * K - 1) / 2 = 2 * K - 1 := by omega
  rw [hdiv]
  have hnat : 2 * K - 1 + 2 = 2 * K + 1 := by omega
  rw [hnat]

/-- Full coefficient deletion budget: one inverse-fourth crossing bond plus the summable
inverse-square perturbation suffix. -/
theorem mobilePathCoefficientMajorant_nested_le
    {k K : ℕ} (hK : 8 ≤ K) (hsize : 4 * K ≤ k + 2) :
    mobilePathCoefficientMajorant k K nestedInfinitePathCenter infinitePathRadius ≤
      1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ)) := by
  have hK1 : 1 ≤ K := by omega
  have hOn := mobileOnsiteRadiusMass_le hK1 (show 4 * K ≤ k + 3 by omega)
  have hEdge := mobileEdgeRadiusMass_le hK1 (show 4 * K - 1 ≤ k + 2 by omega)
  have hCross := mobileCrossingCenterMass_eq hK1 (show 4 * K - 1 < k + 2 by omega)
  have hOnCoarse : mobileOnsiteRadiusMass k K ≤
      3 / (1000000 * (K : ℝ)) := by
    refine le_trans hOn ?_
    norm_num [Nat.cast_mul]
    gcongr
    exact_mod_cast (show K ≤ 4 * K by omega)
  have hEdgeCoarse : mobileEdgeRadiusMass k K ≤
      9 / (1000000 * (K : ℝ)) := by
    refine le_trans hEdge ?_
    have hden : (K : ℝ) ≤ (4 * K - 1 : ℕ) := by exact_mod_cast (show K ≤ 4 * K - 1 by omega)
    gcongr
  have hWeight := nestedInfiniteEdgeWeight_mobileCrossing hK1
  have hCrossCoarse : mobileCrossingCenterMass k K ≤
      1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) := by
    rw [hCross, hWeight]
    have hw : 0 ≤ 1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) := by positivity
    linarith
  rw [mobilePathCoefficientMajorant_nested_eq hK1]
  have hsum := add_le_add (add_le_add hOnCoarse hEdgeCoarse) hCrossCoarse
  calc
    mobileOnsiteRadiusMass k K + mobileEdgeRadiusMass k K + mobileCrossingCenterMass k K ≤
        3 / (1000000 * (K : ℝ)) + 9 / (1000000 * (K : ℝ)) +
          1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) := hsum
    _ = 1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ)) := by ring

/-- Operator-norm distance from one selected finite prefix to its exact mobile packet reference. -/
theorem norm_thermodynamicPath_sub_mobileReference_le
    {k K : ℕ} {p : InfinitePathLabel → ℝ}
    (hK : 8 ≤ K) (hsize : 4 * K ≤ k + 2)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) :
    ‖pathHamiltonian (infinitePathPrefixShell k p) -
      pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
        (infinitePathPrefixShell k p)
        (infinitePathPrefixShell k nestedInfinitePathCenter)‖ ≤
      1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ)) := by
  calc
    ‖pathHamiltonian (infinitePathPrefixShell k p) -
      pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
        (infinitePathPrefixShell k p)
        (infinitePathPrefixShell k nestedInfinitePathCenter)‖ ≤
        ∑ l : PathLabel (k + 1),
          |infinitePathPrefixShell k p l -
            pathPacketReferenceCoeff (mobileInitialPathSites k K) (mobileTailPathSites k K)
              (infinitePathPrefixShell k p)
              (infinitePathPrefixShell k nestedInfinitePathCenter) l| :=
      norm_pathHamiltonian_sub_packetReference_le _ _ _ _
    _ ≤ mobilePathCoefficientMajorant k K nestedInfinitePathCenter infinitePathRadius :=
      sum_abs_mobile_packetReference_error_le_majorant (fun i => le_of_lt (hp i))
    _ ≤ 1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ)) :=
      mobilePathCoefficientMajorant_nested_le hK hsize

/-- Finite-time physical evolution remains within the Duhamel budget of the factorized mobile
reference. -/
theorem norm_unitaryEvolution_thermodynamicPath_sub_mobileReference_le
    {k K : ℕ} {p : InfinitePathLabel → ℝ}
    (hK : 8 ≤ K) (hsize : 4 * K ≤ k + 2)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (t : ℝ) :
    ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
      unitaryEvolution
        (pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
          (infinitePathPrefixShell k p)
          (infinitePathPrefixShell k nestedInfinitePathCenter)) t‖ ≤
      |t| * (1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4) +
        12 / (1000000 * (K : ℝ))) := by
  have href : IsSelfAdjoint
      (pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
        (infinitePathPrefixShell k p)
        (infinitePathPrefixShell k nestedInfinitePathCenter)) :=
    (isSelfAdjoint_pathHamiltonianOnSites _ _).add
      (isSelfAdjoint_pathHamiltonianOnSites _ _)
  have hduhamel :
      ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
        unitaryEvolution
          (pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
            (infinitePathPrefixShell k p)
            (infinitePathPrefixShell k nestedInfinitePathCenter)) t‖ ≤
        |t| * ‖pathHamiltonian (infinitePathPrefixShell k p) -
          pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
            (infinitePathPrefixShell k p)
            (infinitePathPrefixShell k nestedInfinitePathCenter)‖ := by
    simpa [unitaryEvolution] using selfAdjoint_unitaryEvolution_norm_sub_le
      (pathHamiltonian (infinitePathPrefixShell k p))
      (pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
        (infinitePathPrefixShell k p)
        (infinitePathPrefixShell k nestedInfinitePathCenter))
      (isSelfAdjoint_pathHamiltonian _) href t
  refine le_trans hduhamel ?_
  exact mul_le_mul_of_nonneg_left
    (norm_thermodynamicPath_sub_mobileReference_le hK hsize hp) (abs_nonneg t)

/-- Strict mobile-reference approximation throughout the complete laboratory shell. -/
theorem norm_unitaryEvolution_thermodynamicPath_sub_mobileReference_lt
    {k K : ℕ} {p : InfinitePathLabel → ℝ} {t ε : ℝ}
    (hK : 8 ≤ K) (hsize : 4 * K ≤ k + 2)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (hε : 0 < ε) (ht0 : 0 ≤ t)
    (ht : t < 256 * Real.pi * ε * (K + 1)) :
    ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
      unitaryEvolution
        (pathHamiltonianPacketReference (mobileInitialPathSites k K) (mobileTailPathSites k K)
          (infinitePathPrefixShell k p)
          (infinitePathPrefixShell k nestedInfinitePathCenter)) t‖ < ε := by
  have hbound := norm_unitaryEvolution_thermodynamicPath_sub_mobileReference_le
    hK hsize hp t
  rw [abs_of_nonneg ht0] at hbound
  have hbase := StaticLocalLaboratoryComplexityGrowthLaw.mobileCut_baseDuhamel_lt_half
    hK hε ht
  have hpert := StaticLocalLaboratoryComplexityGrowthLaw.mobileCut_perturbDuhamel_lt_half
    hK hε ht0 ht (show 12 / (1000000 * (K : ℝ)) ≤
      12 / (1000000 * (K : ℝ)) by rfl)
  nlinarith

end

end GaloisForLFunctions.HTGeometry
