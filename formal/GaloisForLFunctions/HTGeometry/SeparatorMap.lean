import GaloisForLFunctions.HTGeometry.BrickCoverCompact
import GaloisForLFunctions.HTGeometry.GeneralPosition

/-!
# A nonvanishing separating map out of a compact subset of `ℝ^k`

Given a compact `K ⊆ ℝ^k` and `m > k` pairs of uniformly separated subsets of `K`, there is a
continuous `u : K → ℝ^m` which is negative in the `i`-th coordinate on the first member of the
`i`-th pair, positive on the second, and never zero.

The map is the partition of unity of a fine brick cover of `K`, weighted by vectors chosen inside
the sign box prescribed by which members of which pair the brick meets.  Since the brick cover has
order `k + 1` and `k + 1` vectors in general position in `ℝ^m` (possible because `k < m`) have no
vanishing positive combination, the resulting map avoids the origin.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- The coordinates of a finite sum in `ℝ^m` are the sums of the coordinates. -/
theorem euclidean_sum_apply {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (∑ p ∈ s, f p) i = ∑ p ∈ s, f p i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- **The separating map.** -/
theorem exists_separating_map {k m : ℕ} (hk : 0 < k) (hkm : k < m)
    {K : Set (EuclideanSpace ℝ (Fin k))} (hK : IsCompact K)
    {P Q : Fin m → Set (EuclideanSpace ℝ (Fin k))}
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ y ∈ P i, ∀ y' ∈ Q i, ε < dist y y') :
    ∃ u : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m),
      ContinuousOn u K ∧
      (∀ i, ∀ y ∈ P i, y ∈ K → u y i < 0) ∧
      (∀ i, ∀ y ∈ Q i, y ∈ K → 0 < u y i) ∧
      (∀ y ∈ K, ∃ i, u y i ≠ 0) := by
  classical
  -- a brick cover fine enough that no brick meets both members of a pair
  set δ : ℝ := ε / (2 * (Real.sqrt k + 1)) with hδdef
  have hsqrt : (0 : ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hδ : 0 < δ := by
    rw [hδdef]
    positivity
  have hmesh : Real.sqrt k * δ < ε := by
    rw [hδdef]
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N, B, hBopen, hBcompl, hBcover, hBmesh, hBorder⟩ :=
    exists_enumerated_brick_cover hk hK hδ
  -- the bump functions of the cover
  set ψ : ℕ → EuclideanSpace ℝ (Fin k) → ℝ := fun p y => infDist y (B p)ᶜ with hψdef
  have hψcont : ∀ p, Continuous (ψ p) := fun p => Metric.continuous_infDist_pt _
  have hψnonneg : ∀ p y, 0 ≤ ψ p y := fun p y => Metric.infDist_nonneg
  have hψpos : ∀ p y, 0 < ψ p y ↔ y ∈ B p := by
    intro p y
    rw [← Metric.infDist_pos_iff_notMem_closure (hBcompl p),
      (hBopen p).isClosed_compl.closure_eq, Set.mem_compl_iff, not_not]
  set Φ : EuclideanSpace ℝ (Fin k) → ℝ := fun y => ∑ p ∈ Finset.range N, ψ p y with hΦdef
  have hΦcont : Continuous Φ := continuous_finsetSum _ fun p _ => hψcont p
  have hΦpos : ∀ y ∈ K, 0 < Φ y := by
    intro y hy
    obtain ⟨p, hpN, hpy⟩ := hBcover y hy
    refine lt_of_lt_of_le ((hψpos p y).mpr hpy) ?_
    refine Finset.single_le_sum (f := fun q => ψ q y) (fun q _ => hψnonneg q y) ?_
    exact Finset.mem_range.mpr hpN
  -- the sign boxes
  set meetsP : ℕ → Fin m → Prop := fun p i => ∃ y ∈ B p, y ∈ P i with hmP
  set meetsQ : ℕ → Fin m → Prop := fun p i => ∃ y ∈ B p, y ∈ Q i with hmQ
  have hexcl : ∀ p i, meetsP p i → ¬ meetsQ p i := by
    rintro p i ⟨y, hyB, hyP⟩ ⟨y', hy'B, hy'Q⟩
    have h1 := hsep i y hyP y' hy'Q
    have h2 := hBmesh p y hyB y' hy'B
    linarith
  set S : ℕ → Set (EuclideanSpace ℝ (Fin m)) :=
    fun p => {v | ∀ i, (meetsP p i → v i < 0) ∧ (meetsQ p i → 0 < v i)} with hSdef
  have hSopen : ∀ p, IsOpen (S p) := by
    intro p
    have hrw : S p = ⋂ i : Fin m,
        ({v : EuclideanSpace ℝ (Fin m) | meetsP p i → v i < 0} ∩
          {v : EuclideanSpace ℝ (Fin m) | meetsQ p i → 0 < v i}) := by
      ext v
      simp [hSdef, Set.mem_iInter]
    rw [hrw]
    refine isOpen_iInter_of_finite fun i => IsOpen.inter ?_ ?_
    · by_cases hp : meetsP p i
      · have : {v : EuclideanSpace ℝ (Fin m) | meetsP p i → v i < 0}
            = (fun v : EuclideanSpace ℝ (Fin m) => v i) ⁻¹' Set.Iio 0 := by
          ext v; simp [hp]
        rw [this]
        exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.isOpen_preimage _ isOpen_Iio
      · have : {v : EuclideanSpace ℝ (Fin m) | meetsP p i → v i < 0} = Set.univ := by
          ext v; simp [hp]
        rw [this]
        exact isOpen_univ
    · by_cases hq : meetsQ p i
      · have : {v : EuclideanSpace ℝ (Fin m) | meetsQ p i → 0 < v i}
            = (fun v : EuclideanSpace ℝ (Fin m) => v i) ⁻¹' Set.Ioi 0 := by
          ext v; simp [hq]
        rw [this]
        exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.isOpen_preimage _ isOpen_Ioi
      · have : {v : EuclideanSpace ℝ (Fin m) | meetsQ p i → 0 < v i} = Set.univ := by
          ext v; simp [hq]
        rw [this]
        exact isOpen_univ
  have hSne : ∀ p, (S p).Nonempty := by
    intro p
    refine ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm
      fun i => if meetsP p i then -1 else if meetsQ p i then 1 else 0, ?_⟩
    intro i
    have hval : ((EuclideanSpace.equiv (Fin m) ℝ).symm
        fun i => if meetsP p i then (-1 : ℝ) else if meetsQ p i then 1 else 0) i
        = if meetsP p i then (-1 : ℝ) else if meetsQ p i then 1 else 0 := rfl
    rw [hval]
    constructor
    · intro hp
      simp [hp]
    · intro hq
      have hp : ¬ meetsP p i := fun h => hexcl p i h hq
      simp [hp, hq]
  -- vectors in general position inside the sign boxes
  have hrank : k < Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [finrank_euclideanSpace_fin]
    exact hkm
  obtain ⟨w, hwS, hwgp⟩ := exists_generalPosition hrank S hSopen hSne N
  refine ⟨fun y => ∑ p ∈ Finset.range N, (ψ p y / Φ y) • w p, ?_, ?_, ?_, ?_⟩
  · have hterm : ∀ p : ℕ, ContinuousOn (fun y => (ψ p y / Φ y) • w p) {y | 0 < Φ y} := by
      intro p
      have h1 : ContinuousOn (fun y => ψ p y / Φ y) {y | 0 < Φ y} :=
        ((hψcont p).continuousOn).div hΦcont.continuousOn fun y hy => ne_of_gt hy
      exact h1.smul continuousOn_const
    exact ContinuousOn.mono (s := {y | 0 < Φ y})
      (continuousOn_finsetSum _ fun p _ => hterm p) (fun y hy => hΦpos y hy)
  · intro i y hyP hyK
    have hcoord : (∑ p ∈ Finset.range N, (ψ p y / Φ y) • w p) i
        = ∑ p ∈ Finset.range N, (ψ p y / Φ y) * w p i := by
      rw [euclidean_sum_apply]
      simp [PiLp.smul_apply]
    rw [hcoord]
    set t : Finset ℕ := (Finset.range N).filter (fun p => 0 < ψ p y) with htdef
    have hdrop : ∑ p ∈ Finset.range N, (ψ p y / Φ y) * w p i
        = ∑ p ∈ t, (ψ p y / Φ y) * w p i := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro p hp hpt
      have hz : ψ p y = 0 := by
        rcases lt_or_eq_of_le (hψnonneg p y) with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨hp, h⟩) hpt
        · exact h.symm
      simp [hz]
    rw [hdrop]
    have htne : t.Nonempty := by
      obtain ⟨p, hpN, hpy⟩ := hBcover y hyK
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpN, (hψpos p y).mpr hpy⟩⟩
    have hneg : ∀ p ∈ t, (ψ p y / Φ y) * w p i < 0 := by
      intro p hp
      obtain ⟨hpN, hpos⟩ := Finset.mem_filter.mp hp
      have hyB : y ∈ B p := (hψpos p y).mp hpos
      have hwneg : w p i < 0 := ((hwS p (Finset.mem_range.mp hpN)) i).1 ⟨y, hyB, hyP⟩
      exact mul_neg_of_pos_of_neg (div_pos hpos (hΦpos y hyK)) hwneg
    calc ∑ p ∈ t, (ψ p y / Φ y) * w p i < ∑ _p ∈ t, (0 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty htne hneg
      _ = 0 := by simp
  · intro i y hyQ hyK
    have hcoord : (∑ p ∈ Finset.range N, (ψ p y / Φ y) • w p) i
        = ∑ p ∈ Finset.range N, (ψ p y / Φ y) * w p i := by
      rw [euclidean_sum_apply]
      simp [PiLp.smul_apply]
    rw [hcoord]
    set t : Finset ℕ := (Finset.range N).filter (fun p => 0 < ψ p y) with htdef
    have hdrop : ∑ p ∈ Finset.range N, (ψ p y / Φ y) * w p i
        = ∑ p ∈ t, (ψ p y / Φ y) * w p i := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro p hp hpt
      have hz : ψ p y = 0 := by
        rcases lt_or_eq_of_le (hψnonneg p y) with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨hp, h⟩) hpt
        · exact h.symm
      simp [hz]
    rw [hdrop]
    have htne : t.Nonempty := by
      obtain ⟨p, hpN, hpy⟩ := hBcover y hyK
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpN, (hψpos p y).mpr hpy⟩⟩
    have hpos' : ∀ p ∈ t, (0 : ℝ) < (ψ p y / Φ y) * w p i := by
      intro p hp
      obtain ⟨hpN, hpos⟩ := Finset.mem_filter.mp hp
      have hyB : y ∈ B p := (hψpos p y).mp hpos
      have hwpos : 0 < w p i := ((hwS p (Finset.mem_range.mp hpN)) i).2 ⟨y, hyB, hyQ⟩
      exact mul_pos (div_pos hpos (hΦpos y hyK)) hwpos
    calc (0 : ℝ) = ∑ _p ∈ t, (0 : ℝ) := by simp
      _ < ∑ p ∈ t, (ψ p y / Φ y) * w p i := Finset.sum_lt_sum_of_nonempty htne hpos'
  · intro y hyK
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have huzero : (∑ p ∈ Finset.range N, (ψ p y / Φ y) • w p) = 0 :=
      PiLp.ext fun i => by rw [hcon i]; simp
    set t : Finset ℕ := (Finset.range N).filter (fun p => 0 < ψ p y) with htdef
    have hdrop : ∑ p ∈ Finset.range N, (ψ p y / Φ y) • w p
        = ∑ p ∈ t, (ψ p y / Φ y) • w p := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro p hp hpt
      have hz : ψ p y = 0 := by
        rcases lt_or_eq_of_le (hψnonneg p y) with h | h
        · exact absurd (Finset.mem_filter.mpr ⟨hp, h⟩) hpt
        · exact h.symm
      simp [hz]
    have htne : t.Nonempty := by
      obtain ⟨p, hpN, hpy⟩ := hBcover y hyK
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpN, (hψpos p y).mpr hpy⟩⟩
    have htlt : ∀ p ∈ t, p < N := fun p hp => Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    have hcard : t.card ≤ k + 1 :=
      hBorder y t htlt fun p hp => (hψpos p y).mp (Finset.mem_filter.mp hp).2
    have hlam : ∀ p ∈ t, 0 < ψ p y / Φ y := by
      intro p hp
      exact div_pos (Finset.mem_filter.mp hp).2 (hΦpos y hyK)
    exact sum_smul_ne_zero_of_generalPosition hwgp htlt hcard htne hlam (hdrop ▸ huzero)

end GaloisForLFunctions.HTGeometry
