import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.BarnesHeckeRelation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheHeckeConesTileTheQuadrant

/-!
# The Barnes period is a Hecke eigenfunction for every prime

The boundary Barnes period `P_w(a, b) = Σ_{v ∈ ℕ² ∖ 0} (1_{x ≥ 1} + 1_{y ≥ 1}) (xa + yb)^{−w}` of a
cone basis `M = [[α, β], [γ, δ]]` (`P_w(αa + βb, γa + δb)`) is the lattice sum weighted by the two
half-open cones of `M` (`barnesBoundaryPeriod_eq_coneSum`). Counting cones pointwise turns cone
identities into period identities in the absolute chamber `Re w > 2`:

* **Every prime** (`barnesBoundaryPeriod_hecke_prime`): the Hecke cones of determinant `p` cover each
  vector once, and the `p`-divisible vectors `p + 1` times (`heckeConeCount_eq`), so
  `Σ_{M ∈ X_p} P_w(M(a, b)) = P_w(a, b) + p P_w(pa, pb)`.
* **The source Hecke operator** `T_{p,s} f(a) = Σ_{M ∈ X_p} (γa + δ)^{−2s} f((αa + β)/(γa + δ))`
  (`lewisHeckeOperator`) has eigenvalue `1 + p^{1−w}` on `a ↦ P_w(a, 1)`
  (`barnesBoundaryPeriod_lewisHecke`).
* **Farey splitting, inversion and the Lewis equation** (`barnesBoundaryPeriod_farey`,
  `barnesBoundaryPeriod_reciprocity`, `barnesBoundaryPeriod_three_term`): the determinant-one cones.
-/

noncomputable section
open Complex Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ### Lattice sums over cones -/

/-- The value `(xa + yb)^{−w}` of a vector of the closed quadrant, `0` off it. -/
def quadrantValue (w : ℂ) (a b : ℝ) (v : ℤ × ℤ) : ℂ :=
  if 0 ≤ v.1 ∧ 0 ≤ v.2 then (((v.1 : ℝ) * a + (v.2 : ℝ) * b : ℝ) : ℂ) ^ (-w) else 0

theorem summable_quadrantValue {w : ℂ} (hw : 2 < w.re) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable (quadrantValue w a b) := by
  set c := min a b
  have hc : 0 < c := lt_min ha hb
  have hw0 : -w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hmaj := (summable_barnesLattice_rpow ha hb hc hw).mul_left ((2 : ℝ) ^ w.re)
  have hg : Function.Injective (fun q : ℕ × ℕ => ((q.1 : ℤ), (q.2 : ℤ))) := by
    intro q q' h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2
  rw [← hg.summable_iff]
  · refine Summable.of_norm_bounded hmaj fun q => ?_
    simp only [Function.comp, quadrantValue, Nat.cast_nonneg, and_self, if_true,
      Int.cast_natCast]
    set r := (q.1 : ℝ) * a + (q.2 : ℝ) * b
    have hr0 : 0 ≤ r := by positivity
    have hL : barnesLattice a b q = r := rfl
    rw [hL]
    rcases hr0.lt_or_eq with hr | hr
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.neg_re]
      have hcr : c ≤ r := by
        by_contra h
        push Not at h
        have h1 : (q.1 : ℝ) < 1 := by
          by_contra h1; push Not at h1
          nlinarith [min_le_left a b, mul_le_mul_of_nonneg_right h1 ha.le,
            mul_nonneg (Nat.cast_nonneg q.2 : (0 : ℝ) ≤ q.2) hb.le]
        have h2 : (q.2 : ℝ) < 1 := by
          by_contra h2; push Not at h2
          nlinarith [min_le_right a b, mul_le_mul_of_nonneg_right h2 hb.le,
            mul_nonneg (Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1) ha.le]
        have e1 : q.1 = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h1)
        have e2 : q.2 = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h2)
        simp [r, e1, e2] at hr
      have h1 : (2 * r) ^ (-w.re) ≤ (c + r) ^ (-w.re) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h2 : (2 * r) ^ (-w.re) = 2 ^ (-w.re) * r ^ (-w.re) :=
        Real.mul_rpow (by norm_num) hr.le
      have h3 : (2 : ℝ) ^ w.re * 2 ^ (-w.re) = 1 := by
        rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
      have h4 : 0 ≤ (2 : ℝ) ^ w.re := by positivity
      calc r ^ (-w.re) = (2 : ℝ) ^ w.re * (2 * r) ^ (-w.re) := by
            rw [h2, ← mul_assoc, h3, one_mul]
        _ ≤ (2 : ℝ) ^ w.re * (c + r) ^ (-w.re) := mul_le_mul_of_nonneg_left h1 h4
    · rw [← hr, Complex.ofReal_zero, Complex.zero_cpow hw0, norm_zero]
      positivity
  · rintro ⟨x, y⟩ hv
    simp only [quadrantValue]
    rw [if_neg]
    rintro ⟨hx, hy⟩
    exact hv ⟨(x.toNat, y.toNat), by simp [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]⟩

open Classical in
/-- The weight of `v` in the boundary period of the basis `[[α, β], [γ, δ]]`: one for each of the
half-open cones `{m u₁ + k u₂ : m ≥ 1, k ≥ 0}` and `{m u₁ + k u₂ : m ≥ 0, k ≥ 1}` containing `v`. -/
def coneWeight (α β γ δ : ℤ) (v : ℤ × ℤ) : ℂ :=
  (if InHeckeCone α β γ δ v.1 v.2 then 1 else 0) + (if InHeckeCone δ γ β α v.2 v.1 then 1 else 0)

theorem norm_coneWeight_le (α β γ δ : ℤ) (v : ℤ × ℤ) : ‖coneWeight α β γ δ v‖ ≤ 2 := by
  unfold coneWeight
  split_ifs <;> norm_num

theorem summable_coneWeight_mul {w : ℂ} (hw : 2 < w.re) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (α β γ δ : ℤ) : Summable fun v => coneWeight α β γ δ v * quadrantValue w a b v :=
  Summable.of_norm_bounded ((summable_quadrantValue hw ha hb).norm.mul_left 2) fun v => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_coneWeight_le α β γ δ v) (norm_nonneg _)

/-- **The boundary period of a cone basis is its weighted lattice sum.** -/
theorem barnesBoundaryPeriod_eq_coneSum {α β γ δ : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (hdet : α * δ - β * γ ≠ 0) {w : ℂ} (hw : 2 < w.re) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    barnesBoundaryPeriod w (α * a + β * b) (γ * a + δ * b) =
      ∑' v : ℤ × ℤ, coneWeight α β γ δ v * quadrantValue w a b v := by
  classical
  set G := quadrantValue w a b
  have hG := summable_quadrantValue hw ha hb
  have key : ∀ m k : ℤ, m * α + k * γ = 0 → m * β + k * δ = 0 → m = 0 ∧ k = 0 := by
    intro m k h1 h2
    have e1 : m * (α * δ - β * γ) = 0 := by linear_combination δ * h1 - γ * h2
    have e2 : k * (α * δ - β * γ) = 0 := by linear_combination α * h2 - β * h1
    exact ⟨(mul_eq_zero.mp e1).resolve_right hdet, (mul_eq_zero.mp e2).resolve_right hdet⟩
  let ι₁ : ℕ × ℕ → ℤ × ℤ := fun q =>
    (((q.1 : ℤ) + 1) * α + q.2 * γ, ((q.1 : ℤ) + 1) * β + q.2 * δ)
  let ι₂ : ℕ × ℕ → ℤ × ℤ := fun q =>
    ((q.1 : ℤ) * α + ((q.2 : ℤ) + 1) * γ, (q.1 : ℤ) * β + ((q.2 : ℤ) + 1) * δ)
  have hι₁ : Function.Injective ι₁ := by
    rintro ⟨m, k⟩ ⟨m', k'⟩ h
    simp only [ι₁, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := key ((m : ℤ) - m') ((k : ℤ) - k') (by linear_combination h.1)
      (by linear_combination h.2)
    exact Prod.ext (by omega) (by omega)
  have hι₂ : Function.Injective ι₂ := by
    rintro ⟨m, k⟩ ⟨m', k'⟩ h
    simp only [ι₂, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := key ((m : ℤ) - m') ((k : ℤ) - k') (by linear_combination h.1)
      (by linear_combination h.2)
    exact Prod.ext (by omega) (by omega)
  have hr₁ : Set.range ι₁ = {v | InHeckeCone α β γ δ v.1 v.2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨m, k⟩, h⟩
      simp only [ι₁, Prod.mk.injEq] at h
      exact ⟨(m : ℤ) + 1, k, by omega, by omega, h.1.symm, h.2.symm⟩
    · rintro ⟨m, k, hm, hk, hx, hy⟩
      refine ⟨((m - 1).toNat, k.toNat), ?_⟩
      simp only [ι₁, Prod.mk.injEq]
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hk]
      exact ⟨by rw [hx]; ring, by rw [hy]; ring⟩
  have hr₂ : Set.range ι₂ = {v | InHeckeCone δ γ β α v.2 v.1} := by
    ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨m, k⟩, h⟩
      simp only [ι₂, Prod.mk.injEq] at h
      exact ⟨(k : ℤ) + 1, m, by omega, by omega, by rw [← h.2]; ring, by rw [← h.1]; ring⟩
    · rintro ⟨m, k, hm, hk, hy, hx⟩
      refine ⟨(k.toNat, (m - 1).toNat), ?_⟩
      simp only [ι₂, Prod.mk.injEq]
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hk]
      exact ⟨by rw [hx]; ring, by rw [hy]; ring⟩
  have hnn : ∀ m k : ℕ, ∀ s t : ℤ, 0 ≤ s → 0 ≤ t → 0 ≤ (m : ℤ) * s + (k : ℤ) * t :=
    fun m k s t hs ht => add_nonneg (mul_nonneg (by positivity) hs) (mul_nonneg (by positivity) ht)
  have e₁ : barnesDoubleZeta (α * a + β * b) (γ * a + δ * b) w ((α * a + β * b : ℝ) : ℂ) =
      ∑' v, (Set.range ι₁).indicator G v := by
    rw [barnesDoubleZeta, ← tsum_subtype (Set.range ι₁) G, tsum_range G hι₁]
    refine tsum_congr fun q => ?_
    obtain ⟨m, k⟩ := q
    have p1 := hnn (m + 1) k α γ hα hγ
    have p2 := hnn (m + 1) k β δ hβ hδ
    push_cast at p1 p2
    simp only [G, quadrantValue, ι₁]
    rw [if_pos ⟨p1, p2⟩]
    congr 1
    simp only [barnesLattice]
    push_cast
    ring
  have e₂ : barnesDoubleZeta (α * a + β * b) (γ * a + δ * b) w ((γ * a + δ * b : ℝ) : ℂ) =
      ∑' v, (Set.range ι₂).indicator G v := by
    rw [barnesDoubleZeta, ← tsum_subtype (Set.range ι₂) G, tsum_range G hι₂]
    refine tsum_congr fun q => ?_
    obtain ⟨m, k⟩ := q
    have p1 := hnn m (k + 1) α γ hα hγ
    have p2 := hnn m (k + 1) β δ hβ hδ
    push_cast at p1 p2
    simp only [G, quadrantValue, ι₂]
    rw [if_pos ⟨p1, p2⟩]
    congr 1
    simp only [barnesLattice]
    push_cast
    ring
  rw [barnesBoundaryPeriod, e₁, e₂, ← (hG.indicator _).tsum_add (hG.indicator _), hr₁, hr₂]
  refine tsum_congr fun v => ?_
  simp only [Set.indicator, Set.mem_setOf_eq, coneWeight]
  split_ifs <;> ring

/-! ### Cone membership for the basic bases -/

/-- For a unimodular basis the cone is cut out by the two coordinates of `v` in that basis. -/
theorem inHeckeCone_iff_of_det_one {α β γ δ x y : ℤ} (h : α * δ - β * γ = 1) :
    InHeckeCone α β γ δ x y ↔ 1 ≤ δ * x - γ * y ∧ 0 ≤ α * y - β * x := by
  constructor
  · rintro ⟨m, k, hm, hk, hx, hy⟩
    have e1 : δ * x - γ * y = m := by rw [hx, hy]; linear_combination m * h
    have e2 : α * y - β * x = k := by rw [hx, hy]; linear_combination k * h
    rw [e1, e2]
    exact ⟨hm, hk⟩
  · rintro ⟨h1, h2⟩
    exact ⟨δ * x - γ * y, α * y - β * x, h1, h2, by linear_combination (-x) * h,
      by linear_combination (-y) * h⟩

theorem inHeckeCone_scalar {p : ℤ} (hp : 0 < p) {x y : ℤ} :
    InHeckeCone p 0 0 p x y ↔ p ∣ x ∧ p ∣ y ∧ 1 ≤ x ∧ 0 ≤ y := by
  constructor
  · rintro ⟨m, k, hm, hk, hx, hy⟩
    simp only [mul_zero, add_zero, zero_add] at hx hy
    exact ⟨⟨m, by rw [hx]; ring⟩, ⟨k, by rw [hy]; ring⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨m, hm⟩, ⟨k, hk⟩, hx, hy⟩
    refine ⟨m, k, ?_, ?_, by rw [hm]; ring, by rw [hk]; ring⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

/-! ### The Hecke identity for every prime -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- The count of Hecke cones through a vector of the closed quadrant. -/
theorem heckeConeCount_cast {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (heckeConeCount p x y : ℂ) =
      if 1 ≤ x then (if (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y then (p : ℂ) + 1 else 1) else 0 := by
  by_cases h1 : 1 ≤ x
  · rw [heckeConeCount_eq h1 hy, if_pos h1]
    split_ifs <;> push_cast <;> rfl
  · rw [heckeConeCount_eq_zero (by omega), if_neg h1, Nat.cast_zero]

open Classical in
/-- Summing the cone weights over `X_p` counts the cones through `v` and through its transpose. -/
theorem sum_coneWeight_heckeSet (x y : ℤ) :
    ∑ M ∈ heckeSet p, coneWeight M.1 M.2.1 M.2.2.1 M.2.2.2 (x, y) =
      (heckeConeCount p x y : ℂ) + heckeConeCount p y x := by
  simp only [coneWeight, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_boole]
    rfl
  · have hswap : ∑ M ∈ heckeSet p,
        (if InHeckeCone M.2.2.2 M.2.2.1 M.2.1 M.1 y x then (1 : ℂ) else 0) =
        ∑ M ∈ heckeSet p, (if InHeckeCone M.1 M.2.1 M.2.2.1 M.2.2.2 y x then (1 : ℂ) else 0) := by
      refine Finset.sum_nbij' (fun M => (M.2.2.2, M.2.2.1, M.2.1, M.1))
        (fun M => (M.2.2.2, M.2.2.1, M.2.1, M.1)) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl)
      · rintro ⟨a, b, c, d⟩ hM
        simp only [heckeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hM ⊢
        obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hM
        exact ⟨⟨h4, h3, h2, h1⟩, h5.swap⟩
      · rintro ⟨a, b, c, d⟩ hM
        simp only [heckeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hM ⊢
        obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hM
        exact ⟨⟨h4, h3, h2, h1⟩, h5.swap⟩
    rw [hswap, Finset.sum_boole]
    rfl

/-- **Pointwise count**: the `X_p`-cones through `v` and `vᵀ` are the cones of the identity plus
`p` times the cones of `p · Id`. -/
theorem sum_coneWeight_heckeSet_eq {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∑ M ∈ heckeSet p, coneWeight M.1 M.2.1 M.2.2.1 M.2.2.2 (x, y) =
      coneWeight 1 0 0 1 (x, y) + p * coneWeight p 0 0 p (x, y) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  rw [sum_coneWeight_heckeSet, heckeConeCount_cast hx hy, heckeConeCount_cast hy hx]
  simp only [coneWeight, inHeckeCone_scalar hp0,
    inHeckeCone_iff_of_det_one (show (1 : ℤ) * 1 - 0 * 0 = 1 by norm_num), one_mul, zero_mul,
    sub_zero]
  by_cases h1 : 1 ≤ x <;> by_cases h2 : 1 ≤ y <;> by_cases h3 : (p : ℤ) ∣ x <;>
    by_cases h4 : (p : ℤ) ∣ y <;> simp [h1, h2, h3, h4, hx, hy] <;> ring

/-- **The Barnes Hecke identity for every prime**:
`Σ_{M ∈ X_p} P_w(αa + βb, γa + δb) = P_w(a, b) + p P_w(pa, pb)`. -/
theorem barnesBoundaryPeriod_hecke_prime {w : ℂ} (hw : 2 < w.re) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    ∑ M ∈ heckeSet p, barnesBoundaryPeriod w (M.1 * a + M.2.1 * b) (M.2.2.1 * a + M.2.2.2 * b) =
      barnesBoundaryPeriod w a b + p * barnesBoundaryPeriod w (p * a) (p * b) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hcone : ∀ M ∈ heckeSet p,
      barnesBoundaryPeriod w (M.1 * a + M.2.1 * b) (M.2.2.1 * a + M.2.2.2 * b) =
        ∑' v, coneWeight M.1 M.2.1 M.2.2.1 M.2.2.2 v * quadrantValue w a b v := by
    intro M hM
    simp only [heckeSet, Finset.mem_filter] at hM
    obtain ⟨b0, -, b2, -, b4, -, b6, -⟩ := heckeBasis_bounds hM.2
    exact barnesBoundaryPeriod_eq_coneSum b0 b2 b4 b6 (by rw [hM.2.det]; exact hp0.ne') hw ha hb
  rw [Finset.sum_congr rfl hcone,
    ← Summable.tsum_finsetSum fun M _ => summable_coneWeight_mul hw ha hb _ _ _ _]
  have hI : barnesBoundaryPeriod w a b =
      ∑' v, coneWeight 1 0 0 1 v * quadrantValue w a b v := by
    have := barnesBoundaryPeriod_eq_coneSum (α := 1) (β := 0) (γ := 0) (δ := 1) (by norm_num)
      le_rfl le_rfl (by norm_num) (by norm_num) hw ha hb
    simpa using this
  have hP : barnesBoundaryPeriod w (p * a) (p * b) =
      ∑' v, coneWeight p 0 0 p v * quadrantValue w a b v := by
    have := barnesBoundaryPeriod_eq_coneSum (α := p) (β := 0) (γ := 0) (δ := p) hp0.le
      le_rfl le_rfl hp0.le (by simp [hp.out.ne_zero]) hw ha hb
    simpa using this
  rw [hI, hP, ← tsum_mul_left, ← (summable_coneWeight_mul hw ha hb 1 0 0 1).tsum_add
    ((summable_coneWeight_mul hw ha hb p 0 0 p).mul_left _)]
  refine tsum_congr fun v => ?_
  rw [← Finset.sum_mul]
  obtain ⟨x, y⟩ := v
  by_cases hq : 0 ≤ x ∧ 0 ≤ y
  · rw [sum_coneWeight_heckeSet_eq hq.1 hq.2]
    ring
  · simp [quadrantValue, hq]

/-- The **source Hecke operator** of determinant `p`:
`T_{p,s} f(a) = Σ_{M ∈ X_p} (γa + δ)^{−2s} f((αa + β)/(γa + δ))`. -/
def lewisHeckeOperator (p : ℕ) (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∑ M ∈ heckeSet p, (((M.2.2.1 : ℝ) * a + M.2.2.2 : ℝ) : ℂ) ^ (-(2 * s)) *
    f (((M.1 : ℝ) * a + M.2.1) / ((M.2.2.1 : ℝ) * a + M.2.2.2))

/-- The denominators of the Hecke branches are positive on the positive line. -/
theorem heckeBranch_pos {M : ℤ × ℤ × ℤ × ℤ} (hM : M ∈ heckeSet p) {a : ℝ} (ha : 0 < a) :
    0 < (M.2.2.1 : ℝ) * a + M.2.2.2 ∧ 0 < (M.1 : ℝ) * a + M.2.1 := by
  simp only [heckeSet, Finset.mem_filter] at hM
  have h := hM.2
  have hc : (0 : ℝ) ≤ M.2.2.1 := by exact_mod_cast h.c_nonneg
  have hb : (0 : ℝ) ≤ M.2.1 := by exact_mod_cast h.b_nonneg
  have hd : (0 : ℝ) < M.2.2.2 := by exact_mod_cast lt_of_le_of_lt h.b_nonneg h.b_lt
  have hα : (0 : ℝ) < M.1 := by exact_mod_cast lt_of_le_of_lt h.c_nonneg h.c_lt
  exact ⟨by positivity, by positivity⟩

/-- **The Barnes period is a `T_p`-eigenfunction**: `T_{p,w/2} P_w(·, 1) = (1 + p · p^{−w}) P_w(·, 1)`
on the positive line, `Re w > 2`. -/
theorem barnesBoundaryPeriod_lewisHecke {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    lewisHeckeOperator p (w / 2) (fun x => barnesBoundaryPeriod w x 1) a =
      (1 + p * (p : ℂ) ^ (-w)) * barnesBoundaryPeriod w a 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  unfold lewisHeckeOperator
  rw [show 2 * (w / 2) = w by ring]
  have hterm : ∀ M ∈ heckeSet p,
      (((M.2.2.1 : ℝ) * a + M.2.2.2 : ℝ) : ℂ) ^ (-w) *
        barnesBoundaryPeriod w (((M.1 : ℝ) * a + M.2.1) / ((M.2.2.1 : ℝ) * a + M.2.2.2)) 1 =
      barnesBoundaryPeriod w (M.1 * a + M.2.1 * 1) (M.2.2.1 * a + M.2.2.2 * 1) := by
    intro M hM
    obtain ⟨hc, hx⟩ := heckeBranch_pos hM ha
    have h := barnesBoundaryPeriod_scale w hc (div_pos hx hc) one_pos
    rw [mul_div_cancel₀ _ hc.ne', mul_one] at h
    rw [← h, mul_one, mul_one]
  rw [Finset.sum_congr rfl hterm, barnesBoundaryPeriod_hecke_prime hw ha one_pos]
  have h := barnesBoundaryPeriod_scale w hp0 ha one_pos
  rw [h, Complex.ofReal_natCast]
  ring

end Prime

/-- `p · p^{−w} = p^{1−w}`: the eigenvalue is `1 + p^{1−w}`. -/
theorem natCast_mul_cpow_neg {p : ℕ} (hp : p ≠ 0) (w : ℂ) :
    (p : ℂ) * (p : ℂ) ^ (-w) = (p : ℂ) ^ (1 - w) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hp), Complex.cpow_one]

/-! ### Determinant one: Farey splitting, inversion and the Lewis equation -/

open Classical in
/-- **Farey splitting** of the boundary period: `P_w(a, b) = P_w(a + b, b) + P_w(a, a + b)`. -/
theorem barnesBoundaryPeriod_farey {w : ℂ} (hw : 2 < w.re) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    barnesBoundaryPeriod w a b = barnesBoundaryPeriod w (a + b) b + barnesBoundaryPeriod w a (a + b) := by
  have h1 := barnesBoundaryPeriod_eq_coneSum (α := 1) (β := 1) (γ := 0) (δ := 1) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) hw ha hb
  have h2 := barnesBoundaryPeriod_eq_coneSum (α := 1) (β := 0) (γ := 1) (δ := 1) (by norm_num)
    le_rfl (by norm_num) (by norm_num) (by norm_num) hw ha hb
  have h0 := barnesBoundaryPeriod_eq_coneSum (α := 1) (β := 0) (γ := 0) (δ := 1) (by norm_num)
    le_rfl le_rfl (by norm_num) (by norm_num) hw ha hb
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at h0 h1 h2
  rw [h0, h1, h2, ← (summable_coneWeight_mul hw ha hb 1 1 0 1).tsum_add
    (summable_coneWeight_mul hw ha hb 1 0 1 1)]
  refine tsum_congr fun v => ?_
  rw [← add_mul]
  congr 1
  simp (disch := norm_num) only [coneWeight, inHeckeCone_iff_of_det_one]
  split_ifs <;> first | ring | (exfalso; omega)

/-- `P_w` is symmetric in its two periods. -/
theorem barnesBoundaryPeriod_comm (w : ℂ) (a b : ℝ) :
    barnesBoundaryPeriod w a b = barnesBoundaryPeriod w b a := by
  have hz (o1 o2 : ℝ) (z : ℂ) : barnesDoubleZeta o1 o2 w z = barnesDoubleZeta o2 o1 w z := by
    rw [barnesDoubleZeta, barnesDoubleZeta, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
    refine tsum_congr fun q => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, barnesLattice]
    ring_nf
  rw [barnesBoundaryPeriod, barnesBoundaryPeriod, hz a b, hz a b, add_comm]

/-- **Inversion**: `P_w(a, 1) = a^{−w} P_w(1/a, 1)`. -/
theorem barnesBoundaryPeriod_reciprocity (w : ℂ) {a : ℝ} (ha : 0 < a) :
    barnesBoundaryPeriod w a 1 = (a : ℂ) ^ (-w) * barnesBoundaryPeriod w (1 / a) 1 := by
  have h := barnesBoundaryPeriod_scale w ha one_pos (one_div_pos.mpr ha)
  rw [mul_one, mul_one_div_cancel ha.ne'] at h
  rw [h, barnesBoundaryPeriod_comm w 1 (1 / a)]

/-- **The Lewis three-term equation** of the Barnes period:
`P_w(a, 1) = P_w(a + 1, 1) + (a + 1)^{−w} P_w(a/(a + 1), 1)`. -/
theorem barnesBoundaryPeriod_three_term {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    barnesBoundaryPeriod w a 1 = barnesBoundaryPeriod w (a + 1) 1 +
      ((a + 1 : ℝ) : ℂ) ^ (-w) * barnesBoundaryPeriod w (a / (a + 1)) 1 := by
  have ha1 : 0 < a + 1 := by linarith
  have h := barnesBoundaryPeriod_scale w ha1 (div_pos ha ha1) one_pos
  rw [mul_div_cancel₀ _ ha1.ne', mul_one] at h
  rw [← h, barnesBoundaryPeriod_farey hw ha one_pos]

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
