import Zeta23.Assembly.SeamMult

/-!
# Disjoint-pair Schur–Jensen slack in the multiplicity-aware rank–trace inequality

In `Zeta23.ZeroSide.RankTraceMult`, Lemma R (`rank_trace_mult_k_le`) bounds
`2c · tr(P + Q) − ‖P + Q‖_F²` from above by `∑_j k_c(m_j) + c² b`, discarding the off-diagonal
Schur–Jensen pinching slack between the diagonal of the on-line Gram matrix `Wᴴ W` and its
eigenvalues along `g_c(t) = t² − c t − ((t − c)₊)²`.

For any two distinct indices `x ≠ y` of unit multiplicity (`m_x = m_y = 1`) and norm at most one
(`‖v_x‖² ≤ 1`, `‖v_y‖² ≤ 1`), rotating `(v_x, v_y)` by a real orthogonal `2 × 2` matrix preserves
`P = W Wᴴ` identically while keeping `‖v'_x‖² + ‖v'_y‖² = ‖v_x‖² + ‖v_y‖² ≤ 2`. Whenever `c ≥ 2`,
neither rotated norm squared can cross the kink `t = c` of `k_c(t) = c² − ((c − t)₊)²`, so `k_c`
evaluates purely on its quadratic branch `2c t − t²` at both rotated vectors. Choosing the rotation
that diagonalizes the real `2 × 2` Gram block extracts the exact quadratic overlap gain
`2 ⟨v_x, v_y⟩_ℝ²` with zero loss on norms `< 1`.

Inducting over any finite family of pairwise disjoint simple pairs `(x_p, y_p)` yields the
multiplicity-aware rank–trace inequality, block bounds (`c = 2` and `c = 3`), and Seam A bounds
with the explicit disjoint-pair Gram slack retained.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace GaloisForLFunctions.IncommensurableGaborPinching

section LinearAlgebra

open Zeta23.ZeroSide.RankTraceMult

/-- Pointwise rank-two outer product invariance under a real `2 × 2` rotation with `α² + β² = 1`. -/
lemma rot_outer_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1) (u w : n → 𝕜) (a b : n) :
    ((α : 𝕜) * u a + (β : 𝕜) * w a) * starRingEnd 𝕜 ((α : 𝕜) * u b + (β : 𝕜) * w b)
      + (-(β : 𝕜) * u a + (α : 𝕜) * w a) * starRingEnd 𝕜 (-(β : 𝕜) * u b + (α : 𝕜) * w b)
      = u a * starRingEnd 𝕜 (u b) + w a * starRingEnd 𝕜 (w b) := by
  simp only [map_add, map_mul, map_neg, RCLike.conj_ofReal]
  have h1 : ((α : 𝕜) ^ 2 + (β : 𝕜) ^ 2) = 1 := by exact_mod_cast hαβ
  calc ((α : 𝕜) * u a + (β : 𝕜) * w a) * ((α : 𝕜) * (starRingEnd 𝕜) (u b) + (β : 𝕜) * (starRingEnd 𝕜) (w b))
        + (-(β : 𝕜) * u a + (α : 𝕜) * w a) * (-(β : 𝕜) * (starRingEnd 𝕜) (u b) + (α : 𝕜) * (starRingEnd 𝕜) (w b))
      = ((α : 𝕜) ^ 2 + (β : 𝕜) ^ 2) * (u a * (starRingEnd 𝕜) (u b) + w a * (starRingEnd 𝕜) (w b)) := by ring
    _ = u a * (starRingEnd 𝕜) (u b) + w a * (starRingEnd 𝕜) (w b) := by rw [h1, one_mul]

/-- Existence of unit rotation parameters `(α, β)` diagonalizing a real symmetric `2 × 2` matrix. -/
lemma exists_unit_rot_scalars (A B ρ : ℝ) :
    ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧
      ((α ^ 2 - β ^ 2) * (A - B) + 4 * α * β * ρ) ^ 2 = (A - B) ^ 2 + 4 * ρ ^ 2 := by
  set S : ℝ := (A - B) ^ 2 + 4 * ρ ^ 2
  have hS0 : 0 ≤ S := by positivity
  rcases eq_or_lt_of_le hS0 with hS | hSpos
  · refine ⟨1, 0, by norm_num, ?_⟩
    have hAB : A - B = 0 := by nlinarith [sq_nonneg (A - B), sq_nonneg ρ]
    have hρ : ρ = 0 := by nlinarith [sq_nonneg (A - B), sq_nonneg ρ]
    rw [hAB, hρ]
    simp only [S, hAB, hρ]
    norm_num
  · set D : ℝ := Real.sqrt S
    have hDpos : 0 < D := Real.sqrt_pos.mpr hSpos
    have hDsq : D ^ 2 = S := Real.sq_sqrt hS0
    have hAB_le : |A - B| ≤ D := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by simp only [S]; nlinarith [sq_nonneg ρ])
    have habs := abs_le.mp hAB_le
    have hu_pos : 0 ≤ (1 + (A - B) / D) / 2 := by
      have : -1 ≤ (A - B) / D := by rw [le_div_iff₀ hDpos]; linarith
      linarith
    have hv_pos : 0 ≤ (1 - (A - B) / D) / 2 := by
      have : (A - B) / D ≤ 1 := by rw [div_le_iff₀ hDpos]; linarith
      linarith
    set σ : ℝ := if 0 ≤ ρ then 1 else -1
    have hσ2 : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
    set α : ℝ := Real.sqrt ((1 + (A - B) / D) / 2)
    set β : ℝ := σ * Real.sqrt ((1 - (A - B) / D) / 2)
    have hα2 : α ^ 2 = (1 + (A - B) / D) / 2 := Real.sq_sqrt hu_pos
    have hβ2 : β ^ 2 = (1 - (A - B) / D) / 2 := by
      rw [mul_pow, hσ2, one_mul, Real.sq_sqrt hv_pos]
    refine ⟨α, β, by linarith, ?_⟩
    have hdiff : α ^ 2 - β ^ 2 = (A - B) / D := by linarith
    have hprod_sq : (2 * α * β) ^ 2 = (2 * ρ / D) ^ 2 := by
      calc (2 * α * β) ^ 2 = 4 * α ^ 2 * β ^ 2 := by ring
        _ = (1 + (A - B) / D) * (1 - (A - B) / D) := by rw [hα2, hβ2]; ring
        _ = (D ^ 2 - (A - B) ^ 2) / D ^ 2 := by field_simp; ring
        _ = 4 * ρ ^ 2 / D ^ 2 := by rw [hDsq]; simp only [S]; ring
        _ = (2 * ρ / D) ^ 2 := by ring
    have hprod : 2 * α * β = 2 * ρ / D := by
      have hα0 : 0 ≤ α := Real.sqrt_nonneg _
      have hr0 : 0 ≤ Real.sqrt ((1 - (A - B) / D) / 2) := Real.sqrt_nonneg _
      have hsign : (0 ≤ 2 * α * β ∧ 0 ≤ 2 * ρ / D) ∨ (2 * α * β ≤ 0 ∧ 2 * ρ / D ≤ 0) := by
        simp only [β, σ]
        split_ifs with hρ
        · left
          exact ⟨by positivity, div_nonneg (by linarith) hDpos.le⟩
        · right
          have hρ' : ρ ≤ 0 := le_of_not_ge hρ
          exact ⟨by nlinarith, div_nonpos_of_nonpos_of_nonneg (by linarith) hDpos.le⟩
      have hfac : (2 * α * β - 2 * ρ / D) * (2 * α * β + 2 * ρ / D) = 0 := by
        linarith [hprod_sq]
      rcases mul_eq_zero.mp hfac with h1 | h2
      · linarith
      · rcases hsign with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> linarith
    have hlin : (α ^ 2 - β ^ 2) * (A - B) + 4 * α * β * ρ = D := by
      rw [hdiff, show 4 * α * β * ρ = (2 * α * β) * (2 * ρ) by ring, hprod]
      calc (A - B) / D * (A - B) + 2 * ρ / D * (2 * ρ)
          = ((A - B) ^ 2 + 4 * ρ ^ 2) / D := by field_simp; ring
        _ = D ^ 2 / D := by rw [hDsq]
        _ = D := by field_simp
    rw [hlin, hDsq]

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- Squared Euclidean norm `∑_a ‖u_a‖²` of a single vector in `n → 𝕜`. -/
def vecSq (u : n → 𝕜) : ℝ :=
  ∑ a, ‖u a‖ ^ 2

/-- Real part of the standard inner product `∑_a Re (u_a · conj(w_a))` of two vectors in `n → 𝕜`. -/
def realInnerVec (u w : n → 𝕜) : ℝ :=
  ∑ a, RCLike.re (u a * starRingEnd 𝕜 (w a))

lemma realInnerVec_symm (u w : n → 𝕜) : realInnerVec u w = realInnerVec w u := by
  unfold realInnerVec
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : starRingEnd 𝕜 (u a * starRingEnd 𝕜 (w a)) = w a * starRingEnd 𝕜 (u a) := by
    rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
  rw [← h, RCLike.conj_re]

/-- Expansion of `‖α u + β w‖²` and `‖-β u + α w‖²` for real scalars `α, β`. -/
lemma vecSq_rot_apply (α β : ℝ) (u w : n → 𝕜) :
    vecSq (fun a => (α : 𝕜) * u a + (β : 𝕜) * w a)
      = α ^ 2 * vecSq u + β ^ 2 * vecSq w + 2 * α * β * realInnerVec u w ∧
    vecSq (fun a => -(β : 𝕜) * u a + (α : 𝕜) * w a)
      = β ^ 2 * vecSq u + α ^ 2 * vecSq w - 2 * α * β * realInnerVec u w := by
  have hnorm : ∀ (p q : ℝ) (x y : 𝕜),
      ‖(p : 𝕜) * x + (q : 𝕜) * y‖ ^ 2
        = p ^ 2 * ‖x‖ ^ 2 + q ^ 2 * ‖y‖ ^ 2 + 2 * p * q * RCLike.re (x * starRingEnd 𝕜 y) := by
    intro p q x y
    set z : 𝕜 := (p : 𝕜) * x + (q : 𝕜) * y
    have hz : RCLike.re (z * starRingEnd 𝕜 z) = ‖z‖ ^ 2 := by
      rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hx : RCLike.re (x * starRingEnd 𝕜 x) = ‖x‖ ^ 2 := by
      rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hy : RCLike.re (y * starRingEnd 𝕜 y) = ‖y‖ ^ 2 := by
      rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hxy : RCLike.re (y * starRingEnd 𝕜 x) = RCLike.re (x * starRingEnd 𝕜 y) := by
      have hc : starRingEnd 𝕜 (x * starRingEnd 𝕜 y) = y * starRingEnd 𝕜 x := by
        rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
      rw [← hc, RCLike.conj_re]
    rw [← hz]
    have hexp : z * starRingEnd 𝕜 z
        = ((p ^ 2 : ℝ) : 𝕜) * (x * starRingEnd 𝕜 x)
          + ((q ^ 2 : ℝ) : 𝕜) * (y * starRingEnd 𝕜 y)
          + ((p * q : ℝ) : 𝕜) * (x * starRingEnd 𝕜 y + y * starRingEnd 𝕜 x) := by
      simp only [z, map_add, map_mul, RCLike.conj_ofReal]
      push_cast
      ring
    rw [hexp, map_add, map_add, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul,
      map_add, hx, hy, hxy]
    ring
  unfold vecSq realInnerVec
  constructor
  · simp_rw [hnorm α β]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  · have hnorm' : ∀ a, ‖-(β : 𝕜) * u a + (α : 𝕜) * w a‖ ^ 2
        = β ^ 2 * ‖u a‖ ^ 2 + α ^ 2 * ‖w a‖ ^ 2 - 2 * α * β * RCLike.re (u a * starRingEnd 𝕜 (w a)) := by
      intro a
      have h := hnorm (-β) α (u a) (w a)
      push_cast at h
      linarith
    simp_rw [hnorm']
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Single-pair orthogonal rotation lemma for `kc`: when `c ≥ 2` and `vecSq u, vecSq w ≤ 1`,
rotating `(u, w)` preserves `u u* + w w*` and extracts `2 * (realInnerVec u w)^2` from `kc`. -/
lemma exists_unit_rot_kc {c : ℝ} (hc : 2 ≤ c) {u w : n → 𝕜} (hu : vecSq u ≤ 1) (hw : vecSq w ≤ 1) :
    ∃ u' w' : n → 𝕜,
      (∀ a b : n, u' a * starRingEnd 𝕜 (u' b) + w' a * starRingEnd 𝕜 (w' b)
        = u a * starRingEnd 𝕜 (u b) + w a * starRingEnd 𝕜 (w b)) ∧
      kc c (vecSq u') + kc c (vecSq w') + 2 * (realInnerVec u w) ^ 2
        ≤ kc c (vecSq u) + kc c (vecSq w) := by
  obtain ⟨α, β, hαβ, hdiag⟩ := exists_unit_rot_scalars (vecSq u) (vecSq w) (realInnerVec u w)
  let u' : n → 𝕜 := fun a => (α : 𝕜) * u a + (β : 𝕜) * w a
  let w' : n → 𝕜 := fun a => -(β : 𝕜) * u a + (α : 𝕜) * w a
  refine ⟨u', w', fun a b => rot_outer_eq hαβ u w a b, ?_⟩
  obtain ⟨hx1, hx2⟩ := vecSq_rot_apply α β u w
  set A' := vecSq u'
  set B' := vecSq w'
  have hA'0 : 0 ≤ A' := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : A' + B' = vecSq u + vecSq w := by
    calc A' + B' = (α ^ 2 + β ^ 2) * (vecSq u + vecSq w) := by rw [hx1, hx2]; ring
      _ = vecSq u + vecSq w := by rw [hαβ, one_mul]
  have hdiff : A' - B' = (α ^ 2 - β ^ 2) * (vecSq u - vecSq w) + 4 * α * β * realInnerVec u w := by
    rw [hx1, hx2]; ring
  have hsq_sum : A' ^ 2 + B' ^ 2 = vecSq u ^ 2 + vecSq w ^ 2 + 2 * (realInnerVec u w) ^ 2 := by
    have h1 : 2 * (A' ^ 2 + B' ^ 2) = (A' + B') ^ 2 + (A' - B') ^ 2 := by ring
    rw [hsum, hdiff, hdiag] at h1
    linarith
  have h2c : 2 * c * A' + 2 * c * B' = 2 * c * vecSq u + 2 * c * vecSq w := by
    have := congrArg (fun t => 2 * c * t) hsum
    linarith
  have hA'c : A' ≤ c := by linarith
  have hB'c : B' ≤ c := by linarith
  have huc : vecSq u ≤ c := by linarith
  have hwc : vecSq w ≤ c := by linarith
  rw [kc_of_le hA'c, kc_of_le hB'c, kc_of_le huc, kc_of_le hwc]
  linarith

section DisjointPairs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Simultaneous orthogonal column rotations on pairwise disjoint unit-multiplicity pairs. -/
lemma exists_disjointPairs_rot {κ : Type*} (r : Finset κ) (x y : κ → ι)
    {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (hxsq : ∀ j, xsq v j ≤ 1)
    {c : ℝ} (hc : 2 ≤ c)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hm1 : ∀ p ∈ r, m (x p) = 1 ∧ m (y p) = 1)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset ι))) :
    ∃ v' : ι → n → 𝕜,
      Pmat m v' = Pmat m v ∧
      (∀ j, j ∉ r.biUnion (fun p => ({x p, y p} : Finset ι)) → v' j = v j) ∧
      (∀ p ∈ r, kc c (m (x p) * xsq v' (x p)) + kc c (m (y p) * xsq v' (y p))
          + 2 * (realInnerVec (v (x p)) (v (y p))) ^ 2
        ≤ kc c (m (x p)) + kc c (m (y p))) := by
  classical
  have hxsq' : ∀ j, vecSq (v j) ≤ 1 := hxsq
  induction r using Finset.induction_on with
  | empty =>
    exact ⟨v, rfl, fun _ _ => rfl, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  | insert p₀ s hp₀ ih =>
    have hne_s : ∀ p ∈ s, x p ≠ y p := fun p hp => hne p (Finset.mem_insert_of_mem hp)
    have hm1_s : ∀ p ∈ s, m (x p) = 1 ∧ m (y p) = 1 := fun p hp => hm1 p (Finset.mem_insert_of_mem hp)
    have hdisj_s : (s : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset ι)) :=
      hdisj.subset (Finset.subset_insert p₀ s)
    obtain ⟨v₁, hP₁, hv₁_out, hv₁_pairs⟩ := ih hne_s hm1_s hdisj_s
    have hp₀_ne : x p₀ ≠ y p₀ := hne p₀ (Finset.mem_insert_self p₀ s)
    have hp₀_m : m (x p₀) = 1 ∧ m (y p₀) = 1 := hm1 p₀ (Finset.mem_insert_self p₀ s)
    have hp₀_disj : ∀ q ∈ s, Disjoint ({x p₀, y p₀} : Finset ι) ({x q, y q} : Finset ι) :=
      fun q hq => hdisj (Finset.mem_insert_self p₀ s) (Finset.mem_insert_of_mem hq)
        (fun h => hp₀ (h ▸ hq))
    have hx₀_out : x p₀ ∉ s.biUnion (fun p => ({x p, y p} : Finset ι)) := by
      rw [Finset.mem_biUnion]; rintro ⟨q, hq, hxq⟩
      exact Finset.disjoint_left.mp (hp₀_disj q hq) (by simp) hxq
    have hy₀_out : y p₀ ∉ s.biUnion (fun p => ({x p, y p} : Finset ι)) := by
      rw [Finset.mem_biUnion]; rintro ⟨q, hq, hyq⟩
      exact Finset.disjoint_left.mp (hp₀_disj q hq) (by simp) hyq
    obtain ⟨u', w', hrot_out, hrot_kc⟩ :=
      exists_unit_rot_kc hc (hxsq' (x p₀)) (hxsq' (y p₀))
    let v₂ : ι → n → 𝕜 := Function.update (Function.update v₁ (x p₀) u') (y p₀) w'
    have hv₂_x : v₂ (x p₀) = u' := by
      simp [v₂, Function.update_of_ne hp₀_ne]
    have hv₂_y : v₂ (y p₀) = w' := by
      simp [v₂]
    have hv₂_other : ∀ j, j ≠ x p₀ → j ≠ y p₀ → v₂ j = v₁ j := by
      intro j hjx hjy
      simp [v₂, Function.update_of_ne hjy, Function.update_of_ne hjx]
    refine ⟨v₂, ?_, ?_, ?_⟩
    · rw [← hP₁]
      ext a b
      rw [Pmat_apply hm v₂ a b, Pmat_apply hm v₁ a b]
      set pair₀ : Finset ι := {x p₀, y p₀}
      rw [← Finset.sum_sdiff (Finset.subset_univ pair₀),
        ← Finset.sum_sdiff (s₁ := pair₀) (Finset.subset_univ pair₀)]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_sdiff] at hj
        have hjx : j ≠ x p₀ := fun h => hj.2 (by simp [pair₀, h])
        have hjy : j ≠ y p₀ := fun h => hj.2 (by simp [pair₀, h])
        rw [hv₂_other j hjx hjy]
      · simp only [pair₀, Finset.sum_pair hp₀_ne, hp₀_m.1, hp₀_m.2, RCLike.ofReal_one, one_mul,
          hv₂_x, hv₂_y, hv₁_out (x p₀) hx₀_out, hv₁_out (y p₀) hy₀_out]
        exact hrot_out a b
    · intro j hj
      rw [Finset.biUnion_insert, Finset.mem_union, not_or] at hj
      have hjx : j ≠ x p₀ := fun h => hj.1 (by simp [h])
      have hjy : j ≠ y p₀ := fun h => hj.1 (by simp [h])
      rw [hv₂_other j hjx hjy, hv₁_out j hj.2]
    · intro p hp
      rcases Finset.mem_insert.mp hp with hp_eq | hps
      · rw [hp_eq]
        have hxsq_x : xsq v₂ (x p₀) = vecSq u' := by unfold xsq vecSq; rw [hv₂_x]
        have hxsq_y : xsq v₂ (y p₀) = vecSq w' := by unfold xsq vecSq; rw [hv₂_y]
        rw [hp₀_m.1, hp₀_m.2, one_mul, one_mul, hxsq_x, hxsq_y]
        have hkx : kc c (vecSq (v (x p₀))) ≤ kc c 1 := kc_mono (by linarith) (hxsq' (x p₀))
        have hky : kc c (vecSq (v (y p₀))) ≤ kc c 1 := kc_mono (by linarith) (hxsq' (y p₀))
        linarith
      · have hd := Finset.disjoint_left.mp (hp₀_disj p hps)
        have hpx : x p ≠ x p₀ := fun h =>
          hd (h ▸ Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
        have hpy : x p ≠ y p₀ := fun h =>
          hd (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            (Finset.mem_insert_self _ _)
        have hqx : y p ≠ x p₀ := fun h =>
          hd (h ▸ Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hqy : y p ≠ y p₀ := fun h =>
          hd (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hxsq_xp : xsq v₂ (x p) = xsq v₁ (x p) := by unfold xsq; rw [hv₂_other (x p) hpx hpy]
        have hxsq_yp : xsq v₂ (y p) = xsq v₁ (y p) := by unfold xsq; rw [hv₂_other (y p) hqx hqy]
        rw [hxsq_xp, hxsq_yp]
        exact hv₁_pairs p hps

/-- **Lemma R with disjoint-pair Schur–Jensen slack (`c ≥ 2`).**
For any pairwise disjoint family `r` of unit-multiplicity pairs `(x_p, y_p)` in `ι`,
`2c · tr(P + Q) − ‖P + Q‖_F² + 2 ∑_{p ∈ r} ⟨v_{x_p}, v_{y_p}⟩_ℝ² ≤ ∑_j k_c(m_j) + c² b`. -/
theorem rank_trace_mult_k_disjointPairs [DecidableEq n] {κ : Type*} (r : Finset κ) (x y : κ → ι)
    {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (hxsq : ∀ j, xsq v j ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 2 ≤ c)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hm1 : ∀ p ∈ r, m (x p) = 1 ∧ m (y p) = 1)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset ι))) :
    2 * c * rtrace (Pmat m v + Q) - frobSq (Pmat m v + Q)
        + 2 * ∑ p ∈ r, (realInnerVec (v (x p)) (v (y p))) ^ 2
      ≤ (∑ j, kc c (m j)) + c ^ 2 * b := by
  classical
  obtain ⟨v', hP, hv'_out, hv'_pairs⟩ :=
    exists_disjointPairs_rot r x y hm v hxsq hc hne hm1 hdisj
  have hc0 : 0 < c := by linarith
  have hR := rank_trace_mult_k hm v' hQ hb hc0
  rw [hP] at hR
  set U : Finset ι := r.biUnion (fun p => ({x p, y p} : Finset ι))
  have hsplit_v' : ∑ j : ι, kc c (m j * xsq v' j)
      = ∑ j ∈ Finset.univ \ U, kc c (m j * xsq v' j) + ∑ j ∈ U, kc c (m j * xsq v' j) :=
    (Finset.sum_sdiff (Finset.subset_univ U)).symm
  have hsplit_m : ∑ j : ι, kc c (m j)
      = ∑ j ∈ Finset.univ \ U, kc c (m j) + ∑ j ∈ U, kc c (m j) :=
    (Finset.sum_sdiff (Finset.subset_univ U)).symm
  have hrest : ∑ j ∈ Finset.univ \ U, kc c (m j * xsq v' j) ≤ ∑ j ∈ Finset.univ \ U, kc c (m j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_sdiff] at hj
    have hxsq_eq : xsq v' j = xsq v j := by simp only [xsq, hv'_out j hj.2]
    rw [hxsq_eq]
    exact kc_mono hc0.le (by nlinarith [hm j, hxsq j])
  have hU_v' : ∑ j ∈ U, kc c (m j * xsq v' j)
      = ∑ p ∈ r, (kc c (m (x p) * xsq v' (x p)) + kc c (m (y p) * xsq v' (y p))) := by
    rw [Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun p hp => Finset.sum_pair (hne p hp)
  have hU_m : ∑ j ∈ U, kc c (m j) = ∑ p ∈ r, (kc c (m (x p)) + kc c (m (y p))) := by
    rw [Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun p hp => Finset.sum_pair (hne p hp)
  have hpairs_sum : ∑ p ∈ r, (kc c (m (x p) * xsq v' (x p)) + kc c (m (y p) * xsq v' (y p)))
      + 2 * ∑ p ∈ r, (realInnerVec (v (x p)) (v (y p))) ^ 2
      ≤ ∑ p ∈ r, (kc c (m (x p)) + kc c (m (y p))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hv'_pairs
  linarith

end DisjointPairs

end LinearAlgebra

/-! ## Block-level and Seam A bounds with disjoint-pair slack -/

section BlockAndSeam

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult Zeta23.Assembly

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- `c = 2` block bound with disjoint-pair Schur–Jensen slack on `D.S₁`. -/
lemma mult_two_disjointPairs (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c₀)
    {κ : Type*} (r : Finset κ) (x y : κ → ι)
    (hxS₁ : ∀ p ∈ r, x p ∈ D.S₁) (hyS₁ : ∀ p ∈ r, y p ∈ D.S₁)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset ι))) :
    4 * rtrace (D.blockP c₀ + D.blockQ c₀) - frobSq (D.blockP c₀ + D.blockQ c₀)
        - 2 * (D.Ncount : ℝ)
        + 2 * ∑ p ∈ r, (c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re) ^ 2
      ≤ (D.s₁ : ℝ) := by
  classical
  have hon_of_S₁ : ∀ {z : ι}, z ∈ D.S₁ → z ∈ D.onLine := fun {z} hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have hm_of_S₁ : ∀ {z : ι}, z ∈ D.S₁ → D.m z = 1 := fun {z} hz =>
    (Finset.mem_filter.mp hz).2.2
  by_cases hr : r = ∅
  · subst hr
    simp only [Finset.sum_empty, mul_zero, add_zero]
    exact D.mult_two Pr hc₀ hPois
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hr
    let z₀ : D.onLine := ⟨x p₀, hon_of_S₁ (hxS₁ p₀ hp₀)⟩
    let x' : κ → D.onLine := fun p =>
      if hp : p ∈ r then ⟨x p, hon_of_S₁ (hxS₁ p hp)⟩ else z₀
    let y' : κ → D.onLine := fun p =>
      if hp : p ∈ r then ⟨y p, hon_of_S₁ (hyS₁ p hp)⟩ else z₀
    have hx'_val : ∀ {p : κ}, p ∈ r → (x' p : ι) = x p := fun {p} hp => by simp [x', hp]
    have hy'_val : ∀ {p : κ}, p ∈ r → (y' p : ι) = y p := fun {p} hp => by simp [y', hp]
    have hne' : ∀ p ∈ r, x' p ≠ y' p := by
      intro p hp h
      apply hne p hp
      rw [← hx'_val hp, ← hy'_val hp, h]
    have hm1' : ∀ p ∈ r, D.mhat (x' p) = 1 ∧ D.mhat (y' p) = 1 := by
      intro p hp
      simp only [ZeroBlockData.mhat, hx'_val hp, hy'_val hp]
      exact ⟨by exact_mod_cast hm_of_S₁ (hxS₁ p hp), by exact_mod_cast hm_of_S₁ (hyS₁ p hp)⟩
    have hdisj' : (r : Set κ).PairwiseDisjoint (fun p => ({x' p, y' p} : Finset D.onLine)) := by
      intro p hp q hq hpq
      have hp_mem : p ∈ r := hp
      have hq_mem : q ∈ r := hq
      refine Finset.disjoint_left.mpr fun z hzp hzq => ?_
      have hz1 : (z : ι) ∈ ({x p, y p} : Finset ι) := by
        rcases Finset.mem_insert.mp hzp with rfl | hzy
        · rw [hx'_val hp_mem]; exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp hzy, hy'_val hp_mem]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hz2 : (z : ι) ∈ ({x q, y q} : Finset ι) := by
        rcases Finset.mem_insert.mp hzq with rfl | hzy
        · rw [hx'_val hq_mem]; exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp hzy, hy'_val hq_mem]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact Finset.disjoint_left.mp (hdisj hp hq hpq) hz1 hz2
    have hR := rank_trace_mult_k_disjointPairs (𝕜 := ℂ) r x' y'
      (fun z => D.mhat_nonneg z) (D.vhat c₀) (D.xsq_vhat_le hc₀ hPois)
      (D.blockQ_isHermitian c₀) (D.posIndex_blockQ_le Pr hc₀) (c := 2) le_rfl
      hne' hm1' hdisj'
    rw [← D.blockP_eq_Pmat hc₀] at hR
    have hinner : ∀ p ∈ r,
        realInnerVec (D.vhat c₀ (x' p)) (D.vhat c₀ (y' p))
          = c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re := by
      intro p hp
      have hxon : D.σ (x p) = x p := (D.mem_onLine).mp (hon_of_S₁ (hxS₁ p hp))
      have hyon : D.σ (y p) = y p := (D.mem_onLine).mp (hon_of_S₁ (hyS₁ p hp))
      have hx_im : ∀ k, (D.v (x p) k).im = 0 := by
        intro k
        have hst := congrFun (D.star_v_of_onLine hxon) k
        rw [Pi.star_apply, RCLike.star_def, Complex.ext_iff] at hst
        simp only [Complex.conj_im] at hst
        linarith [hst.2]
      have hy_im : ∀ k, (D.v (y p) k).im = 0 := by
        intro k
        have hst := congrFun (D.star_v_of_onLine hyon) k
        rw [Pi.star_apply, RCLike.star_def, Complex.ext_iff] at hst
        simp only [Complex.conj_im] at hst
        linarith [hst.2]
      unfold realInnerVec ZeroBlockData.vhat
      rw [hx'_val hp, hy'_val hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : Real.sqrt c₀ * Real.sqrt c₀ = c₀ := Real.mul_self_sqrt hc₀.le
      rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul, hsq]
      simp only [RCLike.re_eq_complex_re, Complex.div_ofReal_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, hx_im k, hy_im k]
      ring
    have hsum_eq : ∑ p ∈ r, (realInnerVec (D.vhat c₀ (x' p)) (D.vhat c₀ (y' p))) ^ 2
        = ∑ p ∈ r, (c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re) ^ 2 :=
      Finset.sum_congr rfl fun p hp => by rw [hinner p hp]
    rw [hsum_eq] at hR
    have hk : ∑ z : D.onLine, kc 2 (D.mhat z) = 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) := by
      have := sum_kc_two_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
      simp only [ZeroBlockData.mhat] at this ⊢
      rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => 2 ≤ n),
        D.card_onLine_m_eq_one]
      have h2 : (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
        unfold ZeroBlockData.s₂ ZeroBlockData.S₂ ZeroBlockData.onLine; rw [Finset.filter_filter]
      rw [h2]
    have hN' : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount :=
      by exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
    rw [hk] at hR
    norm_num at hR
    linarith

/-- `c = 3` block bound with disjoint-pair Schur–Jensen slack on `D.S₁`. -/
lemma mult_three_disjointPairs (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c₀)
    {κ : Type*} (r : Finset κ) (x y : κ → ι)
    (hxS₁ : ∀ p ∈ r, x p ∈ D.S₁) (hyS₁ : ∀ p ∈ r, y p ∈ D.S₁)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset ι))) :
    6 * rtrace (D.blockP c₀ + D.blockQ c₀) - frobSq (D.blockP c₀ + D.blockQ c₀)
        - 3 * (D.Ncount : ℝ)
        + 2 * ∑ p ∈ r, (c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re) ^ 2
      ≤ 2 * (Fintype.card ι : ℝ) := by
  classical
  have hon_of_S₁ : ∀ {z : ι}, z ∈ D.S₁ → z ∈ D.onLine := fun {z} hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have hm_of_S₁ : ∀ {z : ι}, z ∈ D.S₁ → D.m z = 1 := fun {z} hz =>
    (Finset.mem_filter.mp hz).2.2
  by_cases hr : r = ∅
  · subst hr
    simp only [Finset.sum_empty, mul_zero, add_zero]
    exact D.mult_three Pr hc₀ hPois
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hr
    let z₀ : D.onLine := ⟨x p₀, hon_of_S₁ (hxS₁ p₀ hp₀)⟩
    let x' : κ → D.onLine := fun p =>
      if hp : p ∈ r then ⟨x p, hon_of_S₁ (hxS₁ p hp)⟩ else z₀
    let y' : κ → D.onLine := fun p =>
      if hp : p ∈ r then ⟨y p, hon_of_S₁ (hyS₁ p hp)⟩ else z₀
    have hx'_val : ∀ {p : κ}, p ∈ r → (x' p : ι) = x p := fun {p} hp => by simp [x', hp]
    have hy'_val : ∀ {p : κ}, p ∈ r → (y' p : ι) = y p := fun {p} hp => by simp [y', hp]
    have hne' : ∀ p ∈ r, x' p ≠ y' p := by
      intro p hp h
      apply hne p hp
      rw [← hx'_val hp, ← hy'_val hp, h]
    have hm1' : ∀ p ∈ r, D.mhat (x' p) = 1 ∧ D.mhat (y' p) = 1 := by
      intro p hp
      simp only [ZeroBlockData.mhat, hx'_val hp, hy'_val hp]
      exact ⟨by exact_mod_cast hm_of_S₁ (hxS₁ p hp), by exact_mod_cast hm_of_S₁ (hyS₁ p hp)⟩
    have hdisj' : (r : Set κ).PairwiseDisjoint (fun p => ({x' p, y' p} : Finset D.onLine)) := by
      intro p hp q hq hpq
      have hp_mem : p ∈ r := hp
      have hq_mem : q ∈ r := hq
      refine Finset.disjoint_left.mpr fun z hzp hzq => ?_
      have hz1 : (z : ι) ∈ ({x p, y p} : Finset ι) := by
        rcases Finset.mem_insert.mp hzp with rfl | hzy
        · rw [hx'_val hp_mem]; exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp hzy, hy'_val hp_mem]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hz2 : (z : ι) ∈ ({x q, y q} : Finset ι) := by
        rcases Finset.mem_insert.mp hzq with rfl | hzy
        · rw [hx'_val hq_mem]; exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp hzy, hy'_val hq_mem]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact Finset.disjoint_left.mp (hdisj hp hq hpq) hz1 hz2
    have hR := rank_trace_mult_k_disjointPairs (𝕜 := ℂ) r x' y'
      (fun z => D.mhat_nonneg z) (D.vhat c₀) (D.xsq_vhat_le hc₀ hPois)
      (D.blockQ_isHermitian c₀) (D.posIndex_blockQ_le Pr hc₀) (c := 3) (by norm_num)
      hne' hm1' hdisj'
    rw [← D.blockP_eq_Pmat hc₀] at hR
    have hinner : ∀ p ∈ r,
        realInnerVec (D.vhat c₀ (x' p)) (D.vhat c₀ (y' p))
          = c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re := by
      intro p hp
      have hxon : D.σ (x p) = x p := (D.mem_onLine).mp (hon_of_S₁ (hxS₁ p hp))
      have hyon : D.σ (y p) = y p := (D.mem_onLine).mp (hon_of_S₁ (hyS₁ p hp))
      have hx_im : ∀ k, (D.v (x p) k).im = 0 := by
        intro k
        have hst := congrFun (D.star_v_of_onLine hxon) k
        rw [Pi.star_apply, RCLike.star_def, Complex.ext_iff] at hst
        simp only [Complex.conj_im] at hst
        linarith [hst.2]
      have hy_im : ∀ k, (D.v (y p) k).im = 0 := by
        intro k
        have hst := congrFun (D.star_v_of_onLine hyon) k
        rw [Pi.star_apply, RCLike.star_def, Complex.ext_iff] at hst
        simp only [Complex.conj_im] at hst
        linarith [hst.2]
      unfold realInnerVec ZeroBlockData.vhat
      rw [hx'_val hp, hy'_val hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : Real.sqrt c₀ * Real.sqrt c₀ = c₀ := Real.mul_self_sqrt hc₀.le
      rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul, hsq]
      simp only [RCLike.re_eq_complex_re, Complex.div_ofReal_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, hx_im k, hy_im k]
      ring
    have hsum_eq : ∑ p ∈ r, (realInnerVec (D.vhat c₀ (x' p)) (D.vhat c₀ (y' p))) ^ 2
        = ∑ p ∈ r, (c₀⁻¹ * ∑ k : d, (D.v (x p) k).re * (D.v (y p) k).re) ^ 2 :=
      Finset.sum_congr rfl fun p hp => by rw [hinner p hp]
    rw [hsum_eq] at hR
    set a₁ : ℝ := ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ)
    set a₂ : ℝ := ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ)
    set a₃ : ℝ := ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ)
    have hk : ∑ z : D.onLine, kc 3 (D.mhat z) = 5 * a₁ + 8 * a₂ + 9 * a₃ := by
      have := sum_kc_three_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
      simp only [ZeroBlockData.mhat] at this ⊢
      rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => n = 2),
        D.card_sub_filter (fun n => 3 ≤ n)]
    have hs1 : a₁ = D.s₁ := by simp only [a₁]; rw [D.card_onLine_m_eq_one]
    have hs2 : a₂ + a₃ = D.s₂ := by simp only [a₂, a₃]; exact_mod_cast D.card_two_add_card_ge_three
    have hNon : a₁ + 2 * a₂ + 3 * a₃ ≤ D.Non := D.Non_ge_weighted
    have hN : (D.Non : ℝ) + 2 * Pr.p ≤ D.Ncount := by exact_mod_cast D.Non_add_two_p_le_Ncount Pr
    have hcard : (Fintype.card ι : ℝ) = D.s₁ + D.s₂ + 2 * Pr.p := by exact_mod_cast D.card_eq Pr
    have ha₂ : 0 ≤ a₂ := Nat.cast_nonneg _
    have ha₃ : 0 ≤ a₃ := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ Pr.p := Nat.cast_nonneg _
    rw [hk] at hR
    norm_num at hR
    linarith

end Block

/-- Normalized finite-grid inner product `(a L²)⁻¹ ∑_{k<d} φ̂_R(γ_x − τ_k) φ̂_R(γ_y − τ_k)` of two
points in `ZI Z T` at parameter package `P` and height `T`. -/
def pairGridOverlap (Z : ZeroConfig) (P : Params) (T : ℝ) (x y : ZI Z T) : ℝ :=
  (P.a T * P.L T ^ 2)⁻¹ *
    ∑ k : Fin (P.d T), P.phiHatR T ((x : ℂ).im - P.tau T k) * P.phiHatR T ((y : ℂ).im - P.tau T k)

lemma block_v_re_eq_phiHatR {Z : ZeroConfig} {P : Params} {T : ℝ}
    (hconj : PhiHatConj T P) {z : ZI Z T} (hz : z ∈ (blockData Z T P hconj).S₁)
    (k : Fin (P.d T)) :
    ((blockData Z T P hconj).v z k).re = P.phiHatR T ((z : ℂ).im - P.tau T k) := by
  have hre : (z : ℂ).re = 1 / 2 :=
    (mkData_σ_eq_iff Z T _ _ z).mp (Finset.mem_filter.mp hz).2.1
  simp only [blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hre, ← Complex.ofReal_sub]
  rfl

/-- **Seam A (`c = 2`, simple critical zeros) with disjoint-pair Schur–Jensen slack.** -/
theorem seamA_mult2_disjointPairs {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {κ : Type*} (r : Finset κ) (x y : κ → ZI Z T)
    (hxS₁ : ∀ p ∈ r, x p ∈ (blockData Z T P hconj).S₁)
    (hyS₁ : ∀ p ∈ r, y p ∈ (blockData Z T P hconj).S₁)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI Z T)))) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      + 2 * ∑ p ∈ r, (pairGridOverlap Z P T (x p) (y p)) ^ 2
      ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hc₀ : 0 < P.a T * P.L T ^ 2 := by positivity
  have hcore := mult_two_disjointPairs (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) hc₀ (sum_normSq_v_le Z T P hconj hreal hPois)
    r x y hxS₁ hyS₁ hne hdisj
  have hoverlap : ∑ p ∈ r,
      ((P.a T * P.L T ^ 2)⁻¹ * ∑ k : Fin (P.d T),
        ((blockData Z T P hconj).v (x p) k).re * ((blockData Z T P hconj).v (y p) k).re) ^ 2
      = ∑ p ∈ r, (pairGridOverlap Z P T (x p) (y p)) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold pairGridOverlap
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [block_v_re_eq_phiHatR hconj (hxS₁ p hp) k, block_v_re_eq_phiHatR hconj (hyS₁ p hp) k]
  rw [hoverlap] at hcore
  rw [← hatP, ← hatQ, ← hat_Az_eq_hatP_add_hatQ Z T P hconj] at hcore
  have hNcnt : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    dsimp only [blockData]
    exact_mod_cast (NIprime_eq_mk Z T _ (evalVec_reflect hconj)).symm
  have hs1_eq : ((blockData Z T P hconj).s₁ : ℝ) = (Z.s1 T : ℝ) := by
    dsimp only [blockData]
    exact_mod_cast (s1_eq_mk Z T _ (evalVec_reflect hconj)).symm
  rw [hNcnt, hs1_eq] at hcore
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

/-- **Seam A (`c = 3`, distinct zeros) with disjoint-pair Schur–Jensen slack.** -/
theorem seamA_mult3_disjointPairs {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {κ : Type*} (r : Finset κ) (x y : κ → ZI Z T)
    (hxS₁ : ∀ p ∈ r, x p ∈ (blockData Z T P hconj).S₁)
    (hyS₁ : ∀ p ∈ r, y p ∈ (blockData Z T P hconj).S₁)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hdisj : (r : Set κ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI Z T)))) :
    6 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 3 * (Z.N T (2 * T) : ℝ)
      - 5 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (6 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      + 2 * ∑ p ∈ r, (pairGridOverlap Z P T (x p) (y p)) ^ 2
      ≤ 2 * (Z.Nd T (2 * T) : ℝ) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hc₀ : 0 < P.a T * P.L T ^ 2 := by positivity
  have hcore := mult_three_disjointPairs (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) hc₀ (sum_normSq_v_le Z T P hconj hreal hPois)
    r x y hxS₁ hyS₁ hne hdisj
  have hoverlap : ∑ p ∈ r,
      ((P.a T * P.L T ^ 2)⁻¹ * ∑ k : Fin (P.d T),
        ((blockData Z T P hconj).v (x p) k).re * ((blockData Z T P hconj).v (y p) k).re) ^ 2
      = ∑ p ∈ r, (pairGridOverlap Z P T (x p) (y p)) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold pairGridOverlap
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [block_v_re_eq_phiHatR hconj (hxS₁ p hp) k, block_v_re_eq_phiHatR hconj (hyS₁ p hp) k]
  rw [hoverlap] at hcore
  rw [← hatP, ← hatQ, ← hat_Az_eq_hatP_add_hatQ Z T P hconj] at hcore
  have hNcnt : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    dsimp only [blockData]
    exact_mod_cast (NIprime_eq_mk Z T _ (evalVec_reflect hconj)).symm
  have hcardZ : (Fintype.card (ZI Z T) : ℝ) = ((Z.ZIprime T).ncard : ℝ) := by
    have h1 := ZeroBlockData.card_eq (mkData Z T (evalVec Z T P) (evalVec_reflect hconj))
      (mkPairReps Z T _ (evalVec_reflect hconj))
    rw [← s1_eq_mk Z T _ (evalVec_reflect hconj),
      ← s2_eq_mk Z T _ (evalVec_reflect hconj),
      ← p_eq_mk Z T _ (evalVec_reflect hconj),
      ← ncard_ZIprime_eq Z T] at h1
    exact_mod_cast h1
  rw [hNcnt, hcardZ] at hcore
  have hpert := ctr_sub_frobSq_perturb 6 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hZd : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hZd]

end BlockAndSeam

end GaloisForLFunctions.IncommensurableGaborPinching
