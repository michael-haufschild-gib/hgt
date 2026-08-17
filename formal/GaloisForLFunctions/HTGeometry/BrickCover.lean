import Mathlib

/-!
# Bricks: an open cover of `ℝ^k` of order `k + 1` and arbitrarily small mesh

For each of the `k + 1` shifts `s / (k + 1)` of the integer lattice, the open cubes of half-width
slightly below half a grid step centred at the shifted lattice points are pairwise disjoint.  Every
point of `ℝ^k` lies in a cube of at least one of the `k + 1` families: in each coordinate
separately, the half-width is chosen so close to half a step that at most one of the `k + 1` shifts
can fail, and `k` coordinates cannot rule out all `k + 1` shifts.

The resulting cover of `ℝ^k` has order at most `k + 1` and mesh at most `√k · δ`, where `δ` is the
grid step.  This is the elementary half of the Lebesgue dimension of Euclidean space.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- Half-width of a brick, as a fraction of the grid step. -/
noncomputable def brickHalf (k : ℕ) : ℝ := 1 / 2 - 1 / (4 * ((k : ℝ) + 1))

/-- The shift between consecutive brick families, as a fraction of the grid step. -/
noncomputable def brickShift (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem brickShift_pos (k : ℕ) : 0 < brickShift k := by
  have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  exact div_pos one_pos this

theorem succ_mul_brickShift (k : ℕ) : ((k : ℝ) + 1) * brickShift k = 1 := by
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [brickShift]
  field_simp

theorem nat_mul_brickShift (k : ℕ) : (k : ℝ) * brickShift k = 1 - brickShift k := by
  have := succ_mul_brickShift k
  linarith [this]

theorem one_sub_two_brickHalf (k : ℕ) : 1 - 2 * brickHalf k = brickShift k / 2 := by
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [brickHalf, brickShift]
  field_simp
  ring

theorem half_sub_brickHalf (k : ℕ) : 1 / 2 - brickHalf k = brickShift k / 4 := by
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [brickHalf, brickShift]
  field_simp
  ring

theorem brickShift_le_one (k : ℕ) : brickShift k ≤ 1 := by
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [brickShift]
  rw [div_le_one h]
  linarith

theorem brickHalf_pos (k : ℕ) : 0 < brickHalf k := by
  have h1 := half_sub_brickHalf k
  have h3 := brickShift_le_one k
  linarith

/-- The brick of the `s`-th shifted grid of step `δ` around the lattice point `z`. -/
def brick (k : ℕ) (δ : ℝ) (s : Fin (k + 1)) (z : Fin k → ℤ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i, |x i - δ * ((z i : ℝ) + (s : ℕ) * brickShift k)| < δ * brickHalf k}

theorem isOpen_brick (k : ℕ) (δ : ℝ) (s : Fin (k + 1)) (z : Fin k → ℤ) :
    IsOpen (brick k δ s z) := by
  have hrw : brick k δ s z = ⋂ i : Fin k,
      (fun x : EuclideanSpace ℝ (Fin k) => x i) ⁻¹'
        Metric.ball (δ * ((z i : ℝ) + (s : ℕ) * brickShift k)) (δ * brickHalf k) := by
    ext x
    simp [brick, Metric.mem_ball, Real.dist_eq]
  rw [hrw]
  exact isOpen_iInter_of_finite fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.isOpen_preimage _ Metric.isOpen_ball

/-- Within one shifted family the bricks are pairwise disjoint. -/
theorem brick_index_eq_of_mem_inter {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {s : Fin (k + 1)}
    {z z' : Fin k → ℤ} {x : EuclideanSpace ℝ (Fin k)} (h : x ∈ brick k δ s z)
    (h' : x ∈ brick k δ s z') : z = z' := by
  funext i
  have h1 := h i
  have h2 := h' i
  rw [abs_lt] at h1 h2
  have hexp : ∀ w : ℤ, δ * ((w : ℝ) + (s : ℕ) * brickShift k)
      = δ * (w : ℝ) + δ * ((s : ℕ) * brickShift k) := fun w => by ring
  rw [hexp] at h1 h2
  have hhalf : 2 * brickHalf k < 1 := by
    have h3 := one_sub_two_brickHalf k
    have h4 := brickShift_pos k
    linarith
  have hda : 2 * (δ * brickHalf k) < δ := by nlinarith
  have hd1 : δ * ((z' i : ℝ) - (z i : ℝ)) < δ * 1 := by
    rw [mul_sub, mul_one]
    linarith [h1.2, h2.1]
  have hd2 : δ * (-1 : ℝ) < δ * ((z' i : ℝ) - (z i : ℝ)) := by
    rw [mul_sub]
    linarith [h1.1, h2.2, hda]
  have hlt1 : ((z' i : ℝ) - (z i : ℝ)) < 1 := lt_of_mul_lt_mul_left hd1 hδ.le
  have hlt2 : (-1 : ℝ) < ((z' i : ℝ) - (z i : ℝ)) := lt_of_mul_lt_mul_left hd2 hδ.le
  have hi1 : (z' i - z i : ℤ) < 1 := by
    have : ((z' i - z i : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hi2 : (-1 : ℤ) < z' i - z i := by
    have : ((-1 : ℤ) : ℝ) < ((z' i - z i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-- The mesh bound: two points of the same brick are at distance at most `√k · δ`. -/
theorem dist_le_of_mem_brick {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {s : Fin (k + 1)} {z : Fin k → ℤ}
    {x y : EuclideanSpace ℝ (Fin k)} (hx : x ∈ brick k δ s z) (hy : y ∈ brick k δ s z) :
    dist x y ≤ Real.sqrt k * δ := by
  have hhalf : 2 * brickHalf k < 1 := by
    have := one_sub_two_brickHalf k
    have := brickShift_pos k
    linarith
  have hcoord : ∀ i, dist (x i) (y i) ^ 2 ≤ δ ^ 2 := by
    intro i
    have h1 := hx i
    have h2 := hy i
    rw [abs_lt] at h1 h2
    have hd : |x i - y i| ≤ δ := by
      rw [abs_le]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    rw [Real.dist_eq]
    nlinarith [abs_nonneg (x i - y i)]
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i : Fin k, dist (x i) (y i) ^ 2 ≤ (k : ℝ) * δ ^ 2 := by
    calc ∑ i : Fin k, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin k, δ ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (k : ℝ) * δ ^ 2 := by simp
  calc Real.sqrt (∑ i : Fin k, dist (x i) (y i) ^ 2) ≤ Real.sqrt ((k : ℝ) * δ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt k * δ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]

/-- At most one of the `k + 1` shifts can be missed in a single coordinate. -/
private theorem shift_unique_aux {k : ℕ} {ti : ℝ} {s s' : Fin (k + 1)} (hlt : (s : ℕ) < (s' : ℕ))
    (hs : ∀ n : ℤ, brickHalf k ≤ |ti - (s : ℕ) * brickShift k - n|)
    (hs' : ∀ n : ℤ, brickHalf k ≤ |ti - (s' : ℕ) * brickShift k - n|) : False := by
  set c := brickShift k with hcdef
  set a := brickHalf k with hadef
  have hc : 0 < c := brickShift_pos k
  have ha1 : 1 - 2 * a = c / 2 := one_sub_two_brickHalf k
  have ha2 : 1 / 2 - a = c / 4 := half_sub_brickHalf k
  have hkc : (k : ℝ) * c = 1 - c := nat_mul_brickShift k
  set n : ℤ := round (ti - (s : ℕ) * c) with hn
  set n' : ℤ := round (ti - (s' : ℕ) * c) with hn'
  set u : ℝ := ti - (s : ℕ) * c - n with hu
  set v : ℝ := ti - (s' : ℕ) * c - n' with hv
  have hub : |u| ≤ 1 / 2 := abs_sub_round _
  have hvb : |v| ≤ 1 / 2 := abs_sub_round _
  have hua : a ≤ |u| := hs n
  have hva : a ≤ |v| := hs' n'
  rw [abs_le] at hub hvb
  have hu1 : a ≤ u ∨ u ≤ -a := by
    rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by rw [h1] at hua; exact hua)
    · exact Or.inr (by rw [h1] at hua; linarith)
  have hv1 : a ≤ v ∨ v ≤ -a := by
    rcases abs_cases v with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by rw [h1] at hva; exact hva)
    · exact Or.inr (by rw [h1] at hva; linarith)
  set jr : ℝ := ((s' : ℕ) : ℝ) - ((s : ℕ) : ℝ) with hjr
  have hj1 : 1 ≤ jr := by
    have : ((s : ℕ) : ℝ) + 1 ≤ ((s' : ℕ) : ℝ) := by exact_mod_cast hlt
    simp only [hjr]
    linarith
  have hjk : jr ≤ (k : ℝ) := by
    have h1 : ((s' : ℕ) : ℝ) ≤ (k : ℝ) := by
      have : (s' : ℕ) ≤ k := Nat.lt_succ_iff.mp s'.isLt
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ ((s : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [hjr]
    linarith
  have hA1 : c ≤ jr * c := by nlinarith
  have hA2 : jr * c ≤ 1 - c := by nlinarith
  have hdiff : u - v = jr * c + ((n' : ℝ) - (n : ℝ)) := by
    simp only [hu, hv, hjr]
    ring
  have hcases : ((n' : ℝ) - (n : ℝ)) ≤ -2 ∨ ((n' : ℝ) - (n : ℝ)) = -1 ∨
      ((n' : ℝ) - (n : ℝ)) = 0 ∨ 1 ≤ ((n' : ℝ) - (n : ℝ)) := by
    have hq : n' - n ≤ -2 ∨ n' - n = -1 ∨ n' - n = 0 ∨ 1 ≤ n' - n := by omega
    rcases hq with hq | hq | hq | hq
    · left
      have : ((n' - n : ℤ) : ℝ) ≤ ((-2 : ℤ) : ℝ) := by exact_mod_cast hq
      push_cast at this
      linarith
    · right; left
      have : ((n' - n : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by exact_mod_cast hq
      push_cast at this
      linarith
    · right; right; left
      have : ((n' - n : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by exact_mod_cast hq
      push_cast at this
      linarith
    · right; right; right
      have : ((1 : ℤ) : ℝ) ≤ ((n' - n : ℤ) : ℝ) := by exact_mod_cast hq
      push_cast at this
      linarith
  rcases hu1 with h | h <;> rcases hv1 with h' | h' <;> rcases hcases with hq | hq | hq | hq <;>
    linarith

/-- In one coordinate at most one shift is missed. -/
private theorem shift_unique {k : ℕ} {ti : ℝ} {s s' : Fin (k + 1)}
    (hs : ∀ n : ℤ, brickHalf k ≤ |ti - (s : ℕ) * brickShift k - n|)
    (hs' : ∀ n : ℤ, brickHalf k ≤ |ti - (s' : ℕ) * brickShift k - n|) : s = s' := by
  rcases lt_trichotomy (s : ℕ) (s' : ℕ) with h | h | h
  · exact absurd (shift_unique_aux h hs hs') (fun x => x)
  · exact Fin.ext h
  · exact absurd (shift_unique_aux h hs' hs) (fun x => x)

/-- **`k` coordinates cannot rule out all `k + 1` shifts.** -/
private theorem exists_good_shift (k : ℕ) (t : Fin k → ℝ) :
    ∃ s : Fin (k + 1), ∀ i, ∃ n : ℤ, |t i - (s : ℕ) * brickShift k - n| < brickHalf k := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  choose bad hbad using hcon
  have hinj : Function.Injective bad := by
    intro s s' hss
    refine shift_unique (ti := t (bad s)) (hbad s) ?_
    rw [hss]
    exact hbad s'
  have := Fintype.card_le_of_injective bad hinj
  simp only [Fintype.card_fin] at this
  omega

/-- **Every point lies in a brick.** -/
theorem exists_mem_brick (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin k)) :
    ∃ (s : Fin (k + 1)) (z : Fin k → ℤ), x ∈ brick k δ s z := by
  obtain ⟨s, hs⟩ := exists_good_shift k fun i => x i / δ
  choose z hz using hs
  refine ⟨s, z, fun i => ?_⟩
  have h := hz i
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have hrw : x i - δ * ((z i : ℝ) + (s : ℕ) * brickShift k)
      = δ * (x i / δ - (s : ℕ) * brickShift k - (z i : ℝ)) := by
    field_simp
    ring
  rw [hrw, abs_mul, abs_of_pos hδ]
  exact mul_lt_mul_of_pos_left h hδ

/-- **The bricks have order at most `k + 1`.**  Two bricks of the same shifted family that share a
point coincide, so the shift index is injective on any family of bricks through a point. -/
theorem brick_card_le {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin k))
    (T : Finset (Fin (k + 1) × (Fin k → ℤ))) (hT : ∀ p ∈ T, x ∈ brick k δ p.1 p.2) :
    T.card ≤ k + 1 := by
  classical
  have hinj : Set.InjOn Prod.fst (T : Set (Fin (k + 1) × (Fin k → ℤ))) := by
    intro p hp q hq h
    have hq' : x ∈ brick k δ p.1 q.2 := by
      rw [h]
      exact hT q hq
    exact Prod.ext h (brick_index_eq_of_mem_inter hδ (hT p hp) hq')
  calc T.card = (T.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin (k + 1)) := Finset.card_le_univ _
    _ = k + 1 := by simp

end GaloisForLFunctions.HTGeometry
