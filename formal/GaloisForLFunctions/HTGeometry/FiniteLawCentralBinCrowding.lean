import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The central-bin crowding floor of a finite law

A finite probability law on the reals cannot spread its pair mass arbitrarily thinly.  Chebyshev's
inequality confines three quarters of the mass to an interval of length four standard deviations;
cutting that interval into half-open cells of width `δ` and applying Cauchy–Schwarz forces one cell
to be heavy.  Two independent samples landing in a common cell differ by less than `δ`, so the
resulting mass is charged either to exact collisions or to strictly near, distinct pairs.

The conclusion is a lower bound of order `δ / (δ + 4σ)` on the near-pair mass *minus* the collision
mass.  Nothing here is asymptotic and no independence structure is used: the law is an arbitrary
finite weighting, and the centre is an arbitrary real number.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Fintype A]

/-- Mass of all ordered pairs carrying the same value. -/
noncomputable def finiteLawCollisionMass (a X : A → ℝ) : ℝ :=
  ∑ α, ∑ β, if X α = X β then a α * a β else 0

/-- Mass of all ordered pairs whose values are distinct and closer than `δ`. -/
noncomputable def finiteLawNearMass (a X : A → ℝ) (δ : ℝ) : ℝ :=
  ∑ α, ∑ β, if 0 < |X α - X β| ∧ |X α - X β| < δ then a α * a β else 0

/-- Mass of all ordered pairs whose values are closer than `δ`, collisions included. -/
noncomputable def finiteLawWithinMass (a X : A → ℝ) (δ : ℝ) : ℝ :=
  ∑ α, ∑ β, if |X α - X β| < δ then a α * a β else 0

/-- Splitting a `δ`-close pair according to whether its two values agree. -/
theorem finiteLawWithinMass_eq_collision_add_near (a X : A → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    finiteLawWithinMass a X δ = finiteLawCollisionMass a X + finiteLawNearMass a X δ := by
  classical
  unfold finiteLawWithinMass finiteLawCollisionMass finiteLawNearMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases h : X α = X β
  · have hz : |X α - X β| = 0 := by rw [h]; simp
    rw [if_pos (by rw [hz]; exact hδ), if_pos h, if_neg (by rw [hz]; simp)]
    ring
  · have hpos : 0 < |X α - X β| := abs_pos.mpr (sub_ne_zero.mpr h)
    by_cases h2 : |X α - X β| < δ
    · rw [if_pos h2, if_neg h, if_pos ⟨hpos, h2⟩]
      ring
    · rw [if_neg h2, if_neg h, if_neg (fun hc => h2 hc.2)]
      ring

theorem finiteLawNearMass_nonneg {a X : A → ℝ} (hnn : ∀ α, 0 ≤ a α) (δ : ℝ) :
    0 ≤ finiteLawNearMass a X δ := by
  classical
  unfold finiteLawNearMass
  refine Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun β _ => ?_
  split_ifs
  · exact mul_nonneg (hnn α) (hnn β)
  · exact le_rfl

/-- Two reals with the same `δ`-cell index differ by less than `δ`. -/
private theorem abs_sub_lt_of_floor_div_eq {x y u δ : ℝ} (hδ : 0 < δ)
    (h : ⌊(x - u) / δ⌋ = ⌊(y - u) / δ⌋) : |x - y| < δ := by
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have h1 : ((⌊(x - u) / δ⌋ : ℤ) : ℝ) ≤ (x - u) / δ := Int.floor_le _
  have h2 : (x - u) / δ < ((⌊(x - u) / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : ((⌊(y - u) / δ⌋ : ℤ) : ℝ) ≤ (y - u) / δ := Int.floor_le _
  have h4 : (y - u) / δ < ((⌊(y - u) / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [h] at h1 h2
  have hx : (x - u) / δ - (y - u) / δ < 1 := by linarith
  have hy : (y - u) / δ - (x - u) / δ < 1 := by linarith
  have hxy : (x - u) / δ - (y - u) / δ = (x - y) / δ := by field_simp; ring
  have hyx : (y - u) / δ - (x - u) / δ = (y - x) / δ := by field_simp; ring
  rw [hxy] at hx
  rw [hyx] at hy
  have hx' : x - y < δ := by
    have := (div_lt_one hδ).mp hx
    linarith
  have hy' : y - x < δ := by
    have := (div_lt_one hδ).mp hy
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- Chebyshev's inequality for a finite law: at most a quarter of the mass sits at distance
`2σ` or more from the centre. -/
private theorem finiteLaw_tail_le_quarter {a X : A → ℝ} (hnn : ∀ α, 0 ≤ a α)
    {m V : ℝ} (hV : V = ∑ α, a α * (X α - m) ^ (2 : ℕ)) (hVpos : 0 < V) :
    ∑ α ∈ Finset.univ.filter (fun α => ¬ (|X α - m| < 2 * Real.sqrt V)), a α ≤ 1 / 4 := by
  classical
  set T : ℝ := 2 * Real.sqrt V with hTdef
  have hSpos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have hT2 : T ^ (2 : ℕ) = 4 * V := by
    rw [hTdef, mul_pow, Real.sq_sqrt hVpos.le]
    norm_num
  set F : Finset A := Finset.univ.filter (fun α => ¬ (|X α - m| < T)) with hF
  have hkey : T ^ (2 : ℕ) * ∑ α ∈ F, a α ≤ V := by
    calc T ^ (2 : ℕ) * ∑ α ∈ F, a α = ∑ α ∈ F, a α * T ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun α _ => by ring
      _ ≤ ∑ α ∈ F, a α * (X α - m) ^ (2 : ℕ) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hge : T ≤ |X α - m| := not_lt.mp (Finset.mem_filter.mp hα).2
          have hsq : T ^ (2 : ℕ) ≤ (X α - m) ^ (2 : ℕ) := by
            have habs : (0 : ℝ) ≤ T := le_of_lt (by positivity)
            nlinarith [sq_abs (X α - m), abs_nonneg (X α - m)]
          exact mul_le_mul_of_nonneg_left hsq (hnn α)
      _ ≤ ∑ α, a α * (X α - m) ^ (2 : ℕ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun α _ _ => mul_nonneg (hnn α) (sq_nonneg _))
      _ = V := hV.symm
  rw [hT2] at hkey
  nlinarith [hkey, hVpos]

/-- **The central-bin crowding floor.**  For any finite nonnegative law of total mass one, any
centre `m`, and any resolution `δ > 0`, the mass of strictly near distinct pairs is at least
`9δ / (16(δ + 4σ))` minus the exact collision mass, where `σ` is the root mean square deviation
from `m`. -/
theorem finiteLaw_crowding_floor_center {a X : A → ℝ} (hnn : ∀ α, 0 ≤ a α)
    (hsum : ∑ α, a α = 1) (m : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    9 * δ / (16 * (δ + 4 * Real.sqrt (∑ α, a α * (X α - m) ^ (2 : ℕ))))
        - finiteLawCollisionMass a X
      ≤ finiteLawNearMass a X δ := by
  classical
  set V : ℝ := ∑ α, a α * (X α - m) ^ (2 : ℕ) with hV
  have hVnn : 0 ≤ V := Finset.sum_nonneg fun α _ => mul_nonneg (hnn α) (sq_nonneg _)
  have hnear : 0 ≤ finiteLawNearMass a X δ := finiteLawNearMass_nonneg hnn δ
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- degenerate law: all mass sits at a single value, so the collision mass is one
    have hterm : ∀ α, a α = 0 ∨ X α = m := by
      intro α
      have hzero : ∀ β ∈ (Finset.univ : Finset A), 0 ≤ a β * (X β - m) ^ (2 : ℕ) :=
        fun β _ => mul_nonneg (hnn β) (sq_nonneg _)
      have hsum0 : ∑ β, a β * (X β - m) ^ (2 : ℕ) = 0 := by rw [← hV, ← hV0]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hzero).mp hsum0 α (Finset.mem_univ α)
      rcases mul_eq_zero.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h))
    have hcoll : finiteLawCollisionMass a X = 1 := by
      unfold finiteLawCollisionMass
      have hstep : ∀ α β : A, (if X α = X β then a α * a β else 0) = a α * a β := by
        intro α β
        by_cases h : X α = X β
        · rw [if_pos h]
        · rcases hterm α with hα | hα
          · rw [if_neg h, hα, zero_mul]
          · rcases hterm β with hβ | hβ
            · rw [if_neg h, hβ, mul_zero]
            · exact absurd (hα.trans hβ.symm) h
      calc (∑ α, ∑ β, if X α = X β then a α * a β else 0)
          = ∑ α, ∑ β, a α * a β :=
            Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => hstep α β
        _ = (∑ α, a α) * ∑ β, a β := (Finset.sum_mul_sum _ _ _ _).symm
        _ = 1 := by rw [hsum]; norm_num
    have hbound : 9 * δ / (16 * (δ + 4 * Real.sqrt V)) ≤ 1 := by
      rw [← hV0, Real.sqrt_zero]
      rw [div_le_one (by positivity)]
      linarith
    rw [hcoll]
    linarith
  · -- nondegenerate law
    set S : ℝ := Real.sqrt V with hS
    have hSpos : 0 < S := Real.sqrt_pos.mpr hVpos
    set T : ℝ := 2 * S with hT
    have hTpos : 0 < T := by positivity
    -- the good set carries three quarters of the mass
    set G : Finset A := Finset.univ.filter (fun α => |X α - m| < T) with hG
    have hgood : 3 / 4 ≤ ∑ α ∈ G, a α := by
      have htail := finiteLaw_tail_le_quarter hnn hV hVpos
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset A) (fun α => |X α - m| < T) a
      rw [hsum] at hsplit
      have htail' : ∑ α ∈ Finset.univ.filter (fun α => ¬ (|X α - m| < T)), a α ≤ 1 / 4 := by
        rw [hT, hS]
        exact htail
      rw [hG]
      linarith [hsplit, htail']
    -- the cell decomposition
    set c : A → ℤ := fun α => ⌊(X α - (m - T)) / δ⌋ with hc
    set N : ℕ := ⌈2 * T / δ⌉₊ with hN
    have hNpos : 0 < N := Nat.ceil_pos.mpr (by positivity)
    set J : Finset ℤ := Finset.Ico (0 : ℤ) (N : ℤ) with hJ
    have hJcard : J.card = N := by
      rw [hJ, Int.card_Ico]
      simp
    have hmaps : ∀ α ∈ G, c α ∈ J := by
      intro α hα
      have h := (Finset.mem_filter.mp hα).2
      have hb := abs_lt.mp h
      have h1 : 0 ≤ X α - (m - T) := by linarith [hb.1]
      have h2 : X α - (m - T) < 2 * T := by linarith [hb.2]
      rw [hJ, Finset.mem_Ico]
      refine ⟨Int.floor_nonneg.mpr (div_nonneg h1 hδ.le), ?_⟩
      rw [hc]
      refine Int.floor_lt.mpr ?_
      have hlt : (X α - (m - T)) / δ < 2 * T / δ := div_lt_div_of_pos_right h2 hδ
      have hle : 2 * T / δ ≤ (N : ℝ) := by
        rw [hN]
        exact_mod_cast Nat.le_ceil _
      push_cast
      linarith
    -- the cell masses
    set b : ℤ → ℝ := fun j => ∑ α ∈ Finset.univ.filter (fun α => c α = j), a α with hb
    -- three quarters of the mass is distributed among `N` cells
    have hsumb : 3 / 4 ≤ ∑ j ∈ J, b j := by
      have hfib := Finset.sum_fiberwise_of_maps_to (s := G) (t := J) (g := c) hmaps a
      have hle : ∀ j ∈ J, (∑ α ∈ G.filter (fun α => c α = j), a α) ≤ b j := by
        intro j _
        simp only [hb]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun α _ _ => hnn α)
        intro α hα
        rw [Finset.mem_filter] at hα ⊢
        exact ⟨Finset.mem_univ α, hα.2⟩
      calc (3 : ℝ) / 4 ≤ ∑ α ∈ G, a α := hgood
        _ = ∑ j ∈ J, ∑ α ∈ G.filter (fun α => c α = j), a α := hfib.symm
        _ ≤ ∑ j ∈ J, b j := Finset.sum_le_sum hle
    -- Cauchy–Schwarz on the cell masses
    have hcs : (9 : ℝ) / 16 ≤ (N : ℝ) * ∑ j ∈ J, b j ^ (2 : ℕ) := by
      have h1 : ((3 : ℝ) / 4) ^ (2 : ℕ) ≤ (∑ j ∈ J, b j) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hsumb 2
      have h2 : (∑ j ∈ J, b j) ^ (2 : ℕ) ≤ (J.card : ℝ) * ∑ j ∈ J, b j ^ (2 : ℕ) :=
        sq_sum_le_card_mul_sum_sq
      rw [hJcard] at h2
      norm_num at h1
      linarith
    -- the squared cell masses are charged to `δ`-close pairs
    have hpos : ∀ α : A, 0 ≤ ∑ β, if |X α - X β| < δ then a α * a β else 0 := by
      intro α
      refine Finset.sum_nonneg fun β _ => ?_
      split_ifs
      · exact mul_nonneg (hnn α) (hnn β)
      · exact le_rfl
    have hcharge : ∑ j ∈ J, b j ^ (2 : ℕ) ≤ finiteLawWithinMass a X δ := by
      have hexpand : ∀ j : ℤ, b j ^ (2 : ℕ)
          = ∑ α ∈ Finset.univ.filter (fun α => c α = j),
              ∑ β ∈ Finset.univ.filter (fun α => c α = j), a α * a β := by
        intro j
        simp only [hb]
        rw [sq]
        exact Finset.sum_mul_sum _ _ _ _
      have hinner : ∀ j : ℤ,
          (∑ α ∈ Finset.univ.filter (fun α => c α = j),
              ∑ β ∈ Finset.univ.filter (fun α => c α = j), a α * a β)
            ≤ ∑ α ∈ Finset.univ.filter (fun α => c α = j),
                ∑ β, if |X α - X β| < δ then a α * a β else 0 := by
        intro j
        refine Finset.sum_le_sum fun α hα => ?_
        have hcα : c α = j := (Finset.mem_filter.mp hα).2
        have heq : (∑ β ∈ Finset.univ.filter (fun α => c α = j), a α * a β)
            = ∑ β ∈ Finset.univ.filter (fun α => c α = j),
                (if |X α - X β| < δ then a α * a β else 0) := by
          refine Finset.sum_congr rfl fun β hβ => ?_
          have hcβ : c β = j := (Finset.mem_filter.mp hβ).2
          have hlt : |X α - X β| < δ := by
            refine abs_sub_lt_of_floor_div_eq (u := m - T) hδ ?_
            have hcc : c α = c β := by rw [hcα, hcβ]
            simpa only [hc] using hcc
          rw [if_pos hlt]
        rw [heq]
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro β _ _
        split_ifs
        · exact mul_nonneg (hnn α) (hnn β)
        · exact le_rfl
      set s : Finset A := Finset.univ.filter (fun α => c α ∈ J) with hs
      have hmaps' : ∀ α ∈ s, c α ∈ J := by
        intro α hα
        exact (Finset.mem_filter.mp hα).2
      have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := J) (g := c) hmaps'
        (fun α => ∑ β, if |X α - X β| < δ then a α * a β else 0)
      have hfilter : ∀ j ∈ J,
          s.filter (fun α => c α = j) = Finset.univ.filter (fun α => c α = j) := by
        intro j hj
        ext α
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, h2⟩
          exact h2
        · intro h2
          exact ⟨by rw [h2]; exact hj, h2⟩
      calc ∑ j ∈ J, b j ^ (2 : ℕ)
          = ∑ j ∈ J, ∑ α ∈ Finset.univ.filter (fun α => c α = j),
              ∑ β ∈ Finset.univ.filter (fun α => c α = j), a α * a β :=
            Finset.sum_congr rfl fun j _ => hexpand j
        _ ≤ ∑ j ∈ J, ∑ α ∈ Finset.univ.filter (fun α => c α = j),
              ∑ β, if |X α - X β| < δ then a α * a β else 0 :=
            Finset.sum_le_sum fun j _ => hinner j
        _ = ∑ j ∈ J, ∑ α ∈ s.filter (fun α => c α = j),
              ∑ β, if |X α - X β| < δ then a α * a β else 0 :=
            Finset.sum_congr rfl fun j hj => by rw [hfilter j hj]
        _ = ∑ α ∈ s, ∑ β, if |X α - X β| < δ then a α * a β else 0 := hfib
        _ ≤ ∑ α, ∑ β, if |X α - X β| < δ then a α * a β else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun α _ _ => hpos α)
        _ = finiteLawWithinMass a X δ := rfl
    -- the cell count is smaller than `1 + 4σ/δ`
    have hNbound : (N : ℝ) * δ < δ + 4 * S := by
      have hceil : (N : ℝ) < 2 * T / δ + 1 := by
        rw [hN]
        exact Nat.ceil_lt_add_one (by positivity)
      have hTS : 2 * T = 4 * S := by rw [hT]; ring
      have hmul : (N : ℝ) * δ < (2 * T / δ + 1) * δ := mul_lt_mul_of_pos_right hceil hδ
      have heq : (2 * T / δ + 1) * δ = 2 * T + δ := by field_simp
      rw [heq, hTS] at hmul
      linarith
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hfinal : 9 * δ / (16 * (δ + 4 * S)) ≤ ∑ j ∈ J, b j ^ (2 : ℕ) := by
      have hstep1 : 9 * δ / (16 * (δ + 4 * S)) ≤ 9 / (16 * (N : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hNbound, hδ]
      have hstep2 : 9 / (16 * (N : ℝ)) ≤ ∑ j ∈ J, b j ^ (2 : ℕ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hcs]
      linarith
    have hwithin := finiteLawWithinMass_eq_collision_add_near a X hδ
    linarith [hfinal, hcharge, hwithin]

/-- **The central-bin crowding floor at the mean.**  Specializing the centre to the mean of the law
gives the sharpest form, since the root mean square deviation is minimized there. -/
theorem finiteLaw_crowding_floor {a X : A → ℝ} (hnn : ∀ α, 0 ≤ a α)
    (hsum : ∑ α, a α = 1) {δ : ℝ} (hδ : 0 < δ) :
    9 * δ / (16 * (δ + 4 * Real.sqrt (∑ α, a α * (X α - ∑ β, a β * X β) ^ (2 : ℕ))))
        - finiteLawCollisionMass a X
      ≤ finiteLawNearMass a X δ :=
  finiteLaw_crowding_floor_center hnn hsum _ hδ

end GaloisForLFunctions.HTGeometry
