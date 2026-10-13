import Mathlib

/-!
# Reindexing grid double sums by the offset

A double sum over the grid `S = [0, d) ∩ ℤ` is a sum over offsets `r = k − l ∈ (−d, d)` of sums over the admissible
`l` (`sum_sum_eq_sum_offset`):

`Σ_{k∈S} Σ_{l∈S} F(k, l) = Σ_{r∈(−d,d)} Σ_{l∈S, l+r∈S} F(l + r, l)`.

For a lattice sum `Σ_{l∈ℤ} c_l = M` with `|c_l| ≤ u_{l+r}` and `|c_l| ≤ v_l` the admissible part differs from `M` by at
most the complementary masses (`norm_sum_admissible_sub_le`, `norm_sum_admissible_le` for `M = 0`), which is how the
finite grid inherits full-lattice Poisson identities.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Offset reindexing of a grid double sum.** -/
theorem sum_sum_eq_sum_offset {M : Type*} [AddCommMonoid M] (d : ℕ) (F : ℤ → ℤ → M) :
    ∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d, F k l
      = ∑ r ∈ Finset.Ioo (-(d : ℤ)) d,
          ∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d), F (l + r) l := by
  set S := Finset.Ico (0 : ℤ) d with hS
  rw [Finset.sum_comm]
  have hinner : ∀ l ∈ S, ∑ k ∈ S, F k l
      = ∑ r ∈ (Finset.Ioo (-(d : ℤ)) d).filter (fun r => l + r ∈ S), F (l + r) l := by
    intro l hl
    refine Finset.sum_nbij' (fun k => k - l) (fun r => l + r) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k ∈ S := hk
      simp only [Finset.mem_filter, Finset.mem_Ioo, hS, Finset.mem_Ico] at hk' hl ⊢
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · intro r hr
      have hr' : r ∈ (Finset.Ioo (-(d : ℤ)) d).filter (fun r => l + r ∈ S) := hr
      simp only [Finset.mem_filter, Finset.mem_Ioo, hS, Finset.mem_Ico] at hr' hl ⊢
      omega
    · intro k _; simp
    · intro r _; simp
    · intro k _; simp
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_comm' (t' := Finset.Ioo (-(d : ℤ)) d)
    (s' := fun r => S.filter (fun l => l + r ∈ S))]
  intro l r
  simp only [Finset.mem_filter, Finset.mem_Ioo, hS, Finset.mem_Ico]
  constructor
  · rintro ⟨hl, ⟨hr1, hr2⟩, hlr⟩; exact ⟨⟨hl, hlr⟩, hr1, hr2⟩
  · rintro ⟨⟨hl, hlr⟩, hr1, hr2⟩; exact ⟨hl, ⟨hr1, hr2⟩, hlr⟩

/-- **Admissible part of a lattice sum.**  If `Σ_{l∈ℤ} c_l = M` and `‖c_l‖ ≤ v_l` and `‖c_l‖ ≤ u_{l+r}` with `u, v ≥ 0`
summable, then the sum over `l ∈ S` with `l + r ∈ S` differs from `M` by at most the masses of `u` and `v` off `S`. -/
theorem norm_sum_admissible_sub_le {c : ℤ → ℂ} {M : ℂ} (hc : HasSum c M) {u v : ℤ → ℝ} (hu0 : ∀ k, 0 ≤ u k)
    (hv0 : ∀ k, 0 ≤ v k) (hus : Summable u) (hvs : Summable v) (r : ℤ)
    (hcu : ∀ l, ‖c l‖ ≤ u (l + r)) (hcv : ∀ l, ‖c l‖ ≤ v l) (S : Finset ℤ) :
    ‖∑ l ∈ S.filter (fun l => l + r ∈ S), c l - M‖
      ≤ ∑' k, ((S : Set ℤ)ᶜ).indicator u k + ∑' k, ((S : Set ℤ)ᶜ).indicator v k := by
  set A := S.filter (fun l => l + r ∈ S) with hA
  have hcs : Summable fun l => ‖c l‖ :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) hcv hvs
  have h := hc.summable.sum_add_tsum_subtype_compl A
  rw [hc.tsum_eq] at h
  have e : ∑ l ∈ A, c l - M = -∑' l : {l : ℤ // l ∉ A}, c l := by linear_combination h
  rw [e, norm_neg]
  refine (norm_tsum_le_tsum_norm (hcs.subtype _)).trans ?_
  have hsub : ∑' l : {l : ℤ // l ∉ A}, ‖c l‖ = ∑' l, (((A : Set ℤ))ᶜ).indicator (fun l => ‖c l‖) l := by
    rw [← _root_.tsum_subtype]; rfl
  rw [hsub]
  have hus' : Summable fun k => ((S : Set ℤ)ᶜ).indicator u k := hus.indicator _
  have hvs' : Summable fun k => ((S : Set ℤ)ᶜ).indicator v k := hvs.indicator _
  set U : ℤ → ℝ := fun k => ((S : Set ℤ)ᶜ).indicator u k with hU
  have hshift : Summable fun l => U (l + r) := by
    have h1 := (Equiv.addRight r).summable_iff (f := U)
    have h2 : (U ∘ (Equiv.addRight r)) = fun l => U (l + r) := by
      funext l; simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [h2] at h1
    exact h1.mpr hus'
  have hshift_eq : ∑' l, U (l + r) = ∑' k, U k := by
    have h1 := (Equiv.addRight r).tsum_eq U
    simpa only [Equiv.coe_addRight] using h1
  rw [← hshift_eq, ← Summable.tsum_add hshift hvs']
  refine Summable.tsum_le_tsum (fun l => ?_) ((hcs.indicator _)) (hshift.add hvs')
  by_cases hl : l ∈ A
  · rw [Set.indicator_of_notMem (by simpa using hl)]
    exact add_nonneg (Set.indicator_nonneg (fun k _ => hu0 k) (l + r))
      (Set.indicator_nonneg (fun k _ => hv0 k) _)
  · rw [Set.indicator_of_mem (by simpa using hl)]
    simp only [hA, Finset.mem_filter, not_and_or] at hl
    rcases hl with hl | hl
    · rw [Set.indicator_of_mem (s := ((S : Set ℤ))ᶜ) (by simpa using hl) v]
      exact (hcv l).trans (le_add_of_nonneg_left (Set.indicator_nonneg (fun k _ => hu0 k) (l + r)))
    · have hU : U (l + r) = u (l + r) := by
        simp only [hU]; rw [Set.indicator_of_mem (by simpa using hl)]
      rw [hU]
      exact (hcu l).trans (le_add_of_nonneg_right (Set.indicator_nonneg (fun k _ => hv0 k) _))

/-- **Admissible part of a vanishing lattice sum.**  The case `M = 0` of `norm_sum_admissible_sub_le`. -/
theorem norm_sum_admissible_le {c : ℤ → ℂ} (hc : HasSum c 0) {u v : ℤ → ℝ} (hu0 : ∀ k, 0 ≤ u k)
    (hv0 : ∀ k, 0 ≤ v k) (hus : Summable u) (hvs : Summable v) (r : ℤ)
    (hcu : ∀ l, ‖c l‖ ≤ u (l + r)) (hcv : ∀ l, ‖c l‖ ≤ v l) (S : Finset ℤ) :
    ‖∑ l ∈ S.filter (fun l => l + r ∈ S), c l‖
      ≤ ∑' k, ((S : Set ℤ)ᶜ).indicator u k + ∑' k, ((S : Set ℤ)ᶜ).indicator v k := by
  simpa using norm_sum_admissible_sub_le hc hu0 hv0 hus hvs r hcu hcv S

end RHTower
