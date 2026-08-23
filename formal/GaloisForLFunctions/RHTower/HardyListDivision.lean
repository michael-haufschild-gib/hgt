import GaloisForLFunctions.RHTower.DivPowRepresentative

/-!
# Dividing a Hardy function by a list of its zeros

Burnol's constructions repeatedly need `(w + 1/2)^n·F(w)/∏(w - z_i)` to be a Hardy function of the
right half-plane, for a finite list `z₁, …, z_n` of zeros of `F`.  Multiplying a Hardy function by
`w + 1/2` is not allowed, so the two operations must be interleaved: the splitting

`(w + 1/2)·G(w)/(w - z) = G(w) + (z + 1/2)·G(w)/(w - z)`

removes one divisor and one factor of `w + 1/2` at a time, and each summand is Hardy as soon as `G`
vanishes at `z`.  Iterating along the list gives the statement below; the multiplicity bookkeeping
is the count of a point in the list.

## Main results

* `exists_isHalfPlaneHardy_listDiv`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_le_analyticOrderAt_of_meromorphic {F : ℂ → ℂ} {z : ℂ} (hana : AnalyticAt ℂ F z)
    (h : ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z) : (1 : ℕ∞) ≤ analyticOrderAt F z := by
  rw [hana.meromorphicOrderAt_eq] at h
  induction hx : analyticOrderAt F z with
  | top => simp
  | coe n =>
      rw [hx] at h
      have hn : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
      have : (1 : ℕ) ≤ n := by exact_mod_cast hn
      exact_mod_cast this

theorem meromorphicOrderAt_halfShift {z : ℂ} (hz : z ≠ -(1 / 2)) :
    meromorphicOrderAt (fun w : ℂ => w + 1 / 2) z = (0 : WithTop ℤ) := by
  have hana : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := analyticAt_id.add analyticAt_const
  have hne : (z : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    exact hz (by linear_combination h)
  rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hne]
  simp

theorem meromorphicOrderAt_sub_point {z p : ℂ} :
    meromorphicOrderAt (fun w : ℂ => w - z) p
      = ((if p = z then (1 : ℤ) else 0 : ℤ) : WithTop ℤ) := by
  classical
  by_cases h : p = z
  · subst h
    simp only [if_pos rfl]
    exact meromorphicOrderAt_sub_const_self _
  · simp only [if_neg h]
    exact meromorphicOrderAt_sub_const_of_ne h

/-- **Dividing a Hardy function by a list of its zeros, absorbing one `w + 1/2` per divisor.** -/
theorem exists_isHalfPlaneHardy_listDiv {C : ℂ → ℂ} {MC : ℝ} (hC : IsHalfPlaneHardy C MC)
    (hCmero : ∀ s : ℂ, MeromorphicAt C s)
    (hCana : ∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ C s) :
    ∀ L : List ℂ, (∀ z ∈ L, z ≠ -(1 / 2)) →
      (∀ z : ℂ, ((L.count z : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt C z) →
      ∃ (K : ℂ → ℂ) (N : ℝ), IsHalfPlaneHardy K N ∧
        (∀ s : ℂ, MeromorphicAt K s) ∧
        (∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ K s) ∧
        (∀ z : ℂ, z ≠ -(1 / 2) →
          meromorphicOrderAt K z = meromorphicOrderAt C z - ((L.count z : ℤ) : WithTop ℤ)) ∧
        ∀ w : ℂ, (∀ z ∈ L, w ≠ z) →
          K w = (w + 1 / 2) ^ L.length * C w / (L.map fun z => w - z).prod := by
  classical
  intro L
  induction L with
  | nil =>
      intro _ _
      refine ⟨C, MC, hC, hCmero, hCana, ?_, ?_⟩
      · intro z _
        simp
      · intro w _
        simp
  | cons z L ih =>
      intro hmem hord
      have hzhalf : z ≠ -(1 / 2) := hmem z (by simp)
      have hmem' : ∀ y ∈ L, y ≠ -(1 / 2) := fun y hy => hmem y (by simp [hy])
      have hord' : ∀ y : ℂ, ((L.count y : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt C y := by
        intro y
        refine le_trans ?_ (hord y)
        have : (L.count y : ℤ) ≤ ((z :: L).count y : ℤ) := by
          have := List.count_cons z L y
          simp only [List.count_cons]
          split_ifs <;> omega
        exact_mod_cast WithTop.coe_le_coe.2 this
      obtain ⟨K', N', hK', hK'mero, hK'ana, hK'ord, hK'val⟩ := ih hmem' hord'
      -- the current function vanishes at `z`
      have hK'z : ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt K' z := by
        rw [hK'ord z hzhalf]
        have hcz : ((z :: L).count z : ℤ) = (L.count z : ℤ) + 1 := by
          simp [List.count_cons]
        have hle := hord z
        rw [hcz] at hle
        induction hx : meromorphicOrderAt C z with
        | top => simp
        | coe n =>
            rw [hx] at hle
            have hn : (L.count z : ℤ) + 1 ≤ n := by exact_mod_cast hle
            have : (1 : ℤ) ≤ n - (L.count z : ℤ) := by omega
            exact_mod_cast this
      have hK'anaz : AnalyticAt ℂ K' z := hK'ana z hzhalf
      have hordz : (1 : ℕ∞) ≤ analyticOrderAt K' z :=
        one_le_analyticOrderAt_of_meromorphic hK'anaz hK'z
      obtain ⟨N₁, hN₁⟩ := exists_isHalfPlaneHardy_divPowNF hK' hK'mero hK'anaz hordz
        (fun s hs => hK'ana s (ne_neg_half_of_re_pos_aux hs))
      set D : ℂ → ℂ := divPowNF K' z 1 with hD
      refine ⟨fun w => K' w + (z + 1 / 2) * D w,
        2 * N' + 2 * (‖(z : ℂ) + 1 / 2‖ ^ 2 * N₁),
        isHalfPlaneHardy_add hK' (isHalfPlaneHardy_const_mul hN₁ _), ?_, ?_, ?_, ?_⟩
      · intro s
        exact (hK'mero s).add ((analyticAt_const).meromorphicAt.mul
          (meromorphicAt_divPow hK'mero z 1 s |>.congr
            (by exact ((meromorphicOn_divPow hK'mero z 1).toMeromorphicNFOn_eq_self_on_nhdsNE
              (Set.mem_univ s)))))
      · intro s hs
        exact (hK'ana s hs).add (analyticAt_const.mul
          (analyticAt_divPowNF hK'mero (hK'ana s hs) hK'anaz hordz))
      · intro y hy
        sorry
      · intro w hw
        sorry

end

end RHTower
