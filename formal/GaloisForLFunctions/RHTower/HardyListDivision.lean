import GaloisForLFunctions.RHTower.DivPowRepresentative
import GaloisForLFunctions.RHTower.DivShiftRepresentative
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift

/-!
# Dividing a Hardy function by a list of its zeros

Burnol's constructions repeatedly need `(w + 1/2)^n·F(w)/∏(w - z_i)` to be a Hardy function of the
right half-plane, for a finite list `z₁, …, z_n` of zeros of `F`.  Multiplying a Hardy function by
`w + 1/2` is not allowed, so the two operations must be interleaved: the splitting

`(w + 1/2)·G(w)/(w - z) = G(w) + (z + 1/2)·G(w)/(w - z)`

removes one divisor and one factor of `w + 1/2` at a time, and each summand is Hardy as soon as `G`
vanishes at `z`.  Iterating along the list gives the statement below, the multiplicity bookkeeping
being the count of a point in the list.

## Main results

* `exists_isHalfPlaneHardy_listDiv`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_le_analyticOrderAt_of_meromorphic {F : ℂ → ℂ} {z : ℂ} (hana : AnalyticAt ℂ F z)
    (h : ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z) : (1 : ℕ∞) ≤ analyticOrderAt F z := by
  rw [Order.one_le_iff_ne_zero]
  intro hzero
  rw [hana.meromorphicOrderAt_eq, hzero] at h
  have h2 : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by simpa using h
  have h3 : (1 : ℤ) ≤ 0 := by exact_mod_cast h2
  omega

theorem withTop_sub_sub (x : WithTop ℤ) (a b : ℤ) :
    x - (a : WithTop ℤ) - (b : WithTop ℤ) = x - ((a + b : ℤ) : WithTop ℤ) := by
  induction x with
  | top => simp
  | coe n =>
      norm_cast
      omega

theorem ne_neg_half_of_re_pos_of {w : ℂ} (hw : 0 < w.re) : w ≠ -(1 / 2) := by
  intro h
  rw [h] at hw
  norm_num at hw

theorem meromorphicOrderAt_halfShift {z : ℂ} (hz : z ≠ -(1 / 2)) :
    meromorphicOrderAt (fun w : ℂ => w + 1 / 2) z = (0 : WithTop ℤ) := by
  have hana : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := analyticAt_id.add analyticAt_const
  have hne : (z : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    exact hz (by linear_combination h)
  rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hne]
  simp

theorem meromorphicOrderAt_sub_point (z p : ℂ) :
    meromorphicOrderAt (fun w : ℂ => w - z) p
      = ((if p = z then (1 : ℤ) else 0 : ℤ) : WithTop ℤ) := by
  classical
  by_cases h : p = z
  · rw [if_pos h, h]
    exact meromorphicOrderAt_sub_const_self _
  · rw [if_neg h]
    exact meromorphicOrderAt_sub_const_of_ne h

/-- **Dividing a Hardy function by a list of its zeros**, absorbing `j` factors of `w + 1/2`
along the way (`j` at most the length of the list, so that the rational multiplier stays bounded
at infinity). -/
theorem exists_isHalfPlaneHardy_listDiv {C : ℂ → ℂ} {MC : ℝ} (hC : IsHalfPlaneHardy C MC)
    (hCmero : ∀ s : ℂ, MeromorphicAt C s)
    (hCana : ∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ C s) :
    ∀ (L : List ℂ) (j : ℕ), j ≤ L.length → (∀ z ∈ L, z ≠ -(1 / 2)) →
      (∀ z : ℂ, z ≠ -(1 / 2) → ((L.count z : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt C z) →
      ∃ (K : ℂ → ℂ) (N : ℝ), IsHalfPlaneHardy K N ∧
        (∀ s : ℂ, MeromorphicAt K s) ∧
        (∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ K s) ∧
        (∀ z : ℂ, z ≠ -(1 / 2) →
          meromorphicOrderAt K z = meromorphicOrderAt C z - ((L.count z : ℤ) : WithTop ℤ)) ∧
        ∀ w : ℂ, w ≠ -(1 / 2) → (∀ z ∈ L, w ≠ z) →
          K w = (w + 1 / 2) ^ j * C w / (L.map fun z => w - z).prod := by
  classical
  intro L
  induction L with
  | nil =>
      intro j hj _ _
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      refine ⟨C, MC, hC, hCmero, hCana, ?_, ?_⟩
      · intro z _
        simp
      · intro w _ _
        simp
  | cons z L ih =>
      intro j hj hmem hord
      have hzhalf : z ≠ -(1 / 2) := hmem z (by simp)
      have hmem' : ∀ y ∈ L, y ≠ -(1 / 2) := fun y hy => hmem y (by simp [hy])
      have hcount : ∀ y : ℂ,
          ((z :: L).count y : ℤ) = (L.count y : ℤ) + (if y = z then (1 : ℤ) else 0) := by
        intro y
        rw [List.count_cons]
        by_cases h : y = z
        · subst h
          simp
        · have hbeq : (z == y) = false := by
            simp only [beq_eq_false_iff_ne]
            exact fun hc => h hc.symm
          simp [hbeq, h]
      have hord' : ∀ y : ℂ, y ≠ -(1 / 2) →
          ((L.count y : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt C y := by
        intro y hy
        refine le_trans ?_ (hord y hy)
        have hle : (L.count y : ℤ) ≤ ((z :: L).count y : ℤ) := by
          rw [hcount y]
          split_ifs <;> omega
        exact_mod_cast WithTop.coe_le_coe.2 hle
      -- the tail of the list, with one fewer absorbed factor when `j > 0`
      have hkey : ∀ i : ℕ, i ≤ L.length →
          ∃ (K' : ℂ → ℂ) (N' : ℝ) (N₁ : ℝ), IsHalfPlaneHardy K' N' ∧
            (∀ s : ℂ, MeromorphicAt K' s) ∧ (∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ K' s) ∧
            (∀ y : ℂ, y ≠ -(1 / 2) →
              meromorphicOrderAt K' y = meromorphicOrderAt C y - ((L.count y : ℤ) : WithTop ℤ)) ∧
            (∀ w : ℂ, w ≠ -(1 / 2) → (∀ y ∈ L, w ≠ y) →
              K' w = (w + 1 / 2) ^ i * C w / (L.map fun y => w - y).prod) ∧
            (1 : ℕ∞) ≤ analyticOrderAt K' z ∧
            IsHalfPlaneHardy (divPowNF K' z 1) N₁ := by
        intro i hi
        obtain ⟨K', N', hK', hK'mero, hK'ana, hK'ord, hK'val⟩ := ih i hi hmem' hord'
        have hK'z : ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt K' z := by
          rw [hK'ord z hzhalf]
          have hle := hord z hzhalf
          have hcz : (((z :: L).count z : ℕ) : ℤ) = ((L.count z : ℕ) : ℤ) + 1 := by
            rw [hcount z, if_pos rfl]
          rw [hcz] at hle
          induction hx : meromorphicOrderAt C z with
          | top => simp
          | coe n =>
              rw [hx] at hle
              have hn : (L.count z : ℤ) + 1 ≤ n := by exact_mod_cast hle
              have h1 : (1 : ℤ) ≤ n - (L.count z : ℤ) := by omega
              exact_mod_cast h1
        have hordz : (1 : ℕ∞) ≤ analyticOrderAt K' z :=
          one_le_analyticOrderAt_of_meromorphic (hK'ana z hzhalf) hK'z
        obtain ⟨N₁, hN₁⟩ := exists_isHalfPlaneHardy_divPowNF hK' hK'mero (hK'ana z hzhalf) hordz
          (fun s hs => hK'ana s (ne_neg_half_of_re_pos_of hs))
        exact ⟨K', N', N₁, hK', hK'mero, hK'ana, hK'ord, hK'val, hordz, hN₁⟩
      cases j with
      | zero =>
          obtain ⟨K', N', N₁, hK', hK'mero, hK'ana, hK'ord, hK'val, hordz, hN₁⟩ :=
            hkey 0 (Nat.zero_le _)
          have hDmero : ∀ s : ℂ, MeromorphicAt (divPowNF K' z 1) s := fun s =>
            (meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)).meromorphicAt
          refine ⟨divPowNF K' z 1, N₁, hN₁, hDmero,
            fun s hs => analyticAt_divPowNF hK'mero (hK'ana s hs) (hK'ana z hzhalf) hordz, ?_, ?_⟩
          · intro y hy
            by_cases hyz : y = z
            · subst hyz
              rw [meromorphicOrderAt_divPowNF_self hK'mero, hK'ord y hy, withTop_sub_sub,
                hcount y, if_pos rfl]
              norm_num
            · rw [meromorphicOrderAt_divPowNF_of_ne hK'mero 1 hyz, hK'ord y hy, hcount y,
                if_neg hyz]
              norm_num
          · intro w hw hwmem
            have hwz : w ≠ z := hwmem z (by simp)
            have hwL : ∀ y ∈ L, w ≠ y := fun y hy => hwmem y (by simp [hy])
            rw [divPowNF_eq hK'mero (hK'ana w hw) hwz, hK'val w hw hwL, pow_one]
            have hne : (w : ℂ) - z ≠ 0 := sub_ne_zero.2 hwz
            have hprodne : ((L.map fun y => w - y).prod : ℂ) ≠ 0 := by
              refine List.prod_ne_zero ?_
              intro hmem0
              obtain ⟨y, hy, hy0⟩ := List.mem_map.1 hmem0
              exact (sub_ne_zero.2 (hwL y hy)) hy0
            simp only [List.map_cons, List.prod_cons]
            field_simp
      | succ i =>
          have hi : i ≤ L.length := by simpa using Nat.succ_le_succ_iff.1 hj
          obtain ⟨K', N', N₁, hK', hK'mero, hK'ana, hK'ord, hK'val, hordz, hN₁⟩ := hkey i hi
          have hDmero : ∀ s : ℂ, MeromorphicAt (divPowNF K' z 1) s := fun s =>
            (meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)).meromorphicAt
          have hDana : ∀ s : ℂ, s ≠ -(1 / 2) → AnalyticAt ℂ (divPowNF K' z 1) s := fun s hs =>
            analyticAt_divPowNF hK'mero (hK'ana s hs) (hK'ana z hzhalf) hordz
          have hstep : ∀ w : ℂ, w ≠ -(1 / 2) → w ≠ z →
              K' w + (z + 1 / 2) * divPowNF K' z 1 w = (w + 1 / 2) * K' w / (w - z) := by
            intro w hw hwz
            have hDw : divPowNF K' z 1 w = K' w / (w - z) ^ (1 : ℕ) :=
              divPowNF_eq hK'mero (hK'ana w hw) hwz
            have hne : (w : ℂ) - z ≠ 0 := sub_ne_zero.2 hwz
            rw [hDw, pow_one]
            field_simp
            ring
          refine ⟨fun w => K' w + (z + 1 / 2) * divPowNF K' z 1 w,
            2 * N' + 2 * (‖(z : ℂ) + 1 / 2‖ ^ (2 : ℕ) * N₁),
            isHalfPlaneHardy_add hK' (isHalfPlaneHardy_const_mul hN₁ _),
            fun s => (hK'mero s).add (analyticAt_const.meromorphicAt.mul (hDmero s)),
            fun s hs => (hK'ana s hs).add (analyticAt_const.mul (hDana s hs)), ?_, ?_⟩
          · intro y hy
            have hgerm : (fun w : ℂ => K' w + (z + 1 / 2) * divPowNF K' z 1 w)
                =ᶠ[𝓝[≠] y] fun w : ℂ => (w + 1 / 2) * K' w / (w - z) := by
              have h1 : ∀ᶠ w : ℂ in 𝓝 y, w ≠ -(1 / 2) := eventually_ne_nhds hy
              have h2 : ∀ᶠ w : ℂ in 𝓝[≠] y, w ≠ z := by
                by_cases hyz : y = z
                · subst hyz
                  filter_upwards [self_mem_nhdsWithin] with w hw
                  simpa using hw
                · exact eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hyz)
              filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1, h2] with w hw hwz
              exact hstep w hw hwz
            rw [meromorphicOrderAt_congr hgerm]
            have hfun : (fun w : ℂ => (w + 1 / 2) * K' w / (w - z))
                = ((fun w : ℂ => w + 1 / 2) * K') / fun w : ℂ => w - z := by
              funext w
              rw [Pi.div_apply, Pi.mul_apply]
            rw [hfun, meromorphicOrderAt_div (f := (fun w : ℂ => w + 1 / 2) * K')
                (g := fun w : ℂ => w - z)
                (((analyticAt_id.add analyticAt_const).meromorphicAt).mul (hK'mero y))
                ((analyticAt_id.sub analyticAt_const).meromorphicAt),
              meromorphicOrderAt_mul (f := fun w : ℂ => w + 1 / 2) (g := K')
                ((analyticAt_id.add analyticAt_const).meromorphicAt) (hK'mero y),
              meromorphicOrderAt_halfShift hy, meromorphicOrderAt_sub_point, zero_add,
              hK'ord y hy, withTop_sub_sub, hcount y]
          · intro w hw hwmem
            show K' w + (z + 1 / 2) * divPowNF K' z 1 w = _
            have hwz : w ≠ z := hwmem z (by simp)
            have hwL : ∀ y ∈ L, w ≠ y := fun y hy => hwmem y (by simp [hy])
            rw [hstep w hw hwz, hK'val w hw hwL]
            have hne : (w : ℂ) - z ≠ 0 := sub_ne_zero.2 hwz
            have hprodne : ((L.map fun y => w - y).prod : ℂ) ≠ 0 := by
              refine List.prod_ne_zero ?_
              intro hmem0
              obtain ⟨y, hy, hy0⟩ := List.mem_map.1 hmem0
              exact (sub_ne_zero.2 (hwL y hy)) hy0
            simp only [List.map_cons, List.prod_cons]
            field_simp
            ring

end

end RHTower
