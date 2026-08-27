import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule
import GaloisForLFunctions.RHTower.Sieve.AdicBlocks

/-!
# Counting nonempty blocks in the repaired aligned schedule

The aligned recurrence is padded by `z₁-z₀` formal steps, but only logarithmically many blocks can
be nonempty.  Before the terminal clipped step, shifted endpoints grow by at least `1+δ/2` once
`δ(z₀-1) ≥ 2`.  Their fixed-base `δ/2`-adic indices are therefore strictly increasing.  This
recovers the source-scale block count without charging the padded schedule length.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Padded indices whose aligned prime block is genuinely nonempty. -/
def mtPaperAlignedActiveBlockIndices (t z₀ z₁ : ℕ) (δ : ℝ) : Finset (Fin t) :=
  Finset.univ.filter fun i =>
    (mtAdjacentPrimeBlock (mtPaperAlignedEndpoint z₀ z₁ δ) i).Nonempty

/-- Indices before the clipped terminal step. -/
def mtPaperAlignedGrowingBlockIndices (t z₀ z₁ : ℕ) (δ : ℝ) : Finset (Fin t) :=
  Finset.univ.filter fun i =>
    mtPaperAlignedEndpoint z₀ z₁ δ (i.1 + 1) < z₁

/-- Active indices whose next endpoint is the clipped target. -/
def mtPaperAlignedTerminalBlockIndices (t z₀ z₁ : ℕ) (δ : ℝ) : Finset (Fin t) :=
  (mtPaperAlignedActiveBlockIndices t z₀ z₁ δ).filter fun i =>
    mtPaperAlignedEndpoint z₀ z₁ δ (i.1 + 1) = z₁

/-- A fixed-base adic index increases after multiplication by one full base step. -/
theorem adicIndex_lt_of_mul_le {δ base x y : ℝ}
    (hδ : 0 < δ) (hbase : 0 < base) (hbasex : base ≤ x)
    (hxy : (1 + δ) * x ≤ y) :
    adicIndex δ base x < adicIndex δ base y := by
  have hbasey : base ≤ y := by
    have hfactor : 1 ≤ 1 + δ := by linarith
    have hx0 : 0 ≤ x := hbase.le.trans hbasex
    exact hbasex.trans ((le_mul_of_one_le_left hx0 hfactor).trans hxy)
  have hx := adicIndex_block hδ hbase hbasex
  have hy := adicIndex_block hδ hbase hbasey
  by_contra hnot
  have hindex : adicIndex δ base y ≤ adicIndex δ base x := Nat.le_of_not_gt hnot
  have hpow : (1 + δ) ^ (adicIndex δ base y + 1) ≤
      (1 + δ) ^ (adicIndex δ base x + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.add_le_add_right hindex 1)
  have hyUpper : y < base * (1 + δ) ^ (adicIndex δ base x + 1) :=
    hy.2.trans_le (mul_le_mul_of_nonneg_left hpow hbase.le)
  have hxNext : base * (1 + δ) ^ (adicIndex δ base x + 1) ≤ y := by
    calc
      base * (1 + δ) ^ (adicIndex δ base x + 1) =
          (1 + δ) * (base * (1 + δ) ^ adicIndex δ base x) := by
        rw [pow_succ]
        ring
      _ ≤ (1 + δ) * x :=
        mul_le_mul_of_nonneg_left hx.1 (by linarith)
      _ ≤ y := hxy
  linarith

/-- Every unclipped aligned step grows shifted endpoint by at least `1+δ/2`. -/
theorem mtPaperAlignedEndpoint_half_growth_of_lt_target
    {z₀ z₁ j : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ))
    (hnext : mtPaperAlignedEndpoint z₀ z₁ δ (j + 1) < z₁) :
    (1 + δ / 2) *
        ((mtPaperAlignedEndpoint z₀ z₁ δ j - 1 : ℕ) : ℝ) ≤
      ((mtPaperAlignedEndpoint z₀ z₁ δ (j + 1) - 1 : ℕ) : ℝ) := by
  let a := mtPaperAlignedEndpoint z₀ z₁ δ j
  let R : ℝ := (1 + δ) * ((a - 1 : ℕ) : ℝ)
  have haLower : z₀ ≤ a :=
    (mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ
      (show 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ) by linarith) j).1
  have hsub : ((z₀ - 1 : ℕ) : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right haLower 1
  have hprogressA : 2 ≤ δ * ((a - 1 : ℕ) : ℝ) :=
    hprogress.trans (mul_le_mul_of_nonneg_left hsub hδ)
  have hfloorLt : Nat.floor R + 1 < z₁ := by
    rw [mtPaperAlignedEndpoint_succ] at hnext
    dsimp [a, R] at hnext ⊢
    omega
  have hnextEq : mtPaperAlignedEndpoint z₀ z₁ δ (j + 1) = Nat.floor R + 1 := by
    rw [mtPaperAlignedEndpoint_succ, Nat.min_eq_right (Nat.le_of_lt hfloorLt)]
  have hfloorLower : R - 1 < (Nat.floor R : ℝ) := by
    have h := Nat.lt_floor_add_one R
    linarith
  have hhalf : (1 + δ / 2) * ((a - 1 : ℕ) : ℝ) ≤ R - 1 := by
    dsimp [R]
    nlinarith
  rw [hnextEq]
  have hfloorCast : (((Nat.floor R + 1 - 1 : ℕ) : ℕ) : ℝ) =
      (Nat.floor R : ℝ) := by
    simp
  rw [hfloorCast]
  exact hhalf.trans hfloorLower.le

/-- Before the terminal clipped step, aligned starting endpoints occupy distinct fixed-base adic
blocks. -/
theorem mtPaperAlignedGrowingBlockIndices_adicIndex_injOn
    {t z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 2 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 < δ)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    Set.InjOn
      (fun i : Fin t => adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ)
        ((mtPaperAlignedEndpoint z₀ z₁ δ i.1 - 1 : ℕ) : ℝ))
      (mtPaperAlignedGrowingBlockIndices t z₀ z₁ δ : Set (Fin t)) := by
  let endpoint := mtPaperAlignedEndpoint z₀ z₁ δ
  have hmono : Monotone endpoint :=
    mtPaperAlignedEndpoint_monotone (by omega) hz hδ.le (by linarith)
  intro i hi k hk hik
  by_contra hne
  have hbase : (0 : ℝ) < ((z₀ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < z₀ - 1)
  have hhalfδ : 0 < δ / 2 := by positivity
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hikv | hkiv
  · have hiGrow := mtPaperAlignedEndpoint_half_growth_of_lt_target
      (z₀ := z₀) (z₁ := z₁) (j := i.1) (δ := δ)
      (by omega) hz hδ.le hprogress (by
        simpa [mtPaperAlignedGrowingBlockIndices] using hi)
    have hiBase : ((z₀ - 1 : ℕ) : ℝ) ≤
        ((endpoint i.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right
        ((mtPaperAlignedEndpoint_mem_Icc (by omega) hz hδ.le (by linarith) i.1).1) 1
    have hstrict := adicIndex_lt_of_mul_le hhalfδ hbase hiBase hiGrow
    have hstepMono : ((endpoint (i.1 + 1) - 1 : ℕ) : ℝ) ≤
        ((endpoint k.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right (hmono (by omega)) 1
    have hi0 : 0 ≤ ((endpoint i.1 - 1 : ℕ) : ℝ) := by positivity
    have hiFactor : ((endpoint i.1 - 1 : ℕ) : ℝ) ≤
        (1 + δ / 2) * ((endpoint i.1 - 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_left hi0 (by linarith)
    have hindexMono := adicIndex_le_of_le hhalfδ hbase
      (hiBase.trans (hiFactor.trans hiGrow)) hstepMono
    exact (ne_of_lt (hstrict.trans_le hindexMono)) hik
  · have hkGrow := mtPaperAlignedEndpoint_half_growth_of_lt_target
      (z₀ := z₀) (z₁ := z₁) (j := k.1) (δ := δ)
      (by omega) hz hδ.le hprogress (by
        simpa [mtPaperAlignedGrowingBlockIndices] using hk)
    have hkBase : ((z₀ - 1 : ℕ) : ℝ) ≤
        ((endpoint k.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right
        ((mtPaperAlignedEndpoint_mem_Icc (by omega) hz hδ.le (by linarith) k.1).1) 1
    have hstrict := adicIndex_lt_of_mul_le hhalfδ hbase hkBase hkGrow
    have hstepMono : ((endpoint (k.1 + 1) - 1 : ℕ) : ℝ) ≤
        ((endpoint i.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right (hmono (by omega)) 1
    have hk0 : 0 ≤ ((endpoint k.1 - 1 : ℕ) : ℝ) := by positivity
    have hkFactor : ((endpoint k.1 - 1 : ℕ) : ℝ) ≤
        (1 + δ / 2) * ((endpoint k.1 - 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_left hk0 (by linarith)
    have hindexMono := adicIndex_le_of_le hhalfδ hbase
      (hkBase.trans (hkFactor.trans hkGrow)) hstepMono
    exact (ne_of_gt (hstrict.trans_le hindexMono)) hik

/-- Exact source-scale count for all unclipped aligned blocks. -/
theorem card_mtPaperAlignedGrowingBlockIndices_le_adicIndex
    {t z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 2 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 < δ)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    (mtPaperAlignedGrowingBlockIndices t z₀ z₁ δ).card ≤
      adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 1 := by
  let f : Fin t → ℕ := fun i => adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ)
    ((mtPaperAlignedEndpoint z₀ z₁ δ i.1 - 1 : ℕ) : ℝ)
  have hcard := Finset.card_le_card_of_injOn f
    (s := mtPaperAlignedGrowingBlockIndices t z₀ z₁ δ)
    (t := Finset.range
      (adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 1))
    (by
      intro i hi
      change f i ∈ Finset.range
        (adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 1)
      rw [Finset.mem_range, Nat.lt_succ_iff]
      apply adicIndex_le_of_le (by positivity)
        (by exact_mod_cast (show 0 < z₀ - 1 by omega))
      · exact_mod_cast Nat.sub_le_sub_right
          ((mtPaperAlignedEndpoint_mem_Icc (by omega) hz hδ.le (by linarith) i.1).1) 1
      · exact_mod_cast Nat.sub_le_sub_right
          ((mtPaperAlignedEndpoint_mem_Icc (by omega) hz hδ.le (by linarith) i.1).2) 1)
    (mtPaperAlignedGrowingBlockIndices_adicIndex_injOn hz₀ hz hδ hprogress)
  simpa [f] using hcard

/-- At most one active block can end at the clipped target. -/
theorem card_mtPaperAlignedTerminalBlockIndices_le_one
    {t z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 1 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 ≤ δ)
    (hprogress : 1 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    (mtPaperAlignedTerminalBlockIndices t z₀ z₁ δ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi k hk
  simp only [mtPaperAlignedTerminalBlockIndices, mtPaperAlignedActiveBlockIndices,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
  obtain ⟨q, hqi⟩ := hi.1
  obtain ⟨r, hqk⟩ := hk.1
  have hiActive : mtPaperAlignedEndpoint z₀ z₁ δ i.1 <
      mtPaperAlignedEndpoint z₀ z₁ δ (i.1 + 1) := by
    obtain ⟨hqLower, hqUpper, -⟩ := mem_primesIco.mp hqi
    omega
  have hkActive : mtPaperAlignedEndpoint z₀ z₁ δ k.1 <
      mtPaperAlignedEndpoint z₀ z₁ δ (k.1 + 1) := by
    obtain ⟨hqLower, hqUpper, -⟩ := mem_primesIco.mp hqk
    omega
  have hmono := mtPaperAlignedEndpoint_monotone hz₀ hz hδ hprogress
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hik | hki
  · have hkTarget : z₁ ≤ mtPaperAlignedEndpoint z₀ z₁ δ k.1 := by
      calc
        z₁ = mtPaperAlignedEndpoint z₀ z₁ δ (i.1 + 1) := hi.2.symm
        _ ≤ mtPaperAlignedEndpoint z₀ z₁ δ k.1 := hmono (by omega)
    have hkUpper :=
      (mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ hprogress k.1).2
    have : mtPaperAlignedEndpoint z₀ z₁ δ k.1 = z₁ := by omega
    omega
  · have hiTarget : z₁ ≤ mtPaperAlignedEndpoint z₀ z₁ δ i.1 := by
      calc
        z₁ = mtPaperAlignedEndpoint z₀ z₁ δ (k.1 + 1) := hk.2.symm
        _ ≤ mtPaperAlignedEndpoint z₀ z₁ δ i.1 := hmono (by omega)
    have hiUpper :=
      (mtPaperAlignedEndpoint_mem_Icc hz₀ hz hδ hprogress i.1).2
    have : mtPaperAlignedEndpoint z₀ z₁ δ i.1 = z₁ := by omega
    omega

/-- Padded empty blocks cost nothing: all nonempty aligned prime blocks are controlled by one
fixed-base adic grid plus the unique clipped terminal block. -/
theorem card_mtPaperAlignedActiveBlockIndices_le_adicIndex_add_two
    {t z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 2 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 < δ)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    (mtPaperAlignedActiveBlockIndices t z₀ z₁ δ).card ≤
      adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 2 := by
  let G := mtPaperAlignedGrowingBlockIndices t z₀ z₁ δ
  let T := mtPaperAlignedTerminalBlockIndices t z₀ z₁ δ
  have hactive : mtPaperAlignedActiveBlockIndices t z₀ z₁ δ ⊆ G ∪ T := by
    intro i hi
    have hnextUpper :=
      (mtPaperAlignedEndpoint_mem_Icc (by omega) hz hδ.le (by linarith) (i.1 + 1)).2
    by_cases hlt : mtPaperAlignedEndpoint z₀ z₁ δ (i.1 + 1) < z₁
    · exact Finset.mem_union_left _ (by simpa [G, mtPaperAlignedGrowingBlockIndices] using hlt)
    · apply Finset.mem_union_right
      simp only [T, mtPaperAlignedTerminalBlockIndices, Finset.mem_filter]
      exact ⟨hi, by omega⟩
  calc
    _ ≤ (G ∪ T).card := Finset.card_le_card hactive
    _ ≤ G.card + T.card := Finset.card_union_le G T
    _ ≤ (adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 1) + 1 :=
      Nat.add_le_add
        (card_mtPaperAlignedGrowingBlockIndices_le_adicIndex hz₀ hz hδ hprogress)
        (card_mtPaperAlignedTerminalBlockIndices_le_one
          (by omega) hz hδ.le (by linarith))
    _ = adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 2 := by omega

/-- Paper parameters make the exact active-block count unconditional. -/
theorem eventually_card_mtPaperAlignedActiveBlockIndices_le_adicIndex_add_two
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ z₁ : ℕ,
      mtLowerCutoffNat X ≤ z₁ →
      (mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card ≤
        adicIndex (mtPaperWidth A X / 2)
          (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) (((z₁ - 1 : ℕ) : ℝ)) + 2 := by
  filter_upwards [eventually_const_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one
    A (2 : ℝ) (by norm_num)] with X hprogress
  intro z₁ hz
  have hshift0 : 0 ≤ (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) := by positivity
  have hwidth : 0 < mtPaperWidth A X := by
    by_contra hnot
    have hnonpos : mtPaperWidth A X ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonpos_of_nonneg hnonpos hshift0
    linarith
  have hshift : 0 < (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) := by
    by_contra hnot
    have hzero : (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) = 0 :=
      le_antisymm (le_of_not_gt hnot) hshift0
    rw [hzero, mul_zero] at hprogress
    norm_num at hprogress
  have hz₀ : 2 ≤ mtLowerCutoffNat X := by
    have : 0 < mtLowerCutoffNat X - 1 := by exact_mod_cast hshift
    omega
  exact card_mtPaperAlignedActiveBlockIndices_le_adicIndex_add_two
    hz₀ hz hwidth hprogress

/-- Real logarithmic form of the exact active-block count. -/
theorem cast_card_mtPaperAlignedActiveBlockIndices_le_four_mul_log_div_add_two
    {t z₀ z₁ : ℕ} {δ : ℝ}
    (hz₀ : 2 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 < δ) (hδTwo : δ ≤ 2)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ)) :
    ((mtPaperAlignedActiveBlockIndices t z₀ z₁ δ).card : ℝ) ≤
      4 * Real.log ((((z₁ - 1 : ℕ) : ℝ)) / (((z₀ - 1 : ℕ) : ℝ))) / δ + 2 := by
  have hcard := card_mtPaperAlignedActiveBlockIndices_le_adicIndex_add_two
    (t := t) hz₀ hz hδ hprogress
  have hbase : (0 : ℝ) < (((z₀ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < z₀ - 1 by omega)
  have hbaseTarget : (((z₀ - 1 : ℕ) : ℝ)) ≤ (((z₁ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_le_sub_right hz 1
  have hadic := adicIndex_le_div
    (δ := δ / 2) (z₀ := (((z₀ - 1 : ℕ) : ℝ)))
    (z₁ := (((z₁ - 1 : ℕ) : ℝ))) (by positivity) (by linarith) hbase hbaseTarget
  calc
    ((mtPaperAlignedActiveBlockIndices t z₀ z₁ δ).card : ℝ) ≤
        ((adicIndex (δ / 2) (((z₀ - 1 : ℕ) : ℝ))
          (((z₁ - 1 : ℕ) : ℝ)) + 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (adicIndex (δ / 2) (((z₀ - 1 : ℕ) : ℝ))
          (((z₁ - 1 : ℕ) : ℝ)) : ℝ) + 2 := by push_cast; ring
    _ ≤ 2 * Real.log ((((z₁ - 1 : ℕ) : ℝ)) / (((z₀ - 1 : ℕ) : ℝ))) /
          (δ / 2) + 2 := by simpa [add_comm] using add_le_add_right hadic 2
    _ = 4 * Real.log ((((z₁ - 1 : ℕ) : ℝ)) / (((z₀ - 1 : ℕ) : ℝ))) / δ + 2 := by
      field_simp
      ring

/-- Source terminal depth is cubic in `log log X`, uniformly for `Y ≤ 4X`. -/
theorem eventually_mtLogDepth_le_two_mul_log_log_cube :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      ((Nat.floor (Real.log (Y : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ)) : ℕ) : ℝ) ≤
        2 * (Real.log (Real.log X)) ^ 3 := by
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  filter_upwards [hloglog, Filter.eventually_ge_atTop (4 : ℝ)] with X hll hX
  intro Y hY hYX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hllPos : 0 < Real.log (Real.log X) := lt_of_lt_of_le zero_lt_one hll
  have hcube : 0 < (Real.log (Real.log X)) ^ 3 := pow_pos hllPos 3
  have hcut : Real.log X / (Real.log (Real.log X)) ^ 3 ≤
      Real.log (mtLowerCutoffNat X : ℝ) := by
    simpa [mtLowerLogCutoff] using mtLowerLogCutoff_le_log_mtLowerCutoffNat X
  have hlogz : 0 < Real.log (mtLowerCutoffNat X : ℝ) :=
    lt_of_lt_of_le (div_pos hL hcube) hcut
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hfloor :
      ((Nat.floor (Real.log (Y : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ)) : ℕ) : ℝ) ≤
          Real.log (Y : ℝ) / Real.log (mtLowerCutoffNat X : ℝ) :=
    Nat.floor_le (div_nonneg hlogY0 hlogz.le)
  have hlogY : Real.log (Y : ℝ) ≤ 2 * Real.log X := by
    have hmono := Real.log_le_log hYpos hYX
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne'] at hmono
    have hlog4 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    linarith
  have hcutMul : Real.log X ≤
      Real.log (mtLowerCutoffNat X : ℝ) * (Real.log (Real.log X)) ^ 3 := by
    exact (div_le_iff₀ hcube).mp hcut
  have hratio : Real.log (Y : ℝ) /
      Real.log (mtLowerCutoffNat X : ℝ) ≤
        2 * (Real.log (Real.log X)) ^ 3 := by
    apply (div_le_iff₀ hlogz).2
    nlinarith
  exact hfloor.trans hratio

/-- Number of genuine paper-aligned prime blocks is one fixed power of `log X`, uniformly in the
root cutoff. -/
theorem eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ z₁ : ℕ,
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card : ℝ) ≤
          6 * (Real.log X) ^ (10 * A + 1) := by
  filter_upwards [eventually_const_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one
      A (2 : ℝ) (by norm_num),
    Filter.eventually_ge_atTop (Real.exp 1)] with X hprogress hX
  intro z₁ hz hz₁X
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hshift0 : 0 ≤ (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) := by positivity
  have hwidth : 0 < mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos hL _
  have hz₀ : 2 ≤ mtLowerCutoffNat X := by
    have hshift : 0 < (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) := by
      by_contra hnot
      have hzero : (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) = 0 :=
        le_antisymm (le_of_not_gt hnot) hshift0
      rw [hzero, mul_zero] at hprogress
      norm_num at hprogress
    have : 0 < mtLowerCutoffNat X - 1 := by exact_mod_cast hshift
    omega
  have hwidthLe : mtPaperWidth A X ≤ 2 := by
    have hone : mtPaperWidth A X ≤ 1 := by
      rw [mtPaperWidth]
      exact Real.rpow_le_one_of_one_le_of_nonpos hL1
        (neg_nonpos.mpr (Nat.cast_nonneg (10 * A)))
    linarith
  have hcard :=
    cast_card_mtPaperAlignedActiveBlockIndices_le_four_mul_log_div_add_two
      (t := z₁ - mtLowerCutoffNat X) hz₀ hz hwidth hwidthLe hprogress
  have hbaseOne : (1 : ℝ) ≤ (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ mtLowerCutoffNat X - 1 by omega)
  have htargetPos : (0 : ℝ) < (((z₁ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < z₁ - 1 by omega)
  have hratioPos : 0 < (((z₁ - 1 : ℕ) : ℝ)) /
      (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) :=
    div_pos htargetPos (zero_lt_one.trans_le hbaseOne)
  have hratioLe : (((z₁ - 1 : ℕ) : ℝ)) /
      (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) ≤ X := by
    have hdivLe : (((z₁ - 1 : ℕ) : ℝ)) /
        (((mtLowerCutoffNat X - 1 : ℕ) : ℝ)) ≤ (((z₁ - 1 : ℕ) : ℝ)) := by
      apply (div_le_iff₀ (zero_lt_one.trans_le hbaseOne)).2
      nlinarith
    have htargetLe : (((z₁ - 1 : ℕ) : ℝ)) ≤ (z₁ : ℝ) := by
      exact_mod_cast Nat.sub_le z₁ 1
    exact hdivLe.trans (htargetLe.trans hz₁X)
  have hlogRatio : Real.log ((((z₁ - 1 : ℕ) : ℝ)) /
      (((mtLowerCutoffNat X - 1 : ℕ) : ℝ))) ≤ Real.log X :=
    Real.log_le_log hratioPos hratioLe
  have hwidthEq : mtPaperWidth A X = ((Real.log X) ^ (10 * A))⁻¹ := by
    rw [mtPaperWidth, Real.rpow_neg hL.le, Real.rpow_natCast]
  have hdivEq : Real.log X / mtPaperWidth A X =
      (Real.log X) ^ (10 * A + 1) := by
    rw [hwidthEq, div_eq_mul_inv, inv_inv, pow_succ]
    ring
  have hpowOne : (1 : ℝ) ≤ (Real.log X) ^ (10 * A + 1) := one_le_pow₀ hL1
  calc
    _ ≤ 4 * Real.log ((((z₁ - 1 : ℕ) : ℝ)) /
        (((mtLowerCutoffNat X - 1 : ℕ) : ℝ))) / mtPaperWidth A X + 2 := hcard
    _ ≤ 4 * Real.log X / mtPaperWidth A X + 2 := by
      gcongr
    _ = 4 * (Real.log X / mtPaperWidth A X) + 2 := by ring
    _ = 4 * (Real.log X) ^ (10 * A + 1) + 2 := by rw [hdivEq]
    _ ≤ 6 * (Real.log X) ^ (10 * A + 1) := by nlinarith

/-- A full fixed-base paper-width grid from `1` through `X` has one fixed polylogarithmic size. -/
theorem eventually_cast_adicIndex_paperWidth_one_add_one_le_three_mul_log_pow
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) ≤
        3 * (Real.log X) ^ (10 * A + 1) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
  have hXone : (1 : ℝ) ≤ X := by
    have : (1 : ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    exact this.trans hX
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hwidth : 0 < mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos hL _
  have hwidthLe : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1
      (neg_nonpos.mpr (Nat.cast_nonneg (10 * A)))
  have hadic := adicIndex_le_div hwidth hwidthLe (by norm_num : (0 : ℝ) < 1) hXone
  have hwidthEq : mtPaperWidth A X = ((Real.log X) ^ (10 * A))⁻¹ := by
    rw [mtPaperWidth, Real.rpow_neg hL.le, Real.rpow_natCast]
  have hdivEq : Real.log X / mtPaperWidth A X =
      (Real.log X) ^ (10 * A + 1) := by
    rw [hwidthEq, div_eq_mul_inv, inv_inv, pow_succ]
    ring
  have hpowOne : (1 : ℝ) ≤ (Real.log X) ^ (10 * A + 1) := one_le_pow₀ hL1
  calc
    ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) =
        (adicIndex (mtPaperWidth A X) 1 X : ℝ) + 1 := by push_cast; ring
    _ ≤ 2 * Real.log (X / 1) / mtPaperWidth A X + 1 := by gcongr
    _ = 2 * (Real.log X / mtPaperWidth A X) + 1 := by ring_nf
    _ = 2 * (Real.log X) ^ (10 * A + 1) + 1 := by rw [hdivEq]
    _ ≤ 3 * (Real.log X) ^ (10 * A + 1) := by nlinarith

/-- Any fixed product of outer paper-width grids remains one fixed power of `log X`. -/
theorem eventually_cast_adicIndex_paperWidth_one_add_one_pow_le_log_pow
    (A r : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (((adicIndex (mtPaperWidth A X) 1 X + 1) ^ r : ℕ) : ℝ) ≤
        (3 : ℝ) ^ r * (Real.log X) ^ (r * (10 * A + 1)) := by
  filter_upwards [eventually_cast_adicIndex_paperWidth_one_add_one_le_three_mul_log_pow A]
    with X hgrid
  calc
    (((adicIndex (mtPaperWidth A X) 1 X + 1) ^ r : ℕ) : ℝ) =
        ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) ^ r := by push_cast; rfl
    _ ≤ (3 * (Real.log X) ^ (10 * A + 1)) ^ r :=
      pow_le_pow_left₀ (by positivity) hgrid r
    _ = (3 : ℝ) ^ r * (Real.log X) ^ (r * (10 * A + 1)) := by
      rw [mul_pow, ← pow_mul]
      simp only [Nat.mul_comm]

end

end RHTower.Sieve
