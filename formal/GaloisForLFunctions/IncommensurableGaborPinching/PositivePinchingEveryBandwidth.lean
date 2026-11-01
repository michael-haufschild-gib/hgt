import GaloisForLFunctions.IncommensurableGaborPinching.CosineWindowArbitraryBandwidth
import GaloisForLFunctions.IncommensurableGaborPinching.ExplicitCosineTripleFloor
import GaloisForLFunctions.IncommensurableGaborPinching.CriticalLineZeroProportion

/-!
# Positive zeta-zero pinching at every fixed positive bandwidth

A shape-one cosine window has a positive triple floor on every bounded gap set.
Packing actual simple critical zeros at a fixed fraction of their mean density
therefore supplies a macroscopic disjoint-pair Gram credit at any fixed bandwidth.
-/

noncomputable section

open Real Filter Asymptotics Topology Finset Zeta23 Zeta23.ZeroSide Zeta23.Assembly Zeta23.ThmD
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- Canonically tapered shape-one cosine window, on the grid of bandwidth `lam`. -/
def zetaCosineParams (lam T : ℝ) : Params := cosineParams (paramsOf stdProfile lam) 1 T

private theorem exists_pair_in_triple_scaled_floor {ι : Type*} [DecidableEq ι]
    {c lam α : ℝ}
    (hfloor : ∀ x y : ℝ, |x| ≤ 6 * lam → |y| ≤ 6 * lam →
      |x + y| ≤ 6 * lam →
      c ≤ max |mtKernel 1 x| (max |mtKernel 1 y| |mtKernel 1 (x + y)|))
    (hlam : 0 < lam) (hα : 0 < α) (im : ι → ℝ) {z₁ z₂ z₃ : ι}
    (h12 : im z₁ < im z₂) (h23 : im z₂ < im z₃)
    (hspan : α * (im z₃ - im z₁) ≤ 3) :
    ∃ x y : ι, x ∈ ({z₁, z₂, z₃} : Finset ι) ∧ y ∈ ({z₁, z₂, z₃} : Finset ι) ∧
      x ≠ y ∧ c ≤ |mtKernel 1 ((2 * lam * α) * |im x - im y|)| := by
  let u := 2 * lam * α * (im z₂ - im z₁)
  let v := 2 * lam * α * (im z₃ - im z₂)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + v ≤ 6 * lam := by
    have h := mul_le_mul_of_nonneg_left hspan (by positivity : 0 ≤ 2 * lam)
    dsimp [u, v]
    nlinarith only [h]
  have hfl := hfloor u v (by rw [abs_of_nonneg hu]; linarith only [hsum, hv])
    (by rw [abs_of_nonneg hv]; linarith only [hsum, hu])
    (by rw [abs_of_nonneg (add_nonneg hu hv)]; exact hsum)
  have hne12 : z₁ ≠ z₂ := fun h => h12.ne (congrArg im h)
  have hne23 : z₂ ≠ z₃ := fun h => h23.ne (congrArg im h)
  have hne13 : z₁ ≠ z₃ := fun h => (h12.trans h23).ne (congrArg im h)
  rcases le_max_iff.mp hfl with h | h
  · refine ⟨z₁, z₂, by simp, by simp, hne12, ?_⟩
    simpa only [u, abs_sub_comm (im z₁), abs_of_nonneg (sub_nonneg.mpr h12.le)] using h
  · rcases le_max_iff.mp h with h | h
    · refine ⟨z₂, z₃, by simp, by simp, hne23, ?_⟩
      simpa only [v, abs_sub_comm (im z₂), abs_of_nonneg (sub_nonneg.mpr h23.le)] using h
    · refine ⟨z₁, z₃, by simp, by simp, hne13, ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (h12.trans h23).le)]
      have heq : 2 * lam * α * (im z₃ - im z₁) = u + v := by
        dsimp [u, v]
        ring
      rw [heq]
      exact h

/-- Actual simple critical indices for the canonically tapered cosine window. -/
def zetaCosineSimpleBlock (lam T : ℝ) : Finset (ZI zetaZeroConfig T) :=
  (blockData zetaZeroConfig T (zetaCosineParams lam T) (GzGp.phiHat_conj _ T)).S₁

/-- Explicit pair floor for the shape-one kernel on the packed triples. -/
def cosinePairFloor (lam : ℝ) : ℝ := 1 / (10 + 720 * Real.pi ^ 2 * lam ^ 2)

/-- Every fixed positive bandwidth has an explicit macroscopic overlap credit on actual
simple critical zeta zeros. -/
theorem zetaCosine_explicit_disjointPairs (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ T in atTop,
      ∃ (r : Finset ℕ) (x y : ℕ → ZI zetaZeroConfig T),
        (∀ p ∈ r, x p ∈ zetaCosineSimpleBlock lam T) ∧
        (∀ p ∈ r, y p ∈ zetaCosineSimpleBlock lam T) ∧
        (∀ p ∈ r, x p ≠ y p) ∧
        (r : Set ℕ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI zetaZeroConfig T))) ∧
        (cosinePairFloor lam ^ 2 / 200) * (zetaZeroConfig.N T (2 * T) : ℝ)
          ≤ 2 * ∑ p ∈ r, (pairGridOverlap zetaZeroConfig (zetaCosineParams lam T) T (x p) (y p)) ^ 2 := by
  let c := cosinePairFloor lam
  have hc : 0 < c := by dsimp [c, cosinePairFloor]; positivity
  have hfloor (x y : ℝ) (hx : |x| ≤ 6 * lam) (hy : |y| ≤ 6 * lam)
      (hxy : |x + y| ≤ 6 * lam) :
      c ≤ max |mtKernel 1 x| (max |mtKernel 1 y| |mtKernel 1 (x + y)|) := by
    have h := mtKernel_shapeOne_explicit_triple_floor x y hx hy hxy
    have heq : 10 + 20 * Real.pi ^ 2 * (6 * lam) ^ 2 =
        10 + 720 * Real.pi ^ 2 * lam ^ 2 := by ring
    rw [heq] at h
    exact h
  let Z := zetaZeroConfig
  let P := paramsOf stdProfile 1
  obtain ⟨Tbase, hbase⟩ := beyond_HD_one_simple_critical_dyadic (1 / 100) (by norm_num)
  have hev_base : ∀ᶠ T in atTop, (13 / 20 : ℝ) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
    filter_upwards [eventually_ge_atTop Tbase] with T hT
    have h := hbase T hT
    have hHD := RHTower.HD_one_ge
    have hN : (0 : ℝ) ≤ Ncount T (2 * T) := Nat.cast_nonneg _
    simp only [Z, zetaZeroConfig_N, zetaZeroConfig_N0s]
    nlinarith only [h, mul_nonneg (by linarith only [hHD] :
      0 ≤ HD 1 + 1 / 10 ^ 8 - 1 / 100 - 13 / 20) hN]
  have hev_bd := (isLittleO_boundary_N Z paperInputs_zeta.RvM).def (show (0 : ℝ) < 1 / 100 by norm_num)
  have hev_scale := eventually_L_mul_T_div_two_pi_le_N Z paperInputs_zeta.RvM
    (P := paramsOf stdProfile (2 / 3)) (by norm_num [paramsOf]) (by norm_num [paramsOf])
  have hev_Nbig := (tendsto_N_atTop Z paperInputs_zeta.RvM).eventually_ge_atTop (100 : ℝ)
  have hev_grid := eventually_pairGridOverlap_cosineParams_close Z
    (P := paramsOf stdProfile lam) taperProfile_stdProfile hlam
    (κ := 1) (by norm_num) le_rfl (by norm_num [paramsOf]) (ε := c / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_l_pos, hev_base, hev_bd, hev_scale,
    hev_Nbig, hev_grid] with T hT16 hl hN0s hbd hscale hNbig hgrid
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hN0] at hbd
  set SB := S₁Bulk Z P T (GzGp.phiHat_conj _ T)
  have hdecomp : (Z.N0s T (2 * T) : ℝ) ≤ (SB.card : ℝ) +
      ((Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ) := by
    have h := N0s_le_card_S₁Bulk_add_boundary Z P (by linarith) (GzGp.phiHat_conj _ T)
    have hcast := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at hcast ⊢
    linarith only [hcast]
  have hSB_ge : (5 / 8 : ℝ) * N ≤ (SB.card : ℝ) := by linarith only [hdecomp, hN0s, hbd, hN0]
  have hm3 : 3 ≤ SB.card := by
    have : (3 : ℝ) ≤ (SB.card : ℝ) := by linarith only [hSB_ge, hNbig]
    exact_mod_cast this
  have hm_sub2 : (5 / 8 : ℝ) * N - 2 ≤ ((SB.card - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ SB.card)]
    norm_num only [Nat.cast_ofNat]
    linarith only [hSB_ge]
  -- Critical ordinates are injective, hence admit a strictly increasing ordering.
  have him_injOn : Set.InjOn (fun z : ZI Z T => (z : ℂ).im) (SB : Set (ZI Z T)) := by
    intro z₁ hz₁ z₂ hz₂ him
    rw [Finset.mem_coe] at hz₁ hz₂
    have hS1_1 := (Finset.mem_filter.mp hz₁).1
    have hS1_2 := (Finset.mem_filter.mp hz₂).1
    have hre1 : (z₁ : ℂ).re = 1 / 2 := by
      have h := (Finset.mem_filter.mp hS1_1).2.1
      dsimp only [blockData] at h
      exact (mkData_σ_eq_iff Z T _ _ z₁).mp h
    have hre2 : (z₂ : ℂ).re = 1 / 2 := by
      have h := (Finset.mem_filter.mp hS1_2).2.1
      dsimp only [blockData] at h
      exact (mkData_σ_eq_iff Z T _ _ z₂).mp h
    apply Subtype.ext
    apply Complex.ext
    · rw [hre1, hre2]
    · exact him
  set Γ : Finset ℝ := SB.image (fun z : ZI Z T => (z : ℂ).im)
  have hΓ_card : Γ.card = SB.card := Finset.card_image_of_injOn him_injOn
  set m : ℕ := Γ.card
  have hm_ge3 : 3 ≤ m := hΓ_card ▸ hm3
  let e := Γ.orderEmbOfFin (rfl : Γ.card = m)
  set g : Fin m → ℝ := fun i => e i
  have hg_mono : StrictMono g := e.strictMono
  have hg_mem : ∀ i : Fin m, g i ∈ Γ := fun i => Γ.orderEmbOfFin_mem (rfl : Γ.card = m) i
  -- Lift each `g i ∈ Γ` back to its unique point `zOf i ∈ SB`
  let zOf : Fin m → ZI Z T := fun i => Classical.choose (Finset.mem_image.mp (hg_mem i))
  have hzOf_mem : ∀ i : Fin m, zOf i ∈ SB := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (hg_mem i))).1
  have hzOf_im : ∀ i : Fin m, (zOf i : ℂ).im = g i := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (hg_mem i))).2
  have hzOf_inj : Function.Injective zOf := by
    intro i₁ i₂ heq
    exact hg_mono.injective (by rw [← hzOf_im i₁, ← hzOf_im i₂, heq])
  have hzOf_S₁ : ∀ i : Fin m, zOf i ∈ (blockData Z T (zetaCosineParams lam T) (GzGp.phiHat_conj _ T)).S₁ := fun i =>
    (Finset.mem_filter.mp (hzOf_mem i)).1
  have hzOf_bulk : ∀ i : Fin m, T + Real.sqrt T ≤ (zOf i : ℂ).im ∧ (zOf i : ℂ).im ≤ 2 * T - Real.sqrt T := by
    intro i
    have hb := (Finset.mem_filter.mp (hzOf_mem i)).2
    exact ⟨hb.1.le, hb.2⟩
  have hg_bounds : ∀ i : Fin m, T + Real.sqrt T ≤ g i ∧ g i ≤ 2 * T - Real.sqrt T := fun i => by
    rw [← hzOf_im i]
    exact hzOf_bulk i
  -- Pack at the fixed auxiliary scale `l(T)/(4π)`.
  set α : ℝ := (paramsOf stdProfile (1 / 2)).L T / (2 * Real.pi)
  have hα_pos : 0 < α := by simp only [α, Params.L, paramsOf]; positivity
  have hab : T + Real.sqrt T ≤ 2 * T - Real.sqrt T := by
    have h4 : 4 ≤ Real.sqrt T := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      exact Real.sqrt_le_sqrt hT16
    have h2s : 2 * Real.sqrt T ≤ T := by
      have : (2 * Real.sqrt T) ^ 2 ≤ T ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith)]; nlinarith
      nlinarith [sq_nonneg (T - 2 * Real.sqrt T)]
    linarith
  obtain ⟨R, hR_lt, hR_card, hR_span, hR_sep⟩ :=
    exists_disjoint_short_triples hm_ge3 hg_mono hab hα_pos hg_bounds
  -- The bulk census leaves at least `N/100` disjoint triples.
  have hα_span_le : α * ((2 * T - Real.sqrt T) - (T + Real.sqrt T)) ≤ (3 / 4) * N := by
    have hlen : (2 * T - Real.sqrt T) - (T + Real.sqrt T) ≤ T := by linarith [Real.sqrt_nonneg T]
    calc α * ((2 * T - Real.sqrt T) - (T + Real.sqrt T))
        ≤ α * T := mul_le_mul_of_nonneg_left hlen hα_pos.le
      _ = (3 / 4) * ((paramsOf stdProfile (2 / 3)).L T * T / (2 * Real.pi)) := by
          simp only [α, Params.L, paramsOf]; ring
      _ ≤ (3 / 4) * N := mul_le_mul_of_nonneg_left hscale (by norm_num)
  have hR_card_ge : (1 / 100 : ℝ) * N ≤ (R.card : ℝ) := by
    have hm_eq : ((m - 2 : ℕ) : ℝ) = ((SB.card - 2 : ℕ) : ℝ) := by rw [show m = SB.card from hΓ_card]
    rw [hm_eq] at hR_card
    linarith only [hR_card, hm_sub2, hα_span_le, hNbig]
  -- Each short triple has a pair above the compact kernel floor.
  have hex_pair : ∀ (j : ℕ) (hj : j ∈ R),
      ∃ u v : ZI Z T,
        u ∈ ({zOf ⟨j, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 2, hR_lt j hj⟩} : Finset (ZI Z T)) ∧
        v ∈ ({zOf ⟨j, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 2, hR_lt j hj⟩} : Finset (ZI Z T)) ∧
        u ≠ v ∧
        c ≤ |mtKernel (1 : ℝ) ((2 * lam * α) * |(u : ℂ).im - (v : ℂ).im|)| := by
    intro j hj
    have h2 : j + 2 < m := hR_lt j hj
    have h1 : j + 1 < m := by omega
    have h0 : j < m := by omega
    have h12 : (zOf ⟨j, h0⟩ : ℂ).im < (zOf ⟨j + 1, h1⟩ : ℂ).im := by
      rw [hzOf_im, hzOf_im]
      exact hg_mono (Fin.mk_lt_mk.mpr (by omega))
    have h23 : (zOf ⟨j + 1, h1⟩ : ℂ).im < (zOf ⟨j + 2, h2⟩ : ℂ).im := by
      rw [hzOf_im, hzOf_im]
      exact hg_mono (Fin.mk_lt_mk.mpr (by omega))
    have hsp : α * ((zOf ⟨j + 2, h2⟩ : ℂ).im - (zOf ⟨j, h0⟩ : ℂ).im) ≤ 3 := by
      rw [hzOf_im, hzOf_im]
      exact hR_span j hj
    exact exists_pair_in_triple_scaled_floor hfloor hlam hα_pos
      (fun z : ZI Z T => (z : ℂ).im) h12 h23 hsp
  classical
  let x : ℕ → ZI Z T := fun j =>
    if hj : j ∈ R then Classical.choose (hex_pair j hj) else zOf ⟨0, by omega⟩
  let y : ℕ → ZI Z T := fun j =>
    if hj : j ∈ R then Classical.choose (Classical.choose_spec (hex_pair j hj))
    else zOf ⟨1, by omega⟩
  have hxy_spec : ∀ j (hj : j ∈ R),
      let T_j : Finset (ZI Z T) :=
        {zOf ⟨j, by have := hR_lt j hj; omega⟩,
         zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
         zOf ⟨j + 2, hR_lt j hj⟩}
      x j ∈ T_j ∧ y j ∈ T_j ∧ x j ≠ y j ∧
        c ≤ |mtKernel (1 : ℝ) ((2 * lam * α) * |(x j : ℂ).im - (y j : ℂ).im|)| := by
    intro j hj
    simp only [x, y, dif_pos hj]
    exact Classical.choose_spec (Classical.choose_spec (hex_pair j hj))
  have hx_SB : ∀ j ∈ R, x j ∈ SB := by
    intro j hj
    have hmem := (hxy_spec j hj).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> (rw [h]; exact hzOf_mem _)
  have hy_SB : ∀ j ∈ R, y j ∈ SB := by
    intro j hj
    have hmem := (hxy_spec j hj).2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> (rw [h]; exact hzOf_mem _)
  refine ⟨R, x, y, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (Finset.mem_filter.mp (hx_SB j hj)).1
  · intro j hj; exact (Finset.mem_filter.mp (hy_SB j hj)).1
  · intro j hj; exact (hxy_spec j hj).2.2.1
  · -- Pairwise disjointness across `j ∈ R` from `3`-separation and `hzOf_inj`
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    have hsep := hR_sep j₁ hj₁ j₂ hj₂ hne
    set T₁ : Finset (ZI Z T) :=
      {zOf ⟨j₁, by have := hR_lt j₁ hj₁; omega⟩,
       zOf ⟨j₁ + 1, by have := hR_lt j₁ hj₁; omega⟩,
       zOf ⟨j₁ + 2, hR_lt j₁ hj₁⟩}
    set T₂ : Finset (ZI Z T) :=
      {zOf ⟨j₂, by have := hR_lt j₂ hj₂; omega⟩,
       zOf ⟨j₂ + 1, by have := hR_lt j₂ hj₂; omega⟩,
       zOf ⟨j₂ + 2, hR_lt j₂ hj₂⟩}
    have hsub₁ : ({x j₁, y j₁} : Finset (ZI Z T)) ⊆ T₁ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hxy_spec j₁ hj₁).1
      · exact (hxy_spec j₁ hj₁).2.1
    have hsub₂ : ({x j₂, y j₂} : Finset (ZI Z T)) ⊆ T₂ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hxy_spec j₂ hj₂).1
      · exact (hxy_spec j₂ hj₂).2.1
    refine Disjoint.mono hsub₁ hsub₂ ?_
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [T₁, T₂, Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
    rcases hz1 with rfl | rfl | rfl <;> rcases hz2 with heq | heq | heq
    all_goals
      have hidx := Fin.mk.inj_iff.mp (hzOf_inj heq)
      omega
  · have hpt_sq : ∀ j ∈ R, (c / 2) ^ 2 ≤
        (pairGridOverlap Z (zetaCosineParams lam T) T (x j) (y j)) ^ 2 := by
      intro j hj
      have hx_b := (Finset.mem_filter.mp (hx_SB j hj)).2
      have hy_b := (Finset.mem_filter.mp (hy_SB j hj)).2
      have hclose := hgrid (x j) (y j) hx_b.1.le hx_b.2 hy_b.1.le hy_b.2
      have hK_ge := (hxy_spec j hj).2.2.2
      have hscale_eq : (paramsOf stdProfile lam).L T / (2 * Real.pi) = 2 * lam * α := by
        simp only [α, Params.L, paramsOf]
        ring
      rw [hscale_eq] at hclose
      change |pairGridOverlap Z (zetaCosineParams lam T) T (x j) (y j) -
        mtKernel 1 ((2 * lam * α) * |(x j : ℂ).im - (y j : ℂ).im|)| ≤ c / 2 at hclose
      have habs_ge : c / 2 ≤ |pairGridOverlap Z (zetaCosineParams lam T) T (x j) (y j)| := by
        have htri := abs_sub_abs_le_abs_sub
          (mtKernel 1 ((2 * lam * α) * |(x j : ℂ).im - (y j : ℂ).im|))
          (pairGridOverlap Z (zetaCosineParams lam T) T (x j) (y j))
        rw [abs_sub_comm
          (mtKernel 1 ((2 * lam * α) * |(x j : ℂ).im - (y j : ℂ).im|))
          (pairGridOverlap Z (zetaCosineParams lam T) T (x j) (y j))] at htri
        linarith only [hK_ge, hclose, htri]
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : 0 ≤ c / 2) habs_ge 2
    have hsum_ge : (R.card : ℝ) * (c / 2) ^ 2
        ≤ ∑ p ∈ R, (pairGridOverlap Z (zetaCosineParams lam T) T (x p) (y p)) ^ 2 := by
      calc (R.card : ℝ) * (c / 2) ^ 2 = ∑ _ ∈ R, (c / 2) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hpt_sq
    have hcredit := mul_le_mul_of_nonneg_right hR_card_ge (sq_nonneg (c / 2))
    change (c ^ 2 / 200) * N ≤ 2 * ∑ p ∈ R,
      (pairGridOverlap Z (zetaCosineParams lam T) T (x p) (y p)) ^ 2
    nlinarith only [hsum_ge, hcredit]

/-- Every fixed positive bandwidth has positive disjoint-pair credit on actual zeta zeros. -/
theorem zetaCosine_positive_disjointPairs (lam : ℝ) (hlam : 0 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T in atTop,
      ∃ (r : Finset ℕ) (x y : ℕ → ZI zetaZeroConfig T),
        (∀ p ∈ r, x p ∈ zetaCosineSimpleBlock lam T) ∧
        (∀ p ∈ r, y p ∈ zetaCosineSimpleBlock lam T) ∧
        (∀ p ∈ r, x p ≠ y p) ∧
        (r : Set ℕ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI zetaZeroConfig T))) ∧
        δ * (zetaZeroConfig.N T (2 * T) : ℝ)
          ≤ 2 * ∑ p ∈ r, (pairGridOverlap zetaZeroConfig (zetaCosineParams lam T) T (x p) (y p)) ^ 2 := by
  exact ⟨cosinePairFloor lam ^ 2 / 200, by unfold cosinePairFloor; positivity,
    zetaCosine_explicit_disjointPairs lam hlam⟩

/-- In particular, the actual cosine Gram at bandwidth four thirds has positive pinching credit. -/
theorem zetaCosine_fourThirds_positive_disjointPairs :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T in atTop,
      ∃ (r : Finset ℕ) (x y : ℕ → ZI zetaZeroConfig T),
        (∀ p ∈ r, x p ∈ zetaCosineSimpleBlock (4 / 3) T) ∧
        (∀ p ∈ r, y p ∈ zetaCosineSimpleBlock (4 / 3) T) ∧
        (∀ p ∈ r, x p ≠ y p) ∧
        (r : Set ℕ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI zetaZeroConfig T))) ∧
        δ * (zetaZeroConfig.N T (2 * T) : ℝ) ≤
          2 * ∑ p ∈ r, (pairGridOverlap zetaZeroConfig (zetaCosineParams (4 / 3) T) T (x p) (y p)) ^ 2 :=
  zetaCosine_positive_disjointPairs (4 / 3) (by norm_num)

private theorem cosine_block_rankTrace {lam T : ℝ} (hT : 0 ≤ T)
    (hL : 16 ≤ (paramsOf stdProfile lam).L T)
    (r : Finset ℕ) (x y : ℕ → ZI zetaZeroConfig T)
    (hx : ∀ p ∈ r, x p ∈ zetaCosineSimpleBlock lam T)
    (hy : ∀ p ∈ r, y p ∈ zetaCosineSimpleBlock lam T)
    (hne : ∀ p ∈ r, x p ≠ y p)
    (hdisj : (r : Set ℕ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI zetaZeroConfig T)))) :
    let P := zetaCosineParams lam T
    4 * RHLinalg.rtrace (P.hat T (zetaZeroConfig.Az P T)) -
      RHLinalg.frobSq (P.hat T (zetaZeroConfig.Az P T)) - 2 * (zetaZeroConfig.N T (2 * T) : ℝ) -
      3 * (NII zetaZeroConfig T : ℝ) +
      2 * ∑ p ∈ r, (pairGridOverlap zetaZeroConfig P T (x p) (y p)) ^ 2 ≤
      zetaZeroConfig.N0s T (2 * T) := by
  let P := zetaCosineParams lam T
  let Z := zetaZeroConfig
  have hconj : PhiHatConj T P := GzGp.phiHat_conj P T
  have hreal : PhiHatReal T P := GzGp.phiHat_ofReal P T
  have hPois : PoissonSq T P := cosineParams_poissonSq
    (P := paramsOf stdProfile lam) taperProfile_stdProfile
    (κ := 1) (by norm_num) le_rfl (by norm_num [paramsOf]) (by simpa [paramsOf] using (by linarith : 8 ≤ (paramsOf stdProfile lam).L T))
  have ha : 0 < P.a T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (cosineParams_mass_ge_quarter (P := paramsOf stdProfile lam) taperProfile_stdProfile
      (κ := 1) (by norm_num) le_rfl (by norm_num [paramsOf]) (by simpa [paramsOf] using hL))
  have hLp : 0 < P.L T := by change 0 < (paramsOf stdProfile lam).L T; linarith only [hL]
  have hcore := mult_two_disjointPairs (blockData Z T P hconj)
    (mkPairReps Z T _ (evalVec_reflect hconj)) (show 0 < P.a T * P.L T ^ 2 by positivity)
    (sum_normSq_v_le Z T P hconj hreal hPois) r x y hx hy hne hdisj
  have hoverlap : ∑ p ∈ r,
      ((P.a T * P.L T ^ 2)⁻¹ * ∑ k : Fin (P.d T),
        ((blockData Z T P hconj).v (x p) k).re * ((blockData Z T P hconj).v (y p) k).re) ^ 2
      = ∑ p ∈ r, (pairGridOverlap Z P T (x p) (y p)) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold pairGridOverlap
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [block_v_re_eq_phiHatR hconj (hx p hp) k, block_v_re_eq_phiHatR hconj (hy p hp) k]
  rw [hoverlap, ← hatP, ← hatQ, ← hat_Az_eq_hatP_add_hatQ Z T P hconj] at hcore
  have hNcnt : ((blockData Z T P hconj).Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    dsimp only [blockData]
    exact_mod_cast (NIprime_eq_mk Z T _ (evalVec_reflect hconj)).symm
  have hs1_eq : ((blockData Z T P hconj).s₁ : ℝ) = (Z.s1 T : ℝ) := by
    dsimp only [blockData]
    exact_mod_cast (s1_eq_mk Z T _ (evalVec_reflect hconj)).symm
  rw [hNcnt, hs1_eq] at hcore
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith only [hcore, hs1]

/-- The actual finite zero Gram retains an explicit normalized rank–trace credit at every
fixed positive bandwidth. Boundary zeros remain explicit; no prime-side estimate is assumed. -/
theorem zetaCosine_explicit_rankTrace (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ T in atTop,
      let P := zetaCosineParams lam T
      4 * RHLinalg.rtrace (P.hat T (zetaZeroConfig.Az P T)) -
        RHLinalg.frobSq (P.hat T (zetaZeroConfig.Az P T)) -
        2 * (zetaZeroConfig.N T (2 * T) : ℝ) - 3 * (NII zetaZeroConfig T : ℝ) +
        (cosinePairFloor lam ^ 2 / 200) * (zetaZeroConfig.N T (2 * T) : ℝ) ≤ zetaZeroConfig.N0s T (2 * T) := by
  have hpairs := zetaCosine_explicit_disjointPairs lam hlam
  have hLtop := Assembly.tendsto_L_atTop (paramsOf stdProfile lam) hlam
  filter_upwards [hpairs, eventually_ge_atTop (0 : ℝ), hLtop.eventually_ge_atTop 16] with T hp hT hL
  obtain ⟨r, x, y, hx, hy, hne, hdisj, hsum⟩ := hp
  have h := cosine_block_rankTrace hT hL r x y hx hy hne hdisj
  dsimp only at h ⊢
  linarith only [h, hsum]

/-- The actual finite zero Gram retains a positive normalized rank–trace credit at every
fixed positive bandwidth. Boundary zeros remain explicit; no prime-side estimate is assumed. -/
theorem zetaCosine_positive_rankTrace (lam : ℝ) (hlam : 0 < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T in atTop,
      let P := zetaCosineParams lam T
      4 * RHLinalg.rtrace (P.hat T (zetaZeroConfig.Az P T)) -
        RHLinalg.frobSq (P.hat T (zetaZeroConfig.Az P T)) -
        2 * (zetaZeroConfig.N T (2 * T) : ℝ) - 3 * (NII zetaZeroConfig T : ℝ) +
        δ * (zetaZeroConfig.N T (2 * T) : ℝ) ≤ zetaZeroConfig.N0s T (2 * T) := by
  exact ⟨cosinePairFloor lam ^ 2 / 200, by unfold cosinePairFloor; positivity,
    zetaCosine_explicit_rankTrace lam hlam⟩

end GaloisForLFunctions.IncommensurableGaborPinching
