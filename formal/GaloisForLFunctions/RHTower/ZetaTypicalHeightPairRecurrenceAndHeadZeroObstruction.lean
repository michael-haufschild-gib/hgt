import GaloisForLFunctions.RHTower.ZetaDiscUniformCarlsonTail

/-!
# Typical-height self-returns of zeta, and the head-zero obstruction

Write `head_M(s) = Σ_{n ≤ M} n^{-s}`.  The disc-uniform Carlson tail law
(`eventually_eventually_volume_discTailBadSet_le`) makes `ζ − head_M` uniformly small on a
translated disc `closedBall c r + iτ` at all heights `τ` outside a set of small density.  Two
consequences are drawn here.

**Typical-height pair recurrence** (`exists_headPhaseReturnSet_zetaReturn_typicalHeight`).  The
simultaneous almost periods `d` of the finitely many phases `n^{-id}`, `n ≤ M`
(`headPhaseReturnSet`), form a set of positive lower density, and along such a `d` the head moves by
at most `M θ` on every vertical line.  Hence for every disc `closedBall c (2r)` in `1/2 < Re s < 1`
and every `ε, δ > 0` there are `M` and `θ > 0` such that each `d ∈ headPhaseReturnSet M θ` is an
`ε`-return shift of `ζ` on `closedBall (c + iτ₁) r` for all base heights `τ₁ ∈ [0, T]` outside a
set of measure `≤ δ T`.  In particular `ζ` has `ε`-return shifts `d ≥ R` on some translate of every
disc (`exists_zetaReturn_shift_ge_on_translate`).  What is *not* obtained is a return of positive
density at one fixed base height: around an off-line zero that is impossible
(`exists_zetaSelfReturn_density_zero`).

**Head-zero obstruction** (`eventually_volume_poleShiftedReturnSet_le`,
`eventually_volume_edPolyReturnSet_le_discTailBadSet_add`).  Shift sets that force a zero of `ζ` in
a translated disc of the right half-strip have density zero, by the `o(T)` count of zeros right of a
fixed abscissa (`eventually_volume_inter_Icc_le_of_forces_zero`).  If `head_M` vanishes at the centre
`ρ₀` of such a disc, every height at which `ζ(· + iτ)` is within `ε ≤ m/2` of the *base* head
`head_M` on the disc forces a zero of `ζ` by the minimum-modulus principle, so the pole-shifted
return set has density zero.  Consequently the finite-head return set `edPolyReturnSet` is contained
in the tail-bad set `discTailBadSet` up to density zero: on a disc where the partial sum has a zero,
Carlson-good heights and Kronecker-return heights are disjoint up to density zero.  Such discs exist
whenever `head_M` has a zero in the strip (`exists_headIsolatingDisc`).
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. Simultaneous almost periods of the first `M` logarithmic phases -/

/-- Shifts `d` at which every phase `n^{-id}`, `1 ≤ n ≤ M`, is within `θ` of `1`. -/
def headPhaseReturnSet (M : ℕ) (θ : ℝ) : Set ℝ :=
  {d : ℝ | ∀ n ∈ Finset.Icc 1 M, ‖bohrChar (Real.log n) d - 1‖ < θ}

/-- Kronecker–Bohr: simultaneous `θ`-almost periods of finitely many phases have positive lower
density. -/
theorem exists_pos_density_headPhaseReturnSet (M : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ κ > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ * T) ≤ volume (headPhaseReturnSet M θ ∩ Icc 0 T) := by
  set u : Fin M → ℝ := fun j => Real.log ((j : ℕ) + 1) with hu
  obtain ⟨κ, hκ, hT⟩ := exists_pos_return_density_of_isBohrAlmostPeriodic
    (continuous_bohrCharVector u) (isBohrAlmostPeriodic_bohrCharVector M u) hθ
  refine ⟨κ, hκ, hT.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  intro d hd n hn
  have hd : ‖bohrCharVector u d - bohrCharVector u 0‖ < θ := hd
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  have hd' := (pi_norm_lt_iff hθ).mp hd ⟨n - 1, by omega⟩
  rw [Pi.sub_apply, bohrCharVector_zero] at hd'
  simp only [bohrCharVector, hu] at hd'
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn1
  rw [hcast] at hd'
  exact hd'

/-- Along a simultaneous almost period the finite head moves by at most `M θ`, uniformly on the
half-plane `Re w ≥ 0`. -/
theorem norm_edPoly_one_Icc_shift_sub_le {M : ℕ} {θ d : ℝ} (hd : d ∈ headPhaseReturnSet M θ)
    {w : ℂ} (hw : 0 ≤ w.re) :
    ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (w + d * I) -
      edPoly (fun _ => 1) (Finset.Icc 1 M) w‖ ≤ M * θ := by
  unfold edPoly
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖(1 : ℂ) * ((n : ℝ) : ℂ) ^ (-(w + d * I)) - 1 * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ θ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := hn1
    rw [one_mul, one_mul, nat_cpow_neg_vertical_translate hn0, ← mul_sub_one, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn0)]
    have h1 : (n : ℝ) ^ (-w).re ≤ 1 := by
      rw [Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
    have h2 := hd n hn
    calc (n : ℝ) ^ (-w).re * ‖bohrChar (Real.log n) d - 1‖ ≤ 1 * θ :=
          mul_le_mul h1 h2.le (norm_nonneg _) zero_le_one
      _ = θ := one_mul θ
  calc (∑ n ∈ Finset.Icc 1 M,
        ‖(1 : ℂ) * ((n : ℝ) : ℂ) ^ (-(w + d * I)) - 1 * ((n : ℝ) : ℂ) ^ (-w)‖)
      ≤ ∑ _n ∈ Finset.Icc 1 M, θ := Finset.sum_le_sum hterm
    _ = M * θ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-! ## 2. Typical-height pair recurrence -/

/-- Base heights at which an almost period `d` of the head (with `M θ ≤ ε/3`) fails to be an
`ε`-return shift of `ζ` on the translated disc are tail-bad at height `τ₁` or at `τ₁ + d`. -/
theorem zetaPairReturnFail_subset_discTailBadSet_union {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) {ε : ℝ} {M : ℕ} {θ d : ℝ} (hMθ : M * θ ≤ ε / 3)
    (hd : d ∈ headPhaseReturnSet M θ) :
    {τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ⊆
      discTailBadSet M c r (ε / 3) ∪
        (fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) := by
  intro τ₁ hτ₁
  by_contra hcon
  simp only [mem_union, mem_preimage, not_or] at hcon
  obtain ⟨hgood1, hgood2⟩ := hcon
  apply hτ₁
  intro s hs
  set z : ℂ := s - τ₁ * I with hz
  have hs1 : s = z + τ₁ * I := by rw [hz]; ring
  have hs2 : s + d * I = z + ((τ₁ + d : ℝ) : ℂ) * I := by rw [hz]; push_cast; ring
  have hzD : z ∈ closedBall c r := by
    rw [mem_closedBall] at hs ⊢
    rwa [hs1, dist_add_right] at hs
  have hzre : 0 ≤ z.re := by have := re_ge_of_mem_closedBall hzD; linarith
  have ht1 : ‖zetaTailFun M s‖ < ε / 3 := by
    rw [hs1]
    by_contra hcon'
    exact hgood1 ⟨z, hzD, not_lt.mp hcon'⟩
  have ht2 : ‖zetaTailFun M (s + d * I)‖ < ε / 3 := by
    rw [hs2]
    by_contra hcon'
    exact hgood2 ⟨z, hzD, not_lt.mp hcon'⟩
  have hsre : 0 ≤ s.re := by rw [hs1]; simpa using hzre
  have hhead : ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (s + d * I) -
      edPoly (fun _ => 1) (Finset.Icc 1 M) s‖ ≤ ε / 3 :=
    (norm_edPoly_one_Icc_shift_sub_le hd hsre).trans hMθ
  have hid : riemannZeta (s + d * I) - riemannZeta s =
      zetaTailFun M (s + d * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (s + d * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) s) - zetaTailFun M s := by
    unfold zetaTailFun
    ring
  rw [hid]
  calc ‖zetaTailFun M (s + d * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (s + d * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) s) - zetaTailFun M s‖
      ≤ ‖zetaTailFun M (s + d * I)‖ + ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (s + d * I) -
          edPoly (fun _ => 1) (Finset.Icc 1 M) s‖ + ‖zetaTailFun M s‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- **Typical-height pair recurrence of `ζ`.**  Let `closedBall c (2r)` lie in `1/2 < Re s < 1`
and `ε, δ > 0`.  There are `M` and `θ > 0` such that every simultaneous `θ`-almost period `d` of
the phases `n^{-id}`, `n ≤ M`, is an `ε`-return shift of `ζ` on the translated disc
`closedBall (c + iτ₁) r` for all base heights `τ₁ ∈ [0, T]` outside a set of measure `≤ δ T`. -/
theorem exists_headPhaseReturnSet_zetaReturn_typicalHeight {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M : ℕ, ∃ θ > 0, ∀ d ∈ headPhaseReturnSet M θ, ∀ᶠ T : ℝ in atTop,
      volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  obtain ⟨M, hM⟩ := (eventually_eventually_volume_discTailBadSet_le hr h0 h1
    (by positivity : 0 < ε / 3) (by positivity : 0 < δ / 4)).exists
  refine ⟨M, ε / (3 * (M + 1)), by positivity, fun d hd => ?_⟩
  have hMθ : (M : ℝ) * (ε / (3 * (M + 1))) ≤ ε / 3 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  have hsub := zetaPairReturnFail_subset_discTailBadSet_union hr h0 hMθ hd
  have hshift : ∀ᶠ T : ℝ in atTop,
      volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T) ≤
        ENNReal.ofReal (|d| + δ / 4 * (T + |d|)) := by
    filter_upwards [(tendsto_atTop_add_const_right atTop |d| tendsto_id).eventually hM,
      eventually_ge_atTop (0 : ℝ)] with T hT hT0
    have hsub2 : (fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T ⊆
        (fun τ₁ : ℝ => τ₁ + d) ⁻¹' (discTailBadSet M c r (ε / 3) ∩ Icc (-|d|) (T + |d|)) := by
      rintro τ₁ ⟨hb, hI⟩
      refine ⟨hb, ?_, ?_⟩ <;> linarith [hI.1, hI.2, neg_abs_le d, le_abs_self d]
    calc volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T)
        ≤ volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹'
            (discTailBadSet M c r (ε / 3) ∩ Icc (-|d|) (T + |d|))) := measure_mono hsub2
      _ = volume (discTailBadSet M c r (ε / 3) ∩ Icc (-|d|) (T + |d|)) :=
          measure_preimage_add_right _ _ _
      _ ≤ volume (Icc (-|d|) 0) + volume (discTailBadSet M c r (ε / 3) ∩ Icc 0 (T + |d|)) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          rintro τ ⟨hτ1, hτ2⟩
          rcases le_total τ 0 with h | h
          · exact Or.inl ⟨hτ2.1, h⟩
          · exact Or.inr ⟨hτ1, h, hτ2.2⟩
      _ ≤ ENNReal.ofReal |d| + ENNReal.ofReal (δ / 4 * (T + |d|)) := by
          refine add_le_add ?_ hT
          rw [Real.volume_Icc]
          simp
      _ = ENNReal.ofReal (|d| + δ / 4 * (T + |d|)) := by
          rw [← ENNReal.ofReal_add (abs_nonneg d) (by positivity)]
  filter_upwards [hM, hshift, eventually_ge_atTop ((|d| + δ / 4 * |d|) / (δ / 2)),
    eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hTbig hT0
  calc volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T)
      ≤ volume ((discTailBadSet M c r (ε / 3) ∩ Icc 0 T) ∪
          ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T)) := by
        refine measure_mono ?_
        rintro τ₁ ⟨hτ, hI⟩
        rcases hsub hτ with h | h
        · exact Or.inl ⟨h, hI⟩
        · exact Or.inr ⟨h, hI⟩
    _ ≤ volume (discTailBadSet M c r (ε / 3) ∩ Icc 0 T) +
          volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 4 * T) + ENNReal.ofReal (|d| + δ / 4 * (T + |d|)) :=
        add_le_add hT1 hT2
    _ = ENNReal.ofReal (δ / 4 * T + (|d| + δ / 4 * (T + |d|))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (δ * T) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ (by positivity)] at hTbig
        linarith

/-- The almost periods of the head form a positive-lower-density set `E` such that every `d ∈ E`
is an `ε`-return shift of `ζ` on `closedBall (c + iτ₁) r` for all but a density-`δ` set of base
heights `τ₁`. -/
theorem exists_pos_density_zetaReturn_typicalHeight {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ E : Set ℝ, (∃ κ > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (κ * T) ≤ volume (E ∩ Icc 0 T)) ∧
      ∀ d ∈ E, ∀ᶠ T : ℝ in atTop,
        volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T) ≤
          ENNReal.ofReal (δ * T) := by
  obtain ⟨M, θ, hθ, hd⟩ := exists_headPhaseReturnSet_zetaReturn_typicalHeight hr h0 h1 hε hδ
  exact ⟨headPhaseReturnSet M θ, exists_pos_density_headPhaseReturnSet M hθ, hd⟩

/-- For every disc of the strip, tolerance `ε` and height `R`, some base height `τ₁ ≥ 0` and some
shift `d ≥ R` give an `ε`-return of `ζ` on `closedBall (c + iτ₁) r`. -/
theorem exists_zetaReturn_shift_ge_on_translate {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ τ₁ : ℝ, 0 ≤ τ₁ ∧ ∃ d : ℝ, R ≤ d ∧ d ∈ zetaReturnSet (closedBall (c + τ₁ * I) r) ε := by
  obtain ⟨M, θ, hθ, hd⟩ :=
    exists_headPhaseReturnSet_zetaReturn_typicalHeight hr h0 h1 hε one_half_pos
  obtain ⟨κ, hκ, hE⟩ := exists_pos_density_headPhaseReturnSet M hθ
  obtain ⟨d, hdE, hdR⟩ : ∃ d ∈ headPhaseReturnSet M θ, R ≤ d := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    obtain ⟨T, hT, hTR⟩ := (hE.and (eventually_gt_atTop (max R 0 / κ))).exists
    have hsub : headPhaseReturnSet M θ ∩ Icc 0 T ⊆ Icc 0 (max R 0) :=
      fun x ⟨hx, hx'⟩ => ⟨hx'.1, (hcon x hx).le.trans (le_max_left _ _)⟩
    have h := hT.trans (measure_mono hsub)
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)] at h
    rw [div_lt_iff₀ hκ] at hTR
    linarith
  obtain ⟨T, hT, hT0⟩ := ((hd d hdE).and (eventually_gt_atTop (0 : ℝ))).exists
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : Icc (0 : ℝ) T ⊆
      {τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T :=
    fun τ₁ hτ₁ => ⟨hcon τ₁ hτ₁.1 d hdR, hτ₁⟩
  have h := (measure_mono hall).trans hT
  rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

/-! ## 3. Shift sets that force a zero of `ζ` have density zero -/

/-- **Zero-forcing shift sets, one window.**  Let `closedBall ρ₀ r` lie in `1/2 < Re s < 1` with
`r ≤ (Re ρ₀ − 1/2)/2` and `r ≤ (1 − Re ρ₀)/2`.  If every `τ ∈ S` produces a zero of `ζ` in
`ball ρ₀ r + iτ`, then `S ∩ [(V − Im ρ₀)/2, V]` eventually has measure `≤ δ V`: each zero of `ζ`
with real part `≥ Re ρ₀ − r` absorbs at most `2r` of the shifts, and there are `o(V)` such zeros. -/
theorem eventually_volume_window_le_of_forces_zero {ρ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) {S : Set ℝ}
    (hS : ∀ τ ∈ S, ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in atTop, volume (S ∩ Icc ((V - ρ₀.im) / 2) V) ≤ ENNReal.ofReal (δ * V) := by
  classical
  set γ₀ := ρ₀.im
  have hre : ∀ s ∈ closedBall ρ₀ r, ρ₀.re - r ≤ s.re ∧ s.re < 1 := by
    intro s hs
    have h := abs_le.mp ((abs_re_le_norm (s - ρ₀)).trans (mem_closedBall_iff_norm.mp hs))
    rw [sub_re] at h
    constructor <;> linarith [h.1, h.2]
  have hσ : (1 : ℝ) / 2 < ρ₀.re - r := by linarith
  have hlin : Tendsto (fun V : ℝ => 2 * (V + γ₀)) atTop atTop :=
    (tendsto_atTop_add_const_right _ γ₀ tendsto_id).const_mul_atTop two_pos
  have hε' : 0 < δ / (4 * r) := by positivity
  filter_upwards [hlin.eventually (eventually_zeroCount_fixedSigma_le hσ hε'),
    hlin.eventually (eventually_ge_atTop (100 : ℝ)),
    eventually_ge_atTop ((2 + 2 * r + δ * |γ₀| / 4) / (3 * δ / 4))] with V hV hV100 hVbig
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hV
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => ρ₀.re - r ≤ w.re)
  have hcover : Icc ((V - γ₀) / 2) V ⊆ (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r) ∪
      Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ∪ Icc (T₂ - γ₀ - r) V := by
    intro x hx
    rcases le_total x (T₁ - γ₀ + r) with h | h
    · exact Or.inl (Or.inl ⟨hx.1, h⟩)
    rcases le_total x (T₂ - γ₀ - r) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr ⟨h', hx.2⟩
  have hmid : S ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r) ⊆
      ⋃ w ∈ Zσ, Icc (w.im - γ₀ - r) (w.im - γ₀ + r) := by
    intro τ ⟨hτS, hτ⟩
    obtain ⟨z, hz, hz0⟩ := hS τ hτS
    have hzre := hre z (ball_subset_closedBall hz)
    have hzim := abs_le.mp ((abs_im_le_norm (z - ρ₀)).trans (mem_ball_iff_norm.mp hz).le)
    rw [sub_im] at hzim
    set w := z + τ * I with hw
    have hwre : w.re = z.re := by simp [hw]
    have hwim : w.im = z.im + τ := by simp [hw]
    have hwZ : w ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le, hwre,
        hwim]
      exact ⟨⟨⟨by linarith [hzre.1], by linarith [hzre.2]⟩,
        ⟨by linarith [hτ.1, hzim.1], by linarith [hτ.2, hzim.2]⟩⟩, hz0⟩
    refine mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwZ, by rw [hwre]; exact hzre.1⟩, ?_⟩
    rw [hwim]
    exact ⟨by linarith [hzim.2], by linarith [hzim.1]⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  have hvmid : volume (S ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ≤
      ENNReal.ofReal (2 * r * (δ / (4 * r) * (T₂ - T₁))) :=
    calc volume (S ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r))
        ≤ volume (⋃ w ∈ Zσ, Icc (w.im - γ₀ - r) (w.im - γ₀ + r)) := measure_mono hmid
      _ ≤ ∑ w ∈ Zσ, volume (Icc (w.im - γ₀ - r) (w.im - γ₀ + r)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ w ∈ Zσ, ENNReal.ofReal (2 * r) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Real.volume_Icc]
          congr 1
          ring
      _ = ENNReal.ofReal (2 * r * Zσ.card) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ENNReal.ofReal (2 * r * (δ / (4 * r) * (T₂ - T₁))) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hcard.trans (hc Z hZ)) (by positivity))
  have hlo : volume (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r)) ≤ ENNReal.ofReal (1 + r) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₁.2])
  have hhi : volume (Icc (T₂ - γ₀ - r) V) ≤ ENNReal.ofReal (1 + r) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₂.1])
  have hlen : T₂ - T₁ ≤ (V + γ₀) / 2 := by linarith [hT₁.1, hT₂.2]
  have hmid' : 2 * r * (δ / (4 * r) * (T₂ - T₁)) = δ / 2 * (T₂ - T₁) := by
    field_simp
    ring
  have hγ : -|γ₀| ≤ γ₀ := neg_abs_le γ₀
  have hVbig' : 2 + 2 * r + δ * |γ₀| / 4 ≤ 3 * δ / 4 * V := by
    rw [div_le_iff₀ (by positivity)] at hVbig
    linarith
  calc volume (S ∩ Icc ((V - γ₀) / 2) V)
      ≤ volume ((S ∩ Icc ((V - γ₀) / 2) (T₁ - γ₀ + r) ∪ S ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r)) ∪
          S ∩ Icc (T₂ - γ₀ - r) V) := by
        refine measure_mono ?_
        rw [← inter_union_distrib_left, ← inter_union_distrib_left]
        exact inter_subset_inter_right _ hcover
    _ ≤ (volume (Icc ((V - γ₀) / 2) (T₁ - γ₀ + r)) +
          volume (S ∩ Icc (T₁ - γ₀ + r) (T₂ - γ₀ - r))) + volume (Icc (T₂ - γ₀ - r) V) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_mono inter_subset_right) le_rfl)) (measure_mono inter_subset_right))
    _ ≤ (ENNReal.ofReal (1 + r) + ENNReal.ofReal (δ / 2 * (T₂ - T₁))) + ENNReal.ofReal (1 + r) :=
        add_le_add (add_le_add hlo (hmid' ▸ hvmid)) hhi
    _ = ENNReal.ofReal ((1 + r) + δ / 2 * (T₂ - T₁) + (1 + r)) := by
        have hmid0 : 0 ≤ δ / 2 * (T₂ - T₁) := mul_nonneg (by positivity) (by linarith)
        rw [← ENNReal.ofReal_add (by positivity) hmid0, ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (δ * V) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left hlen hδ.le
        have h2 := mul_le_mul_of_nonneg_left (le_abs_self γ₀) hδ.le
        linarith

/-- **Zero-forcing shift sets have density zero.** -/
theorem eventually_volume_inter_Icc_le_of_forces_zero {ρ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) {S : Set ℝ}
    (hS : ∀ τ ∈ S, ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (S ∩ Icc 0 T) ≤ ENNReal.ofReal (κ * T) :=
  eventually_volume_inter_Icc_le_of_window
    (fun _ hδ => eventually_volume_window_le_of_forces_zero hr hr2 hr3 hS hδ) hκ

/-! ## 4. The head-zero obstruction -/

/-- Heights at which `ζ(· + iτ)` is within `ε` of the *base* head `head_M` on `K`. -/
def poleShiftedReturnSet (M : ℕ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ z ∈ K, ‖riemannZeta (z + τ * I) - edPoly (fun _ => 1) (Finset.Icc 1 M) z‖ < ε}

/-- A pole-shifted return forces a zero of `ζ` in the translated disc when `head_M` vanishes at the
centre and `|head_M| ≥ m ≥ 2ε` on the boundary circle (minimum-modulus principle). -/
theorem exists_zero_of_mem_poleShiftedReturnSet {M : ℕ} {ρ₀ : ℂ} {r m ε τ : ℝ} (hr : 0 < r)
    (hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1)
    (hρ₀ : edPoly (fun _ => 1) (Finset.Icc 1 M) ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖) (hε : ε ≤ m / 2)
    (hτ : τ ∈ poleShiftedReturnSet M (closedBall ρ₀ r) ε) :
    ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0 := by
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + τ * I)) (closedBall ρ₀ r) := by
    intro s hs
    have hne : s + τ * I ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [hre s hs]
    exact ((differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  refine DeBruijn.exists_zero_of_norm_lt_sphere_on hr hdiff fun z hz => ?_
  have h1 := hτ ρ₀ (mem_closedBall_self hr.le)
  rw [hρ₀, sub_zero] at h1
  have h2 := hτ z (sphere_subset_closedBall hz)
  have h3 := hm z hz
  have h4 := norm_sub_norm_le (edPoly (fun _ => 1) (Finset.Icc 1 M) z) (riemannZeta (z + τ * I))
  rw [norm_sub_rev] at h4
  show ‖riemannZeta (ρ₀ + τ * I)‖ < ‖riemannZeta (z + τ * I)‖
  linarith

/-- **Head-zero obstruction.**  If `head_M` vanishes at `ρ₀`, `closedBall ρ₀ r` lies in
`1/2 < Re s < 1` as above and `|head_M| ≥ m` on its boundary circle, then for `ε ≤ m/2` the
pole-shifted return set has density zero. -/
theorem eventually_volume_poleShiftedReturnSet_le {M : ℕ} {ρ₀ : ℂ} {r m ε : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2)
    (hρ₀ : edPoly (fun _ => 1) (Finset.Icc 1 M) ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖) (hε : ε ≤ m / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (poleShiftedReturnSet M (closedBall ρ₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ * T) := by
  have hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1 := fun s hs => by
    have := re_le_of_mem_closedBall hs
    linarith
  exact eventually_volume_inter_Icc_le_of_forces_zero hr hr2 hr3
    (fun τ hτ => exists_zero_of_mem_poleShiftedReturnSet hr hre hρ₀ hm hε hτ) hκ

/-- Finite-head return heights that are also tail-good are pole-shifted return heights. -/
theorem edPolyReturnSet_inter_tailGood_subset_poleShiftedReturnSet (M : ℕ) (K : Set ℂ) (ε : ℝ) :
    edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K (ε / 2) ∩
      {τ : ℝ | ∀ z ∈ K, ‖zetaTailFun M (z + τ * I)‖ < ε / 2} ⊆
      poleShiftedReturnSet M K ε := by
  rintro τ ⟨hhead, htail⟩ z hz
  have h1 := hhead z hz
  have h2 := htail z hz
  have hid : riemannZeta (z + τ * I) - edPoly (fun _ => 1) (Finset.Icc 1 M) z =
      zetaTailFun M (z + τ * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) z) := by
    unfold zetaTailFun
    ring
  rw [hid]
  calc ‖zetaTailFun M (z + τ * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) z)‖
      ≤ ‖zetaTailFun M (z + τ * I)‖ + ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
          edPoly (fun _ => 1) (Finset.Icc 1 M) z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 h1
    _ = ε := by ring

/-- **Conditioned loss is forced by head zeros.**  Under the head-zero hypotheses, the finite-head
return set is contained in the tail-bad set up to density zero: for every `κ > 0`, eventually
`|edPolyReturnSet ∩ [0,T]| ≤ |discTailBadSet (ε/2) ∩ [0,T]| + κ T`. -/
theorem eventually_volume_edPolyReturnSet_le_discTailBadSet_add {M : ℕ} {ρ₀ : ℂ} {r m ε : ℝ}
    (hr : 0 < r) (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2)
    (hρ₀ : edPoly (fun _ => 1) (Finset.Icc 1 M) ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖) (hε : ε ≤ m / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop,
      volume (edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) (closedBall ρ₀ r) (ε / 2) ∩
        Icc 0 T) ≤
        volume (discTailBadSet M ρ₀ r (ε / 2) ∩ Icc 0 T) + ENNReal.ofReal (κ * T) := by
  filter_upwards [eventually_volume_poleShiftedReturnSet_le hr hr2 hr3 hρ₀ hm hε hκ] with T hT
  have hsplit : edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) (closedBall ρ₀ r) (ε / 2) ∩
      Icc 0 T ⊆ (discTailBadSet M ρ₀ r (ε / 2) ∩ Icc 0 T) ∪
        (poleShiftedReturnSet M (closedBall ρ₀ r) ε ∩ Icc 0 T) := by
    rintro τ ⟨hhead, hT'⟩
    by_cases hbad : τ ∈ discTailBadSet M ρ₀ r (ε / 2)
    · exact Or.inl ⟨hbad, hT'⟩
    · refine Or.inr ⟨edPolyReturnSet_inter_tailGood_subset_poleShiftedReturnSet M _ ε
        ⟨hhead, ?_⟩, hT'⟩
      intro z hz
      by_contra hcon
      exact hbad ⟨z, hz, not_lt.mp hcon⟩
  calc volume (edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) (closedBall ρ₀ r) (ε / 2) ∩
        Icc 0 T)
      ≤ volume ((discTailBadSet M ρ₀ r (ε / 2) ∩ Icc 0 T) ∪
          (poleShiftedReturnSet M (closedBall ρ₀ r) ε ∩ Icc 0 T)) := measure_mono hsplit
    _ ≤ volume (discTailBadSet M ρ₀ r (ε / 2) ∩ Icc 0 T) +
          volume (poleShiftedReturnSet M (closedBall ρ₀ r) ε ∩ Icc 0 T) := measure_union_le _ _
    _ ≤ volume (discTailBadSet M ρ₀ r (ε / 2) ∩ Icc 0 T) + ENNReal.ofReal (κ * T) :=
        add_le_add le_rfl hT

/-- Partial sums are not identically zero (`head_M(0) = M`), so every point of the strip, in
particular every zero of `head_M`, is the centre of a disc inside the strip with a positive floor
for `|head_M|` on its boundary circle. -/
theorem exists_headIsolatingDisc {M : ℕ} (hM : 1 ≤ M) {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re)
    (h2 : ρ₀.re < 1) :
    ∃ r > 0, r ≤ (ρ₀.re - 1 / 2) / 2 ∧ r ≤ (1 - ρ₀.re) / 2 ∧
      ∃ m > 0, ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖ := by
  set h : ℂ → ℂ := edPoly (fun _ => 1) (Finset.Icc 1 M) with hh
  have hdiff : Differentiable ℂ h := differentiable_edPoly_one_Icc M
  have hanOn : AnalyticOnNhd ℂ h univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff
  have han : AnalyticAt ℂ h ρ₀ := hanOn ρ₀ (mem_univ _)
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, h z ≠ 0 := by
    refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero => ?_
    have hall := hanOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ₀) hzero
    have h0 : h 0 = (M : ℂ) := by
      simp only [hh, edPoly, neg_zero, Complex.cpow_zero, mul_one, Finset.sum_const,
        Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    exact hM0 (h0 ▸ hall (mem_univ 0))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r := min (r₁ / 2) (min ((ρ₀.re - 1 / 2) / 2) ((1 - ρ₀.re) / 2)) with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hrr₁ : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr2 : r ≤ (ρ₀.re - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - ρ₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsph : ∀ z ∈ sphere ρ₀ r, h z ≠ 0 := by
    intro z hz
    have hd : dist z ρ₀ = r := mem_sphere.mp hz
    have hzρ : z ≠ ρ₀ := by
      intro h
      rw [h, dist_self] at hd
      linarith
    exact hball (by rw [hd]; exact hrr₁) hzρ
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hdiff.continuous.continuousOn.norm
  exact ⟨r, hr, hr2, hr3, ‖h z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁), fun z hz => hmin hz⟩

end RHTower
