import GaloisForLFunctions.RHTower.XiHermiteBiehlerCount

/-!
# `ξ'` has at most as many zeros right of the line as `ξ`

**Theorem** (`sum_order_deriv_xi_right_le`). For unshadowed heights `T₁ < T₂`, the number of zeros
of `ξ'` (with multiplicity) in `1/2 < Re s < 2`, `T₁ < Im s < T₂` is at most the number of zeros of
`ξ` there.

**Proof (Hurwitz through the Hermite–Biehler family).**
- Around each zero `w` of `ξ'` in the window, take small disjoint closed squares `Q_w` inside the
  window. On `∂Q_w`, `ξ' ≠ 0`, so `|ξ/ξ'| ≤ M` there.
- For `λ = M + 1`, `ξ + λξ' = λξ'(1 + ξ/(λξ'))` with `Re(1 + ξ/(λξ')) > 0` on every `∂Q_w`. So the
  winding lemma (`sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg`) gives exactly `ord(ξ', w)`
  zeros of `ξ + λξ'` in `Q_w`.
- Summing over the disjoint squares and using the Hermite–Biehler count
  (`exists_hermiteBiehler_count_right`) bounds `Σ ord(ξ', w)` by the right zero count of `ξ`.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The closed square of half-side `r` around `w`. -/
def closedSquare (w : ℂ) (r : ℝ) : Set ℂ :=
  uIcc (w.re - r) (w.re + r) ×ℂ uIcc (w.im - r) (w.im + r)

/-- Its boundary. -/
def squareBoundary (w : ℂ) (r : ℝ) : Set ℂ :=
  {z | z ∈ closedSquare w r ∧ (|z.re - w.re| = r ∨ |z.im - w.im| = r)}

theorem mem_closedSquare {w z : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedSquare w r ↔ |z.re - w.re| ≤ r ∧ |z.im - w.im| ≤ r := by
  rw [closedSquare, Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
  simp only [mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem isCompact_squareBoundary (w : ℂ) (r : ℝ) : IsCompact (squareBoundary w r) := by
  have hK : IsCompact (closedSquare w r) := isCompact_uIcc.reProdIm isCompact_uIcc
  refine hK.of_isClosed_subset ?_ (fun z hz => hz.1)
  refine (hK.isClosed).inter ?_
  exact (isClosed_eq (by fun_prop) continuous_const).union (isClosed_eq (by fun_prop) continuous_const)

theorem norm_sub_le_of_mem_closedSquare {w z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ closedSquare w r) : ‖z - w‖ ≤ 2 * r := by
  obtain ⟨h1, h2⟩ := (mem_closedSquare hr).mp hz
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * r := by simp only [Complex.sub_re, Complex.sub_im]; linarith

/-- **`ξ'` has at most as many zeros right of the line as `ξ`.** -/
theorem sum_order_deriv_xi_right_le {T₁ T₂ : ℝ} (hT : T₁ < T₂) (hu₁ : SpeiserUnshadowed T₁)
    (hu₂ : SpeiserUnshadowed T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ deriv xi w = 0) ∧
      (∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0) ∧
      ∑ w ∈ Z₁, (analyticOrderAt (deriv xi) w).toNat ≤
        ∑ w ∈ Z₀, (analyticOrderAt xi w).toNat := by
  classical
  -- the zeros of `ξ'` in the window form a finite set
  have hnD : ∃ z : ℂ, deriv xi z ≠ 0 := by
    refine ⟨2, deriv_xi_ne_zero_of_logDeriv_ne_zero fun h0 => ?_⟩
    have := re_logDeriv_xi_pos_of_one_le_re (s := 2) (by norm_num)
    rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
  have hfin := entire_zeros_closedRectangle_finite analyticOnNhd_deriv_xi hnD
    (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((2 : ℝ) : ℂ) + T₂ * I)
  set Z₁ : Finset ℂ := hfin.toFinset.filter (rightHalfWindow T₁ T₂) with hZ₁
  have hZ₁mem : ∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ deriv xi w = 0 := by
    intro w
    rw [hZ₁, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_sep_iff]
    constructor
    · rintro ⟨⟨-, h0⟩, hw⟩; exact ⟨hw, h0⟩
    · rintro ⟨hw, h0⟩
      refine ⟨⟨?_, h0⟩, hw⟩
      rw [Complex.mem_reProdIm]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      rw [uIcc_of_le (by norm_num), uIcc_of_le hT.le]
      exact ⟨⟨hw.1.le, hw.2.1.le⟩, ⟨hw.2.2.1.le, hw.2.2.2.le⟩⟩
  -- a common half-side for disjoint squares inside the window
  obtain ⟨r₁, hr₁, hr₁le⟩ := exists_pos_le_of_finset Z₁
    (fun w => min (min (w.re - 1 / 2) (2 - w.re)) (min (w.im - T₁) (T₂ - w.im)))
    (fun w hw => by
      obtain ⟨⟨a, b, c, d⟩, -⟩ := (hZ₁mem w).mp hw
      simp only [lt_min_iff, sub_pos]; exact ⟨⟨a, b⟩, c, d⟩)
  obtain ⟨r₂, hr₂, hr₂le⟩ := exists_pos_le_of_finset ((Z₁ ×ˢ Z₁).filter fun q => q.1 ≠ q.2)
    (fun q => ‖q.1 - q.2‖)
    (fun q hq => norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hq).2))
  set r : ℝ := min r₁ r₂ / 8 with hr
  have hr0 : 0 < r := by positivity
  have hr_in : ∀ w ∈ Z₁, closedSquare w r ⊆ {z | rightHalfWindow T₁ T₂ z} := by
    intro w hw z hz
    obtain ⟨h1, h2⟩ := (mem_closedSquare hr0.le).mp hz
    have hb := hr₁le w hw
    have hmin := min_le_left r₁ r₂
    simp only [le_min_iff] at hb
    obtain ⟨⟨a, b⟩, c, d⟩ := hb
    rw [abs_le] at h1 h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdisj : ∀ w ∈ Z₁, ∀ w' ∈ Z₁, w ≠ w' → ∀ z, z ∈ closedSquare w r →
      z ∉ closedSquare w' r := by
    intro w hw w' hw' hne z hz hz'
    have h1 := norm_sub_le_of_mem_closedSquare hr0.le hz
    have h2 := norm_sub_le_of_mem_closedSquare hr0.le hz'
    have h3 := hr₂le (w, w') (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw, hw'⟩, hne⟩)
    have h4 : ‖w - w'‖ ≤ ‖z - w‖ + ‖z - w'‖ := by
      calc ‖w - w'‖ = ‖(z - w') - (z - w)‖ := by ring_nf
        _ ≤ ‖z - w'‖ + ‖z - w‖ := norm_sub_le _ _
        _ = ‖z - w‖ + ‖z - w'‖ := add_comm _ _
    have hmin := min_le_right r₁ r₂
    simp only at h3
    linarith
  -- `ξ'` vanishes in `Q_w` only at `w`; in particular not on the boundary
  have honly : ∀ w ∈ Z₁, ∀ z ∈ closedSquare w r, deriv xi z = 0 → z = w := by
    intro w hw z hz h0
    have hzZ : z ∈ Z₁ := (hZ₁mem z).mpr ⟨hr_in w hw hz, h0⟩
    by_contra hne
    exact hdisj z hzZ w hw hne z (by
      rw [mem_closedSquare hr0.le]
      simp [hr0.le]) hz
  have hbdne : ∀ w ∈ Z₁, ∀ z ∈ squareBoundary w r, deriv xi z ≠ 0 := by
    intro w hw z hz h0
    have := honly w hw z hz.1 h0
    rcases hz.2 with h | h <;> rw [this, sub_self, abs_zero] at h <;> linarith
  -- a uniform bound for `|ξ/ξ'|` on all the boundaries
  set B : Set ℂ := ⋃ w ∈ Z₁, squareBoundary w r with hB
  have hBcpt : IsCompact B := Z₁.isCompact_biUnion fun w _ => isCompact_squareBoundary w r
  have hBne : ∀ z ∈ B, deriv xi z ≠ 0 := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    exact hbdne w hw z hzw
  have hcontB : ContinuousOn (fun z => xi z / deriv xi z) B := by
    intro z hz
    exact ((xi_differentiable z).continuousAt.div
      (analyticOnNhd_deriv_xi z trivial).continuousAt (hBne z hz)).continuousWithinAt
  obtain ⟨M, hM⟩ := hBcpt.exists_bound_of_continuousOn hcontB
  set lam : ℝ := |M| + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  -- the Hermite–Biehler count at this `λ`
  obtain ⟨ZV, Z₀, hZV, hZ₀, hcount⟩ := exists_hermiteBiehler_count_right hlam0 hT hu₁ hu₂
  refine ⟨Z₁, Z₀, hZ₁mem, hZ₀, ?_⟩
  rw [← hcount]
  -- per square: the zeros of `ξ + λξ'` in `Q_w` have total order `ord(ξ', w)`
  have hsq : ∀ w ∈ Z₁, ∃ S : Finset ℂ, (∀ z, z ∈ S ↔ z ∈ closedSquare w r ∧
      xiHermiteBiehler lam z = 0) ∧
      ∑ z ∈ S, (analyticOrderAt (xiHermiteBiehler lam) z).toNat =
        (analyticOrderAt (deriv xi) w).toNat := by
    intro w hw
    set F₀ : ℂ → ℂ := fun s => (lam : ℂ) * deriv xi s with hF₀
    have hF₀A : AnalyticOnNhd ℂ F₀ Set.univ := fun z _ =>
      analyticAt_const.mul (analyticOnNhd_deriv_xi z trivial)
    have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0.ne'
    have hnF₀ : ∃ z : ℂ, F₀ z ≠ 0 := by
      obtain ⟨z, hz⟩ := hnD; exact ⟨z, mul_ne_zero hlamC hz⟩
    have hnV : ∃ z : ℂ, xiHermiteBiehler lam z ≠ 0 := by
      refine ⟨2, ?_⟩
      have hx : xi 2 ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
      have hp := re_logDeriv_xi_pos_of_one_le_re (s := 2) (by norm_num)
      rw [xiHermiteBiehler_eq_mul hx]
      refine mul_ne_zero hx fun h => ?_
      have := congrArg Complex.re h
      simp at this; nlinarith
    -- the boundary condition on `∂Q_w`
    have hbd : ∀ z ∈ squareBoundary w r, RatioLeftBoundary (xiHermiteBiehler lam) F₀
        (fun s => -(1 + xi s / ((lam : ℂ) * deriv xi s))) z := by
      intro z hz
      have hd := hbdne w hw z hz
      have hzB : z ∈ B := Set.mem_iUnion₂.mpr ⟨w, hw, hz⟩
      have hMz := hM z hzB
      have hsmall : ‖xi z / ((lam : ℂ) * deriv xi z)‖ < 1 := by
        rw [div_mul_eq_div_div_swap, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hlam0, div_lt_one hlam0]
        have : ‖xi z / deriv xi z‖ ≤ |M| := hMz.trans (le_abs_self M)
        linarith
      have hre : 0 < (1 + xi z / ((lam : ℂ) * deriv xi z)).re := by
        have := (Complex.abs_re_le_norm (xi z / ((lam : ℂ) * deriv xi z))).trans hsmall.le
        rw [Complex.add_re, Complex.one_re]
        have h2 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hsmall.le)).1
        have h3 : -1 < (xi z / ((lam : ℂ) * deriv xi z)).re := by
          have := neg_abs_le (xi z / ((lam : ℂ) * deriv xi z)).re
          have h4 := (Complex.abs_re_le_norm (xi z / ((lam : ℂ) * deriv xi z))).trans_lt hsmall
          linarith
        linarith
      have hq0 : (1 + xi z / ((lam : ℂ) * deriv xi z)) ≠ 0 := fun h => by
        rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
      have hF₀z : F₀ z ≠ 0 := mul_ne_zero hlamC hd
      have hVeq : ∀ y, deriv xi y ≠ 0 →
          xiHermiteBiehler lam y = F₀ y * (1 + xi y / ((lam : ℂ) * deriv xi y)) := by
        intro y hy
        simp only [hF₀, xiHermiteBiehler]
        field_simp
        ring
      have hDA := analyticOnNhd_deriv_xi z trivial
      have hqA : AnalyticAt ℂ (fun s => 1 + xi s / ((lam : ℂ) * deriv xi s)) z :=
        analyticAt_const.add ((xi_analyticOnNhd_univ z trivial).div
          (analyticAt_const.mul hDA) hF₀z)
      refine ⟨by rw [hVeq z hd]; exact mul_ne_zero hF₀z hq0, hF₀z, hqA.neg,
        by simp only [Complex.neg_re]; linarith, ?_⟩
      have hev : xiHermiteBiehler lam =ᶠ[𝓝 z]
          fun s => F₀ s * (1 + xi s / ((lam : ℂ) * deriv xi s)) := by
        filter_upwards [hDA.continuousAt.eventually_ne hd] with y hy
        exact hVeq y hy
      rw [logDeriv_eq_of_germ_eq hev,
        logDeriv_mul z hF₀z hq0 (hF₀A z trivial).differentiableAt hqA.differentiableAt,
        logDeriv_neg_fun (fun s => 1 + xi s / ((lam : ℂ) * deriv xi s))]
      ring
    have hmemB : ∀ x t : ℝ, ((x : ℂ) + t * I) ∈ closedSquare w r →
        (|x - w.re| = r ∨ |t - w.im| = r) → ((x : ℂ) + t * I) ∈ squareBoundary w r := by
      intro x t hz hb
      exact ⟨hz, by simpa using hb⟩
    have hsqmem : ∀ x t : ℝ, x ∈ uIcc (w.re - r) (w.re + r) → t ∈ uIcc (w.im - r) (w.im + r) →
        ((x : ℂ) + t * I) ∈ closedSquare w r := by
      intro x t hx ht
      rw [closedSquare, Complex.mem_reProdIm]
      simpa using ⟨hx, ht⟩
    have hlt1 : w.re - r < w.re + r := by linarith
    have hlt2 : w.im - r < w.im + r := by linarith
    have hl : ∀ {a b : ℝ}, a ≤ b → a ∈ uIcc a b := fun h => by rw [uIcc_of_le h]; exact ⟨le_rfl, h⟩
    have hrr : ∀ {a b : ℝ}, a ≤ b → b ∈ uIcc a b := fun h => by rw [uIcc_of_le h]; exact ⟨h, le_rfl⟩
    obtain ⟨S₁, S₀, hS₁, hS₀, hsum⟩ := sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg
      (analyticOnNhd_xiHermiteBiehler lam) hF₀A hnV hnF₀ hlt1 hlt2
      (fun x hx => hbd _ (hmemB x _ (hsqmem x _ hx (hl hlt2.le)) (Or.inr (by
        rw [show w.im - r - w.im = -r by ring, abs_neg, abs_of_pos hr0]))))
      (fun x hx => hbd _ (hmemB x _ (hsqmem x _ hx (hrr hlt2.le)) (Or.inr (by
        rw [show w.im + r - w.im = r by ring, abs_of_pos hr0]))))
      (fun t ht => hbd _ (hmemB _ t (hsqmem _ t (hrr hlt1.le) ht) (Or.inl (by
        rw [show w.re + r - w.re = r by ring, abs_of_pos hr0]))))
      (fun t ht => hbd _ (hmemB _ t (hsqmem _ t (hl hlt1.le) ht) (Or.inl (by
        rw [show w.re - r - w.re = -r by ring, abs_neg, abs_of_pos hr0]))))
    refine ⟨S₁, fun z => by rw [hS₁ z]; rfl, ?_⟩
    rw [hsum]
    -- the zeros of `λξ'` in `Q_w` are exactly `{w}`
    have hS₀eq : S₀ = {w} := by
      ext z
      rw [hS₀ z, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, h0⟩
        exact honly w hw z hz ((mul_eq_zero.mp h0).resolve_left hlamC)
      · intro hzw
        rw [hzw]
        refine ⟨(mem_closedSquare hr0.le).mpr (by simp [hr0.le]), ?_⟩
        simp only [hF₀]
        rw [((hZ₁mem w).mp hw).2, mul_zero]
    rw [hS₀eq, Finset.sum_singleton]
    congr 1
    have hmul : analyticOrderAt ((fun _ : ℂ => (lam : ℂ)) * deriv xi) w =
        analyticOrderAt (fun _ : ℂ => (lam : ℂ)) w + analyticOrderAt (deriv xi) w :=
      analyticOrderAt_mul analyticAt_const (analyticOnNhd_deriv_xi w trivial)
    have hc0 : analyticOrderAt (fun _ : ℂ => (lam : ℂ)) w = 0 :=
      (analyticOrderAt_eq_zero (f := fun _ : ℂ => (lam : ℂ)) (z₀ := w)).mpr (Or.inr hlamC)
    change analyticOrderAt ((fun _ : ℂ => (lam : ℂ)) * deriv xi) w = _
    rw [hmul, hc0, zero_add]
  -- sum over the disjoint squares
  choose! S hSmem hSsum using hsq
  have hsubset : Z₁.biUnion S ⊆ ZV := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hzQ, h0⟩ := (hSmem w hw z).mp hzw
    exact (hZV z).mpr ⟨hr_in w hw hzQ, h0⟩
  have hpd : (Z₁ : Set ℂ).PairwiseDisjoint S := by
    intro w hw w' hw' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    exact hdisj w hw w' hw' hne z ((hSmem w hw z).mp hz).1 ((hSmem w' hw' z).mp hz').1
  calc ∑ w ∈ Z₁, (analyticOrderAt (deriv xi) w).toNat
      = ∑ w ∈ Z₁, ∑ z ∈ S w, (analyticOrderAt (xiHermiteBiehler lam) z).toNat :=
        Finset.sum_congr rfl fun w hw => (hSsum w hw).symm
    _ = ∑ z ∈ Z₁.biUnion S, (analyticOrderAt (xiHermiteBiehler lam) z).toNat :=
        (Finset.sum_biUnion hpd).symm
    _ ≤ ∑ z ∈ ZV, (analyticOrderAt (xiHermiteBiehler lam) z).toNat :=
        Finset.sum_le_sum_of_subset hsubset

end

end RHTower
