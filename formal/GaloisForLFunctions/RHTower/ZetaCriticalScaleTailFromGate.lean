import GaloisForLFunctions.RHTower.ZetaOffLineFirstMomentLineCount
import GaloisForLFunctions.RHTower.ZetaTwoThirdsOffLineMomentConstant

/-!
# The off-line moment beyond the critical scale, from one mollified mean-square gate

Littlewood's lemma for the mollified detector `ζΨ` on `[σ₀, 15/2] × [T₁, T₂]`, `σ₀ = ½ − d`, charges
every zero of `ζ` in the rectangle, including the left zeros `σ₀ < Re ρ < ½`
(`exists_zetaWideMoment_le_of_mollified_meanSquare`):

  `2π Σ_{Re ρ ≥ σ₀} m_ρ (Re ρ − σ₀) ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`.

Pairing each zero with its reflection `1 − ρ̄`, `(x + d)⁺ + (d − x)⁺ = 2d + (x − d)⁺ + (−x − d)⁺`
(`x = Re ρ − ½`) gives the exact count identity

  `Σ_{Re ρ ≥ σ₀} m_ρ (Re ρ − σ₀) = d · N + Σ_ρ m_ρ (Re ρ − ½ − d)⁺`

(`sum_strip_posPart_eq`), with `N` the full zero count of the window.  On the Levinson line
`d = R/log T`, Riemann–von Mangoldt `d N ≈ R T/2π` cancels `2R` of the gate constant exactly, so the
off-line moment beyond the critical scale `R/log V` obeys

  `4π Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (log c − 2R + η) V`

(`eventually_offLineTail_le_of_zetaGate`), with no input on the proportion of zeros on the line.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

theorem exists_zetaWideMoment_le_of_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq
    Z hZ
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hlamN : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hG0 : ∀ z : ℂ, levinsonG ((0 : ℝ) : ℂ) z = riemannZeta z := by
    intro z
    simp [levinsonG]
  set Ψ : ℂ → ℂ := edPoly b s with hΨdef
  set g : ℂ → ℂ := levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s with hgdef
  set F : ℂ → ℂ := fun z => levinsonGEntire ((0 : ℝ) : ℂ) z * Ψ z with hFdef
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  -- the mollifier is close to one far to the right
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    rw [hΨdef] at h0
    have hre : (2 : ℝ) ≤ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re := by simp; norm_num
    have hd := norm_edPoly_sub_one_le_exp b hs h1mem hb1 hbn hre
    have hEsmall : Real.exp (-(Real.log 2) * ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
        ≤ 1 / 16 := by
      rw [exp_neg_log_two_eq]
      have hle : ((2 : ℝ) ^ (4 : ℝ))
          ≤ ((2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        simp; norm_num
      have h16 : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h16] at hle
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    rw [h0] at hd
    have hone : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [hone] at hd
    linarith
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hΨright T₁⟩
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    refine levinsonGEntire_ne_zero_of_four_le hlamN ?_
    simp; norm_num
  have hGright : ∀ t : ℝ,
      levinsonG ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    refine levinsonG_ne_zero_of_four_le hlamN ?_
    simp; norm_num
  have hG1' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [hG0]; exact hG1 x hx
  have hG2' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [hG0]; exact hG2 x hx
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20)]
    exact hG1' x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]
    exact hG2' x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        * Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire ((0 : ℝ) : ℂ)) Set.univ :=
    analyticOnNhd_levinsonGEntire _
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hGne : ∃ z : ℂ, levinsonGEntire ((0 : ℝ) : ℂ) z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hGeright T₁⟩
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan hGne w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨana hΨne w
  -- finiteness of the left-edge zero set and a nonzero point
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    have hre1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).re = σ₀ := by simp
    have him1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
    have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
    have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
    rwa [hre1, him1, hre2, him2] at h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht
    rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    constructor
    · intro h0
      have : F ((σ₀ : ℂ) + (t : ℂ) * I)
          = (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
        simp only [hFdef, hgdef, levinsonMollifiedDetector]
        rw [levinsonGEntire_eq _ hzne]
        ring
      rw [this, h0, mul_zero]
    · intro h0
      have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hzne
      have heq : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
        rw [← h0]
        simp only [hFdef, hgdef, levinsonMollifiedDetector]
        rw [levinsonGEntire_eq _ hzne]
        ring
      rcases mul_eq_zero.mp heq with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgauge
      · exact h
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_cases hall : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0
    · exact hall
    exfalso
    have hcon : ∀ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
      intro t ht
      by_contra h0
      exact hall ⟨t, ht, h0⟩
    have hsubset : Set.Ioo T₁ T₂ ⊆
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro t ht
      exact ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hcon t ht⟩
    exact (Set.Ioo_infinite hT) (hgfin.subset hsubset)
  -- the mean square hypothesis in detector form
  have hMsq' : (∫ t in T₁..T₂,
      ‖levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq := by
    refine le_trans (le_of_eq ?_) hMsq
    apply intervalIntegral.integral_congr
    intro t _
    simp only [levinsonMollifiedDetector, hG0]
    rfl
  -- the budget
  have hbud := hbudget 0 (by simp) b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' h20 hT hG1' hG2' hP1 hP2 hgfin hgex hMsq'
  -- gauge cancellation
  have hUopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct] at him
    rw [hEq, Complex.one_im] at him
    linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr hUopen hUsub ?_
    intro z hz
    simp only [hFdef, hgdef, levinsonMollifiedDetector]
    rw [levinsonGEntire_eq _ hz]
    ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [huIcct, Complex.one_im] at him
      linarith [him.1]
    · intro z hz
      have hzne : z ≠ 1 := hUsub hz
      exact analyticAt_levinsonMollifiedDetector _ b hs hzne
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG1' x hx) (hP1 x hx)
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG2' x hx) (hP2 x hx)
    · intro t _
      exact mul_ne_zero (hGright t) (hΨright t)
  -- the exact first-moment Littlewood identity for the entire product on the wide rectangle
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne hσ₀15 hT
      hFbot hFtop hFright
  -- every zeta zero of the narrow rectangle is a zero of `F` in the wide one
  have hsub : Z ⊆ Z' := by
    intro w hw
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    refine (hZ' w).mpr ⟨hwmem, ?_⟩
    · have hw1 : w ≠ 1 := by
        intro h
        rw [h] at hwzero
        exact riemannZeta_one_ne_zero hwzero
      simp only [hFdef]
      rw [levinsonGEntire_eq _ hw1, hG0, hwzero]
      ring
  -- orders: the entire detector at `λ = 0` has the order of `ζ` away from `1`
  have horderG : ∀ w ∈ Z,
      analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w = analyticOrderAt riemannZeta w := by
    intro w hw
    obtain ⟨_, hwzero⟩ := (hZ w).mp hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwzero
      exact riemannZeta_one_ne_zero hwzero
    have hev : levinsonGEntire ((0 : ℝ) : ℂ) =ᶠ[nhds w]
        (fun z : ℂ => (z - 1) ^ 2) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
      rw [Pi.mul_apply, levinsonGEntire_eq _ hz, hG0]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) w :=
      ((analyticAt_id.sub analyticAt_const).pow 2)
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hw1),
      (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hw1)), zero_add]
  have hterm : ∀ w ∈ Z,
      ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
        ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    obtain ⟨hwmem, _⟩ := (hZ w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    rw [huIccx] at hre
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨana w (Set.mem_univ _))
    have hord : ((analyticOrderAt riemannZeta w).toNat : ℝ)
        ≤ ((analyticOrderAt F w).toNat : ℝ) := by
      rw [hmul, ENat.toNat_add (hGorder w) (hPorder w), ← horderG w hw]
      push_cast
      have hnn : (0 : ℝ) ≤ ((analyticOrderAt Ψ w).toNat : ℝ) := Nat.cast_nonneg _
      linarith
    have hw0 : 0 ≤ w.re - σ₀ := by linarith [hre.1]
    exact mul_le_mul_of_nonneg_right hord hw0
  have hZ'nonneg : ∀ w ∈ Z', 0 ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    obtain ⟨hwmem, _⟩ := (hZ' w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum : ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
      ≤ ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
    le_trans (Finset.sum_le_sum hterm)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w hw _ => hZ'nonneg w hw))
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
      ≤ 2 * Real.pi * (∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀)) :=
        mul_le_mul_of_nonneg_left hsum hpi
    _ = weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ := hident
    _ = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by rw [hcongrF, hgaugefree]
    _ ≤ _ := hbud

/-- The zeros of `ζ` in the wide rectangle `[σ₀, 15/2] × [T₁, T₂]` form a finite set. -/
theorem exists_zetaWideRectangleZeros_finset {σ₀ T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ < T₂) :
    ∃ Z : Finset ℂ, ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
  classical
  set F := levinsonGEntire ((0 : ℝ) : ℂ) with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_levinsonGEntire _
  have hlamC : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I,
      levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)⟩
  have hfin := entire_zeros_closedRectangle_finite hFan hFne
    ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
  have hre1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).re = σ₀ := by simp
  have him1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
  have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
  have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
  rw [hre1, him1, hre2, him2] at hfin
  refine ⟨hfin.toFinset, fun z => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
  have hz1 : z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) → z ≠ 1 := by
    intro hmem h
    have him := (Complex.mem_reProdIm.mp hmem).2
    rw [h, Complex.one_im, uIcc_of_le hT.le] at him
    linarith [him.1]
  constructor
  · rintro ⟨hmem, hF0⟩
    refine ⟨hmem, ?_⟩
    rwa [hFdef, levinsonGEntire_eq_zero_iff _ (hz1 hmem), levinsonG_zero_eq] at hF0
  · rintro ⟨hmem, hζ0⟩
    refine ⟨hmem, ?_⟩
    rw [hFdef, levinsonGEntire_eq_zero_iff _ (hz1 hmem), levinsonG_zero_eq]
    exact hζ0

/-! ## The reflection count identity -/

noncomputable section

/-- The off-line moment beyond displacement `d`: `Σ_{0 < Im ρ ≤ T} m_ρ (Re ρ − ½ − d)⁺`. -/
def offLineTail (d T : ℝ) : ℝ :=
  ∑ z ∈ stripFinsetPos T, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0

theorem offLineTail_nonneg (d T : ℝ) : 0 ≤ offLineTail d T :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

theorem offLineTail_mono {d T T' : ℝ} (h : T ≤ T') : offLineTail d T ≤ offLineTail d T' :=
  Finset.sum_le_sum_of_subset_of_nonneg (stripFinsetPos_mono h) fun _ _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

theorem offLineTail_anti {d d' T : ℝ} (h : d ≤ d') : offLineTail d' T ≤ offLineTail d T :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left
    (max_le_max (by linarith) le_rfl) (Nat.cast_nonneg _)

/-- `(x + d)⁺ + (d − x)⁺ = 2d + (x − d)⁺ + (−x − d)⁺` for `d ≥ 0`. -/
theorem posPart_reflect_identity (x d : ℝ) (hd : 0 ≤ d) :
    max (x + d) 0 + max (d - x) 0 = 2 * d + max (x - d) 0 + max (-x - d) 0 := by
  rcases le_total x d with h1 | h1 <;> rcases le_total (-d) x with h2 | h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith)]
    ring

theorem sum_lineReflect_eq {t : Finset ℂ} (ht : ∀ z ∈ t, lineReflect z ∈ t) (f : ℂ → ℝ) :
    ∑ z ∈ t, f (lineReflect z) = ∑ z ∈ t, f z :=
  Finset.sum_nbij' lineReflect lineReflect ht ht (fun z _ => lineReflect_involutive z)
    (fun z _ => lineReflect_involutive z) (fun _ _ => rfl)

/-- **The reflection count identity.**  On a reflection-closed set of zeros of `ξ`, with
`σ₀ = ½ − d`, `Σ m_ρ (Re ρ − σ₀)⁺ = d Σ m_ρ + Σ m_ρ (Re ρ − ½ − d)⁺`. -/
theorem sum_strip_posPart_eq {t : Finset ℂ} (ht : ∀ z ∈ t, lineReflect z ∈ t) {d : ℝ}
    (hd : 0 ≤ d) :
    ∑ z ∈ t, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - (1 / 2 - d)) 0
      = d * ∑ z ∈ t, ((analyticOrderAt xi z).toNat : ℝ)
        + ∑ z ∈ t, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0 := by
  set m : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) with hm
  have hmr : ∀ z, m (lineReflect z) = m z := fun z => by
    simp only [hm, xi_orderAt_lineReflect]
  have hA := sum_lineReflect_eq ht (fun z => m z * max (z.re - (1 / 2 - d)) 0)
  have hB := sum_lineReflect_eq ht (fun z => m z * max (z.re - 1 / 2 - d) 0)
  simp only [hmr, lineReflect_re] at hA hB
  have hpt : ∀ z ∈ t, m z * max (z.re - (1 / 2 - d)) 0 + m z * max (1 - z.re - (1 / 2 - d)) 0
      = 2 * d * m z + m z * max (z.re - 1 / 2 - d) 0 + m z * max (1 - z.re - 1 / 2 - d) 0 := by
    intro z _
    have h := posPart_reflect_identity (z.re - 1 / 2) d hd
    rw [show z.re - (1 / 2 - d) = z.re - 1 / 2 + d by ring,
      show 1 - z.re - (1 / 2 - d) = d - (z.re - 1 / 2) by ring,
      show 1 - z.re - 1 / 2 - d = -(z.re - 1 / 2) - d by ring]
    linear_combination m z * h
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB,
    ← Finset.mul_sum] at hsum
  linarith

theorem lineReflect_mem_window {T₁ T₂ : ℝ} {z : ℂ}
    (hz : z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁) :
    lineReflect z ∈ stripFinsetPos T₂ \ stripFinsetPos T₁ := by
  rw [Finset.mem_sdiff] at hz ⊢
  refine ⟨lineReflect_mem_stripFinsetPos hz.1, fun h => hz.2 ?_⟩
  have := lineReflect_mem_stripFinsetPos h
  rwa [lineReflect_involutive] at this

/-- **The window bridge.**  The zeros of `ξ` with `T₁ < Im ρ ≤ T₂` are charged in the wide
rectangle: `d (N(T₂) − N(T₁)) + tail(T₂) − tail(T₁) ≤ Σ_Z m_ρ (Re ρ − σ₀)`. -/
theorem window_count_add_tail_le_zetaWideSum {d T₁ T₂ : ℝ} (hd : 0 ≤ d) (hT : T₁ ≤ T₂) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 - d) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + (offLineTail d T₂ - offLineTail d T₁)
      ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - (1 / 2 - d)) := by
  classical
  set S := stripFinsetPos T₂ \ stripFinsetPos T₁ with hS
  have hsub := stripFinsetPos_mono hT
  have hN : (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁
      = ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) := by
    unfold xiPosZeroCount
    have h := Finset.sum_sdiff (f := fun z => ((analyticOrderAt xi z).toNat : ℝ)) hsub
    push_cast
    linarith [h]
  have htail : offLineTail d T₂ - offLineTail d T₁
      = ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0 := by
    unfold offLineTail
    have h := Finset.sum_sdiff
      (f := fun z => ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - 1 / 2 - d) 0) hsub
    linarith [h]
  rw [hN, htail, ← sum_strip_posPart_eq (fun z hz => lineReflect_mem_window hz) hd]
  have hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ T₁ < z.im ∧ z.im ≤ T₂ ∧ xi z = 0 := by
    intro z hz
    have hz2 := (Finset.mem_sdiff.mp hz).1
    have hz1 := (Finset.mem_sdiff.mp hz).2
    rw [mem_stripFinsetPos] at hz2
    obtain ⟨h1, h2, h3, h4, hxi⟩ := hz2
    refine ⟨h1, h2, ?_, h4, hxi⟩
    by_contra hle
    push Not at hle
    exact hz1 (mem_stripFinsetPos.mpr ⟨h1, h2, h3, hle, hxi⟩)
  have hfilter : ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) * max (z.re - (1 / 2 - d)) 0
      = ∑ z ∈ S.filter (fun z => 1 / 2 - d ≤ z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - (1 / 2 - d)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z hz => ?_
    obtain ⟨h1, h2, -⟩ := hstrip z hz
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h1, h2⟩]
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith), mul_zero]
  rw [hfilter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro z hz
    obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp hz
    obtain ⟨h1, h2, h3, h4, hxi⟩ := hstrip z hzS
    rw [hZ]
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, (xi_zero_iff_zeta_zero_of_mem_strip h1 h2).mp hxi⟩
    · rw [uIcc_of_le (by linarith : (1 / 2 - d : ℝ) ≤ 15 / 2)]
      exact ⟨hre, by linarith⟩
    · rw [uIcc_of_le hT]
      exact ⟨h3.le, h4⟩
  · intro w hw _
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by linarith : (1 / 2 - d : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])

/-! ## The tail law from one gate -/

/-- **The off-line moment beyond the critical scale, from one mollified mean-square gate.**
For every `η > 0`, eventually `4π Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (log c − 2R + η) V`. -/
theorem eventually_offLineTail_le_of_zetaGate {R c₁ η : ℝ} (hR : 0 < R) (hc₁ : 1 ≤ c₁)
    (hη : 0 < η) (hg : ZetaMollifiedMeanSquareGate R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineTail (R / Real.log V) V ≤ (Real.log c₁ - 2 * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  set ε' : ℝ := η / (32 * Real.pi * R) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'R : 4 * Real.pi * R * ε' = η / 8 := by
    rw [hε']
    field_simp
    ring
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close ε' hε'0
  set B : ℝ := Real.log c₁ - 2 * R + η / 4 with hB
  set D : ℝ := |B| + 2 * C + 4 * Real.pi * (R / Real.log 20) * (xiPosZeroCount 21 : ℝ)
    + 4 * Real.pi * offLineTail 0 21 with hD
  have hε0 : 0 < c₁ * (η / 8) := by positivity
  have hlogε := log_gate_slack_le hc₁ hη
  have hlog20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * offLineTail (R / Real.log (U - 1)) (U - 1)
        ≤ (Real.log c₁ - 2 * R + η) * (U - 1) := by
    filter_upwards [hg (c₁ * (η / 8)) hε0, eventually_ge_atTop (max (T₀ + 1) 23),
      eventually_mul_log_le_quarter hK hη, eventually_const_le_quarter_sub_one D hη]
      with U hU hUbig hlogU hDU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_max_right _ _) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    obtain ⟨hT₂big, hT₂U⟩ := hT₂
    obtain ⟨hT₁20, hT₁21⟩ := hT₁
    have hT12 : T₁ < T₂ := by linarith
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    set d : ℝ := 1 / 2 - σ₀ with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have hdR : d * Real.log T₂ = R := hσ₀R
    have hσ₀eq : σ₀ = 1 / 2 - d := by rw [hd]; ring
    obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) hT₁20 hT12
    have hc := hwide b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂
      ((c₁ + c₁ * (η / 8)) * (T₂ - T₁)) hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + c₁ * (η / 8)) * (T₂ - T₁) / (T₂ - T₁))
        = Real.log (c₁ + c₁ * (η / 8)) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    have hZ' : ∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 - d) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
      rw [← hσ₀eq]; exact hZ
    have hbridge := window_count_add_tail_le_zetaWideSum hd0.le hT12.le Z hZ'
    rw [← hσ₀eq] at hbridge
    -- Riemann–von Mangoldt at `T₂`
    have hN₂ : (1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂) ≤ (xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ (by linarith)
      have hcast : ((xiZeroCount T₂ : ℤ) : ℝ) = (xiPosZeroCount T₂ : ℝ) := by
        rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      linarith
    have hdN₂ : R * T₂ * (1 / (2 * Real.pi) - ε') ≤ d * (xiPosZeroCount T₂ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hN₂ hd0.le
      have e : d * ((1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂))
          = (d * Real.log T₂) * T₂ * (1 / (2 * Real.pi) - ε') := by ring
      rw [e, hdR] at h
      exact h
    -- the window start
    have hdle : d ≤ R / Real.log 20 := by
      rw [le_div_iff₀ hlog20]
      have : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_left this hd0.le
      linarith only [this, hdR]
    have hN₁ : (xiPosZeroCount T₁ : ℝ) ≤ (xiPosZeroCount 21 : ℝ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁21)
    have hdN₁ : d * (xiPosZeroCount T₁ : ℝ) ≤ R / Real.log 20 * (xiPosZeroCount 21 : ℝ) :=
      mul_le_mul hdle hN₁ (Nat.cast_nonneg _) (by positivity)
    have htail₁ : offLineTail d T₁ ≤ offLineTail 0 21 :=
      (offLineTail_anti hd0.le).trans (offLineTail_mono hT₁21)
    -- the gate constant
    have hlc0 : 0 ≤ Real.log (c₁ + c₁ * (η / 8)) :=
      Real.log_nonneg (by linarith only [hc₁, hε0])
    have hlc : (T₂ - T₁) / 2 * Real.log (c₁ + c₁ * (η / 8))
        ≤ T₂ / 2 * (Real.log c₁ + η / 8) := by
      have h1 : (T₂ - T₁) / 2 * Real.log (c₁ + c₁ * (η / 8))
          ≤ T₂ / 2 * Real.log (c₁ + c₁ * (η / 8)) :=
        mul_le_mul_of_nonneg_right (by linarith) hlc0
      exact h1.trans (mul_le_mul_of_nonneg_left hlogε (by linarith))
    have hlogU' : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : K * (Real.log T₂ + Real.log Mb) ≤ 6 * K * Real.log U := by
      have : Real.log T₂ + Real.log Mb ≤ 6 * Real.log U := by linarith only [hlogMb, hlogU']
      have := mul_le_mul_of_nonneg_left this hK.le
      linarith only [this]
    have hmain : 4 * Real.pi * offLineTail d T₂
        ≤ T₂ * B + 2 * C + 12 * K * Real.log U
          + 4 * Real.pi * (R / Real.log 20) * (xiPosZeroCount 21 : ℝ)
          + 4 * Real.pi * offLineTail 0 21 := by
      have e1 : 2 * Real.pi * (R * T₂ * (1 / (2 * Real.pi) - ε')) = R * T₂ - T₂ * (η / 16) := by
        have : 2 * Real.pi * (R * T₂ * (1 / (2 * Real.pi) - ε'))
            = R * T₂ - T₂ * ((4 * Real.pi * R * ε') / 2) := by
          field_simp
          ring
        rw [this, hε'R]
        ring
      have h2π0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have h2π := mul_le_mul_of_nonneg_left hdN₂ h2π0
      rw [e1] at h2π
      have hA := mul_le_mul_of_nonneg_left hbridge h2π0
      have hdN₁' := mul_le_mul_of_nonneg_left hdN₁ h2π0
      have htail₁' := mul_le_mul_of_nonneg_left htail₁ h2π0
      have hBdef : T₂ * B = T₂ * Real.log c₁ - 2 * R * T₂ + T₂ * (η / 4) := by rw [hB]; ring
      linarith only [hc, hA, hlc, hKlog, hdN₁', htail₁', h2π, hBdef]
    have hTB : T₂ * B ≤ (U - 1) * B + |B| := by
      rcases le_or_gt 0 B with hB0 | hB0
      · have : T₂ * B ≤ U * B := mul_le_mul_of_nonneg_right hT₂U hB0
        rw [abs_of_nonneg hB0]
        linarith
      · have h0 : 0 ≤ (T₂ - (U - 1)) * (-B) := mul_nonneg (by linarith) (by linarith)
        rw [abs_of_neg hB0]
        linarith only [h0, hB0]
    have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
    have hmono : offLineTail (R / Real.log (U - 1)) (U - 1) ≤ offLineTail d T₂ := by
      have hd' : d ≤ R / Real.log (U - 1) := by
        rw [le_div_iff₀ hlogU1]
        have : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂big.le
        have := mul_le_mul_of_nonneg_left this hd0.le
        linarith only [this, hdR]
      exact (offLineTail_anti hd').trans (offLineTail_mono hT₂big.le)
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith)
      linarith only [h0]
    have hfin : (Real.log c₁ - 2 * R + η) * (U - 1) = (U - 1) * B + 3 * (η / 4 * (U - 1)) := by
      rw [hB]; ring
    have hπmono := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    rw [hfin]
    have hD' : D = |B| + 2 * C + 4 * Real.pi * (R / Real.log 20) * (xiPosZeroCount 21 : ℝ)
        + 4 * Real.pi * offLineTail 0 21 := hD
    linarith
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have := hshift.eventually hev
  simpa using this

end

end RHTower
