import GaloisForLFunctions.RHTower.LevinsonOddFiberFinal

/-!
# The first horizontal moment of off-line zeta zeros from a mollified mean square

Levinson's Littlewood budget, as built in this development for the mollified detector
`(ζ + λζ′)·Ψ`, is read here at `λ = 0` and as a *first-moment* rather than a counting statement.
For the residue-free product `ζ·Ψ` with `Ψ` a bounded-coefficient Dirichlet polynomial normalized
by `b 1 = 1`, the exact weighted Littlewood identity on `[σ₀, 15/2] × [T₁, T₂]` gives

```text
2π ∑_{ρ ∈ rectangle, Re ρ ≥ 1/2} m_ρ (Re ρ − 1/2)
    ≤ ½ (T₂ − T₁) · log( mean square of ζΨ on Re s = σ₀ ) + O(log T₂ + log Mb),
```

because the mollifier's own zeros only add nonnegative mass and every zero of `ζ` right of the
line carries horizontal weight at least `Re ρ − 1/2`.  Letting the abscissa tend to the critical
line from the left, the same bound holds with the mean square taken on the line itself.

By Littlewood's lemma the left-hand side is `∫_{T₁}^{T₂} log|ζ(1/2+it)| dt` up to `O(log T)`, so
this is an unconditional ceiling for the logarithmic mean of `|ζ|` on the critical line, and for
the average displacement of zeros from the line, in terms of one mollified second moment.  No zero
location or RH premise enters.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **Off-line first moment from a mollified mean square on a Levinson abscissa.**  With the
budget constants of `exists_levinson_mollified_budget_le`, the multiplicity-weighted sum of
`Re ρ − 1/2` over the zeta zeros in `[1/2, 15/2] × [T₁, T₂]` is controlled by the mean square of
`ζ·Ψ` on any abscissa `σ₀ ∈ [1/4, 1/2)`. -/
theorem exists_zetaOffLineFirstMoment_le_of_mollified_meanSquare :
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
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
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
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    have him := (Complex.mem_reProdIm.mp hwmem).2
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    refine (hZ' w).mpr ⟨?_, ?_⟩
    · refine Complex.mem_reProdIm.mpr ⟨?_, him⟩
      rw [huIccx]
      exact ⟨le_trans hσ₀'.le hre.1, hre.2⟩
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
      ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)
        ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    obtain ⟨hwmem, _⟩ := (hZ w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨana w (Set.mem_univ _))
    have hord : ((analyticOrderAt riemannZeta w).toNat : ℝ)
        ≤ ((analyticOrderAt F w).toNat : ℝ) := by
      rw [hmul, ENat.toNat_add (hGorder w) (hPorder w), ← horderG w hw]
      push_cast
      have hnn : (0 : ℝ) ≤ ((analyticOrderAt Ψ w).toNat : ℝ) := Nat.cast_nonneg _
      linarith
    have hw0 : 0 ≤ w.re - 1 / 2 := by linarith [hre.1]
    have hw1 : w.re - 1 / 2 ≤ w.re - σ₀ := by linarith
    calc ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)
        ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - 1 / 2) :=
          mul_le_mul_of_nonneg_right hord hw0
      _ ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
          mul_le_mul_of_nonneg_left hw1 (Nat.cast_nonneg _)
  have hZ'nonneg : ∀ w ∈ Z', 0 ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    obtain ⟨hwmem, _⟩ := (hZ' w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum : (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
      ≤ ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w hw _ => hZ'nonneg w hw)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi *
        (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
      ≤ 2 * Real.pi * (∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀)) :=
        mul_le_mul_of_nonneg_left hsum hpi
    _ = weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ := hident
    _ = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by rw [hcongrF, hgaugefree]
    _ ≤ _ := hbud

/-! ## Passing to the critical line -/

/-- Clamp an abscissa into `[1/4, 1/2]`. -/
def lineClamp (σ : ℝ) : ℝ := max (1 / 4) (min σ (1 / 2))

theorem lineClamp_mem (σ : ℝ) : lineClamp σ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := by
  unfold lineClamp
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem lineClamp_of_mem {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) : lineClamp σ = σ := by
  unfold lineClamp
  rw [min_eq_left hσ.2, max_eq_right hσ.1]

theorem continuous_lineClamp : Continuous lineClamp := by
  unfold lineClamp
  fun_prop

/-- The mollified mean square is continuous in the abscissa on `[1/4, 1/2]`. -/
theorem continuous_clamped_meanSquare (b : ℕ → ℂ) (N : ℕ) (T₁ T₂ : ℝ) :
    Continuous (fun σ : ℝ => ∫ t in T₁..T₂,
      ‖riemannZeta ((lineClamp σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((lineClamp σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  have hs : ∀ m ∈ Finset.Icc 1 N, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hΨ : Continuous (edPoly b (Finset.Icc 1 N)) :=
    (differentiable_edPoly b hs).continuous
  have hpt : Continuous (fun p : ℝ × ℝ => ((lineClamp p.1 : ℂ) + (p.2 : ℂ) * I)) :=
    (Complex.continuous_ofReal.comp (continuous_lineClamp.comp continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hne : ∀ p : ℝ × ℝ, ((lineClamp p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 1 := by
    intro p h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.one_re] at hre
    have := (lineClamp_mem p.1).2
    linarith
  have hζ : Continuous (fun p : ℝ × ℝ => riemannZeta ((lineClamp p.1 : ℂ) + (p.2 : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ContinuousAt.comp (g := riemannZeta)
      ((differentiableAt_riemannZeta (hne p)).continuousAt) hpt.continuousAt
  have hF : Continuous (Function.uncurry (fun σ t : ℝ =>
      ‖riemannZeta ((lineClamp σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((lineClamp σ : ℂ) + (t : ℂ) * I)‖ ^ 2)) := by
    have hΨp : Continuous (fun p : ℝ × ℝ =>
        edPoly b (Finset.Icc 1 N) ((lineClamp p.1 : ℂ) + (p.2 : ℂ) * I)) := hΨ.comp hpt
    exact ((hζ.mul hΨp).norm.pow 2)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF T₁ T₂

/-- **Off-line first moment from the mollified mean square on the critical line.**  The same
budget holds with the mean square of `ζ·Ψ` taken on `Re s = 1/2` itself, for heights whose
horizontal edges avoid the zeros of `ζ` and `Ψ` on `[1/4, 15/2]`. -/
theorem exists_zetaOffLineFirstMoment_le_of_line_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaOffLineFirstMoment_le_of_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq Z hZ
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  set m : ℝ → ℝ := fun σ : ℝ => ∫ t in T₁..T₂,
      ‖riemannZeta ((lineClamp σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((lineClamp σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hm
  have hmcont : Continuous m := continuous_clamped_meanSquare b N T₁ T₂
  have hmhalf : m (1 / 2) ≤ Msq := by
    simp only [hm]
    rw [lineClamp_of_mem (by norm_num)]
    exact hMsq
  -- the bound with `Msq + ε` for every `ε > 0`
  have hstep : ∀ ε : ℝ, 0 < ε →
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
        ≤ (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁))
            + C + K * (Real.log T₂ + Real.log Mb) := by
    intro ε hε
    have hcont : ContinuousAt m (1 / 2) := hmcont.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδε⟩ := hcont ε hε
    set σ₀ : ℝ := max (1 / 4) (1 / 2 - δ / 2) with hσ₀def
    have hσ₀ : 1 / 4 ≤ σ₀ := le_max_left _ _
    have hσ₀' : σ₀ < 1 / 2 := by
      rw [hσ₀def]
      apply max_lt (by norm_num)
      linarith
    have hσ₀mem : σ₀ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2) := ⟨hσ₀, hσ₀'.le⟩
    have hdist : dist σ₀ (1 / 2) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · have : 1 / 2 - δ / 2 ≤ σ₀ := le_max_right _ _
        linarith
    have hmσ₀ : m σ₀ ≤ Msq + ε := by
      have h := hδε hdist
      rw [Real.dist_eq, abs_sub_lt_iff] at h
      linarith [h.1, hmhalf]
    have hmσ₀' : (∫ t in T₁..T₂,
        ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq + ε := by
      have hcl : lineClamp σ₀ = σ₀ := lineClamp_of_mem hσ₀mem
      simp only [hm, hcl] at hmσ₀
      exact hmσ₀
    have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
      Set.Icc_subset_Icc hσ₀ le_rfl
    exact hmain b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ (Msq + ε) hσ₀ hσ₀' h20 hT
      (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
      (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) hmσ₀' Z hZ
  -- let `ε → 0⁺`
  have hlim : Tendsto (fun ε : ℝ =>
      (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
      (𝓝[>] 0) (𝓝 ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
        + C + K * (Real.log T₂ + Real.log Mb))) := by
    have hcont : ContinuousAt (fun ε : ℝ =>
        (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
        0 := by
      have hlog : ContinuousAt (fun ε : ℝ => Real.log ((Msq + ε) / (T₂ - T₁))) 0 := by
        apply ContinuousAt.comp (g := Real.log)
        · apply Real.continuousAt_log
          simp only [add_zero]
          exact (div_pos hMsqpos hlen).ne'
        · fun_prop
      exact ((continuousAt_const.mul hlog).add continuousAt_const).add continuousAt_const
    have h := hcont.tendsto
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hstep ε hε

end

end RHTower
