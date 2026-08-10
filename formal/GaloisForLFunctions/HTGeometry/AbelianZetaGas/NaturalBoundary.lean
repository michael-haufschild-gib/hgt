import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GrandResponse
import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.SeamStripRamification
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# The dilation organ has a natural boundary

The depth-`j` factor of the grand response vanishes when `j(σ+u)` is a nontrivial zeta zero, so
every zero `ρ` lands at `u = ρ/j − σ`.  Those landings have real part in `(−σ, −σ + 1/j]`, so they
can accumulate only on the line `Re u = −σ`; and because the completed zeta has zeros of
arbitrarily large ordinate, the quotients `ρ/j` come arbitrarily close to every purely imaginary
number, so every point of that line is an accumulation point of zeros of the response.  Since the
response is not identically zero on any disc of the chamber, no analytic function on a
neighbourhood of a boundary point can agree with it: the line is a natural boundary.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## Nontrivial zeta zeros of arbitrarily large ordinate -/

/-- The support of the global `Ξ` divisor is unbounded: an infinite closed discrete subset of the
plane cannot lie in a ball. -/
theorem exists_xi_divisor_norm_gt (R : ℝ) :
    ∃ ρ ∈ (MeromorphicOn.divisor RHTower.xi Set.univ).support, R < ‖ρ‖ := by
  by_contra h
  push Not at h
  have hsub : (MeromorphicOn.divisor RHTower.xi Set.univ).support
      ⊆ Metric.closedBall (0 : ℂ) R := by
    intro ρ hρ
    simpa [Metric.mem_closedBall, dist_eq_norm] using h ρ hρ
  have hclosed : IsClosed ((MeromorphicOn.divisor RHTower.xi Set.univ).support) :=
    (MeromorphicOn.divisor RHTower.xi Set.univ).closedSupport isClosed_univ
  have hcpt : IsCompact ((MeromorphicOn.divisor RHTower.xi Set.univ).support) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsub
  exact RHTower.xiDivisorSupport_infinite
    (hcpt.finite (MeromorphicOn.divisor RHTower.xi Set.univ).discreteSupport)

/-- **Nontrivial zeta zeros of arbitrarily large ordinate.** -/
theorem exists_zetaZero_abs_im_gt (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im| := by
  obtain ⟨ρ, hmem, hnorm⟩ := exists_xi_divisor_norm_gt (|T| + 1)
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit ⟨ρ, hmem⟩
  have hzero := RHTower.xi_eq_zero_of_mem_divisor_support ⟨ρ, hmem⟩
  have h0 : 0 < ρ.re := hstrip.1
  have h1 : ρ.re < 1 := hstrip.2
  have hre : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
  have hle : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := norm_le_abs_re_add_abs_im ρ
  refine ⟨ρ, (RHTower.xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hzero, h0, h1, ?_⟩
  have hTle : T ≤ |T| := le_abs_self T
  linarith

/-- The same, with the sign of the ordinate matched to a prescribed nonzero direction. -/
theorem exists_zetaZero_im_div_gt {t : ℝ} (ht : t ≠ 0) (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im / t := by
  obtain ⟨ρ, hz, h0, h1, him⟩ := exists_zetaZero_abs_im_gt (|T| * |t|)
  have htabs : 0 < |t| := abs_pos.mpr ht
  have hkey : |T| < |ρ.im| / |t| := by
    rw [lt_div_iff₀ htabs]
    exact him
  have hTle : T ≤ |T| := le_abs_self T
  rcases le_or_gt 0 (ρ.im / t) with hsign | hsign
  · refine ⟨ρ, hz, h0, h1, ?_⟩
    have habs : |ρ.im / t| = ρ.im / t := abs_of_nonneg hsign
    rw [abs_div] at habs
    linarith [habs ▸ hkey]
  · refine ⟨(starRingEnd ℂ) ρ, ?_, ?_, ?_, ?_⟩
    · rw [riemannZeta_conj, hz, map_zero]
    · simpa using h0
    · simpa using h1
    · have hconj : ((starRingEnd ℂ) ρ).im / t = -(ρ.im / t) := by
        simp [neg_div]
      have habs : |ρ.im / t| = -(ρ.im / t) := abs_of_neg hsign
      rw [abs_div] at habs
      rw [hconj]
      linarith [habs ▸ hkey]

/-! ## The quotients `ρ/j` reach every purely imaginary number -/

theorem norm_div_natCast_sub_mul_I_le (ρ : ℂ) (t : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ‖ρ / (j : ℂ) - (t : ℂ) * I‖ ≤ (|ρ.re| + |ρ.im - (j : ℝ) * t|) / (j : ℝ) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjC : ((j : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : j ≠ 0)
  have hsplit : ρ / (j : ℂ) - (t : ℂ) * I
      = (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I) / (j : ℂ) := by
    field_simp
    push_cast
    ring
  have hre : (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I).re = ρ.re := by
    simp [Complex.sub_re]
  have him : (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I).im = ρ.im - (j : ℝ) * t := by
    simp [Complex.sub_im]
  have hbound := norm_le_abs_re_add_abs_im (ρ - (((j : ℝ) * t : ℝ) : ℂ) * I)
  rw [hre, him] at hbound
  rw [hsplit, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hbound hjR.le

/-- **The landing points reach every purely imaginary number.**  For every `t` and every `ε > 0`
there are a nontrivial zeta zero `ρ` and a depth `j ≥ 1` with `‖ρ/j − it‖ < ε`. -/
theorem exists_zetaZero_depth_near (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℂ) (j : ℕ), riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 1 ≤ j
      ∧ ‖ρ / (j : ℂ) - (t : ℂ) * I‖ < ε := by
  rcases eq_or_ne t 0 with rfl | ht
  · obtain ⟨ρ, hz, h0, h1, _⟩ := exists_zetaZero_abs_im_gt 0
    obtain ⟨j, hj1, hjbig⟩ : ∃ j : ℕ, 1 ≤ j ∧ (|ρ.re| + |ρ.im|) / ε < (j : ℝ) := by
      refine ⟨⌊(|ρ.re| + |ρ.im|) / ε⌋₊ + 1, by omega, ?_⟩
      have := Nat.lt_floor_add_one ((|ρ.re| + |ρ.im|) / ε)
      push_cast
      linarith
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    refine ⟨ρ, j, hz, h0, h1, hj1, ?_⟩
    have hb := norm_div_natCast_sub_mul_I_le ρ 0 hj1
    have hval : (|ρ.re| + |ρ.im - (j : ℝ) * 0|) / (j : ℝ)
        = (|ρ.re| + |ρ.im|) / (j : ℝ) := by norm_num
    rw [hval] at hb
    have hlt : (|ρ.re| + |ρ.im|) / (j : ℝ) < ε := by
      rw [div_lt_iff₀ hjR]
      rw [div_lt_iff₀ hε] at hjbig
      linarith
    exact lt_of_le_of_lt hb hlt
  · set T : ℝ := (1 + |t|) / ε + 1 with hT
    obtain ⟨ρ, hz, h0, h1, him⟩ := exists_zetaZero_im_div_gt ht T
    have hTpos : 1 < T := by
      have : 0 < (1 + |t|) / ε := by positivity
      rw [hT]; linarith
    have hq : (1 : ℝ) < ρ.im / t := lt_trans hTpos him
    set j : ℕ := ⌊ρ.im / t⌋₊ with hjdef
    have hj1 : 1 ≤ j := Nat.le_floor (by exact_mod_cast hq.le)
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hjle : (j : ℝ) ≤ ρ.im / t := Nat.floor_le (by linarith)
    have hjgt : ρ.im / t < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have htabs : 0 < |t| := abs_pos.mpr ht
    have hdiff : |ρ.im - (j : ℝ) * t| < |t| := by
      have hfac : ρ.im - (j : ℝ) * t = t * (ρ.im / t - (j : ℝ)) := by
        field_simp
      rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ.im / t - (j : ℝ))]
      nlinarith
    have hreabs : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith, h1⟩
    have hjbig : (1 + |t|) / ε < (j : ℝ) := by
      have : T - 1 < (j : ℝ) := by linarith
      rw [hT] at this
      linarith
    refine ⟨ρ, j, hz, h0, h1, hj1, ?_⟩
    refine lt_of_le_of_lt (norm_div_natCast_sub_mul_I_le ρ t hj1) ?_
    rw [div_lt_iff₀ hjR]
    rw [div_lt_iff₀ hε] at hjbig
    nlinarith

/-! ## Every zeta zero lands at every depth -/

theorem div_natCast_re (w : ℂ) {j : ℕ} (hj : j ≠ 0) : (w / (j : ℂ)).re = w.re / (j : ℝ) := by
  have hjR : ((j : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hj
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp

/-- The landing point of a zeta zero at depth `j`. -/
def landing (σ : ℝ) (w : ℂ) (j : ℕ) : ℂ := w / (j : ℂ) - ((σ : ℝ) : ℂ)

theorem re_landing (σ : ℝ) (w : ℂ) {j : ℕ} (hj : j ≠ 0) :
    (landing σ w j).re = w.re / (j : ℝ) - σ := by
  rw [landing, Complex.sub_re, div_natCast_re w hj, Complex.ofReal_re]

/-- **The landings sit in the chamber and hug the boundary line.**  A zero of real part in `(0,1)`
lands at real part in `(−σ, −σ + 1/j]`, so depth `j` pushes the landing to within `1/j` of the
line `Re u = −σ`. -/
theorem re_landing_mem (σ : ℝ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) {j : ℕ} (hj : 1 ≤ j) :
    -σ < (landing σ w j).re ∧ (landing σ w j).re < -σ + 1 / (j : ℝ) := by
  have hjne : j ≠ 0 := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  rw [re_landing σ w hjne]
  constructor
  · have : 0 < w.re / (j : ℝ) := div_pos hw0 hjR
    linarith
  · have hstep : w.re / (j : ℝ) < 1 / (j : ℝ) := by gcongr
    linarith

/-- **The grand response vanishes at every landing.**  The depth-`j` factor of the response is
`ζ(j(σ+u))`, which at `u = w/j − σ` is `ζ(w)`. -/
theorem grandResponse_landing_eq_zero (σ : ℝ) {w : ℂ} (hw : riemannZeta w = 0)
    (hw0 : 0 < w.re) {j : ℕ} (hj : 1 ≤ j) :
    grandResponse σ 0 (landing σ w j) = 0 := by
  have hjne : j ≠ 0 := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjC : ((j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hjne
  have hre : 0 < σ + (landing σ w j).re := by
    rw [re_landing σ w hjne]
    have : 0 < w.re / (j : ℝ) := div_pos hw0 hjR
    linarith
  have harg : ((σ : ℝ) : ℂ) + landing σ w j = w / (j : ℂ) := by
    rw [landing]; ring
  have hfac : depthFactor σ 0 j (landing σ w j) = 0 := by
    rw [depthFactor, harg, mul_div_cancel₀ _ hjC, add_zero, hw]
  have hmem : j - 1 ∈ Finset.range j := Finset.mem_range.mpr (by omega)
  have hprod : depthProduct σ 0 j (landing σ w j) = 0 := by
    refine Finset.prod_eq_zero hmem ?_
    have hidx : j - 1 + 1 = j := by omega
    rw [hidx]
    exact hfac
  rw [grandResponse_split σ 0 hre j, hprod, zero_mul]

/-- **Every point of the line `Re u = −σ` is a limit of zeros of the dilation organ.** -/
theorem exists_grandResponse_zero_near (σ : ℝ) {p : ℂ} (hp : p.re = -σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℂ, ‖u - p‖ < ε ∧ -σ < u.re ∧ grandResponse σ 0 u = 0 := by
  obtain ⟨ρ, j, hz, h0, h1, hj, hnear⟩ := exists_zetaZero_depth_near p.im hε
  refine ⟨landing σ ρ j, ?_, (re_landing_mem σ h0 h1 hj).1,
    grandResponse_landing_eq_zero σ hz h0 hj⟩
  have hpform : p = -((σ : ℝ) : ℂ) + ((p.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hp]
  have hdiff : landing σ ρ j - p = ρ / (j : ℂ) - ((p.im : ℝ) : ℂ) * I := by
    rw [landing]
    conv_lhs => rw [hpform]
    ring
  rw [hdiff]
  exact hnear

/-! ## The response is not identically zero on any disc of the chamber -/

/-- On a compact real segment only finitely many parameters put a fixed depth-`i` argument on a
zeta zero. -/
theorem finite_zetaZero_segment (σ : ℝ) (u₀ : ℂ) (i : ℕ) (b : ℝ) :
    {s : ℝ | s ∈ Set.Icc (0 : ℝ) b ∧
      riemannZeta (((i + 1 : ℕ) : ℂ) * ((σ : ℝ) + (u₀ + (s : ℂ)))) = 0}.Finite := by
  classical
  set ψ : ℝ → ℂ := fun s => ((i + 1 : ℕ) : ℂ) * ((σ : ℝ) + (u₀ + (s : ℂ))) with hψ
  have hcont : Continuous ψ := by
    rw [hψ]
    fun_prop
  have hinj : Function.Injective ψ := by
    intro s₁ s₂ h
    rw [hψ] at h
    have hne : ((i + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 := mul_left_cancel₀ hne h
    have h3 : ((s₁ : ℝ) : ℂ) = ((s₂ : ℝ) : ℂ) := by
      have := congrArg (fun z : ℂ => z - ((σ : ℝ) + u₀)) h2
      simpa using this
    exact Complex.ofReal_injective h3
  have hcpt : IsCompact (ψ '' Set.Icc (0 : ℝ) b) :=
    (isCompact_Icc).image hcont
  have hfin : ((ψ '' Set.Icc (0 : ℝ) b) ∩ riemannZetaZeros).Finite :=
    hcpt.inter_riemannZetaZeros_finite
  refine Set.Finite.of_finite_image (f := ψ) (hfin.subset ?_) (hinj.injOn)
  rintro z ⟨s, ⟨hs, hzero⟩, rfl⟩
  exact ⟨⟨s, hs, rfl⟩, by rw [mem_riemannZetaZeros]; exact hzero⟩

/-- **The dilation organ is not identically zero on any disc of the chamber.**  Its zeros are
carried by finitely many pulled-back zeta zero sets on every compact piece, so every disc contains
a point where the response does not vanish. -/
theorem exists_grandResponse_ne_zero_near (σ : ℝ) {u₀ : ℂ} (hu₀ : 0 < σ + u₀.re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℂ, ‖u - u₀‖ < δ ∧ 0 < σ + u.re ∧ grandResponse σ 0 u ≠ 0 := by
  classical
  set a₀ : ℝ := (σ + u₀.re) / 2 with ha₀def
  have ha₀ : 0 < a₀ := by rw [ha₀def]; linarith
  set J : ℕ := max 1 (depthTailThreshold 0 a₀) with hJdef
  set b : ℝ := δ / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  -- the bad parameters form a finite set
  set bad : Set ℝ := ⋃ i ∈ Finset.range J,
    {s : ℝ | s ∈ Set.Icc (0 : ℝ) b ∧
      riemannZeta (((i + 1 : ℕ) : ℂ) * ((σ : ℝ) + (u₀ + (s : ℂ)))) = 0} with hbaddef
  have hbadfin : bad.Finite := by
    rw [hbaddef]
    exact Set.Finite.biUnion (Finset.range J).finite_toSet
      (fun i _ => finite_zetaZero_segment σ u₀ i b)
  have hinf : (Set.Ioo (0 : ℝ) b).Infinite :=
    Set.infinite_coe_iff.mp (Set.Ioo.infinite hb)
  obtain ⟨s, hs, hsbad⟩ := hinf.exists_notMem_finite hbadfin
  refine ⟨u₀ + (s : ℂ), ?_, ?_, ?_⟩
  · have : ‖u₀ + (s : ℂ) - u₀‖ = |s| := by
      simp [Complex.norm_real]
    rw [this, abs_of_pos hs.1]
    rw [hbdef] at hs
    linarith [hs.2]
  · have hre : (u₀ + (s : ℂ)).re = u₀.re + s := by simp
    rw [hre]
    linarith [hs.1]
  · have hre : (u₀ + (s : ℂ)).re = u₀.re + s := by simp
    have hchamber : 0 < σ + (u₀ + (s : ℂ)).re := by rw [hre]; linarith [hs.1]
    have hge : a₀ ≤ σ + (u₀ + (s : ℂ)).re := by
      rw [hre, ha₀def]
      linarith [hs.1]
    have hJthr : depthTailThreshold 0 a₀ ≤ J + 1 := by
      rw [hJdef]
      omega
    have htail : (∏' j : ℕ, depthFactor σ 0 (j + (J + 1)) (u₀ + (s : ℂ))) ≠ 0 :=
      tprod_depthFactor_tail_ne_zero σ 0 ha₀ hge hJthr
    have hcongr : (∏' j : ℕ, depthFactor σ 0 (j + J + 1) (u₀ + (s : ℂ)))
        = ∏' j : ℕ, depthFactor σ 0 (j + (J + 1)) (u₀ + (s : ℂ)) :=
      tprod_congr fun j => by rw [show j + J + 1 = j + (J + 1) by omega]
    have htail' : (∏' j : ℕ, depthFactor σ 0 (j + J + 1) (u₀ + (s : ℂ))) ≠ 0 := by
      rw [hcongr]
      exact htail
    have hprod : depthProduct σ 0 J (u₀ + (s : ℂ)) ≠ 0 := by
      rw [depthProduct, Finset.prod_ne_zero_iff]
      intro i hi
      rw [depthFactor, add_zero]
      intro hzero
      refine hsbad ?_
      rw [hbaddef]
      exact Set.mem_biUnion hi ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩, hzero⟩
    rw [grandResponse_split σ 0 hchamber J]
    exact mul_ne_zero hprod htail'

/-! ## The line `Re u = −σ` is a natural boundary -/

/-- **Theorem 6.1, item 1: the natural boundary.**  No function analytic at a point `p` of the line
`Re u = −σ` can agree with the dilation organ on the chamber side of a neighbourhood of `p`.  The
zeros of the organ accumulate at `p`, which would force the extension to vanish identically near
`p`, while the organ is nonzero somewhere in every disc of the chamber. -/
theorem no_analytic_extension (σ : ℝ) {p : ℂ} (hp : p.re = -σ) {r : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p)
    (hagree : ∀ u : ℂ, ‖u - p‖ < r → -σ < u.re → g u = grandResponse σ 0 u) :
    False := by
  have hzero : ∀ᶠ z in 𝓝 p, g z = 0 := by
    rcases hg.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exfalso
      rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at h
      obtain ⟨ε, hε, hsub⟩ := h
      obtain ⟨u, hnear, hre, hFzero⟩ :=
        exists_grandResponse_zero_near σ hp (lt_min hε hr)
      have hball : u ∈ Metric.ball p ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hnear (min_le_left _ _)
      have hnep : u ∈ ({p}ᶜ : Set ℂ) := by
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        rw [hmem, hp] at hre
        exact lt_irrefl _ hre
      have hgne := hsub ⟨hball, hnep⟩
      have hgu : g u = grandResponse σ 0 u :=
        hagree u (lt_of_lt_of_le hnear (min_le_right _ _)) hre
      exact hgne (by rw [hgu, hFzero])
  rw [Metric.eventually_nhds_iff] at hzero
  obtain ⟨δ, hδ, hδz⟩ := hzero
  set η : ℝ := min δ r with hηdef
  have hη : 0 < η := lt_min hδ hr
  have hηδ : η ≤ δ := min_le_left _ _
  have hηr : η ≤ r := min_le_right _ _
  set u₀ : ℂ := p + ((η / 2 : ℝ) : ℂ) with hu₀def
  have hu₀re : u₀.re = -σ + η / 2 := by
    rw [hu₀def]
    simp [hp]
  have hu₀chamber : 0 < σ + u₀.re := by rw [hu₀re]; linarith
  obtain ⟨u, hnear, hchamber, hne⟩ :=
    exists_grandResponse_ne_zero_near σ hu₀chamber (δ := η / 4) (by linarith)
  have hu₀p : ‖u₀ - p‖ = η / 2 := by
    have hsub : u₀ - p = ((η / 2 : ℝ) : ℂ) := by rw [hu₀def]; ring
    rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ η / 2)]
  have hup : ‖u - p‖ < η := by
    have hdecomp : u - p = (u - u₀) + (u₀ - p) := by ring
    have hle : ‖u - p‖ ≤ ‖u - u₀‖ + ‖u₀ - p‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    rw [hu₀p] at hle
    linarith
  have hgu0 : g u = 0 := by
    refine hδz ?_
    rw [dist_eq_norm]
    linarith
  have hgu : g u = grandResponse σ 0 u :=
    hagree u (lt_of_lt_of_le hup hηr) (by linarith)
  exact hne (by rw [← hgu, hgu0])

/-! ## The singularities accumulate only on the line -/

theorem finite_zetaZero_ball (σ : ℝ) (i : ℕ) (c : ℂ) (R : ℝ) :
    {u : ℂ | u ∈ Metric.closedBall c R ∧
      riemannZeta (((i + 1 : ℕ) : ℂ) * ((σ : ℝ) + u)) = 0}.Finite := by
  classical
  set φ : ℂ → ℂ := fun u => ((i + 1 : ℕ) : ℂ) * ((σ : ℝ) + u) with hφ
  have hcont : Continuous φ := by
    rw [hφ]
    fun_prop
  have hinj : Function.Injective φ := by
    intro u₁ u₂ h
    rw [hφ] at h
    have hne : ((i + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 := mul_left_cancel₀ hne h
    have := congrArg (fun z : ℂ => z - ((σ : ℝ) : ℂ)) h2
    simpa using this
  have hcpt : IsCompact (φ '' Metric.closedBall c R) :=
    (isCompact_closedBall c R).image hcont
  have hfin : ((φ '' Metric.closedBall c R) ∩ riemannZetaZeros).Finite :=
    hcpt.inter_riemannZetaZeros_finite
  refine Set.Finite.of_finite_image (f := φ) (hfin.subset ?_) (hinj.injOn)
  rintro z ⟨u, ⟨hu, hzero⟩, rfl⟩
  exact ⟨⟨u, hu, rfl⟩, by rw [mem_riemannZetaZeros]; exact hzero⟩

/-- **The zeros of the dilation organ accumulate only on the boundary line.**  Inside any compact
set and at any positive distance from the line `Re u = −σ` there are only finitely many of them. -/
theorem finite_grandResponse_zeros (σ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀) (c : ℂ) (R : ℝ) :
    {u : ℂ | u ∈ Metric.closedBall c R ∧ a₀ ≤ σ + u.re
      ∧ grandResponse σ 0 u = 0}.Finite := by
  classical
  set J : ℕ := max 1 (depthTailThreshold 0 a₀) with hJdef
  refine Set.Finite.subset
    (Set.Finite.biUnion (Finset.range J).finite_toSet
      (fun i _ => finite_zetaZero_ball σ i c R)) ?_
  rintro u ⟨hu, hge, hFzero⟩
  have hchamber : 0 < σ + u.re := lt_of_lt_of_le ha₀ hge
  have hJthr : depthTailThreshold 0 a₀ ≤ J + 1 := by
    rw [hJdef]
    omega
  have htail : (∏' j : ℕ, depthFactor σ 0 (j + (J + 1)) u) ≠ 0 :=
    tprod_depthFactor_tail_ne_zero σ 0 ha₀ hge hJthr
  have hcongr : (∏' j : ℕ, depthFactor σ 0 (j + J + 1) u)
      = ∏' j : ℕ, depthFactor σ 0 (j + (J + 1)) u :=
    tprod_congr fun j => by rw [show j + J + 1 = j + (J + 1) by omega]
  have htail' : (∏' j : ℕ, depthFactor σ 0 (j + J + 1) u) ≠ 0 := by
    rw [hcongr]; exact htail
  have hprod : depthProduct σ 0 J u = 0 := by
    have hsplit := grandResponse_split σ 0 hchamber J
    rw [hFzero] at hsplit
    rcases mul_eq_zero.mp hsplit.symm with h | h
    · exact h
    · exact absurd h htail'
  rw [depthProduct] at hprod
  obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine Set.mem_biUnion hi ⟨hu, ?_⟩
  rw [depthFactor, add_zero] at hzero
  exact hzero

end

end GaloisForLFunctions.HTGeometry
