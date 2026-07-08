/-
The unconditional annulus supply: domination without analytic interfaces.

On a fixed annulus inside the critical strip the Euler–Maclaurin representation makes
carrier accuracy a theorem rather than an interface: the remainder bound
`‖ζ − emCarrier N‖ ≤ ‖s‖·N^(−re s)/re s` tends to zero uniformly on the compact annulus
as `N → ∞`, while isolation of ξ-zeros gives ζ a positive floor there by compactness.
For `N` large the completed EM member `archFactor · emCarrier N` therefore dominates ξ
on the two slit charts of an isolating annulus — with no analytic hypothesis remaining.
Consequently every rung of the multiplicity ladder, and the Riemann Hypothesis itself,
reduces to the divisibility of the hole-zero count of an explicit finite-data member on
one isolating annulus per hypothetical off-line zero; such annuli, truncation lengths
and dominating splits exist unconditionally at every strip point.
-/
import GaloisForLFunctions.RHTower.EMCarrier
import GaloisForLFunctions.RHTower.CarrierSplit
import GaloisForLFunctions.RHTower.ArchEnvelope

noncomputable section

namespace RHTower

open Complex Metric Filter

/-! ### §1 Right-half ξ-zeros lie in the open strip -/

/-- A ξ-zero with positive real part has real part below one: ζ is zero-free on
`re ≥ 1` and ξ(1) = 1/2. -/
theorem xi_zero_re_lt_one {ρ : ℂ} (h0 : 0 < ρ.re) (hzero : xi ρ = 0) : ρ.re < 1 := by
  by_contra hge
  have hge' : 1 ≤ ρ.re := not_lt.mp hge
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, xi_one] at hzero
    norm_num at hzero
  exact riemannZeta_ne_zero_of_one_le_re hge' ((xi_eq_zero_iff h0 hρ1).mp hzero)

/-! ### §2 The completed EM member -/

/-- The completed EM member: the archimedean dressing of the Euler–Maclaurin carrier. -/
def completedEM (N : ℕ) : ℂ → ℂ := fun s => archFactor s * emCarrier N s

/-- The completed EM member is analytic on the open critical strip. -/
theorem completedEM_analyticOnNhd_strip {N : ℕ} (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (completedEM N) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  exact (archFactor_analyticOnNhd_re_pos z hz.1).mul (emCarrier_analyticAt_of_ne_one hN hz1)

/-- The archimedean factor divides out: completed-level domination for the EM member is
equivalent to the raw inequality `‖ζ − emCarrier N‖ < ‖emCarrier N‖`. -/
theorem completedEM_domination_iff {N : ℕ} {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    (‖xi s - completedEM N s‖ < ‖completedEM N s‖)
      ↔ (‖riemannZeta s - emCarrier N s‖ < ‖emCarrier N s‖) := by
  unfold completedEM
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  exact norm_mul_sub_lt_iff (archFactor_ne_zero h0 h1 hG)

/-! ### §3 The ζ floor on the closed annulus -/

/-- The closed annulus is nonempty. -/
theorem annulus_closed_nonempty {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R) :
    (closedBall ρ R \ ball ρ r₀).Nonempty := by
  obtain ⟨hP, -⟩ := annulus_basepoints_mem (a := ρ) h0 hrR
  exact ⟨_, ball_subset_closedBall hP.1.2.1,
    fun hb => hP.1.2.2 (ball_subset_closedBall hb)⟩

/-- **ζ holds a positive floor on the closed annulus of an isolating ball inside the
strip**: by isolation the only possible ξ-zero in the closed ball is the centre, which
the annulus excludes, and the norm attains a positive minimum on the compact annulus. -/
theorem zeta_annulus_floor {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ closedBall ρ R \ ball ρ r₀, δ ≤ ‖riemannZeta z‖ := by
  set K := closedBall ρ R \ ball ρ r₀ with hKdef
  have hKsub : K ⊆ closedBall ρ R := fun z hz => hz.1
  have hKcompact : IsCompact K := (isCompact_closedBall ρ R).diff isOpen_ball
  have hz1K : ∀ z ∈ K, z ≠ 1 := by
    intro z hz h
    have hlt := (hstrip z (hKsub hz)).2
    rw [h] at hlt
    simp at hlt
  have hζcont : ContinuousOn riemannZeta K := fun z hz =>
    (differentiableAt_riemannZeta (hz1K z hz)).continuousAt.continuousWithinAt
  have hζne : ∀ z ∈ K, riemannZeta z ≠ 0 := by
    intro z hz hζ0
    have hzρ : z ≠ ρ := by
      intro h
      exact hz.2 (by rw [h]; exact mem_ball_self hr₀)
    exact hiso z (hKsub hz) hzρ
      ((xi_eq_zero_iff (hstrip z (hKsub hz)).1 (hz1K z hz)).mpr hζ0)
  obtain ⟨x, hxK, hmin⟩ :=
    hKcompact.exists_isMinOn (annulus_closed_nonempty hr₀.le hrR) hζcont.norm
  exact ⟨‖riemannZeta x‖, norm_pos_iff.mpr (hζne x hxK), fun z hz => hmin hz⟩

/-! ### §4 Domination for large truncation length -/

/-- **Unconditional raw domination on an isolating annulus.**  Inside the strip, on the
closed annulus of an isolating ball, the Euler–Maclaurin carrier dominates ζ for some
truncation length: the EM remainder decays like `N^(−σ₀)` uniformly on the compact
annulus while ζ holds a positive floor there. -/
theorem exists_em_domination_on_annulus {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ closedBall ρ R \ ball ρ r₀,
      ‖riemannZeta z - emCarrier N z‖ < ‖emCarrier N z‖ := by
  obtain ⟨δ, hδ, hfloor⟩ := zeta_annulus_floor hr₀ hrR hstrip hiso
  set K := closedBall ρ R \ ball ρ r₀ with hKdef
  have hKsub : K ⊆ closedBall ρ R := fun z hz => hz.1
  have hKcompact : IsCompact K := (isCompact_closedBall ρ R).diff isOpen_ball
  obtain ⟨w, hwK, hwmin⟩ := hKcompact.exists_isMinOn
    (annulus_closed_nonempty hr₀.le hrR) Complex.continuous_re.continuousOn
  set σ₀ := w.re with hσ₀def
  have hσ₀pos : 0 < σ₀ := (hstrip w (hKsub hwK)).1
  have hσ₀le : ∀ z ∈ K, σ₀ ≤ z.re := fun z hz => hwmin hz
  have hRpos : 0 < R := lt_trans hr₀ hrR
  have hCpos : 0 < ‖ρ‖ + R := add_pos_of_nonneg_of_pos (norm_nonneg ρ) hRpos
  have hCnorm : ∀ z ∈ K, ‖z‖ ≤ ‖ρ‖ + R := by
    intro z hz
    have h1 : ‖z - ρ‖ ≤ R := by
      have h := hKsub hz
      rwa [mem_closedBall, dist_eq_norm] at h
    calc ‖z‖ = ‖ρ + (z - ρ)‖ := by rw [show ρ + (z - ρ) = z from by ring]
      _ ≤ ‖ρ‖ + ‖z - ρ‖ := norm_add_le _ _
      _ ≤ ‖ρ‖ + R := by linarith
  set ε' := δ / 2 * σ₀ / (‖ρ‖ + R) with hε'def
  have hε'pos : 0 < ε' := div_pos (mul_pos (half_pos hδ) hσ₀pos) hCpos
  have htend : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-σ₀)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hσ₀pos).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNε, hN1⟩ :=
    ((htend.eventually (gt_mem_nhds hε'pos)).and (eventually_ge_atTop 1)).exists
  refine ⟨N, hN1, ?_⟩
  intro z hz
  have hzre : 0 < z.re := (hstrip z (hKsub hz)).1
  have hz1 : z ≠ 1 := by
    intro h
    have hlt := (hstrip z (hKsub hz)).2
    rw [h] at hlt
    simp at hlt
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have herr : ‖riemannZeta z - emCarrier N z‖ ≤ (‖ρ‖ + R) * (N : ℝ) ^ (-σ₀) / σ₀ := by
    refine le_trans (zeta_sub_emCarrier_norm_le hN1 hzre hz1) ?_
    have hb2 : (N : ℝ) ^ (-z.re) ≤ (N : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [hσ₀le z hz])
    have hb0 : (0 : ℝ) ≤ (N : ℝ) ^ (-z.re) := Real.rpow_nonneg (by linarith) _
    exact div_le_div₀
      (mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _))
      (mul_le_mul (hCnorm z hz) hb2 hb0 hCpos.le) hσ₀pos (hσ₀le z hz)
  have hlt : (‖ρ‖ + R) * (N : ℝ) ^ (-σ₀) / σ₀ < δ / 2 := by
    have hstep : (‖ρ‖ + R) * (N : ℝ) ^ (-σ₀) / σ₀ < (‖ρ‖ + R) * ε' / σ₀ := by gcongr
    have heq : (‖ρ‖ + R) * ε' / σ₀ = δ / 2 := by
      rw [hε'def]
      field_simp
    rwa [heq] at hstep
  have herr2 : ‖riemannZeta z - emCarrier N z‖ < δ / 2 := lt_of_le_of_lt herr hlt
  have hfloorz : δ ≤ ‖riemannZeta z‖ := hfloor z hz
  have htri : ‖riemannZeta z‖ ≤ ‖riemannZeta z - emCarrier N z‖ + ‖emCarrier N z‖ := by
    calc ‖riemannZeta z‖ = ‖riemannZeta z - emCarrier N z + emCarrier N z‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-! ### §5 The unconditional isolating supply at every strip point -/

/-- **Isolating annulus with completed-member domination — unconditional.**  Around any
point of the open critical strip there are an isolating annulus and a truncation length
whose completed Euler–Maclaurin member dominates ξ on the two slit charts. -/
theorem exists_isolating_em_domination (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ (r₀ R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖xi z - completedEM N z‖ < ‖completedEM N z‖) := by
  obtain ⟨R₁, hR₁, hiso₁⟩ := xi_exists_isolating_radius ρ
  set R := min (R₁ / 2) (min (ρ.re / 2) ((1 - ρ.re) / 2)) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hRR₁ : R < R₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRre : R ≤ ρ.re / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRre1 : R ≤ (1 - ρ.re) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hstripcb : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - ρ.re| ≤ R := by
      have h := Complex.abs_re_le_norm (z - ρ)
      rw [Complex.sub_re] at h
      linarith
    rw [abs_le] at hre
    constructor
    · linarith [hre.1]
    · linarith [hre.2]
  have hisocb : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0 := by
    intro z hz
    apply hiso₁
    rw [mem_ball]
    rw [mem_closedBall] at hz
    linarith
  obtain ⟨N, hN1, hdomK⟩ := exists_em_domination_on_annulus
    (r₀ := R / 2) (by linarith) (by linarith) hstripcb hisocb
  refine ⟨R / 2, R, N, by linarith, by linarith, hN1,
    fun z hz => hstripcb z (ball_subset_closedBall hz),
    fun z hz => hisocb z (ball_subset_closedBall hz), ?_⟩
  intro z hz
  have hzK : z ∈ closedBall ρ R \ ball ρ (R / 2) := by
    rw [charts_union_eq_annulus ρ (by linarith : (0 : ℝ) ≤ R / 2)] at hz
    exact ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩
  have hstripz := hstripcb z hzK.1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hstripz
    simp at hstripz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hstripz
    simp at hstripz
  exact (completedEM_domination_iff hz0 hz1
    (Gammaℝ_ne_zero_of_re_pos hstripz.1)).mpr (hdomK z hzK)

/-! ### §6 Dominating splits as a datum, their unconditional existence, and the rungs -/

/-- A dominating split of the completed EM member on an isolating annulus at `ρ`:
annulus data, strip containment, isolation, hole-confined split centres, nonvanishing
cofactor, the factorization, and domination of ξ on the two slit charts. -/
def EMSplitData (ρ : ℂ) (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ) : Prop :=
  0 ≤ r₀ ∧ r₀ < R ∧
  (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
  (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
  (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) ∧
  AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
  (∀ z ∈ ball ρ R, completedEM N z = ((zs.map (fun w => z - w)).prod) * u z) ∧
  (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
    ‖xi z - completedEM N z‖ < ‖completedEM N z‖)

/-- **Dominating splits exist unconditionally at every strip point.** -/
theorem emSplitData_exists (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ), EMSplitData ρ r₀ R N zs u := by
  obtain ⟨r₀, R, N, hr₀, hrR, hN1, hstripb, hiso, hdom⟩ :=
    exists_isolating_em_domination ρ h0 h1
  have hFan : AnalyticOnNhd ℂ (completedEM N) (ball ρ R) := fun z hz =>
    completedEM_analyticOnNhd_strip hN1 z (hstripb z hz)
  obtain ⟨zs, u, hzs, huan, hune, hufact⟩ :=
    exists_split_of_domination hr₀.le hrR hFan hdom
  exact ⟨r₀, R, N, zs, u, hr₀.le, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩

/-- **The hole count of any dominating split is the central vanishing order.** -/
theorem emSplitData_count_eq {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : EMSplitData ρ r₀ R N zs u) :
    (analyticOrderAt xi ρ).toNat = zs.length := by
  obtain ⟨h0, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩ := h
  have hchartsub : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, z ∈ ball ρ R := by
    intro z hz
    rw [charts_union_eq_annulus ρ h0] at hz
    exact hz.1
  exact enclosed_count_eq_of_split_domination h0 hrR hiso huan hune hzs
    (fun z hz => hufact z (hchartsub z hz)) hdom

/-- **Every rung of the multiplicity ladder from finite-member divisibility.**  If at
every hypothetical off-line ξ-zero the hole count of every dominating completed EM
split is divisible by `2^k`, then every off-line vanishing order is divisible by `2^k`.
The certificate demand is non-vacuous: dominating splits exist unconditionally. -/
theorem rhLadder_of_em_split_multiplicity (k : ℕ)
    (hpar : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      EMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) :
    RHLadder k := by
  intro ρ hρ h0
  have hρre : 0 < ρ.re := lt_trans (by norm_num) (mem_rightHalf.mp hρ)
  obtain ⟨r₀, R, N, zs, u, hdata⟩ :=
    emSplitData_exists ρ hρre (xi_zero_re_lt_one hρre h0)
  have hdvd : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
    rw [emSplitData_count_eq hdata]
    exact hpar ρ hρ h0 r₀ R N zs u hdata
  have hm : (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt xi ρ :=
    ENat.coe_toNat (xi_orderAt_ne_top ρ)
  obtain ⟨c, hc⟩ := hdvd
  rw [← hm, hc]
  exact ⟨(c : ℕ∞), by push_cast; ring⟩

/-- **The base rung from finite-member parity alone.**  Both former analytic clauses of
the supply — accuracy and floor — are theorems on the isolating annulus; what remains is
the evenness of the hole count of the explicit finite member. -/
theorem rhLadder_one_of_em_split_parity
    (hpar : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      EMSplitData ρ r₀ R N zs u → Even zs.length) :
    RHLadder 1 := by
  refine rhLadder_of_em_split_multiplicity 1 ?_
  intro ρ hρ h0 r₀ R N zs u hdata
  rw [pow_one]
  exact (hpar ρ hρ h0 r₀ R N zs u hdata).two_dvd

/-- **The Riemann Hypothesis from all-orders divisibility of finite-member hole
counts**: the whole ladder transports to the explicit finite member. -/
theorem riemannHypothesis_of_em_split_multiplicity
    (hpar : ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      EMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) :
    RiemannHypothesis :=
  rh_iff_forall_ladder.mpr fun k => rhLadder_of_em_split_multiplicity k (hpar k)

end RHTower
