/-
The anchored finite member and truncation steering.

Multiplying the completed symmetrized EM member by the finite Euler head anchor changes
no zero in the strip — the anchor is a unit there — so every dominating split transports
to the anchored member with the same centres, and the parity certificate (the mod-2 deck
cocycle of a square root) can be read on the anchored object.  On the anchored member
the mirror structure is twisted by exactly the anchor's defect: the line-reflection
mismatch factorizes through the anchor alone, and the mirror product identity rotates
the conjugated member value by precisely the mirror defect angle.

Separately, the truncation length is a steering parameter: the member's hole-zero count
is rigid — always the central vanishing order, for both finite members, at every valid
annulus and truncation length — while the zeros themselves localize: for any ε > 0 all
hole zeros lie within ε of the centre once the truncation is long enough, because the
member converges to ξ uniformly on compact strip subsets and ξ holds a floor off the
centre.
-/
import GaloisForLFunctions.RHTower.SymmetrizedEMCarrier
import GaloisForLFunctions.RHTower.AnchorTilt

noncomputable section

namespace RHTower

open Complex Metric Filter

/-! ### §1 The anchor is analytic, and a unit on the strip -/

/-- Finite products of analytic functions are analytic. -/
theorem analyticAt_finset_prod {ι : Type*} (P : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ p ∈ P, AnalyticAt ℂ (f p) z) :
    AnalyticAt ℂ (fun s => ∏ p ∈ P, f p s) z := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using analyticAt_const
  | insert a s ha ih =>
      rw [show (fun w => ∏ p ∈ insert a s, f p w)
          = fun w => f a w * ∏ p ∈ s, f p w from by
        funext w; rw [Finset.prod_insert ha]]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- The finite Euler head anchor is entire. -/
theorem eulerHeadAnchor_analyticAt {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) (z : ℂ) :
    AnalyticAt ℂ (eulerHeadAnchor P) z := by
  have hfac : ∀ p ∈ P, AnalyticAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) z := by
    intro p hp
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hP p hp; omega)
    have hd : Differentiable ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) := fun w =>
      (differentiableAt_const (1 : ℂ)).sub
        (differentiableAt_id.neg.const_cpow (Or.inl hp0))
    exact (hd.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  exact analyticAt_finset_prod P _ z hfac

/-! ### §2 The anchored member and its defect-twisted mirror structure -/

/-- The anchored symmetric member: the finite Euler head times the completed
symmetrized EM member. -/
def anchoredSEM (P : Finset ℕ) (N : ℕ) : ℂ → ℂ := fun s =>
  eulerHeadAnchor P s * completedSEM N s

/-- **The anchored member's whole mirror mismatch is the anchor's**: the symmetric
member cancels from the line-reflection comparison, leaving the anchor's
non-equivariance as the only asymmetry. -/
theorem anchoredSEM_lineReflection_mismatch {P : Finset ℕ} {N : ℕ} {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    anchoredSEM P N (1 - (starRingEnd ℂ) s) * (starRingEnd ℂ) (eulerHeadAnchor P s)
      = eulerHeadAnchor P (1 - (starRingEnd ℂ) s)
        * (starRingEnd ℂ) (anchoredSEM P N s) := by
  unfold anchoredSEM
  rw [completedSEM_lineReflection h0 h1, map_mul]
  ring

/-- **The mirror polar law on the anchored member**: the anchored member's value at the
reflected point, times the anchor value at the point, is the conjugated symmetric-member
value rotated by exactly the anchor's mirror defect and scaled by the two anchor
moduli.  The defect angle is the entire phase asymmetry of the finite member across the
critical line. -/
theorem anchoredSEM_mirror_polar {P : Finset ℕ} {N : ℕ} {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    anchoredSEM P N (1 - (starRingEnd ℂ) s) * eulerHeadAnchor P s
      = ((‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ * ‖eulerHeadAnchor P s‖ : ℝ) : ℂ)
        * Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I)
        * (starRingEnd ℂ) (completedSEM N s) := by
  unfold anchoredSEM
  rw [completedSEM_lineReflection h0 h1,
    show eulerHeadAnchor P (1 - (starRingEnd ℂ) s) * (starRingEnd ℂ) (completedSEM N s)
        * eulerHeadAnchor P s
      = eulerHeadAnchor P (1 - (starRingEnd ℂ) s) * eulerHeadAnchor P s
        * (starRingEnd ℂ) (completedSEM N s) from by ring,
    eulerHeadAnchor_mul_mirror]

/-- **Split transport to the anchored member.**  The anchor is analytic and nonvanishing
on the strip ball, so any dominating split of the symmetric member yields a split of the
anchored member with the SAME hole centres: the anchoring changes no count and no
parity, only the boundary phase data. -/
theorem anchoredSEM_splitData {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (ball ρ R) ∧ (∀ z ∈ ball ρ R, v z ≠ 0) ∧
      ∀ z ∈ ball ρ R, anchoredSEM P N z = ((zs.map (fun w => z - w)).prod) * v z := by
  obtain ⟨h0, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩ := h
  refine ⟨fun z => eulerHeadAnchor P z * u z,
    fun z hz => (eulerHeadAnchor_analyticAt hP z).mul (huan z hz), ?_, ?_⟩
  · intro z hz
    exact mul_ne_zero (eulerHeadAnchor_ne_zero hP (hstripb z hz).1) (hune z hz)
  · intro z hz
    unfold anchoredSEM
    rw [hufact z hz]
    ring

/-- **The parity certificate reads on the anchored member**: square roots of the
anchored member on the two slit charts have trivial deck class exactly when the
symmetric member's hole count is even. -/
theorem anchoredSEM_deckClass_one_iff_even {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = anchoredSEM P N z)
    (hpG₂ : ∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = anchoredSEM P N z) :
    deckClass G₁ G₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 ↔ Even zs.length := by
  obtain ⟨v, hvan, hvne, hvfact⟩ := anchoredSEM_splitData hP h
  obtain ⟨h0, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩ := h
  exact split_deckClass_one_iff_even h0 hrR hzs hvan hvne hvfact hG₁ hG₂ hpG₁ hpG₂

/-! ### §3 Uniform decay on compact strip subsets -/

/-- Uniform decay of the symmetrized EM error on ANY nonempty compact subset of the
strip: constants from compactness bound the error by `C·N^(−σ)`. -/
theorem sem_uniform_decay_on_compact {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hstrip : ∀ z ∈ K, 0 < z.re ∧ z.re < 1) :
    ∃ (C σ : ℝ), 0 < σ ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ z ∈ K,
      ‖2 * riemannZeta z - semCarrier N z‖ ≤ C * (N : ℝ) ^ (-σ) := by
  obtain ⟨w0, hw0K, hw0min⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨w1, hw1K, hw1max⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨w3, hw3K, hw3max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hχcont : ContinuousOn zetaChi K := by
    intro z hz
    have h1z : 0 < (1 - z).re := by
      have := (hstrip z hz).2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact (zetaChi_analyticAt
      (Gammaℝ_ne_zero_of_re_pos h1z)).continuousAt.continuousWithinAt
  obtain ⟨w2, hw2K, hw2max⟩ := hK.exists_isMaxOn hne hχcont.norm
  have hσ₀pos : 0 < w0.re := (hstrip w0 hw0K).1
  have hσ₁pos : 0 < 1 - w1.re := by
    have := (hstrip w1 hw1K).2
    linarith
  have hA0 : (0 : ℝ) ≤ ‖w3‖ := norm_nonneg _
  refine ⟨‖w3‖ / w0.re + ‖zetaChi w2‖ * ((1 + ‖w3‖) / (1 - w1.re)),
    min w0.re (1 - w1.re), lt_min hσ₀pos hσ₁pos,
    add_nonneg (div_nonneg hA0 hσ₀pos.le)
      (mul_nonneg (norm_nonneg _) (div_nonneg (by linarith) hσ₁pos.le)), ?_⟩
  intro N hN1 z hz
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hzs := hstrip z hz
  have hnormz : ‖z‖ ≤ ‖w3‖ := hw3max hz
  have hrez : w0.re ≤ z.re := hw0min hz
  have hrez1 : 1 - w1.re ≤ (1 - z).re := by
    have hzle : z.re ≤ w1.re := hw1max hz
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hχz : ‖zetaChi z‖ ≤ ‖zetaChi w2‖ := hw2max hz
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hb1 : (N : ℝ) ^ (-z.re) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_le_rpow_of_exponent_le hN1'
      (by have := min_le_left w0.re (1 - w1.re); linarith)
  have hb2 : (N : ℝ) ^ (-(1 - z).re) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_le_rpow_of_exponent_le hN1'
      (by have := min_le_right w0.re (1 - w1.re); linarith)
  refine le_trans (two_zeta_sub_semCarrier_norm_le hN1 hzs.1 hzs.2) ?_
  have hp1 : ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
      ≤ ‖w3‖ * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / w0.re :=
    div_le_div₀ (mul_nonneg hA0 hx0)
      (mul_le_mul hnormz hb1 (Real.rpow_nonneg (Nat.cast_nonneg N) _) hA0)
      hσ₀pos hrez
  have hn1z : ‖(1 : ℂ) - z‖ ≤ 1 + ‖w3‖ := by
    calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one]
      _ ≤ 1 + ‖w3‖ := by linarith
  have hp2i : ‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re
      ≤ (1 + ‖w3‖) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re) :=
    div_le_div₀ (mul_nonneg (by linarith) hx0)
      (mul_le_mul hn1z hb2 (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by linarith))
      hσ₁pos hrez1
  have hp2 : ‖zetaChi z‖ * (‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re)
      ≤ ‖zetaChi w2‖
        * ((1 + ‖w3‖) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re)) :=
    mul_le_mul hχz hp2i
      (div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        (lt_of_lt_of_le hσ₁pos hrez1).le)
      (norm_nonneg _)
  calc ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
        + ‖zetaChi z‖ * (‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re)
      ≤ ‖w3‖ * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / w0.re
        + ‖zetaChi w2‖
          * ((1 + ‖w3‖) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re)) :=
        add_le_add hp1 hp2
    _ = (‖w3‖ / w0.re + ‖zetaChi w2‖ * ((1 + ‖w3‖) / (1 - w1.re)))
        * (N : ℝ) ^ (-min w0.re (1 - w1.re)) := by ring

/-- **The symmetric member converges to ξ uniformly on compact strip subsets**: the
archimedean factor is bounded there, so the completed error inherits the `C·N^(−σ)`
decay. -/
theorem xi_sub_completedSEM_uniform_decay_on_compact {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) (hstrip : ∀ z ∈ K, 0 < z.re ∧ z.re < 1) :
    ∃ (C σ : ℝ), 0 < σ ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ z ∈ K,
      ‖xi z - completedSEM N z‖ ≤ C * (N : ℝ) ^ (-σ) := by
  obtain ⟨C, σ, hσ, hC, hbound⟩ := sem_uniform_decay_on_compact hK hne hstrip
  have harchcont : ContinuousOn archFactor K := fun z hz =>
    (archFactor_analyticOnNhd_re_pos z (hstrip z hz).1).continuousAt.continuousWithinAt
  obtain ⟨w, hwK, hwmax⟩ := hK.exists_isMaxOn hne harchcont.norm
  refine ⟨‖archFactor w‖ / 2 * C, σ, hσ,
    mul_nonneg (by positivity) hC, ?_⟩
  intro N hN z hz
  have hzs := hstrip z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzs
    simp at hzs
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hzs
    simp at hzs
  have hid : xi z - completedSEM N z
      = archFactor z / 2 * (2 * riemannZeta z - semCarrier N z) := by
    rw [xi_eq_archFactor_mul_zeta hz0 hz1 (Gammaℝ_ne_zero_of_re_pos hzs.1)]
    unfold completedSEM
    ring
  have hnorm2 : ‖archFactor z / 2‖ = ‖archFactor z‖ / 2 := by
    rw [norm_div]
    norm_num
  have harchz : ‖archFactor z‖ ≤ ‖archFactor w‖ := hwmax hz
  calc ‖xi z - completedSEM N z‖
      = ‖archFactor z / 2‖ * ‖2 * riemannZeta z - semCarrier N z‖ := by
        rw [hid, norm_mul]
    _ ≤ ‖archFactor w‖ / 2 * (C * (N : ℝ) ^ (-σ)) := by
        rw [hnorm2]
        exact mul_le_mul (by linarith) (hbound N hN z hz) (norm_nonneg _)
          (by positivity)
    _ = ‖archFactor w‖ / 2 * C * (N : ℝ) ^ (-σ) := by ring

/-! ### §4 Truncation steering: rigid count, localizing support -/

/-- **Count rigidity across members, annuli, and truncation lengths**: any dominating
split of the completed EM member and any dominating split of the completed symmetrized
member at the same centre carry the same hole count. -/
theorem splitData_count_rigid {ρ : ℂ} {r₀ R r₀' R' : ℝ} {N N' : ℕ}
    {zs zs' : List ℂ} {u u' : ℂ → ℂ}
    (h : EMSplitData ρ r₀ R N zs u) (h' : SEMSplitData ρ r₀' R' N' zs' u') :
    zs.length = zs'.length := by
  rw [← emSplitData_count_eq h]
  exact semSplitData_count_eq h'

/-- **Hole zeros localize under truncation steering.**  On an isolating strip ball, for
any ε > 0 every zero of the symmetric member in the ball lies within ε of the centre
once the truncation length is large enough: the member converges to ξ uniformly while ξ
holds a floor on the compact set off the centre.  The count stays pinned to the central
order; the support collapses onto the centre. -/
theorem sem_hole_zeros_localize {ρ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hstrip : ∀ z ∈ closedBall ρ r₀, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ r₀, z ≠ ρ → xi z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε ≤ r₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w ∈ closedBall ρ r₀,
      completedSEM N w = 0 → w ∈ ball ρ ε := by
  set K := closedBall ρ r₀ \ ball ρ ε with hKdef
  have hKsub : K ⊆ closedBall ρ r₀ := fun z hz => hz.1
  have hKcompact : IsCompact K := (isCompact_closedBall ρ r₀).diff isOpen_ball
  have hne : K.Nonempty := by
    refine ⟨ρ + (((ε + r₀) / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, show ρ + (((ε + r₀) / 2 : ℝ) : ℂ) * I - ρ
        = (((ε + r₀) / 2 : ℝ) : ℂ) * I from by ring, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    · intro hmem
      rw [mem_ball, dist_eq_norm, show ρ + (((ε + r₀) / 2 : ℝ) : ℂ) * I - ρ
        = (((ε + r₀) / 2 : ℝ) : ℂ) * I from by ring, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hmem
      linarith
  have hxicont : ContinuousOn xi K := fun z _ =>
    ((xi_analyticOnNhd Set.univ) z (Set.mem_univ z)).continuousAt.continuousWithinAt
  have hxine : ∀ z ∈ K, xi z ≠ 0 := by
    intro z hz
    apply hiso z (hKsub hz)
    intro hzρ
    exact hz.2 (hzρ ▸ mem_ball_self hε)
  obtain ⟨x, hxK, hmin⟩ := hKcompact.exists_isMinOn hne hxicont.norm
  have hδ : 0 < ‖xi x‖ := norm_pos_iff.mpr (hxine x hxK)
  obtain ⟨C, σ, hσ, hC, hbound⟩ := xi_sub_completedSEM_uniform_decay_on_compact
    hKcompact hne (fun z hz => hstrip z (hKsub hz))
  have htend : Tendsto (fun n : ℕ => C * ((n : ℝ)) ^ (-σ)) atTop (nhds 0) := by
    have h0' := ((tendsto_rpow_neg_atTop hσ).comp
      tendsto_natCast_atTop_atTop).const_mul C
    simpa using h0'
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((htend.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 1))
  refine ⟨N₀, ?_⟩
  intro N hN w hw hw0
  by_contra hwout
  have hwK : w ∈ K := ⟨hw, hwout⟩
  obtain ⟨hNlt, hN1⟩ := hN₀ N hN
  have herr : ‖xi w - completedSEM N w‖ ≤ C * (N : ℝ) ^ (-σ) := hbound N hN1 w hwK
  rw [hw0, sub_zero] at herr
  have hfl : ‖xi x‖ ≤ ‖xi w‖ := hmin hwK
  linarith

end RHTower
