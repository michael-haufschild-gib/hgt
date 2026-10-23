import GaloisForLFunctions.HTGeometry.BoundedStripAlmostPeriodicThreeLines
import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums

/-!
# A one-sided bound on the critical line excludes finitely many poles to its right

Let `R` be the continuation of a Dirichlet series `Σ f(n) n^{−s}`, absolutely convergent at
`Re s = u₀`.  Suppose that on the closed half-plane `Re s ≥ ½`

`R(s) = H(s) + Σ_j r_j / (s − p_j)`

with `H` holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`, and of subexponential growth in
`|Im s|`, and with finitely many distinct poles `p_j`.

**Theorem** (`false_of_re_le_criticalLine_of_rightmostPole`).  If `Re R(½ + it) ≤ c` for all
`|t| ≥ T₀`, then no pole `p_{j₀}` with `Re p_{j₀} > ½` that is rightmost among the `p_j` can carry a
residue `r_{j₀}` with `Re r_{j₀} > 0`.

So a real part bounded above on the critical line forbids an isolated rightmost family of
positive-residue poles: off-line poles of such a Dirichlet series cannot be finitely many.

Proof.
* **Phragmén–Lindelöf** for `exp H` on the strip `½ < Re s < b`, `b = max u₀ β₀ + 1`: the line
  bound, compactness of `|t| ≤ T₁`, and absolute convergence on `Re s = b` give
  `Re R ≤ C_B` on `{Re s ≥ ½, |Im s| ≥ T₂}`, with `C_B` independent of everything below.
* **Harnack** (`norm_sub_le_of_re_nonneg_on_ball`) for `C_B − R` on discs centred on
  `Re s = b + 1`, plus compactness near the real axis: `R` is bounded on every half-plane
  `Re s > β₀ + η/2`.
* **Bohr** (`isStripAlmostPeriodicOn_of_bounded_LSeries`): `R` is almost periodic on
  `β₀ + η ≤ Re s ≤ b`, so the value `Re R(p_{j₀} + η) ≥ Re r_{j₀}/η − K` recurs at some height
  `≥ T₂`, where it is at most `C_B`.  Letting `η → 0` contradicts `Re r_{j₀} > 0`.
-/

open Complex Set Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The principal-part sum `Σ_j r_j / (z − p_j)`. -/
def complexPrincipalPartSum {m : ℕ} (p r : Fin m → ℂ) (z : ℂ) : ℂ := ∑ j, r j / (z - p j)

theorem norm_principalPartSum_le {m : ℕ} {p r : Fin m → ℂ} {z : ℂ} {d : ℝ} (hd : 0 < d)
    (hz : ∀ j, d ≤ ‖z - p j‖) : ‖complexPrincipalPartSum p r z‖ ≤ (∑ j, ‖r j‖) / d := by
  unfold complexPrincipalPartSum
  calc ‖∑ j, r j / (z - p j)‖ ≤ ∑ j, ‖r j / (z - p j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖r j‖ / d := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hz j)
    _ = (∑ j, ‖r j‖) / d := by rw [Finset.sum_div]

theorem differentiableAt_principalPartSum {m : ℕ} {p r : Fin m → ℂ} {z : ℂ}
    (hz : ∀ j, z ≠ p j) : DifferentiableAt ℂ (complexPrincipalPartSum p r) z := by
  have : complexPrincipalPartSum p r = fun w => ∑ j, r j / (w - p j) := rfl
  rw [this]
  exact DifferentiableAt.fun_sum fun j _ =>
    (differentiableAt_const _).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr (hz j))

theorem continuousAt_principalPartSum {m : ℕ} {p r : Fin m → ℂ} {z : ℂ}
    (hz : ∀ j, z ≠ p j) : ContinuousAt (complexPrincipalPartSum p r) z :=
  (differentiableAt_principalPartSum hz).continuousAt

/-- An absolutely convergent Dirichlet series is bounded on the half-plane right of its line of
absolute convergence. -/
theorem norm_LSeries_le_tsum_term {f : ℕ → ℂ} {u₀ : ℝ} (hsum : LSeriesSummable f (u₀ : ℂ))
    {z : ℂ} (hz : u₀ ≤ z.re) : ‖LSeries f z‖ ≤ ∑' n, ‖LSeries.term f (u₀ : ℂ) n‖ := by
  have hz' : (u₀ : ℂ).re ≤ z.re := by simpa using hz
  have hzs : LSeriesSummable f z := hsum.of_re_le_re hz'
  calc ‖LSeries f z‖ ≤ ∑' n, ‖LSeries.term f z n‖ := norm_tsum_le_tsum_norm hzs.norm
    _ ≤ ∑' n, ‖LSeries.term f (u₀ : ℂ) n‖ :=
        Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hz' n) hzs.norm
          hsum.norm

/-- **Phragmén–Lindelöf for the real part.**  A function holomorphic on `½ < Re z < b`,
continuous up to the boundary, with real part of subexponential growth, has real part bounded
on the closed strip by its bounds on the two boundary lines. -/
theorem re_le_max_of_strip {H : ℂ → ℂ} {b A₁ A₂ : ℝ} (hb : 1 / 2 < b)
    (hH : DifferentiableOn ℂ H {z : ℂ | 1 / 2 < z.re}) (hHc : ContinuousOn H {z : ℂ | 1 / 2 ≤ z.re})
    (hgrowth : ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re →
      (H z).re ≤ B * Real.exp (κ * |z.im|))
    (hleft : ∀ z : ℂ, z.re = 1 / 2 → (H z).re ≤ A₁) (hright : ∀ z : ℂ, z.re = b → (H z).re ≤ A₂)
    {z : ℂ} (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ b) : (H z).re ≤ max A₁ A₂ := by
  have key : ‖Complex.exp (H z)‖ ≤ Real.exp (max A₁ A₂) := by
    refine PhragmenLindelof.vertical_strip (f := fun w => Complex.exp (H w)) ?_ ?_ ?_ ?_ hz1 hz2
    · refine DiffContOnCl.mk ((hH.mono fun w hw => hw.1).cexp) ?_
      rw [closure_preimage_re, closure_Ioo hb.ne]
      exact (hHc.mono fun w hw => hw.1).cexp
    · have hκ : 0 < Real.pi / (2 * (b - 1 / 2)) := div_pos Real.pi_pos (by linarith)
      obtain ⟨B, hB⟩ := hgrowth _ hκ
      refine ⟨Real.pi / (2 * (b - 1 / 2)), ?_, B, ?_⟩
      · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by linarith) (by linarith)]
        linarith
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
        rw [Complex.norm_exp, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hB w hw.1.le)
    · intro w hw
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((hleft w hw).trans (le_max_left _ _))
    · intro w hw
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((hright w hw).trans (le_max_right _ _))
  rwa [Complex.norm_exp, Real.exp_le_exp] at key

/-- Distance from a point at height `|Im z| ≥ Σ_j |Im p_j| + 1` to every pole is at least `1`. -/
theorem one_le_norm_sub_of_im {m : ℕ} {p : Fin m → ℂ} {z : ℂ}
    (hz : (∑ j, |(p j).im|) + 1 ≤ |z.im|) (j : Fin m) : 1 ≤ ‖z - p j‖ := by
  have hj : |(p j).im| ≤ ∑ j, |(p j).im| :=
    Finset.single_le_sum (f := fun j => |(p j).im|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 : |z.im| - |(p j).im| ≤ |(z - p j).im| := by
    rw [sub_im]
    have := abs_sub_abs_le_abs_sub z.im (p j).im
    linarith
  linarith [Complex.abs_im_le_norm (z - p j)]

theorem ne_of_one_le_norm_sub {m : ℕ} {p : Fin m → ℂ} {z : ℂ}
    (hz : (∑ j, |(p j).im|) + 1 ≤ |z.im|) (j : Fin m) : z ≠ p j := fun h => by
  have := one_le_norm_sub_of_im hz j
  rw [h, sub_self, norm_zero] at this
  linarith

/-- **Step A–B.**  Phragmén–Lindelöf turns the one-sided bound on the critical line into a
one-sided bound `Re R ≤ C_B` on the whole half-plane `Re z ≥ ½` above the poles. -/
theorem exists_re_le_above_poles {f : ℕ → ℂ} {u₀ : ℝ} (hsum : LSeriesSummable f (u₀ : ℂ))
    {R H : ℂ → ℂ} {m : ℕ} {p r : Fin m → ℂ}
    (hH : DifferentiableOn ℂ H {z : ℂ | 1 / 2 < z.re}) (hHc : ContinuousOn H {z : ℂ | 1 / 2 ≤ z.re})
    (hgrowth : ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re →
      (H z).re ≤ B * Real.exp (κ * |z.im|))
    (hRH : ∀ z : ℂ, 1 / 2 ≤ z.re → (∀ j, z ≠ p j) → R z = H z + complexPrincipalPartSum p r z)
    (hRL : ∀ z : ℂ, u₀ < z.re → R z = LSeries f z)
    {c T₀ b : ℝ} (hline : ∀ t : ℝ, T₀ ≤ |t| → (R (1 / 2 + t * I)).re ≤ c)
    (hu₀b : u₀ < b) (hpb : ∀ j, (p j).re + 1 ≤ b) (hhalfb : 1 / 2 < b) :
    ∃ CB : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re → (∑ j, |(p j).im|) + 1 ≤ |z.im| → (R z).re ≤ CB := by
  have hρs0 : 0 ≤ ∑ j, ‖r j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS₀ : ∀ z : ℂ, u₀ < z.re → ‖R z‖ ≤ ∑' n, ‖LSeries.term f (u₀ : ℂ) n‖ := fun z hz => by
    rw [hRL z hz]; exact norm_LSeries_le_tsum_term hsum hz.le
  have hpp : ∀ z : ℂ, (∀ j, 1 ≤ ‖z - p j‖) → ‖complexPrincipalPartSum p r z‖ ≤ ∑ j, ‖r j‖ :=
    fun z hz => by simpa using norm_principalPartSum_le (r := r) one_pos hz
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ w ∈ (fun t : ℝ => (1 / 2 : ℂ) + t * I) ''
      Icc (-(max T₀ ((∑ j, |(p j).im|) + 1))) (max T₀ ((∑ j, |(p j).im|) + 1)), ‖H w‖ ≤ C₁ :=
    ((isCompact_Icc).image_of_continuousOn (by fun_prop)).exists_bound_of_continuousOn
      (hHc.mono fun w ⟨t, _, ht⟩ => by rw [← ht]; simp)
  have hleft : ∀ z : ℂ, z.re = 1 / 2 → (H z).re ≤ max (c + ∑ j, ‖r j‖) C₁ := by
    intro z hz
    have hzeq : z = (1 / 2 : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hz]
    rcases le_or_gt (max T₀ ((∑ j, |(p j).im|) + 1)) |z.im| with hbig | hsmall
    · have hT₂z : (∑ j, |(p j).im|) + 1 ≤ |z.im| := (le_max_right _ _).trans hbig
      have hR := hRH z hz.ge (ne_of_one_le_norm_sub hT₂z)
      have hc' : (R z).re ≤ c := by rw [hzeq]; exact hline z.im ((le_max_left _ _).trans hbig)
      have hHz : H z = R z - complexPrincipalPartSum p r z := by rw [hR]; ring
      have h1 := hpp z (one_le_norm_sub_of_im hT₂z)
      have h2 := Complex.abs_re_le_norm (complexPrincipalPartSum p r z)
      have h3 := neg_abs_le (complexPrincipalPartSum p r z).re
      rw [hHz, sub_re]
      exact (by linarith : (R z).re - (complexPrincipalPartSum p r z).re ≤ c + ∑ j, ‖r j‖).trans
        (le_max_left _ _)
    · have hmem : z ∈ (fun t : ℝ => (1 / 2 : ℂ) + t * I) ''
          Icc (-(max T₀ ((∑ j, |(p j).im|) + 1))) (max T₀ ((∑ j, |(p j).im|) + 1)) :=
        ⟨z.im, ⟨by linarith [neg_abs_le z.im], by linarith [le_abs_self z.im]⟩, hzeq.symm⟩
      exact (Complex.re_le_norm _).trans ((hC₁ z hmem).trans (le_max_right _ _))
  have hright : ∀ z : ℂ, z.re = b →
      (H z).re ≤ (∑' n, ‖LSeries.term f (u₀ : ℂ) n‖) + ∑ j, ‖r j‖ := by
    intro z hz
    have hdist : ∀ j, 1 ≤ ‖z - p j‖ := fun j => by
      have h1 := Complex.abs_re_le_norm (z - p j)
      rw [sub_re, hz] at h1
      have := hpb j
      linarith [le_abs_self (b - (p j).re)]
    have hne : ∀ j, z ≠ p j := fun j h => by
      have := hdist j; rw [h, sub_self, norm_zero] at this; linarith
    have hHz : H z = R z - complexPrincipalPartSum p r z := by
      rw [hRH z (by rw [hz]; linarith) hne]; ring
    calc (H z).re ≤ ‖H z‖ := Complex.re_le_norm _
      _ ≤ ‖R z‖ + ‖complexPrincipalPartSum p r z‖ := by rw [hHz]; exact norm_sub_le _ _
      _ ≤ _ := add_le_add (hS₀ z (by rw [hz]; exact hu₀b)) (hpp z hdist)
  refine ⟨max (max (max (c + ∑ j, ‖r j‖) C₁) ((∑' n, ‖LSeries.term f (u₀ : ℂ) n‖) + ∑ j, ‖r j‖) +
      ∑ j, ‖r j‖) (∑' n, ‖LSeries.term f (u₀ : ℂ) n‖), fun z h1 h2 => ?_⟩
  rcases le_or_gt z.re b with hzb | hzb
  · rw [hRH z h1 (ne_of_one_le_norm_sub h2), add_re]
    have hHle := re_le_max_of_strip hhalfb hH hHc hgrowth hleft hright h1 hzb
    have h3 := hpp z (one_le_norm_sub_of_im h2)
    have h4 := Complex.re_le_norm (complexPrincipalPartSum p r z)
    exact le_max_of_le_left (by linarith)
  · exact (Complex.re_le_norm _).trans ((hS₀ z (by linarith)).trans (le_max_right _ _))

/-- **Step C.**  A one-sided bound above the poles, Harnack's inequality on discs centred right
of the line of absolute convergence, and compactness near the real axis bound `R` on every
half-plane right of all poles. -/
theorem exists_norm_le_right_of_re_le {f : ℕ → ℂ} {u₀ : ℝ} (hsum : LSeriesSummable f (u₀ : ℂ))
    {R H : ℂ → ℂ} {m : ℕ} {p r : Fin m → ℂ}
    (hH : DifferentiableOn ℂ H {z : ℂ | 1 / 2 < z.re}) (hHc : ContinuousOn H {z : ℂ | 1 / 2 ≤ z.re})
    (hRH : ∀ z : ℂ, 1 / 2 ≤ z.re → (∀ j, z ≠ p j) → R z = H z + complexPrincipalPartSum p r z)
    (hRL : ∀ z : ℂ, u₀ < z.re → R z = LSeries f z) {CB : ℝ}
    (hReR : ∀ z : ℂ, 1 / 2 ≤ z.re → (∑ j, |(p j).im|) + 1 ≤ |z.im| → (R z).re ≤ CB)
    {x b : ℝ} (hx : 1 / 2 < x) (hpx : ∀ j, (p j).re < x) (hxb : x ≤ b) (hu₀b : u₀ < b) :
    ∃ M : ℝ, ∀ z : ℂ, x < z.re → ‖R z‖ ≤ M := by
  have hS₀ : ∀ z : ℂ, u₀ < z.re → ‖R z‖ ≤ ∑' n, ‖LSeries.term f (u₀ : ℂ) n‖ := fun z hz => by
    rw [hRL z hz]; exact norm_LSeries_le_tsum_term hsum hz.le
  have hneR : ∀ z : ℂ, x ≤ z.re → ∀ j, z ≠ p j := fun z hz j h => by
    have := hpx j; rw [← h] at this; linarith
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ = (x - 1 / 2) / 2 := ⟨_, by linarith, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = b + 1 / 2 - δ := ⟨_, rfl⟩
  have hρδ : δ < ρ := by rw [hρ, hδ]; linarith
  have hρ0 : 0 < ρ := hδ0.trans hρδ
  obtain ⟨T₃, hT₃⟩ : ∃ T₃ : ℝ, T₃ = (∑ j, |(p j).im|) + 1 + ρ := ⟨_, rfl⟩
  obtain ⟨M₃, hM₃⟩ : ∃ M₃, ∀ w ∈ (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) ''
      (Icc x b ×ˢ Icc (-T₃) T₃), ‖R w‖ ≤ M₃ := by
    refine ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (by fun_prop)).exists_bound_of_continuousOn ?_
    have hGc : ContinuousOn (fun z => H z + complexPrincipalPartSum p r z)
        ((fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) '' (Icc x b ×ˢ Icc (-T₃) T₃)) := by
      rintro w ⟨q, hq, rfl⟩
      have hwre : ((q.1 : ℂ) + q.2 * I).re = q.1 := by simp
      refine ContinuousWithinAt.add ?_ (continuousAt_principalPartSum
        (hneR _ (by rw [hwre]; exact hq.1.1))).continuousWithinAt
      refine (hHc _ (show 1 / 2 ≤ ((q.1 : ℂ) + q.2 * I).re by rw [hwre]; linarith [hq.1.1])).mono ?_
      rintro v ⟨q', hq', rfl⟩
      show 1 / 2 ≤ ((q'.1 : ℂ) + q'.2 * I).re
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
        add_zero]
      linarith [hq'.1.1]
    refine hGc.congr ?_
    rintro w ⟨q, hq, rfl⟩
    have hwre : ((q.1 : ℂ) + q.2 * I).re = q.1 := by simp
    exact hRH _ (by rw [hwre]; linarith [hq.1.1]) (hneR _ (by rw [hwre]; exact hq.1.1))
  set S₀ : ℝ := ∑' n, ‖LSeries.term f (u₀ : ℂ) n‖
  have hS₀nn : 0 ≤ S₀ := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨max S₀ (max (2 * |CB| + S₀ + 2 * ρ / δ * (|CB| + S₀)) M₃), fun z hz => ?_⟩
  rcases le_or_gt b z.re with hzb | hzb
  · exact (hS₀ z (by linarith)).trans (le_max_left _ _)
  rcases le_or_gt T₃ |z.im| with hbig | hsmall
  · -- Harnack on the disc of radius `ρ` centred at `b + 1 + i Im z`
    obtain ⟨cc, hcc⟩ : ∃ cc : ℂ, cc = ((b + 1 : ℝ) : ℂ) + (z.im : ℂ) * I := ⟨_, rfl⟩
    have hccre : cc.re = b + 1 := by simp [hcc]
    have hccim : cc.im = z.im := by simp [hcc]
    have hball : ∀ w ∈ ball cc ρ, 1 / 2 < w.re ∧ (∑ j, |(p j).im|) + 1 ≤ |w.im| := by
      intro w hw
      have hwc : ‖w - cc‖ < ρ := mem_ball_iff_norm.mp hw
      have hre := Complex.abs_re_le_norm (w - cc)
      have him := Complex.abs_im_le_norm (w - cc)
      rw [sub_re, hccre] at hre
      rw [sub_im, hccim] at him
      constructor
      · have := neg_abs_le (w.re - (b + 1)); rw [hρ, hδ] at hwc; linarith
      · have := abs_sub_abs_le_abs_sub z.im w.im
        rw [abs_sub_comm] at him
        linarith
    have hRd : DifferentiableOn ℂ R (ball cc ρ) := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hball w hw
      have hGd : DifferentiableAt ℂ (fun z => H z + complexPrincipalPartSum p r z) w :=
        (hH.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hw1)).add
          (differentiableAt_principalPartSum (ne_of_one_le_norm_sub hw2))
      have hev : (fun z => H z + complexPrincipalPartSum p r z) =ᶠ[𝓝 w] R := by
        filter_upwards [isOpen_ball.mem_nhds hw] with v hv
        obtain ⟨hv1, hv2⟩ := hball v hv
        exact (hRH v hv1.le (ne_of_one_le_norm_sub hv2)).symm
      exact (hGd.congr_of_eventuallyEq hev.symm).differentiableWithinAt
    have hgd : DifferentiableOn ℂ (fun w => (CB : ℂ) - R w) (ball cc ρ) :=
      (differentiableOn_const _).sub hRd
    have hgre : ∀ w ∈ ball cc ρ, 0 ≤ ((CB : ℂ) - R w).re := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hball w hw
      simp only [sub_re, ofReal_re]
      linarith [hReR w hw1.le hw2]
    have hzc : ‖z - cc‖ = b + 1 - z.re := by
      have : z - cc = ((z.re - (b + 1) : ℝ) : ℂ) := by apply Complex.ext <;> simp [hcc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hzball : z ∈ ball cc ρ := by rw [mem_ball_iff_norm, hzc, hρ, hδ]; linarith
    have hH' := norm_sub_le_of_re_nonneg_on_ball hgd hgre hzball
    have hRcc : ‖R cc‖ ≤ S₀ := hS₀ cc (by rw [hccre]; linarith)
    have hgc : ((CB : ℂ) - R cc).re ≤ |CB| + S₀ := by
      simp only [sub_re, ofReal_re]
      have := neg_abs_le (R cc).re
      have := Complex.abs_re_le_norm (R cc)
      linarith [le_abs_self CB]
    have hgc0 : 0 ≤ ((CB : ℂ) - R cc).re := hgre cc (mem_ball_self hρ0)
    have hfac : 2 * ‖z - cc‖ / (ρ - ‖z - cc‖) ≤ 2 * ρ / δ := by
      rw [hzc]
      have h2 : δ ≤ ρ - (b + 1 - z.re) := by rw [hρ, hδ]; linarith
      have h3 : 0 ≤ b + 1 - z.re := by linarith
      have h4 : b + 1 - z.re ≤ ρ := by linarith
      calc 2 * (b + 1 - z.re) / (ρ - (b + 1 - z.re)) ≤ 2 * ρ / (ρ - (b + 1 - z.re)) := by
            gcongr
        _ ≤ 2 * ρ / δ := by gcongr
    have hgz : ‖((CB : ℂ) - R z) - ((CB : ℂ) - R cc)‖ ≤ 2 * ρ / δ * (|CB| + S₀) :=
      hH'.trans (mul_le_mul hfac hgc hgc0 (div_nonneg (by linarith) hδ0.le))
    calc ‖R z‖ = ‖R cc - (((CB : ℂ) - R z) - ((CB : ℂ) - R cc))‖ := by congr 1; ring
      _ ≤ ‖R cc‖ + ‖((CB : ℂ) - R z) - ((CB : ℂ) - R cc)‖ := norm_sub_le _ _
      _ ≤ S₀ + 2 * ρ / δ * (|CB| + S₀) := add_le_add hRcc hgz
      _ ≤ 2 * |CB| + S₀ + 2 * ρ / δ * (|CB| + S₀) := by linarith [abs_nonneg CB]
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · have hmem : z ∈ (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I) '' (Icc x b ×ˢ Icc (-T₃) T₃) :=
      ⟨(z.re, z.im), ⟨⟨hz.le, hzb.le⟩, ⟨by linarith [neg_abs_le z.im], by linarith [le_abs_self z.im]⟩⟩,
        by apply Complex.ext <;> simp⟩
    exact (hM₃ z hmem).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **A one-sided bound on the critical line excludes a rightmost positive-residue pole.** -/
theorem false_of_re_le_criticalLine_of_rightmostPole {f : ℕ → ℂ} {u₀ : ℝ}
    (hsum : LSeriesSummable f (u₀ : ℂ)) {R H : ℂ → ℂ} {m : ℕ} {p r : Fin m → ℂ}
    (hp : Function.Injective p)
    (hH : DifferentiableOn ℂ H {z : ℂ | 1 / 2 < z.re}) (hHc : ContinuousOn H {z : ℂ | 1 / 2 ≤ z.re})
    (hgrowth : ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re →
      (H z).re ≤ B * Real.exp (κ * |z.im|))
    (hRH : ∀ z : ℂ, 1 / 2 ≤ z.re → (∀ j, z ≠ p j) → R z = H z + complexPrincipalPartSum p r z)
    (hRL : ∀ z : ℂ, u₀ < z.re → R z = LSeries f z)
    {c T₀ : ℝ} (hline : ∀ t : ℝ, T₀ ≤ |t| → (R (1 / 2 + t * I)).re ≤ c)
    (j₀ : Fin m) (hj₀ : 1 / 2 < (p j₀).re) (hmax : ∀ j, (p j).re ≤ (p j₀).re)
    (hres : 0 < (r j₀).re) : False := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = max u₀ (p j₀).re + 1 := ⟨_, rfl⟩
  have hu₀b : u₀ < b := by rw [hb]; linarith [le_max_left u₀ (p j₀).re]
  have hβb : (p j₀).re + 1 ≤ b := by rw [hb]; linarith [le_max_right u₀ (p j₀).re]
  obtain ⟨CB, hReR⟩ := exists_re_le_above_poles hsum hH hHc hgrowth hRH hRL hline hu₀b
    (fun j => by linarith [hmax j]) (by linarith)
  have hne_of_re : ∀ z : ℂ, (p j₀).re < z.re → ∀ j, z ≠ p j := fun z hz j h => by
    have := hmax j; rw [← h] at this; linarith
  have hRdiff : ∀ x : ℝ, (p j₀).re ≤ x → DifferentiableOn ℂ R {z : ℂ | x < z.re} := by
    intro x hx
    have hG : DifferentiableOn ℂ (fun z => H z + complexPrincipalPartSum p r z) {z : ℂ | x < z.re} :=
      (hH.mono fun z (hz : x < z.re) => show 1 / 2 < z.re by linarith).add fun z hz =>
        (differentiableAt_principalPartSum (hne_of_re z (by
          have : x < z.re := hz; linarith))).differentiableWithinAt
    exact hG.congr fun z hz => hRH z (by have : x < z.re := hz; linarith)
      (hne_of_re z (by have : x < z.re := hz; linarith))
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, ∀ w ∈ (fun η : ℝ => p j₀ + η) '' Icc 0 1, ‖H w‖ ≤ K₀ :=
    ((isCompact_Icc).image_of_continuousOn (by fun_prop)).exists_bound_of_continuousOn
      (hHc.mono fun w ⟨η, hη, hw⟩ => by
        rw [← hw]; show 1 / 2 ≤ (p j₀ + η).re; simp; linarith [hη.1])
  have hK₀0 : 0 ≤ K₀ :=
    (norm_nonneg _).trans (hK₀ (p j₀ + ((0 : ℝ) : ℂ)) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ j ∈ Finset.univ.erase j₀, ‖r j‖ / ‖p j₀ - p j‖ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact Finset.sum_nonneg fun _ _ => by positivity
  -- the key inequality for every small `η`
  have key : ∀ η : ℝ, 0 < η → η ≤ 1 → (r j₀).re / η ≤ CB + 1 + K₀ + D := by
    intro η hη hη1
    have hz₀re : (p j₀ + (η : ℂ)).re = (p j₀).re + η := by simp
    have hz₀im : (p j₀ + (η : ℂ)).im = (p j₀).im := by simp
    have hne₀ : ∀ j, p j₀ + (η : ℂ) ≠ p j := hne_of_re _ (by rw [hz₀re]; linarith)
    have hlow : (r j₀).re / η - K₀ - D ≤ (R (p j₀ + (η : ℂ))).re := by
      rw [hRH _ (by rw [hz₀re]; linarith) hne₀, add_re]
      have hH0 : ‖H (p j₀ + (η : ℂ))‖ ≤ K₀ := hK₀ _ ⟨η, ⟨hη.le, hη1⟩, rfl⟩
      have hsplit : complexPrincipalPartSum p r (p j₀ + (η : ℂ)) =
          r j₀ / (η : ℂ) + ∑ j ∈ Finset.univ.erase j₀, r j / (p j₀ + (η : ℂ) - p j) := by
        unfold complexPrincipalPartSum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
        congr 1
        ring_nf
      have hrest : ‖∑ j ∈ Finset.univ.erase j₀, r j / (p j₀ + (η : ℂ) - p j)‖ ≤ D := by
        rw [hD]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hjne : j ≠ j₀ := Finset.ne_of_mem_erase hj
        have hpos : 0 < ‖p j₀ - p j‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hjne (hp h).symm)
        rw [norm_div]
        refine div_le_div_of_nonneg_left (norm_nonneg _) hpos ?_
        have hsq : normSq (p j₀ - p j) ≤ normSq (p j₀ + (η : ℂ) - p j) := by
          rw [normSq_apply, normSq_apply]
          have hmj := hmax j
          simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, add_zero]
          nlinarith
        rw [Complex.norm_def, Complex.norm_def]
        exact Real.sqrt_le_sqrt hsq
      rw [hsplit, add_re, Complex.div_ofReal_re]
      have h1 := neg_abs_le (H (p j₀ + (η : ℂ))).re
      have h2 := Complex.abs_re_le_norm (H (p j₀ + (η : ℂ)))
      have h3 := neg_abs_le (∑ j ∈ Finset.univ.erase j₀, r j / (p j₀ + (η : ℂ) - p j)).re
      have h4 := Complex.abs_re_le_norm
        (∑ j ∈ Finset.univ.erase j₀, r j / (p j₀ + (η : ℂ) - p j))
      linarith
    -- boundedness right of `β₀ + η / 2`, then Bohr's almost periodicity
    have hxβ : (p j₀).re < (p j₀).re + η / 2 := by linarith
    obtain ⟨M, hM⟩ := exists_norm_le_right_of_re_le hsum hH hHc hRH hRL hReR
      (x := (p j₀).re + η / 2) (b := b) (by linarith) (fun j => by linarith [hmax j])
      (by linarith) hu₀b
    have hap := GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries
      (x := (p j₀).re + η / 2) (u₀ := u₀) (u := b) (l' := (p j₀).re + η) (M := M)
      (by linarith) (by linarith) hu₀b hsum (hRdiff _ hxβ.le) hM hRL
    obtain ⟨L, -, hτ⟩ := hap 1 one_pos
    obtain ⟨τ, hτmem, hτz⟩ := hτ ((∑ j, |(p j).im|) + 1 + |(p j₀).im|)
    have hz₀strip : |(p j₀ + (η : ℂ)).re - ((p j₀).re + η + b) / 2| ≤ (b - ((p j₀).re + η)) / 2 := by
      rw [hz₀re, abs_le]; constructor <;> linarith
    have hclose := hτz _ hz₀strip
    have hhigh : (R (p j₀ + (η : ℂ) + (τ : ℂ) * I)).re ≤ CB := by
      have hre : (p j₀ + (η : ℂ) + (τ : ℂ) * I).re = (p j₀).re + η := by simp
      have him : (p j₀ + (η : ℂ) + (τ : ℂ) * I).im = (p j₀).im + τ := by simp
      refine hReR _ (by rw [hre]; linarith) ?_
      rw [him]
      have hτ1 := hτmem.1
      have := neg_abs_le (p j₀).im
      have hs0 : 0 ≤ ∑ j, |(p j).im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hdiff : (R (p j₀ + (η : ℂ))).re - (R (p j₀ + (η : ℂ) + (τ : ℂ) * I)).re ≤ 1 := by
      have := Complex.abs_re_le_norm (R (p j₀ + (η : ℂ) + (τ : ℂ) * I) - R (p j₀ + (η : ℂ)))
      rw [sub_re] at this
      have := neg_abs_le ((R (p j₀ + (η : ℂ) + (τ : ℂ) * I)).re - (R (p j₀ + (η : ℂ))).re)
      linarith
    linarith
  -- conclusion: `η → 0`
  have hE0 : 0 < |CB| + 1 + K₀ + D := by positivity
  have hη0 : 0 < min 1 ((r j₀).re / (2 * (|CB| + 1 + K₀ + D))) :=
    lt_min one_pos (div_pos hres (by positivity))
  have hk := key _ hη0 (min_le_left _ _)
  have hle : 2 * (|CB| + 1 + K₀ + D) ≤
      (r j₀).re / min 1 ((r j₀).re / (2 * (|CB| + 1 + K₀ + D))) := by
    rw [le_div_iff₀ hη0]
    calc 2 * (|CB| + 1 + K₀ + D) * min 1 ((r j₀).re / (2 * (|CB| + 1 + K₀ + D)))
        ≤ 2 * (|CB| + 1 + K₀ + D) * ((r j₀).re / (2 * (|CB| + 1 + K₀ + D))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (r j₀).re := by field_simp
  linarith [le_abs_self CB]

end GaloisForLFunctions.HTGeometry
