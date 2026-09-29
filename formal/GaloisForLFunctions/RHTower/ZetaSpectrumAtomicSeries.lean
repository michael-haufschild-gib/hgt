import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay

/-!
# Atomic Herglotz series on the zeta spectrum

For real weights `c_j` and ordinates `t_j ≥ 1` of zeros `ζ(½ + it_j) = 0` with
`Σ |c_j| / t_j² < ∞`, the odd atomic series
`Φ̃(s) = (2(s − ½)/π) Σ_j c_j / ((s − ½)² + t_j²)` is the Herglotz function whose boundary
measure on the critical line is `Σ_j c_j (δ_{t_j} + δ_{−t_j})`.

* `atomicZetaPart c t` is `Λ · Φ̃` with every pole cancelled.  Each term uses the double divided
  difference `atomQuot t = dslope (dslope Λ (½ + it)) (½ − it)`, which equals
  `Λ(s)/((s − ½)² + t²)` off the two atoms.
* It is holomorphic on `ℂ ∖ {0, 1}` (`differentiableOn_atomicZetaPart`) and odd under
  `s ↦ 1 − s` (`atomicZetaPart_one_sub`).
* It decays like `(1 + (Im s)²)⁻¹` on `½ ≤ Re s ≤ 3/2` (`exists_decay_atomicZetaPart`).  Near an
  atom the maximum principle on a unit disc bounds the quotient by the size of `Λ` on the circle.
  Far from every atom `|(s − ½)² + t²| ≳ t |Im s − t|`, and `Λ` decays exponentially.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- The odd atomic Herglotz series `Φ̃(s) = (2(s−½)/π) Σ_j c_j/((s−½)² + t_j²)`, whose boundary
measure on the critical line is `Σ_j c_j (δ_{t_j} + δ_{−t_j})`. -/
noncomputable def atomicPairSeries (c t : ℕ → ℝ) (s : ℂ) : ℂ :=
  2 * (s - 1 / 2) / (Real.pi : ℂ) * ∑' j, (c j : ℂ) / ((s - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)

/-- The point `½ + it`. -/
noncomputable def atomPoint (t : ℝ) : ℂ := 1 / 2 + t * I

/-- The mirror point `½ − it = 1 − (½ + it)`. -/
noncomputable def atomMirror (t : ℝ) : ℂ := 1 / 2 - t * I

theorem atomMirror_eq_one_sub (t : ℝ) : atomMirror t = 1 - atomPoint t := by
  simp only [atomMirror, atomPoint]; ring

theorem atomPoint_ne_atomMirror {t : ℝ} (ht : t ≠ 0) : atomPoint t ≠ atomMirror t := by
  intro h
  have := congrArg Complex.im h
  simp [atomPoint, atomMirror] at this
  exact ht (by linarith)

theorem atomPoint_re (t : ℝ) : (atomPoint t).re = 1 / 2 := by simp [atomPoint]
theorem atomMirror_re (t : ℝ) : (atomMirror t).re = 1 / 2 := by simp [atomMirror]

theorem ne_zero_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) : z ≠ 0 := by
  intro h; rw [h] at hz; norm_num at hz

theorem ne_one_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) : z ≠ 1 := by
  intro h; rw [h] at hz; norm_num at hz

/-- `(s − (½ + it))(s − (½ − it)) = (s − ½)² + t²`. -/
theorem sub_atomPoint_mul_sub_atomMirror (s : ℂ) (t : ℝ) :
    (s - atomPoint t) * (s - atomMirror t) = (s - 1 / 2) ^ 2 + (t : ℂ) ^ 2 := by
  simp only [atomPoint, atomMirror]; ring_nf; rw [I_sq]; ring

/-- `Λ = Γ_ℝ ζ` vanishes at a zero of ζ on the critical line. -/
theorem completedRiemannZeta_atomPoint_eq_zero {t : ℝ} (hz : riemannZeta (atomPoint t) = 0) :
    completedRiemannZeta (atomPoint t) = 0 := by
  have hre : 0 < (atomPoint t).re := by rw [atomPoint_re]; norm_num
  have h := riemannZeta_def_of_ne_zero (ne_zero_of_re_eq_half (atomPoint_re t))
  rw [hz, eq_comm, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (Gammaℝ_ne_zero_of_re_pos hre)

theorem completedRiemannZeta_atomMirror_eq_zero {t : ℝ} (hz : riemannZeta (atomPoint t) = 0) :
    completedRiemannZeta (atomMirror t) = 0 := by
  rw [atomMirror_eq_one_sub, completedRiemannZeta_one_sub]
  exact completedRiemannZeta_atomPoint_eq_zero hz

/-- The ζ-cancelled atom factor `Λ(s)/((s−½)² + t²)`, continued across `½ ± it`. -/
noncomputable def atomQuot (t : ℝ) : ℂ → ℂ :=
  dslope (dslope completedRiemannZeta (atomPoint t)) (atomMirror t)

theorem atomQuot_eq {t : ℝ} (ht : t ≠ 0) (hz : riemannZeta (atomPoint t) = 0) {s : ℂ}
    (h1 : s ≠ atomPoint t) (h2 : s ≠ atomMirror t) :
    atomQuot t s = completedRiemannZeta s / ((s - 1 / 2) ^ 2 + (t : ℂ) ^ 2) := by
  have hΛ1 := completedRiemannZeta_atomPoint_eq_zero hz
  have hΛ2 := completedRiemannZeta_atomMirror_eq_zero hz
  have hne := atomPoint_ne_atomMirror ht
  have hg : dslope completedRiemannZeta (atomPoint t) (atomMirror t) = 0 := by
    rw [dslope_of_ne _ hne.symm, slope_def_module, hΛ2, hΛ1, sub_zero, smul_zero]
  rw [atomQuot, dslope_of_ne _ h2, slope_def_module, hg, sub_zero,
    dslope_of_ne _ h1, slope_def_module, hΛ1, sub_zero, smul_eq_mul, smul_eq_mul,
    ← sub_atomPoint_mul_sub_atomMirror]
  have h1' : s - atomPoint t ≠ 0 := sub_ne_zero.mpr h1
  have h2' : s - atomMirror t ≠ 0 := sub_ne_zero.mpr h2
  field_simp

/-- The open set `ℂ ∖ {0, 1}` where `Λ` is holomorphic. -/
def zetaRegular : Set ℂ := {0, 1}ᶜ

theorem isOpen_zetaRegular : IsOpen zetaRegular :=
  (Set.Finite.isClosed (by simp : ({0, 1} : Set ℂ).Finite)).isOpen_compl

theorem differentiableOn_completedRiemannZeta_regular :
    DifferentiableOn ℂ completedRiemannZeta zetaRegular := by
  intro s hs
  simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt

theorem mem_zetaRegular_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) : z ∈ zetaRegular := by
  simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨ne_zero_of_re_eq_half hz, ne_one_of_re_eq_half hz⟩

theorem differentiableOn_atomQuot (t : ℝ) : DifferentiableOn ℂ (atomQuot t) zetaRegular := by
  have h1 : DifferentiableOn ℂ (dslope completedRiemannZeta (atomPoint t)) zetaRegular :=
    (differentiableOn_dslope (isOpen_zetaRegular.mem_nhds
      (mem_zetaRegular_of_re_eq_half (atomPoint_re t)))).mpr
      differentiableOn_completedRiemannZeta_regular
  exact (differentiableOn_dslope (isOpen_zetaRegular.mem_nhds
      (mem_zetaRegular_of_re_eq_half (atomMirror_re t)))).mpr h1

theorem one_sub_mem_zetaRegular {s : ℂ} (hs : s ∈ zetaRegular) : 1 - s ∈ zetaRegular := by
  simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs ⊢
  constructor
  · intro h; exact hs.2 (by linear_combination -h)
  · intro h; exact hs.1 (by linear_combination -h)

/-- `atomQuot` is symmetric under `s ↦ 1 − s`, from `Λ(1 − s) = Λ(s)` off the two atoms and
continuity at them. -/
theorem atomQuot_one_sub {t : ℝ} (ht : t ≠ 0) (hz : riemannZeta (atomPoint t) = 0) {s : ℂ}
    (hs : s ∈ zetaRegular) : atomQuot t (1 - s) = atomQuot t s := by
  have hc1 : ContinuousOn (fun z => atomQuot t (1 - z)) zetaRegular :=
    (differentiableOn_atomQuot t).continuousOn.comp (by fun_prop)
      (fun z hz => one_sub_mem_zetaRegular hz)
  have hc2 : ContinuousOn (atomQuot t) zetaRegular := (differentiableOn_atomQuot t).continuousOn
  have heq : ∀ z ∈ zetaRegular, z ≠ atomPoint t → z ≠ atomMirror t →
      atomQuot t (1 - z) = atomQuot t z := by
    intro z hzr h1 h2
    have h1' : 1 - z ≠ atomPoint t := by
      intro h; apply h2; rw [atomMirror_eq_one_sub, ← h]; ring
    have h2' : 1 - z ≠ atomMirror t := by
      intro h; apply h1; rw [atomMirror_eq_one_sub] at h; linear_combination -h
    rw [atomQuot_eq ht hz h1' h2', atomQuot_eq ht hz h1 h2, completedRiemannZeta_one_sub]
    congr 1; ring
  by_cases hgen : s ≠ atomPoint t ∧ s ≠ atomMirror t
  · exact heq s hs hgen.1 hgen.2
  -- `s` is one of the two atoms: approach it through punctured neighbourhoods
  have hU : zetaRegular ∈ 𝓝 s := isOpen_zetaRegular.mem_nhds hs
  have hev : ∀ᶠ z in 𝓝[≠] s, atomQuot t (1 - z) = atomQuot t z := by
    have hfin : ({atomPoint t, atomMirror t} \ {s} : Set ℂ).Finite := by
      exact (Set.toFinite _)
    have hcl : IsClosed ({atomPoint t, atomMirror t} \ {s} : Set ℂ) := hfin.isClosed
    have hnot : s ∉ ({atomPoint t, atomMirror t} \ {s} : Set ℂ) := by simp
    have hnhds : ({atomPoint t, atomMirror t} \ {s} : Set ℂ)ᶜ ∈ 𝓝 s :=
      hcl.isOpen_compl.mem_nhds hnot
    filter_upwards [nhdsWithin_le_nhds hU, nhdsWithin_le_nhds hnhds,
      self_mem_nhdsWithin] with z hz1 hz2 hz3
    refine heq z hz1 ?_ ?_
    · intro h; apply hz2
      refine ⟨by rw [h]; exact Set.mem_insert _ _, ?_⟩
      exact hz3
    · intro h; apply hz2
      refine ⟨by rw [h]; exact Set.mem_insert_of_mem _ rfl, ?_⟩
      exact hz3
  have ht1 : Tendsto (fun z => atomQuot t (1 - z)) (𝓝[≠] s) (𝓝 (atomQuot t (1 - s))) :=
    ((hc1.continuousAt hU).tendsto).mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (atomQuot t) (𝓝[≠] s) (𝓝 (atomQuot t s)) :=
    ((hc2.continuousAt hU).tendsto).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (ht1.congr' hev) ht2

/-- The ζ-cancelled atomic part `Σ_j (2c_j/π)(s − ½) Λ(s)/((s−½)² + t_j²)`, which equals `Λ Φ̃`
off the atoms and is holomorphic across them. -/
noncomputable def atomicZetaPart (c t : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' j, 2 * (c j : ℂ) / (Real.pi : ℂ) * (s - 1 / 2) * atomQuot (t j) s

theorem atomicPairSeries_one_sub (c t : ℕ → ℝ) (s : ℂ) :
    atomicPairSeries c t (1 - s) = -atomicPairSeries c t s := by
  unfold atomicPairSeries
  have h : ∀ j, (c j : ℂ) / ((1 - s - 1 / 2) ^ 2 + (t j : ℂ) ^ 2) =
      (c j : ℂ) / ((s - 1 / 2) ^ 2 + (t j : ℂ) ^ 2) := fun j => by ring_nf
  simp_rw [h]; ring

theorem atomicZetaPart_one_sub {c t : ℕ → ℝ} (ht : ∀ j, t j ≠ 0)
    (hz : ∀ j, riemannZeta (atomPoint (t j)) = 0) {s : ℂ} (hs : s ∈ zetaRegular) :
    atomicZetaPart c t (1 - s) = -atomicZetaPart c t s := by
  unfold atomicZetaPart
  rw [← tsum_neg]
  congr 1; ext j
  rw [atomQuot_one_sub (ht j) (hz j) hs]; ring

/-- Off the atoms, the ζ-cancelled part is `Λ · Φ̃`. -/
theorem atomicZetaPart_eq_mul {c t : ℕ → ℝ} (ht : ∀ j, t j ≠ 0)
    (hz : ∀ j, riemannZeta (atomPoint (t j)) = 0) {s : ℂ}
    (hs : ∀ j, s ≠ atomPoint (t j) ∧ s ≠ atomMirror (t j)) :
    atomicZetaPart c t s = completedRiemannZeta s * atomicPairSeries c t s := by
  unfold atomicZetaPart atomicPairSeries
  have h : ∀ j, 2 * (c j : ℂ) / (Real.pi : ℂ) * (s - 1 / 2) * atomQuot (t j) s =
      completedRiemannZeta s * (2 * (s - 1 / 2) / (Real.pi : ℂ)) *
        ((c j : ℂ) / ((s - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) := by
    intro j
    rw [atomQuot_eq (ht j) (hz j) (hs j).1 (hs j).2]
    ring
  simp_rw [h, tsum_mul_left]
  ring


/-- **Exponential decay of `Λ = Γ_ℝ ζ` in vertical strips.**  On `−1 ≤ Re z ≤ 2`, `|Im z| ≥ 2`:
`‖Λ(z)‖ ≤ C |Im z|^N e^{−π|Im z|/4}`. -/
theorem exists_bound_completedRiemannZeta_strip :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| →
      ‖completedRiemannZeta z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := by
  obtain ⟨Cg, Ng, hCg, hg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip (-1 / 2) 1
  obtain ⟨Cz, Nz, hCz, hz⟩ := exists_bound_norm_riemannZeta_strip 2
  refine ⟨Real.sqrt Real.pi * Cg * Cz, Ng + Nz, by positivity, fun z h1 h2 h3 => ?_⟩
  have hz0 : z ≠ 0 := by intro h; rw [h] at h3; norm_num at h3
  have him : 1 ≤ |z.im| := by linarith
  have hhalf : ((z / 2).im) = z.im / 2 := by simp
  have hΓ : Complex.Gamma (z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.im hm
    simp at this
    rw [this] at h3; norm_num at h3
  have hGR : Complex.Gammaℝ z ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero)))
      hΓ
  have hΛ : completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    rw [riemannZeta_def_of_ne_zero hz0, div_mul_cancel₀ _ hGR]
  rw [hΛ, norm_mul, Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hzeta : ‖riemannZeta z‖ ≤ Cz * |z.im| ^ Nz := by
    have := hz z.re z.im (by rw [abs_le]; constructor <;> linarith) him
    simpa using this
  have hgam : ‖Complex.Gamma (z / 2)‖ ≤ Cg * |z.im / 2| ^ Ng *
      Real.exp (-(Real.pi * |z.im / 2| / 2)) := by
    have := hg (z / 2) (by simp; linarith) (by simp; linarith)
      (by rw [hhalf, abs_div]; norm_num; linarith)
    rwa [hhalf] at this
  have hpi : Real.pi ^ (-z / 2).re ≤ Real.sqrt Real.pi := by
    have : (-z / 2).re ≤ 1 / 2 := by simp; linarith
    calc Real.pi ^ (-z / 2).re ≤ Real.pi ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) this
      _ = Real.sqrt Real.pi := (Real.sqrt_eq_rpow _).symm
  have habs : |z.im / 2| ^ Ng ≤ |z.im| ^ Ng := by
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_div]; norm_num
  have hexp : Real.exp (-(Real.pi * |z.im / 2| / 2)) = Real.exp (-(Real.pi * |z.im| / 4)) := by
    congr 1; rw [abs_div]; norm_num; ring
  rw [hexp] at hgam
  have hpow : |z.im| ^ (Ng + Nz) = |z.im| ^ Ng * |z.im| ^ Nz := pow_add _ _ _
  calc ‖riemannZeta z‖ * (Real.pi ^ (-z / 2).re * ‖Complex.Gamma (z / 2)‖)
      ≤ (Cz * |z.im| ^ Nz) * (Real.sqrt Real.pi *
          (Cg * |z.im| ^ Ng * Real.exp (-(Real.pi * |z.im| / 4)))) := by
        gcongr
        exact hgam.trans (by gcongr)
    _ = Real.sqrt Real.pi * Cg * Cz * |z.im| ^ (Ng + Nz) * Real.exp (-(Real.pi * |z.im| / 4)) := by
        rw [hpow]; ring

theorem norm_sub_atomPoint_ge {t : ℝ} (w : ℂ) : |w.im - t| ≤ ‖w - atomPoint t‖ := by
  have := Complex.abs_im_le_norm (w - atomPoint t)
  simpa [atomPoint] using this

theorem norm_sub_atomMirror_ge {t : ℝ} (w : ℂ) : |w.im + t| ≤ ‖w - atomMirror t‖ := by
  have := Complex.abs_im_le_norm (w - atomMirror t)
  simpa [atomMirror] using this

theorem sq_norm_sub_atomPoint (w : ℂ) (t : ℝ) :
    ‖w - atomPoint t‖ ^ 2 = (w.re - 1 / 2) ^ 2 + (w.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [atomPoint]; ring

/-- Points within distance `1` of `½ + it` (`t ≥ 1`) stay away from `0` and `1`, in the band
`|Re z − ½| ≤ 1`, `|Im z| ≤ t + 1`. -/
theorem mem_band_of_norm_sub_atomPoint_le {t : ℝ} (ht : 1 ≤ t) {z : ℂ}
    (hz : ‖z - atomPoint t‖ ≤ 1) :
    |z.re - 1 / 2| ≤ 1 ∧ |z.im| ≤ t + 1 ∧ 1 / 10 ≤ ‖z‖ ∧ 1 / 10 ≤ ‖z - 1‖ := by
  have hsq := sq_norm_sub_atomPoint z t
  have h1 : (z.re - 1 / 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.im - t), norm_nonneg (z - atomPoint t)]
  have h2 : (z.im - t) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.re - 1 / 2), norm_nonneg (z - atomPoint t)]
  have hre : |z.re - 1 / 2| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact h1
  have him : |z.im - t| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact h2
  refine ⟨hre, ?_, ?_, ?_⟩
  · rw [abs_le] at him ⊢; constructor <;> linarith
  · -- `‖z‖ ≥ |Im z| ≥ t − 1`, and if `t − 1` is small then `‖z − ρ‖ ≤ 1` forces `|Re z|` ...
    have hρ : ‖atomPoint t‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [atomPoint]; ring
    have hρ' : Real.sqrt (5 / 4) ≤ ‖atomPoint t‖ := by
      rw [Real.sqrt_le_left (norm_nonneg _)] ; nlinarith
    have hs : (1 + 1 / 10 : ℝ) ≤ Real.sqrt (5 / 4) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have htri : ‖atomPoint t‖ ≤ ‖z‖ + ‖z - atomPoint t‖ := by
      have := norm_sub_le z (z - atomPoint t); simpa using this
    linarith
  · have hρ : ‖atomPoint t - 1‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [atomPoint]; ring
    have hρ' : Real.sqrt (5 / 4) ≤ ‖atomPoint t - 1‖ := by
      rw [Real.sqrt_le_left (norm_nonneg _)]; nlinarith
    have hs : (1 + 1 / 10 : ℝ) ≤ Real.sqrt (5 / 4) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have htri : ‖atomPoint t - 1‖ ≤ ‖z - 1‖ + ‖z - atomPoint t‖ := by
      have := norm_sub_le (z - 1) (z - atomPoint t); simpa using this
    linarith

theorem mem_zetaRegular_of_norm_ge {z : ℂ} (h0 : 1 / 10 ≤ ‖z‖) (h1 : 1 / 10 ≤ ‖z - 1‖) :
    z ∈ zetaRegular := by
  simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro h; rw [h] at h0; norm_num at h0
  · intro h; rw [h] at h1; norm_num at h1

/-- `Λ` is bounded on the band `|Re z − ½| ≤ 1`, `|Im z| ≤ T`, away from `0` and `1`. -/
theorem exists_bound_completedRiemannZeta_band (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 → |z.im| ≤ T → 1 / 10 ≤ ‖z‖ →
      1 / 10 ≤ ‖z - 1‖ → ‖completedRiemannZeta z‖ ≤ M := by
  set K : Set ℂ := {z | |z.re - 1 / 2| ≤ 1 ∧ |z.im| ≤ T ∧ 1 / 10 ≤ ‖z‖ ∧ 1 / 10 ≤ ‖z - 1‖}
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have c1 : Continuous fun z : ℂ => |z.re - 1 / 2| :=
        continuous_abs.comp (Complex.continuous_re.sub continuous_const)
      have c2 : Continuous fun z : ℂ => |z.im| := continuous_abs.comp Complex.continuous_im
      have c3 : Continuous fun z : ℂ => ‖z‖ := continuous_norm
      have c4 : Continuous fun z : ℂ => ‖z - 1‖ := continuous_norm.comp (continuous_id.sub continuous_const)
      exact ((isClosed_le c1 continuous_const).inter
        ((isClosed_le c2 continuous_const).inter
          ((isClosed_le continuous_const c3).inter (isClosed_le continuous_const c4))))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 + |T|)).subset fun z hz => ?_
      obtain ⟨h1, h2, -, -⟩ := hz
      rw [mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 + |T| := by
            have : |z.re| ≤ 2 := by rw [abs_le] at h1 ⊢; constructor <;> linarith
            have : |z.im| ≤ |T| := h2.trans (le_abs_self T)
            linarith
  have hc : ContinuousOn completedRiemannZeta K :=
    differentiableOn_completedRiemannZeta_regular.continuousOn.mono fun z hz =>
      mem_zetaRegular_of_norm_ge hz.2.2.1 hz.2.2.2
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨max M 0, le_max_right _ _, fun z h1 h2 h3 h4 =>
    (hM z ⟨h1, h2, h3, h4⟩).trans (le_max_left _ _)⟩

/-- **Near an atom.**  If `‖Λ‖ ≤ M` on the unit circle about `½ + it` (`t ≥ 1`), then the
ζ-cancelled factor is at most `M` on the closed unit disc there (maximum modulus). -/
theorem norm_atomQuot_le_of_near {t : ℝ} (ht : 1 ≤ t) (hz : riemannZeta (atomPoint t) = 0)
    {M : ℝ} (hM : ∀ z ∈ sphere (atomPoint t) 1, ‖completedRiemannZeta z‖ ≤ M) {w : ℂ}
    (hw : ‖w - atomPoint t‖ ≤ 1) : ‖atomQuot t w‖ ≤ M := by
  have ht0 : t ≠ 0 := by linarith
  have hsub : closedBall (atomPoint t) 1 ⊆ zetaRegular := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hz
    obtain ⟨-, -, h3, h4⟩ := mem_band_of_norm_sub_atomPoint_le ht hz
    exact mem_zetaRegular_of_norm_ge h3 h4
  have hd : DiffContOnCl ℂ (atomQuot t) (ball (atomPoint t) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ one_ne_zero]
    exact (differentiableOn_atomQuot t).mono hsub
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (by rw [closure_ball _ one_ne_zero, mem_closedBall, dist_eq_norm]; exact hw)
  intro z hzs
  rw [frontier_ball _ one_ne_zero, mem_sphere, dist_eq_norm] at hzs
  have hmir : ‖atomPoint t - atomMirror t‖ = 2 * t := by
    have : atomPoint t - atomMirror t = ((2 * t : ℝ) : ℂ) * I := by
      simp only [atomPoint, atomMirror]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hzm : 1 ≤ ‖z - atomMirror t‖ := by
    have := norm_add_le (atomPoint t - z) (z - atomMirror t)
    rw [show atomPoint t - z + (z - atomMirror t) = atomPoint t - atomMirror t by ring, hmir,
      norm_sub_rev] at this
    linarith
  have h1 : z ≠ atomPoint t := by
    intro h; rw [h, sub_self, norm_zero] at hzs; norm_num at hzs
  have h2 : z ≠ atomMirror t := by
    intro h; rw [h, sub_self, norm_zero] at hzm; norm_num at hzm
  rw [atomQuot_eq ht0 hz h1 h2, ← sub_atomPoint_mul_sub_atomMirror, norm_div, norm_mul, hzs,
    one_mul]
  calc ‖completedRiemannZeta z‖ / ‖z - atomMirror t‖ ≤ ‖completedRiemannZeta z‖ / 1 := by
        gcongr
    _ ≤ M := by rw [div_one]; exact hM z (by rw [mem_sphere, dist_eq_norm]; exact hzs)

/-- **Near the mirror atom**, by the symmetry `Q(1 − w) = Q(w)`. -/
theorem norm_atomQuot_le_of_near_mirror {t : ℝ} (ht : 1 ≤ t) (hz : riemannZeta (atomPoint t) = 0)
    {M : ℝ} (hM : ∀ z ∈ sphere (atomPoint t) 1, ‖completedRiemannZeta z‖ ≤ M) {w : ℂ}
    (hw : ‖w - atomMirror t‖ ≤ 1) (hwr : w ∈ zetaRegular) : ‖atomQuot t w‖ ≤ M := by
  rw [← atomQuot_one_sub (by linarith) hz hwr]
  refine norm_atomQuot_le_of_near ht hz hM ?_
  have : 1 - w - atomPoint t = -(w - atomMirror t) := by rw [atomMirror_eq_one_sub]; ring
  rw [this, norm_neg]; exact hw

/-- **Far from both atoms**, the factor is `Λ(w)` divided by the two distances. -/
theorem norm_atomQuot_eq_of_far {t : ℝ} (ht : 1 ≤ t) (hz : riemannZeta (atomPoint t) = 0) {w : ℂ}
    (h1 : 1 ≤ ‖w - atomPoint t‖) (h2 : 1 ≤ ‖w - atomMirror t‖) :
    ‖atomQuot t w‖ = ‖completedRiemannZeta w‖ / (‖w - atomPoint t‖ * ‖w - atomMirror t‖) := by
  have hw1 : w ≠ atomPoint t := by intro h; rw [h, sub_self, norm_zero] at h1; norm_num at h1
  have hw2 : w ≠ atomMirror t := by intro h; rw [h, sub_self, norm_zero] at h2; norm_num at h2
  rw [atomQuot_eq (by linarith) hz hw1 hw2, ← sub_atomPoint_mul_sub_atomMirror, norm_div, norm_mul]


theorem sphere_atomPoint_band {t : ℝ} (ht : 1 ≤ t) {z : ℂ} (hz : z ∈ sphere (atomPoint t) 1) :
    |z.re - 1 / 2| ≤ 1 ∧ |z.im| ≤ t + 1 ∧ 1 / 10 ≤ ‖z‖ ∧ 1 / 10 ≤ ‖z - 1‖ ∧ t - 1 ≤ |z.im| := by
  rw [mem_sphere, dist_eq_norm] at hz
  obtain ⟨h1, h2, h3, h4⟩ := mem_band_of_norm_sub_atomPoint_le ht hz.le
  refine ⟨h1, h2, h3, h4, ?_⟩
  have := norm_sub_atomPoint_ge (t := t) z
  rw [hz] at this
  rw [abs_le] at this
  linarith [le_abs_self z.im]

/-- **Uniform local bound.**  Around each point of `ℂ ∖ {0,1}` there is a ball on which every
ζ-cancelled atom factor with `t ≥ 1` is `O(1/t²)`, uniformly in `t`. -/
theorem exists_local_bound_atomQuot {s₀ : ℂ} (hs₀ : s₀ ∈ zetaRegular) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ball s₀ r ⊆ zetaRegular ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 1 ≤ t → riemannZeta (atomPoint t) = 0 → ∀ w ∈ ball s₀ r,
        ‖atomQuot t w‖ ≤ C / t ^ 2 := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp isOpen_zetaRegular s₀ hs₀
  set r : ℝ := min (r₀ / 2) 1
  have hr : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hcl : closedBall s₀ r ⊆ zetaRegular := fun z hz =>
    hball (lt_of_le_of_lt (mem_closedBall.mp hz) (by
      have : r ≤ r₀ / 2 := min_le_left _ _; linarith))
  obtain ⟨Mloc, hMloc⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn
    (differentiableOn_completedRiemannZeta_regular.continuousOn.mono hcl)
  set T₁ : ℝ := 2 * (‖s₀‖ + 1) + 2
  have hT₁ : 2 ≤ T₁ := by simp only [T₁]; linarith [norm_nonneg s₀]
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bound_completedRiemannZeta_band (T₁ + 2)
  have hMloc0 : 0 ≤ Mloc := (norm_nonneg _).trans (hMloc s₀ (mem_closedBall_self hr.le))
  refine ⟨r, hr, hr1, fun z hz => hcl (ball_subset_closedBall hz),
    max Mb Mloc * T₁ ^ 2 + 4 * Mloc, by positivity, fun t ht hzt w hw => ?_⟩
  have ht0 : 0 < t := by linarith
  have hwim : |w.im| ≤ ‖s₀‖ + 1 := by
    have h1 := Complex.abs_im_le_norm w
    have h2 : ‖w‖ ≤ ‖s₀‖ + r := by
      have := norm_le_norm_add_norm_sub' w s₀
      rw [mem_ball, dist_eq_norm] at hw
      linarith [norm_sub_rev w s₀]
    linarith
  have hMsph : ∀ z ∈ sphere (atomPoint t) 1, t ≤ T₁ →
      ‖completedRiemannZeta z‖ ≤ Mb := by
    intro z hz htT
    obtain ⟨h1, h2, h3, h4, -⟩ := sphere_atomPoint_band ht hz
    exact hMb z h1 (by linarith) h3 h4
  have hwΛ : ‖completedRiemannZeta w‖ ≤ Mloc := hMloc w (ball_subset_closedBall hw)
  have ht2 : 0 < t ^ 2 := by positivity
  -- near either atom: then `t ≤ ‖s₀‖ + 2 ≤ T₁`
  by_cases hn1 : ‖w - atomPoint t‖ ≤ 1
  · have htT : t ≤ T₁ := by
      have := norm_sub_atomPoint_ge (t := t) w
      rw [abs_le] at this
      simp only [T₁]; linarith [le_abs_self w.im, norm_nonneg s₀]
    have hq := norm_atomQuot_le_of_near ht hzt (fun z hz => hMsph z hz htT) hn1
    rw [le_div_iff₀ ht2]
    calc ‖atomQuot t w‖ * t ^ 2 ≤ Mb * T₁ ^ 2 := by
          apply mul_le_mul hq (pow_le_pow_left₀ ht0.le htT 2) (by positivity) hMb0
      _ ≤ max Mb Mloc * T₁ ^ 2 + 4 * Mloc := by
          nlinarith [le_max_left Mb Mloc, sq_nonneg T₁]
  by_cases hn2 : ‖w - atomMirror t‖ ≤ 1
  · have htT : t ≤ T₁ := by
      have := norm_sub_atomMirror_ge (t := t) w
      rw [abs_le] at this
      simp only [T₁]; linarith [neg_abs_le w.im, norm_nonneg s₀]
    have hq := norm_atomQuot_le_of_near_mirror ht hzt (fun z hz => hMsph z hz htT) hn2
      (hcl (ball_subset_closedBall hw))
    rw [le_div_iff₀ ht2]
    calc ‖atomQuot t w‖ * t ^ 2 ≤ Mb * T₁ ^ 2 := by
          apply mul_le_mul hq (pow_le_pow_left₀ ht0.le htT 2) (by positivity) hMb0
      _ ≤ max Mb Mloc * T₁ ^ 2 + 4 * Mloc := by
          nlinarith [le_max_left Mb Mloc, sq_nonneg T₁]
  push Not at hn1 hn2
  rw [norm_atomQuot_eq_of_far ht hzt hn1.le hn2.le]
  have hd1 := norm_sub_atomPoint_ge (t := t) w
  have hd2 := norm_sub_atomMirror_ge (t := t) w
  have hprod : 1 ≤ ‖w - atomPoint t‖ * ‖w - atomMirror t‖ := by nlinarith
  rw [div_le_div_iff₀ (by positivity) ht2]
  rcases le_or_gt t T₁ with htT | htT
  · calc ‖completedRiemannZeta w‖ * t ^ 2 ≤ Mloc * T₁ ^ 2 := by
          apply mul_le_mul hwΛ (pow_le_pow_left₀ ht0.le htT 2) (by positivity) hMloc0
      _ ≤ (max Mb Mloc * T₁ ^ 2 + 4 * Mloc) * 1 := by
          nlinarith [le_max_right Mb Mloc, sq_nonneg T₁]
      _ ≤ (max Mb Mloc * T₁ ^ 2 + 4 * Mloc) * (‖w - atomPoint t‖ * ‖w - atomMirror t‖) := by
          gcongr
  · have h1 : t / 2 ≤ ‖w - atomPoint t‖ := by
      refine le_trans ?_ hd1
      rw [abs_sub_comm, le_abs]; left
      simp only [T₁] at htT; linarith [le_abs_self w.im]
    have h2 : t / 2 ≤ ‖w - atomMirror t‖ := by
      refine le_trans ?_ hd2
      rw [le_abs]; left
      simp only [T₁] at htT; linarith [neg_abs_le w.im]
    have hq : t ^ 2 / 4 ≤ ‖w - atomPoint t‖ * ‖w - atomMirror t‖ := by
      have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _); nlinarith
    calc ‖completedRiemannZeta w‖ * t ^ 2 ≤ Mloc * t ^ 2 := by gcongr
      _ = 4 * Mloc * (t ^ 2 / 4) := by ring
      _ ≤ 4 * Mloc * (‖w - atomPoint t‖ * ‖w - atomMirror t‖) := by gcongr
      _ ≤ (max Mb Mloc * T₁ ^ 2 + 4 * Mloc) * (‖w - atomPoint t‖ * ‖w - atomMirror t‖) := by
          gcongr; nlinarith [le_max_right Mb Mloc, sq_nonneg T₁, hMloc0]

/-- Hypotheses on the atoms: ordinates `t_j ≥ 1` of zeros of `ζ(½ + it)`, with
`Σ |c_j| / t_j² < ∞`. -/
structure ZetaAtoms (c t : ℕ → ℝ) : Prop where
  one_le : ∀ j, 1 ≤ t j
  zero : ∀ j, riemannZeta (atomPoint (t j)) = 0
  summable : Summable fun j => |c j| / t j ^ 2

/-- **The ζ-cancelled atomic part is holomorphic on `ℂ ∖ {0, 1}`.** -/
theorem differentiableOn_atomicZetaPart {c t : ℕ → ℝ} (h : ZetaAtoms c t) :
    DifferentiableOn ℂ (atomicZetaPart c t) zetaRegular := by
  intro s₀ hs₀
  obtain ⟨r, hr, hr1, hsub, C, hC0, hC⟩ := exists_local_bound_atomQuot hs₀
  have hd : DifferentiableOn ℂ (atomicZetaPart c t) (ball s₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun j => 2 / Real.pi * (‖s₀‖ + 2) * C * (|c j| / t j ^ 2))
      (h.summable.mul_left _) (fun j => ?_) isOpen_ball (fun j w hw => ?_)
    · exact ((differentiableOn_const _).mul ((differentiableOn_id).sub
        (differentiableOn_const _))).mul ((differentiableOn_atomQuot (t j)).mono hsub)
    · have hq := hC (t j) (h.one_le j) (h.zero j) w hw
      have hw' : ‖w - 1 / 2‖ ≤ ‖s₀‖ + 2 := by
        rw [mem_ball, dist_eq_norm] at hw
        calc ‖w - 1 / 2‖ ≤ ‖w - s₀‖ + ‖s₀‖ + ‖(1 / 2 : ℂ)‖ := by
              have := norm_sub_le (w - s₀ + s₀) (1 / 2 : ℂ)
              have h2 := norm_add_le (w - s₀) s₀
              simp only [sub_add_cancel] at this h2
              linarith
          _ ≤ ‖s₀‖ + 2 := by norm_num; linarith
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_two]
      have ht2 : 0 < t j ^ 2 := by have := h.one_le j; positivity
      calc 2 * |c j| / Real.pi * ‖w - 1 / 2‖ * ‖atomQuot (t j) w‖
          ≤ 2 * |c j| / Real.pi * (‖s₀‖ + 2) * (C / t j ^ 2) := by gcongr
        _ = 2 / Real.pi * (‖s₀‖ + 2) * C * (|c j| / t j ^ 2) := by ring
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).differentiableWithinAt


/-- `(y + 4)^m e^{−π y/4}` is bounded on `y ≥ 0`. -/
theorem exists_bound_pow_mul_exp_neg (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y → (y + 4) ^ m * Real.exp (-(Real.pi * y / 4)) ≤ K := by
  refine ⟨m.factorial * (8 / Real.pi) ^ m * Real.exp (Real.pi / 2), by positivity, fun y hy => ?_⟩
  have hpi := Real.pi_pos
  have hx : 0 ≤ Real.pi * (y + 4) / 8 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx m
  rw [div_le_iff₀ (by positivity)] at h
  have hpow : (y + 4) ^ m = (Real.pi * (y + 4) / 8) ^ m * (8 / Real.pi) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hpow]
  calc (Real.pi * (y + 4) / 8) ^ m * (8 / Real.pi) ^ m * Real.exp (-(Real.pi * y / 4))
      ≤ Real.exp (Real.pi * (y + 4) / 8) * m.factorial * (8 / Real.pi) ^ m *
          Real.exp (-(Real.pi * y / 4)) := by gcongr
    _ = m.factorial * (8 / Real.pi) ^ m * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * y / 8)) := by
        rw [show Real.exp (Real.pi * (y + 4) / 8) * m.factorial * (8 / Real.pi) ^ m *
            Real.exp (-(Real.pi * y / 4)) = m.factorial * (8 / Real.pi) ^ m *
            (Real.exp (Real.pi * (y + 4) / 8) * Real.exp (-(Real.pi * y / 4))) by ring,
          ← Real.exp_add, show Real.pi * (y + 4) / 8 + -(Real.pi * y / 4) =
            Real.pi / 2 + -(Real.pi * y / 8) by ring, Real.exp_add]; ring
    _ ≤ m.factorial * (8 / Real.pi) ^ m * Real.exp (Real.pi / 2) * 1 := by
        gcongr; rw [Real.exp_le_one_iff]; nlinarith
    _ = _ := by ring

/-- `‖(w − ρ)(w − ρ')‖ ≥ t²/(2|Im w| + 4)` when both distances are at least `1`. -/
theorem sq_div_le_norm_mul_of_far {t : ℝ} (ht : 1 ≤ t) {w : ℂ}
    (h1 : 1 ≤ ‖w - atomPoint t‖) (h2 : 1 ≤ ‖w - atomMirror t‖) :
    t ^ 2 / (2 * |w.im| + 4) ≤ ‖w - atomPoint t‖ * ‖w - atomMirror t‖ := by
  have hd1 := norm_sub_atomPoint_ge (t := t) w
  have hd2 := norm_sub_atomMirror_ge (t := t) w
  have hpos : 0 < 2 * |w.im| + 4 := by positivity
  rw [div_le_iff₀ hpos]
  rcases le_or_gt t (2 * |w.im| + 4) with hle | hgt
  · -- one of the two distances is at least `t`
    have hmax : t ≤ max ‖w - atomPoint t‖ ‖w - atomMirror t‖ := by
      have : |w.im - t| + |w.im + t| ≥ 2 * t := by
        have := abs_sub_le (w.im + t) w.im (w.im - t)
        have e : w.im + t - (w.im - t) = 2 * t := by ring
        rw [abs_sub_comm (w.im + t) w.im] at this
        calc |w.im - t| + |w.im + t| ≥ |w.im + t - (w.im - t)| := by
              have := abs_sub (w.im + t) (w.im - t); linarith [abs_sub_comm (w.im - t) (w.im + t)]
          _ = 2 * t := by rw [e, abs_of_pos (by linarith)]
      rcases le_total |w.im - t| |w.im + t| with h | h
      · exact le_trans (by linarith) (hd2.trans (le_max_right _ _))
      · exact le_trans (by linarith) (hd1.trans (le_max_left _ _))
    rcases le_total ‖w - atomPoint t‖ ‖w - atomMirror t‖ with h | h
    · rw [max_eq_right h] at hmax
      nlinarith [mul_le_mul h1 hmax (by linarith) (norm_nonneg _)]
    · rw [max_eq_left h] at hmax
      nlinarith [mul_le_mul hmax h2 (by linarith) (by linarith)]
  · have e1 : t / 2 ≤ ‖w - atomPoint t‖ := by
      refine le_trans ?_ hd1
      rw [abs_sub_comm, le_abs]; left; linarith [le_abs_self w.im]
    have e2 : t / 2 ≤ ‖w - atomMirror t‖ := by
      refine le_trans ?_ hd2
      rw [le_abs]; left; linarith [neg_abs_le w.im]
    have := mul_le_mul e1 e2 (by positivity) (norm_nonneg _)
    nlinarith [abs_nonneg w.im]

/-- **Vertical decay of the ζ-cancelled atomic part** on the strip `½ ≤ Re ≤ 3/2`. -/
theorem exists_decay_atomicZetaPart {c t : ℕ → ℝ} (h : ZetaAtoms c t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → 4 ≤ |w.im| →
      ‖atomicZetaPart c t w‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨CΛ, N, hCΛ, hΛ⟩ := exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK0, hK⟩ := exists_bound_pow_mul_exp_neg (N + 5)
  set S : ℝ := ∑' j, |c j| / t j ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j => by positivity
  refine ⟨2 / Real.pi * CΛ * Real.exp (Real.pi / 2) * S * K, by positivity, fun w h1 h2 h3 => ?_⟩
  set τ : ℝ := |w.im|
  have hτ : 4 ≤ τ := h3
  have hpi := Real.pi_pos
  set E₀ : ℝ := CΛ * (τ + 2) ^ N * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * τ / 4))
  have hE₀ : 0 ≤ E₀ := by positivity
  -- `Λ` on the unit circle about an atom near `w`
  have hsph : ∀ j, |τ - t j| ≤ 1 → ∀ z ∈ sphere (atomPoint (t j)) 1,
      ‖completedRiemannZeta z‖ ≤ E₀ := by
    intro j hj z hz
    obtain ⟨b1, b2, -, -, b5⟩ := sphere_atomPoint_band (h.one_le j) hz
    rw [abs_le] at hj
    have hzim1 : 2 ≤ |z.im| := by linarith
    have hzim2 : |z.im| ≤ τ + 2 := by linarith
    have hzim3 : τ - 2 ≤ |z.im| := by linarith
    have := hΛ z (by rw [abs_le] at b1; linarith) (by rw [abs_le] at b1; linarith) hzim1
    calc ‖completedRiemannZeta z‖ ≤ CΛ * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 4)) := this
      _ ≤ CΛ * (τ + 2) ^ N * Real.exp (-(Real.pi * (τ - 2) / 4)) := by
          gcongr
      _ = E₀ := by
          simp only [E₀]; rw [mul_assoc (CΛ * (τ + 2) ^ N), ← Real.exp_add]; congr 2; ring
  have hwΛ : ‖completedRiemannZeta w‖ ≤ E₀ := by
    have := hΛ w (by linarith) (by linarith) (by linarith)
    refine this.trans ?_
    simp only [E₀]
    have : CΛ * τ ^ N ≤ CΛ * (τ + 2) ^ N := by gcongr; linarith
    have he : 1 ≤ Real.exp (Real.pi / 2) := Real.one_le_exp (by positivity)
    calc CΛ * |w.im| ^ N * Real.exp (-(Real.pi * |w.im| / 4))
        ≤ CΛ * (τ + 2) ^ N * Real.exp (-(Real.pi * τ / 4)) := by gcongr
      _ ≤ CΛ * (τ + 2) ^ N * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi * τ / 4)) := by
          have h0 : 0 ≤ CΛ * (τ + 2) ^ N * Real.exp (-(Real.pi * τ / 4)) := by positivity
          nlinarith
  -- the per-atom bound
  have hq : ∀ j, ‖atomQuot (t j) w‖ ≤ E₀ * (τ + 4) ^ 2 / t j ^ 2 := by
    intro j
    have htj := h.one_le j
    have ht2 : 0 < t j ^ 2 := by positivity
    rw [le_div_iff₀ ht2]
    by_cases n1 : ‖w - atomPoint (t j)‖ ≤ 1
    · have hj : |τ - t j| ≤ 1 := by
        have := (norm_sub_atomPoint_ge (t := t j) w).trans n1
        have hpos : 0 ≤ w.im := by rw [abs_le] at this; linarith
        simpa [τ, abs_of_nonneg hpos] using this
      have hqj := norm_atomQuot_le_of_near htj (h.zero j) (hsph j hj) n1
      have htle : t j ≤ τ + 4 := by rw [abs_le] at hj; linarith
      exact mul_le_mul hqj (pow_le_pow_left₀ (by linarith) htle 2) (by positivity) hE₀
    by_cases n2 : ‖w - atomMirror (t j)‖ ≤ 1
    · have hj : |τ - t j| ≤ 1 := by
        have := (norm_sub_atomMirror_ge (t := t j) w).trans n2
        have hneg : w.im ≤ 0 := by rw [abs_le] at this; linarith
        have e : τ = -w.im := by simp only [τ]; exact abs_of_nonpos hneg
        rw [e]; rw [abs_le] at this ⊢; constructor <;> linarith
      have hreg : w ∈ zetaRegular := by
        simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        constructor
        · intro hw; have : τ = 0 := by simp only [τ]; rw [hw]; simp
          linarith
        · intro hw; have : τ = 0 := by simp only [τ]; rw [hw]; simp
          linarith
      have hqj := norm_atomQuot_le_of_near_mirror htj (h.zero j) (hsph j hj) n2 hreg
      have htle : t j ≤ τ + 4 := by rw [abs_le] at hj; linarith
      exact mul_le_mul hqj (pow_le_pow_left₀ (by linarith) htle 2) (by positivity) hE₀
    push Not at n1 n2
    rw [norm_atomQuot_eq_of_far htj (h.zero j) n1.le n2.le]
    have hfar := sq_div_le_norm_mul_of_far htj n1.le n2.le
    have hprod : 0 < ‖w - atomPoint (t j)‖ * ‖w - atomMirror (t j)‖ := by
      have := mul_le_mul n1.le n2.le zero_le_one (by linarith); linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hprod]
    have hτ' : 2 * |w.im| + 4 ≤ (τ + 4) ^ 2 := by simp only [τ]; nlinarith
    calc ‖completedRiemannZeta w‖ * t j ^ 2
        = ‖completedRiemannZeta w‖ * (t j ^ 2 / (2 * |w.im| + 4)) * (2 * |w.im| + 4) := by
          field_simp
      _ ≤ E₀ * (‖w - atomPoint (t j)‖ * ‖w - atomMirror (t j)‖) * (τ + 4) ^ 2 := by
          gcongr
      _ = E₀ * (τ + 4) ^ 2 * (‖w - atomPoint (t j)‖ * ‖w - atomMirror (t j)‖) := by ring
  -- sum over atoms
  have hw12 : ‖w - 1 / 2‖ ≤ τ + 1 := by
    have := Complex.norm_le_abs_re_add_abs_im (w - 1 / 2)
    have hre : |(w - 1 / 2).re| ≤ 1 := by
      simp; rw [abs_le]; constructor <;> linarith
    have him : (w - 1 / 2).im = w.im := by simp
    rw [him] at this; linarith
  have hterm : ∀ j, ‖2 * (c j : ℂ) / (Real.pi : ℂ) * (w - 1 / 2) * atomQuot (t j) w‖ ≤
      2 / Real.pi * (τ + 1) * (E₀ * (τ + 4) ^ 2) * (|c j| / t j ^ 2) := by
    intro j
    rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_two]
    calc 2 * |c j| / Real.pi * ‖w - 1 / 2‖ * ‖atomQuot (t j) w‖
        ≤ 2 * |c j| / Real.pi * (τ + 1) * (E₀ * (τ + 4) ^ 2 / t j ^ 2) := by
          gcongr; exact hq j
      _ = 2 / Real.pi * (τ + 1) * (E₀ * (τ + 4) ^ 2) * (|c j| / t j ^ 2) := by ring
  have hsum : Summable fun j => ‖2 * (c j : ℂ) / (Real.pi : ℂ) * (w - 1 / 2) * atomQuot (t j) w‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm (h.summable.mul_left _)
  have hZ : ‖atomicZetaPart c t w‖ ≤ 2 / Real.pi * (τ + 1) * (E₀ * (τ + 4) ^ 2) * S := by
    unfold atomicZetaPart
    refine (norm_tsum_le_tsum_norm hsum).trans ?_
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm (h.summable.mul_left _)
  refine hZ.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hpow : (1 + w.im ^ 2) * (τ + 1) * (τ + 4) ^ 2 * (τ + 2) ^ N ≤ (τ + 4) ^ (N + 5) := by
    have e : w.im ^ 2 = τ ^ 2 := (sq_abs w.im).symm
    rw [e, pow_add]
    have a1 : (τ + 2) ^ N ≤ (τ + 4) ^ N := by gcongr; linarith
    have a2 : (1 + τ ^ 2) * (τ + 1) * (τ + 4) ^ 2 ≤ (τ + 4) ^ 5 := by nlinarith
    calc (1 + τ ^ 2) * (τ + 1) * (τ + 4) ^ 2 * (τ + 2) ^ N
        ≤ (τ + 4) ^ 5 * (τ + 4) ^ N := by gcongr
      _ = (τ + 4) ^ N * (τ + 4) ^ 5 := by ring
  have hKτ := hK τ (by linarith)
  calc 2 / Real.pi * (τ + 1) * (E₀ * (τ + 4) ^ 2) * S * (1 + w.im ^ 2)
      = 2 / Real.pi * CΛ * Real.exp (Real.pi / 2) * S *
          ((1 + w.im ^ 2) * (τ + 1) * (τ + 4) ^ 2 * (τ + 2) ^ N * Real.exp (-(Real.pi * τ / 4))) := by
        simp only [E₀]; ring
    _ ≤ 2 / Real.pi * CΛ * Real.exp (Real.pi / 2) * S *
          ((τ + 4) ^ (N + 5) * Real.exp (-(Real.pi * τ / 4))) := by gcongr
    _ ≤ 2 / Real.pi * CΛ * Real.exp (Real.pi / 2) * S * K := by gcongr

end RHTower
