import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource
import GaloisForLFunctions.RHTower.BurnolCoPoissonLinearity
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip

/-!
# The Mellin transform of the co-Poisson sum of a general window seed

Truncating the Mellin integral of the co-Poisson sum at a finite cutoff `T` leaves only the finitely
many indices `k <= T/b`, so no interchange of an infinite sum with an integral is needed.  What
remains is the kernel

`kappa_T(u) = u^(-w) sum_(k <= floor (T/u)) k^(-w) - u^(-1) T^(1-w)/(1-w)`,

whose two divergent halves cancel *identically*, because `u^(-w) (T/u)^(1-w) = u^(-1) T^(1-w)`.
The partial-sum asymptotic for zeta on the strip therefore makes `kappa_T` converge pointwise to
`zeta(w) u^(-w)` with a uniform bound on the window, and dominated convergence against an integrable
seed transports the identity to the Mellin transform of the co-Poisson sum.
-/

open Complex Real MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem cpow_ofReal_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℝ) : ℂ) ^ s = Complex.exp (((Real.log x : ℝ) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]

/-- The error in the partial-sum asymptotic for zeta on the strip. -/
def zetaStripError (w : ℂ) (N : ℕ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) - ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w

theorem sum_cpow_eq_zetaStripError (w : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) =
      riemannZeta w + ((N : ℝ) : ℂ) ^ (1 - w) / (1 - w) + zetaStripError w N := by
  rw [zetaStripError]; ring

theorem tendsto_zetaStripError {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) :
    Tendsto (zetaStripError w) atTop (nhds 0) := by
  have h := (tendsto_sum_cpow_sub_pow hw0 hwne1).sub_const (riemannZeta w)
  rw [sub_self] at h
  exact h

theorem exists_bound_zetaStripError {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, ‖zetaStripError w N‖ ≤ E := by
  have h := (tendsto_zetaStripError hw0 hwne1).norm
  rw [norm_zero] at h
  obtain ⟨E, hE⟩ := h.bddAbove_range
  refine ⟨max E 0, le_max_right _ _, fun N => ?_⟩
  exact le_trans (hE ⟨N, rfl⟩) (le_max_left _ _)

/-- Replacing a real argument by its floor changes a complex power by `O(N^(Re s - 1))`. -/
theorem norm_cpow_natFloor_sub_cpow_le {s : ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hs : ‖s‖ ≤ (⌊M⌋₊ : ℝ)) :
    ‖((⌊M⌋₊ : ℝ) : ℂ) ^ s - ((M : ℝ) : ℂ) ^ s‖ ≤
      2 * ‖s‖ * ((⌊M⌋₊ : ℝ) ^ (s.re - 1)) := by
  set N : ℕ := ⌊M⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by exact_mod_cast hM)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hMlt : M < (N : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one M
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogdiff : 0 ≤ Real.log M - Real.log (N : ℝ) := by
    have := Real.log_le_log hNpos hNle
    linarith
  have hlogle : Real.log M - Real.log (N : ℝ) ≤ (N : ℝ)⁻¹ := by
    have hdiv : Real.log M - Real.log (N : ℝ) = Real.log (M / (N : ℝ)) := by
      rw [Real.log_div hMpos.ne' hNpos.ne']
    rw [hdiv]
    have h1 : Real.log (M / (N : ℝ)) ≤ M / (N : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : M / (N : ℝ) - 1 ≤ (N : ℝ)⁻¹ := by
      rw [div_sub_one hNpos.ne', div_le_iff₀ hNpos]
      field_simp
      linarith
    linarith
  set z : ℂ := ((Real.log M - Real.log (N : ℝ) : ℝ) : ℂ) * s with hz
  have hznorm : ‖z‖ ≤ ‖s‖ * (N : ℝ)⁻¹ := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogdiff, mul_comm]
    exact mul_le_mul_of_nonneg_left hlogle (norm_nonneg s)
  have hzle1 : ‖z‖ ≤ 1 := by
    refine le_trans hznorm ?_
    rw [mul_inv_le_iff₀ hNpos, one_mul]
    exact hs
  have hfac : ((M : ℝ) : ℂ) ^ s =
      ((N : ℝ) : ℂ) ^ s * Complex.exp z := by
    rw [cpow_ofReal_eq_exp hMpos, cpow_ofReal_eq_exp hNpos, ← Complex.exp_add, hz]
    congr 1
    push_cast
    ring
  have hsplit : ((N : ℝ) : ℂ) ^ s - ((M : ℝ) : ℂ) ^ s =
      ((N : ℝ) : ℂ) ^ s * (1 - Complex.exp z) := by
    rw [hfac]; ring
  rw [hsplit, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hexp : ‖1 - Complex.exp z‖ ≤ 2 * ‖z‖ := by
    rw [← norm_neg]
    simpa [neg_sub] using Complex.norm_exp_sub_one_le hzle1
  have hchain : ‖1 - Complex.exp z‖ ≤ 2 * (‖s‖ * (N : ℝ)⁻¹) :=
    le_trans hexp (by linarith [hznorm])
  have hpow : (N : ℝ) ^ s.re * (2 * (‖s‖ * (N : ℝ)⁻¹)) = 2 * ‖s‖ * (N : ℝ) ^ (s.re - 1) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
    field_simp
  calc (N : ℝ) ^ s.re * ‖1 - Complex.exp z‖
      ≤ (N : ℝ) ^ s.re * (2 * (‖s‖ * (N : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hchain (Real.rpow_nonneg hNpos.le _)
    _ = 2 * ‖s‖ * ((N : ℝ) ^ (s.re - 1)) := hpow


theorem inv_ofReal_eq_exp {u : ℝ} (hu : 0 < u) :
    ((u : ℝ) : ℂ)⁻¹ = Complex.exp (((Real.log u : ℝ) : ℂ) * (-1)) := by
  rw [← cpow_ofReal_eq_exp hu, Complex.cpow_neg_one]

/-- The exact cancellation behind the co-Poisson Mellin kernel. -/
theorem cpow_neg_mul_div_cpow {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (w : ℂ) :
    ((u : ℝ) : ℂ) ^ (-w) * (((T / u : ℝ)) : ℂ) ^ (1 - w) =
      ((u : ℝ) : ℂ)⁻¹ * ((T : ℝ) : ℂ) ^ (1 - w) := by
  have hdiv : (0 : ℝ) < T / u := div_pos hT hu
  rw [cpow_ofReal_eq_exp hu, cpow_ofReal_eq_exp hdiv, cpow_ofReal_eq_exp hT,
    inv_ofReal_eq_exp hu, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.log_div hT.ne' hu.ne']
  push_cast
  ring

/-- The truncated Mellin kernel of the co-Poisson sum at cutoff `T`. -/
def coPoissonMellinKernel (w : ℂ) (T u : ℝ) : ℂ :=
  ((u : ℝ) : ℂ) ^ (-w) * (∑ k ∈ Finset.Icc 1 ⌊T / u⌋₊, ((k : ℝ) : ℂ) ^ (-w)) -
    ((u : ℝ) : ℂ)⁻¹ * (((T : ℝ) : ℂ) ^ (1 - w) / (1 - w))

/-- The kernel differs from its limit by the partial-sum error and the floor error only. -/
theorem coPoissonMellinKernel_sub {w : ℂ} (hw : w ≠ 1) {T u : ℝ} (hu : 0 < u) (hT : 0 < T) :
    coPoissonMellinKernel w T u - riemannZeta w * ((u : ℝ) : ℂ) ^ (-w) =
      ((u : ℝ) : ℂ) ^ (-w) * zetaStripError w ⌊T / u⌋₊ +
        ((u : ℝ) : ℂ) ^ (-w) *
          ((((⌊T / u⌋₊ : ℕ) : ℝ) : ℂ) ^ (1 - w) - ((T / u : ℝ) : ℂ) ^ (1 - w)) / (1 - w) := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hcancel := cpow_neg_mul_div_cpow hu hT w
  rw [coPoissonMellinKernel, sum_cpow_eq_zetaStripError]
  linear_combination ((1 : ℂ) / (1 - w)) * hcancel

theorem norm_coPoissonMellinKernel_sub_le {w : ℂ} (hw : w ≠ 1)
    {T u : ℝ} (hu : 0 < u) (hT : 0 < T) (hTu : ‖1 - w‖ + 1 ≤ T / u) :
    ‖coPoissonMellinKernel w T u - riemannZeta w * ((u : ℝ) : ℂ) ^ (-w)‖ ≤
      u ^ (-w.re) *
        (‖zetaStripError w ⌊T / u⌋₊‖ + 2 * ((⌊T / u⌋₊ : ℕ) : ℝ) ^ (-w.re)) := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hnw : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  set M : ℝ := T / u with hM
  have hM1 : 1 ≤ M := le_trans (by linarith [norm_nonneg (1 - w)]) hTu
  set N : ℕ := ⌊M⌋₊ with hN
  have hNfloor : ‖1 - w‖ ≤ (N : ℝ) := by
    have h2 : M < (N : ℝ) + 1 := Nat.lt_floor_add_one M
    linarith
  have hupow : ‖((u : ℝ) : ℂ) ^ (-w)‖ = u ^ (-w.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re]
  have hupos : (0 : ℝ) < u ^ (-w.re) := Real.rpow_pos_of_pos hu _
  have hre : (1 - w).re - 1 = -w.re := by
    rw [Complex.sub_re, Complex.one_re]; ring
  rw [coPoissonMellinKernel_sub hw hu hT]
  refine le_trans (norm_add_le _ _) ?_
  have hfirst : ‖((u : ℝ) : ℂ) ^ (-w) * zetaStripError w N‖ =
      u ^ (-w.re) * ‖zetaStripError w N‖ := by
    rw [norm_mul, hupow]
  have hfloor := norm_cpow_natFloor_sub_cpow_le (s := 1 - w) hM1 (by rw [← hN]; exact hNfloor)
  rw [hre] at hfloor
  have hsecond : ‖((u : ℝ) : ℂ) ^ (-w) *
      ((((N : ℕ) : ℝ) : ℂ) ^ (1 - w) - ((M : ℝ) : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      u ^ (-w.re) * (2 * ((N : ℕ) : ℝ) ^ (-w.re)) := by
    rw [norm_div, norm_mul, hupow, div_le_iff₀ hnw]
    calc u ^ (-w.re) * ‖(((N : ℕ) : ℝ) : ℂ) ^ (1 - w) - ((M : ℝ) : ℂ) ^ (1 - w)‖
        ≤ u ^ (-w.re) * (2 * ‖1 - w‖ * (((N : ℕ) : ℝ) ^ (-w.re))) :=
          mul_le_mul_of_nonneg_left hfloor hupos.le
      _ = u ^ (-w.re) * (2 * ((N : ℕ) : ℝ) ^ (-w.re)) * ‖1 - w‖ := by ring
  calc ‖((u : ℝ) : ℂ) ^ (-w) * zetaStripError w N‖ +
        ‖((u : ℝ) : ℂ) ^ (-w) *
          ((((N : ℕ) : ℝ) : ℂ) ^ (1 - w) - ((M : ℝ) : ℂ) ^ (1 - w)) / (1 - w)‖
      ≤ u ^ (-w.re) * ‖zetaStripError w N‖ + u ^ (-w.re) * (2 * ((N : ℕ) : ℝ) ^ (-w.re)) :=
        add_le_add (le_of_eq hfirst) hsecond
    _ = u ^ (-w.re) * (‖zetaStripError w N‖ + 2 * ((N : ℕ) : ℝ) ^ (-w.re)) := by ring

/-- Uniform bound on the truncated kernel, valid once the cutoff clears the window. -/
theorem norm_coPoissonMellinKernel_sub_le_const {w : ℂ} (hw : w ≠ 1) (hw0 : 0 ≤ w.re)
    {T u : ℝ} (hu : 0 < u) (hT : 0 < T) (hTu : ‖1 - w‖ + 1 ≤ T / u)
    {E : ℝ} (hE : ∀ N : ℕ, ‖zetaStripError w N‖ ≤ E) :
    ‖coPoissonMellinKernel w T u - riemannZeta w * ((u : ℝ) : ℂ) ^ (-w)‖ ≤
      u ^ (-w.re) * (E + 2) := by
  refine le_trans (norm_coPoissonMellinKernel_sub_le hw hu hT hTu) ?_
  have hupos : (0 : ℝ) < u ^ (-w.re) := Real.rpow_pos_of_pos hu _
  refine mul_le_mul_of_nonneg_left ?_ hupos.le
  have hM1 : (1 : ℝ) ≤ T / u := le_trans (by linarith [norm_nonneg (1 - w)]) hTu
  have hN1 : (1 : ℝ) ≤ ((⌊T / u⌋₊ : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ ⌊T / u⌋₊ := Nat.le_floor (by exact_mod_cast hM1)
    exact_mod_cast this
  have hsmall : ((⌊T / u⌋₊ : ℕ) : ℝ) ^ (-w.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have := hE ⌊T / u⌋₊
  linarith

/-- The truncated kernel converges pointwise to the completed zeta kernel. -/
theorem tendsto_coPoissonMellinKernel {w : ℂ} (hw0 : 0 < w.re) (hw : w ≠ 1) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => coPoissonMellinKernel w (n : ℝ) u) atTop
      (nhds (riemannZeta w * ((u : ℝ) : ℂ) ^ (-w))) := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hupow : ‖((u : ℝ) : ℂ) ^ (-w)‖ = u ^ (-w.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re]
  -- the floor of `n / u` tends to infinity
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) / u) atTop atTop :=
    Filter.Tendsto.atTop_div_const hu tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun n : ℕ => ⌊(n : ℝ) / u⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hdiv
  -- the two error terms tend to zero
  have hA : Tendsto (fun n : ℕ => ‖zetaStripError w ⌊(n : ℝ) / u⌋₊‖) atTop (nhds 0) := by
    have := ((tendsto_zetaStripError hw0 hw).comp hfloor).norm
    rw [norm_zero] at this
    exact this
  have hB : Tendsto (fun n : ℕ => 2 * ((⌊(n : ℝ) / u⌋₊ : ℕ) : ℝ) ^ (-w.re)) atTop (nhds 0) := by
    have hrp : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-w.re)) atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (y := w.re) hw0
      exact this.comp tendsto_natCast_atTop_atTop
    have := (hrp.comp hfloor).const_mul (2 : ℝ)
    rw [mul_zero] at this
    exact this
  have hsum : Tendsto
      (fun n : ℕ => u ^ (-w.re) *
        (‖zetaStripError w ⌊(n : ℝ) / u⌋₊‖ + 2 * ((⌊(n : ℝ) / u⌋₊ : ℕ) : ℝ) ^ (-w.re)))
      atTop (nhds 0) := by
    have := (hA.add hB).const_mul (u ^ (-w.re))
    rw [add_zero, mul_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hsum
  filter_upwards [eventually_ge_atTop (⌈(‖1 - w‖ + 1) * u⌉₊ + 1)] with n hn
  have hn1 : (1 : ℕ) ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hceil : ((⌈(‖1 - w‖ + 1) * u⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (‖1 - w‖ + 1) * u ≤ ((⌈(‖1 - w‖ + 1) * u⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hTu : ‖1 - w‖ + 1 ≤ (n : ℝ) / u := by
    rw [le_div_iff₀ hu]
    linarith
  exact norm_coPoissonMellinKernel_sub_le hw hu hnpos hTu


variable {b : ℝ} {g : ℝ → ℂ}

theorem seed_eq_zero_of_le {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {u : ℝ} (hu : u < b) : g u = 0 := by
  by_contra hz
  exact absurd (hsupp (Function.mem_support.mpr hz)).1 (not_le.mpr hu)

theorem norm_cpow_le_of_seed {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) (u : ℝ) :
    ‖g u * ((u : ℝ) : ℂ) ^ (-w)‖ ≤ b ^ (-w.re) * ‖g u‖ := by
  by_cases hz : g u = 0
  · simp [hz]
  · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hb hmem.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hupos, Complex.neg_re, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos hb hmem.1 (by linarith)

/-- The seed against the Mellin kernel is globally integrable. -/
theorem integrable_seed_mul_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) :
    Integrable (fun u : ℝ => g u * ((u : ℝ) : ℂ) ^ (-w)) := by
  refine Integrable.mono' (g := fun u : ℝ => b ^ (-w.re) * ‖g u‖) (hg.norm.const_mul _)
    (hg.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.pow_const (-w)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (norm_cpow_le_of_seed hb hsupp hw0))

theorem seed_eq_zero_of_lt {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {u : ℝ} (hu : b⁻¹ < u) : g u = 0 := by
  by_contra hz
  exact absurd (hsupp (Function.mem_support.mpr hz)).2 (not_le.mpr hu)

/-- Dilating the seed by a positive integer factors the Mellin kernel. -/
theorem seed_dilate_cpow_eq {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) (k : ℕ) (w : ℂ) :
    (fun y : ℝ => g y * (((((k : ℕ) : ℝ) * y : ℝ)) : ℂ) ^ (-w)) =
      fun y : ℝ => (((k : ℕ) : ℝ) : ℂ) ^ (-w) * (g y * ((y : ℝ) : ℂ) ^ (-w)) := by
  funext y
  by_cases hz : g y = 0
  · simp [hz]
  · have hmem : y ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
    have hypos : (0 : ℝ) ≤ y := le_of_lt (lt_of_lt_of_le hb hmem.1)
    have hkpos : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg k
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hkpos hypos]
    ring

/-- For a cutoff `T` only the indices below `T/b` contribute, uniformly in `t <= T`. -/
theorem coPoissonSum_eq_fixed_finset_sum {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((m + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊, (((k : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) := by
  rw [coPoissonSum_eq_window_finset_sum hb ht hsupp]
  refine Finset.sum_subset ?_ ?_
  · refine Finset.Icc_subset_Icc (Nat.one_le_ceil_iff.mpr (by positivity)) ?_
    exact Nat.floor_le_floor (by gcongr)
  · intro k hk hknot
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hkpos : 0 < k := hk1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    rcases lt_or_ge k ⌈t * b⌉₊ with hlow | hhigh
    · have hlt : (k : ℝ) < t * b := Nat.lt_ceil.mp hlow
      have : b⁻¹ < t / (k : ℝ) := by
        rw [lt_div_iff₀ hkR, inv_mul_eq_div, div_lt_iff₀ hb]
        linarith [hlt]
      rw [seed_eq_zero_of_lt hsupp this, mul_zero]
    · have hup : ⌊t / b⌋₊ < k := by
        by_contra hcon
        exact hknot (Finset.mem_Icc.mpr ⟨hhigh, not_lt.mp hcon⟩)
      have hlt : t / b < (k : ℝ) := (Nat.floor_lt (by positivity)).mp hup
      have : t / (k : ℝ) < b := by
        rw [div_lt_iff₀ hkR]
        rw [div_lt_iff₀ hb] at hlt
        linarith
      rw [seed_eq_zero_of_le hsupp this, mul_zero]

/-- The dilated seed integral, after the substitution `t = k u`. -/
theorem integral_Ioc_seed_dilate_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : ℂ) {k : ℕ} (hk : 1 ≤ k)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioc (0 : ℝ) T,
        ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w)) =
      (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
        ∫ u in Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)), g u * ((u : ℝ) : ℂ) ^ (-w) := by
  have hkR : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
  set H : ℝ → ℂ := fun y => g y * (((((k : ℕ) : ℝ) * y : ℝ)) : ℂ) ^ (-w) with hHdef
  have hHeq : H = fun y : ℝ => (((k : ℕ) : ℝ) : ℂ) ^ (-w) * (g y * ((y : ℝ) : ℂ) ^ (-w)) := by
    rw [hHdef]; exact seed_dilate_cpow_eq hb hsupp k w
  have hpt : ∀ t : ℝ,
      ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w) =
        ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * H (((k : ℕ) : ℝ)⁻¹ * t) := by
    intro t
    have hmul : ((k : ℕ) : ℝ) * (((k : ℕ) : ℝ)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hkR), one_mul]
    rw [hHdef]
    simp only [hmul]
    have harg : ((k : ℕ) : ℝ)⁻¹ * t = t / ((k : ℕ) : ℝ) := (div_eq_inv_mul t _).symm
    rw [harg, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpt t)]
  rw [MeasureTheory.integral_const_mul]
  rw [← intervalIntegral.integral_of_le hT]
  have hsmul := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := T) H
    (((k : ℕ) : ℝ)⁻¹)
  rw [mul_zero, inv_mul_eq_div] at hsmul
  have hTk : (0 : ℝ) ≤ T / ((k : ℕ) : ℝ) := div_nonneg hT (Nat.cast_nonneg k)
  have hHint : (∫ x in (0 : ℝ)..T, H (((k : ℕ) : ℝ)⁻¹ * x)) =
      ((k : ℕ) : ℝ) • ∫ x in (0 : ℝ)..(T / ((k : ℕ) : ℝ)), H x := by
    rw [← hsmul, smul_smul, mul_inv_cancel₀ (ne_of_gt hkR), one_smul]
  rw [hHint, intervalIntegral.integral_of_le hTk]
  rw [hHeq]
  rw [MeasureTheory.integral_const_mul]
  rw [Complex.real_smul]
  have hkne : (((k : ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hkR)
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hkne, one_mul]


theorem integrable_seed_dilate_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun t : ℝ =>
      ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w)) := by
  have hkR : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
  have hbase : Integrable (fun y : ℝ => g y * ((y : ℝ) : ℂ) ^ (-w)) :=
    integrable_seed_mul_cpow hb hg hsupp hw0
  have hH : Integrable (fun y : ℝ => g y * (((((k : ℕ) : ℝ) * y : ℝ)) : ℂ) ^ (-w)) := by
    rw [seed_dilate_cpow_eq hb hsupp k w]
    exact hbase.const_mul _
  have hcomp : Integrable (fun t : ℝ =>
      g (((k : ℕ) : ℝ)⁻¹ * t) * (((((k : ℕ) : ℝ) * (((k : ℕ) : ℝ)⁻¹ * t) : ℝ)) : ℂ) ^ (-w)) :=
    hH.comp_mul_left' (inv_ne_zero (ne_of_gt hkR))
  have heq : (fun t : ℝ =>
      ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w)) =
      fun t : ℝ => ((((k : ℕ) : ℝ)) : ℂ)⁻¹ *
        (g (((k : ℕ) : ℝ)⁻¹ * t) *
          (((((k : ℕ) : ℝ) * (((k : ℕ) : ℝ)⁻¹ * t) : ℝ)) : ℂ) ^ (-w)) := by
    funext t
    have hmul : ((k : ℕ) : ℝ) * (((k : ℕ) : ℝ)⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hkR), one_mul]
    have harg : ((k : ℕ) : ℝ)⁻¹ * t = t / ((k : ℕ) : ℝ) := (div_eq_inv_mul t _).symm
    rw [hmul, harg, mul_assoc]
  rw [heq]
  exact hcomp.const_mul _

/-- The truncated Mellin integral of the co-Poisson sum, as a finite sum of dilated seed
integrals. -/
theorem integral_Ioc_coPoissonSum_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc (0 : ℝ) T,
        (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((m + 1 : ℕ) : ℝ))) *
          ((t : ℝ) : ℂ) ^ (-w)) =
      ∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
        ∫ u in Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)), g u * ((u : ℝ) : ℂ) ^ (-w) := by
  have hpt : ∀ t ∈ Ioc (0 : ℝ) T,
      (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((m + 1 : ℕ) : ℝ))) *
          ((t : ℝ) : ℂ) ^ (-w) =
        ∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊,
          ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w) := by
    intro t ht
    rw [coPoissonSum_eq_fixed_finset_sum hb hsupp ht.1 ht.2, Finset.sum_mul]
  rw [setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    exact integral_Ioc_seed_dilate_cpow hb hsupp w (Finset.mem_Icc.mp hk).1 hT.le
  · intro k hk
    exact (integrable_seed_dilate_cpow hb hg hsupp hw0 (Finset.mem_Icc.mp hk).1).restrict



theorem mem_Ioc_div_iff_le_floor {T u : ℝ} (hT : 0 < T) (hu : 0 < u) {k : ℕ} (hk : 1 ≤ k) :
    u ∈ Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)) ↔ k ≤ ⌊T / u⌋₊ := by
  have hkR : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
  rw [Nat.le_floor_iff (le_of_lt (div_pos hT hu))]
  constructor
  · rintro ⟨-, hle⟩
    rw [le_div_iff₀ hkR] at hle
    rw [le_div_iff₀ hu]
    linarith [hle]
  · intro hle
    rw [le_div_iff₀ hu] at hle
    refine ⟨hu, ?_⟩
    rw [le_div_iff₀ hkR]
    linarith [hle]

theorem sum_indicator_cpow_eq {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} {T u : ℝ} (hT : 0 < T) (hu : 0 < u) :
    (∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
        (Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ))).indicator
          (fun v : ℝ => g v * ((v : ℝ) : ℂ) ^ (-w)) u) =
      g u * (((u : ℝ) : ℂ) ^ (-w) *
        ∑ k ∈ Finset.Icc 1 ⌊T / u⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w)) := by
  by_cases hz : g u = 0
  · simp [Set.indicator_apply, hz]
  · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
    have hub : b ≤ u := hmem.1
    have hMK : ⌊T / u⌋₊ ≤ ⌊T / b⌋₊ := Nat.floor_le_floor (by gcongr)
    have hsub : Finset.Icc 1 ⌊T / u⌋₊ ⊆ Finset.Icc 1 ⌊T / b⌋₊ :=
      Finset.Icc_subset_Icc le_rfl hMK
    have hzero : ∀ k ∈ Finset.Icc 1 ⌊T / b⌋₊, k ∉ Finset.Icc 1 ⌊T / u⌋₊ →
        (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
          (Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ))).indicator
            (fun v : ℝ => g v * ((v : ℝ) : ℂ) ^ (-w)) u = 0 := by
      intro k hk hknot
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hnot : ¬ (k ≤ ⌊T / u⌋₊) := fun hle => hknot (Finset.mem_Icc.mpr ⟨hk1, hle⟩)
      have : u ∉ Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)) := by
        intro hmem2
        exact hnot ((mem_Ioc_div_iff_le_floor hT hu hk1).mp hmem2)
      rw [Set.indicator_of_notMem this, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    have hval : ∀ k ∈ Finset.Icc 1 ⌊T / u⌋₊,
        (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
          (Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ))).indicator
            (fun v : ℝ => g v * ((v : ℝ) : ℂ) ^ (-w)) u =
          (((k : ℕ) : ℝ) : ℂ) ^ (-w) * (g u * ((u : ℝ) : ℂ) ^ (-w)) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      rw [Set.indicator_of_mem ((mem_Ioc_div_iff_le_floor hT hu hk1).mpr hk2)]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
    ring

/-- The finite sum of truncated seed integrals is a single integral against the truncated kernel. -/
theorem sum_integral_Ioc_eq_integral_kernel {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) {T : ℝ} (hT : 0 < T) :
    (∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
        ∫ u in Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)), g u * ((u : ℝ) : ℂ) ^ (-w)) =
      ∫ u in Ioi (0 : ℝ), g u *
        (((u : ℝ) : ℂ) ^ (-w) * ∑ k ∈ Finset.Icc 1 ⌊T / u⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w)) := by
  have hbase : Integrable (fun y : ℝ => g y * ((y : ℝ) : ℂ) ^ (-w)) :=
    integrable_seed_mul_cpow hb hg hsupp hw0
  have hterm : ∀ k ∈ Finset.Icc 1 ⌊T / b⌋₊,
      (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
          (∫ u in Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)), g u * ((u : ℝ) : ℂ) ^ (-w)) =
        ∫ u in Ioi (0 : ℝ), (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
          (Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ))).indicator
            (fun v : ℝ => g v * ((v : ℝ) : ℂ) ^ (-w)) u := by
    intro k hk
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)) =
        Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ)) :=
      Set.inter_eq_self_of_subset_right (fun x hx => mem_Ioi.mpr hx.1)
    rw [MeasureTheory.integral_const_mul, setIntegral_indicator measurableSet_Ioc, hset]
  rw [Finset.sum_congr rfl hterm]
  rw [← MeasureTheory.integral_finsetSum]
  · refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact sum_indicator_cpow_eq hb hsupp hT (mem_Ioi.mp hu)
  · intro k hk
    exact ((hbase.indicator measurableSet_Ioc).const_mul _).restrict


theorem integrableOn_Ioc_cpow_neg {w : ℂ} (hw1 : w.re < 1) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-w)) (Ioc (0 : ℝ) T) := by
  have h := intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ)) (b := T) (r := -w)
    (by rw [Complex.neg_re]; linarith)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp h

theorem integral_Ioc_cpow_eq {w : ℂ} (hw1 : w.re < 1) {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc (0 : ℝ) T, ((t : ℝ) : ℂ) ^ (-w)) = ((T : ℝ) : ℂ) ^ (1 - w) / (1 - w) := by
  have hre : (-1 : ℝ) < (-w).re := by rw [Complex.neg_re]; linarith
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [← intervalIntegral.integral_of_le hT.le, integral_cpow (Or.inl hre)]
  rw [Complex.ofReal_zero, Complex.zero_cpow (by rw [show (-w + 1 : ℂ) = 1 - w by ring]; exact hne)]
  rw [show (-w + 1 : ℂ) = 1 - w by ring, sub_zero]

theorem integrableOn_coPoissonSum_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) (T : ℝ) :
    IntegrableOn (fun t : ℝ =>
      (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((m + 1 : ℕ) : ℝ))) *
        ((t : ℝ) : ℂ) ^ (-w)) (Ioc (0 : ℝ) T) := by
  have hfin : IntegrableOn (fun t : ℝ =>
      ∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊,
        ((((k : ℕ) : ℝ)) : ℂ)⁻¹ * g (t / ((k : ℕ) : ℝ)) * ((t : ℝ) : ℂ) ^ (-w))
      (Ioc (0 : ℝ) T) := by
    refine integrable_finsetSum _ fun k hk => ?_
    exact (integrable_seed_dilate_cpow hb hg hsupp hw0 (Finset.mem_Icc.mp hk).1).restrict
  refine hfin.congr_fun (fun t ht => ?_) measurableSet_Ioc
  rw [coPoissonSum_eq_fixed_finset_sum hb hsupp ht.1 ht.2, Finset.sum_mul]

theorem integrableOn_seed_mul_windowSum {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun u : ℝ => g u *
      (((u : ℝ) : ℂ) ^ (-w) * ∑ k ∈ Finset.Icc 1 ⌊T / u⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w)))
      (Ioi (0 : ℝ)) := by
  have hbase : Integrable (fun y : ℝ => g y * ((y : ℝ) : ℂ) ^ (-w)) :=
    integrable_seed_mul_cpow hb hg hsupp hw0
  have hfin : IntegrableOn (fun u : ℝ =>
      ∑ k ∈ Finset.Icc 1 ⌊T / b⌋₊, (((k : ℕ) : ℝ) : ℂ) ^ (-w) *
        (Set.Ioc (0 : ℝ) (T / ((k : ℕ) : ℝ))).indicator
          (fun v : ℝ => g v * ((v : ℝ) : ℂ) ^ (-w)) u) (Ioi (0 : ℝ)) := by
    refine integrable_finsetSum _ fun k hk => ?_
    exact ((hbase.indicator measurableSet_Ioc).const_mul _).restrict
  refine hfin.congr_fun (fun u hu => ?_) measurableSet_Ioi
  exact sum_indicator_cpow_eq hb hsupp hT (mem_Ioi.mp hu)

/-- **The truncated Mellin integral of the co-Poisson sum.**  No interchange of an infinite sum with
an integral occurs: below the cutoff only finitely many indices contribute. -/
theorem integral_Ioc_burnolCoPoisson_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re < 1)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioc (0 : ℝ) T, burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w)) =
      ∫ u in Ioi (0 : ℝ), g u * coPoissonMellinKernel w T u := by
  have hlog : IntegrableOn (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u) (Ioi (0 : ℝ)) :=
    integrableOn_logMass_of_window_seed hb hg hsupp
  have hsplit : ∀ t ∈ Ioc (0 : ℝ) T,
      burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w) =
        (∑' m : ℕ, (((m + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((m + 1 : ℕ) : ℝ))) *
            ((t : ℝ) : ℂ) ^ (-w) -
          coPoissonCorrectionConstant g * ((t : ℝ) : ℂ) ^ (-w) := by
    intro t ht
    rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos ht.1, sub_mul]
  rw [setIntegral_congr_fun measurableSet_Ioc hsplit]
  rw [MeasureTheory.integral_sub (integrableOn_coPoissonSum_cpow hb hg hsupp hw0 T)]
  · rw [integral_Ioc_coPoissonSum_cpow hb hg hsupp hw0 hT,
      sum_integral_Ioc_eq_integral_kernel hb hg hsupp hw0 hT,
      MeasureTheory.integral_const_mul, integral_Ioc_cpow_eq hw1 hT]
    have hcorr : coPoissonCorrectionConstant g * (((T : ℝ) : ℂ) ^ (1 - w) / (1 - w)) =
        ∫ u in Ioi (0 : ℝ), g u * (((u : ℝ) : ℂ)⁻¹ * (((T : ℝ) : ℂ) ^ (1 - w) / (1 - w))) := by
      rw [coPoissonCorrectionConstant_eq_logMass, ← MeasureTheory.integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      ring
    rw [hcorr, ← MeasureTheory.integral_sub
      (integrableOn_seed_mul_windowSum hb hg hsupp hw0 hT)
      (by
        have h2 := hlog.mul_const ((((T : ℝ) : ℂ) ^ (1 - w) / (1 - w)))
        exact h2.congr (Filter.Eventually.of_forall (fun u => by ring)))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [coPoissonMellinKernel]
    ring
  · exact (integrableOn_Ioc_cpow_neg hw1 hT).const_mul _



theorem iUnion_Ioc_natCast : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi (0 : ℝ) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn, -⟩
    exact hn
  · intro hx
    exact ⟨⌈x⌉₊, hx, Nat.le_ceil x⟩

theorem integrableOn_seed_mul_coPoissonMellinKernel {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 ≤ w.re)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun u : ℝ => g u * coPoissonMellinKernel w T u) (Ioi (0 : ℝ)) := by
  have h1 := integrableOn_seed_mul_windowSum hb hg hsupp hw0 hT
  have hlog := integrableOn_logMass_of_window_seed hb hg hsupp
  have h2 : IntegrableOn
      (fun u : ℝ => g u * (((u : ℝ) : ℂ)⁻¹ * (((T : ℝ) : ℂ) ^ (1 - w) / (1 - w))))
      (Ioi (0 : ℝ)) := by
    have h3 := hlog.mul_const ((((T : ℝ) : ℂ) ^ (1 - w) / (1 - w)))
    exact h3.congr (Filter.Eventually.of_forall fun u => by ring)
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.sub_apply, coPoissonMellinKernel]
  ring

theorem norm_seed_mul_coPoissonMellinKernel_le {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 < w.re) (hw : w ≠ 1)
    {E : ℝ} (hE : ∀ N : ℕ, ‖zetaStripError w N‖ ≤ E)
    {T : ℝ} (hT : 0 < T) (hTb : (‖1 - w‖ + 1) * b⁻¹ ≤ T) (u : ℝ) :
    ‖g u * coPoissonMellinKernel w T u‖ ≤
      b ^ (-w.re) * (E + 2 + ‖riemannZeta w‖) * ‖g u‖ := by
  by_cases hz : g u = 0
  · rw [hz]
    simp
  · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hb hmem.1
    have hub : u ≤ b⁻¹ := hmem.2
    have hTu : ‖1 - w‖ + 1 ≤ T / u := by
      rw [le_div_iff₀ hupos]
      calc (‖1 - w‖ + 1) * u ≤ (‖1 - w‖ + 1) * b⁻¹ :=
            mul_le_mul_of_nonneg_left hub (by positivity)
        _ ≤ T := hTb
    have hupow : u ^ (-w.re) ≤ b ^ (-w.re) :=
      Real.rpow_le_rpow_of_nonpos hb hmem.1 (by linarith)
    have hnormz : ‖riemannZeta w * ((u : ℝ) : ℂ) ^ (-w)‖ = ‖riemannZeta w‖ * u ^ (-w.re) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hupos, Complex.neg_re]
    have hbound := norm_coPoissonMellinKernel_sub_le_const hw (le_of_lt hw0) hupos hT hTu hE
    have hk : ‖coPoissonMellinKernel w T u‖ ≤ u ^ (-w.re) * (E + 2 + ‖riemannZeta w‖) := by
      have hadd := norm_add_le
        (coPoissonMellinKernel w T u - riemannZeta w * ((u : ℝ) : ℂ) ^ (-w))
        (riemannZeta w * ((u : ℝ) : ℂ) ^ (-w))
      rw [sub_add_cancel, hnormz] at hadd
      have hrw : u ^ (-w.re) * (E + 2 + ‖riemannZeta w‖)
          = u ^ (-w.re) * (E + 2) + ‖riemannZeta w‖ * u ^ (-w.re) := by ring
      rw [hrw]
      linarith [hbound]
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hE 0)
    have hcoef : (0 : ℝ) ≤ E + 2 + ‖riemannZeta w‖ := by positivity
    rw [norm_mul, mul_comm ‖g u‖]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖coPoissonMellinKernel w T u‖ ≤ u ^ (-w.re) * (E + 2 + ‖riemannZeta w‖) := hk
      _ ≤ b ^ (-w.re) * (E + 2 + ‖riemannZeta w‖) :=
          mul_le_mul_of_nonneg_right hupow hcoef


/-- **The Mellin transform of the co-Poisson sum of a general window seed.**
`M(P_g)(w) = zeta(w) M(g)(w)` on the critical strip, for every integrable seed supported in
`[b, 1/b]` whose co-Poisson sum is Mellin integrable. -/
theorem integral_Ioi_burnolCoPoisson_cpow {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g)
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hint : IntegrableOn
      (fun t : ℝ => burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w)) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ), burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w)) =
      riemannZeta w * ∫ u in Ioi (0 : ℝ), g u * ((u : ℝ) : ℂ) ^ (-w) := by
  have hwne : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    exact lt_irrefl 1 hw1
  obtain ⟨E, hE0, hE⟩ := exists_bound_zetaStripError hw0 hwne
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) (n : ℝ)) := by
    intro m n hmn
    exact Ioc_subset_Ioc_right (by exact_mod_cast hmn)
  have hL : Tendsto (fun n : ℕ => ∫ t in Ioc (0 : ℝ) (n : ℝ),
      burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w)) atTop
      (nhds (∫ t in Ioi (0 : ℝ), burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w))) := by
    have h := tendsto_setIntegral_of_monotone (fun n : ℕ => measurableSet_Ioc) hmono
      (by rw [iUnion_Ioc_natCast]; exact hint)
    rw [iUnion_Ioc_natCast] at h
    exact h
  have hR : Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ), g u * coPoissonMellinKernel w (n : ℝ) u)
      atTop (nhds (∫ u in Ioi (0 : ℝ), g u * (riemannZeta w * ((u : ℝ) : ℂ) ^ (-w)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => b ^ (-w.re) * (E + 2 + ‖riemannZeta w‖) * ‖g u‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact (integrableOn_seed_mul_coPoissonMellinKernel hb hg hsupp hw0.le
        hnpos).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (⌈(‖1 - w‖ + 1) * b⁻¹⌉₊ + 1)] with n hn
      have hn1 : (1 : ℕ) ≤ n := le_trans (Nat.le_add_left 1 _) hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hceil : ((⌈(‖1 - w‖ + 1) * b⁻¹⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hTb : (‖1 - w‖ + 1) * b⁻¹ ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by linarith)
      exact Filter.Eventually.of_forall
        (norm_seed_mul_coPoissonMellinKernel_le hb hsupp hw0 hwne hE hnpos hTb)
    · exact (hg.norm.const_mul _).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (tendsto_coPoissonMellinKernel hw0 hwne (mem_Ioi.mp hu)).const_mul (g u)
  have heq : ∀ᶠ n : ℕ in atTop,
      (∫ t in Ioc (0 : ℝ) (n : ℝ), burnolCoPoissonRightSum g t * ((t : ℝ) : ℂ) ^ (-w)) =
        ∫ u in Ioi (0 : ℝ), g u * coPoissonMellinKernel w (n : ℝ) u := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact integral_Ioc_burnolCoPoisson_cpow hb hg hsupp hw0.le hw1 hnpos
  have hfinal := tendsto_nhds_unique (hL.congr' heq) hR
  rw [hfinal, ← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring



/-- **The completed Mellin evaluation of any co-Poisson source vector.**  It is the zeta factor
times the Mellin transform of the seed. -/
theorem soninMellinEvaluation_burnolCoPoissonSource {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) :
    soninMellinEvaluation w (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) =
      mellinCompletionFactor w *
        (riemannZeta w * ∫ u in Ioi (0 : ℝ), src.seed u * ((u : ℝ) : ℂ) ^ (-w)) := by
  have hw0 : (0 : ℝ) < w.re := by linarith
  have hae := src.vector_eq_sum
  have hintv := integrableOn_extendedSonin_mul_mellinKernel hlo hhi hb src.vector
  have hint : IntegrableOn
      (fun t : ℝ => burnolCoPoissonRightSum src.seed t * ((t : ℝ) : ℂ) ^ (-w)) (Ioi (0 : ℝ)) := by
    refine hintv.congr ?_
    filter_upwards [ae_restrict_of_ae hae] with t ht
    rw [ht, soninMellinKernel]
  rw [soninMellinEvaluation]
  congr 1
  have heq : (∫ t in Ioi (0 : ℝ),
      (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) t *
        soninMellinKernel w t) =
      ∫ t in Ioi (0 : ℝ), burnolCoPoissonRightSum src.seed t * ((t : ℝ) : ℂ) ^ (-w) := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [hae] with t ht
    intro _
    rw [ht, soninMellinKernel]
  rw [heq]
  exact integral_Ioi_burnolCoPoisson_cpow hb src.seed_integrable src.seed_support hw0 hhi hint

/-- At a zero of zeta the completed Mellin evaluation annihilates every co-Poisson source vector. -/
theorem soninMellinEvaluation_burnolCoPoissonSource_eq_zero {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) :
    soninMellinEvaluation w (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) = 0 := by
  rw [soninMellinEvaluation_burnolCoPoissonSource hb src hlo hhi, hz]
  simp

/-- **At a zeta zero the Riesz evaluator is orthogonal to every co-Poisson source vector.** -/
theorem inner_burnolExtendedSoninEvaluationVector_source_eq_zero {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) :
    ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, src.vector⟫_ℂ = 0 := by
  rw [inner_burnolExtendedSoninEvaluationVector]
  exact soninMellinEvaluation_burnolCoPoissonSource_eq_zero hb src hlo hhi hz

/-- Off the zero set of zeta a co-Poisson source vector is detected by the evaluator as soon as its
seed has nonvanishing Mellin transform. -/
theorem soninMellinEvaluation_burnolCoPoissonSource_ne_zero {b : ℝ} (hb : 0 < b)
    (src : BurnolCoPoissonSource b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w ≠ 0)
    (hm : (∫ u in Ioi (0 : ℝ), src.seed u * ((u : ℝ) : ℂ) ^ (-w)) ≠ 0) :
    soninMellinEvaluation w (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) ≠ 0 := by
  rw [soninMellinEvaluation_burnolCoPoissonSource hb src hlo hhi]
  exact mul_ne_zero (mellinCompletionFactor_ne_zero (by linarith)) (mul_ne_zero hz hm)

end RHTower
