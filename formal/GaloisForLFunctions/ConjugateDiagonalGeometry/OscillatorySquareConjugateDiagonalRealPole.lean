import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# Exponential-floor shielding and conjugate-diagonal real poles of oscillatory waves

Landau's oscillation theorem forces a real singularity at the abscissa of convergence for the
Laplace transform of a nonnegative function, whereas a pure oscillatory wave
`W(u) = Σ_{j ∈ F} (c_j e^{(β + i γ_j) u} + c̄_j e^{(β - i γ_j) u})` (`γ_j ≠ 0`) has only nonreal
poles on `Re s = β` and zero residue at the real point `s = β`. Two distinct mechanisms reconcile
nonnegativity with oscillatory complex poles:

1. **Exponential-floor real-pole shielding** (`expBufferedWave_nonneg`,
   `laplace_expBufferedWave_eq`, `tendsto_sub_mul_laplace_expBufferedWave`): adding an exponential
   floor `C e^{α u}` (`β ≤ α`, `2 Σ_{j ∈ F} ‖c_j‖ ≤ C`) makes `C e^{α u} + Re W(u) ≥ 0` on
   `[0, ∞)` and creates a real simple pole `C / (s - α)` at `s = α` of residue `C` that shields the
   complex poles `β ± i γ_j`.
2. **Conjugate-diagonal real-pole creation under squaring** (`conjSymWaveLaplace_residue_zero`,
   `conjSymWave_sq_eq`, `laplace_conjSymWave_sq_eq`, `tendsto_sub_mul_laplace_conjSymWave_sq`,
   `conjDiagResidue_pos_of_exists_ne_zero`): for distinct positive ordinates `γ_j > 0`, squaring the
   sign-changing real wave `W(u)` pairs each mode `β + i γ_j` with its conjugate `β - i γ_j` into
   the strictly real exponential `2 (Σ_{j ∈ F} ‖c_j‖²) e^{2 β u}`, while every off-diagonal pair has
   nonzero imaginary frequency `±(γ_j + γ_k)` or `±(γ_j - γ_k)` (`j ≠ k`). The Laplace transform of
   `W(u)² ≥ 0` on `Re s > 2 β` therefore acquires a real simple pole at `s = 2 β` of strictly
   positive residue `2 Σ_{j ∈ F} ‖c_j‖² > 0`.
-/

open Complex Finset MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry (integrableOn_cexp_neg_mul integral_cexp_neg_mul)

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

variable {ι : Type*}

/-! ### Shifted complex Laplace exponential ray -/

theorem integrableOn_Ioi_cexp_shift {s z : ℂ} (h : z.re < s.re) (a : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * (a * Complex.exp (z * (u : ℂ))))
      (Ioi (0 : ℝ)) := by
  have hre : 0 < (s - z).re := by simp [sub_pos.mpr h]
  have heq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * (a * Complex.exp (z * (u : ℂ)))) =
      fun u : ℝ => a * Complex.exp (-((s - z) * (u : ℂ))) := by
    funext u
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  rw [heq]
  exact (integrableOn_cexp_neg_mul hre).const_mul a

theorem integral_Ioi_cexp_shift {s z : ℂ} (h : z.re < s.re) (a : ℂ) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) * (a * Complex.exp (z * (u : ℂ)))) =
      a / (s - z) := by
  have hre : 0 < (s - z).re := by simp [sub_pos.mpr h]
  have heq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * (a * Complex.exp (z * (u : ℂ)))) =
      fun u : ℝ => a * Complex.exp (-((s - z) * (u : ℂ))) := by
    funext u
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_cexp_neg_mul hre, mul_one_div]

/-! ### Conjugate-symmetric oscillatory waves and exponential-floor shielding -/

/-- Conjugate-symmetric finite oscillatory wave
`W(u) = Σ_{j ∈ F} (c_j e^{(β + i γ_j) u} + c̄_j e^{(β - i γ_j) u})`. -/
def conjSymWave (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ j ∈ F,
    (c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ))) +
      starRingEnd ℂ (c j) * Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ))))

theorem conjSymWave_conj (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    starRingEnd ℂ (conjSymWave F c β γ u) = conjSymWave F c β γ u := by
  unfold conjSymWave
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_mul, map_mul, Complex.conj_conj, ← Complex.exp_conj, ← Complex.exp_conj]
  have e1 : starRingEnd ℂ ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ))) =
      (((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ)) := by simp
  have e2 : starRingEnd ℂ ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ))) =
      (((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)) := by simp
  rw [e1, e2, add_comm]

theorem conjSymWave_im_eq_zero (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    (conjSymWave F c β γ u).im = 0 :=
  Complex.conj_eq_iff_im.mp (conjSymWave_conj F c β γ u)

theorem conjSymWave_eq_ofReal_re (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    conjSymWave F c β γ u = ((conjSymWave F c β γ u).re : ℂ) :=
  Complex.ext rfl (by simp [conjSymWave_im_eq_zero])

theorem conjSymWave_re_eq_sum (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    (conjSymWave F c β γ u).re =
      ∑ j ∈ F, 2 * (c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))).re := by
  unfold conjSymWave
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconj : starRingEnd ℂ (c j) * Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ))) =
      starRingEnd ℂ (c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp
  rw [hconj, Complex.add_re, Complex.conj_re]
  ring

theorem norm_conjSymWave_le (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    ‖conjSymWave F c β γ u‖ ≤ (2 * ∑ j ∈ F, ‖c j‖) * Real.exp (β * u) := by
  unfold conjSymWave
  refine (norm_sum_le _ _).trans ?_
  rw [ two_mul, add_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))‖ = Real.exp (β * u) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ)))‖ = Real.exp (β * u) := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, norm_mul, Complex.norm_conj, h1, h2]

/-- **Exponential-floor nonnegativity.** Whenever `β ≤ α` and `2 Σ_{j ∈ F} ‖c_j‖ ≤ C`, adding the
real exponential floor `C e^{α u}` keeps `C e^{α u} + Re W(u) ≥ 0` on `[0, ∞)`. -/
theorem expBufferedWave_nonneg {F : Finset ι} {c : ι → ℂ} {β α C : ℝ} {γ : ι → ℝ}
    (hβα : β ≤ α) (hC : 2 * ∑ j ∈ F, ‖c j‖ ≤ C) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ C * Real.exp (α * u) + (conjSymWave F c β γ u).re := by
  have habs : |(conjSymWave F c β γ u).re| ≤ C * Real.exp (α * u) := by
    calc |(conjSymWave F c β γ u).re|
        ≤ ‖conjSymWave F c β γ u‖ := Complex.abs_re_le_norm _
      _ ≤ (2 * ∑ j ∈ F, ‖c j‖) * Real.exp (β * u) := norm_conjSymWave_le F c β γ u
      _ ≤ C * Real.exp (β * u) := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ C * Real.exp (α * u) := by
        have hC0 : 0 ≤ C := le_trans (mul_nonneg zero_le_two
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)) hC
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβα hu)) hC0
  linarith [neg_abs_le (conjSymWave F c β γ u).re]

/-- Rational Laplace continuation of `conjSymWave`. -/
def conjSymWaveLaplace (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ F,
    (c j / (s - ((β : ℂ) + Complex.I * (γ j : ℂ))) +
      starRingEnd ℂ (c j) / (s - ((β : ℂ) - Complex.I * (γ j : ℂ))))

theorem integrableOn_Ioi_cexp_mul_conjSymWave {F : Finset ι} {c : ι → ℂ} {β : ℝ} {γ : ι → ℝ}
    {s : ℂ} (hs : β < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * conjSymWave F c β γ u)
      (Ioi (0 : ℝ)) := by
  have heq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * conjSymWave F c β γ u) =
      fun u : ℝ => ∑ j ∈ F,
        (Complex.exp (-(s * (u : ℂ))) *
            (c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))) +
          Complex.exp (-(s * (u : ℂ))) *
            (starRingEnd ℂ (c j) * Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ))))) := by
    funext u
    unfold conjSymWave
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_add _ _ _
  rw [heq]
  refine integrable_finsetSum F fun j _ => ?_
  exact (integrableOn_Ioi_cexp_shift (by simpa using hs) (c j)).add
    (integrableOn_Ioi_cexp_shift (by simpa using hs) (starRingEnd ℂ (c j)))

theorem laplace_conjSymWave_eq {F : Finset ι} {c : ι → ℂ} {β : ℝ} {γ : ι → ℝ}
    {s : ℂ} (hs : β < s.re) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) * conjSymWave F c β γ u) =
      conjSymWaveLaplace F c β γ s := by
  have heq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * conjSymWave F c β γ u) =
      fun u : ℝ => ∑ j ∈ F,
        (Complex.exp (-(s * (u : ℂ))) *
            (c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))) +
          Complex.exp (-(s * (u : ℂ))) *
            (starRingEnd ℂ (c j) * Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ))))) := by
    funext u
    unfold conjSymWave
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_add _ _ _
  rw [heq, integral_finsetSum F fun j _ =>
    (integrableOn_Ioi_cexp_shift (by simpa using hs) (c j)).add
      (integrableOn_Ioi_cexp_shift (by simpa using hs) (starRingEnd ℂ (c j)))]
  unfold conjSymWaveLaplace
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi1 := integrableOn_Ioi_cexp_shift (z := (β : ℂ) + Complex.I * (γ j : ℂ))
    (by simpa using hs) (c j)
  have hi2 := integrableOn_Ioi_cexp_shift (z := (β : ℂ) - Complex.I * (γ j : ℂ))
    (by simpa using hs) (starRingEnd ℂ (c j))
  rw [integral_add hi1 hi2,
    integral_Ioi_cexp_shift (z := (β : ℂ) + Complex.I * (γ j : ℂ)) (by simpa using hs) (c j),
    integral_Ioi_cexp_shift (z := (β : ℂ) - Complex.I * (γ j : ℂ)) (by simpa using hs)
      (starRingEnd ℂ (c j))]

/-- **Laplace transform of the exponential-buffered wave.** On `Re s > α` (`β ≤ α`), the Laplace
transform equals `C / (s - α)` plus the complex conjugate-pair poles at `β ± i γ_j`. -/
theorem laplace_expBufferedWave_eq {F : Finset ι} {c : ι → ℂ} {β α C : ℝ} {γ : ι → ℝ}
    (hβα : β ≤ α) {s : ℂ} (hs : α < s.re) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) *
        (((C * Real.exp (α * u) : ℝ) : ℂ) + conjSymWave F c β γ u)) =
      (C : ℂ) / (s - (α : ℂ)) + conjSymWaveLaplace F c β γ s := by
  have hβs : β < s.re := lt_of_le_of_lt hβα hs
  have hfloor_eq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * ((C * Real.exp (α * u) : ℝ) : ℂ)) =
      fun u : ℝ => Complex.exp (-(s * (u : ℂ))) *
        ((C : ℂ) * Complex.exp ((α : ℂ) * (u : ℂ))) := by
    funext u
    push_cast
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  have hi_floor : IntegrableOn
      (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * ((C * Real.exp (α * u) : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
    rw [hfloor_eq]
    exact integrableOn_Ioi_cexp_shift (by simpa using hs) (C : ℂ)
  have hi_wave := integrableOn_Ioi_cexp_mul_conjSymWave (F := F) (c := c) (γ := γ) hβs
  have hadd : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) *
        (((C * Real.exp (α * u) : ℝ) : ℂ) + conjSymWave F c β γ u)) =
      fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * ((C * Real.exp (α * u) : ℝ) : ℂ) +
        Complex.exp (-(s * (u : ℂ))) * conjSymWave F c β γ u := by
    funext u; ring
  rw [hadd, integral_add hi_floor hi_wave, hfloor_eq,
    integral_Ioi_cexp_shift (z := (α : ℂ)) (by simpa using hs) (C : ℂ),
    laplace_conjSymWave_eq hβs]

theorem continuousAt_conjSymWaveLaplace_of_poles_off_real {F : Finset ι} {c : ι → ℂ}
    {β α : ℝ} {γ : ι → ℝ} (hpoles : ∀ j ∈ F, β = α → γ j ≠ 0) :
    ContinuousAt (conjSymWaveLaplace F c β γ) (α : ℂ) := by
  unfold conjSymWaveLaplace
  refine continuousAt_finset_sum F fun j hj => ?_
  have hne_pos : (α : ℂ) - ((β : ℂ) + Complex.I * (γ j : ℂ)) ≠ 0 := by
    intro h0
    have hre : α - β = 0 := by simpa using congrArg Complex.re h0
    have him : -(γ j) = 0 := by simpa using congrArg Complex.im h0
    exact hpoles j hj (by linarith) (by linarith)
  have hne_neg : (α : ℂ) - ((β : ℂ) - Complex.I * (γ j : ℂ)) ≠ 0 := by
    intro h0
    have hre : α - β = 0 := by simpa using congrArg Complex.re h0
    have him : γ j = 0 := by simpa using congrArg Complex.im h0
    exact hpoles j hj (by linarith) him
  exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne_pos).add
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne_neg)

/-- **Exponential-floor real-pole shielding.** As `s → α` from `Re s > α`, the real pole residue of
the buffered wave equals `C`, completely absorbing the oscillatory poles `β ± i γ_j`. -/
theorem tendsto_sub_mul_laplace_expBufferedWave {F : Finset ι} {c : ι → ℂ} {β α C : ℝ} {γ : ι → ℝ}
    (hβα : β ≤ α) (hpoles : ∀ j ∈ F, β = α → γ j ≠ 0) :
    Tendsto (fun s : ℂ => (s - (α : ℂ)) *
        ∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) *
          (((C * Real.exp (α * u) : ℝ) : ℂ) + conjSymWave F c β γ u))
      (𝓝[{s : ℂ | α < s.re}] (α : ℂ)) (𝓝 (C : ℂ)) := by
  have hcont := continuousAt_conjSymWaveLaplace_of_poles_off_real (c := c) hpoles
  have hlim : Tendsto (fun s : ℂ => (C : ℂ) + (s - (α : ℂ)) * conjSymWaveLaplace F c β γ s)
      (𝓝 (α : ℂ)) (𝓝 (C : ℂ)) := by
    have h0 : Tendsto (fun s : ℂ => (s - (α : ℂ)) * conjSymWaveLaplace F c β γ s)
        (𝓝 (α : ℂ)) (𝓝 ((0 : ℂ) * conjSymWaveLaplace F c β γ (α : ℂ))) := by
      refine Tendsto.mul ?_ hcont.tendsto
      simpa using (continuous_id.sub continuous_const).tendsto (α : ℂ)
    simpa using tendsto_const_nhds.add h0
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs_ne : s - (α : ℂ) ≠ 0 := by
    intro h0
    have : s.re - α = 0 := by simpa using congrArg Complex.re h0
    linarith [ show α < s.re from hs ]
  rw [laplace_expBufferedWave_eq hβα hs, mul_add, mul_div_cancel₀ _ hs_ne]

/-! ### Conjugate-diagonal real-pole creation under squaring -/

/-- **Zero real-axis residue of the unsquared oscillatory wave.** When every `γ_j ≠ 0`, `L_W(s)` is
continuous at `s = β` and `(s - β) L_W(s) → 0` as `s → β`. -/
theorem conjSymWaveLaplace_residue_zero {F : Finset ι} {c : ι → ℂ} {β : ℝ} {γ : ι → ℝ}
    (hγ : ∀ j ∈ F, γ j ≠ 0) :
    Tendsto (fun s : ℂ => (s - (β : ℂ)) * conjSymWaveLaplace F c β γ s)
      (𝓝 (β : ℂ)) (𝓝 0) := by
  have hcont := continuousAt_conjSymWaveLaplace_of_poles_off_real (c := c) (α := β)
    (fun j hj _ => hγ j hj)
  have h0 : Tendsto (fun s : ℂ => (s - (β : ℂ)) * conjSymWaveLaplace F c β γ s)
      (𝓝 (β : ℂ)) (𝓝 ((0 : ℂ) * conjSymWaveLaplace F c β γ (β : ℂ))) := by
    refine Tendsto.mul ?_ hcont.tendsto
    simpa using (continuous_id.sub continuous_const).tendsto (β : ℂ)
  simpa using h0

/-- **Exact conjugate-diagonal square decomposition.** Squaring `conjSymWave` isolates the strictly
real exponential `2 (Σ_{j ∈ F} ‖c_j‖²) e^{2 β u}` from all off-diagonal oscillatory pairs. -/
theorem conjSymWave_sq_eq [DecidableEq ι] (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ) (u : ℝ) :
    (conjSymWave F c β γ u) ^ 2 =
      ((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * (β : ℂ)) * (u : ℂ))) +
        (∑ j ∈ F, ∑ k ∈ F,
          (c j * c k * Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ))) +
            starRingEnd ℂ (c j * c k) *
              Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ))))) +
        ∑ j ∈ F, ∑ k ∈ F.erase j,
          (c j * starRingEnd ℂ (c k) *
              Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ))) +
            starRingEnd ℂ (c j) * c k *
              Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ)))) := by
  set a : ι → ℂ := fun j => c j * Complex.exp ((((β : ℂ) + Complex.I * (γ j : ℂ)) * (u : ℂ)))
  set b : ι → ℂ := fun j =>
    starRingEnd ℂ (c j) * Complex.exp ((((β : ℂ) - Complex.I * (γ j : ℂ)) * (u : ℂ)))
  have hpair_aa : ∀ j k, a j * a k =
      c j * c k * Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ))) := by
    intro j k
    simp only [a]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hpair_bb : ∀ j k, b j * b k =
      starRingEnd ℂ (c j * c k) *
        Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ))) := by
    intro j k
    simp only [b, map_mul]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hpair_ab : ∀ j k, a j * b k =
      c j * starRingEnd ℂ (c k) *
        Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ))) := by
    intro j k
    simp only [a, b]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hpair_ba : ∀ j k, b j * a k =
      starRingEnd ℂ (c j) * c k *
        Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ))) := by
    intro j k
    simp only [a, b]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hdiag : ∀ j, a j * b j + b j * a j =
      2 * ((‖c j‖ ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * (β : ℂ)) * (u : ℂ))) := by
    intro j
    rw [hpair_ab, hpair_ba, sub_self, Complex.ofReal_zero, mul_zero, add_zero, sub_zero,
      mul_comm (starRingEnd ℂ (c j)) (c j), ← two_mul, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    ring
  have hsq : (conjSymWave F c β γ u) ^ 2 =
      (∑ j ∈ F, ∑ k ∈ F, (a j * a k + b j * b k)) +
        ∑ j ∈ F, ∑ k ∈ F, (a j * b k + b j * a k) := by
    unfold conjSymWave
    change (∑ j ∈ F, (a j + b j)) ^ 2 = _
    rw [sq, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : (∑ j ∈ F, ∑ k ∈ F, (a j * b k + b j * a k)) =
      ((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * (β : ℂ)) * (u : ℂ))) +
        ∑ j ∈ F, ∑ k ∈ F.erase j, (a j * b k + b j * a k) := by
    have h1 : ∀ j ∈ F, (∑ k ∈ F, (a j * b k + b j * a k)) =
        (a j * b j + b j * a j) + ∑ k ∈ F.erase j, (a j * b k + b j * a k) :=
      fun j hj => (Finset.add_sum_erase F (fun k => a j * b k + b j * a k) hj).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    congr 1
    simp_rw [hdiag]
    rw [← Finset.sum_mul]
    push_cast
    rw [Finset.mul_sum]
  rw [hsq, hsplit]
  simp_rw [hpair_aa, hpair_bb, hpair_ab, hpair_ba]
  ring

/-- Off-diagonal rational Laplace transform of `W(u)²` (all poles strictly off the real axis). -/
def conjSymWaveSqOffDiagLaplace [DecidableEq ι] (F : Finset ι) (c : ι → ℂ) (β : ℝ) (γ : ι → ℝ)
    (s : ℂ) : ℂ :=
  (∑ j ∈ F, ∑ k ∈ F,
    ((c j * c k) / (s - ((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ))) +
      starRingEnd ℂ (c j * c k) /
        (s - ((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ))))) +
    ∑ j ∈ F, ∑ k ∈ F.erase j,
      ((c j * starRingEnd ℂ (c k)) /
          (s - ((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ))) +
        (starRingEnd ℂ (c j) * c k) /
          (s - ((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ))))

/-- **Closed-form Laplace transform of the squared oscillatory wave `W(u)²` on `Re s > 2 β`.** -/
theorem laplace_conjSymWave_sq_eq [DecidableEq ι] {F : Finset ι} {c : ι → ℂ} {β : ℝ} {γ : ι → ℝ}
    {s : ℂ} (hs : 2 * β < s.re) :
    (∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) * (conjSymWave F c β γ u) ^ 2) =
      ((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ) / (s - 2 * (β : ℂ)) +
        conjSymWaveSqOffDiagLaplace F c β γ s := by
  have hi_diag := integrableOn_Ioi_cexp_shift (z := 2 * (β : ℂ)) (by simpa using hs)
    ((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ)
  have hi_sum1 : ∀ j ∈ F, ∀ k ∈ F, IntegrableOn (fun u : ℝ =>
      Complex.exp (-(s * (u : ℂ))) *
        (c j * c k * Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ)))) +
      Complex.exp (-(s * (u : ℂ))) *
        (starRingEnd ℂ (c j * c k) *
          Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ)))))
      (Ioi (0 : ℝ)) := fun j _ k _ =>
    (integrableOn_Ioi_cexp_shift (by simpa using hs) (c j * c k)).add
      (integrableOn_Ioi_cexp_shift (by simpa using hs) (starRingEnd ℂ (c j * c k)))
  have hi_sum2 : ∀ j ∈ F, ∀ k ∈ F.erase j, IntegrableOn (fun u : ℝ =>
      Complex.exp (-(s * (u : ℂ))) *
        (c j * starRingEnd ℂ (c k) *
          Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ)))) +
      Complex.exp (-(s * (u : ℂ))) *
        (starRingEnd ℂ (c j) * c k *
          Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ)))))
      (Ioi (0 : ℝ)) := fun j _ k _ =>
    (integrableOn_Ioi_cexp_shift (by simpa using hs) (c j * starRingEnd ℂ (c k))).add
      (integrableOn_Ioi_cexp_shift (by simpa using hs) (starRingEnd ℂ (c j) * c k))
  have hi_off1 : IntegrableOn (fun u : ℝ => ∑ j ∈ F, ∑ k ∈ F,
      (Complex.exp (-(s * (u : ℂ))) *
        (c j * c k * Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ)))) +
      Complex.exp (-(s * (u : ℂ))) *
        (starRingEnd ℂ (c j * c k) *
          Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ))))))
      (Ioi (0 : ℝ)) :=
    integrable_finsetSum F fun j hj => integrable_finsetSum F fun k hk => hi_sum1 j hj k hk
  have hi_off2 : IntegrableOn (fun u : ℝ => ∑ j ∈ F, ∑ k ∈ F.erase j,
      (Complex.exp (-(s * (u : ℂ))) *
        (c j * starRingEnd ℂ (c k) *
          Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ)))) +
      Complex.exp (-(s * (u : ℂ))) *
        (starRingEnd ℂ (c j) * c k *
          Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ))))))
      (Ioi (0 : ℝ)) :=
    integrable_finsetSum F fun j hj =>
      integrable_finsetSum (F.erase j) fun k hk => hi_sum2 j hj k hk
  have heq : (fun u : ℝ => Complex.exp (-(s * (u : ℂ))) * (conjSymWave F c β γ u) ^ 2) =
      fun u : ℝ =>
        Complex.exp (-(s * (u : ℂ))) *
          (((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * (β : ℂ)) * (u : ℂ)))) +
        ((∑ j ∈ F, ∑ k ∈ F,
          (Complex.exp (-(s * (u : ℂ))) *
            (c j * c k *
              Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ)))) +
          Complex.exp (-(s * (u : ℂ))) *
            (starRingEnd ℂ (c j * c k) *
              Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) * (u : ℂ)))))) +
        (∑ j ∈ F, ∑ k ∈ F.erase j,
          (Complex.exp (-(s * (u : ℂ))) *
            (c j * starRingEnd ℂ (c k) *
              Complex.exp ((((2 * (β : ℂ)) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ)))) +
          Complex.exp (-(s * (u : ℂ))) *
            (starRingEnd ℂ (c j) * c k *
              Complex.exp ((((2 * (β : ℂ)) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) * (u : ℂ))))))) := by
    funext u
    rw [conjSymWave_sq_eq]
    simp only [mul_add, Finset.mul_sum]
    ring
  rw [heq, integral_add hi_diag (hi_off1.add hi_off2), integral_add hi_off1 hi_off2,
    integral_Ioi_cexp_shift (z := 2 * (β : ℂ)) (by simpa using hs)]
  congr 1
  unfold conjSymWaveSqOffDiagLaplace
  congr 1
  · rw [integral_finsetSum F fun j hj => integrable_finsetSum F fun k hk => hi_sum1 j hj k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_finsetSum F fun k hk => hi_sum1 j hj k hk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add
      (integrableOn_Ioi_cexp_shift (z := 2 * (β : ℂ) + Complex.I * ((γ j + γ k : ℝ) : ℂ))
        (by simpa using hs) _)
      (integrableOn_Ioi_cexp_shift (z := 2 * (β : ℂ) - Complex.I * ((γ j + γ k : ℝ) : ℂ))
        (by simpa using hs) _),
      integral_Ioi_cexp_shift (z := 2 * (β : ℂ) + Complex.I * ((γ j + γ k : ℝ) : ℂ))
        (by simpa using hs),
      integral_Ioi_cexp_shift (z := 2 * (β : ℂ) - Complex.I * ((γ j + γ k : ℝ) : ℂ))
        (by simpa using hs)]
  · rw [integral_finsetSum F fun j hj =>
      integrable_finsetSum (F.erase j) fun k hk => hi_sum2 j hj k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_finsetSum (F.erase j) fun k hk => hi_sum2 j hj k hk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add
      (integrableOn_Ioi_cexp_shift (z := 2 * (β : ℂ) + Complex.I * ((γ j - γ k : ℝ) : ℂ))
        (by simpa using hs) _)
      (integrableOn_Ioi_cexp_shift (z := 2 * (β : ℂ) - Complex.I * ((γ j - γ k : ℝ) : ℂ))
        (by simpa using hs) _),
      integral_Ioi_cexp_shift (z := 2 * (β : ℂ) + Complex.I * ((γ j - γ k : ℝ) : ℂ))
        (by simpa using hs),
      integral_Ioi_cexp_shift (z := 2 * (β : ℂ) - Complex.I * ((γ j - γ k : ℝ) : ℂ))
        (by simpa using hs)]

/-- When `γ` is positive and injective on `F`, the entire off-diagonal Laplace sum is continuous at
the real point `s = 2 β`. -/
theorem continuousAt_conjSymWaveSqOffDiagLaplace [DecidableEq ι] {F : Finset ι} (c : ι → ℂ)
    (β : ℝ) {γ : ι → ℝ} (hγ_pos : ∀ j ∈ F, 0 < γ j) (hγ_inj : Set.InjOn γ F) :
    ContinuousAt (conjSymWaveSqOffDiagLaplace F c β γ) (2 * (β : ℂ)) := by
  unfold conjSymWaveSqOffDiagLaplace
  refine ContinuousAt.add ?_ ?_
  · refine continuousAt_finset_sum F fun j hj => continuousAt_finset_sum F fun k hk => ?_
    have hsum_pos : 0 < γ j + γ k := add_pos (hγ_pos j hj) (hγ_pos k hk)
    have hne1 : 2 * (β : ℂ) - (2 * (β : ℂ) + Complex.I * ((γ j + γ k : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      have him : -(γ j + γ k) = 0 := by simpa using congrArg Complex.im h0
      linarith
    have hne2 : 2 * (β : ℂ) - (2 * (β : ℂ) - Complex.I * ((γ j + γ k : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      have him : γ j + γ k = 0 := by simpa using congrArg Complex.im h0
      linarith
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne1).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne2)
  · refine continuousAt_finset_sum F fun j hj => continuousAt_finset_sum (F.erase j) fun k hk => ?_
    obtain ⟨hk_ne, hkF⟩ := Finset.mem_erase.mp hk
    have hdiff_ne : γ j - γ k ≠ 0 := sub_ne_zero.mpr fun heq => hk_ne (hγ_inj hj hkF heq).symm
    have hne1 : 2 * (β : ℂ) - (2 * (β : ℂ) + Complex.I * ((γ j - γ k : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      have him : -(γ j - γ k) = 0 := by simpa using congrArg Complex.im h0
      exact hdiff_ne (by linarith)
    have hne2 : 2 * (β : ℂ) - (2 * (β : ℂ) - Complex.I * ((γ j - γ k : ℝ) : ℂ)) ≠ 0 := by
      intro h0
      have him : γ j - γ k = 0 := by simpa using congrArg Complex.im h0
      exact hdiff_ne him
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne1).add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne2)

/-- **Conjugate-diagonal real simple pole residue of `W(u)²`.** As `s → 2 β` from `Re s > 2 β`,
`(s - 2 β) ∫_0^∞ e^{-s u} W(u)² du → 2 Σ_{j ∈ F} ‖c_j‖²`. -/
theorem tendsto_sub_mul_laplace_conjSymWave_sq [DecidableEq ι] {F : Finset ι} {c : ι → ℂ}
    {β : ℝ} {γ : ι → ℝ} (hγ_pos : ∀ j ∈ F, 0 < γ j) (hγ_inj : Set.InjOn γ F) :
    Tendsto (fun s : ℂ => (s - 2 * (β : ℂ)) *
        ∫ u in Ioi (0 : ℝ), Complex.exp (-(s * (u : ℂ))) * (conjSymWave F c β γ u) ^ 2)
      (𝓝[{s : ℂ | 2 * β < s.re}] (2 * (β : ℂ)))
      (𝓝 (((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ))) := by
  have hcont := continuousAt_conjSymWaveSqOffDiagLaplace c β hγ_pos hγ_inj
  have hlim : Tendsto (fun s : ℂ =>
      ((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ) +
        (s - 2 * (β : ℂ)) * conjSymWaveSqOffDiagLaplace F c β γ s)
      (𝓝 (2 * (β : ℂ))) (𝓝 (((2 * ∑ j ∈ F, ‖c j‖ ^ 2 : ℝ) : ℂ))) := by
    have h0 : Tendsto (fun s : ℂ => (s - 2 * (β : ℂ)) * conjSymWaveSqOffDiagLaplace F c β γ s)
        (𝓝 (2 * (β : ℂ)))
        (𝓝 ((0 : ℂ) * conjSymWaveSqOffDiagLaplace F c β γ (2 * (β : ℂ)))) := by
      refine Tendsto.mul ?_ hcont.tendsto
      simpa using (continuous_id.sub continuous_const).tendsto (2 * (β : ℂ))
    simpa using tendsto_const_nhds.add h0
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs_ne : s - 2 * (β : ℂ) ≠ 0 := by
    intro h0
    have : s.re - 2 * β = 0 := by simpa using congrArg Complex.re h0
    linarith [show 2 * β < s.re from hs]
  rw [laplace_conjSymWave_sq_eq hs, mul_add, mul_div_cancel₀ _ hs_ne]

/-- **Strict positivity of the conjugate-diagonal residue.** Whenever at least one mode amplitude
`c_j` (`j ∈ F`) is nonzero, the real pole residue `2 Σ_{j ∈ F} ‖c_j‖²` at `s = 2 β` is strictly
positive. -/
theorem conjDiagResidue_pos_of_exists_ne_zero {F : Finset ι} {c : ι → ℂ}
    (hc : ∃ j ∈ F, c j ≠ 0) :
    0 < 2 * ∑ j ∈ F, ‖c j‖ ^ 2 := by
  obtain ⟨j₀, hj₀, hne⟩ := hc
  have hpos : 0 < ‖c j₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hle : ‖c j₀‖ ^ 2 ≤ ∑ j ∈ F, ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) hj₀
  linarith

end GaloisForLFunctions.ConjugateDiagonalGeometry
