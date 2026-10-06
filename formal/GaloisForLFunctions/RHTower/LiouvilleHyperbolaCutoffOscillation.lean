import GaloisForLFunctions.RHTower.LiouvilleTriangularHeadOscillation
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The cutoff transport law for the Liouville hyperbola decomposition

From `λ = μ ∗ 1_□` the Liouville triangle `P(x) = Σ_{n ≤ x} λ(n)(x/n - 1)` is
`P(x) = Σ_{m ≤ x} μ(m) W(x/m)` with `W(y) = Σ_{k ≤ √y} (y/k² - 1)`. Cut the Möbius sum at `x^θ`:
`A_θ(x) = Σ_{m ≤ x^θ} μ(m) W(x/m)`. With `W(y) = Zy - 2√y + O(1)` the head splits as
`A_θ = Z x H₁(x^θ) - 2√x H₂(x^θ) + E_θ`, `|E_θ(x)| ≤ x^θ`, and on `Re s > 2`

`∫ A_θ(e^u) e^{-su} du = Z/((s-1)ζ((s-1)/θ+1)) - 2/((s-½)ζ((s-½)/θ+½)) + R_θ(s)`,

with `R_θ` holomorphic on `Re s > ½` when `θ ≤ ½`. The moving lower endpoint `m^{1/θ}` of every head
integral transports a zero `ρ` of `ζ` to `1 + θ(ρ - 1)`.

Iterating the contraction `ρ ↦ 1 + θ(ρ - 1)` from a critical zero converges to `1`, where the
residue unit does not vanish; hence some zero `ρ` with `½ ≤ Re ρ < 1` has `ζ(1 + θ(ρ - 1)) ≠ 0`.
At `w = 1 + θ(ρ - 1)`, `Re w ≥ 1 - θ/2`, the head transform has a pole that neither `P` nor the
root head can cancel (the root head's argument there has real part `≥ 1/(2θ) ≥ 1`).

Suppose `η(dP + cA_θ)(x) ≤ C x^β` for large `x`, `c ≠ 0`, `1 - θ < β < 1 - θ/2`. The one-sided
Landau engine of `LiouvilleTriangularHeadOscillation` pins the abscissa of the clipped density at
`β`. Multiplying the continuation identity by `D(z) = zU(z)(z-½)U(v(z))U(h(z))`,
`U(w) = (w-1)ζ(w)`, the identity theorem on `Re z > β` evaluated at `w` gives
`η · (cZ/θ) · wU(w)(w-½)U(v(w)) = 0`, a contradiction.

**Cutoff transport law** (`frequently_gt_and_frequently_lt`): for every `0 < θ ≤ ½`, every real
`d`, every `c ≠ 0` and every `β < 1 - θ/2`, `dP + cA_θ` exceeds `C x^β` and falls below `-C x^β`
for arbitrarily large `x`. In particular the cut head `A_θ` and the Möbius tail `P - A_θ` each
oscillate beyond `x^{1-θ/2-ε}`: no split of the hyperbola decomposition at any level `x^θ`,
`θ ≤ ½`, can be estimated piece by piece at the critical exponent.

Starting the contraction from zeros with real part close to the zero abscissa
`Θ = sup Re ρ` (`exists_contracted_nonzero_gt`) sharpens the threshold to the transported
abscissa: `dP + cA_θ` oscillates beyond `x^β` for every `β < 1 - θ(1 - Θ)`
(`frequently_gt_and_frequently_lt_abscissa`).
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.RHTower
open RHTower.LiouvilleTriangularHeadOscillation

namespace RHTower.LiouvilleHyperbolaCutoffOscillation

noncomputable section

/-! ## A zero whose contraction toward one is not a zero -/

theorem zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero {z : ℂ} (hz : riemannZeta z = 0) :
    RHTower.zetaResidueUnit z = 0 := by
  rw [zetaResidueUnit_eq (RHTower.riemannZeta_zero_ne_one hz), hz, mul_zero]

/-- For every contraction ratio `0 < θ < 1` some zero `ρ` with `½ ≤ Re ρ < 1`, `Im ρ ≠ 0` has
`ζ(1 + θ(ρ - 1)) ≠ 0`: iterating the contraction from a critical zero converges to `1`. -/
theorem exists_separated_contracted_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧
      riemannZeta (1 + θ * (ρ - 1)) ≠ 0 := by
  by_contra hnone
  have hstep : ∀ z : ℂ, riemannZeta z = 0 → 1 / 2 ≤ z.re → z.re < 1 → z.im ≠ 0 →
      riemannZeta (1 + θ * (z - 1)) = 0 := by
    intro z hz hlo hhi him
    by_contra hne
    exact hnone ⟨z, hz, hlo, hhi, him, hne⟩
  obtain ⟨t, ht, hzero⟩ := RHTower.exists_Xi_zero_gt 1
  have hz : riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
    apply RHTower.riemannZeta_eq_zero_iff_xi_or_trivial.mpr
    apply Or.inl
    change RHTower.XiC (t : ℂ) = 0
    rw [RHTower.XiC_ofReal, hzero]
    simp
  set z : ℂ := 1 / 2 + (t : ℂ) * I with hzdef
  let p : ℕ → ℝ := fun n => θ ^ n
  let r : ℕ → ℂ := fun n => 1 + (z - 1) * (p n : ℂ)
  have hp : ∀ n, 0 < p n ∧ p n ≤ 1 := fun n =>
    ⟨pow_pos hθ0 _, pow_le_one₀ hθ0.le hθ1.le⟩
  have hrre : ∀ n, (r n).re = 1 - p n / 2 := by
    intro n
    simp [r, hzdef]
    ring
  have hrim : ∀ n, (r n).im = t * p n := by
    intro n
    simp [r, hzdef]
  have hrlo : ∀ n, 1 / 2 ≤ (r n).re := fun n => by
    rw [hrre]; have := (hp n).2; linarith
  have hrhi : ∀ n, (r n).re < 1 := fun n => by
    rw [hrre]; have := (hp n).1; linarith
  have ht0 : t ≠ 0 := by linarith
  have hrimne : ∀ n, (r n).im ≠ 0 := fun n => by
    rw [hrim]; exact mul_ne_zero ht0 (hp n).1.ne'
  have hrnext : ∀ n, r (n + 1) = 1 + θ * (r n - 1) := by
    intro n
    simp only [r, p, pow_succ, Complex.ofReal_mul]
    ring
  have hrzero : ∀ n, riemannZeta (r n) = 0 := by
    intro n
    induction n with
    | zero => simpa [r, p] using hz
    | succ n ih =>
      rw [hrnext]
      exact hstep _ ih (hrlo n) (hrhi n) (hrimne n)
  have hp0 : Tendsto p atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1
  have hr1 : Tendsto r atTop (𝓝 1) := by
    have hc : Tendsto (fun n => (p n : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hp0
    simpa [r] using tendsto_const_nhds.add (tendsto_const_nhds.mul hc)
  have hu1 := (RHTower.analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp hr1
  have hu0 : Tendsto (fun n => RHTower.zetaResidueUnit (r n)) atTop (𝓝 0) := by
    have he : (fun n => RHTower.zetaResidueUnit (r n)) = fun _ : ℕ => (0 : ℂ) :=
      funext fun n => zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero (hrzero n)
    rw [he]
    exact tendsto_const_nhds
  have he := tendsto_nhds_unique hu1 hu0
  simp at he

/-- Starting from any nonreal zero `ρ₀` in the open strip, the contraction `ρ ↦ 1 + θ(ρ - 1)`
reaches a zero `ρ` with `Re ρ₀ ≤ Re ρ < 1`, `Im ρ ≠ 0`, whose image is not a zero. -/
theorem exists_contracted_nonzero_of_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ₀ : ℂ}
    (hz : riemannZeta ρ₀ = 0) (hhi : ρ₀.re < 1) (him : ρ₀.im ≠ 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ₀.re ≤ ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧
      riemannZeta (1 + θ * (ρ - 1)) ≠ 0 := by
  by_contra hnone
  have hstep : ∀ z : ℂ, riemannZeta z = 0 → ρ₀.re ≤ z.re → z.re < 1 → z.im ≠ 0 →
      riemannZeta (1 + θ * (z - 1)) = 0 := by
    intro z hz hlo hhi him
    by_contra hne
    exact hnone ⟨z, hz, hlo, hhi, him, hne⟩
  let p : ℕ → ℝ := fun n => θ ^ n
  let r : ℕ → ℂ := fun n => 1 + (ρ₀ - 1) * (p n : ℂ)
  have hp : ∀ n, 0 < p n ∧ p n ≤ 1 := fun n =>
    ⟨pow_pos hθ0 _, pow_le_one₀ hθ0.le hθ1.le⟩
  have hrre : ∀ n, (r n).re = 1 - (1 - ρ₀.re) * p n := by
    intro n
    simp [r]
    ring
  have hrim : ∀ n, (r n).im = ρ₀.im * p n := by
    intro n
    simp [r]
  have hrlo : ∀ n, ρ₀.re ≤ (r n).re := fun n => by
    rw [hrre]; have := (hp n).2; nlinarith
  have hrhi : ∀ n, (r n).re < 1 := fun n => by
    rw [hrre]; have := (hp n).1; nlinarith
  have hrimne : ∀ n, (r n).im ≠ 0 := fun n => by
    rw [hrim]; exact mul_ne_zero him (hp n).1.ne'
  have hrnext : ∀ n, r (n + 1) = 1 + θ * (r n - 1) := by
    intro n
    simp only [r, p, pow_succ, Complex.ofReal_mul]
    ring
  have hrzero : ∀ n, riemannZeta (r n) = 0 := by
    intro n
    induction n with
    | zero => simpa [r, p] using hz
    | succ n ih =>
      rw [hrnext]
      exact hstep _ ih (hrlo n) (hrhi n) (hrimne n)
  have hp0 : Tendsto p atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1
  have hr1 : Tendsto r atTop (𝓝 1) := by
    have hc : Tendsto (fun n => (p n : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hp0
    simpa [r] using tendsto_const_nhds.add (tendsto_const_nhds.mul hc)
  have hu1 := (RHTower.analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp hr1
  have hu0 : Tendsto (fun n => RHTower.zetaResidueUnit (r n)) atTop (𝓝 0) := by
    have he : (fun n => RHTower.zetaResidueUnit (r n)) = fun _ : ℕ => (0 : ℂ) :=
      funext fun n => zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero (hrzero n)
    rw [he]
    exact tendsto_const_nhds
  have he := tendsto_nhds_unique hu1 hu0
  simp at he

/-- A zero in the open strip is not real. -/
theorem im_ne_zero_of_zero_mem_strip {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) :
    ρ.im ≠ 0 := by
  intro him
  have hρ : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hU := zetaResidueUnit_ofReal_ne_zero h0
  rw [← hρ] at hU
  exact hU (zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hz)

/-- For every level `b ≥ 0` below the zero abscissa `Θ`, some zero `ρ` with `b < Re ρ < 1`,
`Im ρ ≠ 0` has `ζ(1 + θ(ρ - 1)) ≠ 0`. -/
theorem exists_contracted_nonzero_gt {θ b : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hb0 : 0 ≤ b)
    (hb : b < zetaZeroAbscissa) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ b < ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧
      riemannZeta (1 + θ * (ρ - 1)) ≠ 0 := by
  obtain ⟨ρ₀, hz, hhi, hlo⟩ := exists_zetaZero_mem_openStrip_lt_re hb
  have him := im_ne_zero_of_zero_mem_strip hz (by linarith)
  obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := exists_contracted_nonzero_of_zero hθ0 hθ1 hz hhi him
  exact ⟨ρ, h1, lt_of_lt_of_le hlo h2, h3, h4, h5⟩

/-! ## The Möbius head cut at `x^θ` -/

/-- The Möbius head of the Liouville hyperbola decomposition cut at `x^θ`:
`A_θ(x) = Σ_{m ≤ x^θ} μ(m) W(x/m)`. -/
def cutoffHead (θ x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
    LiouvilleTriangularShortHead.squareTriangle (x / m)

/-- `E_θ(x) = A_θ(x) - Z x H₁(x^θ) + 2√x H₂(x^θ)`. -/
def cutoffRemainder (θ x : ℝ) : ℝ :=
  cutoffHead θ x - LiouvilleTriangularShortHead.squareMass * x * mobiusHarmonic (x ^ θ)
    + 2 * Real.sqrt x * mobiusRoot (x ^ θ)

theorem cutoffHead_eq (θ x : ℝ) :
    cutoffHead θ x = LiouvilleTriangularShortHead.squareMass * x * mobiusHarmonic (x ^ θ)
      + -2 * Real.sqrt x * mobiusRoot (x ^ θ) + cutoffRemainder θ x := by
  unfold cutoffRemainder; ring

theorem measurable_cutoffHead (θ : ℝ) : Measurable (cutoffHead θ) :=
  measurable_finsetSum_comp (s := Finset.Icc 1)
    (F := fun m x => ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
      LiouvilleTriangularShortHead.squareTriangle (x / m))
    (fun _ => measurable_const.mul (measurable_squareTriangle.comp (measurable_id.div_const _)))
    (Nat.measurable_floor.comp (measurable_id.pow_const θ))

theorem measurable_cutoffRemainder (θ : ℝ) : Measurable (cutoffRemainder θ) := by
  unfold cutoffRemainder
  have hp : Measurable fun x : ℝ => x ^ θ := measurable_id.pow_const θ
  exact ((measurable_cutoffHead θ).sub ((measurable_const.mul measurable_id).mul
    (measurable_mobiusHarmonic.comp hp))).add
    ((measurable_const.mul Real.continuous_sqrt.measurable).mul (measurable_mobiusRoot.comp hp))

theorem cutoffRemainder_eq (θ x : ℝ) :
    cutoffRemainder θ x = ∑ m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m)) := by
  unfold cutoffRemainder cutoffHead mobiusHarmonic mobiusRoot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  rw [Real.sqrt_div' x (by linarith : (0 : ℝ) ≤ m)]
  field_simp

/-- `|E_θ(x)| ≤ ⌊x^θ⌋` for `x ≥ 1` and `0 ≤ θ ≤ 1`. -/
theorem abs_cutoffRemainder_le {θ x : ℝ} (hθ1 : θ ≤ 1) (hx : 1 ≤ x) :
    |cutoffRemainder θ x| ≤ ⌊x ^ θ⌋₊ := by
  rw [cutoffRemainder_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hxθ : x ^ θ ≤ x := Real.rpow_le_self_of_one_le hx hθ1
  have hxθ0 : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) θ
  calc ∑ m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, |((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m))|
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hmx : (m : ℝ) ≤ x := by
          have h1 : (m : ℝ) ≤ ⌊x ^ θ⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          have h2 : (⌊x ^ θ⌋₊ : ℝ) ≤ x ^ θ := Nat.floor_le hxθ0
          linarith
        have hxm : 1 ≤ x / m := (le_div_iff₀ (by linarith)).mpr (by linarith)
        rw [abs_mul]
        calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| *
              |LiouvilleTriangularShortHead.squareTriangle (x / m)
                - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m)|
            ≤ 1 * 1 := mul_le_mul (abs_moebius_cast_le_one m)
              (LiouvilleTriangularShortHead.squareTriangle_remainder hxm) (abs_nonneg _)
              zero_le_one
          _ = 1 := one_mul 1
    _ = ⌊x ^ θ⌋₊ := by simp

theorem exp_rpow_eq_exp_mul (u θ : ℝ) : Real.exp u ^ θ = Real.exp (θ * u) := by
  rw [← Real.exp_mul, mul_comm]

theorem abs_cutoffRemainder_exp_le {θ u : ℝ} (hθ : θ ≤ 1 / 2) (hu : 0 ≤ u) :
    |cutoffRemainder θ (Real.exp u)| ≤ Real.exp (1 / 2 * u) := by
  refine (abs_cutoffRemainder_le (by linarith) (Real.one_le_exp hu)).trans ?_
  rw [exp_rpow_eq_exp_mul]
  exact (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr (by nlinarith))

/-! ### Transforms of the cut head terms -/

theorem integral_comp_mul (g : ℝ → ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ∫ u in Ioi (0 : ℝ), g (θ * u) = (θ⁻¹ : ℂ) * ∫ v in Ioi (0 : ℝ), g v := by
  have h := integral_comp_mul_left_Ioi g 0 hθ
  rw [mul_zero] at h
  rw [h, Complex.real_smul]
  push_cast
  ring

/-- `∫_0^∞ Z e^u H₁(e^{θu}) e^{-su} du = Z/((s-1)ζ((s-1)/θ+1))` on `Re s > 2`, `0 < θ < 1`. -/
theorem integral_cutHarmonicHead {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularShortHead.squareMass /
          ((s - 1) * riemannZeta ((s - 1) / θ + 1)) := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZ
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set g : ℝ → ℂ := fun v => ((Z * Real.exp (v / θ) * mobiusHarmonic (Real.exp v) : ℝ) : ℂ)
    * Complex.exp (-(s / θ) * v) with hg
  have hpt : ∀ u : ℝ, ((Z * Real.exp u * mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ)
      * Complex.exp (-s * u) = g (θ * u) := by
    intro u
    simp only [hg]
    rw [exp_rpow_eq_exp_mul, show θ * u / θ = u by field_simp]
    congr 2
    push_cast
    field_simp
  have hre : 1 < ((s - 1) / θ).re := by
    rw [show (s - 1) / (θ : ℂ) = (s - 1) * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp only [Complex.sub_re, Complex.one_re]
    rw [← div_eq_mul_inv, lt_div_iff₀ hθ0]
    linarith
  have h3 : 1 < ((s - 1) / θ + 1).re := by
    have : ((s - 1) / θ + 1).re = ((s - 1) / θ).re + 1 := by simp
    rw [this]; linarith
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hL := LSeries_moebius_mul_riemannZeta_eq_one h3
  have hL' : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ((s - 1) / θ + 1)
      = (riemannZeta ((s - 1) / θ + 1))⁻¹ := eq_inv_of_mul_eq_one_left hL
  have key := integral_partialSum_exp_mul_cexp
    (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 : ℂ)))
    (norm_moebius_mul_cpow_le (by simp) one_ne_zero) hre
  rw [LSeries_mul_cpow_neg] at key
  have hg' : ∫ v in Ioi (0 : ℝ), g v = (Z : ℂ) * ∫ v in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ)
        * (k : ℂ) ^ (-(1 : ℂ))) * Complex.exp (-((s - 1) / θ) * v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hg]
    rw [← mobiusHarmonic_ofReal]
    push_cast
    rw [show Complex.exp (-((s - 1) / θ) * v)
        = Complex.exp (v / θ) * Complex.exp (-(s / θ) * v) by
      rw [← Complex.exp_add]; congr 1; field_simp; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_comp_mul g hθ0, hg',
    key, hL']
  field_simp

/-- `∫_0^∞ (-2) e^{u/2} H₂(e^{θu}) e^{-su} du = -2/((s-½)ζ((s-½)/θ+½))` on `Re s > 2`. -/
theorem integral_cutRootHead {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((-2 * Real.sqrt (Real.exp u) *
        mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
      = -2 / ((s - 1 / 2) * riemannZeta ((s - 1 / 2) / θ + 1 / 2)) := by
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set g : ℝ → ℂ := fun v => ((-2 * Real.exp (v / (2 * θ)) * mobiusRoot (Real.exp v) : ℝ) : ℂ)
    * Complex.exp (-(s / θ) * v) with hg
  have hpt : ∀ u : ℝ, ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ)
      * Complex.exp (-s * u) = g (θ * u) := by
    intro u
    simp only [hg]
    rw [exp_rpow_eq_exp_mul, sqrt_exp_eq_exp_half_mul,
      show θ * u / (2 * θ) = 1 / 2 * u by field_simp]
    congr 2
    push_cast
    field_simp
  have hre : 1 < ((s - 1 / 2) / θ).re := by
    rw [show (s - 1 / 2) / (θ : ℂ) = (s - 1 / 2) * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    rw [← div_eq_mul_inv, lt_div_iff₀ hθ0]
    linarith
  have h3 : 1 < ((s - 1 / 2) / θ + 1 / 2).re := by
    have : ((s - 1 / 2) / θ + 1 / 2).re = ((s - 1 / 2) / θ).re + 1 / 2 := by simp
    rw [this]; linarith
  have hsh : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hL := LSeries_moebius_mul_riemannZeta_eq_one h3
  have hL' : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) ((s - 1 / 2) / θ + 1 / 2)
      = (riemannZeta ((s - 1 / 2) / θ + 1 / 2))⁻¹ := eq_inv_of_mul_eq_one_left hL
  have key := integral_partialSum_exp_mul_cexp
    (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (k : ℂ) ^ (-(1 / 2 : ℂ)))
    (norm_moebius_mul_cpow_le (by norm_num) (by norm_num)) hre
  rw [LSeries_mul_cpow_neg] at key
  have hg' : ∫ v in Ioi (0 : ℝ), g v = (-2 : ℂ) * ∫ v in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ)
        * (k : ℂ) ^ (-(1 / 2 : ℂ))) * Complex.exp (-((s - 1 / 2) / θ) * v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hg]
    rw [← mobiusRoot_ofReal]
    push_cast
    rw [show Complex.exp (-((s - 1 / 2) / θ) * v)
        = Complex.exp (v / (2 * θ)) * Complex.exp (-(s / θ) * v) by
      rw [← Complex.exp_add]; congr 1; field_simp; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_comp_mul g hθ0, hg',
    key, hL']
  field_simp

/-! ### The transform of the complete cut head -/

/-- The transform of the bounded remainder of the cut head. -/
def cutoffRemainderTransform (θ : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (cutoffRemainder θ (Real.exp u) : ℂ) * Complex.exp (-z * u)

theorem analyticOnNhd_cutoffRemainderTransform {θ : ℝ} (hθ : θ ≤ 1 / 2) :
    AnalyticOnNhd ℂ (cutoffRemainderTransform θ) {z : ℂ | 1 / 2 < z.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_integral_mul_cexp
      ((measurable_cutoffRemainder θ).comp Real.measurable_exp)
      (fun _ hu => abs_cutoffRemainder_exp_le hθ hu.le) hz).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem abs_cutHarmonicHead_exp_le {θ : ℝ} (hθ : θ ≤ 1 / 2) {u : ℝ} (hu : 0 ≤ u) :
    |LiouvilleTriangularShortHead.squareMass * Real.exp u * mobiusHarmonic (Real.exp u ^ θ)|
      ≤ LiouvilleTriangularShortHead.squareMass * Real.exp (3 / 2 * u) := by
  have hZ := squareMass_pos
  have hE := Real.exp_pos u
  rw [exp_rpow_eq_exp_mul]
  have h1 : |mobiusHarmonic (Real.exp (θ * u))| ≤ Real.exp (1 / 2 * u) :=
    (abs_mobiusHarmonic_le _).trans ((Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (by nlinarith)))
  have h2 : Real.exp (3 / 2 * u) = Real.exp u * Real.exp (1 / 2 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos hZ, abs_of_pos hE, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem abs_cutRootHead_exp_le {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {u : ℝ} (hu : 0 ≤ u) :
    |-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ)| ≤ 2 * Real.exp u := by
  rw [exp_rpow_eq_exp_mul, sqrt_exp_eq_exp_half_mul]
  have hE := Real.exp_pos (1 / 2 * u)
  have h1 : |mobiusRoot (Real.exp (θ * u))| ≤ Real.exp (1 / 2 * u) :=
    (abs_mobiusRoot_le _).trans ((Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (by nlinarith)))
  have h2 : Real.exp u = Real.exp (1 / 2 * u) * Real.exp (1 / 2 * u) := by
    rw [← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos hE, h2]
  norm_num
  nlinarith

theorem abs_cutoffHead_exp_le {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {u : ℝ} (hu : 0 ≤ u) :
    |cutoffHead θ (Real.exp u)|
      ≤ (LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u) := by
  rw [cutoffHead_eq]
  have h1 := abs_cutHarmonicHead_exp_le hθ hu
  have h2 := abs_cutRootHead_exp_le hθ0 hθ hu
  have h3 := abs_cutoffRemainder_exp_le hθ hu
  have hZ := squareMass_pos
  have e1 : Real.exp (3 / 2 * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp u ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (1 / 2 * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have hab := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ) + -2 * Real.sqrt (Real.exp u) *
        mobiusRoot (Real.exp u ^ θ)) (cutoffRemainder θ (Real.exp u))
  have hab2 := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ))
      (-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ))
  nlinarith

theorem integral_cutoffHead_exp_mul_cexp {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularShortHead.squareMass / ((s - 1) * riemannZeta ((s - 1) / θ + 1))
        - 2 / ((s - 1 / 2) * riemannZeta ((s - 1 / 2) / θ + 1 / 2))
        + cutoffRemainderTransform θ s := by
  have hp : Measurable fun u : ℝ => Real.exp u ^ θ := Real.measurable_exp.pow_const θ
  have i1 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass * Real.exp u *
      mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ))
      ((measurable_const.mul Real.measurable_exp).mul (measurable_mobiusHarmonic.comp hp))
      (fun u hu => abs_cutHarmonicHead_exp_le hθ hu.le) (by linarith)
  have i2 : IntegrableOn (fun u : ℝ => ((-2 * Real.sqrt (Real.exp u) *
      mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => -2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ))
      ((measurable_const.mul (Real.continuous_sqrt.measurable.comp Real.measurable_exp)).mul
        (measurable_mobiusRoot.comp hp))
      (fun u hu => by rw [one_mul]; exact abs_cutRootHead_exp_le hθ0 hθ hu.le) (C := 2) (a := 1)
      (by linarith)
  have i3 : IntegrableOn (fun u : ℝ => (cutoffRemainder θ (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 1) (a := 1 / 2)
      ((measurable_cutoffRemainder θ).comp Real.measurable_exp)
      (fun u hu => by simpa using abs_cutoffRemainder_exp_le hθ hu.le) (by linarith)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = (((LiouvilleTriangularShortHead.squareMass * Real.exp u *
          mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
        + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ)
          * Complex.exp (-s * u))
        + (cutoffRemainder θ (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    intro u _
    rw [cutoffHead_eq]
    push_cast
    ring
  have i12 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass *
      Real.exp u * mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
      + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ)
        * Complex.exp (-s * u)) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i12 i3,
    integral_add i1 i2, integral_cutHarmonicHead hθ0 (by linarith) hs,
    integral_cutRootHead hθ0 (by linarith) hs]
  unfold cutoffRemainderTransform
  ring

/-! ## The cut pole model and the contradiction at a contracted zero -/

/-- `h(z) = (z-1)/θ + 1`, the argument of the head zeta factor. -/
def headArg (θ : ℝ) (z : ℂ) : ℂ := (z - 1) / θ + 1

/-- `v(z) = (z-½)/θ + ½`, the argument of the root-head zeta factor. -/
def rootArg (θ : ℝ) (z : ℂ) : ℂ := (z - 1 / 2) / θ + 1 / 2

/-- The three-term transform of `dP + cA_θ`, written with `U(w) = (w-1)ζ(w)`. -/
def cutPoleModel (θ d c : ℝ) (z : ℂ) : ℂ :=
  d * riemannZeta (2 * z) / (z * RHTower.zetaResidueUnit z)
    + c * LiouvilleTriangularShortHead.squareMass / θ / RHTower.zetaResidueUnit (headArg θ z)
    + -2 * c * (rootArg θ z - 1) / ((z - 1 / 2) * RHTower.zetaResidueUnit (rootArg θ z))

/-- `D(z) = z U(z)(z-½) U(v(z)) U(h(z))`. -/
def cutPoleDenominator (θ : ℝ) (z : ℂ) : ℂ :=
  z * RHTower.zetaResidueUnit z * (z - 1 / 2) * RHTower.zetaResidueUnit (rootArg θ z)
    * RHTower.zetaResidueUnit (headArg θ z)

/-- The cut pole model times `D`, without denominators. -/
def cutPoleNumerator (θ d c : ℝ) (z : ℂ) : ℂ :=
  d * riemannZeta (2 * z) * ((z - 1 / 2) * RHTower.zetaResidueUnit (rootArg θ z)
      * RHTower.zetaResidueUnit (headArg θ z))
    + c * LiouvilleTriangularShortHead.squareMass / θ * (z * RHTower.zetaResidueUnit z
      * (z - 1 / 2) * RHTower.zetaResidueUnit (rootArg θ z))
    + -2 * c * (rootArg θ z - 1) * (z * RHTower.zetaResidueUnit z
      * RHTower.zetaResidueUnit (headArg θ z))

theorem cutPoleModel_mul_denominator (θ d c : ℝ) (hθ : (θ : ℂ) ≠ 0) {z : ℂ} (h0 : z ≠ 0)
    (hU : RHTower.zetaResidueUnit z ≠ 0) (hh : z - 1 / 2 ≠ 0)
    (hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0)
    (hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0) :
    cutPoleModel θ d c z * cutPoleDenominator θ z = cutPoleNumerator θ d c z := by
  unfold cutPoleModel cutPoleDenominator cutPoleNumerator
  generalize RHTower.zetaResidueUnit z = A at *
  generalize RHTower.zetaResidueUnit (rootArg θ z) = B2 at *
  generalize RHTower.zetaResidueUnit (headArg θ z) = B1 at *
  generalize riemannZeta (2 * z) = Z2
  generalize rootArg θ z - 1 = V
  generalize hH : z - 1 / 2 = H at *
  field_simp

theorem differentiableAt_cutPoleDenominator (θ : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (cutPoleDenominator θ) z := by
  have hu := fun w => (RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  unfold cutPoleDenominator rootArg headArg
  exact (((differentiableAt_id.mul (hu z)).mul (differentiableAt_id.sub_const _)).mul
    ((hu _).comp z (by fun_prop))).mul ((hu _).comp z (by fun_prop))

theorem differentiableAt_cutPoleNumerator (θ d c : ℝ) {z : ℂ} (hz : 2 * z ≠ 1) :
    DifferentiableAt ℂ (cutPoleNumerator θ d c) z := by
  have hu := fun w => (RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  have hZ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) z :=
    ((analyticOn_riemannZeta _ hz).differentiableAt).comp z (by fun_prop)
  have hv : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (rootArg θ z)) z :=
    (hu _).comp z (by unfold rootArg; fun_prop)
  have hh : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (headArg θ z)) z :=
    (hu _).comp z (by unfold headArg; fun_prop)
  have hr : DifferentiableAt ℂ (fun z : ℂ => rootArg θ z - 1) z := by unfold rootArg; fun_prop
  unfold cutPoleNumerator
  exact (((differentiableAt_const _).mul hZ).mul (((differentiableAt_id.sub_const _).mul hv).mul
    hh)).add ((differentiableAt_const _).mul (((differentiableAt_id.mul (hu z)).mul
      (differentiableAt_id.sub_const _)).mul hv)) |>.add
    (((differentiableAt_const _).mul hr).mul ((differentiableAt_id.mul (hu z)).mul hh))

theorem analyticAt_cutPoleModel_ofReal {θ : ℝ} (hθ0 : 0 < θ) (d c : ℝ) {t : ℝ}
    (ht : 1 / 2 < t) (htθ : 1 - θ < t) :
    AnalyticAt ℂ (cutPoleModel θ d c) t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
  have hth : (t : ℂ) - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2t : 2 * (t : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hU : RHTower.zetaResidueUnit t ≠ 0 := zetaResidueUnit_ofReal_ne_zero (by linarith)
  have hharg : headArg θ (t : ℂ) = (((t - 1) / θ + 1 : ℝ) : ℂ) := by
    unfold headArg; push_cast; ring
  have hrarg : rootArg θ (t : ℂ) = (((t - 1 / 2) / θ + 1 / 2 : ℝ) : ℂ) := by
    unfold rootArg; push_cast; ring
  have hUh : RHTower.zetaResidueUnit (headArg θ t) ≠ 0 := by
    rw [hharg]
    refine zetaResidueUnit_ofReal_ne_zero ?_
    have : 0 < (t - 1) / θ + 1 := by
      rw [div_add_one hθ0.ne']; exact div_pos (by linarith) hθ0
    exact this
  have hpos : 0 < (t - 1 / 2) / θ + 1 / 2 := by
    have := div_pos (by linarith : 0 < t - 1 / 2) hθ0
    linarith
  have hUv : RHTower.zetaResidueUnit (rootArg θ t) ≠ 0 := by
    rw [hrarg]
    exact zetaResidueUnit_ofReal_ne_zero hpos
  have hZ : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) t :=
    (analyticOn_riemannZeta _ h2t).comp (by fun_prop)
  have hAh : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (headArg θ z)) t :=
    (RHTower.analyticAt_zetaResidueUnit _).comp (by unfold headArg; fun_prop)
  have hAv : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (rootArg θ z)) t :=
    (RHTower.analyticAt_zetaResidueUnit _).comp (by unfold rootArg; fun_prop)
  have hr : AnalyticAt ℂ (fun z : ℂ => rootArg θ z - 1) t := by unfold rootArg; fun_prop
  unfold cutPoleModel
  exact (((analyticAt_const.mul hZ).div
      (analyticAt_id.mul (RHTower.analyticAt_zetaResidueUnit _)) (mul_ne_zero ht0 hU)).add
      (analyticAt_const.div hAh hUh)).add
    ((analyticAt_const.mul hr).div ((analyticAt_id.sub analyticAt_const).mul hAv)
      (mul_ne_zero hth hUv))

/-- On `Re s > 2` the transform of `dP + cA_θ` is the cut pole model plus `cR_θ(s)`. -/
theorem integral_cutCombination_exp_mul_cexp {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (d c : ℝ) {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
        : ℝ) : ℂ) * Complex.exp (-s * u)
      = cutPoleModel θ d c s + c * cutoffRemainderTransform θ s := by
  have i1 : IntegrableOn (fun u : ℝ => (liouvilleTriangle (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 2) (a := 2)
      (measurable_liouvilleTriangle.comp Real.measurable_exp)
      (fun u hu => abs_liouvilleTriangle_exp_le hu.le) hs
  have i2 : IntegrableOn (fun u : ℝ => (cutoffHead θ (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := LiouvilleTriangularShortHead.squareMass + 3) (a := 2)
      ((measurable_cutoffHead θ).comp Real.measurable_exp)
      (fun u hu => abs_cutoffHead_exp_le hθ0 hθ hu.le) hs
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ((d * liouvilleTriangle (Real.exp u)
        + c * cutoffHead θ (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)
      = (d : ℂ) * ((liouvilleTriangle (Real.exp u) : ℂ) * Complex.exp (-s * u))
        + (c : ℂ) * ((cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u _
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add (i1.const_mul _)
    (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_liouvilleTriangle_exp_mul_cexp hs, integral_cutoffHead_exp_mul_cexp hθ0 hθ hs]
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1' : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hsh : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hhre : 1 < (headArg θ s).re := by
    unfold headArg
    rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
    have : 0 < (s.re - 1) / θ := div_pos (by linarith) hθ0
    linarith
  have hvre : 1 < (rootArg θ s).re := by
    unfold rootArg
    rw [Complex.add_re, hθre, Complex.sub_re]
    have : 1 ≤ (s.re - (1 / 2 : ℂ).re) / θ := by
      rw [le_div_iff₀ hθ0]; norm_num; linarith
    norm_num at this ⊢
    linarith
  have hh1 : headArg θ s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hhre; linarith
  have hv1 : rootArg θ s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hvre; linarith
  have hz1 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hzh : riemannZeta (headArg θ s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hhre
  have hzv : riemannZeta (rootArg θ s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hvre
  have hd1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  have hdh : headArg θ s - 1 ≠ 0 := sub_ne_zero.mpr hh1
  have hdv : rootArg θ s - 1 ≠ 0 := sub_ne_zero.mpr hv1
  unfold cutPoleModel
  rw [zetaResidueUnit_eq hs1', zetaResidueUnit_eq hh1, zetaResidueUnit_eq hv1]
  have eh : headArg θ s - 1 = (s - 1) / θ := by unfold headArg; ring
  have ehz : (s - 1) / (θ : ℂ) + 1 = headArg θ s := rfl
  have evz : (s - 1 / 2) / (θ : ℂ) + 1 / 2 = rootArg θ s := rfl
  rw [ehz, evz, eh]
  have e3 : -2 * (c : ℂ) * (rootArg θ s - 1) /
      ((s - 1 / 2) * ((rootArg θ s - 1) * riemannZeta (rootArg θ s)))
      = -2 * c / ((s - 1 / 2) * riemannZeta (rootArg θ s)) := by
    rw [show -2 * (c : ℂ) * (rootArg θ s - 1) = (rootArg θ s - 1) * (-2 * c) by ring,
      show (s - 1 / 2) * ((rootArg θ s - 1) * riemannZeta (rootArg θ s))
        = (rootArg θ s - 1) * ((s - 1 / 2) * riemannZeta (rootArg θ s)) by ring,
      mul_div_mul_left _ _ hdv]
  rw [e3]
  generalize riemannZeta (rootArg θ s) = Zv at *
  generalize riemannZeta (headArg θ s) = Zh at *
  field_simp
  ring

/-! ### The contradiction -/

theorem abs_cutCombination_exp_le {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (d c : ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)|
      ≤ (2 * |d| + |c| * (LiouvilleTriangularShortHead.squareMass + 3)) * Real.exp (2 * u) := by
  have h1 := abs_liouvilleTriangle_exp_le hu
  have h2 := abs_cutoffHead_exp_le hθ0 hθ hu
  calc |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)|
      ≤ |d| * |liouvilleTriangle (Real.exp u)| + |c| * |cutoffHead θ (Real.exp u)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |d| * (2 * Real.exp (2 * u))
        + |c| * ((LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u)) := by
        gcongr
    _ = _ := by ring

/-- A one-sided bound `η(dP + cA_θ)(e^u) ≤ C e^{βu} + K` with `1-θ < β` is impossible when
`c ≠ 0` and `β` lies below the image `Re(1 + θ(ρ - 1))` of a zero whose image is not a zero. -/
theorem false_of_oneSided_at_zero {θ d c η C β K : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβθ : 1 - θ < β) (hK : 0 ≤ K) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hρlo : 1 / 2 ≤ ρ.re) (hρhi : ρ.re < 1) (hρim : ρ.im ≠ 0)
    (hwz : riemannZeta (1 + θ * (ρ - 1)) ≠ 0) (hβw : β < 1 - θ * (1 - ρ.re))
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    False := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZdef
  have hZ := squareMass_pos
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set f : ℝ → ℝ := fun u => d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
    with hfdef
  have hf : Measurable f := (measurable_const.mul
    (measurable_liouvilleTriangle.comp Real.measurable_exp)).add
    (measurable_const.mul ((measurable_cutoffHead θ).comp Real.measurable_exp))
  set B : ℝ := 2 * |d| + |c| * (Z + 3) with hBdef
  have hB : 0 ≤ B := by positivity
  have hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (2 * u) := fun u hu =>
    abs_cutCombination_exp_le hθ0 hθ d c hu.le
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : β ≤ 2 := by nlinarith
  have hCC : C < C + 1 := lt_add_one C
  obtain ⟨hc0, hlo, hhi⟩ := isAbscissa_oneSidedMeasure hf hη hC hCC hK hB hβ2
    (by norm_num) hb hg
  set ν := expOneSidedMeasure f η (C + 1) β K with hνdef
  set Ψ : ℂ → ℂ := fun z => ((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - η * (cutPoleModel θ d c z + c * cutoffRemainderTransform θ z) with hΨdef
  have hagree : ∀ z : ℂ, 2 < z.re → complexLaplace ν z = Ψ z := by
    intro z hz
    rw [complexLaplace_oneSidedMeasure_eq hf hβ0 hβ2 hCC.le hb hg hz]
    simp only [hΨdef, hfdef]
    rw [integral_cutCombination_exp_mul_cexp hθ0 hθ d c hz]
  have hΨa : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
    have htβ : (t : ℂ) - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP := analyticAt_cutPoleModel_ofReal hθ0 d c (by linarith : (1 : ℝ) / 2 < t)
      (by linarith : 1 - θ < t)
    have hR : AnalyticAt ℂ (cutoffRemainderTransform θ) t :=
      analyticOnNhd_cutoffRemainderTransform hθ t (by simp; linarith)
    simp only [hΨdef]
    exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) htβ).add
      (analyticAt_const.div analyticAt_id ht0)).sub
      (analyticAt_const.mul (hP.add (analyticAt_const.mul hR)))
  have hcβ : IsAbscissa ν β := isAbscissa_eq_of_analyticAt_real hc0 hlo hhi hΨa hagree
  set V : Set ℂ := {z : ℂ | β < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set Lf : ℂ → ℂ := fun z => (((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - complexLaplace ν z) * cutPoleDenominator θ z with hLf
  set Rf : ℂ → ℂ := fun z => (η : ℂ) * (cutPoleNumerator θ d c z
      + c * cutoffRemainderTransform θ z * cutPoleDenominator θ z) with hRf
  have hLa : AnalyticOnNhd ℂ Lf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hzβ : z - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have d1 : DifferentiableAt ℂ (fun z : ℂ => ((C + 1 : ℝ) : ℂ) / (z - β)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzβ
    have d2 : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) z :=
      (differentiableAt_const _).div differentiableAt_id hz0
    exact (((d1.add d2).sub (hasDerivAt_complexLaplace hcβ hz').differentiableAt).mul
      (differentiableAt_cutPoleDenominator θ z)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ Rf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have h2z : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR : DifferentiableAt ℂ (cutoffRemainderTransform θ) z :=
      (analyticOnNhd_cutoffRemainderTransform hθ z (by simp; linarith)).differentiableAt
    exact ((differentiableAt_const _).mul ((differentiableAt_cutPoleNumerator θ d c h2z).add
      (((differentiableAt_const _).mul hR).mul
        (differentiableAt_cutPoleDenominator θ z)))).differentiableWithinAt
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hev : Lf =ᶠ[𝓝 (3 : ℂ)] Rf := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    have hz' : 2 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz'; linarith
    have hzh : z - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hhre : 1 < (headArg θ z).re := by
      unfold headArg
      rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
      have : 0 < (z.re - 1) / θ := div_pos (by linarith) hθ0
      linarith
    have hvre : 1 < (rootArg θ z).re := by
      unfold rootArg
      rw [Complex.add_re, hθre, Complex.sub_re]
      have : 1 ≤ (z.re - (1 / 2 : ℂ).re) / θ := by
        rw [le_div_iff₀ hθ0]; norm_num; linarith
      norm_num at this ⊢
      linarith
    have hh1 : headArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hhre; linarith
    have hv1 : rootArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hvre; linarith
    have hU : RHTower.zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit_eq hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
    have hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hh1]
      exact mul_ne_zero (sub_ne_zero.mpr hh1) (riemannZeta_ne_zero_of_one_lt_re hhre)
    have hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hv1]
      exact mul_ne_zero (sub_ne_zero.mpr hv1) (riemannZeta_ne_zero_of_one_lt_re hvre)
    simp only [hLf, hRf]
    rw [hagree z hz', ← cutPoleModel_mul_denominator θ d c hθC hz0 hU hzh hUv hUh]
    simp only [hΨdef]
    ring
  have h3V : (3 : ℂ) ∈ V := by show β < (3 : ℂ).re; norm_num; linarith
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    (convex_halfSpace_re_gt β).isPreconnected h3V hev
  set w : ℂ := 1 + θ * (ρ - 1) with hwdef
  have hwre : w.re = 1 - θ * (1 - ρ.re) := by simp [hwdef]; ring
  have hwim : w.im = θ * ρ.im := by simp [hwdef]
  have hwlo : 1 - θ / 2 ≤ w.re := by rw [hwre]; nlinarith
  have hwV : w ∈ V := by show β < w.re; rw [hwre]; exact hβw
  have hhw : headArg θ w = ρ := by
    unfold headArg; rw [hwdef]; field_simp; ring
  have hUh : RHTower.zetaResidueUnit (headArg θ w) = 0 := by
    rw [hhw]; exact zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hρ
  have hDw : cutPoleDenominator θ w = 0 := by
    unfold cutPoleDenominator; rw [hUh, mul_zero]
  have h := heq hwV
  simp only [hLf, hRf, hDw, mul_zero, add_zero] at h
  have hNw : cutPoleNumerator θ d c w = c * Z / θ * (w * RHTower.zetaResidueUnit w * (w - 1 / 2)
      * RHTower.zetaResidueUnit (rootArg θ w)) := by
    unfold cutPoleNumerator; rw [hUh]; ring
  rw [hNw] at h
  have hη0 : (η : ℂ) ≠ 0 := by
    have : η ≠ 0 := by intro h0; rw [h0, abs_zero] at hη; norm_num at hη
    exact_mod_cast this
  have ha : (c : ℂ) * Z / θ ≠ 0 :=
    div_ne_zero (mul_ne_zero (by exact_mod_cast hc) (by exact_mod_cast hZ.ne')) hθC
  have hw0 : w ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; rw [Complex.zero_re] at this; linarith
  have hw1 : w ≠ 1 := by
    intro h0; have := congrArg Complex.im h0; rw [hwim, Complex.one_im] at this
    exact mul_ne_zero hθ0.ne' hρim this
  have hwh : w - 1 / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hrre : 1 ≤ (rootArg θ w).re := by
    have e : rootArg θ w = ρ + (1 / (2 * θ) - 1 / 2) := by
      unfold rootArg; rw [hwdef]; field_simp; ring
    rw [e]
    have h1 : (1 : ℝ) ≤ 1 / (2 * θ) := by rw [le_div_iff₀ (by linarith)]; linarith
    have : (ρ + ((1 : ℂ) / (2 * θ) - 1 / 2)).re = ρ.re + (1 / (2 * θ) - 1 / 2) := by
      simp
    rw [this]; linarith
  have hrim : (rootArg θ w).im = ρ.im := by
    have e : rootArg θ w = ρ + (((1 / (2 * θ) - 1 / 2 : ℝ)) : ℂ) := by
      unfold rootArg; rw [hwdef]; push_cast; field_simp; ring
    rw [e, Complex.add_im, Complex.ofReal_im, add_zero]
  have hv1 : rootArg θ w ≠ 1 := by
    intro h0; have := congrArg Complex.im h0; rw [hrim, Complex.one_im] at this
    exact hρim this
  have hUw : RHTower.zetaResidueUnit w ≠ 0 := by
    rw [zetaResidueUnit_eq hw1]; exact mul_ne_zero (sub_ne_zero.mpr hw1) hwz
  have hUv : RHTower.zetaResidueUnit (rootArg θ w) ≠ 0 := by
    rw [zetaResidueUnit_eq hv1]
    exact mul_ne_zero (sub_ne_zero.mpr hv1) (riemannZeta_ne_zero_of_one_le_re hrre)
  exact (mul_ne_zero hη0 (mul_ne_zero ha (mul_ne_zero (mul_ne_zero (mul_ne_zero hw0 hUw) hwh)
    hUv))) h.symm

/-- A one-sided bound `η(dP + cA_θ)(e^u) ≤ C e^{βu} + K` with `1-θ < β < 1-θ/2` is impossible
when `c ≠ 0`. -/
theorem false_of_oneSided {θ d c η C β K : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hc : c ≠ 0)
    (hη : |η| = 1) (hC : 0 ≤ C) (hβθ : 1 - θ < β) (hβ : β < 1 - θ / 2)
    (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    False := by
  obtain ⟨ρ, hρ, hρlo, hρhi, hρim, hwz⟩ :=
    exists_separated_contracted_zero hθ0 (by linarith : θ < 1)
  exact false_of_oneSided_at_zero hθ0 hθ hc hη hC hβθ hK hρ hρlo hρhi hρim hwz
    (by nlinarith) hg

/-- An eventual bound `η(dP + cA_θ)(x) ≤ C x^β` becomes a bound `C e^{β₁u} + K` on all `u > 0`
for every `β₁ ≥ β`. -/
theorem exists_oneSided_of_eventually_le {θ d c η C β β₁ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (hη : |η| = 1) (hC : 0 ≤ C) (hββ₁ : β ≤ β₁)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, 0 < u →
      η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
        ≤ C * Real.exp (β₁ * u) + K := by
  have hu : ∀ᶠ u in atTop, η * (d * liouvilleTriangle (Real.exp u) +
      c * cutoffHead θ (Real.exp u)) ≤ C * Real.exp (β₁ * u) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually h, eventually_ge_atTop (0 : ℝ)]
      with u hu hu0
    rw [← Real.exp_mul] at hu
    calc _ ≤ C * Real.exp (u * β) := hu
      _ ≤ C * Real.exp (β₁ * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp hu
  set u₁ := max u₀ 0 with hu₁def
  set B : ℝ := 2 * |d| + |c| * (LiouvilleTriangularShortHead.squareMass + 3) with hBdef
  have hB : 0 ≤ B := by have := squareMass_pos; positivity
  refine ⟨B * Real.exp (2 * u₁), by positivity, fun u hu0 => ?_⟩
  have h4 : 0 ≤ C * Real.exp (β₁ * u) := by positivity
  by_cases hle : u₀ ≤ u
  · have := hu₀ u hle
    have : 0 ≤ B * Real.exp (2 * u₁) := by positivity
    linarith
  · have h1 := abs_cutCombination_exp_le hθ0 hθ d c hu0.le
    have h2 : Real.exp (2 * u) ≤ Real.exp (2 * u₁) :=
      Real.exp_le_exp.mpr (by have := le_max_left u₀ 0; linarith)
    have h3 : η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
        ≤ |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)| :=
      calc _ ≤ |η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))| :=
            le_abs_self _
        _ = _ := by rw [abs_mul, hη, one_mul]
    have h5 : B * Real.exp (2 * u) ≤ B * Real.exp (2 * u₁) := mul_le_mul_of_nonneg_left h2 hB
    linarith

/-- A one-sided bound `η(dP + cA_θ)(x) ≤ C x^β` for large `x`, `β < 1 - θ/2`, `c ≠ 0`, is
impossible. -/
theorem false_of_eventually_le {θ d c η C β : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hc : c ≠ 0)
    (hη : |η| = 1) (hC : 0 ≤ C) (hβ : β < 1 - θ / 2)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    False := by
  set β₁ := max β (1 - 3 * θ / 4) with hβ₁def
  have hβ₁θ : 1 - θ < β₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hβ₁ : β₁ < 1 - θ / 2 := max_lt hβ (by linarith)
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le hθ0 hθ hη hC (le_max_left _ _) h
  exact false_of_oneSided (d := d) hθ0 hθ hc hη hC hβ₁θ hβ₁ hK hg

/-- A one-sided bound `η(dP + cA_θ)(x) ≤ C x^β` for large `x` with `β` below the transported
abscissa `1 - θ(1 - Θ)`, `Θ` the supremum of the real parts of the zeros, is impossible. -/
theorem false_of_eventually_le_abscissa {θ d c η C β : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβ : β < 1 - θ * (1 - zetaZeroAbscissa))
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    False := by
  rcases lt_or_ge β (1 - θ / 2) with hβh | hβh
  · exact false_of_eventually_le hθ0 hθ hc hη hC hβh h
  set b := 1 - (1 - β) / θ with hbdef
  have hθb : θ * (1 - b) = 1 - β := by rw [hbdef]; field_simp; ring
  have hb : b < zetaZeroAbscissa := by
    by_contra hcon
    have : θ * (1 - b) ≤ θ * (1 - zetaZeroAbscissa) :=
      mul_le_mul_of_nonneg_left (by linarith [not_lt.mp hcon]) hθ0.le
    linarith
  have hb2 : 1 / 2 ≤ b := by
    by_contra hcon
    have : θ * (1 / 2) < θ * (1 - b) := mul_lt_mul_of_pos_left (by linarith [not_le.mp hcon]) hθ0
    linarith
  obtain ⟨ρ, hρ, hbρ, hρhi, hρim, hwz⟩ :=
    exists_contracted_nonzero_gt hθ0 (by linarith : θ < 1) (by linarith) hb
  have hβw : β < 1 - θ * (1 - ρ.re) := by
    have : θ * (1 - ρ.re) < θ * (1 - b) := mul_lt_mul_of_pos_left (by linarith) hθ0
    linarith
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le hθ0 hθ hη hC le_rfl h
  exact false_of_oneSided_at_zero hθ0 hθ hc hη hC (by linarith) hK hρ (by linarith) hρhi hρim
    hwz hβw hg

/-- **Cutoff transport law.** For every `0 < θ ≤ ½`, every real `d`, every `c ≠ 0`, every
`β < 1 - θ/2` and every `C ≥ 0`, the combination `dP(x) + cA_θ(x)` exceeds `C x^β` and falls below
`-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (d c : ℝ)
    (hc : c ≠ 0) {β C : ℝ} (hβ : β < 1 - θ / 2) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(C * x ^ β)) := by
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le hθ0 hθ hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le hθ0 hθ hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)

/-- The cut head alone oscillates beyond `x^{1-θ/2-ε}`. -/
theorem cutoffHead_frequently {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {β C : ℝ}
    (hβ : β < 1 - θ / 2) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < cutoffHead θ x) ∧
      (∃ᶠ x in atTop, cutoffHead θ x < -(C * x ^ β)) := by
  simpa using frequently_gt_and_frequently_lt hθ0 hθ 0 1 one_ne_zero hβ hC

/-- The Möbius tail `P - A_θ` of the hyperbola decomposition oscillates beyond `x^{1-θ/2-ε}`. -/
theorem cutoffTail_frequently {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {β C : ℝ}
    (hβ : β < 1 - θ / 2) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < liouvilleTriangle x - cutoffHead θ x) ∧
      (∃ᶠ x in atTop, liouvilleTriangle x - cutoffHead θ x < -(C * x ^ β)) := by
  have h := frequently_gt_and_frequently_lt hθ0 hθ 1 (-1) (by norm_num) hβ hC
  simpa [sub_eq_add_neg] using h


/-- **Sharp lower half of the exponent law.** For every `0 < θ ≤ ½`, real `d`, `c ≠ 0`,
`C ≥ 0` and every `β < 1 - θ(1 - Θ)`, `Θ = sup Re ρ`, the combination `dP + cA_θ` exceeds
`C x^β` and falls below `-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt_abscissa {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    (d c : ℝ) (hc : c ≠ 0) {β C : ℝ} (hβ : β < 1 - θ * (1 - zetaZeroAbscissa)) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(C * x ^ β)) := by
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_abscissa hθ0 hθ hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_abscissa hθ0 hθ hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)

end

end RHTower.LiouvilleHyperbolaCutoffOscillation
