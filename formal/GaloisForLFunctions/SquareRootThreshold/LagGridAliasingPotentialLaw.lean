import GaloisForLFunctions.SquareRootThreshold.FiniteLagWindowRecordPotentialLaw

/-!
# Lag grids: the aliasing-potential law

On the lag grid `v = kℓ`, `0 ≤ k ≤ K`, the difference tests read the samples `φ(kℓ)` of the lag
function `φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}`. Suppose `Re W(f_{kℓ}) = φ(0) − φ(kℓ) ≥ 0` there.

**Grid window.** The polynomial `G(ζ) = Σ_{k ≤ K} (φ(0) − φ(kℓ)) ζ^k` has nonnegative coefficients,
so `|G(ζ)| ≤ G(|ζ|)`. Termwise (`sum_lagGrid_eq`),
`G(e^{−sℓ}) = φ(0) Q_K(e^{−sℓ}) − Σ_z D(z) Q_K(e^{(z − s)ℓ})`, `Q_K(w) = Σ_{k ≤ K} w^k` (`geomWin`).

**Aliasing-potential law** (`norm_evenCoeff_mul_geomWin_le`). At `s = σ + i Im z₀` the term of
`z₀` is `D(z₀) Q_K(e^{(Re z₀ − σ)ℓ})`, real and of size `e^{(Re z₀ − σ)(K+1)ℓ}/(e^{(Re z₀ − σ)ℓ} − 1)`;
it is bounded by `|φ(0)|(Q_K(e^{−σℓ}) + |Q_K(e^{−sℓ})|) + Σ_z |D(z)||Q_K(e^{(z−σ)ℓ})|
+ Σ_{z ≠ z₀} |D(z)||Q_K(e^{(z−s)ℓ})|`. Since `|Q_K(w)| ≤ (|w|^{K+1} + 1)/|1 − w|`, the continuum
distances `|Im z|` and `|z − s|` of the finite Laplace window are replaced by the **aliasing gaps**
`|1 − e^{(z − σ)ℓ}|` and `|1 − e^{(z − s)ℓ}|`: the grid sees the height of a zero only modulo `2π/ℓ`.

**What replaces attainment on a grid** (`exists_grid_lag_neg_of_loudness`). With aliasing gaps
`η_ℓ` (to the real axis) and `g_ℓ` (to the record), `κ_ℓ = 1/η_ℓ + 1/g_ℓ`, `θ = Re z₀ − σ` with
`2κ_ℓ N (e^{θℓ} − 1) ≤ 1`, and loudness ratio `N` at the lag `V = (K+1)ℓ`, some grid lag `kℓ ≤ Kℓ` is
negative once `κ_ℓ N |D(z₀)| (e^{θV} − 2) > 3|φ(0)|/(1 − e^{−σℓ}) + κ_ℓ Σ|D|`. A grid needs no
attained top; it needs that the loud zeros do not alias onto the real axis or onto the record,
with gaps large compared with the record's own scale `e^{θℓ} − 1`. The chains that hide from
grids (`exists_chain_hidden_from_grid`) have heights in `2πℤ/ℓ + o(1)`: their grid images `e^{zℓ}`
accumulate on the positive real axis, next to the image of the record, so both gaps fall to the
scale `θℓ` and the side condition fails by the factor `N`. On the continuum the same chain keeps
gaps `≥ 5` (`GridHiddenChainsHaveAnExplicitContinuumLag`).

**For `ζ`** (`zeta_grid_crowding_of_lag_primeWindow_nonneg`): if the window functionals are
nonnegative at the lags `kℓ`, `k ≤ K`, every loud off-line zero is crowded in the aliased sense.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The finite geometric kernel -/

/-- The grid kernel `Q_K(w) = Σ_{k ≤ K} w^k`. -/
def geomWin (K : ℕ) (w : ℂ) : ℂ := ∑ k ∈ Finset.range (K + 1), w ^ k

theorem geomWin_eq (K : ℕ) {w : ℂ} (hw : w ≠ 1) :
    geomWin K w = (w ^ (K + 1) - 1) / (w - 1) := geom_sum_eq hw (K + 1)

/-- `|Q_K(w)| ≤ (|w|^{K+1} + 1)/|1 − w|`. -/
theorem norm_geomWin_le_div (K : ℕ) {w : ℂ} (hw : w ≠ 1) :
    ‖geomWin K w‖ ≤ (‖w‖ ^ (K + 1) + 1) / ‖1 - w‖ := by
  rw [geomWin_eq K hw, norm_div, ← norm_neg (w - 1), neg_sub]
  gcongr
  refine (norm_sub_le _ _).trans_eq ?_
  simp [norm_pow]

/-- `|Q_K(w)| ≤ Σ_{k ≤ K} R^k` for `|w| ≤ R`. -/
theorem norm_geomWin_le_of_le (K : ℕ) {w : ℂ} {R : ℝ} (hR : ‖w‖ ≤ R) :
    ‖geomWin K w‖ ≤ ∑ k ∈ Finset.range (K + 1), R ^ k :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hR k)

/-- For real `x > 1`, `Q_K(x) = (x^{K+1} − 1)/(x − 1)`. -/
theorem norm_geomWin_ofReal_gt_one (K : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖geomWin K x‖ = (x ^ (K + 1) - 1) / (x - 1) := by
  have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
  rw [geomWin_eq K hx1, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact div_nonneg (by linarith [one_le_pow₀ (n := K + 1) hx.le]) (by linarith)

/-! ### The grid window of the lag function -/

/-- **The grid window, termwise.** `Σ_{k ≤ K} e^{−skℓ} φ(kℓ) = Σ_z D(z) Q_K(e^{(z − s)ℓ})`. -/
theorem sum_lagGrid_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (ℓ : ℝ) (K : ℕ) (s : ℂ) :
    ∑ k ∈ Finset.range (K + 1), cexp (-s * (k * ℓ : ℝ)) *
        ((2 * (lagStructure Z b (k * ℓ)).re : ℝ) : ℂ) =
      ∑' z : ℂ, evenCoeff Z b z * geomWin K (cexp ((z - s) * ℓ)) := by
  have hpow : ∀ (z : ℂ) (k : ℕ), cexp (-s * (k * ℓ : ℝ)) * cexp (z * (k * ℓ : ℝ)) =
      cexp ((z - s) * ℓ) ^ k := fun z k => by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ k : ℕ, cexp (-s * (k * ℓ : ℝ)) * ((2 * (lagStructure Z b (k * ℓ)).re : ℝ) : ℂ) =
      ∑' z : ℂ, evenCoeff Z b z * cexp ((z - s) * ℓ) ^ k := fun k => by
    rw [(two_re_lagStructure_eq Z hZ hb hbs (k * ℓ)).2, ← tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [← hpow z k]
    ring
  have hsum : ∀ k : ℕ, Summable fun z : ℂ => evenCoeff Z b z * cexp ((z - s) * ℓ) ^ k :=
    fun k => ((two_re_lagStructure_eq Z hZ hb hbs (k * ℓ)).1.mul_left
      (cexp (-s * (k * ℓ : ℝ)))).congr fun z => by rw [← hpow z k]; ring
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum fun k _ => hsum k]
  refine tsum_congr fun z => ?_
  rw [geomWin, Finset.mul_sum]

/-- **Positivity of the grid window.** For `g_k ≥ 0`, `|Σ_k g_k e^{−skℓ}| ≤ Σ_k g_k e^{−σkℓ}`,
`σ = Re s`, and the right side is real. -/
theorem norm_sum_cexp_mul_le (ℓ : ℝ) (K : ℕ) {g : ℕ → ℝ}
    (hg : ∀ k ∈ Finset.range (K + 1), 0 ≤ g k) (s : ℂ) :
    ‖∑ k ∈ Finset.range (K + 1), cexp (-s * (k * ℓ : ℝ)) * ((g k : ℝ) : ℂ)‖ ≤
      (∑ k ∈ Finset.range (K + 1), cexp (-(s.re : ℂ) * (k * ℓ : ℝ)) * ((g k : ℝ) : ℂ)).re := by
  have hreal : ∑ k ∈ Finset.range (K + 1), cexp (-(s.re : ℂ) * (k * ℓ : ℝ)) * ((g k : ℝ) : ℂ) =
      ((∑ k ∈ Finset.range (K + 1), Real.exp (-s.re * (k * ℓ)) * g k : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal, Complex.ofReal_re]
  refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun k hk => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg k hk)]
  congr 2
  simp

/-! ### The aliasing-potential law -/

/-- **Aliasing-potential law.** If the difference tests are Weil nonnegative at the grid lags
`kℓ`, `0 ≤ k ≤ K`, then for every exponent `z₀` and `s = σ + it`, with `M = 2 Re S(0)`:
`|D(z₀) Q_K(e^{(z₀−s)ℓ})| ≤ |M|(|Q_K(e^{−σℓ})| + |Q_K(e^{−sℓ})|) + Σ_z |D(z)||Q_K(e^{(z−σ)ℓ})|
  + Σ_{z ≠ z₀} |D(z)||Q_K(e^{(z−s)ℓ})|`. -/
theorem norm_evenCoeff_mul_geomWin_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (ℓ : ℝ) (K : ℕ)
    (hm : ∀ k ∈ Finset.range (K + 1),
      0 ≤ (Z.W (twoBump b (k * ℓ) (-1)) (twoBump b (k * ℓ) (-1))).re)
    (z₀ : ℂ) (σ t : ℝ) :
    ‖evenCoeff Z b z₀ * geomWin K (cexp ((z₀ - (σ + t * I)) * ℓ))‖ ≤
      |2 * (lagStructure Z b 0).re| * (‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ +
        ‖geomWin K (cexp (-(σ + t * I) * ℓ))‖) +
      ∑' z : ℂ, ‖evenCoeff Z b z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ +
      ∑' z : ℂ, (if z = z₀ then 0 else
        ‖evenCoeff Z b z‖ * ‖geomWin K (cexp ((z - (σ + t * I)) * ℓ))‖) := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  set φ : ℕ → ℝ := fun k => 2 * (lagStructure Z b (k * ℓ)).re with hφ
  have hg : ∀ k ∈ Finset.range (K + 1), 0 ≤ M - φ k := fun k hk => by
    have := hm k hk
    rwa [re_W_lag_eq Z hZ hb hbs] at this
  -- `G(e^{−sℓ}) = M Q_K(e^{−sℓ}) − Σ_z D(z) Q_K(e^{(z−s)ℓ})`
  have hG : ∀ s : ℂ, ∑ k ∈ Finset.range (K + 1), cexp (-s * (k * ℓ : ℝ)) * ((M - φ k : ℝ) : ℂ) =
      M * geomWin K (cexp (-s * ℓ)) - ∑' z : ℂ, D z * geomWin K (cexp ((z - s) * ℓ)) := by
    intro s
    have e : ∀ k : ℕ, cexp (-s * (k * ℓ : ℝ)) * ((M - φ k : ℝ) : ℂ) =
        M * cexp (-s * ℓ) ^ k - cexp (-s * (k * ℓ : ℝ)) * ((φ k : ℝ) : ℂ) := fun k => by
      rw [← Complex.exp_nat_mul]
      push_cast
      ring_nf
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_lagGrid_eq Z hZ hb hbs ℓ K s, geomWin]
  have hbound : ∀ s : ℂ, ∀ z : ℂ, D z ≠ 0 →
      ‖geomWin K (cexp ((z - s) * ℓ))‖ ≤
        ∑ k ∈ Finset.range (K + 1), Real.exp ((1 / 2 + |s.re|) * |ℓ|) ^ k := fun s z hz =>
    norm_geomWin_le_of_le K (by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have e : ((z - s) * (ℓ : ℂ)).re = (z.re - s.re) * ℓ := by simp
      rw [e]
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
  have hsumL : ∀ s : ℂ, Summable fun z : ℂ => ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖ :=
    fun s => summable_norm_evenCoeff_mul Z hZ hb hbs (fun _ => norm_nonneg _) (hbound s)
  have hsumC : ∀ s : ℂ, Summable fun z : ℂ => D z * geomWin K (cexp ((z - s) * ℓ)) := fun s =>
    (hsumL s).of_norm_bounded fun z => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpos := norm_sum_cexp_mul_le ℓ K hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  have hsplit := (hsumC s).tsum_eq_add_tsum_ite z₀
  have hrest : ‖∑' z : ℂ, (if z = z₀ then 0 else D z * geomWin K (cexp ((z - s) * ℓ)))‖ ≤
      ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖) := by
    have hn : ∀ z : ℂ, ‖(if z = z₀ then 0 else D z * geomWin K (cexp ((z - s) * ℓ)))‖ =
        (if z = z₀ then 0 else ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖) := fun z => by
      split_ifs <;> simp
    have hs' : Summable fun z : ℂ =>
        (if z = z₀ then 0 else ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖) :=
      (hsumL s).of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        fun z => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : (M * geomWin K (cexp (-(σ : ℂ) * ℓ)) -
      ∑' z : ℂ, D z * geomWin K (cexp ((z - σ) * ℓ))).re ≤
      |M| * ‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ +
        ∑' z : ℂ, ‖D z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ := by
    rw [Complex.sub_re]
    have h1 : (M * geomWin K (cexp (-(σ : ℂ) * ℓ))).re ≤
        |M| * ‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' z : ℂ, D z * geomWin K (cexp ((z - σ) * ℓ))).re ≤
        ∑' z : ℂ, ‖D z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  set Gs := ∑ k ∈ Finset.range (K + 1), cexp (-s * (k * ℓ : ℝ)) * ((M - φ k : ℝ) : ℂ) with hGsdef
  set R := ∑' z : ℂ, (if z = z₀ then 0 else D z * geomWin K (cexp ((z - s) * ℓ))) with hRdef
  have hkey : D z₀ * geomWin K (cexp ((z₀ - s) * ℓ)) =
      M * geomWin K (cexp (-s * ℓ)) - Gs - R := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  have htri : ‖M * geomWin K (cexp (-s * ℓ)) - Gs - R‖ ≤
      ‖M * geomWin K (cexp (-s * ℓ))‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le (M * geomWin K (cexp (-s * ℓ))) Gs])
  have hMn : ‖(M : ℂ) * geomWin K (cexp (-s * ℓ))‖ = |M| * ‖geomWin K (cexp (-s * ℓ))‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ +
      ∑' z : ℂ, ‖D z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  linarith

/-! ### What replaces attainment on a grid -/

/-- `|Q_K(e^{wℓ})| ≤ (e^{Re w (K+1)ℓ} + 1)/g` when the aliasing gap `|1 − e^{wℓ}|` is at least `g > 0`. -/
theorem norm_geomWin_cexp_le {K : ℕ} {ℓ g : ℝ} {w : ℂ} (hg : 0 < g)
    (hgap : g ≤ ‖1 - cexp (w * ℓ)‖) :
    ‖geomWin K (cexp (w * ℓ))‖ ≤ (Real.exp (w.re * ((K + 1) * ℓ)) + 1) / g := by
  have hne : cexp (w * ℓ) ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hgap; linarith
  refine (norm_geomWin_le_div K hne).trans ?_
  have e : ‖cexp (w * ℓ)‖ ^ (K + 1) = Real.exp (w.re * ((K + 1) * ℓ)) := by
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_left (by positivity) hg hgap

/-- `|Q_K(ζ)| ≤ 2/(1 − |ζ|)` for `|ζ| < 1`. -/
theorem norm_geomWin_le_of_norm_lt_one (K : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖geomWin K ζ‖ ≤ 2 / (1 - ‖ζ‖) := by
  have hne : ζ ≠ 1 := fun h => by rw [h, norm_one] at hζ; exact lt_irrefl _ hζ
  refine (norm_geomWin_le_div K hne).trans ?_
  have h1 : 1 - ‖ζ‖ ≤ ‖1 - ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ζ; rwa [norm_one] at this
  have h2 : ‖ζ‖ ^ (K + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hζ.le
  calc (‖ζ‖ ^ (K + 1) + 1) / ‖1 - ζ‖ ≤ 2 / ‖1 - ζ‖ :=
        div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ 2 / (1 - ‖ζ‖) := div_le_div_of_nonneg_left (by norm_num) (by linarith) h1

/-- **Grid loudness bound.** Let the difference tests be Weil nonnegative at the lags `kℓ`,
`0 ≤ k ≤ K`, `ℓ > 0`, `V = (K+1)ℓ`. Let the aliasing gap to the real axis be
`|1 − e^{(z−σ)ℓ}| ≥ η` on the exponents, the aliasing gap of the others to `s = σ + i Im z₀` be
`|1 − e^{(z−s)ℓ}| ≥ g`, `κ = 1/η + 1/g`, `θ = Re z₀ − σ > 0` with `2κN(e^{θℓ} − 1) ≤ 1`, and the
loudness at lag `V` at most `N` times that of `z₀`. Then
`κ N |D(z₀)| (e^{θV} − 2) ≤ 4|M|/(1 − e^{−σℓ}) + κ Σ_z |D(z)|`. -/
theorem grid_loudness_bound_of_lag_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {ℓ : ℝ} (hℓ : 0 < ℓ) (K : ℕ)
    (hm : ∀ k ∈ Finset.range (K + 1),
      0 ≤ (Z.W (twoBump b (k * ℓ) (-1)) (twoBump b (k * ℓ) (-1))).re)
    {η g σ N : ℝ} {z₀ : ℂ} (hη : 0 < η)
    (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ ‖1 - cexp ((z - σ) * ℓ)‖) (hg : 0 < g)
    (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 →
      g ≤ ‖1 - cexp ((z - (σ + z₀.im * I)) * ℓ)‖)
    (hθN : 2 * (1 / η + 1 / g) * N * (Real.exp ((z₀.re - σ) * ℓ) - 1) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * ((K + 1) * ℓ)) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * ((K + 1) * ℓ))) :
    (1 / η + 1 / g) * N * ‖evenCoeff Z b z₀‖ * (Real.exp ((z₀.re - σ) * ((K + 1) * ℓ)) - 2) ≤
      4 * |2 * (lagStructure Z b 0).re| / (1 - Real.exp (-σ * ℓ)) +
        (1 / η + 1 / g) * ∑' z : ℂ, ‖evenCoeff Z b z‖ := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  set κ : ℝ := 1 / η + 1 / g with hκ
  set θ : ℝ := z₀.re - σ with hθdef
  set V : ℝ := (K + 1) * ℓ with hVdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  set s : ℂ := σ + z₀.im * I with hs
  have hcore := norm_evenCoeff_mul_geomWin_le Z hZ hb hbs ℓ K hm z₀ σ z₀.im
  rw [← hs] at hcore
  set r : ℝ := Real.exp (-σ * ℓ) with hr
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; nlinarith
  have hr0 : 0 < 1 - r := by linarith
  -- the kernel of `z₀` is real at `s`
  have hz₀s : cexp ((z₀ - s) * ℓ) = ((Real.exp (θ * ℓ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp [hs, hθdef]
  have hx1 : 1 < Real.exp (θ * ℓ) := Real.one_lt_exp_iff.mpr (mul_pos hθ0 hℓ)
  have hpowV : Real.exp (θ * ℓ) ^ (K + 1) = Real.exp (θ * V) := by
    rw [← Real.exp_nat_mul, hVdef]; congr 1; push_cast; ring
  have hLHS : ‖D z₀ * geomWin K (cexp ((z₀ - s) * ℓ))‖ =
      ‖D z₀‖ * ((Real.exp (θ * V) - 1) / (Real.exp (θ * ℓ) - 1)) := by
    rw [norm_mul, hz₀s, norm_geomWin_ofReal_gt_one K hx1, hpowV]
  -- the archimedean-pole kernels
  have hE1 : ‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ ≤ 2 / (1 - r) := by
    have hn : ‖cexp (-(σ : ℂ) * ℓ)‖ = r := by rw [Complex.norm_exp, hr]; simp
    have := norm_geomWin_le_of_norm_lt_one K (ζ := cexp (-(σ : ℂ) * ℓ)) (by rw [hn]; exact hr1)
    rwa [hn] at this
  have hE2 : ‖geomWin K (cexp (-s * ℓ))‖ ≤ 2 / (1 - r) := by
    have hn : ‖cexp (-s * ℓ)‖ = r := by rw [Complex.norm_exp, hr]; simp [hs]
    have := norm_geomWin_le_of_norm_lt_one K (ζ := cexp (-s * ℓ)) (by rw [hn]; exact hr1)
    rwa [hn] at this
  -- the potentials
  set T : ℝ := ∑' z : ℂ, ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) with hT
  have hsL : Summable fun z : ℂ => ‖D z‖ * Real.exp (z.re * V) :=
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := Real.exp (1 / 2 * V))
      (fun _ => (Real.exp_pos _).le) fun z hz => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (abs_re_le_of_evenCoeff_ne_zero hz)) hV0)
  have hsD := summable_norm_evenCoeff Z hZ hb hbs
  have hTeq : T = Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) +
      ∑' z : ℂ, ‖D z‖ := by
    rw [hT, ← tsum_mul_left, ← (hsL.mul_left _).tsum_add hsD]
    refine tsum_congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hsT : Summable fun z : ℂ => ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) := by
    refine ((hsL.mul_left (Real.exp (-σ * V))).add hsD).congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hkern : ∀ {z u : ℂ} {c : ℝ}, 0 < c → u.re = σ → c ≤ ‖1 - cexp ((z - u) * ℓ)‖ →
      ‖D z‖ * ‖geomWin K (cexp ((z - u) * ℓ))‖ ≤
        ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) / c := fun {z u c} hc hu hgap => by
    have := norm_geomWin_cexp_le (K := K) hc hgap
    rw [Complex.sub_re, hu, ← hVdef] at this
    calc ‖D z‖ * ‖geomWin K (cexp ((z - u) * ℓ))‖ ≤
          ‖D z‖ * ((Real.exp ((z.re - σ) * V) + 1) / c) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hP1 : ∑' z : ℂ, ‖D z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ ≤ T / η := by
    rw [hT, ← tsum_div_const]
    have hle : ∀ z : ℂ, ‖D z‖ * ‖geomWin K (cexp ((z - σ) * ℓ))‖ ≤
        ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) / η := fun z => by
      by_cases hz : D z = 0
      · simp [hz]
      · exact hkern hη (by simp) (hηz z hz)
    exact Summable.tsum_le_tsum hle ((hsT.div_const η).of_nonneg_of_le
      (fun _ => by positivity) hle) (hsT.div_const η)
  have hP2 : ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖) ≤
      T / g := by
    rw [hT, ← tsum_div_const]
    have hle : ∀ z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖geomWin K (cexp ((z - s) * ℓ))‖) ≤
        ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) / g := fun z => by
      split_ifs with hzz
      · positivity
      · by_cases hz : D z = 0
        · simp [hz]
        · exact hkern hg (by simp [hs]) (hsep z hzz hz)
    exact Summable.tsum_le_tsum hle ((hsT.div_const g).of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle) (hsT.div_const g)
  have hTb : T ≤ N * ‖D z₀‖ * Real.exp (θ * V) + ∑' z : ℂ, ‖D z‖ := by
    rw [hTeq]
    have h1 : Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) ≤
        N * ‖D z₀‖ * Real.exp (θ * V) := by
      calc Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V)
          ≤ Real.exp (-σ * V) * (N * ‖D z₀‖ * Real.exp (z₀.re * V)) :=
            mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
        _ = N * ‖D z₀‖ * Real.exp (θ * V) := by
            rw [hθdef, show (z₀.re - σ) * V = -σ * V + z₀.re * V by ring, Real.exp_add]; ring
    linarith
  -- assemble
  have hbig : ‖D z₀‖ * ((Real.exp (θ * V) - 1) / (Real.exp (θ * ℓ) - 1)) ≤
      4 * |M| / (1 - r) + κ * T := by
    rw [← hLHS]
    refine hcore.trans ?_
    have hM0 := abs_nonneg M
    have h1 : |M| * (‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ + ‖geomWin K (cexp (-s * ℓ))‖) ≤
        4 * |M| / (1 - r) := by
      calc |M| * (‖geomWin K (cexp (-(σ : ℂ) * ℓ))‖ + ‖geomWin K (cexp (-s * ℓ))‖) ≤
            |M| * (2 / (1 - r) + 2 / (1 - r)) :=
            mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) hM0
        _ = 4 * |M| / (1 - r) := by ring
    have h2 : T / η + T / g = κ * T := by rw [hκ]; ring
    linarith
  have hexp : 0 ≤ Real.exp (θ * V) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hθ0.le hV0)]
  have hd0 : 0 < Real.exp (θ * ℓ) - 1 := by linarith
  have hlow : 2 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1) ≤
      ‖D z₀‖ * ((Real.exp (θ * V) - 1) / (Real.exp (θ * ℓ) - 1)) := by
    have h1 : 2 * κ * N ≤ 1 / (Real.exp (θ * ℓ) - 1) := by
      rw [le_div_iff₀ hd0]; linarith
    calc 2 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1)
        = (2 * κ * N) * (‖D z₀‖ * (Real.exp (θ * V) - 1)) := by ring
      _ ≤ (1 / (Real.exp (θ * ℓ) - 1)) * (‖D z₀‖ * (Real.exp (θ * V) - 1)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg _) hexp)
      _ = _ := by ring
  have hκT : κ * T ≤ κ * (N * ‖D z₀‖ * Real.exp (θ * V)) + κ * ∑' z : ℂ, ‖D z‖ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hTb hκ0.le
  nlinarith

/-- **Explicit first negative grid lag.** Under the hypotheses of
`grid_loudness_bound_of_lag_nonneg` with `V = (K+1)ℓ`, if
`κ N |D(z₀)| (e^{θV} − 2) > 4|M|/(1 − e^{−σℓ}) + κ Σ_z |D(z)|`, then some grid lag `kℓ`,
`0 ≤ k ≤ K`, has `Re W(f_{kℓ}, f_{kℓ}) < 0`. -/
theorem exists_grid_lag_neg_of_loudness (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {ℓ : ℝ} (hℓ : 0 < ℓ) (K : ℕ)
    {η g σ N : ℝ} {z₀ : ℂ} (hη : 0 < η)
    (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ ‖1 - cexp ((z - σ) * ℓ)‖) (hg : 0 < g)
    (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 →
      g ≤ ‖1 - cexp ((z - (σ + z₀.im * I)) * ℓ)‖)
    (hθN : 2 * (1 / η + 1 / g) * N * (Real.exp ((z₀.re - σ) * ℓ) - 1) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * ((K + 1) * ℓ)) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * ((K + 1) * ℓ)))
    (hbig : 4 * |2 * (lagStructure Z b 0).re| / (1 - Real.exp (-σ * ℓ)) +
        (1 / η + 1 / g) * ∑' z : ℂ, ‖evenCoeff Z b z‖ <
      (1 / η + 1 / g) * N * ‖evenCoeff Z b z₀‖ *
        (Real.exp ((z₀.re - σ) * ((K + 1) * ℓ)) - 2)) :
    ∃ k ∈ Finset.range (K + 1),
      (Z.W (twoBump b (k * ℓ) (-1)) (twoBump b (k * ℓ) (-1))).re < 0 := by
  by_contra h
  push Not at h
  exact (grid_loudness_bound_of_lag_nonneg Z hZ hb hbs hℓ K h hη hηz hg hσ hθ hsep hθN
    hL).not_gt hbig

/-- **The grid crowding law for `ζ`.** If the dyadic window functionals of a width
`w ∈ (0, ½ log 2)` are nonnegative at the lags `kℓ`, `0 ≤ k ≤ K`, then every exponent `z₀` with
aliasing gaps `η` (to the real axis) and `g` (of the others to `σ + i Im z₀`), `κ = 1/η + 1/g`,
`2κN(e^{(Re z₀ − σ)ℓ} − 1) ≤ 1` and loudness ratio `N` at lag `(K+1)ℓ` satisfies
`κ N |D(z₀)| (e^{(Re z₀ − σ)(K+1)ℓ} − 2) ≤ 4|M|/(1 − e^{−σℓ}) + κ Σ|D|`. -/
theorem zeta_grid_crowding_of_lag_primeWindow_nonneg {w ℓ : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) (hℓ : 0 < ℓ) (K : ℕ)
    (hP : ∀ k ∈ Finset.range (K + 1), 0 ≤ (lagPrimeWindowRHS (k * ℓ) w (EF.weilTest
      (twoBump (modScaledBump w 0) (k * ℓ) (-1)) (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re)
    {η g σ N : ℝ} {z₀ : ℂ} (hη : 0 < η)
    (hηz : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      η ≤ ‖1 - cexp ((z - σ) * ℓ)‖) (hg : 0 < g) (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      g ≤ ‖1 - cexp ((z - (σ + z₀.im * I)) * ℓ)‖)
    (hθN : 2 * (1 / η + 1 / g) * N * (Real.exp ((z₀.re - σ) * ℓ) - 1) ≤ 1)
    (hL : ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ *
        Real.exp (z.re * ((K + 1) * ℓ)) ≤
      N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ * Real.exp (z₀.re * ((K + 1) * ℓ))) :
    (1 / η + 1 / g) * N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ *
        (Real.exp ((z₀.re - σ) * ((K + 1) * ℓ)) - 2) ≤
      4 * |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| /
          (1 - Real.exp (-σ * ℓ)) +
        (1 / η + 1 / g) * ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ := by
  have hm : ∀ k ∈ Finset.range (K + 1), 0 ≤ (zetaZeroConfig.W
      (twoBump (modScaledBump w 0) (k * ℓ) (-1)) (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re :=
    fun k hk => by
      rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) (k * ℓ) (-1)),
        literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2
          (by positivity)]
      exact hP k hk
  exact grid_loudness_bound_of_lag_nonneg zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0) hℓ K hm hη hηz hg hσ hθ hsep
    hθN hL

end GaloisForLFunctions.SquareRootThreshold
