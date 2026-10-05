import GaloisForLFunctions.RHTower.WeilBoundaryFractionalCountingTwin

/-!
# Rational counting with atoms anywhere: the completed exponential is `K · P · Q`

Let `lam` be full-cone Weil-positive with boundary measure `μ` and `k ≥ 1` with `k μ((a,b]) ∈ ℕ`
for `a < b` in a set of full measure.  No gap near the centre is assumed.

**Theorem** (`bigG_pow_eq_of_fractional_counting`).  There are a finite symmetric set `F ⊂ (−1, 1)`
with symmetric multiplicities `n`, and integers `m_j` at ordinates `t_j ≥ 1` with `Σ m_j/t_j² < ∞`,
such that on `Re s > 1`

`G(s)^k = K · P(s) · Q(s)`,   `P(s) = ∏_{x ∈ F} (s − ½ − ix)^{n_x}`,  `Q = atomQ m t`,

where `G(s) = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)`.  The polynomial `P` satisfies
`P(1 − s) = (−1)^{Σ n_x} P(s)` (`atomPoly_one_sub`) and `|P(σ + iτ)|` increases in `σ ≥ 1/2`
(`norm_atomPoly_le_two`).

**Proof.**
* The atoms of `μ` in `(−1, 1)` have mass at least `1/k` and `μ(−1, 1) < ∞`, so they are finitely
  many; the rest of `μ` has no mass on `(−1, 1)` and is the corpus atomic measure.
* The Poisson representation splits accordingly, and the Weil function is the atomic Herglotz
  series of the large atoms plus `Σ_{x ∈ F} (n_x/k)/(s − ½ − ix)` (`weilFunction_eq_atomicPairSeries_add`).
* `(G^k)'/G^k = k Φ = Q'/Q + P'/P`, so `G^k/(PQ)` is constant (`bigG_pow_eq_mul_atomPoly_atomQ`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal NNReal
open Zeta23 GaloisForLFunctions

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity

/-! ## The polynomial of the small atoms -/

/-- `P(s) = ∏_{x ∈ F} (s − ½ − ix)^{n_x}`. -/
def atomPoly (F : Finset ℝ) (n : ℝ → ℕ) (s : ℂ) : ℂ :=
  ∏ x ∈ F, (s - (1 / 2 + (x : ℂ) * I)) ^ n x

theorem differentiable_atomPoly (F : Finset ℝ) (n : ℝ → ℕ) : Differentiable ℂ (atomPoly F n) := by
  unfold atomPoly
  fun_prop

theorem sub_atom_ne_zero {s : ℂ} (hs : s.re ≠ 1 / 2) (x : ℝ) : s - (1 / 2 + (x : ℂ) * I) ≠ 0 := by
  intro h
  apply hs
  have := congrArg Complex.re h
  simp at this
  linarith

theorem atomPoly_ne_zero (F : Finset ℝ) (n : ℝ → ℕ) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    atomPoly F n s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (sub_atom_ne_zero hs x)

theorem logDeriv_atomPoly (F : Finset ℝ) (n : ℝ → ℕ) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    logDeriv (atomPoly F n) s = ∑ x ∈ F, (n x : ℂ) / (s - (1 / 2 + (x : ℂ) * I)) := by
  unfold atomPoly
  rw [logDeriv_prod (𝕜 := ℂ) (s := F) (f := fun x (z : ℂ) => (z - (1 / 2 + (x : ℂ) * I)) ^ n x)
    (fun x _ => pow_ne_zero _ (sub_atom_ne_zero hs x)) (fun x _ => by fun_prop)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [logDeriv_fun_pow (by fun_prop) (n x), logDeriv_apply, deriv_sub_const, deriv_id'']
  ring

/-- `P(1 − s) = (−1)^{Σ n_x} P(s)` for a symmetric configuration. -/
theorem atomPoly_one_sub (F : Finset ℝ) (n : ℝ → ℕ) (hF : ∀ x ∈ F, -x ∈ F)
    (hn : ∀ x, n (-x) = n x) (s : ℂ) :
    atomPoly F n (1 - s) = (-1) ^ (∑ x ∈ F, n x) * atomPoly F n s := by
  unfold atomPoly
  have h1 : ∀ x ∈ F, (1 - s - (1 / 2 + (x : ℂ) * I)) ^ n x =
      (-1) ^ n x * (s - (1 / 2 + ((-x : ℝ) : ℂ) * I)) ^ n x := by
    intro x _
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_nbij' (fun x => -x) (fun x => -x) (fun x hx => hF x hx) (fun x hx => hF x hx)
    (fun x _ => neg_neg x) (fun x _ => neg_neg x) (fun x _ => ?_)
  rw [hn]

/-- `|s − ½ − ix|` increases in `Re s ≥ 1/2`. -/
theorem norm_sub_atom_le {σ : ℝ} (τ x : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 2) :
    ‖(σ : ℂ) + τ * I - (1 / 2 + (x : ℂ) * I)‖ ≤ ‖(2 : ℂ) + τ * I - (1 / 2 + (x : ℂ) * I)‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_zero, add_zero, sub_im, add_im, mul_im, zero_add, one_div]
  norm_num
  nlinarith

/-- `|P(σ + iτ)| ≤ |P(2 + iτ)|` for `1/2 ≤ σ ≤ 2`. -/
theorem norm_atomPoly_le_two (F : Finset ℝ) (n : ℝ → ℕ) {σ : ℝ} (τ : ℝ) (h1 : 1 / 2 ≤ σ)
    (h2 : σ ≤ 2) : ‖atomPoly F n (σ + τ * I)‖ ≤ ‖atomPoly F n (2 + τ * I)‖ := by
  unfold atomPoly
  rw [norm_prod, norm_prod]
  refine Finset.prod_le_prod (fun x _ => norm_nonneg _) (fun x _ => ?_)
  rw [norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_atom_le τ x h1 h2) _

/-! ## The Weil function with finitely many extra atoms -/

/-- `Σ_{x ∈ F} d_x/(s − ½ − ix)`. -/
def smallSeries (F : Finset ℝ) (d : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑ x ∈ F, (d x : ℂ) / (s - (1 / 2 + (x : ℂ) * I))

theorem differentiableAt_smallSeries (F : Finset ℝ) (d : ℝ → ℝ) {s : ℂ} (hs : s.re ≠ 1 / 2) :
    DifferentiableAt ℂ (smallSeries F d) s := by
  unfold smallSeries
  refine DifferentiableAt.fun_sum fun x _ => ?_
  exact (differentiableAt_const _).div (by fun_prop) (sub_atom_ne_zero hs x)

theorem re_div_sub_atom {w : ℂ} (x : ℝ) (dx : ℝ) :
    ((dx : ℂ) / (w + 1 / 2 - (1 / 2 + (x : ℂ) * I))).re = w.re * (dx * ‖1 / (w - I * x)‖ ^ 2) := by
  have hz : w + 1 / 2 - (1 / 2 + (x : ℂ) * I) = w - I * x := by ring
  rw [hz]
  rw [div_eq_mul_inv, Complex.re_ofReal_mul, one_div, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq,
    Complex.inv_re]
  simp only [sub_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_zero]
  ring

/-- **The atomic identity with finitely many extra atoms.** -/
theorem weilFunction_eq_atomicPairSeries_add {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => c j / t j ^ 2) (F : Finset ℝ) (d : ℝ → ℝ) (hd : ∀ x, 0 ≤ d x)
    (hF : ∀ x ∈ F, -x ∈ F) (hdsym : ∀ x, d (-x) = d x)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
        ∑ x ∈ F, ENNReal.ofReal (d x) * poissonDensity w x) :
    ∀ s : ℂ, 1 < s.re →
      weilFunction lam s = atomicPairSeries (fun j => Real.pi * c j) t s + smallSeries F d s := by
  set A := atomicPairSeries (fun j => Real.pi * c j) t with hA
  have hsumA : Summable fun j => |Real.pi * c j| / t j ^ 2 := by
    refine (hsum.mul_left Real.pi).congr fun j => ?_
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (hc j))]
    ring
  -- equality of real parts on `Re s > 1`
  have hre : ∀ s : ℂ, 1 < s.re → (weilFunction lam s).re = (A s + smallSeries F d s).re := by
    intro s hs
    set w : ℂ := s - 1 / 2 with hwdef
    have hw0 : 0 < w.re := by rw [hwdef]; norm_num; linarith
    have hP := lintegral_poissonDensity_eq hW hs
    rw [← hwdef, hrep w hw0] at hP
    have hΦ0 : 0 ≤ (weilFunction lam s).re / w.re :=
      div_nonneg (re_weilFunction_nonneg hW hs) hw0.le
    have hfin : ∀ j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))
        ≠ ⊤ := fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.mpr ⟨poissonDensity_ne_top _ _, poissonDensity_ne_top _ _⟩)
    have hfinF : ∀ x ∈ F, ENNReal.ofReal (d x) * poissonDensity w x ≠ ⊤ := fun x _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (poissonDensity_ne_top _ _)
    have hT : (∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
        ≠ ⊤ := by
      intro h
      rw [h, top_add] at hP
      exact ENNReal.ofReal_ne_top hP.symm
    have hreal := congrArg ENNReal.toReal hP
    rw [ENNReal.toReal_add hT (ENNReal.sum_ne_top.mpr hfinF), ENNReal.tsum_toReal_eq hfin,
      ENNReal.toReal_sum hfinF, ENNReal.toReal_ofReal hΦ0] at hreal
    have hterm : ∀ j, (ENNReal.ofReal (c j) * (poissonDensity w (t j) +
        poissonDensity w (-(t j)))).toReal =
        c j * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 + ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
      intro j
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc j),
        ENNReal.toReal_add (poissonDensity_ne_top _ _) (poissonDensity_ne_top _ _)]
      congr 1
    have htermF : ∀ x ∈ F, (ENNReal.ofReal (d x) * poissonDensity w x).toReal =
        d x * ‖1 / (w - I * (x : ℂ))‖ ^ 2 := by
      intro x _
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hd x)]
      congr 1
    simp_rw [hterm] at hreal
    rw [Finset.sum_congr rfl htermF] at hreal
    have hAre : (A s).re = w.re * ∑' j, c j * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 +
        ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
      have hAeq : A s = ∑' j, ((c j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        rw [hA, atomicPairSeries, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        rw [← hwdef]
        push_cast
        field_simp
      have hsumC : Summable fun j => ((c j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
        refine Summable.of_norm_bounded
          ((hsum.mul_left (2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2)))) fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
        have := norm_two_mul_div_le hw0 (hone j)
        calc c j * ‖2 * w / (w ^ 2 + (t j : ℂ) ^ 2)‖
            ≤ c j * (2 * ‖w‖ * ((4 + 4 * w.im ^ 2 / w.re ^ 2) / t j ^ 2)) :=
              mul_le_mul_of_nonneg_left this (hc j)
          _ = 2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2) * (c j / t j ^ 2) := by ring
      rw [hAeq, Complex.re_tsum hsumC, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [Complex.re_ofReal_mul, re_two_mul_div hw0]
      ring
    have hSre : (smallSeries F d s).re = w.re * ∑ x ∈ F, d x * ‖1 / (w - I * (x : ℂ))‖ ^ 2 := by
      unfold smallSeries
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hs' : s = w + 1 / 2 := by rw [hwdef]; ring
      rw [hs', re_div_sub_atom]
    rw [Complex.add_re, hAre, hSre, ← mul_add, hreal, mul_div_assoc', mul_div_cancel_left₀ _ hw0.ne']
  -- the difference is constant on `Re s > 1`
  set U : Set ℂ := {z | 1 < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  have hAd := differentiableOn_atomicPairSeries hone hsumA
  have hgd : DifferentiableOn ℂ (fun z => weilFunction lam z - (A z + smallSeries F d z)) U := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hAz : DifferentiableAt ℂ A z := hAd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        show 1 / 2 < z.re; linarith))
    have hSz := differentiableAt_smallSeries F d (s := z) (by intro h; rw [h] at hz'; norm_num at hz')
    exact ((differentiableAt_weilFunction hW hz').sub (hAz.add hSz)).differentiableWithinAt
  have hgre : ∀ z ∈ U, (weilFunction lam z - (A z + smallSeries F d z)).re = 0 := by
    intro z hz
    rw [Complex.sub_re, hre z hz, sub_self]
  have h2U : (2 : ℂ) ∈ U := by show 1 < (2 : ℂ).re; norm_num
  -- the constant is real at `s = 2`, hence zero
  have him : (weilFunction lam 2 - (A 2 + smallSeries F d 2)).im = 0 := by
    have hL : (LSeries (lamC lam) 2).im = 0 := by
      rw [LSeries, Complex.im_tsum (summable_term_lamC hW (by norm_num))]
      refine (tsum_congr fun n => ?_).trans tsum_zero
      rw [LSeries.term_def]
      split_ifs with hn
      · simp
      · rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, lamC]
        rw [show ((n : ℂ) ^ 2) = (((n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_div]
        exact Complex.ofReal_im _
    have hA2 : (A 2).im = 0 := by
      rw [hA, atomicPairSeries]
      have hreal : (∑' j, ((Real.pi * c j : ℝ) : ℂ) / ((2 - 1 / 2) ^ 2 + (t j : ℂ) ^ 2)) =
          ((∑' j, (Real.pi * c j) / ((3 / 2) ^ 2 + t j ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        refine tsum_congr fun j => ?_
        push_cast
        ring
      rw [hreal]
      have : (2 * ((2 : ℂ) - 1 / 2) / (Real.pi : ℂ)) = ((2 * (3 / 2) / Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_im]
    have hS2 : (smallSeries F d 2).im = 0 := by
      have hsum2 : smallSeries F d 2 = (starRingEnd ℂ) (smallSeries F d 2) := by
        unfold smallSeries
        rw [map_sum]
        refine Finset.sum_nbij' (fun x => -x) (fun x => -x) (fun x hx => hF x hx)
          (fun x hx => hF x hx) (fun x _ => neg_neg x) (fun x _ => neg_neg x) (fun x _ => ?_)
        rw [map_div₀, Complex.conj_ofReal, hdsym]
        congr 1
        rw [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        simp only [map_ofNat, map_div₀, map_one]
        push_cast
        ring
      have := congrArg Complex.im hsum2
      rw [Complex.conj_im] at this
      linarith
    rw [Complex.sub_im, Complex.add_im, hA2, hS2, weilFunction]
    simp only [Complex.sub_im, Complex.add_im, hL]
    rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.digamma_one]
    simp
  have hzero : weilFunction lam 2 - (A 2 + smallSeries F d 2) = 0 :=
    Complex.ext (by rw [hgre 2 h2U]; rfl) (by rw [him]; rfl)
  intro s hs
  have hc' := eq_of_re_eq_zero hU hUc hgd hgre hs h2U
  rw [hzero, sub_eq_zero] at hc'
  exact hc'

/-! ## `G^k = K P Q` -/

theorem smallSeries_div_mul (F : Finset ℝ) (n : ℝ → ℕ) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (k : ℂ) * smallSeries F (fun x => (n x : ℝ) / k) s =
      ∑ x ∈ F, (n x : ℂ) / (s - (1 / 2 + (x : ℂ) * I)) := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold smallSeries
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  field_simp

/-- **`G^k = K P Q` on `Re s > 1`.** -/
theorem bigG_pow_eq_mul_atomPoly_atomQ {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {k : ℕ}
    (hk : 0 < k) (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) (F : Finset ℝ)
    (n : ℝ → ℕ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / k) t s +
        smallSeries F (fun x => (n x : ℝ) / k) s)
    {s : ℂ} (hs : 1 < s.re) :
    bigG lam s ^ k = (bigG lam 2 ^ k / (atomPoly F n 2 * atomQ m t 2)) *
      (atomPoly F n s * atomQ m t s) := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := convex_halfSpace_re_gt 1
  set R : ℂ → ℂ := fun z => atomPoly F n z * atomQ m t z with hR
  have hRd : Differentiable ℂ R := (differentiable_atomPoly F n).mul (differentiable_atomQ hone hsum)
  have hre_ne : ∀ z ∈ V, z.re ≠ 1 / 2 := fun z hz => by
    have : (1 : ℝ) < z.re := hz; intro h; rw [h] at this; norm_num at this
  have hRne : ∀ z ∈ V, R z ≠ 0 := fun z hz =>
    mul_ne_zero (atomPoly_ne_zero F n (hre_ne z hz))
      (atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (hre_ne z hz)))
  set r : ℂ → ℂ := fun z => bigG lam z ^ k / R z with hr
  have hGk : ∀ z : ℂ, 1 < z.re → HasDerivAt (fun w => bigG lam w ^ k)
      ((k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z * (1 / z + 1 / (z - 1) +
        gammaRealLogConnection z - LSeries (lamTwo lam) z))) z := by
    intro z hz
    have h := (hasDerivAt_bigG hsl hz).pow k
    refine HasDerivAt.congr_deriv (f := fun w => bigG lam w ^ k) h ?_
    ring
  have hrd : DifferentiableOn ℂ r V := fun z hz =>
    ((hGk z hz).differentiableAt.div (hRd z) (hRne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_re_ne (hre_ne z hz)
    have hQne := atomQ_ne_zero hone hsum hz1
    have hPne := atomPoly_ne_zero F n (hre_ne z hz)
    have hLQ := logDeriv_atomQ hone hsum hz1
    have hLP := logDeriv_atomPoly F n (hre_ne z hz)
    have hLR : logDeriv R z = logDeriv (atomPoly F n) z + logDeriv (atomQ m t) z :=
      logDeriv_mul (f := atomPoly F n) (g := atomQ m t) z hPne hQne
        ((differentiable_atomPoly F n) z) ((differentiable_atomQ hone hsum) z)
    rw [hLQ, hLP, logDeriv_apply] at hLR
    have hR' : deriv R z = (∑ x ∈ F, (n x : ℂ) / (z - (1 / 2 + (x : ℂ) * I)) +
        atomicPairSeries (fun j => Real.pi * m j) t z) * R z := by
      rw [← hLR]; field_simp [hRne z hz]
    have hd : HasDerivAt r (((k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z * (1 / z + 1 / (z - 1) +
        gammaRealLogConnection z - LSeries (lamTwo lam) z)) * R z -
          bigG lam z ^ k * deriv R z) / R z ^ 2) z :=
      (hGk z hz').div (hRd z).hasDerivAt (hRne z hz)
    have hze : 1 / z + 1 / (z - 1) + gammaRealLogConnection z - LSeries (lamTwo lam) z =
        atomicPairSeries (fun j => Real.pi * m j / k) t z +
          smallSeries F (fun x => (n x : ℝ) / k) z := by
      rw [← hid z hz']
      unfold zetaArchimedeanDatum gammaRealLogConnection
      ring
    have hpow : (k : ℂ) * bigG lam z ^ (k - 1) * bigG lam z = (k : ℂ) * bigG lam z ^ k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]
      ring
    rw [hd.deriv, hR', hze, ← atomicPairSeries_div_mul m t hk z,
      ← smallSeries_div_mul F n hk z]
    simp only [Pi.zero_apply]
    rw [div_eq_zero_iff]
    left
    calc (k : ℂ) * bigG lam z ^ (k - 1) * (bigG lam z *
          (atomicPairSeries (fun j => Real.pi * m j / k) t z +
            smallSeries F (fun x => (n x : ℝ) / k) z)) * R z -
          bigG lam z ^ k * (((k : ℂ) * smallSeries F (fun x => (n x : ℝ) / k) z +
            (k : ℂ) * atomicPairSeries (fun j => Real.pi * m j / k) t z) * R z)
        = ((k : ℂ) * bigG lam z ^ (k - 1) * bigG lam z) *
            (atomicPairSeries (fun j => Real.pi * m j / k) t z +
              smallSeries F (fun x => (n x : ℝ) / k) z) * R z -
          (k : ℂ) * bigG lam z ^ k * (atomicPairSeries (fun j => Real.pi * m j / k) t z +
            smallSeries F (fun x => (n x : ℝ) / k) z) * R z := by ring
      _ = 0 := by rw [hpow]; ring
  have h2 : (2 : ℂ) ∈ V := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hc := hVo.is_const_of_deriv_eq_zero hVc.isPreconnected hrd hderiv hs h2
  simp only [hr] at hc
  have hRs := hRne s hs
  rw [div_eq_iff hRs] at hc
  rw [hc]

/-! ## Rational counting with atoms anywhere -/

/-- **Rational counting gives `G^k = K P Q`**, with no gap near the centre. -/
theorem bigG_pow_eq_of_fractional_counting {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℕ} (hk : 0 < k) {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      ∃ n : ℕ, (k : ℝ≥0∞) * boundaryMeasure hW (Ioc a b) = n) :
    ∃ (F : Finset ℝ) (n : ℝ → ℕ) (m : ℕ → ℕ) (t : ℕ → ℝ), (∀ x ∈ F, -x ∈ F) ∧
      (∀ x, n (-x) = n x) ∧ (∀ j, 1 ≤ t j) ∧ (Summable fun j => (m j : ℝ) / t j ^ 2) ∧
      ∀ s : ℂ, 1 < s.re → bigG lam s ^ k =
        (bigG lam 2 ^ k / (atomPoly F n 2 * atomQ m t 2)) * (atomPoly F n s * atomQ m t s) := by
  set μ := boundaryMeasure hW with hμ
  set ν : Measure ℝ := (k : ℝ≥0∞) • μ with hν
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hνapp : ∀ A, ν A = (k : ℝ≥0∞) * μ A := fun A => by simp [hν]
  have hfinν : ∀ a b : ℝ, ν (Ioo a b) ≠ ∞ := fun a b => by
    rw [hνapp]; exact ENNReal.mul_ne_top hktop (boundaryMeasure_Ioo_ne_top hW a b)
  have hcountν : ∀ a ∈ Y, ∀ b ∈ Y, a < b → ∃ n : ℕ, ν (Ioc a b) = n := fun a ha b hb hab => by
    obtain ⟨n, hn⟩ := hcount a ha b hb hab
    exact ⟨n, by rw [hνapp]; exact hn⟩
  obtain ⟨hSc, hSnull⟩ := atoms_countable_and_compl_null hfinν hY hcountν
  have hint : ∀ x, ∃ n : ℕ, ν {x} = n := fun x => by
    obtain ⟨_, _, _, _, _, hn⟩ := exists_isolating_interval hfinν hY hcountν x
    exact hn
  choose kk hkk using hint
  have hzero : ∀ A, μ A = 0 ↔ ν A = 0 := fun A => by
    rw [hνapp, mul_eq_zero]; simp [hk0]
  have hSet : {x : ℝ | μ {x} ≠ 0} = {x : ℝ | ν {x} ≠ 0} := by
    ext x; simp only [mem_setOf_eq, ne_eq, hzero]
  have hSc' : {x : ℝ | μ {x} ≠ 0}.Countable := hSet ▸ hSc
  have hSnull' : μ {x : ℝ | μ {x} ≠ 0}ᶜ = 0 := by rw [hzero, hSet]; exact hSnull
  have hsym : ∀ x : ℝ, μ {-x} = μ {x} := fun x => boundaryMeasure_singleton_neg hW x
  have hmass : ∀ x, μ {x} = ENNReal.ofReal ((kk x : ℝ) / k) := by
    intro x
    have h := hkk x
    rw [hνapp] at h
    rw [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ← h,
      mul_comm, ENNReal.mul_div_cancel_right hk0 hktop]
  have hkksym : ∀ x, kk (-x) = kk x := by
    intro x
    have h1 := hkk (-x)
    have h2 := hkk x
    rw [hνapp, hsym, ← hνapp] at h1
    exact_mod_cast h1.symm.trans h2
  -- the atoms near the centre are finitely many
  set I₁ : Set ℝ := Ioo (-1) 1 with hI₁
  have hI₁m : MeasurableSet I₁ := measurableSet_Ioo
  have hsmall : {x : ℝ | x ∈ I₁ ∧ μ {x} ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (hfinν (-1) 1)
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have hT1 : ∀ x ∈ T, (1 : ℝ≥0∞) ≤ ν {x} := by
      intro x hx
      have hx' := (hTsub hx).2
      rw [hkk x]
      have : kk x ≠ 0 := by
        intro h0
        apply hx'
        rw [hzero, hkk x, h0, Nat.cast_zero]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hle : (N : ℝ≥0∞) ≤ ν (T : Set ℝ) := by
      rw [← sum_measure_singleton]
      calc (N : ℝ≥0∞) = ∑ _x ∈ T, (1 : ℝ≥0∞) := by simp [hTcard]
        _ ≤ ∑ x ∈ T, ν {x} := Finset.sum_le_sum hT1
    have hsub : (T : Set ℝ) ⊆ I₁ := fun x hx => (hTsub hx).1
    have := hle.trans (measure_mono hsub)
    exact absurd (this.trans_lt hN) (lt_irrefl _)
  set F := hsmall.toFinset with hF
  have hFmem : ∀ x, x ∈ F ↔ x ∈ I₁ ∧ μ {x} ≠ 0 := fun x => Set.Finite.mem_toFinset _
  have hI₁neg : ∀ x, -x ∈ I₁ ↔ x ∈ I₁ := fun x => by
    simp only [hI₁, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hFsym : ∀ x ∈ F, -x ∈ F := by
    intro x hx
    rw [hFmem] at hx ⊢
    exact ⟨(hI₁neg x).mpr hx.1, by rw [hsym]; exact hx.2⟩
  -- the measure away from the centre
  set μb := μ.restrict I₁ᶜ with hμb_def
  have hμb : ∀ x, μb {x} = if x ∈ I₁ then 0 else μ {x} := by
    intro x
    rw [hμb_def, Measure.restrict_apply (measurableSet_singleton x)]
    split_ifs with h
    · rw [Set.singleton_inter_of_notMem (by simpa using h), measure_empty]
    · rw [Set.singleton_inter_of_mem (by simpa using h)]
  have hScb : {x : ℝ | μb {x} ≠ 0}.Countable := hSc'.mono fun x hx => by
    simp only [mem_setOf_eq, hμb] at hx ⊢
    split_ifs at hx with h
    · exact absurd rfl hx
    · exact hx
  have hSnullb : μb {x : ℝ | μb {x} ≠ 0}ᶜ = 0 := by
    rw [hμb_def, Measure.restrict_apply hScb.measurableSet.compl]
    refine measure_mono_null (fun x hx => ?_) hSnull'
    simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_not, hμb] at hx ⊢
    rw [if_neg hx.2] at hx
    exact hx.1
  have hsymb : ∀ x : ℝ, μb {-x} = μb {x} := by
    intro x
    rw [hμb, hμb, hsym]
    simp only [hI₁neg]
  have hgapb : μb (Ioo (-1) 1) = 0 := by
    rw [hμb_def, Measure.restrict_apply measurableSet_Ioo, ← hI₁, Set.inter_compl_self, measure_empty]
  have hreprb := lintegral_eq_tsum_pos_atoms hScb hSnullb hsymb hgapb
  -- the measure near the centre
  have hrepr_small : ∀ g : ℝ → ℝ≥0∞, ∫⁻ r in I₁, g r ∂μ = ∑ x ∈ F, g x * μ {x} := by
    intro g
    have hae : ∀ᵐ r ∂μ.restrict I₁, r ∈ (F : Set ℝ) := by
      rw [ae_restrict_iff' hI₁m]
      refine measure_mono_null (fun r hr => ?_) hSnull'
      rw [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp, Finset.mem_coe] at hr
      simp only [mem_compl_iff, mem_setOf_eq, not_not]
      by_contra hne
      exact hr.2 ((hFmem r).mpr ⟨hr.1, hne⟩)
    rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_finset]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Measure.restrict_apply (measurableSet_singleton x),
      Set.singleton_inter_of_mem ((hFmem x).mp hx).1]
  have hsplit : ∀ g : ℝ → ℝ≥0∞, ∫⁻ r, g r ∂μ = ∫⁻ r, g r ∂μb + ∑ x ∈ F, g x * μ {x} := by
    intro g
    rw [← lintegral_add_compl g hI₁m, hrepr_small, add_comm]
  -- the large atoms
  set P := {x : ℝ | μb {x} ≠ 0 ∧ 0 < x} with hP
  have hPc : P.Countable := hScb.mono fun x hx => hx.1
  have hPout : ∀ x ∈ P, x ∉ I₁ := by
    intro x hx h
    have := hx.1
    rw [hμb, if_pos h] at this
    exact this rfl
  have hP1 : ∀ x ∈ P, 1 ≤ x := by
    intro x hx
    by_contra h
    exact hPout x hx ⟨by linarith [hx.2], lt_of_not_ge h⟩
  have hmassb : ∀ x ∈ P, μb {x} = ENNReal.ofReal ((kk x : ℝ) / k) := by
    intro x hx
    rw [hμb, if_neg (hPout x hx), hmass]
  haveI : Encodable P := hPc.toEncodable
  set t : ℕ → ℝ := fun j => (Encodable.decode₂ P j).elim 1 fun x => (x : ℝ) with ht
  set m : ℕ → ℕ := fun j => (Encodable.decode₂ P j).elim 0 fun x => kk x with hm
  have hone : ∀ j, 1 ≤ t j := by
    intro j
    simp only [ht]
    rcases Encodable.decode₂ P j with _ | x
    · simp
    · exact hP1 x x.2
  have hsum : Summable fun j => (m j : ℝ) / t j ^ 2 := by
    have hconv : (fun j => (m j : ℝ) / t j ^ 2) =
        fun j => (m j : ℝ) * (fun r : ℝ => 1 / r ^ 2) (t j) := by
      funext j; simp [div_eq_mul_inv]
    rw [hconv]
    refine (summable_decode₂_iff (fun x : P => kk x) (fun r : ℝ => 1 / r ^ 2)).mpr ?_
    set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / (1 + r ^ 2)) with hg
    have hfinite : ∑' x : P, (g x + g (-x)) * μb {(x : ℝ)} ≠ ∞ := by
      rw [← hreprb g]
      exact (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl)
        (lintegral_inv_one_add_sq_lt_top hW)).ne
    have hsumE := ENNReal.summable_toReal hfinite
    have hterm : ∀ x : P, ((g x + g (-x)) * μb {(x : ℝ)}).toReal =
        (kk x : ℝ) * (2 / k * (1 / (1 + (x : ℝ) ^ 2))) := by
      intro x
      simp only [hg, neg_sq]
      rw [hmassb x x.2, ENNReal.toReal_mul,
        ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
      field_simp
      ring
    simp_rw [hterm] at hsumE
    have hsumE' : Summable fun x : P => (kk x : ℝ) * (2 * (1 / (1 + (x : ℝ) ^ 2))) := by
      refine (hsumE.mul_left (k : ℝ)).congr fun x => ?_
      field_simp
    refine hsumE'.of_nonneg_of_le (fun x => by positivity) fun x => ?_
    have hx1 := hP1 x x.2
    have hk0' : (0 : ℝ) ≤ kk x := Nat.cast_nonneg _
    apply mul_le_mul_of_nonneg_left _ hk0'
    show 1 / (x : ℝ) ^ 2 ≤ 2 * (1 / (1 + (x : ℝ) ^ 2))
    have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the Poisson representation
  have hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal ((m j : ℝ) / k) *
        (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
      ∑ x ∈ F, ENNReal.ofReal ((kk x : ℝ) / k) * poissonDensity w x := by
    intro w _
    rw [← hμ, hsplit, hreprb fun r => poissonDensity w r]
    congr 1
    · have h := tsum_decode₂_eq_ennreal (P := P) (fun x : P => ENNReal.ofReal ((kk x : ℝ) / k))
        (fun r : ℝ => poissonDensity w r + poissonDensity w (-r))
      rw [show (∑' x : P, (poissonDensity w x + poissonDensity w (-x)) * μb {(x : ℝ)}) =
          ∑' x : P, ENNReal.ofReal ((kk x : ℝ) / k) * (poissonDensity w x + poissonDensity w (-x))
          from tsum_congr fun x => by rw [hmassb x x.2, mul_comm], ← h]
      refine tsum_congr fun j => ?_
      simp only [hm, ht]
      rcases Encodable.decode₂ P j with _ | x
      · simp
      · rfl
    · exact Finset.sum_congr rfl fun x _ => by rw [hmass, mul_comm]
  have hid0 := weilFunction_eq_atomicPairSeries_add hW (c := fun j => (m j : ℝ) / k)
    (fun j => by positivity) hone ((hsum.div_const (k : ℝ)).congr fun j => by ring) F
    (fun x => (kk x : ℝ) / k) (fun x => by positivity) hFsym (fun x => by simp only [hkksym]) hrep
  have hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / k) t s +
        smallSeries F (fun x => (kk x : ℝ) / k) s := by
    intro s hs
    have h := hid0 s hs
    have hfun : lamTwo lam = lamC lam := by
      funext n
      rw [lamC, lamTwo]
      split_ifs <;> simp
    have hc : (fun j => Real.pi * ((m j : ℝ) / k)) = fun j => Real.pi * m j / k := by
      funext j; ring
    rw [hc] at h
    rw [← h, weilFunction, zetaArchimedeanDatum, hfun]
  refine ⟨F, kk, m, t, hFsym, hkksym, hone, hsum, fun s hs => ?_⟩
  exact bigG_pow_eq_mul_atomPoly_atomQ hk hone hsum
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) F kk hid hs

end RHTower.WeilSpectral
