import GaloisForLFunctions.SignedArithmeticEnergyIncidence.OnLineCompanionsPayOffLineDepth
import GaloisForLFunctions.RHTower.MobiusCubicGammaAtomJets
import Mathlib.Tactic.LinearCombination
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez

/-!
# Smooth sources pay at the Taylor price

The companion law of `OnLineCompanionsPayOffLineDepth` holds exactly for polynomial sources and,
for an arbitrary source, up to its local polynomial approximation error
(`companions_pay_up_to_error`).  For a smooth source the natural approximant is the Taylor
polynomial at the off-line height `t`:

* **Two-sided Taylor bound** (`abs_sub_taylorSum_le`): along a derivative chain
  `g (k+1) = (g k)'`, `|g 0 x − Σ_{j<d} g_j(t)(x − t)^j/j!| ≤ M |x − t|^d/d!` whenever
  `|g d| ≤ M` between `t` and `x`; the side below `t` is the side above `t` of the reflected
  chain `(−1)^k g_k(−·)`.
* **The Taylor polynomial** (`taylorPoly`) has degree `< d`, reproduces the derivative at `t`
  (`taylorPoly_derivative_eval`), and so carries no derivative error.
* **Smooth companion law** (`companions_pay_up_to_taylor`): with `d ≥ 2` local degrees of
  freedom, at least `d` companions within `δ` of `t`, `|g d| ≤ M` on `[t − δ, t + δ]` and
  `2 w Λ(t) ≤ 1`,
  `Σ_i f(γ_i)² − w f'(t)² ≥ −2 #s (M δ^d/d!)²`.

* **Sources of aperture `A`** (`companions_pay_aperture`): for a trigonometric source
  `Σ_k (a_k cos(λ_k x) + b_k sin(λ_k x))` with `|λ_k| ≤ A` (a Dirichlet polynomial of length
  `e^A` in the height variable), `|f^{(d)}| ≤ A^d m` with `m = Σ_k (|a_k| + |b_k|)`
  (`abs_trigSourceDeriv_le`), so the loss is `2 #s ((Aδ)^d m/d!)²` at every height `t`.

* **The price of the geometry** (`lagrangePrice_le_of_separated`,
  `companions_pay_aperture_explicit`): companions `γ_0, …, γ_k` spaced by `δ` within `r` of `t`
  have Lagrange price `Λ(t) ≤ (k + 1)(k r^{k−1}/δ^k)²` (from
  `HTGeometry.abs_eval_derivative_lagrangeBasis_le`), so the law is explicit in the companion
  geometry alone.

The signed floor of a smooth source is therefore paid by its companions up to the `d`-th Taylor
remainder: the loss decays like `δ^{2d}` as the companions close in on the off-line height, and for
sources of aperture `A` the bound is uniform in the height.
-/

open Polynomial Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The degree `< d` Taylor polynomial `Σ_{j<d} g_j(t)/j! (X − t)^j` of a derivative chain. -/
def taylorPoly (g : ℕ → ℝ → ℝ) (d : ℕ) (t : ℝ) : ℝ[X] :=
  ∑ j ∈ range d, C (g j t / (j.factorial : ℝ)) * (X - C t) ^ j

theorem taylorPoly_eval (g : ℕ → ℝ → ℝ) (d : ℕ) (t x : ℝ) :
    (taylorPoly g d t).eval x = ∑ j ∈ range d, g j t * (x - t) ^ j / (j.factorial : ℝ) := by
  unfold taylorPoly
  rw [eval_finsetSum]
  exact sum_congr rfl fun j _ => by
    rw [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C]; ring

theorem taylorPoly_degree_lt (g : ℕ → ℝ → ℝ) (d : ℕ) (t : ℝ) :
    (taylorPoly g d t).degree < d := by
  unfold taylorPoly
  rw [← mem_degreeLT]
  refine Submodule.sum_mem _ fun j hj => mem_degreeLT.2 ?_
  have h : (C (g j t / (j.factorial : ℝ)) * (X - C t) ^ j).degree ≤ (j : WithBot ℕ) := by
    refine (degree_mul_le _ _).trans ?_
    refine (add_le_add degree_C_le (degree_pow_le _ _)).trans ?_
    rw [degree_X_sub_C, zero_add, nsmul_eq_mul, mul_one]
  exact lt_of_le_of_lt h (by exact_mod_cast mem_range.1 hj)

/-- The Taylor polynomial reproduces the derivative at `t`. -/
theorem taylorPoly_derivative_eval (g : ℕ → ℝ → ℝ) {d : ℕ} (hd : 2 ≤ d) (t : ℝ) :
    (derivative (taylorPoly g d t)).eval t = g 1 t := by
  unfold taylorPoly
  rw [derivative_sum, eval_finsetSum, sum_eq_single 1]
  · rw [derivative_C_mul, pow_one, derivative_sub, derivative_X, derivative_C, sub_zero,
      mul_one, eval_C]
    simp
  · intro j _ hj
    rw [derivative_C_mul, derivative_X_sub_C_pow, eval_mul, eval_C, eval_mul, eval_C, eval_pow,
      eval_sub, eval_X, eval_C, sub_self]
    rcases j with _ | j
    · simp
    · rw [zero_pow (by omega : j + 1 - 1 ≠ 0)]; ring
  · intro h; exact absurd (mem_range.2 (by omega)) h

/-- **Two-sided Taylor bound for a derivative chain.** -/
theorem abs_sub_taylorSum_le {g : ℕ → ℝ → ℝ} (hg : ∀ k x, HasDerivAt (g k) (g (k + 1) x) x)
    (d : ℕ) {t x M : ℝ} (hM : ∀ y ∈ Set.uIcc t x, |g d y| ≤ M) :
    |g 0 x - ∑ j ∈ range d, g j t * (x - t) ^ j / (j.factorial : ℝ)| ≤
      M * |x - t| ^ d / (d.factorial : ℝ) := by
  rcases le_total t x with htx | hxt
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - t)]
    exact RHTower.CubicGamma.abs_taylor_chain_le hg d htx fun y hy =>
      hM y (Set.Icc_subset_uIcc hy)
  · -- reflect: `h_k(y) = (−1)^k g_k(−y)` is again a derivative chain
    set h : ℕ → ℝ → ℝ := fun k y => (-1) ^ k * g k (-y) with hhdef
    have hh : ∀ k y, HasDerivAt (h k) (h (k + 1) y) y := by
      intro k y
      have h1 : HasDerivAt (fun z => g k (-z)) (g (k + 1) (-y) * -1) y :=
        (hg k (-y)).comp y (hasDerivAt_neg y)
      have h2 := h1.const_mul ((-1 : ℝ) ^ k)
      have e : (-1 : ℝ) ^ k * (g (k + 1) (-y) * -1) = h (k + 1) y := by
        simp only [hhdef]; ring
      rw [e] at h2
      exact h2
    have hxt' : -t ≤ -x := by linarith
    have hb := RHTower.CubicGamma.abs_taylor_chain_le hh d hxt' (M := M) fun y hy => by
      simp only [hhdef, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hM (-y) (Set.uIcc_comm t x ▸ Set.Icc_subset_uIcc ⟨by linarith [hy.2], by
        linarith [hy.1]⟩)
    have e0 : h 0 (-x) = g 0 x := by simp [hhdef]
    have ej : ∀ j, h j (-t) * (-x - -t) ^ j / (j.factorial : ℝ) =
        g j t * (x - t) ^ j / (j.factorial : ℝ) := by
      intro j
      have hsign : (-1 : ℝ) ^ j * (-(x - t)) ^ j = (x - t) ^ j := by
        rw [← mul_pow]; congr 1; ring
      simp only [hhdef, neg_neg]
      rw [show -x - -t = -(x - t) by ring]
      linear_combination (g j t / (j.factorial : ℝ)) * hsign
    rw [e0, sum_congr rfl fun j _ => ej j, show -x - -t = -(x - t) by ring] at hb
    rw [abs_of_nonpos (by linarith : x - t ≤ 0)]
    rwa [show -(x - t) = -(x - t) from rfl] at hb

/-- **Smooth sources pay at the Taylor price.** -/
theorem companions_pay_up_to_taylor {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hvs : Set.InjOn v s) {g : ℕ → ℝ → ℝ} (hg : ∀ k x, HasDerivAt (g k) (g (k + 1) x) x)
    {d : ℕ} (hd : 2 ≤ d) (hds : d ≤ #s) {t δ M w : ℝ} (hδ : ∀ i ∈ s, |v i - t| ≤ δ)
    (hM : ∀ y ∈ Set.Icc (t - δ) (t + δ), |g d y| ≤ M) (hw : 0 ≤ w)
    (hΛ : 2 * w * lagrangePrice s v t ≤ 1) :
    -(2 * #s * (M * δ ^ d / (d.factorial : ℝ)) ^ 2) ≤ sampleForm s v w (g 0) (g 1 t) := by
  have hdeg : (taylorPoly g d t).degree < #s :=
    lt_of_lt_of_le (taylorPoly_degree_lt g d t) (by exact_mod_cast hds)
  have h := companions_pay_up_to_error hvs hdeg hw hΛ (g 0) (g 1 t)
  rw [taylorPoly_derivative_eval g hd t, sub_self, zero_pow two_ne_zero, mul_zero,
    add_zero] at h
  -- each companion error is a Taylor remainder
  have herr : ∀ i ∈ s, (g 0 (v i) - (taylorPoly g d t).eval (v i)) ^ 2 ≤
      (M * δ ^ d / (d.factorial : ℝ)) ^ 2 := by
    intro i hi
    have hvi := hδ i hi
    have hsub : Set.uIcc t (v i) ⊆ Set.Icc (t - δ) (t + δ) := by
      intro y hy
      rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        constructor <;> linarith [abs_le.1 hvi]
    have hb := abs_sub_taylorSum_le hg d (t := t) (x := v i) fun y hy => hM y (hsub hy)
    rw [← taylorPoly_eval] at hb
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ⟨by linarith [(abs_nonneg _).trans hvi],
      by linarith [(abs_nonneg _).trans hvi]⟩)
    have hpow : |v i - t| ^ d ≤ δ ^ d := pow_le_pow_left₀ (abs_nonneg _) hvi d
    have hb' : |g 0 (v i) - (taylorPoly g d t).eval (v i)| ≤ M * δ ^ d / (d.factorial : ℝ) :=
      hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hM0) (by positivity))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
  have hsum : ∑ i ∈ s, (g 0 (v i) - (taylorPoly g d t).eval (v i)) ^ 2 ≤
      #s * (M * δ ^ d / (d.factorial : ℝ)) ^ 2 := by
    calc _ ≤ ∑ _i ∈ s, (M * δ ^ d / (d.factorial : ℝ)) ^ 2 := sum_le_sum herr
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  linarith

/-! ### Sources of bounded aperture -/

/-- The `j`-th derivative of the trigonometric source `Σ_k (a_k cos(λ_k x) + b_k sin(λ_k x))`. -/
def trigSourceDeriv {κ : Type*} (K : Finset κ) (lam a b : κ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ K, lam k ^ j * (a k * Real.cos (lam k * x + j * (Real.pi / 2)) +
    b k * Real.sin (lam k * x + j * (Real.pi / 2)))

theorem hasDerivAt_trigSourceDeriv {κ : Type*} (K : Finset κ) (lam a b : κ → ℝ) (j : ℕ)
    (x : ℝ) :
    HasDerivAt (trigSourceDeriv K lam a b j) (trigSourceDeriv K lam a b (j + 1) x) x := by
  unfold trigSourceDeriv
  have hsum := HasDerivAt.fun_sum (u := K) (A := fun k x => lam k ^ j *
      (a k * Real.cos (lam k * x + j * (Real.pi / 2)) +
        b k * Real.sin (lam k * x + j * (Real.pi / 2))))
    (A' := fun k => lam k ^ j * (a k * (-Real.sin (lam k * x + j * (Real.pi / 2)) * lam k) +
        b k * (Real.cos (lam k * x + j * (Real.pi / 2)) * lam k))) (x := x) fun k _ => by
    have hin : HasDerivAt (fun y => lam k * y + j * (Real.pi / 2)) (lam k) x := by
      simpa using ((hasDerivAt_id x).const_mul (lam k)).add_const (j * (Real.pi / 2))
    exact (((hin.cos).const_mul (a k)).add ((hin.sin).const_mul (b k))).const_mul (lam k ^ j)
  refine hsum.congr_deriv (sum_congr rfl fun k _ => ?_)
  · have hc : Real.cos (lam k * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
        -Real.sin (lam k * x + j * (Real.pi / 2)) := by
      rw [show lam k * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2) =
        (lam k * x + j * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring, Real.cos_add_pi_div_two]
    have hs : Real.sin (lam k * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
        Real.cos (lam k * x + j * (Real.pi / 2)) := by
      rw [show lam k * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2) =
        (lam k * x + j * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring, Real.sin_add_pi_div_two]
    rw [hc, hs, pow_succ]
    ring

/-- **Aperture bound**: every derivative of order `d` is at most `A^d Σ_k (|a_k| + |b_k|)`. -/
theorem abs_trigSourceDeriv_le {κ : Type*} (K : Finset κ) {lam a b : κ → ℝ} {A : ℝ}
    (hA : ∀ k ∈ K, |lam k| ≤ A) (d : ℕ) (x : ℝ) :
    |trigSourceDeriv K lam a b d x| ≤ A ^ d * ∑ k ∈ K, (|a k| + |b k|) := by
  unfold trigSourceDeriv
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hlam : |lam k| ^ d ≤ A ^ d := pow_le_pow_left₀ (abs_nonneg _) (hA k hk) d
  rw [abs_mul, abs_pow]
  have htrig : |a k * Real.cos (lam k * x + d * (Real.pi / 2)) +
      b k * Real.sin (lam k * x + d * (Real.pi / 2))| ≤ |a k| + |b k| := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  exact mul_le_mul hlam htrig (abs_nonneg _) (by
    have := (abs_nonneg (lam k)).trans (hA k hk); positivity)

/-- **Sources of aperture `A` pay uniformly in height**: for a trigonometric source with
frequencies `|λ_k| ≤ A` and mass `m = Σ_k (|a_k| + |b_k|)`, at least `d ≥ 2` companions within `δ`
of any height `t`, and `2 w Λ(t) ≤ 1`,
`Σ_i f(γ_i)² − w f'(t)² ≥ −2 #s ((Aδ)^d m / d!)²`. -/
theorem companions_pay_aperture {ι κ : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hvs : Set.InjOn v s) (K : Finset κ) {lam a b : κ → ℝ} {A : ℝ}
    (hA : ∀ k ∈ K, |lam k| ≤ A) {d : ℕ} (hd : 2 ≤ d) (hds : d ≤ #s) {t δ w : ℝ}
    (hδ : ∀ i ∈ s, |v i - t| ≤ δ) (hw : 0 ≤ w) (hΛ : 2 * w * lagrangePrice s v t ≤ 1) :
    -(2 * #s * ((A * δ) ^ d * (∑ k ∈ K, (|a k| + |b k|)) / (d.factorial : ℝ)) ^ 2) ≤
      sampleForm s v w (trigSourceDeriv K lam a b 0) (trigSourceDeriv K lam a b 1 t) := by
  have h := companions_pay_up_to_taylor hvs (hasDerivAt_trigSourceDeriv K lam a b) hd hds hδ
    (M := A ^ d * ∑ k ∈ K, (|a k| + |b k|)) (fun y _ => abs_trigSourceDeriv_le K hA d y) hw hΛ
  have e : A ^ d * (∑ k ∈ K, (|a k| + |b k|)) * δ ^ d / (d.factorial : ℝ) =
      (A * δ) ^ d * (∑ k ∈ K, (|a k| + |b k|)) / (d.factorial : ℝ) := by
    rw [mul_pow]; ring
  rwa [e] at h

/-! ### The price of the companion geometry -/

/-- **The Lagrange price of separated companions**: for companions `γ_0, …, γ_k` with
`|γ_i − γ_j| ≥ |i − j| δ`, all within `r` of `t`, `Λ(t) ≤ (k + 1)(k r^{k−1}/δ^k)²`. -/
theorem lagrangePrice_le_of_separated {k : ℕ} (v : Fin (k + 1) → ℝ) {δ r t : ℝ} (hδ : 0 < δ)
    (hr : 0 ≤ r) (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    (ht : ∀ i, |t - v i| ≤ r) :
    lagrangePrice univ v t ≤ (k + 1) * (k * r ^ (k - 1) / δ ^ k) ^ 2 := by
  have hterm : ∀ i : Fin (k + 1), ((derivative (Lagrange.basis univ v i)).eval t) ^ 2 ≤
      (k * r ^ (k - 1) / δ ^ k) ^ 2 := by
    intro i
    have h := HTGeometry.abs_eval_derivative_lagrangeBasis_le v hδ hr hsep ht i
    -- the integer gaps multiply to at least one
    have hP : 1 ≤ ∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      calc (1 : ℝ) = ∏ _j ∈ univ.erase i, (1 : ℝ) := by rw [prod_const_one]
        _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one) fun j hj => by
          have hij : (i : ℕ) ≠ (j : ℕ) := fun h => (mem_erase.1 hj).1 (Fin.ext h).symm
          rcases lt_or_gt_of_ne hij with hlt | hlt
          · rw [abs_sub_comm, abs_of_pos (sub_pos.2 (by exact_mod_cast hlt))]
            have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hlt
            linarith
          · rw [abs_of_pos (sub_pos.2 (by exact_mod_cast hlt))]
            have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast hlt
            linarith
    have hc : 0 ≤ (k : ℝ) * r ^ (k - 1) / δ ^ k := by positivity
    have hinv : (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP
    have h' : |(derivative (Lagrange.basis univ v i)).eval t| ≤ k * r ^ (k - 1) / δ ^ k :=
      h.trans (by simpa using mul_le_mul_of_nonneg_left hinv hc)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h' 2
  unfold lagrangePrice
  calc ∑ i, ((derivative (Lagrange.basis univ v i)).eval t) ^ 2
      ≤ ∑ _i : Fin (k + 1), (k * r ^ (k - 1) / δ ^ k) ^ 2 := sum_le_sum fun i _ => hterm i
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

/-- **The explicit signed sampling law for sources of aperture `A`.**  Companions
`γ_0, …, γ_k` spaced by `δ` and within `r` of the height `t`, a trigonometric source with
frequencies `|λ_j| ≤ A` and mass `m`, `2 ≤ d ≤ k + 1`, and an off-line depth mass `w` with
`2 w (k + 1)(k r^{k−1}/δ^k)² ≤ 1`:
`Σ_i f(γ_i)² − w f'(t)² ≥ −2 (k + 1) ((A r)^d m/d!)²`, at every height `t`. -/
theorem companions_pay_aperture_explicit {κ : Type*} {k : ℕ} (v : Fin (k + 1) → ℝ) {δ r t w : ℝ}
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    (ht : ∀ i, |t - v i| ≤ r) (K : Finset κ) {lam α β : κ → ℝ} {A : ℝ}
    (hA : ∀ j ∈ K, |lam j| ≤ A) {d : ℕ} (hd : 2 ≤ d) (hdk : d ≤ k + 1) (hw : 0 ≤ w)
    (hprice : 2 * w * ((k + 1) * (k * r ^ (k - 1) / δ ^ k) ^ 2) ≤ 1) :
    -(2 * (k + 1 : ℕ) * ((A * r) ^ d * (∑ j ∈ K, (|α j| + |β j|)) / (d.factorial : ℝ)) ^ 2) ≤
      sampleForm univ v w (trigSourceDeriv K lam α β 0) (trigSourceDeriv K lam α β 1 t) := by
  have hinj : Set.InjOn v (univ : Finset (Fin (k + 1))) := by
    intro i _ j _ hij
    by_contra hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    have h1 : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · rw [abs_sub_comm, abs_of_pos (sub_pos.2 (by exact_mod_cast hlt))]
        have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hlt
        linarith
      · rw [abs_of_pos (sub_pos.2 (by exact_mod_cast hlt))]
        have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast hlt
        linarith
    have := hsep i j
    rw [hij, sub_self, abs_zero] at this
    nlinarith
  have hΛ : 2 * w * lagrangePrice univ v t ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (lagrangePrice_le_of_separated v hδ hr hsep ht)
      (by positivity)) hprice
  have hcard : d ≤ #(univ : Finset (Fin (k + 1))) := by rw [card_univ, Fintype.card_fin]; exact hdk
  have h := companions_pay_aperture hinj K (a := α) (b := β) hA hd hcard (t := t) (δ := r)
    (fun i _ => by rw [abs_sub_comm]; exact ht i) hw hΛ
  rwa [card_univ, Fintype.card_fin] at h

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
