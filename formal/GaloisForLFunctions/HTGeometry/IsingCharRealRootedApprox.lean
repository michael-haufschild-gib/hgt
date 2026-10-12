import GaloisForLFunctions.HTGeometry.EvenRealRootedGaussianBounds
import GaloisForLFunctions.HTGeometry.LeeYangAsanoContraction
import GaloisForLFunctions.HTGeometry.IsingFieldGriffiths
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# Ising characteristic functions are limits of even real-rooted polynomials

For a zero-field ferromagnetic Ising model (`J ≥ 0` on the bonds `E`) with magnetization
`X = Σ_k c_k σ_k`, `c_k ≥ 0`, let `φ(z) = E[e^{izX}] = Z⁻¹ Σ_D W(D) e^{iz X_D}`.

**Theorem** (`exists_even_realRooted_approx`). There are real polynomials `q_N`, split over `ℝ` and
even, with `q_N → φ` locally uniformly on `ℂ`. Concretely,
`q_N(z) = Z⁻¹ Σ_D W(D) ∏_k (1 + i c_k σ_k(D) z/N)^N`.

* `q_N` has real coefficients: complex conjugation flips every spin and the weights are
  flip-invariant (`map_conj_charApproxC`).
* `q_N` is even by the same flip (`eval_neg_charApproxC`).
* All zeros are real by the Lee–Yang theorem. For `Im z < 0`,
  `q_N(z) = Z⁻¹ ∏_k u_k^N · e^{ΣJ} P_E(r)` with `u_k = 1 + i c_k z/N`, `r_k = (ū_k'/u_k)^N` inside the
  unit disc, and `P_E` the Lee–Yang polynomial with bond weights `e^{−2J} ∈ (0,1]`
  (`isingWeight_eq_isingCoeff`, `eval_charApproxC_ne_zero_of_im_neg`).
* `∏_k (1 + b_k z/N)^N → exp(z Σ_k b_k)` locally uniformly (`tendstoLocallyUniformly_prod_pow`).
* Zero masses are handled diagonally: `Q_N[c + 1/(N+1)] → φ[c]`
  (`tendstoLocallyUniformly_charApproxC_shiftMass`).

Consequently (`norm_sq_isingCharFn_le`, `isingCharFn_mul_neg_le`) the Gaussian bounds of
`EvenRealRootedGaussianBounds` hold for `φ` with the constant `L(φ)`.
-/

open Polynomial Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.LeeYang

noncomputable section

/-! ## Products of compound-interest factors -/

/-- `∏_k (1 + b_{N,k} z/N)^N − exp(z Σ_k b_{N,k}) → 0` locally uniformly on `ℂ`, for uniformly
bounded `b`. -/
theorem tendstoLocallyUniformly_prod_pow_sub {ι : Type*} [Fintype ι] (b' : ℕ → ι → ℂ) {C : ℝ}
    (hC : ∀ N k, ‖b' N k‖ ≤ C) :
    TendstoLocallyUniformly (fun (N : ℕ) (z : ℂ) =>
      ∏ k, (1 + b' N k * z / N) ^ N - Complex.exp (z * ∑ k, b' N k)) (fun _ => 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B : ℝ := ∑ _k : ι, C' with hBdef
  set S : ℝ := ∑ _k : ι, C' ^ 2 with hSdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => hC'0
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set M : ℝ := Real.exp (R * B) with hM
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * R * B + S * R ^ 2 + 2 * M * S * R ^ 2 / ε + 1)
  filter_upwards [eventually_ge_atTop N₀] with N hN z hz
  set b : ι → ℂ := b' N with hbdef
  have hbC : ∀ k, ‖b k‖ ≤ C' := fun k => (hC N k).trans (le_max_left _ _)
  have hbB : ∀ k, ‖b k‖ ≤ B := fun k => (hbC k).trans
    (Finset.single_le_sum (f := fun _ : ι => C') (fun _ _ => hC'0) (Finset.mem_univ k))
  have hsumB : ∑ k, ‖b k‖ ≤ B := Finset.sum_le_sum fun k _ => hbC k
  have hsumS : ∑ k, ‖b k‖ ^ 2 ≤ S :=
    Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hbC k) 2
  have hNr : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) := by
    have : 0 ≤ 2 * M * S * R ^ 2 / ε := by positivity
    have : 0 ≤ 2 * R * B := by positivity
    nlinarith [sq_nonneg R]
  have hzR := hR z hz
  -- each factor is small
  set w : ι → ℂ := fun k => b k * z / N with hw
  have hwle : ∀ k, ‖w k‖ ≤ ‖b k‖ * R / N := by
    intro k
    rw [hw, norm_div, norm_mul, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzR (norm_nonneg _)) hpos.le
  have hwhalf : ∀ k, ‖w k‖ ≤ 1 / 2 := by
    intro k
    refine (hwle k).trans ?_
    rw [div_le_iff₀ hpos]
    have : ‖b k‖ * R ≤ B * R := mul_le_mul_of_nonneg_right (hbB k) hR0
    have : 2 * R * B < N := by
      have : 0 ≤ S * R ^ 2 + 2 * M * S * R ^ 2 / ε := by positivity
      linarith
    nlinarith
  have hw1 : ∀ k, (1 : ℂ) + w k ≠ 0 := by
    intro k h
    have : w k = -1 := by linear_combination h
    have := hwhalf k
    rw [‹w k = -1›, norm_neg, norm_one] at this
    norm_num at this
  -- the product is an exponential
  set g : ℂ := ∑ k, (N : ℂ) * Complex.log (1 + w k) with hg
  have hprod : ∏ k, (1 + b k * z / N) ^ N = Complex.exp g := by
    rw [hg, Complex.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Complex.exp_nat_mul, Complex.exp_log (hw1 k)]
  -- the exponent is close to `z Σ b`
  have hgap : ‖g - z * ∑ k, b k‖ ≤ S * R ^ 2 / N := by
    have hsum : z * ∑ k, b k = ∑ k, (N : ℂ) * w k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hw]
      have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
    rw [hsum, hg, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k, ‖(N : ℂ) * Complex.log (1 + w k) - (N : ℂ) * w k‖ ≤ ‖b k‖ ^ 2 * R ^ 2 / N := by
      intro k
      rw [← mul_sub, norm_mul, Complex.norm_natCast]
      have hlt : ‖w k‖ < 1 := lt_of_le_of_lt (hwhalf k) (by norm_num)
      have h1 := Complex.norm_log_one_add_sub_self_le hlt
      have h2 : ‖w k‖ ^ 2 * (1 - ‖w k‖)⁻¹ / 2 ≤ ‖w k‖ ^ 2 := by
        have hden : (1 : ℝ) / 2 ≤ 1 - ‖w k‖ := by linarith [hwhalf k]
        have : (1 - ‖w k‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have h0 : 0 ≤ ‖w k‖ ^ 2 := by positivity
        nlinarith
      have h3 : ‖w k‖ ^ 2 ≤ (‖b k‖ * R / N) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hwle k) 2
      calc (N : ℝ) * ‖Complex.log (1 + w k) - w k‖ ≤ N * (‖b k‖ * R / N) ^ 2 :=
            mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hpos.le
        _ = ‖b k‖ ^ 2 * R ^ 2 / N := by field_simp
    refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
    rw [← Finset.sum_div, ← Finset.sum_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsumS (by positivity)) hpos.le
  have hgap1 : S * R ^ 2 / N ≤ 1 := by
    rw [div_le_one hpos]
    have : 0 ≤ 2 * M * S * R ^ 2 / ε := by positivity
    have : 0 ≤ 2 * R * B := by positivity
    linarith
  have hexp : ‖Complex.exp (z * ∑ k, b k)‖ ≤ M := by
    rw [Complex.norm_exp, hM]
    apply Real.exp_le_exp.mpr
    calc (z * ∑ k, b k).re ≤ ‖z * ∑ k, b k‖ := Complex.re_le_norm _
      _ ≤ R * B := by
        rw [norm_mul]
        exact mul_le_mul hzR ((norm_sum_le _ _).trans hsumB) (norm_nonneg _) hR0
  rw [dist_eq_norm, hprod, zero_sub, norm_neg, norm_sub_rev]
  have hsplit : Complex.exp (z * ∑ k, b k) - Complex.exp g =
      -(Complex.exp (z * ∑ k, b k) * (Complex.exp (g - z * ∑ k, b k) - 1)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  rw [hsplit, norm_neg, norm_mul]
  have hb := Complex.norm_exp_sub_one_le (hgap.trans hgap1)
  calc ‖Complex.exp (z * ∑ k, b k)‖ * ‖Complex.exp (g - z * ∑ k, b k) - 1‖
      ≤ M * (2 * (S * R ^ 2 / N)) :=
        mul_le_mul hexp (hb.trans (by linarith [hgap])) (norm_nonneg _) (by positivity)
    _ < ε := by
        have hM0 : 0 < M := Real.exp_pos _
        rw [show M * (2 * (S * R ^ 2 / N)) = 2 * M * S * R ^ 2 / N by ring,
          div_lt_iff₀ hpos]
        have : 2 * M * S * R ^ 2 / ε < N := by
          have : 0 ≤ 2 * R * B + S * R ^ 2 := by positivity
          linarith
        rw [div_lt_iff₀ hε] at this
        linarith

/-- If `F_i − G_i → 0` and `G_i → g` locally uniformly, then `F_i → g` locally uniformly. -/
theorem tendstoLocallyUniformly_of_sub {α ι : Type*} [TopologicalSpace α] {l : Filter ι}
    {F G : ι → α → ℂ} {g : α → ℂ}
    (h1 : TendstoLocallyUniformly (fun i z => F i z - G i z) (fun _ => 0) l)
    (h2 : TendstoLocallyUniformly G g l) : TendstoLocallyUniformly F g l := by
  rw [Metric.tendstoLocallyUniformly_iff] at h1 h2 ⊢
  intro ε hε x
  obtain ⟨t1, ht1, hev1⟩ := h1 (ε / 2) (by positivity) x
  obtain ⟨t2, ht2, hev2⟩ := h2 (ε / 2) (by positivity) x
  refine ⟨t1 ∩ t2, Filter.inter_mem ht1 ht2, ?_⟩
  filter_upwards [hev1, hev2] with n hn1 hn2 y hy
  have a1 := hn1 y hy.1
  have a2 := hn2 y hy.2
  rw [dist_eq_norm, zero_sub, norm_neg] at a1
  rw [dist_eq_norm] at a2 ⊢
  calc ‖g y - F n y‖ = ‖(g y - G n y) - (F n y - G n y)‖ := by ring_nf
    _ ≤ ‖g y - G n y‖ + ‖F n y - G n y‖ := norm_sub_le _ _
    _ < ε := by linarith

/-- `exp(z s_N) → exp(z s)` locally uniformly when `s_N → s`. -/
theorem tendstoLocallyUniformly_exp_mul {s : ℕ → ℂ} {s₀ : ℂ} (hs : Tendsto s atTop (𝓝 s₀)) :
    TendstoLocallyUniformly (fun (N : ℕ) (z : ℂ) => Complex.exp (z * s N))
      (fun z => Complex.exp (z * s₀)) atTop := by
  let F : C(ℂ × ℂ, ℂ) := ⟨fun p => Complex.exp (p.2 * p.1), by fun_prop⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((F.curry.continuous.tendsto s₀).comp hs)

/-- `∏_k (1 + b_k z/N)^N → exp(z Σ_k b_k)` locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_prod_pow {ι : Type*} [Fintype ι] (b : ι → ℂ) :
    TendstoLocallyUniformly (fun (N : ℕ) (z : ℂ) => ∏ k, (1 + b k * z / N) ^ N)
      (fun z => Complex.exp (z * ∑ k, b k)) atTop :=
  tendstoLocallyUniformly_of_sub
    (tendstoLocallyUniformly_prod_pow_sub (fun _ => b) (C := ∑ k, ‖b k‖) fun _ k =>
      Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ k))
    (tendstoLocallyUniformly_exp_mul tendsto_const_nhds)

/-- Finite constant-weight combinations of locally uniformly convergent sequences converge locally
uniformly. -/
theorem tendstoLocallyUniformly_sum_const_mul {κ ι : Type*} [Fintype κ] {l : Filter ι}
    (a : κ → ℂ) {F : κ → ι → ℂ → ℂ} {f : κ → ℂ → ℂ}
    (h : ∀ k, TendstoLocallyUniformly (F k) (f k) l) :
    TendstoLocallyUniformly (fun i z => ∑ k, a k * F k i z) (fun z => ∑ k, a k * f k z) l := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  set A : ℝ := ∑ k, ‖a k‖ + 1 with hA
  have hA0 : 0 < A := by positivity
  have hk : ∀ k, ∃ t ∈ 𝓝 x, ∀ᶠ n in l, ∀ y ∈ t, dist (f k y) (F k n y) < ε / A := fun k =>
    (Metric.tendstoLocallyUniformly_iff.mp (h k)) (ε / A) (by positivity) x
  choose t ht hev using hk
  refine ⟨⋂ k, t k, Filter.iInter_mem.mpr ht, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hev] with n hn y hy
  rw [Set.mem_iInter] at hy
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ k, (a k * f k y - a k * F k n y)‖ ≤ ∑ k, ‖a k‖ * (ε / A) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [← mul_sub, norm_mul]
        have := hn k y (hy k)
        rw [dist_eq_norm] at this
        exact mul_le_mul_of_nonneg_left this.le (norm_nonneg _)
    _ < ε := by
        rw [← Finset.sum_mul, mul_div_assoc', div_lt_iff₀ hA0]
        nlinarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => norm_nonneg (a k)]

/-! ## The approximants -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The characteristic function `φ(z) = Z⁻¹ Σ_D W(D) e^{izX_D}` of `X = Σ_k c_k σ_k`. -/
def isingCharFn (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (z : ℂ) : ℂ :=
  (∑ D : Finset V, (isingWeight J E D : ℂ) *
    Complex.exp (I * z * ((∑ k, c k * spin D k : ℝ) : ℂ))) / (Zpart J E : ℂ)

/-- The polynomial approximant `Q_N = Σ_D (W(D)/Z) ∏_k (1 + (i c_k σ_k/N) X)^N`. -/
def charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (N : ℕ) : ℂ[X] :=
  ∑ D : Finset V, Polynomial.C (((isingWeight J E D / Zpart J E : ℝ)) : ℂ) *
    ∏ k, (1 + Polynomial.C (I * ((c k * spin D k : ℝ) : ℂ) / N) * X) ^ N

theorem eval_charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (N : ℕ) (z : ℂ) :
    (charApproxC J E c N).eval z = ∑ D : Finset V, (((isingWeight J E D / Zpart J E : ℝ)) : ℂ) *
      ∏ k, (1 + I * ((c k * spin D k : ℝ) : ℂ) / N * z) ^ N := by
  simp [charApproxC, eval_finsetSum, eval_prod]

/-- Diagonal approximation: if `c_N → c` with `|c_N| ≤ C`, then `Q_N[c_N] → φ[c]`. -/
theorem tendstoLocallyUniformly_charApproxC_seq (J : V → V → ℝ) (E : Finset (V × V))
    (cs : ℕ → V → ℝ) (c : V → ℝ) (hcs : ∀ k, Tendsto (fun N => cs N k) atTop (𝓝 (c k)))
    {C : ℝ} (hC : ∀ N k, |cs N k| ≤ C) :
    TendstoLocallyUniformly (fun N z => (charApproxC J E (cs N) N).eval z) (isingCharFn J E c)
      atTop := by
  have hD : ∀ D : Finset V, TendstoLocallyUniformly
      (fun (N : ℕ) (z : ℂ) => ∏ k, (1 + I * ((cs N k * spin D k : ℝ) : ℂ) / N * z) ^ N)
      (fun z => Complex.exp (I * z * ((∑ k, c k * spin D k : ℝ) : ℂ))) atTop := by
    intro D
    have hb : ∀ N k, ‖I * ((cs N k * spin D k : ℝ) : ℂ)‖ ≤ C := by
      intro N k
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have : |spin D k| = 1 := by unfold spin; split_ifs <;> simp
      rw [this, mul_one]; exact hC N k
    have h1 := tendstoLocallyUniformly_prod_pow_sub
      (fun N k => I * ((cs N k * spin D k : ℝ) : ℂ)) hb
    have hs : Tendsto (fun N => ∑ k, I * ((cs N k * spin D k : ℝ) : ℂ)) atTop
        (𝓝 (∑ k, I * ((c k * spin D k : ℝ) : ℂ))) := by
      refine tendsto_finsetSum _ fun k _ => ?_
      refine tendsto_const_nhds.mul ?_
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((hcs k).mul_const _)
    have h2 := tendstoLocallyUniformly_exp_mul hs
    have h := tendstoLocallyUniformly_of_sub h1 h2
    have e1 : (fun (N : ℕ) (z : ℂ) => ∏ k, (1 + I * ((cs N k * spin D k : ℝ) : ℂ) / N * z) ^ N) =
        fun (N : ℕ) (z : ℂ) => ∏ k, (1 + I * ((cs N k * spin D k : ℝ) : ℂ) * z / N) ^ N := by
      funext N z; congr 1; funext k; ring
    have e2 : (fun z => Complex.exp (I * z * ((∑ k, c k * spin D k : ℝ) : ℂ))) =
        fun z => Complex.exp (z * ∑ k, I * ((c k * spin D k : ℝ) : ℂ)) := by
      funext z; congr 1; rw [← Finset.mul_sum]; push_cast; ring
    rw [e1, e2]; exact h
  have hsum := tendstoLocallyUniformly_sum_const_mul
    (fun D : Finset V => (((isingWeight J E D / Zpart J E : ℝ)) : ℂ)) hD
  have e1 : (fun N z => (charApproxC J E (cs N) N).eval z) = fun (N : ℕ) z =>
      ∑ D : Finset V, (((isingWeight J E D / Zpart J E : ℝ)) : ℂ) *
        ∏ k, (1 + I * ((cs N k * spin D k : ℝ) : ℂ) / N * z) ^ N := by
    funext N z; rw [eval_charApproxC]
  have e2 : isingCharFn J E c = fun z => ∑ D : Finset V,
      (((isingWeight J E D / Zpart J E : ℝ)) : ℂ) *
        Complex.exp (I * z * ((∑ k, c k * spin D k : ℝ) : ℂ)) := by
    funext z
    rw [isingCharFn, Finset.sum_div]
    refine Finset.sum_congr rfl fun D _ => ?_
    push_cast; ring
  rw [e1, e2]
  exact hsum

theorem tendstoLocallyUniformly_charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) :
    TendstoLocallyUniformly (fun N z => (charApproxC J E c N).eval z) (isingCharFn J E c) atTop :=
  tendstoLocallyUniformly_charApproxC_seq J E (fun _ => c) c (fun _ => tendsto_const_nhds)
    (C := ∑ k, |c k|) fun _ k =>
      Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

/-- The positive perturbation `c + 1/(N+1)` of nonnegative masses. -/
def shiftMass (c : V → ℝ) (N : ℕ) (k : V) : ℝ := c k + 1 / ((N : ℝ) + 1)

omit [Fintype V] [DecidableEq V] in
theorem shiftMass_pos {c : V → ℝ} (hc : ∀ k, 0 ≤ c k) (N : ℕ) (k : V) : 0 < shiftMass c N k := by
  unfold shiftMass; have := hc k; positivity

theorem tendstoLocallyUniformly_charApproxC_shiftMass (J : V → V → ℝ) (E : Finset (V × V))
    (c : V → ℝ) :
    TendstoLocallyUniformly (fun N z => (charApproxC J E (shiftMass c N) N).eval z)
      (isingCharFn J E c) atTop := by
  refine tendstoLocallyUniformly_charApproxC_seq J E (shiftMass c) c (fun k => ?_)
    (C := ∑ k, |c k| + 1) fun N k => ?_
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (c k)
    rw [add_zero] at h
    exact h
  · unfold shiftMass
    have h1 : |c k| ≤ ∑ j, |c j| :=
      Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : 1 / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h3 : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    calc |c k + 1 / ((N : ℝ) + 1)| ≤ |c k| + |1 / ((N : ℝ) + 1)| := abs_add_le _ _
      _ ≤ ∑ j, |c j| + 1 := by rw [abs_of_nonneg h3]; linarith


/-! ## Lee–Yang structure of the approximants -/

omit [Fintype V] in
/-- The Boltzmann weight in Lee–Yang form: `W(D) = e^{ΣJ} ∏_{bonds crossing D} e^{−2J}`. -/
theorem isingWeight_eq_isingCoeff (J : V → V → ℝ) (E : Finset (V × V)) (D : Finset V) :
    (isingWeight J E D : ℂ) = (Real.exp (∑ p ∈ E, J p.1 p.2) : ℂ) *
      isingCoeff (fun i j => Real.exp (-2 * J i j)) (E.filter fun p => p.1 ≠ p.2) D := by
  have hbw : ∀ p : V × V, ((Real.exp (J p.1 p.2 * spin D p.1 * spin D p.2) : ℝ) : ℂ) =
      (Real.exp (J p.1 p.2) : ℂ) * bondWeight (Real.exp (-2 * J p.1 p.2)) p.1 p.2 D := by
    intro p
    unfold bondWeight spin
    by_cases h1 : p.1 ∈ D <;> by_cases h2 : p.2 ∈ D <;> simp only [h1, h2, if_true, if_false,
      iff_true, iff_false, not_true_eq_false, iff_self,
      mul_one, mul_neg, neg_mul, neg_neg] <;>
    (try rw [← Complex.ofReal_mul, ← Real.exp_add]) <;> (try congr 2) <;> ring_nf
  rw [isingWeight, Real.exp_sum, Complex.ofReal_prod, isingCoeff]
  simp_rw [hbw]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 1
  rw [Finset.prod_filter_of_ne]
  intro p _ hp heq
  apply hp
  simp [bondWeight, heq]

theorem eval_charApproxC_zero (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (z : ℂ) :
    (charApproxC J E c 0).eval z = 1 := by
  rw [eval_charApproxC]
  simp only [pow_zero, Finset.prod_const_one, mul_one]
  rw [← Complex.ofReal_sum, ← Finset.sum_div]
  have hZ := Zpart_pos J E
  rw [show (∑ D : Finset V, isingWeight J E D) = Zpart J E from rfl, div_self hZ.ne',
    Complex.ofReal_one]

/-- Reindexing a sum over down sets by the complement. -/
theorem sum_compl_eq {β : Type*} [AddCommMonoid β] (f : Finset V → β) :
    ∑ D : Finset V, f Dᶜ = ∑ D : Finset V, f D :=
  Fintype.sum_equiv ⟨compl, compl, compl_compl, compl_compl⟩ _ _ fun _ => rfl

/-- **Evenness.** `Q_N(−z) = Q_N(z)`. -/
theorem eval_neg_charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (N : ℕ) (z : ℂ) :
    (charApproxC J E c N).eval (-z) = (charApproxC J E c N).eval z := by
  rw [eval_charApproxC, eval_charApproxC, ← sum_compl_eq]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [isingWeight_compl]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [spin_compl]
  push_cast
  ring

/-- **Real coefficients.** Conjugation fixes `Q_N`. -/
theorem map_conj_charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (N : ℕ) :
    (charApproxC J E c N).map (starRingEnd ℂ) = charApproxC J E c N := by
  unfold charApproxC
  rw [Polynomial.map_sum]
  conv_rhs => rw [← sum_compl_eq]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Complex.conj_ofReal,
    isingWeight_compl]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, spin_compl]
  congr 3
  simp only [map_div₀, map_mul, conj_I, Complex.conj_ofReal, map_natCast]
  push_cast
  ring

theorem eval_conj_charApproxC (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (N : ℕ) (z : ℂ) :
    (charApproxC J E c N).eval (conj z) = conj ((charApproxC J E c N).eval z) := by
  conv_lhs => rw [← map_conj_charApproxC J E c N]
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

/-- **Lee–Yang below the axis.** For `Im z < 0`, `N ≥ 1`, positive masses and ferromagnetic bonds,
`Q_N(z) ≠ 0`. -/
theorem eval_charApproxC_ne_zero_of_im_neg {J : V → V → ℝ} {E : Finset (V × V)} {c : V → ℝ}
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 < c k) {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (hz : z.im < 0) : (charApproxC J E c N).eval z ≠ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set u : V → ℂ := fun k => 1 + I * (c k : ℂ) * z / N with hu
  set v : V → ℂ := fun k => 1 - I * (c k : ℂ) * z / N with hv
  have hure : ∀ k, (u k).re = 1 - c k * z.im / N := by
    intro k; simp [hu, Complex.div_re, Complex.mul_re, Complex.mul_im]; field_simp; ring
  have huim : ∀ k, (u k).im = c k * z.re / N := by
    intro k; simp [hu, Complex.div_im, Complex.mul_re, Complex.mul_im]; field_simp
  have hvre : ∀ k, (v k).re = 1 + c k * z.im / N := by
    intro k; simp [hv, Complex.div_re, Complex.mul_re, Complex.mul_im]; field_simp; ring
  have hvim : ∀ k, (v k).im = -(c k * z.re / N) := by
    intro k; simp [hv, Complex.div_im, Complex.mul_re, Complex.mul_im]; field_simp
  have hcy : ∀ k, c k * z.im / N < 0 := fun k =>
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hc k) hz) hNpos
  have hu0 : ∀ k, u k ≠ 0 := by
    intro k h
    have := congrArg Complex.re h
    rw [hure k, Complex.zero_re] at this
    linarith [hcy k]
  have hnorm : ∀ k, ‖v k‖ < ‖u k‖ := by
    intro k
    have h1 : ‖v k‖ ^ 2 < ‖u k‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply, hure, huim, hvre, hvim]
      nlinarith [hcy k]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  set r : V → ℂ := fun k => (v k / u k) ^ N with hr
  have hr1 : ∀ k, ‖r k‖ < 1 := by
    intro k
    rw [hr, norm_pow, norm_div]
    have h0 : ‖v k‖ / ‖u k‖ < 1 := (div_lt_one (norm_pos_iff.mpr (hu0 k))).mpr (hnorm k)
    exact pow_lt_one₀ (by positivity) h0 (by omega)
  -- factor the evaluation
  have hfac : ∀ D : Finset V, ∏ k, (1 + I * ((c k * spin D k : ℝ) : ℂ) / N * z) ^ N =
      (∏ k, u k ^ N) * ∏ k ∈ D, r k := by
    intro D
    have hite : ∀ k, (1 + I * ((c k * spin D k : ℝ) : ℂ) / N * z) ^ N =
        if k ∈ D then u k ^ N * r k else u k ^ N := by
      intro k
      by_cases hk : k ∈ D
      · rw [if_pos hk, hr, ← mul_pow, mul_div_cancel₀ _ (hu0 k), hv]
        simp only [spin, if_pos hk]
        congr 1; push_cast; ring
      · rw [if_neg hk, hu]
        simp only [spin, if_neg hk]
        congr 1; push_cast; ring
    simp_rw [hite]
    rw [Finset.prod_ite, Finset.prod_mul_distrib]
    have hfil : (Finset.univ.filter fun k => k ∈ D) = D := by ext k; simp
    rw [hfil]
    rw [show (∏ k ∈ D, u k ^ N) * (∏ k ∈ D, r k) * ∏ k ∈ Finset.univ.filter (fun k => k ∉ D),
        u k ^ N = ((∏ k ∈ D, u k ^ N) * ∏ k ∈ Finset.univ.filter (fun k => k ∉ D), u k ^ N) *
          ∏ k ∈ D, r k by ring]
    congr 1
    have hsplit := Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
      (p := fun k => k ∈ D) (f := fun k => u k ^ N)
    rw [hfil] at hsplit
    exact hsplit
  have heval : (charApproxC J E c N).eval z = (∏ k, u k ^ N) * (1 / (Zpart J E : ℂ)) *
      ((Real.exp (∑ p ∈ E, J p.1 p.2) : ℂ) *
        maEval (isingCoeff (fun i j => Real.exp (-2 * J i j)) (E.filter fun p => p.1 ≠ p.2)) r) := by
    rw [eval_charApproxC, maEval, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [hfac D]
    have hw := isingWeight_eq_isingCoeff J E D
    rw [show (((isingWeight J E D / Zpart J E : ℝ)) : ℂ) =
      (isingWeight J E D : ℂ) / (Zpart J E : ℂ) by push_cast; ring, hw]
    ring
  rw [heval]
  have hZ : (Zpart J E : ℂ) ≠ 0 := by exact_mod_cast (Zpart_pos J E).ne'
  refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ =>
    pow_ne_zero _ (hu0 k)) (one_div_ne_zero hZ)) (mul_ne_zero (by exact_mod_cast
      (Real.exp_pos _).ne') ?_)
  refine leeYang_polydisc _ _ (fun p hp => (Finset.mem_filter.mp hp).2) (fun p hp => ?_) r hr1
  have hJp := hJ p (Finset.mem_filter.mp hp).1
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- **All zeros of `Q_N` are real.** -/
theorem im_eq_zero_of_eval_charApproxC_eq_zero {J : V → V → ℝ} {E : Finset (V × V)}
    {c : V → ℝ} (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 < c k) (N : ℕ) {z : ℂ}
    (hz : (charApproxC J E c N).eval z = 0) : z.im = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [eval_charApproxC_zero] at hz; exact absurd hz one_ne_zero
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact eval_charApproxC_ne_zero_of_im_neg hJ hc hN h hz
  · have h' : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
    apply eval_charApproxC_ne_zero_of_im_neg hJ hc hN h'
    rw [eval_conj_charApproxC, hz, map_zero]

/-- **Even real-rooted approximation.** -/
theorem exists_even_realRooted_approx (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ)
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 ≤ c k) :
    ∃ q : ℕ → ℝ[X], (∀ N, (q N).Splits) ∧ (∀ N z, polyEvalC (q N) (-z) = polyEvalC (q N) z) ∧
      TendstoLocallyUniformly (fun N => polyEvalC (q N)) (isingCharFn J E c) atTop := by
  have hlift : ∀ N, ∃ q : ℝ[X], q.map (algebraMap ℝ ℂ) = charApproxC J E (shiftMass c N) N := by
    intro N
    refine (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr fun n => ⟨(
      (charApproxC J E (shiftMass c N) N).coeff n).re, ?_⟩)
    have h := congrArg (fun p : ℂ[X] => p.coeff n) (map_conj_charApproxC J E (shiftMass c N) N)
    simp only [Polynomial.coeff_map] at h
    exact (Complex.conj_eq_iff_re.mp h)
  choose q hq using hlift
  have heval : ∀ N z, polyEvalC (q N) z = (charApproxC J E (shiftMass c N) N).eval z := by
    intro N z; rw [polyEvalC_eq_eval_map, hq]
  refine ⟨q, fun N => ?_, fun N z => ?_, ?_⟩
  · refine splits_of_forall_complex_root_real _ (q N) le_rfl fun z hz => ?_
    have : polyEvalC (q N) z = 0 := hz
    rw [heval] at this
    exact im_eq_zero_of_eval_charApproxC_eq_zero hJ (shiftMass_pos hc N) N this
  · rw [heval, heval, eval_neg_charApproxC]
  · have h := tendstoLocallyUniformly_charApproxC_shiftMass J E c
    exact h.congr fun N z => (heval N z).symm


/-! ## Consequences for the characteristic function -/

theorem isingCharFn_zero (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) :
    isingCharFn J E c 0 = 1 := by
  rw [isingCharFn]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_sum]
  exact div_self (by exact_mod_cast (Zpart_pos J E).ne')

theorem differentiable_isingCharFn (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) :
    Differentiable ℂ (isingCharFn J E c) := by
  unfold isingCharFn
  fun_prop

/-- **Real zeros.** -/
theorem im_eq_zero_of_isingCharFn_eq_zero {J : V → V → ℝ} {E : Finset (V × V)} {c : V → ℝ}
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 ≤ c k) {z : ℂ}
    (hz : isingCharFn J E c z = 0) : z.im = 0 := by
  exact zero_mem_closed_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_charApproxC_shiftMass J E c)
    (fun w _ => Differentiable.analyticAt (differentiable_isingCharFn J E c) w)
    (Eventually.of_forall fun N => Polynomial.differentiable _)
    (isClosed_eq Complex.continuous_im continuous_const)
    (Eventually.of_forall fun N w hw =>
      im_eq_zero_of_eval_charApproxC_eq_zero hJ (shiftMass_pos hc N) N hw)
    (a := 0) (by rw [isingCharFn_zero]; exact one_ne_zero) hz

/-- **Newman-type Gaussian bound.** `‖φ(z)‖² ≤ exp(‖z‖² L(φ))`. -/
theorem norm_sq_isingCharFn_le {J : V → V → ℝ} {E : Finset (V × V)} {c : V → ℝ}
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 ≤ c k) (z : ℂ) :
    ‖isingCharFn J E c z‖ ^ 2 ≤ Real.exp (‖z‖ ^ 2 * (lagRatio (isingCharFn J E c)).re) := by
  obtain ⟨q, hsplit, heven, hconv⟩ := exists_even_realRooted_approx J E c hJ hc
  have h := norm_sq_le_of_tendsto_even hsplit heven hconv
    (by rw [isingCharFn_zero]; exact one_ne_zero) z
  rwa [isingCharFn_zero, norm_one, one_pow, one_mul] at h

/-- **Gaussian decay on the real axis before the first zero.** -/
theorem isingCharFn_mul_neg_le {J : V → V → ℝ} {E : Finset (V × V)} {c : V → ℝ}
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 ≤ c k) {t : ℝ}
    (hne : ∀ s : ℝ, |s| ≤ |t| → isingCharFn J E c s ≠ 0) :
    (isingCharFn J E c t * isingCharFn J E c (-t)).re ≤
      Real.exp (-(t ^ 2 * (lagRatio (isingCharFn J E c)).re)) := by
  obtain ⟨q, hsplit, heven, hconv⟩ := exists_even_realRooted_approx J E c hJ hc
  have h := mul_neg_le_of_tendsto_even hsplit hconv
    (by rw [isingCharFn_zero]; exact one_ne_zero) hne
  rwa [isingCharFn_zero, norm_one, one_pow, one_mul] at h

theorem isingCharFn_neg (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (z : ℂ) :
    isingCharFn J E c (-z) = isingCharFn J E c z := by
  rw [isingCharFn, isingCharFn, ← sum_compl_eq]
  congr 1
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [isingWeight_compl]
  congr 2
  simp only [spin_compl]
  push_cast
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

end

end GaloisForLFunctions.HTGeometry.LeeYang
