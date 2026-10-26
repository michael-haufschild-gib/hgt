import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions
import GaloisForLFunctions.StripBochnerWeilForcing.PositiveDefiniteSectionsAreCompletelyMonotone

/-!
# Lattice-Sieved Post–Widder Positivity and the Landau Real Anchor

Let `H = A + G` on a right half-plane, where `A(s) = Σ b(n) n^{−s}` is a Dirichlet series with
nonnegative coefficients (a *lattice* term: its Bochner scale measure is carried by `{log n}`) and
`G(s) = Σ_{z ∈ S} c(z)/(s − z)` is a finite polar sum (an absolutely continuous scale density
`w(t) = Σ c(z) e^{t Re z} cos(t Im z)`). This module proves that positive-definite vertical sections
of `Re H` force the **continuous part alone** to be positive, and that a positive exponential-cosine
density is anchored at a real pole.

1. **Post–Widder kernels on the logarithmic lattice (`postWidderKernel`,
   `tendsto_postWidder_lattice`).** The order-`k` Post–Widder kernel at scale `t` is bounded by
   `(k/t)(r e^{1−r})^k`, `r = L/t`, so every atom `L = log n ≠ t` is annihilated as `k → ∞`, with a
   uniform `(k/t)(2e^{−2})^k e^{4σ₀ t} n^{−σ₀}` bound beyond `log n ≥ 4t`.

2. **Lattice sieve (`polarScaleWeight_nonneg_of_lattice_posDef`).** Positive-definite sections make
   `x ↦ H(x)` completely monotone; its Post–Widder transform at scale `t` is the lattice part (which
   tends to `0` off `log ℕ`) plus the polar part (which tends to `w(t)`). Hence `w(t) ≥ 0` off the
   countable set `log ℕ`, and everywhere on `(0, ∞)` by continuity.

3. **Evenness forces conjugation symmetry (`polarSum_eq_conj_polarSum_conj_of_even`).** If
   `u ↦ Re G(σ + iu)` is even, `G − conj ∘ G ∘ conj` has vanishing real part, hence vanishing
   derivative (Cauchy–Riemann), hence is a constant that decays at `+∞`.

4. **Landau real anchor (`landau_real_anchor`).** A nonnegative density `w` has Laplace transform
   `G`, so `|G(x + ib)| ≤ G(x)` to the right of the top abscissa `σ*`. Multiplying by `x − σ*` and
   letting `x ↓ σ*` compares residues: `|c(σ* + ib)| ≤ c(σ*)`. A nonzero weight on the top line
   therefore forces a **real** point `σ* ∈ S` of strictly positive weight.

5. **The lattice real anchor (`lattice_real_anchor`).** Combining 2–4: for every lattice series
   plus finite polar sum with even positive-definite sections, the rightmost polar singularity of
   nonzero weight sits on the real axis with positive weight dominating the whole top line.
-/

open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry StripBochnerWeilForcing

/-! ## §1. Post–Widder kernels on the logarithmic lattice -/

/-- Post–Widder kernel of order `k` at scale `t`: `K_k(t, L) = (k/t)^{k+1} L^k e^{−kL/t} / k!`. -/
def postWidderKernel (k : ℕ) (t L : ℝ) : ℝ :=
  ((k : ℝ) / t) ^ (k + 1) * L ^ k * Real.exp (-((k : ℝ) / t) * L) / (k.factorial : ℝ)

theorem postWidderKernel_nonneg (k : ℕ) {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) :
    0 ≤ postWidderKernel k t L := by
  unfold postWidderKernel
  have : 0 ≤ (k : ℝ) / t := div_nonneg (Nat.cast_nonneg k) ht.le
  positivity

/-- Stirling-free kernel bound `K_k(t, L) ≤ (k/t) (r e^{1−r})^k` with `r = L/t`. -/
theorem postWidderKernel_le (k : ℕ) {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) :
    postWidderKernel k t L ≤ (k / t) * ((L / t) * Real.exp (1 - L / t)) ^ k := by
  have hfac : (k : ℝ) ^ k / k.factorial ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg k) k
  have hk : 0 ≤ (k : ℝ) / t := div_nonneg (Nat.cast_nonneg k) ht.le
  have hA : 0 ≤ (L / t) ^ k * Real.exp (-(k : ℝ) * (L / t)) := by
    have : 0 ≤ L / t := div_nonneg hL ht.le
    positivity
  have hlhs : postWidderKernel k t L =
      (k / t) * ((k : ℝ) ^ k / k.factorial) * ((L / t) ^ k * Real.exp (-(k : ℝ) * (L / t))) := by
    unfold postWidderKernel
    rw [show -((k : ℝ) / t) * L = -(k : ℝ) * (L / t) by ring, div_pow, div_pow, pow_succ]
    have ht0 : t ≠ 0 := ht.ne'
    field_simp
    ring
  have hrhs : (k / t) * ((L / t) * Real.exp (1 - L / t)) ^ k =
      (k / t) * Real.exp k * ((L / t) ^ k * Real.exp (-(k : ℝ) * (L / t))) := by
    rw [mul_pow, ← Real.exp_nat_mul,
      show (k : ℝ) * (1 - L / t) = k + (-(k : ℝ) * (L / t)) by ring, Real.exp_add]
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hk) hA

/-- The profile `r e^{1−r}` is strictly below `1` away from `r = 1`. -/
theorem mul_exp_one_sub_lt_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≠ 1) :
    r * Real.exp (1 - r) < 1 := by
  have h := Real.add_one_lt_exp (x := r - 1) (sub_ne_zero.mpr hr1)
  have he : Real.exp (1 - r) = (Real.exp (r - 1))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [he, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  linarith

/-- Tail bound: for `r ≥ 4` and `2κ ≤ k`, `(r e^{1−r})^k e^{κ r} ≤ (2e^{−2})^k e^{4κ}`. -/
theorem mul_exp_one_sub_pow_mul_exp_le {r κ : ℝ} {k : ℕ} (hr : 4 ≤ r) (hκ : 2 * κ ≤ k) :
    (r * Real.exp (1 - r)) ^ k * Real.exp (κ * r) ≤
      (2 * Real.exp (-2)) ^ k * Real.exp (4 * κ) := by
  have h1 : r * Real.exp (1 - r) ≤ 2 * Real.exp (-(r / 2)) := by
    have h := Real.add_one_le_exp (r / 2 - 1)
    have e : Real.exp (r / 2 - 1) * Real.exp (1 - r) = Real.exp (-(r / 2)) := by
      rw [← Real.exp_add]; ring_nf
    calc r * Real.exp (1 - r) ≤ (2 * Real.exp (r / 2 - 1)) * Real.exp (1 - r) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(r / 2)) := by rw [mul_assoc, e]
  have h0 : 0 ≤ r * Real.exp (1 - r) := mul_nonneg (by linarith) (Real.exp_pos _).le
  calc (r * Real.exp (1 - r)) ^ k * Real.exp (κ * r)
      ≤ (2 * Real.exp (-(r / 2))) ^ k * Real.exp (κ * r) := by gcongr
    _ = 2 ^ k * Real.exp (-((k : ℝ) / 2 - κ) * r) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 2 ^ k * Real.exp (-((k : ℝ) / 2 - κ) * 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    _ = (2 * Real.exp (-2)) ^ k * Real.exp (4 * κ) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; ring_nf

theorem two_mul_exp_neg_two_lt_one : 2 * Real.exp (-2) < 1 := by
  have h := Real.add_one_le_exp (2 : ℝ)
  have hpos := Real.exp_pos (2 : ℝ)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one hpos]
  linarith

/-- **Post–Widder annihilation of the logarithmic lattice.** For nonnegative coefficients with
`Σ b(n) n^{−σ₀} < ∞` and a scale `t > 0` off `log ℕ`, the Post–Widder transform
`Σ b(n) K_k(t, log n)` of the lattice measure tends to `0`. -/
theorem tendsto_postWidder_lattice {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {σ₀ : ℝ}
    (hsum : Summable fun n : ℕ => b n * (n : ℝ) ^ (-σ₀)) {t : ℝ} (ht : 0 < t)
    (hlat : ∀ n : ℕ, Real.log n ≠ t) :
    Tendsto (fun k : ℕ => ∑' n : ℕ, b n * postWidderKernel k t (Real.log n)) atTop (𝓝 0) := by
  set N : ℕ := ⌈Real.exp (4 * t)⌉₊ + 1
  set g : ℕ → ℝ := fun n => (Real.log n / t) * Real.exp (1 - Real.log n / t)
  set q : ℝ := 2 * Real.exp (-2)
  set C : ℝ := Real.exp (4 * (σ₀ * t)) * ∑' n : ℕ, b n * (n : ℝ) ^ (-σ₀)
  have hlog_nn : ∀ n : ℕ, 0 ≤ Real.log n := fun n => Real.log_natCast_nonneg n
  have hg_nn : ∀ n, 0 ≤ g n := fun n =>
    mul_nonneg (div_nonneg (hlog_nn n) ht.le) (Real.exp_pos _).le
  have hg_lt : ∀ n, g n < 1 := fun n =>
    mul_exp_one_sub_lt_one (div_nonneg (hlog_nn n) ht.le) fun h => hlat n (by
      field_simp at h; linarith)
  have hq_nn : 0 ≤ q := by positivity
  have hq_lt : q < 1 := two_mul_exp_neg_two_lt_one
  have hC_nn : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (tsum_nonneg fun n => mul_nonneg (hb n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  -- termwise domination for `2 σ₀ t ≤ k`
  set B : ℕ → ℕ → ℝ := fun k n =>
    (k / t) * ((if n < N then b n * g n ^ k else 0) +
      q ^ k * Real.exp (4 * (σ₀ * t)) * (b n * (n : ℝ) ^ (-σ₀)))
  have hdom : ∀ k : ℕ, 2 * (σ₀ * t) ≤ k → ∀ n : ℕ,
      b n * postWidderKernel k t (Real.log n) ≤ B k n := by
    intro k hk n
    have hK := postWidderKernel_le k ht (hlog_nn n)
    have hkt : 0 ≤ (k : ℝ) / t := div_nonneg (Nat.cast_nonneg k) ht.le
    have hsec : 0 ≤ q ^ k * Real.exp (4 * (σ₀ * t)) * (b n * (n : ℝ) ^ (-σ₀)) :=
      mul_nonneg (mul_nonneg (pow_nonneg hq_nn k) (Real.exp_pos _).le)
        (mul_nonneg (hb n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    by_cases hn : n < N
    · simp only [B, if_pos hn]
      calc b n * postWidderKernel k t (Real.log n) ≤ b n * ((k / t) * g n ^ k) :=
            mul_le_mul_of_nonneg_left hK (hb n)
        _ = (k / t) * (b n * g n ^ k) := by ring
        _ ≤ (k / t) * (b n * g n ^ k + q ^ k * Real.exp (4 * (σ₀ * t)) *
              (b n * (n : ℝ) ^ (-σ₀))) := by
            apply mul_le_mul_of_nonneg_left _ hkt; linarith
    · simp only [B, if_neg hn, zero_add]
      have hnN : N ≤ n := Nat.le_of_not_lt hn
      have hn1 : (1 : ℝ) ≤ n := by
        have : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hnN; exact_mod_cast this
      have hnpos : (0 : ℝ) < n := by linarith
      have hexp_le : Real.exp (4 * t) ≤ n := by
        have h1 : Real.exp (4 * t) ≤ (⌈Real.exp (4 * t)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈Real.exp (4 * t)⌉₊ : ℝ) ≤ n := by
          have : ⌈Real.exp (4 * t)⌉₊ ≤ n := le_trans (Nat.le_succ _) hnN; exact_mod_cast this
        linarith
      have hlogn : 4 * t ≤ Real.log n := by
        rw [← Real.log_exp (4 * t)]; exact Real.log_le_log (Real.exp_pos _) hexp_le
      have hr4 : 4 ≤ Real.log n / t := by rw [le_div_iff₀ ht]; linarith
      have htail := mul_exp_one_sub_pow_mul_exp_le (κ := σ₀ * t) hr4 hk
      have hrpow : (n : ℝ) ^ (-σ₀) = Real.exp (-(σ₀ * t) * (Real.log n / t)) := by
        rw [Real.rpow_def_of_pos hnpos]; congr 1; field_simp
      have hgk : g n ^ k ≤ q ^ k * Real.exp (4 * (σ₀ * t)) * (n : ℝ) ^ (-σ₀) := by
        have hE : 0 < Real.exp ((σ₀ * t) * (Real.log n / t)) := Real.exp_pos _
        have hsplit : g n ^ k = (g n ^ k * Real.exp ((σ₀ * t) * (Real.log n / t))) *
            Real.exp (-(σ₀ * t) * (Real.log n / t)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
        rw [hsplit, hrpow]
        exact mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
      calc b n * postWidderKernel k t (Real.log n) ≤ b n * ((k / t) * g n ^ k) :=
            mul_le_mul_of_nonneg_left hK (hb n)
        _ ≤ b n * ((k / t) * (q ^ k * Real.exp (4 * (σ₀ * t)) * (n : ℝ) ^ (-σ₀))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgk hkt) (hb n)
        _ = (k / t) * (q ^ k * Real.exp (4 * (σ₀ * t)) * (b n * (n : ℝ) ^ (-σ₀))) := by ring
  have hBsum : ∀ k : ℕ, Summable (B k) := by
    intro k
    refine Summable.mul_left _ (Summable.add ?_ (hsum.mul_left _))
    refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
    rw [Finset.mem_range] at hn
    exact if_neg hn
  have hBtsum : ∀ k : ℕ, ∑' n, B k n =
      (k / t) * (∑ n ∈ Finset.range N, b n * g n ^ k) + (k / t) * q ^ k * C := by
    intro k
    have hfin : ∑' n : ℕ, (if n < N then b n * g n ^ k else 0) =
        ∑ n ∈ Finset.range N, b n * g n ^ k := by
      rw [tsum_eq_sum (s := Finset.range N) fun n hn => by
        rw [Finset.mem_range] at hn; exact if_neg hn]
      exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
    have hs1 : Summable fun n : ℕ => (if n < N then b n * g n ^ k else 0) :=
      summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
        rw [Finset.mem_range] at hn; exact if_neg hn
    simp only [B]
    rw [tsum_mul_left, Summable.tsum_add hs1 (hsum.mul_left _), hfin, tsum_mul_left]
    simp only [C]; ring
  have hlimU : Tendsto (fun k : ℕ => (k / t) * (∑ n ∈ Finset.range N, b n * g n ^ k) +
      (k / t) * q ^ k * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ∑ n ∈ Finset.range N, (b n / t) * ((k : ℝ) * g n ^ k))
        atTop (𝓝 (∑ n ∈ Finset.range N, (b n / t) * 0)) :=
      tendsto_finsetSum _ fun n _ =>
        (tendsto_self_mul_const_pow_of_lt_one (hg_nn n) (hg_lt n)).const_mul _
    have h2 : Tendsto (fun k : ℕ => (C / t) * ((k : ℝ) * q ^ k)) atTop (𝓝 ((C / t) * 0)) :=
      (tendsto_self_mul_const_pow_of_lt_one hq_nn hq_lt).const_mul _
    simp only [mul_zero, Finset.sum_const_zero] at h1 h2
    have h12 := h1.add h2
    rw [add_zero] at h12
    refine h12.congr fun k => ?_
    rw [Finset.mul_sum]
    simp only [add_zero]
    congr 1
    · exact Finset.sum_congr rfl fun n _ => by ring
    · ring
  refine squeeze_zero' (Eventually.of_forall fun k => tsum_nonneg fun n =>
    mul_nonneg (hb n) (postWidderKernel_nonneg k ht (hlog_nn n))) ?_ hlimU
  filter_upwards [eventually_ge_atTop ⌈2 * (σ₀ * t)⌉₊] with k hk
  have hk' : 2 * (σ₀ * t) ≤ k := (Nat.ceil_le.mp hk)
  rw [← hBtsum k]
  exact Summable.tsum_le_tsum (hdom k hk') (Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hb n) (postWidderKernel_nonneg k ht (hlog_nn n))) (hdom k hk')
    (hBsum k)) (hBsum k)

/-! ## §2. Post–Widder inversion of finite polar sums -/

/-- Iterated derivatives of a finite polar sum to the right of its poles. -/
theorem iterate_deriv_polarSum_eqOn {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ}
    (hSa : ∀ z ∈ S, z.re ≤ a) (n : ℕ) :
    EqOn (deriv^[n] (polarSum S c))
      (fun s : ℂ => (-1 : ℂ) ^ n * (n.factorial : ℂ) *
        ∑ z ∈ S, (c z : ℂ) * ((s - z) ^ (n + 1))⁻¹)
      {s : ℂ | a < s.re} := by
  have hU : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  induction n with
  | zero =>
      intro s _
      simp [polarSum, div_eq_mul_inv]
  | succ n ih =>
      intro s hs
      have hs_re : a < s.re := hs
      rw [Function.iterate_succ_apply']
      have hev : deriv^[n] (polarSum S c) =ᶠ[𝓝 s]
          fun w : ℂ => (-1 : ℂ) ^ n * (n.factorial : ℂ) *
            ∑ z ∈ S, (c z : ℂ) * ((w - z) ^ (n + 1))⁻¹ :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => ih hw
      rw [hev.deriv_eq]
      have hterm : ∀ z ∈ S, HasDerivAt
          (fun w : ℂ => (c z : ℂ) * ((w - z) ^ (n + 1))⁻¹)
          (-(c z : ℂ) * ((n + 1 : ℕ) : ℂ) * ((s - z) ^ (n + 2))⁻¹) s := by
        intro z hz
        have hsz : s - z ≠ 0 := fun h0 => by
          have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
        have hd1 : HasDerivAt (fun w : ℂ => (w - z) ^ (n + 1))
            (((n + 1 : ℕ) : ℂ) * (s - z) ^ n * 1) s :=
          ((hasDerivAt_id s).sub_const z).pow (n + 1)
        have hd2 := (hd1.inv (pow_ne_zero (n + 1) hsz)).const_mul (c z : ℂ)
        refine hd2.congr_deriv ?_
        have hpow1 : (s - z) ^ (n + 1) ≠ 0 := pow_ne_zero _ hsz
        have hpow2 : (s - z) ^ (n + 2) ≠ 0 := pow_ne_zero _ hsz
        field_simp [hpow1, hpow2]
        ring
      have hsum_d := (HasDerivAt.fun_sum hterm).const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
      rw [hsum_d.deriv, Nat.factorial_succ, pow_succ]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring

theorem tendsto_inv_one_sub_div_pow_succ_exp (w : ℂ) :
    Tendsto (fun n : ℕ => ((1 - w / (n : ℂ))⁻¹) ^ (n + 1)) atTop (𝓝 (Complex.exp w)) := by
  have hexp : Tendsto (fun n : ℕ => (1 + (-w) / (n : ℂ)) ^ n) atTop (𝓝 (Complex.exp (-w))) :=
    Complex.tendsto_one_add_div_pow_exp (-w)
  have hinv_exp : Tendsto (fun n : ℕ => ((1 + (-w) / (n : ℂ)) ^ n)⁻¹) atTop
      (𝓝 ((Complex.exp (-w))⁻¹)) :=
    hexp.inv₀ (Complex.exp_ne_zero (-w))
  have h1 : Tendsto (fun n : ℕ => (1 - w / (n : ℂ))⁻¹) atTop (𝓝 ((1 - 0 : ℂ)⁻¹)) := by
    have hdiv : Tendsto (fun n : ℕ => w / (n : ℂ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
        have hr : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp
            (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        simpa using hr
      simpa [div_eq_mul_inv] using hn.const_mul w
    exact (tendsto_const_nhds.sub hdiv).inv₀ (by norm_num)
  have hprod := hinv_exp.mul h1
  have hlim : (Complex.exp (-w))⁻¹ * (1 - 0 : ℂ)⁻¹ = Complex.exp w := by
    rw [Complex.exp_neg, inv_inv, sub_zero, inv_one, mul_one]
  rw [hlim] at hprod
  refine hprod.congr fun n => ?_
  have heq : 1 + (-w) / (n : ℂ) = 1 - w / (n : ℂ) := by ring
  rw [heq, pow_succ, inv_pow]

/-- **Post–Widder inversion of a polar sum.** At scale `t > 0`,
`(x^{k+1}/k!) (−1)^k Re G^{(k)}(x)` at `x = k/t` tends to the scale weight
`Σ c(z) e^{t Re z} cos(t Im z)`. -/
theorem tendsto_postWidder_polarSum {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ}
    (hSa : ∀ z ∈ S, z.re ≤ a) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => ((k : ℝ) / t) ^ (k + 1) / (k.factorial : ℝ) *
      ((-1 : ℝ) ^ k * ((deriv^[k] (polarSum S c)) (((k : ℝ) / t : ℝ) : ℂ)).re))
      atTop (𝓝 (polarScaleWeight S c t)) := by
  have hlim : Tendsto
      (fun n : ℕ => (∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1)).re)
      atTop (𝓝 (polarScaleWeight S c t)) := by
    have hc_lim : Tendsto
        (fun n : ℕ => ∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1))
        atTop (𝓝 (∑ z ∈ S, (c z : ℂ) * Complex.exp (z * (t : ℂ)))) :=
      tendsto_finsetSum S fun z _ =>
        (tendsto_inv_one_sub_div_pow_succ_exp (z * (t : ℂ))).const_mul (c z : ℂ)
    have hre_lim := (Complex.continuous_re.tendsto _).comp hc_lim
    have htarget : (∑ z ∈ S, (c z : ℂ) * Complex.exp (z * (t : ℂ))).re =
        polarScaleWeight S c t := by
      unfold polarScaleWeight
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Complex.re_ofReal_mul, Complex.exp_re]
      have hre_zt : (z * (t : ℂ)).re = z.re * t := by simp
      have him_zt : (z * (t : ℂ)).im = z.im * t := by simp
      rw [hre_zt, him_zt, mul_assoc]
    rwa [htarget] at hre_lim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (a * t) + 1)] with n hn
  have hn_pos : 0 < n := by omega
  have hn_gt : a * t < (n : ℝ) := by
    have hceil : a * t ≤ (Nat.ceil (a * t) : ℝ) := Nat.le_ceil (a * t)
    have hn_cast : (Nat.ceil (a * t) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set xn : ℝ := (n : ℝ) / t
  have hxn_gt : a < xn := (lt_div_iff₀ ht).mpr hn_gt
  have hxn_pos : 0 < xn := div_pos (by exact_mod_cast hn_pos) ht
  have hderiv_eq := iterate_deriv_polarSum_eqOn (c := c) hSa n
    (show (xn : ℂ) ∈ {s : ℂ | a < s.re} by simp [hxn_gt])
  have hcast : ((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) *
        ∑ z ∈ S, (c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹) =
      ∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1) := by
    have hfac_ne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hxnC : (xn : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxn_pos.ne'
    have hpref : ((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
        ((-1 : ℂ) ^ n * (n.factorial : ℂ)) = (xn : ℂ) ^ (n + 1) := by
      push_cast
      calc (xn : ℂ) ^ (n + 1) / (n.factorial : ℂ) * (-1 : ℂ) ^ n *
            ((-1 : ℂ) ^ n * (n.factorial : ℂ))
          = (xn : ℂ) ^ (n + 1) * (((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
              ((n.factorial : ℂ) / (n.factorial : ℂ))) := by ring
        _ = (xn : ℂ) ^ (n + 1) := by
            rw [show (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 from by rw [← mul_pow]; norm_num,
                div_self hfac_ne, mul_one, mul_one]
    rw [← mul_assoc, hpref, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hxz : (xn : ℂ) - z ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
    have hratio : ((xn : ℂ) - z) / (xn : ℂ) = 1 - z * (t : ℂ) / (n : ℂ) := by
      dsimp [xn]; push_cast; field_simp [hnC, htC]
    calc (xn : ℂ) ^ (n + 1) * ((c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹)
        = (c z : ℂ) * ((((xn : ℂ) - z) / (xn : ℂ))⁻¹) ^ (n + 1) := by
            rw [inv_div, div_pow, inv_eq_one_div]
            field_simp [pow_ne_zero (n + 1) hxz, pow_ne_zero (n + 1) hxnC]
      _ = (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1) := by rw [hratio]
  have hre_lhs : (((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) *
        ∑ z ∈ S, (c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹)).re =
      xn ^ (n + 1) / (n.factorial : ℝ) *
        ((-1 : ℝ) ^ n * ((deriv^[n] (polarSum S c)) (xn : ℂ)).re) := by
    rw [hderiv_eq, Complex.re_ofReal_mul]
    ring
  rw [← hcast, hre_lhs]

/-! ## §3. The lattice sieve -/

/-- Iterated derivatives are additive on an open set where both summands are holomorphic. -/
theorem iterate_deriv_add_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (k : ℕ) :
    EqOn (deriv^[k] (fun s => f s + g s)) (fun s => deriv^[k] f s + deriv^[k] g s) U := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    simp only [Function.iterate_succ_apply']
    have hev : deriv^[k] (fun s => f s + g s) =ᶠ[𝓝 s]
        fun s => deriv^[k] f s + deriv^[k] g s :=
      Filter.eventually_of_mem (hU.mem_nhds hs) ih
    rw [hev.deriv_eq]
    exact deriv_add
      (((differentiableOn_iterate_deriv hU hf k) s hs).differentiableAt (hU.mem_nhds hs))
      (((differentiableOn_iterate_deriv hU hg k) s hs).differentiableAt (hU.mem_nhds hs))

/-- `(−1)^k` times the `k`-th derivative of a real lattice series at a real point beyond its
abscissa is `Σ b(n) (log n)^k n^{−x}`. -/
theorem neg_one_pow_mul_re_iterate_deriv_LSeries {b : ℕ → ℝ} (k : ℕ) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < x) :
    (-1 : ℝ) ^ k * ((deriv^[k] (LSeries fun n => (b n : ℂ))) (x : ℂ)).re =
      ∑' n : ℕ, b n * Real.log n ^ k * (n : ℝ) ^ (-x) := by
  rw [← iteratedDeriv_eq_iterate, LSeries_iteratedDeriv k (by simpa using hx)]
  have hlog : ∀ n : ℕ, (LSeries.logMul^[k] fun n => (b n : ℂ)) n =
      ((Real.log n ^ k * b n : ℝ) : ℂ) := by
    intro n
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, ← Complex.natCast_log]
      push_cast; ring
  have hL : LSeries (LSeries.logMul^[k] fun n => (b n : ℂ)) (x : ℂ) =
      ((∑' n : ℕ, b n * Real.log n ^ k * (n : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, hlog n]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hcp : ((n : ℂ)) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hnpos.le]; simp
      rw [hcp, Real.rpow_neg hnpos.le, ← Complex.ofReal_div]
      congr 1
      ring
  rw [hL, show ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← mul_assoc, ← mul_pow]
  norm_num

/-- **Lattice sieve off `log ℕ`.** If a nonnegative lattice series plus a finite polar sum has
positive-definite vertical sections on `σ > a`, the polar scale weight is nonnegative at every
scale `t > 0` not of the form `log n`. -/
theorem polarScaleWeight_nonneg_of_lattice_posDef_of_ne_log {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ} (hSa : ∀ z ∈ S, z.re ≤ a)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < a)
    (hpd : ∀ σ : ℝ, a < σ → IsPosDef fun u : ℝ =>
      (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    {t : ℝ} (ht : 0 < t) (hlat : ∀ n : ℕ, Real.log n ≠ t) :
    0 ≤ polarScaleWeight S c t := by
  set f : ℕ → ℂ := fun n => (b n : ℂ) with hfdef
  set H : ℂ → ℂ := fun s => LSeries f s + polarSum S c s with hHdef
  set U : Set ℂ := {s : ℂ | a < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have habs' : ∀ s : ℂ, a < s.re → LSeries.abscissaOfAbsConv f < s.re := fun s hs =>
    lt_trans habs (EReal.coe_lt_coe_iff.mpr hs)
  have hLd : DifferentiableOn ℂ (LSeries f) U := fun s hs =>
    (LSeries_hasDerivAt (habs' s hs)).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℂ (polarSum S c) U := by
    intro s hs
    change a < s.re at hs
    unfold polarSum
    refine DifferentiableWithinAt.fun_sum fun z hz => ?_
    have hsz : s - z ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
    exact ((differentiableAt_const (c z : ℂ)).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - z) s) hsz).differentiableWithinAt
  have hHd : DifferentiableOn ℂ H U := hLd.add hGd
  set T : ℕ → ℝ → ℝ := fun k x => ((deriv^[k] H) x).re with hTdef
  have hsub : ∀ x : ℝ, a < x → (x : ℂ) ∈ U := fun x hx => by simpa [hUdef] using hx
  have hder : ∀ k x, a < x → HasDerivAt (T k) (T (k + 1) x) x := fun k x hx =>
    hasDerivAt_re_iterate_deriv hU hHd k (hsub x hx)
  have heven : ∀ j x, a < x → 0 ≤ T (2 * j) x := fun j x hx =>
    re_iterate_deriv_two_mul_nonneg hHd hpd j hx
  -- growth of the base of the tower
  have hsumm : LSeriesSummable f a :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using habs)
  set B : ℝ := ∑' n, ‖LSeries.term f a n‖
  set K : ℝ := B + ∑ z ∈ S, |c z|
  have hK : 0 ≤ K := add_nonneg (tsum_nonneg fun n => norm_nonneg _)
    (Finset.sum_nonneg fun z _ => abs_nonneg _)
  have hgrowth : ∀ x : ℝ, max (a + 1) 1 ≤ x → T 0 x ≤ K * Real.sqrt x := by
    intro x hx
    have hxa : a + 1 ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hL : ‖LSeries f x‖ ≤ B := by
      have hle : ∀ n, ‖LSeries.term f x n‖ ≤ ‖LSeries.term f a n‖ := fun n =>
        LSeries.norm_term_le_of_re_le_re f (by simp; linarith) n
      have hs : Summable fun n => ‖LSeries.term f x n‖ :=
        Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsumm.norm
      calc ‖LSeries f x‖ ≤ ∑' n, ‖LSeries.term f x n‖ := norm_tsum_le_tsum_norm hs
        _ ≤ B := Summable.tsum_le_tsum hle hs hsumm.norm
    have hG : ‖polarSum S c x‖ ≤ ∑ z ∈ S, |c z| := by
      calc ‖polarSum S c x‖ ≤ ∑ z ∈ S, ‖(c z : ℂ) / ((x : ℂ) - z)‖ := norm_sum_le S _
        _ ≤ ∑ z ∈ S, |c z| := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
          have hden : 1 ≤ ‖(x : ℂ) - z‖ := by
            calc (1 : ℝ) ≤ x - z.re := by linarith [hSa z hz]
              _ = ((x : ℂ) - z).re := by simp
              _ ≤ ‖(x : ℂ) - z‖ := Complex.re_le_norm _
          exact div_le_self (abs_nonneg _) hden
    have h1x : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
    calc T 0 x = (H x).re := by simp [hTdef]
      _ ≤ ‖H x‖ := Complex.re_le_norm _
      _ ≤ ‖LSeries f x‖ + ‖polarSum S c x‖ := norm_add_le _ _
      _ ≤ K := by simp only [K]; linarith
      _ ≤ K * Real.sqrt x := le_mul_of_one_le_right hK h1x
  have hodd := tower_odd_nonpos hder heven hgrowth
  have hcm : ∀ k x, a < x → 0 ≤ (-1 : ℝ) ^ k * T k x := by
    intro k x hx
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [pow_mul, neg_one_sq, one_pow, one_mul]
      exact heven j x hx
    · rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
      have := hodd j x hx
      linarith
  -- Post–Widder transform of the tower splits into lattice and polar parts
  have hsplit : ∀ k : ℕ, 1 ≤ k → a < (k : ℝ) / t →
      ((k : ℝ) / t) ^ (k + 1) / (k.factorial : ℝ) * ((-1 : ℝ) ^ k * T k ((k : ℝ) / t)) =
        (∑' n : ℕ, b n * postWidderKernel k t (Real.log n)) +
        ((k : ℝ) / t) ^ (k + 1) / (k.factorial : ℝ) *
          ((-1 : ℝ) ^ k * ((deriv^[k] (polarSum S c)) (((k : ℝ) / t : ℝ) : ℂ)).re) := by
    intro k hk hx
    have hadd := iterate_deriv_add_eqOn hU hLd hGd k (hsub _ hx)
    simp only [hTdef, hHdef] at hadd ⊢
    rw [hadd, Complex.add_re, mul_add, mul_add]
    congr 1
    rw [neg_one_pow_mul_re_iterate_deriv_LSeries k (habs' _ (by simpa using hx)),
      ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold postWidderKernel
    rcases eq_or_ne n 0 with rfl | hn
    · simp [zero_pow (Nat.one_le_iff_ne_zero.mp hk)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.rpow_def_of_pos hnpos]
      ring_nf
  have hPW : ∀ᶠ k : ℕ in atTop,
      0 ≤ (∑' n : ℕ, b n * postWidderKernel k t (Real.log n)) +
        ((k : ℝ) / t) ^ (k + 1) / (k.factorial : ℝ) *
          ((-1 : ℝ) ^ k * ((deriv^[k] (polarSum S c)) (((k : ℝ) / t : ℝ) : ℂ)).re) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (a * t) + 1)] with k hk
    have hk1 : 1 ≤ k := by omega
    have hx : a < (k : ℝ) / t := by
      rw [lt_div_iff₀ ht]
      have hceil : a * t ≤ (Nat.ceil (a * t) : ℝ) := Nat.le_ceil (a * t)
      have hk_cast : (Nat.ceil (a * t) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    rw [← hsplit k hk1 hx]
    exact mul_nonneg (div_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg k) ht.le) _)
      (Nat.cast_nonneg _)) (hcm k _ hx)
  have hσ : Summable fun n : ℕ => b n * (n : ℝ) ^ (-a) := by
    refine hsumm.norm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow_def]
      sorry
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hb n)]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_neg hnpos.le]
      simp [div_eq_mul_inv]
  have hlim := (tendsto_postWidder_lattice hb hσ ht hlat).add (tendsto_postWidder_polarSum hSa ht)
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim hPW

/-- **Lattice sieve.** If a nonnegative lattice series plus a finite polar sum has positive-definite
vertical sections on `σ > a`, then the polar scale weight `Σ c(z) e^{t Re z} cos(t Im z)` is
nonnegative at every scale `t > 0`: the absolutely continuous part of a positive scale measure is
positive on its own. -/
theorem polarScaleWeight_nonneg_of_lattice_posDef {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ} (hSa : ∀ z ∈ S, z.re ≤ a)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < a)
    (hpd : ∀ σ : ℝ, a < σ → IsPosDef fun u : ℝ =>
      (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    {t : ℝ} (ht : 0 < t) : 0 ≤ polarScaleWeight S c t := by
  have hD : Dense (Set.range fun n : ℕ => Real.log n)ᶜ :=
    (Set.countable_range _).dense_compl ℝ
  have hex : ∀ j : ℕ, ∃ s ∈ (Set.range fun n : ℕ => Real.log n)ᶜ,
      s ∈ Ioo t (t + 1 / ((j : ℝ) + 1)) := fun j =>
    hD.exists_between (by have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity; linarith)
  choose s hsD hsI using hex
  have hs_lim : Tendsto s atTop (𝓝 t) := by
    have hup : Tendsto (fun j : ℕ => t + 1 / ((j : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun j => (hsI j).1.le) (fun j => (hsI j).2.le)
  have hcont : Continuous (polarScaleWeight S c) := by
    unfold polarScaleWeight; fun_prop
  refine ge_of_tendsto ((hcont.tendsto t).comp hs_lim) (Eventually.of_forall fun j => ?_)
  exact polarScaleWeight_nonneg_of_lattice_posDef_of_ne_log hb hSa habs hpd
    (by linarith [(hsI j).1]) fun n h => hsD j ⟨n, h⟩

end GaloisForLFunctions.BiarithmeticGaugeGeometry
