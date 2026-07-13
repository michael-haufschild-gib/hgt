/-
# The Fredholm determinant on explicit operators — the weld firing

This file evaluates the regularized Fredholm determinant `det₂(1 − zK)` on concrete Hilbert–Schmidt
kernels, exhibiting the determinant–L-function weld (`fredholmDet_weld`) on an operator one can write
down.  The **rank-one diagonal kernel** `d·e_{i₀i₀}` gives

  `det₂(1 − z·(d·e_{i₀i₀})) = (1 − zd)·exp(zd)`,

whose leading factor `1 − zd` is the local `L`-factor shape `1 − p^{−s}` (with `zd ↔ p^{−s}`) — the
inverse Euler factor — and whose `exp(zd)` is the Hilbert–Carleman regularization that makes the
determinant converge for a non-trace-class operator.  The determinant vanishes exactly at `z = 1/d`,
the reciprocal of the operator's single eigenvalue: **the zero of the determinant is the reciprocal
eigenvalue**, the finite model of "the zeros of `Λ` are the reciprocal eigenvalues of the seam
generator `Θ`".

Main results:
* `fredholmDet_zero` — `det₂(1 − 0·K) = 1` for every `K` (the determinant is `1` at the origin).
* `diagKernel`, `hsPow_diagKernel`, `resolventTrace_diagKernel` — the rank-one diagonal operator, its
  powers `d^(n+1)·e_{i₀i₀}`, and its resolvent trace `z·d²/(1 − zd)`.
* `fredholmDet_diagKernel` — `det₂(1 − z·(d·e_{i₀i₀})) = (1 − zd)·exp(zd)`: the weld firing on an
  explicit operator, with the local inverse-Euler-factor `(1 − zd)` inside the determinant.
* `fredholmDet_eulerFactor` — `det₂(1 − p^{−s}·e_{i₀i₀})|_{z=1} = (1 − p^{−s})·exp(p^{−s})`: the codebase
  local Euler factor `1 − p^{−s}` realized as a regularized determinant.
* `diagMul`, `resolventTrace_diagMul`, `fredholmDet_diagMul` — the finite diagonal operator and the
  **finite Euler product** `det₂(1 − z·diagMul g) = ∏_{i∈S} (1 − z·g i)·exp(z·g i)` (with `g i = pᵢ^{−s}`
  the `z`-deformed inverse Euler product `∏(1 − z·pᵢ^{−s})`, whose `z = 1` value is the codebase
  `RHTower.eulerHeadAnchor`), times the Hilbert–Carleman correction `exp(z·∑ g i)`.
-/
import GaloisForLFunctions.HTGeometry.FredholmDeterminant

open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*}

/-- The determinant exponent vanishes at the origin: every term carries `0^(n+2)`. -/
theorem fredholmExp_zero (K : ι × ι → ℂ) : fredholmExp K 0 = 0 := by rw [fredholmExp]; simp

/-- The regularized determinant is `1` at the origin: `det₂(1 − 0·K) = 1`. -/
theorem fredholmDet_zero (K : ι × ι → ℂ) : fredholmDet K 0 = 1 := by
  rw [fredholmDet, fredholmExp_zero, neg_zero, Complex.exp_zero]

/-- The logarithmic derivative of the rank-one candidate `L(w) = (1 − wd)·exp(wd)` is
`−wd²/(1 − wd)` — matching the negative resolvent trace of the rank-one diagonal operator. -/
theorem logDeriv_diagL (d w : ℂ) :
    logDeriv (fun w => (1 - w * d) * Complex.exp (w * d)) w = - (w * d ^ 2 / (1 - w * d)) := by
  have hd1 : HasDerivAt (fun w : ℂ => 1 - w * d) (-d) w := by
    have h := (hasDerivAt_id w).mul_const d; simpa using h.const_sub 1
  have hd2 : HasDerivAt (fun w : ℂ => Complex.exp (w * d)) (Complex.exp (w * d) * d) w := by
    have h := (hasDerivAt_id w).mul_const d; simpa using h.cexp
  have hdL : HasDerivAt (fun w : ℂ => (1 - w * d) * Complex.exp (w * d))
      (-d * Complex.exp (w * d) + (1 - w * d) * (Complex.exp (w * d) * d)) w := hd1.mul hd2
  rw [logDeriv_apply, hdL.deriv]
  have hexp : Complex.exp (w * d) ≠ 0 := Complex.exp_ne_zero _
  field_simp; ring

variable [DecidableEq ι]

/-- The **rank-one diagonal kernel** `d·e_{i₀i₀}`: value `d` at `(i₀,i₀)`, zero elsewhere. -/
noncomputable def diagKernel (i₀ : ι) (d : ℂ) : ι × ι → ℂ := fun p => if p = (i₀, i₀) then d else 0

/-- The rank-one diagonal kernel is Hilbert–Schmidt (finite support). -/
theorem isHS_diagKernel (i₀ : ι) (d : ℂ) : IsHS (diagKernel i₀ d) := by
  apply isHS_of_support_subset {(i₀, i₀)}
  intro p hp; simp only [diagKernel]; rw [if_neg]; intro h; exact hp (by simp [h])

/-- Diagonal kernels compose multiplicatively: `(d·e_{i₀i₀}) ∘ (e·e_{i₀i₀}) = (de)·e_{i₀i₀}`. -/
theorem hsComp_diagKernel (i₀ : ι) (d e : ℂ) :
    hsComp (diagKernel i₀ d) (diagKernel i₀ e) = diagKernel i₀ (d * e) := by
  funext p
  rw [hsComp, tsum_eq_single i₀ (by
    intro k hk; simp only [diagKernel]
    rw [if_neg (show (k, p.2) ≠ (i₀, i₀) from fun h => hk (Prod.ext_iff.mp h).1), mul_zero])]
  simp only [diagKernel, Prod.ext_iff]
  by_cases h1 : p.1 = i₀ <;> by_cases h2 : p.2 = i₀ <;> simp [h1, h2]

/-- The powers of the rank-one diagonal kernel: `(d·e_{i₀i₀})^(n+1) = d^(n+1)·e_{i₀i₀}`. -/
theorem hsPow_diagKernel (i₀ : ι) (d : ℂ) :
    ∀ n, hsPow (diagKernel i₀ d) n = diagKernel i₀ (d ^ (n + 1))
  | 0 => by simp [hsPow]
  | (n + 1) => by rw [hsPow, hsPow_diagKernel i₀ d n, hsComp_diagKernel]; congr 1; ring

/-- The trace of a diagonal kernel is its single entry: `∑ᵢ (c·e_{i₀i₀})(i,i) = c`. -/
theorem tsum_diagKernel_diag (i₀ : ι) (c : ℂ) : ∑' i, diagKernel i₀ c (i, i) = c := by
  rw [tsum_eq_single i₀ (by
    intro i hi; simp only [diagKernel]
    rw [if_neg (show (i, i) ≠ (i₀, i₀) from fun h => hi (Prod.ext_iff.mp h).1)])]
  simp [diagKernel]

/-- The Hilbert–Schmidt norm squared of the rank-one diagonal kernel is `‖d‖²`. -/
theorem hsNormSq_diagKernel (i₀ : ι) (d : ℂ) : hsNormSq (diagKernel i₀ d) = ‖d‖ ^ 2 := by
  rw [hsNormSq, tsum_eq_single (i₀, i₀) (by intro p hp; simp only [diagKernel]; rw [if_neg hp]; simp)]
  simp [diagKernel]

/-- The Hilbert–Schmidt norm of the rank-one diagonal kernel is `‖d‖`. -/
theorem hsNorm_diagKernel (i₀ : ι) (d : ℂ) : hsNorm (diagKernel i₀ d) = ‖d‖ := by
  rw [hsNorm, hsNormSq_diagKernel, Real.sqrt_sq (norm_nonneg d)]

/-- **The resolvent trace of the rank-one diagonal operator:** `z·d²/(1 − zd)` on `|zd| < 1` — a plain
geometric series `∑ₙ z^(n+1)·d^(n+2)`. -/
theorem resolventTrace_diagKernel (i₀ : ι) (d z : ℂ) (hzd : ‖z * d‖ < 1) :
    resolventTrace (diagKernel i₀ d) z = z * d ^ 2 / (1 - z * d) := by
  rw [resolventTrace]
  have hterm : ∀ n : ℕ, z ^ (n + 1) * (∑' i, hsPow (diagKernel i₀ d) (n + 1) (i, i))
      = z * d ^ 2 * (z * d) ^ n := by
    intro n; rw [hsPow_diagKernel, tsum_diagKernel_diag, mul_pow]; ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hzd, div_eq_mul_inv]

/-- **The regularized determinant of a rank-one diagonal Hilbert–Schmidt operator.**
`det₂(1 − z·(d·e_{i₀i₀})) = (1 − zd)·exp(zd)` on the disk `|z|·‖d‖ < 1`.  The factor `(1 − zd)` is the
rank-one Fredholm determinant — the local inverse `L`-factor shape `1 − p^{−s}` (with `zd ↔ p^{−s}`) —
and `exp(zd)` is the Hilbert–Carleman regularization.  The determinant vanishes exactly at `z = 1/d`,
the reciprocal of the single eigenvalue: the weld firing on an explicit operator, with the local
`L`-factor exhibited inside the determinant. -/
theorem fredholmDet_diagKernel (i₀ : ι) (d : ℂ) (r : ℝ) (hr : r * ‖d‖ < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet (diagKernel i₀ d) z = (1 - z * d) * Complex.exp (z * d) := by
  have hK : IsHS (diagKernel i₀ d) := isHS_diagKernel i₀ d
  have hrK : r * hsNorm (diagKernel i₀ d) < 1 := by rw [hsNorm_diagKernel]; exact hr
  have hwd_lt : ∀ w ∈ Metric.ball (0 : ℂ) r, ‖w * d‖ < 1 := by
    intro w hw
    rw [mem_ball_zero_iff] at hw; rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hw.le (norm_nonneg d)) hr
  have hLne : ∀ w ∈ Metric.ball (0 : ℂ) r,
      (fun w => (1 - w * d) * Complex.exp (w * d)) w ≠ 0 := by
    intro w hw
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    rw [sub_ne_zero]; intro h
    have hlt := hwd_lt w hw; rw [← h, norm_one] at hlt; exact lt_irrefl 1 hlt
  have hLdiff : DifferentiableOn ℂ (fun w => (1 - w * d) * Complex.exp (w * d)) (Metric.ball 0 r) :=
    (((differentiable_const 1).sub (differentiable_id.mul_const d)).mul
      (Complex.differentiable_exp.comp (differentiable_id.mul_const d))).differentiableOn
  have hmatch : ∀ w ∈ Metric.ball (0 : ℂ) r,
      logDeriv (fun w => (1 - w * d) * Complex.exp (w * d)) w
        = - resolventTrace (diagKernel i₀ d) w := by
    intro w hw
    rw [logDeriv_diagL, resolventTrace_diagKernel i₀ d w (hwd_lt w hw)]
  obtain ⟨c, hc⟩ := fredholmDet_weld hK r hrK _ hLdiff hLne hmatch
  have hr0 : 0 < r := by rw [mem_ball_zero_iff] at hz; exact lt_of_le_of_lt (norm_nonneg z) hz
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by rw [mem_ball_zero_iff, norm_zero]; exact hr0
  have hc0 := hc 0 h0
  rw [fredholmDet_zero] at hc0
  simp only [zero_mul, sub_zero, Complex.exp_zero, mul_one] at hc0
  rw [hc z hz, ← hc0, one_mul]

/-- **The local inverse Euler factor is a regularized Fredholm determinant.**  For a prime `p ≥ 2` and
`Re s > 0`, the regularized determinant of the rank-one operator `p^{−s}·e_{i₀i₀}` at `z = 1` is

  `det₂(1 − p^{−s}·e_{i₀i₀}) = (1 − p^{−s})·exp(p^{−s})`,

whose leading factor `1 − p^{−s}` is exactly the local Euler factor of `RHTower.eulerHeadAnchor` /
`logDeriv_eulerFactor` (the inverse of the local `ζ`-factor `(1 − p^{−s})⁻¹`).  So each Euler factor of
the completed `L`-function is realized as (the leading factor of) the regularized Fredholm determinant of
an explicit finite-rank operator on `ℓ²`, with the `exp(p^{−s})` the Hilbert–Carleman correction.  This
is the local case of the seam weld: the determinant carries the Euler factor, and its zero at
`z = p^{s}` (i.e. `p^{−s} = 1`, on `Re s = 0`) is the boundary of the factor's nonvanishing region. -/
theorem fredholmDet_eulerFactor (i₀ : ι) {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    fredholmDet (diagKernel i₀ ((p : ℂ) ^ (-s))) 1
      = (1 - (p : ℂ) ^ (-s)) * Complex.exp ((p : ℂ) ^ (-s)) := by
  have hpr : (0 : ℝ) < (p : ℝ) := by positivity
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpr, Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hpr _
  set d : ℂ := (p : ℂ) ^ (-s) with hd_def
  have hd_lt : ‖d‖ < 1 := by rw [hd_def, hnorm]; exact hlt
  have hd0 : (0 : ℝ) < ‖d‖ := by rw [hd_def, hnorm]; exact hpos
  set r : ℝ := (1 + 1 / ‖d‖) / 2 with hr_def
  have hinv : (1 : ℝ) < 1 / ‖d‖ := by rw [lt_div_iff₀ hd0, one_mul]; exact hd_lt
  have hr1 : (1 : ℝ) < r := by rw [hr_def]; linarith
  have hrd : r * ‖d‖ < 1 := by
    have hval : r * ‖d‖ = (‖d‖ + 1) / 2 := by
      rw [hr_def, div_mul_eq_mul_div, add_mul, one_mul, div_mul_cancel₀ _ hd0.ne']
    rw [hval]; linarith
  have hz : (1 : ℂ) ∈ Metric.ball (0 : ℂ) r := by rw [mem_ball_zero_iff, norm_one]; exact hr1
  have hmain := fredholmDet_diagKernel i₀ d r hrd 1 hz
  simpa using hmain

/-! ### The finite Euler product as a regularized determinant

A finite-rank diagonal operator with entries `g i` on `i ∈ S` gives, by orthogonality of the diagonal
entries, a determinant that *factors* over `S`: `det₂ = ∏_{i∈S} (1 − z·g i)·exp(z·g i)`.  With
`g i = pᵢ^{−s}` this is `∏(1 − pᵢ^{−s})·exp(∑ pᵢ^{−s})` — the inverse of the finite Euler product (the
`eulerHeadAnchor`) times the Hilbert–Carleman correction. -/

/-- The **general diagonal kernel** of a function `g`: value `g i` at `(i,i)`, zero off the diagonal. -/
noncomputable def diagMul (g : ι → ℂ) : ι × ι → ℂ := fun p => if p.1 = p.2 then g p.1 else 0

/-- A diagonal kernel with entries supported on a finite set `S` is Hilbert–Schmidt. -/
theorem isHS_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0) : IsHS (diagMul g) := by
  apply isHS_of_support_subset (S.image (fun i => (i, i)))
  intro p hp
  simp only [diagMul]
  by_cases h : p.1 = p.2
  · rw [if_pos h]
    by_contra hne
    exact hp (Finset.mem_image.mpr ⟨p.1, by
      by_contra hiS; exact hne (hg p.1 hiS), Prod.ext_iff.mpr ⟨rfl, h⟩⟩)
  · rw [if_neg h]

/-- Diagonal kernels compose by pointwise multiplication: `diagMul g ∘ diagMul h = diagMul (g·h)`. -/
theorem hsComp_diagMul (g h : ι → ℂ) :
    hsComp (diagMul g) (diagMul h) = diagMul (fun i => g i * h i) := by
  funext p
  rw [hsComp, tsum_eq_single p.1 (by
    intro k hk; simp only [diagMul]
    rw [if_neg (show ¬ p.1 = k from fun h => hk h.symm), zero_mul])]
  by_cases h2 : p.1 = p.2 <;> simp [diagMul, h2]

/-- The powers of a diagonal kernel are pointwise powers: `(diagMul g)^(n+1) = diagMul (g^(n+1))`. -/
theorem hsPow_diagMul (g : ι → ℂ) :
    ∀ n, hsPow (diagMul g) n = diagMul (fun i => g i ^ (n + 1))
  | 0 => by simp [hsPow]
  | (n + 1) => by
      rw [hsPow, hsPow_diagMul g n, hsComp_diagMul]
      funext p; simp only [diagMul]
      by_cases h : p.1 = p.2
      · simp only [h, if_true]; ring
      · simp [h]

/-- The trace of a finitely-supported diagonal kernel is the finite sum of its entries. -/
theorem tsum_diagMul_diag (c : ι → ℂ) (S : Finset ι) (hc : ∀ i ∉ S, c i = 0) :
    ∑' i, diagMul c (i, i) = ∑ i ∈ S, c i := by
  rw [tsum_eq_sum (s := S) (by intro i hi; simp only [diagMul]; simp [hc i hi])]
  apply Finset.sum_congr rfl; intro i _; simp [diagMul]

/-- The Hilbert–Schmidt norm squared of a finitely-supported diagonal kernel is `∑_{i∈S} ‖g i‖²`. -/
theorem hsNormSq_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0) :
    hsNormSq (diagMul g) = ∑ i ∈ S, ‖g i‖ ^ 2 := by
  rw [hsNormSq, tsum_eq_sum (s := S.image (fun i => (i, i))) (by
    intro p hp
    simp only [diagMul]
    by_cases h : p.1 = p.2
    · rw [if_pos h]
      have hgp : g p.1 = 0 := by
        by_contra hne
        exact hp (Finset.mem_image.mpr ⟨p.1, by by_contra hiS; exact hne (hg p.1 hiS),
          Prod.ext_iff.mpr ⟨rfl, h⟩⟩)
      rw [hgp]; simp
    · rw [if_neg h]; simp)]
  rw [Finset.sum_image (by intro a _ b _ h; exact (Prod.ext_iff.mp h).1)]
  apply Finset.sum_congr rfl; intro i _; simp [diagMul]

/-- Each entry is bounded by the Hilbert–Schmidt norm: `‖g i‖ ≤ ‖diagMul g‖_HS` for `i ∈ S`. -/
theorem norm_le_hsNorm_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0)
    {i : ι} (hi : i ∈ S) : ‖g i‖ ≤ hsNorm (diagMul g) := by
  rw [hsNorm, hsNormSq_diagMul g S hg,
    show ‖g i‖ = Real.sqrt (‖g i‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ‖g j‖ ^ 2) (fun j _ => sq_nonneg _) hi)

/-- A geometric resolvent term is summable when `‖wd‖ < 1`. -/
theorem summable_geom_resolvent (w d : ℂ) (h : ‖w * d‖ < 1) :
    Summable (fun n : ℕ => w ^ (n + 1) * d ^ (n + 2)) := by
  have hcong : (fun n : ℕ => w ^ (n + 1) * d ^ (n + 2)) = fun n => w * d ^ 2 * (w * d) ^ n := by
    funext n; rw [mul_pow]; ring
  rw [hcong]; exact (summable_geometric_of_norm_lt_one h).mul_left _

/-- The geometric resolvent sum: `∑ₙ w^(n+1)·d^(n+2) = wd²/(1 − wd)` for `‖wd‖ < 1`. -/
theorem tsum_geom_resolvent (w d : ℂ) (h : ‖w * d‖ < 1) :
    ∑' n : ℕ, w ^ (n + 1) * d ^ (n + 2) = w * d ^ 2 / (1 - w * d) := by
  have hcong : (fun n : ℕ => w ^ (n + 1) * d ^ (n + 2)) = fun n => w * d ^ 2 * (w * d) ^ n := by
    funext n; rw [mul_pow]; ring
  rw [hcong, tsum_mul_left, tsum_geometric_of_norm_lt_one h, div_eq_mul_inv]

/-- **The resolvent trace of a finite diagonal operator is the sum of the rank-one resolvent traces:**
`∑_{i∈S} z·g(i)²/(1 − z·g(i))` (the traces of orthogonal diagonal entries add). -/
theorem resolventTrace_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0) (z : ℂ)
    (hgz : ∀ i ∈ S, ‖z * g i‖ < 1) :
    resolventTrace (diagMul g) z = ∑ i ∈ S, z * g i ^ 2 / (1 - z * g i) := by
  rw [resolventTrace]
  have hterm : ∀ n : ℕ, z ^ (n + 1) * (∑' i, hsPow (diagMul g) (n + 1) (i, i))
      = ∑ i ∈ S, z ^ (n + 1) * g i ^ (n + 2) := by
    intro n
    rw [hsPow_diagMul, tsum_diagMul_diag (fun i => g i ^ (n + 1 + 1)) S
      (by intro i hi; simp [hg i hi]), Finset.mul_sum]
  rw [tsum_congr hterm,
    Summable.tsum_finsetSum (fun i hi => summable_geom_resolvent z (g i) (hgz i hi))]
  apply Finset.sum_congr rfl; intro i hi
  exact tsum_geom_resolvent z (g i) (hgz i hi)

/-- **The finite Euler product as a regularized Fredholm determinant.**
`det₂(1 − z·diagMul g) = ∏_{i∈S} (1 − z·g i)·exp(z·g i)` on the disk `|z|·‖diagMul g‖_HS < 1`.  The
determinant of a finite-rank diagonal operator factors over its entries — each factor `(1 − z·g i)` is a
local inverse `L`-factor.  With `g i = pᵢ^{−s}` and `z = 1` this is `∏(1 − pᵢ^{−s})·exp(∑ pᵢ^{−s})`: the
inverse of the finite Euler product (`RHTower.eulerHeadAnchor`) times the Hilbert–Carleman correction —
the finite-product case of the seam weld. -/
theorem fredholmDet_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0) (r : ℝ)
    (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet (diagMul g) z = ∏ i ∈ S, (1 - z * g i) * Complex.exp (z * g i) := by
  have hK : IsHS (diagMul g) := isHS_diagMul g S hg
  have hfac : ∀ w ∈ Metric.ball (0 : ℂ) r, ∀ i ∈ S, ‖w * g i‖ < 1 := by
    intro w hw i hi
    rw [mem_ball_zero_iff] at hw
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul hw.le (norm_le_hsNorm_diagMul g S hg hi) (norm_nonneg _)
      ((norm_nonneg w).trans hw.le)) hr
  set L : ℂ → ℂ := fun w => ∏ i ∈ S, (1 - w * g i) * Complex.exp (w * g i) with hLdef
  have hLne : ∀ w ∈ Metric.ball (0 : ℂ) r, L w ≠ 0 := by
    intro w hw
    rw [hLdef]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero]; intro h
    have hlt := hfac w hw i hi; rw [← h, norm_one] at hlt; exact lt_irrefl 1 hlt
  have hLdiff : DifferentiableOn ℂ L (Metric.ball 0 r) := by
    apply Differentiable.differentiableOn
    rw [hLdef, show (fun w : ℂ => ∏ i ∈ S, (1 - w * g i) * Complex.exp (w * g i))
        = ∏ i ∈ S, (fun w : ℂ => (1 - w * g i) * Complex.exp (w * g i)) from by
      funext w; rw [Finset.prod_apply]]
    refine Differentiable.finsetProd fun i _ => ?_
    exact ((differentiable_const 1).sub (differentiable_id.mul_const (g i))).mul
      (Complex.differentiable_exp.comp (differentiable_id.mul_const (g i)))
  have hmatch : ∀ w ∈ Metric.ball (0 : ℂ) r, logDeriv L w = - resolventTrace (diagMul g) w := by
    intro w hw
    rw [hLdef, resolventTrace_diagMul g S hg w (fun i hi => hfac w hw i hi),
      logDeriv_prod (f := fun i => fun w : ℂ => (1 - w * g i) * Complex.exp (w * g i))
        (fun i hi => by
          refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
          rw [sub_ne_zero]; intro h
          have hlt := hfac w hw i hi; rw [← h, norm_one] at hlt; exact lt_irrefl 1 hlt)
        (fun i _ => ((differentiable_const 1).sub (differentiable_id.mul_const (g i))).mul
          (Complex.differentiable_exp.comp (differentiable_id.mul_const (g i))) w),
      show (∑ i ∈ S, logDeriv (fun w => (1 - w * g i) * Complex.exp (w * g i)) w)
          = ∑ i ∈ S, -(w * g i ^ 2 / (1 - w * g i)) from
        Finset.sum_congr rfl (fun i _ => logDeriv_diagL (g i) w),
      Finset.sum_neg_distrib]
  obtain ⟨c, hc⟩ := fredholmDet_weld hK r hr L hLdiff hLne hmatch
  have hr0 : 0 < r := by rw [mem_ball_zero_iff] at hz; exact lt_of_le_of_lt (norm_nonneg z) hz
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by rw [mem_ball_zero_iff, norm_zero]; exact hr0
  have hc0 := hc 0 h0
  rw [fredholmDet_zero] at hc0
  have hL0 : L 0 = 1 := by rw [hLdef]; simp
  rw [hL0, mul_one] at hc0
  rw [hc z hz, ← hc0, one_mul, hLdef]

/-! ### The trace-class determinant `det₁` and the bare Euler product

For a finite-rank (trace-class) operator the ordinary Fredholm determinant `det₁(1 − zK)` exists — it is
the regularized `det₂` corrected by the trace term, `det₁ = det₂·exp(−z·tr K)`.  On the finite diagonal
operator the Hilbert–Carleman corrections cancel exactly, leaving the bare characteristic product
`∏_{i∈S} (1 − z·g i)` — the inverse Euler product with no `exp` factor. -/

/-- The **diagonal trace** `tr K = ∑ᵢ K(i,i)` (converges for trace-class `K`). -/
noncomputable def hsTraceDiag (K : ι × ι → ℂ) : ℂ := ∑' i, K (i, i)

/-- The **trace-class Fredholm determinant** `det₁(1 − zK) = det₂(1 − zK)·exp(−z·tr K)` — the ordinary
Fredholm determinant, defined for trace-class `K` by correcting the regularized `det₂` with the trace. -/
noncomputable def fredholmDet1 (K : ι × ι → ℂ) (z : ℂ) : ℂ :=
  fredholmDet K z * Complex.exp (-(z * hsTraceDiag K))

/-- **The trace-class Fredholm determinant of a finite diagonal operator is the characteristic product**
`det₁(1 − z·diagMul g) = ∏_{i∈S} (1 − z·g i)` — the Hilbert–Carleman `exp` corrections cancel against the
trace term, leaving the bare inverse Euler product.  With `g i = pᵢ^{−s}` and `z = 1` this is
`∏(1 − pᵢ^{−s}) = RHTower.eulerHeadAnchor P s` exactly. -/
theorem fredholmDet1_diagMul (g : ι → ℂ) (S : Finset ι) (hg : ∀ i ∉ S, g i = 0) (r : ℝ)
    (hr : r * hsNorm (diagMul g) < 1) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet1 (diagMul g) z = ∏ i ∈ S, (1 - z * g i) := by
  rw [fredholmDet1, fredholmDet_diagMul g S hg r hr z hz]
  have htr : hsTraceDiag (diagMul g) = ∑ i ∈ S, g i := tsum_diagMul_diag g S hg
  rw [htr, Finset.prod_mul_distrib, ← Complex.exp_sum, mul_assoc, ← Complex.exp_add,
    show (∑ i ∈ S, z * g i) + -(z * ∑ i ∈ S, g i) = 0 from by rw [Finset.mul_sum]; ring,
    Complex.exp_zero, mul_one]

omit [DecidableEq ι] in
/-- **The Plemelj identity for the trace-class determinant `det₁`:** `logDeriv det₁(1 − zK)` equals the
*full* (unregularized) resolvent trace `−(tr K + resolventTrace K z) = −tr(K(1 − zK)⁻¹)`.  This is the
exact classical shape `logDeriv Λ = tr((s − Θ)⁻¹)` — the regularized `det₂` version
(`logDeriv_fredholmDet`, `= −resolventTrace`) plus the trace term `tr K` restored by the `exp(−z·tr K)`
correction. -/
theorem logDeriv_fredholmDet1 {K : ι × ι → ℂ} (hK : IsHS K) (r : ℝ) (hr : r * hsNorm K < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    logDeriv (fun w => fredholmDet1 K w) z = -(hsTraceDiag K + resolventTrace K z) := by
  have hf : HasDerivAt (fun w => fredholmDet K w) (fredholmDet K z * (- resolventTrace K z)) z :=
    hasDerivAt_fredholmDet hK r hr z hz
  have hh : HasDerivAt (fun w : ℂ => -(w * hsTraceDiag K)) (-hsTraceDiag K) z := by
    have h := (hasDerivAt_id z).mul_const (hsTraceDiag K); simpa using h.neg
  have hexp : HasDerivAt (fun w => Complex.exp (-(w * hsTraceDiag K)))
      (Complex.exp (-(z * hsTraceDiag K)) * (-hsTraceDiag K)) z := hh.cexp
  have hprod : HasDerivAt (fun w => fredholmDet1 K w)
      (fredholmDet K z * (- resolventTrace K z) * Complex.exp (-(z * hsTraceDiag K))
        + fredholmDet K z * (Complex.exp (-(z * hsTraceDiag K)) * (-hsTraceDiag K))) z := hf.mul hexp
  rw [logDeriv_apply, hprod.deriv, fredholmDet1]
  have h1 : fredholmDet K z ≠ 0 := fredholmDet_ne_zero K z
  have h2 : Complex.exp (-(z * hsTraceDiag K)) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

end HilbertSchmidt
