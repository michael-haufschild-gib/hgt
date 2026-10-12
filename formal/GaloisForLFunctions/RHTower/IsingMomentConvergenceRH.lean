import GaloisForLFunctions.RHTower.IsingLawConvergenceRH

/-!
# Convergence of moments of ferromagnetic Ising magnetizations to Riemann's moments forces RH

Let `X_n = Σ_k c_{n,k} σ_k` be zero-field ferromagnetic Ising magnetizations (`J ≥ 0`, `c ≥ 0`) and
let `m_k = ∫ u^k Φ(u) du / Ξ(0) = (−i)^k (Ξ/Ξ(0))^{(k)}(0)` be the moments of Riemann's distribution.

**Theorem** (`riemannHypothesis_of_isingMoment_tendsto`). If `E[X_n^k] → m_k` for every `k`, RH
holds.

**Proof.** The Taylor coefficients of `φ_n(z) = E[e^{izX_n}]` at `0` are `i^k E[X_n^k]`
(`iteratedDeriv_isingCharFn`). Convergence of the first three gives `L(φ_n) → L(Ξ/Ξ(0))`, hence the
Lee–Yang Gaussian bound `|φ_n(z)|² ≤ exp(|z|² L(φ_n))` is uniform. By Montel every subsequence has a
sub-subsequence converging locally uniformly to an entire `g`, whose Taylor coefficients at `0` are
those of `Ξ/Ξ(0)`. The Taylor series of entire functions converge everywhere, so `g = Ξ/Ξ(0)`, and
the whole sequence converges locally uniformly on `ℂ`. All zeros of `φ_n` are real, so by Hurwitz
all zeros of `Ξ` are real.

This is the method of moments for Griffiths–Simon producers: it suffices that the moment sequence of
`Φ` lie in the closure of the moment sequences of ferromagnetic Ising magnetizations.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace RHTower.GriffithsSimon

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.LeeYang

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `k`-th moment `E[X^k]` of the Ising magnetization `X = Σ_j c_j σ_j`. -/
def isingMoment (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (k : ℕ) : ℝ :=
  ∑ D : Finset V, isingWeight J E D / Zpart J E * (∑ j, c j * spin D j) ^ k

/-- The `k`-th moment of Riemann's distribution, `(−i)^k (Ξ/Ξ(0))^{(k)}(0)`. -/
def riemannMoment (k : ℕ) : ℂ := (-I) ^ k * iteratedDeriv k (fun z => XiC z / XiC 0) 0

/-- Derivatives of the characteristic function: `φ^{(k)}(z) = Σ_D (W/Z)(iX_D)^k e^{izX_D}`. -/
theorem iteratedDeriv_isingCharFn (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (k : ℕ) :
    iteratedDeriv k (isingCharFn J E c) = fun z => ∑ D : Finset V,
      ((((isingWeight J E D / Zpart J E : ℝ)) : ℂ) * (I * ((∑ j, c j * spin D j : ℝ) : ℂ)) ^ k) *
        Complex.exp ((I * ((∑ j, c j * spin D j : ℝ) : ℂ)) * z) := by
  induction k with
  | zero =>
    funext z
    rw [iteratedDeriv_zero, isingCharFn, Finset.sum_div]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [pow_zero, mul_one, Complex.ofReal_div, mul_comm I _, mul_assoc, mul_comm z]
    ring
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    refine HasDerivAt.deriv ?_
    refine HasDerivAt.fun_sum fun D _ => ?_
    set a : ℂ := I * ((∑ j, c j * spin D j : ℝ) : ℂ)
    set w : ℂ := (((isingWeight J E D / Zpart J E : ℝ)) : ℂ)
    have h := (((hasDerivAt_id z).const_mul a).cexp).const_mul (w * a ^ k)
    simp only [id, mul_one] at h
    exact h.congr_deriv (by ring)

/-- The Taylor coefficients at `0` are the moments: `φ^{(k)}(0) = i^k E[X^k]`. -/
theorem iteratedDeriv_isingCharFn_zero (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ)
    (k : ℕ) : iteratedDeriv k (isingCharFn J E c) 0 = I ^ k * (isingMoment J E c k : ℂ) := by
  rw [iteratedDeriv_isingCharFn, isingMoment]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [mul_zero, Complex.exp_zero, mul_one, mul_pow]
  ring

/-- **Normal family from convergent Taylor coefficients.** If the first three Taylor coefficients
converge to those of `Ξ/Ξ(0)`, then `L(φ_n)` is eventually bounded. -/
theorem exists_eventually_lagRatio_le_of_iteratedDeriv
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n)) (c : ∀ n, ι n → ℝ)
    (hmom : ∀ k : ℕ, Tendsto (fun n => iteratedDeriv k (isingCharFn (J n) (E n) (c n)) 0) atTop
      (𝓝 (iteratedDeriv k (fun z => XiC z / XiC 0) 0))) :
    ∃ n₀ : ℕ, ∃ K : ℝ, ∀ n, n₀ ≤ n → (lagRatio (isingCharFn (J n) (E n) (c n))).re ≤ K := by
  set F : ℂ → ℂ := fun z => XiC z / XiC 0 with hF
  have hF0 : F 0 ≠ 0 := div_ne_zero XiC_zero_ne XiC_zero_ne
  have h0 := hmom 0
  have h1 := hmom 1
  have h2 := hmom 2
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at h0 h1
  rw [show (2 : ℕ) = 1 + 1 from rfl] at h2
  simp only [iteratedDeriv_succ] at h2
  have hlag : Tendsto (fun n => lagRatio (isingCharFn (J n) (E n) (c n))) atTop
      (𝓝 (lagRatio F)) := by
    unfold lagRatio
    exact ((h1.pow 2).sub (h0.mul h2)).div (h0.pow 2) (pow_ne_zero 2 hF0)
  have hre := (Complex.continuous_re.tendsto _).comp hlag
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (hre.eventually (gt_mem_nhds (lt_add_one (lagRatio F).re)))
  exact ⟨n₀, (lagRatio F).re + 1, fun n hn => (hn₀ n hn).le⟩

/-- **Moments upgrade to locally uniform convergence on `ℂ`.** For zero-field ferromagnetic Ising
magnetizations (`J ≥ 0`, `c ≥ 0`), convergence of every Taylor coefficient of the characteristic
functions at `0` to that of `Ξ/Ξ(0)` implies locally uniform convergence on `ℂ`. -/
theorem tendstoLocallyUniformly_of_tendsto_iteratedDeriv
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hmom : ∀ k : ℕ, Tendsto (fun n => iteratedDeriv k (isingCharFn (J n) (E n) (c n)) 0) atTop
      (𝓝 (iteratedDeriv k (fun z => XiC z / XiC 0) 0))) :
    TendstoLocallyUniformly (fun n => isingCharFn (J n) (E n) (c n)) (fun z => XiC z / XiC 0)
      atTop := by
  set F : ℂ → ℂ := fun z => XiC z / XiC 0 with hF
  have hFdiff : Differentiable ℂ F := fun z =>
    ((XiC_analytic z (mem_univ z)).div_const).differentiableAt
  obtain ⟨n₀, K, hL⟩ := exists_eventually_lagRatio_le_of_iteratedDeriv J E c hmom
  let x : ℕ → C(ℂ, ℂ) := fun n =>
    ⟨isingCharFn (J n) (E n) (c n), (differentiable_isingCharFn _ _ _).continuous⟩
  let f : C(ℂ, ℂ) := ⟨F, hFdiff.continuous⟩
  have h : Tendsto x atTop (𝓝 f) := by
    refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, hms, g, hgdiff, hgconv⟩ := exists_subseq_of_lagRatio_le J E hJ c hc hL ns hns
    have hcoef : ∀ k, iteratedDeriv k g 0 = iteratedDeriv k F 0 := by
      intro k
      have hd := tendstoLocallyUniformly_iterate_deriv hgconv
        (fun m => differentiable_isingCharFn _ _ _) k
      have p1 := (tendstoLocallyUniformlyOn_univ.2 hd).tendsto_at (mem_univ (0 : ℂ))
      have p2 := (hmom k).comp (hns.comp hms)
      simp only [Function.comp_def, ← iteratedDeriv_eq_iterate] at p1 p2
      exact tendsto_nhds_unique p1 p2
    have hgF : g = F := by
      funext z
      have hg := Complex.hasSum_taylorSeries_of_entire hgdiff 0 z
      have hF' := Complex.hasSum_taylorSeries_of_entire hFdiff 0 z
      simp only [hcoef] at hg
      exact hg.unique hF'
    refine ⟨ms, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr ?_⟩
    rw [show (f : ℂ → ℂ) = g from hgF.symm]
    exact hgconv
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

/-- **Convergence of Taylor coefficients suffices.** -/
theorem riemannHypothesis_of_tendsto_iteratedDeriv_isingCharFn
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hmom : ∀ k : ℕ, Tendsto (fun n => iteratedDeriv k (isingCharFn (J n) (E n) (c n)) 0) atTop
      (𝓝 (iteratedDeriv k (fun z => XiC z / XiC 0) 0))) :
    RiemannHypothesis := by
  have hloc := tendstoLocallyUniformly_of_tendsto_iteratedDeriv J E hJ c hc hmom
  have hX0 := XiC_zero_ne
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hFan : AnalyticOnNhd ℂ (fun z => XiC z / XiC 0) univ := fun w _ =>
    (XiC_analytic w (mem_univ w)).div_const
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hloc hFan
    (Eventually.of_forall fun n => differentiable_isingCharFn _ _ _)
    (isClosed_eq Complex.continuous_im continuous_const)
    (Eventually.of_forall fun n w hw => im_eq_zero_of_isingCharFn_eq_zero (hJ n) (hc n) hw)
    (a := 0) (div_ne_zero hX0 hX0) (show XiC z / XiC 0 = 0 by rw [hXiC, zero_div])
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) (by linarith)

/-- **Griffiths–Simon producers by moments.** If the moments of zero-field ferromagnetic Ising
magnetizations with nonnegative masses converge to the moments of Riemann's distribution
`Φ(u)du/Ξ(0)`, then RH holds. -/
theorem riemannHypothesis_of_isingMoment_tendsto
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hmom : ∀ k : ℕ, Tendsto (fun n => (isingMoment (J n) (E n) (c n) k : ℂ)) atTop
      (𝓝 (riemannMoment k))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_tendsto_iteratedDeriv_isingCharFn J E hJ c hc fun k => ?_
  have h := (hmom k).const_mul (I ^ k)
  simp only [iteratedDeriv_isingCharFn_zero]
  have e : I ^ k * riemannMoment k = iteratedDeriv k (fun z => XiC z / XiC 0) 0 := by
    rw [riemannMoment, ← mul_assoc, ← mul_pow, mul_neg, I_mul_I, neg_neg, one_pow, one_mul]
  rwa [e] at h

end

end RHTower.GriffithsSimon
