import GaloisForLFunctions.RHTower.MobiusCubicGammaAtomJets
import GaloisForLFunctions.RHTower.MobiusAbelPrefixGramSign
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Abel-prefix mixed Gamma--Hankel Gram as an actual Gamma integral

For `p = 5+δ` the frequency derivatives `∂_x f_x` of the cubic source atoms have the Gamma Gram

`⟨∂_x f_x, ∂_y f_y⟩_δ = x y / (x+y)^(p+2) · ((4-2p)(x+y)² + p(p+1) x y)`,

which is the algebraic kernel `abelPrefixGramKernel`.  It is the mixed second derivative of the
source Gram `K_δ(x,y) = x² y² / (x+y)^p`, so the Gram of the unit Abel dipoles
`g_n = f_n - f_(n+1)` is both the double integral of the mixed kernel over the unit square and
its four-term inclusion--exclusion in `K_δ`.  Summation by parts turns the literal finite Möbius
source into Mertens prefixes, and its energy into the exact arithmetic prefix form.
-/

open MeasureTheory Filter Finset intervalIntegral
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-! ### The mixed Gram as a Gamma integral -/

/-- The first frequency derivative as a monomial--exponential combination. -/
theorem atomJet_one_eq (x : ℝ) :
    atomJet 1 x = fun t => (-x ^ 2) * expMono 1 x t + (2 * x) * expMono 0 x t := by
  funext t
  simp [atomJet, expMono]
  ring

/-- Bilinear expansion of a Gram entry between two-term combinations. -/
theorem gammaInner_two_two {δ : ℝ} (hδ : 0 < 5 + δ) {F₁ F₂ G₁ G₂ : ℝ → ℝ}
    (hF₁ : GammaFinite δ F₁) (hF₂ : GammaFinite δ F₂)
    (hG₁ : GammaFinite δ G₁) (hG₂ : GammaFinite δ G₂) (a₁ a₂ b₁ b₂ : ℝ) :
    gammaInner δ (fun t => a₁ * F₁ t + a₂ * F₂ t) (fun t => b₁ * G₁ t + b₂ * G₂ t) =
      a₁ * b₁ * gammaInner δ F₁ G₁ + a₁ * b₂ * gammaInner δ F₁ G₂ +
        a₂ * b₁ * gammaInner δ F₂ G₁ + a₂ * b₂ * gammaInner δ F₂ G₂ := by
  rw [← inner_toL2 hδ ((hF₁.smul a₁).add (hF₂.smul a₂)) ((hG₁.smul b₁).add (hG₂.smul b₂)),
    toL2_add hδ (hF₁.smul a₁) (hF₂.smul a₂), toL2_add hδ (hG₁.smul b₁) (hG₂.smul b₂),
    toL2_smul hδ hF₁, toL2_smul hδ hF₂, toL2_smul hδ hG₁, toL2_smul hδ hG₂]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [inner_toL2 hδ hF₁ hG₁, inner_toL2 hδ hF₁ hG₂, inner_toL2 hδ hF₂ hG₁,
    inner_toL2 hδ hF₂ hG₂]
  ring

private theorem gamma_succ_succ {p : ℝ} (hp : 0 < p) :
    Real.Gamma (p + 2) = (p + 1) * p * Real.Gamma p := by
  rw [show p + 2 = (p + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
    Real.Gamma_add_one hp.ne']
  ring

/-- **Mixed Gamma--Hankel Gram law** (card equation (2)).  For `x, y > 0`,
`⟨∂_x f_x, ∂_y f_y⟩_δ = abelPrefixGramKernel δ x y`. -/
theorem gammaInner_atomJet_one {δ : ℝ} (hδ : 0 ≤ δ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gammaInner δ (atomJet 1 x) (atomJet 1 y) = abelPrefixGramKernel δ x y := by
  have hδ' : 0 < 5 + δ := by linarith
  rw [atomJet_one_eq, atomJet_one_eq,
    gammaInner_two_two hδ' (gammaFinite_expMono hδ' 1 hx) (gammaFinite_expMono hδ' 0 hx)
      (gammaFinite_expMono hδ' 1 hy) (gammaFinite_expMono hδ' 0 hy),
    gammaInner_expMono hδ' 1 1 hx hy, gammaInner_expMono hδ' 1 0 hx hy,
    gammaInner_expMono hδ' 0 1 hx hy, gammaInner_expMono hδ' 0 0 hx hy]
  set p : ℝ := 5 + δ with hp
  have hs : 0 < x + y := by linarith
  have hg : 0 < Real.Gamma p := Real.Gamma_pos_of_pos hδ'
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, zero_add]
  rw [show p + (1 + 1) = p + 2 by ring, gamma_succ_succ hδ', Real.Gamma_add_one hδ'.ne']
  have e2 : (x + y) ^ (p + 2) = (x + y) ^ p * (x + y) ^ 2 := by
    rw [Real.rpow_add hs, Real.rpow_two]
  have e1 : (x + y) ^ (p + 1) = (x + y) ^ p * (x + y) := by
    rw [Real.rpow_add hs, Real.rpow_one]
  have e7 : (x + y) ^ (7 + δ) = (x + y) ^ p * (x + y) ^ 2 := by
    rw [show (7 + δ : ℝ) = p + 2 by rw [hp]; ring, e2]
  have hP : 0 < (x + y) ^ p := Real.rpow_pos_of_pos hs p
  unfold abelPrefixGramKernel
  rw [abelPrefixGramNumerator_formula, e2, e1, e7, ← hp]
  field_simp
  ring

/-! ### The Gram of the source atoms as a two-variable potential -/

/-- `∂_x K_δ(x,y)`, written with negative powers. -/
def sourceKernelX (δ x y : ℝ) : ℝ :=
  2 * x * y ^ 2 * (x + y) ^ (-(5 + δ)) - (5 + δ) * x ^ 2 * y ^ 2 * (x + y) ^ (-(6 + δ))

private theorem hasDerivAt_rpow_shift (c y : ℝ) {x : ℝ} (hs : 0 < x + y) :
    HasDerivAt (fun x => (x + y) ^ c) (c * (x + y) ^ (c - 1)) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x + y) (p := c) (Or.inl hs.ne')).comp x
    ((hasDerivAt_id x).add_const y)
  rw [mul_one] at h
  exact h

private theorem hasDerivAt_rpow_shift' (c x : ℝ) {y : ℝ} (hs : 0 < x + y) :
    HasDerivAt (fun y => (x + y) ^ c) (c * (x + y) ^ (c - 1)) y := by
  have h := (Real.hasDerivAt_rpow_const (x := x + y) (p := c) (Or.inl hs.ne')).comp y
    ((hasDerivAt_id y).const_add x)
  rw [mul_one] at h
  exact h

theorem sourceKernel_eq_mul_rpow_neg {δ x y : ℝ} (hs : 0 < x + y) :
    sourceKernel δ x y = x ^ 2 * y ^ 2 * (x + y) ^ (-(5 + δ)) := by
  rw [sourceKernel, Real.rpow_neg hs.le, div_eq_mul_inv]

theorem hasDerivAt_sourceKernel_fst (δ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x => sourceKernel δ x y) (sourceKernelX δ x y) x := by
  have hs : 0 < x + y := by linarith
  have hev : (fun x => sourceKernel δ x y) =ᶠ[nhds x]
      fun x => x ^ 2 * y ^ 2 * (x + y) ^ (-(5 + δ)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.add continuous_const)).mem_nhds
      (show (0 : ℝ) < x + y from hs)] with z hz
    exact sourceKernel_eq_mul_rpow_neg hz
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 := ((hasDerivAt_pow 2 x).mul_const (y ^ 2)).mul (hasDerivAt_rpow_shift (-(5 + δ)) y hs)
  refine h1.congr_deriv ?_
  unfold sourceKernelX
  rw [show -(5 + δ) - 1 = -(6 + δ) by ring]
  push_cast
  ring

theorem hasDerivAt_sourceKernelX_snd (δ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y => sourceKernelX δ x y) (abelPrefixGramKernel δ x y) y := by
  have hs : 0 < x + y := by linarith
  have h1 := ((hasDerivAt_pow 2 y).const_mul (2 * x)).mul
    (hasDerivAt_rpow_shift' (-(5 + δ)) x hs)
  have h2 := ((hasDerivAt_pow 2 y).const_mul ((5 + δ) * x ^ 2)).mul
    (hasDerivAt_rpow_shift' (-(6 + δ)) x hs)
  refine (h1.sub h2).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · have e5 : (x + y) ^ (-(5 + δ)) = (x + y) ^ (-(7 + δ)) * (x + y) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hs]; ring_nf
    have e6 : (x + y) ^ (-(6 + δ)) = (x + y) ^ (-(7 + δ)) * (x + y) := by
      rw [← Real.rpow_add_one hs.ne']; ring_nf
    have e6' : (x + y) ^ (-(5 + δ) - 1) = (x + y) ^ (-(7 + δ)) * (x + y) := by
      rw [show -(5 + δ) - 1 = -(6 + δ) by ring, e6]
    have e7' : (x + y) ^ (-(6 + δ) - 1) = (x + y) ^ (-(7 + δ)) := by
      rw [show -(6 + δ) - 1 = -(7 + δ) by ring]
    unfold abelPrefixGramKernel
    rw [abelPrefixGramNumerator_formula, e5, e6', e7', e6, div_eq_mul_inv,
      ← Real.rpow_neg hs.le]
    push_cast
    ring
  · filter_upwards with z
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold sourceKernelX
    ring

/-! ### Abel dipoles -/

/-- The unit Abel dipole `g_x = f_x - f_(x+1)`. -/
def abelDipole (x t : ℝ) : ℝ := atom x t - atom (x + 1) t

theorem gammaFinite_abelDipole {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 < x) :
    GammaFinite δ (abelDipole x) :=
  (gammaFinite_atom hδ hx).sub (gammaFinite_atom hδ (by linarith))

/-- The dipole is minus the frequency integral of the first jet. -/
theorem abelDipole_eq_neg_integral (x t : ℝ) :
    abelDipole x t = -∫ u in x..x + 1, atomJet 1 u t := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun u => atomJet 0 u t)
    (fun u _ => hasDerivAt_atomJet 0 t u)
    ((continuous_iff_continuousAt.mpr fun u => by
      have := (hasDerivAt_atomJet 1 t u).continuousAt
      exact this).intervalIntegrable _ _)]
  simp only [atomJet_zero, abelDipole]
  ring

/-- The discrete Gram `D_δ(m,n)` as a four-term inclusion--exclusion in `K_δ`. -/
def abelDipoleGram (δ m n : ℝ) : ℝ :=
  sourceKernel δ m n - sourceKernel δ (m + 1) n - sourceKernel δ m (n + 1) +
    sourceKernel δ (m + 1) (n + 1)

/-- **Card equation (3), first half.**  `⟨g_m, g_n⟩_δ` is the four-term inclusion--exclusion. -/
theorem gammaInner_abelDipole {δ : ℝ} (hδ : 0 < 5 + δ) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    gammaInner δ (abelDipole m) (abelDipole n) = abelDipoleGram δ m n := by
  have hm1 : 0 < m + 1 := by linarith
  have hn1 : 0 < n + 1 := by linarith
  have e : ∀ x, abelDipole x = fun t => 1 * atom x t + (-1) * atom (x + 1) t := by
    intro x; funext t; simp [abelDipole]; ring
  rw [e, e, gammaInner_two_two hδ (gammaFinite_atom hδ hm) (gammaFinite_atom hδ hm1)
    (gammaFinite_atom hδ hn) (gammaFinite_atom hδ hn1),
    gammaInner_atom hδ hm hn, gammaInner_atom hδ hm hn1, gammaInner_atom hδ hm1 hn,
    gammaInner_atom hδ hm1 hn1]
  unfold abelDipoleGram
  ring

theorem continuousOn_abelPrefixGramKernel (δ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => abelPrefixGramKernel δ p.1 p.2) {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
  intro p hp
  have hs : p.1 + p.2 ≠ 0 := by have := hp.1; have := hp.2; positivity
  apply ContinuousAt.continuousWithinAt
  unfold abelPrefixGramKernel abelPrefixGramNumerator abelPrefixGramCore
  apply ContinuousAt.mul
  · apply ContinuousAt.div (by fun_prop)
    · exact ContinuousAt.rpow_const (by fun_prop) (Or.inl hs)
    · exact (Real.rpow_pos_of_pos (by have := hp.1; have := hp.2; positivity) _).ne'
  · fun_prop

/-- **Card equation (3), second half.**  The dipole Gram is the double integral of the mixed
kernel over the unit frequency square. -/
theorem integral_integral_abelPrefixGramKernel (δ : ℝ) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in m..m + 1, ∫ y in n..n + 1, abelPrefixGramKernel δ x y) = abelDipoleGram δ m n := by
  have hinner : ∀ x ∈ Set.uIcc m (m + 1), (∫ y in n..n + 1, abelPrefixGramKernel δ x y) =
      sourceKernelX δ x (n + 1) - sourceKernelX δ x n := by
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le (by linarith)] at hx; linarith [hx.1]
    refine integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
    · have : 0 < y := by rw [Set.uIcc_of_le (by linarith)] at hy; linarith [hy.1]
      exact hasDerivAt_sourceKernelX_snd δ hx0 this
    · refine ContinuousOn.intervalIntegrable ?_
      have hc := continuousOn_abelPrefixGramKernel δ
      refine hc.comp (f := fun y : ℝ => ((x, y) : ℝ × ℝ))
        ((continuous_const.prodMk continuous_id).continuousOn) ?_
      intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact ⟨hx0, by linarith [hy.1]⟩
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_sub]
  · have hX : ∀ c : ℝ, 0 < c → (∫ x in m..m + 1, sourceKernelX δ x c ∂volume) =
        sourceKernel δ (m + 1) c - sourceKernel δ m c := by
      intro c hc
      refine integral_eq_sub_of_hasDerivAt (f := fun x => sourceKernel δ x c)
        (f' := fun x => sourceKernelX δ x c) (fun x hx => ?_) ?_
      · have : 0 < x := by rw [Set.uIcc_of_le (by linarith)] at hx; linarith [hx.1]
        exact hasDerivAt_sourceKernel_fst δ this hc
      · refine ContinuousOn.intervalIntegrable ?_
        intro x hx
        have : 0 < x := by rw [Set.uIcc_of_le (by linarith)] at hx; linarith [hx.1]
        have hs : x + c ≠ 0 := by positivity
        apply ContinuousAt.continuousWithinAt
        unfold sourceKernelX
        apply ContinuousAt.sub
        · exact ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs))
        · exact ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs))
    rw [hX (n + 1) (by linarith), hX n hn]
    unfold abelDipoleGram
    ring
  all_goals
    refine ContinuousOn.intervalIntegrable ?_
    intro x hx
    have : 0 < x := by rw [Set.uIcc_of_le (by linarith)] at hx; linarith [hx.1]
    apply ContinuousAt.continuousWithinAt
    unfold sourceKernelX
    have hs1 : x + (n + 1) ≠ 0 := by positivity
    have hs2 : x + n ≠ 0 := by positivity
    first
    | exact ContinuousAt.sub
        (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs1)))
        (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs1)))
    | exact ContinuousAt.sub
        (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs2)))
        (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs2)))

/-! ### Summation by parts and the prefix energy -/

/-- Prefix sums `A(n) = Σ_{1 ≤ k ≤ n} a_k`. -/
def prefixSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, a k

theorem prefixSum_succ (a : ℕ → ℝ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a (n + 1) := by
  unfold prefixSum
  rw [sum_Icc_succ_top (by omega)]

/-- Finite summation by parts at cutoff `K+1`. -/
theorem sum_Icc_eq_abel (a f : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Icc 1 (K + 1), a n * f n =
      prefixSum a (K + 1) * f (K + 1) + ∑ n ∈ Icc 1 K, prefixSum a n * (f n - f (n + 1)) := by
  induction K with
  | zero => simp [prefixSum]
  | succ K ih =>
      rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega : 1 ≤ K + 1),
        prefixSum_succ a (K + 1)]
      ring

/-- The Mertens prefix `M(n) = Σ_{k ≤ n} μ(k)`. -/
def abelMertens (n : ℕ) : ℝ := prefixSum (fun k => ((μ k : ℤ) : ℝ)) n

/-- The literal finite cubic Möbius source `S_N(t) = Σ_{n ≤ N} μ(n) n² e^{-n t}`. -/
def mobiusCubicSource (N : ℕ) (t : ℝ) : ℝ := ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) * atom n t

/-- **Card equation (1).**  `S_N = M(N) f_N + Σ_{n<N} M(n) g_n` at cutoff `N = K+1`. -/
theorem mobiusCubicSource_eq_abel (K : ℕ) (t : ℝ) :
    mobiusCubicSource (K + 1) t =
      abelMertens (K + 1) * atom ((K + 1 : ℕ) : ℝ) t +
        ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t := by
  unfold mobiusCubicSource abelMertens
  rw [sum_Icc_eq_abel (fun k => ((μ k : ℤ) : ℝ)) (fun n => atom n t) K]
  congr 1
  apply sum_congr rfl
  intro n _
  unfold abelDipole
  push_cast
  ring

theorem sourceKernel_comm (δ x y : ℝ) : sourceKernel δ x y = sourceKernel δ y x := by
  unfold sourceKernel
  rw [add_comm x y]
  ring

theorem gammaInner_atom_abelDipole {δ : ℝ} (hδ : 0 < 5 + δ) {x n : ℝ} (hx : 0 < x)
    (hn : 0 < n) :
    gammaInner δ (atom x) (abelDipole n) = sourceKernel δ x n - sourceKernel δ x (n + 1) := by
  have hn1 : 0 < n + 1 := by linarith
  have e1 : atom x = fun t => 1 * atom x t + 0 * atom x t := by funext t; ring
  have e2 : abelDipole n = fun t => 1 * atom n t + (-1) * atom (n + 1) t := by
    funext t; simp [abelDipole]; ring
  rw [e1, e2, gammaInner_two_two hδ (gammaFinite_atom hδ hx) (gammaFinite_atom hδ hx)
    (gammaFinite_atom hδ hn) (gammaFinite_atom hδ hn1), gammaInner_atom hδ hx hn,
    gammaInner_atom hδ hx hn1]
  ring

/-- **Card equation (4).**  The exact arithmetic prefix form of the finite source energy at
cutoff `N = K+1`. -/
theorem gammaEnergy_mobiusCubicSource {δ : ℝ} (hδ : 0 < 5 + δ) (K : ℕ) :
    gammaEnergy δ (mobiusCubicSource (K + 1)) =
      abelMertens (K + 1) ^ 2 * sourceKernel δ (K + 1 : ℕ) (K + 1 : ℕ) +
        2 * abelMertens (K + 1) * ∑ n ∈ Icc 1 K, abelMertens n *
          (sourceKernel δ n (K + 1 : ℕ) - sourceKernel δ ((n : ℝ) + 1) (K + 1 : ℕ)) +
        ∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K, abelMertens m * abelMertens n * abelDipoleGram δ m n := by
  set N : ℝ := ((K + 1 : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; positivity
  have hpos : ∀ n ∈ Icc 1 K, (0 : ℝ) < n := fun n hn => by
    have := (mem_Icc.mp hn).1; exact_mod_cast this
  have hdip : ∀ n ∈ Icc 1 K, GammaFinite δ (abelDipole n) := fun n hn =>
    gammaFinite_abelDipole hδ (hpos n hn)
  have hdipc : ∀ n ∈ Icc 1 K, GammaFinite δ (fun t => abelMertens n * abelDipole n t) :=
    fun n hn => (hdip n hn).smul _
  have hu : GammaFinite δ (fun t => abelMertens (K + 1) * atom N t) :=
    (gammaFinite_atom hδ hN0).smul _
  have hv := GammaFinite.sum (Icc 1 K) hdipc
  have heq : mobiusCubicSource (K + 1) = fun t => abelMertens (K + 1) * atom N t +
      ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t := by
    funext t; exact mobiusCubicSource_eq_abel K t
  rw [heq, gammaEnergy_add hδ hu hv]
  have hE1 : gammaEnergy δ (fun t => abelMertens (K + 1) * atom N t) =
      abelMertens (K + 1) ^ 2 * sourceKernel δ N N := by
    rw [gammaEnergy, gammaInner_smul_left hδ (gammaFinite_atom hδ hN0) hu, gammaInner_comm,
      gammaInner_smul_left hδ (gammaFinite_atom hδ hN0) (gammaFinite_atom hδ hN0),
      gammaInner_atom hδ hN0 hN0]
    ring
  have hE2 : gammaInner δ (fun t => abelMertens (K + 1) * atom N t)
      (fun t => ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t) =
      abelMertens (K + 1) * ∑ n ∈ Icc 1 K, abelMertens n *
        (sourceKernel δ n N - sourceKernel δ ((n : ℝ) + 1) N) := by
    rw [gammaInner_smul_left hδ (gammaFinite_atom hδ hN0) hv, gammaInner_comm,
      gammaInner_sum_left hδ _ hdipc (gammaFinite_atom hδ hN0)]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [gammaInner_smul_left hδ (hdip n hn) (gammaFinite_atom hδ hN0), gammaInner_comm,
      gammaInner_atom_abelDipole hδ hN0 (hpos n hn), sourceKernel_comm δ N,
      sourceKernel_comm δ N]
  have hE3 : gammaEnergy δ (fun t => ∑ n ∈ Icc 1 K, abelMertens n * abelDipole n t) =
      ∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K, abelMertens m * abelMertens n * abelDipoleGram δ m n := by
    rw [gammaEnergy_sum hδ (Icc 1 K) abelMertens hdip]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    rw [gammaInner_abelDipole hδ (hpos m hm) (hpos n hn)]
  rw [hE1, hE2, hE3]
  ring

/-! ### Quantitative sign atlas -/

/-- The stronger comparable-scale lower bound `B_δ ≥ (3+2δ+δ²) x y`. -/
theorem abelPrefixGramNumerator_ge_strong {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ 2 * y) (hyx : y ≤ 2 * x) :
    (3 + 2 * δ + δ ^ 2) * (x * y) ≤ abelPrefixGramNumerator δ x y := by
  have hC : 0 ≤ x * y := mul_nonneg hx hy
  have hp : (x - 2 * y) * (2 * x - y) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hA : x * y ≤ 2 * abelPrefixGramCore x y := by unfold abelPrefixGramCore; nlinarith
  have hm := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 3 + δ)
  unfold abelPrefixGramNumerator
  nlinarith

/-- Equality case of the comparable bound: `δ = 0`, `x = 2y`. -/
theorem abelPrefixGramNumerator_zero_two_mul (y : ℝ) :
    abelPrefixGramNumerator 0 (2 * y) y = 3 * (2 * y) * y := by
  unfold abelPrefixGramNumerator abelPrefixGramCore
  ring

/-- Equality case of the separated bound: `δ = 1`, `x = 3y`. -/
theorem abelPrefixGramNumerator_one_three_mul (y : ℝ) :
    3 * abelPrefixGramNumerator 1 (3 * y) y = -2 * (3 * y) * y := by
  unfold abelPrefixGramNumerator abelPrefixGramCore
  ring

/-- **Sharpness of the comparable constant.**  `3` is the largest constant `c` with
`c x y ≤ B_δ(x,y)` on the comparable region, uniformly for `0 ≤ δ ≤ 1`. -/
theorem isGreatest_abelPrefixGram_comparable_constant :
    IsGreatest {c : ℝ | ∀ δ ∈ Set.Icc (0 : ℝ) 1, ∀ x y : ℝ, 0 < x → 0 < y → x ≤ 2 * y →
      y ≤ 2 * x → c * x * y ≤ abelPrefixGramNumerator δ x y} 3 := by
  refine ⟨fun δ hδ x y hx hy hxy hyx => ?_, fun c hc => ?_⟩
  · have := abelPrefixGramNumerator_ge_three_mul hδ.1 hx.le hy.le hxy hyx
    linarith
  · have h := hc 0 ⟨le_rfl, zero_le_one⟩ 2 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have e := abelPrefixGramNumerator_zero_two_mul 1
    norm_num at h e
    linarith

/-- **Sharpness of the separated constant.**  `-2` is the least constant `c` with
`3 B_δ(x,y) ≤ c x y` whenever `x ≥ 3y`, uniformly for `0 ≤ δ ≤ 1`. -/
theorem isLeast_abelPrefixGram_separated_constant :
    IsLeast {c : ℝ | ∀ δ ∈ Set.Icc (0 : ℝ) 1, ∀ x y : ℝ, 0 < y → 3 * y ≤ x →
      3 * abelPrefixGramNumerator δ x y ≤ c * x * y} (-2) := by
  refine ⟨fun δ hδ x y hy hxy => ?_, fun c hc => ?_⟩
  · have := abelPrefixGramNumerator_le_neg_two_thirds hδ.1 hδ.2 hy.le hxy
    linarith
  · have h := hc 1 ⟨zero_le_one, le_rfl⟩ 3 1 (by norm_num) (by norm_num)
    have e := abelPrefixGramNumerator_one_three_mul 1
    norm_num at h e
    linarith

/-- The transition constant `c_δ = 3 + δ(1+δ)/(6+2δ)`. -/
def abelTransitionConstant (δ : ℝ) : ℝ := 3 + δ * (1 + δ) / (6 + 2 * δ)

/-- The numerator in the scale ratio `r = x/y`: `B_δ = (6+2δ) x y (c_δ - r - 1/r)`. -/
theorem abelPrefixGramNumerator_eq_transition {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x)
    (hy : 0 < y) :
    abelPrefixGramNumerator δ x y =
      (6 + 2 * δ) * (x * y) * (abelTransitionConstant δ - x / y - y / x) := by
  unfold abelPrefixGramNumerator abelPrefixGramCore abelTransitionConstant
  have h6 : (6 + 2 * δ) ≠ 0 := by linarith
  field_simp
  ring

/-- **Exact transition.**  `sign G_δ(x,y) = sign(c_δ - r - 1/r)`, `r = x/y`. -/
theorem sign_abelPrefixGramKernel {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (hy : 0 < y) :
    SignType.sign (abelPrefixGramKernel δ x y) =
      SignType.sign (abelTransitionConstant δ - x / y - y / x) := by
  have hpos : 0 < x * y / (x + y) ^ (7 + δ) * ((6 + 2 * δ) * (x * y)) := by
    have : 0 < (x + y) ^ (7 + δ) := Real.rpow_pos_of_pos (by linarith) _
    have : 0 < 6 + 2 * δ := by linarith
    positivity
  unfold abelPrefixGramKernel
  rw [abelPrefixGramNumerator_eq_transition hδ hx hy, ← mul_assoc, sign_mul, sign_pos hpos,
    one_mul]

theorem hasDerivAt_abelTransitionConstant {δ : ℝ} (hδ : 0 ≤ δ) :
    HasDerivAt abelTransitionConstant ((6 + 12 * δ + 2 * δ ^ 2) / (6 + 2 * δ) ^ 2) δ := by
  have h6 : (6 + 2 * δ) ≠ 0 := by linarith
  have h := (((hasDerivAt_id δ).mul ((hasDerivAt_id δ).const_add 1)).div
    (((hasDerivAt_id δ).const_mul 2).const_add 6) h6).const_add 3
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.mul_apply]
  field_simp
  ring

/-- `c_δ` is strictly increasing for `δ ≥ 0`, in particular on `[0,1]`. -/
theorem strictMonoOn_abelTransitionConstant :
    StrictMonoOn abelTransitionConstant (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold abelTransitionConstant
  have ha6 : 0 < 6 + 2 * a := by linarith
  have hb6 : 0 < 6 + 2 * b := by linarith
  rw [add_lt_add_iff_left, div_lt_div_iff₀ ha6 hb6]
  have hba : 0 < b - a := by linarith
  nlinarith [mul_pos hba (by positivity : (0 : ℝ) < 6 + 6 * (a + b) + 2 * a * b)]

/-- For `c > 2` and `r > 0`, `c - r - 1/r > 0` exactly on the reciprocal interval
`(1/r₊, r₊)`, `r₊ = (c + √(c²-4))/2`. -/
theorem sub_sub_inv_pos_iff {c r : ℝ} (hc : 2 < c) (hr : 0 < r) :
    0 < c - r - 1 / r ↔
      r ∈ Set.Ioo ((c + Real.sqrt (c ^ 2 - 4)) / 2)⁻¹ ((c + Real.sqrt (c ^ 2 - 4)) / 2) := by
  set s := Real.sqrt (c ^ 2 - 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = c ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hsc : s < c := by
    rw [hs, Real.sqrt_lt' (by linarith)]
    linarith
  have hplus : 0 < (c + s) / 2 := by linarith
  have hinv : ((c + s) / 2)⁻¹ = (c - s) / 2 := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hss]
  rw [hinv, Set.mem_Ioo]
  have hkey : c - r - 1 / r = -((r - (c - s) / 2) * (r - (c + s) / 2)) / r := by
    field_simp
    nlinarith [hss]
  rw [hkey, div_pos_iff_of_pos_right hr, neg_pos]
  constructor
  · intro h
    rcases lt_or_ge r ((c - s) / 2) with h1 | h1
    · exfalso
      have : 0 < (r - (c - s) / 2) * (r - (c + s) / 2) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith
    · rcases lt_or_ge r ((c + s) / 2) with h2 | h2
      · refine ⟨lt_of_le_of_ne h1 ?_, h2⟩
        intro he
        rw [← he] at h
        simp at h
      · exfalso
        have : 0 ≤ (r - (c - s) / 2) * (r - (c + s) / 2) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
  · rintro ⟨h1, h2⟩
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem abelTransitionConstant_zero : abelTransitionConstant 0 = 3 := by
  norm_num [abelTransitionConstant]

theorem abelTransitionConstant_one : abelTransitionConstant 1 = 13 / 4 := by
  norm_num [abelTransitionConstant]

/-- The upper transition ratio at `δ = 0` is `(3+√5)/2`. -/
theorem abelTransition_upper_zero :
    (abelTransitionConstant 0 + Real.sqrt (abelTransitionConstant 0 ^ 2 - 4)) / 2 =
      (3 + Real.sqrt 5) / 2 := by
  rw [abelTransitionConstant_zero]
  norm_num

/-- The upper transition ratio at `δ = 1` is `(13+√105)/8`. -/
theorem abelTransition_upper_one :
    (abelTransitionConstant 1 + Real.sqrt (abelTransitionConstant 1 ^ 2 - 4)) / 2 =
      (13 + Real.sqrt 105) / 8 := by
  rw [abelTransitionConstant_one]
  have h : Real.sqrt ((13 / 4 : ℝ) ^ 2 - 4) = Real.sqrt 105 / 4 := by
    rw [show (13 / 4 : ℝ) ^ 2 - 4 = 105 / 16 by norm_num, Real.sqrt_div' _ (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  ring

/-- `c_δ > 2` for `δ ≥ 0`. -/
theorem two_lt_abelTransitionConstant {δ : ℝ} (hδ : 0 ≤ δ) : 2 < abelTransitionConstant δ := by
  unfold abelTransitionConstant
  have : 0 ≤ δ * (1 + δ) / (6 + 2 * δ) := by positivity
  linarith

/-- **The positive Gram chamber.**  For `x, y > 0`, `G_δ(x,y) > 0` exactly when `x/y` lies in
the reciprocal interval of the transition ratio. -/
theorem abelPrefixGramKernel_pos_iff {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (hy : 0 < y) :
    0 < abelPrefixGramKernel δ x y ↔
      x / y ∈ Set.Ioo ((abelTransitionConstant δ +
          Real.sqrt (abelTransitionConstant δ ^ 2 - 4)) / 2)⁻¹
        ((abelTransitionConstant δ + Real.sqrt (abelTransitionConstant δ ^ 2 - 4)) / 2) := by
  rw [← sub_sub_inv_pos_iff (two_lt_abelTransitionConstant hδ) (div_pos hx hy),
    ← sign_eq_one_iff, sign_abelPrefixGramKernel hδ hx hy, sign_eq_one_iff, one_div_div]

/-! ### Signs of the discrete dipole Gram -/

theorem abelDipoleGram_comm (δ m n : ℝ) : abelDipoleGram δ m n = abelDipoleGram δ n m := by
  unfold abelDipoleGram
  rw [sourceKernel_comm δ m n, sourceKernel_comm δ (m + 1) n, sourceKernel_comm δ m (n + 1),
    sourceKernel_comm δ (m + 1) (n + 1)]
  ring

private theorem inner_integral_eq {δ x n : ℝ} (hx : 0 < x) (hn : 0 < n) :
    (∫ y in n..n + 1, abelPrefixGramKernel δ x y) =
      sourceKernelX δ x (n + 1) - sourceKernelX δ x n := by
  refine integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
  · have : 0 < y := by rw [Set.uIcc_of_le (by linarith)] at hy; linarith [hy.1]
    exact hasDerivAt_sourceKernelX_snd δ hx this
  · refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_abelPrefixGramKernel δ).comp (f := fun y : ℝ => ((x, y) : ℝ × ℝ))
      ((continuous_const.prodMk continuous_id).continuousOn) ?_
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact ⟨hx, by linarith [hy.1]⟩

private theorem continuousOn_sourceKernelX_fst (δ c : ℝ) (hc : 0 < c) :
    ContinuousOn (fun x => sourceKernelX δ x c) (Set.Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hs : x + c ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold sourceKernelX
  exact ContinuousAt.sub
    (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs)))
    (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs)))

private theorem double_integral_pos {δ m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hpos : ∀ x ∈ Set.Ioo m (m + 1), ∀ y ∈ Set.Ioo n (n + 1), 0 < abelPrefixGramKernel δ x y) :
    0 < abelDipoleGram δ m n := by
  rw [← integral_integral_abelPrefixGramKernel δ hm hn]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) (by linarith)
  · refine (ContinuousOn.intervalIntegrable
      (u := fun x => sourceKernelX δ x (n + 1) - sourceKernelX δ x n) ?_).congr ?_
    · refine ((continuousOn_sourceKernelX_fst δ _ (by linarith)).sub
        (continuousOn_sourceKernelX_fst δ _ hn)).mono ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact show (0 : ℝ) < x by linarith [hx.1]
    · intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact (inner_integral_eq (by linarith [hx.1]) hn).symm
  · have hx0 : 0 < x := by linarith [hx.1]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun y hy => hpos x hx y hy)
      (by linarith)
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_abelPrefixGramKernel δ).comp (f := fun y : ℝ => ((x, y) : ℝ × ℝ))
      ((continuous_const.prodMk continuous_id).continuousOn) ?_
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact ⟨hx0, by linarith [hy.1]⟩

/-- **Positive discrete chamber.**  `D_δ(m,n) > 0` when `m+1 ≤ 2n` and `n+1 ≤ 2m`. -/
theorem abelDipoleGram_pos {δ m n : ℝ} (hδ : 0 ≤ δ) (hm : 0 < m) (hn : 0 < n)
    (hmn : m + 1 ≤ 2 * n) (hnm : n + 1 ≤ 2 * m) : 0 < abelDipoleGram δ m n :=
  double_integral_pos hm hn fun x hx y hy =>
    abelPrefixGramKernel_pos_of_comparable hδ (by linarith [hx.1]) (by linarith [hy.1])
      (by linarith [hx.2, hy.1]) (by linarith [hx.1, hy.2])

/-- **Negative discrete chamber.**  `D_δ(m,n) < 0` when `m ≥ 3(n+1)`, for `0 ≤ δ ≤ 1`. -/
theorem abelDipoleGram_neg {δ m n : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm : 0 < m) (hn : 0 < n)
    (hmn : 3 * (n + 1) ≤ m) : abelDipoleGram δ m n < 0 := by
  have h : 0 < -abelDipoleGram δ m n := by
    have e : -abelDipoleGram δ m n = abelDipoleGram δ m n * (-1) := by ring
    rw [← integral_integral_abelPrefixGramKernel δ hm hn]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) (by linarith)
    · refine (ContinuousOn.intervalIntegrable
        (u := fun x => -(sourceKernelX δ x (n + 1) - sourceKernelX δ x n)) ?_).congr ?_
      · refine (((continuousOn_sourceKernelX_fst δ _ (by linarith)).sub
          (continuousOn_sourceKernelX_fst δ _ hn)).neg).mono ?_
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        exact show (0 : ℝ) < x by linarith [hx.1]
      · intro x hx
        rw [Set.uIoc_of_le (by linarith)] at hx
        simp only
        rw [inner_integral_eq (by linarith [hx.1]) hn]
    · have hx0 : 0 < x := by linarith [hx.1]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun y hy => ?_) (by linarith)
      · refine ContinuousOn.intervalIntegrable ?_
        refine ((continuousOn_abelPrefixGramKernel δ).comp
          (f := fun y : ℝ => ((x, y) : ℝ × ℝ))
          ((continuous_const.prodMk continuous_id).continuousOn) ?_).neg
        intro y hy
        rw [Set.uIcc_of_le (by linarith)] at hy
        exact ⟨hx0, by linarith [hy.1]⟩
      · exact neg_pos.mpr (abelPrefixGramKernel_neg_of_separated hδ0 hδ1
          (by linarith [hy.1]) (by linarith [hx.1, hy.2]))
  linarith

/-- The symmetric negative chamber `n ≥ 3(m+1)`. -/
theorem abelDipoleGram_neg' {δ m n : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hm : 0 < m) (hn : 0 < n)
    (hnm : 3 * (m + 1) ≤ n) : abelDipoleGram δ m n < 0 := by
  rw [abelDipoleGram_comm]
  exact abelDipoleGram_neg hδ0 hδ1 hn hm hnm

end RHTower.CubicGamma
