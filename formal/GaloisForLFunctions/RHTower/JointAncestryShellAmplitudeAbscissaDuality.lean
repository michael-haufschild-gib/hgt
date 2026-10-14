import GaloisForLFunctions.RHTower.JointAncestryConstantVectorDyadicShellDetection

/-!
# Amplitude–abscissa duality for constant-vector tests on dyadic shells

Write `JasConstShellSmallPositive N r` for positivity of the level-one constant-vector JAS test on the
primes of `(N, 2N]` for every constant vector `|z| ≤ r`.

**Producer** (`eventually_jasConstShellSmallPositive`, unconditional).  If every zero satisfies
`|Re ρ − ½| ≤ β' < ½`, then for every `β > β'` the test is positive at all amplitudes `|z| ≤ N^{−β}`
for all large `N`.  The kernel of every zero is within `e^{2 N^{−β}·S_{1−β'}(2N)} − 1 → 0` of `1`,
and the uniform angle `Re(1/(ρ(1−ρ))) ≥ (¼ − β'²)|1/(ρ(1−ρ))|` absorbs the error termwise.

**Receiver** (`eventually_exists_small_neg_shell_of_maximal_offLine`).  A maximal off-line zero at
distance `δ` makes the test negative at some amplitude `|z| ≤ N^{−β}` for every `β < δ`.

**Duality** (`forall_abs_re_sub_half_le_iff_frequently_small_positive`).  Without an off-line chain,
for `0 ≤ β < ½`,

`every zero has |Re ρ − ½| ≤ β  ⟺  ∀ ε > 0, ∃ᶠ N, JasConstShellSmallPositive N (N^{−(β+ε)})`.

So the amplitude exponent of shell positivity is exactly the width of the zero-free strip.  In
particular (`riemannHypothesis_iff_not_jasOffLineChain_and_small_shell_positivity`,
`riemannHypothesis_iff_zerosApproachLine_and_small_shell_positivity`)

`RH ⟺ no off-line chain ∧ ∀ ε > 0, ∃ᶠ N, positivity on (N, 2N] for all |z| ≤ N^{−ε}`,

and the same with ZAL.  A producer therefore needs positivity only on shrinking discs of radius
`N^{−ε}`, for every `ε > 0`, on infinitely many shells; the unconditional producer reaches radius
`N^{−½−ε}`.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- Constant-vector positivity on the shell `(N, 2N]` at all amplitudes `|z| ≤ r`. -/
def JasConstShellSmallPositive (N : ℕ) (r : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ r → 0 ≤ (∑' q : XiZeroCopy, jasConstPairTerm (jasPrimeWindow N (2 * N)) 1
    (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re

theorem JasConstShellSmallPositive.mono {N : ℕ} {r r' : ℝ} (h : JasConstShellSmallPositive N r)
    (hr : r' ≤ r) : JasConstShellSmallPositive N r' :=
  fun z hz => h z (hz.trans hr)

/-- The kernel is within `e^{Σ|x_p|} − 1` of `1`. -/
theorem norm_jasConstKernel_sub_one_le (P : Finset Nat.Primes) (σ : ℝ) (u s : ℂ) :
    ‖jasConstKernel P σ u s - 1‖ ≤
      Real.exp (∑ p ∈ P, ‖jasConstFactor σ u p s - 1‖) - 1 := by
  have h := Finset.norm_prod_one_add_sub_one_le P (fun p => jasConstFactor σ u p s - 1)
  have e : jasConstKernel P σ u s = ∏ p ∈ P, (1 + (jasConstFactor σ u p s - 1)) := by
    rw [jasConstKernel]; exact Finset.prod_congr rfl fun p _ => by ring
  rw [e]; exact h

/-- **A small kernel error leaves a pair term with nonnegative real part**, given the uniform
angle `Re w ≥ c₀|w|` and kernel errors `≤ c₀`. -/
theorem re_jasConstPairTerm_nonneg_of_small {P : Finset Nat.Primes} {σ c₀ : ℝ} {u s : ℂ}
    (hcw : c₀ * ‖1 / (s * (1 - s))‖ ≤ (1 / (s * (1 - s))).re)
    (h1 : ‖jasConstKernel P σ u s - 1‖ ≤ c₀) (h2 : ‖jasConstKernel P σ (conj u) s - 1‖ ≤ c₀) :
    0 ≤ (jasConstPairTerm P σ u s).re := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = 1 / (s * (1 - s)) := ⟨_, rfl⟩
  rw [← hw] at hcw
  have e : jasConstPairTerm P σ u s = 2 * w + ((jasConstKernel P σ u s - 1) +
      (jasConstKernel P σ (conj u) s - 1)) * w := by
    rw [jasConstPairTerm, hw, div_eq_mul_one_div _ (s * (1 - s))]; ring
  rw [e, Complex.add_re]
  have hre : (2 * w).re = 2 * w.re := by simp
  have hd : ‖((jasConstKernel P σ u s - 1) + (jasConstKernel P σ (conj u) s - 1)) * w‖ ≤
      2 * c₀ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)
  have := Complex.abs_re_le_norm (((jasConstKernel P σ u s - 1) +
    (jasConstKernel P σ (conj u) s - 1)) * w)
  have := (abs_le.mp (this.trans hd)).1
  rw [hre]
  linarith

/-- **The unconditional small-amplitude producer.**  If every zero satisfies `|Re ρ − ½| ≤ β'`
with `0 < β' < ½`, then for every `β > β'`, constant-vector positivity holds on `(N, 2N]` at all
amplitudes `|z| ≤ N^{−β}` for all large `N`. -/
theorem eventually_jasConstShellSmallPositive {β' β : ℝ} (hβ'0 : 0 < β') (hβ'h : β' < 1 / 2)
    (hββ' : β' < β) (hzeros : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ β') :
    ∀ᶠ N : ℕ in atTop, JasConstShellSmallPositive N ((N : ℝ) ^ (-β)) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 / 4 - β' ^ 2 := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; nlinarith
  have hc₀1 : c₀ ≤ 1 := by rw [hc₀]; nlinarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 - β' := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have h1α : 0 < 1 - α := by linarith
  have hC0 : 0 < C := by rw [hC]; positivity
  -- the prime sum over the shell
  have ev1 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum α (2 * N) ≤ C * jasMainScale α N := by
    filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos), eventually_ge_atTop 2] with N hN hN2
    have h0 : 0 ≤ 1 / (1 - α) + 1 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (jasMainScale_two_mul_le hα0.le hN2) h0
    have e : C * jasMainScale α N = (1 / (1 - α) + 1) * (2 * jasMainScale α N) := by
      rw [hC]; ring
    rw [e]; linarith
  -- the kernel error tends to zero
  have hγ : 0 < β - (1 - α) := by rw [hα]; linarith
  have hlim : Tendsto (fun N : ℕ => 2 * C * ((N : ℝ) ^ (-β) * jasMainScale α N)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(β - (1 - α))) / Real.log N) atTop (𝓝 0) := by
      have h3 := h1.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact h3
    have h4 := h2.const_mul (2 * C)
    rw [mul_zero] at h4
    refine h4.congr' ((eventually_ge_atTop 2).mono fun N hN => ?_)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [jasMainScale]
    congr 1
    rw [mul_div_assoc', ← Real.rpow_add hNpos]
    congr 2
    ring
  have ev2 := hlim.eventually (ge_mem_nhds (show (0 : ℝ) < c₀ / 2 by positivity))
  filter_upwards [ev1, ev2] with N hN1 hN2 z hz
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hu]
  have hun : ‖u‖ ≤ ‖z‖ := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) (by nlinarith [norm_nonneg z])
  have hu2 : ‖u‖ ≤ (N : ℝ) ^ (-β) := hun.trans hz
  -- every kernel is within `c₀` of `1`
  have hkern : ∀ (v : ℂ), ‖v‖ ≤ (N : ℝ) ^ (-β) → ∀ q : XiZeroCopy,
      ‖jasConstKernel (jasPrimeWindow N (2 * N)) 1 v (q.1 : ℂ) - 1‖ ≤ c₀ := by
    intro v hv q
    obtain ⟨-, hb2⟩ := jasConst_set_bounds (P := jasPrimeWindow N (2 * N)) (σ := 1) (δ := β')
      (by linarith) v (hzeros q)
    have hS := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (1 - β')
    rw [← hα] at hS hb2
    have hsum0 : 0 ≤ ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-α * Real.log p) :=
      Finset.sum_nonneg fun p _ => (Real.exp_pos _).le
    have hx : ∑ p ∈ jasPrimeWindow N (2 * N), ‖jasConstFactor 1 v p (q.1 : ℂ) - 1‖ ≤ c₀ / 2 := by
      refine hb2.trans ?_
      have h1 : 2 * ‖v‖ * ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-α * Real.log p) ≤
          2 * (N : ℝ) ^ (-β) * (C * jasMainScale α N) :=
        mul_le_mul (by linarith) (hS.trans hN1) hsum0 (by positivity)
      have e : 2 * (N : ℝ) ^ (-β) * (C * jasMainScale α N) =
          2 * C * ((N : ℝ) ^ (-β) * jasMainScale α N) := by ring
      linarith
    refine (norm_jasConstKernel_sub_one_le _ 1 v _).trans ?_
    have h3 : Real.exp (c₀ / 2) - 1 ≤ c₀ := by
      have := Real.add_one_le_exp (c₀ / 2)
      have h4 : Real.exp (c₀ / 2) ≤ 1 + 2 * (c₀ / 2) := by
        have := Real.exp_bound' (x := c₀ / 2) (by positivity) (by linarith) (n := 1) one_pos
        simp at this
        nlinarith [Real.exp_pos (c₀ / 2)]
      linarith
    exact (sub_le_sub_right (Real.exp_le_exp.mpr hx) 1).trans h3
  have hcu : ‖conj u‖ ≤ (N : ℝ) ^ (-β) := by rw [Complex.norm_conj]; exact hu2
  have hterm : ∀ q : XiZeroCopy, 0 ≤ (jasConstPairTerm (jasPrimeWindow N (2 * N)) 1 u
      (q.1 : ℂ)).re := fun q =>
    re_jasConstPairTerm_nonneg_of_small
      (hc₀ ▸ quarter_sub_sq_mul_norm_le_re_one_div hβ'h (hzeros q)) (hkern u hu2 q)
      (hkern (conj u) hcu q)
  rw [Complex.re_tsum (summable_jasConstPairTerm _ 1 u)]
  exact tsum_nonneg hterm

/-! ## The duality -/

/-- **Amplitude–abscissa duality.**  Without an off-line chain, for `0 ≤ β < ½`, every zero
satisfies `|Re ρ − ½| ≤ β` iff for every `ε > 0` the constant-vector tests on infinitely many
shells `(N, 2N]` are positive at all amplitudes `|z| ≤ N^{−(β+ε)}`. -/
theorem forall_abs_re_sub_half_le_iff_frequently_small_positive (hno : ¬ JasOffLineChain)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) :
    (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ β) ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
        JasConstShellSmallPositive N ((N : ℝ) ^ (-(β + ε))) := by
  constructor
  · intro hz ε hε
    obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min ε ((1 / 2 - β) / 2) := ⟨_, rfl⟩
    have hε'0 : 0 < ε' := by rw [hε']; exact lt_min hε (by linarith)
    have hε'ε : ε' ≤ ε := by rw [hε']; exact min_le_left _ _
    have hε'h : ε' ≤ (1 / 2 - β) / 2 := by rw [hε']; exact min_le_right _ _
    have hev := eventually_jasConstShellSmallPositive (β' := β + ε' / 2) (β := β + ε')
      (by linarith) (by linarith) (by linarith) fun q => (hz q).trans (by linarith)
    refine (hev.and (eventually_ge_atTop 1)).frequently.mono fun N ⟨hN, hN1⟩ => hN.mono ?_
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  · intro hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨q₁, hq₁⟩ := hcon
    have hoff₁ : (q₁.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₁; linarith
    -- a maximal off-line zero exists
    have hnot : ¬ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
        ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| :=
      fun h => hno ⟨⟨q₁, hoff₁⟩, h⟩
    push Not at hnot
    obtain ⟨q₀, hoff, hmax⟩ := hnot
    have hδβ : β < |(q₀.1 : ℂ).re - 1 / 2| := lt_of_lt_of_le hq₁ (hmax q₁)
    have hδ1 : |(q₀.1 : ℂ).re - 1 / 2| < 1 := by
      have h0 := xiZeroCopy_re_pos q₀
      have h1 := xiZeroCopy_re_lt_one q₀
      rw [abs_lt]; constructor <;> linarith
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (|(q₀.1 : ℂ).re - 1 / 2| - β) / 2 := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hev := eventually_exists_small_neg_shell_of_maximal_offLine q₀ hoff hmax (σ := 1)
      (β := β + ε) hδ1 (by linarith) (by rw [hε]; linarith)
    obtain ⟨N, hpos, z, hzn, hz⟩ := ((hfr ε hε0).and_eventually hev).exists
    exact absurd (hpos z hzn) (not_le.mpr hz)

/-- **RH ⟺ no off-line chain ∧ small-amplitude shell positivity.**  RH holds iff the off-line zeros
form no chain and, for every `ε > 0`, the constant-vector tests on infinitely many dyadic shells
`(N, 2N]` are positive at all amplitudes `|z| ≤ N^{−ε}`. -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_small_shell_positivity :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      JasConstShellSmallPositive N ((N : ℝ) ^ (-ε)) := by
  constructor
  · intro hRH
    have hno : ¬ JasOffLineChain := fun ⟨⟨q, hq⟩, _⟩ =>
      hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
    refine ⟨hno, fun ε hε => ?_⟩
    have h := (forall_abs_re_sub_half_le_iff_frequently_small_positive hno le_rfl
      (by norm_num)).mp (fun q => by
        rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self, abs_zero]) ε hε
    simpa using h
  · rintro ⟨hno, hfr⟩
    have h := (forall_abs_re_sub_half_le_iff_frequently_small_positive hno le_rfl
      (by norm_num)).mpr (fun ε hε => by simpa using hfr ε hε)
    exact riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase fun q => by
      have := h q; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this

/-- The zeros approaching the line excludes an off-line chain. -/
theorem not_jasOffLineChain_of_zerosApproachLine (hZ : BacklundConverse.ZerosApproachLine) :
    ¬ JasOffLineChain := by
  rintro ⟨⟨q₁, hq₁⟩, hch⟩
  by_cases hRH : RiemannHypothesis
  · exact hq₁ (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q₁)
  · obtain ⟨Θ, hΘ, q₀, hq₀, hmaxq⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have habs : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := fun q => by
      rw [LindelofSparse.spectral_im_eq, abs_sub_comm]
    have hq₀' : |(q₀.1 : ℂ).re - 1 / 2| = Θ := by rw [← habs]; exact hq₀
    have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₀'; linarith
    obtain ⟨q, hq⟩ := hch q₀ hoff
    have := hmaxq q
    rw [habs, ← hq₀'] at this
    linarith

/-- **RH ⟺ the zeros approach the line ∧ small-amplitude shell positivity.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_small_shell_positivity :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, JasConstShellSmallPositive N ((N : ℝ) ^ (-ε)) := by
  constructor
  · intro hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      (riemannHypothesis_iff_not_jasOffLineChain_and_small_shell_positivity.mp hRH).2⟩
  · rintro ⟨hZ, hfr⟩
    exact riemannHypothesis_iff_not_jasOffLineChain_and_small_shell_positivity.mpr
      ⟨not_jasOffLineChain_of_zerosApproachLine hZ, hfr⟩

end

end RHTower
