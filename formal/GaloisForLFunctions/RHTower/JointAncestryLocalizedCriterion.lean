import GaloisForLFunctions.RHTower.JointAncestryArithmeticCriterion
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase

/-!
# The localized dressed aggregate and a chain-free criterion

Replace the lag weights `1/(ρ(1-ρ))` by Gaussian-localized weights
`G_{T,Δ}(ρ)/(ρ(1-ρ))` with `G_{T,Δ}(s) = exp((s − ½ − iT)²/(2Δ²))`, so that
`|G_{T,Δ}(ρ)| = exp((δ² − (γ − T)²)/(2Δ²))` for `ρ = ½ + δ + iγ`.  On the critical line the weights
are positive, so RH makes every localized dressed aggregate positive semidefinite.

Conversely, an off-line zero is detected at a *fixed finite depth*: the exponent
`f_T(ρ) = δ² − (γ − T)²` attains its maximum at finitely many zeros, a small shift of `T` makes the
maximizing height unique, a finite prime set gives the maximizing pair a phase budget above `π` so its
weighted sector can be rotated to a strictly negative real value, and letting `Δ → 0` suppresses every
other zero by `exp(−κ/(2Δ²))`.  No competition at infinite depth occurs, so off-line chains play no
role:

`RH ⟺ ∀ T, ∀ Δ > 0, the localized aggregate is positive semidefinite at σ = ½ + c`

for every fixed `c ∈ (0, ½]`.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Weighted dressed aggregates -/

/-- The dressed aggregate with arbitrary zero weights `c_ρ`. -/
def jasWeightedAggregate (cw : XiZeroCopy → ℂ) (κ : ℝ) (n : Nat.Primes →₀ ℤ) : ℂ :=
  ∑' q : XiZeroCopy, cw q * jasDressedCoeff ((q.1 : ℂ) + κ) ((q.1 : ℂ) - κ) n

/-- Positive semidefiniteness of a weighted dressed aggregate on rational characters. -/
def JasWeightedPSD (cw : XiZeroCopy → ℂ) (κ : ℝ) : Prop :=
  ∀ (ι : Type) (t : Finset ι) (cc : ι → ℂ) (n : ι → Nat.Primes →₀ ℤ), Set.InjOn n t →
    0 ≤ (∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasWeightedAggregate cw κ (n i - n j)).re

theorem norm_jasDressedCoeff_le_one {q : ℂ} {c : ℝ} (h0 : 0 < q.re + c) (h1 : 0 < 1 - q.re + c)
    (n : Nat.Primes →₀ ℤ) : ‖jasDressedCoeff (q + c) (q - c) n‖ ≤ 1 := by
  rw [jasDressedCoeff, Finsupp.prod, norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun p _ => ?_
  rw [jasDressedLocalCoeff]
  split_ifs
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_jasHoloA_dressed_lt_one h0 p).le
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_jasHoloB_dressed_lt_one h1 p).le

theorem summable_weighted_term {cw : XiZeroCopy → ℂ} (hcw : Summable fun q => ‖cw q‖) {c : ℝ}
    (hc : 0 < c) (a : ℂ) (n : Nat.Primes →₀ ℤ) :
    Summable fun q : XiZeroCopy =>
      a * (cw q * jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) n) := by
  refine Summable.of_norm_bounded (hcw.mul_left ‖a‖) fun q => ?_
  have h0 : 0 < (q.1 : ℂ).re + c := by linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  have h1 : 0 < 1 - (q.1 : ℂ).re + c := by linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  rw [norm_mul, norm_mul]
  have := norm_jasDressedCoeff_le_one h0 h1 n
  calc ‖a‖ * (‖cw q‖ * ‖jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) n‖)
      ≤ ‖a‖ * (‖cw q‖ * 1) := by gcongr
    _ = ‖a‖ * ‖cw q‖ := by ring

/-- The weighted Fejér form on the box `[0,K]^P` at the torus point `w`. -/
def jasWeightedFejerForm (cw : XiZeroCopy → ℂ) (κ : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ)
    (K : ℕ) : ℂ :=
  ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K,
    jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
      jasWeightedAggregate cw κ (jasVecChar P x - jasVecChar P y)

/-- **Weighted Fejér limit.**  Nonnegative weighted Fejér forms at `w` force nonnegativity of the
weighted zero sum of twisted local Euler densities at `w`. -/
theorem re_tsum_weighted_nonneg_of_fejer {cw : XiZeroCopy → ℂ} (hcw : Summable fun q => ‖cw q‖)
    {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes) (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    (hfej : ∀ K, 0 ≤ (jasWeightedFejerForm cw c P w K).re) :
    0 ≤ (∑' q : XiZeroCopy, cw q *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
        (w i)).re := by
  set Q : ℕ → ℂ := fun K => jasWeightedFejerForm cw c P w K with hQ
  have hs : ∀ (x y : ↥P → ℕ), Summable (fun q : XiZeroCopy =>
      jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
        (cw q * jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
          (jasVecChar P x - jasVecChar P y))) :=
    fun x y => summable_weighted_term hcw hc _ _
  have hQeq : ∀ K, Q K = ∑' q : XiZeroCopy, cw q *
      ∏ i : ↥P, ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        w i ^ a * conj (w i) ^ b *
          jasLocalCoeff (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
            ((a : ℤ) - b) := by
    intro K
    rw [hQ]
    simp only [jasWeightedFejerForm, jasWeightedAggregate]
    simp_rw [← tsum_mul_left]
    have hex : ∀ f : (↥P → ℕ) → (↥P → ℕ) → XiZeroCopy → ℂ,
        (∀ x y, Summable (f x y)) →
        ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K, ∑' q, f x y q =
          ∑' q, ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K, f x y q := by
      intro f hf
      rw [Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hf x y]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Summable.tsum_finsetSum fun y _ => hf x y]
    rw [hex _ hs]
    refine tsum_congr fun q => ?_
    rw [← sum_sum_fejer_jasDressedCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  set N : ℕ → ℝ := fun K => ((K : ℝ) + 1) ^ Fintype.card ↥P with hN
  have hNpos : ∀ K, 0 < N K := fun K => by positivity
  have hnn : ∀ K, 0 ≤ (((N K)⁻¹ : ℝ) * Q K : ℂ).re := fun K => by
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (inv_nonneg.mpr (hNpos K).le) (hfej K)
  have hrw : ∀ K, (((N K)⁻¹ : ℝ) * Q K : ℂ) = ∑' q : XiZeroCopy, cw q *
      ∏ i : ↥P, jasLocalFejer (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
        (w i) K := by
    intro K
    rw [hQeq, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    unfold jasLocalFejer
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hN]
    push_cast
    rw [inv_pow]
    ring
  have hlim : Tendsto (fun K => (((N K)⁻¹ : ℝ) * Q K : ℂ)) atTop
      (𝓝 (∑' q : XiZeroCopy, cw q *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (w i))) := by
    simp_rw [hrw]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun q : XiZeroCopy => ‖cw q‖ * ∏ i : ↥P, jasLocalBound c i)
      (hcw.mul_right _) (fun q => ?_) ?_
    · have h0 := (xi_divisor_support_re_mem_open_unit q.1).1
      have h1 := (xi_divisor_support_re_mem_open_unit q.1).2
      have hm := fun p : Nat.Primes => exp_neg_mul_log_lt_one hc p
      refine Tendsto.const_mul _ (tendsto_finsetProd _ fun i _ => ?_)
      exact tendsto_jasLocalFejer ((norm_jasHoloA_dressed_le (c := c) h0 i).trans_lt (hm i))
        ((norm_jasHoloB_dressed_le (c := c) h1 i).trans_lt (hm i)) (hw i)
    · filter_upwards with K q
      have h0 := (xi_divisor_support_re_mem_open_unit q.1).1
      have h1 := (xi_divisor_support_re_mem_open_unit q.1).2
      rw [norm_mul, norm_prod]
      gcongr with i _
      exact norm_jasLocalFejer_dressed_le hc h0 h1 i (hw i) K
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hlim) hnn

theorem re_tsum_weighted_nonneg_of_psd {cw : XiZeroCopy → ℂ} (hcw : Summable fun q => ‖cw q‖)
    {c : ℝ} (hc : 0 < c) (hpsd : JasWeightedPSD cw c) (P : Finset Nat.Primes) (w : ↥P → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) :
    0 ≤ (∑' q : XiZeroCopy, cw q *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
        (w i)).re :=
  re_tsum_weighted_nonneg_of_fejer hcw hc P w hw fun K =>
    hpsd _ (jasFejerBox P K) (jasFejerCoeff P w) (jasVecChar P) (jasVecChar_injective P).injOn

/-! ## Critical zeros with nonnegative weights give positivity -/

theorem jasHoloLocal_conj_eq {a w : ℂ} (hw : ‖w‖ = 1) :
    jasHoloLocal a (conj a) w = ((2 * ((1 - a * w)⁻¹).re - 1 : ℝ) : ℂ) := by
  have hwc : conj w = w⁻¹ := (inv_eq_conj_of_norm_eq_one hw).symm
  have h : (1 - conj a * conj w)⁻¹ = conj ((1 - a * w)⁻¹) := by
    rw [map_inv₀, map_sub, map_one, map_mul]
  unfold jasHoloLocal
  rw [h, Complex.add_conj]
  push_cast
  ring

theorem jasHoloLocal_conj_pos {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) :
    0 < 2 * ((1 - a * w)⁻¹).re - 1 := by
  have := half_lt_re_inv_one_sub (z := a * w) (by rw [norm_mul, hw, mul_one]; exact ha)
  linarith

theorem jasHoloB_sub_eq_conj_of_critical {q : ℂ} (hq : q.re = 1 / 2) (c : ℝ) (p : Nat.Primes) :
    jasHoloB (q - c) p = conj (jasHoloA (q + c) p) := by
  rw [jasHoloB, jasHoloA, ← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
      Complex.conj_ofReal, hq]
    ring
  · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
      Complex.conj_ofReal, hq]
    ring

/-- At a critical zero every sector density is a positive real. -/
theorem jasSectorDensity_eq_ofReal_pos_of_critical {q : ℂ} (hq : q.re = 1 / 2) {c : ℝ}
    (hc : 0 < c) (P : Finset Nat.Primes) (x : ↥P → UnitAddCircle) :
    ∃ r : ℝ, 0 < r ∧ jasSectorDensity q c P x = (r : ℂ) := by
  refine ⟨∏ i : ↥P, (2 * ((1 - jasHoloA (q + c) i * fourier 1 (x i))⁻¹).re - 1),
    Finset.prod_pos fun i _ => ?_, ?_⟩
  · exact jasHoloLocal_conj_pos (norm_jasHoloA_dressed_lt_one (by rw [hq]; linarith) i)
      (norm_fourier_unit 1 _)
  · unfold jasSectorDensity jasHoloCircle
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [jasHoloB_sub_eq_conj_of_critical hq c i, jasHoloLocal_conj_eq (norm_fourier_unit 1 _)]
    push_cast
    ring

/-- **Critical zeros with nonnegative weights give positivity.** -/
theorem jasWeightedPSD_of_critical {cw : XiZeroCopy → ℂ} (hcw : Summable fun q => ‖cw q‖)
    {c : ℝ} (hc : 0 < c) (hcrit : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2)
    (hreal : ∀ q, (cw q).im = 0) (hnn : ∀ q, 0 ≤ (cw q).re) : JasWeightedPSD cw c := by
  classical
  intro ι t cc n _
  set P : Finset Nat.Primes := t.biUnion (fun i => (n i).support) with hP
  have hn : ∀ i ∈ t, (n i).support ⊆ P := fun i hi p hp =>
    Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hs : ∀ i j, Summable (fun q : XiZeroCopy => cc i * conj (cc j) *
      (cw q * jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j))) :=
    fun i j => summable_weighted_term hcw hc _ _
  have hswap : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasWeightedAggregate cw c (n i - n j) =
      ∑' q : XiZeroCopy, ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        (cw q * jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j)) := by
    simp_rw [jasWeightedAggregate, ← tsum_mul_left]
    rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => hs i j]
  rw [hswap, Complex.re_tsum (summable_sum fun i _ => summable_sum fun j _ => hs i j)]
  refine tsum_nonneg fun q => ?_
  have h0 : 0 < (q.1 : ℂ).re + c := by rw [hcrit q]; linarith
  have h1 : 0 < 1 - (q.1 : ℂ).re + c := by rw [hcrit q]; linarith
  have hterm : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
      (cw q * jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j)) =
      cw q * ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hterm, gram_jasDressedCoeff_eq_integral h0 h1 P t cc n hn]
  set f : (↥P → UnitAddCircle) → ℂ := fun x => ∑ i ∈ t, cc i * jasCharBar P (n i) x with hf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_jasCharBar P _)
  have hcont : Continuous fun x => f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x :=
    (hfc.mul (Complex.continuous_conj.comp hfc)).mul (continuous_jasSectorDensity h0 h1 P)
  have hint := hcont.integrable_of_hasCompactSupport
    (μ := Measure.pi fun _ => jasCircleHaar) (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  have hIre : 0 ≤ (∫ x, f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x
      ∂Measure.pi fun _ => jasCircleHaar).re := by
    rw [← hre]
    refine integral_nonneg fun x => ?_
    obtain ⟨r, hr, hD⟩ := jasSectorDensity_eq_ofReal_pos_of_critical (hcrit q) hc P x
    show 0 ≤ (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x).re
    rw [hD, Complex.mul_conj]
    rw [show ((Complex.normSq (f x) : ℝ) : ℂ) * (r : ℂ) = ((Complex.normSq (f x) * r : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
    exact mul_nonneg (Complex.normSq_nonneg _) hr.le
  rw [Complex.mul_re, hreal q, zero_mul, sub_zero]
  exact mul_nonneg (hnn q) hIre

/-! ## Gaussian-localized weights -/

/-- The localization exponent `f_T(ρ) = (Re ρ − ½)² − (Im ρ − T)²`. -/
def jasLocExponent (T : ℝ) (q : XiZeroCopy) : ℝ :=
  ((q.1 : ℂ).re - 1 / 2) ^ 2 - ((q.1 : ℂ).im - T) ^ 2

/-- The Gaussian-localized lag weight `exp((s − ½ − iT)²/(2Δ²))/(s(1 − s))` as a function of `s`. -/
def jasLocWeightC (T Δ : ℝ) (s : ℂ) : ℂ :=
  cexp ((s - 1 / 2 - T * I) ^ 2 / (2 * Δ ^ 2)) * (1 / (s * (1 - s)))

/-- The Gaussian-localized lag weight of a zero copy. -/
def jasLocWeight (T Δ : ℝ) (q : XiZeroCopy) : ℂ := jasLocWeightC T Δ (q.1 : ℂ)

theorem re_jasLoc_arg (T Δ : ℝ) (s : ℂ) :
    ((s - 1 / 2 - T * I) ^ 2 / (2 * Δ ^ 2)).re =
      ((s.re - 1 / 2) ^ 2 - (s.im - T) ^ 2) / (2 * Δ ^ 2) := by
  have h2 : (2 * (Δ : ℂ) ^ 2) = ((2 * Δ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.div_ofReal_re]
  congr 1
  have hre : (s - 1 / 2 - T * I).re = s.re - 1 / 2 := by simp
  have him : (s - 1 / 2 - T * I).im = s.im - T := by simp
  rw [sq, Complex.mul_re, hre, him]
  ring

theorem norm_jasLocWeight (T Δ : ℝ) (q : XiZeroCopy) :
    ‖jasLocWeight T Δ q‖ = Real.exp (jasLocExponent T q / (2 * Δ ^ 2)) *
      ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [jasLocWeight, jasLocWeightC, norm_mul, Complex.norm_exp, re_jasLoc_arg]
  rfl

theorem sq_re_sub_half_lt (q : XiZeroCopy) : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := by
  have h := xi_divisor_support_re_mem_open_unit q.1
  nlinarith [h.1, h.2]

theorem jasLocExponent_le (T : ℝ) (q : XiZeroCopy) : jasLocExponent T q ≤ 1 / 4 := by
  unfold jasLocExponent
  nlinarith [sq_re_sub_half_lt q, sq_nonneg ((q.1 : ℂ).im - T)]

theorem summable_norm_jasLocWeight (T Δ : ℝ) : Summable fun q => ‖jasLocWeight T Δ q‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    (summable_inv_mul_one_sub.norm.mul_left (Real.exp ((1 / 4) / (2 * Δ ^ 2))))
  rw [norm_jasLocWeight]
  gcongr
  exact jasLocExponent_le T q

theorem jasLocWeight_of_critical {q : XiZeroCopy} (hq : (q.1 : ℂ).re = 1 / 2) (T Δ : ℝ) :
    jasLocWeight T Δ q = ((Real.exp (-((q.1 : ℂ).im - T) ^ 2 / (2 * Δ ^ 2)) /
      (1 / 4 + (q.1 : ℂ).im ^ 2) : ℝ) : ℂ) := by
  have h1 : (q.1 : ℂ) - 1 / 2 - T * I = (((q.1 : ℂ).im - T : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hq]
  have h2 : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 + (q.1 : ℂ).im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        Complex.ofReal_re, hq]
      ring
    · simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        Complex.ofReal_im, hq]
      ring
  rw [jasLocWeight, jasLocWeightC, h1, h2]
  have h3 : ((((q.1 : ℂ).im - T : ℝ) : ℂ) * I) ^ 2 / (2 * (Δ : ℂ) ^ 2) =
      ((-((q.1 : ℂ).im - T) ^ 2 / (2 * Δ ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [h3, ← Complex.ofReal_exp]
  push_cast
  ring

/-- **RH makes every localized aggregate positive semidefinite.** -/
theorem jasWeightedPSD_jasLocWeight_of_riemannHypothesis (hRH : RiemannHypothesis) {c : ℝ}
    (hc : 0 < c) (T Δ : ℝ) : JasWeightedPSD (jasLocWeight T Δ) c := by
  have hcrit := fun q => xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  refine jasWeightedPSD_of_critical (summable_norm_jasLocWeight T Δ) hc hcrit (fun q => ?_)
    (fun q => ?_)
  · rw [jasLocWeight_of_critical (hcrit q)]
    exact Complex.ofReal_im _
  · rw [jasLocWeight_of_critical (hcrit q), Complex.ofReal_re]
    positivity

/-! ## Reflection symmetry of a localized sector term -/

theorem jasLocWeightC_reflect (T Δ : ℝ) (s : ℂ) :
    jasLocWeightC T Δ (1 - conj s) = conj (jasLocWeightC T Δ s) := by
  unfold jasLocWeightC
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  · congr 1
    rw [map_div₀, map_pow, map_sub, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have h2 : conj (2 * (Δ : ℂ) ^ 2) = 2 * (Δ : ℂ) ^ 2 := by
      rw [map_mul, map_pow, Complex.conj_ofReal, map_ofNat]
    rw [h2]
    simp only [map_one, map_div₀, map_ofNat]
    ring
  · simp only [map_div₀, map_one, map_mul, map_sub]
    ring

theorem jasHoloA_reflect (s : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasHoloA (1 - conj s + c) p = conj (jasHoloB (s - c) p) := by
  rw [jasHoloA, jasHoloB, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_sub, map_one, Complex.conj_ofReal]
  ring

theorem jasHoloB_reflect (s : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasHoloB (1 - conj s - c) p = conj (jasHoloA (s + c) p) := by
  rw [jasHoloA, jasHoloB, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_add, Complex.conj_ofReal]
  ring

theorem jasHoloLocal_conj_conj (a b x : ℂ) :
    jasHoloLocal (conj b) (conj a) x = conj (jasHoloLocal a b x) := by
  unfold jasHoloLocal
  simp only [map_sub, map_add, map_inv₀, map_one, map_mul, Complex.conj_conj]
  ring

/-- The localized sector term at `s` on the torus `T^P`. -/
def jasLocTerm (T Δ c : ℝ) (P : Finset Nat.Primes) (x : ↥P → ℂ) (s : ℂ) : ℂ :=
  jasLocWeightC T Δ s * ∏ i : ↥P, jasHoloLocal (jasHoloA (s + c) i) (jasHoloB (s - c) i) (x i)

theorem jasLocTerm_reflect (T Δ c : ℝ) (P : Finset Nat.Primes) (x : ↥P → ℂ) (s : ℂ) :
    jasLocTerm T Δ c P x (1 - conj s) = conj (jasLocTerm T Δ c P x s) := by
  unfold jasLocTerm
  rw [jasLocWeightC_reflect, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [jasHoloA_reflect, jasHoloB_reflect, jasHoloLocal_conj_conj]

/-! ## Finiteness and the dominant zero -/

theorem finite_xiZeroCopy_im_near (γ₀ H : ℝ) :
    {q : XiZeroCopy | |(q.1 : ℂ).im - γ₀| < H}.Finite := by
  set M : ℝ := 1 + |γ₀| + |H| with hM
  have hMpos : 0 < M := by positivity
  have hε : (0 : ℝ) < 1 / M ^ 2 := by positivity
  have hfin := Filter.eventually_cofinite.mp
    ((summable_inv_mul_one_sub.norm.tendsto_cofinite_zero).eventually (gt_mem_nhds hε))
  refine hfin.subset fun q hq => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hq ⊢
  have hre := xi_divisor_support_re_mem_open_unit q.1
  have him : |(q.1 : ℂ).im| ≤ |γ₀| + |H| := by
    have h1 : |(q.1 : ℂ).im| ≤ |(q.1 : ℂ).im - γ₀| + |γ₀| := by
      have := abs_add_le ((q.1 : ℂ).im - γ₀) γ₀
      simpa using this
    linarith [le_abs_self H]
  have hn1 : ‖(q.1 : ℂ)‖ ≤ M := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [abs_of_pos hre.1]
    linarith [hre.2]
  have hn2 : ‖1 - (q.1 : ℂ)‖ ≤ M := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have : |(1 - (q.1 : ℂ)).re| ≤ 1 := by
      rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith [hre.1, hre.2]
    have h' : |(1 - (q.1 : ℂ)).im| = |(q.1 : ℂ).im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    rw [h']
    linarith
  have hq0 : (0 : ℝ) < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
  have hq1 : (0 : ℝ) < ‖1 - (q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q)
  rw [norm_div, norm_one, norm_mul]
  rw [one_div_le_one_div (by positivity) (by positivity)]
  calc ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ ≤ M * M := mul_le_mul hn1 hn2 hq1.le hMpos.le
    _ = M ^ 2 := by ring

/-- **A dominant zero.**  If some zero is off the line, there are a shift `T`, a zero `q₁` and a gap
`κ > 0` such that `q₁` maximizes the localization exponent, every maximizer has the height of `q₁`,
and every other zero lies at least `κ` below the maximum. -/
theorem exists_jasLoc_dominant {q₀ : XiZeroCopy} (h₀ : (q₀.1 : ℂ).re ≠ 1 / 2) :
    ∃ T : ℝ, ∃ q₁ : XiZeroCopy, ∃ κ : ℝ, 0 < κ ∧ 0 < jasLocExponent T q₁ ∧
      (∀ q, jasLocExponent T q ≤ jasLocExponent T q₁) ∧
      (∀ q, jasLocExponent T q = jasLocExponent T q₁ → (q.1 : ℂ).im = (q₁.1 : ℂ).im) ∧
      (∀ q, jasLocExponent T q ≠ jasLocExponent T q₁ →
        jasLocExponent T q ≤ jasLocExponent T q₁ - κ) := by
  classical
  set γ₀ := (q₀.1 : ℂ).im with hγ₀
  set δ₀ := (q₀.1 : ℂ).re - 1 / 2 with hδ₀def
  have hδ₀ : δ₀ ≠ 0 := sub_ne_zero.mpr h₀
  have hFfin := finite_xiZeroCopy_im_near γ₀ 2
  set F := hFfin.toFinset with hF
  have hmemF : ∀ q, q ∈ F ↔ |(q.1 : ℂ).im - γ₀| < 2 := fun q => by
    rw [hF, Set.Finite.mem_toFinset]; rfl
  set E : Set ℝ := ⋃ q ∈ F, ⋃ q' ∈ F, {ε : ℝ | (q.1 : ℂ).im ≠ (q'.1 : ℂ).im ∧
      jasLocExponent (γ₀ + ε) q = jasLocExponent (γ₀ + ε) q'} with hE
  have hEfin : E.Finite := by
    refine Set.Finite.biUnion F.finite_toSet fun q _ =>
      Set.Finite.biUnion F.finite_toSet fun q' _ => ?_
    refine Set.Subsingleton.finite fun ε₁ h₁ ε₂ h₂ => ?_
    obtain ⟨hne, he₁⟩ := h₁
    obtain ⟨-, he₂⟩ := h₂
    unfold jasLocExponent at he₁ he₂
    have hne' : (q.1 : ℂ).im - (q'.1 : ℂ).im ≠ 0 := sub_ne_zero.mpr hne
    have hkey : ((q.1 : ℂ).im - (q'.1 : ℂ).im) * (ε₁ - ε₂) = 0 := by
      linear_combination (he₁ - he₂) / 2
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hne'
    · linarith
  set m : ℝ := min 1 |δ₀| with hm
  have hmpos : 0 < m := lt_min one_pos (abs_pos.mpr hδ₀)
  obtain ⟨ε, ⟨hε0, hεm⟩, hεE⟩ := ((Set.Ioo_infinite hmpos).sdiff hEfin).nonempty
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεδ : ε < |δ₀| := lt_of_lt_of_le hεm (min_le_right _ _)
  set T := γ₀ + ε with hT
  have hout : ∀ q, q ∉ F → jasLocExponent T q < 0 := by
    intro q hq
    have hq' : 2 ≤ |(q.1 : ℂ).im - γ₀| := by
      by_contra h
      push Not at h
      exact hq ((hmemF q).mpr h)
    have h1 : 1 ≤ |(q.1 : ℂ).im - T| := by
      have h2 : |(q.1 : ℂ).im - γ₀| ≤ |(q.1 : ℂ).im - T| + |ε| := by
        have := abs_add_le ((q.1 : ℂ).im - T) ε
        rw [hT] at this ⊢
        have he : (q.1 : ℂ).im - (γ₀ + ε) + ε = (q.1 : ℂ).im - γ₀ := by ring
        rw [he] at this
        exact this
      rw [abs_of_pos hε0] at h2
      linarith
    have h2 : 1 ≤ ((q.1 : ℂ).im - T) ^ 2 := by
      nlinarith [abs_nonneg ((q.1 : ℂ).im - T), sq_abs ((q.1 : ℂ).im - T)]
    have h3 := sq_re_sub_half_lt q
    unfold jasLocExponent
    linarith
  have hq₀F : q₀ ∈ F := (hmemF q₀).mpr (by rw [hγ₀, sub_self, abs_zero]; norm_num)
  have hf₀ : 0 < jasLocExponent T q₀ := by
    unfold jasLocExponent
    rw [← hδ₀def, ← hγ₀, hT]
    have : ε ^ 2 < δ₀ ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg δ₀]) hεδ
      rwa [sq_abs] at this
    nlinarith
  obtain ⟨q₁, hq₁F, hmaxF⟩ := F.exists_max_image (jasLocExponent T) ⟨q₀, hq₀F⟩
  have hf₁ : 0 < jasLocExponent T q₁ := lt_of_lt_of_le hf₀ (hmaxF q₀ hq₀F)
  have hmax : ∀ q, jasLocExponent T q ≤ jasLocExponent T q₁ := by
    intro q
    by_cases hq : q ∈ F
    · exact hmaxF q hq
    · exact (hout q hq).le.trans hf₁.le
  have hheight : ∀ q, jasLocExponent T q = jasLocExponent T q₁ → (q.1 : ℂ).im = (q₁.1 : ℂ).im := by
    intro q hq
    have hqF : q ∈ F := by
      by_contra h
      have := hout q h
      linarith
    by_contra hne
    apply hεE
    simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨q, hqF, q₁, hq₁F, hne, hq⟩
  set Flow := F.filter (fun q => jasLocExponent T q ≠ jasLocExponent T q₁) with hFlow
  obtain ⟨κ, hκ, hκle⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 / 4 ∧
      ∀ q ∈ Flow, κ ≤ jasLocExponent T q₁ - jasLocExponent T q := by
    by_cases hne : Flow.Nonempty
    · obtain ⟨qm, hqm, hmin⟩ := Flow.exists_min_image
        (fun q => jasLocExponent T q₁ - jasLocExponent T q) hne
      have hqm' := (Finset.mem_filter.mp hqm).2
      have hpos : 0 < jasLocExponent T q₁ - jasLocExponent T qm := by
        have := hmax qm
        have : jasLocExponent T qm < jasLocExponent T q₁ := lt_of_le_of_ne this hqm'
        linarith
      exact ⟨min (3 / 4) (jasLocExponent T q₁ - jasLocExponent T qm), lt_min (by norm_num) hpos,
        min_le_left _ _, fun q hq => (min_le_right _ _).trans (hmin q hq)⟩
    · refine ⟨3 / 4, by norm_num, le_rfl, fun q hq => absurd ⟨q, hq⟩ hne⟩
  refine ⟨T, q₁, κ, hκ, hf₁, hmax, hheight, fun q hq => ?_⟩
  by_cases hqF : q ∈ F
  · have := hκle.2 q (Finset.mem_filter.mpr ⟨hqF, hq⟩)
    linarith
  · have h1 := hout q hqF
    have h2 : jasLocExponent T q < -(3 / 4) := by
      have hq' : 2 ≤ |(q.1 : ℂ).im - γ₀| := by
        by_contra h
        push Not at h
        exact hqF ((hmemF q).mpr h)
      have h3 : 1 ≤ |(q.1 : ℂ).im - T| := by
        have h4 : |(q.1 : ℂ).im - γ₀| ≤ |(q.1 : ℂ).im - T| + |ε| := by
          have := abs_add_le ((q.1 : ℂ).im - T) ε
          have he : (q.1 : ℂ).im - (γ₀ + ε) + ε = (q.1 : ℂ).im - γ₀ := by ring
          rw [hT, he] at this
          rw [hT]
          exact this
        rw [abs_of_pos hε0] at h4
        linarith
      have h4 : 1 ≤ ((q.1 : ℂ).im - T) ^ 2 := by
        nlinarith [abs_nonneg ((q.1 : ℂ).im - T), sq_abs ((q.1 : ℂ).im - T)]
      have h5 := sq_re_sub_half_lt q
      unfold jasLocExponent
      linarith
    linarith [hκle.1]

/-! ## A phase budget above `π` -/

theorem half_mul_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.arctan x := by
  have hs : Real.sin (Real.arctan x) ≤ Real.arctan x :=
    Real.sin_le (Real.arctan_nonneg.mpr hx0)
  rw [Real.sin_arctan] at hs
  have hsq : Real.sqrt (1 + x ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  calc x / 2 ≤ x / Real.sqrt (1 + x ^ 2) := div_le_div_of_nonneg_left hx0 hpos hsq
    _ ≤ _ := hs

theorem jasPhaseWidth_ge_of_offLine {q : XiZeroCopy} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (p : Nat.Primes) :
    |(q.1 : ℂ).re - 1 / 2| / 4 * (1 / (p : ℝ)) ≤
      jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) := by
  set u := (q.1 : ℂ).re - 1 / 2 with hu
  set L := Real.log (p : ℕ) with hL
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hp2
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hLpos : 0 < L := by linarith
  have hre := xi_divisor_support_re_mem_open_unit q.1
  have hr1 : jasR1 ((q.1 : ℂ) + c) p = Real.exp (-(1 / 2 + c) * L) * Real.exp (-(u * L)) := by
    rw [jasR1_dressed, ← Real.exp_add]; congr 1; rw [hu]; ring
  have hr2 : jasR2 ((q.1 : ℂ) - c) p = Real.exp (-(1 / 2 + c) * L) * Real.exp (u * L) := by
    rw [jasR2_dressed, ← Real.exp_add]; congr 1; rw [hu]; ring
  set r₁ := jasR1 ((q.1 : ℂ) + c) p
  set r₂ := jasR2 ((q.1 : ℂ) - c) p
  have hr₁0 : 0 < r₁ := Real.exp_pos _
  have hr₂0 : 0 < r₂ := Real.exp_pos _
  have hr₁1 : r₁ < 1 := by
    show jasR1 ((q.1 : ℂ) + c) p < 1
    rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hr₂1 : r₂ < 1 := by
    show jasR2 ((q.1 : ℂ) - c) p < 1
    rw [jasR2_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  -- the gap |r₁ − r₂|
  have hfac : Real.exp (-L) ≤ Real.exp (-(1 / 2 + c) * L) := by
    rw [Real.exp_le_exp]; nlinarith
  have hexpL : Real.exp (-L) = 1 / (p : ℝ) := by
    rw [Real.exp_neg, hL, Real.exp_log (by linarith)]; ring
  have hsinh : |u| / 2 ≤ |Real.exp (u * L) - Real.exp (-(u * L))| := by
    have hδL : |u| * L ≤ Real.exp (|u| * L) - 1 := by
      linarith [Real.add_one_le_exp (|u| * L)]
    have hlow : |u| / 2 ≤ |u| * L := by nlinarith [abs_nonneg u]
    have hm : Real.exp (-(|u| * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg u])
    rcases le_total 0 u with hu0 | hu0
    · rw [abs_of_nonneg hu0] at hδL hlow hm ⊢
      rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr (show -(u * L) ≤ u * L by nlinarith)])]
      linarith
    · rw [abs_of_nonpos hu0] at hδL hlow hm ⊢
      have he : Real.exp (u * L) - Real.exp (-(u * L)) =
          -(Real.exp (-u * L) - Real.exp (-(-u * L))) := by ring_nf
      rw [he, abs_neg, abs_of_nonneg (by
        linarith [Real.exp_le_exp.mpr (show -(-u * L) ≤ -u * L by nlinarith)])]
      have : -(-u * L) = -(-u * L) := rfl
      linarith
  have hgap : |u| / 2 * (1 / (p : ℝ)) ≤ |r₁ - r₂| := by
    have hdiff : r₁ - r₂ = Real.exp (-(1 / 2 + c) * L) *
        (Real.exp (-(u * L)) - Real.exp (u * L)) := by rw [hr1, hr2]; ring
    have habs : |r₁ - r₂| = Real.exp (-(1 / 2 + c) * L) *
        |Real.exp (u * L) - Real.exp (-(u * L))| := by
      rw [hdiff, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_sub_comm (Real.exp (-(u * L))) (Real.exp (u * L))]
    rw [habs, ← hexpL]
    nlinarith [Real.exp_pos (-L), abs_nonneg u, abs_nonneg (Real.exp (u * L) - Real.exp (-(u * L)))]
  -- the width
  have hS : Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact mul_le_one₀ (by nlinarith) (by nlinarith) (by nlinarith)
  have hSpos : 0 < Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    apply Real.sqrt_pos.mpr; apply mul_pos <;> nlinarith
  have hratio : |r₁ - r₂| ≤ |r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    rw [le_div_iff₀ hSpos]; nlinarith [abs_nonneg (r₁ - r₂)]
  have hd1 : |r₁ - r₂| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hW : |r₁ - r₂| / 2 ≤ jasPhaseWidth r₁ r₂ := by
    unfold jasPhaseWidth
    exact (half_mul_le_arctan (abs_nonneg _) hd1).trans
      (Real.arctan_le_arctan_iff.mpr hratio)
  calc |u| / 4 * (1 / (p : ℝ)) = (|u| / 2 * (1 / (p : ℝ))) / 2 := by ring
    _ ≤ |r₁ - r₂| / 2 := by linarith
    _ ≤ _ := hW

theorem exists_finset_jasPhaseWidth_gt_pi {q : XiZeroCopy} (hq : (q.1 : ℂ).re ≠ 1 / 2) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) :
    ∃ P : Finset Nat.Primes, Real.pi <
      ∑ p ∈ P, jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) := by
  have hδ : 0 < |(q.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq)
  by_contra hcon
  push Not at hcon
  have hsum : Summable fun p : Nat.Primes =>
      jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) :=
    summable_of_sum_le (fun p => jasPhaseWidth_nonneg _ _) hcon
  have h1 : Summable fun p : Nat.Primes => |(q.1 : ℂ).re - 1 / 2| / 4 * (1 / (p : ℝ)) :=
    hsum.of_nonneg_of_le (fun p => by positivity) fun p => jasPhaseWidth_ge_of_offLine hc hc1 p
  have h2 := h1.mul_left (4 / |(q.1 : ℂ).re - 1 / 2|)
  apply Nat.Primes.not_summable_one_div
  refine h2.congr fun p => ?_
  have hd : |(q.1 : ℂ).re - 1 / 2| ≠ 0 := hδ.ne'
  rw [← mul_assoc, div_mul_div_comm, mul_comm (4 : ℝ), div_self (mul_ne_zero hd (by norm_num)),
    one_mul]

/-! ## Every phase is reachable once the budget exceeds `π` -/

theorem jasRotSlope_neg (r₁ r₂ θ : ℝ) : jasRotSlope r₁ r₂ (-θ) = -jasRotSlope r₁ r₂ θ := by
  unfold jasRotSlope jasRotDen
  rw [Real.sin_neg, Real.cos_neg]
  ring

/-- The extremal angle at which the slope equals `|r₁ − r₂|/√((1 − r₁²)(1 − r₂²))`. -/
def jasExtremalAngle (r₁ r₂ : ℝ) : ℝ :=
  if r₂ ≤ r₁ then Real.arccos ((r₁ + r₂) / (1 + r₁ * r₂))
  else -Real.arccos ((r₁ + r₂) / (1 + r₁ * r₂))

theorem arctan_jasRotSlope_extremal {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂)
    (h₂' : r₂ < 1) :
    Real.arctan (jasRotSlope r₁ r₂ (jasExtremalAngle r₁ r₂)) = jasPhaseWidth r₁ r₂ := by
  unfold jasExtremalAngle jasPhaseWidth
  split_ifs with h
  · rw [jasRotSlope_extremal h₁ h₁' h₂ h₂', abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [jasRotSlope_neg, jasRotSlope_extremal h₁ h₁' h₂ h₂',
      abs_of_neg (by linarith : r₁ - r₂ < 0)]
    congr 1
    ring

theorem exists_sum_arg_jasRotLocal_eq {ι : Type*} (P : Finset ι) {r₁ r₂ : ι → ℝ}
    (h₁ : ∀ i, 0 ≤ r₁ i) (h₁' : ∀ i, r₁ i < 1) (h₂ : ∀ i, 0 ≤ r₂ i) (h₂' : ∀ i, r₂ i < 1)
    {ψ : ℝ} (hψ : |ψ| ≤ ∑ i ∈ P, jasPhaseWidth (r₁ i) (r₂ i)) :
    ∃ θ : ι → ℝ, ∑ i ∈ P, (jasRotLocal (r₁ i) (r₂ i) (θ i)).arg = ψ := by
  set Ψ : ℝ → ℝ := fun t => ∑ i ∈ P,
    Real.arctan (jasRotSlope (r₁ i) (r₂ i) (t * jasExtremalAngle (r₁ i) (r₂ i))) with hΨ
  have hcont : Continuous Ψ :=
    continuous_finsetSum _ fun i _ => Real.continuous_arctan.comp
      ((continuous_jasRotSlope (h₁ i) (h₁' i) (h₂ i) (h₂' i)).comp
        (continuous_id.mul continuous_const))
  have hp1 : Ψ 1 = ∑ i ∈ P, jasPhaseWidth (r₁ i) (r₂ i) := by
    simp only [hΨ, one_mul]
    exact Finset.sum_congr rfl fun i _ =>
      arctan_jasRotSlope_extremal (h₁ i) (h₁' i) (h₂ i) (h₂' i)
  have hm1 : Ψ (-1) = -∑ i ∈ P, jasPhaseWidth (r₁ i) (r₂ i) := by
    simp only [hΨ, neg_one_mul, jasRotSlope_neg, Real.arctan_neg]
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      arctan_jasRotSlope_extremal (h₁ i) (h₁' i) (h₂ i) (h₂' i)
  have hmem : ψ ∈ Set.Icc (Ψ (-1)) (Ψ 1) :=
    ⟨by rw [hm1]; linarith [neg_abs_le ψ], by rw [hp1]; linarith [le_abs_self ψ]⟩
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont.continuousOn hmem
  refine ⟨fun i => t * jasExtremalAngle (r₁ i) (r₂ i), ?_⟩
  rw [← ht]
  exact Finset.sum_congr rfl fun i _ => arg_jasRotLocal (h₁ i) (h₁' i) (h₂ i) (h₂' i) _

theorem norm_jasRotLocal_ge {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂)
    (h₂' : r₂ < 1) (θ : ℝ) :
    (1 - r₁ * r₂) / ((1 + r₁) * (1 + r₂)) ≤ ‖jasRotLocal r₁ r₂ θ‖ := by
  unfold jasRotLocal
  have hn1 : ‖1 - (r₁ : ℂ) * cexp ((θ : ℂ) * I)‖ ≤ 1 + r₁ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₁]
  have hn2 : ‖1 - (r₂ : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)‖ ≤ 1 + r₂ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₂]
  have hne : (1 - (r₁ : ℂ) * cexp ((θ : ℂ) * I)) *
      (1 - (r₂ : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)) ≠ 0 := by
    rw [jasRotLocal_den_eq]; exact jasRotDenC_ne_zero h₁ h₁' h₂ h₂' θ
  have hpos : 0 < ‖(1 - (r₁ : ℂ) * cexp ((θ : ℂ) * I)) *
      (1 - (r₂ : ℂ) * cexp (((-θ : ℝ) : ℂ) * I))‖ := norm_pos_iff.mpr hne
  have hnum : (0 : ℝ) < 1 - r₁ * r₂ := by nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hnum.le]
  rw [norm_mul] at hpos ⊢
  apply div_le_div_of_nonneg_left hnum.le hpos
  exact mul_le_mul hn1 hn2 (norm_nonneg _) (by linarith)

theorem norm_prod_jasHoloLocal_le {c : ℝ} (hc : 0 < c) (q : XiZeroCopy) (P : Finset Nat.Primes)
    (x : ↥P → ℂ) (hx : ∀ i, ‖x i‖ = 1) :
    ‖∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i) (x i)‖ ≤
      ∏ i : ↥P, jasCircleBound c i := by
  have h0 := (xi_divisor_support_re_mem_open_unit q.1).1
  have h1 := (xi_divisor_support_re_mem_open_unit q.1).2
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  have hm := exp_neg_mul_log_lt_one hc i
  have hA := norm_jasHoloA_dressed_le (c := c) h0 i
  have hB := norm_jasHoloB_dressed_le (c := c) h1 i
  refine (norm_jasHoloLocal_le_of_norm_eq_one (hA.trans_lt hm) (hB.trans_lt hm) (hx i)).trans ?_
  have hpos : 0 < 1 - Real.exp (-c * Real.log i) := by linarith
  have e1 : 1 / (1 - ‖jasHoloA ((q.1 : ℂ) + c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos (by linarith)
  have e2 : 1 / (1 - ‖jasHoloB ((q.1 : ℂ) - c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos (by linarith)
  unfold jasCircleBound
  linarith

/-! ## The chain-free converse -/

/-- **Localized converse.**  If for some `c ∈ (0, ½]` every Gaussian-localized dressed aggregate is
positive semidefinite, then the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_forall_jasWeightedPSD_jasLocWeight {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 / 2) (h : ∀ T Δ : ℝ, 0 < Δ → JasWeightedPSD (jasLocWeight T Δ) c) :
    RiemannHypothesis := by
  classical
  refine riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase fun q₀ => ?_
  by_contra h₀
  obtain ⟨T, q₁, κ, hκ, hf₁, hmax, hheight, hgap⟩ := exists_jasLoc_dominant h₀
  set f₁ := jasLocExponent T q₁ with hf₁def
  have hq₁ : (q₁.1 : ℂ).re ≠ 1 / 2 := by
    intro hre
    have : f₁ = -((q₁.1 : ℂ).im - T) ^ 2 := by
      rw [hf₁def, jasLocExponent, hre]; ring
    nlinarith [sq_nonneg ((q₁.1 : ℂ).im - T)]
  obtain ⟨P, hP⟩ := exists_finset_jasPhaseWidth_gt_pi hq₁ hc hc1
  have hα0 : 0 < (q₁.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q₁.1).1]
  have hα1 : 0 < 1 - (q₁.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q₁.1).2]
  set r₁ : Nat.Primes → ℝ := fun p => jasR1 ((q₁.1 : ℂ) + c) p with hr₁
  set r₂ : Nat.Primes → ℝ := fun p => jasR2 ((q₁.1 : ℂ) - c) p with hr₂
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ r₂ p := fun p => (Real.exp_pos _).le
  have hr₁1 : ∀ p, r₁ p < 1 := fun p => by
    simp only [hr₁]; rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hr₂1 : ∀ p, r₂ p < 1 := fun p => by
    simp only [hr₂]; rw [jasR2_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  -- constants
  set mP : ℝ := ∏ p ∈ P, (1 - r₁ p * r₂ p) / ((1 + r₁ p) * (1 + r₂ p)) with hmP
  have hmPpos : 0 < mP := Finset.prod_pos fun p _ => by
    have := hr₁1 p; have := hr₂1 p; have := hr₁0 p; have := hr₂0 p
    apply div_pos <;> nlinarith
  set CP : ℝ := ∏ i : ↥P, jasCircleBound c i with hCP
  have hCP0 : 0 ≤ CP := Finset.prod_nonneg fun i _ => by
    unfold jasCircleBound
    have := exp_neg_mul_log_lt_one hc i
    have : 0 < (1 - Real.exp (-c * Real.log i))⁻¹ := inv_pos.mpr (by linarith)
    linarith
  set S : ℝ := ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  set w₁ : ℝ := ‖1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))‖ with hw₁
  have hw₁pos : 0 < w₁ := by
    rw [hw₁, norm_div, norm_one, norm_mul]
    exact one_div_pos.mpr (mul_pos (norm_pos_iff.mpr (xiZeroCopy_ne_zero q₁))
      (norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q₁)))
  -- choice of `Δ`
  set ε₀ : ℝ := w₁ * mP / (2 * (CP * S + 1)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  set L : ℝ := max 1 (-Real.log ε₀) + 1 with hL
  have hLpos : 0 < L := by have := le_max_left 1 (-Real.log ε₀); linarith
  set Δ : ℝ := Real.sqrt (κ / (2 * L)) with hΔ
  have hΔpos : 0 < Δ := Real.sqrt_pos.mpr (by positivity)
  have hΔsq : 2 * Δ ^ 2 = κ / L := by
    rw [hΔ, Real.sq_sqrt (by positivity)]; field_simp
  have hexpκ : Real.exp (-κ / (2 * Δ ^ 2)) < ε₀ := by
    rw [hΔsq, show -κ / (κ / L) = -L by field_simp]
    have h1 : -L < Real.log ε₀ := by
      have := le_max_right 1 (-Real.log ε₀); linarith
    calc Real.exp (-L) < Real.exp (Real.log ε₀) := Real.exp_lt_exp.mpr h1
      _ = ε₀ := Real.exp_log hε₀pos
  -- the twisted point
  set φ := (jasLocWeight T Δ q₁).arg with hφ
  set ψ : ℝ := if 0 ≤ φ then Real.pi - φ else -Real.pi - φ with hψ
  have hφ1 := Complex.neg_pi_lt_arg (jasLocWeight T Δ q₁)
  have hφ2 := Complex.arg_le_pi (jasLocWeight T Δ q₁)
  have hψabs : |ψ| ≤ Real.pi := by
    rw [hψ]; split_ifs with h0 <;> rw [abs_le] <;> constructor <;> linarith
  have hφψ : cexp (((φ + ψ : ℝ) : ℂ) * I) = -1 := by
    rw [hψ]
    split_ifs with h0
    · rw [show φ + (Real.pi - φ) = Real.pi by ring, Complex.exp_pi_mul_I]
    · rw [show φ + (-Real.pi - φ) = -Real.pi by ring, Complex.ofReal_neg, neg_mul,
        Complex.exp_neg_pi_mul_I]
  obtain ⟨θ, hθ⟩ := exists_sum_arg_jasRotLocal_eq P hr₁0 hr₁1 hr₂0 hr₂1
    (hψabs.trans hP.le)
  set x : ↥P → ℂ := fun i => cexp ((θ i : ℂ) * I) * jasKroneckerPoint ((q₁.1 : ℂ) + c) i with hx
  have hxn : ∀ i, ‖x i‖ = 1 := fun i => by
    simp only [hx]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_jasKroneckerPoint, mul_one]
  have hnn := re_tsum_weighted_nonneg_of_psd (summable_norm_jasLocWeight T Δ) hc
    (h T Δ hΔpos) P x hxn
  -- the terms
  set a : XiZeroCopy → ℂ := fun q => jasLocTerm T Δ c P x (q.1 : ℂ) with ha
  have hterm : ∀ q, jasLocWeight T Δ q *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i) (x i) =
        a q := fun q => rfl
  simp_rw [hterm] at hnn
  -- the dominant term
  have hprod₁ : ∏ i : ↥P, jasHoloLocal (jasHoloA ((q₁.1 : ℂ) + c) i)
      (jasHoloB ((q₁.1 : ℂ) - c) i) (x i) = ∏ p ∈ P, jasRotLocal (r₁ p) (r₂ p) (θ p) := by
    rw [← Finset.prod_coe_sort P]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact jasHoloLocal_twisted_eq_jasRotLocal (q₁.1 : ℂ) c (θ i) i (hr₁1 i) (hr₂1 i)
  set Pr₁ := ∏ p ∈ P, jasRotLocal (r₁ p) (r₂ p) (θ p) with hPr₁
  set nP : ℝ := ∏ p ∈ P, ‖jasRotLocal (r₁ p) (r₂ p) (θ p)‖ with hnP
  have hPr₁ge : mP ≤ nP := by
    rw [hnP]
    exact Finset.prod_le_prod (fun p _ => by
      have := hr₁1 p; have := hr₂1 p; have := hr₁0 p; have := hr₂0 p
      apply div_nonneg <;> nlinarith) fun p _ =>
      norm_jasRotLocal_ge (hr₁0 p) (hr₁1 p) (hr₂0 p) (hr₂1 p) (θ p)
  have ha₁ : (a q₁).re = -(‖jasLocWeight T Δ q₁‖ * nP) := by
    have h1 : a q₁ = jasLocWeight T Δ q₁ * Pr₁ := by
      show jasLocWeight T Δ q₁ * _ = _
      rw [hprod₁]
    have h2 : Pr₁ = ((nP : ℝ) : ℂ) * cexp ((ψ : ℂ) * I) := by
      rw [hPr₁, prod_eq_prod_norm_mul_exp_sum_arg, hθ]
    have h3 : jasLocWeight T Δ q₁ = (‖jasLocWeight T Δ q₁‖ : ℂ) * cexp ((φ : ℂ) * I) :=
      (Complex.norm_mul_exp_arg_mul_I _).symm
    rw [h1, h2]
    conv_lhs => rw [h3]
    have h4 : (‖jasLocWeight T Δ q₁‖ : ℂ) * cexp ((φ : ℂ) * I) *
        (((nP : ℝ) : ℂ) * cexp ((ψ : ℂ) * I)) =
        ((‖jasLocWeight T Δ q₁‖ * nP : ℝ) : ℂ) * cexp (((φ + ψ : ℝ) : ℂ) * I) := by
      rw [show (((φ + ψ : ℝ) : ℂ) * I) = (φ : ℂ) * I + (ψ : ℂ) * I by push_cast; ring,
        Complex.exp_add]
      push_cast
      ring
    rw [h4, hφψ, mul_neg_one, Complex.neg_re, Complex.ofReal_re]
  have hnorm₁ : ‖jasLocWeight T Δ q₁‖ = Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ := norm_jasLocWeight T Δ q₁
  -- maximizers have the same real part as the dominant term
  have hsame : ∀ q, jasLocExponent T q = f₁ → (a q).re = (a q₁).re := by
    intro q hq
    have him := hheight q hq
    have hsq : ((q.1 : ℂ).re - 1 / 2) ^ 2 = ((q₁.1 : ℂ).re - 1 / 2) ^ 2 := by
      have := hq
      rw [hf₁def] at this
      unfold jasLocExponent at this
      rw [him] at this
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · have : (q.1 : ℂ) = (q₁.1 : ℂ) := Complex.ext (by linarith) him
      show (jasLocTerm T Δ c P x (q.1 : ℂ)).re = (jasLocTerm T Δ c P x (q₁.1 : ℂ)).re
      rw [this]
    · have : (q.1 : ℂ) = 1 - conj (q₁.1 : ℂ) := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
        · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; linarith
      show (jasLocTerm T Δ c P x (q.1 : ℂ)).re = (jasLocTerm T Δ c P x (q₁.1 : ℂ)).re
      rw [this, jasLocTerm_reflect, Complex.conj_re]
  -- bound for the other terms
  have hother : ∀ q, jasLocExponent T q ≠ f₁ →
      ‖a q‖ ≤ Real.exp ((f₁ - κ) / (2 * Δ ^ 2)) *
        (‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * CP) := by
    intro q hq
    show ‖jasLocWeight T Δ q * _‖ ≤ _
    rw [norm_mul, norm_jasLocWeight, mul_assoc]
    gcongr
    · exact hgap q hq
    · exact norm_prod_jasHoloLocal_le hc q P x hxn
  -- summability
  have hsa : Summable fun q => ‖a q‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      ((summable_norm_jasLocWeight T Δ).mul_right CP)
    show ‖jasLocWeight T Δ q * _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_prod_jasHoloLocal_le hc q P x hxn) (norm_nonneg _)
  have hsare : Summable fun q => (a q).re :=
    Summable.of_norm_bounded hsa fun q => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  set B : XiZeroCopy → ℝ := fun q => Real.exp ((f₁ - κ) / (2 * Δ ^ 2)) *
    (‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * CP) with hB
  have hBs : Summable B := (summable_inv_mul_one_sub.norm.mul_right CP).mul_left _
  have hB0 : ∀ q, 0 ≤ B q := fun q => by positivity
  have hrest : ∑' q, (if q = q₁ then 0 else (a q).re) ≤ ∑' q, B q := by
    refine Summable.tsum_le_tsum (fun q => ?_) ?_ hBs
    · split_ifs with hq
      · exact hB0 q
      · by_cases hf : jasLocExponent T q = f₁
        · rw [hsame q hf, ha₁]
          have : 0 ≤ ‖jasLocWeight T Δ q₁‖ * nP := by positivity
          linarith [hB0 q]
        · exact (Complex.re_le_norm _).trans (hother q hf)
    · refine Summable.of_norm_bounded hsa fun q => ?_
      split_ifs
      · simp
      · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hBsum : ∑' q, B q = Real.exp ((f₁ - κ) / (2 * Δ ^ 2)) * (S * CP) := by
    rw [hB, tsum_mul_left, tsum_mul_right]
  -- assemble
  have hre := Complex.re_tsum (hsa.of_norm)
  rw [hre, hsare.tsum_eq_add_tsum_ite q₁] at hnn
  have hsplit : Real.exp ((f₁ - κ) / (2 * Δ ^ 2)) =
      Real.exp (f₁ / (2 * Δ ^ 2)) * Real.exp (-κ / (2 * Δ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : 0 < Real.exp (f₁ / (2 * Δ ^ 2)) := Real.exp_pos _
  have hkey : Real.exp (-κ / (2 * Δ ^ 2)) * (S * CP) < w₁ * mP := by
    have h1 : Real.exp (-κ / (2 * Δ ^ 2)) * (S * CP) ≤ ε₀ * (CP * S + 1) := by
      have hSC : 0 ≤ S * CP := mul_nonneg hS0 hCP0
      calc Real.exp (-κ / (2 * Δ ^ 2)) * (S * CP) ≤ ε₀ * (S * CP) :=
            mul_le_mul_of_nonneg_right hexpκ.le hSC
        _ ≤ ε₀ * (CP * S + 1) := by
            apply mul_le_mul_of_nonneg_left _ hε₀pos.le
            rw [mul_comm S CP]; linarith
    have h2 : ε₀ * (CP * S + 1) = w₁ * mP / 2 := by
      rw [hε₀]; field_simp
    have h3 : w₁ * mP / 2 < w₁ * mP := by have := mul_pos hw₁pos hmPpos; linarith
    linarith
  have hfinal : (a q₁).re + ∑' q, (if q = q₁ then 0 else (a q).re) < 0 := by
    rw [ha₁, hnorm₁]
    have hlow : Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ * mP ≤
        Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ * nP := by
      gcongr
    have hup : ∑' q, (if q = q₁ then 0 else (a q).re) ≤
        Real.exp (f₁ / (2 * Δ ^ 2)) * (Real.exp (-κ / (2 * Δ ^ 2)) * (S * CP)) := by
      rw [← mul_assoc, ← hsplit, ← hBsum]; exact hrest
    have : Real.exp (f₁ / (2 * Δ ^ 2)) * (Real.exp (-κ / (2 * Δ ^ 2)) * (S * CP)) <
        Real.exp (f₁ / (2 * Δ ^ 2)) * (w₁ * mP) := mul_lt_mul_of_pos_left hkey hE
    have e1 : Real.exp (f₁ / (2 * Δ ^ 2)) * (w₁ * mP) = Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ * mP := by
      ring
    have e2 : Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ * nP =
        Real.exp (f₁ / (2 * Δ ^ 2)) * w₁ * nP := rfl
    linarith
  linarith

/-- **Chain-free localized criterion.**  For every `c ∈ (0, ½]`, the Riemann Hypothesis holds if
and only if every Gaussian-localized dressed aggregate is positive semidefinite at `σ = ½ + c`. -/
theorem riemannHypothesis_iff_forall_jasWeightedPSD_jasLocWeight {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 / 2) :
    RiemannHypothesis ↔ ∀ T Δ : ℝ, 0 < Δ → JasWeightedPSD (jasLocWeight T Δ) c :=
  ⟨fun hRH T Δ _ => jasWeightedPSD_jasLocWeight_of_riemannHypothesis hRH hc T Δ,
    riemannHypothesis_of_forall_jasWeightedPSD_jasLocWeight hc hc1⟩

end

end RHTower
