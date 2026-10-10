import GaloisForLFunctions.RHTower.JointAncestryPhaseBudgetPositivity
import GaloisForLFunctions.RHTower.JointAncestryUndressedPositivity

/-!
# The pointwise criterion for dressed positivity

For `c > 0` the `σ`-dressed aggregate (`σ = 1/2 + c`) is positive semidefinite on rational characters
if and only if, for every finite prime set `P` and every point `w` of the torus `T^P`,

`0 ≤ Re Σ_ρ (1/(ρ(1-ρ))) ∏_{p ∈ P} ℓ_p^ρ(w_p)`,

where `ℓ_p^ρ(w) = (1 - A w)⁻¹ + (1 - B w̄)⁻¹ - 1` with `A = p^{-(ρ+c)}`, `B = p^{-(1-ρ+c)}`.  Each
factor is the local Euler factor `(1 - AB)/((1 - A w)(1 - B w̄))`, so the criterion asks for pointwise
nonnegativity of the zero sum of twisted partial products `L_P(σ+ρ-½, w) L_P(σ-ρ+½, w̄)/ζ_P(2σ)`.

* Necessity uses Fejér test vectors `Σ_{x ∈ [0,K]^P} w^x χ_x`: their quadratic form factors over the
  primes into Fejér means of the local coefficients, which converge to the local densities.
* Sufficiency uses the single-zero Gram identity and an exchange of the zero sum with the torus
  integral.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Fejér means on `ℤ` -/

/-- Number of pairs in `[0,K]²` with difference `k`. -/
def jasFejerCount (K : ℕ) (k : ℤ) : ℕ :=
  ((Finset.range (K + 1) ×ˢ Finset.range (K + 1)).filter
    (fun ab : ℕ × ℕ => (ab.1 : ℤ) - ab.2 = k)).card

theorem jasFejerCount_le (K : ℕ) (k : ℤ) : jasFejerCount K k ≤ K + 1 := by
  unfold jasFejerCount
  calc _ ≤ (Finset.range (K + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun ab => ab.2) ?_ ?_
        · intro ab hab
          simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
            Set.mem_setOf_eq] at hab
          simp only [Finset.coe_range, Set.mem_Iio]
          exact hab.1.2
        · intro ab hab ab' hab' h
          simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
            Set.mem_setOf_eq] at hab hab'
          simp only at h
          have h1 : ab.1 = ab'.1 := by omega
          exact Prod.ext h1 h
    _ = K + 1 := Finset.card_range _

theorem le_jasFejerCount (K : ℕ) (k : ℤ) : K + 1 - k.natAbs ≤ jasFejerCount K k := by
  unfold jasFejerCount
  rw [← Finset.card_range (K + 1 - k.natAbs)]
  refine Finset.card_le_card_of_injOn (fun j => (j + k.toNat, j + (-k).toNat)) ?_ ?_
  · intro j hj
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    push_cast
    omega
  · intro j _ j' _ h
    simp only [Prod.mk.injEq] at h
    omega

theorem sum_range_sum_range_sub (K : ℕ) (F : ℤ → ℂ) :
    ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1), F ((a : ℤ) - b) =
      ∑' k : ℤ, (jasFejerCount K k : ℂ) * F k := by
  have hprod := Finset.sum_product' (Finset.range (K + 1)) (Finset.range (K + 1))
    (fun a b : ℕ => F ((a : ℤ) - b))
  rw [← hprod, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-(K : ℤ)) K)
      (g := fun ab : ℕ × ℕ => (ab.1 : ℤ) - ab.2) ?_]
  · rw [tsum_eq_sum (s := Finset.Icc (-(K : ℤ)) K) ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl (fun ab hab => by rw [(Finset.mem_filter.mp hab).2]),
        Finset.sum_const, nsmul_eq_mul]
      rfl
    · intro k hk
      rw [jasFejerCount, Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
      rw [Finset.filter_eq_empty_iff]
      intro ab hab
      simp only [Finset.mem_product, Finset.mem_range] at hab
      simp only [Finset.mem_Icc, not_and_or, not_le] at hk
      omega
  · intro ab hab
    simp only [Finset.mem_product, Finset.mem_range] at hab
    simp only [Finset.mem_Icc]
    omega

theorem tendsto_jasFejerCount_div (k : ℤ) :
    Tendsto (fun K : ℕ => (jasFejerCount K k : ℝ) / ((K : ℝ) + 1)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun K : ℕ => 1 - (k.natAbs : ℝ) / ((K : ℝ) + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun K : ℕ => (k.natAbs : ℝ) / ((K : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using h0.const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop k.natAbs] with K hK
    have hK1 : (0 : ℝ) < K + 1 := by positivity
    have hle : ((K + 1 - k.natAbs : ℕ) : ℝ) ≤ jasFejerCount K k := by
      exact_mod_cast le_jasFejerCount K k
    have hc : ((K + 1 - k.natAbs : ℕ) : ℝ) = (K : ℝ) + 1 - k.natAbs := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc] at hle
    rw [le_div_iff₀ hK1, sub_mul, div_mul_cancel₀ _ hK1.ne', one_mul]
    linarith
  · filter_upwards with K
    rw [div_le_one (by positivity)]
    exact_mod_cast jasFejerCount_le K k

theorem jasFejer_term_eq (K : ℕ) (k : ℤ) (z : ℂ) :
    ((K : ℂ) + 1)⁻¹ * ((jasFejerCount K k : ℂ) * z) =
      (((jasFejerCount K k : ℝ) / ((K : ℝ) + 1) : ℝ) : ℂ) * z := by
  push_cast
  ring

/-- **Fejér means of an absolutely summable sequence converge to its sum.** -/
theorem tendsto_jasFejerMean {F : ℤ → ℂ} (hF : Summable F) :
    Tendsto (fun K : ℕ => ((K : ℂ) + 1)⁻¹ *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1), F ((a : ℤ) - b))
      atTop (𝓝 (∑' k, F k)) := by
  simp_rw [sum_range_sum_range_sub, ← tsum_mul_left, jasFejer_term_eq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖F k‖) hF.norm
    (fun k => ?_) ?_
  · have h := ((Complex.continuous_ofReal.tendsto 1).comp
      (tendsto_jasFejerCount_div k)).mul_const (F k)
    simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using h
  · filter_upwards with K k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(jasFejerCount K k : ℝ) / ((K : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      exact_mod_cast jasFejerCount_le K k
    calc _ ≤ 1 * ‖F k‖ := by gcongr
      _ = ‖F k‖ := one_mul _

/-- A Fejér mean is bounded by the absolute sum. -/
theorem norm_jasFejerMean_le {F : ℤ → ℂ} (hF : Summable F) (K : ℕ) :
    ‖((K : ℂ) + 1)⁻¹ *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1), F ((a : ℤ) - b)‖ ≤
      ∑' k, ‖F k‖ := by
  rw [sum_range_sum_range_sub, ← tsum_mul_left]
  simp_rw [jasFejer_term_eq]
  have hs : Summable fun k => (((jasFejerCount K k : ℝ) / ((K : ℝ) + 1) : ℝ) : ℂ) * F k := by
    refine Summable.of_norm_bounded hF.norm fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(jasFejerCount K k : ℝ) / ((K : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      exact_mod_cast jasFejerCount_le K k
    calc _ ≤ 1 * ‖F k‖ := by gcongr
      _ = ‖F k‖ := one_mul _
  refine (norm_tsum_le_tsum_norm hs.norm).trans
    (Summable.tsum_le_tsum (fun k => ?_) hs.norm hF.norm)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |(jasFejerCount K k : ℝ) / ((K : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    exact_mod_cast jasFejerCount_le K k
  calc _ ≤ 1 * ‖F k‖ := by gcongr
    _ = ‖F k‖ := one_mul _

/-! ## The local Fourier series -/

theorem inv_eq_conj_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : w⁻¹ = conj w := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]
  simp

theorem jasLocalCoeff_mul_zpow_natCast (A B w : ℂ) (n : ℕ) :
    jasLocalCoeff A B (n : ℤ) * w ^ (n : ℤ) = (A * w) ^ n := by
  rw [jasLocalCoeff, if_pos (Int.natCast_nonneg n), Int.toNat_natCast, zpow_natCast, mul_pow]

theorem jasLocalCoeff_mul_zpow_neg_succ {A B w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) :
    jasLocalCoeff A B (-((n : ℤ) + 1)) * w ^ (-((n : ℤ) + 1)) = (B * conj w) ^ (n + 1) := by
  have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [jasLocalCoeff, if_neg (by omega), neg_neg, hcast, Int.toNat_natCast, zpow_neg,
    zpow_natCast, ← inv_pow, inv_eq_conj_of_norm_eq_one hw, mul_pow]

/-- The local density is the sum of its two-sided Fourier series on the unit circle. -/
theorem hasSum_jasLocalCoeff_mul_zpow {A B w : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hw : ‖w‖ = 1) :
    HasSum (fun k : ℤ => jasLocalCoeff A B k * w ^ k) (jasHoloLocal A B w) := by
  have hAw : ‖A * w‖ < 1 := by rw [norm_mul, hw, mul_one]; exact hA
  have hBw : ‖B * conj w‖ < 1 := by rw [norm_mul, Complex.norm_conj, hw, mul_one]; exact hB
  have hf : HasSum (fun n : ℕ => jasLocalCoeff A B (n : ℤ) * w ^ (n : ℤ)) (1 - A * w)⁻¹ := by
    simp_rw [jasLocalCoeff_mul_zpow_natCast]
    exact hasSum_geometric_of_norm_lt_one hAw
  have hg : HasSum (fun n : ℕ => jasLocalCoeff A B (-((n : ℤ) + 1)) * w ^ (-((n : ℤ) + 1)))
      ((1 - B * conj w)⁻¹ - 1) := by
    simp_rw [jasLocalCoeff_mul_zpow_neg_succ hw]
    have h1 : HasSum (fun n : ℕ => (B * conj w) ^ (n + 1))
        ((1 - B * conj w)⁻¹ - ∑ i ∈ Finset.range 1, (B * conj w) ^ i) :=
      (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_norm_lt_one hBw)
    rwa [Finset.sum_range_one, pow_zero] at h1
  have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => jasLocalCoeff A B k * w ^ k) hf hg
  convert h using 1
  rw [jasHoloLocal]
  ring

theorem hasSum_norm_jasLocalCoeff_mul_zpow {A B w : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hw : ‖w‖ = 1) :
    HasSum (fun k : ℤ => ‖jasLocalCoeff A B k * w ^ k‖) ((1 - ‖A‖)⁻¹ + ((1 - ‖B‖)⁻¹ - 1)) := by
  have hA' : ‖(‖A‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hB' : ‖(‖B‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hf : HasSum (fun n : ℕ => ‖jasLocalCoeff A B (n : ℤ) * w ^ (n : ℤ)‖) (1 - ‖A‖)⁻¹ := by
    simp_rw [jasLocalCoeff_mul_zpow_natCast, norm_pow, norm_mul, hw, mul_one]
    exact hasSum_geometric_of_norm_lt_one hA'
  have hg : HasSum (fun n : ℕ => ‖jasLocalCoeff A B (-((n : ℤ) + 1)) * w ^ (-((n : ℤ) + 1))‖)
      ((1 - ‖B‖)⁻¹ - 1) := by
    simp_rw [jasLocalCoeff_mul_zpow_neg_succ hw, norm_pow, norm_mul, Complex.norm_conj, hw,
      mul_one]
    have h1 : HasSum (fun n : ℕ => ‖B‖ ^ (n + 1))
        ((1 - ‖B‖)⁻¹ - ∑ i ∈ Finset.range 1, ‖B‖ ^ i) :=
      (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_norm_lt_one hB')
    rwa [Finset.sum_range_one, pow_zero] at h1
  exact hf.of_nat_of_neg_add_one hg

theorem summable_jasLocalCoeff_mul_zpow {A B w : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hw : ‖w‖ = 1) : Summable (fun k : ℤ => jasLocalCoeff A B k * w ^ k) :=
  (hasSum_jasLocalCoeff_mul_zpow hA hB hw).summable

/-- The local Fejér mean `(K+1)⁻¹ Σ_{a,b ≤ K} w^a w̄^b c(a - b)`. -/
def jasLocalFejer (A B w : ℂ) (K : ℕ) : ℂ :=
  ((K : ℂ) + 1)⁻¹ * ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
    w ^ a * conj w ^ b * jasLocalCoeff A B ((a : ℤ) - b)

theorem jasLocalFejer_eq {A B w : ℂ} (hw : ‖w‖ = 1) (K : ℕ) :
    jasLocalFejer A B w K = ((K : ℂ) + 1)⁻¹ *
      ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        (fun k : ℤ => jasLocalCoeff A B k * w ^ k) ((a : ℤ) - b) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  unfold jasLocalFejer
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [mul_comm (jasLocalCoeff A B _) (w ^ _), zpow_sub₀ hw0, zpow_natCast, zpow_natCast, div_eq_mul_inv,
    ← inv_pow, inv_eq_conj_of_norm_eq_one hw]

theorem tendsto_jasLocalFejer {A B w : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hw : ‖w‖ = 1) :
    Tendsto (jasLocalFejer A B w) atTop (𝓝 (jasHoloLocal A B w)) := by
  have h := tendsto_jasFejerMean (summable_jasLocalCoeff_mul_zpow hA hB hw)
  rw [(hasSum_jasLocalCoeff_mul_zpow hA hB hw).tsum_eq] at h
  exact h.congr fun K => (jasLocalFejer_eq hw K).symm

theorem norm_jasLocalFejer_le {A B w : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hw : ‖w‖ = 1)
    (K : ℕ) : ‖jasLocalFejer A B w K‖ ≤ (1 - ‖A‖)⁻¹ + ((1 - ‖B‖)⁻¹ - 1) := by
  rw [jasLocalFejer_eq hw, ← (hasSum_norm_jasLocalCoeff_mul_zpow hA hB hw).tsum_eq]
  exact norm_jasFejerMean_le (summable_jasLocalCoeff_mul_zpow hA hB hw) K

/-! ## Fejér test vectors on a finite prime set -/

/-- The character `Σ_{p ∈ P} x_p e_p` attached to an exponent vector. -/
def jasVecChar (P : Finset Nat.Primes) (x : ↥P → ℕ) : Nat.Primes →₀ ℤ :=
  ∑ i : ↥P, Finsupp.single (i : Nat.Primes) (x i : ℤ)

theorem jasVecChar_apply (P : Finset Nat.Primes) (x : ↥P → ℕ) (i : ↥P) :
    jasVecChar P x i = x i := by
  rw [jasVecChar, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hj (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem jasVecChar_apply_of_notMem (P : Finset Nat.Primes) (x : ↥P → ℕ) {p : Nat.Primes}
    (hp : p ∉ P) : jasVecChar P x p = 0 := by
  rw [jasVecChar, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h
  exact hp (h ▸ j.2)

theorem jasVecChar_injective (P : Finset Nat.Primes) : Function.Injective (jasVecChar P) := by
  intro x y h
  funext i
  have := congrArg (fun f : Nat.Primes →₀ ℤ => f (i : Nat.Primes)) h
  simp only [jasVecChar_apply] at this
  exact_mod_cast this

theorem support_jasVecChar_sub_subset (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    (jasVecChar P x - jasVecChar P y).support ⊆ P := by
  intro p hp
  by_contra hpP
  rw [Finsupp.mem_support_iff, Finsupp.sub_apply, jasVecChar_apply_of_notMem P x hpP,
    jasVecChar_apply_of_notMem P y hpP, sub_zero] at hp
  exact hp rfl

theorem jasDressedCoeff_jasVecChar_sub (s₁ s₂ : ℂ) (P : Finset Nat.Primes) (x y : ↥P → ℕ) :
    jasDressedCoeff s₁ s₂ (jasVecChar P x - jasVecChar P y) =
      ∏ i : ↥P, jasLocalCoeff (jasHoloA s₁ i) (jasHoloB s₂ i) ((x i : ℤ) - y i) := by
  rw [jasDressedCoeff, Finsupp.prod_of_support_subset _ (support_jasVecChar_sub_subset P x y) _
    (fun i _ => by simp [jasDressedLocalCoeff]), ← Finset.prod_coe_sort P]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.sub_apply, jasVecChar_apply, jasVecChar_apply]
  rfl

/-- The Fejér box `[0,K]^P` of exponent vectors. -/
abbrev jasFejerBox (P : Finset Nat.Primes) (K : ℕ) : Finset (↥P → ℕ) :=
  Fintype.piFinset fun _ : ↥P => Finset.range (K + 1)

/-- The Fejér coefficient `w^x = ∏_p w_p^{x_p}`. -/
def jasFejerCoeff (P : Finset Nat.Primes) (w : ↥P → ℂ) (x : ↥P → ℕ) : ℂ := ∏ i, w i ^ x i

/-- **Factorisation of the single-zero Fejér form over the primes.** -/
theorem sum_sum_fejer_jasDressedCoeff (s₁ s₂ : ℂ) (P : Finset Nat.Primes) (w : ↥P → ℂ)
    (K : ℕ) :
    ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K,
        jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
          jasDressedCoeff s₁ s₂ (jasVecChar P x - jasVecChar P y) =
      ∏ i : ↥P, ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        w i ^ a * conj (w i) ^ b *
          jasLocalCoeff (jasHoloA s₁ i) (jasHoloB s₂ i) ((a : ℤ) - b) := by
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [jasDressedCoeff_jasVecChar_sub, jasFejerCoeff, jasFejerCoeff, map_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]

/-! ## Uniform bounds on dressed local parameters -/

theorem norm_jasHoloA_dressed_le {q : ℂ} {c : ℝ} (h0 : 0 < q.re) (p : Nat.Primes) :
    ‖jasHoloA (q + c) p‖ ≤ Real.exp (-c * Real.log p) := by
  rw [norm_jasHoloA, Real.exp_le_exp]
  simp only [Complex.add_re, Complex.ofReal_re]
  nlinarith [log_prime_pos p]

theorem norm_jasHoloB_dressed_le {q : ℂ} {c : ℝ} (h1 : q.re < 1) (p : Nat.Primes) :
    ‖jasHoloB (q - c) p‖ ≤ Real.exp (-c * Real.log p) := by
  rw [jasHoloB, Complex.norm_exp, Real.exp_le_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.neg_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [log_prime_pos p]

theorem exp_neg_mul_log_lt_one {c : ℝ} (hc : 0 < c) (p : Nat.Primes) :
    Real.exp (-c * Real.log p) < 1 := by
  rw [Real.exp_lt_one_iff]
  nlinarith [log_prime_pos p]

/-- The uniform local bound `2/(1 - p^{-c})`. -/
def jasLocalBound (c : ℝ) (p : Nat.Primes) : ℝ := 2 * (1 - Real.exp (-c * Real.log p))⁻¹

theorem norm_jasLocalFejer_dressed_le {q : ℂ} {c : ℝ} (hc : 0 < c) (h0 : 0 < q.re)
    (h1 : q.re < 1) (p : Nat.Primes) {w : ℂ} (hw : ‖w‖ = 1) (K : ℕ) :
    ‖jasLocalFejer (jasHoloA (q + c) p) (jasHoloB (q - c) p) w K‖ ≤ jasLocalBound c p := by
  have hm := exp_neg_mul_log_lt_one hc p
  have hA := norm_jasHoloA_dressed_le (c := c) h0 p
  have hB := norm_jasHoloB_dressed_le (c := c) h1 p
  refine (norm_jasLocalFejer_le (hA.trans_lt hm) (hB.trans_lt hm) hw K).trans ?_
  have hpos : 0 < 1 - Real.exp (-c * Real.log p) := by linarith
  have e1 : (1 - ‖jasHoloA (q + c) p‖)⁻¹ ≤ (1 - Real.exp (-c * Real.log p))⁻¹ :=
    inv_anti₀ hpos (by linarith)
  have e2 : (1 - ‖jasHoloB (q - c) p‖)⁻¹ ≤ (1 - Real.exp (-c * Real.log p))⁻¹ :=
    inv_anti₀ hpos (by linarith)
  unfold jasLocalBound
  linarith

/-! ## Necessity -/

/-- The Fejér form of the `σ`-dressed aggregate on the box `[0,K]^P` at the torus point `w`. -/
def jasFejerForm (σ : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) (K : ℕ) : ℂ :=
  ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K,
    jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
      jasDressedLagAggregate σ (jasVecChar P x - jasVecChar P y)

/-- **Fejér limit.**  If every Fejér form at `w` has nonnegative real part, then the zero sum of the
twisted local Euler densities at `w` has nonnegative real part. -/
theorem re_tsum_prod_jasHoloLocal_nonneg_of_fejer {c : ℝ} (hc : 0 < c)
    (P : Finset Nat.Primes) (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    (hfej : ∀ K, 0 ≤ (jasFejerForm (1 / 2 + c) P w K).re) :
    0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
        (w i)).re := by
  have hc' : (1 / 2 + c - 1 / 2 : ℝ) = c := by ring
  -- the Fejér forms
  set Q : ℕ → ℂ := fun K => ∑ x ∈ jasFejerBox P K, ∑ y ∈ jasFejerBox P K,
    jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
      jasDressedLagAggregate (1 / 2 + c) (jasVecChar P x - jasVecChar P y) with hQ
  have hQnn : ∀ K, 0 ≤ (Q K).re := hfej
  have hs : ∀ (x y : ↥P → ℕ), Summable (fun q : XiZeroCopy =>
      jasFejerCoeff P w x * conj (jasFejerCoeff P w y) *
        (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (jasVecChar P x - jasVecChar P y) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    intro x y
    have := (summable_jasDressedCoeff_term (1 / 2 + c)
      (jasVecChar P x - jasVecChar P y)).mul_left
      (jasFejerCoeff P w x * conj (jasFejerCoeff P w y))
    simpa only [hc'] using this
  have hQeq : ∀ K, Q K = ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
      ∏ i : ↥P, ∑ a ∈ Finset.range (K + 1), ∑ b ∈ Finset.range (K + 1),
        w i ^ a * conj (w i) ^ b *
          jasLocalCoeff (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
            ((a : ℤ) - b) := by
    intro K
    rw [hQ]
    simp only
    simp_rw [jasDressedLagAggregate_eq_tsum, hc', ← tsum_mul_left]
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
  -- normalisation by `(K+1)^{|P|}`
  set N : ℕ → ℝ := fun K => ((K : ℝ) + 1) ^ Fintype.card ↥P with hN
  have hNpos : ∀ K, 0 < N K := fun K => by positivity
  have hnorm : ∀ K, ((N K)⁻¹ : ℝ) * (Q K).re = (((N K)⁻¹ : ℝ) * Q K : ℂ).re := by
    intro K
    rw [Complex.re_ofReal_mul]
  have hnn : ∀ K, 0 ≤ (((N K)⁻¹ : ℝ) * Q K : ℂ).re := fun K => by
    rw [← hnorm]
    exact mul_nonneg (inv_nonneg.mpr (hNpos K).le) (hQnn K)
  have hrw : ∀ K, (((N K)⁻¹ : ℝ) * Q K : ℂ) = ∑' q : XiZeroCopy,
      1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
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
  -- dominated convergence over the zeros
  have hlim : Tendsto (fun K => (((N K)⁻¹ : ℝ) * Q K : ℂ)) atTop
      (𝓝 (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (w i))) := by
    simp_rw [hrw]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
        ∏ i : ↥P, jasLocalBound c i)
      (summable_inv_mul_one_sub.norm.mul_right _) (fun q => ?_) ?_
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

/-- **Positivity forces pointwise positivity.**  If the `σ`-dressed aggregate (`σ = 1/2 + c`,
`c > 0`) is positive semidefinite, then on every finite prime torus the zero sum of the twisted
local Euler densities has nonnegative real part. -/
theorem re_tsum_prod_jasHoloLocal_nonneg_of_psd {c : ℝ} (hc : 0 < c)
    (hpsd : JasDressedPSD (1 / 2 + c)) (P : Finset Nat.Primes) (w : ↥P → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) :
    0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
        (w i)).re :=
  re_tsum_prod_jasHoloLocal_nonneg_of_fejer hc P w hw fun K =>
    hpsd _ (jasFejerBox P K) (jasFejerCoeff P w) (jasVecChar P) (jasVecChar_injective P).injOn

/-! ## Sufficiency -/

theorem norm_jasCharBar (P : Finset Nat.Primes) (n : Nat.Primes →₀ ℤ) (x : ↥P → UnitAddCircle) :
    ‖jasCharBar P n x‖ = 1 := by
  rw [jasCharBar, norm_prod]
  exact Finset.prod_eq_one fun i _ => norm_fourier_unit _ _

/-- The uniform circle bound `2/(1 - p^{-c}) + 1` for a dressed local density. -/
def jasCircleBound (c : ℝ) (p : Nat.Primes) : ℝ := 2 * (1 - Real.exp (-c * Real.log p))⁻¹ + 1

theorem norm_jasSectorDensity_le {q : ℂ} {c : ℝ} (hc : 0 < c) (h0 : 0 < q.re) (h1 : q.re < 1)
    (P : Finset Nat.Primes) (x : ↥P → UnitAddCircle) :
    ‖jasSectorDensity q c P x‖ ≤ ∏ i : ↥P, jasCircleBound c i := by
  unfold jasSectorDensity
  rw [norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  have hm := exp_neg_mul_log_lt_one hc i
  have hA := norm_jasHoloA_dressed_le (c := c) h0 i
  have hB := norm_jasHoloB_dressed_le (c := c) h1 i
  refine (norm_jasHoloCircle_le (hA.trans_lt hm) (hB.trans_lt hm) (x i)).trans ?_
  have hpos : 0 < 1 - Real.exp (-c * Real.log i) := by linarith
  have e1 : 1 / (1 - ‖jasHoloA (q + c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos (by linarith)
  have e2 : 1 / (1 - ‖jasHoloB (q - c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos (by linarith)
  unfold jasCircleBound
  linarith

/-- **Pointwise positivity forces positivity.** -/
theorem jasDressedPSD_of_pointwise {c : ℝ} (hc : 0 < c)
    (hpt : ∀ (P : Finset Nat.Primes) (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (w i)).re) :
    JasDressedPSD (1 / 2 + c) := by
  classical
  intro ι t cc n _
  set P : Finset Nat.Primes := t.biUnion (fun i => (n i).support) with hP
  have hn : ∀ i ∈ t, (n i).support ⊆ P := fun i hi p hp =>
    Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hc' : (1 / 2 + c - 1 / 2 : ℝ) = c := by ring
  set μ : Measure (↥P → UnitAddCircle) := Measure.pi fun _ => jasCircleHaar with hμ
  set f : (↥P → UnitAddCircle) → ℂ := fun x => ∑ i ∈ t, cc i * jasCharBar P (n i) x with hf
  set wt : XiZeroCopy → ℂ := fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hwt
  set C : ℝ := ∏ i : ↥P, jasCircleBound c i with hC
  set Mf : ℝ := (∑ i ∈ t, ‖cc i‖) ^ 2 with hMf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_jasCharBar P _)
  have hfb : ∀ x, ‖f x * conj (f x)‖ ≤ Mf := by
    intro x
    rw [norm_mul, Complex.norm_conj, ← sq, hMf]
    have : ‖f x‖ ≤ ∑ i ∈ t, ‖cc i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_jasCharBar, mul_one]
    gcongr
  have hre : ∀ q : XiZeroCopy, 0 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 1 :=
    fun q => xi_divisor_support_re_mem_open_unit q.1
  -- the zero-by-zero integrands
  set F : XiZeroCopy → (↥P → UnitAddCircle) → ℂ := fun q x =>
    wt q * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x) with hF
  have hFc : ∀ q, Continuous (F q) := by
    intro q
    have h0 : 0 < (q.1 : ℂ).re + c := by linarith [(hre q).1]
    have h1 : 0 < 1 - (q.1 : ℂ).re + c := by linarith [(hre q).2]
    exact continuous_const.mul ((hfc.mul (Complex.continuous_conj.comp hfc)).mul
      (continuous_jasSectorDensity h0 h1 P))
  have hFb : ∀ q x, ‖F q x‖ ≤ ‖wt q‖ * (Mf * C) := by
    intro q x
    rw [hF, norm_mul, norm_mul]
    gcongr
    · exact hfb x
    · exact norm_jasSectorDensity_le hc (hre q).1 (hre q).2 P x
  have hwsum : Summable fun q => ‖wt q‖ := summable_inv_mul_one_sub.norm
  -- the quadratic form as a zero sum of Gram integrals
  have hs : ∀ i j, Summable (fun q : XiZeroCopy => cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    intro i j
    have := (summable_jasDressedCoeff_term (1 / 2 + c) (n i - n j)).mul_left (cc i * conj (cc j))
    simpa only [hc'] using this
  have hQ : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasDressedLagAggregate (1 / 2 + c) (n i - n j) =
      ∑' q : XiZeroCopy, ∫ x, F q x ∂μ := by
    simp_rw [jasDressedLagAggregate_eq_tsum, hc', ← tsum_mul_left]
    have hex : ∑ i ∈ t, ∑ j ∈ t, ∑' q : XiZeroCopy, cc i * conj (cc j) *
        (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) =
        ∑' q : XiZeroCopy, ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
          (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
            ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
      rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Summable.tsum_finsetSum fun j _ => hs i j]
    rw [hex]
    refine tsum_congr fun q => ?_
    have h0 : 0 < (q.1 : ℂ).re + c := by linarith [(hre q).1]
    have h1 : 0 < 1 - (q.1 : ℂ).re + c := by linarith [(hre q).2]
    rw [hF]
    simp only
    rw [integral_const_mul, ← gram_jasDressedCoeff_eq_integral h0 h1 P t cc n hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwt]
    ring
  -- exchange of the zero sum and the torus integral
  have hint : ∀ q, Integrable (F q) μ := fun q =>
    (hFc q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsumint : Summable fun q => ∫ x, ‖F q x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun x => norm_nonneg _)
      (fun q => ?_) (hwsum.mul_right (Mf * C))
    have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ‖F q x‖)
      (C := ‖wt q‖ * (Mf * C)) (Filter.Eventually.of_forall fun x => by
        rw [norm_norm]; exact hFb q x)
    rw [probReal_univ, mul_one] at hb
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hb)
  rw [hQ, integral_tsum_of_summable_integral_norm hint hsumint]
  -- the integrand is a nonnegative weight times the pointwise zero sum
  have hcontS : Continuous fun x => ∑' q, F q x :=
    continuous_tsum hFc (hwsum.mul_right (Mf * C)) hFb
  have hintS : Integrable (fun x => ∑' q, F q x) μ :=
    hcontS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreS := integral_re hintS
  simp only [RCLike.re_to_complex] at hreS
  rw [← hreS]
  refine integral_nonneg fun x => ?_
  have hpx := hpt P (fun i => fourier 1 (x i)) (fun i => norm_fourier_unit _ _)
  have heq : ∑' q, F q x = ((Complex.normSq (f x) : ℝ) : ℂ) *
      ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (fourier 1 (x i)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [hF, ← Complex.mul_conj]
    simp only
    unfold jasSectorDensity jasHoloCircle
    rw [hwt]
    ring
  show 0 ≤ (∑' q, F q x).re
  rw [heq, Complex.re_ofReal_mul]
  exact mul_nonneg (Complex.normSq_nonneg _) hpx

/-! ## The criterion -/

/-- **Pointwise criterion.**  For `c > 0`, the `σ`-dressed aggregate (`σ = 1/2 + c`) is positive
semidefinite on rational characters if and only if on every finite prime torus the zero sum of the
twisted local Euler densities has nonnegative real part. -/
theorem jasDressedPSD_iff_pointwise {c : ℝ} (hc : 0 < c) :
    JasDressedPSD (1 / 2 + c) ↔ ∀ (P : Finset Nat.Primes) (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i)
          (w i)).re :=
  ⟨fun h P w hw => re_tsum_prod_jasHoloLocal_nonneg_of_psd hc h P w hw,
    jasDressedPSD_of_pointwise hc⟩

/-- **Riemann Hypothesis in pointwise Euler form.**  RH implies pointwise positivity of the zero sum
of twisted local Euler densities at `σ = 1`; conversely pointwise positivity at `σ = 1` forces RH
unless the off-line zeros form a chain with no farthest zero. -/
theorem riemannHypothesis_or_chain_of_pointwise_one
    (hpt : ∀ (P : Finset Nat.Primes) (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) i)
          (jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) i) (w i)).re) :
    RiemannHypothesis ∨ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| := by
  have h := jasDressedPSD_of_pointwise (by norm_num : (0 : ℝ) < 1 / 2) hpt
  norm_num at h
  exact riemannHypothesis_or_offLine_chain_of_jasDressedPSD le_rfl h

theorem pointwise_one_of_riemannHypothesis (hRH : RiemannHypothesis) (P : Finset Nat.Primes)
    (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    0 ≤ (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) i)
          (jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) i) (w i)).re := by
  have h := jasDressedPSD_of_riemannHypothesis hRH (σ := 1 / 2 + 1 / 2) (by norm_num)
  exact re_tsum_prod_jasHoloLocal_nonneg_of_psd (by norm_num) h P w hw

end

end RHTower
