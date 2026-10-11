import GaloisForLFunctions.RHTower.XiSliceBoundedDetectionOrder
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Mixed horizontal classes are detected at bounded slice order

Let `ρ` be a zero of `ξ` off the critical line, with ordinate `γ` and displacement
`δ = |Re ρ − ½| > 0`.  The bounded-detection theorem
(`exists_re_xiSliceCoeff_neg_of_offLine_mass`) assumes `ξ(½ + iγ) ≠ 0`.  This file removes that
assumption.  When `ξ(½ + iγ) = 0` with order `k`, the horizontal line through `ρ` carries a critical
zero as well: a *mixed class*.

**Factorization at a zero height** (`xiSliceProduct_eq_pow_mul_away`).  With `γ` the spectral point
of the critical zero and `P` the canonical product over the other zero copies,
`g_γ(x) = x^{2k} G(x)`, where `G(x) = Ξ(0)² (e²/γ²)^k P(γ − ix) P(γ + ix)` is entire and `G(0) ≠ 0`.
The two factors `E₁((γ ∓ ix)/γ)` of the critical copies multiply to `x² e²/γ²`.

**Theorem** (`exists_re_xiSliceCoeff_neg_of_offLine_mass_order`).  If at most `m` copies sit at
`γ ± iδ`, the copies away from `γ` and `γ ± iδ` have `Σ 1/|z − γ|² ≤ S`, and
`2 · 5^m · e^{4δ²S} < 2^N`, then some `c_n(γ)` with `2k ≤ n < 2k + N` has negative real part.

So a mixed class is seen at its own ordinate, with the same detection length `N` as an unmixed
off-line zero, shifted by twice the critical multiplicity.  The proof applies the real-zero
detection bound (`exists_re_taylorCoeff_neg_of_real_zero`) to `G`, which vanishes at `x = δ`, and
identifies the Taylor coefficients of `G` with the shifted slice coefficients by the Leibniz rule
(`iteratedDeriv_pow_mul_zero`).
-/

open Complex Filter Topology Metric
open scoped Nat

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Detection by a positive real zero.**  Let `G` be entire with `G(δ) = 0` for some `δ > 0`,
and `|G| ≤ M` on `|x| = R > δ`.  If `M (δ/R)^N/(1 − δ/R) < Re G(0)`, some Taylor coefficient of `G`
at `0` of order `< N` has negative real part. -/
theorem exists_re_taylorCoeff_neg_of_real_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {δ R M : ℝ} (hδ : 0 < δ) (hδR : δ < R) (hzero : G δ = 0)
    (hM : ∀ x ∈ sphere (0 : ℂ) R, ‖G x‖ ≤ M) {N : ℕ}
    (hN : M * (δ / R) ^ N / (1 - δ / R) < (G 0).re) :
    ∃ j < N, (((j ! : ℂ))⁻¹ * iteratedDeriv j G 0).re < 0 := by
  by_contra hall
  push Not at hall
  have hR0 : 0 < R := hδ.trans hδR
  set r : ℝ := δ / R with hr
  have hr0 : 0 ≤ r := div_nonneg hδ.le hR0.le
  have hr1 : r < 1 := (div_lt_one hR0).mpr hδR
  set a : ℕ → ℂ := fun j => ((j ! : ℂ))⁻¹ * iteratedDeriv j G 0 with ha
  have hcoef : ∀ j, ‖a j‖ ≤ M / R ^ j := by
    intro j
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR0
      hG.diffContOnCl hM
    have hfac : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
    simp only [ha, norm_mul, norm_inv, Complex.norm_natCast]
    calc ((j ! : ℝ))⁻¹ * ‖iteratedDeriv j G 0‖ ≤ ((j ! : ℝ))⁻¹ * ((j ! : ℝ) * M / R ^ j) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfac.le)
      _ = M / R ^ j := by field_simp
  have ha0 : a 0 = G 0 := by simp [ha]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans ((hcoef 0).trans (by simp))
  have hG0M : (G 0).re ≤ M := by
    have h := hcoef 0
    rw [ha0, pow_zero, div_one] at h
    exact (Complex.re_le_norm _).trans h
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [pow_zero, mul_one] at hN
    have : M ≤ M / (1 - r) := le_div_self hM0 (by linarith) (by linarith)
    linarith
  -- the Taylor series at the real zero `δ`
  have hsum : HasSum (fun j => a j * (δ : ℂ) ^ j) 0 := by
    have h := hasSum_taylorSeries_of_entire hG 0 (δ : ℂ)
    rw [hzero] at h
    simp only [sub_zero, smul_eq_mul] at h
    refine h.congr_fun fun j => ?_
    simp only [ha]
    ring
  have htail := (hasSum_nat_add_iff' N).mpr hsum
  have hgeo : HasSum (fun j : ℕ => M * r ^ N * r ^ j) (M * r ^ N / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * r ^ N)
    simpa [div_eq_mul_inv] using this
  have hbound : ∀ j : ℕ, ‖a (j + N) * (δ : ℂ) ^ (j + N)‖ ≤ M * r ^ N * r ^ j := by
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    calc ‖a (j + N)‖ * δ ^ (j + N) ≤ M / R ^ (j + N) * δ ^ (j + N) :=
          mul_le_mul_of_nonneg_right (hcoef _) (pow_nonneg hδ.le _)
      _ = M * r ^ N * r ^ j := by
          rw [hr, div_pow, div_pow, pow_add, pow_add]
          field_simp
  have htailnorm := htail.norm_le_of_bounded hgeo hbound
  have hhead : (G 0).re ≤ (∑ i ∈ Finset.range N, a i * (δ : ℂ) ^ i).re := by
    rw [Complex.re_sum]
    have hterm : ∀ i ∈ Finset.range N, 0 ≤ (a i * (δ : ℂ) ^ i).re := by
      intro i hi
      rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
      exact mul_nonneg (hall i (Finset.mem_range.mp hi)) (pow_nonneg hδ.le _)
    have h0 := Finset.single_le_sum hterm (Finset.mem_range.mpr hNpos)
    simpa [ha0] using h0
  have hre : (∑ i ∈ Finset.range N, a i * (δ : ℂ) ^ i).re ≤ M * r ^ N / (1 - r) := by
    have e : (∑ i ∈ Finset.range N, a i * (δ : ℂ) ^ i) =
        -(0 - ∑ i ∈ Finset.range N, a i * (δ : ℂ) ^ i) := by ring
    rw [e, Complex.neg_re]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans htailnorm)
  linarith

/-- **Leibniz rule against a monomial.**  At `0`, the `n`-th derivative of `x^k G(x)` vanishes
for `n < k` and equals `C(n,k) k! G^{(n−k)}(0)` otherwise. -/
theorem iteratedDeriv_pow_mul_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G) (k n : ℕ) :
    iteratedDeriv n (fun x => x ^ k * G x) 0 =
      if k ≤ n then ((n.choose k * k ! : ℕ) : ℂ) * iteratedDeriv (n - k) G 0 else 0 := by
  have hpow : ContDiffAt ℂ n (fun x : ℂ => x ^ k) 0 :=
    (by fun_prop : ContDiff ℂ n (fun x : ℂ => x ^ k)).contDiffAt
  have hGc : ContDiffAt ℂ n G 0 := hG.contDiff.contDiffAt
  have e : (fun x => x ^ k * G x) = (fun x : ℂ => x ^ k) * G := rfl
  rw [e, iteratedDeriv_mul hpow hGc]
  have hd : ∀ i, iteratedDeriv i (fun x : ℂ => x ^ k) 0 = if i = k then (k ! : ℂ) else 0 := by
    intro i
    rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
    split_ifs with hik
    · subst hik
      rw [Nat.sub_self, pow_zero, mul_one, ← Finset.prod_range_reflect]
      have e2 : ∀ j ∈ Finset.range i, ((i : ℂ) - ((i - 1 - j : ℕ) : ℂ)) = ((j + 1 : ℕ) : ℂ) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [Finset.prod_congr rfl e2, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
    · rcases lt_or_gt_of_ne hik with h | h
      · rw [zero_pow (by omega), mul_zero]
      · rw [Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr h) (by simp), zero_mul]
  simp_rw [hd]
  split_ifs with hkn
  · rw [Finset.sum_eq_single k]
    · simp only [if_true]
      push_cast
      ring
    · intro b _ hb
      simp [hb]
    · intro hk
      exact absurd (Finset.mem_range.mpr (by omega)) hk
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.mp hi
      omega
    simp [this]

/-- The slice product as a product of two values of `Ξ`. -/
theorem xiSliceProduct_eq_XiC_mul (t : ℝ) (x : ℂ) :
    xiSliceProduct t x = XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) := by
  unfold xiSliceProduct XiC
  congr 2 <;> ring_nf <;> rw [I_sq] <;> ring

/-- The two genus-one factors of a critical copy at `γ ≠ 0`. -/
theorem weierstrassE1_sub_mul_add (γ x : ℂ) (hγ : γ ≠ 0) :
    weierstrassE1 ((γ - I * x) / γ) * weierstrassE1 ((γ + I * x) / γ) =
      x ^ 2 * (Complex.exp 2 / γ ^ 2) := by
  unfold weierstrassE1
  have hsum : (γ - I * x) / γ + (γ + I * x) / γ = 2 := by field_simp; ring
  calc (1 - (γ - I * x) / γ) * Complex.exp ((γ - I * x) / γ) *
        ((1 - (γ + I * x) / γ) * Complex.exp ((γ + I * x) / γ))
      = ((1 - (γ - I * x) / γ) * (1 - (γ + I * x) / γ)) *
          (Complex.exp ((γ - I * x) / γ) * Complex.exp ((γ + I * x) / γ)) := by ring
    _ = x ^ 2 * (Complex.exp 2 / γ ^ 2) := by
        rw [← Complex.exp_add, hsum]
        field_simp
        ring_nf
        rw [I_sq]
        ring

/-- **The slice at a zero height.**  If `γ` is the spectral point of the zero `ρ₀` of order `k`,
then `g_γ(x) = x^{2k} · Ξ(0)² (e²/γ²)^k P(γ − ix) P(γ + ix)`, with `P` the canonical product over
the copies away from `ρ₀`. -/
theorem xiSliceProduct_eq_pow_mul_away (ρ₀ : XiDivisorSupport) {γ : ℝ}
    (hγ : xiSpectralPointSupport ρ₀ = γ) (x : ℂ) :
    xiSliceProduct γ x =
      x ^ (2 * Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ))) *
        (XiC 0 ^ 2 * (Complex.exp 2 / (γ : ℂ) ^ 2) ^
            Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ)) *
          (xiCanonicalProductAway ρ₀ ((γ : ℂ) - I * x) *
            xiCanonicalProductAway ρ₀ ((γ : ℂ) + I * x))) := by
  set k := Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ))
  have hγ0 : (γ : ℂ) ≠ 0 := by
    rw [← hγ]
    exact xiSpectralPoint_ne_zero ⟨ρ₀, ⟨0, by
      have := xi_divisor_pos_on_support ρ₀
      omega⟩⟩
  have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
  rw [xiSliceProduct_eq_XiC_mul, hX ((γ : ℂ) - I * x), hX ((γ : ℂ) + I * x),
    xiCanonicalProduct_factorization_at_support ρ₀ ((γ : ℂ) - I * x),
    xiCanonicalProduct_factorization_at_support ρ₀ ((γ : ℂ) + I * x), hγ]
  have hE := weierstrassE1_sub_mul_add (γ : ℂ) x hγ0
  calc XiC 0 * (weierstrassE1 (((γ : ℂ) - I * x) / γ) ^ k *
          xiCanonicalProductAway ρ₀ ((γ : ℂ) - I * x)) *
        (XiC 0 * (weierstrassE1 (((γ : ℂ) + I * x) / γ) ^ k *
          xiCanonicalProductAway ρ₀ ((γ : ℂ) + I * x)))
      = XiC 0 ^ 2 * (weierstrassE1 (((γ : ℂ) - I * x) / γ) *
          weierstrassE1 (((γ : ℂ) + I * x) / γ)) ^ k *
          (xiCanonicalProductAway ρ₀ ((γ : ℂ) - I * x) *
            xiCanonicalProductAway ρ₀ ((γ : ℂ) + I * x)) := by ring
    _ = _ := by rw [hE, mul_pow, ← pow_mul]; ring

/-- **Mixed-class bounded detection.**  Let `ρ` be a zero of `ξ` off the critical line, with
`γ = Im ρ`, `δ = |Re ρ − ½|`, and let `k` be the order of `Ξ` at `γ` (`k = 0` when
`ξ(½ + iγ) ≠ 0`).  Suppose at most `m` zero copies sit at `γ ± iδ` and the copies away from `γ` and
`γ ± iδ` have `Σ 1/|z − γ|² ≤ S`.  If `2 · 5^m · e^{4δ²S} < 2^N`, some slice coefficient `c_n(γ)`
with `2k ≤ n < 2k + N` has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_offLine_mass_order {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) {k : ℕ} (hk : analyticOrderAt XiC (ρ.im : ℂ) = k) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, xiSpectralPoint q ≠ (ρ.im : ℂ) ∧
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ} (hN : 2 * 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) < 2 ^ N) :
    ∃ n, 2 * k ≤ n ∧ n < 2 * k + N ∧ (xiSliceCoeff ρ.im n).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have han : AnalyticAt ℂ XiC (t : ℂ) := XiC_analytic _ (Set.mem_univ _)
  by_cases hΞ : XiC (t : ℂ) ≠ 0
  · -- no critical zero at the ordinate
    have hk0 : k = 0 := by
      have h0 := han.analyticOrderAt_eq_zero.mpr hΞ
      rw [hk] at h0
      exact_mod_cast h0
    obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_offLine_mass hρ hne hΞ hown
      (S := S) (fun F hF => hS F fun q hq => ⟨xiSpectralPoint_ne_ofReal hΞ q, hF q hq⟩) hN
    exact ⟨n, by omega, by omega, hneg⟩
  push Not at hΞ
  -- the critical zero at the ordinate and the factorization of the slice
  obtain ⟨q₀, hq₀⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hΞ
  set ρ₀ : XiDivisorSupport := q₀.1 with hρ₀
  have hγ : xiSpectralPointSupport ρ₀ = t := by rw [← xiSpectralPoint_eq_support]; exact hq₀
  have hkk : k = Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ)) := by
    have h := XiC_analyticOrderAt_support ρ₀
    rw [hγ, hk] at h
    exact_mod_cast h
  set P : ℂ → ℂ := xiCanonicalProductAway ρ₀ with hPdef
  set C : ℂ := XiC 0 ^ 2 * (Complex.exp 2 / (t : ℂ) ^ 2) ^ k with hC
  set G : ℂ → ℂ := fun x => C * (P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x)) with hGdef
  have hfac : ∀ x, xiSliceProduct t x = x ^ (2 * k) * G x := by
    intro x
    have h := xiSliceProduct_eq_pow_mul_away ρ₀ hγ x
    rw [← hkk] at h
    exact h
  have hPd : Differentiable ℂ P :=
    differentiableOn_univ.mp (xiCanonicalProductAway_analytic ρ₀).differentiableOn
  have hGd : Differentiable ℂ G := by
    have h1 : Differentiable ℂ (fun x : ℂ => P ((t : ℂ) - I * x)) :=
      hPd.comp ((differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
    have h2 : Differentiable ℂ (fun x : ℂ => P ((t : ℂ) + I * x)) :=
      hPd.comp ((differentiable_const _).add ((differentiable_const _).mul differentiable_id))
    exact (h1.mul h2).const_mul C
  -- Taylor coefficients of `G` are the shifted slice coefficients
  have hcoef : ∀ j, xiSliceCoeff t (2 * k + j) = ((j ! : ℂ))⁻¹ * iteratedDeriv j G 0 := by
    intro j
    have hfun : xiSliceProduct t = fun x => x ^ (2 * k) * G x := funext hfac
    unfold xiSliceCoeff
    rw [hfun, iteratedDeriv_pow_mul_zero hGd, if_pos (by omega), Nat.add_sub_cancel_left]
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (2 * k) j)
    rw [Nat.add_sub_cancel_left] at h
    have h' : (((2 * k + j).choose (2 * k) * (2 * k) ! : ℕ) : ℂ) * (j ! : ℂ) =
        ((2 * k + j) ! : ℂ) := by exact_mod_cast h
    have hj : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    have hc : (((2 * k + j).choose (2 * k) * (2 * k) ! : ℕ) : ℂ) ≠ 0 := by
      have : 0 < (2 * k + j).choose (2 * k) * (2 * k) ! :=
        Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.factorial_pos _)
      exact_mod_cast this.ne'
    rw [← h']
    field_simp
  -- `G(0)` is a positive real number
  have hG0eq : G 0 = xiSliceCoeff t (2 * k) := by
    have h := hcoef 0
    rw [Nat.add_zero] at h
    rw [h]
    simp
  have hG0im : (G 0).im = 0 := by rw [hG0eq]; exact xiSliceCoeff_im_eq_zero t _
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h
    rw [h] at hΞ
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    exact xi_ne_zero_of_real _ (this ▸ hΞ)
  have hPt : P t ≠ 0 := by
    rw [← hγ]
    exact xiCanonicalProductAway_ne_zero_at ρ₀
  have hG0ne : G 0 ≠ 0 := by
    have hX0 : XiC 0 ≠ 0 := by
      have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
      rw [this]
      exact xi_ne_zero_of_real _
    simp only [hGdef, mul_zero, sub_zero, add_zero, hC]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hX0) (pow_ne_zero _
      (div_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ ht0)))) (mul_ne_zero hPt hPt)
  have hG0nonneg : 0 ≤ (G 0).re := by
    have hreal : ∀ u : ℝ, u ≠ 0 → 0 ≤ (G (u : ℂ)).re := by
      intro u hu
      have hu' : (u : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu)
      have hG : G (u : ℂ) = xiSliceProduct t (u : ℂ) / (u : ℂ) ^ (2 * k) := by
        rw [hfac]; field_simp
      rw [hG, xiSliceProduct_ofReal_eq, ← Complex.ofReal_pow, ← Complex.ofReal_div,
        Complex.ofReal_re]
      exact div_nonneg (sq_nonneg _) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) _)
    have hc : Continuous (fun u : ℝ => (G (u : ℂ)).re) :=
      Complex.continuous_re.comp (hGd.continuous.comp Complex.continuous_ofReal)
    have hlim : Tendsto (fun u : ℝ => (G (u : ℂ)).re) (𝓝[≠] 0) (𝓝 (G ((0 : ℝ) : ℂ)).re) :=
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    rw [Complex.ofReal_zero] at hlim
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun u hu => hreal u hu)
  have hG0pos : 0 < (G 0).re := by
    rcases hG0nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm hG0im) hG0ne
  have hG0norm : ‖G 0‖ = (G 0).re := by
    have hreal : G 0 = (((G 0).re : ℝ) : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hG0im)
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hG0pos]
  -- `G` vanishes at the real point `δ`
  have hGδ : G δ = 0 := by
    have h := hfac (δ : ℂ)
    rw [xiSliceProduct_abs_eq_zero hρ] at h
    have hδ' : (δ : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hδ.ne')
    exact (mul_eq_zero.mp h.symm).resolve_left hδ'
  -- the product over the copies away from the critical zero
  have hzt : ∀ q : XiZeroCopyAway ρ₀, xiSpectralPoint q.1 ≠ (t : ℂ) := by
    intro q h
    apply q.2
    apply xiSpectralPointSupport_injective
    rw [← xiSpectralPoint_eq_support, h, hγ]
  have hP : TendstoLocallyUniformlyOn
      (fun (F : Finset (XiZeroCopyAway ρ₀)) (x : ℂ) =>
        ∏ q ∈ F, weierstrassE1 (x / xiSpectralPoint q.1)) P atTop Set.univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn (fun q : XiZeroCopyAway ρ₀ =>
      xiSpectralPoint q.1) (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductAway_inv_sq_summable ρ₀)
  have hpt : ∀ a : ℂ, Tendsto (fun F : Finset (XiZeroCopyAway ρ₀) =>
      ∏ q ∈ F, weierstrassE1 (a / xiSpectralPoint q.1)) atTop (𝓝 (P a)) :=
    fun a => hP.tendsto_at (Set.mem_univ a)
  have hE : ∀ q : XiZeroCopyAway ρ₀, weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1) ≠ 0 := by
    intro q
    unfold weierstrassE1
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (xiSpectralPoint_ne_zero q.1)]
    exact fun h => hzt q h.symm
  have hratio : ∀ x : ℂ, Tendsto (fun F : Finset (XiZeroCopyAway ρ₀) =>
      ∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2)) atTop
      (𝓝 (P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x) / P t ^ 2)) := by
    intro x
    have hlim := ((hpt ((t : ℂ) - I * x)).mul (hpt ((t : ℂ) + I * x))).div ((hpt t).pow 2)
      (pow_ne_zero 2 hPt)
    refine hlim.congr fun F => ?_
    have hden : (∏ q ∈ F, weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun q _ => hE q)
    simp only [Pi.div_apply]
    rw [div_eq_iff hden, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    have h := weierstrassE1_pair_eq (t : ℂ) (-(I * x)) (xiSpectralPoint q.1)
      (xiSpectralPoint_ne_zero q.1) (hzt q)
    have e1 : (t : ℂ) + -(I * x) = (t : ℂ) - I * x := by ring
    have e2 : (t : ℂ) - -(I * x) = (t : ℂ) + I * x := by ring
    have e3 : (-(I * x)) ^ 2 = -(x ^ 2) := by ring_nf; rw [I_sq]; ring
    rw [e1, e2, e3] at h
    rw [h]
    ring
  -- the bound on the circle `|x| = 2δ`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 5 ^ m * Real.exp (4 * δ ^ 2 * S) := ⟨_, rfl⟩
  have hfinite : ∀ x : ℂ, ‖x‖ = 2 * δ → ∀ F : Finset (XiZeroCopyAway ρ₀),
      ‖∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2)‖ ≤ B := by
    intro x hx F
    set own : XiZeroCopyAway ρ₀ → Prop := fun q =>
      xiSpectralPoint q.1 = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q.1 = (t : ℂ) - (δ : ℂ) * I
    rw [← Finset.prod_filter_mul_prod_filter_not F own, norm_mul, norm_prod, norm_prod]
    have hx2 : ‖x ^ 2‖ = 4 * δ ^ 2 := by rw [norm_pow, hx]; ring
    have h1 : ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖ ≤ 5 ^ m := by
      calc ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖
          ≤ ∏ q ∈ F with own q, (5 : ℝ) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
            have hsq : (xiSpectralPoint q.1 - t) ^ 2 = -((δ : ℂ) ^ 2) := by
              rcases (Finset.mem_filter.mp hq).2 with h | h <;> rw [h] <;> ring_nf <;>
                rw [I_sq] <;> ring
            rw [hsq]
            calc ‖1 + x ^ 2 / -((δ : ℂ) ^ 2)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / -((δ : ℂ) ^ 2)‖ :=
                  norm_add_le _ _
              _ = 5 := by
                  rw [norm_one, norm_div, norm_neg, hx2, norm_pow, Complex.norm_real,
                    Real.norm_eq_abs, abs_of_pos hδ]
                  field_simp
                  norm_num
        _ = 5 ^ (F.filter own).card := by rw [Finset.prod_const]
        _ ≤ 5 ^ m := by
            refine pow_le_pow_right₀ (by norm_num) ?_
            have h := hown ((F.filter own).map (Function.Embedding.subtype _)) fun q hq => by
              obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
              exact (Finset.mem_filter.mp hp).2
            rwa [Finset.card_map] at h
    have h2 : ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖ ≤
        Real.exp (4 * δ ^ 2 * S) := by
      calc ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖
          ≤ ∏ q ∈ F with ¬ own q,
              Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q.1 - t‖ ^ 2)) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
            calc ‖1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖
                ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2‖ := norm_add_le _ _
              _ = 4 * δ ^ 2 * (1 / ‖xiSpectralPoint q.1 - t‖ ^ 2) + 1 := by
                  rw [norm_one, norm_div, hx2, norm_pow]; ring
              _ ≤ Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q.1 - t‖ ^ 2)) :=
                  Real.add_one_le_exp _
        _ = Real.exp (4 * δ ^ 2 * ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q.1 - t‖ ^ 2) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ Real.exp (4 * δ ^ 2 * S) := by
            apply Real.exp_le_exp.mpr
            have hsum := hS ((F.filter fun q => ¬ own q).map (Function.Embedding.subtype _))
              fun q hq => by
                obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
                exact ⟨hzt p, (Finset.mem_filter.mp hp).2⟩
            rw [Finset.sum_map] at hsum
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [hB]
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun q _ => norm_nonneg _) (by positivity)
  have hM : ∀ x ∈ sphere (0 : ℂ) (2 * δ), ‖G x‖ ≤ (G 0).re * B := by
    intro x hx
    have hx' : ‖x‖ = 2 * δ := mem_sphere_zero_iff_norm.mp hx
    have hle := le_of_tendsto (hratio x).norm (Eventually.of_forall (hfinite x hx'))
    have hGx : G x = G 0 * (P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x) / P t ^ 2) := by
      simp only [hGdef, mul_zero, sub_zero, add_zero]
      field_simp
    rw [hGx, norm_mul, hG0norm]
    exact mul_le_mul_of_nonneg_left hle hG0pos.le
  -- the real-zero detection bound at `R = 2δ`
  have hcond : (G 0).re * B * (δ / (2 * δ)) ^ N / (1 - δ / (2 * δ)) < (G 0).re := by
    have hhalf : δ / (2 * δ) = 1 / 2 := by field_simp
    rw [hhalf]
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have e : (G 0).re * B * (1 / 2) ^ N / (1 - 1 / 2) = (2 * B / 2 ^ N) * (G 0).re := by
      rw [one_div_pow]; field_simp; ring
    rw [e]
    have hB2 : 2 * B / 2 ^ N < 1 := by
      rw [div_lt_one h2N, hB]
      simpa [mul_assoc] using hN
    nlinarith
  obtain ⟨j, hj, hneg⟩ := exists_re_taylorCoeff_neg_of_real_zero hGd hδ (by linarith) hGδ hM
    hcond
  exact ⟨2 * k + j, by omega, by omega, by rw [hcoef j]; exact hneg⟩

end

end RHTower
