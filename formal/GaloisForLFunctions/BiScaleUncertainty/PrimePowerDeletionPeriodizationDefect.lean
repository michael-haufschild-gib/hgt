import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionSlabTrains

/-!
# The deletion defect is the energy of a periodization

Delete one prime power `m` from the prime-power blind cone, `ℓ = log m`. The deletion price
`|Λ(m) L_m(c)| ≤ w(m) ‖c‖²`, `w(m) = Λ(m)/√m` (`PrimePowerNodeDeletionPrice`), came from the tower
Fejér bound on the spectral side. Here it is an exact identity in the time domain.

**Theorem** (`massOf_add_sign_mul_nodeVector_eq`). For every nonnegative combination `c` blind at
the powers `m^d`, `d ≥ 2`, every test of `c` supported in an interval `(a_f, a_f + L)` and every
`K` with `L < (K+1)ℓ`, and `σ = ±1`:

`‖c‖² + σ √m L_m(c) = Σ_f c_f ∫_{a_f}^{a_f+ℓ} |Σ_{j=0}^{K} σ^j f(u + jℓ)|² du`.

The defect of the deletion bound is the energy of the `σ`-periodization of the tests along
`log m` over one period. Hence `|√m L_m(c)| ≤ ‖c‖²`, and the price `w(m)` (respectively `−w(m)`) is
attained exactly when the `(−1)`-periodization (respectively the plain periodization) of every test
vanishes; then every test is a pair `f = g + g(· − log m)` (respectively `g − g(· − log m)`) of a
continuous `g` supported in an interval shorter by `log m` (`pair_structure_of_stepSum_eq_zero`).
The narrow pairs of `PrimePowerNodeDeletionPrice` are therefore the only extremals.

**Mechanism.** Unfold the period: `∫_a^{a+ℓ} |S|² = Σ_i σ^i ∫_a^{a+ℓ} f(u+iℓ) S̄(u)`, shift the
`i`-th term to `[a+iℓ, a+(i+1)ℓ]`, where `σ^i S(v − iℓ)` is the symmetric periodization
`Σ_{|d|≤K} σ^{|d|} f(v + dℓ)` (`sign_mul_stepSum_eq_fullSum`); the shifted periods tile the support
and the integral becomes `Σ_d σ^{|d|} k_f(−dℓ)`, in which blindness kills `|d| ≥ 2`.
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Periodizations along one lag -/

/-- The one-sided periodization `S(u) = Σ_{j=0}^{K} σ^j f(u + jℓ)`. -/
def stepSum (ℓ σ : ℝ) (K : ℕ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K + 1), ((σ ^ j : ℝ) : ℂ) * f (u + j * ℓ)

/-- The symmetric periodization `Σ_{j=0}^{2K} σ^{j+K} f(v + (j − K)ℓ)`. -/
def fullSum (ℓ σ : ℝ) (K : ℕ) (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (2 * K + 1), ((σ ^ (j + K) : ℝ) : ℂ) * f (v + ((j : ℝ) - K) * ℓ)

theorem continuous_stepSum {f : ℝ → ℂ} (hf : Continuous f) (ℓ σ : ℝ) (K : ℕ) :
    Continuous (stepSum ℓ σ K f) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (hf.comp (continuous_id.add continuous_const))

theorem continuous_fullSum {f : ℝ → ℂ} (hf : Continuous f) (ℓ σ : ℝ) (K : ℕ) :
    Continuous (fullSum ℓ σ K f) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (hf.comp (continuous_id.add continuous_const))

theorem sign_pow_eq {σ : ℝ} (hσ : σ ^ 2 = 1) {i K : ℕ} (hi : i ≤ K) (j : ℕ) :
    σ ^ i * σ ^ j = σ ^ (j + (K - i) + K) := by
  rw [show j + (K - i) + K = (i + j) + 2 * (K - i) by omega, pow_add, pow_mul, hσ, one_pow, mul_one,
    pow_add]

/-- **The shifted period is the symmetric periodization.** On `[a + iℓ, a + (i+1)ℓ]`,
`σ^i S(v − iℓ) = Σ_{j=0}^{2K} σ^{j+K} f(v + (j − K)ℓ)`. -/
theorem sign_mul_stepSum_eq_fullSum {f : ℝ → ℂ} {a L ℓ σ : ℝ} {K : ℕ} (hσ : σ ^ 2 = 1)
    (hℓ : 0 < ℓ) (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L < (K + 1) * ℓ) {i : ℕ}
    (hi : i ≤ K) {v : ℝ} (hv : v ∈ Icc (a + i * ℓ) (a + (i + 1) * ℓ)) :
    ((σ ^ i : ℝ) : ℂ) * stepSum ℓ σ K f (v - i * ℓ) = fullSum ℓ σ K f v := by
  classical
  obtain ⟨hv1, hv2⟩ := hv
  have zero_of : ∀ x : ℝ, (x ≤ a ∨ a + L ≤ x) → f x = 0 := fun x hx => by
    by_contra h
    have := hsupp x h
    rcases hx with hx | hx <;> linarith [this.1, this.2]
  rw [stepSum, Finset.mul_sum, fullSum]
  set φ : ℕ → ℕ := fun j => j + (K - i) with hφ
  have himage : (Finset.range (K + 1)).image φ ⊆ Finset.range (2 * K + 1) := by
    intro j hj
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.mp hj
    simp only [Finset.mem_range] at hj₀ ⊢; simp only [hφ]; omega
  rw [← Finset.sum_subset himage (fun j hj hjn => ?_), Finset.sum_image (fun x _ y _ h => by
    simp only [hφ] at h; omega)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [← mul_assoc, ← Complex.ofReal_mul, sign_pow_eq hσ hi j]
    congr 2
    simp only [hφ]
    push_cast [Nat.cast_sub hi]
    ring
  · -- terms outside the image vanish by the support
    have hj' := Finset.mem_range.mp hj
    have hout : j < K - i ∨ 2 * K - i < j := by
      by_contra hcon
      push Not at hcon
      exact hjn (Finset.mem_image.mpr ⟨j - (K - i), Finset.mem_range.mpr (by omega), by
        simp only [hφ]; omega⟩)
    have hK : ((K : ℝ) + 1) * ℓ = K * ℓ + ℓ := by ring
    rcases hout with h | h
    · have : (j : ℝ) + 1 ≤ (K : ℝ) - i := by
        have : j + 1 ≤ K - i := h
        have := (Nat.cast_le (α := ℝ)).mpr this
        push_cast [Nat.cast_sub hi] at this; linarith
      rw [zero_of _ (Or.inl (by nlinarith)), mul_zero]
    · have : (K : ℝ) - i + 1 ≤ (j : ℝ) - K := by
        have : 2 * K - i + 1 ≤ j := h
        have := (Nat.cast_le (α := ℝ)).mpr this
        push_cast [Nat.cast_sub (show i ≤ 2 * K by omega)] at this; linarith
      rw [zero_of _ (Or.inr (by nlinarith)), mul_zero]

/-- **The one-period identity.** For `f` continuous, supported in `(a, a + L)`, `L < (K+1)ℓ`:
`∫_a^{a+ℓ} |S(u)|² du = Σ_{j=0}^{2K} σ^{j+K} Re ∫ f(v) f̄(v + (j − K)ℓ) dv`. -/
theorem integral_norm_sq_stepSum {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {a L ℓ σ : ℝ} {K : ℕ} (hσ : σ ^ 2 = 1) (hℓ : 0 < ℓ) (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L))
    (hL : L < (K + 1) * ℓ) :
    ∫ u in a..a + ℓ, ‖stepSum ℓ σ K f u‖ ^ 2 =
      ∑ j ∈ Finset.range (2 * K + 1),
        σ ^ (j + K) * (∫ v, f v * conj (f (v + ((j : ℝ) - K) * ℓ))).re := by
  classical
  set S := stepSum ℓ σ K f with hS
  set B := fullSum ℓ σ K f with hB
  have hSc : Continuous S := continuous_stepSum hf ℓ σ K
  have hBc : Continuous B := continuous_fullSum hf ℓ σ K
  have hfB : Continuous fun v => f v * conj (B v) := hf.mul (continuous_conj.comp hBc)
  -- complexify
  have hcplx : ((∫ u in a..a + ℓ, ‖S u‖ ^ 2 : ℝ) : ℂ) = ∫ u in a..a + ℓ, S u * conj (S u) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- unfold the period
  have hunfold : ∫ u in a..a + ℓ, S u * conj (S u) =
      ∑ i ∈ Finset.range (K + 1), ∫ x in (a + i * ℓ)..(a + (i + 1) * ℓ), f x * conj (B x) := by
    have hexp : ∀ u, S u * conj (S u) =
        ∑ i ∈ Finset.range (K + 1), ((σ ^ i : ℝ) : ℂ) * f (u + i * ℓ) * conj (S u) := by
      intro u; rw [hS, stepSum, Finset.sum_mul]
    simp_rw [hexp]
    have hii : ∀ i ∈ Finset.range (K + 1), IntervalIntegrable
        (fun u => ((σ ^ i : ℝ) : ℂ) * f (u + i * ℓ) * conj (S u)) volume a (a + ℓ) := fun i _ =>
      ((continuous_const.mul (hf.comp (continuous_id.add continuous_const))).mul
        (continuous_conj.comp hSc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hii]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hshift := intervalIntegral.integral_comp_add_right
      (fun x => ((σ ^ i : ℝ) : ℂ) * f x * conj (S (x - i * ℓ))) (a := a) (b := a + ℓ) ((i : ℝ) * ℓ)
    simp only [add_sub_cancel_right] at hshift
    rw [hshift, show a + ℓ + (i : ℝ) * ℓ = a + ((i : ℝ) + 1) * ℓ by ring,
      show a + (i : ℝ) * ℓ = a + i * ℓ from rfl]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hle : a + (i : ℝ) * ℓ ≤ a + ((i : ℝ) + 1) * ℓ := by nlinarith
    rw [Set.uIcc_of_le hle] at hx
    have hA : ((σ ^ i : ℝ) : ℂ) * S (x - i * ℓ) = B x :=
      sign_mul_stepSum_eq_fullSum hσ hℓ hsupp hL hiK hx
    rw [← hA, map_mul, Complex.conj_ofReal]
    ring
  -- the shifted periods tile the support
  have htile : ∑ i ∈ Finset.range (K + 1), ∫ x in (a + i * ℓ)..(a + (i + 1) * ℓ), f x * conj (B x) =
      ∫ x, f x * conj (B x) := by
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (f := fun x => f x * conj (B x))
      (μ := volume) (a := fun k : ℕ => a + k * ℓ) (n := K + 1)
      (fun k _ => hfB.intervalIntegrable _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at hadj
    rw [hadj, intervalIntegral.integral_of_le (by nlinarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    by_cases h : f x = 0
    · rw [h, zero_mul]
    · have := hsupp x h
      exact absurd (show x ∈ Ioc a (a + ((K : ℝ) + 1) * ℓ) from ⟨this.1, by linarith [this.2]⟩) hx
  -- expand the symmetric periodization
  have hexpand : ∫ x, f x * conj (B x) = ∑ j ∈ Finset.range (2 * K + 1),
      ((σ ^ (j + K) : ℝ) : ℂ) * ∫ v, f v * conj (f (v + ((j : ℝ) - K) * ℓ)) := by
    have hpt : ∀ x, f x * conj (B x) = ∑ j ∈ Finset.range (2 * K + 1),
        ((σ ^ (j + K) : ℝ) : ℂ) * (f x * conj (f (x + ((j : ℝ) - K) * ℓ))) := by
      intro x
      rw [hB, fullSum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_ofReal]; ring
    simp_rw [hpt]
    have hint : ∀ j ∈ Finset.range (2 * K + 1), Integrable fun x =>
        ((σ ^ (j + K) : ℝ) : ℂ) * (f x * conj (f (x + ((j : ℝ) - K) * ℓ))) := fun j _ =>
      ((hf.mul (continuous_conj.comp (hf.comp (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
        hfc.mul_right).const_mul _
    rw [integral_finsetSum _ hint]
    simp_rw [integral_const_mul]
  have htotal : ((∫ u in a..a + ℓ, ‖S u‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ Finset.range (2 * K + 1),
      ((σ ^ (j + K) : ℝ) : ℂ) * ∫ v, f v * conj (f (v + ((j : ℝ) - K) * ℓ)) := by
    rw [hcplx, hunfold, htile, hexpand]
  have hre := congrArg Complex.re htotal
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul]

/-! ### 2. The deletion identity -/

/-- `Re k_f(−y) = Re k_f(y)`. -/
theorem re_weilTest_neg (f : ℝ → ℂ) (y : ℝ) :
    (EF.weilTest f f (-y)).re = (EF.weilTest f f y).re := by
  rw [WeilSpectral.weilTest_apply, WeilSpectral.weilTest_apply]
  have h : ∫ u, f u * conj (f (u - -y)) = conj (∫ u, f u * conj (f (u - y))) := by
    rw [← integral_conj]
    have := integral_sub_right_eq_self (μ := volume) (fun u => f u * conj (f (u + y))) y
    simp only [sub_add_cancel] at this
    rw [show (fun u => f u * conj (f (u - -y))) = fun u => f u * conj (f (u + y)) from
      funext fun u => by rw [sub_neg_eq_add], ← this]
    congr 1; funext u
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [h, Complex.conj_re]

/-- `∫ f(v) f̄(v + y) dv = k_f(−y)`. -/
theorem integral_mul_conj_add_eq_weilTest (f : ℝ → ℂ) (y : ℝ) :
    ∫ v, f v * conj (f (v + y)) = EF.weilTest f f (-y) := by
  rw [WeilSpectral.weilTest_apply]
  congr 1; funext v; rw [sub_neg_eq_add]

/-- The lag mass `Σ_f c_f Re k_f(y)`. -/
def lagMass (c : WeilTestFn →₀ ℝ) (y : ℝ) : ℝ := c.sum fun f t => t * (EF.weilTest f.1 f.1 y).re

theorem lagMass_neg (c : WeilTestFn →₀ ℝ) (y : ℝ) : lagMass c (-y) = lagMass c y := by
  unfold lagMass
  exact Finsupp.sum_congr fun f _ => by rw [re_weilTest_neg]

theorem lagMass_zero (c : WeilTestFn →₀ ℝ) : lagMass c 0 = massOf c := by
  unfold lagMass
  rw [show massOf c = c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2 from rfl]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [RHTower.weilTest_zero_eq_integral_norm_sq, Complex.ofReal_re]

/-- At the node `n` the lag mass is `√n L_n(c)/2`. -/
theorem lagMass_log (c : WeilTestFn →₀ ℝ) {n : ℕ} (hn : 2 ≤ n) :
    lagMass c (Real.log n) = Real.sqrt n * nodeAt c n / 2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [nodeAt_eq_sum c hn, lagMass, Finsupp.sum, Finsupp.sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [logValue, Complex.add_re, re_weilTest_neg]
  field_simp
  ring

/-- **The one-period identity for a test**, in autocorrelations:
`∫_a^{a+ℓ} |S|² = Σ_{j=0}^{2K} σ^{j+K} Re k_f((j − K)ℓ)`. -/
theorem integral_norm_sq_stepSum_eq (f : WeilTestFn) {a L ℓ σ : ℝ} {K : ℕ} (hσ : σ ^ 2 = 1)
    (hℓ : 0 < ℓ) (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L < (K + 1) * ℓ) :
    ∫ u in a..a + ℓ, ‖stepSum ℓ σ K f.1 u‖ ^ 2 =
      ∑ j ∈ Finset.range (2 * K + 1), σ ^ (j + K) * (EF.weilTest f.1 f.1 (((j : ℝ) - K) * ℓ)).re := by
  rw [integral_norm_sq_stepSum f.2.1.continuous f.2.2 hσ hℓ hsupp hL]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_conj_add_eq_weilTest, re_weilTest_neg]

/-- **The deletion defect is a periodization energy.** For a nonnegative combination blind at the
powers `m^d`, `d ≥ 2`, every test of which lies in an interval `(a_f, a_f + L)`, `L < (K+1) log m`,
`K ≥ 1`, and `σ = ±1`: `‖c‖² + σ √m L_m(c) = Σ_f c_f ∫_{a_f}^{a_f + log m} |S_f|²`. -/
theorem massOf_add_sign_mul_nodeVector_eq {c : WeilTestFn →₀ ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hb : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0)
    {a : WeilTestFn → ℝ} {L : ℝ} (ha : ∀ f ∈ c.support, ∀ u, f.1 u ≠ 0 → u ∈ Ioo (a f) (a f + L))
    {K : ℕ} (hK : 1 ≤ K) (hL : L < (K + 1) * Real.log m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    massOf c + σ * (Real.sqrt m * nodeVector c ⟨m, hm⟩) =
      c.sum fun f t => t * ∫ u in a f..a f + Real.log m, ‖stepSum (Real.log m) σ K f.1 u‖ ^ 2 := by
  classical
  set ℓ := Real.log m with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  -- expand every test
  have hexp : (c.sum fun f t => t * ∫ u in a f..a f + ℓ, ‖stepSum ℓ σ K f.1 u‖ ^ 2) =
      ∑ j ∈ Finset.range (2 * K + 1), σ ^ (j + K) * lagMass c (((j : ℝ) - K) * ℓ) := by
    rw [Finsupp.sum, Finset.sum_congr rfl fun f hf => by
      rw [integral_norm_sq_stepSum_eq f hσ hℓ (ha f hf) hL]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lagMass, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  -- the lag masses: `‖c‖²` at `0`, `√m L_m/2` at `±ℓ`, `0` beyond
  have hpow : ∀ d : ℕ, 1 ≤ d → lagMass c ((d : ℝ) * ℓ) = Real.sqrt ((m ^ d : ℕ) : ℝ) *
      nodeAt c (m ^ d) / 2 := by
    intro d hd
    have h2 : 2 ≤ m ^ d := le_trans hm (Nat.le_self_pow (by omega) m)
    rw [← lagMass_log c h2]
    congr 1
    rw [hℓdef, Nat.cast_pow, Real.log_pow]
  have hblind : ∀ d : ℕ, 2 ≤ d → lagMass c ((d : ℝ) * ℓ) = 0 := by
    intro d hd
    have h2 : 2 ≤ m ^ d := le_trans hm (Nat.le_self_pow (by omega) m)
    rw [hpow d (by omega), nodeAt, dif_pos h2, hb ⟨m ^ d, h2⟩ ⟨d, hd, rfl⟩, mul_zero, zero_div]
  have hone : lagMass c ℓ = Real.sqrt m * nodeVector c ⟨m, hm⟩ / 2 := by
    have := hpow 1 le_rfl
    rw [Nat.cast_one, one_mul, pow_one] at this
    rw [this, nodeAt, dif_pos hm]
  have hlag : ∀ j ∈ Finset.range (2 * K + 1), σ ^ (j + K) * lagMass c (((j : ℝ) - K) * ℓ) =
      if j = K then massOf c else if j = K - 1 ∨ j = K + 1 then
        σ * (Real.sqrt m * nodeVector c ⟨m, hm⟩ / 2) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases h0 : j = K
    · subst h0
      rw [if_pos rfl, sub_self, zero_mul, lagMass_zero, ← two_mul, pow_mul, hσ, one_pow, one_mul]
    rw [if_neg h0]
    by_cases h1 : j = K - 1 ∨ j = K + 1
    · rw [if_pos h1]
      rcases h1 with rfl | rfl
      · have e : (((K - 1 : ℕ) : ℝ) - K) * ℓ = -ℓ := by
          rw [Nat.cast_sub hK]; push_cast; ring
        rw [e, lagMass_neg, hone, show K - 1 + K = 2 * (K - 1) + 1 by omega, pow_succ, pow_mul, hσ,
          one_pow, one_mul]
      · have e : (((K + 1 : ℕ) : ℝ) - K) * ℓ = ℓ := by push_cast; ring
        rw [e, hone, show K + 1 + K = 2 * K + 1 by omega, pow_succ, pow_mul, hσ, one_pow, one_mul]
    · rw [if_neg h1]
      rcases Nat.lt_or_ge j K with hlt | hge
      · have e : ((j : ℝ) - K) * ℓ = -(((K - j : ℕ) : ℝ) * ℓ) := by
          rw [Nat.cast_sub hlt.le]; ring
        rw [e, lagMass_neg, hblind (K - j) (by omega), mul_zero]
      · have e : ((j : ℝ) - K) * ℓ = ((j - K : ℕ) : ℝ) * ℓ := by rw [Nat.cast_sub hge]
        rw [e, hblind (j - K) (by omega), mul_zero]
  rw [hexp, Finset.sum_congr rfl hlag]
  -- three surviving terms
  set F : ℕ → ℝ := fun j => if j = K then massOf c else if j = K - 1 ∨ j = K + 1 then
    σ * (Real.sqrt m * nodeVector c ⟨m, hm⟩ / 2) else 0 with hF
  have hsub : ({K - 1, K, K + 1} : Finset ℕ) ⊆ Finset.range (2 * K + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub (fun j _ hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp only [if_neg hj.2.1, if_neg (show ¬(j = K - 1 ∨ j = K + 1) by omega)])]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  simp only [if_neg (show K - 1 ≠ K by omega), if_neg (show K + 1 ≠ K by omega),
    true_or, or_true, if_true]
  ring

/-! ### 3. Extremals -/

/-- **At an extreme the periodization of every test vanishes.** If `‖c‖² + σ √m L_m(c) = 0` then the
`σ`-periodization of every test of `c` vanishes on its period `[a_f, a_f + log m]`. -/
theorem stepSum_eq_zero_of_extremal {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ} (hm : 2 ≤ m)
    (hb : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0)
    {a : WeilTestFn → ℝ} {L : ℝ} (ha : ∀ f ∈ c.support, ∀ u, f.1 u ≠ 0 → u ∈ Ioo (a f) (a f + L))
    {K : ℕ} (hK : 1 ≤ K) (hL : L < (K + 1) * Real.log m) {σ : ℝ} (hσ : σ ^ 2 = 1)
    (hext : massOf c + σ * (Real.sqrt m * nodeVector c ⟨m, hm⟩) = 0) :
    ∀ f ∈ c.support, ∀ u ∈ Icc (a f) (a f + Real.log m), stepSum (Real.log m) σ K f.1 u = 0 := by
  classical
  set ℓ := Real.log m with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hid := massOf_add_sign_mul_nodeVector_eq hm hb ha hK hL hσ
  rw [hext, Finsupp.sum] at hid
  have hnn : ∀ f ∈ c.support, 0 ≤ c f * ∫ u in a f..a f + ℓ, ‖stepSum ℓ σ K f.1 u‖ ^ 2 := fun f _ =>
    mul_nonneg (hc f) (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)
  intro f hf u hu
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hid.symm f hf
  have hcf : 0 < c f := lt_of_le_of_ne (hc f) (Ne.symm (Finsupp.mem_support_iff.mp hf))
  have hint : ∫ u in a f..a f + ℓ, ‖stepSum ℓ σ K f.1 u‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hcf.ne'
    · exact h
  have hSc : Continuous (stepSum ℓ σ K f.1) := continuous_stepSum f.2.1.continuous ℓ σ K
  have hgc : Continuous fun u => ‖stepSum ℓ σ K f.1 u‖ ^ 2 := (continuous_norm.comp hSc).pow 2
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (by linarith)
    (Eventually.of_forall fun _ => sq_nonneg _) (hgc.intervalIntegrable _ _)).mp hint
  have hIoc := Measure.eqOn_Ioc_of_ae_eq volume hae hgc.continuousOn continuousOn_const
  have hIcc : Set.EqOn (fun u => ‖stepSum ℓ σ K f.1 u‖ ^ 2) (fun _ => (0 : ℝ))
      (Icc (a f) (a f + ℓ)) :=
    hIoc.of_subset_closure hgc.continuousOn continuousOn_const Ioc_subset_Icc_self
      (by rw [closure_Ioc (by linarith)])
  have h0 := hIcc hu
  simp only [pow_eq_zero_iff (two_ne_zero), norm_eq_zero] at h0
  exact h0

/-- The backward periodization `Σ_{j=0}^{K} σ^j f(u − jℓ)`. -/
def backSum (ℓ σ : ℝ) (K : ℕ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K + 1), ((σ ^ j : ℝ) : ℂ) * f (u - j * ℓ)

theorem continuous_backSum {f : ℝ → ℂ} (hf : Continuous f) (ℓ σ : ℝ) (K : ℕ) :
    Continuous (backSum ℓ σ K f) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (hf.comp (continuous_id.sub continuous_const))

/-- Telescoping: `B(u) − σ B(u − ℓ) = f(u) − σ^{K+1} f(u − (K+1)ℓ)`. -/
theorem backSum_sub_sign_mul (f : ℝ → ℂ) (ℓ σ : ℝ) (K : ℕ) (u : ℝ) :
    backSum ℓ σ K f u - (σ : ℂ) * backSum ℓ σ K f (u - ℓ) =
      f u - ((σ ^ (K + 1) : ℝ) : ℂ) * f (u - (K + 1) * ℓ) := by
  unfold backSum
  rw [Finset.sum_range_succ', Finset.mul_sum, Finset.sum_range_succ]
  have h : ∀ j ∈ Finset.range K, ((σ ^ (j + 1) : ℝ) : ℂ) * f (u - ((j + 1 : ℕ) : ℝ) * ℓ) =
      (σ : ℂ) * (((σ ^ j : ℝ) : ℂ) * f (u - ℓ - (j : ℝ) * ℓ)) := fun j _ => by
    push_cast; rw [show u - ((j : ℝ) + 1) * ℓ = u - ℓ - (j : ℝ) * ℓ by ring]; ring
  rw [Finset.sum_congr rfl h]
  push_cast
  rw [show u - ℓ - (K : ℝ) * ℓ = u - ((K : ℝ) + 1) * ℓ by ring]
  ring_nf

/-- **The backward periodization vanishes past the shortened support.** -/
theorem backSum_eq_zero_of_stepSum {f : ℝ → ℂ} {a L ℓ σ : ℝ} {K : ℕ} (hσ : σ ^ 2 = 1) (hℓ : 0 < ℓ)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L < (K + 1) * ℓ)
    (hS : ∀ u ∈ Icc a (a + ℓ), stepSum ℓ σ K f u = 0) {u : ℝ} (hu1 : a + L - ℓ ≤ u) (hu2 : u ≤ a + L) :
    backSum ℓ σ K f u = 0 := by
  classical
  have zero_of : ∀ x : ℝ, (x ≤ a ∨ a + L ≤ x) → f x = 0 := fun x hx => by
    by_contra h
    have := hsupp x h
    rcases hx with hx | hx <;> linarith [this.1, this.2]
  by_cases hua : u ≤ a
  · unfold backSum
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zero_of _ (Or.inl (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])), mul_zero]
  push Not at hua
  set n := ⌊(u - a) / ℓ⌋₊ with hn
  have hq : 0 ≤ (u - a) / ℓ := div_nonneg (by linarith) hℓ.le
  have hn1 : (n : ℝ) ≤ (u - a) / ℓ := Nat.floor_le hq
  have hn2 : (u - a) / ℓ < n + 1 := Nat.lt_floor_add_one _
  have hn1' : (n : ℝ) * ℓ ≤ u - a := by rwa [le_div_iff₀ hℓ] at hn1
  have hn2' : u - a < ((n : ℝ) + 1) * ℓ := by rwa [div_lt_iff₀ hℓ] at hn2
  have hnK : n ≤ K := by
    have : ((n : ℝ)) < K + 1 := by
      have : (n : ℝ) * ℓ < (K + 1) * ℓ := by linarith
      exact lt_of_mul_lt_mul_right this hℓ.le
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  set u' := u - n * ℓ with hu'
  have hu'mem : u' ∈ Icc a (a + ℓ) := ⟨by linarith, by linarith⟩
  -- the forward sum at `u'` is a sum over `i ≤ n`
  have hfwd : ∑ i ∈ Finset.range (n + 1), ((σ ^ i : ℝ) : ℂ) * f (u' + i * ℓ) = 0 := by
    have h := hS u' hu'mem
    unfold stepSum at h
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : n + 1 ≤ K + 1))
      (fun i hi hin => by
        have hi' : n + 1 ≤ i := by simpa using hin
        have : ((n : ℝ) + 1) ≤ i := by exact_mod_cast hi'
        rw [zero_of _ (Or.inr (by nlinarith)), mul_zero])] at h
    exact h
  -- the backward sum at `u` is the reflected sum over `j ≤ n`
  unfold backSum
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : n + 1 ≤ K + 1))
    (fun j hj hjn => by
      have hj' : n + 1 ≤ j := by simpa using hjn
      have : ((n : ℝ) + 1) ≤ j := by exact_mod_cast hj'
      rw [zero_of _ (Or.inl (by nlinarith)), mul_zero])]
  rw [← Finset.sum_range_reflect]
  have hrefl : ∀ j ∈ Finset.range (n + 1), ((σ ^ (n + 1 - 1 - j) : ℝ) : ℂ) *
      f (u - ((n + 1 - 1 - j : ℕ) : ℝ) * ℓ) =
      ((σ ^ n : ℝ) : ℂ) * (((σ ^ j : ℝ) : ℂ) * f (u' + j * ℓ)) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : σ ^ (n + 1 - 1 - j) = σ ^ n * σ ^ j := by
      rw [← pow_add, show n + j = (n + 1 - 1 - j) + 2 * j by omega, pow_add, pow_mul, hσ, one_pow,
        mul_one]
    rw [hpow, show n + 1 - 1 - j = n - j by omega, Nat.cast_sub hjn, hu']
    push_cast
    rw [show u - ((n : ℝ) - j) * ℓ = u - n * ℓ + j * ℓ by ring]
    ring
  rw [Finset.sum_congr rfl hrefl, ← Finset.mul_sum, hfwd, mul_zero]

/-- **Pair structure of the extremals.** If the `σ`-periodization of a test supported in
`(a, a + L)` vanishes on one period, then `f = g − σ g(· − ℓ)` for a continuous `g` supported in
`(a, a + L − ℓ)`: for `σ = −1` a pair `g + g(· − ℓ)`, for `σ = 1` an antipair. -/
theorem pair_structure_of_stepSum_eq_zero {f : ℝ → ℂ} (hf : Continuous f) {a L ℓ σ : ℝ} {K : ℕ}
    (hσ : σ ^ 2 = 1) (hℓ : 0 < ℓ) (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L))
    (hL : L < (K + 1) * ℓ) (hS : ∀ u ∈ Icc a (a + ℓ), stepSum ℓ σ K f u = 0) :
    ∃ g : ℝ → ℂ, Continuous g ∧ (∀ u, g u ≠ 0 → u ∈ Ioo a (a + L - ℓ)) ∧
      ∀ u, f u = g u - (σ : ℂ) * g (u - ℓ) := by
  classical
  have zero_of : ∀ x : ℝ, (x ≤ a ∨ a + L ≤ x) → f x = 0 := fun x hx => by
    by_contra h
    have := hsupp x h
    rcases hx with hx | hx <;> linarith [this.1, this.2]
  set B := backSum ℓ σ K f with hBdef
  have hvan : ∀ u, a + L - ℓ ≤ u → u ≤ a + L → B u = 0 := fun u h1 h2 =>
    backSum_eq_zero_of_stepSum hσ hℓ hsupp hL hS h1 h2
  have hlow : ∀ u, u ≤ a → B u = 0 := fun u hu => by
    simp only [hBdef, backSum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zero_of _ (Or.inl (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])), mul_zero]
  refine ⟨fun u => B (min u (a + L)), (continuous_backSum hf ℓ σ K).comp
    (continuous_id.min continuous_const), fun u hu => ?_, fun u => ?_⟩
  · simp only at hu
    constructor
    · by_contra h; push Not at h
      exact hu (hlow _ ((min_le_left _ _).trans h))
    · by_contra h; push Not at h
      exact hu (hvan _ (le_min h (by linarith)) (min_le_right _ _))
  · simp only
    rcases le_or_gt u (a + L) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
      have := backSum_sub_sign_mul f ℓ σ K u
      rw [zero_of (u - (K + 1) * ℓ) (Or.inl (by nlinarith)), mul_zero, sub_zero] at this
      exact this.symm
    · rw [min_eq_right h.le, hvan _ (by linarith) le_rfl, zero_of u (Or.inr h.le), zero_sub]
      rcases le_or_gt (u - ℓ) (a + L) with h' | h'
      · rw [min_eq_left h', hvan _ (by linarith) h', mul_zero, neg_zero]
      · rw [min_eq_right h'.le, hvan _ (by linarith) le_rfl, mul_zero, neg_zero]

/-! ### 4. The extremals of the deletion price -/

theorem exists_period_count {L ℓ : ℝ} (hℓ : 0 < ℓ) : ∃ K : ℕ, 1 ≤ K ∧ L < (K + 1) * ℓ := by
  refine ⟨⌈L / ℓ⌉₊ + 1, by omega, ?_⟩
  have h1 : L / ℓ ≤ ⌈L / ℓ⌉₊ := Nat.le_ceil _
  have h2 : L ≤ ⌈L / ℓ⌉₊ * ℓ := by rwa [div_le_iff₀ hℓ] at h1
  push_cast
  nlinarith

/-- **The price `w(m)` is attained only by pairs.** If a nonnegative combination blind at the powers
`m^d`, `d ≥ 2`, attains `√m L_m(c) = ‖c‖²`, then every test of `c` is a pair `g + g(· − log m)` of a
continuous `g` supported in an interval shorter by `log m`. -/
theorem pair_structure_of_price_attained {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ}
    (hm : 2 ≤ m) (hb : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0)
    {a : WeilTestFn → ℝ} {L : ℝ} (ha : ∀ f ∈ c.support, ∀ u, f.1 u ≠ 0 → u ∈ Ioo (a f) (a f + L))
    (hext : Real.sqrt m * nodeVector c ⟨m, hm⟩ = massOf c) :
    ∀ f ∈ c.support, ∃ g : ℝ → ℂ, Continuous g ∧
      (∀ u, g u ≠ 0 → u ∈ Ioo (a f) (a f + L - Real.log m)) ∧
        ∀ u, f.1 u = g u + g (u - Real.log m) := by
  intro f hf
  have hℓ : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  obtain ⟨K, hK, hL⟩ := exists_period_count (L := L) hℓ
  have hzero := stepSum_eq_zero_of_extremal hc hm hb ha hK hL (σ := -1) (by norm_num)
    (by rw [hext]; ring) f hf
  obtain ⟨g, hg, hgs, hgf⟩ := pair_structure_of_stepSum_eq_zero f.2.1.continuous (σ := -1)
    (by norm_num) hℓ (ha f hf) hL hzero
  refine ⟨g, hg, hgs, fun u => ?_⟩
  rw [hgf u]; push_cast; ring

/-- **The price `−w(m)` is attained only by antipairs** `g − g(· − log m)`. -/
theorem antipair_structure_of_price_attained {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ}
    (hm : 2 ≤ m) (hb : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0)
    {a : WeilTestFn → ℝ} {L : ℝ} (ha : ∀ f ∈ c.support, ∀ u, f.1 u ≠ 0 → u ∈ Ioo (a f) (a f + L))
    (hext : Real.sqrt m * nodeVector c ⟨m, hm⟩ = -massOf c) :
    ∀ f ∈ c.support, ∃ g : ℝ → ℂ, Continuous g ∧
      (∀ u, g u ≠ 0 → u ∈ Ioo (a f) (a f + L - Real.log m)) ∧
        ∀ u, f.1 u = g u - g (u - Real.log m) := by
  intro f hf
  have hℓ : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  obtain ⟨K, hK, hL⟩ := exists_period_count (L := L) hℓ
  have hzero := stepSum_eq_zero_of_extremal hc hm hb ha hK hL (σ := 1) (by norm_num)
    (by rw [hext]; ring) f hf
  obtain ⟨g, hg, hgs, hgf⟩ := pair_structure_of_stepSum_eq_zero f.2.1.continuous (σ := 1)
    (by norm_num) hℓ (ha f hf) hL hzero
  refine ⟨g, hg, hgs, fun u => ?_⟩
  rw [hgf u]; push_cast; ring

end

end GaloisForLFunctions.BiScaleUncertainty
