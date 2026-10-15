import GaloisForLFunctions.RHTower.PolarConeAbelRigidity

/-!
# Polar Weil positivity: fakes have partial sums below `−ε x log x`

Let `lam` be polar Weil-positive (`WeilPositive lam`: Weil positivity on every test with
`f̂(±i/2) = 0`) and write `S(N) = Σ_{2 ≤ n ≤ N} lam(n)`.

**Theorem** (`riemannHypothesis_of_weilPositive_of_primeWeightPartialSum`).  If for every `ε > 0`
eventually `S(N) ≥ −ε N log N`, then RH holds and `lam = Λ` on `n ≥ 2`.

**Corollary** (`frequently_primeWeightPartialSum_lt_of_weilPositive`).  A polar Weil-positive
weight system other than `Λ` has `S(N) < −ε N log N` for some `ε > 0` and infinitely many `N`.

So a polar fake carries a negative double pole of exact size: its partial sums reach
`−ε N log N`.  Polar positivity alone gives the upper side of this scale (the log-density
ceiling), so `N log N` is the only scale on which a fake can live.

Proof.  By partial summation `F(s) = Σ_{n≥2} lam(n) n^{−1−s} = (1 + s) ∫_1^∞ S(⌊t⌋) t^{−s−2} dt`
(`oddDirichlet_eq_integral`), and `∫_1^∞ log t · t^{−s−1} dt = 1/s²`.  A lower bound
`S(N) ≥ −K − ε N log N` gives `s² F(s) ≥ −K s² − ε (1 + s)`, which is the hypothesis "no negative
double pole" of the polar Abel rigidity (`riemannHypothesis_of_weilPositive_of_abel`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilPoleWeight

/-! ## A Mellin integral -/

theorem integrableOn_log_mul_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => Real.log t * t ^ (-σ - 1)) (Ioi 1) := by
  refine ((integrableOn_log_sq_mul_rpow_neg hσ).add
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ - 1 < -1) one_pos)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : t ≠ 0 := by have : (1 : ℝ) < t := ht; linarith
    exact ((Real.continuousAt_log ht0).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl ht0))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hp : 0 < t ^ (-σ - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_of_nonneg (mul_nonneg hl0 hp.le), Pi.add_apply]
    have : Real.log t ≤ Real.log t ^ 2 + 1 := by nlinarith
    nlinarith

theorem integral_Ioi_one_log_mul_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (1 : ℝ), Real.log t * t ^ (-σ - 1) = 1 / σ ^ 2 := by
  set F : ℝ → ℝ := fun t => -(t ^ (-σ)) * (Real.log t / σ + 1 / σ ^ 2) with hF
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt F (Real.log x * x ^ (-σ - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) < x := hx; linarith
    have hr := Real.hasDerivAt_rpow_const (x := x) (p := -σ) (Or.inl hx0)
    have hl := Real.hasDerivAt_log hx0
    have hP : HasDerivAt (fun t => Real.log t / σ + 1 / σ ^ 2) (x⁻¹ / σ) x :=
      (hl.div_const σ).add_const _
    refine (hr.neg.mul hP).congr_deriv ?_
    rw [Real.rpow_sub_one hx0]
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 1) 1 := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (-σ)) 1 :=
      Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
    have hlog : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    exact (hc.neg.mul ((hlog.div_const _).add continuousAt_const)).continuousWithinAt
  have htend : Tendsto F atTop (𝓝 0) := by
    have h1 := tendsto_log_pow_mul_rpow_neg hσ 1
    have h0 := tendsto_log_pow_mul_rpow_neg hσ 0
    have hsum := (h1.div_const σ).add (h0.const_mul (1 / σ ^ 2))
    simp only [zero_div, mul_zero, add_zero] at hsum
    have hneg := hsum.neg
    rw [neg_zero] at hneg
    refine hneg.congr fun t => ?_
    simp only [hF, pow_one, pow_zero, one_mul]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_log_mul_rpow_neg hσ) htend]
  simp only [hF, Real.one_rpow, Real.log_one, zero_div, zero_add]
  ring

/-! ## Partial summation -/

theorem sum_Icc_lamC_eq (lam : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, WeilHerglotz.lamC lam k =
      ((WeilSpectral.primeWeightPartialSum lam N : ℝ) : ℂ) := by
  unfold WeilSpectral.primeWeightPartialSum
  rw [Complex.ofReal_sum]
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := fun k hk =>
    Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
  rw [Finset.sum_subset hsub fun k hk hk' => ?_]
  · rfl
  · have hk0 : k = 0 := by
      simp only [Finset.mem_Icc, not_and, not_le, Finset.mem_range] at hk hk'
      omega
    subst hk0
    simp [WeilHerglotz.lamC]

theorem abs_primeWeightPartialSum_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |WeilSpectral.primeWeightPartialSum lam N| ≤ C * (N : ℝ) ^ r := by
  have hsT := hsl r hr
  refine ⟨∑' n : ℕ, |lam n| / (n : ℝ) ^ r, tsum_nonneg fun n => by positivity, fun N => ?_⟩
  unfold WeilSpectral.primeWeightPartialSum
  calc |∑ m ∈ Finset.range (N + 1), if 2 ≤ m then lam m else 0|
      ≤ ∑ m ∈ Finset.range (N + 1), |lam m| / (m : ℝ) ^ r * (N : ℝ) ^ r := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        split_ifs with h
        · have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
          have hmN : (m : ℝ) ≤ N := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          have hp : (m : ℝ) ^ r ≤ (N : ℝ) ^ r := Real.rpow_le_rpow hm0.le hmN (by linarith)
          have hp0 : 0 < (m : ℝ) ^ r := Real.rpow_pos_of_pos hm0 _
          rw [div_mul_eq_mul_div, le_div_iff₀ hp0]
          exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        · simp only [abs_zero]; positivity
    _ = (∑ m ∈ Finset.range (N + 1), |lam m| / (m : ℝ) ^ r) * (N : ℝ) ^ r := by
        rw [Finset.sum_mul]
    _ ≤ (∑' n : ℕ, |lam n| / (n : ℝ) ^ r) * (N : ℝ) ^ r := by
        gcongr
        exact hsT.sum_le_tsum _ (fun n _ => by positivity)

theorem isBigO_sum_lamC {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {r : ℝ} (hr : 1 < r) :
    (fun n => ∑ k ∈ Finset.Icc 1 n, WeilHerglotz.lamC lam k) =O[atTop]
      fun n => (n : ℝ) ^ r := by
  obtain ⟨C, -, hC⟩ := abs_primeWeightPartialSum_le hsl hr
  refine Asymptotics.IsBigO.of_bound C (Eventually.of_forall fun N => ?_)
  rw [sum_Icc_lamC_eq, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ r)]
  exact hC N

/-- **Partial summation:** `F(s) = (1 + s) ∫_1^∞ S(⌊t⌋) t^{−s−2} dt`. -/
theorem oddDirichlet_eq_integral {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℝ} (hs : 0 < s) :
    oddDirichlet lam s = (1 + s) * ∫ t in Ioi (1 : ℝ),
      WeilSpectral.primeWeightPartialSum lam ⌊t⌋₊ * t ^ (-s - 2) := by
  have hrep := LSeries_eq_mul_integral (WeilHerglotz.lamC lam) (r := 1 + s / 2) (by positivity)
    (s := 1 + (s : ℂ)) (by simp; linarith)
    (by simpa using WeilLineIntegral.lseriesSummable_lamC hsl (c := 1 + s) (by linarith))
    (isBigO_sum_lamC hsl (by linarith))
  have hpt : Set.EqOn (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, WeilHerglotz.lamC lam k) *
      (t : ℂ) ^ (-(1 + (s : ℂ) + 1)))
      (fun t => ((WeilSpectral.primeWeightPartialSum lam ⌊t⌋₊ * t ^ (-s - 2) : ℝ) : ℂ))
      (Ioi 1) := by
    intro t ht
    have ht0 : 0 ≤ t := by have : (1 : ℝ) < t := ht; linarith
    simp only
    rw [sum_Icc_lamC_eq, show -(1 + (s : ℂ) + 1) = ((-s - 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0]
    push_cast
    ring
  have h := (LSeries_lamC_eq_oddDirichlet lam s).symm.trans hrep
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal] at h
  exact_mod_cast h

/-- **Lower bound from partial sums:** `S(N) ≥ −K − ε N log N` gives `F(s) ≥ −K − ε(1+s)/s²`. -/
theorem oddDirichlet_ge_of_primeWeightPartialSum_ge {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {K ε : ℝ}
    (hε : 0 ≤ ε)
    (hS : ∀ N : ℕ, 1 ≤ N →
      -K - ε * (N * Real.log N) ≤ WeilSpectral.primeWeightPartialSum lam N)
    {s : ℝ} (hs : 0 < s) :
    -K - ε * (1 + s) / s ^ 2 ≤ oddDirichlet lam s := by
  rw [oddDirichlet_eq_integral hsl hs]
  set f : ℝ → ℝ := fun t => WeilSpectral.primeWeightPartialSum lam ⌊t⌋₊ * t ^ (-s - 2)
    with hf
  set g : ℝ → ℝ := fun t => -K * t ^ (-(1 + s) - 1) - ε * (Real.log t * t ^ (-s - 1)) with hg
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-(1 + s) - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have h2 := integrableOn_log_mul_rpow_neg hs
  have hgi : IntegrableOn g (Ioi 1) := (h1.const_mul (-K)).sub (h2.const_mul ε)
  obtain ⟨C, hC0, hC⟩ := abs_primeWeightPartialSum_le hsl (show 1 < 1 + s / 2 by linarith)
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 1)) :=
    (((measurable_from_nat (f := fun N => WeilSpectral.primeWeightPartialSum lam N)).comp
      Nat.measurable_floor).mul (measurable_id.pow_const _)).aestronglyMeasurable
  have hfi : IntegrableOn f (Ioi 1) := by
    have hdom : IntegrableOn (fun t : ℝ => C * t ^ (-s / 2 - 1)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine hdom.mono' hfm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hfle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hpow : (⌊t⌋₊ : ℝ) ^ (1 + s / 2) ≤ t ^ (1 + s / 2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hfle (by positivity)
    rw [Real.norm_eq_abs, hf, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc |WeilSpectral.primeWeightPartialSum lam ⌊t⌋₊| * t ^ (-s - 2)
        ≤ C * t ^ (1 + s / 2) * t ^ (-s - 2) := by
          gcongr
          exact (hC _).trans (mul_le_mul_of_nonneg_left hpow hC0)
      _ = C * t ^ (-s / 2 - 1) := by rw [mul_assoc, ← Real.rpow_add ht0]; ring_nf
  have hgf : ∀ t ∈ Ioi (1 : ℝ), g t ≤ f t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hfl : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht1.le
    have hfl' : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfl
    have hfle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hlogle : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log (by linarith) hfle
    have hl0 : 0 ≤ Real.log ⌊t⌋₊ := Real.log_nonneg hfl'
    have hxl : (⌊t⌋₊ : ℝ) * Real.log ⌊t⌋₊ ≤ t * Real.log t :=
      mul_le_mul hfle hlogle hl0 ht0.le
    have hS' : -K - ε * (t * Real.log t) ≤ WeilSpectral.primeWeightPartialSum lam ⌊t⌋₊ := by
      have := hS _ hfl
      nlinarith [mul_le_mul_of_nonneg_left hxl hε]
    have hp : 0 < t ^ (-s - 2) := Real.rpow_pos_of_pos ht0 _
    have he1 : t ^ (-(1 + s) - 1) = t ^ (-s - 2) := by ring_nf
    have he2 : t * t ^ (-s - 2) = t ^ (-s - 1) := by
      rw [show t * t ^ (-s - 2) = t ^ (1 : ℝ) * t ^ (-s - 2) by rw [Real.rpow_one],
        ← Real.rpow_add ht0]
      ring_nf
    have hmul := mul_le_mul_of_nonneg_right hS' hp.le
    simp only [hf, hg, he1]
    calc -K * t ^ (-s - 2) - ε * (Real.log t * t ^ (-s - 1))
        = (-K - ε * (t * Real.log t)) * t ^ (-s - 2) := by
          rw [← he2]; ring
      _ ≤ _ := hmul
  have hJ := setIntegral_mono_on hgi hfi measurableSet_Ioi hgf
  have hJg : ∫ t in Ioi (1 : ℝ), g t = -K / (1 + s) - ε / s ^ 2 := by
    simp only [hg]
    rw [integral_sub (h1.const_mul (-K)) (h2.const_mul ε), integral_const_mul,
      integral_const_mul, integral_Ioi_one_rpow_neg (by linarith : 0 < 1 + s),
      integral_Ioi_one_log_mul_rpow_neg hs]
    ring
  have hs1 : 0 < 1 + s := by linarith
  calc -K - ε * (1 + s) / s ^ 2 = (1 + s) * (-K / (1 + s) - ε / s ^ 2) := by
        field_simp
    _ ≤ (1 + s) * ∫ t in Ioi (1 : ℝ), f t := by
        rw [← hJg]; exact mul_le_mul_of_nonneg_left hJ hs1.le

/-- Partial sums eventually above `−ε N log N` for every `ε > 0` exclude a negative double pole. -/
theorem eventually_neg_le_of_primeWeightPartialSum {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hS : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      -(ε * (N * Real.log N)) ≤ WeilSpectral.primeWeightPartialSum lam N) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hS (ε / 4) (by positivity))
  set K := ∑ N ∈ Finset.range N₀, |WeilSpectral.primeWeightPartialSum lam N| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSall : ∀ N : ℕ, 1 ≤ N →
      -K - ε / 4 * (N * Real.log N) ≤ WeilSpectral.primeWeightPartialSum lam N := by
    intro N hN
    have hlog : 0 ≤ (N : ℝ) * Real.log N :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg N)
    rcases lt_or_ge N N₀ with h | h
    · have h1 := Finset.single_le_sum (f := fun N => |WeilSpectral.primeWeightPartialSum lam N|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr h)
      have h2 := neg_abs_le (WeilSpectral.primeWeightPartialSum lam N)
      have h3 : 0 ≤ ε / 4 * (N * Real.log N) := by positivity
      linarith
    · have := hN₀ N h
      linarith
  have hδpos : 0 < min 1 (ε / (2 * (K + 1))) := lt_min one_pos (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδpos)] with s hs hsδ
  have hs' : 0 < s := hs
  have hs1 : s ≤ 1 := (hsδ.trans_le (min_le_left _ _)).le
  have hsε : s < ε / (2 * (K + 1)) := hsδ.trans_le (min_le_right _ _)
  have hF := oddDirichlet_ge_of_primeWeightPartialSum_ge hsl (by positivity) hSall hs'
  have hs2 : 0 < s ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hF hs2.le
  have e : s ^ 2 * (-K - ε / 4 * (1 + s) / s ^ 2) = -K * s ^ 2 - ε / 4 * (1 + s) := by
    field_simp
  rw [e] at hmul
  have hKs : K * s ^ 2 ≤ ε / 2 := by
    have h1 : s * (2 * (K + 1)) < ε := by rwa [lt_div_iff₀ (by positivity)] at hsε
    have h2 : s ^ 2 ≤ s := by nlinarith
    nlinarith
  have hfin : -ε ≤ -K * s ^ 2 - ε / 4 * (1 + s) := by nlinarith
  calc -ε ≤ s ^ 2 * oddDirichlet lam s := hfin.trans hmul
    _ = s * (s * oddDirichlet lam s) := by ring

/-- **Polar rigidity from partial sums.**  A polar Weil-positive weight system whose partial sums
are eventually above `−ε N log N` for every `ε > 0` is `Λ`, and RH holds. -/
theorem riemannHypothesis_of_weilPositive_of_primeWeightPartialSum {lam : ℕ → ℝ}
    (hW : WeilPositive lam)
    (hS : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      -(ε * (N * Real.log N)) ≤ WeilSpectral.primeWeightPartialSum lam N) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  riemannHypothesis_of_weilPositive_of_abel hW (eventually_neg_le_of_primeWeightPartialSum
    (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositive hW hσ) hS)

/-- **Polar fakes reach `−ε N log N`.**  A polar Weil-positive weight system that differs from `Λ`
at some `n ≥ 2` has partial sums below `−ε N log N` for some `ε > 0` and infinitely many `N`. -/
theorem frequently_primeWeightPartialSum_lt_of_weilPositive {lam : ℕ → ℝ}
    (hW : WeilPositive lam) {n : ℕ} (hn : 2 ≤ n)
    (hne : lam n ≠ ArithmeticFunction.vonMangoldt n) :
    ∃ ε > 0, ∃ᶠ N : ℕ in atTop,
      WeilSpectral.primeWeightPartialSum lam N < -(ε * (N * Real.log N)) := by
  by_contra h
  push Not at h
  exact hne ((riemannHypothesis_of_weilPositive_of_primeWeightPartialSum hW h).2 n hn)

end RHTower.EvenSector

end
