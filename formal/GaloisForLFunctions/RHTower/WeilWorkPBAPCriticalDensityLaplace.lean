import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalAbel
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalLaplace

/-!
# The harmonic resonator ceiling in the Dirichlet half-plane

The signed convolution is evaluated through its actual absolutely convergent
series. The cumulative upper bound never requires individual coefficient signs.
-/

open MeasureTheory Filter Topology Set Real
open scoped ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The weight of one integer-product pair in the harmonic cumulative sum. -/
def harmonicPairWeight (lam : ℕ → ℝ) (q : ℕ × ℕ) : ℝ :=
  if 2 ≤ q.1 ∧ 1 ≤ q.2 then lam q.1 / ((q.1 : ℝ) * q.2) else 0

def harmonicPairLevel (q : ℕ × ℕ) : ℝ := log ((q.1 : ℝ) * q.2)

theorem harmonicPairLevel_nonneg (q : ℕ × ℕ) : 0 ≤ harmonicPairLevel q := by
  by_cases hn : q.1 = 0
  · simp [harmonicPairLevel, hn]
  by_cases hm : q.2 = 0
  · simp [harmonicPairLevel, hm]
  apply Real.log_nonneg
  have hn1 : (1:ℝ) ≤ q.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hm1 : (1:ℝ) ≤ q.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  nlinarith

/-- The cumulative function is exactly the finite harmonic density already bounded by resonators. -/
theorem signedCumulative_harmonicPair (lam : ℕ → ℝ) (t : ℝ) :
    signedCumulative (harmonicPairWeight lam) harmonicPairLevel t =
      harmonicDensity lam ⌊exp t⌋₊ := by
  classical
  let N := ⌊exp t⌋₊
  have hcut (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
      log ((n:ℝ)*m) ≤ t ↔ n*m ≤ N := by
    have hpos : 0 < (n:ℝ)*m := mul_pos (by exact_mod_cast (by omega : 0 < n))
      (by exact_mod_cast (by omega : 0 < m))
    rw [Real.log_le_iff_le_exp hpos, Nat.le_floor_iff (exp_pos t).le]
    norm_cast
  rw [signedCumulative, tsum_eq_sum (s := (Finset.Icc 2 N).product (Finset.Icc 1 N))]
  · refine (Finset.sum_product (Finset.Icc 2 N) (Finset.Icc 1 N)
      (fun q : ℕ × ℕ => if harmonicPairLevel q ≤ t then harmonicPairWeight lam q else 0)).trans ?_
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    simp only [harmonicPairWeight, harmonicPairLevel,
      (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hm).1, and_self, if_true]
    simp only [hcut n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1, N]
  · rintro ⟨n,m⟩ hq
    by_cases hn : 2 ≤ n
    · by_cases hm : 1 ≤ m
      · have hnmlt : ¬ n*m ≤ N := by
          intro hnm
          have hnN : n ≤ N := by nlinarith [Nat.mul_le_mul_left n hm]
          have hmN : m ≤ N := by
            nlinarith [Nat.mul_le_mul_right m (show 1 ≤ n by omega)]
          exact hq (Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨hn,hnN⟩, Finset.mem_Icc.mpr ⟨hm,hmN⟩⟩)
        simp only [harmonicPairLevel, (hcut n m hn hm), if_neg hnmlt]
      · simp [harmonicPairWeight, hm]
    · simp [harmonicPairWeight, hn]

/-- Individual pair transform, including the zero indices. -/
theorem harmonicPair_transform (lam : ℕ → ℝ) {s : ℝ} (hs : 0 < s) (q : ℕ × ℕ) :
    harmonicPairWeight lam q * exp (-s*harmonicPairLevel q) =
      ((if 2 ≤ q.1 then lam q.1 else 0) * (q.1 : ℝ)^(-(1+s))) *
        (q.2 : ℝ)^(-(1+s)) := by
  rcases q with ⟨n,m⟩
  by_cases hn : 2 ≤ n
  · by_cases hm : 1 ≤ m
    · have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hmpos : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
      have he : exp (-s * log ((n:ℝ)*m)) = ((n:ℝ)*m)^(-s) := by
        rw [Real.rpow_def_of_pos (mul_pos hnpos hmpos)]
        congr 1
        ring
      simp only [harmonicPairWeight, harmonicPairLevel, hn, hm, and_self, if_true]
      rw [he, Real.mul_rpow hnpos.le hmpos.le,
        show -(1+s) = (-1:ℝ)+(-s) by ring,
        Real.rpow_add hnpos, Real.rpow_add hmpos, Real.rpow_neg_one, Real.rpow_neg_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · have hm0 : m=0 := by omega
      subst m
      have hzpow : (0:ℝ)^(-(1+s)) = 0 := Real.zero_rpow (by linarith : -(1+s) ≠ 0)
      simp only [Nat.cast_zero, hzpow, mul_zero]
      simp [harmonicPairWeight]
  · simp [harmonicPairWeight, hn]

/-- The pair transform is absolutely summable at every positive Laplace parameter. -/
theorem summable_harmonicPair_transform {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {s : ℝ} (hs : 0 < s) :
    Summable fun q : ℕ × ℕ => |harmonicPairWeight lam q| * exp (-s*harmonicPairLevel q) := by
  have hn := summable_critical_abs_terms ha h (by linarith : 1 < 1+s)
  have hm : Summable fun m : ℕ => (m:ℝ)^(-(1+s)) := Real.summable_nat_rpow.mpr (by linarith)
  have hp := hn.mul_of_nonneg hm (fun _ => by positivity) (fun _ => Real.rpow_nonneg (by positivity) _)
  apply hp.congr
  intro q
  have he := congrArg abs (harmonicPair_transform lam hs q)
  simpa only [abs_mul, abs_of_pos (exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q.1) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q.2) _)] using he.symm

/-- Exact product of the two actual Dirichlet series. -/
theorem tsum_harmonicPair_transform {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {s : ℝ} (hs : 0 < s) :
    (∑' q : ℕ × ℕ, harmonicPairWeight lam q * exp (-s*harmonicPairLevel q)) =
      criticalDirichletReal lam (1+s) * ∑' m : ℕ, (m:ℝ)^(-(1+s)) := by
  have hnabs : Summable fun n : ℕ =>
      ‖(if 2 ≤ n then lam n else 0) * (n:ℝ)^(-(1+s))‖ := by
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      summable_critical_abs_terms ha h (by linarith : 1 < 1+s)
  have hm : Summable fun m : ℕ => (m:ℝ)^(-(1+s)) := Real.summable_nat_rpow.mpr (by linarith)
  have hmabs : Summable fun m : ℕ => ‖(m:ℝ)^(-(1+s))‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hm
  simp_rw [harmonicPair_transform lam hs]
  exact (tsum_mul_tsum_of_summable_norm hnabs hmabs).symm

/-- The sharp harmonic ceiling yields a sharp Abel ceiling with a vanishing constant error. -/
theorem critical_dirichlet_product_ceiling {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s →
      s^2 * (criticalDirichletReal lam (1+s) * ∑' m : ℕ, (m:ℝ)^(-(1+s))) ≤
        a + 2*ε + M*s^2 := by
  let K := a*resonatorGammaConstant+C
  let M := max (K/2+(a+K)^2/(16*ε)) 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M,hM,fun s hs => ?_⟩
  have hu : ∀ t : ℝ, 0 ≤ t →
      signedCumulative (harmonicPairWeight lam) harmonicPairLevel t ≤ (a/2+ε)*t^2+M := by
    intro t ht
    rw [signedCumulative_harmonicPair]
    have hN : 1 ≤ ⌊exp t⌋₊ := (Nat.le_floor_iff (exp_pos t).le).mpr (by simpa using Real.one_le_exp_iff.mpr ht)
    have hlog0 : 0 ≤ log (⌊exp t⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlog : log (⌊exp t⌋₊ : ℝ) ≤ t :=
      (Real.log_le_iff_le_exp (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))).mpr
        (Nat.floor_le (exp_pos t).le)
    have hb := critical_harmonic_eps_ceiling ha h ⌊exp t⌋₊ hN hε
    have hsquare : (log (⌊exp t⌋₊ : ℝ))^2 ≤ t^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ a/2+ε by positivity)
    have hrem : K/2+(a+K)^2/(16*ε) ≤ M := le_max_left _ _
    change harmonicDensity lam ⌊exp t⌋₊ ≤ (a/2+ε)*(log (⌊exp t⌋₊ : ℝ))^2+K/2+(a+K)^2/(16*ε) at hb
    linarith
  have hc := signedCumulative_laplace_ceiling (harmonicPairWeight lam) harmonicPairLevel
    hs (show 0 ≤ a/2+ε by positivity) hM harmonicPairLevel_nonneg
    (summable_harmonicPair_transform ha h hs) hu
  rw [tsum_harmonicPair_transform ha h hs] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (pow_pos hs 3).le
  have hnz := hs.ne'
  field_simp at hc'
  nlinarith only [hc']

end RHTower.WeilWorkPBAP
