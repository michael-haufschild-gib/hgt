import GaloisForLFunctions.HTGeometry.CentralBinomialDiagonalKernel
import GaloisForLFunctions.HTGeometry.CentralBinomialWallisAsymptotic
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

lemma normalizedCentralBinom_pos (n : ℕ) :
    0 < normalizedCentralBinom n := by
  rw [normalizedCentralBinom]
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

lemma sqrt_one_sub_mul_normalizedCentralBinom_tsum
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.sqrt (1 - x) * ∑' n : ℕ, normalizedCentralBinom n * x ^ n = 1 := by
  have hsum := normalizedCentralBinom_gf hx0 hx1
  rw [hsum.tsum_eq]
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.2 hpos]

/-- A sequence asymptotic to a multiple of the normalized central-binomial sequence has the
corresponding square-root Abel boundary. -/
theorem tendsto_sqrt_one_sub_mul_tsum_of_normalizedCentralBinom_ratio
    {a : ℕ → ℝ} {K : ℝ}
    (h : Tendsto (fun n : ℕ => a n / normalizedCentralBinom n) atTop (nhds K)) :
    Tendsto
      (fun x : ℝ => Real.sqrt (1 - x) * ∑' n : ℕ, a n * x ^ n)
      (nhdsWithin 1 (Set.Ico 0 1)) (nhds K) := by
  let e : ℕ → ℝ := fun n => a n - K * normalizedCentralBinom n
  have he_ratio : Tendsto
      (fun n : ℕ => e n / normalizedCentralBinom n) atTop (nhds 0) := by
    have hsub := h.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => K) atTop (nhds K))
    convert hsub using 1
    · funext n
      dsimp only [e]
      field_simp [(normalizedCentralBinom_pos n).ne']
    · ring_nf
  have he : Tendsto
      (fun x : ℝ => Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n)
      (nhdsWithin 1 (Set.Ico 0 1)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hNdist⟩ :=
      (Metric.tendsto_atTop.1 he_ratio) (ε / 2) (by positivity)
    have hN : ∀ n ≥ N, |e n / normalizedCentralBinom n| < ε / 2 := by
      intro n hn
      simpa only [Real.dist_eq, sub_zero] using hNdist n hn
    let A : ℝ := ∑ n ∈ Finset.range N, |e n|
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (1 - x))
        (nhdsWithin 1 (Set.Ico 0 1)) (nhds 0) := by
      have hcont : Tendsto (fun x : ℝ => Real.sqrt (1 - x)) (nhds 1) (nhds 0) := by
        have hsub : Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds 0) := by
          simpa using (tendsto_const_nhds.sub tendsto_id :
            Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds (1 - 1)))
        simpa only [Function.comp_def, Real.sqrt_zero] using
          (Real.continuous_sqrt.tendsto 0).comp hsub
      exact hcont.mono_left inf_le_left
    have hfinite : Tendsto (fun x : ℝ => Real.sqrt (1 - x) * A)
        (nhdsWithin 1 (Set.Ico 0 1)) (nhds 0) := by
      simpa using hsqrt.mul_const A
    have hfinite_event : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Ico 0 1),
        Real.sqrt (1 - x) * A < ε / 2 := by
      have := (Metric.tendsto_nhds.1 hfinite) (ε / 2) (by positivity)
      filter_upwards [this] with x hx
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA0)] at hx
      exact hx
    filter_upwards [self_mem_nhdsWithin, hfinite_event] with x hx hxfinite
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x < 1 := hx.2
    have hsqrt0 : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
    have hcx : Summable (fun n : ℕ => normalizedCentralBinom n * x ^ n) :=
      (normalizedCentralBinom_gf hx0 hx1).summable
    have hex : Summable (fun n : ℕ => e n * x ^ n) := by
      apply (hcx.mul_left (max 1 (ε / 2))).of_norm_bounded_eventually_nat
      filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
      have hcpos := normalizedCentralBinom_pos n
      have hratio := hn.le
      have he_bound : |e n| ≤ (ε / 2) * normalizedCentralBinom n := by
        rw [abs_div, abs_of_pos hcpos] at hratio
        exact (div_le_iff₀ hcpos).1 hratio
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
      calc
        |e n| * x ^ n ≤ ((ε / 2) * normalizedCentralBinom n) * x ^ n :=
          mul_le_mul_of_nonneg_right he_bound (pow_nonneg hx0 n)
        _ = (ε / 2) * (normalizedCentralBinom n * x ^ n) := by ring
        _ ≤ max 1 (ε / 2) * (normalizedCentralBinom n * x ^ n) := by
          have hhalf : ε / 2 ≤ max 1 (ε / 2) := le_max_right _ _
          exact mul_le_mul_of_nonneg_right hhalf
            (mul_nonneg (normalizedCentralBinom_nonneg n) (pow_nonneg hx0 n))
    rw [dist_zero_right, Real.norm_eq_abs]
    have hsplit := hex.sum_add_tsum_nat_add N
    have htail :
        |∑' n : ℕ, e (n + N) * x ^ (n + N)| ≤
          (ε / 2) * ∑' n : ℕ,
            normalizedCentralBinom (n + N) * x ^ (n + N) := by
      have hex_tail : Summable (fun n : ℕ => e (n + N) * x ^ (n + N)) :=
        (summable_nat_add_iff N).2 hex
      have hcx_tail : Summable (fun n : ℕ =>
          normalizedCentralBinom (n + N) * x ^ (n + N)) :=
        (summable_nat_add_iff N).2 hcx
      rw [← Real.norm_eq_abs]
      rw [← hcx_tail.tsum_mul_left (ε / 2)]
      apply (norm_tsum_le_tsum_norm hex_tail.norm).trans
      apply hex_tail.norm.tsum_le_tsum
      · intro n
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
        have hn : N ≤ n + N := by omega
        have hcpos := normalizedCentralBinom_pos (n + N)
        have hratio := (hN (n + N) hn).le
        rw [abs_div, abs_of_pos hcpos] at hratio
        have hebound : |e (n + N)| ≤
            (ε / 2) * normalizedCentralBinom (n + N) :=
          (div_le_iff₀ hcpos).1 hratio
        calc
          |e (n + N)| * x ^ (n + N) ≤
              ((ε / 2) * normalizedCentralBinom (n + N)) * x ^ (n + N) :=
            mul_le_mul_of_nonneg_right hebound (pow_nonneg hx0 _)
          _ = (ε / 2) *
              (normalizedCentralBinom (n + N) * x ^ (n + N)) := by ring
      · exact hcx_tail.mul_left (ε / 2)
    calc
      |Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n| ≤
          Real.sqrt (1 - x) * A +
            Real.sqrt (1 - x) *
              |∑' n : ℕ, e (n + N) * x ^ (n + N)| := by
        rw [abs_mul, abs_of_nonneg hsqrt0, ← hsplit]
        have hprefix : |∑ i ∈ Finset.range N, e i * x ^ i| ≤ A := by
          calc
            |∑ i ∈ Finset.range N, e i * x ^ i| ≤
                ∑ i ∈ Finset.range N, |e i * x ^ i| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ A := by
              dsimp only [A]
              apply Finset.sum_le_sum
              intro i hi
              rw [abs_mul, abs_pow, abs_of_nonneg hx0]
              exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx0 hx1.le)
        calc
          Real.sqrt (1 - x) *
              |∑ i ∈ Finset.range N, e i * x ^ i +
                ∑' i : ℕ, e (i + N) * x ^ (i + N)| ≤
              Real.sqrt (1 - x) *
                (|∑ i ∈ Finset.range N, e i * x ^ i| +
                  |∑' i : ℕ, e (i + N) * x ^ (i + N)|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) hsqrt0
          _ = Real.sqrt (1 - x) * |∑ i ∈ Finset.range N, e i * x ^ i| +
                Real.sqrt (1 - x) *
                  |∑' i : ℕ, e (i + N) * x ^ (i + N)| := by ring
          _ ≤ Real.sqrt (1 - x) * A + Real.sqrt (1 - x) *
                |∑' i : ℕ, e (i + N) * x ^ (i + N)| := by
            exact add_le_add (mul_le_mul_of_nonneg_left hprefix hsqrt0) le_rfl
      _ ≤ Real.sqrt (1 - x) * A +
          Real.sqrt (1 - x) * ((ε / 2) *
            ∑' n : ℕ, normalizedCentralBinom (n + N) * x ^ (n + N)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htail hsqrt0)
      _ ≤ Real.sqrt (1 - x) * A + ε / 2 := by
        gcongr
        calc
          Real.sqrt (1 - x) * ((ε / 2) *
              ∑' n : ℕ, normalizedCentralBinom (n + N) * x ^ (n + N)) ≤
              (ε / 2) * (Real.sqrt (1 - x) *
                ∑' n : ℕ, normalizedCentralBinom n * x ^ n) := by
            have hsub : (∑' n : ℕ,
                normalizedCentralBinom (n + N) * x ^ (n + N)) ≤
                ∑' n : ℕ, normalizedCentralBinom n * x ^ n := by
              rw [← hcx.sum_add_tsum_nat_add N]
              exact le_add_of_nonneg_left (Finset.sum_nonneg fun n hn =>
                mul_nonneg (normalizedCentralBinom_nonneg n) (pow_nonneg hx0 n))
            have hhalf : 0 ≤ ε / 2 := by positivity
            calc
              Real.sqrt (1 - x) * ((ε / 2) *
                  ∑' n : ℕ, normalizedCentralBinom (n + N) * x ^ (n + N)) =
                  (ε / 2) * (Real.sqrt (1 - x) *
                    ∑' n : ℕ,
                      normalizedCentralBinom (n + N) * x ^ (n + N)) := by ring
              _ ≤ (ε / 2) * (Real.sqrt (1 - x) *
                    ∑' n : ℕ, normalizedCentralBinom n * x ^ n) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hsub hsqrt0) hhalf
          _ = ε / 2 := by
            rw [sqrt_one_sub_mul_normalizedCentralBinom_tsum hx0 hx1]
            ring
      _ < ε := by linarith
  have hmain : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Ico 0 1),
      Summable (fun n : ℕ => a n * x ^ n) ∧
      Summable (fun n : ℕ => e n * x ^ n) ∧
      Summable (fun n : ℕ => K * normalizedCentralBinom n * x ^ n) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x < 1 := hx.2
    have hc := (normalizedCentralBinom_gf hx0 hx1).summable
    have hevent : ∀ᶠ n : ℕ in atTop,
        |e n / normalizedCentralBinom n| ≤ 1 := by
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 he_ratio) 1 (by norm_num)
      refine eventually_atTop.2 ⟨M, ?_⟩
      intro n hn
      have := (hM n hn).le
      simpa only [Real.dist_eq, sub_zero] using this
    have he : Summable (fun n : ℕ => e n * x ^ n) := by
      apply hc.of_norm_bounded_eventually_nat
      filter_upwards [hevent] with n hn
      have hcpos := normalizedCentralBinom_pos n
      rw [abs_div, abs_of_pos hcpos] at hn
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
      exact mul_le_mul_of_nonneg_right ((div_le_one hcpos).1 hn) (pow_nonneg hx0 n)
    have hK : Summable (fun n : ℕ => K * normalizedCentralBinom n * x ^ n) := by
      simpa [mul_assoc] using (hc.mul_left K)
    have ha : Summable (fun n : ℕ => a n * x ^ n) := by
      have := he.add hK
      apply this.congr
      intro n
      dsimp only [e]
      ring
    exact ⟨ha, he, hK⟩
  have hdecomp :
      (fun x : ℝ => Real.sqrt (1 - x) * ∑' n : ℕ, a n * x ^ n) =ᶠ[
        nhdsWithin 1 (Set.Ico 0 1)]
      (fun x : ℝ => Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n + K) := by
    filter_upwards [self_mem_nhdsWithin, hmain] with x hx hs
    have hterm : ∀ n : ℕ,
        e n * x ^ n + K * normalizedCentralBinom n * x ^ n = a n * x ^ n := by
      intro n
      dsimp only [e]
      ring
    have hgf := normalizedCentralBinom_gf hx.1 hx.2
    calc
      Real.sqrt (1 - x) * ∑' n : ℕ, a n * x ^ n =
          Real.sqrt (1 - x) *
            ∑' n : ℕ,
              (e n * x ^ n + K * normalizedCentralBinom n * x ^ n) := by
        congr 1
        exact tsum_congr fun n => (hterm n).symm
      _ = Real.sqrt (1 - x) *
            ((∑' n : ℕ, e n * x ^ n) +
              ∑' n : ℕ, K * normalizedCentralBinom n * x ^ n) := by
        rw [hs.2.1.tsum_add hs.2.2]
      _ = Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n + K := by
        rw [show (∑' n : ℕ, K * normalizedCentralBinom n * x ^ n) =
            K * ∑' n : ℕ, normalizedCentralBinom n * x ^ n by
          simpa [mul_assoc] using (hgf.summable.tsum_mul_left K)]
        have hnorm := sqrt_one_sub_mul_normalizedCentralBinom_tsum hx.1 hx.2
        calc
          Real.sqrt (1 - x) *
              ((∑' n : ℕ, e n * x ^ n) +
                K * ∑' n : ℕ, normalizedCentralBinom n * x ^ n) =
              Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n +
                K * (Real.sqrt (1 - x) *
                  ∑' n : ℕ, normalizedCentralBinom n * x ^ n) := by ring
          _ = Real.sqrt (1 - x) * ∑' n : ℕ, e n * x ^ n + K := by rw [hnorm, mul_one]
  exact Tendsto.congr' hdecomp.symm (by simpa using he.add_const K)

/-- The sharp coefficient asymptotic `sqrt n * a n → L` transfers to a square-root Abel
boundary with coefficient `sqrt pi * L`. -/
theorem tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul
    {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => Real.sqrt n * a n) atTop (nhds L)) :
    Tendsto
      (fun x : ℝ => Real.sqrt (1 - x) * ∑' n : ℕ, a n * x ^ n)
      (nhdsWithin 1 (Set.Ico 0 1)) (nhds (Real.sqrt Real.pi * L)) := by
  have hden_ne : 1 / Real.sqrt Real.pi ≠ 0 := by positivity
  have hquot := h.div tendsto_sqrtNat_mul_normalizedCentralBinom hden_ne
  have heq :
      (fun n : ℕ => (Real.sqrt n * a n) /
        (Real.sqrt n * normalizedCentralBinom n)) =ᶠ[atTop]
      (fun n : ℕ => a n / normalizedCentralBinom n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt_ne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
    field_simp [hsqrt_ne, (normalizedCentralBinom_pos n).ne']
  have hratio : Tendsto
      (fun n : ℕ => a n / normalizedCentralBinom n) atTop
      (nhds (Real.sqrt Real.pi * L)) := by
    have hquot' := hquot.congr' heq
    convert hquot' using 1
    have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
      (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp [hsqrt_ne]
  exact tendsto_sqrt_one_sub_mul_tsum_of_normalizedCentralBinom_ratio hratio

end

end GaloisForLFunctions.HTGeometry

