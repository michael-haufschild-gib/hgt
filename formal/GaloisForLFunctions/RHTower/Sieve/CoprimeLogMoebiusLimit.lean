import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusUniformBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneLimit

/-!
# Limits from a divided-argument contraction
-/

open Filter Topology

namespace RHTower.Sieve

/-- A bounded solution of `g(Y) = f(Y) - p⁻¹ f(Y/p)` inherits the limit of `g`, multiplied by
the Euler factor `p/(p-1)`. -/
theorem tendsto_of_div_contraction (p : ℝ) (hp : 1 < p)
    (f g : ℝ → ℝ) (L C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ Y : ℝ, |f Y| ≤ C) (hg : Tendsto g atTop (𝓝 L))
    (hrec : ∀ Y : ℝ, g Y = f Y - (1 / p) * f (Y / p)) :
    Tendsto f atTop (𝓝 ((p / (p - 1)) * L)) := by
  let q : ℝ := 1 / p
  let A : ℝ := (p / (p - 1)) * L
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hp0).mpr hp
  have hfixed : L = A - q * A := by
    dsimp [A, q]
    field_simp
  have herr (Y : ℝ) :
      f Y - A = (g Y - L) + q * (f (Y / p) - A) := by
    rw [hrec, hfixed]
    dsimp [q]
    ring
  have hunroll : ∀ n : ℕ, ∀ Y : ℝ,
      f Y - A =
        (∑ i ∈ Finset.range n, q ^ i * (g (Y / p ^ i) - L)) +
          q ^ n * (f (Y / p ^ n) - A) := by
    intro n
    induction n with
    | zero =>
        intro Y
        simp
    | succ n ih =>
        intro Y
        rw [ih Y, herr (Y / p ^ n), Finset.sum_range_succ]
        have harg : Y / p ^ n / p = Y / p ^ (n + 1) := by
          rw [pow_succ]
          field_simp
        rw [harg]
        ring
  rw [show (p / (p - 1)) * L = A from rfl]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  let B : ℝ := C + |A|
  have hB : 0 ≤ B := add_nonneg hC (abs_nonneg A)
  have hpow : Tendsto (fun n : ℕ => q ^ n * B) atTop (𝓝 0) :=
    by simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B
  obtain ⟨n0, hn0⟩ := (Metric.tendsto_atTop.mp hpow) (ε / 2) (by positivity)
  let n : ℕ := max 1 n0
  have hn1 : 1 ≤ n := le_max_left 1 n0
  have htailScalar : q ^ n * B < ε / 2 := by
    have h := hn0 n (le_max_right 1 n0)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hq0 n) hB)] at h
    exact h
  let δ : ℝ := ε / (2 * (n : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hall : ∀ᶠ Y : ℝ in atTop, ∀ i ∈ Finset.range n,
      |g (Y / p ^ i) - L| < δ := by
    rw [Finset.eventually_all]
    intro i hi
    have hscale : Tendsto (fun Y : ℝ => Y / p ^ i) atTop atTop := by
      have hpi : 0 < (p ^ i)⁻¹ := by positivity
      simpa [div_eq_mul_inv] using
        (tendsto_mul_const_atTop_of_pos hpi).mpr (tendsto_id : Tendsto id atTop atTop)
    have hi0 : Tendsto (fun Y : ℝ => g (Y / p ^ i) - L) atTop (𝓝 0) := by
      simpa using (hg.comp hscale).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => L) atTop (𝓝 L))
    have hiNorm := hi0.norm
    rw [Metric.tendsto_atTop] at hiNorm
    obtain ⟨Yi, hYi⟩ := hiNorm δ hδ
    filter_upwards [eventually_ge_atTop Yi] with Y hY
    have h := hYi Y hY
    simpa [Real.dist_eq] using h
  rw [eventually_atTop] at hall
  obtain ⟨Y0, hY0⟩ := hall
  refine ⟨Y0, fun Y hY => ?_⟩
  have hsum :
      |∑ i ∈ Finset.range n, q ^ i * (g (Y / p ^ i) - L)| ≤ ε / 2 := by
    calc
      |∑ i ∈ Finset.range n, q ^ i * (g (Y / p ^ i) - L)|
          ≤ ∑ i ∈ Finset.range n, |q ^ i * (g (Y / p ^ i) - L)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, δ := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 i)]
        calc
          q ^ i * |g (Y / p ^ i) - L| ≤ 1 * |g (Y / p ^ i) - L| := by
            exact mul_le_mul_of_nonneg_right
              (pow_le_one₀ hq0 (le_of_lt hq1)) (abs_nonneg _)
          _ ≤ δ := by simpa using (le_of_lt (hY0 Y hY i hi))
      _ = ε / 2 := by
        simp [δ]
        field_simp
  have htail : |q ^ n * (f (Y / p ^ n) - A)| < ε / 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 n)]
    have hfA : |f (Y / p ^ n) - A| ≤ B := by
      calc
        |f (Y / p ^ n) - A| ≤ |f (Y / p ^ n)| + |A| := abs_sub _ _
        _ ≤ C + |A| := add_le_add (hf _) le_rfl
        _ = B := rfl
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfA (pow_nonneg hq0 n)) htailScalar
  rw [Real.dist_eq, hunroll n Y]
  calc
    |(∑ i ∈ Finset.range n, q ^ i * (g (Y / p ^ i) - L)) +
        q ^ n * (f (Y / p ^ n) - A)|
        ≤ |∑ i ∈ Finset.range n, q ^ i * (g (Y / p ^ i) - L)| +
            |q ^ n * (f (Y / p ^ n) - A)| := abs_add_le _ _
    _ < ε := by linarith

/-- The analytic prime step for the coprime logarithmic Möbius kernel. -/
theorem tendsto_coprimeLogMoebius_prime_step {p e : ℕ} (hp : p.Prime)
    (hpe : ¬ p ∣ e) (he : Squarefree (p * e)) {L : ℝ}
    (hlim : Tendsto (coprimeLogMoebius e) atTop (𝓝 L)) :
    Tendsto (coprimeLogMoebius (p * e)) atTop
      (𝓝 (((p : ℝ) / ((p : ℝ) - 1)) * L)) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  let C : ℝ := coprimeLogMoebiusConst *
    (((p * e : ℕ) : ℝ) / (Nat.totient (p * e) : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg coprimeLogMoebiusConst_nonneg (div_nonneg (by positivity) (by positivity))
  apply tendsto_of_div_contraction (p : ℝ) hpR
    (coprimeLogMoebius (p * e)) (coprimeLogMoebius e) L C hC
  · exact abs_coprimeLogMoebius_le (p * e) he
  · exact hlim
  · intro Y
    exact coprimeLogMoebius_recursion hp hpe Y

/-- For every fixed squarefree modulus `e`, the coprime logarithmic Möbius kernel has its expected
Euler-factor limit `e/φ(e)`. -/
theorem tendsto_coprimeLogMoebius_squarefree : ∀ e : ℕ, Squarefree e →
    Tendsto (coprimeLogMoebius e) atTop
      (𝓝 (((e : ℕ) : ℝ) / (Nat.totient e : ℝ))) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
      intro he
      rcases eq_or_ne e 1 with rfl | hne
      · simpa using tendsto_coprimeLogMoebius_one
      · have he0 : e ≠ 0 := he.ne_zero
        let p := e.minFac
        let e' := e / p
        have hp : p.Prime := Nat.minFac_prime hne
        have hpd : p ∣ e := Nat.minFac_dvd e
        have hmul : p * e' = e := Nat.mul_div_cancel' hpd
        have hpe : ¬ p ∣ e' := by
          intro hdvd
          obtain ⟨k, hk⟩ := hdvd
          have hsq : p * p ∣ e := by
            refine ⟨k, ?_⟩
            calc
              e = p * e' := hmul.symm
              _ = p * (p * k) := by rw [hk]
              _ = p * p * k := by ring
          have hunit := he _ hsq
          rw [Nat.isUnit_iff] at hunit
          exact hp.ne_one hunit
        have he'Sf : Squarefree e' :=
          Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd) he
        have he'lt : e' < e := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hp.one_lt
        have he'0 : e' ≠ 0 := by
          intro hzero
          rw [hzero, Nat.mul_zero] at hmul
          exact he0 hmul.symm
        have hIH := ih e' he'lt he'Sf
        have hprod : Squarefree (p * e') := by rwa [hmul]
        have hstep := tendsto_coprimeLogMoebius_prime_step hp hpe hprod hIH
        have hcop : Nat.Coprime p e' := (hp.coprime_iff_not_dvd).mpr hpe
        have htot : Nat.totient e = (p - 1) * Nat.totient e' := by
          conv_lhs => rw [← hmul]
          rw [Nat.totient_mul hcop, Nat.totient_prime hp]
        have hp1 : 1 ≤ p := hp.one_lt.le
        have hcastSub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          rw [Nat.cast_sub hp1, Nat.cast_one]
        have htotpos : (0 : ℝ) < (Nat.totient e' : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero he'0)
        have hppos : (0 : ℝ) < (p : ℝ) - 1 := by
          have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
          linarith
        have hcastMul : (e : ℝ) = (p : ℝ) * (e' : ℝ) := by
          exact_mod_cast hmul.symm
        have hcastTot : (Nat.totient e : ℝ) =
            ((p : ℝ) - 1) * (Nat.totient e' : ℝ) := by
          calc
            (Nat.totient e : ℝ) = (((p - 1) * Nat.totient e' : ℕ) : ℝ) := by rw [htot]
            _ = ((p - 1 : ℕ) : ℝ) * (Nat.totient e' : ℝ) := by
              norm_num
            _ = ((p : ℝ) - 1) * (Nat.totient e' : ℝ) := by rw [hcastSub]
        have htarget :
            ((p : ℝ) / ((p : ℝ) - 1)) *
                (((e' : ℕ) : ℝ) / (Nat.totient e' : ℝ)) =
              (e : ℝ) / (Nat.totient e : ℝ) := by
          rw [hcastMul, hcastTot]
          field_simp
        rw [hmul] at hstep
        rw [← htarget]
        exact hstep

end RHTower.Sieve
