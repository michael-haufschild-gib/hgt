import GaloisForLFunctions.BezoutValuationIncidence.MoebiusEquidistributionInTheResidueClassesOfAPrime
import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleCouplingOfPrimePacketsWithThePrimeBlock

/-!
# Single-modulus cancellation of the Möbius block

Let `μ_Q = μ · 1_{(Q, 2Q]}` be the Möbius block at scale `Q` and fix a prime `p`.

* **Every class cancels.** For `0 < r < p` the class mass `Σ_{Q<n≤2Q, n≡r} μ(n)/n²` is `o(1/Q)`, by Abel
  summation against `1/(n² log n)` of the log-weighted class sums (`o(x log x)`, from Dirichlet's
  theorem). The whole block has mass `o(1/Q)` by the prime number theorem `M(x) = o(x)`, so the class
  `0` cancels too: unlike the primes, the Möbius block omits no residue class.
* Hence the kernel statistic vanishes at every fixed prime modulus,
  `Q Λ_p(μ_Q) → 0` (`tendsto_mul_kernelStatistic_moebiusWindowRow`), and for every row `c` on a fixed
  finite set of primes the cross-scale coupling vanishes,
  `Q (B + m R' + β H') → 0` (`tendsto_mul_rowBilinear_moebiusWindowRow`).

**The pair** (`singleModulus_pair_moebius_primes`). At every fixed prime modulus the prime block has
`Q Λ_p → -π²(p²-1)²/(144 p²(p-1)) ≠ 0` (the omitted residue class), and every fixed prime packet
couples with it at `-(π²/144) Σ c(p)(1 - p^{-2})/Q`; the Möbius block has both equal to `o(1/Q)`. The
cancellation of the Möbius signs within each residue class of one modulus is exactly what removes
the sieve term. These are fixed-modulus statements, with no rate and no uniformity in `p`.
-/

open Finset Filter Topology
open ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The Möbius block and its class masses -/

/-- The Möbius row on the dyadic window `(Q, 2Q]`. -/
def moebiusWindowRow (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then moebiusReal n else 0

/-- The mass `Σ_{Q<n≤2Q, n ≡ r} μ(n)/n²` of the class `r` modulo `p` in the Möbius block. -/
def moebiusClassMass (p r Q : ℕ) : ℝ :=
  ∑ n ∈ Ioc Q (2 * Q), (if n % p = r then moebiusReal n else 0) / (n : ℝ) ^ 2

/-- The total mass `Σ_{Q<n≤2Q} μ(n)/n²` of the Möbius block. -/
def moebiusBlockMass (Q : ℕ) : ℝ := ∑ n ∈ Ioc Q (2 * Q), moebiusReal n / (n : ℝ) ^ 2

theorem sum_range_moebiusClassMass {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ∑ r ∈ range p, moebiusClassMass p r Q = moebiusBlockMass Q := by
  unfold moebiusClassMass moebiusBlockMass
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_div]
  congr 1
  rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (Nat.mod_lt n hp.pos))]

/-- **The block mass vanishes** (prime number theorem): `Q Σ_{Q<n≤2Q} μ(n)/n² → 0`. -/
theorem tendsto_mul_moebiusBlockMass :
    Tendsto (fun Q : ℕ => (Q : ℝ) * moebiusBlockMass Q) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hM := RHTower.Sieve.tendsto_abs_mertensM_div
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hM.eventually (eventually_le_nhds
    (show (0 : ℝ) < η / 4 by positivity)))
  refine ⟨x₀ + 1, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hS : ∀ x, Q ≤ x → x ≤ 2 * Q → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ η / 4 * x := by
    intro x hx _
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have h := hx₀ x (by omega)
    have heq : RHTower.Sieve.mertensM x = ∑ e ∈ Icc 1 x, moebiusReal e := by
      rw [RHTower.Sieve.mertensM, dampedSign_sum_range_succ_eq_add_Icc]
      simp [moebiusReal]
    rw [heq, div_le_iff₀ hx0] at h
    linarith
  have hab := abs_sum_Ioc_mul_le_of_linear (s := moebiusReal) (w := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (L := η / 4) (D := Q) (X := 2 * Q) (by omega) hS (fun n => by positivity)
    (fun n hn => one_div_le_one_div_of_le (by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 2))
  have hhead : 2 * (Q : ℝ) * (1 / ((Q + 1 : ℕ) : ℝ) ^ 2) ≤ 2 / (Q : ℝ) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hQ0]; push_cast; nlinarith
  have htail : ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ 1 / (Q : ℝ) :=
    (dyadicInverseSquareMass_le Q).trans (one_div_le_one_div_of_le hQ0 (by linarith))
  have hid : moebiusBlockMass Q = ∑ n ∈ Ioc Q (2 * Q), moebiusReal n * (1 / (n : ℝ) ^ 2) := by
    unfold moebiusBlockMass; exact sum_congr rfl fun n _ => by ring
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hQ0, hid]
  calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), moebiusReal n * (1 / (n : ℝ) ^ 2)|
      ≤ (Q : ℝ) * (η / 4 * (2 / (Q : ℝ) + 1 / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left
          (add_le_add hhead htail) (by positivity))) hQ0.le
    _ = 3 * η / 4 := by field_simp; ring
    _ < η := by linarith

/-- **The coprime classes cancel.** For `0 < r < p`, `Q Σ_{Q<n≤2Q, n≡r} μ(n)/n² → 0`. -/
theorem tendsto_mul_moebiusClassMass {p r : ℕ} (hp : p.Prime) (hr0 : 0 < r) (hrp : r < p) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * moebiusClassMass p r Q) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (eventually_abs_sum_class_moebius_log_le hp hr0 hrp (show (0 : ℝ) < η / 8 by positivity))
  refine ⟨x₀ + 2, fun Q hQ => ?_⟩
  have hQ2 : 2 ≤ Q := by omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log Q := by
    rw [Real.log_mul (by norm_num) hQ0.ne']
    have : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) (by exact_mod_cast hQ2)
    linarith
  set s : ℕ → ℝ := fun n => (if n % p = r then 1 else 0) * (moebiusReal n * Real.log n)
  set w : ℕ → ℝ := fun n => 1 / ((n : ℝ) ^ 2 * Real.log n)
  have hS : ∀ x, Q ≤ x → x ≤ 2 * Q → |∑ e ∈ Icc 1 x, s e| ≤ (η / 8 * Real.log (2 * Q)) * x := by
    intro x hx hx2
    have h := hx₀ x (by omega)
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlx : Real.log x ≤ Real.log (2 * Q) := Real.log_le_log hx0 (by exact_mod_cast hx2)
    calc |∑ e ∈ Icc 1 x, s e| ≤ η / 8 * x * Real.log x := h
      _ ≤ η / 8 * x * Real.log (2 * Q) := mul_le_mul_of_nonneg_left hlx (by positivity)
      _ = (η / 8 * Real.log (2 * Q)) * x := by ring
  have hw0 : ∀ n, 0 ≤ w n := fun n => by
    simp only [w]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Real.log_natCast_nonneg n; positivity
  have hwa : ∀ d, Q < d → w (d + 1) ≤ w d := by
    intro d hd
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    have hld : 0 < Real.log (d : ℝ) := Real.log_pos (by linarith)
    have hle : Real.log (d : ℝ) ≤ Real.log ((d + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    simp only [w]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) (by push_cast; linarith) 2) hle hld.le
      (by positivity)
  have hab := abs_sum_Ioc_mul_le_of_linear (s := s) (w := w) (D := Q) (X := 2 * Q) (by omega)
    hS hw0 hwa
  -- `s · w` is the class mass summand on `(Q, 2Q]`
  have hid : moebiusClassMass p r Q = ∑ d ∈ Ioc Q (2 * Q), s d * w d := by
    unfold moebiusClassMass
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ioc] at hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hln : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
    simp only [s, w]
    split_ifs
    · field_simp
    · simp
  have hlQne : Real.log (Q : ℝ) ≠ 0 := hlogQ.ne'
  have hwQ : ∀ n ∈ Ioc Q (2 * Q), w n ≤ 1 / ((Q : ℝ) ^ 2 * Real.log Q) := by
    intro n hn
    rw [mem_Ioc] at hn
    have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have hl : Real.log (Q : ℝ) ≤ Real.log n := Real.log_le_log hQ0 hQn
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul (pow_le_pow_left₀ hQ0.le hQn 2) hl hlogQ.le (by positivity))
  have hhead : 2 * (Q : ℝ) * w (Q + 1) ≤ 2 / ((Q : ℝ) * Real.log Q) := by
    have h := hwQ (Q + 1) (by rw [mem_Ioc]; omega)
    calc 2 * (Q : ℝ) * w (Q + 1) ≤ 2 * (Q : ℝ) * (1 / ((Q : ℝ) ^ 2 * Real.log Q)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 / ((Q : ℝ) * Real.log Q) := by field_simp
  have htail : ∑ d ∈ Ioc Q (2 * Q), w d ≤ 1 / ((Q : ℝ) * Real.log Q) := by
    calc ∑ d ∈ Ioc Q (2 * Q), w d ≤ ∑ _d ∈ Ioc Q (2 * Q), 1 / ((Q : ℝ) ^ 2 * Real.log Q) :=
          sum_le_sum hwQ
      _ = 1 / ((Q : ℝ) * Real.log Q) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
  have hL0 : 0 ≤ η / 8 * Real.log (2 * (Q : ℝ)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Q by linarith)
    positivity
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hQ0, hid]
  calc (Q : ℝ) * |∑ d ∈ Ioc Q (2 * Q), s d * w d|
      ≤ (Q : ℝ) * ((η / 8 * Real.log (2 * Q)) * (2 / ((Q : ℝ) * Real.log Q) +
          1 / ((Q : ℝ) * Real.log Q))) :=
        mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left
          (add_le_add hhead htail) hL0)) hQ0.le
    _ = 3 * η / 8 * (Real.log (2 * Q) / Real.log Q) := by field_simp; ring
    _ ≤ 3 * η / 8 * 2 := by
        gcongr
        rw [div_le_iff₀ hlogQ]; linarith
    _ < η := by linarith

/-- **The class `0` cancels too**: `Q Σ_{Q<n≤2Q, p ∣ n} μ(n)/n² → 0`. -/
theorem tendsto_mul_moebiusClassMass_zero {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * moebiusClassMass p 0 Q) atTop (𝓝 0) := by
  have hcop : Tendsto (fun Q : ℕ => ∑ r ∈ (range p).erase 0, (Q : ℝ) * moebiusClassMass p r Q)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum ((range p).erase 0) fun r hr =>
      tendsto_mul_moebiusClassMass hp (Nat.pos_of_ne_zero (ne_of_mem_erase hr))
        (mem_range.mp (mem_of_mem_erase hr))
    simpa using h
  have h := tendsto_mul_moebiusBlockMass.sub hcop
  rw [sub_zero] at h
  refine h.congr fun Q => ?_
  rw [← sum_range_moebiusClassMass hp Q, ← add_sum_erase _ _ (mem_range.mpr hp.pos), mul_add,
    mul_sum]
  ring

/-! ## §2. The kernel statistic and the coupling -/

theorem sum_Icc_moebiusWindowRow_eq (Q : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (2 * Q), moebiusWindowRow Q n * f n = ∑ n ∈ Ioc Q (2 * Q), moebiusReal n * f n := by
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  rw [← sum_subset hsub fun n hn hn' => by
    have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
    simp [moebiusWindowRow, this]]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_Ioc] at hn
  simp [moebiusWindowRow, hn.1, hn.2]

theorem kernelStatistic_moebiusWindowRow_eq {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    kernelStatistic (2 * Q) (moebiusWindowRow Q) p =
      ∑ r ∈ range p, (bernoulliKernel p r - primeKernelMean p) * moebiusClassMass p r Q +
        ∑ n ∈ Ioc Q (2 * Q), moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n := by
  have hrestrict : kernelStatistic (2 * Q) (moebiusWindowRow Q) p =
      ∑ n ∈ Ioc Q (2 * Q), (moebiusReal n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p) +
        moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n) := by
    rw [kernelStatistic]
    have h := sum_Icc_moebiusWindowRow_eq Q (fun n =>
      1 / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p) + 1 / (n : ℝ) ^ 3 * cubicKernel p n)
    calc _ = ∑ n ∈ Icc 1 (2 * Q), moebiusWindowRow Q n * (1 / (n : ℝ) ^ 2 *
          (bernoulliKernel p n - primeKernelMean p) + 1 / (n : ℝ) ^ 3 * cubicKernel p n) :=
          sum_congr rfl fun n _ => by ring
      _ = _ := by rw [h]; exact sum_congr rfl fun n _ => by ring
  rw [hrestrict, sum_add_distrib]
  congr 1
  have hfib := sum_fiberwise_of_maps_to (s := Ioc Q (2 * Q)) (t := range p) (g := fun n => n % p)
    (fun n _ => mem_range.mpr (Nat.mod_lt n hp.pos))
    (fun n => moebiusReal n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p))
  rw [← hfib]
  refine sum_congr rfl fun r _ => ?_
  rw [moebiusClassMass, mul_sum, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [bernoulliKernel_mod, h]; ring
  · ring

theorem tendsto_mul_moebius_cubicPart {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n) atTop (𝓝 0) := by
  have hbound : ∀ Q : ℕ, 1 ≤ Q → |(Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n| ≤ (p : ℝ) ^ 3 / Q := by
    intro Q hQ
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hterm : ∀ n ∈ Ioc Q (2 * Q), |moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
        1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 := by
      intro n hn
      rw [mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
      rw [abs_mul, abs_div, abs_of_pos (by positivity)]
      refine mul_le_mul ?_ (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
      calc |moebiusReal n| / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right (abs_moebiusReal_le_one' n) (by positivity)
        _ ≤ 1 / (Q : ℝ) ^ 3 :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3)
    rw [abs_mul, abs_of_pos hQ0]
    calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), moebiusReal n / (n : ℝ) ^ 3 * cubicKernel p n|
        ≤ (Q : ℝ) * ∑ _n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)) hQ0.le
      _ = (p : ℝ) ^ 3 / Q := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
  have hlim : Tendsto (fun Q : ℕ => (p : ℝ) ^ 3 / Q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
  rw [Real.norm_eq_abs]; exact hbound Q hQ

/-- **The Möbius block's kernel statistic vanishes at every fixed prime**: `Q Λ_p(μ_Q) → 0`. -/
theorem tendsto_mul_kernelStatistic_moebiusWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (moebiusWindowRow Q) p) atTop (𝓝 0) := by
  have hcls : Tendsto (fun Q : ℕ => ∑ r ∈ range p,
      (bernoulliKernel p r - primeKernelMean p) * ((Q : ℝ) * moebiusClassMass p r Q)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (range p) fun r _ =>
      ((show Tendsto (fun Q : ℕ => (Q : ℝ) * moebiusClassMass p r Q) atTop (𝓝 0) from by
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · exact tendsto_mul_moebiusClassMass_zero hp
        · by_cases hrp : r < p
          · exact tendsto_mul_moebiusClassMass hp hr hrp
          · have : ∀ Q, moebiusClassMass p r Q = 0 := fun Q => sum_eq_zero fun n _ => by
              rw [if_neg (by have := Nat.mod_lt n hp.pos; omega), zero_div]
            simp [this])).const_mul (bernoulliKernel p r - primeKernelMean p))
    simpa using h
  have h := hcls.add (tendsto_mul_moebius_cubicPart hp)
  rw [add_zero] at h
  refine h.congr fun Q => ?_
  rw [kernelStatistic_moebiusWindowRow_eq hp, mul_add, mul_sum]
  congr 1
  exact sum_congr rfl fun r _ => by ring

/-- **The coupling of a fixed prime packet with the Möbius block vanishes.** For `c` supported on a
finite set of primes, `Q (B + m R' + β H') → 0` against `μ_Q`. -/
theorem tendsto_mul_rowBilinear_moebiusWindowRow {c : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ d, c d ≠ 0 → d ∈ S) (hSp : ∀ p ∈ S, p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (moebiusWindowRow Q) +
        rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (moebiusWindowRow Q) +
        rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (moebiusWindowRow Q))) atTop (𝓝 0) := by
  have hcP : ∀ d, c d ≠ 0 → d.Prime := fun d hd => hSp d (hS d hd)
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → S ⊆ Icc 1 (2 * Q) :=
    ⟨S.sup id, fun Q hQ p hp => by
      rw [mem_Icc]
      exact ⟨(hSp p hp).one_lt.le, by have := le_sup (f := id) hp; simp at this; omega⟩⟩
  set A := ∑ d ∈ S, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3
  set C₃ := ∑ d ∈ S, |c d| * (d : ℝ) ^ 3
  -- main term: the block mass vanishes
  have hmain : Tendsto (fun Q : ℕ => (Q : ℝ) * equidistributedMain (2 * Q) c (moebiusWindowRow Q))
      atTop (𝓝 0) := by
    have h := (tendsto_mul_moebiusBlockMass.const_mul (Real.pi ^ 2 / 72)).mul_const A
    rw [mul_zero, zero_mul] at h
    refine h.congr' (eventually_ge_atTop Q₀ |>.mono fun Q hQ => ?_)
    have hr : ∑ d ∈ Icc 1 (2 * Q), c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 = A :=
      (sum_subset (hQ₀ Q hQ) fun d _ hd => by
        have : c d = 0 := by by_contra h; exact hd (hS d h)
        simp [this]).symm
    have hm : ∑ n ∈ Icc 1 (2 * Q), moebiusWindowRow Q n / (n : ℝ) ^ 2 = moebiusBlockMass Q := by
      have h := sum_Icc_moebiusWindowRow_eq Q (fun n => 1 / (n : ℝ) ^ 2)
      simp only [mul_one_div] at h
      rw [h, moebiusBlockMass]
    dsimp only
    rw [equidistributedMain, hr, hm]; ring
  -- kernel statistics
  have hker : Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ d ∈ Icc 1 (2 * Q),
      c d / d * kernelStatistic (2 * Q) (moebiusWindowRow Q) d) atTop (𝓝 0) := by
    have h := tendsto_finsetSum S fun p hp =>
      (tendsto_mul_kernelStatistic_moebiusWindowRow (hSp p hp)).const_mul (c p / p)
    simp only [mul_zero, sum_const_zero] at h
    refine h.congr' (eventually_ge_atTop Q₀ |>.mono fun Q hQ => ?_)
    have hr : ∑ d ∈ Icc 1 (2 * Q), c d / d * kernelStatistic (2 * Q) (moebiusWindowRow Q) d =
        ∑ d ∈ S, c d / d * kernelStatistic (2 * Q) (moebiusWindowRow Q) d :=
      (sum_subset (hQ₀ Q hQ) fun d _ hd => by
        have : c d = 0 := by by_contra h; exact hd (hS d h)
        simp [this]).symm
    dsimp only
    rw [hr, mul_sum]
    exact sum_congr rfl fun p _ => by ring
  -- the fourth-order error
  have herr : Tendsto (fun Q : ℕ => (Q : ℝ) * (6 * (∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3) *
      ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4)) atTop (𝓝 0) := by
    have hb : ∀ Q : ℕ, Q₀ ≤ Q → 1 ≤ Q → |(Q : ℝ) * (6 * (∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3) *
        ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4)| ≤ 6 * C₃ / Q := by
      intro Q hQ hQ1
      have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
      have hC : ∑ d ∈ Icc 1 (2 * Q), |c d| * (d : ℝ) ^ 3 = C₃ := by
        rw [← sum_subset (hQ₀ Q hQ) fun d _ hd => by
          have : c d = 0 := by by_contra h; exact hd (hS d h)
          simp [this]]
      have hC0 : 0 ≤ C₃ := sum_nonneg fun d _ => by positivity
      have hrow : ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 3 := by
        have heq : ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4 =
            ∑ n ∈ Ioc Q (2 * Q), |moebiusReal n| / (n : ℝ) ^ 4 := by
          have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
            rw [mem_Ioc] at hn; rw [mem_Icc]; omega
          rw [← sum_subset hsub fun n hn hn' => by
            have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
            simp [moebiusWindowRow, this]]
          refine sum_congr rfl fun n hn => ?_
          rw [mem_Ioc] at hn
          simp [moebiusWindowRow, hn.1, hn.2]
        rw [heq]
        calc ∑ n ∈ Ioc Q (2 * Q), |moebiusReal n| / (n : ℝ) ^ 4
            ≤ ∑ _n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ 4 := by
              refine sum_le_sum fun n hn => ?_
              rw [mem_Ioc] at hn
              have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
              have hn0 : (0 : ℝ) < n := by linarith
              exact (div_le_div_of_nonneg_right (abs_moebiusReal_le_one' n) (by positivity)).trans
                (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hQn 4))
          _ = 1 / (Q : ℝ) ^ 3 := by
              rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
      have hnn : 0 ≤ ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4 :=
        sum_nonneg fun n _ => by positivity
      rw [hC, abs_of_nonneg (by positivity)]
      calc (Q : ℝ) * (6 * C₃ * ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 4)
          ≤ (Q : ℝ) * (6 * C₃ * (1 / (Q : ℝ) ^ 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow (by positivity)) hQ0.le
        _ ≤ 6 * C₃ / Q := by
            rw [show (Q : ℝ) * (6 * C₃ * (1 / (Q : ℝ) ^ 3)) = 6 * C₃ / Q / Q / Q * Q by
              field_simp]
            have h1 : 6 * C₃ / Q / Q / Q * Q = 6 * C₃ / Q / Q := by field_simp
            rw [h1]
            exact div_le_self (div_nonneg (by positivity) hQ0.le) (by exact_mod_cast hQ1)
    have hlim : Tendsto (fun Q : ℕ => 6 * C₃ / Q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ((eventually_ge_atTop (max Q₀ 1)).mono fun Q hQ => ?_) hlim
    rw [Real.norm_eq_abs]
    exact hb Q (le_of_max_le_left hQ) (le_of_max_le_right hQ)
  have hrest : Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (moebiusWindowRow Q) +
      rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (moebiusWindowRow Q) +
      rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (moebiusWindowRow Q) -
      equidistributedMain (2 * Q) c (moebiusWindowRow Q) -
      ∑ d ∈ Icc 1 (2 * Q), c d / d * kernelStatistic (2 * Q) (moebiusWindowRow Q) d)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun Q => ?_) herr
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left
      (abs_rowBilinear_sub_kernelStatistic_le (2 * Q) (moebiusWindowRow Q) hcP) (Nat.cast_nonneg Q)
  have htot := (hmain.add hker).add hrest
  rw [add_zero, add_zero] at htot
  refine htot.congr fun Q => ?_
  ring

/-! ## §3. The pair -/

/-- **The single-modulus pair of the Möbius and the prime blocks.** At every fixed prime `p` the prime
block carries the omitted-class term `Q Λ_p → -π²(p²-1)²/(144p²(p-1))` while the Möbius block has
`Q Λ_p → 0`; for every row `c` on a fixed finite set of primes the coupling with the prime block tends
to `-(π²/144) Σ c(p)(1-p^{-2})` and the coupling with the Möbius block to `0`. -/
theorem singleModulus_pair_moebius_primes :
    (∀ p : ℕ, p.Prime →
      Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (primeWindowRow Q) p) atTop
        (𝓝 (-(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))))) ∧
      Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (moebiusWindowRow Q) p) atTop
        (𝓝 0)) ∧
    (∀ (c : ℕ → ℝ) (S : Finset ℕ), (∀ d, c d ≠ 0 → d ∈ S) → (∀ p ∈ S, p.Prime) →
      Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (primeWindowRow Q) +
          rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (primeWindowRow Q) +
          rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (primeWindowRow Q))) atTop
        (𝓝 (-(Real.pi ^ 2 / 144 * ∑ p ∈ S, c p * ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2))) ∧
      Tendsto (fun Q : ℕ => (Q : ℝ) * (rowBilinear (2 * Q) c (moebiusWindowRow Q) +
          rowMean (2 * Q) c * vonMangoldtReadout (2 * Q) (moebiusWindowRow Q) +
          rowBeta (2 * Q) c * finiteHarmonicSum (2 * Q) (moebiusWindowRow Q))) atTop (𝓝 0)) :=
  ⟨fun p hp => ⟨tendsto_mul_kernelStatistic_primeWindowRow hp,
      tendsto_mul_kernelStatistic_moebiusWindowRow hp⟩,
    fun c S hS hSp => ⟨tendsto_mul_rowBilinear_primeWindowRow hS hSp,
      tendsto_mul_rowBilinear_moebiusWindowRow hS hSp⟩⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
