import GaloisForLFunctions.RHTower.KuznetsovSqrtPhasePoisson
import GaloisForLFunctions.RHTower.KuznetsovKloostermanSieve
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# DI (1.27): bilinear Kloosterman forms with the phase `e(2θ√(mn)/c)` for small moduli

For `m, n ∈ (N, 2N]`, `1 ≤ |θ| ≤ 2` and `B(θ, c) = Σ_{m,n} ᾱ_m α_n S(m, n; c) e(2θ√(mn)/c)`,
Cauchy–Schwarz in `n` with the smooth weight `η(√(n/N))`, opening the Kloosterman sums and Poisson
summation in `n` (`exists_tsum_sqrtSumFun_sub_le`) leave only the resonant terms `x₁ = x₂`, which carry the
Ramanujan sum `c_c(m₁ − m₂)` and the integral `∫ η(√(t/N)) e(B√t) dt ≪ min(N, cN/|m₁ − m₂|)`:

`|B(θ, c)|² ≤ C (Σ|α|²)² (c N τ(c)(1 + log N) + c² N² (c/N)^p)`  (`exists_bilinear_kloosterman_small_le`).
-/

open MeasureTheory Set Filter Complex
open scoped FourierTransform ComplexConjugate

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

open RHTower.Sieve

noncomputable section

/-! ## Ramanujan sums -/

/-- `|c_c(h)| ≤ Σ_{d ∣ (h, c)} d`. -/
theorem norm_sum_units_stdAddChar_le (c : ℕ) [NeZero c] (h : ZMod c) :
    ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (h * (x : ZMod c))‖ ≤ ∑ d ∈ (h.val.gcd c).divisors, (d : ℝ) := by
  classical
  set Q : RHTower.CGLPositiveModulus := ⟨c, Nat.pos_of_ne_zero (NeZero.ne c)⟩
  have himg : (Finset.univ.image fun x : (ZMod c)ˣ => (x : ZMod c)) =
      Finset.univ.filter IsUnit := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun ha => ⟨ha.unit, rfl⟩⟩
  have hsum : ∑ x : (ZMod c)ˣ, ZMod.stdAddChar (h * (x : ZMod c)) =
      RHTower.cglRamanujanAdditiveSum Q h := by
    rw [RHTower.cglRamanujanAdditiveSum]
    change _ = ∑ a ∈ Finset.univ.filter IsUnit, ZMod.stdAddChar (a * h)
    rw [← himg, Finset.sum_image fun x _ y _ hxy => Units.ext hxy]
    refine Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hsum, cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
  have : |((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc (d : ℝ) * |((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℝ)| ≤ d * 1 := by gcongr
    _ = d := mul_one _

/-- The divisors of `(h.val, c)` are the divisors of `c` dividing any integer representative of `h`. -/
theorem mem_divisors_gcd_val_iff (c : ℕ) [NeZero c] {k : ℤ} (d : ℕ) :
    d ∈ (((k : ZMod c)).val.gcd c).divisors ↔ d ∈ c.divisors ∧ (d : ℤ) ∣ k := by
  have hc : c ≠ 0 := NeZero.ne c
  have hdvd : (c : ℤ) ∣ (((k : ZMod c)).val : ℤ) - k := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, sub_self]
  rw [Nat.mem_divisors, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    refine ⟨⟨h2, hc⟩, ?_⟩
    have h1' : (d : ℤ) ∣ (((k : ZMod c)).val : ℤ) := by exact_mod_cast h1
    have h2' : (d : ℤ) ∣ (c : ℤ) := by exact_mod_cast h2
    have := dvd_sub h1' (h2'.trans hdvd)
    simpa using this
  · rintro ⟨⟨h2, -⟩, hk⟩
    have h2' : (d : ℤ) ∣ (c : ℤ) := by exact_mod_cast h2
    have h1' : (d : ℤ) ∣ (((k : ZMod c)).val : ℤ) := by
      have := dvd_add (h2'.trans hdvd) hk
      simpa using this
    refine ⟨⟨by exact_mod_cast h1', h2⟩, Nat.gcd_ne_zero_right hc⟩

/-! ## A harmonic count -/

theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have heq : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ := by
    rw [harmonic]
    push_cast
    have h1 := Finset.sum_Ico_add' (fun k : ℕ => ((k : ℝ))⁻¹) 0 N 1
    simp only [Nat.cast_add, Nat.cast_one, zero_add] at h1
    rw [Finset.range_eq_Ico, h1, Finset.Ico_add_one_right_eq_Icc]
  rw [← heq]; exact h

/-- For fixed `m₁` and `d ≥ 1`: `Σ_{m₂ ≠ m₁, d ∣ m₂ − m₁, |m₂ − m₁| ≤ N} d/|m₁ − m₂| ≤ 2(1 + log N)`. -/
theorem sum_filter_dvd_div_abs_le (N m₁ d : ℕ) (hd : 0 < d) (s : Finset ℕ)
    (hs : ∀ m ∈ s, (m : ℤ) - m₁ ≤ N ∧ (m₁ : ℤ) - m ≤ N) :
    ∑ m ∈ s.filter (fun m => m ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m), (d : ℝ) / |(m₁ : ℝ) - m| ≤
      2 * (1 + Real.log N) := by
  classical
  set A := s.filter (fun m => m ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- one side of `m₁`
  have side : ∀ (sgn : Bool), ∑ m ∈ A.filter (fun m => decide (m₁ < m) = sgn),
      (d : ℝ) / |(m₁ : ℝ) - m| ≤ 1 + Real.log N := by
    intro sgn
    set A' := A.filter (fun m => decide (m₁ < m) = sgn)
    set φ : ℕ → ℕ := fun m => (Int.natAbs ((m₁ : ℤ) - m)) / d
    have hmem : ∀ m ∈ A', m ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m ∧ m ∈ s ∧ (decide (m₁ < m) = sgn) := by
      intro m hm
      simp only [A', A, Finset.mem_filter] at hm
      exact ⟨hm.1.2.1, hm.1.2.2, hm.1.1, hm.2⟩
    have hval : ∀ m ∈ A', (d : ℝ) / |(m₁ : ℝ) - m| = ((φ m : ℕ) : ℝ)⁻¹ ∧ φ m ∈ Finset.Icc 1 N := by
      intro m hm
      obtain ⟨hne, hdv, hms, -⟩ := hmem m hm
      obtain ⟨k, hk⟩ := hdv
      have habs : (Int.natAbs ((m₁ : ℤ) - m)) = d * k.natAbs := by
        rw [hk, Int.natAbs_mul]; simp
      have hφ : φ m = k.natAbs := by
        simp only [φ]; rw [habs, Nat.mul_div_cancel_left _ hd]
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hne
        have : (m₁ : ℤ) - m = 0 := by rw [hk, mul_zero]
        omega
      have hR : |(m₁ : ℝ) - m| = d * k.natAbs := by
        have : ((Int.natAbs ((m₁ : ℤ) - m) : ℕ) : ℝ) = |(m₁ : ℝ) - m| := by
          rw [Nat.cast_natAbs]; push_cast; rfl
        rw [← this, habs]; push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [hR, hφ]
        have : (0 : ℝ) < k.natAbs := by exact_mod_cast Int.natAbs_pos.2 hk0
        field_simp
      · rw [hφ, Finset.mem_Icc]
        refine ⟨Int.natAbs_pos.2 hk0, ?_⟩
        have h1 := hs m hms
        have h2 : (Int.natAbs ((m₁ : ℤ) - m) : ℤ) ≤ N := by
          rw [Int.natCast_natAbs, abs_le]; constructor <;> linarith [h1.1, h1.2]
        have h3 : (k.natAbs : ℤ) ≤ (Int.natAbs ((m₁ : ℤ) - m) : ℤ) := by
          rw [habs]; push_cast
          nlinarith [Int.natCast_nonneg k.natAbs, (by exact_mod_cast hd : (1 : ℤ) ≤ d)]
        exact_mod_cast h3.trans h2
    have hinj : Set.InjOn φ A' := by
      intro m hm m' hm' heq
      obtain ⟨-, ⟨k, hk⟩, -, hsg⟩ := hmem m hm
      obtain ⟨-, ⟨k', hk'⟩, -, hsg'⟩ := hmem m' hm'
      have habs : Int.natAbs ((m₁ : ℤ) - m) = Int.natAbs ((m₁ : ℤ) - m') := by
        have e1 : Int.natAbs ((m₁ : ℤ) - m) = d * φ m := by
          simp only [φ]; rw [hk, Int.natAbs_mul]; simp [Nat.mul_div_cancel_left _ hd]
        have e2 : Int.natAbs ((m₁ : ℤ) - m') = d * φ m' := by
          simp only [φ]; rw [hk', Int.natAbs_mul]; simp [Nat.mul_div_cancel_left _ hd]
        rw [e1, e2, heq]
      have hsame : (m₁ < m ↔ m₁ < m') := by
        rw [← decide_eq_decide]; rw [hsg, hsg']
      by_cases h : m₁ < m
      · have h' := hsame.1 h
        omega
      · have h' : ¬ m₁ < m' := fun h' => h (hsame.2 h')
        omega
    calc ∑ m ∈ A', (d : ℝ) / |(m₁ : ℝ) - m| = ∑ m ∈ A', ((φ m : ℕ) : ℝ)⁻¹ :=
          Finset.sum_congr rfl fun m hm => (hval m hm).1
      _ = ∑ k ∈ A'.image φ, ((k : ℕ) : ℝ)⁻¹ :=
          (Finset.sum_image (f := fun k : ℕ => ((k : ℝ))⁻¹) hinj).symm
      _ ≤ ∑ k ∈ Finset.Icc 1 N, ((k : ℕ) : ℝ)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => by positivity
          intro k hk
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hk
          exact (hval m hm).2
      _ ≤ 1 + Real.log N := sum_Icc_inv_le_one_add_log N
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun m => decide (m₁ < m) = true)
    (fun m => (d : ℝ) / |(m₁ : ℝ) - m|)
  have hnot : A.filter (fun m => ¬ (decide (m₁ < m) = true)) =
      A.filter (fun m => decide (m₁ < m) = false) := by
    ext m; simp
  rw [← hsplit, hnot]
  linarith [side true, side false]

/-! ## The divisor weight -/

/-- **Schur's test** for a symmetric nonnegative kernel. -/
theorem sum_sum_mul_le_of_symm (s : Finset ℕ) (a : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j) :
    ∑ i ∈ s, ∑ j ∈ s, a i * a j * K i j ≤ ∑ i ∈ s, a i ^ 2 * ∑ j ∈ s, K i j := by
  have hle : ∀ i j, a i * a j * K i j ≤ (a i ^ 2 * K i j + a j ^ 2 * K i j) / 2 := fun i j => by
    nlinarith [mul_nonneg (hK0 i j) (sq_nonneg (a i - a j))]
  have hsym : ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * K i j = ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * K i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hK]
  calc ∑ i ∈ s, ∑ j ∈ s, a i * a j * K i j
      ≤ ∑ i ∈ s, ∑ j ∈ s, (a i ^ 2 * K i j + a j ^ 2 * K i j) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hle i j
    _ = ((∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * K i j) + ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * K i j) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i ∈ s, a i ^ 2 * ∑ j ∈ s, K i j := by
        rw [hsym, add_self_div_two]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- The kernel `K(m₁, m₂) = [m₁ ≠ m₂] Σ_{d ∣ (c, m₁ − m₂)} d/|m₁ − m₂|`. -/
def divisorKernel (c m₁ m₂ : ℕ) : ℝ :=
  ∑ d ∈ c.divisors,
    if m₂ ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m₂ then (d : ℝ) / |(m₁ : ℝ) - m₂| else 0

theorem divisorKernel_symm (c m₁ m₂ : ℕ) : divisorKernel c m₁ m₂ = divisorKernel c m₂ m₁ := by
  unfold divisorKernel
  refine Finset.sum_congr rfl fun d _ => ?_
  have h1 : (m₂ ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m₂) ↔ (m₁ ≠ m₂ ∧ (d : ℤ) ∣ (m₂ : ℤ) - m₁) :=
    ⟨fun h => ⟨h.1.symm, (dvd_sub_comm).1 h.2⟩, fun h => ⟨h.1.symm, (dvd_sub_comm).1 h.2⟩⟩
  by_cases h : m₂ ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m₂
  · rw [if_pos h, if_pos (h1.1 h), abs_sub_comm]
  · rw [if_neg h, if_neg (fun h' => h (h1.2 h'))]

theorem divisorKernel_nonneg (c m₁ m₂ : ℕ) : 0 ≤ divisorKernel c m₁ m₂ :=
  Finset.sum_nonneg fun d _ => by split_ifs <;> positivity

/-- **Row sums of the divisor kernel**: `Σ_{m₂} K(m₁, m₂) ≤ 2 τ(c)(1 + log N)`. -/
theorem sum_divisorKernel_le (c N m₁ : ℕ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, (m : ℤ) - m₁ ≤ N ∧ (m₁ : ℤ) - m ≤ N) :
    ∑ m₂ ∈ s, divisorKernel c m₁ m₂ ≤ 2 * c.divisors.card * (1 + Real.log N) := by
  unfold divisorKernel
  rw [Finset.sum_comm]
  calc ∑ d ∈ c.divisors, ∑ m₂ ∈ s,
        (if m₂ ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m₂ then (d : ℝ) / |(m₁ : ℝ) - m₂| else 0)
      = ∑ d ∈ c.divisors, ∑ m₂ ∈ s.filter (fun m => m ≠ m₁ ∧ (d : ℤ) ∣ (m₁ : ℤ) - m),
          (d : ℝ) / |(m₁ : ℝ) - m₂| :=
        Finset.sum_congr rfl fun d _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ d ∈ c.divisors, 2 * (1 + Real.log N) := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact sum_filter_dvd_div_abs_le N m₁ d (Nat.pos_of_mem_divisors hd) s hs
    _ = 2 * c.divisors.card * (1 + Real.log N) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The Ramanujan bound in kernel form: for `m₁ ≠ m₂`,
`|c_c(m₁ − m₂)| ≤ |m₁ − m₂| K(m₁, m₂)`. -/
theorem norm_ramanujan_le_divisorKernel (c : ℕ) [NeZero c] {m₁ m₂ : ℕ} (hne : m₁ ≠ m₂) :
    ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m₁ : ZMod c) - (m₂ : ZMod c)) * (x : ZMod c))‖ ≤
      |(m₁ : ℝ) - m₂| * divisorKernel c m₁ m₂ := by
  classical
  have hcast : ((m₁ : ZMod c) - (m₂ : ZMod c)) = (((m₁ : ℤ) - m₂ : ℤ) : ZMod c) := by push_cast; rfl
  have habs : 0 < |(m₁ : ℝ) - m₂| := by
    rw [abs_pos, sub_ne_zero]; exact_mod_cast hne
  refine (norm_sum_units_stdAddChar_le c _).trans (le_of_eq ?_)
  rw [hcast, divisorKernel, Finset.mul_sum]
  have hset : ((((m₁ : ℤ) - m₂ : ℤ) : ZMod c).val.gcd c).divisors =
      c.divisors.filter (fun d : ℕ => (d : ℤ) ∣ (m₁ : ℤ) - m₂) := by
    ext d
    rw [mem_divisors_gcd_val_iff, Finset.mem_filter]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : (d : ℤ) ∣ (m₁ : ℤ) - m₂
  · rw [if_pos hd, if_pos ⟨Ne.symm hne, hd⟩]
    field_simp
  · rw [if_neg hd, if_neg (fun h => hd h.2), mul_zero]

/-! ## The phase difference -/

theorem sqrt_two_le : Real.sqrt 2 ≤ 17 / 12 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem abs_sqrt_sub_le {N m₁ m₂ : ℕ} (h₁ : m₁ ∈ Finset.Ioc N (N + N))
    (h₂ : m₂ ∈ Finset.Ioc N (N + N)) :
    |Real.sqrt m₁ - Real.sqrt m₂| ≤ (Real.sqrt 2 - 1) * Real.sqrt N := by
  rw [Finset.mem_Ioc] at h₁ h₂
  have hs : ∀ m : ℕ, N < m → m ≤ N + N → Real.sqrt N ≤ Real.sqrt m ∧
      Real.sqrt m ≤ Real.sqrt 2 * Real.sqrt N := fun m h1 h2 => by
    refine ⟨Real.sqrt_le_sqrt (by exact_mod_cast h1.le), ?_⟩
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by have : (m : ℝ) ≤ N + N := by exact_mod_cast h2
                                linarith)
  obtain ⟨a1, a2⟩ := hs m₁ h₁.1 h₁.2
  obtain ⟨b1, b2⟩ := hs m₂ h₂.1 h₂.2
  rw [abs_le]; constructor <;> nlinarith

theorem abs_sqrt_sub_ge {N m₁ m₂ : ℕ} (h₁ : m₁ ∈ Finset.Ioc N (N + N))
    (h₂ : m₂ ∈ Finset.Ioc N (N + N)) :
    |(m₁ : ℝ) - m₂| ≤ 2 * Real.sqrt 2 * Real.sqrt N * |Real.sqrt m₁ - Real.sqrt m₂| := by
  rw [Finset.mem_Ioc] at h₁ h₂
  have hs : ∀ m : ℕ, m ≤ N + N → Real.sqrt m ≤ Real.sqrt 2 * Real.sqrt N := fun m h2 => by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by have : (m : ℝ) ≤ N + N := by exact_mod_cast h2
                                linarith)
  have e : (m₁ : ℝ) - m₂ = (Real.sqrt m₁ - Real.sqrt m₂) * (Real.sqrt m₁ + Real.sqrt m₂) := by
    have h1 := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) m₁)
    have h2 := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) m₂)
    nlinarith
  rw [e, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have := hs m₁ h₁.2
  have := hs m₂ h₂.2
  have := abs_nonneg (Real.sqrt m₁ - Real.sqrt m₂)
  nlinarith

/-! ## The smoothed exponential sum in `n` -/

/-- The cutoff `η(√(n/N))`. -/
def sqrtCut (N n : ℕ) : ℝ := sqrtWeight (Real.sqrt ((n : ℝ) / N))

theorem sqrtCut_nonneg (N n : ℕ) : 0 ≤ sqrtCut N n := sqrtWeight_nonneg _

theorem sqrtCut_eq_one {N n : ℕ} (hn : n ∈ Finset.Ioc N (N + N)) : sqrtCut N n = 1 := by
  rw [Finset.mem_Ioc] at hn
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h1 : (N : ℝ) < n := by exact_mod_cast hn.1
  have h2 : (n : ℝ) ≤ N + N := by exact_mod_cast hn.2
  apply sqrtWeight_eq_one
  · rw [Real.one_le_sqrt, one_le_div hN]; exact h1.le
  · rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ hN]; linarith

/-- `P(z, B) = Σ_n η(√(n/N)) e(nz/c) e(B√n)`. -/
def sqrtExpSum (c : ℕ) [NeZero c] (N : ℕ) (z : ZMod c) (B : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (3 * N + 1), (sqrtCut N n : ℂ) * ZMod.stdAddChar ((n : ZMod c) * z) *
    cexp (((2 * Real.pi * (B * Real.sqrt n)) : ℝ) * I)

theorem stdAddChar_natCast_mul (c : ℕ) [NeZero c] (n : ℕ) (z : ZMod c) :
    ZMod.stdAddChar ((n : ZMod c) * z) =
      cexp (((2 * Real.pi * ((z.val : ℝ) / c * n)) : ℝ) * I) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have : (n : ZMod c) * z = ((n * z.val : ℕ) : ZMod c) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  congr 1
  push_cast
  field_simp

theorem sqrtExpSum_eq_tsum (c : ℕ) [NeZero c] {N : ℕ} (hN : 1 ≤ N) (z : ZMod c) (B : ℝ) :
    sqrtExpSum c N z B = ∑' n : ℤ, sqrtSumFun N ((z.val : ℝ) / c) B n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tsum_eq_sum (s := (Finset.range (3 * N + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map, sqrtExpSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Nat.castEmbedding_apply, Int.cast_natCast]
    rw [sqrtSumFun, sqrtCut, stdAddChar_natCast_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · intro n hn
    apply sqrtSumFun_eq_zero hN0
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, not_exists,
      not_and] at hn
    by_cases h : 0 ≤ n
    · right
      have hk := hn n.toNat
      have hge : 3 * N + 1 ≤ n.toNat := by
        by_contra hlt
        exact hk (by omega) (Int.toNat_of_nonneg h)
      have : ((3 * N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : ((3 * N + 1 : ℕ) : ℤ) ≤ n := by omega
        exact_mod_cast this
      push_cast at this
      nlinarith
    · left
      have : (n : ℝ) < 0 := by exact_mod_cast (not_le.1 h)
      nlinarith

/-- **Poisson summation for `P(z, B)`**: `|P(z, B) − [z = 0] f̂_0(0)| ≤ C N (c/N)^p`. -/
theorem exists_sqrtExpSum_sub_le {p : ℕ} (hp : 2 ≤ p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℕ) [NeZero c] (N : ℕ) (z : ZMod c) (B : ℝ), 1 ≤ N → |B| * c ≤ 5 / 3 * Real.sqrt N →
      ‖sqrtExpSum c N z B - (if z = 0 then sqrtDiag N B else 0)‖ ≤
        C * N * ((c : ℝ) / N) ^ p := by
  obtain ⟨C, hC0, hC⟩ := exists_tsum_sqrtSumFun_sub_le hp
  refine ⟨C, hC0, fun c _ N z B hN hB => ?_⟩
  have h := hC N c z.val B (by exact_mod_cast hN) (Nat.one_le_iff_ne_zero.2 (NeZero.ne c))
    (ZMod.val_lt z) hB
  rw [sqrtExpSum_eq_tsum c hN]
  have hiff : (z.val = 0) ↔ (z = 0) := ZMod.val_eq_zero z
  by_cases hz : z = 0
  · rw [if_pos (hiff.2 hz)] at h
    rw [if_pos hz]
    exact h
  · rw [if_neg (fun h' => hz (hiff.1 h'))] at h
    rw [if_neg hz]
    exact h

/-! ## Opening the square -/

theorem kloostermanSum_mul_conj (c : ℕ) [NeZero c] (m₁ m₂ n : ZMod c) :
    kloostermanSum c m₁ n * conj (kloostermanSum c m₂ n) =
      ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
        ZMod.stdAddChar (m₁ * (x₁ : ZMod c) - m₂ * (x₂ : ZMod c)) *
          ZMod.stdAddChar (n * (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))) := by
  have hconj : (starRingEnd ℂ) (kloostermanSum c m₂ n) = kloostermanSum c (-m₂) (-n) :=
    star_kloostermanSum c m₂ n
  rw [hconj, kloostermanSum, kloostermanSum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
  rw [kloostermanPhase, kloostermanPhase, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem phase_mul_conj (A : ℝ) {m₁ m₂ n : ℝ} (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) :
    cexp (((2 * Real.pi * A * Real.sqrt (m₁ * n)) : ℝ) * I) *
        conj (cexp (((2 * Real.pi * A * Real.sqrt (m₂ * n)) : ℝ) * I)) =
      cexp (((2 * Real.pi * (A * (Real.sqrt m₁ - Real.sqrt m₂) * Real.sqrt n)) : ℝ) * I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add,
    Real.sqrt_mul h₁, Real.sqrt_mul h₂]
  congr 1
  push_cast
  ring

/-- The row `X_n = Σ_m ᾱ_m S(m, n; c) e(2θ√(mn)/c)`. -/
def smallRow (c : ℕ) [NeZero c] (N : ℕ) (α : ℕ → ℂ) (θ : ℝ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (N + N), conj (α m) * kloostermanSum c (m : ZMod c) (n : ZMod c) *
    cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)

theorem bilinear_eq_sum_smallRow (c : ℕ) [NeZero c] (N : ℕ) (α : ℕ → ℂ) (θ : ℝ) :
    ∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
        conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
          cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I) =
      ∑ n ∈ Finset.Ioc N (N + N), α n * smallRow c N α θ n := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smallRow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Opening the square.** -/
theorem sum_sqrtCut_mul_normSq_smallRow (c : ℕ) [NeZero c] (N : ℕ) (α : ℕ → ℂ) (θ : ℝ) :
    (((∑ n ∈ Finset.range (3 * N + 1), sqrtCut N n * ‖smallRow c N α θ n‖ ^ 2 : ℝ)) : ℂ) =
      ∑ m₁ ∈ Finset.Ioc N (N + N), ∑ m₂ ∈ Finset.Ioc N (N + N), conj (α m₁) * α m₂ *
        ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
          ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c)) *
            sqrtExpSum c N (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))
              (2 * θ / c * (Real.sqrt m₁ - Real.sqrt m₂)) := by
  set S := Finset.Ioc N (N + N)
  set R := Finset.range (3 * N + 1)
  set T : ℕ → ℕ → ℕ → (ZMod c)ˣ → (ZMod c)ˣ → ℂ := fun n m₁ m₂ x₁ x₂ =>
    conj (α m₁) * α m₂ *
      ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c)) *
      ((sqrtCut N n : ℂ) *
        ZMod.stdAddChar ((n : ZMod c) * (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))) *
        cexp (((2 * Real.pi * (2 * θ / c * (Real.sqrt m₁ - Real.sqrt m₂) * Real.sqrt n)) : ℝ) * I))
  have hn : ∀ n, (sqrtCut N n : ℂ) * ((‖smallRow c N α θ n‖ : ℂ)) ^ 2 =
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ, T n m₁ m₂ x₁ x₂ := by
    intro n
    rw [← Complex.mul_conj', smallRow, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [map_mul, map_mul, Complex.conj_conj]
    have hK := kloostermanSum_mul_conj c (m₁ : ZMod c) (m₂ : ZMod c) (n : ZMod c)
    have hE := phase_mul_conj (2 * θ / c) (Nat.cast_nonneg (α := ℝ) m₁)
      (Nat.cast_nonneg (α := ℝ) m₂) (n := (n : ℝ))
    rw [show (sqrtCut N n : ℂ) * (conj (α m₁) * kloostermanSum c (m₁ : ZMod c) (n : ZMod c) *
        cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m₁ : ℝ) * n)) : ℝ) * I) *
        (α m₂ * conj (kloostermanSum c (m₂ : ZMod c) (n : ZMod c)) *
          conj (cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m₂ : ℝ) * n)) : ℝ) * I)))) =
        conj (α m₁) * α m₂ * (kloostermanSum c (m₁ : ZMod c) (n : ZMod c) *
          conj (kloostermanSum c (m₂ : ZMod c) (n : ZMod c))) *
          ((sqrtCut N n : ℂ) * (cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m₁ : ℝ) * n)) : ℝ) * I) *
            conj (cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m₂ : ℝ) * n)) : ℝ) * I)))) by ring,
      hK, hE, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x₂ _ => ?_
    simp only [T]
    ring
  push_cast
  rw [Finset.sum_congr rfl fun n _ => hn n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  simp only [T, sqrtExpSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-! ## The resonant terms -/

theorem card_units_le (c : ℕ) [NeZero c] : (Fintype.card (ZMod c)ˣ : ℝ) ≤ c := by
  rw [ZMod.card_units_eq_totient]; exact_mod_cast Nat.totient_le c

/-- Only `x₁ = x₂` survives the Poisson step. -/
theorem norm_resonant_le (c : ℕ) [NeZero c] (m₁ m₂ : ℕ) (Δ : ℂ) (E : ℝ) (P : ZMod c → ℂ)
    (hP : ∀ z, ‖P z - (if z = 0 then Δ else 0)‖ ≤ E) :
    ‖∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
        ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c)) *
          P (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))‖ ≤
      ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m₁ : ZMod c) - (m₂ : ZMod c)) * (x : ZMod c))‖ * ‖Δ‖ +
        (c : ℝ) ^ 2 * E := by
  classical
  set ψ := fun (x₁ x₂ : (ZMod c)ˣ) =>
    ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c))
  set z := fun (x₁ x₂ : (ZMod c)ˣ) => ((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c)
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hP 0)
  have hsplit : ∀ x₁ x₂, ψ x₁ x₂ * P (z x₁ x₂) = ψ x₁ x₂ * (if z x₁ x₂ = 0 then Δ else 0) +
      ψ x₁ x₂ * (P (z x₁ x₂) - (if z x₁ x₂ = 0 then Δ else 0)) := fun x₁ x₂ => by ring
  have hdiag : ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ, ψ x₁ x₂ * (if z x₁ x₂ = 0 then Δ else 0) =
      (∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m₁ : ZMod c) - (m₂ : ZMod c)) * (x : ZMod c))) * Δ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_eq_single x₁]
    · simp only [z, sub_self, if_true, ψ]
      congr 2; ring
    · intro x₂ _ hne
      have : z x₁ x₂ ≠ 0 := by
        simp only [z]
        intro h
        apply hne
        have h' : ((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) = ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c) := sub_eq_zero.1 h
        exact (inv_injective (Units.ext h')).symm
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ x₁) h
  have hψ : ∀ x₁ x₂, ‖ψ x₁ x₂‖ = 1 := fun x₁ x₂ => by
    simp only [ψ, ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  have hrest : ‖∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
      ψ x₁ x₂ * (P (z x₁ x₂) - (if z x₁ x₂ = 0 then Δ else 0))‖ ≤ (c : ℝ) ^ 2 * E := by
    calc _ ≤ ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ, E := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x₁ _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun x₂ _ => ?_))
          rw [norm_mul, hψ, one_mul]; exact hP _
      _ = (Fintype.card (ZMod c)ˣ : ℝ) ^ 2 * E := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ (c : ℝ) ^ 2 * E := by
          have := card_units_le c
          gcongr
  change ‖∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ, ψ x₁ x₂ * P (z x₁ x₂)‖ ≤ _
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hdiag]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  linarith [hrest]

theorem norm_ramanujan_self_le (c : ℕ) [NeZero c] (m : ℕ) :
    ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m : ZMod c) - (m : ZMod c)) * (x : ZMod c))‖ ≤ c := by
  simp only [sub_self, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Complex.norm_natCast]
  exact_mod_cast (ZMod.card_units_eq_totient c).symm ▸ Nat.totient_le c

/-- **DI (1.27), with the Poisson error made explicit.** For `1 ≤ |θ| ≤ 2` and every `p ≥ 2`,

`|Σ_{m,n ∈ (N,2N]} ᾱ_m α_n S(m,n;c) e(2θ√(mn)/c)|² ≤
  C (Σ|α|²)² (c N τ(c)(1 + log N) + c² N² (c/N)^p)`. -/
theorem exists_bilinear_kloosterman_small_le {p : ℕ} (hp : 2 ≤ p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℕ) [NeZero c] (N : ℕ), 1 ≤ N → ∀ (α : ℕ → ℂ) (θ : ℝ), 1 ≤ |θ| → |θ| ≤ 2 →
      ‖∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
          conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
            cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)‖ ^ 2 ≤
        C * (∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2) ^ 2 *
          ((c : ℝ) * N * c.divisors.card * (1 + Real.log N) +
            (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p) := by
  obtain ⟨C₁, hC₁0, hP⟩ := exists_sqrtExpSum_sub_le hp
  obtain ⟨D, hD0, hDiag⟩ := exists_sqrtDiag_le
  refine ⟨3 + 4 * D + C₁, by positivity, fun c _ N hN α θ hθ1 hθ2 => ?_⟩
  set S := Finset.Ioc N (N + N)
  set R := Finset.range (3 * N + 1)
  set A := ∑ n ∈ S, ‖α n‖ ^ 2
  set X := smallRow c N α θ
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
  have hτ : (1 : ℝ) ≤ c.divisors.card := by
    have : 0 < c.divisors.card :=
      Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (NeZero.ne c)⟩
    exact_mod_cast this
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  set E := C₁ * N * ((c : ℝ) / N) ^ p
  have hE0 : 0 ≤ E := by positivity
  -- Cauchy–Schwarz in `n`
  have hCS : ‖∑ m ∈ S, ∑ n ∈ S, conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)‖ ^ 2 ≤
      A * ∑ n ∈ S, ‖X n‖ ^ 2 := by
    rw [bilinear_eq_sum_smallRow]
    have h1 : ‖∑ n ∈ S, α n * X n‖ ≤ ∑ n ∈ S, ‖α n‖ * ‖X n‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => norm_mul _ _))
    calc ‖∑ n ∈ S, α n * X n‖ ^ 2 ≤ (∑ n ∈ S, ‖α n‖ * ‖X n‖) ^ 2 := by gcongr
      _ ≤ A * ∑ n ∈ S, ‖X n‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq S _ _
  -- the smooth majorant
  have hmaj : ∑ n ∈ S, ‖X n‖ ^ 2 ≤ ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 := by
    have hSR : S ⊆ R := fun n hn => by
      rw [Finset.mem_Ioc] at hn; rw [Finset.mem_range]; omega
    calc ∑ n ∈ S, ‖X n‖ ^ 2 = ∑ n ∈ S, sqrtCut N n * ‖X n‖ ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [sqrtCut_eq_one hn, one_mul]
      _ ≤ ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hSR fun n _ _ =>
            mul_nonneg (sqrtCut_nonneg N n) (by positivity)
  -- the pointwise bound for the resonant sums
  set b : ℕ → ℕ → ℝ := fun m₁ m₂ =>
    3 * c * N * (if m₁ = m₂ then 1 else 0) + 2 * D * c * N * divisorKernel c m₁ m₂ +
      (c : ℝ) ^ 2 * E
  have hb : ∀ m₁ ∈ S, ∀ m₂ ∈ S, ‖∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
      ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c)) *
        sqrtExpSum c N (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))
          (2 * θ / c * (Real.sqrt m₁ - Real.sqrt m₂))‖ ≤ b m₁ m₂ := by
    intro m₁ hm₁ m₂ hm₂
    set B := 2 * θ / c * (Real.sqrt m₁ - Real.sqrt m₂)
    have hBabs : |B| = 2 * |θ| / c * |Real.sqrt m₁ - Real.sqrt m₂| := by
      simp only [B]; rw [abs_mul, abs_div, abs_mul, abs_of_pos hc0]; norm_num
    have hBc : |B| * c ≤ 5 / 3 * Real.sqrt N := by
      have h1 := abs_sqrt_sub_le hm₁ hm₂
      have h2 := sqrt_two_le
      have h3 : |B| * c = 2 * |θ| * |Real.sqrt m₁ - Real.sqrt m₂| := by
        rw [hBabs]; field_simp
      rw [h3]
      have := Real.sqrt_nonneg (N : ℝ)
      have := abs_nonneg (Real.sqrt m₁ - Real.sqrt m₂)
      calc 2 * |θ| * |Real.sqrt m₁ - Real.sqrt m₂| ≤ 2 * 2 * ((Real.sqrt 2 - 1) * Real.sqrt N) := by
            gcongr
        _ ≤ 5 / 3 * Real.sqrt N := by nlinarith
    refine (norm_resonant_le c m₁ m₂ (sqrtDiag N B) E _ fun z => hP c N z B hN hBc).trans ?_
    simp only [b]
    by_cases heq : m₁ = m₂
    · subst heq
      rw [if_pos rfl]
      have h1 := norm_ramanujan_self_le c m₁
      have h2 := norm_sqrtDiag_le hN0 B
      have := divisorKernel_nonneg c m₁ m₁
      have : ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m₁ : ZMod c) - (m₁ : ZMod c)) * (x : ZMod c))‖ *
          ‖sqrtDiag N B‖ ≤ c * (3 * N) := by gcongr
      have : 0 ≤ 2 * D * c * N * divisorKernel c m₁ m₁ := by positivity
      linarith
    · rw [if_neg heq]
      have hsub : 0 < |Real.sqrt m₁ - Real.sqrt m₂| := by
        rw [abs_pos, sub_ne_zero]
        intro h
        apply heq
        have := congrArg (fun x => x ^ 2) h
        simp only [Real.sq_sqrt (Nat.cast_nonneg _)] at this
        exact_mod_cast this
      have hB0 : B ≠ 0 := by
        rw [← abs_pos, hBabs]
        have : 0 < |θ| := by linarith
        positivity
      have h1 := norm_ramanujan_le_divisorKernel c heq
      have h2 := hDiag N B hN0 hB0
      have h3 := abs_sqrt_sub_ge hm₁ hm₂
      have hK0 := divisorKernel_nonneg c m₁ m₂
      -- `|m₁ − m₂| √N/|B| ≤ √2 c N ≤ 2 c N`
      have hkey : |(m₁ : ℝ) - m₂| * (D * Real.sqrt N / |B|) ≤ 2 * D * c * N := by
        have hBpos : 0 < |B| := abs_pos.2 hB0
        have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
        have hs2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hBc2 : |B| * c = 2 * |θ| * |Real.sqrt m₁ - Real.sqrt m₂| := by
          rw [hBabs]; field_simp
        have h2d : 2 * |Real.sqrt m₁ - Real.sqrt m₂| ≤ |B| * c := by
          rw [hBc2]; nlinarith
        rw [mul_div_assoc', div_le_iff₀ hBpos]
        calc |(m₁ : ℝ) - m₂| * (D * Real.sqrt N)
            ≤ (2 * Real.sqrt 2 * Real.sqrt N * |Real.sqrt m₁ - Real.sqrt m₂|) * (D * Real.sqrt N) := by
              gcongr
          _ = Real.sqrt 2 * D * (Real.sqrt N * Real.sqrt N) * (2 * |Real.sqrt m₁ - Real.sqrt m₂|) := by
              ring
          _ = Real.sqrt 2 * D * N * (2 * |Real.sqrt m₁ - Real.sqrt m₂|) := by rw [hsqN]
          _ ≤ Real.sqrt 2 * D * N * (|B| * c) := by gcongr
          _ ≤ 2 * D * N * (|B| * c) := by gcongr
          _ = 2 * D * c * N * |B| := by ring
      calc ‖∑ x : (ZMod c)ˣ, ZMod.stdAddChar (((m₁ : ZMod c) - (m₂ : ZMod c)) * (x : ZMod c))‖ *
            ‖sqrtDiag N B‖ + (c : ℝ) ^ 2 * E
          ≤ (|(m₁ : ℝ) - m₂| * divisorKernel c m₁ m₂) * (D * Real.sqrt N / |B|) +
              (c : ℝ) ^ 2 * E := by gcongr
        _ = divisorKernel c m₁ m₂ * (|(m₁ : ℝ) - m₂| * (D * Real.sqrt N / |B|)) +
              (c : ℝ) ^ 2 * E := by ring
        _ ≤ divisorKernel c m₁ m₂ * (2 * D * c * N) + (c : ℝ) ^ 2 * E := by gcongr
        _ = _ := by ring
  -- summing over `m₁, m₂`
  have hQ : ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 ≤
      ∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * b m₁ m₂ := by
    have hreal := sum_sqrtCut_mul_normSq_smallRow c N α θ
    have hnn : 0 ≤ ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => mul_nonneg (sqrtCut_nonneg N n) (by positivity)
    calc ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2
        = ‖(((∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖∑ m₁ ∈ S, ∑ m₂ ∈ S, conj (α m₁) * α m₂ *
            ∑ x₁ : (ZMod c)ˣ, ∑ x₂ : (ZMod c)ˣ,
              ZMod.stdAddChar ((m₁ : ZMod c) * (x₁ : ZMod c) - (m₂ : ZMod c) * (x₂ : ZMod c)) *
                sqrtExpSum c N (((x₁⁻¹ : (ZMod c)ˣ) : ZMod c) - ((x₂⁻¹ : (ZMod c)ˣ) : ZMod c))
                  (2 * θ / c * (Real.sqrt m₁ - Real.sqrt m₂))‖ := by rw [hreal]
      _ ≤ ∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * b m₁ m₂ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₁ hm₁ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂ hm₂ => ?_))
          rw [norm_mul, norm_mul, Complex.norm_conj]
          gcongr
          exact hb m₁ hm₁ m₂ hm₂
  -- the three pieces
  have hdiag : ∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * (if m₁ = m₂ then (1 : ℝ) else 0) = A := by
    refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
    rw [Finset.sum_eq_single m₁ (fun m₂ _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
      (fun h => absurd hm₁ h), if_pos rfl, mul_one, sq]
  have hker : ∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * divisorKernel c m₁ m₂ ≤
      A * (2 * c.divisors.card * (1 + Real.log N)) := by
    refine (sum_sum_mul_le_of_symm S (fun m => ‖α m‖) (divisorKernel c) (divisorKernel_symm c)
      (divisorKernel_nonneg c)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m₁ hm₁ => ?_
    refine mul_le_mul_of_nonneg_left (sum_divisorKernel_le c N m₁ S fun m hm => ?_) (by positivity)
    rw [Finset.mem_Ioc] at hm hm₁
    constructor <;> omega
  have hsumsq : (∑ m ∈ S, ‖α m‖) ^ 2 ≤ N * A := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun m => ‖α m‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have hcard : (S.card : ℝ) = N := by
      simp only [S, Nat.card_Ioc]; rw [Nat.add_sub_cancel]
    rw [hcard] at h
    exact h
  have hpieces : ∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * b m₁ m₂ =
      3 * c * N * (∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * (if m₁ = m₂ then (1 : ℝ) else 0)) +
        2 * D * c * N * (∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * divisorKernel c m₁ m₂) +
          (c : ℝ) ^ 2 * E * (∑ m ∈ S, ‖α m‖) ^ 2 := by
    have e1 : ∀ m₁ m₂, ‖α m₁‖ * ‖α m₂‖ * b m₁ m₂ =
        3 * c * N * (‖α m₁‖ * ‖α m₂‖ * (if m₁ = m₂ then (1 : ℝ) else 0)) +
          2 * D * c * N * (‖α m₁‖ * ‖α m₂‖ * divisorKernel c m₁ m₂) +
            (c : ℝ) ^ 2 * E * (‖α m₁‖ * ‖α m₂‖) := fun m₁ m₂ => by simp only [b]; ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sq (∑ m ∈ S, ‖α m‖), Finset.sum_mul]
  have htotal : ∑ n ∈ R, sqrtCut N n * ‖X n‖ ^ 2 ≤
      A * (3 * c * N + 4 * D * c * N * c.divisors.card * (1 + Real.log N) +
        (c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) := by
    refine hQ.trans ?_
    rw [hpieces, hdiag]
    have h1 : 2 * D * c * N * (∑ m₁ ∈ S, ∑ m₂ ∈ S, ‖α m₁‖ * ‖α m₂‖ * divisorKernel c m₁ m₂) ≤
        2 * D * c * N * (A * (2 * c.divisors.card * (1 + Real.log N))) := by gcongr
    have h2 : (c : ℝ) ^ 2 * E * (∑ m ∈ S, ‖α m‖) ^ 2 ≤ (c : ℝ) ^ 2 * E * (N * A) := by gcongr
    have h3 : (c : ℝ) ^ 2 * E * (N * A) = A * ((c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) := by
      simp only [E]; ring
    have h4 : 2 * D * c * N * (A * (2 * c.divisors.card * (1 + Real.log N))) =
        A * (4 * D * c * N * c.divisors.card * (1 + Real.log N)) := by ring
    have h5 : A * (3 * c * N + 4 * D * c * N * c.divisors.card * (1 + Real.log N) +
        (c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) = 3 * c * N * A +
          A * (4 * D * c * N * c.divisors.card * (1 + Real.log N)) +
            A * ((c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) := by ring
    rw [h5]
    linarith [h1, h2, h3, h4]
  -- conclusion
  have hfin : A * (3 * c * N + 4 * D * c * N * c.divisors.card * (1 + Real.log N) +
      (c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) ≤
      (3 + 4 * D + C₁) * A * ((c : ℝ) * N * c.divisors.card * (1 + Real.log N) +
        (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p) := by
    set L := (c : ℝ) * N * c.divisors.card * (1 + Real.log N)
    set Q := (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p
    have hcN : 0 ≤ (c : ℝ) * N := by positivity
    have hx : (c : ℝ) * N ≤ L := by
      have h1 : 1 ≤ (c.divisors.card : ℝ) * (1 + Real.log N) := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 hcN
      simp only [L]; linarith
    have hy : 0 ≤ Q := by positivity
    have hz : 0 ≤ L := hcN.trans hx
    have e1 : A * (3 * c * N + 4 * D * c * N * c.divisors.card * (1 + Real.log N) +
        (c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p) =
        3 * (A * ((c : ℝ) * N)) + 4 * D * (A * L) + C₁ * (A * Q) := by simp only [L, Q]; ring
    have e2 : (3 + 4 * D + C₁) * A * (L + Q) =
        3 * (A * L) + 4 * D * (A * L) + C₁ * (A * L) + (3 + 4 * D + C₁) * (A * Q) := by ring
    rw [e1, e2]
    have k1 := mul_le_mul_of_nonneg_left hx hA0
    have k2 : 0 ≤ C₁ * (A * L) := by positivity
    have k3 : 0 ≤ (3 + 4 * D) * (A * Q) := by positivity
    linarith [k1, k2, k3]
  calc _ ≤ A * ∑ n ∈ S, ‖X n‖ ^ 2 := hCS
    _ ≤ A * (A * (3 * c * N + 4 * D * c * N * c.divisors.card * (1 + Real.log N) +
          (c : ℝ) ^ 2 * C₁ * N ^ 2 * ((c : ℝ) / N) ^ p)) := by
        gcongr
        exact hmaj.trans htotal
    _ ≤ A * ((3 + 4 * D + C₁) * A * ((c : ℝ) * N * c.divisors.card * (1 + Real.log N) +
          (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p)) := by gcongr
    _ = _ := by ring

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
