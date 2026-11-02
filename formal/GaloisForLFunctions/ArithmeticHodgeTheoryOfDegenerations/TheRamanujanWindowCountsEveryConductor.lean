import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAPeriodicTwist
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure

/-!
# The Ramanujan window counts every conductor

The window twisted by the Ramanujan sum `c_m(n) = Σ_{de = m} μ(d) e [e ∣ n]`, `m ≥ 2`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Ramanujan sums as twists -/

/-- The Ramanujan sum `c_m(n) = Σ_{de = m} μ(d) e [e ∣ n]` as a real twist. -/
def ramTwist (m n : ℕ) : ℝ :=
  ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
    (if x.2 ∣ n then (x.2 : ℝ) else 0)

theorem ramanujanSum_eq_ramTwist {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ArithmeticEffectivityTheory.ramanujanSum m n = (ramTwist m n : ℂ) := by
  rw [ArithmeticEffectivityTheory.ramanujanSum_eq_sum_moebius hm, ramTwist]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem ramTwist_add_self (m n : ℕ) : ramTwist m (n + m) = ramTwist m n := by
  unfold ramTwist
  refine sum_congr rfl fun x hx => ?_
  simp only [Nat.dvd_add_left (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))]

theorem sum_antidiagonal_moebius {m : ℕ} (hm : 1 < m) :
    ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply_ne (by omega : m ≠ 1)] at h
  have h2 : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) = 0 := by
    rw [← h]
    refine sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 :=
      Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
    simp [hx2]
  exact_mod_cast h2

/-- `Σ_{r<m} ω^r = m [ω = 1]` for an `m`-th root of unity `ω`. -/
theorem sum_range_pow_root {m : ℕ} {ω : ℂ} (hω : ω ^ m = 1) :
    ∑ r ∈ range m, ω ^ r = if ω = 1 then (m : ℂ) else 0 := by
  split_ifs with h1
  · simp [h1]
  · have h := mul_neg_geom_sum ω m
    rw [hω, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm h1))

/-- Ramanujan sums of conductor `m ≥ 2` are mean-zero twists. -/
theorem meanZeroTwist_ramTwist {m : ℕ} (hm : 1 < m) : MeanZeroTwist (ramTwist m) m where
  pos := by omega
  periodic := ramTwist_add_self m
  mean_zero := by
    have hm0 : 0 < m := by omega
    have h : ((∑ r ∈ range m, ramTwist m r : ℝ) : ℂ) = 0 := by
      push_cast
      simp_rw [← ramanujanSum_eq_ramTwist hm0, ArithmeticEffectivityTheory.ramanujanSum]
      rw [Finset.sum_comm]
      refine sum_eq_zero fun ζ hζ => ?_
      have hζp := (mem_primitiveRoots hm0).mp hζ
      rw [sum_range_pow_root hζp.pow_eq_one, if_neg]
      intro h1
      rw [h1] at hζp
      have := hζp.eq_orderOf
      rw [orderOf_one] at this
      omega
    exact_mod_cast h

/-- **The autocorrelation of a Ramanujan sum is itself**: `Σ_{r<m} c_m(r) c_m(r + s) = m c_m(s)`. -/
theorem sum_ramTwist_mul_add {m : ℕ} (hm : 0 < m) (s : ℕ) :
    ∑ r ∈ range m, ramTwist m r * ramTwist m (r + s) = m * ramTwist m s := by
  have h : ((∑ r ∈ range m, ramTwist m r * ramTwist m (r + s) : ℝ) : ℂ) =
      ((m * ramTwist m s : ℝ) : ℂ) := by
    push_cast
    simp_rw [← ramanujanSum_eq_ramTwist hm, ArithmeticEffectivityTheory.ramanujanSum]
    set P := primitiveRoots m ℂ with hP
    have e1 : ∑ r ∈ range m, (∑ ζ ∈ P, ζ ^ r) * ∑ ξ ∈ P, ξ ^ (r + s) =
        ∑ ξ ∈ P, ξ ^ s * ∑ ζ ∈ P, ∑ r ∈ range m, (ζ * ξ) ^ r := by
      have hpt : ∀ r, (∑ ζ ∈ P, ζ ^ r) * ∑ ξ ∈ P, ξ ^ (r + s) =
          ∑ ξ ∈ P, ξ ^ s * ∑ ζ ∈ P, (ζ * ξ) ^ r := fun r => by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
        refine sum_congr rfl fun ξ _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun ζ _ => ?_
        rw [pow_add, mul_pow]
        ring
      rw [sum_congr rfl fun r _ => hpt r, Finset.sum_comm]
      refine sum_congr rfl fun ξ _ => ?_
      rw [← Finset.mul_sum, Finset.sum_comm]
    have e2 : ∀ ξ ∈ P, ∑ ζ ∈ P, ∑ r ∈ range m, (ζ * ξ) ^ r = m := fun ξ hξ => by
      have hξp := (mem_primitiveRoots hm).mp hξ
      have hξ0 : ξ ≠ 0 := hξp.ne_zero hm.ne'
      have hroot : ∀ ζ ∈ P, ∑ r ∈ range m, (ζ * ξ) ^ r = if ζ = ξ⁻¹ then (m : ℂ) else 0 :=
        fun ζ hζ => by
          have hζp := (mem_primitiveRoots hm).mp hζ
          rw [sum_range_pow_root (by rw [mul_pow, hζp.pow_eq_one, hξp.pow_eq_one, one_mul])]
          congr 1
          exact propext (mul_eq_one_iff_eq_inv₀ hξ0)
      rw [sum_congr rfl hroot, Finset.sum_ite_eq' P ξ⁻¹ (fun _ => (m : ℂ)),
        if_pos ((mem_primitiveRoots hm).mpr hξp.inv)]
    rw [e1, sum_congr rfl fun ξ hξ => by rw [e2 ξ hξ], ← Finset.sum_mul, mul_comm]
  exact_mod_cast h

theorem periodicExt_ramTwist_add {m : ℕ} (hm : 0 < m) (r : ℕ) (δ : ℤ) :
    periodicExt (ramTwist m) m (r + δ) = ramTwist m (r + (δ % m).toNat) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hs : (((δ % m).toNat : ℕ) : ℤ) = δ % m := Int.toNat_of_nonneg (Int.emod_nonneg δ hm'.ne')
  unfold periodicExt
  have e : ((r : ℤ) + δ) % m = (((r + (δ % m).toNat) % m : ℕ) : ℤ) := by
    push_cast
    rw [hs, Int.add_emod_emod]
  rw [e, Int.toNat_natCast, periodic_mod (ramTwist_add_self m)]

/-- The autocorrelation of the Ramanujan twist is the Ramanujan sum at the offset. -/
theorem autoCorr_ramTwist {m : ℕ} (hm : 0 < m) (δ : ℤ) :
    autoCorr (ramTwist m) m δ = periodicExt (ramTwist m) m δ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold autoCorr periodMean
  simp_rw [periodicExt_ramTwist_add hm]
  rw [sum_ramTwist_mul_add hm, ← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul, periodicExt]

/-- At an integer offset the Ramanujan sum is `Σ_{de = m} μ(d) e [e ∣ δ]`. -/
theorem periodicExt_ramTwist_eq {m : ℕ} (hm : 0 < m) (δ : ℤ) :
    periodicExt (ramTwist m) m δ = ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℝ) * (if (x.2 : ℤ) ∣ δ then (x.2 : ℝ) else 0) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hs : (((δ % m).toNat : ℕ) : ℤ) = δ % m := Int.toNat_of_nonneg (Int.emod_nonneg δ hm'.ne')
  unfold periodicExt ramTwist
  refine sum_congr rfl fun x hx => ?_
  have hxm : (x.2 : ℤ) ∣ m :=
    Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
  have hiff : x.2 ∣ (δ % m).toNat ↔ (x.2 : ℤ) ∣ δ := by
    rw [← Int.natCast_dvd_natCast, hs]
    have e := Int.mul_ediv_add_emod δ m
    constructor
    · intro h1
      rw [← e]
      exact dvd_add (dvd_mul_of_dvd_left hxm _) h1
    · intro h1
      have : δ % m = δ - m * (δ / m) := by linarith
      rw [this]
      exact dvd_sub h1 (dvd_mul_of_dvd_left hxm _)
  by_cases h1 : (x.2 : ℤ) ∣ δ
  · rw [if_pos (hiff.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]

/-! ### The energy of a Ramanujan window -/

/-- A divisibility lattice sum in the offset: `Σ_{|δ| ≤ D, e ∣ δ} G(δ/a) = Σ_j G(j/(a/e))`. -/
theorem sum_offset_dvd_eq {G : ℝ → ℝ} (hG1 : ∀ t, 1 ≤ |t| → G t = 0) {e : ℕ} (he : 0 < e)
    {a : ℝ} (ha : 0 < a) {D : ℕ} (haD : a ≤ D) :
    ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, (if (e : ℤ) ∣ δ then G (δ * a⁻¹) else 0) =
      ∑' j : ℤ, G (j * (a / e)⁻¹) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hinj : Function.Injective (fun i : ℤ => (e : ℤ) * i) := fun i k hik => by
    simp only at hik
    exact mul_left_cancel₀ (by exact_mod_cast he.ne') hik
  have hsub : ∑' i : ℤ, G (i * (a / e)⁻¹) =
      ∑' j : ℤ, (if (e : ℤ) ∣ j then G (j * a⁻¹) else 0) := by
    rw [← hinj.tsum_eq (f := fun j : ℤ => if (e : ℤ) ∣ j then G (j * a⁻¹) else 0)]
    · refine tsum_congr fun i => ?_
      simp only [dvd_mul_right, if_true]
      congr 1
      push_cast
      field_simp
    · intro j hj
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hj
      obtain ⟨⟨k, hk⟩, -⟩ := hj
      exact ⟨k, by show (e : ℤ) * k = j; omega⟩
  rw [hsub, tsum_eq_sum (s := Finset.Icc (-(D : ℤ)) D)]
  intro j hj
  split_ifs with hej
  · refine hG1 _ ?_
    rw [abs_mul, abs_inv, abs_of_pos ha, le_mul_inv_iff₀ ha, one_mul]
    rw [Finset.mem_Icc, not_and_or] at hj
    rcases hj with h | h
    · push Not at h
      have : (j : ℝ) < -D := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · push Not at h
      have : (D : ℝ) < j := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  · rfl

/-- **The offset sum of a Ramanujan window**:
`Σ_{|δ| ≤ D} c_m(δ) G(δ/a) = 2a Σ_{de = m} μ(d) a_φ(a/e)` for `m ≥ 2`, `a ≤ D`. -/
theorem sum_offset_ramTwist_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {m : ℕ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) {D : ℕ} (haD : a ≤ D) :
    ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * a⁻¹) =
      2 * a * ∑ x ∈ m.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ) * aliasDensity φ (a / x.2) := by
  have hm0 : 0 < m := by omega
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  simp_rw [autoCorr_ramTwist hm0, periodicExt_ramTwist_eq hm0, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hx : ∀ x ∈ m.divisorsAntidiagonal, ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      (ArithmeticFunction.moebius x.1 : ℝ) * (if (x.2 : ℤ) ∣ δ then (x.2 : ℝ) else 0) *
        shellAutocorr φ (δ * a⁻¹) =
      (ArithmeticFunction.moebius x.1 : ℝ) * (a * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (a / x.2)))
      := fun x hx => by
    have he : 0 < x.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    have he0 : (0 : ℝ) < x.2 := by exact_mod_cast he
    have hl := sum_offset_dvd_eq hG1 he ha haD
    rw [tsum_shellAutocorr_eq hφ hφsupp (div_pos ha he0)] at hl
    have e : ∀ δ ∈ Finset.Icc (-(D : ℤ)) D, (ArithmeticFunction.moebius x.1 : ℝ) *
        (if (x.2 : ℤ) ∣ δ then (x.2 : ℝ) else 0) * shellAutocorr φ (δ * a⁻¹) =
        (ArithmeticFunction.moebius x.1 : ℝ) * x.2 *
          (if (x.2 : ℤ) ∣ δ then shellAutocorr φ (δ * a⁻¹) else 0) := fun δ _ => by
      split_ifs <;> ring
    rw [sum_congr rfl e, ← Finset.mul_sum, hl]
    field_simp
  rw [sum_congr rfl hx]
  have hsplit : ∀ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
      (a * ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (a / x.2))) =
      (ArithmeticFunction.moebius x.1 : ℝ) * (a * (∫ u, φ u) ^ 2) +
        2 * a * ((ArithmeticFunction.moebius x.1 : ℝ) * aliasDensity φ (a / x.2)) :=
    fun x _ => by ring
  rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_mul, sum_antidiagonal_moebius hm, zero_mul,
    zero_add, ← mul_sum]

/-- **The energy of a Ramanujan window**: for `m ≥ 2` and `1 ≤ c ≤ N/4`,
`E_N = 2π Σ_{de = m} μ(d) 𝒜_N(c/e) + O(c/N)`. -/
theorem abs_ramEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 1 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * ∑ x ∈ m.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℝ) * horizonAlias φ h (c / x.2) N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := periodicEnergy_le hφ hφsupp hh hA hsupp (M := m) (by omega)
    (ramTwist_add_self m)
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * ∑ x ∈ m.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ) * horizonAlias φ h (c / x.2) N := by
    have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
        ∑ x ∈ m.divisorsAntidiagonal, 2 * c / N * ((ArithmeticFunction.moebius x.1 : ℝ) *
          (h (Real.log n - Real.log N) ^ 2 * aliasDensity φ (c / x.2 * n / N))) := fun n hn => by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      have ha0 : 0 < c * n / N := by positivity
      have haD : c * n / N ≤ ⌈c⌉₊ := by
        refine le_trans ?_ (Nat.le_ceil c)
        rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
      rw [sum_offset_ramTwist_eq hφ hφsupp hm ha0 haD, horizonWeights, div_pow,
        Real.sq_sqrt hn0.le, Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [show c * n / N / x.2 = c / x.2 * n / N by ring]
      field_simp
    rw [sum_congr rfl e, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    unfold horizonAlias
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    field_simp
  rw [← hmain]
  exact hK c hc N hcN

/-! ### The Ramanujan block is quiet below its first resonance -/

/-- **Kuzmin–Landau on a sublattice**: for `0 < τ ≤ π n₀/q` and `n₀ + k ≤ N`, the partial sums of
`n^{iτ}` over the multiples of `q` in `[n₀, n₀ + k]` are at most `3πN/(qτ) + 1`. -/
theorem norm_partial_dvd_cpow_le {q : ℕ} (hq : 0 < q) {n₀ N k : ℕ} (hn₀ : 1 ≤ n₀)
    (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / q) :
    ‖∑ m ∈ range (k + 1), (if q ∣ n₀ + m then
        Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0)‖ ≤
      3 * Real.pi * N / (q * τ) + 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set e : ℕ → ℂ := fun n => Complex.exp (((τ * Real.log n : ℝ) : ℂ) * Complex.I) with he
  rw [show (∑ m ∈ range (k + 1), (if q ∣ n₀ + m then
      Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0)) =
      ∑ m ∈ range (k + 1), (if q ∣ n₀ + m then e (n₀ + m) else 0) from rfl,
    sum_range_dvd_eq q n₀ k hq hn₀ e]
  obtain ⟨a, ha⟩ : ∃ a, a = (n₀ - 1) / q := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (n₀ + k) / q := ⟨_, rfl⟩
  rw [← ha, ← hb]
  rcases Nat.lt_or_ge a b with hab | hab
  · have hreidx : ∑ c ∈ Finset.Ioc a b, e (q * c) = ∑ j ∈ range (b - (a + 1) + 1),
        Complex.exp (((τ * Real.log q : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((τ * Real.log ((a + 1 : ℕ) + j) : ℝ) : ℂ) * Complex.I) := by
      rw [show Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
        show b + 1 - (a + 1) = b - (a + 1) + 1 by omega]
      refine sum_congr rfl fun j _ => ?_
      simp only [he]
      have hj0 : (0 : ℝ) < (a + 1 : ℕ) + j := by positivity
      rw [← Complex.exp_add]
      congr 1
      rw [show ((q * (a + 1 + j) : ℕ) : ℝ) = (q : ℝ) * ((a + 1 : ℕ) + j) by push_cast; ring,
        Real.log_mul hq0.ne' hj0.ne']
      push_cast
      ring
    rw [hreidx, ← mul_sum, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have ha1 : 1 ≤ a + 1 := by omega
    have hab' : (a + 1) + (b - (a + 1)) ≤ b := (Nat.add_sub_cancel' hab).le
    have hτa : τ ≤ Real.pi * (a + 1 : ℕ) := by
      refine hτn.trans ?_
      rw [div_le_iff₀ hq0]
      have : (n₀ : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * q := by
        have h1 : n₀ ≤ (a + 1) * q := by
          have := Nat.lt_div_mul_add (a := n₀ - 1) hq
          rw [ha, add_mul, one_mul]
          omega
        exact_mod_cast h1
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left this Real.pi_pos.le]
    have h := norm_partial_cpow_le ha1 hab' hτ hτa
    refine h.trans ?_
    have hbN : (b : ℝ) ≤ N / q := by
      rw [le_div_iff₀ hq0]
      have : b * q ≤ N := by rw [hb]; exact (Nat.div_mul_le_self _ _).trans hk
      exact_mod_cast this
    have : 3 * Real.pi * b / τ ≤ 3 * Real.pi * N / (q * τ) := by
      rw [div_le_div_iff₀ hτ (by positivity)]
      have := mul_le_mul_of_nonneg_left hbN (by positivity : (0 : ℝ) ≤ 3 * Real.pi * (q * τ))
      rw [show 3 * Real.pi * (q * τ) * (N / q) = 3 * Real.pi * N * τ by field_simp] at this
      nlinarith
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]; positivity

/-- **Kuzmin–Landau for the Ramanujan twist.** For `0 < τ ≤ π n₀/m` and `n₀ + k ≤ N`, the partial
sums of `c_m(n) n^{iτ}` over `[n₀, n₀ + k]` are at most `Σ_{de = m} (3πN/τ + e)`. -/
theorem norm_partial_ramTwist_cpow_le {m : ℕ} {n₀ N k : ℕ} (hn₀ : 1 ≤ n₀)
    (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / m) :
    ‖∑ j ∈ range (k + 1), (ramTwist m (n₀ + j) : ℂ) *
        Complex.exp (((τ * Real.log (n₀ + j) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ x ∈ m.divisorsAntidiagonal, (3 * Real.pi * N / τ + x.2) := by
  have hsplit : ∑ j ∈ range (k + 1), (ramTwist m (n₀ + j) : ℂ) *
      Complex.exp (((τ * Real.log (n₀ + j) : ℝ) : ℂ) * Complex.I) =
      ∑ x ∈ m.divisorsAntidiagonal, ((ArithmeticFunction.moebius x.1 : ℝ) * x.2 : ℂ) *
        ∑ j ∈ range (k + 1), (if x.2 ∣ n₀ + j then
          Complex.exp (((τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j _ => ?_
    simp only [ramTwist]
    push_cast
    rw [Finset.sum_mul]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [hsplit]
  refine (norm_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
  have he : 0 < x.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  have he0 : (0 : ℝ) < x.2 := by exact_mod_cast he
  have hem : (x.2 : ℝ) ≤ m := by
    exact_mod_cast Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  have hτe : τ ≤ Real.pi * n₀ / x.2 :=
    hτn.trans (div_le_div_of_nonneg_left (by positivity) he0 hem)
  have hb := norm_partial_dvd_cpow_le he hn₀ hk hτ hτe
  rw [norm_mul]
  have hμ : ‖((ArithmeticFunction.moebius x.1 : ℝ) * x.2 : ℂ)‖ ≤ x.2 := by
    rw [show ((ArithmeticFunction.moebius x.1 : ℝ) * x.2 : ℂ) =
      (((ArithmeticFunction.moebius x.1 : ℝ) * x.2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos he0]
    have : |(ArithmeticFunction.moebius x.1 : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith
  calc _ ≤ (x.2 : ℝ) * (3 * Real.pi * N / (x.2 * τ) + 1) :=
        mul_le_mul hμ hb (norm_nonneg _) he0.le
    _ = 3 * Real.pi * N / τ + x.2 := by field_simp

/-- The Kuzmin–Landau constant of the Ramanujan twist at frequency `τ`. -/
theorem sum_antidiagonal_KL (m : ℕ) (N τ : ℝ) :
    ∑ x ∈ m.divisorsAntidiagonal, (3 * Real.pi * N / τ + x.2) =
      (m.divisorsAntidiagonal.card : ℝ) * (3 * Real.pi * N / τ) +
        ∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ) := by
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]

/-- **The Ramanujan block below its first resonance**: for `0 < |τ| ≤ π N e^{−A}/m`,
`|D_x(τ)| ≤ (d 3πN/|τ| + σ)(L e^{3A/2} + B e^{A/2})/√N`, `d = #{de = m}`, `σ = Σ_{e|m} e`. -/
theorem norm_dirichletPoly_ram_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {m : ℕ}
    (hm : 0 < m) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < |τ|)
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / m) :
    ‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ≤
      ((m.divisorsAntidiagonal.card : ℝ) * (3 * Real.pi * N / |τ|) +
        ∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ)) *
        ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ t : ℝ, 0 < t → t ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / m →
      ‖dirichletPoly N (twistedWeights h (ramTwist m) N) t‖ ≤
        ((m.divisorsAntidiagonal.card : ℝ) * (3 * Real.pi * N / t) +
          ∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ)) *
          ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have h2 : n₀ ≤ N := windowStart_le hA
    have htn : t ≤ Real.pi * n₀ / m := by
      refine htN.trans (div_le_div_of_nonneg_right ?_ hm0.le)
      exact mul_le_mul_of_nonneg_left (le_windowStart A N) Real.pi_pos.le
    rw [dirichletPoly_twisted_eq_range hsupp hA _ hN]
    refine (norm_sum_mul_le_of_partial (fun j => horizonWeights h N (n₀ + j))
      (fun j => (ramTwist m (n₀ + j) : ℂ) * Complex.exp (((t * Real.log (n₀ + j) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := (m.divisorsAntidiagonal.card : ℝ) * (3 * Real.pi * N / t) +
          ∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ)) fun k hk => ?_).trans ?_
    · have := norm_partial_ramTwist_cpow_le h1 (show n₀ + k ≤ N by omega) ht htn (m := m)
      rw [sum_antidiagonal_KL] at this
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by positivity)
  rcases lt_or_gt_of_ne (abs_pos.mp hτ0) with hneg | hpos
  · have := key (-τ) (by linarith) (by rw [abs_of_neg hneg] at hτ; exact hτ)
    rw [norm_dirichletPoly_neg, ← abs_of_neg hneg] at this
    exact this
  · rw [abs_of_pos hpos] at hτ ⊢
    exact key τ hpos hτ

/-- Small frequencies of the Ramanujan block: for `|τ| ≤ √N`, `|D_x(τ)|²/N ≤ 4W²/N`,
`W = 2 S e^{2A}(L + B)`, `S = Σ_{j<m} |c_m(j)|`. -/
theorem ramLow_small_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {Lh : NNReal}
    (hLh : LipschitzWith Lh h) {m : ℕ} (hm : 1 < m) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ : |τ| ≤ Real.sqrt N) :
    ‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N ≤
      4 * (2 * (∑ j ∈ range m, |ramTwist m j|) * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) ^ 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : (0 : ℝ) ≤ Lh := Lh.2
  set S := ∑ j ∈ range m, |ramTwist m j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD := norm_sq_dirichletPoly_twisted_le hh hA hsupp hB hLh (meanZeroTwist_ramTwist hm) hN τ
  have hK : (Lh : ℝ) + (1 / 2 + |τ|) * Bh ≤ ((Lh : ℝ) + Bh) * (2 * Real.sqrt N) := by
    nlinarith [mul_le_mul_of_nonneg_right hτ hBh0]
  have h1 : 2 * S * (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A)) / N ≤
      2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N := by gcongr
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [div_le_div_iff_of_pos_right hN0]
  refine hD.trans ((mul_le_mul_of_nonneg_left h2 hN0.le).trans (le_of_eq ?_))
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  rw [show 2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N =
      (2 * S * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) * (2 * Real.sqrt N / N) by ring, mul_pow,
    div_pow, mul_pow 2 (Real.sqrt N), hsq]
  field_simp
  ring

/-- Frequencies beyond `√N` and below the first resonance:
`|D_x(τ)|²/N ≤ 18π² d² V²/τ² + 2σ² V²/N²`. -/
theorem ramLow_large_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {m : ℕ}
    (hm : 0 < m) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ} (hτ0 : 0 < |τ|)
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / m) :
    ‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N ≤
      18 * Real.pi ^ 2 * (m.divisorsAntidiagonal.card : ℝ) ^ 2 *
          (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / τ ^ 2 +
        2 * (∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ)) ^ 2 *
          (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  set d := (m.divisorsAntidiagonal.card : ℝ) with hd
  set σ := ∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ) with hσ
  have hD := norm_dirichletPoly_ram_le hsupp hA hB hL hm hN hτ0 hτ
  rw [← hV, ← hd, ← hσ] at hD
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hsq : (d * (3 * Real.pi * N / |τ|) + σ) ^ 2 ≤
      2 * (d * (3 * Real.pi * N / |τ|)) ^ 2 + 2 * σ ^ 2 := by
    nlinarith [sq_nonneg (d * (3 * Real.pi * N / |τ|) - σ)]
  have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  rw [div_le_iff₀ hN0]
  refine h2.trans ?_
  rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
  refine (mul_le_mul_of_nonneg_right hsq (by positivity)).trans (le_of_eq ?_)
  rw [hτ2]
  have : |τ| ≠ 0 := hτ0.ne'
  field_simp
  ring

/-- **The Ramanujan block is quiet below its first resonance**: the energy on
`|τ| ≤ N e^{−A}/m` is `O(N^{−1/2})`. -/
theorem exists_ramLow_energy_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 1 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log m))))
          ((N : ℝ) * Real.exp (-(A + Real.log m))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N := by
  have hm' : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (h 1 - h 0)]
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * (∑ j ∈ range m, |ramTwist m j|) * Real.exp (2 * A) *
      ((Lh : ℝ) + Bh) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  obtain ⟨a, ha⟩ : ∃ a, a = 18 * Real.pi ^ 2 * (m.divisorsAntidiagonal.card : ℝ) ^ 2 * V ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * (∑ x ∈ m.divisorsAntidiagonal, (x.2 : ℝ)) ^ 2 * V ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  refine ⟨Cφ * (8 * W ^ 2) + 2 * Real.pi * (Cφ * a) + 2 * (Cφ * b), by positivity,
    fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hNs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = (N : ℝ) * Real.exp (-(A + Real.log m)) := ⟨_, rfl⟩
  rw [← hT₀]
  have hT₀0 : 0 ≤ T₀ := by rw [hT₀]; positivity
  have hT₀N : T₀ ≤ N := by
    rw [hT₀]
    have : Real.exp (-(A + Real.log m)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ m by
        exact_mod_cast hm.le)])
    nlinarith
  have hT₀res : T₀ ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / m := by
    rw [hT₀, neg_add, Real.exp_add, Real.exp_neg (Real.log m), Real.exp_log hm0, le_div_iff₀ hm0]
    have : (N : ℝ) * (Real.exp (-A) * (m : ℝ)⁻¹) * m = N * Real.exp (-A) := by field_simp
    rw [this]
    nlinarith [Real.pi_gt_three, mul_nonneg hN0.le (Real.exp_pos (-A)).le]
  have hφb : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := fun τ => by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hb₁ : ∀ τ ∈ Set.Icc (-T₀) T₀, |τ| ≤ Real.sqrt N →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N) ≤ Cφ * (4 * W ^ 2 / N) :=
    fun τ _ hτ => by
      have := ramLow_small_le hh hA hsupp hB hLh hm hN hτ
      rw [← hW] at this
      exact mul_le_mul (hφb τ) this (by positivity) hCφ
  have hb₂ : ∀ τ ∈ Set.Icc (-T₀) T₀, Real.sqrt N ≤ |τ| →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N) ≤
        Cφ * a / τ ^ 2 + Cφ * (b / (N : ℝ) ^ 2) :=
    fun τ hτ hτs => by
      have hτ0 : 0 < |τ| := lt_of_lt_of_le hsN hτs
      have := ramLow_large_le hsupp hA hB hL hm' hN hτ0 ((abs_le.mpr hτ).trans hT₀res)
      rw [← hV, ← ha, ← hb] at this
      refine (mul_le_mul (hφb τ) this (by positivity) hCφ).trans (le_of_eq ?_)
      ring
  have hint : IntegrableOn (fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N)) (Set.Icc (-T₀) T₀) :=
    (integrable_energyW hφ hφsupp _ hc hN).integrableOn
  have hsplit := setIntegral_Icc_le_of_split hsN hT₀0 hint (by positivity) (by positivity)
    (by positivity) hb₁ hb₂
  refine hsplit.trans ?_
  have e1 : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) = Cφ * (8 * W ^ 2) / Real.sqrt N := by
    rw [eq_div_iff hsN.ne']
    have : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) * Real.sqrt N =
        Cφ * (8 * W ^ 2) * ((Real.sqrt N * Real.sqrt N) / N) := by ring
    rw [this, hNs, div_self hN0.ne', mul_one]
  have e2 : 2 * (Cφ * a) * (Real.pi / Real.sqrt N) = 2 * Real.pi * (Cφ * a) / Real.sqrt N := by
    ring
  have e3 : 2 * T₀ * (Cφ * (b / (N : ℝ) ^ 2)) ≤ 2 * (Cφ * b) / Real.sqrt N := by
    have hX : 0 ≤ 2 * (Cφ * b) := by positivity
    have h1 : 2 * T₀ * (Cφ * (b / (N : ℝ) ^ 2)) ≤ 2 * (Cφ * b) / N := by
      have : 2 * (Cφ * b) / N = 2 * N * (Cφ * (b / (N : ℝ) ^ 2)) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine h1.trans (div_le_div_of_nonneg_left hX hsN ?_)
    calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := le_mul_of_one_le_left hsN.le hsN1
      _ = N := hNs
  rw [e1, e2, add_div, add_div]
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
