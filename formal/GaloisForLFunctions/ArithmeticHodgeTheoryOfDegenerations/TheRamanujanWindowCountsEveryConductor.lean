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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
