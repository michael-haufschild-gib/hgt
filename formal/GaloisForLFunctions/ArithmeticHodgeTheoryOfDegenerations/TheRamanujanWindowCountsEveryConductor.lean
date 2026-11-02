import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAPeriodicTwist
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure

/-!
# The Ramanujan window counts every conductor

The window twisted by the Ramanujan sum `c_m(n) = Σ_{de = m} μ(d) e [e ∣ n]`, `m ≥ 2`, has
second-order term the conductor-`m` count of the first order.

* **Autocorrelation** (`sum_ramTwist_mul_add`, `autoCorr_ramTwist`): `m⁻¹ Σ_{r<m} c_m(r) c_m(r+s) =
  c_m(s)`. With `c_m(n) = Σ_{ζ primitive} ζ^n`, the double sum over primitive roots collapses on
  `ζξ = 1` by orthogonality of the `m`-th roots of unity.
* **Energy** (`abs_ramEnergy_sub_le`): by the energy law of periodic twists the block energy is
  `(2π/c) Σ_n y_n² Σ_δ c_m(δ) G(δ/a_n)`, and `Σ_δ c_m(δ) G(δ/a) = Σ_{de=m} μ(d) e Σ_j G(ej/a)` is a
  combination of Poisson sums on the lattices `eℤ` (`sum_offset_ramTwist_eq`); since `Σ μ(d) = 0`
  the zero modes cancel and `E_N = 2π Σ_{de = m} μ(d) 𝒜_N(c/e) + O(c/N)`.
* **Quiet region** (`exists_ramLow_energy_le`): below `N e^{−A}/m`, Kuzmin–Landau on each lattice
  `eℤ` (`norm_partial_dvd_cpow_le`) and twisted Riemann sums below `√N` leave `O(N^{−1/2})`.
* **Sharp form** (`ram_layer_sharp`): `c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²) Σ μ(d) 𝒜_N(c/e) → 0`.
* **Critical curve** (`ram_layer_criticalCurve_of_regularBulk`): along `c^{β+1}/log N → K`,
  `c⁻¹⟨W x, x⟩/∫g² → J_{β+1}(m) βJ/K ‖H‖²_{−(β+1)}`, since `(log N) 𝒜_N(c/e) → e^{β+1}βJ/K` and
  `Σ_{de=m} μ(d) e^{β+1} = J_{β+1}(m)`. For the tilted spline (`ram_layer_criticalCurve_exact`):
  `7 φ(m) J(m)/K ‖H‖²_{−8}` with `φ(m) J(m) = J(1) J₈(m) = J(1) φ(m) #ℙ⁷(ℤ/m)`.
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

/-- The aliasing of a Ramanujan window: `𝒜^{(m)}_N(c) = Σ_{de = m} μ(d) 𝒜_N(c/e)`. -/
def ramAlias (φ h : ℝ → ℝ) (m : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * horizonAlias φ h (c / x.2) N

/-- **The energy of a Ramanujan window**: for `m ≥ 2` and `1 ≤ c ≤ N/4`,
`E_N = 2π Σ_{de = m} μ(d) 𝒜_N(c/e) + O(c/N)`. -/
theorem abs_ramEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 1 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * ramAlias φ h m c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := periodicEnergy_le hφ hφsupp hh hA hsupp (M := m) (by omega)
    (ramTwist_add_self m)
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * ramAlias φ h m c N := by
    unfold ramAlias
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

/-- **The second-order term of the Ramanujan window.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ (1 + |u|)^{−q}`, `q > 4`, a `C²` window profile `h` on `[−A, 0]`, the Ramanujan twist
`c_m`, `m ≥ 2`, and every schedule with `c_N ≥ 1`, `c_N → ∞`, `c_N (log N)²/N → 0`:
`c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²) Σ_{de = m} μ(d) 𝒜_N(c/e) → 0`. There is no Weil term. -/
theorem ram_layer_sharp (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) {m : ℕ} (hm : 1 < m) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramTwist m) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / (∫ u, φ u ^ 2) * ramAlias φ h m (c N) N) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hm' : 0 < m := by omega
  have hlogp : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm.le)
  obtain ⟨S', hS'⟩ : ∃ S', S' = ∑ j ∈ range m, |ramTwist m j| := ⟨_, rfl⟩
  obtain ⟨Cp, hCp0, hCp⟩ := exists_abs_twistedPole_le hφ hφsupp hφ2 hh hA hsupp
    (meanZeroTwist_ramTwist hm)
  obtain ⟨KE, hKE0, hKE⟩ := abs_ramEnergy_sub_le hφ hφsupp hh hA hsupp hm
  obtain ⟨CL, hCL0, hCL⟩ := exists_ramLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay
    hh hA hsupp hm
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * (A + 1))).le
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set M := ∫ u, φ u ^ 2 with hM
  set A' := A + Real.log m with hA'
  set x : ℕ → ℕ → ℝ := fun N => twistedWeights h (ramTwist m) N with hx
  set T₀ : ℕ → ℝ := fun N => (N : ℝ) * Real.exp (-A') with hT₀
  set S : ℕ → ℝ → ℝ := fun N => symbolW φ (x N) (c N) N (Real.exp (2 * (A + 1))) with hS
  set E : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (x N) τ‖ ^ 2 / N) with hE
  set P : ℕ → ℝ := fun N =>
    (paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (ramTwist m) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (ramTwist m) N) (c N) N))) (Complex.I / 2) +
    paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (ramTwist m) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (ramTwist m) N) (c N) N))) (-Complex.I / 2)).re /
        (c N * (c N / N * M)) with hP
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (S N τ - Real.log N / (2 * Real.pi) * E N τ) with hRm
  set Lo : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), S N τ with hLo
  set LoE : ℕ → ℝ := fun N => Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ with hLoE
  set Df : ℕ → ℝ := fun N => Real.log N * ((∫ τ, E N τ) - 2 * Real.pi * ramAlias φ h m (c N) N)
    with hDf
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hevA := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A'))
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  have hevT := hT.eventually (eventually_ge_atTop 2)
  -- the pole terms
  have hPt : Tendsto P atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => Cp / (N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    rw [Real.norm_eq_abs]
    exact hCp N hN (c N) (hc0 N) (by linarith [hc0 N])
  -- the quiet region
  have hEnn : ∀ N τ, 0 ≤ E N τ := fun N τ => by simp only [hE]; positivity
  have hLoEt : Tendsto LoE atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * (Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      simpa using tendsto_log_div_sqrt.const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hI := hCL N hN (c N) (hc0 N)
    have hI0 : 0 ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ :=
      setIntegral_nonneg measurableSet_Icc fun τ _ => hEnn N τ
    simp only [hLoE]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hI0]
    calc Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ ≤ Real.log N * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hI hlog0
      _ = CL * (Real.log N / Real.sqrt N) := by ring
  have hLot : Tendsto Lo atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * ((Aν + Real.log 3) / Real.sqrt N +
        Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (Aν + Real.log 3) / Real.sqrt N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using (h1.add tendsto_log_div_sqrt).const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have hT₀N : T₀ N ≤ N := by
      simp only [hT₀, hA']
      have : Real.exp (-(A + Real.log m)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    have hWl : 0 ≤ Aν + Real.log (2 + N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N by linarith); linarith
    have hpt : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤ (Aν + Real.log (2 + N)) * E N τ :=
      fun τ hτ => by
        have hτN : |τ| ≤ N := (abs_le.mpr hτ).trans hT₀N
        have hν' : |nuSymbol (Real.exp (2 * (A + 1))) τ| ≤ Aν + Real.log (2 + N) :=
          (hν τ).trans (by
            have := Real.log_le_log (by positivity : (0 : ℝ) < 2 + |τ|) (by linarith :
              2 + |τ| ≤ 2 + N)
            linarith)
        show |symbolW φ (twistedWeights h (ramTwist m) N) (c N) N (Real.exp (2 * (A + 1))) τ| ≤ _
        rw [symbolW, abs_mul, abs_of_nonneg (by positivity), mul_comm]
        exact mul_le_mul_of_nonneg_right hν' (by positivity)
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp _ (hc0 N) hN _
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp _ (hc0 N) hN
    have h1 : ‖Lo N‖ ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| := by
      simp only [hLo]
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    have h2 : ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤
        ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Aν + Real.log (2 + N)) * E N τ :=
      setIntegral_mono_on hSi.abs.integrableOn (hEi.const_mul _).integrableOn measurableSet_Icc hpt
    rw [integral_const_mul] at h2
    have hI := hCL N hN (c N) (hc0 N)
    have hlog3 : Real.log (2 + N) ≤ Real.log 3 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    refine h1.trans (h2.trans ?_)
    calc (Aν + Real.log (2 + N)) * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ
        ≤ (Aν + Real.log (2 + N)) * (CL / Real.sqrt N) := mul_le_mul_of_nonneg_left hI hWl
      _ ≤ (Aν + Real.log 3 + Real.log N) * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = CL * ((Aν + Real.log 3) / Real.sqrt N + Real.log N / Real.sqrt N) := by ring
  -- the remainder above the cut
  have hRmt : Tendsto Rm atTop (𝓝 0) := by
    set VV := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A' + 1 with hVV
    have hcp : Tendsto (fun N : ℕ => c N ^ q) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hcinf
    have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ q A' (S' * Bh) * VV / c N ^ q)) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := aliasConst Cφ q A' (S' * Bh) * VV)).div_atTop hcp
      simpa using this.const_mul 2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hevA, hevT, eventually_ge_atTop 1] with N h1 h2 hN
    rw [Real.norm_eq_abs]
    have hsq : ∀ n, x N n ^ 2 ≤ S' ^ 2 * horizonWeights h N n ^ 2 := fun n => by
      simp only [hx, twistedWeights, mul_pow]
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hb := abs_periodic_le hm' (ramTwist_add_self m) n
      rw [← hS'] at hb
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hS1 : ∑ n ∈ Icc 1 N, x N n ^ 2 ≤ (S' * Bh) ^ 2 * Real.exp A' := by
      refine (sum_le_sum fun n _ => hsq n).trans ?_
      rw [← mul_sum, mul_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((sum_horizonWeights_sq_le hsupp hB hN).trans ?_)
        (by positivity)
      gcongr
      linarith
    have hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x N n ^ 2 ≤ N * (S' * Bh) ^ 2 := by
      refine (sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hsq n) (Nat.cast_nonneg n)).trans ?_
      have := sum_mul_horizonWeights_sq_le hB N (h := h)
      calc ∑ n ∈ Icc 1 N, (n : ℝ) * (S' ^ 2 * horizonWeights h N n ^ 2)
          = S' ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        _ ≤ S' ^ 2 * (N * Bh ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = N * (S' * Bh) ^ 2 := by ring
    exact abs_remainderW_le hφ hφsupp (by linarith : 1 < q) hCφ hdecay hC0 hC (2 * (A + 1))
      (by linarith) h1 hS1 hS2 h2 (hc0 N)
  -- the energy defect
  have hDft : Tendsto Df atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℕ => Real.log N * (c N / N)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hclog
      · have := hc1 N
        have := Real.log_natCast_nonneg N
        positivity
      · filter_upwards [hev3] with N hN
        have hc0' : 0 ≤ c N / N := by have := hc1 N; positivity
        calc Real.log N * (c N / N) ≤ Real.log N * Real.log N * (c N / N) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hN) hc0'
          _ = c N * Real.log N ^ 2 / N := by ring
    have hlim := t1.const_mul KE
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Real.norm_eq_abs]
    simp only [hDf]
    rw [abs_mul, abs_of_nonneg hlog0]
    have := hKE (c N) (hc1 N) N h4
    calc Real.log N * |(∫ τ, E N τ) - 2 * Real.pi * ramAlias φ h m (c N) N|
        ≤ Real.log N * (KE * c N / N) := mul_le_mul_of_nonneg_left this hlog0
      _ = KE * (Real.log N * (c N / N)) := by ring
  -- the identity
  have hid : ∀ᶠ N : ℕ in atTop, P N + M⁻¹ * Lo N + M⁻¹ * Rm N - M⁻¹ * (2 * Real.pi)⁻¹ * LoE N +
      M⁻¹ * (2 * Real.pi)⁻¹ * Df N =
      (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramTwist m) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / M * ramAlias φ h m (c N) N := by
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hcle : c N ≤ N := by linarith [hc0 N]
    rw [atomForm_eq hφ hφsupp hφ2 (twistedWeights_eq_zero hsupp (ramTwist m) N) hA (hc0 N) hN hcle,
      ← hM]
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp (x N) (hc0 N) hN (2 * (A + 1))
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp (x N) (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSi).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEi
    have hcompl : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, S N τ = Rm N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, E N τ := by
      simp only [hRm]
      rw [integral_sub hSi.integrableOn (hEi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    have hSeq : (∫ τ, symbolW φ (twistedWeights h (ramTwist m) N) (c N) N
        (Real.exp (2 * (A + 1))) τ) = ∫ τ, S N τ := rfl
    rw [hSeq, hsplitS, hcompl]
    simp only [hP, hLo, hLoE, hDf]
    rw [← hsplitE]
    have hpi' : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
    linear_combination (-(M⁻¹ * Real.log N * ramAlias φ h m (c N) N)) * hpi'
  refine Tendsto.congr' hid ?_
  have := (((hPt.add (hLot.const_mul M⁻¹)).add (hRmt.const_mul M⁻¹)).sub
    (hLoEt.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))).add (hDft.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))
  simpa using this

/-! ### The Ramanujan window at the critical curve -/

/-- `Σ_{de = m} μ(d) e^k = J_k(m)`. -/
theorem sum_antidiagonal_moebius_rpow (k : ℝ) (m : ℕ) :
    ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (x.2 : ℝ) ^ k =
      ArithmeticDegenerationTheory.jordanTotient k m := by
  rw [ArithmeticDegenerationTheory.jordanTotient,
    ← Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ) ^ k)]

/-- The aliasing at the overlap `c/e` along the critical curve:
`(log N/∫φ²) 𝒜_N(c/e) → e^{β+1} βJ/K ∫ e^{−βy} h²`. -/
theorem tendsto_log_mul_horizonAlias_div (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) {e : ℕ} (he : 0 < e) :
    Tendsto (fun N : ℕ => Real.log N / (∫ u, φ u ^ 2) * horizonAlias φ h (c N / e) N) atTop
      (𝓝 (K⁻¹ * ((e : ℝ) ^ (β + 1) * (J * (β * ∫ y, Real.exp (-(β * y)) * h y ^ 2))))) := by
  obtain ⟨hcinf, -, hcN⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  rw [show β + 1 + 1 = β + 2 by ring] at hcN
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  set c' : ℕ → ℝ := fun N => max (c N / e) 1 with hc'
  have hc'1 : ∀ N, 1 ≤ c' N := fun N => le_max_right _ _
  have hc'le : ∀ N, c' N ≤ c N := fun N =>
    max_le (div_le_self (by linarith [hc1 N]) he1) (hc1 N)
  have hc'inf : Tendsto c' atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_left _ _) (hcinf.atTop_div_const he0)
  have hc'N : Tendsto (fun N : ℕ => c' N ^ (β + 2) / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc'1 N; positivity) (fun N => ?_) hcN
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith [hc'1 N]) (hc'le N)
      (by linarith)) (Nat.cast_nonneg _)
  have h2 := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hbulk
    hh hA hsupp hc'1 hc'inf hc'N
  have hev : ∀ᶠ N : ℕ in atTop, c' N = c N / e := by
    filter_upwards [hcinf.eventually (eventually_ge_atTop (e : ℝ))] with N hN
    exact max_eq_left (by rw [le_div_iff₀ he0, one_mul]; exact hN)
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (β + 1)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  refine (hinv.mul (h2.const_mul ((e : ℝ) ^ (β + 1)))).congr' ?_
  filter_upwards [hev] with N hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hcp : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos hc0 _
  have hsplit : (e : ℝ) ^ (β + 1) * (c N / e) ^ (β + 1) = c N ^ (β + 1) := by
    rw [Real.div_rpow hc0.le he0.le, mul_div_cancel₀ _ (by positivity)]
  simp only [hN]
  rw [← hsplit]
  field_simp

/-- **The Ramanujan window at the critical curve.** For every profile whose bulk energy has the
rescaled limit `s^β E₁(s) → J`, along `c^{β+1}/log N → K`, the window twisted by the Ramanujan sum
`c_m`, `m ≥ 2`, has `c⁻¹⟨W x, x⟩/∫g² → J_{β+1}(m) βJ/K ∫ e^{−(β+1)y} H²`: the Jordan totient of
conductor `m`. -/
theorem ram_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) {m : ℕ} (hm : 1 < m) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramTwist m) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsharp := ram_layer_sharp hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp hc1 hcinf hclog hm
  set M := ∫ u, φ u ^ 2 with hM
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  have hterm : Tendsto (fun N : ℕ => Real.log N / M * ramAlias φ h m (c N) N) atTop
      (𝓝 (∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
        (K⁻¹ * ((x.2 : ℝ) ^ (β + 1) * (J * (β * I)))))) := by
    have hsum := tendsto_finsetSum m.divisorsAntidiagonal fun x hx =>
      (tendsto_log_mul_horizonAlias_div hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK
        hcrit (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))).const_mul
          (ArithmeticFunction.moebius x.1 : ℝ)
    refine hsum.congr fun N => ?_
    unfold ramAlias
    rw [Finset.mul_sum]
    exact sum_congr rfl fun x _ => by ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
      (K⁻¹ * ((x.2 : ℝ) ^ (β + 1) * (J * (β * I)))) =
      ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K * I := by
    rw [← sum_antidiagonal_moebius_rpow, Finset.sum_mul, Finset.sum_mul, Finset.sum_div,
      Finset.sum_mul]
    exact sum_congr rfl fun x _ => by field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

/-- **The Ramanujan window counts the conductor.** For the tilted spline and every `m ≥ 2`, along
`c⁸/log N → K`, the window twisted by `c_m` has
`c⁻¹⟨W x, x⟩/∫g² → (7 φ(m) J(m)/K) ∫ e^{−8y} H²`, with `φ(m) J(m) = J(1) J₈(m)`: the
second-order term of the conductor-`m` window is the first-order count of conductor `m`,
`J(1) φ(m) #ℙ⁷(ℤ/m)`. -/
theorem ram_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) {m : ℕ}
    (hm : 1 < m) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramTwist m) N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * ((m.totient : ℝ) * ArithmeticDegenerationTheory.jordanCoefficient m) / K *
        ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := ram_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hK hcrit' hm
  have hint : ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight h y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
    congr 1; funext y; norm_num
  have h8 : ((7 : ℝ) + 1) = 8 := by norm_num
  rw [hint, h8] at hlim
  rw [totient_mul_jordanCoefficient (by omega : 0 < m)]
  convert hlim using 2
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
