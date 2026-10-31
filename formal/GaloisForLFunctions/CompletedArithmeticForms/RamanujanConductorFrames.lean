import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates
import GaloisForLFunctions.ArithmeticElectrostatics.TheSelfIntersectionOfATorsionOrbit
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Whole-prefix Riesz frames and exact Gram locality for Ramanujan conductors

Below the square-root conductor horizon `M^2 ≤ N`, the normalized Ramanujan horizon vectors
`v_m = normalizedRamanujanHorizonVector m N` (`1 ≤ m ≤ M`) form a two-sided Riesz sequence
with lower constant `1 - 2θ` (`M ≤ N^θ`, `0 < θ < 1/2`) and absolute upper constant `6`:

* **Exact finite-horizon Gram law (`normalizedRamanujanHorizonVector_gram_exact`).** For `m * l ≤ N`,
  Kluyver's divisor expansion reduces `<v_m, v_l>` to the torsion-orbit intersection `orbitIntersection m l`
  plus a rank-factorized floor-harmonic remainder of size `O(f(m) f(l) / (N log N))`. The `1 / log N`
  off-diagonal matrix is nonzero only along prime-power divisibility steps `l = m p^k` or `m = l p^k`.
* **Uniform upper Riesz frame and Bessel inequality (`ramanujanConductor_upper_riesz`,
  `sum_inner_normalizedRamanujanHorizonVector_sq_le`).** Weighted Schur testing with `w_m = m^{-1/2}`
  on the prime-power off-diagonal and a prime-subset mean-square bound on the floor remainder yield
  `‖∑_{m=1}^M a_m v_m‖^2 ≤ 6 ∑_{m=1}^M a_m^2` for `M^2 ≤ N` and `4 e^7 ≤ log N`, with no logarithmic loss.
* **Lower Riesz frame and exact dimension (`ramanujanConductor_lower_riesz`, `finrank_conductorSubspace_eq`).**
  The large-sieve lower bound gives `(1 - 2θ) ∑_{m=1}^M a_m^2 ≤ ‖∑_{m=1}^M a_m v_m‖^2`, linear independence,
  and `finrank ℝ (conductorSubspace M N) = M`.
* **Divisor-totient packet envelope (`sum_normalizedRamanujanMode_sq_le`).** Hölder's totient quotient
  formula and divisor-count convolution bound `∑_{m=1}^M c̃_m(n)^2 ≤ n (1 + log M)^4` for every `n ≥ 1`.
-/

noncomputable section

open Finset Filter Topology
open scoped BigOperators RealInnerProductSpace ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.CompletedArithmeticForms

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory ArithmeticEffectivityTheory
  ArithmeticElectrostatics ArithmeticIntersectionTheory SignedArithmeticHodgeTheory

/-! ### Conductor subspace and lower Riesz frame -/

/-- The indexed family of normalized Ramanujan conductor modes on `Icc 1 M`. -/
def conductorBasisFamily (M N : ℕ) (m : ↥(Icc 1 M)) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  normalizedRamanujanHorizonVector m.1 N

/-- The `M`-conductor subspace spanned by `normalizedRamanujanHorizonVector m N` for `1 ≤ m ≤ M`. -/
def conductorSubspace (M N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
  Submodule.span ℝ (Set.range (conductorBasisFamily M N))

/-- Bilinear expansion of the squared norm of a conductor combination. -/
theorem norm_sum_normalizedRamanujanHorizonVector_sq_eq_gram (S : Finset ℕ) (N : ℕ) (a : ℕ → ℝ) :
    ‖∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      ∑ m ∈ S, ∑ l ∈ S, a m * a l *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine sum_congr rfl fun m _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- Norm-square identity connecting Euclidean combinations of `v_m` to pole-profile sums. -/
theorem norm_sum_normalizedRamanujanHorizonVector_sq (S : Finset ℕ) (N : ℕ) (a : ℕ → ℝ) :
    ‖∑ m ∈ S, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, (∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2) / Real.log N := by
  have hrew : (∑ m ∈ S, ∑ l ∈ S, a m * a l *
      ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) =
      (∑ m ∈ S, ∑ l ∈ S, a m * a l *
        ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) / Real.log N := by
    rw [sum_div]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun l _ => ?_
    rw [normalizedRamanujanHorizonVector_inner]
    ring
  rw [norm_sum_normalizedRamanujanHorizonVector_sq_eq_gram, hrew]
  congr 1
  calc
    (∑ m ∈ S, ∑ l ∈ S, a m * a l * ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) =
        ∑ m ∈ S, ∑ n ∈ Icc 1 N, ∑ l ∈ S, a m * a l * (ramanujanPoleProfile m n * ramanujanPoleProfile l n) := by
      refine sum_congr rfl fun m _ => ?_
      calc
        (∑ l ∈ S, a m * a l * ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) =
            ∑ l ∈ S, ∑ n ∈ Icc 1 N, a m * a l * (ramanujanPoleProfile m n * ramanujanPoleProfile l n) :=
          sum_congr rfl fun l _ => mul_sum _ _ _
        _ = ∑ n ∈ Icc 1 N, ∑ l ∈ S, a m * a l * (ramanujanPoleProfile m n * ramanujanPoleProfile l n) :=
          sum_comm
    _ = ∑ n ∈ Icc 1 N, ∑ m ∈ S, ∑ l ∈ S, (a m * ramanujanPoleProfile m n) * (a l * ramanujanPoleProfile l n) := by
      rw [sum_comm]
      exact sum_congr rfl fun n _ => sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring
    _ = ∑ n ∈ Icc 1 N, (∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2 := by
      refine sum_congr rfl fun n _ => ?_
      rw [sq, sum_mul]
      exact sum_congr rfl fun m _ => (mul_sum _ _ _).symm

/-- Lower Riesz frame bound on `Icc 1 M` below the square-root horizon. -/
theorem ramanujanConductor_lower_riesz_log {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N) (a : ℕ → ℝ) :
    (1 - 2 * Real.log M / Real.log N) * (∑ m ∈ Icc 1 M, a m ^ 2) ≤
      ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hlog_le : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlow := ramanujanPoleProfile_family_squareRoot_lower hM a N
  rw [norm_sum_normalizedRamanujanHorizonVector_sq, le_div_iff₀ hL]
  have h1 : (1 - 2 * Real.log M / Real.log N) * (∑ m ∈ Icc 1 M, a m ^ 2) * Real.log N =
      (Real.log N - 2 * Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    field_simp [hL.ne']
  rw [h1]
  exact (mul_le_mul_of_nonneg_right (by linarith only [hlog_le])
    (sum_nonneg fun _ _ => sq_nonneg _)).trans hlow

/-- Lower Riesz frame bound at level of distribution `M ≤ N^θ` (`0 < θ < 1/2`), valid for all `M ≥ 1`. -/
theorem ramanujanConductor_lower_riesz {θ : ℝ} {M N : ℕ} (hM1 : 1 ≤ M) (hN : 4 ≤ N)
    (hMN : (M : ℝ) ≤ (N : ℝ) ^ θ) (a : ℕ → ℝ) :
    (1 - 2 * θ) * (∑ m ∈ Icc 1 M, a m ^ 2) ≤
      ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hL : 0 < Real.log N := Real.log_pos hN1
  by_cases hM2 : 2 ≤ M
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlogM : Real.log M ≤ θ * Real.log N := by
      have h := Real.log_le_log hM0 hMN
      rwa [Real.log_rpow hN0] at h
    have hdiv : 2 * Real.log M / Real.log N ≤ 2 * θ := by
      rw [div_le_iff₀ hL]
      linarith only [hlogM]
    exact (mul_le_mul_of_nonneg_right (by linarith only [hdiv])
      (sum_nonneg fun _ _ => sq_nonneg _)).trans
        (ramanujanConductor_lower_riesz_log hM2 (by omega) a)
  · have hMeq : M = 1 := by omega
    subst hMeq
    simp only [Icc_self, sum_singleton]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hθ0 : 0 ≤ θ := by
      by_contra hneg
      have hrp : (N : ℝ) ^ θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (lt_of_not_ge hneg)
      have h1le : (1 : ℝ) ≤ (N : ℝ) ^ θ := by simpa using hMN
      linarith
    have hv1 : 1 ≤ ‖normalizedRamanujanHorizonVector 1 N‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, normalizedRamanujanHorizonVector_inner, le_div_iff₀ hL, one_mul]
      have hprof : ∀ n ∈ Icc 1 N, ramanujanPoleProfile 1 n * ramanujanPoleProfile 1 n = ((n : ℝ))⁻¹ := by
        intro n hn
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient zero_lt_one]
        simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one,
          ramanujanLagCoefficient_of_dvd (one_dvd n)]
        rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt hn0, one_div]
      rw [sum_congr rfl hprof, show Icc 1 N = Ioc 0 N from rfl, ← HTGeometry.harmonic_eq_sum_Ioc]
      have he := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
      rw [Real.eulerMascheroniSeq', if_neg (by omega : N ≠ 0)] at he
      have hγ := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
      simp [Real.eulerMascheroniSeq] at hγ
      linarith
    calc
      (1 - 2 * θ) * a 1 ^ 2 ≤ 1 * a 1 ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = a 1 ^ 2 * 1 := by ring
      _ ≤ a 1 ^ 2 * ‖normalizedRamanujanHorizonVector 1 N‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hv1 (sq_nonneg _)

/-- Linear independence of `conductorBasisFamily M N` whenever `2 * log M < log N`. -/
theorem linearIndependent_conductorBasisFamily {M N : ℕ} (hN : 2 ≤ N)
    (hMN : 2 * Real.log M < Real.log N) :
    LinearIndependent ℝ (conductorBasisFamily M N) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let a : ℕ → ℝ := fun m => if hm : m ∈ Icc 1 M then g ⟨m, hm⟩ else 0
  have hsum : (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) = 0 := by
    rw [← hg, Finset.univ_eq_attach,
      ← Finset.sum_attach (Icc 1 M) (fun m => a m • normalizedRamanujanHorizonVector m N)]
    refine sum_congr rfl fun m _ => ?_
    simp only [a, dif_pos m.2, conductorBasisFamily]
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos hN1
  by_cases hM2 : 2 ≤ M
  · have hpos : 0 < 1 - 2 * Real.log M / Real.log N := by
      rw [sub_pos, div_lt_one hL]
      exact hMN
    have hriesz := ramanujanConductor_lower_riesz_log hM2 hN a
    rw [hsum, norm_zero, zero_pow (by decide)] at hriesz
    have hsq0 : (∑ m ∈ Icc 1 M, a m ^ 2) = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hriesz hpos) (sum_nonneg fun _ _ => sq_nonneg _)
    intro m
    have hm0 := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp hsq0 m.1 m.2
    have ha0 : a m.1 = 0 := sq_eq_zero_iff.mp hm0
    dsimp only [a] at ha0
    rwa [dif_pos m.2] at ha0
  · intro m
    have hM1 : M = 1 := by
      have := (mem_Icc.mp m.2).1
      have := (mem_Icc.mp m.2).2
      omega
    subst hM1
    have hm_eq : ∀ x : ↥(Icc 1 1), x = m := fun x => Subtype.ext (by
      have := (mem_Icc.mp x.2).1
      have := (mem_Icc.mp x.2).2
      have := (mem_Icc.mp m.2).1
      have := (mem_Icc.mp m.2).2
      omega)
    have huniv : (Finset.univ : Finset ↥(Icc 1 1)) = {m} := by
      ext x
      simp [hm_eq x]
    rw [huniv, sum_singleton] at hg
    have hm1_val : m.1 = 1 := by
      have := (mem_Icc.mp m.2).1
      have := (mem_Icc.mp m.2).2
      omega
    rw [conductorBasisFamily, hm1_val] at hg
    have hv0 : normalizedRamanujanHorizonVector 1 N ≠ 0 := by
      intro hz
      have hn0 : ‖normalizedRamanujanHorizonVector 1 N‖ ^ 2 = 0 := by simp [hz]
      rw [← real_inner_self_eq_norm_sq, normalizedRamanujanHorizonVector_inner,
        div_eq_zero_iff] at hn0
      rcases hn0 with h0 | hL0
      · have h1mem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
        have h1pos : 0 < ramanujanPoleProfile 1 1 * ramanujanPoleProfile 1 1 := by
          rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient zero_lt_one]
          simp [ramanujanLagCoefficient_of_dvd]
        have hge := single_le_sum (fun n _ => mul_self_nonneg (ramanujanPoleProfile 1 n)) h1mem
        linarith
      · exact hL.ne' hL0
    exact (smul_eq_zero.mp hg).resolve_right hv0

/-- Exact dimension `finrank ℝ (conductorSubspace M N) = M` below the square-root horizon. -/
theorem finrank_conductorSubspace_eq {M N : ℕ} (hN : 2 ≤ N)
    (hMN : 2 * Real.log M < Real.log N) :
    Module.finrank ℝ (conductorSubspace M N) = M := by
  unfold conductorSubspace
  rw [finrank_span_eq_card (linearIndependent_conductorBasisFamily hN hMN), Fintype.card_coe,
    Nat.card_Icc]
  omega

/-- Representation of elements of `conductorSubspace M N` as linear combinations over `Icc 1 M`. -/
theorem mem_conductorSubspace_iff {M N : ℕ} {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} :
    x ∈ conductorSubspace M N ↔
      ∃ a : ℕ → ℝ, (∀ m, m ∉ Icc 1 M → a m = 0) ∧
        x = ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N := by
  unfold conductorSubspace
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun m => if hm : m ∈ Icc 1 M then c ⟨m, hm⟩ else 0, fun m hm => dif_neg hm, ?_⟩
    rw [← Finset.sum_coe_sort (Icc 1 M)]
    refine sum_congr rfl fun m _ => ?_
    simp [m.2, conductorBasisFamily]
  · rintro ⟨a, _, rfl⟩
    refine ⟨fun m => a m.1, ?_⟩
    rw [← Finset.sum_coe_sort (Icc 1 M)]
    rfl

/-! ### Exact finite-horizon Gram law via torsion-orbit intersections -/

/-- Floor-harmonic remainder `H_{⌊N/L⌋} - (log N + γ - log L)`. -/
def harmonicFloorError (N L : ℕ) : ℝ :=
  (harmonic (N / L) : ℝ) - (Real.log N + Real.eulerMascheroniConstant - Real.log L)

/-- For `1 ≤ L ≤ N`, the floor-harmonic remainder is bounded by `4 L / N`. -/
theorem abs_harmonicFloorError_le {N L : ℕ} (hL : 1 ≤ L) (hLN : L ≤ N) :
    |harmonicFloorError N L| ≤ 4 * (L : ℝ) / N := by
  let q := N / L
  have hq1 : 1 ≤ q := Nat.div_pos hLN hL
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hL.trans hLN)
  have hh := HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hq1
  have hr := roundoff_le (Nat.pos_of_ne_zero (by omega : L ≠ 0)) hLN
  have hid : harmonicFloorError N L =
      ((harmonic q : ℝ) - Real.log q - Real.eulerMascheroniConstant) -
        (Real.log N - Real.log (q : ℝ) - Real.log L) := by
    unfold harmonicFloorError
    dsimp only [q]
    ring
  have h2q : |harmonicFloorError N L| ≤ 2 / (q : ℝ) := by
    rw [hid]
    have hr' : |Real.log N - Real.log (q : ℝ) - Real.log L| ≤ 1 / (q : ℝ) := by
      rw [abs_of_nonneg hr.1]
      exact hr.2
    exact (abs_sub _ _).trans ((add_le_add hh hr').trans_eq (by ring))
  have hNlt : N < (q + 1) * L := by
    dsimp only [q]
    have hmod := Nat.mod_lt N (by omega : 0 < L)
    have hdiv := Nat.mod_add_div N L
    nlinarith only [hmod, hdiv]
  have hNle : (N : ℝ) ≤ 2 * (q : ℝ) * L := by
    have hnat : N ≤ 2 * q * L := by nlinarith only [hNlt, hq1]
    exact_mod_cast hnat
  refine h2q.trans ?_
  rw [div_le_div_iff₀ hq0 hN0]
  nlinarith only [hNle]

/-- Harmonic sum of `1 / n` over multiples of `L` in `Icc 1 N`. -/
private theorem sum_Icc_dvd_inv_eq_harmonic (N : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (∑ n ∈ Icc 1 N, if L ∣ n then 1 / (n : ℝ) else 0) =
      (1 / (L : ℝ)) * (harmonic (N / L) : ℝ) := by
  have hL0 : 0 < L := hL
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  rw [← sum_filter]
  have hbij : (∑ n ∈ (Icc 1 N).filter (L ∣ ·), 1 / (n : ℝ)) =
      ∑ k ∈ Icc 1 (N / L), 1 / ((L * k : ℕ) : ℝ) := by
    refine sum_nbij' (fun n => n / L) (fun k => L * k) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnI, hdvd⟩ := mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hL0, Nat.div_le_div_right hnN⟩
    · intro k hk
      obtain ⟨hk1, hkQ⟩ := mem_Icc.mp hk
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right L k⟩
      · exact Nat.mul_pos hL0 hk1
      · exact (Nat.mul_le_mul_left L hkQ).trans (Nat.mul_div_le N L)
    · intro n hn
      exact Nat.mul_div_cancel' (mem_filter.mp hn).2
    · intro k _
      exact Nat.mul_div_cancel_left k hL0
    · intro n hn
      rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]
  rw [hbij, show Icc 1 (N / L) = Ioc 0 (N / L) from rfl, HTGeometry.harmonic_eq_sum_Ioc, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  field_simp [hLR]

/-- Double Möbius transform of `gcd` evaluates to `δ_{m, l} φ(m)`. -/
private theorem doubleMoebius_gcd_eq {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ)) =
      if m = l then (m.totient : ℝ) else 0 := by
  rw [doubleMoebius_swap]
  have hinner : ∀ d ∈ m.divisors,
      (∑ e ∈ l.divisors, (μ (l / e) : ℝ) * (Nat.gcd d e : ℝ)) =
        if l ∣ d then (l.totient : ℝ) else 0 :=
    fun d _ => sum_moebius_mul_gcd d hl
  rw [sum_congr rfl fun d hd => by rw [hinner d hd], sum_moebius_ite_dvd hm]
  by_cases hlm : l ∣ m
  · rw [if_pos hlm, ← sum_mul]
    obtain ⟨k, rfl⟩ := hlm
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [Nat.mul_div_cancel_left k hl, sum_divisors_moebius hk]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have hne : l * k ≠ l := fun h => hk1 (Nat.eq_of_mul_eq_mul_left hl (h.trans (mul_one l).symm))
      rw [if_neg hk1, if_neg hne, zero_mul]
  · have hne : m ≠ l := fun h => hlm (h ▸ dvd_rfl)
    rw [if_neg hlm, if_neg hne]

/-- Double Möbius transform of `gcd(d, e) * log lcm(d, e)` is `orbitIntersection m l`. -/
private theorem doubleMoebius_gcd_log_lcm_eq {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * Real.log (Nat.lcm d e)) =
      orbitIntersection m l := by
  rw [orbitIntersection_eq_doubleMoebius hm hl]
  exact doubleMoebius_congr fun d hd e he =>
    (logEnergy_eq (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)).symm

/-- Raw finite-horizon Gram identity for unnormalized Kluyver coefficients (`m * l ≤ N`). -/
theorem sum_ramanujanLagCoefficient_mul_div_eq {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (_hml : m * l ≤ N) :
    (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) =
      (if m = l then (m.totient : ℝ) * (Real.log N + Real.eulerMascheroniConstant) else 0) -
        orbitIntersection m l +
        doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * harmonicFloorError N (Nat.lcm d e)) := by
  have expand_n (n : ℕ) :
      ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ) =
        ∑ e ∈ l.divisors, (μ (l / e) : ℝ) * ∑ d ∈ m.divisors, (μ (m / d) : ℝ) *
          (if Nat.lcm d e ∣ n then (d : ℝ) * e / (n : ℝ) else 0) := by
    rw [ramanujanLagCoefficient, ramanujanLagCoefficient, sum_mul]
    simp only [moebiusReal, mul_sum, sum_div]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => sum_congr rfl fun d _ => ?_
    by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n
    · have hlcm : Nat.lcm d e ∣ n := Nat.lcm_dvd hdn hen
      simp only [if_pos hdn, if_pos hen, if_pos hlcm]
      ring
    · have hlcm : ¬ Nat.lcm d e ∣ n := fun h => hen ((Nat.dvd_lcm_right d e).trans h)
      simp [if_pos hdn, if_neg hen, if_neg hlcm]
    · have hlcm : ¬ Nat.lcm d e ∣ n := fun h => hdn ((Nat.dvd_lcm_left d e).trans h)
      simp [if_neg hdn, if_neg hlcm]
    · have hlcm : ¬ Nat.lcm d e ∣ n := fun h => hdn ((Nat.dvd_lcm_left d e).trans h)
      simp [if_neg hdn, if_neg hen, if_neg hlcm]
  have hswap :
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) =
        doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * (harmonic (N / Nat.lcm d e) : ℝ)) := by
    simp_rw [expand_n]
    rw [sum_comm]
    unfold doubleMoebius
    refine sum_congr rfl fun e he => ?_
    rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun d hd => ?_
    rw [← mul_sum]
    congr 1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hL : 1 ≤ Nat.lcm d e := Nat.lcm_pos hd0 he0
    have hLR : (Nat.lcm d e : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hd0 he0).ne'
    have hprod : (d : ℝ) * e = (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) := by
      exact_mod_cast (Nat.gcd_mul_lcm d e).symm
    have hterm (n : ℕ) :
        (if Nat.lcm d e ∣ n then (d : ℝ) * e / (n : ℝ) else 0) =
          ((d : ℝ) * e) * (if Nat.lcm d e ∣ n then 1 / (n : ℝ) else 0) := by
      split_ifs <;> ring
    simp_rw [hterm, ← mul_sum, sum_Icc_dvd_inv_eq_harmonic N hL, hprod]
    field_simp [hLR]
  rw [hswap]
  have hsplit : doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * (harmonic (N / Nat.lcm d e) : ℝ)) =
      doubleMoebius m l (fun d e =>
        (Nat.gcd d e : ℝ) * (Real.log N + Real.eulerMascheroniConstant) +
          (Nat.gcd d e : ℝ) * harmonicFloorError N (Nat.lcm d e) -
          (Nat.gcd d e : ℝ) * Real.log (Nat.lcm d e)) := by
    refine doubleMoebius_congr fun d _ e _ => ?_
    unfold harmonicFloorError
    ring
  rw [hsplit, doubleMoebius_add_sub]
  have hconst : doubleMoebius m l
      (fun d e => (Nat.gcd d e : ℝ) * (Real.log N + Real.eulerMascheroniConstant)) =
        if m = l then (m.totient : ℝ) * (Real.log N + Real.eulerMascheroniConstant) else 0 := by
    have hfactor : doubleMoebius m l
        (fun d e => (Nat.gcd d e : ℝ) * (Real.log N + Real.eulerMascheroniConstant)) =
          doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ)) *
            (Real.log N + Real.eulerMascheroniConstant) := by
      unfold doubleMoebius
      rw [sum_mul]
      refine sum_congr rfl fun e _ => ?_
      rw [mul_assoc]
      congr 1
      rw [sum_mul]
      exact sum_congr rfl fun d _ => (mul_assoc _ _ _).symm
    rw [hfactor, doubleMoebius_gcd_eq hm hl]
    split_ifs <;> ring
  rw [hconst, doubleMoebius_gcd_log_lcm_eq hm hl]
  ring

/-- The normalized floor-harmonic remainder in `<v_m, v_l>`. -/
def conductorGramFloorError (m l N : ℕ) : ℝ :=
  doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * harmonicFloorError N (Nat.lcm d e)) /
    (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ) * Real.log N)

/-- Exact finite-horizon Gram formula for `normalizedRamanujanHorizonVector`: the `1 / log N`
off-diagonal coupling is `-orbitIntersection m l / (√(φ(m) φ(l)) log N)`, supported purely on
prime-power divisibility steps `l ∣ m` or `m ∣ l`. -/
theorem normalizedRamanujanHorizonVector_gram_exact {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hml : m * l ≤ N) (hL : 0 < Real.log N) :
    ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ =
      (if m = l then
        1 + (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N
      else
        -(if l ∣ m then Real.sqrt ((l.totient : ℝ) / m.totient) * Λ (m / l)
          else if m ∣ l then Real.sqrt ((m.totient : ℝ) / l.totient) * Λ (l / m)
          else 0) / Real.log N) +
      conductorGramFloorError m l N := by
  have hφm : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφl : 0 < (l.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hl
  have hsm : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφm).ne'
  have hsl : Real.sqrt (l.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφl).ne'
  have hpole : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) =
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient m n * ramanujanLagCoefficient l n / (n : ℝ)) /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
    rw [sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [ramanujanPoleProfile, ramanujanPoleProfile,
      normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hl]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp [hsm, hsl]
    rw [Real.sq_sqrt hn0]
  rw [normalizedRamanujanHorizonVector_inner, hpole, div_div,
    sum_ramanujanLagCoefficient_mul_div_eq hm hl hml]
  unfold conductorGramFloorError
  by_cases heq : m = l
  · subst heq
    rw [if_pos rfl, if_pos rfl, orbitIntersection_self_eq hm,
      localCorrection_eq_totient_mul_tameDifferent]
    have hss : Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ) = (m.totient : ℝ) :=
      Real.mul_self_sqrt hφm.le
    rw [hss]
    field_simp [hφm.ne', hL.ne']
    ring
  · rw [if_neg heq, if_neg heq, orbitIntersection_eq hm hl heq]
    by_cases hlm : l ∣ m
    · rw [if_pos hlm, if_pos hlm, Real.sqrt_div hφl.le]
      field_simp [hsm, hsl, hL.ne']
      rw [Real.sq_sqrt hφl.le]
      ring
    · rw [if_neg hlm, if_neg hlm]
      by_cases hml' : m ∣ l
      · rw [if_pos hml', if_pos hml', Real.sqrt_div hφm.le]
        field_simp [hsm, hsl, hL.ne']
        rw [Real.sq_sqrt hφm.le]
        ring
      · rw [if_neg hml', if_neg hml']
        ring

/-! ### Diagonal, prime-power Schur, and floor-remainder operator bounds -/

/-- `tameDifferent m ≤ log m` for every positive conductor `m`. -/
theorem tameDifferent_le_log {m : ℕ} (hm : 0 < m) : tameDifferent m ≤ Real.log m := by
  have hprimes : ∀ p ∈ m.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hterm : ∀ p ∈ m.primeFactors, Real.log p / ((p : ℝ) - 1) ≤ Real.log p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprimes p hp).two_le
    exact div_le_self (Real.log_nonneg (by linarith)) (by linarith)
  have hpos : 0 < ∏ p ∈ m.primeFactors, p := prod_pos fun p hp => (hprimes p hp).pos
  have hle : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  unfold tameDifferent
  calc
    (∑ p ∈ m.primeFactors, Real.log p / ((p : ℝ) - 1)) ≤ ∑ p ∈ m.primeFactors, Real.log p :=
      sum_le_sum hterm
    _ = Real.log ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod fun p hp => by exact_mod_cast (hprimes p hp).ne_zero]
    _ ≤ Real.log m := Real.log_le_log (by exact_mod_cast hpos) hle

/-- Prime-power totient lower step: `φ(l) * p^(k-1) * (p - 1) ≤ φ(l * p^k)`. -/
private theorem totient_mul_prime_pow_ge (l : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    l.totient * p ^ (k - 1) * (p - 1) ≤ (l * p ^ k).totient := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  simp only [Nat.add_sub_cancel]
  induction j with
  | zero =>
    simp only [pow_zero, mul_one, zero_add, pow_one]
    by_cases hpl : p ∣ l
    · rw [mul_comm l p, Nat.totient_mul_of_prime_of_dvd hp hpl, mul_comm p l.totient]
      exact Nat.mul_le_mul_left _ (Nat.sub_le p 1)
    · have hcop : l.Coprime p := (hp.coprime_iff_not_dvd.mpr hpl).symm
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
  | succ j ih =>
    have hdvd : p ∣ l * p ^ (j + 1) := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) l
    rw [show l * p ^ (j + 1 + 1) = p * (l * p ^ (j + 1)) by rw [pow_succ]; ring,
      Nat.totient_mul_of_prime_of_dvd hp hdvd]
    calc
      l.totient * p ^ (j + 1) * (p - 1) = p * (l.totient * p ^ j * (p - 1)) := by
        rw [pow_succ]; ring
      _ ≤ p * (l * p ^ (j + 1)).totient := Nat.mul_le_mul_left p (ih (Nat.succ_pos j))

/-- Elementary Chebyshev bound `∑_{t=1}^M Λ(t)/t ≤ 2 log M` without analytic inputs. -/
private theorem sum_Icc_vonMangoldt_div_le (M : ℕ) :
    (∑ t ∈ Icc 1 M, (Λ t : ℝ) / t) ≤ 2 * Real.log M := by
  rcases lt_or_ge M 2 with hM | hM2
  · interval_cases M <;> simp
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hterm : ∀ t ∈ Icc 1 M, (Λ t : ℝ) / t ≤ (2 / (M : ℝ)) * (((M / t : ℕ) : ℝ) * Λ t) := by
    intro t ht
    obtain ⟨ht1, htM⟩ := mem_Icc.mp ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have hq1 : 1 ≤ M / t := Nat.div_pos htM ht1
    have hMlt : M < (M / t + 1) * t := by
      have hmod := Nat.mod_lt M ht1
      have hdiv := Nat.mod_add_div M t
      nlinarith only [hmod, hdiv]
    have hMle : (M : ℝ) ≤ 2 * ((M / t : ℕ) : ℝ) * t := by
      have hnat : M ≤ 2 * (M / t) * t := by nlinarith only [hMlt, hq1]
      exact_mod_cast hnat
    have hinv : 1 / (t : ℝ) ≤ (2 / (M : ℝ)) * ((M / t : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ ht0 hM0]
      linarith only [hMle]
    calc
      (Λ t : ℝ) / t = (1 / (t : ℝ)) * Λ t := by ring
      _ ≤ ((2 / (M : ℝ)) * ((M / t : ℕ) : ℝ)) * Λ t :=
        mul_le_mul_of_nonneg_right hinv ArithmeticFunction.vonMangoldt_nonneg
      _ = (2 / (M : ℝ)) * (((M / t : ℕ) : ℝ) * Λ t) := by ring
  have hcheb : (∑ t ∈ Icc 1 M, ((M / t : ℕ) : ℝ) * Λ t) = ∑ j ∈ Icc 1 M, Real.log j := by
    have hrew : ∀ j ∈ Icc 1 M, Real.log j = ∑ t ∈ Icc 1 M, if t ∣ j then (Λ t : ℝ) else 0 := by
      intro j hj
      obtain ⟨hj1, hjM⟩ := mem_Icc.mp hj
      rw [← ArithmeticFunction.vonMangoldt_sum, ← sum_filter]
      refine sum_subset (fun t ht => ?_) (fun t ht hnot => ?_)
      · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ht,
          (Nat.le_of_dvd hj1 (Nat.dvd_of_mem_divisors ht)).trans hjM⟩,
          Nat.dvd_of_mem_divisors ht⟩
      · obtain ⟨_, htdvd⟩ := mem_filter.mp ht
        exact False.elim (hnot (Nat.mem_divisors.mpr ⟨htdvd, by omega⟩))
    rw [sum_congr rfl hrew, sum_comm]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨ht1, _⟩ := mem_Icc.mp ht
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    have hcard : ((Icc 1 M).filter (t ∣ ·)).card = (Icc 1 (M / t)).card := by
      refine Finset.card_bij (fun j _ => j / t) ?_ ?_ ?_
      · intro j hj
        obtain ⟨hjI, hdvd⟩ := mem_filter.mp hj
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hjI).1 hdvd) ht1,
          Nat.div_le_div_right (mem_Icc.mp hjI).2⟩
      · intro j₁ hj₁ j₂ hj₂ heq
        rw [← Nat.mul_div_cancel' (mem_filter.mp hj₁).2,
          ← Nat.mul_div_cancel' (mem_filter.mp hj₂).2, heq]
      · intro k hk
        obtain ⟨hk1, hkQ⟩ := mem_Icc.mp hk
        exact ⟨t * k, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos ht1 hk1,
          (Nat.mul_le_mul_left t hkQ).trans (Nat.mul_div_le M t)⟩, dvd_mul_right t k⟩,
          Nat.mul_div_cancel_left k ht1⟩
    rw [hcard, Nat.card_Icc, Nat.add_sub_cancel]
  calc
    (∑ t ∈ Icc 1 M, (Λ t : ℝ) / t) ≤ ∑ t ∈ Icc 1 M, (2 / (M : ℝ)) * (((M / t : ℕ) : ℝ) * Λ t) :=
      sum_le_sum hterm
    _ = (2 / (M : ℝ)) * ∑ j ∈ Icc 1 M, Real.log j := by rw [← mul_sum, hcheb]
    _ ≤ (2 / (M : ℝ)) * ∑ _j ∈ Icc 1 M, Real.log M := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun j hj => ?_) (by positivity)
      exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hj).1) (by exact_mod_cast (mem_Icc.mp hj).2)
    _ = 2 * Real.log M := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      field_simp [hM0.ne']

/-- The off-diagonal prime-power kernel `K(m, l)` appearing at scale `1 / log N`. -/
private def conductorOffDiagKernel (m l : ℕ) : ℝ :=
  if m = l then 0
  else if l ∣ m then Real.sqrt ((l.totient : ℝ) / m.totient) * Λ (m / l)
  else if m ∣ l then Real.sqrt ((m.totient : ℝ) / l.totient) * Λ (l / m)
  else 0

private theorem conductorOffDiagKernel_nonneg (m l : ℕ) : 0 ≤ conductorOffDiagKernel m l := by
  unfold conductorOffDiagKernel
  split_ifs <;> positivity

private theorem conductorOffDiagKernel_symm {m l : ℕ} (_hm : 0 < m) (_hl : 0 < l) :
    conductorOffDiagKernel m l = conductorOffDiagKernel l m := by
  unfold conductorOffDiagKernel
  by_cases hml : m = l
  · subst hml; simp
  · rw [if_neg hml, if_neg (Ne.symm hml)]
    by_cases hlm : l ∣ m
    · have hnot : ¬ m ∣ l := fun h => hml (Nat.dvd_antisymm h hlm)
      rw [if_pos hlm, if_neg hnot, if_pos hlm]
    · rw [if_neg hlm]
      by_cases hml' : m ∣ l
      · rw [if_pos hml', if_pos hml']
      · simp [hlm, hml']

/-- Weighted row sum of `conductorOffDiagKernel` with weight `w_l = 1 / √l`. -/
private theorem conductorOffDiagKernel_weighted_row_le {M m : ℕ} (hm : m ∈ Icc 1 M) :
    Real.sqrt m * (∑ l ∈ Icc 1 M, conductorOffDiagKernel m l / Real.sqrt l) ≤
      3 * Real.sqrt 2 * Real.log M := by
  obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hdown_pt : ∀ l ∈ Icc 1 M, l ≠ m → l ∣ m →
      Real.sqrt m * (Real.sqrt ((l.totient : ℝ) / m.totient) * Λ (m / l) / Real.sqrt l) ≤
        Real.sqrt 2 * Λ (m / l) := by
    intro l hl hne hlm
    by_cases hΛ : Λ (m / l) = 0
    · simp [hΛ]
    obtain ⟨hl1, _⟩ := mem_Icc.mp hl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    obtain ⟨p, k, hp, hk0, hpk⟩ :=
      (isPrimePow_nat_iff (m / l)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hm_eq : m = l * p ^ k := by rw [hpk, Nat.mul_div_cancel' hlm]
    have htot := totient_mul_prime_pow_ge l hp hk0
    rw [← hm_eq] at htot
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpk0 : (0 : ℝ) < (p : ℝ) ^ (k - 1) := pow_pos (by linarith) _
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hrat : (m : ℝ) * l.totient / (l * m.totient) ≤ 2 := by
      rw [div_le_iff₀ (mul_pos hl0 hφm)]
      have htotR : (l.totient : ℝ) * (p : ℝ) ^ (k - 1) * ((p : ℝ) - 1) ≤ m.totient := by
        have hcast : ((l.totient * p ^ (k - 1) * (p - 1) : ℕ) : ℝ) ≤ m.totient := by
          exact_mod_cast htot
        rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at hcast
      have hmR : (m : ℝ) = (l : ℝ) * ((p : ℝ) ^ (k - 1) * p) := by
        rw [hm_eq, Nat.cast_mul, Nat.cast_pow]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk0).symm⟩
        simp [pow_succ]
      have hp_le : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
      calc
        (m : ℝ) * l.totient = (l : ℝ) * (l.totient : ℝ) * (p : ℝ) ^ (k - 1) * p := by
          rw [hmR]; ring
        _ ≤ (l : ℝ) * (l.totient : ℝ) * (p : ℝ) ^ (k - 1) * (2 * ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hp_le (by positivity)
        _ = 2 * (l : ℝ) * ((l.totient : ℝ) * (p : ℝ) ^ (k - 1) * ((p : ℝ) - 1)) := by ring
        _ ≤ 2 * (l : ℝ) * m.totient := mul_le_mul_of_nonneg_left htotR (by positivity)
        _ = 2 * ((l : ℝ) * m.totient) := by ring
    have hsq : Real.sqrt m * (Real.sqrt ((l.totient : ℝ) / m.totient) / Real.sqrt l) ≤ Real.sqrt 2 := by
      have hlhs : Real.sqrt m * (Real.sqrt ((l.totient : ℝ) / m.totient) / Real.sqrt l) =
          Real.sqrt ((m : ℝ) * l.totient / (l * m.totient)) := by
        rw [← Real.sqrt_div (by positivity : 0 ≤ (l.totient : ℝ) / m.totient),
          ← Real.sqrt_mul hm0.le]
        congr 1
        field_simp [hl0.ne', hφm.ne']
      rw [hlhs]
      exact Real.sqrt_le_sqrt hrat
    calc
      Real.sqrt m * (Real.sqrt ((l.totient : ℝ) / m.totient) * Λ (m / l) / Real.sqrt l) =
          (Real.sqrt m * (Real.sqrt ((l.totient : ℝ) / m.totient) / Real.sqrt l)) * Λ (m / l) := by ring
      _ ≤ Real.sqrt 2 * Λ (m / l) :=
        mul_le_mul_of_nonneg_right hsq ArithmeticFunction.vonMangoldt_nonneg
  have hup_pt : ∀ l ∈ Icc 1 M, l ≠ m → m ∣ l →
      Real.sqrt m * (Real.sqrt ((m.totient : ℝ) / l.totient) * Λ (l / m) / Real.sqrt l) ≤
        Real.sqrt 2 * (Λ (l / m) / ((l / m : ℕ) : ℝ)) := by
    intro l hl hne hml
    by_cases hΛ : Λ (l / m) = 0
    · simp [hΛ]
    obtain ⟨hl1, _⟩ := mem_Icc.mp hl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    obtain ⟨p, k, hp, hk0, hpk⟩ :=
      (isPrimePow_nat_iff (l / m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hl_eq : l = m * p ^ k := by rw [hpk, Nat.mul_div_cancel' hml]
    have htot := totient_mul_prime_pow_ge m hp hk0
    rw [← hl_eq] at htot
    have hφl : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpk_pos : (0 : ℝ) < ((l / m : ℕ) : ℝ) := by
      rw [← hpk]; exact_mod_cast pow_pos hp.pos k
    have hrat : (m : ℝ) * m.totient / (l * l.totient) ≤ 2 / ((l / m : ℕ) : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hl0 hφl) (sq_pos_of_pos hpk_pos)]
      have htotR : (m.totient : ℝ) * (p : ℝ) ^ (k - 1) * ((p : ℝ) - 1) ≤ l.totient := by
        have hcast : ((m.totient * p ^ (k - 1) * (p - 1) : ℕ) : ℝ) ≤ l.totient := by
          exact_mod_cast htot
        rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at hcast
      have hlR : (l : ℝ) = (m : ℝ) * ((l / m : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hml).symm
      have hquotR : ((l / m : ℕ) : ℝ) = (p : ℝ) ^ (k - 1) * p := by
        rw [← hpk, Nat.cast_pow]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk0).symm⟩
        simp [pow_succ]
      have hp_le : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
      calc
        (m : ℝ) * m.totient * ((l / m : ℕ) : ℝ) ^ 2 =
            (m : ℝ) * ((l / m : ℕ) : ℝ) * ((m.totient : ℝ) * (p : ℝ) ^ (k - 1) * p) := by
          rw [hquotR]; ring
        _ ≤ (m : ℝ) * ((l / m : ℕ) : ℝ) * ((m.totient : ℝ) * (p : ℝ) ^ (k - 1) * (2 * ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp_le (by positivity)) (by positivity)
        _ = 2 * ((m : ℝ) * ((l / m : ℕ) : ℝ)) * ((m.totient : ℝ) * (p : ℝ) ^ (k - 1) * ((p : ℝ) - 1)) := by ring
        _ ≤ 2 * ((m : ℝ) * ((l / m : ℕ) : ℝ)) * l.totient :=
          mul_le_mul_of_nonneg_left htotR (by positivity)
        _ = 2 * ((l : ℝ) * l.totient) := by rw [← hlR]; ring
    have hsq : Real.sqrt m * (Real.sqrt ((m.totient : ℝ) / l.totient) / Real.sqrt l) ≤
        Real.sqrt 2 / ((l / m : ℕ) : ℝ) := by
      have hlhs : Real.sqrt m * (Real.sqrt ((m.totient : ℝ) / l.totient) / Real.sqrt l) =
          Real.sqrt ((m : ℝ) * m.totient / (l * l.totient)) := by
        rw [← Real.sqrt_div (by positivity : 0 ≤ (m.totient : ℝ) / l.totient),
          ← Real.sqrt_mul hm0.le]
        congr 1
        field_simp [hl0.ne', hφl.ne']
      rw [hlhs, ← Real.sqrt_sq hpk_pos.le, ← Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt hrat
    calc
      Real.sqrt m * (Real.sqrt ((m.totient : ℝ) / l.totient) * Λ (l / m) / Real.sqrt l) =
          (Real.sqrt m * (Real.sqrt ((m.totient : ℝ) / l.totient) / Real.sqrt l)) * Λ (l / m) := by ring
      _ ≤ (Real.sqrt 2 / ((l / m : ℕ) : ℝ)) * Λ (l / m) :=
        mul_le_mul_of_nonneg_right hsq ArithmeticFunction.vonMangoldt_nonneg
      _ = Real.sqrt 2 * (Λ (l / m) / ((l / m : ℕ) : ℝ)) := by ring
  rw [mul_sum]
  have hpoint : ∀ l ∈ Icc 1 M,
      Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l) ≤
        (if l ∣ m then Real.sqrt 2 * Λ (m / l) else 0) +
          (if m ∣ l then Real.sqrt 2 * (Λ (l / m) / ((l / m : ℕ) : ℝ)) else 0) := by
    intro l hl
    unfold conductorOffDiagKernel
    by_cases heq : m = l
    · subst heq
      rw [if_pos rfl, zero_div, mul_zero]
      split_ifs <;> positivity
    · rw [if_neg heq]
      by_cases hlm : l ∣ m
      · have hnot : ¬ m ∣ l := fun h => heq (Nat.dvd_antisymm h hlm)
        rw [if_pos hlm, if_pos hlm, if_neg hnot, add_zero]
        exact hdown_pt l hl (Ne.symm heq) hlm
      · rw [if_neg hlm, if_neg hlm, zero_add]
        by_cases hml : m ∣ l
        · rw [if_pos hml, if_pos hml]
          exact hup_pt l hl (Ne.symm heq) hml
        · rw [if_neg hml, if_neg hml, zero_div, mul_zero]
  have hsum_down :
      (∑ l ∈ Icc 1 M, if l ∣ m then Real.sqrt 2 * (Λ (m / l) : ℝ) else 0) ≤
        Real.sqrt 2 * Real.log M := by
    rw [← sum_filter]
    have hsub : (Icc 1 M).filter (· ∣ m) ⊆ m.divisors :=
      fun l hl => Nat.mem_divisors.mpr ⟨(mem_filter.mp hl).2, by omega⟩
    calc
      (∑ l ∈ (Icc 1 M).filter (· ∣ m), Real.sqrt 2 * (Λ (m / l) : ℝ)) ≤
          ∑ l ∈ m.divisors, Real.sqrt 2 * (Λ (m / l) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = Real.sqrt 2 * ∑ d ∈ m.divisors, (Λ d : ℝ) := by
        rw [← mul_sum, Nat.sum_div_divisors m (fun d => (Λ d : ℝ))]
      _ = Real.sqrt 2 * Real.log m := by rw [ArithmeticFunction.vonMangoldt_sum]
      _ ≤ Real.sqrt 2 * Real.log M :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hm0 (by exact_mod_cast hmM)) (by positivity)
  have hsum_up :
      (∑ l ∈ Icc 1 M, if m ∣ l then Real.sqrt 2 * ((Λ (l / m) : ℝ) / ((l / m : ℕ) : ℝ)) else 0) ≤
        2 * Real.sqrt 2 * Real.log M := by
    rw [← sum_filter]
    have hinj : ∀ l₁ ∈ (Icc 1 M).filter (m ∣ ·), ∀ l₂ ∈ (Icc 1 M).filter (m ∣ ·),
        l₁ / m = l₂ / m → l₁ = l₂ := by
      intro l₁ hl₁ l₂ hl₂ heq
      rw [← Nat.mul_div_cancel' (mem_filter.mp hl₁).2,
        ← Nat.mul_div_cancel' (mem_filter.mp hl₂).2, heq]
    have hmaps : ((Icc 1 M).filter (m ∣ ·)).image (· / m) ⊆ Icc 1 M := by
      intro t ht
      obtain ⟨l, hl, rfl⟩ := mem_image.mp ht
      obtain ⟨hlI, hml⟩ := mem_filter.mp hl
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hlI).1 hml) hm1,
        (Nat.div_le_self l m).trans (mem_Icc.mp hlI).2⟩
    calc
      (∑ l ∈ (Icc 1 M).filter (m ∣ ·), Real.sqrt 2 * ((Λ (l / m) : ℝ) / ((l / m : ℕ) : ℝ))) =
          ∑ t ∈ ((Icc 1 M).filter (m ∣ ·)).image (· / m), Real.sqrt 2 * ((Λ t : ℝ) / t) := by
        rw [sum_image hinj]
      _ ≤ ∑ t ∈ Icc 1 M, Real.sqrt 2 * ((Λ t : ℝ) / t) :=
        sum_le_sum_of_subset_of_nonneg hmaps fun _ _ _ => by positivity
      _ = Real.sqrt 2 * ∑ t ∈ Icc 1 M, (Λ t : ℝ) / t := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt 2 * (2 * Real.log M) :=
        mul_le_mul_of_nonneg_left (sum_Icc_vonMangoldt_div_le M) (by positivity)
      _ = 2 * Real.sqrt 2 * Real.log M := by ring
  calc
    (∑ l ∈ Icc 1 M, Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l)) ≤
        (∑ l ∈ Icc 1 M, if l ∣ m then Real.sqrt 2 * (Λ (m / l) : ℝ) else 0) +
          ∑ l ∈ Icc 1 M, if m ∣ l then Real.sqrt 2 * ((Λ (l / m) : ℝ) / ((l / m : ℕ) : ℝ)) else 0 := by
      rw [← sum_add_distrib]
      exact sum_le_sum hpoint
    _ ≤ Real.sqrt 2 * Real.log M + 2 * Real.sqrt 2 * Real.log M := add_le_add hsum_down hsum_up
    _ = 3 * Real.sqrt 2 * Real.log M := by ring

/-- Weighted Schur bound on the prime-power off-diagonal quadratic form. -/
private theorem abs_sum_conductorOffDiagKernel_le {M : ℕ} (a : ℕ → ℝ) :
    |∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l| ≤
      3 * Real.sqrt 2 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 := by
  have hpoint : ∀ m ∈ Icc 1 M, ∀ l ∈ Icc 1 M,
      |a m * a l * conductorOffDiagKernel m l| ≤
        (1 / 2) * (a m ^ 2 * (Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l)) +
          a l ^ 2 * (Real.sqrt l * (conductorOffDiagKernel l m / Real.sqrt m))) := by
    intro m hm l hl
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (mem_Icc.mp hl).1
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    have hsl : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl0
    have hK0 : 0 ≤ conductorOffDiagKernel m l := conductorOffDiagKernel_nonneg m l
    have hsym := conductorOffDiagKernel_symm (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
    rw [abs_mul, abs_mul, abs_of_nonneg hK0, ← hsym]
    have hsq := sq_nonneg (|a m| * Real.sqrt (Real.sqrt m / Real.sqrt l) -
      |a l| * Real.sqrt (Real.sqrt l / Real.sqrt m))
    have hprod : Real.sqrt (Real.sqrt m / Real.sqrt l) * Real.sqrt (Real.sqrt l / Real.sqrt m) = 1 := by
      rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (Real.sqrt m),
        div_self (mul_pos hsl hsm).ne', Real.sqrt_one]
    have h1 : Real.sqrt (Real.sqrt m / Real.sqrt l) ^ 2 = Real.sqrt m / Real.sqrt l :=
      Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (Real.sqrt l / Real.sqrt m) ^ 2 = Real.sqrt l / Real.sqrt m :=
      Real.sq_sqrt (by positivity)
    have hab : 2 * (|a m| * |a l|) ≤
        a m ^ 2 * (Real.sqrt m / Real.sqrt l) + a l ^ 2 * (Real.sqrt l / Real.sqrt m) := by
      have hexp : (|a m| * Real.sqrt (Real.sqrt m / Real.sqrt l) -
          |a l| * Real.sqrt (Real.sqrt l / Real.sqrt m)) ^ 2 =
        a m ^ 2 * (Real.sqrt m / Real.sqrt l) + a l ^ 2 * (Real.sqrt l / Real.sqrt m) -
          2 * (|a m| * |a l| *
            (Real.sqrt (Real.sqrt m / Real.sqrt l) * Real.sqrt (Real.sqrt l / Real.sqrt m))) := by
        calc
          _ = |a m| ^ 2 * Real.sqrt (Real.sqrt m / Real.sqrt l) ^ 2 +
                |a l| ^ 2 * Real.sqrt (Real.sqrt l / Real.sqrt m) ^ 2 -
                2 * (|a m| * |a l| *
                  (Real.sqrt (Real.sqrt m / Real.sqrt l) * Real.sqrt (Real.sqrt l / Real.sqrt m))) := by
            ring
          _ = _ := by rw [sq_abs, sq_abs, h1, h2]
      rw [hexp, hprod, mul_one] at hsq
      linarith only [hsq]
    have hmul := mul_le_mul_of_nonneg_right hab hK0
    calc
      |a m| * |a l| * conductorOffDiagKernel m l =
          (1 / 2) * ((2 * (|a m| * |a l|)) * conductorOffDiagKernel m l) := by ring
      _ ≤ (1 / 2) * ((a m ^ 2 * (Real.sqrt m / Real.sqrt l) +
            a l ^ 2 * (Real.sqrt l / Real.sqrt m)) * conductorOffDiagKernel m l) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by ring
  calc
    |∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l| ≤
        ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, |a m * a l * conductorOffDiagKernel m l| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M,
          (1 / 2) * (a m ^ 2 * (Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l)) +
            a l ^ 2 * (Real.sqrt l * (conductorOffDiagKernel l m / Real.sqrt m))) :=
      sum_le_sum fun m hm => sum_le_sum fun l hl => hpoint m hm l hl
    _ = ∑ m ∈ Icc 1 M, a m ^ 2 *
          (Real.sqrt m * ∑ l ∈ Icc 1 M, conductorOffDiagKernel m l / Real.sqrt l) := by
      simp only [mul_add, sum_add_distrib, ← mul_sum]
      have hswap : (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M,
          a l ^ 2 * (Real.sqrt l * (conductorOffDiagKernel l m / Real.sqrt m))) =
        ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M,
          a m ^ 2 * (Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l)) := sum_comm
      rw [hswap]
      have hfactor : (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M,
          a m ^ 2 * (Real.sqrt m * (conductorOffDiagKernel m l / Real.sqrt l))) =
        ∑ m ∈ Icc 1 M, a m ^ 2 *
          (Real.sqrt m * ∑ l ∈ Icc 1 M, conductorOffDiagKernel m l / Real.sqrt l) := by
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum, mul_sum]
      rw [hfactor]
      ring
    _ ≤ ∑ m ∈ Icc 1 M, a m ^ 2 * (3 * Real.sqrt 2 * Real.log M) :=
      sum_le_sum fun m hm =>
        mul_le_mul_of_nonneg_left (conductorOffDiagKernel_weighted_row_le hm) (sq_nonneg _)
    _ = 3 * Real.sqrt 2 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 := by rw [← sum_mul]; ring

/-- Divisor-amplitude factor bounding the floor-harmonic remainder. -/
private def floorAmplitude (m : ℕ) : ℝ :=
  (∑ d ∈ m.divisors, |(μ (m / d) : ℝ)| * (d : ℝ)) / Real.sqrt (m.totient : ℝ)

private theorem floorAmplitude_nonneg (m : ℕ) : 0 ≤ floorAmplitude m :=
  div_nonneg (sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)

/-- Entrywise rank-1 majorant on `conductorGramFloorError`. -/
private theorem abs_conductorGramFloorError_le {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hml : m * l ≤ N) (hL : 0 < Real.log N) :
    |conductorGramFloorError m l N| ≤
      4 / ((N : ℝ) * Real.log N) * (floorAmplitude m * floorAmplitude l) := by
  have hN1 : 1 ≤ N := (Nat.mul_pos hm hl).trans_le hml
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hinner : |doubleMoebius m l (fun d e => (Nat.gcd d e : ℝ) * harmonicFloorError N (Nat.lcm d e))| ≤
      (4 / (N : ℝ)) * (∑ d ∈ m.divisors, |(μ (m / d) : ℝ)| * (d : ℝ)) *
        (∑ e ∈ l.divisors, |(μ (l / e) : ℝ)| * (e : ℝ)) := by
    unfold doubleMoebius
    calc
      |∑ e ∈ l.divisors, (μ (l / e) : ℝ) *
          ∑ d ∈ m.divisors, (μ (m / d) : ℝ) * ((Nat.gcd d e : ℝ) * harmonicFloorError N (Nat.lcm d e))| ≤
          ∑ e ∈ l.divisors, |(μ (l / e) : ℝ)| *
            ∑ d ∈ m.divisors, |(μ (m / d) : ℝ)| *
              ((Nat.gcd d e : ℝ) * |harmonicFloorError N (Nat.lcm d e)|) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
          (abs_nonneg _)
        refine sum_congr rfl fun d _ => ?_
        rw [abs_mul, abs_mul,
          show |(Nat.gcd d e : ℝ)| = (Nat.gcd d e : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ ∑ e ∈ l.divisors, |(μ (l / e) : ℝ)| *
            ∑ d ∈ m.divisors, |(μ (m / d) : ℝ)| * (4 * (d : ℝ) * e / N) := by
        refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left (sum_le_sum fun d hd => ?_) (abs_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        have he0 : 0 < e := Nat.pos_of_mem_divisors he
        have hdeN : d * e ≤ N :=
          (Nat.mul_le_mul (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd))
            (Nat.le_of_dvd hl (Nat.dvd_of_mem_divisors he))).trans hml
        have hLN : Nat.lcm d e ≤ N := (Nat.div_le_self (d * e) (Nat.gcd d e)).trans hdeN
        have hferr := abs_harmonicFloorError_le (Nat.lcm_pos hd0 he0) hLN
        have hprod : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * e := by
          exact_mod_cast Nat.gcd_mul_lcm d e
        calc
          (Nat.gcd d e : ℝ) * |harmonicFloorError N (Nat.lcm d e)| ≤
              (Nat.gcd d e : ℝ) * (4 * (Nat.lcm d e : ℝ) / N) :=
            mul_le_mul_of_nonneg_left hferr (Nat.cast_nonneg _)
          _ = 4 * ((Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ)) / N := by ring
          _ = 4 * (d : ℝ) * e / N := by rw [hprod]; ring
      _ = (4 / (N : ℝ)) * (∑ d ∈ m.divisors, |(μ (m / d) : ℝ)| * (d : ℝ)) *
            (∑ e ∈ l.divisors, |(μ (l / e) : ℝ)| * (e : ℝ)) := by
        rw [mul_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        exact sum_congr rfl fun d _ => by ring
  unfold conductorGramFloorError floorAmplitude
  rw [abs_div, abs_of_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm))
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hl))) hL)]
  exact (div_le_div_of_nonneg_right hinner (by positivity)).trans_eq (by ring)

/-- Multiplicative Euler-product majorant on the squared floor amplitude. -/
private theorem floorAmplitude_sq_le_euler {m : ℕ} (hm : 0 < m) :
    floorAmplitude m ^ 2 ≤ (m : ℝ) * ∏ p ∈ m.primeFactors, (1 + 7 / (p : ℝ)) := by
  have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  unfold floorAmplitude
  rw [div_pow, Real.sq_sqrt hφm.le, div_le_iff₀ hφm]
  revert hm
  refine Nat.recOnPrimeCoprime (fun h => False.elim (Nat.lt_irrefl 0 h)) ?_ ?_ m
  · intro p k hp _
    rcases k with _ | k
    · simp
    · have hsum : (∑ d ∈ (p ^ (k + 1)).divisors, |(μ (p ^ (k + 1) / d) : ℝ)| * (d : ℝ)) =
          (p : ℝ) ^ k * ((p : ℝ) + 1) := by
        rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ]
        have hzero : ∀ j ∈ range k,
            |(μ (p ^ (k + 1) / p ^ j) : ℝ)| * ((p ^ j : ℕ) : ℝ) = 0 := by
          intro j hj
          have hjlt : j < k := mem_range.mp hj
          rw [Nat.pow_div (by omega) hp.pos]
          have hnsq : ¬ Squarefree (p ^ (k + 1 - j)) := by
            rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
            omega
          simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
        rw [sum_eq_zero hzero, zero_add, Nat.pow_div (by omega) hp.pos,
          show k + 1 - k = 1 by omega, pow_one, ArithmeticFunction.moebius_apply_prime hp,
          Nat.div_self (pow_pos hp.pos _), ArithmeticFunction.moebius_apply_one]
        push_cast
        norm_num
        ring
      rw [hsum, Nat.totient_prime_pow_succ hp k,
        Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) hp, prod_singleton]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      have hpoly : ((p : ℝ) + 1) ^ 2 ≤ (1 + 7 / (p : ℝ)) * (p : ℝ) * ((p : ℝ) - 1) := by
        have h1 : (1 + 7 / (p : ℝ)) * (p : ℝ) = (p : ℝ) + 7 := by field_simp [hp0.ne']
        rw [h1]
        nlinarith only [hp2]
      calc
        ((p : ℝ) ^ k * ((p : ℝ) + 1)) ^ 2 = (p : ℝ) ^ (2 * k) * ((p : ℝ) + 1) ^ 2 := by ring
        _ ≤ (p : ℝ) ^ (2 * k) * ((1 + 7 / (p : ℝ)) * (p : ℝ) * ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hpoly (pow_nonneg hp0.le _)
        _ = (p : ℝ) ^ (k + 1) * (1 + 7 / (p : ℝ)) * ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
          rw [pow_succ, show 2 * k = k + k by ring, pow_add]; ring
  · intro a b _ _ hab iha ihb hab_pos
    have ha : 0 < a := Nat.pos_of_mul_pos_right hab_pos
    have hb : 0 < b := Nat.pos_of_mul_pos_left hab_pos
    have hdiv : (∑ d ∈ (a * b).divisors, |(μ (a * b / d) : ℝ)| * (d : ℝ)) =
        (∑ d₁ ∈ a.divisors, |(μ (a / d₁) : ℝ)| * (d₁ : ℝ)) *
          (∑ d₂ ∈ b.divisors, |(μ (b / d₂) : ℝ)| * (d₂ : ℝ)) := by
      rw [sum_divisors_mul_of_coprime hab, sum_mul]
      refine sum_congr rfl fun d₁ hd₁ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun d₂ hd₂ => ?_
      have h1 := Nat.dvd_of_mem_divisors hd₁
      have h2 := Nat.dvd_of_mem_divisors hd₂
      have hcop_q : (a / d₁).Coprime (b / d₂) :=
        (hab.coprime_div_left h1).coprime_div_right h2
      rw [← Nat.div_mul_div_comm h1 h2,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_q]
      push_cast
      rw [abs_mul]
      ring
    rw [hdiv, mul_pow, Nat.totient_mul hab, hab.primeFactors_mul,
      prod_union hab.disjoint_primeFactors, Nat.cast_mul, Nat.cast_mul]
    calc
      (∑ d₁ ∈ a.divisors, |(μ (a / d₁) : ℝ)| * (d₁ : ℝ)) ^ 2 *
          (∑ d₂ ∈ b.divisors, |(μ (b / d₂) : ℝ)| * (d₂ : ℝ)) ^ 2 ≤
        ((a : ℝ) * (∏ p ∈ a.primeFactors, (1 + 7 / (p : ℝ))) * a.totient) *
          ((b : ℝ) * (∏ p ∈ b.primeFactors, (1 + 7 / (p : ℝ))) * b.totient) :=
        mul_le_mul (iha ha) (ihb hb) (sq_nonneg _) (by positivity)
      _ = (a : ℝ) * b *
            ((∏ p ∈ a.primeFactors, (1 + 7 / (p : ℝ))) * ∏ p ∈ b.primeFactors, (1 + 7 / (p : ℝ))) *
            ((a.totient : ℝ) * b.totient) := by ring

/-- Mean-square bound `∑_{m=1}^M f(m)^2 ≤ e^7 M^2` via prime-subset expansion. -/
private theorem sum_floorAmplitude_sq_le (M : ℕ) :
    (∑ m ∈ Icc 1 M, floorAmplitude m ^ 2) ≤ Real.exp 7 * (M : ℝ) ^ 2 := by
  let P := (Icc 1 M).filter Nat.Prime
  have hP_prime : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hm_sub : ∀ m ∈ Icc 1 M, m.primeFactors ⊆ P := by
    intro m hm p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.pos,
      (Nat.le_of_dvd (mem_Icc.mp hm).1 (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hm).2⟩, hpp⟩
  have hmult_sum : ∀ r : ℕ, 1 ≤ r →
      (∑ m ∈ (Icc 1 M).filter (r ∣ ·), (m : ℝ)) ≤ (M : ℝ) ^ 2 / r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hbij : (∑ m ∈ (Icc 1 M).filter (r ∣ ·), (m : ℝ)) =
        (r : ℝ) * ∑ k ∈ Icc 1 (M / r), (k : ℝ) := by
      rw [mul_sum]
      refine sum_nbij' (fun m => m / r) (fun k => r * k) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hmI, hdvd⟩ := mem_filter.mp hm
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hmI).1 hdvd) hr,
          Nat.div_le_div_right (mem_Icc.mp hmI).2⟩
      · intro k hk
        obtain ⟨hk1, hkQ⟩ := mem_Icc.mp hk
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hr hk1,
          (Nat.mul_le_mul_left r hkQ).trans (Nat.mul_div_le M r)⟩, dvd_mul_right r k⟩
      · intro m hm
        exact Nat.mul_div_cancel' (mem_filter.mp hm).2
      · intro k _
        exact Nat.mul_div_cancel_left k hr
      · intro m hm
        exact_mod_cast (Nat.mul_div_cancel' (mem_filter.mp hm).2).symm
    have hQ : (∑ k ∈ Icc 1 (M / r), (k : ℝ)) ≤ ((M / r : ℕ) : ℝ) ^ 2 := by
      let Q := M / r
      calc
        (∑ k ∈ Icc 1 Q, (k : ℝ)) ≤ ∑ _k ∈ Icc 1 Q, (Q : ℝ) :=
          sum_le_sum fun k hk => by exact_mod_cast (mem_Icc.mp hk).2
        _ = (Q : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, sq]
    have hQr : ((M / r : ℕ) : ℝ) ≤ (M : ℝ) / r := by
      rw [le_div_iff₀ hr0]
      exact_mod_cast Nat.div_mul_le_self M r
    rw [hbij]
    calc
      (r : ℝ) * (∑ k ∈ Icc 1 (M / r), (k : ℝ)) ≤ (r : ℝ) * ((M / r : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hQ hr0.le
      _ ≤ (r : ℝ) * ((M : ℝ) / r) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hQr 2) hr0.le
      _ = (M : ℝ) ^ 2 / r := by field_simp [hr0.ne']
  have hsum_P : (∑ p ∈ P, 7 / (p : ℝ) ^ 2) ≤ 7 := by
    have hsub : P ⊆ Icc 2 M := by
      intro p hp
      exact mem_Icc.mpr ⟨(hP_prime p hp).two_le, (mem_Icc.mp (mem_filter.mp hp).1).2⟩
    have htele : (∑ n ∈ Icc 2 M, 1 / (n : ℝ) ^ 2) ≤ 1 := by
      rcases lt_or_ge M 2 with hM | hM
      · rw [Icc_eq_empty_of_lt hM, sum_empty]; norm_num
      · obtain ⟨K, rfl⟩ : ∃ K, M = K + 2 := ⟨M - 2, (Nat.sub_add_cancel hM).symm⟩
        have hpt : ∀ n ∈ Icc 2 (K + 2), 1 / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
          intro n hn
          have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by linarith
          have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
          rw [div_sub_div _ _ hn1.ne' hn0.ne', div_le_div_iff₀ (sq_pos_of_pos hn0) (mul_pos hn1 hn0)]
          nlinarith only [hn2]
        have htel_eq : ∀ J : ℕ,
            (∑ n ∈ Icc 2 (J + 2), (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) = 1 - 1 / ((J + 2 : ℕ) : ℝ) := by
          intro J
          induction J with
          | zero => simp; norm_num
          | succ J ih =>
            have hins : Icc 2 (J + 1 + 2) = insert (J + 1 + 2) (Icc 2 (J + 2)) := by
              ext x; simp only [mem_insert, mem_Icc]; omega
            rw [hins, sum_insert (by simp), ih]
            push_cast
            ring
        calc
          (∑ n ∈ Icc 2 (K + 2), 1 / (n : ℝ) ^ 2) ≤
              ∑ n ∈ Icc 2 (K + 2), (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := sum_le_sum hpt
          _ = 1 - 1 / ((K + 2 : ℕ) : ℝ) := htel_eq K
          _ ≤ 1 := by
            have hpos : 0 ≤ 1 / ((K + 2 : ℕ) : ℝ) := by positivity
            linarith only [hpos]
    calc
      (∑ p ∈ P, 7 / (p : ℝ) ^ 2) ≤ ∑ n ∈ Icc 2 M, 7 / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 7 * ∑ n ∈ Icc 2 M, 1 / (n : ℝ) ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
      _ ≤ 7 * 1 := mul_le_mul_of_nonneg_left htele (by norm_num)
      _ = 7 := mul_one 7
  calc
    (∑ m ∈ Icc 1 M, floorAmplitude m ^ 2) ≤
        ∑ m ∈ Icc 1 M, (m : ℝ) * ∏ p ∈ m.primeFactors, (1 + 7 / (p : ℝ)) :=
      sum_le_sum fun m hm => floorAmplitude_sq_le_euler (mem_Icc.mp hm).1
    _ = ∑ m ∈ Icc 1 M, (m : ℝ) * ∑ T ∈ m.primeFactors.powerset, ∏ p ∈ T, (7 / (p : ℝ)) := by
      refine sum_congr rfl fun m _ => ?_
      rw [prod_one_add]
    _ ≤ ∑ m ∈ Icc 1 M, ∑ T ∈ P.powerset,
          if (∏ p ∈ T, p) ∣ m then (m : ℝ) * ∏ p ∈ T, (7 / (p : ℝ)) else 0 := by
      refine sum_le_sum fun m hm => ?_
      rw [mul_sum]
      have hpow_sub : m.primeFactors.powerset ⊆ P.powerset :=
        powerset_mono.mpr (hm_sub m hm)
      calc
        (∑ T ∈ m.primeFactors.powerset, (m : ℝ) * ∏ p ∈ T, (7 / (p : ℝ))) =
            ∑ T ∈ m.primeFactors.powerset,
              if (∏ p ∈ T, p) ∣ m then (m : ℝ) * ∏ p ∈ T, (7 / (p : ℝ)) else 0 := by
          refine sum_congr rfl fun T hT => ?_
          have hdvd : (∏ p ∈ T, p) ∣ m :=
            (prod_dvd_prod_of_subset T m.primeFactors id (mem_powerset.mp hT)).trans
              (Nat.prod_primeFactors_dvd m)
          rw [if_pos hdvd]
        _ ≤ ∑ T ∈ P.powerset,
              if (∏ p ∈ T, p) ∣ m then (m : ℝ) * ∏ p ∈ T, (7 / (p : ℝ)) else 0 :=
          sum_le_sum_of_subset_of_nonneg hpow_sub fun _ _ _ => by split_ifs <;> positivity
    _ = ∑ T ∈ P.powerset, (∏ p ∈ T, (7 / (p : ℝ))) * ∑ m ∈ (Icc 1 M).filter ((∏ p ∈ T, p) ∣ ·), (m : ℝ) := by
      rw [sum_comm]
      refine sum_congr rfl fun T _ => ?_
      rw [← sum_filter, mul_sum]
      exact sum_congr rfl fun m _ => mul_comm _ _
    _ ≤ ∑ T ∈ P.powerset, (∏ p ∈ T, (7 / (p : ℝ))) * ((M : ℝ) ^ 2 / (∏ p ∈ T, p : ℕ)) := by
      refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left ?_
        (prod_nonneg fun p _ => by positivity)
      exact hmult_sum (∏ p ∈ T, p) (prod_pos fun p hp => (hP_prime p (mem_powerset.mp hT hp)).pos)
    _ = (M : ℝ) ^ 2 * ∑ T ∈ P.powerset, ∏ p ∈ T, (7 / (p : ℝ) ^ 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun T hT => ?_
      have hr0 : (∏ p ∈ T, (p : ℝ)) ≠ 0 :=
        prod_ne_zero_iff.mpr fun p hp => by exact_mod_cast (hP_prime p (mem_powerset.mp hT hp)).ne_zero
      rw [Nat.cast_prod, prod_div_distrib, prod_div_distrib, prod_pow]
      field_simp [hr0]
    _ = (M : ℝ) ^ 2 * ∏ p ∈ P, (1 + 7 / (p : ℝ) ^ 2) := by rw [prod_one_add]
    _ ≤ (M : ℝ) ^ 2 * ∏ p ∈ P, Real.exp (7 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (prod_le_prod (fun _ _ => by positivity) fun p _ => by
          simpa only [add_comm] using Real.add_one_le_exp (7 / (p : ℝ) ^ 2)) (sq_nonneg _)
    _ = (M : ℝ) ^ 2 * Real.exp (∑ p ∈ P, 7 / (p : ℝ) ^ 2) := by rw [Real.exp_sum]
    _ ≤ (M : ℝ) ^ 2 * Real.exp 7 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_P) (sq_nonneg _)
    _ = Real.exp 7 * (M : ℝ) ^ 2 := mul_comm _ _

/-- Uniform whole-prefix upper Riesz frame bound `‖∑_{m=1}^M a_m v_m‖^2 ≤ 6 ∑_{m=1}^M a_m^2`
below the square-root horizon `M^2 ≤ N` once `4 e^7 ≤ log N`. -/
theorem ramanujanConductor_upper_riesz {M N : ℕ} (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) (a : ℕ → ℝ) :
    ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      6 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
  by_cases hM0 : M = 0
  · subst hM0; simp
  have hM1 : 1 ≤ M := Nat.pos_of_ne_zero hM0
  have hN1 : 1 ≤ N := (Nat.mul_pos hM1 hM1).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have he7 : (1 : ℝ) ≤ Real.exp 7 := Real.one_le_exp (by norm_num)
    linarith
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  rw [norm_sum_normalizedRamanujanHorizonVector_sq_eq_gram]
  have hexpand :
      (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) =
      (∑ m ∈ Icc 1 M, a m ^ 2 *
          (1 + (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N)) -
        (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l) / Real.log N +
        ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorGramFloorError m l N := by
    have hrew : ∀ m ∈ Icc 1 M, ∀ l ∈ Icc 1 M,
        a m * a l * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ =
          (if m = l then a m ^ 2 *
              (1 + (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N)
            else 0) -
            (a m * a l * conductorOffDiagKernel m l) / Real.log N +
            a m * a l * conductorGramFloorError m l N := by
      intro m hm l hl
      have hmlN : m * l ≤ N :=
        (Nat.mul_le_mul (mem_Icc.mp hm).2 (mem_Icc.mp hl).2).trans hMN
      rw [normalizedRamanujanHorizonVector_gram_exact (mem_Icc.mp hm).1 (mem_Icc.mp hl).1 hmlN hL0]
      unfold conductorOffDiagKernel
      by_cases heq : m = l
      · subst heq; simp; ring
      · simp only [if_neg heq]
        ring
    simp_rw [sum_congr rfl fun m hm => sum_congr rfl (hrew m hm)]
    simp only [sum_add_distrib, sum_sub_distrib, ← sum_div]
    congr 2
    refine sum_congr rfl fun m hm => ?_
    rw [sum_ite_eq, if_pos hm]
  rw [hexpand]
  have hγ : Real.eulerMascheroniConstant ≤ 1 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1
    simp [Real.eulerMascheroniSeq'] at h
    exact h.le
  have hdiag :
      (∑ m ∈ Icc 1 M, a m ^ 2 *
        (1 + (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N)) ≤
        2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have ht := tameDifferent_le_log (mem_Icc.mp hm).1
    have hnum : Real.eulerMascheroniConstant - Real.log m + tameDifferent m ≤ Real.log N := by
      linarith only [ht, hγ, hL1]
    have hfrac : (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N ≤ 1 :=
      (div_le_one hL0).mpr hnum
    calc
      a m ^ 2 * (1 + (Real.eulerMascheroniConstant - Real.log m + tameDifferent m) / Real.log N) ≤
          a m ^ 2 * 2 := mul_le_mul_of_nonneg_left (by linarith only [hfrac]) (sq_nonneg _)
      _ = 2 * a m ^ 2 := mul_comm _ _
  have hoff :
      -((∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l) / Real.log N) ≤
        3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have habs := abs_sum_conductorOffDiagKernel_le (M := M) a
    have hlogM : 2 * Real.log M ≤ Real.log N := by
      have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
      have hsq : (M : ℝ) ^ 2 ≤ N := by exact_mod_cast (show M ^ 2 ≤ N by simpa [sq] using hMN)
      have h := Real.log_le_log (pow_pos hMR 2) hsq
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have h32 : 3 * Real.sqrt 2 ≤ 6 := by
      have hs2 : Real.sqrt 2 ≤ 2 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    have hnum : -(∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l) ≤
        3 * Real.log N * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      calc
        -(∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l) ≤
            |∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorOffDiagKernel m l| :=
          neg_le_abs _
        _ ≤ 3 * Real.sqrt 2 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 := habs
        _ ≤ 6 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h32 (Real.log_natCast_nonneg M))
            (sum_nonneg fun _ _ => sq_nonneg _)
        _ ≤ 3 * Real.log N * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hlogM]) (sum_nonneg fun _ _ => sq_nonneg _)
    rw [← neg_div, div_le_iff₀ hL0]
    linarith only [hnum]
  have hrem :
      (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorGramFloorError m l N) ≤
        ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 M) (fun m => |a m|) floorAmplitude
    simp only [sq_abs] at hcs
    have hMN_real : (M : ℝ) ^ 2 ≤ N := by exact_mod_cast (show M ^ 2 ≤ N by simpa [sq] using hMN)
    calc
      (∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, a m * a l * conductorGramFloorError m l N) ≤
          ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M, |a m| * |a l| * |conductorGramFloorError m l N| := by
        refine sum_le_sum fun m _ => sum_le_sum fun l _ => ?_
        have h := le_abs_self (a m * a l * conductorGramFloorError m l N)
        rwa [abs_mul, abs_mul] at h
      _ ≤ ∑ m ∈ Icc 1 M, ∑ l ∈ Icc 1 M,
            |a m| * |a l| * (4 / ((N : ℝ) * Real.log N) * (floorAmplitude m * floorAmplitude l)) := by
        refine sum_le_sum fun m hm => sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact abs_conductorGramFloorError_le (mem_Icc.mp hm).1 (mem_Icc.mp hl).1
          ((Nat.mul_le_mul (mem_Icc.mp hm).2 (mem_Icc.mp hl).2).trans hMN) hL0
      _ = 4 / ((N : ℝ) * Real.log N) * (∑ m ∈ Icc 1 M, |a m| * floorAmplitude m) ^ 2 := by
        rw [sq, sum_mul, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum, mul_sum]
        exact sum_congr rfl fun l _ => by ring
      _ ≤ 4 / ((N : ℝ) * Real.log N) *
            ((∑ m ∈ Icc 1 M, a m ^ 2) * ∑ m ∈ Icc 1 M, floorAmplitude m ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ 4 / ((N : ℝ) * Real.log N) * ((∑ m ∈ Icc 1 M, a m ^ 2) * (Real.exp 7 * (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (sum_floorAmplitude_sq_le M) (sum_nonneg fun _ _ => sq_nonneg _))
          (by positivity)
      _ = (4 * Real.exp 7 * (M : ℝ) ^ 2 / ((N : ℝ) * Real.log N)) * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
      _ ≤ 1 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _)
        rw [div_le_one (mul_pos hN0 hL0)]
        calc
          4 * Real.exp 7 * (M : ℝ) ^ 2 ≤ 4 * Real.exp 7 * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hMN_real (by positivity)
          _ ≤ Real.log N * (N : ℝ) := mul_le_mul_of_nonneg_right hL hN0.le
          _ = (N : ℝ) * Real.log N := mul_comm _ _
      _ = ∑ m ∈ Icc 1 M, a m ^ 2 := one_mul _
  linarith only [hdiag, hoff, hrem]

/-- Individual norm-square ceiling `‖v_m‖^2 ≤ 6` for every `1 ≤ m ≤ M` with `M^2 ≤ N`. -/
theorem normalizedRamanujanHorizonVector_norm_sq_le_six {m M N : ℕ} (hm : m ∈ Icc 1 M)
    (hMN : M * M ≤ N) (hL : 4 * Real.exp 7 ≤ Real.log N) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 6 := by
  have h := ramanujanConductor_upper_riesz hMN hL (fun k => if k = m then 1 else 0)
  simpa only [ite_smul, one_smul, zero_smul, sum_ite_eq', if_pos hm, ite_pow, one_pow,
    zero_pow (by decide : 2 ≠ 0), mul_one] using h

/-- Dual Bessel inequality `∑_{m=1}^M <y, v_m>^2 ≤ 6 ‖y‖^2` on `ℝ^N`. -/
theorem sum_inner_normalizedRamanujanHorizonVector_sq_le {M N : ℕ} (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) (y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ m ∈ Icc 1 M, ⟪y, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤ 6 * ‖y‖ ^ 2 := by
  let a : ℕ → ℝ := fun m => ⟪y, normalizedRamanujanHorizonVector m N⟫
  let w := ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N
  have hid : (∑ m ∈ Icc 1 M, a m ^ 2) = ⟪y, w⟫ := by
    dsimp only [w]
    rw [inner_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [real_inner_smul_right]
    dsimp only [a]
    ring
  have hcs : ⟪y, w⟫ ≤ ‖y‖ * ‖w‖ := real_inner_le_norm y w
  have hw := ramanujanConductor_upper_riesz hMN hL a
  have h0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hsq : (∑ m ∈ Icc 1 M, a m ^ 2) ^ 2 ≤ 6 * ‖y‖ ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    calc
      (∑ m ∈ Icc 1 M, a m ^ 2) ^ 2 = ⟪y, w⟫ ^ 2 := by rw [hid]
      _ ≤ (‖y‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (hid ▸ h0) hcs 2
      _ = ‖y‖ ^ 2 * ‖w‖ ^ 2 := mul_pow _ _ 2
      _ ≤ ‖y‖ ^ 2 * (6 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = 6 * ‖y‖ ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  by_cases hz : (∑ m ∈ Icc 1 M, a m ^ 2) = 0
  · rw [hz]; positivity
  · have hpos : 0 < ∑ m ∈ Icc 1 M, a m ^ 2 := lt_of_le_of_ne h0 (Ne.symm hz)
    nlinarith only [hsq, hpos]

/-! ### Divisor-totient packet envelope -/

/-- Submultiplicativity of the divisor-count function: `τ(a * b) ≤ τ(a) * τ(b)`. -/
private theorem card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases hab0 : a * b = 0
  · simp [hab0]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
  rw [← card_product]
  refine Finset.card_le_card_of_injOn (fun d => (Nat.gcd d a, d / Nat.gcd d a)) ?_ ?_
  · intro d hd
    have hdvd : d ∣ a * b := Nat.dvd_of_mem_divisors hd
    have hg_dvd_d : Nat.gcd d a ∣ d := Nat.gcd_dvd_left d a
    have hg0 : 0 < Nat.gcd d a := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero ha0)
    have hcop : (d / Nat.gcd d a).Coprime (a / Nat.gcd d a) := Nat.coprime_div_gcd_div_gcd hg0
    have hqb : d / Nat.gcd d a ∣ b := by
      have hmul_dvd : (d / Nat.gcd d a) * Nat.gcd d a ∣ (a / Nat.gcd d a * b) * Nat.gcd d a := by
        rw [Nat.div_mul_cancel hg_dvd_d,
          show a / Nat.gcd d a * b * Nat.gcd d a = a / Nat.gcd d a * Nat.gcd d a * b by ring,
          Nat.div_mul_cancel (Nat.gcd_dvd_right d a)]
        exact hdvd
      exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_right hg0).mp hmul_dvd)
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d a, ha0⟩,
      Nat.mem_divisors.mpr ⟨hqb, hb0⟩⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    calc
      d₁ = d₁ / Nat.gcd d₁ a * Nat.gcd d₁ a := (Nat.div_mul_cancel (Nat.gcd_dvd_left d₁ a)).symm
      _ = d₂ / Nat.gcd d₂ a * Nat.gcd d₂ a := congrArg₂ (· * ·) h2 h1
      _ = d₂ := Nat.div_mul_cancel (Nat.gcd_dvd_left d₂ a)

/-- Squarefree totient ratio bound `r / φ(r)^2 ≤ τ(r)^2 / r`. -/
private theorem squarefree_div_totient_sq_le {r : ℕ} (hr0 : 0 < r) (hr : Squarefree r) :
    (r : ℝ) / (r.totient : ℝ) ^ 2 ≤ (r.divisors.card : ℝ) ^ 2 / r := by
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  rw [div_le_div_iff₀ (sq_pos_of_pos hφr) hrR]
  revert hr0 hr
  refine Nat.recOnPrimeCoprime (fun h => False.elim (Nat.lt_irrefl 0 h)) ?_ ?_ r
  · intro p k hp hk_pos hsq
    rcases k with _ | _ | k
    · simp
    · simp only [Nat.zero_add, pow_one]
      rw [Nat.totient_prime hp, hp.divisors, card_pair hp.ne_one.symm]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      rw [Nat.cast_sub hp.one_lt.le]
      push_cast
      nlinarith only [hp2]
    · exfalso
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)] at hsq
      omega
  · intro a b _ _ hab iha ihb hab_pos hab_sq
    have ha0 : 0 < a := Nat.pos_of_mul_pos_right hab_pos
    have hb0 : 0 < b := Nat.pos_of_mul_pos_left hab_pos
    have ha_sq : Squarefree a := hab_sq.squarefree_of_dvd (dvd_mul_right a b)
    have hb_sq : Squarefree b := hab_sq.squarefree_of_dvd (dvd_mul_left b a)
    have hcard : (a * b).divisors.card = a.divisors.card * b.divisors.card := by
      rw [Nat.divisors_mul, Finset.mul_def, card_image_of_injOn hab.mul_injOn_divisors, card_product]
    rw [hcard, Nat.totient_mul hab]
    push_cast
    calc
      ((a : ℝ) * b) * ((a : ℝ) * b) = ((a : ℝ) * a) * ((b : ℝ) * b) := by ring
      _ ≤ ((a.divisors.card : ℝ) ^ 2 * (a.totient : ℝ) ^ 2) *
            ((b.divisors.card : ℝ) ^ 2 * (b.totient : ℝ) ^ 2) :=
        mul_le_mul (iha ha0 ha_sq) (ihb hb0 hb_sq) (by positivity) (by positivity)
      _ = ((a.divisors.card : ℝ) * b.divisors.card) ^ 2 * ((a.totient : ℝ) * b.totient) ^ 2 := by ring

/-- Dirichlet-convolution harmonic bound on `[1, M]`:
`∑_{r=1}^M ∑_{d ∣ r} (f(d)/d) (f(r/d)/(r/d)) ≤ (∑_{d=1}^M f(d)/d)^2` for nonnegative `f`. -/
private theorem sum_Icc_divisors_mul_div_le (M : ℕ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ r ∈ Icc 1 M, ∑ d ∈ r.divisors, (f d / d) * (f (r / d) / (r / d : ℕ))) ≤
      (∑ d ∈ Icc 1 M, f d / d) ^ 2 := by
  have hdiv_eq : ∀ r ∈ Icc 1 M, r.divisors = (Icc 1 M).filter (· ∣ r) := by
    intro r hr
    obtain ⟨hr1, hrM⟩ := mem_Icc.mp hr
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hr1, (Nat.le_of_dvd hr1 hdvd).trans hrM⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  have hrew :
      (∑ r ∈ Icc 1 M, ∑ d ∈ r.divisors, (f d / d) * (f (r / d) / (r / d : ℕ))) =
        ∑ d ∈ Icc 1 M, ∑ r ∈ (Icc 1 M).filter (d ∣ ·), (f d / d) * (f (r / d) / (r / d : ℕ)) := by
    calc
      (∑ r ∈ Icc 1 M, ∑ d ∈ r.divisors, (f d / d) * (f (r / d) / (r / d : ℕ))) =
          ∑ r ∈ Icc 1 M, ∑ d ∈ (Icc 1 M).filter (· ∣ r),
            (f d / d) * (f (r / d) / (r / d : ℕ)) :=
        sum_congr rfl fun r hr => by rw [hdiv_eq r hr]
      _ = ∑ r ∈ Icc 1 M, ∑ d ∈ Icc 1 M,
            if d ∣ r then (f d / d) * (f (r / d) / (r / d : ℕ)) else 0 :=
        sum_congr rfl fun r _ => sum_filter _ _
      _ = ∑ d ∈ Icc 1 M, ∑ r ∈ Icc 1 M,
            if d ∣ r then (f d / d) * (f (r / d) / (r / d : ℕ)) else 0 := sum_comm
      _ = ∑ d ∈ Icc 1 M, ∑ r ∈ (Icc 1 M).filter (d ∣ ·),
            (f d / d) * (f (r / d) / (r / d : ℕ)) :=
        sum_congr rfl fun d _ => (sum_filter _ _).symm
  rw [hrew, sq, sum_mul]
  refine sum_le_sum fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hbij :
      (∑ r ∈ (Icc 1 M).filter (d ∣ ·), (f d / d) * (f (r / d) / (r / d : ℕ))) =
        ∑ q ∈ Icc 1 (M / d), (f d / d) * (f q / q) := by
    refine Finset.sum_bij (fun r _ => r / d) ?_ ?_ ?_ ?_
    · intro r hr
      obtain ⟨hrI, hdvd⟩ := mem_filter.mp hr
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hrI).1 hdvd) hd0,
        Nat.div_le_div_right (mem_Icc.mp hrI).2⟩
    · intro r₁ hr₁ r₂ hr₂ heq
      rw [← Nat.mul_div_cancel' (mem_filter.mp hr₁).2,
        ← Nat.mul_div_cancel' (mem_filter.mp hr₂).2, heq]
    · intro q hq
      obtain ⟨hq1, hqM⟩ := mem_Icc.mp hq
      exact ⟨d * q, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd0 hq1,
        (Nat.mul_le_mul_left d hqM).trans (Nat.mul_div_le M d)⟩, dvd_mul_right d q⟩,
        Nat.mul_div_cancel_left q hd0⟩
    · intro r _; rfl
  rw [hbij, ← mul_sum]
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self M d))
      fun q _ _ => div_nonneg (hf q) (Nat.cast_nonneg q))
    (div_nonneg (hf d) (Nat.cast_nonneg d))

/-- Fourth-power harmonic bound `∑_{r=1}^M τ(r)^2 / r ≤ (1 + log M)^4`. -/
private theorem sum_Icc_card_divisors_sq_div_le (M : ℕ) :
    (∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) ^ 2 / r) ≤ (1 + Real.log M) ^ 4 := by
  have htau1 : (∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) / r) ≤ (1 + Real.log M) ^ 2 := by
    have hrw : ∀ r ∈ Icc 1 M, (r.divisors.card : ℝ) / r =
        ∑ d ∈ r.divisors, ((1 : ℝ) / d) * (1 / (r / d : ℕ)) := by
      intro r _
      have hpt : ∀ d ∈ r.divisors, ((1 : ℝ) / d) * (1 / (r / d : ℕ)) = 1 / (r : ℝ) := by
        intro d hd
        have hmul : (d : ℝ) * (r / d : ℕ) = r := by
          exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        rw [div_mul_div_comm, one_mul, hmul]
      rw [sum_congr rfl hpt, sum_const, nsmul_eq_mul, mul_one_div]
    calc
      (∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) / r) =
          ∑ r ∈ Icc 1 M, ∑ d ∈ r.divisors, ((1 : ℝ) / d) * (1 / (r / d : ℕ)) :=
        sum_congr rfl hrw
      _ ≤ (∑ d ∈ Icc 1 M, (1 : ℝ) / d) ^ 2 :=
        sum_Icc_divisors_mul_div_le M (fun _ => 1) (fun _ => zero_le_one)
      _ ≤ (1 + Real.log M) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity)
          (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log M) 2
  have hpt2 : ∀ r ∈ Icc 1 M, (r.divisors.card : ℝ) ^ 2 / r ≤
      ∑ d ∈ r.divisors,
        ((d.divisors.card : ℝ) / d) * (((r / d).divisors.card : ℝ) / (r / d : ℕ)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hcard_eq : (r.divisors.card : ℝ) ^ 2 / r =
        ∑ _d ∈ r.divisors, (r.divisors.card : ℝ) / r := by
      rw [sum_const, nsmul_eq_mul, sq, mul_div_assoc]
    rw [hcard_eq]
    refine sum_le_sum fun d hd => ?_
    have hmul : d * (r / d) = r := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hsubm : (r.divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * (r / d).divisors.card := by
      have hnat : r.divisors.card ≤ d.divisors.card * (r / d).divisors.card := by
        conv_lhs => rw [← hmul]
        exact card_divisors_mul_le d (r / d)
      exact_mod_cast hnat
    have hr_cast : (r : ℝ) = (d : ℝ) * (r / d : ℕ) := by exact_mod_cast hmul.symm
    calc
      (r.divisors.card : ℝ) / r ≤ ((d.divisors.card : ℝ) * (r / d).divisors.card) / r :=
        div_le_div_of_nonneg_right hsubm hr0.le
      _ = ((d.divisors.card : ℝ) / d) * (((r / d).divisors.card : ℝ) / (r / d : ℕ)) := by
        rw [hr_cast, div_mul_div_comm]
  calc
    (∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) ^ 2 / r) ≤
        ∑ r ∈ Icc 1 M, ∑ d ∈ r.divisors,
          ((d.divisors.card : ℝ) / d) * (((r / d).divisors.card : ℝ) / (r / d : ℕ)) :=
      sum_le_sum hpt2
    _ ≤ (∑ d ∈ Icc 1 M, (d.divisors.card : ℝ) / d) ^ 2 :=
      sum_Icc_divisors_mul_div_le M (fun a => (a.divisors.card : ℝ)) (fun _ => Nat.cast_nonneg _)
    _ ≤ ((1 + Real.log M) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) htau1 2
    _ = (1 + Real.log M) ^ 4 := by ring

/-- Sublinearity of Euler's totient under multiplication: `φ(d * r) ≤ φ(d) * r`. -/
private theorem totient_mul_le_self (d : ℕ) : ∀ r : ℕ, (d * r).totient ≤ d.totient * r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.lt_or_ge r 2 with hr | hr
    · interval_cases r <;> simp
    · obtain ⟨p, hp, s, rfl⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
      have hs0 : 0 < s := Nat.pos_of_ne_zero fun h => by simp [h] at hr
      have hs : s < p * s := lt_mul_left hs0 hp.one_lt
      have hstep : (p * (d * s)).totient ≤ p * (d * s).totient := by
        by_cases hdvd : p ∣ d * s
        · rw [Nat.totient_mul_of_prime_of_dvd hp hdvd]
        · rw [Nat.totient_mul_of_prime_of_not_dvd hp hdvd]
          exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      calc
        (d * (p * s)).totient = (p * (d * s)).totient := by ring_nf
        _ ≤ p * (d * s).totient := hstep
        _ ≤ p * (d.totient * s) := Nat.mul_le_mul_left p (ih s hs)
        _ = d.totient * (p * s) := by ring

/-- Divisor-totient packet envelope: for every `n ≥ 1` and `M : ℕ`,
`∑_{m=1}^M c̃_m(n)^2 ≤ n (1 + log M)^4`. -/
theorem sum_normalizedRamanujanMode_sq_le (M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ m ∈ Icc 1 M, normalizedRamanujanMode m n ^ 2) ≤ (n : ℝ) * (1 + Real.log M) ^ 4 := by
  have hpoint : ∀ m ∈ Icc 1 M,
      normalizedRamanujanMode m n ^ 2 ≤
        ((Nat.gcd m n).totient : ℝ) *
          ((m / Nat.gcd m n).divisors.card : ℝ) ^ 2 / (m / Nat.gcd m n : ℕ) := by
    intro m hm
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
    let d := Nat.gcd m n
    let r := m / d
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_left n hm0
    have hd_dvd : d ∣ m := Nat.gcd_dvd_left m n
    have hr0 : 0 < r := Nat.div_pos (Nat.le_of_dvd hm0 hd_dvd) hd0
    rw [normalizedRamanujanMode_eq_coefficient hm0, div_pow, Real.sq_sqrt hφm.le,
      ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_eq_moebius_totient_quotient]
    change ((m.totient : ℝ) * (moebiusReal r / (r.totient : ℝ))) ^ 2 / (m.totient : ℝ) ≤
      (d.totient : ℝ) * (r.divisors.card : ℝ) ^ 2 / r
    by_cases hsq : Squarefree r
    · have hμ : moebiusReal r ^ 2 = 1 := by
        unfold moebiusReal
        rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
          (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq) with h1 | h1 <;>
          simp [h1]
      have htot_le : (m.totient : ℝ) ≤ (d.totient : ℝ) * r := by
        have hm_eq : m = d * r := (Nat.mul_div_cancel' hd_dvd).symm
        have hnat : m.totient ≤ d.totient * r := hm_eq ▸ totient_mul_le_self d r
        exact_mod_cast hnat
      have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr0
      have hsimp : ((m.totient : ℝ) * (moebiusReal r / (r.totient : ℝ))) ^ 2 / (m.totient : ℝ) =
          (m.totient : ℝ) / (r.totient : ℝ) ^ 2 := by
        calc
          ((m.totient : ℝ) * (moebiusReal r / (r.totient : ℝ))) ^ 2 / (m.totient : ℝ) =
              (m.totient : ℝ) * moebiusReal r ^ 2 / (r.totient : ℝ) ^ 2 := by
            field_simp [hφm.ne', hφr.ne']
          _ = (m.totient : ℝ) / (r.totient : ℝ) ^ 2 := by rw [hμ, mul_one]
      rw [hsimp]
      calc
        (m.totient : ℝ) / (r.totient : ℝ) ^ 2 ≤ ((d.totient : ℝ) * r) / (r.totient : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right htot_le (sq_nonneg _)
        _ = (d.totient : ℝ) * ((r : ℝ) / (r.totient : ℝ) ^ 2) := by ring
        _ ≤ (d.totient : ℝ) * ((r.divisors.card : ℝ) ^ 2 / r) :=
          mul_le_mul_of_nonneg_left (squarefree_div_totient_sq_le hr0 hsq) (Nat.cast_nonneg _)
        _ = (d.totient : ℝ) * (r.divisors.card : ℝ) ^ 2 / r := by ring
    · have hμ0 : moebiusReal r = 0 := by
        unfold moebiusReal
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      rw [hμ0]
      simp only [zero_div, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hinj : ∀ m₁ ∈ Icc 1 M, ∀ m₂ ∈ Icc 1 M,
      (Nat.gcd m₁ n, m₁ / Nat.gcd m₁ n) = (Nat.gcd m₂ n, m₂ / Nat.gcd m₂ n) → m₁ = m₂ := by
    intro m₁ _ m₂ _ heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    calc
      m₁ = Nat.gcd m₁ n * (m₁ / Nat.gcd m₁ n) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m₁ n)).symm
      _ = Nat.gcd m₂ n * (m₂ / Nat.gcd m₂ n) := congrArg₂ (· * ·) h1 h2
      _ = m₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left m₂ n)
  have hsub : (Icc 1 M).image (fun m => (Nat.gcd m n, m / Nat.gcd m n)) ⊆
      n.divisors ×ˢ Icc 1 M := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    have hg0 : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm1
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m n, by omega⟩,
      mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm1 (Nat.gcd_dvd_left m n)) hg0,
        (Nat.div_le_self m _).trans hmM⟩⟩
  calc
    (∑ m ∈ Icc 1 M, normalizedRamanujanMode m n ^ 2) ≤
        ∑ m ∈ Icc 1 M, ((Nat.gcd m n).totient : ℝ) *
          ((m / Nat.gcd m n).divisors.card : ℝ) ^ 2 / (m / Nat.gcd m n : ℕ) :=
      sum_le_sum hpoint
    _ = ∑ x ∈ (Icc 1 M).image (fun m => (Nat.gcd m n, m / Nat.gcd m n)),
          (x.1.totient : ℝ) * ((x.2.divisors.card : ℝ) ^ 2 / x.2) := by
      rw [sum_image hinj]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ x ∈ n.divisors ×ˢ Icc 1 M,
          (x.1.totient : ℝ) * ((x.2.divisors.card : ℝ) ^ 2 / x.2) :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ d ∈ n.divisors, (d.totient : ℝ)) * ∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) ^ 2 / r := by
      rw [sum_product, sum_mul]
      exact sum_congr rfl fun d _ => by dsimp only; exact (mul_sum _ _ _).symm
    _ = (n : ℝ) * ∑ r ∈ Icc 1 M, (r.divisors.card : ℝ) ^ 2 / r := by
      congr 1
      exact_mod_cast Nat.sum_totient n
    _ ≤ (n : ℝ) * (1 + Real.log M) ^ 4 :=
      mul_le_mul_of_nonneg_left (sum_Icc_card_divisors_sq_div_le M) (Nat.cast_nonneg n)

#print axioms ramanujanConductor_lower_riesz
#print axioms finrank_conductorSubspace_eq
#print axioms normalizedRamanujanHorizonVector_gram_exact
#print axioms ramanujanConductor_upper_riesz
#print axioms sum_inner_normalizedRamanujanHorizonVector_sq_le
#print axioms sum_normalizedRamanujanMode_sq_le

end GaloisForLFunctions.CompletedArithmeticForms
