import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialPointsOfTheConstantSourceAreAtypical
import GaloisForLFunctions.RHTower.TwistedMertensLittlewood
import GaloisForLFunctions.RHTower.TwistedMertensOrderLowerBound
import GaloisForLFunctions.RHTower.TwistedMobiusZeroObstruction
import GaloisForLFunctions.RHTower.TwistedOrderLawExact
import GaloisForLFunctions.RHTower.DirichletLZeroHalfPlane

/-!
# The special locus reads GRH

At the trivial point the Möbius exponent is the zero abscissa `Θ` of `ζ`. This module proves the same
at every primitive Dirichlet gauge point: the Möbius exponent of `dirichletGauge χ` is the zero
abscissa `Θ_χ` of `L(s, χ)`.

* **Descent through the primes of `q`** (`coprimeMoebiusSet_eq_split`, `hasBound_insert_iff`). The
  twisted Möbius sum prime to a set `P` and the one prime to `P ∪ {p}` determine each other:
  `C_P(N) = C_{P∪p}(N) − χ(p) C_{P∪p}(N/p)`, inverted by a geometric series in `p^{−θ}`. Power bounds of
  positive exponent pass in both directions (`hasBound_iff_of_subset`).
* **The coprime sum is the twisted Mertens function**
  (`coprimeMoebiusSet_primeFactors_dirichletGauge`). Prime to `q`, the Dirichlet gauge point is its
  character, and `χ` vanishes elsewhere.
* **The exponent** (`gaugeExponent_moebius_dirichletGauge`). The twisted Littlewood bound gives
  `≤ Θ_χ`; a zero of `L(s, χ)` right of a power bound obstructs it, giving `≥ Θ_χ`.
* **Never better than typical; typical iff GRH** (`typicalExponent_le_gaugeExponent_moebius_dirichletGauge`,
  `dirichletGRH_iff_dirichletGauge_typical`). `L(s, χ)` has a zero with real part at least `1/2`, so the
  Dirichlet point is never better than typical, and it is typical iff GRH holds for `χ`. Vertical shifts
  and finite modifications do not change this (`gaugeExponent_moebius_dirichletGauge_verticalShift`).

For the constant source the special locus is atypical (exponent `0` or `1`). For the Möbius source every
point of the special locus, the trivial point included, sits at or above the typical exponent, and the
generalized Riemann hypothesis is the statement that all of them sit at it.
-/

open MeasureTheory Finset Filter Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### Descent through a set of primes -/

/-- The twisted Möbius sum over the integers in `[1, N]` divisible by no prime of `P`. -/
def coprimeMoebiusSet (P : Finset ℕ) (y : GaugeTorus) (N : ℕ) : ℂ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => ∀ r ∈ P, ¬ r ∣ n), ((μ n : ℤ) : ℂ) * twist y n

@[simp] theorem coprimeMoebiusSet_zero (P : Finset ℕ) (y : GaugeTorus) :
    coprimeMoebiusSet P y 0 = 0 := by
  simp [coprimeMoebiusSet]

theorem coprimeMoebiusSet_empty (y : GaugeTorus) (N : ℕ) :
    coprimeMoebiusSet ∅ y N = moebiusGaugeSum N y := by
  simp [coprimeMoebiusSet, moebiusGaugeSum]

/-- **Descent.** `C_P(N) = C_{P∪p}(N) − χ(p) C_{P∪p}(N/p)` for a prime `p ∉ P`. -/
theorem coprimeMoebiusSet_eq_split {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (y : GaugeTorus) (N : ℕ) :
    coprimeMoebiusSet P y N = coprimeMoebiusSet (insert p P) y N -
      twist y p * coprimeMoebiusSet (insert p P) y (N / p) := by
  classical
  have hsplit := sum_filter_add_sum_filter_not ((Icc 1 N).filter (fun n => ∀ r ∈ P, ¬ r ∣ n))
    (fun n => p ∣ n) (fun n => ((μ n : ℤ) : ℂ) * twist y n)
  rw [filter_filter, filter_filter] at hsplit
  have hins : ∀ M, (Icc 1 M).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ ¬ p ∣ n) =
      (Icc 1 M).filter (fun n => ∀ r ∈ insert p P, ¬ r ∣ n) := by
    intro M
    refine filter_congr fun n _ => ?_
    simp only [mem_insert, forall_eq_or_imp]
    exact and_comm
  have hmult : ∑ n ∈ (Icc 1 N).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ p ∣ n),
      ((μ n : ℤ) : ℂ) * twist y n = -(twist y p * coprimeMoebiusSet (insert p P) y (N / p)) := by
    rw [show (Icc 1 N).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ p ∣ n) =
        ((Icc 1 N).filter (fun n => p ∣ n)).filter (fun n => ∀ r ∈ P, ¬ r ∣ n) by
          rw [filter_filter]; exact filter_congr fun n _ => and_comm,
      ← image_mul_Icc hp.pos, filter_image,
      sum_image fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab]
    have hcongr : (Icc 1 (N / p)).filter (fun m => ∀ r ∈ P, ¬ r ∣ p * m) =
        (Icc 1 (N / p)).filter (fun m => ∀ r ∈ P, ¬ r ∣ m) :=
      filter_congr fun m _ => forall_not_dvd_prime_mul hP hp hpP m
    rw [hcongr, coprimeMoebiusSet, ← hins, ← filter_filter, sum_filter (fun m => ¬ p ∣ m),
      mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp (mem_filter.mp hm).1).1
    rw [moebius_prime_mul hp, twist_mul y hp.ne_zero hm0]
    split_ifs <;> ring
  rw [coprimeMoebiusSet, coprimeMoebiusSet, ← hsplit, hmult, hins]
  ring

/-- **Inversion.** `C_{P∪p}(N) = Σ_k χ(p)^k C_P(N/p^k)`. -/
theorem coprimeMoebiusSet_insert_eq_sum {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (y : GaugeTorus) (N : ℕ) :
    coprimeMoebiusSet (insert p P) y N = ∑ k ∈ range (N + 1),
      twist y p ^ k * coprimeMoebiusSet P y (N / p ^ k) := by
  have hpartial : ∀ K : ℕ, coprimeMoebiusSet (insert p P) y N =
      ∑ k ∈ range K, twist y p ^ k * coprimeMoebiusSet P y (N / p ^ k) +
        twist y p ^ K * coprimeMoebiusSet (insert p P) y (N / p ^ K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hs := coprimeMoebiusSet_eq_split hP hp hpP y (N / p ^ K)
      rw [Nat.div_div_eq_div_mul, ← pow_succ] at hs
      rw [ih, Finset.sum_range_succ, pow_succ]
      linear_combination (-(twist y p ^ K)) * hs
  have hlt : N < p ^ (N + 1) :=
    (Nat.lt_pow_self hp.one_lt (n := N)).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self N))
  rw [hpartial (N + 1), Nat.div_eq_of_lt hlt, coprimeMoebiusSet_zero, mul_zero, add_zero]

/-- A power bound for the twisted Möbius sum prime to `P`. -/
def HasCoprimeBound (P : Finset ℕ) (y : GaugeTorus) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖coprimeMoebiusSet P y N‖ ≤ C * ((N : ℝ) + 1) ^ θ

/-- **Power bounds pass through one prime**, in both directions. -/
theorem hasBound_insert_iff {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (y : GaugeTorus) {θ : ℝ} (hθ : 0 < θ) :
    HasCoprimeBound (insert p P) y θ ↔ HasCoprimeBound P y θ := by
  constructor
  · rintro ⟨D, hD, hS⟩
    refine ⟨2 * D, by positivity, fun N => ?_⟩
    have hNp : (((N / p : ℕ) : ℝ) + 1) ^ θ ≤ ((N : ℝ) + 1) ^ θ := by
      refine Real.rpow_le_rpow (by positivity) ?_ hθ.le
      have : ((N / p : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N p
      linarith
    rw [coprimeMoebiusSet_eq_split hP hp hpP y N]
    calc ‖coprimeMoebiusSet (insert p P) y N -
          twist y p * coprimeMoebiusSet (insert p P) y (N / p)‖
        ≤ ‖coprimeMoebiusSet (insert p P) y N‖ +
            ‖twist y p * coprimeMoebiusSet (insert p P) y (N / p)‖ := norm_sub_le _ _
      _ ≤ D * ((N : ℝ) + 1) ^ θ + D * ((N : ℝ) + 1) ^ θ := by
          rw [norm_mul, norm_twist, one_mul]
          exact add_le_add (hS N) ((hS _).trans (mul_le_mul_of_nonneg_left hNp hD))
      _ = 2 * D * ((N : ℝ) + 1) ^ θ := by ring
  · rintro ⟨C, hC, hS⟩
    set r : ℝ := (p : ℝ) ^ (-θ) with hr
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    have hr1 : r < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    have hinv : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
    refine ⟨C * 2 ^ θ * (1 - r)⁻¹, by positivity, fun N => ?_⟩
    have hgeom : ∑ k ∈ range (N + 1), r ^ k ≤ (1 - r)⁻¹ := by
      rw [geom_sum_eq hr1.ne, div_le_iff_of_neg (by linarith : r - 1 < 0)]
      have hne : (1 : ℝ) - r ≠ 0 := by linarith
      have hm : (1 - r)⁻¹ * (r - 1) = -1 := by
        rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ hne]
      rw [hm]
      linarith [pow_nonneg hr0 (N + 1)]
    have hK : 0 ≤ C * 2 ^ θ * ((N : ℝ) + 1) ^ θ := by positivity
    rw [coprimeMoebiusSet_insert_eq_sum hP hp hpP y N]
    calc ‖∑ k ∈ range (N + 1), twist y p ^ k * coprimeMoebiusSet P y (N / p ^ k)‖
        ≤ ∑ k ∈ range (N + 1), ‖twist y p ^ k * coprimeMoebiusSet P y (N / p ^ k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ range (N + 1), C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * r ^ k := by
          refine sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow, norm_twist, one_pow, one_mul]
          exact norm_div_pow_le (coprimeMoebiusSet_zero P y) hp hθ hC hS N k
      _ = C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * ∑ k ∈ range (N + 1), r ^ k := by rw [mul_sum]
      _ ≤ C * 2 ^ θ * ((N : ℝ) + 1) ^ θ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hK
      _ = C * 2 ^ θ * (1 - r)⁻¹ * ((N : ℝ) + 1) ^ θ := by ring

/-- **Power bounds pass through any finite set of primes.** -/
theorem hasBound_iff_of_subset (y : GaugeTorus) {θ : ℝ} (hθ : 0 < θ) :
    ∀ T : Finset ℕ, (∀ r ∈ T, r.Prime) → (HasCoprimeBound T y θ ↔ HasCoprimeBound ∅ y θ) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun _ => Iff.rfl
  | insert p T hpT ih =>
    intro hT
    have hT' : ∀ r ∈ T, r.Prime := fun r hr => hT r (mem_insert_of_mem hr)
    rw [hasBound_insert_iff hT' (hT p (mem_insert_self p T)) hpT y hθ, ih hT']

theorem gaugePowerBound_moebius_iff_hasBound {y : GaugeTorus} {θ : ℝ} :
    GaugePowerBound moebiusSource y θ ↔ HasCoprimeBound ∅ y θ := by
  rw [gaugePowerBound_moebius_iff]
  simp only [HasCoprimeBound, coprimeMoebiusSet_empty]

/-! ### The Dirichlet gauge point -/

variable {q : ℕ} [NeZero q]

/-- **The coprime sum is the twisted Mertens function.** -/
theorem coprimeMoebiusSet_primeFactors_dirichletGauge (χ : DirichletCharacter ℂ q) (N : ℕ) :
    coprimeMoebiusSet q.primeFactors (dirichletGauge χ) N =
      RHTower.partialSumSeq (↗χ * ↗μ) N := by
  classical
  rw [RHTower.partialSumSeq, sum_range_succ_eq_add_Icc]
  simp only [Pi.mul_apply, ArithmeticFunction.map_zero, Int.cast_zero, mul_zero, zero_add]
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n)]
  have hnon : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ ∀ r ∈ q.primeFactors, ¬ r ∣ n),
      (χ (n : ZMod q) : ℂ) * ((μ n : ℤ) : ℂ) = 0 := by
    refine sum_eq_zero fun n hn => ?_
    obtain ⟨-, hnr⟩ := mem_filter.mp hn
    have hncop : ¬ Nat.Coprime n q := fun h => hnr (coprime_iff_forall_primeFactors.mp h)
    rw [MulChar.map_nonunit χ fun hu => hncop ((ZMod.isUnit_iff_coprime n q).mp hu), zero_mul]
  rw [hnon, add_zero, coprimeMoebiusSet]
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hnI, hnr⟩ := mem_filter.mp hn
  rw [twist_dirichletGauge χ (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1)
    (coprime_iff_forall_primeFactors.mpr hnr), mul_comm]

/-- Power bounds at the Dirichlet gauge point are power bounds of the twisted Mertens function. -/
theorem gaugePowerBound_moebius_dirichletGauge_iff (χ : DirichletCharacter ℂ q) {θ : ℝ}
    (hθ : 0 < θ) :
    GaugePowerBound moebiusSource (dirichletGauge χ) θ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖RHTower.partialSumSeq (↗χ * ↗μ) N‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
  rw [gaugePowerBound_moebius_iff_hasBound, ← hasBound_iff_of_subset (dirichletGauge χ) hθ
    q.primeFactors fun r hr => Nat.prime_of_mem_primeFactors hr]
  simp only [HasCoprimeBound, coprimeMoebiusSet_primeFactors_dirichletGauge]

/-- A power bound on the twisted Mertens function bounds the zero abscissa. -/
theorem zeroAbscissa_le_of_partialSum_bound {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, ‖RHTower.partialSumSeq (↗χ * ↗μ) N‖ ≤ C * ((N : ℝ) + 1) ^ α) :
    RHTower.zeroAbscissa χ ≤ α := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ρ, hzero, hρ⟩ := RHTower.exists_zero_lt_re hχ hprim hlt
  -- The Hermitian square of the partial sums inherits the bound with exponent `2α + 1`.
  have hmixed := RHTower.norm_mixedAdditiveConvolutionPower_le_of_subpower hC hα hb 0
  have hupper : ∀ M : ℕ, (RHTower.mixedAdditiveConvolutionPower
      (RHTower.partialSumSeq (↗χ * ↗μ)) 1 M).re ≤ C ^ 2 * ((M : ℝ) + 1) ^ (2 * α + 1) := by
    intro M
    refine (Complex.re_le_norm _).trans ((hmixed M).trans (le_of_eq ?_))
    congr 2
    push_cast
    ring
  have hdecay := RHTower.twistedMobiusLaplaceDecay_of_mertensSubpower χ one_pos
    (by positivity) (by positivity) hupper
  have hb' : max ((2 * α + 1 + 1) / (2 * ((1 : ℕ) : ℝ)) - 1) 0 = α := by
    rw [show (2 * α + 1 + 1) / (2 * ((1 : ℕ) : ℝ)) - 1 = α by push_cast; ring]
    exact max_eq_left hα
  rw [hb'] at hdecay
  exact RHTower.not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero hχ hα hρ hzero hdecay

/-- `Θ_χ ≥ 1/2`: `L(s, χ)` has a zero with real part at least `1/2`. -/
theorem half_le_zeroAbscissa {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    1 / 2 ≤ RHTower.zeroAbscissa χ := by
  obtain ⟨ρ, hρ, hzero⟩ := RHTower.exists_LFunction_eq_zero_half_le_re hχ hprim
  exact hρ.trans (RHTower.re_le_zeroAbscissa hχ hzero)

/-- **The Dirichlet points read their zeros.** At a primitive nonprincipal Dirichlet gauge point the
Möbius exponent is the zero abscissa of `L(s, χ)`. -/
theorem gaugeExponent_moebius_dirichletGauge {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    gaugeExponent moebiusSource (dirichletGauge χ) = RHTower.zeroAbscissa χ := by
  have hΘ := half_le_zeroAbscissa hχ hprim
  refine le_antisymm ?_ ?_
  · -- The twisted Littlewood bound.
    refine gaugeExponent_le_of_forall (by linarith) fun ε hε => ?_
    obtain ⟨A, hA, hb⟩ := RHTower.twistedMertensSubpowerBound_zeroAbscissa hχ hprim ε hε
    exact (gaugePowerBound_moebius_dirichletGauge_iff χ (by linarith)).mpr ⟨A, hA.le, hb⟩
  · -- A zero right of a power bound obstructs it.
    by_contra hlt
    push Not at hlt
    obtain ⟨α, h1, h2⟩ := exists_between hlt
    have hα : 0 < α := lt_of_le_of_lt (gaugeExponent_nonneg norm_moebiusSource_le) h1
    obtain ⟨C, hC, hb⟩ := (gaugePowerBound_moebius_dirichletGauge_iff χ hα).mp
      (gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le h1)
    exact absurd (zeroAbscissa_le_of_partialSum_bound hχ hprim hα.le hC hb) (not_le.mpr h2)

/-- **The Dirichlet points are never better than typical.** -/
theorem typicalExponent_le_gaugeExponent_moebius_dirichletGauge {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    typicalExponent moebiusSource ≤ gaugeExponent moebiusSource (dirichletGauge χ) := by
  rw [typicalExponent_moebius_eq_half, gaugeExponent_moebius_dirichletGauge hχ hprim]
  exact half_le_zeroAbscissa hχ hprim

/-- **GRH for `χ` is the typicality of its Dirichlet point.** -/
theorem dirichletGRH_iff_dirichletGauge_typical {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    RHTower.DirichletGRH χ ↔
      gaugeExponent moebiusSource (dirichletGauge χ) = typicalExponent moebiusSource := by
  rw [gaugeExponent_moebius_dirichletGauge hχ hprim, typicalExponent_moebius_eq_half]
  exact (RHTower.zeroAbscissa_eq_half_iff_dirichletGRH hχ hprim).symm

/-- The whole vertical line through a Dirichlet point reads `Θ_χ`. -/
theorem gaugeExponent_moebius_dirichletGauge_verticalShift {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) :
    gaugeExponent moebiusSource (dirichletGauge χ + verticalShift t) = RHTower.zeroAbscissa χ := by
  rw [gaugeExponent_add_verticalShift norm_moebiusSource_le,
    gaugeExponent_moebius_dirichletGauge hχ hprim]

end GaloisForLFunctions.ArithmeticGaugeTheory
