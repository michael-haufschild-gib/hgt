import GaloisForLFunctions.BezoutValuationIncidence.TheHypercubeDirichletFormDivergesBelowHalfDamping
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsATailPhenomenon
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.LocalEulerFactorsAndPronicDilationContraction
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros

/-!
# The natural-cutoff dilation form is the receiver

Truncating the Möbius row by prime support gives the hypercube form, which diverges below half
damping (`TheHypercubeDirichletFormDivergesBelowHalfDamping`). Truncating by size gives the
natural-cutoff form
`D^{nat}_{r,ε}(N) = ∑_{d₁,d₂ ≤ N} μ(d₁)μ(d₂)(d₁d₂)^{-1/2-ε} Φ_r(d₁/d₂)`, the pronic energy of
`Ψ_N(n) = ∑_{d ≤ N} μ(d)d^{-ε} C_r(⌊n/d⌋)`. Below its horizon this primitive is a finite
combination of dilated receivers, `A_ε` the centred damped divisor prefix:

`Ψ_N(n) = ∑_{ab = r} a μ(b) (α_ε ⌊n/a⌋ + A_ε(⌊n/a⌋))` for `n ≤ N`
(`naturalDilationPrimitive_eq`).

* Admission at `ε` bounds the head energy `∑_{n ≤ N} Ψ_N(n)²/(n(n+1))` uniformly in `N` for every
  core `r > 1`, by the pronic dilation contraction `‖f(⌊·/a⌋)‖ ≤ a^{-1/2}‖f‖`
  (`bounded_naturalDilationHeadEnergy_of_mem_receiverDampings`).
* For a prime core `p` the primitive is `p A_ε(⌊n/p⌋) - A_ε(n)` plus a bounded term: the local
  factor `1 - p·p^{-s}`, whose zero `s = 1` lies right of the critical line. Exact block dilation
  gives `√p ‖A_ε‖_M ≤ K + ‖A_ε‖_{pM+p-1}`; the sub-linear growth `E_T(ε) = O(1 + T^{1-2ε})` rules
  out the linear mode, so iterating backwards bounds the receiver
  (`mem_receiverDampings_of_bounded_naturalDilationHeadEnergy`).

So the head of the natural form is bounded exactly at the admitted dampings
(`bounded_naturalDilationHeadEnergy_iff_mem_receiverDampings`); a cutoff-uniform bound on the
natural form at one damping is admission, and on an interval of dampings a zero-free strip
(`re_le_of_bounded_naturalDilationDirichletForm_on_Ioo`).
-/

open Filter Topology Finset
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics renaming pronicNorm → pnorm,
  pronicNorm_add_le → pnorm_add_le, pronicNorm_nonneg → pnorm_nonneg,
  pronicNorm_smul → pnorm_smul, pronicNorm_le_of_abs_le → pnorm_le_of_abs_le,
  pronicNorm_dilate_le → pnorm_dilate_le
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The natural-cutoff primitive in receiver coordinates -/

/-- The natural-cutoff dilation Dirichlet form over the scales `d ≤ N`. -/
def naturalDilationDirichletForm (ε : ℝ) (N r : ℕ) (hr : 1 < r) : ℝ :=
  signedDilationDirichletForm moebiusReal ε (Icc 1 N) r hr

/-- Its primitive `Ψ_N(n) = ∑_{d ≤ N} μ(d)d^{-ε} C_r(⌊n/d⌋)`. -/
def naturalDilationPrimitive (ε : ℝ) (N r n : ℕ) : ℝ :=
  signedDilationPrimitive moebiusReal ε (Icc 1 N) r n

/-- The real Ramanujan primitive in floor coordinates: `C_r(m) = ∑_{ab = r} a μ(b) ⌊m/a⌋`. -/
theorem pmRamanujanPrimitive_re_eq_floor (r m : ℕ) :
    (pmRamanujanPrimitive r m).re =
      ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 * ((m / x.1 : ℕ) : ℝ) := by
  rw [pmRamanujanPrimitive_eq_floor, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [moebiusReal, Complex.mul_re]

/-- Below the cutoff the damped floor sum is the damped divisor prefix:
`∑_{d ≤ N} μ(d)d^{-ε}⌊m/d⌋ = α_ε m + A_ε(m)` for `m ≤ N`. -/
theorem sum_Icc_moebiusReal_rpow_floor_eq {ε : ℝ} {m N : ℕ} (hmN : m ≤ N) :
    ∑ d ∈ Icc 1 N, moebiusReal d * (d : ℝ) ^ (-ε) * ((m / d : ℕ) : ℝ) =
      (pmPowerDampedDivisorDensity ε).re * m + pmPowerDampedCenteredDivisorPrefix ε m := by
  have hsub : ∑ d ∈ Icc 1 N, moebiusReal d * (d : ℝ) ^ (-ε) * ((m / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 m, moebiusReal d * (d : ℝ) ^ (-ε) * ((m / d : ℕ) : ℝ) := by
    symm
    refine Finset.sum_subset (Icc_subset_Icc le_rfl hmN) fun d hd hdm => ?_
    have hlt : m < d := by
      simp only [mem_Icc, not_and, not_le] at hd hdm
      exact hdm hd.1
    rw [Nat.div_eq_of_lt hlt]
    simp
  rw [hsub, ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_eq_floor_sum]
  simp only [moebiusReal]
  ring

/-- **The natural primitive below its horizon.** For `n ≤ N`,
`Ψ_N(n) = ∑_{ab = r} a μ(b) (α_ε ⌊n/a⌋ + A_ε(⌊n/a⌋))`: the natural cutoff commutes with the
floor expansion of `C_r`, and each floor sum is the damped divisor prefix. -/
theorem naturalDilationPrimitive_eq (ε : ℝ) (r : ℕ) {N n : ℕ} (hn : n ≤ N) :
    naturalDilationPrimitive ε N r n =
      ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 *
        ((pmPowerDampedDivisorDensity ε).re * ((n / x.1 : ℕ) : ℝ) +
          pmPowerDampedCenteredDivisorPrefix ε (n / x.1)) := by
  rw [naturalDilationPrimitive, signedDilationPrimitive]
  simp_rw [pmRamanujanPrimitive_re_eq_floor, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_Icc_moebiusReal_rpow_floor_eq (le_trans (Nat.div_le_self n x.1) hn), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d x.1]
  ring

/-- For a prime core the natural primitive is the local factor `1 - p·p^{-s}` applied to the
receiver: `Ψ_N(n) = p A_ε(⌊n/p⌋) - A_ε(n) + α_ε (p⌊n/p⌋ - n)` for `n ≤ N`. -/
theorem naturalDilationPrimitive_prime_eq (ε : ℝ) {p : ℕ} (hp : p.Prime) {N n : ℕ} (hn : n ≤ N) :
    naturalDilationPrimitive ε N p n =
      p * pmPowerDampedCenteredDivisorPrefix ε (n / p) - pmPowerDampedCenteredDivisorPrefix ε n +
        (pmPowerDampedDivisorDensity ε).re * (p * ((n / p : ℕ) : ℝ) - n) := by
  rw [naturalDilationPrimitive_eq ε p hn, Nat.sum_divisorsAntidiagonal
      (fun a b => (a : ℝ) * moebiusReal b * ((pmPowerDampedDivisorDensity ε).re *
        ((n / a : ℕ) : ℝ) + pmPowerDampedCenteredDivisorPrefix ε (n / a))),
    hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp only [Nat.div_self hp.pos, Nat.div_one, moebiusReal_one', moebiusReal_of_prime hp]
  push_cast
  ring

/-! ## §2. Admission bounds the natural head energy -/

/-- The pronic norm only sees the window `1 ≤ n ≤ T`. -/
theorem pnorm_congr {f g : ℕ → ℝ} {T : ℕ} (h : ∀ n ∈ Icc 1 T, f n = g n) :
    pnorm f T = pnorm g T := by
  unfold TransHorizonIncidenceMechanics.pronicNorm
  rw [Finset.sum_congr rfl fun n hn => by rw [h n hn]]

/-- Minkowski's inequality for finite sums in the pronic norm. -/
theorem pnorm_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℝ) (T : ℕ) :
    pnorm (fun n => ∑ i ∈ s, F i n) T ≤ ∑ i ∈ s, pnorm (F i) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TransHorizonIncidenceMechanics.pronicNorm]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (pnorm_add_le _ _ T).trans (add_le_add le_rfl ih)

/-- The receiver energy is the square of the pronic norm of the centred prefix. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_sq_pronicNorm (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      pnorm (pmPowerDampedCenteredDivisorPrefix ε) T ^ 2 := by
  rw [TransHorizonIncidenceMechanics.pronicNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => by positivity)]
  rfl

/-- **Admission bounds the natural head.** If the receiver is admitted at `ε`, then for every core
`r > 1` the head of the natural primitive has pronic norm bounded uniformly in the cutoff. -/
theorem bounded_naturalDilationHeadEnergy_of_mem_receiverDampings {ε : ℝ}
    (hε : ε ∈ receiverDampings) {r : ℕ} (hr : 1 < r) :
    ∃ K : ℝ, ∀ N : ℕ, pnorm (naturalDilationPrimitive ε N r) N ≤ K := by
  obtain ⟨-, B, hB⟩ := hε
  set A := pmPowerDampedCenteredDivisorPrefix ε
  set α := (pmPowerDampedDivisorDensity ε).re
  set G : ℕ → ℝ := fun n => α * (pmRamanujanPrimitive r n).re +
    ∑ x ∈ r.divisorsAntidiagonal, (x.1 : ℝ) * moebiusReal x.2 * A (n / x.1)
  have hG : ∀ N : ℕ, ∀ n ∈ Icc 1 N, naturalDilationPrimitive ε N r n = G n := by
    intro N n hn
    rw [naturalDilationPrimitive_eq ε r (mem_Icc.mp hn).2]
    simp only [G, pmRamanujanPrimitive_re_eq_floor, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  have hA0 : A 0 = 0 := by simp [A]
  have hAB : ∀ N : ℕ, pnorm A N ≤ Real.sqrt (max B 0) := fun N => by
    rw [TransHorizonIncidenceMechanics.pronicNorm]
    refine Real.sqrt_le_sqrt ((hB N).trans (le_max_left _ _))
  refine ⟨|α| * pmRamanujanPrimitiveBound r +
    (∑ x ∈ r.divisorsAntidiagonal, |(x.1 : ℝ) * moebiusReal x.2| * (x.1 : ℝ) ^ (-(1 / 2 : ℝ))) *
      Real.sqrt (max B 0), fun N => ?_⟩
  rw [pnorm_congr (hG N)]
  refine (pnorm_add_le _ _ N).trans (add_le_add ?_ ?_)
  · rw [pnorm_smul]
    exact mul_le_mul_of_nonneg_left (pnorm_le_of_abs_le
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (fun n => (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr n)) N)
      (abs_nonneg _)
  · refine (pnorm_finsetSum_le _ _ N).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    have hx1 : 1 ≤ x.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    rw [pnorm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((pnorm_dilate_le A hA0 hx1 N).trans
      (mul_le_mul_of_nonneg_left (hAB N) (by positivity))) (abs_nonneg _)

/-! ## §3. A bounded prime-core head forces admission -/

/-- **Exact block dilation.** For `f(0) = 0` and `p ≥ 1`, on the complete blocks
`n ≤ pM + p - 1`: `∑ f(⌊n/p⌋)²/(n(n+1)) = p⁻¹ ∑_{k ≤ M} f(k)²/(k(k+1))`, since
`∑_{n = pk}^{pk+p-1} 1/(n(n+1)) = 1/(pk(k+1))`. -/
theorem sum_pronic_dilate_block_eq (f : ℕ → ℝ) (hf0 : f 0 = 0) {p : ℕ} (hp : 1 ≤ p) (M : ℕ) :
    ∑ n ∈ Icc 1 (p * M + (p - 1)), f (n / p) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      (1 / (p : ℝ)) * ∑ k ∈ Icc 1 M, f k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  induction M with
  | zero =>
    rw [Finset.sum_eq_zero fun n hn => by
      rw [Nat.div_eq_of_lt (by have := (mem_Icc.mp hn).2; omega), hf0]; simp]
    simp
  | succ M ih =>
    have hsplit : Icc 1 (p * (M + 1) + (p - 1)) =
        Icc 1 (p * M + (p - 1)) ∪ Ico (p * M + p) (p * M + p + p) := by
      ext n
      simp only [mem_union, mem_Icc, mem_Ico, mul_add, mul_one]
      omega
    have hdisj : Disjoint (Icc 1 (p * M + (p - 1))) (Ico (p * M + p) (p * M + p + p)) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [mem_Icc, mem_Ico] at h1 h2
      omega
    have hblock : ∑ n ∈ Ico (p * M + p) (p * M + p + p),
        f (n / p) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
          f (M + 1) ^ 2 / ((p : ℝ) * (((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) + 1))) := by
      have hdiv : ∀ n ∈ Ico (p * M + p) (p * M + p + p), n / p = M + 1 := by
        intro n hn
        simp only [mem_Ico] at hn
        refine Nat.div_eq_of_lt_le ?_ ?_
        · rw [add_mul, one_mul, mul_comm]; omega
        · rw [add_mul, add_mul, one_mul, mul_comm]; omega
      rw [Finset.sum_congr rfl fun n hn => by
        rw [hdiv n hn, div_eq_mul_one_div (f (M + 1) ^ 2)], ← Finset.mul_sum,
        sum_Ico_reciprocal_pronic (by positivity) (by omega)]
      push_cast
      field_simp
      ring
    have hdiv3 : ∀ a b c : ℝ, a / (b * c) = 1 / b * (a / c) := fun a b c => by
      rw [one_div_mul_eq_div, div_div, mul_comm c b]
    rw [hsplit, Finset.sum_union hdisj, ih, hblock, Finset.sum_Icc_succ_top (by omega),
      hdiv3 (f (M + 1) ^ 2) (p : ℝ) (((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) + 1)), ← mul_add]

/-- The iterated block map `M ↦ pM + p - 1` multiplies `M + 1` by `p`. -/
private theorem iterate_block_add_one {p : ℕ} (hp : 1 ≤ p) (k M : ℕ) :
    (fun m => p * m + (p - 1))^[k] M + 1 = p ^ k * (M + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc p * (fun m => p * m + (p - 1))^[k] M + (p - 1) + 1
        = p * ((fun m => p * m + (p - 1))^[k] M + 1) := by
          rw [mul_add, mul_one]; omega
      _ = p ^ k * p * (M + 1) := by rw [ih]; ring

/-- **A bounded prime-core head forces admission.** For a prime `p` and `ε > 0`, if the head of
the natural primitive with core `p` has pronic norm bounded uniformly in the cutoff, then the
receiver is admitted at `ε`. -/
theorem mem_receiverDampings_of_bounded_naturalDilationHeadEnergy {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε)
    (hK : ∃ K : ℝ, ∀ N : ℕ, pnorm (naturalDilationPrimitive ε N p) N ≤ K) :
    ε ∈ receiverDampings := by
  rcases le_or_gt (1 / 2) ε with hε | hε
  · exact Ici_half_subset_receiverDampings hε
  obtain ⟨K, hK⟩ := hK
  obtain ⟨D, hD0, hD⟩ := ArithmeticCompensationTheory.exists_dampedMobiusEnergy_le hε0 hε
  set A := pmPowerDampedCenteredDivisorPrefix ε
  set α := (pmPowerDampedDivisorDensity ε).re
  set f : ℕ → ℝ := fun M => pnorm A M
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsp : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hpR
  have hA0 : A 0 = 0 := by simp [A]
  have hK0 : 0 ≤ K := (pnorm_nonneg _ 0).trans (hK 0)
  set K₁ := K + |α| * p
  -- one block step: `√p ‖A‖_M ≤ K₁ + ‖A‖_{pM+p-1}`
  have hstep : ∀ M : ℕ, Real.sqrt p * f M ≤ K₁ + f (p * M + (p - 1)) := by
    intro M
    set T := p * M + (p - 1)
    have hnorm : pnorm (fun n => (p : ℝ) * A (n / p)) T = Real.sqrt p * f M := by
      have hps : (p : ℝ) * Real.sqrt (1 / (p : ℝ)) = Real.sqrt p := by
        rw [one_div, Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]
      rw [pnorm_smul (p : ℝ) (fun n => A (n / p)), abs_of_pos (by positivity : (0 : ℝ) < p),
        TransHorizonIncidenceMechanics.pronicNorm, sum_pronic_dilate_block_eq A hA0 hp1 M,
        Real.sqrt_mul (by positivity),
        ← mul_assoc, hps]
      rfl
    have hpt : ∀ n ∈ Icc 1 T, (p : ℝ) * A (n / p) =
        naturalDilationPrimitive ε T p n + A n +
          (-α) * ((p : ℝ) * ((n / p : ℕ) : ℝ) - n) := by
      intro n hn
      rw [naturalDilationPrimitive_prime_eq ε hp (mem_Icc.mp hn).2]
      ring
    have hc : pnorm (fun n => (-α) * ((p : ℝ) * ((n / p : ℕ) : ℝ) - n)) T ≤ |α| * p := by
      rw [pnorm_smul, abs_neg]
      refine mul_le_mul_of_nonneg_left (pnorm_le_of_abs_le (by positivity) (fun n => ?_) T)
        (abs_nonneg _)
      have h1 : (p : ℝ) * ((n / p : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n p
      have h2' : n < n / p * p + p := Nat.lt_div_mul_add (by omega)
      have h2 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h2'
      rw [abs_le]
      constructor <;> linarith
    rw [← hnorm, pnorm_congr hpt]
    calc pnorm (fun n => naturalDilationPrimitive ε T p n + A n +
          (-α) * ((p : ℝ) * ((n / p : ℕ) : ℝ) - n)) T
        ≤ pnorm (fun n => naturalDilationPrimitive ε T p n + A n) T +
            pnorm (fun n => (-α) * ((p : ℝ) * ((n / p : ℕ) : ℝ) - n)) T :=
          pnorm_add_le _ _ T
      _ ≤ (K + f T) + |α| * p :=
          add_le_add ((pnorm_add_le _ _ T).trans (add_le_add (hK T) le_rfl)) hc
      _ = K₁ + f T := by ring
  -- the fixed point `L = K₁/(√p - 1)` of `x ↦ (K₁ + x)/√p` dominates every `‖A‖_M`
  set q : ℝ := (Real.sqrt p)⁻¹
  set L : ℝ := K₁ / (Real.sqrt p - 1)
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hL0 : 0 ≤ L := div_nonneg (add_nonneg hK0 (by positivity)) (by linarith)
  set g : ℕ → ℝ := fun M => f M - L
  have hs0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs1 : Real.sqrt p - 1 ≠ 0 := (sub_pos.mpr hsp).ne'
  have hLfix : q * K₁ = L - q * L := by
    simp only [L, q]
    field_simp
  have hgstep : ∀ M : ℕ, g M ≤ q * g (p * M + (p - 1)) := by
    intro M
    have hfM : f M ≤ q * (K₁ + f (p * M + (p - 1))) :=
      (le_inv_mul_iff₀ (by linarith)).mpr (hstep M)
    simp only [g]
    rw [mul_add] at hfM
    rw [mul_sub]
    linarith
  have hiter : ∀ k M : ℕ, g M ≤ q ^ k * g ((fun m => p * m + (p - 1))^[k] M) := by
    intro k
    induction k with
    | zero => intro M; simp
    | succ k ih =>
      intro M
      refine (ih M).trans ?_
      rw [Function.iterate_succ_apply', pow_succ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hgstep _) (by positivity)
  -- the energy growth `E_T = O(1 + T^{1-2ε})` sends `q^k ‖A‖_{M_k}` to zero
  have hgle : ∀ M : ℕ, g M ≤ 0 := by
    intro M
    set c : ℝ := ((M : ℝ) + 1) ^ (1 - 2 * ε) with hc
    have hlim : Tendsto (fun k : ℕ => Real.sqrt (D * ((1 / (p : ℝ)) ^ k +
        ((p : ℝ) ^ (-(2 * ε))) ^ k * c))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => (1 / (p : ℝ)) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one (by linarith)).mpr hpR)
      have h2 : Tendsto (fun k : ℕ => ((p : ℝ) ^ (-(2 * ε))) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))
      have h3 := ((h1.add (h2.mul_const c)).const_mul D).sqrt
      simpa using h3
    refine ge_of_tendsto' hlim fun k => ?_
    set Mk := (fun m => p * m + (p - 1))^[k] M
    have hMk : (Mk : ℝ) + 1 = (p : ℝ) ^ k * ((M : ℝ) + 1) := by
      exact_mod_cast iterate_block_add_one hp1 k M
    refine (hiter k M).trans ?_
    have hfk : q ^ k * g Mk ≤ q ^ k * f Mk :=
      mul_le_mul_of_nonneg_left (by simp only [g]; linarith) (by positivity)
    refine hfk.trans ?_
    rw [← Real.sqrt_sq (mul_nonneg (by positivity) (pnorm_nonneg _ _) : 0 ≤ q ^ k * f Mk)]
    refine Real.sqrt_le_sqrt ?_
    have hE : f Mk ^ 2 ≤ D * (1 + (Mk : ℝ) ^ (1 - 2 * ε)) := by
      rw [show f Mk ^ 2 = pmPowerDampedDivisorDiscreteEnergy ε Mk from
        (pmPowerDampedDivisorDiscreteEnergy_eq_sq_pronicNorm ε Mk).symm]
      exact hD Mk
    have hq2 : (q ^ k) ^ 2 = (1 / (p : ℝ)) ^ k := by
      simp only [q]
      rw [← pow_mul, mul_comm k 2, pow_mul, inv_pow, Real.sq_sqrt (by positivity), one_div]
    have hgrow : (Mk : ℝ) ^ (1 - 2 * ε) ≤ ((p : ℝ) ^ k) ^ (1 - 2 * ε) * c := by
      rw [hc, ← Real.mul_rpow (by positivity) (by positivity), ← hMk]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hpk : (1 / (p : ℝ)) ^ k * ((p : ℝ) ^ k) ^ (1 - 2 * ε) = ((p : ℝ) ^ (-(2 * ε))) ^ k := by
      rw [← Real.rpow_natCast_mul (by positivity), mul_comm (k : ℝ),
        Real.rpow_mul_natCast (by positivity), ← mul_pow]
      congr 1
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
      congr 1
      ring
    calc (q ^ k * f Mk) ^ 2 = (1 / (p : ℝ)) ^ k * f Mk ^ 2 := by rw [mul_pow, hq2]
      _ ≤ (1 / (p : ℝ)) ^ k * (D * (1 + (Mk : ℝ) ^ (1 - 2 * ε))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (1 / (p : ℝ)) ^ k * (D * (1 + ((p : ℝ) ^ k) ^ (1 - 2 * ε) * c)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hD0) (by positivity)
      _ = D * ((1 / (p : ℝ)) ^ k + ((1 / (p : ℝ)) ^ k * ((p : ℝ) ^ k) ^ (1 - 2 * ε)) * c) := by
          ring
      _ = D * ((1 / (p : ℝ)) ^ k + ((p : ℝ) ^ (-(2 * ε))) ^ k * c) := by rw [hpk]
  refine ⟨hε0, L ^ 2, fun T => ?_⟩
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sq_pronicNorm]
  exact pow_le_pow_left₀ (pnorm_nonneg _ _) (by have := hgle T; simp only [g] at this; linarith) 2

/-! ## §4. The natural form at the receiver -/

/-- **The natural head is the receiver.** For a prime core `p` and `ε > 0`, the head of the
natural-cutoff primitive is bounded uniformly in the cutoff iff the receiver is admitted. -/
theorem bounded_naturalDilationHeadEnergy_iff_mem_receiverDampings {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε) :
    (∃ K : ℝ, ∀ N : ℕ, pnorm (naturalDilationPrimitive ε N p) N ≤ K) ↔
      ε ∈ receiverDampings :=
  ⟨mem_receiverDampings_of_bounded_naturalDilationHeadEnergy hp hε0,
    fun h => bounded_naturalDilationHeadEnergy_of_mem_receiverDampings h hp.one_lt⟩

/-- The head energy is a window of the natural form, so it is bounded by it. -/
theorem pnorm_naturalDilationPrimitive_sq_le (ε : ℝ) (N : ℕ) {r : ℕ} (hr : 1 < r) :
    pnorm (naturalDilationPrimitive ε N r) N ^ 2 ≤ naturalDilationDirichletForm ε N r hr := by
  rw [TransHorizonIncidenceMechanics.pronicNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => by positivity),
    show Icc 1 N = Ico 1 (N + 1) by ext n; simp only [mem_Icc, mem_Ico]; omega]
  exact sum_Ico_signedDilationPrimitive_sq_le moebiusReal ε
    (fun d hd => (mem_Icc.mp hd).1) hr le_rfl

/-- **A natural-cutoff bound is admission.** For a prime core `p` and `ε > 0`, a bound on the
natural-cutoff dilation form uniform in the cutoff gives `ε ∈ receiverDampings`. -/
theorem mem_receiverDampings_of_bounded_naturalDilationDirichletForm {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε)
    (hB : ∃ B : ℝ, ∀ N : ℕ, naturalDilationDirichletForm ε N p hp.one_lt ≤ B) :
    ε ∈ receiverDampings := by
  obtain ⟨B, hB⟩ := hB
  refine mem_receiverDampings_of_bounded_naturalDilationHeadEnergy hp hε0
    ⟨Real.sqrt (max B 0), fun N => ?_⟩
  rw [← Real.sqrt_sq (pnorm_nonneg _ _)]
  exact Real.sqrt_le_sqrt
    ((pnorm_naturalDilationPrimitive_sq_le ε N hp.one_lt).trans ((hB N).trans (le_max_left _ _)))

/-- **On a band of dampings the natural form gives a zero-free strip.** If for a prime core `p`
the natural-cutoff form is bounded uniformly in the cutoff at every damping of `(a, b)`,
`0 ≤ a < b`, then every zero of `ζ` in the critical strip has real part `≤ 1/2 + a`. -/
theorem re_le_of_bounded_naturalDilationDirichletForm_on_Ioo {p : ℕ} (hp : p.Prime) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hB : ∀ ε ∈ Set.Ioo a b, ∃ B : ℝ, ∀ N : ℕ, naturalDilationDirichletForm ε N p hp.one_lt ≤ B)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) :
    ρ.re ≤ 1 / 2 + a :=
  re_le_of_Ioo_subset_receiverDampings hab
    (fun ε hε => mem_receiverDampings_of_bounded_naturalDilationDirichletForm hp
      (ha.trans_lt hε.1) (hB ε hε)) hzero hρ1

end

end GaloisForLFunctions.BezoutValuationIncidence
