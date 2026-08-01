import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.RHTower.MobiusFinitePrimeApertureSourceConsumption

/-!
# Exponential-Gibbs boundary laws for the Möbius source

This module records unconditional finite-section infrastructure for Route E.  A finite prime
aperture is evaluated at the all-minus Boolean character.  Adjoining a prime acts by the literal
dilation difference `I - T_p`, while every Taylor jet is an explicit product of local
amplification factors.  These identities explain why fixed-aperture contraction cannot supply the
open all-prime Möbius cancellation source.

No cancellation estimate, zero-free hypothesis, or form of RH is assumed here.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Product represented by one Boolean prime subset; the empty subset represents `1`. -/
def finitePrimeSubsetProduct (T : Finset ℕ) : ℕ :=
  ∏ p ∈ T, p

/-- Finite squarefree exponential partition evaluated at the all-minus prime character. -/
def finitePrimeParityPartition (P : Finset ℕ) (w : ℂ) : ℂ :=
  ∑ T ∈ P.powerset,
    (-1 : ℂ) ^ T.card * Complex.exp (-((finitePrimeSubsetProduct T : ℕ) : ℂ) * w)

/-- Algebraic `m`-th Taylor moment of the finite all-minus partition. -/
def finitePrimeParityMoment (P : Finset ℕ) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m *
    ∑ T ∈ P.powerset,
      (-1 : ℂ) ^ T.card * ∏ p ∈ T, ((p : ℂ) ^ m)

/-- Boolean inclusion--exclusion factors every finite parity moment into local prime factors. -/
theorem finitePrimeParityMoment_eq_prod (P : Finset ℕ) (m : ℕ) :
    finitePrimeParityMoment P m =
      (-1 : ℂ) ^ m * ∏ p ∈ P, (1 - (p : ℂ) ^ m) := by
  rw [finitePrimeParityMoment]
  congr 1
  simpa using
    (Finset.prod_sub (fun _ : ℕ => (1 : ℂ)) (fun p : ℕ => (p : ℂ) ^ m) P).symm

/-- Every genuine analytic Taylor jet equals the explicit Boolean parity moment. -/
theorem iteratedDeriv_finitePrimeParityPartition_zero
    (P : Finset ℕ) (m : ℕ) :
    iteratedDeriv m (finitePrimeParityPartition P) 0 =
      finitePrimeParityMoment P m := by
  change iteratedDeriv m (fun w : ℂ =>
    ∑ T ∈ P.powerset,
      (-1 : ℂ) ^ T.card *
        Complex.exp (-((finitePrimeSubsetProduct T : ℕ) : ℂ) * w)) 0 = _
  rw [HurwitzExp.iteratedDeriv_finset_sum P.powerset m
    (fun T _ => contDiff_const.mul
      (HurwitzExp.contDiff_expLin (-((finitePrimeSubsetProduct T : ℕ) : ℂ)))) 0]
  simp only [iteratedDeriv_const_mul_field, HurwitzExp.iteratedDeriv_expLin,
    mul_zero, Complex.exp_zero, mul_one]
  rw [finitePrimeParityMoment]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [neg_pow]
  simp only [finitePrimeSubsetProduct]
  push_cast
  rw [Finset.prod_pow]
  ring

/-- Closed all-order jet formula for a finite prime aperture. -/
theorem iteratedDeriv_finitePrimeParityPartition_zero_eq_prod
    (P : Finset ℕ) (m : ℕ) :
    iteratedDeriv m (finitePrimeParityPartition P) 0 =
      (-1 : ℂ) ^ m * ∏ p ∈ P, (1 - (p : ℂ) ^ m) := by
  rw [iteratedDeriv_finitePrimeParityPartition_zero,
    finitePrimeParityMoment_eq_prod]

/-- Adjoining one new prime applies the exact dilation difference `I - T_p`. -/
theorem finitePrimeParityPartition_insert
    (P : Finset ℕ) {p : ℕ} (hp : p ∉ P) (w : ℂ) :
    finitePrimeParityPartition (insert p P) w =
      finitePrimeParityPartition P w -
        finitePrimeParityPartition P ((p : ℂ) * w) := by
  rw [finitePrimeParityPartition, Finset.sum_powerset_insert hp]
  rw [finitePrimeParityPartition, finitePrimeParityPartition]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T hTP
  have hpT : p ∉ T := fun h => hp (Finset.mem_of_subset (Finset.mem_powerset.mp hTP) h)
  rw [Finset.card_insert_of_notMem hpT, pow_succ]
  simp only [finitePrimeSubsetProduct, Finset.prod_insert hpT]
  push_cast
  have hexp :
      (-((p : ℂ) * ∏ q ∈ T, (q : ℂ))) * w =
        (-(∏ q ∈ T, (q : ℂ))) * ((p : ℂ) * w) := by ring
  rw [hexp]
  ring

/-- A new prime multiplies the `m`-th finite-section jet by `1-p^m`. -/
theorem finitePrimeParityMoment_insert
    (P : Finset ℕ) {p m : ℕ} (hp : p ∉ P) :
    finitePrimeParityMoment (insert p P) m =
      (1 - (p : ℂ) ^ m) * finitePrimeParityMoment P m := by
  rw [finitePrimeParityMoment_eq_prod, finitePrimeParityMoment_eq_prod]
  rw [Finset.prod_insert hp]
  ring

/-- At positive jet order a genuine prime is an amplifier in norm, never a strict contraction. -/
theorem norm_finitePrimeParityMoment_insert
    (P : Finset ℕ) {p m : ℕ} (hp : p ∉ P) (hpPrime : p.Prime) (hm : 0 < m) :
    ‖finitePrimeParityMoment (insert p P) m‖ =
      ((p : ℝ) ^ m - 1) * ‖finitePrimeParityMoment P m‖ := by
  rw [finitePrimeParityMoment_insert P hp, norm_mul]
  have hpPow : (1 : ℝ) < (p : ℝ) ^ m := by
    exact one_lt_pow₀ (by exact_mod_cast hpPrime.one_lt) hm.ne'
  have hnorm : ‖(1 : ℂ) - (p : ℂ) ^ m‖ = (p : ℝ) ^ m - 1 := by
    rw [← ofReal_one, ← ofReal_natCast, ← ofReal_pow, ← ofReal_sub, norm_real,
      Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hpPow)]
    ring
  rw [hnorm]

/-- Term of the Möbius--Laplace transform retained by the canonical prime aperture through `Y`. -/
def finitePrimeApertureMobiusLaplaceTerm (Y : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture Y) n *
    Complex.exp (-((n : ℝ) * x : ℝ))

/-- Exponential Möbius sum whose squarefree support uses only primes at most `Y`. -/
def finitePrimeApertureMobiusLaplaceTransform (Y : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, finitePrimeApertureMobiusLaplaceTerm Y x n

theorem norm_finitePrimeApertureMobiusCoefficient_le_one (Y n : ℕ) :
    ‖finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture Y) n‖ ≤ 1 := by
  rw [finitePrimeApertureMobiusCoefficient]
  split_ifs
  · exact norm_mobiusComplexCoefficient_le_one n
  · simp

theorem summable_finitePrimeApertureMobiusLaplaceTerm
    (Y : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (finitePrimeApertureMobiusLaplaceTerm Y x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_exp_neg 0 hx)
  rw [finitePrimeApertureMobiusLaplaceTerm, norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right
    (norm_finitePrimeApertureMobiusCoefficient_le_one Y n) hexp

/-- Aperture coverage makes every Laplace term through `Y` literally equal to the full term. -/
theorem finitePrimeApertureMobiusLaplaceTerm_eq_of_le
    {Y n : ℕ} (hn : n ≤ Y) (x : ℝ) :
    finitePrimeApertureMobiusLaplaceTerm Y x n =
      mobiusDiscreteLaplaceTerm x n := by
  rw [finitePrimeApertureMobiusLaplaceTerm, mobiusDiscreteLaplaceTerm]
  rw [finitePrimeApertureMobiusCoefficient_eq_of_covers
    (S := mobiusFinitePrimeAperture Y) (N := Y) (n := n) Finset.Subset.rfl hn]
  rfl

theorem norm_mobiusLaplaceTerm_sub_finiteAperture_le
    (Y n : ℕ) (x : ℝ) :
    ‖mobiusDiscreteLaplaceTerm x n - finitePrimeApertureMobiusLaplaceTerm Y x n‖ ≤
      Real.exp (-((n : ℝ) * x)) := by
  rw [mobiusDiscreteLaplaceTerm, finitePrimeApertureMobiusLaplaceTerm, ← sub_mul, norm_mul,
    Complex.norm_exp]
  have hcoeff :
      ‖mobiusComplexCoefficient n -
        finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture Y) n‖ ≤ 1 := by
    rw [finitePrimeApertureMobiusCoefficient]
    split_ifs
    · simp
    · simpa using norm_mobiusComplexCoefficient_le_one n
  exact mul_le_of_le_one_left (Real.exp_pos _).le hcoeff

theorem summable_mobiusLaplaceTerm_sub_finiteAperture
    (Y : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ =>
      mobiusDiscreteLaplaceTerm x n - finitePrimeApertureMobiusLaplaceTerm Y x n) :=
  (summable_mobiusDiscreteLaplaceTerm hx).sub
    (summable_finitePrimeApertureMobiusLaplaceTerm Y hx)

/-- Closed geometric value of the exponential tail after the first `K` integer frequencies. -/
theorem tsum_exp_neg_nat_add (x : ℝ) (K : ℕ) (hx : 0 < x) :
    (∑' n : ℕ, Real.exp (-(((n + K : ℕ) : ℝ) * x))) =
      Real.exp (-((K : ℝ) * x)) / (1 - Real.exp (-x)) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc
    (∑' n : ℕ, Real.exp (-(((n + K : ℕ) : ℝ) * x))) =
        ∑' n : ℕ, Real.exp (-x) ^ K * Real.exp (-x) ^ n := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      congr 1
      ring
    _ = Real.exp (-x) ^ K * ∑' n : ℕ, Real.exp (-x) ^ n := by
      rw [tsum_mul_left]
    _ = Real.exp (-x) ^ K * (1 - Real.exp (-x))⁻¹ := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = Real.exp (-((K : ℝ) * x)) / (1 - Real.exp (-x)) := by
      rw [← Real.exp_nat_mul]
      simp only [div_eq_mul_inv]
      congr 1
      congr 1
      ring

/-- Exact absolute tail bound for a finite prime aperture.  The aperture error starts only after
`Y`, because every integer through `Y` has all prime factors in the aperture. -/
theorem norm_mobiusLaplace_sub_finitePrimeAperture_le
    (Y : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖mobiusDiscreteLaplaceTransform x -
        finitePrimeApertureMobiusLaplaceTransform Y x‖ ≤
      Real.exp (-(((Y + 1 : ℕ) : ℝ) * x)) / (1 - Real.exp (-x)) := by
  let d : ℕ → ℂ := fun n =>
    mobiusDiscreteLaplaceTerm x n - finitePrimeApertureMobiusLaplaceTerm Y x n
  have hd : Summable d := summable_mobiusLaplaceTerm_sub_finiteAperture Y hx
  have hhead : ∑ n ∈ Finset.range (Y + 1), d n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_range] at hn
    dsimp only [d]
    rw [finitePrimeApertureMobiusLaplaceTerm_eq_of_le (Nat.le_of_lt_succ hn)]
    exact sub_self _
  have hsplit : (∑' n : ℕ, d n) = ∑' n : ℕ, d (n + (Y + 1)) := by
    have h := hd.sum_add_tsum_nat_add (Y + 1)
    rw [hhead, zero_add] at h
    exact h.symm
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-(((n + (Y + 1) : ℕ) : ℝ) * x))) := by
    have hbase := summable_pow_mul_exp_neg 0 hx
    have hbase' : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
      simpa using hbase
    have hinj : Function.Injective (fun n : ℕ => n + (Y + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    change Summable
      ((fun n : ℕ => Real.exp (-((n : ℝ) * x))) ∘ (fun n : ℕ => n + (Y + 1)))
    exact hbase'.comp_injective hinj
  rw [mobiusDiscreteLaplaceTransform, finitePrimeApertureMobiusLaplaceTransform,
    ← (summable_mobiusDiscreteLaplaceTerm hx).tsum_sub
      (summable_finitePrimeApertureMobiusLaplaceTerm Y hx)]
  change ‖∑' n : ℕ, d n‖ ≤ _
  rw [hsplit]
  have hdshift : Summable (fun n : ℕ => d (n + (Y + 1))) := by
    apply hd.comp_injective
    intro a b hab
    exact Nat.add_right_cancel hab
  calc
    ‖∑' n : ℕ, d (n + (Y + 1))‖ ≤
        ∑' n : ℕ, ‖d (n + (Y + 1))‖ :=
      norm_tsum_le_tsum_norm hdshift.norm
    _ ≤ ∑' n : ℕ,
        Real.exp (-(((n + (Y + 1) : ℕ) : ℝ) * x)) := by
      exact hdshift.norm.tsum_le_tsum
        (fun n => norm_mobiusLaplaceTerm_sub_finiteAperture_le Y (n + (Y + 1)) x)
        hmajor
    _ = Real.exp (-(((Y + 1 : ℕ) : ℝ) * x)) /
        (1 - Real.exp (-x)) := tsum_exp_neg_nat_add x (Y + 1) hx

/-- Prime factors of `n` lying strictly beyond the moving boundary `z`. -/
def mobiusLargePrimeFactors (z n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (z < ·)

/-- Number of distinct prime factors of `n` beyond `z`. -/
def mobiusLargePrimeFactorCount (z n : ℕ) : ℕ :=
  (mobiusLargePrimeFactors z n).card

/-- Möbius coefficient in the sector with no prime factor beyond `z`. -/
def mobiusZeroLargePrimeCoefficient (z n : ℕ) : ℂ :=
  if mobiusLargePrimeFactorCount z n = 0 then mobiusComplexCoefficient n else 0

/-- Möbius coefficient in the sector with exactly one prime factor beyond `z`. -/
def mobiusOneLargePrimeCoefficient (z n : ℕ) : ℂ :=
  if mobiusLargePrimeFactorCount z n = 1 then mobiusComplexCoefficient n else 0

/-- Residual Möbius coefficient with at least two prime factors beyond `z`. -/
def mobiusTwoLargePrimeRemainderCoefficient (z n : ℕ) : ℂ :=
  if 2 ≤ mobiusLargePrimeFactorCount z n then mobiusComplexCoefficient n else 0

theorem mobiusCoefficient_eq_zero_add_one_add_twoLarge (z n : ℕ) :
    mobiusComplexCoefficient n =
      mobiusZeroLargePrimeCoefficient z n + mobiusOneLargePrimeCoefficient z n +
        mobiusTwoLargePrimeRemainderCoefficient z n := by
  by_cases h0 : mobiusLargePrimeFactorCount z n = 0
  · simp [mobiusZeroLargePrimeCoefficient, mobiusOneLargePrimeCoefficient,
      mobiusTwoLargePrimeRemainderCoefficient, h0]
  by_cases h1 : mobiusLargePrimeFactorCount z n = 1
  · simp [mobiusZeroLargePrimeCoefficient, mobiusOneLargePrimeCoefficient,
      mobiusTwoLargePrimeRemainderCoefficient, h1]
  have h2 : 2 ≤ mobiusLargePrimeFactorCount z n := by omega
  simp [mobiusZeroLargePrimeCoefficient, mobiusOneLargePrimeCoefficient,
    mobiusTwoLargePrimeRemainderCoefficient, h0, h1, h2]

theorem norm_mobiusZeroLargePrimeCoefficient_le_one (z n : ℕ) :
    ‖mobiusZeroLargePrimeCoefficient z n‖ ≤ 1 := by
  rw [mobiusZeroLargePrimeCoefficient]
  split_ifs
  · exact norm_mobiusComplexCoefficient_le_one n
  · simp

theorem norm_mobiusOneLargePrimeCoefficient_le_one (z n : ℕ) :
    ‖mobiusOneLargePrimeCoefficient z n‖ ≤ 1 := by
  rw [mobiusOneLargePrimeCoefficient]
  split_ifs
  · exact norm_mobiusComplexCoefficient_le_one n
  · simp

theorem norm_mobiusTwoLargePrimeRemainderCoefficient_le_one (z n : ℕ) :
    ‖mobiusTwoLargePrimeRemainderCoefficient z n‖ ≤ 1 := by
  rw [mobiusTwoLargePrimeRemainderCoefficient]
  split_ifs
  · exact norm_mobiusComplexCoefficient_le_one n
  · simp

/-- Sector Laplace term for a supplied arithmetic coefficient. -/
def mobiusPrimeSectorLaplaceTerm (c : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  c n * Complex.exp (-((n : ℝ) * x : ℝ))

def mobiusZeroLargePrimeLaplaceTransform (z : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusPrimeSectorLaplaceTerm (mobiusZeroLargePrimeCoefficient z) x n

def mobiusOneLargePrimeLaplaceTransform (z : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusPrimeSectorLaplaceTerm (mobiusOneLargePrimeCoefficient z) x n

def mobiusTwoLargePrimeRemainderLaplaceTransform (z : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    mobiusPrimeSectorLaplaceTerm (mobiusTwoLargePrimeRemainderCoefficient z) x n

private theorem summable_mobiusPrimeSectorLaplaceTerm_of_norm_le_one
    {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) {x : ℝ} (hx : 0 < x) :
    Summable (mobiusPrimeSectorLaplaceTerm c x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_exp_neg 0 hx)
  rw [mobiusPrimeSectorLaplaceTerm, norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (hc n) hexp

theorem summable_mobiusZeroLargePrimeLaplaceTerm
    (z : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (mobiusPrimeSectorLaplaceTerm (mobiusZeroLargePrimeCoefficient z) x) :=
  summable_mobiusPrimeSectorLaplaceTerm_of_norm_le_one
    (norm_mobiusZeroLargePrimeCoefficient_le_one z) hx

theorem summable_mobiusOneLargePrimeLaplaceTerm
    (z : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (mobiusPrimeSectorLaplaceTerm (mobiusOneLargePrimeCoefficient z) x) :=
  summable_mobiusPrimeSectorLaplaceTerm_of_norm_le_one
    (norm_mobiusOneLargePrimeCoefficient_le_one z) hx

theorem summable_mobiusTwoLargePrimeRemainderLaplaceTerm
    (z : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable
      (mobiusPrimeSectorLaplaceTerm (mobiusTwoLargePrimeRemainderCoefficient z) x) :=
  summable_mobiusPrimeSectorLaplaceTerm_of_norm_le_one
    (norm_mobiusTwoLargePrimeRemainderCoefficient_le_one z) hx

/-- Exact zero/one/two-or-more large-prime decomposition of the full Möbius--Laplace source. -/
theorem mobiusDiscreteLaplaceTransform_eq_largePrimeBoundary_add_remainder
    (z : ℕ) {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x =
      mobiusZeroLargePrimeLaplaceTransform z x +
        mobiusOneLargePrimeLaplaceTransform z x +
          mobiusTwoLargePrimeRemainderLaplaceTransform z x := by
  have hzero := summable_mobiusZeroLargePrimeLaplaceTerm z hx
  have hone := summable_mobiusOneLargePrimeLaplaceTerm z hx
  have htwo := summable_mobiusTwoLargePrimeRemainderLaplaceTerm z hx
  rw [mobiusDiscreteLaplaceTransform, mobiusZeroLargePrimeLaplaceTransform,
    mobiusOneLargePrimeLaplaceTransform, mobiusTwoLargePrimeRemainderLaplaceTransform]
  rw [← hzero.tsum_add hone]
  rw [← (hzero.add hone).tsum_add htwo]
  apply tsum_congr
  intro n
  rw [mobiusDiscreteLaplaceTerm, mobiusPrimeSectorLaplaceTerm,
    mobiusPrimeSectorLaplaceTerm, mobiusPrimeSectorLaplaceTerm,
    ← add_mul, ← add_mul, ← mobiusCoefficient_eq_zero_add_one_add_twoLarge]
  rfl

theorem mobiusLargePrimeFactorCount_eq_zero_iff_subset_aperture (z n : ℕ) :
    mobiusLargePrimeFactorCount z n = 0 ↔
      n.primeFactors ⊆ mobiusFinitePrimeAperture z := by
  constructor
  · intro hzero p hp
    have hfilter : n.primeFactors.filter (z < ·) = ∅ := by
      rw [← Finset.card_eq_zero]
      exact hzero
    have hpNot : ¬z < p := by
      intro hzp
      have : p ∈ n.primeFactors.filter (z < ·) := Finset.mem_filter.mpr ⟨hp, hzp⟩
      rw [hfilter] at this
      exact Finset.notMem_empty p this
    have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    rw [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpPrime⟩
  · intro hsubset
    rw [mobiusLargePrimeFactorCount, mobiusLargePrimeFactors, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro p hp
    have hpAperture := hsubset hp
    rw [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range] at hpAperture
    omega

/-- The zero-large-prime sector is exactly the canonical finite-prime aperture coefficient. -/
theorem mobiusZeroLargePrimeCoefficient_eq_finiteAperture (z n : ℕ) :
    mobiusZeroLargePrimeCoefficient z n =
      finitePrimeApertureMobiusCoefficient (mobiusFinitePrimeAperture z) n := by
  rw [mobiusZeroLargePrimeCoefficient, finitePrimeApertureMobiusCoefficient]
  by_cases hzero : mobiusLargePrimeFactorCount z n = 0
  · rw [if_pos hzero, if_pos
      ((mobiusLargePrimeFactorCount_eq_zero_iff_subset_aperture z n).mp hzero)]
  · rw [if_neg hzero, if_neg]
    intro hsubset
    exact hzero
      ((mobiusLargePrimeFactorCount_eq_zero_iff_subset_aperture z n).mpr hsubset)

theorem mobiusZeroLargePrimeLaplaceTransform_eq_finiteAperture
    (z : ℕ) (x : ℝ) :
    mobiusZeroLargePrimeLaplaceTransform z x =
      finitePrimeApertureMobiusLaplaceTransform z x := by
  rw [mobiusZeroLargePrimeLaplaceTransform, finitePrimeApertureMobiusLaplaceTransform]
  apply tsum_congr
  intro n
  rw [mobiusPrimeSectorLaplaceTerm, finitePrimeApertureMobiusLaplaceTerm,
    mobiusZeroLargePrimeCoefficient_eq_finiteAperture]

/-- Two distinct prime factors beyond `z` force the integer strictly beyond `z^2`. -/
theorem sq_lt_of_two_le_mobiusLargePrimeFactorCount
    {z n : ℕ} (hcount : 2 ≤ mobiusLargePrimeFactorCount z n) :
    z ^ 2 < n := by
  have hone : 1 < (mobiusLargePrimeFactors z n).card := by
    rw [mobiusLargePrimeFactorCount] at hcount
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hone
  rw [mobiusLargePrimeFactors, Finset.mem_filter] at hp hq
  have hpData := Nat.mem_primeFactors.mp hp.1
  have hqData := Nat.mem_primeFactors.mp hq.1
  have hpPrime : p.Prime := hpData.1
  have hqPrime : q.Prime := hqData.1
  have hpqDvd : p * q ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hpPrime hqPrime).mpr hpq) hpData.2.1 hqData.2.1
  have hn0 : n ≠ 0 := hpData.2.2
  have hpqLe : p * q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpqDvd
  have hzpq : z ^ 2 < p * q := by
    nlinarith
  exact lt_of_lt_of_le hzpq hpqLe

/-- The two-large-prime residual term vanishes through the square boundary `z^2`. -/
theorem mobiusTwoLargePrimeRemainderCoefficient_eq_zero_of_le_sq
    {z n : ℕ} (hn : n ≤ z ^ 2) :
    mobiusTwoLargePrimeRemainderCoefficient z n = 0 := by
  rw [mobiusTwoLargePrimeRemainderCoefficient, if_neg]
  intro hcount
  exact (not_lt_of_ge hn) (sq_lt_of_two_le_mobiusLargePrimeFactorCount hcount)

/-- Through the square boundary `z^2`, the combined zero/one-large-prime coefficient is the
literal Möbius coefficient.  Thus a transport theorem on this truncation cannot replace the
all-prime sign problem by a different finite coefficient system. -/
theorem mobiusZero_add_oneLargePrimeCoefficient_eq_mobius_of_le_sq
    {z n : ℕ} (hn : n ≤ z ^ 2) :
    mobiusZeroLargePrimeCoefficient z n + mobiusOneLargePrimeCoefficient z n =
      mobiusComplexCoefficient n := by
  rw [mobiusCoefficient_eq_zero_add_one_add_twoLarge z n,
    mobiusTwoLargePrimeRemainderCoefficient_eq_zero_of_le_sq hn, add_zero]

/-- Absolute geometric bound for the sector with at least two primes beyond `z`. -/
theorem norm_mobiusTwoLargePrimeRemainderLaplaceTransform_le
    (z : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖mobiusTwoLargePrimeRemainderLaplaceTransform z x‖ ≤
      Real.exp (-((((z ^ 2) + 1 : ℕ) : ℝ) * x)) / (1 - Real.exp (-x)) := by
  let r : ℕ → ℂ := fun n =>
    mobiusPrimeSectorLaplaceTerm (mobiusTwoLargePrimeRemainderCoefficient z) x n
  have hr : Summable r := summable_mobiusTwoLargePrimeRemainderLaplaceTerm z hx
  have hhead : ∑ n ∈ Finset.range (z ^ 2 + 1), r n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_range] at hn
    dsimp only [r, mobiusPrimeSectorLaplaceTerm]
    rw [mobiusTwoLargePrimeRemainderCoefficient_eq_zero_of_le_sq (Nat.le_of_lt_succ hn),
      zero_mul]
  have hsplit : (∑' n : ℕ, r n) = ∑' n : ℕ, r (n + (z ^ 2 + 1)) := by
    have h := hr.sum_add_tsum_nat_add (z ^ 2 + 1)
    rw [hhead, zero_add] at h
    exact h.symm
  have hrshift : Summable (fun n : ℕ => r (n + (z ^ 2 + 1))) := by
    apply hr.comp_injective
    intro a b hab
    exact Nat.add_right_cancel hab
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-(((n + (z ^ 2 + 1) : ℕ) : ℝ) * x))) := by
    have hbase := summable_pow_mul_exp_neg 0 hx
    have hbase' : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
      simpa using hbase
    change Summable
      ((fun n : ℕ => Real.exp (-((n : ℝ) * x))) ∘ (fun n : ℕ => n + (z ^ 2 + 1)))
    exact hbase'.comp_injective (by intro a b hab; exact Nat.add_right_cancel hab)
  rw [mobiusTwoLargePrimeRemainderLaplaceTransform]
  change ‖∑' n : ℕ, r n‖ ≤ _
  rw [hsplit]
  calc
    ‖∑' n : ℕ, r (n + (z ^ 2 + 1))‖ ≤
        ∑' n : ℕ, ‖r (n + (z ^ 2 + 1))‖ :=
      norm_tsum_le_tsum_norm hrshift.norm
    _ ≤ ∑' n : ℕ,
        Real.exp (-(((n + (z ^ 2 + 1) : ℕ) : ℝ) * x)) := by
      exact hrshift.norm.tsum_le_tsum (fun n => by
        dsimp only [r, mobiusPrimeSectorLaplaceTerm]
        rw [norm_mul, Complex.norm_exp]
        exact mul_le_of_le_one_left (Real.exp_pos _).le
          (norm_mobiusTwoLargePrimeRemainderCoefficient_le_one z _)) hmajor
    _ = Real.exp (-((((z ^ 2) + 1 : ℕ) : ℝ) * x)) /
        (1 - Real.exp (-x)) := tsum_exp_neg_nat_add x (z ^ 2 + 1) hx

/-- At the moving boundary `z^2 x ≈ (1/2) log(1/x)`, every sector with at least two
large primes is already within the critical half-power budget. -/
theorem norm_mobiusTwoLargePrimeRemainderLaplaceTransform_le_critical
    (z : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hscale : (1 / 2 : ℝ) * Real.log (1 / x) ≤ (((z ^ 2) + 1 : ℕ) : ℝ) * x) :
    ‖mobiusTwoLargePrimeRemainderLaplaceTransform z x‖ ≤
      2 * x ^ (-(1 / 2 : ℝ)) := by
  have htail := norm_mobiusTwoLargePrimeRemainderLaplaceTransform_le z hx
  refine htail.trans ?_
  have hden : x / 2 ≤ 1 - Real.exp (-x) :=
    half_mul_le_one_sub_exp_neg hx hx1
  have hdenPos : 0 < 1 - Real.exp (-x) := lt_of_lt_of_le (by positivity) hden
  have hlog : Real.log (1 / x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  have hnum :
      Real.exp (-((((z ^ 2) + 1 : ℕ) : ℝ) * x)) ≤ x ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    rw [hlog] at hscale
    linarith
  have hpower :
      2 * x ^ (-(1 / 2 : ℝ)) * (x / 2) = x ^ (1 / 2 : ℝ) := by
    calc
      2 * x ^ (-(1 / 2 : ℝ)) * (x / 2) =
          x ^ (-(1 / 2 : ℝ)) * x := by ring
      _ = x ^ (-(1 / 2 : ℝ)) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ (1 / 2 : ℝ) := by congr 1; ring
  rw [div_le_iff₀ hdenPos]
  calc
    Real.exp (-((((z ^ 2) + 1 : ℕ) : ℝ) * x)) ≤ x ^ (1 / 2 : ℝ) := hnum
    _ = 2 * x ^ (-(1 / 2 : ℝ)) * (x / 2) := hpower.symm
    _ ≤ 2 * x ^ (-(1 / 2 : ℝ)) * (1 - Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)

/-- Positive squarefree exponential partition normalizing the Gibbs law. -/
def mobiusSquarefreeExponentialPartition (x : ℝ) : ℝ :=
  ∑' n : ℕ, ‖mobiusComplexCoefficient n‖ * Real.exp (-((n : ℝ) * x))

theorem summable_mobiusSquarefreeExponentialWeight {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ =>
      ‖mobiusComplexCoefficient n‖ * Real.exp (-((n : ℝ) * x))) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun n => ?_) (summable_pow_mul_exp_neg 0 hx)
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (norm_mobiusComplexCoefficient_le_one n) hexp

theorem mobiusSquarefreeExponentialPartition_pos {x : ℝ} (hx : 0 < x) :
    0 < mobiusSquarefreeExponentialPartition x := by
  exact (summable_mobiusSquarefreeExponentialWeight hx).tsum_pos
    (fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) 1
    (by simp [mobiusComplexCoefficient]; positivity)

/-- The positive squarefree partition has the sharp elementary `x⁻¹` upper envelope. -/
theorem mobiusSquarefreeExponentialPartition_le_inv {x : ℝ} (hx : 0 < x) :
    mobiusSquarefreeExponentialPartition x ≤ 1 / x := by
  let a : ℕ → ℝ := fun n =>
    ‖mobiusComplexCoefficient n‖ * Real.exp (-((n : ℝ) * x))
  have ha : Summable a := summable_mobiusSquarefreeExponentialWeight hx
  have hshift : mobiusSquarefreeExponentialPartition x = ∑' n : ℕ, a (n + 1) := by
    have h := ha.sum_add_tsum_nat_add 1
    rw [mobiusSquarefreeExponentialPartition]
    simpa [a, mobiusComplexCoefficient] using h.symm
  have hashift : Summable (fun n : ℕ => a (n + 1)) :=
    ha.comp_injective Nat.succ_injective
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-(((n + 1 : ℕ) : ℝ) * x))) := by
    have hbase := summable_pow_mul_exp_neg 0 hx
    have hbase' : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * x))) := by
      simpa using hbase
    exact hbase'.comp_injective Nat.succ_injective
  have hgeom :
      mobiusSquarefreeExponentialPartition x ≤
        Real.exp (-x) / (1 - Real.exp (-x)) := by
    rw [hshift]
    calc
      (∑' n : ℕ, a (n + 1)) ≤
          ∑' n : ℕ, Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) := by
        exact hashift.tsum_le_tsum (fun n => by
          dsimp only [a]
          have hexp : 0 ≤ Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) :=
            (Real.exp_pos _).le
          exact mul_le_of_le_one_left hexp
            (norm_mobiusComplexCoefficient_le_one (n + 1))) hmajor
      _ = Real.exp (-x) / (1 - Real.exp (-x)) := by
        simpa using tsum_exp_neg_nat_add x 1 hx
  have hq0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hq1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hexpinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hq0
  rw [hexpinv] at hmul
  have hqx : Real.exp (-x) * x ≤ 1 - Real.exp (-x) := by nlinarith
  have hquot : Real.exp (-x) / (1 - Real.exp (-x)) ≤ 1 / x :=
    (div_le_div_iff₀ (sub_pos.mpr hq1) hx).2 (by simpa using hqx)
  exact hgeom.trans hquot

/-- Parity Fourier coefficient of the normalized positive squarefree exponential law. -/
def mobiusSquarefreeExponentialGibbsParity (x : ℝ) : ℂ :=
  mobiusDiscreteLaplaceTransform x / (mobiusSquarefreeExponentialPartition x : ℂ)

/-- Exact positive-source factorization `Phi = Z * E[parity]`. -/
theorem mobiusSquarefreePartition_mul_gibbsParity
    {x : ℝ} (hx : 0 < x) :
    (mobiusSquarefreeExponentialPartition x : ℂ) *
        mobiusSquarefreeExponentialGibbsParity x =
      mobiusDiscreteLaplaceTransform x := by
  rw [mobiusSquarefreeExponentialGibbsParity]
  exact mul_div_cancel₀ _ (ofReal_ne_zero.mpr
    (mobiusSquarefreeExponentialPartition_pos hx).ne')

/-- Exact Gibbs form of the open all-strict-half source. -/
def MobiusSquarefreeExponentialGibbsAllStrictHalfMixing : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
    ‖mobiusSquarefreeExponentialGibbsParity x‖ ≤ C * x ^ (1 / 2 - ε)

/-- The Gibbs parity exponent is exactly `1/2-ε`: multiplication by `Z(x) ≤ x⁻¹` turns it
into the `x⁻ᵇ`, `b>1/2`, Möbius--Laplace law consumed by Route E. -/
theorem mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_gibbsMixing
    (hmix : MobiusSquarefreeExponentialGibbsAllStrictHalfMixing) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := b - 1 / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hmix ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx0 hx1
  have hx : 0 < x := hx0
  have hfactor := congrArg norm (mobiusSquarefreePartition_mul_gibbsParity hx)
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (mobiusSquarefreeExponentialPartition_pos hx)] at hfactor
  rw [← hfactor]
  have hZ := mobiusSquarefreeExponentialPartition_le_inv hx
  have hP := hbound x hx hx1.le
  calc
    mobiusSquarefreeExponentialPartition x *
        ‖mobiusSquarefreeExponentialGibbsParity x‖ ≤
        (1 / x) * (C * x ^ (1 / 2 - ε)) :=
      mul_le_mul hZ hP (norm_nonneg _) (by positivity)
    _ = C * x ^ (-b) := by
      rw [one_div, ← Real.rpow_neg_one x]
      calc
        x ^ (-1 : ℝ) * (C * x ^ (1 / 2 - ε)) =
            C * (x ^ (-1 : ℝ) * x ^ (1 / 2 - ε)) := by ring
        _ = C * x ^ ((-1 : ℝ) + (1 / 2 - ε)) := by
          rw [Real.rpow_add hx]
        _ = C * x ^ (-b) := by
          congr 2
          dsimp [ε]
          ring
    _ = C * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]

/-- Unconditional consumer: proving the positive Gibbs boundary-mixing law proves RH. -/
theorem riemannHypothesis_of_mobiusSquarefreeExponentialGibbsMixing
    (hmix : MobiusSquarefreeExponentialGibbsAllStrictHalfMixing) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_gibbsMixing hmix)

end

end RHTower
