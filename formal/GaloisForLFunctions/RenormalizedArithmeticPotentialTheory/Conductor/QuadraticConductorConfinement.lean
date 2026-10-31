import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.ExplicitRoughConditioning
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.RamanujanApproximationByLogarithmicMoment
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds

/-!
# Quadratic accuracy loss in exponential conductor confinement

The conditional logarithmic class moment is bounded before truncating class
support. Applying the spectral tail estimate to this moment saves one power
of the squared-error tolerance.
-/

noncomputable section
open Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory BezoutValuationIncidence
  CompletedArithmeticForms CriticalArithmeticCorrelationTheory

/-- Harmonic conditioning contracts the logarithmic smooth-part moment. -/
theorem sum_smoothRoughMean_log_classMass_le (P N : ℕ) (x : ℕ → ℝ) :
    (∑ a ∈ sieveClassPrefix (primePrefixSieve P) N,
      Real.log (a : ℕ) * sieveClassMass (primePrefixSieve P) a N *
        smoothRoughMean P N x a ^ 2) ≤
        ∑ n ∈ Icc 1 N,
          Real.log (RHTower.Sieve.smoothPart (P - 1) n) * x n ^ 2 := by
  rw [sum_sieveClassPrefix_primePrefix P N
    (fun a => Real.log (a : ℕ) * sieveClassMass (primePrefixSieve P) a N *
        smoothRoughMean P N x a ^ 2),
    sum_Icc_eq_smoothRough_fibres P N]
  refine sum_le_sum fun a ha => ?_
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp ha).2
  have hj := sum_mul_sq_wMean_sub_le
    (s := roughInterval P (N / a)) (w := fun k => 1 / (k : ℝ))
    (v := fun k => poleGauge x (a * k)) (fun k _ => by positivity) (0 : ℝ)
  simp only [sub_zero] at hj
  have hj' := mul_le_mul_of_nonneg_left hj
    (div_nonneg (Real.log_natCast_nonneg a) (Nat.cast_nonneg a))
  have hleft : Real.log a / (a : ℝ) *
      ((∑ k ∈ roughInterval P (N / a), (1 : ℝ) / k) *
        wMean (roughInterval P (N / a)) (fun k => 1 / (k : ℝ))
          (fun k => poleGauge x (a * k)) ^ 2) =
        Real.log (a : ℕ) * sieveClassMass (primePrefixSieve P) a N *
        smoothRoughMean P N x a ^ 2 := by
    rw [sieveClassMass, sievedHarmonic_primePrefix_eq]
    unfold roughHarmonic smoothRoughMean
    ring
  rw [hleft, mul_sum] at hj'
  refine hj'.trans_eq ?_
  exact sum_congr rfl fun b hb => by
    have hb0 : (b : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < b from (mem_roughInterval.mp hb).1).ne'
    rw [smoothPart_mul_of_mem_rough_fibre ha hb, poleGauge, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
    field_simp

/-- The conditioned logarithmic moment costs defect plus three Euler corrections. -/
theorem sum_smoothRoughMean_prefix_logMoment_le (P N : ℕ) {A : ℕ} (hAN : A ≤ N)
    (x : ℕ → ℝ) :
    (∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
      (Real.log (a : ℕ) + ladderConstant P) * sieveClassMass (primePrefixSieve P) a N *
        smoothRoughMean P N x a ^ 2) ≤
      2 * poleDefect N x + 3 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hL := ladderConstant_nonneg P
  have hprefix : sieveClassPrefix (primePrefixSieve P) A ⊆
      sieveClassPrefix (primePrefixSieve P) N := by
    intro a ha
    exact (mem_sieveClassPrefix _ N a).mpr
      (((mem_sieveClassPrefix _ A a).mp ha).trans hAN)
  have hlog := (sum_smoothRoughMean_log_classMass_le P N x).trans
    (sum_log_smoothPart_mul_sq_le P N x)
  have hmass := mul_le_mul_of_nonneg_left
    (sum_smoothRoughMean_classMass_le P N x) hL
  calc
    _ ≤ ∑ a ∈ sieveClassPrefix (primePrefixSieve P) N,
        (Real.log (a : ℕ) + ladderConstant P) * sieveClassMass (primePrefixSieve P) a N *
          smoothRoughMean P N x a ^ 2 := by
      refine sum_le_sum_of_subset_of_nonneg hprefix fun a _ _ => ?_
      exact mul_nonneg
        (mul_nonneg (add_nonneg (Real.log_natCast_nonneg _) hL)
          (div_nonneg (sievedHarmonic_nonneg _ _) (Nat.cast_nonneg _))) (sq_nonneg _)
    _ = (∑ a ∈ sieveClassPrefix (primePrefixSieve P) N,
        Real.log (a : ℕ) * sieveClassMass (primePrefixSieve P) a N *
          smoothRoughMean P N x a ^ 2) +
        ladderConstant P * ∑ a ∈ sieveClassPrefix (primePrefixSieve P) N,
          sieveClassMass (primePrefixSieve P) a N * smoothRoughMean P N x a ^ 2 := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    _ ≤ _ := by linarith only [hlog, hmass]

private theorem exists_nat_log_cutoff_explicit {x : ℝ} (hx : 0 ≤ x) :
    ∃ T : ℕ, 1 < T ∧ x ≤ Real.log T ∧ Real.log T ≤ x + 3 := by
  let z : ℝ := x + 2
  let T : ℕ := ⌈Real.exp z⌉₊
  have hz : 0 < z := by dsimp only [z]; linarith only [hx]
  have hexp : 1 < Real.exp z := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
  have hceil : Real.exp z ≤ (T : ℝ) := Nat.le_ceil _
  have hTR : (1 : ℝ) < T := hexp.trans_le hceil
  have hT : 1 < T := by exact_mod_cast hTR
  have hlower : z ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hceil
  have hceilUpper : (T : ℝ) < Real.exp z + 1 := Nat.ceil_lt_add_one (Real.exp_pos z).le
  have hdouble : (T : ℝ) ≤ 2 * Real.exp z := by linarith only [hceilUpper, hexp]
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hupper : Real.log T ≤ z + 1 := by
    have h := Real.log_le_log (zero_lt_one.trans hTR) hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero z), Real.log_exp] at h
    linarith only [h, hlogTwo]
  refine ⟨T, hT, ?_, ?_⟩
  · dsimp only [z] at hlower; linarith only [hlower]
  · dsimp only [z] at hupper; linarith only [hupper]


private def quadraticCutoffCoefficient (C₀ : ℝ) : ℝ :=
  54 * (2 * (C₀ + 3) + 2 * (Real.log 4 + 4)) + 49

private theorem exists_quadratic_cutoffs {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ P A R : ℕ, 1 < P ∧ 1 < A ∧ 1 < R ∧ A ^ 2 ≤ R ∧
        2 * ladderConstant P + 4 ≤ Real.log R ∧
        C₀ / Real.log P * K ≤ δ ∧
        (2 * K + 2 * ladderConstant P) / Real.log A ≤ δ ∧
        16 * (2 * K + 3 * ladderConstant P) / Real.log R ≤ δ ∧
        Real.log R ≤ quadraticCutoffCoefficient C₀ / δ ^ 2 * (K + 1) := by
  let J : ℝ := Real.log 4 + 4
  have hJ : 0 < J := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [J]; linarith only [h]
  let B₁ : ℝ := C₀ + 3
  let B₂ : ℝ := 2 * B₁ + 2 * J
  let B₃ : ℝ := 2 * (1 + B₂) + 3
  intro δ hδ hδ1 K hK
  have hK1 : 0 < K + 1 := by linarith only [hK]
  have hinv1 : 1 ≤ 1 / δ := one_le_div hδ |>.mpr hδ1
  have hinv2 : 1 / δ ≤ 1 / δ ^ 2 := by
    rw [div_le_div_iff₀ hδ (sq_pos_of_pos hδ)]
    nlinarith only [hδ.le, hδ1]
  obtain ⟨P, hP, hPlow, hPup⟩ := exists_nat_log_cutoff_explicit
    (div_nonneg (mul_nonneg hC₀.le hK1.le) hδ.le)
  have hPR : (1 : ℝ) < P := by exact_mod_cast hP
  have hlogP : 0 < Real.log P := Real.log_pos hPR
  have hPbound : Real.log P ≤ (B₁ / δ) * (K + 1) := by
    calc
      Real.log P ≤ C₀ * (K + 1) / δ + 3 := hPup
      _ ≤ C₀ * (K + 1) / δ + 3 * (1 / δ) * (K + 1) := by
        have h1 : (1 : ℝ) ≤ (1 / δ) * (K + 1) := by nlinarith only [hinv1, hK]
        linarith only [h1]
      _ = (B₁ / δ) * (K + 1) := by dsimp only [B₁]; ring
  have hL0 := ladderConstant_nonneg P
  have hLbound : ladderConstant P ≤ (B₂ / δ) * (K + 1) := by
    have hL := ladderConstant_le_log (show 1 ≤ P by omega)
    change ladderConstant P ≤ 2 * (Real.log P + J) at hL
    have hJterm : 2 * J ≤ (2 * J / δ) * (K + 1) := by
      have h1 : (1 : ℝ) ≤ (1 / δ) * (K + 1) := by nlinarith only [hinv1, hK]
      have hm := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * J by positivity)
      linarith only [hm.trans_eq (by ring : 2 * J * ((1 / δ) * (K + 1)) = (2 * J / δ) * (K + 1))]
    calc
      ladderConstant P ≤ 2 * Real.log P + 2 * J := by linarith only [hL]
      _ ≤ 2 * ((B₁ / δ) * (K + 1)) + (2 * J / δ) * (K + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hPbound zero_le_two) hJterm
      _ = (B₂ / δ) * (K + 1) := by dsimp only [B₂]; ring
  obtain ⟨A, hA, hAlow, hAup⟩ := exists_nat_log_cutoff_explicit
    (div_nonneg (mul_nonneg zero_le_two (add_nonneg hK hL0)) hδ.le)
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log A := Real.log_pos hAR
  have hAbound : Real.log A ≤ (B₃ / δ ^ 2) * (K + 1) := by
    have hKL : K + ladderConstant P ≤ ((1 + B₂) / δ) * (K + 1) := by
      have hKterm : K + 1 ≤ (1 / δ) * (K + 1) :=
        (one_mul (K + 1)).symm.trans_le (mul_le_mul_of_nonneg_right hinv1 hK1.le)
      calc
        K + ladderConstant P ≤ (K + 1) + (B₂ / δ) * (K + 1) := by linarith only [hLbound]
        _ ≤ (1 / δ) * (K + 1) + (B₂ / δ) * (K + 1) := add_le_add hKterm le_rfl
        _ = ((1 + B₂) / δ) * (K + 1) := by ring
    have h3term : (3 : ℝ) ≤ (3 / δ ^ 2) * (K + 1) := by
      have h12 : (1 : ℝ) ≤ 1 / δ ^ 2 := hinv1.trans hinv2
      have h1 : (1 : ℝ) ≤ (1 / δ ^ 2) * (K + 1) :=
        (one_mul (1 : ℝ)).symm.trans_le (mul_le_mul h12 (by linarith only [hK]) zero_le_one
          (zero_le_one.trans h12))
      linarith only [(mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
        (by ring : 3 * ((1 / δ ^ 2) * (K + 1)) = (3 / δ ^ 2) * (K + 1))]
    calc
      Real.log A ≤ 2 * (K + ladderConstant P) / δ + 3 := hAup
      _ ≤ 2 * (((1 + B₂) / δ) * (K + 1)) / δ + (3 / δ ^ 2) * (K + 1) :=
        add_le_add (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKL zero_le_two) hδ.le) h3term
      _ = (B₃ / δ ^ 2) * (K + 1) := by
        dsimp only [B₃]
        field_simp [hδ.ne']
  let z : ℝ := 2 * Real.log A + 2 * ladderConstant P + 4 +
    16 * (2 * K + 3 * ladderConstant P) / δ
  have hfrac : 0 ≤ 16 * (2 * K + 3 * ladderConstant P) / δ := by positivity
  obtain ⟨R, hR, hRlow, hRup⟩ := exists_nat_log_cutoff_explicit (by dsimp only [z]; positivity : 0 ≤ z)
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRR
  have hARsq : A ^ 2 ≤ R := by
    have hlogs : Real.log ((A : ℝ) ^ 2) ≤ Real.log R := by
      rw [pow_two, Real.log_mul (zero_lt_one.trans hAR).ne' (zero_lt_one.trans hAR).ne']
      dsimp only [z] at hRlow
      linarith only [hRlow, hL0, hfrac]
    have he := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_log (sq_pos_of_pos (zero_lt_one.trans hAR)),
      Real.exp_log (zero_lt_one.trans hRR)] at he
    exact_mod_cast he
  have hEuler : 2 * ladderConstant P + 4 ≤ Real.log R := by
    dsimp only [z] at hRlow; linarith only [hRlow, hlogA, hfrac]
  have hmean : C₀ / Real.log P * K ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogP]
    have hp := (div_le_iff₀ hδ).mp hPlow
    nlinarith only [hp, hC₀]
  have htail : (2 * K + 2 * ladderConstant P) / Real.log A ≤ δ := by
    apply (div_le_iff₀ hlogA).mpr
    have ha := (div_le_iff₀ hδ).mp hAlow
    nlinarith only [ha]
  have hmode : 16 * (2 * K + 3 * ladderConstant P) / Real.log R ≤ δ := by
    apply (div_le_iff₀ hlogR).mpr
    have hf : 16 * (2 * K + 3 * ladderConstant P) / δ ≤ Real.log R := by
      dsimp only [z] at hRlow; linarith only [hRlow, hlogA, hL0]
    have h := (div_le_iff₀ hδ).mp hf
    nlinarith only [h]
  have hRbound : Real.log R ≤ quadraticCutoffCoefficient C₀ / δ ^ 2 * (K + 1) := by
    have hB₂0 : 0 ≤ B₂ := by dsimp only [B₂, B₁]; positivity
    have hL2 : ladderConstant P ≤ (B₂ / δ ^ 2) * (K + 1) := by
      refine hLbound.trans (mul_le_mul_of_nonneg_right ?_ hK1.le)
      have hm := mul_le_mul_of_nonneg_left hinv2 hB₂0
      simpa only [mul_one_div] using hm
    have hKterm : K + 1 ≤ (1 / δ) * (K + 1) :=
      (one_mul (K + 1)).symm.trans_le (mul_le_mul_of_nonneg_right hinv1 hK1.le)
    have hmoment : 2 * K + 3 * ladderConstant P ≤
        ((2 + 3 * B₂) / δ) * (K + 1) := by
      calc
        _ ≤ 2 * ((1 / δ) * (K + 1)) + 3 * ((B₂ / δ) * (K + 1)) := by
          linarith only [hKterm, hLbound]
        _ = _ := by ring
    have hdiv : 16 * (2 * K + 3 * ladderConstant P) / δ ≤
        ((32 + 48 * B₂) / δ ^ 2) * (K + 1) := by
      calc
        _ ≤ 16 * (((2 + 3 * B₂) / δ) * (K + 1)) / δ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmoment (by norm_num)) hδ.le
        _ = _ := by field_simp [hδ.ne']; ring
    have h7 : (7 : ℝ) ≤ (7 / δ ^ 2) * (K + 1) := by
      have h12 : (1 : ℝ) ≤ 1 / δ ^ 2 := hinv1.trans hinv2
      have h1 : (1 : ℝ) ≤ (1 / δ ^ 2) * (K + 1) := by
        nlinarith only [h12, hK]
      linarith only [(mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 7)).trans_eq
        (by ring : 7 * ((1 / δ ^ 2) * (K + 1)) = (7 / δ ^ 2) * (K + 1))]
    dsimp only [z] at hRup
    calc
      Real.log R ≤ 2 * Real.log A + 2 * ladderConstant P + 7 +
          16 * (2 * K + 3 * ladderConstant P) / δ := by linarith only [hRup]
      _ ≤ 2 * ((B₃ / δ ^ 2) * (K + 1)) + 2 * ((B₂ / δ ^ 2) * (K + 1)) +
          (7 / δ ^ 2) * (K + 1) + ((32 + 48 * B₂) / δ ^ 2) * (K + 1) :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hAbound zero_le_two)
          (mul_le_mul_of_nonneg_left hL2 zero_le_two)) h7) hdiv
      _ = _ := by dsimp only [quadraticCutoffCoefficient, B₃, B₂, B₁, J]; ring
  exact ⟨P, A, R, hP, hA, hR, hARsq, hEuler, hmean, htail, hmode, hRbound⟩

private def extendSieveCoefficient (Q : Finset Nat.Primes)
    (b : SieveClass Q → ℝ) (m : ℕ) : ℝ :=
  if hm : SieveSupported Q m then b ⟨m, hm⟩ else 0

private theorem extendSieveCoefficient_at (Q : Finset Nat.Primes)
    (b : SieveClass Q → ℝ) (m : SieveClass Q) :
    extendSieveCoefficient Q b (m : ℕ) = b m := by
  rw [extendSieveCoefficient, dif_pos m.property]

private theorem sum_extendSieveCoefficient_ramanujanPole (Q : Finset Nat.Primes)
    (R : ℕ) (b : SieveClass Q → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 R, extendSieveCoefficient Q b m * ramanujanPoleProfile m n) =
      ∑ m ∈ sieveClassPrefix Q R, b m * ramanujanPoleProfile m n := by
  let S := (sieveClassPrefix Q R).image (fun m : SieveClass Q => (m : ℕ))
  have hS : S ⊆ Icc 1 R := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨a.property.pos, (mem_sieveClassPrefix Q R a).mp ha⟩
  have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmS : m ∉ S) :
      extendSieveCoefficient Q b m * ramanujanPoleProfile m n = 0 := by
    have hnot : ¬SieveSupported Q m := by
      intro hsup
      exact hmS (mem_image.mpr ⟨⟨m, hsup⟩,
        (mem_sieveClassPrefix Q R ⟨m, hsup⟩).mpr (mem_Icc.mp hm).2, rfl⟩)
    rw [extendSieveCoefficient, dif_neg hnot, zero_mul]
  calc
    _ = ∑ m ∈ S, extendSieveCoefficient Q b m * ramanujanPoleProfile m n :=
      (sum_subset hS hzero).symm
    _ = ∑ m ∈ sieveClassPrefix Q R,
        extendSieveCoefficient Q b (m : ℕ) * ramanujanPoleProfile m n := by
      dsimp only [S]
      exact sum_image (fun a _ b _ h => Subtype.ext h)
    _ = _ := sum_congr rfl fun m _ => by rw [extendSieveCoefficient_at]

private theorem sum_horizon_truncated_coefficients {N R : ℕ} (hNR : N ≤ R)
    (b : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) =
      ∑ m ∈ Icc 1 N, b m * ramanujanPoleProfile m n := by
  have hsub : Icc 1 N ⊆ Icc 1 R := fun m hm =>
    mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hNR⟩
  calc
    _ = ∑ m ∈ Icc 1 N, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n := by
      symm
      apply sum_subset hsub
      intro m hm hmN
      have hn : ¬m ≤ N := fun h => hmN (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
      rw [if_neg hn, zero_mul]
    _ = _ := sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]


/-- Explicit absolute coefficient for quadratic-accuracy conductor confinement. -/
def quadraticConfinementConstant : ℝ :=
  64 * quadraticCutoffCoefficient explicitRoughConditioningConstant

theorem quadraticConfinementConstant_pos : 0 < quadraticConfinementConstant := by
  have h := explicitRoughConditioningConstant_pos
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  unfold quadraticConfinementConstant quadraticCutoffCoefficient
  positivity

/-- Every bounded-defect vector has an exponential conductor approximation with quadratic
dependence on the squared-error tolerance and a closed-form absolute constant. -/
theorem exists_explicit_quadratic_conductor_cutoff :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      ∃ R : ℕ, 2 ≤ R ∧ Real.log R ≤ quadraticConfinementConstant / η ^ 2 * (K + 1) ∧
        ∀ N : ℕ, ∀ x : ℕ → ℝ,
          (∑ n ∈ Icc 1 N, x n ^ 2) ≤ 1 → poleDefect N x ≤ K →
          ∃ b : ℕ → ℝ,
            (∑ n ∈ Icc 1 N,
              (x n - ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  intro η hη hη1 K hK
  let C₀ := explicitRoughConditioningConstant
  have hC₀ := explicitRoughConditioningConstant_pos
  have hconditioning := smoothRoughPoleProjection_error_le_explicit
  let δ : ℝ := η / 8
  have hδ : 0 < δ := div_pos hη (by norm_num)
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith only [hη1]
  obtain ⟨P, A, R, hP, hA, hR, hAR, hEuler, hmeanBound, htailBound, hmodeBound, hRlog⟩ :=
    exists_quadratic_cutoffs hC₀ δ hδ hδ1 K hK
  have hRlog' : Real.log R ≤ quadraticConfinementConstant / η ^ 2 * (K + 1) := by
    refine hRlog.trans_eq ?_
    dsimp only [δ, quadraticConfinementConstant, C₀]
    field_simp [hη.ne']
    ring
  refine ⟨R, by omega, hRlog', fun N x hmass hdef => ?_⟩
  by_cases hRN : R ≤ N
  · have hPR : (1 : ℝ) < P := by exact_mod_cast hP
    have hAR' : (1 : ℝ) < A := by exact_mod_cast hA
    have hRR : (1 : ℝ) < R := by exact_mod_cast hR
    have hlogP : 0 < Real.log P := Real.log_pos hPR
    have hlogA : 0 < Real.log A := Real.log_pos hAR'
    have hlogR : 0 < Real.log R := Real.log_pos hRR
    have hL0 := ladderConstant_nonneg P
    have hAN : A ≤ N := by
      have hself : A ≤ A ^ 2 := by
        calc
          A = A * 1 := (Nat.mul_one A).symm
          _ ≤ A * A := Nat.mul_le_mul_left A (show 1 ≤ A by omega)
          _ = A ^ 2 := (pow_two A).symm
      exact (hself.trans hAR).trans hRN
    have hlogN : Real.log R ≤ Real.log (N + 1 : ℕ) :=
      Real.log_le_log (zero_lt_one.trans hRR)
        (by exact_mod_cast hRN.trans (Nat.le_succ N))
    have hNsieve : 2 * (sieveEuler (primePrefixSieve P) - Real.eulerMascheroniConstant) + 4 ≤
        Real.log (N + 1 : ℕ) := by
      rw [sieveEuler_primePrefix_sub_euler]
      exact hEuler.trans hlogN
    let f : ℕ → ℝ := smoothRoughMean P N x
    let g : ℕ → ℝ := fun n =>
      (if RHTower.Sieve.smoothPart (P - 1) n ≤ A then
        f (RHTower.Sieve.smoothPart (P - 1) n) else 0) / Real.sqrt n
    obtain ⟨b, hb⟩ := exists_sieveProfile_ramanujan_approximation_logMoment (primePrefixSieve P) hR
      ((hAR.trans hRN).trans (Nat.le_succ N)) hNsieve (fun a => f a)
    rw [sieveEuler_primePrefix_sub_euler] at hb
    have hprofileMoment :
        (∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
          (Real.log (a : ℕ) + ladderConstant P) * sieveClassMass (primePrefixSieve P) a N *
            f a ^ 2) ≤ 2 * K + 3 * ladderConstant P := by
      have hmoment := sum_smoothRoughMean_prefix_logMoment_le P N hAN x
      have hmass' := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL0)
      dsimp only [f]
      linarith only [hmoment, hmass', hdef]
    have hpacketError : (∑ n ∈ Icc 1 N,
        (g n - ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R,
          b m * ramanujanPoleProfile m n) ^ 2) ≤ δ := by
      dsimp only [g]
      rw [smoothProfile_ramanujan_error_eq_classMass P A R N f b]
      calc
        _ ≤ (16 / Real.log R) *
            ∑ a ∈ sieveClassPrefix (primePrefixSieve P) A,
              (Real.log (a : ℕ) + ladderConstant P) * sieveClassMass (primePrefixSieve P) a N *
                f a ^ 2 := hb
        _ ≤ (16 / Real.log R) * (2 * K + 3 * ladderConstant P) :=
          mul_le_mul_of_nonneg_left hprofileMoment (by positivity)
        _ = 16 * (2 * K + 3 * ladderConstant P) / Real.log R := by ring
        _ ≤ δ := hmodeBound
    have hmeanError :
        (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) ≤ δ := by
      exact (hconditioning P (by omega) N x).trans
        ((mul_le_mul_of_nonneg_left hdef (div_nonneg hC₀.le hlogP.le)).trans hmeanBound)
    have hsmoothTail :
        (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) ≤ δ := by
      have hpaid := mul_le_mul_of_nonneg_left hmass (mul_nonneg zero_le_two hL0)
      have hnum : 2 * poleDefect N x + 2 * ladderConstant P * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
          2 * K + 2 * ladderConstant P := by nlinarith only [hdef, hpaid]
      exact (sum_outside_smoothPart_le P N hA x).trans
        ((div_le_div_of_nonneg_right hnum hlogA.le).trans htailBound)
    have hpreError : (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) ≤ 2 * δ := by
      calc
        _ ≤ ∑ n ∈ Icc 1 N, ((x n - smoothRoughPoleProjection P N x n) ^ 2 +
            if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) := by
          refine sum_le_sum fun n _ => ?_
          by_cases hn : RHTower.Sieve.smoothPart (P - 1) n ≤ A
          · simp only [g, f, if_pos hn, if_neg (not_lt.mpr hn), add_zero,
              smoothRoughPoleProjection]
            exact le_rfl
          · simp only [g, if_neg hn, if_pos (not_le.mp hn), zero_div, sub_zero]
            exact le_add_of_nonneg_left (sq_nonneg _)
        _ = (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) +
            (∑ n ∈ Icc 1 N, if A < RHTower.Sieve.smoothPart (P - 1) n then x n ^ 2 else 0) :=
          sum_add_distrib
        _ ≤ δ + δ := add_le_add hmeanError hsmoothTail
        _ = 2 * δ := by ring
    refine ⟨extendSieveCoefficient (primePrefixSieve P) b, ?_⟩
    simp_rw [sum_extendSieveCoefficient_ramanujanPole (primePrefixSieve P) R b]
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          (2 * (x n - g n) ^ 2 + 2 * (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) :=
        sum_le_sum fun n _ => by
          nlinarith only [sq_nonneg ((x n - g n) - (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n))]
      _ = 2 * (∑ n ∈ Icc 1 N, (x n - g n) ^ 2) +
          2 * (∑ n ∈ Icc 1 N, (g n -
            ∑ m ∈ sieveClassPrefix (primePrefixSieve P) R, b m * ramanujanPoleProfile m n) ^ 2) := by
        simp only [sum_add_distrib, mul_sum]
      _ ≤ 2 * (2 * δ) + 2 * δ := add_le_add
        (mul_le_mul_of_nonneg_left hpreError zero_le_two)
        (mul_le_mul_of_nonneg_left hpacketError zero_le_two)
      _ ≤ η := by dsimp only [δ]; linarith only [hη]
  · obtain ⟨b, hb⟩ := exists_horizon_ramanujanPole_expansion N x
    refine ⟨fun m => if m ≤ N then b m else 0, ?_⟩
    have hNR : N ≤ R := (lt_of_not_ge hRN).le
    have hzero : (∑ n ∈ Icc 1 N,
        (x n - ∑ m ∈ Icc 1 R, (if m ≤ N then b m else 0) * ramanujanPoleProfile m n) ^ 2) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [sum_horizon_truncated_coefficients hNR, ← hb n hn, sub_self, zero_pow (by decide)]
    rw [hzero]
    exact hη.le

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
