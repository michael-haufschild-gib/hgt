import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationLocalAnalyticBranchNoGo
import GaloisForLFunctions.RHTower.SuzukiArchimedeanParityHankelInfiniteRank
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# HB pre-divisor finite Schwarz-polarized infinite-rank no-go

The exact moving-horizon/AIME susceptibility, polarized as a two-real-variable sum kernel,
has infinite separation rank on the physical open square `(0, 1/2)²`.  Distinct translates
are separated by their distinct rational poles after analytic continuation and denominator
clearing.  Therefore no finite-dimensional Hermitian or Schwarz-polarized left-QNM/right-response
pairing can supply the required HB compensation.

The surviving class must be genuinely infinite-dimensional, nonseparated, singular,
support-changing, or sheet-changing.
-/

open Complex Set

namespace RHTower

noncomputable section

def d4PreDivisorOpticalCancellationReducedNumerator (z : ℂ) : ℂ :=
  54 * d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
      (d4PreDivisorHorizonAngularShiftHolomorphic z)
      (d4PreDivisorReflectedHorizonAngularShiftHolomorphic z) *
    (2 - z) * (z + 1)

def d4PreDivisorOpticalCancellationReducedDenominator (z : ℂ) : ℂ :=
  d4PreDivisorHorizonAngularShiftHolomorphic z ^ 2 *
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic z ^ 2

@[simp] theorem d4PreDivisorOpticalCancellationReducedNumerator_zero :
    d4PreDivisorOpticalCancellationReducedNumerator 0 = 864 := by
  norm_num [d4PreDivisorOpticalCancellationReducedNumerator,
    d4EventHorizonThirdMassParityCrossNumeratorHolomorphic,
    d4PreDivisorHorizonAngularShiftHolomorphic,
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic]

theorem d4PreDivisorOpticalCancellationHolomorphicContinuation_eq_reduced
    (z : ℂ)
    (hA : d4PreDivisorHorizonAngularShiftHolomorphic z ≠ 0)
    (hB : d4PreDivisorReflectedHorizonAngularShiftHolomorphic z ≠ 0) :
    d4PreDivisorOpticalCancellationHolomorphicContinuation z =
      d4PreDivisorOpticalCancellationReducedNumerator z /
        d4PreDivisorOpticalCancellationReducedDenominator z := by
  unfold d4PreDivisorOpticalCancellationHolomorphicContinuation
  dsimp only
  rw [show z * (1 - z) * (2 - z) * (3 - z) * (z + 1) * (z + 2) =
      d4PreDivisorHorizonAngularShiftHolomorphic z *
        d4PreDivisorReflectedHorizonAngularShiftHolomorphic z *
          (2 - z) * (z + 1) by
    unfold d4PreDivisorHorizonAngularShiftHolomorphic
      d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    ring]
  unfold d4PreDivisorOpticalCancellationReducedNumerator
    d4PreDivisorOpticalCancellationReducedDenominator
  field_simp [hA, hB]
  ring

theorem d4PreDivisorOpticalCancellationReducedDenominator_ofReal_ne_zero
    {t : ℝ} (ht : t ≠ 0) (htLower : -(1 / 4 : ℝ) < t)
    (htUpper : t < 1 / 4) :
    d4PreDivisorOpticalCancellationReducedDenominator (t : ℂ) ≠ 0 := by
  unfold d4PreDivisorOpticalCancellationReducedDenominator
    d4PreDivisorHorizonAngularShiftHolomorphic
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic
  apply mul_ne_zero <;> apply pow_ne_zero 2 <;> apply mul_ne_zero
  · exact_mod_cast ht
  · exact_mod_cast (show (3 : ℝ) - t ≠ 0 by linarith)
  · exact_mod_cast (show (1 : ℝ) - t ≠ 0 by linarith)
  · exact_mod_cast (show (2 : ℝ) + t ≠ 0 by linarith)

@[simp] theorem d4PreDivisorOpticalCancellationReducedDenominator_zero :
    d4PreDivisorOpticalCancellationReducedDenominator 0 = 0 := by
  norm_num [d4PreDivisorOpticalCancellationReducedDenominator,
    d4PreDivisorHorizonAngularShiftHolomorphic,
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic]

def d4PreDivisorOpticalCancellationPolarizedKernel (x y : ℝ) : ℂ :=
  d4PreDivisorOpticalCancellationHolomorphicContinuation
    ((((x + y) / 2 : ℝ) : ℂ))

def d4PreDivisorOpticalCancellationClearedTranslateRelation
    {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, c j * d4PreDivisorOpticalCancellationReducedNumerator
      ((z + (y j : ℂ)) / 2) *
    ∏ k ∈ Finset.univ.erase j,
      d4PreDivisorOpticalCancellationReducedDenominator
        ((z + (y k : ℂ)) / 2)

def d4PreDivisorOpticalCancellationTranslatePacket
    {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, c j * d4PreDivisorOpticalCancellationHolomorphicContinuation
    ((z + (y j : ℂ)) / 2)

theorem fullDenominator_mul_d4PreDivisorOpticalCancellationTranslatePacket
    {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ)
    (hshifts : ∀ j,
      d4PreDivisorHorizonAngularShiftHolomorphic
          ((z + (y j : ℂ)) / 2) ≠ 0 ∧
        d4PreDivisorReflectedHorizonAngularShiftHolomorphic
          ((z + (y j : ℂ)) / 2) ≠ 0) :
    (∏ k, d4PreDivisorOpticalCancellationReducedDenominator
        ((z + (y k : ℂ)) / 2)) *
      d4PreDivisorOpticalCancellationTranslatePacket y c z =
        d4PreDivisorOpticalCancellationClearedTranslateRelation y c z := by
  rw [d4PreDivisorOpticalCancellationTranslatePacket, Finset.mul_sum,
    d4PreDivisorOpticalCancellationClearedTranslateRelation]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj,
    Finset.sdiff_singleton_eq_erase]
  have hA := (hshifts j).1
  have hB := (hshifts j).2
  have hD : d4PreDivisorOpticalCancellationReducedDenominator
      ((z + (y j : ℂ)) / 2) ≠ 0 := by
    unfold d4PreDivisorOpticalCancellationReducedDenominator
    exact mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)
  rw [d4PreDivisorOpticalCancellationHolomorphicContinuation_eq_reduced _ hA hB]
  field_simp [hD]

theorem differentiable_d4PreDivisorOpticalCancellationClearedTranslateRelation
    {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) :
    Differentiable ℂ
      (d4PreDivisorOpticalCancellationClearedTranslateRelation y c) := by
  unfold d4PreDivisorOpticalCancellationClearedTranslateRelation
    d4PreDivisorOpticalCancellationReducedNumerator
    d4PreDivisorOpticalCancellationReducedDenominator
    d4PreDivisorHorizonAngularShiftHolomorphic
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
  fun_prop

theorem d4PreDivisorOpticalCancellationClearedTranslateRelation_eq_zero_of_posReal_lt
    {n : ℕ} {y : Fin n → ℝ} {c : Fin n → ℂ}
    (hyPos : ∀ j, 0 < y j) (hyLt : ∀ j, y j < 1 / 2)
    (hpacket : ∀ x : ℝ, 0 < x → x < 1 / 2 →
      d4PreDivisorOpticalCancellationTranslatePacket y c (x : ℂ) = 0) :
    ∀ z, d4PreDivisorOpticalCancellationClearedTranslateRelation y c z = 0 := by
  apply GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    (differentiable_d4PreDivisorOpticalCancellationClearedTranslateRelation y c)
    (t₀ := (1 / 4 : ℝ)) (r := (1 / 4 : ℝ)) (by norm_num)
  intro x hx
  rw [abs_lt] at hx
  have hxPos : 0 < x := by linarith
  have hxLt : x < 1 / 2 := by linarith
  have hshifts : ∀ j,
      d4PreDivisorHorizonAngularShiftHolomorphic
          (((x : ℂ) + (y j : ℂ)) / 2) ≠ 0 ∧
        d4PreDivisorReflectedHorizonAngularShiftHolomorphic
          (((x : ℂ) + (y j : ℂ)) / 2) ≠ 0 := by
    intro j
    constructor
    · unfold d4PreDivisorHorizonAngularShiftHolomorphic
      apply mul_ne_zero
      · exact_mod_cast (show (x + y j) / 2 ≠ 0 by linarith [hyPos j])
      · exact_mod_cast (show (3 : ℝ) - (x + y j) / 2 ≠ 0 by
          linarith [hyLt j])
    · unfold d4PreDivisorReflectedHorizonAngularShiftHolomorphic
      apply mul_ne_zero
      · exact_mod_cast (show (1 : ℝ) - (x + y j) / 2 ≠ 0 by
          linarith [hyLt j])
      · exact_mod_cast (show (2 : ℝ) + (x + y j) / 2 ≠ 0 by
          linarith [hyPos j])
  have hclear :=
    fullDenominator_mul_d4PreDivisorOpticalCancellationTranslatePacket
      y c (x : ℂ) hshifts
  rw [hpacket x hxPos hxLt, mul_zero] at hclear
  exact hclear.symm

theorem d4PreDivisorOpticalCancellationTranslatePacket_coeff_zero_of_posReal_lt
    {n : ℕ} {y : Fin n → ℝ} {c : Fin n → ℂ}
    (hy : Function.Injective y)
    (hyPos : ∀ j, 0 < y j) (hyLt : ∀ j, y j < 1 / 2)
    (hpacket : ∀ x : ℝ, 0 < x → x < 1 / 2 →
      d4PreDivisorOpticalCancellationTranslatePacket y c (x : ℂ) = 0) :
    c = 0 := by
  have hzero :=
    d4PreDivisorOpticalCancellationClearedTranslateRelation_eq_zero_of_posReal_lt
      hyPos hyLt hpacket
  funext j
  have hother : ∀ l ∈ Finset.univ, l ≠ j →
      c l * d4PreDivisorOpticalCancellationReducedNumerator
          ((-(y j : ℂ) + (y l : ℂ)) / 2) *
        ∏ k ∈ Finset.univ.erase l,
          d4PreDivisorOpticalCancellationReducedDenominator
            ((-(y j : ℂ) + (y k : ℂ)) / 2) = 0 := by
    intro l hl hlj
    have hjmem : j ∈ Finset.univ.erase l := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hlj, Finset.mem_univ j⟩
    have hprod :
        (∏ k ∈ Finset.univ.erase l,
          d4PreDivisorOpticalCancellationReducedDenominator
            ((-(y j : ℂ) + (y k : ℂ)) / 2)) = 0 := by
      apply Finset.prod_eq_zero hjmem
      simp
    rw [hprod, mul_zero]
  have hsingle :
      (∑ l, c l * d4PreDivisorOpticalCancellationReducedNumerator
          ((-(y j : ℂ) + (y l : ℂ)) / 2) *
        ∏ k ∈ Finset.univ.erase l,
          d4PreDivisorOpticalCancellationReducedDenominator
            ((-(y j : ℂ) + (y k : ℂ)) / 2)) =
      c j * d4PreDivisorOpticalCancellationReducedNumerator 0 *
        ∏ k ∈ Finset.univ.erase j,
          d4PreDivisorOpticalCancellationReducedDenominator
            ((-(y j : ℂ) + (y k : ℂ)) / 2) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l hl hlj
      exact hother l hl hlj
    · simp
  have hprodNe :
      (∏ k ∈ Finset.univ.erase j,
        d4PreDivisorOpticalCancellationReducedDenominator
          ((-(y j : ℂ) + (y k : ℂ)) / 2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hyNe : y k ≠ y j := by
      intro heq
      exact hkj (hy heq)
    have hD :=
      d4PreDivisorOpticalCancellationReducedDenominator_ofReal_ne_zero
        (t := (y k - y j) / 2)
        (div_ne_zero (sub_ne_zero.mpr hyNe) (by norm_num))
        (by linarith [hyPos k, hyPos j, hyLt k, hyLt j])
        (by linarith [hyPos k, hyPos j, hyLt k, hyLt j])
    simpa [Complex.ofReal_sub, Complex.ofReal_div, sub_eq_add_neg,
      add_comm] using hD
  have hj := hzero (-(y j : ℂ))
  rw [d4PreDivisorOpticalCancellationClearedTranslateRelation,
    hsingle] at hj
  have hcP := (mul_eq_zero.mp hj).resolve_right hprodNe
  exact (mul_eq_zero.mp hcP).resolve_right (by norm_num)

theorem d4PreDivisorOpticalCancellationPolarizedKernel_not_hasPositiveOpenSquareSeparationRankAtMost
    (r : ℕ) :
    ¬ HasPositiveOpenSquareSeparationRankAtMost r (1 / 2)
      d4PreDivisorOpticalCancellationPolarizedKernel := by
  rintro ⟨f, g, hsep⟩
  let y : Fin (r + 1) → ℝ := fun j =>
    (1 / 2 : ℝ) * (((j : ℕ) : ℝ) + 1) / (r + 2)
  have hy : Function.Injective y := by
    intro j k hjk
    apply Fin.ext
    have hden : ((r + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [y] at hjk
    field_simp [hden] at hjk
    have hcast : ((j : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
      nlinarith
    exact_mod_cast hcast
  have hyPos : ∀ j, 0 < y j := by
    intro j
    dsimp only [y]
    positivity
  have hyLt : ∀ j, y j < 1 / 2 := by
    intro j
    have hj : (j : ℕ) + 1 < r + 2 := by omega
    dsimp only [y]
    change (1 / 2 : ℝ) * (((j : ℕ) : ℝ) + 1) /
      (((r : ℕ) : ℝ) + 2) < 1 / 2
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 2)]
    have hjReal : (((j : ℕ) : ℝ) + 1) < (r + 2 : ℕ) := by
      exact_mod_cast hj
    norm_num at hjReal ⊢
    linarith
  let T : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun c k => ∑ j, c j * g k (y j)
      map_add' := by
        intro c d
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  have hrank :
      Module.finrank ℂ (Fin r → ℂ) <
        Module.finrank ℂ (Fin (r + 1) → ℂ) := by
    simp
  have hker : LinearMap.ker T ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hrank
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨c, hcKer, hcNe⟩ := hker
  have hTc : T c = 0 := LinearMap.mem_ker.mp hcKer
  have hrow (k : Fin r) : (∑ j, c j * g k (y j)) = 0 :=
    congrFun hTc k
  have hpacket : ∀ x : ℝ, 0 < x → x < 1 / 2 →
      d4PreDivisorOpticalCancellationTranslatePacket y c (x : ℂ) = 0 := by
    intro x hx hxb
    rw [d4PreDivisorOpticalCancellationTranslatePacket]
    calc
      (∑ j, c j * d4PreDivisorOpticalCancellationHolomorphicContinuation
          (((x : ℂ) + (y j : ℂ)) / 2)) =
          ∑ j, c j * ∑ k, f k x * g k (y j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show d4PreDivisorOpticalCancellationHolomorphicContinuation
              (((x : ℂ) + (y j : ℂ)) / 2) =
            d4PreDivisorOpticalCancellationPolarizedKernel x (y j) by
          simp only [d4PreDivisorOpticalCancellationPolarizedKernel,
            Complex.ofReal_add, Complex.ofReal_div,
            Complex.ofReal_ofNat]]
        rw [hsep x (y j) hx hxb (hyPos j) (hyLt j)]
      _ = ∑ j, ∑ k, c j * (f k x * g k (y j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, c j * (f k x * g k (y j)) :=
        Finset.sum_comm
      _ = ∑ k, f k x * ∑ j, c j * g k (y j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by
        simp_rw [hrow]
        simp
  have hcZero :=
    d4PreDivisorOpticalCancellationTranslatePacket_coeff_zero_of_posReal_lt
      hy hyPos hyLt hpacket
  exact hcNe hcZero

/-- Closed certificate killing every finite-dimensional Schwarz-polarized compensation of the
third-mass pre-divisor susceptibility on the physical open square. -/
def D4HBPreDivisorFiniteSchwarzPolarizedRouteKilled : Prop :=
  ∀ r : ℕ, ¬ HasPositiveOpenSquareSeparationRankAtMost r (1 / 2)
    d4PreDivisorOpticalCancellationPolarizedKernel

theorem d4HBPreDivisorFiniteSchwarzPolarizedRouteKilled :
    D4HBPreDivisorFiniteSchwarzPolarizedRouteKilled := by
  intro r
  exact
    d4PreDivisorOpticalCancellationPolarizedKernel_not_hasPositiveOpenSquareSeparationRankAtMost r

end


end RHTower
