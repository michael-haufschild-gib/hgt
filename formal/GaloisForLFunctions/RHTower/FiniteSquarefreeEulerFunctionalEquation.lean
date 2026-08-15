import GaloisForLFunctions.RHTower.FiniteSquarefreeEulerComplementRigidity
import GaloisForLFunctions.RHTower.DiagonalCharacter
import GaloisForLFunctions.Hurwitz.MulticolumnPowerOrbit

/-!
# Finite squarefree Euler functional equations

The literal finite Euler-product functional equation is reduced to the
Boolean-complement coefficient system at its negative-integer samples.
This restores the full converse and proves the exact zero-line conclusion.
-/

namespace RHTower

open scoped BigOperators
open Finset

noncomputable section

def finiteEulerPrimeProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

def finiteEulerCardProduct (P : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-s))

def finiteEulerCardFunctionalEquation (P : Finset ℕ) (a : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∀ s : ℂ,
    finiteEulerCardProduct P a s =
      ε * (finiteEulerPrimeProduct P : ℂ) ^ ((1 / 2 : ℂ) - s) *
        finiteEulerCardProduct P a (1 - s)

def finiteEulerNegativeSample (P : Finset ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∏ p ∈ P, (1 - a p * (p : ℂ) ^ m)

def finiteEulerReflectedNegativeSample (P : Finset ℕ) (a : ℕ → ℂ) (ε : ℂ) (m : ℕ) : ℂ :=
  ε * finiteEulerComplementRoot P * (∏ p ∈ P, (p : ℂ)) ^ m *
    ∏ p ∈ P, (1 - a p / (p : ℂ) ^ (m + 1))

theorem finiteEulerPrimeProduct_cast (P : Finset ℕ) :
    (finiteEulerPrimeProduct P : ℂ) = ∏ p ∈ P, (p : ℂ) := by
  simp [finiteEulerPrimeProduct]

theorem finiteEulerPrimeProduct_real (P : Finset ℕ) :
    finiteEulerPrimeMass P = (finiteEulerPrimeProduct P : ℝ) := by
  simp [finiteEulerPrimeMass, finiteEulerPrimeProduct]

theorem finiteEulerPrimeProduct_cpow (P : Finset ℕ) (s : ℂ) :
    (finiteEulerPrimeProduct P : ℂ) ^ s = ∏ p ∈ P, (p : ℂ) ^ s := by
  rw [finiteEulerPrimeProduct_cast]
  simpa using GaloisForLFunctions.prod_ofReal_cpow P (fun p => (p : ℝ))
    (fun p _ => Nat.cast_nonneg p) s

theorem finiteEulerPrimeProduct_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    0 < finiteEulerPrimeProduct P := by
  unfold finiteEulerPrimeProduct
  exact Finset.prod_pos fun p hp => (hP p hp).pos

theorem finiteEulerComplementRoot_eq_half_cpow
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    finiteEulerComplementRoot P =
      (finiteEulerPrimeProduct P : ℂ) ^ (1 / 2 : ℂ) := by
  rw [finiteEulerComplementRoot, finiteEulerPrimeProduct_real]
  rw [Real.sqrt_eq_rpow]
  rw [Complex.ofReal_cpow (le_of_lt (by exact_mod_cast finiteEulerPrimeProduct_pos hP))]
  norm_num

theorem finiteEulerCardProduct_negNat (P : Finset ℕ) (a : ℕ → ℂ) (m : ℕ) :
    finiteEulerCardProduct P a (-(m : ℂ)) = finiteEulerNegativeSample P a m := by
  unfold finiteEulerCardProduct finiteEulerNegativeSample
  apply Finset.prod_congr rfl
  intro p hp
  rw [show (-(-(m : ℂ)) : ℂ) = (m : ℂ) by ring, Complex.cpow_natCast]

theorem finiteEulerCardProduct_one_add_nat
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (m : ℕ) :
    finiteEulerCardProduct P a (1 + (m : ℂ)) =
      ∏ p ∈ P, (1 - a p / (p : ℂ) ^ (m + 1)) := by
  unfold finiteEulerCardProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  rw [show (-(1 + (m : ℂ)) : ℂ) = -(1 + (m : ℂ)) by ring, Complex.cpow_neg]
  rw [Complex.cpow_add 1 (m : ℂ) hp0, Complex.cpow_one, Complex.cpow_natCast]
  rw [show (p : ℂ) * (p : ℂ) ^ m = (p : ℂ) ^ (m + 1) by ring]
  simp [div_eq_mul_inv]

theorem finiteEulerCenteredPower_negNat
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (ε : ℂ) (m : ℕ) :
    ε * (finiteEulerPrimeProduct P : ℂ) ^ ((1 / 2 : ℂ) - (-(m : ℂ))) =
      ε * finiteEulerComplementRoot P * (∏ p ∈ P, (p : ℂ)) ^ m := by
  have hQ0 : (finiteEulerPrimeProduct P : ℂ) ≠ 0 := by
    exact_mod_cast (finiteEulerPrimeProduct_pos hP).ne'
  rw [show ((1 / 2 : ℂ) - (-(m : ℂ)) : ℂ) = (1 / 2 : ℂ) + (m : ℂ) by ring]
  rw [Complex.cpow_add (1 / 2 : ℂ) (m : ℂ) hQ0, Complex.cpow_natCast]
  rw [← finiteEulerComplementRoot_eq_half_cpow hP, finiteEulerPrimeProduct_cast]
  ring

theorem finiteEulerCardFunctionalEquation_negativeSample
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hFE : finiteEulerCardFunctionalEquation P a ε) (m : ℕ) :
    finiteEulerNegativeSample P a m = finiteEulerReflectedNegativeSample P a ε m := by
  have h := hFE (-(m : ℂ))
  rw [finiteEulerCardProduct_negNat, finiteEulerCenteredPower_negNat hP,
    show (1 - (-(m : ℂ)) : ℂ) = 1 + (m : ℂ) by ring,
    finiteEulerCardProduct_one_add_nat hP] at h
  exact h

def finiteEulerSubsetNode (S : Finset ℕ) : ℂ := ∏ p ∈ S, (p : ℂ)

theorem finiteEulerNegativeSample_expand (P : Finset ℕ) (a : ℕ → ℂ) (m : ℕ) :
    finiteEulerNegativeSample P a m =
      ∑ S ∈ P.powerset,
        (-1 : ℂ) ^ S.card * (∏ p ∈ S, a p) * finiteEulerSubsetNode S ^ m := by
  unfold finiteEulerNegativeSample finiteEulerSubsetNode
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one]
  simp_rw [Finset.prod_mul_distrib, ← Finset.prod_pow]
  ring_nf

theorem finiteEulerReflectedNegativeSample_preexpand
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ) (m : ℕ) :
    finiteEulerReflectedNegativeSample P a ε m =
      ε * finiteEulerComplementRoot P *
        ∏ p ∈ P, ((p : ℂ) ^ m - a p / (p : ℂ)) := by
  unfold finiteEulerReflectedNegativeSample
  rw [← Finset.prod_pow]
  calc
    (ε * finiteEulerComplementRoot P * ∏ p ∈ P, (p : ℂ) ^ m) *
        ∏ p ∈ P, (1 - a p / (p : ℂ) ^ (m + 1)) =
        ε * finiteEulerComplementRoot P *
          ((∏ p ∈ P, (p : ℂ) ^ m) *
            ∏ p ∈ P, (1 - a p / (p : ℂ) ^ (m + 1))) := by ring
    _ = ε * finiteEulerComplementRoot P *
          ∏ p ∈ P, ((p : ℂ) ^ m * (1 - a p / (p : ℂ) ^ (m + 1))) := by
      rw [← Finset.prod_mul_distrib]
    _ = ε * finiteEulerComplementRoot P *
          ∏ p ∈ P, ((p : ℂ) ^ m - a p / (p : ℂ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
      field_simp [hp0]
      ring

theorem finiteEulerReflectedNegativeSample_expand_raw
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ) (m : ℕ) :
    finiteEulerReflectedNegativeSample P a ε m =
      ε * finiteEulerComplementRoot P *
        ∑ T ∈ P.powerset,
          (-1 : ℂ) ^ T.card * finiteEulerSubsetNode (P \ T) ^ m *
            ∏ p ∈ T, a p / (p : ℂ) := by
  rw [finiteEulerReflectedNegativeSample_preexpand hP]
  rw [Finset.prod_sub]
  simp only [finiteEulerSubsetNode]
  simp_rw [← Finset.prod_pow]

theorem finiteEuler_sum_powerset_complement (P : Finset ℕ) (f : Finset ℕ → ℂ) :
    ∑ T ∈ P.powerset, f T = ∑ S ∈ P.powerset, f (P \ S) := by
  classical
  apply Finset.sum_bij' (fun T _ => P \ T) (fun S _ => P \ S)
  · intro T hT
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset)
  · intro S hS
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset)
  · intro T hT
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
  · intro S hS
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hS)
  · intro T hT
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)]

theorem finiteEulerComplementSign_sdiff
    {P S : Finset ℕ} (hS : S ⊆ P) :
    (-1 : ℂ) ^ (P \ S).card = (-1 : ℂ) ^ P.card * (-1 : ℂ) ^ S.card := by
  have hcard := Finset.card_sdiff_add_card_eq_card hS
  have hsq : (-1 : ℂ) ^ S.card * (-1 : ℂ) ^ S.card = 1 := by
    simpa [finiteEulerComplementSign] using finiteEulerComplementSign_sq S
  calc
    (-1 : ℂ) ^ (P \ S).card =
        (-1 : ℂ) ^ (P \ S).card *
          ((-1 : ℂ) ^ S.card * (-1 : ℂ) ^ S.card) := by rw [hsq, mul_one]
    _ = ((-1 : ℂ) ^ (P \ S).card * (-1 : ℂ) ^ S.card) *
          (-1 : ℂ) ^ S.card := by ring
    _ = (-1 : ℂ) ^ P.card * (-1 : ℂ) ^ S.card := by
      rw [← pow_add, hcard]

theorem finiteEulerReflectedNegativeSample_expand
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ) (m : ℕ) :
    finiteEulerReflectedNegativeSample P a ε m =
      ∑ S ∈ P.powerset,
        (-1 : ℂ) ^ S.card *
          finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε) *
            finiteEulerSubsetNode S ^ m := by
  rw [finiteEulerReflectedNegativeSample_expand_raw hP]
  let f : Finset ℕ → ℂ := fun T =>
    (-1 : ℂ) ^ T.card * finiteEulerSubsetNode (P \ T) ^ m *
      ∏ p ∈ T, a p / (p : ℂ)
  change ε * finiteEulerComplementRoot P * (∑ T ∈ P.powerset, f T) = _
  rw [finiteEuler_sum_powerset_complement P f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := Finset.mem_powerset.mp hS
  simp only [f, Finset.sdiff_sdiff_eq_self hSP]
  rw [Finset.prod_div_distrib, finiteEulerComplementCoefficient,
    finiteEulerFunctionalConstant, finiteEulerComplementSign_sdiff hSP]
  simp only [finiteEulerComplementSign]
  ring

theorem finiteEulerSubsetNode_injective
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Function.Injective (fun S : ↥P.powerset => finiteEulerSubsetNode S.1) := by
  intro S T hST
  apply Subtype.ext
  apply RHTower.Sieve.prod_injOn_powerset hP S.2 T.2
  dsimp [finiteEulerSubsetNode] at hST
  have hcastS : (∏ p ∈ (S.1 : Finset ℕ), (p : ℂ)) =
      ((∏ p ∈ (S.1 : Finset ℕ), p : ℕ) : ℂ) := by simp
  have hcastT : (∏ p ∈ (T.1 : Finset ℕ), (p : ℂ)) =
      ((∏ p ∈ (T.1 : Finset ℕ), p : ℕ) : ℂ) := by simp
  rw [hcastS, hcastT] at hST
  exact_mod_cast hST

theorem finiteEulerNegativeSamples_force_coefficients
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hsample : ∀ m : ℕ,
      finiteEulerNegativeSample P a m = finiteEulerReflectedNegativeSample P a ε m) :
    ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε) := by
  let c : ↥P.powerset → ℂ := fun S =>
    (-1 : ℂ) ^ S.1.card *
      ((∏ q ∈ S.1, a q) -
        finiteEulerComplementCoefficient P S.1 a (finiteEulerFunctionalConstant P ε))
  have hsum : ∀ m : ℕ,
      ∑ S : ↥P.powerset, c S * finiteEulerSubsetNode S.1 ^ m = 0 := by
    intro m
    have hEq := hsample m
    rw [finiteEulerNegativeSample_expand,
      finiteEulerReflectedNegativeSample_expand hP] at hEq
    have hraw :
        ∑ S ∈ P.powerset,
          ((-1 : ℂ) ^ S.card * (∏ q ∈ S, a q) -
            (-1 : ℂ) ^ S.card *
              finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε)) *
            finiteEulerSubsetNode S ^ m = 0 := by
      calc
        ∑ S ∈ P.powerset,
            ((-1 : ℂ) ^ S.card * (∏ q ∈ S, a q) -
              (-1 : ℂ) ^ S.card *
                finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε)) *
              finiteEulerSubsetNode S ^ m =
            ∑ S ∈ P.powerset,
              ((-1 : ℂ) ^ S.card * (∏ q ∈ S, a q) * finiteEulerSubsetNode S ^ m -
                (-1 : ℂ) ^ S.card *
                  finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε) *
                    finiteEulerSubsetNode S ^ m) := by
              apply Finset.sum_congr rfl
              intro S hS
              ring
        _ =
            (∑ S ∈ P.powerset,
              (-1 : ℂ) ^ S.card * (∏ q ∈ S, a q) * finiteEulerSubsetNode S ^ m) -
            ∑ S ∈ P.powerset,
              (-1 : ℂ) ^ S.card *
                finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε) *
                  finiteEulerSubsetNode S ^ m := by
              rw [Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr hEq
    rw [Finset.univ_eq_attach]
    calc
      ∑ S ∈ P.powerset.attach, c S * finiteEulerSubsetNode S.1 ^ m =
          ∑ S ∈ P.powerset,
            ((-1 : ℂ) ^ S.card *
              ((∏ q ∈ S, a q) -
                finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε))) *
              finiteEulerSubsetNode S ^ m := by
            simpa [c] using (Finset.sum_attach P.powerset
              (fun S => ((-1 : ℂ) ^ S.card *
                ((∏ q ∈ S, a q) -
                  finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε))) *
                    finiteEulerSubsetNode S ^ m))
      _ = ∑ S ∈ P.powerset,
            ((-1 : ℂ) ^ S.card * (∏ q ∈ S, a q) -
              (-1 : ℂ) ^ S.card *
                finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε)) *
              finiteEulerSubsetNode S ^ m := by
            apply Finset.sum_congr rfl
            intro S hS
            ring
      _ = 0 := hraw
  have hc := HurwitzJointOrbit.power_sum_coeff_zero_fintype
    (fun S : ↥P.powerset => finiteEulerSubsetNode S.1) c
    (finiteEulerSubsetNode_injective hP) hsum
  intro S hS
  let SS : ↥P.powerset := ⟨S, Finset.mem_powerset.mpr hS⟩
  have hz := congrFun hc SS
  dsimp [c, SS] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (pow_ne_zero _ (by norm_num)))

theorem finiteEulerLocalMirror
    {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : a ^ 2 = (p : ℂ)) (s : ℂ) :
    1 - a * (p : ℂ) ^ (-s) =
      (-a * (p : ℂ) ^ (-s)) * (1 - a * (p : ℂ) ^ (-(1 - s))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmode : (p : ℂ) ^ (-s) * (p : ℂ) ^ (-(1 - s)) = (p : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hp0]
    rw [show ((-s : ℂ) + -(1 - s)) = (-1 : ℂ) by ring, Complex.cpow_neg,
      Complex.cpow_one]
  calc
    1 - a * (p : ℂ) ^ (-s) =
        a ^ 2 * ((p : ℂ) ^ (-s) * (p : ℂ) ^ (-(1 - s))) -
          a * (p : ℂ) ^ (-s) := by
            rw [hmode, ha]
            field_simp [hp0]
    _ = (-a * (p : ℂ) ^ (-s)) * (1 - a * (p : ℂ) ^ (-(1 - s))) := by
      ring

theorem finiteEulerCardProduct_mirror
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ 2 = (p : ℂ)) (s : ℂ) :
    finiteEulerCardProduct P a s =
      finiteEulerComplementSign P * (∏ p ∈ P, a p) *
        (finiteEulerPrimeProduct P : ℂ) ^ (-s) * finiteEulerCardProduct P a (1 - s) := by
  unfold finiteEulerCardProduct
  calc
    ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-s)) =
        ∏ p ∈ P, ((-a p * (p : ℂ) ^ (-s)) *
          (1 - a p * (p : ℂ) ^ (-(1 - s)))) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact finiteEulerLocalMirror (hP p hp) (a p) (hlocal p hp) s
    _ = (∏ p ∈ P, -a p) * (∏ p ∈ P, (p : ℂ) ^ (-s)) *
          ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-(1 - s))) := by
          calc
            ∏ p ∈ P, ((-a p * (p : ℂ) ^ (-s)) *
                (1 - a p * (p : ℂ) ^ (-(1 - s)))) =
                ∏ p ∈ P, ((-a p) * (p : ℂ) ^ (-s) *
                  (1 - a p * (p : ℂ) ^ (-(1 - s)))) := by
                    apply Finset.prod_congr rfl
                    intro p hp
                    ring
            _ = (∏ p ∈ P, (-a p) * (p : ℂ) ^ (-s)) *
                ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-(1 - s))) := by
                  rw [Finset.prod_mul_distrib]
            _ = (∏ p ∈ P, -a p) * (∏ p ∈ P, (p : ℂ) ^ (-s)) *
                ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-(1 - s))) := by
                  rw [Finset.prod_mul_distrib]
    _ = finiteEulerComplementSign P * (∏ p ∈ P, a p) *
          (finiteEulerPrimeProduct P : ℂ) ^ (-s) *
            ∏ p ∈ P, (1 - a p * (p : ℂ) ^ (-(1 - s))) := by
          rw [Finset.prod_neg, finiteEulerComplementSign,
            ← finiteEulerPrimeProduct_cpow]

theorem finiteEulerCardFunctionalEquation_of_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ 2 = (p : ℂ)) :
    finiteEulerCardFunctionalEquation P a
      (finiteEulerComplementSign P * (∏ p ∈ P, a p) /
        finiteEulerComplementRoot P) := by
  intro s
  have hQ0 : (finiteEulerPrimeProduct P : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (finiteEulerPrimeProduct_pos hP))
  have hpow : (finiteEulerPrimeProduct P : ℂ) ^ ((1 / 2 : ℂ) - s) =
      finiteEulerComplementRoot P * (finiteEulerPrimeProduct P : ℂ) ^ (-s) := by
    rw [show ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + (-s) by ring,
      Complex.cpow_add _ _ hQ0, ← finiteEulerComplementRoot_eq_half_cpow hP]
  calc
    finiteEulerCardProduct P a s =
        finiteEulerComplementSign P * (∏ p ∈ P, a p) *
          (finiteEulerPrimeProduct P : ℂ) ^ (-s) *
            finiteEulerCardProduct P a (1 - s) :=
      finiteEulerCardProduct_mirror hP a hlocal s
    _ = (finiteEulerComplementSign P * (∏ p ∈ P, a p) /
          finiteEulerComplementRoot P) *
        (finiteEulerPrimeProduct P : ℂ) ^ ((1 / 2 : ℂ) - s) *
          finiteEulerCardProduct P a (1 - s) := by
        rw [hpow]
        field_simp [finiteEulerComplementRoot_ne_zero hP]

theorem finiteEulerCardFunctionalEquation_force_coefficients
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hFE : finiteEulerCardFunctionalEquation P a ε) :
    ∀ S, S ⊆ P → (∏ p ∈ S, a p) =
      finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε) := by
  apply finiteEulerNegativeSamples_force_coefficients hP a ε
  intro m
  exact finiteEulerCardFunctionalEquation_negativeSample hP a ε hFE m

theorem finiteEulerCardFunctionalEquation_force_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hε : ε ≠ 0) (hFE : finiteEulerCardFunctionalEquation P a ε) :
    ∀ p ∈ P, a p ^ 2 = (p : ℂ) := by
  apply finiteEulerComplement_coefficients_force_localSquares hP a
    (finiteEulerFunctionalConstant P ε)
  · unfold finiteEulerFunctionalConstant
    exact mul_ne_zero (mul_ne_zero hε (by simp [finiteEulerComplementSign]))
      (finiteEulerComplementRoot_ne_zero hP)
  · exact finiteEulerCardFunctionalEquation_force_coefficients hP a ε hFE

theorem finiteEulerCardFunctionalEquation_epsilon_formula
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hFE : finiteEulerCardFunctionalEquation P a ε) :
    ε = finiteEulerComplementSign P * (∏ p ∈ P, a p) /
      finiteEulerComplementRoot P := by
  exact finiteEulerComplement_epsilon_formula hP a ε
    (finiteEulerCardFunctionalEquation_force_coefficients hP a ε hFE)

theorem finiteEulerCardFunctionalEquation_epsilon_sq
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hε : ε ≠ 0) (hFE : finiteEulerCardFunctionalEquation P a ε) :
    ε ^ 2 = 1 := by
  exact finiteEulerComplement_epsilon_sq hP a ε hε
    (finiteEulerCardFunctionalEquation_force_coefficients hP a ε hFE)

theorem finiteEulerCardProduct_zero_realPart
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ 2 = (p : ℂ)) {s : ℂ}
    (hz : finiteEulerCardProduct P a s = 0) :
    s.re = 1 / 2 := by
  unfold finiteEulerCardProduct at hz
  rcases Finset.prod_eq_zero_iff.mp hz with ⟨p, hp, hpzero⟩
  have hprime : p.Prime := hP p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hpC : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_num
  have hmul : a p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hpzero).symm
  have hnorm : ‖a p‖ * (p : ℝ) ^ (-s.re) = 1 := by
    calc
      ‖a p‖ * (p : ℝ) ^ (-s.re) = ‖a p * (p : ℂ) ^ (-s)‖ := by
        rw [norm_mul, hpC, Complex.norm_cpow_eq_rpow_re_of_pos hpR]
        simp
      _ = ‖(1 : ℂ)‖ := by rw [hmul]
      _ = 1 := norm_one
  have hnormsq : ‖a p‖ ^ 2 = (p : ℝ) := by
    calc
      ‖a p‖ ^ 2 = ‖a p ^ 2‖ := by rw [norm_pow]
      _ = ‖(p : ℂ)‖ := by rw [hlocal p hp]
      _ = (p : ℝ) := by
        rw [hpC, Complex.norm_real]
        exact abs_of_nonneg (Nat.cast_nonneg p)
  have hsq : (p : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2 = 1 := by
    calc
      (p : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2 =
          (‖a p‖ * (p : ℝ) ^ (-s.re)) ^ 2 := by
            rw [mul_pow, hnormsq]
      _ = 1 := by
        rw [hnorm]
        norm_num
  have htriple : (p : ℝ) * (p : ℝ) ^ (-s.re) * (p : ℝ) ^ (-s.re) = 1 := by
    calc
      (p : ℝ) * (p : ℝ) ^ (-s.re) * (p : ℝ) ^ (-s.re) =
          (p : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2 := by ring
      _ = 1 := hsq
  have hrpow : (p : ℝ) ^ (((1 : ℝ) + (-s.re)) + (-s.re)) = (p : ℝ) ^ (0 : ℝ) := by
    calc
      (p : ℝ) ^ (((1 : ℝ) + (-s.re)) + (-s.re)) =
          (p : ℝ) ^ ((1 : ℝ) + (-s.re)) * (p : ℝ) ^ (-s.re) := by
            rw [Real.rpow_add hpR]
      _ = ((p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-s.re)) *
          (p : ℝ) ^ (-s.re) := by rw [Real.rpow_add hpR]
      _ = 1 := by simpa only [Real.rpow_one] using htriple
      _ = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  have hpneone : (p : ℝ) ≠ 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    linarith
  have hexp : ((1 : ℝ) + (-s.re)) + (-s.re) = 0 :=
    (Real.rpow_right_inj hpR hpneone).mp hrpow
  linarith

theorem finiteEulerCardFunctionalEquation_rigidity
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hε : ε ≠ 0) (hFE : finiteEulerCardFunctionalEquation P a ε) :
    (∀ p ∈ P, a p ^ 2 = (p : ℂ)) ∧
      ε = finiteEulerComplementSign P * (∏ p ∈ P, a p) /
        finiteEulerComplementRoot P ∧ ε ^ 2 = 1 := by
  exact ⟨finiteEulerCardFunctionalEquation_force_localSquares hP a ε hε hFE,
    finiteEulerCardFunctionalEquation_epsilon_formula hP a ε hFE,
    finiteEulerCardFunctionalEquation_epsilon_sq hP a ε hε hFE⟩

theorem finiteEulerCardFunctionalEquation_zero_realPart
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hε : ε ≠ 0) (hFE : finiteEulerCardFunctionalEquation P a ε) {s : ℂ}
    (hz : finiteEulerCardProduct P a s = 0) :
    s.re = 1 / 2 := by
  exact finiteEulerCardProduct_zero_realPart hP a
    (finiteEulerCardFunctionalEquation_force_localSquares hP a ε hε hFE) hz

end

end RHTower
