import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# The residue profile of balanced products

Multiplication of two uniform residue rows is not uniform. Its exact
Fourier coefficient is the modulus times a gcd. This is the coherent
arithmetic profile that ordinary short-window smoothing erases.
-/

namespace GaloisForLFunctions.Goldbach

open Finset RHTower.Sieve
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Ordered multiplication fibres in the complete residue square. -/
def productResidueCount (q : ℕ+) (r : ZMod (q : ℕ)) : ℕ :=
  ∑ a : ZMod (q : ℕ), ∑ b : ZMod (q : ℕ), if a * b = r then 1 else 0

/-- Multiplicity of zero in multiplication by one residue. -/
def productZeroMultiplicity (q : ℕ+) (h : ZMod (q : ℕ)) : ℕ :=
  Fintype.card {a : ZMod (q : ℕ) // h * a = 0}

theorem productZeroMultiplicity_eq_gcd (q : ℕ+) (h : ZMod (q : ℕ)) :
    productZeroMultiplicity q h = Nat.gcd (q : ℕ) h.val := by
  have he : {a : ZMod (q : ℕ) // h * a = 0} ≃
      (nsmulAddMonoidHom h.val : ZMod (q : ℕ) →+ ZMod (q : ℕ)).ker :=
    Equiv.subtypeEquivRight fun a => by
      simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
        nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hc := Nat.card_congr he
  have hk := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (q : ℕ)) h.val
  simpa only [productZeroMultiplicity, Nat.card_eq_fintype_card, ZMod.card] using hc.trans hk

/-- Exact pushforward of arbitrary observations through residue multiplication. -/
theorem productResidueCount_pairing (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) * f r) =
      ∑ a : ZMod (q : ℕ), ∑ b : ZMod (q : ℕ), f (a * b) := by
  classical
  simp only [productResidueCount, Nat.cast_sum, apply_ite, Nat.cast_one,
    Nat.cast_zero, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  simp

theorem sum_productResidueCount (q : ℕ+) :
    (∑ r : ZMod (q : ℕ), productResidueCount q r) = (q : ℕ) ^ 2 := by
  have h := productResidueCount_pairing q (fun _ => 1)
  simp only [mul_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  rw [pow_two]
  exact_mod_cast h

/-- Every frequency retains its exact nonunit multiplicity. -/
theorem productResidueCount_fourier (q : ℕ+) (h : ZMod (q : ℕ)) :
    (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) *
      ZMod.stdAddChar (h * r)) =
        (q : ℕ) * (Nat.gcd (q : ℕ) h.val : ℂ) := by
  classical
  rw [productResidueCount_pairing]
  have hinner (a : ZMod (q : ℕ)) :
      (∑ b : ZMod (q : ℕ), ZMod.stdAddChar (h * (a * b))) =
        if h * a = 0 then ((q : ℕ) : ℂ) else 0 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm, apply_ite, Nat.cast_zero] using
      sum_stdAddChar_mul (q : ℕ) (h * a)
  simp_rw [hinner]
  rw [← productZeroMultiplicity_eq_gcd, productZeroMultiplicity, Fintype.card_subtype]
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- Inverse Fourier reconstruction of the entire arithmetic product profile. -/
theorem productResidueCount_eq_gcdFourier (q : ℕ+) (r : ZMod (q : ℕ)) :
    (productResidueCount q r : ℂ) =
      ∑ h : ZMod (q : ℕ), (Nat.gcd (q : ℕ) h.val : ℂ) *
        ZMod.stdAddChar (-(h * r)) := by
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
  have hi : ZMod.dft.symm (fun r => (productResidueCount q r : ℂ)) =
      fun h : ZMod (q : ℕ) => (Nat.gcd (q : ℕ) h.val : ℂ) := by
    funext h
    rw [ZMod.invDFT_apply]
    simp only [smul_eq_mul]
    have hs : (∑ j : ZMod (q : ℕ), ZMod.stdAddChar (j * h) *
        (productResidueCount q j : ℂ)) =
        ((q : ℕ) : ℂ) * (Nat.gcd (q : ℕ) h.val : ℂ) := by
      simpa only [mul_comm] using productResidueCount_fourier q h
    rw [hs, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  have h := congrArg (fun f : ZMod (q : ℕ) → ℂ => ZMod.dft f) hi
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_comm] using congrFun h r

/-- The local nonuniformity measured before pairing with an arithmetic row. -/
def productResidueCenteredEnergy (q : ℕ+) : ℝ :=
  ∑ r : ZMod (q : ℕ), ((productResidueCount q r : ℝ) - (q : ℕ)) ^ 2

/-- Parseval isolates the full gcd spectrum, with the constant mode removed exactly. -/
theorem productResidueCenteredEnergy_eq_gcd (q : ℕ+) :
    productResidueCenteredEnergy q =
      (q : ℕ) * ((∑ h : ZMod (q : ℕ), (Nat.gcd (q : ℕ) h.val : ℝ) ^ 2) -
        ((q : ℕ) : ℝ) ^ 2) := by
  have hp := sum_normSq_weighted_stdAddChar_mul_of_injective
    (q : ℕ) (fun r : ZMod (q : ℕ) => r) Function.injective_id
    (fun r => (productResidueCount q r : ℂ))
  simp_rw [productResidueCount_fourier] at hp
  have hn (a b : ℕ) : Complex.normSq ((a : ℂ) * b) =
      (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := by simp [Complex.normSq, pow_two]; ring
  have hn' (a : ℕ) : Complex.normSq (a : ℂ) = (a : ℝ) ^ 2 := by
    simp [Complex.normSq, pow_two]
  simp_rw [hn, hn'] at hp
  rw [← mul_sum] at hp
  have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  have hsq : (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℝ) ^ 2) =
      ((q : ℕ) : ℝ) * ∑ h : ZMod (q : ℕ), (Nat.gcd (q : ℕ) h.val : ℝ) ^ 2 := by
    apply mul_left_cancel₀ hq
    simpa only [pow_two, mul_assoc] using hp.symm
  have hm : (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℝ)) =
      ((q : ℕ) : ℝ) ^ 2 := by exact_mod_cast sum_productResidueCount q
  have he (r : ZMod (q : ℕ)) :
      ((productResidueCount q r : ℝ) - (q : ℕ)) ^ 2 =
        (productResidueCount q r : ℝ) ^ 2 -
          (2 * ((q : ℕ) : ℝ)) * productResidueCount q r + ((q : ℕ) : ℝ) ^ 2 := by ring
  simp only [productResidueCenteredEnergy, he, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, sum_const, card_univ, ZMod.card, nsmul_eq_mul, hsq, hm]
  ring

/-- A complete number of residue blocks, with an arbitrary starting phase. -/
theorem sum_residue_blocks (q : ℕ+) (k : ℕ) (c : ZMod (q : ℕ))
    (f : ZMod (q : ℕ) → ℂ) :
    (∑ i ∈ range ((q : ℕ) * k), f ((i : ZMod (q : ℕ)) + c)) =
      (k : ℂ) * ∑ r : ZMod (q : ℕ), f r := by
  have hbase (g : ZMod (q : ℕ) → ℂ) :
      (∑ i ∈ range (q : ℕ), g (i : ZMod (q : ℕ))) =
        ∑ r : ZMod (q : ℕ), g r := by
    apply sum_bij (fun (i : ℕ) _ => (i : ZMod (q : ℕ)))
    · intro i hi
      exact mem_univ _
    · intro i hi j hj hij
      have hv := congrArg ZMod.val hij
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hi),
        Nat.mod_eq_of_lt (mem_range.mp hj)] using hv
    · intro r _
      exact ⟨r.val, mem_range.mpr r.val_lt, ZMod.natCast_zmod_val r⟩
    · intro i hi
      rfl
  have hshift : (∑ r : ZMod (q : ℕ), f (r + c)) = ∑ r : ZMod (q : ℕ), f r :=
    Fintype.sum_equiv (Equiv.addRight c) _ f (fun _ => rfl)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    rw [hbase (fun r => f (r + c)), hshift]
    push_cast
    ring

/-- The actual balanced interval `(qk,2qk]`, observed modulo `q`. -/
def balancedProductResidueCount (q : ℕ+) (k : ℕ) (r : ZMod (q : ℕ)) : ℕ :=
  ∑ i ∈ range ((q : ℕ) * k), ∑ j ∈ range ((q : ℕ) * k),
    if ((((q : ℕ) * k + i + 1) * ((q : ℕ) * k + j + 1) : ℕ) : ZMod (q : ℕ)) = r
    then 1 else 0

/-- Balanced products realize the local profile exactly, including nonunit residues. -/
theorem balancedProduct_periodic_pairing (q : ℕ+) (k : ℕ)
    (f : ZMod (q : ℕ) → ℂ) :
    (∑ i ∈ range ((q : ℕ) * k), ∑ j ∈ range ((q : ℕ) * k),
      f (((((q : ℕ) * k + i + 1) * ((q : ℕ) * k + j + 1)) : ℕ) : ZMod (q : ℕ))) =
        (k : ℂ) ^ 2 * ∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) * f r := by
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self,
    zero_mul, zero_add]
  have hin (a : ZMod (q : ℕ)) :
      (∑ j ∈ range ((q : ℕ) * k), f (a * ((j : ZMod (q : ℕ)) + 1))) =
        (k : ℂ) * ∑ b : ZMod (q : ℕ), f (a * b) :=
    sum_residue_blocks q k 1 (fun r => f (a * r))
  simp_rw [hin]
  rw [← mul_sum]
  rw [sum_residue_blocks q k 1 (fun r => ∑ b : ZMod (q : ℕ), f (r * b))]
  rw [productResidueCount_pairing]
  ring

theorem balancedProductResidueCount_eq (q : ℕ+) (k : ℕ) (r : ZMod (q : ℕ)) :
    balancedProductResidueCount q k r = k ^ 2 * productResidueCount q r := by
  classical
  have h := balancedProduct_periodic_pairing q k (fun x => if x = r then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true] at h
  exact_mod_cast h

/-- Every nontrivial modulus has a nonconstant multiplication profile. -/
theorem productResidueCenteredEnergy_eq_zero_iff (q : ℕ+) :
    productResidueCenteredEnergy q = 0 ↔ (q : ℕ) = 1 := by
  constructor
  · intro h
    by_contra hq
    have hz (r : ZMod (q : ℕ)) :
        ((productResidueCount q r : ℝ) - (q : ℕ)) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg
        ((productResidueCount q r : ℝ) - (q : ℕ)))).mp h r (mem_univ _)
    have hc (r : ZMod (q : ℕ)) : (productResidueCount q r : ℂ) = (q : ℕ) := by
      have hr := sub_eq_zero.mp (sq_eq_zero_iff.mp (hz r))
      exact_mod_cast hr
    have ho : (1 : ZMod (q : ℕ)) ≠ 0 := fun h => hq (ZMod.one_eq_zero_iff.mp h)
    have hs := sum_stdAddChar_mul (q : ℕ) (1 : ZMod (q : ℕ))
    simp only [mul_one, if_neg ho, Nat.cast_zero] at hs
    have hp := productResidueCount_fourier q 1
    simp only [hc, ← mul_sum, one_mul, hs, mul_zero, ZMod.val_one'' hq,
      Nat.gcd_one_right, Nat.cast_one, mul_one] at hp
    have hn : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
    exact hn hp.symm
  · intro hq
    have h : q = 1 := Subtype.ext hq
    subst q
    have hv (a : ZMod ((1 : ℕ+) : ℕ)) : a.val = 0 := by
      have ha := a.val_lt
      change a.val < 1 at ha
      omega
    rw [productResidueCenteredEnergy_eq_gcd]
    simp only [hv, Nat.gcd_zero_right, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    norm_num

theorem productResidueCenteredEnergy_pos_iff (q : ℕ+) :
    0 < productResidueCenteredEnergy q ↔ 1 < (q : ℕ) := by
  have hn : 0 ≤ productResidueCenteredEnergy q :=
    sum_nonneg fun r _ => sq_nonneg _
  have hz := productResidueCenteredEnergy_eq_zero_iff q
  have hp := q.pos
  constructor
  · intro h
    have hne : (q : ℕ) ≠ 1 := fun hq => (ne_of_gt h) (hz.mpr hq)
    omega
  · intro h
    exact lt_of_le_of_ne hn (fun he => (Nat.ne_of_gt h) (hz.mp he.symm))

/-- Averaging over a positive number of complete periods. -/
def residueBlockAverage (q h : ℕ+) (f : ZMod (q : ℕ) → ℂ)
    (r : ZMod (q : ℕ)) : ℂ :=
  (∑ j ∈ range ((q : ℕ) * (h : ℕ)), f (r + j)) / ((q : ℕ) * (h : ℕ))

theorem residueBlockAverage_eq_mean (q h : ℕ+) (f : ZMod (q : ℕ) → ℂ)
    (r : ZMod (q : ℕ)) :
    residueBlockAverage q h f r = (∑ s : ZMod (q : ℕ), f s) / (q : ℕ) := by
  have hs := sum_residue_blocks q (h : ℕ) r f
  simp only [add_comm] at hs
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
  have hh : ((h : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h.ne_zero
  rw [residueBlockAverage, hs]
  field_simp

/-- Complete-period smoothing deletes the entire nonconstant product profile. -/
theorem productResidueBlockAverage (q h : ℕ+) (r : ZMod (q : ℕ)) :
    residueBlockAverage q h (fun s => (productResidueCount q s : ℂ)) r = (q : ℕ) := by
  rw [residueBlockAverage_eq_mean]
  have hm : (∑ s : ZMod (q : ℕ), (productResidueCount q s : ℂ)) =
      ((q : ℕ) : ℂ) ^ 2 := by exact_mod_cast sum_productResidueCount q
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
  rw [hm, pow_two, mul_div_cancel_right₀ _ hq]

/-- Mean on one finite residue fibre. -/
def residueFiberMean (L : ℕ+) (u : Fin (L : ℕ) → ℝ) : ℝ :=
  (∑ j, u j) / (L : ℕ)

theorem sum_eq_card_mul_residueFiberMean (L : ℕ+) (u : Fin (L : ℕ) → ℝ) :
    (∑ j, u j) = (L : ℕ) * residueFiberMean L u := by
  have hL : ((L : ℕ) : ℝ) ≠ 0 := by exact_mod_cast L.ne_zero
  simp only [residueFiberMean, mul_div_cancel₀ _ hL]

/-- Signed pairing retains the covariance after removing both fibre means. -/
theorem residueFiber_pairing_decomposition (L : ℕ+)
    (u v : Fin (L : ℕ) → ℝ) :
    (∑ j, u j * v j) =
      (L : ℕ) * residueFiberMean L u * residueFiberMean L v +
        ∑ j, (u j - residueFiberMean L u) * (v j - residueFiberMean L v) := by
  have he (j : Fin (L : ℕ)) :
      (u j - residueFiberMean L u) * (v j - residueFiberMean L v) =
        u j * v j - u j * residueFiberMean L v -
          residueFiberMean L u * v j + residueFiberMean L u * residueFiberMean L v := by
    ring
  simp only [he, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_eq_card_mul_residueFiberMean L u, sum_eq_card_mul_residueFiberMean L v]
  ring

/-- Exact residue projection energy, including its nonnegative residual. -/
theorem residueFiber_energy_decomposition (q L : ℕ+)
    (w : ZMod (q : ℕ) → Fin (L : ℕ) → ℝ) :
    (∑ r, ∑ j, (w r j) ^ 2) =
      (L : ℕ) * ∑ r, (residueFiberMean L (w r)) ^ 2 +
        ∑ r, ∑ j, (w r j - residueFiberMean L (w r)) ^ 2 := by
  have he (r : ZMod (q : ℕ)) := residueFiber_pairing_decomposition L (w r) (w r)
  simp only [← pow_two, mul_assoc] at he
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum]

/-- One integer placed in its residue fibre, with the quotient reduced modulo `L`. -/
def productResidueAtom (q L : ℕ+) (n : ℕ)
    (r : ZMod (q : ℕ)) (t : Fin (L : ℕ)) : ℝ :=
  if (n : ZMod (q : ℕ)) = r then
    if (⟨n / (q : ℕ) % (L : ℕ), Nat.mod_lt _ L.pos⟩ : Fin (L : ℕ)) = t
    then 1 else 0
  else 0

theorem sum_productResidueAtom (q L : ℕ+) (n : ℕ) (r : ZMod (q : ℕ)) :
    (∑ t, productResidueAtom q L n r t) =
      if (n : ZMod (q : ℕ)) = r then 1 else 0 := by
  classical
  by_cases hn : (n : ZMod (q : ℕ)) = r
  · simp [productResidueAtom, hn]
  · simp [productResidueAtom, hn]

/-- Actual balanced products, shifted before their finite residue encoding. -/
def balancedProductRow (q L : ℕ+) (k c : ℕ)
    (r : ZMod (q : ℕ)) (t : Fin (L : ℕ)) : ℝ :=
  ∑ i ∈ range ((q : ℕ) * k), ∑ j ∈ range ((q : ℕ) * k),
    productResidueAtom q L
      (((q : ℕ) * k + i + 1) * ((q : ℕ) * k + j + 1) + c) r t

theorem sum_balancedProductRow (q L : ℕ+) (k c : ℕ) (r : ZMod (q : ℕ)) :
    (∑ t, balancedProductRow q L k c r t) =
      (k : ℝ) ^ 2 * productResidueCount q (r - (c : ZMod (q : ℕ))) := by
  classical
  have hs : (∑ t, balancedProductRow q L k c r t) =
      ∑ i ∈ range ((q : ℕ) * k), ∑ j ∈ range ((q : ℕ) * k),
        ∑ t, productResidueAtom q L
          (((q : ℕ) * k + i + 1) * ((q : ℕ) * k + j + 1) + c) r t := by
    unfold balancedProductRow
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
  rw [hs]
  simp_rw [sum_productResidueAtom]
  have hc (n : ℕ) : ((n + c : ℕ) : ZMod (q : ℕ)) = r ↔
      (n : ZMod (q : ℕ)) = r - (c : ZMod (q : ℕ)) := by
    rw [Nat.cast_add, eq_sub_iff_add_eq]
  simp_rw [hc]
  have hh := balancedProductResidueCount_eq q k (r - (c : ZMod (q : ℕ)))
  unfold balancedProductResidueCount at hh
  exact_mod_cast hh

/-- Difference between the actual product row and its complete-period window average. -/
def balancedProductSmoothingRow (q L h : ℕ+) (k : ℕ)
    (r : ZMod (q : ℕ)) (t : Fin (L : ℕ)) : ℝ :=
  balancedProductRow q L k ((q : ℕ) * (h : ℕ)) r t -
    (∑ j ∈ range ((q : ℕ) * (h : ℕ)),
      balancedProductRow q L k ((q : ℕ) * (h : ℕ) - j) r t) /
        ((q : ℕ) * (h : ℕ))

theorem sum_balancedProductSmoothingRow (q L h : ℕ+) (k : ℕ)
    (r : ZMod (q : ℕ)) :
    (∑ t, balancedProductSmoothingRow q L h k r t) =
      (k : ℝ) ^ 2 * ((productResidueCount q r : ℝ) - (q : ℕ)) := by
  have hav : (∑ j ∈ range ((q : ℕ) * (h : ℕ)),
      (productResidueCount q (r - (((q : ℕ) * (h : ℕ) - j : ℕ) : ZMod (q : ℕ))) : ℝ)) /
        ((q : ℕ) * (h : ℕ)) = (q : ℕ) := by
    have he : (∑ j ∈ range ((q : ℕ) * (h : ℕ)),
        (productResidueCount q (r - (((q : ℕ) * (h : ℕ) - j : ℕ) : ZMod (q : ℕ))) : ℝ)) =
          ∑ j ∈ range ((q : ℕ) * (h : ℕ)),
            (productResidueCount q (r + (j : ZMod (q : ℕ))) : ℝ) := by
      apply sum_congr rfl
      intro j hj
      rw [Nat.cast_sub (Nat.le_of_lt (mem_range.mp hj)), Nat.cast_mul,
        ZMod.natCast_self, zero_mul, zero_sub, sub_neg_eq_add]
    rw [he]
    have hh := productResidueBlockAverage q h r
    unfold residueBlockAverage at hh
    dsimp only at hh
    apply Complex.ofReal_injective
    push_cast
    exact hh
  simp only [balancedProductSmoothingRow, sum_sub_distrib, ← sum_div]
  rw [sum_comm (s := (univ : Finset (Fin (L : ℕ))))]
  simp_rw [sum_balancedProductRow]
  simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul, sub_zero]
  rw [← mul_sum, mul_div_assoc, hav, ← mul_sub]

/-- Full periodic cost and exact residual for the actual balanced product smoothing. -/
theorem balancedProductSmoothing_energy (q L h : ℕ+) (k : ℕ) :
    (∑ r, ∑ t, (balancedProductSmoothingRow q L h k r t) ^ 2) =
      (k : ℝ) ^ 4 / (L : ℕ) * productResidueCenteredEnergy q +
        ∑ r, ∑ t, (balancedProductSmoothingRow q L h k r t -
          residueFiberMean L (balancedProductSmoothingRow q L h k r)) ^ 2 := by
  have hL : ((L : ℕ) : ℝ) ≠ 0 := by exact_mod_cast L.ne_zero
  have hm (r : ZMod (q : ℕ)) :
      residueFiberMean L (balancedProductSmoothingRow q L h k r) =
        (k : ℝ) ^ 2 * ((productResidueCount q r : ℝ) - (q : ℕ)) / (L : ℕ) := by
    rw [residueFiberMean, sum_balancedProductSmoothingRow]
  rw [residueFiber_energy_decomposition]
  congr 1
  simp_rw [hm, div_pow, mul_pow]
  rw [← sum_div, ← mul_sum]
  unfold productResidueCenteredEnergy
  field_simp

theorem balancedProductSmoothing_energy_ge (q L h : ℕ+) (k : ℕ) :
    (k : ℝ) ^ 4 / (L : ℕ) * productResidueCenteredEnergy q ≤
      ∑ r, ∑ t, (balancedProductSmoothingRow q L h k r t) ^ 2 := by
  rw [balancedProductSmoothing_energy]
  exact le_add_of_nonneg_right (sum_nonneg fun r _ => sum_nonneg fun t _ => sq_nonneg _)

/-- Actual signed pairing after removing precisely the periodic product bias. -/
theorem balancedProductSmoothing_pairing (q L h : ℕ+) (k : ℕ)
    (g : ZMod (q : ℕ) → Fin (L : ℕ) → ℝ) :
    (∑ r, ∑ t, balancedProductSmoothingRow q L h k r t * g r t) =
      (k : ℝ) ^ 2 * ∑ r, ((productResidueCount q r : ℝ) - (q : ℕ)) *
        residueFiberMean L (g r) +
      ∑ r, ∑ t, (balancedProductSmoothingRow q L h k r t -
        residueFiberMean L (balancedProductSmoothingRow q L h k r)) *
          (g r t - residueFiberMean L (g r)) := by
  have hm (r : ZMod (q : ℕ)) :
      (L : ℕ) * residueFiberMean L (balancedProductSmoothingRow q L h k r) =
        (k : ℝ) ^ 2 * ((productResidueCount q r : ℝ) - (q : ℕ)) :=
    (sum_eq_card_mul_residueFiberMean L _).symm.trans
      (sum_balancedProductSmoothingRow q L h k r)
  have he (r : ZMod (q : ℕ)) :=
    residueFiber_pairing_decomposition L (balancedProductSmoothingRow q L h k r) (g r)
  simp_rw [he, hm]
  rw [sum_add_distrib]
  simp only [mul_assoc, ← mul_sum]

/-- Width containing every shifted product without reducing its quotient modulo `L`. -/
def balancedProductSmoothingWidth (q h : ℕ+) (k : ℕ) : ℕ+ :=
  ⟨4 * (q : ℕ) * k ^ 2 + (h : ℕ) + 1, by omega⟩

theorem balancedProductSmoothing_noWrap (q h : ℕ+) (k : ℕ)
    (i j : Fin ((q : ℕ) * k)) (c : Fin ((q : ℕ) * (h : ℕ) + 1)) :
    ((q : ℕ) * k + i.val + 1) * ((q : ℕ) * k + j.val + 1) + c.val <
      (q : ℕ) * (balancedProductSmoothingWidth q h k : ℕ) := by
  have hi : (q : ℕ) * k + i.val + 1 ≤ 2 * ((q : ℕ) * k) := by
    have := i.is_lt
    omega
  have hj : (q : ℕ) * k + j.val + 1 ≤ 2 * ((q : ℕ) * k) := by
    have := j.is_lt
    omega
  have hp := Nat.mul_le_mul hi hj
  have he : (q : ℕ) * (balancedProductSmoothingWidth q h k : ℕ) =
      (2 * ((q : ℕ) * k)) * (2 * ((q : ℕ) * k)) + (q : ℕ) * (h : ℕ) + (q : ℕ) := by
    change (q : ℕ) * (4 * (q : ℕ) * k ^ 2 + (h : ℕ) + 1) = _
    ring
  rw [he]
  have := c.is_lt
  have := q.pos
  omega

/-- At `X = 4j²`, `H = 2j = √X`, the smoothing error has a fixed positive `X²` floor. -/
theorem balancedProductSmoothing_squareRoot_obstruction (j : ℕ+) :
    let k := 2 * (j : ℕ) ^ 2
    let L := balancedProductSmoothingWidth 2 j k
    productResidueCenteredEnergy 2 / 34 * (4 * ((j : ℕ) : ℝ) ^ 2) ^ 2 ≤
      ∑ r, ∑ t, (balancedProductSmoothingRow 2 L j k r t) ^ 2 := by
  let k := 2 * (j : ℕ) ^ 2
  let L := balancedProductSmoothingWidth 2 j k
  let x : ℝ := (j : ℕ)
  change productResidueCenteredEnergy 2 / 34 * (4 * x ^ 2) ^ 2 ≤
    ∑ r, ∑ t, (balancedProductSmoothingRow 2 L j k r t) ^ 2
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ ((j : ℕ) : ℝ)
    exact_mod_cast Nat.succ_le_of_lt j.pos
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hx2 : x ≤ x ^ 2 := by
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hx4 : x ^ 2 ≤ x ^ 4 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr (hx.trans hx2))]
  have hk : (k : ℝ) = 2 * x ^ 2 := by
    dsimp [k, x]
    push_cast
    rfl
  have hL : ((L : ℕ) : ℝ) = 32 * x ^ 4 + x + 1 := by
    change ((4 * 2 * (2 * (j : ℕ) ^ 2) ^ 2 + (j : ℕ) + 1 : ℕ) : ℝ) = _
    push_cast
    dsimp [x]
    ring
  have hLb : ((L : ℕ) : ℝ) ≤ 34 * x ^ 4 := by
    rw [hL]
    have hx4' := hx2.trans hx4
    have h14 := hx.trans hx4'
    linarith
  have hLp : 0 < ((L : ℕ) : ℝ) := by exact_mod_cast L.pos
  have hratio : (4 * x ^ 2) ^ 2 / 34 ≤ (k : ℝ) ^ 4 / (L : ℕ) := by
    rw [div_le_div_iff₀ (by norm_num) hLp, hk]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hLb) (pow_nonneg hx0 4)]
  have hE : 0 ≤ productResidueCenteredEnergy 2 :=
    sum_nonneg fun r _ => sq_nonneg _
  calc
    productResidueCenteredEnergy 2 / 34 * (4 * x ^ 2) ^ 2 =
        ((4 * x ^ 2) ^ 2 / 34) * productResidueCenteredEnergy 2 := by ring
    _ ≤ (k : ℝ) ^ 4 / (L : ℕ) * productResidueCenteredEnergy 2 :=
      mul_le_mul_of_nonneg_right hratio hE
    _ ≤ _ := balancedProductSmoothing_energy_ge 2 L j k

end

end GaloisForLFunctions.Goldbach
