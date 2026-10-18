import GaloisForLFunctions.BiScaleUncertainty.SixthReadoutStability

/-!
# Prime-selective differences of literal translated moments

Finite differences in the lag variables are averages of products of signal
differences. Even CRT lags isolate individual prime coordinates of actual
sieve signals. The construction uses a finite cube of literal observations.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Each cube vertex chooses whether a lag difference is applied. -/
def cubeLag {m : ℕ} (t : Fin m → ℕ) (b : Fin m → Fin 2) (i : Fin m) : ℕ :=
  if b i = 0 then 0 else t i

/-- Alternating coefficients of the finite-difference cube. -/
def cubeSign {m : ℕ} (b : Fin m → Fin 2) : ℝ :=
  ∏ i, if b i = 0 then 1 else -1

/-- A finite signed sum of literal translated observations. -/
def momentContrast (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (t : Fin m → ℕ) : ℝ :=
  ∑ b : Fin m → Fin 2, cubeSign b * translatedMoment N c (cubeLag t b)

/-- Multilinearity converts the raw observation cube to an actual signal-difference product. -/
theorem momentContrast_eq (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (t : Fin m → ℕ) :
    momentContrast N c t =
      (∑ n ∈ Finset.range N.factorial,
        ∏ i, (sieveSeq N c n-sieveSeq N c (n+t i))) / (N.factorial : ℝ) := by
  unfold momentContrast translatedMoment
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = ∑ b : Fin m → Fin 2, ∏ i,
        ((if b i = 0 then (1 : ℝ) else -1)*
          sieveSeq N c (n+(if b i = 0 then 0 else t i))) := by
      simp only [cubeSign, cubeLag, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Fin 2,
        ((if b = 0 then (1 : ℝ) else -1)*
          sieveSeq N c (n+(if b = 0 then 0 else t i))) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [Fin.sum_univ_two]
      ring

/-- The unreduced raw observation count depends on degree, not on the factorial period. -/
theorem cube_card (m : ℕ) : Fintype.card (Fin m → Fin 2) = 2^m := by simp

private theorem cubeSign_abs {m : ℕ} (b : Fin m → Fin 2) : |cubeSign b| = 1 := by
  unfold cubeSign
  rw [Finset.abs_prod]
  have h (i : Fin m) : |if b i = 0 then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  simp_rw [h]
  simp

/-- The contrast amplifies raw errors by at most the sum over its observation
cube. This estimate holds for every pair of actual sieve signals. -/
theorem momentContrast_error (N : ℕ) (c e : ℕ → ℝ) {m : ℕ} (t : Fin m → ℕ) :
    |momentContrast N c t-momentContrast N e t| ≤
      ∑ b : Fin m → Fin 2,
        |translatedMoment N c (cubeLag t b)-translatedMoment N e (cubeLag t b)| := by
  unfold momentContrast
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b : Fin m → Fin 2,
        |cubeSign b*translatedMoment N c (cubeLag t b)-
          cubeSign b*translatedMoment N e (cubeLag t b)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_sub, abs_mul, cubeSign_abs, one_mul]

private theorem modes_coprime (N : ℕ) :
    Pairwise (fun p q : oddPrimeModes N => Nat.Coprime (p : ℕ) (q : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (mem_oddPrimeModes.mp p.property).1
    (mem_oddPrimeModes.mp q.property).1).mpr
  intro h
  exact hpq (Subtype.ext h)

local instance (N : ℕ) : NeZero (primeFamilyPeriod N) := by
  refine ⟨?_⟩
  have h := primeFamilyPeriod_odd N
  obtain ⟨j,hj⟩ := h
  omega

/-- Half an even CRT lag: the chosen prime receives the inverse of two. -/
def selectiveHalf (N : ℕ) (p : oddPrimeModes N) : ZMod (primeFamilyPeriod N) :=
  (ZMod.prodEquivPi (fun q : oddPrimeModes N => (q : ℕ)) (modes_coprime N)).symm
    (fun q => if q = p then ((((q : ℕ)+1)/2 : ℕ) : ZMod (q : ℕ)) else 0)

/-- A concrete even lag equal to one at the chosen prime and zero at every other mode. -/
def selectiveLag (N : ℕ) (p : oddPrimeModes N) : ℕ := 2*(selectiveHalf N p).val

private theorem selectiveHalf_mod (N : ℕ) (p q : oddPrimeModes N) :
    ((selectiveHalf N p).val : ZMod (q : ℕ)) =
      if q = p then ((((q : ℕ)+1)/2 : ℕ) : ZMod (q : ℕ)) else 0 := by
  let e : ZMod (primeFamilyPeriod N) ≃+* (∀ r : oddPrimeModes N, ZMod (r : ℕ)) :=
    ZMod.prodEquivPi (fun r : oddPrimeModes N => (r : ℕ)) (modes_coprime N)
  have he : e (selectiveHalf N p) q = ((selectiveHalf N p).val : ZMod (q : ℕ)) := by
    calc
      _ = e ((selectiveHalf N p).val : ZMod (primeFamilyPeriod N)) q := by
        rw [ZMod.natCast_zmod_val]
      _ = _ := by simp only [map_natCast]; rfl
  rw [← he]
  exact congrFun (e.apply_symm_apply _) q

theorem selectiveLag_mod (N : ℕ) (p q : oddPrimeModes N) :
    (selectiveLag N p : ZMod (q : ℕ)) = if q = p then 1 else 0 := by
  unfold selectiveLag
  push_cast
  rw [selectiveHalf_mod]
  by_cases hqp : q = p
  · rw [if_pos hqp, if_pos hqp]
    have ho := (mem_oddPrimeModes.mp q.property).2.1
    obtain ⟨j,hj⟩ := ho
    have hh : 2*(((q : ℕ)+1)/2) = (q : ℕ)+1 := by omega
    have hc := congrArg (fun n : ℕ => (n : ZMod (q : ℕ))) hh
    simpa using hc
  · simp [hqp]

/-- Every multiple of a selected lag preserves the signal's parity character. -/
theorem selectiveLag_parity (N : ℕ) (p : oddPrimeModes N) (j : ℕ) :
    parityFactor (j*selectiveLag N p) = 1 := by
  have hd : 2 ∣ j*selectiveLag N p := ⟨j*(selectiveHalf N p).val, by unfold selectiveLag; ring⟩
  simp [parityFactor, hd]

/-- Multiples of the CRT lag act only on their chosen residue coordinate. -/
theorem selectiveLag_multiple_mod (N : ℕ) (p q : oddPrimeModes N) (j : ℕ) :
    ((j*selectiveLag N p : ℕ) : ZMod (q : ℕ)) =
      if q = p then (j : ZMod (q : ℕ)) else 0 := by
  rw [Nat.cast_mul, selectiveLag_mod]
  split_ifs <;> simp

/-- One literal signal difference isolates one arbitrary prime coefficient,
without support or nonvanishing assumptions. -/
theorem selective_difference (N : ℕ) (a : ℕ → ℝ) (p : oddPrimeModes N) (n j : ℕ) :
    sieveSeq N (primeFamilyWeight N a) n-
      sieveSeq N (primeFamilyWeight N a) (n+j*selectiveLag N p) =
      parityFactor n*a p*(residueRow p (n : ZMod (p : ℕ))-
        residueRow p ((n : ZMod (p : ℕ))+(j : ZMod (p : ℕ)))) := by
  rw [sieveSeq_primeFamilyWeight, sieveSeq_primeFamilyWeight]
  change parityFactor n*(∑ q : oddPrimeModes N, a q*residueRow q (n : ZMod (q : ℕ)))-
    parityFactor (n+j*selectiveLag N p)*
      (∑ q : oddPrimeModes N, a q*residueRow q ((n+j*selectiveLag N p : ℕ) : ZMod (q : ℕ))) = _
  rw [parityFactor_add, selectiveLag_parity, mul_one, ← mul_sub, ← Finset.sum_sub_distrib]
  have ht (q : oddPrimeModes N) :
      a q*residueRow q (n : ZMod (q : ℕ))-
        a q*residueRow q ((n+j*selectiveLag N p : ℕ) : ZMod (q : ℕ)) =
      if q = p then a p*(residueRow p (n : ZMod (p : ℕ))-
        residueRow p ((n : ZMod (p : ℕ))+(j : ZMod (p : ℕ)))) else 0 := by
    rw [Nat.cast_add, selectiveLag_multiple_mod]
    by_cases hqp : q = p
    · subst q
      simp
      ring
    · simp [hqp]
  simp_rw [ht]
  simp
  ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
