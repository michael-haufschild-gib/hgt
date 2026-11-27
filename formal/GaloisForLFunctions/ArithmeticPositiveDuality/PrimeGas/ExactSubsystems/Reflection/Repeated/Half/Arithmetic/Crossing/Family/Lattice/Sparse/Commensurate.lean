import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature

/-! # Algebraic damping on integer shells with commensurate energy differences -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse

open Real

variable {I : Type*} [Fintype I]

/-- All gaps of a finite spectrum are integer multiples of a common positive spacing. -/
def Commensurate (E : I → ℝ) := ∃ (h c : ℝ) (k : I → ℕ), 0<h ∧ E=fun i => h*levels k i+c

/-- A positive algebraic exponent of a rational base above one cannot give
an algebraic integer whose inverse is also integral. -/
private theorem unit_power (b : ℚ) (hb : 1<b) {d : ℝ} (hd : 0<d)
    (fwd : IsIntegral ℤ ((b : ℝ)^d)) (back : IsIntegral ℤ (((b : ℝ)^d)⁻¹)) : Transcendental ℚ d := by
  have br : (1 : ℝ)<b := by exact_mod_cast hb
  have bp := zero_lt_one.trans br
  intro alg
  by_cases irr : Irrational d
  · have base : IsAlgebraic ℚ (b : ℝ) := isAlgebraic_algebraMap b
    exact GaloisForLFunctions.RHTower.gelfondSchneiderReal_holds _ _ bp br.ne'
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr base) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg)
      irr ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp fwd.isAlgebraic)
  · obtain ⟨q,rfl⟩ := Classical.not_not.mp irr
    have mult : (q : ℝ)*(q.den : ℝ)=(q.num : ℝ) := by exact_mod_cast q.mul_den_eq_num
    have power : ((b : ℝ)^(q : ℝ))^q.den=((b^q.num : ℚ) : ℝ) := by
      rw [← rpow_natCast,← rpow_mul bp.le,mult,rpow_intCast,Rat.cast_zpow]
    have int := back.pow q.den
    rw [inv_pow,power] at int
    obtain ⟨z,hz⟩ := int.exists_int_iff_exists_rat.mp ⟨(b^q.num)⁻¹,by rw [Rat.cast_inv]⟩
    have gt : 1<((b^q.num : ℚ) : ℝ) := by rw [← power]; exact one_lt_pow₀ (one_lt_rpow br hd) q.den_pos.ne'
    have small := inv_lt_one_of_one_lt₀ gt
    have positive := inv_pos.mpr (zero_lt_one.trans gt)
    rw [hz] at small positive
    have z0 : 0<z := by exact_mod_cast positive
    have z1 : z<1 := by exact_mod_cast small
    omega

private theorem gap_exists (k : I → ℕ) (asym : ¬Reflects (levels k)) : ∃ i j, k i<k j := by
  by_contra! none
  apply asym
  rcases isEmpty_or_nonempty I with he | hn
  · exact ⟨0,Equiv.refl _,fun i => (he.false i).elim⟩
  · obtain ⟨x⟩ := hn
    refine ⟨(k x : ℝ)+(k x : ℝ),Equiv.refl _,fun i => ?_⟩
    have same := le_antisymm (none x i) (none i x)
    change (k i : ℝ)+(k i : ℝ)=(k x : ℝ)+(k x : ℝ)
    rw [same]

private theorem grid_blind (a : I → ℕ+) (inj : Function.Injective (energy ∘ a))
    (grid : Commensurate (energy ∘ a)) (asym : ¬Reflects (energy ∘ a)) {d : ℝ} (hd : 0<d)
    (hit : agrees (energy ∘ a) d) : Transcendental ℚ d := by
  obtain ⟨h,c,k,hp,eq⟩ := grid
  have distinct : Function.Injective k := by
    intro i j ij
    apply inj
    rw [eq]
    change h*(k i : ℝ)+c=h*(k j : ℝ)+c
    rw [ij]
  rw [eq,affine_reflects _ _ _ hp.ne'] at asym
  rw [eq,agrees_affine] at hit
  obtain ⟨i,j,lt⟩ := gap_exists k asym
  letI : Nonempty I := ⟨i⟩
  let m := k j-k i
  let b : ℚ := ((a j : ℕ) : ℚ)/((a i : ℕ) : ℚ)
  have eval (u : I) : exp ((energy ∘ a) u)=((a u : ℕ) : ℝ) := exp_log (Nat.cast_pos.mpr (a u).pos)
  have ratio : (b : ℝ)=exp ((m : ℝ)*h) := by
    change ((((a j : ℕ) : ℚ)/((a i : ℕ) : ℚ) : ℚ) : ℝ)=_
    rw [Rat.cast_div,Rat.cast_natCast,Rat.cast_natCast,← eval j,← eval i,← exp_sub,eq]
    change exp (h*(k j : ℝ)+c-(h*(k i : ℝ)+c))=exp (((k j-k i : ℕ) : ℝ)*h)
    rw [Nat.cast_sub lt.le]
    congr 1
    ring
  have br : (1 : ℝ)<b := by rw [ratio,one_lt_exp_iff]; exact mul_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt lt)) hp
  have np : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let x := exp (d*h/Fintype.card I)
  have u : IsIntegral ℤ x ∧ IsIntegral ℤ x⁻¹ := unit_coordinates k distinct asym hit
  have pow : x^(Fintype.card I*m)=(b : ℝ)^d := by
    rw [rpow_def_of_pos (zero_lt_one.trans br),ratio,log_exp]
    unfold x
    rw [← exp_nat_mul]
    congr 1
    rw [Nat.cast_mul]
    field_simp
  apply unit_power b (by exact_mod_cast br) hd
  · rw [← pow]; exact u.1.pow _
  · rw [← pow,← inv_pow]; exact u.2.pow _

/-- On any commensurate simple spectrum of actual integer shells, a single
opposite-order comparison detects every nonzero algebraic damping. -/
theorem commensurate_reading (a : I → ℕ+) (inj : Function.Injective (energy ∘ a))
    (grid : Commensurate (energy ∘ a)) (d : ℝ) (alg : IsAlgebraic ℚ d) :
    agrees (energy ∘ a) d ↔ d=0 ∨ Reflects (energy ∘ a) := by
  constructor
  · intro hit
    by_contra! both
    rcases lt_or_gt_of_ne both.1 with neg | pos
    · have rev : agrees (energy ∘ a) (-d) := by simpa only [agrees,neg_neg] using hit.symm
      exact grid_blind a inj grid both.2 (neg_pos.mpr neg) rev alg.neg
    · exact grid_blind a inj grid both.2 pos hit alg
  · rintro (rfl | symm)
    · simp only [agrees,neg_zero]
    · exact reflection_agrees symm _

#print axioms commensurate_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse
