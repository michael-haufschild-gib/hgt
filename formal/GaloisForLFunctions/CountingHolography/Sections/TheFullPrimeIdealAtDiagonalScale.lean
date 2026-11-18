import GaloisForLFunctions.CountingHolography.Sections.TheCoefficientIndependentPrimeMeshError
import Mathlib.NumberTheory.Chebyshev

/-!
# The full prime ideal at diagonal scale

All prime powers contribute to the integrated contact, but only ordinary
prime floors can contribute at quadratic conductor scale. The regularized
jet is the remaining discretization term in the original section surplus.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction

/-- Integrated prime contact, with all prime powers in the original window. -/
def fullPrimeContact {N : ℕ} (a : Fin N → ℤ) : ℝ :=
  ∑ k ∈ Icc 2 (3*windowEnd N), integratedContact a k*vonMangoldt k

/-- Adding back the ordinary floor loss approximates even the full prime
ideal to square-root accuracy, independently of the spline coefficients. -/
theorem fullPrimeGenerator_ordinary_floor_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    |Real.log (generator a : ℝ)+ordinaryFloorLoss a-fullPrimeContact a| ≤
      C*Real.sqrt (3*windowEnd N : ℕ) := by
  obtain ⟨B,hB,hquad⟩ := original_contact_quadrature
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨34*B+|D|,by positivity,fun N a => ?_⟩
  let L := 3*windowEnd N
  let S := Icc 2 L
  let X := contactMultiplicity (packet a) L (resolution a)
  let w := fun k => Int.fract (X k)*vonMangoldt k
  let V := ∑ k ∈ S.filter (fun k => ¬k.Prime), w k
  have hV : 0 ≤ V := sum_nonneg fun _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg
  have hVL : V ≤ |D| * Real.sqrt L := calc
    _ ≤ ∑ k ∈ S.filter (fun k => ¬k.Prime), vonMangoldt k := sum_le_sum fun k _ =>
      mul_le_of_le_one_left vonMangoldt_nonneg (Int.fract_lt_one (X k)).le
    _ ≤ ∑ k ∈ (Ioc 0 L).filter (fun k => ¬k.Prime), vonMangoldt k := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
      intro k hk
      obtain ⟨hk,hp⟩ := mem_filter.mp hk
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩,hp⟩
    _ = Chebyshev.psi L-Chebyshev.theta L := by rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
    _ ≤ _ := (hD L).trans (mul_le_mul_of_nonneg_right (le_abs_self D) (Real.sqrt_nonneg _))
  have hsplit : ordinaryFloorLoss a+V = ∑ k ∈ S, w k := sum_filter_add_sum_filter_not S Nat.Prime w
  have he : Real.log (generator a : ℝ)+ordinaryFloorLoss a+V-fullPrimeContact a =
      ∑ k ∈ S, (X k-integratedContact a k)*vonMangoldt k := by
    rw [add_assoc,hsplit,generator,log_contactGenerator]
    change (∑ k ∈ S, (⌊X k⌋:ℝ)*vonMangoldt k)+(∑ k ∈ S, w k)-
      (∑ k ∈ S, integratedContact a k*vonMangoldt k) = _
    rw [← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [show w k=Int.fract (X k)*vonMangoldt k from rfl,← add_mul,Int.floor_add_fract,sub_mul]
  have hraw : |∑ k ∈ S, (X k-integratedContact a k)*vonMangoldt k| ≤ 34*B*Real.sqrt L := calc
    _ ≤ ∑ k ∈ S, |(X k-integratedContact a k)*vonMangoldt k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, B*(vonMangoldt k/Real.sqrt k) := by
      refine sum_le_sum fun k hk => ?_
      rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
      exact (mul_le_mul_of_nonneg_right (hquad N a (lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hk).1))
        vonMangoldt_nonneg).trans_eq (by ring)
    _ ≤ _ := by
      rw [← mul_sum,mul_comm (34:ℝ),mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hB
      exact (sum_le_sum_of_subset_of_nonneg (s := S) (t := Ioc 0 L) (fun _ hk =>
        mem_Ioc.mpr ⟨lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩)
        (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))).trans
          (_root_.RHTower.sum_vonMangoldt_div_sqrt_le L)
  rw [← he,abs_le] at hraw
  change |Real.log (generator a : ℝ)+ordinaryFloorLoss a-fullPrimeContact a| ≤ (34*B+|D|)*Real.sqrt L
  rw [abs_le]
  constructor <;> linarith only [hraw.1,hraw.2,hV,hVL]

/-- For every multiplicity the discrepancy in the full generator on the
three squares is linear in the conductor index after restoring ordinary floors. -/
theorem successorSquare_full_generator_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ m : ℕ,
    let a := m • successorSquareTriple n
    |Real.log (generator a : ℝ)+ordinaryFloorLoss a-(m:ℝ)^2*fullPrimeContact (successorSquareTriple n)| ≤ C*n := by
  obtain ⟨B,hB,h⟩ := fullPrimeGenerator_ordinary_floor_error
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  refine ⟨B*A,mul_nonneg hB (zero_le_one.trans hA),fun {n} hn m => ?_⟩
  have hh := h _ (m • successorSquareTriple n)
  have hroot := Real.sqrt_le_sqrt (hwin hn)
  rw [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg (α := ℝ) n))] at hroot
  simp only [fullPrimeContact,integratedContact_nsmul,mul_assoc,← mul_sum] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot hB).trans_eq (mul_assoc ..).symm)

/-- Restoring the ordinary floors and the integrated prime powers leaves the
original jet radius, up to an error linear in conductor and multiplicity. -/
theorem successorSquare_full_surplus_and_jet : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ m : ℕ,
    let a := m • successorSquareTriple n
    |(radius a-Real.log (generator a : ℝ))-
      (ordinaryFloorLoss a+jetRadius a-(m:ℝ)^2*fullPrimeContact (successorSquareTriple n))| ≤ C*((n:ℝ)+m) := by
  obtain ⟨B,hB,hg⟩ := successorSquare_full_generator_error
  obtain ⟨J,hJ,hpole⟩ := pole_balanced_linear_error
  refine ⟨B+4*J,by positivity,fun {n} hn m => ?_⟩
  let d := successorSquareTriple n
  let a := m • d
  have hbal : positivePoleDegree a = 0 := by
    change (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i:ℝ)+1)*(((m • d) i : ℤ):ℝ)) = 0
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
    simp_rw [mul_left_comm _ (m:ℝ)]
    rw [← mul_sum,show (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i:ℝ)+1)*(d i:ℝ))=0 from positivePoleDegree_successorSquareTriple hn,mul_zero]
  have hsize : (resolution a : ℝ) ≤ (m:ℝ)*4 := by
    change (resolution (m • d):ℝ) ≤ _
    rw [resolution_smul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (coefficientVariation_eq_resolution d ▸ successorSquareTriple_mass n) (Nat.cast_nonneg _)
  have hp := (hpole _ a hbal).trans (mul_le_mul_of_nonneg_left hsize hJ)
  have hfull : |Real.log (generator a : ℝ)+ordinaryFloorLoss a-(m:ℝ)^2*fullPrimeContact d| ≤ B*n := hg hn m
  change |(radius a-Real.log (generator a : ℝ))-(ordinaryFloorLoss a+jetRadius a-(m:ℝ)^2*fullPrimeContact d)| ≤ _
  rw [abs_le] at hp hfull ⊢
  constructor <;> linarith only [hp.1,hp.2,hfull.1,hfull.2,mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m),
    mul_nonneg hJ (Nat.cast_nonneg (α := ℝ) n)]

#print axioms fullPrimeGenerator_ordinary_floor_error
#print axioms successorSquare_full_generator_error
#print axioms successorSquare_full_surplus_and_jet

end GaloisForLFunctions.CountingHolography.Sections
