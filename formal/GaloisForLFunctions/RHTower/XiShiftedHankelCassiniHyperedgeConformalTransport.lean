import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniPairEnergyTransport
import GaloisForLFunctions.HTGeometry.VandermondeSign

/-!
# All-degree Cassini hyperedge conformal transport

For a finite `d`-node packet, define its Cassini hyperedge energy by

`E_d(z) = (∏ᵢ zᵢ) · ∏_{i<j}(zⱼ-zᵢ)²`.

Under the common reciprocal-mass shift `z ↦ z/(1+h z)`, this energy obeys the exact cocycle

`E_d(M_h z) = E_d(z) / (∏ᵢ(1+h zᵢ))^(2d-1)`.

Thus every Hankel degree has conformal weight `2d-1`.  Differentiating at zero gives the exact
hyperedge transport law

`d/dh E_d(M_h z)|₀ = -(2d-1)(∑ᵢ zᵢ)E_d(z)`.

The degree-one pair transport from the preceding module is therefore the first member of one
all-degree law: contact orientation is governed by the hyperedge velocity barycenter, not by a
degree-specific angular criterion.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

def cassiniMobiusShift (h z : ℂ) : ℂ := z / (1 + h * z)

def cassiniHyperedgeEnergy {d : ℕ} (z : Fin d → ℂ) : ℂ :=
  (∏ i, z i) * vandermondeProd z ^ 2

private theorem prod_prod_Ioi_pair_eq_pow
    {d : ℕ} (a : Fin d → ℂ) (ha : ∀ i, a i ≠ 0) :
    (∏ i, ∏ j ∈ Finset.Ioi i, a j * a i) =
      (∏ i, a i) ^ (d - 1) := by
  by_cases hd : d = 0
  · subst d
    simp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let P : ℂ := ∏ i, a i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  rw [Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun j _ => a j)]
  have hinner (i : Fin d) : (∏ j ∈ ({i}ᶜ : Finset (Fin d)), a j) = P / a i := by
    apply (eq_div_iff (ha i)).2
    simpa only [P, Finset.prod_singleton] using
      Finset.prod_compl_mul_prod ({i} : Finset (Fin d)) a
  simp_rw [hinner]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, P]
  change P ^ d / P = P ^ (d - 1)
  rw [show d = (d - 1) + 1 by omega, pow_succ]
  field_simp
  congr 1

private theorem vandermondeProd_cassiniMobiusShift
    {d : ℕ} (h : ℂ) (z : Fin d → ℂ)
    (hne : ∀ i, 1 + h * z i ≠ 0) :
    vandermondeProd (fun i => cassiniMobiusShift h (z i)) =
      vandermondeProd z / (∏ i, (1 + h * z i)) ^ (d - 1) := by
  rw [vandermondeProd, vandermondeProd]
  simp_rw [cassiniMobiusShift]
  have hdiff (i j : Fin d) :
      z j / (1 + h * z j) - z i / (1 + h * z i) =
        (z j - z i) / ((1 + h * z j) * (1 + h * z i)) := by
    rw [div_sub_div (z j) (z i) (hne j) (hne i)]
    congr 1
    ring
  simp_rw [hdiff]
  simp_rw [Finset.prod_div_distrib]
  rw [prod_prod_Ioi_pair_eq_pow (fun i => 1 + h * z i) hne]

theorem cassiniHyperedgeEnergy_mobiusShift
    {d : ℕ} (h : ℂ) (z : Fin d → ℂ)
    (hne : ∀ i, 1 + h * z i ≠ 0) :
    cassiniHyperedgeEnergy (fun i => cassiniMobiusShift h (z i)) =
      cassiniHyperedgeEnergy z /
        (∏ i, (1 + h * z i)) ^ (2 * d - 1) := by
  rw [cassiniHyperedgeEnergy, cassiniHyperedgeEnergy,
    vandermondeProd_cassiniMobiusShift h z hne]
  simp_rw [cassiniMobiusShift]
  rw [Finset.prod_div_distrib]
  have hprod : (∏ i, (1 + h * z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  by_cases hd : d = 0
  · subst d
    simp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  field_simp [hprod]
  have hexp : 2 * d - 1 = 1 + 2 * (d - 1) := by omega
  rw [hexp, pow_add, pow_one, Nat.mul_comm 2 (d - 1)]
  ring

def cassiniHyperedgeConformalOrbit {d : ℕ} (z : Fin d → ℂ) (h : ℂ) : ℂ :=
  cassiniHyperedgeEnergy z /
    (∏ i, (1 + h * z i)) ^ (2 * d - 1)

theorem cassiniHyperedgeEnergy_mobiusShift_eq_conformalOrbit
    {d : ℕ} (h : ℂ) (z : Fin d → ℂ)
    (hne : ∀ i, 1 + h * z i ≠ 0) :
    cassiniHyperedgeEnergy (fun i => cassiniMobiusShift h (z i)) =
      cassiniHyperedgeConformalOrbit z h := by
  exact cassiniHyperedgeEnergy_mobiusShift h z hne

theorem hasDerivAt_cassiniHyperedgeConformalOrbit_zero
    {d : ℕ} (z : Fin d → ℂ) :
    HasDerivAt (cassiniHyperedgeConformalOrbit z)
      (-((2 * d - 1 : ℕ) : ℂ) * (∑ i, z i) * cassiniHyperedgeEnergy z) 0 := by
  let k : ℕ := 2 * d - 1
  let P : ℂ → ℂ := ∏ i, fun h => 1 + h * z i
  have hbase (i : Fin d) :
      HasDerivAt (fun h : ℂ => 1 + h * z i) (z i) 0 := by
    simpa only [one_mul] using
      (hasDerivAt_mul_const (x := (0 : ℂ)) (z i)).const_add 1
  have hprod := HasDerivAt.finsetProd
    (u := (Finset.univ : Finset (Fin d)))
    (f := fun i h => 1 + h * z i)
    (f' := z)
    (x := (0 : ℂ)) (fun i _ => hbase i)
  have hP : HasDerivAt P (∑ i, z i) 0 := by
    change HasDerivAt (∏ i, fun h : ℂ => 1 + h * z i) _ 0
    simpa only [zero_mul, add_zero, Finset.prod_const_one,
      smul_eq_mul, one_mul] using hprod
  have hpow : HasDerivAt (P ^ k)
      ((k : ℂ) * ∑ i, z i) 0 := by
    simpa only [P, Finset.prod_apply, zero_mul, add_zero, Finset.prod_const_one, one_pow,
      one_mul, mul_one] using hP.pow k
  have hP0 : (P ^ k) 0 = 1 := by
    simp [P, Finset.prod_apply]
  have hinvOuter : HasDerivAt (fun y : ℂ => y⁻¹) (-1) ((P ^ k) 0) := by
    rw [hP0]
    simpa using hasDerivAt_inv (x := (1 : ℂ)) one_ne_zero
  have hinv : HasDerivAt (fun h : ℂ => ((P ^ k) h)⁻¹)
      (-((k : ℂ) * ∑ i, z i)) 0 := by
    convert hinvOuter.comp 0 hpow using 1
    all_goals first | rfl | ring
  have hmulOuter : HasDerivAt
      (fun y : ℂ => cassiniHyperedgeEnergy z * y)
      (cassiniHyperedgeEnergy z) (((P ^ k) 0)⁻¹) := by
    rw [hP0]
    simpa using hasDerivAt_const_mul (x := (1 : ℂ)) (cassiniHyperedgeEnergy z)
  have hquot' : HasDerivAt
      (fun h : ℂ => cassiniHyperedgeEnergy z * ((P ^ k) h)⁻¹)
      (-(cassiniHyperedgeEnergy z) * ((k : ℂ) * ∑ i, z i)) 0 := by
    convert hmulOuter.comp 0 hinv using 1
    all_goals first | rfl | ring
  have horbit : HasDerivAt (cassiniHyperedgeConformalOrbit z)
      (-(cassiniHyperedgeEnergy z) * ((k : ℂ) * ∑ i, z i)) 0 := by
    have hfun : cassiniHyperedgeConformalOrbit z =
        (fun h : ℂ => cassiniHyperedgeEnergy z * ((P ^ k) h)⁻¹) := by
      funext h
      simp only [cassiniHyperedgeConformalOrbit, P, k, Pi.pow_apply,
        Finset.prod_apply, div_eq_mul_inv]
    rw [hfun]
    exact hquot'
  convert horbit using 1
  dsimp only [k]
  ring

theorem hasDerivAt_cassiniHyperedgeEnergy_mobiusShift_zero
    {d : ℕ} (z : Fin d → ℂ) :
    HasDerivAt
      (fun h => cassiniHyperedgeEnergy (fun i => cassiniMobiusShift h (z i)))
      (-((2 * d - 1 : ℕ) : ℂ) * (∑ i, z i) * cassiniHyperedgeEnergy z) 0 := by
  apply (hasDerivAt_cassiniHyperedgeConformalOrbit_zero z).congr_of_eventuallyEq
  have hne : ∀ᶠ h : ℂ in nhds 0, ∀ i, 1 + h * z i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun h : ℂ => 1 + h * z i) 0 :=
      ((hasDerivAt_mul_const (x := (0 : ℂ)) (z i)).const_add 1).continuousAt
    exact hc.eventually_ne (by simp)
  filter_upwards [hne] with h hh
  exact cassiniHyperedgeEnergy_mobiusShift_eq_conformalOrbit h z hh

end

end RHTower
