import GaloisForLFunctions.RHTower.ChiRamanujanCriticalDistinguishedPrime
import GaloisForLFunctions.RHTower.ChiRamanujanCompleteCubicTrace
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact critical source on the complete prime-square grid

Every literal critical atom is grouped on the radical-square torsion grid.
Finite Fourier injectivity identifies its exact distinguished-prime product
mass. Cofactor units give a bijection with all local prime-square coordinates,
including zero and nonprimitive residues. The local factors are precisely
shifted valuation coefficients; two distinct primitive prime-square factors
force zero mass. No infinite-prime limit or physical cancellation estimate
is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

private lemma grid_phase_add (n : ℤ) (x y : ℝ) :
    ramanujanFourierPhase n (x+y) =
      ramanujanFourierPhase n x * ramanujanFourierPhase n y := by
  unfold ramanujanFourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma grid_phase_sum {ι : Type*} (s : Finset ι) (n : ℤ) (x : ι → ℝ) :
    ramanujanFourierPhase n (∑ i ∈ s, x i) =
      ∏ i ∈ s, ramanujanFourierPhase n (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ramanujanFourierPhase]
  | @insert a s ha ih => simp [ha, grid_phase_add, ih]

private lemma grid_subtorsion_sum {p : ℕ} (hp : p ≠ 0) (n : ℤ) :
    (∑ k : Fin (p^2), if p ∣ k.val then
      ramanujanFourierPhase n ((k.val : ℝ)/(p^2 : ℕ)) else 0) =
      if p ∣ n.natAbs then (p : ℂ) else 0 := by
  letI : NeZero p := ⟨hp⟩
  have he := (finProdFinEquiv (m := p) (n := p)).sum_comp
    (fun k => if p ∣ k.val then
      ramanujanFourierPhase n ((k.val : ℝ)/(p*p : ℕ)) else 0)
  rw [pow_two, ← he, Fintype.sum_prod_type]
  have hk (a b : Fin p) : p ∣ b.val+p*a.val ↔ b=0 := by
    simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b.isLt]
    simpa only [Fin.val_zero] using (@Fin.ext_iff p b 0).symm
  change (∑ a : Fin p, ∑ b : Fin p, if p ∣ b.val+p*a.val then
    ramanujanFourierPhase n (((b.val+p*a.val : ℕ) : ℝ)/(p*p : ℕ)) else 0) = _
  simp only [hk]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_zero,
    Nat.zero_add, Nat.cast_mul]
  have hc : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  simp_rw [mul_div_mul_left _ _ hc]
  exact sum_ramanujanFourierPhase_torsion hp n

def ramanujanGridBase (p : ℕ) (k : Fin (p^2)) : ℝ :=
  (if k.val=0 then 1 else 0) - (p : ℝ)⁻¹*(if p ∣ k.val then 1 else 0)

def ramanujanGridTag (p : ℕ) (k : Fin (p^2)) : ℝ :=
  (p : ℝ)⁻¹*(if p ∣ k.val then 1 else 0) - ((p^2 : ℕ) : ℝ)⁻¹

private lemma grid_cast_ite (b : Prop) [Decidable b] :
    ((if b then 1 else 0 : ℝ) : ℂ) = if b then 1 else 0 := by
  split_ifs <;> rfl

private lemma grid_uniform_fourier {p : ℕ} (hp : p ≠ 0) (n : ℤ) :
    (∑ k : Fin (p^2), ((p : ℂ)⁻¹*(if p ∣ k.val then 1 else 0))*
      ramanujanFourierPhase n ((k.val : ℝ)/(p^2 : ℕ))) =
      (ramanujanTorsionIndicator p n.natAbs : ℂ) := by
  simp only [mul_assoc, ite_mul, one_mul, zero_mul]
  rw [← Finset.mul_sum, grid_subtorsion_sum hp]
  split_ifs <;> simp_all [ramanujanTorsionIndicator]

theorem ramanujanGridBase_fourier {p : ℕ} (hp : p ≠ 0) (n : ℤ) :
    (∑ k : Fin (p^2), (ramanujanGridBase p k : ℂ)*
      ramanujanFourierPhase n ((k.val : ℝ)/(p^2 : ℕ))) =
      (1-ramanujanTorsionIndicator p n.natAbs : ℝ) := by
  letI : NeZero (p^2) := ⟨pow_ne_zero 2 hp⟩
  simp only [ramanujanGridBase, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, grid_cast_ite,
    sub_mul, Finset.sum_sub_distrib]
  rw [grid_uniform_fourier hp]
  have he (k : Fin (p^2)) : k.val=0 ↔ k=0 := by
    simpa only [Fin.val_zero] using (@Fin.ext_iff (p^2) k 0).symm
  simp [he, ite_mul, ramanujanFourierPhase]

theorem ramanujanGridTag_fourier {p : ℕ} (hp : p ≠ 0) (n : ℤ) :
    (∑ k : Fin (p^2), (ramanujanGridTag p k : ℂ)*
      ramanujanFourierPhase n ((k.val : ℝ)/(p^2 : ℕ))) =
      (ramanujanTorsionIndicator p n.natAbs - ramanujanTorsionIndicator (p^2) n.natAbs : ℝ) := by
  simp only [ramanujanGridTag, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, grid_cast_ite,
    sub_mul, Finset.sum_sub_distrib]
  rw [grid_uniform_fourier hp, ← Finset.mul_sum,
    sum_ramanujanFourierPhase_torsion (pow_ne_zero 2 hp)]
  split_ifs <;> simp_all [ramanujanTorsionIndicator]

abbrev RamanujanGridPrime (P : Finset ℕ) := {p // p ∈ P.filter Nat.Prime}

abbrev RamanujanLocalGrid (P : Finset ℕ) := (p : RamanujanGridPrime P) → Fin (p.val^2)

def ramanujanLocalGridNode {P : Finset ℕ} (x : RamanujanLocalGrid P) : ℝ :=
  ∑ p, ((x p).val : ℝ)/(p.val^2 : ℕ)

def ramanujanLocalGridWeight (P : Finset ℕ) (x : RamanujanLocalGrid P) : ℝ :=
  ∑ p : RamanujanGridPrime P, Real.log p.val *
    ∏ q : RamanujanGridPrime P,
      if q.val=p.val then ramanujanGridTag q.val (x q) else ramanujanGridBase q.val (x q)

private lemma grid_selected_fourier {p q : ℕ} (hq : q ≠ 0) (n : ℤ) :
    (∑ k : Fin (q^2),
      ((if q=p then ramanujanGridTag q k else ramanujanGridBase q k : ℝ) : ℂ)*
        ramanujanFourierPhase n ((k.val : ℝ)/(q^2 : ℕ))) =
    ((if q=p then ramanujanTorsionIndicator q n.natAbs-ramanujanTorsionIndicator (q^2) n.natAbs
      else 1-ramanujanTorsionIndicator q n.natAbs : ℝ) : ℂ) := by
  split_ifs <;> first | exact ramanujanGridTag_fourier hq n | exact ramanujanGridBase_fourier hq n

private lemma grid_selected_product (P : Finset ℕ) (p : RamanujanGridPrime P) (n : ℕ) :
    (∏ q : RamanujanGridPrime P,
      if q.val=p.val then ramanujanTorsionIndicator q.val n-ramanujanTorsionIndicator (q.val^2) n
      else 1-ramanujanTorsionIndicator q.val n) =
      (ramanujanTorsionIndicator p.val n-ramanujanTorsionIndicator (p.val^2) n)*
        ∏ q ∈ (P.filter Nat.Prime).erase p.val, (1-ramanujanTorsionIndicator q n) := by
  change (∏ q : (P.filter Nat.Prime),
    (fun q : ℕ => if q=p.val then ramanujanTorsionIndicator q n-ramanujanTorsionIndicator (q^2) n
      else 1-ramanujanTorsionIndicator q n) q.val) = _
  have hu : (Finset.univ : Finset (RamanujanGridPrime P))=(P.filter Nat.Prime).attach := by
    ext
    simp
  rw [hu, Finset.prod_attach (P.filter Nat.Prime) (fun q : ℕ =>
    if q=p.val then ramanujanTorsionIndicator q n-ramanujanTorsionIndicator (q^2) n
      else 1-ramanujanTorsionIndicator q n), ← Finset.mul_prod_erase _ _ p.property]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [if_neg (Finset.mem_erase.mp hq).1]

theorem ramanujanLocalGridWeight_fourier (P : Finset ℕ) (n : ℤ) :
    (∑ x : RamanujanLocalGrid P, (ramanujanLocalGridWeight P x : ℂ)*
      ramanujanFourierPhase n (ramanujanLocalGridNode x)) =
      (ramanujanDistinguishedPrimeMultiplier P n.natAbs : ℂ) := by
  classical
  simp only [ramanujanLocalGridWeight, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Finset.sum_mul, ramanujanLocalGridNode, grid_phase_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.prod_mul_distrib, ← Finset.mul_sum]
  trans ∑ p : RamanujanGridPrime P, (Real.log p.val : ℂ) *
    ∏ q : RamanujanGridPrime P,
      ((if q.val=p.val then ramanujanTorsionIndicator q.val n.natAbs-
        ramanujanTorsionIndicator (q.val^2) n.natAbs
        else 1-ramanujanTorsionIndicator q.val n.natAbs : ℝ) : ℂ)
  · apply Finset.sum_congr rfl
    intro p hp
    congr 1
    calc
      _ = ∏ q : RamanujanGridPrime P, ∑ k : Fin (q.val^2),
          ((if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k : ℝ) : ℂ)*
            ramanujanFourierPhase n ((k.val : ℝ)/(q.val^2 : ℕ)) := by
        convert (Fintype.prod_sum (fun (q : RamanujanGridPrime P) (k : Fin (q.val^2)) =>
          ((if q.val=p.val then ramanujanGridTag q.val k else ramanujanGridBase q.val k : ℝ) : ℂ)*
            ramanujanFourierPhase n ((k.val : ℝ)/(q.val^2 : ℕ)))).symm using 1
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q hq
        exact grid_selected_fourier (Finset.mem_filter.mp q.property).2.ne_zero n
  simp only [← Complex.ofReal_prod, grid_selected_product, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  congr 1
  have hu : (Finset.univ : Finset (RamanujanGridPrime P))=(P.filter Nat.Prime).attach := by
    ext
    simp
  rw [hu, Finset.sum_attach (P.filter Nat.Prime) (fun p : ℕ => Real.log p *
    ((ramanujanTorsionIndicator p n.natAbs-ramanujanTorsionIndicator (p^2) n.natAbs)*
      ∏ q ∈ (P.filter Nat.Prime).erase p, (1-ramanujanTorsionIndicator q n.natAbs)))]
  simp only [ramanujanDistinguishedPrimeMultiplier, mul_assoc]

def ramanujanGridModulus (P : Finset ℕ) : ℕ := ramanujanPrimeRadical P ^ 2

private lemma grid_modulus_nezero (P : Finset ℕ) : ramanujanGridModulus P ≠ 0 :=
  pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr
    (fun _ hp => (Finset.mem_filter.mp hp).2.ne_zero))

local instance grid_modulus_neZero (P : Finset ℕ) : NeZero (ramanujanGridModulus P) :=
  ⟨grid_modulus_nezero P⟩

def ramanujanCriticalGridIndex {P : Finset ℕ} (a : RamanujanPrimeOnlyAtomIndex P) :
    ZMod (ramanujanGridModulus P) :=
  (a.1.2.val*(ramanujanGridModulus P / a.1.1.val) +
    a.2.2.val*(ramanujanGridModulus P / a.2.1.val^2) : ℕ)

def ramanujanLocalGridIndex {P : Finset ℕ} (x : RamanujanLocalGrid P) :
    ZMod (ramanujanGridModulus P) :=
  (∑ p : RamanujanGridPrime P, (x p).val*(ramanujanGridModulus P / p.val^2) : ℕ)

private lemma grid_phase_cast {Q : ℕ} [NeZero Q] (a : ℕ) (n : ℤ) :
    ramanujanFourierPhase n ((a : ℝ)/Q) =
      ZMod.stdAddChar ((a : ZMod Q)*(n : ZMod Q)) := by
  have h := ZMod.stdAddChar_coe (N := Q) ((a : ℤ)*n)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  rw [h, ramanujanFourierPhase]
  congr 1
  push_cast
  ring

private lemma grid_scale {Q d : ℕ} (hQ : Q ≠ 0) (hd : d ∣ Q) (a : ℕ) :
    (a : ℝ)/d = (a*(Q/d) : ℕ)/Q := by
  have hQc : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  rw [Nat.cast_mul, Nat.cast_div_charZero hd]
  field_simp

theorem ramanujanCriticalGridIndex_phase (P : Finset ℕ)
    (a : RamanujanPrimeOnlyAtomIndex P) (n : ℤ) :
    ramanujanFourierPhase n (ramanujanPrimeOnlyAtomNode a) =
      ZMod.stdAddChar (ramanujanCriticalGridIndex a*(n : ZMod (ramanujanGridModulus P))) := by
  have hd : a.1.1.val ∣ ramanujanGridModulus P :=
    (Nat.dvd_of_mem_divisors a.1.1.property).trans (dvd_pow_self _ (by omega : 2 ≠ 0))
  have he : a.2.1.val^2 ∣ ramanujanGridModulus P :=
    pow_dvd_pow_of_dvd (Nat.dvd_of_mem_divisors a.2.1.property) 2
  rw [ramanujanPrimeOnlyAtomNode, ramanujanAtomNode, ramanujanSquareSieveAtomNode,
    grid_scale (grid_modulus_nezero P) hd,
    grid_scale (grid_modulus_nezero P) he, ← add_div, ← Nat.cast_add, grid_phase_cast]
  rfl

theorem ramanujanLocalGridIndex_phase (P : Finset ℕ) (x : RamanujanLocalGrid P) (n : ℤ) :
    ramanujanFourierPhase n (ramanujanLocalGridNode x) =
      ZMod.stdAddChar (ramanujanLocalGridIndex x*(n : ZMod (ramanujanGridModulus P))) := by
  have he (p : RamanujanGridPrime P) :
      ((x p).val : ℝ)/(p.val^2 : ℕ) =
        ((x p).val*(ramanujanGridModulus P/p.val^2) : ℕ)/ramanujanGridModulus P :=
    grid_scale (grid_modulus_nezero P)
      (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ p.property) 2) _
  simp only [ramanujanLocalGridNode, he]
  rw [← Finset.sum_div, ← Nat.cast_sum, grid_phase_cast]
  rfl

private def grid_mass {Q : ℕ} {α : Type*} [Fintype α]
    (u : α → ZMod Q) (w : α → ℂ) (k : ZMod Q) : ℂ :=
  ∑ a, if u a=k then w a else 0

private lemma grid_mass_fourier {Q : ℕ} [NeZero Q] {α : Type*} [Fintype α]
    (u : α → ZMod Q) (w : α → ℂ) (n : ZMod Q) :
    (∑ k, grid_mass u w k*ZMod.stdAddChar (k*n)) =
      ∑ a, w a*ZMod.stdAddChar (u a*n) := by
  classical
  simp only [grid_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp [ite_mul]

theorem ramanujanCriticalPrimeAtomWeight_grouped (P : Finset ℕ)
    (k : ZMod (ramanujanGridModulus P)) :
    (∑ a : RamanujanPrimeOnlyAtomIndex P,
      if ramanujanCriticalGridIndex a=k then (ramanujanCriticalPrimeAtomWeight P a : ℂ) else 0) =
    ∑ x : RamanujanLocalGrid P,
      if ramanujanLocalGridIndex x=k then (ramanujanLocalGridWeight P x : ℂ) else 0 := by
  have he (n : ZMod (ramanujanGridModulus P)) :
      (∑ a : RamanujanPrimeOnlyAtomIndex P,
        (ramanujanCriticalPrimeAtomWeight P a : ℂ)*ZMod.stdAddChar (ramanujanCriticalGridIndex a*n)) =
      ∑ x : RamanujanLocalGrid P,
        (ramanujanLocalGridWeight P x : ℂ)*ZMod.stdAddChar (ramanujanLocalGridIndex x*n) := by
    have h := (sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished P (n.val : ℤ)).trans
      (ramanujanLocalGridWeight_fourier P (n.val : ℤ)).symm
    simpa only [ramanujanCriticalGridIndex_phase, ramanujanLocalGridIndex_phase,
      Int.cast_natCast, ZMod.natCast_zmod_val] using h
  have hm : grid_mass ramanujanCriticalGridIndex (fun a => (ramanujanCriticalPrimeAtomWeight P a : ℂ)) =
      grid_mass ramanujanLocalGridIndex (fun x => (ramanujanLocalGridWeight P x : ℂ)) := by
    apply ZMod.dft.injective
    ext n
    simp only [ZMod.dft_apply, smul_eq_mul]
    simp_rw [mul_comm (ZMod.stdAddChar _), ← mul_neg]
    rw [grid_mass_fourier, grid_mass_fourier, he]
  exact congrFun hm k

private lemma grid_modulus_prod (P : Finset ℕ) :
    ramanujanGridModulus P = ∏ p ∈ P.filter Nat.Prime, p^2 := by
  simp only [ramanujanGridModulus, ramanujanPrimeRadical, Finset.prod_pow]

private lemma grid_cofactor (P : Finset ℕ) (p : RamanujanGridPrime P) :
    ramanujanGridModulus P / p.val^2 = ∏ q ∈ (P.filter Nat.Prime).erase p.val, q^2 := by
  have he : ramanujanGridModulus P =
      p.val^2 * ∏ q ∈ (P.filter Nat.Prime).erase p.val, q^2 := by
    rw [grid_modulus_prod]
    exact (Finset.mul_prod_erase _ _ p.property).symm
  rw [he, Nat.mul_div_right _ (pow_pos (Finset.mem_filter.mp p.property).2.pos 2)]

private lemma grid_cofactor_coprime (P : Finset ℕ) (p : RamanujanGridPrime P) :
    (ramanujanGridModulus P / p.val^2).Coprime (p.val^2) := by
  rw [grid_cofactor, Nat.coprime_prod_left_iff]
  intro q hq
  exact Nat.coprime_pow_primes 2 2
    (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).2
    (Finset.mem_filter.mp p.property).2 (Finset.mem_erase.mp hq).1

private lemma grid_projection (P : Finset ℕ) (p : RamanujanGridPrime P) (x : RamanujanLocalGrid P) :
    ZMod.castHom (m := p.val^2) (n := ramanujanGridModulus P)
      (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ p.property) 2)
      (ZMod (p.val^2)) (ramanujanLocalGridIndex x) =
        ((x p).val : ZMod (p.val^2)) * (ramanujanGridModulus P / p.val^2 : ℕ) := by
  classical
  change (ZMod.cast ((∑ q : RamanujanGridPrime P,
    (x q).val*(ramanujanGridModulus P/q.val^2) : ℕ) : ZMod (ramanujanGridModulus P)) :
    ZMod (p.val^2)) = _
  rw [ZMod.cast_natCast (m := p.val^2) (n := ramanujanGridModulus P)
    (R := ZMod (p.val^2))
    (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ p.property) 2)]
  simp only [Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_eq_single p
  · intro q hq hqp
    have hd : p.val^2 ∣ ramanujanGridModulus P / q.val^2 := by
      rw [grid_cofactor]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr
        ⟨fun h => hqp (Subtype.ext h.symm), p.property⟩)
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero]
  · simp

theorem ramanujanLocalGridIndex_injective (P : Finset ℕ) :
    Function.Injective (ramanujanLocalGridIndex (P := P)) := by
  intro x y h
  funext p
  have he := congrArg (ZMod.castHom (m := p.val^2) (n := ramanujanGridModulus P)
    (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ p.property) 2) (ZMod (p.val^2))) h
  rw [grid_projection P p x, grid_projection P p y] at he
  have hu := (ZMod.isUnit_iff_coprime _ _).mpr (grid_cofactor_coprime P p)
  have hv := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (hu.mul_right_cancel he)
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt (x p).isLt, Nat.mod_eq_of_lt (y p).isLt] using hv

theorem ramanujanCriticalPrimeAtomWeight_localProduct (P : Finset ℕ) (x : RamanujanLocalGrid P) :
    (∑ a : RamanujanPrimeOnlyAtomIndex P,
      if ramanujanCriticalGridIndex a=ramanujanLocalGridIndex x
        then (ramanujanCriticalPrimeAtomWeight P a : ℂ) else 0) =
      (ramanujanLocalGridWeight P x : ℂ) := by
  rw [ramanujanCriticalPrimeAtomWeight_grouped]
  simp only [(ramanujanLocalGridIndex_injective P).eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

def ramanujanGridValuation (p : ℕ) (k : Fin (p^2)) : ℤ :=
  if k.val=0 then 0 else if p ∣ k.val then -1 else -2

theorem ramanujanGridBase_normalized (p : Nat.Primes) (k : Fin (p.val^2)) :
    ramanujanGridBase p.val k = (1-(p.val : ℝ)⁻¹)*
      coefficient (p.val : ℝ)⁻¹ (ramanujanGridValuation p.val k) := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hm : (p.val : ℝ)-1 ≠ 0 := by linarith
  by_cases hk : k.val=0
  · simp [ramanujanGridBase, ramanujanGridValuation, coefficient, hk]
  by_cases hd : p.val ∣ k.val
  · simp only [ramanujanGridBase, ramanujanGridValuation, hk, hd, if_false, if_true,
      coefficient, zero_sub, mul_one]
    field_simp [hm]
  · simp [ramanujanGridBase, ramanujanGridValuation, coefficient, hk, hd]

/-- The distinguished local coefficient has the additional valuation shift. -/
theorem ramanujanGridTag_normalized (p : Nat.Primes) (k : Fin (p.val^2)) :
    ramanujanGridTag p.val k = (1-(p.val : ℝ)⁻¹)*(p.val : ℝ)⁻¹*
      coefficient (p.val : ℝ)⁻¹ (ramanujanGridValuation p.val k+1) := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hm : (p.val : ℝ)-1 ≠ 0 := by linarith
  have hm' : -1+(p.val : ℝ) ≠ 0 := by linarith
  by_cases hk : k.val=0
  · simp [ramanujanGridTag, ramanujanGridValuation, coefficient, hk]
    ring
  by_cases hd : p.val ∣ k.val
  · norm_num [ramanujanGridTag, ramanujanGridValuation, coefficient, hk, hd]
    ring
  · norm_num [ramanujanGridTag, ramanujanGridValuation, coefficient, hk, hd]
    field_simp [hm, hm']

/-- Every radical-square torsion node has exactly one tuple of local coordinates. -/
theorem ramanujanLocalGridIndex_bijective (P : Finset ℕ) :
    Function.Bijective (ramanujanLocalGridIndex (P := P)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨ramanujanLocalGridIndex_injective P, ?_⟩
  rw [ZMod.card]
  change Fintype.card ((p : RamanujanGridPrime P) → Fin (p.val^2)) = _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_coe_sort (P.filter Nat.Prime) (fun p : ℕ => p^2), grid_modulus_prod]

private lemma grid_local_dvd (P : Finset ℕ) (x : RamanujanLocalGrid P)
    (p : RamanujanGridPrime P) {d : ℕ} (hd : d ∣ p.val^2) :
    d ∣ (ramanujanLocalGridIndex x).val ↔ d ∣ (x p).val := by
  let hQ : p.val^2 ∣ ramanujanGridModulus P :=
    pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ p.property) 2
  have hl (k : ZMod (ramanujanGridModulus P)) :
      ZMod.castHom hd (ZMod d) (ZMod.castHom hQ (ZMod (p.val^2)) k) =
        (k.val : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val k]
    simp only [map_natCast]
  have he := congrArg (ZMod.castHom hd (ZMod d)) (grid_projection P p x)
  rw [hl] at he
  simp only [map_mul, map_natCast] at he
  have hu : IsUnit ((ramanujanGridModulus P / p.val^2 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime _ _).mpr ((grid_cofactor_coprime P p).of_dvd_right hd)
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, he]
  constructor
  · intro h
    apply hu.mul_right_cancel
    simpa only [zero_mul] using h
  · intro h
    rw [h, zero_mul]

def ramanujanCriticalGridWeight (P : Finset ℕ) (k : ZMod (ramanujanGridModulus P)) : ℝ :=
  ∑ p ∈ P.filter Nat.Prime,
    Real.log p*((p : ℝ)⁻¹*ramanujanTorsionIndicator p k.val-((p^2 : ℕ) : ℝ)⁻¹)*
      ∏ q ∈ (P.filter Nat.Prime).erase p,
        (ramanujanTorsionIndicator (q^2) k.val-(q : ℝ)⁻¹*ramanujanTorsionIndicator q k.val)

private lemma grid_base_direct (P : Finset ℕ) (x : RamanujanLocalGrid P) (p : RamanujanGridPrime P) :
    ramanujanGridBase p.val (x p) =
      ramanujanTorsionIndicator (p.val^2) (ramanujanLocalGridIndex x).val-
        (p.val : ℝ)⁻¹*ramanujanTorsionIndicator p.val (ramanujanLocalGridIndex x).val := by
  have hz : p.val^2 ∣ (x p).val ↔ (x p).val=0 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt (x p).isLt]
  simp only [ramanujanGridBase, ramanujanTorsionIndicator,
    grid_local_dvd P x p (dvd_refl (p.val^2)),
    grid_local_dvd P x p (dvd_pow_self _ (by omega : 2 ≠ 0)), hz]

private lemma grid_tag_direct (P : Finset ℕ) (x : RamanujanLocalGrid P) (p : RamanujanGridPrime P) :
    ramanujanGridTag p.val (x p) =
      (p.val : ℝ)⁻¹*ramanujanTorsionIndicator p.val (ramanujanLocalGridIndex x).val-
        ((p.val^2 : ℕ) : ℝ)⁻¹ := by
  simp only [ramanujanGridTag, ramanujanTorsionIndicator,
    grid_local_dvd P x p (dvd_pow_self _ (by omega : 2 ≠ 0))]

private lemma grid_product_replace (P : Finset ℕ) (p : RamanujanGridPrime P) (a b : ℕ → ℝ) :
    (∏ q : RamanujanGridPrime P, if q.val=p.val then a q.val else b q.val) =
      a p.val * ∏ q ∈ (P.filter Nat.Prime).erase p.val, b q := by
  rw [Finset.prod_coe_sort (P.filter Nat.Prime) (fun q => if q=p.val then a q else b q),
    ← Finset.mul_prod_erase _ _ p.property]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [if_neg (Finset.mem_erase.mp hq).1]

theorem ramanujanLocalGridWeight_eq_direct (P : Finset ℕ) (x : RamanujanLocalGrid P) :
    ramanujanLocalGridWeight P x = ramanujanCriticalGridWeight P (ramanujanLocalGridIndex x) := by
  let a : ℕ → ℝ := fun p =>
    (p : ℝ)⁻¹*ramanujanTorsionIndicator p (ramanujanLocalGridIndex x).val-((p^2 : ℕ) : ℝ)⁻¹
  let b : ℕ → ℝ := fun q =>
    ramanujanTorsionIndicator (q^2) (ramanujanLocalGridIndex x).val-
      (q : ℝ)⁻¹*ramanujanTorsionIndicator q (ramanujanLocalGridIndex x).val
  simp only [ramanujanLocalGridWeight, grid_tag_direct, grid_base_direct]
  change (∑ p : RamanujanGridPrime P, Real.log p.val *
    ∏ q : RamanujanGridPrime P, if q.val=p.val then a q.val else b q.val) = _
  simp_rw [grid_product_replace P _ a b]
  rw [Finset.sum_coe_sort (P.filter Nat.Prime)
    (fun p : ℕ => Real.log p * (a p * ∏ q ∈ (P.filter Nat.Prime).erase p, b q))]
  dsimp [a,b]
  simp only [ramanujanCriticalGridWeight, mul_assoc]

/-- The actual grouped critical mass at every grid node, with no frequency cutoff. -/
theorem ramanujanCriticalPrimeAtomWeight_grid (P : Finset ℕ) (k : ZMod (ramanujanGridModulus P)) :
    (∑ a : RamanujanPrimeOnlyAtomIndex P,
      if ramanujanCriticalGridIndex a=k then (ramanujanCriticalPrimeAtomWeight P a : ℂ) else 0) =
      (ramanujanCriticalGridWeight P k : ℂ) := by
  obtain ⟨x, rfl⟩ := (ramanujanLocalGridIndex_bijective P).2 k
  rw [ramanujanCriticalPrimeAtomWeight_localProduct, ramanujanLocalGridWeight_eq_direct]

/-- Two distinct primitive prime-square coordinates annihilate every distinguished term. -/
theorem ramanujanCriticalGridWeight_two_primitive (P : Finset ℕ)
    (k : ZMod (ramanujanGridModulus P))
    (p q : RamanujanGridPrime P) (hpq : p ≠ q)
    (hp : ¬p.val ∣ k.val) (hq : ¬q.val ∣ k.val) : ramanujanCriticalGridWeight P k = 0 := by
  have hb (r : ℕ) (hr : ¬r ∣ k.val) :
      ramanujanTorsionIndicator (r^2) k.val-(r : ℝ)⁻¹*ramanujanTorsionIndicator r k.val=0 := by
    have hr2 : ¬r^2 ∣ k.val := fun h => hr ((dvd_pow_self r (by omega : 2 ≠ 0)).trans h)
    simp [ramanujanTorsionIndicator, hr, hr2]
  unfold ramanujanCriticalGridWeight
  apply Finset.sum_eq_zero
  intro r hr
  suffices ∏ s ∈ (P.filter Nat.Prime).erase r,
      (ramanujanTorsionIndicator (s^2) k.val-(s : ℝ)⁻¹*ramanujanTorsionIndicator s k.val)=0 by
    rw [this, mul_zero]
  by_cases hpr : p.val=r
  · apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨?_, q.property⟩) (hb q.val hq)
    intro hqr
    exact hpq (Subtype.ext (hpr.trans hqr.symm))
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hpr, p.property⟩) (hb p.val hp)


end RHTower.BAGTrace
