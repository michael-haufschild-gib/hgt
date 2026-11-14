import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchDecomposition

/-!
# Exact splitting of nonzero Kummer branch points

For the inverse-power coefficient family over the square finite field,
every prime above a nonzero auxiliary-field branch point has ramification
index `N/gcd(N,R)` and residue degree one. The fundamental degree sum
therefore gives exactly `gcd(N,R)` primes in the actual normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n R : ℕ)
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ)
    (a : (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ)

/-- Every nonzero auxiliary-field branch splits into exactly `gcd(Q+1,R)` actual normalization primes. -/
theorem squareKummer_primePowerBranch_primes_card :
    (IsDedekindDomain.primesOverFinset
      (Ideal.span {X - C ((a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) :
        SquareConstantField p (kummerSquareIndex d n))})
      (SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R)
        (p ^ (d + 1) - 2) R)).card = Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R := by
  classical
  let K := SquareConstantField p (kummerSquareIndex d n)
  let B := SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
  let F := FractionRing K[X]
  let L := SquareKummerField p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
  let α : K := a
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C α)
  let T := IsDedekindDomain.primesOverFinset (Ideal.span {X - C α}) B
  let N := p ^ (kummerSquareIndex d n + 1) + 1
  let δ := Nat.gcd N R
  let D := N / δ
  letI : (Ideal.span {X - C α}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C α}) ≠ ⊥ := v.ne_bot
  have hDpos : 0 < D := Nat.div_pos
    (Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left N R))
    (Nat.gcd_pos_of_pos_left R (Nat.succ_pos _))
  have hterm : ∀ P ∈ T,
      (Ideal.span {X - C α}).ramificationIdx' P * (Ideal.span {X - C α}).inertiaDeg' P = D := by
    intro P hP
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
    letI := hprime
    letI := hover
    have hP0 : P ≠ ⊥ := by
      have hinj : Function.Injective (algebraMap K[X] B) :=
        Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
      have hm := (Ideal.mem_of_liesOver P (Ideal.span {X - C α}) (X - C α)).mp
        (Ideal.mem_span_singleton_self _)
      intro h
      have hz : algebraMap K[X] B (X - C α) = 0 := by simpa only [h, Ideal.mem_bot] using hm
      exact X_sub_C_ne_zero α (hinj (hz.trans (map_zero _).symm))
    let w : HeightOneSpectrum B := ⟨P, hprime, hP0⟩
    have he := squareKummer_primePowerBranch_ramification_exact p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) R d a w
    have hf := squareKummer_primePowerBranch_inertia p d n R η a w
    change (Ideal.span {X - C α}).ramificationIdx' P = D at he
    change (Ideal.span {X - C α}).inertiaDeg' P = 1 at hf
    rw [he, hf, mul_one]
  have hsum := Ideal.sum_ramification_inertia B F L hv0
  rw [kummerBranchField_finrank] at hsum
  have hcount : T.card * D = N := by
    calc
      T.card * D = ∑ P ∈ T, D := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ = ∑ P ∈ T, (Ideal.span {X - C α}).ramificationIdx' P *
          (Ideal.span {X - C α}).inertiaDeg' P :=
        Finset.sum_congr rfl (fun P hP => (hterm P hP).symm)
      _ = N := hsum
  change T.card = δ
  apply Nat.eq_of_mul_eq_mul_left hDpos
  have hfactor : D * δ = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N R)
  exact (Nat.mul_comm D T.card).trans (hcount.trans hfactor.symm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
