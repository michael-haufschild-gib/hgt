import GaloisForLFunctions.HTGeometry.HenselFactorization
import GaloisForLFunctions.HTGeometry.NewtonFibreLift

/-!
# Uniqueness in the completed critical fibre

The Newton construction produces a lift of every coprime point of the pure critical fibre.  This
file proves the complementary statement: such a lift is unique in its adic residue class.

If two correction pairs agree modulo `I^k`, subtracting their factorisation equations shows that
their linearised difference is an error modulo `I^(k+1)`.  The coprime-splitting estimate then puts
the two differences themselves in `I^(k+1)`.  Induction and adic Hausdorffness make them zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- A polynomial below the horizon that is divisible by the horizon is zero, over any nontrivial
coefficient ring. -/
theorem eq_zero_of_X_pow_dvd_of_natDegree_lt_of_commRing [Nontrivial S] {L : ℕ} {p : S[X]}
    (hdvd : (X : S[X]) ^ L ∣ p) (hdeg : p.natDegree < L) : p = 0 := by
  have hmod : p %ₘ X ^ L = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := S) L)).2 hdvd
  ext i
  by_cases hi : i < L
  · have hcoeff := congrArg (fun q : S[X] => q.coeff i) hmod
    rwa [coeff_modByMonic_X_pow, if_pos hi, Polynomial.coeff_zero] at hcoeff
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hdeg (Nat.le_of_not_gt hi))

/-- **Adic uniqueness of a deformed coprime factorisation over the horizon.** -/
theorem deformed_factorisation_unique [Nontrivial S] (I : Ideal S) [IsHausdorff I S]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A B Γ Γ' P Q P' Q' : S[X]}
    (hA : A.Monic) (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n)
    (hcop : IsCoprime A B)
    (hΓ : CoeffMem I Γ) (hΓ' : CoeffMem I Γ')
    (hP : CoeffMem I P) (hQ : CoeffMem I Q)
    (hP' : CoeffMem I P') (hQ' : CoeffMem I Q')
    (hPdeg : P.natDegree < m) (hQdeg : Q.natDegree < n)
    (hP'deg : P'.natDegree < m) (hQ'deg : Q'.natDegree < n)
    (hdvd : (X : S[X]) ^ (m + n) ∣
      inversionError (A + Γ + P) (B + Γ' + Q))
    (hdvd' : (X : S[X]) ^ (m + n) ∣
      inversionError (A + Γ + P') (B + Γ' + Q')) :
    P = P' ∧ Q = Q' := by
  let dP : S[X] := P - P'
  let dQ : S[X] := Q - Q'
  have hdPdeg : dP.natDegree < m :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hPdeg hP'deg)
  have hdQdeg : dQ.natDegree < n :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hQdeg hQ'deg)
  have hdPmem : CoeffMem I dP := hP.sub hP'
  have hdQmem : CoeffMem I dQ := hQ.sub hQ'
  let H : S[X] := dP * B + A * dQ
  let R : S[X] := dP * (Γ' + Q') + (Γ + P') * dQ + dP * dQ
  have hdiff :
      inversionError (A + Γ + P) (B + Γ' + Q) -
          inversionError (A + Γ + P') (B + Γ' + Q') = H + R := by
    dsimp only [H, R, dP, dQ, inversionError]
    ring
  have hdivHR : (X : S[X]) ^ (m + n) ∣ H + R := by
    rw [← hdiff]
    exact dvd_sub hdvd hdvd'
  have hHdeg : H.natDegree < m + n := by
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    apply max_lt
    · calc
        (dP * B).natDegree ≤ dP.natDegree + B.natDegree :=
          Polynomial.natDegree_mul_le
        _ < m + n := by omega
    · calc
        (A * dQ).natDegree ≤ A.natDegree + dQ.natDegree :=
          Polynomial.natDegree_mul_le
        _ < m + n := by omega
  have hcontract : ∀ k : ℕ, 1 ≤ k →
      CoeffMem (I ^ k) dP → CoeffMem (I ^ k) dQ →
      CoeffMem (I ^ (k + 1)) dP ∧ CoeffMem (I ^ (k + 1)) dQ := by
    intro k hk hdPk hdQk
    have hpowR : I ^ k * I ≤ I ^ (k + 1) := by
      rw [pow_succ]
    have hpowL : I * I ^ k ≤ I ^ (k + 1) := by
      rw [mul_comm]
      exact hpowR
    have hpow2 : I ^ k * I ^ k ≤ I ^ (k + 1) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    have hRmem : CoeffMem (I ^ (k + 1)) R := by
      dsimp only [R]
      exact
        ((CoeffMem.mul hdPk (hΓ'.add hQ')).mono hpowR).add
          ((CoeffMem.mul (hΓ.add hP') hdQk).mono hpowL) |>.add
            ((CoeffMem.mul hdPk hdQk).mono hpow2)
    have hne : (X : S[X]) ^ (m + n) ≠ 1 := by
      intro heq
      have hnat := congrArg Polynomial.natDegree heq
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one] at hnat
      omega
    let R₀ : S[X] := R %ₘ X ^ (m + n)
    have hR₀deg : R₀.natDegree < m + n := by
      dsimp only [R₀]
      have hlt := Polynomial.natDegree_modByMonic_lt R
        (monic_X_pow (R := S) (m + n)) hne
      rwa [Polynomial.natDegree_X_pow] at hlt
    have hR₀mem : CoeffMem (I ^ (k + 1)) R₀ :=
      hRmem.modByMonic_X_pow (m + n)
    have hdivR : (X : S[X]) ^ (m + n) ∣ R - R₀ := by
      exact X_pow_dvd_sub_modByMonic R (m + n)
    have hdivSmall : (X : S[X]) ^ (m + n) ∣ H + R₀ := by
      have : H + R₀ = (H + R) - (R - R₀) := by ring
      rw [this]
      exact dvd_sub hdivHR hdivR
    have hsmallzero : H + R₀ = 0 :=
      eq_zero_of_X_pow_dvd_of_natDegree_lt_of_commRing hdivSmall
        (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hHdeg hR₀deg))
    have hHeq : H = -R₀ := by linear_combination hsmallzero
    have hHmem : CoeffMem (I ^ (k + 1)) H := by
      rw [hHeq]
      exact hR₀mem.neg
    exact coprimeSplit_coeff_mem hA hAdeg hBdeg hm hn hcop (I ^ (k + 1))
      hHmem hdPdeg hdQdeg rfl
  have hall : ∀ k : ℕ,
      CoeffMem (I ^ (k + 1)) dP ∧ CoeffMem (I ^ (k + 1)) dQ := by
    intro k
    induction k with
    | zero => simpa using And.intro hdPmem hdQmem
    | succ k ih =>
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          hcontract (k + 1) (by omega) ih.1 ih.2
  have hdPzero : dP = 0 := by
    ext i
    apply IsHausdorff.haus (inferInstance : IsHausdorff I S) (dP.coeff i)
    intro k
    rw [smodEq_iff_sub_mem]
    simpa using (Ideal.pow_le_pow_right (by omega : k ≤ k + 1)) ((hall k).1 i)
  have hdQzero : dQ = 0 := by
    ext i
    apply IsHausdorff.haus (inferInstance : IsHausdorff I S) (dQ.coeff i)
    intro k
    rw [smodEq_iff_sub_mem]
    simpa using (Ideal.pow_le_pow_right (by omega : k ≤ k + 1)) ((hall k).2 i)
  exact ⟨sub_eq_zero.mp hdPzero, sub_eq_zero.mp hdQzero⟩

end GaloisForLFunctions.HTGeometry
