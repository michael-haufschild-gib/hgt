import GaloisForLFunctions.HTGeometry.EigenvolumeUnitInvariance

/-!
# The local order law at a single prime divisor

The packaged form of the order law quantifies over all prime divisors at once, because it is
stated through the divisor map.  A concrete instance normally supplies the data at one divisor at a
time, so the law is restated here with the two divisors and the identification between them as
explicit arguments.  Nothing is assumed about any other prime divisor.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

/-- **The shifted order law at a single prime divisor.** -/
theorem formOrder_shiftLaw_at (φ : B →+* B) (P Q : PrimeDivisor B)
    (hQ : Q.1 = Ideal.comap φ P.1)
    {π : Localization.AtPrime Q.1} (hπ : Irreducible π) (e : ℕ) (hepos : 0 < e)
    (he : addVal (Localization.AtPrime P.1) (localMapAt φ P Q hQ π) = (e : ℕ∞))
    {a b J : B} (ha : a ≠ 0) (hb : b ≠ 0)
    (hJ : orderAt P J = ((e - 1 : ℕ) : ℕ∞)) :
    formOrder (φ a * J) (φ b) P + 1 = (e : ℤ) * (formOrder a b Q + 1) := by
  have hpa : orderAt P (φ a) = (e : ℕ∞) * orderAt Q a :=
    orderAt_map_eq_mul_ramification φ P Q hQ hπ e he a ha
  have hpb : orderAt P (φ b) = (e : ℕ∞) * orderAt Q b :=
    orderAt_map_eq_mul_ramification φ P Q hQ hπ e he b hb
  obtain ⟨na, hna⟩ : ∃ n : ℕ, orderAt Q a = (n : ℕ∞) := ⟨_, orderAt_toNat_spec Q ha⟩
  obtain ⟨nb, hnb⟩ : ∃ n : ℕ, orderAt Q b = (n : ℕ∞) := ⟨_, orderAt_toNat_spec Q hb⟩
  have hta : (orderAt Q a).toNat = na := by rw [hna]; exact ENat.toNat_coe _
  have htb : (orderAt Q b).toNat = nb := by rw [hnb]; exact ENat.toNat_coe _
  have hnuma : orderAt P (φ a * J) = ((e * na + (e - 1) : ℕ) : ℕ∞) := by
    rw [orderAt_mul, hpa, hJ, hna, Nat.cast_add, Nat.cast_mul]
  have hnumb : orderAt P (φ b) = ((e * nb : ℕ) : ℕ∞) := by
    rw [hpb, hnb, Nat.cast_mul]
  have htoa : (orderAt P (φ a * J)).toNat = e * na + (e - 1) := by
    rw [hnuma]; exact ENat.toNat_coe _
  have htob : (orderAt P (φ b)).toNat = e * nb := by
    rw [hnumb]; exact ENat.toNat_coe _
  have h1 : 1 ≤ e := hepos
  show ((orderAt P (φ a * J)).toNat : ℤ) - ((orderAt P (φ b)).toNat : ℤ) + 1 =
    (e : ℤ) * ((((orderAt Q a).toNat : ℤ) - ((orderAt Q b).toNat : ℤ)) + 1)
  rw [htoa, htob, hta, htb]
  push_cast [Nat.cast_sub h1]
  ring

/-- **The eigenvolume order law at a single prime divisor.**  With the eigenvolume condition at
that divisor, the shifted law relates the order there to the order below it. -/
theorem formOrder_eigen_shiftLaw_at (φ : B →+* B) (P Q : PrimeDivisor B)
    (hQ : Q.1 = Ideal.comap φ P.1)
    {π : Localization.AtPrime Q.1} (hπ : Irreducible π) (e : ℕ) (hepos : 0 < e)
    (he : addVal (Localization.AtPrime P.1) (localMapAt φ P Q hQ π) = (e : ℕ∞))
    {a b J : B} (ha : a ≠ 0) (hb : b ≠ 0)
    (hJ : orderAt P J = ((e - 1 : ℕ) : ℕ∞))
    (heig : formOrder (φ a * J) (φ b) P = formOrder a b P) :
    formOrder a b P + 1 = (e : ℤ) * (formOrder a b Q + 1) := by
  rw [← heig]
  exact formOrder_shiftLaw_at φ P Q hQ hπ e hepos he ha hb hJ

end GaloisForLFunctions.HTGeometry
