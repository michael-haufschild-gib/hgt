import GaloisForLFunctions.HTGeometry.EigenvolumeHorizonCapstone

/-!
# The local order law from the pullback law and the Jacobian

The pullback of the rational form `a / b` along a self-map is `(φ a · J) / (φ b)`, where `J` is
the Jacobian factor.  The order of a pullback scales by the ramification index, so if the Jacobian
has order `e - 1` at a prime divisor then the shifted order law

`ord (pullback) + 1 = e * (ord (form) + 1)`

holds there.  This reduces the local order law, which the horizon capstone takes as data, to the
single statement that the Jacobian has order `e - 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {B : Type*}
variable [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

theorem orderAt_ne_top (P : PrimeDivisor B) {x : B} (hx : x ≠ 0) : orderAt P x ≠ ⊤ := by
  show addVal (Localization.AtPrime P.1) (algebraMap B (Localization.AtPrime P.1) x) ≠ ⊤
  rw [Ne, addVal_eq_top_iff]
  exact algebraMap_localization_ne_zero P hx

theorem orderAt_mul (P : PrimeDivisor B) (x y : B) :
    orderAt P (x * y) = orderAt P x + orderAt P y := by
  simp only [orderAt, map_mul, AddValuation.map_mul]

theorem orderAt_toNat_spec (P : PrimeDivisor B) {x : B} (hx : x ≠ 0) :
    orderAt P x = (((orderAt P x).toNat : ℕ) : ℕ∞) :=
  (ENat.coe_toNat (orderAt_ne_top P hx)).symm

/-- **The shifted local order law from the pullback law and the Jacobian.** -/
theorem formOrder_pullback_shiftLaw (φ : B →+* B)
    (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
    (P : PrimeDivisor B)
    {π : Localization.AtPrime (divisorBelow φ hwd P).1} (hπ : Irreducible π)
    (e : ℕ) (hepos : 0 < e)
    (he : addVal (Localization.AtPrime P.1)
        (localMapAt φ P (divisorBelow φ hwd P) rfl π) = (e : ℕ∞))
    {a b J : B} (ha : a ≠ 0) (hb : b ≠ 0)
    (hJ : orderAt P J = ((e - 1 : ℕ) : ℕ∞)) :
    formOrder (φ a * J) (φ b) P + 1 =
      (e : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1) := by
  set Q := divisorBelow φ hwd P
  have hpa : orderAt P (φ a) = (e : ℕ∞) * orderAt Q a :=
    orderAt_map_eq_mul_ramification φ P Q rfl hπ e he a ha
  have hpb : orderAt P (φ b) = (e : ℕ∞) * orderAt Q b :=
    orderAt_map_eq_mul_ramification φ P Q rfl hπ e he b hb
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

section Eigenvolume

variable (φ : B →+* B)
variable (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
variable (e : PrimeDivisor B → ℕ) (hone : ∀ P, 1 ≤ e P)
variable (π : ∀ P : PrimeDivisor B, Localization.AtPrime (divisorBelow φ hwd P).1)
variable (hπ : ∀ P, Irreducible (π P))
variable (he : ∀ P, addVal (Localization.AtPrime P.1)
  (localMapAt φ P (divisorBelow φ hwd P) rfl (π P)) = ((e P : ℕ) : ℕ∞))
variable {a b J : B} (ha : a ≠ 0) (hb : b ≠ 0)
variable (hJ : ∀ P, orderAt P J = ((e P - 1 : ℕ) : ℕ∞))
variable (heig : ∀ P, formOrder (φ a * J) (φ b) P = formOrder a b P)

include hone hπ he ha hb hJ heig in
/-- **The local order law holds for an eigenvolume.**  If the rational form `a / b` has the same
divisor as its pullback `(φ a · J) / (φ b)`, and the Jacobian factor `J` has order `e - 1` at every
prime divisor, then the shifted order law holds everywhere.  This discharges the law that the
horizon theorem takes as data. -/
theorem eigenvolume_shiftLaw (P : PrimeDivisor B) :
    formOrder a b P + 1 = (e P : ℤ) * (formOrder a b (divisorBelow φ hwd P) + 1) := by
  rw [← heig P]
  exact formOrder_pullback_shiftLaw φ hwd P (hπ P) (e P) (hone P) (he P) ha hb (hJ P)

include hone hπ he ha hb hJ heig in
/-- **The horizon of an eigenvolume is a reduced divisor.** -/
theorem eigenvolume_formOrder_eq_neg_one
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    {P : PrimeDivisor B} (hP : formOrder a b P ≠ 0) :
    formOrder a b P = -1 :=
  formOrder_eq_neg_one φ hwd hsurj ha hb e hone
    (eigenvolume_shiftLaw φ hwd e hone π hπ he ha hb hJ heig) hram hP

include hone hπ he ha hb hJ heig in
/-- **The horizon of an eigenvolume is totally invariant.** -/
theorem eigenvolume_formOrder_ne_zero_iff
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    (P : PrimeDivisor B) :
    formOrder a b P ≠ 0 ↔ formOrder a b (divisorBelow φ hwd P) ≠ 0 :=
  formOrder_ne_zero_iff φ hwd hsurj ha hb e hone
    (eigenvolume_shiftLaw φ hwd e hone π hπ he ha hb hJ heig) hram P

include hone hπ he ha hb hJ heig in
/-- **A self-map preserving an eigenvolume is unramified off its horizon.** -/
theorem eigenvolume_ramificationIndex_eq_one_off_horizon
    {P : PrimeDivisor B} (hP : formOrder a b P = 0) :
    e P = 1 :=
  ramificationIndex_eq_one_off_horizon φ hwd e
    (eigenvolume_shiftLaw φ hwd e hone π hπ he ha hb hJ heig) hP

end Eigenvolume

end GaloisForLFunctions.HTGeometry
