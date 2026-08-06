import GaloisForLFunctions.HTGeometry.EigenvolumePullbackLaw

/-!
# The eigenvolume condition from a unit multiple

The order of a rational form along a prime divisor depends only on the form and not on the chosen
numerator and denominator, and it is unchanged by multiplication by a unit.  Consequently a form
whose pullback is a unit multiple of itself has the same divisor as its pullback: the eigenvolume
condition holds.

This is the divisorial content of taking the top exterior power of an invariant coframe.  The
pullback of the top wedge is the determinant of the transition matrix times the wedge, and that
determinant is a unit, so the eigenvolume condition is not an assumption about orders but a
consequence of invariance of the coframe.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {B : Type*}
variable [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

/-- **The order of a rational form depends only on the form.**  Two numerator-denominator pairs
representing the same fraction have the same order along every prime divisor. -/
theorem formOrder_eq_of_cross (P : PrimeDivisor B) {a b a' b' : B}
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0)
    (h : a * b' = a' * b) :
    formOrder a b P = formOrder a' b' P := by
  obtain ⟨na, hna⟩ : ∃ n : ℕ, orderAt P a = (n : ℕ∞) := ⟨_, orderAt_toNat_spec P ha⟩
  obtain ⟨nb, hnb⟩ : ∃ n : ℕ, orderAt P b = (n : ℕ∞) := ⟨_, orderAt_toNat_spec P hb⟩
  obtain ⟨na', hna'⟩ : ∃ n : ℕ, orderAt P a' = (n : ℕ∞) := ⟨_, orderAt_toNat_spec P ha'⟩
  obtain ⟨nb', hnb'⟩ : ∃ n : ℕ, orderAt P b' = (n : ℕ∞) := ⟨_, orderAt_toNat_spec P hb'⟩
  have hkey : orderAt P (a * b') = orderAt P (a' * b) := by rw [h]
  rw [orderAt_mul, orderAt_mul, hna, hnb, hna', hnb'] at hkey
  have hnat : na + nb' = na' + nb := by exact_mod_cast hkey
  have hta : (orderAt P a).toNat = na := by rw [hna]; exact ENat.toNat_coe _
  have htb : (orderAt P b).toNat = nb := by rw [hnb]; exact ENat.toNat_coe _
  have hta' : (orderAt P a').toNat = na' := by rw [hna']; exact ENat.toNat_coe _
  have htb' : (orderAt P b').toNat = nb' := by rw [hnb']; exact ENat.toNat_coe _
  show ((orderAt P a).toNat : ℤ) - ((orderAt P b).toNat : ℤ) =
    ((orderAt P a').toNat : ℤ) - ((orderAt P b').toNat : ℤ)
  rw [hta, htb, hta', htb']
  omega

/-- A unit has order zero along every prime divisor. -/
theorem orderAt_unit (P : PrimeDivisor B) (u : Bˣ) : orderAt P (u : B) = 0 :=
  addVal_of_isUnit (u.isUnit.map (algebraMap B (Localization.AtPrime P.1)))

@[simp] theorem formOrder_unit_mul (P : PrimeDivisor B) (u : Bˣ) (a b : B) :
    formOrder ((u : B) * a) b P = formOrder a b P := by
  simp [formOrder, orderAt_mul, orderAt_unit]

/-- **The eigenvolume condition from invariance up to a unit.**  If the pullback of the form
`a / b`, namely `(φ a · J) / (φ b)`, is the unit multiple `u · (a / b)`, then the pullback has the
same order as the form along every prime divisor. -/
theorem eigenvolume_condition_of_unit (φ : B →+* B) {a b J : B}
    (ha : a ≠ 0) (hb : b ≠ 0) (hφaJ : φ a * J ≠ 0) (hφb : φ b ≠ 0)
    (u : Bˣ) (hu : (φ a * J) * b = ((u : B) * a) * φ b) (P : PrimeDivisor B) :
    formOrder (φ a * J) (φ b) P = formOrder a b P := by
  rw [formOrder_eq_of_cross P hφaJ hφb (mul_ne_zero u.ne_zero ha) hb hu]
  exact formOrder_unit_mul P u a b

section UnitEigenvolume

variable (φ : B →+* B)
variable (hwd : ∀ P : PrimeDivisor B, (Ideal.comap φ P.1).height = 1)
variable (e : PrimeDivisor B → ℕ) (hone : ∀ P, 1 ≤ e P)
variable (π : ∀ P : PrimeDivisor B, Localization.AtPrime (divisorBelow φ hwd P).1)
variable (hπ : ∀ P, Irreducible (π P))
variable (he : ∀ P, addVal (Localization.AtPrime P.1)
  (localMapAt φ P (divisorBelow φ hwd P) rfl (π P)) = ((e P : ℕ) : ℕ∞))
variable {a b J : B} (ha : a ≠ 0) (hb : b ≠ 0) (hφaJ : φ a * J ≠ 0) (hφb : φ b ≠ 0)
variable (hJ : ∀ P, orderAt P J = ((e P - 1 : ℕ) : ℕ∞))
variable (u : Bˣ) (hu : (φ a * J) * b = ((u : B) * a) * φ b)

include hone hπ he ha hb hφaJ hφb hJ hu in
/-- **The horizon of a unit eigenvolume is a reduced divisor.**  The hypotheses are now exactly
the geometry: the pullback of the form is a unit multiple of the form, and the Jacobian factor has
order `e - 1` at every prime divisor. -/
theorem unitEigenvolume_formOrder_eq_neg_one
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    {P : PrimeDivisor B} (hP : formOrder a b P ≠ 0) :
    formOrder a b P = -1 :=
  eigenvolume_formOrder_eq_neg_one φ hwd e hone π hπ he ha hb hJ
    (eigenvolume_condition_of_unit φ ha hb hφaJ hφb u hu) hsurj hram hP

include hone hπ he ha hb hφaJ hφb hJ hu in
/-- **The horizon of a unit eigenvolume is totally invariant.** -/
theorem unitEigenvolume_formOrder_ne_zero_iff
    (hsurj : Function.Surjective (divisorBelow φ hwd))
    (hram : ∀ P : PrimeDivisor B, formOrder a b P ≠ 0 → ∀ n : ℕ, 0 < n →
      (divisorBelow φ hwd)^[n] P = P → ∃ k < n, 1 < e ((divisorBelow φ hwd)^[k] P))
    (P : PrimeDivisor B) :
    formOrder a b P ≠ 0 ↔ formOrder a b (divisorBelow φ hwd P) ≠ 0 :=
  eigenvolume_formOrder_ne_zero_iff φ hwd e hone π hπ he ha hb hJ
    (eigenvolume_condition_of_unit φ ha hb hφaJ hφb u hu) hsurj hram P

include hone hπ he ha hb hφaJ hφb hJ hu in
/-- **A self-map preserving a unit eigenvolume is unramified off its horizon.** -/
theorem unitEigenvolume_ramificationIndex_eq_one_off_horizon
    {P : PrimeDivisor B} (hP : formOrder a b P = 0) :
    e P = 1 :=
  eigenvolume_ramificationIndex_eq_one_off_horizon φ hwd e hone π hπ he ha hb hJ
    (eigenvolume_condition_of_unit φ ha hb hφaJ hφb u hu) hP

end UnitEigenvolume

end GaloisForLFunctions.HTGeometry
