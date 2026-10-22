/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 13.5 (`t45`),
algebraic core.

For an affine scheme `X = Spec R` and a rank-one valuation ring `𝒪` with maximal ideal `𝔪`, the
`𝒪`-valued points of `W_rat (X)` are the pointed multiplicative maps `Q : R → 𝒪` satisfying

* a) `𝔭 = Q⁻¹(0)` is additively closed — hence a prime ideal — and `Q` factors through `R / 𝔭`;
* b) `𝔮 = Q⁻¹(𝔪)` is additively closed — hence a prime ideal — and `Q mod 𝔪` factors through
  `R / 𝔮`;

and these are equivalent to the pointwise conditions

* a') `Q f' = 0 → Q (f + f') = Q f`;
* b') `Q f' ∈ 𝔪 → Q (f + f') ≡ Q f mod 𝔪`.

All of that is proved here: the two equivalences, that `𝔭` and `𝔮` are prime ideals with
`𝔭 ⊆ 𝔮`, the factorization of `Q` through `R / 𝔭` as a pointed multiplicative map, and that `Q`
takes unit values outside `𝔮` — the input for extending `Q` to the local ring `R_𝔮`.
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace RHTower

open IsLocalRing

variable {R O : Type*} [CommRing R] [CommRing O]

/-- **Deninger, Corollary 13.5 (`t45`), condition a').**  The zero set of a pointed multiplicative
map is additively closed exactly when the map is unchanged by adding an element of that set —
which is exactly the assertion that the map factors through the quotient. -/
def DeningerAdditiveOnZeros (Q : R →*₀ O) : Prop :=
  ∀ f f' : R, Q f' = 0 → Q (f + f') = Q f

/-- **Deninger, Corollary 13.5 (`t45`), condition b').** -/
def DeningerAdditiveModMax [IsLocalRing O] (Q : R →*₀ O) : Prop :=
  ∀ f f' : R, Q f' ∈ maximalIdeal O → Q (f + f') - Q f ∈ maximalIdeal O

/-- **Deninger, Corollary 13.5 (`t45`), a).**  The zero set of a pointed multiplicative map
satisfying a') is a prime ideal. -/
def deningerZeroIdeal (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q) : Ideal R where
  carrier := {f | Q f = 0}
  add_mem' := by
    intro f f' hf hf'
    show Q (f + f') = 0
    rw [ha f f' hf']
    exact hf
  zero_mem' := map_zero Q
  smul_mem' := by
    intro r f hf
    show Q (r • f) = 0
    rw [smul_eq_mul, map_mul, show Q f = 0 from hf, mul_zero]

@[simp] theorem deningerMem_zeroIdeal {Q : R →*₀ O} {ha : DeningerAdditiveOnZeros Q} {f : R} :
    f ∈ deningerZeroIdeal Q ha ↔ Q f = 0 := Iff.rfl

theorem deningerZeroIdeal_isPrime [IsDomain O] (Q : R →*₀ O)
    (ha : DeningerAdditiveOnZeros Q) : (deningerZeroIdeal Q ha).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : R) ∈ deningerZeroIdeal Q ha := htop ▸ Submodule.mem_top
    rw [deningerMem_zeroIdeal, map_one] at h1
    exact one_ne_zero h1
  · intro f g hfg
    rw [deningerMem_zeroIdeal, map_mul] at hfg
    rcases mul_eq_zero.1 hfg with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **Deninger, Corollary 13.5 (`t45`), b).**  The preimage of the maximal ideal under a pointed
multiplicative map satisfying b') is a prime ideal. -/
def deningerMaxIdeal [IsLocalRing O] (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) : Ideal R where
  carrier := {f | Q f ∈ maximalIdeal O}
  add_mem' := by
    intro f f' hf hf'
    show Q (f + f') ∈ maximalIdeal O
    have h := hb f f' hf'
    have : Q (f + f') = (Q (f + f') - Q f) + Q f := by ring
    rw [this]
    exact Ideal.add_mem _ h hf
  zero_mem' := by
    show Q 0 ∈ maximalIdeal O
    rw [map_zero]
    exact Ideal.zero_mem _
  smul_mem' := by
    intro r f hf
    show Q (r • f) ∈ maximalIdeal O
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _ hf

@[simp] theorem deningerMem_maxIdeal [IsLocalRing O] {Q : R →*₀ O} {hb : DeningerAdditiveModMax Q}
    {f : R} : f ∈ deningerMaxIdeal Q hb ↔ Q f ∈ maximalIdeal O := Iff.rfl

theorem deningerMaxIdeal_isPrime [IsLocalRing O] (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) :
    (deningerMaxIdeal Q hb).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : R) ∈ deningerMaxIdeal Q hb := htop ▸ Submodule.mem_top
    rw [deningerMem_maxIdeal, map_one] at h1
    exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · intro f g hfg
    rw [deningerMem_maxIdeal, map_mul] at hfg
    haveI := (maximalIdeal.isMaximal O).isPrime
    rcases (maximalIdeal.isMaximal O).isPrime.mem_or_mem hfg with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem deningerZeroIdeal_le_maxIdeal [IsLocalRing O] (Q : R →*₀ O)
    (ha : DeningerAdditiveOnZeros Q) (hb : DeningerAdditiveModMax Q) :
    deningerZeroIdeal Q ha ≤ deningerMaxIdeal Q hb := by
  intro f hf
  rw [deningerMem_zeroIdeal] at hf
  rw [deningerMem_maxIdeal, hf]
  exact Ideal.zero_mem _

/-- Outside the prime `Q⁻¹(𝔪)` the values of `Q` are units. -/
theorem deningerIsUnit_of_notMem_maxIdeal [IsLocalRing O] (Q : R →*₀ O)
    (hb : DeningerAdditiveModMax Q) {s : R} (hs : s ∉ deningerMaxIdeal Q hb) :
    IsUnit (Q s) := by
  rw [deningerMem_maxIdeal] at hs
  exact notMem_maximalIdeal.1 hs

/-- **Deninger, Corollary 13.5 (`t45`): a) ⟺ a').**  Condition a') says exactly that `Q` is
constant on the cosets of its zero set, i.e. that it factors through the quotient. -/
theorem deningerAdditiveOnZeros_iff (Q : R →*₀ O) :
    DeningerAdditiveOnZeros Q ↔ ∀ f f' : R, Q (f - f') = 0 → Q f = Q f' := by
  constructor
  · intro ha f f' h
    have := ha f' (f - f') h
    rwa [add_sub_cancel] at this
  · intro ha f f' hf'
    refine ha (f + f') f ?_
    rwa [add_sub_cancel_left]

/-- **Deninger, Corollary 13.5 (`t45`): the factorization of a).**  A pointed multiplicative map
satisfying a') factors through the quotient by its zero ideal. -/
noncomputable def deningerQuotientLift (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q) :
    (R ⧸ deningerZeroIdeal Q ha) →*₀ O where
  toFun := Quotient.lift Q (by
    intro a b hab
    have h : Q (a - b) = 0 := by
      have : a - b ∈ deningerZeroIdeal Q ha := (Submodule.quotientRel_def _).1 hab
      exact this
    exact (deningerAdditiveOnZeros_iff Q).1 ha a b h)
  map_zero' := map_zero Q
  map_one' := map_one Q
  map_mul' := by
    intro x y
    refine Quotient.inductionOn₂ x y fun a b => ?_
    exact map_mul Q a b

@[simp] theorem deningerQuotientLift_mk (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q) (f : R) :
    deningerQuotientLift Q ha (Ideal.Quotient.mk _ f) = Q f := rfl

/-- **Deninger, Corollary 13.5 (`t45`): b) ⟺ b').** -/
theorem deningerAdditiveModMax_iff [IsLocalRing O] (Q : R →*₀ O) :
    DeningerAdditiveModMax Q ↔
      ∀ f f' : R, Q (f - f') ∈ maximalIdeal O → Q f - Q f' ∈ maximalIdeal O := by
  constructor
  · intro hb f f' h
    have := hb f' (f - f') h
    rwa [add_sub_cancel] at this
  · intro hb f f' hf'
    refine hb (f + f') f ?_
    rwa [add_sub_cancel_left]

attribute [instance] deningerMaxIdeal_isPrime

variable {R O : Type*} [CommRing R] [CommRing O] [IsLocalRing O]

/-- **Deninger, Corollary 13.5 (`t45`), the extension to the local ring.**  A pointed
multiplicative map `Q : R → 𝒪` whose preimage of the maximal ideal is a prime `𝔮` extends to the
localization `R_𝔮`, by `r / s ↦ Q r · (Q s)⁻¹`; the values `Q s` for `s ∉ 𝔮` are units. -/
noncomputable def deningerLocalQ (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) :
    Localization.AtPrime (deningerMaxIdeal Q hb) →*₀ O where
  toFun z := Localization.liftOn z (fun r s => Q r * Ring.inverse (Q (s : R))) (by
    intro a c b d h
    rw [Localization.r_iff_exists] at h
    obtain ⟨u, hu⟩ := h
    have hQu : IsUnit (Q (u : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb u.2
    have hQb : IsUnit (Q (b : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb b.2
    have hQd : IsUnit (Q (d : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb d.2
    have hu' : Q (u : R) * (Q (d : R) * Q a) = Q (u : R) * (Q (b : R) * Q c) := by
      have := congrArg Q hu
      simpa [map_mul, mul_assoc] using this
    have hcancel : Q (d : R) * Q a = Q (b : R) * Q c := hQu.mul_left_cancel hu'
    have hbinv : Ring.inverse (Q (b : R)) * Q (b : R) = 1 := Ring.inverse_mul_cancel _ hQb
    have hdinv : Ring.inverse (Q (d : R)) * Q (d : R) = 1 := Ring.inverse_mul_cancel _ hQd
    calc Q a * Ring.inverse (Q (b : R))
        = (Ring.inverse (Q (d : R)) * Q (d : R)) * (Q a * Ring.inverse (Q (b : R))) := by
          rw [hdinv, one_mul]
      _ = Ring.inverse (Q (d : R)) * (Q (d : R) * Q a) * Ring.inverse (Q (b : R)) := by ring
      _ = Ring.inverse (Q (d : R)) * (Q (b : R) * Q c) * Ring.inverse (Q (b : R)) := by
          rw [hcancel]
      _ = Q c * Ring.inverse (Q (d : R)) * (Ring.inverse (Q (b : R)) * Q (b : R)) := by ring
      _ = Q c * Ring.inverse (Q (d : R)) := by rw [hbinv, mul_one])
  map_zero' := by
    show Localization.liftOn (0 : Localization.AtPrime (deningerMaxIdeal Q hb)) _ _ = 0
    rw [show (0 : Localization.AtPrime (deningerMaxIdeal Q hb))
        = Localization.mk 0 1 from (Localization.mk_zero 1).symm, Localization.liftOn_mk]
    simp
  map_one' := by
    show Localization.liftOn (1 : Localization.AtPrime (deningerMaxIdeal Q hb)) _ _ = 1
    rw [show (1 : Localization.AtPrime (deningerMaxIdeal Q hb))
        = Localization.mk 1 1 from (Localization.mk_one).symm, Localization.liftOn_mk]
    simp
  map_mul' := by
    intro x y
    refine Localization.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    rw [Localization.mk_mul]
    show Localization.liftOn (Localization.mk (a * c) (b * d)) _ _
      = Localization.liftOn (Localization.mk a b) _ _ * Localization.liftOn (Localization.mk c d) _ _
    rw [Localization.liftOn_mk, Localization.liftOn_mk, Localization.liftOn_mk]
    have hQb : IsUnit (Q (b : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb b.2
    have hQd : IsUnit (Q (d : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb d.2
    rw [Submonoid.coe_mul, map_mul Q (b : R) (d : R), map_mul Q a c,
      Ring.mul_inverse_rev' (Commute.all (Q (b : R)) (Q (d : R)))]
    ring

@[simp] theorem deningerLocalQ_mk (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q)
    (r : R) (s : (deningerMaxIdeal Q hb).primeCompl) :
    deningerLocalQ Q hb (Localization.mk r s) = Q r * Ring.inverse (Q (s : R)) := rfl

theorem deningerIsUnit_inverse (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q)
    (s : (deningerMaxIdeal Q hb).primeCompl) : IsUnit (Ring.inverse (Q (s : R))) := by
  obtain ⟨u, hu⟩ := deningerIsUnit_of_notMem_maxIdeal Q hb s.2
  refine ⟨u⁻¹, ?_⟩
  rw [← hu]
  exact (Ring.inverse_unit u).symm

/-- The extension of `Q` to `R_𝔮` restricts to `Q` on `R`. -/
@[simp] theorem deningerLocalQ_algebraMap (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) (r : R) :
    deningerLocalQ Q hb
      (algebraMap R (Localization.AtPrime (deningerMaxIdeal Q hb)) r) = Q r := by
  rw [← Localization.mk_one_eq_algebraMap, deningerLocalQ_mk]
  simp

/-- **Deninger, Corollary 13.5 (`t45`).**  `Q_𝔮⁻¹ (0) = 𝔭 R_𝔮` in coordinates. -/
theorem deningerLocalQ_eq_zero_iff (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q)
    (r : R) (s : (deningerMaxIdeal Q hb).primeCompl) :
    deningerLocalQ Q hb (Localization.mk r s) = 0 ↔ Q r = 0 := by
  rw [deningerLocalQ_mk]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := deningerIsUnit_inverse Q hb s
    have := congrArg (fun z => z * ((u⁻¹ : Oˣ) : O)) h
    simp only [zero_mul] at this
    rw [mul_assoc, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at this
    exact this
  · intro h
    rw [h, zero_mul]

/-- **Deninger, Corollary 13.5 (`t45`).**  `Q_𝔮⁻¹ (𝔪) = 𝔮 R_𝔮` in coordinates. -/
theorem deningerLocalQ_mem_maximalIdeal_iff (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q)
    (r : R) (s : (deningerMaxIdeal Q hb).primeCompl) :
    deningerLocalQ Q hb (Localization.mk r s) ∈ maximalIdeal O ↔ Q r ∈ maximalIdeal O := by
  rw [deningerLocalQ_mk]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := deningerIsUnit_inverse Q hb s
    have hmul : Q r * Ring.inverse (Q (s : R)) * ((u⁻¹ : Oˣ) : O) = Q r := by
      rw [mul_assoc, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    rw [← hmul]
    exact Ideal.mul_mem_right _ _ h
  · intro h
    exact Ideal.mul_mem_right _ _ h

/-- The value of the extension on `s' a / (s s')` is its value on `a / s`. -/
theorem deningerLocalQ_shift (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) (a : R)
    (s s' : (deningerMaxIdeal Q hb).primeCompl) :
    Q ((s' : R) * a) * Ring.inverse (Q (((s * s' : (deningerMaxIdeal Q hb).primeCompl)) : R))
      = Q a * Ring.inverse (Q (s : R)) := by
  have hQs' : IsUnit (Q (s' : R)) := deningerIsUnit_of_notMem_maxIdeal Q hb s'.2
  have hrev : Ring.inverse (Q (((s * s' : (deningerMaxIdeal Q hb).primeCompl)) : R))
      = Ring.inverse (Q (s' : R)) * Ring.inverse (Q (s : R)) := by
    rw [Submonoid.coe_mul, map_mul,
      Ring.mul_inverse_rev' (Commute.all (Q (s : R)) (Q (s' : R)))]
  rw [hrev, map_mul]
  calc Q (s' : R) * Q a * (Ring.inverse (Q (s' : R)) * Ring.inverse (Q (s : R)))
      = (Q (s' : R) * Ring.inverse (Q (s' : R))) * (Q a * Ring.inverse (Q (s : R))) := by ring
    _ = Q a * Ring.inverse (Q (s : R)) := by
        rw [Ring.mul_inverse_cancel _ hQs', one_mul]

/-- **Deninger, Corollary 13.5 (`t45`), condition 2) for the extension.**  The extension `Q_𝔮` is
again unchanged by adding an element of its zero set: clearing the denominator turns the assertion
into condition a') for `Q`. -/
theorem deningerLocalQ_additiveOnZeros (Q : R →*₀ O) (ha : DeningerAdditiveOnZeros Q)
    (hb : DeningerAdditiveModMax Q) :
    DeningerAdditiveOnZeros (deningerLocalQ Q hb) := by
  intro z z'
  refine Localization.induction_on₂ z z' ?_
  rintro ⟨a, s⟩ ⟨a', s'⟩ hz'
  have ha' : Q a' = 0 := (deningerLocalQ_eq_zero_iff Q hb a' s').1 hz'
  rw [Localization.add_mk, deningerLocalQ_mk, deningerLocalQ_mk]
  have hsum : Q ((s : R) * a' + (s' : R) * a) = Q ((s' : R) * a) := by
    have h := ha ((s' : R) * a) ((s : R) * a') (by rw [map_mul, ha', mul_zero])
    rw [add_comm] at h
    exact h
  rw [hsum, deningerLocalQ_shift Q hb a s s']

/-- **Deninger, Corollary 13.5 (`t45`), condition 3) for the extension.**  The extension `Q_𝔮` is
again additive modulo the maximal ideal. -/
theorem deningerLocalQ_additiveModMax (Q : R →*₀ O) (hb : DeningerAdditiveModMax Q) :
    DeningerAdditiveModMax (deningerLocalQ Q hb) := by
  intro z z'
  refine Localization.induction_on₂ z z' ?_
  rintro ⟨a, s⟩ ⟨a', s'⟩ hz'
  have ha' : Q a' ∈ maximalIdeal O :=
    (deningerLocalQ_mem_maximalIdeal_iff Q hb a' s').1 hz'
  rw [Localization.add_mk, deningerLocalQ_mk, deningerLocalQ_mk,
    ← deningerLocalQ_shift Q hb a s s']
  have hmem : Q ((s : R) * a' + (s' : R) * a) - Q ((s' : R) * a) ∈ maximalIdeal O := by
    have h := hb ((s' : R) * a) ((s : R) * a') (by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ ha')
    rw [add_comm ((s' : R) * a) ((s : R) * a')] at h
    exact h
  have hfac : Q ((s : R) * a' + (s' : R) * a)
        * Ring.inverse (Q (((s * s' : (deningerMaxIdeal Q hb).primeCompl)) : R))
      - Q ((s' : R) * a)
        * Ring.inverse (Q (((s * s' : (deningerMaxIdeal Q hb).primeCompl)) : R))
      = (Q ((s : R) * a' + (s' : R) * a) - Q ((s' : R) * a))
        * Ring.inverse (Q (((s * s' : (deningerMaxIdeal Q hb).primeCompl)) : R)) := by
    ring
  rw [hfac]
  exact Ideal.mul_mem_right _ _ hmem

end RHTower
