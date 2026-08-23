import GaloisForLFunctions.RHTower.DeningerDynSysTiltCorrespondence

/-!
# Additivity modulo `p` and homomorphisms of tilts

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.16
(`t1213n`), first assertion.

Deninger's subspace `Y^⋄ = Y^⋄_{1/p}` consists of the points whose pointed multiplicative map is
additive modulo `p`.  Reduction modulo `p` of a pointed multiplicative map is automatically
multiplicative and pointed, so it is a ring homomorphism exactly when the map is additive modulo
`p`; by the tilting correspondence this happens exactly when the map comes from a homomorphism of
tilts.
-/

namespace RHTower

open Perfection PreTilt

universe u

variable {A O : Type u} [CommRing A] [CommRing O] {p : ℕ} [Fact p.Prime]
variable [Fact (¬ IsUnit (p : A))] [Fact (¬ IsUnit (p : O))]

/-- The reduction modulo `p` of a pointed multiplicative map which is additive modulo `p`, as a
ring homomorphism. -/
def deningerReductionRingHom (χ : PreTilt A p →* O)
    (h : ∀ r s : PreTilt A p, χ (r + s) - χ r - χ s ∈ Ideal.span {(p : O)}) :
    PreTilt A p →+* ModP O p where
  toFun x := Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by
    have hmem := h 0 0
    rw [add_zero, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_sub,
      sub_eq_zero] at hmem
    exact left_eq_add.mp hmem
  map_add' a b := by
    have hmem := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_sub, sub_eq_zero] at hmem
    exact hmem

omit [Fact (¬ IsUnit (p : O))] in
@[simp] theorem deningerReductionRingHom_apply (χ : PreTilt A p →* O)
    (h : ∀ r s : PreTilt A p, χ (r + s) - χ r - χ s ∈ Ideal.span {(p : O)}) (x : PreTilt A p) :
    deningerReductionRingHom χ h x = Ideal.Quotient.mk (Ideal.span {(p : O)}) (χ x) := rfl

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- **Deninger, Proposition 14.16 (`t1213n`), first assertion.**  A pointed multiplicative map
`A♭ → 𝒪` comes from a homomorphism of tilts exactly when it is additive modulo `p`. -/
theorem deningerTiltChar_exists_iff_additiveModP (χ : PreTilt A p →* O) :
    (∃ χflat : PreTilt A p →+* PreTilt O p, deningerTiltChar χflat = χ)
      ↔ ∀ r s : PreTilt A p, χ (r + s) - χ r - χ s ∈ Ideal.span {(p : O)} := by
  rw [deningerTiltChar_exists_iff]
  constructor
  · rintro ⟨χbar, hχ⟩ r s
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, hχ, hχ, hχ, map_add]
    ring
  · intro h
    exact ⟨deningerReductionRingHom χ h, fun x => rfl⟩

/-! ### The untilt is injective at zero -/

/-- The untilt of `0` is `0`: it is its own `p^n`-th power and lies in `(p)`, hence in every power
of `(p)`, and the ring is `p`-adically separated. -/
theorem deningerUntilt_zero : PreTilt.untilt (0 : PreTilt O p) = 0 := by
  set a : O := PreTilt.untilt (0 : PreTilt O p) with ha
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : O)}) a = 0 := by
    rw [ha, PreTilt.mk_untilt_eq_coeff_zero]
    exact map_zero _
  have hbase : (p : O) ∣ a := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq_zero_iff_mem.1 hmk
  have hpow : ∀ n : ℕ, a ^ p ^ n = a := by
    intro n
    have hz : ((frobeniusEquiv (PreTilt O p) p).symm)^[n] (0 : PreTilt O p) = 0 := by
      induction n with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
    have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow (0 : PreTilt O p) n
    rw [hz] at h
    exact h
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]
  intro n
  refine deningerSMod_of_dvd ?_
  rw [sub_zero, ← hpow n]
  refine dvd_trans (pow_dvd_pow (p : O) ?_) (pow_dvd_pow_of_dvd hbase (p ^ n))
  exact Nat.le_of_lt (Nat.lt_pow_self (Fact.out (p := p.Prime)).one_lt)

/-- **Deninger, Proposition 14.16 (`t1213n`).**  Over a reduced ring the untilt vanishes only at
`0`: an `n`-th Frobenius root has `p^n`-th power the given untilt, hence is nilpotent, hence zero,
and its class is the `n`-th coefficient. -/
theorem deningerUntilt_eq_zero_iff [IsReduced O] (x : PreTilt O p) :
    PreTilt.untilt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine Perfection.ext (fun n => ?_)
    have hiter : ((frobenius (PreTilt O p) p)^[n])
        (((frobeniusEquiv (PreTilt O p) p).symm)^[n] x) = x := by
      rw [← coe_frobeniusEquiv]
      exact Function.LeftInverse.iterate
        (fun z => (frobeniusEquiv (PreTilt O p) p).apply_symm_apply z) n x
    have hc0 : PreTilt.coeff 0 (((frobeniusEquiv (PreTilt O p) p).symm)^[n] x)
        = PreTilt.coeff n x := by
      have hstep := PreTilt.coeff_iterate_frobenius 0 n
        (((frobeniusEquiv (PreTilt O p) p).symm)^[n] x)
      rw [hiter, zero_add] at hstep
      exact hstep.symm
    have hpow := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
    rw [h] at hpow
    have hzero : PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm)^[n] x) = 0 :=
      IsReduced.eq_zero _ ⟨p ^ n, hpow⟩
    have := PreTilt.mk_untilt_eq_coeff_zero
      (((frobeniusEquiv (PreTilt O p) p).symm)^[n] x)
    rw [hzero, map_zero] at this
    have hcoeff : PreTilt.coeff n x = 0 := by rw [← hc0, ← this]
    rw [PreTilt.coeff_def] at hcoeff
    rw [hcoeff]
    exact (map_zero (Perfection.coeff (ModP O p) p n)).symm
  · rintro rfl
    exact deningerUntilt_zero

/-- **Deninger, Proposition 14.16 (`t1213n`).**  The pointed multiplicative map attached to a
homomorphism of tilts vanishes exactly where the homomorphism does. -/
theorem deningerTiltChar_eq_zero_iff [IsReduced O] (χ : PreTilt A p →+* PreTilt O p)
    (f : PreTilt A p) : deningerTiltChar χ f = 0 ↔ χ f = 0 := by
  rw [deningerTiltChar_apply]
  exact deningerUntilt_eq_zero_iff (χ f)

/-! ### The bijection of Proposition 14.16 -/

open Classical in
/-- **Deninger, Proposition 14.16 (`t1213n`).**  Homomorphisms of tilts `A♭ → 𝒪♭` correspond
bijectively to the pointed multiplicative maps `A♭ → 𝒪` that are additive modulo `p`, that is, to
Deninger's subspace `Y^⋄`. -/
noncomputable def deningerTiltCharAdditiveEquiv :
    (PreTilt A p →+* PreTilt O p) ≃
      {χ : PreTilt A p →* O //
        ∀ r s : PreTilt A p, χ (r + s) - χ r - χ s ∈ Ideal.span {(p : O)}} where
  toFun χflat :=
    ⟨deningerTiltChar χflat,
      (deningerTiltChar_exists_iff_additiveModP (deningerTiltChar χflat)).1 ⟨χflat, rfl⟩⟩
  invFun χ := ((deningerTiltChar_exists_iff_additiveModP χ.1).2 χ.2).choose
  left_inv χflat := by
    refine deningerTiltChar_injective ?_
    exact ((deningerTiltChar_exists_iff_additiveModP (deningerTiltChar χflat)).2
      ((deningerTiltChar_exists_iff_additiveModP (deningerTiltChar χflat)).1
        ⟨χflat, rfl⟩)).choose_spec
  right_inv χ := by
    refine Subtype.ext ?_
    exact ((deningerTiltChar_exists_iff_additiveModP χ.1).2 χ.2).choose_spec

@[simp] theorem deningerTiltCharAdditiveEquiv_apply (χflat : PreTilt A p →+* PreTilt O p) :
    (deningerTiltCharAdditiveEquiv (A := A) (O := O) χflat : PreTilt A p →* O)
      = deningerTiltChar χflat := rfl

/-- **Deninger, Proposition 14.16 (`t1213n`).**  Under the correspondence the nonvanishing
conditions on the two sides agree. -/
theorem deningerTiltCharAdditiveEquiv_ne_zero [IsReduced O]
    (χflat : PreTilt A p →+* PreTilt O p) (f : PreTilt A p) :
    (deningerTiltCharAdditiveEquiv (A := A) (O := O) χflat).1 f ≠ 0 ↔ χflat f ≠ 0 := by
  rw [deningerTiltCharAdditiveEquiv_apply]
  exact not_congr (deningerTiltChar_eq_zero_iff χflat f)

end RHTower
