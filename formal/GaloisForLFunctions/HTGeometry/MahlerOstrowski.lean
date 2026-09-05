import GaloisForLFunctions.HTGeometry.MahlerPerfectDifferentialBridge
import GaloisForLFunctions.HTGeometry.AutomorphismFamilyOstrowski

/-!
# The Ostrowski criterion in the Mahler model

The Mahler substitution is an automorphism of the ambient field whose invariants are the
constants, it restricts to an automorphism of the two-variable perfect base, and it commutes
exactly with the derivation obtained by dividing the Euler operator by the twisting coordinate.
Hence an additive primitive of a base increment is differentially transcendental over the base as
soon as no nonzero constant-coefficient combination of the increment's jets is a coboundary.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-! ## The substitution is an automorphism of the ambient field -/

theorem embDomain_eq_self_of_apply_eq {Γ R : Type*} [PartialOrder Γ] [Zero R]
    (g : Γ ↪o Γ) (hg : ∀ a, g a = a) (x : HahnSeries Γ R) :
    HahnSeries.embDomain g x = x := by
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  have h := HahnSeries.embDomain_coeff (f := g) (x := x) (a := γ)
  rwa [hg γ] at h

theorem mahlerHom_C (p : ℕ) (hp : 0 < p) (c : k) :
    mahlerHom p hp (HahnSeries.C c : HahnSeries ℚ k) = HahnSeries.C c := by
  show HahnSeries.embDomain _ (HahnSeries.C c : HahnSeries ℚ k) = HahnSeries.C c
  rw [HahnSeries.C_apply, HahnSeries.embDomain_single]
  norm_num

/-- The inverse Mahler substitution on Hahn series: `w^γ ↦ w^(γ/p)`. -/
def mahlerHomInv (p : ℕ) (hp : 0 < p) : HahnSeries ℚ k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom (qShrinkHom p 1) (qShrinkHom_injective hp 1)
    (qShrinkHom_le_iff hp 1)

theorem mahlerHomInv_C (p : ℕ) (hp : 0 < p) (c : k) :
    mahlerHomInv p hp (HahnSeries.C c : HahnSeries ℚ k) = HahnSeries.C c := by
  show HahnSeries.embDomain _ (HahnSeries.C c : HahnSeries ℚ k) = HahnSeries.C c
  rw [HahnSeries.C_apply, HahnSeries.embDomain_single]
  norm_num [qShrinkHom]

theorem mahlerHom_mahlerHomInv (p : ℕ) (hp : 0 < p) (f : HahnSeries ℚ k) :
    mahlerHom p hp (mahlerHomInv p hp f) = f := by
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.ne'
  show HahnSeries.embDomain (⟨⟨qStretchHom p, qStretchHom_injective hp⟩,
      qStretchHom_le_iff hp _ _⟩ : ℚ ↪o ℚ)
      (HahnSeries.embDomain (⟨⟨qShrinkHom p 1, qShrinkHom_injective hp 1⟩,
        qShrinkHom_le_iff hp 1 _ _⟩ : ℚ ↪o ℚ) f) = f
  rw [embDomain_comp]
  refine embDomain_eq_self_of_apply_eq _ (fun γ => ?_) f
  show (p : ℚ) * (((p : ℚ) ^ 1)⁻¹ * γ) = γ
  field_simp

theorem mahlerHomInv_mahlerHom (p : ℕ) (hp : 0 < p) (f : HahnSeries ℚ k) :
    mahlerHomInv p hp (mahlerHom p hp f) = f := by
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.ne'
  show HahnSeries.embDomain (⟨⟨qShrinkHom p 1, qShrinkHom_injective hp 1⟩,
      qShrinkHom_le_iff hp 1 _ _⟩ : ℚ ↪o ℚ)
      (HahnSeries.embDomain (⟨⟨qStretchHom p, qStretchHom_injective hp⟩,
        qStretchHom_le_iff hp _ _⟩ : ℚ ↪o ℚ) f) = f
  rw [embDomain_comp]
  refine embDomain_eq_self_of_apply_eq _ (fun γ => ?_) f
  show ((p : ℚ) ^ 1)⁻¹ * ((p : ℚ) * γ) = γ
  field_simp

theorem C_natCast_ne_zero [CharZero k] {p : ℕ} (hp : 1 < p) :
    (HahnSeries.C ((p : k)) : HahnSeries ℚ k) ≠ 0 := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  intro h
  have := congrArg (fun x : HahnSeries ℚ k => x.coeff 0) h
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
  exact hpk this

/-- The inverse of the Mahler substitution on the ambient field. -/
def mahlerDilationInv [CharZero k] (p : ℕ) (hp : 1 < p) : MahlerAmbient k →+* MahlerAmbient k :=
  hahnTwistHom (mahlerHomInv p (by omega))
    (laurentChar (HahnSeries.C ((p : k)) : HahnSeries ℚ k) (C_natCast_ne_zero hp))

@[simp]
theorem coeff_mahlerDilationInv [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) (n : ℤ) :
    (mahlerDilationInv p hp f).coeff n
      = (HahnSeries.C ((p : k)) : HahnSeries ℚ k) ^ n * mahlerHomInv p (by omega) (f.coeff n) := by
  simp [mahlerDilationInv]

theorem mahlerDilation_mahlerDilationInv [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) :
    mahlerDilation p hp (mahlerDilationInv p hp f) = f := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerDilation, coeff_mahlerDilationInv, map_mul, map_zpow₀, mahlerHom_C,
    mahlerHom_mahlerHomInv, ← mul_assoc, ← mul_zpow, ← map_mul, inv_mul_cancel₀ hpk, map_one,
    one_zpow, one_mul]

theorem mahlerDilationInv_mahlerDilation [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) :
    mahlerDilationInv p hp (mahlerDilation p hp f) = f := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerDilationInv, coeff_mahlerDilation, map_mul, map_zpow₀, mahlerHomInv_mahlerHom,
    mahlerHomInv_C, ← mul_assoc, ← mul_zpow, ← map_mul, mul_inv_cancel₀ hpk, map_one, one_zpow,
    one_mul]

/-- **The Mahler substitution is an automorphism of the ambient field.** -/
def mahlerDilationEquiv [CharZero k] (p : ℕ) (hp : 1 < p) :
    MahlerAmbient k ≃+* MahlerAmbient k :=
  { toFun := mahlerDilation p hp
    invFun := mahlerDilationInv p hp
    left_inv := mahlerDilationInv_mahlerDilation p hp
    right_inv := mahlerDilation_mahlerDilationInv p hp
    map_mul' := map_mul _
    map_add' := map_add _ }

@[simp]
theorem mahlerDilationEquiv_apply [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) :
    mahlerDilationEquiv p hp f = mahlerDilation p hp f := rfl

/-! ## Constants -/

theorem algebraMap_k_mahlerAmbient (c : k) :
    algebraMap k (MahlerAmbient k) c = HahnSeries.C (HahnSeries.C c) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  simp

theorem coeff_C_C (c : k) (n : ℤ) :
    (HahnSeries.C (HahnSeries.C c) : MahlerAmbient k).coeff n
      = if n = 0 then (HahnSeries.C c : HahnSeries ℚ k) else 0 := by
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl, HahnSeries.C_apply, HahnSeries.coeff_single_same]
  · rw [if_neg h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

theorem mahlerDilation_C_C [CharZero k] (p : ℕ) (hp : 1 < p) (c : k) :
    mahlerDilation p hp (HahnSeries.C (HahnSeries.C c) : MahlerAmbient k)
      = HahnSeries.C (HahnSeries.C c) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerDilation, coeff_C_C]
  by_cases h : n = 0
  · rw [if_pos h, h, zpow_zero, one_mul, mahlerHom_C]
  · rw [if_neg h, map_zero, mul_zero]

/-- The perfect base is a `k`-algebra through the constant Hahn series. -/
@[reducible] def perfectAlgebra (p : ℕ) (hp : 1 < p) : Algebra k (perfectBase (k := k) p hp) :=
  (((HahnSeries.C : k →+* HahnSeries ℚ k)).codRestrict (perfectBase p hp)
    (C_mem_perfectBase p hp)).toAlgebra

theorem algebraMap_k_perfectBase (p : ℕ) (hp : 1 < p) (c : k) :
    letI := perfectAlgebra (k := k) p hp
    ((algebraMap k (perfectBase (k := k) p hp) c : perfectBase (k := k) p hp)
      : HahnSeries ℚ k) = HahnSeries.C c := rfl

theorem mahlerPEmbed_algebraMap_const [CharZero k] (p : ℕ) (hp : 1 < p) (c : k) :
    letI := perfectAlgebra (k := k) p hp
    mahlerPEmbed k p hp (algebraMap k (MahlerPBase k p hp) c)
      = HahnSeries.C (HahnSeries.C c) := by
  letI := perfectAlgebra (k := k) p hp
  have htower : algebraMap k (MahlerPBase k p hp) c
      = algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)
        (algebraMap k (perfectBase (k := k) p hp) c) :=
    IsScalarTower.algebraMap_apply k (perfectBase (k := k) p hp) (MahlerPBase k p hp) c
  rw [htower]
  show (hahnMapRingHom ((perfectBase (k := k) p hp).subtype))
      ((algebraMap (RatFunc (perfectBase (k := k) p hp))
        (LaurentSeries (perfectBase (k := k) p hp)))
        (algebraMap (perfectBase (k := k) p hp) (RatFunc (perfectBase (k := k) p hp))
          (algebraMap k (perfectBase (k := k) p hp) c))) = _
  rw [algebraMap_const_laurentSeries]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_hahnMapRingHom, HahnSeries.C_apply]
  by_cases h : n = 0
  · subst h
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
    exact algebraMap_k_perfectBase p hp c
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, map_zero]

/-- The base acts on the ambient field through the Hahn expansion. -/
@[reducible] def mahlerPEmbedAlgebra [CharZero k] (p : ℕ) (hp : 1 < p) :
    Algebra (MahlerPBase k p hp) (MahlerAmbient k) := (mahlerPEmbed k p hp).toAlgebra

/-! ## The criterion -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **The differential Ostrowski criterion in the Mahler model.**  An additive primitive of a base
increment for the substitution `w ↦ w^p`, `h ↦ p⁻¹h` is differentially transcendental over the
two-variable perfect base as soon as no nonzero constant-coefficient combination of the jets of
the increment is a coboundary of the substitution in that base. -/
theorem differentialIndependent_of_mahler_primitive [CharZero k] (p : ℕ) (hp : 1 < p)
    (u : MahlerAmbient k) (bb : MahlerPBase k p hp)
    (hshift : mahlerDilation p hp u = u + mahlerPEmbed k p hp bb)
    (hnot : letI := perfectAlgebra (k := k) p hp
      letI := mahlerPBaseDifferential (k := k) p hp
      ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : MahlerPBase k p hp,
        mahlerPBaseDilation p hp y - y ≠
          Finsupp.linearCombination (MahlerPBase k p hp)
            (fun q : Unit × ℕ => differentialJet q.2 bb)
            (Finsupp.mapRange (algebraMap k (MahlerPBase k p hp)) (map_zero _) c)) :
    letI := perfectAlgebra (k := k) p hp
    letI := mahlerPBaseDifferential (k := k) p hp
    letI := mahlerCommDifferential (k := k)
    letI := mahlerPEmbedAlgebra (k := k) p hp
    DifferentialIndependent (MahlerPBase k p hp) (fun _ : Unit => u) := by
  letI := perfectAlgebra (k := k) p hp
  letI := mahlerPBaseDifferential (k := k) p hp
  letI := mahlerCommDifferential (k := k)
  letI := mahlerPEmbedAlgebra (k := k) p hp
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := MahlerPBase k p hp)
    (A := MahlerAmbient k)
    fun c => by
      rw [algebraMap_k_mahlerAmbient]
      exact (mahlerPEmbed_algebraMap_const p hp c).symm
  haveI : DifferentialAlgebra (MahlerPBase k p hp) (MahlerAmbient k) :=
    ⟨fun x => (mahlerPEmbed_mahlerPBaseDeriv p hp x).symm⟩
  haveI : CharZero (MahlerPBase k p hp) :=
    charZero_of_injective_algebraMap (algebraMap k (MahlerPBase k p hp)).injective
  refine automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (C := k) (K := MahlerPBase k p hp) (L := MahlerAmbient k)
    (fun _ : Unit => mahlerPBaseDilation p hp) (fun _ : Unit => mahlerDilationEquiv p hp)
    (fun _ x => by exact (mahlerPEmbed_mahlerPBaseDilation p hp x).symm)
    (fun _ x => by exact mahlerDilation_mahlerCommDeriv p hp x)
    (fun _ c => ?_) (fun z hz => ?_) (fun _ : Unit => u) (fun _ _ => bb)
    (fun _ _ => by exact hshift) (fun c hc y => ⟨(), hnot c hc y⟩)
  · show mahlerDilation p hp (algebraMap k (MahlerAmbient k) c) = _
    rw [algebraMap_k_mahlerAmbient, mahlerDilation_C_C]
  · obtain ⟨c, hc⟩ := exists_C_C_of_mahlerDilation_eq_self hp (hz ())
    exact ⟨c, by rw [hc, algebraMap_k_mahlerAmbient]⟩

end

end GaloisForLFunctions.HTGeometry
