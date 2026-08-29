import GaloisForLFunctions.HTGeometry.QDifferenceEulerCompat
import GaloisForLFunctions.HTGeometry.AutomorphismFamilyOstrowski

/-!
# The differential Ostrowski criterion in the two-variable Laurent model

The two-variable Laurent field `k((z))((h))` supplies every structural hypothesis of the
arbitrary-family Ostrowski criterion for the dilation `z ↦ b z`, `h ↦ a⁻¹ h`: the base field
`k(z)(h)` embeds in it, the dilation restricts to the base, the derivation commutes with the
dilation, and — when the multipliers are multiplicatively independent — the invariants are exactly
the constants.  What remains for a concrete equation is only the shift identity and the absence of
a telescoper.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem qDilation_qDilation_inv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) :
    qDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb) (qDilation a b ha hb f) = f := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  rw [coeff_coeff_qDilation, coeff_coeff_qDilation, inv_zpow, inv_zpow, ← zpow_neg, ← zpow_neg,
    neg_neg,
    show a ^ n * (b ^ (-m) * (a ^ (-n) * (b ^ m * (f.coeff n).coeff m)))
      = (a ^ n * a ^ (-n)) * (b ^ (-m) * b ^ m) * (f.coeff n).coeff m from by ring,
    ← zpow_add₀ ha, ← zpow_add₀ hb, add_neg_cancel, neg_add_cancel, zpow_zero, zpow_zero,
    one_mul, one_mul]

theorem qDilation_inv_qDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) :
    qDilation a b ha hb (qDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb) f) = f := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  rw [coeff_coeff_qDilation, coeff_coeff_qDilation, inv_zpow, inv_zpow, ← zpow_neg, ← zpow_neg,
    neg_neg,
    show a ^ (-n) * (b ^ m * (a ^ n * (b ^ (-m) * (f.coeff n).coeff m)))
      = (a ^ (-n) * a ^ n) * (b ^ m * b ^ (-m)) * (f.coeff n).coeff m from by ring,
    ← zpow_add₀ ha, ← zpow_add₀ hb, neg_add_cancel, add_neg_cancel, zpow_zero, zpow_zero,
    one_mul, one_mul]

/-- The dilation of the ambient field as an automorphism. -/
def qDilationEquiv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : QLaurent k ≃+* QLaurent k where
  toFun := qDilation a b ha hb
  invFun := qDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb)
  left_inv f := qDilation_qDilation_inv a b ha hb f
  right_inv f := qDilation_inv_qDilation a b ha hb f
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem qDilationEquiv_apply (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) :
    qDilationEquiv a b ha hb f = qDilation a b ha hb f := rfl

theorem qBaseDilation_qBaseDilation_inv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (x : QBase k) :
    qBaseDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb) (qBaseDilation a b ha hb x) = x := by
  refine (qEmbed k).injective ?_
  rw [qEmbed_qBaseDilation, qEmbed_qBaseDilation, qDilation_qDilation_inv]

theorem qBaseDilation_inv_qBaseDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (x : QBase k) :
    qBaseDilation a b ha hb (qBaseDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb) x) = x := by
  refine (qEmbed k).injective ?_
  rw [qEmbed_qBaseDilation, qEmbed_qBaseDilation, qDilation_inv_qDilation]

/-- The dilation of the base field as an automorphism. -/
def qBaseDilationEquiv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : QBase k ≃+* QBase k where
  toFun := qBaseDilation a b ha hb
  invFun := qBaseDilation a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb)
  left_inv x := qBaseDilation_qBaseDilation_inv a b ha hb x
  right_inv x := qBaseDilation_inv_qBaseDilation a b ha hb x
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem qBaseDilationEquiv_apply (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (x : QBase k) :
    qBaseDilationEquiv a b ha hb x = qBaseDilation a b ha hb x := rfl

theorem qEmbed_algebraMap_const (c : k) :
    qEmbed k (algebraMap k (QBase k) c) = HahnSeries.C (HahnSeries.C c) := by
  have htower : algebraMap k (QBase k) c
      = algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) c) :=
    IsScalarTower.algebraMap_apply k (RatFunc k) (QBase k) c
  rw [htower, qEmbed_algebraMap_coeff, algebraMap_const_laurentSeries, HahnSeries.C_apply,
    ← HahnSeries.C_apply, ← HahnSeries.C_apply]

/-- The differential structure of the base field with `δ z = z` and `δ h = s h`. -/
@[reducible] def qBaseDifferential (s : k) : Differential (QBase k) :=
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  twoCylinderDifferential (algebraMap k (RatFunc k) s)

/-- The base field acts on the ambient field through the Laurent expansion. -/
@[reducible] def qEmbedAlgebra : Algebra (QBase k) (QLaurent k) := (qEmbed k).toAlgebra

theorem smul_qLaurent (x : k) (w : QLaurent k) :
    x • w = (HahnSeries.C (HahnSeries.C x) : QLaurent k) * w := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  rw [HahnSeries.coeff_smul, coeff_C_mul_hahn, HahnSeries.coeff_smul, coeff_C_mul_hahn,
    smul_eq_mul]

theorem algebraMap_k_qLaurent (c : k) :
    algebraMap k (QLaurent k) c = HahnSeries.C (HahnSeries.C c) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  simp

set_option maxHeartbeats 4000000 in
/-- **The differential Ostrowski criterion in the two-variable Laurent model.**  An additive
primitive of a base increment for the dilation `z ↦ b z`, `h ↦ a⁻¹ h` is differentially
transcendental over `k(z)(h)` as soon as no nonzero constant-coefficient differential character of
the increment is a dilation coboundary in the base.  The multiplicative independence of the
multipliers is what makes the invariants of the ambient field the constants. -/
theorem differentialIndependent_of_qDifference_primitive [CharZero k]
    (a b s : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0)
    (u : QLaurent k) (bb : QBase k)
    (hshift : qDilation a b ha hb u = u + qEmbed k bb)
    (hnot : letI := qBaseDifferential s
      ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : QBase k,
        qBaseDilation a b ha hb y - y ≠
          Finsupp.linearCombination (QBase k)
            (fun p : Unit × ℕ => differentialJet p.2 bb)
            (Finsupp.mapRange (algebraMap k (QBase k)) (map_zero _) c)) :
    letI := qBaseDifferential s
    letI := qDifferential s
    letI := qEmbedAlgebra (k := k)
    DifferentialIndependent (QBase k) (fun _ : Unit => u) := by
  letI := qBaseDifferential s
  letI := qDifferential s
  letI := qEmbedAlgebra (k := k)
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := QBase k) (A := QLaurent k)
    fun c => by rw [algebraMap_k_qLaurent]; exact (qEmbed_algebraMap_const c).symm
  haveI : DifferentialAlgebra (QBase k) (QLaurent k) :=
    ⟨fun x => (qEmbed_twoCylDerivation s x).symm⟩
  refine automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (C := k) (K := QBase k) (L := QLaurent k)
    (fun _ : Unit => qBaseDilationEquiv a b ha hb) (fun _ : Unit => qDilationEquiv a b ha hb)
    (fun _ x => by exact (qEmbed_qBaseDilation a b ha hb x).symm)
    (fun _ x => by exact qDilation_qDerivation a b s ha hb x)
    (fun _ c => ?_) (fun z hz => ?_) (fun _ : Unit => u) (fun _ _ => bb) (fun _ _ => by exact hshift)
    (fun c hc y => ?_)
  · show qDilation a b ha hb (algebraMap k (QLaurent k) c) = _
    rw [algebraMap_k_qLaurent, qDilation_C_C]
  · obtain ⟨c, hc⟩ := exists_C_C_of_qDilation_eq_self a b ha hb hind (hz ())
    exact ⟨c, by rw [hc, algebraMap_k_qLaurent]⟩
  · exact ⟨(), hnot c hc y⟩

end

end GaloisForLFunctions.HTGeometry
