import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatProfiniteHaarTransport
import GaloisForLFunctions.RHTower.CCMRationalIntegralFiniteAdeleCyclicHaarAverage
import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatPeriodicWeights

/-!
# Finite Bruhat cyclic Haar packets

A translated finite Bruhat function is pulled back by a full-support positive
denominator.  Its support then lies in integral finite adeles.  An open
translation stabilizer produces a finite cyclic quotient, and normalized Haar
averaging proves that endpoint-integral vanishing forces exact vanishing of
the finite residue-weight sum.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-- Canonical positive-natural rational scaling label. -/
def ccmRationalPositiveNatAdelicScaling
    (D : ℕ) (hD : 0 < D) : CCMRationalAdelicScaling :=
  ⟨ccmRationalNatUnit D (Nat.ne_of_gt hD)⟩

/-- Pull back a right-translated finite Bruhat function by denominator `D`. -/
def ccmRationalFiniteBruhatDenominatorPullback
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (D : ℕ) (hD : 0 < D) : CCMRationalFiniteBruhatSchwartz :=
  ccmRationalFiniteBruhatScaling
    (ccmRationalPositiveNatAdelicScaling D hD)
    (ccmRationalFiniteBruhatMulRight phi b)

@[simp]
theorem ccmRationalFiniteBruhatDenominatorPullback_apply
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (D : ℕ) (hD : 0 < D) (x : CCMRationalFiniteAdele) :
    (ccmRationalFiniteBruhatDenominatorPullback phi b D hD).1 x =
      phi.1
        (algebraMap ℚ CCMRationalFiniteAdele ((D : ℚ)⁻¹) * x * b) := by
  rfl

/-- Pullback values on diagonal integers are exactly denominator-cleared
rational-orbit values. -/
theorem ccmRationalFiniteBruhatDenominatorPullback_diagonal
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (D : ℕ) (hD : 0 < D) (n : ℤ) :
    (ccmRationalFiniteBruhatDenominatorPullback phi b D hD).1
        (ccmRationalIntegralFiniteAdeleDiagonal n).1 =
      phi.1 (algebraMap ℚ CCMRationalFiniteAdele
        ((n : ℚ) / (D : ℚ)) * b) := by
  rw [ccmRationalFiniteBruhatDenominatorPullback_apply]
  change phi.1
      (algebraMap ℚ CCMRationalFiniteAdele ((D : ℚ)⁻¹) *
        algebraMap ℤ CCMRationalFiniteAdele n * b) = _
  rw [show algebraMap ℤ CCMRationalFiniteAdele n =
      algebraMap ℚ CCMRationalFiniteAdele (n : ℚ) by simp]
  rw [← map_mul]
  congr 2
  field_simp

/-- A full-support denominator makes the denominator pullback supported in
integral finite adeles. -/
theorem ccmRationalFiniteBruhatDenominatorPullback_support_subset_integral
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (D : ℕ) (hD : 0 < D)
    (hsupport : ∀ x : CCMRationalFiniteAdele,
      phi.1 (x * b) ≠ 0 →
        algebraMap ℕ CCMRationalFiniteAdele D * x ∈
          ccmRationalIntegralFiniteAdelesAddSubgroup) :
    Function.support
        ((ccmRationalFiniteBruhatDenominatorPullback phi b D hD).1 :
          CCMRationalFiniteAdele → ℂ) ⊆
      ccmRationalIntegralFiniteAdeles := by
  intro x hx
  have hxint := hsupport
    (algebraMap ℚ CCMRationalFiniteAdele ((D : ℚ)⁻¹) * x) (by
      simpa [ccmRationalFiniteBruhatDenominatorPullback_apply] using hx)
  have hDmap : algebraMap ℕ CCMRationalFiniteAdele D =
      algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) := by simp
  have hprod :
      algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) *
        algebraMap ℚ CCMRationalFiniteAdele ((D : ℚ)⁻¹) = 1 := by
    rw [← map_mul]
    simp [ne_of_gt hD]
  rw [hDmap, ← mul_assoc, hprod, one_mul] at hxint
  exact hxint

/-- Exact Haar transport for denominator pullback restricted to integral
finite adeles. -/
theorem ccmRationalFiniteBruhatDenominatorPullback_restrictedIntegral_eq
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (D : ℕ) (hD : 0 < D)
    (hsupport : ∀ x : CCMRationalFiniteAdele,
      phi.1 (x * b.1) ≠ 0 →
        algebraMap ℕ CCMRationalFiniteAdele D * x ∈
          ccmRationalIntegralFiniteAdelesAddSubgroup) :
    (∫ x : ccmRationalIntegralFiniteAdelesAddSubgroup,
      (ccmRationalFiniteBruhatDenominatorPullback phi b.1 D hD).1 x.1
      ∂ccmRationalIntegralFiniteAdelesHaar) =
        (D : ℝ)⁻¹ • ccmRationalFiniteBruhatIntegral phi := by
  let h := ccmRationalFiniteBruhatDenominatorPullback phi b.1 D hD
  have hsupp :=
    ccmRationalFiniteBruhatDenominatorPullback_support_subset_integral
      phi b.1 D hD hsupport
  calc
    (∫ x : ccmRationalIntegralFiniteAdelesAddSubgroup,
        h.1 x.1 ∂ccmRationalIntegralFiniteAdelesHaar) =
        ∫ x in ccmRationalIntegralFiniteAdeles,
          h.1 x ∂ccmRationalFiniteAdeleHaar := by
      exact integral_subtype_comap
        ccmRationalIntegralFiniteAdeles_isOpen.measurableSet h.1
    _ = ∫ x, h.1 x ∂ccmRationalFiniteAdeleHaar :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        by_contra hne
        exact hx (hsupp hne)
    _ = ccmRationalFiniteBruhatIntegral h := rfl
    _ = (D : ℝ)⁻¹ • ccmRationalFiniteBruhatIntegral phi := by
      rw [show h = ccmRationalFiniteBruhatScaling
          (ccmRationalPositiveNatAdelicScaling D hD)
          (ccmRationalFiniteBruhatMulRight phi b.1) by rfl,
        ccmRationalFiniteBruhatIntegral_scaling,
        ccmRationalFiniteBruhatIntegral_mulRight_profinite]
      congr 1
      change |((D : ℚ) : ℝ)|⁻¹ = (D : ℝ)⁻¹
      have hDR : 0 < ((D : ℚ) : ℝ) := by exact_mod_cast hD
      rw [abs_of_pos hDR]
      congr 1

/-- Vanishing corollary of exact restricted Haar transport. -/
theorem ccmRationalFiniteBruhatDenominatorPullback_restrictedIntegral_eq_zero
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (D : ℕ) (hD : 0 < D)
    (hsupport : ∀ x : CCMRationalFiniteAdele,
      phi.1 (x * b.1) ≠ 0 →
        algebraMap ℕ CCMRationalFiniteAdele D * x ∈
          ccmRationalIntegralFiniteAdelesAddSubgroup)
    (hzero : ccmRationalFiniteBruhatIntegral phi = 0) :
    (∫ x : ccmRationalIntegralFiniteAdelesAddSubgroup,
      (ccmRationalFiniteBruhatDenominatorPullback phi b.1 D hD).1 x.1
      ∂ccmRationalIntegralFiniteAdelesHaar) = 0 := by
  rw [ccmRationalFiniteBruhatDenominatorPullback_restrictedIntegral_eq
    phi b D hD hsupport, hzero, smul_zero]

/-- For positive modulus, the canonical equivalence `Fin N ≃ ZMod N`
preserves canonical values. -/
theorem ccmRationalZMod_finEquiv_val :
    ∀ (N : ℕ) [NeZero N] (r : Fin N),
      (ZMod.finEquiv N r).val = r.val
  | 0, h, _ => (h.ne 0 rfl).elim
  | _ + 1, _, _ => rfl

/-- Exact finite-place packet with cyclic residue weights and Haar control. -/
structure CCMRationalFiniteBruhatCyclicHaarPacket
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  period : ℕ
  period_neZero : NeZero period
  weight : Fin period → ℂ
  rationalDenominator : ∀ q : ℚ,
    phi.1 (algebraMap ℚ CCMRationalFiniteAdele q * b.1) ≠ 0 →
      algebraMap ℕ ℚ denominator * q ∈ (algebraMap ℤ ℚ).range
  finiteCoefficient : ∀ n : ℤ,
    phi.1 (algebraMap ℚ CCMRationalFiniteAdele
      ((n : ℚ) / (denominator : ℚ)) * b.1) =
      weight (@ccmRationalPeriodicResidue period period_neZero n)
  weightSum_eq :
    ∑ r, weight r =
      period • ((denominator : ℝ)⁻¹ •
        ccmRationalFiniteBruhatIntegral phi)

/-- Vanishing finite endpoint kills exact packet weight sum. -/
theorem CCMRationalFiniteBruhatCyclicHaarPacket.weightSum_eq_zero
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (P : CCMRationalFiniteBruhatCyclicHaarPacket phi b)
    (hzero : ccmRationalFiniteBruhatIntegral phi = 0) :
    ∑ r, P.weight r = 0 := by
  rw [P.weightSum_eq, hzero, smul_zero, nsmul_zero]

/-- Every finite Bruhat factor over the genuine profinite class-space
coordinate admits a cyclic Haar packet. -/
theorem ccmRationalFiniteBruhat_exists_cyclicHaarPacket
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit) :
    Nonempty (CCMRationalFiniteBruhatCyclicHaarPacket phi b) := by
  obtain ⟨D, hD, hsupport, hrational⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_positiveNatFullDenominator phi b.1
  let h := ccmRationalFiniteBruhatDenominatorPullback phi b.1 D hD
  letI : NonarchimedeanAddGroup CCMRationalFiniteAdele :=
    ccmRationalFiniteAdele_nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ :=
    ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer h
  let W : OpenAddSubgroup ccmRationalIntegralFiniteAdelesAddSubgroup :=
    V.comap ccmRationalIntegralFiniteAdelesAddSubgroup.subtype
      continuous_subtype_val
  let N := Nat.card
    (ccmRationalIntegralFiniteAdelesAddSubgroup ⧸ W.toAddSubgroup)
  have hN : N ≠ 0 :=
    ccmRationalIntegralFiniteAdele_openQuotient_card_ne_zero W
  letI hNZ : NeZero N := ⟨hN⟩
  let ψ : ccmRationalIntegralFiniteAdelesAddSubgroup → ℂ :=
    fun x => h.1 x.1
  have hperiod : ∀ x z : ccmRationalIntegralFiniteAdelesAddSubgroup,
      ψ (x + N • z) = ψ x := by
    intro x z
    have hzW : N • z ∈ W :=
      ccmRationalIntegralFiniteAdele_openQuotient_nsmulRange_le W ⟨z, rfl⟩
    simpa [ψ] using hV x.1 ⟨(N • z).1, hzW⟩
  let F : ℤ → ℂ :=
    fun n => ψ (ccmRationalIntegralFiniteAdeleDiagonal n)
  have hF : Function.Periodic F (N : ℤ) := by
    intro n
    have hp := hperiod (ccmRationalIntegralFiniteAdeleDiagonal n)
      (ccmRationalIntegralFiniteAdeleDiagonal 1)
    have hNm : N • ccmRationalIntegralFiniteAdeleDiagonal 1 =
        ccmRationalIntegralFiniteAdeleDiagonal (N : ℤ) := by
      rw [← map_nsmul]
      simp
    rw [hNm] at hp
    simpa [F, map_add] using hp
  let w : Fin N → ℂ := ccmRationalPeriodicResidueWeight N F
  have hw (n : ℤ) :
      phi.1 (algebraMap ℚ CCMRationalFiniteAdele
        ((n : ℚ) / (D : ℚ)) * b.1) =
        w (ccmRationalPeriodicResidue N n) := by
    rw [← ccmRationalFiniteBruhatDenominatorPullback_diagonal
      phi b.1 D hD n]
    exact ccmRationalPeriodic_eq_residueWeight N F hF n
  refine ⟨⟨D, hD, N, hNZ, w, hrational, hw, ?_⟩⟩
  have hψc : Continuous ψ :=
    h.1.continuous.comp continuous_subtype_val
  letI : IsFiniteMeasure ccmRationalIntegralFiniteAdelesHaar :=
    ⟨by
      rw [ccmRationalIntegralFiniteAdelesHaar_univ]
      exact ENNReal.one_lt_top⟩
  have hψi : Integrable ψ ccmRationalIntegralFiniteAdelesHaar :=
    hψc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace ψ)
  have hclass :
      ∀ {x y : ccmRationalIntegralFiniteAdelesAddSubgroup},
        QuotientAddGroup.mk'
            (nsmulAddMonoidHom
              (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range x =
          QuotientAddGroup.mk'
            (nsmulAddMonoidHom
              (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range y →
        ψ x = ψ y :=
    ccmRationalIntegralFiniteAdele_classInvariant_of_nsmulInvariant
      N ψ hperiod
  have hψintegral :=
    ccmRationalFiniteBruhatDenominatorPullback_restrictedIntegral_eq
      phi b D hD hsupport
  have hsum :=
    ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral
      N ψ hψi hclass
  calc
    ∑ r, w r =
        ∑ r : Fin N,
          ψ (ccmRationalIntegralFiniteAdeleDiagonal
            ((ZMod.finEquiv N r).val : ℤ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [w, ccmRationalPeriodicResidueWeight, F,
        ccmRationalZMod_finEquiv_val]
    _ = ∑ r : ZMod N,
          ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) :=
      (ZMod.finEquiv N).toEquiv.sum_comp
        (fun r : ZMod N =>
          ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)))
    _ = N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := hsum
    _ = N • ((D : ℝ)⁻¹ • ccmRationalFiniteBruhatIntegral phi) := by
      rw [hψintegral]

end RHTower
end GaloisForLFunctions
