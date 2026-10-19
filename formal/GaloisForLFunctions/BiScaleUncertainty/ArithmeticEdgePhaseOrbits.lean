import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgePhaseFibre

/-!
# Translation orbits of the arithmetic edge phase code

The constant code line is exactly literal translation of the realized sieve signals. On nonempty
support the quotient has cardinality two to the code nullity minus one. Maximal allowed rank is
exactly constant-sign recovery; every deficient rank supplies an actual nontranslation witness.
-/

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
open GaloisForLFunctions.BezoutValuationIncidence

namespace BinaryPhase

theorem neg_eq (x : ZMod 2) : -x=x := by
  calc
    -x = -x+(x+x) := by rw [add_self,add_zero]
    _ = x := by rw [← add_assoc,neg_add_cancel,zero_add]

theorem sign_eq_signed_iff (x y ε : ZMod 2) :
    sign x = sign ε * sign y ↔ x+y=ε := by
  constructor
  · intro h
    apply sign_injective
    rw [sign_add,h,mul_assoc,← pow_two,sign_sq,mul_one]
  · intro h
    have hh : sign x * sign y = sign ε := by rw [← sign_add,h]
    calc
      sign x = (sign x*sign y)*sign y := by
        rw [mul_assoc,← pow_two,sign_sq,mul_one]
      _ = sign ε * sign y := by rw [hh]

end BinaryPhase

namespace Blocks
variable {V : Type*} [Fintype V] (D : Blocks V)

theorem profiles_twist_signed_iff (a : ℕ → ℝ) (x y : D.Phase a) (ε : ZMod 2) :
    (∀ q, D.profile (D.twist a x) q = BinaryPhase.sign ε * D.profile (D.twist a y) q) ↔
      ∀ q, x q+y q=ε := by
  constructor
  · intro h q
    apply (BinaryPhase.sign_eq_signed_iff _ _ _).mp
    apply mul_right_cancel₀ ((D.mem_active_iff a q.val).mp q.property)
    simpa only [D.profile_twist,twist,D.phaseEval_mem a x q.val q.property,
      D.phaseEval_mem a y q.val q.property,mul_assoc] using h q.val
  · intro h q
    by_cases hq : q ∈ D.active a
    · have hh : BinaryPhase.sign (D.phaseEval a q x) =
          BinaryPhase.sign ε * BinaryPhase.sign (D.phaseEval a q y) := by
        rw [D.phaseEval_mem a x q hq,D.phaseEval_mem a y q hq]
        exact (BinaryPhase.sign_eq_signed_iff _ _ _).mpr (h ⟨q,hq⟩)
      simp only [D.profile_twist,twist,hh,mul_assoc]
    · have ha : D.profile a q = 0 := by
        by_contra hn
        exact hq ((D.mem_active_iff a q).mpr hn)
      simp only [D.profile_twist,twist,ha,mul_zero]

theorem commonSign_twists_iff (a : ℕ → ℝ) (x y : D.Phase a) :
    D.CommonSign (D.twist a x) (D.twist a y) ↔ ∃ ε, ∀ q, x q+y q=ε := by
  constructor
  · rintro (h | h)
    · refine ⟨0,(D.profiles_twist_signed_iff a x y 0).mp ?_⟩
      simpa only [BinaryPhase.sign_zero,one_mul] using h
    · refine ⟨1,(D.profiles_twist_signed_iff a x y 1).mp ?_⟩
      simpa only [BinaryPhase.sign_one,neg_one_mul] using h
  · rintro ⟨ε,h⟩
    rcases BinaryPhase.eq_zero_or_one ε with rfl | rfl
    · left
      simpa only [BinaryPhase.sign_zero,one_mul] using
        (D.profiles_twist_signed_iff a x y 0).mpr h
    · right
      simpa only [BinaryPhase.sign_one,neg_one_mul] using
        (D.profiles_twist_signed_iff a x y 1).mpr h

theorem commonSign_twist_iff (a : ℕ → ℝ) (x : D.Phase a) :
    D.CommonSign a (D.twist a x) ↔ ∃ ε, ∀ q, x q=ε := by
  have hz (q : ℕ) : D.profile (D.twist a 0) q = D.profile a q := by
    simp only [D.profile_twist,twist,map_zero,BinaryPhase.sign_zero,one_mul]
  simpa only [CommonSign,hz,Pi.zero_apply,zero_add] using
    D.commonSign_twists_iff a 0 x

/-- The all-one code vector is the actual product-block translation. -/
def codeOne (a : ℕ → ℝ) : LinearMap.ker (D.phaseMap a) :=
  ⟨fun _ => 1,D.const_mem_phase_kernel a 1⟩

def commonCode (a : ℕ → ℝ) : Submodule (ZMod 2) (LinearMap.ker (D.phaseMap a)) :=
  Submodule.span (ZMod 2) {D.codeOne a}

theorem mem_commonCode (a : ℕ → ℝ) (x : LinearMap.ker (D.phaseMap a)) :
    x ∈ D.commonCode a ↔ ∃ ε, ∀ q, x.val q=ε := by
  rw [commonCode,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨ε,h⟩
    refine ⟨ε,fun q => ?_⟩
    have hh := congrArg (fun z : LinearMap.ker (D.phaseMap a) => z.val q) h
    change ε*1=x.val q at hh
    simpa only [mul_one] using hh.symm
  · rintro ⟨ε,h⟩
    refine ⟨ε,?_⟩
    apply Subtype.ext
    funext q
    change ε*1=x.val q
    simpa only [mul_one] using (h q).symm

theorem codeOne_ne_zero (a : ℕ → ℝ) (ha : (D.active a).Nonempty) : D.codeOne a ≠ 0 := by
  obtain ⟨q,hq⟩ := ha
  intro h
  have hh := congrArg (fun z : LinearMap.ker (D.phaseMap a) => z.val ⟨q,hq⟩) h
  change (1 : ZMod 2)=0 at hh
  exact one_ne_zero hh

theorem finrank_commonCode (a : ℕ → ℝ) (ha : (D.active a).Nonempty) :
    Module.finrank (ZMod 2) (D.commonCode a) = 1 := by
  unfold commonCode
  exact finrank_span_singleton (D.codeOne_ne_zero a ha)

/-- Code classes modulo the actual common-sign translation. -/
abbrev PhaseOrbits (a : ℕ → ℝ) := LinearMap.ker (D.phaseMap a) ⧸ D.commonCode a

/-- Equality of code classes is exactly literal translation of their actual sieve signals. -/
theorem phase_orbit_eq_iff_translate (n : ℕ) (a : ℕ → ℝ)
    (x y : LinearMap.ker (D.phaseMap a)) :
    (Submodule.Quotient.mk x : D.PhaseOrbits a) = Submodule.Quotient.mk y ↔
      ∃ t, ∀ k, sieveSeq (D.cutoff n) (D.weights n (D.twist a y.val)) k =
        sieveSeq (D.cutoff n) (D.weights n (D.twist a x.val)) (k+t) := by
  rw [D.translation_iff_common,D.commonSign_twists_iff]
  rw [Submodule.Quotient.eq,D.mem_commonCode]
  change (∃ ε, ∀ q, x.val q-y.val q=ε) ↔ ∃ ε, ∀ q, x.val q+y.val q=ε
  simp only [sub_eq_add_neg,BinaryPhase.neg_eq]

/-- Number of actual translation classes in the fourth-data fibre on nonempty support. -/
theorem phase_orbit_card (a : ℕ → ℝ) (ha : (D.active a).Nonempty) :
    Nat.card (D.PhaseOrbits a) = 2^((D.active a).card-D.phaseRank a-1) := by
  have hk := D.phase_rank_nullity a
  have hc := D.finrank_commonCode a ha
  have hq := (D.commonCode a).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (D.PhaseOrbits a) +
    Module.finrank (ZMod 2) (D.commonCode a) =
      Module.finrank (ZMod 2) (LinearMap.ker (D.phaseMap a)) at hq
  have hd : Module.finrank (ZMod 2) (D.PhaseOrbits a) =
      (D.active a).card-D.phaseRank a-1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hd,Nat.card_eq_fintype_card,ZMod.card]

theorem commonCode_top_iff_rank (a : ℕ → ℝ) (ha : (D.active a).Nonempty) :
    D.commonCode a = ⊤ ↔ D.phaseRank a = (D.active a).card-1 := by
  have hp := Finset.card_pos.mpr ha
  have hk := D.phase_rank_nullity a
  have hc := D.finrank_commonCode a ha
  constructor
  · intro h
    rw [h] at hc
    simp only [finrank_top] at hc
    omega
  · intro h
    have hd : Module.finrank (ZMod 2) (LinearMap.ker (D.phaseMap a)) = 1 := by omega
    apply Submodule.eq_of_le_of_finrank_eq le_top
    simpa only [finrank_top,hd] using hc

theorem every_code_constant_iff_rank (a : ℕ → ℝ) (ha : (D.active a).Nonempty) :
    (∀ x : LinearMap.ker (D.phaseMap a), ∃ ε, ∀ q, x.val q=ε) ↔
      D.phaseRank a = (D.active a).card-1 := by
  rw [← D.commonCode_top_iff_rank a ha]
  constructor
  · intro h
    apply le_antisymm le_top
    intro x _
    exact (D.mem_commonCode a x).mpr (h x)
  · intro h x
    apply (D.mem_commonCode a x).mp
    rw [h]
    exact Submodule.mem_top

/-- Rank deficiency constructs an actual indistinguishable signal outside the translation orbit. -/
theorem exists_fourth_nontranslate_of_rank (n : ℕ) (a : ℕ → ℝ)
    (ha : (D.active a).Nonempty) (hr : D.phaseRank a ≠ (D.active a).card-1) :
    ∃ b : ℕ → ℝ,
      (∀ v : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
        translatedMoment (D.cutoff n) (D.weights n b) v) ∧
      ¬ ∃ t, ∀ k, sieveSeq (D.cutoff n) (D.weights n b) k =
        sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  classical
  have hn : ¬ ∀ x : LinearMap.ker (D.phaseMap a), ∃ ε, ∀ q, x.val q=ε := by
    intro h
    exact hr ((D.every_code_constant_iff_rank a ha).mp h)
  obtain ⟨x,hx⟩ := not_forall.mp hn
  refine ⟨D.twist a x.val,(D.fourth_twist_iff_kernel n a x.val).mpr x.property,?_⟩
  intro ht
  exact hx ((D.commonSign_twist_iff a x.val).mp ((D.translation_iff_common n a _).mp ht))

end Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
