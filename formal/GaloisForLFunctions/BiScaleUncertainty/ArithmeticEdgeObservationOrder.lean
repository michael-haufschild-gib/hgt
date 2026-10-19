import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgePhaseOrbits
import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeObservationHierarchy

/-! Sharp translated observation degree for arbitrary arithmetic edge profiles. -/

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges.Blocks
open GaloisForLFunctions.BezoutValuationIncidence
open AffineSieve
variable {V : Type*} [Fintype V] (D : Blocks V)

theorem phase_constant_of_small (a : ℕ → ℝ) (ha : (D.active a).card ≤ 1) (x : D.Phase a) :
    ∃ ε, ∀ q, x q=ε := by
  classical
  by_cases hn : (D.active a).Nonempty
  · obtain ⟨q,hq⟩ := hn
    refine ⟨x ⟨q,hq⟩,fun r => ?_⟩
    have he : r = ⟨q,hq⟩ := Subtype.ext ((Finset.card_le_one_iff.mp ha) r.property hq)
    rw [he]
  · refine ⟨0,fun q => ?_⟩
    exact False.elim (hn ⟨q.val,q.property⟩)

theorem recover_small (n : ℕ) (a e : ℕ → ℝ) (ha : (D.active a).card ≤ 1)
    (hf : ∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t = affineMoment (D.cutoff n) e s t) :
    ∃ t, ∀ k, sieveSeq (D.cutoff n) e k = sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  obtain ⟨b,hb⟩ := D.affine_partner_realization n a e hf
  have hq := (D.affine_iff_quadratic n a e).mp hf
  have hqb (h : Fin 2 → ℕ) : translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h := by
    simpa only [translatedMoment,hb] using hq h
  have hs (q : ℕ) : (D.profile a q)^2 = (D.profile b q)^2 := by
    simpa only [D.coordinate_weights] using
      (quadratic_moments_iff_coordinate_squares (D.cutoff n) (D.weights n a) (D.weights n b)).mp hqb q
  have hc := (D.commonSign_twist_iff a (D.phaseBetween a b)).mpr
    (D.phase_constant_of_small a ha (D.phaseBetween a b))
  have hab : D.CommonSign a b := by
    simpa only [CommonSign,D.profile_twist_phaseBetween a b hs] using hc
  obtain ⟨t,ht⟩ := (D.translation_iff_common n a b).mpr hab
  exact ⟨t,fun k => (hb k).trans (ht k)⟩

theorem recover_fourth_of_rank (n : ℕ) (a e : ℕ → ℝ)
    (ha : (D.active a).Nonempty) (hr : D.phaseRank a = (D.active a).card-1)
    (h4 : ∀ h : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) e h) :
    ∃ t, ∀ k, sieveSeq (D.cutoff n) e k = sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  let s : D.FourthSignalFibre n a := ⟨sieveSeq (D.cutoff n) e,⟨e,rfl,h4⟩⟩
  obtain ⟨x,hx⟩ := D.phaseToFourthSignal_surjective n a s
  have hc := (D.every_code_constant_iff_rank a ha).mpr hr x
  obtain ⟨t,ht⟩ := (D.translation_iff_common n a (D.twist a x.val)).mpr
    ((D.commonSign_twist_iff a x.val).mpr hc)
  refine ⟨t,fun k => ?_⟩
  have hh := congrArg (fun z : D.FourthSignalFibre n a => z.val k) hx
  exact hh.symm.trans (ht k)

theorem recover_sixth (n : ℕ) (a e : ℕ → ℝ)
    (hf : ∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t = affineMoment (D.cutoff n) e s t)
    (h6 : ∀ h : Fin 6 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) e h) :
    ∃ t, ∀ k, sieveSeq (D.cutoff n) e k = sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  obtain ⟨b,hb⟩ := D.affine_partner_realization n a e hf
  have h6b (h : Fin 6 → ℕ) : translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n b) h := by
    simpa only [translatedMoment,hb] using h6 h
  obtain ⟨t,ht⟩ := (D.translation_iff_common n a b).mpr ((D.sixth_iff_common n a b).mp h6b)
  exact ⟨t,fun k => (hb k).trans (ht k)⟩

/-- Two active orders always admit an actual nontranslation witness through degree three. -/
theorem exists_through_three_nontranslate (n : ℕ) (a : ℕ → ℝ) (ha : 2 ≤ (D.active a).card) :
    ∃ b : ℕ → ℝ,
      (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t =
        affineMoment (D.cutoff n) (D.weights n b) s t) ∧
      MomentsThrough (D.cutoff n) 3 (D.weights n a) (D.weights n b) ∧
      ¬ ∃ t, ∀ k, sieveSeq (D.cutoff n) (D.weights n b) k =
        sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  classical
  obtain ⟨p,q,hp,hq,hne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (D.active a).card)
  let x : D.Phase a := fun r => if r.val=p then 1 else 0
  have hx : ¬ ∃ ε, ∀ r, x r=ε := by
    rintro ⟨ε,h⟩
    have h1 : (1 : ZMod 2)=ε := by simpa only [x,if_pos rfl] using h ⟨p,hp⟩
    have h0 : (0 : ZMod 2)=ε := by simpa only [x,if_neg (Ne.symm hne)] using h ⟨q,hq⟩
    exact one_ne_zero (h1.trans h0.symm)
  have hs (r : ℕ) : (D.profile a r)^2 = (D.profile (D.twist a x) r)^2 := by
    rw [D.profile_twist]
    exact (D.twist_square a x r).symm
  have hm := D.through_three_of_profile_squares n a (D.twist a x) hs
  refine ⟨D.twist a x,(D.affine_iff_quadratic n a _).mpr (hm 2 (by decide)),hm,?_⟩
  intro ht
  exact hx ((D.commonSign_twist_iff a x).mp ((D.translation_iff_common n a _).mp ht))

/-- Recovery against arbitrary real sieve competitors with all affine data supplied. -/
def RecoveryDegree (n : ℕ) (a : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ e : ℕ → ℝ,
    (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t = affineMoment (D.cutoff n) e s t) →
    MomentsThrough (D.cutoff n) m (D.weights n a) e →
      ∃ t, ∀ k, sieveSeq (D.cutoff n) e k = sieveSeq (D.cutoff n) (D.weights n a) (k+t)

/-- The sharp additional translated degrees are zero, four or six according to support and code rank. -/
theorem recoveryDegree_iff (n : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    D.RecoveryDegree n a m ↔
      (D.active a).card ≤ 1 ∨
        (4 ≤ m ∧ D.phaseRank a = (D.active a).card-1) ∨ 6 ≤ m := by
  constructor
  · intro h
    by_cases hs : (D.active a).card ≤ 1
    · exact Or.inl hs
    by_cases h6 : 6 ≤ m
    · exact Or.inr (Or.inr h6)
    have hm5 : m ≤ 5 := by omega
    have hc : 2 ≤ (D.active a).card := by omega
    have h4 : 4 ≤ m := by
      by_contra hn
      obtain ⟨b,hf,hm,ht⟩ := D.exists_through_three_nontranslate n a hc
      exact ht (h (D.weights n b) hf (momentsThrough_mono hm (by omega)))
    have hr : D.phaseRank a = (D.active a).card-1 := by
      by_contra hn
      have ha : (D.active a).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨b,hb,ht⟩ := D.exists_fourth_nontranslate_of_rank n a ha hn
      exact ht (h (D.weights n b) (D.affine_of_fourth n a _ hb)
        (momentsThrough_mono (D.through_five_of_fourth n a _ hb) hm5))
    exact Or.inr (Or.inl ⟨h4,hr⟩)
  · rintro (hs | ⟨h4,hr⟩ | h6) e hf hm
    · exact D.recover_small n a e hs hf
    · by_cases hs : (D.active a).card ≤ 1
      · exact D.recover_small n a e hs hf
      · have ha : (D.active a).Nonempty := Finset.card_pos.mp (by omega)
        exact D.recover_fourth_of_rank n a e ha hr (hm 4 h4)
    · exact D.recover_sixth n a e hf (hm 6 h6)

/-- Recovery from translated moments alone, against arbitrary real sieve competitors. -/
def MomentRecoveryDegree (n : ℕ) (a : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ e : ℕ → ℝ, MomentsThrough (D.cutoff n) m (D.weights n a) e →
    ∃ t, ∀ k, sieveSeq (D.cutoff n) e k = sieveSeq (D.cutoff n) (D.weights n a) (k+t)

/-- Without affine data the sharp degrees are two, four or six, including the zero signal. -/
theorem momentRecoveryDegree_iff (n : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    D.MomentRecoveryDegree n a m ↔
      2 ≤ m ∧ ((D.active a).card ≤ 1 ∨
        (4 ≤ m ∧ D.phaseRank a = (D.active a).card-1) ∨ 6 ≤ m) := by
  constructor
  · intro h
    have h2 : 2 ≤ m := by
      by_contra hn
      exact D.orderTwo_not_translate n a (h (orderTwoWeight (D.cutoff n))
        (momentsThrough_mono (D.orderTwo_through_one n a) (by omega)))
    refine ⟨h2,(D.recoveryDegree_iff n a m).mp ?_⟩
    intro e _ he
    exact h e he
  · rintro ⟨h2,h⟩ e he
    exact (D.recoveryDegree_iff n a m).mpr h e
      ((D.affine_iff_quadratic n a e).mpr (he 2 h2)) he

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges.Blocks
