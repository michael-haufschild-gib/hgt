import GaloisForLFunctions.HTGeometry.UpperEndFilter
import GaloisForLFunctions.Bottcher.AnalyticDomain
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The meromorphic field at the complex upper end

No single upper half-plane is stable under every complex translation.  The upper-end filter repairs
this geometric defect: a representative is allowed to be analytic above some height depending on
the representative, and two representatives agree when they agree above some further height.

The resulting analytic germs form an integral domain.  The proof is the identity theorem on one
common sufficiently high half-plane.  Its fraction field is therefore a genuine meromorphic field,
and every complex translation acts on it by a field automorphism.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

/-- Raising the lower boundary shrinks an upper half-plane. -/
theorem upperTail_mono {H K : ℝ} (h : H ≤ K) : upperTail K ⊆ upperTail H := by
  intro z hz
  simp only [upperTail, mem_setOf_eq] at hz ⊢
  exact lt_of_le_of_lt h hz

/-- Upper-end germs admitting a representative analytic on some sufficiently high half-plane. -/
def upperEndAnalyticSubring : Subring (Germ upperEndFilter ℂ) where
  carrier := {g | ∃ (f : ℂ → ℂ) (H : ℝ),
    AnalyticOnNhd ℂ f (upperTail H) ∧ (Germ.coeRingHom upperEndFilter f) = g}
  mul_mem' := by
    rintro a b ⟨f, H, hf, rfl⟩ ⟨g, K, hg, rfl⟩
    let L := max H K
    refine ⟨f * g, L, ?_, by rw [map_mul]⟩
    exact (hf.mono (upperTail_mono (le_max_left H K))).mul
      (hg.mono (upperTail_mono (le_max_right H K)))
  one_mem' := ⟨1, 0, analyticOnNhd_const, map_one _⟩
  add_mem' := by
    rintro a b ⟨f, H, hf, rfl⟩ ⟨g, K, hg, rfl⟩
    let L := max H K
    refine ⟨f + g, L, ?_, by rw [map_add]⟩
    exact (hf.mono (upperTail_mono (le_max_left H K))).add
      (hg.mono (upperTail_mono (le_max_right H K)))
  zero_mem' := ⟨0, 0, analyticOnNhd_const, map_zero _⟩
  neg_mem' := by
    rintro a ⟨f, H, hf, rfl⟩
    exact ⟨-f, H, hf.neg, by rw [map_neg]⟩

/-- **Upper-end identity law.** Eventual analytic germs form an integral domain.

If a product is eventually zero, choose one upper half-plane lying above both analyticity heights
and the equality height.  The ordinary identity theorem on that connected half-plane forces one
factor to vanish there, hence to be the zero upper-end germ. -/
theorem isDomain_upperEndAnalyticSubring : IsDomain upperEndAnalyticSubring := by
  haveI hnt : Nontrivial upperEndAnalyticSubring := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hv := congrArg (Subtype.val) h
    rw [ZeroMemClass.coe_zero, OneMemClass.coe_one] at hv
    exact zero_ne_one hv
  haveI hnzd : NoZeroDivisors upperEndAnalyticSubring := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, H, hf, hfa⟩ := a.2
    obtain ⟨g, K, hg, hgb⟩ := b.2
    have hval : (a : Germ upperEndFilter ℂ) * (b : Germ upperEndFilter ℂ) = 0 := by
      have h2 := congrArg (Subtype.val) hab
      rwa [MulMemClass.coe_mul, ZeroMemClass.coe_zero] at h2
    have hfa' : (a : Germ upperEndFilter ℂ) = (↑f : Germ upperEndFilter ℂ) := hfa.symm
    have hgb' : (b : Germ upperEndFilter ℂ) = (↑g : Germ upperEndFilter ℂ) := hgb.symm
    rw [hfa', hgb', ← Germ.coe_mul, ← Germ.coe_zero, Germ.coe_eq] at hval
    change ∀ᶠ z in upperEndFilter, f z * g z = 0 at hval
    rw [upperEndFilter_basis.eventually_iff] at hval
    obtain ⟨L, -, hL⟩ := hval
    let M := max H (max K L)
    have hMH : H ≤ M := le_max_left _ _
    have hMK : K ≤ M := le_trans (le_max_left K L) (le_max_right H (max K L))
    have hML : L ≤ M := le_trans (le_max_right K L) (le_max_right H (max K L))
    have heq : EqOn (fun x => f x * g x) 0 (upperTail M) := by
      intro z hz
      exact hL (upperTail_mono hML hz)
    rcases Bottcher.analyticOnNhd_domain
        (hf.mono (upperTail_mono hMH)) (hg.mono (upperTail_mono hMK))
        (upperTail_isPreconnected M) (upperTail_isOpen M) heq with h0 | h0
    · left
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hfa', ← Germ.coe_zero, Germ.coe_eq]
      change ∀ᶠ z in upperEndFilter, f z = 0
      rw [upperEndFilter_basis.eventually_iff]
      exact ⟨M, trivial, h0⟩
    · right
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, hgb', ← Germ.coe_zero, Germ.coe_eq]
      change ∀ᶠ z in upperEndFilter, g z = 0
      rw [upperEndFilter_basis.eventually_iff]
      exact ⟨M, trivial, h0⟩
  exact NoZeroDivisors.to_isDomain _

/-- The field of meromorphic germs at the complex upper end. -/
abbrev upperEndMeroField : Type := FractionRing upperEndAnalyticSubring

/-- The upper-end meromorphic carrier is a field. -/
theorem upperEndMeroField_hasField : Nonempty (Field upperEndMeroField) :=
  letI := isDomain_upperEndAnalyticSubring
  ⟨inferInstance⟩

/-- Complex translation preserves eventual analyticity, with the exact height change
`H ↦ H - Im h`. -/
theorem upperEndTranslateGerm_mem (h : ℂ) {a : Germ upperEndFilter ℂ}
    (ha : a ∈ upperEndAnalyticSubring) :
    upperEndTranslateGerm h a ∈ upperEndAnalyticSubring := by
  obtain ⟨f, H, hf, hfa⟩ := ha
  refine ⟨fun z ↦ f (z + h), H - h.im, ?_, ?_⟩
  · exact hf.comp (analyticOnNhd_id.add analyticOnNhd_const) (by
      intro z hz
      simp only [upperTail, mem_setOf_eq, Complex.add_im] at hz ⊢
      linarith)
  · rw [← hfa]
    exact (upperEndTranslateGerm_coe h f).symm

/-- Every complex translation restricts to an automorphism of the upper-end analytic domain. -/
noncomputable def upperEndTranslationAnalyticEquiv (h : ℂ) :
    upperEndAnalyticSubring ≃+* upperEndAnalyticSubring where
  toFun a := ⟨upperEndTranslateGerm h a, upperEndTranslateGerm_mem h a.2⟩
  invFun a := ⟨upperEndTranslateGerm (-h) a, upperEndTranslateGerm_mem (-h) a.2⟩
  left_inv a := by
    apply Subtype.ext
    change upperEndTranslateGerm (-h) (upperEndTranslateGerm h
      (a : Germ upperEndFilter ℂ)) = a
    rw [upperEndTranslateGerm_add, neg_add_cancel, upperEndTranslateGerm_zero]
  right_inv a := by
    apply Subtype.ext
    change upperEndTranslateGerm h (upperEndTranslateGerm (-h)
      (a : Germ upperEndFilter ℂ)) = a
    rw [upperEndTranslateGerm_add, add_neg_cancel, upperEndTranslateGerm_zero]
  map_mul' a b := by
    apply Subtype.ext
    exact (upperEndTranslateGerm h).map_mul a b
  map_add' a b := by
    apply Subtype.ext
    exact (upperEndTranslateGerm h).map_add a b

@[simp]
theorem upperEndTranslationAnalyticEquiv_coe (h : ℂ)
    (a : upperEndAnalyticSubring) :
    ((upperEndTranslationAnalyticEquiv h a : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) = upperEndTranslateGerm h a :=
  rfl

/-- Every complex translation lifts to an automorphism of the upper-end meromorphic field. -/
noncomputable def upperEndTranslationMeroEquiv (h : ℂ) :
    upperEndMeroField ≃+* upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact IsFractionRing.ringEquivOfRingEquiv (upperEndTranslationAnalyticEquiv h)

/-- Translation on the fraction field agrees with translation on analytic germs. -/
theorem upperEndTranslationMeroEquiv_algebraMap (h : ℂ)
    (a : upperEndAnalyticSubring) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndTranslationMeroEquiv h
        (algebraMap upperEndAnalyticSubring upperEndMeroField a) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndTranslationAnalyticEquiv h a) := by
  letI := isDomain_upperEndAnalyticSubring
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

/-- Upper-end translations compose according to addition of their displacements. -/
theorem upperEndTranslationAnalyticEquiv_add (h k : ℂ)
    (a : upperEndAnalyticSubring) :
    upperEndTranslationAnalyticEquiv h (upperEndTranslationAnalyticEquiv k a) =
      upperEndTranslationAnalyticEquiv (h + k) a := by
  apply Subtype.ext
  change upperEndTranslateGerm h (upperEndTranslateGerm k
    (a : Germ upperEndFilter ℂ)) = upperEndTranslateGerm (h + k) a
  exact upperEndTranslateGerm_add h k a

/-- The same additive composition law holds on the upper-end meromorphic field. -/
theorem upperEndTranslationMeroEquiv_add (h k : ℂ)
    (x : upperEndMeroField) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndTranslationMeroEquiv h (upperEndTranslationMeroEquiv k x) =
      upperEndTranslationMeroEquiv (h + k) x := by
  letI := isDomain_upperEndAnalyticSubring
  obtain ⟨a, b, _hb, rfl⟩ :=
    IsFractionRing.div_surjective upperEndAnalyticSubring x
  rw [map_div₀, map_div₀, map_div₀]
  simp only [upperEndTranslationMeroEquiv_algebraMap,
    upperEndTranslationAnalyticEquiv_add]

/-- Complex translations commute on the upper-end meromorphic field. -/
theorem upperEndTranslationMeroEquiv_comm (h k : ℂ)
    (x : upperEndMeroField) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndTranslationMeroEquiv h (upperEndTranslationMeroEquiv k x) =
      upperEndTranslationMeroEquiv k (upperEndTranslationMeroEquiv h x) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [upperEndTranslationMeroEquiv_add, upperEndTranslationMeroEquiv_add, add_comm]

end GaloisForLFunctions.HTGeometry
