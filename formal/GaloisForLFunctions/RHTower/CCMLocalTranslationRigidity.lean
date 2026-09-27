import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Tactic

/-!
# Measurable rigidity of two local translations

No continuity of the source is assumed. A local period propagates through
integer multiples inside the interval. This identifies the source with a
measurable circle lift; the second local period becomes an irrational rotation.
The interval must contain one complete period cell and its second translate.
-/

open MeasureTheory Set Filter
noncomputable section
namespace RHTower

def CCMLocalTranslationInvariant (f : ℝ → ℂ) (L U p : ℝ) : Prop :=
  ∀ᵐ x : ℝ, x ∈ Icc L U → x+p ∈ Icc L U → f (x+p) = f x

private theorem local_nat (f : ℝ → ℂ) (L U p : ℝ) (hp : 0 ≤ p)
    (hf : CCMLocalTranslationInvariant f L U p) (n : ℕ) :
    ∀ᵐ x : ℝ, x ∈ Icc L U → x+(n : ℝ)*p ∈ Icc L U → f (x+(n : ℝ)*p) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (quasiMeasurePreserving_add_right volume ((n : ℝ)*p)).ae hf
    filter_upwards [ih,hs] with x hx hs hxi hxn
    have hnp : 0 ≤ (n : ℝ)*p := mul_nonneg (Nat.cast_nonneg n) hp
    have hmid : x+(n : ℝ)*p ∈ Icc L U := by
      constructor
      · linarith [hxi.1]
      · push_cast at hxn
        linarith [hxn.2]
    have heq : x+((n+1 : ℕ) : ℝ)*p = (x+(n : ℝ)*p)+p := by push_cast; ring
    rw [heq] at hxn ⊢
    exact (hs hmid hxn).trans (hx hxi hmid)

private theorem local_int (f : ℝ → ℂ) (L U p : ℝ) (hp : 0 ≤ p)
    (hf : CCMLocalTranslationInvariant f L U p) (n : ℤ) :
    ∀ᵐ x : ℝ, x ∈ Icc L U → x+(n : ℝ)*p ∈ Icc L U → f (x+(n : ℝ)*p) = f x := by
  cases n with
  | ofNat n => exact local_nat f L U p hp hf n
  | negSucc n =>
    have hs := (quasiMeasurePreserving_add_right volume (-((n+1 : ℕ) : ℝ)*p)).ae
      (local_nat f L U p hp hf (n+1))
    filter_upwards [hs] with x hx hxi hxn
    have heq : ((Int.negSucc n : ℤ) : ℝ)*p = -((n+1 : ℕ) : ℝ)*p := by
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    rw [heq] at hxn ⊢
    have hback : x + -((n+1 : ℕ) : ℝ)*p + ((n+1 : ℕ) : ℝ)*p = x := by ring
    have h := hx hxn (by rwa [hback])
    rw [hback] at h
    exact h.symm

private theorem lift_agrees (f : ℝ → ℂ) (L U p : ℝ) (hp : 0 < p)
    (hwidth : L+p ≤ U) (hf : CCMLocalTranslationInvariant f L U p) :
    letI : Fact (0 < p) := ⟨hp⟩
    ∀ᵐ x : ℝ, x ∈ Icc L U →
      f (AddCircle.equivIoc p L (x : AddCircle p)) = f x := by
  letI : Fact (0 < p) := ⟨hp⟩
  have hall := (ae_all_iff.mpr (fun n : ℤ => local_int f L U p hp.le hf n))
  filter_upwards [hall] with x hx hxi
  let n := toIocDiv hp L x
  have hr : x-(n : ℝ)*p ∈ Ioc L (L+p) := by
    simpa only [zsmul_eq_mul] using sub_toIocDiv_zsmul_mem_Ioc hp L x
  have hrI : x-(n : ℝ)*p ∈ Icc L U := ⟨hr.1.le,hr.2.trans hwidth⟩
  have heq : (AddCircle.equivIoc p L (x : AddCircle p) : ℝ) = x-(n : ℝ)*p := by
    change toIocMod hp L x = x-(n : ℝ)*p
    simp only [toIocMod, zsmul_eq_mul, n]
  rw [heq]
  have h := hx (-n) hxi
  simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using h
    (by simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using hrI)

private theorem circle_ae_pullback (p L : ℝ) [Fact (0 < p)]
    (g : AddCircle p → ℂ) (c : ℂ) (hc : g =ᵐ[volume] fun _ => c) :
    ∀ᵐ x : ℝ, g (x : AddCircle p) = c := by
  rw [← Measure.restrict_univ (μ := volume),
    ← iUnion_Ioc_add_zsmul (show 0 < p from Fact.out) L, ae_restrict_iUnion_iff]
  intro n
  have h := (AddCircle.measurePreserving_mk p (L+n • p)).quasiMeasurePreserving.ae hc
  simpa only [add_smul, one_smul, add_assoc] using h

/-- Two incommensurable local translations force measurable constancy once
the interval contains a period cell and its second translate. -/
theorem ae_eq_const_of_two_ccmLocalTranslations
    (f : ℝ → ℂ) (hf : Measurable f) (L U p q : ℝ)
    (hp : 0 < p) (hq : 0 ≤ q) (hwidth : L+p+q ≤ U)
    (hirr : Irrational (q/p))
    (hper : CCMLocalTranslationInvariant f L U p)
    (hqper : CCMLocalTranslationInvariant f L U q) :
    ∃ c : ℂ, ∀ᵐ x : ℝ, x ∈ Icc L U → f x = c := by
  letI : Fact (0 < p) := ⟨hp⟩
  let g : AddCircle p → ℂ := fun z => f (AddCircle.equivIoc p L z)
  have hg : Measurable g :=
    hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc p L).measurable)
  have hagree : ∀ᵐ x : ℝ, x ∈ Icc L U → g (x : AddCircle p) = f x :=
    lift_agrees f L U p hp (by linarith) hper
  have hshift := (quasiMeasurePreserving_add_right volume q).ae hagree
  have hinvReal : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc L (L+p)),
      g ((x : AddCircle p)+(q : AddCircle p)) = g (x : AddCircle p) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hagree,hshift,hqper] with x hx hs hqstep hxcell
    have hxi : x ∈ Icc L U := ⟨hxcell.1.le, by linarith [hxcell.2]⟩
    have hxq : x+q ∈ Icc L U := ⟨by linarith [hxi.1], by linarith [hxcell.2]⟩
    rw [← AddCircle.coe_add, hs hxq, hqstep hxi hxq, hx hxi]
  have hinv : (fun z => g (z+(q : AddCircle p))) =ᵐ[volume] g := by
    have hmp := AddCircle.measurePreserving_mk p L
    rw [← hmp.map_eq]
    exact (ae_map_iff hmp.measurable.aemeasurable
      (measurableSet_eq_fun (hg.comp (measurable_id.add measurable_const)) hg)).mpr hinvReal
  have he : Ergodic (fun z : AddCircle p => z+(q : AddCircle p)) :=
    AddCircle.ergodic_add_right.mpr (AddCircle.denseRange_zsmul_iff.mp
      (AddCircle.denseRange_zsmul_coe_iff.mpr hirr))
  obtain ⟨c,hc⟩ := he.ae_eq_const_of_ae_eq_comp₀ hg.nullMeasurable hinv
  have hreal := circle_ae_pullback p L g c hc
  refine ⟨c, ?_⟩
  filter_upwards [hagree,hreal] with x hx hc hxi
  exact (hx hxi).symm.trans hc

end RHTower
