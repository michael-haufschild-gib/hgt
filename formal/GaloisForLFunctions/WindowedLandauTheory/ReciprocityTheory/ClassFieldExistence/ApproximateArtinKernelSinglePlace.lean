import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalIdelicArtinKernelClosure

/-! An element of the kernel at a single finite place is approximable
by principal ideles in congruence neighbourhoods away from that place. -/

noncomputable section

open NumberField IsDedekindDomain WithZero Topology
open scoped RestrictedProduct

namespace GlobalTheory.Reciprocity

open IdeleGroup

private theorem isOpen_integers_away {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen {f : FiniteAdeleRing (𝓞 E) E | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ≠ w)

private theorem mem_integers_iff {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (z : E) :
    algebraMap E (v.adicCompletion E) z ∈ v.adicCompletionIntegers E ↔ v.valuation E z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v ((z : v.adicCompletion E)) ≤ 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

private theorem le_of_mul_inv_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y t : w.adicCompletion E) (ht : t ≠ 0) (h : y * t⁻¹ ∈ w.adicCompletionIntegers E) : Valued.v y ≤ Valued.v t := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀] at h
  have hp : 0 < Valued.v t := by
    rw [pos_iff_ne_zero]; exact (_root_.map_ne_zero _).mpr ht
  simpa using (mul_inv_le_iff₀ hp).mp h

private theorem snd_mul_archPositive {E : Type} [Field E] [NumberField E]
    (d c : IdeleGroup E) (hc : c ∈ archPositive E) :
    ((d * c : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (d : AdeleRing (𝓞 E) E).2 := by
  have hv : (c : AdeleRing (𝓞 E) E).2 = 1 :=
    congrArg (fun u : (FiniteAdeleRing (𝓞 E) E)ˣ => u.val)
      (show toFinite E c = 1 from hc.1)
  change (d : AdeleRing (𝓞 E) E).2 * (c : AdeleRing (𝓞 E) E).2 = _
  rw [hv, mul_one]

private theorem snd_diagonal {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    ((diagonal E k : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := rfl

private theorem localIdele_snd_ne {E : Type} [Field E] [NumberField E] (w v : HeightOneSpectrum (𝓞 E)) (hv : v ≠ w)
    (x : (w.adicCompletion E)ˣ) : ((finiteEmbedding w x : IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = 1 :=
  congrArg Units.val (finiteProj_finiteEmbedding_of_ne hv x)

theorem exists_global_approx_of_mem_diagonal_arch_closure {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (hmem : finiteEmbedding w x ∈ ((diagonal E).range ⊔ archPositive E).topologicalClosure)
    (a : ℕ) (t : w.adicCompletion E) (ht : t ≠ 0) :
    ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t := by
  have hmem' : finiteEmbedding w x ∈ closure (((diagonal E).range ⊔ archPositive E :
      Subgroup (IdeleGroup E)) : Set (IdeleGroup E)) := hmem
  let g1 : IdeleGroup E → FiniteAdeleRing (𝓞 E) E := fun y => (y : AdeleRing (𝓞 E) E).2
  let g2 : IdeleGroup E → FiniteAdeleRing (𝓞 E) E := fun y => ((y⁻¹ : IdeleGroup E) : AdeleRing (𝓞 E) E).2
  have hg1 : Continuous g1 := continuous_snd.comp Units.continuous_val
  have hg2 : Continuous g2 := continuous_snd.comp Units.continuous_coe_inv
  let c : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((a : E)⁻¹)
  let U : Set (FiniteAdeleRing (𝓞 E) E) := {f | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E}
  have hU : IsOpen U := isOpen_integers_away w
  let N : Set (IdeleGroup E) := (fun y => (g1 y - 1) * c) ⁻¹' U ∩ g2 ⁻¹' U ∩
    (fun y => (g1 y w - (x : w.adicCompletion E)) * t⁻¹) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  have hN : IsOpen N := by
    refine ((hU.preimage ((hg1.sub continuous_const).mul continuous_const)).inter (hU.preimage hg2)).inter ?_
    exact (Valued.isOpen_valuationSubring _).preimage
      ((((RestrictedProduct.continuous_eval w).comp hg1).sub continuous_const).mul continuous_const)
  have hxN : finiteEmbedding w x ∈ N := by
    refine ⟨⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
    · show ((g1 (finiteEmbedding w x) - 1) * c) v ∈ v.adicCompletionIntegers E
      have e : ((g1 (finiteEmbedding w x) - 1) * c) v = 0 := by
        show (((finiteEmbedding w x : IdeleGroup E) : AdeleRing (𝓞 E) E).2 v - 1) * c v = 0
        rw [localIdele_snd_ne w v hv, sub_self, zero_mul]
      rw [e]; exact zero_mem _
    · show g2 (finiteEmbedding w x) v ∈ v.adicCompletionIntegers E
      have e : g2 (finiteEmbedding w x) v = 1 := by
        show (((finiteEmbedding w x)⁻¹ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = 1
        rw [← map_inv]
        exact localIdele_snd_ne w v hv _
      rw [e]; exact one_mem _
    · show (g1 (finiteEmbedding w x) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E
      have e : g1 (finiteEmbedding w x) w = (x : w.adicCompletion E) := congrArg Units.val (finiteProj_finiteEmbedding w x)
      rw [e, sub_self, zero_mul]; exact zero_mem _
  obtain ⟨h, hhN, hhH⟩ := mem_closure_iff.mp hmem' N hN hxN
  obtain ⟨_, ⟨k, rfl⟩, d, hd, rfl⟩ := Subgroup.mem_sup.1 hhH
  have e1 : g1 (diagonal E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := by
    show ((diagonal E k * d : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = _
    rw [snd_mul_archPositive _ _ hd, snd_diagonal]
  have e2 : g2 (diagonal E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((k⁻¹ : Eˣ) : E) := by
    show (((diagonal E k * d)⁻¹ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = _
    rw [mul_inv, ← map_inv, snd_mul_archPositive _ _ (inv_mem hd), snd_diagonal]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hhN
  refine ⟨k, fun v hv => ⟨?_, ?_⟩, ?_⟩
  · have this : ((g1 (diagonal E k * d) - 1) * c) v ∈ v.adicCompletionIntegers E := h1 v hv
    have e : ((g1 (diagonal E k * d) - 1) * c) v = algebraMap E (v.adicCompletion E) (((k : E) - 1) / (a : E)) := by
      rw [e1, div_eq_mul_inv, map_mul, map_sub, map_one]
      rfl
    rw [e] at this
    exact (mem_integers_iff v _).mp this
  · have this : g2 (diagonal E k * d) v ∈ v.adicCompletionIntegers E := h2 v hv
    rw [e2] at this
    rw [← Units.val_inv_eq_inv_val]
    exact (mem_integers_iff v _).mp this
  · have e : g1 (diagonal E k * d) w = algebraMap E (w.adicCompletion E) (k : E) := by
      rw [e1]; rfl
    have h3' : (g1 (diagonal E k * d) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E := h3
    rw [e] at h3'
    exact le_of_mul_inv_mem w _ t ht h3'

theorem exists_global_approx_of_globalArtin_eq_one {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (f : CompactIdeleClassQuotient E →* Gal(maximalAbelianExtension E Ω/E))
    (hf : Continuous f) (hm : MatchesFiniteIdelicArtin E Ω f)
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (hx : f (toCompactIdeleClassQuotient E (finiteEmbedding w x)) = 1)
    (a : ℕ) (t : w.adicCompletion E) (ht : t ≠ 0) :
    ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t := by
  have h : finiteEmbedding w x ∈ (f.comp (toCompactIdeleClassQuotient E)).ker := hx
  rw [globalArtin_idele_ker_eq_closure f hf hm] at h
  exact exists_global_approx_of_mem_diagonal_arch_closure w x h a t ht

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_global_approx_of_mem_diagonal_arch_closure
#print axioms GlobalTheory.Reciprocity.exists_global_approx_of_globalArtin_eq_one
