import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticRootCountsByRootSeparation
import GaloisForLFunctions.RepresentationLifting.Probability.FiniteQuotientHaar
import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature

/-!
# Split quadratics at every p-adic precision

Compactness converts separately chosen congruence solutions into an
integral solution. Consequently the uniform split probabilities at finite
precision decrease to the probability of an actual integral root. The
compact-image argument applies to continuous systems with arbitrarily
many output coordinates.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory Filter RHTower
open scoped Topology Classical
noncomputable section
variable (p : ℕ) [Fact p.Prime]

/-- Equality modulo a prime power descends to each lower precision. -/
theorem padic_congruence_mono {x y : ℤ_[p]} {k h : ℕ} (hkh : k≤h)
    (he : PadicInt.toZModPow h x = PadicInt.toZModPow h y) :
    PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  have hl := PadicInt.zmod_cast_comp_toZModPow (p:=p) k h hkh
  rw [← RingHom.congr_fun hl x,← RingHom.congr_fun hl y,RingHom.comp_apply,RingHom.comp_apply,he]

/-- Membership in a compact p-adic image is detected by its projections
at all finite precisions, even when the witnesses change with precision. -/
theorem compact_padic_image_iff_all_precisions {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ι → ℤ_[p]) (hf : Continuous f) (y : ι → ℤ_[p]) :
    y∈Set.range f ↔ ∀ h : ℕ, ∃ x : X, ∀ i, PadicInt.toZModPow h (f x i)=PadicInt.toZModPow h (y i) := by
  constructor
  · rintro ⟨x,rfl⟩ h
    exact ⟨x,fun _ => rfl⟩
  · intro h
    let S (k : ℕ) : Set X := {x | ∀ i, PadicInt.toZModPow k (f x i)=PadicInt.toZModPow k (y i)}
    have hclosed (k : ℕ) : IsClosed (S k) := by
      change IsClosed {x : X | ∀ i, _}
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq ((fieldOnePadicInt_toZModPow_continuous p k).comp
        ((continuous_apply i).comp hf)) continuous_const
    have hdec (k : ℕ) : S (k+1)⊆S k := fun _ hx i => padic_congruence_mono p (Nat.le_succ _) (hx i)
    obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hdec h (hclosed 0).isCompact hclosed
    refine ⟨x,funext fun i => PadicInt.ext_of_toZModPow.mp fun k => ?_⟩
    exact (Set.mem_iInter.mp hx k) i

/-- A quadratic has an integral root if and only if it has a root in
every residue ring. The statement includes residue characteristic two. -/
theorem padic_quadratic_root_iff_all_precisions (t d : ℤ_[p]) :
    (∃ x : ℤ_[p], x*(t-x)=d) ↔ ∀ h : ℕ, ∃ x : ZMod (p^h),
      x*(PadicInt.toZModPow h t-x)=PadicInt.toZModPow h d := by
  let f (x : ℤ_[p]) (_ : Unit) := x*(t-x)
  have hf : Continuous f := continuous_pi fun _ => continuous_id.mul (continuous_const.sub continuous_id)
  constructor
  · rintro ⟨x,rfl⟩ h
    exact ⟨PadicInt.toZModPow h x,by rw [map_mul,map_sub]⟩
  · intro h
    have ha : (fun _ : Unit => d)∈Set.range f := (compact_padic_image_iff_all_precisions p f hf _).mpr (by
      intro k
      obtain ⟨r,hr⟩ := h k
      obtain ⟨x,hx⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p:=p) k) r
      exact ⟨x,fun _ => by simpa only [f,map_mul,map_sub,hx] using hr⟩)
    obtain ⟨x,hx⟩ := ha
    exact ⟨x,congrFun hx ()⟩

/-- Root existence at a single finite precision as an event in coefficient space. -/
def quadraticSplitTube (h : ℕ) : Set (ℤ_[p]×ℤ_[p]) :=
  {z | ∃ x : ZMod (p^h), x*(PadicInt.toZModPow h z.1-x)=PadicInt.toZModPow h z.2}

private theorem splitTube_antitone : Antitone (quadraticSplitTube p) := by
  intro k h hkh z hz
  obtain ⟨x,hx⟩ := hz
  obtain ⟨u,hu⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p:=p) h) x
  have lift : PadicInt.toZModPow h (u*(z.1-u))=PadicInt.toZModPow h z.2 := by
    simpa only [map_mul,map_sub,hu] using hx
  exact ⟨PadicInt.toZModPow k u,by simpa only [map_mul,map_sub] using padic_congruence_mono p hkh lift⟩

private def coefficientProjection (h : ℕ) : (ℤ_[p]×ℤ_[p]) →+ ZMod (p^h)×ZMod (p^h) :=
  (PadicInt.toZModPow h).toAddMonoidHom.prodMap (PadicInt.toZModPow h).toAddMonoidHom

private theorem coefficientProjection_continuous (h : ℕ) : Continuous (coefficientProjection p h) :=
  ((fieldOnePadicInt_toZModPow_continuous p h).comp continuous_fst).prodMk
    ((fieldOnePadicInt_toZModPow_continuous p h).comp continuous_snd)

private theorem measurable_splitTube (h : ℕ) : MeasurableSet (quadraticSplitTube p h) :=
  ((isOpen_discrete {z : ZMod (p^h)×ZMod (p^h) | ∃ x, x*(z.1-x)=z.2}).preimage
    (coefficientProjection_continuous p h)).measurableSet

private instance coordProb : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

private theorem splitTube_intersection :
    (⋂ k, quadraticSplitTube p k) = {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2} := by
  ext z
  exact Set.mem_iInter.trans (padic_quadratic_root_iff_all_precisions p z.1 z.2).symm

/-- The splitting event is a countable intersection of measurable finite-precision events. -/
theorem measurableSet_padic_quadratic_split :
    MeasurableSet {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2} := by
  rw [←splitTube_intersection]
  exact MeasurableSet.iInter (measurable_splitTube p)

/-- The Haar mass of a finite-precision split event is the uniform
fraction of coefficient pairs with a root in that residue ring. -/
theorem quadraticSplitTube_mass (h : ℕ) :
    let μ := fieldOnePadicIntNormalizedHaar p
    letI : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    (μ.prod μ).real (quadraticSplitTube p h) = ((splitCoefficientLabels (ZMod (p^h))).card:ℝ)/(p:ℝ)^(2*h) := by
  letI : NeZero (p^h) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let μ := fieldOnePadicIntNormalizedHaar p
  let f := PadicInt.toZModPow (p:=p) h
  have surj : Function.Surjective (coefficientProjection p h) :=
    (ZMod.ringHom_surjective f).prodMap (ZMod.ringHom_surjective f)
  have hh := haar_finite_quotient_probability (μ.prod μ) (coefficientProjection p h) surj
    (coefficientProjection_continuous p h) (fun z => ∃ x, x*(z.1-x)=z.2)
  have hlabels : Nat.card {z : ZMod (p^h)×ZMod (p^h) // ∃ x, x*(z.1-x)=z.2} =
      (splitCoefficientLabels (ZMod (p^h))).card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    apply congrArg Finset.card
    ext z
    simp only [splitCoefficientLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hlabels,Nat.card_prod,Nat.card_zmod,Nat.cast_mul,Nat.cast_pow] at hh
  change (μ.prod μ).real (quadraticSplitTube p h) =
    ((splitCoefficientLabels (ZMod (p^h))).card:ℝ)/((p:ℝ)^h*(p:ℝ)^h) at hh
  exact hh.trans (by rw [two_mul,pow_add])

/-- Uniform finite-precision root probabilities converge to the actual
Haar probability that a monic quadratic has an integral root. -/
theorem tendsto_split_coefficient_probability :
    let μ := fieldOnePadicIntNormalizedHaar p
    Tendsto (fun h : ℕ => (μ.prod μ).real (quadraticSplitTube p h)) atTop
      (𝓝 ((μ.prod μ).real {z : ℤ_[p]×ℤ_[p] | ∃ x : ℤ_[p], x*(z.1-x)=z.2})) := by
  let μ := (fieldOnePadicIntNormalizedHaar p).prod (fieldOnePadicIntNormalizedHaar p)
  have hh := tendsto_measure_iInter_atTop (μ:=μ) (fun k => (measurable_splitTube p k).nullMeasurableSet)
    (splitTube_antitone p) ⟨0,measure_ne_top _ _⟩
  rw [splitTube_intersection] at hh
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh

#print axioms compact_padic_image_iff_all_precisions
#print axioms padic_quadratic_root_iff_all_precisions
#print axioms quadraticSplitTube_mass
#print axioms tendsto_split_coefficient_probability
end
end GaloisForLFunctions.RepresentationLifting
