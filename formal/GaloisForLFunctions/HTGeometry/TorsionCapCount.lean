import GaloisForLFunctions.HTGeometry.ComplexSumConcentration

/-!
# The torsion cap: counting phase vectors with an atypically large average

Under the uniform law on `k`-torsion phase vectors of length `D` the coordinates are independent
unimodular variables of mean zero, because the `k`-th roots of unity sum to zero.  The complex
Hoeffding bound therefore says that the fraction of vectors whose coordinate sum has modulus at
least `ε` is at most `4 exp(-ε²/(4D))`.

Multiplying by the total count turns that fraction into a bound on the number of such vectors:
at `ε = cD` the count is at most `4 e^{-c²D/4} k^D`, which is the torsion-cap estimate before the
passage to projective classes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section TorsionCount

variable (D k : ℕ)

/-- The uniform law on `k`-torsion phase vectors of length `D`. -/
def torsionMeasure [NeZero k] : Measure (Fin D → Fin k) :=
  Measure.pi fun _ => (PMF.uniformOfFintype (Fin k)).toMeasure

instance instIsProbabilityMeasureTorsion [NeZero k] :
    IsProbabilityMeasure (torsionMeasure D k) := by
  haveI : ∀ _i : Fin D, IsProbabilityMeasure ((PMF.uniformOfFintype (Fin k)).toMeasure) :=
    fun _ => PMF.toMeasure.isProbabilityMeasure _
  rw [torsionMeasure]
  infer_instance

variable {D k}

theorem torsionMeasure_singleton [NeZero k] (ω : Fin D → Fin k) :
    (torsionMeasure D k) {ω} = ((k : ℝ≥0∞) ^ D)⁻¹ := by
  classical
  have hset : ({ω} : Set (Fin D → Fin k)) = Set.univ.pi fun a => ({ω a} : Set (Fin k)) := by
    ext x
    constructor
    · rintro rfl
      intro a _
      rfl
    · intro hx
      funext a
      exact hx a (Set.mem_univ a)
  rw [torsionMeasure, hset, Measure.pi_pi]
  have hone : ∀ a : Fin D, ((PMF.uniformOfFintype (Fin k)).toMeasure {ω a}) = ((k : ℝ≥0∞))⁻¹ := by
    intro a
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    simp
  rw [Finset.prod_congr rfl fun a _ => hone a, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.inv_pow]

/-- **The uniform law counts.**  The measure of a set of phase vectors is its cardinality over the
total count. -/
theorem torsionMeasure_real_finset [NeZero k] (S : Finset (Fin D → Fin k)) :
    (torsionMeasure D k).real (S : Set (Fin D → Fin k)) = (S.card : ℝ) / (k : ℝ) ^ D := by
  classical
  have hk : (0 : ℝ) < (k : ℝ) := by
    have := NeZero.pos k
    exact_mod_cast this
  have hunion : (S : Set (Fin D → Fin k)) = ⋃ ω ∈ S, ({ω} : Set (Fin D → Fin k)) := by
    ext x
    simp
  have hdisj : (S : Set (Fin D → Fin k)).PairwiseDisjoint
      fun ω => ({ω} : Set (Fin D → Fin k)) := by
    intro a _ b _ hab
    exact Set.disjoint_singleton.mpr hab
  have hmeasure : (torsionMeasure D k) (S : Set (Fin D → Fin k))
      = ∑ ω ∈ S, ((k : ℝ≥0∞) ^ D)⁻¹ := by
    rw [hunion, measure_biUnion_finset hdisj fun ω _ => measurableSet_singleton ω]
    exact Finset.sum_congr rfl fun ω _ => torsionMeasure_singleton ω
  rw [measureReal_def, hmeasure, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, div_eq_mul_inv]
  simp

/-- **The torsion cap.**  At most `4 e^{-ε²/(4D)} k^D` phase vectors have coordinate sum of modulus
at least `ε`. -/
theorem card_le_of_forall_norm_sum_ge [NeZero k] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k)
    (S : Finset (Fin D → Fin k)) {ε : ℝ} (hε : 0 ≤ ε)
    (hS : ∀ ω ∈ S, ε ≤ ‖∑ a, ζ ^ (ω a : ℕ)‖) :
    (S.card : ℝ) ≤ 4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by
    have := NeZero.pos k
    exact_mod_cast this
  set Y : Fin k → ℂ := fun x => ζ ^ (x : ℕ) with hY
  set X : Fin D → (Fin D → Fin k) → ℂ := fun a ω => Y (ω a) with hX
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
  have hYnorm : ∀ x : Fin k, ‖Y x‖ = 1 := by
    intro x
    rw [hY, norm_pow, hnorm, one_pow]
  have hindep : iIndepFun X (torsionMeasure D k) := by
    rw [hX, torsionMeasure]
    exact iIndepFun_pi fun _ => (measurable_of_finite Y).aemeasurable
  have hindepRe : iIndepFun (fun a ω => (X a ω).re) (torsionMeasure D k) :=
    hindep.comp (fun _ => Complex.re) fun _ => Complex.measurable_re
  have hindepIm : iIndepFun (fun a ω => (X a ω).im) (torsionMeasure D k) :=
    hindep.comp (fun _ => Complex.im) fun _ => Complex.measurable_im
  have hmeas : ∀ a, AEMeasurable (X a) (torsionMeasure D k) := fun a =>
    (measurable_of_finite (X a)).aemeasurable
  have hbound : ∀ a, ∀ᵐ ω ∂(torsionMeasure D k), ‖X a ω‖ ≤ 1 := by
    intro a
    filter_upwards with ω
    rw [hX, hYnorm]
  have hsumzero : (∑ x : Fin k, Y x) = 0 := by
    rw [hY, Fin.sum_univ_eq_sum_range fun i => ζ ^ i]
    exact hζ.geom_sum_eq_zero hk
  have hmarginal : ∀ a : Fin D, ∀ f : ℂ → ℝ, Measurable f →
      ∫ ω, f (X a ω) ∂(torsionMeasure D k)
        = ∫ x, f (Y x) ∂((PMF.uniformOfFintype (Fin k)).toMeasure) := by
    intro a f hf
    have hmp : MeasurePreserving (fun ω : Fin D → Fin k => ω a) (torsionMeasure D k)
        ((PMF.uniformOfFintype (Fin k)).toMeasure) := by
      rw [torsionMeasure]
      exact measurePreserving_eval _ a
    calc ∫ ω, f (X a ω) ∂(torsionMeasure D k)
        = ∫ ω, (fun x => f (Y x)) (ω a) ∂(torsionMeasure D k) := rfl
      _ = ∫ x, f (Y x) ∂((PMF.uniformOfFintype (Fin k)).toMeasure) := by
          rw [← hmp.map_eq, integral_map (measurable_pi_apply a).aemeasurable
            ((hf.comp (measurable_of_finite Y)).aestronglyMeasurable)]
  have hcentreRe : ∀ a, ∫ ω, (X a ω).re ∂(torsionMeasure D k) = 0 := by
    intro a
    rw [hmarginal a Complex.re Complex.measurable_re, PMF.integral_eq_sum]
    have hval : ∀ x : Fin k, ((PMF.uniformOfFintype (Fin k)) x).toReal • (Y x).re
        = ((k : ℝ))⁻¹ * (Y x).re := by
      intro x
      rw [PMF.uniformOfFintype_apply]
      simp
    rw [Finset.sum_congr rfl fun x _ => hval x, ← Finset.mul_sum, ← Complex.re_sum, hsumzero]
    simp
  have hcentreIm : ∀ a, ∫ ω, (X a ω).im ∂(torsionMeasure D k) = 0 := by
    intro a
    rw [hmarginal a Complex.im Complex.measurable_im, PMF.integral_eq_sum]
    have hval : ∀ x : Fin k, ((PMF.uniformOfFintype (Fin k)) x).toReal • (Y x).im
        = ((k : ℝ))⁻¹ * (Y x).im := by
      intro x
      rw [PMF.uniformOfFintype_apply]
      simp
    rw [Finset.sum_congr rfl fun x _ => hval x, ← Finset.mul_sum, ← Complex.im_sum, hsumzero]
    simp
  have hconc := measureReal_norm_sum_ge_le (μ := torsionMeasure D k) X hindepRe hindepIm hmeas
    hbound hcentreRe hcentreIm hε
  rw [Fintype.card_fin] at hconc
  have hsub : (S : Set (Fin D → Fin k)) ⊆ {ω | ε ≤ ‖∑ a, X a ω‖} := by
    intro ω hω
    exact hS ω (by exact_mod_cast hω)
  have hmono : (torsionMeasure D k).real (S : Set (Fin D → Fin k))
      ≤ (torsionMeasure D k).real {ω | ε ≤ ‖∑ a, X a ω‖} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [torsionMeasure_real_finset] at hmono
  have hchain : (S.card : ℝ) / (k : ℝ) ^ D ≤ 4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) :=
    le_trans hmono hconc
  rw [div_le_iff₀ (by positivity)] at hchain
  exact hchain


/-- Counting through a map with constant fibre size. -/
theorem card_filter_mem_eq_mul {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (π : A → B) (k : ℕ) (hfib : ∀ b, (Finset.univ.filter fun a => π a = b).card = k)
    (T : Finset B) :
    (Finset.univ.filter fun a => π a ∈ T).card = k * T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := π) (s := Finset.univ.filter fun a => π a ∈ T) (t := T) fun a ha => (Finset.mem_filter.mp ha).2]
  have hterm : ∀ b ∈ T,
      ((Finset.univ.filter fun a => π a ∈ T).filter fun a => π a = b).card = k := by
    intro b hb
    rw [← hfib b]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hab⟩
      exact hab
    · intro hab
      exact ⟨by rw [hab]; exact hb, hab⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]

/-- A set covered by finitely many small sets is small. -/
theorem card_le_of_subset_biUnion {A ι : Type*} [DecidableEq A] [DecidableEq ι]
    (T : Finset ι) (S : ι → Finset A) (U : Finset A) (hsub : U ⊆ T.biUnion S)
    (B : ℕ) (hB : ∀ i ∈ T, (S i).card ≤ B) :
    U.card ≤ T.card * B := by
  classical
  calc U.card ≤ (T.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ T, (S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, B := Finset.sum_le_sum hB
    _ = T.card * B := by rw [Finset.sum_const, smul_eq_mul]

/-- **The torsion-cap count `(7)`.**  If every representative of a captured class has coordinate sum
of modulus at least `ε` for one of `N` targets, then the number of classes obeys the exponential
cap. -/
theorem card_classes_le_of_cover {B ι : Type*} [DecidableEq B] [DecidableEq ι]
    [NeZero k] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k)
    (π : (Fin D → Fin k) → B) (hfib : ∀ b, (Finset.univ.filter fun ω => π ω = b).card = k)
    (E : Finset B) (Y : Finset ι) (S : ι → Finset (Fin D → Fin k))
    (hcover : (Finset.univ.filter fun ω => π ω ∈ E) ⊆ Y.biUnion S)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hS : ∀ y ∈ Y, ∀ ω ∈ S y, ε ≤ ‖∑ a, ζ ^ (ω a : ℕ)‖) :
    (k : ℝ) * (E.card : ℝ)
      ≤ (Y.card : ℝ) * (4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D) := by
  classical
  have hcount : ∀ y ∈ Y, ((S y).card : ℝ)
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D := fun y hy =>
    card_le_of_forall_norm_sum_ge hζ hk (S y) hε (hS y hy)
  have hbound : (((Finset.univ.filter fun ω => π ω ∈ E).card : ℕ) : ℝ)
      ≤ ∑ y ∈ Y, ((S y).card : ℝ) := by
    have hle : (Finset.univ.filter fun ω => π ω ∈ E).card ≤ ∑ y ∈ Y, (S y).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    exact_mod_cast hle
  have hsum : (∑ y ∈ Y, ((S y).card : ℝ))
      ≤ (Y.card : ℝ) * (4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D) := by
    calc (∑ y ∈ Y, ((S y).card : ℝ))
        ≤ ∑ _y ∈ Y, 4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D :=
          Finset.sum_le_sum hcount
      _ = (Y.card : ℝ) * (4 * Real.exp (-ε ^ 2 / (4 * (D : ℝ))) * (k : ℝ) ^ D) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfibcount := card_filter_mem_eq_mul π k hfib E
  rw [hfibcount] at hbound
  push_cast at hbound
  linarith [hbound, hsum]

end TorsionCount

end

end GaloisForLFunctions.HTGeometry
