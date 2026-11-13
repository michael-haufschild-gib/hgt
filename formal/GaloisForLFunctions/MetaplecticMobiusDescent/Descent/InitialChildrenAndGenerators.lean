/-
Initial children and generator transport adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.ClippingProfilesAndInitialFibers
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.DescentProfiles

/-!
# Initial children and generator transport

Child logarithmic tests, canonical margins and initial children of the descent. Generators are
units times primary elements; second generator sectors and the second source pair kernel.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson InverseInitialFibers
open scoped BigOperators Classical

def weightedEnergy {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ i ∈ s, w i * ‖f i‖ ^ 2

theorem weightedEnergy_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ weightedEnergy s w f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f g : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
      Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by
  have hn (F : ι → ℂ) :
      (∑ i ∈ s, ‖(w i : ℂ)‖ * ‖F i‖ ^ 2) = weightedEnergy s w F := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  simpa only [hn] using DescentWeightedCauchy.weighted_cauchy s (fun i => (w i : ℂ)) f g

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

theorem weightedEnergy_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    weightedEnergy s w (f ∘ p) ≤ weightedEnergy t D f := by
  exact fiber_energy_bound s t p w D (fun j => ‖f j‖ ^ 2) hp
    (fun j _ => sq_nonneg _) hD

theorem weighted_cauchy_fiber {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f g : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ‖∑ i ∈ s, (w i : ℂ) * f (p i) * star (g (p i))‖ ≤
      Real.sqrt (weightedEnergy t D f) * Real.sqrt (weightedEnergy t D g) := by
  apply (weighted_cauchy s w (f ∘ p) (g ∘ p) hw).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D f hp hD))
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D g hp hD))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]

end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson InverseInitialFibers
open scoped BigOperators Classical

abbrev InitialChild := Ideal O × Ideal O × O

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (quadraticIdealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryIdealGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryIdealGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : quadraticIdealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, quadraticIdeal_mul_quotient hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ quadraticIdealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp [he])
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal O) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (hsource x hxs)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 : c.1 ≠ 0 := he ▸ (initialChild_nonzero x (hsource x hx)).1
    exact initialChild_fiber_weight source hsource c ht0
      (hlabels c.2.1 (Finset.mem_product.mp hfk).1) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

def initialPositiveEnergy {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal O)) (rows : Finset O) (F : InitialChild → ℂ) : ℝ :=
  ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
    ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
      ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2

theorem initialPositiveEnergy_nonneg {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal O)) (rows : Finset O) (F : InitialChild → ℂ) :
    0 ≤ initialPositiveEnergy source labels rows F := by
  unfold initialPositiveEnergy
  positivity

theorem initial_weighted_count {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      Real.sqrt (initialPositiveEnergy source labels rows F) *
        Real.sqrt (initialPositiveEnergy source labels rows G) := by
  have hF := initial_energy_projection source hsource labels rows hlabels hchild w hw1 F
  have hG := initial_energy_projection source hsource labels rows hlabels hchild w hw1 G
  apply (weighted_cauchy source w (F ∘ initialChild) (G ∘ initialChild) hw0).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem initial_weighted_count_normalized {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) (H : ℝ) (hH : 0 < H) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      H * (Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows F) *
        Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows G)) := by
  apply (initial_weighted_count source hsource labels rows hlabels hchild w hw0 hw1 F G).trans_eq
  rw [Real.sqrt_mul (inv_nonneg.mpr hH.le), Real.sqrt_mul (inv_nonneg.mpr hH.le)]
  have hc : H * (Real.sqrt H⁻¹) ^ 2 = 1 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hH.le), mul_inv_cancel₀ hH.ne']
  calc
    _ = (H * (Real.sqrt H⁻¹) ^ 2) *
        (Real.sqrt (initialPositiveEnergy source labels rows F) *
          Real.sqrt (initialPositiveEnergy source labels rows G)) := by rw [hc, one_mul]
    _ = _ := by ring

end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open scoped BigOperators Classical

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : O →* ℂ) (m a f k : O)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ m (a*f) k H S =
      secondChildColumn p hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, primeSubsetRow, map_mul, map_pow, Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

theorem secondChildColumn_puncture_unit (Ψ : O →* ℂ) (u : Oˣ) (m f k : O)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ ((u:O)*m) f k H S =
      secondChildColumn p hg Ψ m f k H S := by
  have he : Ideal.span {((u:O)*m)} = Ideal.span {m} :=
    Ideal.span_singleton_mul_left_unit u.isUnit m
  simp only [secondChildColumn,primeCoprimeMask_congr_span p S he]

theorem secondChildColumn_generator_unit (Ψ : O →* ℂ) (u : Oˣ) (m f d k : O)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ m ((u:O)*f) ((u:O)*d*k) H S =
      secondChildColumn p hg Ψ m f (d*((u:O)^5*k)) H S := by
  rw [secondChildColumn_label_transfer]
  congr 1
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer (F : Finset ι) (Ψ : O →* ℂ)
    (m a f k : O) (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

theorem generator_eq_unit_primary (I : Ideal O) (e : O)
    (he : Ideal.span {e} = I) (hI : primaryIdealGenerator I ≠ 0) :
    ∃ u : Oˣ, e = (u:O)*primaryIdealGenerator I := by
  have ha : Associated (primaryIdealGenerator I) e :=
    Ideal.span_singleton_eq_span_singleton.mp ((primaryIdealGenerator_spec I hI).1.trans he.symm)
  obtain ⟨u,hu⟩ := ha
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

lemma normalized_generator_row_norm (u : Oˣ) (d k : O) :
    ‖ringComplex (d*((u:O)^5*k))‖ =
      ‖ringComplex (d*k)‖ := by
  have he : d*((u:O)^5*k) = ((u^5:Oˣ):O)*(d*k) := by
    change d*((u:O)^5*k) = (u:O)^5*(d*k)
    ring
  rw [he,map_mul,norm_mul,norm_ringComplex_unit,one_mul]

end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson InverseMoment JointLogSeparation SecondPassArithmetic FirstPassCubeLabels MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

def secondOuterPhase (h y : Fin 6 → ℝ) : ℂ :=
  kernelLogPhase (h 0) (y 0) * kernelLogPhase (h 1) (y 1) *
    kernelLogPhase (h 2) (y 2) * kernelLogPhase (h 3) (y 3)

def childLogTest (omega : ℝ → ℂ) (h : ℝ) (y : ℝ) : ℂ :=
  omega y * kernelLogPhase h (Real.log y)

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        kernelLogPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        kernelLogPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring!

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,kernelLogPhase_norm,mul_one]

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N) (X : ℝ) :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem fresh_ratio_of_source_support (W : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n) (hw : W (g*v*n) ≠ 0) :
    n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)) := by
  have hgp : 0 < g := hg₀.trans_le hg.1
  have hvp : 0 < v := hv₀.trans_le hv.1
  have hghi : 0 < g₁ := hgp.trans_le hg.2
  have hvhi : 0 < v₁ := hvp.trans_le hv.2
  have hsource := hs hw
  constructor
  · apply (div_le_iff₀ (mul_pos hghi hvhi)).mpr
    calc
      a ≤ g*v*n := hsource.1
      _ ≤ (g₁*v₁)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.2 hv.2 hvp.le hghi.le) hn
      _ = _ := by ring
  · apply (le_div_iff₀ (mul_pos hg₀ hv₀)).mpr
    calc
      _ = (g₀*v₀)*n := by ring
      _ ≤ g*v*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.1 hv.1 hv₀.le hgp.le) hn
      _ ≤ b := hsource.2

theorem fresh_window_eq_one (W omega : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n)
    (homega : ∀ n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)), omega n = 1)
    (hw : W (g*v*n) ≠ 0) : omega n = 1 :=
  homega n (fresh_ratio_of_source_support W a b g₀ g₁ v₀ v₁ g v n hs hg₀ hv₀ hg hv hn hw)


end InverseMoment

namespace InverseMoment
def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

theorem markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith

theorem markedMargins_subcollection {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_subcollection {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_weaken {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

theorem canonical_transition (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring

theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

theorem child_row_decrease {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

theorem childF_upper {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith

theorem clipping_bounds {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

theorem initial_prefactor_identity (m r z G P : ℝ) :
    (m - 2 * (r + z - 2 * G) + P) + P +
      2 * initialF r z G P 0 = m := by
  unfold initialF
  ring

theorem initial_energy_exponent {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith

theorem total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith

theorem depth_margin {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith


end InverseMoment

namespace InverseMoment
open Eisenstein
open scoped BigOperators Classical
theorem ideal_divisor_power_small (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ 0 →
      ((idealDivisors I).card : ℝ)^j ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have hj : 0 < (j+1 : ℝ) := by positivity
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/(j+1)) (div_pos hε hj)
  refine ⟨C ^ (j+1), by positivity, ?_⟩
  intro I hI
  have hcard : (1 : ℝ) ≤ (idealDivisors I).card := by
    exact_mod_cast InverseInitialFibers.divisor_card_pos I hI
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^(j+1) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(Ideal.absNorm I : ℝ)^(ε/(j+1)))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (hb I hI) _
    _ = C ^ (j+1)*(Ideal.absNorm I : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      field_simp


end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

theorem primeMark_indexed_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A =
      ∑ r ∈ (I.pi (fun i => L i ∩ A)).image (indexedSlotAssignment I),
        slotAssignmentWeight I a (fun i hi => r (I.equivFin ⟨i,hi⟩)) := by
  rw [Finset.sum_image (fun q _ r _ h => indexedSlotAssignment_injective I h)]
  simpa only [indexedSlotAssignment,Equiv.symm_apply_apply] using
    primeMark_supported_assignments I L a A

def pairedSlotAssignment (J₁ J₂ : Finset σ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : Fin (J₁.card+J₂.card) → ι :=
  Fin.addCases (indexedSlotAssignment J₁ q.1) (indexedSlotAssignment J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

def pairedSlotWeight (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁ q.1)*slotAssignmentWeight J₂ a₂ q.2

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)


omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)


theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2


end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open scoped Classical
/-- A finite disk containing every frequency below the scaled quadratic cutoff. -/
def secondFrequencyCutoff (scale H : ℝ) : Finset O :=
  (finite_norm_sublevel (Real.sqrt (H/scale))).toFinset

lemma mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖ringComplex k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  change k ∈ (finite_norm_sublevel (Real.sqrt (H/scale))).toFinset
  rw [Set.Finite.mem_toFinset]
  change ‖ringComplex k‖ ≤ Real.sqrt (H/scale)
  have hR : 0 ≤ H/scale := (sq_nonneg _).trans hk
  nlinarith only [hk, Real.sq_sqrt hR, Real.sqrt_nonneg (H/scale), norm_nonneg (ringComplex k)]

lemma secondFrequencyCutoff_zero (scale H : ℝ) : (0:O) ∈ secondFrequencyCutoff scale H := by
  change 0 ∈ (finite_norm_sublevel (Real.sqrt (H/scale))).toFinset
  simpa only [Set.Finite.mem_toFinset,Set.mem_setOf_eq,map_zero,norm_zero] using Real.sqrt_nonneg (H/scale)

lemma outside_secondFrequencyCutoff (scale H : ℝ) (hs : 0<scale) (k:O)
    (hk : k ∉ secondFrequencyCutoff scale H) : H < scale * ‖ringComplex k‖^2 := by
  have hn : H/scale < ‖ringComplex k‖^2 := lt_of_not_ge (fun h => hk (mem_secondFrequencyCutoff scale H k h))
  simpa only [mul_comm] using (div_lt_iff₀ hs).mp hn
lemma active_product_norm_disjoint {ι : Type*} [DecidableEq ι] (p:ι→O)
    (S T:Finset ι) (hd:Disjoint S T) :
    ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2 =
      primeProductNorm p S * primeProductNorm p T := by
  rw [Finset.prod_coe_sort]
  simp only [Finset.sdiff_eq_self_of_disjoint hd,Finset.sdiff_eq_self_of_disjoint hd.symm,
    Finset.prod_union hd.symm,map_mul,norm_mul,mul_pow,primeProductNorm]
  ring
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O

def secondOuterBall (Y E X₁ X₂ H : ℝ) : Finset Eis :=
  secondFrequencyCutoff (Y / (E * X₁ * X₂)) H

theorem secondOuterBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hE : 0 < E) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (e : Eis) (he : e ≠ 0) (heE : ‖ringComplex e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ secondOuterBall Y E X₁ X₂ H) :
    H ≤ (Y / (‖ringComplex e‖^2 *
      ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2)) * ‖ringComplex k‖^2 := by
  have hs : 0 < Y/(E*X₁*X₂) := by positivity
  have hn : 0 < ‖ringComplex e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he))
  have hprod : ‖ringComplex e‖^2 * primeProductNorm p S * primeProductNorm p T ≤ E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul heE hS (primeProductNorm_pos p hp S).le hE.le)
      hT (primeProductNorm_pos p hp T).le (mul_pos hE hX₁).le
  have hb : Y/(E*X₁*X₂) ≤
      Y/(‖ringComplex e‖^2 * ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2) := by
    rw [active_product_norm_disjoint p S T hd]
    apply div_le_div_of_nonneg_left hY.le
    · exact mul_pos hn (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
    · simpa only [mul_assoc] using hprod
  exact (outside_secondFrequencyCutoff _ H hs k hk).le.trans
    (mul_le_mul_of_nonneg_right hb (sq_nonneg _))

theorem secondOuterBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y E X₁ X₂ H : ℝ),
      0 < Y → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (e : Eis), e ≠ 0 → ‖ringComplex e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
      let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
      ‖∑' k : {k : Eis // k ∉ secondOuterBall Y E X₁ X₂ H},
        secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ ≤
      (Y / ‖ringComplex n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder A
  have hb := hb p hp hg hinj
  refine ⟨s,C,hC,?_⟩
  intro W Y E X₁ X₂ H hY hE hX₁ hX₂ hH e he heE S T hd hS hT
  exact hb S T e he W Y H hY hH (secondOuterBall Y E X₁ X₂ H)
    (fun k hk => secondOuterBall_raw_tail p hp Y E X₁ X₂ H hY hE hX₁ hX₂ e he heE S T hd hS hT k hk)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

lemma norm_unit_mul (u:Oˣ) (k:O) : ‖ringComplex ((u:O)*k)‖=‖ringComplex k‖ := by
  rw [map_mul,norm_mul,norm_ringComplex_unit,one_mul]

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ringComplex (secondUnitFrequency u v k)‖ =
      ‖ringComplex k‖ :=
  norm_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryIdealGenerator L)
    (hd : d*e = (v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hg F Ψ m (primaryIdealGenerator L)
        (primaryIdealGenerator D*primaryIdealGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E)*k) =
    primaryIdealGenerator D*primaryIdealGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem secondCanonical_row_norm (D E : Ideal Eis) (u v : Eisˣ) (d e k : Eis)
    (hd : d*e = (v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E)) :
    ‖ringComplex
      (primaryIdealGenerator D*primaryIdealGenerator E*secondUnitFrequency u v k)‖ =
      ‖ringComplex (d*e*k)‖ := by
  rw [hd]
  have hl : primaryIdealGenerator D*primaryIdealGenerator E*secondUnitFrequency u v k =
      ((u^4*v:Eisˣ):Eis)*(primaryIdealGenerator D*primaryIdealGenerator E*k) := by
    unfold secondUnitFrequency
    ring
  rw [hl,norm_unit_mul]
  have hr : (v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E)*k =
      (v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E*k) := by ring
  rw [hr,norm_unit_mul]

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryIdealGenerator L ≠ 0) (hD : primaryIdealGenerator D ≠ 0) (hE : primaryIdealGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryIdealGenerator L ∧
      d*e = (v:Eis)*(primaryIdealGenerator D*primaryIdealGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryIdealGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryIdealGenerator_mul] using hv⟩

end
end InverseMoment

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
local notation "Eis" => O
variable {ι:Type*} [DecidableEq ι] (p:ι→O)
def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) * (‖ringComplex (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖ringComplex e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖ringComplex e‖^2, primeProductNorm p V,
        ‖ringComplex k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖ringComplex (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖ringComplex k‖^2 /
      (‖ringComplex e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖ringComplex k‖^2 / (‖ringComplex e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
