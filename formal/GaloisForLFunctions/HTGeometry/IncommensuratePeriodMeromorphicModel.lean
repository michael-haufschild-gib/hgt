import GaloisForLFunctions.HTGeometry.MeromorphicTranslationFixedField
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicPhysicalCharacteristicIncidence
import GaloisForLFunctions.HTGeometry.MultiplicativeOrbitNonSummability
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositum
import Mathlib.NumberTheory.Real.Irrational

/-!
# The incommensurate-period meromorphic model

Two ingredients of the concrete double-sine model are built here, inside the global meromorphic
field.

**The common fixed field.**  A germ fixed by two translations is fixed by their whole integer span
(`addTranslationMeroEquiv_fixed_of_mem_intSpan`).  When the two periods are `ℚ`-independent and
`ℝ`-dependent — the case of two positive reals with irrational ratio — that span is not discrete,
so it contains arbitrarily small nonzero periods, and a global meromorphic germ with arbitrarily
small periods is constant.  Hence
`exists_constant_of_two_realDependent_translations_fixed`: the common fixed field of the two
translations is exactly `ℂ`.  This is the hypothesis under which the arbitrary-family Ostrowski
criterion applies, and it is the only place where incommensurability of the two periods is used.

**Independent cylinder coordinates.**  The exponential characters `z ↦ exp(μ z)` are monoid
homomorphisms of the additive group of `ℂ`, injective in `μ`, so Dedekind's independence of
characters makes exponentials with pairwise distinct frequencies linearly independent
(`exp_coeff_eq_zero_of_sum_eq_zero`).  Point evaluation of global analytic germs is a ring
homomorphism, so the same independence holds for the exponential modes
`physicalExponentialMero μ` inside the meromorphic field
(`physicalExponentialMero_coeff_eq_zero_of_sum_eq_zero`).  This is the separation statement that
makes the two cylinders `u₁ = exp(2πi z/ω₁)` and `u₂ = exp(2πi z/ω₂)` independent coordinates when
`ω₁/ω₂` is irrational.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance twoCylDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance twoCylComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance twoCylComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

/-! ## Fixed points of an integer span of translations -/

theorem addTranslationMeroEquiv_fixed_neg {q : ℂ} {z : meroField (Set.univ : Set ℂ)}
    (h : addTranslationMeroEquiv q z = z) : addTranslationMeroEquiv (-q) z = z := by
  have hcong := congrArg (addTranslationMeroEquiv (-q)) h
  rw [addTranslationMeroEquiv_add, neg_add_cancel, addTranslationMeroEquiv_zero_apply] at hcong
  exact hcong.symm

theorem addTranslationMeroEquiv_fixed_intMul {q : ℂ} {z : meroField (Set.univ : Set ℂ)}
    (h : addTranslationMeroEquiv q z = z) (a : ℤ) :
    addTranslationMeroEquiv ((a : ℂ) * q) z = z := by
  refine Int.induction_on a ?_ ?_ ?_
  · simpa using addTranslationMeroEquiv_zero_apply z
  · intro n ih
    have hsplit : (((n : ℤ) + 1 : ℤ) : ℂ) * q = (-q) + ((n : ℂ) + 1 + 1) * q := by
      push_cast; ring
    push_cast at ih ⊢
    rw [show ((n : ℂ) + 1) * q = q + (n : ℂ) * q by ring, ← addTranslationMeroEquiv_add, ih, h]
  · intro n ih
    push_cast at ih ⊢
    rw [show (-(n : ℂ) - 1) * q = (-q) + (-(n : ℂ)) * q by ring,
      ← addTranslationMeroEquiv_add, ih, addTranslationMeroEquiv_fixed_neg h]

theorem addTranslationMeroEquiv_fixed_of_mem_intSpan {ι : Type*} (v : ι → ℂ)
    {z : meroField (Set.univ : Set ℂ)} (h : ∀ i, addTranslationMeroEquiv (v i) z = z)
    {q : ℂ} (hq : q ∈ Submodule.span ℤ (Set.range v)) :
    addTranslationMeroEquiv q z = z := by
  refine Submodule.span_induction
    (p := fun x _ => addTranslationMeroEquiv x z = z) ?_ ?_ ?_ ?_ hq
  · rintro x ⟨i, rfl⟩
    exact h i
  · exact addTranslationMeroEquiv_zero_apply z
  · intro x y _ _ hx hy
    rw [← addTranslationMeroEquiv_add, hy, hx]
  · intro a x _ hx
    have : a • x = (a : ℂ) * x := by
      simp [zsmul_eq_mul]
    rw [this]
    exact addTranslationMeroEquiv_fixed_intMul hx a

/-- **The common fixed field of two incommensurate real translations is the constants.**
Two `ℚ`-independent, `ℝ`-dependent periods generate a non-discrete group, hence arbitrarily small
nonzero periods, and a global meromorphic germ with arbitrarily small periods is constant. -/
theorem exists_constant_of_two_realDependent_translations_fixed
    {α β : ℂ} (hQ : LinearIndependent ℚ ![α, β]) (hdep : ¬ LinearIndependent ℝ ![α, β])
    {z : meroField (Set.univ : Set ℂ)}
    (hα : addTranslationMeroEquiv α z = z) (hβ : addTranslationMeroEquiv β z = z) :
    ∃ c : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = z := by
  obtain ⟨p, hpmem, hpne, hpzero⟩ := exists_small_rankTwo_realDependent_periods ![α, β] hQ hdep
  have hgen : ∀ i : Fin 2, addTranslationMeroEquiv (![α, β] i) z = z := by
    intro i
    fin_cases i
    · simpa using hα
    · simpa using hβ
  obtain ⟨c, hc⟩ := exists_constant_of_small_translation_fixed z p hpzero hpne
    (fun n => addTranslationMeroEquiv_fixed_of_mem_intSpan ![α, β] hgen (hpmem n))
  exact ⟨c, hc⟩


/-! ## Exponentials with distinct frequencies -/

/-- The exponential character `z ↦ exp (μ z)` as a monoid homomorphism. -/
def expMonoidHom (mu : ℂ) : Multiplicative ℂ →* ℂ where
  toFun := fun z => Complex.exp (mu * Multiplicative.toAdd z)
  map_one' := by simp
  map_mul' := by
    intro x y
    show Complex.exp (mu * (Multiplicative.toAdd x + Multiplicative.toAdd y))
      = Complex.exp (mu * Multiplicative.toAdd x) * Complex.exp (mu * Multiplicative.toAdd y)
    rw [mul_add, Complex.exp_add]

theorem expMonoidHom_injective : Function.Injective expMonoidHom := by
  intro mu nu h
  by_contra hne
  have hd : mu - nu ≠ 0 := sub_ne_zero.mpr hne
  have hz := congrFun (congrArg (fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) h)
    (Multiplicative.ofAdd ((Real.pi : ℂ) * Complex.I / (mu - nu)))
  have hval : Complex.exp (mu * ((Real.pi : ℂ) * Complex.I / (mu - nu)))
      = Complex.exp (nu * ((Real.pi : ℂ) * Complex.I / (mu - nu))) := hz
  rw [Complex.exp_eq_exp_iff_exists_int] at hval
  obtain ⟨n, hn⟩ := hval
  have hsub : (mu - nu) * ((Real.pi : ℂ) * Complex.I / (mu - nu))
      = (Real.pi : ℂ) * Complex.I := by
    field_simp
  have hkey : (Real.pi : ℂ) * Complex.I = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hn - hsub
  have hpiI : ((Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have hzero : ((Real.pi : ℂ) * Complex.I) * (1 - (n : ℂ) * 2) = 0 := by
    linear_combination hkey
  have hone : (1 : ℂ) - (n : ℂ) * 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hpiI
  have hcast : (n : ℤ) * 2 = 1 := by
    have : (n : ℂ) * 2 = 1 := by linear_combination -hone
    exact_mod_cast this
  omega


/-- **Distinct frequencies give independent exponentials.**  A finite complex combination of
exponentials with pairwise distinct frequencies vanishes identically only when all coefficients
vanish. -/
theorem exp_coeff_eq_zero_of_sum_eq_zero {ι : Type*} (s : Finset ι) (mu : ι → ℂ)
    (hmu : Set.InjOn mu s) (g : ι → ℂ)
    (h : ∀ z : ℂ, ∑ i ∈ s, g i * Complex.exp (mu i * z) = 0) : ∀ i ∈ s, g i = 0 := by
  classical
  have hinj : Function.Injective (fun i : (s : Finset ι) => expMonoidHom (mu (i : ι))) := by
    intro i j hij
    exact Subtype.ext (hmu i.2 j.2 (expMonoidHom_injective hij))
  have hLI := (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).comp _ hinj
  rw [linearIndependent_iff'] at hLI
  have hsum : ∑ i ∈ (Finset.univ : Finset (s : Finset ι)), g (i : ι) •
      ((fun i : (s : Finset ι) =>
        ((expMonoidHom (mu (i : ι)) : Multiplicative ℂ →* ℂ) : Multiplicative ℂ → ℂ)) i) = 0 := by
    funext z
    have hz := h (Multiplicative.toAdd z)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    show ∑ x : (s : Finset ι), g (x : ι) * Complex.exp (mu (x : ι) * Multiplicative.toAdd z) = 0
    rw [Finset.sum_coe_sort s (fun i => g i * Complex.exp (mu i * Multiplicative.toAdd z))]
    exact hz
  intro i hi
  exact hLI Finset.univ (fun j => g (j : ι)) hsum ⟨i, hi⟩ (Finset.mem_univ _)

/-- Point evaluation of a global analytic germ, as a ring homomorphism. -/
def analyticEvalAt (z : ℂ) : analyticSubring (Set.univ : Set ℂ) →+* ℂ :=
  (univGermEval z).comp (Subring.subtype (analyticSubring (Set.univ : Set ℂ)))

@[simp] theorem analyticEvalAt_physicalExponentialAnalytic (z mu : ℂ) :
    analyticEvalAt z (physicalExponentialAnalytic mu) = Complex.exp (mu * z) := rfl

@[simp] theorem analyticEvalAt_constToAnalytic (z c : ℂ) :
    analyticEvalAt z (constToAnalytic Set.univ c) = c := rfl

/-- The same statement inside the global meromorphic field. -/
theorem physicalExponentialMero_coeff_eq_zero_of_sum_eq_zero {ι : Type*} (s : Finset ι)
    (mu : ι → ℂ) (hmu : Set.InjOn mu s) (g : ι → ℂ)
    (h : ∑ i ∈ s, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (g i) *
        physicalExponentialMero (mu i) = 0) :
    ∀ i ∈ s, g i = 0 := by
  classical
  set A : analyticSubring (Set.univ : Set ℂ) :=
    ∑ i ∈ s, constToAnalytic Set.univ (g i) * physicalExponentialAnalytic (mu i) with hA
  have hmapA : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) A = 0 := by
    rw [hA, map_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; rfl
  have hA0 : A = 0 :=
    IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (by simpa using hmapA)
  refine exp_coeff_eq_zero_of_sum_eq_zero s mu hmu g ?_
  intro z
  have hval := congrArg (analyticEvalAt z) hA0
  rw [hA, map_sum, map_zero] at hval
  rw [← hval]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; simp


/-! ## Two positive real periods with irrational ratio -/

theorem not_linearIndependent_real_ofReal_pair (a b : ℝ) :
    ¬ LinearIndependent ℝ ![(a : ℂ), (b : ℂ)] := by
  intro hind
  rcases eq_or_ne a 0 with ha | ha
  · have := (LinearIndependent.pair_iff.mp hind) 1 0 (by simp [ha])
    exact one_ne_zero this.1
  · have hcomb : b • (a : ℂ) + (-a) • (b : ℂ) = 0 := by
      show (b : ℂ) * (a : ℂ) + ((-a : ℝ) : ℂ) * (b : ℂ) = 0
      push_cast
      ring
    have := (LinearIndependent.pair_iff.mp hind) b (-a) hcomb
    exact ha (neg_eq_zero.mp this.2)

theorem linearIndependent_rat_ofReal_pair_of_irrational {a b : ℝ} (h : Irrational (a / b)) :
    LinearIndependent ℚ ![(a : ℂ), (b : ℂ)] := by
  have hb : b ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at h
    exact h ⟨0, by simp⟩
  refine LinearIndependent.pair_iff.mpr ?_
  intro p q hpq
  have hreal : (p : ℝ) * a + (q : ℝ) * b = 0 := by
    have : ((((p : ℝ) * a + (q : ℝ) * b : ℝ)) : ℂ) = 0 := by
      push_cast
      simpa [Rat.smul_def] using hpq
    exact_mod_cast this
  rcases eq_or_ne p 0 with hp | hp
  · refine ⟨hp, ?_⟩
    rw [hp] at hreal
    simp only [Rat.cast_zero, zero_mul, zero_add] at hreal
    have := (mul_eq_zero.mp hreal).resolve_right hb
    exact_mod_cast this
  · exfalso
    have hpR : (p : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hp
    have hdiv : a / b = ((-q / p : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith [hreal]
    exact h ⟨-q / p, hdiv.symm⟩

/-- **The common fixed field of two incommensurate real periods is the constants.** -/
theorem exists_constant_of_two_realPeriods_fixed {om1 om2 : ℝ}
    (h : Irrational (om1 / om2)) {z : meroField (Set.univ : Set ℂ)}
    (h1 : addTranslationMeroEquiv (om1 : ℂ) z = z)
    (h2 : addTranslationMeroEquiv (om2 : ℂ) z = z) :
    ∃ c : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = z :=
  exists_constant_of_two_realDependent_translations_fixed
    (linearIndependent_rat_ofReal_pair_of_irrational h)
    (not_linearIndependent_real_ofReal_pair om1 om2) h1 h2


/-! ## The two cylinder coordinates are algebraically independent -/

/-- Global analytic germs are determined by their point values. -/
theorem analyticSubring_ext {a b : analyticSubring (Set.univ : Set ℂ)}
    (h : ∀ z, analyticEvalAt z a = analyticEvalAt z b) : a = b :=
  Subtype.ext (univGerm_ext h)

@[simp] theorem physicalExponentialAnalytic_zero :
    physicalExponentialAnalytic 0 = 1 := by
  refine analyticSubring_ext fun z => ?_
  rw [analyticEvalAt_physicalExponentialAnalytic, map_one, zero_mul, Complex.exp_zero]

theorem physicalExponentialAnalytic_add (a b : ℂ) :
    physicalExponentialAnalytic (a + b)
      = physicalExponentialAnalytic a * physicalExponentialAnalytic b := by
  refine analyticSubring_ext fun z => ?_
  rw [map_mul, analyticEvalAt_physicalExponentialAnalytic,
    analyticEvalAt_physicalExponentialAnalytic, analyticEvalAt_physicalExponentialAnalytic,
    ← Complex.exp_add]
  ring_nf

@[simp] theorem physicalExponentialMero_zero :
    physicalExponentialMero 0 = 1 := by
  rw [physicalExponentialMero, physicalExponentialAnalytic_zero, map_one]

theorem physicalExponentialMero_add (a b : ℂ) :
    physicalExponentialMero (a + b)
      = physicalExponentialMero a * physicalExponentialMero b := by
  rw [physicalExponentialMero, physicalExponentialMero, physicalExponentialMero,
    physicalExponentialAnalytic_add, map_mul]

theorem physicalExponentialMero_pow (a : ℂ) (n : ℕ) :
    physicalExponentialMero a ^ n = physicalExponentialMero ((n : ℂ) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← physicalExponentialMero_add]
      congr 1
      push_cast
      ring


/-- The frequency of a monomial in two exponential coordinates. -/
def pairFrequency (l : Fin 2 → ℂ) (d : Fin 2 →₀ ℕ) : ℂ :=
  (d 0 : ℂ) * l 0 + (d 1 : ℂ) * l 1

theorem pairFrequency_injective {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) :
    Function.Injective (pairFrequency l) := by
  intro d e h
  set g : Fin 2 → ℚ := fun i => ((d i : ℤ) : ℚ) - ((e i : ℤ) : ℚ) with hg
  have hsum : ∑ i, g i • l i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [hg, Rat.smul_def]
    push_cast
    have hd := h
    rw [pairFrequency, pairFrequency] at hd
    linear_combination hd
  have hz := Fintype.linearIndependent_iff.mp hl g hsum
  refine Finsupp.ext fun i => ?_
  have hi := hz i
  rw [hg] at hi
  have : ((d i : ℤ) : ℚ) = ((e i : ℤ) : ℚ) := by linarith [hi]
  exact_mod_cast this

/-- **Two incommensurate exponential coordinates are algebraically independent.** -/
theorem algebraicIndependent_pair_physicalExponentialMero {l : Fin 2 → ℂ}
    (hl : LinearIndependent ℚ l) :
    AlgebraicIndependent ℂ (fun i : Fin 2 => physicalExponentialMero (l i)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  have hexpand : MvPolynomial.aeval (fun i : Fin 2 => physicalExponentialMero (l i)) P
      = ∑ d ∈ P.support, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P)
          * physicalExponentialMero (pairFrequency l d) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    rw [Fin.prod_univ_two, physicalExponentialMero_pow, physicalExponentialMero_pow,
      ← physicalExponentialMero_add]
    rfl
  rw [hexpand] at hP
  have hcoeff := physicalExponentialMero_coeff_eq_zero_of_sum_eq_zero P.support
    (pairFrequency l) (pairFrequency_injective hl).injOn
    (fun d => MvPolynomial.coeff d P) hP
  refine MvPolynomial.ext _ _ fun d => ?_
  by_cases hd : d ∈ P.support
  · simpa using hcoeff d hd
  · simpa using MvPolynomial.notMem_support_iff.mp hd


/-! ## The embedded cylinder coordinate field and its translation action -/

theorem transcendental_physicalExponentialMero {l : Fin 2 → ℂ}
    (hl : LinearIndependent ℚ l) (i : Fin 2) :
    Transcendental ℂ (physicalExponentialMero (l i)) :=
  (algebraicIndependent_pair_physicalExponentialMero hl).transcendental i

/-- The cylinder coordinate field `ℂ(u)` embedded in the global meromorphic field. -/
def cylinderEmbed {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (i : Fin 2) :
    RatFunc ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ) :=
  RatFunc.liftAlgHom (Polynomial.aeval (physicalExponentialMero (l i)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (transcendental_physicalExponentialMero hl i)))

theorem cylinderEmbed_injective {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (i : Fin 2) :
    Function.Injective (cylinderEmbed hl i) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp
    (transcendental_physicalExponentialMero hl i))


@[simp] theorem cylinderEmbed_X {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (i : Fin 2) :
    cylinderEmbed hl i (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
      = physicalExponentialMero (l i) := by
  rw [cylinderEmbed, show (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X / 1 by rw [div_one],
    show (1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) 1 from (map_one _).symm,
    RatFunc.liftAlgHom_apply_div]
  simp

theorem cylinderEmbed_polynomial {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (i : Fin 2)
    (p : Polynomial ℂ) :
    cylinderEmbed hl i (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = Polynomial.aeval (physicalExponentialMero (l i)) p := by
  rw [cylinderEmbed, show (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p / 1 by rw [div_one],
    show (1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) 1 from (map_one _).symm,
    RatFunc.liftAlgHom_apply_div]
  simp

/-- **Translation acts on the embedded cylinder coordinate field by dilation.**  Translating by
`tau` multiplies the coordinate `u = exp(l z)` by `exp(l tau)`, so it corresponds to the
multiplicative dilation `ratFuncScale (exp (l tau))` of `ℂ(X)`. -/
theorem addTranslationMeroEquiv_cylinderEmbed {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l)
    (i : Fin 2) (tau : ℂ) (y : RatFunc ℂ) :
    addTranslationMeroEquiv tau (cylinderEmbed hl i y)
      = cylinderEmbed hl i (ratFuncScale (Complex.exp (l i * tau)) (Complex.exp_ne_zero _) y) := by
  have hpoly : ∀ p : Polynomial ℂ,
      addTranslationMeroEquiv tau (Polynomial.aeval (physicalExponentialMero (l i)) p)
        = Polynomial.aeval (physicalExponentialMero (l i))
            (polyScale (Complex.exp (l i * tau)) p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        have h1 : Polynomial.aeval (physicalExponentialMero (l i)) (p + q)
            = Polynomial.aeval (physicalExponentialMero (l i)) p
              + Polynomial.aeval (physicalExponentialMero (l i)) q := map_add _ _ _
        have h2 : polyScale (Complex.exp (l i * tau)) (p + q)
            = polyScale (Complex.exp (l i * tau)) p + polyScale (Complex.exp (l i * tau)) q :=
          map_add _ _ _
        rw [h1, (addTranslationMeroEquiv tau).map_add, hp, hq, h2, map_add]
    | monomial n a =>
        rw [Polynomial.aeval_monomial, map_mul, map_pow,
          addTranslationMeroEquiv_algebraMap_complex,
          addTranslationMeroEquiv_physicalExponentialMero, polyScale_eq_comp]
        simp only [Polynomial.monomial_comp]
        rw [map_mul, Polynomial.aeval_C, map_pow, map_mul, Polynomial.aeval_C,
          Polynomial.aeval_X]
  refine RatFunc.induction_on (P := fun y => addTranslationMeroEquiv tau (cylinderEmbed hl i y)
    = cylinderEmbed hl i (ratFuncScale (Complex.exp (l i * tau))
        (Complex.exp_ne_zero _) y)) y ?_
  intro p q _
  rw [ratFuncScale_div, map_div₀, map_div₀, map_div₀]
  simp only [cylinderEmbed_polynomial, hpoly]


/-! ## The two-cylinder function field inside the meromorphic field -/

variable {l : Fin 2 → ℂ}

/-- The second cylinder coordinate is transcendental over the first cylinder's coordinate field:
the ring homomorphism evaluating a polynomial over `ℂ(u₁)` at `u₂` is injective. -/
theorem injective_eval₂_second_cylinder (hl : LinearIndependent ℚ l) :
    Function.Injective (Polynomial.eval₂RingHom (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
        meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1))) := by
  classical
  set u1 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 0) with hu1
  set u2 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 1) with hu2
  have hAI := algebraicIndependent_pair_physicalExponentialMero hl
  have hpolyInj : Function.Injective (Polynomial.aeval u1 : Polynomial ℂ →ₐ[ℂ] _) :=
    transcendental_iff_injective.mp (transcendental_physicalExponentialMero hl 0)
  -- the polynomial ring maps into the subalgebra generated by the first coordinate
  have hmem : ∀ p : Polynomial ℂ, Polynomial.aeval u1 p ∈
      Algebra.adjoin ℂ ((fun i : Fin 2 => physicalExponentialMero (l i)) '' {0}) := by
    intro p
    have himg : (fun i : Fin 2 => physicalExponentialMero (l i)) '' {0} = {u1} := by
      simp [hu1]
    rw [himg, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  letI : Algebra (Polynomial ℂ) (meroField (Set.univ : Set ℂ)) :=
    (Polynomial.aeval u1 : Polynomial ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ)).toRingHom.toAlgebra
  letI : Algebra (Polynomial ℂ)
      (Algebra.adjoin ℂ ((fun i : Fin 2 => physicalExponentialMero (l i)) '' {0})) :=
    ((Polynomial.aeval u1).codRestrict _ hmem).toAlgebra
  haveI : IsScalarTower (Polynomial ℂ)
      (Algebra.adjoin ℂ ((fun i : Fin 2 => physicalExponentialMero (l i)) '' {0}))
      (meroField (Set.univ : Set ℂ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinjBase : Function.Injective (algebraMap (Polynomial ℂ)
      (Algebra.adjoin ℂ ((fun i : Fin 2 => physicalExponentialMero (l i)) '' {0}))) := by
    intro p q h
    exact hpolyInj (congrArg Subtype.val h)
  have hTadj : Transcendental
      (Algebra.adjoin ℂ ((fun i : Fin 2 => physicalExponentialMero (l i)) '' {0})) u2 :=
    hAI.transcendental_adjoin (s := {0}) (i := 1) (by simp)
  have hTpoly : Transcendental (Polynomial ℂ) u2 := hTadj.restrictScalars hinjBase
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) := (cylinderEmbed hl 0).toAlgebra
  haveI : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    IsScalarTower.of_algebraMap_eq fun p => (cylinderEmbed_polynomial hl 0 p).symm
  have hTrat : Transcendental (RatFunc ℂ) u2 := by
    intro hcon
    exact hTpoly ((IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ)
      (meroField (Set.univ : Set ℂ))).mpr hcon)
  exact transcendental_iff_injective.mp hTrat


/-- The two-cylinder function field `ℂ(u₁)(u₂)` embedded in the global meromorphic field. -/
def twoCylinderEmbed (hl : LinearIndependent ℚ l) :
    RatFunc (RatFunc ℂ) →+* meroField (Set.univ : Set ℂ) :=
  RatFunc.liftRingHom
    (Polynomial.eval₂RingHom (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
        meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (injective_eval₂_second_cylinder hl))

theorem twoCylinderEmbed_injective (hl : LinearIndependent ℚ l) :
    Function.Injective (twoCylinderEmbed hl) :=
  RatFunc.liftRingHom_injective _ (injective_eval₂_second_cylinder hl)

theorem twoCylinderEmbed_div (hl : LinearIndependent ℚ l) (p q : Polynomial (RatFunc ℂ)) :
    twoCylinderEmbed hl (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p /
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) q)
      = Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
            meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1)) p /
        Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
            meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1)) q :=
  RatFunc.liftMonoidWithZeroHom_apply_div _
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (injective_eval₂_second_cylinder hl)) p q


/-- **Translation acts on the embedded two-cylinder field by dilating the second coordinate**,
whenever the first coordinate is a period of the translation. -/
theorem addTranslationMeroEquiv_twoCylinderEmbed (hl : LinearIndependent ℚ l) (tau : ℂ)
    (h1 : Complex.exp (l 0 * tau) = 1) (y : RatFunc (RatFunc ℂ)) :
    addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
      = twoCylinderEmbed hl
          (ratFuncScale (algebraMap ℂ (RatFunc ℂ) (Complex.exp (l 1 * tau)))
            (by simp [Complex.exp_ne_zero]) y) := by
  classical
  set s : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (Complex.exp (l 1 * tau)) with hs
  have hs0 : s ≠ 0 := by simp [hs, Complex.exp_ne_zero]
  set iota : RatFunc ℂ →+* meroField (Set.univ : Set ℂ) :=
    (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ)).toRingHom with hiota
  set u2 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 1) with hu2
  -- the coefficient field is fixed by the translation
  have hcoeff : ∀ c : RatFunc ℂ, addTranslationMeroEquiv tau (iota c) = iota c := by
    intro c
    rw [hiota]
    show addTranslationMeroEquiv tau (cylinderEmbed hl 0 c) = cylinderEmbed hl 0 c
    rw [addTranslationMeroEquiv_cylinderEmbed hl 0 tau c, ratFuncScale_of_eq_one _ h1]
  have hiotaS : iota s = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (Complex.exp (l 1 * tau)) := by
    rw [hs, hiota]
    exact (cylinderEmbed hl 0).commutes _
  have hpoly : ∀ p : Polynomial (RatFunc ℂ),
      addTranslationMeroEquiv tau (Polynomial.eval₂ iota u2 p)
        = Polynomial.eval₂ iota u2 (polyScale s p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [Polynomial.eval₂_add, (addTranslationMeroEquiv tau).map_add, hp, hq, map_add,
          Polynomial.eval₂_add]
    | monomial n c =>
        rw [Polynomial.eval₂_monomial, map_mul, map_pow, hcoeff,
          addTranslationMeroEquiv_physicalExponentialMero, polyScale_eq_comp]
        simp only [Polynomial.monomial_comp]
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, hiotaS]
  refine RatFunc.induction_on (P := fun y => addTranslationMeroEquiv tau (twoCylinderEmbed hl y)
    = twoCylinderEmbed hl (ratFuncScale s hs0 y)) y ?_
  intro p q _
  rw [ratFuncScale_div, twoCylinderEmbed_div, twoCylinderEmbed_div, map_div₀, hpoly, hpoly]

end

end GaloisForLFunctions.HTGeometry
