import GaloisForLFunctions.HTGeometry.RectangularKreinInertia
import GaloisForLFunctions.HTGeometry.UniversalConstraintOrientation
import GaloisForLFunctions.HTGeometry.UniversalOrientedHerglotz

/-!
# Universal prime-residue Krein--Hamming geometry

Finite sign flips are made at the actual prime-log poles of the fixed universal Herglotz source.
They are rational gauges of the same embedded differential field.  Their relative Pick defects are
rectangular factored Krein forms whose exact inertia recovers the directed Hamming geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial Matrix Complex
open scoped Differential BigOperators

noncomputable section

/-- The fixed positive prime weight of the universal source. -/
def universalPrimeWeight (p : Nat.Primes) : ℝ :=
  primeDyadicWeight (fun q => universalFacetOrbitGauge q) p

theorem universalPrimeWeight_pos (p : Nat.Primes) : 0 < universalPrimeWeight p :=
  primeDyadicWeight_pos _ p

/-- Flip the actual source residue at every prime in a finite chamber. -/
def universalPrimeOrientedHerglotz (J : Finset Nat.Primes) (z : ℂ) : ℂ :=
  primeLogHerglotz (fun q => universalFacetOrbitGauge q) z -
    2 * ∑ p ∈ J, (universalPrimeWeight p : ℂ) *
      ((primeLogSupport p : ℂ) - z)⁻¹

/-- The translated rational correction induced by a finite prime-residue chamber. -/
def primeFlipGaugeRatFunc (J : Finset Nat.Primes) (h : ℂ) : RatFunc ℂ :=
  ∑ p ∈ J, RatFunc.C ((-2 : ℂ) * (universalPrimeWeight p : ℂ)) *
    (RatFunc.C (primeLogSupport p : ℂ) - (RatFunc.X + RatFunc.C h))⁻¹

/-- The rational gauge on the universal palette induced by finite prime-residue flips. -/
def universalPrimeOrientedPaletteGauge (J : Finset Nat.Primes) :
    UniversalFacetOrbitIndex → RatFunc ℂ := fun q =>
  primeFlipGaugeRatFunc J (universalFacetOrbitShift q)

/-- The complete universal translated palette in a finite prime-residue chamber. -/
def universalFacetOrbitPrimeOrientedSource
    (J : Finset Nat.Primes) (q : UniversalFacetOrbitIndex) : upperEndMeroField :=
  universalFacetOrbitRationalGaugeSource (universalPrimeOrientedPaletteGauge J) q

/-- Every finite prime-residue chamber retains differential independence of the universal palette. -/
theorem universalFacetOrbitPrimeOrientedSource_differentialIndependent
    (J : Finset Nat.Primes) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (universalFacetOrbitPrimeOrientedSource J) := by
  simpa [universalFacetOrbitPrimeOrientedSource] using
    universalFacetOrbitRationalGaugeSource_differentialIndependent
      (universalPrimeOrientedPaletteGauge J)

/-- Every finite prime-residue chamber generates exactly the same embedded differential field. -/
theorem universalFacetOrbitPrimeOrientedSource_differentialAdjoin_eq
    (J : Finset Nat.Primes) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialAdjoin (RatFunc ℂ) (Set.range (universalFacetOrbitPrimeOrientedSource J)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge)) := by
  simpa [universalFacetOrbitPrimeOrientedSource] using
    universalFacetOrbitRationalGaugeSource_differentialAdjoin_eq
      (universalPrimeOrientedPaletteGauge J)

set_option synthInstance.maxHeartbeats 200000 in
/-- Every finite prime-residue chamber retains every finite localized Stanley--Reisner differential
matroid. -/
theorem universalFacetOrbitPrimeOriented_stanleyReisnerLaurentDifferentialMatroid
    (J : Finset Nat.Primes)
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      universalFacetOrbitPrimeOrientedSource J
        (finiteFacetOrbitUniversalIndex e facets q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  simpa [universalFacetOrbitPrimeOrientedSource] using
    universalFacetOrbitRationalGauge_stanleyReisnerLaurentDifferentialMatroid
      (universalPrimeOrientedPaletteGauge J) d facets N

/-! ## Exact prime-support Herglotz selection -/

/-- Delete one chosen source atom and all other finite flips; the result is regular at the chosen
prime-log pole. -/
def universalPrimeOrientedRegular
    (J : Finset Nat.Primes) (p : Nat.Primes) (z : ℂ) : ℂ :=
  primeLogTail (fun q => universalFacetOrbitGauge q) p z -
    2 * ∑ q ∈ J.erase p, (universalPrimeWeight q : ℂ) *
      ((primeLogSupport q : ℂ) - z)⁻¹

theorem continuousAt_universalPrimeOrientedRegular
    (J : Finset Nat.Primes) (p : Nat.Primes) :
    ContinuousAt (universalPrimeOrientedRegular J p) (primeLogSupport p : ℂ) := by
  apply ContinuousAt.sub
  · exact (differentiableAt_primeLogTail
      (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
      (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
        (universalFacetOrbitGauge.norm_coe_le_norm q)) p).continuousAt
  · apply ContinuousAt.const_mul
    let T := J.erase p
    change ContinuousAt (fun z : ℂ => ∑ q ∈ T,
      (universalPrimeWeight q : ℂ) * ((primeLogSupport q : ℂ) - z)⁻¹) _
    have hpT : p ∉ T := by simp [T]
    revert hpT
    induction T using Finset.induction_on with
    | empty =>
        intro hpT
        simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) _)
    | @insert q T hq ih =>
        intro hpInsert
        have hqp : q ≠ p := by
          intro h
          subst q
          exact hpInsert (by simp)
        have hpT : p ∉ T := by
          intro hp
          exact hpInsert (by simp [hp])
        have hterm : ContinuousAt (fun z : ℂ =>
            (universalPrimeWeight q : ℂ) * ((primeLogSupport q : ℂ) - z)⁻¹)
            (primeLogSupport p : ℂ) := by
          apply ContinuousAt.const_mul
          apply ContinuousAt.inv₀ (continuousAt_const.sub continuousAt_id)
          intro heq
          have hsupp : primeLogSupport q = primeLogSupport p := by
            exact Complex.ofReal_injective (sub_eq_zero.mp heq)
          exact hqp (primeLogSupport_injective hsupp)
        simpa [Finset.sum_insert hq] using hterm.add (ih hpT)

theorem universalPrimeOrientedHerglotz_eq_regular_sub_atom
    {J : Finset Nat.Primes} {p : Nat.Primes} (hpJ : p ∈ J) (z : ℂ) :
    universalPrimeOrientedHerglotz J z =
      universalPrimeOrientedRegular J p z -
        (universalPrimeWeight p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹ := by
  rw [universalPrimeOrientedHerglotz, universalPrimeOrientedRegular]
  have hsplit := Finset.sum_erase_add (s := J) (f := fun q =>
    (universalPrimeWeight q : ℂ) * ((primeLogSupport q : ℂ) - z)⁻¹) hpJ
  rw [← hsplit]
  have htail := primeLogHerglotz_add_polar_eq_tail
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) p z
  rw [show ((z - (primeLogSupport p : ℂ))⁻¹) =
      -(((primeLogSupport p : ℂ) - z)⁻¹) by rw [← inv_neg, neg_sub]] at htail
  simp only [universalPrimeWeight]
  linear_combination htail

/-- A negative Cauchy atom with any positive weight dominates a continuous background near its real
pole. -/
theorem exists_upper_im_neg_of_continuous_sub_weightedAtom
    (a c : ℝ) (hc : 0 < c) (g : ℂ → ℂ) (hg : ContinuousAt g (a : ℂ)) :
    ∃ z : ℂ, 0 < z.im ∧
      (g z - (c : ℂ) * ((a : ℂ) - z)⁻¹).im < 0 := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let h : ℂ → ℂ := fun z => (c : ℂ)⁻¹ * g z
  have hh : ContinuousAt h (a : ℂ) := hg.const_mul _
  obtain ⟨z, hz, hneg⟩ := exists_upper_im_neg_of_continuous_add_negativeAtom a h hh
  refine ⟨z, hz, ?_⟩
  have heq : g z - (c : ℂ) * ((a : ℂ) - z)⁻¹ =
      (c : ℂ) * (h z - ((a : ℂ) - z)⁻¹) := by
    dsimp [h]
    field_simp
  rw [heq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hc hneg

theorem universalPrimeOrientedHerglotz_not_nonneg_of_nonempty
    (J : Finset Nat.Primes) (hJ : J.Nonempty) :
    ¬ ∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im := by
  obtain ⟨p, hpJ⟩ := hJ
  obtain ⟨z, hz, hneg⟩ := exists_upper_im_neg_of_continuous_sub_weightedAtom
    (primeLogSupport p) (universalPrimeWeight p) (universalPrimeWeight_pos p)
    (universalPrimeOrientedRegular J p)
    (continuousAt_universalPrimeOrientedRegular J p)
  intro hnonneg
  have h := hnonneg z hz
  rw [universalPrimeOrientedHerglotz_eq_regular_sub_atom hpJ z] at h
  exact (not_lt_of_ge h) hneg

/-- The finite prime-residue chamber is Herglotz exactly at its all-positive vertex. -/
theorem universalPrimeOrientedHerglotz_nonneg_iff_empty (J : Finset Nat.Primes) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im) ↔ J = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact universalPrimeOrientedHerglotz_not_nonneg_of_nonempty J
      (Finset.nonempty_iff_ne_empty.mpr hne) h
  · rintro rfl z hz
    simpa [universalPrimeOrientedHerglotz] using
      universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz

/-! ## Exact finite Krein signature on canonical response probes -/

/-- Canonical unit-height upper-half-plane probes.  Their real coordinates enumerate the finite
response channels, while the fixed positive imaginary part keeps every probe away from every real
prime-log pole. -/
def primeKreinProbeNode (N : ℕ) (j : Fin N) : ℂ :=
  ((j : ℕ) : ℂ) + Complex.I

theorem primeKreinProbeNode_injective (N : ℕ) :
    Function.Injective (primeKreinProbeNode N) := by
  intro i j hij
  have hre := congrArg Complex.re hij
  simp [primeKreinProbeNode] at hre
  apply Fin.ext
  exact_mod_cast hre

theorem primeLogSupport_ne_primeKreinProbeNode
    (p : Nat.Primes) (N : ℕ) (j : Fin N) :
    (primeLogSupport p : ℂ) ≠ primeKreinProbeNode N j := by
  intro h
  have him := congrArg Complex.im h
  simp [primeKreinProbeNode] at him

/-- A prime response channel sampled on a finite upper-half-plane packet.  The square-root weight
puts its outer product at the physical intensity `2 * universalPrimeWeight p`. -/
def universalPrimeKreinFeature {k N : ℕ}
    (p : Fin k → Nat.Primes) (z : Fin N → ℂ) (i : Fin k) : Fin N → ℂ :=
  (Real.sqrt (2 * universalPrimeWeight (p i)) : ℂ) •
    fun j => ((primeLogSupport (p i) : ℂ) - z j)⁻¹

/-- The signed response Gram for `kp` positive and `kn` negative prime channels on the canonical
unit-height probe packet. -/
def universalPrimeKreinProbeForm {kp kn : ℕ}
    (positivePrime : Fin kp → Nat.Primes)
    (negativePrime : Fin kn → Nat.Primes) :
    Matrix (Fin (kp + kn)) (Fin (kp + kn)) ℂ :=
  rectangularKreinForm
    (universalPrimeKreinFeature positivePrime (primeKreinProbeNode (kp + kn)))
    (universalPrimeKreinFeature negativePrime (primeKreinProbeNode (kp + kn)))

/-- Distinct positive and negative prime channels give a linearly independent combined response
packet on the canonical probes.  This is the source-side controllability/minimality input that
makes the Krein signature sharp rather than merely bounded. -/
theorem universalPrimeKreinProbe_combined_linearIndependent {kp kn : ℕ}
    (positivePrime : Fin kp → Nat.Primes)
    (negativePrime : Fin kn → Nat.Primes)
    (hprime : Function.Injective (Sum.elim positivePrime negativePrime)) :
    LinearIndependent ℂ
      (Sum.elim
        (universalPrimeKreinFeature positivePrime (primeKreinProbeNode (kp + kn)))
        (universalPrimeKreinFeature negativePrime (primeKreinProbeNode (kp + kn)))) := by
  let e : Fin kp ⊕ Fin kn ≃ Fin (kp + kn) := finSumFinEquiv
  let allPrime : Fin (kp + kn) → Nat.Primes :=
    fun i => Sum.elim positivePrime negativePrime (e.symm i)
  let raw : Fin (kp + kn) → (Fin (kp + kn) → ℂ) :=
    fun i j => ((primeLogSupport (allPrime i) : ℂ) -
      primeKreinProbeNode (kp + kn) j)⁻¹
  have hallPrime : Function.Injective allPrime :=
    hprime.comp e.symm.injective
  have hpole : Function.Injective
      (fun i => (primeLogSupport (allPrime i) : ℂ)) := by
    intro i j hij
    apply hallPrime
    apply primeLogSupport_injective
    exact Complex.ofReal_injective hij
  have hraw : LinearIndependent ℂ raw := by
    simpa [raw] using
      cauchy_linearIndependent
        (fun i => (primeLogSupport (allPrime i) : ℂ))
        (primeKreinProbeNode (kp + kn)) hpole
        (primeKreinProbeNode_injective (kp + kn))
        (fun i j => primeLogSupport_ne_primeKreinProbeNode (allPrime i) (kp + kn) j)
  have hreindexed : LinearIndependent ℂ (fun s => raw (e s)) :=
    hraw.comp e e.injective
  let scale : Fin kp ⊕ Fin kn → ℂ := fun s =>
    (Real.sqrt (2 * universalPrimeWeight (Sum.elim positivePrime negativePrime s)) : ℂ)
  have hscale : ∀ s, scale s ≠ 0 := by
    intro s
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.2
      (mul_pos (by norm_num) (universalPrimeWeight_pos _))).ne'
  have hscaled := linearIndependent_smul_nonzero
    (fun s => raw (e s)) scale hreindexed hscale
  convert hscaled using 1 with s
  cases s <;>
    simp [universalPrimeKreinFeature, scale, raw, allPrime, e]

/-- **Exact negative-channel count.**  The signed prime-response Gram has negative inertia exactly
`kn`: every negative-definite subspace has dimension at most `kn`, and one of dimension `kn`
exists.  No arbitrary probe or surjectivity hypothesis remains. -/
theorem universalPrimeKreinProbe_exact_neg_inertia {kp kn : ℕ}
    (positivePrime : Fin kp → Nat.Primes)
    (negativePrime : Fin kn → Nat.Primes)
    (hprime : Function.Injective (Sum.elim positivePrime negativePrime)) :
    (∀ W : Submodule ℂ (Fin (kp + kn) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            (universalPrimeKreinProbeForm positivePrime negativePrime).mulVec y).re < 0) →
        Module.finrank ℂ W ≤ kn) ∧
      (∃ W : Submodule ℂ (Fin (kp + kn) → ℂ), Module.finrank ℂ W = kn ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            (universalPrimeKreinProbeForm positivePrime negativePrime).mulVec y).re < 0) := by
  let w := universalPrimeKreinFeature positivePrime (primeKreinProbeNode (kp + kn))
  let u := universalPrimeKreinFeature negativePrime (primeKreinProbeNode (kp + kn))
  have hlinear : LinearIndependent ℂ (Sum.elim w u) := by
    simpa only [w, u] using
      universalPrimeKreinProbe_combined_linearIndependent
        positivePrime negativePrime hprime
  have hsurjective := rectangular_eval_surjective_of_linearIndependent w u hlinear
  simpa only [universalPrimeKreinProbeForm, w, u] using
    rectangular_exact_neg_inertia w u hsurjective

/-- **Exact positive-channel count.**  On the same canonical response packet, the positive inertia
is exactly `kp`.  Together with the negative theorem, the intrinsic Krein signature recovers both
directed channel counts. -/
theorem universalPrimeKreinProbe_exact_pos_inertia {kp kn : ℕ}
    (positivePrime : Fin kp → Nat.Primes)
    (negativePrime : Fin kn → Nat.Primes)
    (hprime : Function.Injective (Sum.elim positivePrime negativePrime)) :
    (∀ W : Submodule ℂ (Fin (kp + kn) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ
            (universalPrimeKreinProbeForm positivePrime negativePrime).mulVec y).re) →
        Module.finrank ℂ W ≤ kp) ∧
      (∃ W : Submodule ℂ (Fin (kp + kn) → ℂ), Module.finrank ℂ W = kp ∧
        ∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ
            (universalPrimeKreinProbeForm positivePrime negativePrime).mulVec y).re) := by
  let w := universalPrimeKreinFeature positivePrime (primeKreinProbeNode (kp + kn))
  let u := universalPrimeKreinFeature negativePrime (primeKreinProbeNode (kp + kn))
  have hlinear : LinearIndependent ℂ (Sum.elim w u) := by
    simpa only [w, u] using
      universalPrimeKreinProbe_combined_linearIndependent
        positivePrime negativePrime hprime
  have hsurjective := rectangular_eval_surjective_of_linearIndependent w u hlinear
  simpa only [universalPrimeKreinProbeForm, w, u] using
    rectangular_exact_pos_inertia w u hsurjective

end


end GaloisForLFunctions.HTGeometry
