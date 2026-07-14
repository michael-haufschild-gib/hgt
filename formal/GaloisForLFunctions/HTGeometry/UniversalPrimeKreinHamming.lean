import GaloisForLFunctions.HTGeometry.RectangularKreinInertia
import GaloisForLFunctions.HTGeometry.UniversalConstraintOrientation
import GaloisForLFunctions.HTGeometry.UniversalOrientedHerglotz

/-!
# Universal prime-residue Krein--Hamming geometry

Finite sign flips are made at the actual prime-log poles of the fixed universal Herglotz source.
They are rational gauges of the same embedded differential field.  Their relative Pick defects are
rectangular factored Krein forms whose exact inertia recovers the directed Hamming geometry.
The same Hamming distance is recovered independently as the normalized sum-of-squares master
energy of binary dephasing charges on the two chambers.
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
  have heq :
      Sum.elim
          (universalPrimeKreinFeature positivePrime (primeKreinProbeNode (kp + kn)))
          (universalPrimeKreinFeature negativePrime (primeKreinProbeNode (kp + kn))) =
        fun s => scale s • (fun t => raw (e t)) s := by
    funext s
    cases s <;>
      simp [universalPrimeKreinFeature, scale, raw, allPrime, e]
  rw [heq]
  exact hscaled

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

/-! ## Chamber dephasing master and exact finite-set interface -/

/-- The canonical enumeration of a finite prime packet. -/
def finsetPrimeEnumeration (S : Finset Nat.Primes) : Fin S.card → Nat.Primes :=
  fun i => (S.equivFin.symm i : Nat.Primes)

theorem finsetPrimeEnumeration_mem (S : Finset Nat.Primes) (i : Fin S.card) :
    finsetPrimeEnumeration S i ∈ S := by
  exact (S.equivFin.symm i).property

theorem finsetPrimeEnumeration_injective (S : Finset Nat.Primes) :
    Function.Injective (finsetPrimeEnumeration S) := by
  intro i j hij
  apply S.equivFin.symm.injective
  apply Subtype.ext
  simpa [finsetPrimeEnumeration] using hij

/-- The positive packet `L \ J` and negative packet `J \ L` are jointly injective. -/
theorem primeChamberDifferenceEnumeration_injective
    (J L : Finset Nat.Primes) :
    Function.Injective
      (Sum.elim (finsetPrimeEnumeration (L \ J))
        (finsetPrimeEnumeration (J \ L))) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (finsetPrimeEnumeration_injective (L \ J) hab)
      | inr j =>
          have hi := Finset.mem_sdiff.mp (finsetPrimeEnumeration_mem (L \ J) i)
          have hj := Finset.mem_sdiff.mp (finsetPrimeEnumeration_mem (J \ L) j)
          have hab' : finsetPrimeEnumeration (L \ J) i =
              finsetPrimeEnumeration (J \ L) j := by
            simpa using hab
          exact (hi.2 (hab'.symm ▸ hj.1)).elim
  | inr i =>
      cases b with
      | inl j =>
          have hi := Finset.mem_sdiff.mp (finsetPrimeEnumeration_mem (J \ L) i)
          have hj := Finset.mem_sdiff.mp (finsetPrimeEnumeration_mem (L \ J) j)
          have hab' : finsetPrimeEnumeration (J \ L) i =
              finsetPrimeEnumeration (L \ J) j := by
            simpa using hab
          exact (hj.2 (hab' ▸ hi.1)).elim
      | inr j =>
          exact congrArg Sum.inr (finsetPrimeEnumeration_injective (J \ L) hab)

/-- The relative prime-response form for the ordered chamber pair `(J,L)`: channels in `L \ J`
are positive and channels in `J \ L` are negative. -/
def universalPrimeChamberRelativeKreinProbeForm
    (J L : Finset Nat.Primes) :
    Matrix (Fin ((L \ J).card + (J \ L).card))
      (Fin ((L \ J).card + (J \ L).card)) ℂ :=
  universalPrimeKreinProbeForm
    (finsetPrimeEnumeration (L \ J)) (finsetPrimeEnumeration (J \ L))

/-- The relative chamber form has negative inertia exactly `#(J \ L)`. -/
theorem universalPrimeChamberRelativeKreinProbe_exact_neg_inertia
    (J L : Finset Nat.Primes) :
    (∀ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            (universalPrimeChamberRelativeKreinProbeForm J L).mulVec y).re < 0) →
        Module.finrank ℂ W ≤ (J \ L).card) ∧
      (∃ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        Module.finrank ℂ W = (J \ L).card ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ
            (universalPrimeChamberRelativeKreinProbeForm J L).mulVec y).re < 0) := by
  simpa only [universalPrimeChamberRelativeKreinProbeForm] using
    universalPrimeKreinProbe_exact_neg_inertia
      (finsetPrimeEnumeration (L \ J)) (finsetPrimeEnumeration (J \ L))
      (primeChamberDifferenceEnumeration_injective J L)

/-- The relative chamber form has positive inertia exactly `#(L \ J)`. -/
theorem universalPrimeChamberRelativeKreinProbe_exact_pos_inertia
    (J L : Finset Nat.Primes) :
    (∀ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ
            (universalPrimeChamberRelativeKreinProbeForm J L).mulVec y).re) →
        Module.finrank ℂ W ≤ (L \ J).card) ∧
      (∃ W : Submodule ℂ (Fin ((L \ J).card + (J \ L).card) → ℂ),
        Module.finrank ℂ W = (L \ J).card ∧
        ∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ
            (universalPrimeChamberRelativeKreinProbeForm J L).mulVec y).re) := by
  simpa only [universalPrimeChamberRelativeKreinProbeForm] using
    universalPrimeKreinProbe_exact_pos_inertia
      (finsetPrimeEnumeration (L \ J)) (finsetPrimeEnumeration (J \ L))
      (primeChamberDifferenceEnumeration_injective J L)

/-- The undirected chamber support, with the order chosen to match positive then negative Krein
channels. -/
def primeChamberSymmetricDifference
    (J L : Finset Nat.Primes) : Finset Nat.Primes :=
  (L \ J) ∪ (J \ L)

/-- The Hamming distance between two finite prime-residue chambers. -/
def primeChamberHammingDistance (J L : Finset Nat.Primes) : ℕ :=
  (L \ J).card + (J \ L).card

theorem primeChamberSymmetricDifference_card (J L : Finset Nat.Primes) :
    (primeChamberSymmetricDifference J L).card = primeChamberHammingDistance J L := by
  have hdis : Disjoint (L \ J) (J \ L) := by
    rw [Finset.disjoint_left]
    intro p hpLJ hpJL
    exact (Finset.mem_sdiff.mp hpLJ).2 (Finset.mem_sdiff.mp hpJL).1
  rw [primeChamberSymmetricDifference, Finset.card_union_of_disjoint hdis,
    primeChamberHammingDistance]

theorem primeChamberHammingDistance_eq_zero_iff (J L : Finset Nat.Primes) :
    primeChamberHammingDistance J L = 0 ↔ J = L := by
  constructor
  · intro h
    have hparts : (L \ J).card = 0 ∧ (J \ L).card = 0 := by
      exact Nat.add_eq_zero_iff.mp h
    have hLJ : L ⊆ J :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hparts.1)
    have hJL : J ⊆ L :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hparts.2)
    exact Finset.Subset.antisymm hJL hLJ
  · rintro rfl
    simp [primeChamberHammingDistance]

/-- The binary `Z`-charge of a prime in a residue chamber. -/
def primeChamberDephasingCharge (J : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  if p ∈ J then -1 else 1

/-- Every changed prime contributes the same squared charge gap `4`. -/
theorem primeChamberDephasingCharge_gap_sq
    (J L : Finset Nat.Primes) {p : Nat.Primes}
    (hp : p ∈ primeChamberSymmetricDifference J L) :
    (primeChamberDephasingCharge J p - primeChamberDephasingCharge L p) ^ 2 = 4 := by
  rw [primeChamberSymmetricDifference, Finset.mem_union] at hp
  rcases hp with hp | hp
  · have hpLJ := Finset.mem_sdiff.mp hp
    norm_num [primeChamberDephasingCharge, hpLJ.1, hpLJ.2]
  · have hpJL := Finset.mem_sdiff.mp hp
    norm_num [primeChamberDephasingCharge, hpJL.1, hpJL.2]

/-- The normalized independent-dephasing master energy of the coherence `|J><L|`.  The factor
`1/4` is the Pauli-`Z` normalization for which one changed binary charge has unit rate. -/
def primeChamberDephasingMasterEnergy (J L : Finset Nat.Primes) : ℝ :=
  (1 / 4 : ℝ) * ∑ p ∈ primeChamberSymmetricDifference J L,
    (primeChamberDephasingCharge J p - primeChamberDephasingCharge L p) ^ 2

/-- **Dephasing--Hamming identity.**  The static positive master energy is exactly the chamber
Hamming distance, hence also the sum of the exact positive and negative Krein channel counts. -/
theorem primeChamberDephasingMasterEnergy_eq_hamming
    (J L : Finset Nat.Primes) :
    primeChamberDephasingMasterEnergy J L = (primeChamberHammingDistance J L : ℝ) := by
  rw [primeChamberDephasingMasterEnergy]
  calc
    (1 / 4 : ℝ) * ∑ p ∈ primeChamberSymmetricDifference J L,
        (primeChamberDephasingCharge J p - primeChamberDephasingCharge L p) ^ 2 =
        (1 / 4 : ℝ) * ∑ _p ∈ primeChamberSymmetricDifference J L, (4 : ℝ) := by
          congr 1
          exact Finset.sum_congr rfl fun p hp =>
            primeChamberDephasingCharge_gap_sq J L hp
    _ = ((primeChamberSymmetricDifference J L).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (primeChamberHammingDistance J L : ℝ) := by
      rw [primeChamberSymmetricDifference_card]

/-- The independent-dephasing master has zero energy exactly on diagonal chamber coherences. -/
theorem primeChamberDephasingMasterEnergy_eq_zero_iff
    (J L : Finset Nat.Primes) :
    primeChamberDephasingMasterEnergy J L = 0 ↔ J = L := by
  rw [primeChamberDephasingMasterEnergy_eq_hamming]
  simpa using primeChamberHammingDistance_eq_zero_iff J L

/-- **Constraint discharge at the positive chamber.**  For a finite residue orientation, the
global Herglotz positivity condition is equivalent to vanishing of one positive dephasing master
energy against the all-positive chamber. -/
theorem universalPrimeOrientedHerglotz_nonneg_iff_dephasingMasterEnergy_eq_zero
    (J : Finset Nat.Primes) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im) ↔
      primeChamberDephasingMasterEnergy J ∅ = 0 := by
  rw [universalPrimeOrientedHerglotz_nonneg_iff_empty,
    primeChamberDephasingMasterEnergy_eq_zero_iff]

end


end GaloisForLFunctions.HTGeometry
