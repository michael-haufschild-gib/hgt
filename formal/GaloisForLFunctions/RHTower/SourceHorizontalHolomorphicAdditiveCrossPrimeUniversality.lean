import GaloisForLFunctions.RHTower.PrimeExponentialHolomorphicDeterminingSourceImage
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticContinuousJets
import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicPrimeLogZeroCondensation
import GaloisForLFunctions.RHTower.RouteRReciprocalLogFisherEntranceWall
import GaloisForLFunctions.RHTower.XiOrderedPrimeDeterminantNormalForm
import GaloisForLFunctions.HTGeometry.AnderssonLemmaOne
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor

/-!
# Additive cross-prime determinant universality for the holomorphic SC reservoir

Finite Fisher-deconvolved prime Bockstein sums are dense among odd entire functions in the
compact-open topology. Consequently, determinants of the additive two-port matrices

\`\`\`
[[1, O_a(z)], [-O_b(z), 1]]
\`\`\`

are dense among every entire even function normalized by \`F(0) = 1\`. In particular they
converge locally uniformly to normalized centered Xi. Thus unrestricted additive cross-prime
coupling is universal and cannot discriminate RH; any surviving SC route must impose additional
arithmetic structure on admissible coefficients or couplings.

No RH assumption, zero-location input, numerical computation, or nonstandard axiom is used.
-/

open Complex Filter Set TopologicalSpace Topology

namespace RHTower

noncomputable section

def univSubtypeHomeomorph : (Set.univ : Set ℂ) ≃ₜ ℂ where
  toEquiv := Equiv.Set.univ ℂ
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

def univContinuousMapHomeomorph : C((Set.univ : Set ℂ), ℂ) ≃ₜ C(ℂ, ℂ) :=
  univSubtypeHomeomorph.arrowCongr (Homeomorph.refl ℂ)

@[simp] theorem univContinuousMapHomeomorph_apply
    (f : C((Set.univ : Set ℂ), ℂ)) (z : ℂ) :
    univContinuousMapHomeomorph f z = f ⟨z, Set.mem_univ z⟩ :=
  rfl

@[simp] theorem univContinuousMapHomeomorph_symm_apply
    (F : C(ℂ, ℂ)) (z : (Set.univ : Set ℂ)) :
    univContinuousMapHomeomorph.symm F z = F z :=
  rfl

theorem mem_holoOn_univ_iff_differentiable_transport
    (f : C((Set.univ : Set ℂ), ℂ)) :
    f ∈ HTGeometry.holoOn Set.univ ↔
      Differentiable ℂ (univContinuousMapHomeomorph f) := by
  constructor
  · rintro ⟨F, hF, hf⟩
    have heq : (univContinuousMapHomeomorph f : ℂ → ℂ) = F := by
      funext z
      exact hf ⟨z, Set.mem_univ z⟩
    rw [heq]
    simpa only [differentiableOn_univ] using hF
  · intro hf
    refine ⟨(univContinuousMapHomeomorph f : ℂ → ℂ), hf.differentiableOn, ?_⟩
    intro z
    rfl

def holoOnUnivHomeomorphDeninger :
    HTGeometry.holoOn Set.univ ≃ₜ DeningerCompactOpenEntire :=
  univContinuousMapHomeomorph.subtype
    mem_holoOn_univ_iff_differentiable_transport

@[simp] theorem holoOnUnivHomeomorphDeninger_apply
    (f : HTGeometry.holoOn Set.univ) (z : ℂ) :
    holoOnUnivHomeomorphDeninger f z =
      (f : C((Set.univ : Set ℂ), ℂ)) ⟨z, Set.mem_univ z⟩ :=
  rfl

def deningerPrimeExponentialCoefficientMap
    (a : Nat.Primes →₀ ℂ) : DeningerCompactOpenEntire :=
  holoOnUnivHomeomorphDeninger
    (primeExponentialCoefficientMap Set.univ a)

theorem exists_deningerPrimeExponentialCoefficientMap_tendsto
    (F : DeningerCompactOpenEntire) :
    ∃ a : ℕ → (Nat.Primes →₀ ℂ),
      Tendsto (fun n => deningerPrimeExponentialCoefficientMap (a n))
        atTop (𝓝 F) := by
  let f : HTGeometry.holoOn Set.univ :=
    holoOnUnivHomeomorphDeninger.symm F
  have hfClosure :
      f ∈ closure
        (LinearMap.range
          (primeExponentialCoefficientMap Set.univ) :
            Set (HTGeometry.holoOn Set.univ)) := by
    change f ∈
      (LinearMap.range
        (primeExponentialCoefficientMap Set.univ)).topologicalClosure
    rw [topologicalClosure_range_primeExponentialCoefficientMap_eq_top
      isOpen_univ convex_univ]
    exact Submodule.mem_top
  have hFClosure : F ∈ closure (Set.range deningerPrimeExponentialCoefficientMap) := by
    have hmapped := map_mem_closure
      holoOnUnivHomeomorphDeninger.continuous hfClosure
      (t := Set.range deningerPrimeExponentialCoefficientMap) (by
        rintro g ⟨a, rfl⟩
        exact ⟨a, rfl⟩)
    simpa [f] using hmapped
  obtain ⟨u, huRange, huTend⟩ :=
    mem_closure_iff_seq_limit.mp hFClosure
  choose a ha using huRange
  refine ⟨a, ?_⟩
  simpa only [ha] using huTend

private def complexNegContinuousMap : C(ℂ, ℂ) :=
  ⟨fun z => -z, continuous_neg⟩

def deningerCompactOpenNegPrecomp :
    DeningerCompactOpenEntire →L[ℂ] DeningerCompactOpenEntire where
  toFun F :=
    ⟨(F.1 : C(ℂ, ℂ)).comp complexNegContinuousMap,
      F.2.comp (fun _ => differentiableAt_id.neg)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply Continuous.subtype_mk
    exact (ContinuousMap.continuous_precomp complexNegContinuousMap).comp
      continuous_subtype_val

@[simp] theorem deningerCompactOpenNegPrecomp_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenNegPrecomp F z = F (-z) :=
  rfl

def deningerCompactOpenOddDifference :
    DeningerCompactOpenEntire →L[ℂ] DeningerCompactOpenEntire where
  toFun F := F - deningerCompactOpenNegPrecomp F
  map_add' F G := by
    ext z
    simp
    ring
  map_smul' c F := by
    ext z
    simp
    ring
  cont := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub
      (continuous_subtype_val.comp deningerCompactOpenNegPrecomp.continuous)

@[simp] theorem deningerCompactOpenOddDifference_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenOddDifference F z = F z - F (-z) :=
  rfl

def deningerOddPrimeExponentialSum
    (a : Nat.Primes →₀ ℂ) : DeningerCompactOpenEntire :=
  deningerCompactOpenOddDifference
    (deningerPrimeExponentialCoefficientMap a)

theorem exists_deningerOddPrimeExponentialSum_tendsto_of_odd
    (F : DeningerCompactOpenEntire) (hodd : ∀ z, F (-z) = -F z) :
    ∃ a : ℕ → (Nat.Primes →₀ ℂ),
      Tendsto (fun n => deningerOddPrimeExponentialSum (a n))
        atTop (𝓝 F) := by
  obtain ⟨a, ha⟩ :=
    exists_deningerPrimeExponentialCoefficientMap_tendsto
      ((2 : ℂ)⁻¹ • F)
  refine ⟨a, ?_⟩
  have hmap := deningerCompactOpenOddDifference.continuous.continuousAt.tendsto.comp ha
  have htarget :
      deningerCompactOpenOddDifference ((2 : ℂ)⁻¹ • F) = F := by
    ext z
    change (2 : ℂ)⁻¹ * F z - (2 : ℂ)⁻¹ * F (-z) = F z
    rw [hodd]
    ring
  change Tendsto
    (deningerCompactOpenOddDifference ∘
      fun n => deningerPrimeExponentialCoefficientMap (a n))
    atTop (𝓝 F)
  rw [← htarget]
  exact hmap

theorem primeExponentialCoefficientMap_apply_sum
    (a : Nat.Primes →₀ ℂ) (z : ℂ) :
    ((primeExponentialCoefficientMap Set.univ a :
      HTGeometry.holoOn Set.univ) : C((Set.univ : Set ℂ), ℂ))
        ⟨z, Set.mem_univ z⟩ =
      a.sum fun p c => c * primeExponential p z := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | @single_add p c a hp hc ih =>
      rw [map_add]
      rw [Finsupp.sum_add_index (by intros; simp) (by intros; ring)]
      rw [Finsupp.sum_single_index (by simp)]
      change
        (((primeExponentialCoefficientMap Set.univ
            (Finsupp.single p c) : HTGeometry.holoOn Set.univ) :
              C((Set.univ : Set ℂ), ℂ)) ⟨z, Set.mem_univ z⟩) +
          (((primeExponentialCoefficientMap Set.univ a :
              HTGeometry.holoOn Set.univ) :
                C((Set.univ : Set ℂ), ℂ)) ⟨z, Set.mem_univ z⟩) =
            c * primeExponential p z +
              a.sum fun p c => c * primeExponential p z
      rw [ih]
      rw [primeExponentialCoefficientMap_single,
        ← complex_smul_primeExponentialOn]
      rfl

theorem deningerPrimeExponentialCoefficientMap_apply_sum
    (a : Nat.Primes →₀ ℂ) (z : ℂ) :
    deningerPrimeExponentialCoefficientMap a z =
      a.sum fun p c => c * primeExponential p z := by
  exact primeExponentialCoefficientMap_apply_sum a z

def fisherDeconvolvedBocksteinSum
    (a : Nat.Primes →₀ ℂ) (z : ℂ) : ℂ :=
  a.sum fun p c =>
    (c / (primeActivationOccupancyFisherDensity p : ℂ)) *
      preDivisorHolomorphicPrimeBockstein z p

theorem fisherDeconvolvedBocksteinAtom_eq_oddPrimeExponential
    (p : Nat.Primes) (c z : ℂ) :
    (c / (primeActivationOccupancyFisherDensity p : ℂ)) *
        preDivisorHolomorphicPrimeBockstein z p =
      c * primeExponential p z - c * primeExponential p (-z) := by
  have hF : (primeActivationOccupancyFisherDensity p : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (primeActivationOccupancyFisherDensity_pos p).ne'
  unfold preDivisorHolomorphicPrimeBockstein primeExponential
  let L : ℂ := (Real.log ((p : ℕ) : ℝ) : ℂ)
  let Fp : ℂ := (primeActivationOccupancyFisherDensity p : ℂ)
  have hFp : Fp ≠ 0 := hF
  change
    (c / Fp) * (Fp * (Complex.exp (-(L * z)) - Complex.exp (L * z))) =
      c * Complex.exp (-L * z) - c * Complex.exp (-L * -z)
  have hminus : -L * z = -(L * z) := by ring
  have href : -L * -z = L * z := by ring
  rw [hminus, href]
  rw [div_eq_mul_inv]
  calc
    c * Fp⁻¹ * (Fp *
        (Complex.exp (-(L * z)) - Complex.exp (L * z))) =
      c * (Fp⁻¹ * Fp) *
        (Complex.exp (-(L * z)) - Complex.exp (L * z)) := by ring
    _ = c * Complex.exp (-(L * z)) - c * Complex.exp (L * z) := by
      rw [inv_mul_cancel₀ hFp]
      ring

theorem fisherDeconvolvedBocksteinSum_eq_oddPrimeExponentialSum
    (a : Nat.Primes →₀ ℂ) (z : ℂ) :
    fisherDeconvolvedBocksteinSum a z =
      deningerOddPrimeExponentialSum a z := by
  classical
  rw [fisherDeconvolvedBocksteinSum,
    deningerOddPrimeExponentialSum,
    deningerCompactOpenOddDifference_apply,
    deningerPrimeExponentialCoefficientMap_apply_sum,
    deningerPrimeExponentialCoefficientMap_apply_sum,
    ← Finsupp.sum_sub]
  apply Finsupp.sum_congr
  intro p hp
  exact fisherDeconvolvedBocksteinAtom_eq_oddPrimeExponential p (a p) z

def deningerCompactOpenCoordinate : DeningerCompactOpenEntire :=
  ⟨⟨fun z => z, continuous_id⟩, differentiable_id⟩

@[simp] theorem deningerCompactOpenCoordinate_apply (z : ℂ) :
    deningerCompactOpenCoordinate z = z :=
  rfl

def deningerCompactOpenDslope (F : DeningerCompactOpenEntire) :
    DeningerCompactOpenEntire :=
  ⟨⟨dslope (F : ℂ → ℂ) 0,
      (GaloisForLFunctions.HTGeometry.differentiable_dslope_of_differentiable
        F.2 0).continuous⟩,
    GaloisForLFunctions.HTGeometry.differentiable_dslope_of_differentiable F.2 0⟩

@[simp] theorem deningerCompactOpenDslope_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenDslope F z = dslope (F : ℂ → ℂ) 0 z :=
  rfl

theorem deningerCompactOpenDslope_odd_of_even
    (F : DeningerCompactOpenEntire) (heven : ∀ z, F (-z) = F z) :
    ∀ z, deningerCompactOpenDslope F (-z) =
      -deningerCompactOpenDslope F z := by
  intro z
  by_cases hz : z = 0
  · subst z
    simp only [neg_zero, deningerCompactOpenDslope_apply]
    rw [dslope_same]
    have hderiv : deriv (F : ℂ → ℂ) 0 = 0 := by
      simpa only [iteratedDeriv_one] using
        (GaloisForLFunctions.HTGeometry.iteratedDeriv_zero_of_even_of_odd
          heven (by exact ⟨0, by omega⟩ : Odd 1))
    rw [hderiv, neg_zero]
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [deningerCompactOpenDslope_apply,
      deningerCompactOpenDslope_apply,
      dslope_of_ne _ hnz, dslope_of_ne _ hz,
      slope_def_field, slope_def_field]
    change (F (-z) - F 0) / (-z - 0) =
      -((F z - F 0) / (z - 0))
    rw [heven]
    field_simp [hz]
    ring

theorem one_add_coordinate_mul_dslope_eq_of_normalized
    (F : DeningerCompactOpenEntire) (hnorm : F 0 = 1) :
    ∀ z, 1 + z * deningerCompactOpenDslope F z = F z := by
  intro z
  by_cases hz : z = 0
  · subst z
    simpa using hnorm.symm
  · rw [deningerCompactOpenDslope_apply, dslope_of_ne _ hz,
      slope_def_field]
    change 1 + z * ((F z - F 0) / (z - 0)) = F z
    rw [hnorm]
    field_simp [hz]
    ring

def deningerCompactOpenMul
    (F G : DeningerCompactOpenEntire) : DeningerCompactOpenEntire :=
  ⟨F.1 * G.1, F.2.mul G.2⟩

@[simp] theorem deningerCompactOpenMul_apply
    (F G : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenMul F G z = F z * G z :=
  rfl

theorem continuous_deningerCompactOpenMul :
    Continuous fun FG : DeningerCompactOpenEntire × DeningerCompactOpenEntire =>
      deningerCompactOpenMul FG.1 FG.2 := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

def deningerCompactOpenOne : DeningerCompactOpenEntire :=
  ⟨⟨fun _ => 1, continuous_const⟩, differentiable_const 1⟩

@[simp] theorem deningerCompactOpenOne_apply (z : ℂ) :
    deningerCompactOpenOne z = 1 :=
  rfl

def additiveSCCrossPrimeDeterminantEntire
    (a b : Nat.Primes →₀ ℂ) : DeningerCompactOpenEntire :=
  deningerCompactOpenOne +
    deningerCompactOpenMul
      (deningerOddPrimeExponentialSum a)
      (deningerOddPrimeExponentialSum b)

@[simp] theorem additiveSCCrossPrimeDeterminantEntire_apply
    (a b : Nat.Primes →₀ ℂ) (z : ℂ) :
    additiveSCCrossPrimeDeterminantEntire a b z =
      1 + deningerOddPrimeExponentialSum a z *
        deningerOddPrimeExponentialSum b z :=
  rfl

def additiveSCCrossPrimeMatrix
    (a b : Nat.Primes →₀ ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, fisherDeconvolvedBocksteinSum a z;
    -fisherDeconvolvedBocksteinSum b z, 1]

theorem det_additiveSCCrossPrimeMatrix
    (a b : Nat.Primes →₀ ℂ) (z : ℂ) :
    (additiveSCCrossPrimeMatrix a b z).det =
      additiveSCCrossPrimeDeterminantEntire a b z := by
  rw [Matrix.det_fin_two]
  simp [additiveSCCrossPrimeMatrix,
    additiveSCCrossPrimeDeterminantEntire_apply,
    fisherDeconvolvedBocksteinSum_eq_oddPrimeExponentialSum]

theorem exists_additiveSCCrossPrimeDeterminantEntire_tendsto
    (F : DeningerCompactOpenEntire) (hnorm : F 0 = 1)
    (heven : ∀ z, F (-z) = F z) :
    ∃ a b : ℕ → (Nat.Primes →₀ ℂ),
      Tendsto
        (fun n => additiveSCCrossPrimeDeterminantEntire (a n) (b n))
        atTop (𝓝 F) := by
  obtain ⟨a, ha⟩ :=
    exists_deningerOddPrimeExponentialSum_tendsto_of_odd
      deningerCompactOpenCoordinate (fun z => by simp)
  obtain ⟨b, hb⟩ :=
    exists_deningerOddPrimeExponentialSum_tendsto_of_odd
      (deningerCompactOpenDslope F)
      (deningerCompactOpenDslope_odd_of_even F heven)
  refine ⟨a, b, ?_⟩
  have hpairs : Tendsto
      (fun n =>
        (deningerOddPrimeExponentialSum (a n),
          deningerOddPrimeExponentialSum (b n)))
      atTop
      (𝓝 (deningerCompactOpenCoordinate,
        deningerCompactOpenDslope F)) :=
    ha.prodMk_nhds hb
  have hmul :=
    continuous_deningerCompactOpenMul.continuousAt.tendsto.comp hpairs
  have hadd : Tendsto
      (fun n => deningerCompactOpenOne +
        deningerCompactOpenMul
          (deningerOddPrimeExponentialSum (a n))
          (deningerOddPrimeExponentialSum (b n)))
      atTop
      (𝓝 (deningerCompactOpenOne +
        deningerCompactOpenMul deningerCompactOpenCoordinate
          (deningerCompactOpenDslope F))) :=
    tendsto_const_nhds.add hmul
  have htarget : deningerCompactOpenOne +
      deningerCompactOpenMul deningerCompactOpenCoordinate
        (deningerCompactOpenDslope F) = F := by
    ext z
    exact one_add_coordinate_mul_dslope_eq_of_normalized F hnorm z
  change Tendsto
    (fun n => deningerCompactOpenOne +
      deningerCompactOpenMul
        (deningerOddPrimeExponentialSum (a n))
        (deningerOddPrimeExponentialSum (b n)))
    atTop (𝓝 F)
  rw [← htarget]
  exact hadd

theorem exists_additiveSCCrossPrimeMatrix_tendstoLocallyUniformly
    (F : DeningerCompactOpenEntire) (hnorm : F 0 = 1)
    (heven : ∀ z, F (-z) = F z) :
    ∃ a b : ℕ → (Nat.Primes →₀ ℂ),
      TendstoLocallyUniformly
        (fun n z => (additiveSCCrossPrimeMatrix (a n) (b n) z).det)
        (F : ℂ → ℂ) atTop := by
  obtain ⟨a, b, hab⟩ :=
    exists_additiveSCCrossPrimeDeterminantEntire_tendsto F hnorm heven
  refine ⟨a, b, ?_⟩
  have habC : Tendsto
      (fun n =>
        (additiveSCCrossPrimeDeterminantEntire (a n) (b n)).1)
      atTop (𝓝 F.1) :=
    (continuous_subtype_val.tendsto F).comp hab
  have hloc :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp habC
  have heqseq :
      (fun n z => (additiveSCCrossPrimeMatrix (a n) (b n) z).det) =
        (fun n z =>
          additiveSCCrossPrimeDeterminantEntire (a n) (b n) z) := by
    funext n z
    exact det_additiveSCCrossPrimeMatrix (a n) (b n) z
  rw [heqseq]
  exact hloc

def deningerNormalizedXiC : DeningerCompactOpenEntire :=
  ⟨⟨fun z => XiC z / XiC 0,
      XiC_differentiable.div_const (XiC 0) |>.continuous⟩,
    XiC_differentiable.div_const (XiC 0)⟩

@[simp] theorem deningerNormalizedXiC_apply (z : ℂ) :
    deningerNormalizedXiC z = XiC z / XiC 0 :=
  rfl

/-- Unconditional normalized-Xi specialization of additive cross-prime determinant
universality. Every approximant is a literal determinant of a `2 × 2` matrix whose
off-diagonal entries are finite Fisher-deconvolved prime Bockstein sums. -/
theorem exists_additiveSCCrossPrimeMatrix_tendstoLocallyUniformly_normalizedXiC :
    ∃ a b : ℕ → (Nat.Primes →₀ ℂ),
      TendstoLocallyUniformly
        (fun n z => (additiveSCCrossPrimeMatrix (a n) (b n) z).det)
        (fun z => XiC z / XiC 0) atTop := by
  change ∃ a b : ℕ → (Nat.Primes →₀ ℂ),
    TendstoLocallyUniformly
      (fun n z => (additiveSCCrossPrimeMatrix (a n) (b n) z).det)
      (deningerNormalizedXiC : ℂ → ℂ) atTop
  exact exists_additiveSCCrossPrimeMatrix_tendstoLocallyUniformly
    deningerNormalizedXiC
    (by exact div_self XiC_zero_ne_zero)
    (fun z => by rw [deningerNormalizedXiC_apply,
      deningerNormalizedXiC_apply, XiC_even])

end

end RHTower

