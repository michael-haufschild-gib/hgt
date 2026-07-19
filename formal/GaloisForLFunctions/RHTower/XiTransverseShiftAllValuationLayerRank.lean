import GaloisForLFunctions.RHTower.XiTransverseShiftDefectDifferentialRank

/-!
# Transverse Xi shift rank beyond every scalar valuation layer

The absolute transverse-rank theorem shows that distinct positive integral filtered von Mangoldt
shift defects are jointly differentially independent over the true rational coordinate field.
This module proves the stronger completion-boundary statement: the whole finite family remains
jointly differentially independent after adjoining every prime-zeta valuation layer at once.
Finitarity and the pointed collision law then identify the represented matroid of every arbitrary
indexed shift family over that complete layer field: zero shifts are loops, repetitions are
parallel, and the rank of any packet is the number of distinct nonzero shifts.

The decisive step is transverse rather than diagonal. A proposed relation uses only finitely many
valuation layers, so it leaves one exponent coordinate unused. On that coordinate all old scalar
layers vanish, while the new shift columns become exponential-polynomial functions

`(log p)^(k+1) * (1 - exp (-(e+1) * a * log p))`.

Prime exp/log fibre rigidity kills every aperture column simultaneously. The old scalar layers
then separate on their private exponent coordinates. Thus the result is not obtained by applying
the one-source completion theorem shift by shift.

No declaration here constrains Xi zeros or proves RH. The capstone rules out every differential
compression of the transverse source family beyond literal zero/repetition collisions, even over
the completed scalar valuation field.
-/

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiTransverseLayerUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiTransverseLayerUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiTransverseLayerUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiTransverseLayerUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiTransverseLayerCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiTransverseLayerCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiTransverseAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiTransverseAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

theorem xiTransversePrimePowerCoordinateProfile_apply
    (f : ArithmeticFunction ℂ) (p : Nat.Primes) (e : ℕ) :
    primePowerCoordinateProfile f (p, e) = f ((p : ℕ) ^ (e + 1)) := by
  simp [primePowerCoordinateProfile]

/-- A nowhere-zero common weight on one valuation layer preserves independence of the complete
finite rotated-log jet packet. -/
theorem xiTransversePrimePowerLayerJetCoefficients_eq_zero
    (e m : ℕ) (w : Nat.Primes → ℂ) (hw : ∀ p, w p ≠ 0)
    (c : Fin (m + 1) → ℂ)
    (hfin : {p : Nat.Primes |
        ∑ k : Fin (m + 1), c k *
          (rotatedPrimePowerClockWeight (p, e) ^ (k : ℕ) * w p) ≠ 0}.Finite) :
    c = 0 := by
  classical
  have hbase := primePowerRotatedLogPowers_tailCoefficientIndependent e m
  have hweighted := (tailCoefficientIndependent_commonWeight_iff
      (fun k : Fin (m + 1) => fun p : Nat.Primes =>
        ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (k : ℕ))) w hw).mpr hbase
  apply hweighted c
  have hset : {p : Nat.Primes |
      ∑ k : Fin (m + 1), c k *
        (w p * ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (k : ℕ))) ≠ 0} =
      {p : Nat.Primes |
        ∑ k : Fin (m + 1), c k *
          (rotatedPrimePowerClockWeight (p, e) ^ (k : ℕ) * w p) ≠ 0} := by
    ext p
    simp only [Set.mem_setOf_eq,
      rotatedPrimePowerClockWeight_eq_valuation_mul_primeLog]
    have hsum :
        (∑ k : Fin (m + 1), c k *
          (w p * (↑(e + 1) * rotatedPrimeLogClock p) ^ (k : ℕ))) =
        ∑ k : Fin (m + 1), c k *
          ((↑(e + 1) * rotatedPrimeLogClock p) ^ (k : ℕ) * w p) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum]
  rw [hset]
  exact hfin

/-- Reading a clock-local finite jet combination on one valuation layer leaves only finitely many
active prime rays. -/
theorem xiTransversePrimeProfileJetCombination_layer_finite
    {I : Type*} [Fintype I] (G : I → ArithmeticFunction ℂ) (m : ℕ)
    (c : I × Fin (m + 1) → ℂ)
    (hlocal : PrimePowerClockLocal
      (primePowerCoordinateProfile (∑ col, c col • primeProfileJetSource G m col)))
    (e : ℕ) :
    {p : Nat.Primes |
      ∑ col : I × Fin (m + 1), c col *
        (rotatedPrimePowerClockWeight (p, e) ^ (col.2 : ℕ) *
          primePowerCoordinateProfile (G col.1) (p, e)) ≠ 0}.Finite := by
  classical
  apply hlocal.subset
  intro p hp
  refine ⟨(p, e), rfl, ?_⟩
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun g => primePowerCoordinateProfile g (p, e)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show primePowerCoordinateProfile
      (∑ col, c col • primeProfileJetSource G m col) (p, e) =
      ∑ col, primePowerCoordinateProfile
        (c col • primeProfileJetSource G m col) (p, e) from
    map_sum ev _ Finset.univ]
  simpa only [primePowerCoordinateProfile_smul, primeProfileJetSource,
    primePowerCoordinateProfile_primeProfileRotatedLogJet] using hp

theorem xiTransverse_cpowWeight_primePow (a e : ℕ) (p : Nat.Primes) :
    cpowWeight (a : ℂ) ((p : ℕ) ^ (e + 1)) =
      primeShiftFactor (((e + 1 : ℕ) : ℂ) * (a : ℂ)) p := by
  rw [← cpowWeight_prime_eq_primeShiftFactor]
  unfold cpowWeight
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring

/-- On valuation layer `e`, the shift-`a` jet is a nonzero scalar multiple of the prime-layer jet
with effective shift `(e+1)a`. -/
theorem xiTransverseShift_layerJet_eq_primeJet
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (e m : ℕ) (ak : A × Fin (m + 1)) (p : Nat.Primes) :
    rotatedPrimePowerClockWeight (p, e) ^ (ak.2 : ℕ) *
        primePowerCoordinateProfile
          (xiTransverseShiftArithmetic (shift ak.1)) (p, e) =
      (((e + 1 : ℕ) : ℂ) ^ (ak.2 : ℕ)) *
        primeProfileJetSource
          (fun a => xiTransverseShiftArithmetic ((e + 1) * shift a)) m ak p := by
  rw [rotatedPrimePowerClockWeight_eq_valuation_mul_primeLog,
    xiTransversePrimePowerCoordinateProfile_apply,
    xiTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    xiTransverse_cpowWeight_primePow]
  simp only [primeProfileJetSource, primeProfileRotatedLogJet_apply,
    xiTransverseShiftArithmetic_apply_prime]
  have hshift :
      (((e + 1) * shift ak.1 : ℕ) : ℂ) =
        (((e + 1 : ℕ) : ℂ) * (shift ak.1 : ℂ)) := by
    push_cast
    rfl
  rw [hshift]
  simp only [rotatedPrimeLogClock, primeLogClock, mul_pow]
  ring

/-- Distinct positive shift columns and all their finite jets are tail-independent on every fixed
valuation layer. -/
theorem xiTransverseShift_layerJets_tailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (e m : ℕ) :
    TailCoefficientIndependent
      (fun ak : A × Fin (m + 1) => fun p : Nat.Primes =>
        rotatedPrimePowerClockWeight (p, e) ^ (ak.2 : ℕ) *
          primePowerCoordinateProfile
            (xiTransverseShiftArithmetic (shift ak.1)) (p, e)) := by
  classical
  let scaledShift : A → ℕ := fun a => (e + 1) * shift a
  have hscaledPos : ∀ a, 0 < scaledShift a := by
    intro a
    exact Nat.mul_pos (Nat.succ_pos e) (hpos a)
  have hscaledInj : Function.Injective scaledShift := by
    intro a b hab
    apply hinj
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos e) hab
  have hprime := xiTransverseShift_primeJets_tailIndependent
    scaledShift hscaledPos hscaledInj m
  intro c hfinite
  let d : A × Fin (m + 1) → ℂ := fun ak =>
    c ak * (((e + 1 : ℕ) : ℂ) ^ (ak.2 : ℕ))
  have hfinite' :
      {p : Nat.Primes |
        ∑ ak : A × Fin (m + 1), d ak *
          primeProfileJetSource
            (fun a => xiTransverseShiftArithmetic (scaledShift a)) m ak p ≠ 0}.Finite := by
    apply hfinite.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have hsum :
        (∑ ak : A × Fin (m + 1), d ak *
          primeProfileJetSource
            (fun a => xiTransverseShiftArithmetic (scaledShift a)) m ak p) =
        ∑ ak : A × Fin (m + 1), c ak *
          (rotatedPrimePowerClockWeight (p, e) ^ (ak.2 : ℕ) *
            primePowerCoordinateProfile
              (xiTransverseShiftArithmetic (shift ak.1)) (p, e)) := by
      apply Finset.sum_congr rfl
      intro ak _
      rw [xiTransverseShift_layerJet_eq_primeJet shift e m ak p]
      simp only [d, scaledShift]
      ring
    rw [← hsum]
    exact hp
  have hd : d = 0 := hprime d hfinite'
  funext ak
  have hak := congrFun hd ak
  simp only [d, Pi.zero_apply] at hak
  exact (mul_eq_zero.mp hak).resolve_right
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e)))

/-- Every positive shift source is nonzero on every positive prime-power coordinate. -/
theorem xiTransverseShiftArithmetic_primePow_ne_zero
    (a : ℕ) (ha : 0 < a) (p : Nat.Primes) (e : ℕ) :
    xiTransverseShiftArithmetic a ((p : ℕ) ^ (e + 1)) ≠ 0 := by
  rw [xiTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    xiTransverse_cpowWeight_primePow]
  apply mul_ne_zero
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    exact_mod_cast (Real.log_pos hp).ne'
  · intro hzero
    have hexp :
        primeShiftFactor (((e + 1 : ℕ) : ℂ) * (a : ℂ)) p ≠ 1 := by
      have hrate : 0 < (((e + 1) * a : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.succ_pos e) ha
      have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
      have hpow : ((p : ℕ) : ℝ) ^ (-(((e + 1) * a : ℕ) : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hrate)
      have hfactor :
          primeShiftFactor (((e + 1 : ℕ) : ℂ) * (a : ℂ)) p =
            ((((p : ℕ) : ℝ) ^ (-(((e + 1) * a : ℕ) : ℝ)) : ℝ) : ℂ) := by
        rw [← cpowWeight_prime_eq_primeShiftFactor]
        unfold cpowWeight
        have hcast :
            -(((e + 1 : ℕ) : ℂ) * (a : ℂ)) =
              (-(((e + 1) * a : ℕ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hcast]
        simpa using
          (Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))
            (-(((e + 1) * a : ℕ) : ℝ))).symm
      rw [hfactor]
      exact_mod_cast hpow.ne
    exact hexp (sub_eq_zero.mp hzero).symm

/-- A finite transverse shift packet remains clock-independent when combined with any finite set
of distinct scalar valuation layers. The proof reads the transverse packet on one unused layer,
then reads each scalar layer on its own coordinate. -/
theorem xiTransverseShift_withValuationLayers_clockIndependent
    {A H : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype H] [DecidableEq H]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift)
    (idx : H → ℕ) (hidx : Function.Injective idx) :
    PrimeProfileClockIndependent
      (Sum.elim (fun a => xiTransverseShiftArithmetic (shift a))
        (fun z : H => scalarReplicatedPrimeProfile
          (scalarValuationBasisProfile (idx z)))) := by
  classical
  set G : A ⊕ H → ArithmeticFunction ℂ :=
    Sum.elim (fun a => xiTransverseShiftArithmetic (shift a))
      (fun z : H => scalarReplicatedPrimeProfile
        (scalarValuationBasisProfile (idx z))) with hGdef
  have hprofile : ∀ (z : H) (p : Nat.Primes) (e : ℕ),
      primePowerCoordinateProfile (G (Sum.inr z)) (p, e) =
        (if e = idx z then (1 : ℂ) else 0) := by
    intro z p e
    rw [hGdef]
    simp [scalarValuationBasisProfile,
      primePowerCoordinateProfile_scalarReplicatedPrimeProfile
        (scalarValuationBasisProfile (idx z)) (p, e)]
  have hnew : ∀ (a : A) (p : Nat.Primes) (e : ℕ),
      primePowerCoordinateProfile (G (Sum.inl a)) (p, e) =
        xiTransverseShiftArithmetic (shift a) ((p : ℕ) ^ (e + 1)) := by
    intro a p e
    rw [hGdef]
    exact xiTransversePrimePowerCoordinateProfile_apply _ _ _
  let used : Finset ℕ := Finset.univ.image idx
  have hnot : ¬ (Set.univ : Set ℕ) ⊆ (↑used : Set ℕ) := by
    intro hsub
    exact Set.infinite_univ (used.finite_toSet.subset hsub)
  obtain ⟨e0, _, he0used⟩ := Set.not_subset.mp hnot
  have he0 : ∀ z : H, idx z ≠ e0 := by
    intro z hz
    exact he0used (Finset.mem_image.mpr ⟨z, Finset.mem_univ z, hz⟩)
  rw [primeProfileClockIndependent_iff_finiteTailIndependent]
  intro m c hlocal
  change PrimePowerClockLocal
    (primePowerCoordinateProfile
      (∑ col, c col • primeProfileJetSource G m col)) at hlocal
  have hnewzero : ∀ (a : A) (k : Fin (m + 1)), c (Sum.inl a, k) = 0 := by
    have hfin := xiTransversePrimeProfileJetCombination_layer_finite G m c hlocal e0
    have hreduce : ∀ p : Nat.Primes,
        (∑ col : (A ⊕ H) × Fin (m + 1), c col *
          (rotatedPrimePowerClockWeight (p, e0) ^ (col.2 : ℕ) *
            primePowerCoordinateProfile (G col.1) (p, e0))) =
          ∑ ak : A × Fin (m + 1), c (Sum.inl ak.1, ak.2) *
            (rotatedPrimePowerClockWeight (p, e0) ^ (ak.2 : ℕ) *
              primePowerCoordinateProfile
                (xiTransverseShiftArithmetic (shift ak.1)) (p, e0)) := by
      intro p
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type,
        Fintype.sum_prod_type]
      have hright : ∀ z : H,
          (∑ k : Fin (m + 1), c (Sum.inr z, k) *
            (rotatedPrimePowerClockWeight (p, e0) ^ (k : ℕ) *
              primePowerCoordinateProfile (G (Sum.inr z)) (p, e0))) = 0 := by
        intro z
        apply Finset.sum_eq_zero
        intro k _
        rw [hprofile z p e0, if_neg (fun h => he0 z h.symm)]
        ring
      simp only [hright, Finset.sum_const_zero, add_zero, hnew]
      simp only [xiTransversePrimePowerCoordinateProfile_apply]
    have hfin' : {p : Nat.Primes |
        ∑ ak : A × Fin (m + 1), c (Sum.inl ak.1, ak.2) *
          (rotatedPrimePowerClockWeight (p, e0) ^ (ak.2 : ℕ) *
            primePowerCoordinateProfile
              (xiTransverseShiftArithmetic (shift ak.1)) (p, e0)) ≠ 0}.Finite := by
      apply hfin.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      rw [hreduce p]
      exact hp
    have hz := xiTransverseShift_layerJets_tailIndependent shift hpos hinj e0 m
      (fun ak => c (Sum.inl ak.1, ak.2)) hfin'
    intro a k
    exact congrFun hz (a, k)
  have holdzero : ∀ (z : H) (k : Fin (m + 1)), c (Sum.inr z, k) = 0 := by
    intro z
    have hfin := xiTransversePrimeProfileJetCombination_layer_finite G m c hlocal (idx z)
    have hreduce : ∀ p : Nat.Primes,
        (∑ col : (A ⊕ H) × Fin (m + 1), c col *
          (rotatedPrimePowerClockWeight (p, idx z) ^ (col.2 : ℕ) *
            primePowerCoordinateProfile (G col.1) (p, idx z))) =
          ∑ k : Fin (m + 1), c (Sum.inr z, k) *
            (rotatedPrimePowerClockWeight (p, idx z) ^ (k : ℕ) * (1 : ℂ)) := by
      intro p
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      have hleft : (∑ a : A, ∑ k : Fin (m + 1), c (Sum.inl a, k) *
          (rotatedPrimePowerClockWeight (p, idx z) ^ (k : ℕ) *
            primePowerCoordinateProfile (G (Sum.inl a)) (p, idx z))) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro k _
        rw [hnewzero a k, zero_mul]
      rw [hleft, zero_add]
      rw [Finset.sum_eq_single z]
      · apply Finset.sum_congr rfl
        intro k _
        rw [hprofile z p (idx z), if_pos rfl]
      · intro y _ hy
        apply Finset.sum_eq_zero
        intro k _
        rw [hprofile y p (idx z), if_neg (fun h => hy (hidx h.symm))]
        ring
      · intro hz
        exact absurd (Finset.mem_univ z) hz
    have hfin' : {p : Nat.Primes |
        ∑ k : Fin (m + 1), c (Sum.inr z, k) *
          (rotatedPrimePowerClockWeight (p, idx z) ^ (k : ℕ) * (1 : ℂ)) ≠ 0}.Finite := by
      apply hfin.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      rw [hreduce p]
      exact hp
    have hz := xiTransversePrimePowerLayerJetCoefficients_eq_zero (idx z) m
      (fun _ => (1 : ℂ)) (fun _ => one_ne_zero)
      (fun k => c (Sum.inr z, k)) hfin'
    intro k
    exact congrFun hz k
  funext col
  obtain ⟨i, k⟩ := col
  rcases i with a | z
  · exact hnewzero a k
  · exact holdzero z k

/-- **All-valuation finite transverse-rank theorem.** Distinct positive integral Xi prime-source
shift defects are jointly differentially independent over the single field generated by the true
rational coordinate and every prime-zeta valuation layer simultaneously. -/
theorem xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun a => finiteAbscissaLSeriesToUpperEndMero
        (xiTransverseShiftFiniteAbscissaSource (shift a))) := by
  classical
  let y : A → upperEndMeroField := fun a =>
    finiteAbscissaLSeriesToUpperEndMero
      (xiTransverseShiftFiniteAbscissaSource (shift a))
  let G : Set upperEndMeroField := Set.range analyticScalarValuationLayerCarrier
  have habs : DifferentialIndependent upperEndRationalCoordinateField y := by
    exact xiTransverseShiftUpperEndCarrier_differentialIndependent shift hpos hinj
  let equivRange : A ≃ Set.range y := Equiv.ofInjective y habs.injective
  have hstages : ∀ G0 : Set upperEndMeroField,
      G0 ⊆ G → G0.Finite →
        DiffIndepOn
          (differentialAdjoin upperEndRationalCoordinateField G0)
          (Set.range y) := by
    intro G0 hG0 hfinite
    letI : Fintype G0 := hfinite.fintype
    letI : DecidableEq G0 := Classical.decEq G0
    choose idx hidxCarrier using fun z : G0 => hG0 z.2
    have hidx : Function.Injective idx := by
      intro z w hzw
      apply Subtype.ext
      rw [← hidxCarrier z, ← hidxCarrier w, hzw]
    let sources : A ⊕ G0 → finiteAbscissaArithmeticSubalgebra :=
      Sum.elim (fun a => xiTransverseShiftFiniteAbscissaSource (shift a))
        (fun z : G0 => boundedScalarReplicatedFiniteAbscissa
          (scalarValuationBasisProfile (idx z)) 1
          (scalarValuationBasisProfile_norm_le_one (idx z)))
    have hsourceSupport : ∀ i,
        PrimeProfileSupportedOnPositivePrimePowers (sources i).1 := by
      intro i
      rcases i with a | z
      · exact xiTransverseShiftArithmetic_supportedOnPositivePrimePowers (shift a)
      · exact scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers _
    have hclock : PrimeProfileClockIndependent (fun i => (sources i).1) := by
      have hfamily : (fun i => (sources i).1) =
          Sum.elim (fun a => xiTransverseShiftArithmetic (shift a))
            (fun z : G0 => scalarReplicatedPrimeProfile
              (scalarValuationBasisProfile (idx z))) := by
        funext i
        rcases i with a | z <;> rfl
      rw [hfamily]
      exact xiTransverseShift_withValuationLayers_clockIndependent
        shift hpos hinj idx hidx
    have hcombined :=
      differentialIndependent_finiteAbscissaPrimeProfiles_of_clockIndependent
        sources hsourceSupport hclock
    have hfamily :
        (fun i => finiteAbscissaLSeriesToUpperEndMero (sources i)) =
          Sum.elim y (fun z : G0 => z.1) := by
      funext i
      rcases i with a | z
      · rfl
      · simpa only [sources, analyticScalarValuationLayerCarrier,
          analyticScalarReplicatedCarrier] using hidxCarrier z
    rw [hfamily] at hcombined
    have hrelative :=
      (differentialIndependent_sumElim_right_iff y (fun z : G0 => z.1)).mp
        hcombined |>.2
    rw [Subtype.range_val] at hrelative
    unfold DiffIndepOn
    have h := hrelative.comp equivRange.symm equivRange.symm.injective
    simpa [equivRange] using h
  have hset : DiffIndepOn
      (differentialAdjoin upperEndRationalCoordinateField G) (Set.range y) :=
    diffIndepOn_differentialAdjoin_of_forall_finite_subset hstages
  unfold DiffIndepOn at hset
  have h := hset.comp equivRange equivRange.injective
  simpa [analyticScalarValuationLayerDifferentialField, G, y, equivRange] using h

/-! ## Exact arbitrary-family completion law -/

/-- Injective nonzero transverse shift families remain differentially independent over the
complete scalar valuation-layer field, without a finiteness assumption on the index type. -/
theorem xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers_of_injective_ne_zero
    {A : Type*} (shift : A → ℕ) (hinj : Function.Injective shift)
    (hne : ∀ a, shift a ≠ 0) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
      (fun a => xiTransverseShiftUpperEndCarrier (shift a)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro I hIfinite
  by_cases hIempty : I = ∅
  · subst I
    exact algebraicIndependent_empty_type
  letI : Fintype I := hIfinite.fintype
  letI : Nonempty I :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hIempty)
  simpa [xiTransverseShiftUpperEndCarrier] using
    xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers
      (fun i : I => shift i)
      (fun i => Nat.pos_of_ne_zero (hne i))
      (fun i j hij => Subtype.ext (hinj hij))

/-- **All-valuation pointed collision law.** Even after adjoining every scalar prime-valuation
layer, zero shifts are loops, repetitions are parallel, and distinct positive shifts are the only
differential directions in an arbitrary indexed family. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision
    {A : Type*} (shift : A → ℕ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a => xiTransverseShiftUpperEndCarrier (shift a)) =
      affinePointedCollisionMatroid shift 0 := by
  apply differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
  · intro I hIinj hInonzero
    apply
      xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers_of_injective_ne_zero
        (fun i : I => shift i)
    · intro i j hij
      exact Subtype.ext (hIinj i.2 j.2 hij)
    · intro i
      exact hInonzero i i.2
  · intro i hi
    rw [hi, xiTransverseShiftUpperEndCarrier_zero]
    exact differentialAlgebraicOver_algebraMap 0
  · intro i j _ hij
    rw [hij, sub_self]
    exact differentialAlgebraicOver_algebraMap 0

/-- Exact Prop interface over the complete scalar valuation-layer field. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff
    {A : Type*} (shift : A → ℕ) (I : Set A) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun i : I => xiTransverseShiftUpperEndCarrier (shift i)) ↔
      Set.InjOn shift I ∧ ∀ i ∈ I, shift i ≠ 0 := by
  let x := fun a => xiTransverseShiftUpperEndCarrier (shift a)
  constructor
  · intro hI
    have hmatroid : (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField) x).Indep I :=
      (differentialFamilyMatroid_indep_iff x I).mpr hI
    rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff] at hmatroid
    exact hmatroid
  · intro hI
    apply (differentialFamilyMatroid_indep_iff x I).mp
    rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff]
    exact hI

/-- Exact relative differential rank of every transverse shift packet over the complete scalar
valuation-layer field. -/
theorem xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eRk
    {A : Type*} (shift : A → ℕ) (I : Set A) :
    (differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun a => xiTransverseShiftUpperEndCarrier (shift a))).eRk I =
      ((shift '' I) ∩ {a | a ≠ 0}).encard := by
  rw [xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

end

end RHTower
