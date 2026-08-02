import GaloisForLFunctions.HTGeometry.PrimeDependentValuationLayerBarrier
import GaloisForLFunctions.HTGeometry.PrimeValuationCoordinateFusionCompletion

/-!
# Primitive sources beyond residue--valuation fusion completion

Finite residue alphabets and prime-power valuation layers generate a canonical differential field
closed under same-prime carrier fusion. This file proves that a prime-power source which is
nowhere zero on infinitely many valuation layers remains differentially independent over that
entire depth--residue completion.

The proof has two parts. Cofinite tail density makes every finite depth--residue window free under
the complete logarithmic clock. A proposed differential relation uses only finitely many window
generators, so an unused valuation layer annihilates every old source while retaining the new one.
The resulting private layer separates all jets of the primitive source before the old window is
removed by its own clock independence.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

local instance scalarCompletionUpperEndDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance scalarCompletionUpperEndComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance scalarCompletionUpperEndDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

theorem privateLayerClockIndependence
    {H : Type*} [Fintype H] [DecidableEq H]
    (f : ArithmeticFunction ℂ) (G : H → ArithmeticFunction ℂ)
    (hG : PrimeProfileClockIndependent G)
    (e₀ : ℕ)
    (hGzero : ∀ z : H, ∀ p : Nat.Primes,
      G z ((p : ℕ) ^ (e₀ + 1)) = 0)
    (hf₀ : ∀ p : Nat.Primes, f ((p : ℕ) ^ (e₀ + 1)) ≠ 0) :
    PrimeProfileClockIndependent
      (Sum.elim (fun _ : Unit => f) G) := by
  classical
  let S : Unit ⊕ H → ArithmeticFunction ℂ :=
    Sum.elim (fun _ : Unit => f) G
  rw [primeProfileClockIndependent_iff_finiteTailIndependent]
  intro m c hlocal
  change PrimePowerClockLocal
    (primePowerCoordinateProfile
      (∑ col, c col • primeProfileJetSource S m col)) at hlocal
  have hnewzero : ∀ k : Fin (m + 1), c (Sum.inl (), k) = 0 := by
    have hfin := primeProfileJetCombination_layer_finite S m c hlocal e₀
    have hreduce : ∀ p : Nat.Primes,
        (∑ col : (Unit ⊕ H) × Fin (m + 1), c col *
          (rotatedPrimePowerClockWeight (p, e₀) ^ (col.2 : ℕ) *
            primePowerCoordinateProfile (S col.1) (p, e₀))) =
          ∑ k : Fin (m + 1), c (Sum.inl (), k) *
            (rotatedPrimePowerClockWeight (p, e₀) ^ (k : ℕ) *
              f ((p : ℕ) ^ (e₀ + 1))) := by
      intro p
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      have hright : ∀ z : H,
          (∑ k : Fin (m + 1), c (Sum.inr z, k) *
            (rotatedPrimePowerClockWeight (p, e₀) ^ (k : ℕ) *
              primePowerCoordinateProfile (S (Sum.inr z)) (p, e₀))) = 0 := by
        intro z
        apply Finset.sum_eq_zero
        intro k _
        rw [show primePowerCoordinateProfile (S (Sum.inr z)) (p, e₀) =
            G z ((p : ℕ) ^ (e₀ + 1)) by
          exact primePowerCoordinateProfile_apply_eq (G z) p e₀]
        rw [hGzero z p]
        ring
      simp only [hright, Finset.sum_const_zero, add_zero,
        Finset.univ_unique, Finset.sum_singleton]
      congr 1
    have hfin' : {p : Nat.Primes |
        ∑ k : Fin (m + 1), c (Sum.inl (), k) *
          (rotatedPrimePowerClockWeight (p, e₀) ^ (k : ℕ) *
            f ((p : ℕ) ^ (e₀ + 1))) ≠ 0}.Finite := by
      apply hfin.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      rw [hreduce p]
      exact hp
    have hz := primePowerLayerJetCoefficients_eq_zero e₀ m
      (fun p => f ((p : ℕ) ^ (e₀ + 1))) hf₀
      (fun k => c (Sum.inl (), k)) hfin'
    intro k
    exact congrFun hz k
  cases isEmpty_or_nonempty H with
  | inl hEmpty =>
      funext col
      rcases col with ⟨i, k⟩
      rcases i with u | z
      · cases u
        exact hnewzero k
      · exact isEmptyElim z
  | inr hNonempty =>
    letI : Nonempty H := hNonempty
    rw [primeProfileClockIndependent_iff_finiteTailIndependent] at hG
    let cOld : H × Fin (m + 1) → ℂ := fun col =>
      c (Sum.inr col.1, col.2)
    have hsource :
        (∑ col, c col • primeProfileJetSource S m col) =
          ∑ col, cOld col • primeProfileJetSource G m col := by
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      have hleft :
          (∑ k : Fin (m + 1),
            c (Sum.inl (), k) • primeProfileJetSource S m (Sum.inl (), k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [hnewzero k, zero_smul]
      rw [Finset.univ_unique, Finset.sum_singleton, hleft, zero_add]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro k _
      rfl
    have hold := hG m cOld (by
      rw [← hsource]
      exact hlocal)
    funext col
    rcases col with ⟨i, k⟩
    rcases i with u | z
    · cases u
      exact hnewzero k
    · exact congrFun hold (z, k)

theorem cofiniteTailDenseOn_primeResidueValuationSource_clockIndependent
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    [Nonempty (PrimeResidueValuationInteractionGridIndex d A)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    PrimeProfileClockIndependent
      (fun x : PrimeResidueValuationInteractionGridIndex d A =>
        (finiteAbscissaPrimePowerDilation x.1
          (primeResidueFiniteAbscissaSource A y x.2)).1) := by
  classical
  letI : Fintype (∀ i, A i) := Fintype.ofFinite _
  letI : DecidableEq (∀ i, A i) := Classical.decEq _
  rw [primeProfileClockIndependent_iff_finiteTailIndependent]
  intro m
  let B : Fin d → Type u := fun _ =>
    (∀ i, A i) × (Unit × Fin (m + 1))
  letI (r : Fin d) : Fintype (B r) := inferInstance
  letI (r : Fin d) : DecidableEq (B r) := Classical.decEq _
  let a : ∀ r, B r → Nat.Primes → ℂ := fun r z p =>
    primeResidueInteractionCoefficient A y z.1 p *
      ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
        (z.2.2 : ℕ))
  have htail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    have h :=
      (primePowerCoefficientShiftedRotatedJet_tailIndependent_iff
        r.1 (primeResidueInteractionCoefficient A y)
        (fun _ : Unit => (0 : ℂ))
        (fun _ _ _ => Subsingleton.elim _ _)
        (primeResidueInteractionCoefficient_patternRangeFinite A y) m).mpr
        (primeResidueInteractionCoefficient_tailIndependent A y hy)
    simpa [a, primeShiftFactor] using h
  have hraw :=
    algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
      d B a htail
  let embed :
      PrimeResidueValuationInteractionGridIndex d A × Fin (m + 1) →
        Σ r, B r :=
    fun q => ⟨q.1.1, (q.1.2, ((), q.2))⟩
  have hembed : Function.Injective embed := by
    rintro ⟨⟨r, z⟩, k⟩ ⟨⟨s, w⟩, l⟩ h
    cases h
    rfl
  have hsub := hraw.comp embed hembed
  apply primeProfileTailIndependent_of_algebraicIndependent
  · intro q
    exact primeProfileRotatedLogJet_supportedOnPositivePrimePowers _
      (by
        intro n hn
        have hsource :
            (finiteAbscissaPrimePowerDilation q.1.1
              (primeResidueFiniteAbscissaSource A y q.1.2)).1 =
              arithmeticOfPrimePowerColumn q.1.1
                (primeResidueInteractionCoefficient A y q.1.2) := by
          apply finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
          rfl
        change
          (finiteAbscissaPrimePowerDilation q.1.1
            (primeResidueFiniteAbscissaSource A y q.1.2)).1 n ≠ 0 at hn
        rw [hsource] at hn
        obtain ⟨p, hp⟩ :=
          arithmeticOfPrimePowerColumn_support q.1.1
            (primeResidueInteractionCoefficient A y q.1.2) hn
        exact ⟨p, q.1.1, hp⟩)
      q.2
  · convert hsub using 1
    funext q
    congr 2
    ext n
    simp only [primeProfileJetSource, primeProfileRotatedLogJet_apply,
      embed, primePowerSigmaExponent, primePowerSigmaCoefficient, a]
    rw [finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
      q.1.1 (primeResidueFiniteAbscissaSource A y q.1.2)
      (primeResidueInteractionCoefficient A y q.1.2)]
    · by_cases hpow :
          ∃ p : Nat.Primes, n = (p : ℕ) ^ (q.1.1.1 + 1)
      · let p := chosenPrimePowerBase (q.1.1.1 + 1) n hpow
        have hn := chosenPrimePowerBase_spec (q.1.1.1 + 1) n hpow
        rw [hn, arithmeticOfPrimePowerColumn_apply,
          arithmeticOfPrimePowerColumn_apply]
        have hlog : Real.log (((p : ℕ) ^ (q.1.1.1 + 1) : ℕ) : ℝ) =
            ((q.1.1.1 + 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
          rw [show (((p : ℕ) ^ (q.1.1.1 + 1) : ℕ) : ℝ) =
              ((p : ℕ) : ℝ) ^ (q.1.1.1 + 1) by norm_num,
            Real.log_pow]
        rw [hlog]
        push_cast
        simp only [rotatedPrimeLogClock, primeLogClock, mul_pow]
        rw [Complex.ofReal_log (Nat.cast_nonneg (p : ℕ))]
        rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by norm_num]
        ring_nf
      · simp [arithmeticOfPrimePowerColumn, hpow]
    · rfl

/-- The complete depth--residue source family, over all valuation layers at once, is free under
the full logarithmic clock.  Finite character is essential: every proposed relation occupies a
bounded depth window and is therefore detected by the corresponding finite-grid theorem. -/
theorem cofiniteTailDenseOn_primeResidueValuationAllLayerSource_clockIndependent
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    PrimeProfileClockIndependent
      (fun x : ℕ × (∀ i, A i) =>
        (finiteAbscissaPrimePowerDilation x.1
          (primeResidueFiniteAbscissaSource A y x.2)).1) := by
  classical
  letI : Fintype (∀ i, A i) := Fintype.ofFinite _
  letI : DecidableEq (∀ i, A i) := Classical.decEq _
  unfold PrimeProfileClockIndependent
  rw [linearIndependent_iff']
  intro s c hsum q hq
  have hdepth :
      ((fun z : (ℕ × (∀ i, A i)) × ℕ => z.1.1) '' (s : Set _)).Finite :=
    s.finite_toSet.image _
  obtain ⟨D, hD⟩ := hdepth.bddAbove
  letI : Nonempty (PrimeResidueValuationInteractionGridIndex (D + 1) A) :=
    ⟨⟨⟨0, Nat.zero_lt_succ D⟩, fun _ => 1⟩⟩
  let embed : s →
      PrimeResidueValuationInteractionGridIndex (D + 1) A × ℕ :=
    fun z =>
      (⟨⟨z.1.1.1,
          Nat.lt_succ_of_le (hD ⟨z.1, z.2, rfl⟩)⟩, z.1.1.2⟩,
        z.1.2)
  have hembed : Function.Injective embed := by
    intro z w hzw
    apply Subtype.ext
    have hval := congrArg
      (fun r :
        PrimeResidueValuationInteractionGridIndex (D + 1) A × ℕ =>
          (((r.1.1 : ℕ), r.1.2), r.2)) hzw
    simpa [embed] using hval
  have hfull :=
    cofiniteTailDenseOn_primeResidueValuationSource_clockIndependent
      (d := D + 1) A y hy
  unfold PrimeProfileClockIndependent at hfull
  have hsub := hfull.comp embed hembed
  have hsum' :
      ∑ z : s, c z.1 •
          primeProfileClockJetFamily
            (fun x : ℕ × (∀ i, A i) =>
              (finiteAbscissaPrimePowerDilation x.1
                (primeResidueFiniteAbscissaSource A y x.2)).1) z.1 = 0 := by
    rw [← s.sum_attach] at hsum
    simpa only [Finset.attach_eq_univ] using hsum
  have hsumEmbed :
      ∑ z : s, c z.1 •
          (primeProfileClockJetFamily
            (fun x : PrimeResidueValuationInteractionGridIndex (D + 1) A =>
              (finiteAbscissaPrimePowerDilation x.1
                (primeResidueFiniteAbscissaSource A y x.2)).1)
            (embed z)) = 0 := by
    calc
      ∑ z : s, c z.1 •
          (primeProfileClockJetFamily
            (fun x : PrimeResidueValuationInteractionGridIndex (D + 1) A =>
              (finiteAbscissaPrimePowerDilation x.1
                (primeResidueFiniteAbscissaSource A y x.2)).1)
            (embed z)) =
        ∑ z : s, c z.1 •
          primeProfileClockJetFamily
            (fun x : ℕ × (∀ i, A i) =>
              (finiteAbscissaPrimePowerDilation x.1
                (primeResidueFiniteAbscissaSource A y x.2)).1) z.1 := by
          apply Finset.sum_congr rfl
          intro z hz
          rfl
      _ = 0 := hsum'
  exact Fintype.linearIndependent_iff.mp hsub
    (fun z : s => c z.1) hsumEmbed ⟨q, hq⟩

theorem finiteAbscissaPrimePowerDilation_apply_primePower_of_ne
    (e r : ℕ) (f : finiteAbscissaArithmeticSubalgebra)
    (a : Nat.Primes → ℂ) (hf : f.1 = arithmeticOfPrimeColumn a)
    (her : e ≠ r) (p : Nat.Primes) :
    (finiteAbscissaPrimePowerDilation e f).1
        ((p : ℕ) ^ (r + 1)) = 0 := by
  rw [finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn e f a hf]
  classical
  unfold arithmeticOfPrimePowerColumn
  change
    (if h : ∃ q : Nat.Primes,
        (p : ℕ) ^ (r + 1) = (q : ℕ) ^ (e + 1) then
      a (chosenPrimePowerBase (e + 1) ((p : ℕ) ^ (r + 1)) h)
    else 0) = 0
  split_ifs with hpow
  · obtain ⟨q, hq⟩ := hpow
    have hpdvd : (p : ℕ) ∣ (q : ℕ) ^ (e + 1) := by
      rw [← hq]
      exact dvd_pow_self (p : ℕ) (Nat.succ_ne_zero r)
    have hpq : p = q :=
      Subtype.ext (Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpdvd)
    subst q
    have hexp : r + 1 = e + 1 :=
      Nat.pow_right_injective p.2.two_le hq
    exact (her (by omega)).elim
  · rfl

theorem finiteAbscissaPrimePowerDilation_supportedOnPositivePrimePowers
    (e : ℕ) (f : finiteAbscissaArithmeticSubalgebra)
    (a : Nat.Primes → ℂ) (hf : f.1 = arithmeticOfPrimeColumn a) :
    PrimeProfileSupportedOnPositivePrimePowers
      (finiteAbscissaPrimePowerDilation e f).1 := by
  intro n hn
  rw [finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn e f a hf]
    at hn
  obtain ⟨p, hp⟩ := arithmeticOfPrimePowerColumn_support e a hn
  exact ⟨p, e, hp⟩

theorem analyticPrimeProfileCarrier_differentialIndependent_over_residueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers F.1)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      (fun _ : Unit => finiteAbscissaLSeriesToUpperEndMero F) := by
  classical
  letI : Fintype (∀ i, A i) := Fintype.ofFinite _
  letI : DecidableEq (∀ i, A i) := Classical.decEq _
  let target : upperEndMeroField := finiteAbscissaLSeriesToUpperEndMero F
  let generators : Set upperEndMeroField :=
    Set.range (primeResidueValuationUpperEndAllLayerCarrier A y)
  have hstages : ∀ G₀ : Set upperEndMeroField,
      G₀ ⊆ generators → G₀.Finite →
        GaloisForLFunctions.DiffIndepOn
          (GaloisForLFunctions.differentialAdjoin
            upperEndRationalCoordinateField G₀)
          ({target} : Set upperEndMeroField) := by
    intro G₀ hG₀ hfinite
    letI : Fintype G₀ := hfinite.fintype
    letI : DecidableEq G₀ := Classical.decEq G₀
    choose idx hidxCarrier using fun z : G₀ => hG₀ z.2
    have hidx : Function.Injective idx := by
      intro z w hzw
      apply Subtype.ext
      rw [← hidxCarrier z, ← hidxCarrier w, hzw]
    obtain ⟨e₀, he₀nonzero, he₀used⟩ :=
      exists_nonvanishing_layer_notMem F.1 hinf
        (Finset.univ.image fun z : G₀ => (idx z).1)
    have he₀ : ∀ z : G₀, (idx z).1 ≠ e₀ := by
      intro z hz
      exact he₀used (Finset.mem_image.mpr
        ⟨z, Finset.mem_univ z, hz⟩)
    let oldSource : G₀ → finiteAbscissaArithmeticSubalgebra := fun z =>
      finiteAbscissaPrimePowerDilation (idx z).1
        (primeResidueFiniteAbscissaSource A y (idx z).2)
    have hOldSupport : ∀ z,
        PrimeProfileSupportedOnPositivePrimePowers (oldSource z).1 := by
      intro z
      apply finiteAbscissaPrimePowerDilation_supportedOnPositivePrimePowers
        (idx z).1 (primeResidueFiniteAbscissaSource A y (idx z).2)
        (primeResidueInteractionCoefficient A y (idx z).2)
      rfl
    have hOldClock :
        PrimeProfileClockIndependent (fun z => (oldSource z).1) := by
      cases isEmpty_or_nonempty G₀ with
      | inl hEmpty =>
          unfold PrimeProfileClockIndependent
          rw [linearIndependent_iff]
          intro l _
          ext z
          exact isEmptyElim z.1
      | inr hNonempty =>
          letI : Nonempty G₀ := hNonempty
          let D : ℕ := Finset.univ.sup fun z : G₀ => (idx z).1
          have hdepth : ∀ z : G₀, (idx z).1 ≤ D := by
            intro z
            simpa [D] using
              (Finset.le_sup (f := fun z : G₀ => (idx z).1)
                (Finset.mem_univ z))
          let embed : G₀ →
              PrimeResidueValuationInteractionGridIndex (D + 1) A :=
            fun z => ⟨⟨(idx z).1, Nat.lt_succ_of_le (hdepth z)⟩,
              (idx z).2⟩
          have hembed : Function.Injective embed := by
            intro z w hzw
            apply hidx
            apply Prod.ext
            · exact congrArg
                (fun q :
                  PrimeResidueValuationInteractionGridIndex (D + 1) A =>
                    (q.1 : ℕ)) hzw
            · exact congrArg
                (fun q :
                  PrimeResidueValuationInteractionGridIndex (D + 1) A =>
                    q.2) hzw
          letI : Nonempty
              (PrimeResidueValuationInteractionGridIndex (D + 1) A) :=
            ⟨⟨⟨0, Nat.zero_lt_succ D⟩, fun _ => 1⟩⟩
          have hfull :=
            cofiniteTailDenseOn_primeResidueValuationSource_clockIndependent
              (d := D + 1) A y hy
          unfold PrimeProfileClockIndependent at hfull ⊢
          let jetEmbed : G₀ × ℕ →
              PrimeResidueValuationInteractionGridIndex (D + 1) A × ℕ :=
            fun q => (embed q.1, q.2)
          have hjetEmbed : Function.Injective jetEmbed := by
            intro z w hzw
            apply Prod.ext
            · exact hembed (congrArg Prod.fst hzw)
            · exact congrArg
                (fun q :
                  PrimeResidueValuationInteractionGridIndex (D + 1) A × ℕ =>
                    q.2) hzw
          have hsub := hfull.comp jetEmbed hjetEmbed
          have hjetFamily :
              (primeProfileClockJetFamily
                  (fun x :
                    PrimeResidueValuationInteractionGridIndex (D + 1) A =>
                    (finiteAbscissaPrimePowerDilation x.1
                      (primeResidueFiniteAbscissaSource A y x.2)).1) ∘
                jetEmbed) =
              primeProfileClockJetFamily (fun z => (oldSource z).1) := by
            funext q
            rfl
          rw [hjetFamily] at hsub
          exact hsub
    let sources : Unit ⊕ G₀ → finiteAbscissaArithmeticSubalgebra :=
      Sum.elim (fun _ : Unit => F) oldSource
    have hsourceSupport : ∀ i,
        PrimeProfileSupportedOnPositivePrimePowers (sources i).1 := by
      intro i
      rcases i with u | z
      · exact hsupport
      · exact hOldSupport z
    have hclock :
        PrimeProfileClockIndependent (fun i => (sources i).1) := by
      have hcombined := privateLayerClockIndependence F.1
        (fun z => (oldSource z).1) hOldClock e₀
        (fun z p =>
          finiteAbscissaPrimePowerDilation_apply_primePower_of_ne
            (idx z).1 e₀
            (primeResidueFiniteAbscissaSource A y (idx z).2)
            (primeResidueInteractionCoefficient A y (idx z).2)
            rfl (he₀ z) p)
        he₀nonzero
      have hsourceFamily :
          (fun i => (sources i).1) =
            Sum.elim (fun _ : Unit => F.1)
              (fun z => (oldSource z).1) := by
        funext i
        rcases i with u | z <;> rfl
      rw [hsourceFamily]
      exact hcombined
    have hcombined :=
      differentialIndependent_finiteAbscissaPrimeProfiles_of_clockIndependent
        sources hsourceSupport hclock
    have hfamily :
        (fun i => finiteAbscissaLSeriesToUpperEndMero (sources i)) =
          Sum.elim (fun _ : Unit => target) (fun z : G₀ => z.1) := by
      funext i
      rcases i with u | z
      · rfl
      · change
          finiteAbscissaLSeriesToUpperEndMero
              (finiteAbscissaPrimePowerDilation (idx z).1
                (primeResidueFiniteAbscissaSource A y (idx z).2)) =
            z.1
        exact hidxCarrier z
    rw [hfamily] at hcombined
    have hrelative :=
      (GaloisForLFunctions.differentialIndependent_sumElim_right_iff
        (fun _ : Unit => target) (fun z : G₀ => z.1)).mp hcombined |>.2
    rw [Subtype.range_val] at hrelative
    unfold GaloisForLFunctions.DiffIndepOn
    have hsingleton := hrelative.comp
      (fun _ : ({target} : Set upperEndMeroField) => ())
      (fun a b _ => Subsingleton.elim a b)
    have htarget :
        ((fun _ : Unit => target) ∘
            (fun _ : ({target} : Set upperEndMeroField) => ())) =
          (fun z : ({target} : Set upperEndMeroField) => z.1) := by
      funext z
      exact (Set.mem_singleton_iff.mp z.2).symm
    rw [htarget] at hsingleton
    exact hsingleton
  have hset : GaloisForLFunctions.DiffIndepOn
      (GaloisForLFunctions.differentialAdjoin
        upperEndRationalCoordinateField generators)
      ({target} : Set upperEndMeroField) :=
    diffIndepOn_differentialAdjoin_of_forall_finite_subset hstages
  unfold GaloisForLFunctions.DiffIndepOn at hset
  have hunit := hset.comp
    (fun _ : Unit =>
      (⟨target, Set.mem_singleton target⟩ :
        ({target} : Set upperEndMeroField)))
    (fun a b _ => Subsingleton.elim a b)
  simpa [primeResidueValuationUpperEndCoordinateFusionCompletionField,
    generators, target, Function.comp_def] using! hunit

/-- The primitive source is hypertranscendental over the complete depth--residue fusion field. -/
theorem analyticPrimeProfileCarrier_hypertranscendentalOver_residueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (F : finiteAbscissaArithmeticSubalgebra)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers F.1)
    (hinf : ¬ {e : Nat |
      ∀ p : Nat.Primes, F.1 ((p : Nat) ^ (e + 1)) ≠ 0}.Finite) :
    HypertranscendentalOver
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      (finiteAbscissaLSeriesToUpperEndMero F) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    analyticPrimeProfileCarrier_differentialIndependent_over_residueFusionCompletion
      A y hy F hsupport hinf

/-- Rational coordinate gauges have all jets in every coordinate-relative fusion completion. -/
theorem differentialJet_mem_residueFusionCompletion_of_mem_rationalCoordinate
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : upperEndMeroField) (hx : x ∈ upperEndRationalCoordinateField)
    (n : Nat) :
    GaloisForLFunctions.differentialJet n x ∈
      primeResidueValuationUpperEndCoordinateFusionCompletionField A y := by
  have hcoord : ∀ k : Nat, GaloisForLFunctions.differentialJet k x ∈
      upperEndRationalCoordinateField := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        rw [GaloisForLFunctions.differentialJet_succ]
        exact upperEndRationalCoordinateField_derivationClosed ih
  simpa using IntermediateField.algebraMap_mem
    (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
    (⟨GaloisForLFunctions.differentialJet n x, hcoord n⟩ :
      upperEndRationalCoordinateField)

/-- Adding rational coordinate gauges preserves independence across the fusion boundary. -/
theorem differentialIndependent_over_residueFusionCompletion_add_rationalCoordinate
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    {J : Type*} {x : J → upperEndMeroField}
    (hx : GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y) x)
    (r : J → upperEndMeroField)
    (hr : ∀ j, r j ∈ upperEndRationalCoordinateField) :
    GaloisForLFunctions.DifferentialIndependent
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      (fun j => x j + r j) := by
  apply hx.addOfJetsInBase
  intro j n
  exact ⟨⟨GaloisForLFunctions.differentialJet n (r j),
    differentialJet_mem_residueFusionCompletion_of_mem_rationalCoordinate
      A y (r j) (hr j) n⟩, rfl⟩

end

end GaloisForLFunctions.HTGeometry
