import GaloisForLFunctions.RHTower.GaussSquareDiagonalLogResidue
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Label-faithful multi-place assembly of the Gauss channel system

The per-place residue laws assemble into one block-diagonal operator on the `ℓ²`-direct sum of
the circle spaces, one factor per member of a finite prime family.  The assembly is exactly
label-faithful: cross-place matrix elements of every power vanish identically, each place's
diagonal is the actual single-place diagonal, and the localized channel residue is realized
*per label* by the actual operators — at power one for one-fold components and at power two for
two-fold components.  Summing the labels afterwards recovers the scalar
`gaussPairedChannelResidue`, so the existing paired Schatten layer is precisely the label-blind
codiagonal shadow of this object.

The assembly retains the reflection data of every place — sample-value conjugation and phase
evenness per label, with both frequency orientations entering the diagonal as separate
summands — and admits the canonical cofinal prime aperture given by the `nth`-prime
enumeration, whose labels are injective.  Finally, the assembled residue current is a strictly
positive section of the same `(Nat.Primes → ℝ)` label bundle that carries the source-zero
horizontal class: its `log p` normalization is the rational local factor
`(2/m²)·((p-1)/p)^{2m}·(p^m-1)²`, and its pointwise product with the horizontal prime carrier
keeps the carrier's exact sign and critical radical at every label.  Identification with the
intersection pairing and any positivity statement are not claimed here.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

open GaloisForLFunctions.RHTower

noncomputable section

/-! ## The assembled space and the single-place embeddings -/

/-- The multi-place space: the `ℓ²`-direct sum of one circle space per family member. -/
abbrev GaussAssembledSpace (J : Type*) [Fintype J] :=
  PiLp 2 (fun _ : J => Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))

/-- The single-place embedding at the label `j`. -/
def gaussPlaceEmbed {J : Type*} [Fintype J] [DecidableEq J] (j : J)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : GaussAssembledSpace J :=
  (WithLp.toLp 2) (Pi.single j u)

/-- Same-place inner products restrict to the place. -/
theorem inner_gaussPlaceEmbed_same {J : Type*} [Fintype J] [DecidableEq J] (j : J)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPlaceEmbed j u) (gaussPlaceEmbed j v) : ℂ) = inner ℂ u v := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · simp [gaussPlaceEmbed]
  · intro b _ hb
    simp [gaussPlaceEmbed, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## The assembled block operator -/

/-- **The assembled quasi-inner block**: the block-diagonal operator whose place-`j` block is the
full quasi-inner block of the component `kk j` at the prime `prime j`. -/
def gaussAssembledBlock {J : Type*} [Fintype J] {m : ℕ} (hm : 1 ≤ m)
    (kk : J → Fin m) (prime : J → Nat.Primes) :
    GaussAssembledSpace J →L[ℂ] GaussAssembledSpace J :=
  ((((PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : J => Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))).symm) :
      _ →L[ℂ] _)).comp
    ((ContinuousLinearMap.pi
      (fun j => (gaussQuasiInnerGFull hm (kk j) (prime j)).comp
        (ContinuousLinearMap.proj j))).comp
      (((PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : J => Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))))) : _ →L[ℂ] _))

/-- The assembled block acts place by place. -/
theorem gaussAssembledBlock_apply {J : Type*} [Fintype J] {m : ℕ} (hm : 1 ≤ m)
    (kk : J → Fin m) (prime : J → Nat.Primes) (x : GaussAssembledSpace J) (j : J) :
    ((gaussAssembledBlock hm kk prime x).ofLp j)
      = gaussQuasiInnerGFull hm (kk j) (prime j) (x.ofLp j) := rfl

/-- Every power of the assembled block acts place by place. -/
theorem gaussAssembledBlock_pow_apply {J : Type*} [Fintype J] {m : ℕ} (hm : 1 ≤ m)
    (kk : J → Fin m) (prime : J → Nat.Primes) (r : ℕ) (x : GaussAssembledSpace J) (j : J) :
    (((gaussAssembledBlock hm kk prime ^ r) x).ofLp j)
      = (gaussQuasiInnerGFull hm (kk j) (prime j) ^ r) (x.ofLp j) := by
  induction r with
  | zero =>
      rw [pow_zero, pow_zero]
      rfl
  | succ r ih =>
      have h1 : (gaussAssembledBlock hm kk prime ^ (r + 1)) x
          = gaussAssembledBlock hm kk prime ((gaussAssembledBlock hm kk prime ^ r) x) := by
        rw [pow_succ']
        rfl
      have h2 : (gaussQuasiInnerGFull hm (kk j) (prime j) ^ (r + 1)) (x.ofLp j)
          = gaussQuasiInnerGFull hm (kk j) (prime j)
              ((gaussQuasiInnerGFull hm (kk j) (prime j) ^ r) (x.ofLp j)) := by
        rw [pow_succ']
        rfl
      rw [h1, h2, gaussAssembledBlock_apply, ih]

/-! ## Exact label-faithfulness -/

/-- **Cross-place matrix elements of every power vanish identically**: the assembly never mixes
prime labels. -/
theorem inner_gaussPlaceEmbed_assembled_ne {J : Type*} [Fintype J] [DecidableEq J]
    {m : ℕ} (hm : 1 ≤ m) (kk : J → Fin m) (prime : J → Nat.Primes) (r : ℕ)
    {j j' : J} (hjj' : j ≠ j')
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPlaceEmbed j u)
      ((gaussAssembledBlock hm kk prime ^ r) (gaussPlaceEmbed j' v)) : ℂ) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [gaussAssembledBlock_pow_apply]
  by_cases hij : i = j
  · subst hij
    have hsingle : (gaussPlaceEmbed j' v).ofLp i = 0 := by
      simp [gaussPlaceEmbed, (Ne.symm hjj' : j' ≠ i)]
    rw [hsingle, map_zero, inner_zero_right]
  · have hji : j ≠ i := fun h => hij h.symm
    have hsingle : (gaussPlaceEmbed j u).ofLp i = 0 := by
      simp [gaussPlaceEmbed, hji]
    rw [hsingle, inner_zero_left]

/-- **Place-faithfulness**: the same-place matrix elements of every power are the actual
single-place matrix elements. -/
theorem inner_gaussPlaceEmbed_assembled_same {J : Type*} [Fintype J] [DecidableEq J]
    {m : ℕ} (hm : 1 ≤ m) (kk : J → Fin m) (prime : J → Nat.Primes) (r : ℕ) (j : J)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPlaceEmbed j u)
      ((gaussAssembledBlock hm kk prime ^ r) (gaussPlaceEmbed j v)) : ℂ)
      = inner ℂ u ((gaussQuasiInnerGFull hm (kk j) (prime j) ^ r) v) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [gaussAssembledBlock_pow_apply]
    simp [gaussPlaceEmbed]
  · intro b _ hb
    rw [gaussAssembledBlock_pow_apply]
    have hjb : j ≠ b := Ne.symm hb
    have hsingle : (gaussPlaceEmbed j u).ofLp b = 0 := by
      simp [gaussPlaceEmbed, hjb]
    rw [hsingle, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## The label-faithful diagonal current -/

/-- The label-faithful two-sided diagonal current of the assembled block: one complex value per
prime label and frequency, both frequency orientations entering as separate summands, no sum
over labels. -/
def gaussAssembledDiagonal {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ} (hm : 1 ≤ m)
    (kk : J → Fin m) (prime : J → Nat.Primes) (r : ℕ) (n : ℕ) : J → ℂ :=
  fun j =>
    (inner ℂ (gaussPlaceEmbed j (fourierLp 2 ((n : ℤ) + 1)))
      ((gaussAssembledBlock hm kk prime ^ r)
        (gaussPlaceEmbed j (fourierLp 2 ((n : ℤ) + 1)))) : ℂ) +
    (inner ℂ (gaussPlaceEmbed j (fourierLp 2 (-((n : ℤ) + 1))))
      ((gaussAssembledBlock hm kk prime ^ r)
        (gaussPlaceEmbed j (fourierLp 2 (-((n : ℤ) + 1))))) : ℂ)

/-- The assembled diagonal current is literally the family of single-place two-sided diagonals. -/
theorem gaussAssembledDiagonal_eq {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (hm : 1 ≤ m) (kk : J → Fin m) (prime : J → Nat.Primes) (r : ℕ) (n : ℕ) (j : J) :
    gaussAssembledDiagonal hm kk prime r n j
      = (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
          ((gaussQuasiInnerGFull hm (kk j) (prime j) ^ r) (fourierLp 2 ((n : ℤ) + 1))) : ℂ) +
        inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
          ((gaussQuasiInnerGFull hm (kk j) (prime j) ^ r) (fourierLp 2 (-((n : ℤ) + 1)))) := by
  rw [gaussAssembledDiagonal, inner_gaussPlaceEmbed_assembled_same,
    inner_gaussPlaceEmbed_assembled_same]

/-! ## Per-label residue laws for the actual assembled operator -/

/-- **Per-label residue law at `m = 1`.**  Each label of the assembled diagonal current at power
one carries the localized channel residue of its own prime, for the actual assembled operator. -/
theorem tendsto_gaussAssembledDiagonal_logResidue_one {J : Type*} [Fintype J] [DecidableEq J]
    (kk : J → Fin 1) (prime : J → Nat.Primes) (j : J) :
    Tendsto (fun N : ℕ =>
      ((gaussLocalFactorWeight 1 (prime j) : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          gaussAssembledDiagonal (le_refl 1) kk prime 1 n j) / (Real.log N : ℂ)))
      atTop (nhds ((gaussChannelResidue 1 (prime j) : ℝ) : ℂ)) := by
  have hbase := tendsto_gaussLocalDiagonal_logResidue (kk j) (prime j)
  refine hbase.congr fun N => ?_
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  exact (gaussAssembledDiagonal_eq (le_refl 1) kk prime 1 n j).symm

/-- **Per-label residue law at `m = 2`.**  Each label of the assembled diagonal current at power
two carries the localized channel residue of its own prime, for the actual assembled operator. -/
theorem tendsto_gaussAssembledDiagonal_logResidue_two {J : Type*} [Fintype J] [DecidableEq J]
    (kk : J → Fin 2) (prime : J → Nat.Primes) (j : J) :
    Tendsto (fun N : ℕ =>
      ((gaussLocalFactorWeight 2 (prime j) : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          gaussAssembledDiagonal one_le_two kk prime 2 n j) / (Real.log N : ℂ)))
      atTop (nhds ((gaussChannelResidue 2 (prime j) : ℝ) : ℂ)) := by
  have hbase := tendsto_gaussSquareLocalDiagonal_logResidue (kk j) (prime j)
  refine hbase.congr fun N => ?_
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  exact (gaussAssembledDiagonal_eq one_le_two kk prime 2 n j).symm

/-! ## Codiagonal collapse onto the paired scalar -/

/-- **Codiagonal collapse.**  Summing the labels of the assembled residue laws recovers exactly
the scalar `gaussPairedChannelResidue`: the existing paired layer is the label-blind shadow of
the assembly. -/
theorem tendsto_gaussAssembledDiagonal_codiagonal_two {J : Type*} [Fintype J] [DecidableEq J]
    (kk : J → Fin 2) (prime : J → Nat.Primes) :
    Tendsto (fun N : ℕ => ∑ j : J,
      ((gaussLocalFactorWeight 2 (prime j) : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N,
          gaussAssembledDiagonal one_le_two kk prime 2 n j) / (Real.log N : ℂ)))
      atTop (nhds ((gaussPairedChannelResidue 2 prime : ℝ) : ℂ)) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset J)
    (fun j _ => tendsto_gaussAssembledDiagonal_logResidue_two kk prime j)
  have hval : (∑ j : J, ((gaussChannelResidue 2 (prime j) : ℝ) : ℂ))
      = ((gaussPairedChannelResidue 2 prime : ℝ) : ℂ) := by
    rw [gaussPairedChannelResidue]
    push_cast
    rfl
  rwa [hval] at hsum

/-! ## Reflection data retained per label -/

/-- The assembled sample-value family reverses by conjugation at every label: both reflection
orientations survive the assembly. -/
theorem gaussAssembled_sampleValue_reflection {J : Type*} {m : ℕ}
    (kk : J → Fin m) (prime : J → Nat.Primes) (j : J) (i : ℤ) :
    gaussSampleValue (kk j) (prime j) (-i)
      = starRingEnd ℂ (gaussSampleValue (kk j) (prime j) i) :=
  gaussSampleValue_neg _ _ _

/-- The assembled phase family is even at every label. -/
theorem gaussAssembled_samplePhase_reflection {J : Type*} {m : ℕ}
    (prime : J → Nat.Primes) (j : J) (i : ℤ) :
    gaussSamplePhase m (prime j) (-i) = gaussSamplePhase m (prime j) i :=
  gaussSamplePhase_neg _ _ _

/-! ## The canonical cofinal prime aperture -/

/-- The canonical prime family at aperture `N`: the first `π(N)` primes. -/
def gaussCanonicalPrimeFamily (N : ℕ) : Fin (Nat.primeCounting N) → Nat.Primes :=
  fun i => ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩

/-- The canonical prime labels are pairwise distinct: the aperture is a genuine multi-place
family. -/
theorem gaussCanonicalPrimeFamily_injective (N : ℕ) :
    Function.Injective (gaussCanonicalPrimeFamily N) := by
  intro a b hab
  have hval : Nat.nth Nat.Prime a = Nat.nth Nat.Prime b := by
    have := congrArg (fun q : Nat.Primes => (q : ℕ)) hab
    simpa [gaussCanonicalPrimeFamily] using this
  by_contra hne
  have hvne : (a : ℕ) ≠ (b : ℕ) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvne with h | h
  · exact absurd hval
      (ne_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr h))
  · exact absurd hval.symm
      (ne_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr h))

/-- The canonical assembled block at aperture `N`, with two-fold components. -/
def gaussCanonicalAssembledBlock (N : ℕ) :
    GaussAssembledSpace (Fin (Nat.primeCounting N)) →L[ℂ]
      GaussAssembledSpace (Fin (Nat.primeCounting N)) :=
  gaussAssembledBlock one_le_two (fun _ => (0 : Fin 2)) (gaussCanonicalPrimeFamily N)

/-- **Canonical cofinal label-faithful assembly.**  At every aperture the canonical family has
injective labels, every label of the actual assembled operator carries its own localized channel
residue, the codiagonal collapse is the paired scalar, and the critical depth is cofinal. -/
theorem gaussCanonicalAssembled_law (N : ℕ) :
    Function.Injective (gaussCanonicalPrimeFamily N) ∧
      (∀ j : Fin (Nat.primeCounting N),
        Tendsto (fun M : ℕ =>
          ((gaussLocalFactorWeight 2 (gaussCanonicalPrimeFamily N j) : ℝ) : ℂ) *
            ((∑ n ∈ Finset.range M,
              gaussAssembledDiagonal one_le_two (fun _ => (0 : Fin 2))
                (gaussCanonicalPrimeFamily N) 2 n j) / (Real.log M : ℂ)))
          atTop (nhds ((gaussChannelResidue 2 (gaussCanonicalPrimeFamily N j) : ℝ) : ℂ))) ∧
      Tendsto (fun M : ℕ => ∑ j : Fin (Nat.primeCounting N),
        ((gaussLocalFactorWeight 2 (gaussCanonicalPrimeFamily N j) : ℝ) : ℂ) *
          ((∑ n ∈ Finset.range M,
            gaussAssembledDiagonal one_le_two (fun _ => (0 : Fin 2))
              (gaussCanonicalPrimeFamily N) 2 n j) / (Real.log M : ℂ)))
        atTop (nhds ((gaussPairedChannelResidue 2 (gaussCanonicalPrimeFamily N) : ℝ) : ℂ)) ∧
      Tendsto gaussPairedCriticalDepth atTop atTop :=
  ⟨gaussCanonicalPrimeFamily_injective N,
    fun j => tendsto_gaussAssembledDiagonal_logResidue_two _ _ j,
    tendsto_gaussAssembledDiagonal_codiagonal_two _ _,
    tendsto_gaussPairedCriticalDepth⟩

/-! ## The assembled residue current in the carrier's label bundle -/

/-- The assembled residue current: the all-prime, label-faithful section of channel residues. -/
def gaussChannelResidueCurrent (m : ℕ) : Nat.Primes → ℝ :=
  fun p => gaussChannelResidue m p

/-- The current is strictly positive at every label. -/
theorem gaussChannelResidueCurrent_pos {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    0 < gaussChannelResidueCurrent m p :=
  gaussChannelResidue_pos hm p

/-- **Weil normalization.**  The `log p`-normalized current is the rational local factor
`(2/m²)·((p-1)/p)^{2m}·(p^m-1)²`. -/
theorem gaussChannelResidueCurrent_mul_log {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    gaussChannelResidueCurrent m p * Real.log (p : ℝ)
      = 2 / (m : ℝ) ^ (2 : ℕ) * gaussLocalFactorWeight m p * ((p : ℝ) ^ m - 1) ^ (2 : ℕ) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  have hm0 : ((m : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    exact this.ne'
  rw [gaussChannelResidueCurrent, gaussChannelResidue, gaussLocalFactorWeight, div_pow]
  field_simp

/-- The current reads the left-half carrier orientation positively at every label. -/
theorem gaussChannelResidueCurrent_mul_carrier_pos_of_leftHalf {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (hhalf : (q.1 : ℂ).re < 1 / 2) (p : Nat.Primes) :
    0 < gaussChannelResidueCurrent m p * sourceZeroHorizontalPrimeCarrier q p :=
  mul_pos (gaussChannelResidueCurrent_pos hm p)
    (sourceZeroHorizontalPrimeCarrier_pos_of_leftHalf q hhalf p)

/-- The current reads the right-half carrier orientation negatively at every label. -/
theorem gaussChannelResidueCurrent_mul_carrier_neg_of_rightHalf {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (hhalf : 1 / 2 < (q.1 : ℂ).re) (p : Nat.Primes) :
    gaussChannelResidueCurrent m p * sourceZeroHorizontalPrimeCarrier q p < 0 :=
  mul_neg_of_pos_of_neg (gaussChannelResidueCurrent_pos hm p)
    (sourceZeroHorizontalPrimeCarrier_neg_of_rightHalf q hhalf p)

/-- **Radical preservation.**  Weighting the horizontal prime carrier by the assembled residue
current changes no zero set: the weighted carrier vanishes at a label exactly on the critical
line. -/
theorem gaussChannelResidueCurrent_mul_carrier_eq_zero_iff {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussChannelResidueCurrent m p * sourceZeroHorizontalPrimeCarrier q p = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h (gaussChannelResidueCurrent_pos hm p).ne'
    · exact (sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p).1 h
  · intro h
    exact Or.inr ((sourceZeroHorizontalPrimeCarrier_eq_zero_iff q p).2 h)

/-- **Reflection through the weighted carrier.**  The current is fixed by the line-conjugate
reflection while the carrier reverses, so the weighted carrier reverses: both orientations stay
alive after weighting by the assembly. -/
theorem gaussChannelResidueCurrent_mul_carrier_reflection {m : ℕ}
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussChannelResidueCurrent m p *
        sourceZeroHorizontalPrimeCarrier (xiZeroCopyLineConjEquiv q) p
      = -(gaussChannelResidueCurrent m p * sourceZeroHorizontalPrimeCarrier q p) := by
  rw [sourceZeroHorizontalPrimeCarrier_reflection]
  ring

end

end RHTower
