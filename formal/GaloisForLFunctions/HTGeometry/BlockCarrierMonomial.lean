import GaloisForLFunctions.HTGeometry.OstrowskiRelationCarrier

/-!
# Monomials in the jets of several carriers

A palette of `n` functions needs a relation among the jets of `n` different carriers, not of one.
Every carrier in such a palette has the same frequency family and differs only in its amplitudes —
in the intended construction the amplitudes of the `k`-th carrier are those of a fixed carrier
restricted to the `k`-th block of a partition of the index set.

So the expansion machinery generalizes by allowing the amplitude family to depend on the slot of the
monomial: the `j`-th factor of a monomial is a jet of the carrier `b j`.  Nothing else changes, and
the existing product-of-series lemma already takes a slot-indexed family, so the expansion, the
finite combination and the vanishing statement all carry over verbatim.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The amplitude of one monomial in the jets of a slot-indexed family of carriers. -/
def blockMonomialAmplitude {M : ℕ} (b : Fin M → ι → ℂ) (omega : ι → ℝ) (c : ℂ)
    (s : Fin M → ℕ) (n : Fin M → ι) : ℂ :=
  c * ∏ j, b j (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j

omit [DecidableEq ι] in
theorem summable_norm_blockMonomialAmplitude {omega : ι → ℝ} {M : ℕ} {b : Fin M → ι → ℂ}
    (hb : ∀ j, ExpSeriesNormallySummable (b j) omega) (c : ℂ) (s : Fin M → ℕ) :
    Summable fun n : Fin M → ι => ‖blockMonomialAmplitude b omega c s n‖ := by
  have hjet : ∀ j : Fin M,
      Summable fun i => ‖b j i * (Complex.I * (omega i : ℂ)) ^ s j‖ :=
    fun j => summable_norm_of_expSeriesNormallySummable ((hb j).iteratedDeriv (s j))
  have hprod := summable_norm_prod_expSeries M
    (fun j i => b j i * (Complex.I * (omega i : ℂ)) ^ s j) hjet
  have hval : ∀ n : Fin M → ι, ‖blockMonomialAmplitude b omega c s n‖
      = ‖c‖ * ‖∏ j, b j (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j‖ := by
    intro n
    rw [blockMonomialAmplitude, norm_mul]
  simpa only [hval] using hprod.mul_left ‖c‖

omit [DecidableEq ι] in
/-- **A monomial in the jets of several carriers is an exponential series over tuples.** -/
theorem blockMonomial_eq_expSeriesCarrier {omega : ι → ℝ} {M : ℕ} {b : Fin M → ι → ℂ}
    (hb : ∀ j, ExpSeriesNormallySummable (b j) omega) (c : ℂ) (s : Fin M → ℕ) (t : ℝ) :
    c * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (b j) omega) (t : ℂ)
      = expSeriesCarrier (blockMonomialAmplitude b omega c s) (tupleFrequency omega) t := by
  have hjet : ∀ j : Fin M, iteratedDeriv (s j) (cexpSeriesCarrier (b j) omega) (t : ℂ)
      = expSeriesCarrier (fun i => b j i * (Complex.I * (omega i : ℂ)) ^ s j) omega t := by
    intro j
    rw [iteratedDeriv_cexpSeriesCarrier (s j) (hb j), cexpSeriesCarrier_ofReal]
  have hsum : ∀ j : Fin M, Summable fun i => ‖b j i * (Complex.I * (omega i : ℂ)) ^ s j‖ :=
    fun j => summable_norm_of_expSeriesNormallySummable ((hb j).iteratedDeriv (s j))
  rw [Finset.prod_congr rfl fun j _ => hjet j,
    prod_expSeriesCarrier M (fun j i => b j i * (Complex.I * (omega i : ℂ)) ^ s j) omega hsum t,
    const_mul_expSeriesCarrier]
  rfl

omit [DecidableEq ι] in
/-- **A finite combination of such monomials is one exponential series.** -/
theorem blockMonomialCombination_eq_expSeriesCarrier {omega : ι → ℝ} {M : ℕ} {b : Fin M → ι → ℂ}
    (hb : ∀ j, ExpSeriesNormallySummable (b j) omega) {K : Finset (Fin M → ℕ)}
    (c : (Fin M → ℕ) → ℂ) (t : ℝ) :
    ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (b j) omega) (t : ℂ)
      = expSeriesCarrier
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
          blockMonomialAmplitude b omega (c p.1.1) p.1.1 p.2)
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t := by
  have hnorm : ∀ s : {s // s ∈ K},
      Summable fun n : Fin M → ι => ‖blockMonomialAmplitude b omega (c s.1) s.1 n‖ :=
    fun s => summable_norm_blockMonomialAmplitude hb (c s.1) s.1
  rw [← sum_expSeriesCarrier
    (fun s : {s // s ∈ K} => blockMonomialAmplitude b omega (c s.1) s.1)
    (fun _ : {s // s ∈ K} => tupleFrequency omega) hnorm t]
  have hterm : ∀ s : {s // s ∈ K},
      expSeriesCarrier (blockMonomialAmplitude b omega (c s.1) s.1) (tupleFrequency omega) t
        = c s.1 * ∏ j, iteratedDeriv (s.1 j) (cexpSeriesCarrier (b j) omega) (t : ℂ) :=
    fun s => (blockMonomial_eq_expSeriesCarrier hb (c s.1) s.1 t).symm
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  exact (Finset.sum_coe_sort K
    (fun s => c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (b j) omega) (t : ℂ))).symm

omit [DecidableEq ι] in
/-- **A vanishing combination is a vanishing exponential series.** -/
theorem blockExpSeriesCarrier_sigma_eq_zero {omega : ι → ℝ} {M : ℕ} {b : Fin M → ι → ℂ}
    (hb : ∀ j, ExpSeriesNormallySummable (b j) omega) {K : Finset (Fin M → ℕ)}
    (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ,
      ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (b j) omega) (t : ℂ) = 0)
    (t : ℝ) :
    expSeriesCarrier
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
          blockMonomialAmplitude b omega (c p.1.1) p.1.1 p.2)
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t = 0 := by
  rw [← blockMonomialCombination_eq_expSeriesCarrier hb c t]
  exact hzero t

/-! ### The fibre amplitude is a permanent -/

/-- **The fibre amplitude of a several-carrier monomial.**  At the frequency of an injective tuple
only the permutations of that tuple contribute, so the amplitude is the permanent-type sum of the
matrix whose `(j, l)` entry is the `j`-th carrier's amplitude at the `l`-th index times the `l`-th
frequency to the `j`-th order.

With one carrier the amplitude factors out and the sum is a symmetric function of the frequencies;
with several it does not, and the block structure of the carriers is what makes the permanent
factor. -/
theorem fiberAmplitude_blockMonomial {omega : ι → ℝ} (h : RationallyIndependentSequence omega)
    {M : ℕ} (b : Fin M → ι → ℂ) (s : Fin M → ℕ) {i : Fin M → ι} (hi : Function.Injective i) :
    fiberAmplitude
        (fun n : Fin M → ι => ∏ j, b j (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j)
        (tupleFrequency omega) (tupleFrequency omega i)
      = ∑ sigma : Equiv.Perm (Fin M),
          ∏ j, b j (i (sigma j)) * (Complex.I * (omega (i (sigma j)) : ℂ)) ^ s j := by
  classical
  set B : (Fin M → ι) → ℂ :=
    fun n => ∏ j, b j (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j with hB
  have hstep : fiberAmplitude B (tupleFrequency omega) (tupleFrequency omega i)
      = ∑' sigma : Equiv.Perm (Fin M), B (fun j => i (sigma j)) := by
    rw [fiberAmplitude, ← (fiberPermEquiv h hi).tsum_eq (fun n => B (n : Fin M → ι))]
    exact tsum_congr fun sigma => rfl
  rw [hstep, tsum_fintype]

end

end GaloisForLFunctions.HTGeometry
