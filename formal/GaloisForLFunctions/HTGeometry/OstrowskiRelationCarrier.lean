import GaloisForLFunctions.HTGeometry.MonomialFiberAmplitude
import GaloisForLFunctions.HTGeometry.ExponentialSeriesSigmaSum
import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteVanishing

/-!
# A differential monomial combination of a carrier is one exponential series

Each monomial in the jets of an exponential carrier is an exponential series indexed by tuples, and
a finite combination of them is the exponential series indexed by the disjoint union.

So a vanishing combination has vanishing amplitude at every frequency, and at the frequency of an
injective tuple that amplitude is a symmetric expression in the chosen frequencies.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The amplitude of one monomial in the jets, scaled by its coefficient. -/
def monomialAmplitude (a : ι → ℂ) (omega : ι → ℝ) {M : ℕ} (c : ℂ) (s : Fin M → ℕ)
    (n : Fin M → ι) : ℂ :=
  c * ∏ j, a (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j

omit [DecidableEq ι] in
theorem summable_norm_monomialAmplitude {a : ι → ℂ} {omega : ι → ℝ}
    (ha : ExpSeriesNormallySummable a omega) {M : ℕ} (c : ℂ) (s : Fin M → ℕ) :
    Summable fun n : Fin M → ι => ‖monomialAmplitude a omega c s n‖ := by
  have hjet : ∀ j : Fin M,
      Summable fun i => ‖a i * (Complex.I * (omega i : ℂ)) ^ s j‖ :=
    fun j => summable_norm_of_expSeriesNormallySummable (ha.iteratedDeriv (s j))
  have hprod := summable_norm_prod_expSeries M
    (fun j i => a i * (Complex.I * (omega i : ℂ)) ^ s j) hjet
  have hval : ∀ n : Fin M → ι, ‖monomialAmplitude a omega c s n‖
      = ‖c‖ * ‖∏ j, a (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s j‖ := by
    intro n
    rw [monomialAmplitude, norm_mul]
  simpa only [hval] using hprod.mul_left ‖c‖

omit [DecidableEq ι] in
/-- **A monomial in the jets is an exponential series over tuples.** -/
theorem monomial_eq_expSeriesCarrier {a : ι → ℂ} {omega : ι → ℝ}
    (ha : ExpSeriesNormallySummable a omega) {M : ℕ} (c : ℂ) (s : Fin M → ℕ) (t : ℝ) :
    c * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ)
      = expSeriesCarrier (monomialAmplitude a omega c s) (tupleFrequency omega) t := by
  have hjet : ∀ j : Fin M, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ)
      = expSeriesCarrier (fun i => a i * (Complex.I * (omega i : ℂ)) ^ s j) omega t := by
    intro j
    rw [iteratedDeriv_cexpSeriesCarrier (s j) ha, cexpSeriesCarrier_ofReal]
  have hsum : ∀ j : Fin M, Summable fun i => ‖a i * (Complex.I * (omega i : ℂ)) ^ s j‖ :=
    fun j => summable_norm_of_expSeriesNormallySummable (ha.iteratedDeriv (s j))
  rw [Finset.prod_congr rfl fun j _ => hjet j,
    prod_expSeriesCarrier M (fun j i => a i * (Complex.I * (omega i : ℂ)) ^ s j) omega hsum t,
    const_mul_expSeriesCarrier]
  rfl

omit [DecidableEq ι] in
/-- **A vanishing combination of monomials is a vanishing exponential series.** -/
theorem expSeriesCarrier_sigma_eq_zero {a : ι → ℂ} {omega : ι → ℝ}
    (ha : ExpSeriesNormallySummable a omega) {M : ℕ} {K : Finset (Fin M → ℕ)}
    (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ,
      ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ) = 0)
    (t : ℝ) :
    expSeriesCarrier
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
          monomialAmplitude a omega (c p.1.1) p.1.1 p.2)
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t = 0 := by
  have hnorm : ∀ s : {s // s ∈ K},
      Summable fun n : Fin M → ι => ‖monomialAmplitude a omega (c s.1) s.1 n‖ :=
    fun s => summable_norm_monomialAmplitude ha (c s.1) s.1
  rw [← sum_expSeriesCarrier (fun s : {s // s ∈ K} => monomialAmplitude a omega (c s.1) s.1)
    (fun _ : {s // s ∈ K} => tupleFrequency omega) hnorm t]
  have hterm : ∀ s : {s // s ∈ K},
      expSeriesCarrier (monomialAmplitude a omega (c s.1) s.1) (tupleFrequency omega) t
        = c s.1 * ∏ j, iteratedDeriv (s.1 j) (cexpSeriesCarrier a omega) (t : ℂ) :=
    fun s => (monomial_eq_expSeriesCarrier ha (c s.1) s.1 t).symm
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  have hz := hzero t
  rw [← Finset.sum_coe_sort K
    (fun s => c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ))] at hz
  exact hz

/-! ## The coefficients of a vanishing combination -/

set_option maxHeartbeats 1600000 in
/-- **At the frequency of an injective tuple, a vanishing combination gives a polynomial
identity.** -/
theorem eval_permSum_combination_eq_zero {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (ha : ExpSeriesNormallySummable a omega)
    {M : ℕ} {K : Finset (Fin M → ℕ)} (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ,
      ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ) = 0)
    {i : Fin M → ι} (hi : Function.Injective i) (hane : ∀ l, a (i l) ≠ 0) :
    MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (∑ s ∈ K, c s • permSum s) = 0 := by
  classical
  have hnorm : ∀ s : {s // s ∈ K},
      Summable fun n : Fin M → ι => ‖monomialAmplitude a omega (c s.1) s.1 n‖ :=
    fun s => summable_norm_monomialAmplitude ha (c s.1) s.1
  have hfib := fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero
    (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => monomialAmplitude a omega (c p.1.1) p.1.1 p.2)
    (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2)
    (summable_norm_sigma hnorm) (expSeriesCarrier_sigma_eq_zero ha c hzero)
    (tupleFrequency omega i)
  rw [fiberAmplitude_sigma (fun s : {s // s ∈ K} => monomialAmplitude a omega (c s.1) s.1)
    (fun _ : {s // s ∈ K} => tupleFrequency omega) hnorm] at hfib
  have hterm : ∀ s : {s // s ∈ K},
      fiberAmplitude (monomialAmplitude a omega (c s.1) s.1) (tupleFrequency omega)
          (tupleFrequency omega i)
        = c s.1 * ((∏ l, a (i l)) *
          MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (permSum s.1)) := by
    intro s
    rw [show monomialAmplitude a omega (c s.1) s.1
        = fun n : Fin M → ι => c s.1 * ∏ j, a (n j) * (Complex.I * (omega (n j) : ℂ)) ^ s.1 j from
      rfl, fiberAmplitude_const_mul, fiberAmplitude_monomial hom a s.1 hi]
  rw [Finset.sum_congr rfl fun s _ => hterm s] at hfib
  have hsplit : ∑ s : {s // s ∈ K}, c s.1 * ((∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (permSum s.1))
      = (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ))
          (∑ s ∈ K, c s • permSum s) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_coe_sort K
      (fun s => (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ)) (c s • permSum s))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  rw [hsplit] at hfib
  have hprodne : (∏ l, a (i l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hane l
  exact (mul_eq_zero.mp hfib).resolve_left hprodne

end

end GaloisForLFunctions.HTGeometry
