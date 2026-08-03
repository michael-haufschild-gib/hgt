import GaloisForLFunctions.HTGeometry.MonomialFiberAmplitude
import GaloisForLFunctions.HTGeometry.ExponentialSeriesSigmaSum
import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteVanishing
import GaloisForLFunctions.HTGeometry.PolynomialBohrVanishing

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
/-- **A finite combination of monomials is one exponential series.** -/
theorem monomialCombination_eq_expSeriesCarrier {a : ι → ℂ} {omega : ι → ℝ}
    (ha : ExpSeriesNormallySummable a omega) {M : ℕ} {K : Finset (Fin M → ℕ)}
    (c : (Fin M → ℕ) → ℂ) (t : ℝ) :
    ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ)
      = expSeriesCarrier
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
          monomialAmplitude a omega (c p.1.1) p.1.1 p.2)
        (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t := by
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
  exact (Finset.sum_coe_sort K
    (fun s => c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ))).symm

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
  rw [← monomialCombination_eq_expSeriesCarrier ha c t]
  exact hzero t

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
  have hvan : ∀ t : ℝ, expSeriesCarrier
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => monomialAmplitude a omega (c p.1.1) p.1.1 p.2)
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) t = 0 :=
    fun t => expSeriesCarrier_sigma_eq_zero ha c hzero t
  have hsum : Summable fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
      ‖monomialAmplitude a omega (c p.1.1) p.1.1 p.2‖ :=
    summable_norm_sigma (J := fun _ : {s // s ∈ K} => (Fin M → ι))
      (b := fun s n => monomialAmplitude a omega (c s.1) s.1 n) hnorm
  have hfib := fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero
    (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => monomialAmplitude a omega (c p.1.1) p.1.1 p.2)
    (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2)
    hsum hvan (tupleFrequency omega i)
  rw [fiberAmplitude_sigma (J := fun _ : {s // s ∈ K} => (Fin M → ι))
    (fun s : {s // s ∈ K} => monomialAmplitude a omega (c s.1) s.1)
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
    rw [MvPolynomial.smul_eval]
    ring
  rw [hsplit] at hfib
  have hprodne : (∏ l, a (i l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hane l
  exact (mul_eq_zero.mp hfib).resolve_left hprodne

/-- **Ostrowski's core: a vanishing monomial combination has vanishing coefficients.**  The
frequencies being rationally independent and infinitely many amplitudes nonzero, no nonzero finite
combination of distinct differential monomials of the carrier vanishes identically. -/
theorem eq_zero_of_monomialCombination_vanishing {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (ha : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) {M : ℕ} {K : Finset (Fin M → ℕ)}
    (hdistinct : ∀ s ∈ K, ∀ s' ∈ K, tupleCount s = tupleCount s' → s = s')
    (c : (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ,
      ∑ s ∈ K, c s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ) = 0) :
    ∀ s ∈ K, c s = 0 := by
  classical
  have hmapinj : Function.Injective fun i : ι => Complex.I * (omega i : ℂ) := by
    intro i j hij
    have hreal : ((omega i : ℝ) : ℂ) = ((omega j : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hij
    exact injective_of_rationallyIndependentSequence hom (by exact_mod_cast hreal)
  have hSinf : ((fun i : ι => Complex.I * (omega i : ℂ)) '' {i : ι | a i ≠ 0}).Infinite :=
    hinf.image hmapinj.injOn
  have hQ : (∑ s ∈ K, c s • permSum s) = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow_injective hSinf _ ?_
    intro x hx hxinj
    have hchoice : ∀ l : Fin M, ∃ i₀ : ι, a i₀ ≠ 0 ∧ Complex.I * (omega i₀ : ℂ) = x l := by
      intro l
      obtain ⟨i₀, hi₀, hval⟩ := hx l
      exact ⟨i₀, hi₀, hval⟩
    choose i hi0 hival using hchoice
    have hiinj : Function.Injective i := by
      intro l l' hll
      refine hxinj ?_
      rw [← hival l, ← hival l', hll]
    have hkey := eval_permSum_combination_eq_zero hom ha c hzero hiinj hi0
    rwa [show (fun l => Complex.I * (omega (i l) : ℂ)) = x from funext hival] at hkey
  exact eq_zero_of_permSum_combination c hdistinct hQ

/-! ## Polynomial coefficients -/

omit [DecidableEq ι] in
theorem norm_expSeriesCarrier_le {J : Type*} {B : J → ℂ} {Omega : J → ℝ}
    (hB : Summable fun j => ‖B j‖) (t : ℝ) :
    ‖expSeriesCarrier B Omega t‖ ≤ ∑' j, ‖B j‖ := by
  have hsum : Summable fun j => B j * expChar (Omega j) t := by
    refine Summable.of_norm ?_
    simpa using hB
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · simpa using hB
  · exact le_of_eq (tsum_congr fun j => by simp)

/-- **A polynomial combination of differential monomials of a carrier has zero coefficients.**
The coefficients may be polynomials in the variable: each degree is separated by the top-degree
argument, and each separated combination dies by the frequency argument. -/
theorem eq_zero_of_polynomialMonomialCombination_vanishing {a : ι → ℂ} {omega : ι → ℝ}
    (hom : RationallyIndependentSequence omega) (ha : ExpSeriesNormallySummable a omega)
    (hinf : {i : ι | a i ≠ 0}.Infinite) {M : ℕ} {K : Finset (Fin M → ℕ)}
    (hdistinct : ∀ s ∈ K, ∀ s' ∈ K, tupleCount s = tupleCount s' → s = s')
    (D : ℕ) (c : ℕ → (Fin M → ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ d ∈ Finset.range (D + 1), (t : ℂ) ^ d *
      ∑ s ∈ K, c d s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ) = 0) :
    ∀ d ≤ D, ∀ s ∈ K, c d s = 0 := by
  classical
  set G : ℕ → ℝ → ℂ := fun d t =>
    ∑ s ∈ K, c d s * ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier a omega) (t : ℂ) with hG
  have hnorm : ∀ d : ℕ, Summable fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
      ‖monomialAmplitude a omega (c d p.1.1) p.1.1 p.2‖ := by
    intro d
    exact summable_norm_sigma (J := fun _ : {s // s ∈ K} => (Fin M → ι))
      (b := fun s n => monomialAmplitude a omega (c d s.1) s.1 n)
      fun s => summable_norm_monomialAmplitude ha (c d s.1) s.1
  have hGcarrier : ∀ d : ℕ, G d = expSeriesCarrier
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι =>
        monomialAmplitude a omega (c d p.1.1) p.1.1 p.2)
      (fun p : Σ _ : {s // s ∈ K}, Fin M → ι => tupleFrequency omega p.2) :=
    fun d => funext fun t => monomialCombination_eq_expSeriesCarrier ha (c d) t
  have hap : ∀ d, HTGeometry.IsBohrAlmostPeriodic (G d) := by
    intro d
    rw [hGcarrier d]
    exact isBohrAlmostPeriodic_expSeriesCarrier (hnorm d) _
  have hbdd : ∀ d, ∃ C : ℝ, ∀ t : ℝ, ‖G d t‖ ≤ C := by
    intro d
    refine ⟨∑' p : Σ _ : {s // s ∈ K}, Fin M → ι,
      ‖monomialAmplitude a omega (c d p.1.1) p.1.1 p.2‖, fun t => ?_⟩
    rw [hGcarrier d]
    exact norm_expSeriesCarrier_le (hnorm d) t
  have hGzero := eq_zero_of_polynomialCombination_bohr G hap hbdd D hzero
  intro d hd s hs
  refine eq_zero_of_monomialCombination_vanishing hom ha hinf hdistinct (c d) ?_ s hs
  intro t
  exact congrFun (hGzero d hd) t

end

end GaloisForLFunctions.HTGeometry
