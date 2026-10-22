import GaloisForLFunctions.RHTower.CCM.CCMEulerDenominatorCarrier

/-!
# Eventual carrier rigidity for the actual finite Euler denominators

Deleting any finite initial collection of stages does not restore a nonzero
fixed Sonin-carrier core. The initial vector need not have a Fourier gap: apply
the initial finite denominator first, then use all new genuine primes. Every
finite collection of stage conditions nevertheless has a nonzero solution.
-/

noncomputable section

open IsDedekindDomain MeasureTheory
open scoped BigOperators Classical

namespace RHTower

private def eulerPrime (v : HeightOneSpectrum ℤ) : ℕ :=
  Rat.HeightOneSpectrum.primesEquiv v

private theorem eulerPrime_one_lt (v : HeightOneSpectrum ℤ) : 1 < eulerPrime v :=
  (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt

/-- Genuine prime insertion agrees with multiplication of the actual physical factors. -/
theorem ccmFiniteEulerDenominator_insert (S : Finset (HeightOneSpectrum ℤ))
    (v : HeightOneSpectrum ℤ) (hv : v ∉ S) :
    ccmFiniteEulerDenominator (insert v S) =
      ccmPlaceEulerDenominator v * ccmFiniteEulerDenominator S := by
  apply ContinuousLinearMap.ext
  intro f
  apply archimedeanMellinUnitary.injective
  change archimedeanMellinUnitary (ccmFiniteEulerDenominator (insert v S) f) =
    archimedeanMellinUnitary (ccmPlaceEulerDenominator v (ccmFiniteEulerDenominator S f))
  apply Lp.ext
  filter_upwards [mellin_ccmFiniteEulerDenominator_ae (insert v S) f,
    mellin_evenPrimeLocalFactor_ae (eulerPrime v : ℝ)
      (by exact_mod_cast eulerPrime_one_lt v) (ccmFiniteEulerDenominator S f),
    mellin_ccmFiniteEulerDenominator_ae S f] with t hfull hhead htail
  change archimedeanMellinUnitary
    (ccmPlaceEulerDenominator v (ccmFiniteEulerDenominator S f)) t = _ at hhead
  rw [hfull, hhead, htail]
  change (∏ w ∈ insert v S, semilocalPrimeSymbol (eulerPrime w : ℝ) t) *
      archimedeanMellinUnitary f t =
    semilocalPrimeSymbol (eulerPrime v : ℝ) t *
      ((∏ w ∈ S, semilocalPrimeSymbol (eulerPrime w : ℝ) t) * archimedeanMellinUnitary f t)
  rw [Finset.prod_insert hv, mul_assoc]

/-- Finite Euler inversion is valid without a uniform inverse estimate. -/
theorem ccmFiniteEulerDenominator_isUnit (S : Finset (HeightOneSpectrum ℤ)) :
    IsUnit (ccmFiniteEulerDenominator S) := by
  have hlist : ∀ l : List (HeightOneSpectrum ℤ),
      IsUnit (l.map ccmPlaceEulerDenominator).prod := by
    intro l
    induction l with
    | nil => simp
    | cons v l ih =>
      have hv : IsUnit (ccmPlaceEulerDenominator v) :=
        evenPrimeLocalFactor_isUnit (eulerPrime v : ℝ) (by exact_mod_cast eulerPrime_one_lt v)
      simpa only [List.map_cons, List.prod_cons] using hv.mul ih
  exact hlist S.toList

private theorem exists_new_prime_above (S : Finset (HeightOneSpectrum ℤ)) (r : ℝ) :
    ∃ v : HeightOneSpectrum ℤ, v ∉ S ∧ r < (eulerPrime v : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (n + ∑ v ∈ S, eulerPrime v + 1)
  let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩
  have hprime : eulerPrime v = p := by simp only [eulerPrime, v, Equiv.apply_symm_apply]
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hle := Finset.single_le_sum (fun w (_ : w ∈ S) => Nat.zero_le (eulerPrime w)) hv
    rw [hprime] at hle
    omega
  · rw [hprime]
    have hnp : n ≤ p := by omega
    exact hn.trans_le (by exact_mod_cast hnp)

private theorem fourierGap_mono {a b : ℝ} (hab : a ≤ b) {f : evenSubspace}
    (hf : evenFourierCutoff b f = 0) : evenFourierCutoff a f = 0 := by
  calc
    evenFourierCutoff a f = evenFourierCutoff a (evenFourierCutoff b f) :=
      (DFunLike.congr_fun (evenFourierCutoff_mul_of_le a b hab) f).symm
    _ = 0 := by rw [hf, map_zero]

/-- Exact eventual-admission classification, with no initial carrier or gap premise. -/
theorem ccmFiniteEulerDenominator_eventual_soninCarrier_iff_zero
    {b : ℝ} (hb : 0 < b) (f : evenSubspace) :
    (∃ S₀ : Finset (HeightOneSpectrum ℤ), ∀ S : Finset (HeightOneSpectrum ℤ),
      S₀ ⊆ S → ccmFiniteEulerDenominator S f ∈ evenCentralSoninCarrier b) ↔ f = 0 := by
  constructor
  · rintro ⟨S₀, hS₀⟩
    let g := ccmFiniteEulerDenominator S₀ f
    have hg : g ∈ evenCentralSoninCarrier b := hS₀ S₀ (fun _ h => h)
    have hgGap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b g).mp hg).2
    have hgzero : g = 0 := by
      apply (ccmFiniteEulerDenominator_common_soninCarrier_iff_zero hb g).mp
      intro T
      apply (ccmFiniteEulerDenominator_mem_soninCarrier_iff T hb hg).mpr
      obtain ⟨v, hv, hscale⟩ := exists_new_prime_above S₀ (ccmFiniteEulerCarrierScale T)
      have hnew : ccmPlaceEulerDenominator v g ∈ evenCentralSoninCarrier b := by
        have h := hS₀ (insert v S₀) (Finset.subset_insert v S₀)
        rw [ccmFiniteEulerDenominator_insert S₀ v hv] at h
        exact h
      have hgap : evenFourierCutoff ((eulerPrime v : ℝ) * b) g = 0 := by
        apply (evenPrimeLocalFactor_fourierGap_iff_of_gap (eulerPrime v : ℝ)
          (by exact_mod_cast eulerPrime_one_lt v) b hgGap).mp
        exact ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b _).mp hnew).2
      exact fourierGap_mono (mul_le_mul_of_nonneg_right hscale.le hb.le) hgap
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp
      (ccmFiniteEulerDenominator_isUnit S₀)).1
    exact hinj (hgzero.trans (map_zero _).symm)
  · rintro rfl
    refine ⟨∅, fun S _ => ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem _

/-- Positive survivor: every finite collection of actual stage conditions has a nonzero solution. -/
theorem ccmFiniteEulerDenominator_finiteFamily_commonCarrier
    (F : Finset (Finset (HeightOneSpectrum ℤ))) {b : ℝ} (hb : 0 < b) :
    ∃ f : evenSubspace, f ≠ 0 ∧ f ∈ evenCentralSoninCarrier b ∧
      ∀ S ∈ F, ccmFiniteEulerDenominator S f ∈ evenCentralSoninCarrier b := by
  let c := b + ∑ S ∈ F, max 0 (ccmFiniteEulerCarrierScale S * b)
  have hsum : 0 ≤ ∑ S ∈ F, max 0 (ccmFiniteEulerCarrierScale S * b) :=
    Finset.sum_nonneg fun S _ => le_max_left _ _
  have hbc : b ≤ c := by dsimp only [c]; linarith
  obtain ⟨f, hf0, hfc, _⟩ :=
    ccmFiniteEulerDenominator_exists_nonzero_commonCarrier ∅ (hb.trans_le hbc)
  have hfb := evenCentralSoninCarrier_antitone hbc hfc
  refine ⟨f, hf0, hfb, fun S hS => ?_⟩
  apply (ccmFiniteEulerDenominator_mem_soninCarrier_iff S hb hfb).mpr
  have hSc : ccmFiniteEulerCarrierScale S * b ≤ c := by
    have hs := Finset.single_le_sum (fun T (_ : T ∈ F) =>
      le_max_left 0 (ccmFiniteEulerCarrierScale T * b)) hS
    have hm := le_max_right 0 (ccmFiniteEulerCarrierScale S * b)
    dsimp only [c]
    linarith
  exact fourierGap_mono hSc
    ((mem_evenCentralSoninCarrier_iff_cutoffs_zero c f).mp hfc).2

end RHTower
