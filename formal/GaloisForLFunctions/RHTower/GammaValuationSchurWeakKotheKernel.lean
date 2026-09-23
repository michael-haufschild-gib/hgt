import GaloisForLFunctions.RHTower.GammaValuationSchurKotheVectorNoGoDualSurvivor

/-!
# Weak Köthe completion of the Gamma-valuation Schur kernel

The valuation-axis coefficients of a rapid Deninger test are summed layer by layer.  Their weak
Gram form is absolutely summable, continuous with respect to the zeroth height seminorm on both
inputs, and has a nonnegative quadratic energy.

Although P-G76 proves that each prime's coherent valuation prefixes are not Köthe-Cauchy as
vectors, their pairings through this weak kernel converge to the exact two-prime
Gamma-valuation Szegő covariance.  This constructs the forced mixed completion `K_H -> K_H'` and
realizes cofinal Schur translation weakly before scalar compression.

No Xi zero, RH premise, numerical computation, fitted parameter, or added axiom enters.
-/

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

def gammaValuationLayerSum (e : ℕ) (a : DeningerHeightKothe) : ℂ :=
  ∑' p : Nat.Primes,
    (a : DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))

theorem gammaValuationFixedLayerAxis_injective (e : ℕ) :
    Function.Injective
      (fun p : Nat.Primes =>
        gammaSewnMobiusApertureStokesPrimePowerAxis (p, e)) := by
  intro p q h
  have hpq := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact congrArg Prod.fst hpq

theorem summable_gammaValuationLayerSum
    (e : ℕ) (a : DeningerHeightKothe) :
    Summable (fun p : Nat.Primes =>
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))) := by
  exact Summable.of_norm_bounded
    ((deningerHeightKothe_summable_norm a).comp_injective
      (gammaValuationFixedLayerAxis_injective e)) (fun _ => le_rfl)

theorem gammaValuationProdSwap_injective :
    Function.Injective (fun ep : ℕ × Nat.Primes => (ep.2, ep.1)) := by
  rintro ⟨e, p⟩ ⟨f, q⟩ h
  simpa only [Prod.mk.injEq, and_comm] using h

theorem norm_gammaValuationLayerSum_le_axisNorm
    (e : ℕ) (a : DeningerHeightKothe) :
    ‖gammaValuationLayerSum e a‖ ≤
      ∑' p : Nat.Primes,
        ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖ := by
  exact norm_tsum_le_tsum_norm
    (summable_gammaValuationLayerSum e a).norm

theorem summable_gammaValuationAxisNorm_prod
    (a : DeningerHeightKothe) :
    Summable (fun ep : ℕ × Nat.Primes =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis (ep.2, ep.1))‖) := by
  have hpair : Summable (fun pe : Nat.Primes × ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pe)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      gammaSewnMobiusApertureStokesPrimePowerAxis_injective
  exact hpair.comp_injective gammaValuationProdSwap_injective

theorem summable_norm_gammaValuationLayerSum (a : DeningerHeightKothe) :
    Summable (fun e : ℕ => ‖gammaValuationLayerSum e a‖) := by
  have hprod := summable_gammaValuationAxisNorm_prod a
  have hslices : Summable (fun e : ℕ =>
      ∑' p : Nat.Primes,
        ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖) := hprod.prod
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun e => norm_gammaValuationLayerSum_le_axisNorm e a) hslices

theorem tsum_norm_gammaValuationLayerSum_le (a : DeningerHeightKothe) :
    ∑' e : ℕ, ‖gammaValuationLayerSum e a‖ ≤ deningerHeightSeminorm 0 a := by
  have hprod := summable_gammaValuationAxisNorm_prod a
  have hslices : Summable (fun e : ℕ =>
      ∑' p : Nat.Primes,
        ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖) := hprod.prod
  calc
    ∑' e : ℕ, ‖gammaValuationLayerSum e a‖ ≤
        ∑' e : ℕ, ∑' p : Nat.Primes,
          ‖(a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖ :=
      Summable.tsum_le_tsum
        (fun e => norm_gammaValuationLayerSum_le_axisNorm e a)
        (summable_norm_gammaValuationLayerSum a) hslices
    _ = ∑' ep : ℕ × Nat.Primes,
          ‖(a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesPrimePowerAxis (ep.2, ep.1))‖ :=
      hprod.tsum_prod.symm
    _ ≤ ∑' m : DeningerPrimeLattice,
          ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
      exact hprod.tsum_le_tsum_of_inj
        (fun ep : ℕ × Nat.Primes =>
          gammaSewnMobiusApertureStokesPrimePowerAxis (ep.2, ep.1))
        (gammaSewnMobiusApertureStokesPrimePowerAxis_injective.comp
          gammaValuationProdSwap_injective)
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (deningerHeightKothe_summable_norm a)
    _ = deningerHeightSeminorm 0 a := (deningerHeightSeminorm_zero_eq a).symm

def gammaValuationWeakKernel
    (a b : DeningerHeightKothe) : ℂ :=
  ∑' e : ℕ, conj (gammaValuationLayerSum e a) * gammaValuationLayerSum e b

theorem summable_gammaValuationWeakKernel
    (a b : DeningerHeightKothe) :
    Summable (fun e : ℕ =>
      conj (gammaValuationLayerSum e a) * gammaValuationLayerSum e b) := by
  let C := deningerHeightSeminorm 0 b
  have hC : 0 ≤ C := apply_nonneg _ _
  have ha := summable_norm_gammaValuationLayerSum a
  have hbase : Summable (fun e : ℕ => ‖gammaValuationLayerSum e a‖ * C) :=
    ha.mul_right C
  refine Summable.of_norm_bounded hbase fun e => ?_
  rw [norm_mul, Complex.norm_conj]
  have hb : ‖gammaValuationLayerSum e b‖ ≤ C :=
    (norm_gammaValuationLayerSum_le_axisNorm e b).trans
      (le_trans (Summable.tsum_le_tsum_of_inj
        (fun p : Nat.Primes =>
          gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
        (gammaValuationFixedLayerAxis_injective e)
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        ((deningerHeightKothe_summable_norm b).comp_injective
          (gammaValuationFixedLayerAxis_injective e))
        (deningerHeightKothe_summable_norm b))
        (by simpa [C] using (deningerHeightSeminorm_zero_eq b).symm.le))
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem norm_gammaValuationWeakKernel_le
    (a b : DeningerHeightKothe) :
    ‖gammaValuationWeakKernel a b‖ ≤
      deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b := by
  let C := deningerHeightSeminorm 0 b
  have hC : 0 ≤ C := apply_nonneg _ _
  have hsum := summable_gammaValuationWeakKernel a b
  calc
    ‖gammaValuationWeakKernel a b‖ ≤
        ∑' e : ℕ, ‖conj (gammaValuationLayerSum e a) *
          gammaValuationLayerSum e b‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' e : ℕ, ‖gammaValuationLayerSum e a‖ * C := by
      refine Summable.tsum_le_tsum (fun e => ?_) hsum.norm
        ((summable_norm_gammaValuationLayerSum a).mul_right C)
      rw [norm_mul, Complex.norm_conj]
      gcongr
      exact (norm_gammaValuationLayerSum_le_axisNorm e b).trans
        (le_trans (Summable.tsum_le_tsum_of_inj
          (fun p : Nat.Primes =>
            gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
          (gammaValuationFixedLayerAxis_injective e)
          (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
          ((deningerHeightKothe_summable_norm b).comp_injective
            (gammaValuationFixedLayerAxis_injective e))
          (deningerHeightKothe_summable_norm b))
          (by simpa [C] using (deningerHeightSeminorm_zero_eq b).symm.le))
    _ = (∑' e : ℕ, ‖gammaValuationLayerSum e a‖) * C := tsum_mul_right
    _ ≤ deningerHeightSeminorm 0 a * C :=
      mul_le_mul_of_nonneg_right (tsum_norm_gammaValuationLayerSum_le a) hC
    _ = _ := rfl

def gammaValuationWeakEnergy (a : DeningerHeightKothe) : ℝ :=
  ∑' e : ℕ, ‖gammaValuationLayerSum e a‖ ^ (2 : ℕ)

theorem gammaValuationWeakEnergy_nonneg (a : DeningerHeightKothe) :
    0 ≤ gammaValuationWeakEnergy a := by
  exact tsum_nonneg fun _ => sq_nonneg _

theorem summable_gammaValuationWeakEnergy (a : DeningerHeightKothe) :
    Summable (fun e : ℕ => ‖gammaValuationLayerSum e a‖ ^ (2 : ℕ)) := by
  let C := deningerHeightSeminorm 0 a
  have hC : 0 ≤ C := apply_nonneg _ _
  have hbase : Summable (fun e : ℕ => ‖gammaValuationLayerSum e a‖ * C) :=
    (summable_norm_gammaValuationLayerSum a).mul_right C
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun e => ?_) hbase
  have he : ‖gammaValuationLayerSum e a‖ ≤ C :=
    (le_trans (norm_gammaValuationLayerSum_le_axisNorm e a)
      (Summable.tsum_le_tsum_of_inj
        (fun p : Nat.Primes =>
          gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
        (gammaValuationFixedLayerAxis_injective e)
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        ((deningerHeightKothe_summable_norm a).comp_injective
          (gammaValuationFixedLayerAxis_injective e))
        (deningerHeightKothe_summable_norm a))).trans
      (by simpa [C] using (deningerHeightSeminorm_zero_eq a).symm.le)
  nlinarith [norm_nonneg (gammaValuationLayerSum e a)]

theorem gammaValuationWeakEnergy_le (a : DeningerHeightKothe) :
    gammaValuationWeakEnergy a ≤ deningerHeightSeminorm 0 a ^ (2 : ℕ) := by
  let C := deningerHeightSeminorm 0 a
  have hC : 0 ≤ C := apply_nonneg _ _
  have hE := summable_gammaValuationWeakEnergy a
  have hbase : Summable (fun e : ℕ => ‖gammaValuationLayerSum e a‖ * C) :=
    (summable_norm_gammaValuationLayerSum a).mul_right C
  calc
    gammaValuationWeakEnergy a ≤
        ∑' e : ℕ, ‖gammaValuationLayerSum e a‖ * C := by
      refine Summable.tsum_le_tsum (fun e => ?_) hE hbase
      have he : ‖gammaValuationLayerSum e a‖ ≤ C :=
        (le_trans (norm_gammaValuationLayerSum_le_axisNorm e a)
          (Summable.tsum_le_tsum_of_inj
            (fun p : Nat.Primes =>
              gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
            (gammaValuationFixedLayerAxis_injective e)
            (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
            ((deningerHeightKothe_summable_norm a).comp_injective
              (gammaValuationFixedLayerAxis_injective e))
            (deningerHeightKothe_summable_norm a))).trans
          (by simpa [C] using (deningerHeightSeminorm_zero_eq a).symm.le)
      nlinarith [norm_nonneg (gammaValuationLayerSum e a)]
    _ = (∑' e : ℕ, ‖gammaValuationLayerSum e a‖) * C := tsum_mul_right
    _ ≤ C * C := mul_le_mul_of_nonneg_right
      (by simpa [C] using tsum_norm_gammaValuationLayerSum_le a) hC
    _ = deningerHeightSeminorm 0 a ^ (2 : ℕ) := by simp [C, pow_two]

theorem gammaValuationWeakKernel_self_eq_energy (a : DeningerHeightKothe) :
    gammaValuationWeakKernel a a = (gammaValuationWeakEnergy a : ℂ) := by
  rw [gammaValuationWeakKernel, gammaValuationWeakEnergy, Complex.ofReal_tsum]
  apply tsum_congr
  intro e
  rw [Complex.conj_mul']
  norm_cast

theorem gammaValuationKothePrefix_coord
    (p q : Nat.Primes) (N e : ℕ) :
    ((gammaValuationKothePrefix p N : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (q, e)) =
      if p = q ∧ e < N
      then (xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ)
      else 0 := by
  classical
  simp only [gammaValuationKothePrefix, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, deningerKotheDelta_coe]
  by_cases hpq : p = q
  · subst q
    by_cases he : e < N
    · rw [if_pos ⟨rfl, he⟩]
      rw [Finset.sum_eq_single e]
      · simp
      · intro f hf hfe
        have hpair : (p, f) ≠ (p, e) := by
          intro h
          exact hfe (congrArg Prod.snd h)
        rw [Pi.single_eq_of_ne
          (gammaSewnMobiusApertureStokesPrimePowerAxis_injective.ne hpair).symm]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr he)).elim
    · rw [if_neg (by simp [he])]
      rw [Finset.sum_eq_zero]
      intro f hf
      have hfe : f ≠ e := by
        intro h
        subst f
        exact he (Finset.mem_range.mp hf)
      have hpair : (p, f) ≠ (p, e) := by
        intro h
        exact hfe (congrArg Prod.snd h)
      rw [Pi.single_eq_of_ne
        (gammaSewnMobiusApertureStokesPrimePowerAxis_injective.ne hpair).symm]
      simp
  · rw [if_neg (by simp [hpq])]
    rw [Finset.sum_eq_zero]
    intro f hf
    have hpair : (p, f) ≠ (q, e) := by
      intro h
      exact hpq (congrArg Prod.fst h)
    rw [Pi.single_eq_of_ne
      (gammaSewnMobiusApertureStokesPrimePowerAxis_injective.ne hpair).symm]
    simp

theorem gammaValuationLayerSum_prefix
    (p : Nat.Primes) (N e : ℕ) :
    gammaValuationLayerSum e (gammaValuationKothePrefix p N) =
      if e < N then (xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ)
      else 0 := by
  rw [gammaValuationLayerSum]
  by_cases he : e < N
  · rw [if_pos he, tsum_eq_single p]
    · simp [gammaValuationKothePrefix_coord, he]
    · intro q hqp
      simp [gammaValuationKothePrefix_coord, he, hqp.symm]
  · rw [if_neg he]
    have hzero : (fun q : Nat.Primes =>
        ((gammaValuationKothePrefix p N : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (q, e))) =
        fun _ => 0 := by
      funext q
      simp [gammaValuationKothePrefix_coord, he]
    rw [hzero, tsum_zero]

theorem gammaValuationWeakKernel_prefix_eq_schurPrefix
    (p q : Nat.Primes) (N : ℕ) :
    gammaValuationWeakKernel (gammaValuationKothePrefix p N)
        (gammaValuationKothePrefix q N) =
      (arithmeticSchurPrefixKernel N
        (xiTransversePrimeApertureDiskNode 1 p)
        (xiTransversePrimeApertureDiskNode 1 q)
        (arithmeticPrimeSchurBoundaryAmplitude p)
        (arithmeticPrimeSchurBoundaryAmplitude q) : ℂ) := by
  rw [gammaValuationWeakKernel, tsum_eq_sum (s := Finset.range N)]
  · rw [arithmeticSchurPrefixKernel]
    push_cast
    apply Finset.sum_congr rfl
    intro e he
    rw [gammaValuationLayerSum_prefix, gammaValuationLayerSum_prefix,
      if_pos (Finset.mem_range.mp he), if_pos (Finset.mem_range.mp he),
      arithmeticSchurValuationCoordinate_prime_eq,
      arithmeticSchurValuationCoordinate_prime_eq]
    simp
  · intro e he
    have hN : ¬ e < N := by simpa using he
    rw [gammaValuationLayerSum_prefix, gammaValuationLayerSum_prefix,
      if_neg hN, if_neg hN]
    simp

theorem tendsto_arithmeticPrimeSchurPrefixKernel_atTop
    (p q : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      arithmeticSchurPrefixKernel N
        (xiTransversePrimeApertureDiskNode 1 p)
        (xiTransversePrimeApertureDiskNode 1 q)
        (arithmeticPrimeSchurBoundaryAmplitude p)
        (arithmeticPrimeSchurBoundaryAmplitude q)) atTop
      (𝓝 (xiTransverseGammaValuationSzegoKernel p q)) := by
  let K := xiTransverseGammaValuationSzegoKernel p q
  let x := xiTransversePrimeApertureDiskNode 1 p
  let y := xiTransversePrimeApertureDiskNode 1 q
  have hres : Tendsto (fun N : ℕ => (x * y) ^ N * K) atTop (𝓝 0) := by
    simpa [x, y, K] using
      tendsto_xiTransverseGammaValuationSzegoKernel_residual_atTop p q
  have heq : (fun N : ℕ =>
      arithmeticSchurPrefixKernel N x y
        (arithmeticPrimeSchurBoundaryAmplitude p)
        (arithmeticPrimeSchurBoundaryAmplitude q)) =
      (fun N : ℕ => K - (x * y) ^ N * K) := by
    funext N
    have hid := xiTransverseGammaValuationSzegoKernel_sub_prefix_eq_residual N p q
    have hid' : K - arithmeticSchurPrefixKernel N x y
        (arithmeticPrimeSchurBoundaryAmplitude p)
        (arithmeticPrimeSchurBoundaryAmplitude q) = (x * y) ^ N * K := by
      simpa only [K, x, y, arithmeticSchurPrefixKernel,
        arithmeticSchurValuationCoordinate_prime_eq] using hid
    linarith
  rw [heq]
  simpa using (tendsto_const_nhds.sub hres)

theorem tendsto_gammaValuationWeakKernel_prefix_atTop
    (p q : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      gammaValuationWeakKernel (gammaValuationKothePrefix p N)
        (gammaValuationKothePrefix q N)) atTop
      (𝓝 (xiTransverseGammaValuationSzegoKernel p q : ℂ)) := by
  have hreal := tendsto_arithmeticPrimeSchurPrefixKernel_atTop p q
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr'
  filter_upwards with N
  rw [gammaValuationWeakKernel_prefix_eq_schurPrefix]
  rfl

end

end RHTower
