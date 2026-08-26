import GaloisForLFunctions.RHTower.CenteredRealEvenPolynomialDensity
import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetInterpolation
import GaloisForLFunctions.RHTower.QuartetSymmetryJets

/-!
# Jetwise compact-open density of centered real-even polynomials

For a finite sign- and Schwarz-stable packet, an explicit Hermite basis gives a finite-dimensional
polynomial section of the jet map. Applying that section to the Taylor-approximation jet error
produces a correction converging compact-open to zero. Real-even averaging then preserves both
the exact compatible jets and convergence.
-/

open Complex Filter Set Topology Polynomial Function
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Flattened coordinate type of a finite variable-depth entire jet packet. -/
abbrev FiniteEntireJetCoordinate {ι : Type*} (m : ι → ℕ) :=
  (i : ι) × Fin (m i)

def finiteEntireJetDelta {ι : Type*} {m : ι → ℕ}
    (idx j : FiniteEntireJetCoordinate m) : ℂ := by
  classical
  exact if j = idx then 1 else 0

/-- Polynomial realizing one standard coordinate in a finite Hermite jet packet. -/
def finiteHermiteJetBasisPolynomial {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ)
    (idx : FiniteEntireJetCoordinate m) : Polynomial ℂ := by
  classical
  exact Classical.choose (exists_polynomial_iterateDerivative_eval_eq a ha m
    (fun i => deningerLocalJetPolynomial (a i)
      (fun k => finiteEntireJetDelta idx ⟨i, k⟩)))

@[simp] theorem finiteHermiteJetBasisPolynomial_jet {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ)
    (idx : FiniteEntireJetCoordinate m) (i : ι) (k : Fin (m i)) :
    (derivative^[k.1] (finiteHermiteJetBasisPolynomial a ha m idx)).eval (a i) =
      finiteEntireJetDelta idx ⟨i, k⟩ := by
  classical
  unfold finiteHermiteJetBasisPolynomial
  calc
    _ = (derivative^[k.1]
          (deningerLocalJetPolynomial (a i)
            (fun j => finiteEntireJetDelta idx ⟨i, j⟩))).eval (a i) :=
      Classical.choose_spec (exists_polynomial_iterateDerivative_eval_eq a ha m
        (fun i => deningerLocalJetPolynomial (a i)
          (fun j => finiteEntireJetDelta idx ⟨i, j⟩))) i k.1 k.2
    _ = _ := deningerLocalJetPolynomial_iterateDerivative_eval
      (a i) (fun j => finiteEntireJetDelta idx ⟨i, j⟩) k.2

/-- Linear polynomial Hermite section assembled from the standard-coordinate basis. -/
def finiteHermiteJetSectionPolynomial {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ)
    (v : FiniteEntireJetCoordinate m → ℂ) : Polynomial ℂ := by
  classical
  exact ∑ idx, C (v idx) * finiteHermiteJetBasisPolynomial a ha m idx

@[simp] theorem finiteHermiteJetSectionPolynomial_jet {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ)
    (v : FiniteEntireJetCoordinate m → ℂ) (i : ι) (k : Fin (m i)) :
    (derivative^[k.1] (finiteHermiteJetSectionPolynomial a ha m v)).eval (a i) =
      v ⟨i, k⟩ := by
  classical
  rw [finiteHermiteJetSectionPolynomial, iterate_derivative_sum,
    Polynomial.eval_finsetSum]
  simp only [iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    finiteHermiteJetBasisPolynomial_jet]
  rw [Finset.sum_eq_single ⟨i, k⟩]
  · simp [finiteEntireJetDelta]
  · intro j hj hne
    simp [finiteEntireJetDelta, Ne.symm hne]
  · simp

/-- Bundle an entire function as a compact-open source. -/
def deningerCompactOpenOfEntire (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    DeningerCompactOpenEntire :=
  ⟨⟨f, hf.continuous⟩, hf⟩

/-- Locally uniform polynomial convergence is convergence in the compact-open entire source. -/
theorem deningerCompactOpenPolynomial_tendsto_of_locallyUniform
    {P : ℕ → Polynomial ℂ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : TendstoLocallyUniformly (fun n z => (P n).eval z) f atTop) :
    Tendsto (fun n => deningerCompactOpenPolynomial (P n)) atTop
      (𝓝 (deningerCompactOpenOfEntire f hf)) := by
  rw [tendsto_subtype_rng]
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  simpa [deningerCompactOpenPolynomial, deningerCompactOpenOfEntire] using h

/-- Coordinatewise-vanishing finite jet data have compact-open-vanishing polynomial sections. -/
theorem finiteHermiteJetSectionPolynomial_tendstoLocallyUniformly_zero
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ)
    {v : ℕ → FiniteEntireJetCoordinate m → ℂ}
    (hv : ∀ idx, Tendsto (fun n => v n idx) atTop (𝓝 0)) :
    TendstoLocallyUniformly
      (fun n z => (finiteHermiteJetSectionPolynomial a ha m (v n)).eval z)
      (fun _ => 0) atTop := by
  let B : FiniteEntireJetCoordinate m → DeningerCompactOpenEntire := fun idx =>
    deningerCompactOpenPolynomial (finiteHermiteJetBasisPolynomial a ha m idx)
  have hsum : Tendsto
      (fun n => ∑ idx, v n idx • B idx) atTop
      (𝓝 (∑ idx, (0 : ℂ) • B idx)) := by
    apply tendsto_finsetSum Finset.univ
    intro idx hidx
    exact (hv idx).smul_const (B idx)
  have hsource : Tendsto
      (fun n => deningerCompactOpenPolynomial
        (finiteHermiteJetSectionPolynomial a ha m (v n))) atTop
      (𝓝 (0 : DeningerCompactOpenEntire)) := by
    convert hsum using 1
    · funext n
      ext z
      change deningerCompactOpenEvaluation z
          (deningerCompactOpenPolynomial
            (finiteHermiteJetSectionPolynomial a ha m (v n))) =
        deningerCompactOpenEvaluation z (∑ idx, v n idx • B idx)
      rw [map_sum]
      simp only [map_smul, deningerCompactOpenEvaluation_apply, smul_eq_mul]
      dsimp [B]
      change Polynomial.eval z
        (∑ idx ∈ Finset.univ,
          C (v n idx) * finiteHermiteJetBasisPolynomial a ha m idx) =
          ∑ idx ∈ Finset.univ, v n idx * Polynomial.eval z
            (finiteHermiteJetBasisPolynomial a ha m idx)
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro idx hidx
      simp
    · simp
  have hval := (continuous_subtype_val.tendsto (0 : DeningerCompactOpenEntire)).comp hsource
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hval

/-- Every derivative jet of a Schwarz-real function is Schwarz-real. -/
theorem iteratedDeriv_of_schwarzReal {f : ℂ → ℂ}
    (hschwarz : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n f ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (iteratedDeriv n f z) := by
  have hiter :
      iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
        (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]
  have hfun : (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = f := by
    funext w
    simpa [Function.comp_apply] using (hschwarz ((starRingEnd ℂ) w)).symm
  rw [hfun] at hiter
  have hz := congrFun hiter ((starRingEnd ℂ) z)
  simpa [Function.comp_apply] using hz

/-- Real-even polynomials are compact-open dense inside every compatible finite-jet fiber. -/
theorem exists_realEvenPolynomial_compactOpen_approximation_with_finiteJets
    {ι : Type*} [Fintype ι]
    (negIdx conjIdx : ι ≃ ι) (a : ι → ℂ) (ha : Function.Injective a)
    (m : ι → ℕ)
    (haneg : ∀ i, a (negIdx i) = -a i)
    (haconj : ∀ i, a (conjIdx i) = (starRingEnd ℂ) (a i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z)
    (hschwarz : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ n z, (P n).eval (-z) = (P n).eval z) ∧
      (∀ n z, (P n).eval ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((P n).eval z)) ∧
      (∀ n i k, k < m i →
        (derivative^[k] (P n)).eval (a i) = iteratedDeriv k f (a i)) ∧
      TendstoLocallyUniformly (fun n z => (P n).eval z) f atTop := by
  let T : ℕ → Polynomial ℂ := fun n => polynomialRealEvenAverage (entireTaylorPolynomial f n)
  have hT : TendstoLocallyUniformly (fun n z => (T n).eval z) f atTop :=
    polynomialRealEvenAverage_tendstoLocallyUniformly
      (entireTaylorPolynomial_tendstoLocallyUniformly hf) hf.continuous heven hschwarz
  have hTsource := deningerCompactOpenPolynomial_tendsto_of_locallyUniform hf hT
  let e : ℕ → FiniteEntireJetCoordinate m → ℂ := fun n idx =>
    iteratedDeriv idx.2.1 f (a idx.1) -
      (derivative^[idx.2.1] (T n)).eval (a idx.1)
  have he : ∀ idx, Tendsto (fun n => e n idx) atTop (𝓝 0) := by
    intro idx
    have hj := ((continuous_deningerCompactOpenJet (a idx.1) idx.2.1).tendsto
      (deningerCompactOpenOfEntire f hf)).comp hTsource
    change Tendsto
      (fun n => deningerCompactOpenJet (a idx.1) idx.2.1
        (deningerCompactOpenPolynomial (T n))) atTop
      (𝓝 (deningerCompactOpenJet (a idx.1) idx.2.1
        (deningerCompactOpenOfEntire f hf))) at hj
    have hj' : Tendsto
        (fun n => (derivative^[idx.2.1] (T n)).eval (a idx.1)) atTop
        (𝓝 (iteratedDeriv idx.2.1 f (a idx.1))) := by
      convert hj using 1
      · funext n
        exact (deningerCompactOpenJet_polynomial (T n) idx.2.1 (a idx.1)).symm
      · rfl
    have hc : Tendsto
        (fun _ : ℕ => iteratedDeriv idx.2.1 f (a idx.1)) atTop
        (𝓝 (iteratedDeriv idx.2.1 f (a idx.1))) := tendsto_const_nhds
    simpa only [e, sub_self] using hc.sub hj'
  let Cseq : ℕ → Polynomial ℂ := fun n => finiteHermiteJetSectionPolynomial a ha m (e n)
  have hC : TendstoLocallyUniformly (fun n z => (Cseq n).eval z) (fun _ => 0) atTop :=
    finiteHermiteJetSectionPolynomial_tendstoLocallyUniformly_zero a ha m he
  let Q : ℕ → Polynomial ℂ := fun n => T n + Cseq n
  have hQ : TendstoLocallyUniformly (fun n z => (Q n).eval z) f atTop := by
    have hadd := hT.add hC
    convert hadd using 1
    · funext n z
      simp [Q]
    · funext z
      simp
  have hQjet : ∀ n i k, k < m i →
      (derivative^[k] (Q n)).eval (a i) = iteratedDeriv k f (a i) := by
    intro n i k hk
    change (derivative^[k] (T n + Cseq n)).eval (a i) = _
    rw [iterate_map_add, Polynomial.eval_add,
      finiteHermiteJetSectionPolynomial_jet a ha m (e n) i ⟨k, hk⟩]
    simp [e]
  let target : ι → Polynomial ℂ := fun i =>
    deningerLocalJetPolynomial (a i)
      (fun k : Fin (m i) => iteratedDeriv k.1 f (a i))
  have htarget : ∀ i k, k < m i →
      (derivative^[k] (target i)).eval (a i) = iteratedDeriv k f (a i) := by
    intro i k hk
    exact deningerLocalJetPolynomial_iterateDerivative_eval
      (a i) (fun k => iteratedDeriv k.1 f (a i)) hk
  have htargetNeg : ∀ i k, k < m i →
      (derivative^[k] (target (negIdx i))).eval (a (negIdx i)) =
        (-1 : ℂ) ^ k * (derivative^[k] (target i)).eval (a i) := by
    intro i k hk
    rw [htarget i k hk]
    have hkneg : k < m (negIdx i) := by rwa [hmneg]
    rw [htarget (negIdx i) k hkneg, haneg]
    exact iteratedDeriv_of_even hf heven k (a i)
  have htargetConj : ∀ i k, k < m i →
      (derivative^[k] (target (conjIdx i))).eval (a (conjIdx i)) =
        (starRingEnd ℂ) ((derivative^[k] (target i)).eval (a i)) := by
    intro i k hk
    rw [htarget i k hk]
    have hkconj : k < m (conjIdx i) := by rwa [hmconj]
    rw [htarget (conjIdx i) k hkconj, haconj]
    exact iteratedDeriv_of_schwarzReal hschwarz k (a i)
  let P : ℕ → Polynomial ℂ := fun n => polynomialRealEvenAverage (Q n)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact fun n => polynomialRealEvenAverage_eval_neg _
  · exact fun n => polynomialRealEvenAverage_eval_conj _
  · intro n i k hk
    have havg := polynomialRealEvenAverage_preserves_compatible_jets
      negIdx conjIdx a m target haneg haconj hmneg hmconj htargetNeg htargetConj
      (Q n) (fun i k hk => (hQjet n i k hk).trans (htarget i k hk).symm)
      i k hk
    exact havg.trans (htarget i k hk)
  · exact polynomialRealEvenAverage_tendstoLocallyUniformly
      hQ hf.continuous heven hschwarz

end

end RHTower
