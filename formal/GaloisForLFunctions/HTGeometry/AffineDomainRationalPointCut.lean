import GaloisForLFunctions.HTGeometry.NoetherNormalizationKrullDim
import GaloisForLFunctions.HTGeometry.RegularLocalDomain
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Cutting an affine domain by a function vanishing at a rational point

Let `B` be a finitely generated domain over a field `K`, `ε : B → K` a `K`-point and `f ≠ 0` a
function with `ε(f) = 0`. Then `dim B ≤ dim B/(f) + 1`
(`ringKrullDim_le_quotient_add_one_of_rationalPoint`).

**Proof.**
* Choose a Noether normalization `K[t_1, …, t_s] ⊆ B`, so `dim B = s`. Going down holds,
  since the base is integrally closed and `B` is torsion-free.
* The point `ε` lies over the rational point `q = ε(g(t))`, whose maximal ideal in `K[t]` ends
  the explicit chain of kernels of the partial evaluations `t_i ↦ q_i (i < k)`, of length `s`.
* Going down lifts this chain to a chain in `B` of length `s` ending at `M = ker ε`, so
  `dim B_M = ht M ≥ s`.
* In the local domain `B_M` the element `f` is a nonzero element of the maximal ideal, so
  `dim B_M/(f) + 1 = dim B_M` (`ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes`).
* Finally `B_M/(f)` is a localization of `B/(f)`, so its dimension is at most `dim B/(f)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The partial evaluation `t_i ↦ q_i` for `i < k`. -/
def partialEval {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) (k : ℕ) :
    MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin s) K :=
  aeval fun i => if (i : ℕ) < k then C (q i) else X i

theorem partialEval_succ {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) (k : ℕ) :
    partialEval q (k + 1) =
      (aeval fun i : Fin s => if (i : ℕ) = k then C (q i) else X i).comp (partialEval q k) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [partialEval, AlgHom.comp_apply, aeval_X]
  by_cases h1 : (i : ℕ) < k
  · rw [if_pos (by omega), if_pos h1, aeval_C, algebraMap_eq]
  · rw [if_neg h1]
    simp only [aeval_X]
    by_cases h2 : (i : ℕ) = k
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

theorem ker_partialEval_mono {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) (k : ℕ) :
    RingHom.ker (partialEval q k) ≤ RingHom.ker (partialEval q (k + 1)) := by
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  rw [partialEval_succ, AlgHom.comp_apply]
  erw [hp]
  exact map_zero _

theorem ker_partialEval_lt {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) (k : Fin s) :
    RingHom.ker (partialEval q k) < RingHom.ker (partialEval q (k + 1)) := by
  refine lt_of_le_of_ne (ker_partialEval_mono q k) fun h => ?_
  have hmem : X k - C (q k) ∈ RingHom.ker (partialEval q (k + 1)) := by
    rw [RingHom.mem_ker, map_sub, partialEval, aeval_X, aeval_C, if_pos (by omega)]
    simp
  rw [← h, RingHom.mem_ker, map_sub, partialEval, aeval_X, aeval_C, if_neg (lt_irrefl _),
    algebraMap_eq, sub_eq_zero] at hmem
  have := congrArg (MvPolynomial.totalDegree) hmem
  rw [totalDegree_X, totalDegree_C] at this
  exact one_ne_zero this

theorem ker_partialEval_full {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) :
    RingHom.ker (partialEval q s) = RingHom.ker (aeval q : MvPolynomial (Fin s) K →ₐ[K] K) := by
  have h : partialEval q s = (Algebra.ofId K (MvPolynomial (Fin s) K)).comp (aeval q) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [partialEval, aeval_X, AlgHom.comp_apply, if_pos i.2, Algebra.ofId_apply,
      algebraMap_eq]
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, h, AlgHom.comp_apply, Algebra.ofId_apply,
    algebraMap_eq, C_eq_zero]

/-- The chain of partial-evaluation kernels, of length `s`, ending at the point ideal of `q`. -/
def partialEvalSeries {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) :
    LTSeries (PrimeSpectrum (MvPolynomial (Fin s) K)) :=
  LTSeries.mk s (fun k => ⟨RingHom.ker (partialEval q k), RingHom.ker_isPrime _⟩)
    (Fin.strictMono_iff_lt_succ.mpr fun k => by
      change RingHom.ker (partialEval q k) < RingHom.ker (partialEval q (k + 1))
      exact ker_partialEval_lt q k)

theorem partialEvalSeries_last {K : Type*} [Field K] {s : ℕ} (q : Fin s → K) :
    (partialEvalSeries q).last.asIdeal = RingHom.ker (aeval q : MvPolynomial (Fin s) K →ₐ[K] K) := by
  rw [← ker_partialEval_full]
  rfl

/-- **Cutting by a function vanishing at a rational point.** -/
theorem ringKrullDim_le_quotient_add_one_of_rationalPoint {K B : Type*} [Field K] [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (ε : B →ₐ[K] K) {f : B} (hf0 : f ≠ 0)
    (hf : ε f = 0) : ringKrullDim B ≤ ringKrullDim (B ⧸ Ideal.span {f}) + 1 := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  have hdimB := ringKrullDim_eq_of_noetherNormalization g hinj hint
  -- the base `K[t]` and going down
  letI : Algebra (MvPolynomial (Fin s) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) B := ⟨fun x => hint x⟩
  haveI : Module.IsTorsionFree (MvPolynomial (Fin s) K) B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin s) K) B := inferInstance
  -- the point
  set M : Ideal B := RingHom.ker ε with hM
  have hεsurj : Function.Surjective ε := fun c => ⟨algebraMap K B c, by simp⟩
  haveI hMmax : M.IsMaximal := RingHom.ker_isMaximal_of_surjective ε hεsurj
  haveI : M.IsPrime := hMmax.isPrime
  set q : Fin s → K := fun i => ε (g (X i)) with hq
  have hcomap : M.comap (algebraMap (MvPolynomial (Fin s) K) B) =
      RingHom.ker (aeval q : MvPolynomial (Fin s) K →ₐ[K] K) := by
    have h : (ε.comp g) = aeval q := MvPolynomial.algHom_ext fun i => by simp [hq]
    ext p
    rw [Ideal.mem_comap, hM, RingHom.mem_ker, RingHom.mem_ker, ← h]
    rfl
  -- the chain lifted by going down
  set l := partialEvalSeries q with hl
  haveI : M.LiesOver l.last.asIdeal := ⟨by rw [partialEvalSeries_last, ← hcomap]⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l M
  have hheight : (s : ℕ∞) ≤ M.height := by
    have h1 := Order.length_le_height_last (p := L)
    rw [hlen, hlast, ← PrimeSpectrum.height_eq_orderHeight] at h1
    simpa [hl, partialEvalSeries] using h1
  -- the local ring at the point
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  set R := Localization.AtPrime M
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing M.primeCompl R inferInstance
  have hdimR : ringKrullDim R = (M.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height M R
  set x : R := algebraMap B R f with hx
  have hxM : x ∈ IsLocalRing.maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (by rw [hM, RingHom.mem_ker]; exact hf)
  have hx0 : x ≠ 0 := by
    have hinjR := IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)
    rw [hx, ← map_zero (algebraMap B R)]
    exact fun h => hf0 (hinjR h)
  have hmin : ∀ p ∈ minimalPrimes R, x ∉ p := by
    intro p hp hxp
    have hp0 : p = ⊥ := by
      rw [IsDomain.minimalPrimes_eq_singleton_bot] at hp
      exact hp
    rw [hp0, Ideal.mem_bot] at hxp
    exact hx0 hxp
  have hcut := ringKrullDim_quotient_span_singleton_succ_of_notMem_minimalPrimes hmin hxM
  -- `R/(x)` is a localization of `B/(f)`
  set ψ : B →+* R ⧸ Ideal.span {x} := (Ideal.Quotient.mk _).comp (algebraMap B R) with hψ
  have hψf : ψ f = 0 := by
    rw [hψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  set ψbar : B ⧸ Ideal.span {f} →+* R ⧸ Ideal.span {x} :=
    Ideal.Quotient.lift _ ψ (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hψf, mul_zero]) with hψbar
  have hmono : StrictMono (PrimeSpectrum.comap ψbar) := by
    refine Monotone.strictMono_of_injective (fun P Q hPQ => Ideal.comap_mono hPQ) ?_
    intro P Q hPQ
    have h1 : P.asIdeal.comap ψ = Q.asIdeal.comap ψ := by
      have e : ψ = ψbar.comp (Ideal.Quotient.mk _) := by
        ext a; simp [hψbar]
      rw [e, ← Ideal.comap_comap, ← Ideal.comap_comap]
      exact congrArg _ (congrArg PrimeSpectrum.asIdeal hPQ)
    rw [hψ, ← Ideal.comap_comap, ← Ideal.comap_comap] at h1
    have h2 := congrArg (Ideal.map (algebraMap B R)) h1
    rw [IsLocalization.map_under M.primeCompl R, IsLocalization.map_under M.primeCompl R] at h2
    have h3 := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {x}))) h2
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h3
    exact PrimeSpectrum.ext h3
  have hle : ringKrullDim (R ⧸ Ideal.span {x}) ≤ ringKrullDim (B ⧸ Ideal.span {f}) :=
    Order.krullDim_le_of_strictMono _ hmono
  calc ringKrullDim B = (s : WithBot ℕ∞) := by rw [hdimB]; rfl
    _ ≤ ringKrullDim R := by rw [hdimR]; exact_mod_cast hheight
    _ = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := hcut.symm
    _ ≤ ringKrullDim (B ⧸ Ideal.span {f}) + 1 := by gcongr

end

end GaloisForLFunctions.HTGeometry
