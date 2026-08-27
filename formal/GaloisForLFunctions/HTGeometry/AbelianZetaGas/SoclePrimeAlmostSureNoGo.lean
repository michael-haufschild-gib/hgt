import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SoclePrimePartialLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Almost-sure failure of the centered socle prime series

The local q-Gamma laws are realized on their honest prime-indexed Kolmogorov product space. Every
finite cutoff sum has exactly the previously constructed `soclePrimePartialLaw`. Almost-sure
convergence would therefore imply weak convergence of those laws, contradicting the distributional
no-go in the condensed chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

private def soclePrimeCutoffEquiv (P : ℕ) :
    SoclePrimeIndex P ≃ ↥(primeCutoff P) := by
  classical
  refine Equiv.ofBijective
    (fun p : SoclePrimeIndex P =>
      (⟨soclePrimeIndexPrime p, ?_⟩ : ↥(primeCutoff P))) ?_
  · exact Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩
  · constructor
    · intro p q hpq
      exact (soclePrimeEmbedding P).injective (congrArg Subtype.val hpq)
    · rintro ⟨q, hq⟩
      simp only [primeCutoff, Finset.mem_map, Finset.mem_univ, true_and] at hq
      obtain ⟨p, hp⟩ := hq
      exact ⟨p, Subtype.ext hp⟩

/-- Kolmogorov product of the actual q-Gamma laws over all primes. -/
def soclePrimeProductMeasure {σ : ℝ} (hσ : 0 < σ) : Measure (Nat.Primes → ℝ) :=
  Measure.infinitePi fun p : Nat.Primes => qLaw (primeNome hσ p)

instance soclePrimeProductMeasure_isProbability {σ : ℝ} (hσ : 0 < σ) :
    IsProbabilityMeasure (soclePrimeProductMeasure hσ) := by
  rw [soclePrimeProductMeasure]
  infer_instance

/-- Centered cutoff sum on the fixed prime-indexed product space. -/
def soclePrimeProductPartialSum (c : Nat.Primes → ℝ) (P : ℕ)
    (x : Nat.Primes → ℝ) : ℝ :=
  soclePrimePartialSum c (P := P) (fun p => x (soclePrimeIndexPrime p))

theorem measurable_soclePrimeProductPartialSum (c : Nat.Primes → ℝ) (P : ℕ) :
    Measurable (soclePrimeProductPartialSum c P) := by
  change Measurable (fun x : Nat.Primes → ℝ =>
    ∑ p : SoclePrimeIndex P, (x (soclePrimeIndexPrime p) - c (soclePrimeIndexPrime p)))
  fun_prop

/-- Every cutoff sum on the Kolmogorov product has exactly the literal finite q-Gamma law. -/
theorem map_soclePrimeProductPartialSum {σ : ℝ} (hσ : 0 < σ)
    (c : Nat.Primes → ℝ) (P : ℕ) :
    Measure.map (soclePrimeProductPartialSum c P) (soclePrimeProductMeasure hσ) =
      soclePrimePartialMeasure hσ c P := by
  classical
  let I : Finset Nat.Primes := primeCutoff P
  let e : SoclePrimeIndex P ≃ ↥I := soclePrimeCutoffEquiv P
  let reindex : (↥I → ℝ) → (SoclePrimeIndex P → ℝ) := fun y p => y (e p)
  have hreindex_measurable : Measurable reindex := by
    fun_prop
  have hfun : soclePrimeProductPartialSum c P =
      fun x => soclePrimePartialSum c (reindex (I.restrict x)) := by
    funext x
    simp only [soclePrimeProductPartialSum, soclePrimePartialSum]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
  have hrestrict :
      Measure.map I.restrict (soclePrimeProductMeasure hσ) =
        Measure.pi (fun p : ↥I => qLaw (primeNome hσ p.1)) := by
    simpa [soclePrimeProductMeasure] using
      (Measure.infinitePi_map_restrict
        (fun p : Nat.Primes => qLaw (primeNome hσ p)) (I := I))
  have hreindex :
      Measure.map reindex (Measure.pi (fun p : ↥I => qLaw (primeNome hσ p.1))) =
        Measure.pi (fun p : SoclePrimeIndex P =>
          qLaw (primeNome hσ (soclePrimeIndexPrime p))) := by
    have hmeasure :
        (fun p : ↥I => qLaw (primeNome hσ p.1)) =
          (fun p : ↥I => qLaw (primeNome hσ (soclePrimeIndexPrime (e.symm p)))) := by
      funext p
      apply congrArg qLaw
      apply congrArg (primeNome hσ)
      exact (congrArg Subtype.val (e.apply_symm_apply p)).symm
    rw [hmeasure]
    have hmap := Measure.pi_map_piCongrLeft e.symm
      (fun p : SoclePrimeIndex P => qLaw (primeNome hσ (soclePrimeIndexPrime p)))
    have hreindex_eq : reindex =
        MeasurableEquiv.piCongrLeft (fun _ : SoclePrimeIndex P => ℝ) e.symm := by
      funext y p
      simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hreindex_eq]
    exact hmap
  calc
    Measure.map (soclePrimeProductPartialSum c P) (soclePrimeProductMeasure hσ) =
        Measure.map (soclePrimePartialSum c)
          (Measure.map (reindex ∘ I.restrict) (soclePrimeProductMeasure hσ)) := by
      rw [Measure.map_map (measurable_soclePrimePartialSum c P)
        (hreindex_measurable.comp (Finset.measurable_restrict I))]
      exact congrArg (fun f => Measure.map f (soclePrimeProductMeasure hσ)) hfun
    _ = Measure.map (soclePrimePartialSum c)
        (Measure.map reindex
          (Measure.map I.restrict (soclePrimeProductMeasure hσ))) := by
      rw [Measure.map_map hreindex_measurable (Finset.measurable_restrict I)]
    _ = soclePrimePartialMeasure hσ c P := by
      rw [hrestrict, hreindex]
      rfl

/-- No deterministic centering makes the socle prime series converge almost surely in the
condensed chamber `1 / 2 < σ ≤ 1`. -/
theorem not_ae_convergent_soclePrimeProductPartialSum {σ : ℝ} (hσ : 0 < σ)
    (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1) (c : Nat.Primes → ℝ) :
    ¬ ∀ᵐ x ∂soclePrimeProductMeasure hσ,
        ∃ z : ℝ, Tendsto (fun P => soclePrimeProductPartialSum c P x) atTop (𝓝 z) := by
  classical
  intro hconv
  let Z : (Nat.Primes → ℝ) → ℝ := fun x =>
    if hx : ∃ z : ℝ, Tendsto (fun P => soclePrimeProductPartialSum c P x) atTop (𝓝 z) then
      Classical.choose hx
    else 0
  have hlim : ∀ᵐ x ∂soclePrimeProductMeasure hσ,
      Tendsto (fun P => soclePrimeProductPartialSum c P x) atTop (𝓝 (Z x)) := by
    filter_upwards [hconv] with x hx
    simpa only [Z, dif_pos hx] using Classical.choose_spec hx
  have hX : ∀ P,
      AEMeasurable (soclePrimeProductPartialSum c P) (soclePrimeProductMeasure hσ) :=
    fun P => (measurable_soclePrimeProductPartialSum c P).aemeasurable
  have hZ : AEMeasurable Z (soclePrimeProductMeasure hσ) :=
    aemeasurable_of_tendsto_metrizable_ae atTop hX hlim
  have hdist := tendstoInDistribution_of_ae_tendsto hX hZ hlim
  let μ : ProbabilityMeasure ℝ :=
    ⟨(soclePrimeProductMeasure hσ).map Z, Measure.isProbabilityMeasure_map hZ⟩
  apply not_tendsto_soclePrimePartialLaw hσ hhalf hσ1 c μ
  have hlaw : ∀ P,
      (⟨(soclePrimeProductMeasure hσ).map (soclePrimeProductPartialSum c P),
          Measure.isProbabilityMeasure_map (hX P)⟩ : ProbabilityMeasure ℝ) =
        soclePrimePartialLaw hσ c P := by
    intro P
    apply Subtype.ext
    exact map_soclePrimeProductPartialSum hσ c P
  simpa only [hlaw, μ] using hdist.tendsto

end

end GaloisForLFunctions.HTGeometry
