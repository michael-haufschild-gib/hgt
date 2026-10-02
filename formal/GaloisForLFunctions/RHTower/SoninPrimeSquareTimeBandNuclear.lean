import GaloisForLFunctions.RHTower.SoninTimeBandTaylorSourceDirection
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

noncomputable section
open scoped BigOperators
namespace RHTower

private theorem traceNorm_le_nuclear_hasSum {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ i, HasRankLE (A i) 1)
    (hn : Summable (fun i => ‖A i‖)) (hS : HasSum A T) :
    traceNorm H T ≤ ∑' i, ‖A i‖ := by
  let B : ι → SchattenOneOperator H := fun i =>
    ⟨A i, memSchattenClass_of_hasRankLE one_pos (hA i)⟩
  have hnorm (i : ι) : ‖B i‖ = ‖A i‖ :=
    traceNorm_eq_norm_of_hasRankLE_one (hA i)
  have hnB : Summable (fun i => ‖B i‖) := hn.congr (fun i => (hnorm i).symm)
  have hB : Summable B := Summable.of_norm hnB
  have hSA : HasSum A ((∑' i, B i : SchattenOneOperator H) : H →L[ℂ] H) :=
    (schattenOneCoeCLM (H := H)).hasSum hB.hasSum
  have heq := hSA.unique hS
  have hbound : ‖∑' i, B i‖ ≤ ∑' i, ‖A i‖ := by
    simpa only [hnorm] using norm_tsum_le_tsum_norm hnB
  change traceNorm H ((∑' i, B i : SchattenOneOperator H) : H →L[ℂ] H) ≤ _ at hbound
  rwa [heq] at hbound

/-- The original prime-square source acting on the actual finite time-band
operator, in the genuine trace-norm carrier. -/
def soninPrimeSquareTimeBandSource (a c d : ℝ) (ha : 0 ≤ a) (p : Nat.Primes) :
    SchattenOneOperator SoninL2 :=
  ⟨(soninLogPrimePowerCoefficient (p, 0) •
      dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))) ∘L
        fullTimeBandFourier (-a) a c d (neg_le_self ha),
    memSchattenClass_one_comp_left
      (memSchattenClass_one_fullTimeBandFourier (-a) a c d (neg_le_self ha)) _⟩

/-- Unconditional trace-norm assembly of the original unsquared prime-square
response on the actual time-band operator, retaining both dilation directions. -/
theorem summable_soninPrimeSquareTimeBandSource (a c d : ℝ) (ha : 0 ≤ a) :
    Summable (soninPrimeSquareTimeBandSource a c d ha) := by
  classical
  let A := fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha)
  let T := fullTimeBandFourier (-a) a c d (neg_le_self ha)
  let D : Nat.Primes → SoninL2 →L[ℂ] SoninL2 := fun p =>
    soninLogPrimePowerCoefficient (p, 0) •
      dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))
  have hnA : Summable (fun n => ‖A n‖) :=
    summable_norm_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha)
  let M : ℝ := ∑' n, ‖A n‖
  have hM : 0 ≤ M := tsum_nonneg (fun _ => norm_nonneg _)
  have hMp : 0 < M + 1 := by linarith
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε hMp
  obtain ⟨s, hs⟩ := soninPrimeSquare_timeBandTaylor_uniform_tail a c d ha δ hδ
  refine ⟨s, fun t ht => ?_⟩
  let Dt := ∑ p ∈ t, D p
  have htail (n : ℕ) : ‖Dt ∘L A n‖ ≤ δ * ‖A n‖ := hs t ht n
  have hn : Summable (fun n => ‖Dt ∘L A n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail (hnA.mul_left δ)
  have hS : HasSum (fun n => Dt ∘L A n) (Dt ∘L T) :=
    (hasSum_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha)).mul_left Dt
  have hnuc := traceNorm_le_nuclear_hasSum (fun n => Dt ∘L A n) (Dt ∘L T)
    (fun n => (hasRankLE_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha) n).comp_left Dt)
    hn hS
  have hval : ((∑ p ∈ t, soninPrimeSquareTimeBandSource a c d ha p :
      SchattenOneOperator SoninL2) : SoninL2 →L[ℂ] SoninL2) = Dt ∘L T := by
    change (schattenOneCoeCLM (H := SoninL2))
      (∑ p ∈ t, soninPrimeSquareTimeBandSource a c d ha p) = _
    rw [map_sum]
    change (∑ p ∈ t, D p ∘L T) = (∑ p ∈ t, D p) ∘L T
    apply ContinuousLinearMap.ext
    intro x
    simp only [sum_apply, ContinuousLinearMap.comp_apply]
  rw [SchattenOneOperator.norm_def, hval]
  calc
    _ ≤ ∑' n, ‖Dt ∘L A n‖ := hnuc
    _ ≤ ∑' n, δ * ‖A n‖ := Summable.tsum_le_tsum htail hn (hnA.mul_left δ)
    _ = δ * M := tsum_mul_left
    _ < ε := by
      have heq : δ * (M + 1) = ε := div_mul_cancel₀ ε hMp.ne'
      nlinarith
end RHTower
