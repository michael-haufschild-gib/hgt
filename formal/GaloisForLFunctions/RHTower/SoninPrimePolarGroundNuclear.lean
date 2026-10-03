import GaloisForLFunctions.RHTower.SoninPrimePolarGroundTransfer
import GaloisForLFunctions.RHTower.SoninTimeBandTaylorSourceDirection
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

/-!
# Native nuclear admission through one physical ground column

The exact all-degree ground transfer controls every literal Fourier Taylor
column. Its factorial series converges in the genuine Schatten-one Banach
space, so each original symmetric prime–polar time-band tail is bounded by
its single physical ground column with a fixed cutoff-independent constant.
The arithmetic ground-tail decay and complete Fourier/response transport are
separate remaining obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower

/-- Difference of the full original two-direction prime–polar sources. -/
def soninPrimePolarSymmetricTail (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    SoninL2 →L[ℂ] SoninL2 :=
  (soninPrimePolarSourceOperator P b R 1 hb + soninPrimePolarSourceOperator P b R (-1) hb) -
    (soninPrimePolarSourceOperator Q b S 1 hb + soninPrimePolarSourceOperator Q b S (-1) hb)

private theorem monomial_tail_norm (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a n)‖ ≤
      a^n * ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0)‖ := by
  have h := soninPrimePolar_symmetric_tail_monomial_energy a ha n P Q b R S hb
  change ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a n)‖^2 + _ =
    a^(2*n) * ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0)‖^2 at h
  have hp : a^(2*n) = (a^n)^2 := by rw [mul_comm 2 n, pow_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg ha _) (norm_nonneg _))).mp
  rw [mul_pow, ← hp]
  have hpos : 0 ≤ a^(2*n)*(n:ℝ)*((n:ℝ)+1)*
      ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity)
        (soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0))‖^2 := by positivity
  dsimp only [soninPrimePolarSymmetricTail] at hpos
  linarith

private theorem degree_relative_mass (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a^n * ‖soninCutoffMonomial a 0‖ ≤ ((n+1:ℕ):ℝ) * ‖soninCutoffMonomial a n‖ := by
  apply (sq_le_sq₀ (mul_nonneg (pow_nonneg ha _) (norm_nonneg _)) (by positivity)).mp
  rw [mul_pow, mul_pow, norm_sq_soninCutoffMonomial a ha 0, norm_sq_soninCutoffMonomial a ha n]
  simp only [mul_zero, zero_add, pow_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero, div_one]
  have hn : 0 < 2*(n:ℝ)+1 := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hn]
  have hp : a^(2*n+1) = (a^n)^2*a := by rw [pow_add, pow_mul]; ring
  rw [hp]
  have hpos : 0 ≤ 2*a*(a^n)^2*(n:ℝ)^2 := by positivity
  nlinarith

private theorem ground_norm_pos (a : ℝ) (ha : 0 < a) :
    0 < ‖soninCutoffMonomial a 0‖ := by
  have h := norm_sq_soninCutoffMonomial a ha.le 0
  simp only [mul_zero, zero_add, pow_one, Nat.cast_zero, div_one] at h
  nlinarith [norm_nonneg (soninCutoffMonomial a 0)]

private theorem output_operator_norm (D T : SoninL2 →L[ℂ] SoninL2) (f : SoninL2)
    (e : ℝ) (he : 0 ≤ e) (hT : ∀ x, T x ∈ Submodule.span ℂ ({f} : Set SoninL2))
    (hD : ‖D f‖ ≤ e*‖f‖) : ‖D ∘L T‖ ≤ e*‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg he (norm_nonneg _))
  intro x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hT x)
  change ‖D (T x)‖ ≤ (e*‖T‖)*‖x‖
  calc
    _ = ‖c‖*‖D f‖ := by rw [← hc, map_smul, norm_smul]
    _ ≤ ‖c‖*(e*‖f‖) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = e*‖T x‖ := by rw [← hc, norm_smul]; ring
    _ ≤ e*(‖T‖*‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) he
    _ = _ := by ring

private theorem nuclear_norm_le {ι : Type*}
    (A : ι → SoninL2 →L[ℂ] SoninL2) (T : SoninL2 →L[ℂ] SoninL2)
    (hA : ∀ i, HasRankLE (A i) 1) (hn : Summable (fun i => ‖A i‖)) (hS : HasSum A T) :
    traceNorm SoninL2 T ≤ ∑' i, ‖A i‖ := by
  let B : ι → SchattenOneOperator SoninL2 := fun i =>
    ⟨A i, memSchattenClass_of_hasRankLE one_pos (hA i)⟩
  have hnorm (i : ι) : ‖B i‖ = ‖A i‖ := traceNorm_eq_norm_of_hasRankLE_one (hA i)
  have hnB : Summable (fun i => ‖B i‖) := hn.congr (fun i => (hnorm i).symm)
  have hB : Summable B := Summable.of_norm hnB
  have hSA : HasSum A ((∑' i, B i : SchattenOneOperator SoninL2) : SoninL2 →L[ℂ] SoninL2) :=
    (schattenOneCoeCLM (H := SoninL2)).hasSum hB.hasSum
  have heq := hSA.unique hS
  have hbound : ‖∑' i, B i‖ ≤ ∑' i, ‖A i‖ := by
    simpa only [hnorm] using norm_tsum_le_tsum_norm hnB
  change traceNorm SoninL2 ((∑' i, B i : SchattenOneOperator SoninL2) :
    SoninL2 →L[ℂ] SoninL2) ≤ _ at hbound
  rwa [heq] at hbound

/-- One fixed nuclear reconstruction constant, independent of prime and continuum cutoffs. -/
def soninGroundNuclearConstant (a c d : ℝ) (ha : 0 < a) : ℝ :=
  (∑' n, ((n+1:ℕ):ℝ) * ‖fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le) n‖) /
    ‖soninCutoffMonomial a 0‖

/-- The native symmetric source tail on the actual physical time-band operator,
packaged in the genuine Schatten-one Banach space. -/
def soninPrimePolarTimeBandTail (a c d : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) : SchattenOneOperator SoninL2 :=
  ⟨soninPrimePolarSymmetricTail P Q b R S hb ∘L
      fullTimeBandFourier (-a) a c d (neg_le_self ha.le),
    memSchattenClass_one_comp_left
      (memSchattenClass_one_fullTimeBandFourier (-a) a c d (neg_le_self ha.le)) _⟩

/-- Genuine nuclear control of each native full source tail by its single
physical ground column. No arithmetic tail convergence is assumed. -/
theorem soninPrimePolar_timeBand_ground_nuclear (a c d : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    ‖soninPrimePolarTimeBandTail a c d ha P Q b R S hb‖ ≤
      soninGroundNuclearConstant a c d ha *
        ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0)‖ := by
  change traceNorm SoninL2 (soninPrimePolarSymmetricTail P Q b R S hb ∘L
    fullTimeBandFourier (-a) a c d (neg_le_self ha.le)) ≤ _
  let K := soninPrimePolarSymmetricTail P Q b R S hb
  let A := fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)
  let T := fullTimeBandFourier (-a) a c d (neg_le_self ha.le)
  let e := ‖K (soninCutoffMonomial a 0)‖ / ‖soninCutoffMonomial a 0‖
  have he : 0 ≤ e := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hg := ground_norm_pos a ha
  have hcolumn (n : ℕ) : ‖K (soninCutoffMonomial a n)‖ ≤
      (e*((n+1:ℕ):ℝ)) * ‖soninCutoffMonomial a n‖ := by
    calc
      _ ≤ a^n * ‖K (soninCutoffMonomial a 0)‖ := monomial_tail_norm a ha.le n P Q b R S hb
      _ = e*(a^n * ‖soninCutoffMonomial a 0‖) := by dsimp [e]; field_simp
      _ ≤ e*(((n+1:ℕ):ℝ) * ‖soninCutoffMonomial a n‖) :=
        mul_le_mul_of_nonneg_left (degree_relative_mass a ha.le n) he
      _ = _ := by ring
  have htail (n : ℕ) : ‖K ∘L A n‖ ≤ e*(((n+1:ℕ):ℝ)*‖A n‖) := by
    have h := output_operator_norm K (A n) (soninCutoffMonomial a n)
      (e*((n+1:ℕ):ℝ)) (by positivity)
      (fullTimeBandFourierTaylorTerm_mem_span_cutoffMonomial a c d ha.le n) (hcolumn n)
    simpa only [mul_assoc] using h
  have hw : Summable (fun n => ((n+1:ℕ):ℝ)*‖A n‖) :=
    summable_succ_mul_norm_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)
  have hn : Summable (fun n => ‖K ∘L A n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail (hw.mul_left e)
  have hS : HasSum (fun n => K ∘L A n) (K ∘L T) :=
    (hasSum_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le)).mul_left K
  calc
    _ ≤ ∑' n, ‖K ∘L A n‖ := nuclear_norm_le _ _
      (fun n => (hasRankLE_fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha.le) n).comp_left K) hn hS
    _ ≤ ∑' n, e*(((n+1:ℕ):ℝ)*‖A n‖) := Summable.tsum_le_tsum htail hn (hw.mul_left e)
    _ = _ := by rw [tsum_mul_left]; dsimp [soninGroundNuclearConstant, e, A, K]; ring

end RHTower
