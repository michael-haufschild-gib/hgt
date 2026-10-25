import GaloisForLFunctions.BezoutValuationIncidence.SignedVaughanTailsVanishAtTheirAbsoluteScale
import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity
import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity

/-!
# Centered Vaughan cancellation at product horizons

At a covering product horizon the large leg is exactly its removed linear mean.
Signed reciprocal tails and a common estimate for truncated Möbius receivers make
all five centered norms negligible at the trivial scale. The resulting Gram bound
is uniform over every factorization and allows bounded moving coefficient packets.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem vaughan_tendsto_finite_sum_zero {ι : Type*} (S : Finset ι)
    (f : ι → ℕ → ℝ) (hf : ∀ i ∈ S, Tendsto (f i) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ S, f i T) atTop (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [sum_empty] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | @insert i S hi ih =>
    simp only [sum_insert hi]
    simpa only [add_zero] using (hf i (mem_insert_self _ _)).add
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

/-- The linear sequence has pronic energy between half its horizon and its horizon. -/
theorem sq_pronicNorm_natCast_bounds (T : ℕ) :
    (T : ℝ) / 2 ≤ pronicNorm (fun n : ℕ => (n : ℝ)) T ^ 2 ∧
      pronicNorm (fun n : ℕ => (n : ℝ)) T ^ 2 ≤ T := by
  have heq : pronicNorm (fun n : ℕ => (n : ℝ)) T ^ 2 =
      ∑ n ∈ Icc 1 T, (n : ℝ) / ((n : ℝ) + 1) := by
    rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    apply sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    field_simp
  rw [heq]
  constructor
  · calc
      (T : ℝ) / 2 = ∑ _n ∈ Icc 1 T, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := sum_le_sum fun n hn => by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
        apply (le_div_iff₀ (by positivity)).mpr
        linarith only [hn1]
  · calc
      _ ≤ ∑ _n ∈ Icc 1 T, (1 : ℝ) := sum_le_sum fun n _ =>
        (div_le_one (by positivity)).mpr (by linarith)
      _ = _ := by simp

private theorem sq_pronicNorm_centredPiece_eq_diagonal (ε : ℝ) (U V T : ℕ) (i : Fin 5) :
    pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n i) T ^ 2 =
      pmPronicVaughanCentredGram ε U V T i i := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  simp only [pmPronicVaughanCentredGram, pow_two, pronicSeq, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]

/-- At a product horizon, the large leg's centered energy costs only two signed tails. -/
theorem pmPronicVaughanCentredGram_large_product_div_le {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : 1 ≤ U * V) :
    pmPronicVaughanCentredGram ε U V (U * V) 3 3 / ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
      pmPronicPowerDensity ε ^ 2 *
        (((U : ℝ) ^ ε * ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U)) *
         ((V : ℝ) ^ ε * ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε V))) ^ 2 := by
  have hT0 : (0 : ℝ) < (U * V : ℕ) := by exact_mod_cast hUV
  have hscale : 0 < ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε) := Real.rpow_pos_of_pos hT0 _
  have hpow : (((U * V : ℕ) : ℝ) ^ ε) ^ 2 *
      ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε) = (U * V : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
    rw [show ε * ((2 : ℕ) : ℝ) + (1 - 2 * ε) = 1 by push_cast; ring, Real.rpow_one]
  have hmul : ((U * V : ℕ) : ℝ) ^ ε = (U : ℝ) ^ ε * (V : ℝ) ^ ε := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg U) (Nat.cast_nonneg V)]
  rw [div_le_iff₀ hscale, pmPronicVaughanCentredGram_large_of_cover ε (by nlinarith)]
  calc
    _ ≤ pmPronicVaughanMean ε U V 3 ^ 2 * (U * V : ℕ) :=
      mul_le_mul_of_nonneg_left (sq_pronicNorm_natCast_bounds (U * V)).2 (sq_nonneg _)
    _ = pmPronicVaughanMean ε U V 3 ^ 2 *
        ((((U * V : ℕ) : ℝ) ^ ε) ^ 2 * ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε)) :=
      congrArg (fun x : ℝ => pmPronicVaughanMean ε U V 3 ^ 2 * x) hpow.symm
    _ = _ := by
      rw [pmPronicVaughanMean_large_factorization hε, hmul]
      ring

/-- The empty large leg has zero normalized centered energy along every divergent product. -/
theorem tendsto_pmPronicVaughanCentredGram_large_product_div {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T => pmPronicVaughanCentredGram ε (U T) (V T) (U T * V T) 3 3 /
      ((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have hlim := ((tendsto_product_scaled_pmPronicVaughanSmallDensity_tails hε U V hUV).pow 2).const_mul
    (pmPronicPowerDensity ε ^ 2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun T => by
    rw [← sq_pronicNorm_centredPiece_eq_diagonal]
    positivity) ?_ hlim
  filter_upwards [hUV.eventually_ge_atTop 1] with T hT
  exact pmPronicVaughanCentredGram_large_product_div_le hε hT

/-- The centered large-leg norm is negligible at the trivial norm scale. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPiece_large_product_div {ε : ℝ}
    (hε : 0 < ε) (U V : ℕ → ℕ) (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n 3)
      (U T * V T) / Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have h := (tendsto_pmPronicVaughanCentredGram_large_product_div hε U V hUV).sqrt
  simpa only [← sq_pronicNorm_centredPiece_eq_diagonal,
    Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.sqrt_sq (pronicNorm_nonneg _ _), Real.sqrt_zero] using h

private theorem tendsto_vaughan_first_small_norm_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun T => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n 0)
      (H T) / Real.sqrt ((H T : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  simpa only [pmPronicVaughanCentredPiece,
    pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε] using
    tendsto_pronicNorm_truncatedMoebius_div_at_horizon hε hε2 U H hH

private theorem tendsto_vaughan_pole_norm_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun T => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n 4)
      (H T) / Real.sqrt ((H T : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have ha : Tendsto (fun T => Real.sqrt ((H T : ℝ) ^ (1 - 2 * ε))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (((tendsto_rpow_atTop
      (by linarith only [hε2] : 0 < 1 - 2 * ε)).comp tendsto_natCast_atTop_atTop).comp hH)
  have hlim : Tendsto (fun T => (1 / 2 : ℝ) / Real.sqrt ((H T : ℝ) ^ (1 - 2 * ε)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop ha
  refine squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (pronicNorm_nonneg _ _) (Real.sqrt_nonneg _)) ?_ hlim
  exact Eventually.of_forall fun T => div_le_div_of_nonneg_right
    (pronicNorm_le_of_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (abs_pmPronicVaughanPiece_pole_sub_mean_le hε.le (U T) (V T)) (H T))
    (Real.sqrt_nonneg _)

private theorem pronicNorm_four_add_le (f g h k : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => f n + (g n + (h n + k n))) T ≤
      pronicNorm f T + (pronicNorm g T + (pronicNorm h T + pronicNorm k T)) :=
  (pronicNorm_add_le f (fun n => g n + (h n + k n)) T).trans
    (add_le_add le_rfl ((pronicNorm_add_le g (fun n => h n + k n) T).trans
      (add_le_add le_rfl (pronicNorm_add_le h k T))))

private theorem pronicNorm_vaughan_smallSmall_le_others (ε : ℝ) (U V T : ℕ) :
    pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 2) T ≤
      pronicNorm (pmBezoutInteriorPrefix ε) T +
        (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 0) T +
          (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 1) T +
            (pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 3) T +
              pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n 4) T))) := by
  let e : Fin 5 → ℕ → ℝ := fun j n => pmPronicVaughanCentredPiece ε U V n j
  have heq : e 2 = fun n => pmBezoutInteriorPrefix ε n +
      (-1 : ℝ) * (e 0 n + (e 1 n + (e 3 n + e 4 n))) := by
    funext n
    have hs : (∑ j : Fin 5, e j n) = pmBezoutInteriorPrefix ε n := by
      simp only [e, pmPronicVaughanCentredPiece, sum_sub_distrib, ← sum_mul,
        sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, zero_mul, sub_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change e 0 n + (e 1 n + (e 2 n + (e 3 n + e 4 n))) = _ at hs
    linarith only [hs]
  change pronicNorm (e 2) T ≤ _
  rw [heq]
  have h := pronicNorm_add_le (pmBezoutInteriorPrefix ε)
    (fun n => (-1 : ℝ) * (e 0 n + (e 1 n + (e 3 n + e 4 n)))) T
  rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
  exact h.trans (add_le_add le_rfl (pronicNorm_four_add_le (e 0) (e 1) (e 3) (e 4) T))

/-- The exact five-piece identity transfers product-horizon cancellation to the small-small leg. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPiece_smallSmall_product_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n 2)
      (U T * V T) / Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have h0 := tendsto_vaughan_first_small_norm_div hε hε2 U V (fun T => U T * V T) hUV
  have h1 : Tendsto (fun T => pronicNorm
      (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n 1) (U T * V T) /
        Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) :=
    tendsto_vaughan_first_small_norm_div hε hε2 V U (fun T => U T * V T) hUV
  have h3 := tendsto_pronicNorm_pmPronicVaughanCentredPiece_large_product_div hε U V hUV
  have h4 := tendsto_vaughan_pole_norm_div hε hε2 U V (fun T => U T * V T) hUV
  have hI : Tendsto (fun T => pronicNorm (pmBezoutInteriorPrefix ε) (U T * V T) /
      Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_pronicNorm_pmBezoutInteriorPrefix_div_smooth_scale hε hε2).comp hUV
  have hlim := hI.add (h0.add (h1.add (h3.add h4)))
  simp only [add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (pronicNorm_nonneg _ _) (Real.sqrt_nonneg _)) ?_ hlim
  exact Eventually.of_forall fun T => by
    simpa only [add_div] using div_le_div_of_nonneg_right
      (pronicNorm_vaughan_smallSmall_le_others ε (U T) (V T) (U T * V T))
      (Real.sqrt_nonneg (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)))

/-- Every centered component is negligible at the product horizon's trivial norm scale. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPiece_product_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) (i : Fin 5) :
    Tendsto (fun T => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n i)
      (U T * V T) / Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  fin_cases i
  · exact tendsto_vaughan_first_small_norm_div hε hε2 U V (fun T => U T * V T) hUV
  · exact tendsto_vaughan_first_small_norm_div hε hε2 V U (fun T => U T * V T) hUV
  · exact tendsto_pronicNorm_pmPronicVaughanCentredPiece_smallSmall_product_div hε hε2 U V hUV
  · exact tendsto_pronicNorm_pmPronicVaughanCentredPiece_large_product_div hε U V hUV
  · exact tendsto_vaughan_pole_norm_div hε hε2 U V (fun T => U T * V T) hUV

/-- Every centered component energy is negligible at the product horizon's trivial scale. -/
theorem tendsto_pmPronicVaughanCentredGram_diagonal_product_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) (i : Fin 5) :
    Tendsto (fun T => pmPronicVaughanCentredGram ε (U T) (V T) (U T * V T) i i /
      ((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have h := (tendsto_pronicNorm_pmPronicVaughanCentredPiece_product_div hε hε2 U V hUV i).pow 2
  simpa only [div_pow, Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    sq_pronicNorm_centredPiece_eq_diagonal, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h

/-- The sum of the five centered component energies. -/
def pmPronicVaughanCentredTrace (ε : ℝ) (U V T : ℕ) : ℝ :=
  ∑ i : Fin 5, pmPronicVaughanCentredGram ε U V T i i

theorem pmPronicVaughanCentredTrace_nonneg (ε : ℝ) (U V T : ℕ) :
    0 ≤ pmPronicVaughanCentredTrace ε U V T := by
  apply sum_nonneg
  intro i _
  rw [← sq_pronicNorm_centredPiece_eq_diagonal]
  positivity

/-- Young's inequality pays every absolute centered Gram entry by the centered trace. -/
theorem abs_pmPronicVaughanCentredGram_le_trace (ε : ℝ) (U V T : ℕ) (i j : Fin 5) :
    |pmPronicVaughanCentredGram ε U V T i j| ≤ pmPronicVaughanCentredTrace ε U V T := by
  have hdiag (k : Fin 5) : pmPronicVaughanCentredGram ε U V T k k ≤
      pmPronicVaughanCentredTrace ε U V T := by
    unfold pmPronicVaughanCentredTrace
    exact Finset.single_le_sum (s := univ)
      (f := fun j : Fin 5 => pmPronicVaughanCentredGram ε U V T j j) (a := k)
      (fun j _ => by rw [← sq_pronicNorm_centredPiece_eq_diagonal]; positivity) (mem_univ k)
  have hhalf : |pmPronicVaughanCentredGram ε U V T i j| ≤
      (pmPronicVaughanCentredGram ε U V T i i + pmPronicVaughanCentredGram ε U V T j j) / 2 := by
    unfold pmPronicVaughanCentredGram
    rw [← sum_add_distrib, sum_div]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n _
    let x := pmPronicVaughanCentredPiece ε U V n i
    let y := pmPronicVaughanCentredPiece ε U V n j
    have hxy : |x * y| ≤ (x * x + y * y) / 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (pronicSeq n) : (0 : ℝ) ≤ (pronicSeq n : ℝ))]
    exact (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg _)).trans_eq (by ring)
  exact hhalf.trans (by linarith only [hdiag i, hdiag j])

/-- The whole centered trace vanishes at the trivial scale along every divergent product. -/
theorem tendsto_pmPronicVaughanCentredTrace_product_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T => pmPronicVaughanCentredTrace ε (U T) (V T) (U T * V T) /
      ((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  simpa only [pmPronicVaughanCentredTrace, sum_div] using
    vaughan_tendsto_finite_sum_zero univ _
      (fun i _ => tendsto_pmPronicVaughanCentredGram_diagonal_product_div hε hε2 U V hUV i)

/-- Every moving signed centered Gram entry vanishes at the product horizon's trivial scale. -/
theorem tendsto_pmPronicVaughanCentredGram_product_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) (i j : ℕ → Fin 5) :
    Tendsto (fun T => pmPronicVaughanCentredGram ε (U T) (V T) (U T * V T) (i T) (j T) /
      ((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (Eventually.of_forall fun T => ?_)
    (tendsto_pmPronicVaughanCentredTrace_product_div hε hε2 U V hUV)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact div_le_div_of_nonneg_right
    (abs_pmPronicVaughanCentredGram_le_trace ε (U T) (V T) (U T * V T) (i T) (j T))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The trace estimate has one threshold for all factorizations of a product horizon. -/
theorem uniform_pmPronicVaughanCentredTrace_product_div {ε η : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hη : 0 < η) :
    ∃ N : ℕ, ∀ U V : ℕ, N ≤ U * V →
      pmPronicVaughanCentredTrace ε U V (U * V) / ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε) < η := by
  by_contra h
  push Not at h
  choose U V hbig hbad using h
  have hUV : Tendsto (fun T => U T * V T) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    exact hT.trans (hbig T)
  have hlim := tendsto_pmPronicVaughanCentredTrace_product_div hε hε2 U V hUV
  obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact (not_lt_of_ge (hbad T)) hT

/-- Every centered matrix entry has the same uniform little-o threshold at product horizons. -/
theorem uniform_pmPronicVaughanCentredGram_product_div {ε η : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hη : 0 < η) :
    ∃ N : ℕ, ∀ U V : ℕ, N ≤ U * V → ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram ε U V (U * V) i j /
        ((U * V : ℕ) : ℝ) ^ (1 - 2 * ε)| < η := by
  obtain ⟨N, hN⟩ := uniform_pmPronicVaughanCentredTrace_product_div hε hε2 hη
  refine ⟨N, fun U V hUV i j => ?_⟩
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact (div_le_div_of_nonneg_right (abs_pmPronicVaughanCentredGram_le_trace ε U V (U * V) i j)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_lt (hN U V hUV)

/-- Bounded coefficient schedules preserve the product-horizon norm saving. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPacket_product_div {ε B : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hUV : Tendsto (fun T => U T * V T) atTop atTop) (w : ℕ → Fin 5 → ℝ)
    (hw : ∀ T i, |w T i| ≤ B) :
    Tendsto (fun T => pronicNorm (pmPronicVaughanCentredPacket ε (U T) (V T) (w T))
      (U T * V T) / Real.sqrt (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have hsum := vaughan_tendsto_finite_sum_zero univ _
    (fun i _ => tendsto_pronicNorm_pmPronicVaughanCentredPiece_product_div hε hε2 U V hUV i)
  have hlim := hsum.const_mul B
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun T =>
    div_nonneg (pronicNorm_nonneg _ _) (Real.sqrt_nonneg _))
    (Eventually.of_forall fun T => ?_) hlim
  have heq : pmPronicVaughanCentredPacket ε (U T) (V T) (w T) =
      fun n => ∑ i : Fin 5, w T i * pmPronicVaughanCentredPiece ε (U T) (V T) n i := by
    funext n
    simp only [pmPronicVaughanCentredPacket, pmPronicVaughanPacket,
      pmPronicVaughanCentredPiece, pmPronicVaughanPacketLinearMean,
      mul_sub, sum_sub_distrib, sum_mul, mul_assoc]
  rw [heq]
  have hnorm : pronicNorm (fun n => ∑ i : Fin 5,
      w T i * pmPronicVaughanCentredPiece ε (U T) (V T) n i) (U T * V T) ≤
      B * ∑ i : Fin 5, pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n i) (U T * V T) := by
    calc
      _ ≤ ∑ i : Fin 5, pronicNorm (fun n => w T i * pmPronicVaughanCentredPiece ε (U T) (V T) n i)
          (U T * V T) := pronicNorm_sum_le univ _ _
      _ ≤ ∑ i : Fin 5, B * pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U T) (V T) n i)
          (U T * V T) := sum_le_sum fun i _ => by
            rw [pronicNorm_smul]
            exact mul_le_mul_of_nonneg_right (hw T i) (pronicNorm_nonneg _ _)
      _ = _ := (mul_sum _ _ _).symm
  have hdiv := div_le_div_of_nonneg_right hnorm
    (Real.sqrt_nonneg (((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)))
  simpa only [mul_div_assoc, sum_div] using hdiv

/-- In particular, two divergent cutoffs allow arbitrary aspect ratio at their product horizon. -/
theorem tendsto_pmPronicVaughanCentredGram_product_div_of_cutoffs_atTop {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i j : Fin 5) :
    Tendsto (fun T => pmPronicVaughanCentredGram ε (U T) (V T) (U T * V T) i j /
      ((U T * V T : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have hUV : Tendsto (fun T => U T * V T) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hU.eventually_ge_atTop b, hV.eventually_ge_atTop 1] with T hUT hVT
    exact hUT.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (U T) hVT)
  exact tendsto_pmPronicVaughanCentredGram_product_div hε hε2 U V hUV (fun _ => i) (fun _ => j)




end GaloisForLFunctions.BezoutValuationIncidence
