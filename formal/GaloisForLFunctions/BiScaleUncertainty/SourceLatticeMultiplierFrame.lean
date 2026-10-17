import GaloisForLFunctions.BiScaleUncertainty.OptimizedHyperbolicRayReceiver
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# Source lattice budgets replace multiplier-frame blindness

Compact source correlations have finite support on the dyadic lattice. Their
absolute mass and centered correction mass give a uniform multiplier frame for
arbitrary signed coefficients. Coherent packets then remove the support radius
from the odd moment penalty without a source-zero hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SourceLattice
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment HyperbolicRay
noncomputable section

def sourceSample (f : C_c(ℝ, ℝ)) (k : ℤ) : ℝ := autocorr f ((k : ℝ) * Real.log 2)

theorem sourceSample_neg (f : C_c(ℝ, ℝ)) (k : ℤ) : sourceSample f (-k) = sourceSample f k := by
  unfold sourceSample
  rw [Int.cast_neg, neg_mul, autocorr_neg]

/-- Compactness supplies finite lattice support; no summability premise is required. -/
theorem sourceSample_finite (f : C_c(ℝ, ℝ)) : (Function.support (sourceSample f)).Finite := by
  obtain ⟨D, _, hs⟩ := exists_pos_autocorr_support_radius f.hasCompactSupport
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n, hn⟩ := exists_nat_gt (D / Real.log 2)
  have hnd : D < (n : ℝ) * Real.log 2 := (div_lt_iff₀ hd).mp hn
  refine (Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset ?_
  intro k hk
  change autocorr f ((k : ℝ) * Real.log 2) ≠ 0 at hk
  have hb : |(k : ℝ)| < (n : ℝ) := by
    by_contra hn
    apply hk
    apply hs
    rw [abs_mul, abs_of_pos hd]
    exact hnd.trans_le (mul_le_mul_of_nonneg_right (le_of_not_gt hn) hd.le)
  have hb' := abs_lt.mp hb
  constructor
  · exact_mod_cast hb'.1.le
  · exact_mod_cast hb'.2.le

private theorem summable_abs_of_finite (k : ℤ → ℝ) (hk : (Function.support k).Finite) :
    Summable (fun z => |k z|) := by
  apply summable_of_hasFiniteSupport
  apply hk.subset
  intro z hz
  change |k z| ≠ 0 at hz
  change k z ≠ 0
  exact fun he => hz (by rw [he, abs_zero])

/-- Intrinsic original-source row budget, including its origin energy. -/
def correlationMass (f : C_c(ℝ, ℝ)) : ℝ := ∑' k : ℤ, |sourceSample f k|

def correctionSample (f : C_c(ℝ, ℝ)) (k : ℤ) : ℝ :=
  if k = 0 then 0 else
    (sourceMean f (1 / 2) - Real.cosh (((k : ℝ) * Real.log 2) / 2) ^ 2) * sourceSample f k /
      (2 * Real.cosh (((k : ℝ) * Real.log 2) / 2))

theorem correctionSample_neg (f : C_c(ℝ, ℝ)) (k : ℤ) :
    correctionSample f (-k) = correctionSample f k := by
  by_cases hk : k = 0
  · simp [hk, correctionSample]
  · rw [correctionSample, if_neg (neg_ne_zero.mpr hk), correctionSample, if_neg hk,
      sourceSample_neg]
    simp only [Int.cast_neg, neg_mul, neg_div, Real.cosh_neg]

theorem correctionSample_finite (f : C_c(ℝ, ℝ)) :
    (Function.support (correctionSample f)).Finite := by
  apply (sourceSample_finite f).subset
  intro k hk
  change correctionSample f k ≠ 0 at hk
  change sourceSample f k ≠ 0
  intro hz
  apply hk
  simp [correctionSample, hz]

/-- Absolute centered correction budget; zero lag is excluded exactly. -/
def correctionMass (f : C_c(ℝ, ℝ)) : ℝ := ∑' k : ℤ, |correctionSample f k|

theorem correlationMass_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ correlationMass f :=
  tsum_nonneg fun _ => abs_nonneg _

theorem correctionMass_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ correctionMass f :=
  tsum_nonneg fun _ => abs_nonneg _

private theorem lattice_row_le (k : ℤ → ℝ) (hk : (Function.support k).Finite)
    (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, |k ((j : ℤ) - (i : ℤ))|) ≤ ∑' z : ℤ, |k z| := by
  classical
  have hinj : ∀ a ∈ s, ∀ b ∈ s, (a : ℤ) - (i : ℤ) = (b : ℤ) - (i : ℤ) → a = b := by
    intro a _ b _ h
    omega
  rw [← Finset.sum_image (f := fun z : ℤ => |k z|) hinj]
  exact (summable_abs_of_finite k hk).sum_le_tsum _ (fun _ _ => abs_nonneg _)

private theorem lattice_quad_le (k : ℤ → ℝ) (hk : (Function.support k).Finite)
    (heven : ∀ z, k (-z) = k z) (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * k ((j : ℤ) - (i : ℤ))) ≤
      (∑' z : ℤ, |k z|) * ∑ i ∈ s, w i ^ 2 := by
  have hpt (i j : ℕ) : 2 * (w i * w j * k ((j : ℤ) - (i : ℤ))) ≤
      (w i ^ 2 + w j ^ 2) * |k ((j : ℤ) - (i : ℤ))| := by
    have ha := le_abs_self (w i * w j * k ((j : ℤ) - (i : ℤ)))
    rw [abs_mul, abs_mul] at ha
    have hb : 2 * (|w i| * |w j|) ≤ w i ^ 2 + w j ^ 2 := by
      nlinarith only [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
    have hc := mul_le_mul_of_nonneg_right hb (abs_nonneg (k ((j : ℤ) - (i : ℤ))))
    linarith only [ha, hc]
  have hsum : 2 * (∑ i ∈ s, ∑ j ∈ s, w i * w j * k ((j : ℤ) - (i : ℤ))) ≤
      ∑ i ∈ s, ∑ j ∈ s, (w i ^ 2 + w j ^ 2) * |k ((j : ℤ) - (i : ℤ))| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hpt i j
  have hswap : (∑ i ∈ s, ∑ j ∈ s, w j ^ 2 * |k ((j : ℤ) - (i : ℤ))|) =
      ∑ i ∈ s, ∑ j ∈ s, w i ^ 2 * |k ((j : ℤ) - (i : ℤ))| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show (i : ℤ) - (j : ℤ) = -((j : ℤ) - (i : ℤ)) by ring, heven]
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, (w i ^ 2 + w j ^ 2) * |k ((j : ℤ) - (i : ℤ))|) =
      2 * ∑ i ∈ s, w i ^ 2 * ∑ j ∈ s, |k ((j : ℤ) - (i : ℤ))| := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [hswap, ← two_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
  have hrows : (∑ i ∈ s, w i ^ 2 * ∑ j ∈ s, |k ((j : ℤ) - (i : ℤ))|) ≤
      (∑' z : ℤ, |k z|) * ∑ i ∈ s, w i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (lattice_row_le k hk s i) (sq_nonneg (w i))
  rw [hsplit] at hsum
  linarith only [hsum, hrows]

/-- Every coalesced source packet has a chain-independent lattice row bound. -/
theorem differenceGram_le_lattice (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    translationGramEnergy f (pairSet N) (differenceWeight (1 / 2) w (chainNode (Real.log 2)))
      (differenceNode (chainNode (Real.log 2))) ≤
        correlationMass f * collisionEnergy N (1 / 2) (Real.log 2) w := by
  rw [differenceGram_eq_lagGram]
  have h := lattice_quad_le (sourceSample f) (sourceSample_finite f) (sourceSample_neg f)
    (Finset.range (2 * N + 1)) (lagAmplitude N (1 / 2) (Real.log 2) w)
  have he : translationGramEnergy f (Finset.range (2 * N + 1))
      (lagAmplitude N (1 / 2) (Real.log 2) w) (lagNode N (Real.log 2)) =
      ∑ i ∈ Finset.range (2 * N + 1), ∑ j ∈ Finset.range (2 * N + 1),
        lagAmplitude N (1 / 2) (Real.log 2) w i * lagAmplitude N (1 / 2) (Real.log 2) w j *
          sourceSample f ((j : ℤ) - (i : ℤ)) := by
    unfold translationGramEnergy sourceSample lagNode
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    congr 2
    ring
  rw [he]
  exact h

theorem sourceCorrection_eq_lattice_quad (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    sourceCorrection f (1 / 2) (sourceMean f (1 / 2)) (Finset.range (N + 1)) w
      (chainNode (Real.log 2)) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          w i * w j * correctionSample f ((j : ℤ) - (i : ℤ)) := by
  symm
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  have hd : (∑ i ∈ Finset.range (N + 1), w i * w i * correctionSample f ((i : ℤ) - (i : ℤ))) = 0 := by
    simp [correctionSample]
  rw [hd, zero_add]
  unfold sourceCorrection
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_offDiag.mp hp
  have hn : (p.2 : ℤ) - (p.1 : ℤ) ≠ 0 := by omega
  rw [correctionSample, if_neg hn]
  unfold differenceWeight differenceNode chainNode sourceSample
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  rw [show (p.2 : ℝ) * Real.log 2 - (p.1 : ℝ) * Real.log 2 =
    ((p.2 : ℝ) - (p.1 : ℝ)) * Real.log 2 by ring]
  rw [show (1 / 2 : ℝ) * (((p.2 : ℝ) - (p.1 : ℝ)) * Real.log 2) =
    (((p.2 : ℝ) - (p.1 : ℝ)) * Real.log 2) / 2 by ring]
  ring

theorem sourceCorrection_le_lattice (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    sourceCorrection f (1 / 2) (sourceMean f (1 / 2)) (Finset.range (N + 1)) w
      (chainNode (Real.log 2)) ≤ correctionMass f * weightEnergy N w := by
  rw [sourceCorrection_eq_lattice_quad]
  exact lattice_quad_le _ (correctionSample_finite f) (correctionSample_neg f) _ _

/-- Uniform multiplier-frame constant, paid entirely by actual original-source data. -/
def latticeFrame (f : C_c(ℝ, ℝ)) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 + correctionMass f +
    Real.sqrt (2 * autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * correlationMass f)

theorem latticeFrame_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ latticeFrame f :=
  add_nonneg (add_nonneg (autocorr_zero_nonneg _) (correctionMass_nonneg f)) (Real.sqrt_nonneg _)

theorem odd_sinhGram_le_latticeFrame (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (N + 1)) w (chainNode (Real.log 2)) ≤
        latticeFrame (oddCompactSource f) * weightEnergy N w := by
  let F := oddCompactSource f
  let Q := autocorr (centeredSource F (1 / 2) (sourceMean F (1 / 2))) 0
  have hQ : 0 ≤ Q := autocorr_zero_nonneg _
  have hΓ := correlationMass_nonneg F
  have hW := weightEnergy_nonneg N w
  have hG := (differenceGram_le_lattice F N w).trans
    (mul_le_mul_of_nonneg_left (dyadic_collisionEnergy_le N w) hΓ)
  have hs : Real.sqrt (Q * translationGramEnergy F (pairSet N)
      (differenceWeight (1 / 2) w (chainNode (Real.log 2)))
      (differenceNode (chainNode (Real.log 2)))) ≤
      Real.sqrt (2 * Q * correlationMass F) * weightEnergy N w := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hW, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Q * correlationMass F)]
    have h := mul_le_mul_of_nonneg_left hG hQ
    nlinarith only [h]
  have hd := odd_defect_le_sourceDefectUpper f (1 / 2) (sourceMean F (1 / 2))
    (Finset.range (N + 1)) w (chainNode (Real.log 2))
  have he := sourceCorrection_le_lattice F N w
  unfold sourceDefectUpper at hd
  rw [sinhGram_eq_diagonal_add_defect]
  change autocorr (sinhCompact (1 / 2) F) 0 * weightEnergy N w + _ ≤ latticeFrame F * weightEnergy N w
  unfold latticeFrame
  change _ ≤ (autocorr (sinhCompact (1 / 2) F) 0 + correctionMass F +
    Real.sqrt (2 * Q * correlationMass F)) * weightEnergy N w
  change _ ≤ _ + Real.sqrt (Q * translationGramEnergy F (pairSet N)
    (differenceWeight (1 / 2) w (chainNode (Real.log 2)))
    (differenceNode (chainNode (Real.log 2)))) at hd
  linarith only [hd, he, hs]

private theorem integral_sq_le_uniform_frame (g : C_c(ℝ, ℝ)) (C : ℝ)
    (hframe : ∀ N : ℕ, translationGramEnergy g (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) ≤ C * ((N : ℝ) + 1)) :
    (∫ u, g u) ^ 2 ≤ Real.log 2 * C := by
  by_contra hn
  have heps : 0 < (∫ u, g u) ^ 2 - Real.log 2 * C := by linarith only [hn]
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((2 * (multiplierSourceRadius g + 1) * C - (∫ u, g u) ^ 2) /
      ((∫ u, g u) ^ 2 - Real.log 2 * C))
  have hlarge := (div_lt_iff₀ heps).mp hN
  have hh := (integral_sq_le_chain_gram g N).trans
    (mul_le_mul_of_nonneg_left (hframe N) (chainSpan_pos g N).le)
  have hcount : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hlin : ((N : ℝ) + 1) * (∫ u, g u) ^ 2 ≤ chainSpan g N * C :=
    le_of_mul_le_mul_right (by nlinarith only [hh]) hcount
  unfold chainSpan at hlin
  nlinarith only [hlin, hlarge]

/-- Lattice source budgets remove both the support radius and the blindness premise. -/
theorem odd_moment_sq_le_latticeFrame (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      Real.log 2 * latticeFrame (oddCompactSource f) := by
  rw [← integral_sinhCompact_eq_moment]
  apply integral_sq_le_uniform_frame
  intro N
  simpa [weightEnergy] using odd_sinhGram_le_latticeFrame f N (fun _ => 1)

/-- Full optimized plastic receiver for arbitrary signed original-source correlations. -/
theorem odd_plasticCrossover_ge_latticeFrame (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * latticeFrame (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_moment_sq_le_latticeFrame f
  nlinarith only [hp, hm]

private theorem sourceSample_zero_of_positive_zeros (f : C_c(ℝ, ℝ))
    (hz : ∀ m : ℕ, 1 ≤ m → autocorr f ((m : ℝ) * Real.log 2) = 0)
    (k : ℤ) (hk : k ≠ 0) : sourceSample f k = 0 := by
  have hnat (n : ℕ) (hn : n ≠ 0) : sourceSample f (n : ℤ) = 0 := by
    unfold sourceSample
    rw [Int.cast_natCast]
    exact hz n (by omega)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact hnat n (fun hn => hk (by simp [hn]))
  · rw [sourceSample_neg]
    exact hnat n (fun hn => hk (by simp [hn]))

theorem correlationMass_of_source_zeros (f : C_c(ℝ, ℝ))
    (hz : ∀ m : ℕ, 1 ≤ m → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    correlationMass f = autocorr f 0 := by
  unfold correlationMass
  rw [tsum_eq_single 0]
  · simp only [sourceSample, Int.cast_zero, zero_mul, abs_of_nonneg (autocorr_zero_nonneg _)]
  · intro k hk
    rw [sourceSample_zero_of_positive_zeros f hz k hk, abs_zero]

theorem correctionMass_of_source_zeros (f : C_c(ℝ, ℝ))
    (hz : ∀ m : ℕ, 1 ≤ m → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    correctionMass f = 0 := by
  have he : correctionSample f = fun _ => 0 := by
    funext k
    by_cases hk : k = 0
    · simp [correctionSample, hk]
    · rw [correctionSample, if_neg hk, sourceSample_zero_of_positive_zeros f hz k hk]
      simp
  simp [correctionMass, he]

/-- The unconditional constant recovers the previous source-zero frame exactly. -/
theorem latticeFrame_of_source_zeros (f : C_c(ℝ, ℝ))
    (hz : ∀ m : ℕ, 1 ≤ m → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    latticeFrame f = autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f := by
  unfold latticeFrame
  rw [correlationMass_of_source_zeros f hz, correctionMass_of_source_zeros f hz, add_zero]
  rw [mul_assoc, mean_energy_mul_source_eq_variance]
  rfl

end
end GaloisForLFunctions.BiScaleUncertainty.SourceLattice
