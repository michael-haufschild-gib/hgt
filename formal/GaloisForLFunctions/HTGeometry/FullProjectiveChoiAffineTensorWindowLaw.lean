import GaloisForLFunctions.HTGeometry.ProjectiveChoiTensorMajorantWindowLaw
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowAffineCharacterWindow

open Real intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Full projective frequency packet: the clock harmonic followed by all
clock-normalized spectral ratios. -/
def fullProjectiveFrequency (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 y

def packetClockCharacter (k : Fin (n + 1) → ℕ × ℕ) : ℤ :=
  packetCharacter k 0

def packetRatioCharacter (k : Fin (n + 1) → ℕ × ℕ) : Fin n → ℤ :=
  fun j => packetCharacter k j.succ

theorem dotProd_packetCharacter_fullProjectiveFrequency
    (y : Fin n → ℝ) (k : Fin (n + 1) → ℕ × ℕ) :
    KleinbockMargulis.dotProd (packetCharacter k) (fullProjectiveFrequency y) =
      (packetClockCharacter k : ℝ) +
        KleinbockMargulis.dotProd (packetRatioCharacter k) y := by
  rw [KleinbockMargulis.dotProd, Fin.sum_univ_succ]
  simp only [fullProjectiveFrequency, packetClockCharacter,
    Fin.cons_zero, Fin.cons_succ, mul_one]
  rfl

theorem packetFreq_fullProjectiveFrequency
    (y : Fin n → ℝ) (k : Fin (n + 1) → ℕ × ℕ) :
    packetFreq (fullProjectiveFrequency y) k =
      KleinbockMargulis.dotProd (packetRatioCharacter k) y +
        (packetClockCharacter k : ℝ) := by
  rw [← dotProd_packetCharacter, dotProd_packetCharacter_fullProjectiveFrequency]
  ring

theorem packetAffineCharacter_nonconstant
    {N : ℕ} {k : Fin (n + 1) → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N (n + 1)) :
    packetClockCharacter k ≠ 0 ∨ packetRatioCharacter k ≠ 0 := by
  by_contra h
  push Not at h
  apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hk
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h.1
  · exact congrFun h.2 j

/-- Full-projective affine Fourier cost; clock harmonic is separated from
the multiplicative height of ratio characters. -/
noncomputable def periodicFejerMajorantAffineMultiplicativeCost
    (N : ℕ) (rho e : ℝ) (c : Fin (n + 1) → ℝ) (eps : ℝ) : ℝ :=
  KleinbockMargulis.indexedMultiplicativeFourierL1Cost
    (ι := {k // k ∈ nonconstantPacketIndexSet N (n + 1)})
    (fun k => majorantPacketAmp N rho e c k.1)
    (fun k => packetRatioCharacter k.1) eps

theorem periodicFejerMajorantAffineMultiplicativeCost_center_independent
    (N : ℕ) (rho e : ℝ) (c c' : Fin (n + 1) → ℝ) (eps : ℝ) :
    periodicFejerMajorantAffineMultiplicativeCost N rho e c eps =
      periodicFejerMajorantAffineMultiplicativeCost N rho e c' eps := by
  classical
  simp only [periodicFejerMajorantAffineMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_majorantPacketAmp_center_independent N rho e c c' k.1]

/-- Full-projective tensor majorant discrepancy from the affine character
law. -/
theorem exists_uniform_fullProjectiveFejerMajorant_affineWindowDiscrepancy
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin (n + 1) → ℝ) (u T : ℝ), 0 < T →
      ‖((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ((periodicProductFejerMajorant N rho c
              (fun j => t * fullProjectiveFrequency y j) : ℝ) : ℂ)) -
          ((((rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) : ℝ) : ℂ))‖ ≤
        (2 * C / T) * periodicFejerMajorantAffineMultiplicativeCost N rho
          (periodicTentFejerError N rho) c eps := by
  classical
  set S := nonconstantPacketIndexSet N (n + 1) with hS
  obtain ⟨C, hC, hpacket⟩ :=
    KleinbockMargulis.exists_global_indexedAffineFourierPacketHaarDiscrepancy
      (n := n) (ι := {k // k ∈ S}) hy heps
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerMajorant N rho c
          (fun j => t * fullProjectiveFrequency y j) : ℝ) : ℂ) =
        ((((rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) : ℝ) : ℂ)) +
          ∑ i : {k // k ∈ S},
            majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1 *
              Complex.exp ((t : ℂ) *
                ((KleinbockMargulis.dotProd (packetRatioCharacter i.1) y +
                  (packetClockCharacter i.1 : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [periodicProductFejerMajorant_eq_const_add N hrho hrhopi]
    rw [← hS]
    congr 1
    rw [Finset.sum_coe_sort S (fun k =>
      majorantPacketAmp N rho (periodicTentFejerError N rho) c k *
        Complex.exp ((t : ℂ) *
          ((KleinbockMargulis.dotProd (packetRatioCharacter k) y +
            (packetClockCharacter k : ℝ) : ℝ) : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ => by
      rw [majorantPacketMode_linearPhase N rho (periodicTentFejerError N rho)
        c (fullProjectiveFrequency y) k t,
        packetFreq_fullProjectiveFrequency]
  have hmain := hpacket
    (((rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) : ℝ) : ℂ)
    (fun i : {k // k ∈ S} =>
      majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1)
    (fun i : {k // k ∈ S} => packetClockCharacter i.1)
    (fun i : {k // k ∈ S} => packetRatioCharacter i.1)
    (fun i => by
      apply packetAffineCharacter_nonconstant
      rw [← hS]
      exact i.2) u T hT
  rw [show periodicFejerMajorantAffineMultiplicativeCost N rho
      (periodicTentFejerError N rho) c eps =
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost
      (fun i : {k // k ∈ S} =>
        majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1)
      (fun i : {k // k ∈ S} => packetRatioCharacter i.1) eps by rfl]
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * fullProjectiveFrequency y j) : ℝ) : ℂ)) =
      ∫ t in u..(u + T),
        (((((rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) : ℝ) : ℂ)) +
          ∑ i : {k // k ∈ S},
            majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1 *
              Complex.exp ((t : ℂ) *
                ((KleinbockMargulis.dotProd (packetRatioCharacter i.1) y +
                  (packetClockCharacter i.1 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [hInt]
  exact hmain

/-- Ratio-tail height bound for every full-projective packet sheet. -/
theorem packetRatioCharacter_piPlus_le
    (N : ℕ) {k : Fin (n + 1) → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N (n + 1)) :
    KleinbockMargulis.PiPlus (packetRatioCharacter k) ≤
      (2 * ((N : ℝ) + 1)) ^ n := by
  classical
  have hfull : k ∈ Fintype.piFinset (fun _ : Fin (n + 1) =>
      Finset.range (N + 1) ×ˢ Finset.range (N + 1)) :=
    (Finset.mem_sdiff.mp hk).1
  rw [KleinbockMargulis.PiPlus]
  calc
    (∏ j, max |(packetRatioCharacter k j : ℝ)| 1) ≤
        ∏ _j : Fin n, (2 * ((N : ℝ) + 1)) := by
      refine Finset.prod_le_prod (fun j _ => by positivity) ?_
      intro j _
      have hj := Fintype.mem_piFinset.mp hfull j.succ
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hj
      have ha : ((k j.succ).1 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hj.1
      have hb : ((k j.succ).2 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hj.2
      apply max_le
      · simp only [packetRatioCharacter, packetCharacter]
        rw [abs_le]
        constructor <;> push_cast <;> linarith
      · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
    _ = (2 * ((N : ℝ) + 1)) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem packetRatioCharacter_multiplicativeWeight_le
    (N : ℕ) {eps : ℝ} (heps : 0 ≤ eps)
    {k : Fin (n + 1) → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N (n + 1)) :
    KleinbockMargulis.PiPlus (packetRatioCharacter k) /
        KleinbockMargulis.PiPlus (packetRatioCharacter k) ^ (-eps) ≤
      (2 * ((N : ℝ) + 1)) ^ ((n : ℝ) * (1 + eps)) := by
  let P := KleinbockMargulis.PiPlus (packetRatioCharacter k)
  let B := 2 * ((N : ℝ) + 1)
  have hP : 0 < P := KleinbockMargulis.PiPlus_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hPB : P ≤ B ^ n := packetRatioCharacter_piPlus_le N hk
  rw [div_rpow_neg_eq_rpow_one_add hP]
  calc
    P ^ (1 + eps) ≤ (B ^ n) ^ (1 + eps) :=
      Real.rpow_le_rpow hP.le hPB (by linarith)
    _ = B ^ ((n : ℝ) * (1 + eps)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hB.le]

noncomputable def periodicFejerMajorantAffineCostUpperBound
    (N n : ℕ) (rho e eps : ℝ) : ℝ :=
  ((N : ℝ) + 1) ^ (2 * (n + 1)) *
    (((((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ (n + 1)) *
      (2 * ((N : ℝ) + 1)) ^ ((n : ℝ) * (1 + eps)))

theorem periodicFejerMajorantAffineMultiplicativeCost_le_explicit
    (N : ℕ) {rho e eps : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (he : 0 ≤ e) (heps : 0 ≤ eps) (c : Fin (n + 1) → ℝ) :
    periodicFejerMajorantAffineMultiplicativeCost N rho e c eps ≤
      periodicFejerMajorantAffineCostUpperBound N n rho e eps := by
  classical
  let A : ℝ := (((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ (n + 1)
  let W : ℝ := (2 * ((N : ℝ) + 1)) ^ ((n : ℝ) * (1 + eps))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  rw [periodicFejerMajorantAffineMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  calc
    (∑ k : {k // k ∈ nonconstantPacketIndexSet N (n + 1)},
        ‖majorantPacketAmp N rho e c k.1‖ *
          (KleinbockMargulis.PiPlus (packetRatioCharacter k.1) /
            KleinbockMargulis.PiPlus (packetRatioCharacter k.1) ^ (-eps))) ≤
      ∑ _k : {k // k ∈ nonconstantPacketIndexSet N (n + 1)}, A * W := by
        refine Finset.sum_le_sum fun k _ => ?_
        apply mul_le_mul
        · exact norm_majorantPacketAmp_le N hrho hrhopi he c k.1
        · exact packetRatioCharacter_multiplicativeWeight_le N heps k.2
        · have hP := KleinbockMargulis.PiPlus_pos (packetRatioCharacter k.1)
          exact div_nonneg hP.le (Real.rpow_pos_of_pos hP _).le
        · exact hA
    _ = (((nonconstantPacketIndexSet N (n + 1)).card : ℝ) * (A * W)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast Fintype.card_coe (nonconstantPacketIndexSet N (n + 1))
    _ ≤ ((N : ℝ) + 1) ^ (2 * (n + 1)) * (A * W) := by
      exact mul_le_mul_of_nonneg_right (card_modeIndex_le (d := n + 1) N)
        (mul_nonneg hA hW)
    _ = periodicFejerMajorantAffineCostUpperBound N n rho e eps := by rfl

/-- Full-projective product-tent upper law with multiplicative tensor
remainder. -/
theorem exists_uniform_windowMean_fullProjectiveTent_le_affineTensorMajorant
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin (n + 1) → ℝ) (u T : ℝ), 0 < T →
      (1 / T) * ∫ t in u..(u + T),
          periodicProductTent rho c
            (fun j => t * fullProjectiveFrequency y j) ≤
        (rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) +
          (2 * C / T) * periodicFejerMajorantAffineMultiplicativeCost N rho
            (periodicTentFejerError N rho) c eps := by
  obtain ⟨C, hC, hdisc⟩ :=
    exists_uniform_fullProjectiveFejerMajorant_affineWindowDiscrepancy
      hy heps N hrho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hcontM := continuous_periodicProductFejerMajorant N rho c
    (fullProjectiveFrequency y)
  have hcontT := continuous_periodicProductTent rho c (fullProjectiveFrequency y)
  have hd := hdisc c u T hT
  let Z : ℂ :=
    ((1 / (T : ℂ)) *
        ∫ t in u..(u + T),
          ((periodicProductFejerMajorant N rho c
            (fun j => t * fullProjectiveFrequency y j) : ℝ) : ℂ)) -
      ((((rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) : ℝ) : ℂ))
  have hre : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hdZ : ‖Z‖ ≤
      (2 * C / T) * periodicFejerMajorantAffineMultiplicativeCost N rho
        (periodicTentFejerError N rho) c eps := by
    simpa [Z] using hd
  have hupper := (abs_le.mp (hre.trans hdZ)).2
  dsimp [Z] at hupper
  rw [re_window_mean_ofReal hcontM hT u] at hupper
  have hpi : u ≤ u + T := by linarith
  have hmono :
      (∫ t in u..(u + T),
          periodicProductTent rho c
            (fun j => t * fullProjectiveFrequency y j)) ≤
        ∫ t in u..(u + T),
          periodicProductFejerMajorant N rho c
            (fun j => t * fullProjectiveFrequency y j) := by
    refine intervalIntegral.integral_mono_on hpi
      (hcontT.intervalIntegrable _ _) (hcontM.intervalIntegrable _ _) ?_
    intro t _
    exact periodicProductTent_le_periodicProductFejerMajorant N hrho c _
  have hupper' :
      (1 / T) * ∫ t in u..(u + T),
          periodicProductFejerMajorant N rho c
            (fun j => t * fullProjectiveFrequency y j) ≤
        (rho / (2 * π) + periodicTentFejerError N rho) ^ (n + 1) +
          (2 * C / T) * periodicFejerMajorantAffineMultiplicativeCost N rho
            (periodicTentFejerError N rho) c eps := by
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hmono (by positivity)) hupper'

/-- Complete adaptive cube union for the full projective orbit, including
the clock coordinate. -/
theorem exists_adaptiveFullProjectiveFiniteCubeUnion_centerFreeTensorWindowUpper
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) (N m : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Fin m → Fin (n + 1) → ℝ) (u T : ℝ), 0 < T →
        (volume (finiteCubeVisit rho c (fullProjectiveFrequency y) ∩
          Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ (n + 1) * T *
            (((m : ℕ) : ℝ) *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ (n + 1) +
              (2 * C / T) * ((m : ℝ) *
                periodicFejerMajorantAffineCostUpperBound N n (2 * rho)
                  (periodicTentFejerError N (2 * rho)) eps)) := by
  have h2rho : 0 < 2 * rho := by positivity
  obtain ⟨C, hC, hsingle⟩ :=
    exists_uniform_windowMean_fullProjectiveTent_le_affineTensorMajorant
      hy heps N h2rho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have he : 0 ≤ periodicTentFejerError N (2 * rho) :=
    (periodicTentFejerError_pos N h2rho).le
  have hcont : ∀ a : Fin m, Continuous fun t : ℝ =>
      periodicProductTent (2 * rho) (c a)
        (fun j => t * fullProjectiveFrequency y j) :=
    fun a => continuous_periodicProductTent (2 * rho) (c a)
      (fullProjectiveFrequency y)
  have hsingleExplicit : ∀ a : Fin m,
      (1 / T) * ∫ t in u..(u + T),
          periodicProductTent (2 * rho) (c a)
            (fun j => t * fullProjectiveFrequency y j) ≤
        (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ (n + 1) +
          (2 * C / T) * periodicFejerMajorantAffineCostUpperBound N n (2 * rho)
            (periodicTentFejerError N (2 * rho)) eps := by
    intro a
    refine (hsingle (c a) u T hT).trans ?_
    have hcost := periodicFejerMajorantAffineMultiplicativeCost_le_explicit
      (n := n) N h2rho hrhopi he heps.le (c a)
    gcongr
  have hsumInt :
      (1 / T) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
            (fun j => t * fullProjectiveFrequency y j) ≤
        ((m : ℕ) : ℝ) *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ (n + 1) +
          (2 * C / T) * ((m : ℝ) *
            periodicFejerMajorantAffineCostUpperBound N n (2 * rho)
              (periodicTentFejerError N (2 * rho)) eps) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      calc
        ∑ a : Fin m, (1 / T) *
            ∫ t in u..(u + T),
              periodicProductTent (2 * rho) (c a)
                (fun j => t * fullProjectiveFrequency y j) ≤
          ∑ _a : Fin m,
            ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ (n + 1) +
              (2 * C / T) * periodicFejerMajorantAffineCostUpperBound N n (2 * rho)
                (periodicTentFejerError N (2 * rho)) eps) := by
            exact Finset.sum_le_sum fun a _ => hsingleExplicit a
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    · intro a _
      exact (hcont a).intervalIntegrable u (u + T)
  have hle : u ≤ u + T := by linarith
  have hfin : volume (Set.Ioc u (u + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIf : IntegrableOn
      (Set.indicator (finiteCubeVisit rho c (fullProjectiveFrequency y))
        (fun _ => (1 : ℝ))) (Set.Ioc u (u + T)) :=
    (integrableOn_const (C := (1 : ℝ)) hfin (by simp)).indicator
      (measurableSet_finiteCubeVisit rho c (fullProjectiveFrequency y))
  have hIg : IntegrableOn
      (fun t => (2 : ℝ) ^ (n + 1) * ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a)
          (fun j => t * fullProjectiveFrequency y j))
      (Set.Ioc u (u + T)) := by
    have hc : Continuous fun t : ℝ => ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a)
          (fun j => t * fullProjectiveFrequency y j) :=
      continuous_finsetSum _ fun a _ => hcont a
    exact (continuous_const.mul hc).intervalIntegrable u (u + T) |>.1
  have hmono :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c (fullProjectiveFrequency y))
            (fun _ => (1 : ℝ)) t ≤
        ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ (n + 1) * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a)
              (fun j => t * fullProjectiveFrequency y j) :=
    setIntegral_mono_on hIf hIg measurableSet_Ioc fun t _ =>
      indicator_finiteCubeVisit_le_scaled_sum_tent hrho c
        (fullProjectiveFrequency y) t
  have hind :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c (fullProjectiveFrequency y))
            (fun _ => (1 : ℝ)) t =
        (volume (finiteCubeVisit rho c (fullProjectiveFrequency y) ∩
          Set.Ioc u (u + T))).toReal := by
    rw [setIntegral_indicator
      (measurableSet_finiteCubeVisit rho c (fullProjectiveFrequency y)),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [Set.inter_comm]
  have hright :
      ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ (n + 1) * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a)
              (fun j => t * fullProjectiveFrequency y j) =
        (2 : ℝ) ^ (n + 1) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
            (fun j => t * fullProjectiveFrequency y j) := by
    rw [← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_const_mul]
  rw [hind, hright] at hmono
  have hTmul := mul_le_mul_of_nonneg_left hsumInt (le_of_lt hT)
  have hInt :
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
          (fun j => t * fullProjectiveFrequency y j)) ≤
        T * (((m : ℕ) : ℝ) *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ (n + 1) +
            (2 * C / T) * ((m : ℝ) *
              periodicFejerMajorantAffineCostUpperBound N n (2 * rho)
                (periodicTentFejerError N (2 * rho)) eps)) := by
    calc
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
          (fun j => t * fullProjectiveFrequency y j)) =
          T * ((1 / T) * ∫ t in u..(u + T),
            ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
              (fun j => t * fullProjectiveFrequency y j)) := by field_simp
      _ ≤ _ := hTmul
  have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by positivity
  exact hmono.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hInt hscale)

/-- Full physical projective-Choi target law: anchor, clock, and every ratio
coordinate are retained. -/
theorem exists_fullProjectiveMetricBallFamily_centerFreeTensorWindowUpper
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius (n + 1) delta ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (u T : ℝ), 0 < T →
        (volume
          (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
              (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ (n + 1) * T *
            (((m : ℕ) : ℝ) *
                (2 * zeroAnchoredChoiAngularRadius (n + 1) delta / (2 * π) +
                  periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) ^ (n + 1) +
              (2 * C / T) * ((m : ℝ) *
                periodicFejerMajorantAffineCostUpperBound N n
                  (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)
                  (periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius (n + 1) delta)) eps)) := by
  let rho : ℝ := zeroAnchoredChoiAngularRadius (n + 1) delta
  have hrho : 0 < rho := by
    change 0 < zeroAnchoredChoiAngularRadius (n + 1) delta
    rw [zeroAnchoredChoiAngularRadius]
    positivity
  obtain ⟨C, hC, hcube⟩ :=
    exists_adaptiveFullProjectiveFiniteCubeUnion_centerFreeTensorWindowUpper
      hy heps N m hrho (by simpa only [rho] using hsmall)
  refine ⟨C, hC, ?_⟩
  intro target u T hT
  have hsub :
      zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
          (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T) ⊆
        finiteCubeVisit rho
            (fun a => zeroAnchoredMetricBallAngularCenter (n + 1) (target a) delta)
            (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _
      (zeroAnchoredMetricBallFamilyAngularVisit_subset_finiteCubeVisit
        (n + 1) m hdelta target (fullProjectiveFrequency y))
  have hrhsFinite :
      volume
          (finiteCubeVisit rho
              (fun a => zeroAnchoredMetricBallAngularCenter (n + 1) (target a) delta)
              (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m delta target
          (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T))).toReal ≤
      (volume
        (finiteCubeVisit rho
          (fun a => zeroAnchoredMetricBallAngularCenter (n + 1) (target a) delta)
          (fullProjectiveFrequency y) ∩ Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrhsFinite
  have hc := hcube
    (fun a => zeroAnchoredMetricBallAngularCenter (n + 1) (target a) delta)
    u T hT
  exact hreal.trans (by simpa only [rho] using hc)

end

end GaloisForLFunctions.HTGeometry
