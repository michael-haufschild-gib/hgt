import GaloisForLFunctions.BiScaleUncertainty.ProjectedHyperbolicGramControl

/-!
# Arithmetic collision energy for hyperbolic multiplier leakage

Equal pair differences form a single translation packet. Coalescing them gives
an exact weighted additive-collision energy and an explicit source cross-lag
error. A doubled source-zero range kills that error without assuming any
multiplier zeros. The unconditional form retains it in the full odd receiver.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ArithmeticMultiplierCollisions
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram
noncomputable section

def chainNode (δ : ℝ) (i : ℕ) : ℝ := (i : ℝ) * δ

def pairSet (N : ℕ) : Finset (ℕ × ℕ) := (Finset.range (N + 1)).offDiag

/-- Natural slot for the signed integer displacement j-i. -/
def lagSlot (N : ℕ) (p : ℕ × ℕ) : ℕ := N + p.2 - p.1

def lagNode (N : ℕ) (δ : ℝ) (r : ℕ) : ℝ := (r : ℝ) * δ - (N : ℝ) * δ

def lagPairs (N r : ℕ) : Finset (ℕ × ℕ) := (pairSet N).filter (fun p => lagSlot N p = r)

/-- All signed pair coefficients with the same displacement are added before squaring. -/
def lagAmplitude (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ p ∈ lagPairs N r, differenceWeight α w (chainNode δ) p

private theorem pair_bounds {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairSet N) :
    p.1 ≤ N ∧ p.2 ≤ N ∧ p.1 ≠ p.2 := by
  simpa only [pairSet, Finset.mem_offDiag, Finset.mem_range, Nat.lt_succ_iff] using hp

private theorem slot_mem {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairSet N) :
    lagSlot N p ∈ Finset.range (2 * N + 1) := by
  have h := pair_bounds hp
  simp only [Finset.mem_range, lagSlot]
  omega

private theorem displacement_slot {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairSet N) (δ : ℝ) :
    differenceNode (chainNode δ) p = lagNode N δ (lagSlot N p) := by
  have h := pair_bounds hp
  unfold differenceNode chainNode lagNode lagSlot
  rw [Nat.cast_sub (by omega : p.1 ≤ N + p.2), Nat.cast_add]
  ring

/-- Exact coalescence against any function of displacement. -/
theorem sum_lagAmplitude (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) (H : ℝ → ℝ) :
    (∑ r ∈ Finset.range (2 * N + 1), lagAmplitude N α δ w r * H (lagNode N δ r)) =
      ∑ p ∈ pairSet N, differenceWeight α w (chainNode δ) p *
        H (differenceNode (chainNode δ) p) := by
  have hg : (∑ r ∈ Finset.range (2 * N + 1), ∑ p ∈ lagPairs N r,
      differenceWeight α w (chainNode δ) p * H (differenceNode (chainNode δ) p)) =
      ∑ p ∈ pairSet N, differenceWeight α w (chainNode δ) p *
        H (differenceNode (chainNode δ) p) :=
    Finset.sum_fiberwise_of_maps_to (fun _ hp => slot_mem hp) _
  rw [← hg]
  apply Finset.sum_congr rfl
  intro r _
  rw [lagAmplitude, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  rw [displacement_slot hp'.1, hp'.2]

theorem lagAmplitude_center (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    lagAmplitude N α δ w N = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hb := pair_bounds hp'.1
  have hs := hp'.2
  unfold lagSlot at hs
  omega

/-- Positive-lag amplitudes are the weighted aperiodic correlation of the node weights. -/
theorem lagAmplitude_positive (N k : ℕ) (α δ : ℝ) (w : ℕ → ℝ)
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    lagAmplitude N α δ w (N + k) =
      (∑ i ∈ Finset.range (N + 1 - k), w i * w (i + k)) /
        (2 * Real.cosh (α * ((k : ℝ) * δ))) := by
  rw [Finset.sum_div]
  unfold lagAmplitude
  symm
  apply Finset.sum_bij (fun i _ => (i, i + k))
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [lagPairs, Finset.mem_filter, pairSet, Finset.mem_offDiag,
      Finset.mem_range, lagSlot]
    omega
  · intro i _ j _ hij
    exact congrArg Prod.fst hij
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hb := pair_bounds hp'.1
    have hs := hp'.2
    unfold lagSlot at hs
    refine ⟨p.1, Finset.mem_range.mpr (by omega), ?_⟩
    exact Prod.ext rfl (by dsimp; omega)
  · intro i _
    unfold differenceWeight differenceNode chainNode
    rw [Nat.cast_add]
    rw [show ((i : ℝ) + (k : ℝ)) * δ - (i : ℝ) * δ = (k : ℝ) * δ by ring]

/-- Uniform node weights retain the full number of colliding pairs at each positive lag. -/
theorem lagAmplitude_positive_one (N k : ℕ) (α δ : ℝ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    lagAmplitude N α δ (fun _ => 1) (N + k) =
      ((N + 1 - k : ℕ) : ℝ) / (2 * Real.cosh (α * ((k : ℝ) * δ))) := by
  rw [lagAmplitude_positive N k α δ _ hk hkN]
  simp

/-- Full source Gram energy of the pair packet equals the coalesced lag Gram. -/
theorem differenceGram_eq_lagGram (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    translationGramEnergy f (pairSet N) (differenceWeight α w (chainNode δ))
        (differenceNode (chainNode δ)) =
      translationGramEnergy f (Finset.range (2 * N + 1)) (lagAmplitude N α δ w) (lagNode N δ) := by
  rw [translationGramEnergy_eq_integral, translationGramEnergy_eq_integral]
  congr 1
  funext u
  rw [sum_lagAmplitude N α δ w (fun x => f (u + x))]

/-- Weighted additive-collision energy, including coherent cross terms at equal lags. -/
def collisionEnergy (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (2 * N + 1), lagAmplitude N α δ w r ^ 2

theorem collisionEnergy_nonneg (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    0 ≤ collisionEnergy N α δ w := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every remaining cross term is an original-source sample at an integer lag. -/
def crossLagError (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (2 * N + 1)).offDiag,
    lagAmplitude N α δ w p.1 * lagAmplitude N α δ w p.2 *
      autocorr f ((p.2 : ℝ) * δ - (p.1 : ℝ) * δ)

private theorem gram_diagonal_offDiag {ι : Type*} (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    translationGramEnergy f s w t = autocorr f 0 * (∑ i ∈ s, w i ^ 2) +
      ∑ p ∈ s.offDiag, w p.1 * w p.2 * autocorr f (t p.2 - t p.1) := by
  classical
  unfold translationGramEnergy
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [sub_self]; ring

/-- Exact collision decomposition; no source zero is assumed. -/
theorem differenceGram_eq_collision_add_error (f : C_c(ℝ, ℝ))
    (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    translationGramEnergy f (pairSet N) (differenceWeight α w (chainNode δ))
        (differenceNode (chainNode δ)) =
      autocorr f 0 * collisionEnergy N α δ w + crossLagError f N α δ w := by
  rw [differenceGram_eq_lagGram, gram_diagonal_offDiag]
  unfold collisionEnergy crossLagError
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  unfold lagNode
  ring

/-- Twice the original arithmetic zero range diagonalizes the coalesced packet. -/
theorem crossLagError_eq_zero_of_double_zeros (f : C_c(ℝ, ℝ))
    (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * δ) = 0) :
    crossLagError f N α δ w = 0 := by
  have ho := arithmetic_progression_pairwise_orth (f := (f : ℝ → ℝ)) 0 δ (2 * N) hz
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_offDiag.mp hp
  have hh := ho p.2 hp'.2.1 p.1 hp'.1 (Ne.symm hp'.2.2)
  simp only [zero_add] at hh
  rw [hh, mul_zero]

theorem differenceGram_eq_collision_of_double_zeros (f : C_c(ℝ, ℝ))
    (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * δ) = 0) :
    translationGramEnergy f (pairSet N) (differenceWeight α w (chainNode δ))
        (differenceNode (chainNode δ)) = autocorr f 0 * collisionEnergy N α δ w := by
  rw [differenceGram_eq_collision_add_error, crossLagError_eq_zero_of_double_zeros f N α δ w hz,
    add_zero]

theorem mean_energy_mul_source_eq_variance (f : C_c(ℝ, ℝ)) (α : ℝ) :
    autocorr (centeredSource f α (sourceMean f α)) 0 * autocorr f 0 = sourceVariance f α := by
  have h := centered_energy_variance_identity f α (sourceMean f α)
  have hm : autocorr f 0 * sourceMean f α - coshMass f α = 0 := by
    unfold sourceMean
    by_cases hR : autocorr f 0 = 0
    · have hn := sourceVariance_nonneg f α
      unfold sourceVariance at hn
      rw [hR] at hn
      have hM : coshMass f α = 0 := by nlinarith [sq_nonneg (coshMass f α)]
      simp [hR, hM]
    · field_simp
      ring
  rw [hm] at h
  nlinarith only [h]

/-- Exact source-grid control of odd multiplier leakage by weighted collision energy. -/
theorem odd_defect_abs_le_variance_collision (f : C_c(ℝ, ℝ))
    (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr (oddCompactSource f) ((m : ℝ) * δ) = 0) :
    |sinhCliqueGramDefect (oddCompactSource f) α (Finset.range (N + 1)) w (chainNode δ)| ≤
      Real.sqrt (sourceVariance (oddCompactSource f) α * collisionEnergy N α δ w) := by
  let F := oddCompactSource f
  have ho := arithmetic_progression_pairwise_orth (f := (F : ℝ → ℝ)) 0 δ N
    (fun m hm hmn => hz m hm (by omega))
  have he : sourceCorrection F α (sourceMean F α) (Finset.range (N + 1)) w (chainNode δ) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    have hh := ho p.2 hp'.2.1 p.1 hp'.1 (Ne.symm hp'.2.2)
    simp only [zero_add] at hh
    change _ * autocorr F ((p.2 : ℝ) * δ - (p.1 : ℝ) * δ) = 0
    rw [hh, mul_zero]
  have h := odd_defect_abs_sub_correction_le f α (sourceMean F α)
    (Finset.range (N + 1)) w (chainNode δ)
  rw [he, sub_zero] at h
  change |sinhCliqueGramDefect F α (Finset.range (N + 1)) w (chainNode δ)| ≤
    Real.sqrt (autocorr (centeredSource F α (sourceMean F α)) 0 *
      translationGramEnergy F (pairSet N) (differenceWeight α w (chainNode δ))
        (differenceNode (chainNode δ))) at h
  rw [differenceGram_eq_collision_of_double_zeros F N α δ w hz,
    ← mul_assoc, mean_energy_mul_source_eq_variance] at h
  exact h

/-- Full logarithmic source blindness supplies the doubled dyadic zero range. -/
theorem odd_logGrid_defect_abs_le_variance_collision (f : C_c(ℝ, ℝ))
    (N : ℕ) (α : ℝ) (w : ℕ → ℝ)
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    |sinhCliqueGramDefect (oddCompactSource f) α (Finset.range (N + 1)) w (chainNode (Real.log 2))| ≤
      Real.sqrt (sourceVariance (oddCompactSource f) α * collisionEnergy N α (Real.log 2) w) := by
  apply odd_defect_abs_le_variance_collision
  intro m hm _
  have hb : ∀ k : ℕ, 2 ≤ 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have hp : 2 ≤ 2 ^ m := by cases m with
    | zero => omega
    | succ m => exact hb m
  have h := hz (2 ^ m) hp
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

def lagCovariance (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (2 * N + 1), lagAmplitude N α δ w r * autocorr f (lagNode N δ r)

def lagCorrection (f : C_c(ℝ, ℝ)) (N : ℕ) (α c δ : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (2 * N + 1), lagAmplitude N α δ w r *
    (c - Real.cosh (α * lagNode N δ r) ^ 2) * autocorr f (lagNode N δ r)

theorem packetCovariance_eq_lags (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    packetCovariance f (pairSet N) (differenceWeight α w (chainNode δ))
        (differenceNode (chainNode δ)) = lagCovariance f N α δ w :=
  (sum_lagAmplitude N α δ w (autocorr f)).symm

theorem sourceCorrection_eq_lags (f : C_c(ℝ, ℝ)) (N : ℕ) (α c δ : ℝ) (w : ℕ → ℝ) :
    sourceCorrection f α c (Finset.range (N + 1)) w (chainNode δ) = lagCorrection f N α c δ w := by
  simpa only [sourceCorrection, lagCorrection, pairSet, mul_assoc] using
    (sum_lagAmplitude N α δ w (fun x => (c - Real.cosh (α * x) ^ 2) * autocorr f x)).symm

/-- The signed cross-lag error still gives an actual nonnegative Schur energy. -/
theorem collisionSchur_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    0 ≤ autocorr f 0 * collisionEnergy N α δ w + crossLagError f N α δ w -
      lagCovariance f N α δ w ^ 2 / autocorr f 0 := by
  have h := packetSchurEnergy_nonneg f (pairSet N)
    (differenceWeight α w (chainNode δ)) (differenceNode (chainNode δ))
  unfold packetSchurEnergy at h
  rwa [differenceGram_eq_collision_add_error, packetCovariance_eq_lags] at h

/-- Source-only leakage envelope exposing the collision, cross-lag and projection terms. -/
def collisionDefectUpper (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) : ℝ :=
  lagCorrection f N α (sourceMean f α) δ w +
    Real.sqrt (autocorr (centeredSource f α (sourceMean f α)) 0 *
      (autocorr f 0 * collisionEnergy N α δ w + crossLagError f N α δ w -
        lagCovariance f N α δ w ^ 2 / autocorr f 0))

theorem collisionDefectUpper_eq_projected (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    collisionDefectUpper f N α δ w =
      projectedDefectUpper f α (Finset.range (N + 1)) w (chainNode δ) := by
  unfold collisionDefectUpper projectedDefectUpper packetSchurEnergy
  rw [sourceCorrection_eq_lags,
    show (Finset.range (N + 1)).offDiag = pairSet N from rfl,
    differenceGram_eq_collision_add_error, packetCovariance_eq_lags]

theorem odd_defect_le_collisionDefectUpper (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    sinhCliqueGramDefect (oddCompactSource f) α (Finset.range (N + 1)) w (chainNode δ) ≤
      collisionDefectUpper (oddCompactSource f) N α δ w := by
  rw [collisionDefectUpper_eq_projected]
  exact odd_defect_le_projectedDefectUpper f α _ w _

/-- The entire envelope reduces to the variance-collision product on the doubled zero range. -/
theorem collisionDefectUpper_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * δ) = 0) :
    collisionDefectUpper f N α δ w = Real.sqrt (sourceVariance f α * collisionEnergy N α δ w) := by
  have ho := arithmetic_progression_pairwise_orth (f := (f : ℝ → ℝ)) 0 δ N
    (fun m hm hmn => hz m hm (by omega))
  have hp : ∀ p ∈ (Finset.range (N + 1)).offDiag,
      autocorr f (differenceNode (chainNode δ) p) = 0 := by
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    simpa only [zero_add, differenceNode, chainNode] using
      ho p.2 hp'.2.1 p.1 hp'.1 (Ne.symm hp'.2.2)
  have h := sourceClique_centering_boundary f α (Finset.range (N + 1)) w (chainNode δ) hp
  rw [collisionDefectUpper_eq_projected, h.2.1, sourceDefectUpper, h.1, zero_add]
  change Real.sqrt (autocorr (centeredSource f α (sourceMean f α)) 0 *
    translationGramEnergy f (pairSet N) (differenceWeight α w (chainNode δ))
      (differenceNode (chainNode δ))) = _
  rw [differenceGram_eq_collision_of_double_zeros f N α δ w hz,
    ← mul_assoc, mean_energy_mul_source_eq_variance]

/-- Arithmetic collar lower bound with every source cross-lag error retained. -/
def collisionJumpBound (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) (b : ℕ → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      ((∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode δ) y i *
        Real.cosh ((chainNode δ i - y) / 2)) -
        Real.sqrt (∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode δ) y i ^ 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      max (collisionDefectUpper f N (1 / 2) δ (sinhJumpTransferWeights f b (chainNode δ) y)) 0)

theorem collisionJumpBound_eq_projected (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) (b : ℕ → ℝ) (y : ℝ) :
    collisionJumpBound f N δ b y = projectedJumpBound f (Finset.range (N + 1)) b (chainNode δ) y := by
  unfold collisionJumpBound projectedJumpBound
  rw [collisionDefectUpper_eq_projected]

theorem continuous_collisionJumpBound (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) (b : ℕ → ℝ) :
    Continuous (collisionJumpBound f N δ b) := by
  have he : collisionJumpBound f N δ b = projectedJumpBound f (Finset.range (N + 1)) b (chainNode δ) :=
    funext fun y => collisionJumpBound_eq_projected f N δ b y
  rw [he]
  exact continuous_projectedJumpBound _ _ _ _

theorem odd_secantJumpCollar_ge_collision (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) (b : ℕ → ℝ) (y : ℝ) :
    collisionJumpBound (oddCompactSource f) N δ b y ≤
      secantJumpCollar (oddCompactSource f) (Finset.range (N + 1)) b (chainNode δ) y := by
  rw [collisionJumpBound_eq_projected]
  exact odd_secantJumpCollar_ge_projected _ _ _ _ _

/-- Full original secant receiver in explicit arithmetic-collision coordinates. -/
theorem odd_secantEnergy_ge_collision (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) :
    (∫ y in (0 : ℝ)..|δ|, collisionJumpBound (oddCompactSource f) N |δ| (fun _ => 1) (-y)) ≤
      biScaleSecantEnergy (oddCompactSource f) := by
  simp_rw [collisionJumpBound_eq_projected]
  exact odd_secantEnergy_ge_projected f δ (N + 1)

/-- Actual odd plastic functional, with measured collisions and all nonzero cross-lag errors. -/
theorem odd_plasticCrossover_ge_collision (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) :
    (∫ y in (0 : ℝ)..|δ|, collisionJumpBound (oddCompactSource f) N |δ| (fun _ => 1) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  simp_rw [collisionJumpBound_eq_projected]
  exact odd_plasticCrossover_ge_projected f δ (N + 1)

/-- On the doubled source-zero range the only leakage cost is the variance-collision product. -/
theorem collisionJumpBound_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (δ : ℝ) (b : ℕ → ℝ) (y : ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * δ) = 0) :
    collisionJumpBound f N δ b y =
      autocorr (sinhCompact (1 / 2) f) 0 *
        ((∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode δ) y i *
          Real.cosh ((chainNode δ i - y) / 2)) -
          Real.sqrt (∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode δ) y i ^ 2)) -
      Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
        Real.sqrt (sourceVariance f (1 / 2) *
          collisionEnergy N (1 / 2) δ (sinhJumpTransferWeights f b (chainNode δ) y))) := by
  unfold collisionJumpBound
  rw [collisionDefectUpper_of_double_zeros f N (1 / 2) δ _ hz,
    max_eq_left (Real.sqrt_nonneg _)]

end
end GaloisForLFunctions.BiScaleUncertainty.ArithmeticMultiplierCollisions
