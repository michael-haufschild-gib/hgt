import GaloisForLFunctions.RHTower.StaticChoiCarrierPurityCrowdingLaw

/-!
# Return-free coherence floor and the required target-compression scale

This file tests the carrier-independent purity surrogate, not the unproved
ordinary-local-ensemble incidence-action bound.

For every spectrum in positive dimension, every replica order, and every
possibly circuit-budget-dependent initial cutoff `a`, choose
`T = 1 + 4*|a| + u^2`. The full pair purity on the two surviving Gaussian
source sheets satisfies

`P >= gaussianFloorTwo^2 / (16 * sqrt(r+1) * staticChoiSpeed energy * T)`.

Nearby surviving times, rather than early returns or a minimum spectral gap,
force this floor. At fixed errors 1/2 and 3/4 it strictly exceeds the Gaussian
first-entry receiver threshold at every replica order. Hence discarding
target projection cannot close that receiver even by letting replicas grow.

The positive boundary is quantitative: for any actual carrier action `A`
and any positive capacity `N=k+1`, either the receiver budget fails or

`A/P < sqrt(r+1) * (7/16)^(2*r) / (4*N*staticChoiSpeed energy*T)`.

This is a necessary compression requirement, not an ensemble suppression
theorem. Carrier action retains the actual target subspace and both source
restrictions. No circuit-image weight, source fibre, spectral degeneracy,
or initial cutoff is assumed away. Public capstones take only data, with
positive dimension and admissible time built into their parametrization.
No external-literature novelty or new-physics claim is made.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Full pair purity after removing the actual initial interval from both source times.
No target projection is applied in this quantity. -/
def returnExcisedStaticChoiPairPurity (d : ℕ) (energy : Fin d → ℝ)
    (r : ℕ) (a T : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, finitePureStateFidelity
      (staticSpectralChoiVector d (T * p.1) energy).ofLp
      (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
    ∂(((gaussianReal 0 1).restrict (Icc (-|a| / T) (|a| / T))ᶜ).prod
      ((gaussianReal 0 1).restrict (Icc (-|a| / T) (|a| / T))ᶜ))

private theorem staticChoiSpeed_one_le {d : ℕ} (energy : Fin d → ℝ) :
    1 ≤ staticChoiSpeed energy := by
  unfold staticChoiSpeed
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => abs_nonneg (energy i))

private theorem real_gaussian_shifted_interval_lower {x δ : ℝ}
    (hx : |x| ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    2 * gaussianFloorTwo * δ ≤ (gaussianReal 0 1).real (Icc (x - δ) (x + δ)) := by
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (gaussianReal_Icc_shifted_lower hx hδ0 hδ1)
  rw [ENNReal.toReal_ofReal (by positivity [gaussianFloorTwo_pos])] at h
  exact h

private theorem staticChoi_replica_coherence_lower
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (r : ℕ)
    {T x y : ℝ} (hT : 1 ≤ T)
    (hxy : |x - y| ≤ 1 /
      (4 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T)) :
    (1 / 2 : ℝ) ≤ finitePureStateFidelity
      (staticSpectralChoiVector d (T * x) energy).ofLp
      (staticSpectralChoiVector d (T * y) energy).ofLp ^ r := by
  let b : ℝ := 1 / (4 * Real.sqrt ((r : ℝ) + 1))
  have hR : 0 < Real.sqrt ((r : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hS : 0 < staticChoiSpeed energy := staticChoiSpeed_pos energy
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hdist : pureStateTraceDistance
      (staticSpectralChoiVector d (T * x) energy)
      (staticSpectralChoiVector d (T * y) energy) ≤ b := by
    calc
      _ ≤ staticChoiSpeed energy * |T * x - T * y| :=
        pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy _ _
      _ = (staticChoiSpeed energy * T) * |x - y| := by
        rw [← mul_sub, abs_mul, abs_of_pos hTpos, mul_assoc]
      _ ≤ (staticChoiSpeed energy * T) *
          (1 / (4 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T)) :=
        mul_le_mul_of_nonneg_left hxy (mul_nonneg hS.le hTpos.le)
      _ = b := by
        dsimp [b]
        field_simp [hR.ne', hS.ne', hTpos.ne']
  have hb0 : 0 ≤ b := by positivity
  have hsq := sq_pureStateTraceDistance
    (staticSpectralChoiVector d (T * x) energy)
    (staticSpectralChoiVector d (T * y) energy)
    (staticSpectralChoiVector_norm hd _ energy).le
    (staticSpectralChoiVector_norm hd _ energy).le
  have hdistSq := (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) hb0).2 hdist
  have hfid : 1 - b ^ (2 : ℕ) ≤ finitePureStateFidelity
      (staticSpectralChoiVector d (T * x) energy).ofLp
      (staticSpectralChoiVector d (T * y) energy).ofLp := by
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    rw [norm_inner_symm]
    linarith only [hsq, hdistSq]
  have hbSq : b ^ (2 : ℕ) = 1 / (16 * ((r : ℝ) + 1)) := by
    dsimp [b]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hrb : (r : ℝ) * b ^ (2 : ℕ) ≤ 1 / 16 := by
    rw [hbSq, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 16 * ((r : ℝ) + 1))).2
    linarith only
  have hfid0 : 0 ≤ finitePureStateFidelity
      (staticSpectralChoiVector d (T * x) energy).ofLp
      (staticSpectralChoiVector d (T * y) energy).ofLp := sq_nonneg _
  have hber := one_add_mul_sub_le_pow (by linarith only [hfid0] :
      -1 ≤ finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp
        (staticSpectralChoiVector d (T * y) energy).ofLp) r
  have hmul := mul_le_mul_of_nonneg_left hfid (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  linarith only [hber, hmul, hrb]

private theorem returnExcisedStaticChoiPairPurity_lower_aux
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (r : ℕ)
    {a T : ℝ} (hT : 1 ≤ T) (ha : |a| / T ≤ 1 / 4) :
    gaussianFloorTwo ^ (2 : ℕ) /
      (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T) ≤
      returnExcisedStaticChoiPairPurity d energy r a T := by
  let R : ℝ := Real.sqrt ((r : ℝ) + 1)
  let S : ℝ := staticChoiSpeed energy
  let δ : ℝ := 1 / (4 * R * S * T)
  let ν := (gaussianReal 0 1).restrict (Icc (-|a| / T) (|a| / T))ᶜ
  let f : ℝ × ℝ → ℝ := fun p => finitePureStateFidelity
    (staticSpectralChoiVector d (T * p.1) energy).ofLp
    (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
  have hR : 1 ≤ R := by
    dsimp [R]
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (r : ℝ) + 1 from
        le_add_of_nonneg_left (Nat.cast_nonneg r))
  have hS : 1 ≤ S := staticChoiSpeed_one_le energy
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδ : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    calc
      (4 : ℝ) ≤ 4 * R := le_mul_of_one_le_right (by norm_num) hR
      _ ≤ (4 * R) * S := le_mul_of_one_le_right (by positivity) hS
      _ ≤ (4 * R * S) * T := le_mul_of_one_le_right (by positivity) hT
  have hf0 : ∀ p, 0 ≤ f p := fun p => pow_nonneg (sq_nonneg _) r
  have hf : Integrable f (ν.prod ν) :=
    (integrable_gaussianPair_staticChoi_fidelity_pow hd energy T r).mono_measure
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hsliceInt : ∀ y, Integrable (fun x => f (x, y)) ν := fun y =>
    integrable_staticChoi_fidelity_pow hd energy T
      (staticSpectralChoiVector d (T * y) energy)
      (staticSpectralChoiVector_norm hd _ energy) r _
  have hinner : ∀ y ∈ Icc (3 / 4 : ℝ) 1,
      gaussianFloorTwo * δ ≤ ∫ x, f (x, y) ∂ν := by
    intro y hy
    have hyabs : |y| ≤ 1 := abs_le.mpr ⟨by linarith only [hy.1], hy.2⟩
    have hJsub : Icc (y - δ) (y + δ) ⊆ (Icc (-|a| / T) (|a| / T))ᶜ := by
      intro x hx hbad
      linarith only [hx.1, hy.1, hbad.2, hδ, ha]
    have hmeasure := Measure.restrict_mono hJsub
      (le_rfl : gaussianReal 0 1 ≤ gaussianReal 0 1)
    have hJint : Integrable (fun x => f (x, y))
        ((gaussianReal 0 1).restrict (Icc (y - δ) (y + δ))) :=
      (hsliceInt y).mono_measure hmeasure
    calc
      gaussianFloorTwo * δ ≤
          (gaussianReal 0 1).real (Icc (y - δ) (y + δ)) * (1 / 2) := by
        have hl := real_gaussian_shifted_interval_lower hyabs hδpos.le (by linarith only [hδ])
        linarith only [hl]
      _ = ∫ _x in Icc (y - δ) (y + δ), (1 / 2 : ℝ) ∂gaussianReal 0 1 := by
        rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      _ ≤ ∫ x in Icc (y - δ) (y + δ), f (x, y) ∂gaussianReal 0 1 := by
        apply setIntegral_mono_on (integrable_const _) hJint measurableSet_Icc
        intro x hx
        apply staticChoi_replica_coherence_lower hd energy r hT
        change |x - y| ≤ δ
        rw [abs_le]
        constructor <;> linarith only [hx.1, hx.2]
      _ ≤ ∫ x, f (x, y) ∂ν :=
        integral_mono_measure hmeasure
          (Filter.Eventually.of_forall fun x => hf0 (x, y)) (hsliceInt y)
  have hIsub : Icc (3 / 4 : ℝ) 1 ⊆ (Icc (-|a| / T) (|a| / T))ᶜ := by
    intro y hy hbad
    linarith only [hy.1, hbad.2, ha]
  have hmeasure := Measure.restrict_mono hIsub
    (le_rfl : gaussianReal 0 1 ≤ gaussianReal 0 1)
  have hgInt := hf.integral_prod_right
  have hIint := hgInt.mono_measure hmeasure
  have hImass : gaussianFloorTwo / 4 ≤
      (gaussianReal 0 1).real (Icc (3 / 4 : ℝ) 1) := by
    have hl := real_gaussian_shifted_interval_lower
      (x := (7 / 8 : ℝ)) (δ := (1 / 8 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    norm_num at hl
    linarith only [hl]
  unfold returnExcisedStaticChoiPairPurity
  change _ ≤ ∫ p, f p ∂ν.prod ν
  rw [integral_prod_symm f hf]
  calc
    gaussianFloorTwo ^ (2 : ℕ) /
        (16 * R * S * T) = (gaussianFloorTwo / 4) * (gaussianFloorTwo * δ) := by
      dsimp [δ]
      field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hR),
        ne_of_gt (lt_of_lt_of_le zero_lt_one hS), hTpos.ne']
      ring
    _ ≤ (gaussianReal 0 1).real (Icc (3 / 4 : ℝ) 1) * (gaussianFloorTwo * δ) :=
      mul_le_mul_of_nonneg_right hImass (mul_nonneg gaussianFloorTwo_pos.le hδpos.le)
    _ = ∫ _y in Icc (3 / 4 : ℝ) 1, gaussianFloorTwo * δ ∂gaussianReal 0 1 := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    _ ≤ ∫ y in Icc (3 / 4 : ℝ) 1, ∫ x, f (x, y) ∂ν ∂gaussianReal 0 1 :=
      setIntegral_mono_on (integrable_const _) hIint measurableSet_Icc hinner
    _ ≤ ∫ y, ∫ x, f (x, y) ∂ν ∂ν :=
      integral_mono_measure hmeasure
        (Filter.Eventually.of_forall fun y => integral_nonneg fun x => hf0 (x, y)) hgInt

/-- A cutoff may be any circuit-budget-dependent number. Once the window is at least
four times that cutoff, nearby surviving times force a replica-purity floor.
Dimension, spectrum, cutoff, time offset and replica order are unrestricted data. -/
theorem returnExcisedStaticChoiPairPurity_coherence_floor
    (n : ℕ) (energy : Fin (n + 1) → ℝ) (r : ℕ) (a u : ℝ) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    gaussianFloorTwo ^ (2 : ℕ) /
        (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T) ≤
      returnExcisedStaticChoiPairPurity (n + 1) energy r a T := by
  dsimp only
  have hT : 1 ≤ 1 + 4 * |a| + u ^ (2 : ℕ) := by
    linarith only [abs_nonneg a, sq_nonneg u]
  apply returnExcisedStaticChoiPairPurity_lower_aux (Nat.succ_pos n) energy r hT
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hT)).2
  linarith only [sq_nonneg u]

private theorem fixed_error_receiver_lt_coherence_floor_aux
    {d : ℕ} (energy : Fin d → ℝ) (r : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (gaussianFloorTwo / (8 * staticChoiSpeed energy * T) * (7 / 16 : ℝ) ^ r) ^
        (2 : ℕ) <
      gaussianFloorTwo ^ (2 : ℕ) /
        (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T) := by
  let R := Real.sqrt ((r : ℝ) + 1)
  let S := staticChoiSpeed energy
  have hlinear : (1 : ℝ) ≤ (r : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg r)
  have hR : 1 ≤ R := Real.one_le_sqrt.mpr hlinear
  have hS : 1 ≤ S := staticChoiSpeed_one_le energy
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRle : R ≤ (2 : ℝ) ^ r := by
    have hnat : (r : ℝ) + 1 ≤ (2 : ℝ) ^ r := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r))
    exact (Real.sqrt_le_self_iff.mpr (Or.inr hlinear)).trans hnat
  have hpow : R * (7 / 16 : ℝ) ^ (2 * r) ≤ 1 := by
    calc
      R * (7 / 16 : ℝ) ^ (2 * r) ≤
          (2 : ℝ) ^ r * (7 / 16 : ℝ) ^ (2 * r) :=
        mul_le_mul_of_nonneg_right hRle (pow_nonneg (by norm_num) _)
      _ = ((2 : ℝ) * (7 / 16 : ℝ) ^ (2 : ℕ)) ^ r := by
        rw [pow_mul, mul_pow]
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hST : 1 ≤ S * T :=
    one_le_mul_of_one_le_of_one_le hS hT
  have hratio : R * (7 / 16 : ℝ) ^ (2 * r) / (S * T) ≤ 1 :=
    (div_le_one (mul_pos hSpos hTpos)).2 (hpow.trans hST)
  calc
    (gaussianFloorTwo / (8 * S * T) * (7 / 16 : ℝ) ^ r) ^ (2 : ℕ) =
        (gaussianFloorTwo ^ (2 : ℕ) / (64 * R * S * T)) *
          (R * (7 / 16 : ℝ) ^ (2 * r) / (S * T)) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
      field_simp [hRpos.ne', hSpos.ne', hTpos.ne']
      ring
    _ ≤ gaussianFloorTwo ^ (2 : ℕ) / (64 * R * S * T) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ < gaussianFloorTwo ^ (2 : ℕ) / (16 * R * S * T) := by
      apply div_lt_div_of_pos_left (sq_pos_of_pos gaussianFloorTwo_pos) (by positivity)
      have hRST : 0 < R * S * T := mul_pos (mul_pos hRpos hSpos) hTpos
      linarith only [hRST]

/-- At fixed errors 1/2 and 3/4, full replica purity cannot satisfy the first-entry
receiver. The result holds at every replica order, not only fixed order as T grows.
It does not constrain the smaller, target-projected incidence action. -/
theorem returnExcisedStaticChoiPairPurity_exceeds_fixedError_receiver
    (n : ℕ) (energy : Fin (n + 1) → ℝ) (r : ℕ) (a u : ℝ) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    (gaussianFloorTwo *
        (((3 / 4 : ℝ) - 1 / 2) / staticChoiSpeed energy / (2 * T)) *
        (1 - (3 / 4 : ℝ) ^ (2 : ℕ)) ^ r) ^ (2 : ℕ) <
      returnExcisedStaticChoiPairPurity (n + 1) energy r a T := by
  dsimp only
  have hT : 1 ≤ 1 + 4 * |a| + u ^ (2 : ℕ) := by
    linarith only [abs_nonneg a, sq_nonneg u]
  have haux := fixed_error_receiver_lt_coherence_floor_aux energy r hT
  have heq :
      gaussianFloorTwo *
          (((3 / 4 : ℝ) - 1 / 2) / staticChoiSpeed energy /
            (2 * (1 + 4 * |a| + u ^ (2 : ℕ)))) *
          (1 - (3 / 4 : ℝ) ^ (2 : ℕ)) ^ r =
        gaussianFloorTwo / (8 * staticChoiSpeed energy *
          (1 + 4 * |a| + u ^ (2 : ℕ))) * (7 / 16 : ℝ) ^ r := by
    norm_num only
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  exact haux.trans_le (returnExcisedStaticChoiPairPurity_coherence_floor n energy r a u)

/-- Quantitative positive boundary of the purity obstruction: actual compression
ratio lies in [0,1] and is bounded by the absolute projected action divided by the
proved coherence floor. No estimate of that absolute action is assumed or claimed. -/
theorem returnExcisedStaticChoiCarrierAction_relative_compression
    (n : ℕ) (energy : Fin (n + 1) → ℝ) (r : ℕ) (a u : ℝ)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin r → (Fin (n + 1) × Fin (n + 1))))) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    let A := returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r V
      (fun x => (staticSpectralChoiVector (n + 1) (T * x) energy).ofLp)
      (Icc (-|a| / T) (|a| / T))
    let P := returnExcisedStaticChoiPairPurity (n + 1) energy r a T
    0 ≤ A / P ∧ A / P ≤ min 1
      (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T * A /
        gaussianFloorTwo ^ (2 : ℕ)) := by
  dsimp only
  let T := 1 + 4 * |a| + u ^ (2 : ℕ)
  let A := returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r V
    (fun x => (staticSpectralChoiVector (n + 1) (T * x) energy).ofLp)
    (Icc (-|a| / T) (|a| / T))
  let P := returnExcisedStaticChoiPairPurity (n + 1) energy r a T
  let L := gaussianFloorTwo ^ (2 : ℕ) /
    (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T)
  have hT : 0 < T := by dsimp [T]; positivity
  have hL : 0 < L := by dsimp [L]; positivity [staticChoiSpeed_pos energy, gaussianFloorTwo_pos]
  have hfloor : L ≤ P := returnExcisedStaticChoiPairPurity_coherence_floor n energy r a u
  have hP : 0 < P := hL.trans_le hfloor
  have hA : 0 ≤ A := returnExcisedReplicaCarrierIncidenceAction_nonneg _ _ _ _ _
  have hcompression : A ≤ P :=
    returnExcisedReplicaCarrierIncidenceAction_le_fullReplicaPurity
      (gaussianReal 0 1) r V
      (fun x => (staticSpectralChoiVector (n + 1) (T * x) energy).ofLp)
      (Icc (-|a| / T) (|a| / T))
      (fun v => (Continuous.inner continuous_const
        (continuous_finitePureTensorPowerEuclidean_comp (r := r)
          (fun x : ℝ => staticSpectralChoiVector (n + 1) (T * x) energy)
          (continuous_staticSpectralChoiVector_scaled (Nat.succ_pos n) energy T))).aestronglyMeasurable)
      (fun v => integrable_sq_inner_staticChoiReplica (Nat.succ_pos n) energy T v _)
  change 0 ≤ A / P ∧ A / P ≤ min 1
    (16 * Real.sqrt ((r : ℝ) + 1) * staticChoiSpeed energy * T * A /
      gaussianFloorTwo ^ (2 : ℕ))
  refine ⟨div_nonneg hA hP.le, le_min ((div_le_one hP).2 hcompression) ?_⟩
  calc
    A / P ≤ A / L := div_le_div_of_nonneg_left hA hL hfloor
    _ = _ := by
      dsimp [L]
      rw [div_div_eq_mul_div, mul_comm A]

/-- **Necessary compression at the complete-union receiver scale.** For any positive
capacity k+1, either the exact incidence budget fails, or relative target compression
must beat the displayed growing-replica scale. This is an unconditional diagnostic
disjunction, not a claim that the ordinary ensemble supplies its second branch. -/
theorem returnExcisedStaticChoiCarrierAction_receiver_or_required_compression
    (n : ℕ) (energy : Fin (n + 1) → ℝ) (r k : ℕ) (a u : ℝ)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin r → (Fin (n + 1) × Fin (n + 1))))) :
    let T := 1 + 4 * |a| + u ^ (2 : ℕ)
    let A := returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r V
      (fun x => (staticSpectralChoiVector (n + 1) (T * x) energy).ofLp)
      (Icc (-|a| / T) (|a| / T))
    let P := returnExcisedStaticChoiPairPurity (n + 1) energy r a T
    (gaussianFloorTwo / (8 * staticChoiSpeed energy * T) * (7 / 16 : ℝ) ^ r) ^
        (2 : ℕ) ≤ ((k : ℝ) + 1) * A ∨
      A / P < Real.sqrt ((r : ℝ) + 1) * (7 / 16 : ℝ) ^ (2 * r) /
        (4 * ((k : ℝ) + 1) * staticChoiSpeed energy * T) := by
  dsimp only
  let T := 1 + 4 * |a| + u ^ (2 : ℕ)
  let S := staticChoiSpeed energy
  let R := Real.sqrt ((r : ℝ) + 1)
  let N : ℝ := (k : ℝ) + 1
  let A := returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r V
    (fun x => (staticSpectralChoiVector (n + 1) (T * x) energy).ofLp)
    (Icc (-|a| / T) (|a| / T))
  let P := returnExcisedStaticChoiPairPurity (n + 1) energy r a T
  let F := (gaussianFloorTwo / (8 * S * T) * (7 / 16 : ℝ) ^ r) ^ (2 : ℕ)
  let K := 16 * R * S * T / gaussianFloorTwo ^ (2 : ℕ)
  have hS : 0 < S := staticChoiSpeed_pos energy
  have hT : 0 < T := by dsimp [T]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : 0 < K := by dsimp [K, R]; positivity [gaussianFloorTwo_pos]
  change F ≤ N * A ∨ A / P < R * (7 / 16 : ℝ) ^ (2 * r) / (4 * N * S * T)
  by_cases hbudget : F ≤ N * A
  · exact Or.inl hbudget
  apply Or.inr
  have hsmall : A < F / N := by
    apply (lt_div_iff₀ hN).2
    rw [mul_comm A N]
    exact lt_of_not_ge hbudget
  have hrelative :=
    (returnExcisedStaticChoiCarrierAction_relative_compression n energy r a u V).2
  change A / P ≤ min 1 (16 * R * S * T * A / gaussianFloorTwo ^ (2 : ℕ)) at hrelative
  have hbound : A / P ≤ K * A := by
    apply hrelative.trans
    apply (min_le_right _ _).trans_eq
    dsimp [K]
    ring
  calc
    A / P ≤ K * A := hbound
    _ < K * (F / N) := mul_lt_mul_of_pos_left hsmall hK
    _ = _ := by
      dsimp [K, F]
      rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
      field_simp [gaussianFloorTwo_pos.ne', hS.ne', hT.ne', hN.ne']
      ring

end RHTower
