import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman
import GaloisForLFunctions.HTGeometry.ObserverInvisibleTubeShortcut

/-!
# Instant exact complexity forces a calibration singularity

A Lipschitz certificate normalized at the reference state and reaching a prescribed value at a
state has Lipschitz constant at least that value divided by the distance to the reference state.
The same bound holds for the exact-penalty value, because the empty gate word already costs only
the penalty times that distance.

When the state approaches the reference state linearly in time while the certified value stays
bounded below, the condition number therefore diverges at least inversely with time: no finite
Lipschitz constant certifies the value uniformly on a punctured neighbourhood of time zero.  For a
Schrödinger orbit the linear approach is the Duhamel bound with speed the operator norm of the
generator.
-/

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section ConditionNumber

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- **Certificate condition number, quotient form.**  A Lipschitz certificate normalized at the
reference state and reaching the value `c` has Lipschitz constant at least `c` divided by the
distance to the reference state. -/
theorem div_dist_le_lipschitzConstant_of_certificate {chi x : X} {phi : X → ℝ} {lam c : ℝ}
    (hlip : ∀ u v : X, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi chi ≤ 0) (hval : c ≤ phi x) (hd : 0 < dist x chi) :
    c / dist x chi ≤ lam := by
  have h := _root_.HTGeometry.le_lipschitzConstant_of_certificate hlip hnorm hval
  rw [div_le_iff₀ hd]
  linarith

/-- **Calibration singularity.**  A linear-in-time approach to the reference state turns the
condition number into an inverse time divergence. -/
theorem div_le_lipschitzConstant_of_linear_approach {chi x : X} {phi : X → ℝ} {lam c v t : ℝ}
    (hlip : ∀ u v : X, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi chi ≤ 0) (hval : c ≤ phi x) (hspeed : dist x chi ≤ v * |t|)
    (hlam : 0 ≤ lam) (hvt : 0 < v * |t|) :
    c / (v * |t|) ≤ lam := by
  have h := _root_.HTGeometry.le_mul_lipschitzConstant_of_certificate_of_linear_approach
    hlip hnorm hval hspeed hlam
  rw [div_le_iff₀ hvt]
  linarith

/-- **Exact-penalty condition number.**  The empty gate word bounds the exact-penalty value by the
penalty times the distance to the reference state. -/
theorem penaltyValue_le_mul_dist {act : Γ → X → X} {chi : X} {lam : ℝ} (hlam : 0 ≤ lam) (x : X) :
    _root_.HTGeometry.penaltyValue act chi lam 0 x ≤ lam * dist x chi := by
  have h := _root_.HTGeometry.penaltyValue_le_wordCost (act := act) (chi := chi) (lam := lam)
    (eps := 0) hlam x ([] : List Γ)
  have hw : _root_.HTGeometry.wordCost act chi lam 0 x ([] : List Γ) = lam * dist x chi := by
    rw [_root_.HTGeometry.wordCost]
    simp [_root_.HTGeometry.wordAct]
  rw [hw] at h
  exact h

/-- **Exact-penalty calibration singularity.**  If the exact-penalty value at `x` reaches `c`, the
penalty is at least `c` divided by the distance to the reference state. -/
theorem div_dist_le_penalty_of_penaltyValue {act : Γ → X → X} {chi : X} {lam c : ℝ}
    (hlam : 0 ≤ lam) (x : X) (hval : c ≤ _root_.HTGeometry.penaltyValue act chi lam 0 x)
    (hd : 0 < dist x chi) :
    c / dist x chi ≤ lam := by
  have h := le_trans hval (penaltyValue_le_mul_dist (act := act) (chi := chi) hlam x)
  rw [div_le_iff₀ hd]
  linarith

/-- A Bellman subsolution without slack is dominated by the penalty times the distance to the
reference state. -/
theorem bellmanSubsolution_le_mul_dist {act : Γ → X → X} {inv : Γ → Γ} {chi : X} {lam : ℝ}
    {phi : X → ℝ} (h : _root_.HTGeometry.IsBellmanSubsolution act inv chi lam 0 phi) (x : X) :
    phi x ≤ lam * dist x chi := by
  have hx := h.1 x
  rwa [sub_zero, max_eq_left (dist_nonneg (x := x) (y := chi))] at hx

/-- **No uniform certificate near time zero.**  If the certified value stays bounded below while
the state approaches the reference state linearly in time, then arbitrarily close to time zero the
certificate Lipschitz constant exceeds every prescribed bound. -/
theorem exists_time_lipschitzConstant_gt {c v δ : ℝ} (hc : 0 < c) (hv : 0 < v) (hδ : 0 < δ)
    {chi : X} {x : ℝ → X} {phi : ℝ → X → ℝ} {lam : ℝ → ℝ}
    (hlip : ∀ s : ℝ, ∀ u w : X, phi s u - phi s w ≤ lam s * dist u w)
    (hnorm : ∀ s : ℝ, phi s chi ≤ 0) (hval : ∀ s : ℝ, c ≤ phi s (x s))
    (hspeed : ∀ s : ℝ, dist (x s) chi ≤ v * |s|) (hlam : ∀ s : ℝ, 0 ≤ lam s) (Λ : ℝ) :
    ∃ s : ℝ, 0 < |s| ∧ |s| < δ ∧ Λ < lam s := by
  set B : ℝ := |Λ| + 1 with hB
  have hBpos : 0 < B := by positivity
  set s : ℝ := min δ (c / (v * B)) / 2 with hs
  have hcvB : 0 < c / (v * B) := by positivity
  have hspos : 0 < s := by
    rw [hs]
    have : 0 < min δ (c / (v * B)) := lt_min hδ hcvB
    linarith
  have habs : |s| = s := abs_of_pos hspos
  have hsδ : s < δ := by
    rw [hs]
    have hmin : min δ (c / (v * B)) ≤ δ := min_le_left _ _
    linarith
  have hsB : s < c / (v * B) := by
    rw [hs]
    have hmin : min δ (c / (v * B)) ≤ c / (v * B) := min_le_right _ _
    linarith
  refine ⟨s, by rw [habs]; exact hspos, by rw [habs]; exact hsδ, ?_⟩
  have hvs : 0 < v * |s| := by
    rw [habs]
    positivity
  have hbound := div_le_lipschitzConstant_of_linear_approach (hlip s) (hnorm s) (hval s)
    (hspeed s) (hlam s) hvs
  have hkey : Λ < c / (v * |s|) := by
    rw [habs]
    rw [lt_div_iff₀ (by positivity)]
    have hs' : v * s < c / B := by
      rw [lt_div_iff₀ hBpos]
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < v * B)).mp hsB
      linarith [this]
    have hΛB : Λ * B ≤ |Λ| * B := by
      exact mul_le_mul_of_nonneg_right (le_abs_self Λ) hBpos.le
    have hstep : Λ * (v * s) ≤ |Λ| * (v * s) :=
      mul_le_mul_of_nonneg_right (le_abs_self Λ) (by positivity)
    have hfinal : |Λ| * (v * s) < c := by
      have h1 : v * s < c / B := hs'
      have h2 : |Λ| * (v * s) ≤ |Λ| * (c / B) :=
        mul_le_mul_of_nonneg_left h1.le (abs_nonneg Λ)
      have h3 : |Λ| * (c / B) < c := by
        rw [hB]
        rw [mul_div_assoc']
        rw [div_lt_iff₀ hBpos]
        nlinarith [hc, abs_nonneg Λ]
      linarith
    linarith
  exact lt_of_lt_of_le hkey hbound

end ConditionNumber

section Schroedinger

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Schrödinger orbit of a state. -/
def evolvedState (H : Matrix d d ℂ) (t : ℝ) (ψ : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H t *ᵥ ψ.ofLp)

theorem unitaryEvolution_zero (t : ℝ) : unitaryEvolution (0 : Matrix d d ℂ) t = 1 := by
  rw [unitaryEvolution, smul_zero, smul_zero, NormedSpace.exp_zero]

theorem evolvedState_zero_generator (t : ℝ) (ψ : EuclideanSpace ℂ d) :
    evolvedState (0 : Matrix d d ℂ) t ψ = ψ := by
  rw [evolvedState, unitaryEvolution_zero, Matrix.one_mulVec]
  rfl

/-- **Duhamel displacement.**  A Schrödinger orbit leaves its initial state at speed at most the
operator norm of the generator. -/
theorem norm_evolvedState_sub_le {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (t : ℝ)
    (ψ : EuclideanSpace ℂ d) :
    ‖evolvedState H t ψ - ψ‖ ≤ |t| * ‖H‖ * ‖ψ‖ := by
  have h := QuantumAlg.norm_unitaryEvolution_mulVec_sub_le hH
    (IsSelfAdjoint.zero (Matrix d d ℂ)) t ψ
  rw [sub_zero] at h
  have hzero : (EuclideanSpace.equiv d ℂ).symm
      (unitaryEvolution (0 : Matrix d d ℂ) t *ᵥ ψ.ofLp) = ψ :=
    evolvedState_zero_generator t ψ
  rw [hzero] at h
  exact h

theorem dist_evolvedState_le {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (t : ℝ)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) :
    dist (evolvedState H t ψ) ψ ≤ ‖H‖ * |t| := by
  rw [dist_eq_norm]
  have h := norm_evolvedState_sub_le hH t ψ
  rw [hψ, mul_one] at h
  rwa [mul_comm] at h

/-- **Calibration singularity of an instant exact jump.**  Every Lipschitz certificate of a
complexity value `c` along a Schrödinger orbit of a unit seed has Lipschitz constant at least `c`
divided by the elapsed time times the generator norm. -/
theorem div_le_lipschitzConstant_of_evolvedState {H : Matrix d d ℂ} (hH : IsSelfAdjoint H)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {t : ℝ}
    {phi : EuclideanSpace ℂ d → ℝ} {lam c : ℝ}
    (hlip : ∀ u v : EuclideanSpace ℂ d, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi ψ ≤ 0) (hval : c ≤ phi (evolvedState H t ψ)) (hlam : 0 ≤ lam)
    (hpos : 0 < ‖H‖ * |t|) :
    c / (‖H‖ * |t|) ≤ lam :=
  div_le_lipschitzConstant_of_linear_approach hlip hnorm hval
    (dist_evolvedState_le hH t hψ) hlam hpos


/-- **Instant exact jump.**  Every Lipschitz certificate of the exponential exact-complexity value
`(2^n - 1)/16` along a Schrödinger orbit of a unit seed has Lipschitz constant at least
`(2^n - 1)/(16 |t| ‖H‖)`. -/
theorem instant_jump_condition_number {n : ℕ} {H : Matrix d d ℂ} (hH : IsSelfAdjoint H)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {t : ℝ}
    {phi : EuclideanSpace ℂ d → ℝ} {lam : ℝ}
    (hlip : ∀ u v : EuclideanSpace ℂ d, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi ψ ≤ 0)
    (hval : ((2 ^ n - 1 : ℝ) / 16) ≤ phi (evolvedState H t ψ)) (hlam : 0 ≤ lam)
    (hpos : 0 < ‖H‖ * |t|) :
    (2 ^ n - 1 : ℝ) / (16 * (‖H‖ * |t|)) ≤ lam := by
  have h := div_le_lipschitzConstant_of_evolvedState hH hψ hlip hnorm hval hlam hpos
  rw [div_div] at h
  exact h

/-- **No uniform certificate of an instant jump.**  Along a Schrödinger orbit of a unit seed with
nonzero generator, if the certified value stays at least `c > 0` then arbitrarily close to time
zero the certificate Lipschitz constant exceeds every prescribed bound. -/
theorem exists_time_lipschitzConstant_gt_evolvedState {H : Matrix d d ℂ} (hH : IsSelfAdjoint H)
    (hHpos : 0 < ‖H‖) {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    {phi : ℝ → EuclideanSpace ℂ d → ℝ} {lam : ℝ → ℝ}
    (hlip : ∀ s : ℝ, ∀ u v : EuclideanSpace ℂ d, phi s u - phi s v ≤ lam s * dist u v)
    (hnorm : ∀ s : ℝ, phi s ψ ≤ 0)
    (hval : ∀ s : ℝ, c ≤ phi s (evolvedState H s ψ)) (hlam : ∀ s : ℝ, 0 ≤ lam s) (Λ : ℝ) :
    ∃ s : ℝ, 0 < |s| ∧ |s| < δ ∧ Λ < lam s :=
  exists_time_lipschitzConstant_gt hc hHpos hδ hlip hnorm hval
    (fun s => dist_evolvedState_le hH s hψ) hlam Λ

end Schroedinger

end

end GaloisForLFunctions.HTGeometry
