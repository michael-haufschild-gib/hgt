import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform

/-!
# Width--capacity obstruction for replicated common-Hardy reporters

Cofinal replication can recover an omitted diagonal Fisher collision algebraically: split one
atom into `k` equal-mass orthogonal copies and the off-diagonal replica sum tends to twice the
original collision.  A hard-cut/soft-damping reporter sees a different geometry.  Copies at the
same height span intervals of length zero, while copies separated inside a fibre of diameter
`Delta` have total Laplace capacity at most `2 p^(2 : ℕ) |a d| Delta`, independently of replica count.

Consequently a vanishing-width replica fibre cannot turn algebraic collision evacuation into one
bounded common-Hardy source.  Retaining a nonzero collision requires a genuinely nonlocal height
spread or reporter capacity growing at least inversely with fibre width.  This is the exact
obstruction separating the scalar cofinal-replica identity from a presentation-independent
Gamma/co-Poisson reporter mate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Algebraic ordered off-diagonal contribution of one atom replicated `k` times. -/
def fisherReplicaOffDiagonalCollision (k : ℕ) (p a d : ℝ) : ℝ :=
  ∑ r : Fin k, ∑ s : Fin k,
    if s = r then 0 else (p / k) ^ (2 : ℕ) * (a + a) * d

private theorem fisherReplica_inner_sum (k : ℕ) (r : Fin k) (C : ℝ) :
    (∑ s : Fin k, if s = r then 0 else C) = (k - 1 : ℕ) * C := by
  rw [show (fun s : Fin k => if s = r then 0 else C) =
      fun s => C - if s = r then C else 0 by
    funext s
    split_ifs <;> simp_all]
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.sum_ite_eq' Finset.univ r]
  simp
  have hk : 0 < k := Fin.pos_iff_nonempty.mpr ⟨r⟩
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := Nat.cast_pred hk
  rw [hcast]
  ring

/-- Replication preserves a proportion `1 - 1/k` of the doubled collision. -/
theorem fisherReplicaOffDiagonalCollision_eq
    {k : ℕ} (hk : 0 < k) (p a d : ℝ) :
    fisherReplicaOffDiagonalCollision k p a d =
      2 * p ^ (2 : ℕ) * a * d * (1 - 1 / k) := by
  rw [fisherReplicaOffDiagonalCollision]
  simp_rw [fisherReplica_inner_sum k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := Nat.cast_pred hk
  rw [hcast]
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne']
  ring

/-- Total interval-width capacity of the ordered replicated collision channel. -/
def fisherReplicaIntervalCollisionCapacity
    (k : ℕ) (p a d : ℝ) (height : Fin k → ℝ) : ℝ :=
  ∑ r : Fin k, ∑ s : Fin k,
    if s = r then 0
    else (p / k) ^ (2 : ℕ) * (2 * |a * d|) * |height r - height s|

/-- Uniform width--capacity law: increasing replica count does not compensate for shrinking
within-fibre height diameter. -/
theorem fisherReplicaIntervalCollisionCapacity_le
    {k : ℕ} (hk : 0 < k) {p a d Delta : ℝ} {height : Fin k → ℝ}
    (hDelta : 0 ≤ Delta)
    (hdiam : ∀ r s, |height r - height s| ≤ Delta) :
    fisherReplicaIntervalCollisionCapacity k p a d height ≤
      2 * p ^ (2 : ℕ) * |a * d| * Delta := by
  have hcoeff : 0 ≤ (p / (k : ℝ)) ^ (2 : ℕ) * (2 * |a * d|) := by
    positivity
  calc
    fisherReplicaIntervalCollisionCapacity k p a d height ≤
        Delta * fisherReplicaOffDiagonalCollision k p |a * d| 1 := by
      rw [fisherReplicaIntervalCollisionCapacity,
        fisherReplicaOffDiagonalCollision]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      by_cases hsr : s = r
      · simp [hsr]
      · simp only [hsr, if_false, mul_one]
        have h := mul_le_mul_of_nonneg_left (hdiam r s) hcoeff
        nlinarith
    _ = Delta * (2 * p ^ (2 : ℕ) * |a * d| * (1 - 1 / k)) := by
      rw [fisherReplicaOffDiagonalCollision_eq hk]
      ring
    _ ≤ 2 * p ^ (2 : ℕ) * |a * d| * Delta := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hinv : 0 ≤ (1 : ℝ) / k := by positivity
      have hfactor : 1 - (1 : ℝ) / k ≤ 1 := by linarith
      have hbase : 0 ≤ Delta * (2 * p ^ (2 : ℕ) * |a * d|) := by positivity
      nlinarith

theorem fisherReplicaIntervalCollisionCapacity_nonneg
    (k : ℕ) (p a d : ℝ) (height : Fin k → ℝ) :
    0 ≤ fisherReplicaIntervalCollisionCapacity k p a d height := by
  rw [fisherReplicaIntervalCollisionCapacity]
  positivity

/-- Vanishing fibre width forces total interval capacity to zero, at every replica depth. -/
theorem tendsto_fisherReplicaIntervalCollisionCapacity_zero
    (p a d : ℝ) (Delta : ℕ → ℝ)
    (height : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hDelta : Tendsto Delta atTop (𝓝 0))
    (hDeltaNonneg : ∀ n, 0 ≤ Delta n)
    (hdiam : ∀ n r s, |height n r - height n s| ≤ Delta n) :
    Tendsto
      (fun n => fisherReplicaIntervalCollisionCapacity
        (n + 1) p a d (height n))
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact fisherReplicaIntervalCollisionCapacity_nonneg
      (n + 1) p a d (height n)
  · intro n
    exact fisherReplicaIntervalCollisionCapacity_le (Nat.succ_pos n)
      (hDeltaNonneg n) (hdiam n)
  · have h := hDelta.const_mul (2 * p ^ (2 : ℕ) * |a * d|)
    simpa only [mul_zero] using h

/-- Abstract no-recovery form: any scalar reporter bounded by vanishing interval capacity cannot
converge to the nonzero algebraic collision retained by cofinal replication. -/
theorem no_vanishingWidthReporter_recovers_fisherReplicaCollision
    (p a d : ℝ) (hcollision : 2 * p ^ (2 : ℕ) * a * d ≠ 0)
    (Delta : ℕ → ℝ) (height : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (output : ℕ → ℝ)
    (hDelta : Tendsto Delta atTop (𝓝 0))
    (hDeltaNonneg : ∀ n, 0 ≤ Delta n)
    (hdiam : ∀ n r s, |height n r - height n s| ≤ Delta n)
    (houtput : ∀ n, |output n| ≤
      fisherReplicaIntervalCollisionCapacity (n + 1) p a d (height n)) :
    ¬ Tendsto output atTop (𝓝 (2 * p ^ (2 : ℕ) * a * d)) := by
  have hcapacity := tendsto_fisherReplicaIntervalCollisionCapacity_zero
    p a d Delta height hDelta hDeltaNonneg hdiam
  have habs : Tendsto (fun n => |output n|) atTop (𝓝 0) := by
    apply squeeze_zero
    · exact fun n => abs_nonneg (output n)
    · exact houtput
    · exact hcapacity
  have hzero : Tendsto output atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  intro htarget
  have heq : (0 : ℝ) = 2 * p ^ (2 : ℕ) * a * d :=
    tendsto_nhds_unique hzero htarget
  exact hcollision heq.symm

/-- Laplace damping retained by a positive scalar replication.  `weight` is the split of one
source mass and `shift` is the inward Hardy height assigned to each copy. -/
def fisherReplicaDampingFactor
    (k : ℕ) (weight shift : Fin k → ℝ) (x : ℝ) : ℝ :=
  ∑ r : Fin k, weight r * Real.exp (-x * shift r)

/-- Positive scalar replication is rigid: if its weights sum to one, its Hardy shifts are
nonnegative, and it preserves one strictly positive exponential damping moment exactly, then
every positive-mass replica has zero shift.

This is the equality case of the elementary positive-contraction inequality, stated in the form
needed for common-Hardy source admission.  It excludes persistent positive fibre spread before
any cofinal limit is taken. -/
theorem fisherReplicaDamping_eq_one_forces_zero_shift
    {k : ℕ} {weight shift : Fin k → ℝ} {x : ℝ}
    (hweight : ∀ r, 0 ≤ weight r)
    (hsum : ∑ r, weight r = 1)
    (hshift : ∀ r, 0 ≤ shift r)
    (hx : 0 < x)
    (hdamp : fisherReplicaDampingFactor k weight shift x = 1) :
    ∀ r, weight r ≠ 0 → shift r = 0 := by
  have hterm : ∀ r : Fin k,
      0 ≤ weight r * (1 - Real.exp (-x * shift r)) := by
    intro r
    apply mul_nonneg (hweight r)
    rw [sub_nonneg, Real.exp_le_one_iff]
    have hm := mul_nonneg hx.le (hshift r)
    nlinarith
  have hdeficit :
      ∑ r : Fin k, weight r * (1 - Real.exp (-x * shift r)) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hsum]
    exact sub_eq_zero.mpr hdamp.symm
  intro r hweightNonzero
  have hrzero : weight r * (1 - Real.exp (-x * shift r)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => hterm i)).mp hdeficit r (Finset.mem_univ r)
  have hexp : Real.exp (-x * shift r) = 1 := by
    rcases mul_eq_zero.mp hrzero with hzero | hzero
    · exact (hweightNonzero hzero).elim
    · exact (sub_eq_zero.mp hzero).symm
  have harg : -x * shift r = 0 :=
    (Real.exp_eq_one_iff (-x * shift r)).mp hexp
  nlinarith

/-- Equal positive replica weights make the rigidity total: exact damping preservation forces all
replica heights to coincide with the original height zero. -/
theorem fisherUniformReplicaDamping_eq_one_forces_zero_shift
    {k : ℕ} (hk : 0 < k) {shift : Fin k → ℝ} {x : ℝ}
    (hshift : ∀ r, 0 ≤ shift r)
    (hx : 0 < x)
    (hdamp : fisherReplicaDampingFactor
      k (fun _ => 1 / (k : ℝ)) shift x = 1) :
    ∀ r, shift r = 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hall := fisherReplicaDamping_eq_one_forces_zero_shift
    (weight := fun _ => 1 / (k : ℝ))
    (shift := shift) (x := x)
    (fun _ => (div_pos zero_lt_one hkR).le)
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp)
    hshift hx hdamp
  exact fun r => hall r (div_pos zero_lt_one hkR).ne'

/-- A positive-half-plane exponential kernel has no gain on one oriented interval: its Laplace
coefficient is bounded by coefficient norm times interval width. -/
theorem norm_orientedCutoffLaplaceCoefficient_le_width
    {lower upper : ℝ} (hlower : 0 ≤ lower) {coefficient node : ℂ}
    (hnode : 0 ≤ node.re) :
    ‖orientedCutoffLaplaceCoefficient
        lower upper coefficient node‖ ≤
      ‖coefficient‖ * max (upper - lower) 0 := by
  by_cases horder : lower ≤ upper
  · rw [orientedCutoffLaplaceCoefficient, if_pos horder,
      max_eq_left (sub_nonneg.mpr horder)]
    have hbound : ∀ u ∈ Set.uIoc lower upper,
        ‖Complex.exp (-node * (u : ℂ)) * coefficient‖ ≤ ‖coefficient‖ := by
      intro u hu
      rw [Set.uIoc_of_le horder] at hu
      have hu0 : 0 ≤ u := hlower.trans hu.1.le
      rw [norm_mul, Complex.norm_exp]
      have hexp : Real.exp ((-node * (u : ℂ)).re) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        have hm := mul_nonneg hnode hu0
        nlinarith
      exact mul_le_of_le_one_left (norm_nonneg coefficient) hexp
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa [abs_of_nonneg (sub_nonneg.mpr horder)] using h
  · rw [orientedCutoffLaplaceCoefficient, if_neg horder, norm_zero,
      max_eq_right (sub_nonpos.mpr (le_of_not_ge horder))]
    positivity

/-- Literal intervalized replica reporter at one Hardy node.  Both orientations are included so
the definition dominates every choice of a strict-lower joined presentation. -/
def fisherReplicaOrientedCollisionLaplace
    (k : ℕ) (p a d : ℝ) (height : Fin k → ℝ) (node : ℂ) : ℂ :=
  ∑ r : Fin k, ∑ s : Fin k,
    if s = r then 0 else
      orientedCutoffLaplaceCoefficient
        (min (height r) (height s)) (max (height r) (height s))
        ((((p / k) ^ (2 : ℕ) * (2 * a * d) : ℝ) : ℂ)) node

/-- Exact source preservation and nonzero oriented collision capacity are incompatible for
positive equal-mass scalar replicas.  Exact preservation collapses every height to zero, so every
oriented interval is degenerate and the common-Hardy reporter vanishes identically. -/
theorem fisherReplicaOrientedCollisionLaplace_eq_zero_of_dampingPreserving
    {k : ℕ} (hk : 0 < k) {p a d x : ℝ} {height : Fin k → ℝ} {node : ℂ}
    (hheight : ∀ r, 0 ≤ height r)
    (hx : 0 < x)
    (hdamp : fisherReplicaDampingFactor
      k (fun _ => 1 / (k : ℝ)) height x = 1) :
    fisherReplicaOrientedCollisionLaplace k p a d height node = 0 := by
  have hzero := fisherUniformReplicaDamping_eq_one_forces_zero_shift
    hk hheight hx hdamp
  simp [fisherReplicaOrientedCollisionLaplace,
    orientedCutoffLaplaceCoefficient, hzero]

/-- Class-level scalar no-go: a positive equal-mass replica family that preserves even one inward
Laplace damping moment cannot report a nonzero evacuated Fisher collision. -/
theorem no_positiveDampingPreservingReplica_recovers_fisherReplicaCollision
    {k : ℕ} (hk : 0 < k) {p a d x : ℝ} {height : Fin k → ℝ} {node : ℂ}
    (hcollision : 2 * p ^ (2 : ℕ) * a * d ≠ 0)
    (hheight : ∀ r, 0 ≤ height r)
    (hx : 0 < x)
    (hdamp : fisherReplicaDampingFactor
      k (fun _ => 1 / (k : ℝ)) height x = 1) :
    fisherReplicaOrientedCollisionLaplace k p a d height node ≠
      ((2 * p ^ (2 : ℕ) * a * d : ℝ) : ℂ) := by
  rw [fisherReplicaOrientedCollisionLaplace_eq_zero_of_dampingPreserving
    hk hheight hx hdamp]
  exact fun heq => hcollision (Complex.ofReal_injective heq.symm)

/-- Every literal oriented Laplace realization is bounded by interval collision capacity. -/
theorem norm_fisherReplicaOrientedCollisionLaplace_le_capacity
    {k : ℕ} {p a d : ℝ} {height : Fin k → ℝ} {node : ℂ}
    (hheight : ∀ r, 0 ≤ height r) (hnode : 0 ≤ node.re) :
    ‖fisherReplicaOrientedCollisionLaplace k p a d height node‖ ≤
      fisherReplicaIntervalCollisionCapacity k p a d height := by
  rw [fisherReplicaOrientedCollisionLaplace,
    fisherReplicaIntervalCollisionCapacity]
  refine (norm_sum_le Finset.univ _).trans ?_
  apply Finset.sum_le_sum
  intro r _
  refine (norm_sum_le Finset.univ _).trans ?_
  apply Finset.sum_le_sum
  intro s _
  by_cases hsr : s = r
  · simp [hsr]
  · simp only [hsr, if_false]
    have hbound := norm_orientedCutoffLaplaceCoefficient_le_width
      (lower := min (height r) (height s))
      (upper := max (height r) (height s))
      (show 0 ≤ min (height r) (height s) from
        le_min (hheight r) (hheight s))
      (coefficient := ((((p / k) ^ (2 : ℕ) * (2 * a * d) : ℝ) : ℂ)))
      (node := node) hnode
    have hwidth :
        max (max (height r) (height s) - min (height r) (height s)) 0 =
          |height r - height s| := by
      rw [max_eq_left (sub_nonneg.mpr min_le_max), abs_sub_comm]
      exact max_sub_min_eq_abs (height r) (height s)
    rw [hwidth] at hbound
    have hcoefficient :
        ‖((((p / k) ^ (2 : ℕ) * (2 * a * d) : ℝ) : ℂ))‖ =
          (p / k) ^ (2 : ℕ) * (2 * |a * d|) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (p / (k : ℝ))), abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_mul]
      ring
    rw [hcoefficient] at hbound
    exact hbound

/-- Vanishing replica width kills the literal common-Hardy collision contribution at every node
in the closed right half-plane. -/
theorem tendsto_fisherReplicaOrientedCollisionLaplace_zero
    (p a d : ℝ) (node : ℂ) (hnode : 0 ≤ node.re)
    (Delta : ℕ → ℝ) (height : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hheight : ∀ n r, 0 ≤ height n r)
    (hDelta : Tendsto Delta atTop (𝓝 0))
    (hDeltaNonneg : ∀ n, 0 ≤ Delta n)
    (hdiam : ∀ n r s, |height n r - height n s| ≤ Delta n) :
    Tendsto
      (fun n => fisherReplicaOrientedCollisionLaplace
        (n + 1) p a d (height n) node)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
  · exact fun n => norm_nonneg _
  · exact fun n => norm_fisherReplicaOrientedCollisionLaplace_le_capacity
      (hheight n) hnode
  · exact tendsto_fisherReplicaIntervalCollisionCapacity_zero
      p a d Delta height hDelta hDeltaNonneg hdiam

/-- Headline incompatibility: a nonzero cofinal algebraic collision cannot be the limit of the
same replicas' uniformly bounded, vanishing-width oriented common-Hardy reporters. -/
theorem no_vanishingWidthOrientedLaplace_recovers_fisherReplicaCollision
    (p a d : ℝ) (hcollision : 2 * p ^ (2 : ℕ) * a * d ≠ 0)
    (node : ℂ) (hnode : 0 ≤ node.re)
    (Delta : ℕ → ℝ) (height : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hheight : ∀ n r, 0 ≤ height n r)
    (hDelta : Tendsto Delta atTop (𝓝 0))
    (hDeltaNonneg : ∀ n, 0 ≤ Delta n)
    (hdiam : ∀ n r s, |height n r - height n s| ≤ Delta n) :
    ¬ Tendsto
      (fun n => fisherReplicaOrientedCollisionLaplace
        (n + 1) p a d (height n) node)
      atTop (𝓝 ((2 * p ^ (2 : ℕ) * a * d : ℝ) : ℂ)) := by
  intro htarget
  have hzero := tendsto_fisherReplicaOrientedCollisionLaplace_zero
    p a d node hnode Delta height hheight hDelta hDeltaNonneg hdiam
  have heq : (0 : ℂ) = ((2 * p ^ (2 : ℕ) * a * d : ℝ) : ℂ) :=
    tendsto_nhds_unique hzero htarget
  exact hcollision (Complex.ofReal_injective heq.symm)

end GaloisForLFunctions.HTGeometry
