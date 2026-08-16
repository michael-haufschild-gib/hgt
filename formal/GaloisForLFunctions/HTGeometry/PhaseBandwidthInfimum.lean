import GaloisForLFunctions.HTGeometry.CentralizerBudgetSplit

/-!
# The bandwidth as an attained infimum

The bandwidth of a phase assignment is the infimum of the Lipschitz constants of its lifts.  That
infimum is attained and equals the largest nearest-neighbour ratio: the ratio is a lower bound
because a Lipschitz lift must cross each gap, and it is achieved by the shortest-increment lift
extended by the McShane formula.

Only the gaps below the top index matter, so the construction is stated with the step hypothesis
restricted to `j < n`.  With the infimum in hand, an exact recurrence -- all adjacent phases equal --
gives bandwidth exactly zero, not merely an admissible zero.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Bounded-range versions of the construction -/

theorem shortestLift_sub_le_of_lt {θ E : ℕ → ℝ} {L : ℝ} {n : ℕ}
    (hstep : ∀ j, j < n → circDist (θ (j + 1)) (θ j) ≤ L * (E (j + 1) - E j)) :
    ∀ i j : ℕ, i ≤ j → j ≤ n → |shortestLift θ j - shortestLift θ i| ≤ L * (E j - E i) := by
  intro i j hij hjn
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    subst this
    simp
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
      have hjn' : j ≤ n := le_trans (Nat.le_succ j) hjn
      have hprev := ih hij' hjn'
      have hjlt : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hjn
      have hgap : |shortestLift θ (j + 1) - shortestLift θ j| ≤ L * (E (j + 1) - E j) := by
        rw [shortestLift]
        simpa [circDist] using hstep j hjlt
      have htri : |shortestLift θ (j + 1) - shortestLift θ i|
          ≤ |shortestLift θ (j + 1) - shortestLift θ j|
            + |shortestLift θ j - shortestLift θ i| := abs_sub_le _ _ _
      have hcomb : L * (E (j + 1) - E j) + L * (E j - E i) = L * (E (j + 1) - E i) := by ring
      linarith [htri, hgap, hprev]
    · have : i = j + 1 := le_antisymm hij hge
      subst this
      simp

/-- **The bandwidth is achieved**, with the step hypothesis restricted to the gaps that exist. -/
theorem exists_phaseLift_of_step_lt {θ E : ℕ → ℝ} {L : ℝ} {n : ℕ} (hL : 0 ≤ L)
    (hmono : ∀ j, j < n → E j ≤ E (j + 1))
    (hstep : ∀ j, j < n → circDist (θ (j + 1)) (θ j) ≤ L * (E (j + 1) - E j)) :
    ∃ p : ℝ → ℝ, (∀ x y, |p x - p y| ≤ L * |x - y|) ∧ IsPhaseLift θ E n p := by
  set q : ℕ → ℝ := shortestLift θ with hq
  have hEmono : ∀ i j : ℕ, i ≤ j → j ≤ n → E i ≤ E j := by
    intro i j hij hjn
    induction j with
    | zero => simp [Nat.le_zero.mp hij]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hjn' : j ≤ n := le_trans (Nat.le_succ j) hjn
        have hjlt : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hjn
        exact le_trans (ih (Nat.lt_succ_iff.mp hlt) hjn') (hmono j hjlt)
      · have : i = j + 1 := le_antisymm hij hge
        subst this
        exact le_rfl
  have hcompat : ∀ i ≤ n, ∀ j ≤ n, q i - q j ≤ L * |E i - E j| := by
    intro i hi j hj
    rcases le_total j i with hji | hij
    · have h := shortestLift_sub_le_of_lt hstep j i hji hi
      have habs : |E i - E j| = E i - E j :=
        abs_of_nonneg (by linarith [hEmono j i hji hi])
      rw [habs]
      linarith [(abs_le.mp h).2]
    · have h := shortestLift_sub_le_of_lt hstep i j hij hj
      have habs : |E i - E j| = E j - E i := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith [hEmono i j hij hj])
      rw [habs]
      linarith [(abs_le.mp h).1]
  refine ⟨mcShaneLift q E L n, mcShaneLift_lip q E hL n, fun j hj => ?_⟩
  rw [mcShaneLift_apply q E hcompat hj]
  exact shortestLift_congr θ j

/-! ## The bandwidth infimum -/

/-- The set of Lipschitz constants of lifts of a phase assignment. -/
def phaseLiftConstants (θ E : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  {L : ℝ | ∃ p : ℝ → ℝ, (∀ x y, |p x - p y| ≤ L * |x - y|) ∧ IsPhaseLift θ E n p}

/-- **The spectral phase bandwidth**, as in `(5)`. -/
noncomputable def phaseBandwidth (θ E : ℕ → ℝ) (n : ℕ) : ℝ := sInf (phaseLiftConstants θ E n)

/-- **`(7)`: the bandwidth is the largest nearest-neighbour ratio, and it is attained.** -/
theorem phaseBandwidth_eq {θ E : ℕ → ℝ} {n : ℕ} {M : ℝ}
    (hmono : ∀ j, j < n → E j < E (j + 1))
    (hub : ∀ j, j < n → circDist (θ (j + 1)) (θ j) ≤ M * (E (j + 1) - E j))
    {j₀ : ℕ} (hj₀ : j₀ < n)
    (hattain : circDist (θ (j₀ + 1)) (θ j₀) = M * (E (j₀ + 1) - E j₀)) :
    phaseBandwidth θ E n = M := by
  have hgap : 0 < E (j₀ + 1) - E j₀ := by linarith [hmono j₀ hj₀]
  have hM0 : 0 ≤ M := by
    have hnn : 0 ≤ circDist (θ (j₀ + 1)) (θ j₀) := circDist_nonneg _ _
    rw [hattain] at hnn
    nlinarith [hnn, hgap]
  have hmem : M ∈ phaseLiftConstants θ E n :=
    exists_phaseLift_of_step_lt hM0 (fun j hj => le_of_lt (hmono j hj)) hub
  have hlb : ∀ L ∈ phaseLiftConstants θ E n, M ≤ L := by
    rintro L ⟨p, hLip, hlift⟩
    have hj₀n : j₀ + 1 ≤ n := hj₀
    have hj₀n' : j₀ ≤ n := le_trans (Nat.le_succ j₀) hj₀n
    have h := circDist_le_of_lip hLip hlift hj₀n hj₀n'
    rw [abs_of_pos hgap, hattain] at h
    nlinarith [h, hgap]
  exact IsLeast.csInf_eq ⟨hmem, hlb⟩

/-- **`(14)`/`(15)`: an exact projective recurrence has bandwidth exactly zero.** -/
theorem phaseBandwidth_eq_zero {θ E : ℕ → ℝ} {n : ℕ}
    (hmono : ∀ j, j < n → E j < E (j + 1)) {j₀ : ℕ} (hj₀ : j₀ < n)
    (hzero : ∀ j, j < n → circDist (θ (j + 1)) (θ j) = 0) :
    phaseBandwidth θ E n = 0 := by
  refine phaseBandwidth_eq hmono (fun j hj => ?_) hj₀ ?_
  · rw [hzero j hj, zero_mul]
  · rw [hzero j₀ hj₀, zero_mul]

/-! ## The robust bandwidth -/

theorem phaseBandwidth_nonneg (θ E : ℕ → ℝ) (n : ℕ) : 0 ≤ phaseBandwidth θ E n := by
  refine Real.sInf_nonneg fun L hL => ?_
  obtain ⟨p, hLip, _⟩ := hL
  exact lip_nonneg hLip

/-- **`(6)`: the robust bandwidth**, the infimum of the bandwidths of the admissible competitors. -/
noncomputable def robustPhaseBandwidth (E : ℕ → ℝ) (n : ℕ) (S : Set (ℕ → ℝ)) : ℝ :=
  sInf ((fun θ => phaseBandwidth θ E n) '' S)

/-- **`(15)`: a competitor of zero bandwidth collapses the robust bandwidth.**  Under an approximate
recurrence the constant phase assignment is admissible and has bandwidth zero, so the robust
bandwidth is exactly zero. -/
theorem robustPhaseBandwidth_eq_zero {E : ℕ → ℝ} {n : ℕ} {S : Set (ℕ → ℝ)} {θ₀ : ℕ → ℝ}
    (hmem : θ₀ ∈ S) (hzero : phaseBandwidth θ₀ E n = 0) :
    robustPhaseBandwidth E n S = 0 := by
  refine IsLeast.csInf_eq ⟨⟨θ₀, hmem, hzero⟩, ?_⟩
  rintro b ⟨θ, _, rfl⟩
  exact phaseBandwidth_nonneg θ E n


/-- **Every circle point is a phase.**  This is the bridge from the card's `ζⱼ` to the real phases
`θⱼ` that `IsPhaseLift` uses. -/
theorem exists_phase_of_norm_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ θ : ℝ, Complex.exp (-(θ : ℂ) * Complex.I) = ζ := by
  refine ⟨-Complex.arg ζ, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hζ] at h
  push_cast at h ⊢
  rw [neg_neg]
  simpa using h


/-! ## The spectral torus in the diagonal model -/

section DiagonalModel

open _root_.Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **The spectral torus in the eigenbasis.**  A combination of the rank-one spectral projections is
the diagonal matrix of its coefficients, so `(3)` is the diagonal model. -/
theorem sum_smul_spectralProj (ζ : d → ℂ) :
    ∑ j, ζ j • Matrix.diagonal (fun l => if l = j then (1 : ℂ) else 0) = Matrix.diagonal ζ := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.diagonal_apply_eq]
    · intro c _ hca
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      rw [if_neg (Ne.symm hca), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Matrix.diagonal_apply_ne _ hab]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [Matrix.diagonal_apply_ne _ hab]

/-- **The static orbit is diagonal in the eigenbasis**, with entries the orbit phases. -/
theorem exp_diagonal_orbit (v : d → ℂ) :
    NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp v) :=
  Matrix.exp_diagonal v

end DiagonalModel

end GaloisForLFunctions.HTGeometry
