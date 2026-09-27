import GaloisForLFunctions.RHTower.LogarithmicExponentialEntryConvolution

/-!
# A Mellin oscillator for signed arithmetic prefixes

The two critical modes are `exp(t/2) sum(w/n)` and `exp(-t/2) sum(w)`.
Their difference and half-sum solve the autonomous Euler--Lagrange system
for `L(q,p)=p^2+q^2/4`. Time translation preserves the action with its
translated endpoints. The Noether energy is the product of the two
prefix sums. Entry jumps include a signed cross term and a diagonal term;
no global conservation across arithmetic forcing is asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def mellinPrefixMass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, w n

def mellinPrefixReciprocal (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, w n / n

def mellinPrefixPosition (w : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * mellinPrefixReciprocal w N - Real.exp (-(t / 2)) * mellinPrefixMass w N

def mellinPrefixMomentum (w : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (Real.exp (t / 2) * mellinPrefixReciprocal w N + Real.exp (-(t / 2)) * mellinPrefixMass w N) / 2

def mellinOscillatorAction (q p : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, p t ^ 2 + q t ^ 2 / 4

theorem mellinOscillatorAction_translation (q p : ℝ → ℝ) (a b r : ℝ) :
    mellinOscillatorAction (fun t => q (t + r)) (fun t => p (t + r)) a b =
      mellinOscillatorAction q p (a + r) (b + r) := by
  unfold mellinOscillatorAction
  exact intervalIntegral.integral_comp_add_right (fun t => p t ^ 2 + q t ^ 2 / 4) r

theorem hasDerivAt_mellinPrefixPosition (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (mellinPrefixPosition w N) (mellinPrefixMomentum w N t) t := by
  have hp := ((Real.hasDerivAt_exp (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)).mul_const (mellinPrefixReciprocal w N)
  have hm := ((Real.hasDerivAt_exp (-(t / 2))).comp t
    (((hasDerivAt_id t).div_const 2).neg)).mul_const (mellinPrefixMass w N)
  apply (hp.sub hm).congr_deriv
  unfold mellinPrefixMomentum
  ring

theorem hasDerivAt_mellinPrefixMomentum (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (mellinPrefixMomentum w N) (mellinPrefixPosition w N t / 4) t := by
  have hp := ((Real.hasDerivAt_exp (t / 2)).comp t
    ((hasDerivAt_id t).div_const 2)).mul_const (mellinPrefixReciprocal w N)
  have hm := ((Real.hasDerivAt_exp (-(t / 2))).comp t
    (((hasDerivAt_id t).div_const 2).neg)).mul_const (mellinPrefixMass w N)
  apply ((hp.add hm).div_const 2).congr_deriv
  unfold mellinPrefixPosition
  ring

/-- The autonomous oscillator energy is exactly an arithmetic prefix product. -/
theorem mellinPrefix_noether_energy (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    mellinPrefixMomentum w N t ^ 2 - mellinPrefixPosition w N t ^ 2 / 4 =
      mellinPrefixReciprocal w N * mellinPrefixMass w N := by
  have he : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold mellinPrefixMomentum mellinPrefixPosition
  calc
    _ = (Real.exp (t / 2) * Real.exp (-(t / 2))) *
        (mellinPrefixReciprocal w N * mellinPrefixMass w N) := by ring
    _ = _ := by rw [he, one_mul]

theorem hasDerivAt_mellinPrefix_noether_energy (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (fun s => mellinPrefixMomentum w N s ^ 2 -
      mellinPrefixPosition w N s ^ 2 / 4) 0 t := by
  simpa only [mellinPrefix_noether_energy] using
    (hasDerivAt_const t (mellinPrefixReciprocal w N * mellinPrefixMass w N))

theorem mellinPrefixMass_succ (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixMass w (N + 1) = mellinPrefixMass w N + w (N + 1) := by
  exact Finset.sum_Icc_succ_top (by omega) w

theorem mellinPrefixReciprocal_succ (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixReciprocal w (N + 1) = mellinPrefixReciprocal w N + w (N + 1) / (N + 1 : ℕ) := by
  exact Finset.sum_Icc_succ_top (by omega) (fun n => w n / n)

/-- The force at a new arithmetic entry changes the Noether charge by an
explicit signed cross term plus its diagonal square. -/
theorem mellinPrefix_noether_energy_jump (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixReciprocal w (N + 1) * mellinPrefixMass w (N + 1) -
      mellinPrefixReciprocal w N * mellinPrefixMass w N =
        w (N + 1) * (mellinPrefixReciprocal w N + mellinPrefixMass w N / (N + 1 : ℕ)) +
          w (N + 1) ^ 2 / (N + 1 : ℕ) := by
  rw [mellinPrefixMass_succ, mellinPrefixReciprocal_succ]
  ring

private theorem entry_modes_match (N : ℕ) :
    Real.exp (Real.log (N + 1 : ℕ) / 2) / (N + 1 : ℕ) =
      Real.exp (-(Real.log (N + 1 : ℕ) / 2)) := by
  have hn : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  calc
    _ = Real.exp (Real.log (N + 1 : ℕ) / 2 - Real.log (N + 1 : ℕ)) := by
      rw [Real.exp_sub, Real.exp_log hn]
    _ = _ := by congr 1; ring

theorem mellinPrefixPosition_entry_continuity (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixPosition w (N + 1) (Real.log (N + 1 : ℕ)) =
      mellinPrefixPosition w N (Real.log (N + 1 : ℕ)) := by
  unfold mellinPrefixPosition
  rw [mellinPrefixMass_succ, mellinPrefixReciprocal_succ]
  have he := entry_modes_match N
  calc
    _ = Real.exp (Real.log (N + 1 : ℕ) / 2) * mellinPrefixReciprocal w N -
        Real.exp (-(Real.log (N + 1 : ℕ) / 2)) * mellinPrefixMass w N +
        w (N + 1) * (Real.exp (Real.log (N + 1 : ℕ) / 2) / (N + 1 : ℕ) -
          Real.exp (-(Real.log (N + 1 : ℕ) / 2))) := by ring
    _ = _ := by rw [he, sub_self, mul_zero, add_zero]

theorem mellinPrefixMomentum_entry_jump (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixMomentum w (N + 1) (Real.log (N + 1 : ℕ)) -
      mellinPrefixMomentum w N (Real.log (N + 1 : ℕ)) =
        w (N + 1) * Real.exp (-(Real.log (N + 1 : ℕ) / 2)) := by
  unfold mellinPrefixMomentum
  rw [mellinPrefixMass_succ, mellinPrefixReciprocal_succ]
  calc
    _ = w (N + 1) / 2 * (Real.exp (Real.log (N + 1 : ℕ) / 2) / (N + 1 : ℕ) +
        Real.exp (-(Real.log (N + 1 : ℕ) / 2))) := by ring
    _ = _ := by rw [entry_modes_match]; ring

theorem logarithmicFiniteEntryProfile_exp_eq_prefix (w : ℕ → ℝ) (U : ℕ) (t : ℝ) :
    logarithmicFiniteEntryProfile w U Real.exp t =
      Real.exp t * mellinPrefixReciprocal w (min U ⌊Real.exp t⌋₊) := by
  rw [logarithmicFiniteEntryProfile_eq_min_prefix, mellinPrefixReciprocal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [Real.exp_sub, Real.exp_log hnp]
  ring

theorem logarithmicFiniteEntryProfile_one_eq_prefix (w : ℕ → ℝ) (U : ℕ) (t : ℝ) :
    logarithmicFiniteEntryProfile w U (fun _ => 1) t =
      mellinPrefixMass w (min U ⌊Real.exp t⌋₊) := by
  simp only [logarithmicFiniteEntryProfile_eq_min_prefix, mellinPrefixMass, mul_one]

end RHTower
