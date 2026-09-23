import GaloisForLFunctions.RHTower.PurePointSpectralBlockRecurrenceLaw

/-!
# Pure-point observer-coherence law

The exact observer law extends to arbitrary pure-point spectral index types
and arbitrary observer families.  Under the physically necessary summability
condition, zero total displacement is equivalent to phase locking on every
positively weighted nonzero spectral block.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Total weighted squared displacement for an arbitrary family of observers
over an arbitrary pure-point spectrum. -/
def purePointObserverDistanceSq
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (phase : ι → ι → ℂ)
    (block : J → ι → ι → E) : ℝ :=
  ∑' p : J × (ι × ι),
    lam p.1 *
      ‖phase p.2.1 p.2.2 • block p.1 p.2.1 p.2.2 -
        block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ)

/-- Total observer-weighted phase energy over an arbitrary pure-point
spectrum. -/
def purePointObserverPhaseEnergy
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (phase : ι → ι → ℂ)
    (block : J → ι → ι → E) : ℝ :=
  ∑' p : J × (ι × ι),
    lam p.1 * ‖block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ) *
      ‖phase p.2.1 p.2.2 - 1‖ ^ (2 : ℕ)

private theorem observer_displacement_term_eq_phase_term
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : ℝ) (phase : ℂ) (block : E) :
    lam * ‖phase • block - block‖ ^ (2 : ℕ) =
      lam * ‖block‖ ^ (2 : ℕ) * ‖phase - 1‖ ^ (2 : ℕ) := by
  have h : phase • block - block = (phase - 1) • block := by
    module
  rw [h, norm_smul, mul_pow]
  ring

/--
Dimension-free observer law: every observer displacement is exactly the
corresponding coherence-weighted phase energy.
-/
theorem purePointObserverDistanceSq_eq_phaseEnergy
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (phase : ι → ι → ℂ)
    (block : J → ι → ι → E) :
    purePointObserverDistanceSq lam phase block =
      purePointObserverPhaseEnergy lam phase block := by
  unfold purePointObserverDistanceSq purePointObserverPhaseEnergy
  apply tsum_congr
  intro p
  exact observer_displacement_term_eq_phase_term
    (lam p.1) (phase p.2.1 p.2.2) (block p.1 p.2.1 p.2.2)

/-- The observer-displacement series is summable exactly when its phase-energy
series is summable. -/
theorem summable_purePointObserver_distance_iff_phaseEnergy
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (phase : ι → ι → ℂ)
    (block : J → ι → ι → E) :
    Summable (fun p : J × (ι × ι) =>
        lam p.1 *
          ‖phase p.2.1 p.2.2 • block p.1 p.2.1 p.2.2 -
            block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ)) ↔
      Summable (fun p : J × (ι × ι) =>
        lam p.1 * ‖block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ) *
          ‖phase p.2.1 p.2.2 - 1‖ ^ (2 : ℕ)) := by
  apply summable_congr
  intro p
  exact observer_displacement_term_eq_phase_term
    (lam p.1) (phase p.2.1 p.2.2) (block p.1 p.2.1 p.2.2)

/--
Universal pure-point zero law.  For nonnegative observer weights and a
summable phase-energy series, total return is exact precisely when every
positively observed nonzero spectral block has locked phase.
-/
theorem purePointObserverPhaseEnergy_eq_zero_iff
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (phase : ι → ι → ℂ)
    (block : J → ι → ι → E)
    (hlam : ∀ a, 0 ≤ lam a)
    (hsummable : Summable (fun p : J × (ι × ι) =>
      lam p.1 * ‖block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ) *
        ‖phase p.2.1 p.2.2 - 1‖ ^ (2 : ℕ))) :
    purePointObserverPhaseEnergy lam phase block = 0 ↔
      ∀ a i j, 0 < lam a → block a i j ≠ 0 → phase i j = 1 := by
  let f : J × (ι × ι) → ℝ := fun p =>
    lam p.1 * ‖block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ) *
      ‖phase p.2.1 p.2.2 - 1‖ ^ (2 : ℕ)
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    exact mul_nonneg
      (mul_nonneg (hlam p.1) (sq_nonneg _))
      (sq_nonneg _)
  have hf_summable : Summable f := by
    simpa only [f] using hsummable
  constructor
  · intro hzero a i j hpos hblock
    have hsum : ∑' p, f p = 0 := by
      simpa only [f, purePointObserverPhaseEnergy] using hzero
    have hle : f (a, (i, j)) ≤ ∑' p, f p :=
      hf_summable.le_tsum (a, (i, j))
        (fun p _hne => hf_nonneg p)
    have hterm : f (a, (i, j)) = 0 :=
      le_antisymm (by simpa only [hsum] using hle)
        (hf_nonneg (a, (i, j)))
    have hnorm_block : ‖block a i j‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hblock
    have hphase_sq : ‖phase i j - 1‖ ^ (2 : ℕ) = 0 := by
      have hproduct :
          (lam a * ‖block a i j‖ ^ (2 : ℕ)) *
            ‖phase i j - 1‖ ^ (2 : ℕ) = 0 := by
        simpa only [f] using hterm
      exact (mul_eq_zero.mp hproduct).resolve_left
        (mul_ne_zero hpos.ne' (pow_ne_zero 2 hnorm_block))
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hphase_sq))
  · intro hlocked
    have hfun : f = 0 := by
      funext p
      by_cases hweight : lam p.1 = 0
      · simp [f, hweight]
      have hpos : 0 < lam p.1 :=
        lt_of_le_of_ne (hlam p.1) (Ne.symm hweight)
      by_cases hblock : block p.1 p.2.1 p.2.2 = 0
      · simp [f, hblock]
      have hphase := hlocked p.1 p.2.1 p.2.2 hpos hblock
      simp [f, hphase]
    rw [purePointObserverPhaseEnergy]
    simpa only [f, hfun] using! (tsum_zero : ∑' _p : J × (ι × ι), (0 : ℝ) = 0)

/--
Hamiltonian specialization: exact return occurs precisely when every visible
energy gap has accumulated an integer phase.
-/
theorem purePointHamiltonianObserverDistanceSq_eq_zero_iff
    {J ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (lam : J → ℝ) (t : ℝ) (energy : ι → ℝ)
    (block : J → ι → ι → E)
    (hlam : ∀ a, 0 ≤ lam a)
    (hsummable : Summable (fun p : J × (ι × ι) =>
      lam p.1 * ‖block p.1 p.2.1 p.2.2‖ ^ (2 : ℕ) *
        ‖purePointHamiltonianPhase t energy p.2.1 p.2.2 - 1‖ ^ (2 : ℕ))) :
    purePointObserverDistanceSq lam
        (purePointHamiltonianPhase t energy) block = 0 ↔
      ∀ a i j, 0 < lam a → block a i j ≠ 0 →
        Complex.exp
          (Complex.I * (((t * (energy i - energy j) : ℝ) : ℂ))) = 1 := by
  rw [purePointObserverDistanceSq_eq_phaseEnergy]
  simpa only [purePointHamiltonianPhase] using
    (purePointObserverPhaseEnergy_eq_zero_iff
      lam (purePointHamiltonianPhase t energy) block hlam hsummable)

end RHTower
