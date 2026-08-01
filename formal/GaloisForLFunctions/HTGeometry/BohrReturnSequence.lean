import GaloisForLFunctions.HTGeometry.BohrSpectrum

/-!
# Common return times of a finite family of almost periodic functions

Almost periodicity of finitely many functions is almost periodicity of the tuple, so for every
tolerance the functions share a relatively dense set of almost periods.  Choosing tolerances `1/(l+1)`
and almost periods beyond `l` produces a single sequence of return times tending to `+∞` along which
every member of the family converges to itself, uniformly on the line.

This is the diagonal choice of return times used by the recurrence collapse: a finite differential
relation is translated along one sequence that works simultaneously for all the finitely many
coefficient and monomial functions appearing in it.
-/

open Filter Topology

namespace GaloisForLFunctions

open HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- A finite family of almost periodic functions is almost periodic as a tuple. -/
theorem isBohrAlmostPeriodic_fin : ∀ {n : ℕ} {g : Fin n → ℝ → E},
    (∀ i, Continuous (g i)) → (∀ i, IsBohrAlmostPeriodic (g i)) →
      IsBohrAlmostPeriodic (fun x => (fun i => g i x : Fin n → E)) := by
  intro n
  induction n with
  | zero =>
      intro g _ _ ε hε
      refine ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun x => ?_⟩⟩
      have : (fun i : Fin 0 => g i (x + a)) - (fun i : Fin 0 => g i x) = 0 := by
        funext i
        exact absurd i.2 (by omega)
      rw [this, norm_zero]
      exact hε.le
  | succ m ih =>
      intro g hcont hap ε hε
      set G : ℝ → (Fin m → E) := fun x => (fun i => g i.succ x) with hGdef
      have hGcont : Continuous G := by
        refine continuous_pi fun i => hcont i.succ
      have hGap : IsBohrAlmostPeriodic G := ih (fun i => hcont i.succ) (fun i => hap i.succ)
      obtain ⟨L, hL, hdense⟩ :=
        exists_common_almostPeriods (hcont 0) (hap 0) hGcont hGap hε
      refine ⟨L, hL, fun a => ?_⟩
      obtain ⟨τ, hτmem, hτ0, hτG⟩ := hdense a
      refine ⟨τ, hτmem, fun x => ?_⟩
      rw [pi_norm_le_iff_of_nonneg hε.le]
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hτ0 x
      · intro j
        have hj := hτG x
        rw [pi_norm_le_iff_of_nonneg hε.le] at hj
        simpa using hj j

/-- **Bohr return sequence.**  A finite family of almost periodic functions admits a common
sequence of return times tending to `+∞` along which every member converges uniformly to itself. -/
theorem exists_bohr_return_sequence {n : ℕ} {g : Fin n → ℝ → E}
    (hcont : ∀ i, Continuous (g i)) (hap : ∀ i, IsBohrAlmostPeriodic (g i)) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      ∀ i : Fin n, ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ x : ℝ, ‖g i (x + T l) - g i x‖ ≤ ε := by
  classical
  have hall : ∀ l : ℕ, ∃ τ : ℝ, (l : ℝ) ≤ τ ∧
      ∀ i x, ‖g i (x + τ) - g i x‖ ≤ 1 / (l + 1 : ℝ) := by
    intro l
    have hpos : (0:ℝ) < 1 / (l + 1 : ℝ) := by positivity
    obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_fin hcont hap _ hpos
    obtain ⟨τ, hτmem, hτ⟩ := hdense (l : ℝ)
    refine ⟨τ, hτmem.1, fun i x => ?_⟩
    have h := hτ x
    rw [pi_norm_le_iff_of_nonneg hpos.le] at h
    simpa using h i
  choose T hTge hTbound using hall
  refine ⟨T, ?_, ?_⟩
  · refine tendsto_atTop_mono hTge ?_
    exact tendsto_natCast_atTop_atTop
  · intro i ε hε
    obtain ⟨l₀, hl₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop l₀] with l hl x
    refine le_trans (hTbound l i x) ?_
    have hmono : 1 / (l + 1 : ℝ) ≤ 1 / (l₀ + 1 : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hl
    exact le_trans hmono hl₀.le

/-- Pointwise form: along the common return sequence every member of the family converges to itself
at every point. -/
theorem exists_bohr_return_sequence_tendsto {n : ℕ} {g : Fin n → ℝ → E}
    (hcont : ∀ i, Continuous (g i)) (hap : ∀ i, IsBohrAlmostPeriodic (g i)) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      ∀ (i : Fin n) (x : ℝ), Tendsto (fun l => g i (x + T l)) atTop (nhds (g i x)) := by
  obtain ⟨T, hT, hbound⟩ := exists_bohr_return_sequence hcont hap
  refine ⟨T, hT, fun i x => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨l₀, hl₀⟩ := (hbound i (ε / 2) (by linarith)).exists_forall_of_atTop
  refine ⟨l₀, fun l hl => ?_⟩
  have h := hl₀ l hl x
  rw [dist_eq_norm]
  linarith [h]

end GaloisForLFunctions
