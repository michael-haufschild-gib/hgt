import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Necessity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Sufficiency

/-!
# Exact heat threshold at adaptive clock resolution

The diagonal and the near-diagonal strip account for the entire abscissa.
For a nonzero clock, inverse square-root resolution in the product of the
labels is exactly the onset of detection of probability-preserving splitting.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock

open SampledClocks CopyExchange
variable (M : Clock)

def abscissa : ℝ := if M.time = 0 then 1 else max (1/2) (1-(M.exponent:ℝ))

private theorem vacuum_clock (ht : M.time = 0) : M.gate = (binary 0).Resonant := by
  funext x
  have hz (n : ℕ+) : clockPhase 0 n = 1 := by change Circle.exp (0*energy n) = 1; simp
  have ha : M.gate x := by
    change dist (clockPhase M.time (x false)) (clockPhase M.time (x true)) < _
    rw [ht,hz,hz,dist_self]
    exact mul_pos M.scale.property (Real.exp_pos _)
  have hb : (binary 0).Resonant x := fun _ => by simp [Network.phase,binary]
  exact propext (iff_of_true ha hb)

/-- The heat is trace class precisely to the right of the adaptive abscissa, at every time. -/
theorem trace_iff (s : ℂ) : HasSectorHeat M.gate s ↔ M.abscissa < s.re := by
  by_cases ht : M.time = 0
  · rw [M.vacuum_clock ht,binary_threshold,abscissa,if_pos ht,if_pos rfl]
  · rw [M.heat_iff,abscissa,if_neg ht,max_lt_iff]
    exact ⟨fun h => ⟨M.diagonal_bound h,M.strip_bound h⟩,fun h => M.heat_sum_of_bounds ht h.1 h.2⟩

/-- The heat operator on the closed subspace spanned by accepted occupations. -/
def measuredHeat (s : {z : ℂ // M.abscissa < z.re}) :=
  sectorHeat M.gate ⟨s.val,(sectorHeat_iff _ _).mp ((M.trace_iff s.val).mpr s.property)⟩

theorem partition_trace (s : {z : ℂ // M.abscissa < z.re}) :
    ContinuousLinearMap.opTrace (M.measuredHeat s) =
      ∑' x : {x // M.gate x}, heat s.val (x.val false*x.val true) := by
  rw [measuredHeat,sectorHeat_trace]
  apply tsum_congr
  intro x
  rw [wordHeat,Fintype.prod_bool,heat_mul,mul_comm]

theorem abscissa_half_iff : M.abscissa = 1/2 ↔ M.time ≠ 0 ∧ 1/2 ≤ (M.exponent : ℝ) := by
  by_cases ht : M.time = 0
  · simp [abscissa,ht]
  · rw [abscissa,if_neg ht,max_eq_left_iff]
    exact ⟨fun h => ⟨ht,by linarith only [h]⟩,fun h => by linarith only [h.2]⟩

def AtBoundary (s : ℂ) : Prop :=
  ¬HasSectorHeat M.gate s ∧ ∀ δ : ℝ, 0 < δ → HasSectorHeat M.gate (s+(δ : ℂ))

theorem boundary_iff (s : ℂ) : M.AtBoundary s ↔ s.re = M.abscissa := by
  simp only [AtBoundary,M.trace_iff,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · rintro ⟨hl,hr⟩
    apply le_antisymm hl
    by_contra! h
    have hb := hr _ (sub_pos.mpr h)
    linarith only [hb]
  · intro h
    exact ⟨h.le,fun δ hδ => by linarith only [h,hδ]⟩

/-- An adaptive clock detects the isometry line exactly at nonzero time and exponent at least one half. -/
theorem detects_split_iff :
    (∀ s : ℂ, (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔ M.AtBoundary s) ↔
      M.time ≠ 0 ∧ 1/2 ≤ (M.exponent : ℝ) := by
  simp only [split_isometric_iff,M.boundary_iff,← M.abscissa_half_iff]
  constructor
  · intro h
    have hh := (h (1/2)).mp (by norm_num)
    simpa using hh.symm
  · intro h s
    rw [h]

#print axioms trace_iff
#print axioms partition_trace
#print axioms abscissa_half_iff
#print axioms boundary_iff
#print axioms detects_split_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Clock
