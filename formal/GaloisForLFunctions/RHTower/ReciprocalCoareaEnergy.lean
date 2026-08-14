import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.ReciprocalCoareaOptimality

/-!
# Reciprocal energies of a cofactor shell

In the complementary logarithmic coordinate `u = log(x/p)` a cofactor shell carries prime
log-density `v - u + O(1)` (Mertens' first theorem in window form).  The outer certification
energy weights each prime by `u^{-2}` and the inner energy by the available logarithmic length
`v`, so their product is bounded independently of the scale: the two powers cancel before any
Cauchy–Schwarz step.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The prime log-density mass of a window `(A, B]`. -/
def primeLogWindowMass (A B : ℝ) : ℝ :=
  mertensPrimeWeightSum ⌊B⌋₊ - mertensPrimeWeightSum ⌊A⌋₊

/-- The uniform window constant of the prime log-density. -/
def primeLogWindowConst : ℝ := 2 * (mertensPrimeWindowBound + 1)

theorem primeLogWindowConst_nonneg : 0 ≤ primeLogWindowConst := by
  have := mertensPrimeWindowBound_nonneg
  rw [primeLogWindowConst]
  linarith

/-- **Mertens' first theorem in window form.** -/
theorem abs_primeLogWindowMass_sub_le {A B : ℝ} (hA : 2 ≤ A) (hB : 2 ≤ B) :
    |primeLogWindowMass A B - (Real.log B - Real.log A)| ≤ primeLogWindowConst := by
  have hAbd := abs_mertensPrimeWeightSum_floor_sub_log_le hA
  have hBbd := abs_mertensPrimeWeightSum_floor_sub_log_le hB
  have hA' := abs_le.mp hAbd
  have hB' := abs_le.mp hBbd
  rw [primeLogWindowMass, primeLogWindowConst, abs_le]
  constructor <;> linarith [hA'.1, hA'.2, hB'.1, hB'.2]

/-- The prime log-density of a cofactor shell is its logarithmic width up to one constant. -/
theorem abs_coareaShellMass_sub_le {x u v : ℝ} (hx : 0 < x) (huv : u ≤ v)
    (hA : 2 ≤ x * Real.exp (-v)) :
    |primeLogWindowMass (x * Real.exp (-v)) (x * Real.exp (-u)) - (v - u)|
      ≤ primeLogWindowConst := by
  have hexp : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hB : 2 ≤ x * Real.exp (-u) := by
    have hmul : x * Real.exp (-v) ≤ x * Real.exp (-u) := by
      exact mul_le_mul_of_nonneg_left hexp hx.le
    linarith
  have hlogA : Real.log (x * Real.exp (-v)) = Real.log x - v := by
    rw [Real.log_mul (ne_of_gt hx) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  have hlogB : Real.log (x * Real.exp (-u)) = Real.log x - u := by
    rw [Real.log_mul (ne_of_gt hx) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  have h := abs_primeLogWindowMass_sub_le hA hB
  rw [hlogA, hlogB] at h
  have hval : Real.log x - u - (Real.log x - v) = v - u := by ring
  rwa [hval] at h

/-! ## The two certification energies -/

/-- The outer certification energy of the shell `x e^{-v} < p ≤ x e^{-u}`: each prime is weighted
by the inverse square of its cofactor scale.  The shell is half-open, so consecutive shells tile
the range of scales without repeating a prime. -/
def coareaOuterEnergy (x u v : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊,
    (if p.Prime ∧ x * Real.exp (-v) < (p : ℝ) then
      Real.log p / ((p : ℝ) * Real.log (x / p) ^ 2) else 0)

/-- The inner certification energy at logarithmic length `v`, with cell norm `L`. -/
def coareaInnerEnergy (L v : ℝ) : ℝ := L ^ 2 * mertensPrimeWeightSum ⌊Real.exp v⌋₊

theorem coareaOuterEnergy_nonneg {x u v : ℝ} : 0 ≤ coareaOuterEnergy x u v := by
  refine Finset.sum_nonneg fun p hp => ?_
  by_cases hcase : p.Prime ∧ x * Real.exp (-v) < (p : ℝ)
  · rw [if_pos hcase]
    have hp0 : (0 : ℝ) < p := by
      have := hcase.1.pos
      exact_mod_cast this
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hcase.1.one_lt.le)
    positivity
  · rw [if_neg hcase]

/-- **The outer energy is the shell mass damped by the inverse square cofactor scale.** -/
theorem coareaOuterEnergy_le {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (huv : u ≤ v)
    (hA : 2 ≤ x * Real.exp (-v)) :
    coareaOuterEnergy x u v
      ≤ (v - u + primeLogWindowConst) / u ^ 2 := by
  classical
  have hexp : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hAB : x * Real.exp (-v) ≤ x * Real.exp (-u) := mul_le_mul_of_nonneg_left hexp hx.le
  have hB : 2 ≤ x * Real.exp (-u) := le_trans hA hAB
  have hA0 : (0 : ℝ) ≤ x * Real.exp (-v) := by linarith
  have hmass := abs_le.mp (abs_coareaShellMass_sub_le hx huv hA)
  -- termwise damping: on the shell the cofactor scale is at least `u`
  have hterm : ∀ p ∈ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊,
      (if p.Prime ∧ x * Real.exp (-v) < (p : ℝ) then
        Real.log p / ((p : ℝ) * Real.log (x / p) ^ 2) else 0)
        ≤ (if p.Prime ∧ x * Real.exp (-v) < (p : ℝ) then Real.log p / (p : ℝ) else 0) / u ^ 2 := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    by_cases hcase : p.Prime ∧ x * Real.exp (-v) < (p : ℝ)
    · rw [if_pos hcase, if_pos hcase]
      have hp0 : (0 : ℝ) < p := by
        have := hcase.1.pos
        exact_mod_cast this
      have hple : (p : ℝ) ≤ x * Real.exp (-u) := by
        have := Nat.floor_le (by positivity : (0 : ℝ) ≤ x * Real.exp (-u))
        exact le_trans (by exact_mod_cast hp.2) this
      have hlogx : u ≤ Real.log (x / p) := by
        have hquot : Real.exp u ≤ x / p := by
          rw [le_div_iff₀ hp0]
          have hval : Real.exp u * (x * Real.exp (-u)) = x := by
            rw [← mul_assoc, mul_comm (Real.exp u) x, mul_assoc, ← Real.exp_add]
            simp
          calc Real.exp u * (p : ℝ) ≤ Real.exp u * (x * Real.exp (-u)) := by
                exact mul_le_mul_of_nonneg_left hple (Real.exp_pos u).le
            _ = x := hval
        have hlog := Real.log_le_log (Real.exp_pos u) hquot
        rwa [Real.log_exp] at hlog
      have hlogpos : (0 : ℝ) < Real.log (x / p) := lt_of_lt_of_le hu hlogx
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hcase.1.one_lt.le)
      have hsq : u ^ 2 ≤ Real.log (x / p) ^ 2 := by nlinarith [hu, hlogx]
      have hden1 : (0 : ℝ) < (p : ℝ) * Real.log (x / p) ^ 2 := mul_pos hp0 (pow_pos hlogpos 2)
      have hden2 : (0 : ℝ) < (p : ℝ) * u ^ 2 := mul_pos hp0 (pow_pos hu 2)
      rw [div_div, div_le_div_iff₀ hden1 hden2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hp0.le) hlogp
    · rw [if_neg hcase, if_neg hcase, zero_div]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  -- the damped sum is exactly the shell mass
  have hMeq : ∀ n : ℕ, mertensPrimeWeightSum n
      = ∑ p ∈ Finset.Icc 1 n, (if p.Prime then Real.log p / (p : ℝ) else 0) := by
    intro n
    rw [mertensPrimeWeightSum_eq, Finset.sum_filter]
  have hsub : Finset.Icc 1 ⌊x * Real.exp (-v)⌋₊ ⊆ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor hAB)
  have hstep : ∀ p ∈ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊,
      (if p.Prime ∧ x * Real.exp (-v) < (p : ℝ) then Real.log p / (p : ℝ) else 0)
        = (if ⌊x * Real.exp (-v)⌋₊ < p then
            (if p.Prime then Real.log p / (p : ℝ) else 0) else 0) := by
    intro p _
    have hiff : ⌊x * Real.exp (-v)⌋₊ < p ↔ x * Real.exp (-v) < (p : ℝ) := Nat.floor_lt hA0
    by_cases hp : p.Prime
    · by_cases hlt : x * Real.exp (-v) < (p : ℝ)
      · rw [if_pos ⟨hp, hlt⟩, if_pos (hiff.mpr hlt), if_pos hp]
      · rw [if_neg fun h => hlt h.2, if_neg fun h => hlt (hiff.mp h)]
    · by_cases hlt : x * Real.exp (-v) < (p : ℝ)
      · rw [if_neg fun h => hp h.1, if_pos (hiff.mpr hlt), if_neg hp]
      · rw [if_neg fun h => hp h.1, if_neg fun h => hlt (hiff.mp h)]
  have hset : {p ∈ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊ | ⌊x * Real.exp (-v)⌋₊ < p}
      = Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊ \ Finset.Icc 1 ⌊x * Real.exp (-v)⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hwindow : ∑ p ∈ Finset.Icc 1 ⌊x * Real.exp (-u)⌋₊,
      (if p.Prime ∧ x * Real.exp (-v) < (p : ℝ) then Real.log p / (p : ℝ) else 0)
      = primeLogWindowMass (x * Real.exp (-v)) (x * Real.exp (-u)) := by
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, hset, primeLogWindowMass, hMeq, hMeq,
      ← Finset.sum_sdiff hsub]
    ring
  rw [hwindow]
  exact div_le_div_of_nonneg_right (by linarith [hmass.2]) (by positivity)

end

end RHTower
