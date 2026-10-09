import GaloisForLFunctions.RHTower.RiemannSiegelLeeYangChain

/-!
# The quarter-turn zero count for Lee–Yang chains

For the Lee–Yang chain of `RiemannSiegelLeeYangChain` with exponential fields
`u_k = e^{−i λ_k t}` on the real line and real fugacities `|c_k| < 1`, the partition function has
an explicit continuous phase:

* **Conjugate gauge** (`chainPair_snd_eq`): `B_k = e^{−i r_k t} conj A_k`, `r_k = Σ_{j ≤ k} λ_j`.
  With `a_k = e^{i r_k t/2} A_k` one has `Z_N = e^{−i r_N t/2}(a_N + conj a_N)`
  (`chainZ_eq_gauge`) and `a_{k+1} = e^{i λ_{k+1} t/2}(a_k + c_k conj a_k)` (`gaugeA_succ`).
* **Polar form** (`exists_gaugeA_polar`): `a_k = ρ_k e^{i ψ_k}`, `ρ_k > 0`, where
  `ψ_0 = λ_0 t/2` and `ψ_{k+1} = λ_{k+1} t/2 + ψ_k + arg (1 + c_k e^{−2iψ_k})`.
* **Quarter-turn invariance** (`floor_mul_le_phaseStep`): the Möbius step `ψ ↦ ψ + arg(1 + c e^{−2iψ})`
  never decreases the number `⌊2ψ/π⌋` of completed quarter turns.  Hence
  `Σ_{k ≤ N} ⌊λ_k t/π⌋ ≤ ⌊2ψ_N(t)/π⌋` (`sum_floor_le_floor_chainPhase`).
* **Zero count** (`exists_chainZ_zeros`): every `j` with `2j + 1 ≤ Σ_k ⌊λ_k T/π⌋` gives a zero of
  `t ↦ Z_N(t)` in `(0, T]` with phase exactly `π/2 + jπ`; distinct `j` give distinct zeros.
* **Closed fugacities** (`exists_chainZ_eq_zero_Icc`): for `|c_k| ≤ 1` and nonnegative frequencies,
  the partition function vanishes somewhere in `[0, π/λ_k]` for every `k ≤ N` with `λ_k > 0`.

The couplings act by Möbius maps fixing the two phases `0` and `π`, so they can delay a
quarter turn but never undo one: every site of frequency `λ` forces its own zeros below
`π/λ`, whatever the couplings.
-/

open Complex Finset Set Filter Topology

namespace RHTower.LeeYangChain

noncomputable section

/-! ## Fields on the real line and the conjugate gauge -/

/-- Exponential fields at a real point `t`. -/
abbrev lineField (freqs : ℕ → ℝ) (t : ℝ) : ℕ → ℂ := chainExpField freqs (t : ℂ)

/-- Cumulative frequency `r_k = Σ_{j ≤ k} λ_j`. -/
def cumFreq (freqs : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), freqs j

theorem cumFreq_zero (freqs : ℕ → ℝ) : cumFreq freqs 0 = freqs 0 := by
  simp [cumFreq]

theorem cumFreq_succ (freqs : ℕ → ℝ) (k : ℕ) :
    cumFreq freqs (k + 1) = cumFreq freqs k + freqs (k + 1) := by
  rw [cumFreq, sum_range_succ, ← cumFreq]

theorem lineField_eq (freqs : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    lineField freqs t k = cexp (((-(freqs k * t) : ℝ) : ℂ) * I) := by
  rw [lineField, chainExpField]
  congr 1
  push_cast
  ring

theorem conj_cexp_real_mul_I (x : ℝ) :
    (starRingEnd ℂ) (cexp ((x : ℂ) * I)) = cexp (((-x : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem cexp_real_mul_I_mul (x y : ℝ) :
    cexp ((x : ℂ) * I) * cexp ((y : ℂ) * I) = cexp (((x + y : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Conjugate gauge.**  On the real line `B_k = e^{−i r_k t} conj A_k`. -/
theorem chainPair_snd_eq (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    (chainPair c (lineField freqs t) k).2 =
      cexp (((-(cumFreq freqs k * t)) : ℝ) * I) *
        (starRingEnd ℂ) (chainPair c (lineField freqs t) k).1 := by
  induction k with
  | zero =>
    simp only [chainPair, map_one, mul_one, cumFreq_zero]
    exact lineField_eq freqs t 0
  | succ k ih =>
    simp only [chainPair]
    rw [ih, lineField_eq, map_add, map_mul, map_mul, Complex.conj_ofReal,
      conj_cexp_real_mul_I, Complex.conj_conj, cumFreq_succ]
    have h1 : cexp ((((-(freqs (k + 1) * t)) : ℝ) : ℂ) * I) *
        cexp ((((-(cumFreq freqs k * t)) : ℝ) : ℂ) * I) =
        cexp ((((-((cumFreq freqs k + freqs (k + 1)) * t)) : ℝ) : ℂ) * I) := by
      rw [cexp_real_mul_I_mul]
      congr 3
      ring
    have h3 : cexp ((((-(cumFreq freqs k * t)) : ℝ) : ℂ) * I) *
        cexp (((-(-(cumFreq freqs k * t)) : ℝ) : ℂ) * I) = 1 := by
      rw [cexp_real_mul_I_mul]
      simp
    linear_combination ((starRingEnd ℂ) (chainPair c (lineField freqs t) k).1 +
        (c k : ℂ) * (chainPair c (lineField freqs t) k).1 *
          cexp (((-(-(cumFreq freqs k * t)) : ℝ) : ℂ) * I)) * h1 -
      ((c k : ℂ) * (chainPair c (lineField freqs t) k).1 *
        cexp ((((-(freqs (k + 1) * t)) : ℝ) : ℂ) * I)) * h3

/-- The gauged weight `a_k = e^{i r_k t/2} A_k`. -/
def gaugeA (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  cexp (((cumFreq freqs k * t / 2 : ℝ) : ℂ) * I) * (chainPair c (lineField freqs t) k).1

theorem gaugeA_zero (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) :
    gaugeA c freqs t 0 = cexp (((freqs 0 * t / 2 : ℝ) : ℂ) * I) := by
  simp [gaugeA, chainPair, cumFreq_zero]

/-- **Partition function in the gauge.** `Z_N = e^{−i r_N t/2} (a_N + conj a_N)`. -/
theorem chainZ_eq_gauge (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    chainZ c (lineField freqs t) N =
      cexp (((-(cumFreq freqs N * t / 2)) : ℝ) * I) *
        (gaugeA c freqs t N + (starRingEnd ℂ) (gaugeA c freqs t N)) := by
  rw [chainZ, chainPair_snd_eq, gaugeA, map_mul, conj_cexp_real_mul_I, mul_add, ← mul_assoc,
    ← mul_assoc, cexp_real_mul_I_mul, cexp_real_mul_I_mul]
  have e1 : ((-(cumFreq freqs N * t / 2) + cumFreq freqs N * t / 2 : ℝ) : ℂ) = 0 := by
    push_cast; ring
  have e2 : (-(cumFreq freqs N * t / 2) + -(cumFreq freqs N * t / 2) : ℝ) =
      -(cumFreq freqs N * t) := by ring
  rw [e1, e2, zero_mul, Complex.exp_zero, one_mul]

/-- **Gauged recursion.** `a_{k+1} = e^{i λ_{k+1} t/2} (a_k + c_k conj a_k)`. -/
theorem gaugeA_succ (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    gaugeA c freqs t (k + 1) =
      cexp (((freqs (k + 1) * t / 2 : ℝ) : ℂ) * I) *
        (gaugeA c freqs t k + (c k : ℂ) * (starRingEnd ℂ) (gaugeA c freqs t k)) := by
  rw [gaugeA, gaugeA]
  simp only [chainPair]
  rw [chainPair_snd_eq, map_mul, conj_cexp_real_mul_I, cumFreq_succ]
  have e1 : cexp (((freqs (k + 1) * t / 2 : ℝ) : ℂ) * I) *
      cexp (((cumFreq freqs k * t / 2 : ℝ) : ℂ) * I) =
      cexp ((((cumFreq freqs k + freqs (k + 1)) * t / 2 : ℝ) : ℂ) * I) := by
    rw [cexp_real_mul_I_mul]
    congr 3
    ring
  have e2 : cexp ((((cumFreq freqs k + freqs (k + 1)) * t / 2 : ℝ) : ℂ) * I) *
      cexp ((((-(cumFreq freqs k * t)) : ℝ) : ℂ) * I) =
      cexp (((freqs (k + 1) * t / 2 : ℝ) : ℂ) * I) *
        cexp (((-(cumFreq freqs k * t / 2) : ℝ) : ℂ) * I) := by
    rw [cexp_real_mul_I_mul, cexp_real_mul_I_mul]
    congr 3
    ring
  linear_combination (-(chainPair c (lineField freqs t) k).1) * e1 +
    ((c k : ℂ) * (starRingEnd ℂ) (chainPair c (lineField freqs t) k).1) * e2

/-! ## The explicit phase -/

/-- The Möbius phase step `ψ ↦ ψ + arg (1 + c e^{−2iψ})`. -/
def phaseStep (c ψ : ℝ) : ℝ := ψ + Complex.arg (1 + (c : ℂ) * cexp (((-2 * ψ : ℝ) : ℂ) * I))

/-- The chain phase `ψ_k(t)`. -/
def chainPhase (c : ℕ → ℝ) (freqs : ℕ → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => freqs 0 * t / 2
  | k + 1 => freqs (k + 1) * t / 2 + phaseStep (c k) (chainPhase c freqs t k)

theorem re_one_add_mul_cexp_pos {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    0 < (1 + (c : ℂ) * cexp ((x : ℂ) * I)).re := by
  have hre : (1 + (c : ℂ) * cexp ((x : ℂ) * I)).re = 1 + c * Real.cos x := by
    simp [Complex.exp_ofReal_mul_I_re]
  rw [hre]
  have h1 : |c * Real.cos x| ≤ |c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_cos_le_one x)
  have h2 := neg_abs_le (c * Real.cos x)
  linarith

theorem one_add_mul_cexp_ne_zero {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    1 + (c : ℂ) * cexp ((x : ℂ) * I) ≠ 0 := by
  intro h
  have := re_one_add_mul_cexp_pos hc x
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **Polar form of the gauged weight.** -/
theorem exists_gaugeA_polar {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ gaugeA c freqs t k = (ρ : ℂ) * cexp ((chainPhase c freqs t k : ℂ) * I) := by
  induction k with
  | zero => exact ⟨1, one_pos, by rw [gaugeA_zero, chainPhase]; push_cast; ring_nf⟩
  | succ k ih =>
    obtain ⟨ρ, hρ, hk⟩ := ih
    set ψ := chainPhase c freqs t k with hψ
    set w : ℂ := 1 + (c k : ℂ) * cexp (((-2 * ψ : ℝ) : ℂ) * I) with hw
    have hw0 : w ≠ 0 := one_add_mul_cexp_ne_zero (hc k) _
    refine ⟨ρ * ‖w‖, mul_pos hρ (norm_pos_iff.mpr hw0), ?_⟩
    have hpolar : (‖w‖ : ℂ) * cexp ((Complex.arg w : ℂ) * I) = w := Complex.norm_mul_exp_arg_mul_I w
    have hconj : (starRingEnd ℂ) ((ρ : ℂ) * cexp ((ψ : ℂ) * I)) =
        (ρ : ℂ) * cexp (((-ψ : ℝ) : ℂ) * I) := by
      rw [map_mul, Complex.conj_ofReal, conj_cexp_real_mul_I]
    have hsplit : cexp (((-ψ : ℝ) : ℂ) * I) =
        cexp ((ψ : ℂ) * I) * cexp (((-2 * ψ : ℝ) : ℂ) * I) := by
      rw [cexp_real_mul_I_mul]; congr 3; ring
    have hfactor : (ρ : ℂ) * cexp ((ψ : ℂ) * I) +
        (c k : ℂ) * ((ρ : ℂ) * (cexp ((ψ : ℂ) * I) * cexp (((-2 * ψ : ℝ) : ℂ) * I))) =
        (ρ : ℂ) * cexp ((ψ : ℂ) * I) * w := by
      rw [hw]; ring
    have hexp : cexp (((freqs (k + 1) * t / 2 : ℝ) : ℂ) * I) * cexp ((ψ : ℂ) * I) *
        cexp ((Complex.arg w : ℂ) * I) =
        cexp (((freqs (k + 1) * t / 2 + (ψ + Complex.arg w) : ℝ) : ℂ) * I) := by
      rw [cexp_real_mul_I_mul, cexp_real_mul_I_mul, add_assoc]
    have hstep : chainPhase c freqs t (k + 1) =
        freqs (k + 1) * t / 2 + (ψ + Complex.arg w) := rfl
    rw [gaugeA_succ, hk, hconj, hsplit, hfactor, hstep, ← hexp]
    conv_lhs => rw [← hpolar]
    push_cast
    ring

/-! ## Quarter-turn invariance -/

/-- **Quarter-turn invariance of the Möbius step.**  The step never undoes a completed quarter
turn: `⌊2ψ/π⌋ · π/2 ≤ ψ + arg (1 + c e^{−2iψ})`. -/
theorem floor_mul_le_phaseStep {c : ℝ} (hc : |c| < 1) (ψ : ℝ) :
    (⌊2 * ψ / Real.pi⌋ : ℝ) * (Real.pi / 2) ≤ phaseStep c ψ := by
  have hpi := Real.pi_pos
  set j := ⌊2 * ψ / Real.pi⌋ with hj
  set θ := ψ - (j : ℝ) * (Real.pi / 2) with hθ
  have hθ0 : 0 ≤ θ := by
    have h := Int.floor_le (2 * ψ / Real.pi)
    rw [← hj, le_div_iff₀ hpi] at h
    rw [hθ]; nlinarith
  have hθ1 : θ < Real.pi / 2 := by
    have h := Int.lt_floor_add_one (2 * ψ / Real.pi)
    rw [← hj, div_lt_iff₀ hpi] at h
    rw [hθ]; nlinarith
  set w : ℂ := 1 + (c : ℂ) * cexp (((-2 * ψ : ℝ) : ℂ) * I) with hw
  have hw0 : w ≠ 0 := one_add_mul_cexp_ne_zero hc _
  have hwre : 0 < w.re := re_one_add_mul_cexp_pos hc _
  have harg : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  show (j : ℝ) * (Real.pi / 2) ≤ ψ + Complex.arg w
  by_contra hcon
  have hcon := not_le.mp hcon
  have hneg : Complex.arg w + θ < 0 := by rw [hθ]; linarith
  have hlow : -Real.pi < Complex.arg w + θ := by
    have := (abs_lt.mp harg).1
    linarith [Real.pi_pos]
  -- the imaginary part of `w e^{iθ}` computed two ways
  have him1 : (w * cexp ((θ : ℂ) * I)).im = ‖w‖ * Real.sin (Complex.arg w + θ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_assoc, cexp_real_mul_I_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsinpos : Real.sin (Complex.arg w + θ) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt hneg hlow
  have hlt : (w * cexp ((θ : ℂ) * I)).im < 0 := by
    rw [him1]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw0) hsinpos
  have hψ : -2 * ψ + θ = -θ + (-j : ℤ) * Real.pi := by
    rw [hθ]; push_cast; ring
  have him2 : (w * cexp ((θ : ℂ) * I)).im =
      Real.sin θ + c * Real.sin (-θ + (-j : ℤ) * Real.pi) := by
    rw [hw, add_mul, one_mul, mul_assoc, cexp_real_mul_I_mul, Complex.add_im,
      Complex.exp_ofReal_mul_I_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, hψ]
  have hsin : Real.sin (-θ + (-j : ℤ) * Real.pi) = (-1) ^ (-j) * Real.sin (-θ) :=
    Real.sin_add_int_mul_pi (-θ) (-j)
  have hsinθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hbound : |c * Real.sin (-θ + (-j : ℤ) * Real.pi)| ≤ |c| * Real.sin θ := by
    rw [hsin, abs_mul, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul, Real.sin_neg,
      abs_neg, abs_of_nonneg hsinθ]
  have hge : 0 ≤ (w * cexp ((θ : ℂ) * I)).im := by
    rw [him2]
    have := neg_abs_le (c * Real.sin (-θ + (-j : ℤ) * Real.pi))
    nlinarith [abs_nonneg c]
  linarith

/-- **Quarter-turn count.**  `Σ_{j ≤ k} ⌊λ_j t/π⌋ ≤ ⌊2ψ_k(t)/π⌋`. -/
theorem sum_floor_le_floor_chainPhase {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ)
    (t : ℝ) (k : ℕ) :
    ∑ j ∈ range (k + 1), ⌊freqs j * t / Real.pi⌋ ≤ ⌊2 * chainPhase c freqs t k / Real.pi⌋ := by
  have hpi := Real.pi_pos
  induction k with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, chainPhase]
    apply le_of_eq
    congr 1
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hstep := floor_mul_le_phaseStep (hc k) (chainPhase c freqs t k)
    have hfl : ⌊2 * chainPhase c freqs t k / Real.pi⌋ ≤
        ⌊2 * phaseStep (c k) (chainPhase c freqs t k) / Real.pi⌋ := by
      apply Int.le_floor.mpr
      rw [le_div_iff₀ hpi]
      nlinarith
    have hsplit : 2 * chainPhase c freqs t (k + 1) / Real.pi =
        freqs (k + 1) * t / Real.pi + 2 * phaseStep (c k) (chainPhase c freqs t k) / Real.pi := by
      simp only [chainPhase]
      ring
    rw [hsplit]
    calc ∑ j ∈ range (k + 1), ⌊freqs j * t / Real.pi⌋ + ⌊freqs (k + 1) * t / Real.pi⌋
        ≤ ⌊2 * phaseStep (c k) (chainPhase c freqs t k) / Real.pi⌋ +
            ⌊freqs (k + 1) * t / Real.pi⌋ := by linarith
      _ ≤ _ := by
          rw [add_comm (⌊2 * phaseStep (c k) (chainPhase c freqs t k) / Real.pi⌋)]
          exact Int.le_floor_add _ _

/-! ## Continuity and the value at the origin -/

theorem continuous_phaseStep {c : ℝ} (hc : |c| < 1) : Continuous (phaseStep c) := by
  unfold phaseStep
  refine continuous_id.add (continuous_iff_continuousAt.mpr fun ψ => ?_)
  have hslit : (1 + (c : ℂ) * cexp (((-2 * ψ : ℝ) : ℂ) * I)) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_add_mul_cexp_pos hc _))
  exact (Complex.continuousAt_arg hslit).comp
    (f := fun ψ : ℝ => 1 + (c : ℂ) * cexp (((-2 * ψ : ℝ) : ℂ) * I)) (by fun_prop)

theorem continuous_chainPhase {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ) (k : ℕ) :
    Continuous fun t => chainPhase c freqs t k := by
  induction k with
  | zero => exact (continuous_const.mul continuous_id).div_const 2
  | succ k ih =>
    exact ((continuous_const.mul continuous_id).div_const 2).add
      ((continuous_phaseStep (hc k)).comp ih)

theorem phaseStep_zero {c : ℝ} (hc : |c| < 1) : phaseStep c 0 = 0 := by
  have h1 : (0 : ℝ) ≤ 1 + c := by linarith [neg_abs_le c]
  simp only [phaseStep, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    zero_add]
  have : (1 + (c : ℂ)) = ((1 + c : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.arg_ofReal_of_nonneg h1]

theorem chainPhase_at_zero {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ) (k : ℕ) :
    chainPhase c freqs 0 k = 0 := by
  induction k with
  | zero => simp [chainPhase]
  | succ k ih => simp only [chainPhase, ih, phaseStep_zero (hc k), mul_zero, zero_div, add_zero]

/-! ## Zeros from the phase -/

/-- A quarter-turn phase `cos ψ_N = 0` is a zero of the partition function. -/
theorem chainZ_eq_zero_of_cos_eq_zero {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ)
    {t : ℝ} {N : ℕ} (h : Real.cos (chainPhase c freqs t N) = 0) :
    chainZ c (lineField freqs t) N = 0 := by
  obtain ⟨ρ, -, hpol⟩ := exists_gaugeA_polar hc freqs t N
  rw [chainZ_eq_gauge, hpol, map_mul, Complex.conj_ofReal, conj_cexp_real_mul_I]
  have hsum : (ρ : ℂ) * cexp ((chainPhase c freqs t N : ℂ) * I) +
      (ρ : ℂ) * cexp (((-chainPhase c freqs t N : ℝ) : ℂ) * I) =
      ((2 * ρ * Real.cos (chainPhase c freqs t N) : ℝ) : ℂ) := by
    have e : ∀ x : ℝ, cexp ((x : ℂ) * I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := fun x => by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [e, e, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hsum, h, mul_zero, Complex.ofReal_zero, mul_zero]

/-- **Zero at every reached quarter-turn level.** -/
theorem exists_chainZ_zero_at_level {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (N j : ℕ)
    (hj : (2 * (j : ℤ) + 1) ≤ ∑ i ∈ range (N + 1), ⌊freqs i * T / Real.pi⌋) :
    ∃ t ∈ Ioc 0 T, chainPhase c freqs t N = Real.pi / 2 + j * Real.pi ∧
      chainZ c (lineField freqs t) N = 0 := by
  have hpi := Real.pi_pos
  have hfl := (hj.trans (sum_floor_le_floor_chainPhase hc freqs T N))
  have hreach : Real.pi / 2 + j * Real.pi ≤ chainPhase c freqs T N := by
    have h1 : ((2 * (j : ℤ) + 1 : ℤ) : ℝ) ≤ 2 * chainPhase c freqs T N / Real.pi :=
      (Int.cast_le.mpr hfl).trans (Int.floor_le _)
    push_cast at h1
    rw [le_div_iff₀ hpi] at h1
    nlinarith
  have hcont := (continuous_chainPhase hc freqs N).continuousOn (s := Icc 0 T)
  have hmem : Real.pi / 2 + j * Real.pi ∈
      Icc (chainPhase c freqs 0 N) (chainPhase c freqs T N) := by
    rw [chainPhase_at_zero hc]
    exact ⟨by positivity, hreach⟩
  obtain ⟨t, ⟨ht0, htT⟩, hval⟩ := intermediate_value_Icc hT hcont hmem
  simp only at hval
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · subst h
      rw [chainPhase_at_zero hc] at hval
      have : (0 : ℝ) < Real.pi / 2 + j * Real.pi := by positivity
      linarith
  refine ⟨t, ⟨htpos, htT⟩, hval, chainZ_eq_zero_of_cos_eq_zero hc freqs ?_⟩
  rw [hval]
  have : Real.pi / 2 + (j : ℝ) * Real.pi = Real.pi / 2 + ((j : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [this, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]

/-- **The quarter-turn zero count.**  With `S = Σ_{i ≤ N} ⌊λ_i T/π⌋`, the partition function has at
least `M` distinct zeros in `(0, T]` for every `M` with `2M ≤ S + 1`. -/
theorem exists_chainZ_zeros {c : ℕ → ℝ} (hc : ∀ k, |c k| < 1) (freqs : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (N M : ℕ)
    (hM : 2 * (M : ℤ) ≤ ∑ i ∈ range (N + 1), ⌊freqs i * T / Real.pi⌋ + 1) :
    ∃ f : Fin M → ℝ, Function.Injective f ∧
      ∀ j, f j ∈ Ioc 0 T ∧ chainZ c (lineField freqs (f j)) N = 0 := by
  have hlev : ∀ j : Fin M, ∃ t ∈ Ioc 0 T,
      chainPhase c freqs t N = Real.pi / 2 + (j : ℕ) * Real.pi ∧
        chainZ c (lineField freqs t) N = 0 := fun j =>
    exists_chainZ_zero_at_level hc freqs hT N j (by have := j.isLt; omega)
  choose f hfmem hfphase hfzero using hlev
  refine ⟨f, fun a b hab => ?_, fun j => ⟨hfmem j, hfzero j⟩⟩
  have h := (hfphase a).symm.trans ((congrArg (fun t => chainPhase c freqs t N) hab).trans
    (hfphase b))
  have hpi := Real.pi_pos
  have : ((a : ℕ) : ℝ) = (b : ℕ) := by
    have h' : (a : ℕ) * Real.pi = (b : ℕ) * Real.pi := by linarith
    exact mul_right_cancel₀ hpi.ne' h'
  exact Fin.ext (by exact_mod_cast this)

/-! ## Closed fugacities by compactness -/

theorem continuous_chainPair_scaled (c : ℕ → ℝ) (freqs : ℕ → ℝ) (k : ℕ) :
    Continuous fun p : ℝ × ℝ => chainPair (fun i => p.1 * c i) (lineField freqs p.2) k := by
  have hu : ∀ i, Continuous fun p : ℝ × ℝ => lineField freqs p.2 i := fun i => by
    simp only [lineField, chainExpField]
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)).neg
  have hcs : ∀ i, Continuous fun p : ℝ × ℝ => (((p.1 * c i : ℝ)) : ℂ) := fun i =>
    Complex.continuous_ofReal.comp (continuous_fst.mul continuous_const)
  induction k with
  | zero => exact continuous_const.prodMk (hu 0)
  | succ k ih =>
    exact (ih.fst.add ((hcs k).mul ih.snd)).prodMk
      ((hu (k + 1)).mul (((hcs k).mul ih.fst).add ih.snd))

/-- **A zero below `π/λ` for closed fugacities.**  For `|c_k| ≤ 1` and nonnegative frequencies,
every site `k₀ ≤ N` of positive frequency forces a real zero of the partition function in
`[0, π/λ_{k₀}]`. -/
theorem exists_chainZ_eq_zero_Icc {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1) {freqs : ℕ → ℝ}
    (hfreq : ∀ k, 0 ≤ freqs k) {N k₀ : ℕ} (hk₀ : k₀ ≤ N) (hpos : 0 < freqs k₀) :
    ∃ t ∈ Icc 0 (Real.pi / freqs k₀), chainZ c (lineField freqs t) N = 0 := by
  have hpi := Real.pi_pos
  set T := Real.pi / freqs k₀ with hTdef
  have hT : 0 ≤ T := by positivity
  -- the count is at least one at `T`
  have hS : (1 : ℤ) ≤ ∑ i ∈ range (N + 1), ⌊freqs i * T / Real.pi⌋ := by
    have hk : freqs k₀ * T / Real.pi = 1 := by rw [hTdef]; field_simp
    have hterm : ⌊freqs k₀ * T / Real.pi⌋ = 1 := by rw [hk]; simp
    have hnn : ∀ i ∈ range (N + 1), 0 ≤ ⌊freqs i * T / Real.pi⌋ := fun i _ =>
      Int.floor_nonneg.mpr (by have := hfreq i; positivity)
    rw [← hterm]
    exact single_le_sum hnn (mem_range.mpr (by omega))
  -- scaled fugacities `s_n c` with `s_n = 1 - 1/(n+2)`
  set s : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hsdef
  have hs_abs : ∀ n k, |s n * c k| < 1 := fun n k => by
    have hs0 : 0 ≤ s n := by
      simp only [hsdef]
      have : 1 / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hs1 : s n < 1 := by
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      simp only [hsdef]
      linarith
    rw [abs_mul, abs_of_nonneg hs0]
    calc s n * |c k| ≤ s n * 1 := mul_le_mul_of_nonneg_left (hc k) hs0
      _ < 1 := by linarith
  have hzero : ∀ n, ∃ t ∈ Icc 0 T,
      chainZ (fun i => s n * c i) (lineField freqs t) N = 0 := fun n => by
    obtain ⟨t, ht, -, hz⟩ := exists_chainZ_zero_at_level (c := fun i => s n * c i)
      (fun k => hs_abs n k) freqs hT N 0 (by simpa using hS)
    exact ⟨t, Ioc_subset_Icc_self ht, hz⟩
  choose tn htn hzn using hzero
  obtain ⟨t, htmem, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).tendsto_subseq htn
  have hs_lim : Tendsto s atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    have h' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine h.congr fun n => ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa [hsdef] using (tendsto_const_nhds (x := (1 : ℝ))).sub h'
  have hpair : Tendsto (fun n => (s (φ n), tn (φ n))) atTop (𝓝 (1, t)) :=
    (hs_lim.comp hφ.tendsto_atTop).prodMk_nhds hlim
  have hcontZ : Continuous fun p : ℝ × ℝ =>
      chainZ (fun i => p.1 * c i) (lineField freqs p.2) N := by
    have h := continuous_chainPair_scaled c freqs N
    exact h.fst.add h.snd
  have hlimZ := (hcontZ.tendsto (1, t)).comp hpair
  have hval : chainZ (fun i => (1 : ℝ) * c i) (lineField freqs t) N = 0 := by
    refine tendsto_nhds_unique hlimZ ?_
    exact tendsto_const_nhds.congr fun n => (hzn (φ n)).symm
  refine ⟨t, htmem, ?_⟩
  simpa only [one_mul] using hval

end

end RHTower.LeeYangChain
