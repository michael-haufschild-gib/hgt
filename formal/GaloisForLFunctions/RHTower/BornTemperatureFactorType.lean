import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Born temperature and the Bost–Connes factor-type selector

The wavefunction with amplitudes `n ^ (-s)` on the integer basis assigns the basis state `n`
the Born weight `‖(n : ℂ) ^ (-s)‖ ^ 2 = n ^ (-2 Re s)`.  The Gibbs weight of `n` at inverse
temperature `β` for the multiplicative Hamiltonian with eigenvalue `log n` is
`exp (-β log n) = n ^ (-β)`.  Matching the two — even only projectively, allowing an overall
normalization — forces `β = 2 Re s`: the factor `2` is the Born rule converting an amplitude
exponent into a probability exponent, not a chosen rescaling.  Multiplying every amplitude by
one fixed nonzero scalar (the archimedean `Γ`-completion at fixed `s`) changes no Born datum,
so the completion is invisible to this temperature.

Functional-equation–Schwarz reflection `s ↦ 1 - conj s` sends the Born temperature to
`2 - β`, a reflection of the temperature axis with unique fixed point `β = 1`.  Any labelling
of temperatures that is constant with one value on `0 < β ≤ 1` and constant with a different
value on `1 < β` — the Bost–Connes phase diagram assigns type `III₁` to the first range
(unique KMS state) and type `I` to the second (extremal Gibbs sectors) — therefore matches
the reflected pair `(β, 2 - β)` with `0 < β < 2` exactly at `β = 1`.  Since every `xi` zero
lies in the open critical strip, its Born temperature lies in `(0, 2)`, and the Riemann
hypothesis is equivalent to the reflected labels agreeing at every zero.

The label match at `s` is in turn equivalent to the reflection already fixing `s`.  Hence a
normal equivalence of the two reflected sectors either is excluded by the label mismatch or
is the identity of a single sector: the reflected-sector duality carries no content beyond
the location of the zeros, and its existence at every zero restates the Riemann hypothesis.
The von Neumann classification enters only as the stated hypothesis on a label function.
-/

noncomputable section

namespace RHTower

/-! ## Born and Gibbs weights on the integer basis -/

/-- The Born weight of the integer basis state `n` in the wavefunction with amplitudes
`n ^ (-s)`: the squared modulus of the amplitude. -/
def bornWeight (s : ℂ) (n : ℕ) : ℝ := ‖(n : ℂ) ^ (-s)‖ ^ 2

/-- The Gibbs weight of the state `n` at inverse temperature `β` for the multiplicative
Hamiltonian with eigenvalue `log n` on the basis state `n`. -/
def gibbsWeight (β : ℝ) (n : ℕ) : ℝ := Real.exp (-β * Real.log n)

theorem bornWeight_eq_rpow {s : ℂ} {n : ℕ} (hn : 0 < n) :
    bornWeight s n = (n : ℝ) ^ (-(2 * s.re)) := by
  unfold bornWeight
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re,
    ← Real.rpow_natCast ((n : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  push_cast
  ring

theorem gibbsWeight_eq_rpow {β : ℝ} {n : ℕ} (hn : 0 < n) :
    gibbsWeight β n = (n : ℝ) ^ (-β) := by
  unfold gibbsWeight
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]
  congr 1
  ring

/-- **The Born rule forces the inverse temperature.**  The Born weights of the wavefunction
at `s` agree with the Gibbs weights at inverse temperature `β` on every occupied level iff
`β = 2 Re s`. -/
theorem bornWeight_eq_gibbsWeight_iff (s : ℂ) (β : ℝ) :
    (∀ n : ℕ, 0 < n → bornWeight s n = gibbsWeight β n) ↔ β = 2 * s.re := by
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    rw [bornWeight_eq_rpow (by norm_num), gibbsWeight_eq_rpow (by norm_num)] at h2
    push_cast at h2
    have hlog := congrArg Real.log h2
    rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
    have hln2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have := mul_right_cancel₀ hln2 hlog
    linarith
  · rintro rfl
    intro n hn
    rw [bornWeight_eq_rpow hn, gibbsWeight_eq_rpow hn]

/-- Even projectively — allowing an overall normalization `c > 0` — the Gibbs comparison
pins the same temperature, and the constant is then `1`. -/
theorem bornWeight_propto_gibbsWeight_iff (s : ℂ) (β : ℝ) :
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → bornWeight s n = c * gibbsWeight β n) ↔
      β = 2 * s.re := by
  constructor
  · rintro ⟨c, _, h⟩
    have hb1 : bornWeight s 1 = 1 := by simp [bornWeight]
    have hg1 : gibbsWeight β 1 = 1 := by simp [gibbsWeight]
    have h1 := h 1 (by norm_num)
    rw [hb1, hg1, mul_one] at h1
    apply (bornWeight_eq_gibbsWeight_iff s β).1
    intro n hn
    rw [h n hn, ← h1, one_mul]
  · intro hβ
    exact ⟨1, one_pos, fun n hn => by
      rw [one_mul]
      exact (bornWeight_eq_gibbsWeight_iff s β).2 hβ n hn⟩

/-- Multiplying every amplitude by one fixed nonzero scalar — the effect of the archimedean
`Γ`-completion at fixed `s` — changes no Born datum: the projective Gibbs comparison still
pins `β = 2 Re s`.  The completed constraint is invisible to the Born temperature. -/
theorem scaled_bornWeight_propto_gibbsWeight_iff (c : ℂ) (hc : c ≠ 0) (s : ℂ) (β : ℝ) :
    (∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 0 < n → ‖c * (n : ℂ) ^ (-s)‖ ^ 2 = d * gibbsWeight β n) ↔
      β = 2 * s.re := by
  have hkey : ∀ n : ℕ, ‖c * (n : ℂ) ^ (-s)‖ ^ 2 = ‖c‖ ^ 2 * bornWeight s n := by
    intro n
    unfold bornWeight
    rw [norm_mul, mul_pow]
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  constructor
  · rintro ⟨d, hd, h⟩
    apply (bornWeight_propto_gibbsWeight_iff s β).1
    refine ⟨d / ‖c‖ ^ 2, div_pos hd hc2, fun n hn => ?_⟩
    have hcn := h n hn
    rw [hkey n] at hcn
    rw [div_mul_eq_mul_div, eq_div_iff hc2.ne']
    linear_combination hcn
  · intro hβ
    refine ⟨‖c‖ ^ 2, hc2, fun n hn => ?_⟩
    rw [hkey n, (bornWeight_eq_gibbsWeight_iff s β).2 hβ n hn]

/-! ## The Born temperature, its reflection, and the normalizability wall -/

/-- The Born inverse temperature of the wavefunction at `s`. -/
def bornBeta (s : ℂ) : ℝ := 2 * s.re

/-- Functional-equation–Schwarz reflection reflects the Born temperature about `β = 1`. -/
theorem bornBeta_reflect (s : ℂ) :
    bornBeta (1 - starRingEnd ℂ s) = 2 - bornBeta s := by
  unfold bornBeta
  rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

/-- **Normalizability wall.**  The Born weights are summable iff `Re s > 1/2`. -/
theorem summable_bornWeight_iff (s : ℂ) :
    Summable (fun n : ℕ => bornWeight s n) ↔ 1 / 2 < s.re := by
  constructor
  · intro h
    have h1 : Summable fun n : ℕ => bornWeight s (n + 1) :=
      (summable_nat_add_iff (f := fun n : ℕ => bornWeight s n) 1).2 h
    have h1' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      h1.congr fun n => bornWeight_eq_rpow n.succ_pos
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * s.re)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(2 * s.re))) 1).1 h1'
    have := Real.summable_nat_rpow.1 h2
    linarith
  · intro h
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * s.re)) :=
      Real.summable_nat_rpow.2 (by linarith)
    have h1' : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(2 * s.re)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(2 * s.re))) 1).2 h2
    have h1 : Summable fun n : ℕ => bornWeight s (n + 1) :=
      h1'.congr fun n => (bornWeight_eq_rpow n.succ_pos).symm
    exact (summable_nat_add_iff (f := fun n : ℕ => bornWeight s n) 1).1 h1

/-- The wavefunction is normalizable exactly in the low-temperature phase of its Born
temperature: `Σ ‖n^{-s}‖²` converges iff `β = 2 Re s > 1`.  The normalizability wall, the
Gibbs-existence wall, and the phase-transition temperature coincide under the Born rule. -/
theorem summable_bornWeight_iff_one_lt_bornBeta (s : ℂ) :
    Summable (fun n : ℕ => bornWeight s n) ↔ 1 < bornBeta s := by
  rw [summable_bornWeight_iff]
  unfold bornBeta
  constructor <;> intro <;> linarith

/-! ## The factor-type selector -/

/-- The reflected pair `(β, 2 - β)` lies in the same Bost–Connes phase: both in the
high-temperature/critical range `β ≤ 1`, or both in the low-temperature range `β > 1`. -/
def ReflectedPhaseMatch (β : ℝ) : Prop := β ≤ 1 ↔ 2 - β ≤ 1

/-- The reflected phases match exactly at the transition temperature. -/
theorem reflectedPhaseMatch_iff (β : ℝ) : ReflectedPhaseMatch β ↔ β = 1 := by
  unfold ReflectedPhaseMatch
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h.1 hlt.le
      linarith
    · have := h.2 (by linarith)
      linarith
  · rintro rfl
    norm_num

/-- Any labelling of temperatures that is constant with one value on the high-temperature
phase `0 < β ≤ 1` and constant with a different value on the low-temperature phase `1 < β` —
the published Bost–Connes classification labels the first `III₁` and the second `I` —
assigns equal labels to a reflected pair `(β, 2 - β)` with `0 < β < 2` exactly at the
transition `β = 1`. -/
theorem factorLabel_reflect_eq_iff {T : Type*} (label : ℝ → T) (tHigh tLow : T)
    (hne : tHigh ≠ tLow)
    (hHigh : ∀ β : ℝ, 0 < β → β ≤ 1 → label β = tHigh)
    (hLow : ∀ β : ℝ, 1 < β → label β = tLow)
    {β : ℝ} (h0 : 0 < β) (h2 : β < 2) :
    label β = label (2 - β) ↔ β = 1 := by
  constructor
  · intro h
    by_contra hne1
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · rw [hHigh β h0 hlt.le, hLow (2 - β) (by linarith)] at h
      exact hne h
    · rw [hLow β hgt, hHigh (2 - β) (by linarith) (by linarith)] at h
      exact hne h.symm
  · rintro rfl
    norm_num

/-! ## Zeros of `xi`, their Born temperatures, and the equivalences -/

/-- Every zero of the completed `xi` lies in the open critical strip. -/
theorem xi_zero_re_mem_open_unit {ρ : ℂ} (hρ : xi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hle
    have h1 : (1 : ℝ) ≤ ((1 : ℂ) - ρ).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    exact xi_ne_zero_of_one_le_re h1 (by rw [xi_one_sub]; exact hρ)
  · by_contra hge
    exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hρ

/-- The Born temperature of every `xi` zero lies in the open temperature strip `(0, 2)`. -/
theorem bornBeta_xi_zero_mem {ρ : ℂ} (hρ : xi ρ = 0) :
    0 < bornBeta ρ ∧ bornBeta ρ < 2 := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hρ
  unfold bornBeta
  constructor <;> linarith

/-- Under RH every `xi` zero lies on the critical line. -/
theorem xi_zero_re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xi ρ = 0) :
    ρ.re = 1 / 2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : (1 : ℂ) - ρ ∈ rightHalf := by
      rw [mem_rightHalf]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact rh_iff_xi_ne_zero_right.mp hRH _ hmem (by rw [xi_one_sub]; exact hρ)
  · exact rh_iff_xi_ne_zero_right.mp hRH ρ (mem_rightHalf.mpr hgt) hρ

/-- **RH as reflected-phase matching.**  RH holds iff at every `xi` zero the Born
temperature and its functional-equation reflection lie in the same Bost–Connes phase. -/
theorem riemannHypothesis_iff_xiZero_reflectedPhaseMatch :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → ReflectedPhaseMatch (bornBeta ρ) := by
  constructor
  · intro hRH ρ hρ
    rw [reflectedPhaseMatch_iff]
    unfold bornBeta
    rw [xi_zero_re_eq_half_of_RH hRH hρ]
    norm_num
  · intro hmatch
    apply rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ h0
    have h := (reflectedPhaseMatch_iff _).1 (hmatch ρ h0)
    unfold bornBeta at h
    have := mem_rightHalf.mp hρ
    linarith

/-- **RH as factor-type matching.**  For any labelling obeying the Bost–Connes phase
diagram, RH holds iff at every `xi` zero the labels at the Born temperature and at its
functional-equation reflection agree. -/
theorem riemannHypothesis_iff_xiZero_factorLabel_match {T : Type*} (label : ℝ → T)
    (tHigh tLow : T) (hne : tHigh ≠ tLow)
    (hHigh : ∀ β : ℝ, 0 < β → β ≤ 1 → label β = tHigh)
    (hLow : ∀ β : ℝ, 1 < β → label β = tLow) :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, xi ρ = 0 → label (bornBeta ρ) = label (2 - bornBeta ρ) := by
  constructor
  · intro hRH ρ hρ
    obtain ⟨h0, h2⟩ := bornBeta_xi_zero_mem hρ
    rw [factorLabel_reflect_eq_iff label tHigh tLow hne hHigh hLow h0 h2]
    unfold bornBeta
    rw [xi_zero_re_eq_half_of_RH hRH hρ]
    norm_num
  · intro hmatch
    rw [riemannHypothesis_iff_xiZero_reflectedPhaseMatch]
    intro ρ hρ
    obtain ⟨h0, h2⟩ := bornBeta_xi_zero_mem hρ
    rw [reflectedPhaseMatch_iff]
    exact (factorLabel_reflect_eq_iff label tHigh tLow hne hHigh hLow h0 h2).1
      (hmatch ρ hρ)

/-! ## Collapse of the reflected duality -/

/-- Functional-equation–Schwarz reflection fixes a point exactly on the critical line. -/
theorem fe_reflection_fixed_iff (s : ℂ) :
    1 - starRingEnd ℂ s = s ↔ s.re = 1 / 2 := by
  rw [Complex.ext_iff]
  constructor
  · rintro ⟨hre, _⟩
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    constructor
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, h]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

/-- **Collapse of the reflected duality.**  The necessary phase-match condition holds at `s`
exactly when the functional-equation reflection already fixes `s`, where the change of clock
perspective is the identity.  A normal equivalence of the two reflected sectors is therefore
either excluded by the type mismatch or the identity of a single sector; no intermediate
object exists to construct. -/
theorem reflectedPhaseMatch_iff_reflection_fixed (s : ℂ) :
    ReflectedPhaseMatch (bornBeta s) ↔ 1 - starRingEnd ℂ s = s := by
  rw [reflectedPhaseMatch_iff, fe_reflection_fixed_iff]
  unfold bornBeta
  constructor <;> intro <;> linarith

/-- **RH as pointwise self-duality.**  RH holds iff the functional-equation reflection fixes
every `xi` zero — iff the reflected-sector duality demanded at every zero is everywhere the
identity.  The duality carries no content beyond the location of the zeros. -/
theorem riemannHypothesis_iff_xiZero_reflection_fixed :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → 1 - starRingEnd ℂ ρ = ρ := by
  rw [riemannHypothesis_iff_xiZero_reflectedPhaseMatch]
  exact forall_congr' fun ρ => imp_congr_right fun _ =>
    reflectedPhaseMatch_iff_reflection_fixed ρ

end RHTower
