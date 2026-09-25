import GaloisForLFunctions.RHTower.ZeroNetworkConductance

/-!
# Angular energy quantization

The maximum principle needed attainment because it was a *maximum* principle.  Replace it by an
*energy*.  For two zeros `ρ ≠ ρ'` put

  `cos²θ(ρ,ρ') = (Re ρ − Re ρ')² / |ρ − ρ'|²`,

the squared cosine of the angle the segment `ρ − ρ'` makes with the real axis.  Summing over `ρ'`
gives the **angular energy** of a zero,

  `E(ρ) = Σ_{ρ' ≠ ρ} cos²θ(ρ,ρ')`.

The sum converges for every zero: real parts are confined to a strip, so `cos²θ ≤ 1/|ρ − ρ'|²`, and
the zero network is locally finite.

The content of this module is that `E` is **quantized**.  A zero `ρ` off the critical line is joined
to its functional-equation partner `1 − ρ̄` by a segment that is exactly horizontal, so that single
pair contributes `cos²θ = 1` — *no matter how close `ρ` is to the line*.  The conductance
`1/|ρ − σρ|²` and the squared displacement `(2 Re ρ − 1)²` are reciprocal, and their product is one.
Hence

  `E(ρ) ≥ 1` for every off-line zero,  `E(ρ) = 0` for every zero iff the hypothesis holds.

So `sup E` never lies in the open interval `(0,1)`: either every zero sees every other zero in a
purely vertical direction, or some zero carries a full unit of angular energy.  The hypothesis is
equivalent to the *threshold* `E < 1`, not to an exact equality, and no attainment hypothesis is
used anywhere.

The quantization also explains at the object level why continuity and deformation arguments cannot
reach the hypothesis: the partner term is `1` for every off-line `ρ` and `0` on the line, so the
energy jumps rather than decays as a zero approaches the line.  A family of counterexamples drifting
onto the critical line does not become cheap on the way.
-/

open Complex

namespace RHTower

noncomputable section

/-- The squared cosine of the angle from `ρ_j` to `ρ_k`, and `0` on the diagonal. -/
def angularEnergyTerm (j k : XiDivisorSupport) : ℝ :=
  if k = j then 0
  else ((j : ℂ).re - (k : ℂ).re) ^ (2 : ℕ) / Complex.normSq ((j : ℂ) - (k : ℂ))

/-- The angular energy of a zero: the total squared cosine seen from it. -/
def angularEnergy (j : XiDivisorSupport) : ℝ := ∑' k, angularEnergyTerm j k

theorem angularEnergyTerm_nonneg (j k : XiDivisorSupport) : 0 ≤ angularEnergyTerm j k := by
  rw [angularEnergyTerm]
  split
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

/-- Each term is at most the conductance, because real parts live in a strip of width one. -/
theorem angularEnergyTerm_le_zeroConductance (j k : XiDivisorSupport) :
    angularEnergyTerm j k ≤ zeroConductance j k := by
  rw [angularEnergyTerm]
  split
  · rw [zeroConductance]
    exact div_nonneg zero_le_one (Complex.normSq_nonneg _)
  · have hnum : ((j : ℂ).re - (k : ℂ).re) ^ (2 : ℕ) ≤ 1 := by
      obtain ⟨hj0, hj1⟩ := xiDivisorSupport_re_mem j
      obtain ⟨hk0, hk1⟩ := xiDivisorSupport_re_mem k
      nlinarith
    rw [zeroConductance, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum
      (inv_nonneg.mpr (Complex.normSq_nonneg _))

theorem summable_angularEnergyTerm (j : XiDivisorSupport) :
    Summable (fun k => angularEnergyTerm j k) :=
  Summable.of_nonneg_of_le (angularEnergyTerm_nonneg j)
    (angularEnergyTerm_le_zeroConductance j) (summable_zeroConductance j)

theorem angularEnergy_nonneg (j : XiDivisorSupport) : 0 ≤ angularEnergy j :=
  tsum_nonneg (angularEnergyTerm_nonneg j)

/-- **The quantum.**  The segment from an off-line zero to its functional-equation partner is
horizontal, and the conductance is exactly the reciprocal of the squared displacement.  The
contribution is `1` regardless of the distance to the critical line. -/
theorem angularEnergyTerm_supportPartner {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) :
    angularEnergyTerm ρ (supportPartner ρ) = 1 := by
  have hne : supportPartner ρ ≠ ρ := fun hc => h ((supportPartner_eq_self_iff ρ).mp hc)
  have hd : (2 * (ρ : ℂ).re - 1) ≠ 0 := fun hc => h (by linarith)
  rw [angularEnergyTerm, if_neg hne, supportPartner_re, sub_supportPartner_eq,
    Complex.normSq_ofReal]
  rw [show (ρ : ℂ).re - (1 - (ρ : ℂ).re) = 2 * (ρ : ℂ).re - 1 by ring]
  field_simp

/-- On the critical line the partner term vanishes: the energy jumps, it does not decay. -/
theorem angularEnergyTerm_supportPartner_of_re_eq_half {ρ : XiDivisorSupport}
    (h : (ρ : ℂ).re = 1 / 2) : angularEnergyTerm ρ (supportPartner ρ) = 0 := by
  rw [(supportPartner_eq_self_iff ρ).mpr h, angularEnergyTerm, if_pos rfl]

/-- **Every off-line zero carries at least one unit of angular energy.** -/
theorem one_le_angularEnergy {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) :
    1 ≤ angularEnergy ρ := by
  have hle := (summable_angularEnergyTerm ρ).le_tsum (supportPartner ρ)
    (fun b _ => angularEnergyTerm_nonneg ρ b)
  rwa [angularEnergyTerm_supportPartner h] at hle

theorem angularEnergyTerm_eq_zero_of_angularEnergy_eq_zero {j : XiDivisorSupport}
    (h : angularEnergy j = 0) (k : XiDivisorSupport) : angularEnergyTerm j k = 0 := by
  have hle := (summable_angularEnergyTerm j).le_tsum k
    (fun b _ => angularEnergyTerm_nonneg j b)
  rw [← angularEnergy, h] at hle
  exact le_antisymm hle (angularEnergyTerm_nonneg j k)

theorem re_eq_of_angularEnergyTerm_eq_zero {j k : XiDivisorSupport} (hk : k ≠ j)
    (h : angularEnergyTerm j k = 0) : (k : ℂ).re = (j : ℂ).re := by
  rw [angularEnergyTerm, if_neg hk] at h
  have hpos : 0 < Complex.normSq ((j : ℂ) - (k : ℂ)) := by
    rw [Complex.normSq_pos, sub_ne_zero]
    exact fun hc => hk (Subtype.ext hc.symm)
  rcases div_eq_zero_iff.mp h with h1 | h2
  · have := sq_eq_zero_iff.mp h1
    linarith
  · exact absurd h2 hpos.ne'

/-- **A single zero of vanishing angular energy proves the hypothesis.**  If one zero sees every
other zero in a purely vertical direction, all real parts coincide. -/
theorem riemannHypothesis_of_angularEnergy_eq_zero {j : XiDivisorSupport}
    (h : angularEnergy j = 0) : RiemannHypothesis := by
  refine riemannHypothesis_of_forall_re_eq (c := (j : ℂ).re) fun ρ => ?_
  by_cases hρ : ρ = j
  · rw [hρ]
  · exact re_eq_of_angularEnergyTerm_eq_zero hρ
      (angularEnergyTerm_eq_zero_of_angularEnergy_eq_zero h ρ)

theorem angularEnergy_eq_zero_of_riemannHypothesis (h : RiemannHypothesis)
    (j : XiDivisorSupport) : angularEnergy j = 0 := by
  have hhalf : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re = 1 / 2 := fun ρ =>
    (supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ)
  have hterm : ∀ k, angularEnergyTerm j k = 0 := by
    intro k
    rw [angularEnergyTerm]
    split
    · rfl
    · rw [hhalf j, hhalf k]
      norm_num
  rw [angularEnergy]
  simp [hterm]

theorem riemannHypothesis_iff_forall_angularEnergy_eq_zero :
    RiemannHypothesis ↔ ∀ j : XiDivisorSupport, angularEnergy j = 0 := by
  constructor
  · exact angularEnergy_eq_zero_of_riemannHypothesis
  · intro hall
    by_cases hne : Nonempty XiDivisorSupport
    · obtain ⟨j⟩ := hne
      exact riemannHypothesis_of_angularEnergy_eq_zero (hall j)
    · exact riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => absurd ⟨ρ⟩ hne

/-- **The threshold form.**  The hypothesis is equivalent to a strict inequality, not to an exact
equality: no attainment, no maximum, no limit is involved. -/
theorem riemannHypothesis_iff_forall_angularEnergy_lt_one :
    RiemannHypothesis ↔ ∀ j : XiDivisorSupport, angularEnergy j < 1 := by
  constructor
  · intro h j
    rw [angularEnergy_eq_zero_of_riemannHypothesis h j]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
    by_contra hc
    exact absurd (one_le_angularEnergy hc) (not_le.mpr (h ρ))

/-- **The gap.**  The angular energies never all lie in the open interval `(0,1)`. -/
theorem angularEnergy_eq_zero_of_forall_lt_one (h : ∀ j : XiDivisorSupport, angularEnergy j < 1)
    (j : XiDivisorSupport) : angularEnergy j = 0 :=
  angularEnergy_eq_zero_of_riemannHypothesis
    (riemannHypothesis_iff_forall_angularEnergy_lt_one.mpr h) j

end

end RHTower
