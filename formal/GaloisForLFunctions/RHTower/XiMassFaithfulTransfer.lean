import GaloisForLFunctions.RHTower.XiAbstractInstance
import GaloisForLFunctions.RHTower.XiMassShiftedFamily
import GaloisForLFunctions.HTGeometry.AbstractSpectralMass

/-!
# The mass-shifted Xi carrier is quantitatively faithful

`XiMassShiftedFamily` builds the mass-shifted carrier `sqrt (alpha ^ 2 + a ^ 2)` of the Xi divisor
directly, and shows that a bounded vertical line for its trace forces RH.  That construction is an
instance of the abstract mass deformation: the mass-shifted Xi family and the mass deformation of
the abstract Poisson family have the same points, and the abstract construction uses only the
admissibility interface — in particular not the Xi-specific height bound `Re alpha > 3`.

The deformation conserves the charge `Im (alpha ^ 2)`, so no displacement information is destroyed.
Quantitatively, because the least Poisson height of the Xi divisor exceeds `3`,

`9 * (1/2 - Re rho) ^ 2 ≤ (9 + a ^ 2) * (mass-shifted displacement) ^ 2`.

For `a = 1/2` the loss factor is `sqrt (37/36) < 1.014`.  A displacement or defect bound for the
prime-accessible mass-shifted carrier therefore returns an explicit zero-free region for zeta, not
merely the degenerate conclusion that a vanishing bound gives RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Xi divisor's least Poisson height exceeds three. -/
theorem three_lt_xiPoissonBottomHeight : 3 < xiPoissonBottomHeight :=
  three_lt_xiPoissonPoint_re xiPoissonBottomCopy

theorem xiPoissonAbstract_base : xiPoissonAbstract.base = xiPoissonBottomHeight := rfl

/-- **The mass-shifted Xi carrier is the abstract mass deformation.**  The Xi-specific construction
and the interface-only construction have the same points. -/
theorem xiMassFamily_pt_eq_mass_pt {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    (xiMassFamily ha).pt q = (xiPoissonAbstract.mass ha).pt q := rfl

theorem xiMassFamily_traceC_eq {a : ℝ} (ha : 1 / 2 ≤ a) (τ : ℂ) :
    (xiMassFamily ha).traceC τ = (xiPoissonAbstract.mass ha).traceC τ := rfl

theorem xiMassFamily_traceReal_eq {a : ℝ} (ha : 1 / 2 ≤ a) (σ : ℝ) :
    (xiMassFamily ha).traceReal σ = (xiPoissonAbstract.mass ha).traceReal σ := rfl

/-- **The deformation conserves the displacement charge of every Xi zero.**  `Im (alpha ^ 2)` is the
same for the Poisson carrier and for every mass-shifted carrier. -/
theorem charge_xiMassFamily_eq {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    (((xiMassFamily ha).pt q) ^ 2).im = ((xiPoissonPoint q) ^ 2).im := by
  rw [xiMassFamily_pt_eq_mass_pt ha q]
  exact xiPoissonAbstract.charge_mass ha q

/-- **Pointwise faithfulness for the Xi divisor.**  The distance of a zero from the critical line is
recovered from the mass-shifted displacement with the explicit loss `(9 + a ^ 2)/9`. -/
theorem nine_mul_sq_im_xiSpectralPoint_le {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    9 * (xiSpectralPoint q).im ^ 2 ≤ (9 + a ^ 2) * ((xiMassFamily ha).pt q).im ^ 2 := by
  have habs := xiPoissonAbstract.sq_im_le_of_mass ha q
  rw [xiPoissonAbstract_base] at habs
  have hpt : xiPoissonAbstract.pt q = xiPoissonPoint q := rfl
  rw [hpt] at habs
  rw [← xiMassFamily_pt_eq_mass_pt ha q] at habs
  have hsq := sq_im_xiPoissonPoint_eq q
  rw [hsq] at habs
  have hb := three_lt_xiPoissonBottomHeight
  have hj : (0 : ℝ) ≤ ((xiMassFamily ha).pt q).im ^ 2 := sq_nonneg _
  have hB : (9 : ℝ) ≤ xiPoissonBottomHeight ^ 2 := by nlinarith
  have hBpos : (0 : ℝ) < xiPoissonBottomHeight ^ 2 := by nlinarith
  have key : xiPoissonBottomHeight ^ 2 * (9 * (xiSpectralPoint q).im ^ 2)
      ≤ xiPoissonBottomHeight ^ 2 * ((9 + a ^ 2) * ((xiMassFamily ha).pt q).im ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left habs (by norm_num : (0:ℝ) ≤ 9),
      mul_nonneg (mul_nonneg (sq_nonneg a) hj) (sub_nonneg.mpr hB)]
  exact le_of_mul_le_mul_left key hBpos

/-- **A displacement bound for the mass-shifted carrier is a zero-free region for zeta.** -/
theorem sq_im_xiSpectralPoint_le_of_mass_im_le {a M : ℝ} (ha : 1 / 2 ≤ a)
    (h : ∀ q : XiZeroCopy, ((xiMassFamily ha).pt q).im ^ 2 ≤ M) (q : XiZeroCopy) :
    9 * (xiSpectralPoint q).im ^ 2 ≤ (9 + a ^ 2) * M := by
  have h1 := nine_mul_sq_im_xiSpectralPoint_le ha q
  have h2 := h q
  nlinarith [sq_nonneg a]

/-- **The defect of the prime-accessible carrier is an explicit zero-free region for zeta.**  A
bound `M` for the mass-shifted defect at one admissible real time bounds the distance of every zero
from the critical line, with only the two explicit losses `(9 + a ^ 2)/9` from the deformation and
`exp (sigma a)` from the raised heights. -/
theorem sq_im_xiSpectralPoint_le_of_xiMass_defect_le {a σ M : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ)
    (hσ' : σ ≤ 2 * Real.pi)
    (h : (xiMassFamily ha).traceReal σ - ((xiMassFamily ha).traceC (σ : ℂ)).re ≤ M)
    (q : XiZeroCopy) :
    9 * (xiSpectralPoint q).im ^ 2 ≤
      (9 + a ^ 2) *
        (Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) *
          Real.exp (σ * (xiPoissonPoint q).re)) := by
  have hdef : (xiPoissonAbstract.mass ha).defect σ ≤ M := by
    rw [HTGeometry.AbstractSpectralFamily.defect, ← xiMassFamily_traceReal_eq ha σ,
      ← xiMassFamily_traceC_eq ha (σ : ℂ)]
    exact h
  have habs := xiPoissonAbstract.sq_im_le_of_mass_defect_le ha hσ hσ' hdef q
  rw [xiPoissonAbstract_base] at habs
  have hpt : xiPoissonAbstract.pt q = xiPoissonPoint q := rfl
  rw [hpt] at habs
  rw [sq_im_xiPoissonPoint_eq q] at habs
  have hb := three_lt_xiPoissonBottomHeight
  have hMnn : 0 ≤ M := by
    have hd := (xiPoissonAbstract.mass ha).defect_nonneg hσ
    linarith
  have hrest : (0 : ℝ) ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) *
      Real.exp (σ * (xiPoissonPoint q).re) := by positivity
  have hB : (9 : ℝ) ≤ xiPoissonBottomHeight ^ 2 := by nlinarith
  have hBpos : (0 : ℝ) < xiPoissonBottomHeight ^ 2 := by nlinarith
  have key : xiPoissonBottomHeight ^ 2 * (9 * (xiSpectralPoint q).im ^ 2)
      ≤ xiPoissonBottomHeight ^ 2 *
        ((9 + a ^ 2) *
          (Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) *
            Real.exp (σ * (xiPoissonPoint q).re))) := by
    nlinarith [mul_le_mul_of_nonneg_left habs (by norm_num : (0:ℝ) ≤ 9),
      mul_nonneg (mul_nonneg (sq_nonneg a) hrest) (sub_nonneg.mpr hB)]
  exact le_of_mul_le_mul_left key hBpos

/-- **The mass-shifted line criterion, both directions.**  For every mass `a ≥ 1/2` the Riemann
Hypothesis is equivalent to boundedness of the mass-shifted trace on one vertical line. The forward
direction is the new half: the deformation preserves the real locus exactly, so RH really does make
the prime-accessible carrier bounded. -/
theorem riemannHypothesis_iff_exists_xiMassTrace_line_bound {a : ℝ} (ha : 1 / 2 ≤ a) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧
        ∀ x : ℝ, ‖(xiMassFamily ha).traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro hRH
    obtain ⟨σ, C, hσ, hline⟩ :=
      (xiPoissonAbstract.im_eq_zero_iff_exists_mass_line_bound ha).mp
        (fun q => xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
    exact ⟨σ, C, hσ, fun x => by rw [xiMassFamily_traceC_eq ha]; exact hline x⟩
  · rintro ⟨σ, C, hσ, hline⟩
    exact riemannHypothesis_of_xiMassTrace_line_bound ha hσ hline

end

end RHTower

namespace RHTower

noncomputable section

/-- **Charge neutrality for the Xi divisor.**  Weighted by any real-time Poisson weight, the total
displacement charge `2 * height * (1/2 - Re rho)` of the zeros vanishes unconditionally.  Every
functional of the divisor that is linear in the distance to the critical line is therefore blind. -/
theorem tsum_xiPoissonWeight_mul_charge_eq_zero {σ : ℝ} (hσ : 0 < σ) :
    ∑' q : XiZeroCopy, xiPoissonWeight σ q * ((xiPoissonPoint q) ^ 2).im = 0 :=
  xiPoissonAbstract.tsum_weight_mul_charge_eq_zero hσ

/-- The Poisson trace of the Xi divisor is real on the positive real axis. -/
theorem im_xiPoissonTraceC_ofReal_eq_zero {σ : ℝ} (hσ : 0 < σ) :
    (xiPoissonTraceC (σ : ℂ)).im = 0 :=
  xiPoissonAbstract.im_traceC_ofReal_eq_zero hσ

/-- The same neutrality for every mass-shifted carrier: the deformation conserves each charge, so it
conserves the vanishing of their weighted total. -/
theorem tsum_xiMass_weight_mul_charge_eq_zero {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) :
    ∑' q : XiZeroCopy,
        (xiPoissonAbstract.mass ha).weight σ q * ((xiPoissonPoint q) ^ 2).im = 0 := by
  have h := (xiPoissonAbstract.mass ha).tsum_weight_mul_charge_eq_zero hσ
  refine Eq.trans (tsum_congr fun q => ?_) h
  rw [HTGeometry.AbstractSpectralFamily.charge, xiPoissonAbstract.mass_pt_sq ha q,
    Complex.add_im, Complex.ofReal_im, add_zero]
  rfl

end

end RHTower

namespace RHTower

noncomputable section

/-- **The mass-shifted energy never exceeds the Poisson energy.** -/
theorem xiMassEnergy_le_xiPoissonEnergy {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) :
    (xiPoissonAbstract.mass ha).energy σ ≤ xiPoissonAbstract.energy σ :=
  xiPoissonAbstract.energy_mass_le ha hσ

/-- **Global faithfulness for the Xi divisor.**  The Poisson displacement energy of the zeros is
recovered from the prime-accessible mass-shifted energy up to the two explicit factors
`(9 + a ^ 2)/9` and `exp (sigma a)`.  Together with `xiMassEnergy_le_xiPoissonEnergy` the two
invariants are comparable, so the mass-shifted criterion is not merely sufficient for RH: it carries
the same quantitative information as the Poisson one. -/
theorem nine_mul_exp_mul_xiPoissonEnergy_le {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) :
    9 * (Real.exp (-(σ * a)) * xiPoissonAbstract.energy σ)
      ≤ (9 + a ^ 2) * (xiPoissonAbstract.mass ha).energy σ := by
  have habs := xiPoissonAbstract.energy_le_mass_energy ha hσ
  rw [xiPoissonAbstract_base] at habs
  have hb := three_lt_xiPoissonBottomHeight
  have hB : (9 : ℝ) ≤ xiPoissonBottomHeight ^ 2 := by nlinarith
  have hBpos : (0 : ℝ) < xiPoissonBottomHeight ^ 2 := by nlinarith
  have hEm : (0 : ℝ) ≤ (xiPoissonAbstract.mass ha).energy σ :=
    (xiPoissonAbstract.mass ha).energy_nonneg σ
  have hE : (0 : ℝ) ≤ Real.exp (-(σ * a)) * xiPoissonAbstract.energy σ := by
    have := xiPoissonAbstract.energy_nonneg σ
    positivity
  have key : xiPoissonBottomHeight ^ 2 * (9 * (Real.exp (-(σ * a)) * xiPoissonAbstract.energy σ))
      ≤ xiPoissonBottomHeight ^ 2 * ((9 + a ^ 2) * (xiPoissonAbstract.mass ha).energy σ) := by
    nlinarith [mul_le_mul_of_nonneg_left habs (by norm_num : (0:ℝ) ≤ 9),
      mul_nonneg (mul_nonneg (sq_nonneg a) hEm) (sub_nonneg.mpr hB)]
  exact le_of_mul_le_mul_left key hBpos

/-- **RH is the vanishing of the mass-shifted energy.**  Both directions, for every mass. -/
theorem riemannHypothesis_iff_xiMassEnergy_eq_zero {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ)
    (hσ' : σ ≤ 2 * Real.pi) :
    RiemannHypothesis ↔ (xiPoissonAbstract.mass ha).energy σ = 0 := by
  constructor
  · intro hRH
    refine ((xiPoissonAbstract.mass ha).im_eq_zero_iff_energy_eq_zero hσ hσ').mp fun q => ?_
    exact (xiPoissonAbstract.mass_im_eq_zero_iff ha q).mpr
      (xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro h
    refine riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero fun q => ?_)
    exact (xiPoissonAbstract.mass_im_eq_zero_iff ha q).mp
      ((xiPoissonAbstract.mass ha).im_eq_zero_iff_energy_eq_zero hσ hσ' |>.mpr h q)

end

end RHTower
