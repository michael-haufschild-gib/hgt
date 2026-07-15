import GaloisForLFunctions.HTGeometry.GammaShiftDirichletResidual
import GaloisForLFunctions.RHTower.ZetaHypertranscendental

/-!
# Gamma-shift readout of zeta jets

The generic Gamma-shift residual theorem is specialized to the Riemann zeta function and all of
its positive derivatives.  The zeroth jet reads the neutral Dirichlet atom `n = 1`; every positive
jet reads the first logarithmic atom `n = 2`, with the exact sign and logarithmic power predicted by
the paper theorem.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions

open Filter Polynomial LSeries

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The ordinary zeta coefficient stream, normalized to zero at the ignored index `0`. -/
def zetaValueCoeff (n : ℕ) : ℂ := if n = 0 then 0 else 1

@[simp] theorem zetaValueCoeff_zero : zetaValueCoeff 0 = 0 := by
  simp [zetaValueCoeff]

@[simp] theorem zetaValueCoeff_one : zetaValueCoeff 1 = 1 := by
  simp [zetaValueCoeff]

theorem zetaValueCoeff_eq_one {n : ℕ} (hn : n ≠ 0) : zetaValueCoeff n = 1 := by
  simp [zetaValueCoeff, hn]

theorem zetaValueCoeff_abscissa_lt_top :
    LSeries.abscissaOfAbsConv zetaValueCoeff < ⊤ := by
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → zetaValueCoeff n = (1 : ℕ → ℂ) n := by
    intro n hn
    simp [zetaValueCoeff, hn]
  rw [LSeries.abscissaOfAbsConv_congr hcongr,
    LSeries.abscissaOfAbsConv_one]
  exact EReal.coe_lt_top 1

theorem LSeries_zetaValueCoeff_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries zetaValueCoeff s = riemannZeta s := by
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → zetaValueCoeff n = (1 : ℕ → ℂ) n := by
    intro n hn
    simp [zetaValueCoeff, hn]
  rw [LSeries_congr hcongr, LSeries_one_eq_riemannZeta hs]

/-- J1: every positive zeta jet is the signed `LSeries` of the logarithmic atom stream. -/
theorem iteratedDeriv_riemannZeta_eq_signed_LSeries
    (j : ℕ) (hj : 0 < j) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j riemannZeta s =
      (-1 : ℂ) ^ j * LSeries (⇑(zetaJetA j)) s := by
  rw [iteratedDeriv_riemannZeta_eq j hs, if_neg hj.ne', zero_add]

theorem gammaJetAnnihilator_riemannZeta_eq_LSeries
    (x : ℝ) (hx : 1 < x) (shift : ι → ℂ) (mult : ι → ℕ) :
    gammaJetAnnihilator (x : ℂ) shift mult riemannZeta =
      gammaJetAnnihilator (x : ℂ) shift mult (fun z => LSeries zetaValueCoeff z) := by
  rw [gammaJetAnnihilator, gammaJetAnnihilator]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  symm
  apply LSeries_zetaValueCoeff_eq_riemannZeta
  rw [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  linarith

theorem gammaJetAnnihilator_zetaJet_eq_signed_LSeries
    (j : ℕ) (hj : 0 < j) (x : ℝ) (hx : 1 < x)
    (shift : ι → ℂ) (mult : ι → ℕ) :
    gammaJetAnnihilator (x : ℂ) shift mult
        (fun z => iteratedDeriv j riemannZeta z) =
      (-1 : ℂ) ^ j *
        gammaJetAnnihilator (x : ℂ) shift mult
          (fun z => LSeries (⇑(zetaJetA j)) z) := by
  rw [gammaJetAnnihilator, gammaJetAnnihilator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_riemannZeta_eq_signed_LSeries j hj]
  · ring_nf
  · rw [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith

/-- J2 for `ζ`: the neutral atom `n=1` is read with coefficient one. -/
theorem gammaJetAnnihilator_riemannZeta_normalized_tendsto
    (shift : ι → ℂ) (mult : ι → ℕ) :
    Tendsto (fun x : ℝ =>
      gammaJetAnnihilator (x : ℂ) shift mult riemannZeta /
        (x : ℂ) ^ gammaJetOrder mult)
      atTop (𝓝 ((-1 : ℂ) ^ gammaJetOrder mult)) := by
  have hlim := gammaJetAnnihilator_LSeries_firstCoeff_tendsto
    zetaValueCoeff 0 (by
      intro m hm
      have : m = 0 := by omega
      subst m
      rfl) zetaValueCoeff_abscissa_lt_top shift mult
  have hcongr : (fun x : ℝ =>
      (((0 : ℕ) : ℂ) + 1) ^ (x : ℂ) *
          gammaJetAnnihilator (x : ℂ) shift mult (fun z => LSeries zetaValueCoeff z) /
        (x : ℂ) ^ gammaJetOrder mult) =ᶠ[atTop]
      (fun x : ℝ => gammaJetAnnihilator (x : ℂ) shift mult riemannZeta /
        (x : ℂ) ^ gammaJetOrder mult) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [gammaJetAnnihilator_riemannZeta_eq_LSeries x hx]
    simp
  have hout := hlim.congr' hcongr
  simpa [zetaValueCoeff] using hout

/-- J2 for every positive zeta derivative: the first atom is `n=2` with value `(-log 2)^j`. -/
theorem gammaJetAnnihilator_zetaJet_normalized_tendsto
    (j : ℕ) (hj : 0 < j) (shift : ι → ℂ) (mult : ι → ℕ) :
    Tendsto (fun x : ℝ =>
      (2 : ℂ) ^ (x : ℂ) *
          gammaJetAnnihilator (x : ℂ) shift mult
            (fun z => iteratedDeriv j riemannZeta z) /
        (x : ℂ) ^ gammaJetOrder mult)
      atTop (𝓝 ((-1 : ℂ) ^ (gammaJetOrder mult + j) * (Real.log 2 : ℂ) ^ j)) := by
  have hzero : ∀ m ≤ 1, (zetaJetA j : ArithmeticFunction ℂ) m = 0 := by
    intro m hm
    simp [zetaJetA_apply]
    omega
  have habscissa : LSeries.abscissaOfAbsConv (⇑(zetaJetA j)) < ⊤ :=
    (abscissaOfAbsConv_zetaJetA_le j).trans_lt (EReal.coe_lt_top 1)
  have hlim := gammaJetAnnihilator_LSeries_firstCoeff_tendsto
    (⇑(zetaJetA j)) 1 hzero habscissa shift mult
  have hscaled := hlim.const_mul ((-1 : ℂ) ^ j)
  have htarget : (-1 : ℂ) ^ j *
      ((zetaJetA j : ArithmeticFunction ℂ) 2 * (-1 : ℂ) ^ gammaJetOrder mult) =
      (-1 : ℂ) ^ (gammaJetOrder mult + j) * (Real.log 2 : ℂ) ^ j := by
    rw [zetaJetA_apply]
    simp only [show 2 ≤ (2 : ℕ) by omega, if_true]
    rw [pow_add]
    ring_nf
  rw [htarget] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [gammaJetAnnihilator_zetaJet_eq_signed_LSeries j hj x hx]
  ring_nf

end

end GaloisForLFunctions
