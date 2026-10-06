import GaloisForLFunctions.RHTower.KuznetsovExplicitIdentity
import GaloisForLFunctions.RHTower.KontorovichLebedevInversion

/-!
# The Kuznetsov identity on the line `a₁ = σ + it`, `a₂ = σ − it`

On the line `s₁ = σ − it`, `s₂ = σ + it` (`σ > 1`, `t` real) the explicit Kuznetsov identity
becomes an identity between `K`-Bessel functions of order `2it`:

`Σ_{(c,d)} w(c,d) (c²)^{−σ} K_{2it}(X/|c|)
   = (X²/4)^{½−σ} 2^{3−2σ} [Σ_j ρ_j(v) conj ρ_j(w) M(t, ν_j) + (4π)⁻¹ ∫ Σ_i η_i(v) conj η_i(w) M(t, ir) dr]`

with `X = 4π√(μν)` and `M(t, ν) = ∫_0^∞ x^{2σ−2} K_{2it}(x) K_{2ν}(x) dx` (`kuznetsov_bessel`).

Proof.  Legendre's duplication formula gives `W(b, ν) = √π 2^{½−b} Γ(b−½+ν)Γ(b−½−ν)/Γ(b)`, so by
the Mellin product of two `K`-Bessel functions
`W(σ+it, ν) W(σ−it, ν) = π 2^{5−4σ} Γ(2σ−1) M(t, ν) / (Γ(σ+it)Γ(σ−it))`; on the geometric side
`(c²)^{it−σ} V(σ+it, σ−it; μ, ν, c²) = 2π 2^{2−2σ} Γ(2σ−1) (ν/μ)^{it} (c²)^{−σ} K_{2it}(X/|c|)
/ (Γ(σ+it)Γ(σ−it))`.  The factors `(ν/μ)^{it}` and `Γ(2σ−1)/(Γ(σ+it)Γ(σ−it))` cancel.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry MaassWhittaker

noncomputable section

variable {N : ℕ}

/-! ## Powers of positive reals -/

theorem cpow_ofReal_eq_exp {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a : ℝ) : ℂ) ^ z = cexp (z * (Real.log a : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), Complex.ofReal_log ha.le, mul_comm]

theorem two_cpow_eq_exp (z : ℂ) : (2 : ℂ) ^ z = cexp (z * (Real.log 2 : ℂ)) := by
  have h := cpow_ofReal_eq_exp (a := 2) (by norm_num) z
  push_cast at h
  exact h

/-! ## The Mellin transform of the Whittaker function on the line -/

/-- **Duplication form**: `W(b, ν) = √π 2^{−(b−½)} Γ(b−½+ν) Γ(b−½−ν) / Γ(b)` for `Re b > ½`. -/
theorem whittMellin_eq {b : ℂ} (hb : 1 / 2 < b.re) (ν : ℂ) :
    whittMellin b ν = (Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-(b - 1 / 2)) *
      Complex.Gamma (b - 1 / 2 + ν) * Complex.Gamma (b - 1 / 2 - ν) / Complex.Gamma b := by
  have hdup := Complex.Gamma_mul_Gamma_add_half (b - 1 / 2)
  rw [show b - 1 / 2 + 1 / 2 = b by ring] at hdup
  have hG2 : Complex.Gamma (2 * (b - 1 / 2)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGb : Complex.Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have h2 : (2 : ℂ) ^ (b - 1 / 2 - 1) * (2 : ℂ) ^ (1 - 2 * (b - 1 / 2)) = (2 : ℂ) ^ (-(b - 1 / 2)) := by
    rw [← Complex.cpow_add _ _ two_ne_zero]; congr 1; ring
  unfold whittMellin
  rw [div_eq_div_iff hG2 hGb]
  calc (2 : ℂ) ^ (b - 1 / 2 - 1) * Complex.Gamma (b - 1 / 2) * Complex.Gamma (b - 1 / 2 + ν) *
        Complex.Gamma (b - 1 / 2 - ν) * Complex.Gamma b
      = (2 : ℂ) ^ (b - 1 / 2 - 1) * (Complex.Gamma (b - 1 / 2) * Complex.Gamma b) *
          Complex.Gamma (b - 1 / 2 + ν) * Complex.Gamma (b - 1 / 2 - ν) := by ring
    _ = _ := by rw [hdup, ← h2]; ring

/-- `M(t, ν) = ∫_0^∞ x^{2σ−2} K_{2it}(x) K_{2ν}(x) dx`. -/
def besselPairMellin (σ t : ℝ) (ν : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((2 * σ - 2 : ℝ) : ℂ) * modifiedBesselKOrder x (2 * t * Complex.I) *
    modifiedBesselKOrder x (2 * ν)

/-- **The product on the line**:
`W(σ+it, ν) W(σ−it, ν) = π 2^{5−4σ} Γ(2σ−1) M(t, ν) / (Γ(σ+it) Γ(σ−it))`. -/
theorem whittMellin_mul_line {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) {ν : ℂ}
    (hν : |ν.re| < σ - 1 / 2) :
    whittMellin ((σ : ℂ) + t * Complex.I) ν * whittMellin ((σ : ℂ) - t * Complex.I) ν =
      Real.pi * (2 : ℂ) ^ ((5 - 4 * σ : ℝ) : ℂ) * Complex.Gamma (2 * σ - 1) /
        (Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)) *
          besselPairMellin σ t ν := by
  have hp : 1 / 2 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  have hm : 1 / 2 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  set s : ℂ := ((2 * σ - 1 : ℝ) : ℂ)
  have hchamber : |(2 * t * Complex.I : ℂ).re| + |(2 * ν).re| < s.re := by
    simp only [s, Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    simp only [mul_zero, mul_one, zero_mul, sub_zero, sub_self, abs_zero, zero_add]
    rw [abs_mul, abs_two]; linarith
  have hM := integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder hchamber
  have hs1 : s - 1 = ((2 * σ - 2 : ℝ) : ℂ) := by simp only [s]; push_cast; ring
  rw [hs1] at hM
  have hGs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [s]; linarith)
  have hGp : Complex.Gamma ((σ : ℂ) + t * Complex.I) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGm : Complex.Gamma ((σ : ℂ) - t * Complex.I) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (Real.sqrt Real.pi : ℂ) * Real.sqrt Real.pi = Real.pi := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [whittMellin_eq hp, whittMellin_eq hm, besselPairMellin, hM]
  have e1 : (s + 2 * t * Complex.I + 2 * ν) / 2 = (σ : ℂ) + t * Complex.I - 1 / 2 + ν := by simp only [s]; push_cast; ring
  have e2 : (s + 2 * t * Complex.I - 2 * ν) / 2 = (σ : ℂ) + t * Complex.I - 1 / 2 - ν := by simp only [s]; push_cast; ring
  have e3 : (s - 2 * t * Complex.I + 2 * ν) / 2 = (σ : ℂ) - t * Complex.I - 1 / 2 + ν := by simp only [s]; push_cast; ring
  have e4 : (s - 2 * t * Complex.I - 2 * ν) / 2 = (σ : ℂ) - t * Complex.I - 1 / 2 - ν := by simp only [s]; push_cast; ring
  rw [e1, e2, e3, e4]
  have hs : (2 * (σ : ℂ) - 1) = s := by simp only [s]; push_cast; ring
  rw [hs]
  have hpow : (2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) * (2 : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2)) =
      (2 : ℂ) ^ ((5 - 4 * σ : ℝ) : ℂ) * (2 : ℂ) ^ (s - 3) := by
    rw [← Complex.cpow_add _ _ two_ne_zero, ← Complex.cpow_add _ _ two_ne_zero]
    congr 1; simp only [s]; push_cast; ring
  set A₁ := Complex.Gamma ((σ : ℂ) + t * Complex.I - 1 / 2 + ν)
  set A₂ := Complex.Gamma ((σ : ℂ) + t * Complex.I - 1 / 2 - ν)
  set A₃ := Complex.Gamma ((σ : ℂ) - t * Complex.I - 1 / 2 + ν)
  set A₄ := Complex.Gamma ((σ : ℂ) - t * Complex.I - 1 / 2 - ν)
  calc (Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) * A₁ * A₂ /
          Complex.Gamma ((σ : ℂ) + t * Complex.I) *
        ((Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2)) * A₃ * A₄ /
          Complex.Gamma ((σ : ℂ) - t * Complex.I))
      = ((Real.sqrt Real.pi : ℂ) * Real.sqrt Real.pi) *
          ((2 : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) *
            (2 : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2))) * (A₁ * A₂ * A₃ * A₄) /
          (Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)) := by
        ring
    _ = Real.pi * ((2 : ℂ) ^ ((5 - 4 * σ : ℝ) : ℂ) * (2 : ℂ) ^ (s - 3)) * (A₁ * A₂ * A₃ * A₄) /
          (Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)) := by
        rw [hπ, hpow]
    _ = _ := by field_simp

/-! ## The geometric side on the line -/

theorem log_kuzParam {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) :
    Real.log (Kuznetsov.kuzParam μ ν q) =
      2 * Real.log (2 * Real.pi) + Real.log μ + Real.log ν - Real.log q := by
  unfold Kuznetsov.kuzParam
  have h4 : (4 : ℝ) * Real.pi ^ 2 = (2 * Real.pi) ^ 2 := by ring
  rw [h4, Real.log_div (by positivity) hq.ne', Real.log_mul (by positivity) hν.ne',
    Real.log_mul (by positivity) hμ.ne', Real.log_pow]
  push_cast; ring

/-- **The geometric kernel on the line**:
`q^{it−σ} V(σ+it, σ−it; μ, ν, q) = 2π 2^{2−2σ} Γ(2σ−1)/(Γ(σ+it)Γ(σ−it)) (ν/μ)^{it} q^{−σ} K_{2it}(2√P)`. -/
theorem kuzValue_line {μ ν q : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q) (σ t : ℝ) :
    ((q : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) *
        Kuznetsov.kuzValue ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν q =
      2 * Real.pi * (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) * Complex.Gamma (2 * σ - 1) /
          (Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)) *
        ((ν / μ : ℝ) : ℂ) ^ (t * Complex.I) * ((q : ℝ) : ℂ) ^ (-(σ : ℂ)) *
          modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν q)) (2 * t * Complex.I) := by
  have hP : 0 < Kuznetsov.kuzParam μ ν q := by unfold Kuznetsov.kuzParam; positivity
  have hd : ((σ : ℂ) + t * Complex.I) - ((σ : ℂ) - t * Complex.I) = 2 * t * Complex.I := by ring
  have hs : ((σ : ℂ) + t * Complex.I) + ((σ : ℂ) - t * Complex.I) = 2 * σ := by ring
  unfold Kuznetsov.kuzValue
  rw [hd, hs, show 2 * (t : ℂ) * Complex.I / 2 = t * Complex.I by ring,
    show (2 : ℂ) - 2 * σ = ((2 - 2 * σ : ℝ) : ℂ) by push_cast; ring,
    cpow_ofReal_eq_exp hq, cpow_ofReal_eq_exp hq, cpow_ofReal_eq_exp hP,
    cpow_ofReal_eq_exp (by positivity : (0 : ℝ) < 2 * Real.pi * μ),
    cpow_ofReal_eq_exp (by positivity : (0 : ℝ) < ν / μ), log_kuzParam hμ hν hq,
    Real.log_div hν.ne' hμ.ne', Real.log_mul (by positivity) hμ.ne']
  have hE : cexp (-((σ : ℂ) - t * Complex.I) * (Real.log q : ℂ)) *
      cexp (t * Complex.I * ((2 * Real.log (2 * Real.pi) + Real.log μ + Real.log ν - Real.log q : ℝ) : ℂ)) *
      cexp (-(2 * t * Complex.I) * ((Real.log (2 * Real.pi) + Real.log μ : ℝ) : ℂ)) =
      cexp (t * Complex.I * ((Real.log ν - Real.log μ : ℝ) : ℂ)) * cexp (-(σ : ℂ) * (Real.log q : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  linear_combination (2 * Real.pi * (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) * Complex.Gamma (2 * σ - 1) /
      (Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)) *
      modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν q)) (2 * t * Complex.I)) * hE

/-! ## The identity on the line -/

theorem conj_ofReal_sub_mul_I (σ t : ℝ) :
    conj ((σ : ℂ) - t * Complex.I) = (σ : ℂ) + t * Complex.I := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

theorem conj_ofReal_add_mul_I (σ t : ℝ) :
    conj ((σ : ℂ) + t * Complex.I) = (σ : ℂ) - t * Complex.I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

theorem two_pi_cpow_line {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (σ t : ℝ) :
    ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) *
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2)) =
      ((4 * Real.pi ^ 2 * μ * ν : ℝ) : ℂ) ^ ((1 / 2 - σ : ℝ) : ℂ) *
        ((ν / μ : ℝ) : ℂ) ^ (t * Complex.I) := by
  rw [cpow_ofReal_eq_exp (by positivity), cpow_ofReal_eq_exp (by positivity),
    cpow_ofReal_eq_exp (by positivity), cpow_ofReal_eq_exp (by positivity),
    ← Complex.exp_add, ← Complex.exp_add,
    Real.log_mul (by positivity) hμ.ne', Real.log_mul (by positivity) hν.ne',
    Real.log_mul (by positivity) hν.ne', Real.log_mul (by positivity) hμ.ne',
    Real.log_div hν.ne' hμ.ne',
    show (4 : ℝ) * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring, Real.log_pow]
  congr 1; push_cast; ring

/-- **The Kuznetsov identity on the line** `s₁ = σ − it`, `s₂ = σ + it`. -/
theorem kuznetsov_bessel (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) {n m : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) :
    ∑' r : ReducedRow, rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(σ : ℂ)) *
        modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))
          (2 * t * Complex.I) =
      ((4 * Real.pi ^ 2 * μ * ν : ℝ) : ℂ) ^ ((1 / 2 - σ : ℝ) : ℂ) * (2 : ℂ) ^ ((3 - 2 * σ : ℝ) : ℂ) *
        ((∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
            besselPairMellin σ t (specParam j.1)) +
          (4 * Real.pi : ℂ)⁻¹ * ∫ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
            conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
            besselPairMellin σ t (r * Complex.I)) := by
  have hs₁ : 1 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  have hs₂ : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  have h := kuznetsov_explicit hN hs₁ hs₂ hμ hν hv hw hn hm
  rw [conj_ofReal_sub_mul_I, conj_ofReal_add_mul_I] at h
  have hσ' : 1 / 2 < σ := by linarith
  set γ := Complex.Gamma ((σ : ℂ) + t * Complex.I) * Complex.Gamma ((σ : ℂ) - t * Complex.I)
  set G := Complex.Gamma (2 * σ - 1)
  set E : ℂ := ((ν / μ : ℝ) : ℂ) ^ (t * Complex.I)
  set Cw : ℂ := Real.pi * (2 : ℂ) ^ ((5 - 4 * σ : ℝ) : ℂ) * G / γ
  -- geometric side
  have hgeo : ∀ r : ReducedRow, rowWeight μ ν v w r.1 *
      (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) *
      Kuznetsov.kuzValue ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν ((r.1.1 0 : ℝ) ^ 2) =
      (2 * Real.pi * (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) * G / γ * E) *
        (rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(σ : ℂ)) *
          modifiedBesselKOrder (2 * Real.sqrt (Kuznetsov.kuzParam μ ν ((r.1.1 0 : ℝ) ^ 2)))
            (2 * t * Complex.I)) := fun r => by
    have hq : (0 : ℝ) < (r.1.1 0 : ℝ) ^ 2 := by
      have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
      positivity
    rw [mul_assoc, kuzValue_line hμ hν hq σ t]
    ring
  rw [tsum_congr hgeo, tsum_mul_left] at h
  -- discrete spectrum
  have hdisc : ∀ j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) *
      whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1) *
      whittMellin ((σ : ℂ) - t * Complex.I) (specParam j.1) =
      Cw * (cuspCoeff j μ v * conj (cuspCoeff j (-ν) w) * besselPairMellin σ t (specParam j.1)) :=
    fun j => by
      have hj : |(specParam j.1).re| < σ - 1 / 2 :=
        (abs_re_specParam_le (cuspEigenBasis_lam_nonneg j)).trans_lt (by linarith)
      rw [mul_assoc (cuspCoeff j μ v * conj (cuspCoeff j (-ν) w)), whittMellin_mul_line hσ' t hj]
      ring
  rw [tsum_congr hdisc, tsum_mul_left] at h
  -- continuous spectrum
  have hcont : ∀ r : ℝ, ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
      whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) *
      whittMellin ((σ : ℂ) - t * Complex.I) (r * Complex.I) =
      Cw * ∑ i, eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m) *
        besselPairMellin σ t (r * Complex.I) := fun r => by
    have hr : |((r : ℂ) * Complex.I).re| < σ - 1 / 2 := by simp; linarith
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc (eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n *
      conj (eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m)),
      whittMellin_mul_line hσ' t hr]
    ring
  simp_rw [hcont] at h
  rw [integral_const_mul, mul_assoc (4 : ℂ), two_pi_cpow_line hμ hν σ t] at h
  -- cancellation
  have hγ : γ ≠ 0 := mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
    (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hG : G ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hE : E ≠ 0 := by
    simp only [E]; rw [cpow_ofReal_eq_exp (by positivity)]; exact Complex.exp_ne_zero _
  have h2 : (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) ≠ 0 := by
    rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _
  have hpow : (2 : ℂ) ^ ((5 - 4 * σ : ℝ) : ℂ) =
      (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) * (2 : ℂ) ^ ((3 - 2 * σ : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ two_ne_zero]; congr 1; push_cast; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K : ℂ := 4 * Real.pi * (2 : ℂ) ^ ((2 - 2 * σ : ℝ) : ℂ) * G / γ * E
  have hK : K ≠ 0 := mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hπ)
    h2) hG) hγ) hE
  refine mul_left_cancel₀ hK ?_
  simp only [Cw] at h
  rw [hpow] at h
  linear_combination h

end

end GaloisForLFunctions.RHTower.DeckPointPair
