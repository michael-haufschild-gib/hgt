import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonTermOfAConductor
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheNormalizedAtomicTransform
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# The zero ledger of the bulk

A fixed packet of conductors `x = Σ_{e∈E} y_e r_e`, `r_e(n) = c_e(n)/√(φ(e) n log N)`, is read by a
point `ρ` of a zero configuration through the Weil summand of its atomic test
(`SpacingScaleHarmonicAnalysis.Wsummand_atomicTest`): the atom factor `ĝ(γ_ρ) conj ĝ(γ̄_ρ)` times the
Dirichlet factor `D_x(γ_ρ) D_x(γ_{1−ρ})`. The Dirichlet factor is a quadratic form in the conductor
Dirichlet polynomials `D_e(ρ;N)` and `D_e(1 − ρ;N)`, and by the horizon law only the pole conductor
has a term growing with `N`.

* **Ledger factor** (`tendsto_packetLedger`): `(log N/N) D_x(γ_ρ) D_x(γ_{1−ρ}) → y_1²/(ρ(1 − ρ))`
  for every `ρ` in the open strip.
* **Bulk zero ledger** (`tendsto_bulkLedger`): for every profile `φ` and every overlap schedule with
  `c_N/N → 0`, the contribution of `ρ` to the normalized complete form satisfies
  `(log N / c_N) · W_ρ / ∫g² → m_ρ ((∫φ)²/∫φ²) · y_1²/(ρ(1 − ρ))`.
* **At the critical curve** (`tendsto_bulkLedger_criticalCurve`): along `c_N⁸/log N → K` the
  contribution rescaled by `c_N⁷` tends to `K m_ρ ((∫φ)²/∫φ²) y_1²/(ρ(1 − ρ))`.
* **Sign** (`re_inv_mul_one_sub_pos`): `Re 1/(ρ(1 − ρ)) > 0` on the open strip.

A single point of the strip, on the line or off it, enters the second-order term of a fixed packet
only through the pole coefficient `y_1`, with a weight of positive real part. Fixed conductor
packets cannot see an individual zero at any multiple of the critical curve; the statement holds
for every configuration, so it carries no selection.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-- Atomic weights of the conductor packet `Σ_{e∈E} y_e r_e`, `r_e(n) = c_e(n)/√(φ(e) n log N)`. -/
def packetWeights (E : Finset ℕ) (y : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ e ∈ E, y e * ramanujanLagCoefficient e n /
    (Real.sqrt e.totient * Real.sqrt n * Real.sqrt (Real.log N))

/-- The pole coefficient `[1 ∈ E] y_1`. -/
def poleCoefficient (E : Finset ℕ) (y : ℕ → ℝ) : ℝ := if 1 ∈ E then y 1 else 0

/-- `n^{−1/2} e^{(s−½) log n} = n^{s−1}`. -/
theorem inv_sqrt_mul_exp {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ((Real.sqrt n : ℝ) : ℂ)⁻¹ * Complex.exp ((s - 1 / 2) * (Real.log n : ℂ)) =
      ((n : ℝ) : ℂ) ^ (s - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : ((Real.sqrt n : ℝ) : ℂ) = Complex.exp ((Real.log n : ℂ) / 2) := by
    rw [show Real.sqrt n = Real.exp (Real.log n / 2) by rw [Real.exp_half, Real.exp_log hn0],
      Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hsq, ← Complex.exp_neg, ← Complex.exp_add, RHTower.cpow_ofReal_eq_exp hn0]
  congr 1
  ring

/-- The conjugate Dirichlet factor is the Dirichlet polynomial at `γ_{1−ρ}`. -/
theorem conj_dirichletPoly_conj_gammaOf (N : ℕ) (x : ℕ → ℝ) (ρ : ℂ) :
    conj (dirichletPoly N x (conj (gammaOf ρ))) = dirichletPoly N x (gammaOf (1 - ρ)) := by
  have hg : gammaOf (1 - ρ) = -gammaOf ρ := by unfold gammaOf; ring
  unfold dirichletPoly
  rw [map_sum, hg]
  refine sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- `D_x(γ_s) = (log N)^{−1/2} Σ_{e∈E} (y_e/√φ(e)) D_e(s;N)` for the packet weights. -/
theorem dirichletPoly_packetWeights (E : Finset ℕ) (y : ℕ → ℝ) (N : ℕ) (s : ℂ) :
    dirichletPoly N (packetWeights E y N) (gammaOf s) =
      ((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ *
        ∑ e ∈ E, ((y e / Real.sqrt e.totient : ℝ) : ℂ) * conductorDirichlet e N s := by
  rw [dirichletPoly_gammaOf, mul_sum]
  unfold packetWeights conductorDirichlet
  simp only [Complex.ofReal_sum, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [← inv_sqrt_mul_exp hn1 s]
  push_cast
  ring

/-- `‖N^{−1} N^s‖ → 0` on `Re s < 1`. -/
theorem tendsto_inv_mul_cpow {s : ℂ} (hs1 : s.re < 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) : ℂ)⁻¹ * ((N : ℝ) : ℂ) ^ s) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show 0 < 1 - s.re by linarith)).comp
    tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN0,
    Complex.norm_cpow_eq_rpow_re_of_pos hN0, Function.comp_apply, neg_sub,
    Real.rpow_sub hN0, Real.rpow_one, inv_mul_eq_div]

/-- The pole part of a packet: `Σ_{e∈E} u_e [e = 1] N^s/s = u_1 N^s/s`. -/
theorem sum_mul_horizonTerm (E : Finset ℕ) (u : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    ∑ e ∈ E, u e * horizonTerm e N s = (if 1 ∈ E then u 1 else 0) * (((N : ℝ) : ℂ) ^ s / s) := by
  unfold horizonTerm
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq' E 1]
  split_ifs <;> simp

/-- The remainder of a packet after its horizon term converges. -/
theorem tendsto_packet_remainder {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (E : Finset ℕ)
    (u : ℕ → ℂ) :
    Tendsto (fun N : ℕ => ∑ e ∈ E, u e * conductorDirichlet e N s -
        (if 1 ∈ E then u 1 else 0) * (((N : ℝ) : ℂ) ^ s / s)) atTop
      (𝓝 (∑ e ∈ E, u e * (riemannZeta (1 - s) * jordanC e s))) := by
  have h := tendsto_finsetSum E fun e _ =>
    (tendsto_conductorDirichlet_sub_horizonTerm hs0 hs1 e).const_mul (u e)
  refine h.congr fun N => ?_
  rw [← sum_mul_horizonTerm, ← sum_sub_distrib]
  exact sum_congr rfl fun e _ => by ring

/-- **The ledger factor.** For `ρ` in the open strip,
`(log N/N) D_x(γ_ρ) D_x(γ_{1−ρ}) → y_1²/(ρ(1 − ρ))`. -/
theorem tendsto_packetLedger {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (E : Finset ℕ)
    (y : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ((Real.log N / N : ℝ) : ℂ) *
        (dirichletPoly N (packetWeights E y N) (gammaOf ρ) *
          dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ)))) atTop
      (𝓝 (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) := by
  have hρ0' : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1' : 1 - ρ ≠ 0 := fun h => by
    have : ρ = 1 := by linear_combination -h
    rw [this, Complex.one_re] at hρ1; exact lt_irrefl 1 hρ1
  have hσ0 : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hσ1 : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  set u : ℕ → ℂ := fun e => ((y e / Real.sqrt e.totient : ℝ) : ℂ) with hu
  set U : ℂ := if 1 ∈ E then u 1 else 0 with hU
  have hUy : U = (poleCoefficient E y : ℂ) := by
    simp only [hU, hu, poleCoefficient]
    split_ifs <;> simp
  -- remainders
  set A : ℕ → ℂ := fun N => ∑ e ∈ E, u e * conductorDirichlet e N ρ -
    U * (((N : ℝ) : ℂ) ^ ρ / ρ) with hA
  set B : ℕ → ℂ := fun N => ∑ e ∈ E, u e * conductorDirichlet e N (1 - ρ) -
    U * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)) with hB
  obtain ⟨a, ha⟩ : ∃ a, Tendsto A atTop (𝓝 a) := ⟨_, tendsto_packet_remainder hρ0 hρ1 E u⟩
  obtain ⟨b, hb⟩ : ∃ b, Tendsto B atTop (𝓝 b) := ⟨_, tendsto_packet_remainder hσ0 hσ1 E u⟩
  have hp : Tendsto (fun N : ℕ => ((N : ℝ) : ℂ)⁻¹ * ((N : ℝ) : ℂ) ^ ρ) atTop (𝓝 0) :=
    tendsto_inv_mul_cpow hρ1
  have hq : Tendsto (fun N : ℕ => ((N : ℝ) : ℂ)⁻¹ * ((N : ℝ) : ℂ) ^ (1 - ρ)) atTop (𝓝 0) :=
    tendsto_inv_mul_cpow hσ1
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  -- the limit of the expanded product
  have hlim : Tendsto (fun N : ℕ => U ^ 2 / (ρ * (1 - ρ)) +
      U / ρ * (((N : ℝ) : ℂ)⁻¹ * ((N : ℝ) : ℂ) ^ ρ) * B N +
      U / (1 - ρ) * (((N : ℝ) : ℂ)⁻¹ * ((N : ℝ) : ℂ) ^ (1 - ρ)) * A N +
      ((N : ℝ) : ℂ)⁻¹ * A N * B N) atTop (𝓝 (U ^ 2 / (ρ * (1 - ρ)))) := by
    have := (((tendsto_const_nhds (x := U ^ 2 / (ρ * (1 - ρ)))).add
      ((hp.const_mul (U / ρ)).mul hb)).add
      ((hq.const_mul (U / (1 - ρ))).mul ha)).add ((hinv.mul ha).mul hb)
    simpa using this
  have hval : U ^ 2 / (ρ * (1 - ρ)) = ((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)) := by
    rw [hUy]; push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hNc' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hLc : ((Real.log N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hpow : ((N : ℝ) : ℂ)⁻¹ * (((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ)) = 1 := by
    rw [← Complex.cpow_add _ _ hNc, add_sub_cancel, Complex.cpow_one, inv_mul_cancel₀ hNc]
  have hsq : ((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ =
      ((Real.log N : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hL0.le]
  have hAe : ∑ e ∈ E, u e * conductorDirichlet e N ρ = A N + U * (((N : ℝ) : ℂ) ^ ρ / ρ) := by
    simp only [hA]; ring
  have hBe : ∑ e ∈ E, u e * conductorDirichlet e N (1 - ρ) =
      B N + U * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)) := by
    simp only [hB]; ring
  simp only [hu] at hAe hBe
  rw [dirichletPoly_packetWeights, dirichletPoly_packetWeights, hAe, hBe]
  set X := A N + U * (((N : ℝ) : ℂ) ^ ρ / ρ)
  set Y := B N + U * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))
  have hnorm : ((Real.log N / N : ℝ) : ℂ) *
      (((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * X * (((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * Y)) =
      ((N : ℝ) : ℂ)⁻¹ * (X * Y) := by
    rw [show ((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * X * (((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * Y)
        = (((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Real.log N) : ℝ) : ℂ)⁻¹) *
          (X * Y) by ring, hsq, Complex.ofReal_div]
    field_simp
  rw [hnorm]
  simp only [X, Y]
  simp only [div_mul_eq_div_div] at hval ⊢
  linear_combination (-(U ^ 2 / ρ / (1 - ρ))) * hpow - hval

/-- `Re 1/(ρ(1 − ρ)) > 0` on the open strip. -/
theorem re_inv_mul_one_sub_pos {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    0 < (1 / (ρ * (1 - ρ))).re := by
  have hre : (ρ * (1 - ρ)).re = ρ.re * (1 - ρ.re) + ρ.im * ρ.im := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hpos : 0 < (ρ * (1 - ρ)).re := by rw [hre]; nlinarith [mul_self_nonneg ρ.im]
  have hne : ρ * (1 - ρ) ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos; exact lt_irrefl 0 hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)

/-- `∫ g(u/w)² = w ∫ g²`. -/
theorem integral_atomDilate_sq (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ u, atomDilate φ w u ^ 2 = w * ∫ u, φ u ^ 2 := by
  simpa [atomDilate, smul_eq_mul, abs_of_pos hw] using
    Measure.integral_comp_div (fun v => φ v ^ 2) w

theorem paperFT_cx_zero (φ : ℝ → ℝ) : paperFT (cx φ) 0 = ((∫ u, φ u : ℝ) : ℂ) := by
  simp only [paperFT, cx, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_ofReal

/-- The contribution of a point `ρ` to the normalized complete form of the packet
`Σ_{e∈E} y_e r_e` at overlap `c` and horizon `N`. -/
def bulkLedger (Z : ZeroConfig) (φ : ℝ → ℝ) (E : Finset ℕ) (y : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (ρ : ℂ) : ℂ :=
  Z.Wsummand (cx (atomicTest N (packetWeights E y N) (atomDilate φ (c / N))))
      (cx (atomicTest N (packetWeights E y N) (atomDilate φ (c / N)))) ρ /
    ((∫ u, atomDilate φ (c / N) u ^ 2 : ℝ) : ℂ)

/-- The ledger entry factors into the multiplicity, the atom factor and the ledger factor. -/
theorem log_div_mul_bulkLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (E : Finset ℕ) (y : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    ((Real.log N / c : ℝ) : ℂ) * bulkLedger Z φ E y c N ρ =
      (Z.mult ρ : ℂ) * (paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) *
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
      (((Real.log N / N : ℝ) : ℂ) * (dirichletPoly N (packetWeights E y N) (gammaOf ρ) *
        dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : Continuous (atomDilate φ (c / N)) := by unfold atomDilate; fun_prop
  have hgc : HasCompactSupport (atomDilate φ (c / N)) := hasCompactSupport_atomDilate hw.ne' hφc
  unfold bulkLedger
  rw [Wsummand_atomicTest Z hg hgc, paperFT_atomDilate hw, paperFT_atomDilate hw,
    conj_dirichletPoly_conj_gammaOf, integral_atomDilate_sq φ hw]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hI : ((∫ u, φ u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ2.ne'
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

/-- **Bulk zero ledger.** Along every overlap schedule with `c_N/N → 0`, a point `ρ` of the open
strip contributes `(c_N/log N) m_ρ ((∫φ)²/∫φ²) y_1²/(ρ(1 − ρ)) + o(c_N/log N)` to the normalized
complete form of a fixed conductor packet. -/
theorem tendsto_bulkLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (E : Finset ℕ) (y : ℕ → ℝ) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((Real.log N / c N : ℝ) : ℂ) * bulkLedger Z φ E y (c N) N ρ) atTop
      (𝓝 ((Z.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))))) := by
  have hF : Continuous (paperFT (cx φ)) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)).continuous
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using hcN.ofReal
  have h1 : Tendsto (fun N : ℕ => paperFT (cx φ) (((c N / N : ℝ) : ℂ) * gammaOf ρ)) atTop
      (𝓝 (paperFT (cx φ) 0)) := by
    have := (hw.mul_const (gammaOf ρ))
    rw [zero_mul] at this
    exact (hF.tendsto 0).comp this
  have h2 : Tendsto (fun N : ℕ => conj (paperFT (cx φ) (((c N / N : ℝ) : ℂ) * conj (gammaOf ρ))))
      atTop (𝓝 (conj (paperFT (cx φ) 0))) := by
    have := (hw.mul_const (conj (gammaOf ρ)))
    rw [zero_mul] at this
    exact (Complex.continuous_conj.tendsto _).comp ((hF.tendsto 0).comp this)
  have hlim := (((h1.mul h2).const_mul (Z.mult ρ : ℂ)).div_const ((∫ u, φ u ^ 2 : ℝ) : ℂ)).mul
    (tendsto_packetLedger hρ0 hρ1 E y)
  rw [paperFT_cx_zero, Complex.conj_ofReal] at hlim
  have hval : (Z.mult ρ : ℂ) * (((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) * (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) =
      (Z.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [log_div_mul_bulkLedger Z hφ hφc hφ2 E y (hc N) hN ρ]

/-- **The bulk ledger at the critical curve.** Along `c_N⁸/log N → K`, the contribution of a
point `ρ` of the open strip to a fixed packet, rescaled by the margin exponent `c_N⁷`, tends to
`K m_ρ ((∫φ)²/∫φ²) y_1²/(ρ(1 − ρ))`. -/
theorem tendsto_bulkLedger_criticalCurve (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (E : Finset ℕ) (y : ℕ → ℝ) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) {K : ℝ}
    (hK : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => ((c N ^ 7 : ℝ) : ℂ) * bulkLedger Z φ E y (c N) N ρ) atTop
      (𝓝 ((K : ℂ) * ((Z.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))))) := by
  have hlim := (Complex.continuous_ofReal.tendsto K |>.comp hK).mul
    (tendsto_bulkLedger Z hφ hφc hφ2 hρ0 hρ1 E y hc hcN)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hc0 := hc N
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
