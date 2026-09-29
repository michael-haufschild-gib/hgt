import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH
import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimeTransport
import GaloisForLFunctions.RHTower.SelbergTruncatedVonMangoldtKreinCompletion
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleDiagonalBounds
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundVariance

/-!
# One literal parity pole per aperture decides RH, and Weil-positive supersystems force RH

The restricted Weil quadratic on the two literal pole vectors `e^{±x/2}` of the aperture `[−a,a]`
has parity energies `2(A + rC)`, `r = ±1`, where `A` is the diagonal and `C` the cross entry. RH is
equivalent to nonnegativity of both at every aperture (`riemannHypothesis_iff_parityPole_nonneg`).

* **One parity suffices** (`riemannHypothesis_iff_evenParityPole_nonneg`,
  `riemannHypothesis_iff_oddParityPole_nonneg`). The even energy bounds the integrated Chebyshev
  deficit `D(2a)` from below by `−B e^a`, the odd energy bounds it from above. Either one-sided bound
  gives RH by Landau's theorem (`riemannHypothesis_of_logChebyshevDeficitPrimitive_ge`,
  `riemannHypothesis_of_logChebyshevDeficitPrimitive_le`).
* **Supersystems** (`riemannHypothesis_of_evenParityPole_supersystem`). Every visible prime atom
  `n ≤ e^{2a}` acts on the even pole with the nonnegative energy
  `2(2(e^a/n − e^{−a}) + (2a − log n)(1 + 1/n))`. So enlarging the weights above `Λ` can only lower
  the even-pole energy. If a weight system `λ ≥ Λ` has nonnegative even-pole Weil energy at every
  aperture, then so does `Λ`, and RH holds.

The supersystem theorem is the Landau step of order rigidity: a Weil-positive completion of ζ's
archimedean datum that majorizes the von Mangoldt weights forces RH.
-/

open Complex Set
open scoped InnerProduct BigOperators
open GaloisForLFunctions.RHTower

noncomputable section
namespace RHTower

/-! ## One-sided deficit bounds from a single parity -/

theorem ccmPoleIntegratedChebyshevDeficit_ge_of_evenParity (a : SuzukiPositiveAperture)
    (h : 0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1)) :
    -(ccmWeilPoleUniformDeficitBound * Real.exp a.1) ≤ ccmPoleIntegratedChebyshevDeficit a := by
  rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl)] at h
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hA := abs_le.mp (abs_ccmWeilPoleDiagonal_le a)
  have hB := ccmGammaPoleCrossBoundaryMass_le a
  have ha := a.property
  have he : 1 ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hC : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hBC := mul_le_mul_of_nonneg_left he hC
  have hKC := mul_le_mul_of_nonneg_left hae hK
  unfold ccmWeilPoleUniformDeficitBound
  nlinarith

theorem ccmPoleIntegratedChebyshevDeficit_le_of_oddParity (a : SuzukiPositiveAperture)
    (h : 0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) :
    ccmPoleIntegratedChebyshevDeficit a ≤ ccmWeilPoleUniformDeficitBound * Real.exp a.1 := by
  rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl)] at h
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hA := abs_le.mp (abs_ccmWeilPoleDiagonal_le a)
  have hB := ccmGammaPoleCrossBoundaryMass_le a
  have ha := a.property
  have he : 1 ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hC : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hBC := mul_le_mul_of_nonneg_left he hC
  have hKC := mul_le_mul_of_nonneg_left hae hK
  unfold ccmWeilPoleUniformDeficitBound
  nlinarith

/-- The deficit primitive at `T > 0` is the aperture deficit at `a = T/2`. -/
private theorem deficitPrimitive_eq_aperture {T : ℝ} (hT : 0 < T) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmPoleIntegratedChebyshevDeficit ⟨T / 2, by linarith⟩ := by
  rw [ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive]
  congr 1
  change T = 2 * (T / 2)
  ring

/-! ## One parity pole decides RH -/

/-- **Even parity pole.** Nonnegative Weil energy of `e^{x/2} + e^{−x/2}` on every aperture forces
RH. -/
theorem riemannHypothesis_of_evenParityPole_nonneg
    (h : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_ge
    (B := ccmWeilPoleUniformDeficitBound) fun T hT => ?_
  rcases eq_or_lt_of_le hT with h0 | hpos
  · rw [← h0, ccmLogChebyshevDeficitPrimitive, intervalIntegral.integral_same]
    have := ccmWeilPoleUniformDeficitBound_pos
    have := Real.exp_pos (0 / 2 : ℝ)
    nlinarith
  · rw [deficitPrimitive_eq_aperture hpos]
    exact ccmPoleIntegratedChebyshevDeficit_ge_of_evenParity ⟨T / 2, by linarith⟩ (h _)

/-- **Odd parity pole.** Nonnegative Weil energy of `e^{x/2} − e^{−x/2}` on every aperture forces
RH. -/
theorem riemannHypothesis_of_oddParityPole_nonneg
    (h : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_le
    (B := ccmWeilPoleUniformDeficitBound) fun T hT => ?_
  rcases eq_or_lt_of_le hT with h0 | hpos
  · rw [← h0, ccmLogChebyshevDeficitPrimitive, intervalIntegral.integral_same]
    have := ccmWeilPoleUniformDeficitBound_pos
    have := Real.exp_pos (0 / 2 : ℝ)
    positivity
  · rw [deficitPrimitive_eq_aperture hpos]
    exact ccmPoleIntegratedChebyshevDeficit_le_of_oddParity ⟨T / 2, by linarith⟩ (h _)

/-- RH is exactly nonnegativity of the even literal pole at every aperture. -/
theorem riemannHypothesis_iff_evenParityPole_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) :=
  ⟨fun hRH a => ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _,
    riemannHypothesis_of_evenParityPole_nonneg⟩

/-- RH is exactly nonnegativity of the odd literal pole at every aperture. -/
theorem riemannHypothesis_iff_oddParityPole_nonneg :
    RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) :=
  ⟨fun hRH a => ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _,
    riemannHypothesis_of_oddParityPole_nonneg⟩

/-! ## Weil-positive supersystems -/

/-- The visible cutoff `n ≤ ⌊e^{2a}⌋` means `log n ≤ 2a`. -/
private theorem log_le_of_le_floor (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) : Real.log n ≤ 2 * a.1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n : ℝ) ≤ Real.exp (2 * a.1) :=
    le_trans (by exact_mod_cast hN) (Nat.floor_le (Real.exp_pos _).le)
  rw [← Real.exp_le_exp, Real.exp_log hnR]
  exact hle

/-- Every visible prime atom has nonnegative energy on the even literal pole. -/
theorem evenParityPole_atom_nonneg (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) :
    0 ≤ (1 / Real.sqrt n) *
      (inner ℂ (logTranslationCLM (Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1 +
        inner ℂ (logTranslationCLM (-Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1).re := by
  have hv := log_le_of_le_floor a hn hN
  set f := ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1) with hf
  have hT := inner_ccmPrimeTransportOperator a n f f
  have hpar := ccmPrimeTransport_polar_parity a hn hv (r := 1) (Or.inl rfl)
  rw [ccmArchimedeanFormToAperture_polarParity] at hf
  rw [hf] at hT
  rw [hT] at hpar
  have hre := congrArg Complex.re hpar
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  rw [hf, hre]
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : Real.exp (-a.1) ≤ Real.exp a.1 / n := by
    rw [le_div_iff₀ hnR, ← Real.exp_log hnR, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hl : 0 ≤ 2 * a.1 - Real.log n := by linarith
  have hinv : 0 < 1 + 1 / (n : ℝ) := by positivity
  have := mul_nonneg hl hinv.le
  nlinarith

/-- Raising the weights above `Λ` can only lower the even-pole Weil energy. -/
theorem weilSourceQuadraticWith_evenParity_le_of_ge {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ (ccmPolarParityFormVector a 1) ≤
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    le_rfl (fun n _ _ => rfl)]
  unfold ccmRestrictedWeilSourceQuadraticWith
  simp only
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1 +
            inner ℂ (logTranslationCLM (-Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1).re ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        lam n * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1 +
            inner ℂ (logTranslationCLM (-Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a 1)).1).re := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hatom := evenParityPole_atom_nonneg a hn2 hnN
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hge n hn2) hatom
  linarith

/-- **Weil-positive supersystems force RH.** If weights `λ ≥ Λ` (on `n ≥ 2`) give nonnegative
restricted Weil energy on the even literal pole at every aperture, then RH holds. -/
theorem riemannHypothesis_of_evenParityPole_supersystem {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n)
    (hpos : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a 1)) :
    RiemannHypothesis :=
  riemannHypothesis_of_evenParityPole_nonneg fun a =>
    (hpos a).trans (weilSourceQuadraticWith_evenParity_le_of_ge hge a)

/-- RH is equivalent to the existence of a Weil-positive (on the even literal poles) weight
system that majorizes the von Mangoldt weights. -/
theorem riemannHypothesis_iff_exists_evenParityPole_supersystem :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ,
      (∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      ∀ a : SuzukiPositiveAperture,
        0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
          (ccmPolarParityFormVector a 1) := by
  constructor
  · intro hRH
    refine ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ), fun n _ => le_rfl, fun a => ?_⟩
    rw [ccmRestrictedWeilSourceQuadraticWith_eq a _ le_rfl (fun n _ _ => rfl)]
    exact ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _
  · rintro ⟨lam, hge, hpos⟩
    exact riemannHypothesis_of_evenParityPole_supersystem hge hpos

/-! ## Weil-positive nonnegative subsystems -/

/-- Every visible prime atom acts on the odd literal pole with energy at most `4e^a/n`. -/
theorem oddParityPole_atom_le (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ ⌊Real.exp (2 * a.1)⌋₊) :
    (1 / Real.sqrt n) *
      (inner ℂ (logTranslationCLM (Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1 +
        inner ℂ (logTranslationCLM (-Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1).re ≤
      4 * (Real.exp a.1 / n) := by
  have hv := log_le_of_le_floor a hn hN
  set f := ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1)) with hf
  have hT := inner_ccmPrimeTransportOperator a n f f
  have hpar := ccmPrimeTransport_polar_parity a hn hv (r := -1) (Or.inr rfl)
  rw [ccmArchimedeanFormToAperture_polarParity] at hf
  rw [hf] at hT
  rw [hT] at hpar
  have hre := congrArg Complex.re hpar
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  rw [hf, hre]
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 ≤ 2 * a.1 - Real.log n := by linarith
  have hinv : 0 < 1 + 1 / (n : ℝ) := by positivity
  have := mul_nonneg hl hinv.le
  have hm := Real.exp_pos (-a.1)
  nlinarith

/-- For a nonnegative subsystem, the odd-pole Weil energy exceeds that of `Λ` by at most
`4 e^a Σ_{n ≤ e^{2a}} Λ(n)/n`. -/
theorem weilSourceQuadraticWith_oddParity_le_of_subsystem {lam : ℕ → ℝ}
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ (ccmPolarParityFormVector a (-1)) ≤
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) +
        4 * Real.exp a.1 * ccmReciprocalMangoldtCumulative (Real.exp (2 * a.1)) := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    le_rfl (fun n _ _ => rfl)]
  unfold ccmRestrictedWeilSourceQuadraticWith ccmReciprocalMangoldtCumulative
  simp only
  rw [Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1 +
            inner ℂ (logTranslationCLM (-Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1).re ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (lam n * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1 +
            inner ℂ (logTranslationCLM (-Real.log n)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
              (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1).re +
          4 * Real.exp a.1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n)) := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hatom := oddParityPole_atom_le a hn2 hnN
    have hΛ0 : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hu0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) - lam n := by linarith [hle n hn2]
    have hul : (ArithmeticFunction.vonMangoldt n : ℝ) - lam n ≤ ArithmeticFunction.vonMangoldt n := by
      linarith [h0 n hn2]
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hq : 0 ≤ 4 * (Real.exp a.1 / n) := by positivity
    have key := mul_le_mul hul hatom
    set R := (1 / Real.sqrt n) *
      (inner ℂ (logTranslationCLM (Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1 +
        inner ℂ (logTranslationCLM (-Real.log n)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1)
          (ccmArchimedeanFormToAperture a (ccmPolarParityFormVector a (-1))).1).re with hR
    have h1 : ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * R ≤
        ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (4 * (Real.exp a.1 / n)) :=
      mul_le_mul_of_nonneg_left hatom hu0
    have h2 : ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (4 * (Real.exp a.1 / n)) ≤
        (ArithmeticFunction.vonMangoldt n : ℝ) * (4 * (Real.exp a.1 / n)) :=
      mul_le_mul_of_nonneg_right hul hq
    have h3 : (ArithmeticFunction.vonMangoldt n : ℝ) * (4 * (Real.exp a.1 / n)) =
        4 * Real.exp a.1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by ring
    nlinarith [key]
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- The one-sided deficit bound supplied by a nonnegative subsystem with odd-pole positivity. -/
theorem ccmPoleIntegratedChebyshevDeficit_le_of_oddParity_subsystem {lam : ℕ → ℝ}
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) (a : SuzukiPositiveAperture)
    (h : 0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
      (ccmPolarParityFormVector a (-1))) :
    ccmPoleIntegratedChebyshevDeficit a ≤
      (ccmWeilPoleUniformDeficitBound + 2 * (Real.log 4 + 5) + 2) * (1 + 2 * a.1) *
        Real.exp a.1 := by
  have hQ := le_trans h (weilSourceQuadraticWith_oddParity_le_of_subsystem h0 hle a)
  rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl)] at hQ
  have hcum : ccmReciprocalMangoldtCumulative (Real.exp (2 * a.1)) ≤ 2 * a.1 + (Real.log 4 + 5) := by
    have hE := abs_le.mp (abs_ccmReciprocalMangoldtError_le (show 0 ≤ 2 * a.1 by linarith [a.property]))
    unfold ccmReciprocalMangoldtError at hE
    linarith [hE.2]
  have hd := abs_le.mp (abs_integratedChebyshevDeficit_sub_weilPoleCross_le a)
  have hA := abs_le.mp (abs_ccmWeilPoleDiagonal_le a)
  have hB := ccmGammaPoleCrossBoundaryMass_le a
  have ha := a.property
  have he : 1 ≤ Real.exp a.1 := Real.one_le_exp ha.le
  have hep := Real.exp_pos a.1
  have hae : a.1 ≤ Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ 2 * Real.log 2 + Real.pi + 1 := by positivity
  have hK : 0 ≤ |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5 := by
    positivity
  have hU := ccmWeilPoleUniformDeficitBound_pos
  have hBC := mul_le_mul_of_nonneg_left he hC
  have hKC := mul_le_mul_of_nonneg_left hae hK
  have hcumE := mul_le_mul_of_nonneg_left hcum (show 0 ≤ 4 * Real.exp a.1 by positivity)
  have hae2 : a.1 ≤ a.1 * Real.exp a.1 := by nlinarith
  unfold ccmWeilPoleUniformDeficitBound at hU ⊢
  nlinarith

/-- **Weil-positive nonnegative subsystems force RH.** If weights `0 ≤ λ ≤ Λ` (on `n ≥ 2`) give
nonnegative restricted Weil energy on the odd literal pole at every aperture, then RH holds. No
density hypothesis is needed: the literal pole vectors carry ζ's pole weight themselves. -/
theorem riemannHypothesis_of_oddParityPole_subsystem {lam : ℕ → ℝ}
    (h0 : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ))
    (hpos : ∀ a : SuzukiPositiveAperture,
      0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarParityFormVector a (-1))) :
    RiemannHypothesis := by
  set B := ccmWeilPoleUniformDeficitBound + 2 * (Real.log 4 + 5) + 2 with hBdef
  have hB0 : 0 ≤ B := by
    have := ccmWeilPoleUniformDeficitBound_pos
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    rw [hBdef]; positivity
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_le_mul (B := B) fun T hT => ?_
  rcases eq_or_lt_of_le hT with h0T | hpos'
  · rw [← h0T, ccmLogChebyshevDeficitPrimitive, intervalIntegral.integral_same]
    have := Real.exp_pos (0 / 2 : ℝ)
    positivity
  · rw [deficitPrimitive_eq_aperture hpos']
    have h := ccmPoleIntegratedChebyshevDeficit_le_of_oddParity_subsystem h0 hle
      ⟨T / 2, by linarith⟩ (hpos _)
    have hT2 : (1 + 2 * (T / 2)) = 1 + T := by ring
    simpa only [hT2] using h

/-- RH is equivalent to the existence of a nonnegative subsystem of the von Mangoldt weights with
nonnegative odd-pole Weil energy at every aperture. -/
theorem riemannHypothesis_iff_exists_oddParityPole_subsystem :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ,
      (∀ n, 2 ≤ n → 0 ≤ lam n) ∧
      (∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
      ∀ a : SuzukiPositiveAperture,
        0 ≤ ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
          (ccmPolarParityFormVector a (-1)) := by
  constructor
  · intro hRH
    refine ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      fun n _ => ArithmeticFunction.vonMangoldt_nonneg, fun n _ => le_rfl, fun a => ?_⟩
    rw [ccmRestrictedWeilSourceQuadraticWith_eq a _ le_rfl (fun n _ _ => rfl)]
    exact ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a _
  · rintro ⟨lam, h0, hle, hpos⟩
    exact riemannHypothesis_of_oddParityPole_subsystem h0 hle hpos

end RHTower
