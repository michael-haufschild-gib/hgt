import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGenusLawForcesSimpleZeros
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheThetaH0OfSpecZ

/-!
# The window genus is a Young conjugate

The **window genus** `g(A, ε)` is the largest dimension of a space of Hodge-class tests in a window
of length `A` on which `|Q| ≤ ε‖·‖²` (`windowGenus`; the genus function of ACS at level `A/2`). It
is the effective dimension of the window `h¹` at threshold `ε`: the rank of the lattice that must
carry the sections of the window.

Its main term is a Legendre (Young) transform. A window of length `A = 2L` and a band `[−T, T]`
have Shannon number `(2L)(2T)/2π`; every zero of height `≤ T` costs one condition on each side, and
the zeros up to height `T` number `N₀(T) = (T/2π)(log(T/2π) − 1)` to main order. The surplus is
maximal at the Landau height `T = 2πe^{2L}` and equals `2e^{2L}`:

* **Young** (`young_le`, `young_eq_iff`): `2Lx − x(log x − 1) ≤ e^{2L}` for `x > 0`, with equality
  iff `x = e^{2L}`.
* **The genus main term** (`isGreatest_shannonSurplus`, `shannonSurplus_eq_iff`):
  `sup_T [(2L)(2T)/2π − 2N₀(T)] = 2e^{2L}`, attained exactly at `T = 2πe^{2L}`, the Landau height
  of ACS at `η = 0` (`landauHeight_zero`).
* **The window genus attains it** (`exists_windowGenus_ge`): `g(A, ε_η) ≥ (2 − η)e^{A}` plus twice
  the multiplicity excess, for all long windows.
* **It is the theta count of `Spec ℤ`** (`tendsto_exp_arithH0_div_exp`):
  `e^{A} = exp h⁰_ℤ(A)·(1 + o(1))`, the Gaussian count of the integers at degree `A`. The window of
  length `A` carries the integer lattice of degree `A`, counted twice; the Gamma factor enters as
  the zero density whose Young conjugate this is.
-/

noncomputable section

open Filter Topology Real

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry Zeta23

/-! ### Young's inequality for `x log x − x` and `e^y` -/

/-- **Young**: `2Lx − x(log x − 1) ≤ e^{2L}` for `x > 0`. -/
theorem young_le (L : ℝ) {x : ℝ} (hx : 0 < x) :
    2 * L * x - x * (Real.log x - 1) ≤ Real.exp (2 * L) := by
  have h := Real.add_one_le_exp (2 * L - Real.log x)
  rw [Real.exp_sub, Real.exp_log hx, le_div_iff₀ hx] at h
  nlinarith

/-- Equality in Young's inequality holds exactly at `x = e^{2L}`. -/
theorem young_eq_iff (L : ℝ) {x : ℝ} (hx : 0 < x) :
    2 * L * x - x * (Real.log x - 1) = Real.exp (2 * L) ↔ x = Real.exp (2 * L) := by
  constructor
  · intro h
    by_contra hne
    have hlog : 2 * L - Real.log x ≠ 0 := fun h0 => hne (by
      rw [show 2 * L = Real.log x by linarith, Real.exp_log hx])
    have hlt := Real.add_one_lt_exp hlog
    rw [Real.exp_sub, Real.exp_log hx, lt_div_iff₀ hx] at hlt
    nlinarith
  · rintro rfl
    rw [Real.log_exp]; ring

/-! ### The Shannon surplus -/

/-- The main term `N₀(T) = (T/2π)(log(T/2π) − 1)` of the zero count up to height `T`. -/
def zeroCountMain (T : ℝ) : ℝ := T / (2 * π) * (Real.log (T / (2 * π)) - 1)

/-- The **Shannon surplus** of a window of length `2L` against the zeros up to height `T`:
`(2L)(2T)/2π − 2N₀(T)`. -/
def shannonSurplus (L T : ℝ) : ℝ := 2 * L * (2 * T) / (2 * π) - 2 * zeroCountMain T

theorem shannonSurplus_eq (L T : ℝ) :
    shannonSurplus L T =
      2 * (2 * L * (T / (2 * π)) - T / (2 * π) * (Real.log (T / (2 * π)) - 1)) := by
  unfold shannonSurplus zeroCountMain; ring

/-- **The genus main term is the Young conjugate of the zero density**: the Shannon surplus is at
most `2e^{2L}` and attains it. -/
theorem isGreatest_shannonSurplus (L : ℝ) :
    IsGreatest {S | ∃ T : ℝ, 0 < T ∧ S = shannonSurplus L T} (2 * Real.exp (2 * L)) := by
  refine ⟨⟨2 * π * Real.exp (2 * L), by positivity, ?_⟩, ?_⟩
  · rw [shannonSurplus_eq, show 2 * π * Real.exp (2 * L) / (2 * π) = Real.exp (2 * L) by
      field_simp, (young_eq_iff L (Real.exp_pos _)).mpr rfl]
  · rintro S ⟨T, hT, rfl⟩
    rw [shannonSurplus_eq]
    have := young_le L (x := T / (2 * π)) (by positivity)
    linarith

/-- The surplus is maximal exactly at the Landau height `T = 2πe^{2L}`. -/
theorem shannonSurplus_eq_iff (L : ℝ) {T : ℝ} (hT : 0 < T) :
    shannonSurplus L T = 2 * Real.exp (2 * L) ↔ T = 2 * π * Real.exp (2 * L) := by
  rw [shannonSurplus_eq]
  have h := young_eq_iff L (x := T / (2 * π)) (by positivity)
  constructor
  · intro he
    have h2 := h.mp (by linarith)
    rw [div_eq_iff (by positivity)] at h2
    linarith
  · intro he
    have : T / (2 * π) = Real.exp (2 * L) := by rw [he]; field_simp
    linarith [h.mpr this]

/-- The Landau height at `η = 0` is the Young maximizer `2πe^{2L}`. -/
theorem landauHeight_zero (L : ℝ) : landauHeight 0 L = 2 * π * Real.exp (2 * L) := by
  simp [landauHeight]

/-! ### The window genus -/

/-- The **window genus** `g(A, ε)`: the genus function of `ℤ` at level `A/2`. -/
def windowGenus (A ε : ℝ) : ℕ := genusFunction (A / 2) ε

/-- **The window genus attains the Young conjugate**: for every `0 < η ≤ 1` and every long window,
`g(A, ε_η) ≥ (2 − η)e^{A} + 2(N − N_d)` at the Landau height. -/
theorem exists_windowGenus_ge {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
      (2 - η) * Real.exp A + 2 * ((zetaZeroConfig.N 0 (landauHeight η (A / 2)) : ℝ) -
        zetaZeroConfig.Nd 0 (landauHeight η (A / 2))) ≤
        (windowGenus A (naturalThreshold η (A / 2)) : ℝ) := by
  obtain ⟨L₀, hL₀⟩ := genusFunction_ge_distinct hη0 hη1
  refine ⟨2 * L₀, fun A hA => ?_⟩
  have h := hL₀ (A / 2) (by linarith)
  rwa [show 2 * (A / 2) = A by ring] at h

/-- **The genus main term is the theta count of `Spec ℤ`**: `exp h⁰_ℤ(A)/e^{A} → 1`. -/
theorem tendsto_exp_arithH0_div_exp :
    Tendsto (fun A => Real.exp (arithH0 A) / Real.exp A) atTop (𝓝 1) := by
  have h := (Real.continuous_exp.tendsto 0).comp tendsto_arithH0_sub_atTop
  rw [Real.exp_zero] at h
  refine h.congr fun A => ?_
  simp only [Function.comp, Real.exp_sub]

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
