import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheTwoCollarFormOfAStage

/-!
# The kick is the collar reflection

On a window of length `A` and level `N + 1` the kick of the stage is `−2w c_H(ℓ)`,
`c_H(ℓ) = ∫_{−A}^{−ℓ} H(u)H(u + ℓ) du`, `ℓ = log(N + 1)`. Let `R u = −A − ℓ − u` be the reflection of
the left collar `L = [−A, −ℓ]` about its midpoint (`collarReflection`).

* **Collar Rosati form** (`corr_eq_collar_windowInvolution`): for every window test,
  `c_H(ℓ) = ∫_L H(u)·(σ_AH)(Ru) du`: the kick pairs `H` with its Rosati image `σ_AH`, read on one
  collar through `R`.
* **Sectors** (`corr_eq_of_even`, `corr_eq_of_odd`). On `σ_A`-even tests
  `c_H(ℓ) = ¼∫_L (H + H∘R)² − ¼∫_L (H − H∘R)²`, on `σ_A`-odd tests the negative. Hence
  (`weilQuad_eq_of_even`, `weilQuad_eq_of_odd`)

  `Q(H) = Q_N(H) − (w/2)∫_L(H + H∘R)² + (w/2)∫_L(H − H∘R)²` on even tests,
  `Q(H) = Q_N(H) + (w/2)∫_L(H + H∘R)² − (w/2)∫_L(H − H∘R)²` on odd tests.

  The kick is a **positive source** exactly on the even–antisymmetric and the odd–symmetric collar
  data, and a cost on the other two sectors.
* **Parity splitting** (`weilPair_even_odd`, `window_nonneg_iff_sectors`): even and odd tests are
  `Q`-orthogonal, so a window is nonnegative iff it is nonnegative on each `σ_A`-sector.
* **The frozen datum pre-installs the sign** (`collar_antisymmetric_of_frozen_negative_even`,
  `collar_symmetric_of_frozen_negative_odd`): on a nonnegative window, an even test that the frozen
  form makes negative carries more `R`-antisymmetric than `R`-symmetric mass on its left collar; an
  odd one carries more `R`-symmetric mass. The negative frozen directions that the newest fold
  repairs (WTZ `exists_first_stage_positive_exit_loan_failure`) are forced into these two sectors.
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ WindowTowerOfSpecZ
  SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri RHTower.WeilMarkovPole

variable {A ℓ : ℝ} {H : ℝ → ℝ}

/-- The **collar reflection** `R u = −A − ℓ − u`: the reflection of the left collar `[−A, −ℓ]` about
its midpoint. -/
def collarReflection (A ℓ u : ℝ) : ℝ := -A - ℓ - u

theorem continuous_collarReflection (A ℓ : ℝ) : Continuous (collarReflection A ℓ) := by
  unfold collarReflection; fun_prop

/-- **The kick is a collar Rosati form**: `c_H(ℓ) = ∫_{−A}^{−ℓ} H(u)·(σ_AH)(Ru) du`. -/
theorem corr_eq_collar_windowInvolution (hH : IsWindowTest A H) (hℓA : ℓ ≤ A) :
    corr H ℓ = ∫ u in (-A)..(-ℓ), H u * windowInvolution A H (collarReflection A ℓ u) := by
  rw [corr_eq_intervalIntegral hH hℓA]
  congr 1
  funext u
  simp only [windowInvolution, collarReflection]
  ring_nf

/-- On a `σ_A`-even test the kick reads one collar through its reflection. -/
theorem corr_eq_collar_of_even (hH : IsWindowTest A H) (hσ : windowInvolution A H = H)
    (hℓA : ℓ ≤ A) : corr H ℓ = ∫ u in (-A)..(-ℓ), H u * H (collarReflection A ℓ u) := by
  rw [corr_eq_collar_windowInvolution hH hℓA, hσ]

/-- On a `σ_A`-odd test the kick reads minus the collar reflection form. -/
theorem corr_eq_collar_of_odd (hH : IsWindowTest A H) (hσ : windowInvolution A H = fun u => -H u)
    (hℓA : ℓ ≤ A) : corr H ℓ = -∫ u in (-A)..(-ℓ), H u * H (collarReflection A ℓ u) := by
  rw [corr_eq_collar_windowInvolution hH hℓA, hσ, ← intervalIntegral.integral_neg]
  congr 1
  funext u
  ring

/-- The collar reflection form, polarized: `∫_L H·H∘R = ¼∫_L(H + H∘R)² − ¼∫_L(H − H∘R)²`. -/
theorem integral_collar_polarize (hH : Continuous H) (A ℓ : ℝ) :
    ∫ u in (-A)..(-ℓ), H u * H (collarReflection A ℓ u) =
      (∫ u in (-A)..(-ℓ), (H u + H (collarReflection A ℓ u)) ^ 2) / 4 -
        (∫ u in (-A)..(-ℓ), (H u - H (collarReflection A ℓ u)) ^ 2) / 4 := by
  have hR : Continuous fun u => H (collarReflection A ℓ u) :=
    hH.comp (continuous_collarReflection A ℓ)
  have i1 : IntervalIntegrable (fun u => (H u + H (collarReflection A ℓ u)) ^ 2) volume (-A) (-ℓ) :=
    ((hH.add hR).pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => (H u - H (collarReflection A ℓ u)) ^ 2) volume (-A) (-ℓ) :=
    ((hH.sub hR).pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
    ← intervalIntegral.integral_sub (i1.div_const 4) (i2.div_const 4)]
  congr 1
  funext u
  ring

/-- **The kick on even tests**: `c_H(ℓ) = ¼∫_L(H + H∘R)² − ¼∫_L(H − H∘R)²`. -/
theorem corr_eq_of_even (hH : IsWindowTest A H) (hσ : windowInvolution A H = H) (hℓA : ℓ ≤ A) :
    corr H ℓ = (∫ u in (-A)..(-ℓ), (H u + H (collarReflection A ℓ u)) ^ 2) / 4 -
      (∫ u in (-A)..(-ℓ), (H u - H (collarReflection A ℓ u)) ^ 2) / 4 := by
  rw [corr_eq_collar_of_even hH hσ hℓA, integral_collar_polarize hH.continuous]

/-- **The kick on odd tests**: `c_H(ℓ) = ¼∫_L(H − H∘R)² − ¼∫_L(H + H∘R)²`. -/
theorem corr_eq_of_odd (hH : IsWindowTest A H) (hσ : windowInvolution A H = fun u => -H u)
    (hℓA : ℓ ≤ A) :
    corr H ℓ = (∫ u in (-A)..(-ℓ), (H u - H (collarReflection A ℓ u)) ^ 2) / 4 -
      (∫ u in (-A)..(-ℓ), (H u + H (collarReflection A ℓ u)) ^ 2) / 4 := by
  rw [corr_eq_collar_of_odd hH hσ hℓA, integral_collar_polarize hH.continuous]
  ring

/-- **Weil's form on an even test across a stage**:
`Q(H) = Q_N(H) − (w/2)∫_L(H + H∘R)² + (w/2)∫_L(H − H∘R)²`. -/
theorem weilQuad_eq_of_even {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) (hσ : windowInvolution A H = H) :
    weilQuad H = stageForm N H -
      primeJumpWeight (N + 1) / 2 *
        (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
          (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) +
      primeJumpWeight (N + 1) / 2 *
        (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
          (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) := by
  rw [weilQuad_eq_stageForm_sub_corr hH hN hA,
    corr_eq_of_even hH hσ (log_succ_le_of_windowLevel hA)]
  ring

/-- **Weil's form on an odd test across a stage**:
`Q(H) = Q_N(H) + (w/2)∫_L(H + H∘R)² − (w/2)∫_L(H − H∘R)²`. -/
theorem weilQuad_eq_of_odd {N : ℕ} (hN : 1 ≤ N) (hA : windowLevel A = N + 1)
    (hH : IsWindowTest A H) (hσ : windowInvolution A H = fun u => -H u) :
    weilQuad H = stageForm N H +
      primeJumpWeight (N + 1) / 2 *
        (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
          (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) -
      primeJumpWeight (N + 1) / 2 *
        (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
          (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) := by
  rw [weilQuad_eq_stageForm_sub_corr hH hN hA,
    corr_eq_of_odd hH hσ (log_succ_le_of_windowLevel hA)]
  ring

/-! ### Parity splitting -/

/-- Even and odd tests are `Q`-orthogonal. -/
theorem weilPair_even_odd {E O : ℝ → ℝ} (hE : E ∈ realTests) (hO : O ∈ realTests)
    (he : windowInvolution A E = E) (ho : windowInvolution A O = fun u => -O u) :
    weilPair E O = 0 := by
  have hp := weilQuad_plane hE hO 1 1
  have hm := weilQuad_plane hE hO 1 (-1)
  have hσ : windowInvolution A (fun u => 1 * E u + 1 * O u) = fun u => 1 * E u + -1 * O u := by
    funext u
    have e1 := congrFun he u
    have o1 := congrFun ho u
    simp only [windowInvolution] at e1 o1 ⊢
    rw [e1, o1]
    ring
  have hQ := weilQuad_windowInvolution A (fun u => 1 * E u + 1 * O u)
  rw [hσ, hm, hp] at hQ
  linarith

/-- The even part `(H + σH)/2` of a window test. -/
def evenPart (A : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => (1 / 2) * H u + (1 / 2) * windowInvolution A H u

/-- The odd part `(H − σH)/2` of a window test. -/
def oddPart (A : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => (1 / 2) * H u + (-1 / 2) * windowInvolution A H u

theorem evenPart_windowInvolution (A : ℝ) (H : ℝ → ℝ) :
    windowInvolution A (evenPart A H) = evenPart A H := by
  funext u
  simp only [evenPart, windowInvolution, show -A - (-A - u) = u by ring]
  ring

theorem oddPart_windowInvolution (A : ℝ) (H : ℝ → ℝ) :
    windowInvolution A (oddPart A H) = fun u => -oddPart A H u := by
  funext u
  simp only [oddPart, windowInvolution, show -A - (-A - u) = u by ring]
  ring

theorem evenPart_add_oddPart (A : ℝ) (H : ℝ → ℝ) :
    (fun u => 1 * evenPart A H u + 1 * oddPart A H u) = H := by
  funext u
  simp only [evenPart, oddPart]
  ring

/-- **Parity splitting.** A window is nonnegative iff it is nonnegative on its `σ_A`-even and on its
`σ_A`-odd tests. -/
theorem window_nonneg_iff_sectors :
    (∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G) ↔
      (∀ G : ℝ → ℝ, IsWindowTest A G → windowInvolution A G = G → 0 ≤ weilQuad G) ∧
        (∀ G : ℝ → ℝ, IsWindowTest A G → windowInvolution A G = (fun u => -G u) →
          0 ≤ weilQuad G) := by
  refine ⟨fun h => ⟨fun G hG _ => h G hG, fun G hG _ => h G hG⟩, fun ⟨he, ho⟩ G hG => ?_⟩
  have hE : IsWindowTest A (evenPart A G) := isWindowTest_lin hG hG.windowInvolution _ _
  have hO : IsWindowTest A (oddPart A G) := isWindowTest_lin hG hG.windowInvolution _ _
  have hW := weilPair_even_odd (mem_realTests_of_isWindowTest hE) (mem_realTests_of_isWindowTest hO)
    (evenPart_windowInvolution A G) (oddPart_windowInvolution A G)
  have hplane := weilQuad_plane (mem_realTests_of_isWindowTest hE)
    (mem_realTests_of_isWindowTest hO) 1 1
  rw [evenPart_add_oddPart, hW] at hplane
  have h1 := he _ hE (evenPart_windowInvolution A G)
  have h2 := ho _ hO (oddPart_windowInvolution A G)
  rw [hplane]
  nlinarith

/-! ### The sign pre-installed by the frozen datum -/

/-- **Frozen-negative even tests are collar-antisymmetric.** On a nonnegative window of level `N + 1`,
a `σ_A`-even test with `Q_N(H) < 0` satisfies `∫_L(H + H∘R)² < ∫_L(H − H∘R)²`. -/
theorem collar_antisymmetric_of_frozen_negative_even {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (hσ : windowInvolution A H = H) (hneg : stageForm N H < 0) :
    (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) <
      ∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2 := by
  have hQ := hpos H hH
  rw [weilQuad_eq_of_even hN hA hH hσ] at hQ
  have hw := primeJumpWeight_nonneg (N + 1)
  by_contra hc
  rw [not_lt] at hc
  have : 0 ≤ primeJumpWeight (N + 1) / 2 *
      ((∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) -
      ∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **Frozen-negative odd tests are collar-symmetric.** On a nonnegative window of level `N + 1`,
a `σ_A`-odd test with `Q_N(H) < 0` satisfies `∫_L(H − H∘R)² < ∫_L(H + H∘R)²`. -/
theorem collar_symmetric_of_frozen_negative_odd {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (hσ : windowInvolution A H = fun u => -H u)
    (hneg : stageForm N H < 0) :
    (∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) <
      ∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2 := by
  have hQ := hpos H hH
  rw [weilQuad_eq_of_odd hN hA hH hσ] at hQ
  have hw := primeJumpWeight_nonneg (N + 1)
  by_contra hc
  rw [not_lt] at hc
  have : 0 ≤ primeJumpWeight (N + 1) / 2 *
      ((∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u - H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) -
      ∫ u in (-A)..(-Real.log (N + 1 : ℕ)),
        (H u + H (collarReflection A (Real.log (N + 1 : ℕ)) u)) ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
