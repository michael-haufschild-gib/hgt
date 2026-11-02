import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum

/-!
# The canonical class of a window

On a window `W = [−A, 0]` the prime jump by `ℓ = log n` has two parts. Where it leaves the window it
pays exactly its share of the creation potential; where it stays, it **folds** the left end
`I⁻ = [−A, −ℓ]` onto the right end `I⁺ = [ℓ − A, 0]` and leaves a remainder of the creation on the
two ends. For a test `H` vanishing off `W`:

`∫ (H(u) − H(u+ℓ))² − 2∫H² = ∫_{I⁻}(H(u) − H(u+ℓ))² − ∫ (1_{I⁻} + 1_{I⁺}) H²`

(`jump_sub_creation_eq_fold`). The weight `m_ℓ = 1_{I⁻} + 1_{I⁺}` counts the in-window neighbours
of a point under the jump. Summed over the active prime powers it is the **canonical density** of
the window, `k_A = Σ_{n ≤ e^A} (Λ(n)/√n) m_{log n}`, and Weil's form on window tests is

`Q(H) = Ω(0)‖H‖² + J_∞(H) + Σ_{n ≤ e^A} (Λ(n)/√n)·(fold energy of T_n) − ∫ k_A H² + pole`

(`weilQuad_eq_fold_sub_canonical`): archimedean jumps and fold energies are nonnegative; the
canonical density is the only prime cost left on the window.

* **Degree** (`integral_canonicalDensity`): the canonical class has mass
  `deg k_A = Σ_{n ≤ e^A} (Λ(n)/√n)·2(A − log n)`, the Riesz mean of the half-weighted Chebyshev
  function: `deg k_A = 2∫_0^A ψ_{1/2}(e^t) dt` (`canonicalMass_eq_integral_halfChebyshev`).
* **Shape** (`canonicalDensity_eq_halfChebyshev`): on the window
  `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`, the half-weighted Chebyshev function at the
  distances to the two ends: a jump stays inside on one side exactly when it is shorter than the
  distance to that end. At an end `k_A = ψ_{1/2}(e^A)`, at the centre `k_A = 2ψ_{1/2}(e^{A/2})`.
* **Duality** (`canonicalDensity_reflect`): `k_A(−A − u) = k_A(u)`; the window involution exchanges
  the two ends of every fold.
* **Departing jumps** (`inWindowCount_eq_zero_of_lt`): a jump longer than the window carries no
  canonical density.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

/-- The number of in-window neighbours of `u` under the jump by `ℓ`: `1_{[−A,−ℓ]} + 1_{[ℓ−A,0]}`. -/
def inWindowCount (A ℓ u : ℝ) : ℝ :=
  (Icc (-A) (-ℓ)).indicator 1 u + (Icc (ℓ - A) 0).indicator 1 u

/-- The **fold energy** of the jump by `ℓ` on a window: `∫_{[−A,−ℓ]} (H(u) − H(u + ℓ))²`. -/
def foldEnergy (A ℓ : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ u, (Icc (-A) (-ℓ)).indicator (fun u => (H u - H (u + ℓ)) ^ 2) u

/-- The **canonical density** `k_A = Σ_{2 ≤ n ≤ e^A} (Λ(n)/√n) m_{log n}` of a window. -/
def canonicalDensity (A u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * inWindowCount A (Real.log n) u

/-- The **canonical mass** `Σ_{2 ≤ n ≤ e^A} (Λ(n)/√n)·2(A − log n)` of a window. -/
def canonicalMass (A : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * (2 * (A - Real.log n))

/-- The half-weighted Chebyshev function `ψ_{1/2}(x) = Σ_{2 ≤ n ≤ x} Λ(n)/√n`. -/
def halfChebyshev (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, primeJumpWeight n

variable {A ℓ : ℝ} {H : ℝ → ℝ}

/-- `m_ℓ(u) f(u) = 1_{[−A,−ℓ]} f(u) + 1_{[ℓ−A,0]} f(u)`. -/
theorem inWindowCount_mul (A ℓ u : ℝ) (f : ℝ → ℝ) :
    inWindowCount A ℓ u * f u = (Icc (-A) (-ℓ)).indicator f u + (Icc (ℓ - A) 0).indicator f u := by
  unfold inWindowCount
  by_cases h1 : u ∈ Icc (-A) (-ℓ) <;> by_cases h2 : u ∈ Icc (ℓ - A) 0 <;> simp [h1, h2, add_mul]

/-- `∫ (f + g − 2h) = ∫ f + ∫ g − 2∫ h`. -/
theorem integral_add_sub_two_mul {f g h : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hh : Integrable h) :
    ∫ u, (f u + g u - 2 * h u) = (∫ u, f u) + (∫ u, g u) - 2 * ∫ u, h u := by
  rw [integral_sub (f := fun u => f u + g u) (hf.add hg) (hh.const_mul 2),
    integral_add hf hg, integral_const_mul]

theorem inWindowCount_nonneg (A ℓ u : ℝ) : 0 ≤ inWindowCount A ℓ u := by
  unfold inWindowCount
  exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem foldEnergy_nonneg (A ℓ : ℝ) (H : ℝ → ℝ) : 0 ≤ foldEnergy A ℓ H :=
  integral_nonneg fun u => indicator_nonneg (fun _ _ => sq_nonneg _) u

/-- **Departing jumps carry no canonical density.** -/
theorem inWindowCount_eq_zero_of_lt (h : A < ℓ) (u : ℝ) : inWindowCount A ℓ u = 0 := by
  unfold inWindowCount
  rw [indicator_of_notMem (fun hm => by linarith [hm.1, hm.2]),
    indicator_of_notMem (fun hm => by linarith [hm.1, hm.2]), add_zero]

/-- **Window duality**: the involution `u ↦ −A − u` exchanges the two ends of a fold. -/
theorem inWindowCount_reflect (A ℓ u : ℝ) : inWindowCount A ℓ (-A - u) = inWindowCount A ℓ u := by
  unfold inWindowCount
  have h1 : (-A - u ∈ Icc (-A) (-ℓ)) ↔ u ∈ Icc (ℓ - A) 0 := by
    simp only [mem_Icc]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  have h2 : (-A - u ∈ Icc (ℓ - A) 0) ↔ u ∈ Icc (-A) (-ℓ) := by
    simp only [mem_Icc]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  by_cases ha : u ∈ Icc (ℓ - A) 0 <;> by_cases hb : u ∈ Icc (-A) (-ℓ) <;>
    simp [indicator, h1, h2, ha, hb, add_comm]

theorem canonicalDensity_reflect (A u : ℝ) : canonicalDensity A (-A - u) = canonicalDensity A u := by
  unfold canonicalDensity
  simp_rw [inWindowCount_reflect]

theorem canonicalDensity_nonneg (A u : ℝ) : 0 ≤ canonicalDensity A u :=
  Finset.sum_nonneg fun n _ => mul_nonneg (primeJumpWeight_nonneg n) (inWindowCount_nonneg _ _ _)

/-! ### The fold identity -/

theorem integrable_indicator_Icc_one (a b : ℝ) : Integrable ((Icc a b).indicator (1 : ℝ → ℝ)) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp [Real.volume_Icc]))

/-- **The fold identity.** For `H` continuous, compactly supported and vanishing off `[−A, 0]`, and
every `ℓ`, the jump energy minus the creation is the fold energy minus the in-window count:
`∫(H − H(·+ℓ))² − 2∫H² = ∫_{[−A,−ℓ]}(H − H(·+ℓ))² − ∫ m_ℓ H²`. -/
theorem jump_sub_creation_eq_fold (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) :
    (∫ u, (H u - H (u + ℓ)) ^ 2) - 2 * ∫ u, H u ^ 2 =
      foldEnergy A ℓ H - ∫ u, inWindowCount A ℓ u * H u ^ 2 := by
  set P : ℝ → ℝ := fun u => H u * H (u + ℓ) with hP
  have iH := integrable_sq hc hcs
  have iHs : Integrable fun u => H (u + ℓ) ^ 2 :=
    integrable_sq (hc.comp (continuous_add_const ℓ)) (hasCompactSupport_comp_add hcs ℓ)
  have iP : Integrable P := integrable_mul_shift hc hcs ℓ
  -- the product lives on the left end of the fold
  have hPsupp : ∀ u, u ∉ Icc (-A) (-ℓ) → P u = 0 := fun u hu => by
    simp only [hP]
    by_cases h1 : u ∈ Icc (-A) 0
    · rw [hv (u + ℓ) fun hm => hu ⟨h1.1, by linarith [hm.2]⟩, mul_zero]
    · rw [hv u h1, zero_mul]
  have hPind : (Icc (-A) (-ℓ)).indicator P = P := by
    funext u
    by_cases hu : u ∈ Icc (-A) (-ℓ)
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hPsupp u hu]
  -- translating the left end onto the right end
  have htr : ∫ u, (Icc (-A) (-ℓ)).indicator (fun u => H (u + ℓ) ^ 2) u =
      ∫ u, (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u := by
    rw [← integral_add_right_eq_self (fun u => (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u) ℓ]
    congr 1
    funext u
    have hiff : u + ℓ ∈ Icc (ℓ - A) 0 ↔ u ∈ Icc (-A) (-ℓ) := by
      simp only [mem_Icc]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
    by_cases hu : u ∈ Icc (-A) (-ℓ)
    · rw [indicator_of_mem hu, indicator_of_mem (hiff.mpr hu)]
    · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mp h))]
  -- expand the squares
  have hexp : ∀ u, (H u - H (u + ℓ)) ^ 2 = H u ^ 2 + H (u + ℓ) ^ 2 - 2 * P u := fun u => by
    simp only [hP]; ring
  have hfull : ∫ u, (H u - H (u + ℓ)) ^ 2 = 2 * (∫ u, H u ^ 2) - 2 * ∫ u, P u := by
    simp_rw [hexp]
    rw [integral_add_sub_two_mul iH iHs iP, integral_add_right_eq_self (fun u => H u ^ 2) ℓ]
    ring
  have mI := measurableSet_Icc (a := -A) (b := -ℓ)
  have mJ := measurableSet_Icc (a := ℓ - A) (b := (0 : ℝ))
  have hfold : foldEnergy A ℓ H =
      (∫ u, (Icc (-A) (-ℓ)).indicator (fun u => H u ^ 2) u) +
        (∫ u, (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u) - 2 * ∫ u, P u := by
    have hpt : ∀ u, (Icc (-A) (-ℓ)).indicator (fun u => (H u - H (u + ℓ)) ^ 2) u =
        (Icc (-A) (-ℓ)).indicator (fun u => H u ^ 2) u +
          (Icc (-A) (-ℓ)).indicator (fun u => H (u + ℓ) ^ 2) u -
            2 * (Icc (-A) (-ℓ)).indicator P u := fun u => by
      by_cases hu : u ∈ Icc (-A) (-ℓ)
      · simp only [indicator_of_mem hu, hexp]
      · simp only [indicator_of_notMem hu]; ring
    rw [foldEnergy, integral_congr_ae (Eventually.of_forall hpt),
      integral_add_sub_two_mul (iH.indicator mI) (iHs.indicator mI) (iP.indicator mI), hPind, htr]
  have hcount : ∫ u, inWindowCount A ℓ u * H u ^ 2 =
      (∫ u, (Icc (-A) (-ℓ)).indicator (fun u => H u ^ 2) u) +
        ∫ u, (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u := by
    have hpt : ∀ u, inWindowCount A ℓ u * H u ^ 2 =
        (Icc (-A) (-ℓ)).indicator (fun u => H u ^ 2) u +
          (Icc (ℓ - A) 0).indicator (fun u => H u ^ 2) u := fun u =>
      inWindowCount_mul A ℓ u (fun u => H u ^ 2)
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_add (iH.indicator mI) (iH.indicator mJ)]
  rw [hfull, hfold, hcount]
  ring

/-! ### Weil's form on a window -/

theorem integral_canonicalDensity_mul (hc : Continuous H) (hcs : HasCompactSupport H) (A : ℝ) :
    ∫ u, canonicalDensity A u * H u ^ 2 =
      ∑ n ∈ Finset.Icc 2 (windowLevel A),
        primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2 := by
  have iH := integrable_sq hc hcs
  have hint : ∀ n ∈ Finset.Icc 2 (windowLevel A), Integrable fun u =>
      primeJumpWeight n * (inWindowCount A (Real.log n) u * H u ^ 2) := fun n _ => by
    refine Integrable.const_mul ?_ _
    have hpt : (fun u => inWindowCount A (Real.log n) u * H u ^ 2) = fun u =>
        (Icc (-A) (-Real.log n)).indicator (fun u => H u ^ 2) u +
          (Icc (Real.log n - A) 0).indicator (fun u => H u ^ 2) u :=
      funext fun u => inWindowCount_mul A (Real.log n) u (fun u => H u ^ 2)
    rw [hpt]
    exact (iH.indicator measurableSet_Icc).add (iH.indicator measurableSet_Icc)
  simp_rw [canonicalDensity, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

/-- **The Markov form of a window, folded**: `M_{⌊e^A⌋}(H) = Ω(0)‖H‖² + J_∞(H) +
Σ (Λ(n)/√n)·(fold energy) − ∫ k_A H²`. -/
theorem markovForm_eq_fold_sub_canonical (hc : Continuous H) (hcs : HasCompactSupport H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) :
    markovForm (windowLevel A) H =
      EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * foldEnergy A (Real.log n) H) -
          ∫ u, canonicalDensity A u * H u ^ 2 := by
  have hfold : ∀ n ∈ Finset.Icc 2 (windowLevel A),
      primeJumpWeight n * (∫ u, (H u - H (u + Real.log n)) ^ 2) -
        2 * primeJumpWeight n * (∫ u, H u ^ 2) =
      primeJumpWeight n * foldEnergy A (Real.log n) H -
        primeJumpWeight n * ∫ u, inWindowCount A (Real.log n) u * H u ^ 2 := fun n _ => by
    have := jump_sub_creation_eq_fold hc hcs hv (ℓ := Real.log n)
    rw [show 2 * primeJumpWeight n * (∫ u, H u ^ 2) = primeJumpWeight n * (2 * ∫ u, H u ^ 2) by
      ring, ← mul_sub, this, mul_sub]
  have hsum := Finset.sum_congr rfl hfold
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  rw [markovForm, creationPotential, primeJump, integral_canonicalDensity_mul hc hcs,
    ← Finset.mul_sum] at *
  linear_combination hsum

/-- **Weil's form on a window** is archimedean jumps plus fold energies minus the canonical density,
plus the pole plane. -/
theorem weilQuad_eq_fold_sub_canonical (hH : IsWindowTest A H) :
    weilQuad H =
      EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H +
        (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * foldEnergy A (Real.log n) H) -
          (∫ u, canonicalDensity A u * H u ^ 2) +
            (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  rw [weilQuad_eq_markovForm_windowLevel hH,
    markovForm_eq_fold_sub_canonical hH.continuous hH.hasCompactSupport hH.vanish]
  ring

/-! ### The degree of the canonical class -/

theorem log_le_of_mem_Icc_windowLevel {A : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 (windowLevel A)) :
    0 < Real.log n ∧ Real.log n ≤ A := by
  obtain ⟨h2, hL⟩ := Finset.mem_Icc.mp hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnA : (n : ℝ) ≤ Real.exp A := (Nat.le_floor_iff (Real.exp_pos A).le).mp hL
  exact ⟨Real.log_pos hn1, (Real.log_le_iff_le_exp (by linarith)).mpr hnA⟩

/-- The in-window count of an active jump has mass `2(A − ℓ)`. -/
theorem integral_inWindowCount (hℓ : ℓ ≤ A) : ∫ u, inWindowCount A ℓ u = 2 * (A - ℓ) := by
  unfold inWindowCount
  rw [integral_add (integrable_indicator_Icc_one _ _) (integrable_indicator_Icc_one _ _),
    integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
    Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
  ring

/-- **The degree of the canonical class**: `∫ k_A = Σ_{n ≤ e^A} (Λ(n)/√n)·2(A − log n)`. -/
theorem integral_canonicalDensity (A : ℝ) : ∫ u, canonicalDensity A u = canonicalMass A := by
  unfold canonicalDensity canonicalMass
  rw [integral_finsetSum _ fun n _ => by
    unfold inWindowCount
    exact ((integrable_indicator_Icc_one _ _).add (integrable_indicator_Icc_one _ _)).const_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_inWindowCount (log_le_of_mem_Icc_windowLevel hn).2]

theorem canonicalMass_nonneg (A : ℝ) : 0 ≤ canonicalMass A :=
  Finset.sum_nonneg fun n hn => mul_nonneg (primeJumpWeight_nonneg n)
    (by linarith [(log_le_of_mem_Icc_windowLevel hn).2])

/-- `ψ_{1/2}(e^t)` as a sum over the active prime powers of a longer window. -/
theorem halfChebyshev_exp_eq {A t : ℝ} (ht : t ≤ A) :
    halfChebyshev (Real.exp t) = ∑ n ∈ Finset.Icc 2 (windowLevel A),
      primeJumpWeight n * (Ici (Real.log n)).indicator (1 : ℝ → ℝ) t := by
  have hsub : Finset.Icc 2 ⌊Real.exp t⌋₊ =
      (Finset.Icc 2 (windowLevel A)).filter fun n : ℕ => Real.log (n : ℝ) ≤ t := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨h2, hn⟩
      have hnt : (n : ℝ) ≤ Real.exp t := (Nat.le_floor_iff (Real.exp_pos t).le).mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact ⟨⟨h2, hn.trans (windowLevel_mono ht)⟩, (Real.log_le_iff_le_exp hn0).mpr hnt⟩
    · rintro ⟨⟨h2, _⟩, hlog⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact ⟨h2, (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp hn0).mp hlog)⟩
  rw [halfChebyshev, hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : Real.log n ≤ t
  · rw [if_pos h, indicator_of_mem (mem_Ici.mpr h), Pi.one_apply, mul_one]
  · rw [if_neg h, indicator_of_notMem (fun hm => h (mem_Ici.mp hm)), mul_zero]

/-- On the window, `m_ℓ(u) = 1[ℓ ≤ −u] + 1[ℓ ≤ A + u]`: one neighbour inside on each side that is
farther away than `ℓ`. -/
theorem inWindowCount_eq_of_mem {u : ℝ} (hu : u ∈ Icc (-A) 0) (ℓ : ℝ) :
    inWindowCount A ℓ u = (Ici ℓ).indicator 1 (-u) + (Ici ℓ).indicator 1 (A + u) := by
  unfold inWindowCount
  have h1 : u ∈ Icc (-A) (-ℓ) ↔ -u ∈ Ici ℓ := by
    simp only [mem_Icc, mem_Ici]; constructor
    · rintro ⟨_, h⟩; linarith
    · intro h; exact ⟨hu.1, by linarith⟩
  have h2 : u ∈ Icc (ℓ - A) 0 ↔ A + u ∈ Ici ℓ := by
    simp only [mem_Icc, mem_Ici]; constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; exact ⟨by linarith, hu.2⟩
  by_cases ha : -u ∈ Ici ℓ <;> by_cases hb : A + u ∈ Ici ℓ <;>
    simp [indicator, ha, hb, h1, h2]

/-- **The shape of the canonical class**: `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})` on the
window. -/
theorem canonicalDensity_eq_halfChebyshev {u : ℝ} (hu : u ∈ Icc (-A) 0) :
    canonicalDensity A u = halfChebyshev (Real.exp (-u)) + halfChebyshev (Real.exp (A + u)) := by
  rw [halfChebyshev_exp_eq (A := A) (by linarith [hu.1]),
    halfChebyshev_exp_eq (A := A) (by linarith [hu.2]), ← Finset.sum_add_distrib, canonicalDensity]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inWindowCount_eq_of_mem hu, mul_add]

theorem halfChebyshev_one : halfChebyshev 1 = 0 := by
  simp [halfChebyshev]

/-- At an end of the window the canonical density is `ψ_{1/2}(e^A)`. -/
theorem canonicalDensity_end (hA : 0 ≤ A) : canonicalDensity A 0 = halfChebyshev (Real.exp A) := by
  rw [canonicalDensity_eq_halfChebyshev ⟨by linarith, le_rfl⟩, neg_zero, Real.exp_zero,
    halfChebyshev_one, add_zero, zero_add]

/-- At the centre of the window the canonical density is `2ψ_{1/2}(e^{A/2})`. -/
theorem canonicalDensity_centre (hA : 0 ≤ A) :
    canonicalDensity A (-(A / 2)) = 2 * halfChebyshev (Real.exp (A / 2)) := by
  rw [canonicalDensity_eq_halfChebyshev ⟨by linarith, by linarith⟩, neg_neg,
    show A + -(A / 2) = A / 2 by ring]
  ring

/-- The canonical degree is twice the end value plus `|Ω(0)|`. -/
theorem canonicalDegree_eq_halfChebyshev (A : ℝ) :
    canonicalDegree A = 2 * halfChebyshev (Real.exp A) - EF.gammaBracket 0 := by
  rw [canonicalDegree_eq]; rfl

theorem setIntegral_Ioc_indicator_Ici {c A : ℝ} (hc : 0 < c) (hcA : c ≤ A) :
    ∫ t in Ioc 0 A, (Ici c).indicator (1 : ℝ → ℝ) t = A - c := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : Ioc 0 A ∩ Ici c = Icc c A := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [hset]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  exact Real.volume_real_Icc_of_le hcA

/-- **The canonical degree is a Riesz mean**: `deg k_A = 2∫_0^A ψ_{1/2}(e^t) dt`. -/
theorem canonicalMass_eq_integral_halfChebyshev {A : ℝ} (hA : 0 ≤ A) :
    canonicalMass A = 2 * ∫ t in (0 : ℝ)..A, halfChebyshev (Real.exp t) := by
  rw [intervalIntegral.integral_of_le hA,
    setIntegral_congr_fun measurableSet_Ioc fun t ht => halfChebyshev_exp_eq ht.2,
    integral_finsetSum _ fun n _ => by
      refine Integrable.const_mul ?_ _
      exact (integrableOn_const (by simp [Real.volume_Ioc])).indicator measurableSet_Ici,
    Finset.mul_sum, canonicalMass]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h0, hA'⟩ := log_le_of_mem_Icc_windowLevel hn
  rw [integral_const_mul, setIntegral_Ioc_indicator_Ici h0 hA']
  ring

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
