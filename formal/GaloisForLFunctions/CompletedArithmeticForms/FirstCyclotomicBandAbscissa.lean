import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevGrowth
import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevZeroExclusion
import GaloisForLFunctions.CompletedArithmeticForms.ChebyshevThinBandAbscissa

/-!
# Every nonempty cyclotomic band retains the Chebyshev zero width

The fixed first band has energy abscissa `2Θ` among exponents at least one.
Monotonicity extends this identity and its subpower equivalence to every
eventually positive integer bandwidth. The zero band has identically zero energy.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Filter

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- Increasing the frequency cutoff adds nonnegative mode energies. -/
theorem chebyshevCyclotomicNear_mono (N : ℕ) {K L : ℕ} (hKL : K ≤ L) :
    chebyshevCyclotomicNear N K ≤ chebyshevCyclotomicNear N L := by
  unfold chebyshevCyclotomicNear
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    omega
  · intro k _ _
    exact sq_nonneg _

private theorem chebyshevCyclotomicNear_le_full (N K : ℕ) :
    chebyshevCyclotomicNear N K ≤ chebyshevCyclotomicNear N N := by
  unfold chebyshevCyclotomicNear
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    omega
  · intro k _ _
    exact sq_nonneg _

/-- The empty band carries no energy. -/
theorem chebyshevCyclotomicNear_zero (N : ℕ) : chebyshevCyclotomicNear N 0 = 0 := by
  have he : (Finset.Ico 1 (N + 1)).filter (fun k => ¬ (0 < k ∧ 0 < N + 1 - k)) = ∅ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]
    omega
  rw [chebyshevCyclotomicNear, he, Finset.sum_empty, zero_div]

/-- Every bandwidth admits the intrinsic upper exponents with one uniform constant. -/
theorem chebyshevCyclotomicNear_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N K : ℕ, 2 ≤ N →
      chebyshevCyclotomicNear N K ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hB⟩ := chebyshevPowerBand_subpower 1 ε hε
  refine ⟨C, hC, fun N K hN => (chebyshevCyclotomicNear_le_full N K).trans ?_⟩
  simpa only [chebyshevPowerBand, Real.rpow_one, Nat.ceil_natCast] using hB N hN

/-- The first band alone detects the complete Chebyshev zero exponent. -/
theorem two_mul_zetaZeroAbscissa_le_of_first_band_power
    {r C : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevCyclotomicNear N 1 ≤ C * (N : ℝ) ^ r) :
    2 * zetaZeroAbscissa ≤ r := by
  have h := zetaZeroAbscissa_le_of_firstCyclotomicContinuous_growth
    (by linarith only [hr] : 0 ≤ (r - 1) / 2)
    (isBigO_chebyshevFirstCyclotomicContinuous_of_near_power hr hC hB)
  linarith only [h]

private theorem first_band_power_of_eventually_positive_band
    {K : ℕ → ℕ} (hK : ∀ᶠ N in atTop, 1 ≤ K N)
    {r C : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicNear N 1 ≤ A * (N : ℝ) ^ r := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hK
  let S : ℝ := ∑ n ∈ Finset.range N₀, max 0 (chebyshevCyclotomicNear n 1)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨C + S, add_nonneg hC hS, fun N hN => ?_⟩
  by_cases hlarge : N₀ ≤ N
  · exact ((chebyshevCyclotomicNear_mono N (hN₀ N hlarge)).trans (hB N hN)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hsmall : N < N₀ := lt_of_not_ge hlarge
    have hterm : chebyshevCyclotomicNear N 1 ≤ S :=
      (le_max_right _ _).trans
        (Finset.single_le_sum (fun n _ => le_max_left 0 (chebyshevCyclotomicNear n 1))
          (Finset.mem_range.mpr hsmall))
    have hone : 1 ≤ (N : ℝ) ^ r := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [hr] : 0 ≤ r)
    exact hterm.trans ((le_add_of_nonneg_left hC).trans
      (le_mul_of_one_le_right (add_nonneg hC hS) hone))

/-- Any eventually nonempty frequency band detects the full zero exponent. -/
theorem two_mul_zetaZeroAbscissa_le_of_band_power
    {K : ℕ → ℕ} (hK : ∀ᶠ N in atTop, 1 ≤ K N)
    {r C : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ r) :
    2 * zetaZeroAbscissa ≤ r := by
  obtain ⟨A, hA, hfirst⟩ := first_band_power_of_eventually_positive_band hK hr hC hB
  exact two_mul_zetaZeroAbscissa_le_of_first_band_power hr hA hfirst

/-- Every eventually positive bandwidth, including the fixed first band, has abscissa `2Θ`. -/
theorem chebyshevCyclotomicBand_exponent_inf (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 1 ≤ K N) :
    sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ r} = 2 * zetaZeroAbscissa := by
  let E := {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ r}
  have hbdd : BddBelow E := ⟨1, fun _ h => h.1⟩
  have hmem (ε : ℝ) (hε : 0 < ε) : 2 * zetaZeroAbscissa + ε ∈ E := by
    obtain ⟨C, hC, hB⟩ := chebyshevCyclotomicNear_subpower ε hε
    exact ⟨by linarith only [half_le_zetaZeroAbscissa, hε], C, hC, fun N hN => hB N (K N) hN⟩
  have hne : E.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 (by norm_num)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbdd (hmem ε hε)
  · apply le_csInf hne
    rintro r ⟨hr, C, hC, hB⟩
    exact two_mul_zetaZeroAbscissa_le_of_band_power hK hr hC hB

/-- Subpower bounds for any eventually positive band are exactly zero-width bounds. -/
theorem chebyshevCyclotomicBand_subpower_iff (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 1 ≤ K N) (r : ℝ) (hr : 1 ≤ r) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ (r + ε)) ↔
        2 * zetaZeroAbscissa ≤ r := by
  constructor
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨C, hC, hB⟩ := h ε hε
    exact two_mul_zetaZeroAbscissa_le_of_band_power hK (by linarith only [hr, hε]) hC hB
  · intro h ε hε
    obtain ⟨C, hC, hB⟩ := chebyshevCyclotomicNear_subpower ε hε
    refine ⟨C, hC, fun N hN => (hB N (K N) hN).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [h])) hC

/-- The fixed first band retains the complete energy abscissa. -/
theorem chebyshevFirstCyclotomicBand_exponent_inf :
    sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicNear N 1 ≤ C * (N : ℝ) ^ r} = 2 * zetaZeroAbscissa :=
  chebyshevCyclotomicBand_exponent_inf (fun _ => 1) (Eventually.of_forall (fun _ => le_rfl))

/-- RH is equivalent to `N^(1+ε)` energy bounds in any eventually nonempty band. -/
theorem riemannHypothesis_iff_chebyshevCyclotomicBand (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 1 ≤ K N) :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevCyclotomicNear N (K N) ≤ C * (N : ℝ) ^ (1 + ε) := by
  rw [chebyshevCyclotomicBand_subpower_iff K hK 1 le_rfl,
    ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    linarith only [h, half_le_zetaZeroAbscissa]

/-- The fixed first band alone supplies an exact RH energy criterion. -/
theorem riemannHypothesis_iff_chebyshevFirstCyclotomicBand :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevCyclotomicNear N 1 ≤ C * (N : ℝ) ^ (1 + ε) :=
  riemannHypothesis_iff_chebyshevCyclotomicBand (fun _ => 1)
    (Eventually.of_forall (fun _ => le_rfl))

#print axioms chebyshevCyclotomicNear_zero
#print axioms two_mul_zetaZeroAbscissa_le_of_band_power
#print axioms chebyshevCyclotomicBand_exponent_inf
#print axioms chebyshevCyclotomicBand_subpower_iff
#print axioms chebyshevFirstCyclotomicBand_exponent_inf
#print axioms riemannHypothesis_iff_chebyshevCyclotomicBand
#print axioms riemannHypothesis_iff_chebyshevFirstCyclotomicBand

end GaloisForLFunctions.CompletedArithmeticForms
