import GaloisForLFunctions.RHTower.WeilPositivitySummablePerturbationRigidity

/-!
# Existence of Weil-positive weight systems reduces to finite levels

Call real weights `lam` *Weil-positive up to level `A`* (`WeilPositiveUpTo`) if the finite-atom Weil
symbol of `ζ` with weights `lam` has nonnegative energy on every polar-constrained `C²` test at every
level `a ≤ A`, and *Weil-positive* (`WeilPositive`) if this holds at every level.

* **Level-wise box** (`abs_le_boxWidth_of_weilPositiveUpTo`).  Weil positivity up to level `A` gives
  `|lam(n)| ≤ √n (log n + C₀)` for every `n ≥ 2` whose resonator level `log n/2 + 1/(4(n+1))` is at
  most `A`, with an absolute constant `C₀`.  The two-point resonators in the single-level Weil–Toeplitz
  bound give this.
* **Existence reduction** (`exists_weilPositive_iff_forall_level`).  A Weil-positive weight system
  exists iff every finite level admits a weight system that is Weil-positive up to that level.  Clamp
  the finite-level solutions into the box, extract a coordinatewise convergent subsequence
  (Tychonoff), and pass to the limit in the energy of each test.  That energy is an affine function
  of the finitely many weights it sees.
* **Existence and uniqueness.**  Together with a uniqueness statement (at most one Weil-positive
  weight system), the reduction would make positivity of the von Mangoldt weights equivalent to
  finite-level existence.  This is the split of Minkowski's problem into an existence part and a
  uniqueness part.  Uniqueness is known along every summable, constant, and finite-measure
  perturbation of `Λ` (`vonMangoldt_add_summable_not_weilPositive`,
  `eq_zero_of_vonMangoldt_add_const_weilPositive`, `vonMangoldt_sub_measure_weilPositive_eq`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

/-- Weil positivity of the weights `lam` on polar-constrained `C²` tests at every level `a ≤ A`. -/
def WeilPositiveUpTo (lam : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → a ≤ A → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
    0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))

/-- Weil positivity at every level. -/
def WeilPositive (lam : ℕ → ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
    0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))

/-- The resonator level `log n / 2 + 1/(4(n+1))` of the atom `n`. -/
def atomLevel (n : ℕ) : ℝ := Real.log n / 2 + 1 / ((n : ℝ) + 1) / 4

/-- The box constant `C₀ = log 2 + 9/2 + profileRatio/2`. -/
def boxConst : ℝ := Real.log 2 + 9 / 2 + profileRatio / 2

/-- The half-width `√n (log n + C₀)` of the Weil box at `n`. -/
def boxWidth (n : ℕ) : ℝ := |Real.sqrt n * (Real.log n + boxConst)|

/-- **The level-wise box.**  Weil positivity up to level `A` gives `|lam(n)| ≤ √n (log n + C₀)` for
every `n ≥ 2` with `atomLevel n ≤ A`. -/
theorem abs_le_boxWidth_of_weilPositiveUpTo {lam : ℕ → ℝ} {A : ℝ} (hW : WeilPositiveUpTo lam A)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hA : atomLevel n₀ ≤ A) : |lam n₀| ≤ boxWidth n₀ := by
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hlev0 : 0 ≤ atomLevel n₀ := by
    unfold atomLevel
    have := Real.log_nonneg (show (1 : ℝ) ≤ n₀ by exact_mod_cast (by omega : 1 ≤ n₀))
    positivity
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * lam n₀ ≤ Real.sqrt n₀ * (Real.log n₀ + boxConst) := by
    intro s hs
    have hc : ∀ m, n₀ < m → twoPointCoeff n₀ (s : ℂ) m = 0 := by
      intro m hm; unfold twoPointCoeff; rw [if_neg (by omega), if_neg (by omega)]
    have h := weil_multiplicativeToeplitz_bound_at (lam := lam) (N := n₀) (by omega)
      (twoPointCoeff n₀ (s : ℂ)) hc (fun f hf hfs hp hm => hW _ hlev0 hA f hf hfs hp hm)
    have hdiag : ∀ n ∈ Finset.Icc 2 n₀, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 n₀, twoPointCoeff n₀ (s : ℂ) (n * m) *
          conj (twoPointCoeff n₀ (s : ℂ) m)).re = if n = n₀ then lam n₀ / Real.sqrt n₀ * s else 0 := by
      intro n hn
      rw [twoPointCoeff_diag hn₀ _ (Finset.mem_Icc.mp hn).1]
      split_ifs with h' <;> simp [h']
    rw [Finset.sum_congr rfl hdiag, Finset.sum_ite_eq'] at h
    rw [if_pos (Finset.mem_Icc.mpr ⟨hn₀, le_rfl⟩)] at h
    have hnorm : ∑ m ∈ Finset.Icc 1 n₀, ‖twoPointCoeff n₀ (s : ℂ) m‖ ^ 2 = 2 := by
      have hpt : ∀ m ∈ Finset.Icc 1 n₀, ‖twoPointCoeff n₀ (s : ℂ) m‖ ^ 2 =
          (if m = 1 then 1 else 0) + (if m = n₀ then 1 else 0) := by
        intro m _
        unfold twoPointCoeff
        by_cases h1 : m = 1
        · subst h1; simp; omega
        · by_cases h2 : m = n₀
          · subst h2; rcases hs with rfl | rfl <;> simp [h1]
          · simp [h1, h2]
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩),
        if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]; norm_num
    rw [hnorm] at h
    have : s * lam n₀ = Real.sqrt n₀ * (lam n₀ / Real.sqrt n₀ * s) := by field_simp
    rw [this]
    have h' : lam n₀ / Real.sqrt n₀ * s ≤ Real.log n₀ + boxConst := by
      unfold boxConst; linarith
    exact mul_le_mul_of_nonneg_left h' hsq.le
  have hb : Real.sqrt n₀ * (Real.log n₀ + boxConst) ≤ boxWidth n₀ := le_abs_self _
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

/-- The symbol energy is an affine function of the finitely many weights it sees. -/
theorem integral_weilAtomSymbol_eq_affine {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (lam : ℕ → ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
        2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
  integral_weilAtomSymbol_eq_arch_sub hf hfs lam

/-- **Minkowski split: existence reduces to finite levels.**  A Weil-positive weight system exists iff
for every level `A` some weight system is Weil-positive up to level `A`.  The finite-level
solutions lie in the box `|lam(n)| ≤ √n (log n + C₀)` on the atoms they see (Tychonoff), and the
symbol energy of each test is affine in finitely many weights, so a convergent subsequence has
a Weil-positive limit. -/
theorem exists_weilPositive_iff_forall_level :
    (∃ lam : ℕ → ℝ, WeilPositive lam) ↔ ∀ A : ℝ, ∃ lam : ℕ → ℝ, WeilPositiveUpTo lam A := by
  constructor
  · rintro ⟨lam, hlam⟩ A
    exact ⟨lam, fun a ha _ f hf hfs hp hm => hlam a ha f hf hfs hp hm⟩
  intro hex
  choose lam hlam using fun k : ℕ => hex (k : ℝ)
  -- clamp into the box
  set clamp : ℕ → ℕ → ℝ := fun k n => max (-boxWidth n) (min (boxWidth n) (lam k n)) with hclamp
  have hK : IsCompact (Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ k, clamp k ∈ Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) := by
    intro k n _
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [hclamp, mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  obtain ⟨lam₀, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ n, Tendsto (fun j => clamp (φ j) n) atTop (𝓝 (lam₀ n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  -- the clamp is inactive on the atoms seen at a fixed level, eventually
  have hagree : ∀ n, 2 ≤ n → ∀ᶠ j in atTop, clamp (φ j) n = lam (φ j) n := by
    intro n hn
    obtain ⟨K, hK⟩ := exists_nat_ge (atomLevel n)
    filter_upwards [(hφ.tendsto_atTop.eventually_ge_atTop K)] with j hj
    have hlev : atomLevel n ≤ (φ j : ℝ) := hK.trans (by exact_mod_cast hj)
    have hbox := abs_le_boxWidth_of_weilPositiveUpTo (hlam (φ j)) hn hlev
    rw [abs_le] at hbox
    simp only [hclamp]
    rw [min_eq_right hbox.2, max_eq_right hbox.1]
  refine ⟨lam₀, fun a ha f hf hfs hp hm => ?_⟩
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set c : ℕ → ℝ := fun n => (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re
  set E : (ℕ → ℝ) → ℝ := fun l => (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
    2 * π * ∑ n ∈ Finset.Icc 2 N, l n / Real.sqrt n * c n with hE
  have hEq : ∀ l, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol l N (τ / (2 * π)) = E l :=
    fun l => integral_weilAtomSymbol_eq_affine hf hfs l
  have hElim : Tendsto (fun j => E (clamp (φ j))) atTop (𝓝 (E lam₀)) := by
    simp only [hE]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ (tendsto_finsetSum _ fun n _ => ?_))
    exact ((hcoord n).div_const _).mul_const _
  have hEagree : ∀ᶠ j in atTop, E (clamp (φ j)) = E (lam (φ j)) := by
    have hall : ∀ᶠ j in atTop, ∀ n ∈ Finset.Icc 2 N, clamp (φ j) n = lam (φ j) n :=
      (Finset.eventually_all _).mpr fun n hn => hagree n (Finset.mem_Icc.mp hn).1
    filter_upwards [hall] with j hj
    simp only [hE]
    congr 2
    exact Finset.sum_congr rfl fun n hn => by rw [hj n hn]
  have hEpos : ∀ᶠ j in atTop, 0 ≤ E (clamp (φ j)) := by
    obtain ⟨K, hK⟩ := exists_nat_ge a
    filter_upwards [hEagree, hφ.tendsto_atTop.eventually_ge_atTop K] with j hj hjK
    rw [hj, ← hEq]
    exact hlam (φ j) a ha (hK.trans (by exact_mod_cast hjK)) f hf hfs hp hm
  rw [hEq]
  exact ge_of_tendsto hElim hEpos

end RHTower
