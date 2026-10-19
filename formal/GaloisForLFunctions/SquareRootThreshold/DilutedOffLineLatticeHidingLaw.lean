import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfOffLineLattices
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# Dilution: sparse off-line lattices in a dense on-line background

An isolated off-line pair in the on-line lattice of density `L/2π` hides up to an aperture of
order `log(δL)/(2δ)`; a dense off-line lattice of the same density hides up to the Nyquist
aperture `L/2`. This module interpolates.

Superpose the doubled on-line lattice `{½ + 2πik/L}` and an off-line lattice
`{½ ± δ + 2πij/ℓ}` of lower density, `ℓ ≤ L` (`dilutedLatticeConfig`). Below the background's
Nyquist aperture the on-line lattice contributes only the diagonal `2L ∫|f|²`
(`RHTower`-lattice Poisson, `hasSum_Wsummand_onLineLattice`), so the configuration has the lag
formula of the off-line lattice with the lag-zero mass raised by `2L/ℓ`
(`W_dilutedLatticeConfig`): the symbol is `2cosh(δmℓ) + (2L/ℓ)·[m = 0]`.

* **Dilution law** (`dilutedLattice_weil_nonneg_iff`, `dilutedLattice_hodgeIndex_iff`). For
  `0 < a ≤ L/2`, with `n = ⌈2a/ℓ⌉`, the configuration is invisible at aperture `a`, equivalently
  satisfies the level-`a` Hodge index, iff `ℓ (√(S₊S₋) − n) ≤ 2L`, `S_± = Σ_{j<n} e^{±2δjℓ}`.
* **The hiding aperture is logarithmic in the density ratio**
  (`dilutedLattice_weil_nonneg_of_le`, `dilutedLattice_not_hodgeIndex_of_lt`). Invisible when
  `(2a + ℓ) e^{2δa} ≤ 2L`; visible, by polar-constrained tests, when
  `ℓ e^{δ(2a − ℓ)} > 2L + 2a + ℓ`. So the hiding aperture is `(1/2δ) log(L/ℓ)` up to lower-order
  terms.

A sparse off-line lattice therefore behaves like a family of isolated pairs: its hiding aperture
grows only logarithmically in the background density, whereas a crystal of the background density
hides up to `L/2`. For a fixed off-line density inside zeros of `ζ`-density `L ≍ log T` the hiding
aperture is `≍ (1/2δ) log log T`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The doubled on-line lattice of spacing `2π/L` together with the off-line lattice pair
`{½ ± δ + 2πij/ℓ}`. -/
def dilutedLatticeConfig {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (verticalLatticePoint L 0) ∪
    (Set.range (verticalLatticePoint ℓ δ) ∪ Set.range (verticalLatticePoint ℓ (-δ)))
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun ρ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp only [verticalLatticePoint] <;>
      constructor <;> linarith
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩
    · exact Or.inr (Or.inr ⟨k, (reflect_verticalLatticePoint ℓ δ k).symm⟩)
    · exact Or.inr (Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_neg]⟩)
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    have hG := finite_latticeWindow (h := 2 * π / ℓ) (by positivity) T₁ T₂
    refine ((hF.image (verticalLatticePoint L 0)).union
      ((hG.image (verticalLatticePoint ℓ δ)).union
        (hG.image (verticalLatticePoint ℓ (-δ))))).subset ?_
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩)

/-- The off-line part of a configuration on one vertical lattice with multiplicity one. -/
theorem hasSum_Wsummand_offLineLattice (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ)
    (hmult : ∀ k : ℤ, Z.mult (verticalLatticePoint ℓ s k) = 1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    HasSum (fun ρ : Set.range (verticalLatticePoint ℓ s) => Z.Wsummand f f ρ)
      (((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * (Real.exp (s * (m * ℓ)) : ℂ)) := by
  obtain ⟨A, hfs⟩ := exists_Icc_of_hasCompactSupport hfc
  rw [(verticalLatticePoint_injective hℓ s).hasSum_range_iff]
  have hfun : Z.Wsummand f f ∘ verticalLatticePoint ℓ s = fun k : ℤ =>
      paperFT (EF.weilTest f f) ((((k : ℝ) * (2 * π / ℓ) : ℝ) : ℂ) - I * s) := by
    funext k
    rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc,
      hmult, Nat.cast_one, one_mul]
  rw [hfun]
  exact hasSum_paperFT_lattice_sub_I_mul hℓ (EF.weilTest_contDiff hf hf.continuous hfc)
    (weilTest_abs_le hfs hfs) s

/-- **Lag formula below the background Nyquist aperture.** For tests supported in `[-L/2, L/2]`,
`W(f, f) = ℓ Σ_m k(mℓ) (2cosh(δmℓ) + (2L/ℓ)[m = 0])`. -/
theorem W_dilutedLatticeConfig {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (dilutedLatticeConfig hℓ hL hδ hδ').W f f = ((ℓ : ℝ) : ℂ) *
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shiftSymbol (latticeSymbol ℓ δ) (-(2 * L / ℓ)) m := by
  set Z := dilutedLatticeConfig hℓ hL hδ hδ' with hZ
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hon : ∀ k : ℤ, Z.mult (verticalLatticePoint L 0 k) = 2 := fun k => by
    simp [hZ, dilutedLatticeConfig, verticalLatticePoint]
  have hoff : ∀ (s : ℝ), s ≠ 0 → ∀ k : ℤ, Z.mult (verticalLatticePoint ℓ s k) = 1 :=
    fun s hs k => by
      simp only [hZ, dilutedLatticeConfig, verticalLatticePoint]
      rw [if_neg]
      intro h
      exact hs (by linarith)
  have hA := hasSum_Wsummand_onLineLattice Z hL hon hf hf.continuous hfs hfs
  have hBp := hasSum_Wsummand_offLineLattice Z hℓ δ (hoff δ hδ.ne') hf hfc
  have hBm := hasSum_Wsummand_offLineLattice Z hℓ (-δ) (hoff (-δ) (by linarith)) hf hfc
  have hd₁ : Disjoint (Set.range (verticalLatticePoint ℓ δ))
      (Set.range (verticalLatticePoint ℓ (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0))
      (Set.range (verticalLatticePoint ℓ δ) ∪ Set.range (verticalLatticePoint ℓ (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ (⟨k', hk'⟩ | ⟨k', hk'⟩) <;>
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂ hA
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ hBp hBm)
  rw [ZeroConfig.W]
  refine hall.tsum_eq.trans ?_
  -- rewrite the right side
  rw [lagSum_shiftSymbol hℓ hfc, ← weilTest_self_zero]
  obtain ⟨A, hfsA⟩ := exists_Icc_of_hasCompactSupport hfc
  obtain ⟨S, hS⟩ := exists_lag_window (K := EF.weilTest f f) hℓ (weilTest_abs_le hfsA hfsA)
  rw [tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul],
    tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul],
    tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul]]
  have hk0 : EF.weilTest f f 0 = ∫ t, f t * conj (f t) := by
    rw [weilTest_apply]; simp
  rw [hk0]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hsum : ∑ m ∈ S, EF.weilTest f f (m * ℓ) * latticeSymbol ℓ δ m =
      ∑ m ∈ S, EF.weilTest f f (m * ℓ) * (Real.exp (δ * (m * ℓ)) : ℂ) +
        ∑ m ∈ S, EF.weilTest f f (m * ℓ) * (Real.exp (-δ * (m * ℓ)) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [latticeSymbol, Real.cosh_eq, neg_mul]
    push_cast
    ring
  rw [hsum]
  push_cast
  have hℓL : (ℓ : ℂ) * (2 * (L : ℂ) / (ℓ : ℂ)) = 2 * L := by field_simp
  linear_combination (-(∫ t, f t * conj (f t))) * hℓL

/-! ### The dilution law -/

theorem latticeFloor_one (ℓ δ : ℝ) : latticeFloor ℓ δ 1 = 0 := by
  simp [latticeFloor]

/-- The shifted lattice symbol has Toeplitz floor `latticeFloor + 2L/ℓ`. -/
theorem dilutedSymbol_toeplitz_floor (ℓ L δ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    (latticeFloor ℓ δ n + 2 * L / ℓ) * ∑ j, ‖c j‖ ^ 2 ≤
      (toeplitzForm (shiftSymbol (latticeSymbol ℓ δ) (-(2 * L / ℓ))) n c).re := by
  rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re]
  have := latticeSymbol_toeplitz_floor ℓ δ c
  nlinarith

theorem dilutedLattice_lag {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (haL : a ≤ L / 2) :
    ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (dilutedLatticeConfig hℓ hL hδ hδ').W f f = ((ℓ : ℝ) : ℂ) *
        ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shiftSymbol (latticeSymbol ℓ δ) (-(2 * L / ℓ)) m :=
  fun _ hf hfs => W_dilutedLatticeConfig hℓ hL hδ hδ' hf
    (hfs.trans (Icc_subset_Icc (by linarith) haL))

/-- Invisibility from the dilution bound. -/
theorem dilutedLattice_weil_nonneg_of_floor {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (haL : a ≤ L / 2)
    (h : -(ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊) ≤ 2 * L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) : 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re := by
  have h1 := weil_floor_of_toeplitz_floor _ hℓ _ (dilutedLattice_lag hℓ hL hδ hδ' haL) 0
    (fun c => by
      have := dilutedSymbol_toeplitz_floor ℓ L δ c
      have hc : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have hfl : 0 ≤ latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L / ℓ := by
        rw [show latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L / ℓ =
          (ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L) / ℓ by
          rw [eq_div_iff hℓ.ne', add_mul, div_mul_cancel₀ _ hℓ.ne']; ring]
        exact div_nonneg (by linarith) hℓ.le
      nlinarith) hf hfs
  simpa using h1

/-- Visibility, by polar-constrained tests, when the dilution bound fails. -/
theorem dilutedLattice_not_hodgeIndex_of_floor {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (h : 2 * L < -(ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊)) :
    ¬ HodgeIndexAtLevel (dilutedLatticeConfig hℓ hL hδ hδ') a := by
  intro hH
  have hn1 : 1 ≤ ⌈2 * a / ℓ⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hn : 2 ≤ ⌈2 * a / ℓ⌉₊ := by
    by_contra h2
    have : ⌈2 * a / ℓ⌉₊ = 1 := by omega
    rw [this, latticeFloor_one] at h
    linarith
  obtain ⟨c, hc0, hc⟩ := exists_latticeSymbol_toeplitz_floor_attained hℓ hδ hn
  have hT := toeplitz_floor_of_hodge_floor _ hℓ _ (dilutedLattice_lag hℓ hL hδ hδ' haL) ha 0
    (fun f hf hfs hp hm => by simpa using hH f hf hfs hp hm) c
  rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re, hc] at hT
  have : (latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L / ℓ) * ∑ j, ‖c j‖ ^ 2 < 0 := by
    have hneg : latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L / ℓ < 0 := by
      rw [show latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L / ℓ =
        (ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊ + 2 * L) / ℓ by
          rw [eq_div_iff hℓ.ne', add_mul, div_mul_cancel₀ _ hℓ.ne']; ring]
      exact div_neg_of_neg_of_pos (by linarith) hℓ
    exact mul_neg_of_neg_of_pos hneg hc0
  nlinarith

/-- **Dilution law.** For `0 < a ≤ L/2` the diluted lattice is invisible at aperture `a` iff
`ℓ(√(S₊S₋) − n) ≤ 2L`, `n = ⌈2a/ℓ⌉`. -/
theorem dilutedLattice_weil_nonneg_iff {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ↔
      -(ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊) ≤ 2 * L := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact dilutedLattice_not_hodgeIndex_of_floor hℓ hL hδ hδ' ha haL hlt
      fun f hf hfs _ _ => h f hf hfs
  · exact fun h f hf hfs => dilutedLattice_weil_nonneg_of_floor hℓ hL hδ hδ' haL h hf hfs

/-- **Dilution law for the Hodge index.** -/
theorem dilutedLattice_hodgeIndex_iff {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    HodgeIndexAtLevel (dilutedLatticeConfig hℓ hL hδ hδ') a ↔
      -(ℓ * latticeFloor ℓ δ ⌈2 * a / ℓ⌉₊) ≤ 2 * L := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact dilutedLattice_not_hodgeIndex_of_floor hℓ hL hδ hδ' ha haL hlt h
  · exact fun h f hf hfs _ _ => dilutedLattice_weil_nonneg_of_floor hℓ hL hδ hδ' haL h hf hfs

/-! ### The hiding aperture -/

/-- **Invisible below `(1/2δ) log(L/ℓ)`.** If `(2a + ℓ) e^{2δa} ≤ 2L` and `a ≤ L/2`, the diluted
lattice is invisible at aperture `a`. -/
theorem dilutedLattice_weil_nonneg_of_le {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hsmall : (2 * a + ℓ) * Real.exp (2 * δ * a) ≤ 2 * L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) : 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re := by
  refine dilutedLattice_weil_nonneg_of_floor hℓ hL hδ hδ' haL ?_ hf hfs
  have := (latticeFloor_aperture_bounds hℓ hδ ha).1
  linarith

/-- **Visible above `(1/2δ) log(L/ℓ)`.** If `ℓ/2 < a ≤ L/2` and `ℓ e^{δ(2a − ℓ)} > 2L + 2a + ℓ`,
the diluted lattice violates the level-`a` Hodge index. -/
theorem dilutedLattice_not_hodgeIndex_of_lt {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hlarge : 2 * L + 2 * a + ℓ < ℓ * Real.exp (δ * (2 * a - ℓ))) :
    ¬ HodgeIndexAtLevel (dilutedLatticeConfig hℓ hL hδ hδ') a := by
  refine dilutedLattice_not_hodgeIndex_of_floor hℓ hL hδ hδ' ha haL ?_
  have := (latticeFloor_aperture_bounds hℓ hδ ha).2
  linarith

end GaloisForLFunctions.SquareRootThreshold
