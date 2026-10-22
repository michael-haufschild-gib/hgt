import GaloisForLFunctions.SquareRootThreshold.DilutedOffLineLatticeHidingLaw
import GaloisForLFunctions.SquareRootThreshold.CrystalRigidityAtTheSquareRootThreshold
import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfPeriodicConfigurations

/-!
# Diluted Periodic Patterns and Crystal Visibility in an On-Line Background

This module establishes the first leg of the **Dilution–Crystallization–Incommensurability (DCI)
Pincer**: superposing an arbitrary `P`-pair periodic off-line pattern of period `2π/ℓ` (`P`
reflected off-line pairs per period at offsets `c_r` and depths `d_r ∈ (0, ½]`) onto a dense
doubled on-line lattice `{½ + 2πik/L}` of background density `L/2π`.

1. **Lag formula in a dense on-line background (`W_dilutedPatternConfig`):**
   For every `C²` test `f` supported in `[-L/2, L/2]`, the on-line lattice contributes purely the
   lag-zero mass `2L ∫|f|²`, so
   `W(f, f) = ℓ Σ_m k(mℓ) (D(m) + (2L/ℓ) [m = 0])`,
   where `D(m) = Σ_r 2cosh(d_r mℓ) e^{i c_r mℓ}` is the `P`-pair pattern symbol.
2. **Toeplitz equivalence and mode bound (`dilutedPattern_weil_nonneg_iff_toeplitz`,
   `norm_patternSymbol_le_of_diluted_hiding`):**
   For `0 < a ≤ L/2`, the diluted pattern is Weil-nonnegative at aperture `a` iff the Toeplitz form
   of `shiftSymbol (patternSymbol ℓ c d) (-(2L/ℓ))` of size `⌈2a/ℓ⌉₊` is positive semidefinite.
   Consequently, hiding at aperture `a ≤ L/2` forces every mode `1 ≤ m < ⌈2a/ℓ⌉₊` to satisfy
   `ℓ ‖D(m)‖ ≤ 2Pℓ + 2L`.
3. **Constructive harmonic alignment of uniform crystals (`patternSymbol_crystal_mul_period`,
   `norm_patternSymbol_crystal_mul_period`):**
   When `(θ, d)` is a uniform crystal (`d_r = δ` and `P(θ_r − θ_{r'}) ∈ ℤ`), destructive
   interference kills the sub-harmonics `1 ≤ m < P`, buying hiding up to `Pℓ/2`. However, at every
   harmonic `m = kP` (`k ≥ 1`), the crystal condition `z_r^P = z_{r'}^P` forces **100% constructive
   phase alignment** `z_r^{kP} = z_0^{kP}`, so `‖D(kP)‖ = 2P cosh(δ k P ℓ)`.
4. **Logarithmic visibility of diluted crystals (`diluted_crystal_visible_at_harmonic`):**
   Even when `P` off-line pairs per period crystallize into a uniform crystal, as soon as the
   harmonic lag `kPℓ < 2a` (`a ≤ L/2`) satisfies `2Pℓ + 2L < 2Pℓ cosh(δ k P ℓ)`, the diluted crystal
   is strictly visible at aperture `a` (`∃ f, Re W(f, f) < 0`), i.e. at the logarithmic aperture
   `a ≍ (1/2δ) log(L/(Pℓ)) + Pℓ/2 ≪ L/2`.
5. **Logarithmic visibility of general diluted periodic patterns (`diluted_pattern_visible_of_mode`):**
   For any periodic off-line pattern (crystalline or not), `CoshSymbolData.exists_mode_lower`
   provides a mode `m ∈ [k, k+P)` with `‖D(m)‖ ≥ c e^{d_max mℓ}`, forcing visibility as soon as
   `c ℓ e^{d_max mℓ} > 2Pℓ + 2L`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Zeta23 _root_.RHTower GaloisForLFunctions.SquareRootThreshold

/-! ### Superposing a `P`-pair periodic off-line pattern on an on-line lattice -/

/-- The doubled on-line lattice of spacing `2π/L` together with `P` off-line pairs per period
`2π/ℓ` at offsets `c_r` and depths `d_r ∈ (0, ½]`. -/
def dilutedPatternConfig {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ} (c d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (verticalLatticePoint L 0) ∪
    ((Set.range fun rj : Fin P × ℤ => patternPoint ℓ (d rj.1) (c rj.1) rj.2) ∪
      Set.range fun rj : Fin P × ℤ => patternPoint ℓ (-d rj.1) (c rj.1) rj.2)
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun _ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨rj, rfl⟩ | ⟨rj, rfl⟩)
    · simp only [verticalLatticePoint]; constructor <;> linarith
    · simp only [patternPoint]; constructor <;> linarith [hd0 rj.1, hd1 rj.1]
    · simp only [patternPoint]; constructor <;> linarith [hd0 rj.1, hd1 rj.1]
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨rj, rfl⟩ | ⟨rj, rfl⟩)
    · exact Or.inl ⟨k, by rw [reflect_verticalLatticePoint, neg_zero]⟩
    · exact Or.inr (Or.inr ⟨rj, (reflect_patternPoint _ _ _ _).symm⟩)
    · exact Or.inr (Or.inl ⟨rj, by rw [reflect_patternPoint, neg_neg]⟩)
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
    have hPfin := (patternConfig hℓ c d hd0 hd1).finite_window T₁ T₂
    refine ((hF.image (verticalLatticePoint L 0)).union hPfin).subset ?_
    rintro ρ ⟨⟨k, rfl⟩ | hpat, h1, h2⟩
    · exact Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨hpat, h1, h2⟩

/-- **Lag formula for a diluted periodic off-line pattern.** Below the background Nyquist aperture
`L/2`, the on-line lattice contributes `2L ∫|f|²` at lag zero while the `P`-pair off-line pattern
contributes `ℓ Σ_m k(mℓ) D(m)`. -/
theorem W_dilutedPatternConfig {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ} (c d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j')
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (dilutedPatternConfig hℓ hL c d hd0 hd1).W f f = ((ℓ : ℝ) : ℂ) *
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shiftSymbol (patternSymbol ℓ c d) (-(2 * L / ℓ)) m := by
  set Z := dilutedPatternConfig hℓ hL c d hd0 hd1 with hZ
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hon : ∀ k : ℤ, Z.mult (verticalLatticePoint L 0 k) = 2 := fun k => by
    simp [hZ, dilutedPatternConfig, verticalLatticePoint]
  have hA := hasSum_Wsummand_onLineLattice Z hL hon hf hf.continuous hfs hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  set K := EF.weilTest f f with hKdef
  have hinj : ∀ e : Fin P → ℝ, Function.Injective fun rj : Fin P × ℤ =>
      patternPoint ℓ (e rj.1) (c rj.1) rj.2 := by
    intro e rj rj' h
    have him := congrArg Complex.im h
    simp only [patternPoint] at him
    obtain ⟨h1, h2⟩ := hc rj.1 rj'.1 rj.2 rj'.2 him
    exact Prod.ext h1 h2
  have hsum : ∀ (e : Fin P → ℝ), (∀ r, e r ≠ 0) →
      HasSum (fun ρ : Set.range (fun rj : Fin P × ℤ =>
        patternPoint ℓ (e rj.1) (c rj.1) rj.2) => Z.Wsummand f f ρ)
      (∑ r : Fin P, ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
        (Real.exp (e r * (m * ℓ)) : ℂ)) := by
    intro e he
    rw [(hinj e).hasSum_range_iff]
    refine hasSum_fin_prod fun r => ?_
    have := hasSum_paperFT_translate hℓ hK hKs (c r) (e r)
    refine this.congr_fun fun j => ?_
    have hmult : Z.mult (patternPoint ℓ (e r) (c r) j) = 1 := by
      simp only [hZ, dilutedPatternConfig, patternPoint]
      rw [if_neg]
      have := he r
      intro h; exact this (by linarith)
    simp only [Function.comp_apply, ZeroConfig.Wsummand, hmult, Nat.cast_one, one_mul]
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, gammaOf_patternPoint]
  have hp := hsum d (fun r => (hd0 r).ne')
  have hm := hsum (fun r => -d r) (fun r => neg_ne_zero.mpr (hd0 r).ne')
  have hd_off : Disjoint (Set.range fun rj : Fin P × ℤ => patternPoint ℓ (d rj.1) (c rj.1) rj.2)
      (Set.range fun rj : Fin P × ℤ => patternPoint ℓ (-d rj.1) (c rj.1) rj.2) := by
    rw [Set.disjoint_left]
    rintro _ ⟨rj, rfl⟩ ⟨rj', hrj'⟩
    have hre := congrArg Complex.re hrj'
    simp only [patternPoint] at hre
    have := hd0 rj.1; have := hd0 rj'.1
    linarith
  have hd_on : Disjoint (Set.range (verticalLatticePoint L 0))
      ((Set.range fun rj : Fin P × ℤ => patternPoint ℓ (d rj.1) (c rj.1) rj.2) ∪
        Set.range fun rj : Fin P × ℤ => patternPoint ℓ (-d rj.1) (c rj.1) rj.2) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ (⟨rj, hrj⟩ | ⟨rj, hrj⟩) <;>
    · have hre := congrArg Complex.re hrj
      simp only [verticalLatticePoint, patternPoint] at hre
      have := hd0 rj.1
      linarith
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd_on hA
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd_off hp hm)
  rw [ZeroConfig.W]
  refine hall.tsum_eq.trans ?_
  rw [lagSum_shiftSymbol hℓ hfc, ← _root_.RHTower.weilTest_self_zero, ← hKdef]
  obtain ⟨S, hS⟩ := exists_lag_window (K := K) hℓ hKs
  have hEsum : ∀ (r : Fin P) (x : ℝ), ∑' m : ℤ, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
      (Real.exp (x * (m * ℓ)) : ℂ) = ∑ m ∈ S, K (m * ℓ) * cexp (I * c r * (m * ℓ)) *
        (Real.exp (x * (m * ℓ)) : ℂ) := fun r x =>
    tsum_eq_sum fun m hm => by rw [hS m hm, zero_mul, zero_mul]
  rw [tsum_eq_sum (s := S) fun m hm => by rw [hS m hm, zero_mul]]
  simp_rw [hEsum, ← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
  have hk0 : K 0 = ∫ t, f t * conj (f t) := by
    rw [hKdef, weilTest_apply]; simp
  rw [hk0]
  have hpat : ∑ r : Fin P, ∑ m ∈ S,
      (K (m * ℓ) * cexp (I * c r * (m * ℓ)) * (Real.exp (d r * (m * ℓ)) : ℂ) +
        K (m * ℓ) * cexp (I * c r * (m * ℓ)) * (Real.exp (-d r * (m * ℓ)) : ℂ)) =
      ∑ m ∈ S, K (m * ℓ) * patternSymbol ℓ c d m := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [patternSymbol, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.cosh_eq]
    push_cast
    ring_nf
  rw [hpat]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  have hℓL : (ℓ : ℂ) * (2 * (L : ℂ) / (ℓ : ℂ)) = 2 * L := by field_simp
  linear_combination (-(∫ t, f t * conj (f t))) * hℓL

/-! ### Toeplitz equivalence and mode bound below the background Nyquist aperture -/

/-- **Toeplitz equivalence for diluted periodic patterns.** At any aperture `0 < a ≤ L/2`,
`dilutedPatternConfig` is Weil-nonnegative iff the Toeplitz form of size `⌈2a/ℓ⌉₊` of the
shifted pattern symbol `D(m) + (2L/ℓ)[m = 0]` is positive semidefinite. -/
theorem dilutedPattern_weil_nonneg_iff_toeplitz {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ}
    (c d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j')
    {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((dilutedPatternConfig hℓ hL c d hd0 hd1).W f f).re) ↔
      ∀ v : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
        0 ≤ (toeplitzForm (shiftSymbol (patternSymbol ℓ c d) (-(2 * L / ℓ))) ⌈2 * a / ℓ⌉₊ v).re := by
  set D' := shiftSymbol (patternSymbol ℓ c d) (-(2 * L / ℓ))
  constructor
  · intro h v
    by_contra hneg
    push Not at hneg
    have hna : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) * ℓ < 2 * a := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
      have : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) < 2 * a / ℓ := by linarith
      rwa [lt_div_iff₀ hℓ] at this
    obtain ⟨f, B, hB, hf, hfs, hlag⟩ := exists_test_lagSum_eq_toeplitz hℓ hna D' v
    have hfsL : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
      hfs.trans (Icc_subset_Icc (by linarith) haL)
    have hpos := h f hf hfs
    rw [W_dilutedPatternConfig hℓ hL c d hd0 hd1 hc hf hfsL, hlag, ← mul_assoc,
      show ((ℓ : ℝ) : ℂ) * (B : ℂ) = ((ℓ * B : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul] at hpos
    nlinarith [mul_pos hℓ hB]
  · intro hT f hf hfs
    have hfsL : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
      hfs.trans (Icc_subset_Icc (by linarith) haL)
    rw [W_dilutedPatternConfig hℓ hL c d hd0 hd1 hc hf hfsL]
    exact re_lagSum_nonneg_of_toeplitz hℓ D' hT hf hfs

/-- **Mode bound in an on-line background.** If a `P`-pair periodic off-line pattern superposed on
an on-line lattice of density `L` hides at aperture `0 < a ≤ L/2`, then every mode `1 ≤ m < ⌈2a/ℓ⌉₊`
satisfies `ℓ ‖D(m)‖ ≤ 2Pℓ + 2L`. -/
theorem norm_patternSymbol_le_of_diluted_hiding {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ}
    (c d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j')
    {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedPatternConfig hℓ hL c d hd0 hd1).W f f).re)
    {m : ℕ} (hm1 : 1 ≤ m) (hmn : m < ⌈2 * a / ℓ⌉₊) :
    ℓ * ‖patternSymbol ℓ c d m‖ ≤ 2 * P * ℓ + 2 * L := by
  have hT := (dilutedPattern_weil_nonneg_iff_toeplitz hℓ hL c d hd0 hd1 hc ha haL).mp h
  set D' := shiftSymbol (patternSymbol ℓ c d) (-(2 * L / ℓ)) with hD'
  have hD'herm : ∀ k, D' (-k) = conj (D' k) := by
    intro k
    simp only [hD', shiftSymbol, lagDelta, neg_eq_zero, map_sub, map_mul, Complex.conj_ofReal,
      patternSymbol_neg]
    split_ifs <;> simp
  have hle := norm_le_of_toeplitzForm_nonneg hD'herm hT hm1 hmn
  have hDm : D' m = patternSymbol ℓ c d m := by
    simp only [hD', shiftSymbol, lagDelta]
    rw [if_neg (by exact_mod_cast (by omega : m ≠ 0)), mul_zero, sub_zero]
  have hD0 : (D' 0).re = 2 * P + 2 * L / ℓ := by
    simp only [hD', shiftSymbol, lagDelta, if_true, mul_one, patternSymbol_zero]
    simp
  rw [hDm, hD0] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hℓ.le
  have hdiv : ℓ * (2 * P + 2 * L / ℓ) = 2 * P * ℓ + 2 * L := by
    rw [mul_add, mul_div_cancel₀ _ hℓ.ne']; ring
  linarith

/-! ### Constructive harmonic alignment and logarithmic visibility of diluted crystals -/

/-- **Constructive phase alignment at crystal harmonics.** For any `P`-pair uniform crystal
(`d_r = δ` and `P(θ_r − θ_{r'}) ∈ ℤ`), at every harmonic `m = k * P` (`k : ℕ`) the `P` phase
points align to one common phase `phasePoint θ r₀ ^ (k * P)`, giving
`D(kP) = 2P cosh(δ k P ℓ) (z_{r₀})^{kP}`. -/
theorem patternSymbol_crystal_mul_period {ℓ δ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (θ d : Fin P → ℝ)
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k)
    (r₀ : Fin P) (k : ℕ) :
    patternSymbol ℓ (scaledOffset ℓ θ) d ((k * P : ℕ) : ℤ) =
      ((2 * P * Real.cosh (δ * ((k * P : ℕ) * ℓ)) : ℝ) : ℂ) * phasePoint θ r₀ ^ (k * P) := by
  rw [patternSymbol_scaledOffset hℓ]
  have hpow : ∀ r : Fin P, phasePoint θ r ^ (k * P) = phasePoint θ r₀ ^ (k * P) := by
    intro r
    rw [mul_comm k P, pow_mul, pow_mul, phasePoint_pow_eq_of_crystal θ hcr r r₀]
  have hterm : ∀ r : Fin P, ((2 * Real.cosh (d r * ((k * P : ℕ) * ℓ)) : ℝ) : ℂ) *
      phasePoint θ r ^ (k * P) =
      ((2 * Real.cosh (δ * ((k * P : ℕ) * ℓ)) : ℝ) : ℂ) * phasePoint θ r₀ ^ (k * P) := by
    intro r
    rw [hunif r, hpow r]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Exact norm of a uniform crystal at every harmonic `m = kP`.** While the sub-harmonics
`1 ≤ m < P` vanish by destructive interference, every harmonic `m = kP` (`P > 0`) has exact norm
`‖D(kP)‖ = 2P cosh(δ k P ℓ)`. -/
theorem norm_patternSymbol_crystal_mul_period {ℓ δ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hunif : ∀ r, d r = δ)
    (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k) (k : ℕ) :
    ‖patternSymbol ℓ (scaledOffset ℓ θ) d ((k * P : ℕ) : ℤ)‖ =
      2 * P * Real.cosh (δ * ((k * P : ℕ) * ℓ)) := by
  let r₀ : Fin P := ⟨0, hP⟩
  rw [patternSymbol_crystal_mul_period hℓ θ d hunif hcr r₀ k, norm_mul, norm_pow]
  have hz1 : ‖phasePoint θ r₀‖ = 1 := by
    rw [phasePoint, show 2 * π * I * θ r₀ = (2 * π * θ r₀ : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [hz1, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Sub-harmonic invisibility of a diluted crystal up to `Pℓ/2`.** A `P`-pair uniform crystal
superposed on an on-line lattice of density `L` hides at every aperture `0 < a ≤ min (Pℓ/2) (L/2)`. -/
theorem diluted_crystal_hides_below_period {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ}
    (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r r', d r = d r') (hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)
    {a : ℝ} (ha : 0 < a) (haP : a ≤ P * ℓ / 2) (haL : a ≤ L / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1).W f f).re := by
  refine (dilutedPattern_weil_nonneg_iff_toeplitz hℓ hL _ d hd0 hd1
    (scaledOffset_injective hℓ hθ) ha haL).mpr ?_ f hf hfs
  intro v
  rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re]
  set D := patternSymbol ℓ (scaledOffset ℓ θ) d with hD
  have hnP : ⌈2 * a / ℓ⌉₊ ≤ P := by
    rw [Nat.ceil_le, div_le_iff₀ hℓ]; linarith
  have hmode : ∀ k : ℕ, 1 ≤ k → k < P → D k = 0 := by
    intro k hk1 hkP
    rw [hD, patternSymbol_scaledOffset hℓ]
    have hdr : ∀ r, d r = d ⟨0, by omega⟩ := fun r => hunif r _
    simp_rw [hdr, ← Finset.mul_sum]
    rw [powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
      (fun i => phasePoint_pow_eq_of_crystal θ hcr i ⟨0, by omega⟩) hk1 hkP, mul_zero]
  have hzero : ∀ m ∈ (Finset.Ioo (-(⌈2 * a / ℓ⌉₊ : ℤ)) ⌈2 * a / ℓ⌉₊).erase 0, ‖D m‖ = 0 := by
    intro m hm
    rw [Finset.mem_erase, Finset.mem_Ioo] at hm
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [hmode k (by omega) (by omega), norm_zero]
    · rw [hD, patternSymbol_neg, Complex.norm_conj, ← hD, hmode k (by omega) (by omega),
        norm_zero]
  have hG := re_toeplitzForm_ge D v
  rw [Finset.sum_eq_zero hzero, sub_zero, hD, patternSymbol_zero,
    show (2 * (P : ℂ)).re = 2 * P by simp] at hG
  have hsum_nonneg : 0 ≤ ∑ j, ‖v j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hL) hℓ]

/-- **Logarithmic visibility of a diluted crystal at harmonics `m = kP`.** Whenever `k ≥ 1`,
`kPℓ < 2a`, `a ≤ L/2`, and the constructive crystal harmonic `2Pℓ cosh(δ k P ℓ)` exceeds the
combined diagonal `2Pℓ + 2L`, the `P`-pair uniform crystal in background `L` is strictly visible at
aperture `a`. Thus crystallization cannot push the hiding horizon beyond the logarithmic scale
`a ≍ (1/2δ) log(L/(Pℓ)) + Pℓ/2`. -/
theorem diluted_crystal_visible_at_harmonic {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) {P : ℕ}
    (hP : 0 < P) (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (hka : ((k * P : ℕ) : ℝ) * ℓ < 2 * a) (haL : a ≤ L / 2)
    (hlarge : 2 * P * ℓ + 2 * L < 2 * P * ℓ * Real.cosh (δ * ((k * P : ℕ) * ℓ))) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1).W f f).re < 0 := by
  by_contra hcon
  push Not at hcon
  have ha0 : 0 < a := by
    have : (0 : ℝ) ≤ ((k * P : ℕ) : ℝ) * ℓ := by positivity
    linarith
  have hm1 : 1 ≤ k * P := Nat.mul_pos hk hP
  have hmn : k * P < ⌈2 * a / ℓ⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hℓ]
    exact hka
  have hle := norm_patternSymbol_le_of_diluted_hiding hℓ hL (scaledOffset ℓ θ) d hd0 hd1
    (scaledOffset_injective hℓ hθ) ha0 haL hcon hm1 hmn
  rw [norm_patternSymbol_crystal_mul_period hℓ hP θ d hunif hcr k] at hle
  linarith

/-- **Logarithmic visibility of an arbitrary diluted periodic pattern.** For any `P`-pair periodic
off-line pattern `(θ, d)` in background `L`, there exist `c > 0` and `K₀ : ℕ` (from Turán/Lagrange
power-sum lower bounds on the deepest nodes) such that at any aperture `a ≤ L/2` covering a window
`[(k + P - 1)ℓ/2, a]` (`k ≥ K₀`) where `c ℓ e^{d_max k ℓ} > 2Pℓ + 2L`, the diluted pattern is
strictly visible at aperture `a`. -/
theorem exists_diluted_pattern_visibility_constants {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') :
    let dmax := Finset.univ.sup' ⟨⟨0, hP⟩, Finset.mem_univ _⟩ d
    ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ (L : ℝ) (hL : 0 < L) (k : ℕ), K₀ ≤ k →
      ∀ (a : ℝ), ((k + P : ℕ) : ℝ) * ℓ / 2 < a → a ≤ L / 2 →
      2 * P * ℓ + 2 * L < c * ℓ * Real.exp (dmax * (k * ℓ)) →
      ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1).W f f).re < 0 := by
  let S : CoshSymbolData ℓ (patternSymbol ℓ (scaledOffset ℓ θ) d) P :=
    { d := d
      z := phasePoint θ
      hd0 := fun r => (hd0 r).le
      hpos := ⟨⟨0, hP⟩, hd0 _⟩
      hz := fun r => by
        rw [phasePoint, show 2 * π * I * θ r = (2 * π * θ r : ℝ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      hinj := phasePoint_injective hθ
      herm := patternSymbol_neg ℓ (scaledOffset ℓ θ) d
      modes := patternSymbol_scaledOffset hℓ θ d }
  obtain ⟨c, hc, K₀, hmode⟩ := S.exists_mode_lower hℓ
  refine ⟨c, hc, K₀ + 1, fun L hL k hk a ha haL hlarge => ?_⟩
  obtain ⟨m, hkm, hmP, hDm⟩ := hmode k (by omega)
  by_contra hcon
  push Not at hcon
  have ha0 : 0 < a := by
    have : (0 : ℝ) ≤ ((k + P : ℕ) : ℝ) * ℓ / 2 := by positivity
    linarith
  have hm1 : 1 ≤ m := by omega
  have hmn : m < ⌈2 * a / ℓ⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hℓ]
    have hm_lt : (m : ℝ) < ((k + P : ℕ) : ℝ) := by exact_mod_cast hmP
    have : (m : ℝ) * ℓ < ((k + P : ℕ) : ℝ) * ℓ := mul_lt_mul_of_pos_right hm_lt hℓ
    linarith
  have hle := norm_patternSymbol_le_of_diluted_hiding hℓ hL (scaledOffset ℓ θ) d hd0 hd1
    (scaledOffset_injective hℓ hθ) ha0 haL hcon hm1 hmn
  have hdmax_pos : 0 < S.dmax := S.dmax_pos
  have hexp : Real.exp (S.dmax * (k * ℓ)) ≤ Real.exp (S.dmax * (m * ℓ)) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hdmax_pos.le)
    refine mul_le_mul_of_nonneg_right ?_ hℓ.le
    exact_mod_cast hkm
  have hcm : c * ℓ * Real.exp (S.dmax * (k * ℓ)) ≤ ℓ * ‖patternSymbol ℓ (scaledOffset ℓ θ) d m‖ := by
    calc c * ℓ * Real.exp (S.dmax * (k * ℓ))
        ≤ c * ℓ * Real.exp (S.dmax * (m * ℓ)) := by gcongr
      _ = ℓ * (c * Real.exp (S.dmax * (m * ℓ))) := by ring
      _ ≤ ℓ * ‖patternSymbol ℓ (scaledOffset ℓ θ) d m‖ :=
          mul_le_mul_of_nonneg_left hDm hℓ.le
  change 2 * P * ℓ + 2 * L < c * ℓ * Real.exp (S.dmax * (k * ℓ)) at hlarge
  linarith

end GaloisForLFunctions.DilutionCrystallizationPincer
