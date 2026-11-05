import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.CrystallineFragilityOfOffLineLattices
import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# Mixed depths hide beyond the Ingham scale

Configurations of one depth are resolved at the Ingham scale `a > π/(2g)`
(`eq_of_mimic_of_oneDepth`), and configurations of any depths at `a > π/g`. Here the gap is shown to
be genuine: configurations of mixed depths hide beyond the Ingham scale.

* **Weighted columns** (`column`, `hasSum_Wsummand_column`). The column of FE pairs
  `½ ± δ + i(6j + r)g`, `g = 2π/L`, of multiplicity `n` has image
  `n ℓ Σ_m k(mℓ) e^{irmπ/3} 2cosh(δmℓ)`, `ℓ = L/6`, `k = f ⋆ f̃`, by Poisson summation.
  Superpositions of disjoint columns add (`hasSum_Wsummand_superpose`).
* **A window sees seven lags** (`lagSum_pair_eq`). At aperture `a < 2ℓ` only `|m| ≤ 3` survive,
  and the image is `ℓ Σ_{|m| ≤ 3} k(mℓ) D(m)` with the symbol `D(m) = Σ_r n_r e^{irmπ/3} 2T_m(P_r)`,
  `P_r = cosh(δ_r ℓ)`.
* **The symbols agree** (`mixed_symbol_eq`). With depth cosines `P = 367/6, 8, 3/2` at residues
  `0, ±1, 3` (multiplicities `29, 6016, 89929`) in `Z`, and `P = 5/3` at residues `±2`
  (multiplicity `50995`) in `Z'`, the two symbols coincide at `m = 0, …, 3`. This is four rational
  identities in Chebyshev values. The weights solve the `4 × 4` system whose determinant
  vanishes at these rational depth cosines.
* **Hiding** (`mixedDepth_mimics_beyond_ingham`, `not_eq_of_mimic_at_ingham_scale`). The union is
  separated at `g` apart from FE partners, and `Z, Z'` are mimics at every `a < L/3 = 2π/(3g)`,
  above the Ingham scale `π/(2g) = L/4`.
* **Five lags** (`mixed4_symbol_eq`, `mixedDepth_mimics_to_five_sixths`,
  `not_eq_of_mimic_below_five_sixths`). With an on-line column of multiplicity `644870094548` at
  residue `0` (`lineColumn`) against off-line columns at `±1, ±2, 3` with depth cosines
  `11381/3358, 2131/73, 30292/1679`, the symbols agree at `|m| ≤ 4`: the symbol of `Z₄` is
  constant there. So mixed depths hide up to `5π/(6g)`, and no `c < 5/6` gives a resolution
  threshold `cπ/g`.
* **Sharp** (`mixedDepth_five_sixths_sharp`). Above `5π/(6g)` the two-bump test at lag `5ℓ` sees
  the symbol difference at `m = ±5`, a nonzero rational, so `Z₄` and `Z₄'` hide exactly up to
  `5π/(6g)`; by `eq_zero_of_lagSymbol_eq_zero` no period-`6` pattern does better.

With one depth the factor `cosh` divides out and Ingham applies. With mixed depths the weights
`cosh(δ_r v)` differ between residues, and the extra freedom pays for the conditions at the lags
`π/g ≤ |v| < 4π/(3g)`.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower SquareRootThreshold RHTower.LocalCountFalsifier

/-! ### Weighted columns -/

/-- The column of FE pairs `½ ± δ + i(6j + r)(2π/L)`, `j ∈ ℤ`, all of multiplicity `n`. -/
def column {L : ℝ} (hL : 0 < L) (r : ℤ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (n : ℕ)
    (hn : 1 ≤ n) : ZeroConfig where
  carrier := (Set.range fun j : ℤ => verticalLatticePoint L δ (6 * j + r)) ∪
    Set.range fun j : ℤ => verticalLatticePoint L (-δ) (6 * j + r)
  mult := fun _ => n
  one_le_mult := fun _ _ => hn
  strip := by
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩) <;> simp only [verticalLatticePoint] <;> constructor <;>
      linarith
  reflect_mem := by
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inr ⟨j, (reflect_verticalLatticePoint L δ _).symm⟩
    · exact Or.inl ⟨j, by rw [reflect_verticalLatticePoint, neg_neg]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := fun T₁ T₂ =>
    ((offLineLatticeConfig hL hδ0 hδ1).finite_window T₁ T₂).subset (by
      rintro _ ⟨(⟨j, rfl⟩ | ⟨j, rfl⟩), h⟩
      · exact ⟨Or.inl ⟨_, rfl⟩, h⟩
      · exact ⟨Or.inr ⟨_, rfl⟩, h⟩)

theorem temperedConfig_column {L : ℝ} (hL : 0 < L) (r : ℤ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (n : ℕ) (hn : 1 ≤ n) : TemperedConfig (column hL r hδ0 hδ1 n hn) := by
  have hsub : (column hL r hδ0 hδ1 n hn).carrier ⊆ (offLineLatticeConfig hL hδ0 hδ1).carrier := by
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  let ι : (column hL r hδ0 hδ1 n hn).carrier → (offLineLatticeConfig hL hδ0 hδ1).carrier :=
    fun ρ => ⟨ρ.1, hsub ρ.2⟩
  have hinj : Function.Injective ι := fun _ _ h =>
    Subtype.ext (by simpa [ι] using congrArg Subtype.val h)
  have hsum := ((temperedConfig_offLineLatticeConfig hL hδ0 hδ1).comp_injective hinj).mul_left
    (n : ℝ)
  exact hsum.congr fun ρ => by
    simp [ι, column, offLineLatticeConfig, div_eq_mul_inv]

/-- The lag sum `ℓ Σ_m K(mℓ) e^{icmℓ} e^{smℓ}` of a translated lattice of depth `s`. -/
def lagSum (ℓ c s : ℝ) (K : ℝ → ℂ) : ℂ :=
  ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, K (m * ℓ) * cexp (I * c * (m * ℓ)) * (Real.exp (s * (m * ℓ)) : ℂ)

/-- **The image series of a column.** -/
theorem hasSum_Wsummand_column {L : ℝ} (hL : 0 < L) (r : ℤ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {A : ℝ}
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) :
    HasSum (fun ρ : (column hL r hδ0 hδ1 n hn).carrier =>
        (column hL r hδ0 hδ1 n hn).Wsummand f f ρ)
      ((n : ℂ) * (lagSum (L / 6) ((r : ℝ) * (2 * π / L)) δ (EF.weilTest f f) +
        lagSum (L / 6) ((r : ℝ) * (2 * π / L)) (-δ) (EF.weilTest f f))) := by
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  have hℓ : 0 < L / 6 := by positivity
  have hpt : ∀ (s : ℝ) (j : ℤ), (column hL r hδ0 hδ1 n hn).Wsummand f f
      (verticalLatticePoint L s (6 * j + r)) = (n : ℂ) * paperFT (EF.weilTest f f)
        ((((r : ℝ) * (2 * π / L) + j * (2 * π / (L / 6)) : ℝ) : ℂ) - I * s) := by
    intro s j
    have e : (((6 * j + r : ℤ) : ℝ) * (2 * π / L)) = (r : ℝ) * (2 * π / L) + j * (2 * π / (L / 6)) := by
      push_cast
      field_simp
      ring
    unfold ZeroConfig.Wsummand
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, gammaOf_verticalLatticePoint, e]
    simp only [column]
    ring
  have hinj : ∀ s : ℝ, Function.Injective fun j : ℤ => verticalLatticePoint L s (6 * j + r) :=
    fun s j j' h => by
      have := verticalLatticePoint_injective hL s h
      omega
  have hside : ∀ s : ℝ, HasSum (fun ρ : Set.range (fun j : ℤ => verticalLatticePoint L s (6 * j + r)) =>
      (column hL r hδ0 hδ1 n hn).Wsummand f f ρ)
      ((n : ℂ) * lagSum (L / 6) ((r : ℝ) * (2 * π / L)) s (EF.weilTest f f)) := by
    intro s
    rw [(hinj s).hasSum_range_iff]
    exact ((hasSum_paperFT_translate hℓ hK hKs _ s).mul_left (n : ℂ)).congr_fun fun j => by
      simp only [Function.comp_apply]
      exact hpt s j
  have hd : Disjoint (Set.range fun j : ℤ => verticalLatticePoint L δ (6 * j + r))
      (Set.range fun j : ℤ => verticalLatticePoint L (-δ) (6 * j + r)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, rfl⟩ ⟨j', hj'⟩
    have hre := congrArg Complex.re hj'
    simp only [verticalLatticePoint] at hre
    linarith
  rw [mul_add]
  exact HasSum.add_disjoint (f := (column hL r hδ0 hδ1 n hn).Wsummand f f) hd (hside δ) (hside (-δ))

/-! ### Superposition -/

theorem superpose_mult_left {Z₁ Z₂ : ZeroConfig} (hd : Disjoint Z₁.carrier Z₂.carrier) {ρ : ℂ}
    (hρ : ρ ∈ Z₁.carrier) : (superpose Z₁ Z₂).mult ρ = Z₁.mult ρ := by
  have h2 : ρ ∉ Z₂.carrier := Set.disjoint_left.mp hd hρ
  simp only [superpose, if_pos hρ, if_neg h2, add_zero]

theorem superpose_mult_right {Z₁ Z₂ : ZeroConfig} (hd : Disjoint Z₁.carrier Z₂.carrier) {ρ : ℂ}
    (hρ : ρ ∈ Z₂.carrier) : (superpose Z₁ Z₂).mult ρ = Z₂.mult ρ := by
  have h1 : ρ ∉ Z₁.carrier := Set.disjoint_right.mp hd hρ
  simp only [superpose, if_pos hρ, if_neg h1, zero_add]

/-- The image series of a disjoint superposition is the sum of the two series. -/
theorem hasSum_Wsummand_superpose {Z₁ Z₂ : ZeroConfig} (hd : Disjoint Z₁.carrier Z₂.carrier)
    {f : ℝ → ℂ} {A₁ A₂ : ℂ} (h₁ : HasSum (fun ρ : Z₁.carrier => Z₁.Wsummand f f ρ) A₁)
    (h₂ : HasSum (fun ρ : Z₂.carrier => Z₂.Wsummand f f ρ) A₂) :
    HasSum (fun ρ : (superpose Z₁ Z₂).carrier => (superpose Z₁ Z₂).Wsummand f f ρ)
      (A₁ + A₂) := by
  have h₁' : HasSum ((superpose Z₁ Z₂).Wsummand f f ∘ ((↑) : Z₁.carrier → ℂ)) A₁ :=
    h₁.congr_fun fun ρ => by
      simp only [Function.comp_apply, ZeroConfig.Wsummand, superpose_mult_left hd ρ.2]
  have h₂' : HasSum ((superpose Z₁ Z₂).Wsummand f f ∘ ((↑) : Z₂.carrier → ℂ)) A₂ :=
    h₂.congr_fun fun ρ => by
      simp only [Function.comp_apply, ZeroConfig.Wsummand, superpose_mult_right hd ρ.2]
  exact HasSum.add_disjoint hd h₁' h₂'

theorem temperedConfig_superpose {Z₁ Z₂ : ZeroConfig} (hd : Disjoint Z₁.carrier Z₂.carrier)
    (h₁ : TemperedConfig Z₁) (h₂ : TemperedConfig Z₂) : TemperedConfig (superpose Z₁ Z₂) := by
  obtain ⟨a₁, ha₁⟩ := h₁
  obtain ⟨a₂, ha₂⟩ := h₂
  refine ⟨a₁ + a₂, HasSum.add_disjoint (f := fun ρ : ℂ =>
    ((superpose Z₁ Z₂).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) hd ?_ ?_⟩
  · exact ha₁.congr_fun fun ρ => by
      simp only [Function.comp_apply, superpose_mult_left hd ρ.2]
  · exact ha₂.congr_fun fun ρ => by
      simp only [Function.comp_apply, superpose_mult_right hd ρ.2]

theorem disjoint_column {L : ℝ} (hL : 0 < L) {r r' : ℤ} {δ δ' : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hδ0' : 0 < δ') (hδ1' : δ' ≤ 1 / 2) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : ∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + r') :
    Disjoint (column hL r hδ0 hδ1 n hn).carrier (column hL r' hδ0' hδ1' n' hn').carrier := by
  have him : ∀ (s s' : ℝ) (j j' : ℤ), verticalLatticePoint L s (6 * j + r) ≠
      verticalLatticePoint L s' (6 * j' + r') := by
    intro s s' j j' he
    have hi := congrArg Complex.im he
    simp only [verticalLatticePoint] at hi
    have hc : (((6 * j + r : ℤ) : ℝ)) = ((6 * j' + r' : ℤ) : ℝ) :=
      mul_right_cancel₀ (by positivity : (2 * π / L) ≠ 0) hi
    exact h j j' (by exact_mod_cast hc)
  rw [Set.disjoint_left]
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩) (⟨j', hj'⟩ | ⟨j', hj'⟩)
  all_goals exact him _ _ _ _ hj'.symm

/-! ### Values of the lag symbol -/

/-- `cos(kπ/3)` through `k mod 6`. -/
def cosTable (s : ℤ) : ℝ := if s = 0 then 1 else if s = 3 then -1 else if s = 1 ∨ s = 5 then 1 / 2
  else -1 / 2

theorem cos_int_mul_pi_div_three (k : ℤ) : Real.cos (k * π / 3) = cosTable (k % 6) := by
  have hk : (k : ℝ) * π / 3 = ((k % 6 : ℤ) : ℝ) * π / 3 + ((k / 6 : ℤ) : ℝ) * (2 * π) := by
    have hz : k = k % 6 + 6 * (k / 6) := by omega
    have h' : (k : ℝ) = ((k % 6 : ℤ) : ℝ) + 6 * ((k / 6 : ℤ) : ℝ) := by
      exact_mod_cast hz
    rw [h']
    ring
  rw [hk, Real.cos_add_int_mul_two_pi]
  have h0 : 0 ≤ k % 6 := Int.emod_nonneg k (by norm_num)
  have h6 : k % 6 < 6 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨s, hs⟩ : ∃ s, s = k % 6 := ⟨_, rfl⟩
  rw [← hs] at h0 h6 ⊢
  have c2 : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have c4 : Real.cos (4 * π / 3) = -1 / 2 := by
    rw [show 4 * π / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num
  have c5 : Real.cos (5 * π / 3) = 1 / 2 := by
    rw [show 5 * π / 3 = 2 * π - π / 3 by ring, Real.cos_two_pi_sub, Real.cos_pi_div_three]
  interval_cases s
  · simp [cosTable]
  · simp [cosTable, Real.cos_pi_div_three]
  · norm_num [cosTable, c2]
  · rw [show ((3 : ℤ) : ℝ) * π / 3 = π by push_cast; ring, Real.cos_pi]; simp [cosTable]
  · norm_num [cosTable, c4]
  · norm_num [cosTable, c5]

/-- `cosh(mx)` for `|m| ≤ 3` through Chebyshev polynomials of `cosh x`. -/
theorem cosh_mul_int_eq {x P : ℝ} (hx : Real.cosh x = P) (m : ℤ) (hm : -5 ≤ m ∧ m ≤ 5) :
    Real.cosh (x * m) = if m = 0 then 1 else if m = 1 ∨ m = -1 then P
      else if m = 2 ∨ m = -2 then 2 * P ^ 2 - 1 else if m = 3 ∨ m = -3 then 4 * P ^ 3 - 3 * P
      else if m = 4 ∨ m = -4 then 8 * P ^ 4 - 8 * P ^ 2 + 1
      else 16 * P ^ 5 - 20 * P ^ 3 + 5 * P := by
  have c2' : ∀ y : ℝ, Real.cosh (2 * y) = 2 * Real.cosh y ^ 2 - 1 := fun y => by
    rw [Real.cosh_two_mul]; nlinarith [Real.cosh_sq y]
  have c2 : Real.cosh (2 * x) = 2 * P ^ 2 - 1 := by rw [c2', hx]
  have c3 : Real.cosh (3 * x) = 4 * P ^ 3 - 3 * P := by rw [Real.cosh_three_mul, hx]
  have c4 : Real.cosh (4 * x) = 8 * P ^ 4 - 8 * P ^ 2 + 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, c2', c2]; ring
  have c5 : Real.cosh (5 * x) = 16 * P ^ 5 - 20 * P ^ 3 + 5 * P := by
    have h5 := Real.cosh_add (4 * x) x
    have h3 := Real.cosh_sub (4 * x) x
    rw [show 4 * x + x = 5 * x by ring] at h5
    rw [show 4 * x - x = 3 * x by ring, c3] at h3
    rw [c4, hx] at h5 h3
    linear_combination h5 + h3
  obtain ⟨h1, h2⟩ := hm
  interval_cases m
  · rw [show x * ((-5 : ℤ) : ℝ) = -(5 * x) by push_cast; ring, Real.cosh_neg, c5]; norm_num
  · rw [show x * ((-4 : ℤ) : ℝ) = -(4 * x) by push_cast; ring, Real.cosh_neg, c4]; norm_num
  · rw [show x * ((-3 : ℤ) : ℝ) = -(3 * x) by push_cast; ring, Real.cosh_neg, c3]; norm_num
  · rw [show x * ((-2 : ℤ) : ℝ) = -(2 * x) by push_cast; ring, Real.cosh_neg, c2]; norm_num
  · rw [show x * ((-1 : ℤ) : ℝ) = -x by push_cast; ring, Real.cosh_neg, hx]; norm_num
  · simp
  · simp [hx]
  · rw [show x * ((2 : ℤ) : ℝ) = 2 * x by push_cast; ring, c2]; norm_num
  · rw [show x * ((3 : ℤ) : ℝ) = 3 * x by push_cast; ring, c3]; norm_num
  · rw [show x * ((4 : ℤ) : ℝ) = 4 * x by push_cast; ring, c4]; norm_num
  · rw [show x * ((5 : ℤ) : ℝ) = 5 * x by push_cast; ring, c5]; norm_num

/-- The column symbol at residue `r`, scaled depth `x`, lag index `m`. -/
def colSym (r : ℤ) (x : ℝ) (m : ℤ) : ℂ :=
  cexp (I * ((((r * m : ℤ) : ℝ) * π / 3 : ℝ) : ℂ)) * ((2 * Real.cosh (x * m) : ℝ) : ℂ)

theorem cexp_I_mul_ofReal (θ : ℝ) : cexp (I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem colSym_pair (r : ℤ) (x : ℝ) (m : ℤ) :
    colSym r x m + colSym (-r) x m =
      ((2 * Real.cos (((r * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x * m)) : ℝ) : ℂ) := by
  have e : (((-r * m : ℤ) : ℝ) * π / 3) = -((((r * m : ℤ) : ℝ) * π / 3)) := by push_cast; ring
  simp only [colSym]
  rw [e, cexp_I_mul_ofReal, cexp_I_mul_ofReal, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem colSym_zero (x : ℝ) (m : ℤ) : colSym 0 x m = ((2 * Real.cosh (x * m) : ℝ) : ℂ) := by
  simp [colSym]

theorem colSym_three (x : ℝ) (m : ℤ) :
    colSym 3 x m = ((Real.cos (((3 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x * m)) : ℝ) : ℂ) := by
  have e : (((3 * m : ℤ) : ℝ) * π / 3) = (m : ℝ) * π := by push_cast; ring
  simp only [colSym]
  rw [cexp_I_mul_ofReal, e, Real.sin_int_mul_pi]
  push_cast
  ring

/-- A kernel living in `|u| < (N + 1)ℓ` vanishes at the lags `mℓ`, `|m| > N`. -/
theorem kernel_lag_eq_zero {L : ℝ} (hL : 0 < L) (N : ℕ) {K : ℝ → ℂ} {A : ℝ}
    (hK : ∀ u, K u ≠ 0 → |u| ≤ A) (hA : A < (N + 1) * (L / 6)) (m : ℤ)
    (hm : m ∉ Finset.Icc (-(N : ℤ)) N) : K (m * (L / 6)) = 0 := by
  have hℓ : 0 < L / 6 := by positivity
  by_contra hne
  have h1 := hK _ hne
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
  have h4 : (N : ℝ) + 1 ≤ |(m : ℝ)| := by
    rcases hm with h | h
    · have : (m : ℝ) ≤ -((N : ℝ) + 1) := by exact_mod_cast (by omega : m ≤ -((N : ℤ) + 1))
      rw [abs_of_neg (by linarith)]; linarith
    · have : (N : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : (N : ℤ) + 1 ≤ m)
      rw [abs_of_pos (by linarith)]; linarith
  rw [abs_mul, abs_of_pos hℓ] at h1
  nlinarith

/-- A column pair of lag sums is a finite symbol sum when the kernel lives in `|u| < (N + 1)ℓ`. -/
theorem lagSum_pair_eq {L : ℝ} (hL : 0 < L) (r : ℤ) (x : ℝ) {K : ℝ → ℂ} {A : ℝ} (N : ℕ)
    (hK : ∀ u, K u ≠ 0 → |u| ≤ A) (hA : A < (N + 1) * (L / 6)) :
    lagSum (L / 6) ((r : ℝ) * (2 * π / L)) (6 * x / L) K +
        lagSum (L / 6) ((r : ℝ) * (2 * π / L)) (-(6 * x / L)) K =
      ((L / 6 : ℝ) : ℂ) * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, K (m * (L / 6)) * colSym r x m := by
  have hzero := kernel_lag_eq_zero hL N hK hA
  unfold lagSum
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) fun m hm => by
      rw [hzero m hm, zero_mul, zero_mul],
    tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) fun m hm => by rw [hzero m hm, zero_mul, zero_mul],
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e1 : cexp (I * (((r : ℝ) * (2 * π / L) : ℝ) : ℂ) * ((m : ℂ) * ((L / 6 : ℝ) : ℂ))) =
      cexp (I * ((((r * m : ℤ) : ℝ) * π / 3 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    field_simp
    ring
  have e2 : 6 * x / L * (m * (L / 6)) = x * m := by field_simp
  have e3 : -(6 * x / L) * (m * (L / 6)) = -(x * m) := by field_simp
  simp only [colSym]
  rw [e1, e2, e3, Real.cosh_eq]
  push_cast
  ring

/-! ### Separation -/

theorem column_mem {L : ℝ} (hL : 0 < L) (r : ℤ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) {ρ : ℂ} (hρ : ρ ∈ (column hL r hδ0 hδ1 n hn).carrier) :
    ∃ j : ℤ, ρ.im = ((6 * j + r : ℤ) : ℝ) * (2 * π / L) ∧ |ρ.re - 1 / 2| = δ := by
  rcases hρ with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨j, rfl, by simp [verticalLatticePoint, abs_of_pos hδ0]⟩
  · exact ⟨j, rfl, by simp [verticalLatticePoint, abs_of_pos hδ0]⟩

/-- Points on the ordinate lattice `(2π/L)ℤ` whose depth is a function of the ordinate index are
separated at `2π/L` apart from FE partners. -/
theorem separated_of_depthFun {L : ℝ} (hL : 0 < L) {U : Set ℂ} (D : ℤ → ℝ)
    (hU : ∀ ρ ∈ U, ∃ k : ℤ, ρ.im = k * (2 * π / L) ∧ |ρ.re - 1 / 2| = D k) :
    ∀ ρ ∈ U, ∀ ρ' ∈ U, ρ' ≠ ρ → ρ' ≠ reflect ρ → 2 * π / L ≤ |ρ.im - ρ'.im| := by
  intro ρ hρ ρ' hρ' hne hne'
  obtain ⟨k, hk, hkD⟩ := hU ρ hρ
  obtain ⟨k', hk', hkD'⟩ := hU ρ' hρ'
  have hg : 0 < 2 * π / L := by positivity
  by_cases hkk : k = k'
  · subst hkk
    exfalso
    have him : ρ'.im = ρ.im := by rw [hk, hk']
    have habs : |ρ'.re - 1 / 2| = |ρ.re - 1 / 2| := by rw [hkD, hkD']
    have hrr : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    have hri : (reflect ρ).im = ρ.im := by simp [reflect]
    rcases abs_eq_abs.mp habs with h | h
    · exact hne (Complex.ext (by linarith) him)
    · exact hne' (Complex.ext (by rw [hrr]; linarith) (by rw [hri]; exact him))
  · rw [hk, hk', ← sub_mul, abs_mul, abs_of_pos hg]
    have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
      have : (1 : ℤ) ≤ |k - k'| := Int.one_le_abs (sub_ne_zero.mpr hkk)
      exact_mod_cast this
    nlinarith

/-! ### The symbol identity -/

theorem mixed_symbol_real {x0 x1 x2 x3 : ℝ} (h0 : Real.cosh x0 = 367 / 6) (h1 : Real.cosh x1 = 8)
    (h2 : Real.cosh x2 = 5 / 3) (h3 : Real.cosh x3 = 3 / 2) (m : ℤ) (hm : -3 ≤ m ∧ m ≤ 3) :
    29 * (2 * Real.cosh (x0 * m)) +
        6016 * (2 * Real.cos (((1 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x1 * m))) +
        89929 * (Real.cos (((3 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x3 * m))) =
      50995 * (2 * Real.cos (((2 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x2 * m))) := by
  rw [cos_int_mul_pi_div_three, cos_int_mul_pi_div_three, cos_int_mul_pi_div_three,
    cosh_mul_int_eq h0 m ⟨by omega, by omega⟩, cosh_mul_int_eq h1 m ⟨by omega, by omega⟩,
    cosh_mul_int_eq h2 m ⟨by omega, by omega⟩, cosh_mul_int_eq h3 m ⟨by omega, by omega⟩]
  obtain ⟨hm1, hm2⟩ := hm
  interval_cases m <;> norm_num [cosTable]

/-- **The two symbols agree at `|m| ≤ 3`.** -/
theorem mixed_symbol_eq {x0 x1 x2 x3 : ℝ} (h0 : Real.cosh x0 = 367 / 6) (h1 : Real.cosh x1 = 8)
    (h2 : Real.cosh x2 = 5 / 3) (h3 : Real.cosh x3 = 3 / 2) (m : ℤ) (hm : -3 ≤ m ∧ m ≤ 3) :
    29 * colSym 0 x0 m + 6016 * colSym 1 x1 m + 6016 * colSym (-1) x1 m +
        89929 * colSym 3 x3 m = 50995 * colSym 2 x2 m + 50995 * colSym (-2) x2 m := by
  have hrC := congrArg (fun t : ℝ => (t : ℂ)) (mixed_symbol_real h0 h1 h2 h3 m hm)
  have p1 := colSym_pair 1 x1 m
  have p2 := colSym_pair 2 x2 m
  have z0 := colSym_zero x0 m
  have z3 := colSym_three x3 m
  push_cast at hrC p1 p2 z0 z3
  linear_combination 29 * z0 + 6016 * p1 + 89929 * z3 - 50995 * p2 + hrC

/-! ### The configurations -/

/-- The scaled depth `x` with `cosh x = P`. -/
def acoshOf (P : ℝ) : ℝ := Real.arsinh √(P ^ 2 - 1)

theorem acoshOf_props {P : ℝ} (hP : 1 < P) :
    0 < acoshOf P ∧ acoshOf P ≤ P ∧ Real.cosh (acoshOf P) = P := by
  have hy0 : 0 < √(P ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hy2 : √(P ^ 2 - 1) ^ 2 = P ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hx0 : 0 < acoshOf P := Real.arsinh_pos_iff.mpr hy0
  refine ⟨hx0, ?_, ?_⟩
  · have h1 : acoshOf P ≤ √(P ^ 2 - 1) := by
      have := (Real.self_le_sinh_iff (x := acoshOf P)).mpr hx0.le
      rwa [acoshOf, Real.sinh_arsinh] at this
    have h2 : √(P ^ 2 - 1) ≤ P := by nlinarith
    linarith
  · rw [acoshOf, Real.cosh_arsinh, hy2, show 1 + (P ^ 2 - 1) = P ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

theorem mixedDepth_pos {L : ℝ} (hL : 734 ≤ L) {P : ℝ} (hP : 1 < P) : 0 < 6 * acoshOf P / L := by
  have := (acoshOf_props hP).1
  have : 0 < L := by linarith
  positivity

theorem mixedDepth_le {L : ℝ} (hL : 734 ≤ L) {P : ℝ} (hP : 1 < P) (hP' : P ≤ 367 / 6) :
    6 * acoshOf P / L ≤ 1 / 2 := by
  have := (acoshOf_props hP).2.1
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The column of residue `r`, depth `6 acosh(P)/L` and multiplicity `n`. -/
def mixedColumn {L : ℝ} (hL : 734 ≤ L) (r : ℤ) {P : ℝ} (hP : 1 < P) (hP' : P ≤ 367 / 6) (n : ℕ)
    (hn : 1 ≤ n) : ZeroConfig :=
  column (L := L) (by linarith) r (mixedDepth_pos hL hP) (mixedDepth_le hL hP hP') n hn

/-- `Z`: residues `0, ±1, 3` with depth cosines `367/6, 8, 3/2` and multiplicities
`29, 6016, 89929`, ordinate period `6g`, `g = 2π/L`. -/
def mixedZ {L : ℝ} (hL : 734 ≤ L) : ZeroConfig :=
  superpose (superpose (superpose
    (mixedColumn hL 0 (P := 367 / 6) (by norm_num) (by norm_num) 29 (by norm_num))
    (mixedColumn hL 1 (P := 8) (by norm_num) (by norm_num) 6016 (by norm_num)))
    (mixedColumn hL (-1) (P := 8) (by norm_num) (by norm_num) 6016 (by norm_num)))
    (mixedColumn hL 3 (P := 3 / 2) (by norm_num) (by norm_num) 89929 (by norm_num))

/-- `Z'`: residues `±2` with depth cosine `5/3` and multiplicity `50995`. -/
def mixedZ' {L : ℝ} (hL : 734 ≤ L) : ZeroConfig :=
  superpose (mixedColumn hL 2 (P := 5 / 3) (by norm_num) (by norm_num) 50995 (by norm_num))
    (mixedColumn hL (-2) (P := 5 / 3) (by norm_num) (by norm_num) 50995 (by norm_num))

theorem disjoint_mixedColumn {L : ℝ} (hL : 734 ≤ L) {r r' : ℤ} {P P' : ℝ} (hP : 1 < P)
    (hP' : P ≤ 367 / 6) (hQ : 1 < P') (hQ' : P' ≤ 367 / 6) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : ∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + r') :
    Disjoint (mixedColumn hL r hP hP' n hn).carrier (mixedColumn hL r' hQ hQ' n' hn').carrier := by
  unfold mixedColumn
  exact disjoint_column _ _ _ _ _ _ _ h

theorem temperedConfig_mixedColumn {L : ℝ} (hL : 734 ≤ L) (r : ℤ) {P : ℝ} (hP : 1 < P)
    (hP' : P ≤ 367 / 6) (n : ℕ) (hn : 1 ≤ n) : TemperedConfig (mixedColumn hL r hP hP' n hn) := by
  unfold mixedColumn
  exact temperedConfig_column _ _ _ _ _ _

theorem mixedColumn_mem {L : ℝ} (hL : 734 ≤ L) (r : ℤ) {P : ℝ} (hP : 1 < P) (hP' : P ≤ 367 / 6)
    {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ} (hρ : ρ ∈ (mixedColumn hL r hP hP' n hn).carrier) :
    ∃ j : ℤ, ρ.im = ((6 * j + r : ℤ) : ℝ) * (2 * π / L) ∧ |ρ.re - 1 / 2| = 6 * acoshOf P / L := by
  unfold mixedColumn at hρ
  exact column_mem _ _ _ _ _ hρ

/-- The image series of a mixed column against a window of aperture `a < L/3`. -/
theorem hasSum_mixedColumn {L : ℝ} (hL : 734 ≤ L) (r : ℤ) {P : ℝ} (hP : 1 < P)
    (hP' : P ≤ 367 / 6) (n : ℕ) (hn : 1 ≤ n) (N : ℕ) {a : ℝ} (ha : 2 * a < (N + 1) * (L / 6))
    {f : ℝ → ℂ} (hf : ApertureWindow a f) :
    HasSum (fun ρ : (mixedColumn hL r hP hP' n hn).carrier =>
        (mixedColumn hL r hP hP' n hn).Wsummand f f ρ)
      ((n : ℂ) * (((L / 6 : ℝ) : ℂ) * ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        EF.weilTest f f (m * (L / 6)) * colSym r (acoshOf P) m)) := by
  have hL0 : 0 < L := by linarith
  have hfs : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rw [show 2 * a / 2 = a by ring]; exact hf.2
  have h := hasSum_Wsummand_column hL0 r (mixedDepth_pos hL hP)
    (mixedDepth_le hL hP hP') n hn hf.1 hfs
  rw [lagSum_pair_eq hL0 r (acoshOf P) N (weilTest_abs_le hfs hfs) ha] at h
  unfold mixedColumn
  exact h

/-! ### Mixed depths hide beyond the Ingham scale -/

/-- **Mixed depths hide beyond the Ingham scale.** For `L ≥ 734` the configurations `Z = mixedZ`,
`Z' = mixedZ'` are tempered, disjoint and nonempty; their union is separated at `g = 2π/L` apart
from FE partners; and they are mimics at every aperture `a < L/3 = 2π/(3g)`, above the Ingham
scale `π/(2g) = L/4`.

The union is a periodic pattern of period `6g` with FE pairs at all six residues. Poisson
summation gives `W = ℓ Σ_m k(mℓ) D(m)`, `ℓ = L/6`, and a window of aperture `a < 2ℓ` sees only
`|m| ≤ 3`. There the two symbols agree (`mixed_symbol_eq`): with `c_k = cos(kπ/3)` and Chebyshev
values `T_m`, `29 T_m(367/6) + 12032 c_m T_m(8) + 89929 c_{3m} T_m(3/2) = 101990 c_{2m} T_m(5/3)`. -/
theorem mixedDepth_mimics_beyond_ingham {L : ℝ} (hL : 734 ≤ L) :
    TemperedConfig (mixedZ hL) ∧ TemperedConfig (mixedZ' hL) ∧ (mixedZ hL).carrier.Nonempty ∧
      Disjoint (mixedZ hL).carrier (mixedZ' hL).carrier ∧
      (∀ ρ ∈ (mixedZ hL).carrier ∪ (mixedZ' hL).carrier,
        ∀ ρ' ∈ (mixedZ hL).carrier ∪ (mixedZ' hL).carrier, ρ' ≠ ρ → ρ' ≠ reflect ρ →
          2 * π / L ≤ |ρ.im - ρ'.im|) ∧
      ∀ a < L / 3, ∀ f, ApertureWindow a f → (mixedZ hL).W f f = (mixedZ' hL).W f f := by
  have hL0 : 0 < L := by linarith
  have q0 : (1 : ℝ) < 367 / 6 := by norm_num
  have q0' : (367 / 6 : ℝ) ≤ 367 / 6 := le_rfl
  have q1 : (1 : ℝ) < 8 := by norm_num
  have q1' : (8 : ℝ) ≤ 367 / 6 := by norm_num
  have q2 : (1 : ℝ) < 5 / 3 := by norm_num
  have q2' : (5 / 3 : ℝ) ≤ 367 / 6 := by norm_num
  have q3 : (1 : ℝ) < 3 / 2 := by norm_num
  have q3' : (3 / 2 : ℝ) ≤ 367 / 6 := by norm_num
  have n29 : 1 ≤ 29 := by norm_num
  have n6016 : 1 ≤ 6016 := by norm_num
  have n89929 : 1 ≤ 89929 := by norm_num
  have n50995 : 1 ≤ 50995 := by norm_num
  -- disjointness of the six columns
  have d01 := disjoint_mixedColumn hL (r := 0) (r' := 1) q0 q0' q1 q1' n29 n6016
    (by intro j j'; omega)
  have d0m1 := disjoint_mixedColumn hL (r := 0) (r' := -1) q0 q0' q1 q1' n29 n6016
    (by intro j j'; omega)
  have d1m1 := disjoint_mixedColumn hL (r := 1) (r' := -1) q1 q1' q1 q1' n6016 n6016
    (by intro j j'; omega)
  have d03 := disjoint_mixedColumn hL (r := 0) (r' := 3) q0 q0' q3 q3' n29 n89929
    (by intro j j'; omega)
  have d13 := disjoint_mixedColumn hL (r := 1) (r' := 3) q1 q1' q3 q3' n6016 n89929
    (by intro j j'; omega)
  have dm13 := disjoint_mixedColumn hL (r := -1) (r' := 3) q1 q1' q3 q3' n6016 n89929
    (by intro j j'; omega)
  have d2m2 := disjoint_mixedColumn hL (r := 2) (r' := -2) q2 q2' q2 q2' n50995 n50995
    (by intro j j'; omega)
  have dZ1 : Disjoint (superpose (mixedColumn hL 0 q0 q0' 29 n29)
      (mixedColumn hL 1 q1 q1' 6016 n6016)).carrier (mixedColumn hL (-1) q1 q1' 6016 n6016).carrier :=
    Set.disjoint_union_left.mpr ⟨d0m1, d1m1⟩
  have dZ2 : Disjoint (superpose (superpose (mixedColumn hL 0 q0 q0' 29 n29)
      (mixedColumn hL 1 q1 q1' 6016 n6016)) (mixedColumn hL (-1) q1 q1' 6016 n6016)).carrier
      (mixedColumn hL 3 q3 q3' 89929 n89929).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d03, d13⟩, dm13⟩
  have dcol : ∀ {r : ℤ} {P : ℝ} (hP : 1 < P) (hP' : P ≤ 367 / 6) {n : ℕ} (hn : 1 ≤ n),
      (∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + 2) → (∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + -2) →
      Disjoint (mixedColumn hL r hP hP' n hn).carrier (mixedZ' hL).carrier :=
    by
    intro r P hP hP' n hn h2 hm2
    exact Set.disjoint_union_right.mpr
      ⟨disjoint_mixedColumn hL hP hP' q2 q2' hn n50995 h2,
        disjoint_mixedColumn hL hP hP' q2 q2' hn n50995 hm2⟩
  have dZZ : Disjoint (mixedZ hL).carrier (mixedZ' hL).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨dcol q0 q0' n29 (by intro j j'; omega) (by intro j j'; omega),
          dcol q1 q1' n6016 (by intro j j'; omega) (by intro j j'; omega)⟩,
        dcol q1 q1' n6016 (by intro j j'; omega) (by intro j j'; omega)⟩,
      dcol q3 q3' n89929 (by intro j j'; omega) (by intro j j'; omega)⟩
  refine ⟨?_, ?_, ?_, dZZ, ?_, ?_⟩
  -- temperedness
  · exact temperedConfig_superpose dZ2 (temperedConfig_superpose dZ1
      (temperedConfig_superpose d01 (temperedConfig_mixedColumn ..)
        (temperedConfig_mixedColumn ..)) (temperedConfig_mixedColumn ..))
      (temperedConfig_mixedColumn ..)
  · exact temperedConfig_superpose d2m2 (temperedConfig_mixedColumn ..)
      (temperedConfig_mixedColumn ..)
  -- a point of `Z`
  · exact ⟨_, Or.inl (Or.inl (Or.inl (Or.inl ⟨0, rfl⟩)))⟩
  -- separation: the depth is a function of the ordinate index mod 6
  · set δ := fun P : ℝ => 6 * acoshOf P / L with hδ
    refine separated_of_depthFun hL0 (fun k => if k % 6 = 0 then δ (367 / 6) else
      if k % 6 = 3 then δ (3 / 2) else if k % 6 = 1 ∨ k % 6 = 5 then δ 8 else δ (5 / 3)) ?_
    intro ρ hρ
    rcases hρ with (((h | h) | h) | h) | (h | h)
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 0 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 1 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 1) % 6 = 1 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL (-1) _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + -1) % 6 = 5 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 3 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 3) % 6 = 3 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 2 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 2) % 6 = 2 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL (-2) _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + -2) % 6 = 4 by omega]⟩
  -- mimicry
  · intro a ha f hf
    have ha3 : 2 * a < ((3 : ℕ) + 1) * (L / 6) := by push_cast; linarith
    have hZ := hasSum_Wsummand_superpose dZ2 (hasSum_Wsummand_superpose dZ1
      (hasSum_Wsummand_superpose d01 (hasSum_mixedColumn hL 0 q0 q0' 29 n29 3 ha3 hf)
        (hasSum_mixedColumn hL 1 q1 q1' 6016 n6016 3 ha3 hf))
      (hasSum_mixedColumn hL (-1) q1 q1' 6016 n6016 3 ha3 hf))
      (hasSum_mixedColumn hL 3 q3 q3' 89929 n89929 3 ha3 hf)
    have hZ' := hasSum_Wsummand_superpose d2m2 (hasSum_mixedColumn hL 2 q2 q2' 50995 n50995 3 ha3 hf)
      (hasSum_mixedColumn hL (-2) q2 q2' 50995 n50995 3 ha3 hf)
    unfold mixedZ mixedZ'
    rw [ZeroConfig.W, ZeroConfig.W, hZ.tsum_eq, hZ'.tsum_eq]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    push_cast at hm
    have key := mixed_symbol_eq (acoshOf_props q0).2.2 (acoshOf_props q1).2.2
      (acoshOf_props q2).2.2 (acoshOf_props q3).2.2 m hm
    push_cast
    linear_combination ((L : ℂ) / 6 * EF.weilTest f f (m * (L / 6))) * key

/-! ### On-line columns -/

theorem verticalLatticePoint_ne {L : ℝ} (hL : 0 < L) {s s' : ℝ} {k k' : ℤ} (h : k ≠ k') :
    verticalLatticePoint L s k ≠ verticalLatticePoint L s' k' := by
  intro he
  have hi := congrArg Complex.im he
  simp only [verticalLatticePoint] at hi
  exact h (by exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π / L) ≠ 0) hi)

/-- The on-line column `½ + i(6j + r)(2π/L)`, `j ∈ ℤ`, of multiplicity `n`. -/
def lineColumn {L : ℝ} (hL : 0 < L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n) : ZeroConfig where
  carrier := Set.range fun j : ℤ => verticalLatticePoint L 0 (6 * j + r)
  mult := fun _ => n
  one_le_mult := fun _ _ => hn
  strip := by
    rintro _ ⟨j, rfl⟩
    simp only [verticalLatticePoint]
    norm_num
  reflect_mem := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j, by rw [reflect_verticalLatticePoint, neg_zero]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := fun T₁ T₂ =>
    ((onLineLatticeConfig hL).finite_window T₁ T₂).subset (by
      rintro _ ⟨⟨j, rfl⟩, h⟩
      exact ⟨⟨_, rfl⟩, h⟩)

theorem temperedConfig_lineColumn {L : ℝ} (hL : 0 < L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    TemperedConfig (lineColumn hL r n hn) := by
  have hsub : (lineColumn hL r n hn).carrier ⊆ (onLineLatticeConfig hL).carrier := by
    rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩
  let ι : (lineColumn hL r n hn).carrier → (onLineLatticeConfig hL).carrier :=
    fun ρ => ⟨ρ.1, hsub ρ.2⟩
  have hinj : Function.Injective ι := fun _ _ h =>
    Subtype.ext (by simpa [ι] using congrArg Subtype.val h)
  have hsum := ((temperedConfig_onLineLatticeConfig hL).comp_injective hinj).mul_left
    ((n : ℝ) / 2)
  refine hsum.congr fun ρ => ?_
  simp only [ι, lineColumn, onLineLatticeConfig, Function.comp_apply]
  push_cast
  ring

/-- **The image series of an on-line column.** -/
theorem hasSum_Wsummand_lineColumn {L : ℝ} (hL : 0 < L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {A : ℝ} (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) :
    HasSum (fun ρ : (lineColumn hL r n hn).carrier => (lineColumn hL r n hn).Wsummand f f ρ)
      ((n : ℂ) * lagSum (L / 6) ((r : ℝ) * (2 * π / L)) 0 (EF.weilTest f f)) := by
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hK := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs := weilTest_abs_le hfs hfs
  have hℓ : 0 < L / 6 := by positivity
  have hinj : Function.Injective fun j : ℤ => verticalLatticePoint L 0 (6 * j + r) :=
    fun j j' h => by
      have := verticalLatticePoint_injective hL 0 h
      omega
  have hlin : HasSum (fun ρ : Set.range (fun j : ℤ => verticalLatticePoint L 0 (6 * j + r)) =>
      (lineColumn hL r n hn).Wsummand f f ρ)
      ((n : ℂ) * lagSum (L / 6) ((r : ℝ) * (2 * π / L)) 0 (EF.weilTest f f)) := by
    rw [hinj.hasSum_range_iff]
    refine ((hasSum_paperFT_translate hℓ hK hKs _ 0).mul_left (n : ℂ)).congr_fun fun j => ?_
    have e : (((6 * j + r : ℤ) : ℝ) * (2 * π / L)) =
        (r : ℝ) * (2 * π / L) + j * (2 * π / (L / 6)) := by
      push_cast
      field_simp
      ring
    simp only [Function.comp_apply]
    unfold ZeroConfig.Wsummand
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, gammaOf_verticalLatticePoint, e]
    simp only [lineColumn]
    ring
  exact hlin

theorem lagSum_line_eq {L : ℝ} (hL : 0 < L) (r : ℤ) {K : ℝ → ℂ} {A : ℝ} (N : ℕ)
    (hK : ∀ u, K u ≠ 0 → |u| ≤ A) (hA : A < (N + 1) * (L / 6)) :
    lagSum (L / 6) ((r : ℝ) * (2 * π / L)) 0 K =
      ((L / 6 : ℝ) : ℂ) * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, K (m * (L / 6)) * (colSym r 0 m / 2) := by
  have hzero := kernel_lag_eq_zero hL N hK hA
  unfold lagSum
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) fun m hm => by
    rw [hzero m hm, zero_mul, zero_mul]]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e1 : cexp (I * (((r : ℝ) * (2 * π / L) : ℝ) : ℂ) * ((m : ℂ) * ((L / 6 : ℝ) : ℂ))) =
      cexp (I * ((((r * m : ℤ) : ℝ) * π / 3 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    field_simp
    ring
  simp only [colSym, zero_mul, Real.exp_zero, Real.cosh_zero]
  rw [e1]
  push_cast
  ring

theorem lineColumn_mem {L : ℝ} (hL : 0 < L) (r : ℤ) {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ}
    (hρ : ρ ∈ (lineColumn hL r n hn).carrier) :
    ∃ j : ℤ, ρ.im = ((6 * j + r : ℤ) : ℝ) * (2 * π / L) ∧ |ρ.re - 1 / 2| = 0 := by
  obtain ⟨j, rfl⟩ := hρ
  exact ⟨j, rfl, by simp [verticalLatticePoint]⟩

/-! ### Hiding up to `5π/(6g)` -/

theorem mixed4_symbol_real {x1 x2 x3 : ℝ} (h1 : Real.cosh x1 = 11381 / 3358)
    (h2 : Real.cosh x2 = 2131 / 73) (h3 : Real.cosh x3 = 30292 / 1679) (m : ℤ)
    (hm : -4 ≤ m ∧ m ≤ 4) :
    155314585150 * (2 * Real.cos (((1 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x1 * m))) +
        1311418449 * (2 * Real.cos (((2 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x2 * m))) +
        9183040076 * (Real.cos (((3 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x3 * m))) =
      644870094548 := by
  rw [cos_int_mul_pi_div_three, cos_int_mul_pi_div_three, cos_int_mul_pi_div_three,
    cosh_mul_int_eq h1 m ⟨by omega, by omega⟩, cosh_mul_int_eq h2 m ⟨by omega, by omega⟩,
    cosh_mul_int_eq h3 m ⟨by omega, by omega⟩]
  obtain ⟨hm1, hm2⟩ := hm
  interval_cases m <;> norm_num [cosTable]

/-- **The symbol of `Z₄` is constant up to `|m| ≤ 4`**, equal to that of the on-line column. -/
theorem mixed4_symbol_eq {x1 x2 x3 : ℝ} (h1 : Real.cosh x1 = 11381 / 3358)
    (h2 : Real.cosh x2 = 2131 / 73) (h3 : Real.cosh x3 = 30292 / 1679) (m : ℤ)
    (hm : -4 ≤ m ∧ m ≤ 4) :
    155314585150 * colSym 1 x1 m + 155314585150 * colSym (-1) x1 m +
        1311418449 * colSym 2 x2 m + 1311418449 * colSym (-2) x2 m +
        9183040076 * colSym 3 x3 m = 644870094548 * (colSym 0 0 m / 2) := by
  have hrC := congrArg (fun t : ℝ => (t : ℂ)) (mixed4_symbol_real h1 h2 h3 m hm)
  have p1 := colSym_pair 1 x1 m
  have p2 := colSym_pair 2 x2 m
  have z3 := colSym_three x3 m
  have z0 : colSym 0 0 m = 2 := by simp [colSym]
  push_cast at hrC p1 p2 z3
  rw [z0]
  linear_combination 155314585150 * p1 + 1311418449 * p2 + 9183040076 * z3 + hrC

/-- The on-line column of residue `r` and multiplicity `n`. -/
def mixedLine {L : ℝ} (hL : 734 ≤ L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n) : ZeroConfig :=
  lineColumn (L := L) (by linarith) r n hn

theorem hasSum_mixedLine {L : ℝ} (hL : 734 ≤ L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n) (N : ℕ) {a : ℝ}
    (ha : 2 * a < (N + 1) * (L / 6)) {f : ℝ → ℂ} (hf : ApertureWindow a f) :
    HasSum (fun ρ : (mixedLine hL r n hn).carrier => (mixedLine hL r n hn).Wsummand f f ρ)
      ((n : ℂ) * (((L / 6 : ℝ) : ℂ) * ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        EF.weilTest f f (m * (L / 6)) * (colSym r 0 m / 2))) := by
  have hL0 : 0 < L := by linarith
  have hfs : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rw [show 2 * a / 2 = a by ring]; exact hf.2
  have h := hasSum_Wsummand_lineColumn hL0 r n hn hf.1 hfs
  rw [lagSum_line_eq hL0 r N (weilTest_abs_le hfs hfs) ha] at h
  unfold mixedLine
  exact h

theorem disjoint_mixedColumn_mixedLine {L : ℝ} (hL : 734 ≤ L) {r r' : ℤ} {P : ℝ} (hP : 1 < P)
    (hP' : P ≤ 367 / 6) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : ∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + r') :
    Disjoint (mixedColumn hL r hP hP' n hn).carrier (mixedLine hL r' n' hn').carrier := by
  unfold mixedColumn mixedLine
  rw [Set.disjoint_left]
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩) ⟨j', hj'⟩ <;>
    exact verticalLatticePoint_ne (L := L) (by linarith) (h j j').symm hj'

theorem temperedConfig_mixedLine {L : ℝ} (hL : 734 ≤ L) (r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    TemperedConfig (mixedLine hL r n hn) := by
  unfold mixedLine
  exact temperedConfig_lineColumn _ _ _ _

theorem mixedLine_mem {L : ℝ} (hL : 734 ≤ L) (r : ℤ) {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ}
    (hρ : ρ ∈ (mixedLine hL r n hn).carrier) :
    ∃ j : ℤ, ρ.im = ((6 * j + r : ℤ) : ℝ) * (2 * π / L) ∧ |ρ.re - 1 / 2| = 0 := by
  unfold mixedLine at hρ
  exact lineColumn_mem _ _ _ hρ

/-- `Z₄`: off-line columns at residues `±1, ±2, 3` with depth cosines `11381/3358, 2131/73,
30292/1679` and multiplicities `155314585150, 1311418449, 9183040076`. -/
def mixedZ4 {L : ℝ} (hL : 734 ≤ L) : ZeroConfig :=
  superpose (superpose (superpose (superpose
    (mixedColumn hL 1 (P := 11381 / 3358) (by norm_num) (by norm_num) 155314585150 (by norm_num))
    (mixedColumn hL (-1) (P := 11381 / 3358) (by norm_num) (by norm_num) 155314585150
      (by norm_num)))
    (mixedColumn hL 2 (P := 2131 / 73) (by norm_num) (by norm_num) 1311418449 (by norm_num)))
    (mixedColumn hL (-2) (P := 2131 / 73) (by norm_num) (by norm_num) 1311418449 (by norm_num)))
    (mixedColumn hL 3 (P := 30292 / 1679) (by norm_num) (by norm_num) 9183040076 (by norm_num))

/-- `Z₄'`: the on-line column at residue `0` with multiplicity `644870094548`. -/
def mixedZ4' {L : ℝ} (hL : 734 ≤ L) : ZeroConfig := mixedLine hL 0 644870094548 (by norm_num)

/-- **Mixed depths hide up to `5π/(6g)`.** For `L ≥ 734`, `Z₄ = mixedZ4` and `Z₄' = mixedZ4'` are
tempered, disjoint and nonempty; their union is separated at `g = 2π/L` apart from FE partners; and
they are mimics at every aperture `a < 5L/12 = 5π/(6g)`. A window of aperture `a < 5ℓ/2` sees the
lags `|m| ≤ 4`, where the symbol of `Z₄` is the constant `644870094548` (`mixed4_symbol_eq`). -/
theorem mixedDepth_mimics_to_five_sixths {L : ℝ} (hL : 734 ≤ L) :
    TemperedConfig (mixedZ4 hL) ∧ TemperedConfig (mixedZ4' hL) ∧ (mixedZ4 hL).carrier.Nonempty ∧
      Disjoint (mixedZ4 hL).carrier (mixedZ4' hL).carrier ∧
      (∀ ρ ∈ (mixedZ4 hL).carrier ∪ (mixedZ4' hL).carrier,
        ∀ ρ' ∈ (mixedZ4 hL).carrier ∪ (mixedZ4' hL).carrier, ρ' ≠ ρ → ρ' ≠ reflect ρ →
          2 * π / L ≤ |ρ.im - ρ'.im|) ∧
      ∀ a < 5 * L / 12, ∀ f, ApertureWindow a f → (mixedZ4 hL).W f f = (mixedZ4' hL).W f f := by
  have hL0 : 0 < L := by linarith
  have q1 : (1 : ℝ) < 11381 / 3358 := by norm_num
  have q1' : (11381 / 3358 : ℝ) ≤ 367 / 6 := by norm_num
  have q2 : (1 : ℝ) < 2131 / 73 := by norm_num
  have q2' : (2131 / 73 : ℝ) ≤ 367 / 6 := by norm_num
  have q3 : (1 : ℝ) < 30292 / 1679 := by norm_num
  have q3' : (30292 / 1679 : ℝ) ≤ 367 / 6 := by norm_num
  have nb : 1 ≤ 155314585150 := by norm_num
  have nc : 1 ≤ 1311418449 := by norm_num
  have nd : 1 ≤ 9183040076 := by norm_num
  have n0 : 1 ≤ 644870094548 := by norm_num
  have d1m1 := disjoint_mixedColumn hL (r := 1) (r' := -1) q1 q1' q1 q1' nb nb
    (by intro j j'; omega)
  have d12 := disjoint_mixedColumn hL (r := 1) (r' := 2) q1 q1' q2 q2' nb nc (by intro j j'; omega)
  have dm12 := disjoint_mixedColumn hL (r := -1) (r' := 2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have d1m2 := disjoint_mixedColumn hL (r := 1) (r' := -2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have dm1m2 := disjoint_mixedColumn hL (r := -1) (r' := -2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have d2m2 := disjoint_mixedColumn hL (r := 2) (r' := -2) q2 q2' q2 q2' nc nc
    (by intro j j'; omega)
  have d13 := disjoint_mixedColumn hL (r := 1) (r' := 3) q1 q1' q3 q3' nb nd (by intro j j'; omega)
  have dm13 := disjoint_mixedColumn hL (r := -1) (r' := 3) q1 q1' q3 q3' nb nd
    (by intro j j'; omega)
  have d23 := disjoint_mixedColumn hL (r := 2) (r' := 3) q2 q2' q3 q3' nc nd (by intro j j'; omega)
  have dm23 := disjoint_mixedColumn hL (r := -2) (r' := 3) q2 q2' q3 q3' nc nd
    (by intro j j'; omega)
  have dA : Disjoint (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)).carrier
      (mixedColumn hL 2 q2 q2' 1311418449 nc).carrier :=
    Set.disjoint_union_left.mpr ⟨d12, dm12⟩
  have dB : Disjoint (superpose (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)) (mixedColumn hL 2 q2 q2' 1311418449 nc)).carrier
      (mixedColumn hL (-2) q2 q2' 1311418449 nc).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d1m2, dm1m2⟩, d2m2⟩
  have dC : Disjoint (superpose (superpose (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)) (mixedColumn hL 2 q2 q2' 1311418449 nc))
      (mixedColumn hL (-2) q2 q2' 1311418449 nc)).carrier
      (mixedColumn hL 3 q3 q3' 9183040076 nd).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨d13, dm13⟩, d23⟩, dm23⟩
  have dl : ∀ {r : ℤ} {P : ℝ} (hP : 1 < P) (hP' : P ≤ 367 / 6) {n : ℕ} (hn : 1 ≤ n),
      (∀ j j' : ℤ, 6 * j + r ≠ 6 * j' + 0) →
      Disjoint (mixedColumn hL r hP hP' n hn).carrier (mixedZ4' hL).carrier := by
    intro r P hP hP' n hn h
    exact disjoint_mixedColumn_mixedLine hL hP hP' hn n0 h
  have dZZ : Disjoint (mixedZ4 hL).carrier (mixedZ4' hL).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨dl q1 q1' nb (by intro j j'; omega),
        dl q1 q1' nb (by intro j j'; omega)⟩, dl q2 q2' nc (by intro j j'; omega)⟩,
      dl q2 q2' nc (by intro j j'; omega)⟩, dl q3 q3' nd (by intro j j'; omega)⟩
  refine ⟨?_, ?_, ?_, dZZ, ?_, ?_⟩
  · exact temperedConfig_superpose dC (temperedConfig_superpose dB
      (temperedConfig_superpose dA (temperedConfig_superpose d1m1 (temperedConfig_mixedColumn ..)
        (temperedConfig_mixedColumn ..)) (temperedConfig_mixedColumn ..))
      (temperedConfig_mixedColumn ..)) (temperedConfig_mixedColumn ..)
  · exact temperedConfig_mixedLine ..
  · exact ⟨_, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨0, rfl⟩))))⟩
  · set δ := fun P : ℝ => 6 * acoshOf P / L with hδ
    refine separated_of_depthFun hL0 (fun k => if k % 6 = 0 then 0 else
      if k % 6 = 3 then δ (30292 / 1679) else if k % 6 = 1 ∨ k % 6 = 5 then δ (11381 / 3358)
      else δ (2131 / 73)) ?_
    intro ρ hρ
    rcases hρ with ((((h | h) | h) | h) | h) | h
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 1 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 1) % 6 = 1 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL (-1) _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + -1) % 6 = 5 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 2 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 2) % 6 = 2 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL (-2) _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + -2) % 6 = 4 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedColumn_mem hL 3 _ _ _ h
      exact ⟨_, hj, by rw [hd]; simp [hδ, show (6 * j + 3) % 6 = 3 by omega]⟩
    · obtain ⟨j, hj, hd⟩ := mixedLine_mem hL 0 _ h
      exact ⟨_, hj, by rw [hd]; simp⟩
  · intro a ha f hf
    have ha4 : 2 * a < ((4 : ℕ) + 1) * (L / 6) := by push_cast; linarith
    have hZ := hasSum_Wsummand_superpose dC (hasSum_Wsummand_superpose dB
      (hasSum_Wsummand_superpose dA (hasSum_Wsummand_superpose d1m1
        (hasSum_mixedColumn hL 1 q1 q1' 155314585150 nb 4 ha4 hf)
        (hasSum_mixedColumn hL (-1) q1 q1' 155314585150 nb 4 ha4 hf))
        (hasSum_mixedColumn hL 2 q2 q2' 1311418449 nc 4 ha4 hf))
        (hasSum_mixedColumn hL (-2) q2 q2' 1311418449 nc 4 ha4 hf))
      (hasSum_mixedColumn hL 3 q3 q3' 9183040076 nd 4 ha4 hf)
    have hZ' := hasSum_mixedLine hL 0 644870094548 n0 4 ha4 hf
    unfold mixedZ4 mixedZ4'
    rw [ZeroConfig.W, ZeroConfig.W, hZ.tsum_eq, hZ'.tsum_eq]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    push_cast at hm
    have key := mixed4_symbol_eq (acoshOf_props q1).2.2 (acoshOf_props q2).2.2
      (acoshOf_props q3).2.2 m hm
    push_cast
    linear_combination ((L : ℂ) / 6 * EF.weilTest f f (m * (L / 6))) * key

/-! ### The five-sixths pair is sharp -/

/-- The symbol of `Z₄`. -/
def phiZ4 (m : ℤ) : ℂ :=
  155314585150 * colSym 1 (acoshOf (11381 / 3358)) m +
    155314585150 * colSym (-1) (acoshOf (11381 / 3358)) m +
    1311418449 * colSym 2 (acoshOf (2131 / 73)) m + 1311418449 * colSym (-2) (acoshOf (2131 / 73)) m +
    9183040076 * colSym 3 (acoshOf (30292 / 1679)) m

/-- The symbol of `Z₄'`. -/
def phiZ4' (m : ℤ) : ℂ := 644870094548 * (colSym 0 0 m / 2)

/-- The image difference of `Z₄` and `Z₄'` on a window whose kernel lives in `|u| < (N + 1)ℓ`. -/
theorem mixedZ4_W_sub {L : ℝ} (hL : 734 ≤ L) (N : ℕ) {a : ℝ} (ha : 2 * a < (N + 1) * (L / 6))
    {f : ℝ → ℂ} (hf : ApertureWindow a f) :
    (mixedZ4 hL).W f f - (mixedZ4' hL).W f f = ((L / 6 : ℝ) : ℂ) *
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, EF.weilTest f f (m * (L / 6)) * (phiZ4 m - phiZ4' m) := by
  have q1 : (1 : ℝ) < 11381 / 3358 := by norm_num
  have q1' : (11381 / 3358 : ℝ) ≤ 367 / 6 := by norm_num
  have q2 : (1 : ℝ) < 2131 / 73 := by norm_num
  have q2' : (2131 / 73 : ℝ) ≤ 367 / 6 := by norm_num
  have q3 : (1 : ℝ) < 30292 / 1679 := by norm_num
  have q3' : (30292 / 1679 : ℝ) ≤ 367 / 6 := by norm_num
  have nb : 1 ≤ 155314585150 := by norm_num
  have nc : 1 ≤ 1311418449 := by norm_num
  have nd : 1 ≤ 9183040076 := by norm_num
  have n0 : 1 ≤ 644870094548 := by norm_num
  have d1m1 := disjoint_mixedColumn hL (r := 1) (r' := -1) q1 q1' q1 q1' nb nb
    (by intro j j'; omega)
  have d12 := disjoint_mixedColumn hL (r := 1) (r' := 2) q1 q1' q2 q2' nb nc (by intro j j'; omega)
  have dm12 := disjoint_mixedColumn hL (r := -1) (r' := 2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have d1m2 := disjoint_mixedColumn hL (r := 1) (r' := -2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have dm1m2 := disjoint_mixedColumn hL (r := -1) (r' := -2) q1 q1' q2 q2' nb nc
    (by intro j j'; omega)
  have d2m2 := disjoint_mixedColumn hL (r := 2) (r' := -2) q2 q2' q2 q2' nc nc
    (by intro j j'; omega)
  have d13 := disjoint_mixedColumn hL (r := 1) (r' := 3) q1 q1' q3 q3' nb nd (by intro j j'; omega)
  have dm13 := disjoint_mixedColumn hL (r := -1) (r' := 3) q1 q1' q3 q3' nb nd
    (by intro j j'; omega)
  have d23 := disjoint_mixedColumn hL (r := 2) (r' := 3) q2 q2' q3 q3' nc nd (by intro j j'; omega)
  have dm23 := disjoint_mixedColumn hL (r := -2) (r' := 3) q2 q2' q3 q3' nc nd
    (by intro j j'; omega)
  have dA : Disjoint (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)).carrier
      (mixedColumn hL 2 q2 q2' 1311418449 nc).carrier :=
    Set.disjoint_union_left.mpr ⟨d12, dm12⟩
  have dB : Disjoint (superpose (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)) (mixedColumn hL 2 q2 q2' 1311418449 nc)).carrier
      (mixedColumn hL (-2) q2 q2' 1311418449 nc).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d1m2, dm1m2⟩, d2m2⟩
  have dC : Disjoint (superpose (superpose (superpose (mixedColumn hL 1 q1 q1' 155314585150 nb)
      (mixedColumn hL (-1) q1 q1' 155314585150 nb)) (mixedColumn hL 2 q2 q2' 1311418449 nc))
      (mixedColumn hL (-2) q2 q2' 1311418449 nc)).carrier
      (mixedColumn hL 3 q3 q3' 9183040076 nd).carrier :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨d13, dm13⟩, d23⟩, dm23⟩
  have hZ := hasSum_Wsummand_superpose dC (hasSum_Wsummand_superpose dB
    (hasSum_Wsummand_superpose dA (hasSum_Wsummand_superpose d1m1
      (hasSum_mixedColumn hL 1 q1 q1' 155314585150 nb N ha hf)
      (hasSum_mixedColumn hL (-1) q1 q1' 155314585150 nb N ha hf))
      (hasSum_mixedColumn hL 2 q2 q2' 1311418449 nc N ha hf))
      (hasSum_mixedColumn hL (-2) q2 q2' 1311418449 nc N ha hf))
    (hasSum_mixedColumn hL 3 q3 q3' 9183040076 nd N ha hf)
  have hZ' := hasSum_mixedLine hL 0 644870094548 n0 N ha hf
  unfold mixedZ4 mixedZ4'
  rw [ZeroConfig.W, ZeroConfig.W, hZ.tsum_eq, hZ'.tsum_eq]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [phiZ4, phiZ4']
  push_cast
  ring

theorem mixed4_symbol_real_five {x1 x2 x3 : ℝ} (h1 : Real.cosh x1 = 11381 / 3358)
    (h2 : Real.cosh x2 = 2131 / 73) (h3 : Real.cosh x3 = 30292 / 1679) (m : ℤ)
    (hm : m = 5 ∨ m = -5) :
    155314585150 * (2 * Real.cos (((1 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x1 * m))) +
        1311418449 * (2 * Real.cos (((2 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x2 * m))) +
        9183040076 * (Real.cos (((3 * m : ℤ) : ℝ) * π / 3) * (2 * Real.cosh (x3 * m))) =
      644870094548 - 36469449013318963017129111481200 / 25223062072031 := by
  have hm' : -5 ≤ m ∧ m ≤ 5 := by rcases hm with rfl | rfl <;> norm_num
  rw [cos_int_mul_pi_div_three, cos_int_mul_pi_div_three, cos_int_mul_pi_div_three,
    cosh_mul_int_eq h1 m hm', cosh_mul_int_eq h2 m hm', cosh_mul_int_eq h3 m hm']
  rcases hm with rfl | rfl <;> norm_num [cosTable]

/-- **The symbols differ at the sixth lags.** -/
theorem phiZ4_sub_five (m : ℤ) (hm : m = 5 ∨ m = -5) :
    phiZ4 m - phiZ4' m = -((36469449013318963017129111481200 / 25223062072031 : ℝ) : ℂ) := by
  have h1 := (acoshOf_props (P := 11381 / 3358) (by norm_num)).2.2
  have h2 := (acoshOf_props (P := 2131 / 73) (by norm_num)).2.2
  have h3 := (acoshOf_props (P := 30292 / 1679) (by norm_num)).2.2
  have hrC := congrArg (fun t : ℝ => (t : ℂ)) (mixed4_symbol_real_five h1 h2 h3 m hm)
  have p1 := colSym_pair 1 (acoshOf (11381 / 3358)) m
  have p2 := colSym_pair 2 (acoshOf (2131 / 73)) m
  have z3 := colSym_three (acoshOf (30292 / 1679)) m
  have z0 : colSym 0 0 m = 2 := by simp [colSym]
  push_cast at hrC p1 p2 z3
  simp only [phiZ4, phiZ4']
  rw [z0]
  push_cast
  linear_combination 155314585150 * p1 + 1311418449 * p2 + 9183040076 * z3 + hrC

theorem phiZ4_sub_eq_zero (m : ℤ) (hm : -4 ≤ m ∧ m ≤ 4) : phiZ4 m - phiZ4' m = 0 := by
  rw [sub_eq_zero, phiZ4, phiZ4']
  exact mixed4_symbol_eq (acoshOf_props (by norm_num)).2.2 (acoshOf_props (by norm_num)).2.2
    (acoshOf_props (by norm_num)).2.2 m hm

/-- **The five-sixths pair is sharp.** At every aperture `a > 5L/12 = 5π/(6g)` some window of
aperture `a` separates `Z₄` from `Z₄'`: the two-bump test at lag `5ℓ` reads the symbol difference
at `m = ±5`, which is nonzero. -/
theorem mixedDepth_five_sixths_sharp {L : ℝ} (hL : 734 ≤ L) {a : ℝ} (ha : 5 * L / 12 < a) :
    ∃ f, ApertureWindow a f ∧ (mixedZ4 hL).W f f ≠ (mixedZ4' hL).W f f := by
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 < L / 6 := by positivity
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℝ, w₀ = min ((a - 5 * (L / 6) / 2) / 2) (L / 6 / 8) := ⟨_, rfl⟩
  have hw0 : 0 < w₀ := by rw [hw₀]; exact lt_min (by linarith) (by positivity)
  have hw1 : w₀ ≤ (a - 5 * (L / 6) / 2) / 2 := hw₀ ▸ min_le_left _ _
  have hw2 : w₀ ≤ L / 6 / 8 := hw₀ ▸ min_le_right _ _
  set b := modScaledBump w₀ 0 with hb
  have hbs := modScaledBump_support hw0 0
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  have hsupp : tsupport (twoBump b (5 * (L / 6)) (-1)) ⊆
      Icc (-(5 * (L / 6) / 2 + w₀)) (5 * (L / 6) / 2 + w₀) :=
    tsupport_twoBump_modScaledBump_subset hw0 (by positivity)
  have hfd : ContDiff ℝ 2 (twoBump b (5 * (L / 6)) (-1)) :=
    contDiff_bumpTest (contDiff_modScaledBump_two w₀ 0) _ _
  have hf' : ApertureWindow (5 * (L / 6) / 2 + w₀) (twoBump b (5 * (L / 6)) (-1)) := ⟨hfd, hsupp⟩
  refine ⟨twoBump b (5 * (L / 6)) (-1),
    ⟨hfd, hsupp.trans (Icc_subset_Icc (by linarith) (by linarith))⟩, ?_⟩
  rw [← sub_ne_zero, mixedZ4_W_sub hL 5 (a := 5 * (L / 6) / 2 + w₀) (by push_cast; linarith) hf']
  -- only the lags `m = ±5` survive
  have hK : ∀ y : ℝ, EF.weilTest (twoBump b (5 * (L / 6)) (-1)) (twoBump b (5 * (L / 6)) (-1)) y =
      2 * EF.weilTest b b y - EF.weilTest b b (y + 5 * (L / 6)) -
        EF.weilTest b b (y - 5 * (L / 6)) :=
    weilTest_twoBump_neg_one (contDiff_modScaledBump_two w₀ 0).continuous hbc _
  have hK0 : ∀ y : ℝ, 2 * w₀ < |y| → EF.weilTest b b y = 0 := fun y hy =>
    weilTest_self_eq_zero_of_lt hbs hy
  have hlag : ∀ j : ℤ, j ≠ 0 → 2 * w₀ < |(j : ℝ) * (L / 6)| := fun j hj => by
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    rw [abs_mul, abs_of_pos hℓ0]
    nlinarith
  have hfive : ∀ m : ℤ, (m = 5 ∨ m = -5) →
      EF.weilTest (twoBump b (5 * (L / 6)) (-1)) (twoBump b (5 * (L / 6)) (-1)) (m * (L / 6)) =
        -EF.weilTest b b 0 := by
    intro m hm
    rw [hK]
    rcases hm with rfl | rfl
    · have e1 : EF.weilTest b b (((5 : ℤ) : ℝ) * (L / 6)) = 0 := hK0 _ (hlag 5 (by norm_num))
      have e2 : EF.weilTest b b (((5 : ℤ) : ℝ) * (L / 6) + 5 * (L / 6)) = 0 := by
        rw [show ((5 : ℤ) : ℝ) * (L / 6) + 5 * (L / 6) = ((10 : ℤ) : ℝ) * (L / 6) by
          push_cast; ring]
        exact hK0 _ (hlag 10 (by norm_num))
      rw [e1, e2, show ((5 : ℤ) : ℝ) * (L / 6) - 5 * (L / 6) = 0 by push_cast; ring]
      ring
    · have e1 : EF.weilTest b b (((-5 : ℤ) : ℝ) * (L / 6)) = 0 := hK0 _ (hlag (-5) (by norm_num))
      have e3 : EF.weilTest b b (((-5 : ℤ) : ℝ) * (L / 6) - 5 * (L / 6)) = 0 := by
        rw [show ((-5 : ℤ) : ℝ) * (L / 6) - 5 * (L / 6) = ((-10 : ℤ) : ℝ) * (L / 6) by
          push_cast; ring]
        exact hK0 _ (hlag (-10) (by norm_num))
      rw [e1, e3, show ((-5 : ℤ) : ℝ) * (L / 6) + 5 * (L / 6) = 0 by push_cast; ring]
      ring
  rw [Finset.sum_eq_add (a := 5) (b := -5) (by norm_num)]
  · rw [hfive 5 (Or.inl rfl), hfive (-5) (Or.inr rfl), phiZ4_sub_five 5 (Or.inl rfl),
      phiZ4_sub_five (-5) (Or.inr rfl), SquareRootThreshold.weilTest_self_zero]
    have hpos := integral_norm_sq_modScaledBump_pos hw0
    have hδ : (36469449013318963017129111481200 / 25223062072031 : ℝ) ≠ 0 := by norm_num
    have hval : ((L / 6 : ℝ) : ℂ) * (-((∫ t, ‖b t‖ ^ 2 : ℝ) : ℂ) *
        -((36469449013318963017129111481200 / 25223062072031 : ℝ) : ℂ) +
        -((∫ t, ‖b t‖ ^ 2 : ℝ) : ℂ) *
          -((36469449013318963017129111481200 / 25223062072031 : ℝ) : ℂ)) =
        (((L / 6) * (2 * (∫ t, ‖b t‖ ^ 2) *
          (36469449013318963017129111481200 / 25223062072031)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hval, Complex.ofReal_ne_zero]
    positivity
  · intro m hm hne
    rw [Finset.mem_Icc] at hm
    push_cast at hm
    rw [phiZ4_sub_eq_zero m ⟨by omega, by omega⟩, mul_zero]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) h
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) h

/-- **The Ingham scale does not resolve mixed depths.** Tempered mimics whose union is separated at
`g` apart from FE partners need not coincide at apertures above `π/(2g)`. -/
theorem not_eq_of_mimic_at_ingham_scale :
    ¬ ∀ (Z Z' : ZeroConfig) (g a : ℝ), TemperedConfig Z → TemperedConfig Z' → 0 < g →
      π / (2 * g) < a →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ → ρ' ≠ reflect ρ →
        g ≤ |ρ.im - ρ'.im|) →
      (∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) → Z.carrier = Z'.carrier := by
  intro h
  obtain ⟨hT, hT', ⟨ρ, hρ⟩, hd, hsep, hW⟩ := mixedDepth_mimics_beyond_ingham (L := 734) le_rfl
  have hg : (0 : ℝ) < 2 * π / 734 := by positivity
  have ha : π / (2 * (2 * π / 734)) < 7 * 734 / 24 := by
    rw [show π / (2 * (2 * π / 734)) = 734 / 4 by field_simp; ring]
    norm_num
  have heq := h _ _ _ _ hT hT' hg ha hsep (hW _ (by norm_num))
  exact Set.disjoint_left.mp hd hρ (heq ▸ hρ)

/-- **Separated configurations are not resolved below `5π/(6g)`.** For every `c < 5/6` there are
tempered mimics at an aperture above `cπ/g`, separated at `g` apart from FE partners, that differ. -/
theorem not_eq_of_mimic_below_five_sixths {c : ℝ} (hc : c < 5 / 6) :
    ¬ ∀ (Z Z' : ZeroConfig) (g a : ℝ), TemperedConfig Z → TemperedConfig Z' → 0 < g →
      c * π / g < a →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ → ρ' ≠ reflect ρ →
        g ≤ |ρ.im - ρ'.im|) →
      (∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) → Z.carrier = Z'.carrier := by
  intro h
  obtain ⟨hT, hT', ⟨ρ, hρ⟩, hd, hsep, hW⟩ := mixedDepth_mimics_to_five_sixths (L := 734) le_rfl
  have hg : (0 : ℝ) < 2 * π / 734 := by positivity
  have ha : c * π / (2 * π / 734) < (c * 734 / 2 + 5 * 734 / 12) / 2 := by
    rw [show c * π / (2 * π / 734) = c * 734 / 2 by field_simp]
    linarith
  have heq := h _ _ _ _ hT hT' hg ha hsep (hW _ (by linarith))
  exact Set.disjoint_left.mp hd hρ (heq ▸ hρ)

end GaloisForLFunctions.ZeroConfigurationGeometry
