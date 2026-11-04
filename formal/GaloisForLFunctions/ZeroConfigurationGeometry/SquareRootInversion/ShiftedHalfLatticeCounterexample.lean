import GaloisForLFunctions.ZeroConfigurationGeometry.SparseOnLineClustersNeverCancel

/-!
# Sharp Nyquist counterexample to two-configuration local inversion up to `λ = 1`

For `L > 0`, let `Z₀ = simpleHalfLatticeConfig hL` (`{½ + i k π / L : k ∈ ℤ}`, multiplicity `1`)
and let `Z₁ = shiftedSimpleHalfLatticeConfig hL` (`{½ + i (2k + 1) π / (2L) : k ∈ ℤ}`,
multiplicity `1`) be its half-period vertical shift. Their disjoint union is the doubled-density
simple lattice `simpleHalfLatticeConfig (2L)` (`{½ + i m π / (2L) : m ∈ ℤ}`).

* **Exact Weil mimicry up to `L`** (`W_shiftedSimpleHalfLatticeConfig`,
  `W_shiftedSimpleHalfLatticeConfig_eq_simpleHalfLatticeConfig`). Since `Z_{2L}` splits cleanly into
  its even indices (`Z₀`) and odd indices (`Z₁`), on every pair of `C²` windows supported in
  `[−L, L] ⊆ [−2L, 2L]` we have
  `W_{Z₁}(f, g) = W_{Z_{2L}}(f, g) − W_{Z₀}(f, g) = 4L⟨f, g⟩ − 2L⟨f, g⟩ = 2L⟨f, g⟩ = W_{Z₀}(f, g)`.
* **Exact local counts** (`abs_N_simpleHalfLatticeConfig_sub_le_one`,
  `abs_N_shiftedSimpleHalfLatticeConfig_sub_le_one`). On every interval `(x, y]` (`x ≤ y`), both
  configurations satisfy `|N(x, y) − (L/π)(y − x)| ≤ 1`.
* **Disjointness and separation at the square-root scale**
  (`exists_rvm_pair_mimic_disjoint_up_to_one`). Setting `L = ½ log(T/2π)` (`T ≥ 2π e^π`), for every
  `0 < λ ≤ 1` (in particular across the entire interval `½ < λ ≤ 1`), `Z₀` and `Z₁` are
  critical-line simple tempered configurations with Riemann–von Mangoldt local count error `≤ 1` and
  identical Weil images at aperture `λ · ½ log(T/2π)`, yet have disjoint carriers, nonempty support
  in `[T − 1, T + 1]`, and uniform minimum separation `π / log(T/2π)` across `Z₀ ∪ Z₁`.
-/

open MeasureTheory Complex Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The odd-index half-lattice point `½ + i (2k + 1) π / (2L) = ½ + i (k + ½) π / L`. -/
def shiftedHalfLatticePoint (L : ℝ) (k : ℤ) : ℂ :=
  _root_.RHTower.verticalLatticePoint (4 * L) 0 (2 * k + 1)

theorem shiftedHalfLatticePoint_re (L : ℝ) (k : ℤ) :
    (shiftedHalfLatticePoint L k).re = 1 / 2 := by
  simp [shiftedHalfLatticePoint, _root_.RHTower.verticalLatticePoint]

theorem shiftedHalfLatticePoint_im {L : ℝ} (hL : 0 < L) (k : ℤ) :
    (shiftedHalfLatticePoint L k).im = ((k : ℝ) + 1 / 2) * (π / L) := by
  simp only [shiftedHalfLatticePoint, _root_.RHTower.verticalLatticePoint]
  push_cast
  field_simp [hL.ne']
  ring

theorem shiftedHalfLatticePoint_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (shiftedHalfLatticePoint L) := by
  intro j k h
  have h4 : 0 < 4 * L := by positivity
  have hinj := _root_.RHTower.verticalLatticePoint_injective h4 0 h
  omega

theorem simpleHalfLatticePoint_eq_even {L : ℝ} (hL : 0 < L) (k : ℤ) :
    _root_.RHTower.verticalLatticePoint (2 * L) 0 k =
      _root_.RHTower.verticalLatticePoint (4 * L) 0 (2 * k) := by
  apply Complex.ext
  · simp [_root_.RHTower.verticalLatticePoint]
  · simp only [_root_.RHTower.verticalLatticePoint]
    push_cast
    field_simp [hL.ne']

/-- The simple critical-line half-shifted lattice `{½ + i(k + ½)π/L : k ∈ ℤ}`, multiplicity `1`. -/
def shiftedSimpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) : ZeroConfig where
  carrier := Set.range (shiftedHalfLatticePoint L)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ ⟨k, rfl⟩
    rw [shiftedHalfLatticePoint_re]
    norm_num
  reflect_mem := by
    rintro _ ⟨k, rfl⟩
    refine ⟨-(k + 1), ?_⟩
    rw [shiftedHalfLatticePoint, _root_.RHTower.reflect_verticalLatticePoint, neg_zero,
      shiftedHalfLatticePoint]
    congr 1
    omega
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    have h2L : 0 < 2 * L := by positivity
    refine ((simpleHalfLatticeConfig h2L).finite_window T₁ T₂).subset ?_
    rintro z ⟨⟨k, rfl⟩, h1, h2⟩
    refine ⟨⟨2 * k + 1, ?_⟩, h1, h2⟩
    rw [shiftedHalfLatticePoint]
    congr 1
    ring

theorem carrier_shifted_subset_double {L : ℝ} (hL : 0 < L) :
    (shiftedSimpleHalfLatticeConfig hL).carrier ⊆
      (simpleHalfLatticeConfig (mul_pos two_pos hL)).carrier := by
  rintro _ ⟨k, rfl⟩
  refine ⟨2 * k + 1, ?_⟩
  simp only [shiftedHalfLatticePoint]
  congr 1
  ring

theorem disjoint_simpleHalfLattice_shifted {L : ℝ} (hL : 0 < L) :
    Disjoint (simpleHalfLatticeConfig hL).carrier
      (shiftedSimpleHalfLatticeConfig hL).carrier := by
  rw [Set.disjoint_left]
  rintro z ⟨j, rfl⟩ ⟨k, hk⟩
  have h4 : 0 < 4 * L := by positivity
  rw [simpleHalfLatticePoint_eq_even hL j, shiftedHalfLatticePoint] at hk
  have hinj := _root_.RHTower.verticalLatticePoint_injective h4 0 hk
  omega

theorem carrier_double_eq_union {L : ℝ} (hL : 0 < L) :
    (simpleHalfLatticeConfig (mul_pos two_pos hL)).carrier =
      (simpleHalfLatticeConfig hL).carrier ∪ (shiftedSimpleHalfLatticeConfig hL).carrier := by
  ext z
  simp only [simpleHalfLatticeConfig, _root_.RHTower.onLineLatticeConfig,
    shiftedSimpleHalfLatticeConfig, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      refine ⟨k, ?_⟩
      rw [simpleHalfLatticePoint_eq_even hL k]
      congr 1 <;> ring
    · right
      refine ⟨k, ?_⟩
      rw [shiftedHalfLatticePoint]
      congr 1 <;> ring
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨2 * k, ?_⟩
      rw [simpleHalfLatticePoint_eq_even hL k]
      congr 1; ring
    · refine ⟨2 * k + 1, ?_⟩
      rw [shiftedHalfLatticePoint]
      congr 1; ring

theorem temperedConfig_shiftedSimpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) :
    TemperedConfig (shiftedSimpleHalfLatticeConfig hL) := by
  have h2L : 0 < 2 * L := mul_pos two_pos hL
  have hsub := carrier_shifted_subset_double hL
  let ι : (shiftedSimpleHalfLatticeConfig hL).carrier → (simpleHalfLatticeConfig h2L).carrier :=
    fun ρ => ⟨ρ.1, hsub ρ.2⟩
  have hinj : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hsum := (temperedConfig_simpleHalfLatticeConfig h2L).comp_injective hinj
  exact hsum.congr fun _ => rfl

/-- The signed difference `m_{Z_{2L}} − m_{Z_L}` is the multiplicity indicator of the odd-index
half-shifted lattice `Z_{L, shift}`. -/
theorem multDiff_double_sub_simpleHalfLattice {L : ℝ} (hL : 0 < L) (z : ℂ) :
    multDiff (simpleHalfLatticeConfig (mul_pos two_pos hL)) (simpleHalfLatticeConfig hL) z =
      (shiftedSimpleHalfLatticeConfig hL).carrier.indicator
        (fun w => ((shiftedSimpleHalfLatticeConfig hL).mult w : ℂ)) z := by
  have hunion := carrier_double_eq_union hL
  have hdisj := Set.disjoint_left.mp (disjoint_simpleHalfLattice_shifted hL)
  unfold multDiff
  by_cases hz0 : z ∈ (simpleHalfLatticeConfig hL).carrier
  · have hz2 : z ∈ (simpleHalfLatticeConfig (mul_pos two_pos hL)).carrier := by
      rw [hunion]; exact Or.inl hz0
    have hz1 : z ∉ (shiftedSimpleHalfLatticeConfig hL).carrier := hdisj hz0
    rw [Set.indicator_of_mem hz2, Set.indicator_of_mem hz0, Set.indicator_of_notMem hz1]
    simp [simpleHalfLatticeConfig]
  · by_cases hz1 : z ∈ (shiftedSimpleHalfLatticeConfig hL).carrier
    · have hz2 : z ∈ (simpleHalfLatticeConfig (mul_pos two_pos hL)).carrier := by
        rw [hunion]; exact Or.inr hz1
      rw [Set.indicator_of_mem hz2, Set.indicator_of_notMem hz0, Set.indicator_of_mem hz1]
      simp [simpleHalfLatticeConfig, shiftedSimpleHalfLatticeConfig]
    · have hz2 : z ∉ (simpleHalfLatticeConfig (mul_pos two_pos hL)).carrier := by
        rw [hunion]; rintro (h | h) <;> contradiction
      rw [Set.indicator_of_notMem hz2, Set.indicator_of_notMem hz0, Set.indicator_of_notMem hz1,
        sub_zero]

/-- **Weil form of the shifted half-lattice below Nyquist.** For `C²` windows supported in `[−L, L]`,
`Z₁` has the exact diagonal inner-product Weil form `2L ∫ f · conj g`. -/
theorem W_shiftedSimpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfs : tsupport f ⊆ Icc (-L) L) (hgs : tsupport g ⊆ Icc (-L) L) :
    (shiftedSimpleHalfLatticeConfig hL).W f g = 2 * L * ∫ t, f t * conj (g t) := by
  have h2L : 0 < 2 * L := mul_pos two_pos hL
  have hsub : Icc (-L) L ⊆ Icc (-(2 * L)) (2 * L) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hfc : HasCompactSupport f := CompactIccSpace.isCompact_Icc.of_isClosed_subset isClosed_tsupport hfs
  have hgc : HasCompactSupport g := CompactIccSpace.isCompact_Icc.of_isClosed_subset isClosed_tsupport hgs
  have hdiff := W_sub_W_eq_tsum (temperedConfig_simpleHalfLatticeConfig h2L)
    (temperedConfig_simpleHalfLatticeConfig hL) hf hfc hg hgc
  have hind : (∑' z, multDiff (simpleHalfLatticeConfig h2L) (simpleHalfLatticeConfig hL) z *
      pointImage f g z) = (shiftedSimpleHalfLatticeConfig hL).W f g := by
    rw [W_eq_tsum_indicator]
    refine tsum_congr fun z => ?_
    rw [multDiff_double_sub_simpleHalfLattice hL z]
    by_cases hz : z ∈ (shiftedSimpleHalfLatticeConfig hL).carrier
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  rw [← hind, ← hdiff, W_simpleHalfLatticeConfig h2L hf hg.continuous (hfs.trans hsub)
    (hgs.trans hsub), W_simpleHalfLatticeConfig hL hf hg.continuous hfs hgs]
  push_cast
  ring

theorem W_shiftedSimpleHalfLatticeConfig_eq_simpleHalfLatticeConfig {L a : ℝ} (hL : 0 < L)
    (ha : a ≤ L) {f g : ℝ → ℂ} (hf : ApertureWindow a f) (hg : ApertureWindow a g) :
    (shiftedSimpleHalfLatticeConfig hL).W f g = (simpleHalfLatticeConfig hL).W f g := by
  have hsub : Icc (-a) a ⊆ Icc (-L) L := Icc_subset_Icc (by linarith) ha
  rw [W_shiftedSimpleHalfLatticeConfig hL hf.1 hg.1 (hf.2.trans hsub) (hg.2.trans hsub),
    W_simpleHalfLatticeConfig hL hf.1 hg.1.continuous (hf.2.trans hsub) (hg.2.trans hsub)]

/-! ### Exact window counting and separation -/

private theorem card_shifted_lattice_Ioc_sub {h α x y : ℝ} (hh : 0 < h) (hxy : x ≤ y) :
    let S := Finset.Icc (⌊x / h - α⌋ + 1) ⌊y / h - α⌋
    |(S.card : ℝ) - (y - x) / h| ≤ 1 := by
  intro S
  set a := ⌊x / h - α⌋
  set b := ⌊y / h - α⌋
  have hle : x / h - α ≤ y / h - α := by
    have : x / h ≤ y / h := div_le_div_of_nonneg_right hxy hh.le
    linarith
  have hab : a ≤ b := Int.floor_mono hle
  have hcard : (S.card : ℝ) = ((b - a : ℤ) : ℝ) := by
    have hc : S.card = (b + 1 - (a + 1)).toNat := Int.card_Icc (a + 1) b
    have hba : b + 1 - (a + 1) = b - a := by ring
    have hnn : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [hc, hba]
    exact_mod_cast Int.toNat_of_nonneg hnn
  rw [hcard, Int.cast_sub]
  have ha1 : (a : ℝ) ≤ x / h - α := Int.floor_le _
  have ha2 : x / h - α < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hb1 : (b : ℝ) ≤ y / h - α := Int.floor_le _
  have hb2 : y / h - α < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hdiff : (y / h - α) - (x / h - α) = (y - x) / h := by ring
  rw [abs_le]
  constructor <;> linarith

private theorem window_eq_image_Icc {Z : ZeroConfig} {ϕ : ℤ → ℂ} {h α x y : ℝ} (hh : 0 < h)
    (hcar : Z.carrier = Set.range ϕ) (him : ∀ k, (ϕ k).im = ((k : ℝ) + α) * h) :
    Z.window x y = (↑(Finset.Icc (⌊x / h - α⌋ + 1) ⌊y / h - α⌋) : Set ℤ).image ϕ := by
  ext z
  simp only [ZeroConfig.window, hcar, Set.mem_inter_iff, Set.mem_range, Set.mem_setOf_eq,
    Set.mem_image, Finset.mem_coe, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨k, rfl⟩, hx, hy⟩
    rw [him k] at hx hy
    have hk1 : x / h - α < k := by
      have : x / h < (k : ℝ) + α := (div_lt_iff₀ hh).mpr hx
      linarith
    have hk2 : (k : ℝ) ≤ y / h - α := by
      have : (k : ℝ) + α ≤ y / h := (le_div_iff₀ hh).mpr hy
      linarith
    have hfl : ⌊x / h - α⌋ < k := by
      have : (⌊x / h - α⌋ : ℝ) < k := (Int.floor_le _).trans_lt hk1
      exact_mod_cast this
    have hfr : k ≤ ⌊y / h - α⌋ := Int.le_floor.mpr hk2
    exact ⟨k, ⟨by omega, hfr⟩, rfl⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    refine ⟨⟨k, rfl⟩, ?_, ?_⟩
    · rw [him k]
      have h1 : (⌊x / h - α⌋ : ℝ) + 1 ≤ k := by exact_mod_cast hk1
      have h2 : x / h - α < (⌊x / h - α⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h3 : x / h < (k : ℝ) + α := by linarith
      exact (div_lt_iff₀ hh).mp h3
    · rw [him k]
      have h1 : (k : ℝ) ≤ ⌊y / h - α⌋ := by exact_mod_cast hk2
      have h2 : (⌊y / h - α⌋ : ℝ) ≤ y / h - α := Int.floor_le _
      have h3 : (k : ℝ) + α ≤ y / h := by linarith
      exact (le_div_iff₀ hh).mp h3

private theorem N_eq_card_Icc_of_unit_lattice {Z : ZeroConfig} {ϕ : ℤ → ℂ} {h α x y : ℝ}
    (hh : 0 < h) (hinj : Function.Injective ϕ) (hcar : Z.carrier = Set.range ϕ)
    (hmult : ∀ z, Z.mult z = 1) (him : ∀ k, (ϕ k).im = ((k : ℝ) + α) * h) :
    Z.N x y = (Finset.Icc (⌊x / h - α⌋ + 1) ⌊y / h - α⌋).card := by
  classical
  set I := Finset.Icc (⌊x / h - α⌋ + 1) ⌊y / h - α⌋
  have hwin := window_eq_image_Icc (Z := Z) hh hcar him (x := x) (y := y)
  have hfin : (Z.window x y).Finite := Z.finite_window x y
  have hto : hfin.toFinset = I.image ϕ := by
    ext z
    simp [Set.Finite.mem_toFinset, hwin]
  rw [ZeroConfig.N, finsum_mem_eq_finite_toFinset_sum _ hfin, hto]
  simp only [hmult, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_image_of_injective I hinj]

/-- Every interval count of `simpleHalfLatticeConfig hL` lies within `1` of `(L/π)(y − x)`. -/
theorem abs_N_simpleHalfLatticeConfig_sub_le_one {L : ℝ} (hL : 0 < L) {x y : ℝ} (hxy : x ≤ y) :
    |((simpleHalfLatticeConfig hL).N x y : ℝ) - L / π * (y - x)| ≤ 1 := by
  have hh : 0 < π / L := by positivity
  have h2L : 0 < 2 * L := mul_pos two_pos hL
  have him : ∀ k : ℤ, (_root_.RHTower.verticalLatticePoint (2 * L) 0 k).im =
      ((k : ℝ) + 0) * (π / L) := fun k => by
    simp only [_root_.RHTower.verticalLatticePoint]
    field_simp [hL.ne']
    ring
  have hN := N_eq_card_Icc_of_unit_lattice (Z := simpleHalfLatticeConfig hL) hh
    (_root_.RHTower.verticalLatticePoint_injective h2L 0) rfl (fun _ => rfl) him (x := x) (y := y)
  have hcard := card_shifted_lattice_Ioc_sub (α := 0) hh hxy
  have hdiv : (y - x) / (π / L) = L / π * (y - x) := by field_simp; ring
  rwa [hN, ← hdiv]

/-- Every interval count of `shiftedSimpleHalfLatticeConfig hL` lies within `1` of `(L/π)(y − x)`. -/
theorem abs_N_shiftedSimpleHalfLatticeConfig_sub_le_one {L : ℝ} (hL : 0 < L) {x y : ℝ}
    (hxy : x ≤ y) :
    |((shiftedSimpleHalfLatticeConfig hL).N x y : ℝ) - L / π * (y - x)| ≤ 1 := by
  have hh : 0 < π / L := by positivity
  have hN := N_eq_card_Icc_of_unit_lattice (Z := shiftedSimpleHalfLatticeConfig hL) hh
    (shiftedHalfLatticePoint_injective hL) rfl (fun _ => rfl)
    (shiftedHalfLatticePoint_im hL) (x := x) (y := y)
  have hcard := card_shifted_lattice_Ioc_sub (α := 1 / 2) hh hxy
  have hdiv : (y - x) / (π / L) = L / π * (y - x) := by field_simp; ring
  rwa [hN, ← hdiv]

/-- Distinct points in the combined carrier `Z₀ ∪ Z₁` are separated by at least `π / (2L)`. -/
theorem sep_simpleHalfLattice_union_shifted {L : ℝ} (hL : 0 < L) {z w : ℂ}
    (hz : z ∈ (simpleHalfLatticeConfig hL).carrier ∪ (shiftedSimpleHalfLatticeConfig hL).carrier)
    (hw : w ∈ (simpleHalfLatticeConfig hL).carrier ∪ (shiftedSimpleHalfLatticeConfig hL).carrier)
    (hzw : z ≠ w) : π / (2 * L) ≤ ‖z - w‖ := by
  rw [← carrier_double_eq_union hL] at hz hw
  obtain ⟨j, rfl⟩ := hz
  obtain ⟨k, rfl⟩ := hw
  have hjk : j ≠ k := fun e => hzw (by rw [e])
  have h1 : (1 : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by
    have : 1 ≤ |j - k| := Int.one_le_abs (sub_ne_zero.mpr hjk)
    exact_mod_cast this
  have him : |(_root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 j -
      _root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 k).im| =
      |(j : ℝ) - (k : ℝ)| * (π / (2 * L)) := by
    simp only [Complex.sub_im, _root_.RHTower.verticalLatticePoint]
    have e : (j : ℝ) * (2 * π / (2 * (2 * L))) - (k : ℝ) * (2 * π / (2 * (2 * L))) =
        ((j : ℝ) - (k : ℝ)) * (π / (2 * L)) := by field_simp [hL.ne']; ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
  calc π / (2 * L) = 1 * (π / (2 * L)) := (one_mul _).symm
    _ ≤ |(j : ℝ) - (k : ℝ)| * (π / (2 * L)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = |(_root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 j -
          _root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 k).im| := him.symm
    _ ≤ ‖_root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 j -
          _root_.RHTower.verticalLatticePoint (2 * (2 * L)) 0 k‖ := Complex.abs_im_le_norm _

/-- **Sharp Nyquist refutation of two-configuration local inversion across `0 < λ ≤ 1`.**
For every `T ≥ 2π e^π` and every `0 < λ ≤ 1` (in particular across the entire posed range
`½ < λ ≤ 1` at aperture `λ · ½ log(T/2π)`), there exist two critical-line simple tempered
configurations `Z₀, Z₁` with:
1. exact Riemann–von Mangoldt local counts `|N_{Zⱼ}(x, y) − (1/2π) log(T/2π)(y − x)| ≤ 1` on all
   intervals `(x, y]`;
2. identical Weil images `Z₀.W f g = Z₁.W f g` on all windows of aperture `λ · ½ log(T/2π)`;
3. disjoint carriers (`Z₀.carrier ∩ Z₁.carrier = ∅`), a point of `Z₀` in `[T − 1, T + 1]`, and
   uniform minimum distance `‖z − w‖ ≥ π / log(T/2π)` between all distinct points of
   `Z₀.carrier ∪ Z₁.carrier`. -/
theorem exists_rvm_pair_mimic_disjoint_up_to_one {T lam : ℝ}
    (hT : 2 * π * Real.exp π ≤ T) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃ Z₀ Z₁ : ZeroConfig,
      TemperedConfig Z₀ ∧ TemperedConfig Z₁ ∧
      (∀ z ∈ Z₀.carrier, z.re = 1 / 2 ∧ Z₀.mult z = 1) ∧
      (∀ z ∈ Z₁.carrier, z.re = 1 / 2 ∧ Z₁.mult z = 1) ∧
      (∀ x y : ℝ, x ≤ y →
        |(Z₀.N x y : ℝ) - Real.log (T / (2 * π)) / (2 * π) * (y - x)| ≤ 1 ∧
        |(Z₁.N x y : ℝ) - Real.log (T / (2 * π)) / (2 * π) * (y - x)| ≤ 1) ∧
      (∀ f g : ℝ → ℂ,
        ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
        ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) g →
        Z₀.W f g = Z₁.W f g) ∧
      Disjoint Z₀.carrier Z₁.carrier ∧
      (∃ z₀ ∈ Z₀.carrier, |z₀.im - T| ≤ 1) ∧
      (∀ z ∈ Z₀.carrier ∪ Z₁.carrier, ∀ w ∈ Z₀.carrier ∪ Z₁.carrier,
        z ≠ w → π / Real.log (T / (2 * π)) ≤ ‖z - w‖) := by
  have h2π : 0 < 2 * π := by positivity
  have hexp : Real.exp π ≤ T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  have hlog_ge : π ≤ Real.log (T / (2 * π)) := by
    have := Real.log_le_log (Real.exp_pos π) hexp
    rwa [Real.log_exp] at this
  set L := Real.log (T / (2 * π)) / 2 with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith [Real.pi_pos]
  have hLπ : π / 2 ≤ L := by rw [hLdef]; linarith
  refine ⟨simpleHalfLatticeConfig hL, shiftedSimpleHalfLatticeConfig hL,
    temperedConfig_simpleHalfLatticeConfig hL, temperedConfig_shiftedSimpleHalfLatticeConfig hL,
    ?_, ?_, ?_, ?_, disjoint_simpleHalfLattice_shifted hL, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨by simp [_root_.RHTower.verticalLatticePoint], rfl⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨shiftedHalfLatticePoint_re L k, rfl⟩
  · intro x y hxy
    have hd : L / π = Real.log (T / (2 * π)) / (2 * π) := by rw [hLdef]; ring
    rw [← hd]
    exact ⟨abs_N_simpleHalfLatticeConfig_sub_le_one hL hxy,
      abs_N_shiftedSimpleHalfLatticeConfig_sub_le_one hL hxy⟩
  · intro f g hf hg
    have ha : lam * L ≤ L := mul_le_of_le_one_left hL.le hlam1
    exact (W_shiftedSimpleHalfLatticeConfig_eq_simpleHalfLatticeConfig hL ha hf hg).symm
  · set h := π / L
    have hh0 : 0 < h := by positivity
    have hh2 : h ≤ 2 := by
      rw [show h = π / L from rfl, div_le_iff₀ hL]
      linarith
    set k : ℤ := ⌊(T + 1) / h⌋
    refine ⟨_root_.RHTower.verticalLatticePoint (2 * L) 0 k, ⟨k, rfl⟩, ?_⟩
    have him : (_root_.RHTower.verticalLatticePoint (2 * L) 0 k).im = (k : ℝ) * h := by
      simp only [_root_.RHTower.verticalLatticePoint, h]
      field_simp [hL.ne']
      ring
    rw [him, abs_le]
    have hk1 : (k : ℝ) ≤ (T + 1) / h := Int.floor_le _
    have hk2 : (T + 1) / h - 1 < (k : ℝ) := by linarith [Int.lt_floor_add_one ((T + 1) / h)]
    have hmul1 : (k : ℝ) * h ≤ T + 1 := (le_div_iff₀ hh0).mp hk1
    have hmul2 : T + 1 - h < (k : ℝ) * h := by
      have := mul_lt_mul_of_pos_right hk2 hh0
      rwa [sub_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at this
    constructor <;> linarith
  · intro z hz w hw hzw
    have h2 : 2 * L = Real.log (T / (2 * π)) := by rw [hLdef]; ring
    rw [← h2]
    exact sep_simpleHalfLattice_union_shifted hL hz hw hzw

end GaloisForLFunctions.ZeroConfigurationGeometry
