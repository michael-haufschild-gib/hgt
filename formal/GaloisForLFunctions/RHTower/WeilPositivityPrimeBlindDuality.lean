import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistence

/-!
# The existence half of Weil positivity is prime-blind archimedean positivity

For a test `f` write `A(f) = ∫ |f̂(τ)|² A(τ/2π) dτ` for its archimedean energy (`archEnergy`, with the
archimedean Weil symbol of `ζ`) and `c_n(f) = Re (φ_f(log n) + φ_f(-log n))` for the value of its
autocorrelation `φ_f = f ⋆ f̃` at the atom `n` (`atomCoeff`).  The energy of `f` under weights `lam`
is `A(f) - 2π Σ_n lam(n) n^{-1/2} c_n(f)`.

**Prime-blind archimedean positivity** up to level `A` (`PrimeBlindPositive`): every finite family
of polar-constrained `C²` tests `f_i` at levels `≤ A` with weights `α_i ≥ 0` whose combined
autocorrelation vanishes at every `±log n`, `n ≥ 2`, has `Σ α_i A(f_i) ≥ 0`.  The statement contains
the archimedean symbol of `ζ` and the positions `log n` of all integers, and nothing else: no primes,
no zeros, no weights.

* `primeBlindPositive_of_weilPositiveUpTo`: a weight system that is Weil-positive up to level `A`
  forces prime-blind positivity up to level `A`, since on a prime-blind family the weights drop out.
* `exists_weilPositiveUpTo_of_primeBlindPositive`: prime-blind positivity up to level `A + 1`
  produces a weight system that is Weil-positive up to level `A`.  The weights are sought in the
  compact box `|lam(n)| ≤ √n (log n + C₀)`.  If none works, finitely many tests exclude the box, and
  Hahn–Banach separation gives nonnegative weights whose combined energy is negative on the whole box.
  The two-point resonator `g_w(x + log n/2) ± g_w(x - log n/2)` sees exactly the atom `n`
  (`atomCoeff_twoPointResonator`), and its archimedean energy is at most `√n (log n + C₀)` times its
  atom coefficient (`archEnergy_twoPointResonator_le`).  Adding one resonator per atom cancels every
  atom and costs exactly the worst box corner, so the family becomes prime-blind with negative
  archimedean energy.
* `exists_weilPositive_iff_primeBlindPositive`: **a Weil-positive weight system exists iff
  prime-blind archimedean positivity holds at every level.**  With a uniqueness statement for the
  Weil-positive weights, positivity of the von Mangoldt weights would become a statement about the
  archimedean symbol of `ζ` and the set `{log n}` alone.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

/-- The archimedean energy `∫ |f̂(τ)|² A(τ/2π) dτ` of a test. -/
def archEnergy (f : ℝ → ℂ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))

/-- The value `Re (φ_f(log n) + φ_f(-log n))` of the autocorrelation of `f` at the atom `n`. -/
def atomCoeff (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re

/-- A polar-constrained `C²` test supported in `[-a, a]`. -/
def IsPolarTest (a : ℝ) (f : ℝ → ℂ) : Prop :=
  0 ≤ a ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
    paperFT f (-(I / 2)) = 0

theorem atomCoeff_eq_zero_of_floor_lt {a : ℝ} {f : ℝ → ℂ} (hfs : tsupport f ⊆ Icc (-a) a)
    {n : ℕ} (hn : ⌊Real.exp (2 * a)⌋₊ < n) : atomCoeff f n = 0 := by
  have hx : Real.exp (2 * a) < n := Nat.lt_of_floor_lt hn
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hx
  have hlog : 2 * a < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hx
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by exact_mod_cast (show (0:ℝ) < n from hn0))
    exact this)
  have hh : ∀ u, a < |u| → f u = 0 := by
    intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hfs hmem
    rw [mem_Icc] at this
    have := abs_le.mpr ⟨this.1, this.2⟩
    linarith
  unfold atomCoeff
  rw [weilTest_self_eq_zero hh (by rw [abs_of_nonneg hl0]; exact hlog),
    weilTest_self_eq_zero hh (by rw [abs_neg, abs_of_nonneg hl0]; exact hlog)]
  simp

/-- The energy of a test at level `a`, with the atoms counted up to any `M ≥ ⌊e^{2a}⌋`. -/
theorem integral_weilAtomSymbol_eq_archEnergy_sub {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (lam : ℕ → ℝ) {M : ℕ} (hM : ⌊Real.exp (2 * a)⌋₊ ≤ M) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      archEnergy f - 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * atomCoeff f n := by
  rw [integral_weilAtomSymbol_eq_arch_sub hf hfs lam]
  unfold archEnergy
  congr 2
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hM) fun n hn hnot => ?_
  have hlt : ⌊Real.exp (2 * a)⌋₊ < n := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with h | h
    · have := (Finset.mem_Icc.mp hn).1; omega
    · exact h
  rw [show (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re = atomCoeff f n from rfl,
    atomCoeff_eq_zero_of_floor_lt hfs hlt, mul_zero]

/-! ### Two-point resonators: exact affine energies -/

/-- The two-point resonator `g_w(x + (log n)/2) + s g_w(x - (log n)/2)`, `w = 1/(n+1)`. -/
def twoPointResonator (n : ℕ) (s : ℝ) : ℝ → ℂ :=
  resonator n (twoPointCoeff n (s : ℂ)) (1 / ((n : ℝ) + 1))

/-- The mass `∫ g_w²` of one resonator bump, `w = 1/(n+1)`. -/
def resonatorMass (n : ℕ) : ℝ := ∫ t, gR (1 / ((n : ℝ) + 1)) t ^ 2

theorem resonatorMass_pos (n : ℕ) : 0 < resonatorMass n :=
  lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity)) (integral_gR_sq_ge (by positivity))

theorem twoPointCoeff_vanish {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ∀ m, n < m → twoPointCoeff n s m = 0 := by
  intro m hm
  unfold twoPointCoeff
  rw [if_neg (by omega), if_neg (by omega)]

theorem isPolarTest_twoPointResonator {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    IsPolarTest (atomLevel n) (twoPointResonator n s) := by
  have hw : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := n) (c := twoPointCoeff n (s : ℂ)) hw
  refine ⟨by unfold atomLevel; positivity, contDiff_resonator _ _ _ 2, ?_, hp1, hp2⟩
  exact tsupport_subset_of_vanish fun u hu =>
    sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu

theorem atomCoeff_twoPointResonator {n : ℕ} (hn : 2 ≤ n) (s : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    atomCoeff (twoPointResonator n s) m = 2 * resonatorMass n * (if m = n then s else 0) := by
  set w : ℝ := 1 / ((n : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hvan0 : ∀ Y, 1 / ((n : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by rw [← hwdef] at hY; linarith)
  have hgc0 : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgs0 := hasCompactSupport_gC hw
  have hk0 : EF.weilTest (gC w) (gC w) 0 = ((resonatorMass n : ℝ) : ℂ) :=
    weilTest_self_zero_ofReal (g := gR w)
  have h1 := weilTest_translates_log hgc0 hgs0 hvan0 (twoPointCoeff_vanish (by omega) (s : ℂ))
    (show 1 ≤ m by omega)
  have h2 := weilTest_translates_neg_log hgc0 hgs0 hvan0 (twoPointCoeff_vanish (by omega) (s : ℂ))
    (show 1 ≤ m by omega)
  rw [sum_conj_swap] at h2
  unfold atomCoeff
  rw [show twoPointResonator n s =
      fun u => ∑ m ∈ Finset.Icc 1 n, twoPointCoeff n (s : ℂ) m * gC w (u - resPt n m) from rfl,
    h1, h2, hk0, twoPointCoeff_diag hn _ hm]
  split_ifs with h
  · simp [Complex.conj_ofReal]; ring
  · simp

theorem archEnergy_twoPointResonator_le {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    archEnergy (twoPointResonator n s) ≤ 4 * π * resonatorMass n * (Real.log n + boxConst) := by
  have hN : 1 ≤ n := by omega
  have hN1 : (0 : ℝ) < n + 1 := by positivity
  have hNr : (1 : ℝ) ≤ n := by exact_mod_cast hN
  set c : ℕ → ℂ := twoPointCoeff n (s : ℂ) with hcdef
  have hc : ∀ m, n < m → c m = 0 := twoPointCoeff_vanish (by omega) (s : ℂ)
  set w : ℝ := 1 / ((n : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by rw [hwdef, div_le_one hN1]; linarith
  have hwN : w * ((n : ℝ) + 1) = 1 := by rw [hwdef]; field_simp
  set a : ℝ := Real.log n / 2 + w / 4 with hadef
  set F := resonator n c w with hFdef
  set F' := resonatorDeriv n c w with hF'def
  have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu
  have hF'van : ∀ u, a < |u| → F' u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => deriv_gC_eq_zero hw hv) hu
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
  have hF's : tsupport F' ⊆ Icc (-a) a := tsupport_subset_of_vanish hF'van
  have hF2 : ContDiff ℝ 2 F := contDiff_resonator n c w 2
  have hF'2 : ContDiff ℝ 2 F' := contDiff_resonatorDeriv n c w 2
  have hFcs : HasCompactSupport F :=
    hasCompactSupport_of_support_subset_abs (Λ := a) fun u hu => by
      by_contra h; push Not at h; exact hu (hFvan u h)
  set k0r : ℝ := ∫ t, gR w t ^ 2 with hk0r
  set k1r : ℝ := ∫ t, gR' w t ^ 2 with hk1r
  have hk0 : EF.weilTest (gC w) (gC w) 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := gR w)
  have hk1 : EF.weilTest (deriv (gC w)) (deriv (gC w)) 0 = (k1r : ℂ) := by
    rw [deriv_gC]; exact weilTest_self_zero_ofReal (g := gR' w)
  have hvan0 : ∀ Y, 1 / ((n : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by rw [← hwdef] at hY; linarith)
  have hvan1 : ∀ Y, 1 / ((n : ℝ) + 1) ≤ |Y| →
      EF.weilTest (deriv (gC w)) (deriv (gC w)) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => deriv_gC_eq_zero hw hu)
      (by rw [← hwdef] at hY; linarith)
  have hgc0 : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgc1 : Continuous (deriv (gC w)) := (contDiff_deriv_gC w 0).continuous
  have hgs0 := hasCompactSupport_gC hw
  have hgs1 := hasCompactSupport_deriv_gC hw
  have hsumc : ∑ m ∈ Finset.Icc 1 n, ‖c m‖ ^ 2 = 2 := by
    have hpt : ∀ m ∈ Finset.Icc 1 n, ‖c m‖ ^ 2 =
        (if m = 1 then 1 else 0) + (if m = n then 1 else 0) := by
      intro m _
      rw [hcdef]
      unfold twoPointCoeff
      by_cases h1 : m = 1
      · subst h1; simp; omega
      · by_cases h2 : m = n
        · subst h2; rcases hs with rfl | rfl <;> simp [h1]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩),
      if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]; norm_num
  have hmass0 : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 = 2 * π * k0r * 2 := by
    have h := integral_normSq_paperFT_mul_cos_eq hF2 hFs 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc0 hgs0 hvan0 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 n, c m * gC w (u - resPt n m) from rfl, h0, hk0,
      sum_mul_conj_eq, hsumc]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hmass1 : ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = 2 * π * k1r * 2 := by
    have h := integral_normSq_paperFT_mul_cos_eq hF'2 hF's 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc1 hgs1 hvan1 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F' = fun u => ∑ m ∈ Finset.Icc 1 n, c m * deriv (gC w) (u - resPt n m) from rfl, h0,
      hk1, sum_mul_conj_eq, hsumc]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hderiv : ∀ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = τ ^ 2 * ‖paperFT F τ‖ ^ 2 := by
    intro τ
    rw [hF'def, ← deriv_resonator, paperFT_deriv (contDiff_resonator n c w 1) hFcs]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_pow, sq_abs]
  set α : ℝ := Real.log ((n : ℝ) + 1) + 9 / 2 with hα
  set β : ℝ := w ^ 2 / 2 with hβ
  have hpt : ∀ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2 := by
    intro τ
    have hA := archimedeanWeilSymbol_le_log_add τ
    have hpos1 : 0 < 1 + w * |τ| := by positivity
    have hle : 1 + |τ| ≤ ((n : ℝ) + 1) * (1 + w * |τ|) := by
      have : ((n : ℝ) + 1) * (1 + w * |τ|) = (n : ℝ) + 1 + |τ| := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm ((n : ℝ) + 1) w, hwN, one_mul]
      rw [this]; linarith
    have hlog1 : Real.log (1 + |τ|) ≤ Real.log ((n : ℝ) + 1) + w * |τ| := by
      calc Real.log (1 + |τ|) ≤ Real.log (((n : ℝ) + 1) * (1 + w * |τ|)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log ((n : ℝ) + 1) + Real.log (1 + w * |τ|) :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ Real.log ((n : ℝ) + 1) + w * |τ| := by
            have := Real.log_le_sub_one_of_pos hpos1; linarith
    have hamgm : w * |τ| ≤ 1 / 2 + w ^ 2 * τ ^ 2 / 2 := by
      have := sq_nonneg (w * |τ| - 1)
      have h2 : (w * |τ|) ^ 2 = w ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith
    have hA' : archimedeanWeilSymbol (τ / (2 * π)) ≤ α + β * τ ^ 2 := by
      rw [hα, hβ]; linarith
    rw [hderiv τ]
    have hnn : 0 ≤ ‖paperFT F τ‖ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hA' hnn
    linarith
  have hint1 := integrable_normSq_paperFT_mul_arch hF2 hFs
  have hint2 := integrable_normSq_paperFT hF2 hFs
  have hint3 := integrable_normSq_paperFT hF'2 hF's
  have harch : archEnergy F ≤ α * (2 * π * k0r * 2) + β * (2 * π * k1r * 2) := by
    calc archEnergy F = ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) := rfl
      _ ≤ ∫ τ : ℝ, (α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2) :=
          integral_mono hint1 ((hint2.const_mul α).add (hint3.const_mul β)) hpt
      _ = α * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) + β * ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 := by
          rw [integral_add (hint2.const_mul α) (hint3.const_mul β), integral_const_mul,
            integral_const_mul]
      _ = α * (2 * π * k0r * 2) + β * (2 * π * k1r * 2) := by rw [hmass0, hmass1]
  have hratio : β * k1r ≤ profileRatio / 2 * k0r := by
    have := sq_mul_integral_gR'_le hw hw1
    rw [hβ, hk1r, hk0r]; nlinarith
  have hlog2 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hk0pos : 0 < k0r := resonatorMass_pos n
  have hkm : resonatorMass n = k0r := rfl
  rw [hkm]
  have hpi : 0 < π := Real.pi_pos
  have h1 : β * (2 * π * k1r * 2) ≤ 4 * π * (profileRatio / 2 * k0r) := by
    have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4 * π by positivity)
    nlinarith
  have h2 : α * (2 * π * k0r * 2) ≤ 4 * π * k0r * (Real.log 2 + Real.log n + 9 / 2) := by
    have : α ≤ Real.log 2 + Real.log n + 9 / 2 := by rw [hα]; linarith
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 4 * π * k0r by positivity)
    nlinarith
  calc archEnergy (twoPointResonator n s) = archEnergy F := rfl
    _ ≤ α * (2 * π * k0r * 2) + β * (2 * π * k1r * 2) := harch
    _ ≤ 4 * π * k0r * (Real.log 2 + Real.log n + 9 / 2) + 4 * π * (profileRatio / 2 * k0r) := by
        linarith
    _ = 4 * π * k0r * (Real.log n + boxConst) := by unfold boxConst; ring

/-! ### Prime-blind archimedean positivity and the existence of Weil-positive weights -/

/-- **Prime-blind archimedean positivity up to level `A`.**  For every finite family of
polar-constrained `C²` tests `f_i` at levels `a_i ≤ A` and weights `α_i ≥ 0` whose combined
autocorrelation `Φ = Σ α_i f_i ⋆ f̃_i` vanishes at `±log n` for every `n ≥ 2`, the archimedean energy
`Σ α_i ∫ |f̂_i|² A` is nonnegative.  Only the archimedean symbol of `ζ` and the positions `log n`
enter. -/
def PrimeBlindPositive (A : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ),
    (∀ i, a i ≤ A) → (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) →
    (∀ n : ℕ, 2 ≤ n → ∑ i, α i * atomCoeff (f i) n = 0) →
    0 ≤ ∑ i, α i * archEnergy (f i)

/-- The energy of a weighted family is the weighted archimedean energy minus the weights paired with
the combined autocorrelation at the atoms. -/
theorem sum_mul_energy_eq {ι : Type} [Fintype ι] (f : ι → ℝ → ℂ) (α : ι → ℝ) (lam : ℕ → ℝ)
    (M : ℕ) :
    ∑ i, α i * (archEnergy (f i) - 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n *
        atomCoeff (f i) n) =
      ∑ i, α i * archEnergy (f i) - 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n *
        ∑ i, α i * atomCoeff (f i) n := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring

/-- Weil positivity up to level `A` implies prime-blind archimedean positivity up to level `A`: on a
prime-blind family the weights drop out of the energy. -/
theorem primeBlindPositive_of_weilPositiveUpTo {lam : ℕ → ℝ} {A : ℝ}
    (hW : WeilPositiveUpTo lam A) : PrimeBlindPositive A := by
  intro ι _ a f α ha hf hα hblind
  set M := ⌊Real.exp (2 * A)⌋₊
  have hM : ∀ i, ⌊Real.exp (2 * a i)⌋₊ ≤ M := fun i =>
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [ha i]))
  have hE : ∀ i, 0 ≤ archEnergy (f i) -
      2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * atomCoeff (f i) n := by
    intro i
    obtain ⟨ha0, hf2, hfs, hp, hm⟩ := hf i
    rw [← integral_weilAtomSymbol_eq_archEnergy_sub hf2 hfs lam (hM i)]
    exact hW (a i) ha0 (ha i) (f i) hf2 hfs hp hm
  have hzero : ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * ∑ i, α i * atomCoeff (f i) n = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [hblind n (Finset.mem_Icc.mp hn).1, mul_zero]
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hα i) (hE i)
  rwa [sum_mul_energy_eq, hzero, mul_zero, sub_zero] at this

theorem boxWidth_div_sqrt {n : ℕ} (hn : 2 ≤ n) :
    boxWidth n / Real.sqrt n = Real.log n + boxConst := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hc : 0 < boxConst := by
    unfold boxConst
    have := profileRatio_nonneg
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  unfold boxWidth
  rw [abs_of_nonneg (by positivity)]
  field_simp

theorem atomLevel_le {A : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnM : n ≤ ⌊Real.exp (2 * A)⌋₊) :
    atomLevel n ≤ A + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnle : (n : ℝ) ≤ Real.exp (2 * A) :=
    le_trans (by exact_mod_cast hnM) (Nat.floor_le (Real.exp_pos _).le)
  have hlog : Real.log n ≤ 2 * A := by
    have := Real.log_le_log hn0 hnle
    rwa [Real.log_exp] at this
  have hw : 1 / ((n : ℝ) + 1) / 4 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]; linarith
  unfold atomLevel
  linarith

/-- **Existence from prime-blind positivity.**  Prime-blind archimedean positivity up to level
`A + 1` produces a weight system that is Weil-positive up to level `A`.

The weights are sought in the compact box `|lam(n)| ≤ √n (log n + C₀)`.  If none works, finitely
many tests already exclude the box, and Hahn–Banach separation of the compact convex set of their
energy vectors from the nonnegative orthant gives weights `α ≥ 0` whose combined energy is negative
on the whole box.  Adding the two-point resonator at each atom `n`, with weight
`|C_n|/(2 ∫ g_w²)` and sign opposite to the combined atom coefficient `C_n`, cancels every atom
exactly.  The resonators cost at most `√n (log n + C₀) |C_n|` of archimedean energy, which is the
worst box corner, so the resulting prime-blind family has negative archimedean energy. -/
theorem exists_weilPositiveUpTo_of_primeBlindPositive {A : ℝ}
    (hP : PrimeBlindPositive (A + 1)) : ∃ lam : ℕ → ℝ, WeilPositiveUpTo lam A := by
  classical
  set M := ⌊Real.exp (2 * A)⌋₊ with hMdef
  let T := {p : ℝ × (ℝ → ℂ) // p.1 ≤ A ∧ IsPolarTest p.1 p.2}
  let E : T → (ℕ → ℝ) → ℝ := fun p lam =>
    archEnergy p.1.2 - 2 * π * ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * atomCoeff p.1.2 n
  set B : Set (ℕ → ℝ) := Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) with hBdef
  have hBc : IsCompact B := isCompact_univ_pi fun n => isCompact_Icc
  have hBconv : Convex ℝ B := convex_pi fun n _ => convex_Icc _ _
  have hEcont : ∀ p : T, Continuous (E p) := fun p =>
    continuous_const.sub (continuous_const.mul (continuous_finsetSum _ fun n _ =>
      ((continuous_apply n).div_const _).mul_const _))
  let K : T → Set (ℕ → ℝ) := fun p => {lam | 0 ≤ E p lam}
  have hKc : ∀ p, IsClosed (K p) := fun p => isClosed_le continuous_const (hEcont p)
  have hMle : ∀ p : T, ⌊Real.exp (2 * p.1.1)⌋₊ ≤ M := fun p =>
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [p.2.1]))
  suffices hne : (B ∩ ⋂ p, K p).Nonempty by
    obtain ⟨lam, -, hlam⟩ := hne
    refine ⟨lam, fun a ha haA f hf hfs hp hm => ?_⟩
    have hmem := Set.mem_iInter.mp hlam ⟨(a, f), haA, ha, hf, hfs, hp, hm⟩
    rw [integral_weilAtomSymbol_eq_archEnergy_sub hf hfs lam
      (hMle ⟨(a, f), haA, ha, hf, hfs, hp, hm⟩)]
    exact hmem
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  obtain ⟨u, hu⟩ := hBc.elim_finite_subfamily_closed K hKc hemp
  -- separation of the energy vectors from the nonnegative orthant
  let Φ : (ℕ → ℝ) → (↥u → ℝ) := fun lam p => E p.1 lam
  have haff : ∀ (p : T) (l₁ l₂ : ℕ → ℝ) (a b : ℝ), a + b = 1 →
      E p (a • l₁ + b • l₂) = a * E p l₁ + b * E p l₂ := by
    intro p l₁ l₂ a b hab
    simp only [E, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ n ∈ Finset.Icc 2 M, (a * l₁ n + b * l₂ n) / Real.sqrt n * atomCoeff p.1.2 n =
        a * ∑ n ∈ Finset.Icc 2 M, l₁ n / Real.sqrt n * atomCoeff p.1.2 n +
          b * ∑ n ∈ Finset.Icc 2 M, l₂ n / Real.sqrt n * atomCoeff p.1.2 n := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hs]
    linear_combination (-archEnergy p.1.2) * hab
  set C : Set (↥u → ℝ) := Φ '' B with hCdef
  set O : Set (↥u → ℝ) := Set.univ.pi fun _ => Ici (0 : ℝ) with hOdef
  have hCconv : Convex ℝ C := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    obtain ⟨l₁, hl₁, rfl⟩ := hy₁
    obtain ⟨l₂, hl₂, rfl⟩ := hy₂
    refine ⟨a • l₁ + b • l₂, hBconv hl₁ hl₂ ha hb hab, ?_⟩
    funext p
    simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, haff p.1 l₁ l₂ a b hab]
  have hCc : IsCompact C := hBc.image (continuous_pi fun p => hEcont p.1)
  have hOconv : Convex ℝ O := convex_pi fun _ _ => convex_Ici 0
  have hOc : IsClosed O := isClosed_set_pi fun _ _ => isClosed_Ici
  have hdisj : Disjoint C O := by
    rw [Set.disjoint_left]
    rintro y ⟨lam, hlam, rfl⟩ hO
    have hmem : lam ∈ B ∩ ⋂ p ∈ u, K p :=
      ⟨hlam, Set.mem_iInter₂.mpr fun p hp => (Set.mem_univ_pi.mp hO) ⟨p, hp⟩⟩
    rw [hu] at hmem
    exact hmem
  obtain ⟨φ, u₀, v₀, hφC, huv, hφO⟩ :=
    geometric_hahn_banach_compact_closed hCconv hCc hOconv hOc hdisj
  have hv₀ : v₀ < 0 := by
    have := hφO 0 (Set.mem_univ_pi.mpr fun _ => Set.mem_Ici.mpr le_rfl)
    rwa [map_zero] at this
  let α : ↥u → ℝ := fun p => φ fun j => if p = j then 1 else 0
  have hα : ∀ p, 0 ≤ α p := by
    intro p
    by_contra h
    push Not at h
    have hmem : (v₀ / α p) • (fun j : ↥u => if p = j then (1 : ℝ) else 0) ∈ O := by
      refine Set.mem_univ_pi.mpr fun j => Set.mem_Ici.mpr ?_
      have : 0 ≤ v₀ / α p := (div_pos_of_neg_of_neg hv₀ h).le
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp [this]
    have := hφO _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne] at this
    exact lt_irrefl _ this
  have hφsum : ∀ y : ↥u → ℝ, φ y = ∑ p, α p * y p := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (φ : (↥u → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hneg : ∀ lam ∈ B, ∑ p, α p * E p.1 lam < 0 := by
    intro lam hlam
    have := hφC (Φ lam) ⟨lam, hlam, rfl⟩
    rw [hφsum] at this
    linarith
  -- the worst box corner
  let Cn : ℕ → ℝ := fun n => ∑ p : ↥u, α p * atomCoeff p.1.1.2 n
  let lamS : ℕ → ℝ := fun n => if 0 ≤ Cn n then -boxWidth n else boxWidth n
  have hlamS : lamS ∈ B := by
    refine Set.mem_univ_pi.mpr fun n => ?_
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [lamS, mem_Icc]
    split_ifs <;> constructor <;> linarith
  have hcorner : ∑ p, α p * E p.1 lamS = ∑ p : ↥u, α p * archEnergy p.1.1.2 +
      2 * π * ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * |Cn n| := by
    have h := sum_mul_energy_eq (fun p : ↥u => p.1.1.2) α lamS M
    simp only [E]
    rw [h]
    have hterm : ∀ n ∈ Finset.Icc 2 M, lamS n / Real.sqrt n * Cn n =
        -((Real.log n + boxConst) * |Cn n|) := by
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      rw [← boxWidth_div_sqrt hn2]
      simp only [lamS]
      split_ifs with hc
      · rw [abs_of_nonneg hc]; ring
      · rw [abs_of_neg (not_le.mp hc)]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    ring
  -- the prime-blind family: the tests of `u` and one resonator per atom
  let sgn : ℕ → ℝ := fun n => if 0 ≤ Cn n then -1 else 1
  have hsgn : ∀ n, sgn n = 1 ∨ sgn n = -1 := fun n => by
    simp only [sgn]; split_ifs <;> simp
  let aF : ↥u ⊕ ↥(Finset.Icc 2 M) → ℝ :=
    Sum.elim (fun p => p.1.1.1) (fun n => atomLevel n.1)
  let fF : ↥u ⊕ ↥(Finset.Icc 2 M) → ℝ → ℂ :=
    Sum.elim (fun p => p.1.1.2) (fun n => twoPointResonator n.1 (sgn n.1))
  let αF : ↥u ⊕ ↥(Finset.Icc 2 M) → ℝ :=
    Sum.elim α (fun n => |Cn n.1| / (2 * resonatorMass n.1))
  have hlev : ∀ x, aF x ≤ A + 1 := by
    rintro (p | n)
    · show p.1.1.1 ≤ A + 1
      linarith [p.1.2.1]
    · exact atomLevel_le (Finset.mem_Icc.mp n.2).1 (Finset.mem_Icc.mp n.2).2
  have hpol : ∀ x, IsPolarTest (aF x) (fF x) := by
    rintro (p | n)
    · exact p.1.2.2
    · exact isPolarTest_twoPointResonator (Finset.mem_Icc.mp n.2).1 _
  have hwt : ∀ x, 0 ≤ αF x := by
    rintro (p | n)
    · exact hα p
    · exact div_nonneg (abs_nonneg _) (by have := resonatorMass_pos n.1; positivity)
  have hblind : ∀ m : ℕ, 2 ≤ m → ∑ x, αF x * atomCoeff (fF x) m = 0 := by
    intro m hm
    rw [Fintype.sum_sum_type]
    have hres : ∑ n : ↥(Finset.Icc 2 M), αF (Sum.inr n) * atomCoeff (fF (Sum.inr n)) m =
        ∑ n ∈ Finset.Icc 2 M, (if m = n then |Cn n| * sgn n else 0) := by
      rw [← Finset.sum_coe_sort (Finset.Icc 2 M)]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hn2 := (Finset.mem_Icc.mp n.2).1
      have hk := resonatorMass_pos n.1
      simp only [αF, fF, Sum.elim_inr]
      rw [atomCoeff_twoPointResonator hn2 _ hm]
      split_ifs
      · field_simp
      · simp
    rw [hres, Finset.sum_ite_eq]
    show Cn m + _ = 0
    split_ifs with hmM
    · simp only [sgn]
      split_ifs with hc
      · rw [abs_of_nonneg hc]; ring
      · rw [abs_of_neg (not_le.mp hc)]; ring
    · have hMm : M < m := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmM
        rcases hmM with h | h
        · omega
        · exact h
      have : Cn m = 0 := Finset.sum_eq_zero fun p _ => by
        rw [atomCoeff_eq_zero_of_floor_lt p.1.2.2.2.2.1 (lt_of_le_of_lt (hMle p.1) hMm), mul_zero]
      rw [this, add_zero]
  have hpos := hP _ aF fF αF hlev hpol hwt hblind
  rw [Fintype.sum_sum_type] at hpos
  have hres : ∑ n : ↥(Finset.Icc 2 M), αF (Sum.inr n) * archEnergy (fF (Sum.inr n)) ≤
      2 * π * ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * |Cn n| := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort (Finset.Icc 2 M)]
    refine Finset.sum_le_sum fun n _ => ?_
    have hn2 := (Finset.mem_Icc.mp n.2).1
    have hk := resonatorMass_pos n.1
    simp only [αF, fF, Sum.elim_inr]
    have hle := archEnergy_twoPointResonator_le hn2 (hsgn n.1)
    have hc : 0 ≤ |Cn n.1| / (2 * resonatorMass n.1) :=
      div_nonneg (abs_nonneg _) (by positivity)
    calc |Cn n.1| / (2 * resonatorMass n.1) * archEnergy (twoPointResonator n.1 (sgn n.1))
        ≤ |Cn n.1| / (2 * resonatorMass n.1) *
            (4 * π * resonatorMass n.1 * (Real.log n.1 + boxConst)) :=
          mul_le_mul_of_nonneg_left hle hc
      _ = 2 * π * ((Real.log n.1 + boxConst) * |Cn n.1|) := by field_simp; ring
  have hsumu : ∑ p : ↥u, αF (Sum.inl p) * archEnergy (fF (Sum.inl p)) =
      ∑ p : ↥u, α p * archEnergy p.1.1.2 := rfl
  have := hneg lamS hlamS
  rw [hcorner] at this
  linarith

/-- **The existence half of Weil positivity is prime-blind archimedean positivity.**  A weight
system that is Weil-positive at every level (finite-atom Weil symbol of `ζ`, polar-constrained `C²`
tests) exists iff prime-blind archimedean positivity holds at every level.  The right side involves
only the archimedean symbol of `ζ` and the positions `log n`, `n ≥ 2`: neither primes nor zeros. -/
theorem exists_weilPositive_iff_primeBlindPositive :
    (∃ lam : ℕ → ℝ, WeilPositive lam) ↔ ∀ A : ℝ, PrimeBlindPositive A := by
  constructor
  · rintro ⟨lam, hlam⟩ A
    exact primeBlindPositive_of_weilPositiveUpTo fun a ha _ f hf hfs hp hm => hlam a ha f hf hfs hp hm
  · intro h
    exact exists_weilPositive_iff_forall_level.mpr fun A =>
      exists_weilPositiveUpTo_of_primeBlindPositive (h (A + 1))

end RHTower
