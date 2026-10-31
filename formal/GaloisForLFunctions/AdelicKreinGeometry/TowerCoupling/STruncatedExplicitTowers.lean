import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.PolarSecondDifference
import GaloisForLFunctions.AdelicKreinGeometry.ASignatureFormulaForPrimeTowers
import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectivityBatteryOnPrimeTowers
import GaloisForLFunctions.HeckeKreinToeplitz.OnTheFiniteStratumEveryFlipHasInfiniteIndex
import GaloisForLFunctions.RHTower.WeilFullConePNTErrorWiener
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketEnergy

/-!
# Separable `S`-truncated explicit-formula prime-tower assemblies

Let `S` be a finite set of primes and `K_S = Σ_{p ∈ S} k_p^{(S)}(v_p(·))` (`towerAssembly S k`) a
separable prime-tower assembly whose local kernels combine `S`-truncated prime powers, the Gamma
archimedean integral, a local pole share `wPole p · towerPole g (log p)`, and local running
counterterms `C + D·δ₁ + A·negAbsKernel`.

* **`S`-truncated weights are `ℓ¹` at `s = ½`** (`summable_truncWeight_div_sqrt`): restricting any
  weight `lam` bounded along each prime tower `p ∈ S` (including `Λ` and `primeFlipWeight q`) to
  prime powers of `S` gives `Σ_{n ≥ 2} |lam_S(n)| / √n < ∞`.
* **Local decay and pole pair structure** (`tendsto_towerPrime_atTop`, `tendsto_towerArch_atTop`,
  `towerPole_eq_pairKernel`): on every tower `ℓ > 0`, both the `S`-truncated prime correlation and
  the Gamma correlation tend to `0` at `+∞`, while the pole correlation is the hyperbolic pair
  `pairKernel (valChar e^{ℓ/2}) (poleWeight g)`.
* **Glued signature classification and zero-blindness** (`negIndex_archGlue_sTruncatedAssembly`):
  either some local non-pole second difference fails positive definiteness and
  `κ(archGlue(K_S, c)) = ⊤`, or every local polar index `κ₀(k_p^{(S)}) ∈ {0, 1}` counts only
  whether `wPole p · poleWeight g ≠ 0` and `κ(archGlue(K_S, c)) ∈ {r_S + 1, r_S + 2}`—receiving
  zero contribution from primes in `S` or Gamma.
* **Pole-retaining divergence** (`card_add_one_le_negIndex_archGlue_poleRetaining`,
  `tendsto_negIndex_archGlue_poleRetaining_atTop`): for the cubic spline and nonzero pole shares,
  `κ(archGlue(K_S, c)) ≥ |S| + 1 → ⊤` for all running counterterms.
* **Pole-free spectral gap and twin-flip blindness** (`negIndex_archGlue_poleFree_mem`,
  `negIndex_weilArchState_ne_two`, `exists_diagonal_counterterm_posDef`,
  `exists_prime_flip_obstruction`): pole-free assemblies have glued index in `{1, 2, ⊤}`, missing
  every finite non-RH value `κ(K_ζ) + 1 ≥ 3`, while diagonal counterterms collapse both `Λ` and its
  single-prime flip to glued index `1` even though at least one of the two has global index `⊤`.
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ComplexConjugate Real
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport
  rightZeros)
open GaloisForLFunctions.ArithmeticCountingPositivity (primeFlipWeight abs_primeFlipWeight)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline cubicSpline_eq_zero paperFT_cubicSpline_ne_zero)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

/-! ### `S`-truncated arithmetic weights and `ℓ¹` summability at `s = ½` -/

/-- `n` is a positive prime power `p^k` (`k ≥ 1`) of a prime `p ∈ S`. -/
def IsSPrimePow (S : Finset Nat.Primes) (n : ℕ) : Prop :=
  ∃ p ∈ S, ∃ k : ℕ, 1 ≤ k ∧ n = (p : ℕ) ^ k

/-- Restriction of an arithmetic weight `lam : ℕ → ℝ` to prime powers of `S`. -/
def truncWeight (S : Finset Nat.Primes) (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  open Classical in if IsSPrimePow S n then lam n else 0

/-- The `S`-truncated von Mangoldt weight `Λ_S`. -/
def vonMangoldtS (S : Finset Nat.Primes) : ℕ → ℝ :=
  truncWeight S fun n => (ArithmeticFunction.vonMangoldt n : ℝ)

theorem abs_truncWeight_le (S : Finset Nat.Primes) (lam : ℕ → ℝ) (n : ℕ) :
    |truncWeight S lam n| ≤ |lam n| := by
  classical
  simp only [truncWeight]
  split_ifs
  · exact le_rfl
  · simp

/-- **Finite prime-set `ℓ¹` summability at `s = ½`.** If `lam` is bounded on the powers of each
prime `p ∈ S`, then `Σ_{n ≥ 2} |truncWeight S lam n| / √n < ∞`. -/
theorem summable_truncWeight_div_sqrt (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ p ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((p : ℕ) ^ k)| ≤ C) :
    Summable fun n : ℕ => if 2 ≤ n then |truncWeight S lam n| / Real.sqrt n else 0 := by
  classical
  set g : ℕ → ℝ := fun n => if 2 ≤ n then |truncWeight S lam n| / Real.sqrt n else 0
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [g]
    split_ifs <;> positivity
  have hC : ∀ p : Nat.Primes, ∃ C : ℝ, 0 ≤ C ∧
      (p ∈ S → ∀ k : ℕ, 1 ≤ k → |lam ((p : ℕ) ^ k)| ≤ C) := fun p => by
    by_cases hp : p ∈ S
    · obtain ⟨C, hC⟩ := hlam p hp
      exact ⟨max 0 C, le_max_left _ _, fun _ k hk => (hC k hk).trans (le_max_right _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose C hC0 hC_bd using hC
  set r : Nat.Primes → ℝ := fun p => (Real.sqrt (p : ℕ))⁻¹
  have hr0 : ∀ p, 0 ≤ r p := fun p => by simp only [r]; positivity
  have hr1 : ∀ p : Nat.Primes, r p < 1 := fun p => by
    have hp2 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    have hsq : 1 < Real.sqrt (p : ℕ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt zero_le_one hp2
    exact inv_lt_one_of_one_lt₀ hsq
  refine summable_of_sum_le hg0 (c := ∑ p ∈ S, C p * (1 - r p)⁻¹) fun t => ?_
  set K : ℕ := t.sup id
  have hterm : ∀ n ∈ t, g n ≤
      ∑ p ∈ S, ∑ k ∈ Icc 1 K, if n = (p : ℕ) ^ k then C p * r p ^ k else 0 := by
    intro n hn
    by_cases h2 : 2 ≤ n ∧ IsSPrimePow S n
    · obtain ⟨hn2, p₀, hp₀, k₀, hk₀, rfl⟩ := h2
      have hkK : k₀ ≤ K := by
        have hlt : k₀ < (p₀ : ℕ) ^ k₀ :=
          lt_of_lt_of_le k₀.lt_two_pow_self (Nat.pow_le_pow_left p₀.2.two_le k₀)
        have hsup : (p₀ : ℕ) ^ k₀ ≤ K := Finset.le_sup (f := id) hn
        exact hlt.le.trans hsup
      have hval : g ((p₀ : ℕ) ^ k₀) ≤ C p₀ * r p₀ ^ k₀ := by
        simp only [g, if_pos hn2, truncWeight, if_pos ⟨p₀, hp₀, k₀, hk₀, rfl⟩]
        have hsq : Real.sqrt (((p₀ : ℕ) ^ k₀ : ℕ) : ℝ) = Real.sqrt (p₀ : ℕ) ^ k₀ := by
          rw [Nat.cast_pow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
            ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast,
            ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
        rw [hsq, div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_right (hC_bd p₀ hp₀ k₀ hk₀) (pow_nonneg (hr0 p₀) _)
      have hsingle1 : C p₀ * r p₀ ^ k₀ ≤
          ∑ k ∈ Icc 1 K, if (p₀ : ℕ) ^ k₀ = (p₀ : ℕ) ^ k then C p₀ * r p₀ ^ k else 0 := by
        have := single_le_sum
          (f := fun k => if (p₀ : ℕ) ^ k₀ = (p₀ : ℕ) ^ k then C p₀ * r p₀ ^ k else 0)
          (fun k _ => by split_ifs; exact mul_nonneg (hC0 p₀) (pow_nonneg (hr0 p₀) _); exact le_rfl)
          (mem_Icc.mpr ⟨hk₀, hkK⟩)
        simpa using this
      exact (hval.trans hsingle1).trans (single_le_sum
        (f := fun p => ∑ k ∈ Icc 1 K, if (p₀ : ℕ) ^ k₀ = (p : ℕ) ^ k then C p * r p ^ k else 0)
        (fun p _ => sum_nonneg fun k _ => by
          split_ifs; exact mul_nonneg (hC0 p) (pow_nonneg (hr0 p) _); exact le_rfl) hp₀)
    · have hg_zero : g n = 0 := by
        simp only [g, truncWeight]
        by_cases hn2 : 2 ≤ n
        · have hnot : ¬ IsSPrimePow S n := fun hs => h2 ⟨hn2, hs⟩
          simp [hn2, hnot]
        · simp [hn2]
      rw [hg_zero]
      exact sum_nonneg fun p _ => sum_nonneg fun k _ => by
        split_ifs; exact mul_nonneg (hC0 p) (pow_nonneg (hr0 p) _); exact le_rfl
  calc ∑ n ∈ t, g n
      ≤ ∑ n ∈ t, ∑ p ∈ S, ∑ k ∈ Icc 1 K, if n = (p : ℕ) ^ k then C p * r p ^ k else 0 :=
        sum_le_sum hterm
    _ = ∑ p ∈ S, ∑ k ∈ Icc 1 K, ∑ n ∈ t, if n = (p : ℕ) ^ k then C p * r p ^ k else 0 := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ p ∈ S, ∑ k ∈ Icc 1 K, C p * r p ^ k := by
        refine sum_le_sum fun p _ => sum_le_sum fun k _ => ?_
        rw [Finset.sum_ite_eq']
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hC0 p) (pow_nonneg (hr0 p) _)
    _ ≤ ∑ p ∈ S, C p * (1 - r p)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hC0 p)
        have hgeom := hasSum_geometric_of_lt_one (hr0 p) (hr1 p)
        exact (hgeom.summable.sum_le_tsum (Icc 1 K) fun k _ => pow_nonneg (hr0 p) k).trans
          hgeom.tsum_eq.le

theorem summable_truncWeight_of_bdd (S : Finset Nat.Primes) {lam : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |lam n| ≤ B) :
    Summable fun n : ℕ => if 2 ≤ n then |truncWeight S lam n| / Real.sqrt n else 0 :=
  summable_truncWeight_div_sqrt S fun _ _ => ⟨B, fun _ _ => hB _⟩

theorem vonMangoldt_prime_pow_le_log (p : Nat.Primes) {k : ℕ} (hk : 1 ≤ k) :
    |(ArithmeticFunction.vonMangoldt ((p : ℕ) ^ k) : ℝ)| ≤ Real.log (p : ℕ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le))]

theorem summable_vonMangoldtS_div_sqrt (S : Finset Nat.Primes) :
    Summable fun n : ℕ => if 2 ≤ n then |vonMangoldtS S n| / Real.sqrt n else 0 :=
  summable_truncWeight_div_sqrt S fun p _ => ⟨Real.log (p : ℕ), fun _ hk =>
    vonMangoldt_prime_pow_le_log p hk⟩

theorem summable_truncWeight_primeFlipWeight_div_sqrt (S : Finset Nat.Primes) (q : ℕ) :
    Summable fun n : ℕ =>
      if 2 ≤ n then |truncWeight S (primeFlipWeight q) n| / Real.sqrt n else 0 :=
  summable_truncWeight_div_sqrt S fun p _ => ⟨Real.log (p : ℕ), fun k hk => by
    rw [abs_primeFlipWeight]; exact vonMangoldt_prime_pow_le_log p hk⟩

/-! ### Explicit-formula tower pieces on `ℤ` -/

/-- The pole weight `(g ⋆ g̃)^(i/2)` of a generator `g : ℝ → ℂ`. -/
def poleWeight (g : ℝ → ℂ) : ℂ :=
  paperFT (EF.weilTest g g) (I / 2)

theorem poleWeight_eq_mul_conj {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    poleWeight g = paperFT g (I / 2) * conj (paperFT g (-I / 2)) := by
  have hc : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  rw [poleWeight, EF.paperFT_weilTest hg hg hgc hgc, hc]

theorem poleWeight_cubicSpline_ne_zero : poleWeight (cx cubicSpline) ≠ 0 := by
  have h1 : (I / 2 : ℂ).im ≠ 0 := by simp
  have h2 : (-I / 2 : ℂ).im ≠ 0 := by simp
  rw [poleWeight_eq_mul_conj (cx_contDiff contDiff_cubicSpline).continuous
    (cx_hasCompactSupport hasCompactSupport_cubicSpline)]
  exact mul_ne_zero (paperFT_cubicSpline_ne_zero h1)
    ((map_ne_zero _).mpr (paperFT_cubicSpline_ne_zero h2))

/-- The pole term of the explicit formula along the tower of step `ℓ`. -/
def towerPole (g : ℝ → ℂ) (ℓ : ℝ) (m : Multiplicative ℤ) : ℂ :=
  RHTower.WeilSpectral.polePart
    (RHTower.WeilSpectral.transl (-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

/-- The prime term of the explicit formula along the tower of step `ℓ`. -/
def towerPrime (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) (m : Multiplicative ℤ) : ℂ :=
  RHTower.WeilSpectral.primePart lam
    (RHTower.WeilSpectral.transl (-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

/-- The archimedean Gamma term of the explicit formula along the tower of step `ℓ`. -/
def towerArch (g : ℝ → ℂ) (ℓ : ℝ) (m : Multiplicative ℤ) : ℂ :=
  RHTower.WeilSpectral.archPart
    (RHTower.WeilSpectral.transl (-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

theorem towerKernel_eq_parts (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) (m : Multiplicative ℤ) :
    towerKernel lam g ℓ m = towerPole g ℓ m - towerPrime lam g ℓ m + towerArch g ℓ m := rfl

private theorem tilde_transl_weilTest_self (g : ℝ → ℂ) (y : ℝ) :
    EF.tilde (RHTower.WeilSpectral.transl y (EF.weilTest g g)) =
      RHTower.WeilSpectral.transl (-y) (EF.weilTest g g) := by
  funext x
  have h := congrFun (RHTower.WeilSpectral.tilde_weilTest_self g) (x + y)
  simp only [EF.tilde, RHTower.WeilSpectral.transl] at h ⊢
  rw [← h]
  congr 2
  ring

theorem isHermKernel_towerPrime (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) :
    IsHermKernel (towerPrime lam g ℓ) := fun m => by
  show towerPrime lam g ℓ m⁻¹ = conj (towerPrime lam g ℓ m)
  set y : ℝ := -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ
  have hy : -((Multiplicative.toAdd m⁻¹ : ℤ) : ℝ) * ℓ = -y := by
    simp only [toAdd_inv, Int.cast_neg, y]; ring
  simp only [towerPrime, hy, ← tilde_transl_weilTest_self g y, RHTower.WeilSpectral.primePart,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [EF.tilde, neg_neg, map_mul, map_add, Complex.conj_ofReal]
  ring

theorem isHermKernel_towerArch (g : ℝ → ℂ) (ℓ : ℝ) :
    IsHermKernel (towerArch g ℓ) := fun m => by
  show towerArch g ℓ m⁻¹ = conj (towerArch g ℓ m)
  set y : ℝ := -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ
  have hy : -((Multiplicative.toAdd m⁻¹ : ℤ) : ℝ) * ℓ = -y := by
    simp only [toAdd_inv, Int.cast_neg, y]; ring
  simp only [towerArch, hy, ← tilde_transl_weilTest_self g y, RHTower.WeilSpectral.archPart]
  have hint : (∫ r : ℝ, paperFT (EF.tilde (RHTower.WeilSpectral.transl y (EF.weilTest g g))) r *
      (EF.gammaBracket r : ℂ)) =
      conj (∫ r : ℝ, paperFT (RHTower.WeilSpectral.transl y (EF.weilTest g g)) r *
        (EF.gammaBracket r : ℂ)) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [EF.paperFT_tilde, Complex.conj_ofReal, map_mul]
  rw [hint, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

/-- **The tower pole term is a single hyperbolic pair.** -/
theorem towerPole_eq_pairKernel (g : ℝ → ℂ) (ℓ : ℝ) :
    towerPole g ℓ = pairKernel (valChar (Real.exp (ℓ / 2) : ℂ)) (poleWeight g) := by
  funext m
  set r : ℝ := Real.exp (ℓ / 2)
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have htilde : paperFT (EF.weilTest g g) (-I / 2) = conj (poleWeight g) := by
    have hc : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
    conv_lhs => rw [← RHTower.WeilSpectral.tilde_weilTest_self g]
    rw [EF.paperFT_tilde, hc, poleWeight]
  have hexp1 : cexp (I * (I / 2) * ((-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ : ℝ) : ℂ)) =
      valChar (r : ℂ) m := by
    have h1 : I * (I / 2) * ((-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ : ℝ) : ℂ) =
        (Multiplicative.toAdd m : ℤ) * ((ℓ / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [h1, Complex.exp_int_mul, ← Complex.ofReal_exp, valChar, dif_pos hr]
  have hexp2 : cexp (I * (-I / 2) * ((-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ : ℝ) : ℂ)) =
      reflectChar (valChar (r : ℂ)) m := by
    have h1 : I * (-I / 2) * ((-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ : ℝ) : ℂ) =
        (-(Multiplicative.toAdd m : ℤ) : ℤ) * ((ℓ / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [reflectChar_valChar hr, Complex.conj_ofReal, h1, Complex.exp_int_mul, ← Complex.ofReal_exp,
      valChar, dif_pos (inv_ne_zero hr), inv_zpow, ← zpow_neg]
  simp only [towerPole, RHTower.WeilSpectral.polePart, RHTower.WeilSpectral.paperFT_transl,
    htilde, hexp1, hexp2, pairKernel, poleWeight]
  ring

theorem isHermKernel_towerPole (g : ℝ → ℂ) (ℓ : ℝ) : IsHermKernel (towerPole g ℓ) := by
  rw [towerPole_eq_pairKernel]
  exact isHermKernel_pairKernel _ _

/-! ### Decay of the `S`-truncated prime and archimedean tower correlations -/

/-- Dominated-convergence decay of `towerPrime` for any `s = ½`-summable weight. -/
theorem tendsto_towerPrime_atTop {lam : ℕ → ℝ}
    (hsum : Summable fun n : ℕ => if 2 ≤ n then |lam n| / Real.sqrt n else 0)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun n : ℤ => towerPrime lam g ℓ (Multiplicative.ofAdd n)) atTop (𝓝 0) := by
  set K : ℝ → ℂ := EF.weilTest g g
  have hKc : Continuous K := (EF.weilTest_contDiff hg hg.continuous hgc).continuous
  have hKs : HasCompactSupport K := EF.weilTest_hasCompactSupport hgc hgc
  obtain ⟨R, hR⟩ := RHTower.WeilSpectral.exists_abs_bound_of_hasCompactSupport hKs
  obtain ⟨x₀, hx₀⟩ := hKc.norm.exists_forall_ge_of_hasCompactSupport hKs.norm
  set M : ℝ := ‖K x₀‖
  have hM : ∀ x, ‖K x‖ ≤ M := hx₀
  set b : ℕ → ℝ := fun k => (if 2 ≤ k then |lam k| / Real.sqrt k else 0) * (2 * M)
  have hb : Summable b := hsum.mul_right (2 * M)
  set F : ℤ → ℕ → ℂ := fun n k =>
    ((if 2 ≤ k then lam k / Real.sqrt k else 0 : ℝ) : ℂ) *
      (RHTower.WeilSpectral.transl (-(n : ℝ) * ℓ) K (Real.log k) +
        RHTower.WeilSpectral.transl (-(n : ℝ) * ℓ) K (-Real.log k))
  have hbd : ∀ n k, ‖F n k‖ ≤ b k := fun n k => by
    simp only [F, b, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcoeff : |if 2 ≤ k then lam k / Real.sqrt k else 0| =
        if 2 ≤ k then |lam k| / Real.sqrt k else 0 := by
      split_ifs with hk
      · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      · simp
    rw [hcoeff]
    refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> positivity)
    exact (norm_add_le _ _).trans (by linarith [hM (Real.log k - -(n : ℝ) * ℓ),
      hM (-Real.log k - -(n : ℝ) * ℓ)])
  have hlim : ∀ k : ℕ, Tendsto (fun n : ℤ => F n k) atTop (𝓝 0) := fun k => by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N₀, hN₀⟩ := exists_int_gt ((|R| + |Real.log k|) / ℓ)
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have hnℓ : |R| + |Real.log k| < (n : ℝ) * ℓ := by
      have h1 : (|R| + |Real.log k|) / ℓ < n := hN₀.trans_le (by exact_mod_cast hn)
      rwa [div_lt_iff₀ hℓ] at h1
    have hzero : ∀ x : ℝ, |R| < |x| → K x = 0 := fun x hx => by
      by_contra hne
      linarith [hR x hne, le_abs_self R]
    have h1 : RHTower.WeilSpectral.transl (-(n : ℝ) * ℓ) K (Real.log k) = 0 := by
      refine hzero _ ?_
      have htri := abs_sub_abs_le_abs_sub ((n : ℝ) * ℓ) (-Real.log k)
      rw [abs_of_pos (by linarith [abs_nonneg R, abs_nonneg (Real.log k)]), abs_neg] at htri
      rw [RHTower.WeilSpectral.transl, show Real.log k - -(n : ℝ) * ℓ =
        (n : ℝ) * ℓ - (-Real.log k) by ring]
      linarith
    have h2 : RHTower.WeilSpectral.transl (-(n : ℝ) * ℓ) K (-Real.log k) = 0 := by
      refine hzero _ ?_
      have htri := abs_sub_abs_le_abs_sub ((n : ℝ) * ℓ) (Real.log k)
      rw [abs_of_pos (by linarith [abs_nonneg R, abs_nonneg (Real.log k)])] at htri
      rw [RHTower.WeilSpectral.transl, show -Real.log k - -(n : ℝ) * ℓ =
        (n : ℝ) * ℓ - Real.log k by ring]
      linarith
    simp [F, h1, h2]
  have htsum := tendsto_tsum_of_dominated_convergence hb hlim (Eventually.of_forall hbd)
  simpa [F, towerPrime, RHTower.WeilSpectral.primePart] using htsum

/-- Decay of the Gamma correlation along any tower of positive step `ℓ > 0`. -/
theorem tendsto_towerArch_atTop (g : ℝ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun n : ℤ => towerArch g ℓ (Multiplicative.ofAdd n)) atTop (𝓝 0) := by
  have hy : Tendsto (fun n : ℤ => (n : ℝ) * ℓ) atTop atTop :=
    (tendsto_intCast_atTop_atTop).atTop_mul_const hℓ
  have hpos : Tendsto (fun n : ℤ =>
      RHTower.WeilSpectral.archPart (RHTower.WeilSpectral.transl ((n : ℝ) * ℓ) (EF.weilTest g g)))
      atTop (𝓝 0) :=
    RHTower.WeilSpectral.tendsto_archPart_transl.comp hy
  have hconj := (continuous_conj.tendsto 0).comp hpos
  rw [map_zero] at hconj
  refine hconj.congr fun n => ?_
  simp only [Function.comp_apply]
  have hh := isHermKernel_towerArch g ℓ (Multiplicative.ofAdd (-n))
  rw [← ofAdd_neg, neg_neg] at hh
  rw [← hh]
  simp [towerArch]

theorem tendsto_secondDiff_of_tendsto {k : Multiplicative ℤ → ℂ}
    (hk : Tendsto (fun n : ℤ => k (Multiplicative.ofAdd n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℤ => secondDiff k (Multiplicative.ofAdd n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℤ => k (Multiplicative.ofAdd n * Multiplicative.ofAdd 1))
      atTop (𝓝 0) := by
    have e : (fun n : ℤ => k (Multiplicative.ofAdd n * Multiplicative.ofAdd 1)) =
        fun n : ℤ => k (Multiplicative.ofAdd (n + 1)) := funext fun n => by rw [← ofAdd_add]
    rw [e]
    exact hk.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have h2 : Tendsto (fun n : ℤ => k (Multiplicative.ofAdd n * Multiplicative.ofAdd (-1)))
      atTop (𝓝 0) := by
    have e : (fun n : ℤ => k (Multiplicative.ofAdd n * Multiplicative.ofAdd (-1))) =
        fun n : ℤ => k (Multiplicative.ofAdd (n + -1)) := funext fun n => by rw [← ofAdd_add]
    rw [e]
    exact hk.comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  simpa [secondDiff] using ((hk.const_mul 2).sub h1).sub h2

/-! ### Local `S`-truncated explicit-formula kernels and their glued assemblies -/

/-- Local running counterterms `C + D·δ₁ + A·negAbsKernel` on a prime tower `ℤ`. -/
structure LocalCounterterm where
  constTerm : ℝ
  diagTerm : ℝ
  absTerm : ℝ

/-- Evaluation of a local running counterterm on `Multiplicative ℤ`. -/
def LocalCounterterm.eval (ct : LocalCounterterm) (m : Multiplicative ℤ) : ℂ :=
  (ct.constTerm : ℂ) + (if m = 1 then (ct.diagTerm : ℂ) else 0) +
    (ct.absTerm : ℂ) * negAbsKernel m

theorem LocalCounterterm.isHermKernel (ct : LocalCounterterm) : IsHermKernel ct.eval := fun m => by
  show ct.eval m⁻¹ = conj (ct.eval m)
  have h1 : m⁻¹ = 1 ↔ m = 1 := inv_eq_one
  simp only [LocalCounterterm.eval, h1, isHermKernel_negAbsKernel m, map_add, map_mul,
    Complex.conj_ofReal]
  split_ifs <;> simp

theorem LocalCounterterm.secondDiff_eq_zero_of_two_le (ct : LocalCounterterm) {n : ℤ}
    (hn : 2 ≤ n) : secondDiff ct.eval (Multiplicative.ofAdd n) = 0 := by
  have heq : ct.eval = fun m =>
      ((ct.constTerm : ℂ) + (if m = 1 then (ct.diagTerm : ℂ) else 0)) +
        (ct.absTerm : ℂ) * negAbsKernel m := funext fun _ => rfl
  rw [heq, secondDiff_add, secondDiff_add, secondDiff_const,
    secondDiff_deltaOne_of_two_le hn (ct.diagTerm : ℂ), secondDiff_const_mul,
    secondDiff_negAbsKernel_of_pos (by omega)]
  ring

theorem LocalCounterterm.tendsto_secondDiff_atTop (ct : LocalCounterterm) :
    Tendsto (fun n : ℤ => secondDiff ct.eval (Multiplicative.ofAdd n)) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℤ)] with n hn
  exact (ct.secondDiff_eq_zero_of_two_le hn).symm

/-- The non-pole part of a local `S`-truncated explicit-formula tower kernel at prime `p`:
`−wPrime · towerPrime_S + wArch · towerArch + counterterm`. -/
def sTruncatedNonPole (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ) (p : Nat.Primes)
    (wPrime wArch : ℝ) (ct : LocalCounterterm) (m : Multiplicative ℤ) : ℂ :=
  -(wPrime : ℂ) * towerPrime (truncWeight S lam) g (Real.log (p : ℕ)) m +
    (wArch : ℂ) * towerArch g (Real.log (p : ℕ)) m + ct.eval m

/-- The full local `S`-truncated explicit-formula tower kernel at prime `p`, combining pole share
`wPole`, `S`-truncated prime sum, Gamma integral, and running counterterm `ct`. -/
def sTruncatedLocal (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ) (p : Nat.Primes)
    (wPole wPrime wArch : ℝ) (ct : LocalCounterterm) (m : Multiplicative ℤ) : ℂ :=
  (wPole : ℂ) * towerPole g (Real.log (p : ℕ)) m +
    sTruncatedNonPole S lam g p wPrime wArch ct m

theorem isHermKernel_sTruncatedNonPole (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ)
    (p : Nat.Primes) (wPrime wArch : ℝ) (ct : LocalCounterterm) :
    IsHermKernel (sTruncatedNonPole S lam g p wPrime wArch ct) := fun m => by
  show sTruncatedNonPole S lam g p wPrime wArch ct m⁻¹ =
    conj (sTruncatedNonPole S lam g p wPrime wArch ct m)
  simp only [sTruncatedNonPole, isHermKernel_towerPrime _ _ _ m, isHermKernel_towerArch _ _ m,
    ct.isHermKernel m, map_add, map_mul, map_neg, Complex.conj_ofReal]

theorem isHermKernel_sTruncatedLocal (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ)
    (p : Nat.Primes) (wPole wPrime wArch : ℝ) (ct : LocalCounterterm) :
    IsHermKernel (sTruncatedLocal S lam g p wPole wPrime wArch ct) := fun m => by
  show sTruncatedLocal S lam g p wPole wPrime wArch ct m⁻¹ =
    conj (sTruncatedLocal S lam g p wPole wPrime wArch ct m)
  simp only [sTruncatedLocal, isHermKernel_towerPole _ _ m,
    isHermKernel_sTruncatedNonPole _ _ _ _ _ _ _ m, map_add, map_mul, Complex.conj_ofReal]

theorem sTruncatedLocal_eq_pairKernel_add (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ)
    (p : Nat.Primes) (wPole wPrime wArch : ℝ) (ct : LocalCounterterm) :
    sTruncatedLocal S lam g p wPole wPrime wArch ct =
      fun m => pairKernel (valChar (Real.exp (Real.log (p : ℕ) / 2) : ℂ))
        ((wPole : ℂ) * poleWeight g) m + sTruncatedNonPole S lam g p wPrime wArch ct m := by
  funext m
  simp only [sTruncatedLocal, towerPole_eq_pairKernel, pairKernel, map_mul, Complex.conj_ofReal]
  ring

theorem tendsto_secondDiff_sTruncatedNonPole (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (p : Nat.Primes)
    (wPrime wArch : ℝ) (ct : LocalCounterterm) :
    Tendsto (fun n : ℤ =>
      secondDiff (sTruncatedNonPole S lam g p wPrime wArch ct) (Multiplicative.ofAdd n))
      atTop (𝓝 0) := by
  have hℓ : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hp_lim := tendsto_towerPrime_atTop (summable_truncWeight_div_sqrt S hlam) hg hgc hℓ
  have ha_lim := tendsto_towerArch_atTop g hℓ
  have hsd1 := tendsto_secondDiff_of_tendsto (hp_lim.const_mul (-(wPrime : ℂ)))
  have hsd2 := tendsto_secondDiff_of_tendsto (ha_lim.const_mul (wArch : ℂ))
  rw [mul_zero] at hsd1 hsd2
  have hsum := (hsd1.add hsd2).add ct.tendsto_secondDiff_atTop
  rw [add_zero, add_zero] at hsum
  refine hsum.congr fun n => ?_
  have heq : sTruncatedNonPole S lam g p wPrime wArch ct = fun m =>
      (-(wPrime : ℂ) * towerPrime (truncWeight S lam) g (Real.log (p : ℕ)) m +
        (wArch : ℂ) * towerArch g (Real.log (p : ℕ)) m) + ct.eval m := funext fun _ => rfl
  rw [heq, secondDiff_add, secondDiff_add]
  rfl

/-- **Polar trichotomy of a local `S`-truncated explicit-formula kernel.** -/
theorem polarIndex_sTruncatedLocal (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (p : Nat.Primes)
    (wPole wPrime wArch : ℝ) (ct : LocalCounterterm) :
    (¬ IsPosDefKernel (secondDiff (sTruncatedNonPole S lam g p wPrime wArch ct)) →
        polarIndex (sTruncatedLocal S lam g p wPole wPrime wArch ct) = ⊤) ∧
      (IsPosDefKernel (secondDiff (sTruncatedNonPole S lam g p wPrime wArch ct)) →
        (wPole : ℂ) * poleWeight g = 0 →
        polarIndex (sTruncatedLocal S lam g p wPole wPrime wArch ct) = 0) ∧
      (IsPosDefKernel (secondDiff (sTruncatedNonPole S lam g p wPrime wArch ct)) →
        (wPole : ℂ) * poleWeight g ≠ 0 →
        polarIndex (sTruncatedLocal S lam g p wPole wPrime wArch ct) = 1) := by
  have hr : 1 < Real.exp (Real.log (p : ℕ) / 2) := by
    have hℓ : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
    exact Real.one_lt_exp_iff.mpr (by linarith)
  rw [sTruncatedLocal_eq_pairKernel_add]
  exact polarIndex_pairKernel_add_of_secondDiff_tendsto hr ((wPole : ℂ) * poleWeight g)
    (isHermKernel_sTruncatedNonPole S lam g p wPrime wArch ct)
    (tendsto_secondDiff_sTruncatedNonPole S hlam hg hgc p wPrime wArch ct)

/-- Separable prime-tower assembly built from local `S`-truncated explicit-formula tower kernels. -/
def sTruncatedAssembly (S : Finset Nat.Primes) (lam : ℕ → ℝ) (g : ℝ → ℂ)
    (wPole wPrime wArch : S → ℝ) (ct : S → LocalCounterterm) : posUnits → ℂ :=
  towerAssembly S fun p =>
    sTruncatedLocal S lam g (p : Nat.Primes) (wPole p) (wPrime p) (wArch p) (ct p)

/-- **Glued signature classification and zero-blindness.** For every separable `S`-truncated
explicit-formula assembly and `c > 0`, either some local non-pole second difference fails positive
definiteness and `κ(archGlue(K_S, c)) = ⊤`, or every local polar index `κ₀ ∈ {0, 1}` counts only
whether `wPole p · poleWeight g ≠ 0` and `κ(archGlue(K_S, c)) ∈ {r_S + 1, r_S + 2}`. -/
theorem negIndex_archGlue_sTruncatedAssembly (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (wPole wPrime wArch : S → ℝ) (ct : S → LocalCounterterm) {c : ℝ} (hc : 0 < c) :
    ((∃ p : S, ¬ IsPosDefKernel
        (secondDiff (sTruncatedNonPole S lam g (p : Nat.Primes) (wPrime p) (wArch p) (ct p)))) ∧
      negIndex (archGlue (sTruncatedAssembly S lam g wPole wPrime wArch ct) c) = ⊤) ∨
    ((∀ p : S, IsPosDefKernel
        (secondDiff (sTruncatedNonPole S lam g (p : Nat.Primes) (wPrime p) (wArch p) (ct p)))) ∧
      (∑ p : S, polarIndex (sTruncatedLocal S lam g (p : Nat.Primes)
          (wPole p) (wPrime p) (wArch p) (ct p)) =
        ((univ.filter fun p : S => (wPole p : ℂ) * poleWeight g ≠ 0).card : ℕ∞)) ∧
      (negIndex (archGlue (sTruncatedAssembly S lam g wPole wPrime wArch ct) c) =
          ((univ.filter fun p : S => (wPole p : ℂ) * poleWeight g ≠ 0).card : ℕ∞) + 1 ∨
        negIndex (archGlue (sTruncatedAssembly S lam g wPole wPrime wArch ct) c) =
          ((univ.filter fun p : S => (wPole p : ℂ) * poleWeight g ≠ 0).card : ℕ∞) + 2)) := by
  classical
  have hk : ∀ p : S, IsHermKernel
      (sTruncatedLocal S lam g (p : Nat.Primes) (wPole p) (wPrime p) (wArch p) (ct p)) :=
    fun p => isHermKernel_sTruncatedLocal S lam g (p : Nat.Primes) (wPole p) (wPrime p) (wArch p)
      (ct p)
  have hlo := towerSignature_lower S hk hc
  have hhi := towerSignature_upper S hk hc
  by_cases hall : ∀ p : S, IsPosDefKernel
      (secondDiff (sTruncatedNonPole S lam g (p : Nat.Primes) (wPrime p) (wArch p) (ct p)))
  · right
    set rS : ℕ := (univ.filter fun p : S => (wPole p : ℂ) * poleWeight g ≠ 0).card
    have hsum : ∑ p : S, polarIndex (sTruncatedLocal S lam g (p : Nat.Primes)
        (wPole p) (wPrime p) (wArch p) (ct p)) = (rS : ℕ∞) := by
      have hp : ∀ p : S, polarIndex (sTruncatedLocal S lam g (p : Nat.Primes)
          (wPole p) (wPrime p) (wArch p) (ct p)) =
          if (wPole p : ℂ) * poleWeight g ≠ 0 then 1 else 0 := fun p => by
        obtain ⟨_, h0, h1⟩ := polarIndex_sTruncatedLocal S hlam hg hgc (p : Nat.Primes)
          (wPole p) (wPrime p) (wArch p) (ct p)
        by_cases hw : (wPole p : ℂ) * poleWeight g ≠ 0
        · rw [if_pos hw, h1 (hall p) hw]
        · push Not at hw
          rw [if_neg (not_not.mpr hw), h0 (hall p) hw]
      simp_rw [hp]
      rw [Finset.sum_boole]
      rfl
    refine ⟨hall, hsum, ?_⟩
    change _ at hlo hhi
    rw [sTruncatedAssembly]
    rw [hsum] at hlo hhi
    generalize negIndex (archGlue (towerAssembly S fun p =>
      sTruncatedLocal S lam g (p : Nat.Primes) (wPole p) (wPrime p) (wArch p) (ct p)) c) = x
      at hlo hhi ⊢
    induction x using ENat.recTopCoe with
    | top =>
      exact absurd (top_le_iff.mp hhi) (by exact_mod_cast ENat.coe_ne_top (rS + 2))
    | coe n =>
      have hlo' : rS + 1 ≤ n := by exact_mod_cast hlo
      have hhi' : n ≤ rS + 2 := by exact_mod_cast hhi
      rcases (show n = rS + 1 ∨ n = rS + 2 by omega) with rfl | rfl
      · exact Or.inl (by push_cast; rfl)
      · exact Or.inr (by push_cast; rfl)
  · left
    push Not at hall
    obtain ⟨p₀, hp₀⟩ := hall
    refine ⟨⟨p₀, hp₀⟩, top_le_iff.mp ?_⟩
    have htop := (polarIndex_sTruncatedLocal S hlam hg hgc (p₀ : Nat.Primes)
      (wPole p₀) (wPrime p₀) (wArch p₀) (ct p₀)).1 hp₀
    have hle : polarIndex (sTruncatedLocal S lam g (p₀ : Nat.Primes)
        (wPole p₀) (wPrime p₀) (wArch p₀) (ct p₀)) ≤
        ∑ p : S, polarIndex (sTruncatedLocal S lam g (p : Nat.Primes)
          (wPole p) (wPrime p) (wArch p) (ct p)) :=
      single_le_sum (fun _ _ => zero_le _) (mem_univ p₀)
    rw [htop, top_le_iff] at hle
    rw [sTruncatedAssembly]
    calc (⊤ : ℕ∞) = ⊤ + 1 := rfl
      _ = ∑ p : S, polarIndex (sTruncatedLocal S lam g (p : Nat.Primes)
            (wPole p) (wPrime p) (wArch p) (ct p)) + 1 := by rw [hle]
      _ ≤ _ := hlo

/-! ### Unconditional divergence of pole-retaining assemblies -/

/-- **Pole-retaining lower bound.** If every prime in `S` carries a nonzero pole share for the
cubic spline, then `|S| + 1 ≤ κ(archGlue(K_S, c))` unconditionally for all running counterterms. -/
theorem card_add_one_le_negIndex_archGlue_poleRetaining (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {wPole : S → ℝ} (hwPole : ∀ p : S, wPole p ≠ 0) (wPrime wArch : S → ℝ)
    (ct : S → LocalCounterterm) {c : ℝ} (hc : 0 < c) :
    (S.card : ℕ∞) + 1 ≤
      negIndex (archGlue (sTruncatedAssembly S lam (cx cubicSpline) wPole wPrime wArch ct) c) := by
  have hg := cx_contDiff contDiff_cubicSpline
  have hgc := cx_hasCompactSupport hasCompactSupport_cubicSpline
  rcases negIndex_archGlue_sTruncatedAssembly S hlam hg hgc wPole wPrime wArch ct hc with
    ⟨_, htop⟩ | ⟨_, _, hmem⟩
  · rw [htop]; exact le_top
  · have hcard : (univ.filter fun p : S =>
        (wPole p : ℂ) * poleWeight (cx cubicSpline) ≠ 0).card = S.card := by
      have hfilt : (univ.filter fun p : S =>
          (wPole p : ℂ) * poleWeight (cx cubicSpline) ≠ 0) = univ := by
        ext p
        simp only [mem_filter, mem_univ, true_and]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hwPole p)) poleWeight_cubicSpline_ne_zero
      rw [hfilt, Finset.card_univ, Fintype.card_coe]
    rw [hcard] at hmem
    rcases hmem with h1 | h2
    · rw [h1]
    · rw [h2]; gcongr; norm_num

/-- **Pole-retaining unconditional divergence.** Along the directed family `atTop` of finite prime
sets `S`, the glued negative index of any pole-retaining cubic-spline assembly tends to `⊤`. -/
theorem tendsto_negIndex_archGlue_poleRetaining_atTop
    {lam : Finset Nat.Primes → ℕ → ℝ}
    (hlam : ∀ S, ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam S ((q : ℕ) ^ k)| ≤ C)
    {wPole : (S : Finset Nat.Primes) → S → ℝ} (hwPole : ∀ S p, wPole S p ≠ 0)
    (wPrime wArch : (S : Finset Nat.Primes) → S → ℝ)
    (ct : (S : Finset Nat.Primes) → S → LocalCounterterm) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun S => negIndex
      (archGlue (sTruncatedAssembly S (lam S) (cx cubicSpline)
        (wPole S) (wPrime S) (wArch S) (ct S)) c)) atTop (𝓝 ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_nat]
  intro m
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset Nat.Primes, m ≤ S₀.card := by
    have hinf : (Set.univ : Set Nat.Primes).Infinite := Set.infinite_univ_iff.mpr
      ⟨Nat.infinite_setOf_prime.to_subtype⟩
    obtain ⟨S₀, _, hcard⟩ := hinf.exists_subset_card_eq m
    exact ⟨S₀, hcard.ge⟩
  filter_upwards [eventually_ge_atTop S₀] with S hS
  have hm : (m : ℕ∞) ≤ (S.card : ℕ∞) := Nat.cast_le.mpr (hS₀.trans (Finset.card_le_card hS))
  exact hm.trans ((le_self_add (a := (S.card : ℕ∞)) (b := 1)).trans
    (card_add_one_le_negIndex_archGlue_poleRetaining S (hlam S) (hwPole S)
      (wPrime S) (wArch S) (ct S) hc))

/-! ### Pole-free spectral gap, diagonal counterterms, and twin-flip blindness -/

/-- **Pole-free glued values.** When every local pole share is zero, the glued negative index lies
in `{1, 2, ⊤}` for every `S` and all local counterterms. -/
theorem negIndex_archGlue_poleFree_mem (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (wPrime wArch : S → ℝ) (ct : S → LocalCounterterm) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (sTruncatedAssembly S lam g (fun _ => 0) wPrime wArch ct) c) ∈
      ({1, 2, ⊤} : Set ℕ∞) := by
  rcases negIndex_archGlue_sTruncatedAssembly S hlam hg hgc (fun _ => 0) wPrime wArch ct hc with
    ⟨_, htop⟩ | ⟨_, _, hmem⟩
  · simp [htop]
  · have hfilt : (univ.filter fun _ : S => ((0 : ℝ) : ℂ) * poleWeight g ≠ 0) = ∅ := by simp
    rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_add, zero_add] at hmem
    rcases hmem with h1 | h2 <;> simp [h1, h2]

/-- **Unconditional parity gap of Weil's archimedean state.** Because `κ(K_ζ)` is even
(`negIndex_zetaKernel_le_one_iff`), `κ(weilArchState c) = κ(K_ζ) + 1` is never `2`: it is `1` (under
RH) or at least `3`. -/
theorem negIndex_weilArchState_ne_two {c : ℝ} (hc : 0 < c) :
    negIndex (weilArchState c) ≠ 2 := by
  rw [negIndex_weilArchState_eq_add_one hc]
  intro h
  have h1 : negIndex zetaKernel ≤ 1 := by
    have : negIndex zetaKernel + 1 ≤ (1 : ℕ∞) + 1 := by rw [h]; norm_num
    exact WithTop.le_of_add_le_add_right (ENat.coe_ne_top 1) this
  have h0 := negIndex_zetaKernel_le_one_iff.mp h1
  rw [h0] at h
  norm_num at h

/-- On the non-RH finite stratum `0 < κ(K_ζ) < ⊤`, no net of pole-free `S`-truncated assemblies
converges in glued negative index to `κ(weilArchState c) = κ(K_ζ) + 1`. -/
theorem not_tendsto_negIndex_archGlue_poleFree_of_finite_pos {ι : Type*} {l : Filter ι} [l.NeBot]
    (S : ι → Finset Nat.Primes) {lam : ι → ℕ → ℝ}
    (hlam : ∀ i, ∀ q ∈ S i, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam i ((q : ℕ) ^ k)| ≤ C)
    {g : ι → ℝ → ℂ} (hg : ∀ i, ContDiff ℝ 2 (g i)) (hgc : ∀ i, HasCompactSupport (g i))
    (wPrime wArch : (i : ι) → S i → ℝ) (ct : (i : ι) → S i → LocalCounterterm)
    {c : ℝ} (hc : 0 < c) (hpos : 0 < negIndex zetaKernel) (hfin : negIndex zetaKernel < ⊤) :
    ¬ Tendsto (fun i => negIndex
        (archGlue (sTruncatedAssembly (S i) (lam i) (g i) (fun _ => 0)
          (wPrime i) (wArch i) (ct i)) c))
      l (𝓝 (negIndex (weilArchState c))) := by
  intro htend
  obtain ⟨m, hm_top, hm_eq⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hmle1 : negIndex zetaKernel ≤ 1 := by
      rw [← hm_eq]; exact Nat.cast_le.mpr (by omega)
    have h0 := negIndex_zetaKernel_le_one_iff.mp hmle1
    exact hpos.ne' h0
  have hstate : negIndex (weilArchState c) = ((m + 1 : ℕ) : ℕ∞) := by
    rw [negIndex_weilArchState_eq_add_one hc, ← hm_eq]; rfl
  rw [hstate] at htend
  have hnhds : ({((m + 1 : ℕ) : ℕ∞)} : Set ℕ∞) ∈ 𝓝 ((m + 1 : ℕ) : ℕ∞) :=
    (ENat.isOpen_singleton (ENat.coe_ne_top (m + 1))).mem_nhds rfl
  have hev := htend.eventually hnhds
  obtain ⟨i, hi⟩ := hev.exists
  have hmem := negIndex_archGlue_poleFree_mem (S i) (hlam i) (hg i) (hgc i) (wPrime i) (wArch i)
    (ct i) hc
  rw [Set.mem_singleton_iff.mp hi] at hmem
  rcases hmem with h | h | h
  · have : m + 1 = 1 := Nat.cast_injective h; omega
  · have : m + 1 = 2 := Nat.cast_injective h; omega
  · exact ENat.coe_ne_top (m + 1) h

/-! ### Explicit diagonal counterterm positivity and unconditional twin-flip obstruction -/

/-- Schur bound for an `ℓ¹` kernel on a finite set of distinct group elements. -/
theorem abs_hermQuad_gram_le_tsum_norm {G : Type*} [Group G] [DecidableEq G] {h : G → ℂ}
    (hh : Summable fun m : G => ‖h m‖) (s : Finset G) (w : s → ℂ) :
    |hermQuad (gram h fun z : s => (z : G)) w| ≤
      (∑' m : G, ‖h m‖) * ∑ i : s, ‖w i‖ ^ 2 := by
  rw [hermQuad_gram]
  calc |(∑ i : s, ∑ j : s, conj (w i) * h (((i : G))⁻¹ * (j : G)) * w j).re|
      ≤ ‖∑ i : s, ∑ j : s, conj (w i) * h (((i : G))⁻¹ * (j : G)) * w j‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ i : s, ∑ j : s, ‖conj (w i) * h (((i : G))⁻¹ * (j : G)) * w j‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i : s, ∑ j : s, (‖w i‖ * ‖w j‖) * ‖h (((i : G))⁻¹ * (j : G))‖ := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]; ring
    _ ≤ ∑ i : s, ∑ j : s, ((‖w i‖ ^ 2 + ‖w j‖ ^ 2) / 2) * ‖h (((i : G))⁻¹ * (j : G))‖ := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        nlinarith [sq_nonneg (‖w i‖ - ‖w j‖)]
    _ = (∑ i : s, ‖w i‖ ^ 2 * ∑ j : s, ‖h (((i : G))⁻¹ * (j : G))‖) / 2 +
          (∑ j : s, ‖w j‖ ^ 2 * ∑ i : s, ‖h (((i : G))⁻¹ * (j : G))‖) / 2 := by
        have hsplit : ∀ i j : s,
            ((‖w i‖ ^ 2 + ‖w j‖ ^ 2) / 2) * ‖h (((i : G))⁻¹ * (j : G))‖ =
              (‖w i‖ ^ 2 * ‖h (((i : G))⁻¹ * (j : G))‖) / 2 +
                (‖w j‖ ^ 2 * ‖h (((i : G))⁻¹ * (j : G))‖) / 2 := fun _ _ => by ring
        simp_rw [hsplit, sum_add_distrib, ← sum_div]
        congr 1
        · congr 1; exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
        · congr 1
          rw [Finset.sum_comm]
          exact sum_congr rfl fun j _ => (mul_sum _ _ _).symm
    _ ≤ ((∑ i : s, ‖w i‖ ^ 2 * ∑' m : G, ‖h m‖) / 2) +
          ((∑ j : s, ‖w j‖ ^ 2 * ∑' m : G, ‖h m‖) / 2) := by
        have hrow : ∀ i : s, ∑ j : s, ‖h (((i : G))⁻¹ * (j : G))‖ ≤ ∑' m : G, ‖h m‖ := fun i => by
          let f : s ↪ G := ⟨fun j => ((i : G))⁻¹ * (j : G), fun j₁ j₂ h =>
            Subtype.ext (mul_left_cancel h)⟩
          rw [← Finset.sum_map univ f (fun m => ‖h m‖)]
          exact hh.sum_le_tsum _ fun _ _ => norm_nonneg _
        have hcol : ∀ j : s, ∑ i : s, ‖h (((i : G))⁻¹ * (j : G))‖ ≤ ∑' m : G, ‖h m‖ := fun j => by
          let f : s ↪ G := ⟨fun i => ((i : G))⁻¹ * (j : G), fun i₁ i₂ h => by
            have := mul_right_cancel h
            exact Subtype.ext (inv_injective this)⟩
          rw [← Finset.sum_map univ f (fun m => ‖h m‖)]
          exact hh.sum_le_tsum _ fun _ _ => norm_nonneg _
        gcongr
        · exact mul_le_mul_of_nonneg_left (hrow _) (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hcol _) (sq_nonneg _)
    _ = (∑' m : G, ‖h m‖) * ∑ i : s, ‖w i‖ ^ 2 := by
        simp_rw [← sum_mul]
        ring

/-- For compactly supported `K` and `ℓ > 0`, `m ↦ ‖K(x + mℓ)‖` has uniformly bounded `ℓ¹(ℤ)` norm
with respect to `x ∈ ℝ`. -/
private theorem sum_norm_shift_le {K : ℝ → ℂ} {R M : ℝ} (hR : ∀ u, K u ≠ 0 → |u| ≤ R)
    (hM : ∀ u, ‖K u‖ ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) (t : Finset (Multiplicative ℤ)) :
    ∑ m ∈ t, ‖K (x + (Multiplicative.toAdd m : ℝ) * ℓ)‖ ≤
      M * (2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg (K 0)).trans (hM 0)
  set N : ℤ := ⌈|R| / ℓ⌉₊ + 1
  set a : ℤ := ⌊-x / ℓ⌋ - N
  set b : ℤ := ⌊-x / ℓ⌋ + N
  set J : Finset (Multiplicative ℤ) := (Icc a b).map
    ⟨Multiplicative.ofAdd, Multiplicative.ofAdd.injective⟩
  have hvan : ∀ m ∈ t, m ∉ J → ‖K (x + (Multiplicative.toAdd m : ℝ) * ℓ)‖ = 0 := by
    intro m _ hmJ
    rw [norm_eq_zero]
    by_contra hne
    have habs := hR _ hne
    have hdiv : |x / ℓ + (Multiplicative.toAdd m : ℝ)| ≤ |R| / ℓ := by
      have heq : x / ℓ + (Multiplicative.toAdd m : ℝ) =
          (x + (Multiplicative.toAdd m : ℝ) * ℓ) / ℓ := by field_simp
      rw [heq, abs_div, abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right (habs.trans (le_abs_self R)) hℓ.le
    have hN : |R| / ℓ < (N : ℝ) := by
      simp only [N]; push_cast
      linarith [Nat.le_ceil (|R| / ℓ)]
    have hfl1 := Int.floor_le (-x / ℓ)
    have hfl2 := Int.lt_floor_add_one (-x / ℓ)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdiv
    have hma : a ≤ Multiplicative.toAdd m := by
      have : (a : ℝ) < (Multiplicative.toAdd m : ℝ) + 1 := by
        simp only [a]; push_cast; linarith [show -x / ℓ = -(x / ℓ) by ring]
      exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    have hmb : Multiplicative.toAdd m ≤ b := by
      have : (Multiplicative.toAdd m : ℝ) < (b : ℝ) + 1 := by
        simp only [b]; push_cast; linarith [show -x / ℓ = -(x / ℓ) by ring]
      exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
    exact hmJ (Finset.mem_map.mpr ⟨Multiplicative.toAdd m, mem_Icc.mpr ⟨hma, hmb⟩, ofAdd_toAdd m⟩)
  have hsub : ∑ m ∈ t, ‖K (x + (Multiplicative.toAdd m : ℝ) * ℓ)‖ =
      ∑ m ∈ t.filter (· ∈ J), ‖K (x + (Multiplicative.toAdd m : ℝ) * ℓ)‖ := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun m hm => ?_
    split_ifs with h
    · rfl
    · exact hvan m hm h
  have hcard : ((t.filter (· ∈ J)).card : ℝ) ≤ 2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3 := by
    have hle1 : (t.filter (· ∈ J)).card ≤ J.card :=
      Finset.card_le_card fun m hm => (mem_filter.mp hm).2
    have hle2 : J.card = (Icc a b).card := Finset.card_map _
    have hle3 : ((Icc a b).card : ℝ) ≤ (b : ℝ) + 1 - a := by
      rw [Int.card_Icc]
      have hpos : 0 ≤ b + 1 - a := by simp only [a, b, N]; omega
      have htn : ((b + 1 - a).toNat : ℤ) = b + 1 - a := Int.toNat_of_nonneg hpos
      have hc : (((b + 1 - a).toNat : ℕ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast htn
      rw [hc]; push_cast; linarith
    calc ((t.filter (· ∈ J)).card : ℝ) ≤ (J.card : ℝ) := Nat.cast_le.mpr hle1
      _ = ((Icc a b).card : ℝ) := by rw [hle2]
      _ ≤ (b : ℝ) + 1 - a := hle3
      _ = 2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3 := by simp only [a, b, N]; push_cast; ring
  rw [hsub]
  calc ∑ m ∈ t.filter (· ∈ J), ‖K (x + (Multiplicative.toAdd m : ℝ) * ℓ)‖
      ≤ ∑ _m ∈ t.filter (· ∈ J), M := sum_le_sum fun m _ => hM _
    _ = ((t.filter (· ∈ J)).card : ℝ) * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3) * M := mul_le_mul_of_nonneg_right hcard hM0
    _ = M * (2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3) := mul_comm _ _

/-- `towerPrime` of an `S`-truncated weight lies in `ℓ¹(ℤ)`. -/
theorem summable_norm_towerPrime_truncWeight (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable fun m : Multiplicative ℤ => ‖towerPrime (truncWeight S lam) g ℓ m‖ := by
  set K : ℝ → ℂ := EF.weilTest g g
  have hKc : Continuous K := (EF.weilTest_contDiff hg hg.continuous hgc).continuous
  have hKs : HasCompactSupport K := EF.weilTest_hasCompactSupport hgc hgc
  obtain ⟨R, hR⟩ := RHTower.WeilSpectral.exists_abs_bound_of_hasCompactSupport hKs
  obtain ⟨x₀, hx₀⟩ := hKc.norm.exists_forall_ge_of_hasCompactSupport hKs.norm
  set M : ℝ := ‖K x₀‖
  set W : ℝ := 2 * M * (2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3)
  set c : ℕ → ℝ := fun n => if 2 ≤ n then |truncWeight S lam n| / Real.sqrt n else 0
  have hc : Summable c := summable_truncWeight_div_sqrt S hlam
  refine summable_of_sum_le (fun _ => norm_nonneg _) (c := (∑' n, c n) * W) fun t => ?_
  have hpt : ∀ m : Multiplicative ℤ, ‖towerPrime (truncWeight S lam) g ℓ m‖ ≤
      ∑' n : ℕ, c n * (‖K (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖ +
        ‖K (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖) := fun m => by
    have hsum_m : Summable fun n : ℕ =>
        c n * (‖K (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖ +
          ‖K (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖) := by
      refine (hc.mul_right (2 * M)).of_nonneg_of_le (fun n => by
        refine mul_nonneg ?_ (by positivity)
        simp only [c]; split_ifs <;> positivity) fun n => ?_
      refine mul_le_mul_of_nonneg_left ?_ (by simp only [c]; split_ifs <;> positivity)
      linarith [hx₀ (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ),
        hx₀ (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · refine hsum_m.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hcn : |if 2 ≤ n then truncWeight S lam n / Real.sqrt n else 0| = c n := by
        simp only [c]; split_ifs with hn
        · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
        · simp
      rw [hcn, RHTower.WeilSpectral.transl, RHTower.WeilSpectral.transl,
        show Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
          Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring,
        show -Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
          -Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
        (by simp only [c]; split_ifs <;> positivity)
    · refine hsum_m.tsum_mono (hsum_m.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_)
        fun n => ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hcn : |if 2 ≤ n then truncWeight S lam n / Real.sqrt n else 0| = c n := by
          simp only [c]; split_ifs with hn
          · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          · simp
        rw [hcn, RHTower.WeilSpectral.transl, RHTower.WeilSpectral.transl,
          show Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
            Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring,
          show -Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
            -Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (by simp only [c]; split_ifs <;> positivity)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hcn : |if 2 ≤ n then truncWeight S lam n / Real.sqrt n else 0| = c n := by
          simp only [c]; split_ifs with hn
          · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          · simp
        rw [hcn, RHTower.WeilSpectral.transl, RHTower.WeilSpectral.transl,
          show Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
            Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring,
          show -Real.log n - -((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ =
            -Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ by ring]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (by simp only [c]; split_ifs <;> positivity)
  have hsum_n : ∀ m ∈ t, Summable fun n : ℕ =>
      c n * (‖K (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖ +
        ‖K (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖) := fun m _ => by
    refine (hc.mul_right (2 * M)).of_nonneg_of_le
      (fun n => mul_nonneg (by simp only [c]; split_ifs <;> positivity) (by positivity)) fun n =>
      mul_le_mul_of_nonneg_left (by linarith [hx₀ (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ),
        hx₀ (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)])
        (by simp only [c]; split_ifs <;> positivity)
  calc ∑ m ∈ t, ‖towerPrime (truncWeight S lam) g ℓ m‖
      ≤ ∑ m ∈ t, ∑' n : ℕ, c n * (‖K (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖ +
          ‖K (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖) :=
        sum_le_sum fun m _ => hpt m
    _ = ∑' n : ℕ, ∑ m ∈ t, c n * (‖K (Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖ +
          ‖K (-Real.log n + (Multiplicative.toAdd m : ℝ) * ℓ)‖) :=
        (Summable.tsum_finsetSum hsum_n).symm
    _ ≤ ∑' n : ℕ, c n * W := by
        refine (Summable.sum fun m hm => hsum_n m hm).tsum_le_tsum (fun n => ?_) (hc.mul_right W)
        rw [← mul_sum, sum_add_distrib]
        refine mul_le_mul_of_nonneg_left ?_ (by simp only [c]; split_ifs <;> positivity)
        have h1 := sum_norm_shift_le hR hx₀ hℓ (Real.log n) t
        have h2 := sum_norm_shift_le hR hx₀ hℓ (-Real.log n) t
        simp only [W]; linarith
    _ = (∑' n, c n) * W := tsum_mul_right

/-- **Explicit diagonal counterterm positivity.** For every finite prime set `S`, tower-bounded
weight `lam`, `C²` compactly supported `g`, `p ∈ Nat.Primes`, and `wPrime : ℝ`, there exists `D₀`
such that for all `D ≥ D₀`, the pole-free local kernel with Gamma weight `1` and diagonal
counterterm `D·δ₁` is positive definite on `ℤ` (`negIndex = 0`, `polarIndex = 0`). -/
theorem exists_diagonal_counterterm_posDef (S : Finset Nat.Primes) {lam : ℕ → ℝ}
    (hlam : ∀ q ∈ S, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → |lam ((q : ℕ) ^ k)| ≤ C)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (p : Nat.Primes) (wPrime : ℝ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      IsPosDefKernel (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩) ∧
      polarIndex (sTruncatedLocal S lam g p 0 wPrime 1 ⟨0, D, 0⟩) = 0 := by
  set ℓ : ℝ := Real.log (p : ℕ)
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast p.2.one_lt)
  set K : ℝ → ℂ := EF.weilTest g g
  have hKc : Continuous K := (EF.weilTest_contDiff hg hg.continuous hgc).continuous
  have hKs : HasCompactSupport K := EF.weilTest_hasCompactSupport hgc hgc
  obtain ⟨R, hR⟩ := RHTower.WeilSpectral.exists_abs_bound_of_hasCompactSupport hKs
  obtain ⟨x₀, hx₀⟩ := hKc.norm.exists_forall_ge_of_hasCompactSupport hKs.norm
  set k₀ : Multiplicative ℤ → ℂ := fun m => K (-((Multiplicative.toAdd m : ℤ) : ℝ) * ℓ)
  have hk₀_sum : Summable fun m : Multiplicative ℤ => ‖k₀ m‖ := by
    refine summable_of_sum_le (fun _ => norm_nonneg _)
      (c := ‖K x₀‖ * (2 * (⌈|R| / ℓ⌉₊ : ℝ) + 3)) fun t => ?_
    have h := sum_norm_shift_le (K := fun u => K (-u))
      (fun u hu => by simpa using hR (-u) hu) (fun u => hx₀ (-u)) hℓ 0 t
    refine le_trans ?_ h
    refine sum_le_sum fun m _ => ?_
    simp only [k₀, zero_add]
    exact le_of_eq (by congr 2; ring)
  have hp_sum := summable_norm_towerPrime_truncWeight S hlam hg hgc hℓ
  set D₀ : ℝ := 10 * (∑' m, ‖k₀ m‖) + |wPrime| * ∑' m, ‖towerPrime (truncWeight S lam) g ℓ m‖
  refine ⟨D₀, fun D hD => ?_⟩
  have hherm := isHermKernel_sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩
  have hpd : IsPosDefKernel (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩) := by
    rw [isPosDefKernel_iff hherm]
    refine nonpos_iff_eq_zero.mp (negIndex_le_of_finset _ fun s => ?_)
    rw [Nat.cast_le_zero]
    by_contra hne
    obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex
      (-gram (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩) fun z : s => (z : Multiplicative ℤ))
    have hWpos : 0 < Module.finrank ℂ W := by rw [← hWr]; exact Nat.pos_of_ne_zero hne
    set bW := Module.finBasis ℂ W
    set v : W := bW ⟨0, hWpos⟩
    have hv0 : (v : s → ℂ) ≠ 0 := fun h => bW.ne_zero ⟨0, hWpos⟩ (Subtype.ext h)
    have hneg : hermQuad (gram (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩)
        (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) < 0 := by
      have := hW _ v.2 hv0; rw [hermQuad_neg] at this; linarith
    -- Evaluate the archimedean form as a packet Gamma integral
    set e := Fintype.equivFin s
    set w : Fin (Fintype.card s) → ℂ := fun i => (v : s → ℂ) (e.symm i)
    set t : Fin (Fintype.card s) → ℝ := fun i =>
      (Multiplicative.toAdd ((e.symm i : s) : Multiplicative ℤ) : ℝ) * ℓ
    set G : ℝ → ℂ := ∑ j, w j • RHTower.WeilSpectral.transl (t j) g
    have hGc : ContDiff ℝ 2 G := by
      have heq : G = fun x => ∑ j, w j * g (x - t j) := funext fun x => by
        simp [G, Finset.sum_apply, RHTower.WeilSpectral.transl]
      rw [heq]
      exact ContDiff.sum fun j _ => contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))
    have hGs : HasCompactSupport G :=
      HasCompactSupport.finset_sum fun j _ =>
        (hgc.comp_homeomorph (Homeomorph.subRight (t j))).smul_left
    have hadm := RHTower.WeilSpectral.admissible_weilTest hg hgc
    have harch_eq : hermQuad (gram (towerArch g ℓ) fun z : s => (z : Multiplicative ℤ))
        (v : s → ℂ) = (RHTower.WeilSpectral.archPart (EF.weilTest G G)).re := by
      have h1 : EF.weilTest G G =
          ∑ i, ∑ j, (star (w i) * w j) • RHTower.WeilSpectral.transl (t j - t i) K :=
        RHTower.WeilSpectral.weilTest_sum_transl hg.continuous hgc t w
      have hlin : ∀ {ι : Type*} (u : Finset ι) (f : ι → ℝ → ℂ),
          (∀ i ∈ u, RHTower.WeilSpectral.Admissible (f i)) →
          RHTower.WeilSpectral.archPart (∑ i ∈ u, f i) =
            ∑ i ∈ u, RHTower.WeilSpectral.archPart (f i) := by
        intro ι u f hf
        classical
        induction u using Finset.induction_on with
        | empty => simp [RHTower.WeilSpectral.archPart, paperFT]
        | insert a u ha ih =>
          have h1 := hf a (mem_insert_self a u)
          have h2 := RHTower.WeilSpectral.Admissible.sum u fun i hi => hf i (mem_insert_of_mem hi)
          rw [sum_insert ha, sum_insert ha, ← ih fun i hi => hf i (mem_insert_of_mem hi)]
          unfold RHTower.WeilSpectral.archPart
          rw [← mul_add, ← integral_add h1.arch h2.arch]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun r => ?_)
          rw [RHTower.WeilSpectral.paperFT_add h1 h2]; ring
      have hsmul : ∀ (a : ℂ) (f : ℝ → ℂ),
          RHTower.WeilSpectral.archPart (a • f) = a * RHTower.WeilSpectral.archPart f := fun a f => by
        unfold RHTower.WeilSpectral.archPart
        rw [mul_left_comm, ← integral_const_mul]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        rw [RHTower.WeilSpectral.paperFT_smul]; ring
      rw [h1, hlin _ _ fun i _ => RHTower.WeilSpectral.Admissible.sum _ fun j _ =>
        (hadm.transl _).smul _]
      have hinner : ∀ i, RHTower.WeilSpectral.archPart
          (∑ j, (star (w i) * w j) • RHTower.WeilSpectral.transl (t j - t i) K) =
          ∑ j, conj (w i) * RHTower.WeilSpectral.archPart
            (RHTower.WeilSpectral.transl (t j - t i) K) * w j := fun i => by
        rw [hlin _ _ fun j _ => (hadm.transl _).smul _]
        refine sum_congr rfl fun j _ => ?_
        rw [hsmul, Complex.star_def]; ring
      simp_rw [hinner]
      rw [hermQuad_gram]
      congr 1
      rw [← e.symm.sum_comp]
      refine sum_congr rfl fun i _ => ?_
      rw [← e.symm.sum_comp]
      refine sum_congr rfl fun j _ => ?_
      simp only [w, t, towerArch, toAdd_mul, toAdd_inv]
      congr 3
      push_cast; ring
    have hk₀_eq : ∫ u, ‖G u‖ ^ 2 =
        hermQuad (gram k₀ fun z : s => (z : Multiplicative ℤ)) (v : s → ℂ) := by
      have h0 : EF.weilTest G G 0 = ((∫ u, ‖G u‖ ^ 2 : ℝ) : ℂ) := by
        rw [RHTower.WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have h1 := congrFun (RHTower.WeilSpectral.weilTest_sum_transl hg.continuous hgc t w) 0
      rw [h0] at h1
      have hre := congrArg Complex.re h1
      simp only [Complex.ofReal_re, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        RHTower.WeilSpectral.transl, zero_sub, Complex.star_def] at hre
      rw [hre, hermQuad_gram]
      congr 1
      rw [← e.symm.sum_comp]
      refine sum_congr rfl fun i _ => ?_
      rw [← e.symm.sum_comp]
      refine sum_congr rfl fun j _ => ?_
      simp only [w, t, k₀, toAdd_mul, toAdd_inv]
      have hsh : -((Multiplicative.toAdd (e.symm j : Multiplicative ℤ) : ℝ) * ℓ -
          (Multiplicative.toAdd (e.symm i : Multiplicative ℤ) : ℝ) * ℓ) =
          -((-Multiplicative.toAdd (e.symm i : Multiplicative ℤ) +
            Multiplicative.toAdd (e.symm j : Multiplicative ℤ) : ℤ) : ℝ) * ℓ := by
        push_cast; ring
      rw [hsh]; ring
    have harch_lo : -10 * ((∑' m, ‖k₀ m‖) * ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2) ≤
        hermQuad (gram (towerArch g ℓ) fun z : s => (z : Multiplicative ℤ)) (v : s → ℂ) := by
      rw [harch_eq]
      have hPn : ∀ r : ℝ, paperFT (EF.weilTest G G) r = ((‖paperFT G r‖ ^ 2 : ℝ) : ℂ) := fun r => by
        rw [EF.paperFT_weilTest hGc.continuous hGc.continuous hGs hGs, Complex.conj_ofReal,
          Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hkd : ContDiff ℝ 2 (EF.weilTest G G) := EF.weilTest_contDiff hGc hGc.continuous hGs
      have hks : HasCompactSupport (EF.weilTest G G) := EF.weilTest_hasCompactSupport hGs hGs
      have hD : Integrable fun r : ℝ => ‖paperFT G r‖ ^ 2 := by
        have hP : Integrable fun r : ℝ => paperFT (EF.weilTest G G) r :=
          EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hkd hks)
        exact hP.norm.congr (Eventually.of_forall fun r => by
          simp only; rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
      have hGint : Integrable fun r : ℝ => ‖paperFT G r‖ ^ 2 * EF.gammaBracket r := by
        have hGc' := RHTower.LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
          hGc hGs hGc hGs
        exact hGc'.re.congr (Eventually.of_forall fun r => by
          change (paperFT (EF.weilTest G G) r * (EF.gammaBracket r : ℂ)).re = _
          rw [hPn]; simp)
      have hre : (RHTower.WeilSpectral.archPart (EF.weilTest G G)).re =
          (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT G r‖ ^ 2 * EF.gammaBracket r := by
        unfold RHTower.WeilSpectral.archPart
        have : ∫ r : ℝ, paperFT (EF.weilTest G G) r * (EF.gammaBracket r : ℂ) =
            ((∫ r : ℝ, ‖paperFT G r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
          rw [← integral_complex_ofReal]
          exact integral_congr_ae (Eventually.of_forall fun r => by simp only; rw [hPn]; push_cast; rfl)
        rw [this, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_mul, Complex.ofReal_re]
      have hgamma : ∫ r : ℝ, ‖paperFT G r‖ ^ 2 * (-10) ≤
          ∫ r : ℝ, ‖paperFT G r‖ ^ 2 * EF.gammaBracket r :=
        integral_mono (hD.mul_const (-10)) hGint fun r => by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hl := Real.log_nonneg (show 1 ≤ 1 + |r| / 4 by linarith [abs_nonneg r])
          linarith [RHTower.WeilWorkPBAP.gammaBracket_lower r]
      rw [integral_mul_const] at hgamma
      have hpl := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hGc hGs
      have hstep1 : -10 * ∫ u, ‖G u‖ ^ 2 ≤ (RHTower.WeilSpectral.archPart (EF.weilTest G G)).re := by
        rw [hre, ← hpl]
        have hπ : 0 < 1 / (2 * π) := by positivity
        nlinarith
      have hstep2 : ∫ u, ‖G u‖ ^ 2 ≤ (∑' m, ‖k₀ m‖) * ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2 := by
        rw [hk₀_eq]
        exact (le_abs_self _).trans (abs_hermQuad_gram_le_tsum_norm hk₀_sum s (v : s → ℂ))
      nlinarith
    have hprime_lo : -(|wPrime| * ((∑' m, ‖towerPrime (truncWeight S lam) g ℓ m‖) *
        ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2)) ≤
        hermQuad (gram (fun m => -(wPrime : ℂ) * towerPrime (truncWeight S lam) g ℓ m)
          fun z : s => (z : Multiplicative ℤ)) (v : s → ℂ) := by
      have hsmul : gram (fun m => -(wPrime : ℂ) * towerPrime (truncWeight S lam) g ℓ m)
          (fun z : s => (z : Multiplicative ℤ)) =
          ((-wPrime : ℝ) : ℂ) • gram (towerPrime (truncWeight S lam) g ℓ)
            (fun z : s => (z : Multiplicative ℤ)) := by
        ext i j; simp [gram]
      rw [hsmul, ArithmeticCastelnuovoSeveri.hermQuad_ofReal_smul]
      have habs := abs_hermQuad_gram_le_tsum_norm hp_sum s (v : s → ℂ)
      have hmul : |(-wPrime) * hermQuad (gram (towerPrime (truncWeight S lam) g ℓ)
          (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ)| ≤
          |wPrime| * ((∑' m, ‖towerPrime (truncWeight S lam) g ℓ m‖) *
            ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2) := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      linarith [neg_abs_le ((-wPrime) * hermQuad (gram (towerPrime (truncWeight S lam) g ℓ)
        (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ))]
    have hdiag : hermQuad (gram (LocalCounterterm.eval ⟨0, D, 0⟩)
        (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) =
        D * ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2 := by
      rw [hermQuad_gram]
      have hterm : ∀ i j : s,
          conj ((v : s → ℂ) i) * LocalCounterterm.eval ⟨0, D, 0⟩ (((i : Multiplicative ℤ))⁻¹ * j) *
            (v : s → ℂ) j =
          if i = j then ((D * ‖(v : s → ℂ) i‖ ^ 2 : ℝ) : ℂ) else 0 := fun i j => by
        have h1 : ((i : Multiplicative ℤ))⁻¹ * (j : Multiplicative ℤ) = 1 ↔ i = j := by
          rw [inv_mul_eq_one]; exact Subtype.ext_iff.symm
        simp only [LocalCounterterm.eval, Complex.ofReal_zero, zero_add, zero_mul, add_zero, h1]
        split_ifs with hij
        · subst hij
          rw [mul_right_comm, Complex.conj_mul', ← Complex.ofReal_pow]
          push_cast; ring
        · ring
      simp_rw [hterm, Finset.sum_ite_eq, if_pos (mem_univ _), ← Complex.ofReal_sum,
        Complex.ofReal_re, mul_sum]
    have hsplit : hermQuad (gram (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩)
        (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) =
        hermQuad (gram (fun m => -(wPrime : ℂ) * towerPrime (truncWeight S lam) g ℓ m)
          (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) +
        hermQuad (gram (towerArch g ℓ) (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) +
        hermQuad (gram (LocalCounterterm.eval ⟨0, D, 0⟩)
          (fun z : s => (z : Multiplicative ℤ))) (v : s → ℂ) := by
      have heq : gram (sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩)
          (fun z : s => (z : Multiplicative ℤ)) =
          (gram (fun m => -(wPrime : ℂ) * towerPrime (truncWeight S lam) g ℓ m)
            (fun z : s => (z : Multiplicative ℤ)) +
          gram (towerArch g ℓ) (fun z : s => (z : Multiplicative ℤ))) +
          gram (LocalCounterterm.eval ⟨0, D, 0⟩) (fun z : s => (z : Multiplicative ℤ)) := by
        ext i j; simp [gram, sTruncatedNonPole, ℓ]
      rw [heq, HeckeKreinToeplitz.hermQuad_add, HeckeKreinToeplitz.hermQuad_add]
    have hnorm_nonneg : 0 ≤ ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hD_diff : 0 ≤ (D - D₀) * ∑ i : s, ‖(v : s → ℂ) i‖ ^ 2 :=
      mul_nonneg (by linarith) hnorm_nonneg
    rw [hsplit, hdiag] at hneg
    simp only [D₀] at hD_diff
    linarith
  refine ⟨hpd, ?_⟩
  have heq : sTruncatedLocal S lam g p 0 wPrime 1 ⟨0, D, 0⟩ =
      sTruncatedNonPole S lam g p wPrime 1 ⟨0, D, 0⟩ := by
    funext m; simp [sTruncatedLocal]
  rw [heq]
  exact nonpos_iff_eq_zero.mp ((polarIndex_le_negIndex _).trans hpd.negIndex_eq_zero.le)

/-- Positive `L²` norm of the cubic spline. -/
theorem integral_cubicSpline_sq_pos : 0 < ∫ u : ℝ, cubicSpline u ^ 2 := by
  have hcont : Continuous fun u : ℝ => cubicSpline u ^ 2 := contDiff_cubicSpline.continuous.pow 2
  have hsupp : HasCompactSupport fun u : ℝ => cubicSpline u ^ 2 := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -4) (b := 4)) fun u hu => ?_
    have habs : 4 < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · linarith [neg_le_abs u]
      · linarith [le_abs_self u]
    simp [cubicSpline_eq_zero habs]
  have hint : Integrable fun u : ℝ => cubicSpline u ^ 2 :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hne : ∃ x : ℝ, cubicSpline x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hft : paperFT (fun x => (cubicSpline x : ℂ)) I = 0 := by
      simp [paperFT, hall]
    exact paperFT_cubicSpline_ne_zero (z := I) (by simp) hft
  obtain ⟨x₀, hx₀⟩ := hne
  rw [(integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hint)]
  have hopen : IsOpen (Function.support fun u : ℝ => cubicSpline u ^ 2) :=
    hcont.isOpen_support
  exact hopen.measure_pos volume ⟨x₀, pow_ne_zero 2 hx₀⟩

/-- A separable prime-tower assembly of positive-definite local kernels is positive definite. -/
theorem isPosDefKernel_towerAssembly (S : Finset Nat.Primes) {k : S → Multiplicative ℤ → ℂ}
    (hk : ∀ p : S, IsPosDefKernel (k p)) : IsPosDefKernel (towerAssembly S k) := by
  refine ⟨isHermKernel_towerAssembly S fun p => (hk p).1, fun n x c => ?_⟩
  have hsum : ∀ t : Finset S, 0 ≤ hermQuad (∑ p ∈ t, gram (k p) fun a => valS S (x a) p) c := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => simp [hermQuad]
    | insert p t hp ih =>
      rw [sum_insert hp, HeckeKreinToeplitz.hermQuad_add]
      exact add_nonneg ((hk p).2 n (fun a => valS S (x a) p) c) ih
  have hgram : gram (towerAssembly S k) x = ∑ p : S, gram (k p) fun a => valS S (x a) p := by
    ext a b; simp [towerAssembly, gram, separable, Finset.sum_apply]
  rw [hgram]
  exact hsum univ

/-- **Unconditional twin-flip blindness of counterterm-stabilized `S`-truncated assemblies.**
There exists an explicit prime `q` (`8 ≤ log q`) such that for every finite prime set `S`,
sufficiently large diagonal running counterterms give **both** `Λ` and `primeFlipWeight q` glued
negative index `1` on their pole-free `S`-truncated assemblies, even though at least one of `ζ` and
its `q`-flipped twin has infinite global negative index `⊤`. -/
theorem exists_prime_flip_obstruction (c : ℝ) (hc : 0 < c) :
    ∃ q : ℕ, q.Prime ∧
      (negIndex zetaKernel = ⊤ ∨ negIndex (weightKernel (primeFlipWeight q) cubicSpline) = ⊤) ∧
      ∀ S : Finset Nat.Primes, ∃ ct : S → LocalCounterterm,
        negIndex (archGlue (sTruncatedAssembly S
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (cx cubicSpline) (fun _ => 0) (fun _ => 1) (fun _ => 1) ct) c) = 1 ∧
          negIndex (archGlue (sTruncatedAssembly S (primeFlipWeight q)
            (cx cubicSpline) (fun _ => 0) (fun _ => 1) (fun _ => 1) ct) c) = 1 := by
  obtain ⟨q, hq_ge, hq⟩ := Nat.exists_infinite_primes (⌈Real.exp 8⌉₊ + 1)
  have hlog : 2 * 4 ≤ Real.log q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    rw [show (2 * 4 : ℝ) = 8 by norm_num, Real.le_log_iff_exp_le hqpos]
    exact (Nat.le_ceil (Real.exp 8)).trans (by exact_mod_cast (by omega : ⌈Real.exp 8⌉₊ ≤ q))
  have hsupp : ∀ u : ℝ, 4 ≤ |u| → cubicSpline u = 0 := by
    -- Extend vanishing of cubicSpline from 4 < |u| to 4 ≤ |u| by continuity.
    intro u hu
    rcases hu.lt_or_eq with hlt | heq
    · exact cubicSpline_eq_zero hlt
    · have hlim : Tendsto (fun k : ℕ => cubicSpline (u + (if 0 ≤ u then 1 else -1) / ((k : ℝ) + 1)))
          atTop (𝓝 (cubicSpline u)) := by
        refine (contDiff_cubicSpline.continuous.tendsto u).comp ?_
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (if 0 ≤ u then (1 : ℝ) else -1)
        rw [mul_zero] at h0
        simpa [div_eq_mul_inv, mul_comm] using tendsto_const_nhds.add h0
      have hzero : ∀ k : ℕ, cubicSpline (u + (if 0 ≤ u then 1 else -1) / ((k : ℝ) + 1)) = 0 := by
        intro k
        refine cubicSpline_eq_zero ?_
        have hd : 0 < 1 / ((k : ℝ) + 1) := by positivity
        by_cases hu0 : 0 ≤ u
        · rw [if_pos hu0]
          have hu4 : u = 4 := by rw [abs_of_nonneg hu0] at heq; linarith
          rw [hu4, abs_of_pos (by linarith)]; linarith
        · rw [if_neg hu0]
          have hu4 : u = -4 := by rw [abs_of_neg (not_le.mp hu0)] at heq; linarith
          rw [hu4, show -4 + -1 / ((k : ℝ) + 1) = -(4 + 1 / ((k : ℝ) + 1)) by ring, abs_neg,
            abs_of_pos (by linarith)]; linarith
      exact tendsto_nhds_unique hlim (by simp_rw [hzero]; exact tendsto_const_nhds)
  have hor := negIndex_zetaKernel_eq_top_or_flip hq cubicSpline_mem_realTests
    integral_cubicSpline_sq_pos hsupp hlog
  refine ⟨q, hq, hor, fun S => ?_⟩
  have hg := cx_contDiff contDiff_cubicSpline
  have hgc := cx_hasCompactSupport hasCompactSupport_cubicSpline
  have hD : ∀ p : S, ∃ D : ℝ,
      IsPosDefKernel (sTruncatedNonPole S (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (cx cubicSpline) (p : Nat.Primes) 1 1 ⟨0, D, 0⟩) ∧
      IsPosDefKernel (sTruncatedNonPole S (primeFlipWeight q)
        (cx cubicSpline) (p : Nat.Primes) 1 1 ⟨0, D, 0⟩) := fun p => by
    obtain ⟨D₁, hD₁⟩ := exists_diagonal_counterterm_posDef S
      (fun r _ => ⟨Real.log (r : ℕ), fun _ hk => vonMangoldt_prime_pow_le_log r hk⟩)
      hg hgc (p : Nat.Primes) 1
    obtain ⟨D₂, hD₂⟩ := exists_diagonal_counterterm_posDef S
      (fun r _ => ⟨Real.log (r : ℕ), fun k hk => by
        rw [abs_primeFlipWeight]; exact vonMangoldt_prime_pow_le_log r hk⟩)
      hg hgc (p : Nat.Primes) 1
    exact ⟨max D₁ D₂, (hD₁ _ (le_max_left _ _)).1, (hD₂ _ (le_max_right _ _)).1⟩
  choose D hD₁ hD₂ using hD
  refine ⟨fun p => ⟨0, D p, 0⟩, ?_, ?_⟩
  · have hpos : IsPosDefKernel (sTruncatedAssembly S
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (cx cubicSpline) (fun _ => 0) (fun _ => 1) (fun _ => 1) fun p => ⟨0, D p, 0⟩) := by
      refine isPosDefKernel_towerAssembly S fun p => ?_
      have heq : sTruncatedLocal S (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (cx cubicSpline) (p : Nat.Primes) 0 1 1 ⟨0, D p, 0⟩ =
          sTruncatedNonPole S (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (cx cubicSpline) (p : Nat.Primes) 1 1 ⟨0, D p, 0⟩ := funext fun _ => by
        simp [sTruncatedLocal]
      rw [heq]
      exact hD₁ p
    have hk : ∀ p : S, IsHermKernel (sTruncatedLocal S
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (cx cubicSpline) (p : Nat.Primes) 0 1 1 ⟨0, D p, 0⟩) :=
      fun p => isHermKernel_sTruncatedLocal _ _ _ _ _ _ _ _
    rw [sTruncatedAssembly, negIndex_archGlue_towerAssembly S hk hc,
      ← negIndex_towerAssembly S, ← sTruncatedAssembly, hpos.negIndex_eq_zero, zero_add]
  · have hpos : IsPosDefKernel (sTruncatedAssembly S (primeFlipWeight q)
        (cx cubicSpline) (fun _ => 0) (fun _ => 1) (fun _ => 1) fun p => ⟨0, D p, 0⟩) := by
      refine isPosDefKernel_towerAssembly S fun p => ?_
      have heq : sTruncatedLocal S (primeFlipWeight q)
          (cx cubicSpline) (p : Nat.Primes) 0 1 1 ⟨0, D p, 0⟩ =
          sTruncatedNonPole S (primeFlipWeight q)
            (cx cubicSpline) (p : Nat.Primes) 1 1 ⟨0, D p, 0⟩ := funext fun _ => by
        simp [sTruncatedLocal]
      rw [heq]
      exact hD₂ p
    have hk : ∀ p : S, IsHermKernel (sTruncatedLocal S (primeFlipWeight q)
        (cx cubicSpline) (p : Nat.Primes) 0 1 1 ⟨0, D p, 0⟩) :=
      fun p => isHermKernel_sTruncatedLocal _ _ _ _ _ _ _ _
    rw [sTruncatedAssembly, negIndex_archGlue_towerAssembly S hk hc,
      ← negIndex_towerAssembly S, ← sTruncatedAssembly, hpos.negIndex_eq_zero, zero_add]

end GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling
