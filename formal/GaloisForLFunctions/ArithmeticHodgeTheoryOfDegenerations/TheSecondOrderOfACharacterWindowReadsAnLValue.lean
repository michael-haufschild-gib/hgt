import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSpectrumOfARamanujanSumIsTheUnitGroup
import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve

/-!
# The second order of a character window reads an `L`-value

The second-order term of a window twisted by a mean-zero periodic weight is its spectral sum, the
Dirichlet series `2M^s Σ_j |χ̂(j)|² j^{−s}` of its power spectrum, `s = β + 1`
(`periodicTwist_layer_criticalCurve_dirichlet`). For a Ramanujan sum the spectrum is the unit
group and the series is a count, `2ζ(s)J_s(m)` (`twistSpectralSum_ramTwist`). For the real part of
a primitive Dirichlet character `ψ` modulo `q` the spectrum carries a phase, and the count acquires
an `L`-value:

* **The spectrum of `Re(cψ)`** (`twistCoeff_charTwist`, `twistPower_charTwist`): with the Gauss
  sum `τ = τ(ψ)`, `S_k = (c ψ̄(k) τ + c̄ ψ(−1) ψ(k) τ̄)/2`, so

  `|χ̂(k)|² = |c|² [(k, q) = 1]/(2q) + Re(c² ψ̄(−1) ψ̄(k)² τ²)/(2q²)`.

* **The spectral sum is a count plus an `L`-value** (`twistSpectralSum_charTwist`):

  `2q^s Σ_j |χ̂(j)|² j^{−s} = |c|² ζ(s) J_s(q)/q + q^{s−2} Re(c² ψ̄(−1) τ(ψ)² L(s, ψ̄²))`.

* **The character pair splits the count by `|L(s, ψ̄²)|`** (`abs_twistSpectralSum_charTwist_sub_le`,
  `exists_charTwist_extremal`): on the circle `|c| = 1` (the windows twisted by
  `cos θ Re ψ − sin θ Im ψ`) the spectral sum ranges exactly over
  `ζ(s)J_s(q)/q ± q^{s−1} ‖L(s, ψ̄²)‖`.

* **The second-order term** (`charTwist_layer_criticalCurve`): along `c^{β+1}/log N → K` the window
  `h(log(n/N)) Re(c ψ(n))/√n` has second-order coefficient `βA_φ/(K∫φ²)` times the spectral sum at
  `s = β + 1`.

Since `|τ|² = q` and `|L(s, ψ̄²)| ≤ Σ_{(j,q)=1} j^{−s}`, the `L`-value term never exceeds the count:
the second order stays positive. For a quadratic `ψ` (`ψ̄²` principal, `τ² = ψ(−1)q`) the two terms
agree and give the unit count `2ζ(s)J_s(q)/q` (for the Legendre symbol `2ζ(s)(p^s − 1)/p`). Beyond the count, the second order of a
complex character window sees the `L`-function of the squared character.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {q : ℕ} [NeZero q] {φ h : ℝ → ℝ} {A : ℝ}

/-- The real twist of a Dirichlet character along `c ∈ ℂ`: `n ↦ Re(c ψ(n))`. -/
def charTwist (c : ℂ) (ψ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := (c * ψ (n : ZMod q)).re

/-- The `L`-series of the squared conjugate character, `L(s, ψ̄²) = Σ_j ψ̄(j)² j^{−s}`. -/
def charSqL (ψ : DirichletCharacter ℂ q) (s : ℝ) : ℂ :=
  ∑' j : ℕ, conj (ψ (j : ZMod q)) ^ 2 * (((j : ℝ) ^ (-s) : ℝ) : ℂ)

/-- A primitive character of modulus `q ≥ 2` is not trivial. -/
theorem ne_one_of_isPrimitive {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q) :
    ψ ≠ 1 := by
  intro h1
  have hc := hψ
  unfold DirichletCharacter.IsPrimitive at hc
  rw [h1, DirichletCharacter.conductor_one] at hc
  omega

/-- The real twist of a nontrivial character is a mean-zero twist of period `q`. -/
theorem meanZeroTwist_charTwist (c : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) :
    MeanZeroTwist (charTwist c ψ) q := by
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne q), fun n => ?_, ?_⟩
  · simp [charTwist]
  · have h := MulChar.sum_eq_zero_of_ne_one hψ
    rw [sum_zmod_eq_sum_range] at h
    have := congrArg (fun z => (c * z).re) h
    simpa [charTwist, Complex.re_sum, Finset.mul_sum] using this

omit [NeZero q] in
/-- The character at `n` as a unit value: `|ψ(n)|² = [(n, q) = 1]`. -/
theorem normSq_charApply (ψ : DirichletCharacter ℂ q) (n : ℕ) :
    Complex.normSq (ψ (n : ZMod q)) = if Nat.Coprime n q then 1 else 0 := by
  split_ifs with hc
  · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hc
    have := DirichletCharacter.unit_norm_eq_one ψ hu.unit
    rw [IsUnit.unit_spec] at this
    rw [Complex.normSq_eq_norm_sq, this, one_pow]
  · have hu : ¬ IsUnit (n : ZMod q) := fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h)
    rw [MulChar.map_nonunit ψ hu, map_zero]

/-- `e(kn/q)` as the standard additive character of `ℤ/q`. -/
theorem cexp_eq_stdChar (k n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (k * n / q)) =
      RHTower.stdChar q ((k : ZMod q) * (n : ZMod q)) := by
  have h := ZMod.stdAddChar_coe (N := q) ((k * n : ℕ) : ℤ)
  push_cast at h
  rw [h]
  congr 1
  ring

/-- **The spectrum of `Re(cψ)`**: `S_k = (c ψ̄(k) τ + c̄ ψ(−1) ψ(k) τ̄)/2`. -/
theorem twistCoeff_charTwist (c : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (k : ℕ) :
    twistCoeff (charTwist c ψ) q k =
      (c * (conj (ψ (k : ZMod q)) * gaussSum ψ (RHTower.stdChar q)) +
        conj c * (ψ (-1) * ψ (k : ZMod q) * conj (gaussSum ψ (RHTower.stdChar q)))) / 2 := by
  set τ := gaussSum ψ (RHTower.stdChar q) with hτ
  unfold twistCoeff charTwist
  simp_rw [cexp_eq_stdChar, Complex.re_eq_add_conj, map_mul]
  rw [← sum_zmod_eq_sum_range q (fun b => (c * ψ b + conj c * conj (ψ b)) / 2 *
    RHTower.stdChar q ((k : ZMod q) * b))]
  have h1 : ∑ b : ZMod q, ψ b * RHTower.stdChar q ((k : ZMod q) * b) = conj (ψ k) * τ :=
    (RHTower.conj_mul_gaussSum_of_isPrimitive hψ (k : ZMod q)).symm
  have h2 : ∑ b : ZMod q, conj (ψ b) * RHTower.stdChar q ((k : ZMod q) * b) =
      ψ (-1) * ψ (k : ZMod q) * conj τ := by
    have e : ∑ b : ZMod q, conj (ψ b) * RHTower.stdChar q ((k : ZMod q) * b) =
        conj (∑ b : ZMod q, ψ b * RHTower.stdChar q (-(k : ZMod q) * b)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [(starRingEnd ℂ).map_mul, RHTower.conj_stdChar, neg_mul, neg_neg]
    rw [e, ← RHTower.conj_mul_gaussSum_of_isPrimitive hψ, map_mul, Complex.conj_conj,
      show -(k : ZMod q) = -1 * k by ring, map_mul]
  have hsplit : ∑ b : ZMod q, (c * ψ b + conj c * conj (ψ b)) / 2 *
      RHTower.stdChar q ((k : ZMod q) * b) =
      (c * ∑ b : ZMod q, ψ b * RHTower.stdChar q ((k : ZMod q) * b) +
        conj c * ∑ b : ZMod q, conj (ψ b) * RHTower.stdChar q ((k : ZMod q) * b)) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit, h1, h2]

/-- **The power spectrum of `Re(cψ)`**:
`|χ̂(k)|² = |c|² [(k, q) = 1]/(2q) + Re(c² ψ̄(−1) ψ̄(k)² τ²)/(2q²)`. -/
theorem twistPower_charTwist (c : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (k : ℕ) :
    twistPower (charTwist c ψ) q k =
      Complex.normSq c * (if Nat.Coprime k q then 1 else 0) / (2 * q) +
        (c ^ 2 * conj (ψ (-1)) * conj (ψ (k : ZMod q)) ^ 2 *
          gaussSum ψ (RHTower.stdChar q) ^ 2).re / (2 * (q : ℝ) ^ 2) := by
  set τ := gaussSum ψ (RHTower.stdChar q) with hτ
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hτ2 : Complex.normSq τ = q := by
    rw [Complex.normSq_eq_norm_sq]; exact RHTower.normSq_gaussSum_of_isPrimitive hψ
  have hε : Complex.normSq (ψ (-1)) = 1 := by
    have := DirichletCharacter.unit_norm_eq_one ψ (-1)
    rw [Units.val_neg, Units.val_one] at this
    rw [Complex.normSq_eq_norm_sq, this, one_pow]
  have hk := normSq_charApply ψ k
  unfold twistPower
  rw [twistCoeff_charTwist c hψ, ← hτ, Complex.sq_norm, Complex.normSq_div, Complex.normSq_add,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_conj, Complex.normSq_conj, hτ2, hε, hk]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2]
  have hre : (c * (conj (ψ (k : ZMod q)) * τ) *
      conj (conj c * (ψ (-1) * ψ (k : ZMod q) * conj τ))).re =
      (c ^ 2 * conj (ψ (-1)) * conj (ψ (k : ZMod q)) ^ 2 * τ ^ 2).re := by
    congr 1
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hre]
  field_simp
  split_ifs <;> ring

omit [NeZero q] in
/-- The count `Σ_{(j,q)=1} j^{−s} = ζ(s) J_s(q)/q^s`. -/
theorem tsum_coprime_rpow {s : ℝ} (hs : 1 < s) (hq : 1 < q) :
    ∑' j : ℕ, (if Nat.Coprime j q then (1 : ℝ) else 0) * (j : ℝ) ^ (-s) =
      ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s q /
        (q : ℝ) ^ s := by
  have hq0 : 0 < q := by omega
  have hR := twistSpectralSum_ramTwist hs hq
  rw [twistSpectralSum_eq_dirichlet hs (meanZeroTwist_ramTwist hq)] at hR
  simp_rw [twistPower_ramTwist hq0] at hR
  have hqs : 0 < (q : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast hq0) s
  field_simp
  linarith

/-- **The spectral sum of a character window is a count plus an `L`-value**:
`2q^s Σ_j |χ̂(j)|² j^{−s} = |c|² ζ(s) J_s(q)/q + q^s/q² Re(c² ψ̄(−1) τ(ψ)² L(s, ψ̄²))`. -/
theorem twistSpectralSum_charTwist (c : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive)
    (hq : 1 < q) {s : ℝ} (hs : 1 < s) :
    2 * (q : ℝ) ^ s * ∑' j : ℕ, twistPower (charTwist c ψ) q j * (j : ℝ) ^ (-s) =
      Complex.normSq c * (ArithmeticDegenerationTheory.zetaSum s *
          ArithmeticDegenerationTheory.jordanTotient s q / q) +
        (q : ℝ) ^ s / (q : ℝ) ^ 2 *
          (c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s).re := by
  set τ := gaussSum ψ (RHTower.stdChar q) with hτ
  set ε := c ^ 2 * conj (ψ (-1)) with hεdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hg : Summable fun j : ℕ => (j : ℝ) ^ (-s) := Real.summable_nat_rpow.mpr (by linarith)
  -- the `L`-series converges absolutely
  have hLs : Summable fun j : ℕ => conj (ψ (j : ZMod q)) ^ 2 * (((j : ℝ) ^ (-s) : ℝ) : ℂ) := by
    refine Summable.of_norm_bounded hg fun j => ?_
    rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 : ‖ψ (j : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
    have h2 : ‖ψ (j : ZMod q)‖ ^ 2 ≤ 1 := by
      have := norm_nonneg (ψ (j : ZMod q)); nlinarith
    have h3 : (0 : ℝ) ≤ (j : ℝ) ^ (-s) := by positivity
    nlinarith
  have hLre : (ε * τ ^ 2 * charSqL ψ s).re =
      ∑' j : ℕ, (ε * conj (ψ (j : ZMod q)) ^ 2 * τ ^ 2).re * (j : ℝ) ^ (-s) := by
    unfold charSqL
    rw [← tsum_mul_left, Complex.re_tsum (hLs.mul_left _)]
    refine tsum_congr fun j => ?_
    rw [← Complex.re_mul_ofReal]
    congr 1
    ring
  have hS1 : Summable fun j : ℕ => Complex.normSq c * (if Nat.Coprime j q then (1 : ℝ) else 0) /
      (2 * q) * (j : ℝ) ^ (-s) := by
    have hb : Summable fun j : ℕ => Complex.normSq c / (2 * (q : ℝ)) * (j : ℝ) ^ (-s) :=
      hg.mul_left _
    have hc0 := Complex.normSq_nonneg c
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hb
    · have : (0 : ℝ) ≤ (j : ℝ) ^ (-s) := by positivity
      split_ifs <;> positivity
    · have : (0 : ℝ) ≤ (j : ℝ) ^ (-s) := by positivity
      split_ifs
      · rw [mul_one]
      · simp only [mul_zero, zero_div, zero_mul]; positivity
  have hS2 : Summable fun j : ℕ => (ε * conj (ψ (j : ZMod q)) ^ 2 * τ ^ 2).re /
      (2 * (q : ℝ) ^ 2) * (j : ℝ) ^ (-s) := by
    have := (Complex.reCLM.summable ((hLs.mul_left (ε * τ ^ 2)))).mul_left (1 / (2 * (q : ℝ) ^ 2))
    refine this.congr fun j => ?_
    simp only [Complex.reCLM_apply]
    rw [show ε * τ ^ 2 * (conj (ψ (j : ZMod q)) ^ 2 * (((j : ℝ) ^ (-s) : ℝ) : ℂ)) =
      ε * conj (ψ (j : ZMod q)) ^ 2 * τ ^ 2 * (((j : ℝ) ^ (-s) : ℝ) : ℂ) by ring,
      Complex.re_mul_ofReal]
    ring
  simp_rw [twistPower_charTwist c hψ, add_mul]
  rw [Summable.tsum_add hS1 hS2]
  have e1 : ∑' j : ℕ, Complex.normSq c * (if Nat.Coprime j q then (1 : ℝ) else 0) / (2 * q) *
      (j : ℝ) ^ (-s) = (Complex.normSq c / (2 * q)) *
        ∑' j : ℕ, (if Nat.Coprime j q then (1 : ℝ) else 0) * (j : ℝ) ^ (-s) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e2 : ∑' j : ℕ, (ε * conj (ψ (j : ZMod q)) ^ 2 * τ ^ 2).re / (2 * (q : ℝ) ^ 2) *
      (j : ℝ) ^ (-s) = (1 / (2 * (q : ℝ) ^ 2)) * (ε * τ ^ 2 * charSqL ψ s).re := by
    rw [hLre, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [e1, e2, tsum_coprime_rpow hs hq]
  have hqs : 0 < (q : ℝ) ^ s := Real.rpow_pos_of_pos hq0 s
  field_simp

/-- `‖ψ̄(−1) τ(ψ)²‖ = q`. -/
theorem norm_sign_mul_gaussSum_sq {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) :
    ‖conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2‖ = q := by
  have h1 : ‖ψ (-1)‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one ψ (-1)
    rwa [Units.val_neg, Units.val_one] at this
  rw [norm_mul, Complex.norm_conj, norm_pow, h1, one_mul,
    RHTower.normSq_gaussSum_of_isPrimitive hψ]

/-- **The `L`-value bounds the deviation from the count**: on the unit circle `|c| = 1`,
`|2q^s Σ_j |χ̂(j)|² j^{−s} − ζ(s)J_s(q)/q| ≤ q^{s−1} ‖L(s, ψ̄²)‖`. -/
theorem abs_twistSpectralSum_charTwist_sub_le {c : ℂ} (hc : Complex.normSq c = 1)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q) {s : ℝ} (hs : 1 < s) :
    |2 * (q : ℝ) ^ s * ∑' j : ℕ, twistPower (charTwist c ψ) q j * (j : ℝ) ^ (-s) -
        ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s q /
          q| ≤ (q : ℝ) ^ s / q * ‖charSqL ψ s‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hcn : ‖c‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hc] at h
    nlinarith [norm_nonneg c]
  rw [twistSpectralSum_charTwist c hψ hq hs, hc, one_mul, add_sub_cancel_left, abs_mul,
    abs_of_pos (by positivity)]
  have hre := Complex.abs_re_le_norm
    (c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s)
  have hn : ‖c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s‖ =
      q * ‖charSqL ψ s‖ := by
    rw [show c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s =
      c ^ 2 * (conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2) * charSqL ψ s by ring,
      norm_mul, norm_mul, norm_pow, hcn, norm_sign_mul_gaussSum_sq hψ, one_pow, one_mul]
  rw [hn] at hre
  calc (q : ℝ) ^ s / (q : ℝ) ^ 2 *
        |(c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s).re|
      ≤ (q : ℝ) ^ s / (q : ℝ) ^ 2 * (q * ‖charSqL ψ s‖) :=
        mul_le_mul_of_nonneg_left hre (by positivity)
    _ = (q : ℝ) ^ s / q * ‖charSqL ψ s‖ := by field_simp

/-- **The character pair splits the count by `|L(s, ψ̄²)|`**: on the circle of twists
`Re(cψ)`, `|c| = 1`, the spectral sum attains both `ζ(s)J_s(q)/q ± q^{s−1} ‖L(s, ψ̄²)‖`. -/
theorem exists_charTwist_extremal {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q)
    {s : ℝ} (hs : 1 < s) :
    ∃ cP cM : ℂ, Complex.normSq cP = 1 ∧ Complex.normSq cM = 1 ∧
      2 * (q : ℝ) ^ s * ∑' j : ℕ, twistPower (charTwist cP ψ) q j * (j : ℝ) ^ (-s) =
        ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s q /
          q + (q : ℝ) ^ s / q * ‖charSqL ψ s‖ ∧
      2 * (q : ℝ) ^ s * ∑' j : ℕ, twistPower (charTwist cM ψ) q j * (j : ℝ) ^ (-s) =
        ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s q /
          q - (q : ℝ) ^ s / q * ‖charSqL ψ s‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set w := conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 * charSqL ψ s with hw
  have hwn : ‖w‖ = q * ‖charSqL ψ s‖ := by
    rw [hw, norm_mul, norm_sign_mul_gaussSum_sq hψ]
  have hrw : ∀ c : ℂ, c ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 *
      charSqL ψ s = c ^ 2 * w := fun c => by rw [hw]; ring
  -- the value on the circle as a function of `c²`
  have hval : ∀ c : ℂ, Complex.normSq c = 1 →
      2 * (q : ℝ) ^ s * ∑' j : ℕ, twistPower (charTwist c ψ) q j * (j : ℝ) ^ (-s) =
        ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s q /
          q + (q : ℝ) ^ s / (q : ℝ) ^ 2 * (c ^ 2 * w).re := fun c hc => by
    rw [twistSpectralSum_charTwist c hψ hq hs, hc, one_mul, hrw]
  -- a square root on the unit circle
  have hroot : ∀ u : ℂ, ‖u‖ = 1 → ∃ c : ℂ, c ^ 2 = u ∧ Complex.normSq c = 1 := by
    intro u hu
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < 2)
    refine ⟨c, hc, ?_⟩
    have h1 : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc, hu]
    rw [Complex.normSq_eq_norm_sq, h1]
  by_cases hw0 : w = 0
  · have hL : ‖charSqL ψ s‖ = 0 := by
      have h := hwn
      rw [hw0, norm_zero] at h
      have := mul_eq_zero.mp h.symm
      rcases this with h' | h'
      · exact absurd h' hq0.ne'
      · exact h'
    refine ⟨1, 1, by simp, by simp, ?_, ?_⟩ <;>
      · rw [hval 1 (by simp), hw0, hL]; simp
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have huP : ‖conj w / (‖w‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos,
        div_self hwpos.ne']
    have huM : ‖-(conj w / (‖w‖ : ℂ))‖ = 1 := by rw [norm_neg, huP]
    obtain ⟨cP, hcP2, hcP⟩ := hroot _ huP
    obtain ⟨cM, hcM2, hcM⟩ := hroot _ huM
    have hconj : (conj w / (‖w‖ : ℂ) * w).re = ‖w‖ := by
      rw [div_mul_eq_mul_div, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_div,
        Complex.ofReal_re, sq, mul_div_assoc, div_self hwpos.ne', mul_one]
    refine ⟨cP, cM, hcP, hcM, ?_, ?_⟩
    · rw [hval cP hcP, hcP2, hconj, hwn]
      field_simp
    · rw [hval cM hcM, hcM2, neg_mul, Complex.neg_re, hconj, hwn]
      field_simp
      ring

/-- **The second-order term of a character window.** For a primitive Dirichlet character `ψ`
modulo `q ≥ 2` and `a ∈ ℂ`, along `c^{β+1}/log N → K` the window `h(log(n/N)) Re(a ψ(n))/√n` has
second-order term `(βA_φ/(K∫φ²)) (|a|² ζ(β+1) J_{β+1}(q)/q +
q^{β−1} Re(a² ψ̄(−1) τ(ψ)² L(β+1, ψ̄²))) ∫ e^{−(β+1)y} H²`. -/
theorem charTwist_layer_criticalCurve (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (a : ℂ) {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (charTwist a ψ) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        (Complex.normSq a * (ArithmeticDegenerationTheory.zetaSum (β + 1) *
            ArithmeticDegenerationTheory.jordanTotient (β + 1) q / q) +
          (q : ℝ) ^ (β + 1) / (q : ℝ) ^ 2 *
            (a ^ 2 * conj (ψ (-1)) * gaussSum ψ (RHTower.stdChar q) ^ 2 *
              charSqL ψ (β + 1)).re) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  have h := periodicTwist_layer_criticalCurve_dirichlet hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit (meanZeroTwist_charTwist a (ne_one_of_isPrimitive hψ hq))
  rwa [twistSpectralSum_charTwist a hψ hq (by linarith)] at h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
