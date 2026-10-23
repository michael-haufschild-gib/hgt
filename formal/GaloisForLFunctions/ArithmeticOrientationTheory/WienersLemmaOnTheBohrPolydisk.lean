import GaloisForLFunctions.ArithmeticOrientationTheory.TheCriticalWienerAlgebraIsABanachAlgebra
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Wiener's lemma on the Bohr polydisk

A **Bohr point** is a completely multiplicative `ω : ℕ → ℂ` with `|ω| ≤ 1` (`BohrPoint`): a point
`(ω(p))_p` of the closed unit polydisk indexed by the primes.  The **Bohr evaluation** of an
element of the Wiener algebra `𝒲_σ` at `ω` is `Σ_n f(n) ω(n) n^{−σ}` (`bohrEval`); at
`ω(n) = n^{σ−s}` it is the Dirichlet series `Σ f(n) n^{−s}`, `Re s ≥ σ`.

* **Bohr evaluations are characters** (`bohrEval_mul`, `bohrEval_one`, `bohrCharacter`): twisting
  by a completely multiplicative `ω` commutes with Dirichlet convolution.
* **Every character is a Bohr evaluation** (`apply_eq_bohrEval`): a continuous character `φ` of
  `𝒲_σ` is evaluation at `ω(n) = φ(δ_n) n^σ`; the bound `|ω| ≤ 1` is the spectral bound
  `|φ(δ_n)| ≤ ‖δ_n‖ = n^{−σ}`, and the value on `f` comes from `f = Σ f(n) δ_n`.  So the Gelfand
  spectrum of `𝒲_σ` is the Bohr polydisk.
* **Wiener's lemma** (`isUnit_iff_forall_bohrEval_ne_zero`): `f` is invertible in `𝒲_σ` iff its
  Bohr evaluation vanishes at no point of the polydisk.  A unit has no zero in the closed
  half-plane `Re s ≥ σ` (`lSeries_ne_zero_of_isUnit`).
* **Towers** (`isUnit_iff_of_tower`): for `f` supported on the powers of one prime `p`, `f` is a
  unit iff its local series `Σ_k f(p^k) p^{−kσ} z^k` has no zero in the closed unit disk.
* **Local Euler factors of every degree** (`isUnit_prod_localFactor_iff`): the convolution
  `Π_i (δ₁ − α_i δ_p)` is a unit iff every Satake parameter satisfies `|α_i| < p^σ`.  At
  `σ = ½` this is the threshold `√p` of the critical Wiener monoid, in every degree.

The general criterion is the polydisk, not the half-plane: the half-plane only reaches the
points `ω(p) = p^{σ−s}` whose radii are tied together by one `Re s`.
-/

open ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### Bohr points and Bohr evaluation -/

/-- A point of the Bohr polydisk: a completely multiplicative `ω : ℕ → ℂ` with `|ω| ≤ 1`. -/
structure BohrPoint where
  /-- The completely multiplicative function. -/
  ω : ℕ → ℂ
  map_one : ω 1 = 1
  map_mul : ∀ m n, ω (m * n) = ω m * ω n
  norm_le_one : ∀ n, ‖ω n‖ ≤ 1

/-- The Bohr evaluation `Σ_n f(n) ω(n) n^{−σ}`. -/
def bohrEval (σ : ℝ) (f : ArithmeticFunction ℂ) (ω : BohrPoint) : ℂ :=
  LSeries (fun n => f n * ω.ω n) σ

theorem lSeriesSummable_twist {σ : ℝ} {f : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (ω : BohrPoint) : LSeriesSummable (fun n => f n * ω.ω n) σ := by
  rw [← summable_norm_term_iff] at hf ⊢
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le σ ?_) hf
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (ω.norm_le_one n)

/-- Twisting by a completely multiplicative function commutes with Dirichlet convolution. -/
theorem twist_mul (f g : ArithmeticFunction ℂ) (ω : BohrPoint) :
    (fun n => (f * g) n * ω.ω n) = (fun n => f n * ω.ω n) ⍟ (fun n => g n * ω.ω n) := by
  funext n
  rw [LSeries.convolution_def, mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.1 hx).1, ω.map_mul]
  ring

/-- **Bohr evaluations are multiplicative.** -/
theorem bohrEval_mul {σ : ℝ} {f g : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) :
    bohrEval σ (f * g) ω = bohrEval σ f ω * bohrEval σ g ω := by
  unfold bohrEval
  rw [twist_mul]
  exact LSeries_convolution' (lSeriesSummable_twist hf ω) (lSeriesSummable_twist hg ω)

theorem bohrEval_one (σ : ℝ) (ω : BohrPoint) : bohrEval σ 1 ω = 1 := by
  unfold bohrEval LSeries
  rw [tsum_eq_single 1]
  · simp [ω.map_one]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · rw [term_of_ne_zero h0, one_apply_ne hn, zero_mul, zero_div]

theorem bohrEval_add {σ : ℝ} {f g : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) :
    bohrEval σ (f + g) ω = bohrEval σ f ω + bohrEval σ g ω := by
  unfold bohrEval
  rw [← LSeries_add (lSeriesSummable_twist hf ω) (lSeriesSummable_twist hg ω)]
  congr 1
  funext n
  simp [add_mul]

theorem bohrEval_smul (σ : ℝ) (c : ℂ) (f : ArithmeticFunction ℂ) (ω : BohrPoint) :
    bohrEval σ (c • f) ω = c * bohrEval σ f ω := by
  unfold bohrEval
  rw [← LSeries_smul]
  congr 1
  funext n
  simp [mul_assoc]

namespace WienerAlgebraAt

variable {σ : ℝ}

/-- The Bohr evaluation at `ω` as a character of `𝒲_σ`. -/
def bohrCharacter (σ : ℝ) (ω : BohrPoint) : WienerAlgebraAt σ →ₐ[ℂ] ℂ where
  toFun f := bohrEval σ f.toFn ω
  map_one' := bohrEval_one σ ω
  map_mul' f g := bohrEval_mul f.summable g.summable ω
  map_zero' := by simp [bohrEval, toFn_zero, LSeries, term_def]
  map_add' f g := bohrEval_add f.summable g.summable ω
  commutes' c := by
    show bohrEval σ (algebraMap ℂ (ArithmeticFunction ℂ) c) ω = c
    rw [Algebra.algebraMap_eq_smul_one, bohrEval_smul, bohrEval_one, mul_one]

theorem bohrCharacter_apply (ω : BohrPoint) (f : WienerAlgebraAt σ) :
    bohrCharacter σ ω f = bohrEval σ f.toFn ω := rfl

/-! ### Every character is a Bohr evaluation -/

/-- `n^σ` as a complex number. -/
theorem norm_natCast_cpow (n : ℕ) (hn : n ≠ 0) : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ σ := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re]

/-- The Bohr point of a continuous character: `ω(n) = φ(δ_n) n^σ`. -/
def characterBohrPoint (φ : WeakDual.characterSpace ℂ (WienerAlgebraAt σ)) : BohrPoint where
  ω n := if n = 0 then 0 else φ (pointMass n) * (n : ℂ) ^ (σ : ℂ)
  map_one := by
    rw [if_neg one_ne_zero, pointMass_one, map_one, Nat.cast_one, Complex.one_cpow, mul_one]
  map_mul m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, ← pointMass_mul, map_mul,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  norm_le_one n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg hn, norm_mul, norm_natCast_cpow n hn]
    have h1 : ‖φ (pointMass n)‖ ≤ (n : ℝ) ^ (-σ) := by
      rw [← norm_pointMass (σ := σ) hn]
      exact spectrum.norm_le_norm_of_mem (AlgHom.apply_mem_spectrum φ _)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc ‖φ (pointMass n)‖ * (n : ℝ) ^ σ ≤ (n : ℝ) ^ (-σ) * (n : ℝ) ^ σ :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn0.le σ)
      _ = 1 := by rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]

/-- **Every continuous character of `𝒲_σ` is a Bohr evaluation.** -/
theorem apply_eq_bohrEval (φ : WeakDual.characterSpace ℂ (WienerAlgebraAt σ))
    (f : WienerAlgebraAt σ) : φ f = bohrEval σ f.toFn (characterBohrPoint φ) := by
  have h := (hasSum_pointMass f).map φ (map_continuous φ)
  have h' : HasSum (fun n => term (fun n => f.toFn n * (characterBohrPoint φ).ω n) σ n) (φ f) := by
    refine h.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [Function.comp_apply, map_smul, smul_eq_mul]
      rw [term_of_ne_zero hn]
      show f.toFn n * (if n = 0 then 0 else φ (pointMass n) * (n : ℂ) ^ (σ : ℂ)) /
        (n : ℂ) ^ (σ : ℂ) = _
      rw [if_neg hn, ← mul_assoc, mul_div_cancel_right₀]
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h0 => hn (by exact_mod_cast h0.1)
  exact h'.tsum_eq.symm

/-! ### Wiener's lemma -/

/-- **Wiener's lemma for `𝒲_σ`.**  An element is invertible iff its Bohr evaluation vanishes at no
point of the Bohr polydisk. -/
theorem isUnit_iff_forall_bohrEval_ne_zero (f : WienerAlgebraAt σ) :
    IsUnit f ↔ ∀ ω : BohrPoint, bohrEval σ f.toFn ω ≠ 0 := by
  constructor
  · rintro hf ω h0
    obtain ⟨g, hg⟩ := hf.exists_right_inv
    have h := congrArg (bohrCharacter σ ω) hg
    rw [map_mul, map_one, bohrCharacter_apply, h0, zero_mul] at h
    exact zero_ne_one h
  · intro h
    by_contra hf
    obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hf
    exact h _ ((apply_eq_bohrEval φ f).symm.trans hφ)

/-- The Bohr point `ω(n) = n^{σ−s}` of a point `s` of the closed half-plane `Re s ≥ σ`. -/
def halfPlanePoint (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) : BohrPoint where
  ω n := if n = 0 then 0 else (n : ℂ) ^ ((σ : ℂ) - s)
  map_one := by simp
  map_mul m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
  norm_le_one n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg hn, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn) ?_
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

theorem bohrEval_halfPlanePoint (f : ArithmeticFunction ℂ) (s : ℂ) (hs : σ ≤ s.re) :
    bohrEval σ f (halfPlanePoint σ s hs) = LSeries (⇑f) s := by
  unfold bohrEval LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [term_of_ne_zero hn, term_of_ne_zero hn]
  show f n * (if n = 0 then 0 else (n : ℂ) ^ ((σ : ℂ) - s)) / (n : ℂ) ^ (σ : ℂ) = f n / (n : ℂ) ^ s
  rw [if_neg hn, Complex.cpow_sub _ _ hn']
  have h1 : (n : ℂ) ^ (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hn' h.1
  have h2 : (n : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hn' h.1
  field_simp

/-- **A unit has no zero in the closed half-plane `Re s ≥ σ`.** -/
theorem lSeries_ne_zero_of_isUnit {f : WienerAlgebraAt σ} (hf : IsUnit f) {s : ℂ}
    (hs : σ ≤ s.re) : LSeries (⇑f.toFn) s ≠ 0 := by
  rw [← bohrEval_halfPlanePoint f.toFn s hs]
  exact (isUnit_iff_forall_bohrEval_ne_zero f).1 hf _

/-! ### Towers and local Euler factors -/

theorem _root_.GaloisForLFunctions.ArithmeticOrientationTheory.BohrPoint.map_pow (ω : BohrPoint)
    (n k : ℕ) : ω.ω (n ^ k) = ω.ω n ^ k := by
  induction k with
  | zero => simp [ω.map_one]
  | succ k ih => rw [pow_succ, ω.map_mul, ih, pow_succ]

/-- `n` is a power of the prime `p` iff `p^{v_p(n)} = n`. -/
theorem pow_factorization_eq_iff {p : ℕ} (hp : p.Prime) {n : ℕ} :
    p ^ n.factorization p = n ↔ ∃ k, n = p ^ k := by
  constructor
  · exact fun h => ⟨_, h.symm⟩
  · rintro ⟨k, rfl⟩
    rw [hp.factorization_pow, Finsupp.single_eq_same]

/-- The tower Bohr point at `p` with `ω(p) = z`: `ω(p^k) = z^k`, zero off the powers of `p`. -/
def towerPoint {p : ℕ} (hp : p.Prime) (z : ℂ) (hz : ‖z‖ ≤ 1) : BohrPoint where
  ω n := if p ^ n.factorization p = n then z ^ n.factorization p else 0
  map_one := by simp
  map_mul m n := by
    by_cases hm : ∃ a, m = p ^ a
    · by_cases hn : ∃ b, n = p ^ b
      · obtain ⟨a, rfl⟩ := hm
        obtain ⟨b, rfl⟩ := hn
        rw [← pow_add, if_pos ((pow_factorization_eq_iff hp).2 ⟨a + b, rfl⟩),
          if_pos ((pow_factorization_eq_iff hp).2 ⟨a, rfl⟩),
          if_pos ((pow_factorization_eq_iff hp).2 ⟨b, rfl⟩), hp.factorization_pow,
          hp.factorization_pow, hp.factorization_pow, Finsupp.single_eq_same,
          Finsupp.single_eq_same, Finsupp.single_eq_same, pow_add]
      · have hmn : ¬ ∃ k, m * n = p ^ k := by
          rintro ⟨k, hk⟩
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left m hk)
          exact hn ⟨i, hi⟩
        rw [if_neg (mt (pow_factorization_eq_iff hp).1 hmn),
          if_neg (mt (pow_factorization_eq_iff hp).1 hn), mul_zero]
    · have hmn : ¬ ∃ k, m * n = p ^ k := by
        rintro ⟨k, hk⟩
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro n hk)
        exact hm ⟨i, hi⟩
      rw [if_neg (mt (pow_factorization_eq_iff hp).1 hmn),
        if_neg (mt (pow_factorization_eq_iff hp).1 hm), zero_mul]
  norm_le_one n := by
    split_ifs
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
    · simp

theorem towerPoint_prime {p : ℕ} (hp : p.Prime) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (towerPoint hp z hz).ω p = z := by
  show (if p ^ p.factorization p = p then z ^ p.factorization p else 0) = z
  rw [hp.factorization_self, pow_one, if_pos rfl, pow_one]

/-- The Bohr evaluation of a tower-supported function is its local series at `z = ω(p)`. -/
theorem bohrEval_of_tower {p : ℕ} (hp : p.Prime) {f : ArithmeticFunction ℂ}
    (hf : ∀ n, (∀ k, n ≠ p ^ k) → f n = 0) (ω : BohrPoint) :
    bohrEval σ f ω = ∑' k : ℕ, f (p ^ k) * ω.ω p ^ k / ((p ^ k : ℕ) : ℂ) ^ (σ : ℂ) := by
  unfold bohrEval LSeries
  rw [← (Nat.pow_right_injective hp.two_le).tsum_eq]
  · refine tsum_congr fun k => ?_
    rw [term_of_ne_zero (pow_ne_zero k hp.ne_zero), BohrPoint.map_pow]
  · intro n hn
    by_contra h
    apply hn
    have h' : ∀ k, n ≠ p ^ k := fun k hk => h ⟨k, hk.symm⟩
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · rw [term_of_ne_zero h0, hf n h', zero_mul, zero_div]

/-- **Wiener's lemma for towers.**  An element supported on the powers of a prime `p` is a unit
of `𝒲_σ` iff its local series `Σ_k f(p^k) p^{−kσ} z^k` has no zero in the closed unit disk. -/
theorem isUnit_iff_of_tower {p : ℕ} (hp : p.Prime) (f : WienerAlgebraAt σ)
    (hf : ∀ n, (∀ k, n ≠ p ^ k) → f.toFn n = 0) :
    IsUnit f ↔ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ∑' k : ℕ, f.toFn (p ^ k) * z ^ k / ((p ^ k : ℕ) : ℂ) ^ (σ : ℂ) ≠ 0 := by
  rw [isUnit_iff_forall_bohrEval_ne_zero]
  constructor
  · intro h z hz
    have := h (towerPoint hp z hz)
    rwa [bohrEval_of_tower hp hf, towerPoint_prime] at this
  · intro h ω
    rw [bohrEval_of_tower hp hf]
    exact h _ (ω.norm_le_one p)

/-- The complex local factor `δ₁ − α δ_p` in `𝒲_σ`. -/
def localFactor (p : ℕ) (α : ℂ) : WienerAlgebraAt σ := 1 - α • pointMass p

theorem bohrEval_pointMass {n : ℕ} (hn : n ≠ 0) (ω : BohrPoint) :
    bohrEval σ (pointMassFn n) ω = ω.ω n / (n : ℂ) ^ (σ : ℂ) := by
  unfold bohrEval LSeries
  rw [tsum_eq_single n]
  · rw [term_of_ne_zero hn, pointMassFn_apply, if_pos ⟨hn, rfl⟩, one_mul]
  · intro m hm
    rcases eq_or_ne m 0 with rfl | h0
    · simp
    · rw [term_of_ne_zero h0, pointMassFn_apply, if_neg (fun h => hm h.2), zero_mul, zero_div]

theorem bohrCharacter_localFactor {p : ℕ} (hp : p ≠ 0) (α : ℂ) (ω : BohrPoint) :
    bohrCharacter σ ω (localFactor p α) = 1 - α * ω.ω p / (p : ℂ) ^ (σ : ℂ) := by
  rw [localFactor, map_sub, map_one, map_smul, bohrCharacter_apply, toFn_pointMass,
    bohrEval_pointMass hp, smul_eq_mul, mul_div_assoc]

/-- **The unit law for complex local factors**: `δ₁ − α δ_p` is a unit of `𝒲_σ` iff
`|α| < p^σ`. -/
theorem isUnit_localFactor_iff {p : ℕ} (hp : p.Prime) (α : ℂ) :
    IsUnit (localFactor p α : WienerAlgebraAt σ) ↔ ‖α‖ < (p : ℝ) ^ σ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpσ : ‖(p : ℂ) ^ (σ : ℂ)‖ = (p : ℝ) ^ σ := norm_natCast_cpow p hp.ne_zero
  have hpσ0 : (p : ℂ) ^ (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hp.ne_zero (by exact_mod_cast h.1)
  rw [isUnit_iff_forall_bohrEval_ne_zero]
  simp_rw [← bohrCharacter_apply, bohrCharacter_localFactor hp.ne_zero]
  constructor
  · intro h
    by_contra hα
    rw [not_lt] at hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hα
      exact absurd hα (not_le.2 (Real.rpow_pos_of_pos hp0 σ))
    have hz : ‖(p : ℂ) ^ (σ : ℂ) / α‖ ≤ 1 := by
      rw [norm_div, hpσ, div_le_one (norm_pos_iff.2 hα0)]
      exact hα
    have := h (towerPoint hp _ hz)
    rw [towerPoint_prime] at this
    apply this
    field_simp
    ring
  · intro h ω h0
    have h1 : α * ω.ω p / (p : ℂ) ^ (σ : ℂ) = 1 := by linear_combination -h0
    have h2 : ‖α * ω.ω p / (p : ℂ) ^ (σ : ℂ)‖ < 1 := by
      rw [norm_div, norm_mul, hpσ, div_lt_one (Real.rpow_pos_of_pos hp0 σ)]
      calc ‖α‖ * ‖ω.ω p‖ ≤ ‖α‖ * 1 := mul_le_mul_of_nonneg_left (ω.norm_le_one p) (norm_nonneg _)
        _ < (p : ℝ) ^ σ := by rw [mul_one]; exact h
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2

/-- **Local Euler factors of every degree.**  The convolution `Π_i (δ₁ − α_i δ_p)` of the local
factors with Satake parameters `α_i` is a unit of `𝒲_σ` iff `|α_i| < p^σ` for every `i`. -/
theorem isUnit_prod_localFactor_iff {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (α : ι → ℂ) :
    IsUnit (∏ i ∈ s, (localFactor p (α i) : WienerAlgebraAt σ)) ↔
      ∀ i ∈ s, ‖α i‖ < (p : ℝ) ^ σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, IsUnit.mul_iff, isUnit_localFactor_iff hp, ih,
      Finset.forall_mem_insert]

end WienerAlgebraAt

end

end GaloisForLFunctions.ArithmeticOrientationTheory
