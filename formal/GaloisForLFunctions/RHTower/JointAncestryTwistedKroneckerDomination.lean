import GaloisForLFunctions.RHTower.JointAncestryBernoulliAggregate
import GaloisForLFunctions.RHTower.JointAncestryDressedSectorGapLaw
import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorKroneckerAmplification

/-!
# Twisted Kronecker points: on-line sectors cannot compensate an off-line pair

Fix a strip point `ρ = β + iγ` with `β < 1/2` and a dressing `0 ≤ c ≤ 1 - β`.  At the twisted
Kronecker point `z_p = e^{iφ} p^{iγ}` the Bernoulli factor of `ρ` is

`G_p(φ) = 2 + r₁ e^{iφ} + r₂ e^{-iφ}`,   `r₁ = p^{-(β + c)}`, `r₂ = p^{-(1 - β + c)}`.

Its phase is at least `(r₁ - r₂) sin φ / 4` and its modulus at least `2 + r₁ cos φ`.  Because
`Σ_p r₁ = ∞`, a uniform twist accumulates any prescribed total phase in `[0, 2π)`, and since the
phase grows linearly in `sin φ` the twist needed is small, so the modulus keeps most of its
Kronecker amplitude.  On-line Bernoulli factors are real and at most `2(1 + p^{-(1/2 + c)})`, and
`r₁ / p^{-(1/2+c)} = p^{1/2 - β}` is unbounded, so the off-line amplitude beats every on-line
amplitude by an arbitrary factor.

Consequently a Bernoulli mixture of on-line sectors with total weight `Λ` plus one off-line pair
`w G + conj (w G)` is negative at a suitable twisted Kronecker point, whatever `Λ` and `w ≠ 0`.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## The twisted local value -/

/-- `2 + r₁ e^{iφ} + r₂ e^{-iφ}`. -/
def jasTwistedValue (r₁ r₂ φ : ℝ) : ℂ :=
  2 + (r₁ : ℂ) * cexp ((φ : ℂ) * I) + (r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)

theorem re_jasTwistedValue (r₁ r₂ φ : ℝ) :
    (jasTwistedValue r₁ r₂ φ).re = 2 + (r₁ + r₂) * Real.cos φ := by
  simp only [jasTwistedValue, Complex.add_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Real.cos_neg]
  norm_num
  ring

theorem im_jasTwistedValue (r₁ r₂ φ : ℝ) :
    (jasTwistedValue r₁ r₂ φ).im = (r₁ - r₂) * Real.sin φ := by
  simp only [jasTwistedValue, Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    Real.sin_neg]
  norm_num
  ring

theorem re_jasTwistedValue_pos {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂)
    (h₂' : r₂ < 1) (φ : ℝ) : 0 < (jasTwistedValue r₁ r₂ φ).re := by
  rw [re_jasTwistedValue]
  have := Real.neg_one_le_cos φ
  have := Real.cos_le_one φ
  nlinarith

theorem norm_jasTwistedValue_le {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ ≤ 1) (h₂ : 0 ≤ r₂)
    (h₂' : r₂ ≤ 1) (φ : ℝ) : ‖jasTwistedValue r₁ r₂ φ‖ ≤ 4 := by
  have e₁ : ‖(r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ = r₁ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₁]
  have e₂ : ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ = r₂ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₂]
  calc ‖jasTwistedValue r₁ r₂ φ‖
      ≤ ‖(2 : ℂ) + (r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ + ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ :=
        norm_add_le _ _
    _ ≤ ‖(2 : ℂ)‖ + ‖(r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ + ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 4 := by rw [e₁, e₂]; norm_num; linarith

theorem le_norm_jasTwistedValue {r₁ r₂ : ℝ} (h₂ : 0 ≤ r₂) {φ : ℝ}
    (hφ : 0 ≤ Real.cos φ) : 2 + r₁ * Real.cos φ ≤ ‖jasTwistedValue r₁ r₂ φ‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [re_jasTwistedValue]
  nlinarith

theorem jasTwistedValue_zero_arg (r₁ r₂ : ℝ) (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) :
    (jasTwistedValue r₁ r₂ 0).arg = 0 := by
  have him : (jasTwistedValue r₁ r₂ 0).im = 0 := by rw [im_jasTwistedValue]; simp
  have hre : 0 < (jasTwistedValue r₁ r₂ 0).re := by rw [re_jasTwistedValue]; simp; positivity
  rw [Complex.arg_eq_zero_iff]
  exact ⟨hre.le, him⟩

/-- **Phase growth.**  `arg G(φ) ≥ (r₁ - r₂) sin φ / 4` on `[0, π/2]`. -/
theorem arg_jasTwistedValue_ge {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂)
    (h₁₂ : r₂ ≤ r₁) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ Real.pi / 2) :
    (r₁ - r₂) * Real.sin φ / 4 ≤ (jasTwistedValue r₁ r₂ φ).arg := by
  set G := jasTwistedValue r₁ r₂ φ
  have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have him : 0 ≤ G.im := by rw [im_jasTwistedValue]; exact mul_nonneg (by linarith) hsin
  have hargnn : 0 ≤ G.arg := Complex.arg_nonneg_iff.mpr him
  have hre := re_jasTwistedValue_pos h₁ h₁' h₂ (by linarith) φ
  have hpos : 0 < ‖G‖ := lt_of_lt_of_le hre (Complex.re_le_norm _)
  have hle4 := norm_jasTwistedValue_le h₁ h₁'.le h₂ (by linarith) φ
  have h1 : (r₁ - r₂) * Real.sin φ / 4 ≤ G.im / ‖G‖ := by
    rw [im_jasTwistedValue, div_le_div_iff₀ (by norm_num) hpos]
    exact mul_le_mul_of_nonneg_left hle4 (mul_nonneg (by linarith) hsin)
  rw [← Complex.sin_arg] at h1
  exact h1.trans (Real.sin_le hargnn)

theorem continuous_arg_jasTwistedValue {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₁' : r₁ < 1) (h₂ : 0 ≤ r₂)
    (h₂' : r₂ < 1) : Continuous fun φ : ℝ => (jasTwistedValue r₁ r₂ φ).arg := by
  have hG : Continuous fun φ : ℝ => jasTwistedValue r₁ r₂ φ := by
    unfold jasTwistedValue; fun_prop
  refine continuous_iff_continuousAt.mpr fun φ => ?_
  exact (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr
    (Or.inl (re_jasTwistedValue_pos h₁ h₁' h₂ h₂' φ)))).comp hG.continuousAt

/-! ## Bernoulli factors at twisted Kronecker points -/

/-- The dressed Bernoulli factor of `ρ` at prime `p`. -/
def jasDressedBernoulli (ρ : ℂ) (c : ℝ) (p : Nat.Primes) (z : ℂ) : ℂ :=
  jasBernoulliFactor (jasHoloA (ρ + c) p) (jasHoloB (ρ - c) p) z

/-- The twisted Kronecker point `e^{iφ} p^{iγ}`. -/
def jasTwistedPoint (ρ : ℂ) (φ : ℝ) (p : Nat.Primes) : ℂ :=
  cexp ((φ : ℂ) * I) * jasKroneckerPoint ρ p

theorem norm_jasTwistedPoint (ρ : ℂ) (φ : ℝ) (p : Nat.Primes) : ‖jasTwistedPoint ρ φ p‖ = 1 := by
  rw [jasTwistedPoint, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_jasKroneckerPoint, one_mul]

theorem jasKroneckerPoint_congr_im {s₁ s₂ : ℂ} (h : s₁.im = s₂.im) (p : Nat.Primes) :
    jasKroneckerPoint s₁ p = jasKroneckerPoint s₂ p := by
  unfold jasKroneckerPoint; rw [h]

theorem jasDressedBernoulli_twisted (ρ : ℂ) (c φ : ℝ) (p : Nat.Primes) :
    jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p) =
      jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ := by
  have hK₁ : jasKroneckerPoint ρ p = jasKroneckerPoint (ρ + c) p :=
    jasKroneckerPoint_congr_im (by simp) p
  have hK₂ : jasKroneckerPoint ρ p = jasKroneckerPoint (ρ - c) p :=
    jasKroneckerPoint_congr_im (by simp) p
  have hA : jasTwistedPoint ρ φ p * jasHoloA (ρ + c) p = (jasR1 (ρ + c) p : ℂ) * cexp ((φ : ℂ) * I) := by
    rw [jasTwistedPoint, hK₁, mul_assoc, mul_comm (jasKroneckerPoint _ p), jasHoloA_mul_kronecker,
      mul_comm]
  have hconj : conj (cexp ((φ : ℂ) * I)) = cexp (((-φ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]; congr 1; simp
  have hB : conj (jasTwistedPoint ρ φ p) * jasHoloB (ρ - c) p =
      (jasR2 (ρ - c) p : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) := by
    rw [jasTwistedPoint, map_mul, hconj, hK₂, mul_assoc, mul_comm (conj _),
      jasHoloB_mul_conj_kronecker, mul_comm]
  have hzz : jasTwistedPoint ρ φ p * conj (jasTwistedPoint ρ φ p) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_jasTwistedPoint]; simp
  rw [jasDressedBernoulli, jasBernoulliFactor, hA, hB, hzz, jasTwistedValue]
  ring

/-! ## On-line Bernoulli factors -/

/-- The critical radius `p^{-(1/2 + c)}`. -/
def jasCriticalRadius (c : ℝ) (p : Nat.Primes) : ℝ := Real.exp (-(1 / 2 + c) * Real.log p)

theorem jasHoloB_eq_conj_jasHoloA_dressed {q : ℂ} (hq : q.re = 1 / 2) (c : ℝ) (p : Nat.Primes) :
    jasHoloB (q - c) p = conj (jasHoloA (q + c) p) := by
  rw [jasHoloB, jasHoloA, ← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
      Complex.conj_ofReal, hq]
    ring
  · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
      Complex.conj_ofReal, hq]
    ring

theorem norm_jasHoloA_dressed_critical {q : ℂ} (hq : q.re = 1 / 2) (c : ℝ) (p : Nat.Primes) :
    ‖jasHoloA (q + c) p‖ = jasCriticalRadius c p := by
  rw [norm_jasHoloA, jasCriticalRadius]
  congr 2
  simp [hq]

/-- On the critical line the Bernoulli factor at a unit point is real, positive and at most
`2(1 + p^{-(1/2+c)})`. -/
theorem jasDressedBernoulli_critical {q : ℂ} (hq : q.re = 1 / 2) {c : ℝ} (hc : 0 ≤ c)
    (p : Nat.Primes) {z : ℂ} (hz : ‖z‖ = 1) :
    jasDressedBernoulli q c p z = ((2 + 2 * (z * jasHoloA (q + c) p).re : ℝ) : ℂ) ∧
      0 < 2 + 2 * (z * jasHoloA (q + c) p).re ∧
      2 + 2 * (z * jasHoloA (q + c) p).re ≤ 2 + 2 * jasCriticalRadius c p := by
  set A := jasHoloA (q + c) p
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have hnorm : ‖z * A‖ = jasCriticalRadius c p := by
    rw [norm_mul, hz, one_mul, norm_jasHoloA_dressed_critical hq]
  have hr : jasCriticalRadius c p < 1 := by
    rw [jasCriticalRadius, Real.exp_lt_one_iff]
    nlinarith [log_prime_pos p]
  have hre := Complex.abs_re_le_norm (z * A)
  rw [hnorm] at hre
  refine ⟨?_, ?_, ?_⟩
  · rw [jasDressedBernoulli, jasBernoulliFactor, jasHoloB_eq_conj_jasHoloA_dressed hq, hzz]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      rw [show conj z * conj A = conj (z * A) by rw [map_mul], Complex.conj_re]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im]
      rw [show conj z * conj A = conj (z * A) by rw [map_mul], Complex.conj_im]
      ring
  · linarith [neg_abs_le (z * A).re]
  · linarith [le_abs_self (z * A).re]

/-! ## Domination at a twisted Kronecker point -/

theorem exists_finset_sum_ge_of_not_summable {α : Type*} {f : α → ℝ} (hf : 0 ≤ f)
    (hns : ¬ Summable f) (T : ℝ) : ∃ s : Finset α, T ≤ ∑ x ∈ s, f x := by
  by_contra h
  push Not at h
  exact hns (summable_of_sum_le hf fun u => (h u).le)

/-- **Twisted Kronecker domination.**  For an off-line strip point with `β < 1/2` and a dressing
`0 ≤ c ≤ 1 - β`, for every unit direction `ω` and every factor `M` there is a finite prime set and a
twisted Kronecker point at which the Bernoulli product of `ρ` points exactly against `ω` and exceeds
`M` times the largest possible on-line Bernoulli product. -/
theorem exists_twisted_kronecker_domination {ρ : ℂ} (h0 : 0 < ρ.re) (hβ : ρ.re < 1 / 2)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 - ρ.re) {ω : ℂ} (hω : ‖ω‖ = 1) (M : ℝ) :
    ∃ (P : Finset Nat.Primes) (φ : ℝ),
      (ω * ∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p)).re =
        -‖∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p)‖ ∧
      M * ∏ p ∈ P, (2 + 2 * jasCriticalRadius c p) ≤
        ‖∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p)‖ := by
  classical
  set δ := 1 / 2 - ρ.re with hδ
  have hδ0 : 0 < δ := by linarith
  set r₁ : Nat.Primes → ℝ := fun p => jasR1 (ρ + c) p with hr₁
  set r₂ : Nat.Primes → ℝ := fun p => jasR2 (ρ - c) p with hr₂
  set r₀ : Nat.Primes → ℝ := fun p => jasCriticalRadius c p with hr₀
  have hr₀e : ∀ p : Nat.Primes, r₀ p = Real.exp (-(1 / 2 + c) * Real.log p) := fun p => rfl
  have hr₁e : ∀ p, r₁ p = Real.exp (-(ρ.re + c) * Real.log p) := fun p => jasR1_dressed ρ c p
  have hr₂e : ∀ p, r₂ p = Real.exp (-(1 - ρ.re + c) * Real.log p) := fun p => jasR2_dressed ρ c p
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => by rw [hr₁e]; positivity
  have hr₂0 : ∀ p, 0 ≤ r₂ p := fun p => by rw [hr₂e]; positivity
  have hr₁1 : ∀ p, r₁ p < 1 := fun p => by
    rw [hr₁e, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hr₂1 : ∀ p, r₂ p < 1 := fun p => by
    rw [hr₂e, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  -- threshold prime: `p^δ ≥ 8`
  set p₀ : ℕ := ⌈Real.exp (Real.log 8 / δ)⌉₊ with hp₀
  have hbig : ∀ p : Nat.Primes, p₀ ≤ (p : ℕ) → Real.log 8 ≤ δ * Real.log p := by
    intro p hp
    have h1 : Real.exp (Real.log 8 / δ) ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp)
    have h2 : Real.log 8 / δ ≤ Real.log p := by
      rw [← Real.log_exp (Real.log 8 / δ)]
      exact Real.log_le_log (Real.exp_pos _) h1
    rw [div_le_iff₀ hδ0] at h2
    linarith
  have hratio : ∀ p : Nat.Primes, p₀ ≤ (p : ℕ) → 8 * r₀ p ≤ r₁ p := by
    intro p hp
    have h := hbig p hp
    rw [hr₁e, hr₀e,
      show (8 : ℝ) = Real.exp (Real.log 8) by rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [hδ] at h; nlinarith)
  have hgap : ∀ p : Nat.Primes, p₀ ≤ (p : ℕ) → r₁ p / 2 ≤ r₁ p - r₂ p := by
    intro p hp
    have h := hbig p hp
    have hsplit : r₂ p = r₁ p * Real.exp (-(2 * δ) * Real.log p) := by
      rw [hr₁e, hr₂e, ← Real.exp_add]; congr 1; rw [hδ]; ring
    have hsmall : Real.exp (-(2 * δ) * Real.log p) ≤ 1 / 2 := by
      have : Real.exp (-(2 * δ) * Real.log p) ≤ Real.exp (-Real.log 8) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.log_pos (show (1 : ℝ) < 8 by norm_num)])
      rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
      linarith
    rw [hsplit]
    nlinarith [hr₁0 p]
  -- divergence of `Σ_{p ≥ p₀} r₁`
  set f : Nat.Primes → ℝ := fun p => if p₀ ≤ (p : ℕ) then r₁ p else 0 with hf
  have hf0 : 0 ≤ f := fun p => by simp only [hf]; split <;> simp [hr₁0 p]
  have hns : ¬ Summable f := by
    intro hs
    apply Nat.Primes.not_summable_one_div
    refine Summable.of_norm_bounded_eventually hs ?_
    have hfin : {p : Nat.Primes | (p : ℕ) < p₀}.Finite :=
      (Set.finite_lt_nat p₀).preimage Subtype.val_injective.injOn
    refine Filter.eventually_cofinite.mpr (hfin.subset fun p hp => ?_)
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra hlt
    push Not at hlt
    apply hp
    simp only [hf, if_pos hlt]
    rw [Real.norm_of_nonneg (by positivity), hr₁e,
      show 1 / ((p : ℕ) : ℝ) = Real.exp (-Real.log p) by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos), one_div]]
    exact Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])
  set R : ℝ := max (32 * Real.pi) (16 * max M 1) with hR
  obtain ⟨s, hs⟩ := exists_finset_sum_ge_of_not_summable hf0 hns R
  set P := s.filter (fun p : Nat.Primes => p₀ ≤ (p : ℕ)) with hP
  have hPbig : ∀ p ∈ P, p₀ ≤ (p : ℕ) := fun p hp => (Finset.mem_filter.mp hp).2
  have hSR : R ≤ ∑ p ∈ P, r₁ p := by
    rw [hP, Finset.sum_filter]
    exact hs
  have hR32 : 32 * Real.pi ≤ R := le_max_left _ _
  have hRM : 16 * max M 1 ≤ R := le_max_right _ _
  -- total phase
  set Θ : ℝ → ℝ := fun φ => ∑ p ∈ P, (jasTwistedValue (r₁ p) (r₂ p) φ).arg with hΘ
  have hΘcont : Continuous Θ :=
    continuous_finsetSum _ fun p _ =>
      continuous_arg_jasTwistedValue (hr₁0 p) (hr₁1 p) (hr₂0 p) (hr₂1 p)
  have hΘ0 : Θ 0 = 0 :=
    Finset.sum_eq_zero fun p _ => jasTwistedValue_zero_arg _ _ (hr₁0 p) (hr₂0 p)
  have hΘge : ∀ φ, 0 ≤ φ → φ ≤ Real.pi / 2 → Real.sin φ * (R / 8) ≤ Θ φ := by
    intro φ h0φ h1φ
    have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi h0φ (by linarith [Real.pi_pos])
    calc Real.sin φ * (R / 8) ≤ Real.sin φ * (∑ p ∈ P, r₁ p / 8) := by
          rw [← Finset.sum_div]; gcongr
      _ = ∑ p ∈ P, (r₁ p / 2) * Real.sin φ / 4 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ P, (r₁ p - r₂ p) * Real.sin φ / 4 :=
          Finset.sum_le_sum fun p hp => by
            have := hgap p (hPbig p hp); gcongr
      _ ≤ Θ φ := Finset.sum_le_sum fun p hp =>
          arg_jasTwistedValue_ge (hr₁0 p) (hr₁1 p) (hr₂0 p)
            (by linarith [hgap p (hPbig p hp), hr₁0 p]) h0φ h1φ
  -- target phase
  set θ : ℝ := Real.pi - ω.arg with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Complex.arg_le_pi ω]
  have hθ1 : θ < 2 * Real.pi := by rw [hθ]; linarith [Complex.neg_pi_lt_arg ω]
  have hΘtop : θ ≤ Θ (Real.pi / 2) := by
    have := hΘge (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl
    rw [Real.sin_pi_div_two, one_mul] at this
    linarith [Real.pi_pos]
  obtain ⟨φ, ⟨hφ0, hφ1⟩, hΘφ⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)
    hΘcont.continuousOn ⟨by rw [hΘ0]; exact hθ0, hΘtop⟩
  -- the twist is small
  have hsinφ : Real.sin φ ≤ 1 / 2 := by
    have h := hΘge φ hφ0 hφ1
    rw [hΘφ] at h
    have hR0 : 0 < R / 8 := by linarith [Real.pi_pos]
    have : Real.sin φ ≤ θ / (R / 8) := by rw [le_div_iff₀ hR0]; linarith
    calc Real.sin φ ≤ θ / (R / 8) := this
      _ ≤ (2 * Real.pi) / (32 * Real.pi / 8) := by
          gcongr
      _ = 1 / 2 := by field_simp; ring
  have hcosφ : 1 / 2 ≤ Real.cos φ := by
    have hc0' : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
    have hsq := Real.cos_sq_add_sin_sq φ
    have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
    nlinarith
  have hprodeq : ∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p) =
      ∏ p ∈ P, jasTwistedValue (r₁ p) (r₂ p) φ :=
    Finset.prod_congr rfl fun p _ => jasDressedBernoulli_twisted ρ c φ p
  refine ⟨P, φ, ?_, ?_⟩
  · -- exact anti-alignment
    rw [hprodeq, norm_prod]
    have hpolar := prod_eq_prod_norm_mul_exp_sum_arg P (fun p => jasTwistedValue (r₁ p) (r₂ p) φ)
    change ∏ p ∈ P, jasTwistedValue (r₁ p) (r₂ p) φ =
      ((∏ p ∈ P, ‖jasTwistedValue (r₁ p) (r₂ p) φ‖ : ℝ) : ℂ) * cexp ((Θ φ : ℂ) * I) at hpolar
    rw [hpolar, hΘφ, hθ]
    have hω' : ω = cexp ((ω.arg : ℂ) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ω, hω]
      simp
    nth_rw 1 [hω']
    have hexp : cexp ((ω.arg : ℂ) * I) *
        (((∏ p ∈ P, ‖jasTwistedValue (r₁ p) (r₂ p) φ‖ : ℝ) : ℂ) *
          cexp (((Real.pi - ω.arg : ℝ) : ℂ) * I)) =
        -(((∏ p ∈ P, ‖jasTwistedValue (r₁ p) (r₂ p) φ‖ : ℝ) : ℂ)) := by
      rw [mul_left_comm, ← Complex.exp_add,
        show (ω.arg : ℂ) * I + ((Real.pi - ω.arg : ℝ) : ℂ) * I = (Real.pi : ℂ) * I by
          push_cast; ring, Complex.exp_pi_mul_I]
      ring
    rw [hexp, Complex.neg_re, Complex.ofReal_re]
  · -- amplitude
    rw [hprodeq, norm_prod]
    have hlocal : ∀ p ∈ P, (2 + 2 * r₀ p) * (1 + r₁ p / 16) ≤
        ‖jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
      intro p hp
      have h8 := hratio p (hPbig p hp)
      have hr0 : 0 ≤ r₀ p := by rw [hr₀]; exact (Real.exp_pos _).le
      have hle := le_norm_jasTwistedValue (r₁ := r₁ p) (hr₂0 p) (show 0 ≤ Real.cos φ by linarith)
      have hr11 := hr₁1 p
      have : (2 + 2 * r₀ p) * (1 + r₁ p / 16) ≤ 2 + r₁ p * Real.cos φ := by
        nlinarith [hr₁0 p]
      linarith
    have hprod : (∏ p ∈ P, (2 + 2 * r₀ p)) * (1 + ∑ p ∈ P, r₁ p / 16) ≤
        ∏ p ∈ P, ‖jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
      calc (∏ p ∈ P, (2 + 2 * r₀ p)) * (1 + ∑ p ∈ P, r₁ p / 16)
          ≤ (∏ p ∈ P, (2 + 2 * r₀ p)) * ∏ p ∈ P, (1 + r₁ p / 16) := by
            gcongr
            · exact Finset.prod_nonneg fun p _ => by
                have : 0 ≤ r₀ p := by rw [hr₀]; exact (Real.exp_pos _).le
                linarith
            · exact jas_one_add_sum_le_prod_one_add P _ fun p => by
                have := hr₁0 p; positivity
        _ = ∏ p ∈ P, (2 + 2 * r₀ p) * (1 + r₁ p / 16) := (Finset.prod_mul_distrib).symm
        _ ≤ _ := Finset.prod_le_prod (fun p _ => by
              have : 0 ≤ r₀ p := by rw [hr₀]; exact (Real.exp_pos _).le
              have := hr₁0 p
              positivity) hlocal
    have hM : M ≤ 1 + ∑ p ∈ P, r₁ p / 16 := by
      rw [← Finset.sum_div]
      have := le_max_left M 1
      linarith
    have hpos : 0 ≤ ∏ p ∈ P, (2 + 2 * r₀ p) := Finset.prod_nonneg fun p _ => by
      have : 0 ≤ r₀ p := by rw [hr₀]; exact (Real.exp_pos _).le
      linarith
    calc M * ∏ p ∈ P, (2 + 2 * jasCriticalRadius c p)
        = M * ∏ p ∈ P, (2 + 2 * r₀ p) := rfl
      _ ≤ (1 + ∑ p ∈ P, r₁ p / 16) * ∏ p ∈ P, (2 + 2 * r₀ p) := by gcongr
      _ ≤ _ := by rw [mul_comm]; exact hprod

/-- **On-line incapacity.**  A Bernoulli mixture of on-line sectors of total weight at most `Λ`
together with one off-line pair `w G_ρ + conj (w G_ρ)` is negative at some twisted Kronecker point:
on-line sectors can never compensate an off-line pair. -/
theorem exists_bernoulli_mixture_neg {ρ : ℂ} (h0 : 0 < ρ.re) (hβ : ρ.re < 1 / 2) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 1 - ρ.re) {w : ℂ} (hw : w ≠ 0) (Λ : ℝ) :
    ∃ (P : Finset Nat.Primes) (φ : ℝ),
      2 * (w * ∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p)).re +
        Λ * ∏ p ∈ P, (2 + 2 * jasCriticalRadius c p) < 0 := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ω := w / (‖w‖ : ℂ) with hωdef
  have hω : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_real, Real.norm_of_nonneg hwn.le, div_self hwn.ne']
  obtain ⟨P, φ, halign, hamp⟩ :=
    exists_twisted_kronecker_domination h0 hβ hc0 hc hω ((|Λ| + 1) / (2 * ‖w‖))
  refine ⟨P, φ, ?_⟩
  set G := ∏ p ∈ P, jasDressedBernoulli ρ c p (jasTwistedPoint ρ φ p)
  set Q := ∏ p ∈ P, (2 + 2 * jasCriticalRadius c p)
  have hQ : 0 < Q := Finset.prod_pos fun p _ => by
    have : 0 < jasCriticalRadius c p := Real.exp_pos _
    linarith
  have hwG : (w * G).re = ‖w‖ * (ω * G).re := by
    rw [show w * G = (‖w‖ : ℂ) * (ω * G) by
      rw [hωdef, ← mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast hwn.ne')], Complex.re_ofReal_mul]
  rw [hwG, halign]
  have h1 : (|Λ| + 1) / (2 * ‖w‖) * Q * (2 * ‖w‖) = (|Λ| + 1) * Q := by
    field_simp
  have h2 : (|Λ| + 1) * Q ≤ 2 * ‖w‖ * ‖G‖ := by
    rw [← h1]; nlinarith
  nlinarith [le_abs_self Λ, neg_abs_le Λ]

end

end RHTower
