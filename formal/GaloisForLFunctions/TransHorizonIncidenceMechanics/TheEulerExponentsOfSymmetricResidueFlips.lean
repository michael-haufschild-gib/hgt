import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsReadTheCriticalZeros

/-!
# The Euler exponents of symmetric residue flips

For `S ⊆ ZMod q` let `f = f_{q,S}` flip the primes whose residue lies in `S` (`residueFlip`) and put
`s_χ = Σ_{u ∈ S unit} χ(u⁻¹)` (`setCoeff`). Orthogonality gives `Σ_χ s_χ χ(b) = φ(q) [b ∈ S unit]`
(`sum_setCoeff_mul`), so at every prime
`f(p) y = y − (2/φ) Σ_χ s_χ χ(p) y + (f(p) − 1)[p ∣ q] y` (`residueFlip_prime_mul_eq`).
When `S` is closed under inversion on the units (`UnitSymmetric`) every `s_χ` is real
(`setCoeff_im_eq_zero`), and the Euler logs of `ζ` and of `L(·, χ)` (each `Re Σ_p χ(p) p^{-w}` up to
`S = Σ_p p^{-2}`) give on `Re w > 1`

`log|F(w)| ≤ (1 − 2ρ) log|ζ(w)| − (2/φ) Σ_{χ ≠ 1} s_χ log|L(w, χ)| + B`,  `ρ = s_1/φ(q)`

(`exists_log_norm_residueFlip_le`): `ρ` is the proportion of flipped unit classes, and the
nonprincipal characters enter with real exponents.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Character coefficients of a residue set -/

/-- The character coefficient of a residue set: `s_χ = Σ_{u ∈ S unit} χ(u⁻¹)`. -/
def setCoeff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ u : (ZMod q)ˣ, if (u : ZMod q) ∈ S then χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) else 0

/-- **Orthogonality**: `Σ_χ s_χ χ(b) = φ(q)` if `b` is a unit in `S`, and `0` otherwise. -/
theorem sum_setCoeff_mul {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * χ b =
      if IsUnit b ∧ b ∈ S then (q.totient : ℂ) else 0 := by
  unfold setCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ u : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q,
      (if (u : ZMod q) ∈ S then χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) else 0) * χ b =
        if (u : ZMod q) ∈ S ∧ (u : ZMod q) = b then (q.totient : ℂ) else 0 := fun u => by
    by_cases hu : (u : ZMod q) ∈ S
    · simp only [hu, if_true, true_and]
      rw [← ZMod.inv_coe_unit]
      exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _) b
    · simp [hu]
  rw [Finset.sum_congr rfl fun u _ => hinner u]
  by_cases hb : IsUnit b ∧ b ∈ S
  · obtain ⟨⟨v, rfl⟩, hvS⟩ := hb
    rw [if_pos ⟨v.isUnit, hvS⟩, Finset.sum_eq_single v]
    · rw [if_pos ⟨hvS, rfl⟩]
    · intro u _ huv
      rw [if_neg]
      rintro ⟨_, h⟩
      exact huv (Units.ext h)
    · intro h; exact absurd (Finset.mem_univ v) h
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun u _ => if_neg ?_
    rintro ⟨hu, rfl⟩
    exact hb ⟨u.isUnit, hu⟩

/-- The principal coefficient counts the unit classes of `S`. -/
theorem setCoeff_one {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    setCoeff S 1 = ((S.filter IsUnit).card : ℂ) := by
  have h := sum_setCoeff_mul S 1
  have hsum : ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * χ 1 =
      ∑ χ : DirichletCharacter ℂ q, setCoeff S χ := by simp
  have hcount : setCoeff S 1 = ∑ u : (ZMod q)ˣ, if (u : ZMod q) ∈ S then (1 : ℂ) else 0 := by
    unfold setCoeff
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · exact MulChar.one_apply_coe _
    · rfl
  rw [hcount, Finset.sum_boole]
  congr 1
  rw [← Finset.card_map ⟨Units.val, Units.val_injective⟩]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.isUnit⟩
  · rintro ⟨ha, ⟨u, rfl⟩⟩; exact ⟨u, ha, rfl⟩

/-- `S` is closed under inversion on the units. -/
def UnitSymmetric {q : ℕ} (S : Finset (ZMod q)) : Prop :=
  ∀ u : (ZMod q)ˣ, (u : ZMod q) ∈ S → ((u⁻¹ : (ZMod q)ˣ) : ZMod q) ∈ S

/-- Character values at units are unimodular: `conj χ(u⁻¹) = χ(u)`. -/
theorem conj_char_inv_unit {q : ℕ} (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    starRingEnd ℂ (χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = χ (u : ZMod q) := by
  have h1 : χ (u : ZMod q) * χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hn : ‖χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q)‖ = 1 := χ.unit_norm_eq_one _
  have hconj : starRingEnd ℂ (χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) =
      (χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q))⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  rw [hconj]
  exact (eq_inv_of_mul_eq_one_left h1).symm

/-- **The coefficients of a symmetric set are real.** -/
theorem setCoeff_im_eq_zero {q : ℕ} [NeZero q] {S : Finset (ZMod q)} (hS : UnitSymmetric S)
    (χ : DirichletCharacter ℂ q) : (setCoeff S χ).im = 0 := by
  have hreindex : setCoeff S χ =
      ∑ u : (ZMod q)ˣ, if (u : ZMod q) ∈ S then χ (u : ZMod q) else 0 := by
    unfold setCoeff
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun u => ?_
    simp only [Equiv.inv_apply]
    by_cases hu : (u : ZMod q) ∈ S
    · rw [if_pos hu, if_pos (hS u hu)]
    · rw [if_neg hu, if_neg fun h => hu (by simpa using hS u⁻¹ h)]
  have hconj : starRingEnd ℂ (setCoeff S χ) = setCoeff S χ := by
    conv_rhs => rw [hreindex]
    unfold setCoeff
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · exact conj_char_inv_unit χ u
    · exact map_zero _
  exact Complex.conj_eq_iff_im.mp hconj

/-! ### The prime decomposition -/

/-- **The prime decomposition of a residue flip**: for a prime `p` and `y ∈ ℂ`,
`f(p) y = y − (2/φ) Σ_χ s_χ χ(p) y + (f(p) − 1) [p ∣ q] y`. -/
theorem residueFlip_prime_mul_eq {q : ℕ} [NeZero q] (S : Finset (ZMod q)) {p : ℕ}
    (hp : p.Prime) (y : ℂ) :
    (residueFlip q S p : ℂ) * y = y - (2 / q.totient) *
      ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * (χ p * y) +
        ((residueFlip q S p : ℂ) - 1) * (if IsUnit (p : ZMod q) then 0 else y) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum : ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * (χ p * y) =
      (∑ χ : DirichletCharacter ℂ q, setCoeff S χ * χ p) * y := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun χ _ => by ring
  rw [hsum, sum_setCoeff_mul S (p : ZMod q), residueFlip_prime q S hp]
  by_cases hu : IsUnit (p : ZMod q)
  · rw [if_pos hu]
    by_cases hS : (p : ZMod q) ∈ S
    · rw [if_pos hS, if_pos ⟨hu, hS⟩]
      push_cast
      field_simp
      ring
    · rw [if_neg hS, if_neg (show ¬ (IsUnit (p : ZMod q) ∧ (p : ZMod q) ∈ S) from fun h => hS h.2)]
      push_cast
      ring
  · rw [if_neg hu, if_neg (show ¬ (IsUnit (p : ZMod q) ∧ (p : ZMod q) ∈ S) from fun h => hu h.1)]
    by_cases hS : (p : ZMod q) ∈ S
    · rw [if_pos hS]; push_cast; ring
    · rw [if_neg hS]; push_cast; ring

/-- The weighted prime sum over the primes dividing `q` is at most `2(q + 1)` when the weights
are at most `2`. -/
theorem norm_tsum_nonunit_primes_mul_le {q : ℕ} [NeZero q] {w : ℂ} (hw : 1 < w.re) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 2) :
    ‖∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else a p * ((p : ℕ) : ℂ) ^ (-w))‖ ≤
      2 * (q + 1) := by
  classical
  set h : ℕ → ℂ := fun n => if n.Prime ∧ ¬ IsUnit ((n : ℕ) : ZMod q) then a n * (n : ℂ) ^ (-w)
    else 0
  have hsupp : Function.support h ⊆ {n : ℕ | n.Prime} := fun n hn => by
    simp only [h, Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
    exact hn.1.1
  have heq : ∑' p : Nat.Primes,
      (if IsUnit ((p : ℕ) : ZMod q) then 0 else a p * ((p : ℕ) : ℂ) ^ (-w)) = ∑' n, h n := by
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun p => ?_
    have hp : ((p : {n : ℕ | n.Prime}) : ℕ).Prime := p.2
    simp only [h, hp, true_and]
    split_ifs <;> rfl
  have hfin : ∀ n ∉ Finset.range (q + 1), h n = 0 := by
    intro n hn
    simp only [h]
    rw [if_neg]
    rintro ⟨hp, hnu⟩
    apply hn
    rw [Finset.mem_range, Nat.lt_succ_iff]
    by_contra hnq
    apply hnu
    refine (ZMod.isUnit_iff_coprime n q).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_)
    intro hdvd
    exact hnq (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
  rw [heq, tsum_eq_sum hfin]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.range (q + 1), ‖h n‖ ≤ ∑ _n ∈ Finset.range (q + 1), (2 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        simp only [h]
        split_ifs with hc
        · have hn : (0 : ℝ) < n := by exact_mod_cast hc.1.pos
          rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn,
            Complex.neg_re]
          have h1 : (n : ℝ) ^ (-w.re) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hc.1.one_lt.le) (by linarith)
          calc ‖a n‖ * (n : ℝ) ^ (-w.re) ≤ 2 * 1 :=
                mul_le_mul (ha n) h1 (by positivity) (by norm_num)
            _ = 2 := by ring
        · simp
    _ = 2 * (q + 1) := by simp; ring

/-- The two-sided Euler log of `L(·, χ)`: `|log|L(w, χ)| − Re Σ_p χ(p) p^{-w}| ≤ S` on `Re w > 1`. -/
theorem abs_log_norm_LSeries_sub_re_le {q : ℕ} (χ : DirichletCharacter ℂ q) {w : ℂ}
    (hw : 1 < w.re) :
    |Real.log ‖LSeries (fun n => χ n) w‖ - (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re| ≤
      primeSquareMass := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hys : Summable y := summable_prime_cpow_neg hw
  have hχy : ∀ p : Nat.Primes, ‖χ p * y p‖ ≤ ‖y p‖ := fun p => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hs : Summable (fun p : Nat.Primes => χ p * y p) := hys.norm.of_norm_bounded fun p => hχy p
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - χ p * y p)) := hs.clog_one_sub.neg
  have hlog : Real.log ‖LSeries (fun n => χ n) w‖ =
      ∑' p : Nat.Primes, (-Complex.log (1 - χ p * y p)).re := by
    rw [← DirichletCharacter.LSeries_eulerProduct_exp_log χ hw, Complex.norm_exp,
      Complex.re_tsum hL, Real.log_exp]
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - χ p * y p)).re) :=
    Complex.reCLM.summable hL
  have hre2 : Summable (fun p : Nat.Primes => (χ p * y p).re) := Complex.reCLM.summable hs
  have hterm : ∀ p : Nat.Primes, ‖(-Complex.log (1 - χ p * y p)).re - (χ p * y p).re‖ ≤
      ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    rw [Real.norm_eq_abs]
    have hv : ‖χ p * y p‖ ≤ 1 / 2 := (hχy p).trans (norm_prime_cpow_neg_le hw p).1
    exact (abs_re_neg_log_one_sub_sub_re_le hv).trans
      ((pow_le_pow_left₀ (norm_nonneg _) (hχy p) 2).trans (norm_prime_cpow_neg_le hw p).2)
  have hdiff := hre1.sub hre2
  rw [hlog, Complex.re_tsum hs, ← hre1.tsum_sub hre2, ← Real.norm_eq_abs, primeSquareMass]
  exact (norm_tsum_le_tsum_norm hdiff.norm).trans
    (Summable.tsum_le_tsum hterm hdiff.norm summable_primeSquare)

/-! ### The Euler bound -/

/-- The complex prime sum of a residue flip, split along the characters:
`Σ_p f(p) y_p = P − (2/φ) Σ_χ s_χ P_χ + E`. -/
theorem tsum_residueFlip_prime_eq {q : ℕ} [NeZero q] (S : Finset (ZMod q)) {w : ℂ}
    (hw : 1 < w.re) :
    ∑' p : Nat.Primes, (residueFlip q S p : ℂ) * ((p : ℕ) : ℂ) ^ (-w) =
      ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w) - (2 / q.totient) *
        ∑ χ : DirichletCharacter ℂ q, setCoeff S χ *
          ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w) +
        ∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w)) := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hys : Summable y := summable_prime_cpow_neg hw
  have hsumχ : ∀ χ : DirichletCharacter ℂ q, Summable (fun p : Nat.Primes => χ p * y p) :=
    fun χ => hys.norm.of_norm_bounded fun p => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hE : Summable (fun p : Nat.Primes => ((residueFlip q S p : ℂ) - 1) *
      (if IsUnit ((p : ℕ) : ZMod q) then 0 else y p)) :=
    (hys.norm.mul_left 2).of_norm_bounded fun p => by
      rw [norm_mul]
      have h1 : ‖(residueFlip q S p : ℂ) - 1‖ ≤ 2 := by
        rcases residueFlip_prime_eq_one_or q S p.2 with h | h <;> rw [h] <;> norm_num
      have h2 : ‖(if IsUnit ((p : ℕ) : ZMod q) then 0 else y p)‖ ≤ ‖y p‖ := by
        split_ifs <;> simp
      exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  have hfin : Summable (fun p : Nat.Primes => (2 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * (χ p * y p)) :=
    (summable_sum fun χ _ => (hsumχ χ).mul_left _).mul_left _
  rw [tsum_congr fun p => residueFlip_prime_mul_eq S p.2 (y p),
    Summable.tsum_add (hys.sub hfin) hE, Summable.tsum_sub hys hfin, tsum_mul_left,
    Summable.tsum_finsetSum fun χ _ => (hsumχ χ).mul_left _]
  simp_rw [tsum_mul_left]
  rfl

/-- **The Euler bound of a symmetric residue flip.** For `S` closed under inversion on the units,
on `Re w > 1`: `log|F(w)| ≤ (1 − 2s_1/φ) log|ζ(w)| − (2/φ) Σ_{χ ≠ 1} s_χ log|L(w, χ)| + B`. -/
theorem exists_log_norm_residueFlip_le {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (hS : UnitSymmetric S) :
    ∃ B : ℝ, ∀ w : ℂ, 1 < w.re →
      Real.log ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        (1 - 2 * (setCoeff S 1).re / q.totient) * Real.log ‖riemannZeta w‖ -
          (2 / q.totient) * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (setCoeff S χ).re * Real.log ‖LSeries (fun n => χ n) w‖ + B := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hS₂ : 0 ≤ primeSquareMass := tsum_nonneg fun p => by positivity
  set s₁ : ℝ := (setCoeff S 1).re
  refine ⟨primeSquareMass + |1 - 2 * s₁ / q.totient| * primeSquareMass +
    2 * |s₁| / q.totient * (q + 1) + 2 * (q + 1) +
    2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      |(setCoeff S χ).re| * primeSquareMass, fun w hw => ?_⟩
  -- the pattern series against its prime sum
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (residueFlip q S) w) hw fun n => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_residueFlip_le_one q S n)
  have hFn : ∑' n, cweightedPatternHom (residueFlip q S) w n =
      ∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := tsum_congr fun n => rfl
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom (residueFlip q S) w p =
      ∑' p : Nat.Primes, (residueFlip q S p : ℂ) * ((p : ℕ) : ℂ) ^ (-w) := tsum_congr fun p => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast]
  have hS2 : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = primeSquareMass := rfl
  rw [hFn, hFp, tsum_residueFlip_prime_eq S hw, hS2] at hF
  -- the principal sum is `P − N`
  have hys := summable_prime_cpow_neg hw
  have hNs : Summable (fun p : Nat.Primes =>
      if IsUnit ((p : ℕ) : ZMod q) then (0 : ℂ) else ((p : ℕ) : ℂ) ^ (-w)) :=
    hys.norm.of_norm_bounded fun p => by split_ifs <;> simp
  have hP1 : ∑' p : Nat.Primes, (1 : DirichletCharacter ℂ q) p * ((p : ℕ) : ℂ) ^ (-w) =
      ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w) -
        ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w)) := by
    rw [← hys.tsum_sub hNs]
    refine tsum_congr fun p => ?_
    by_cases hu : IsUnit ((p : ℕ) : ZMod q)
    · rw [MulChar.one_apply hu, if_pos hu]; ring
    · rw [MulChar.map_nonunit _ hu, if_neg hu]; ring
  -- real parts of the split
  have hre : (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w) - 2 / (q.totient : ℂ) *
      ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w) +
        ∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re =
      (1 - 2 * s₁ / q.totient) * (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)).re +
        2 * s₁ / q.totient *
          (∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re -
        2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (setCoeff S χ).re * (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re +
        (∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re := by
    have hmul : ∀ χ : DirichletCharacter ℂ q,
        (setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re =
          (setCoeff S χ).re * (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re := fun χ => by
      rw [Complex.mul_re, setCoeff_im_eq_zero hS χ, zero_mul, sub_zero]
    have hc : (2 / (q.totient : ℂ)) = (((2 / q.totient : ℝ)) : ℂ) := by push_cast; rfl
    rw [Complex.add_re, Complex.sub_re, hc, Complex.re_ofReal_mul, Complex.re_sum]
    simp_rw [hmul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)), hP1,
      Complex.sub_re]
    ring
  rw [hre] at hF
  set P := ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)
  set N := ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))
  set E := ∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
    (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))
  -- the Euler logs and the finite corrections
  have hζ := abs_log_norm_riemannZeta_sub_re_le hw
  have hNb : |N.re| ≤ q + 1 :=
    (Complex.abs_re_le_norm _).trans (norm_tsum_nonunit_primes_le (q := q) hw)
  have hEb : |E.re| ≤ 2 * (q + 1) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := norm_tsum_nonunit_primes_mul_le (q := q) hw
      (fun n => (residueFlip q S n : ℂ) - 1) fun n => by
        have h1 := abs_residueFlip_le_one q S n
        calc ‖(residueFlip q S n : ℂ) - 1‖ ≤ ‖(residueFlip q S n : ℂ)‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [Complex.norm_real, Real.norm_eq_abs, norm_one]; linarith
          _ = 2 := by norm_num
    refine le_of_eq_of_le ?_ h
    congr 1
    refine tsum_congr fun p => ?_
    split_ifs <;> simp
  have hχs : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      -((setCoeff S χ).re * (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re) ≤
        -((setCoeff S χ).re * Real.log ‖LSeries (fun n => χ n) w‖) +
          |(setCoeff S χ).re| * primeSquareMass := fun χ _ => by
    have h := abs_log_norm_LSeries_sub_re_le χ hw
    have h2 : |(setCoeff S χ).re * ((∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re -
        Real.log ‖LSeries (fun n => χ n) w‖)| ≤ |(setCoeff S χ).re| * primeSquareMass := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have h3 := neg_abs_le ((setCoeff S χ).re * ((∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re -
      Real.log ‖LSeries (fun n => χ n) w‖))
    linarith [mul_sub ((setCoeff S χ).re) ((∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re)
      (Real.log ‖LSeries (fun n => χ n) w‖)]
  have hsumχ := Finset.sum_le_sum hχs
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsumχ
  have hφ2 : 0 ≤ 2 / (q.totient : ℝ) := by positivity
  have hsumχ' := mul_le_mul_of_nonneg_left hsumχ hφ2
  have hζterm : (1 - 2 * s₁ / q.totient) * P.re ≤
      (1 - 2 * s₁ / q.totient) * Real.log ‖riemannZeta w‖ +
        |1 - 2 * s₁ / q.totient| * primeSquareMass := by
    have h2 : |(1 - 2 * s₁ / q.totient) * (P.re - Real.log ‖riemannZeta w‖)| ≤
        |1 - 2 * s₁ / q.totient| * primeSquareMass := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hζ) (abs_nonneg _)
    have h3 := le_abs_self ((1 - 2 * s₁ / q.totient) * (P.re - Real.log ‖riemannZeta w‖))
    linarith [mul_sub (1 - 2 * s₁ / q.totient) P.re (Real.log ‖riemannZeta w‖)]
  have hNterm : 2 * s₁ / q.totient * N.re ≤ 2 * |s₁| / q.totient * (q + 1) := by
    have h1 : 2 * s₁ / q.totient * N.re ≤ |2 * s₁ / q.totient * N.re| := le_abs_self _
    have h2 : |2 * s₁ / q.totient * N.re| = 2 * |s₁| / q.totient * |N.re| := by
      rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hφ]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hNb (by positivity))
  have hEterm := le_abs_self E.re
  have hFle := (abs_le.mp hF).2
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
