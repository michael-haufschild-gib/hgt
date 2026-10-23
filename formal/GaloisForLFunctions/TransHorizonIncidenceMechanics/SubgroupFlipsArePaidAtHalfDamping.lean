import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterBoundaryOfResidueClassFlips
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfTheConstantSignPatternOnTheFullRange
import GaloisForLFunctions.RHTower.DirichletLLogStrip
import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnsignedMajorantsAndSignBlindDataStopAtHalfDamping
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Subgroup flips are paid at half damping

Let `H` be a subgroup of `G = (ZMod q)ˣ` of index `k ≥ 2`, and let `f_H` be the completely
multiplicative `±1` pattern with `f_H(p) = −1` exactly at the primes `p ∤ q` with `p mod q ∉ H`
(`subgroupFlipSet`, `residueFlip`). Its flipped primes have density `1 − 1/k ≥ 1/2 > 1/4`, and the
quarter law predicts payment at half damping. This is proved unconditionally
(`receiverBounded_subgroupFlip_half`).

* **Orthogonality** (`sum_subgroupCoeff_mul`): `[b ∈ H] = φ(q)^{-1} Σ_χ c_χ χ(b)` with
  `c_χ = Σ_{h∈H} χ(h⁻¹) ∈ {0, |H|}` — real and nonnegative (`subgroupCoeff_eq_real`).
* **Euler bound** (`exists_log_norm_subgroupFlip_le`): `f_H(p) = −1 + 2[p | q] + (2/φ) Σ_χ c_χ χ(p)`,
  and the Euler logs of `ζ` and `L(·, χ)` give
  `log|F(w)| ≤ −log|ζ(w)| + (2/φ) Σ_χ c_χ log|L(w, χ)| + B`. The principal character contributes
  `(2|H|/φ) log|ζ|` (Mathlib's `LFunctionTrivChar_eq_mul_riemannZeta`), so the `ζ` exponent is
  `2/k − 1 ∈ [−1, 0]`: only `1/|ζ|` and `|L|` from above are needed — no zero-free region for `L`.
* **Size on the strip** (`exists_norm_subgroupFlip_le`): `1/|ζ| ≪ log¹⁰|t|`, `|L(w, χ)| ≪ log|t|`
  (`RHTower.norm_LFunction_le_log`), and boundedness on `|t| ≤ 9` (`L(·, χ)` entire for `χ ≠ 1`)
  give `|F(1 + u + it)| ≤ B₀` for `|t| ≤ 2` and `≤ B₁ |t|^{1/4}` for `|t| ≥ 2`; the line-energy
  criterion pays the receiver.

For index `k ≥ 3` the flipped density `1 − 1/k` is neither `1/2` nor `1`, so below half damping the
pattern is unpaid (`not_receiverBounded_residueFlip`): **the receiver of `f_H(d) d^{-ε}` is paid
exactly for `ε ≥ 1/2`** (`receiverBounded_subgroupFlip_iff`).
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Character coefficients of a subgroup -/

open Classical in
/-- The character coefficient of a subgroup `H ≤ (ZMod q)ˣ`: `c_χ = Σ_{h ∈ H} χ(h⁻¹)`. -/
def subgroupCoeff {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h : H, χ (((h : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q)

/-- `c_χ` is `|H|` or `0`: in particular a nonnegative real. -/
theorem subgroupCoeff_eq_real {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    ∃ r : ℝ, 0 ≤ r ∧ subgroupCoeff H χ = r := by
  classical
  by_cases htriv : ∀ h : H, χ ((h : (ZMod q)ˣ) : ZMod q) = 1
  · refine ⟨Fintype.card H, Nat.cast_nonneg _, ?_⟩
    unfold subgroupCoeff
    have : ∀ h : H, χ (((h : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := fun h => by
      have := htriv h⁻¹
      simpa using this
    rw [Finset.sum_congr rfl fun h _ => this h]
    simp
  · obtain ⟨h₀, hh₀⟩ := not_forall.mp htriv
    refine ⟨0, le_rfl, ?_⟩
    -- reindex `h ↦ h h₀`
    have hre : subgroupCoeff H χ =
        χ (((h₀ : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) * subgroupCoeff H χ := by
      unfold subgroupCoeff
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulRight h₀) _ _ fun h => ?_).symm
      simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, map_mul]
    have hne : χ (((h₀ : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) ≠ 1 := by
      intro h1
      apply hh₀
      have hmul : χ ((h₀ : (ZMod q)ˣ) : ZMod q) * χ (((h₀ : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      rwa [h1, mul_one] at hmul
    have : (χ (((h₀ : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) - 1) * subgroupCoeff H χ = 0 := by
      rw [sub_mul, one_mul, ← hre, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · rw [h, Complex.ofReal_zero]

/-- Membership of a residue in `H`. -/
def InSubgroup {q : ℕ} (H : Subgroup (ZMod q)ˣ) (b : ZMod q) : Prop :=
  ∃ h ∈ H, ((h : (ZMod q)ˣ) : ZMod q) = b

open Classical in
/-- **Orthogonality**: `Σ_χ c_χ χ(b) = φ(q) [b ∈ H]`. -/
theorem sum_subgroupCoeff_mul {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, subgroupCoeff H χ * χ b =
      if InSubgroup H b then (q.totient : ℂ) else 0 := by
  classical
  unfold subgroupCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ h : H, ∑ χ : DirichletCharacter ℂ q,
      χ (((h : (ZMod q)ˣ)⁻¹ : (ZMod q)ˣ) : ZMod q) * χ b =
        if ((h : (ZMod q)ˣ) : ZMod q) = b then (q.totient : ℂ) else 0 := fun h => by
    rw [← ZMod.inv_coe_unit]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _) b
  rw [Finset.sum_congr rfl fun h _ => hinner h]
  by_cases hb : InSubgroup H b
  · obtain ⟨h₀, hh₀, hval⟩ := hb
    rw [if_pos ⟨h₀, hh₀, hval⟩, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun h : H => ((h : (ZMod q)ˣ) : ZMod q) = b).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨(⟨h₀, hh₀⟩ : H), ?_⟩
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hh
        apply Subtype.ext
        apply Units.ext
        rw [hh, hval]
      · rintro rfl; exact hval
    rw [hcard]; simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg]
    intro hh
    exact hb ⟨h, h.2, hh⟩

/-- `|Re(−log(1 − v)) − Re v| ≤ |v|²` for `|v| ≤ 1/2`. -/
theorem abs_re_neg_log_one_sub_sub_re_le {v : ℂ} (hv : ‖v‖ ≤ 1 / 2) :
    |(-Complex.log (1 - v)).re - v.re| ≤ ‖v‖ ^ 2 := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_log_one_add_sub_self_le_sq (v := -v) (by rw [norm_neg]; exact hv))
  rw [norm_neg, ← sub_eq_add_neg] at h
  simp only [Complex.sub_re, Complex.neg_re] at h ⊢
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `|p^{-w}| ≤ 1/2` and `|p^{-w}|² ≤ p^{-2}` on `Re w > 1`. -/
theorem norm_prime_cpow_neg_le {w : ℂ} (hw : 1 < w.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-w)‖ ≤ 1 / 2 ∧ ‖((p : ℕ) : ℂ) ^ (-w)‖ ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-w)‖ = ((p : ℕ) : ℝ) ^ (-w.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast p.2.pos), Complex.neg_re]
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by linarith
  rw [hnorm]
  constructor
  · calc ((p : ℕ) : ℝ) ^ (-w.re) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)

/-- **The Euler log-modulus of an L-series**: for completely multiplicative `g` with
`|g(p)| ≤ |p^{-w}|` and `Re w > 1`, `|log|Σ g(n)| − Re Σ_p g(p)| ≤ Σ_p p^{-2}`. -/
theorem abs_log_norm_tsum_sub_re_le (g : ℕ →*₀ ℂ) {w : ℂ} (hw : 1 < w.re)
    (hg : ∀ n : ℕ, ‖g n‖ ≤ ‖((n : ℕ) : ℂ) ^ (-w)‖) :
    |Real.log ‖∑' n, g n‖ - (∑' p : Nat.Primes, g p).re| ≤
      ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hsum : Summable (fun n => ‖g n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => (hg n).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Complex.zero_cpow (show -w ≠ 0 by
        intro h; have := congrArg Complex.re h; simp at this; linarith), norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    · rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn),
        Complex.neg_re]
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  have hgp : ∀ p : Nat.Primes, ‖g p‖ ≤ 1 / 2 := fun p =>
    (hg p).trans (norm_prime_cpow_neg_le hw p).1
  have hgs : Summable (fun p : Nat.Primes => g p) :=
    ((Nat.Primes.summable_rpow.mpr (show -w.re < -1 by linarith))).of_norm_bounded fun p => by
      refine (hg p).trans (le_of_eq ?_)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
        (by exact_mod_cast p.2.pos), Complex.neg_re]
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - g p)) := hgs.clog_one_sub.neg
  have hsq2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hlog : Real.log ‖∑' n, g n‖ = ∑' p : Nat.Primes, (-Complex.log (1 - g p)).re := by
    rw [← hE, Complex.norm_exp, Complex.re_tsum hL, Real.log_exp]
  have hterm : ∀ p : Nat.Primes, ‖(-Complex.log (1 - g p)).re - (g p).re‖ ≤
      ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    rw [Real.norm_eq_abs]
    refine (abs_re_neg_log_one_sub_sub_re_le (hgp p)).trans ?_
    exact (pow_le_pow_left₀ (norm_nonneg _) (hg p) 2).trans (norm_prime_cpow_neg_le hw p).2
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - g p)).re) :=
    Complex.reCLM.summable hL
  have hre2 : Summable (fun p : Nat.Primes => (g p).re) := Complex.reCLM.summable hgs
  have hdiff : Summable (fun p : Nat.Primes => (-Complex.log (1 - g p)).re - (g p).re) :=
    hre1.sub hre2
  rw [hlog, Complex.re_tsum hgs, ← hre1.tsum_sub hre2, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hdiff.norm).trans (Summable.tsum_le_tsum hterm hdiff.norm hsq2)

/-- Primes that are not units mod `q` divide `q`: their prime sum is at most `q + 1`. -/
theorem norm_tsum_nonunit_primes_le {q : ℕ} [NeZero q] {w : ℂ} (hw : 1 < w.re) :
    ‖∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))‖ ≤ q + 1 := by
  classical
  set h : ℕ → ℂ := fun n => if n.Prime ∧ ¬ IsUnit ((n : ℕ) : ZMod q) then (n : ℂ) ^ (-w) else 0
  have hsupp : Function.support h ⊆ {n : ℕ | n.Prime} := fun n hn => by
    simp only [h, Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
    exact hn.1.1
  have heq : ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w)) =
      ∑' n, h n := by
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
  calc ∑ n ∈ Finset.range (q + 1), ‖h n‖ ≤ ∑ _n ∈ Finset.range (q + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        simp only [h]
        split_ifs with hc
        · have hn : (0 : ℝ) < n := by exact_mod_cast hc.1.pos
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hc.1.one_lt.le)
            (by linarith)
        · simp
    _ = q + 1 := by simp

/-- A completely multiplicative pattern bounded by `1` at the primes is bounded by `1`. -/
theorem abs_patternHom_le_one (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (n : ℕ) :
    |f n| ≤ 1 := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact hf p hp
  | mul a b ha hb => rw [map_mul, abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb

/-- A residue-class flip is bounded by `1`. -/
theorem abs_residueFlip_le_one (q : ℕ) (S : Finset (ZMod q)) (n : ℕ) :
    |residueFlip q S n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rcases residueFlip_prime_eq_one_or q S hp with h | h <;> simp [h]) n

/-- `Σ_p p^{-w}` converges on `Re w > 1`. -/
theorem summable_prime_cpow_neg {w : ℂ} (hw : 1 < w.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-w)) :=
  (Nat.Primes.summable_rpow.mpr (show -w.re < -1 by linarith)).of_norm_bounded fun p => by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast p.2.pos), Complex.neg_re]

/-- The Euler log of `ζ`: `log|ζ(w)| ≤ Re Σ_p p^{-w} + Σ_p p^{-2}` on `Re w > 1`. -/
theorem log_norm_riemannZeta_le_re_tsum_add {w : ℂ} (hw : 1 < w.re) :
    Real.log ‖riemannZeta w‖ ≤ (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)).re +
      ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hys : Summable y := summable_prime_cpow_neg hw
  have hZ := riemannZeta_eulerProduct_exp_log hw
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - y p)) := hys.clog_one_sub.neg
  have hlog : Real.log ‖riemannZeta w‖ = ∑' p : Nat.Primes, (-Complex.log (1 - y p)).re := by
    rw [← hZ, Complex.norm_exp, Complex.re_tsum hL, Real.log_exp]
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - y p)).re) :=
    Complex.reCLM.summable hL
  have hre2 : Summable (fun p : Nat.Primes => (y p).re) := Complex.reCLM.summable hys
  have hsq2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  rw [hlog, Complex.re_tsum hys]
  have := Summable.tsum_le_tsum (fun p => by
      have h := abs_re_neg_log_one_sub_sub_re_le (norm_prime_cpow_neg_le hw p).1
      have h2 := (norm_prime_cpow_neg_le hw p).2
      linarith [(abs_le.mp h).2] : ∀ p : Nat.Primes,
        (-Complex.log (1 - y p)).re ≤ (y p).re + ((p : ℕ) : ℝ) ^ (-2 : ℝ))
    hre1 (hre2.add hsq2)
  rwa [hre2.tsum_add hsq2] at this

/-- The Euler log of `L(·, χ)`: `Re Σ_p χ(p) p^{-w} ≤ log|L(w, χ)| + Σ_p p^{-2}` on `Re w > 1`. -/
theorem re_tsum_char_le_log_norm_LSeries_add {q : ℕ} (χ : DirichletCharacter ℂ q) {w : ℂ}
    (hw : 1 < w.re) :
    (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re ≤
      Real.log ‖LSeries (fun n => χ n) w‖ + ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hys : Summable y := summable_prime_cpow_neg hw
  have hE := DirichletCharacter.LSeries_eulerProduct_exp_log χ hw
  have hχy : ∀ p : Nat.Primes, ‖χ p * y p‖ ≤ ‖y p‖ := fun p => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hs : Summable (fun p : Nat.Primes => χ p * y p) :=
    hys.norm.of_norm_bounded fun p => hχy p
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - χ p * y p)) := hs.clog_one_sub.neg
  have hlog : Real.log ‖LSeries (fun n => χ n) w‖ =
      ∑' p : Nat.Primes, (-Complex.log (1 - χ p * y p)).re := by
    rw [← hE, Complex.norm_exp, Complex.re_tsum hL, Real.log_exp]
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - χ p * y p)).re) :=
    Complex.reCLM.summable hL
  have hre2 : Summable (fun p : Nat.Primes => (χ p * y p).re) := Complex.reCLM.summable hs
  have hsq2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  rw [hlog, Complex.re_tsum hs]
  have := Summable.tsum_le_tsum (fun p => by
      have hv : ‖χ p * y p‖ ≤ 1 / 2 := (hχy p).trans (norm_prime_cpow_neg_le hw p).1
      have h := abs_re_neg_log_one_sub_sub_re_le hv
      have h2 := (pow_le_pow_left₀ (norm_nonneg _) (hχy p) 2).trans (norm_prime_cpow_neg_le hw p).2
      linarith [(abs_le.mp h).1] : ∀ p : Nat.Primes,
        (χ p * y p).re ≤ (-Complex.log (1 - χ p * y p)).re + ((p : ℕ) : ℝ) ^ (-2 : ℝ))
    hre2 (hre1.add hsq2)
  rwa [hre1.tsum_add hsq2] at this

open Classical in
/-- The prime values of a subgroup flip: `f(p) = −1 + 2[p ∣ q] + (2/φ) Σ_χ c_χ χ(p)`. -/
theorem subgroupFlip_prime_decomp {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (f : ℕ →*₀ ℝ)
    (hf : ∀ p : ℕ, p.Prime → f p = if IsUnit (p : ZMod q) ∧ ¬ InSubgroup H p then -1 else 1)
    (p : Nat.Primes) (y : ℂ) :
    (f p : ℂ) * y = -y + 2 * (if IsUnit ((p : ℕ) : ZMod q) then 0 else y) +
      (2 / q.totient) * ∑ χ : DirichletCharacter ℂ q, subgroupCoeff H χ * (χ p * y) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hsum : ∑ χ : DirichletCharacter ℂ q, subgroupCoeff H χ * (χ p * y) =
      (∑ χ : DirichletCharacter ℂ q, subgroupCoeff H χ * χ p) * y := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun χ _ => by ring
  rw [hsum, sum_subgroupCoeff_mul H ((p : ℕ) : ZMod q), hf p p.2]
  have hφC : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  by_cases hu : IsUnit ((p : ℕ) : ZMod q)
  · by_cases hH : InSubgroup H ((p : ℕ) : ZMod q)
    · simp only [hu, hH, not_true_eq_false, and_false, if_false, if_true]
      field_simp; push_cast; ring
    · simp only [hu, hH, not_false_eq_true, and_self, if_true, if_false]
      push_cast; ring
  · have hH : ¬ InSubgroup H ((p : ℕ) : ZMod q) := by
      rintro ⟨h, _, hh⟩; exact hu (hh ▸ Units.isUnit h)
    simp only [hu, hH, false_and, if_false]
    push_cast; ring

open Classical in
/-- The prime sum of a subgroup flip split along the characters. -/
theorem re_tsum_subgroupFlip_eq {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (f : ℕ →*₀ ℝ)
    (hf : ∀ p : ℕ, p.Prime → f p = if IsUnit (p : ZMod q) ∧ ¬ InSubgroup H p then -1 else 1)
    {w : ℂ} (hw : 1 < w.re) :
    (∑' p : Nat.Primes, (f p : ℂ) * ((p : ℕ) : ℂ) ^ (-w)).re =
      -(∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)).re +
        2 * (∑' p : Nat.Primes,
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re +
        (2 / q.totient) * ∑ χ : DirichletCharacter ℂ q,
          (subgroupCoeff H χ).re * (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hys : Summable y := summable_prime_cpow_neg hw
  have hsumχ : ∀ χ : DirichletCharacter ℂ q, Summable (fun p : Nat.Primes => χ p * y p) := fun χ =>
    hys.norm.of_norm_bounded fun p => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hnus : Summable (fun p : Nat.Primes =>
      if IsUnit ((p : ℕ) : ZMod q) then (0 : ℂ) else y p) :=
    hys.norm.of_norm_bounded fun p => by split_ifs <;> simp [y]
  rw [tsum_congr fun p => subgroupFlip_prime_decomp H f hf p (y p),
    Summable.tsum_add (hys.neg.add (hnus.mul_left 2))
      ((summable_sum fun χ _ => (hsumχ χ).mul_left _).mul_left _),
    Summable.tsum_add hys.neg (hnus.mul_left 2), tsum_neg, tsum_mul_left, tsum_mul_left,
    Summable.tsum_finsetSum fun χ _ => (hsumχ χ).mul_left _]
  simp only [Complex.add_re, Complex.neg_re]
  have h2 : ∀ X : ℂ, ((2 : ℂ) * X).re = 2 * X.re := fun X => by simp [Complex.mul_re]
  rw [h2, show ((2 : ℂ) / q.totient) = (((2 : ℝ) / q.totient : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]
  have hχ : ∀ χ : DirichletCharacter ℂ q,
      (∑' p : Nat.Primes, subgroupCoeff H χ * (χ p * y p)).re =
        (subgroupCoeff H χ).re * (∑' p : Nat.Primes, χ p * y p).re := fun χ => by
    obtain ⟨r, -, hcr⟩ := subgroupCoeff_eq_real H χ
    rw [tsum_mul_left, hcr, Complex.re_ofReal_mul, Complex.ofReal_re]
  simp_rw [hχ]
  rfl

open Classical in
/-- **The subgroup-flip Euler bound.** Let `f(p) = −1` exactly for the units `p mod q ∉ H`. On
`Re w > 1`: `log|F(w)| ≤ −log|ζ(w)| + (2/φ(q)) Σ_χ c_χ log|L(w, χ)| + B`, `c_χ = Σ_{h∈H} χ(h⁻¹) ≥ 0`. -/
theorem exists_log_norm_subgroupFlip_le {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (f : ℕ →*₀ ℝ)
    (hf : ∀ p : ℕ, p.Prime → f p = if IsUnit (p : ZMod q) ∧ ¬ InSubgroup H p then -1 else 1) :
    ∃ B : ℝ, ∀ w : ℂ, 1 < w.re →
      Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        -Real.log ‖riemannZeta w‖ +
          (2 / q.totient) * ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re *
            Real.log ‖LSeries (fun n => χ n) w‖ + B := by
  set S₂ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  have hr : ∀ χ : DirichletCharacter ℂ q, 0 ≤ (subgroupCoeff H χ).re := fun χ => by
    obtain ⟨r, hr0, hcr⟩ := subgroupCoeff_eq_real H χ
    rw [hcr, Complex.ofReal_re]; exact hr0
  have h2φ : 0 ≤ (2 : ℝ) / q.totient := by positivity
  refine ⟨3 * S₂ + 2 * (q + 1) +
    (2 / q.totient) * ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re * S₂, fun w hw => ?_⟩
  -- the pattern series against its prime sum
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom f w) hw fun n => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
    refine mul_le_of_le_one_left (norm_nonneg _) (abs_patternHom_le_one f (fun p hp => ?_) n)
    rw [hf p hp]; split_ifs <;> simp
  have hFn : ∑' n, cweightedPatternHom f w n = ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) :=
    tsum_congr fun n => rfl
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom f w p =
      ∑' p : Nat.Primes, (f p : ℂ) * ((p : ℕ) : ℂ) ^ (-w) := tsum_congr fun p => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast]
  rw [hFn, hFp, re_tsum_subgroupFlip_eq H f hf hw] at hF
  have hζ := log_norm_riemannZeta_le_re_tsum_add hw
  have hnu := (Complex.re_le_norm _).trans (norm_tsum_nonunit_primes_le (q := q) hw)
  have hχ : ∑ χ : DirichletCharacter ℂ q,
        (subgroupCoeff H χ).re * (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re ≤
      ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re * Real.log ‖LSeries (fun n => χ n) w‖ +
        ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re * S₂ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun χ _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (re_tsum_char_le_log_norm_LSeries_add χ hw) (hr χ)
  have hχa := mul_le_mul_of_nonneg_left hχ h2φ
  rw [mul_add] at hχa
  -- linear assembly over opaque atoms
  have key : ∀ {lF Ry Rn lZ X Y W a S Q : ℝ}, 0 ≤ S → |lF - (-Ry + 2 * Rn + a * X)| ≤ S →
      lZ ≤ Ry + S → Rn ≤ Q → a * X ≤ a * Y + a * W →
      lF ≤ -lZ + a * Y + (3 * S + 2 * Q + a * W) := by
    intro lF Ry Rn lZ X Y W a S Q h0 h1 h3 h4 h5
    have := (abs_le.mp h1).2
    linarith
  exact key (tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _) hF hζ hnu hχa


/-! ### `1/ζ` at large heights, polylogarithmically -/

/-- `1/|ζ(w)| ≤ K log¹⁰|Im w|` for `1 < Re w ≤ 2`, `|Im w| ≥ 9`. -/
theorem exists_inv_norm_zeta_le_log_pow_large :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 9 ≤ |w.im| →
      ‖riemannZeta w‖⁻¹ ≤ K * Real.log |w.im| ^ 10 := by
  set A := RHTower.zetaLowerA
  have hA : 0 < A := RHTower.zetaLowerA_pos
  refine ⟨max (20 / A) (4 * (1 + 1 / A)), by positivity, fun w hw hw2 ht => ?_⟩
  set σ := w.re
  set t := w.im
  have hwst : w = (σ : ℂ) + (t : ℂ) * I := (Complex.re_add_im w).symm
  set L := Real.log |t|
  have hL2 : 2 ≤ L := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log |t| :=
      Real.log_le_log (Real.exp_pos 2) (by have := RHTower.exp_two_lt_eight; linarith)
    rwa [Real.log_exp] at h1
  have hL1 : 1 ≤ L := by linarith
  have hL9 : 1 ≤ L ^ 9 := one_le_pow₀ hL1
  have hζ0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw.le
  have hpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hζ0
  -- both regions give `≤ max(20/A, 4(1 + 1/A)) · L^{10}`
  have hmain : ‖riemannZeta w‖⁻¹ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 := by
    by_cases hstrip : σ ≤ 1 + A / L ^ 9
    · have h := RHTower.norm_inv_riemannZeta_le (σ := σ) (t := t) ht
        (by have : 0 ≤ A / L ^ 9 := by positivity
            linarith) hstrip
      rw [← hwst, norm_inv] at h
      calc ‖riemannZeta w‖⁻¹ ≤ 20 / A * L ^ 7 := h
        _ ≤ 20 / A * L ^ 10 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) (by positivity)
        _ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hσA : A / L ^ 9 < σ - 1 := by linarith [not_le.mp hstrip]
      have hσ1 : 1 < σ := by have : 0 < A / L ^ 9 := by positivity
                             linarith
      -- the doubled height
      have hB : ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I)‖ ≤ L + 6 := by
        have h := RHTower.norm_riemannZeta_le_log_add (s := (σ : ℂ) + 2 * (t : ℂ) * I)
          (by simp; linarith) (by simp; linarith) (by simp [abs_mul]; linarith)
        have him : ((σ : ℂ) + 2 * (t : ℂ) * I).im = 2 * t := by simp
        rw [him, abs_mul, abs_two, Real.log_mul (by norm_num) (by linarith)] at h
        have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        linarith
      have hneg := RHTower.Sieve.neg_log_norm_riemannZeta_le_of_bound (σ := σ) (t := t)
        (B := L + 6) hσ1 hB
      rw [← hwst] at hneg
      have hx1 : 1 ≤ 1 + 1 / (σ - 1) := by
        have : 0 < 1 / (σ - 1) := one_div_pos.mpr (by linarith)
        linarith
      have hx : 1 + 1 / (σ - 1) ≤ 1 + L ^ 9 / A := by
        have hpos' : 0 < A / L ^ 9 := by positivity
        have h1 : 1 / (σ - 1) < 1 / (A / L ^ 9) := one_div_lt_one_div_of_lt hpos' hσA
        rw [one_div_div] at h1
        linarith
      have hB1 : 1 ≤ L + 6 := by linarith
      -- `1/|ζ| = exp(−log|ζ|) ≤ (1 + 1/(σ−1))^{3/4} (L+6)^{1/4} ≤ (1 + 1/(σ−1))(L+6)`
      have hexp : ‖riemannZeta w‖⁻¹ ≤ (1 + 1 / (σ - 1)) * (L + 6) := by
        have h1 : ‖riemannZeta w‖⁻¹ = Real.exp (-Real.log ‖riemannZeta w‖) := by
          rw [Real.exp_neg, Real.exp_log hpos]
        have h2 : Real.exp (3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log (L + 6)) =
            (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) * (L + 6) ^ (1 / 4 : ℝ) := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith),
            mul_comm (3 / 4 : ℝ), mul_comm (1 / 4 : ℝ)]
        have h3 : (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) ≤ 1 + 1 / (σ - 1) := by
          calc (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) ≤ (1 + 1 / (σ - 1)) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
            _ = 1 + 1 / (σ - 1) := Real.rpow_one _
        have h4 : (L + 6) ^ (1 / 4 : ℝ) ≤ L + 6 := by
          calc (L + 6) ^ (1 / 4 : ℝ) ≤ (L + 6) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
            _ = L + 6 := Real.rpow_one _
        rw [h1]
        calc Real.exp (-Real.log ‖riemannZeta w‖)
            ≤ Real.exp (3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log (L + 6)) :=
              Real.exp_le_exp.mpr hneg
          _ = (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) * (L + 6) ^ (1 / 4 : ℝ) := h2
          _ ≤ (1 + 1 / (σ - 1)) * (L + 6) :=
              mul_le_mul h3 h4 (by positivity) (by linarith)
      calc ‖riemannZeta w‖⁻¹ ≤ (1 + 1 / (σ - 1)) * (L + 6) := hexp
        _ ≤ (1 + L ^ 9 / A) * (L + 6) := mul_le_mul_of_nonneg_right hx (by linarith)
        _ ≤ (L ^ 9 + L ^ 9 / A) * (4 * L) := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
        _ = 4 * (1 + 1 / A) * L ^ 10 := by field_simp
        _ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  exact hmain


/-! ### The subgroup flip -/

open Classical in
/-- The residues flipped by `H`: the units outside `H`. -/
def subgroupFlipSet {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) : Finset (ZMod q) :=
  Finset.univ.filter fun a => IsUnit a ∧ ¬ InSubgroup H a

open Classical in
theorem residueFlip_subgroupFlipSet_prime {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {p : ℕ}
    (hp : p.Prime) :
    residueFlip q (subgroupFlipSet H) p =
      if IsUnit (p : ZMod q) ∧ ¬ InSubgroup H p then -1 else 1 := by
  rw [residueFlip_prime q _ hp]
  simp only [subgroupFlipSet, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
theorem subgroupCoeff_one {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    subgroupCoeff H 1 = (Nat.card H : ℂ) := by
  unfold subgroupCoeff
  rw [Finset.sum_congr rfl fun h _ => MulChar.one_apply (Units.isUnit _)]
  simp [Nat.card_eq_fintype_card]

/-- The coefficients sum to `φ(q)`. -/
theorem sum_re_subgroupCoeff {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re = q.totient := by
  classical
  have h := sum_subgroupCoeff_mul H 1
  simp only [map_one, mul_one] at h
  rw [if_pos ⟨1, H.one_mem, Units.val_one⟩] at h
  rw [← Complex.re_sum, h, Complex.natCast_re]

/-- `log x ≤ log(1 + x)` for `x ≥ 0`. -/
theorem log_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ Real.log (1 + x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact Real.log_le_log hx (by linarith)

/-- `log^{12} x ≤ 48^{12} x^{1/4}` for `x ≥ 1`. -/
theorem log_pow_twelve_le_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 12 ≤ 48 ^ 12 * x ^ (1 / 4 : ℝ) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ 48 * x ^ (1 / 48 : ℝ) := by
    have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (show (0 : ℝ) < 1 / 48 by norm_num)
    rw [div_eq_mul_inv] at h
    linarith [show x ^ (1 / 48 : ℝ) * (1 / 48 : ℝ)⁻¹ = 48 * x ^ (1 / 48 : ℝ) by norm_num; ring]
  have h := pow_le_pow_left₀ h0 hlog 12
  have hp : (48 * x ^ (1 / 48 : ℝ)) ^ 12 = 48 ^ 12 * x ^ (1 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 48 : ℝ)), ← Real.rpow_mul (by linarith)]
    norm_num
  linarith

open Classical in
/-- **The size of a subgroup flip on the strip.** For `2|H| ≤ φ(q)` there are `B₀, B₁` with
`|F(w)| ≤ B₀` for `|Im w| ≤ 9` and `|F(w)| ≤ B₁ |Im w|^{1/4}` for `|Im w| ≥ 9`, `1 < Re w ≤ 2`. -/
theorem exists_norm_subgroupFlip_le {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hk : 2 * Nat.card H ≤ q.totient) :
    ∃ B₀ B₁ : ℝ, ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (|w.im| ≤ 9 → ‖∑' n : ℕ, (residueFlip q (subgroupFlipSet H) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ B₀) ∧
      (9 ≤ |w.im| → ‖∑' n : ℕ, (residueFlip q (subgroupFlipSet H) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ B₁ * |w.im| ^ (1 / 4 : ℝ)) := by
  set f := residueFlip q (subgroupFlipSet H)
  obtain ⟨B, hB⟩ := exists_log_norm_subgroupFlip_le H f
    fun p hp => residueFlip_subgroupFlipSet_prime H hp
  obtain ⟨K₁, hK₁, hζL⟩ := exists_inv_norm_zeta_le_log_pow_large
  obtain ⟨K₂, hK₂, hζbox⟩ := exists_inv_norm_zeta_le_box
  -- `L(·, χ)` on the closed box, `χ ≠ 1`
  set Kb : Set ℂ := (Icc (1 : ℝ) 2) ×ℂ (Icc (-9 : ℝ) 9)
  have hKb : IsCompact Kb := isCompact_Icc.reProdIm isCompact_Icc
  have hMχ : ∀ χ : DirichletCharacter ℂ q, ∃ M : ℝ, χ ≠ 1 →
      ∀ w ∈ Kb, ‖DirichletCharacter.LFunction χ w‖ ≤ M := fun χ => by
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    · obtain ⟨M, hM⟩ := hKb.exists_bound_of_continuousOn
        (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousOn
      exact ⟨M, fun _ => hM⟩
  choose M hM using hMχ
  set Mt : ℝ := ∑ χ : DirichletCharacter ℂ q, |M χ|
  have hMt : ∀ χ, χ ≠ 1 → ∀ w ∈ Kb, ‖DirichletCharacter.LFunction χ w‖ ≤ Mt := fun χ hχ w hw =>
    (hM χ hχ w hw).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun χ _ => abs_nonneg (M χ)) (Finset.mem_univ χ)))
  set CQ := RHTower.characterLogStripConstant q
  have hCQ : 1 ≤ CQ := RHTower.one_le_characterLogStripConstant q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set a : ℝ := 2 * Nat.card H / q.totient
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    simp only [a]; rw [div_le_one hφ]; exact_mod_cast hk
  set ω : ℝ := ((q.primeFactors.card : ℕ) : ℝ)
  set B'' : ℝ := B + a * (ω * Real.log 2)
  -- the master estimate: `|F| ≤ e^{B''}(1 + 1/|ζ|)(1 + K)²` whenever `|L(w,χ)| ≤ K`, `χ ≠ 1`
  have hmaster : ∀ w : ℂ, 1 < w.re → ∀ K : ℝ, 0 ≤ K →
      (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖LSeries (fun n => χ n) w‖ ≤ K) →
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp B'' * (1 + ‖riemannZeta w‖⁻¹) * (1 + K) ^ 2 := by
    intro w hw K hK hLK
    have hζ0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw.le
    have hζpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hζ0
    have hlogF := hB w hw
    -- the principal character: `log|L(w, 1)| ≤ log|ζ(w)| + ω log 2`
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
    have hL1 : Real.log ‖LSeries (fun n => (1 : DirichletCharacter ℂ q) n) w‖ ≤
        Real.log ‖riemannZeta w‖ + ω * Real.log 2 := by
      rw [← DirichletCharacter.LFunction_eq_LSeries _ hw,
        show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w = _ from
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hw1, norm_mul]
      have hfac : ∀ p ∈ q.primeFactors, (1 / 2 : ℝ) ≤ ‖1 - (p : ℂ) ^ (-w)‖ ∧
          ‖1 - (p : ℂ) ^ (-w)‖ ≤ 2 := fun p hp => by
        have hp' := Nat.prime_of_mem_primeFactors hp
        have h := (norm_prime_cpow_neg_le hw ⟨p, hp'⟩).1
        simp only at h
        constructor
        · have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-w))
          rw [norm_one] at this; linarith
        · have := norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-w))
          rw [norm_one] at this; linarith
      have hpos : 0 < ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))‖ := by
        rw [norm_prod]
        exact Finset.prod_pos fun p hp => lt_of_lt_of_le (by norm_num) (hfac p hp).1
      have hprod : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))‖ ≤ 2 ^ q.primeFactors.card := by
        rw [norm_prod]
        calc ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-w)‖ ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => (hfac p hp).2
          _ = 2 ^ q.primeFactors.card := by simp
      rw [Real.log_mul hpos.ne' hζpos.ne']
      have := Real.log_le_log hpos hprod
      rw [Real.log_pow] at this
      simp only [ω]
      linarith
    -- the nonprincipal characters
    have hr : ∀ χ : DirichletCharacter ℂ q, 0 ≤ (subgroupCoeff H χ).re := fun χ => by
      obtain ⟨r, hr0, hcr⟩ := subgroupCoeff_eq_real H χ
      rw [hcr, Complex.ofReal_re]; exact hr0
    have hlogK : 0 ≤ Real.log (1 + K) := Real.log_nonneg (by linarith)
    have hrest : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (subgroupCoeff H χ).re * Real.log ‖LSeries (fun n => χ n) w‖ ≤
          q.totient * Real.log (1 + K) := by
      calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (subgroupCoeff H χ).re * Real.log ‖LSeries (fun n => χ n) w‖
          ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (subgroupCoeff H χ).re * Real.log (1 + K) := by
            refine Finset.sum_le_sum fun χ hχ => mul_le_mul_of_nonneg_left ?_ (hr χ)
            have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
            exact (log_le_log_one_add (norm_nonneg _)).trans
              (Real.log_le_log (by positivity) (by linarith [hLK χ hχ1]))
        _ ≤ ∑ χ : DirichletCharacter ℂ q, (subgroupCoeff H χ).re * Real.log (1 + K) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun χ _ _ => mul_nonneg (hr χ) hlogK
        _ = q.totient * Real.log (1 + K) := by rw [← Finset.sum_mul, sum_re_subgroupCoeff]
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ => (subgroupCoeff H χ).re * Real.log ‖LSeries (fun n => χ n) w‖)
      (Finset.mem_univ 1)
    rw [← hsplit, subgroupCoeff_one, Complex.natCast_re] at hlogF
    -- the `ζ` exponent `a − 1 ∈ [−1, 0]`
    set Z := ‖riemannZeta w‖
    have hZ1 : -Real.log Z ≤ Real.log (1 + Z⁻¹) := by
      rw [← Real.log_inv]; exact log_le_log_one_add (inv_nonneg.mpr hζpos.le)
    have hZ0 : 0 ≤ Real.log (1 + Z⁻¹) := Real.log_nonneg (by have := inv_nonneg.mpr hζpos.le; linarith)
    have hζterm : (1 - a) * -Real.log Z ≤ Real.log (1 + Z⁻¹) := by
      rcases le_total 0 (-Real.log Z) with hx | hx
      · nlinarith
      · nlinarith
    have hlog : Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.log (1 + Z⁻¹) + 2 * Real.log (1 + K) + B'' := by
      have h1 := mul_le_mul_of_nonneg_left hL1 (Nat.cast_nonneg (Nat.card H) : (0 : ℝ) ≤ Nat.card H)
      have h2φ : (0 : ℝ) ≤ 2 / q.totient := by positivity
      have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 hrest) h2φ
      have hae : 2 / (q.totient : ℝ) * (Nat.card H * (Real.log Z + ω * Real.log 2) +
          q.totient * Real.log (1 + K)) = a * Real.log Z + a * (ω * Real.log 2) +
            2 * Real.log (1 + K) := by
        simp only [a]; field_simp
      rw [hae] at h3
      simp only [B'']
      nlinarith
    rcases (norm_nonneg (∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w))).eq_or_lt with h0 | hFpos
    · rw [← h0]; positivity
    · rw [← Real.exp_log hFpos]
      calc Real.exp (Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖)
          ≤ Real.exp (Real.log (1 + Z⁻¹) + 2 * Real.log (1 + K) + B'') := Real.exp_le_exp.mpr hlog
        _ = Real.exp B'' * (1 + Z⁻¹) * (1 + K) ^ 2 := by
            rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
              show 2 * Real.log (1 + K) = Real.log ((1 + K) ^ 2) by rw [Real.log_pow]; push_cast; ring,
              Real.exp_log (by positivity)]
            ring
  refine ⟨Real.exp B'' * (1 + K₂) * (1 + Mt) ^ 2,
    Real.exp B'' * (1 + K₁) * (1 + CQ) ^ 2 * 48 ^ 12, fun w hw hw2 => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · -- the box
    have hmem : w ∈ Kb := Complex.mem_reProdIm.mpr ⟨⟨hw.le, hw2⟩, abs_le.mp ht⟩
    have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun χ _ => abs_nonneg _
    refine (hmaster w hw Mt hMt0 fun χ hχ => ?_).trans ?_
    · rw [← DirichletCharacter.LFunction_eq_LSeries _ hw]; exact hMt χ hχ w hmem
    · have hz := hζbox w hw hw2 ht
      gcongr
  · -- large heights
    set σ := w.re
    set t := w.im
    have hwst : w = (σ : ℂ) + (t : ℂ) * I := (Complex.re_add_im w).symm
    set L := Real.log |t|
    have hL2 : 2 ≤ L := by
      have h1 : Real.log (Real.exp 2) ≤ Real.log |t| :=
        Real.log_le_log (Real.exp_pos 2) (by have := RHTower.exp_two_lt_eight; linarith)
      rwa [Real.log_exp] at h1
    have hL1 : 1 ≤ L := by linarith
    have hσL : 1 - 1 / L ≤ σ := by
      have : 0 < 1 / L := by positivity
      linarith
    have hK0 : 0 ≤ CQ * L := by positivity
    refine (hmaster w hw (CQ * L) hK0 fun χ hχ => ?_).trans ?_
    · rw [← DirichletCharacter.LFunction_eq_LSeries _ hw, hwst]
      exact RHTower.norm_LFunction_le_log χ (by linarith) hσL hw2
    · have hz := hζL w hw hw2 ht
      have hL10 : 1 ≤ L ^ 10 := one_le_pow₀ hL1
      have hpoly : (1 + ‖riemannZeta w‖⁻¹) * (1 + CQ * L) ^ 2 ≤ (1 + K₁) * (1 + CQ) ^ 2 * L ^ 12 := by
        have h1 : 1 + ‖riemannZeta w‖⁻¹ ≤ (1 + K₁) * L ^ 10 := by nlinarith
        have h2 : 1 + CQ * L ≤ (1 + CQ) * L := by nlinarith
        have h2' := pow_le_pow_left₀ (by positivity) h2 2
        calc (1 + ‖riemannZeta w‖⁻¹) * (1 + CQ * L) ^ 2 ≤ ((1 + K₁) * L ^ 10) * ((1 + CQ) * L) ^ 2 :=
              mul_le_mul h1 h2' (by positivity) (by positivity)
          _ = (1 + K₁) * (1 + CQ) ^ 2 * L ^ 12 := by ring
      have hlog12 := log_pow_twelve_le_rpow (show (1 : ℝ) ≤ |t| by linarith)
      calc Real.exp B'' * (1 + ‖riemannZeta w‖⁻¹) * (1 + CQ * L) ^ 2
          = Real.exp B'' * ((1 + ‖riemannZeta w‖⁻¹) * (1 + CQ * L) ^ 2) := by ring
        _ ≤ Real.exp B'' * ((1 + K₁) * (1 + CQ) ^ 2 * L ^ 12) :=
            mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
        _ ≤ Real.exp B'' * ((1 + K₁) * (1 + CQ) ^ 2 * (48 ^ 12 * |t| ^ (1 / 4 : ℝ))) := by
            gcongr
        _ = Real.exp B'' * (1 + K₁) * (1 + CQ) ^ 2 * 48 ^ 12 * |t| ^ (1 / 4 : ℝ) := by ring

/-! ### The receiver of a subgroup flip -/

open Classical in
/-- **Subgroup flips are paid at half damping.** For a subgroup `H ≤ (ZMod q)ˣ` with
`2|H| ≤ φ(q)`, the pattern flipping every prime outside `H` gives a paid half-damped weight. -/
theorem receiverBounded_subgroupFlip_half {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hk : 2 * Nat.card H ≤ q.totient) :
    ReceiverBounded (fun d => residueFlip q (subgroupFlipSet H) d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨B₀, B₁, hB⟩ := exists_norm_subgroupFlip_le H hk
  set f := residueFlip q (subgroupFlipSet H)
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_residueFlip_le_one q _ d)
  set P : ℝ := ∑' d : ℕ, c d / d
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hbd : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      1 < ((σ : ℂ) + t * I + 1 / 2).re ∧ ((σ : ℂ) + t * I + 1 / 2).re ≤ 2 :=
    fun σ t hσ hσ' => by rw [hwre]; constructor <;> linarith
  have hCP : ∀ σ t : ℝ, ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I + 1 / 2))‖ + |P| := fun σ t => by
    rw [weightDirichletSeries_pattern]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    rw [Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_bounds (c := c) (P := P) (B₀ := |B₀| + |P|)
    (B₁ := |B₀| + |B₁| + |P|)
    (fun σ t hσ hσ' ht => (hCP σ t).trans (by
      have := (hB _ (hbd σ t hσ hσ').1 (hbd σ t hσ hσ').2).1 (by rw [hwim]; linarith)
      linarith [le_abs_self B₀]))
    (fun σ t hσ hσ' ht => (hCP σ t).trans (by
      have h1 : 1 ≤ |t| ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hP := abs_nonneg P
      rcases le_total |t| 9 with h9 | h9
      · have := (hB _ (hbd σ t hσ hσ').1 (hbd σ t hσ hσ').2).1 (by rw [hwim]; exact h9)
        nlinarith [le_abs_self B₀, abs_nonneg B₀, abs_nonneg B₁]
      · have := (hB _ (hbd σ t hσ hσ').1 (hbd σ t hσ hσ').2).2 (by rw [hwim]; exact h9)
        rw [hwim] at this
        nlinarith [le_abs_self B₁, abs_nonneg B₀, abs_nonneg B₁,
          mul_le_mul_of_nonneg_right (le_abs_self B₁) (by positivity : (0 : ℝ) ≤ |t| ^ (1 / 4 : ℝ))]))
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hc hM⟩

open Classical in
/-- `S_H` consists of the `φ(q) − |H|` units outside `H`. -/
theorem card_filter_isUnit_subgroupFlipSet {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    ((subgroupFlipSet H).filter IsUnit).card = q.totient - Nat.card H := by
  have hfilt : (subgroupFlipSet H).filter IsUnit = subgroupFlipSet H := by
    ext a
    simp only [subgroupFlipSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have himage : subgroupFlipSet H =
      (Finset.univ.filter fun u : (ZMod q)ˣ => u ∉ H).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    simp only [subgroupFlipSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, InSubgroup]
    constructor
    · rintro ⟨⟨u, rfl⟩, hnot⟩
      exact ⟨u, fun hu => hnot ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.isUnit, fun ⟨h, hh, he⟩ => hu ?_⟩
      rwa [← Units.ext he]
  rw [hfilt, himage, Finset.card_map, Finset.filter_not,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
    ZMod.card_units_eq_totient]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
/-- **The damping threshold of a subgroup flip is exactly `1/2`.** For `H ≤ (ZMod q)ˣ` of index at
least three (`3|H| ≤ φ(q)`) and `ε > 0`, the weight `f_H(d) d^{-ε}` is paid iff `ε ≥ 1/2`. -/
theorem receiverBounded_subgroupFlip_iff {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (h3 : 3 * Nat.card H ≤ q.totient) {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (fun d => residueFlip q (subgroupFlipSet H) d * (d : ℝ) ^ (-ε)) ↔
      1 / 2 ≤ ε := by
  have hH1 : 1 ≤ Nat.card H := Nat.card_pos
  have hcard := card_filter_isUnit_subgroupFlipSet H
  constructor
  · intro hpaid
    by_contra hlt
    exact not_receiverBounded_residueFlip hε (not_le.mp hlt) (subgroupFlipSet H)
      (by rw [hcard]; omega) (by rw [hcard]; omega) hpaid
  · intro hε2
    rcases hε2.eq_or_lt with heq | hgt
    · subst heq
      exact receiverBounded_subgroupFlip_half H (by omega)
    · obtain ⟨E, hE⟩ := (uniformReceiverBound_iff_half_lt (K := 1) one_pos hε).mpr hgt
      refine ⟨E, hE _ fun d => ?_⟩
      rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
        (abs_residueFlip_le_one q _ d)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_subgroupFlip_iff
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_subgroupFlip_half
