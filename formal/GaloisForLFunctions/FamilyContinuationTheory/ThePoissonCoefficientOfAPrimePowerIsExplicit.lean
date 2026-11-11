import GaloisForLFunctions.FamilyContinuationTheory.ThePrimeGaussIdentitiesFixTheLocalPhases
import GaloisForLFunctions.FamilyContinuationTheory.ThePoissonCoefficientOfAPrimePowerIsOneGaussSum

/-!
# The Poisson coefficient of a prime power is explicit

At a primary prime `π ∤ 6` of `O = ℤ[ω]` with `N(π) = Q`, sextic residue character `χ`, trace
character `ψ = ψ_π` and Gauss sums `G_r = Σ_x χ(x)^r ψ(x)`, the Poisson coefficient
`F(π^k, π^t; H)` of the cubic-theta probe is

* `Q^{-t}` times the local transform `P(t, k; H)` (`localPoisson_eq_poissonCoeff`): the row
  Gauss sum modulo `π^{t+k}` is `Q^t g_{π^k}(−m)` (`rowGauss_eq`);
* twisted by a unit `h` of the frequency through `χ(h)^k χ(h)^{−t}`
  (`poissonCoeff_unit_mul`);
* at the frequency `π^j` given by the layer values `L_r(n, j)`
  (`layerGauss_mulChar_pow`): `L_r(n, j) = Q^{n−1} G_r [j = n−1]` for `6 ∤ r`, and the
  Ramanujan sum `Q^n [n ≤ j] − Q^{n−1} [n−1 ≤ j]` for `6 ∣ r`;

so that, for `t ≥ 1`, `F(1, π^t; π^j) = L_t(t, j)`, `F(π, π^t; π^j) = χ(−1) G₁ L_{t−1}(t+1, j)`
and `F(π^k, π^t; π^j) = 0` for `k ≥ 2`; for `t = 0`, `F(π^k, 1; π^j) = Q^k [j = 0]`.

The corrected coefficient at a prime power is
`K(π^k, π^{e}, π^{l}; H) = χ(−1)^{tk} γ₂(π^e) G(π^t)⁻¹ F(π^k, π^t; H)`, `t = e + 3l`
(`correctedCoeff_prime_pow`), with `G(π^t) = \overline{χ(4)}^t Γ(π)^{t mod 2}`
(`thetaPhase_prime_pow`). These are the entries of the local table of the scalar Euler
identity.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The trace character depends only on the element of the modulus. -/
theorem principalTraceChar_congr {N N' : O} (h : N = N') (hN : N ≠ 0) (hN' : N' ≠ 0) (x : O) :
    principalTraceChar N hN (Ideal.Quotient.mk _ x) =
      principalTraceChar N' hN' (Ideal.Quotient.mk _ x) := by
  subst h
  rfl

/-- A representative differs from the element by a multiple of the modulus. -/
theorem dvd_qrep_mk_sub (N x : O) : N ∣ qrep (Ideal.Quotient.mk (Ideal.span {N}) x) - x := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]

/-- The Poisson coefficient at `s = A = 1` is one. -/
theorem poissonCoeff_of_eq_one {s A : O} [NeZero s] [NeZero A] (hs : s = 1) (hA : A = 1) (H : O) :
    poissonCoeff s A H = 1 := by
  subst hs hA
  have hsub : Subsingleton (O ⧸ Ideal.span {(1 : O) * 1}) := by
    rw [mul_one, Ideal.span_singleton_one]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  have hg : ∀ x : O, sexticGauss 1 x = 1 := by
    intro x
    have hsub1 : Subsingleton (O ⧸ Ideal.span {(1 : O)}) := by
      rw [Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    unfold sexticGauss sexticGaussPow
    rw [Fintype.sum_subsingleton _ 0, Subsingleton.elim (Ideal.Quotient.mk _ x * 0) 0,
      AddChar.map_zero_eq_one, mul_one, pow_one, sexticResidue, sexticSymbol_one_denominator]
  unfold poissonCoeff residueFourier
  rw [Fintype.sum_subsingleton _ 0, Subsingleton.elim (Ideal.Quotient.mk _ H * 0) 0,
    AddChar.map_zero_eq_one, mul_one]
  dsimp only
  rw [hg, mul_one]
  exact sexticSymbol_one_denominator _

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

/-! ### From the global coefficient to the local transform -/

include h2 hprim in
/-- **The row sum.** `I(m) = Q^t g_{π^k}(−m)` modulo `π^{t+k}`. -/
theorem rowGauss_eq {t k : ℕ} (hn : 1 ≤ t + k) (x : O) :
    rowGauss π (complexSexticChar (Ideal.span {π}) hlam) hn (Ideal.Quotient.mk _ x) =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t * sexticGauss (π ^ k) (-x) := by
  set χ := complexSexticChar (Ideal.span {π}) hlam
  let f : O ⧸ Ideal.span {π ^ (t + k)} →+* O ⧸ Ideal.span {π ^ k} :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow π (Nat.le_add_left k t)))
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective e
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hQ : (Ideal.absNorm (Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← card_quot_span]
    exact_mod_cast Fintype.card_ne_zero
  have hker : ((Finset.univ.filter fun d => f d = 0).card : ℂ) =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t := by
    have hc := card_eq_card_ker_mul f hf
    rw [card_quot_span_pow, card_quot_span_pow, pow_add] at hc
    exact mul_right_cancel₀ (pow_ne_zero k hQ) hc.symm
  have hterm : ∀ d : O ⧸ Ideal.span {π ^ (t + k)},
      χ (layerReduction π hn d) ^ k * principalTraceChar (π ^ (t + k)) (NeZero.ne _)
          (-(Ideal.Quotient.mk _ (π ^ t) * Ideal.Quotient.mk _ x * d)) =
        sexticResidue (π ^ k) (f d) ^ 1 *
          principalTraceChar (π ^ k) (NeZero.ne _) (Ideal.Quotient.mk _ (-x) * f d) := by
    intro d
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hfy : f (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y := rfl
    rw [hfy, pow_one, sexticResidue_mk, sexticSymbol_prime_pow π hlam h2 hprim, layerReduction_mk,
      ← map_mul, ← map_mul, ← map_neg, ← map_mul,
      principalTraceChar_congr (show π ^ (t + k) = π ^ t * π ^ k by ring) _
        (mul_ne_zero (NeZero.ne _) (NeZero.ne _)),
      show -(π ^ t * x * y) = π ^ t * (-x * y) by ring, principalTraceChar_mul_right]
  unfold rowGauss sexticGauss sexticGaussPow
  rw [Finset.sum_congr rfl fun d _ => hterm d,
    sum_comp_eq_card_mul f hf (fun e => sexticResidue (π ^ k) e ^ 1 *
      principalTraceChar (π ^ k) (NeZero.ne _) (Ideal.Quotient.mk _ (-x) * e)), hker]

include h2 hprim in
/-- **The local transform is the Poisson coefficient.** `P(t, k; H) = Q^t F(π^k, π^t; H)`. -/
theorem localPoisson_eq_poissonCoeff {t k : ℕ} (hn : 1 ≤ t + k) (H : O) :
    localPoisson π (complexSexticChar (Ideal.span {π}) hlam) hn H =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t * poissonCoeff (π ^ k) (π ^ t) H := by
  rw [poissonCoeff, residueFourier_congr (show π ^ k * π ^ t = π ^ (t + k) by ring),
    residueFourier, Finset.mul_sum]
  unfold localPoisson
  refine Finset.sum_congr rfl fun m _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hd := dvd_qrep_mk_sub (π ^ (t + k)) x
  rw [rowGauss_eq π hlam h2 hprim, layerReduction_mk,
    sexticSymbol_congr ((pow_dvd_pow π (Nat.le_add_right t k)).trans hd),
    sexticSymbol_prime_pow π hlam h2 hprim,
    sexticGauss_congr (π ^ k) (show π ^ k ∣ -qrep (Ideal.Quotient.mk _ x) - -x by
      rw [neg_sub_neg]
      exact dvd_sub_comm.mp ((pow_dvd_pow π (Nat.le_add_left k t)).trans hd))]
  ring

/-! ### The unit part of the frequency -/

omit [NeZero π] in
/-- A residue outside `(π)` is a unit modulo the prime `π`. -/
theorem unit_mk_of_not_mem {h : O} (hh : h ∉ Ideal.span {π}) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {π}) h) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  exact isUnit_iff_ne_zero.mpr fun h0 => hh (Ideal.Quotient.eq_zero_iff_mem.mp h0)

include h2 hprim in
/-- **The unit twist.** For `π ∤ h`: `F(π^k, π^t; hH) = χ(h)^k χ(h)^{−t} F(π^k, π^t; H)`. -/
theorem poissonCoeff_unit_mul (k t : ℕ) {h : O} (hh : h ∉ Ideal.span {π}) (H : O) :
    poissonCoeff (π ^ k) (π ^ t) (h * H) =
      complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ h) ^ k *
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ h) ^ t)⁻¹ *
          poissonCoeff (π ^ k) (π ^ t) H := by
  have hpr := prime_of_isMaximal_span π
  have hcop : IsCoprime h π :=
    (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr
      (fun hd => hh (Ideal.mem_span_singleton.mpr hd)) |>.symm
  have hw : IsCoprime h (π ^ k * π ^ t) := (hcop.pow_right).mul_right hcop.pow_right
  have htw := sexticSymbol_mul_poissonCoeff (π ^ k) (π ^ t) hw H
  rw [sexticSymbol_prime_pow π hlam h2 hprim, sexticSymbol_prime_pow π hlam h2 hprim] at htw
  have hu : complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ h) ≠ 0 :=
    (IsUnit.map _ (unit_mk_of_not_mem π hh)).ne_zero
  set c := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ h)
  calc poissonCoeff (π ^ k) (π ^ t) (h * H) =
      (c ^ t)⁻¹ * (c ^ t * poissonCoeff (π ^ k) (π ^ t) (h * H)) := by
        rw [inv_mul_cancel_left₀ (pow_ne_zero t hu)]
    _ = c ^ k * (c ^ t)⁻¹ * poissonCoeff (π ^ k) (π ^ t) H := by rw [← htw]; ring

/-! ### Layer values -/

omit [NeZero π] in
include h2 in
/-- The sextic residue character has exact order six. -/
theorem complexSexticChar_pow_eq_one_iff (r : ℕ) :
    complexSexticChar (Ideal.span {π}) hlam ^ r = 1 ↔ 6 ∣ r := by
  set χ := complexSexticChar (Ideal.span {π}) hlam
  obtain ⟨hc2, hc3, h6⟩ := complexSexticChar_powers (Ideal.span {π}) hlam
  have hne2 : ¬ orderOf χ ∣ 2 := fun h => complexCubicChar_ne_one _ hlam
    (hc2 ▸ orderOf_dvd_iff_pow_eq_one.mp h)
  have hne3 : ¬ orderOf χ ∣ 3 := fun h => complexQuadraticChar_ne_one _ (ringChar_ne_two π h2)
    (hc3 ▸ orderOf_dvd_iff_pow_eq_one.mp h)
  have hd : orderOf χ ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hord : orderOf χ = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    set n := orderOf χ
    interval_cases n <;> omega
  rw [← orderOf_dvd_iff_pow_eq_one, hord]

/-- The value of the layer sum of `χ^r` modulo `π^n` at the frequency `π^j`:
`Q^{n−1} G_r [j = n−1]` for `6 ∤ r`, the Ramanujan sum `Q^n [n ≤ j] − Q^{n−1} [n−1 ≤ j]` for
`6 ∣ r`. -/
def sexticLayer (r n j : ℕ) : ℂ :=
  if 6 ∣ r then
    (if n ≤ j then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ n else 0) -
      (if n - 1 ≤ j then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (n - 1) else 0)
  else if j = n - 1 then
    (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (n - 1) *
      gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ r) (principalTraceChar π (NeZero.ne π))
  else 0

omit hP in
/-- `π^b ∈ (π^a) ↔ a ≤ b` for a prime `π`. -/
theorem pow_mem_span_pow_iff (hpr : Prime π) (a b : ℕ) :
    π ^ b ∈ Ideal.span {π ^ a} ↔ a ≤ b := by
  rw [Ideal.mem_span_singleton]
  exact pow_dvd_pow_iff (NeZero.ne π) hpr.not_unit

include h2 in
/-- **The layer sums of the powers of `χ`** at the frequency `π^j`. -/
theorem layerGauss_mulChar_pow (r : ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    layerGauss π hn (fun e => (complexSexticChar (Ideal.span {π}) hlam ^ r) e) (π ^ j) =
      sexticLayer π hlam r n j := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hpr := prime_of_isMaximal_span π
  set χ := complexSexticChar (Ideal.span {π}) hlam
  unfold sexticLayer
  by_cases h6 : 6 ∣ r
  · have h1 : χ ^ r = 1 := (complexSexticChar_pow_eq_one_iff π hlam h2 r).mpr h6
    have hfun : (fun e => (χ ^ r) e) = fun e => if e = 0 then 0 else 1 := by
      funext e
      rw [h1]
      by_cases he : e = 0
      · rw [if_pos he, he, MulChar.map_zero]
      · rw [if_neg he, MulChar.one_apply (isUnit_iff_ne_zero.mpr he)]
    rw [if_pos h6, hfun, layerGauss_one]
    simp only [pow_mem_span_pow_iff π hpr]
  · rw [if_neg h6]
    have h1 : χ ^ r ≠ 1 := fun h => h6 ((complexSexticChar_pow_eq_one_iff π hlam h2 r).mp h)
    by_cases hj : n - 1 ≤ j
    · obtain ⟨d, rfl⟩ : ∃ d, j = n - 1 + d := ⟨j - (n - 1), by omega⟩
      rw [pow_add, layerGauss_eq]
      by_cases hd : d = 0
      · subst hd
        rw [if_pos (by omega), pow_zero, map_one]
        simp only [one_mul]
        rfl
      · rw [if_neg (by omega)]
        have h0 : Ideal.Quotient.mk (Ideal.span {π}) (π ^ d) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          exact dvd_pow_self π hd
        simp only [h0, zero_mul, AddChar.map_zero_eq_one, mul_one]
        rw [MulChar.sum_eq_zero_of_ne_one h1, mul_zero]
    · rw [layerGauss_eq_zero π hn _ (by rw [pow_mem_span_pow_iff π hpr]; omega), if_neg (by omega)]

/-! ### The values of the Poisson coefficient -/

include hlam h2 hprim in
/-- **`t = 0`.** `F(π^k, 1; π^j) = Q^k [j = 0]` for `k ≥ 1`. -/
theorem poissonCoeff_pow_zero_right {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    poissonCoeff (π ^ k) (π ^ 0) (π ^ j) =
      if j = 0 then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ k else 0 := by
  have h := localPoisson_eq_poissonCoeff π hlam h2 hprim (t := 0) (k := k) (by omega) (π ^ j)
  rw [localPoisson_zero_left, pow_zero, one_mul, zero_add] at h
  rw [← h]
  split_ifs with hj
  · rw [hj, pow_zero, map_one, MulChar.map_one, one_pow, mul_one]
  · have h0 : Ideal.Quotient.mk (Ideal.span {π}) (π ^ j) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact dvd_pow_self π hj
    rw [h0, MulChar.map_zero, zero_pow (by omega), mul_zero]

include h2 hprim in
/-- **`k = 0`.** `F(1, π^t; π^j) = L_t(t, j)` for `t ≥ 1`. -/
theorem poissonCoeff_pow_zero_left {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    poissonCoeff (π ^ 0) (π ^ t) (π ^ j) = sexticLayer π hlam t t j := by
  have hQ : (Ideal.absNorm (Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← card_quot_span]
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ t + 0 := ht
  have h := localPoisson_eq_poissonCoeff π hlam h2 hprim hn (π ^ j)
  rw [localPoisson_zero_right] at h
  have hfun : (fun e => complexSexticChar (Ideal.span {π}) hlam e ^ t) =
      fun e => (complexSexticChar (Ideal.span {π}) hlam ^ t) e := by
    funext e
    rw [MulChar.pow_apply' _ (by omega)]
  rw [hfun, layerGauss_mulChar_pow π hlam h2] at h
  exact (mul_left_cancel₀ (pow_ne_zero t hQ) h).symm

include h2 hprim in
/-- **`k = 1`.** `F(π, π^t; π^j) = χ(−1) G₁ L_{t−1}(t+1, j)` for `t ≥ 1`. -/
theorem poissonCoeff_pow_one_left {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    poissonCoeff (π ^ 1) (π ^ t) (π ^ j) =
      complexSexticChar (Ideal.span {π}) hlam (-1) *
        gaussSum (complexSexticChar (Ideal.span {π}) hlam) (principalTraceChar π (NeZero.ne π)) *
          sexticLayer π hlam (t - 1) (t + 1) j := by
  have hQ : (Ideal.absNorm (Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← card_quot_span]
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ t + 1 := by omega
  have h := localPoisson_eq_poissonCoeff π hlam h2 hprim hn (π ^ j)
  have h1 := localPoisson_one π (complexSexticChar (Ideal.span {π}) hlam) ht hn (π ^ j)
  rw [layerGauss_mulChar_pow π hlam h2, h, mul_assoc, mul_assoc] at h1
  have h1' := mul_left_cancel₀ (pow_ne_zero t hQ) h1
  have hsq := mulChar_neg_one_sq (complexSexticChar (Ideal.span {π}) hlam)
  linear_combination complexSexticChar (Ideal.span {π}) hlam (-1) * h1' -
    poissonCoeff (π ^ 1) (π ^ t) (π ^ j) * hsq

include hlam h2 hprim in
/-- **`k ≥ 2`.** `F(π^k, π^t; H) = 0` for `t ≥ 1`. -/
theorem poissonCoeff_pow_eq_zero {t k : ℕ} (ht : 1 ≤ t) (hk : 2 ≤ k) (H : O) :
    poissonCoeff (π ^ k) (π ^ t) H = 0 := by
  have hQ : (Ideal.absNorm (Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← card_quot_span]
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ t + k := by omega
  have h := localPoisson_eq_poissonCoeff π hlam h2 hprim hn H
  rw [localPoisson_eq_zero π _ ht hk hn] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero t hQ)

/-! ### The corrected coefficient at a prime power -/

include h2 in
/-- Powers of `π` are odd. -/
theorem prime_pow_odd (n : ℕ) : π ^ n ∉ Ideal.span {(2 : O)} := by
  induction n with
  | zero => rw [pow_zero]; exact not_mem_two_of_isCoprime isCoprime_one_left
  | succ n ih => rw [pow_succ]; exact odd_mul ih (prime_odd π h2)

include h2 in
/-- `r(π, π^b) = r(π, π)^b`. -/
theorem quadraticPhase_prime_pow_right (b : ℕ) :
    quadraticPhase π (π ^ b) = quadraticPhase π π ^ b := by
  have hodd := prime_odd π h2
  induction b with
  | zero =>
    rw [pow_zero, pow_zero, quadraticPhase_comm]
    exact quadraticPhase_one_left hodd
  | succ b ih =>
    rw [pow_succ, quadraticPhase_mul_right hodd (prime_pow_odd π h2 b) hodd, ih, pow_succ]

include h2 in
/-- **`r(π^a, π^b) = r(π, π)^{ab}`.** -/
theorem quadraticPhase_prime_pow (a b : ℕ) :
    quadraticPhase (π ^ a) (π ^ b) = quadraticPhase π π ^ (a * b) := by
  induction a with
  | zero => rw [pow_zero, zero_mul, pow_zero]; exact quadraticPhase_one_left (prime_pow_odd π h2 b)
  | succ a ih =>
    rw [pow_succ, quadraticPhase_mul_left (prime_pow_odd π h2 a) (prime_odd π h2)
      (prime_pow_odd π h2 b), ih, quadraticPhase_prime_pow_right π h2, ← pow_add]
    congr 1
    ring

include h2 hprim in
/-- **`G(π^t) = \overline{χ(4)}^t Γ(π)^{t mod 2}`.** -/
theorem thetaPhase_prime_pow (t : ℕ) :
    thetaPhase (π ^ t) =
      starRingEnd ℂ (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 4)) ^ t *
        fixedDualAverage π ^ (t % 2) := by
  unfold thetaPhase
  rw [sexticSymbol_prime_pow π hlam h2 hprim, map_pow]
  congr 1
  have hsplit : π ^ t = π ^ (t % 2) * (π ^ (t / 2)) ^ 2 := by
    rw [← pow_mul, ← pow_add, mul_comm (t / 2) 2, Nat.mod_add_div]
  rw [hsplit, gamma_mul_sq (prime_pow_odd π h2 _) (prime_pow_odd π h2 _)]
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> rw [h]
  · rw [pow_zero, pow_zero, fixedDualAverage_one]
  · rw [pow_one, pow_one]

/-- `γ₂(1) = 1`. -/
theorem thetaGauss_of_eq_one {c : O} [NeZero c] (hc : c = 1) : thetaGauss c = 1 := by
  subst hc
  have hsub : Subsingleton (O ⧸ Ideal.span {(1 : O)}) := by
    rw [Ideal.span_singleton_one]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  unfold thetaGauss sexticGaussPow
  rw [Fintype.sum_subsingleton _ 0, Subsingleton.elim (Ideal.Quotient.mk _ 1 * 0) 0,
    AddChar.map_zero_eq_one, mul_one, sexticResidue, sexticSymbol_one_denominator, one_pow,
    map_one, norm_one, Complex.ofReal_one, div_one]

/-- `γ₂` depends only on the element. -/
theorem thetaGauss_congr {c c' : O} [NeZero c] [NeZero c'] (h : c = c') :
    thetaGauss c = thetaGauss c' := by
  subst h
  rfl

include h2 hprim in
/-- **`γ₂(π) = G₂/|π|`.** -/
theorem thetaGauss_prime :
    thetaGauss π = gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 2)
      (principalTraceChar π (NeZero.ne π)) / (‖ringComplex π‖ : ℂ) := by
  unfold thetaGauss sexticGaussPow gaussSum
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [sexticResidue_mk, sexticSymbol_prime π hlam h2 hprim, map_one, one_mul,
    MulChar.pow_apply' _ (by norm_num)]

include h2 in
/-- **The corrected coefficient at a prime power.** With `t = e + 3l`,
`K(π^k, π^e, π^l; H) = r(π, π)^{tk} γ₂(π^e) G(π^t)⁻¹ F(π^k, π^t; H)`. -/
theorem correctedCoeff_prime_pow (e l k : ℕ) (H : O) :
    correctedCoeff (π ^ k) (π ^ e) (π ^ l) H =
      quadraticPhase π π ^ ((e + 3 * l) * k) * thetaGauss (π ^ e) *
        (thetaPhase (π ^ (e + 3 * l)))⁻¹ * poissonCoeff (π ^ k) (π ^ (e + 3 * l)) H := by
  have hA : π ^ e * (π ^ l) ^ 3 = π ^ (e + 3 * l) := by ring
  unfold correctedCoeff
  rw [poissonCoeff_congr_index (π ^ k) hA H, hA, quadraticPhase_prime_pow π h2]
  ring

end Prime

end GaloisForLFunctions.FamilyContinuationTheory
