import GaloisForLFunctions.RHTower.QuadraticGaussSumSign

/-!
# Square and fourth-power laws of quadratic Gauss sums

For `q > 0` and `(a, q) = 1`, the quadratic Gauss sum `G(a; q) = Σ_{r mod q} e(a r²/q)` satisfies

`G(a; q)² = χ₄(q) q` (`q` odd),   `G(a; q) = 0` (`q ≡ 2 mod 4`),   `G(a; q)² = 2 q i χ₄(a)` (`4 ∣ q`),

hence `G(a; q)^4 = q²`, `0`, `-4 q²` respectively.

The proof reindexes over `ZMod`: the Chinese remainder factorization
`G(a; mn) = G(an; m) G(am; n)`, the odd prime-power reduction `G(a; ℓ^{k+2}) = ℓ G(a; ℓ^k)`,
the two-adic reduction `G(a; 2^{k+4}) = 2 G(a; 2^{k+2})` with the explicit values at `2, 4, 8`,
and Gauss's evaluation at an odd prime (`QuadraticGaussSumSign`) through the Legendre twist.
In particular `|G(a; q)| = √q` for odd `q`.
-/
open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower.HalfWeight

/-! ## Quadratic Gauss sums over `ZMod` -/

theorem stdAddChar_intCast_eq (q : ℕ) [NeZero q] (t : ℤ) :
    ZMod.stdAddChar (N := q) (t : ZMod q) = cexp (2 * Real.pi * I * t / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_intCast]

/-- `e(t e / N) = e(t / d)` whenever `N = d e`. -/
theorem stdAddChar_intCast_mul {N d e : ℕ} [NeZero N] [NeZero d] (h : (N : ℂ) = d * e) (t : ℤ) :
    ZMod.stdAddChar (N := N) ((t * e : ℤ) : ZMod N) = ZMod.stdAddChar (N := d) (t : ZMod d) := by
  have he : (e : ℂ) ≠ 0 := by
    intro he; have : (N : ℂ) = 0 := by rw [h, he, mul_zero]
    exact NeZero.ne N (by exact_mod_cast this)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [stdAddChar_intCast_eq, stdAddChar_intCast_eq, h]
  congr 1
  push_cast
  field_simp

theorem gaussQ_eq_sum_zmod (a : ℤ) (c : ℕ) [NeZero c] :
    gaussQ a c = ∑ x : ZMod c, ZMod.stdAddChar ((a : ZMod c) * x ^ 2) := by
  unfold gaussQ
  let e : Fin c ≃ ZMod c :=
    { toFun := fun r => ((r : ℕ) : ZMod c)
      invFun := fun a => ⟨a.val, ZMod.val_lt a⟩
      left_inv := fun r => Fin.ext (ZMod.val_natCast_of_lt r.2)
      right_inv := fun a => ZMod.natCast_zmod_val a }
  refine Fintype.sum_equiv e _ _ fun r => ?_
  simp only [e, Equiv.coe_fn_mk]
  have h := stdAddChar_intCast_eq c (a * ((r : ℕ) : ℤ) ^ 2)
  push_cast at h
  rw [h]
  congr 1
  ring

/-- Base-`b` digit reindexing: `y = r + b w`. -/
theorem sum_zmod_digits {N b c : ℕ} [NeZero N] [NeZero b] [NeZero c] (h : N = b * c)
    (f : ZMod N → ℂ) :
    ∑ y : ZMod N, f y = ∑ r : ZMod b, ∑ w : ZMod c, f ((r.val + b * w.val : ℕ) : ZMod N) := by
  rw [← Fintype.sum_prod_type']
  let Φ : ZMod b × ZMod c → ZMod N := fun p => ((p.1.val + b * p.2.val : ℕ) : ZMod N)
  have hlt : ∀ p : ZMod b × ZMod c, p.1.val + b * p.2.val < N := by
    intro p
    have h1 := ZMod.val_lt p.1
    have h2 := ZMod.val_lt p.2
    rw [h]
    nlinarith
  have hinj : Function.Injective Φ := by
    intro p p' hp
    simp only [Φ] at hp
    have hv := congrArg ZMod.val hp
    rw [ZMod.val_natCast_of_lt (hlt p), ZMod.val_natCast_of_lt (hlt p')] at hv
    have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    have e1 : p.1.val = p'.1.val := by
      have := congrArg (· % b) hv
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt p.1),
        Nat.mod_eq_of_lt (ZMod.val_lt p'.1)] using this
    have e2 : p.2.val = p'.2.val := by
      rw [e1] at hv
      have := Nat.add_left_cancel hv
      exact Nat.eq_of_mul_eq_mul_left hb this
    exact Prod.ext (ZMod.val_injective _ e1) (ZMod.val_injective _ e2)
  have hbij : Function.Bijective Φ := by
    refine (Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, ?_⟩
    simp [ZMod.card, h]
  exact (Fintype.sum_bijective Φ hbij _ _ fun p => rfl).symm

/-- Chinese remainder reindexing: `y = u n + v m` for coprime `m, n`. -/
theorem sum_zmod_crt {N m n : ℕ} [NeZero N] [NeZero m] [NeZero n] (h : N = m * n)
    (hmn : Nat.Coprime m n) (f : ZMod N → ℂ) :
    ∑ y : ZMod N, f y =
      ∑ u : ZMod m, ∑ v : ZMod n, f ((u.val : ZMod N) * n + (v.val : ZMod N) * m) := by
  rw [← Fintype.sum_prod_type']
  let Φ : ZMod m × ZMod n → ZMod N := fun p => (p.1.val : ZMod N) * n + (p.2.val : ZMod N) * m
  have hinj : Function.Injective Φ := by
    intro p p' hp
    simp only [Φ] at hp
    have hm : m ∣ N := ⟨n, h⟩
    have hn : n ∣ N := ⟨m, by rw [h, mul_comm]⟩
    have h1 := congrArg (ZMod.castHom hm (ZMod m)) hp
    have h2 := congrArg (ZMod.castHom hn (ZMod n)) hp
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_self, mul_zero, add_zero, zero_add] at h1 h2
    have hu : IsUnit (n : ZMod m) := (ZMod.unitOfCoprime n hmn.symm).isUnit
    have hv : IsUnit (m : ZMod n) := (ZMod.unitOfCoprime m hmn).isUnit
    exact Prod.ext (hu.mul_right_cancel h1) (hv.mul_right_cancel h2)
  have hbij : Function.Bijective Φ := by
    refine (Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, ?_⟩
    simp [ZMod.card, h]
  exact (Fintype.sum_bijective Φ hbij _ _ fun p => rfl).symm

/-! ## Multiplicativity and reductions -/

/-- **Chinese remainder factorization** `G(a; mn) = G(an; m) G(am; n)` for coprime `m, n`. -/
theorem gaussQ_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    (a : ℤ) : gaussQ a (m * n) = gaussQ (a * n) m * gaussQ (a * m) n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [gaussQ_eq_sum_zmod, gaussQ_eq_sum_zmod, gaussQ_eq_sum_zmod, sum_zmod_crt rfl hmn,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  have h0 : ((m * n : ℕ) : ZMod (m * n)) = 0 := ZMod.natCast_self _
  have key : (a : ZMod (m * n)) * ((u.val : ZMod (m * n)) * n + (v.val : ZMod (m * n)) * m) ^ 2 =
      (((a * (u.val : ℤ) ^ 2 * n) * n : ℤ) : ZMod (m * n)) +
        (((a * (v.val : ℤ) ^ 2 * m) * m : ℤ) : ZMod (m * n)) := by
    push_cast at h0 ⊢
    linear_combination (2 * (a : ZMod (m * n)) * u.val * v.val) * h0
  rw [key, AddChar.map_add_eq_mul,
    stdAddChar_intCast_mul (N := m * n) (d := m) (e := n) (by push_cast; ring),
    stdAddChar_intCast_mul (N := m * n) (d := n) (e := m) (by push_cast; ring)]
  congr 2
  · push_cast; rw [ZMod.natCast_zmod_val]; ring
  · push_cast; rw [ZMod.natCast_zmod_val]; ring

theorem gaussQ_one (a : ℤ) : gaussQ a 1 = 1 := by
  simp [gaussQ]

/-- The sum of `e(b v / ℓ)` over `v mod ℓ`. -/
theorem sum_stdAddChar_intCast_mul (ℓ : ℕ) [NeZero ℓ] (b : ℤ) :
    ∑ v : ZMod ℓ, ZMod.stdAddChar (N := ℓ) ((b * (v.val : ℤ) : ℤ) : ZMod ℓ) =
      if (b : ZMod ℓ) = 0 then (ℓ : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := ℓ)) (b : ZMod ℓ)
    (ZMod.isPrimitive_stdAddChar ℓ)
  simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

/-- **Odd prime-power reduction** `G(a; ℓ^{k+2}) = ℓ G(a; ℓ^k)` for `ℓ ∤ 2a`. -/
theorem gaussQ_prime_pow_add_two {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) {a : ℤ}
    (ha : ¬ (ℓ : ℤ) ∣ a) (k : ℕ) : gaussQ a (ℓ ^ (k + 2)) = ℓ * gaussQ a (ℓ ^ k) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  set N := ℓ ^ (k + 2)
  set b := ℓ ^ (k + 1)
  have hN : N = b * ℓ := by simp only [N, b]; ring
  rw [gaussQ_eq_sum_zmod, gaussQ_eq_sum_zmod, sum_zmod_digits hN]
  have hbN : ((b ^ 2 : ℕ) : ZMod N) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨ℓ ^ k, by simp only [N, b]; ring⟩
  have hterm : ∀ (u : ZMod b) (v : ZMod ℓ),
      ZMod.stdAddChar (N := N) ((a : ZMod N) * ((u.val + b * v.val : ℕ) : ZMod N) ^ 2) =
        ZMod.stdAddChar (N := N) ((a * (u.val : ℤ) ^ 2 : ℤ) : ZMod N) *
          ZMod.stdAddChar (N := ℓ) (((2 * a * u.val) * (v.val : ℤ) : ℤ) : ZMod ℓ) := by
    intro u v
    have key : (a : ZMod N) * ((u.val + b * v.val : ℕ) : ZMod N) ^ 2 =
        ((a * (u.val : ℤ) ^ 2 : ℤ) : ZMod N) +
          (((2 * a * u.val) * (v.val : ℤ)) * b : ℤ) := by
      push_cast at hbN ⊢
      linear_combination (a : ZMod N) * (v.val : ZMod N) ^ 2 * hbN
    rw [key, AddChar.map_add_eq_mul,
      stdAddChar_intCast_mul (N := N) (d := ℓ) (e := b) (by simp only [N, b]; push_cast; ring)]
  simp_rw [hterm, ← Finset.mul_sum, sum_stdAddChar_intCast_mul]
  have hdvd : ∀ u : ZMod b, ((2 * a * u.val : ℤ) : ZMod ℓ) = 0 ↔ ℓ ∣ u.val := by
    intro u
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    constructor
    · intro h
      rcases hp.dvd_or_dvd h with h' | h'
      · rcases hp.dvd_or_dvd h' with h'' | h''
        · exfalso
          have : ℓ ∣ 2 := by exact_mod_cast h''
          exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
        · exact absurd h'' ha
      · exact_mod_cast h'
    · intro h
      exact dvd_mul_of_dvd_right (by exact_mod_cast h) _
  simp_rw [hdvd]
  have hb : b = ℓ * ℓ ^ k := by simp only [b]; ring
  rw [sum_zmod_digits (N := b) (b := ℓ) (c := ℓ ^ k) hb, Finset.mul_sum]
  rw [Finset.sum_eq_single (0 : ZMod ℓ)]
  · refine Finset.sum_congr rfl fun w _ => ?_
    have hlt : (0 : ZMod ℓ).val + ℓ * w.val < b := by
      have := ZMod.val_lt w
      simp only [ZMod.val_zero, zero_add, hb]
      exact Nat.mul_lt_mul_of_pos_left this (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [ZMod.val_natCast_of_lt hlt, if_pos ⟨w.val, by simp⟩]
    simp only [ZMod.val_zero, zero_add]
    have e := stdAddChar_intCast_mul (N := N) (d := ℓ ^ k) (e := ℓ ^ 2) (t := a * (w.val : ℤ) ^ 2)
      (by simp only [N]; push_cast; ring)
    have hψ : ZMod.stdAddChar (N := N) ((a * ((ℓ * w.val : ℕ) : ℤ) ^ 2 : ℤ) : ZMod N) =
        ZMod.stdAddChar (N := ℓ ^ k) ((a : ZMod (ℓ ^ k)) * w ^ 2) := by
      rw [show ((a * ((ℓ * w.val : ℕ) : ℤ) ^ 2 : ℤ) : ZMod N) =
          ((a * (w.val : ℤ) ^ 2 * ((ℓ ^ 2 : ℕ) : ℤ) : ℤ) : ZMod N) by push_cast; ring, e]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hψ]
    ring
  · intro r _ hr
    refine Finset.sum_eq_zero fun w _ => ?_
    have hlt : r.val + ℓ * w.val < b := by
      have h1 := ZMod.val_lt r
      have h2 := ZMod.val_lt w
      rw [hb]
      calc r.val + ℓ * w.val < ℓ + ℓ * w.val := by omega
        _ = ℓ * (w.val + 1) := by ring
        _ ≤ ℓ * ℓ ^ k := Nat.mul_le_mul_left _ h2
    rw [ZMod.val_natCast_of_lt hlt, if_neg]
    · simp
    · intro hd
      apply hr
      have : ℓ ∣ r.val := by
        have := (Nat.dvd_add_right (dvd_mul_right ℓ w.val)).mp (by simpa [add_comm] using hd)
        exact this
      have hr0 : r.val = 0 := Nat.eq_zero_of_dvd_of_lt this (ZMod.val_lt r)
      exact (ZMod.val_eq_zero r).mp hr0
  · simp

/-- The sign `χ₄(q)` of an odd modulus: `1` for `q ≡ 1 (mod 4)`, `-1` otherwise. -/
def oddSquareSign (q : ℕ) : ℂ := if q % 4 = 1 then 1 else -1

theorem oddSquareSign_mul {m n : ℕ} (hm : m % 2 = 1) (hn : n % 2 = 1) :
    oddSquareSign (m * n) = oddSquareSign m * oddSquareSign n := by
  unfold oddSquareSign
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases hm4 with h1 | h1 <;> rcases hn4 with h2 | h2 <;>
    simp [Nat.mul_mod, h1, h2]

theorem oddSquareSign_sq (q : ℕ) : oddSquareSign q ^ 2 = 1 := by
  unfold oddSquareSign; split_ifs <;> norm_num

/-- **Gauss's square law at an odd prime**: `G(a; ℓ)² = χ₄(ℓ) ℓ` for `ℓ ∤ a`. -/
theorem gaussQ_prime_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) {a : ℤ}
    (ha : ¬ (ℓ : ℤ) ∣ a) : gaussQ a ℓ ^ 2 = oddSquareSign ℓ * ℓ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have ha0 : (a : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact h2
  set ψ := ZMod.stdAddChar (N := ℓ)
  have h1 : ∑ x : ZMod ℓ, ψ ((a : ZMod ℓ) * x ^ 2) =
      ∑ t : ZMod ℓ, (((Finset.univ.filter fun x : ZMod ℓ => x ^ 2 = t).card : ℕ) : ℂ) *
        ψ ((a : ZMod ℓ) * t) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod ℓ => x ^ 2)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]; simp
  have h2' : ∀ t : ZMod ℓ, (((Finset.univ.filter fun x : ZMod ℓ => x ^ 2 = t).card : ℕ) : ℂ) =
      legendreC ℓ t + 1 := by
    intro t
    have := quadraticChar_card_sqrts hchar t
    unfold legendreC
    rw [MulChar.ringHomComp_apply]
    have e : (Finset.univ.filter fun x : ZMod ℓ => x ^ 2 = t) = {x | x ^ 2 = t}.toFinset := by
      ext x; simp
    rw [e]
    have h := congrArg (fun z : ℤ => (z : ℂ)) this
    push_cast at h
    rw [h]
    rfl
  have hsum0 : ∑ t : ZMod ℓ, ψ ((a : ZMod ℓ) * t) = 0 := by
    have := AddChar.sum_mulShift (ψ := ψ) (a : ZMod ℓ) (ZMod.isPrimitive_stdAddChar ℓ)
    rw [if_neg ha0] at this
    simpa [mul_comm] using this
  have hG : gaussQ a ℓ = gaussSum (legendreC ℓ) (ψ.mulShift (a : ZMod ℓ)) := by
    rw [gaussQ_eq_sum_zmod, h1]
    simp_rw [h2', add_mul, one_mul, Finset.sum_add_distrib, hsum0, add_zero]
    rfl
  have hshift := gaussSum_mulShift (legendreC ℓ) ψ (Units.mk0 (a : ZMod ℓ) ha0)
  rw [Units.val_mk0, gaussSum_legendre ℓ h2] at hshift
  have hχ : legendreC ℓ (a : ZMod ℓ) ^ 2 = 1 := by
    unfold legendreC
    rw [MulChar.ringHomComp_apply]
    have := quadraticChar_sq_one ha0
    have h := congrArg (fun z : ℤ => (z : ℂ)) this
    push_cast at h
    exact h
  have hquad : gaussQuad ℓ ^ 2 = oddSquareSign ℓ * ℓ := by
    have hodd : ℓ % 2 = 1 := Nat.odd_iff.mp (hℓ.odd_of_ne_two h2)
    have hsq : ((Real.sqrt ℓ : ℝ) : ℂ) ^ 2 = ℓ := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg ℓ)]; simp
    unfold oddSquareSign
    rcases (by omega : ℓ % 4 = 1 ∨ ℓ % 4 = 3) with h4 | h4
    · rw [gaussQuad_of_mod_four_eq_one ℓ h4, hsq, if_pos h4, one_mul]
    · rw [gaussQuad_of_mod_four_eq_three ℓ h4, mul_pow, hsq, Complex.I_sq, if_neg (by omega)]
  have hG' : gaussQ a ℓ * legendreC ℓ (a : ZMod ℓ) = gaussQuad ℓ := by
    rw [hG, mul_comm]; exact hshift
  have : (gaussQ a ℓ * legendreC ℓ (a : ZMod ℓ)) ^ 2 = oddSquareSign ℓ * ℓ := by rw [hG', hquad]
  rwa [mul_pow, hχ, mul_one] at this

/-- For an odd prime `ℓ ∤ a`, `G(a; ℓ)^4 = ℓ²`. -/
theorem gaussQ_prime_pow_four {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) {a : ℤ}
    (ha : ¬ (ℓ : ℤ) ∣ a) : gaussQ a ℓ ^ 4 = (ℓ : ℂ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gaussQ_prime_sq hℓ h2 ha, mul_pow,
    oddSquareSign_sq, one_mul]

/-! ## Powers of two -/

theorem cexp_two_pi_I_add_int (x : ℂ) (n : ℤ) :
    cexp (2 * Real.pi * I * (x + n)) = cexp (2 * Real.pi * I * x) := by
  rw [mul_add, Complex.exp_add, show 2 * (Real.pi : ℂ) * I * n = n * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cexp_pi_I_mul_odd {a : ℤ} (ha : Odd a) : cexp (2 * Real.pi * I * (a / 2)) = -1 := by
  obtain ⟨j, rfl⟩ := ha
  rw [show ((2 * j + 1 : ℤ) : ℂ) / 2 = 1 / 2 + (j : ℂ) by push_cast; ring,
    cexp_two_pi_I_add_int, show 2 * (Real.pi : ℂ) * I * (1 / 2) = Real.pi * I by ring,
    Complex.exp_pi_mul_I]

theorem gaussQ_two {a : ℤ} (ha : Odd a) : gaussQ a 2 = 0 := by
  unfold gaussQ
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  rw [show (2 : ℕ) = ((2 : ℕ) : ℂ) from rfl] at *
  have h := cexp_pi_I_mul_odd ha
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, one_pow, mul_one, Nat.cast_ofNat] at h ⊢
  rw [h]; ring

theorem gaussQ_four (a : ℤ) :
    gaussQ a 4 = 2 * (1 + cexp (2 * Real.pi * I * (a / 4))) := by
  unfold gaussQ
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have e2 : ((((3 : Fin 4) : ℕ) : ℂ)) = 3 := by norm_num
  rw [e2]
  have h3 : 2 * (Real.pi : ℂ) * I * (a * 3 ^ 2 / 4) = 2 * Real.pi * I * (a / 4 + ((2 * a : ℤ) : ℂ)) := by
    push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * I * (a * 2 ^ 2 / 4) = 2 * Real.pi * I * (0 + (a : ℂ)) := by ring
  rw [h3, h2, cexp_two_pi_I_add_int, show (a : ℂ) = ((a : ℤ) : ℂ) from rfl, cexp_two_pi_I_add_int]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, one_pow, mul_one]
  ring

theorem gaussQ_eight {a : ℤ} (ha : Odd a) :
    gaussQ a 8 = 4 * cexp (2 * Real.pi * I * (a / 8)) := by
  unfold gaussQ
  rw [Fin.sum_univ_eight]
  have hv : ∀ j : Fin 8, (((j : ℕ) : ℂ)) = ((j : ℕ) : ℂ) := fun _ => rfl
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat]
  have c3 : ((((3 : Fin 8) : ℕ) : ℂ)) = 3 := by norm_num
  have c4 : ((((4 : Fin 8) : ℕ) : ℂ)) = 4 := by norm_num
  have c5 : ((((5 : Fin 8) : ℕ) : ℂ)) = 5 := by norm_num
  have c6 : ((((6 : Fin 8) : ℕ) : ℂ)) = 6 := by norm_num
  have c7 : ((((7 : Fin 8) : ℕ) : ℂ)) = 7 := by norm_num
  rw [c3, c4, c5, c6, c7]
  have hodd := cexp_pi_I_mul_odd ha
  have e1 : ∀ n : ℤ, ∀ m : ℂ, m = (a : ℂ) / 8 + n →
      cexp (2 * Real.pi * I * m) = cexp (2 * Real.pi * I * (a / 8)) := by
    intro n m hm; rw [hm, cexp_two_pi_I_add_int]
  have e2 : ∀ n : ℤ, ∀ m : ℂ, m = (a : ℂ) / 2 + n → cexp (2 * Real.pi * I * m) = -1 := by
    intro n m hm; rw [hm, cexp_two_pi_I_add_int, hodd]
  have e0 : ∀ n : ℤ, ∀ m : ℂ, m = n → cexp (2 * Real.pi * I * m) = 1 := by
    intro n m hm; rw [hm, show (n : ℂ) = 0 + n by ring, cexp_two_pi_I_add_int]; simp
  have t0 : cexp (2 * Real.pi * I * ((a : ℂ) * 0 ^ 2 / 8)) = 1 := e0 0 _ (by push_cast; ring)
  have t1 : cexp (2 * Real.pi * I * ((a : ℂ) * 1 ^ 2 / 8)) = cexp (2 * Real.pi * I * (a / 8)) :=
    e1 0 _ (by push_cast; ring)
  have t2 : cexp (2 * Real.pi * I * ((a : ℂ) * 2 ^ 2 / 8)) = -1 := e2 0 _ (by push_cast; ring)
  have t3 : cexp (2 * Real.pi * I * ((a : ℂ) * 3 ^ 2 / 8)) = cexp (2 * Real.pi * I * (a / 8)) :=
    e1 a _ (by ring)
  have t4 : cexp (2 * Real.pi * I * ((a : ℂ) * 4 ^ 2 / 8)) = 1 := e0 (2 * a) _ (by push_cast; ring)
  have t5 : cexp (2 * Real.pi * I * ((a : ℂ) * 5 ^ 2 / 8)) = cexp (2 * Real.pi * I * (a / 8)) :=
    e1 (3 * a) _ (by push_cast; ring)
  have t6 : cexp (2 * Real.pi * I * ((a : ℂ) * 6 ^ 2 / 8)) = -1 :=
    e2 (4 * a) _ (by push_cast; ring)
  have t7 : cexp (2 * Real.pi * I * ((a : ℂ) * 7 ^ 2 / 8)) = cexp (2 * Real.pi * I * (a / 8)) :=
    e1 (6 * a) _ (by push_cast; ring)
  rw [t0, t1, t2, t3, t4, t5, t6, t7]
  ring

theorem stdAddChar_two_intCast_parity (t : ℤ) :
    ZMod.stdAddChar (N := 2) (t : ZMod 2) = if Even t then 1 else -1 := by
  rw [stdAddChar_intCast_eq]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [show 2 * (Real.pi : ℂ) * I * ((j + j : ℤ) : ℂ) / ((2 : ℕ) : ℂ) = j * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I]
  · have ho : Odd t := Int.not_even_iff_odd.mp h
    have := cexp_pi_I_mul_odd ho
    rw [← this]; congr 1; push_cast; ring

/-- **Two-adic reduction** `G(a; 2^{k+4}) = 2 G(a; 2^{k+2})` for odd `a`. -/
theorem gaussQ_two_pow_add_four {a : ℤ} (ha : Odd a) (k : ℕ) :
    gaussQ a (2 ^ (k + 4)) = 2 * gaussQ a (2 ^ (k + 2)) := by
  set N := 2 ^ (k + 4)
  set b := 2 ^ (k + 2)
  set c := 2 ^ (k + 1)
  have hN : N = b * 4 := by simp only [N, b]; ring
  have hb : b = 2 * c := by simp only [b, c]; ring
  have hb' : b = c * 2 := by simp only [b, c]; ring
  -- the target modulus
  rw [gaussQ_eq_sum_zmod, gaussQ_eq_sum_zmod, sum_zmod_digits hN]
  have hbN : ((b ^ 2 : ℕ) : ZMod N) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact ⟨2 ^ k, by simp only [N, b]; ring⟩
  have hterm : ∀ (u : ZMod b) (v : ZMod 4),
      ZMod.stdAddChar (N := N) ((a : ZMod N) * ((u.val + b * v.val : ℕ) : ZMod N) ^ 2) =
        ZMod.stdAddChar (N := N) ((a * (u.val : ℤ) ^ 2 : ℤ) : ZMod N) *
          ZMod.stdAddChar (N := 2) (((a * u.val) * (v.val : ℤ) : ℤ) : ZMod 2) := by
    intro u v
    have key : (a : ZMod N) * ((u.val + b * v.val : ℕ) : ZMod N) ^ 2 =
        ((a * (u.val : ℤ) ^ 2 : ℤ) : ZMod N) +
          (((a * u.val) * (v.val : ℤ)) * ((2 * b : ℕ) : ℤ) : ℤ) := by
      push_cast at hbN ⊢
      linear_combination (a : ZMod N) * (v.val : ZMod N) ^ 2 * hbN
    rw [key, AddChar.map_add_eq_mul,
      stdAddChar_intCast_mul (N := N) (d := 2) (e := 2 * b) (by simp only [N, b]; push_cast; ring)]
  simp_rw [hterm, ← Finset.mul_sum]
  have hinner : ∀ u : ZMod b, ∑ v : ZMod 4,
      ZMod.stdAddChar (N := 2) (((a * u.val) * (v.val : ℤ) : ℤ) : ZMod 2) =
        if 2 ∣ u.val then 4 else 0 := by
    intro u
    have hpar : Even (a * (u.val : ℤ)) ↔ 2 ∣ u.val := by
      rw [Int.even_mul]
      constructor
      · rintro (he | he)
        · exact absurd he (Int.not_even_iff_odd.mpr ha)
        · exact even_iff_two_dvd.mp (Int.even_coe_nat _ |>.mp he)
      · intro h; exact Or.inr ((Int.even_coe_nat _).mpr (even_iff_two_dvd.mpr h))
    show ∑ v : Fin 4, ZMod.stdAddChar (N := 2) (((a * u.val) * ((v : ℕ) : ℤ) : ℤ) : ZMod 2) = _
    rw [Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, stdAddChar_two_intCast_parity]
    have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [v3]
    have e0 : Even (a * (u.val : ℤ) * ((0 : ℕ) : ℤ)) := by simp
    have e2 : Even (a * (u.val : ℤ) * ((2 : ℕ) : ℤ)) := ⟨a * u.val, by push_cast; ring⟩
    have e1 : Even (a * (u.val : ℤ) * ((1 : ℕ) : ℤ)) ↔ 2 ∣ u.val := by
      rw [← hpar]; simp
    have e3 : Even (a * (u.val : ℤ) * ((3 : ℕ) : ℤ)) ↔ 2 ∣ u.val := by
      rw [← hpar]
      push_cast
      rw [Int.even_mul]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (by decide)
      · exact Or.inl
    simp only [if_pos e0, if_pos e2, e1, e3]
    split_ifs <;> norm_num
  simp_rw [hinner]
  -- restrict to even `u`
  rw [sum_zmod_digits (N := b) (b := 2) (c := c) hb, Finset.sum_eq_single (0 : ZMod 2)]
  · have hG : ∑ y : ZMod b, ZMod.stdAddChar (N := b) ((a : ZMod b) * y ^ 2) =
        2 * ∑ w : ZMod c, ZMod.stdAddChar (N := b) ((a * (w.val : ℤ) ^ 2 : ℤ) : ZMod b) := by
      rw [sum_zmod_digits (N := b) (b := c) (c := 2) hb', Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have hcc : ((c ^ 2 : ℕ) : ZMod b) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact ⟨2 ^ k, by simp only [b, c]; ring⟩
      have hcb : ((c * 2 : ℕ) : ZMod b) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, hb']
      have hs : ∀ s : ZMod 2, ZMod.stdAddChar (N := b) ((a : ZMod b) * ((w.val + c * s.val : ℕ) :
          ZMod b) ^ 2) = ZMod.stdAddChar (N := b) ((a * (w.val : ℤ) ^ 2 : ℤ) : ZMod b) := by
        intro s
        congr 1
        push_cast at hcc hcb ⊢
        linear_combination (a : ZMod b) * (w.val * s.val) * hcb +
          (a : ZMod b) * (s.val : ZMod b) ^ 2 * hcc
      simp_rw [hs, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      push_cast; ring
    rw [hG, ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hlt : (0 : ZMod 2).val + 2 * w.val < b := by
      have := ZMod.val_lt w
      simp only [ZMod.val_zero, zero_add, hb]
      omega
    rw [ZMod.val_natCast_of_lt hlt, if_pos ⟨w.val, by simp⟩]
    simp only [ZMod.val_zero, zero_add]
    have e := stdAddChar_intCast_mul (N := N) (d := b) (e := 4) (t := a * (w.val : ℤ) ^ 2)
      (by simp only [N, b]; push_cast; ring)
    rw [show ((a * ((2 * w.val : ℕ) : ℤ) ^ 2 : ℤ) : ZMod N) =
        ((a * (w.val : ℤ) ^ 2 * ((4 : ℕ) : ℤ) : ℤ) : ZMod N) by push_cast; ring, e]
    ring
  · intro r _ hr
    refine Finset.sum_eq_zero fun w _ => ?_
    have hlt : r.val + 2 * w.val < b := by
      have h1 := ZMod.val_lt r
      have h2 := ZMod.val_lt w
      rw [hb]; omega
    rw [ZMod.val_natCast_of_lt hlt, if_neg]
    · simp
    · intro hd
      apply hr
      have h1 := ZMod.val_lt r
      have : r.val = 0 := by omega
      exact (ZMod.val_eq_zero r).mp this
  · simp

/-! ## Square and fourth-power laws -/

/-- `G(a; 2^{k+2})² = 2^{k+3} e^{2πi a/4}` for odd `a`. -/
theorem gaussQ_two_pow_sq {a : ℤ} (ha : Odd a) (k : ℕ) :
    gaussQ a (2 ^ (k + 2)) ^ 2 = 2 ^ (k + 3) * cexp (2 * Real.pi * I * (a / 4)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hω : cexp (2 * Real.pi * I * (a / 2)) = -1 := cexp_pi_I_mul_odd ha
    match k, ih with
    | 0, _ =>
      rw [show (0 + 2 : ℕ) = 2 from rfl, show (2 : ℕ) ^ 2 = 4 from rfl, gaussQ_four]
      set ω := cexp (2 * Real.pi * I * (a / 4))
      have hω2 : ω ^ 2 = -1 := by
        rw [← hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
      linear_combination 4 * hω2
    | 1, _ =>
      rw [show (1 + 2 : ℕ) = 3 from rfl, show (2 : ℕ) ^ 3 = 8 from rfl, gaussQ_eight ha]
      have hω2 : cexp (2 * Real.pi * I * (a / 8)) ^ 2 = cexp (2 * Real.pi * I * (a / 4)) := by
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      rw [mul_pow, hω2]; norm_num
    | j + 2, ih =>
      rw [show j + 2 + 2 = j + 4 by ring, gaussQ_two_pow_add_four ha, mul_pow, ih j (by omega)]
      ring

theorem gaussQ_two_pow_pow_four {a : ℤ} (ha : Odd a) (k : ℕ) :
    gaussQ a (2 ^ (k + 2)) ^ 4 = -4 * ((2 ^ (k + 2) : ℕ) : ℂ) ^ 2 := by
  have hω : cexp (2 * Real.pi * I * (a / 4)) ^ 2 = -1 := by
    rw [← cexp_pi_I_mul_odd ha, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gaussQ_two_pow_sq ha, mul_pow, hω]
  push_cast; ring

/-- **Odd moduli**: `G(a; q)² = χ₄(q) q` for `(a, q) = 1`. -/
theorem gaussQ_sq_of_odd : ∀ q : ℕ, q % 2 = 1 → ∀ a : ℤ, IsCoprime a q →
    gaussQ a q ^ 2 = oddSquareSign q * q := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hodd a ha
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
      simp [pow_succ] at hodd
    have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hpa : ¬ (p : ℤ) ∣ a := by
      intro hd
      have : IsCoprime a (p : ℤ) := by
        have := ha
        push_cast at this
        exact this.of_isCoprime_of_dvd_right (dvd_pow_self _ hn.ne')
      exact (Nat.prime_iff_prime_int.mp hp).not_unit (this.isUnit_of_dvd' hd dvd_rfl)
    clear hn hodd ha
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [gaussQ_one, oddSquareSign]
      | 1, _ => simpa using gaussQ_prime_sq hp hp2 hpa
      | m + 2, ih =>
        have hpm : p ^ m % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr hpo))
        rw [gaussQ_prime_pow_add_two hp hp2 hpa, mul_pow, ih m (by omega),
          show p ^ (m + 2) = p ^ m * (p * p) by ring,
          oddSquareSign_mul hpm (by rw [Nat.mul_mod, hpo]), oddSquareSign_mul hpo hpo]
        have := oddSquareSign_sq p
        push_cast
        linear_combination -(oddSquareSign (p ^ m) * (p : ℂ) ^ m * (p : ℂ) ^ 2) * this
  | zero => intro h; simp at h
  | one => intro _ a _; simp [gaussQ_one, oddSquareSign]
  | coprime a b ha hb hab iha ihb =>
    intro hodd x hx
    obtain ⟨hao', hbo'⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)
    have hao : a % 2 = 1 := Nat.odd_iff.mp hao'
    have hbo : b % 2 = 1 := Nat.odd_iff.mp hbo'
    have hxa : IsCoprime x a := by
      have := hx; push_cast at this; exact this.of_isCoprime_of_dvd_right (dvd_mul_right _ _)
    have hxb : IsCoprime x b := by
      have := hx; push_cast at this; exact this.of_isCoprime_of_dvd_right (dvd_mul_left _ _)
    have hab' : IsCoprime (a : ℤ) b := Nat.isCoprime_iff_coprime.mpr hab
    rw [gaussQ_mul_of_coprime (by omega) (by omega) hab, mul_pow,
      iha hao (x * b) (hxa.mul_left hab'.symm), ihb hbo (x * a) (hxb.mul_left hab'),
      oddSquareSign_mul hao hbo]
    push_cast; ring

/-- Odd moduli: `G(a; q)^4 = q²` for `(a, q) = 1`. -/
theorem gaussQ_pow_four_of_odd (q : ℕ) (hq : q % 2 = 1) (a : ℤ) (ha : IsCoprime a q) :
    gaussQ a q ^ 4 = (q : ℂ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gaussQ_sq_of_odd q hq a ha, mul_pow,
    oddSquareSign_sq, one_mul]

/-- Moduli `q ≡ 2 (mod 4)`: `G(a; q) = 0` for `(a, q) = 1`. -/
theorem gaussQ_eq_zero_of_mod_four_eq_two {q : ℕ} (hq : q % 4 = 2) {a : ℤ}
    (ha : IsCoprime a q) : gaussQ a q = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := ⟨q / 2, by omega⟩
  have hm : m % 2 = 1 := by omega
  have hcop : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr (Nat.odd_iff.mpr hm)
  rw [gaussQ_mul_of_coprime (by norm_num) (by omega) hcop, gaussQ_two, zero_mul]
  have hao : Odd a := by
    rcases Int.even_or_odd a with he | ho
    · exfalso
      have h2 : (2 : ℤ) ∣ a := even_iff_two_dvd.mp he
      have : IsCoprime a (2 : ℤ) := by
        have := ha; push_cast at this; exact this.of_isCoprime_of_dvd_right (dvd_mul_right _ _)
      have hu := this.isUnit_of_dvd' h2 dvd_rfl
      rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
    · exact ho
  exact Int.odd_mul.mpr ⟨hao, by exact_mod_cast Nat.odd_iff.mpr hm⟩

/-- The quarter phase `e^{2πi n/4}` depends only on `n mod 4`. -/
theorem cexp_quarter_int (n : ℤ) :
    cexp (2 * Real.pi * I * ((n : ℂ) / 4)) = cexp (2 * Real.pi * I * (((n % 4 : ℤ) : ℂ) / 4)) := by
  have h := Int.emod_add_mul_ediv n 4
  conv_lhs => rw [← h]
  push_cast
  rw [show (((n % 4 : ℤ) : ℂ) + 4 * ((n / 4 : ℤ) : ℂ)) / 4 = ((n % 4 : ℤ) : ℂ) / 4 + ((n / 4 : ℤ) : ℂ) by
    ring, cexp_two_pi_I_add_int]

theorem cexp_quarter_one : cexp (2 * Real.pi * I * ((1 : ℂ) / 4)) = I := by
  rw [show 2 * (Real.pi : ℂ) * I * (1 / 4) = Real.pi / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

theorem cexp_quarter_three : cexp (2 * Real.pi * I * ((3 : ℂ) / 4)) = -I := by
  rw [show 2 * (Real.pi : ℂ) * I * (3 / 4) = ((3 : ℕ) : ℂ) * (Real.pi / 2 * I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Complex.I_sq]; ring

/-- `e^{2πi am/4} χ₄(m) = i χ₄(a)` for odd `a` and odd `m`. -/
theorem cexp_quarter_mul_oddSquareSign {a : ℤ} (ha : Odd a) {m : ℕ} (hm : m % 2 = 1) :
    cexp (2 * Real.pi * I * (((a * m : ℤ) : ℂ) / 4)) * oddSquareSign m =
      I * (if a % 4 = 1 then 1 else -1) := by
  rw [cexp_quarter_int]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by
    obtain ⟨k, rfl⟩ := ha; omega
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  have hmz : ((m : ℤ) % 4) = ((m % 4 : ℕ) : ℤ) := by push_cast; rfl
  unfold oddSquareSign
  rcases ha4 with h1 | h1 <;> rcases hm4 with h2 | h2
  · have : (a * m) % 4 = 1 := by rw [Int.mul_emod, h1, hmz, h2]; norm_num
    rw [this, if_pos h2, if_pos h1]; push_cast; rw [cexp_quarter_one]
  · have : (a * m) % 4 = 3 := by rw [Int.mul_emod, h1, hmz, h2]; norm_num
    rw [this, if_neg (by omega), if_pos h1]; push_cast; rw [cexp_quarter_three]; ring
  · have : (a * m) % 4 = 3 := by rw [Int.mul_emod, h1, hmz, h2]; norm_num
    rw [this, if_pos h2, if_neg (by omega)]; push_cast; rw [cexp_quarter_three]; ring
  · have : (a * m) % 4 = 1 := by rw [Int.mul_emod, h1, hmz, h2]; norm_num
    rw [this, if_neg (by omega), if_neg (by omega)]; push_cast; rw [cexp_quarter_one]

/-- **Moduli divisible by `4`**: `G(a; q)² = 2 q i χ₄(a)` for `(a, q) = 1`. -/
theorem gaussQ_sq_of_four_dvd {q : ℕ} (hq0 : 0 < q) (hq : 4 ∣ q) {a : ℤ}
    (ha : IsCoprime a q) : gaussQ a q ^ 2 = 2 * q * I * (if a % 4 = 1 then 1 else -1) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hq0.ne'
  have hm0 : 0 < m := hm.pos
  have hk : 2 ≤ k := by
    by_contra hk
    interval_cases k
    · simp only [pow_zero, one_mul] at hq
      obtain ⟨j, rfl⟩ := hm; omega
    · obtain ⟨j, rfl⟩ := hm; omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hcop : Nat.Coprime (2 ^ (j + 2)) m :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hm)
  have hao : Odd a := by
    rcases Int.even_or_odd a with he | ho
    · exfalso
      have h2 : (2 : ℤ) ∣ a := even_iff_two_dvd.mp he
      have : IsCoprime a (2 : ℤ) := by
        have := ha; push_cast at this
        exact this.of_isCoprime_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
      have hu := this.isUnit_of_dvd' h2 dvd_rfl
      rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
    · exact ho
  have ham : IsCoprime a (m : ℤ) := by
    have := ha; push_cast at this; exact this.of_isCoprime_of_dvd_right (dvd_mul_left _ _)
  have h2m : IsCoprime ((2 ^ (j + 2) : ℕ) : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp hm
  rw [gaussQ_mul_of_coprime (by positivity) hm0 hcop, mul_pow,
    gaussQ_two_pow_sq (Int.odd_mul.mpr ⟨hao, by exact_mod_cast hm⟩) j,
    gaussQ_sq_of_odd m hmodd _ (ham.mul_left h2m)]
  have key := cexp_quarter_mul_oddSquareSign hao hmodd
  push_cast at key ⊢
  linear_combination (2 ^ (j + 3) * (m : ℂ)) * key

/-- Moduli divisible by `4`: `G(a; q)^4 = -4 q²` for `(a, q) = 1`. -/
theorem gaussQ_pow_four_of_four_dvd {q : ℕ} (hq0 : 0 < q) (hq : 4 ∣ q) {a : ℤ}
    (ha : IsCoprime a q) : gaussQ a q ^ 4 = -4 * (q : ℂ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gaussQ_sq_of_four_dvd hq0 hq ha, mul_pow,
    mul_pow, Complex.I_sq]
  split_ifs <;> ring

/-- **Fourth-power law of quadratic Gauss sums.** For `(a, q) = 1`, `q > 0`,
`G(a; q)^4` equals `q²`, `0` or `-4 q²` according as `q` is odd, `q ≡ 2 (mod 4)` or `4 ∣ q`. -/
theorem gaussQ_pow_four {q : ℕ} (hq0 : 0 < q) {a : ℤ} (ha : IsCoprime a q) :
    gaussQ a q ^ 4 =
      if q % 2 = 1 then (q : ℂ) ^ 2 else if q % 4 = 2 then 0 else -4 * (q : ℂ) ^ 2 := by
  split_ifs with h1 h2
  · exact gaussQ_pow_four_of_odd q h1 a ha
  · rw [gaussQ_eq_zero_of_mod_four_eq_two h2 ha]; norm_num
  · exact gaussQ_pow_four_of_four_dvd hq0 (by omega) ha

/-- **Quadratic Gauss-sum square law.** For `q > 0` and `(a, q) = 1`,
`G(a; q)² = χ₄(q) q` (`q` odd), `0` (`q ≡ 2 mod 4`), `2 q i χ₄(a)` (`4 ∣ q`). -/
theorem gaussQ_sq {q : ℕ} (hq0 : 0 < q) {a : ℤ} (ha : IsCoprime a q) :
    gaussQ a q ^ 2 =
      if q % 2 = 1 then oddSquareSign q * q
      else if q % 4 = 2 then 0 else 2 * q * I * (if a % 4 = 1 then 1 else -1) := by
  split_ifs with h1 h2
  · exact gaussQ_sq_of_odd q h1 a ha
  · rw [gaussQ_eq_zero_of_mod_four_eq_two h2 ha]; norm_num
  · rw [gaussQ_sq_of_four_dvd hq0 (by omega) ha, if_pos ‹_›]
  · rw [gaussQ_sq_of_four_dvd hq0 (by omega) ha, if_neg ‹_›]

/-- For odd `q` and `(a, q) = 1`, `|G(a; q)| = √q`. -/
theorem norm_gaussQ_of_odd {q : ℕ} (hq : q % 2 = 1) {a : ℤ} (ha : IsCoprime a q) :
    ‖gaussQ a q‖ = Real.sqrt q := by
  have h := congrArg (‖·‖) (gaussQ_pow_four_of_odd q hq a ha)
  simp only [norm_pow, Complex.norm_natCast] at h
  have h4 : ‖gaussQ a q‖ ^ 2 = q := by
    have hsq : (‖gaussQ a q‖ ^ 2) ^ 2 = ((q : ℝ)) ^ 2 := by rw [← pow_mul]; exact h
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  rw [← h4, Real.sqrt_sq (norm_nonneg _)]

end GaloisForLFunctions.RHTower.HalfWeight
