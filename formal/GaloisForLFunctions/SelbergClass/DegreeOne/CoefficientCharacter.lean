import GaloisForLFunctions.RHTower.SelbergClass.FullEulerLogPrime
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Multiplicativity of Selberg coefficients and periodic multiplicative functions

* The coefficients of a full Selberg function are multiplicative (`coeff_mul_of_coprime`).  The
  logarithmic derivative of the Euler product gives `a(N) log N = Σ_{d ∣ N} a(N/d) c(d)`, with `c`
  supported on prime powers; each prime power divides exactly one of two coprime factors, and the
  claim follows by strong induction.
* A periodic multiplicative function agrees on the reduced residues with a Dirichlet character
  (`exists_dirichletCharacter_of_periodic`).
-/

noncomputable section

set_option autoImplicit false

open Complex RHTower

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-- The Euler convolution sum, written over divisors. -/
theorem logMul_coeff_eq_sum_divisors (F : RHTower.SelbergClass) (N : ℕ) :
    LSeries.logMul F.coeff N =
      ∑ d ∈ N.divisors, F.coeff (N / d) * LSeries.logMul F.eulerLogCoeff d := by
  rw [F.logMul_coeff_apply N]
  exact Nat.sum_divisorsAntidiagonal' fun i j => F.coeff i * LSeries.logMul F.eulerLogCoeff j

/-- A prime power dividing a coprime product divides one of its factors. -/
theorem prime_pow_dvd_or {m n p k : ℕ} (hp : p.Prime) (hmn : m.Coprime n)
    (hdvd : p ^ k ∣ m * n) : p ^ k ∣ m ∨ p ^ k ∣ n := by
  by_cases hpm : p ∣ m
  · left
    have hpn : ¬ p ∣ n := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hmn hpm h)
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)).dvd_of_dvd_mul_right hdvd
  · right
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)).dvd_of_dvd_mul_left hdvd

/-- The Euler sum over the divisors of a coprime product splits over the two factors. -/
theorem sum_divisors_mul_split (F : RHTower.SelbergClass) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (g : ℕ → ℂ) :
    ∑ d ∈ (m * n).divisors, g d * LSeries.logMul F.eulerLogCoeff d =
      ∑ d ∈ m.divisors.erase 1, g d * LSeries.logMul F.eulerLogCoeff d +
        ∑ d ∈ n.divisors.erase 1, g d * LSeries.logMul F.eulerLogCoeff d := by
  classical
  have hdisj : Disjoint (m.divisors.erase 1) (n.divisors.erase 1) := by
    refine Finset.disjoint_left.mpr fun d hd hd' => ?_
    have h1 := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
    have h2 := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd')
    exact (Finset.ne_of_mem_erase hd) (Nat.eq_one_of_dvd_coprimes hmn h1.1 h2.1)
  rw [← Finset.sum_union hdisj]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · have h := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      exact Nat.mem_divisors.mpr ⟨h.1.mul_right n, mul_ne_zero hm hn⟩
    · have h := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      exact Nat.mem_divisors.mpr ⟨h.1.mul_left m, mul_ne_zero hm hn⟩
  · intro d hd hnot
    have hdvd := (Nat.mem_divisors.mp hd).1
    by_cases hb : F.eulerLogCoeff d = 0
    · simp [LSeries.logMul, hb]
    obtain ⟨p, k, hp, hk, rfl⟩ := F.eulerLogCoeff_primePower hb
    exfalso
    apply hnot
    have hne1 : p ^ k ≠ 1 := (Nat.one_lt_pow hk.ne' hp.one_lt).ne'
    rcases prime_pow_dvd_or hp hmn hdvd with h | h
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne1, Nat.mem_divisors.mpr ⟨h, hm⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne1, Nat.mem_divisors.mpr ⟨h, hn⟩⟩)

/-- The divisor sum over `d ≠ 1` is the full sum, since `log 1 = 0`. -/
theorem sum_erase_one_eq (F : RHTower.SelbergClass) (N : ℕ) (g : ℕ → ℂ) :
    ∑ d ∈ N.divisors.erase 1, g d * LSeries.logMul F.eulerLogCoeff d =
      ∑ d ∈ N.divisors, g d * LSeries.logMul F.eulerLogCoeff d :=
  Finset.sum_erase _ (by simp [LSeries.logMul])

theorem log_natCast_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Complex.log ((m * n : ℕ) : ℂ) = Complex.log (m : ℂ) + Complex.log (n : ℂ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← Complex.natCast_log, ← Complex.natCast_log, ← Complex.natCast_log]
  push_cast
  rw [Real.log_mul hmR hnR]
  push_cast
  rfl

/-- **The coefficients of a full Selberg function are multiplicative.** -/
theorem coeff_mul_of_coprime (F : RHTower.SelbergClass) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) : F.coeff (m * n) = F.coeff m * F.coeff n := by
  have key : ∀ N m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → m * n = N →
      F.coeff (m * n) = F.coeff m * F.coeff n := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro m n hm hn hmn hN
      subst hN
      rcases eq_or_ne (m * n) 1 with h1 | h1
      · have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right h1
        have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_left h1
        subst hm1 hn1
        simp [F.coeff_one]
      have hmain := logMul_coeff_eq_sum_divisors F (m * n)
      rw [sum_divisors_mul_split F hm hn hmn (fun d => F.coeff (m * n / d))] at hmain
      have hA : ∑ d ∈ m.divisors.erase 1, F.coeff (m * n / d) * LSeries.logMul F.eulerLogCoeff d =
          F.coeff n * LSeries.logMul F.coeff m := by
        rw [logMul_coeff_eq_sum_divisors F m, ← sum_erase_one_eq F m, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdm := (Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)).1
        have hd1 := Finset.ne_of_mem_erase hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm)
        have hq0 : m / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) hdpos).ne'
        have hdiv : m * n / d = m / d * n := (Nat.div_mul_right_comm hdm n).symm
        have hlt : m / d * n < m * n := by
          refine Nat.mul_lt_mul_of_pos_right ?_ (Nat.pos_of_ne_zero hn)
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega)
        have hcop : (m / d).Coprime n := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdm) hmn
        rw [hdiv, ih _ hlt _ _ hq0 hn hcop rfl]
        ring
      have hB : ∑ d ∈ n.divisors.erase 1, F.coeff (m * n / d) * LSeries.logMul F.eulerLogCoeff d =
          F.coeff m * LSeries.logMul F.coeff n := by
        rw [logMul_coeff_eq_sum_divisors F n, ← sum_erase_one_eq F n, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdn := (Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)).1
        have hd1 := Finset.ne_of_mem_erase hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
        have hq0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos).ne'
        have hdiv : m * n / d = m * (n / d) := Nat.mul_div_assoc m hdn
        have hlt : m * (n / d) < m * n := by
          refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.pos_of_ne_zero hm)
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        have hcop : m.Coprime (n / d) := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdn) hmn
        rw [hdiv, ih _ hlt _ _ hm hq0 hcop rfl]
        ring
      rw [hA, hB] at hmain
      simp only [LSeries.logMul] at hmain
      have hlog : Complex.log ((m * n : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        refine Complex.ofReal_ne_zero.mpr (Real.log_pos ?_).ne'
        have : 1 < m * n := by
          have : 0 < m * n := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
          omega
        exact_mod_cast this
      refine mul_left_cancel₀ hlog ?_
      rw [hmain, log_natCast_mul hm hn]
      ring
  exact key _ m n hm hn hmn rfl

/-! ### Periodic multiplicative functions -/

/-- **A periodic multiplicative function is a Dirichlet character on the reduced residues.** -/
theorem exists_dirichletCharacter_of_periodic {q : ℕ} [NeZero q] {b : ℕ → ℂ}
    (hper : ∀ n : ℕ, n ≠ 0 → b (n + q) = b n) (hone : b 1 = 1)
    (hmul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → b (m * n) = b m * b n) :
    ∃ χ : DirichletCharacter ℂ q, ∀ n : ℕ, n ≠ 0 → n.Coprime q → b n = χ n := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hkper : ∀ k n : ℕ, n ≠ 0 → b (n + k * q) = b n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro n hn
      have e : n + (k + 1) * q = n + k * q + q := by ring
      rw [e, hper _ (by omega), ih n hn]
  have hle : ∀ m n : ℕ, m ≠ 0 → m ≤ n → (m : ZMod q) = (n : ZMod q) → b m = b n := by
    intro m n hm hmn h
    rw [ZMod.natCast_eq_natCast_iff] at h
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hmn).mp h
    have e : n = m + k * q := by
      rw [mul_comm, ← hk]
      omega
    rw [e, hkper k m hm]
  have hcong : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → (m : ZMod q) = (n : ZMod q) → b m = b n := by
    intro m n hm hn h
    rcases le_total m n with h' | h'
    · exact hle m n hm h' h
    · exact (hle n m hn h' h.symm).symm
  let B : ZMod q → ℂ := fun u => b (u.val + q)
  have hcast : ∀ u : ZMod q, ((u.val + q : ℕ) : ZMod q) = u := by
    intro u
    push_cast
    simp
  have hB : ∀ n : ℕ, n ≠ 0 → B (n : ZMod q) = b n := fun n hn =>
    hcong _ _ (by omega) hn (hcast _)
  let φ : (ZMod q)ˣ →* ℂ :=
    { toFun := fun u => B (u : ZMod q)
      map_one' := by
        have h := hB 1 one_ne_zero
        rw [Nat.cast_one] at h
        rw [Units.val_one, h, hone]
      map_mul' := by
        intro u v
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (u : ZMod q).val + q := ⟨_, rfl⟩
        obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (v : ZMod q).val + q := ⟨_, rfl⟩
        have hm0 : m ≠ 0 := by omega
        have hum : (m : ZMod q) = u := by
          rw [hm]
          exact hcast _
        have hvr : (r : ZMod q) = v := by
          rw [hr]
          exact hcast _
        have hcop : m.Coprime q := (ZMod.isUnit_iff_coprime m q).mp (by rw [hum]; exact u.isUnit)
        obtain ⟨n₀, h1, h2⟩ := Nat.chineseRemainder hcop.symm r 1
        obtain ⟨n, hn⟩ : ∃ n : ℕ, n = n₀ + q * m := ⟨_, rfl⟩
        have hn0 : n ≠ 0 := by
          have : 0 < q * m := Nat.mul_pos hq (Nat.pos_of_ne_zero hm0)
          omega
        have hvn : (n : ZMod q) = v := by
          rw [← hvr, hn, ZMod.natCast_eq_natCast_iff]
          refine Nat.ModEq.trans ?_ h1
          simp [Nat.ModEq]
        have hn1 : n ≡ 1 [MOD m] := by
          rw [hn]
          refine Nat.ModEq.trans ?_ h2
          simp [Nat.ModEq]
        have hmcop : m.Coprime n := by
          have := hn1.gcd_eq
          rw [Nat.gcd_one_left] at this
          exact (Nat.coprime_comm.mp this)
        have hmulv := hmul m n hm0 hn0 hmcop
        have huv : ((m * n : ℕ) : ZMod q) = ((u * v : (ZMod q)ˣ) : ZMod q) := by
          rw [Nat.cast_mul, hum, hvn, Units.val_mul]
        rw [← huv, hB _ (mul_ne_zero hm0 hn0), hmulv, ← hB m hm0, ← hB n hn0, hum, hvn] }
  refine ⟨MulChar.ofUnitHom φ.toHomUnits, fun n hn hcop => ?_⟩
  have hu : ((ZMod.unitOfCoprime n hcop : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) :=
    ZMod.coe_unitOfCoprime n hcop
  rw [← hu, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  change b n = B _
  rw [hu, hB n hn]

end GaloisForLFunctions.SelbergClass.DegreeOne
