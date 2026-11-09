import Mathlib

/-!
# Simultaneous inseparability costs the primorial

Stepanov's method rests on the Frobenius having zero derivative. On `ℤ[X]` the substitute is
`ψ_n F = F(X^n)` (`Polynomial.expand ℤ n`), whose derivative is divisible by `n`.

* No endomorphism of `ℤ[X]` has zero derivative except evaluation at an integer
  (`exists_eq_C_eval_of_derivative_eq_zero`).
* Stepanov's identity holds modulo `n` at every order: derivatives of `A · ψ_n B` fall on `A`
  (`C_dvd_iterate_derivative_mul_expand_sub`).
* A monic polynomial whose derivative vanishes modulo every prime of `S` has degree divisible by
  `∏_{p ∈ S} p`, so `∑_{p ∈ S} log p ≤ log deg` (`prod_dvd_natDegree_of_map_derivative_eq_zero`,
  `sum_log_le_log_natDegree`).
* A monic polynomial that is a `p^{k_p}`-th power modulo each `p ∈ S` has degree divisible by
  `∏ p^{k_p}` (`prod_pow_dvd_natDegree`); `ψ_n` attains this (`map_expand_pow_mul`), and every
  root modulo `p` then has multiplicity `≥ p^k` (`pow_le_rootMultiplicity_map_expand`).
* Multiplicity `m` at every prime of `S` costs log-degree `≤ ∑ log p + |S| log m`
  (`log_prod_pow_clog_le`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- Reduction of integer polynomials modulo `p`. -/
local notation "red" p => Polynomial.map (Int.castRingHom (ZMod p))

/-! ### No archimedean zero derivative -/

/-- A ring endomorphism of `ℤ[X]` sending `X` to a polynomial of zero derivative is evaluation at
an integer: its image is the constants. -/
theorem exists_eq_C_eval_of_derivative_eq_zero (φ : ℤ[X] →+* ℤ[X])
    (h : derivative (φ X) = 0) : ∃ a : ℤ, ∀ F : ℤ[X], φ F = C (F.eval a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, φ X = C a := ⟨_, eq_C_of_derivative_eq_zero h⟩
  have hφ : φ = C.comp (evalRingHom a) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simpa using ha
  exact ⟨a, fun F => by rw [hφ]; rfl⟩

/-! ### Stepanov's identity modulo `n` -/

/-- Every derivative of `A · ψ_n B` agrees modulo `n` with the derivative taken on `A` alone. -/
theorem C_dvd_iterate_derivative_mul_expand_sub (n : ℕ) (B : ℤ[X]) (k : ℕ) (A : ℤ[X]) :
    C (n : ℤ) ∣ derivative^[k] (A * expand ℤ n B) - derivative^[k] A * expand ℤ n B := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    have hstep : derivative (A * expand ℤ n B) =
        derivative A * expand ℤ n B +
          C (n : ℤ) * (A * (expand ℤ n (derivative B) * X ^ (n - 1))) := by
      rw [derivative_mul, derivative_expand, map_natCast]
      ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep,
      iterate_map_add, iterate_derivative_C_mul, add_sub_right_comm]
    exact dvd_add (ih (derivative A)) (dvd_mul_right _ _)

/-! ### The Chebyshev floor -/

/-- If the derivative of a monic integer polynomial vanishes modulo `p`, then `p` divides its
degree: the leading coefficient of the derivative is the degree. -/
theorem dvd_natDegree_of_map_derivative_eq_zero {p : ℕ} {F : ℤ[X]} (hF : F.Monic)
    (h : (red p) (derivative F) = 0) : p ∣ F.natDegree := by
  rcases Nat.eq_zero_or_pos F.natDegree with h0 | hpos
  · rw [h0]; exact dvd_zero p
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hc := congrArg (fun G : (ZMod p)[X] => G.coeff d) h
  simp only [coeff_map, coeff_derivative, coeff_zero] at hc
  have hlead : F.coeff (d + 1) = 1 := by
    have := hF.coeff_natDegree
    rwa [hd] at this
  rw [hlead, one_mul] at hc
  have hc' : ((d + 1 : ℕ) : ZMod p) = 0 := by simpa using hc
  rw [hd]
  exact (ZMod.natCast_eq_zero_iff _ _).mp hc'

/-- A monic polynomial inseparable modulo every prime of `S` has degree divisible by the
primorial of `S`. -/
theorem prod_dvd_natDegree_of_map_derivative_eq_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {F : ℤ[X]} (hF : F.Monic) (h : ∀ p ∈ S, (red p) (derivative F) = 0) :
    ∏ p ∈ S, p ∣ F.natDegree :=
  Finset.prod_primes_dvd _ (fun p hp => (hS p hp).prime)
    fun p hp => dvd_natDegree_of_map_derivative_eq_zero hF (h p hp)

/-- The Chebyshev count of `S` is at most the logarithm of the degree. -/
theorem sum_log_le_log_natDegree {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {F : ℤ[X]} (hF : F.Monic) (hdeg : 1 ≤ F.natDegree)
    (h : ∀ p ∈ S, (red p) (derivative F) = 0) :
    ∑ p ∈ S, Real.log p ≤ Real.log F.natDegree := by
  have hle : ∏ p ∈ S, p ≤ F.natDegree :=
    Nat.le_of_dvd hdeg (prod_dvd_natDegree_of_map_derivative_eq_zero hS hF h)
  have hpos : ∀ p ∈ S, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (hS p hp).ne_zero
  rw [← Real.log_prod hpos]
  rw [← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast hle)
  exact_mod_cast Finset.prod_pos fun p hp => (hS p hp).pos

/-! ### The exact cost of inseparability -/

/-- If a monic integer polynomial is an `N`-th power modulo a prime, `N` divides its degree. -/
theorem dvd_natDegree_of_map_eq_pow {p : ℕ} [Fact p.Prime] {F : ℤ[X]} (hF : F.Monic) {N : ℕ}
    {G : (ZMod p)[X]} (h : (red p) F = G ^ N) : N ∣ F.natDegree := by
  have hd := congrArg natDegree h
  rw [hF.natDegree_map, natDegree_pow] at hd
  exact ⟨_, hd⟩

/-- Prime powers at distinct primes that each divide `N` divide it jointly. -/
theorem prod_pow_dvd_of_forall_pow_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ)
    {N : ℕ} (h : ∀ p ∈ S, p ^ k p ∣ N) : ∏ p ∈ S, p ^ k p ∣ N := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q T hq ih =>
    have hqp : q.Prime := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    rw [prod_insert hq]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h q (mem_insert_self q T))
      (ih hT fun p hp => h p (mem_insert_of_mem hp))
    refine Nat.Coprime.prod_right fun p hp => ?_
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hqp (hT p hp)).mpr fun e => hq (e ▸ hp))

/-- A monic polynomial that is a `p ^ k p`-th power modulo each prime `p ∈ S` has degree divisible
by `∏ p ^ k p`. -/
theorem prod_pow_dvd_natDegree {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ)
    {F : ℤ[X]} (hF : F.Monic)
    (h : ∀ p ∈ S, ∃ G : (ZMod p)[X], (red p) F = G ^ (p ^ k p)) :
    ∏ p ∈ S, p ^ k p ∣ F.natDegree :=
  prod_pow_dvd_of_forall_pow_dvd hS k fun p hp => by
    obtain ⟨G, hG⟩ := h p hp
    haveI : Fact p.Prime := ⟨hS p hp⟩
    exact dvd_natDegree_of_map_eq_pow hF hG

/-- Over `𝔽_p`, `ψ_{p^k}` is the `p^k`-th power. -/
theorem expand_prime_pow_zmod (p : ℕ) [Fact p.Prime] (k : ℕ) (g : (ZMod p)[X]) :
    expand (ZMod p) (p ^ k) g = g ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', expand_mul, ih, ZMod.expand_card, ← pow_mul, mul_comm]

/-- `ψ_{p^k m} F ≡ (ψ_m F)^{p^k}` modulo `p`: the bound of `prod_pow_dvd_natDegree` is attained. -/
theorem map_expand_pow_mul (p : ℕ) [Fact p.Prime] (k m : ℕ) (F : ℤ[X]) :
    (red p) (expand ℤ (p ^ k * m) F) = ((red p) (expand ℤ m F)) ^ (p ^ k) := by
  rw [expand_mul, map_expand, expand_prime_pow_zmod]

/-- Every root modulo `p` of `ψ_{p^k m} F`, `F` monic, has multiplicity at least `p^k`. -/
theorem pow_le_rootMultiplicity_map_expand (p : ℕ) [Fact p.Prime] (k : ℕ) {m : ℕ} (hm : 0 < m)
    {F : ℤ[X]} (hF : F.Monic) {a : ZMod p}
    (ha : ((red p) (expand ℤ (p ^ k * m) F)).IsRoot a) :
    p ^ k ≤ rootMultiplicity a ((red p) (expand ℤ (p ^ k * m) F)) := by
  have hmon : ((red p) (expand ℤ (p ^ k * m) F)).Monic :=
    (hF.expand (Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos k) hm)).map _
  rw [le_rootMultiplicity_iff hmon.ne_zero]
  rw [map_expand_pow_mul] at ha ⊢
  have hroot : ((red p) (expand ℤ m F)).IsRoot a := by
    rw [IsRoot.def, eval_pow] at ha
    exact (pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos k).ne').mp ha
  exact pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hroot) _

/-! ### The price of multiplicity `m` -/

/-- Multiplicity `m` at every prime of `S` is reached by `n = ∏ p ^ ⌈log_p m⌉`, whose logarithm is
at most the Chebyshev count of `S` plus `|S| log m`. -/
theorem log_prod_pow_clog_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : 1 ≤ m) :
    Real.log (∏ p ∈ S, p ^ Nat.clog p m : ℕ) ≤ ∑ p ∈ S, Real.log p + S.card * Real.log m := by
  have hterm : ∀ p ∈ S, Real.log ((p ^ Nat.clog p m : ℕ) : ℝ) ≤ Real.log p + Real.log m := by
    intro p hp
    have hp1 : 1 < p := (hS p hp).one_lt
    have hle : p ^ Nat.clog p m ≤ p * m := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · have hc : 0 < Nat.clog p m := Nat.clog_pos hp1 h1
        have hlt := Nat.pow_pred_clog_lt_self hp1 h1
        calc p ^ Nat.clog p m = p ^ ((Nat.clog p m).pred + 1) :=
              congrArg (p ^ ·) (Nat.succ_pred_eq_of_pos hc).symm
          _ = p * p ^ (Nat.clog p m).pred := pow_succ' _ _
          _ ≤ p * m := Nat.mul_le_mul_left p hlt.le
      · have hm1 : m = 1 := le_antisymm h1 hm
        subst hm1
        simpa [Nat.clog_one_right] using hp1.le
    have hpos : (0 : ℝ) < ((p ^ Nat.clog p m : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (hS p hp).pos _
    calc Real.log ((p ^ Nat.clog p m : ℕ) : ℝ) ≤ Real.log ((p * m : ℕ) : ℝ) :=
          Real.log_le_log hpos (by exact_mod_cast hle)
      _ = Real.log p + Real.log m := by
          rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (hS p hp).ne_zero)
            (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm))]
  have hne : ∀ p ∈ S, ((p ^ Nat.clog p m : ℕ) : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (pow_pos (hS p hp).pos _).ne'
  rw [Nat.cast_prod, Real.log_prod hne]
  calc ∑ p ∈ S, Real.log ((p ^ Nat.clog p m : ℕ) : ℝ) ≤ ∑ p ∈ S, (Real.log p + Real.log m) :=
        Finset.sum_le_sum hterm
    _ = ∑ p ∈ S, Real.log p + S.card * Real.log m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- With `n = ∏ p ^ ⌈log_p m⌉`, every root of `ψ_n F` modulo a prime of `S` has multiplicity at
least `m`. -/
theorem le_rootMultiplicity_map_expand_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ}
    {F : ℤ[X]} (hF : F.Monic) {p : ℕ} [Fact p.Prime] (hp : p ∈ S) {a : ZMod p}
    (ha : ((red p) (expand ℤ (∏ q ∈ S, q ^ Nat.clog q m) F)).IsRoot a) :
    m ≤ rootMultiplicity a ((red p) (expand ℤ (∏ q ∈ S, q ^ Nat.clog q m) F)) := by
  have hsplit : ∏ q ∈ S, q ^ Nat.clog q m =
      p ^ Nat.clog p m * ∏ q ∈ S.erase p, q ^ Nat.clog q m := (mul_prod_erase S _ hp).symm
  have hpos : 0 < ∏ q ∈ S.erase p, q ^ Nat.clog q m :=
    Finset.prod_pos fun q hq => pow_pos (hS q (mem_of_mem_erase hq)).pos _
  rw [hsplit] at ha ⊢
  exact (Nat.le_pow_clog (Fact.out : p.Prime).one_lt m).trans
    (pow_le_rootMultiplicity_map_expand p _ hpos hF ha)

#print axioms exists_eq_C_eval_of_derivative_eq_zero
#print axioms C_dvd_iterate_derivative_mul_expand_sub
#print axioms sum_log_le_log_natDegree
#print axioms prod_pow_dvd_natDegree
#print axioms pow_le_rootMultiplicity_map_expand
#print axioms log_prod_pow_clog_le
#print axioms le_rootMultiplicity_map_expand_prod

end GaloisForLFunctions.SignFreePurityMechanisms
