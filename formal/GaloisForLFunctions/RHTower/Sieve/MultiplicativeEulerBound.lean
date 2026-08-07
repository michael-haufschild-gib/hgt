import Mathlib.NumberTheory.EulerProduct.Basic
import GaloisForLFunctions.RHTower.Sieve.EulerDamping
import GaloisForLFunctions.RHTower.SquarefreeDensityLowerBound

/-!
# The Euler bound for a bounded multiplicative Dirichlet series

The damping estimate of `EulerDamping.lean` bounds a *finite* Euler product over squarefree smooth
integers.  Halász's method needs the same bound for the whole Dirichlet series of a multiplicative
function, prime powers included:

`‖∑_n f(n) n^{-s}‖ ≤ exp(∑_p Re(f(p) p^{-s}) + 5/2)`  for `Re s > 1`, `|f| ≤ 1`.

Each local factor `∑_e f(p^e) p^{-es}` is `1 + f(p)p^{-s}` plus a tail of size at most `2p^{-2Re s}`,
so `‖1 + z‖ ≤ exp(Re z + ‖z‖²)` still applies after the tail is folded into the exponent.  The
resulting per-prime excess is summable against `∑_p p^{-2}`, whose value stays below `49/100`, so the
whole prime-power contribution costs one absolute constant.

The gain over the squarefree proxy is that the left side is now the actual Dirichlet series, so the
bound composes with Perron inversion.
-/

namespace RHTower.Sieve

open Complex Filter Nat Topology EulerProduct

/-- The twisted summand `n ↦ f n · n^{-s}` of a Dirichlet series. -/
noncomputable def twistedSummand (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  f n * (n : ℂ) ^ (-s)

section

variable {f : ℕ → ℂ} {s : ℂ}

theorem twistedSummand_zero (hs : s ≠ 0) : twistedSummand f s 0 = 0 := by
  rw [twistedSummand, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs), mul_zero]

theorem twistedSummand_one (hf1 : f 1 = 1) : twistedSummand f s 1 = 1 := by
  rw [twistedSummand, hf1, Nat.cast_one, Complex.one_cpow, mul_one]

theorem natCast_cpow_mul (m n : ℕ) :
    ((m * n : ℕ) : ℂ) ^ (-s) = ((m : ℕ) : ℂ) ^ (-s) * ((n : ℕ) : ℂ) ^ (-s) := by
  have h : ((m * n : ℕ) : ℂ) = (((m : ℝ) * (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg,
    Complex.ofReal_natCast, Complex.ofReal_natCast]

theorem twistedSummand_mul
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    {m n : ℕ} (h : Nat.Coprime m n) :
    twistedSummand f s (m * n) = twistedSummand f s m * twistedSummand f s n := by
  rw [twistedSummand, twistedSummand, twistedSummand, hmul h, natCast_cpow_mul]
  ring

theorem norm_twistedSummand_le (hbdd : ∀ n, ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖twistedSummand f s n‖ ≤ ((n : ℝ)) ^ (-s.re) := by
  have h1 : ‖((n : ℕ) : ℂ) ^ (-s)‖ = ((n : ℝ)) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  rw [twistedSummand, norm_mul, h1]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hbdd n)

theorem summable_nat_rpow_neg (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((n : ℝ)) ^ (-s.re)) := by
  refine (Real.summable_nat_rpow_inv.mpr hs).congr fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

theorem summable_norm_twistedSummand (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖twistedSummand f s n‖) := by
  refine (summable_nat_rpow_neg hs).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith
    rw [twistedSummand_zero hs0, norm_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · exact norm_twistedSummand_le hbdd hn

/-! ## The local factor -/

theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]

set_option maxHeartbeats 1000000 in
/-- **The local factor obeys the damping bound with an explicit prime-power excess.** -/
theorem norm_tsum_localFactor_le (hf1 : f 1 = 1) (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) :
    ‖∑' e : ℕ, twistedSummand f s (p ^ e)‖ ≤
      Real.exp ((twistedSummand f s p).re + 5 * ((p : ℝ)) ^ (-(2 * s.re))) := by
  set x : ℝ := (p : ℝ) with hxdef
  set σ : ℝ := s.re with hσdef
  have hx2 : (2 : ℝ) ≤ x := by
    rw [hxdef]
    exact_mod_cast hp.two_le
  have hx0 : (0 : ℝ) < x := by linarith
  set q : ℝ := x ^ (-σ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have hqx : q * x ≤ 1 := by
    have h1 : q ≤ x⁻¹ := by
      rw [hqdef, ← Real.rpow_neg_one x]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
    calc q * x ≤ x⁻¹ * x := mul_le_mul_of_nonneg_right h1 hx0.le
      _ = 1 := h2
  have hqhalf : q ≤ 1 / 2 := by
    have h2q : q * 2 ≤ q * x := mul_le_mul_of_nonneg_left hx2 hq0.le
    linarith
  have hq2 : q ^ 2 = x ^ (-(2 * σ)) := by
    rw [hqdef, ← Real.rpow_natCast (x ^ (-σ)) 2, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  -- the norm of each power term
  have hnormpow : ∀ e : ℕ, ‖twistedSummand f s (p ^ e)‖ ≤ q ^ e := by
    intro e
    have hpos : 0 < p ^ e := pow_pos hp.pos e
    have h1 := norm_twistedSummand_le hbdd (s := s) hpos
    have h2 : ((((p ^ e : ℕ)) : ℝ)) ^ (-σ) = q ^ e := by
      rw [Nat.cast_pow, ← Real.rpow_natCast x e, ← Real.rpow_mul hx0.le, hqdef,
        ← Real.rpow_natCast (x ^ (-σ)) e, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have hgeom : Summable (fun e : ℕ => q ^ e) :=
    summable_geometric_of_lt_one hq0.le (by linarith)
  have hsumnorm : Summable (fun e : ℕ => ‖twistedSummand f s (p ^ e)‖) :=
    hgeom.of_nonneg_of_le (fun e => norm_nonneg _) hnormpow
  have hsum : Summable (fun e : ℕ => twistedSummand f s (p ^ e)) :=
    Summable.of_norm hsumnorm
  -- split off the first two terms
  have hsum1 : Summable (fun e : ℕ => twistedSummand f s (p ^ (e + 1))) :=
    (summable_nat_add_iff 1).2 hsum
  have hsum2 : Summable (fun e : ℕ => twistedSummand f s (p ^ (e + 2))) :=
    (summable_nat_add_iff 2).2 hsum
  have hsplit : ∑' e : ℕ, twistedSummand f s (p ^ e) =
      1 + (twistedSummand f s p + ∑' e : ℕ, twistedSummand f s (p ^ (e + 2))) := by
    rw [hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add, pow_zero, pow_one,
      twistedSummand_one hf1]
  -- the tail
  have htail : ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ ≤ 2 * q ^ 2 := by
    have hnorm2 : Summable (fun e : ℕ => ‖twistedSummand f s (p ^ (e + 2))‖) :=
      (summable_nat_add_iff 2).2 hsumnorm
    refine le_trans (norm_tsum_le_tsum_norm hnorm2) ?_
    have hle : ∑' e : ℕ, ‖twistedSummand f s (p ^ (e + 2))‖ ≤ ∑' e : ℕ, q ^ (e + 2) :=
      Summable.tsum_le_tsum (fun e => hnormpow (e + 2)) hnorm2
        ((summable_nat_add_iff 2).2 hgeom)
    have hval : ∑' e : ℕ, q ^ (e + 2) = q ^ 2 * (1 - q)⁻¹ := by
      rw [show (fun e : ℕ => q ^ (e + 2)) = fun e : ℕ => q ^ 2 * q ^ e by
        funext e; rw [pow_add]; ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le (by linarith)]
    have hinv : (1 - q)⁻¹ ≤ 2 := by
      have h1 : (0 : ℝ) < 1 - q := by linarith
      rw [inv_le_comm₀ h1 (by norm_num : (0:ℝ) < 2)]
      linarith
    rw [hval]
    have := mul_le_mul_of_nonneg_left hinv (sq_nonneg q)
    linarith
  -- the main step
  have hnormp : ‖twistedSummand f s p‖ ≤ q := by
    have := hnormpow 1
    rwa [pow_one, pow_one] at this
  have hrep : -q ≤ (twistedSummand f s p).re := by
    have h1 : |(twistedSummand f s p).re| ≤ ‖twistedSummand f s p‖ :=
      Complex.abs_re_le_norm _
    have h2 := abs_le.mp h1
    linarith [h2.1]
  set a : ℝ := (twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2 with hadef
  set b : ℝ := ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ with hbdef
  have hb0 : 0 ≤ b := norm_nonneg _
  have hstep : ‖∑' e : ℕ, twistedSummand f s (p ^ e)‖ ≤ Real.exp a + b := by
    rw [hsplit, ← add_assoc]
    exact le_trans (norm_add_le _ _)
      (add_le_add_right (norm_one_add_le_exp (twistedSummand f s p)) _)
  have hfold : Real.exp a + b ≤ Real.exp (a + b * Real.exp (-a)) := by
    have hcancel : Real.exp a * (b * Real.exp (-a)) = b := by
      rw [← mul_assoc, mul_comm (Real.exp a) b, mul_assoc, ← Real.exp_add]
      simp
    have h1 : 1 + b * Real.exp (-a) ≤ Real.exp (b * Real.exp (-a)) := by
      have := Real.add_one_le_exp (b * Real.exp (-a))
      linarith
    calc Real.exp a + b = Real.exp a * (1 + b * Real.exp (-a)) := by
          rw [mul_add, mul_one, hcancel]
      _ ≤ Real.exp a * Real.exp (b * Real.exp (-a)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
      _ = Real.exp (a + b * Real.exp (-a)) := (Real.exp_add _ _).symm
  have hexpa : Real.exp (-a) ≤ 2 := by
    have hna : -a ≤ 1 / 2 := by
      have h1 : (0:ℝ) ≤ ‖twistedSummand f s p‖ ^ 2 := sq_nonneg _
      rw [hadef]
      linarith
    exact le_trans (Real.exp_le_exp.mpr hna) exp_half_le_two
  have hfinal : a + b * Real.exp (-a) ≤
      (twistedSummand f s p).re + 5 * x ^ (-(2 * σ)) := by
    have h1 : ‖twistedSummand f s p‖ ^ 2 ≤ q ^ 2 :=
      pow_le_pow_left (norm_nonneg _) hnormp 2
    have hq2nn : (0 : ℝ) ≤ 2 * q ^ 2 := by positivity
    have h2 : b * Real.exp (-a) ≤ (2 * q ^ 2) * 2 :=
      mul_le_mul htail hexpa (Real.exp_pos _).le hq2nn
    rw [hadef, ← hq2]
    linarith
  exact le_trans hstep (le_trans hfold (Real.exp_le_exp.mpr hfinal))

/-! ## The prime-power excess is an absolute constant -/

theorem summable_primes_inv_sq :
    Summable (fun p : Nat.Primes => (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  exact hbase.comp_injective (fun a b h => Subtype.ext h)

theorem tsum_primes_inv_sq_le :
    ∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 ≤ 49 / 100 := by
  classical
  refine summable_primes_inv_sq.tsum_le_of_sum_le fun t => ?_
  have hinj : ∀ a ∈ t, ∀ b ∈ t, ((a : ℕ) : ℕ) = ((b : ℕ) : ℕ) → a = b :=
    fun a _ b _ h => Subtype.ext h
  have himage : ∑ n ∈ t.image (fun p : Nat.Primes => (p : ℕ)), (1 : ℝ) / ((n : ℝ)) ^ 2
      = ∑ p ∈ t, (1 : ℝ) / (((p : ℕ) : ℝ)) ^ 2 := Finset.sum_image hinj
  set u : Finset ℕ := t.image (fun p : Nat.Primes => (p : ℕ)) with hu
  have hsub : u ⊆ Nat.primesBelow (u.sup id + 1) := by
    intro n hn
    have hprime : n.Prime := by
      rw [hu, Finset.mem_image] at hn
      obtain ⟨p, _, rfl⟩ := hn
      exact p.2
    have hlt : n < u.sup id + 1 :=
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
    exact Nat.mem_primesBelow.mpr ⟨hlt, hprime⟩
  have hle : ∑ n ∈ u, (1 : ℝ) / ((n : ℝ)) ^ 2
      ≤ ∑ n ∈ Nat.primesBelow (u.sup id + 1), (1 : ℝ) / ((n : ℝ)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
  rw [← himage]
  exact le_trans hle (sum_primesBelow_one_div_sq_le _)

theorem rpow_two_le_inv_sq {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    ((p : ℝ)) ^ (-(2 * σ)) ≤ (1 : ℝ) / ((p : ℝ)) ^ 2 := by
  have hx2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hx0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : ((p : ℝ)) ^ (-(2 * σ)) ≤ ((p : ℝ)) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((p : ℝ)) ^ (-(2 : ℝ)) = (1 : ℝ) / ((p : ℝ)) ^ 2 := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  rw [h2] at h1
  exact h1

theorem summable_primes_rpow_two {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun p : Nat.Primes => ((((p : ℕ)) : ℝ)) ^ (-(2 * σ))) := by
  refine summable_primes_inv_sq.of_nonneg_of_le (fun p => ?_) fun p => ?_
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact rpow_two_le_inv_sq hσ p.2

theorem tsum_primes_rpow_two_le {σ : ℝ} (hσ : 1 ≤ σ) :
    ∑' p : Nat.Primes, ((((p : ℕ)) : ℝ)) ^ (-(2 * σ)) ≤ 49 / 100 :=
  le_trans
    (Summable.tsum_le_tsum (fun p => rpow_two_le_inv_sq hσ p.2)
      (summable_primes_rpow_two hσ) summable_primes_inv_sq)
    tsum_primes_inv_sq_le

end

end RHTower.Sieve
