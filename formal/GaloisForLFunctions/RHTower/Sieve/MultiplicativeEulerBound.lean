import Mathlib.NumberTheory.EulerProduct.Basic
import GaloisForLFunctions.RHTower.Sieve.EulerDamping
import GaloisForLFunctions.HTGeometry.SquarefreeDensityLowerBound

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
  have h : ((m * n : ℕ) : ℂ) = (((m : ℝ) : ℂ)) * (((n : ℝ) : ℂ)) := by
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

theorem summable_nat_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n : ℝ)) ^ (-σ)) := by
  refine (Real.summable_nat_rpow_inv.mpr hσ).congr fun n => ?_
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
    rw [hval] at hle
    have hstep2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg q)
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
  have hb0 : (0 : ℝ) ≤ ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ := norm_nonneg _
  have hstep : ‖∑' e : ℕ, twistedSummand f s (p ^ e)‖ ≤
      Real.exp ((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2)
        + ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ := by
    rw [hsplit, ← add_assoc]
    refine le_trans (norm_add_le _ _) ?_
    linarith [norm_one_add_le_exp (twistedSummand f s p)]
  have hfold : ∀ A B : ℝ, 0 ≤ B → Real.exp A + B ≤ Real.exp (A + B * Real.exp (-A)) := by
    intro A B hB
    have hcancel : Real.exp A * (B * Real.exp (-A)) = B := by
      rw [← mul_assoc, mul_comm (Real.exp A) B, mul_assoc, ← Real.exp_add]
      simp
    have h1 : 1 + B * Real.exp (-A) ≤ Real.exp (B * Real.exp (-A)) := by
      have := Real.add_one_le_exp (B * Real.exp (-A))
      linarith
    calc Real.exp A + B = Real.exp A * (1 + B * Real.exp (-A)) := by
          rw [mul_add, mul_one, hcancel]
      _ ≤ Real.exp A * Real.exp (B * Real.exp (-A)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos A).le
      _ = Real.exp (A + B * Real.exp (-A)) := (Real.exp_add _ _).symm
  have hexpa :
      Real.exp (-((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2)) ≤ 2 := by
    have hna : -((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2) ≤ 1 / 2 := by
      have h1 : (0 : ℝ) ≤ ‖twistedSummand f s p‖ ^ 2 := sq_nonneg _
      linarith
    exact le_trans (Real.exp_le_exp.mpr hna) exp_half_le_two
  have hfinal : ((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2)
      + ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ *
        Real.exp (-((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2))
      ≤ (twistedSummand f s p).re + 5 * x ^ (-(2 * σ)) := by
    have h1 : ‖twistedSummand f s p‖ ^ 2 ≤ q ^ 2 := by
      have h0 := norm_nonneg (twistedSummand f s p)
      exact pow_le_pow_left₀ h0 hnormp 2
    have hq2nn : (0 : ℝ) ≤ 2 * q ^ 2 := by positivity
    have h2 : ‖∑' e : ℕ, twistedSummand f s (p ^ (e + 2))‖ *
        Real.exp (-((twistedSummand f s p).re + ‖twistedSummand f s p‖ ^ 2))
        ≤ (2 * q ^ 2) * 2 :=
      mul_le_mul htail hexpa (Real.exp_pos _).le hq2nn
    rw [← hq2]
    linarith
  exact le_trans hstep (le_trans (hfold _ _ hb0) (Real.exp_le_exp.mpr hfinal))

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


/-! ## The Euler bound for the whole series -/

/-- **The Euler bound for a bounded multiplicative Dirichlet series.**  The whole series, prime
powers included, is damped by the real part of its prime sum, at the cost of one absolute
constant. -/
theorem norm_tsum_twistedSummand_le_exp
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤
      Real.exp ((∑' p : Nat.Primes, (twistedSummand f s (p : ℕ)).re) + 5 / 2) := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs2 : 1 < 2 * s.re := by linarith
  have hsum := summable_norm_twistedSummand hbdd hs
  have hmul' : ∀ {m n : ℕ}, Nat.Coprime m n →
      twistedSummand f s (m * n) = twistedSummand f s m * twistedSummand f s n :=
    fun h => twistedSummand_mul hmul h
  -- the Euler product, as convergence of partial products over the primes below `n`
  have hE := EulerProduct.eulerProduct (f := twistedSummand f s) (twistedSummand_one hf1)
    hmul' hsum (twistedSummand_zero hs0)
  have hEn := hE.norm
  simp only [norm_prod] at hEn
  -- the exponent, as a function on the naturals supported on the primes
  set g : ℕ → ℝ := fun n =>
    (twistedSummand f s n).re + 5 * ((n : ℝ)) ^ (-(2 * s.re)) with hg
  set c : ℕ → ℝ := fun n => if n.Prime then g n else 0 with hc
  have hrpowsum : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 * s.re))) :=
    summable_nat_rpow_neg hs2
  have hcsum : Summable c := by
    refine Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖twistedSummand f s n‖ + 5 * ((n : ℝ)) ^ (-(2 * s.re)))
      (hsum.add (hrpowsum.mul_left 5)) fun n => ?_
    have hrnn : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(2 * s.re)) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hp : n.Prime
    · have hre : |(twistedSummand f s n).re| ≤ ‖twistedSummand f s n‖ :=
        Complex.abs_re_le_norm _
      have : ‖c n‖ ≤ |(twistedSummand f s n).re| + 5 * ((n : ℝ)) ^ (-(2 * s.re)) := by
        rw [hc]
        simp only [if_pos hp, hg]
        refine le_trans (norm_add_le _ _) ?_
        have h5 : ‖5 * ((n : ℝ)) ^ (-(2 * s.re))‖ = 5 * ((n : ℝ)) ^ (-(2 * s.re)) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [h5, Real.norm_eq_abs]
      linarith
    · rw [hc]
      simp only [if_neg hp, norm_zero]
      have h0 : (0 : ℝ) ≤ ‖twistedSummand f s n‖ := norm_nonneg _
      positivity
  have hCt := hcsum.hasSum.tendsto_sum_nat
  -- the exponential side
  have hprimesBelow : ∀ n : ℕ, ∑ i ∈ Finset.range n, c i = ∑ p ∈ Nat.primesBelow n, g p := by
    intro n
    rw [Nat.primesBelow, Finset.sum_filter]
  have hexpT : Filter.Tendsto
      (fun n : ℕ => Real.exp (∑ i ∈ Finset.range n, c i)) Filter.atTop
      (𝓝 (Real.exp (∑' n : ℕ, c n))) :=
    (Real.continuous_exp.tendsto _).comp hCt
  have hexpP : Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, Real.exp (g p)) Filter.atTop
      (𝓝 (Real.exp (∑' n : ℕ, c n))) := by
    refine hexpT.congr fun n => ?_
    rw [hprimesBelow n, Real.exp_sum]
  -- termwise comparison of the two nets
  have hcompare : ∀ n : ℕ,
      (∏ p ∈ Nat.primesBelow n, ‖∑' e : ℕ, twistedSummand f s (p ^ e)‖)
        ≤ ∏ p ∈ Nat.primesBelow n, Real.exp (g p) := by
    intro n
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
    exact norm_tsum_localFactor_le hf1 hbdd hs (Nat.prime_of_mem_primesBelow hp)
  have hmain : ‖∑' n : ℕ, twistedSummand f s n‖ ≤ Real.exp (∑' n : ℕ, c n) :=
    le_of_tendsto_of_tendsto' hEn hexpP hcompare
  -- identify the exponent
  have hnormsub : Summable (fun p : Nat.Primes => ‖twistedSummand f s (p : ℕ)‖) :=
    hsum.comp_injective fun a b h => Subtype.ext h
  have hresum : Summable (fun p : Nat.Primes => (twistedSummand f s (p : ℕ)).re) :=
    Summable.of_norm_bounded (g := fun p : Nat.Primes => ‖twistedSummand f s (p : ℕ)‖)
      hnormsub fun p => by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
  have hrsum : Summable (fun p : Nat.Primes => 5 * ((((p : ℕ)) : ℝ)) ^ (-(2 * s.re))) :=
    (summable_primes_rpow_two (le_of_lt hs)).mul_left 5
  have hsupp : Function.support c ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    have hprime : n.Prime := by
      by_contra hnp
      exact hn (by rw [hc]; simp only [if_neg hnp])
    exact ⟨⟨n, hprime⟩, rfl⟩
  have hcoe : ∑' n : ℕ, c n = ∑' p : Nat.Primes, g (p : ℕ) := by
    rw [← Function.Injective.tsum_eq (f := c) (g := fun p : Nat.Primes => (p : ℕ))
      (fun a b h => Subtype.ext h) hsupp]
    exact tsum_congr fun p => by rw [hc]; simp only [if_pos p.2]
  have hsplit : ∑' p : Nat.Primes, g (p : ℕ) =
      (∑' p : Nat.Primes, (twistedSummand f s (p : ℕ)).re) +
        ∑' p : Nat.Primes, 5 * ((((p : ℕ)) : ℝ)) ^ (-(2 * s.re)) := by
    rw [hg]
    exact hresum.tsum_add hrsum
  have htailbound : ∑' p : Nat.Primes, 5 * ((((p : ℕ)) : ℝ)) ^ (-(2 * s.re)) ≤ 5 / 2 := by
    rw [tsum_mul_left]
    have := tsum_primes_rpow_two_le (le_of_lt hs)
    linarith
  refine le_trans hmain (Real.exp_le_exp.mpr ?_)
  rw [hcoe, hsplit]
  linarith

/-! ## The bound in distance form -/

/-- The prime sum at an abscissa, `P(σ) = ∑_p p^{-σ}`. -/
noncomputable def primeAbscissaSum (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((((p : ℕ)) : ℝ)) ^ (-σ)

/-- The distance of `f` from the character at `s`, weighted at the abscissa `Re s`.  Termwise this is
`p^{-Re s}(1 - Re(f(p) p^{-i Im s}))`, written so that no polar decomposition is needed. -/
noncomputable def mulDistSqTsum (f : ℕ → ℂ) (s : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    (((((p : ℕ)) : ℝ)) ^ (-s.re) - (twistedSummand f s (p : ℕ)).re)

theorem summable_primes_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((((p : ℕ)) : ℝ)) ^ (-σ)) :=
  (summable_nat_rpow_neg hσ).comp_injective fun _ _ h => Subtype.ext h

theorem mulDistSqTsum_term_nonneg (hbdd : ∀ n, ‖f n‖ ≤ 1) (p : Nat.Primes) :
    0 ≤ ((((p : ℕ)) : ℝ)) ^ (-s.re) - (twistedSummand f s (p : ℕ)).re := by
  have h1 : (twistedSummand f s (p : ℕ)).re ≤ ‖twistedSummand f s (p : ℕ)‖ :=
    Complex.re_le_norm _
  have h2 := norm_twistedSummand_le hbdd (s := s) p.2.pos
  linarith

theorem summable_mulDistSqTsum (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      ((((p : ℕ)) : ℝ)) ^ (-s.re) - (twistedSummand f s (p : ℕ)).re) := by
  have hre : Summable (fun p : Nat.Primes => (twistedSummand f s (p : ℕ)).re) :=
    Summable.of_norm_bounded
      (g := fun p : Nat.Primes => ‖twistedSummand f s (p : ℕ)‖)
      ((summable_norm_twistedSummand hbdd hs).comp_injective fun a b h => Subtype.ext h)
      fun p => by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
  exact (summable_primes_rpow_neg hs).sub hre

theorem mulDistSqTsum_nonneg (hbdd : ∀ n, ‖f n‖ ≤ 1) (_hs : 1 < s.re) :
    0 ≤ mulDistSqTsum f s := by
  rw [mulDistSqTsum]
  exact tsum_nonneg fun p => mulDistSqTsum_term_nonneg hbdd p

/-- The prime sum of the twisted real parts is the abscissa sum minus the distance. -/
theorem tsum_re_twistedSummand_eq_sub (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    (∑' p : Nat.Primes, (twistedSummand f s (p : ℕ)).re) =
      primeAbscissaSum s.re - mulDistSqTsum f s := by
  have hre : Summable (fun p : Nat.Primes => (twistedSummand f s (p : ℕ)).re) :=
    Summable.of_norm_bounded
      (g := fun p : Nat.Primes => ‖twistedSummand f s (p : ℕ)‖)
      ((summable_norm_twistedSummand hbdd hs).comp_injective fun a b h => Subtype.ext h)
      fun p => by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
  rw [primeAbscissaSum, mulDistSqTsum, (summable_primes_rpow_neg hs).tsum_sub hre]
  ring

/-- **The Euler bound in distance form.**  Every unit of distance from the character costs the series
one factor of `e^{-1}`, against the trivial size `exp(P(σ))`.  This is the shape Halász's method
consumes at `σ = 1 + 1/log x`, where `P(σ)` is of order `log log x`. -/
theorem norm_tsum_twistedSummand_le_exp_sub_dist
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤
      Real.exp (primeAbscissaSum s.re - mulDistSqTsum f s + 5 / 2) := by
  have h := norm_tsum_twistedSummand_le_exp hf1 hmul hbdd hs
  rwa [tsum_re_twistedSummand_eq_sub hbdd hs] at h

end

end RHTower.Sieve
