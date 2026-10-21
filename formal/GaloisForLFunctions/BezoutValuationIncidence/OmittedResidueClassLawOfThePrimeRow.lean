import GaloisForLFunctions.PNTPlus.Wiener
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.DualNormOfTheCrossScaleFunctional
import GaloisForLFunctions.BezoutValuationIncidence.SharpConstantOfTheRankTwoRemainder

/-!
# The omitted residue class law of the prime row

Fix a prime `p` and let `c'_Q = Λ · 1_{(Q, 2Q]}` be the von Mangoldt row on a dyadic window. Its kernel
statistic at `p` (the single-modulus statistic of the cross-scale dual norm),

`Λ_p(c'_Q) = Σ_n (c'_Q(n)/n²)(𝔅(p, n) - m_p) + Σ_n (c'_Q(n)/n³) 𝔅₃(p, n)`,

depends on `n` only through the residue `n mod p`. Two arithmetic facts decide it.

* **The coprime classes cancel exactly.** By Dirichlet's theorem in Chebyshev form
  (`WeakPNT_AP`), every class `r ≢ 0` carries the mass `W(Q)/(p-1) + o(1/Q)`,
  `W(Q) = Σ_{Q<n≤2Q} n^{-2}`; since the centred kernel has zero mean over all residues, these classes
  contribute `-(𝔅(p, 0) - m_p) W(Q)/(p-1)`.
* **The class `0` is omitted.** A prime power in `(Q, 2Q]` divisible by `p` is a power of `p`, and
  there is at most one, so the class `0` carries `O(log Q/Q²)`.

Hence (`tendsto_mul_kernelStatistic_primeWindowRow`)

`Q · Λ_p(c'_Q) → -(𝔅(p, 0) - m_p)/(2(p-1)) = -π²(p² - 1)²/(144 p² (p - 1))`.

The single-modulus statistic of the actual prime row is therefore not small: it is the sieve term of
the residue class that the primes omit, of relative size `≍ 1/p` against the trivial bound; a row
equidistributed in every class, including `0`, has statistic `o(1/Q)` instead. This law is for fixed
moduli; it says nothing about moduli growing with `Q`.
-/

open Finset Filter Topology
open ArithmeticFunction GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The prime row and Dirichlet's theorem with a linear rate -/

/-- The von Mangoldt row on the dyadic window `(Q, 2Q]`. -/
def primeWindowRow (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then vonMangoldt n else 0

/-- The centred prime-power count of the class `r` modulo `p`: `1_{n ≡ r} Λ(n) - 1/(p-1)`. -/
def classDefect (p r : ℕ) (n : ℕ) : ℝ :=
  (if n % p = r then vonMangoldt n else 0) - 1 / ((p : ℝ) - 1)

/-- **Dirichlet's theorem with a linear rate.** For a class `0 < r < p`, every `δ > 0` and all
large `x`, `|Σ_{n ≤ x} (1_{n ≡ r} Λ(n) - 1/(p-1))| ≤ δ x`. -/
theorem eventually_abs_sum_classDefect_le {p r : ℕ} (hp : p.Prime) (hr0 : 0 < r) (hrp : r < p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, |∑ n ∈ Icc 1 x, classDefect p r n| ≤ δ * x := by
  have hcop : r.Coprime p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hr0 hrp))
  have hlim := WeakPNT_AP (q := p) (a := r) hp.one_lt.le hcop hrp
  rw [Nat.totient_prime hp] at hlim
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.one_lt.le]; simp
  rw [hcast] at hlim
  have hev := (hlim.comp (tendsto_add_atTop_nat 1)).eventually
    (Metric.ball_mem_nhds _ (half_pos hδ))
  filter_upwards [hev, eventually_ge_atTop (⌈2 / δ⌉₊ + 1)] with x hx hxbig
  simp only [Function.comp_apply, Real.dist_eq] at hx
  set f : ℕ → ℝ := fun n => if n % p = r then vonMangoldt n else 0 with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef, Nat.zero_mod, (Nat.pos_iff_ne_zero.mp hr0).symm]
  have hsum : ∑ n ∈ Icc 1 x, classDefect p r n = cumsum f (x + 1) - x / ((p : ℝ) - 1) := by
    rw [cumsum, dampedSign_sum_range_succ_eq_add_Icc, hf0, zero_add]
    simp only [classDefect, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul, hfdef]
    push_cast; ring
  have hxR : ((x + 1 : ℕ) : ℝ) = (x : ℝ) + 1 := by push_cast; ring
  rw [hxR] at hx
  have hx1 : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have hb : |cumsum f (x + 1) - ((x : ℝ) + 1) / ((p : ℝ) - 1)| ≤ δ / 2 * ((x : ℝ) + 1) := by
    have h := hx.le
    rw [show cumsum f (x + 1) / ((x : ℝ) + 1) - 1 / ((p : ℝ) - 1) =
        (cumsum f (x + 1) - ((x : ℝ) + 1) / ((p : ℝ) - 1)) / ((x : ℝ) + 1) by
      field_simp] at h
    rwa [abs_div, abs_of_pos hx1, div_le_iff₀ hx1] at h
  have hpinv : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hxδ : 2 / δ + 1 ≤ (x : ℝ) := by
    have h1 : (⌈2 / δ⌉₊ : ℝ) + 1 ≤ x := by exact_mod_cast hxbig
    linarith [Nat.le_ceil (2 / δ)]
  have hδx : δ / 2 * ((x : ℝ) + 1) + 1 ≤ δ * x := by
    have : 2 ≤ δ * ((x : ℝ) - 1) := by
      have h := mul_le_mul_of_nonneg_left (show 2 / δ ≤ (x : ℝ) - 1 by linarith) hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h
    nlinarith
  rw [hsum, show cumsum f (x + 1) - (x : ℝ) / ((p : ℝ) - 1) =
    (cumsum f (x + 1) - ((x : ℝ) + 1) / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1) by ring]
  calc _ ≤ |cumsum f (x + 1) - ((x : ℝ) + 1) / ((p : ℝ) - 1)| + |1 / ((p : ℝ) - 1)| :=
        abs_add_le _ _
    _ ≤ δ / 2 * ((x : ℝ) + 1) + 1 := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / ((p : ℝ) - 1))]; linarith
    _ ≤ δ * x := hδx

/-! ## §2. The window mass `W(Q) = Σ_{Q<n≤2Q} n^{-2}` -/

/-- The window mass `W(Q) = Σ_{Q<n≤2Q} n^{-2}`. -/
def dyadicInverseSquareMass (Q : ℕ) : ℝ := ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2

theorem dyadicInverseSquareMass_le (Q : ℕ) : dyadicInverseSquareMass Q ≤ 1 / ((Q : ℝ) + 1) := by
  unfold dyadicInverseSquareMass
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  have hterm : ∀ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ 1 / ((Q : ℝ) + 1) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have : (Q : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) this 2)
  calc ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ ∑ _n ∈ Ioc Q (2 * Q), 1 / ((Q : ℝ) + 1) ^ 2 :=
        sum_le_sum hterm
    _ = (Q : ℝ) / ((Q : ℝ) + 1) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; ring
    _ ≤ 1 / ((Q : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- Telescoping bounds `1/(n(n+1)) ≤ 1/n² ≤ 1/((n-1)n)` give `Q W(Q) → 1/2`. -/
theorem tendsto_mul_dyadicInverseSquareMass : Tendsto (fun Q : ℕ => (Q : ℝ) * dyadicInverseSquareMass Q) atTop (𝓝 (1 / 2)) := by
  -- lower bound by the telescoping sum `Σ (1/n - 1/(n+1)) = 1/(Q+1) - 1/(2Q+1)`
  have htel : ∀ Q : ℕ, ∑ n ∈ Ioc Q (2 * Q), (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
      1 / ((Q : ℝ) + 1) - 1 / (2 * (Q : ℝ) + 1) := by
    intro Q
    have hshift : ∀ K : ℕ, ∑ n ∈ Ioc Q (Q + K), (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
        1 / ((Q : ℝ) + 1) - 1 / ((Q : ℝ) + K + 1) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [show Q + (K + 1) = Q + K + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
        push_cast; ring
    rw [show 2 * Q = Q + Q by ring, hshift]; ring
  have hupper : ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) * dyadicInverseSquareMass Q ≤ 1 / 2 := by
    intro Q hQ
    have htel' : ∑ n ∈ Ioc Q (2 * Q), (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
        1 / (Q : ℝ) - 1 / (2 * (Q : ℝ)) := by
      have hshift : ∀ K : ℕ, ∑ n ∈ Ioc Q (Q + K), (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
          1 / (Q : ℝ) - 1 / ((Q : ℝ) + K) := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
          rw [show Q + (K + 1) = Q + K + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
          push_cast; ring
      rw [show 2 * Q = Q + Q by ring, hshift]; ring
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hle : dyadicInverseSquareMass Q ≤ 1 / (Q : ℝ) - 1 / (2 * (Q : ℝ)) := by
      rw [← htel', dyadicInverseSquareMass]
      refine sum_le_sum fun n hn => ?_
      rw [mem_Ioc] at hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have he : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / (((n : ℝ) - 1) * n) := by
        have : (n : ℝ) - 1 ≠ 0 := by linarith
        have : (n : ℝ) ≠ 0 := by linarith
        field_simp; ring
      rw [he]
      exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
    calc (Q : ℝ) * dyadicInverseSquareMass Q ≤ (Q : ℝ) * (1 / (Q : ℝ) - 1 / (2 * (Q : ℝ))) :=
          mul_le_mul_of_nonneg_left hle hQ0.le
      _ = 1 / 2 := by field_simp; ring
  have hlower : ∀ Q : ℕ, (Q : ℝ) * (1 / ((Q : ℝ) + 1) - 1 / (2 * (Q : ℝ) + 1)) ≤
      (Q : ℝ) * dyadicInverseSquareMass Q := by
    intro Q
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg Q)
    rw [← htel Q, dyadicInverseSquareMass]
    refine sum_le_sum fun n hn => ?_
    rw [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have he : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp; ring
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hlim : Tendsto (fun Q : ℕ => (Q : ℝ) * (1 / ((Q : ℝ) + 1) - 1 / (2 * (Q : ℝ) + 1)))
      atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun Q : ℕ => (Q : ℝ) / ((Q : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
    have h2 : Tendsto (fun Q : ℕ => (Q : ℝ) / (2 * (Q : ℝ) + 1)) atTop (𝓝 (1 / 2)) := by
      have h := (tendsto_natCast_div_add_atTop (1 / 2 : ℝ)).div_const 2
      refine h.congr' (Eventually.of_forall fun Q => ?_)
      have : (0 : ℝ) < (Q : ℝ) + 1 / 2 := by positivity
      field_simp
    refine (h1.sub h2).congr' (Eventually.of_forall fun Q => ?_) |>.trans ?_
    · ring
    · norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (Eventually.of_forall hlower) ((eventually_ge_atTop 1).mono hupper)

/-! ## §3. The class masses -/

/-- The mass `M_r(Q) = Σ_{Q<n≤2Q, n ≡ r} Λ(n)/n²` of the class `r` modulo `p`. -/
def primeClassMass (p r Q : ℕ) : ℝ := ∑ n ∈ Ioc Q (2 * Q), (if n % p = r then vonMangoldt n else 0) / (n : ℝ) ^ 2

/-- **The coprime classes are equidistributed.** For `0 < r < p`,
`Q (M_r(Q) - W(Q)/(p-1)) → 0`. -/
theorem tendsto_mul_primeClassMass_sub {p r : ℕ} (hp : p.Prime) (hr0 : 0 < r) (hrp : r < p) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * (primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1)))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (eventually_abs_sum_classDefect_le hp hr0 hrp
    (show (0 : ℝ) < η / 4 by positivity))
  refine ⟨x₀ + 1, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hid : primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1) =
      ∑ n ∈ Ioc Q (2 * Q), classDefect p r n * (1 / (n : ℝ) ^ 2) := by
    rw [primeClassMass, dyadicInverseSquareMass, sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [classDefect]; ring
  have hab := abs_sum_Ioc_mul_le_of_linear (s := classDefect p r)
    (w := fun n : ℕ => 1 / (n : ℝ) ^ 2) (L := η / 4) (D := Q) (X := 2 * Q) (by omega)
    (fun x hx _ => hx₀ x (by omega)) (fun n => by positivity)
    (fun n hn => one_div_le_one_div_of_le (by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 2))
  have hhead : 2 * (Q : ℝ) * (1 / ((Q + 1 : ℕ) : ℝ) ^ 2) ≤ 2 / (Q : ℝ) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hQ0]; push_cast; nlinarith
  have htail : ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ 1 / (Q : ℝ) :=
    (dyadicInverseSquareMass_le Q).trans (one_div_le_one_div_of_le hQ0 (by linarith))
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hQ0, hid]
  calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), classDefect p r n * (1 / (n : ℝ) ^ 2)|
      ≤ (Q : ℝ) * (η / 4 * (2 / (Q : ℝ) + 1 / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left
          (add_le_add hhead htail) (by positivity))) hQ0.le
    _ = 3 * η / 4 := by field_simp; ring
    _ < η := by linarith

/-- In `(Q, 2Q]` at most one prime power is divisible by the prime `p`. -/
theorem card_filter_dvd_isPrimePow_le_one {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    ((Ioc Q (2 * Q)).filter (fun n => n % p = 0 ∧ IsPrimePow n)).card ≤ 1 := by
  refine card_le_one.mpr fun a ha b hb => ?_
  simp only [mem_filter, mem_Ioc] at ha hb
  have hpow : ∀ n, n % p = 0 → IsPrimePow n → ∃ k, n = p ^ k := by
    intro n hn hpp
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q ^ k := Nat.dvd_of_mod_eq_zero hn
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpq)
    exact ⟨k, by rw [this]⟩
  obtain ⟨i, rfl⟩ := hpow a ha.2.1 ha.2.2
  obtain ⟨j, rfl⟩ := hpow b hb.2.1 hb.2.2
  have h2 := hp.two_le
  have key : ∀ i j : ℕ, i < j → Q < p ^ i → p ^ j ≤ 2 * Q → False := by
    intro i j hij hi hj
    have : 2 * p ^ i ≤ p ^ j := by
      calc 2 * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ h2
        _ = p ^ (i + 1) := by ring
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hij
    omega
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h ha.1.1 hb.1.2).elim
  · rw [h]
  · exact (key j i h hb.1.1 ha.1.2).elim

/-- **The class `0` is omitted.** `Q M_0(Q) → 0`. -/
theorem tendsto_mul_primeClassMass_zero {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * primeClassMass p 0 Q) atTop (𝓝 0) := by
  have hbound : ∀ Q : ℕ, 1 ≤ Q → 0 ≤ (Q : ℝ) * primeClassMass p 0 Q ∧
      (Q : ℝ) * primeClassMass p 0 Q ≤ Real.log (2 * Q) / Q := by
    intro Q hQ
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hnn : 0 ≤ primeClassMass p 0 Q := sum_nonneg fun n _ => by
      split_ifs <;> positivity [vonMangoldt_nonneg (n := n)]
    refine ⟨mul_nonneg hQ0.le hnn, ?_⟩
    set S := (Ioc Q (2 * Q)).filter (fun n => n % p = 0 ∧ IsPrimePow n)
    have hsupp : primeClassMass p 0 Q = ∑ n ∈ S, vonMangoldt n / (n : ℝ) ^ 2 := by
      rw [primeClassMass, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      by_cases h0 : n % p = 0
      · by_cases hpp : IsPrimePow n
        · simp [h0, hpp]
        · have : vonMangoldt n = 0 := by
            by_contra hne; exact hpp (vonMangoldt_ne_zero_iff.mp hne)
          simp [h0, hpp, this]
      · simp [h0]
    have hterm : ∀ n ∈ S, vonMangoldt n / (n : ℝ) ^ 2 ≤ Real.log (2 * Q) / (Q : ℝ) ^ 2 := by
      intro n hn
      simp only [S, mem_filter, mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.1.le
      have hn2 : (n : ℝ) ≤ 2 * Q := by exact_mod_cast hn.1.2
      have hlog : vonMangoldt n ≤ Real.log (2 * Q) :=
        vonMangoldt_le_log.trans (Real.log_le_log hn0 hn2)
      have hlog0 : 0 ≤ Real.log (2 * (Q : ℝ)) :=
        Real.log_nonneg (by have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
                            linarith)
      calc vonMangoldt n / (n : ℝ) ^ 2 ≤ Real.log (2 * Q) / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hlog (by positivity)
        _ ≤ Real.log (2 * Q) / (Q : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left hlog0 (by positivity) (pow_le_pow_left₀ hQ0.le hQn 2)
    have hcard := card_filter_dvd_isPrimePow_le_one hp Q
    have hlog0 : 0 ≤ Real.log (2 * (Q : ℝ)) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
                          linarith)
    calc (Q : ℝ) * primeClassMass p 0 Q ≤ (Q : ℝ) * (S.card * (Real.log (2 * Q) / (Q : ℝ) ^ 2)) := by
          rw [hsupp]
          refine mul_le_mul_of_nonneg_left ?_ hQ0.le
          exact (sum_le_sum hterm).trans (by rw [sum_const, nsmul_eq_mul])
      _ ≤ (Q : ℝ) * (1 * (Real.log (2 * Q) / (Q : ℝ) ^ 2)) := by
          gcongr
          exact_mod_cast hcard
      _ = Real.log (2 * Q) / Q := by field_simp
  have hlim : Tendsto (fun Q : ℕ => Real.log (2 * (Q : ℝ)) / Q) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
    have h2 := h.const_mul 2
    simp only [mul_zero] at h2
    refine h2.congr' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_)
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    simp only [Function.comp_apply, pow_one, add_zero, one_mul]
    field_simp
  exact squeeze_zero' (eventually_ge_atTop 1 |>.mono fun Q hQ => (hbound Q hQ).1)
    (eventually_ge_atTop 1 |>.mono fun Q hQ => (hbound Q hQ).2) hlim

/-! ## §4. The omitted class law -/

/-- The cubic part `Σ_{Q<n≤2Q} Λ(n) n^{-3} 𝔅₃(p, n)` is `o(1/Q)`. -/
theorem tendsto_mul_cubicPart {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n) atTop (𝓝 0) := by
  have hbound : ∀ Q : ℕ, 1 ≤ Q → |(Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n| ≤ (p : ℝ) ^ 3 * (Real.log (2 * Q) / Q) := by
    intro Q hQ
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hlog0 : 0 ≤ Real.log (2 * (Q : ℝ)) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
                          linarith)
    have hterm : ∀ n ∈ Ioc Q (2 * Q), |vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n| ≤
        Real.log (2 * Q) / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 := by
      intro n hn
      rw [mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
      have hn2 : (n : ℝ) ≤ 2 * Q := by exact_mod_cast hn.2
      rw [abs_mul, abs_div, abs_of_nonneg vonMangoldt_nonneg, abs_of_pos (by positivity)]
      refine mul_le_mul ?_ (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
      calc vonMangoldt n / (n : ℝ) ^ 3 ≤ Real.log (2 * Q) / (n : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right (vonMangoldt_le_log.trans (Real.log_le_log hn0 hn2))
              (by positivity)
        _ ≤ Real.log (2 * Q) / (Q : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left hlog0 (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3)
    rw [abs_mul, abs_of_pos hQ0]
    calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n|
        ≤ (Q : ℝ) * ∑ _n ∈ Ioc Q (2 * Q), Real.log (2 * Q) / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)) hQ0.le
      _ = (p : ℝ) ^ 3 * (Real.log (2 * Q) / Q) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
  have hlim : Tendsto (fun Q : ℕ => (p : ℝ) ^ 3 * (Real.log (2 * (Q : ℝ)) / Q)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
    have h2 := h.const_mul (2 * (p : ℝ) ^ 3)
    simp only [mul_zero] at h2
    refine h2.congr' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_)
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    simp only [Function.comp_apply, pow_one, add_zero, one_mul]
    field_simp
  refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
  rw [Real.norm_eq_abs]; exact hbound Q hQ

/-- The kernel statistic of the prime row, grouped by residues modulo `p`. -/
theorem kernelStatistic_primeWindowRow_eq {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    kernelStatistic (2 * Q) (primeWindowRow Q) p =
      ∑ r ∈ range p, (bernoulliKernel p r - primeKernelMean p) * primeClassMass p r Q +
        ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n := by
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  have hrestrict : kernelStatistic (2 * Q) (primeWindowRow Q) p =
      ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p) +
        vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n) := by
    rw [kernelStatistic, ← sum_subset hsub fun n hn hn' => by
      have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
      simp [primeWindowRow, this]]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ioc] at hn
    simp [primeWindowRow, hn.1, hn.2]
  rw [hrestrict, sum_add_distrib]
  congr 1
  have hfib := sum_fiberwise_of_maps_to (s := Ioc Q (2 * Q)) (t := range p) (g := fun n => n % p)
    (fun n _ => mem_range.mpr (Nat.mod_lt n hp.pos))
    (fun n => vonMangoldt n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p))
  rw [← hfib]
  refine sum_congr rfl fun r hr => ?_
  rw [primeClassMass, mul_sum, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [bernoulliKernel_mod, h]; ring
  · ring

/-- **The omitted residue class law.** For every prime `p`,
`Q · Λ_p(Λ 1_{(Q,2Q]}) → -(𝔅(p, 0) - m_p)/(2(p - 1)) = -π²(p² - 1)²/(144 p² (p - 1))`. -/
theorem tendsto_mul_kernelStatistic_primeWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (primeWindowRow Q) p) atTop
      (𝓝 (-(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set b : ℕ → ℝ := fun r => bernoulliKernel p r - primeKernelMean p with hbdef
  -- the class decomposition, with the coprime classes centred at `W(Q)/(p-1)`
  have hdecomp : ∀ Q : ℕ, (Q : ℝ) * kernelStatistic (2 * Q) (primeWindowRow Q) p =
      -(b 0) / ((p : ℝ) - 1) * ((Q : ℝ) * dyadicInverseSquareMass Q) +
        ∑ r ∈ (range p).erase 0, b r * ((Q : ℝ) * (primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1))) +
          b 0 * ((Q : ℝ) * primeClassMass p 0 Q) +
            (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n := by
    intro Q
    have hsum0 : ∑ r ∈ (range p).erase 0, b r = -(b 0) := by
      have h := sum_range_bernoulliKernel_sub_mean hp
      rw [← add_sum_erase _ _ (mem_range.mpr hp.pos)] at h
      linarith
    rw [kernelStatistic_primeWindowRow_eq hp Q, ← add_sum_erase _ _ (mem_range.mpr hp.pos)]
    have hsplit : ∑ r ∈ (range p).erase 0, b r * ((Q : ℝ) * (primeClassMass p r Q -
        dyadicInverseSquareMass Q / ((p : ℝ) - 1))) = (Q : ℝ) * ∑ r ∈ (range p).erase 0, b r * primeClassMass p r Q -
          (Q : ℝ) * dyadicInverseSquareMass Q / ((p : ℝ) - 1) * ∑ r ∈ (range p).erase 0, b r := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun r _ => by ring
    rw [hsplit, hsum0]
    simp only [hbdef]
    field_simp
    ring
  -- each piece converges
  have hcop : Tendsto (fun Q : ℕ => ∑ r ∈ (range p).erase 0,
      b r * ((Q : ℝ) * (primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1)))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum ((range p).erase 0) fun r hr =>
      (tendsto_mul_primeClassMass_sub hp (Nat.pos_of_ne_zero (ne_of_mem_erase hr))
        (mem_range.mp (mem_of_mem_erase hr))).const_mul (b r)
    simpa using h
  have hlim := (((tendsto_mul_dyadicInverseSquareMass.const_mul (-(b 0) / ((p : ℝ) - 1))).add hcop).add
    ((tendsto_mul_primeClassMass_zero hp).const_mul (b 0))).add (tendsto_mul_cubicPart hp)
  have hb0 : b 0 = Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (72 * (p : ℝ) ^ 2) := by
    simp only [hbdef, bernoulliKernel_zero hp.pos, primeKernelMean]
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
  have hL : -(b 0) / ((p : ℝ) - 1) * (1 / 2) + 0 + b 0 * 0 + 0 =
      -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))) := by
    rw [hb0]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← hL]
  exact hlim.congr fun Q => (hdecomp Q).symm

end

end GaloisForLFunctions.BezoutValuationIncidence
