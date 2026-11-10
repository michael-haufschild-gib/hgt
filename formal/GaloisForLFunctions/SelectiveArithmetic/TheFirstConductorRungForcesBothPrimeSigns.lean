import GaloisForLFunctions.SelectiveArithmetic.TheSignIsSquareRootCancellationOfTheRieszMean
import GaloisForLFunctions.SelectiveArithmetic.BoundedShapesDoNotDecideFeasibility
import GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum

/-!
# The first conductor rung forces both prime signs

Missing one prime sign makes a real character's Riesz mean equal, up to ramified
primes and proper prime powers, to a signed untwisted Riesz mean. Ramified primes
cost at most `2a log q`; proper powers cost `O(a² exp a)`.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-- A prime at which a Dirichlet character vanishes divides its modulus. -/
theorem prime_dvd_of_character_eq_zero {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hzero : χ (p : ZMod q) = 0) : p ∣ q := by
  by_contra hn
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hn)
  exact (hu.map χ.toMonoidHom).ne_zero hzero

/-- The total von Mangoldt mass of ramified primes is at most `log q`. -/
theorem sum_ramified_prime_mass_le {q N : ℕ} (hq : q ≠ 0) :
    ∑ p ∈ (Icc 2 N).filter (fun p => p.Prime ∧ p ∣ q), (Λ p : ℝ) ≤ Real.log q := by
  rw [← ArithmeticFunction.vonMangoldt_sum]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hp).2.2, hq⟩
  · intro p _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- When every unramified prime has sign `s`, only ramification and proper powers
separate the character Riesz mean from the signed prime main term. -/
theorem riesz_twist_error_le {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    {a s : ℝ} (ha : 0 ≤ a) (hs : |s| = 1)
    (hprime : ∀ p : ℕ, p.Prime → p ≤ ⌊Real.exp (2 * a)⌋₊ →
      χ (p : ZMod q) = 0 ∨ χ (p : ZMod q) = (s : ℂ)) :
    |(∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)) -
      s * ∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n)| ≤
      2 * a * Real.log q +
        4 * a * ∑ n ∈ (Icc 2 ⌊Real.exp (2 * a)⌋₊).filter (fun n => ¬ n.Prime), (Λ n : ℝ) := by
  classical
  let N := ⌊Real.exp (2 * a)⌋₊
  have hpoint (n : ℕ) (hn : n ∈ Icc 2 N) :
      |(twistWeight χ n - s * (Λ n : ℝ)) * (2 * a - Real.log n)| ≤
        2 * a * (if n.Prime ∧ n ∣ q then (Λ n : ℝ) else 0) +
          4 * a * (if ¬ n.Prime then (Λ n : ℝ) else 0) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : 0 < n)
    have hnE : (n : ℝ) ≤ Real.exp (2 * a) :=
      (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans
        (Nat.floor_le (Real.exp_pos _).le)
    have hlog : Real.log n ≤ 2 * a := by
      simpa only [Real.log_exp] using Real.log_le_log hn0 hnE
    have hw : 0 ≤ 2 * a - Real.log n := sub_nonneg.mpr hlog
    have hw' : 2 * a - Real.log n ≤ 2 * a := by
      linarith only [Real.log_natCast_nonneg n]
    have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hp : n.Prime
    · rcases hprime n hp (mem_Icc.mp hn).2 with hz | hz
      · have hd := prime_dvd_of_character_eq_zero χ hp hz
        simp only [twistWeight, hz, Complex.zero_re, mul_zero, zero_sub,
          abs_mul, abs_neg, hs, one_mul, abs_of_nonneg hΛ, abs_of_nonneg hw,
          if_pos (And.intro hp hd), if_false, not_true_eq_false, hp, add_zero]
        nlinarith only [mul_le_mul_of_nonneg_left hw' hΛ]
      · have he : twistWeight χ n - s * (Λ n : ℝ) = 0 := by
          simp only [twistWeight, hz, Complex.ofReal_re]
          ring
        rw [he, zero_mul, abs_zero]
        positivity
    · have he : |twistWeight χ n - s * (Λ n : ℝ)| ≤ 2 * (Λ n : ℝ) := by
        have htw := dominated_twistWeight χ n
        have hsm : |s * (Λ n : ℝ)| = Λ n := by rw [abs_mul, hs, one_mul, abs_of_nonneg hΛ]
        have htri := abs_sub (twistWeight χ n) (s * (Λ n : ℝ))
        rw [hsm] at htri
        linarith only [htri, htw]
      simp only [hp, false_and, if_false, not_false_eq_true, if_true, mul_zero, zero_add]
      rw [abs_mul, abs_of_nonneg hw]
      have hm := mul_le_mul he hw' hw (by positivity : (0 : ℝ) ≤ 2 * Λ n)
      nlinarith only [hm]
  have he : (∑ n ∈ Icc 2 N, twistWeight χ n * (2 * a - Real.log n)) -
      s * ∑ n ∈ Icc 2 N, (Λ n : ℝ) * (2 * a - Real.log n) =
      ∑ n ∈ Icc 2 N, (twistWeight χ n - s * (Λ n : ℝ)) * (2 * a - Real.log n) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  change |_ - s * _| ≤ _
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpoint).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, ← sum_filter]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (sum_ramified_prime_mass_le hq) (by positivity)) _

/-- Proper prime powers up to `exp(2a)` have von Mangoldt mass `O(a exp a)`. -/
theorem sum_nonprime_mass_le_exp {a : ℝ} (ha : 0 ≤ a) :
    ∑ n ∈ (Icc 2 ⌊Real.exp (2 * a)⌋₊).filter (fun n => ¬ n.Prime), (Λ n : ℝ) ≤
      Real.exp a * (4 * a + 4 * Real.log 4 + 16) := by
  classical
  let N := ⌊Real.exp (2 * a)⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by linarith : 0 ≤ 2 * a))
  have hNE : (N : ℝ) ≤ Real.exp (2 * a) := Nat.floor_le (Real.exp_pos _).le
  have hlog : Real.log N ≤ 2 * a := by
    simpa only [Real.log_exp] using Real.log_le_log
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNE
  have hsqrt (n : ℕ) (hn : n ∈ Icc 2 N) : Real.sqrt n ≤ Real.exp a := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have he : Real.exp a ^ 2 = Real.exp (2 * a) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans hNE
  have hsum : ∑ n ∈ (Icc 2 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) ≤
      Real.exp a * ∑ n ∈ (Ioc 0 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) / Real.sqrt n := by
    calc
      _ ≤ Real.exp a * ∑ n ∈ (Icc 2 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) / Real.sqrt n := by
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ) < n := by
          exact_mod_cast (by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega : 0 < n)
        have hsp := Real.sqrt_pos.mpr hn0
        rw [mul_div_assoc, le_div_iff₀ hsp]
        nlinarith only [mul_le_mul_of_nonneg_left (hsqrt n (mem_filter.mp hn).1)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          obtain ⟨hn, hp⟩ := mem_filter.mp hn
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,
            (mem_Icc.mp hn).2⟩, hp⟩) (fun n _ _ => by positivity)) (Real.exp_pos _).le
  refine hsum.trans ((mul_le_mul_of_nonneg_left
    (_root_.RHTower.sum_nonprime_vonMangoldt_div_sqrt_le hN) (Real.exp_pos _).le).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith only [hlog]

/-- At every aperture above `log log q` by a fixed amount, positivity on the two
polar packets rules out a single sign on all unramified primes in the window. -/
theorem exists_first_rung_excludes_one_prime_sign {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ {q : ℕ} [NeZero q] (hq : 1 < q), M ≤ Real.log q →
      ∀ {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive),
      let a := Real.log (Real.log q) + η
      0 ≤ twistedZeroSum hq hprim (evenPolar a (Real.exp (-a))) →
      0 ≤ twistedZeroSum hq hprim (oddPolar a (Real.exp (-a))) →
      ∀ s : ℝ, |s| = 1 → ¬ (∀ p : ℕ, p.Prime → p ≤ ⌊Real.exp (2 * a)⌋₊ →
        χ (p : ZMod q) = 0 ∨ χ (p : ZMod q) = (s : ℂ)) := by
  obtain ⟨C, hC⟩ := exists_riesz_twist_le_of_nonneg
  let c := Real.exp (-η)
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show -η < 0 by linarith only [hη])
  let ε := (1 - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith only [hc1]
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith only [hc0]
  obtain ⟨Y₀, hY₀, hY⟩ := exists_riesz_ge hε hε1
  let D := 4 * Real.log 4 + 16
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let K := |C| + 20 + 4 * D + 3 * Real.pi
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_cubic_lt_exp K hε)
  let A₀ := max (max A 1) (Real.log Y₀ / 2)
  refine ⟨Real.exp A₀, fun {q} _ hq hqM χ hprim => ?_⟩
  dsimp only
  let a := Real.log (Real.log q) + η
  intro hE hO s hs hprime
  have hx : 0 < Real.log q := (Real.exp_pos _).trans_le hqM
  have hlog : A₀ ≤ Real.log (Real.log q) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hqM
  have haA : A₀ ≤ a := by dsimp [a]; linarith only [hlog, hη]
  have ha : 1 ≤ a := ((le_max_right A 1).trans (le_max_left _ _)).trans haA
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hsmall := hA a (((le_max_left A 1).trans (le_max_left _ _)).trans haA)
  have hYa : Y₀ ≤ Real.exp (2 * a) := by
    rw [← Real.exp_log (zero_lt_one.trans_le hY₀)]
    apply Real.exp_le_exp.mpr
    have hh := (le_max_right (max A 1) (Real.log Y₀ / 2)).trans haA
    linarith only [hh]
  have hmain := hY (Real.exp (2 * a)) hYa
  rw [riesz_window_eq a] at hmain
  have hupper := hC hq hprim ha hE hO
  have herr := riesz_twist_error_le (NeZero.ne q) χ ha0 hs hprime
  have hpower := mul_le_mul_of_nonneg_left (sum_nonprime_mass_le_exp ha0)
    (by positivity : 0 ≤ 4 * a)
  have htriangle :
      s * (∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n)) =
      (∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)) -
        ((∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)) -
          s * (∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n))) := by ring
  have htri := abs_sub
    (∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n))
    ((∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)) -
      s * (∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n)))
  rw [← htriangle, abs_mul, hs, one_mul] at htri
  have hmain' := hmain.trans (le_abs_self _)
  have hxE : Real.log q = c * Real.exp a := by
    dsimp [c, a]
    rw [← Real.exp_add]
    rw [show -η + (Real.log (Real.log q) + η) = Real.log (Real.log q) by ring,
      Real.exp_log hx]
  have hE1 : 1 ≤ Real.exp a := Real.one_le_exp ha0
  have hpow1 : 1 ≤ (1 + a) ^ 3 := one_le_pow₀ (by linarith only [ha])
  have hpowA : a ≤ (1 + a) ^ 3 := by
    nlinarith only [sq_nonneg a, pow_nonneg ha0 3, ha]
  have hpowA2 : a ^ 2 ≤ (1 + a) ^ 3 := by
    nlinarith only [sq_nonneg a, pow_nonneg ha0 3, ha]
  have hCE : C * (1 + a) ^ 3 ≤ |C| * (1 + a) ^ 3 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hpoly : 4 * c * a + 16 * a ^ 2 + 4 * D * a + Real.pi + 2 * Real.pi * a +
      C * (1 + a) ^ 3 ≤ K * (1 + a) ^ 3 := by
    have hca : c * a ≤ a := mul_le_of_le_one_left ha0 hc1.le
    have hDa := mul_le_mul_of_nonneg_left hpowA hD
    have hπa := mul_le_mul_of_nonneg_left hpowA Real.pi_pos.le
    have hπ1 := mul_le_mul_of_nonneg_left hpow1 Real.pi_pos.le
    dsimp [K]
    nlinarith only [hca, hpowA, hpowA2, hDa, hπa, hπ1, hCE]
  have hrem : (Real.log q + Real.pi) * (Real.exp a + 2 * a) +
      C * (1 + a) ^ 3 * Real.exp a + 2 * a * Real.log q +
        4 * a * (Real.exp a * (4 * a + D)) < (1 - ε) * Real.exp (2 * a) := by
    rw [hxE]
    have hπE := mul_le_mul_of_nonneg_left hE1 (mul_nonneg Real.pi_pos.le ha0)
    have hpolyE := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos a).le
    have hsmallE := mul_lt_mul_of_pos_right hsmall (Real.exp_pos a)
    have he : Real.exp (2 * a) = Real.exp a * Real.exp a := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp only [ε] at *
    nlinarith only [hπE, hpolyE, hsmallE]
  dsimp only [D] at hrem
  linarith only [hmain', htri, hupper, herr, hpower, hrem]

/-- Positivity at aperture `log log q + η` forces genuine primes of both signs
strictly below `exp(2η) log²q`, uniformly over real primitive characters. -/
theorem first_conductor_rung_forces_both_prime_signs {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ {q : ℕ} [NeZero q] (hq : 1 < q), M ≤ Real.log q →
      ∀ {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive), MulChar.IsQuadratic χ →
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        tsupport (fun u => (f u : ℂ)) ⊆
          Set.Icc (-(Real.log (Real.log q) + η)) (Real.log (Real.log q) + η) →
        0 ≤ twistedZeroSum hq hprim f) →
      (∃ p : ℕ, p.Prime ∧ (p : ℝ) < Real.exp (2 * η) * Real.log q ^ 2 ∧
        χ (p : ZMod q) = 1) ∧
      (∃ p : ℕ, p.Prime ∧ (p : ℝ) < Real.exp (2 * η) * Real.log q ^ 2 ∧
        χ (p : ZMod q) = -1) := by
  obtain ⟨M, hM⟩ := exists_first_rung_excludes_one_prime_sign (half_pos hη)
  refine ⟨max M 1, fun {q} _ hq hqM χ hprim hquad hpos => ?_⟩
  let a := Real.log (Real.log q) + η / 2
  have hx : 0 < Real.log q := zero_lt_one.trans_le ((le_max_right _ _).trans hqM)
  have haa : a ≤ Real.log (Real.log q) + η := by dsimp [a]; linarith only [hη]
  have hsupp : Set.Icc (-a) a ⊆
      Set.Icc (-(Real.log (Real.log q) + η)) (Real.log (Real.log q) + η) := by
    intro u hu
    exact ⟨(neg_le_neg haa).trans hu.1, hu.2.trans haa⟩
  have hE : 0 ≤ twistedZeroSum hq hprim (evenPolar a (Real.exp (-a))) :=
    hpos _ ((contDiff_evenPolar a _).of_le (by norm_num))
      ((tsupport_ofReal_subset_of_eq_zero fun u hu =>
        evenPolar_eq_zero (Real.exp_pos _) hu).trans hsupp)
  have hO : 0 ≤ twistedZeroSum hq hprim (oddPolar a (Real.exp (-a))) :=
    hpos _ ((contDiff_oddPolar a _).of_le (by norm_num))
      ((tsupport_ofReal_subset_of_eq_zero fun u hu =>
        oddPolar_eq_zero (Real.exp_pos _) hu).trans hsupp)
  have hno := hM hq ((le_max_left _ _).trans hqM) hprim hE hO
  have hbound : ∀ p : ℕ, p ≤ ⌊Real.exp (2 * a)⌋₊ →
      (p : ℝ) < Real.exp (2 * η) * Real.log q ^ 2 := by
    intro p hp
    have he : Real.exp (2 * a) = Real.exp η * Real.log q ^ 2 := by
      rw [show 2 * a = η + (Real.log (Real.log q) + Real.log (Real.log q)) by dsimp [a]; ring,
        Real.exp_add, Real.exp_add, Real.exp_log hx]
      ring
    have hle : (p : ℝ) ≤ Real.exp (2 * a) :=
      (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (2 * a)⌋₊).trans
        (Nat.floor_le (Real.exp_pos _).le)
    rw [he] at hle
    exact hle.trans_lt (mul_lt_mul_of_pos_right
      (Real.exp_lt_exp.mpr (by linarith only [hη])) (sq_pos_of_pos hx))
  constructor
  · by_contra hn
    push Not at hn
    apply hno (-1) (by norm_num)
    intro p hp hpN
    rcases hquad (p : ZMod q) with hz | hz | hz
    · exact Or.inl hz
    · exact False.elim (hn p hp (hbound p hpN) hz)
    · exact Or.inr (by simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hz)
  · by_contra hn
    push Not at hn
    apply hno 1 (by norm_num)
    intro p hp hpN
    rcases hquad (p : ZMod q) with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr (by simpa only [Complex.ofReal_one] using hz)
    · exact False.elim (hn p hp (hbound p hpN) hz)

end GaloisForLFunctions.SelectiveArithmetic
