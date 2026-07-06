/-
Chebyshev window counts: the prime mass of a multiplicative window.

Chebyshev's two bounds — `θ x ≤ x·log 4` and
`(x−1)·log 2 − log(x+2) − 2√x·log x ≤ θ x` — pin the log-weighted prime mass of the
window `(x, y]` from below by `y·log 2 − x·log 4` up to explicit lower-order terms.
Dividing by `log y` counts primes: any multiplicative window `(x, e^L·x]` of
logarithmic length `L > log 2` contains at least
`((y−1)log 2 − log(y+2) − 2√y·log y − x·log 4)/log y` primes — a quantity that grows
like `x·(e^L·log 2 − log 4)/log x`, unboundedly.  This turns the one-prime-per-window
Bertrand supply into a divergent-budget supply on the same windows.
-/
import GaloisForLFunctions.RHTower.DefectSteering

noncomputable section

namespace RHTower

open Finset

/-- The primes of the window `(x, y]`. -/
def windowPrimes (x y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime

theorem mem_windowPrimes {x y : ℝ} {p : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p ∈ windowPrimes x y ↔ Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ y := by
  unfold windowPrimes
  rw [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (Nat.floor_lt hx).mp h1,
      le_trans (Nat.cast_le.mpr h2) (Nat.floor_le hy)⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(Nat.floor_lt hx).mpr h1, Nat.le_floor h2⟩, hp⟩

/-- The window's log-weighted prime mass is the θ-increment. -/
theorem sum_log_windowPrimes {x y : ℝ} (hxy : x ≤ y) :
    ∑ p ∈ windowPrimes x y, Real.log p
      = Chebyshev.theta y - Chebyshev.theta x := by
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hsplit : Finset.Ioc 0 ⌊y⌋₊ = Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ :=
    (Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hfl).symm
  have hdisj : Disjoint ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime) := by
    have h : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact absurd (mem_Ioc.mp hz').1 (not_lt.mpr (mem_Ioc.mp hz).2)
    exact h.mono (filter_subset _ _) (filter_subset _ _)
  have hθy : Chebyshev.theta y
      = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p
        + ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta, hsplit, filter_union, sum_union hdisj]
  have hθx : Chebyshev.theta x
      = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := rfl
  rw [hθy, hθx]
  unfold windowPrimes
  ring

/-- **The Chebyshev window count**: the number of primes in `(x, y]` is at least the
window's θ-mass divided by `log y`, and the mass is at least
`(y−1)·log 2 − log(y+2) − 2√y·log y − x·log 4`. -/
theorem windowPrimes_card_ge {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (y - 1) * Real.log 2 - Real.log (y + 2) - 2 * Real.sqrt y * Real.log y
        - Real.log 4 * x
      ≤ (windowPrimes x y).card * Real.log y := by
  have hy1 : (1 : ℝ) ≤ y := le_trans hx hxy
  have hylog : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hmass : (y - 1) * Real.log 2 - Real.log (y + 2) - 2 * Real.sqrt y * Real.log y
      - Real.log 4 * x ≤ ∑ p ∈ windowPrimes x y, Real.log p := by
    rw [sum_log_windowPrimes hxy]
    have h1 := Chebyshev.theta_ge' hy1
    have h2 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ x by linarith)
    linarith
  have hsum : ∑ p ∈ windowPrimes x y, Real.log p
      ≤ (windowPrimes x y).card * Real.log y := by
    have h := Finset.sum_le_card_nsmul (windowPrimes x y) (fun p => Real.log (p : ℝ))
      (Real.log y) ?_
    · rwa [nsmul_eq_mul] at h
    · intro p hp
      obtain ⟨hprime, hlt, hle⟩ := (mem_windowPrimes (by linarith) (by linarith)).mp hp
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
      exact Real.log_le_log hppos hle
  linarith

/-! ### The window supply interface: prime gaps as a named input -/

/-- **The window prime supply at logarithmic length `L`**: beyond some threshold, every
logarithmic window of length `L` contains a prime.  For `L > log 2` this is a theorem
(Bertrand / Chebyshev); for arbitrarily small `L` it is the short-gap consequence of
the prime number theorem, `log(p'/p) → 0` — the named quantitative input for steering
at all heights. -/
def PrimeWindowSupply (L : ℝ) : Prop :=
  ∃ X : ℝ, ∀ b : ℝ, X ≤ b → ∃ p : ℕ, Nat.Prime p ∧ Real.log p ∈ Set.Ioo b (b + L)

/-- The supply is monotone in the window length. -/
theorem PrimeWindowSupply.mono {L L' : ℝ} (hLL' : L ≤ L') (h : PrimeWindowSupply L) :
    PrimeWindowSupply L' := by
  obtain ⟨X, hX⟩ := h
  refine ⟨X, fun b hb => ?_⟩
  obtain ⟨p, hp, h1, h2⟩ := hX b hb
  exact ⟨p, hp, h1, by linarith⟩

/-- **The unconditional instance**: window lengths above `log 2` are supplied by
Bertrand's postulate. -/
theorem primeWindowSupply_of_log_two_lt {L : ℝ} (hL : Real.log 2 < L) :
    PrimeWindowSupply L := by
  refine ⟨max 1 (-Real.log (L - Real.log 2) + 1), fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_left _ _) hb
  have hb2 : -Real.log (L - Real.log 2) + 1 ≤ b := le_trans (le_max_right _ _) hb
  have hexp1 : (0 : ℝ) < Real.exp b := Real.exp_pos b
  have hgap : Real.exp (-b) < L - Real.log 2 := by
    have h1 : Real.exp (-b) < Real.exp (Real.log (L - Real.log 2)) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_log (by linarith)] at h1
  obtain ⟨p, hp, hQ, hmem⟩ := exists_prime_log_mem_Ioo 0
    (by exact_mod_cast hexp1) hgap
  exact ⟨p, hp, hmem⟩

/-- The sine floor on the central half-window: `sin θ ≥ √2/2` on `[π/4, 3π/4]`. -/
theorem sin_ge_sqrt_two_div_two {θ : ℝ} (h1 : Real.pi / 4 ≤ θ)
    (h2 : θ ≤ 3 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin θ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases le_or_gt θ (Real.pi / 2) with hle | hgt
  · rw [← Real.sin_pi_div_four]
    exact Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, hle⟩ h1
  · rw [← Real.sin_pi_sub θ, ← Real.sin_pi_div_four]
    exact Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

/-- **Conditional steering at every height**: given the window supply at length
`π/(2τ)`, every quarter-offset sine window is hit, so positive-sine primes of
arbitrarily large size exist at EVERY height `τ > 0` — with the uniform sine floor
`√2/2` from the quarter-window placement. -/
theorem exists_prime_sin_pos_of_supply {τ : ℝ} (hτ : 0 < τ)
    (hsupply : PrimeWindowSupply (Real.pi / (2 * τ))) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      Real.sqrt 2 / 2 ≤ Real.sin (τ * Real.log q) := by
  obtain ⟨X, hX⟩ := hsupply
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max (τ * X / (2 * Real.pi)) (τ * Real.log ((Q : ℝ) + 1) / (2 * Real.pi)))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  set b := (2 * Real.pi * (k : ℝ) + Real.pi / 4) / τ with hbdef
  have hk1 : τ * X / (2 * Real.pi) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hk2 : τ * Real.log ((Q : ℝ) + 1) / (2 * Real.pi) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have hbX : X ≤ b := by
    rw [div_lt_iff₀ h2pi] at hk1
    rw [hbdef, le_div_iff₀ hτ]
    nlinarith
  obtain ⟨q, hq, hmem⟩ := hX b hbX
  have hQq : Q < q := by
    have hlogQ : Real.log ((Q : ℝ) + 1) < Real.log q := by
      rw [div_lt_iff₀ h2pi] at hk2
      have hbQ : Real.log ((Q : ℝ) + 1) < b := by
        rw [hbdef, lt_div_iff₀ hτ]
        nlinarith
      linarith [hmem.1]
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
    have h := (Real.log_lt_log_iff (by positivity) hqpos).mp hlogQ
    exact_mod_cast (by linarith : (Q : ℝ) < (q : ℝ))
  refine ⟨q, hq, hQq, ?_⟩
  have hhalf : τ * (Real.pi / (2 * τ)) = Real.pi / 2 := by
    rw [mul_comm (2 : ℝ) τ, ← div_div, ← mul_div_assoc, mul_comm τ (Real.pi / τ),
      div_mul_cancel₀ _ hτ.ne']
  have hτb : τ * b = 2 * Real.pi * (k : ℝ) + Real.pi / 4 := by
    rw [hbdef, mul_comm, div_mul_cancel₀ _ hτ.ne']
  have h1 : 2 * Real.pi * (k : ℝ) + Real.pi / 4 < τ * Real.log q := by
    have h := mul_lt_mul_of_pos_left hmem.1 hτ
    linarith
  have h2 : τ * Real.log q < 2 * Real.pi * (k : ℝ) + 3 * Real.pi / 4 := by
    have h := mul_lt_mul_of_pos_left hmem.2 hτ
    rw [mul_add, hτb, hhalf] at h
    linarith
  have hper : Real.sin (τ * Real.log q)
      = Real.sin (τ * Real.log q - (k : ℤ) * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  rw [hper]
  apply sin_ge_sqrt_two_div_two
  · push_cast
    linarith
  · push_cast
    linarith

/-- **Conditional negative steering at every height**: the `5π/4`-offset windows give
primes with `sin(τ·log q) ≤ −√2/2` beyond any bound, at every height `τ > 0`. -/
theorem exists_prime_sin_neg_of_supply {τ : ℝ} (hτ : 0 < τ)
    (hsupply : PrimeWindowSupply (Real.pi / (2 * τ))) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      Real.sin (τ * Real.log q) ≤ -(Real.sqrt 2 / 2) := by
  obtain ⟨X, hX⟩ := hsupply
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max (τ * X / (2 * Real.pi)) (τ * Real.log ((Q : ℝ) + 1) / (2 * Real.pi)))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  set b := (2 * Real.pi * (k : ℝ) + 5 * Real.pi / 4) / τ with hbdef
  have hk1 : τ * X / (2 * Real.pi) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hk2 : τ * Real.log ((Q : ℝ) + 1) / (2 * Real.pi) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have hbX : X ≤ b := by
    rw [div_lt_iff₀ h2pi] at hk1
    rw [hbdef, le_div_iff₀ hτ]
    nlinarith
  obtain ⟨q, hq, hmem⟩ := hX b hbX
  have hQq : Q < q := by
    have hlogQ : Real.log ((Q : ℝ) + 1) < Real.log q := by
      rw [div_lt_iff₀ h2pi] at hk2
      have hbQ : Real.log ((Q : ℝ) + 1) < b := by
        rw [hbdef, lt_div_iff₀ hτ]
        nlinarith
      linarith [hmem.1]
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
    have h := (Real.log_lt_log_iff (by positivity) hqpos).mp hlogQ
    exact_mod_cast (by linarith : (Q : ℝ) < (q : ℝ))
  refine ⟨q, hq, hQq, ?_⟩
  have hhalf : τ * (Real.pi / (2 * τ)) = Real.pi / 2 := by
    rw [mul_comm (2 : ℝ) τ, ← div_div, ← mul_div_assoc, mul_comm τ (Real.pi / τ),
      div_mul_cancel₀ _ hτ.ne']
  have hτb : τ * b = 2 * Real.pi * (k : ℝ) + 5 * Real.pi / 4 := by
    rw [hbdef, mul_comm, div_mul_cancel₀ _ hτ.ne']
  have h1 : 2 * Real.pi * (k : ℝ) + 5 * Real.pi / 4 < τ * Real.log q := by
    have h := mul_lt_mul_of_pos_left hmem.1 hτ
    linarith
  have h2 : τ * Real.log q < 2 * Real.pi * (k : ℝ) + 7 * Real.pi / 4 := by
    have h := mul_lt_mul_of_pos_left hmem.2 hτ
    rw [mul_add, hτb, hhalf] at h
    linarith
  have hper : Real.sin (τ * Real.log q)
      = Real.sin (τ * Real.log q - (k : ℤ) * (2 * Real.pi)) :=
    (Real.sin_sub_int_mul_two_pi _ _).symm
  have hshift : Real.sin (τ * Real.log q - (k : ℤ) * (2 * Real.pi))
      = -Real.sin (τ * Real.log q - (k : ℤ) * (2 * Real.pi) - Real.pi) := by
    have h := Real.sin_add_pi (τ * Real.log q - (k : ℤ) * (2 * Real.pi) - Real.pi)
    rw [sub_add_cancel] at h
    exact h
  rw [hper, hshift, neg_le_neg_iff]
  apply sin_ge_sqrt_two_div_two
  · push_cast
    linarith
  · push_cast
    linarith

/-- **The steering wheel at every height, from the gap supply**: given the window
prime supply at length `π/(2·Im s)`, the defect walk has strictly positive steps at
every prime scale — at EVERY height, not only below `π/log 2`. -/
theorem exists_prime_mirrorTiltIncrement_pos_of_supply {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hτ : 0 < s.im)
    (hsupply : PrimeWindowSupply (Real.pi / (2 * s.im))) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧ 0 < mirrorTiltIncrement q s := by
  obtain ⟨q, hq, hQq, hsin⟩ := exists_prime_sin_pos_of_supply hτ hsupply Q
  have hpos : 0 < Real.sin (s.im * Real.log q) :=
    lt_of_lt_of_le (by positivity) hsin
  exact ⟨q, hq, hQq, mirrorTiltIncrement_pos hq.two_le h0 h1 hpos⟩

/-- **The reverse steering wheel at every height, from the gap supply.** -/
theorem exists_prime_mirrorTiltIncrement_neg_of_supply {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hτ : 0 < s.im)
    (hsupply : PrimeWindowSupply (Real.pi / (2 * s.im))) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧ mirrorTiltIncrement q s < 0 := by
  obtain ⟨q, hq, hQq, hsin⟩ := exists_prime_sin_neg_of_supply hτ hsupply Q
  have hneg : Real.sin (s.im * Real.log q) < 0 :=
    lt_of_le_of_lt hsin (neg_lt_zero.mpr (by positivity))
  exact ⟨q, hq, hQq, mirrorTiltIncrement_neg hq.two_le h0 h1 hneg⟩

/-! ### Greedy accumulation: small nonnegative steps with large total hit every level -/

/-- The defect over a prime set is the sum of the per-prime mirror increments. -/
theorem anchorMirrorDefect_eq_sum (P : Finset ℕ) (s : ℂ) :
    anchorMirrorDefect P s = ∑ q ∈ P, mirrorTiltIncrement q s := by
  unfold anchorMirrorDefect anchorTilt mirrorTiltIncrement
  rw [← Finset.sum_add_distrib]

/-- The linear floor of the arctangent on `[0,1]`: `arctan z ≥ z/2`. -/
theorem arctan_ge_half_self {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    z / 2 ≤ Real.arctan z := by
  have hmono : MonotoneOn (fun w : ℝ => Real.arctan w - w / 2) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (Real.continuous_arctan.sub (continuous_id.div_const 2)).continuousOn
    · intro t _
      exact ((Real.differentiable_arctan t).sub
        ((differentiable_id.div_const 2) t)).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hd : deriv (fun w : ℝ => Real.arctan w - w / 2) t
          = 1 / (1 + t ^ 2) - 1 / 2 := by
        have ha := Real.hasDerivAt_arctan t
        have hb : HasDerivAt (fun w : ℝ => w / 2) (1 / 2) t := by
          simpa using (hasDerivAt_id t).div_const 2
        exact (ha.sub hb).deriv
      rw [hd]
      have h2 : 1 + t ^ 2 ≤ 2 := by nlinarith [ht.1.le, ht.2.le]
      have h3 : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have h4 := one_div_le_one_div_of_le h3 h2
      linarith
  have h := hmono (Set.left_mem_Icc.mpr zero_le_one) ⟨h0, h1⟩ h0
  simp only [Real.arctan_zero] at h
  linarith

/-- **The greedy accumulation lemma**: from a finite pool of nonnegative steps each of
size at most `ε` whose total reaches `T`, some sub-pool sums into `[T, T + ε]`. -/
theorem exists_subset_sum_between {f : ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (S : Finset ℕ) (T : ℝ), 0 ≤ T → (∀ p ∈ S, 0 ≤ f p) → (∀ p ∈ S, f p ≤ ε) →
      T ≤ ∑ p ∈ S, f p →
      ∃ S' ⊆ S, T ≤ ∑ p ∈ S', f p ∧ ∑ p ∈ S', f p ≤ T + ε := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro T hT0 _ _ htot
      simp only [Finset.sum_empty] at htot
      exact ⟨∅, Finset.Subset.refl _, by simp; linarith, by simp; linarith⟩
  | insert a S₀ ha ih =>
      intro T hT0 hf0 hfε htot
      rcases le_or_gt T (f a) with hTa | hTa
      · refine ⟨{a}, Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a S₀),
          ?_, ?_⟩
        · rw [Finset.sum_singleton]
          exact hTa
        · rw [Finset.sum_singleton]
          have := hfε a (Finset.mem_insert_self a S₀)
          linarith
      · have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a S₀)
        have htot' : T - f a ≤ ∑ p ∈ S₀, f p := by
          rw [Finset.sum_insert ha] at htot
          linarith
        obtain ⟨S₀', hsub, hlo, hhi⟩ := ih (T - f a) (by linarith)
          (fun p hp => hf0 p (Finset.mem_insert_of_mem hp))
          (fun p hp => hfε p (Finset.mem_insert_of_mem hp)) htot'
        have haS₀' : a ∉ S₀' := fun h => ha (hsub h)
        refine ⟨insert a S₀', Finset.insert_subset_insert a hsub, ?_, ?_⟩
        · rw [Finset.sum_insert haS₀']
          linarith
        · rw [Finset.sum_insert haS₀']
          linarith

/-! ### Elementary power bounds -/

/-- Negative powers are antitone in the base. -/
theorem rpow_neg_anti {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) :
    b ^ (-c) ≤ a ^ (-c) := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos (lt_of_lt_of_le ha hab)]
  apply Real.exp_le_exp.mpr
  have h := Real.log_le_log ha hab
  nlinarith

/-- The logarithm below any small power: `log t ≤ m·t^(1/m)` for `t ≥ 1`, `m ≥ 1`. -/
theorem log_le_mul_rpow {t : ℝ} (ht : 1 ≤ t) {m : ℝ} (hm : 1 ≤ m) :
    Real.log t ≤ m * t ^ (1 / m) := by
  have htpos : (0 : ℝ) < t := by linarith
  have h1 : Real.log (t ^ (1 / m)) = (1 / m) * Real.log t := Real.log_rpow htpos _
  have h2 : Real.log (t ^ (1 / m)) ≤ t ^ (1 / m) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t ^ (1 / m) by positivity)
    linarith
  have h3 : (1 / m) * Real.log t ≤ t ^ (1 / m) := h1 ▸ h2
  have hm0 : m ≠ 0 := by linarith
  calc Real.log t = m * ((1 / m) * Real.log t) := by
        rw [show m * ((1 / m) * Real.log t) = (m * (1 / m)) * Real.log t from by ring,
          mul_one_div_cancel hm0, one_mul]
    _ ≤ m * t ^ (1 / m) := mul_le_mul_of_nonneg_left h3 (by linarith)

/-! ### The reachability theorem -/

set_option maxHeartbeats 3200000 in
/-- **Full nonnegative reachability of the defect walk** (heights below `π/(2 log 2)`,
where the quarter-offset sine windows carry Chebyshev-divergent budgets).  For every
target `T ≥ 0` and tolerance `ε > 0` there is a finite prime set whose mirror defect
lands in `[T, T + ε]`: one late window holds enough uniformly-small positive steps, and
the greedy accumulation stops inside the tolerance band. -/
theorem anchorMirrorDefect_reachable_nonneg {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hτ : 0 < s.im) (hτ2 : s.im * (2 * Real.log 2) < Real.pi)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧
      T ≤ anchorMirrorDefect P s ∧ anchorMirrorDefect P s ≤ T + ε := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the window length, its exponential, and the leading constant
  set Lw : ℝ := Real.pi / (2 * s.im) with hLwdef
  have hLwpos : 0 < Lw := by positivity
  have hLwgt : Real.log 2 < Lw := by
    rw [hLwdef, lt_div_iff₀ (by positivity)]
    nlinarith
  set C : ℝ := Real.exp Lw with hCdef
  have hC2 : 2 < C := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp Lw := Real.exp_lt_exp.mpr hLwgt
  have hC0 : (0 : ℝ) < C := by linarith
  set A₀ : ℝ := C * Real.log 2 - Real.log 4 with hA₀def
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hA₀pos : 0 < A₀ := by
    rw [hA₀def, hlog4]
    nlinarith
  -- exponents
  set σ₀ : ℝ := min s.re (1 - s.re) with hσ₀def
  have hσ₀pos : 0 < σ₀ := lt_min h0 (by linarith)
  have hσ₀le : σ₀ ≤ s.re := min_le_left _ _
  have hσ₀le' : σ₀ ≤ 1 - s.re := min_le_right _ _
  set μ : ℝ := (1 - s.re) / 2 with hμdef
  have hμpos : 0 < μ := by
    rw [hμdef]
    linarith
  set m : ℝ := 2 / (1 - s.re) with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef, le_div_iff₀ (by linarith)]
    linarith
  have hminv : 1 / m = μ := by
    rw [hmdef, hμdef, one_div_div]
  -- the constants of the divergence bound
  set K : ℝ := Real.log 2 + 4 * Real.sqrt C + 8 * C ^ ((3 : ℝ) / 4) with hKdef
  have hKpos : 0 < K := by
    have h1 : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC0
    have h2 : (0 : ℝ) < C ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hC0 _
    rw [hKdef]
    positivity
  set D : ℝ := Real.log C + m with hDdef
  have hDpos : 0 < D := by
    have := Real.log_pos (by linarith : 1 < C)
    rw [hDdef]
    linarith
  set c₉ : ℝ := A₀ / (2 * D) * (C ^ (-s.re) * (Real.sqrt 2 / 8)) with hc₉def
  have hc₉pos : 0 < c₉ := by
    have h1 : (0 : ℝ) < C ^ (-s.re) := Real.rpow_pos_of_pos hC0 _
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [hc₉def]
    positivity
  -- the size thresholds
  set δ₁ : ℝ := min (1 / 2) (ε / 4) with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  set X₁ : ℝ := δ₁ ^ (-(1 / σ₀)) with hX₁def
  set X₂ : ℝ := (2 * K / A₀ + 1) ^ ((4 : ℝ)) with hX₂def
  set X₃ : ℝ := (T / c₉ + 1) ^ (1 / μ) with hX₃def
  set Xm : ℝ := max 2 (max X₁ (max X₂ X₃)) with hXmdef
  have hXmpos : (0 : ℝ) < Xm := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  -- choose the window index
  obtain ⟨k, hk⟩ := exists_nat_gt (s.im * Real.log Xm / (2 * Real.pi))
  set b : ℝ := (2 * Real.pi * (k : ℝ) + Real.pi / 4) / s.im with hbdef
  set x : ℝ := Real.exp b with hxdef
  set y : ℝ := C * x with hydef
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  have hxXm : Xm ≤ x := by
    have hblog : Real.log Xm ≤ b := by
      rw [div_lt_iff₀ h2pi] at hk
      rw [hbdef, le_div_iff₀ hτ]
      nlinarith
    calc Xm = Real.exp (Real.log Xm) := (Real.exp_log hXmpos).symm
      _ ≤ Real.exp b := Real.exp_le_exp.mpr hblog
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hxXm
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hxy : x ≤ y := by
    rw [hydef]
    nlinarith
  have hy1 : (1 : ℝ) ≤ y := le_trans hx1 hxy
  have hy0 : (0 : ℝ) < y := by linarith
  have hyexp : y = Real.exp (b + Lw) := by
    rw [hydef, hxdef, hCdef, ← Real.exp_add, add_comm]
  -- the step bounds on the window
  have hτb : s.im * b = 2 * Real.pi * (k : ℝ) + Real.pi / 4 := by
    rw [hbdef, mul_comm, div_mul_cancel₀ _ hτ.ne']
  have hhalf : s.im * Lw = Real.pi / 2 := by
    rw [hLwdef, mul_comm (2 : ℝ) s.im, ← div_div, ← mul_div_assoc,
      mul_comm s.im (Real.pi / s.im), div_mul_cancel₀ _ hτ.ne']
  have hwindow : ∀ p ∈ windowPrimes x y, Nat.Prime p ∧
      Real.sqrt 2 / 2 ≤ Real.sin (s.im * Real.log p) ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
    intro p hp
    obtain ⟨hprime, hlt, hle⟩ := (mem_windowPrimes hx0.le hy0.le).mp hp
    refine ⟨hprime, ?_, hlt, hle⟩
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hlogp1 : b < Real.log p := by
      rw [hxdef] at hlt
      have := Real.exp_log hppos
      calc b = Real.log (Real.exp b) := (Real.log_exp b).symm
        _ < Real.log p := Real.log_lt_log (Real.exp_pos b) hlt
    have hlogp2 : Real.log p ≤ b + Lw := by
      rw [hyexp] at hle
      calc Real.log p ≤ Real.log (Real.exp (b + Lw)) :=
            Real.log_le_log hppos hle
        _ = b + Lw := Real.log_exp _
    have h1 : 2 * Real.pi * (k : ℝ) + Real.pi / 4 < s.im * Real.log p := by
      have := mul_lt_mul_of_pos_left hlogp1 hτ
      linarith
    have h2 : s.im * Real.log p ≤ 2 * Real.pi * (k : ℝ) + 3 * Real.pi / 4 := by
      have h := mul_le_mul_of_nonneg_left hlogp2 hτ.le
      rw [mul_add, hτb, hhalf] at h
      linarith
    have hper : Real.sin (s.im * Real.log p)
        = Real.sin (s.im * Real.log p - (k : ℤ) * (2 * Real.pi)) :=
      (Real.sin_sub_int_mul_two_pi _ _).symm
    rw [hper]
    apply sin_ge_sqrt_two_div_two
    · push_cast
      linarith
    · push_cast
      linarith
  -- nonnegativity and ceiling of the steps
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hstep0 : ∀ p ∈ windowPrimes x y, 0 ≤ mirrorTiltIncrement p s := by
    intro p hp
    obtain ⟨hprime, hsin, -, -⟩ := hwindow p hp
    exact (mirrorTiltIncrement_pos hprime.two_le h0 h1
      (lt_of_lt_of_le (by positivity) hsin)).le
  have hX₁pos : (0 : ℝ) < X₁ := Real.rpow_pos_of_pos hδ₁pos _
  have hu_x : x ^ (-σ₀) ≤ δ₁ := by
    have hX₁x : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxXm
    have h := rpow_neg_anti hX₁pos hX₁x hσ₀pos.le
    have hXpow : X₁ ^ (-σ₀) = δ₁ := by
      rw [hX₁def, ← Real.rpow_mul hδ₁pos.le,
        show -(1 / σ₀) * -σ₀ = σ₀ / σ₀ from by ring, div_self hσ₀pos.ne',
        Real.rpow_one]
    linarith [hXpow ▸ h]
  have hstepε : ∀ p ∈ windowPrimes x y, mirrorTiltIncrement p s ≤ ε := by
    intro p hp
    obtain ⟨hprime, -, hlt, -⟩ := hwindow p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have habs := abs_mirrorTiltIncrement_le hprime.two_le hσ₀pos hσ₀le hσ₀le'
    have hup : (p : ℝ) ^ (-σ₀) ≤ x ^ (-σ₀) := rpow_neg_anti hx0 hlt.le hσ₀pos.le
    have hupos : (0 : ℝ) < (p : ℝ) ^ (-σ₀) := Real.rpow_pos_of_pos hppos _
    have hux12 : x ^ (-σ₀) ≤ 1 / 2 := le_trans hu_x (min_le_left _ _)
    have huxε4 : x ^ (-σ₀) ≤ ε / 4 := le_trans hu_x (min_le_right _ _)
    have hmono2 : 2 * ((p : ℝ) ^ (-σ₀) / (1 - (p : ℝ) ^ (-σ₀)))
        ≤ 2 * x ^ (-σ₀) / (1 - x ^ (-σ₀)) := by
      have hden1 : (0 : ℝ) < 1 - x ^ (-σ₀) := by linarith
      have hden2 : (0 : ℝ) < 1 - (p : ℝ) ^ (-σ₀) := by linarith
      rw [← mul_div_assoc, div_le_div_iff₀ hden2 hden1]
      nlinarith
    have hfinal : 2 * x ^ (-σ₀) / (1 - x ^ (-σ₀)) ≤ 4 * x ^ (-σ₀) := by
      have hden1 : (0 : ℝ) < 1 - x ^ (-σ₀) := by linarith
      rw [div_le_iff₀ hden1]
      have hux0 : (0 : ℝ) ≤ x ^ (-σ₀) := (Real.rpow_pos_of_pos hx0 _).le
      nlinarith
    have hchain := le_trans (le_trans (le_abs_self _) habs) (le_trans hmono2 hfinal)
    linarith
  -- the per-prime step floor on the window
  have hstepfloor : ∀ p ∈ windowPrimes x y,
      y ^ (-s.re) * Real.sqrt 2 / 8 ≤ mirrorTiltIncrement p s := by
    intro p hp
    obtain ⟨hprime, hsin, hlt, hle⟩ := hwindow p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hge := mirrorTiltIncrement_ge hprime.two_le h0 h1
      (lt_of_lt_of_le (by positivity) hsin)
    have hpy : y ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) := rpow_neg_anti hppos hle h0.le
    have hy0' : (0 : ℝ) ≤ y ^ (-s.re) := (Real.rpow_pos_of_pos hy0 _).le
    have hz : y ^ (-s.re) * (Real.sqrt 2 / 2) / 2
        ≤ (p : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log p) / 2 := by
      have hmul := mul_le_mul hpy hsin (by positivity)
        (Real.rpow_pos_of_pos hppos _).le
      linarith
    have hz1 : y ^ (-s.re) * (Real.sqrt 2 / 2) / 2 ≤ 1 := by
      have hy1' : y ^ (-s.re) ≤ 1 := by
        have h := rpow_neg_anti one_pos hy1 h0.le
        rwa [Real.one_rpow] at h
      have hs2 : Real.sqrt 2 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have hz0 : (0 : ℝ) ≤ y ^ (-s.re) * (Real.sqrt 2 / 2) / 2 := by positivity
    have hhalf' := arctan_ge_half_self hz0 hz1
    have harctan := Real.arctan_mono hz
    calc y ^ (-s.re) * Real.sqrt 2 / 8
        = y ^ (-s.re) * (Real.sqrt 2 / 2) / 2 / 2 := by ring
      _ ≤ Real.arctan (y ^ (-s.re) * (Real.sqrt 2 / 2) / 2) := hhalf'
      _ ≤ Real.arctan ((p : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log p) / 2) := harctan
      _ ≤ mirrorTiltIncrement p s := hge
  -- the window mass beats (A₀/2)·x
  have hcard := windowPrimes_card_ge hx1 hxy
  have hy4 : (4 : ℝ) < y := by
    rw [hydef]
    nlinarith
  have hmass2 : A₀ / 2 * x
      ≤ (y - 1) * Real.log 2 - Real.log (y + 2) - 2 * Real.sqrt y * Real.log y
        - Real.log 4 * x := by
    have hlog_y2 : Real.log (y + 2) ≤ 4 * Real.sqrt y := by
      have hb1 : Real.log (y + 2) ≤ 2 * (y + 2) ^ ((1 : ℝ) / 2) :=
        log_le_mul_rpow (by linarith) (by norm_num)
      have hb2 : (y + 2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (y + 2) :=
        (Real.sqrt_eq_rpow _).symm
      have hb3 : Real.sqrt (y + 2) ≤ Real.sqrt (4 * y) :=
        Real.sqrt_le_sqrt (by linarith)
      have hb4 : Real.sqrt (4 * y) = 2 * Real.sqrt y := by
        rw [show (4 : ℝ) * y = 2 ^ 2 * y by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      calc Real.log (y + 2) ≤ 2 * (y + 2) ^ ((1 : ℝ) / 2) := hb1
        _ = 2 * Real.sqrt (y + 2) := by rw [hb2]
        _ ≤ 2 * (2 * Real.sqrt y) := by
            rw [← hb4]
            linarith [hb3]
        _ = 4 * Real.sqrt y := by ring
    have hsqy : 2 * Real.sqrt y * Real.log y ≤ 8 * y ^ ((3 : ℝ) / 4) := by
      have hb1 : Real.log y ≤ 4 * y ^ ((1 : ℝ) / 4) := log_le_mul_rpow hy1 (by norm_num)
      have hb2 : y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 4) = y ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hy0]
        norm_num
      have hb3 : Real.sqrt y = y ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow y
      calc 2 * Real.sqrt y * Real.log y
          ≤ 2 * Real.sqrt y * (4 * y ^ ((1 : ℝ) / 4)) := by
            apply mul_le_mul_of_nonneg_left hb1 (by positivity)
        _ = 8 * (y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 4)) := by rw [hb3]; ring
        _ = 8 * y ^ ((3 : ℝ) / 4) := by rw [hb2]
    have hsqrtCx : Real.sqrt y = Real.sqrt C * Real.sqrt x := by
      rw [hydef, Real.sqrt_mul hC0.le]
    have hCx34 : y ^ ((3 : ℝ) / 4) = C ^ ((3 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) := by
      rw [hydef, Real.mul_rpow hC0.le hx0.le]
    have hx12 : Real.sqrt x ≤ x ^ ((3 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hone : (1 : ℝ) ≤ x ^ ((3 : ℝ) / 4) := by
      calc (1 : ℝ) = 1 ^ ((3 : ℝ) / 4) := (Real.one_rpow _).symm
        _ ≤ x ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
    have hKbound : Real.log 2 + 4 * Real.sqrt y + 8 * y ^ ((3 : ℝ) / 4)
        ≤ K * x ^ ((3 : ℝ) / 4) := by
      rw [hsqrtCx, hCx34, hKdef]
      have hsC : (0 : ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg C
      have hC34 : (0 : ℝ) ≤ C ^ ((3 : ℝ) / 4) := (Real.rpow_pos_of_pos hC0 _).le
      nlinarith [hx12, hone, (Real.rpow_pos_of_pos hx0 ((3 : ℝ) / 4)).le,
        Real.sqrt_nonneg x]
    have hX₂x : X₂ ≤ x :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) hxXm
    have hx14 : 2 * K / A₀ ≤ x ^ ((1 : ℝ) / 4) := by
      have hbase : (0 : ℝ) ≤ 2 * K / A₀ + 1 := by positivity
      have hb1 : X₂ ^ ((1 : ℝ) / 4) ≤ x ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by rw [hX₂def]; positivity) hX₂x (by norm_num)
      have hb2 : X₂ ^ ((1 : ℝ) / 4) = 2 * K / A₀ + 1 := by
        rw [hX₂def, ← Real.rpow_mul hbase]
        norm_num
      linarith [hb2 ▸ hb1]
    have hKx : K * x ^ ((3 : ℝ) / 4) ≤ A₀ / 2 * x := by
      have hb1 : K ≤ A₀ / 2 * x ^ ((1 : ℝ) / 4) := by
        rw [div_le_iff₀ hA₀pos] at hx14
        nlinarith
      have hb2 : x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) = x := by
        rw [← Real.rpow_add hx0]
        norm_num
      calc K * x ^ ((3 : ℝ) / 4)
          ≤ A₀ / 2 * x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right hb1 (Real.rpow_pos_of_pos hx0 _).le
        _ = A₀ / 2 * x := by rw [mul_assoc, hb2]
    have hexpand : (y - 1) * Real.log 2 - Real.log 4 * x = A₀ * x - Real.log 2 := by
      rw [hydef, hA₀def]
      ring
    linarith
  -- count and total budget
  have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hcount : A₀ / 2 * x / Real.log y ≤ ((windowPrimes x y).card : ℝ) := by
    rw [div_le_iff₀ hlogy_pos]
    exact le_trans hmass2 hcard
  have hsum_ge : ((windowPrimes x y).card : ℝ) * (y ^ (-s.re) * Real.sqrt 2 / 8)
      ≤ ∑ p ∈ windowPrimes x y, mirrorTiltIncrement p s := by
    have h := Finset.card_nsmul_le_sum (windowPrimes x y)
      (fun p => mirrorTiltIncrement p s) (y ^ (-s.re) * Real.sqrt 2 / 8) hstepfloor
    rwa [nsmul_eq_mul] at h
  have hxμ1 : (1 : ℝ) ≤ x ^ μ := by
    calc (1 : ℝ) = 1 ^ μ := (Real.one_rpow _).symm
      _ ≤ x ^ μ := Real.rpow_le_rpow (by norm_num) hx1 hμpos.le
  have hlogy_le : Real.log y ≤ D * x ^ μ := by
    have hb1 : Real.log y = Real.log C + Real.log x := by
      rw [hydef, Real.log_mul hC0.ne' hx0.ne']
    have hb2 : Real.log x ≤ m * x ^ μ := by
      have h := log_le_mul_rpow hx1 hm1
      rwa [hminv] at h
    have hb3 : Real.log C ≤ Real.log C * x ^ μ :=
      le_mul_of_one_le_right (Real.log_pos (by linarith)).le hxμ1
    have hb4 : D * x ^ μ = Real.log C * x ^ μ + m * x ^ μ := by
      rw [hDdef]
      ring
    linarith
  have htotal : T ≤ ∑ p ∈ windowPrimes x y, mirrorTiltIncrement p s := by
    have hxμpos : (0 : ℝ) < x ^ μ := Real.rpow_pos_of_pos hx0 _
    have hy_rpow : y ^ (-s.re) = C ^ (-s.re) * x ^ (-s.re) := by
      rw [hydef, Real.mul_rpow hC0.le hx0.le]
    have hxx : x * x ^ (-s.re) = x ^ μ * x ^ μ := by
      rw [show x * x ^ (-s.re) = x ^ (1 : ℝ) * x ^ (-s.re) from by rw [Real.rpow_one],
        ← Real.rpow_add hx0, ← Real.rpow_add hx0,
        show (1 : ℝ) + -s.re = μ + μ from by rw [hμdef]; ring]
    have hkey : x ^ μ * Real.log y ≤ x * x ^ (-s.re) * D := by
      rw [hxx]
      have h := mul_le_mul_of_nonneg_left hlogy_le hxμpos.le
      nlinarith
    have hfrac : x ^ μ / D ≤ x * x ^ (-s.re) / Real.log y := by
      rw [div_le_div_iff₀ hDpos hlogy_pos]
      linarith
    have hstep1 : c₉ * x ^ μ
        ≤ A₀ / 2 * x / Real.log y * (y ^ (-s.re) * Real.sqrt 2 / 8) := by
      rw [hy_rpow, hc₉def]
      have hE0 : (0 : ℝ) ≤ A₀ * C ^ (-s.re) * Real.sqrt 2 / 16 := by
        have := (Real.rpow_pos_of_pos hC0 (-s.re)).le
        positivity
      calc A₀ / (2 * D) * (C ^ (-s.re) * (Real.sqrt 2 / 8)) * x ^ μ
          = A₀ * C ^ (-s.re) * Real.sqrt 2 / 16 * (x ^ μ / D) := by ring
        _ ≤ A₀ * C ^ (-s.re) * Real.sqrt 2 / 16 * (x * x ^ (-s.re) / Real.log y) :=
            mul_le_mul_of_nonneg_left hfrac hE0
        _ = A₀ / 2 * x / Real.log y * (C ^ (-s.re) * x ^ (-s.re) * Real.sqrt 2 / 8) := by
            ring
    have hX₃x : X₃ ≤ x :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right _ _)) hxXm
    have hTc : T / c₉ ≤ x ^ μ := by
      have hbase : (0 : ℝ) ≤ T / c₉ + 1 := by positivity
      have hb1 : X₃ ^ μ ≤ x ^ μ :=
        Real.rpow_le_rpow (by rw [hX₃def]; positivity) hX₃x hμpos.le
      have hb2 : X₃ ^ μ = T / c₉ + 1 := by
        rw [hX₃def, ← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ hμpos.ne',
          Real.rpow_one]
      linarith [hb2 ▸ hb1]
    have hxμT : T ≤ c₉ * x ^ μ := by
      have h := (div_le_iff₀ hc₉pos).mp hTc
      linarith
    have hcount' := mul_le_mul_of_nonneg_right hcount
      (show (0 : ℝ) ≤ y ^ (-s.re) * Real.sqrt 2 / 8 by positivity)
    linarith
  -- greedy accumulation inside the window
  obtain ⟨P, hPsub, hlo, hhi⟩ := exists_subset_sum_between hε.le (windowPrimes x y) T hT
    hstep0 hstepε htotal
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p hp
    exact ((mem_windowPrimes hx0.le hy0.le).mp (hPsub hp)).1
  · rw [anchorMirrorDefect_eq_sum]
    exact hlo
  · rw [anchorMirrorDefect_eq_sum]
    exact hhi

end RHTower
