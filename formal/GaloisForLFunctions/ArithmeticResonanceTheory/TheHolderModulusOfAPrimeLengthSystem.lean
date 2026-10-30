import GaloisForLFunctions.ArithmeticResonanceTheory.IntegralityForbidsSuperConformalDistortion
import GaloisForLFunctions.HTGeometry.SymbolicShiftSpace

/-!
# The Hölder modulus of a prime-length system

A one-sided subshift with roof `φ` is a **prime-length system** (`IsPrimeLength`) when every
admissible periodic point `x` of least period `L` has `e^{φ^L(x)}` prime: the primitive periodic
orbits have lengths `log p`. A realization of `ζ` as the dynamical zeta function
`exp Σ_n n⁻¹ Σ_{σⁿx = x} e^{−s φⁿ(x)}` is such a system.

**Cycle families.** For a cycle `u` (period point `y = u^∞`, length `L`) and a re-entry word `v`,
the periodic points `x n = (u^n v)^∞` of periods `P n = nL + |v|` shadow `y` for `(n + 1) L`
symbols, and `x (n + 1)`, after one turn around `u`, shadows `x n` for `P n + nL` symbols
(`IsCycleFamily`, `isCycleFamily_familyPoint`). For a `(C, θ)`-Hölder roof the bounded-distortion
estimate gives the one-step law

  `|φ^{P (n+1)}(x (n+1)) − φ^L(y) − φ^{P n}(x n)| ≤ 2C θ^{nL} / (1 − θ)`

(`abs_familyStep_le`), i.e. `p (n + 1) = a · p n · e^{δ n}` with `|δ n| = O((θ^L)^n)`, where
`p n = e^{φ^{P n}(x n)}` and `a = e^{φ^L(y)}`.

**Theorem** (`one_le_mul_pow_of_cycleFamily`). If `a ≥ 2` is an integer and the `p n` are eventually
prime, then `a · θ^L ≥ 1`. Otherwise the family is super-conformal and integrality forces
`p (n + 1) = a · p n` (`not_eventually_prime_of_ratio`).

**Fixed-point law** (`one_le_exp_mul_of_isPrimeLength`). In a prime-length system with Hölder
modulus `θ`, every fixed point `a^∞` that can be left to a symbol `b ≠ a` and re-entered satisfies
`θ · e^{φ(a^∞)} ≥ 1`: the roof cannot be smoother than its own size at the fixed point.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry.Symbolic

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {k : ℕ}

/-! ## Cycle families -/

/-- **Cycle family** of a cycle point `y` of period `L`: periodic data `x n` of periods
`P n` with `P (n + 1) = L + P n`, following `y` for `(n + 1) L` symbols, and such that `x (n + 1)`
shifted once around the cycle follows `x n` for `P n + n L` symbols. -/
structure IsCycleFamily (y : ℕ → Fin k) (L : ℕ) (x : ℕ → ℕ → Fin k) (P : ℕ → ℕ) : Prop where
  period_succ : ∀ n, P (n + 1) = L + P n
  agree_cycle : ∀ n, Agree (L + n * L) (x (n + 1)) y
  agree_shift : ∀ n, Agree (P n + n * L) (shiftBy L (x (n + 1))) (x n)

/-- The periodic point `u^∞` of the word `u 0, …, u (L − 1)`. -/
def cyclePoint (u : ℕ → Fin k) (L : ℕ) : ℕ → Fin k := fun i => u (i % L)

/-- The periodic point `(u^n v)^∞`: `n` copies of `u` (length `L`) followed by `v` (length `L'`). -/
def familyPoint (u v : ℕ → Fin k) (L L' n : ℕ) : ℕ → Fin k := fun i =>
  if i % (n * L + L') < n * L then u (i % (n * L + L') % L) else v (i % (n * L + L') - n * L)

/-- The words `u^n v` form a cycle family of `u^∞`. -/
theorem isCycleFamily_familyPoint (u v : ℕ → Fin k) (L L' : ℕ) :
    IsCycleFamily (cyclePoint u L) L (familyPoint u v L L') (fun n => n * L + L') := by
  refine ⟨fun n => by ring, fun n i hi => ?_, fun n i hi => ?_⟩
  · simp only [familyPoint, cyclePoint, add_one_mul]
    rw [Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  · simp only [familyPoint, shiftBy_apply, add_one_mul]
    generalize n * L = N at *
    by_cases hi1 : i < N + L'
    · rw [Nat.mod_eq_of_lt (show i + L < N + L + L' by omega), Nat.mod_eq_of_lt hi1]
      by_cases hiN : i < N
      · rw [if_pos (by omega), if_pos hiN, Nat.add_mod_right]
      · rw [if_neg (by omega), if_neg hiN]
        congr 1; omega
    · rw [Nat.mod_eq_sub_mod (show N + L + L' ≤ i + L by omega),
        Nat.mod_eq_of_lt (show i + L - (N + L + L') < N + L + L' by omega),
        Nat.mod_eq_sub_mod (show N + L' ≤ i by omega),
        Nat.mod_eq_of_lt (show i - (N + L') < N + L' by omega),
        if_pos (by omega), if_pos (by omega)]
      congr 2; omega

/-! ## The one-step distortion law -/

section Distortion

variable {A : Fin k → Fin k → Prop} {φ : (ℕ → Fin k) → ℝ} {C θ : ℝ}

/-- **One-step law.** Along a cycle family of a `(C, θ)`-Hölder roof,
`|φ^{P (n+1)}(x (n+1)) − φ^L(y) − φ^{P n}(x n)| ≤ 2 C θ^{nL}/(1 − θ)`. -/
theorem abs_familyStep_le (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    {y : ℕ → Fin k} {L : ℕ} {x : ℕ → ℕ → Fin k} {P : ℕ → ℕ} (hF : IsCycleFamily y L x P)
    (hy : IsAdmissible A y) (hx : ∀ n, IsAdmissible A (x n)) (n : ℕ) :
    |birkhoff φ (P (n + 1)) (x (n + 1)) - birkhoff φ L y - birkhoff φ (P n) (x n)| ≤
      2 * C / (1 - θ) * (θ ^ L) ^ n := by
  -- split one turn around the cycle off the period of `x (n + 1)`
  rw [hF.period_succ, birkhoff_add]
  have h1 := abs_birkhoff_sub_le hθ0 hθ1 hh L (n * L) (hx (n + 1)) hy (hF.agree_cycle n)
  have h2 := abs_birkhoff_sub_le hθ0 hθ1 hh (P n) (n * L) ((hx (n + 1)).shiftBy L) (hx n)
    (hF.agree_shift n)
  have hpow : θ ^ (n * L) = (θ ^ L) ^ n := by rw [← pow_mul, Nat.mul_comm]
  calc |birkhoff φ L (x (n + 1)) + birkhoff φ (P n) (shiftBy L (x (n + 1))) - birkhoff φ L y -
        birkhoff φ (P n) (x n)|
      = |(birkhoff φ L (x (n + 1)) - birkhoff φ L y) +
          (birkhoff φ (P n) (shiftBy L (x (n + 1))) - birkhoff φ (P n) (x n))| := by ring_nf
    _ ≤ |birkhoff φ L (x (n + 1)) - birkhoff φ L y| +
          |birkhoff φ (P n) (shiftBy L (x (n + 1))) - birkhoff φ (P n) (x n)| := abs_add_le _ _
    _ ≤ C * θ ^ (n * L) / (1 - θ) + C * θ ^ (n * L) / (1 - θ) := add_le_add h1 h2
    _ = 2 * C / (1 - θ) * (θ ^ L) ^ n := by rw [hpow]; ring

/-- **The cycle law.** If the exponentiated cycle length `a = e^{φ^L(y)}` is an integer `≥ 2` and
the exponentiated lengths `p n = e^{φ^{P n}(x n)}` of a cycle family are eventually prime, then
`a · θ^L ≥ 1`. -/
theorem one_le_mul_pow_of_cycleFamily (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    {y : ℕ → Fin k} {L : ℕ} {x : ℕ → ℕ → Fin k} {P : ℕ → ℕ} (hF : IsCycleFamily y L x P)
    (hy : IsAdmissible A y) (hx : ∀ n, IsAdmissible A (x n))
    {a : ℕ} (ha : 2 ≤ a) (hya : Real.exp (birkhoff φ L y) = a)
    {p : ℕ → ℕ} (hp : ∀ n, Real.exp (birkhoff φ (P n) (x n)) = p n)
    (hprime : ∀ᶠ n in atTop, (p n).Prime) : 1 ≤ a * θ ^ L := by
  by_contra hlt
  rw [not_le] at hlt
  set δ : ℕ → ℝ := fun n =>
    birkhoff φ (P (n + 1)) (x (n + 1)) - birkhoff φ L y - birkhoff φ (P n) (x n) with hδ
  refine not_eventually_prime_of_ratio ha (pow_nonneg hθ0 L) hlt
    (fun n => abs_familyStep_le hθ0 hθ1 hh hF hy hx n) (fun n => ?_) hprime
  rw [← hp (n + 1), ← hp n, ← hya, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Distortion

/-! ## Prime-length systems and the fixed-point law -/

/-- **Prime-length system.** Every admissible periodic point `x` of least period `L > 0` has
`e^{φ^L(x)}` prime. -/
def IsPrimeLength (A : Fin k → Fin k → Prop) (φ : (ℕ → Fin k) → ℝ) : Prop :=
  ∀ x : ℕ → Fin k, IsAdmissible A x → ∀ L, 0 < L → Function.minimalPeriod (shiftBy 1) x = L →
    ∃ q : ℕ, q.Prime ∧ Real.exp (birkhoff φ L x) = q

theorem shiftBy_one_iterate (m : ℕ) (x : ℕ → Fin k) : (shiftBy 1)^[m] x = shiftBy m x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, shiftBy_shiftBy, Nat.add_comm]

/-- The least period of a sequence periodic with period `P > 0` whose periods are all multiples
of `P`. -/
theorem minimalPeriod_eq_of_dvd {x : ℕ → Fin k} {P : ℕ} (hP : 0 < P) (hper : shiftBy P x = x)
    (hdvd : ∀ m, 0 < m → shiftBy m x = x → P ∣ m) :
    Function.minimalPeriod (shiftBy 1) x = P := by
  have hpt : Function.IsPeriodicPt (shiftBy 1) P x := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, shiftBy_one_iterate, hper]
  have hpos := hpt.minimalPeriod_pos hP
  refine Nat.dvd_antisymm (hpt.minimalPeriod_dvd) (hdvd _ hpos ?_)
  have := Function.isPeriodicPt_minimalPeriod (shiftBy 1) x
  rwa [Function.IsPeriodicPt, Function.IsFixedPt, shiftBy_one_iterate] at this

/-- The fixed-point family `(a^n b a)^∞` — one `b` per period `n + 2`, at the residue `n`. -/
def fixedPointFamily (a b : Fin k) (n : ℕ) : ℕ → Fin k := fun i => if i % (n + 2) = n then b else a

theorem isCycleFamily_fixedPointFamily (a b : Fin k) :
    IsCycleFamily (fun _ => a) 1 (fixedPointFamily a b) (fun n => n + 2) := by
  refine ⟨fun n => by ring, fun n i hi => ?_, fun n i hi => ?_⟩
  · simp only [fixedPointFamily]
    rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
  · simp only [fixedPointFamily, shiftBy_apply]
    by_cases hi1 : i < n + 2
    · rw [Nat.mod_eq_of_lt (show i + 1 < n + 1 + 2 by omega), Nat.mod_eq_of_lt hi1]
      by_cases hin : i = n
      · rw [if_pos (by omega), if_pos hin]
      · rw [if_neg (by omega), if_neg hin]
    · rw [Nat.mod_eq_sub_mod (show n + 1 + 2 ≤ i + 1 by omega),
        Nat.mod_eq_of_lt (show i + 1 - (n + 1 + 2) < n + 1 + 2 by omega),
        Nat.mod_eq_sub_mod (show n + 2 ≤ i by omega),
        Nat.mod_eq_of_lt (show i - (n + 2) < n + 2 by omega),
        if_neg (by omega), if_neg (by omega)]

theorem fixedPointFamily_eq_b_iff {a b : Fin k} (hab : a ≠ b) (n i : ℕ) :
    fixedPointFamily a b n i = b ↔ i % (n + 2) = n := by
  simp only [fixedPointFamily]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' hab, fun h' => absurd h' h⟩

theorem minimalPeriod_fixedPointFamily {a b : Fin k} (hab : a ≠ b) (n : ℕ) :
    Function.minimalPeriod (shiftBy 1) (fixedPointFamily a b n) = n + 2 := by
  refine minimalPeriod_eq_of_dvd (by omega) ?_ fun m _ hm => ?_
  · funext i
    simp [fixedPointFamily, Nat.add_mod_right]
  · -- the unique `b` of a period sits at residue `n`
    have h := congrFun hm n
    rw [shiftBy_apply] at h
    have hb : fixedPointFamily a b n n = b :=
      (fixedPointFamily_eq_b_iff hab n n).mpr (Nat.mod_eq_of_lt (by omega))
    rw [hb, fixedPointFamily_eq_b_iff hab] at h
    have hmod : n + m ≡ n + 0 [MOD n + 2] := by
      rw [Nat.ModEq, h, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' n hmod)

theorem isAdmissible_fixedPointFamily {A : Fin k → Fin k → Prop} {a b : Fin k} (haa : A a a)
    (hab' : A a b) (hba : A b a) (n : ℕ) :
    IsAdmissible A (fixedPointFamily a b n) := by
  intro i
  -- after a `b` comes an `a`
  by_cases hi : i % (n + 2) = n
  · have hnext : (i + 1) % (n + 2) = n + 1 := by
      rw [Nat.add_mod, hi, Nat.mod_eq_of_lt (show 1 < n + 2 by omega),
        Nat.mod_eq_of_lt (show n + 1 < n + 2 by omega)]
    simp only [fixedPointFamily, if_pos hi, if_neg (show (i + 1) % (n + 2) ≠ n by omega)]
    exact hba
  · simp only [fixedPointFamily, if_neg hi]
    split_ifs
    · exact hab'
    · exact haa

variable {A : Fin k → Fin k → Prop} {φ : (ℕ → Fin k) → ℝ} {C θ : ℝ}

/-- **The fixed-point law.** In a `(C, θ)`-Hölder prime-length system, a fixed point `a^∞` that can
be left to a symbol `b ≠ a` and re-entered (`A a a`, `A a b`, `A b a`) satisfies
`θ · e^{φ(a^∞)} ≥ 1`. -/
theorem one_le_exp_mul_of_isPrimeLength (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    (hPL : IsPrimeLength A φ) {a b : Fin k} (hab : a ≠ b) (haa : A a a) (hab' : A a b)
    (hba : A b a) : 1 ≤ Real.exp (φ (fun _ => a)) * θ := by
  have hya : IsAdmissible A (fun _ : ℕ => a) := fun _ => haa
  -- the fixed point has least period `1`
  have hmin1 : Function.minimalPeriod (shiftBy 1) (fun _ : ℕ => a) = 1 :=
    minimalPeriod_eq_of_dvd one_pos rfl fun m _ _ => one_dvd m
  obtain ⟨q, hq, hqa⟩ := hPL _ hya 1 one_pos hmin1
  have hb1 : birkhoff φ 1 (fun _ : ℕ => a) = φ (fun _ => a) := by simp [birkhoff]
  rw [hb1] at hqa
  -- the family members have prime lengths over their least periods `n + 2`
  have hfam := fun n => isAdmissible_fixedPointFamily haa hab' hba n
  choose p hp using fun n => hPL _ (hfam n) (n + 2) (by omega)
    (minimalPeriod_fixedPointFamily hab n)
  have h := one_le_mul_pow_of_cycleFamily hθ0 hθ1 hh (isCycleFamily_fixedPointFamily a b) hya
    hfam hq.two_le (by rw [hb1, hqa]) (fun n => (hp n).2) (Eventually.of_forall fun n => (hp n).1)
  rw [pow_one, ← hqa] at h
  exact h

end GaloisForLFunctions.ArithmeticResonanceTheory
