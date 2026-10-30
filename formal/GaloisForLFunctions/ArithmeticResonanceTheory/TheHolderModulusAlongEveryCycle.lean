import GaloisForLFunctions.ArithmeticResonanceTheory.ARealizationOfZetaIsPrimeLength

/-!
# The Hölder modulus along every cycle

A **return word** at a symbol `a` (`IsReturnWord`) starts with `a`, contains no other `a`, is
admissible and closes back to `a`. Two different return words `u`, `v` at the same symbol produce
the cycle family `(uⁿv)^∞`, and every member is a primitive periodic orbit
(`minimalPeriod_familyPoint`): the occurrences of `a` in one period sit at `0, |u|, …, n|u|`, so a
smaller period would shift the block before `v` onto `v`, forcing first `|u| = |v|` (the next
occurrence of `a` must land on an occurrence of `a`) and then `u = v` letter by letter.

**Theorem** (`one_le_exp_mul_pow_of_returnWords`). In a `θ`-Hölder prime-length system, every
cycle `u` with a second return word at its base symbol satisfies

  `θ^{|u|} · e^{φ^{|u|}(u^∞)} ≥ 1`,

i.e. `θ ≥ p_u^{−1/|u|}` where `p_u` is the prime of the cycle: the roof cannot be smoother than
the geometric mean of its own contraction along any re-enterable cycle. The fixed-point law
(`one_le_exp_mul_of_isPrimeLength`) is the case `|u| = 1`.

**Corollary** (`one_le_exp_mul_pow_of_holderRealization`). For every Hölder realization of `ζ` on a
subshift of finite type this holds along every re-enterable cycle; it is the price of the zero-free
strip such a realization would give.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry.Symbolic

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {k : ℕ} {A : Fin k → Fin k → Prop}

/-- A **return word** at `a`: it starts with `a`, contains no other `a`, is admissible and closes
back to `a`. -/
structure IsReturnWord (A : Fin k → Fin k → Prop) (a : Fin k) (u : ℕ → Fin k) (L : ℕ) : Prop where
  pos : 0 < L
  start : u 0 = a
  avoid : ∀ i, 0 < i → i < L → u i ≠ a
  adm_in : ∀ i, i + 1 < L → A (u i) (u (i + 1))
  adm_close : A (u (L - 1)) a

/-- `(i + 1) % P` is `i % P + 1` or wraps to `0`. -/
theorem succ_mod_eq_ite {P : ℕ} (hP : 0 < P) (i : ℕ) :
    (i + 1) % P = if i % P + 1 < P then i % P + 1 else 0 := by
  have hlt := Nat.mod_lt i hP
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show i % P + 1 = P by omega, Nat.mod_self]
  · have : P = 1 := by omega
    subst this; simp [Nat.mod_one]

/-- One period of `(uⁿv)^∞`, read at a position `r < n|u| + |v|`. -/
def blockWord (u v : ℕ → Fin k) (L n r : ℕ) : Fin k := if r < n * L then u (r % L) else v (r - n * L)

theorem familyPoint_apply (u v : ℕ → Fin k) (L L' n i : ℕ) :
    familyPoint u v L L' n i = blockWord u v L n (i % (n * L + L')) := rfl

section ReturnWords

variable {a : Fin k} {u v : ℕ → Fin k} {L L' : ℕ}

/-- Inside one period the symbol `a` sits exactly at the block starts `0, L, …, nL`. -/
theorem blockWord_eq_iff (hu : IsReturnWord A a u L) (hv : IsReturnWord A a v L') (n : ℕ)
    {r : ℕ} (hr : r < n * L + L') :
    blockWord u v L n r = a ↔ (r < n * L ∧ r % L = 0) ∨ r = n * L := by
  unfold blockWord
  split_ifs with h
  · constructor
    · intro hua
      left
      refine ⟨h, ?_⟩
      by_contra h0
      exact hu.avoid (r % L) (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ hu.pos) hua
    · rintro (⟨-, h0⟩ | h0)
      · rw [h0]; exact hu.start
      · omega
  · constructor
    · intro hva
      right
      by_contra h0
      exact hv.avoid (r - n * L) (by omega) (by omega) hva
    · rintro (⟨h1, -⟩ | h0)
      · omega
      · rw [h0, Nat.sub_self]; exact hv.start

theorem blockWord_zero (hu : IsReturnWord A a u L) (hv : IsReturnWord A a v L') (n : ℕ) :
    blockWord u v L n 0 = a := by
  refine (blockWord_eq_iff hu hv n (by have := hv.pos; omega)).mpr ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · right; simp
  · left; exact ⟨Nat.mul_pos hn hu.pos, Nat.zero_mod _⟩

/-- The cycle point `u^∞` of a return word is admissible. -/
theorem isAdmissible_cyclePoint (hu : IsReturnWord A a u L) : IsAdmissible A (cyclePoint u L) := by
  intro i
  simp only [cyclePoint]
  rw [succ_mod_eq_ite hu.pos]
  have hlt := Nat.mod_lt i hu.pos
  split_ifs with h
  · exact hu.adm_in _ h
  · rw [show i % L = L - 1 by omega, hu.start]; exact hu.adm_close

/-- The cycle point of a return word has least period its length. -/
theorem minimalPeriod_cyclePoint (hu : IsReturnWord A a u L) :
    Function.minimalPeriod (shiftBy 1) (cyclePoint u L) = L := by
  refine minimalPeriod_eq_of_dvd hu.pos ?_ fun m _ hm => ?_
  · funext i; simp [cyclePoint, Nat.add_mod_right]
  · have h := congrFun hm 0
    simp only [shiftBy_apply, zero_add, cyclePoint, Nat.zero_mod, hu.start] at h
    by_contra hndvd
    exact hu.avoid (m % L) (Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
      (Nat.mod_lt _ hu.pos) h

/-- Every member of the cycle family of two return words is admissible. -/
theorem isAdmissible_familyPoint (hu : IsReturnWord A a u L) (hv : IsReturnWord A a v L')
    (n : ℕ) : IsAdmissible A (familyPoint u v L L' n) := by
  have hL := hu.pos
  have hL' := hv.pos
  set P := n * L + L' with hP
  have hP0 : 0 < P := by omega
  intro i
  rw [familyPoint_apply, familyPoint_apply, succ_mod_eq_ite hP0]
  set r := i % P with hr
  have hrP : r < P := Nat.mod_lt _ hP0
  split_ifs with hwrap
  · -- the next position stays inside the period
    by_cases hu1 : r + 1 < n * L
    · -- inside the `u`-blocks
      have hr1 : r < n * L := by omega
      simp only [blockWord, if_pos hr1, if_pos hu1]
      rw [succ_mod_eq_ite hL]
      split_ifs with hin
      · exact hu.adm_in _ hin
      · rw [show r % L = L - 1 by have := Nat.mod_lt r hL; omega, hu.start]
        exact hu.adm_close
    · by_cases hr1 : r < n * L
      · -- the last letter of the last `u` before `v`
        have hrn : r + 1 = n * L := by omega
        simp only [blockWord, if_pos hr1, hrn, Nat.sub_self, hv.start]
        have hmod : (r + 1) % L = 0 := by rw [hrn, Nat.mul_mod_left]
        have hlast : r % L = L - 1 := by
          have := Nat.mod_lt r hL
          rw [succ_mod_eq_ite hL] at hmod
          split_ifs at hmod with hin
          omega
        rw [hlast, if_neg (lt_irrefl _)]
        exact hu.adm_close
      · -- inside `v`
        simp only [blockWord, if_neg hr1, if_neg hu1]
        rw [show r + 1 - n * L = r - n * L + 1 by omega]
        exact hv.adm_in _ (by omega)
  · -- wrap-around from the last letter of `v` to the first block
    have hrlast : r = P - 1 := by omega
    have hr1 : ¬ r < n * L := by omega
    rw [blockWord_zero hu hv n]
    simp only [blockWord, if_neg hr1]
    rw [show r - n * L = L' - 1 by omega]
    exact hv.adm_close

/-- **The cycle family of two different return words is primitive**: `(uⁿv)^∞` has least period
`n|u| + |v|`. -/
theorem minimalPeriod_familyPoint (hu : IsReturnWord A a u L) (hv : IsReturnWord A a v L')
    (hne : ¬ (L = L' ∧ ∀ i < L, u i = v i)) (n : ℕ) :
    Function.minimalPeriod (shiftBy 1) (familyPoint u v L L' n) = n * L + L' := by
  have hL := hu.pos
  have hL' := hv.pos
  set P := n * L + L' with hP
  have hP0 : 0 < P := by omega
  refine minimalPeriod_eq_of_dvd hP0 ?_ fun m _ hm => ?_
  · funext i; simp [familyPoint_apply, hP, Nat.add_mod_right]
  -- the residue `d = m mod P` is itself a period
  set d := m % P with hd
  have hdP : d < P := Nat.mod_lt _ hP0
  have hshift : ∀ i, blockWord u v L n ((i + d) % P) = blockWord u v L n (i % P) := by
    intro i
    have hmod : (i + m) % P = (i + d) % P := by
      rw [Nat.add_mod, Nat.add_mod i d, hd, Nat.mod_mod]
    have h := congrFun hm i
    rw [shiftBy_apply, familyPoint_apply, familyPoint_apply, ← hP, hmod] at h
    exact h
  by_contra hndvd
  have hd0 : d ≠ 0 := fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
  -- `d` is a block start: `L ∣ d` and `d ≤ nL`
  have hda : blockWord u v L n d = a := by
    have h := hshift 0
    rwa [zero_add, Nat.mod_eq_of_lt hdP, Nat.zero_mod, blockWord_zero hu hv n] at h
  have hdblock := (blockWord_eq_iff hu hv n hdP).mp hda
  have hdvd : L ∣ d := by
    rcases hdblock with ⟨-, h⟩ | h
    · exact Nat.dvd_of_mod_eq_zero h
    · rw [h]; exact Dvd.intro_left n rfl
  have hdle : d ≤ n * L := by rcases hdblock with ⟨h, -⟩ | h <;> omega
  -- the block `q = nL − d` is carried onto `v`
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨b, hb⟩ : ∃ b, n = c + b := ⟨n - c, by
    have : L * c ≤ L * n := by rw [← hc, mul_comm L n]; exact hdle
    have := Nat.le_of_mul_le_mul_left this hL
    omega⟩
  have hb1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact absurd (by rw [hc, h, mul_zero]) hd0
    · exact h
  set q := b * L with hq
  have hqd : q + d = n * L := by rw [hq, hc, hb]; ring
  have hqL : q + L ≤ n * L := by rw [hb, hq]; nlinarith
  -- the lengths agree: the `a` after the block `q` lands on an `a`
  have hLL : L = L' := by
    have hqa : blockWord u v L n (q + L) = a := by
      refine (blockWord_eq_iff hu hv n (by omega)).mpr ?_
      rcases lt_or_eq_of_le hqL with h | h
      · left; exact ⟨h, by rw [hq, show b * L + L = (b + 1) * L by ring, Nat.mul_mod_left]⟩
      · right; exact h
    have h := hshift (q + L)
    rw [Nat.mod_eq_of_lt (show q + L < P by omega), hqa,
      show q + L + d = n * L + L by omega] at h
    rcases lt_trichotomy L L' with hlt | heq | hgt
    · rw [Nat.mod_eq_of_lt (show n * L + L < P by omega)] at h
      rcases (blockWord_eq_iff hu hv n (show n * L + L < P by omega)).mp h with ⟨h1, -⟩ | h1 <;>
        omega
    · exact heq
    · have hn1 : 1 ≤ n := by rw [hb]; omega
      rw [Nat.mod_eq_sub_mod (show P ≤ n * L + L by omega),
        Nat.mod_eq_of_lt (show n * L + L - P < P by omega),
        show n * L + L - P = L - L' by omega] at h
      rcases (blockWord_eq_iff hu hv n (show L - L' < P by omega)).mp h with ⟨-, h1⟩ | h1
      · rw [Nat.mod_eq_of_lt (show L - L' < L by omega)] at h1; omega
      · have : L ≤ n * L := Nat.le_mul_of_pos_left L hn1
        omega
  -- and the letters agree: the block `q` is a copy of `u`, shifted onto `v`
  refine hne ⟨hLL, fun i hi => ?_⟩
  have h := hshift (q + i)
  rw [show q + i + d = n * L + i by omega, Nat.mod_eq_of_lt (show n * L + i < P by omega),
    Nat.mod_eq_of_lt (show q + i < P by omega)] at h
  simp only [blockWord, if_neg (show ¬ n * L + i < n * L by omega),
    if_pos (show q + i < n * L by omega), Nat.add_sub_cancel_left] at h
  rw [hq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi] at h
  exact h.symm

end ReturnWords

variable {φ : (ℕ → Fin k) → ℝ} {C θ : ℝ}

/-- **The Hölder modulus along every cycle.** In a `(C, θ)`-Hölder prime-length system, a return
word `u` at a symbol that has a second, different return word `v` satisfies
`θ^{|u|} · e^{φ^{|u|}(u^∞)} ≥ 1`. -/
theorem one_le_exp_mul_pow_of_returnWords (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    (hPL : IsPrimeLength A φ) {a : Fin k} {u v : ℕ → Fin k} {L L' : ℕ}
    (hu : IsReturnWord A a u L) (hv : IsReturnWord A a v L')
    (hne : ¬ (L = L' ∧ ∀ i < L, u i = v i)) :
    1 ≤ Real.exp (birkhoff φ L (cyclePoint u L)) * θ ^ L := by
  have hy := isAdmissible_cyclePoint hu
  obtain ⟨q, hq, hqa⟩ := hPL _ hy L hu.pos (minimalPeriod_cyclePoint hu)
  have hx := isAdmissible_familyPoint hu hv
  choose p hp using fun n => hPL _ (hx n) (n * L + L') (by have := hv.pos; omega)
    (minimalPeriod_familyPoint hu hv hne n)
  have h := one_le_mul_pow_of_cycleFamily hθ0 hθ1 hh (isCycleFamily_familyPoint u v L L') hy hx
    hq.two_le hqa (fun n => (hp n).2) (Eventually.of_forall fun n => (hp n).1)
  rwa [← hqa] at h

/-- **The price of the strip along every cycle.** A realization of `ζ` by a `(C, θ)`-Hölder roof on
a subshift of finite type has `θ^{|u|} · e^{φ^{|u|}(u^∞)} ≥ 1` for every return word `u` whose base
symbol has a second, different return word. -/
theorem one_le_exp_mul_pow_of_holderRealization {R₀ : ℝ} (hφ : IsHolderPotential A φ R₀ C θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {rmin : ℝ} (hrmin : 0 < rmin)
    (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1))
    (hreal : ∀ s : ℂ, 1 < s.re →
      riemannZeta s = Complex.exp (∑' n : ℕ, periodicZ A φ (n + 1) s / ((n : ℂ) + 1)))
    {a : Fin k} {u v : ℕ → Fin k} {L L' : ℕ} (hu : IsReturnWord A a u L)
    (hv : IsReturnWord A a v L') (hne : ¬ (L = L' ∧ ∀ i < L, u i = v i)) :
    1 ≤ Real.exp (birkhoff φ L (cyclePoint u L)) * θ ^ L :=
  one_le_exp_mul_pow_of_returnWords hθ0 hθ1 hφ.holder
    (isPrimeLength_of_realization hrmin hmin hsum hreal) hu hv hne

end GaloisForLFunctions.ArithmeticResonanceTheory
