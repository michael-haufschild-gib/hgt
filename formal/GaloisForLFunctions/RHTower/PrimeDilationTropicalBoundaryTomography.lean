import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence
import Mathlib.Data.Nat.Choose.Sum

/-!
# Prime-dilation tropical-boundary tomography

A bounded prime-valuation vector has a maximum shell radius.  Its first crossing time in each
prime direction is the number of prime multiplications required to leave that shell.  These
crossing times recover every valuation coordinate exactly.

Prime multiplication is therefore an intrinsic reset-and-carry operation on the complete family
of shell-covariance failures.  This is the unconditional algebraic core of the proposed
face-complete source completion; it does not prove RH or construct the Xi-conormal comparison.
-/

namespace RHTower

/-- A bounded supernatural prime-valuation vector together with an attained shell radius. -/
structure BoundedPrimeValuation where
  valuation : Nat.Primes → ℕ
  radius : ℕ
  valuation_le_radius : ∀ p, valuation p ≤ radius
  radius_attained : ∃ p, valuation p = radius

namespace BoundedPrimeValuation

/-- First positive number of multiplications by `p` required to cross the present shell radius. -/
def crossingTime (x : BoundedPrimeValuation) (p : Nat.Primes) : ℕ :=
  x.radius - x.valuation p + 1

theorem crossingTime_pos (x : BoundedPrimeValuation) (p : Nat.Primes) :
    0 < x.crossingTime p := by
  simp [crossingTime]

/-- Crossing-time tomography recovers each valuation coordinate. -/
theorem valuation_add_crossingTime (x : BoundedPrimeValuation) (p : Nat.Primes) :
    x.valuation p + x.crossingTime p = x.radius + 1 := by
  simp only [crossingTime]
  have hle := x.valuation_le_radius p
  omega

theorem valuation_eq_radius_add_one_sub_crossingTime
    (x : BoundedPrimeValuation) (p : Nat.Primes) :
    x.valuation p = x.radius + 1 - x.crossingTime p := by
  rw [crossingTime]
  have hle := x.valuation_le_radius p
  omega

theorem crossingTime_le_radius_add_one
    (x : BoundedPrimeValuation) (p : Nat.Primes) :
    x.crossingTime p ≤ x.radius + 1 := by
  rw [crossingTime]
  omega

theorem crossingTime_eq_radius_add_one_of_valuation_eq_zero
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p = 0) :
    x.crossingTime p = x.radius + 1 := by
  simp [crossingTime, hp]

/-- At fixed radius, the complete crossing-time profile is injective. -/
theorem ext_of_radius_eq_of_crossingTime_eq
    {x y : BoundedPrimeValuation}
    (hradius : x.radius = y.radius)
    (hcrossing : ∀ p, x.crossingTime p = y.crossingTime p) :
    x = y := by
  have hvaluation : x.valuation = y.valuation := by
    funext p
    calc
      x.valuation p = x.radius + 1 - x.crossingTime p :=
        valuation_eq_radius_add_one_sub_crossingTime x p
      _ = y.radius + 1 - y.crossingTime p := by rw [hradius, hcrossing p]
      _ = y.valuation p :=
        (valuation_eq_radius_add_one_sub_crossingTime y p).symm
  cases x
  cases y
  simp only at hvaluation hradius
  subst hvaluation
  subst hradius
  rfl

/-- If both bounded valuation vectors have a zero coordinate, their complete crossing-time
profiles recover the radius as well as every coordinate.  Ordinary integers satisfy this
hypothesis at every prime outside their finite support. -/
theorem ext_of_exists_valuation_eq_zero_of_crossingTime_eq
    {x y : BoundedPrimeValuation}
    (hxzero : ∃ p, x.valuation p = 0)
    (hyzero : ∃ p, y.valuation p = 0)
    (hcrossing : ∀ p, x.crossingTime p = y.crossingTime p) :
    x = y := by
  obtain ⟨p, hp⟩ := hxzero
  obtain ⟨q, hq⟩ := hyzero
  have hxy : x.radius ≤ y.radius := by
    have hpmax := crossingTime_eq_radius_add_one_of_valuation_eq_zero x p hp
    have hpbound := crossingTime_le_radius_add_one y p
    rw [← hcrossing p, hpmax] at hpbound
    omega
  have hyx : y.radius ≤ x.radius := by
    have hqmax := crossingTime_eq_radius_add_one_of_valuation_eq_zero y q hq
    have hqbound := crossingTime_le_radius_add_one x q
    rw [hcrossing q, hqmax] at hqbound
    omega
  exact ext_of_radius_eq_of_crossingTime_eq (le_antisymm hxy hyx) hcrossing

/-- Exact threshold law: the `k`th prime dilation has crossed the old radius exactly when the
crossing time is at most `k`. -/
theorem crossingTime_le_iff_radius_lt_add
    (x : BoundedPrimeValuation) (p : Nat.Primes) (k : ℕ) :
    x.crossingTime p ≤ k ↔ x.radius < x.valuation p + k := by
  rw [crossingTime]
  have hle := x.valuation_le_radius p
  omega

/-- Multiplication by one prime on bounded supernatural valuation vectors. -/
noncomputable def primeDilation
    (x : BoundedPrimeValuation) (p : Nat.Primes) : BoundedPrimeValuation where
  valuation q := if q = p then x.valuation q + 1 else x.valuation q
  radius := if x.valuation p = x.radius then x.radius + 1 else x.radius
  valuation_le_radius := by
    intro q
    by_cases hpmax : x.valuation p = x.radius
    · rw [if_pos hpmax]
      by_cases hqp : q = p
      · subst q
        rw [if_pos rfl, hpmax]
      · rw [if_neg hqp]
        exact (x.valuation_le_radius q).trans (Nat.le_succ _)
    · rw [if_neg hpmax]
      by_cases hqp : q = p
      · subst q
        rw [if_pos rfl]
        have hp_le := x.valuation_le_radius p
        omega
      · rw [if_neg hqp]
        exact x.valuation_le_radius q
  radius_attained := by
    by_cases hpmax : x.valuation p = x.radius
    · refine ⟨p, ?_⟩
      simp [hpmax]
    · obtain ⟨q, hq⟩ := x.radius_attained
      have hqp : q ≠ p := by
        intro h
        subst q
        exact hpmax hq
      refine ⟨q, ?_⟩
      simp [hqp, hpmax, hq]

@[simp] theorem primeDilation_valuation_same
    (x : BoundedPrimeValuation) (p : Nat.Primes) :
    (x.primeDilation p).valuation p = x.valuation p + 1 := by
  simp [primeDilation]

theorem primeDilation_valuation_of_ne
    (x : BoundedPrimeValuation) {p q : Nat.Primes} (hqp : q ≠ p) :
    (x.primeDilation p).valuation q = x.valuation q := by
  simp [primeDilation, hqp]

theorem primeDilation_radius_of_eq
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p = x.radius) :
    (x.primeDilation p).radius = x.radius + 1 := by
  simp [primeDilation, hp]

theorem primeDilation_radius_of_ne
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p ≠ x.radius) :
    (x.primeDilation p).radius = x.radius := by
  simp [primeDilation, hp]

/-- A prime already on the winning face crosses the radius and becomes the unique winner. -/
theorem primeDilation_unique_winner_of_eq
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p = x.radius) :
    ∀ q, (x.primeDilation p).valuation q = (x.primeDilation p).radius ↔ q = p := by
  intro q
  constructor
  · intro hq
    by_contra hne
    rw [primeDilation_valuation_of_ne x hne,
      primeDilation_radius_of_eq x p hp] at hq
    have hle := x.valuation_le_radius q
    omega
  · rintro rfl
    simp [primeDilation, hp]

/-- If `p` is below the winning face, its crossing time decrements by one. -/
theorem crossingTime_primeDilation_same_of_lt
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p < x.radius) :
    (x.primeDilation p).crossingTime p + 1 = x.crossingTime p := by
  rw [crossingTime, crossingTime, primeDilation_valuation_same,
    primeDilation_radius_of_ne x p (ne_of_lt hp)]
  omega

/-- If `p` is already on the winning face, dilation resets its crossing time to one. -/
theorem crossingTime_primeDilation_same_of_eq
    (x : BoundedPrimeValuation) (p : Nat.Primes)
    (hp : x.valuation p = x.radius) :
    (x.primeDilation p).crossingTime p = 1 := by
  rw [crossingTime, primeDilation_valuation_same,
    primeDilation_radius_of_eq x p hp, hp]
  omega

/-- Below the winning face, dilation by `p` leaves every other crossing time unchanged. -/
theorem crossingTime_primeDilation_ne_of_lt
    (x : BoundedPrimeValuation) {p q : Nat.Primes}
    (hqp : q ≠ p) (hp : x.valuation p < x.radius) :
    (x.primeDilation p).crossingTime q = x.crossingTime q := by
  rw [crossingTime, crossingTime, primeDilation_valuation_of_ne x hqp,
    primeDilation_radius_of_ne x p (ne_of_lt hp)]

/-- Crossing the winning face carries one unit into every other prime direction. -/
theorem crossingTime_primeDilation_ne_of_eq
    (x : BoundedPrimeValuation) {p q : Nat.Primes}
    (hqp : q ≠ p) (hp : x.valuation p = x.radius) :
    (x.primeDilation p).crossingTime q = x.crossingTime q + 1 := by
  rw [crossingTime, crossingTime, primeDilation_valuation_of_ne x hqp,
    primeDilation_radius_of_eq x p hp]
  have hle := x.valuation_le_radius q
  omega

/-- Exact reset-and-carry law for prime dilation on the complete crossing-time profile. -/
theorem primeDilation_resetAndCarry
    (x : BoundedPrimeValuation) (p : Nat.Primes) :
    (x.crossingTime p = 1 ∧
        (x.primeDilation p).crossingTime p = 1 ∧
        ∀ q, q ≠ p →
          (x.primeDilation p).crossingTime q = x.crossingTime q + 1) ∨
      (1 < x.crossingTime p ∧
        (x.primeDilation p).crossingTime p + 1 = x.crossingTime p ∧
        ∀ q, q ≠ p →
          (x.primeDilation p).crossingTime q = x.crossingTime q) := by
  by_cases hp : x.valuation p = x.radius
  · left
    have htime : x.crossingTime p = 1 := by
      simp [crossingTime, hp]
    exact ⟨htime, crossingTime_primeDilation_same_of_eq x p hp,
      fun q hqp => crossingTime_primeDilation_ne_of_eq x hqp hp⟩
  · right
    have hlt : x.valuation p < x.radius :=
      lt_of_le_of_ne (x.valuation_le_radius p) hp
    have htime : 1 < x.crossingTime p := by
      rw [crossingTime]
      omega
    exact ⟨htime, crossingTime_primeDilation_same_of_lt x p hlt,
      fun q hqp => crossingTime_primeDilation_ne_of_lt x hqp hlt⟩

/-- Indicator of one radial maximum-exponent shell on the bounded valuation source. -/
def tropicalShellIndicator (m : ℕ) (x : BoundedPrimeValuation) : ℤ :=
  if x.radius = m then 1 else 0

/-- Indicator that `p` lies on the winning face of the radius-`m` valuation cube. -/
def primeWinningFacetIndicator
    (p : Nat.Primes) (m : ℕ) (x : BoundedPrimeValuation) : ℤ :=
  if x.radius = m ∧ x.valuation p = m then 1 else 0

/-- **Prime-dilation shell boundary law.** The failure of a radial shell to be covariant under
one prime dilation is exactly the signed difference of the two adjacent winning-facet cells. -/
theorem tropicalShellIndicator_primeDilation_sub
    (x : BoundedPrimeValuation) (p : Nat.Primes) {m : ℕ} (hm : 0 < m) :
    tropicalShellIndicator m (x.primeDilation p) - tropicalShellIndicator m x =
      primeWinningFacetIndicator p (m - 1) x -
        primeWinningFacetIndicator p m x := by
  by_cases hp : x.valuation p = x.radius
  · rw [tropicalShellIndicator, tropicalShellIndicator,
      primeWinningFacetIndicator, primeWinningFacetIndicator,
      primeDilation_radius_of_eq x p hp]
    simp only [hp]
    split_ifs <;> omega
  · have hlt : x.valuation p < x.radius :=
      lt_of_le_of_ne (x.valuation_le_radius p) hp
    rw [tropicalShellIndicator, tropicalShellIndicator,
      primeWinningFacetIndicator, primeWinningFacetIndicator,
      primeDilation_radius_of_ne x p hp]
    split_ifs <;> omega

/-- Additive form of the shell/facet conservation law.  Adjoining the winning-facet cells closes
the first source operation forced by radial shell covariance failure. -/
theorem tropicalShellIndicator_primeDilation
    (x : BoundedPrimeValuation) (p : Nat.Primes) {m : ℕ} (hm : 0 < m) :
    tropicalShellIndicator m (x.primeDilation p) =
      tropicalShellIndicator m x +
        primeWinningFacetIndicator p (m - 1) x -
          primeWinningFacetIndicator p m x := by
  have hboundary := tropicalShellIndicator_primeDilation_sub x p hm
  omega

/-- Source covariance defect in one prime-dilation direction. -/
noncomputable def primeDifference
    (p : Nat.Primes) (f : BoundedPrimeValuation → ℤ)
    (x : BoundedPrimeValuation) : ℤ :=
  f (x.primeDilation p) - f x

/-- Indicator of the radius-`m` face on which every prime in `F` is a winner.
Primes outside `F` may also be winners. -/
def winningFaceIndicator
    (F : Finset Nat.Primes) (m : ℕ) (x : BoundedPrimeValuation) : ℤ :=
  if x.radius = m ∧ ∀ p ∈ F, x.valuation p = m then 1 else 0

theorem winningFaceIndicator_singleton
    (x : BoundedPrimeValuation) (p : Nat.Primes) (m : ℕ) :
    winningFaceIndicator {p} m x = primeWinningFacetIndicator p m x := by
  simp [winningFaceIndicator, primeWinningFacetIndicator]

/-- Winning-face cells form the intersection semilattice of the prime-facet cover. -/
theorem winningFaceIndicator_mul
    (x : BoundedPrimeValuation) (F G : Finset Nat.Primes) (m : ℕ) :
    winningFaceIndicator F m x * winningFaceIndicator G m x =
      winningFaceIndicator (F ∪ G) m x := by
  unfold winningFaceIndicator
  by_cases hF : x.radius = m ∧ ∀ p ∈ F, x.valuation p = m
  · by_cases hG : x.radius = m ∧ ∀ p ∈ G, x.valuation p = m
    · have hUnion : x.radius = m ∧ ∀ p ∈ F ∪ G, x.valuation p = m := by
        refine ⟨hF.1, ?_⟩
        intro p hp
        rw [Finset.mem_union] at hp
        rcases hp with hpF | hpG
        · exact hF.2 p hpF
        · exact hG.2 p hpG
      rw [if_pos hF, if_pos hG, if_pos hUnion]
      norm_num
    · have hUnion : ¬(x.radius = m ∧ ∀ p ∈ F ∪ G, x.valuation p = m) := by
        intro h
        exact hG ⟨h.1, fun p hpG => h.2 p (Finset.mem_union_right F hpG)⟩
      rw [if_pos hF, if_neg hG, if_neg hUnion]
      norm_num
  · have hUnion : ¬(x.radius = m ∧ ∀ p ∈ F ∪ G, x.valuation p = m) := by
      intro h
      exact hF ⟨h.1, fun p hpF => h.2 p (Finset.mem_union_left G hpF)⟩
    rw [if_neg hF, if_neg hUnion]
    norm_num

/-- Winners visible in a finite prime aperture. -/
def winnerSetWithin
    (x : BoundedPrimeValuation) (P : Finset Nat.Primes) : Finset Nat.Primes :=
  P.filter (fun p => x.valuation p = x.radius)

/-- **Finite prime-winning Čech augmentation.** At every source point where a finite aperture
contains a winner, alternating over all nonempty faces of its winner simplex recovers the radial
shell indicator exactly. -/
theorem tropicalShellIndicator_eq_alternating_winningFace_sum
    (x : BoundedPrimeValuation) (P : Finset Nat.Primes) (m : ℕ)
    (hW : (winnerSetWithin x P).Nonempty) :
    tropicalShellIndicator m x =
      ∑ F ∈ (winnerSetWithin x P).powerset.erase ∅,
        (-1 : ℤ) ^ (F.card + 1) * winningFaceIndicator F m x := by
  classical
  let W := winnerSetWithin x P
  have hsumZero :
      (∑ F ∈ W.powerset, (-1 : ℤ) ^ F.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hW
  have hempty : (∅ : Finset Nat.Primes) ∈ W.powerset := by
    simp
  have herase :
      (∑ F ∈ W.powerset.erase ∅, (-1 : ℤ) ^ F.card) = -1 := by
    have hsplit :=
      Finset.sum_erase_add W.powerset (fun F => (-1 : ℤ) ^ F.card) hempty
    rw [hsumZero] at hsplit
    norm_num at hsplit ⊢
    exact hsplit
  have halternating :
      (∑ F ∈ W.powerset.erase ∅, (-1 : ℤ) ^ (F.card + 1)) = 1 := by
    calc
      (∑ F ∈ W.powerset.erase ∅, (-1 : ℤ) ^ (F.card + 1)) =
          -(∑ F ∈ W.powerset.erase ∅, (-1 : ℤ) ^ F.card) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro F hF
            rw [pow_succ]
            ring
      _ = 1 := by rw [herase]; norm_num
  by_cases hradius : x.radius = m
  · rw [tropicalShellIndicator, if_pos hradius]
    calc
      1 = ∑ F ∈ W.powerset.erase ∅, (-1 : ℤ) ^ (F.card + 1) :=
        halternating.symm
      _ = ∑ F ∈ (winnerSetWithin x P).powerset.erase ∅,
          (-1 : ℤ) ^ (F.card + 1) * winningFaceIndicator F m x := by
            apply Finset.sum_congr rfl
            intro F hF
            have hsubset : F ⊆ W := by
              exact Finset.mem_powerset.mp (Finset.mem_of_mem_erase hF)
            have hface :
                winningFaceIndicator F m x = 1 := by
              unfold winningFaceIndicator
              rw [if_pos]
              refine ⟨hradius, ?_⟩
              intro p hpF
              have hpW := hsubset hpF
              have hpRadius :
                  x.valuation p = x.radius :=
                (Finset.mem_filter.mp hpW).2
              exact hpRadius.trans hradius
            rw [hface]
            ring
  · simp [tropicalShellIndicator, winningFaceIndicator, hradius]

/-- **Face-extension law.** Once a nonempty winning face has been generated, taking
the covariance defect in a new prime direction adjoins exactly that prime to the face. -/
theorem primeDifference_winningFaceIndicator_of_nonempty_not_mem
    (x : BoundedPrimeValuation) (F : Finset Nat.Primes) (p : Nat.Primes) (m : ℕ)
    (hF : F.Nonempty) (hpF : p ∉ F) :
    primeDifference p (winningFaceIndicator F m) x =
      -winningFaceIndicator (insert p F) m x := by
  unfold primeDifference winningFaceIndicator
  by_cases hpmax : x.valuation p = x.radius
  · have hout :
        ¬ ((x.primeDilation p).radius = m ∧
          ∀ q ∈ F, (x.primeDilation p).valuation q = m) := by
      rintro ⟨hradius, hface⟩
      obtain ⟨q, hqF⟩ := hF
      have hqp : q ≠ p := by
        intro h
        subst q
        exact hpF hqF
      have hq := hface q hqF
      rw [primeDilation_radius_of_eq x p hpmax] at hradius
      rw [primeDilation_valuation_of_ne x hqp] at hq
      have hle := x.valuation_le_radius q
      omega
    have hinsert :
        (x.radius = m ∧ ∀ q ∈ insert p F, x.valuation q = m) ↔
          (x.radius = m ∧ ∀ q ∈ F, x.valuation q = m) := by
      constructor
      · rintro ⟨hradius, hface⟩
        exact ⟨hradius, fun q hqF => hface q (Finset.mem_insert_of_mem hqF)⟩
      · rintro ⟨hradius, hface⟩
        refine ⟨hradius, ?_⟩
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hqF
        · exact hpmax.trans hradius
        · exact hface q hqF
    rw [if_neg hout]
    by_cases hface : x.radius = m ∧ ∀ q ∈ F, x.valuation q = m
    · rw [if_pos hface, if_pos (hinsert.mpr hface)]
      norm_num
    · rw [if_neg hface, if_neg (fun h => hface (hinsert.mp h))]
      norm_num
  · have hbelow : x.valuation p < x.radius :=
      lt_of_le_of_ne (x.valuation_le_radius p) hpmax
    have hdilation :
        ((x.primeDilation p).radius = m ∧
            ∀ q ∈ F, (x.primeDilation p).valuation q = m) ↔
          (x.radius = m ∧ ∀ q ∈ F, x.valuation q = m) := by
      constructor
      · rintro ⟨hradius, hface⟩
        refine ⟨?_, ?_⟩
        · simpa [primeDilation_radius_of_ne x p hpmax] using hradius
        · intro q hqF
          have hqp : q ≠ p := by
            intro h
            subst q
            exact hpF hqF
          simpa [primeDilation_valuation_of_ne x hqp] using hface q hqF
      · rintro ⟨hradius, hface⟩
        refine ⟨?_, ?_⟩
        · simpa [primeDilation_radius_of_ne x p hpmax] using hradius
        · intro q hqF
          have hqp : q ≠ p := by
            intro h
            subst q
            exact hpF hqF
          simpa [primeDilation_valuation_of_ne x hqp] using hface q hqF
    have hinsert :
        ¬ (x.radius = m ∧ ∀ q ∈ insert p F, x.valuation q = m) := by
      rintro ⟨hradius, hface⟩
      have hp := hface p (Finset.mem_insert_self p F)
      omega
    rw [if_neg hinsert]
    by_cases hface : x.radius = m ∧ ∀ q ∈ F, x.valuation q = m
    · rw [if_pos hface, if_pos (hdilation.mpr hface)]
      norm_num
    · rw [if_neg hface, if_neg (fun h => hface (hdilation.mp h))]
      norm_num

/-- Iteration of source covariance defects in an ordered finite prime list. -/
noncomputable def iteratedPrimeDifference :
    List Nat.Primes → (BoundedPrimeValuation → ℤ) → BoundedPrimeValuation → ℤ
  | [], f => f
  | p :: ps, f => primeDifference p (iteratedPrimeDifference ps f)

/-- **Higher winning-face generation.** Every squarefree iterated prime-dilation defect
of a positive radial shell is the signed boundary of the corresponding simultaneous-winning
face. Thus the source operation closure of radial shells contains the full finite face nerve. -/
theorem iteratedPrimeDifference_tropicalShellIndicator
    (ps : List Nat.Primes) (hne : ps ≠ []) (hnd : ps.Nodup)
    (x : BoundedPrimeValuation) {m : ℕ} (hm : 0 < m) :
    iteratedPrimeDifference ps (tropicalShellIndicator m) x =
      (-1 : ℤ) ^ (ps.length - 1) *
        (winningFaceIndicator ps.toFinset (m - 1) x -
          winningFaceIndicator ps.toFinset m x) := by
  induction ps generalizing x with
  | nil =>
      exact (hne rfl).elim
  | cons p ps ih =>
      obtain ⟨hpF, hps⟩ := List.nodup_cons.mp hnd
      by_cases htail : ps = []
      · subst ps
        simp only [iteratedPrimeDifference, primeDifference]
        rw [tropicalShellIndicator_primeDilation_sub x p hm]
        simp [winningFaceIndicator_singleton]
      · have ihD := ih htail hps (x.primeDilation p)
        have ihx := ih htail hps x
        have hlow :=
          primeDifference_winningFaceIndicator_of_nonempty_not_mem
            x ps.toFinset p (m - 1) ((List.toFinset_nonempty_iff ps).mpr htail)
              (by simpa using hpF)
        have hhigh :=
          primeDifference_winningFaceIndicator_of_nonempty_not_mem
            x ps.toFinset p m ((List.toFinset_nonempty_iff ps).mpr htail)
              (by simpa using hpF)
        rw [iteratedPrimeDifference, primeDifference, ihD, ihx]
        simp only [List.length_cons, Nat.succ_sub_one, List.toFinset_cons]
        unfold primeDifference at hlow hhigh
        calc
          (-1 : ℤ) ^ (ps.length - 1) *
                (winningFaceIndicator ps.toFinset (m - 1) (x.primeDilation p) -
                  winningFaceIndicator ps.toFinset m (x.primeDilation p)) -
              (-1 : ℤ) ^ (ps.length - 1) *
                (winningFaceIndicator ps.toFinset (m - 1) x -
                  winningFaceIndicator ps.toFinset m x) =
              (-1 : ℤ) ^ (ps.length - 1) *
                ((winningFaceIndicator ps.toFinset (m - 1) (x.primeDilation p) -
                    winningFaceIndicator ps.toFinset (m - 1) x) -
                  (winningFaceIndicator ps.toFinset m (x.primeDilation p) -
                    winningFaceIndicator ps.toFinset m x)) := by ring
          _ = (-1 : ℤ) ^ (ps.length - 1) *
                (-winningFaceIndicator (insert p ps.toFinset) (m - 1) x -
                  -winningFaceIndicator (insert p ps.toFinset) m x) := by
                rw [hlow, hhigh]
          _ = -((-1 : ℤ) ^ (ps.length - 1)) *
                (winningFaceIndicator (insert p ps.toFinset) (m - 1) x -
                  winningFaceIndicator (insert p ps.toFinset) m x) := by ring
          _ = (-1 : ℤ) ^ ps.length *
                (winningFaceIndicator (insert p ps.toFinset) (m - 1) x -
                  winningFaceIndicator (insert p ps.toFinset) m x) := by
                have hlength : ps.length = (ps.length - 1) + 1 := by
                  have : 0 < ps.length := List.length_pos_of_ne_nil htail
                  omega
                have hsign :
                    (-1 : ℤ) ^ ps.length =
                      -((-1 : ℤ) ^ (ps.length - 1)) := by
                  calc
                    (-1 : ℤ) ^ ps.length =
                        (-1 : ℤ) ^ ((ps.length - 1) + 1) := by
                      exact congrArg (fun n : ℕ => (-1 : ℤ) ^ n) hlength
                    _ = -((-1 : ℤ) ^ (ps.length - 1)) := by
                      rw [pow_succ]
                      ring
                rw [hsign]

end BoundedPrimeValuation

end RHTower
