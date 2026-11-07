import GaloisForLFunctions.ArithmeticScatteringHolography.TheBaseChangeTower
import GaloisForLFunctions.ArithmeticScatteringHolography.TheBlackHoleOfACurve
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The count law of the probes

A black hole `(q, t)` has a ring: `ℤ[π] = ℤ[x]/(x² - t x + q)`, with `G = ℤ[π]/(1 - π)` of order `q + 1 - t` and `G' = ℤ[π]/(1 + π)` of order
`q + 1 + t`. This ring exists for fakes too, where it is a real quadratic order. It carries every two-term probe `y - x π`, and the
Krein square is its norm: the number of elements of `ℤ[π]/(y - x π)` is `|𝒬(x, y)|` (`card_quotient_probeLattice`). The tower of a fake is a
tower of honest groups, `ℤ[π]/(1 - π^n)`, of order `q^n + 1 - V_n` (`card_quotient_tower`). So the counts of a fake are perfectly good
counts, positive at every level, and this is why the tower cannot detect it.

What fails is that they are not quadratic. Call **the count law** the parallelogram law

  `K(φ + ψ) + K(φ - ψ) = 2 K(φ) + 2 K(ψ)`

for the count `K(x, y)` of the probe `y - x π`. Its first instance, at `φ = 1` and `ψ = π`, is

  `#G + #G' = 2(q + 1)`,

the conservation of channels that defines the graph: it holds on every black hole (`first_conservation`). **The law at all probes is
equivalent to universal damping** (`exists_countLaw_iff`, `probeCount_law_iff`): a function `K ≥ 0` with `K(1) = 1`, `K(π) = q`, `K(1 - π) = #G` and
the parallelogram law must be `𝒬` (`CountLaw.eq_kreinSquare`), and then `𝒬 ≥ 0`, so `t² ≤ 4q`. The statement does not mention `t` as a
parameter of the wave system: it uses only `q` and the number of cusps (`Channels.universal_iff_countLaw`). On a fake it breaks at the second
probe already (`fake_violates_second_probe`).

So the law on the graph that excludes the fakes exists. On a true curve `K` is the degree, the parallelogram law is the theorem of the cube, and
`K ≥ 0` because it is a count (`TheCountLawOfATrueCurve`, where this reproves Hasse's theorem). The three cases are the three ways the two properties can meet:

* a curve: `K` is a count and is quadratic;
* a fake: `K = |𝒬|` is a count and is not quadratic;
* `ℤ`: the Weil form is quadratic, and no count is known (`TheIntegerProbesOfTheHorizon`).
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### The law determines the form -/

/-- The parallelogram law for a count of probes. -/
def CountLaw (K : ℤ → ℤ → ℕ) : Prop :=
  ∀ x y u v, ((K (x + u) (y + v) : ℕ) : ℤ) + K (x - u) (y - v) = 2 * K x y + 2 * K u v

/-- A sequence with vanishing second difference, vanishing at `0` and `1`, vanishes. -/
theorem eq_zero_of_second_diff {g : ℤ → ℤ} (h : ∀ n, g (n + 1) + g (n - 1) = 2 * g n) (h0 : g 0 = 0)
    (h1 : g 1 = 0) (n : ℤ) : g n = 0 := by
  have up : ∀ m : ℕ, g m = 0 ∧ g (m + 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using ⟨h0, h1⟩
    | succ m ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have := h (m + 1)
      rw [show (m : ℤ) + 1 - 1 = m by ring, ih.1, ih.2] at this
      push_cast
      linarith
  have hm1 : g (-1) = 0 := by
    have := h 0
    simp only [zero_add, zero_sub, h0, h1] at this
    linarith
  have down : ∀ m : ℕ, g (-(m : ℤ)) = 0 ∧ g (-(m : ℤ) - 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using ⟨h0, hm1⟩
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [show -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 by push_cast; ring]
        exact ih.2
      · have := h (-(m : ℤ) - 1)
        rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih.1, ih.2] at this
        rw [show -((m + 1 : ℕ) : ℤ) - 1 = -(m : ℤ) - 1 - 1 by push_cast; ring]
        linarith
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact (up m).1
  · exact (down m).1

/-- **The count law forces the form.** A function with the parallelogram law and the values `K(1) = 1`, `K(π) = q`, `K(1 - π) = q + 1 - t` is the
Krein square. -/
theorem CountLaw.eq_kreinSquare {K : ℤ → ℤ → ℕ} (hK : CountLaw K) {q t : ℤ} (h01 : K 0 1 = 1)
    (h10 : (K 1 0 : ℤ) = q) (h11 : (K 1 1 : ℤ) = q + 1 - t) (x y : ℤ) :
    (K x y : ℤ) = kreinSquare q t x y := by
  set F : ℤ → ℤ → ℤ := fun x y => (K x y : ℤ) - kreinSquare q t x y with hF
  have hlaw (x y u v : ℤ) : F (x + u) (y + v) + F (x - u) (y - v) = 2 * F x y + 2 * F u v := by
    simp only [hF]
    have := hK x y u v
    unfold kreinSquare
    linarith [this, (by ring : ((y + v) ^ 2 - t * (x + u) * (y + v) + q * (x + u) ^ 2) +
      ((y - v) ^ 2 - t * (x - u) * (y - v) + q * (x - u) ^ 2) =
      2 * (y ^ 2 - t * x * y + q * x ^ 2) + 2 * (v ^ 2 - t * u * v + q * u ^ 2))]
  have hF01 : F 0 1 = 0 := by
    simp only [hF, h01]
    unfold kreinSquare
    simp
  have hF10 : F 1 0 = 0 := by
    simp only [hF, h10]
    unfold kreinSquare
    ring
  have hF11 : F 1 1 = 0 := by
    simp only [hF, h11]
    unfold kreinSquare
    ring
  have hF00 : F 0 0 = 0 := by
    have := hlaw 0 0 0 0
    simp only [add_zero, sub_zero] at this
    linarith
  have hzero (y : ℤ) : F 0 y = 0 := by
    refine eq_zero_of_second_diff (g := fun y => F 0 y) (fun n => ?_) hF00 hF01 y
    have := hlaw 0 n 0 1
    simp only [add_zero, sub_zero, hF01] at this
    linarith
  have hone (y : ℤ) : F 1 y = 0 := by
    refine eq_zero_of_second_diff (g := fun y => F 1 y) (fun n => ?_) hF10 hF11 y
    have := hlaw 1 n 0 1
    simp only [add_zero, sub_zero, hF01] at this
    linarith
  have hall : F x y = 0 := by
    refine eq_zero_of_second_diff (g := fun x => F x y) (fun n => ?_) (hzero y) (hone y) x
    have := hlaw n y 1 0
    simp only [add_zero, sub_zero, hF10] at this
    linarith
  simp only [hF] at hall
  linarith

theorem kreinSquare_cast (q t x y : ℤ) :
    ((kreinSquare q t x y : ℤ) : ℝ) = kreinSquare (q : ℝ) (t : ℝ) (x : ℝ) (y : ℝ) := by
  unfold kreinSquare
  push_cast
  ring

/-- **Channel conservation at every probe forces universal damping.** -/
theorem CountLaw.universal {K : ℤ → ℤ → ℕ} (hK : CountLaw K) {q t : ℤ} (h01 : K 0 1 = 1)
    (h10 : (K 1 0 : ℤ) = q) (h11 : (K 1 1 : ℤ) = q + 1 - t) : t ^ 2 ≤ 4 * q := by
  have h : ∀ m n : ℤ, 0 ≤ kreinSquare (q : ℝ) (t : ℝ) (n : ℝ) (m : ℝ) := by
    intro m n
    rw [← kreinSquare_cast, ← hK.eq_kreinSquare h01 h10 h11]
    positivity
  have := integer_kreinSquare_nonneg_iff.mp h
  exact_mod_cast this

/-- The norm form is nonnegative on the integers exactly under universal damping. -/
theorem kreinSquare_int_nonneg_iff (q t : ℤ) :
    (∀ x y : ℤ, 0 ≤ kreinSquare q t x y) ↔ t ^ 2 ≤ 4 * q := by
  have e : t ^ 2 ≤ 4 * q ↔ (t : ℝ) ^ 2 ≤ 4 * (q : ℝ) := by exact_mod_cast Iff.rfl
  rw [e, ← integer_kreinSquare_nonneg_iff]
  constructor
  · intro h m n
    rw [← kreinSquare_cast]
    exact_mod_cast h n m
  · intro h x y
    have := h y x
    rw [← kreinSquare_cast] at this
    exact_mod_cast this

/-- **The law exists exactly under universal damping.** -/
theorem exists_countLaw_iff (q t : ℤ) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 1 ∧ (K 1 0 : ℤ) = q ∧ (K 1 1 : ℤ) = q + 1 - t) ↔
      t ^ 2 ≤ 4 * q := by
  constructor
  · rintro ⟨K, hK, h01, h10, h11⟩
    exact hK.universal h01 h10 h11
  · intro h
    have hn := (kreinSquare_int_nonneg_iff q t).mpr h
    have hcast (x y : ℤ) : ((kreinSquare q t x y).natAbs : ℤ) = kreinSquare q t x y :=
      Int.natAbs_of_nonneg (hn x y)
    refine ⟨fun x y => (kreinSquare q t x y).natAbs, ?_, ?_, ?_, ?_⟩
    · intro x y u v
      simp only [hcast]
      unfold kreinSquare
      ring
    · simp [kreinSquare]
    · simp only [hcast]
      unfold kreinSquare
      ring
    · simp only [hcast]
      unfold kreinSquare
      ring

/-- **The law on the graph.** A black hole has universal damping exactly if the count of its channels extends to a count of all probes:
a function `K` with `K(1) = 1`, `K(π) = q`, `K(1 - π) = #G` and the parallelogram law. The statement uses only `q` and the number of
cusps. -/
theorem Channels.universal_iff_countLaw {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]
    (B : Channels G D) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 1 ∧ K 1 0 = B.q ∧ K 1 1 = Fintype.card G) ↔
      B.traceR ^ 2 ≤ 4 * (B.q : ℝ) := by
  have htr : B.traceR = (((B.q : ℤ) + 1 - (Fintype.card G : ℤ) : ℤ) : ℝ) := by
    unfold Channels.traceR
    push_cast
    ring
  have hiff : B.traceR ^ 2 ≤ 4 * (B.q : ℝ) ↔
      ((B.q : ℤ) + 1 - (Fintype.card G : ℤ)) ^ 2 ≤ 4 * (B.q : ℤ) := by
    rw [htr]
    exact_mod_cast Iff.rfl
  rw [hiff, ← exists_countLaw_iff]
  constructor
  · rintro ⟨K, hK, h01, h10, h11⟩
    refine ⟨K, hK, h01, by exact_mod_cast h10, ?_⟩
    rw [h11]
    ring
  · rintro ⟨K, hK, h01, h10, h11⟩
    refine ⟨K, hK, h01, by exact_mod_cast h10, ?_⟩
    have : (K 1 1 : ℤ) = (Fintype.card G : ℤ) := by
      rw [h11]
      ring
    exact_mod_cast this

/-! ### The ring of a black hole -/

/-- Multiplication by the probe `y - x π` on `ℤ[π]`, in the basis `1, π`. -/
def probeMatrix (q t x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![y, q * x; -x, y - t * x]

/-- **The Krein square is the norm of the probe.** -/
theorem det_probeMatrix (q t x y : ℤ) : (probeMatrix q t x y).det = kreinSquare q t x y := by
  rw [probeMatrix, Matrix.det_fin_two_of]
  unfold kreinSquare
  ring

/-- The ideal generated by the probe, as a lattice in `ℤ[π] = ℤ²`. -/
def probeLattice (q t x y : ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  LinearMap.range (Matrix.toLin' (probeMatrix q t x y))

/-- **A probe has `|𝒬|` points.** The quotient `ℤ[π]/(y - x π)` has `|𝒬(x, y)|` elements, for every black hole, true or fake. -/
theorem card_quotient_probeLattice {q t x y : ℤ} (h : kreinSquare q t x y ≠ 0) :
    Nat.card ((Fin 2 → ℤ) ⧸ probeLattice q t x y) = (kreinSquare q t x y).natAbs := by
  have hdet : (probeMatrix q t x y).det ≠ 0 := by rwa [det_probeMatrix]
  have hinj : Function.Injective (Matrix.toLin' (probeMatrix q t x y)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] probeLattice q t x y := LinearEquiv.ofInjective _ hinj
  have hmain := Submodule.natAbs_det_equiv (probeLattice q t x y) e
  have hcomp : (probeLattice q t x y).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e : (Fin 2 → ℤ) →+ probeLattice q t x y) =
      Matrix.toLin' (probeMatrix q t x y) := by
    ext v i
    rfl
  rw [hcomp, LinearMap.det_toLin', det_probeMatrix] at hmain
  exact hmain.symm

/-- The count of the probe `y - x π`: the number of elements of `ℤ[π]/(y - x π)`. -/
def probeCount (q t x y : ℤ) : ℕ := (kreinSquare q t x y).natAbs

/-- **The first instance of the law holds on every black hole**: `#G + #G' = 2(q + 1)`. -/
theorem first_conservation {q t : ℤ} (hq : 0 ≤ q) (ht : |t| ≤ q + 1) :
    (probeCount q t 1 1 : ℤ) + probeCount q t (-1) 1 = 2 * probeCount q t 0 1 + 2 * probeCount q t 1 0 := by
  have h := abs_le.mp ht
  have e1 : kreinSquare q t 1 1 = q + 1 - t := by
    unfold kreinSquare
    ring
  have e2 : kreinSquare q t (-1) 1 = q + 1 + t := by
    unfold kreinSquare
    ring
  have e3 : kreinSquare q t 0 1 = 1 := by
    unfold kreinSquare
    ring
  have e4 : kreinSquare q t 1 0 = q := by
    unfold kreinSquare
    ring
  simp only [probeCount, e1, e2, e3, e4]
  rw [Int.natAbs_of_nonneg (by linarith : 0 ≤ q + 1 - t), Int.natAbs_of_nonneg (by linarith : 0 ≤ q + 1 + t),
    Int.natAbs_of_nonneg hq]
  simp
  ring

/-- **The counts of the ring obey the law exactly under universal damping.** On a fake, `K = |𝒬|` is a count and is not quadratic. -/
theorem probeCount_law_iff {q t : ℤ} (hq : 0 ≤ q) (ht : |t| ≤ q + 1) :
    CountLaw (probeCount q t) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have h' := abs_le.mp ht
    refine h.universal (q := q) (t := t) ?_ ?_ ?_
    · simp [probeCount, kreinSquare]
    · simp only [probeCount]
      rw [show kreinSquare q t 1 0 = q by unfold kreinSquare; ring]
      exact Int.natAbs_of_nonneg hq
    · simp only [probeCount]
      rw [show kreinSquare q t 1 1 = q + 1 - t by unfold kreinSquare; ring]
      exact Int.natAbs_of_nonneg (by linarith)
  · intro h
    have hn := (kreinSquare_int_nonneg_iff q t).mpr h
    intro x y u v
    simp only [probeCount, Int.natAbs_of_nonneg (hn _ _)]
    unfold kreinSquare
    ring

/-- **A fake breaks the law at the second probe.** With three cusps and `q ≥ 9`, the count of `2 - π` is `q - 8`, and the law would need `8 - q`. -/
theorem fake_violates_second_probe {q : ℤ} (hq : 9 ≤ q) :
    let t := q - 2
    (probeCount q t 1 2 : ℤ) = q - 8 ∧
      ((probeCount q t 1 2 : ℤ) + probeCount q t 1 0 ≠ 2 * probeCount q t 1 1 + 2 * probeCount q t 0 1) := by
  intro t
  have e1 : kreinSquare q t 1 2 = 8 - q := by
    simp only [t]
    unfold kreinSquare
    ring
  have e2 : kreinSquare q t 1 0 = q := by
    unfold kreinSquare
    ring
  have e3 : kreinSquare q t 1 1 = 3 := by
    simp only [t]
    unfold kreinSquare
    ring
  have e4 : kreinSquare q t 0 1 = 1 := by
    unfold kreinSquare
    ring
  have h1 : ((8 - q).natAbs : ℤ) = q - 8 := by
    rw [Int.natAbs_eq_iff.mpr (Or.inr (show (8 - q) = -((q - 8).toNat : ℤ) by
      rw [Int.toNat_of_nonneg (by linarith)]; ring))]
    rw [Int.toNat_of_nonneg (by linarith)]
  simp only [probeCount, e1, e2, e3, e4]
  refine ⟨h1, ?_⟩
  rw [h1, Int.natAbs_of_nonneg (by linarith : 0 ≤ q)]
  simp
  omega

/-! ### The tower of a fake is a tower of groups -/

/-- The coefficient of `π` in `π^n`. -/
def powA (q t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * powA q t (n + 1) - q * powA q t n

/-- The constant term of `π^n`: `π^n = a_n π + b_n`. -/
def powB (q t : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -q * powA q t n

/-- The trace of `π^n`. -/
def powV (q t : ℤ) (n : ℕ) : ℤ := t * powA q t n + 2 * powB q t n

theorem powA_succ (q t : ℤ) (n : ℕ) : powA q t (n + 1) = t * powA q t n + powB q t n := by
  cases n with
  | zero => simp [powA, powB]
  | succ m =>
    show t * powA q t (m + 1) - q * powA q t m = t * powA q t (m + 1) + -q * powA q t m
    ring

/-- **The norm of `π^n` is `q^n`.** -/
theorem norm_pow (q t : ℤ) (n : ℕ) :
    powB q t n ^ 2 + t * powA q t n * powB q t n + q * powA q t n ^ 2 = q ^ n := by
  induction n with
  | zero => simp [powA, powB]
  | succ n ih =>
    rw [powA_succ, show powB q t (n + 1) = -q * powA q t n from rfl, pow_succ q n, ← ih]
    ring

/-- **The norm of `1 - π^n` is the point count of the tower.** -/
theorem kreinSquare_tower (q t : ℤ) (n : ℕ) :
    kreinSquare q t (powA q t n) (1 - powB q t n) = q ^ n + 1 - powV q t n := by
  have h := norm_pow q t n
  unfold kreinSquare powV
  linear_combination h

/-- The trace of `π^n` is the trace of the base change. -/
theorem powV_cast (q t : ℤ) (n : ℕ) : ((powV q t n : ℤ) : ℝ) = towerTrace (q : ℝ) (t : ℝ) n := by
  have hrec (n : ℕ) : powV q t (n + 2) = t * powV q t (n + 1) - q * powV q t n := by
    unfold powV
    rw [powA_succ q t (n + 1), powA_succ q t n,
      show powB q t (n + 2) = -q * powA q t (n + 1) from rfl,
      show powB q t (n + 1) = -q * powA q t n from rfl, powA_succ q t n]
    ring
  induction n using Nat.twoStepInduction with
  | zero => simp [powV, powA, powB, towerTrace]
  | one => simp [powV, powA, powB, towerTrace]
  | more n h0 h1 =>
    rw [hrec, towerTrace_add_two, ← h0, ← h1]
    push_cast
    ring

/-- **The tower of a fake is a tower of honest groups.** For every `|t| ≤ q` and `n ≥ 1`, the group `ℤ[π]/(1 - π^n)` has exactly
`q^n + 1 - V_n` elements. So a fake has a point count at every level, and these are counts of a real object. -/
theorem card_quotient_tower {q t : ℤ} (hq : 2 ≤ q) (ht : |t| ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.card ((Fin 2 → ℤ) ⧸ probeLattice q t (powA q t n) (1 - powB q t n)) : ℕ) : ℝ) =
      (q : ℝ) ^ n + 1 - towerTrace (q : ℝ) (t : ℝ) n := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ht' : |(t : ℝ)| ≤ q := by exact_mod_cast ht
  have hlt := abs_towerTrace_lt (by linarith : (1 : ℝ) < q) ht' (by omega : 0 < n)
  have hpos : (0 : ℝ) < (q : ℝ) ^ n + 1 - towerTrace (q : ℝ) (t : ℝ) n := by
    have := (abs_lt.mp hlt).2
    linarith
  have hcast : ((kreinSquare q t (powA q t n) (1 - powB q t n) : ℤ) : ℝ) =
      (q : ℝ) ^ n + 1 - towerTrace (q : ℝ) (t : ℝ) n := by
    rw [kreinSquare_tower]
    push_cast
    rw [powV_cast]
  have hne : kreinSquare q t (powA q t n) (1 - powB q t n) ≠ 0 := by
    intro h0
    rw [h0] at hcast
    push_cast at hcast
    linarith
  have hnn : 0 ≤ kreinSquare q t (powA q t n) (1 - powB q t n) := by
    have : (0 : ℝ) ≤ ((kreinSquare q t (powA q t n) (1 - powB q t n) : ℤ) : ℝ) := by
      rw [hcast]
      exact hpos.le
    exact_mod_cast this
  rw [card_quotient_probeLattice hne]
  have h1 : (((kreinSquare q t (powA q t n) (1 - powB q t n)).natAbs : ℤ) : ℝ) =
      ((kreinSquare q t (powA q t n) (1 - powB q t n) : ℤ) : ℝ) := by
    rw [Int.natAbs_of_nonneg hnn]
  rw [← hcast, ← h1]
  simp

end GaloisForLFunctions.ArithmeticScatteringHolography

end
