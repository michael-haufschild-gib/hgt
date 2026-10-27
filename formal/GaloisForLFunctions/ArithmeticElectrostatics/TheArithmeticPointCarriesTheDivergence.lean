import GaloisForLFunctions.ArithmeticElectrostatics.TheTorsionCountertermIsLogarithmic

/-!
# The arithmetic point carries the divergence

The arithmetic point `z = 1` of the characteristic circle is the orbit `O_1`: one charge, fixed by
every power map. Its interaction with the orbit of order `n ≥ 2` is `I(1, n) = Λ(n)` — the von
Mangoldt function is the potential of `O_n` at the arithmetic point. This file shows that the
divergence of the diagonal renormalization of the torsion pairing is carried by that point.

* **The arithmetic point** (`eq_one_of_forall_pow_eq_self`, `orbitIntersection_one_left`):
  `1` is the only point of the unit circle fixed by every power map, and `I(1, n) = Λ(n)`.
* **Self-intersections are nonnegative** (`orbitIntersection_self_nonneg`): the local correction
  never exceeds the degree term, so `I(n, n) = log |disc Φ_n| ≥ 0`.
* **The divergence sits at the arithmetic point** (`le_counterterm_one`): if a counterterm
  `c(n) > 0` per point renormalizes the orders `≤ N`, then
  `c(1) ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/(c(n) φ(n))`. The single charge at `z = 1` meets every prime-power
  orbit, and the renormalized energy restricted to the test `y_1 = 1`, `y_n = Λ(n)/(c(n)φ(n))`
  is the Cauchy–Schwarz defect of that meeting.
* **Constant counterterms** (`sq_le_of_renormalizesAt`, `log_two_mul_le_sq_of_renormalizesAt`):
  `κ² ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/φ(n) ≥ log 2 · (log N − log 4 − 4)`, so the arithmetic point alone
  forces `κ → ∞`.

A counterterm bounded on the orbits of order `≥ 2` must therefore diverge at `O_1`: the
renormalization of the diagonal is a statement about the potential at the arithmetic point, the
same point at which `ψ(N) = Σ log |1 − ζ|` over the Farey torsion is RH.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory

/-! ### The arithmetic point -/

/-- **The arithmetic point**: a point of the unit circle fixed by the squaring map is `1`. -/
theorem eq_one_of_forall_pow_eq_self {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ t : ℕ, 1 ≤ t → z ^ t = z) :
    z = 1 := by
  have h2 := h 2 (by norm_num)
  have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; exact zero_ne_one hz
  have : z * (z - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact absurd h0 hz0
  · exact sub_eq_zero.mp h1

/-- The orbit of order `1` is the arithmetic point. -/
theorem primitiveRoots_one : primitiveRoots 1 ℂ = {1} := by
  ext ζ
  rw [mem_primitiveRoots one_pos, IsPrimitiveRoot.one_right_iff, mem_singleton]

/-- `Λ(n)` is the interaction of the arithmetic point with the orbit of order `n`. -/
theorem orbitIntersection_one_left {n : ℕ} (hn : 2 ≤ n) : orbitIntersection 1 n = Λ n := by
  have := orbitIntersection_hecke (m := 1) (t := n) one_pos hn
  rw [one_mul, Nat.totient_one, Nat.cast_one, one_mul] at this
  exact this

/-- The arithmetic point does not interact with itself. -/
theorem orbitIntersection_one_one : orbitIntersection 1 1 = 0 := by
  simp [orbitIntersection, primitiveRoots_one]

/-! ### Nonnegative self-intersections -/

/-- The local correction never exceeds the degree term: `D(n) ≤ φ(n) log n`. -/
theorem localCorrection_le {n : ℕ} (hn : 0 < n) :
    localCorrection n ≤ (Nat.totient n : ℝ) * Real.log n := by
  rw [localCorrection, mul_apply, ← vonMangoldt_sum, mul_sum,
    ← Nat.sum_divisorsAntidiagonal' (fun a b => (Nat.totient n : ℝ) * Λ a)]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (Nat.totient n : ℝ) * Λ a)] at *
  rw [← Nat.sum_divisorsAntidiagonal (fun a b => totientR a * Λ b),
    ← Nat.sum_divisorsAntidiagonal' (fun a b => (Nat.totient n : ℝ) * Λ a)]
  refine sum_le_sum fun x hx => ?_
  obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [totientR_apply]
  refine mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
  exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hn)
    (Nat.totient_dvd_of_dvd ⟨x.2, hmul.symm⟩)

/-- **Self-intersections are nonnegative**: `I(n, n) = log |disc Φ_n| ≥ 0`. -/
theorem orbitIntersection_self_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ orbitIntersection n n := by
  rw [orbitIntersection_self_eq hn]
  linarith [localCorrection_le hn]

/-! ### The divergence at the arithmetic point -/

/-- A counterterm `c(n)` per point **renormalizes** the orders `≤ N` when
`Σ y_m y_n I(m, n) ≤ Σ c(n) φ(n) y_n²` for every configuration. -/
def RenormalizesWith (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ y : ℕ → ℝ, torsionPairing N y ≤ ∑ n ∈ Icc 1 N, c n * Nat.totient n * y n ^ 2

/-- **The divergence sits at the arithmetic point**:
`c(1) ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/(c(n) φ(n))` for every renormalizing counterterm. -/
theorem le_counterterm_one {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℝ} (hc : ∀ n ∈ Icc 2 N, 0 < c n)
    (h : RenormalizesWith N c) :
    ∑ n ∈ Icc 2 N, Λ n ^ 2 / (c n * Nat.totient n) ≤ c 1 := by
  set A := ∑ n ∈ Icc 2 N, Λ n ^ 2 / (c n * Nat.totient n)
  set y : ℕ → ℝ := fun n => if n = 1 then 1 else Λ n / (c n * Nat.totient n)
  set S := Icc 1 N
  have h1S : 1 ∈ S := mem_Icc.mpr ⟨le_rfl, hN⟩
  have hSe : S.erase 1 = Icc 2 N := by
    ext n; simp only [mem_erase, mem_Icc, S]; omega
  have hden : ∀ n ∈ Icc 2 N, 0 < c n * Nat.totient n := fun n hn =>
    mul_pos (hc n hn) (by exact_mod_cast Nat.totient_pos.mpr (by have := (mem_Icc.mp hn).1; omega))
  have hy0 : ∀ n ∈ S, 0 ≤ y n := by
    intro n hn
    by_cases h1 : n = 1
    · simp [y, h1]
    · have hn2 : n ∈ Icc 2 N := by rw [← hSe]; exact mem_erase.mpr ⟨h1, hn⟩
      simp only [y, if_neg h1]
      exact div_nonneg vonMangoldt_nonneg (hden n hn2).le
  have hI : ∀ m ∈ S, ∀ n ∈ S, 0 ≤ orbitIntersection m n := by
    intro m hm n hn
    by_cases hmn : m = n
    · rw [hmn]; exact orbitIntersection_self_nonneg (mem_Icc.mp hn).1
    · exact orbitIntersection_nonneg_of_ne (mem_Icc.mp hm).1 (mem_Icc.mp hn).1 hmn
  have hF : ∀ m ∈ S, ∀ n ∈ S, 0 ≤ y m * y n * orbitIntersection m n := fun m hm n hn =>
    mul_nonneg (mul_nonneg (hy0 m hm) (hy0 n hn)) (hI m hm n hn)
  -- the row and the column of the arithmetic point
  have hrow : ∀ n ∈ Icc 2 N, y 1 * y n * orbitIntersection 1 n = Λ n ^ 2 / (c n * Nat.totient n) :=
    fun n hn => by
      have hn1 : n ≠ 1 := by have := (mem_Icc.mp hn).1; omega
      simp only [y, if_pos rfl, if_neg hn1, one_mul, orbitIntersection_one_left (mem_Icc.mp hn).1]
      ring
  have hlow : 2 * A ≤ torsionPairing N y := by
    rw [torsionPairing, ← add_sum_erase S _ h1S, ← add_sum_erase S _ h1S, hSe]
    have hcol : ∑ m ∈ Icc 2 N, y m * y 1 * orbitIntersection m 1 ≤
        ∑ m ∈ Icc 2 N, ∑ n ∈ S, y m * y n * orbitIntersection m n := by
      refine sum_le_sum fun m hm => ?_
      have hmS : m ∈ S := by rw [← hSe] at hm; exact mem_of_mem_erase hm
      exact single_le_sum (fun n hn => hF m hmS n hn) h1S
    have hcol' : ∑ m ∈ Icc 2 N, y m * y 1 * orbitIntersection m 1 = A := by
      refine sum_congr rfl fun m hm => ?_
      rw [orbitIntersection_comm, mul_comm (y m), hrow m hm]
    rw [orbitIntersection_one_one, mul_zero, zero_add, sum_congr rfl hrow]
    linarith
  have hup : torsionPairing N y ≤ c 1 + A := by
    refine (h y).trans (le_of_eq ?_)
    rw [← add_sum_erase S _ h1S, hSe]
    simp only [y, if_pos rfl, Nat.totient_one, Nat.cast_one, mul_one, one_pow]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn1 : n ≠ 1 := by have := (mem_Icc.mp hn).1; omega
    rw [if_neg hn1]
    have := (hden n hn).ne'
    field_simp
    ring
  linarith

/-- A constant counterterm `κ` satisfies `κ² ≥ Σ_{2 ≤ n ≤ N} Λ(n)²/φ(n)`. -/
theorem sq_le_of_renormalizesAt {N : ℕ} (hN : 3 ≤ N) {κ : ℝ} (h : RenormalizesAt N κ) :
    ∑ n ∈ Icc 2 N, Λ n ^ 2 / Nat.totient n ≤ κ ^ 2 := by
  -- `κ > 0`, from the orbit of the prime `3`
  have h3 := le_of_renormalizesAt_prime h Nat.prime_three hN
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hκ : 0 < κ := by norm_num at h3; linarith
  have hc : RenormalizesWith N fun _ => κ := fun y => by
    have := h y
    rw [selfMass, mul_sum] at this
    exact this.trans (le_of_eq (sum_congr rfl fun n _ => by ring))
  have := le_counterterm_one (by omega) (fun n _ => hκ) hc
  rw [show (∑ n ∈ Icc 2 N, Λ n ^ 2 / (κ * Nat.totient n)) =
      (∑ n ∈ Icc 2 N, Λ n ^ 2 / Nat.totient n) / κ by
    rw [sum_div]; exact sum_congr rfl fun n _ => by rw [div_div, mul_comm]] at this
  rw [div_le_iff₀ hκ] at this
  nlinarith

/-- `Λ(n)² ≥ log 2 · Λ(n)`: a nonzero value of `Λ` is the logarithm of a prime. -/
theorem log_two_mul_le_vonMangoldt_sq (n : ℕ) : Real.log 2 * Λ n ≤ Λ n ^ 2 := by
  by_cases h : IsPrimePow n
  · have hval : Λ n = Real.log (n.minFac) := by rw [vonMangoldt_apply, if_pos h]
    have hge : Real.log 2 ≤ Λ n := by
      rw [hval]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.minFac_prime h.ne_one).two_le)
    nlinarith [vonMangoldt_nonneg (n := n)]
  · rw [vonMangoldt_eq_zero_iff.mpr h]; simp

/-- **The arithmetic point forces divergence**: a constant counterterm renormalizing the orders
`≤ N` satisfies `κ² ≥ log 2 · (log N − log 4 − 4)`. -/
theorem log_two_mul_le_sq_of_renormalizesAt {N : ℕ} (hN : 3 ≤ N) {κ : ℝ}
    (h : RenormalizesAt N κ) :
    Real.log 2 * (Real.log N - (Real.log 4 + 4)) ≤ κ ^ 2 := by
  refine le_trans ?_ (sq_le_of_renormalizesAt hN h)
  -- Mertens' lower bound for `Σ Λ(n)/n`
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first N (by omega))).1
  have hsplit : ∑ d ∈ Icc 1 N, Λ d / d = ∑ d ∈ Icc 2 N, Λ d / d := by
    rw [← add_sum_erase (Icc 1 N) _ (mem_Icc.mpr ⟨le_rfl, by omega⟩)]
    rw [vonMangoldt_apply_one, zero_div, zero_add]
    exact sum_congr (by ext n; simp only [mem_erase, mem_Icc]; omega) fun _ _ => rfl
  have hterm : ∀ n ∈ Icc 2 N, Real.log 2 * (Λ n / n) ≤ Λ n ^ 2 / Nat.totient n := by
    intro n hn
    have hn2 := (mem_Icc.mp hn).1
    have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφn : (Nat.totient n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
    rw [← mul_div_assoc]
    calc Real.log 2 * Λ n / n ≤ Λ n ^ 2 / n :=
          div_le_div_of_nonneg_right (log_two_mul_le_vonMangoldt_sq n) (by positivity)
      _ ≤ Λ n ^ 2 / Nat.totient n := div_le_div_of_nonneg_left (sq_nonneg _) hφ hφn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc Real.log 2 * (Real.log N - (Real.log 4 + 4))
      ≤ Real.log 2 * ∑ d ∈ Icc 2 N, Λ d / d := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left (by linarith) hlog2.le
    _ = ∑ d ∈ Icc 2 N, Real.log 2 * (Λ d / d) := mul_sum _ _ _
    _ ≤ ∑ n ∈ Icc 2 N, Λ n ^ 2 / Nat.totient n := sum_le_sum hterm

end GaloisForLFunctions.ArithmeticElectrostatics
