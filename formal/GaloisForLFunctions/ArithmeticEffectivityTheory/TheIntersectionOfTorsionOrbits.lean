import GaloisForLFunctions.ArithmeticEffectivityTheory.TheLogEnergyOfRootsOfUnity

/-!
# The intersection of torsion orbits: `Λ` as an intersection number

The primitive roots of unity of order `m` form one Galois orbit `O_m` on the characteristic circle.
The **archimedean intersection** of two orbits is
`I(m, n) = Σ_{ζ ∈ O_m} Σ_{η ∈ O_n} log |ζ − η|`, the logarithm of the absolute value of the resultant
of `Φ_m` and `Φ_n`.

* **The intersection law** (`orbitIntersection_eq`). For `m ≠ n`,
  `I(m, n) = φ(n) Λ(m/n)` if `n ∣ m`, `φ(m) Λ(n/m)` if `m ∣ n`, and `0` otherwise
  (Apostol's resultant theorem). The proof inverts the closed form
  `J(a, b) = gcd(a, b) log lcm(a, b)` of the energy of `μ_a` against `μ_b` in both variables
  (`orbitIntersection_eq_sum`), and evaluates the double Möbius sum through
  `gcd(a, b) = Σ_{e ∣ a, e ∣ b} φ(e)` (`sum_moebius_mul_sum_divisors_gcd`).
* **The Hecke law** (`orbitIntersection_hecke`). `I(m, m t) = φ(m) Λ(t)`: an orbit meets its image
  under the Hecke correspondence of degree `t` in `Λ(t)` per point, the same for every `m`.

So the von Mangoldt function — the Lefschetz number of the prime comb — is an intersection number of
torsion cycles on the characteristic circle, computed by integers (cyclotomic resultants) and
equivariant along the Hecke action. The arithmetic of the explicit formula's prime side is an
intersection theory on `ℝ/ℤ` that no Beurling system carries: it uses the lattice `ℤ ⊂ ℝ`.
-/

noncomputable section

open Polynomial Finset Complex
open scoped Real ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The archimedean intersection `I(m, n) = Σ_{ζ ∈ O_m, η ∈ O_n} log |ζ − η|` of two torsion orbits. -/
def orbitIntersection (m n : ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, Real.log ‖ζ - η‖

/-- The energy of `μ_a` against `μ_b` is the sum of the orbit intersections. -/
theorem logEnergy_eq_sum_orbitIntersection (a b : ℕ) :
    logEnergy a b = ∑ m ∈ a.divisors, ∑ n ∈ b.divisors, orbitIntersection m n := by
  simp only [logEnergy, orbitIntersection, sum_nthRoots_eq_sum_divisors_real]
  exact sum_congr rfl fun m _ => sum_comm

/-- Möbius inversion in the form used below. -/
theorem sum_divisors_moebius_eq_of {f g : ℕ → ℝ} (h : ∀ b > 0, ∑ e ∈ b.divisors, f e = g b)
    {n : ℕ} (hn : 0 < n) : ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * g b = f n := by
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp h) n hn
  rwa [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * g b)] at this

/-- `Σ_{c ∣ k} μ(k/c) = [k = 1]`. -/
theorem sum_divisors_moebius {k : ℕ} (hk : 0 < k) :
    ∑ c ∈ k.divisors, (μ (k / c) : ℝ) = if k = 1 then 1 else 0 := by
  have := sum_divisors_moebius_eq_of (f := fun i => if i = 1 then (1 : ℝ) else 0)
    (g := fun _ => 1) (fun b hb => by simp [hb.ne']) hk
  simpa using this

/-- `Σ_{c ∣ k} μ(k/c) log c = Λ(k)`. -/
theorem sum_divisors_moebius_log {k : ℕ} (hk : 0 < k) :
    ∑ c ∈ k.divisors, (μ (k / c) : ℝ) * Real.log c = Λ k :=
  sum_divisors_moebius_eq_of (f := fun i => Λ i) (g := fun b => Real.log b)
    (fun _ _ => ArithmeticFunction.vonMangoldt_sum) hk

/-- The Möbius transform in both variables, `Σ_{b ∣ n} μ(n/b) Σ_{a ∣ m} μ(m/a) X(a, b)`. -/
def doubleMoebius (m n : ℕ) (X : ℕ → ℕ → ℝ) : ℝ :=
  ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * X a b

theorem doubleMoebius_swap (m n : ℕ) (X : ℕ → ℕ → ℝ) :
    doubleMoebius m n X =
      ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * X a b := by
  simp only [doubleMoebius, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem doubleMoebius_congr {m n : ℕ} {X Y : ℕ → ℕ → ℝ}
    (h : ∀ a ∈ m.divisors, ∀ b ∈ n.divisors, X a b = Y a b) :
    doubleMoebius m n X = doubleMoebius m n Y :=
  sum_congr rfl fun b hb => congrArg _ (sum_congr rfl fun a ha => by rw [h a ha b hb])

theorem doubleMoebius_add_sub (m n : ℕ) (X Y Z : ℕ → ℕ → ℝ) :
    doubleMoebius m n (fun a b => X a b + Y a b - Z a b) =
      doubleMoebius m n X + doubleMoebius m n Y - doubleMoebius m n Z := by
  simp only [doubleMoebius, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]

/-- **Double Möbius inversion**: `I(m, n)` is the double Möbius transform of the energy `J`. -/
theorem orbitIntersection_eq_doubleMoebius {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    orbitIntersection m n = doubleMoebius m n logEnergy :=
  (sum_divisors_moebius_eq_of (f := fun n' => orbitIntersection m n')
    (g := fun b => ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * logEnergy a b)
    (fun b _ => (sum_divisors_moebius_eq_of
      (f := fun m' => ∑ e ∈ b.divisors, orbitIntersection m' e) (g := fun a => logEnergy a b)
      (fun a _ => (logEnergy_eq_sum_orbitIntersection a b).symm) hm).symm) hn).symm

/-- `{e ∣ b : e ∣ a}` is the set of divisors of `gcd(a, b)`. -/
theorem filter_divisors_dvd_eq {a b : ℕ} (hb : 0 < b) :
    b.divisors.filter (· ∣ a) = (Nat.gcd a b).divisors := by
  ext e
  simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  have : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_right a hb).ne'
  constructor
  · rintro ⟨⟨heb, -⟩, hea⟩; exact ⟨⟨hea, heb⟩, this⟩
  · rintro ⟨⟨hea, heb⟩, -⟩; exact ⟨⟨heb, hb.ne'⟩, hea⟩

/-- **The gcd kernel**: `Σ_{b ∣ n} μ(n/b) Σ_{e ∣ gcd(a, b)} h(e) = [n ∣ a] h(n)`. -/
theorem sum_moebius_mul_sum_divisors_gcd (h : ℕ → ℝ) (a : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ e ∈ (Nat.gcd a b).divisors, h e =
      if n ∣ a then h n else 0 :=
  sum_divisors_moebius_eq_of (f := fun e => if e ∣ a then h e else 0) (fun b hb => by
    rw [← sum_filter, filter_divisors_dvd_eq hb]) hn

/-- `Σ_{b ∣ n} μ(n/b) gcd(a, b) = [n ∣ a] φ(n)`, from `k = Σ_{e ∣ k} φ(e)`. -/
theorem sum_moebius_mul_gcd (a : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * (Nat.gcd a b : ℝ) =
      if n ∣ a then (Nat.totient n : ℝ) else 0 := by
  refine Eq.trans ?_ (sum_moebius_mul_sum_divisors_gcd (fun e => (Nat.totient e : ℝ)) a hn)
  refine sum_congr rfl fun b _ => ?_
  rw [show (Nat.gcd a b : ℝ) = ∑ e ∈ (Nat.gcd a b).divisors, (Nat.totient e : ℝ) by
    exact_mod_cast (Nat.sum_totient (Nat.gcd a b)).symm]

/-- The Möbius transform of `k ↦ k log k`. -/
def kLogKernel (e : ℕ) : ℝ :=
  ∑ d ∈ e.divisors, (μ (e / d) : ℝ) * ((d : ℝ) * Real.log d)

theorem mul_log_eq_sum_kLogKernel {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * Real.log k = ∑ e ∈ k.divisors, kLogKernel e :=
  ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := kLogKernel)
    (g := fun k => (k : ℝ) * Real.log k)).mpr (fun n _ => by
      rw [kLogKernel, ← Nat.sum_divisorsAntidiagonal' (fun a b =>
        (μ a : ℝ) * ((b : ℝ) * Real.log b))]) k hk).symm

/-- `Σ_{b ∣ n} μ(n/b) g log g = [n ∣ a] K(n)` for `g = gcd(a, b)`. -/
theorem sum_moebius_mul_gcd_log (a : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ((Nat.gcd a b : ℝ) * Real.log (Nat.gcd a b)) =
      if n ∣ a then kLogKernel n else 0 := by
  refine Eq.trans ?_ (sum_moebius_mul_sum_divisors_gcd kLogKernel a hn)
  refine sum_congr rfl fun b hb => ?_
  rw [mul_log_eq_sum_kLogKernel (Nat.gcd_pos_of_pos_right a (Nat.pos_of_mem_divisors hb))]

/-- Restriction to the multiples of `n`:
`Σ_{a ∣ m} μ(m/a) [n ∣ a] F(a) = [n ∣ m] Σ_{c ∣ m/n} μ((m/n)/c) F(n c)`. -/
theorem sum_moebius_ite_dvd {m n : ℕ} (hm : 0 < m) (F : ℕ → ℝ) :
    ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * (if n ∣ a then F a else 0) =
      if n ∣ m then ∑ c ∈ (m / n).divisors, (μ ((m / n) / c) : ℝ) * F (n * c) else 0 := by
  split_ifs with hnm
  · obtain ⟨k, rfl⟩ := hnm
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [Nat.mul_div_cancel_left k hn]
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    refine sum_nbij' (fun a => a / n) (fun c => n * c) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, Nat.mem_divisors] at ha ⊢
      obtain ⟨⟨had, -⟩, c, rfl⟩ := ha
      rw [Nat.mul_div_cancel_left c hn]
      exact ⟨(Nat.mul_dvd_mul_iff_left hn).mp had, hk.ne'⟩
    · intro c hc
      simp only [mem_filter, Nat.mem_divisors] at hc ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left n hc.1, (Nat.mul_pos hn hk).ne'⟩, dvd_mul_right n c⟩
    · intro a ha
      simp only [mem_filter] at ha
      exact Nat.mul_div_cancel' ha.2
    · intro c _; exact Nat.mul_div_cancel_left c hn
    · intro a ha
      simp only [mem_filter] at ha
      obtain ⟨c, rfl⟩ := ha.2
      rw [Nat.mul_div_cancel_left c hn, Nat.mul_div_mul_left k c hn]
  · refine sum_eq_zero fun a ha => ?_
    rw [if_neg fun hna => hnm (hna.trans (Nat.dvd_of_mem_divisors ha)), mul_zero]

/-- `Σ_{a ∣ m, n ∣ a} μ(m/a) log a = [n ∣ m] (Λ(m/n) + [m = n] log n)`. -/
theorem sum_moebius_dvd_log {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * (if n ∣ a then Real.log a else 0) =
      if n ∣ m then Λ (m / n) + (if m = n then Real.log n else 0) else 0 := by
  simp only [sum_moebius_ite_dvd hm]
  by_cases hnm : n ∣ m
  · rw [if_pos hnm, if_pos hnm]
    obtain ⟨k, rfl⟩ := hnm
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [Nat.mul_div_cancel_left k hn]
    have : ∀ c ∈ k.divisors, (μ (k / c) : ℝ) * Real.log ((n * c : ℕ) : ℝ) =
        Real.log n * (μ (k / c) : ℝ) + (μ (k / c) : ℝ) * Real.log c := by
      intro c hc
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn.ne')
        (by exact_mod_cast (Nat.pos_of_mem_divisors hc).ne')]
      ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, sum_divisors_moebius hk,
      sum_divisors_moebius_log hk]
    by_cases h1 : k = 1
    · subst h1; simp
    · have : n * k ≠ n := fun h => h1 (Nat.eq_of_mul_eq_mul_left hn (h.trans (mul_one n).symm))
      rw [if_neg h1, if_neg this]; ring
  · rw [if_neg hnm, if_neg hnm]

theorem doubleMoebius_gcd_mul_log_left {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    doubleMoebius m n (fun a b => (Nat.gcd a b : ℝ) * Real.log a) =
      (Nat.totient n : ℝ) * if n ∣ m then Λ (m / n) + (if m = n then Real.log n else 0) else 0 := by
  rw [doubleMoebius_swap, ← sum_moebius_dvd_log hm hn, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have : ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ((Nat.gcd a b : ℝ) * Real.log a) =
      Real.log a * ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * (Nat.gcd a b : ℝ) := by
    rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  rw [this, sum_moebius_mul_gcd a hn]
  split_ifs <;> ring

theorem doubleMoebius_gcd_mul_log_right {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    doubleMoebius m n (fun a b => (Nat.gcd a b : ℝ) * Real.log b) =
      (Nat.totient m : ℝ) * if m ∣ n then Λ (n / m) + (if n = m then Real.log m else 0) else 0 := by
  rw [doubleMoebius, ← sum_moebius_dvd_log hn hm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have : ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * ((Nat.gcd a b : ℝ) * Real.log b) =
      Real.log b * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * (Nat.gcd b a : ℝ) := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by rw [Nat.gcd_comm]; ring
  rw [this, sum_moebius_mul_gcd b hm]
  split_ifs <;> ring

theorem doubleMoebius_gcd_mul_log_gcd {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    doubleMoebius m n (fun a b => (Nat.gcd a b : ℝ) * Real.log (Nat.gcd a b)) =
      if m = n then kLogKernel n else 0 := by
  rw [doubleMoebius_swap]
  simp only [sum_moebius_mul_gcd_log _ hn, sum_moebius_ite_dvd hm]
  by_cases hnm : n ∣ m
  · rw [if_pos hnm, ← sum_mul]
    obtain ⟨k, rfl⟩ := hnm
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [Nat.mul_div_cancel_left k hn, sum_divisors_moebius hk]
    by_cases h1 : k = 1
    · subst h1; simp
    · have : n * k ≠ n := fun h => h1 (Nat.eq_of_mul_eq_mul_left hn (h.trans (mul_one n).symm))
      rw [if_neg h1, if_neg this, zero_mul]
  · rw [if_neg hnm, if_neg fun h : m = n => hnm (h ▸ dvd_rfl)]

/-- `gcd(a, b) log lcm(a, b) = g log a + g log b − g log g`. -/
theorem gcd_mul_log_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (Nat.gcd a b : ℝ) * Real.log (Nat.lcm a b) = (Nat.gcd a b : ℝ) * Real.log a +
      (Nat.gcd a b : ℝ) * Real.log b - (Nat.gcd a b : ℝ) * Real.log (Nat.gcd a b) := by
  have hg : (0 : ℝ) < Nat.gcd a b := by exact_mod_cast Nat.gcd_pos_of_pos_left b ha
  have hl : (Nat.lcm a b : ℝ) = a * b / Nat.gcd a b := by
    rw [Nat.lcm, Nat.cast_div (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) b) hg.ne']
    push_cast; ring
  rw [hl, Real.log_div (by positivity) hg.ne', Real.log_mul (by positivity) (by positivity)]
  ring

/-- **The intersection formula** for all pairs of orbits. -/
theorem orbitIntersection_formula {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    orbitIntersection m n =
      (Nat.totient n : ℝ) * (if n ∣ m then Λ (m / n) + (if m = n then Real.log n else 0) else 0) +
      (Nat.totient m : ℝ) * (if m ∣ n then Λ (n / m) + (if n = m then Real.log m else 0) else 0) -
      (if m = n then kLogKernel n else 0) := by
  rw [orbitIntersection_eq_doubleMoebius hm hn,
    doubleMoebius_congr (Y := fun a b => (Nat.gcd a b : ℝ) * Real.log a +
      (Nat.gcd a b : ℝ) * Real.log b - (Nat.gcd a b : ℝ) * Real.log (Nat.gcd a b))
      (fun a ha b hb => by
        rw [logEnergy_eq (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb),
          gcd_mul_log_lcm (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)]),
    doubleMoebius_add_sub, doubleMoebius_gcd_mul_log_left hm hn,
    doubleMoebius_gcd_mul_log_right hm hn, doubleMoebius_gcd_mul_log_gcd hm hn]

/-- **The intersection law** (Apostol's resultant theorem): distinct orbits meet in
`φ(n) Λ(m/n)` when `n ∣ m`, in `φ(m) Λ(n/m)` when `m ∣ n`, and in `0` otherwise. -/
theorem orbitIntersection_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    orbitIntersection m n =
      if n ∣ m then (Nat.totient n : ℝ) * Λ (m / n)
      else if m ∣ n then (Nat.totient m : ℝ) * Λ (n / m) else 0 := by
  rw [orbitIntersection_formula hm hn]
  by_cases hnm : n ∣ m
  · have hmn' : ¬ m ∣ n := fun h => hmn (Nat.dvd_antisymm h hnm)
    simp [hnm, hmn', hmn]
  · by_cases hmn' : m ∣ n
    · simp [hnm, hmn', hmn, Ne.symm hmn]
    · simp [hnm, hmn', hmn]

/-- **The Hecke law**: an orbit meets its image under the degree-`t` Hecke correspondence in
`Λ(t)` per point, `I(m, m t) = φ(m) Λ(t)`. -/
theorem orbitIntersection_hecke {m t : ℕ} (hm : 0 < m) (ht : 1 < t) :
    orbitIntersection m (m * t) = (Nat.totient m : ℝ) * Λ t := by
  have hne : m ≠ m * t := fun h => by
    have := Nat.eq_of_mul_eq_mul_left hm (h.symm.trans (mul_one m).symm); omega
  have hndvd : ¬ m * t ∣ m := fun h => by
    have := Nat.le_of_dvd hm h
    nlinarith
  rw [orbitIntersection_eq hm (by positivity) hne, if_neg hndvd, if_pos (dvd_mul_right m t),
    Nat.mul_div_cancel_left t hm]

/-- **The self-intersection**: `I(n, n) = 2 φ(n) log n − Σ_{d ∣ n} μ(n/d) d log d`, the logarithm of
the discriminant of `Φ_n`. -/
theorem orbitIntersection_self {n : ℕ} (hn : 0 < n) :
    orbitIntersection n n = 2 * (Nat.totient n : ℝ) * Real.log n - kLogKernel n := by
  rw [orbitIntersection_formula hn hn]
  simp only [dvd_refl, if_true, Nat.div_self hn, ArithmeticFunction.vonMangoldt_apply_one, zero_add]
  ring

end GaloisForLFunctions.ArithmeticEffectivityTheory
