import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsWeighsTheZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGluingIndexIsTheSelfEnergyOfTheJets

/-!
# The normal form of the pairing of the degree points

A packet `f` sampled at the scale `N` gives the real divisor `Σ c_n γ_n` with `c_n = f_n/√n`: the
graph `Γ_n` in the unitary normalization, with the mass `1/n` of its cell. In these coordinates
the pairing of the degree points is one matrix on the positive integers, with no scale in it:

* off the diagonal `Γ_m · Γ_n = ½(1/|m − n| + 1/(m + n)) + Λ(n/m)`, the jet plus the contact, the
  contact present when `m` divides `n`;
* on the diagonal `Γ_n · Γ_n = −log(n/2π)`, the counterterm of the comb of the degree points;
* the degrees are `d₁ = Σ c_n/n` and `d₂ = Σ c_n`.

The pairing `combPairing S c` is defined for every finite set `S` of degree points and every real
vector `c`, at every finite scale.

* **The normal form is the pairing of the degree points** (`combPairing_sample`): on the window
  `N < n ≤ (1 + L)N` and on the samples of a packet that vanishes above the window it is jets plus
  twice the contacts minus the counterterm.
* **Zariski's lemma on a comb** (`combPairing_eq_potential_sub_dirichlet`): off the diagonal the
  matrix is nonnegative, so `D·D = Σ c_n² V(n) − ½ Σ_{m≠n} (c_m − c_n)² Γ_m·Γ_n`, with the
  potential `V(n)`: the row of `n` in `S` minus the counterterm.
* **The contacts below a point cancel the divergence of the counterterm**
  (`combPotential_eq_of_properDivisors_subset`): if `S` contains the proper divisors of `n`, then
  `V(n)` is the row of the jets plus the contacts above `n` plus `log 2π`.
* **The limit** (`tendsto_combForm_sample`): on the samples of a packet the form
  `2 d₁ d₂ − D·D` tends to the sum over the zeros.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### The entries -/

/-- The contact of `Γ_m` and `Γ_n` in the normal form: `Λ(n/m)` if `m` divides `n`, `Λ(m/n)` if
`n` divides `m`. -/
def contact (m n : ℕ) : ℝ :=
  (if m ∣ n then (Λ (n / m) : ℝ) else 0) + (if n ∣ m then (Λ (m / n) : ℝ) else 0)

theorem contact_comm (m n : ℕ) : contact m n = contact n m := add_comm _ _

theorem contact_nonneg (m n : ℕ) : 0 ≤ contact m n := by
  unfold contact
  refine add_nonneg ?_ ?_ <;> split_ifs <;>
    first | exact ArithmeticFunction.vonMangoldt_nonneg | exact le_rfl

/-- Below a degree point the contact is the von Mangoldt function of the quotient. -/
theorem contact_of_dvd_of_lt {m n : ℕ} (h : m ∣ n) (hmn : m < n) : contact m n = Λ (n / m) := by
  have hn : ¬ n ∣ m := fun h' => by
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by
      subst h0
      rw [zero_dvd_iff] at h
      omega
    exact absurd (Nat.le_of_dvd hm0 h') (by omega)
  rw [contact, if_pos h, if_neg hn, add_zero]

theorem jetKernel_nonneg (m n : ℕ) : 0 ≤ jetKernel m n := by
  unfold jetKernel
  positivity

/-- The pairing of two distinct degree points: the jet plus the contact. -/
def pairKernel (m n : ℕ) : ℝ := jetKernel m n + contact m n

theorem pairKernel_comm (m n : ℕ) : pairKernel m n = pairKernel n m := by
  rw [pairKernel, pairKernel, jetKernel_comm, contact_comm]

theorem pairKernel_nonneg (m n : ℕ) : 0 ≤ pairKernel m n :=
  add_nonneg (jetKernel_nonneg m n) (contact_nonneg m n)

/-- The counterterm of the comb of the degree points at `n`: `log(n/2π)`. -/
def counterterm (n : ℕ) : ℝ := Real.log ((n : ℝ) / (2 * Real.pi))

/-! ### The pairing, the degrees and the form -/

/-- The pairing of the real divisor `Σ_{n ∈ S} c_n γ_n` with itself. -/
def combPairing (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * pairKernel m n - ∑ n ∈ S, c n ^ 2 * counterterm n

/-- The first degree `d₁ = Σ c_n/n`. -/
def degOne (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ S, c n / n

/-- The second degree `d₂ = Σ c_n`. -/
def degTwo (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ S, c n

/-- Weil's form on the comb: `2 d₁ d₂ − D·D`. -/
def combForm (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := 2 * (degOne S c * degTwo S c) - combPairing S c

/-- The potential at `n`: the row of `n` in `S` minus the counterterm. -/
def combPotential (S : Finset ℕ) (n : ℕ) : ℝ := ∑ m ∈ S.erase n, pairKernel m n - counterterm n

/-- The Dirichlet form of the pairing on `S`. -/
def combDirichlet (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * pairKernel m n

theorem combDirichlet_nonneg (S : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ combDirichlet S c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (pairKernel_nonneg _ _)

/-! ### Zariski's lemma on a comb -/

/-- **Zariski's lemma on a comb.** The pairing is the potential on the squares minus half the
Dirichlet form. -/
theorem combPairing_eq_potential_sub_dirichlet (S : Finset ℕ) (c : ℕ → ℝ) :
    combPairing S c = ∑ n ∈ S, c n ^ 2 * combPotential S n - combDirichlet S c / 2 := by
  have h := sum_mul_mul_eq_row_sub_dirichlet S pairKernel pairKernel_comm c
  have hpot : ∑ n ∈ S, c n ^ 2 * combPotential S n =
      ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S.erase n, pairKernel m n - ∑ n ∈ S, c n ^ 2 * counterterm n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [combPotential, mul_sub]
  rw [combPairing, h, hpot, combDirichlet]
  ring

/-- The pairing is at most the potential on the squares. -/
theorem combPairing_le_potential (S : Finset ℕ) (c : ℕ → ℝ) :
    combPairing S c ≤ ∑ n ∈ S, c n ^ 2 * combPotential S n := by
  rw [combPairing_eq_potential_sub_dirichlet]
  linarith [combDirichlet_nonneg S c]

/-! ### The contacts below a degree point -/

/-- The contacts of `Γ_n` with the graphs of its proper divisors sum to `log n`. -/
theorem sum_contact_properDivisors {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ n.properDivisors, contact m n = Real.log n := by
  rw [← sum_vonMangoldt_div_properDivisors hn]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Nat.mem_properDivisors] at hm
  exact contact_of_dvd_of_lt hm.1 hm.2

/-- The row of the contacts in `S`: the divisors of `n` and the multiples of `n`. -/
theorem sum_contact_erase (S : Finset ℕ) (n : ℕ) :
    ∑ m ∈ S.erase n, contact m n =
      ∑ m ∈ (S.erase n).filter (· ∣ n), (Λ (n / m) : ℝ) +
        ∑ m ∈ (S.erase n).filter (n ∣ ·), (Λ (m / n) : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  rfl

/-- **The contacts below a point cancel the divergence of the counterterm.** If `S` contains the
proper divisors of `n`, the potential at `n` is the row of the jets, the contacts with the
multiples of `n` in `S`, and `log 2π`. -/
theorem combPotential_eq_of_properDivisors_subset {S : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hS : n.properDivisors ⊆ S) :
    combPotential S n = ∑ m ∈ S.erase n, jetKernel m n +
      ∑ m ∈ (S.erase n).filter (n ∣ ·), (Λ (m / n) : ℝ) + Real.log (2 * Real.pi) := by
  have hfilter : (S.erase n).filter (· ∣ n) = n.properDivisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hne, -⟩, hd⟩
      exact ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨⟨hlt.ne, hS (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)⟩, hd⟩
  have hlow : ∑ m ∈ (S.erase n).filter (· ∣ n), (Λ (n / m) : ℝ) = Real.log n := by
    rw [hfilter]
    exact sum_vonMangoldt_div_properDivisors hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : counterterm n = Real.log n - Real.log (2 * Real.pi) := by
    rw [counterterm, Real.log_div hn'.ne' (by positivity)]
  unfold combPotential pairKernel
  rw [Finset.sum_add_distrib, sum_contact_erase, hlow, hc]
  ring

/-! ### The normal form is the pairing of the degree points -/

/-- The coordinates of a packet sampled at the scale `N`: `c_n = f(log(n/N))/√n`. -/
def sampleCoord (f : ℝ → ℝ) (N n : ℕ) : ℝ := degreeSample f N n / Real.sqrt n

/-- The contacts of `Γ_m` with the graphs above it in the window. -/
theorem sum_contact_above (f : ℝ → ℝ) {L N m : ℕ}
    (hsupp : ∀ n : ℕ, N + L * N < n → degreeSample f N n = 0)
    (hm : m ∈ Ioc N (N + L * N)) :
    ∑ n ∈ (Ioc N (N + L * N)).erase m,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ k ∈ Icc 2 L, contactWeight k * (degreeSample f N m * degreeSample f N (m * k) / m) := by
  obtain ⟨hNm, hmtop⟩ := Finset.mem_Ioc.mp hm
  have hm0 : 0 < m := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  -- each term in the coordinates of the normal form
  have key : ∀ lam a b s r y : ℝ, 0 < s → 0 < r → s * s = y →
      lam / r * (a * b / y) = a / s * (b / (s * r)) * lam := by
    intro lam a b s r y hs hr hy
    subst hy
    field_simp
  have hterm : ∀ k ∈ Icc 2 L, contactWeight k *
        (degreeSample f N m * degreeSample f N (m * k) / m) =
      sampleCoord f N m * sampleCoord f N (m * k) * (Λ k : ℝ) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      have := (Finset.mem_Icc.mp hk).1
      exact_mod_cast (by omega : 0 < k)
    rw [contactWeight, sampleCoord, sampleCoord, Nat.cast_mul, Real.sqrt_mul hm'.le]
    exact key _ _ _ _ _ _ (Real.sqrt_pos.mpr hm') (Real.sqrt_pos.mpr hk0)
      (Real.mul_self_sqrt hm'.le)
  have hleft : ∑ n ∈ (Ioc N (N + L * N)).erase m,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ n ∈ ((Ioc N (N + L * N)).erase m).filter (m ∣ ·),
        sampleCoord f N m * sampleCoord f N n * (Λ (n / m) : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, hleft]
  have hright : ∑ k ∈ Icc 2 L, sampleCoord f N m * sampleCoord f N (m * k) * (Λ k : ℝ) =
      ∑ k ∈ (Icc 2 L).filter (fun k => m * k ∈ Ioc N (N + L * N)),
        sampleCoord f N m * sampleCoord f N (m * k) * (Λ k : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    split_ifs with h
    · rfl
    · have hk2 := (Finset.mem_Icc.mp hk).1
      have hgt : N + L * N < m * k := by
        by_contra hle
        refine h (Finset.mem_Ioc.mpr ⟨?_, not_lt.mp hle⟩)
        calc N < m := hNm
          _ ≤ m * k := Nat.le_mul_of_pos_right m (by omega)
      rw [show sampleCoord f N (m * k) = 0 by rw [sampleCoord, hsupp _ hgt, zero_div],
        mul_zero, zero_mul]
  rw [hright]
  refine Finset.sum_nbij' (fun n => n / m) (fun k => m * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hne, hnS⟩ := Finset.mem_erase.mp hn1
    obtain ⟨k, rfl⟩ := hd
    obtain ⟨hlow, htop⟩ := Finset.mem_Ioc.mp hnS
    rw [Nat.mul_div_cancel_left k hm0]
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (mul_one m)
    have hkL : k ≤ L := by
      by_contra hgt
      have h1 : (N + 1) * (L + 1) ≤ m * k := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hkL⟩, hnS⟩
  · intro k hk
    obtain ⟨hk1, hkS⟩ := Finset.mem_filter.mp hk
    have hk2 := (Finset.mem_Icc.mp hk1).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hkS⟩, dvd_mul_right m k⟩
    intro h
    have : m * k = m * 1 := by rw [h, mul_one]
    have := Nat.eq_of_mul_eq_mul_left hm0 this
    omega
  · intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  · intro k _
    exact Nat.mul_div_cancel_left k hm0
  · intro n hn
    obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp hn).2
    rw [Nat.mul_div_cancel_left k hm0]

/-- The jets of the normal form on the samples of a packet. -/
theorem sum_jets_sample (f : ℝ → ℝ) (L N : ℕ) :
    ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * jetKernel m n = degreePairing f L N := by
  have hpos : ∀ n ∈ Ioc N (N + L * N), (0 : ℝ) < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast (by omega : 0 < n)
  have key : ∀ a b j s t : ℝ, 0 < s → 0 < t → a / s * (b / t) * j = a * b * (j / (s * t)) := by
    intro a b j s t hs ht
    field_simp
  unfold degreePairing
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
  have hm' := hpos m (Finset.mem_of_mem_erase hm)
  have hn' := hpos n hn
  rw [sampleCoord, sampleCoord, levyKernel, Real.sqrt_mul hm'.le]
  exact key _ _ _ _ _ (Real.sqrt_pos.mpr hm') (Real.sqrt_pos.mpr hn')

/-- The contacts of the normal form on the samples of a packet: each pair is counted from its
lower point, twice. -/
theorem sum_contact_sample (f : ℝ → ℝ) {L N : ℕ}
    (hsupp : ∀ n : ℕ, N + L * N < n → degreeSample f N n = 0) :
    ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * contact m n = 2 * degreeContact f L N := by
  have hsplit : ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * contact m n =
      ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
          sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) +
        ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
          sampleCoord f N m * sampleCoord f N n * (if n ∣ m then (Λ (m / n) : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [contact, mul_add]
  have hswap : ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * (if n ∣ m then (Λ (m / n) : ℝ) else 0) =
      ∑ m ∈ Ioc N (N + L * N), ∑ n ∈ (Ioc N (N + L * N)).erase m,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) :=
    Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  have hswap' : ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      ∑ m ∈ Ioc N (N + L * N), ∑ n ∈ (Ioc N (N + L * N)).erase m,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) :=
    Finset.sum_comm' (s' := fun m => (Ioc N (N + L * N)).erase m) (t' := Ioc N (N + L * N))
      fun n m => by
        simp only [Finset.mem_erase]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
          fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩
  have hlower : ∑ m ∈ Ioc N (N + L * N), ∑ n ∈ (Ioc N (N + L * N)).erase m,
        sampleCoord f N m * sampleCoord f N n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
      degreeContact f L N := by
    unfold degreeContact
    rw [Finset.sum_congr rfl fun m hm => sum_contact_above f hsupp hm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  rw [hsplit, hswap, hswap', hlower]
  ring

/-- **The normal form is the pairing of the degree points.** On the window `N < n ≤ (1 + L)N`
and on the samples of a packet that vanishes above the window, the pairing of the divisor
`Σ (f_n/√n) γ_n` is jets plus twice the contacts minus the counterterm. -/
theorem combPairing_sample (f : ℝ → ℝ) {L N : ℕ}
    (hsupp : ∀ n : ℕ, N + L * N < n → degreeSample f N n = 0) :
    combPairing (Ioc N (N + L * N)) (sampleCoord f N) =
      degreeForm f L N + 2 * degreeContact f L N := by
  have hct : ∑ n ∈ Ioc N (N + L * N), sampleCoord f N n ^ 2 * counterterm n =
      ∑ n ∈ Ioc N (N + L * N),
        degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [sampleCoord, counterterm, div_pow, Real.sq_sqrt hn']
  have hsplit : ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        sampleCoord f N m * sampleCoord f N n * pairKernel m n =
      ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
          sampleCoord f N m * sampleCoord f N n * jetKernel m n +
        ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
          sampleCoord f N m * sampleCoord f N n * contact m n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [pairKernel, mul_add]
  rw [combPairing, hsplit, sum_jets_sample, sum_contact_sample f hsupp, hct, degreeForm]
  ring

/-! ### The limit on packets -/

variable {f : ℝ → ℝ}

/-- A packet supported below `log K` has no sample above the window of ratio `1 + 3K`. -/
theorem degreeSample_eq_zero_above {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {N : ℕ} (hN : 1 ≤ N) {n : ℕ}
    (hn : N + 3 * K * N < n) : degreeSample f N n = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlt : ((N + 3 * K * N : ℕ) : ℝ) < n := by exact_mod_cast hn
  push_cast at hlt
  have hKN : (0 : ℝ) ≤ K * N := mul_nonneg (by linarith) hN'.le
  show f (Real.log ((n : ℝ) / N)) = 0
  refine hsupp _ (Or.inr (Real.log_le_log (by linarith) ?_))
  rw [le_div_iff₀ hN']
  nlinarith

/-- **The pairing of the normal form on a packet** tends to twice the product of the degrees
minus the sum over the zeros. -/
theorem tendsto_combPairing_sample (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ}
    (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => combPairing (Ioc N (N + 3 * K * N)) (sampleCoord f N)) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f)) := by
  refine (tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (combPairing_sample f fun n hn => degreeSample_eq_zero_above hK hsupp hN hn).symm

/-- The integral of a function supported in the window. -/
theorem intervalIntegral_window_eq {G : ℝ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hG : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → G u = 0) :
    ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), G u = ∫ u, G u := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  refine intervalIntegral.integral_eq_integral_of_support_subset fun u hu => ?_
  rw [Function.mem_support] at hu
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hu (hG u (Or.inl (by linarith [not_lt.mp h])))
  · by_contra h
    refine hu (hG u (Or.inr ((Real.log_le_log (by linarith) ?_).trans (not_le.mp h).le)))
    push_cast
    linarith

/-- **The degrees of the normal form on a packet**: `d₁ d₂` tends to the product of the degrees
`∫ f e^{−u/2}` and `∫ f e^{u/2}`. -/
theorem tendsto_degOne_mul_degTwo_sample (hcont : Continuous f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degOne (Ioc N (N + 3 * K * N)) (sampleCoord f N) *
        degTwo (Ioc N (N + 3 * K * N)) (sampleCoord f N)) atTop
      (𝓝 ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) := by
  have hL : 1 ≤ 3 * K := by omega
  have hG1 : Continuous fun u : ℝ => f u * Real.exp (-u / 2) := by fun_prop
  have hG2 : Continuous fun u : ℝ => f u * Real.exp (u / 2) := by fun_prop
  have i1 : ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u * Real.exp (-u / 2) =
      ∫ u, f u * Real.exp (-u / 2) :=
    intervalIntegral_window_eq (G := fun u => f u * Real.exp (-u / 2)) hK fun u hu => by
      show f u * Real.exp (-u / 2) = 0
      rw [hsupp u hu, zero_mul]
  have i2 : ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u * Real.exp (u / 2) =
      ∫ u, f u * Real.exp (u / 2) :=
    intervalIntegral_window_eq (G := fun u => f u * Real.exp (u / 2)) hK fun u hu => by
      show f u * Real.exp (u / 2) = 0
      rw [hsupp u hu, zero_mul]
  have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (-Real.log ((n : ℝ) / N) / 2) / n) atTop
      (𝓝 (∫ u, f u * Real.exp (-u / 2))) := by
    rw [← i1]
    exact tendsto_degreeSum hG1 hL
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (Real.log ((n : ℝ) / N) / 2) / n) atTop
      (𝓝 (∫ u, f u * Real.exp (u / 2))) := by
    rw [← i2]
    exact tendsto_degreeSum hG2 hL
  have key1 : ∀ x s t y : ℝ, 0 < s → 0 < t → 0 < y → x * (s / t)⁻¹ / y = t * (x / s / y) := by
    intro x s t y hs ht hy
    field_simp
  have key2 : ∀ x s t y : ℝ, 0 < s → 0 < t → s * s = y → x * (s / t) / y = x / s / t := by
    intro x s t y hs ht hy
    subst hy
    field_simp
  refine (h1.mul h2).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN'
  have hexp : ∀ n : ℕ, 0 < n → Real.exp (Real.log ((n : ℝ) / N) / 2) = Real.sqrt n / Real.sqrt N :=
    fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← Real.sqrt_div hn'.le, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hn' hN')]
      congr 1
      ring
  have e1 : ∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (-Real.log ((n : ℝ) / N) / 2) / n =
      Real.sqrt N * degOne (Ioc N (N + 3 * K * N)) (sampleCoord f N) := by
    rw [degOne, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [neg_div, Real.exp_neg, hexp n hn0, sampleCoord, degreeSample]
    exact key1 _ _ _ _ (Real.sqrt_pos.mpr hn') hsN hn'
  have e2 : ∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (Real.log ((n : ℝ) / N) / 2) / n =
      degTwo (Ioc N (N + 3 * K * N)) (sampleCoord f N) / Real.sqrt N := by
    rw [degTwo, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [hexp n hn0, sampleCoord, degreeSample]
    exact key2 _ _ _ _ (Real.sqrt_pos.mpr hn') hsN (Real.mul_self_sqrt hn'.le)
  show (∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (-Real.log ((n : ℝ) / N) / 2) / n) *
      (∑ n ∈ Ioc N (N + 3 * K * N),
        f (Real.log ((n : ℝ) / N)) * Real.exp (Real.log ((n : ℝ) / N) / 2) / n) = _
  rw [e1, e2]
  field_simp

/-- **Weil's form on the comb tends to the sum over the zeros.** On the samples of a packet the
form `2 d₁ d₂ − D·D` of the normal form tends to `Z(f)`. -/
theorem tendsto_combForm_sample (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ}
    (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => combForm (Ioc N (N + 3 * K * N)) (sampleCoord f N)) atTop
      (𝓝 (zeroSum f)) := by
  have h1 := (tendsto_degOne_mul_degTwo_sample hf.continuous hK hsupp).const_mul 2
  have h2 := tendsto_combPairing_sample hf hfc hK hsupp
  have h := h1.sub h2
  rw [show 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
      (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f) =
      zeroSum f by ring] at h
  exact h

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
