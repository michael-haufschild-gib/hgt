import GaloisForLFunctions.BezoutValuationIncidence.NumeratorSplitOfTheWindowEnergy

/-!
# One-numerator clusters are short-interval sums

Fix a numerator `a ≥ 1` and a prime packet `c` on `S ⊆ (P, 2P]`, `2P ≤ N`, `M = N!`. The fractions
`a/p` are the `M`-th roots `ω^{a(M/p)}`, `ω = e^{2πi/M}`. In the discrete Gallagher inequality for
`Ψ_a(m) = Σ_p u(p, a) ω_p^{am}` the arc at `ω^x` collects the primes with `x ≤ a(M/p) < x + L`. If
`4PL ≤ aM`, i.e. the arc length `δ = L/M` is at most `a/(4P)`, the arcs never wrap. Each nonempty arc
then has `x ≥ aM/(4P)`, so its primes form the interval `(aM/(x+L), aM/x]` of length at most
`16P²L/(aM) = 16P²δ/a`, and only the arcs with `a(M/(2P)) < x + L`, `x < a(M/P)` are nonempty.
Hence, whenever every twisted interval sum

`|Σ_{p ∈ S, t₁ < p ≤ t₂} u(p, a) ω_p^{aX}|`,  `t₂ - t₁ ≤ 16P²L/(aM)`,

is at most `B`,

`Σ_{X ≤ m < X+K} |Ψ_a(m)|² ≤ (4M/L²)(a(M/(2P)) + L) B²`,  `4KL ≤ M`.

The conjugate numerator gives the same, since `Ψ_{-a} = conj Ψ_a`. With `δ ≍ 1/K` the factor is
`≍ K²a/P + K`. Twisted square-root cancellation `B² ≍ |c|²P²/(a³X)` over intervals of length
`≍ P²/(aX)` puts the window energy within a polylogarithm of the diagonal.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Roots of the common modulus -/

theorem stdRoot_eq_pow_of_dvd {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (hpM : p ∣ M) :
    stdRoot p = stdRoot M ^ (M / p) := by
  rw [stdRoot, stdRoot, ← Complex.exp_nat_mul]
  congr 1
  have hpR : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hMR : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  rw [Nat.cast_div hpM hpR]
  field_simp

theorem stdRoot_pow_mod {M : ℕ} (hM : 0 < M) (n : ℕ) : stdRoot M ^ n = stdRoot M ^ (n % M) := by
  have hω : IsPrimitiveRoot (stdRoot M) M := Complex.isPrimitiveRoot_exp M hM.ne'
  conv_lhs => rw [← Nat.mod_add_div n M, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]

theorem nthRootsFinset_eq_image {M : ℕ} (hM : 0 < M) :
    Polynomial.nthRootsFinset M (1 : ℂ) = (range M).image (fun x => stdRoot M ^ x) := by
  have hω : IsPrimitiveRoot (stdRoot M) M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hinj : Set.InjOn (fun x => stdRoot M ^ x) (range M : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro ξ hξ
    obtain ⟨x, _, rfl⟩ := mem_image.mp hξ
    rw [Polynomial.mem_nthRootsFinset hM, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  · rw [hω.card_nthRootsFinset, card_image_of_injOn hinj, card_range]

/-! ## §2. One arc -/

/-- The one-numerator frequencies `ω_p^a`, `p ∈ S`. -/
def numeratorFreqs (S : Finset ℕ) (a : ℕ) : Finset ℂ := S.image fun p => stdRoot p ^ a

theorem numeratorSum_eq {S : Finset ℕ} {a : ℕ} (hS : ∀ p ∈ S, p.Prime ∧ a ∈ Ico 1 p)
    (c : ℕ → ℝ) (m : ℕ) :
    numeratorSum S c a m = ∑ ζ ∈ numeratorFreqs S a, primeSpectrumCoeff c ζ * ζ ^ m := by
  rw [numeratorFreqs, sum_image]
  · refine sum_congr rfl fun p hp => ?_
    rw [primeSpectrumCoeff, orderOf_stdRoot_pow (hS p hp).1 (hS p hp).2, fareyCoeff]
  · intro p hp p' hp' h
    have h1 := orderOf_stdRoot_pow (hS p hp).1 (hS p hp).2
    have h2 := orderOf_stdRoot_pow (hS p' hp').1 (hS p' hp').2
    simp only at h
    rw [h] at h1
    exact h1.symm.trans h2

/-- **One arc.** Under no wrap (`L ≤ a(M/p) < M`), the arc at `ω^x` collects the primes with
`x ≤ a(M/p) < x + L`. -/
theorem arc_sum_eq {M a L X x : ℕ} {S : Finset ℕ} (hM : 0 < M)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M ∧ a ∈ Ico 1 p ∧ L ≤ a * (M / p) ∧ a * (M / p) < M)
    (hx : x < M) (c : ℕ → ℝ) :
    ∑ y ∈ range L, (if stdRoot M ^ x * stdRoot M ^ y ∈ numeratorFreqs S a then
        primeSpectrumCoeff c (stdRoot M ^ x * stdRoot M ^ y) *
          (stdRoot M ^ x * stdRoot M ^ y) ^ X else 0) =
      ∑ p ∈ S.filter (fun p => x ≤ a * (M / p) ∧ a * (M / p) < x + L),
        fareyCoeff c p a * (stdRoot p ^ a) ^ X := by
  classical
  have hω : IsPrimitiveRoot (stdRoot M) M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hroot : ∀ p ∈ S, stdRoot p ^ a = stdRoot M ^ (a * (M / p)) := fun p hp => by
    rw [stdRoot_eq_pow_of_dvd (hS p hp).1.pos hM (hS p hp).2.1, ← pow_mul, mul_comm]
  have hcoef : ∀ p ∈ S, primeSpectrumCoeff c (stdRoot p ^ a) = fareyCoeff c p a := fun p hp => by
    rw [primeSpectrumCoeff, orderOf_stdRoot_pow (hS p hp).1 (hS p hp).2.2.1, fareyCoeff]
  -- the index `a(M/p)` determines the prime
  have hinj : ∀ p ∈ S, ∀ p' ∈ S, a * (M / p) = a * (M / p') → p = p' := by
    intro p hp p' hp' h
    have ha : 0 < a := (mem_Ico.mp (hS p hp).2.2.1).1
    have h' : M / p = M / p' := Nat.eq_of_mul_eq_mul_left ha h
    have e1 := Nat.div_mul_cancel (hS p hp).2.1
    have e2 := Nat.div_mul_cancel (hS p' hp').2.1
    have hq : 0 < M / p := Nat.div_pos (Nat.le_of_dvd hM (hS p hp).2.1) (hS p hp).1.pos
    rw [h'] at e1
    exact Nat.eq_of_mul_eq_mul_left (by rwa [h'] at hq) (e1.trans e2.symm)
  -- each arc point: a root of the family iff it is `a(M/p)` for some `p`
  have hpt : ∀ y ∈ range L, (if stdRoot M ^ x * stdRoot M ^ y ∈ numeratorFreqs S a then
      primeSpectrumCoeff c (stdRoot M ^ x * stdRoot M ^ y) *
        (stdRoot M ^ x * stdRoot M ^ y) ^ X else 0) =
      ∑ p ∈ S, (if x + y = a * (M / p) then fareyCoeff c p a * (stdRoot p ^ a) ^ X else 0) := by
    intro y hy
    have hy' := mem_range.mp hy
    rw [← pow_add]
    by_cases hex : ∃ p ∈ S, x + y = a * (M / p)
    · obtain ⟨p, hp, hpe⟩ := hex
      have hmem : stdRoot M ^ (x + y) ∈ numeratorFreqs S a := by
        rw [hpe, ← hroot p hp]; exact mem_image_of_mem _ hp
      rw [if_pos hmem, sum_eq_single p (fun p' hp' hne =>
        if_neg fun h => hne (hinj p' hp' p hp (h.symm.trans hpe))) (fun h => absurd hp h),
        if_pos hpe, hpe, ← hroot p hp, hcoef p hp]
    · rw [sum_eq_zero fun p hp => if_neg fun h => hex ⟨p, hp, h⟩, if_neg]
      intro hmem
      obtain ⟨p, hp, hpe⟩ := mem_image.mp hmem
      rw [hroot p hp, stdRoot_pow_mod hM (x + y)] at hpe
      have hlt := (hS p hp).2.2.2.2
      have hmod := hω.pow_inj hlt (Nat.mod_lt _ hM) hpe
      rcases Nat.lt_or_ge (x + y) M with h | h
      · rw [Nat.mod_eq_of_lt h] at hmod
        exact hex ⟨p, hp, hmod.symm⟩
      · have hL := (hS p hp).2.2.2.1
        have : (x + y) % M = x + y - M := by
          rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        omega
  rw [sum_congr rfl hpt, sum_comm, sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases hin : x ≤ a * (M / p) ∧ a * (M / p) < x + L
  · rw [if_pos hin, sum_eq_single (a * (M / p) - x)
      (fun y _ hne => if_neg fun h => hne (by omega))
      (fun h => absurd (mem_range.mpr (by omega)) h), if_pos (by omega)]
  · rw [if_neg hin]
    refine sum_eq_zero fun y hy => if_neg fun h => hin ⟨by omega, by have := mem_range.mp hy; omega⟩

/-! ## §3. Clusters are short intervals -/

/-- **One numerator through its clusters.** For `S ⊆ (P, 2P]` primes, `1 ≤ P`, `2P ≤ N`,
`1 ≤ a ≤ P`, `1 ≤ L`, `4KL ≤ N!`, `4PL ≤ aN!`, if every twisted sum of `u(p, a) ω_p^{aX}` over
`p ∈ S ∩ (t₁, t₂]` with `t₂ - t₁ ≤ 16P²L/(aN!)` has norm at most `B`, then
`Σ_{X ≤ m < X+K} |Ψ_a(m)|² ≤ (4N!/L²)(a(N!/(2P)) + L) B²`. -/
theorem sum_numeratorSum_sq_le {N P K L a X : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P) (hP : 1 ≤ P) (hPN : 2 * P ≤ N) (ha : 1 ≤ a)
    (haP : a ≤ P) (hL : 1 ≤ L) (hKL : 4 * K * L ≤ N.factorial)
    (hPL : 4 * P * L ≤ a * N.factorial) (c : ℕ → ℝ) {B : ℝ}
    (hB : ∀ t₁ t₂ : ℝ, t₂ - t₁ ≤ 16 * (P : ℝ) ^ 2 * L / (a * N.factorial) →
      ‖∑ p ∈ S.filter (fun p : ℕ => t₁ < (p : ℝ) ∧ (p : ℝ) ≤ t₂),
        fareyCoeff c p a * (stdRoot p ^ a) ^ X‖ ≤ B) :
    ∑ j ∈ range K, ‖numeratorSum S c a (X + j)‖ ^ 2 ≤
      4 * N.factorial / (L : ℝ) ^ 2 * ((a * (N.factorial / (2 * P)) : ℕ) + L) * B ^ 2 := by
  classical
  set M := N.factorial
  have hM : 0 < M := Nat.factorial_pos N
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdvd : ∀ d, 0 < d → d ≤ N → d ∣ M := fun d h1 h2 => Nat.dvd_factorial h1 h2
  have h2P : 2 * P ∣ M := hdvd _ (by omega) hPN
  have hPd : P ∣ M := hdvd _ (by omega) (by omega)
  have hq2 : M / P = 2 * (M / (2 * P)) := by
    obtain ⟨t, ht⟩ := h2P
    have h1 : M / (2 * P) = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
    have h2 : M / P = 2 * t := by
      rw [ht, show 2 * P * t = P * (2 * t) by ring]; exact Nat.mul_div_cancel_left _ (by omega)
    rw [h1, h2]
  have hcast : ∀ d, d ∣ M → 0 < d → ((M / d : ℕ) : ℝ) = (M : ℝ) / d := fun d hd hd0 =>
    Nat.cast_div hd (by exact_mod_cast hd0.ne')
  -- facts about each prime of the packet
  have hpack : ∀ p ∈ S, p.Prime ∧ p ∣ M ∧ a ∈ Ico 1 p ∧ L ≤ a * (M / p) ∧ a * (M / p) < M := by
    intro p hp
    obtain ⟨hpr, hPp, hp2⟩ := hS p hp
    have hpM : p ∣ M := hdvd _ hpr.pos (by omega)
    refine ⟨hpr, hpM, mem_Ico.mpr ⟨ha, by omega⟩, ?_, ?_⟩
    · -- `L ≤ aM/(4P) ≤ a(M/p)`
      have h1 : (L : ℝ) ≤ a * M / (4 * P) := by
        rw [le_div_iff₀ (by positivity)]; exact_mod_cast (by nlinarith : L * (4 * P) ≤ a * M)
      have h2 : (a : ℝ) * M / (4 * P) ≤ ((a * (M / p) : ℕ) : ℝ) := by
        push_cast
        rw [hcast p hpM hpr.pos]
        have hpR : (p : ℝ) ≤ 2 * P := by exact_mod_cast hp2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
        rw [div_le_iff₀ (by positivity)]
        rw [show (a : ℝ) * (M / p) * (4 * P) = a * M * (4 * P) / p by field_simp]
        rw [le_div_iff₀ hp0]
        have ha0 : (0 : ℝ) ≤ a * M := by positivity
        nlinarith
      exact_mod_cast h1.trans h2
    · have hq := Nat.div_mul_cancel hpM
      have hlt : a < p := by omega
      nlinarith [Nat.div_pos (Nat.le_of_dvd hM hpM) hpr.pos]
  -- Gallagher over the one-numerator family
  have hT : ∀ ζ ∈ numeratorFreqs S a, ζ ^ M = 1 := by
    intro ζ hζ
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
    have hω : IsPrimitiveRoot (stdRoot p) p := Complex.isPrimitiveRoot_exp p (hpack p hp).1.ne_zero
    obtain ⟨t, ht⟩ := (hpack p hp).2.1
    rw [ht, ← pow_mul, show a * (p * t) = p * (a * t) by ring, pow_mul, hω.pow_eq_one, one_pow]
  have hgal := discrete_gallagher (A := X) hM hL hKL hT (primeSpectrumCoeff c)
  have hlhs : ∑ j ∈ range K, ‖∑ ζ ∈ numeratorFreqs S a, primeSpectrumCoeff c ζ * ζ ^ (X + j)‖ ^ 2 =
      ∑ j ∈ range K, ‖numeratorSum S c a (X + j)‖ ^ 2 :=
    sum_congr rfl fun j _ => by
      rw [numeratorSum_eq (fun p hp => ⟨(hpack p hp).1, (hpack p hp).2.2.1⟩)]
  rw [hlhs] at hgal
  have hω : IsPrimitiveRoot (stdRoot M) M := Complex.isPrimitiveRoot_exp M hM.ne'
  have hinj : Set.InjOn (fun x => stdRoot M ^ x) (range M : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  rw [nthRootsFinset_eq_image hM, sum_image hinj] at hgal
  set cl : ℕ → ℂ := fun x => ∑ p ∈ S.filter (fun p => x ≤ a * (M / p) ∧ a * (M / p) < x + L),
    fareyCoeff c p a * (stdRoot p ^ a) ^ X
  have harc : ∀ x ∈ range M, ‖∑ y ∈ range L, (if stdRoot M ^ x * stdRoot M ^ y ∈ numeratorFreqs S a
      then primeSpectrumCoeff c (stdRoot M ^ x * stdRoot M ^ y) *
        (stdRoot M ^ x * stdRoot M ^ y) ^ X else 0)‖ ^ 2 = ‖cl x‖ ^ 2 := fun x hx => by
    rw [arc_sum_eq hM hpack (mem_range.mp hx)]
  rw [sum_congr rfl harc] at hgal
  -- each cluster is a short interval, and only few arcs carry one
  set lo := a * (M / (2 * P)) + 1 - L
  set hi := a * (M / P)
  have hcl : ∀ x ∈ range M, ‖cl x‖ ^ 2 ≤ if x ∈ Ico lo hi then B ^ 2 else 0 := by
    intro x _
    by_cases hne : (S.filter (fun p => x ≤ a * (M / p) ∧ a * (M / p) < x + L)).Nonempty
    · obtain ⟨p, hpf⟩ := hne
      obtain ⟨hp, hpx, hpxL⟩ := mem_filter.mp hpf
      obtain ⟨hpr, hPp, hp2⟩ := hS p hp
      have hpM := (hpack p hp).2.1
      -- the arc lies in the counted range
      have hq_le : M / (2 * P) ≤ M / p := Nat.div_le_div_left hp2 hpr.pos
      have hq_lt : M / p < M / P := by
        have e1 := Nat.div_mul_cancel hpM
        have e2 := Nat.div_mul_cancel hPd
        by_contra hcon
        rw [not_lt] at hcon
        have : M / P * P < M / p * p := by
          calc M / P * P ≤ M / p * P := Nat.mul_le_mul_right _ hcon
            _ < M / p * p := Nat.mul_lt_mul_of_pos_left hPp (Nat.div_pos (Nat.le_of_dvd hM hpM)
              hpr.pos)
        omega
      have hxr : x ∈ Ico lo hi := by
        refine mem_Ico.mpr ⟨?_, ?_⟩
        · have := Nat.mul_le_mul_left a hq_le; omega
        · have := Nat.mul_lt_mul_of_pos_left hq_lt ha; omega
      rw [if_pos hxr]
      -- the cluster is a twisted interval sum
      -- `x > aM/(4P)`
      have h2L : 2 * L ≤ a * (M / (2 * P)) := by
        have e := Nat.div_mul_cancel h2P
        have : 2 * L * (2 * P) ≤ a * (M / (2 * P)) * (2 * P) := by
          rw [show a * (M / (2 * P)) * (2 * P) = a * M by rw [mul_assoc, e]]; nlinarith
        exact Nat.le_of_mul_le_mul_right this (by omega)
      have hxL : L < x := by
        have := Nat.mul_le_mul_left a hq_le; omega
      have hxR : (a : ℝ) * M / (4 * P) < x := by
        have h1 : (a : ℝ) * M / (2 * P) = ((a * (M / (2 * P)) : ℕ) : ℝ) := by
          push_cast; rw [hcast _ h2P (by omega)]; push_cast; ring
        have h3 : ((a * (M / (2 * P)) : ℕ) : ℝ) < x + L := by
          have := Nat.mul_le_mul_left a hq_le
          exact_mod_cast (by omega : a * (M / (2 * P)) < x + L)
        have h4 : (2 : ℝ) * L ≤ ((a * (M / (2 * P)) : ℕ) : ℝ) := by exact_mod_cast h2L
        have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
        rw [div_lt_iff₀ (by positivity)]
        have : (a : ℝ) * M = 2 * P * ((a * (M / (2 * P)) : ℕ) : ℝ) := by
          rw [← h1]; field_simp
        rw [this]
        nlinarith
      have hx0R : (0 : ℝ) < x := lt_of_le_of_lt (by positivity) hxR
      -- the cluster as an interval sum
      set t₁ : ℝ := (a : ℝ) * M / ((x : ℝ) + L)
      set t₂ : ℝ := (a : ℝ) * M / x
      have hfilt : S.filter (fun p => x ≤ a * (M / p) ∧ a * (M / p) < x + L) =
          S.filter (fun p : ℕ => t₁ < (p : ℝ) ∧ (p : ℝ) ≤ t₂) := by
        refine filter_congr fun q hq => ?_
        have hqM := (hpack q hq).2.1
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (hpack q hq).1.pos
        have hqc : ((a * (M / q) : ℕ) : ℝ) = (a : ℝ) * M / q := by
          push_cast; rw [hcast q hqM (hpack q hq).1.pos]; ring
        constructor
        · rintro ⟨h1, h2⟩
          have h1' : (x : ℝ) ≤ (a : ℝ) * M / q := by rw [← hqc]; exact_mod_cast h1
          have h2' : (a : ℝ) * M / q < x + L := by rw [← hqc]; exact_mod_cast h2
          constructor
          · rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hq0] at h2'; linarith
          · rw [le_div_iff₀ hx0R]
            rw [le_div_iff₀ hq0] at h1'; linarith
        · rintro ⟨h1, h2⟩
          have h1' : (a : ℝ) * M / q < x + L := by
            rw [div_lt_iff₀ (by positivity)] at h1; rw [div_lt_iff₀ hq0]; linarith
          have h2' : (x : ℝ) ≤ (a : ℝ) * M / q := by
            rw [le_div_iff₀ hx0R] at h2; rw [le_div_iff₀ hq0]; linarith
          constructor
          · have : (x : ℝ) ≤ ((a * (M / q) : ℕ) : ℝ) := by rw [hqc]; exact h2'
            exact_mod_cast this
          · have : ((a * (M / q) : ℕ) : ℝ) < ((x + L : ℕ) : ℝ) := by rw [hqc]; push_cast; exact h1'
            exact_mod_cast this
      have hlen : t₂ - t₁ ≤ 16 * (P : ℝ) ^ 2 * L / (a * M) := by
        have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
        have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
        have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        have hdiff : t₂ - t₁ = (a : ℝ) * M * L / (x * (x + L)) := by
          simp only [t₁, t₂]; field_simp; ring
        rw [hdiff, div_le_div_iff₀ (by positivity) (by positivity)]
        have hx4 : (a : ℝ) * M < 4 * P * x := by
          rw [div_lt_iff₀ (by positivity)] at hxR; linarith
        have hsq : ((a : ℝ) * M) ^ 2 ≤ (4 * P * x) ^ 2 := pow_le_pow_left₀ (by positivity) hx4.le 2
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ L),
          mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (a : ℝ) * M) hL0) hx0R.le]
      have hBx := hB t₁ t₂ hlen
      rw [← hfilt] at hBx
      exact pow_le_pow_left₀ (norm_nonneg _) hBx 2
    · rw [not_nonempty_iff_eq_empty] at hne
      have : cl x = 0 := by simp only [cl, hne, sum_empty]
      rw [this, norm_zero, zero_pow two_ne_zero]
      split_ifs <;> positivity
  have hcount : ∑ x ∈ range M, ‖cl x‖ ^ 2 ≤ ((a * (M / (2 * P)) : ℕ) + L) * B ^ 2 := by
    calc ∑ x ∈ range M, ‖cl x‖ ^ 2 ≤ ∑ x ∈ range M, (if x ∈ Ico lo hi then B ^ 2 else 0) :=
          sum_le_sum hcl
      _ ≤ ∑ x ∈ Ico lo hi, B ^ 2 := by
          rw [← sum_filter]
          exact sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.mp hx).2)
            fun _ _ _ => sq_nonneg _
      _ = (hi - lo : ℕ) * B ^ 2 := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ((a * (M / (2 * P)) : ℕ) + L) * B ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have e : a * (M / P) = 2 * (a * (M / (2 * P))) := by rw [hq2]; ring
          have : hi - lo ≤ a * (M / (2 * P)) + L := by
            simp only [hi, lo, e]; omega
          exact_mod_cast this
  calc ∑ j ∈ range K, ‖numeratorSum S c a (X + j)‖ ^ 2
      ≤ 4 * M / (L : ℝ) ^ 2 * ∑ x ∈ range M, ‖cl x‖ ^ 2 := hgal
    _ ≤ 4 * M / (L : ℝ) ^ 2 * (((a * (M / (2 * P)) : ℕ) + L) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-! ## §4. The conjugate numerator -/

/-- `Ψ_{-a} = conj Ψ_a`: the numerators `a` and `p - a` give conjugate one-numerator sums. -/
theorem conjNumeratorSum_eq_conj {S : Finset ℕ} {a : ℕ} (hS : ∀ p ∈ S, 0 < p ∧ a ≤ p) (c : ℕ → ℝ)
    (m : ℕ) : conjNumeratorSum S c a m = conj (numeratorSum S c a m) := by
  rw [conjNumeratorSum, numeratorSum, map_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hp0, hap⟩ := hS p hp
  have hω : IsPrimitiveRoot (stdRoot p) p := Complex.isPrimitiveRoot_exp p hp0.ne'
  have hn : ‖stdRoot p ^ a‖ = 1 := by rw [stdRoot_pow, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hne : stdRoot p ^ a ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hrefl : stdRoot p ^ (p - a) = conj (stdRoot p ^ a) := by
    rw [← Complex.inv_eq_conj hn]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, Nat.sub_add_cancel hap, hω.pow_eq_one]
  rw [fareyCoeff, fareyCoeff, hrefl]
  generalize stdRoot p ^ a = z
  rw [map_mul, map_mul, map_pow, map_div₀, map_sub, map_one, Complex.conj_ofReal]

theorem norm_conjNumeratorSum {S : Finset ℕ} {a : ℕ} (hS : ∀ p ∈ S, 0 < p ∧ a ≤ p) (c : ℕ → ℝ)
    (m : ℕ) : ‖conjNumeratorSum S c a m‖ = ‖numeratorSum S c a m‖ := by
  rw [conjNumeratorSum_eq_conj hS, Complex.norm_conj]

end

end GaloisForLFunctions.BezoutValuationIncidence
