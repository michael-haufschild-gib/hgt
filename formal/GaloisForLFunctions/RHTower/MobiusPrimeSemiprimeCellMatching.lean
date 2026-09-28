import GaloisForLFunctions.RHTower.PrimeCellPartition

/-!
# Complete prime-layer compensation by nearby semiprimes

Fix `B > 0`.  Split `(R, 2R]` into `J = ⌊(log R)^B⌋` cells of width `h = R/J ≤ 2R/(log R)^B`.
In each cell the primes number at most `(101/100) h/log R`, while the semiprimes `qr`,
`q ∈ {2, 3, 5}`, `r > 5` prime, number at least `(99/100)(1/2 + 1/3 + 1/5) h/log R`.  A cellwise
injection therefore sends every prime `p ∈ (R, 2R]` to a squarefree semiprime `φ(p) = qr` of its own
cell, so `|φ(p) - p| ≤ 2R/(log R)^B`.  The signs are literal, `μ(p) = -1`, `μ(φ(p)) = 1`, and the
band Lipschitz law gives, uniformly in `0 ≤ δ ≤ 1`,

`‖∑_p (f_{φ(p)} - f_p)‖_δ² ≤ C R^{1-δ}/(log R)^{2B+2}`.                         (1)
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.PrimeCells

open RHTower.CubicGamma

/-- The semiprimes `qr ∈ (u, v]`, `q ∈ {2, 3, 5}`, `r` prime. -/
def semiprimeTargets (u v : ℝ) : Finset ℕ :=
  ({2, 3, 5} : Finset ℕ).biUnion fun q => (windowPrimes (u / q) (v / q)).image (q * ·)

theorem small_cofactor_cases {q : ℕ} (hq : q ∈ ({2, 3, 5} : Finset ℕ)) :
    q.Prime ∧ 2 ≤ q ∧ q ≤ 5 := by
  have hq' : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
  rcases hq' with h | h | h <;> subst h <;> norm_num

/-- A window prime above `u/q ≥ 6` exceeds `5`, and `qr ∈ (u, v]`. -/
theorem windowPrimes_div_facts {u v : ℝ} (hu : 30 ≤ u) (huv : u ≤ v) {q r : ℕ}
    (hq : q ∈ ({2, 3, 5} : Finset ℕ)) (hr : r ∈ windowPrimes (u / q) (v / q)) :
    r.Prime ∧ 5 < r ∧ u < (q * r : ℕ) ∧ ((q * r : ℕ) : ℝ) ≤ v := by
  obtain ⟨-, hq2, hq5⟩ := small_cofactor_cases hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
  obtain ⟨hrp, hlt, hle⟩ := (mem_windowPrimes (by positivity)
    (div_nonneg (by linarith) hq0.le)).mp hr
  rw [div_lt_iff₀ hq0] at hlt
  rw [le_div_iff₀ hq0] at hle
  have h5 : (5 : ℝ) < r := by
    by_contra h
    push Not at h
    have : (r : ℝ) * q ≤ 5 * 5 := by gcongr
    linarith
  exact ⟨hrp, by exact_mod_cast h5, by push_cast; linarith, by push_cast; linarith⟩

theorem mem_semiprimeTargets {u v : ℝ} (hu : 30 ≤ u) (huv : u ≤ v) {n : ℕ}
    (hn : n ∈ semiprimeTargets u v) :
    ∃ q r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧ n = q * r ∧ u < n ∧ (n : ℝ) ≤ v := by
  unfold semiprimeTargets at hn
  obtain ⟨q, hq, hn⟩ := mem_biUnion.mp hn
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hn
  obtain ⟨hrp, h5, hlt, hle⟩ := windowPrimes_div_facts hu huv hq hr
  exact ⟨q, r, by simpa using hq, hrp, h5, rfl, hlt, hle⟩

/-- The three families are disjoint (the prime factor `≤ 5` is `q`), so the target count is
`∑_{q ∈ {2,3,5}} #{r ∈ (u/q, v/q]}`. -/
theorem card_semiprimeTargets {u v : ℝ} (hu : 30 ≤ u) (huv : u ≤ v) :
    (semiprimeTargets u v).card =
      ∑ q ∈ ({2, 3, 5} : Finset ℕ), (windowPrimes (u / q) (v / q)).card := by
  unfold semiprimeTargets
  rw [card_biUnion]
  · refine sum_congr rfl fun q hq => card_image_of_injOn fun r _ r' _ h => ?_
    exact Nat.eq_of_mul_eq_mul_left (small_cofactor_cases hq).1.pos h
  · intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hn
    obtain ⟨r', hr', h⟩ := mem_image.mp hn'
    obtain ⟨hqp, -, hq5⟩ := small_cofactor_cases hq
    obtain ⟨hqp', -, hq5'⟩ := small_cofactor_cases hq'
    obtain ⟨hrp, h5, -⟩ := windowPrimes_div_facts hu huv hq hr
    obtain ⟨hrp', h5', -⟩ := windowPrimes_div_facts hu huv hq' hr'
    exact hne (prime_eq_of_mul_eq hqp' hrp' hqp hrp (by omega) (by omega) h).symm

/-- `(99/100)(1/2 + 1/3 + 1/5) > 101/100`: the semiprime supply beats the prime demand. -/
theorem semiprimeTargets_card_ge {u v L : ℝ} (hu : 30 ≤ u) (huv : u ≤ v) (hL : 0 < L)
    (hlow : ∀ q : ℕ, q ∈ ({2, 3, 5} : Finset ℕ) →
      (1 - 1 / 100) * (v - u) / (q * L) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ)) :
    (1 + 1 / 100) * (v - u) / L ≤ ((semiprimeTargets u v).card : ℝ) := by
  rw [card_semiprimeTargets hu huv]
  push_cast
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have h2 := hlow 2 (by decide)
  have h3 := hlow 3 (by decide)
  have h5 := hlow 5 (by decide)
  push_cast at h2 h3 h5
  have hvu : 0 ≤ v - u := by linarith
  have e : (1 - 1 / 100) * (v - u) / (2 * L) + (1 - 1 / 100) * (v - u) / (3 * L) +
      (1 - 1 / 100) * (v - u) / (5 * L) = 3069 / 3000 * ((v - u) / L) := by
    field_simp; ring
  have e2 : (1 + 1 / 100) * (v - u) / L = 3030 / 3000 * ((v - u) / L) := by ring
  have hq : 0 ≤ (v - u) / L := by positivity
  nlinarith

/-- **Energy of a matched family.**  If `X ≤ N · 4 C_1 (2R/L^B) R^{-(3+δ)/2}` and
`N ≤ W R/L`, then `X² ≤ 64 C_1² W² R^{1-δ}/L^{2B+2}`. -/
theorem matched_energy_sq_le {R L B W N X c δ : ℝ} (hR : 0 < R) (hL : 0 < L) (hc : 0 ≤ c)
    (hN : N ≤ W * R / L) (hX0 : 0 ≤ X)
    (hX : X ≤ N * (4 * c * (2 * R / L ^ B) * R ^ (-(3 + δ) / 2))) :
    X ^ 2 ≤ 64 * c ^ 2 * W ^ 2 * R ^ (1 - δ) / L ^ (2 * B + 2) := by
  have hLB : 0 < L ^ B := Real.rpow_pos_of_pos hL B
  have hRδ : 0 ≤ R ^ (-(3 + δ) / 2) := Real.rpow_nonneg hR.le _
  have e1 : R * R * R ^ (-(3 + δ) / 2) = R ^ ((1 - δ) / 2) := by
    rw [show R * R = R ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_add hR]; ring_nf
  have e2 : (R ^ ((1 - δ) / 2)) ^ 2 = R ^ (1 - δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; ring_nf
  have e3 : (L * L ^ B) ^ 2 = L ^ (2 * B + 2) := by
    rw [mul_pow, ← Real.rpow_natCast (L ^ B), ← Real.rpow_mul hL.le, ← Real.rpow_two,
      ← Real.rpow_add hL]
    push_cast; ring_nf
  have hY : X ≤ 8 * c * W * (R ^ ((1 - δ) / 2) / (L * L ^ B)) := by
    calc X ≤ N * (4 * c * (2 * R / L ^ B) * R ^ (-(3 + δ) / 2)) := hX
      _ ≤ W * R / L * (4 * c * (2 * R / L ^ B) * R ^ (-(3 + δ) / 2)) := by gcongr
      _ = 8 * c * W * (R * R * R ^ (-(3 + δ) / 2) / (L * L ^ B)) := by field_simp; ring
      _ = 8 * c * W * (R ^ ((1 - δ) / 2) / (L * L ^ B)) := by rw [e1]
  calc X ^ 2 ≤ (8 * c * W * (R ^ ((1 - δ) / 2) / (L * L ^ B))) ^ 2 := by gcongr
    _ = 64 * c ^ 2 * W ^ 2 * ((R ^ ((1 - δ) / 2)) ^ 2 / (L * L ^ B) ^ 2) := by ring
    _ = 64 * c ^ 2 * W ^ 2 * R ^ (1 - δ) / L ^ (2 * B + 2) := by rw [e2, e3]; ring

/-- **Cellwise prime–semiprime matching at one scale.**  Given the cell counts
`#{p ∈ (u,v]} ≤ (101/100)(v-u)/L` and `#{r ∈ (u/q, v/q]} ≥ (99/100)(v-u)/(qL)` for all windows
`(u, v] ⊆ [R, 2R]` of length at least `R/x`, every prime of `(R, 2R]` is matched injectively to a
semiprime `qr`, `q ∈ {2,3,5}`, `r > 5` prime, in `(R, 2R]` at distance at most `2R/x`. -/
theorem exists_cell_matching_of_counts {R : ℕ} {L x : ℝ} (hR30 : (30 : ℝ) ≤ R) (hx : 1 ≤ x)
    (hL : 0 < L)
    (hup : ∀ u v : ℝ, (R : ℝ) ≤ u → u ≤ v → v ≤ 2 * R → R / x ≤ v - u →
      ((windowPrimes u v).card : ℝ) ≤ (1 + 1 / 100) * (v - u) / L)
    (hlow : ∀ q : ℕ, 2 ≤ q → q ≤ 5 → ∀ u v : ℝ, (R : ℝ) ≤ u → u ≤ v → v ≤ 2 * R → R / x ≤ v - u →
      (1 - 1 / 100) * (v - u) / (q * L) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ)) :
    ∃ φ : ℕ → ℕ, Set.InjOn φ ↑(windowPrimes R (2 * R)) ∧
      ∀ p ∈ windowPrimes R (2 * R), (R : ℝ) < φ p ∧ (φ p : ℝ) ≤ 2 * R ∧
        (∃ q r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧ φ p = q * r) ∧
        |(φ p : ℝ) - p| ≤ 2 * R / x := by
  classical
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨hJ1, hhlow, hhup, hJh⟩ := cell_scale hR0 hx
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ, h = (R : ℝ) / ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hhdef] at hhlow hhup hJh
  have hJ0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hJ1
  have hh : 0 < h := by rw [hhdef]; positivity
  -- the cells `(R + ih, R + (i+1)h]`, `i < J`
  have hcell : ∀ i < ⌊x⌋₊, (R : ℝ) ≤ R + i * h ∧ (R : ℝ) + i * h ≤ R + (i + 1) * h ∧
      (R : ℝ) + (i + 1) * h ≤ 2 * R ∧ (R : ℝ) / x ≤ R + (i + 1) * h - (R + i * h) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast hi
    have h1 : (0 : ℝ) ≤ i * h := by positivity
    have h2 : ((i : ℝ) + 1) * h ≤ ⌊x⌋₊ * h := by gcongr
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hPmem : ∀ p ∈ windowPrimes R (2 * R), p.Prime ∧ (R : ℝ) < p ∧ (p : ℝ) ≤ 2 * R :=
    fun p hp => (mem_windowPrimes (by positivity) (by positivity)).mp hp
  have hPc : ∀ p ∈ windowPrimes R (2 * R), cellIndex R h p < ⌊x⌋₊ := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := hPmem p hp
    exact cellIndex_lt hh h1 (by rw [hJh]; linarith)
  set T := (range ⌊x⌋₊).biUnion fun i =>
    semiprimeTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) with hT
  have hcount : ∀ i, ((windowPrimes R (2 * R)).filter (cellIndex R h · = i)).card ≤
      (T.filter (cellIndex R h · = i)).card := by
    intro i
    by_cases hi : i < ⌊x⌋₊
    · obtain ⟨hu, huv, hv, hgap⟩ := hcell i hi
      have hsub1 : (windowPrimes R (2 * R)).filter (cellIndex R h · = i) ⊆
          windowPrimes ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) := by
        intro p hp
        obtain ⟨hp, hpi⟩ := mem_filter.mp hp
        obtain ⟨hpp, h1, -⟩ := hPmem p hp
        obtain ⟨h3, h4⟩ := cellIndex_spec hh h1
        rw [hpi] at h3 h4
        exact (mem_windowPrimes (by linarith) (by linarith)).mpr ⟨hpp, h3, h4⟩
      have hsub2 : semiprimeTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) ⊆
          T.filter (cellIndex R h · = i) := by
        intro n hn
        obtain ⟨-, -, -, -, -, -, h3, h4⟩ := mem_semiprimeTargets (by linarith) huv hn
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_range.mpr hi, hn⟩, cellIndex_eq hh h3 h4⟩
      have hle : ((windowPrimes ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card : ℝ) ≤
          (semiprimeTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card :=
        (hup _ _ hu huv hv hgap).trans (semiprimeTargets_card_ge (by linarith) huv hL
          fun q hq => hlow q (small_cofactor_cases hq).2.1 (small_cofactor_cases hq).2.2 _ _
            hu huv hv hgap)
      have hle' : (windowPrimes ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card ≤
          (semiprimeTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card := by
        exact_mod_cast hle
      exact (card_le_card hsub1).trans (hle'.trans (card_le_card hsub2))
    · have : (windowPrimes R (2 * R)).filter (cellIndex R h · = i) = ∅ := by
        refine filter_eq_empty_iff.mpr fun p hp hpi => hi ?_
        rw [← hpi]; exact hPc p hp
      rw [this]; exact Nat.zero_le _
  obtain ⟨φ, hinj, hφ⟩ := exists_cellwise_injOn _ _ T hcount
  refine ⟨φ, hinj, fun p hp => ?_⟩
  obtain ⟨hφT, hφc⟩ := hφ p hp
  obtain ⟨i, hi, hn⟩ := mem_biUnion.mp hφT
  have hi' := mem_range.mp hi
  obtain ⟨hu, huv, hv, -⟩ := hcell i hi'
  obtain ⟨q, r, hq, hr, h5, he, hlt, hle⟩ := mem_semiprimeTargets (by linarith) huv hn
  have hci : cellIndex R h (φ p) = i := cellIndex_eq hh hlt hle
  obtain ⟨-, h1, -⟩ := hPmem p hp
  obtain ⟨h3, h4⟩ := cellIndex_spec hh h1
  rw [← hφc, hci] at h3 h4
  refine ⟨by linarith, hle.trans hv, ⟨q, r, hq, hr, h5, he⟩, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- The literal signs of the matching: `μ(p) = -1` and `μ(qr) = 1`. -/
theorem moebius_prime_semiprime {p q r : ℕ} (hp : p.Prime) (hq : q = 2 ∨ q = 3 ∨ q = 5)
    (hr : r.Prime) (h5 : 5 < r) : μ p = -1 ∧ μ (q * r) = 1 := by
  have hqp : q.Prime := by rcases hq with h | h | h <;> subst h <;> norm_num
  have hq5 : q ≤ 5 := by rcases hq with h | h | h <;> omega
  refine ⟨ArithmeticFunction.moebius_apply_prime hp, ?_⟩
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    ((Nat.coprime_primes hqp hr).mpr (by omega)), ArithmeticFunction.moebius_apply_prime hqp,
    ArithmeticFunction.moebius_apply_prime hr]
  norm_num

/-- **Complete prime-layer compensation (1).**  Fix `B > 0`.  For all large `R` there is an
injection `φ` from the primes of `(R, 2R]` to squarefree semiprimes `qr ∈ (R, 2R]`, `q ∈ {2,3,5}`,
`r > 5` prime, with `|φ(p) - p| ≤ 2R/(log R)^B`, literal signs `μ(p) = -1`, `μ(φ(p)) = 1`, sources
and targets disjoint in `(R, 2R]` (so `∑_p (f_{φ(p)} - f_p)` is the literal Möbius subsum over them,
and each of its atoms occurs exactly once in the source at every cutoff `N ≥ 2R`), and
uniformly in `0 ≤ δ ≤ 1`: `‖∑_p (f_{φ(p)} - f_p)‖_δ² ≤ C R^{1-δ}/(log R)^{2B+2}`. -/
theorem exists_prime_semiprime_matching {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ φ : ℕ → ℕ, Set.InjOn φ ↑(windowPrimes R (2 * R)) ∧
        (∀ p ∈ windowPrimes R (2 * R), R < φ p ∧ φ p ≤ 2 * R ∧
          ∃ q r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧ φ p = q * r) ∧
        (∀ p ∈ windowPrimes R (2 * R), |(φ p : ℝ) - p| ≤ 2 * R / Real.log R ^ B) ∧
        (∀ p ∈ windowPrimes R (2 * R), μ p = -1 ∧ μ (φ p) = 1) ∧
        Disjoint (windowPrimes R (2 * R)) ((windowPrimes R (2 * R)).image φ) ∧
        windowPrimes R (2 * R) ∪ (windowPrimes R (2 * R)).image φ ⊆ Ioc R (2 * R) ∧
        (∀ t : ℝ, ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t) =
          ∑ n ∈ windowPrimes R (2 * R) ∪ (windowPrimes R (2 * R)).image φ,
            ((μ n : ℤ) : ℝ) * atom n t) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t)) ^ 2 ≤
            C * (R : ℝ) ^ (1 - δ) / Real.log R ^ (2 * B + 2) := by
  obtain ⟨R₁, -, hup⟩ := exists_card_windowPrimes_le B (ε := 1 / 100) (by norm_num)
  obtain ⟨R₂, -, hlow⟩ := exists_card_windowPrimes_div_ge B (ε := 1 / 100) (by norm_num)
  have hev : ∀ᶠ R : ℝ in atTop, R₁ ≤ R ∧ R₂ ≤ R ∧ 30 ≤ R ∧ 1 ≤ Real.log R :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 1)))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  have hc := jetConst_nonneg 1
  refine ⟨64 * jetConst 1 ^ 2 * 2 ^ 2 + 1, by positivity, ⌈X⌉₊, fun R hR => ?_⟩
  have hRX : X ≤ (R : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hR)
  obtain ⟨hR1, hR2, hR30, hL1⟩ := hX R hRX
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  have hx : 1 ≤ Real.log R ^ B := Real.one_le_rpow hL1 hB.le
  obtain ⟨φ, hinj, hφ⟩ := exists_cell_matching_of_counts hR30 hx hL0 (hup R hR1)
    (fun q hq2 hq5 u v => hlow R hR2 q (by exact_mod_cast hq2) (by exact_mod_cast hq5) u v)
  have hPmem : ∀ p ∈ windowPrimes R (2 * R), p.Prime ∧ (R : ℝ) < p ∧ (p : ℝ) ≤ 2 * R :=
    fun p hp => (mem_windowPrimes (by positivity) (by positivity)).mp hp
  have hμ : ∀ p ∈ windowPrimes R (2 * R), μ p = -1 ∧ μ (φ p) = 1 := by
    intro p hp
    obtain ⟨-, -, ⟨q, r, hq, hr, h5, he⟩, -⟩ := hφ p hp
    rw [he]
    exact moebius_prime_semiprime (hPmem p hp).1 hq hr h5
  have hdisj : Disjoint (windowPrimes R (2 * R)) ((windowPrimes R (2 * R)).image φ) := by
    rw [disjoint_left]
    intro n hnP hnI
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hnI
    obtain ⟨-, -, ⟨q, r, hq, hr, h5, he⟩, -⟩ := hφ p hp
    have hn := (hPmem _ hnP).1
    rw [he] at hn
    have hq1 : q ≠ 1 := by rcases hq with h | h | h <;> omega
    exact Nat.not_prime_mul hq1 (by omega) hn
  have hcardP : ((windowPrimes R (2 * R)).card : ℝ) ≤ 2 * R / Real.log R := by
    have hgap : (R : ℝ) / Real.log R ^ B ≤ 2 * R - R := by
      rw [show (2 : ℝ) * R - R = R by ring]; exact div_le_self hR0.le hx
    have := hup R hR1 R (2 * R) le_rfl (by linarith) le_rfl hgap
    calc ((windowPrimes R (2 * R)).card : ℝ) ≤ (1 + 1 / 100) * (2 * R - R) / Real.log R := this
      _ ≤ 2 * R / Real.log R := div_le_div_of_nonneg_right (by linarith) hL0.le
  refine ⟨φ, hinj, fun p hp => ?_, fun p hp => (hφ p hp).2.2.2, hμ, hdisj, fun n hn => ?_,
    fun t => ?_, fun δ hδ0 hδ1 => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := hφ p hp
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, h3⟩
  · rw [mem_Ioc]
    rcases mem_union.mp hn with hn | hn
    · obtain ⟨-, h1, h2⟩ := hPmem n hn
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
      obtain ⟨h1, h2, -⟩ := hφ p hp
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have := sum_dipoles_eq_literal _ φ 1 hinj hdisj (fun p hp => by simpa using hμ p hp) t
    simpa using this
  · have hnorm := gammaNorm_matched_le hδ0 hδ1 hR0 (windowPrimes R (2 * R)) φ
      (fun p hp => ⟨(hPmem p hp).2.1.le, (hPmem p hp).2.2⟩)
      (fun p hp => ⟨(hφ p hp).1.le, (hφ p hp).2.1⟩) (fun p hp => (hφ p hp).2.2.2)
    have hsq := matched_energy_sq_le (W := 2) hR0 hL0 hc hcardP (gammaNorm_nonneg _ _) hnorm
    have hRδ : 0 ≤ (R : ℝ) ^ (1 - δ) / Real.log R ^ (2 * B + 2) := by positivity
    calc _ ≤ 64 * jetConst 1 ^ 2 * 2 ^ 2 * (R : ℝ) ^ (1 - δ) / Real.log R ^ (2 * B + 2) := hsq
      _ ≤ (64 * jetConst 1 ^ 2 * 2 ^ 2 + 1) * (R : ℝ) ^ (1 - δ) / Real.log R ^ (2 * B + 2) := by
          rw [mul_div_assoc, mul_div_assoc]
          gcongr
          linarith

end RHTower.PrimeCells
