import GaloisForLFunctions.RHTower.MobiusTwoJetPrimeSemiprimePacket
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeHarmonic
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# A linear-density balanced extraction from the cubic Möbius source

Fix `0 < η < 4/29` and put `Y = ⌊R^η⌋`.  For every odd squarefree cofactor `q ≤ Y` take the balanced
cofactor packet `P_{R,q} = μ(q)[Σ_r f_{2qr} - Σ_p f_{qp}]`.  Each selected integer has exactly one
prime factor above `R^{1-η} > Y` (the prime `r` or `p`), its odd squarefree cofactor is `q`, and
parity separates `2qr` from `qp`; so the packets are disjoint and their union `U` is a literal
Möbius subpacket, `μ(2qr) = μ(q)`, `μ(qp) = -μ(q)`.

* `Σ_{q ≤ Y odd squarefree} 1/q ≥ (log Y)/8 - 7/8` (the corpus harmonic bound with `Q = 2`), so `U`
  has equally many atoms of Möbius sign `+1` and `-1`, at least `c R` of each;
* `Σ_{q ≤ Y} q^{-21/50} ≪ Y^{29/50}` gives, uniformly in `0 ≤ δ ≤ 1`,
  `‖Σ_{n∈U} μ(n) f_n‖_δ ≤ C [R^{η-(1+δ)/2} + R^{29η/50-2/25-δ/2}/log R]`,
  both exponents negative for `η < 4/29`; at `η = 1/10` they are `-2/5-δ/2` and `-11/500-δ/2`.

On dyadic shells these packets have summable norms, so removing them from `S_{2^{J+2}}` is a bounded
perturbation.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-- **(9)** `Σ_{q ≤ Y, q odd squarefree} 1/q ≥ (log Y)/8 - 7/8`. -/
theorem sum_inv_odd_squarefree_ge {Y : ℕ} (hY : 1 ≤ Y) :
    (1 / 8 : ℝ) * Real.log Y - 7 / 8 ≤
      ∑ q ∈ (Icc 1 Y).filter (fun q => Odd q ∧ Squarefree q), 1 / (q : ℝ) := by
  have h := RHTower.Sieve.sum_inv_coprime_squarefree_ge (M := Y) (Q := 2) (by norm_num)
    (dvd_refl 2) hY (by simp [Nat.Prime.primeFactors Nat.prime_two]; norm_num)
  have e : (Icc 1 Y).filter (fun n => Nat.Coprime n 2 ∧ Squarefree n) =
      (Icc 1 Y).filter (fun q => Odd q ∧ Squarefree q) := by
    apply Finset.filter_congr
    intro n _
    rw [Nat.coprime_comm, Nat.coprime_two_left]
  rwa [e] at h

/-- Disjointness of the cofactor packets: the large prime factor determines the cofactor. -/
theorem cofactor_eq_of_mul_eq {q q' r r' : ℕ} (hr : r.Prime) (hr' : r'.Prime) (hq' : 1 ≤ q')
    (hrq' : q' < r) (h : q * r = q' * r') : q = q' := by
  have hdvd : r ∣ q' * r' := ⟨q, by rw [← h]; ring⟩
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · exact absurd (Nat.le_of_dvd hq' h1) (by omega)
  · have hrr : r = r' := (Nat.prime_dvd_prime_iff_eq hr hr').mp h1
    subst hrr
    exact Nat.eq_of_mul_eq_mul_right hr.pos h

/-- A cofactor block with atoms of sign `μ(q)` and `-μ(q)` in equal numbers has `k` atoms of each
Möbius sign. -/
theorem card_filter_sign_block {A B : Finset ℕ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hA : ∀ a ∈ A, μ a = s) (hB : ∀ b ∈ B, μ b = -s) {k : ℕ}
    (hAk : A.card = k) (hBk : B.card = k) :
    ((A ∪ B).filter (fun n => μ n = 1)).card = k ∧
      ((A ∪ B).filter (fun n => μ n = -1)).card = k := by
  rw [filter_union, filter_union]
  rcases hs with rfl | rfl
  · rw [filter_true_of_mem (fun a ha => hA a ha), filter_false_of_mem (fun b hb => by
        rw [hB b hb]; decide), union_empty, filter_false_of_mem (fun a ha => by
        rw [hA a ha]; decide), filter_true_of_mem (fun b hb => hB b hb), empty_union]
    exact ⟨hAk, hBk⟩
  · rw [filter_false_of_mem (fun a ha => by rw [hA a ha]; decide),
      filter_true_of_mem (fun b hb => by rw [hB b hb]; decide), empty_union,
      filter_true_of_mem (fun a ha => hA a ha), filter_false_of_mem (fun b hb => by
        rw [hB b hb]; decide), union_empty]
    exact ⟨hBk, hAk⟩

/-- `log ⌊R^η⌋ ≥ η log R - log 2` for `R ≥ 1`, `η ≥ 0`. -/
theorem log_floor_rpow_ge {R η : ℝ} (hR : 1 ≤ R) (hη : 0 ≤ η) :
    η * Real.log R - Real.log 2 ≤ Real.log (⌊R ^ η⌋₊ : ℝ) := by
  have hRη : 1 ≤ R ^ η := Real.one_le_rpow hR hη
  have hY1 : 1 ≤ ⌊R ^ η⌋₊ := Nat.le_floor (by exact_mod_cast hRη)
  have hY : R ^ η / 2 ≤ (⌊R ^ η⌋₊ : ℝ) := by
    rcases le_or_gt (R ^ η) 2 with h | h
    · have : (1 : ℝ) ≤ ⌊R ^ η⌋₊ := by exact_mod_cast hY1
      linarith
    · have := Nat.lt_floor_add_one (R ^ η)
      linarith
  have hpos : 0 < R ^ η / 2 := by positivity
  calc η * Real.log R - Real.log 2 = Real.log (R ^ η / 2) := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by linarith)]
    _ ≤ _ := Real.log_le_log hpos hY

/-- `Σ_{q ∈ Q} q^{-21/50} ≤ 3 R^{29η/50}` for `Q ⊆ [1, ⌊R^η⌋]`. -/
theorem sum_cofactor_rpow_le {R η : ℝ} (hR : 1 ≤ R) (hη : 0 ≤ η) {Q : Finset ℕ}
    (hQ : Q ⊆ Icc 1 ⌊R ^ η⌋₊) :
    ∑ q ∈ Q, (q : ℝ) ^ (-(21 / 50 : ℝ)) ≤ 3 * R ^ (29 / 50 * η) := by
  have hRη : 1 ≤ R ^ η := Real.one_le_rpow hR hη
  set Y : ℕ := ⌊R ^ η⌋₊ with hY
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast hRη)
  have hYR : (Y : ℝ) ≤ R ^ η := Nat.floor_le (by linarith)
  have hsub : ∑ q ∈ Q, (q : ℝ) ^ (-(21 / 50 : ℝ)) ≤ ∑ q ∈ Icc 1 Y, (q : ℝ) ^ (-(21 / 50 : ℝ)) :=
    sum_le_sum_of_subset_of_nonneg hQ fun q _ _ => Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hhead := RHTower.sum_rpow_neg_head_le (c := 21 / 50) (by norm_num) (by norm_num) Y
  have hY29 : (1 : ℝ) ≤ (Y : ℝ) ^ (1 - 21 / 50 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hY1) (by norm_num)
  have hYR29 : (Y : ℝ) ^ (1 - 21 / 50 : ℝ) ≤ R ^ (29 / 50 * η) := by
    calc (Y : ℝ) ^ (1 - 21 / 50 : ℝ) ≤ (R ^ η) ^ (1 - 21 / 50 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg Y) hYR (by norm_num)
      _ = R ^ (29 / 50 * η) := by rw [← Real.rpow_mul (by linarith)]; ring_nf
  calc ∑ q ∈ Q, (q : ℝ) ^ (-(21 / 50 : ℝ))
      ≤ 1 + (Y : ℝ) ^ (1 - 21 / 50 : ℝ) / (1 - 21 / 50) := hsub.trans hhead
    _ ≤ 3 * (Y : ℝ) ^ (1 - 21 / 50 : ℝ) := by norm_num; linarith
    _ ≤ 3 * R ^ (29 / 50 * η) := by gcongr

/-- **Linear-density extraction.**  For `0 < η < 4/29` and all large `R` the union of the
cofactor packets over odd squarefree `q ≤ ⌊R^η⌋` is a literal Möbius subpacket of `(2R, 4R)`
with equally many atoms of each sign, at least `c R` of each, and uniformly in `0 ≤ δ ≤ 1`
`‖Σ_{n∈U} μ(n) f_n‖_δ ≤ C [R^{η-(1+δ)/2} + R^{29η/50-2/25-δ/2}/log R]`. -/
theorem exists_linear_density_packet {η : ℝ} (hη0 : 0 < η) (hη : η < 4 / 29) :
    ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ U : Finset ℕ, ∃ Q : Finset ℕ, ∃ Rs Ps : ℕ → Finset ℕ,
        Q = (Icc 1 ⌊R ^ η⌋₊).filter (fun q => Odd q ∧ Squarefree q) ∧
        U = Q.biUnion (fun q => (Rs q).image (fun r => 2 * q * r) ∪ (Ps q).image (fun p => q * p)) ∧
        (∀ q ∈ Q, ∀ r ∈ Rs q, r.Prime ∧ R < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) < 2 * R) ∧
        (∀ q ∈ Q, ∀ p ∈ Ps q, p.Prime ∧ 2 * R < ((q * p : ℕ) : ℝ) ∧ ((q * p : ℕ) : ℝ) < 4 * R) ∧
        (∀ q ∈ Q, (Rs q).card = (Ps q).card) ∧
        (∀ n ∈ U, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ μ n ≠ 0) ∧
        (∀ t : ℝ, ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t =
          ∑ q ∈ Q, ((μ q : ℤ) : ℝ) * (∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
            ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t)) ∧
        (U.filter (fun n => μ n = 1)).card = (U.filter (fun n => μ n = -1)).card ∧
        c * R ≤ (U.filter (fun n => μ n = 1)).card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (η - (1 + δ) / 2) + R ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log R) := by
  obtain ⟨R₁, C₈, c₈, hR₁, hC₈, hc₈, hpk⟩ := exists_cofactor_two_jet_packet
  -- threshold: `log R ≥ 2(log 2 + 7)/η`
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, 1 ≤ R₂ ∧ ∀ R : ℝ, R₂ ≤ R →
      2 * (Real.log 2 + 7) / η ≤ Real.log R := by
    obtain ⟨X, hX⟩ := eventually_atTop.mp
      (Real.tendsto_log_atTop.eventually_ge_atTop (2 * (Real.log 2 + 7) / η))
    exact ⟨max 1 X, le_max_left _ _, fun R hR => hX R (le_of_max_le_right hR)⟩
  refine ⟨c₈ * η / 16, 3 * C₈, max R₁ R₂, by positivity, by positivity,
    le_max_of_le_right hR₂.1, fun R hR => ?_⟩
  have hRR₁ : R₁ ≤ R := le_of_max_le_left hR
  have hR5 : 5 ≤ R := hR₁.trans hRR₁
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hlogR : 2 * (Real.log 2 + 7) / η ≤ Real.log R := hR₂.2 R (le_of_max_le_right hR)
  have hlogpos : 0 < Real.log R := Real.log_pos (by linarith)
  set Y : ℕ := ⌊R ^ η⌋₊ with hYdef
  have hRη1 : 1 ≤ R ^ η := Real.one_le_rpow hR1 hη0.le
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast hRη1)
  have hYR : (Y : ℝ) ≤ R ^ η := Nat.floor_le (by linarith)
  set Q : Finset ℕ := (Icc 1 Y).filter (fun q => Odd q ∧ Squarefree q) with hQdef
  have hQmem : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ Y ∧ Odd q ∧ Squarefree q := fun q hq => by
    rw [hQdef, mem_filter, mem_Icc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  -- `q ≤ R^η ≤ R^{1-η}` and `q² ≤ R`
  have hηhalf : η ≤ 1 - η := by linarith
  have hRηle : R ^ η ≤ R ^ (1 - η) := Real.rpow_le_rpow_of_exponent_le hR1 hηhalf
  have hq2 : ∀ q ∈ Q, (q : ℝ) ^ 2 ≤ R := by
    intro q hq
    have hqY : (q : ℝ) ≤ R ^ η := (by exact_mod_cast (hQmem q hq).2.1 : (q : ℝ) ≤ Y).trans hYR
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    calc (q : ℝ) ^ 2 ≤ (R ^ η) ^ 2 := pow_le_pow_left₀ hq0 hqY 2
      _ = R ^ (2 * η) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; ring_nf
      _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
      _ = R := Real.rpow_one R
  have hex : ∀ q : ℕ, q ∈ Q → ∃ RP : Finset ℕ × Finset ℕ,
      (∀ r ∈ RP.1, r.Prime ∧ R < ((q * r : ℕ) : ℝ) ∧ ((q * r : ℕ) : ℝ) < 2 * R) ∧
      (∀ p ∈ RP.2, p.Prime ∧ 2 * R < ((q * p : ℕ) : ℝ) ∧ ((q * p : ℕ) : ℝ) < 4 * R) ∧
      RP.1.card = RP.2.card ∧ c₈ * R / (q * Real.log R) ≤ RP.1.card ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ r ∈ RP.1, atom ((2 * q * r : ℕ) : ℝ) t -
          ∑ p ∈ RP.2, atom ((q * p : ℕ) : ℝ) t) ≤
          C₈ * (R ^ (-(1 + δ) / 2) +
            R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R) := by
    intro q hq
    obtain ⟨Rs, Ps, h1, h2, h3, h4, h5⟩ := hpk R hRR₁ q (hQmem q hq).1 (hq2 q hq)
    exact ⟨(Rs, Ps), h1, h2, h3, h4, h5⟩
  choose! RP hRs hPs hcard hcount hnorm using hex
  set Rs : ℕ → Finset ℕ := fun q => (RP q).1 with hRsdef
  set Ps : ℕ → Finset ℕ := fun q => (RP q).2 with hPsdef
  -- the large prime exceeds every cofactor
  have hbig : ∀ q ∈ Q, ∀ x : ℕ, R < ((q * x : ℕ) : ℝ) → ∀ q' ∈ Q, q' < x := by
    intro q hq x hx q' hq'
    have hqY : (q : ℝ) ≤ R ^ η := (by exact_mod_cast (hQmem q hq).2.1 : (q : ℝ) ≤ Y).trans hYR
    have hq'Y : (q' : ℝ) ≤ R ^ η := (by exact_mod_cast (hQmem q' hq').2.1 : (q' : ℝ) ≤ Y).trans hYR
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQmem q hq).1
    push_cast at hx
    -- `x > R/q ≥ R^{1-η} ≥ R^η ≥ q'`
    have hxq : R / q < x := by rw [div_lt_iff₀ hq0]; linarith
    have hRq : R ^ (1 - η) ≤ R / q := by
      rw [le_div_iff₀ hq0]
      calc R ^ (1 - η) * q ≤ R ^ (1 - η) * R ^ η := by gcongr
        _ = R := by rw [← Real.rpow_add hR0]; simp
    have : (q' : ℝ) < x := by linarith
    exact_mod_cast this
  have hA2 : ∀ q ∈ Q, ∀ r ∈ Rs q, 2 < r ∧ q < r := by
    intro q hq r hr
    have h := hRs q hq r hr
    have hlt := hbig q hq r h.2.1 q hq
    refine ⟨?_, hlt⟩
    have h1 : 1 ≤ q := (hQmem q hq).1
    rcases (hQmem q hq).2.2.1 with ⟨k, hk⟩
    by_contra hr2
    have hr2' : r ≤ 2 := by omega
    have := h.1.two_le
    have hr' : r = 2 := by omega
    -- `q < r = 2` forces `q = 1`, but then `R < r = 2`
    have hq1 : q = 1 := by omega
    have : R < ((q * r : ℕ) : ℝ) := h.2.1
    rw [hq1, hr'] at this
    norm_num at this
    linarith
  have hP2 : ∀ q ∈ Q, ∀ p ∈ Ps q, 2 < p ∧ q < p := by
    intro q hq p hp
    have h := hPs q hq p hp
    have hRqp : R < ((q * p : ℕ) : ℝ) := by linarith [h.2.1]
    have hlt := hbig q hq p hRqp q hq
    refine ⟨?_, hlt⟩
    by_contra hp2
    have := h.1.two_le
    have h1 := (hQmem q hq).1
    have hp' : p = 2 := by omega
    have hq1 : q = 1 := by omega
    have : 2 * R < ((q * p : ℕ) : ℝ) := h.2.1
    rw [hq1, hp'] at this
    norm_num at this
    linarith
  set A : ℕ → Finset ℕ := fun q => (Rs q).image (fun r => 2 * q * r) with hAdef
  set B : ℕ → Finset ℕ := fun q => (Ps q).image (fun p => q * p) with hBdef
  have hinjA : ∀ q ∈ Q, Set.InjOn (fun r => 2 * q * r) (Rs q) := fun q hq a _ b _ h => by
    have h1 : 0 < 2 * q := by have := (hQmem q hq).1; omega
    exact Nat.eq_of_mul_eq_mul_left h1 h
  have hinjB : ∀ q ∈ Q, Set.InjOn (fun p => q * p) (Ps q) := fun q hq a _ b _ h =>
    Nat.eq_of_mul_eq_mul_left (hQmem q hq).1 h
  -- parity: `A` is even, `B` is odd
  have hBodd : ∀ q ∈ Q, ∀ n ∈ B q, Odd n := by
    intro q hq n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact (hQmem q hq).2.2.1.mul ((hPs q hq p hp).1.odd_of_ne_two (by have := (hP2 q hq p hp).1; omega))
  have hAeven : ∀ q ∈ Q, ∀ n ∈ A q, Even n := by
    intro q hq n hn
    obtain ⟨r, _, rfl⟩ := mem_image.mp hn
    exact ⟨q * r, by ring⟩
  have hdisjAB : ∀ q ∈ Q, ∀ q' ∈ Q, Disjoint (A q) (B q') := by
    intro q hq q' hq'
    rw [Finset.disjoint_left]
    intro n hnA hnB
    exact (Nat.not_even_iff_odd.mpr (hBodd q' hq' n hnB)) (hAeven q hq n hnA)
  have hpair : (↑Q : Set ℕ).PairwiseDisjoint (fun q => A q ∪ B q) := by
    intro q hq q' hq' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    rcases mem_union.mp hn with h1 | h1 <;> rcases mem_union.mp hn' with h2 | h2
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp h1
      obtain ⟨r', hr', he⟩ := mem_image.mp h2
      apply hne
      have h2' : 2 * (q' * r') = 2 * (q * r) := by rw [← mul_assoc, ← mul_assoc]; exact he
      have e : q * r = q' * r' := (Nat.eq_of_mul_eq_mul_left (by norm_num) h2').symm
      exact cofactor_eq_of_mul_eq (hRs q hq r hr).1 (hRs q' hq' r' hr').1 (hQmem q' hq').1
        (hbig q hq r (hRs q hq r hr).2.1 q' hq') e
    · exact Finset.disjoint_left.mp (hdisjAB q hq q' hq') h1 h2
    · exact Finset.disjoint_left.mp (hdisjAB q' hq' q hq) h2 h1
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp h1
      obtain ⟨p', hp', he⟩ := mem_image.mp h2
      apply hne
      have hRqp : R < ((q * p : ℕ) : ℝ) := by linarith [(hPs q hq p hp).2.1]
      exact cofactor_eq_of_mul_eq (hPs q hq p hp).1 (hPs q' hq' p' hp').1 (hQmem q' hq').1
        (hbig q hq p hRqp q' hq') he.symm
  -- Möbius values on the atoms
  have hμq : ∀ q ∈ Q, μ q = 1 ∨ μ q = -1 := by
    intro q hq
    rw [ArithmeticFunction.moebius_apply_of_squarefree (hQmem q hq).2.2.2]
    rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors q) with h | h <;> simp [h]
  have hμA : ∀ q ∈ Q, ∀ n ∈ A q, μ n = μ q := by
    intro q hq n hn
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hn
    exact moebius_two_mul_mul_prime (hQmem q hq).2.2.1 (hRs q hq r hr).1 (hA2 q hq r hr).2
      (hA2 q hq r hr).1
  have hμB : ∀ q ∈ Q, ∀ n ∈ B q, μ n = -μ q := by
    intro q hq n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact moebius_mul_prime_of_lt (hQmem q hq).1 (hPs q hq p hp).1 (hP2 q hq p hp).2
  have hcardA : ∀ q ∈ Q, (A q).card = (Rs q).card := fun q hq => card_image_of_injOn (hinjA q hq)
  have hcardB : ∀ q ∈ Q, (B q).card = (Rs q).card := fun q hq => by
    rw [card_image_of_injOn (hinjB q hq)]
    exact (hcard q hq).symm
  set U : Finset ℕ := Q.biUnion (fun q => A q ∪ B q) with hUdef
  -- the signed counts
  have hfilt : ∀ s : ℤ, (U.filter (fun n => μ n = s)).card =
      ∑ q ∈ Q, ((A q ∪ B q).filter (fun n => μ n = s)).card := by
    intro s
    rw [hUdef, filter_biUnion, card_biUnion]
    exact hpair.mono fun q => filter_subset _ _
  have hplus : (U.filter (fun n => μ n = 1)).card = ∑ q ∈ Q, (Rs q).card := by
    rw [hfilt]
    exact sum_congr rfl fun q hq => (card_filter_sign_block (hμq q hq) (hμA q hq) (hμB q hq)
      (hcardA q hq) (hcardB q hq)).1
  have hminus : (U.filter (fun n => μ n = -1)).card = ∑ q ∈ Q, (Rs q).card := by
    rw [hfilt]
    exact sum_congr rfl fun q hq => (card_filter_sign_block (hμq q hq) (hμA q hq) (hμB q hq)
      (hcardA q hq) (hcardB q hq)).2
  -- the sum identity
  have hsum : ∀ t : ℝ, ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t =
      ∑ q ∈ Q, ((μ q : ℤ) : ℝ) * (∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
        ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t) := by
    intro t
    rw [hUdef, sum_biUnion hpair]
    apply sum_congr rfl
    intro q hq
    rw [sum_union (hdisjAB q hq q hq), hAdef, hBdef, sum_image (hinjA q hq),
      sum_image (hinjB q hq), mul_sub, mul_sum, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro r hr
      have := hμA q hq (2 * q * r) (mem_image_of_mem _ hr)
      rw [this]
    · rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro p hp
      have := hμB q hq (q * p) (mem_image_of_mem _ hp)
      rw [this]
      push_cast
      ring
  refine ⟨U, Q, Rs, Ps, rfl, rfl, hRs, hPs, hcard, ?_, hsum, by rw [hplus, hminus], ?_, ?_⟩
  · -- positions and nonvanishing
    intro n hn
    obtain ⟨q, hq, hnq⟩ := mem_biUnion.mp hn
    have hμq0 : μ q ≠ 0 := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr (hQmem q hq).2.2.2
    rcases mem_union.mp hnq with hnA | hnB
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hnA
      have h := hRs q hq r hr
      have e : ((2 * q * r : ℕ) : ℝ) = 2 * ((q * r : ℕ) : ℝ) := by push_cast; ring
      refine ⟨by rw [e]; linarith [h.2.1], by rw [e]; linarith [h.2.2], ?_⟩
      rw [hμA q hq _ hnA]
      exact hμq0
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp hnB
      have h := hPs q hq p hp
      refine ⟨h.2.1, h.2.2, ?_⟩
      rw [hμB q hq _ hnB]
      exact neg_ne_zero.mpr hμq0
  · -- the count
    rw [hplus]
    have hQsum := sum_inv_odd_squarefree_ge hY1
    rw [← hQdef] at hQsum
    have hlogY := log_floor_rpow_ge hR1 hη0.le
    rw [← hYdef] at hlogY
    have hsumR : c₈ * R / Real.log R * ∑ q ∈ Q, 1 / (q : ℝ) ≤ ((∑ q ∈ Q, (Rs q).card : ℕ) : ℝ) := by
      push_cast
      rw [mul_sum]
      apply sum_le_sum
      intro q hq
      have h := hcount q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQmem q hq).1
      calc c₈ * R / Real.log R * (1 / (q : ℝ)) = c₈ * R / (q * Real.log R) := by
            field_simp
        _ ≤ _ := h
    refine le_trans ?_ hsumR
    have hA : 0 ≤ c₈ * R / Real.log R := by positivity
    have hηl : η * Real.log R / 16 ≤ (1 / 8 : ℝ) * Real.log Y - 7 / 8 := by
      have h1 : 2 * (Real.log 2 + 7) ≤ η * Real.log R := by
        rw [div_le_iff₀ hη0] at hlogR; linarith
      linarith
    calc c₈ * η / 16 * R = c₈ * R / Real.log R * (η * Real.log R / 16) := by
          field_simp
      _ ≤ c₈ * R / Real.log R * ((1 / 8 : ℝ) * Real.log Y - 7 / 8) :=
          mul_le_mul_of_nonneg_left hηl hA
      _ ≤ c₈ * R / Real.log R * ∑ q ∈ Q, 1 / (q : ℝ) := mul_le_mul_of_nonneg_left hQsum hA
  · -- the norm
    intro δ hδ0 hδ1
    have hδ : 0 < 5 + δ := by linarith
    have hfinF : ∀ q ∈ Q, GammaFinite δ (fun t => ∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
        ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t) := by
      intro q hq
      have hq1 := (hQmem q hq).1
      refine (GammaFinite.sum _ fun r hr => gammaFinite_atom hδ ?_).sub
        (GammaFinite.sum _ fun p hp => gammaFinite_atom hδ ?_)
      · exact Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos two_pos hq1) (hRs q hq r hr).1.pos)
      · exact Nat.cast_pos.mpr (Nat.mul_pos hq1 (hPs q hq p hp).1.pos)
    have hfun : (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) = fun t => ∑ q ∈ Q,
        ((μ q : ℤ) : ℝ) * (∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
          ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t) := funext hsum
    rw [hfun]
    refine (gammaNorm_sum_le hδ _ fun q hq => (hfinF q hq).smul _).trans ?_
    have hterm : ∀ q ∈ Q, gammaNorm δ (fun t => ((μ q : ℤ) : ℝ) *
        (∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t - ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t)) ≤
        C₈ * (R ^ (-(1 + δ) / 2) +
          R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R) := by
      intro q hq
      rw [gammaNorm_smul hδ (hfinF q hq)]
      have hμ1 : |((μ q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hn0 := gammaNorm_nonneg δ (fun t => ∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
        ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t)
      calc |((μ q : ℤ) : ℝ)| * gammaNorm δ (fun t => ∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
            ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t)
          ≤ 1 * gammaNorm δ (fun t => ∑ r ∈ Rs q, atom ((2 * q * r : ℕ) : ℝ) t -
            ∑ p ∈ Ps q, atom ((q * p : ℕ) : ℝ) t) := mul_le_mul_of_nonneg_right hμ1 hn0
        _ ≤ _ := by rw [one_mul]; exact hnorm q hq δ hδ0 hδ1
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum, sum_add_distrib, sum_const]
    have hQcard : (Q.card : ℝ) ≤ R ^ η := by
      have : Q.card ≤ Y := by
        calc Q.card ≤ (Icc 1 Y).card := card_filter_le _ _
          _ = Y := by simp
      exact (by exact_mod_cast this : (Q.card : ℝ) ≤ Y).trans hYR
    have hQsum := sum_cofactor_rpow_le hR1 hη0.le (Q := Q) (filter_subset _ _)
    have hsplit : ∑ q ∈ Q, R ^ (-(2 / 25 : ℝ) - δ / 2) * (q : ℝ) ^ (-(21 / 50 : ℝ)) / Real.log R =
        R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R * ∑ q ∈ Q, (q : ℝ) ^ (-(21 / 50 : ℝ)) := by
      rw [mul_sum]; apply sum_congr rfl; intro q _; ring
    rw [hsplit, nsmul_eq_mul]
    have hr1 : 0 ≤ R ^ (-(1 + δ) / 2) := Real.rpow_nonneg hR0.le _
    have hr2 : 0 ≤ R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R := by
      have := Real.rpow_nonneg hR0.le (-(2 / 25 : ℝ) - δ / 2); positivity
    have e1 : R ^ η * R ^ (-(1 + δ) / 2) = R ^ (η - (1 + δ) / 2) := by
      rw [← Real.rpow_add hR0]; ring_nf
    have e2 : R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R * (3 * R ^ (29 / 50 * η)) =
        3 * (R ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log R) := by
      rw [show 29 / 50 * η - 2 / 25 - δ / 2 = (-(2 / 25 : ℝ) - δ / 2) + 29 / 50 * η by ring,
        Real.rpow_add hR0]
      ring
    have hp1 : 0 ≤ R ^ (η - (1 + δ) / 2) := Real.rpow_nonneg hR0.le _
    have hp2 : 0 ≤ R ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log R := by
      have := Real.rpow_nonneg hR0.le (29 / 50 * η - 2 / 25 - δ / 2); positivity
    calc C₈ * ((Q.card : ℝ) * R ^ (-(1 + δ) / 2) +
          R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R * ∑ q ∈ Q, (q : ℝ) ^ (-(21 / 50 : ℝ)))
        ≤ C₈ * (R ^ η * R ^ (-(1 + δ) / 2) +
          R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R * (3 * R ^ (29 / 50 * η))) := by
          gcongr
      _ = C₈ * (R ^ (η - (1 + δ) / 2) +
          3 * (R ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log R)) := by rw [e1, e2]
      _ ≤ 3 * C₈ * (R ^ (η - (1 + δ) / 2) + R ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log R) := by
          nlinarith

/-- **(10)–(11)** at `η = 1/10`: balanced literal extraction of at least `c R` atoms of each
sign with `‖Σ_{n∈U} μ(n) f_n‖_δ ≤ C [R^{-2/5-δ/2} + R^{-11/500-δ/2}/log R]`. -/
theorem exists_linear_density_packet_tenth :
    ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ U : Finset ℕ,
        (∀ n ∈ U, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ μ n ≠ 0) ∧
        (U.filter (fun n => μ n = 1)).card = (U.filter (fun n => μ n = -1)).card ∧
        c * R ≤ (U.filter (fun n => μ n = 1)).card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (-(2 / 5 : ℝ) - δ / 2) + R ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log R) := by
  obtain ⟨c, C, R₀, hc, hC, hR₀, h⟩ := exists_linear_density_packet (η := 1 / 10)
    (by norm_num) (by norm_num)
  refine ⟨c, C, R₀, hc, hC, hR₀, fun R hR => ?_⟩
  obtain ⟨U, -, -, -, -, -, -, -, -, hpos, -, hbal, hcount, hnorm⟩ := h R hR
  refine ⟨U, hpos, hbal, hcount, fun δ hδ0 hδ1 => ?_⟩
  have e1 : (1 / 10 : ℝ) - (1 + δ) / 2 = -(2 / 5 : ℝ) - δ / 2 := by ring
  have e2 : 29 / 50 * (1 / 10 : ℝ) - 2 / 25 - δ / 2 = -(11 / 500 : ℝ) - δ / 2 := by ring
  have hb := hnorm δ hδ0 hδ1
  rwa [e1, e2] at hb

/-- The two-jet bound tends to zero uniformly in `0 ≤ δ ≤ 1`. -/
theorem tendsto_twoJet_bound :
    Tendsto (fun R : ℝ => R ^ (-(1 / 2 : ℝ)) + R ^ (-(2 / 25 : ℝ)) / Real.log R) atTop (𝓝 0) ∧
      ∀ R δ : ℝ, 1 < R → 0 ≤ δ →
        R ^ (-(1 + δ) / 2) + R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R ≤
          R ^ (-(1 / 2 : ℝ)) + R ^ (-(2 / 25 : ℝ)) / Real.log R := by
  refine ⟨?_, fun R δ hR hδ => ?_⟩
  · have h1 : Tendsto (fun R : ℝ => R ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h2 : Tendsto (fun R : ℝ => R ^ (-(2 / 25 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h3 : Tendsto (fun R : ℝ => (Real.log R)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have := h1.add (h2.mul h3)
    simpa [div_eq_mul_inv] using this
  · have hlog : 0 < Real.log R := Real.log_pos hR
    have a1 : R ^ (-(1 + δ) / 2) ≤ R ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hR.le (by linarith)
    have a2 : R ^ (-(2 / 25 : ℝ) - δ / 2) ≤ R ^ (-(2 / 25 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hR.le (by linarith)
    have : R ^ (-(2 / 25 : ℝ) - δ / 2) / Real.log R ≤ R ^ (-(2 / 25 : ℝ)) / Real.log R := by
      gcongr
    linarith

/-- **Cofinal reduction for the prime–semiprime packets (2).**  Along `N_J = 2^{J+2}`, removing the
completed dyadic packets leaves a literal subsource at bounded Gamma distance, for every
`0 ≤ δ ≤ 1`. -/
theorem primeSemiprime_cofinal_reduction :
    ∃ U : ℕ → Finset ℕ, (∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2)) ∧
      (∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        (∀ J : ℕ, ∀ t : ℝ, mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t =
          ∑ n ∈ Icc 1 (2 ^ (J + 2)) \ (range (J + 1)).biUnion U, ((μ n : ℤ) : ℝ) * atom n t) ∧
        ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
          ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  obtain ⟨_, _, A, B, b, hb, -, -, -, -, -, -, -, hsupp, hnorm⟩ :=
    exists_dyadic_prime_semiprime_packets
  refine ⟨fun j => A j ∪ B j, hsupp, ⟨b, hb, hnorm⟩, fun δ hδ0 hδ1 => ?_⟩
  exact cofinal_packet_reduction (fun j => A j ∪ B j) b hb hsupp hδ0 fun j => hnorm j δ hδ0 hδ1

/-- **Dyadic linear-density packets.**  For `0 < η < 4/29` the linear-density extractions at
`R = 2^j` occupy disjoint dyadic shells, keep balanced literal signs with at least `c 2^j` atoms of
each sign, and have norms with a summable majorant uniform in `0 ≤ δ ≤ 1`; removing them from
`S_{2^{J+2}}` is a bounded perturbation. -/
theorem linearDensity_cofinal_reduction {η : ℝ} (hη0 : 0 < η) (hη : η < 4 / 29) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : ℕ → Finset ℕ,
      (∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2) ∧ μ n ≠ 0) ∧
      (∀ j, ((U j).filter (fun n => μ n = 1)).card = ((U j).filter (fun n => μ n = -1)).card) ∧
      (∀ᶠ j in atTop, c * 2 ^ j ≤ ((U j).filter (fun n => μ n = 1)).card) ∧
      (∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
          ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  obtain ⟨c, C, R₀, hc, hC, hR₀, hpk⟩ := exists_linear_density_packet hη0 hη
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, max R₀ 2 ≤ (2 : ℝ) ^ j₀ :=
    pow_unbounded_of_one_lt (max R₀ 2) (by norm_num) |>.imp fun _ h => h.le
  have hex : ∀ j : ℕ, ∃ U : Finset ℕ,
      (j₀ ≤ j → (∀ n ∈ U, 2 * (2 : ℝ) ^ j < n ∧ (n : ℝ) < 4 * 2 ^ j ∧ μ n ≠ 0) ∧
        (U.filter (fun n => μ n = 1)).card = (U.filter (fun n => μ n = -1)).card ∧
        c * 2 ^ j ≤ (U.filter (fun n => μ n = 1)).card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (((2 : ℝ) ^ j) ^ (η - (1 + δ) / 2) +
              ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log (2 ^ j))) ∧
      (j < j₀ → U = ∅) := by
    intro j
    by_cases hj : j₀ ≤ j
    · have hR : R₀ ≤ (2 : ℝ) ^ j :=
        (le_max_left _ _).trans (hj₀.trans (pow_le_pow_right₀ (by norm_num) hj))
      obtain ⟨U, -, -, -, -, -, -, -, -, hpos, -, hbal, hcount, hnorm⟩ := hpk _ hR
      exact ⟨U, fun _ => ⟨hpos, hbal, hcount, hnorm⟩, fun h => absurd hj (by omega)⟩
    · exact ⟨∅, fun h => absurd h hj, fun _ => rfl⟩
  choose U hU hU0 using hex
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set b : ℕ → ℝ := fun j => C * (((2 : ℝ) ^ (η - 1 / 2)) ^ j +
    ((2 : ℝ) ^ (29 / 50 * η - 2 / 25)) ^ j / Real.log 2) with hbdef
  have hb : Summable b := by
    have h1 : Summable (fun j : ℕ => ((2 : ℝ) ^ (η - 1 / 2)) ^ j) :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
    have h2 : Summable (fun j : ℕ => ((2 : ℝ) ^ (29 / 50 * η - 2 / 25)) ^ j) :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
    exact (h1.add (h2.div_const _)).mul_left C
  have hsupp : ∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2) ∧ μ n ≠ 0 := by
    intro j n hn
    by_cases hj : j₀ ≤ j
    · obtain ⟨h1, h2, h3⟩ := (hU j hj).1 n hn
      have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      have e2 : ((2 ^ (j + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ j := by push_cast; ring
      refine ⟨?_, ?_, h3⟩
      · have : ((2 ^ (j + 1) : ℕ) : ℝ) < (n : ℝ) := by rw [e1]; exact h1
        exact_mod_cast this
      · have : (n : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by rw [e2]; exact h2
        exact_mod_cast this
    · simp [hU0 j (by omega)] at hn
  have hnorm : ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j := by
    intro j δ hδ0 hδ1
    by_cases hj : j₀ ≤ j
    · refine ((hU j hj).2.2.2 δ hδ0 hδ1).trans ?_
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0
        have : max R₀ 2 ≤ 1 := by simpa using hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
        linarith [le_max_right R₀ 2]
      have hlogj : Real.log 2 ≤ Real.log (2 ^ j) := by
        rw [Real.log_pow]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        nlinarith
      have hp1 : ((2 : ℝ) ^ j) ^ (η - (1 + δ) / 2) ≤ ((2 : ℝ) ^ (η - 1 / 2)) ^ j := by
        rw [show ((2 : ℝ) ^ (η - 1 / 2)) ^ j = ((2 : ℝ) ^ j) ^ (η - 1 / 2) by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm]]
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
      have hp2 : ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) ≤
          ((2 : ℝ) ^ (29 / 50 * η - 2 / 25)) ^ j := by
        rw [show ((2 : ℝ) ^ (29 / 50 * η - 2 / 25)) ^ j = ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25) by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm]]
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
      have hq0 : 0 ≤ ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) :=
        Real.rpow_nonneg (by positivity) _
      have hdiv : ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log (2 ^ j) ≤
          ((2 : ℝ) ^ (29 / 50 * η - 2 / 25)) ^ j / Real.log 2 := by
        calc ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log (2 ^ j)
            ≤ ((2 : ℝ) ^ j) ^ (29 / 50 * η - 2 / 25 - δ / 2) / Real.log 2 :=
              div_le_div_of_nonneg_left hq0 hlog2 hlogj
          _ ≤ _ := by gcongr
      simp only [hbdef]
      gcongr
    · simp only [hU0 j (by omega), Finset.sum_empty]
      have : gammaNorm δ (fun _ : ℝ => (0 : ℝ)) = 0 := by
        simp [gammaNorm, gammaEnergy, gammaInner]
      rw [this]
      simp only [hbdef]
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (η - 1 / 2)
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (29 / 50 * η - 2 / 25)
      positivity
  refine ⟨c, hc, U, hsupp, fun j => ?_, ?_, ⟨b, hb, hnorm⟩, fun δ hδ0 hδ1 => ?_⟩
  · by_cases hj : j₀ ≤ j
    · exact (hU j hj).2.1
    · simp [hU0 j (by omega)]
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (hU j hj).2.2.1
  · exact (cofinal_packet_reduction U b hb (fun j n hn => ⟨(hsupp j n hn).1, (hsupp j n hn).2.1⟩)
      hδ0 fun j => hnorm j δ hδ0 hδ1).2

end RHTower.CubicGamma
