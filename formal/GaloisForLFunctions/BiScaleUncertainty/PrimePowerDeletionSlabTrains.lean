import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionStaircaseTrains

/-!
# Euler additivity on the integer grid: slab trains

Delete one prime power `m_p = p^{e(p)}` for every prime `p` of a finite set `P` from the integer-grid
blind cone, which asks for blindness at **every** integer `n ≥ 2` outside `{m_p}` (all composites
included). On the prime-power cone the price is the Euler sum `Σ_{p∈P} w(m_p)`, `w(m) = Λ(m)/√m`
(`PrimePowerDeletionPriceEulerAdditivity`), attained by iterated pairs whose lags include every
product `m_A`, `|A| ≥ 2`.

**Theorem** (`isLUB_gridEulerDeviations`, `isGLB_gridEulerDeviations`). On the integer-grid cone the
deviations `(A − W)/‖c‖²` have supremum `Σ_{p∈P} w(m_p)` and infimum `−Σ_{p∈P} w(m_p)`. In particular
deleting every prime `p ≤ x` from the integer grid costs `Σ_{p≤x} log p/√p`
(`isGLB_gridEulerDeviations_primes_le`): composite nodes never change a single-node deletion price.

**Mechanism.** Fix `p₀ ∈ P`, `Q = P \ {p₀}`. The slab train has narrow bumps at
`Σ_{i∈Q} k_i log(m_i/m_{p₀}) + ε log m_{p₀}`, `k ∈ {0, …, M}^Q`, `ε ∈ {0, 1}`, with signs
`σ^ε Π τ_i^{k_i}`. In the exponent lattice of `(m_p)` the positions lie on the slab of coordinate sum
`0` and `1`, so a lag `log n` with `n ≥ 2` needs nonnegative exponents of coordinate sum one: `n` is one
of the deleted nodes (`slab_lag_cases`, by the `p`-adic valuations). The node `m_{p₀}` is charged by
the `(M+1)^{|Q|}` rungs, every `m_i` by the `M(M+1)^{|Q|−1}` steps, and the deviation is
`σ w(m_{p₀}) + Σ_i σ τ_i w(m_i) M/(M+1)`.
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Slab vertices and their lags -/

/-- The cube `{0, …, M}^Q` of slab coordinates. -/
def slabBox (Q : Finset ℕ) (M : ℕ) : Finset (Q → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (M + 1)

/-- The vertex set `{0, …, M}^Q × {0, 1}`. -/
def slabIndex (Q : Finset ℕ) (M : ℕ) : Finset ((Q → ℕ) × ℕ) := slabBox Q M ×ˢ Finset.range 2

/-- The position `Σ_i k_i log(m_i/m₀) + ε log m₀` of the vertex `(k, ε)`. -/
def slabPos {Q : Finset ℕ} (m : ℕ → ℕ) (m₀ : ℕ) (a : (Q → ℕ) × ℕ) : ℝ :=
  ∑ i : Q, (a.1 i : ℝ) * (Real.log (m i) - Real.log m₀) + a.2 * Real.log m₀

/-- The numerator `Π m_i^{k_a,i} · m₀^{ε_a + Σ k_b}` of the lag from `b` to `a`. -/
def slabNum {Q : Finset ℕ} (m : ℕ → ℕ) (m₀ : ℕ) (a b : (Q → ℕ) × ℕ) : ℕ :=
  (∏ i : Q, m i ^ a.1 i) * m₀ ^ (a.2 + ∑ i : Q, b.1 i)

/-- The denominator `Π m_i^{k_b,i} · m₀^{ε_b + Σ k_a}`. -/
def slabDen {Q : Finset ℕ} (m : ℕ → ℕ) (m₀ : ℕ) (a b : (Q → ℕ) × ℕ) : ℕ :=
  (∏ i : Q, m i ^ b.1 i) * m₀ ^ (b.2 + ∑ i : Q, a.1 i)

section Lags

variable {Q : Finset ℕ} {m : ℕ → ℕ} {m₀ : ℕ} (hm : ∀ i ∈ Q, 1 ≤ m i) (hm₀ : 1 ≤ m₀)

include hm hm₀ in
theorem slabNum_pos (a b : (Q → ℕ) × ℕ) : 0 < slabNum m m₀ a b :=
  Nat.mul_pos (Finset.prod_pos fun i _ => pow_pos (hm i i.2) _) (pow_pos hm₀ _)

include hm hm₀ in
theorem slabDen_pos (a b : (Q → ℕ) × ℕ) : 0 < slabDen m m₀ a b :=
  Nat.mul_pos (Finset.prod_pos fun i _ => pow_pos (hm i i.2) _) (pow_pos hm₀ _)

include hm hm₀ in
theorem slabPos_sub (a b : (Q → ℕ) × ℕ) :
    slabPos m m₀ a - slabPos m m₀ b =
      Real.log (slabNum m m₀ a b) - Real.log (slabDen m m₀ a b) := by
  have hpos : ∀ i : Q, (0 : ℝ) < m i := fun i => by exact_mod_cast hm i i.2
  have h₀ : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have hlogprod : ∀ k : Q → ℕ, Real.log ((∏ i : Q, m i ^ k i : ℕ) : ℝ) =
      ∑ i : Q, (k i : ℝ) * Real.log (m i) := by
    intro k
    push_cast
    rw [Real.log_prod (fun i _ => (pow_pos (hpos i) _).ne')]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.log_pow]
  simp only [slabPos, slabNum, slabDen]
  push_cast
  have hpa : (0 : ℝ) < ∏ i : Q, (m i : ℝ) ^ a.1 i := Finset.prod_pos fun i _ => pow_pos (hpos i) _
  have hpb : (0 : ℝ) < ∏ i : Q, (m i : ℝ) ^ b.1 i := Finset.prod_pos fun i _ => pow_pos (hpos i) _
  rw [Real.log_mul hpa.ne' (pow_pos h₀ _).ne', Real.log_mul hpb.ne' (pow_pos h₀ _).ne',
    Real.log_pow, Real.log_pow]
  rw [show (∏ i : Q, (m i : ℝ) ^ a.1 i) = ((∏ i : Q, m i ^ a.1 i : ℕ) : ℝ) by push_cast; rfl,
    show (∏ i : Q, (m i : ℝ) ^ b.1 i) = ((∏ i : Q, m i ^ b.1 i : ℕ) : ℝ) by push_cast; rfl,
    hlogprod, hlogprod]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
  ring

end Lags

/-- The `r`-adic valuation of `Π_{i∈Q} (i^{e_i})^{k_i} · (p₀^{e₀})^t`: `e_r k_r` at `r ∈ Q`, `e₀ t` at `p₀`. -/
theorem factorization_slab {Q : Finset ℕ} (hQ : ∀ i ∈ Q, i.Prime) {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀Q : p₀ ∉ Q) (e : ℕ → ℕ) (k : Q → ℕ) (t : ℕ) :
    (∀ r : Q, ((∏ i : Q, ((i : ℕ) ^ e i) ^ k i) * (p₀ ^ e p₀) ^ t).factorization r =
      e r * k r) ∧
      ((∏ i : Q, ((i : ℕ) ^ e i) ^ k i) * (p₀ ^ e p₀) ^ t).factorization p₀ = e p₀ * t := by
  classical
  have hne : ∀ i : Q, ((i : ℕ) ^ e i) ^ k i ≠ 0 := fun i =>
    pow_ne_zero _ (pow_ne_zero _ (hQ i i.2).ne_zero)
  have hprod : (∏ i : Q, ((i : ℕ) ^ e i) ^ k i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hp0 : (p₀ ^ e p₀) ^ t ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp₀.ne_zero)
  have hfac : ((∏ i : Q, ((i : ℕ) ^ e i) ^ k i) * (p₀ ^ e p₀) ^ t).factorization =
      (∑ i : Q, Finsupp.single (i : ℕ) (e i * k i)) + Finsupp.single p₀ (e p₀ * t) := by
    rw [Nat.factorization_mul hprod hp0, Nat.factorization_prod fun i _ => hne i, ← pow_mul,
      hp₀.factorization_pow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, (hQ i i.2).factorization_pow]
  refine ⟨fun r => ?_, ?_⟩
  · have hr0 : ¬ (p₀ = (r : ℕ)) := fun h => hp₀Q (by rw [h]; exact r.2)
    rw [hfac, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, if_neg hr0, add_zero,
      Finset.sum_eq_single r (fun i _ hir => by
        rw [Finsupp.single_apply, if_neg (fun h => hir (Subtype.ext h))]) (by simp)]
    simp
  · rw [hfac, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, if_pos rfl]
    rw [Finset.sum_eq_zero fun i _ => by
      have hi0 : ¬ ((i : ℕ) = p₀) := fun h => hp₀Q (by rw [← h]; exact i.2)
      rw [Finsupp.single_apply, if_neg hi0], zero_add]

section SlabLag

variable {Q : Finset ℕ} (hQ : ∀ i ∈ Q, i.Prime) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀Q : p₀ ∉ Q)
  {e : ℕ → ℕ} (he : ∀ i ∈ Q, 1 ≤ e i) (he₀ : 1 ≤ e p₀)

/-- The deleted nodes `m_i = i^{e_i}`. -/
abbrev slabNode (e : ℕ → ℕ) (i : ℕ) : ℕ := i ^ e i

include hQ hp₀ hp₀Q he he₀ in
/-- **The only integer lags of the slab are the deleted nodes.** If the lag from `b` to `a` is
`log n`, `n ≥ 1`, then `a = b` and `n = 1`, or `b = (k, 0)`, `a = (k, 1)` and `n = m₀`, or
`b = (k, 0)`, `a = (k + δ_r, 1)` and `n = m_r`. -/
theorem slab_lag_cases {a b : (Q → ℕ) × ℕ} (ha : a.2 < 2) (hb : b.2 < 2) {n : ℕ} (hn : 1 ≤ n)
    (h : slabNum (slabNode e) (slabNode e p₀) a b = n * slabDen (slabNode e) (slabNode e p₀) a b) :
    (a = b ∧ n = 1) ∨ (a.1 = b.1 ∧ a.2 = 1 ∧ b.2 = 0 ∧ n = slabNode e p₀) ∨
      (∃ r : Q, a.1 = b.1 + Pi.single r 1 ∧ a.2 = 1 ∧ b.2 = 0 ∧ n = slabNode e r) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hm : ∀ i ∈ Q, 1 ≤ slabNode e i := fun i hi => Nat.one_le_pow _ _ (hQ i hi).pos
  have hm₀ : 1 ≤ slabNode e p₀ := Nat.one_le_pow _ _ hp₀.pos
  have hden0 := (slabDen_pos hm hm₀ a b).ne'
  have hfac := congrArg Nat.factorization h
  rw [Nat.factorization_mul hn0 hden0] at hfac
  have hnum_eq : slabNum (slabNode e) (slabNode e p₀) a b =
      (∏ i : Q, ((i : ℕ) ^ e i) ^ a.1 i) * (p₀ ^ e p₀) ^ (a.2 + ∑ i : Q, b.1 i) := rfl
  have hden_eq : slabDen (slabNode e) (slabNode e p₀) a b =
      (∏ i : Q, ((i : ℕ) ^ e i) ^ b.1 i) * (p₀ ^ e p₀) ^ (b.2 + ∑ i : Q, a.1 i) := rfl
  obtain ⟨hNr, hN₀⟩ := factorization_slab hQ hp₀ hp₀Q e a.1 (a.2 + ∑ i : Q, b.1 i)
  obtain ⟨hDr, hD₀⟩ := factorization_slab hQ hp₀ hp₀Q e b.1 (b.2 + ∑ i : Q, a.1 i)
  -- coordinatewise: `k_a ≥ k_b`
  have hcoord : ∀ r : Q, b.1 r ≤ a.1 r := by
    intro r
    have h1 := congrArg (fun g => g r) hfac
    simp only [Finsupp.add_apply] at h1
    rw [hnum_eq, hNr, hden_eq, hDr] at h1
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt (show 0 < e r by have := he r r.2; omega)
    omega
  -- at `p₀`: `ε_a + Σ k_b ≥ ε_b + Σ k_a`
  have hbase : b.2 + ∑ i : Q, a.1 i ≤ a.2 + ∑ i : Q, b.1 i := by
    have h1 := congrArg (fun g => g p₀) hfac
    simp only [Finsupp.add_apply] at h1
    rw [hnum_eq, hN₀, hden_eq, hD₀] at h1
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt (show 0 < e p₀ by omega)
    omega
  set d : Q → ℕ := fun r => a.1 r - b.1 r with hd
  have had : a.1 = b.1 + d := funext fun r => by simp only [hd, Pi.add_apply]; have := hcoord r; omega
  have hsum : ∑ i : Q, a.1 i = ∑ i : Q, b.1 i + ∑ i : Q, d i := by
    rw [had]; simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hdsum : ∑ i : Q, d i ≤ 1 := by omega
  have hden_pos := slabDen_pos hm hm₀ a b
  rcases Nat.lt_or_ge (∑ i : Q, d i) 1 with h0 | h1
  · -- no step: `k_a = k_b`
    have hd0 : ∀ r, d r = 0 := fun r => by
      have := Finset.single_le_sum (f := d) (fun i _ => Nat.zero_le _) (Finset.mem_univ r); omega
    have hk : a.1 = b.1 := by rw [had]; funext r; simp [hd0 r]
    rcases Nat.lt_or_ge a.2 (b.2 + 1) with hle | hgt
    · left
      have he2 : a.2 = b.2 := by omega
      refine ⟨Prod.ext hk he2, ?_⟩
      have hnd : slabNum (slabNode e) (slabNode e p₀) a b =
          slabDen (slabNode e) (slabNode e p₀) a b := by
        simp only [slabNum, slabDen]; rw [hk, he2]
      rw [hnd] at h
      exact (Nat.eq_of_mul_eq_mul_right hden_pos (by rw [one_mul]; exact h)).symm
    · right; left
      have ha2 : a.2 = 1 := by omega
      have hb2 : b.2 = 0 := by omega
      refine ⟨hk, ha2, hb2, ?_⟩
      have hnd : slabNum (slabNode e) (slabNode e p₀) a b =
          slabNode e p₀ * slabDen (slabNode e) (slabNode e p₀) a b := by
        simp only [slabNum, slabDen]; rw [hk, ha2, hb2]; ring
      rw [hnd] at h
      exact (Nat.eq_of_mul_eq_mul_right hden_pos h).symm
  · -- one step `δ_r`
    right; right
    have hds : ∑ i : Q, d i = 1 := by omega
    have ha2 : a.2 = 1 := by omega
    have hb2 : b.2 = 0 := by omega
    obtain ⟨r, -, hr⟩ : ∃ r ∈ (Finset.univ : Finset Q), d r ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero hall] at hds
      omega
    have hdr : d r = 1 := by
      have := Finset.single_le_sum (f := d) (fun i _ => Nat.zero_le _) (Finset.mem_univ r); omega
    have hother : ∀ i, i ≠ r → d i = 0 := by
      intro i hir
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset Q) d (Finset.mem_univ r)
      have := Finset.single_le_sum (f := d) (fun j _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hir, Finset.mem_univ i⟩)
      omega
    have hdsingle : d = Pi.single r 1 := by
      funext i
      by_cases hir : i = r
      · subst hir; simp [hdr]
      · simp [hir, hother i hir]
    refine ⟨r, by rw [had, hdsingle], ha2, hb2, ?_⟩
    have hprod : (∏ i : Q, slabNode e i ^ a.1 i) = slabNode e r * ∏ i : Q, slabNode e i ^ b.1 i := by
      rw [had, hdsingle]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single r (fun i _ hir => by simp [hir]) (by simp)]
      simp
    have hnd : slabNum (slabNode e) (slabNode e p₀) a b =
        slabNode e r * slabDen (slabNode e) (slabNode e p₀) a b := by
      simp only [slabNum, slabDen]
      rw [hprod, ha2, hb2, hsum, hds]
      ring
    rw [hnd] at h
    exact (Nat.eq_of_mul_eq_mul_right hden_pos h).symm

end SlabLag

/-! ### 2. The slab train -/

/-- A bound for all numerators and denominators of the lags of the slab of size `M`. -/
def slabBound (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M : ℕ) : ℕ :=
  (slabIndex Q M ×ˢ slabIndex Q M).sup fun ab => max (slabNum m m₀ ab.1 ab.2) (slabDen m m₀ ab.1 ab.2)

theorem slabNum_le_bound {Q : Finset ℕ} {m : ℕ → ℕ} {m₀ M : ℕ} {a b : (Q → ℕ) × ℕ}
    (ha : a ∈ slabIndex Q M) (hb : b ∈ slabIndex Q M) :
    slabNum m m₀ a b ≤ slabBound Q m m₀ M ∧ slabDen m m₀ a b ≤ slabBound Q m m₀ M := by
  have h := Finset.le_sup (f := fun ab : ((Q → ℕ) × ℕ) × ((Q → ℕ) × ℕ) =>
    max (slabNum m m₀ ab.1 ab.2) (slabDen m m₀ ab.1 ab.2))
    (show (a, b) ∈ slabIndex Q M ×ˢ slabIndex Q M from Finset.mem_product.mpr ⟨ha, hb⟩)
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

/-- **Separation of the slab lags** at `±log n` for a bump of index `N ≥` the slab bound. -/
theorem slab_sep {Q : Finset ℕ} {m : ℕ → ℕ} {m₀ M N : ℕ} (hm : ∀ i ∈ Q, 1 ≤ m i) (hm₀ : 1 ≤ m₀)
    (hN : slabBound Q m m₀ M ≤ N) {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∀ a ∈ slabIndex Q M, ∀ b ∈ slabIndex Q M,
      slabPos m m₀ a - slabPos m m₀ b ≠ s * Real.log n →
        1 / (2 * ((N : ℝ) + 1)) < |s * Real.log n - slabPos m m₀ a + slabPos m m₀ b| := by
  intro a ha b hb hne
  obtain ⟨hU0, hV0⟩ := slabNum_le_bound (m := m) (m₀ := m₀) ha hb
  have hN' : (slabBound Q m m₀ M : ℝ) ≤ N := by exact_mod_cast hN
  have hU1 : (slabNum m m₀ a b : ℝ) ≤ slabBound Q m m₀ M := by exact_mod_cast hU0
  have hV1 : (slabDen m m₀ a b : ℝ) ≤ slabBound Q m m₀ M := by exact_mod_cast hV0
  have hUB := hU1.trans hN'
  have hVB := hV1.trans hN'
  have hU := slabNum_pos hm hm₀ a b
  have hV := slabDen_pos hm hm₀ a b
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrad : ∀ X : ℕ, (X : ℝ) ≤ N → 1 / (2 * ((N : ℝ) + 1)) < 1 / ((X : ℝ) + 1) := by
    intro X hX
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  rw [slabPos_sub hm hm₀] at hne
  rw [show s * Real.log n - slabPos m m₀ a + slabPos m m₀ b =
    s * Real.log n - (slabPos m m₀ a - slabPos m m₀ b) by ring, slabPos_sub hm hm₀]
  rcases hs with rfl | rfl
  · rw [one_mul] at hne ⊢
    have hne' : n * slabDen m m₀ a b ≠ slabNum m m₀ a b := by
      intro h
      apply hne
      rw [← h]; push_cast
      rw [Real.log_mul hn'.ne' (by positivity)]; ring
    have := RHTower.WeilExcess.inv_succ_le_abs_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity))
      hU hne'
    refine (hrad _ hUB).trans_le (this.trans (le_of_eq ?_))
    push_cast
    rw [Real.log_mul hn'.ne' (by positivity)]; ring_nf
  · rw [neg_one_mul] at hne ⊢
    have hne' : n * slabNum m m₀ a b ≠ slabDen m m₀ a b := by
      intro h
      apply hne
      have : Real.log (slabDen m m₀ a b) = Real.log n + Real.log (slabNum m m₀ a b) := by
        rw [← h]; push_cast; rw [Real.log_mul hn'.ne' (by positivity)]
      rw [this]; ring
    have := RHTower.WeilExcess.inv_succ_le_abs_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity))
      hV hne'
    refine (hrad _ hVB).trans_le (this.trans (le_of_eq ?_))
    push_cast
    rw [Real.log_mul hn'.ne' (by positivity), abs_sub_comm]; ring_nf

/-- The slab train `Σ_{(k,ε)} σ^ε h_N(u − Σ_i k_i log(m_i/m₀) − ε log m₀)`. -/
def slabTrain (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M N : ℕ) (σ : ℝ) (u : ℝ) : ℂ :=
  ∑ a ∈ slabIndex Q M, ((σ ^ a.2 : ℝ) : ℂ) * narrowBumpC N (u - slabPos m m₀ a)

theorem contDiff_slabTrain (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M N : ℕ) (σ : ℝ) :
    ContDiff ℝ 2 (slabTrain Q m m₀ M N σ) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (((contDiff_narrowBumpC _).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_slabTrain (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M N : ℕ) (σ : ℝ) :
    HasCompactSupport (slabTrain Q m m₀ M N σ) :=
  hasCompactSupport_finsetSum _ fun _ _ =>
    ((hasCompactSupport_narrowBumpC _).comp_homeomorph (Homeomorph.subRight _)).mul_left

/-- The slab train as a Weil test. -/
def slabTrainFn (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M N : ℕ) (σ : ℝ) : WeilTestFn :=
  ⟨slabTrain Q m m₀ M N σ, contDiff_slabTrain Q m m₀ M N σ, hasCompactSupport_slabTrain Q m m₀ M N σ⟩

/-- The lag coefficient of the slab train at `y`. -/
def slabLagCoeff (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M : ℕ) (σ y : ℝ) : ℝ :=
  ∑ a ∈ slabIndex Q M, ∑ b ∈ slabIndex Q M,
    if slabPos m m₀ a - slabPos m m₀ b = y then σ ^ a.2 * σ ^ b.2 else 0

theorem slabLagCoeff_neg (Q : Finset ℕ) (m : ℕ → ℕ) (m₀ M : ℕ) (σ y : ℝ) :
    slabLagCoeff Q m m₀ M σ (-y) = slabLagCoeff Q m m₀ M σ y := by
  unfold slabLagCoeff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : slabPos m m₀ a - slabPos m m₀ b = y
  · rw [if_pos h, if_pos (by linarith), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (by linarith)]

theorem weilTest_slabTrain {Q : Finset ℕ} {m : ℕ → ℕ} {m₀ M N : ℕ} (hm : ∀ i ∈ Q, 1 ≤ m i)
    (hm₀ : 1 ≤ m₀) (hN : slabBound Q m m₀ M ≤ N) {n : ℕ} (hn : 1 ≤ n) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (σ : ℝ) :
    EF.weilTest (slabTrain Q m m₀ M N σ) (slabTrain Q m m₀ M N σ) (s * Real.log n) =
      (slabLagCoeff Q m m₀ M σ (s * Real.log n) : ℂ) * ((∫ t, (narrowBump N t) ^ 2 : ℝ) : ℂ) := by
  unfold slabTrain slabLagCoeff
  exact weilTest_train_select (slabIndex Q M) (fun a => σ ^ a.2) (slabPos m m₀) N (s * Real.log n)
    (slab_sep hm hm₀ hN hn s hs)

/-! ### 3. The coefficients of the slab -/

/-- Steps in direction `r` start at the vertices with `k_r ≥ 1`: there are `M(M+1)^{|Q|−1}` of them. -/
theorem card_filter_slabBox_mul {Q : Finset ℕ} (M : ℕ) (r : Q) :
    ((slabBox Q M).filter fun k => 1 ≤ k r).card * (M + 1) = M * (slabBox Q M).card := by
  classical
  have hfilt : (slabBox Q M).filter (fun k => 1 ≤ k r) =
      Fintype.piFinset fun i => if i = r then Finset.Icc 1 M else Finset.range (M + 1) := by
    ext k
    simp only [slabBox, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hk, h1⟩ i
      by_cases hir : i = r
      · subst hir; simp only [if_true, Finset.mem_Icc]; have := Finset.mem_range.mp (hk i); omega
      · simp only [hir, if_false]; exact hk i
    · intro hk
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hir : i = r
        · have := hk i; simp only [hir, if_true, Finset.mem_Icc] at this
          subst hir; exact Finset.mem_range.mpr (by omega)
        · have := hk i; simp only [hir, if_false] at this; exact this
      · have := hk r; simp only [if_true, Finset.mem_Icc] at this; exact this.1
  rw [hfilt, slabBox, Fintype.card_piFinset, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
    ← Finset.mul_prod_erase Finset.univ (fun _ => (Finset.range (M + 1)).card) (Finset.mem_univ r)]
  have hrest : ∏ x ∈ Finset.univ.erase r,
      (if x = r then Finset.Icc 1 M else Finset.range (M + 1)).card =
      ∏ x ∈ Finset.univ.erase r, (Finset.range (M + 1)).card :=
    Finset.prod_congr rfl fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)]
  rw [hrest, if_pos rfl, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel]
  ring

section Coefficients

variable {Q : Finset ℕ} (hQ : ∀ i ∈ Q, i.Prime) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀Q : p₀ ∉ Q)
  {e : ℕ → ℕ} (he : ∀ i ∈ Q, 1 ≤ e i) (he₀ : 1 ≤ e p₀) {σ : ℝ} (hσ : σ ^ 2 = 1)

include hQ hp₀ in
theorem slabPos_sub_eq_log_iff {a b : (Q → ℕ) × ℕ} {n : ℕ} (hn : 1 ≤ n) :
    slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b = Real.log n ↔
      slabNum (slabNode e) (slabNode e p₀) a b = n * slabDen (slabNode e) (slabNode e p₀) a b := by
  have hm : ∀ i ∈ Q, 1 ≤ slabNode e i := fun i hi => Nat.one_le_pow _ _ (hQ i hi).pos
  have hm₀ : 1 ≤ slabNode e p₀ := Nat.one_le_pow _ _ hp₀.pos
  have hU := slabNum_pos hm hm₀ a b
  have hV := slabDen_pos hm hm₀ a b
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [slabPos_sub hm hm₀, sub_eq_iff_eq_add, ← Real.log_mul hn'.ne' (by positivity)]
  constructor
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < slabNum _ _ a b))
      (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < n * slabDen _ _ a b)) h
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring_nf

include hQ hp₀ hp₀Q he he₀ hσ in
/-- The diagonal coefficient is the number of vertices `2(M+1)^{|Q|}`. -/
theorem slabLagCoeff_zero (M : ℕ) :
    slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log (1 : ℕ)) =
      2 * (slabBox Q M).card := by
  classical
  unfold slabLagCoeff
  have key : ∀ a ∈ slabIndex Q M, (∑ b ∈ slabIndex Q M,
      if slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
        Real.log (1 : ℕ) then σ ^ a.2 * σ ^ b.2 else 0) = 1 := by
    intro a ha
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
          Real.log (1 : ℕ) ↔ b = a from ?_) rfl rfl, Finset.sum_ite_eq' _ a, if_pos ha]
    · rw [← pow_add, ← two_mul, pow_mul, hσ, one_pow]
    · have ha' := Finset.mem_range.mp (Finset.mem_product.mp ha).2
      have hb' := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      rw [slabPos_sub_eq_log_iff hQ hp₀ le_rfl]
      constructor
      · intro h
        rcases slab_lag_cases hQ hp₀ hp₀Q he he₀ ha' hb' le_rfl h with ⟨hab, -⟩ | ⟨-, -, -, h1⟩ |
            ⟨r, -, -, -, h1⟩
        · exact hab.symm
        · exact absurd h1 (Nat.one_lt_pow (by omega) hp₀.one_lt).ne
        · exact absurd h1 (Nat.one_lt_pow (by have := he r r.2; omega) (hQ r r.2).one_lt).ne
      · rintro rfl; simp [slabNum, slabDen]
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul, mul_one, slabIndex,
    Finset.card_product, Finset.card_range]
  push_cast; ring

theorem slabNum_rung {Q : Finset ℕ} (m : ℕ → ℕ) (m₀ : ℕ) {a b : (Q → ℕ) × ℕ} (hk : a.1 = b.1)
    (ha : a.2 = 1) (hb : b.2 = 0) : slabNum m m₀ a b = m₀ * slabDen m m₀ a b := by
  simp only [slabNum, slabDen]; rw [hk, ha, hb]; ring

theorem slabNum_step {Q : Finset ℕ} (m : ℕ → ℕ) (m₀ : ℕ) {a b : (Q → ℕ) × ℕ} (r : Q)
    (hk : a.1 = b.1 + Pi.single r 1) (ha : a.2 = 1) (hb : b.2 = 0) :
    slabNum m m₀ a b = m r * slabDen m m₀ a b := by
  classical
  have hprod : (∏ i : Q, m i ^ a.1 i) = m r * ∏ i : Q, m i ^ b.1 i := by
    rw [hk]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single r (fun i _ hir => by simp [hir]) (by simp)]
    simp
  have hsingle : ∑ i : Q, (Pi.single r 1 : Q → ℕ) i = 1 := by
    rw [Finset.sum_eq_single r (fun i _ hir => by simp [hir]) (by simp)]; simp
  have hsum : ∑ i : Q, a.1 i = ∑ i : Q, b.1 i + 1 := by
    rw [hk]; simp only [Pi.add_apply, Finset.sum_add_distrib, hsingle]
  simp only [slabNum, slabDen]
  rw [hprod, ha, hb, hsum]
  ring

include hQ hp₀ hp₀Q he he₀ in
/-- **The rungs.** The coefficient at `log m₀` is `(M+1)^{|Q|} σ`. -/
theorem slabLagCoeff_log_base (M : ℕ) :
    slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log ((slabNode e p₀ : ℕ) : ℝ)) =
      (slabBox Q M).card * σ := by
  classical
  have h2 : 2 ≤ slabNode e p₀ := (hp₀.isPrimePow.pow (by omega)).two_le
  unfold slabLagCoeff
  have key : ∀ a ∈ slabIndex Q M, (∑ b ∈ slabIndex Q M,
      if slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
        Real.log ((slabNode e p₀ : ℕ) : ℝ) then σ ^ a.2 * σ ^ b.2 else 0) =
        if a.2 = 1 then σ else 0 := by
    intro a ha
    have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have ha1 := (Finset.mem_product.mp ha).1
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
          Real.log ((slabNode e p₀ : ℕ) : ℝ) ↔ a.2 = 1 ∧ b = (a.1, 0) from ?_) rfl rfl]
    · by_cases h1 : a.2 = 1
      · have hmem : (a.1, 0) ∈ slabIndex Q M := by
          simp only [slabIndex, Finset.mem_product, Finset.mem_range]; exact ⟨ha1, by norm_num⟩
        simp only [h1, true_and, Finset.sum_ite_eq']
        simp [hmem]
      · simp [h1]
    · have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      rw [slabPos_sub_eq_log_iff hQ hp₀ (by omega)]
      constructor
      · intro h
        rcases slab_lag_cases hQ hp₀ hp₀Q he he₀ ha2 hb2 (by omega) h with ⟨-, h1⟩ |
            ⟨hk, h1, h2', -⟩ | ⟨r, -, -, -, h1⟩
        · omega
        · exact ⟨h1, Prod.ext hk.symm h2'⟩
        · exfalso
          have := (eq_of_prime_pow_eq hp₀ (hQ r r.2) he₀ h1).1
          exact hp₀Q (this ▸ r.2)
      · rintro ⟨h1, rfl⟩
        exact slabNum_rung _ _ rfl h1 rfl
  rw [Finset.sum_congr rfl key, slabIndex, Finset.sum_product]
  simp

include hQ hp₀ hp₀Q he he₀ in
/-- **The steps.** The coefficient at `log m_r` is `#{k : k_r ≥ 1} σ`. -/
theorem slabLagCoeff_log_step (M : ℕ) (r : Q) :
    slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log ((slabNode e r : ℕ) : ℝ)) =
      ((slabBox Q M).filter fun k => 1 ≤ k r).card * σ := by
  classical
  have h2 : 2 ≤ slabNode e r := ((hQ r r.2).isPrimePow.pow (by have := he r r.2; omega)).two_le
  unfold slabLagCoeff
  have key : ∀ a ∈ slabIndex Q M, (∑ b ∈ slabIndex Q M,
      if slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
        Real.log ((slabNode e r : ℕ) : ℝ) then σ ^ a.2 * σ ^ b.2 else 0) =
        if a.2 = 1 ∧ 1 ≤ a.1 r then σ else 0 := by
    intro a ha
    have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have ha1 := (Finset.mem_product.mp ha).1
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        slabPos (slabNode e) (slabNode e p₀) a - slabPos (slabNode e) (slabNode e p₀) b =
          Real.log ((slabNode e r : ℕ) : ℝ) ↔
            (a.2 = 1 ∧ 1 ≤ a.1 r) ∧ b = (a.1 - Pi.single r 1, 0) from ?_) rfl rfl]
    · by_cases h1 : a.2 = 1 ∧ 1 ≤ a.1 r
      · simp only [h1, and_self, true_and, Finset.sum_ite_eq']
        have hmem : (a.1 - Pi.single r 1, 0) ∈ slabIndex Q M := by
          refine Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr (by norm_num)⟩
          simp only [slabBox, Fintype.mem_piFinset, Finset.mem_range] at ha1 ⊢
          intro i; have := ha1 i; simp only [Pi.sub_apply]; omega
        simp [hmem]
      · simp only [h1, false_and, if_false, Finset.sum_const_zero]
    · have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      rw [slabPos_sub_eq_log_iff hQ hp₀ (by omega)]
      constructor
      · intro h
        rcases slab_lag_cases hQ hp₀ hp₀Q he he₀ ha2 hb2 (by omega) h with ⟨-, h1⟩ |
            ⟨-, -, -, h1⟩ | ⟨r', hk, h1, h2', h3⟩
        · omega
        · exfalso
          have := (eq_of_prime_pow_eq (hQ r r.2) hp₀ (he r r.2) h1).1
          exact hp₀Q (this ▸ r.2)
        · have hrr : r' = r := Subtype.ext (eq_of_prime_pow_eq (hQ r' r'.2) (hQ r r.2)
            (he r' r'.2) h3.symm).1
          subst hrr
          refine ⟨⟨h1, by rw [hk]; simp⟩, Prod.ext ?_ h2'⟩
          funext i; rw [hk]; simp
      · rintro ⟨⟨h1, h1'⟩, rfl⟩
        refine slabNum_step _ _ r ?_ h1 rfl
        funext i
        by_cases hir : i = r
        · subst hir; simp; omega
        · simp [hir]
  rw [Finset.sum_congr rfl key, slabIndex, Finset.sum_product]
  have : ∀ k ∈ slabBox Q M, (∑ ε ∈ Finset.range 2, if ε = 1 ∧ 1 ≤ k r then σ else 0) =
      if 1 ≤ k r then σ else 0 := by
    intro k _
    simp [Finset.sum_range_succ]
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

include hQ hp₀ hp₀Q he he₀ in
/-- **No other integer lag.** -/
theorem slabLagCoeff_log_eq_zero (M : ℕ) {n : ℕ} (hn : 2 ≤ n) (h₀ : n ≠ slabNode e p₀)
    (hr : ∀ r : Q, n ≠ slabNode e r) :
    slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log n) = 0 := by
  unfold slabLagCoeff
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => if_neg fun h => ?_
  rw [slabPos_sub_eq_log_iff hQ hp₀ (by omega)] at h
  rcases slab_lag_cases hQ hp₀ hp₀Q he he₀ (Finset.mem_range.mp (Finset.mem_product.mp ha).2)
      (Finset.mem_range.mp (Finset.mem_product.mp hb).2) (by omega) h with
    ⟨-, h1⟩ | ⟨-, -, -, h1⟩ | ⟨r, -, -, -, h1⟩
  · omega
  · exact h₀ h1
  · exact hr r h1

end Coefficients

/-! ### 4. The integer-grid Euler cone -/

/-- The deviations `(A − W)/‖c‖²` on the cone blind at every integer `n ≥ 2` outside
`{p^{e(p)} : p ∈ P}`. -/
def gridEulerDeviations (P : Finset ℕ) (e : ℕ → ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn ({n | 2 ≤ n} \ ↑(eulerNodes P e)) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem gridEulerDeviations_subset (P : Finset ℕ) (e : ℕ → ℕ) :
    gridEulerDeviations P e ⊆ eulerDeviations P e := by
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  exact ⟨c, hc, fun j hj => hb j ⟨j.2, hj.2⟩, hpos, rfl⟩

section Deviation

variable {Q : Finset ℕ} (hQ : ∀ i ∈ Q, i.Prime) {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀Q : p₀ ∉ Q)
  {e : ℕ → ℕ} (he : ∀ i ∈ Q, 1 ≤ e i) (he₀ : 1 ≤ e p₀) {σ : ℝ} (hσ : σ ^ 2 = 1) {M N : ℕ}
  (hN : slabBound Q (slabNode e) (slabNode e p₀) M ≤ N)

include hQ hp₀ hN in
theorem logValue_slabTrain {n : ℕ} (hn : 1 ≤ n) :
    logValue (slabTrain Q (slabNode e) (slabNode e p₀) M N σ) n =
      2 * slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log n) *
        (∫ t, (narrowBump N t) ^ 2) / Real.sqrt n := by
  have hm : ∀ i ∈ Q, 1 ≤ slabNode e i := fun i hi => Nat.one_le_pow _ _ (hQ i hi).pos
  have hm₀ : 1 ≤ slabNode e p₀ := Nat.one_le_pow _ _ hp₀.pos
  have e1 := weilTest_slabTrain hm hm₀ hN hn 1 (Or.inl rfl) σ
  have e2 := weilTest_slabTrain hm hm₀ hN hn (-1) (Or.inr rfl) σ
  rw [one_mul] at e1
  rw [neg_one_mul, slabLagCoeff_neg] at e2
  rw [logValue, e1, e2, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

include hQ hp₀ hp₀Q he he₀ hσ hN in
theorem massOf_single_slabTrainFn :
    massOf (Finsupp.single (slabTrainFn Q (slabNode e) (slabNode e p₀) M N σ) 1) =
      2 * (slabBox Q M).card * ∫ t, (narrowBump N t) ^ 2 := by
  have hm : ∀ i ∈ Q, 1 ≤ slabNode e i := fun i hi => Nat.one_le_pow _ _ (hQ i hi).pos
  have hm₀ : 1 ≤ slabNode e p₀ := Nat.one_le_pow _ _ hp₀.pos
  have hk := weilTest_slabTrain hm hm₀ hN le_rfl 1 (Or.inl rfl) σ
  rw [one_mul, slabLagCoeff_zero hQ hp₀ hp₀Q he he₀ hσ, Nat.cast_one, Real.log_one,
    RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm' : ∫ u, ‖slabTrain Q (slabNode e) (slabNode e p₀) M N σ u‖ ^ 2 =
      2 * (slabBox Q M).card * ∫ t, (narrowBump N t) ^ 2 := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact hm'

include hQ hp₀ hp₀Q he he₀ hN in
/-- **The slab train is blind at every integer outside the deleted nodes**, composites included. -/
theorem gridBlind_single_slabTrainFn :
    BlindOn ({n | 2 ≤ n} \ ↑(eulerNodes (insert p₀ Q) e))
      (Finsupp.single (slabTrainFn Q (slabNode e) (slabNode e p₀) M N σ) 1) := by
  intro j ⟨hj2, hj⟩
  have hj' : ∀ p ∈ insert p₀ Q, p ^ e p ≠ (j : ℕ) := fun p hp h =>
    hj (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, hp, h⟩))
  rw [nodeVector_single_test, logVector_apply]
  change logValue (slabTrain Q (slabNode e) (slabNode e p₀) M N σ) j = 0
  rw [logValue_slabTrain hQ hp₀ hN (by have : 2 ≤ (j : ℕ) := hj2; omega),
    slabLagCoeff_log_eq_zero hQ hp₀ hp₀Q he he₀ M hj2
      (fun h => hj' p₀ (Finset.mem_insert_self _ _) h.symm)
      (fun r h => hj' r (Finset.mem_insert_of_mem r.2) h.symm)]
  simp

include hQ hp₀ hp₀Q he he₀ hσ hN in
/-- **The slab deviation**: `σ (w(m₀) + (M/(M+1)) Σ_{r∈Q} w(m_r))`. -/
theorem slab_mem_gridEulerDeviations :
    σ * (ArithmeticFunction.vonMangoldt (p₀ ^ e p₀) / Real.sqrt ((p₀ ^ e p₀ : ℕ) : ℝ) +
        (M / (M + 1)) * ∑ r ∈ Q, ArithmeticFunction.vonMangoldt (r ^ e r) /
          Real.sqrt ((r ^ e r : ℕ) : ℝ)) ∈ gridEulerDeviations (insert p₀ Q) e := by
  classical
  have hP : ∀ p ∈ insert p₀ Q, p.Prime := fun p hp => by
    rcases Finset.mem_insert.mp hp with rfl | h
    · exact hp₀
    · exact hQ p h
  have heP : ∀ p ∈ insert p₀ Q, 1 ≤ e p := fun p hp => by
    rcases Finset.mem_insert.mp hp with rfl | h
    · exact he₀
    · exact he p h
  have hmass := massOf_single_slabTrainFn hQ hp₀ hp₀Q he he₀ hσ hN
  have hI := integral_narrowBump_sq_pos N
  have hbox : (0 : ℝ) < (slabBox Q M).card := by
    have : (slabBox Q M).Nonempty := ⟨fun _ => 0, by simp [slabBox]⟩
    exact_mod_cast this.card_pos
  have hpos : 0 < massOf (Finsupp.single (slabTrainFn Q (slabNode e) (slabNode e p₀) M N σ) 1) := by
    rw [hmass]; positivity
  have hb := gridBlind_single_slabTrainFn hQ hp₀ hp₀Q he he₀ hN (σ := σ)
  have hbPP : BlindOn (primePowerNodes \ ↑(eulerNodes (insert p₀ Q) e))
      (Finsupp.single (slabTrainFn Q (slabNode e) (slabNode e p₀) M N σ) 1) :=
    fun j hj => hb j ⟨j.2, hj.2⟩
  refine ⟨_, fun g => ?_, hb, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · set I := ∫ t, (narrowBump N t) ^ 2
    set B : ℝ := (slabBox Q M).card
    set c : ℝ := (M : ℝ) / (M + 1)
    have hnode : ∀ p ∈ insert p₀ Q, nodeAt (Finsupp.single (slabTrainFn Q (slabNode e)
        (slabNode e p₀) M N σ) 1) (p ^ e p) =
        2 * slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ (Real.log ((p ^ e p : ℕ) : ℝ)) * I /
          Real.sqrt ((p ^ e p : ℕ) : ℝ) := by
      intro p hp
      have h2 := two_le_pow hP heP hp
      rw [nodeAt, dif_pos h2, nodeVector_single_test, logVector_apply]
      exact logValue_slabTrain (n := p ^ e p) hQ hp₀ hN (by omega)
    have hbase : slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ
        (Real.log ((p₀ ^ e p₀ : ℕ) : ℝ)) = B * σ :=
      slabLagCoeff_log_base hQ hp₀ hp₀Q he he₀ (σ := σ) M
    have hstep : ∀ r ∈ Q, slabLagCoeff Q (slabNode e) (slabNode e p₀) M σ
        (Real.log ((r ^ e r : ℕ) : ℝ)) = c * B * σ := by
      intro r hr
      have h := slabLagCoeff_log_step hQ hp₀ hp₀Q he he₀ (σ := σ) M ⟨r, hr⟩
      have hc := card_filter_slabBox_mul (Q := Q) M ⟨r, hr⟩
      have hM : (0 : ℝ) < M + 1 := by positivity
      have hc' : (((slabBox Q M).filter fun k => 1 ≤ k ⟨r, hr⟩).card : ℝ) = c * B := by
        simp only [c, B]
        rw [div_mul_eq_mul_div, eq_div_iff hM.ne']
        exact_mod_cast hc
      exact h.trans (by rw [hc'])
    have hsq : ∀ p ∈ insert p₀ Q, 0 < Real.sqrt ((p ^ e p : ℕ) : ℝ) := fun p hp =>
      Real.sqrt_pos.mpr (by have := two_le_pow hP heP hp; exact_mod_cast (show 0 < p ^ e p by omega))
    have hs₀ := hsq p₀ (Finset.mem_insert_self _ _)
    rw [nodeArchEnergy_eq_weilEnergy_add_finset _ hbPP, add_sub_cancel_left, eulerNodes,
      Finset.sum_image (injOn_eulerNodes hP heP), Finset.sum_insert hp₀Q, hmass,
      hnode p₀ (Finset.mem_insert_self _ _), hbase]
    have hsum : ∑ r ∈ Q, (ArithmeticFunction.vonMangoldt (r ^ e r) : ℝ) *
        nodeAt (Finsupp.single (slabTrainFn Q (slabNode e) (slabNode e p₀) M N σ) 1) (r ^ e r) =
        (2 * c * B * σ * I) * ∑ r ∈ Q, ArithmeticFunction.vonMangoldt (r ^ e r) /
          Real.sqrt ((r ^ e r : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hnode r (Finset.mem_insert_of_mem hr), hstep r hr]
      ring
    rw [hsum, eq_div_iff (by positivity)]
    field_simp
    ring

end Deviation

/-- **Euler additivity on the integer grid: the supremum.** For a nonempty finite set of primes the
deviations on the integer-grid cone have least upper bound `Σ_{p∈P} w(p^{e(p)})`. -/
theorem isLUB_gridEulerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) (hPne : P.Nonempty) :
    IsLUB (gridEulerDeviations P e) (eulerPrice P e) := by
  classical
  obtain ⟨p₀, hp₀P⟩ := hPne
  set Q := P.erase p₀ with hQdef
  have hPQ : P = insert p₀ Q := (Finset.insert_erase hp₀P).symm
  have hp₀Q : p₀ ∉ Q := Finset.notMem_erase p₀ P
  have hQ : ∀ i ∈ Q, i.Prime := fun i hi => hP i (Finset.mem_of_mem_erase hi)
  have heQ : ∀ i ∈ Q, 1 ≤ e i := fun i hi => he i (Finset.mem_of_mem_erase hi)
  refine ⟨fun x hx => (isGreatest_eulerDeviations hP he).2 (gridEulerDeviations_subset P e hx),
    fun b hb => ?_⟩
  set S := ∑ r ∈ Q, ArithmeticFunction.vonMangoldt (r ^ e r) / Real.sqrt ((r ^ e r : ℕ) : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hprice : eulerPrice P e = ArithmeticFunction.vonMangoldt (p₀ ^ e p₀) /
      Real.sqrt ((p₀ ^ e p₀ : ℕ) : ℝ) + S := by
    rw [eulerPrice, hPQ, Finset.sum_insert hp₀Q]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (S / ε)
  have hmem := slab_mem_gridEulerDeviations hQ (hP p₀ hp₀P) hp₀Q heQ (he p₀ hp₀P) (σ := 1)
    (by norm_num) (M := M) (N := slabBound Q (slabNode e) (slabNode e p₀) M) le_rfl
  rw [← hPQ] at hmem
  have hle := hb hmem
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hsmall : S / (M + 1) < ε := by
    rw [div_lt_iff₀ hM1]; rw [div_lt_iff₀ hε] at hM; nlinarith
  have hfrac : (M : ℝ) / (M + 1) * S = S - S / (M + 1) := by field_simp; ring
  rw [hprice]
  rw [one_mul, hfrac] at hle
  linarith

/-- **Euler additivity on the integer grid: the infimum** `−Σ_{p∈P} w(p^{e(p)})`. -/
theorem isGLB_gridEulerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) (hPne : P.Nonempty) :
    IsGLB (gridEulerDeviations P e) (-eulerPrice P e) := by
  classical
  obtain ⟨p₀, hp₀P⟩ := hPne
  set Q := P.erase p₀ with hQdef
  have hPQ : P = insert p₀ Q := (Finset.insert_erase hp₀P).symm
  have hp₀Q : p₀ ∉ Q := Finset.notMem_erase p₀ P
  have hQ : ∀ i ∈ Q, i.Prime := fun i hi => hP i (Finset.mem_of_mem_erase hi)
  have heQ : ∀ i ∈ Q, 1 ≤ e i := fun i hi => he i (Finset.mem_of_mem_erase hi)
  refine ⟨fun x hx => (isLeast_eulerDeviations hP he).2 (gridEulerDeviations_subset P e hx),
    fun b hb => ?_⟩
  set S := ∑ r ∈ Q, ArithmeticFunction.vonMangoldt (r ^ e r) / Real.sqrt ((r ^ e r : ℕ) : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hprice : eulerPrice P e = ArithmeticFunction.vonMangoldt (p₀ ^ e p₀) /
      Real.sqrt ((p₀ ^ e p₀ : ℕ) : ℝ) + S := by
    rw [eulerPrice, hPQ, Finset.sum_insert hp₀Q]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (S / ε)
  have hmem := slab_mem_gridEulerDeviations hQ (hP p₀ hp₀P) hp₀Q heQ (he p₀ hp₀P) (σ := -1)
    (by norm_num) (M := M) (N := slabBound Q (slabNode e) (slabNode e p₀) M) le_rfl
  rw [← hPQ] at hmem
  have hle := hb hmem
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hsmall : S / (M + 1) < ε := by
    rw [div_lt_iff₀ hM1]; rw [div_lt_iff₀ hε] at hM; nlinarith
  have hfrac : (M : ℝ) / (M + 1) * S = S - S / (M + 1) := by field_simp; ring
  rw [hprice]
  rw [hfrac] at hle
  linarith

/-- **Deleting every prime up to `x` from the integer grid** costs `Σ_{p ≤ x} log p/√p`, as on the
prime-power cone: the composites never matter. -/
theorem isGLB_gridEulerDeviations_primes_le (x : ℕ) (hx : 2 ≤ x) :
    IsGLB (gridEulerDeviations ((Finset.range (x + 1)).filter Nat.Prime) fun _ => 1)
      (-∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p / Real.sqrt p) := by
  have hP : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p.Prime := fun p hp =>
    (Finset.mem_filter.mp hp).2
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  have h := isGLB_gridEulerDeviations hP (e := fun _ => 1) (fun _ _ => le_rfl) hne
  rwa [eulerPrice_eq hP fun _ _ => le_rfl, Finset.sum_congr rfl fun p _ => by rw [pow_one]] at h

end

end GaloisForLFunctions.BiScaleUncertainty
