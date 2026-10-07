import GaloisForLFunctions.RHTower.WeilZetaSquareMoments

/-!
# Möbius mollification de-tilts the Kakutani–Poisson functional of `|ζ|²`

The leading term of the windowed twisted second moment
`∫ ω_L(t) |ζ(1/2+it)|² cos((log u − log w)t) dt` is `ρ(u,w) W(L)`, where
`ρ(u,w) = (lcm(u,w)/gcd(u,w))^{-1/2}` (`kpCorr`) and `W(L) = Re ∫ ω_L log t`
(`exists_abs_momentRe_sub_le`). Equivalently, `ρ(u,w)` is the integral of `z(u) conj z(w)` against
the product of Poisson kernels `⊗_p P_{p^{-1/2}}` on the Bohr torus.

Multiply the weight by `|M_P(t)|² = Π_{p ∈ P} |1 − p^{-1/2-it}|² = Π_{p ∈ P} (1 + 1/p − 2p^{-1/2} cos(t log p))`
(`mollWeight`) for a finite set `P` of primes. Then the leading coefficient becomes

`T_P(u,w) = Π_{p ∈ P}(1 − 1/p) · [v_p(u) = v_p(w) for all p ∈ P] · ρ(u,w)`  (`closedT`).

So the Poisson kernels at the primes of `P` are replaced by `(1 − 1/p)` times Haar measure
(`exists_abs_momentP_sub_le`). The proof inducts on `P`. Adding a prime `q` multiplies the weight
by `1 + 1/q − 2q^{-1/2}cos(t log q)`, and `T_P` satisfies the same recursion (`closedT_insert`) by the
local identity `(1 + 1/q)ρ − q^{-1/2}(ρ(uq,w) + ρ(u,wq)) = (1 − 1/q)[v_q(u) = v_q(w)]ρ`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilZetaSquare

open RHTower.ZetaNotch

/-! ## The Kakutani–Poisson correlation -/

/-- `ρ(u, w) = (lcm(u,w)/gcd(u,w))^{-1/2}`. -/
def kpCorr (u w : ℕ) : ℝ := ((Nat.lcm u w : ℝ) / (Nat.gcd u w : ℝ)) ^ (-(1 / 2 : ℝ))

theorem kpCorr_symm (u w : ℕ) : kpCorr u w = kpCorr w u := by
  simp [kpCorr, Nat.lcm_comm, Nat.gcd_comm]

theorem kpCorr_nonneg (u w : ℕ) : 0 ≤ kpCorr u w :=
  Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

theorem kpCorr_self {a : ℕ} (ha : a ≠ 0) : kpCorr a a = 1 := by
  have h : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  simp [kpCorr, Nat.lcm_self, Nat.gcd_self, div_self h]

theorem kpCorr_one_right (n : ℕ) : kpCorr n 1 = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  simp [kpCorr]

/-- `ρ(u,w) ≤ √w · u^{-1/2}`. -/
theorem kpCorr_le {u w : ℕ} (hu : u ≠ 0) (hw : w ≠ 0) :
    kpCorr u w ≤ Real.sqrt w * (u : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hw0 : (0 : ℝ) < w := by exact_mod_cast Nat.pos_of_ne_zero hw
  have hg0 : (0 : ℝ) < Nat.gcd u w := by exact_mod_cast Nat.gcd_pos_of_pos_left w (Nat.pos_of_ne_zero hu)
  have hlcm : (u : ℝ) ≤ Nat.lcm u w := by
    exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos (Nat.pos_of_ne_zero hu) (Nat.pos_of_ne_zero hw))
      (Nat.dvd_lcm_left u w)
  have hgcd : (Nat.gcd u w : ℝ) ≤ w := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hw) (Nat.gcd_dvd_right u w)
  have hratio : (u : ℝ) / w ≤ (Nat.lcm u w : ℝ) / Nat.gcd u w :=
    div_le_div₀ (by positivity) hlcm hg0 hgcd
  calc kpCorr u w ≤ ((u : ℝ) / w) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hratio (by norm_num)
    _ = Real.sqrt w * (u : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow hu0.le hw0.le, Real.rpow_neg hw0.le, div_inv_eq_mul, Real.sqrt_eq_rpow]
        ring

/-- For coprime `h, k`: `ρ(h,k) = (hk)^{-1/2}`. -/
theorem kpCorr_reduce {u w : ℕ} (hu : 0 < u) :
    kpCorr u w = (Real.sqrt (((u / Nat.gcd u w : ℕ) : ℝ) * ((w / Nat.gcd u w : ℕ) : ℝ)))⁻¹ := by
  set g := Nat.gcd u w with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left w hu
  obtain ⟨h, hh⟩ := Nat.gcd_dvd_left u w
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_right u w
  rw [← hg] at hh hk
  have hlcm : Nat.lcm u w = g * h * k := by
    have h1 := Nat.gcd_mul_lcm u w
    rw [← hg] at h1
    have : g * Nat.lcm u w = g * (g * h * k) := by
      rw [h1]
      calc u * w = (g * h) * (g * k) := by rw [← hh, ← hk]
        _ = g * (g * h * k) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos this
  have huq : u / g = h := by rw [hh, Nat.mul_div_cancel_left _ hgpos]
  have hwq : w / g = k := by rw [hk, Nat.mul_div_cancel_left _ hgpos]
  rw [huq, hwq, kpCorr, ← hg, hlcm]
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  push_cast
  rw [show (g : ℝ) * h * k / g = h * k by field_simp, Real.sqrt_eq_rpow, ← Real.rpow_neg
    (by positivity)]

/-! ## Local change under multiplication by a prime -/

theorem factorization_mul_prime_apply {u q : ℕ} (hu : u ≠ 0) (hq : q.Prime) (p : ℕ) :
    (u * q).factorization p = u.factorization p + if p = q then 1 else 0 := by
  rw [Nat.factorization_mul hu hq.ne_zero, Finsupp.add_apply, hq.factorization]
  by_cases hp : p = q
  · subst hp; simp
  · simp [hp]

theorem gcd_lcm_mul_prime {u w q : ℕ} (hu : u ≠ 0) (hw : w ≠ 0) (hq : q.Prime) :
    (w.factorization q ≤ u.factorization q →
      Nat.gcd (u * q) w = Nat.gcd u w ∧ Nat.lcm (u * q) w = Nat.lcm u w * q) ∧
    (u.factorization q < w.factorization q →
      Nat.gcd (u * q) w = Nat.gcd u w * q ∧ Nat.lcm (u * q) w = Nat.lcm u w) := by
  have huq : u * q ≠ 0 := mul_ne_zero hu hq.ne_zero
  have hg : Nat.gcd u w ≠ 0 := Nat.gcd_ne_zero_left hu
  have hl : Nat.lcm u w ≠ 0 := Nat.lcm_ne_zero hu hw
  have hgq : Nat.gcd (u * q) w ≠ 0 := Nat.gcd_ne_zero_left huq
  have hlq : Nat.lcm (u * q) w ≠ 0 := Nat.lcm_ne_zero huq hw
  have fg : ∀ p, (Nat.gcd (u * q) w).factorization p =
      min (u.factorization p + if p = q then 1 else 0) (w.factorization p) := by
    intro p; rw [Nat.factorization_gcd huq hw, Finsupp.inf_apply, factorization_mul_prime_apply hu hq]
  have fl : ∀ p, (Nat.lcm (u * q) w).factorization p =
      max (u.factorization p + if p = q then 1 else 0) (w.factorization p) := by
    intro p; rw [Nat.factorization_lcm huq hw, Finsupp.sup_apply, factorization_mul_prime_apply hu hq]
  have fg0 : ∀ p, (Nat.gcd u w).factorization p = min (u.factorization p) (w.factorization p) := by
    intro p; rw [Nat.factorization_gcd hu hw, Finsupp.inf_apply]
  have fl0 : ∀ p, (Nat.lcm u w).factorization p = max (u.factorization p) (w.factorization p) := by
    intro p; rw [Nat.factorization_lcm hu hw, Finsupp.sup_apply]
  constructor
  · intro hle
    refine ⟨Nat.eq_of_factorization_eq hgq hg fun p => ?_,
      Nat.eq_of_factorization_eq hlq (mul_ne_zero hl hq.ne_zero) fun p => ?_⟩
    · rw [fg, fg0]
      by_cases hp : p = q
      · subst hp; simp only [if_true]; omega
      · simp [hp]
    · rw [fl, factorization_mul_prime_apply hl hq, fl0]
      by_cases hp : p = q
      · subst hp; simp only [if_true]; omega
      · simp [hp]
  · intro hlt
    refine ⟨Nat.eq_of_factorization_eq hgq (mul_ne_zero hg hq.ne_zero) fun p => ?_,
      Nat.eq_of_factorization_eq hlq hl fun p => ?_⟩
    · rw [fg, factorization_mul_prime_apply hg hq, fg0]
      by_cases hp : p = q
      · subst hp; simp only [if_true]; omega
      · simp [hp]
    · rw [fl, fl0]
      by_cases hp : p = q
      · subst hp; simp only [if_true]; omega
      · simp [hp]

/-- **`ρ(uq, w)`.** Multiplying `u` by a prime `q` scales `ρ` by `q^{-1/2}` if `v_q(w) ≤ v_q(u)`,
and by `q^{1/2}` otherwise. -/
theorem kpCorr_mul_prime_left {u w q : ℕ} (hu : u ≠ 0) (hw : w ≠ 0) (hq : q.Prime) :
    kpCorr (u * q) w = kpCorr u w *
      (if w.factorization q ≤ u.factorization q then (q : ℝ) ^ (-(1 / 2 : ℝ))
        else (q : ℝ) ^ (1 / 2 : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hg0 : (0 : ℝ) < Nat.gcd u w := by exact_mod_cast Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left hu)
  have hl0 : (0 : ℝ) < Nat.lcm u w := by exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hu hw)
  obtain ⟨h1, h2⟩ := gcd_lcm_mul_prime hu hw hq
  split_ifs with hle
  · obtain ⟨hg, hl⟩ := h1 hle
    rw [kpCorr, kpCorr, hg, hl]
    push_cast
    rw [mul_div_right_comm, Real.mul_rpow (by positivity) hq0.le]
  · push Not at hle
    obtain ⟨hg, hl⟩ := h2 hle
    rw [kpCorr, kpCorr, hg, hl]
    push_cast
    rw [div_mul_eq_div_div, Real.div_rpow (by positivity) hq0.le, Real.rpow_neg hq0.le,
      div_inv_eq_mul]

theorem kpCorr_mul_prime_right {u w q : ℕ} (hu : u ≠ 0) (hw : w ≠ 0) (hq : q.Prime) :
    kpCorr u (w * q) = kpCorr u w *
      (if u.factorization q ≤ w.factorization q then (q : ℝ) ^ (-(1 / 2 : ℝ))
        else (q : ℝ) ^ (1 / 2 : ℝ)) := by
  rw [kpCorr_symm, kpCorr_mul_prime_left hw hu hq, kpCorr_symm]

/-! ## The de-tilted coefficient -/

/-- `Π_{p ∈ P} (1 − 1/p)`. -/
def kpMass (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

theorem kpMass_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 0 < kpMass P := by
  refine Finset.prod_pos fun p hp => ?_
  have : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

open scoped Classical in
/-- `T_P(u,w) = Π_{p∈P}(1 − 1/p) · [v_p(u) = v_p(w) for p ∈ P] · ρ(u,w)`. -/
def closedT (P : Finset ℕ) (u w : ℕ) : ℝ :=
  kpMass P * (if ∀ p ∈ P, u.factorization p = w.factorization p then kpCorr u w else 0)

theorem closedT_empty (u w : ℕ) : closedT ∅ u w = kpCorr u w := by
  simp [closedT, kpMass]

/-- **The recursion** for adding a prime `q ∉ P`. -/
theorem closedT_insert {P : Finset ℕ} {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) {u w : ℕ} (hu : u ≠ 0)
    (hw : w ≠ 0) :
    closedT (insert q P) u w = (1 + 1 / (q : ℝ)) * closedT P u w -
      (q : ℝ) ^ (-(1 / 2 : ℝ)) * (closedT P (u * q) w + closedT P u (w * q)) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hcondL : (∀ p ∈ P, (u * q).factorization p = w.factorization p) ↔
      ∀ p ∈ P, u.factorization p = w.factorization p := by
    refine forall₂_congr fun p hp => ?_
    have hpq : p ≠ q := fun h => hqP (h ▸ hp)
    rw [factorization_mul_prime_apply hu hq, if_neg hpq, add_zero]
  have hcondR : (∀ p ∈ P, u.factorization p = (w * q).factorization p) ↔
      ∀ p ∈ P, u.factorization p = w.factorization p := by
    refine forall₂_congr fun p hp => ?_
    have hpq : p ≠ q := fun h => hqP (h ▸ hp)
    rw [factorization_mul_prime_apply hw hq, if_neg hpq, add_zero]
  have hmass : kpMass (insert q P) = (1 - 1 / (q : ℝ)) * kpMass P := by
    rw [kpMass, Finset.prod_insert hqP]; rfl
  have hhalf : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / q := by
    rw [← Real.rpow_add hq0, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      one_div]
  have hone : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hq0, show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]
  unfold closedT
  rw [hmass]
  by_cases hc : ∀ p ∈ P, u.factorization p = w.factorization p
  · rw [if_pos (hcondL.mpr hc), if_pos (hcondR.mpr hc), if_pos hc,
      kpCorr_mul_prime_left hu hw hq, kpCorr_mul_prime_right hu hw hq]
    set ρ := kpCorr u w
    set m := kpMass P
    rcases lt_trichotomy (u.factorization q) (w.factorization q) with hlt | heq | hgt
    · rw [if_neg (fun h => hlt.ne (h q (Finset.mem_insert_self q P))),
        if_neg (by omega : ¬ w.factorization q ≤ u.factorization q), if_pos hlt.le]
      have : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (m * (ρ * (q : ℝ) ^ (1 / 2 : ℝ)) +
          m * (ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)))) = m * ρ * (1 + 1 / q) := by
        rw [← hhalf]; linear_combination (m * ρ) * hone
      rw [this]; ring
    · have hi : ∀ p ∈ insert q P, u.factorization p = w.factorization p := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        exacts [heq, hc p hp]
      rw [if_pos hi, if_pos heq.ge, if_pos heq.le]
      have : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (m * (ρ * (q : ℝ) ^ (-(1 / 2 : ℝ))) +
          m * (ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)))) = m * ρ * (2 / q) := by
        rw [show (2 : ℝ) / q = 1 / q + 1 / q by ring, ← hhalf]; ring
      rw [this]; ring
    · rw [if_neg (fun h => hgt.ne' (h q (Finset.mem_insert_self q P))), if_pos hgt.le,
        if_neg (by omega : ¬ u.factorization q ≤ w.factorization q)]
      have : (q : ℝ) ^ (-(1 / 2 : ℝ)) * (m * (ρ * (q : ℝ) ^ (-(1 / 2 : ℝ))) +
          m * (ρ * (q : ℝ) ^ (1 / 2 : ℝ))) = m * ρ * (1 + 1 / q) := by
        rw [← hhalf]; linear_combination (m * ρ) * hone
      rw [this]; ring
  · rw [if_neg (fun h => hc fun p hp => h p (Finset.mem_insert_of_mem hp)),
      if_neg (fun h => hc (hcondL.mp h)), if_neg (fun h => hc (hcondR.mp h)), if_neg hc]
    ring

/-! ## The mollified weight -/

/-- `|M_P(t)|² = Π_{p ∈ P} (1 + 1/p − 2 p^{-1/2} cos(t log p))`. -/
def mollWeight (P : Finset ℕ) (t : ℝ) : ℝ :=
  ∏ p ∈ P, (1 + 1 / (p : ℝ) - 2 * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p))

theorem mollFactor_nonneg {p : ℕ} (hp : 1 ≤ p) (t : ℝ) :
    0 ≤ 1 + 1 / (p : ℝ) - 2 * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    rw [Real.rpow_neg_one]
  have hr : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hc := Real.cos_le_one (t * Real.log p)
  nlinarith [sq_nonneg (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))]

theorem mollFactor_le {p : ℕ} (hp : 1 ≤ p) (t : ℝ) :
    1 + 1 / (p : ℝ) - 2 * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p) ≤ 4 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
  have hr0 : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hr1 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have hc := Real.neg_one_le_cos (t * Real.log p)
  nlinarith

theorem mollWeight_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℝ) : 0 ≤ mollWeight P t :=
  Finset.prod_nonneg fun p hp => mollFactor_nonneg (hP p hp).one_lt.le t

theorem mollWeight_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    mollWeight P t ≤ 4 ^ P.card := by
  rw [mollWeight, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun p hp => mollFactor_nonneg (hP p hp).one_lt.le t)
    fun p hp => mollFactor_le (hP p hp).one_lt.le t

theorem continuous_mollWeight (P : Finset ℕ) : Continuous (mollWeight P) := by
  unfold mollWeight
  exact continuous_finsetProd _ fun p _ => by fun_prop

/-- The pointwise recursion for `mollWeight · cos`. -/
theorem mollWeight_insert_mul_cos {P : Finset ℕ} {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) {u w : ℕ}
    (hu : u ≠ 0) (hw : w ≠ 0) (t : ℝ) :
    mollWeight (insert q P) t * Real.cos ((Real.log u - Real.log w) * t) =
      (1 + 1 / (q : ℝ)) * (mollWeight P t * Real.cos ((Real.log u - Real.log w) * t)) -
        (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          (mollWeight P t * Real.cos ((Real.log (u * q : ℕ) - Real.log w) * t) +
            mollWeight P t * Real.cos ((Real.log u - Real.log (w * q : ℕ)) * t)) := by
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [mollWeight, Finset.prod_insert hqP, ← mollWeight]
  push_cast
  rw [Real.log_mul hu0 hq0, Real.log_mul hw0 hq0]
  have h1 : Real.cos ((Real.log u + Real.log q - Real.log w) * t) =
      Real.cos ((Real.log u - Real.log w) * t + t * Real.log q) := by ring_nf
  have h2 : Real.cos ((Real.log u - (Real.log w + Real.log q)) * t) =
      Real.cos ((Real.log u - Real.log w) * t - t * Real.log q) := by ring_nf
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

/-! ## The mollified twisted second moment -/

/-- `∫ ω_L |ζ|² |M_P|² cos((log u − log w)t)`. -/
def momentP (P : Finset ℕ) (L : ℝ) (u w : ℕ) : ℝ :=
  ∫ t, win L t * zsq t * mollWeight P t * Real.cos ((Real.log u - Real.log w) * t)

theorem integrable_momentP_integrand (P : Finset ℕ) {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    Integrable fun t => win L t * zsq t * mollWeight P t * Real.cos (ξ * t) := by
  have h := integrable_win_mul hL (g := fun t => zsq t * mollWeight P t * Real.cos (ξ * t))
    ((continuous_zsq.mul (continuous_mollWeight P)).mul (by fun_prop))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  ring

theorem momentP_insert {P : Finset ℕ} {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) {L : ℝ} (hL : 0 < L)
    {u w : ℕ} (hu : u ≠ 0) (hw : w ≠ 0) :
    momentP (insert q P) L u w = (1 + 1 / (q : ℝ)) * momentP P L u w -
      (q : ℝ) ^ (-(1 / 2 : ℝ)) * (momentP P L (u * q) w + momentP P L u (w * q)) := by
  unfold momentP
  have hpt : ∀ t, win L t * zsq t * mollWeight (insert q P) t * Real.cos ((Real.log u - Real.log w) * t) =
      (1 + 1 / (q : ℝ)) * (win L t * zsq t * mollWeight P t * Real.cos ((Real.log u - Real.log w) * t)) -
        (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          (win L t * zsq t * mollWeight P t * Real.cos ((Real.log (u * q : ℕ) - Real.log w) * t) +
            win L t * zsq t * mollWeight P t * Real.cos ((Real.log u - Real.log (w * q : ℕ)) * t)) := by
    intro t
    have := mollWeight_insert_mul_cos hq hqP hu hw t
    calc _ = win L t * zsq t * (mollWeight (insert q P) t * Real.cos ((Real.log u - Real.log w) * t)) := by
          ring
      _ = _ := by rw [this]; ring
  simp_rw [hpt]
  have i1 := integrable_momentP_integrand P hL (Real.log u - Real.log w)
  have i2 := integrable_momentP_integrand P hL (Real.log (u * q : ℕ) - Real.log w)
  have i3 := integrable_momentP_integrand P hL (Real.log u - Real.log (w * q : ℕ))
  have i23 : Integrable fun t =>
      win L t * zsq t * mollWeight P t * Real.cos ((Real.log (u * q : ℕ) - Real.log w) * t) +
        win L t * zsq t * mollWeight P t * Real.cos ((Real.log u - Real.log (w * q : ℕ)) * t) := i2.add i3
  rw [integral_sub (i1.const_mul _) (i23.const_mul _), integral_const_mul,
    integral_const_mul, integral_add i2 i3]

/-- **De-tilting.** For a finite set `P` of primes there is `C` with
`|∫ ω_L |ζ|² |M_P|² cos((log u − log w)t) − T_P(u,w) W(L)| ≤ C u w L` for all `u, w ≥ 1`, `L ≥ 16`. -/
theorem exists_abs_momentP_sub_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {u w : ℕ}, 0 < u → 0 < w →
      |momentP P L u w - closedT P u w * (logWindow L).re| ≤ C * ((u : ℝ) * w) * L := by
  induction P using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hmain⟩ := exists_abs_momentRe_sub_le
    refine ⟨C, hC, fun {L} hL {u w} hu hw => ?_⟩
    set g := Nat.gcd u w with hg
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left w hu
    have hhpos : 0 < u / g := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u w)) hgpos
    have hkpos : 0 < w / g := Nat.div_pos (Nat.le_of_dvd hw (Nat.gcd_dvd_right u w)) hgpos
    have hcop : Nat.Coprime (u / g) (w / g) := Nat.coprime_div_gcd_div_gcd hgpos
    have h := hmain hL hhpos hkpos hcop
    have hlog : Real.log ((u / g : ℕ) : ℝ) - Real.log ((w / g : ℕ) : ℝ) = Real.log u - Real.log w := by
      have hgd : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
      rw [Nat.cast_div (Nat.gcd_dvd_left u w) hgd, Nat.cast_div (Nat.gcd_dvd_right u w) hgd,
        Real.log_div (by exact_mod_cast hu.ne') hgd, Real.log_div (by exact_mod_cast hw.ne') hgd]
      ring
    have hmom : momentP ∅ L u w = momentRe L (Real.log u - Real.log w) := by
      simp [momentP, momentRe, mollWeight]
    rw [hlog, ← kpCorr_reduce hu] at h
    rw [hmom, closedT_empty]
    refine h.trans ?_
    have hL0 : 0 ≤ L := by linarith
    have hle : ((u / g : ℕ) : ℝ) * ((w / g : ℕ) : ℝ) ≤ (u : ℝ) * w := by
      have h1 : ((u / g : ℕ) : ℝ) ≤ u := by exact_mod_cast Nat.div_le_self u g
      have h2 : ((w / g : ℕ) : ℝ) ≤ w := by exact_mod_cast Nat.div_le_self w g
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    gcongr
  | insert q P hqP ih =>
    have hq : q.Prime := hP q (Finset.mem_insert_self q P)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    obtain ⟨C, hC, hmain⟩ := ih hP'
    refine ⟨C * (2 + 2 * q), by positivity, fun {L} hL {u w} hu hw => ?_⟩
    have hL0 : 0 < L := by linarith
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
    have hqpow0 : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hqpow1 : (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num)
    have huq : 0 < u * q := Nat.mul_pos hu hq.pos
    have hwq : 0 < w * q := Nat.mul_pos hw hq.pos
    rw [momentP_insert hq hqP hL0 hu.ne' hw.ne', closedT_insert hq hqP hu.ne' hw.ne']
    set W := (logWindow L).re
    have e1 := hmain hL hu hw
    have e2 := hmain hL huq hw
    have e3 := hmain hL hu hwq
    push_cast at e2 e3
    have hrw : (1 + 1 / (q : ℝ)) * momentP P L u w - (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        (momentP P L (u * q) w + momentP P L u (w * q)) -
        ((1 + 1 / (q : ℝ)) * closedT P u w - (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          (closedT P (u * q) w + closedT P u (w * q))) * W =
        (1 + 1 / (q : ℝ)) * (momentP P L u w - closedT P u w * W) -
          (q : ℝ) ^ (-(1 / 2 : ℝ)) * ((momentP P L (u * q) w - closedT P (u * q) w * W) +
            (momentP P L u (w * q) - closedT P u (w * q) * W)) := by ring
    rw [hrw]
    have hinv : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
    have hA : 0 ≤ C * ((u : ℝ) * w) * L := by positivity
    calc |(1 + 1 / (q : ℝ)) * (momentP P L u w - closedT P u w * W) -
          (q : ℝ) ^ (-(1 / 2 : ℝ)) * ((momentP P L (u * q) w - closedT P (u * q) w * W) +
            (momentP P L u (w * q) - closedT P u (w * q) * W))|
        ≤ (1 + 1 / (q : ℝ)) * (C * ((u : ℝ) * w) * L) +
            1 * (C * ((u : ℝ) * q * w) * L + C * ((u : ℝ) * (w * q)) * L) := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_pos (by positivity)]
            exact mul_le_mul_of_nonneg_left e1 (by positivity)
          · rw [abs_mul, abs_of_nonneg hqpow0]
            refine mul_le_mul hqpow1 ((abs_add_le _ _).trans (add_le_add e2 e3)) (abs_nonneg _) zero_le_one
      _ ≤ 2 * (C * ((u : ℝ) * w) * L) + 2 * q * (C * ((u : ℝ) * w) * L) := by
          have h2 : (1 + 1 / (q : ℝ)) * (C * ((u : ℝ) * w) * L) ≤ 2 * (C * ((u : ℝ) * w) * L) := by
            nlinarith
          have h3 : 1 * (C * ((u : ℝ) * q * w) * L + C * ((u : ℝ) * (w * q)) * L) =
              2 * q * (C * ((u : ℝ) * w) * L) := by ring
          linarith
      _ = C * (2 + 2 * q) * ((u : ℝ) * w) * L := by ring

end RHTower.WeilZetaSquare
