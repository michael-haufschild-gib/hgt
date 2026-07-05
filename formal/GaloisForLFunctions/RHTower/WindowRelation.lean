/-
The window relation (MWM lane, W1 — task #129; doc 18-window-relation.md).

For window data closed under the critical-line reflection `z ↦ 1 − z̄` with
reflection-invariant multiplicities, the bookkeeping identity

  (ID)  D = L + 2·N    (total order = on-line order + twice the right-half order)

holds, and hence  D ≡ L (mod 2^{k+1}) ⟺ 2^k ∣ N. Instantiated on ξ:

* `xi_window_relation_of_ladder` — the ladder rung `RHLadder k` forces the window
  relation D ≡ L (mod 2^{k+1}) for EVERY reflection-closed zero configuration of ξ
  (closure and invariance are supplied by the banked equivariances
  `xi_orderAt_conj`, `xi_orderAt_one_sub`).
* `pair_window_relation_iff` — the shrunk-window reading: for the two-point
  configuration {ρ₀, 1−ρ̄₀} of an off-line point, the relation IS the rung
  `2^k ∣ mult`, per zero.

Together these are the formal content of doc 18 §2: the ladder ⟺ the per-window
relation between the two boundary invariants (whose dictionary readings — deck class
at level 2^{k+1} and seam ledger at level k+1 — are banked separately).
-/
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.XiDeck

namespace RHTower

open Complex Finset

/-- Reflection across the critical line, `z ↦ 1 − z̄`. -/
noncomputable def lineReflect (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z

theorem lineReflect_re (z : ℂ) : (lineReflect z).re = 1 - z.re := by
  simp [lineReflect]

theorem lineReflect_involutive (z : ℂ) : lineReflect (lineReflect z) = z := by
  simp only [lineReflect, map_sub, map_one, Complex.conj_conj]
  ring

/-- **The bookkeeping identity (ID).** For a finite configuration closed under the
line reflection with reflection-invariant multiplicities: total = on-line + 2·right. -/
theorem window_identity {t : Finset ℂ} {m : ℂ → ℕ}
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hm : ∀ z ∈ t, m (lineReflect z) = m z) :
    ∑ z ∈ t, m z =
      ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z +
        2 * ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not t (fun z => z.re = 1 / 2) m
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (t.filter (fun z => ¬ z.re = 1 / 2)) (fun z => 1 / 2 < z.re) m
  have hR : (t.filter (fun z => ¬ z.re = 1 / 2)).filter (fun z => 1 / 2 < z.re)
      = t.filter (fun z => 1 / 2 < z.re) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, -⟩, hlt⟩
      exact ⟨hz, hlt⟩
    · rintro ⟨hz, hlt⟩
      exact ⟨⟨hz, ne_of_gt hlt⟩, hlt⟩
  have hL : (t.filter (fun z => ¬ z.re = 1 / 2)).filter (fun z => ¬ 1 / 2 < z.re)
      = t.filter (fun z => z.re < 1 / 2) := by
    ext z
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨hz, hne⟩, hle⟩
      exact ⟨hz, lt_of_le_of_ne hle hne⟩
    · rintro ⟨hz, hlt⟩
      exact ⟨⟨hz, ne_of_lt hlt⟩, le_of_lt hlt⟩
  have hbij : ∑ z ∈ t.filter (fun z => z.re < 1 / 2), m z
      = ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z := by
    refine Finset.sum_nbij' lineReflect lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hclosed z hz.1, ?_⟩
      rw [lineReflect_re]
      linarith [hz.2]
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hclosed z hz.1, ?_⟩
      rw [lineReflect_re]
      linarith [hz.2]
    · intro z _
      exact lineReflect_involutive z
    · intro z _
      exact lineReflect_involutive z
    · intro z hz
      rw [Finset.mem_filter] at hz
      exact (hm z hz.1).symm
  rw [hR, hL] at hsplit2
  omega

/-- The relation reads the rung: `D ≡ L (mod 2^{k+1}) ⟺ 2^k ∣ N` given (ID). -/
theorem window_modEq_iff {k D L N : ℕ} (hID : D = L + 2 * N) :
    D ≡ L [MOD 2 ^ (k + 1)] ↔ 2 ^ k ∣ N := by
  subst hID
  have h1 : (L + 2 * N ≡ L [MOD 2 ^ (k + 1)]) ↔
      (L ≡ L + 2 * N [MOD 2 ^ (k + 1)]) := ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  rw [h1, Nat.modEq_iff_dvd' (Nat.le_add_right L (2 * N)),
    Nat.add_sub_cancel_left, pow_succ, mul_comm (2 ^ k) 2,
    mul_dvd_mul_iff_left (two_ne_zero)]

/-- **Ladder ⟹ window relation.** If `RHLadder k` holds, then every
reflection-closed zero configuration of ξ satisfies `D ≡ L (mod 2^{k+1})`. -/
theorem xi_window_relation_of_ladder {k : ℕ} (hlad : RHLadder k)
    {t : Finset ℂ} {m : ℂ → ℕ}
    (hzero : ∀ z ∈ t, xi z = 0)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t) :
    ∑ z ∈ t, m z ≡
      ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)] := by
  classical
  have hmrefl : ∀ z ∈ t, m (lineReflect z) = m z := by
    intro z hz
    have h1 : analyticOrderAt xi (lineReflect z) = analyticOrderAt xi z := by
      simp only [lineReflect]
      rw [xi_orderAt_one_sub, xi_orderAt_conj]
    have h2 := hm _ (hclosed z hz)
    rw [h1, ← hm z hz] at h2
    exact Nat.cast_inj.mp h2
  rw [window_modEq_iff (window_identity hclosed hmrefl)]
  refine Finset.dvd_sum ?_
  intro z hz
  rw [Finset.mem_filter] at hz
  have hright : z ∈ rightHalf := by
    rw [mem_rightHalf]
    exact hz.2
  have hdvd := hlad z hright (hzero z hz.1)
  rw [← hm z hz.1] at hdvd
  exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

/-- **The shrunk-window reading.** For the two-point configuration
`{ρ₀, 1−ρ̄₀}` of an off-line point with common multiplicity `mult`, the window
relation IS the rung: `D ≡ L (mod 2^{k+1}) ⟺ 2^k ∣ mult` — per zero. -/
theorem pair_window_relation_iff {k mult : ℕ} {ρ₀ : ℂ} (hoff : 1 / 2 < ρ₀.re) :
    (∑ z ∈ ({ρ₀, lineReflect ρ₀} : Finset ℂ), (fun _ => mult) z ≡
      ∑ z ∈ ({ρ₀, lineReflect ρ₀} : Finset ℂ).filter (fun z => z.re = 1 / 2),
        (fun _ => mult) z [MOD 2 ^ (k + 1)]) ↔ 2 ^ k ∣ mult := by
  classical
  have hne : ρ₀ ≠ lineReflect ρ₀ := by
    intro h
    have hre := congrArg Complex.re h
    rw [lineReflect_re] at hre
    linarith
  have hD : ∑ z ∈ ({ρ₀, lineReflect ρ₀} : Finset ℂ), (fun _ => mult) z
      = mult + mult := Finset.sum_pair hne
  have hfilter : ({ρ₀, lineReflect ρ₀} : Finset ℂ).filter (fun z => z.re = 1 / 2)
      = (∅ : Finset ℂ) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl)
    · intro h
      linarith
    · rw [lineReflect_re]
      intro h
      linarith
  rw [hD, hfilter, Finset.sum_empty, Nat.modEq_zero_iff_dvd,
    show mult + mult = 2 * mult from by ring, pow_succ, mul_comm (2 ^ k) 2,
    mul_dvd_mul_iff_left (two_ne_zero)]

end RHTower

namespace RHTower

open Complex Finset

/-- **RH from all two-point window relations.**  It is enough to know that every
right-half ξ-zero, paired with its critical-line reflection, satisfies the two-point
window relation at every dyadic level.  The relation reads `2^k ∣ mult` by
`pair_window_relation_iff`; all levels force the positive finite local order to vanish,
which is impossible for an actual zero. -/
theorem rh_iff_pair_window_relation_all_levels :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        (∑ z ∈ ({ρ, lineReflect ρ} : Finset ℂ),
            (fun _ => (analyticOrderAt xi ρ).toNat) z ≡
          ∑ z ∈ ({ρ, lineReflect ρ} : Finset ℂ).filter (fun z => z.re = 1 / 2),
            (fun _ => (analyticOrderAt xi ρ).toNat) z [MOD 2 ^ (k + 1)]) := by
  constructor
  · intro hRH k ρ hρ hzero
    exact False.elim ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero)
  · intro hrel
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    let m : ℕ := (analyticOrderAt xi ρ).toNat
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ m := by
      intro k
      exact (pair_window_relation_iff (k := k) (mult := m) (ρ₀ := ρ) (mem_rightHalf.mp hρ)).mp
        (hrel k ρ hρ hzero)
    have hm0 : m = 0 := by
      by_contra hm0
      have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
      have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
      omega
    have hm : (m : ℕ∞) = analyticOrderAt xi ρ := ENat.coe_toNat (xi_orderAt_ne_top ρ)
    have hne : analyticOrderAt xi ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩
    rw [← hm, hm0] at hne
    exact hne rfl

end RHTower

namespace RHTower

open Complex Finset

/-- **RH from all finite reflection-closed window relations.**  The finite-window
congruence surface is complete: if every finite reflection-closed ξ-zero
configuration satisfies the window relation at every dyadic level, then there are no
right-half ξ-zeros.  The reverse direction is `xi_window_relation_of_ladder` applied
to the RH ladder. -/
theorem rh_iff_all_finite_window_relations_all_levels :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ (t : Finset ℂ) (m : ℂ → ℕ),
        (∀ z ∈ t, xi z = 0) →
        (∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z) →
        (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ z ∈ t, m z ≡
          ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)]) := by
  constructor
  · intro hRH k t m hzero hm hclosed
    exact xi_window_relation_of_ladder ((rh_iff_forall_ladder.mp hRH) k) hzero hm hclosed
  · intro hwin
    refine rh_iff_pair_window_relation_all_levels.mpr ?_
    intro k ρ hρ hzero
    let m : ℕ := (analyticOrderAt xi ρ).toNat
    have hmρ : (m : ℕ∞) = analyticOrderAt xi ρ := ENat.coe_toNat (xi_orderAt_ne_top ρ)
    have horder_reflect : analyticOrderAt xi (lineReflect ρ) = analyticOrderAt xi ρ := by
      simp only [lineReflect]
      rw [xi_orderAt_one_sub, xi_orderAt_conj]
    have hzero_reflect : xi (lineReflect ρ) = 0 := by
      simp only [lineReflect]
      rw [xi_one_sub, xi_conj, hzero, map_zero]
    have hzero_pair : ∀ z ∈ ({ρ, lineReflect ρ} : Finset ℂ), xi z = 0 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hzero
      · exact hzero_reflect
    have hm_pair : ∀ z ∈ ({ρ, lineReflect ρ} : Finset ℂ),
        ((fun _ => m) z : ℕ∞) = analyticOrderAt xi z := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmρ
      · rw [horder_reflect]
        exact hmρ
    have hclosed_pair : ∀ z ∈ ({ρ, lineReflect ρ} : Finset ℂ),
        lineReflect z ∈ ({ρ, lineReflect ρ} : Finset ℂ) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inr rfl
      · rw [lineReflect_involutive]
        exact Or.inl rfl
    exact hwin k ({ρ, lineReflect ρ} : Finset ℂ) (fun _ => m) hzero_pair hm_pair hclosed_pair

end RHTower
