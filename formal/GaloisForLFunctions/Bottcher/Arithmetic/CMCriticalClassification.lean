import GaloisForLFunctions.Bottcher.Arithmetic.CMCriticalOrbits

/-!
# Finite unicritical orbits over CM fields in degree at least three

Cyclotomic rigidity reduces every finite orbit to a ratio of order two or
three. The remaining dynamics depends only on the degree modulo six.
-/

noncomputable section
namespace Bottcher.Arithmetic
open Set NumberField

private theorem criticalOrbit_finite_of_closed_finset {K : Type*} [Field K]
    (d : ℕ) (c : K) (s : Finset K) (h0 : 0 ∈ s)
    (hs : ∀ x ∈ s, x ^ (d + 2) + c ∈ s) :
    (range (criticalOrbit d c)).Finite := by
  have hm : ∀ n, criticalOrbit d c n ∈ s := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [criticalOrbit_succ]; exact hs _ ih
  exact s.finite_toSet.subset (by rintro _ ⟨n, rfl⟩; exact hm n)

/-- The second critical iterate vanishes exactly at zero and the period-two parameter equation. -/
theorem criticalOrbit_second_zero_iff {K : Type*} [Field K] (d : ℕ) (c : K) :
    criticalOrbit d c 2 = 0 ↔ c = 0 ∨ c ^ (d + 1) = -1 := by
  have he : criticalOrbit d c 2 = c * (c ^ (d + 1) + 1) := by
    rw [show 2 = 1 + 1 by rfl, criticalOrbit_succ, criticalOrbit_one]
    rw [show d + 2 = d + 1 + 1 by omega, pow_succ]
    ring
  rw [he, mul_eq_zero, add_eq_zero_iff_eq_neg]

private theorem finite_criticalOrbit_zero {K : Type*} [Field K] (d : ℕ) :
    (range (criticalOrbit d (0 : K))).Finite := by
  classical
  apply criticalOrbit_finite_of_closed_finset d 0 {0} (by simp)
  intro x hx
  have hx0 : x = 0 := Finset.mem_singleton.mp hx
  simp only [hx0, zero_pow (by omega : d + 2 ≠ 0), zero_add, Finset.mem_singleton]

private theorem finite_criticalOrbit_order_two {K : Type*} [Field K]
    (d : ℕ) (c : K) (hc : c ^ (d + 1) = -1) :
    (range (criticalOrbit d c)).Finite := by
  classical
  have hcp : c ^ (d + 2) + c = 0 := by
    rw [show d + 2 = d + 1 + 1 by omega, pow_succ, hc]
    ring
  apply criticalOrbit_finite_of_closed_finset d c {0, c} (by simp)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · right
    rw [zero_pow (by omega : d + 2 ≠ 0), zero_add]
  · exact Or.inl hcp

private theorem normalized_critical_step {K : Type*} [Field K]
    (d : ℕ) (c u : K) :
    (c * u) ^ (d + 3) + c = c * (1 + c ^ (d + 2) * u ^ (d + 3)) := by
  rw [mul_pow, show d + 3 = d + 2 + 1 by omega, pow_succ c]
  ring

private theorem cube_root_relations {K : Type*} [Field K] (t : K)
    (ht : t ^ 2 + t + 1 = 0) :
    t ^ 3 = 1 ∧ (-t ^ 2) ^ 2 = t ∧ (-t ^ 2) ^ 3 = -1 ∧
      (-t ^ 2) ^ 4 = t ^ 2 ∧ (-t ^ 2) ^ 5 = -t ∧ (-t ^ 2) ^ 6 = 1 := by
  have h3 : t ^ 3 = 1 := by linear_combination (t - 1) * ht
  have h2 : (-t ^ 2) ^ 2 = t := by
    calc
      (-t ^ 2) ^ 2 = t ^ 3 * t := by ring
      _ = t := by rw [h3, one_mul]
  have hs3 : (-t ^ 2) ^ 3 = -1 := by
    calc
      (-t ^ 2) ^ 3 = -(t ^ 3) ^ 2 := by ring
      _ = -1 := by rw [h3, one_pow]
  have h4 : (-t ^ 2) ^ 4 = t ^ 2 := by
    calc
      (-t ^ 2) ^ 4 = ((-t ^ 2) ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [h2]
  have h5 : (-t ^ 2) ^ 5 = -t := by
    calc
      (-t ^ 2) ^ 5 = (-t ^ 2) ^ 2 * (-t ^ 2) ^ 3 := by ring
      _ = -t := by rw [h2, hs3]; ring
  have h6 : (-t ^ 2) ^ 6 = 1 := by
    calc
      (-t ^ 2) ^ 6 = ((-t ^ 2) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hs3]; ring
  exact ⟨h3, h2, hs3, h4, h5, h6⟩

private theorem criticalOrbit_second_cube_root {K : Type*} [Field K]
    (d : ℕ) (c : K) (ht : (c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0) :
    criticalOrbit (d + 1) c 2 = c * (-(c ^ (d + 2)) ^ 2) := by
  rw [show 2 = 1 + 1 by rfl, criticalOrbit_succ, criticalOrbit_one]
  rw [show d + 1 + 2 = d + 2 + 1 by omega, pow_succ]
  linear_combination c * ht

private theorem criticalOrbit_third_cube_root {K : Type*} [Field K]
    (d : ℕ) (c : K) (ht : (c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0) :
    criticalOrbit (d + 1) c 3 =
      c * (1 + c ^ (d + 2) * (-(c ^ (d + 2)) ^ 2) ^ ((d + 3) % 6)) := by
  rw [show 3 = 2 + 1 by rfl, criticalOrbit_succ, criticalOrbit_second_cube_root d c ht]
  rw [show d + 1 + 2 = d + 3 by omega, normalized_critical_step]
  rw [pow_eq_pow_mod (d + 3) (cube_root_relations _ ht).2.2.2.2.2]

private theorem finite_criticalOrbit_third_closes {K : Type*} [Field K]
    (d : ℕ) (c : K)
    (h : criticalOrbit d c 3 = 0 ∨ criticalOrbit d c 3 = criticalOrbit d c 2) :
    (range (criticalOrbit d c)).Finite := by
  classical
  apply criticalOrbit_finite_of_closed_finset d c {0, c, criticalOrbit d c 2} (by simp)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl
  · exact Or.inr (Or.inl (by rw [zero_pow (by omega : d + 2 ≠ 0), zero_add]))
  · right; right
    rw [show 2 = 1 + 1 by rfl, criticalOrbit_succ, criticalOrbit_one]
  · rw [← criticalOrbit_succ]
    exact h.imp_right Or.inr

private theorem finite_criticalOrbit_cube_root {K : Type*} [Field K]
    (d : ℕ) (c : K) (ht : (c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0)
    (hr : (d + 3) % 6 = 0 ∨ (d + 3) % 6 = 1) :
    (range (criticalOrbit (d + 1) c)).Finite := by
  apply finite_criticalOrbit_third_closes
  rcases hr with hr | hr
  · right
    rw [criticalOrbit_third_cube_root d c ht, hr, pow_zero, mul_one,
      criticalOrbit_second_cube_root d c ht]
    linear_combination c * ht
  · left
    rw [criticalOrbit_third_cube_root d c ht, hr, pow_one]
    calc
      c * (1 + c ^ (d + 2) * (-(c ^ (d + 2)) ^ 2)) =
          c * (1 - (c ^ (d + 2)) ^ 3) := by ring
      _ = 0 := by rw [(cube_root_relations _ ht).1, sub_self, mul_zero]

private theorem two_mul_not_cyclotomic {K : Type*} [Field K] [NumberField K]
    (c : K) (hc : IsOfFinOrder c) : ¬ (2 * c = 0 ∨ IsOfFinOrder (2 * c)) := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  have hnorm : ‖φ c‖ = 1 := (φ.toMonoidHom.isOfFinOrder hc).norm_eq_one
  have htwo : ‖φ (2 * c)‖ = 2 := by rw [map_mul, map_ofNat, norm_mul, hnorm]; norm_num
  rintro (hz | hu)
  · rw [hz, map_zero, norm_zero] at htwo
    norm_num at htwo
  · have hu' : ‖φ (2 * c)‖ = 1 := (φ.toMonoidHom.isOfFinOrder hu).norm_eq_one
    linarith only [htwo, hu']

private theorem cube_root_difference_not_cyclotomic {K : Type*} [Field K] [NumberField K]
    (c t : K) (hc : IsOfFinOrder c) (htor : IsOfFinOrder t)
    (ht : t ^ 2 + t + 1 = 0) :
    ¬ (c * (1 - t) = 0 ∨ IsOfFinOrder (c * (1 - t))) := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  have hc1 : ‖φ c‖ = 1 := (φ.toMonoidHom.isOfFinOrder hc).norm_eq_one
  have ht1 : ‖φ t‖ = 1 := (φ.toMonoidHom.isOfFinOrder htor).norm_eq_one
  have ht' : (φ t) ^ 2 + φ t + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ ht
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hc1
    norm_num at hc1
  rintro (hz | hu)
  · have ht0 : t = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc0) |>.symm
    rw [ht0] at ht
    norm_num at ht
  · have hu1 : ‖φ (c * (1 - t))‖ = 1 := (φ.toMonoidHom.isOfFinOrder hu).norm_eq_one
    rw [map_mul, map_sub, map_one, norm_mul, hc1, one_mul] at hu1
    have hbad := (complex_unit_sum_iff (-φ t)).mp
      ⟨by rw [norm_neg, ht1], by simpa only [sub_eq_add_neg] using hu1⟩
    have hz : φ t = 0 := by linear_combination (1 / 2 : ℂ) * ht' - (1 / 2 : ℂ) * hbad
    rw [hz, norm_zero] at ht1
    norm_num at ht1

private theorem cube_root_finite_degree_residue
    {K : Type*} [Field K] [NumberField K] [IsCMField K] (d : ℕ) (c : K)
    (hf : (range (criticalOrbit (d + 1) c)).Finite)
    (hc : IsOfFinOrder c) (ht : (c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0) :
    (d + 3) % 6 = 0 ∨ (d + 3) % 6 = 1 := by
  let t := c ^ (d + 2)
  have hiter := (criticalOrbit_infinite_or_all_cyclotomic d c).resolve_left hf.not_infinite
  have hrel := cube_root_relations t ht
  have h3 := criticalOrbit_third_cube_root d c ht
  change criticalOrbit (d + 1) c 3 = c * (1 + t * (-t ^ 2) ^ ((d + 3) % 6)) at h3
  have htor : IsOfFinOrder t := hc.pow
  have hlt : (d + 3) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : (d + 3) % 6
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    have hz3 : criticalOrbit (d + 1) c 3 = -c * t := by
      rw [hrel.2.1] at h3
      calc
        _ = c * (1 + t * t) := h3
        _ = -c * t := by linear_combination c * ht
    have hu6 : (-t) ^ 6 = 1 := by
      calc
        (-t) ^ 6 = (t ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hrel.1, one_pow]
    have hz4 : criticalOrbit (d + 1) c 4 = 2 * c := by
      rw [show 4 = 3 + 1 by rfl, criticalOrbit_succ, hz3,
        show -c * t = c * (-t) by ring, show d + 1 + 2 = d + 3 by omega,
        normalized_critical_step, pow_eq_pow_mod (d + 3) hu6, hr]
      change c * (1 + t * (-t) ^ 2) = 2 * c
      calc
        _ = c * (1 + t ^ 3) := by ring
        _ = 2 * c := by rw [hrel.1]; ring
    exact two_mul_not_cyclotomic c hc (hz4 ▸ hiter 4)
  · exfalso
    rw [hrel.2.2.1] at h3
    have hz3 : criticalOrbit (d + 1) c 3 = c * (1 - t) := by simpa only [mul_neg_one, sub_eq_add_neg] using h3
    exact cube_root_difference_not_cyclotomic c t hc htor ht (hz3 ▸ hiter 3)
  · exfalso
    rw [hrel.2.2.2.1] at h3
    have hz3 : criticalOrbit (d + 1) c 3 = 2 * c := by
      calc
        _ = c * (1 + t * t ^ 2) := h3
        _ = c * (1 + t ^ 3) := by ring
        _ = 2 * c := by rw [hrel.1]; ring
    exact two_mul_not_cyclotomic c hc (hz3 ▸ hiter 3)
  · exfalso
    rw [hrel.2.2.2.2.1] at h3
    have hz3 : criticalOrbit (d + 1) c 3 = c * (1 - t ^ 2) := by
      calc
        _ = c * (1 + t * (-t)) := h3
        _ = c * (1 - t ^ 2) := by ring
    have ht2 : (t ^ 2) ^ 2 + t ^ 2 + 1 = 0 := by
      calc
        _ = t * t ^ 3 + t ^ 2 + 1 := by ring
        _ = 0 := by rw [hrel.1, mul_one]; linear_combination ht
    exact cube_root_difference_not_cyclotomic c (t ^ 2) hc htor.pow ht2 (hz3 ▸ hiter 3)

/-- Complete finite-critical-orbit classification over CM fields for every degree at least three. -/
theorem finite_criticalOrbit_cm_iff
    {K : Type*} [Field K] [NumberField K] [IsCMField K] (d : ℕ) (c : K) :
    (range (criticalOrbit (d + 1) c)).Finite ↔
      c = 0 ∨ c ^ (d + 2) = -1 ∨
        ((c ^ (d + 2)) ^ 2 + c ^ (d + 2) + 1 = 0 ∧
          ((d + 3) % 6 = 0 ∨ (d + 3) % 6 = 1)) := by
  constructor
  · intro hf
    have h := (criticalOrbit_infinite_or_parameter_equations d c).resolve_left hf.not_infinite
    rcases h with hz | ht | ht
    · exact Or.inl hz
    · exact Or.inr (Or.inl ht)
    · right; right
      refine ⟨ht, ?_⟩
      have hc0 : c ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by omega : d + 2 ≠ 0)] at ht
        norm_num at ht
      have hc := ((criticalOrbit_infinite_or_zero_or_finiteOrder d c).resolve_left
        hf.not_infinite).resolve_left hc0
      exact cube_root_finite_degree_residue d c hf hc ht
  · rintro (rfl | ht | ⟨ht, hr⟩)
    · exact finite_criticalOrbit_zero (d + 1)
    · exact finite_criticalOrbit_order_two (d + 1) c ht
    · exact finite_criticalOrbit_cube_root d c ht hr

end Bottcher.Arithmetic

#print axioms Bottcher.Arithmetic.criticalOrbit_second_zero_iff
#print axioms Bottcher.Arithmetic.finite_criticalOrbit_cm_iff
