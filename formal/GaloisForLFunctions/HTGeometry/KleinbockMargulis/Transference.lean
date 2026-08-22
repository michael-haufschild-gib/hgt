import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Setup

/-!
# Khintchine transference: simultaneous ⟹ dual approximation

Kleinbock--Margulis Theorem A concludes that almost every point of a nondegenerate manifold is
*not* very well multiplicatively approximable, a statement about the **dual** (linear-form) side.
The first-return exponent of a physical recurrence is a **simultaneous** statement: one time `q`
must bring every phase back at once.  The bridge is the easy half of Khintchine's transference
principle, which here is pure pigeonhole:

if `q y` is within `q^{-1/n-ε}` of `ℤⁿ`, the sublattice `{a ∈ ℤⁿ : q ∣ a·p}` has index at most
`q` in `ℤⁿ`, so it meets the cube of side `q^{1/n}`; a nonzero lattice point `a` there satisfies
`|a·y + b| = |a·δ|/q ≤ n q^{-1-ε}`, and `Π₊(a) ≤ q`, giving `|a·y+b| Π₊(a) ≤ n q^{-ε}`.

## Main results

* `VWA` — simultaneous very well approximable vectors `(1.2)`.
* `exists_small_dvd_dotProd` — the pigeonhole sublattice point.
* `vwma_of_vwa` — simultaneous very well approximable implies very well multiplicatively
  approximable, hence "not VWMA" gives the exact simultaneous Diophantine exponent `1/n`.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {n : ℕ}

/-- **(1.2).**  `y` is (simultaneously) very well approximable: for some `ε > 0` there are
infinitely many `q ≥ 1` admitting `p ∈ ℤⁿ` with `max_i |q yᵢ - pᵢ| ≤ q^{-1/n-ε}`. -/
def VWA (y : Fin n → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    {q : ℕ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
      |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)}.Infinite

/-- The integer pairing `a · p`. -/
def dotInt (a p : Fin n → ℤ) : ℤ := ∑ i, a i * p i

/-- **Pigeonhole in the index-`q` sublattice.**  If `(Q+1)^n > q ≥ 1` then some nonzero integer
vector with coordinates bounded by `Q` pairs to a multiple of `q` against `p`. -/
theorem exists_small_dvd_dotProd {q : ℕ} (hq : 1 ≤ q) (p : Fin n → ℤ) {Q : ℕ}
    (hQ : q < (Q + 1) ^ n) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ (∀ i, |a i| ≤ (Q : ℤ)) ∧ (q : ℤ) ∣ dotInt a p := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin n → Fin (Q + 1)) := by
    simp only [ZMod.card, Fintype.card_fun, Fintype.card_fin]
    exact hQ
  obtain ⟨c, c', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun c : Fin n → Fin (Q + 1) => ((∑ i, (c i : ℤ) * p i : ℤ) : ZMod q)) hcard
  refine ⟨fun i => (c i : ℤ) - (c' i : ℤ), ?_, ?_, ?_⟩
  · intro hzero
    apply hne
    funext i
    have := congrFun hzero i
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact Fin.ext (by exact_mod_cast this)
  · intro i
    show |(c i : ℤ) - (c' i : ℤ)| ≤ (Q : ℤ)
    have h1 : (c i : ℤ) ≤ (Q : ℤ) := by
      have := (c i).isLt
      omega
    have h2 : (c' i : ℤ) ≤ (Q : ℤ) := by
      have := (c' i).isLt
      omega
    have h3 : (0 : ℤ) ≤ (c i : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (c' i : ℤ) := Int.natCast_nonneg _
    rw [abs_le]
    omega
  · have hsub : dotInt (fun i => (c i : ℤ) - (c' i : ℤ)) p =
        (∑ i, (c i : ℤ) * p i) - ∑ i, (c' i : ℤ) * p i := by
      unfold dotInt
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsub, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, heq, sub_self]

/-- A real number outside `ℤ` stays a fixed positive distance from every integer. -/
theorem exists_dist_int_pos {t : ℝ} (ht : ∀ b : ℤ, t + (b : ℝ) ≠ 0) :
    ∃ dt : ℝ, 0 < dt ∧ ∀ b : ℤ, dt ≤ |t + (b : ℝ)| := by
  have hf0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hf1 : Int.fract t < 1 := Int.fract_lt_one t
  have hfne : Int.fract t ≠ 0 := by
    intro h
    refine ht (-⌊t⌋) ?_
    have hsplit := Int.floor_add_fract t
    rw [h, add_zero] at hsplit
    push_cast
    linarith
  have hfpos : 0 < Int.fract t := lt_of_le_of_ne hf0 (Ne.symm hfne)
  refine ⟨min (Int.fract t) (1 - Int.fract t), lt_min hfpos (by linarith), ?_⟩
  intro b
  have hfl : t = (⌊t⌋ : ℝ) + Int.fract t := (Int.floor_add_fract t).symm
  have hkey : t + (b : ℝ) = ((⌊t⌋ + b : ℤ) : ℝ) + Int.fract t := by
    push_cast
    linarith [Int.floor_add_fract t]
  rcases lt_trichotomy (⌊t⌋ + b) 0 with hlt | heq | hgt
  · have hlt' : (⌊t⌋ + b : ℤ) ≤ -1 := by omega
    have hle : ((⌊t⌋ + b : ℤ) : ℝ) ≤ -1 := by
      have hz := (Int.cast_le (R := ℝ)).mpr hlt'
      simpa using hz
    have : t + (b : ℝ) ≤ -1 + Int.fract t := by rw [hkey]; linarith
    rw [abs_of_nonpos (by linarith)]
    have := min_le_right (Int.fract t) (1 - Int.fract t)
    linarith
  · rw [hkey, heq]
    simp only [Int.cast_zero, zero_add, abs_of_nonneg hf0]
    exact min_le_left _ _
  · have hgt' : (1 : ℤ) ≤ ⌊t⌋ + b := by omega
    have hge : (1 : ℝ) ≤ ((⌊t⌋ + b : ℤ) : ℝ) := by
      have hz := (Int.cast_le (R := ℝ)).mpr hgt'
      simpa using hz
    have : (1 : ℝ) ≤ t + (b : ℝ) := by rw [hkey]; linarith
    rw [abs_of_nonneg (by linarith)]
    have h1 := min_le_left (Int.fract t) (1 - Int.fract t)
    linarith

/-- **The transference construction at one simultaneous approximation.**  From `q` with
`‖q y - p‖_∞ ≤ q^{-1/n-ε}` the index-`q` sublattice supplies a nonzero `a` with
`Π₊(a) ≤ q` and `|a·y + b| ≤ n q^{-1-ε}`. -/
theorem exists_transfer_point (hn : 0 < n) {y : Fin n → ℝ} {ε : ℝ} (_hε : 0 < ε)
    {q : ℕ} (hq2 : 2 ≤ q) {p : Fin n → ℤ}
    (hp : ∀ i, |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)) :
    ∃ (a : Fin n → ℤ) (b : ℤ), a ≠ 0 ∧ PiPlus a ≤ (q : ℝ) ∧
      |dotProd a y + (b : ℝ)| ≤ (n : ℝ) * (q : ℝ) ^ (-1 - ε) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set ν : ℝ := (q : ℝ) ^ ((n : ℝ))⁻¹ with hν
  have hν0 : 0 < ν := Real.rpow_pos_of_pos hq0 _
  have hνpow : ν ^ (n : ℕ) = (q : ℝ) := by
    rw [hν, ← Real.rpow_natCast ((q : ℝ) ^ ((n : ℝ))⁻¹) n, ← Real.rpow_mul hq0.le,
      inv_mul_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  set Q : ℕ := ⌊ν⌋₊ with hQdef
  have hQle : (Q : ℝ) ≤ ν := Nat.floor_le hν0.le
  have hQlt : ν < (Q : ℝ) + 1 := Nat.lt_floor_add_one ν
  have hν1 : 1 < ν := by
    rw [hν]
    exact (Real.one_lt_rpow_iff_of_pos hq0).mpr (Or.inl ⟨by linarith, inv_pos.mpr hnR⟩)
  have hQ1 : 1 ≤ Q := by
    refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
    rw [hQdef] at h
    have := Nat.floor_eq_zero.mp h
    linarith
  have hqQ : q < (Q + 1) ^ n := by
    have hR : (q : ℝ) < ((Q : ℝ) + 1) ^ (n : ℕ) := by
      calc (q : ℝ) = ν ^ (n : ℕ) := hνpow.symm
        _ < ((Q : ℝ) + 1) ^ (n : ℕ) := pow_lt_pow_left₀ hQlt hν0.le (by omega)
    have hcast : (((Q + 1) ^ n : ℕ) : ℝ) = ((Q : ℝ) + 1) ^ (n : ℕ) := by push_cast; ring
    have hlt : (q : ℝ) < (((Q + 1) ^ n : ℕ) : ℝ) := by rw [hcast]; exact hR
    exact_mod_cast hlt
  obtain ⟨a, ha0, haQ, hdvd⟩ := exists_small_dvd_dotProd hq1 p hqQ
  obtain ⟨c, hc⟩ := hdvd
  have habsR : ∀ i, |(a i : ℝ)| ≤ (Q : ℝ) := by
    intro i
    have h1 : |(a i : ℝ)| = ((|a i| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [h1]
    exact_mod_cast haQ i
  refine ⟨a, -c, ha0, ?_, ?_⟩
  · have hstep : PiPlus a ≤ (Q : ℝ) ^ (n : ℕ) := by
      unfold PiPlus
      calc ∏ i, max |(a i : ℝ)| 1 ≤ ∏ _i : Fin n, (Q : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_right _ _))
              (fun i _ => max_le (habsR i) (by exact_mod_cast hQ1))
        _ = (Q : ℝ) ^ (n : ℕ) := by simp
    refine hstep.trans ?_
    calc (Q : ℝ) ^ (n : ℕ) ≤ ν ^ (n : ℕ) := pow_le_pow_left₀ (by positivity) hQle n
      _ = (q : ℝ) := hνpow
  · have hdi : ∑ i, (a i : ℝ) * (p i : ℝ) = (q : ℝ) * (c : ℝ) := by
      have hcast : ((dotInt a p : ℤ) : ℝ) = ∑ i, (a i : ℝ) * (p i : ℝ) := by
        unfold dotInt
        push_cast
        ring
      rw [← hcast, hc]
      push_cast
      ring
    have hexp : ∑ i, (a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ))
        = (q : ℝ) * (∑ i, (a i : ℝ) * y i) - ∑ i, (a i : ℝ) * (p i : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsum : (q : ℝ) * (dotProd a y + ((-c : ℤ) : ℝ)) =
        ∑ i, (a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ)) := by
      rw [hexp, hdi]
      unfold dotProd
      push_cast
      ring
    have hbound : |∑ i, (a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ))| ≤
        (n : ℝ) * (q : ℝ) ^ (-ε) := by
      have hterm : ∀ i ∈ Finset.univ,
          |(a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ))| ≤ ν * (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε) := by
        intro i _
        rw [abs_mul]
        exact mul_le_mul ((habsR i).trans hQle) (hp i) (abs_nonneg _) hν0.le
      refine ((Finset.abs_sum_le_sum_abs
        (fun i => (a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ))) Finset.univ).trans
        (Finset.sum_le_sum hterm)).trans ?_
      have hcard : (∑ _i : Fin n, ν * (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)) =
          (n : ℝ) * (ν * (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)) := by
        simp
      rw [hcard]
      refine mul_le_mul_of_nonneg_left ?_ hnR.le
      rw [hν, ← Real.rpow_add hq0]
      exact le_of_eq (by congr 1; ring)
    have hfinal : (q : ℝ) * |dotProd a y + ((-c : ℤ) : ℝ)| ≤ (n : ℝ) * (q : ℝ) ^ (-ε) := by
      calc (q : ℝ) * |dotProd a y + ((-c : ℤ) : ℝ)|
          = |(q : ℝ) * (dotProd a y + ((-c : ℤ) : ℝ))| := by
            rw [abs_mul, abs_of_nonneg hq0.le]
        _ = |∑ i, (a i : ℝ) * ((q : ℝ) * y i - (p i : ℝ))| := by rw [hsum]
        _ ≤ (n : ℝ) * (q : ℝ) ^ (-ε) := hbound
    refine le_of_mul_le_mul_left ?_ hq0
    have hqe : (q : ℝ) * ((n : ℝ) * (q : ℝ) ^ (-1 - ε)) = (n : ℝ) * (q : ℝ) ^ (-ε) := by
      have hstep : (q : ℝ) * (q : ℝ) ^ (-1 - ε) = (q : ℝ) ^ (-ε) := by
        nth_rewrite 1 [← Real.rpow_one (q : ℝ)]
        rw [← Real.rpow_add hq0]
        congr 1
        ring
      rw [← mul_assoc, mul_comm (q : ℝ) (n : ℝ), mul_assoc, hstep]
    rw [hqe]
    exact hfinal

/-- **Khintchine transference (the half needed here).**  A simultaneously very well approximable
vector is very well multiplicatively approximable.  Contrapositively, `¬ VWMA y` gives the exact
simultaneous Diophantine exponent `1/n`. -/
theorem vwma_of_vwa (hn : 0 < n) {y : Fin n → ℝ} (h : VWA y) : VWMA y := by
  classical
  obtain ⟨ε, hε, hinf⟩ := h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases hdeg : ∃ a : Fin n → ℤ, a ≠ 0 ∧ ∃ b : ℤ, dotProd a y + (b : ℝ) = 0
  · obtain ⟨a, ha0, b, hab⟩ := hdeg
    obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      refine ha0 (funext fun i => ?_)
      by_contra hi
      exact hcon ⟨i, hi⟩
    refine ⟨1, one_pos, ?_⟩
    refine Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (fun i => ((k : ℤ) + 1) * a i)) ?_ ?_
    · intro k k' hkk'
      have hval := congrFun hkk' i₀
      simp only at hval
      have hk : ((k : ℤ) + 1) = ((k' : ℤ) + 1) := mul_right_cancel₀ hi₀ hval
      have hk' : (k : ℤ) = (k' : ℤ) := by omega
      exact_mod_cast hk' 
    · intro k
      refine ⟨((k : ℤ) + 1) * b, ?_⟩
      have hscale : dotProd (fun i => ((k : ℤ) + 1) * a i) y
          = (((k : ℤ) + 1 : ℤ) : ℝ) * dotProd a y := by
        unfold dotProd
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by push_cast; ring
      have hzero : dotProd (fun i => ((k : ℤ) + 1) * a i) y +
          ((((k : ℤ) + 1) * b : ℤ) : ℝ) = 0 := by
        rw [hscale]
        push_cast
        linear_combination ((k : ℝ) + 1) * hab
      rw [hzero, abs_zero, zero_mul]
      exact Real.rpow_nonneg (le_trans zero_le_one (one_le_PiPlus _)) _
  · have hnd : ∀ a : Fin n → ℤ, a ≠ 0 → ∀ b : ℤ, dotProd a y + (b : ℝ) ≠ 0 := by
      intro a ha b hab
      exact hdeg ⟨a, ha, b, hab⟩
    refine ⟨ε / 2, by positivity, ?_⟩
    -- the exponent threshold making the multiplicative inequality hold
    have hqn_of : ∀ q : ℕ, ⌈(n : ℝ) ^ (2 / ε)⌉₊ ≤ q → (n : ℝ) ≤ (q : ℝ) ^ (ε / 2) := by
      intro q hq
      have h1 : (n : ℝ) ^ (2 / ε) ≤ (q : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
      have h2 : ((n : ℝ) ^ (2 / ε)) ^ (ε / 2) ≤ (q : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnR.le _) h1 (by positivity)
      rwa [← Real.rpow_mul hnR.le, show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one] at h2
    -- one transference point for every large enough simultaneous approximation
    have hmem : ∀ q : ℕ, 2 ≤ q → (n : ℝ) ≤ (q : ℝ) ^ (ε / 2) →
        ∀ p : Fin n → ℤ,
        (∀ i, |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)) →
        ∃ a : Fin n → ℤ, a ≠ 0 ∧ (∃ b : ℤ,
            |dotProd a y + (b : ℝ)| * PiPlus a ≤ PiPlus a ^ (-(ε / 2)) ∧
            |dotProd a y + (b : ℝ)| ≤ (n : ℝ) * (q : ℝ) ^ (-1 - ε)) := by
      intro q hq2 hqn p hp
      obtain ⟨a, b, ha0, hPi, hsmall⟩ := exists_transfer_point hn hε hq2 hp
      have hq1 : 1 ≤ q := by omega
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
      have hPi1 : (1 : ℝ) ≤ PiPlus a := one_le_PiPlus a
      refine ⟨a, ha0, b, ?_, hsmall⟩
      have hrhs : (q : ℝ) ^ (-(ε / 2)) ≤ PiPlus a ^ (-(ε / 2)) := by
        rw [Real.rpow_neg hq0.le, Real.rpow_neg (by linarith : (0 : ℝ) ≤ PiPlus a)]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_le_rpow (by linarith) hPi (by positivity))
      calc |dotProd a y + (b : ℝ)| * PiPlus a
          ≤ ((n : ℝ) * (q : ℝ) ^ (-1 - ε)) * (q : ℝ) :=
            mul_le_mul hsmall hPi (le_trans zero_le_one hPi1) (by positivity)
        _ = (n : ℝ) * (q : ℝ) ^ (-ε) := by
            have hstep : (q : ℝ) ^ (-1 - ε) * (q : ℝ) = (q : ℝ) ^ (-ε) := by
              nth_rewrite 2 [← Real.rpow_one (q : ℝ)]
              rw [← Real.rpow_add hq0]
              congr 1
              ring
            rw [mul_assoc, hstep]
        _ ≤ (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right hqn (Real.rpow_nonneg hq0.le _)
        _ = (q : ℝ) ^ (-(ε / 2)) := by
            rw [← Real.rpow_add hq0]
            congr 1
            ring
        _ ≤ PiPlus a ^ (-(ε / 2)) := hrhs
    -- suppose the multiplicative approximation set were finite
    intro hfin
    have hda : ∀ a : Fin n → ℤ, ∃ da : ℝ, 0 < da ∧
        (a ≠ 0 → ∀ b : ℤ, da ≤ |dotProd a y + (b : ℝ)|) := by
      intro a
      by_cases ha : a = 0
      · exact ⟨1, one_pos, fun h => absurd ha h⟩
      · obtain ⟨da, hda0, hdab⟩ := exists_dist_int_pos (hnd a ha)
        exact ⟨da, hda0, fun _ => hdab⟩
    choose dA hdA0 hdAb using hda
    set TF : Finset (Fin n → ℤ) := hfin.toFinset.erase 0 with hTF
    obtain ⟨q₀, hq₀S, hq₀gt⟩ := hinf.exists_gt (max 2 ⌈(n : ℝ) ^ (2 / ε)⌉₊)
    obtain ⟨hq₀1, p₀, hp₀⟩ := hq₀S
    obtain ⟨a₀, ha₀0, b₀, ha₀mem, -⟩ :=
      hmem q₀ (by omega) (hqn_of q₀ (by omega)) p₀ hp₀
    have hTFne : TF.Nonempty := by
      refine ⟨a₀, Finset.mem_erase.mpr ⟨ha₀0, ?_⟩⟩
      exact hfin.mem_toFinset.mpr ⟨b₀, ha₀mem⟩
    set dmin : ℝ := TF.inf' hTFne dA with hdmin
    have hdmin0 : 0 < dmin := by
      rw [hdmin, Finset.lt_inf'_iff]
      exact fun a _ => hdA0 a
    obtain ⟨q, hqS, hqgt⟩ := hinf.exists_gt
      (max (max 2 ⌈(n : ℝ) ^ (2 / ε)⌉₊) ⌈(n : ℝ) / dmin⌉₊)
    obtain ⟨hq1, p, hp⟩ := hqS
    have hq2 : 2 ≤ q := by omega
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    obtain ⟨a, ha0, b, hamem, hsmall⟩ := hmem q hq2 (hqn_of q (by omega)) p hp
    have hmemTF : a ∈ TF := Finset.mem_erase.mpr ⟨ha0, hfin.mem_toFinset.mpr ⟨b, hamem⟩⟩
    have hdle : dmin ≤ dA a := Finset.inf'_le _ hmemTF
    have h1 : dA a ≤ |dotProd a y + (b : ℝ)| := hdAb a ha0 b
    have hqbig : (n : ℝ) / dmin < (q : ℝ) := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      have : ⌈(n : ℝ) / dmin⌉₊ < q := by omega
      exact_mod_cast this
    have h3 : (n : ℝ) * (q : ℝ) ^ (-1 - ε) < dmin := by
      have hstep : (q : ℝ) ^ (-1 - ε) ≤ (q : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1R (by linarith)
      have hinv : (q : ℝ) ^ (-1 : ℝ) = (q : ℝ)⁻¹ := by
        rw [Real.rpow_neg hq0.le, Real.rpow_one]
      have hlt : (n : ℝ) / (q : ℝ) < dmin := by
        rw [div_lt_iff₀ hq0]
        rw [div_lt_iff₀ hdmin0] at hqbig
        linarith
      calc (n : ℝ) * (q : ℝ) ^ (-1 - ε) ≤ (n : ℝ) * (q : ℝ)⁻¹ := by
            rw [← hinv]
            exact mul_le_mul_of_nonneg_left hstep hnR.le
        _ = (n : ℝ) / (q : ℝ) := by rw [div_eq_mul_inv]
        _ < dmin := hlt
    linarith

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
