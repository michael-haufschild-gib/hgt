import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLettersOfACompensatedStencilAreSmooth
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure

/-!
# The compensated producer

The compensated letters are smooth, so a far letter has to detect only prime powers `Q = q^e` with `q ≤ 2y + 2`. Take `G = 2^g`, which sees the powers of two for free, and
for each `Q` a far letter `G_Q Q`, where `G_Q ∣ G` is the largest power of two with `G_Q Q ≤ 3 G`. Its weight `D_Q/G_Q` pays for the failure of `Q` as long as the near
point `s = r mod G` lies below `G_Q`. Past that, `2 Q s/(3 G) ≥ 1`, so the linear term pays. One more letter `3 G`, of weight `Z`, gives the linear term.

Every far letter has the same size `≍ G`, and the cost of all of them is the weighted defect over `G`. So a level `Y` needs only `G ≍ y³/Y`, up to logarithms: an alphabet `y³/Y`
in place of `y⁴/Y`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

variable {y : ℕ} {d : ℕ → ℕ}

/-- The modulus of the far letter at `Q`. -/
def farModulus (g K Q : ℕ) : ℕ := 2 ^ min g (Nat.log 2 (K / Q))

theorem farModulus_pos (g K Q : ℕ) : 0 < farModulus g K Q := pow_pos (by norm_num) _

theorem farModulus_dvd (g K Q : ℕ) : farModulus g K Q ∣ 2 ^ g := pow_dvd_pow 2 (min_le_left _ _)

theorem farModulus_mul_le {g K Q : ℕ} (hQ : 0 < Q) (hQK : Q ≤ K) : farModulus g K Q * Q ≤ K := by
  have hne : K / Q ≠ 0 := (Nat.div_pos hQK hQ).ne'
  have h1 : farModulus g K Q ≤ K / Q :=
    (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (Nat.pow_log_le_self 2 hne)
  calc farModulus g K Q * Q ≤ K / Q * Q := Nat.mul_le_mul_right Q h1
    _ ≤ K := Nat.div_mul_le_self K Q

/-- Below the far modulus the far letter pays. At or above it the linear term does: `K < 2 Q s`. -/
theorem lt_of_farModulus_le {g K Q s : ℕ} (hQ : 0 < Q) (hsG : s < 2 ^ g) (h : farModulus g K Q ≤ s) :
    K < 2 * Q * s := by
  have hmin : Nat.log 2 (K / Q) < g := by
    by_contra hge
    push Not at hge
    rw [farModulus, min_eq_left hge] at h
    omega
  rw [farModulus, min_eq_right hmin.le] at h
  have h1 : K / Q < 2 ^ (Nat.log 2 (K / Q)).succ := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h1
  have h2 : K / Q + 1 ≤ 2 * s := by omega
  calc K < Q * (K / Q + 1) := Nat.lt_mul_div_succ K hQ
    _ ≤ Q * (2 * s) := Nat.mul_le_mul_left Q h2
    _ = 2 * Q * s := by ring

/-- `1/G_Q ≤ 1/G + 2 Q/K`. -/
theorem inv_farModulus_le {g K Q : ℕ} (hQ : 0 < Q) (hK : 0 < K) :
    1 / (farModulus g K Q : ℝ) ≤ 1 / ((2 ^ g : ℕ) : ℝ) + 2 * (Q : ℝ) / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h0 : (0 : ℝ) ≤ 1 / ((2 ^ g : ℕ) : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ 2 * (Q : ℝ) / K := by positivity
  rcases le_or_gt g (Nat.log 2 (K / Q)) with h | h
  · rw [farModulus, min_eq_left h]
    linarith
  · rw [farModulus, min_eq_right h.le]
    have h2 : K / Q < 2 ^ (Nat.log 2 (K / Q)).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : K < Q * (K / Q + 1) := Nat.lt_mul_div_succ K hQ
    have h4 : K / Q + 1 ≤ 2 * 2 ^ Nat.log 2 (K / Q) := by
      rw [pow_succ] at h2
      omega
    have h5 : K ≤ 2 * Q * 2 ^ Nat.log 2 (K / Q) := by
      calc K ≤ Q * (K / Q + 1) := h3.le
        _ ≤ Q * (2 * 2 ^ Nat.log 2 (K / Q)) := Nat.mul_le_mul_left Q h4
        _ = _ := by ring
    have h6 : (K : ℝ) ≤ 2 * (Q : ℝ) * ((2 ^ Nat.log 2 (K / Q) : ℕ) : ℝ) := by exact_mod_cast h5
    have hpos : (0 : ℝ) < ((2 ^ Nat.log 2 (K / Q) : ℕ) : ℝ) := by positivity
    have h7 : 1 / ((2 ^ Nat.log 2 (K / Q) : ℕ) : ℝ) ≤ 2 * (Q : ℝ) / K := by
      rw [div_le_div_iff₀ hpos hKR]
      linarith
    linarith

/-- The far letters. -/
def compFar (y : ℕ) (d : ℕ → ℕ) (g K r : ℕ) : ℝ :=
  ∑ x ∈ compPairs y, ((compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g K (x.1 ^ x.2)) *
    ((r % (farModulus g K (x.1 ^ x.2) * x.1 ^ x.2) : ℕ) : ℝ)

theorem compPairs_prime {x : ℕ × ℕ} (hx : x ∈ compPairs y) : x.1.Prime := by
  simp only [compPairs, mem_filter, mem_product] at hx
  exact hx.1.1.2

theorem compPairs_le {x : ℕ × ℕ} (hx : x ∈ compPairs y) : x.1 ^ x.2 ≤ y * y := by
  simp only [compPairs, mem_filter] at hx
  exact hx.2

/-- **The far letters pay the failures.** -/
theorem sum_defects_le_compFar {g K r : ℕ} (hK : 0 < K) :
    ∑ x ∈ compPairs y, (if x.1 ^ x.2 ∣ r - r % 2 ^ g then 0 else (compDefect y d (x.1 ^ x.2) : ℝ)) ≤
      compFar y d g K r + (2 * ((r % 2 ^ g : ℕ) : ℝ) / K) * compWeighted y d := by
  obtain ⟨s, hs⟩ : ∃ s, s = r % 2 ^ g := ⟨_, rfl⟩
  rw [← hs]
  have hsG : s < 2 ^ g := hs ▸ Nat.mod_lt r (pow_pos (by norm_num) g)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rw [compFar, compWeighted, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x hx => ?_
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = x.1 ^ x.2 := ⟨_, rfl⟩
  rw [← hQdef]
  have hQ : 0 < Q := hQdef ▸ pow_pos (compPairs_prime hx).pos _
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (compDefect y d Q : ℝ) := ⟨_, rfl⟩
  rw [← hD]
  have hD0 : 0 ≤ D := hD ▸ Nat.cast_nonneg _
  obtain ⟨Gx, hGx⟩ : ∃ Gx, Gx = farModulus g K Q := ⟨_, rfl⟩
  rw [← hGx]
  have hGx0 : 0 < Gx := hGx ▸ farModulus_pos g K Q
  have hGxR : (0 : ℝ) < Gx := by exact_mod_cast hGx0
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmodnn : (0 : ℝ) ≤ ((r % (Gx * Q) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT1 : 0 ≤ D / (Gx : ℝ) * ((r % (Gx * Q) : ℕ) : ℝ) := by positivity
  have hT2 : 0 ≤ 2 * (s : ℝ) / K * ((Q : ℝ) * D) := by positivity
  by_cases hdiv : Q ∣ r - s
  · rw [if_pos hdiv]
    linarith
  rw [if_neg hdiv]
  by_cases hsGx : s < Gx
  · -- The far letter pays.
    have hmod : r % Gx = s := by
      have hdvd : Gx ∣ 2 ^ g := hGx ▸ farModulus_dvd g K Q
      rw [← Nat.mod_mod_of_dvd r hdvd, ← hs, Nat.mod_eq_of_lt hsGx]
    have hge := mod_mul_ge (r := r) hGx0 hQ
    rw [hmod, if_neg hdiv] at hge
    have hle : (Gx : ℝ) ≤ ((r % (Gx * Q) : ℕ) : ℝ) := by linarith
    have hpay : D ≤ D / (Gx : ℝ) * ((r % (Gx * Q) : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hGxR]
      exact mul_le_mul_of_nonneg_left hle hD0
    linarith
  · -- The linear term pays.
    push Not at hsGx
    have hlt := lt_of_farModulus_le hQ hsG (hGx ▸ hsGx : farModulus g K Q ≤ s)
    have hltR : (K : ℝ) ≤ 2 * (Q : ℝ) * s := by exact_mod_cast hlt.le
    have hpay : D ≤ 2 * (s : ℝ) / K * ((Q : ℝ) * D) := by
      have e : 2 * (s : ℝ) / K * ((Q : ℝ) * D) = (2 * (Q : ℝ) * s) / K * D := by ring
      rw [e]
      have h1 : 1 ≤ (2 * (Q : ℝ) * s) / K := (one_le_div hKR).mpr hltR
      nlinarith
    linarith

/-- **The total lower bound.** With `s = r mod 2^g`, near part, linear letter and far letters together are at least `N(s) + Z s` minus the linear term. -/
theorem compTotal_ge (hc : IsCompensation y d) {g K r : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (hK : 0 < K) (hTG : y * y ≤ 2 ^ g) :
    compNear y d (r % 2 ^ g) + Z * ((r % 2 ^ g : ℕ) : ℝ) -
        (2 * ((r % 2 ^ g : ℕ) : ℝ) / K) * compWeighted y d ≤
      compNear y d r + Z * ((r % (2 ^ g * 3) : ℕ) : ℝ) + compFar y d g K r := by
  have hsr : r % 2 ^ g ≤ r := Nat.mod_le _ _
  have hmod : 2 ^ g ∣ r - r % 2 ^ g := Nat.dvd_sub_mod r
  have h1 := abs_compNear_sub_le_defects hc hTG hsr hmod
  have h2 := sum_defects_le_compFar (y := y) (d := d) (g := g) (K := K) (r := r) hK
  have h3 := (abs_le.mp h1).1
  have h4 := mod_mul_ge (G := 2 ^ g) (P := 3) (r := r) (pow_pos (by norm_num) g) (by norm_num)
  have h5 : ((r % 2 ^ g : ℕ) : ℝ) ≤ ((r % (2 ^ g * 3) : ℕ) : ℝ) := by
    have h6 : (0 : ℝ) ≤ if 3 ∣ r - r % 2 ^ g then 0 else ((2 ^ g : ℕ) : ℝ) := by
      split_ifs
      · exact le_rfl
      · positivity
    linarith
  have h7 := mul_le_mul_of_nonneg_left h5 hZ
  linarith

/-- **A family of letters clears to an integer stencil.** -/
theorem exists_stencil_of_family {ι : Type*} [DecidableEq ι] (I : Finset ι) (ℓ : ι → ℕ) (w : ι → ℚ)
    (hℓ : ∀ i ∈ I, 2 ≤ ℓ i) :
    ∃ (c : ℕ →₀ ℤ) (D : ℕ), 0 < D ∧ c 0 = 0 ∧ IsBalanced c ∧
      (∀ r : ℕ, (stepWeight c r : ℝ) = (D : ℝ) * ∑ i ∈ I, (w i : ℝ) * ((r % ℓ i : ℕ) : ℝ)) ∧
      stencilSlope c = (D : ℝ) * ∑ i ∈ I, (w i : ℝ) * Real.log (ℓ i) ∧
      c.support ⊆ insert 1 (I.image ℓ) := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℚ, q = fun k => ∑ i ∈ I.filter (fun i => ℓ i = k), w i := ⟨_, rfl⟩
  have hJ2 : ∀ k ∈ I.image ℓ, 2 ≤ k := fun k hk => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    exact hℓ i hi
  have hkey : ∀ φ : ℕ → ℝ, ∑ k ∈ I.image ℓ, (q k : ℝ) * φ k = ∑ i ∈ I, (w i : ℝ) * φ (ℓ i) := by
    intro φ
    rw [← sum_fiberwise_of_maps_to (g := ℓ) (t := I.image ℓ) (fun i hi => mem_image_of_mem ℓ hi)]
    refine sum_congr rfl fun k _ => ?_
    rw [hq]
    simp only
    rw [Rat.cast_sum, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.mp hi).2]
  obtain ⟨c, D, hD, hc0, hbal, hstep, hslope, hsupp, -⟩ := exists_stencil_of_weights (J := I.image ℓ) q hJ2
  refine ⟨c, D, hD, hc0, hbal, fun r => ?_, ?_, hsupp⟩
  · rw [hstep r, hkey fun k => ((r % k : ℕ) : ℝ)]
  · rw [hslope, hkey fun k => Real.log k]

/-- The slope of the near part. -/
def compSlope (y : ℕ) (d : ℕ → ℕ) : ℝ :=
  ∑ k ∈ Icc 2 (y * y), (-(compCoeff y d k : ℝ) / k) * Real.log k

/-- **The compensated producer.** A linear weight `Z` covering the near error and the far linear term gives an integer producer on `[1, 2^g)`. -/
theorem exists_compensated_producer (hc : IsCompensation y d) (hy : 4 ≤ y) {g : ℕ} {Y : ℝ} {Z : ℚ}
    (hTG : y * y < 2 ^ g) (hZ0 : 0 ≤ (Z : ℝ))
    (hnear : ∀ s, 1 ≤ s → s < 2 ^ g → |compNear y d s - compCount y d s| ≤ (s : ℝ) * Y)
    (hZY : Y + 2 * compWeighted y d / ((2 ^ g * 3 : ℕ) : ℝ) ≤ (Z : ℝ)) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m (2 ^ g) ∧ AlphabetLE c (2 ^ g * 3) ∧
      stencilSlope c ≤ (m : ℝ) * (compSlope y d + (Z : ℝ) * Real.log ((2 ^ g * 3 : ℕ) : ℝ) +
        (∑ x ∈ compPairs y, (compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g (2 ^ g * 3) (x.1 ^ x.2)) *
          Real.log ((2 ^ g * 3 : ℕ) : ℝ)) := by
  classical
  obtain ⟨G, hGdef⟩ : ∃ G, G = 2 ^ g := ⟨_, rfl⟩
  rw [← hGdef] at hTG hnear hZY ⊢
  obtain ⟨K, hKdef⟩ : ∃ K, K = G * 3 := ⟨_, rfl⟩
  rw [← hKdef] at hZY ⊢
  have hG0 : 0 < G := by rw [hGdef]; positivity
  have hK0 : 0 < K := by rw [hKdef]; omega
  have hGK : G ≤ K := by rw [hKdef]; omega
  have hT3 : ∀ k ∈ Icc 2 (y * y), k ≠ G * 3 := by
    intro k hk h
    have := (mem_Icc.mp hk).2
    omega
  -- The index set of all the letters.
  obtain ⟨I, hI⟩ : ∃ I : Finset (ℕ ⊕ (ℕ × ℕ)), I = (insert (G * 3) (Icc 2 (y * y))).disjSum (compPairs y) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ ⊕ (ℕ × ℕ) → ℕ, ℓ = Sum.elim id
      (fun x => farModulus g K (x.1 ^ x.2) * x.1 ^ x.2) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ ⊕ (ℕ × ℕ) → ℚ, w = Sum.elim
      (fun k => if k ≤ y * y then -(compCoeff y d k : ℚ) / k else Z)
      (fun x => (compDefect y d (x.1 ^ x.2) : ℚ) / farModulus g K (x.1 ^ x.2)) := ⟨_, rfl⟩
  have hQ3 : ∀ x ∈ compPairs y, 3 ≤ x.1 ^ x.2 := by
    intro x hx
    simp only [compPairs, mem_filter, mem_product, mem_Icc] at hx
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h2, -⟩, -⟩ := hx
    calc 3 ≤ x.1 := h1
      _ = x.1 ^ 1 := (pow_one _).symm
      _ ≤ x.1 ^ x.2 := Nat.pow_le_pow_right (by omega) h2
  have hGbig : 2 ≤ G := by
    have : 16 ≤ y * y := by nlinarith
    omega
  have hℓ2 : ∀ i ∈ I, 2 ≤ ℓ i := by
    intro i hi
    rw [hI] at hi
    rw [hℓ]
    rcases i with k | x
    · have hk := mem_disjSum.mp hi
      simp only [Sum.inl.injEq, exists_eq_right, reduceCtorEq, and_false, exists_false, or_false] at hk
      simp only [Sum.elim_inl, id]
      rcases mem_insert.mp hk with h | h
      · omega
      · exact (mem_Icc.mp h).1
    · have hx := mem_disjSum.mp hi
      simp only [reduceCtorEq, and_false, exists_false, Sum.inr.injEq, exists_eq_right, false_or] at hx
      simp only [Sum.elim_inr]
      have h1 := hQ3 x hx
      have h2 := farModulus_pos g K (x.1 ^ x.2)
      nlinarith
  obtain ⟨c, D, hD, hc0, hbal, hstep, hslope, hsupp⟩ := exists_stencil_of_family I ℓ w hℓ2
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  -- The sum over the family.
  have hsplit : ∀ φ : ℕ → ℝ, ∑ i ∈ I, (w i : ℝ) * φ (ℓ i) =
      (Z : ℝ) * φ (G * 3) + ∑ k ∈ Icc 2 (y * y), (-(compCoeff y d k : ℝ) / k) * φ k +
        ∑ x ∈ compPairs y, ((compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g K (x.1 ^ x.2)) *
          φ (farModulus g K (x.1 ^ x.2) * x.1 ^ x.2) := by
    intro φ
    rw [hI, sum_disjSum, sum_insert (fun h => hT3 _ h rfl)]
    have hnot : ¬ G * 3 ≤ y * y := by omega
    congr 1
    congr 1
    · rw [hw, hℓ]
      simp only [Sum.elim_inl, id, if_neg hnot]
    · refine sum_congr rfl fun k hk => ?_
      rw [hw, hℓ]
      simp only [Sum.elim_inl, id, if_pos (mem_Icc.mp hk).2]
      push_cast
      rfl
    · refine sum_congr rfl fun x _ => ?_
      rw [hw, hℓ]
      simp only [Sum.elim_inr]
      push_cast
      rfl
  have hval : ∀ r, ∑ i ∈ I, (w i : ℝ) * ((r % ℓ i : ℕ) : ℝ) =
      compNear y d r + (Z : ℝ) * ((r % (G * 3) : ℕ) : ℝ) + compFar y d g K r := by
    intro r
    have h := hsplit fun k => ((r % k : ℕ) : ℝ)
    rw [h, compNear, compFar]
    ring
  -- Nonnegativity and the window.
  have hlow : ∀ r, 1 ≤ r % G → 1 ≤ compNear y d r + (Z : ℝ) * ((r % (G * 3) : ℕ) : ℝ) + compFar y d g K r := by
    intro r hs
    have h := compTotal_ge hc (r := r) (K := K) hZ0 hK0 (hGdef ▸ hTG.le)
    rw [← hGdef] at h
    have hsG : r % G < G := Nat.mod_lt _ hG0
    have hn := (abs_le.mp (hnear _ hs hsG)).1
    have hco := one_le_compCount hc (r % G)
    have hs0 : (0 : ℝ) ≤ ((r % G : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hZY hs0
    have e : (2 * ((r % G : ℕ) : ℝ) / K) * compWeighted y d =
        ((r % G : ℕ) : ℝ) * (2 * compWeighted y d / K) := by ring
    rw [e] at h
    nlinarith
  have hnn : ∀ r, 0 ≤ compNear y d r + (Z : ℝ) * ((r % (G * 3) : ℕ) : ℝ) + compFar y d g K r := by
    intro r
    by_cases hs : 1 ≤ r % G
    · exact zero_le_one.trans (hlow r hs)
    · have hs0 : r % G = 0 := by omega
      have h := compTotal_ge hc (r := r) (K := K) hZ0 hK0 (hGdef ▸ hTG.le)
      rw [← hGdef, hs0] at h
      have hN0 : compNear y d 0 = 0 := by
        simp [compNear]
      rw [hN0] at h
      simpa using h
  have hP : IsProducer c D G := by
    refine ⟨hc0, hbal, fun r => ?_, hD, hGbig, fun r hr => ?_⟩
    · have hR : (0 : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r, hval r]
        exact mul_nonneg hDR.le (hnn r)
      exact_mod_cast hR
    · obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
      have hR : ((D : ℤ) : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r, hval r]
        push_cast
        have h1 := hlow r (by rw [Nat.mod_eq_of_lt hr2]; exact hr1)
        calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hDR.le
      exact_mod_cast hR
  refine ⟨c, D, hP, fun k hk => ?_, ?_⟩
  · rcases mem_insert.mp (hsupp hk) with h | h
    · omega
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp h
      rw [hI] at hi
      rw [hℓ]
      rcases i with k' | x
      · have hk' := mem_disjSum.mp hi
        simp only [Sum.inl.injEq, exists_eq_right, reduceCtorEq, and_false, exists_false, or_false] at hk'
        simp only [Sum.elim_inl, id]
        rcases mem_insert.mp hk' with h' | h'
        · omega
        · have := (mem_Icc.mp h').2
          omega
      · have hx := mem_disjSum.mp hi
        simp only [reduceCtorEq, and_false, exists_false, Sum.inr.injEq, exists_eq_right, false_or] at hx
        simp only [Sum.elim_inr]
        refine farModulus_mul_le (pow_pos (compPairs_prime hx).pos _) ?_
        have := compPairs_le hx
        omega
  · -- The slope.
    rw [hslope, hsplit fun k => Real.log k]
    refine mul_le_mul_of_nonneg_left ?_ hDR.le
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK0
    have hlogK := Real.log_nonneg hKR
    have hfar : ∑ x ∈ compPairs y, ((compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g K (x.1 ^ x.2)) *
        Real.log ((farModulus g K (x.1 ^ x.2) * x.1 ^ x.2 : ℕ) : ℝ) ≤
        (∑ x ∈ compPairs y, (compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g K (x.1 ^ x.2)) * Real.log K := by
      rw [sum_mul]
      refine sum_le_sum fun x hx => ?_
      have hQ0 : 0 < x.1 ^ x.2 := pow_pos (compPairs_prime hx).pos _
      have hG0' := farModulus_pos g K (x.1 ^ x.2)
      have hle := farModulus_mul_le (g := g) hQ0 (by have := compPairs_le hx; omega : x.1 ^ x.2 ≤ K)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Real.log_le_log ?_ (by exact_mod_cast hle)
      exact_mod_cast Nat.mul_pos hG0' hQ0
    have hKeq : G * 3 = K := hKdef.symm
    rw [hKeq, compSlope]
    linarith

/-- The total weight of the far letters. -/
theorem sum_far_weight_le (hy : 4 ≤ y) {g : ℕ} (hTG : y * y < 2 ^ g) :
    ∑ x ∈ compPairs y, (compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g (2 ^ g * 3) (x.1 ^ x.2) ≤
      compWeighted y d / ((2 ^ g : ℕ) : ℝ) + 2 * compWeighted y d / ((2 ^ g * 3 : ℕ) : ℝ) := by
  have hK : 0 < 2 ^ g * 3 := by positivity
  have hKR : (0 : ℝ) < ((2 ^ g * 3 : ℕ) : ℝ) := by exact_mod_cast hK
  have hGR : (0 : ℝ) < ((2 ^ g : ℕ) : ℝ) := by positivity
  rw [compWeighted, sum_div, mul_sum, sum_div, ← sum_add_distrib]
  refine sum_le_sum fun x hx => ?_
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = x.1 ^ x.2 := ⟨_, rfl⟩
  rw [← hQdef]
  have hQ : 0 < Q := hQdef ▸ pow_pos (compPairs_prime hx).pos _
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hD0 : (0 : ℝ) ≤ (compDefect y d Q : ℝ) := Nat.cast_nonneg _
  have hinv := inv_farModulus_le (g := g) hQ hK
  calc (compDefect y d Q : ℝ) / farModulus g (2 ^ g * 3) Q
      = (compDefect y d Q : ℝ) * (1 / (farModulus g (2 ^ g * 3) Q : ℝ)) := by ring
    _ ≤ (compDefect y d Q : ℝ) * (1 / ((2 ^ g : ℕ) : ℝ) + 2 * (Q : ℝ) / ((2 ^ g * 3 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv hD0
    _ = (compDefect y d Q : ℝ) / ((2 ^ g : ℕ) : ℝ) +
          2 * ((Q : ℝ) * (compDefect y d Q : ℝ)) / ((2 ^ g * 3 : ℕ) : ℝ) := by ring
    _ ≤ _ := by
        have h1 : (compDefect y d Q : ℝ) ≤ (Q : ℝ) * (compDefect y d Q : ℝ) :=
          le_mul_of_one_le_left hD0 hQR
        have h2 : (compDefect y d Q : ℝ) / ((2 ^ g : ℕ) : ℝ) ≤
            (Q : ℝ) * (compDefect y d Q : ℝ) / ((2 ^ g : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right h1 hGR.le
        linarith

/-- The pronic weight on `r = j + 1`. -/
private def pronicStep (j : ℕ) : ℝ := 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))

private lemma pronicStep_nonneg (j : ℕ) : 0 ≤ pronicStep j := by
  rw [pronicStep]
  positivity

private lemma sum_range_pronicStep (n : ℕ) : ∑ j ∈ range n, pronicStep j = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pronicStep]
    push_cast
    field_simp
    ring

private lemma sum_Ico_pronicStep {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Ico a b, pronicStep j = 1 / ((a : ℝ) + 1) - 1 / ((b : ℝ) + 1) := by
  rw [sum_Ico_eq_sub _ h, sum_range_pronicStep, sum_range_pronicStep]
  ring

private lemma sum_ite_lt_le' {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n G : ℕ) :
    ∑ j ∈ range n, (if j + 1 < G then a j else 0) ≤ ∑ j ∈ range (G - 1), a j := by
  classical
  rw [← sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => ha j
  have := (mem_filter.mp hj).2
  exact mem_range.mpr (by omega)

/-- **The slope of the near part.** The spikes cost at most `(4/y)(1 + log y²)` in all. -/
theorem compSlope_le (hc : IsCompensation y d) (hy : 4 ≤ y) {G : ℕ} (hG : 2 ≤ G) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hnear : ∀ s, 1 ≤ s → s < G → |compNear y d s - compCount y d s| ≤ (s : ℝ) * Y) :
    compSlope y d ≤ 1 - 1 / (G : ℝ) + 4 / (y : ℝ) * (1 + Real.log ((y * y : ℕ) : ℝ)) + Y * (1 + Real.log G) +
      compMass y d / G := by
  classical
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hGR : (0 : ℝ) < G := by exact_mod_cast (by omega : 0 < G)
  have hsum := (isFakePrimeMeasure_pronic (y * y)).hasSum_saw (fun k => -(compCoeff y d k : ℝ) / k)
  have hobj : objective (fun k => -(compCoeff y d k : ℝ) / k) (y * y) = compSlope y d := rfl
  rw [hobj] at hsum
  refine le_of_tendsto' hsum.tendsto_sum_nat fun n => ?_
  have hsaw : ∀ r, saw (fun k => -(compCoeff y d k : ℝ) / k) (y * y) r = compNear y d r := fun _ => rfl
  simp only [hsaw]
  -- The spike between `P` and `d_P`.
  have hspike : ∀ s, compCount y d s - 1 =
      ∑ P ∈ largePrimes y, if P ≤ s ∧ s < d P then (1 : ℝ) else 0 := by
    intro s
    rw [compCount, add_sub_cancel_left]
    refine sum_congr rfl fun P hP => ?_
    have hlt := hc.lt P hP
    by_cases h1 : d P ≤ s
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), sub_self]
    · by_cases h2 : P ≤ s
      · rw [if_pos h2, if_neg h1, if_pos ⟨h2, by omega⟩, sub_zero]
      · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), sub_zero]
  have hterm : ∀ j : ℕ, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * compNear y d (j + 1) ≤
      (if j + 1 < G then pronicStep j else 0) +
      (if j + 1 < G then Y * (1 / ((j : ℝ) + 2)) else 0) +
      ∑ P ∈ largePrimes y, (if P ≤ j + 1 ∧ j + 1 < d P then pronicStep j else 0) +
      compMass y d * (if G ≤ j + 1 then pronicStep j else 0) := by
    intro j
    have hp := pronicStep_nonneg j
    have hpron : (0 : ℝ) < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
    have hspk : 0 ≤ ∑ P ∈ largePrimes y, (if P ≤ j + 1 ∧ j + 1 < d P then pronicStep j else 0) :=
      sum_nonneg fun P _ => by split_ifs <;> linarith
    have hval : ∑ P ∈ largePrimes y, (if P ≤ j + 1 ∧ j + 1 < d P then pronicStep j else 0) =
        pronicStep j * (compCount y d (j + 1) - 1) := by
      rw [hspike, mul_sum]
      refine sum_congr rfl fun P _ => ?_
      split_ifs <;> simp
    change pronicStep j * compNear y d (j + 1) ≤ _
    by_cases hj : j + 1 < G
    · rw [if_pos hj, if_pos hj, if_neg (by omega), mul_zero, add_zero, hval]
      have hn := (abs_le.mp (hnear (j + 1) (by omega) hj)).2
      have h1 : compNear y d (j + 1) ≤ compCount y d (j + 1) + ((j + 1 : ℕ) : ℝ) * Y := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have e : pronicStep j * (((j + 1 : ℕ) : ℝ) * Y) = Y * (1 / ((j : ℝ) + 2)) := by
        rw [pronicStep]
        push_cast
        field_simp
      have e2 : pronicStep j * (compCount y d (j + 1) + ((j + 1 : ℕ) : ℝ) * Y) =
          pronicStep j * compCount y d (j + 1) + Y * (1 / ((j : ℝ) + 2)) := by
        rw [mul_add, e]
      rw [e2] at h2
      linarith
    · rw [if_neg hj, if_neg hj, if_pos (by omega), zero_add, zero_add]
      have h1 := (abs_le.mp (abs_compNear_le (y := y) (d := d) (j + 1))).2
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have hM0 : 0 ≤ compMass y d := compMass_nonneg
      nlinarith
  refine (sum_le_sum fun j _ => hterm j).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum]
  -- The four parts.
  have hA : ∑ j ∈ range n, (if j + 1 < G then pronicStep j else 0) ≤ 1 - 1 / (G : ℝ) := by
    refine (sum_ite_lt_le' pronicStep_nonneg n G).trans (le_of_eq ?_)
    rw [sum_range_pronicStep, Nat.cast_sub (by omega)]
    push_cast
    congr 2
    ring
  have hB : ∑ j ∈ range n, (if j + 1 < G then Y * (1 / ((j : ℝ) + 2)) else 0) ≤ Y * (1 + Real.log G) := by
    refine (sum_ite_lt_le' (fun j => by positivity) n G).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hY0
    have hH := harmonic_le_one_add_log G
    rw [harmonic_eq_sum_Icc] at hH
    push_cast at hH
    refine le_trans ?_ hH
    have hre : ∑ j ∈ range (G - 1), 1 / ((j : ℝ) + 2) = ∑ i ∈ Ioc 1 G, ((i : ℝ))⁻¹ := by
      have hset : Ioc 1 G = Ico 2 (G + 1) := by
        ext x
        simp only [mem_Ioc, mem_Ico]
        omega
      rw [hset, sum_Ico_eq_sum_range]
      have hn' : G + 1 - 2 = G - 1 := by omega
      rw [hn']
      refine sum_congr rfl fun j _ => ?_
      push_cast
      rw [one_div, add_comm]
    rw [hre]
    refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun _ _ _ => by positivity
    have := mem_Ioc.mp hi
    exact mem_Icc.mpr (by omega)
  have hC : ∑ j ∈ range n, ∑ P ∈ largePrimes y, (if P ≤ j + 1 ∧ j + 1 < d P then pronicStep j else 0) ≤
      4 / (y : ℝ) * (1 + Real.log ((y * y : ℕ) : ℝ)) := by
    rw [sum_comm]
    have hP : ∀ P ∈ largePrimes y, ∑ j ∈ range n, (if P ≤ j + 1 ∧ j + 1 < d P then pronicStep j else 0) ≤
        4 / (y : ℝ) * (1 / (d P : ℝ)) := by
      intro P hP
      have hP0 := (mem_largePrimes.mp hP).2.pos
      have hlt := hc.lt P hP
      have hPR : (0 : ℝ) < P := by exact_mod_cast hP0
      have hdR : (0 : ℝ) < d P := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le P) hlt
      have hsub : (range n).filter (fun j => P ≤ j + 1 ∧ j + 1 < d P) ⊆ Ico (P - 1) (d P - 1) := by
        intro j hj
        obtain ⟨-, h1, h2⟩ := mem_filter.mp hj
        exact mem_Ico.mpr (by omega)
      rw [← sum_filter]
      refine (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => pronicStep_nonneg j).trans ?_
      rw [sum_Ico_pronicStep (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      have e1 : (P : ℝ) - 1 + 1 = P := by ring
      have e2 : (d P : ℝ) - 1 + 1 = d P := by ring
      rw [e1, e2, div_sub_div _ _ hPR.ne' hdR.ne', one_mul, mul_one]
      have hle := hc.le P hP
      have hbound : (d P : ℝ) - P ≤ 4 * (P : ℝ) / y := by
        have e : (P : ℝ) * (1 + 4 / (y : ℝ)) = P + 4 * (P : ℝ) / y := by ring
        linarith
      rw [div_le_iff₀ (by positivity)]
      calc (d P : ℝ) - P ≤ 4 * (P : ℝ) / y := hbound
        _ = _ := by
            field_simp
    refine (sum_le_sum hP).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_inv_compensation_le hc) (by positivity)
  have hD : ∑ j ∈ range n, (if G ≤ j + 1 then pronicStep j else 0) ≤ 1 / (G : ℝ) := by
    rw [← sum_filter]
    by_cases hnG : G - 1 ≤ n
    · have hset : (range n).filter (fun j => G ≤ j + 1) = Ico (G - 1) n := by
        ext j
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      rw [hset, sum_Ico_pronicStep hnG, Nat.cast_sub (by omega)]
      push_cast
      have e : (G : ℝ) - 1 + 1 = G := by ring
      rw [e]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · have hset : (range n).filter (fun j => G ≤ j + 1) = ∅ := by
        ext j
        simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and, not_le]
        omega
      rw [hset, sum_empty]
      positivity
  have hM0 : 0 ≤ compMass y d := compMass_nonneg
  have hD' := mul_le_mul_of_nonneg_left hD hM0
  have e : compMass y d * (1 / (G : ℝ)) = compMass y d / G := by ring
  rw [e] at hD'
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
