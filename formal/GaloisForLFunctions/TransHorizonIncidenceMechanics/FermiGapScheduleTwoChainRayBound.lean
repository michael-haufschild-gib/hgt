import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapScheduleMixedChains
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiAllBoundaryTraceFourfoldConditioningGain

/-!
# One-gap Fermi schedules: the two-chain ray inequality

The **one-gap trace** at level `g ≥ 1` reads every reciprocal-cell boundary except those of
dyadic level `g` (the boundaries `2^g b`, `b` odd). At `g = 1` it is the selected trace. Along a
dyadic ray it misses exactly the step between the levels `g - 1` and `g`, so the ray splits into
two mixed chains: the bottom levels `0, …, g-1`, pinned below by the observed base value and
free at the gap, and the top levels `g, …, ⌊log₂ N⌋ + 1` with the saturated tail, free at the gap
and pinned above. A mixed chain of length `n` has constant `λ_n = 2 - 2 cos(π/(2n+1))`, the
Dirichlet constant of a chain of length `2n`, and `1/λ_n ≤ ((2n+1)² + 2)/π²`. Hence

`K_g(N) ≤ (1 + 2^-(m+1)) (max(2g + 2m + 3, 2(L - g) + 9)² + 2)/π²`, `L = ⌊log₂ N⌋`,

for every `m < g`: up to lower order the gap at relative depth `α = g/L` costs at most
`4 max(α, 1-α)²/π² · L²`. The edge gap `g = 1` is the selected trace, whose sharp constant is
`(4/π²) L²`. A gap at half depth costs nothing: its constant is squeezed between the full trace
and the bound above, and

`K_{⌊L/2⌋+1}(N)/(log₂ N)² → 1/π²`,

the value of the trace that reads every boundary. One unobserved level is free when it splits the
dyadic depth in half, and costs a factor four when it sits at the bottom.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The one-gap trace -/

/-- Physical energy of the readings at the boundaries `2^g b` (`b` odd) of dyadic level `g`. -/
def fermiLevelPronicEnergy (N : ℕ) (c : ℕ → ℝ) (g : ℕ) : ℝ :=
  ∑' j : ℕ, fermiBoundaryJump N c (2 ^ g * (2 * j + 1)) ^ 2 /
    (pronicSeq (2 ^ g * (2 * j + 1)) : ℝ)

/-- The **one-gap trace** energy: every boundary except those of dyadic level `g`. -/
def fermiGapPronicEnergy (N : ℕ) (c : ℕ → ℝ) (g : ℕ) : ℝ :=
  fermiAllBoundaryPronicEnergy N c - fermiLevelPronicEnergy N c g

/-- The one-gap energy of the ray over `b`, with the gap at level `h + 1`. -/
def fermiRayGapEnergy (N : ℕ) (c : ℕ → ℝ) (b h : ℕ) : ℝ :=
  fermiRayAllBoundaryEnergy N c b -
    fermiNormalizedDyadicJump N c b h ^ 2 * fermiDyadicPronicWeight (h + 1) b

theorem fermiLevel_term_eq (N : ℕ) (c : ℕ → ℝ) (b h : ℕ) :
    fermiBoundaryJump N c (2 ^ (h + 1) * b) ^ 2 / (pronicSeq (2 ^ (h + 1) * b) : ℝ) =
      fermiNormalizedDyadicJump N c b h ^ 2 * fermiDyadicPronicWeight (h + 1) b := by
  unfold fermiNormalizedDyadicJump fermiDyadicPronicWeight
  rw [div_pow]
  field_simp

/-- The level readings are one term of the all-boundary ray energy. -/
theorem fermiLevel_term_le_ray (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) (h : ℕ) :
    fermiNormalizedDyadicJump N c b h ^ 2 * fermiDyadicPronicWeight (h + 1) b ≤
      fermiRayAllBoundaryEnergy N c b := by
  unfold fermiRayAllBoundaryEnergy
  have h1 := (fermiRay_weighted_summable N c hb).2.le_tsum h
    (fun k _ => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
  have h2 : 0 ≤ fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b :=
    mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _)
  linarith

theorem fermiRayGapEnergy_nonneg (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) (h : ℕ) :
    0 ≤ fermiRayGapEnergy N c b h := by
  unfold fermiRayGapEnergy
  linarith [fermiLevel_term_le_ray N c hb h]

/-- The one-gap energy is the sum of its ray energies over odd bases. -/
theorem fermiGapPronicEnergy_eq_sum_rays (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    fermiGapPronicEnergy N c (h + 1) = ∑' j : ℕ, fermiRayGapEnergy N c (2 * j + 1) h ∧
      Summable (fun j : ℕ => fermiRayGapEnergy N c (2 * j + 1) h) := by
  obtain ⟨hQ, hQs⟩ := fermiAllBoundaryPronicEnergy_eq_sum_rays N c
  have hLs : Summable (fun j : ℕ => fermiNormalizedDyadicJump N c (2 * j + 1) h ^ 2 *
      fermiDyadicPronicWeight (h + 1) (2 * j + 1)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
      (fun j => fermiLevel_term_le_ray N c (by omega) h) hQs
  have hL : fermiLevelPronicEnergy N c (h + 1) = ∑' j : ℕ,
      fermiNormalizedDyadicJump N c (2 * j + 1) h ^ 2 *
        fermiDyadicPronicWeight (h + 1) (2 * j + 1) :=
    tsum_congr fun j => fermiLevel_term_eq N c (2 * j + 1) h
  refine ⟨?_, hQs.sub hLs⟩
  unfold fermiGapPronicEnergy fermiRayGapEnergy
  rw [hQ, hL, hQs.tsum_sub hLs]

theorem fermiGapPronicEnergy_nonneg (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    0 ≤ fermiGapPronicEnergy N c (h + 1) := by
  rw [(fermiGapPronicEnergy_eq_sum_rays N c h).1]
  exact tsum_nonneg fun j => fermiRayGapEnergy_nonneg N c (by omega) h

/-- The gap at level one is the selected trace. -/
theorem fermiGapPronicEnergy_one (N : ℕ) (c : ℕ → ℝ) :
    fermiGapPronicEnergy N c 1 = fermiSelectedTotalPronicEnergy N c := by
  have hL : fermiLevelPronicEnergy N c 1 = fermiTwiceOddPronicEnergy N c :=
    tsum_congr fun j => by rw [show 2 ^ 1 * (2 * j + 1) = 4 * j + 2 by ring]
  unfold fermiGapPronicEnergy fermiAllBoundaryPronicEnergy
  rw [hL]; ring

/-- Removing a level never increases the trace energy. -/
theorem fermiGapPronicEnergy_le_allBoundary (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    fermiGapPronicEnergy N c (h + 1) ≤ fermiAllBoundaryPronicEnergy N c := by
  have hL : 0 ≤ fermiLevelPronicEnergy N c (h + 1) :=
    tsum_nonneg fun j => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  unfold fermiGapPronicEnergy; linarith

/-! ### Mixed constants -/

/-- The mixed constant `λ_n = 2 - 2 cos(π/(2n+1))` of a chain of length `n`. -/
def mixedChainConstant (n : ℕ) : ℝ := 2 - 2 * Real.cos (Real.pi / (2 * (n : ℝ) + 1))

theorem mixedChainConstant_pos (n : ℕ) : 0 < mixedChainConstant n := by
  unfold mixedChainConstant
  have hx : 0 < Real.pi / (2 * (n : ℝ) + 1) := by positivity
  have hxπ : Real.pi / (2 * (n : ℝ) + 1) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, (Nat.cast_nonneg n : (0 : ℝ) ≤ _)]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hxπ hx
  rw [Real.cos_zero] at this
  linarith

/-- `1/λ_n ≤ ((2n+1)² + 2)/π²` for `n ≥ 2`. -/
theorem one_div_mixedChainConstant_le {n : ℕ} (hn : 2 ≤ n) :
    1 / mixedChainConstant n ≤ ((2 * (n : ℝ) + 1) ^ 2 + 2) / Real.pi ^ 2 := by
  set r : ℝ := 2 * (n : ℝ) + 1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr5 : (5 : ℝ) ≤ r := by simp only [r]; linarith
  set t := Real.pi / r with ht
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by linarith)]; linarith
  have ht2 : t ^ 2 ≤ Real.pi ^ 2 / 25 := by
    rw [ht, div_pow]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    nlinarith
  have hcos := Real.cos_bound (x := t) (by rw [abs_of_pos htpos]; exact ht1)
  rw [abs_of_pos htpos] at hcos
  have hlow : t ^ 2 * (1 - 5 * t ^ 2 / 48) ≤ mixedChainConstant n := by
    unfold mixedChainConstant
    have := (abs_le.mp hcos).2
    have hrr : Real.pi / (2 * (n : ℝ) + 1) = t := rfl
    rw [hrr]; nlinarith
  -- `(1 - 5t²/48)(1 + 2t²/π²) ≥ 1`
  have hkey : 1 ≤ t ^ 2 * (1 - 5 * t ^ 2 / 48) * (1 / t ^ 2 + 2 / Real.pi ^ 2) := by
    have hπ2 : 9 < Real.pi ^ 2 := by nlinarith
    have hπ2' : Real.pi ^ 2 < 10 := by nlinarith
    have ht0 : 0 < t ^ 2 := by positivity
    have e : t ^ 2 * (1 - 5 * t ^ 2 / 48) * (1 / t ^ 2 + 2 / Real.pi ^ 2) =
        (1 - 5 * t ^ 2 / 48) * (1 + 2 * t ^ 2 / Real.pi ^ 2) := by
      field_simp
    rw [e]
    have h1 : 2 * t ^ 2 / Real.pi ^ 2 ≥ t ^ 2 / 5 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have h2 : 2 * t ^ 2 / Real.pi ^ 2 ≤ 2 / 25 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hlampos := mixedChainConstant_pos n
  have hprod : 0 < t ^ 2 * (1 - 5 * t ^ 2 / 48) := by
    apply mul_pos (by positivity); nlinarith
  have hfin : 1 / mixedChainConstant n ≤ 1 / t ^ 2 + 2 / Real.pi ^ 2 := by
    rw [div_le_iff₀ hlampos]
    calc (1 : ℝ) ≤ t ^ 2 * (1 - 5 * t ^ 2 / 48) * (1 / t ^ 2 + 2 / Real.pi ^ 2) := hkey
      _ ≤ mixedChainConstant n * (1 / t ^ 2 + 2 / Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_right hlow (by positivity)
      _ = _ := by ring
  have e2 : 1 / t ^ 2 + 2 / Real.pi ^ 2 = (r ^ 2 + 2) / Real.pi ^ 2 := by
    rw [ht, div_pow]; field_simp
  rw [e2] at hfin
  exact hfin

/-! ### The two chains of a gapped ray -/

/-- **Bottom chain.** The levels `0, …, h` of a ray, pinned below by the base value and free at
the gap, with the first `m + 1` steps half-weighted. -/
theorem gap_bottom_chain_bound (y : ℕ → ℝ) {h m : ℕ} (hmh : m ≤ h) :
    mixedChainConstant (h + m + 2) * (∑ k ∈ range (h + 1), y k ^ 2) ≤
      (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
        ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 := by
  set zb : ℕ → ℝ := fun i => if i = 0 then 0 else y (i - 1) with hzb
  have hzb0 : zb 0 = 0 := by simp [hzb]
  have hzbs (k : ℕ) : zb (k + 1) = y k := by simp [hzb]
  have hbot := mixed_chain_soft_prefix_bound (h + 1) (m + 1) (by omega) zb hzb0
  have hbm : (∑ i ∈ range (h + 1 + 1), zb i ^ 2) = ∑ k ∈ range (h + 1), y k ^ 2 := by
    rw [sum_range_succ', hzb0]; simp only [hzbs]; ring
  have hbp : (∑ i ∈ range (m + 1), (zb (i + 1) - zb i) ^ 2) =
      y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
    rw [sum_range_succ', hzbs, hzb0]
    simp only [hzbs]
    rw [add_comm]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by ring
  have hbr : (∑ j ∈ range (h + 1 - (m + 1)), (zb (m + 1 + j + 1) - zb (m + 1 + j)) ^ 2) =
      ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 := by
    rw [show h + 1 - (m + 1) = h - m by omega]
    refine sum_congr rfl fun j _ => ?_
    rw [show m + 1 + j + 1 = (m + j + 1) + 1 by ring, hzbs, show m + 1 + j = (m + j) + 1 by ring,
      hzbs]
    ring
  rw [hbm, hbp, hbr] at hbot
  unfold mixedChainConstant
  convert hbot using 3
  push_cast; ring_nf

/-- **Top chain.** The levels `h + 1, …, D` of a ray continued by the three-step ramp `y_D/3`,
pinned above and free at the gap. -/
theorem gap_top_chain_bound (y : ℕ → ℝ) {h D : ℕ} (hhD : h + 1 ≤ D) :
    mixedChainConstant (D - h + 2) * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) ≤
      y D ^ 2 / 3 + ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 := by
  set T := D - h + 2 with hT
  set zt : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then y D / 3 else
    if i = 2 then 2 * y D / 3 else y (D + 3 - i) with hzt
  have hzt0 : zt 0 = 0 := by simp [hzt]
  have hzt1 : zt 1 = y D / 3 := by simp [hzt]
  have hzt2 : zt 2 = 2 * y D / 3 := by simp [hzt]
  have hzt3 (r : ℕ) : zt (3 + r) = y (D - r) := by
    simp only [hzt]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1; omega
  have htop := mixed_chain_energy_bound T zt hzt0
  have htm : (∑ i ∈ range (T + 1), zt i ^ 2) =
      5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2 := by
    rw [show T + 1 = 3 + (D - h) by omega, sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hzt0, hzt1, hzt2]
    have hrefl : (∑ r ∈ range (D - h), zt (3 + r) ^ 2) =
        ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2 := by
      simp only [hzt3]
      rw [← sum_range_reflect]
      exact sum_congr rfl fun k hk => by
        have := mem_range.mp hk; congr 2; omega
    rw [hrefl]
    ring
  have hte : (∑ i ∈ range T, (zt (i + 1) - zt i) ^ 2) =
      y D ^ 2 / 3 + ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 := by
    rw [show T = 3 + (D - h - 1) by omega, sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hzt0, hzt1, hzt2]
    have hz3 : zt (2 + 1) = y D := by rw [show (2 : ℕ) + 1 = 3 + 0 by rfl, hzt3 0, Nat.sub_zero]
    rw [hz3]
    have hrefl : (∑ r ∈ range (D - h - 1), (zt (3 + r + 1) - zt (3 + r)) ^ 2) =
        ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 := by
      have hsh (r : ℕ) : zt (3 + r + 1) = zt (3 + (r + 1)) := by
        rw [show 3 + r + 1 = 3 + (r + 1) by ring]
      simp only [hsh, hzt3]
      rw [← sum_range_reflect]
      refine sum_congr rfl fun k hk => ?_
      have := mem_range.mp hk
      rw [show D - (D - h - 1 - 1 - k + 1) = h + 1 + k by omega,
        show D - (D - h - 1 - 1 - k) = h + 1 + k + 1 by omega]
    rw [hrefl]
    ring
  rw [htm, hte] at htop
  unfold mixedChainConstant
  exact htop

/-- The sieve side of a ray: `b² P ≤ Σ_{k ≤ D} y_k² + y_D²/3`, `D = log₂ N + 1`. -/
theorem fermiRaySieveEnergy_sq_mul_le (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) :
    (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤
      (∑ k ∈ range (Nat.log 2 N + 1 + 1), fermiNormalizedDyadicSieve N c b k ^ 2) +
        fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1) ^ 2 / 3 := by
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hPs := (fermiRay_weighted_summable N c hb).1
  unfold fermiRaySieveEnergy
  rw [← tsum_mul_left]
  have hle : ∑' k : ℕ, (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b k ^ 2 *
      fermiDyadicPronicWeight k b) ≤ ∑' k : ℕ, fermiNormalizedDyadicSieve N c b k ^ 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) (hPs.mul_left _) (fermiRay_sq_summable N c b)
    have hw := (fermiDyadicPronicWeight_bounds k b hb).2
    have : (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b ≤ 1 := by
      rw [← le_div_iff₀' hb2]; simpa using hw
    nlinarith [sq_nonneg (fermiNormalizedDyadicSieve N c b k)]
  have hsplit := (fermiRay_sq_summable N c b).sum_add_tsum_nat_add (Nat.log 2 N + 1 + 1)
  have htail := fermiRay_value_tail N c b
  linarith

/-- The boundary side of a gapped ray: `ρ_m (E_bot + E_top) ≤ b² Q_gap`. -/
theorem fermiRayGapEnergy_ge (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) {h m : ℕ}
    (hmh : m ≤ h) (hhL : h ≤ Nat.log 2 N) :
    let y := fun k => fermiNormalizedDyadicSieve N c b k
    let D := Nat.log 2 N + 1
    fermiRayWeightFloor m *
        ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
          ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 +
          (y D ^ 2 / 3 + ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2)) ≤
      (b : ℝ) ^ 2 * fermiRayGapEnergy N c b h := by
  intro y D
  have hxy (k : ℕ) : fermiNormalizedDyadicJump N c b k = y k - y (k + 1) :=
    fermiNormalizedDyadicJump_eq_sub N c hb k
  have hQs := (fermiRay_weighted_summable N c hb).2
  set f : ℕ → ℝ := fun k => fermiNormalizedDyadicJump N c b k ^ 2 *
    fermiDyadicPronicWeight (k + 1) b with hf
  set ρ := fermiRayWeightFloor m
  have hρ1 : ρ ≤ 1 := fermiRayWeightFloor_le_one m
  have hsplit := hQs.sum_add_tsum_nat_add D
  have h1 : (∑ k ∈ range D, f k) = (∑ k ∈ range m, f k) + ∑ j ∈ range (D - m), f (m + j) := by
    have := sum_range_add f m (D - m); rwa [show m + (D - m) = D by omega] at this
  have h2 : (∑ j ∈ range (D - m), f (m + j)) = (∑ j ∈ range (h - m), f (m + j)) +
      ∑ j ∈ range (D - h), f (h + j) := by
    have := sum_range_add (fun j => f (m + j)) (h - m) (D - h)
    rw [show h - m + (D - h) = D - m by omega] at this
    rw [this]; congr 1; exact sum_congr rfl fun j _ => by congr 1; omega
  have h3 : (∑ j ∈ range (D - h), f (h + j)) = f h + ∑ k ∈ range (D - h - 1), f (h + 1 + k) := by
    rw [show D - h = (D - h - 1) + 1 by omega, sum_range_succ', add_comm]
    congr 1
    exact sum_congr rfl fun k _ => by congr 1; omega
  have hgap : fermiRayGapEnergy N c b h =
      fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
        ((∑ k ∈ range m, f k) + (∑ j ∈ range (h - m), f (m + j)) +
          (∑ k ∈ range (D - h - 1), f (h + 1 + k)) + ∑' j, f (j + D)) := by
    unfold fermiRayGapEnergy fermiRayAllBoundaryEnergy
    have hfh : fermiNormalizedDyadicJump N c b h ^ 2 * fermiDyadicPronicWeight (h + 1) b = f h :=
      rfl
    rw [hfh, ← hsplit, h1, h2, h3]
    ring
  have hw_half (k : ℕ) : (1 / 2 : ℝ) ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b :=
    (half_le_fermiWeightRatio k).trans (fermiDyadicPronicWeight_floor k b hb)
  have hw_ρ (k : ℕ) (hk : m + 1 ≤ k) : ρ ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b :=
    (fermiWeightRatio_mono hk).trans (fermiDyadicPronicWeight_floor k b hb)
  have hbase : (1 / 2) * y 0 ^ 2 ≤
      (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) := by
    have := hw_half 0
    have e : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 *
        fermiDyadicPronicWeight 0 b) = y 0 ^ 2 * ((b : ℝ) ^ 2 * fermiDyadicPronicWeight 0 b) := by
      simp only [y]; ring
    rw [e]; exact (mul_le_mul_of_nonneg_left this (sq_nonneg _)).trans_eq' (mul_comm _ _)
  have hlow : (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ k ∈ range m, f k := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have e : (b : ℝ) ^ 2 * f k = (y k - y (k + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (k + 1) b) := by
      simp only [hf, hxy k]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_half (k + 1)) (sq_nonneg _)).trans_eq' (mul_comm _ _)
  have hmid : ρ * ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ j ∈ range (h - m), f (m + j) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    have e : (b : ℝ) ^ 2 * f (m + j) = (y (m + j) - y (m + j + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (m + j + 1) b) := by
      simp only [hf, hxy (m + j)]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (m + j + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have htopQ : ρ * ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ k ∈ range (D - h - 1), f (h + 1 + k) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have e : (b : ℝ) ^ 2 * f (h + 1 + k) = (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (h + 1 + k + 1) b) := by
      simp only [hf, hxy (h + 1 + k)]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (h + 1 + k + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have htailQ : ρ * (y D ^ 2 / 3) ≤ (b : ℝ) ^ 2 * ∑' j : ℕ, f (j + D) := by
    have ht := fermiRay_jump_tail N c hb
    have hyD : y D ^ 2 / 3 = ∑' j : ℕ, fermiNormalizedDyadicJump N c b (j + D) ^ 2 := ht.symm
    rw [hyD, ← tsum_mul_left, ← tsum_mul_left]
    have hsum1 : Summable (fun j => ρ * fermiNormalizedDyadicJump N c b (j + D) ^ 2) :=
      (((summable_nat_add_iff D).mpr (fermiRay_jump_sq_summable N c hb))).mul_left _
    have hsum2 : Summable (fun j => (b : ℝ) ^ 2 * f (j + D)) :=
      ((summable_nat_add_iff D).mpr hQs).mul_left _
    refine Summable.tsum_le_tsum (fun j => ?_) hsum1 hsum2
    have e : (b : ℝ) ^ 2 * f (j + D) = fermiNormalizedDyadicJump N c b (j + D) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (j + D + 1) b) := by simp only [hf]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (j + D + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have hhalf : ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) ≤
      (1 / 2) * y 0 ^ 2 + (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))
    calc ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) ≤
        1 * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_right hρ1 h0
      _ = _ := by ring
  rw [hgap]
  have hL : ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
        ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 +
        (y D ^ 2 / 3 + ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2)) =
      ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) +
        ρ * ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 + ρ * (y D ^ 2 / 3) +
        ρ * ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 := by ring
  have hR : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
        ((∑ k ∈ range m, f k) + (∑ j ∈ range (h - m), f (m + j)) +
          (∑ k ∈ range (D - h - 1), f (h + 1 + k)) + ∑' j, f (j + D))) =
      (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) +
        (b : ℝ) ^ 2 * (∑ k ∈ range m, f k) + (b : ℝ) ^ 2 * (∑ j ∈ range (h - m), f (m + j)) +
        (b : ℝ) ^ 2 * (∑ k ∈ range (D - h - 1), f (h + 1 + k)) +
        (b : ℝ) ^ 2 * ∑' j, f (j + D) := by ring
  rw [hL, hR]
  linarith

/-- **Two-chain ray inequality.** With the gap at level `h + 1` and `m ≤ h ≤ log₂ N`, the ray
sieve energy is at most `1/(ρ_m min(λ_{h+m+2}, λ_{log₂ N - h + 3}))` times the one-gap ray
energy. -/
theorem fermiRaySieveEnergy_le_gap (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) {h m : ℕ}
    (hmh : m ≤ h) (hhL : h ≤ Nat.log 2 N) :
    fermiRaySieveEnergy N c b ≤
      1 / (fermiRayWeightFloor m * min (mixedChainConstant (h + m + 2))
        (mixedChainConstant (Nat.log 2 N - h + 3))) * fermiRayGapEnergy N c b h := by
  set y : ℕ → ℝ := fun k => fermiNormalizedDyadicSieve N c b k with hy
  set D := Nat.log 2 N + 1 with hD
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hρ := fermiRayWeightFloor_pos m
  set lb := mixedChainConstant (h + m + 2)
  set lt := mixedChainConstant (Nat.log 2 N - h + 3)
  have hlb := mixedChainConstant_pos (h + m + 2)
  have hlt := mixedChainConstant_pos (Nat.log 2 N - h + 3)
  set lam := min lb lt
  have hlam : 0 < lam := lt_min hlb hlt
  have hP := fermiRaySieveEnergy_sq_mul_le N c hb
  have hbot := gap_bottom_chain_bound y hmh
  have htop := gap_top_chain_bound y (show h + 1 ≤ D by omega)
  rw [show D - h + 2 = Nat.log 2 N - h + 3 by omega] at htop
  have hQ := fermiRayGapEnergy_ge N c hb hmh hhL
  simp only at hQ
  set Eb := (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
    ∑ j ∈ range (h - m), (y (m + j) - y (m + j + 1)) ^ 2 with hEb
  set Et := y D ^ 2 / 3 + ∑ k ∈ range (D - h - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2
    with hEt
  have hsplitY : (∑ k ∈ range (D + 1), y k ^ 2) =
      (∑ k ∈ range (h + 1), y k ^ 2) + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2 := by
    have := sum_range_add (fun k => y k ^ 2) (h + 1) (D - h)
    rwa [show h + 1 + (D - h) = D + 1 by omega] at this
  have hbot' : (∑ k ∈ range (h + 1), y k ^ 2) ≤ Eb / lam := by
    rw [le_div_iff₀ hlam]
    have : lam * (∑ k ∈ range (h + 1), y k ^ 2) ≤ lb * (∑ k ∈ range (h + 1), y k ^ 2) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  have htop' : (∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) + y D ^ 2 / 3 ≤ Et / lam := by
    rw [le_div_iff₀ hlam]
    have hm0 : 0 ≤ 5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2 :=
      add_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)
    have : lam * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) ≤
        lt * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hm0
    have hy2 : 0 ≤ lam * (y D ^ 2 / 3) := mul_nonneg hlam.le (by positivity)
    have e : lam * ((∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) + y D ^ 2 / 3) ≤
        lam * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h), y (h + 1 + k) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hlam.le
      nlinarith [sq_nonneg (y D)]
    linarith
  have hfin : (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤ (Eb + Et) / lam := by
    rw [add_div]
    have hP' : (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤
        (∑ k ∈ range (D + 1), y k ^ 2) + y D ^ 2 / 3 := hP
    rw [hsplitY] at hP'
    linarith
  have hK : 0 ≤ 1 / (fermiRayWeightFloor m * lam) := by positivity
  rw [← mul_le_mul_iff_of_pos_left hb2]
  calc (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤ (Eb + Et) / lam := hfin
    _ = 1 / (fermiRayWeightFloor m * lam) * (fermiRayWeightFloor m * (Eb + Et)) := by
        field_simp
    _ ≤ 1 / (fermiRayWeightFloor m * lam) * ((b : ℝ) ^ 2 * fermiRayGapEnergy N c b h) :=
        mul_le_mul_of_nonneg_left hQ hK
    _ = _ := by ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
