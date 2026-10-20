import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiAllBoundaryTraceConditioningBound

/-!
# Rising sine packets for the all-boundary Fermi trace

On `L + 1` dyadic levels put the rising sine profile `y_k = sin((k+1)θ)`, `θ = π/(L+2)`, and
synthesize it by the dyadic coefficients `c(1) = y₀`, `c(2^(k+1)) = 2^(k+1) y_{k+1} - 2^k y_k`.
The profile vanishes at the virtual levels `-1` and `L + 1`, so it is the Dirichlet ground
mode of the chain: its jump energy, base jump included, is exactly `λ S` with
`λ = 2 - 2 cos θ` and mass `S = Σ y_k² = (L+2)/2`. Horizon saturation continues the top value
`y_L = sin θ` by halving and costs only `sin² θ / 3`. All coefficients are nonnegative, because
`2 sin((k+1)θ) ≥ sin(kθ)` on the whole profile by reflection.

On every dyadic ray the physical sieve energy is at least `(S - 2)/b²` and the physical
all-boundary energy at most `λ S / b²`. Hence, at every horizon `N ≥ 2^L`, both all-boundary
inverse constants are at least `(1 - 4/(L+2))/λ ≈ (L+2)²/π²`.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Angle of the rising sine profile on `L + 1` levels. -/
def sinePacketAngle (L : ℕ) : ℝ := Real.pi / ((L : ℝ) + 2)

/-- The rising sine profile `sin((k+1)π/(L+2))`. -/
def sinePacketProfile (L k : ℕ) : ℝ := Real.sin (((k : ℝ) + 1) * sinePacketAngle L)

/-- Dyadic coefficients whose normalized rays follow the rising sine profile. -/
def fermiDyadicSinePacket (L d : ℕ) : ℝ :=
  (if d = 1 then sinePacketProfile L 0 else 0) +
    ∑ k ∈ range L, if d = 2 ^ (k + 1) then
      (2 : ℝ) ^ (k + 1) * sinePacketProfile L (k + 1) - (2 : ℝ) ^ k * sinePacketProfile L k
    else 0

/-! ### The profile -/

private theorem angle_pos (L : ℕ) : 0 < sinePacketAngle L := by
  unfold sinePacketAngle; positivity

private theorem angle_mul (L : ℕ) : ((L : ℝ) + 2) * sinePacketAngle L = Real.pi := by
  unfold sinePacketAngle; field_simp

private theorem profile_nonneg (L k : ℕ) (hk : k ≤ L + 1) : 0 ≤ sinePacketProfile L k := by
  unfold sinePacketProfile
  apply Real.sin_nonneg_of_nonneg_of_le_pi (by have := angle_pos L; positivity)
  have hk' : (k : ℝ) + 1 ≤ (L : ℝ) + 2 := by exact_mod_cast (show k + 1 ≤ L + 2 by omega)
  rw [← angle_mul L]
  exact mul_le_mul_of_nonneg_right hk' (angle_pos L).le

private theorem profile_le_one (L k : ℕ) : sinePacketProfile L k ≤ 1 := Real.sin_le_one _

private theorem profile_zero_pos (L : ℕ) : 0 < sinePacketProfile L 0 := by
  unfold sinePacketProfile
  simp only [Nat.cast_zero, zero_add, one_mul]
  apply Real.sin_pos_of_pos_of_lt_pi (angle_pos L)
  unfold sinePacketAngle
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

private theorem profile_top (L : ℕ) : sinePacketProfile L (L + 1) = 0 := by
  unfold sinePacketProfile
  rw [show ((L + 1 : ℕ) : ℝ) + 1 = (L : ℝ) + 2 by push_cast; ring, angle_mul, Real.sin_pi]

private theorem profile_last (L : ℕ) : sinePacketProfile L L = sinePacketProfile L 0 := by
  unfold sinePacketProfile
  have h : ((L : ℝ) + 1) * sinePacketAngle L = Real.pi - sinePacketAngle L := by
    have := angle_mul L; linarith
  rw [h, Real.sin_pi_sub]
  simp

/-- `sin a ≤ sin x` whenever `0 ≤ a ≤ x ≤ π - a`. -/
private theorem sin_le_sin_of_inner {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hx : x ≤ Real.pi - a) : Real.sin a ≤ Real.sin x := by
  by_cases h : x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h hax
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)

/-- The rising sine profile never more than halves from one level to the next. -/
private theorem profile_half_le (L k : ℕ) (hk : k < L) :
    sinePacketProfile L k ≤ 2 * sinePacketProfile L (k + 1) := by
  set θ := sinePacketAngle L
  have hθ := angle_pos L
  have hπ := angle_mul L
  -- reflect: `y_{k+1} = sin(jθ)`, `y_k = sin((j+1)θ)` with `j = L - k`
  have hj1 : ((L - k : ℕ) : ℝ) = (L : ℝ) - k := by push_cast [Nat.cast_sub hk.le]; ring
  have hr1 : sinePacketProfile L (k + 1) = Real.sin (((L - k : ℕ) : ℝ) * θ) := by
    unfold sinePacketProfile
    rw [hj1, show ((L : ℝ) - k) * θ = Real.pi - (((k + 1 : ℕ) : ℝ) + 1) * θ by
      push_cast; nlinarith, Real.sin_pi_sub]
  have hr0 : sinePacketProfile L k = Real.sin ((((L - k : ℕ) : ℝ) + 1) * θ) := by
    unfold sinePacketProfile
    rw [hj1, show ((L : ℝ) - k + 1) * θ = Real.pi - ((k : ℝ) + 1) * θ by nlinarith,
      Real.sin_pi_sub]
  rw [hr1, hr0]
  have hj : (1 : ℝ) ≤ ((L - k : ℕ) : ℝ) := by
    have : 1 ≤ L - k := by omega
    exact_mod_cast this
  have hjL : ((L - k : ℕ) : ℝ) ≤ (L : ℝ) := by
    have : L - k ≤ L := Nat.sub_le L k
    exact_mod_cast this
  set j : ℝ := ((L - k : ℕ) : ℝ)
  have hjθ : j * θ ≤ Real.pi - θ := by nlinarith
  have hsj : 0 ≤ Real.sin (j * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  have hsθ : Real.sin θ ≤ Real.sin (j * θ) :=
    sin_le_sin_of_inner hθ.le (by nlinarith) hjθ
  have hsθ0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.le (by nlinarith)
  rw [show (j + 1) * θ = j * θ + θ by ring, Real.sin_add]
  have hc1 := Real.cos_le_one θ
  have hc2 := Real.cos_le_one (j * θ)
  nlinarith [mul_le_mul_of_nonneg_left hc1 hsj, mul_le_mul_of_nonneg_right hc2 hsθ0]

/-- Every coefficient of the rising sine packet is nonnegative. -/
theorem fermiDyadicSinePacket_nonneg (L d : ℕ) : 0 ≤ fermiDyadicSinePacket L d := by
  unfold fermiDyadicSinePacket
  apply add_nonneg
  · split_ifs
    · exact (profile_zero_pos L).le
    · rfl
  · apply sum_nonneg
    intro k hk
    split_ifs
    · have h := profile_half_le L k (mem_range.mp hk)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
      rw [pow_succ]
      nlinarith
    · rfl

/-! ### Exact mass and Dirichlet energy of the profile -/

/-- Telescoping cosine sum: `2 sin θ Σ_{k<n} cos(2(k+1)θ) = sin((2n+1)θ) - sin θ`. -/
private theorem two_sin_mul_sum_cos_even (θ : ℝ) (n : ℕ) :
    2 * Real.sin θ * (∑ k ∈ range n, Real.cos (2 * ((k : ℝ) + 1) * θ)) =
      Real.sin ((2 * (n : ℝ) + 1) * θ) - Real.sin θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := Real.sin_sub_sin ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ) ((2 * (n : ℝ) + 1) * θ)
    have e1 : ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ - (2 * (n : ℝ) + 1) * θ) / 2 = θ := by
      push_cast; ring
    have e2 : ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ + (2 * (n : ℝ) + 1) * θ) / 2 =
        2 * ((n : ℝ) + 1) * θ := by push_cast; ring
    rw [e1, e2] at h
    linarith

/-- The profile mass is exactly `(L + 2)/2`. -/
theorem sinePacketProfile_mass (L : ℕ) :
    (∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2) = ((L : ℝ) + 2) / 2 := by
  set θ := sinePacketAngle L
  have hθ := angle_pos L
  have hπ := angle_mul L
  have hsin : Real.sin θ ≠ 0 := (profile_zero_pos L).ne' |>.symm |> fun h => by
    have := profile_zero_pos L
    unfold sinePacketProfile at this
    simp only [Nat.cast_zero, zero_add, one_mul] at this
    exact this.ne'
  have hcos : (∑ k ∈ range (L + 1), Real.cos (2 * ((k : ℝ) + 1) * θ)) = -1 := by
    have h := two_sin_mul_sum_cos_even θ (L + 1)
    have htop : (2 * (((L + 1 : ℕ) : ℝ)) + 1) * θ = 2 * Real.pi - θ := by
      push_cast; nlinarith
    rw [htop, Real.sin_two_pi_sub] at h
    have : 2 * Real.sin θ * (∑ k ∈ range (L + 1), Real.cos (2 * ((k : ℝ) + 1) * θ) + 1) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero hsin)
    · linarith
  have hsq (k : ℕ) : sinePacketProfile L k ^ 2 =
      1 / 2 - Real.cos (2 * ((k : ℝ) + 1) * θ) / 2 := by
    unfold sinePacketProfile
    rw [show 2 * ((k : ℝ) + 1) * θ = 2 * (((k : ℝ) + 1) * θ) by ring, Real.cos_two_mul,
      Real.cos_sq']
    ring
  simp_rw [hsq]
  have hdiv : (∑ x ∈ range (L + 1), Real.cos (2 * ((x : ℝ) + 1) * θ) / 2) =
      (∑ x ∈ range (L + 1), Real.cos (2 * ((x : ℝ) + 1) * θ)) / 2 :=
    (Finset.sum_div _ _ _).symm
  rw [Finset.sum_sub_distrib, hdiv, hcos, Finset.sum_const, Finset.card_range]
  simp
  ring

/-- Dirichlet ground mode: base jump, interior jumps and the drop at the top sum to
`(2 - 2 cos θ)` times the mass. -/
theorem sinePacketProfile_dirichlet_energy (L : ℕ) :
    sinePacketProfile L 0 ^ 2 +
        (∑ k ∈ range L, (sinePacketProfile L k - sinePacketProfile L (k + 1)) ^ 2) +
        sinePacketProfile L L ^ 2 =
      (2 - 2 * Real.cos (sinePacketAngle L)) *
        ∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2 := by
  set θ := sinePacketAngle L
  -- the chain `v_j = sin(jθ)`, `v_0 = v_{L+2} = 0`
  set v : ℕ → ℝ := fun j => Real.sin ((j : ℝ) * θ) with hv
  have hvP (k : ℕ) : sinePacketProfile L k = v (k + 1) := by
    simp [hv, sinePacketProfile, θ]
  have hv0 : v 0 = 0 := by simp [hv]
  have hvend : v (L + 2) = 0 := by
    simp only [hv]
    rw [show ((L + 2 : ℕ) : ℝ) = (L : ℝ) + 2 by push_cast; ring, angle_mul, Real.sin_pi]
  have hrec (j : ℕ) : v (j + 2) + v j = 2 * Real.cos θ * v (j + 1) := by
    simp only [hv]
    have h1 := Real.sin_add (((j + 1 : ℕ) : ℝ) * θ) θ
    have h2 := Real.sin_sub (((j + 1 : ℕ) : ℝ) * θ) θ
    rw [show ((j + 2 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ + θ by push_cast; ring,
      show (j : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ - θ by push_cast; ring, h1, h2]
    ring
  -- `A = Σ_{j<L+2} v_j v_{j+1}` equals `cos θ · T`, `T = Σ_{j<L+2} v_j²`
  set T := ∑ j ∈ range (L + 2), v j ^ 2
  set A := ∑ j ∈ range (L + 2), v j * v (j + 1)
  have hA : A = Real.cos θ * T := by
    have hA1 : A = ∑ j ∈ range (L + 1), v (j + 1) * v (j + 2) := by
      simp only [A]; rw [Finset.sum_range_succ', hv0]; simp
    have hA2 : (∑ j ∈ range (L + 1), v (j + 1) * v (j + 2)) =
        2 * Real.cos θ * (∑ j ∈ range (L + 1), v (j + 1) ^ 2) -
          ∑ j ∈ range (L + 1), v j * v (j + 1) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      have := hrec j
      have : v (j + 2) = 2 * Real.cos θ * v (j + 1) - v j := by linarith
      rw [this]; ring
    have hA3 : (∑ j ∈ range (L + 1), v j * v (j + 1)) = A := by
      have h := Finset.sum_range_succ (fun j => v j * v (j + 1)) (L + 1)
      rw [show L + 1 + 1 = L + 2 by ring, hvend, mul_zero, add_zero] at h
      exact h.symm
    have hT : (∑ j ∈ range (L + 1), v (j + 1) ^ 2) = T := by
      simp only [T]; rw [Finset.sum_range_succ' (fun j => v j ^ 2), hv0]; simp
    rw [hA2, hA3, hT] at hA1
    linarith
  -- jump energy of the chain
  have hE : (∑ j ∈ range (L + 2), (v (j + 1) - v j) ^ 2) = (2 - 2 * Real.cos θ) * T := by
    have hshift : (∑ j ∈ range (L + 2), v (j + 1) ^ 2) = T := by
      simp only [T]
      rw [Finset.sum_range_succ (fun j => v (j + 1) ^ 2), Finset.sum_range_succ' (fun j => v j ^ 2),
        show L + 1 + 1 = L + 2 by ring, hvend, hv0]
    have : (∑ j ∈ range (L + 2), (v (j + 1) - v j) ^ 2) =
        (∑ j ∈ range (L + 2), v (j + 1) ^ 2) + T - 2 * A := by
      simp only [T, A]
      rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [this, hshift, hA]; ring
  -- translate to the profile
  have hmass : (∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2) = T := by
    simp only [T]
    rw [Finset.sum_range_succ' (fun j => v j ^ 2), hv0]
    simp [hvP]
  have hjumps : sinePacketProfile L 0 ^ 2 +
      (∑ k ∈ range L, (sinePacketProfile L k - sinePacketProfile L (k + 1)) ^ 2) +
      sinePacketProfile L L ^ 2 = ∑ j ∈ range (L + 2), (v (j + 1) - v j) ^ 2 := by
    rw [show L + 2 = L + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ', hv0]
    rw [show L + 1 + 1 = L + 2 by ring, hvend]
    simp only [hvP]
    have : (∑ k ∈ range L, (v (k + 1) - v (k + 1 + 1)) ^ 2) =
        ∑ k ∈ range L, (v (k + 1 + 1) - v (k + 1)) ^ 2 :=
      sum_congr rfl fun k _ => by ring
    rw [this]
    ring
  rw [hjumps, hE, hmass]

/-! ### The packet on dyadic rays -/

private theorem pow_dvd_odd_ray (a k : ℕ) {b : ℕ} (hb : Odd b) :
    (2 : ℕ) ^ a ∣ 2 ^ k * b ↔ a ≤ k := by
  rw [(Nat.Coprime.pow_left a hb.coprime_two_left).dvd_mul_right,
    Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))]

private theorem prefix_telescope (L k : ℕ) (f : ℕ → ℝ) :
    f 0 + (∑ j ∈ range L, if j < k then f (j + 1) - f j else 0) = f (min L k) := by
  have hs : (range L).filter (fun j => j < k) = range (min L k) := by
    ext j; simp
  rw [← Finset.sum_filter, hs, Finset.sum_range_sub]
  ring

/-- On the ray over an odd base, the packet response is `2^min(k,L) y_{min(k,L)}`, at every
horizon `N ≥ 2^L`. -/
theorem sieveSeq_fermiDyadicSinePacket_ray {L N : ℕ} (hLN : 2 ^ L ≤ N) (k : ℕ) {b : ℕ}
    (hb : Odd b) :
    sieveSeq N (fermiDyadicSinePacket L) (2 ^ k * b) =
      (2 : ℝ) ^ (min L k) * sinePacketProfile L (min L k) := by
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hLN
  unfold sieveSeq fermiDyadicSinePacket
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc]
  rw [if_pos ⟨⟨le_rfl, hN1⟩, one_dvd _⟩]
  let f := fun j : ℕ => (2 : ℝ) ^ j * sinePacketProfile L j
  have ht (j : ℕ) (hj : j ∈ range L) :
      (if (1 ≤ 2 ^ (j + 1) ∧ 2 ^ (j + 1) ≤ N) ∧ 2 ^ (j + 1) ∣ 2 ^ k * b then
        (2 : ℝ) ^ (j + 1) * sinePacketProfile L (j + 1) - (2 : ℝ) ^ j * sinePacketProfile L j
      else 0) = if j < k then f (j + 1) - f j else 0 := by
    have hjL := mem_range.mp hj
    have hle : 2 ^ (j + 1) ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) hjL) hLN
    have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    simp only [hle, hpos, true_and, pow_dvd_odd_ray (j + 1) k hb,
      show j + 1 ≤ k ↔ j < k by omega]
    rfl
  rw [Finset.sum_congr rfl ht]
  have h0 : sinePacketProfile L 0 = f 0 := by simp [f]
  rw [h0, prefix_telescope]

private theorem packet_normalized_head {L N : ℕ} (hLN : 2 ^ L ≤ N) {b : ℕ} (hb : Odd b)
    {k : ℕ} (hk : k ≤ L) :
    fermiNormalizedDyadicSieve N (fermiDyadicSinePacket L) b k = sinePacketProfile L k := by
  unfold fermiNormalizedDyadicSieve
  rw [sieveSeq_fermiDyadicSinePacket_ray hLN k hb, Nat.min_eq_right hk]
  field_simp

private theorem packet_normalized_tail {L N : ℕ} (hLN : 2 ^ L ≤ N) {b : ℕ} (hb : Odd b)
    (j : ℕ) :
    fermiNormalizedDyadicSieve N (fermiDyadicSinePacket L) b (L + j) =
      sinePacketProfile L L / (2 : ℝ) ^ j := by
  unfold fermiNormalizedDyadicSieve
  rw [sieveSeq_fermiDyadicSinePacket_ray hLN (L + j) hb, Nat.min_eq_left (by omega), pow_add]
  field_simp

private theorem weight_floor' (k b : ℕ) (hb : 0 < b) :
    (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b := by
  have h := (fermiDyadicPronicWeight_bounds k b hb).1
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h hb2.le
  have he : (b : ℝ) ^ 2 * ((2 : ℝ) ^ k / (((2 : ℝ) ^ k + 1) * (b : ℝ) ^ 2)) =
      (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) := by
    field_simp
  linarith

private theorem weight_ceiling (k b : ℕ) (hb : 0 < b) :
    (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b ≤ 1 := by
  have h := (fermiDyadicPronicWeight_bounds k b hb).2
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  rw [← le_div_iff₀' hb2]; simpa using h

/-- On every ray the packet's physical sieve energy is at least `(S - 2)/b²`. -/
theorem fermiRaySieveEnergy_sinePacket_ge {L N : ℕ} (hLN : 2 ^ L ≤ N) {b : ℕ} (hb : Odd b) :
    (∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2) - 2 ≤
      (b : ℝ) ^ 2 * fermiRaySieveEnergy N (fermiDyadicSinePacket L) b := by
  have hb0 : 0 < b := hb.pos
  have hs := (fermiRay_weighted_summable N (fermiDyadicSinePacket L) hb0).1
  have hpart := hs.sum_le_tsum (range (L + 1))
    (fun k _ => mul_nonneg (sq_nonneg _) (by unfold fermiDyadicPronicWeight; positivity))
  unfold fermiRaySieveEnergy
  have hterm (k : ℕ) (hk : k ∈ range (L + 1)) :
      sinePacketProfile L k ^ 2 - 1 / (2 : ℝ) ^ k ≤ (b : ℝ) ^ 2 *
        (fermiNormalizedDyadicSieve N (fermiDyadicSinePacket L) b k ^ 2 *
          fermiDyadicPronicWeight k b) := by
    rw [packet_normalized_head hLN hb (by have := mem_range.mp hk; omega)]
    have hw := weight_floor' k b hb0
    have hp1 : sinePacketProfile L k ^ 2 ≤ 1 := by
      have h1 := profile_le_one L k
      have h0 := profile_nonneg L k (by have := mem_range.mp hk; omega)
      nlinarith
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hfrac : 1 - 1 / (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) := by
      have he : (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) = 1 - 1 / ((2 : ℝ) ^ k + 1) := by
        field_simp; ring
      have hi : 1 / ((2 : ℝ) ^ k + 1) ≤ 1 / (2 : ℝ) ^ k :=
        one_div_le_one_div_of_le h2 (by linarith)
      linarith
    have e1 := mul_le_mul_of_nonneg_left (hfrac.trans hw) (sq_nonneg (sinePacketProfile L k))
    have e2 : sinePacketProfile L k ^ 2 * (1 / (2 : ℝ) ^ k) ≤ 1 * (1 / (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hp1 (by positivity)
    have e3 : (b : ℝ) ^ 2 * (sinePacketProfile L k ^ 2 * fermiDyadicPronicWeight k b) =
        sinePacketProfile L k ^ 2 * ((b : ℝ) ^ 2 * fermiDyadicPronicWeight k b) := by ring
    rw [e3]
    nlinarith
  have hgeom : (∑ k ∈ range (L + 1), 1 / (2 : ℝ) ^ k) ≤ 2 := by
    have := sum_geometric_two_le (L + 1)
    simpa [one_div, inv_pow] using this
  calc (∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2) - 2
      ≤ ∑ k ∈ range (L + 1), (sinePacketProfile L k ^ 2 - 1 / (2 : ℝ) ^ k) := by
        rw [Finset.sum_sub_distrib]; linarith
    _ ≤ ∑ k ∈ range (L + 1), (b : ℝ) ^ 2 *
        (fermiNormalizedDyadicSieve N (fermiDyadicSinePacket L) b k ^ 2 *
          fermiDyadicPronicWeight k b) := Finset.sum_le_sum hterm
    _ = (b : ℝ) ^ 2 * ∑ k ∈ range (L + 1),
        fermiNormalizedDyadicSieve N (fermiDyadicSinePacket L) b k ^ 2 *
          fermiDyadicPronicWeight k b := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpart (by positivity)

/-- On every ray the packet's physical all-boundary energy is at most `λ S / b²`. -/
theorem fermiRayAllBoundaryEnergy_sinePacket_le {L N : ℕ} (hLN : 2 ^ L ≤ N) {b : ℕ}
    (hb : Odd b) :
    (b : ℝ) ^ 2 * fermiRayAllBoundaryEnergy N (fermiDyadicSinePacket L) b ≤
      (2 - 2 * Real.cos (sinePacketAngle L)) *
        ∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2 := by
  have hb0 : 0 < b := hb.pos
  set c := fermiDyadicSinePacket L
  set y := fun k => fermiNormalizedDyadicSieve N c b k
  have hxy (k : ℕ) : fermiNormalizedDyadicJump N c b k = y k - y (k + 1) :=
    fermiNormalizedDyadicJump_eq_sub N c hb0 k
  have hs := (fermiRay_weighted_summable N c hb0).2
  -- the jumps beyond level `L` halve the top value
  have hxtail (j : ℕ) : fermiNormalizedDyadicJump N c b (j + L) =
      sinePacketProfile L L / (2 : ℝ) ^ (j + 1) := by
    rw [hxy, show j + L = L + j by ring, show L + j + 1 = L + (j + 1) by ring]
    simp only [y]
    rw [packet_normalized_tail hLN hb, packet_normalized_tail hLN hb, pow_succ]
    field_simp; ring
  have hsq_tail : Summable (fun j : ℕ => (sinePacketProfile L L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail_val : ∑' j : ℕ, (sinePacketProfile L L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j =
      sinePacketProfile L L ^ 2 / 3 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have hxtail_sq (j : ℕ) : fermiNormalizedDyadicJump N c b (j + L) ^ 2 =
      (sinePacketProfile L L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j := by
    have h4 : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring, pow_add, pow_mul]
      norm_num; ring
    rw [hxtail, div_pow, h4, one_div_pow]
    field_simp
  -- bound the weighted series by the unweighted one
  unfold fermiRayAllBoundaryEnergy
  have hsplit := hs.sum_add_tsum_nat_add L
  rw [mul_add, ← hsplit, mul_add]
  have hbase : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 *
      fermiDyadicPronicWeight 0 b) ≤ sinePacketProfile L 0 ^ 2 := by
    rw [packet_normalized_head hLN hb (Nat.zero_le _)]
    have := weight_ceiling 0 b hb0
    nlinarith [sq_nonneg (sinePacketProfile L 0)]
  have hhead : (b : ℝ) ^ 2 * ∑ k ∈ range L, fermiNormalizedDyadicJump N c b k ^ 2 *
      fermiDyadicPronicWeight (k + 1) b ≤
      ∑ k ∈ range L, (sinePacketProfile L k - sinePacketProfile L (k + 1)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkL := mem_range.mp hk
    rw [hxy]
    simp only [y]
    rw [packet_normalized_head hLN hb hkL.le, packet_normalized_head hLN hb hkL]
    have := weight_ceiling (k + 1) b hb0
    nlinarith [sq_nonneg (sinePacketProfile L k - sinePacketProfile L (k + 1))]
  have htail : (b : ℝ) ^ 2 * ∑' j : ℕ, fermiNormalizedDyadicJump N c b (j + L) ^ 2 *
      fermiDyadicPronicWeight (j + L + 1) b ≤ sinePacketProfile L L ^ 2 / 3 := by
    rw [← tsum_mul_left, ← htail_val]
    refine Summable.tsum_le_tsum (fun j => ?_) (((summable_nat_add_iff L).mpr hs).mul_left _)
      hsq_tail
    rw [← hxtail_sq j]
    have := weight_ceiling (j + L + 1) b hb0
    nlinarith [sq_nonneg (fermiNormalizedDyadicJump N c b (j + L))]
  have henergy := sinePacketProfile_dirichlet_energy L
  have hL2 : 0 ≤ sinePacketProfile L L ^ 2 := sq_nonneg _
  linarith

/-- **Sine-packet lower bound.** At every horizon `N ≥ 2^L`, `L ≥ 2`, the packet satisfies
`P ≥ (1 - 4/(L+2))/λ · Q_all` with `λ = 2 - 2 cos(π/(L+2))`, and `Q_all > 0`. -/
theorem sinePacket_allBoundary_ratio {L N : ℕ} (hL : 2 ≤ L) (hLN : 2 ^ L ≤ N) :
    0 < fermiAllBoundaryPronicEnergy N (fermiDyadicSinePacket L) ∧
      (1 - 4 / ((L : ℝ) + 2)) / (2 - 2 * Real.cos (sinePacketAngle L)) *
          fermiAllBoundaryPronicEnergy N (fermiDyadicSinePacket L) ≤
        sieveTotalPronicEnergy N (fermiDyadicSinePacket L) := by
  set c := fermiDyadicSinePacket L
  set lam := 2 - 2 * Real.cos (sinePacketAngle L)
  set S := ∑ k ∈ range (L + 1), sinePacketProfile L k ^ 2
  have hS : S = ((L : ℝ) + 2) / 2 := sinePacketProfile_mass L
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlam : 0 < lam := by
    have hθ := angle_pos L
    have hθπ : sinePacketAngle L ≤ Real.pi := by
      unfold sinePacketAngle
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ hθ
    rw [Real.cos_zero] at this
    simp only [lam]; linarith
  obtain ⟨hP, hPs⟩ := sieveTotalPronicEnergy_eq_sum_rays N c
  obtain ⟨hQ, hQs⟩ := fermiAllBoundaryPronicEnergy_eq_sum_rays N c
  have hodd (j : ℕ) : Odd (2 * j + 1) := ⟨j, rfl⟩
  have hQnn (j : ℕ) : 0 ≤ fermiRayAllBoundaryEnergy N c (2 * j + 1) := by
    unfold fermiRayAllBoundaryEnergy
    have hs := (fermiRay_weighted_summable N c (by omega : 0 < 2 * j + 1)).2
    have : 0 ≤ ∑' k : ℕ, fermiNormalizedDyadicJump N c (2 * j + 1) k ^ 2 *
        fermiDyadicPronicWeight (k + 1) (2 * j + 1) :=
      tsum_nonneg fun k => mul_nonneg (sq_nonneg _)
        (by unfold fermiDyadicPronicWeight; positivity)
    have : 0 ≤ fermiNormalizedDyadicSieve N c (2 * j + 1) 0 ^ 2 *
        fermiDyadicPronicWeight 0 (2 * j + 1) :=
      mul_nonneg (sq_nonneg _) (by unfold fermiDyadicPronicWeight; positivity)
    linarith
  constructor
  · -- the base ray carries the positive base value
    rw [hQ]
    have h0 : 0 < fermiRayAllBoundaryEnergy N c 1 := by
      unfold fermiRayAllBoundaryEnergy
      have hv : fermiNormalizedDyadicSieve N c 1 0 = sinePacketProfile L 0 :=
        packet_normalized_head hLN odd_one (Nat.zero_le _)
      have hw : 0 < fermiDyadicPronicWeight 0 1 := by
        unfold fermiDyadicPronicWeight pronicSeq; norm_num
      have hp := profile_zero_pos L
      have : 0 ≤ ∑' k : ℕ, fermiNormalizedDyadicJump N c 1 k ^ 2 *
          fermiDyadicPronicWeight (k + 1) 1 :=
        tsum_nonneg fun k => mul_nonneg (sq_nonneg _)
          (by unfold fermiDyadicPronicWeight; positivity)
      rw [hv]
      have : 0 < sinePacketProfile L 0 ^ 2 * fermiDyadicPronicWeight 0 1 := by positivity
      linarith
    have := hQs.le_tsum 0 (fun j _ => hQnn j)
    simp only [mul_zero, zero_add] at this
    linarith
  · rw [hP, hQ, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hQs.mul_left _) hPs
    have hb2 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hPj := fermiRaySieveEnergy_sinePacket_ge hLN (hodd j)
    have hQj := fermiRayAllBoundaryEnergy_sinePacket_le hLN (hodd j)
    have hκ : (1 - 4 / ((L : ℝ) + 2)) / lam = (S - 2) / (lam * S) := by
      rw [hS]; field_simp; ring
    rw [hκ]
    have hSpos : 0 < S := by rw [hS]; positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hS2 : 0 ≤ S - 2 := by rw [hS]; linarith
    rw [← mul_le_mul_iff_of_pos_left hb2]
    nlinarith [mul_le_mul_of_nonneg_left hQj hS2, mul_le_mul_of_nonneg_left hPj
      (by positivity : (0 : ℝ) ≤ lam * S), hQnn j]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
