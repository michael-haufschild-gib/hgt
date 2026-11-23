import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrowdedCut

/-! # Number of packet tests needed at an exponentially small signal -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

private theorem absorb {c : ℝ} (hc : 1 ≤ c) {L : ℕ} (hL : 0 < L) :
    c ≤ c^L := le_self_pow₀ hc hL.ne'

/-- A geometric signal cutoff permits a geometric guard tolerance and
a geometric number of packet tests. The factor of L accounts for the
duration in the Hamiltonian perturbation estimate. -/
theorem geometric_packet_scale {b κ : ℝ} (hb : 0 < b) (hκ : 0 < κ) :
    ∃ r d g : ℝ, 0 < r ∧ 0 < d ∧ 0 < g ∧ g ≤ 1 ∧ ∃ k : ℕ, 0 < k ∧
      ∀ L : ℕ, 0 < L → 3*r^L ≤ b^L ∧ 72*(L:ℝ)*g^L ≤ d^L ∧ d^L < r^L ∧
        ∀ v : ℝ, ((k^L*k^L:ℕ):ℝ)*(r^L-d^L)*v ≤
          2*Real.sqrt (k^L*k^L:ℕ)+(k^L*k^L:ℕ)*d^L → v<κ := by
  let r := min b 1/3
  have hr : 0 < r := div_pos (lt_min hb zero_lt_one) (by norm_num)
  have hr₁ : r ≤ 1 := by dsimp only [r]; linarith only [min_le_right b (1:ℝ)]
  let c := min (1/4:ℝ) (κ/8)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc₁ : c ≤ 1 := (min_le_left ..).trans (by norm_num)
  let d := r*c
  have hd : 0 < d := mul_pos hr hc
  have hdc : d ≤ 1 := (mul_le_of_le_one_right hr.le hc₁).trans hr₁
  let g := d/144
  have hg : 0 < g := div_pos hd (by norm_num)
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (8/κ)/r)
  have hkr := (div_lt_iff₀ hr).mp hk
  have hkr₁ : 1 ≤ (k:ℝ)*r := (le_max_left ..).trans hkr.le
  have hkr₂ : 8/κ < (k:ℝ)*r := (le_max_right ..).trans_lt hkr
  have hkpos : 0 < (k:ℝ) := (div_pos (zero_lt_one.trans_le (le_max_left ..)) hr).trans hk
  refine ⟨r,d,g,hr,hd,hg,(div_le_self hd.le (by norm_num)).trans hdc,k,Nat.cast_pos.mp hkpos,?_⟩
  intro L hL
  have hbr : 3*r^L ≤ b^L := by
    calc 3*r^L ≤ 3^L*r^L := mul_le_mul_of_nonneg_right (absorb (by norm_num) hL) (pow_pos hr _).le
         _ = (3*r)^L := (mul_pow ..).symm
         _ ≤ _ := pow_le_pow_left₀ (by positivity) (by dsimp [r]; linarith only [min_le_left b (1:ℝ)]) _
  have hLG : 72*(L:ℝ)*g^L ≤ d^L := by
    have htwo : (L:ℝ) ≤ 2^L := by exact_mod_cast (Nat.lt_two_pow_self : L < 2^L).le
    have hcst := mul_le_mul (absorb (by norm_num : (1:ℝ)≤72) hL) htwo
      (Nat.cast_nonneg _) (by positivity)
    calc 72*(L:ℝ)*g^L ≤ (72^L*2^L)*g^L := mul_le_mul_of_nonneg_right hcst (pow_pos hg _).le
         _ = (72*2*g)^L := by rw [mul_pow,mul_pow]
         _ = _ := by rw [show 72*2*g=d by dsimp only [g]; ring]
  have hpow : c^L ≤ c := pow_le_of_le_one hc.le hc₁ hL.ne'
  have hδ₁ : d^L ≤ r^L/4 := by
    rw [show d^L=r^L*c^L from mul_pow ..]
    exact (mul_le_mul_of_nonneg_left (hpow.trans (min_le_left ..)) (pow_pos hr _).le).trans_eq (by ring)
  have hδ₂ : d^L ≤ r^L*κ/8 := by
    rw [show d^L=r^L*c^L from mul_pow ..]
    exact (mul_le_mul_of_nonneg_left (hpow.trans (min_le_right ..)) (pow_pos hr _).le).trans_eq (by ring)
  refine ⟨hbr,hLG,hδ₁.trans_lt (by linarith only [pow_pos hr L]),?_⟩
  apply overlap_of_square_packets (pow_pos hr _) hκ hδ₁ hδ₂
  have hh := (div_lt_iff₀ hκ).mp (hkr₂.trans_le (absorb hkr₁ hL))
  simpa only [mul_pow,Nat.cast_pow,mul_assoc] using hh

#print axioms geometric_packet_scale
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
