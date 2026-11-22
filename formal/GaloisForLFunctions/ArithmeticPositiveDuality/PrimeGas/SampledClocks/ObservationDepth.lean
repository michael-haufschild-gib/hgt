import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.RepeatedObservations

/-!
# Exact angular resolution of a dyadic clock prefix

Up to an initial angular aperture of two thirds of π, each extra squaring
halves the accepted arc. A cubic phase already prevents this law after
two observations for every larger aperture up to π.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

/-- Squared chord at angular distance θ from the identity. -/
def aperture (θ : ℝ) : ℝ := 2 - 2 * Real.cos θ

private theorem aperture_nonneg (θ : ℝ) : 0 ≤ aperture θ := by
  unfold aperture
  linarith only [Real.cos_le_one θ]

private theorem aperture_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi) :
    aperture u ≤ aperture v := by
  unfold aperture
  linarith only [Real.cos_le_cos_of_nonneg_of_le_pi hu hv huv]

private theorem aperture_double (u : ℝ) : aperture (2*u) = aperture u*(4-aperture u) := by
  rw [aperture,Real.cos_two_mul]
  unfold aperture
  ring

private theorem aperture_third : aperture (Real.pi/3) = 1 := by
  rw [aperture,Real.cos_pi_div_three]
  norm_num

private theorem aperture_two_thirds : aperture (2*Real.pi/3) = 3 := by
  rw [aperture,HTGeometry.cos_two_pi_div_three]
  norm_num

/-- On the first accepted arc, comparison with the doubled smaller chord has only one branch. -/
private theorem invert_chord {y b : ℝ} (hy : y < 3) (hb : b ≤ 1) :
    y*(4-y) < b*(4-b) ↔ y < b := by
  have hp : 0 < 4-b-y := by linarith only [hy,hb]
  constructor
  · intro h
    by_contra! hby
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hby) hp.le]
  · intro h
    nlinarith only [mul_pos (sub_pos.mpr h) hp]

private theorem split_times (z : Circle) (n : ℕ) (a : ℝ) :
    (∀ k : ℕ, k ≤ n+1 → chordSq (z^(2^k : ℕ)) < a) ↔
      chordSq z < a ∧ ∀ k : ℕ, k ≤ n → chordSq ((z^2)^(2^k : ℕ)) < a := by
  have step (k : ℕ) : z^(2^(k+1) : ℕ) = (z^2)^(2^k : ℕ) := by rw [pow_succ',pow_mul]
  constructor
  · intro h
    refine ⟨by simpa only [pow_zero,pow_one] using h 0 (Nat.zero_le _),?_⟩
    intro k hk
    exact step k ▸ h (k+1) (Nat.succ_le_succ hk)
  · rintro ⟨h0,hs⟩ (_ | k) hk
    · simpa only [pow_zero,pow_one] using h0
    · rw [step]
      exact hs k (Nat.le_of_succ_le_succ hk)

/-- At times one through the Nth doubling, the surviving arc has aperture θ/2ᴺ. -/
theorem finite_angular_resolution (θ : Set.Icc 0 (2*Real.pi/3)) (N : ℕ) (z : Circle) :
    (∀ k : ℕ, k ≤ N → chordSq (z^(2^k : ℕ)) < aperture θ.val) ↔
      chordSq z < aperture (θ.val / (2:ℝ)^N) := by
  induction N generalizing z with
  | zero => simp
  | succ n ih =>
    let u := θ.val / (2:ℝ)^n
    have hp : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hu : 0 ≤ u := div_nonneg θ.property.1 (zero_le_one.trans hp)
    have hul : u ≤ θ.val := div_le_self θ.property.1 hp
    have hπ := Real.pi_pos
    have hθ := θ.property.2
    have hl : aperture (u/2) ≤ aperture θ.val :=
      aperture_mono (by linarith only [hu]) (by linarith only [hu,hul]) (by linarith only [hπ,hθ])
    have hb : aperture (u/2) ≤ 1 := by
      rw [← aperture_third]
      exact aperture_mono (by linarith only [hu]) (by linarith only [hul,hθ]) (by linarith only [hπ])
    have hmax : aperture θ.val ≤ 3 :=
      (aperture_mono θ.property.1 hθ (by linarith only [hπ])).trans_eq aperture_two_thirds
    have ha : aperture u = aperture (u/2)*(4-aperture (u/2)) := by
      exact (congrArg aperture (show u = 2*(u/2) by ring)).trans (aperture_double (u/2))
    have hdiv : θ.val / (2:ℝ)^(n+1) = u/2 := by rw [pow_succ,div_mul_eq_div_div]
    rw [split_times,ih,chord_square,hdiv]
    change (chordSq z < aperture θ.val ∧ chordSq z*(4-chordSq z) < aperture u) ↔
      chordSq z < aperture (u/2)
    rw [ha]
    constructor
    · rintro ⟨hy,hs⟩
      exact (invert_chord (hy.trans_le hmax) hb).mp hs
    · intro hy
      have hstart := hy.trans_le hl
      exact ⟨hstart,(invert_chord (hstart.trans_le hmax) hb).mpr hy⟩

/-- Two readings suffice to witness failure of angular halving above 2π/3. -/
theorem angular_halving_iff (θ : Set.Icc 0 Real.pi) :
    (∀ z : Circle, (∀ k : ℕ, k ≤ 1 → chordSq (z^(2^k : ℕ)) < aperture θ.val) ↔
      chordSq z < aperture (θ.val/2)) ↔ θ.val ≤ 2*Real.pi/3 := by
  constructor
  · intro h
    by_contra! hθ
    obtain ⟨z,_,hz⟩ := cubic_sharp
    have hπ := Real.pi_pos
    have hlo : 3 < aperture θ.val := by
      have hcos := Real.strictAntiOn_cos (show 2*Real.pi/3 ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith) θ.property hθ
      rw [HTGeometry.cos_two_pi_div_three] at hcos
      unfold aperture
      linarith only [hcos]
    have hhalf : aperture (θ.val/2) ≤ 2 := by
      have ha := aperture_mono (show 0 ≤ θ.val/2 by linarith only [θ.property.1])
        (show θ.val/2 ≤ Real.pi/2 by linarith only [θ.property.2]) (by linarith only [hπ])
      simpa only [aperture,Real.cos_pi_div_two,mul_zero,sub_zero] using ha
    have hb := (h z).mp fun k _ => (hz k).trans_lt hlo
    have hz0 : chordSq z = 3 := by simpa only [pow_zero,pow_one] using hz 0
    linarith only [hz0,hb,hhalf]
  · intro h z
    simpa only [pow_one] using finite_angular_resolution (⟨θ.val,θ.property.1,h⟩ : Set.Icc 0 (2*Real.pi/3)) 1 z

/-- The finite observation protocol has this same exact effective aperture on every network edge. -/
theorem Network.prefix_angular_resolution {I E : Type*} (G : Network I E) (θ : Set.Icc 0 (2*Real.pi/3))
    (N : ℕ) (x : I → ℕ+) : G.Prefix (Real.sqrt (aperture θ.val)) (N+1) x ↔
      ∀ e, chordSq (G.phase e x) < aperture (θ.val / (2:ℝ)^N) := by
  have hc (w : Circle) : dist w 1 < Real.sqrt (aperture θ.val) ↔ chordSq w < aperture θ.val := by
    rw [← sq_lt_sq₀ dist_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (aperture_nonneg _)]
    rfl
  constructor
  · intro h e
    apply (finite_angular_resolution θ N (G.phase e x)).mp
    intro k hk
    apply (hc _).mp
    simpa only [G.multiple_phase] using h ⟨k,Nat.lt_succ_of_le hk⟩ e
  · intro h k e
    rw [G.multiple_phase,hc]
    exact (finite_angular_resolution θ N (G.phase e x)).mpr (h e) k.val (Nat.le_of_lt_succ k.isLt)

#print axioms finite_angular_resolution
#print axioms angular_halving_iff
#print axioms Network.prefix_angular_resolution

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
