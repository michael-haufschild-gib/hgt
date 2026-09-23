import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightGreen
import GaloisForLFunctions.RHTower.DeningerKotheComplete

/-!
# Forms, Green energy, and the Lagrangian graph of the prime-log height source

The reflected pairing `⟨a,b⟩₀ = ∑_m a_m b_{-m}` is continuous for the zeroth seminorm, and
twisting it by the generator gives the alternating form `Ψ(a,b) = i ∑_m ℓ(m) a_m b_{-m}`,
continuous for the pair `(p₁, p₀)`.

Pairing a vector with the odd Hodge sign of its star produces the Green energy

`Ψ(a, W(a*)) = ∑_m |ℓ(m)| |a_m|² ≥ 0`,

which vanishes exactly on the zero vector of the sector of vanishing total character.  On the
double of that sector the graph of the modulus is closed and equals its own symplectic
annihilator: it is a closed Lagrangian relation whose Green form is that energy.

* `deningerPairing`, `deningerPsi` : the two forms and their continuity bounds.
* `deningerHeightEnergy`, `deningerPsi_hodgeStar` : **the Green energy identity.**
* `deningerLagrangian_isotropic`, `deningerLagrangian_maximal`,
  `deningerLagrangian_closed` : **the closed Lagrangian graph.**
-/

namespace RHTower

open GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The reflected pairing -/

private theorem deningerPairing_summable (a b : DeningerHeightKothe) :
    Summable fun m : DeningerPrimeLattice =>
      (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (-m) := by
  refine Summable.of_norm_bounded
    ((deningerHeightKothe_summable_norm a).mul_right (deningerHeightSeminorm 0 b))
    fun m => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (deningerHeightKothe_norm_le b (-m)) (norm_nonneg _)

/-- **The reflected pairing** `⟨a,b⟩₀ = ∑_m a_m b_{-m}`. -/
def deningerPairing (a b : DeningerHeightKothe) : ℂ :=
  ∑' m, (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (-m)

/-- The reflected pairing is bounded by the product of the zeroth seminorms. -/
theorem deningerPairing_norm_le (a b : DeningerHeightKothe) :
    ‖deningerPairing a b‖ ≤ deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b := by
  have hsummable : Summable fun m : DeningerPrimeLattice =>
      ‖(a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (-m)‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      ((deningerHeightKothe_summable_norm a).mul_right (deningerHeightSeminorm 0 b))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (deningerHeightKothe_norm_le b (-m)) (norm_nonneg _)
  refine le_trans (norm_tsum_le_tsum_norm hsummable) ?_
  have hle : ∑' m : DeningerPrimeLattice,
      ‖(a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (-m)‖
      ≤ ∑' m : DeningerPrimeLattice,
          ‖(a : DeningerPrimeLattice → ℂ) m‖ * deningerHeightSeminorm 0 b := by
    refine Summable.tsum_le_tsum (fun m => ?_) hsummable
      ((deningerHeightKothe_summable_norm a).mul_right (deningerHeightSeminorm 0 b))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (deningerHeightKothe_norm_le b (-m)) (norm_nonneg _)
  refine le_trans hle (le_of_eq ?_)
  rw [Summable.tsum_mul_right _ (deningerHeightKothe_summable_norm a),
    deningerHeightSeminorm_zero_eq b, deningerHeightSeminorm_zero_eq a]

/-- The reflected pairing is symmetric. -/
theorem deningerPairing_comm (a b : DeningerHeightKothe) :
    deningerPairing a b = deningerPairing b a := by
  rw [deningerPairing, deningerPairing]
  rw [← (Equiv.neg DeningerPrimeLattice).tsum_eq
    (fun m : DeningerPrimeLattice =>
      (b : DeningerPrimeLattice → ℂ) m * (a : DeningerPrimeLattice → ℂ) (-m))]
  refine tsum_congr fun m => ?_
  show (a : DeningerPrimeLattice → ℂ) m * (b : DeningerPrimeLattice → ℂ) (-m)
      = (b : DeningerPrimeLattice → ℂ) (-m) * (a : DeningerPrimeLattice → ℂ) (- -m)
  rw [neg_neg, mul_comm]

/-- The reflected pairing against a basis vector reads off a reflected coordinate. -/
theorem deningerPairing_delta (n : DeningerPrimeLattice) (b : DeningerHeightKothe) :
    deningerPairing (deningerKotheDelta deningerHeightKotheData n) b
      = (b : DeningerPrimeLattice → ℂ) (-n) := by
  classical
  rw [deningerPairing, tsum_eq_single n]
  · rw [deningerKotheDelta_coe]
    simp
  · intro m hm
    have hzero : ((deningerKotheDelta deningerHeightKotheData n : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) m = 0 := by
      rw [deningerKotheDelta_coe]
      exact Pi.single_eq_of_ne hm 1
    rw [hzero, zero_mul]

/-! ## The alternating form -/

/-- **The alternating form** `Ψ(a,b) = i ∑_m ℓ(m) a_m b_{-m}`. -/
def deningerPsi (a b : DeningerHeightKothe) : ℂ :=
  Complex.I * deningerPairing (deningerGenerator a) b

/-- The alternating form is bounded by `p₁(a) p₀(b)`. -/
theorem deningerPsi_norm_le (a b : DeningerHeightKothe) :
    ‖deningerPsi a b‖ ≤ deningerHeightSeminorm 1 a * deningerHeightSeminorm 0 b := by
  rw [deningerPsi, norm_mul, Complex.norm_I, one_mul]
  refine le_trans (deningerPairing_norm_le (deningerGenerator a) b) ?_
  have hgen : deningerHeightSeminorm 0 (deningerGenerator a)
      ≤ deningerHeightSeminorm 1 a := by
    have h := deningerHeightSeminorm_generator_le 0 a
    rwa [Nat.zero_add] at h
  exact mul_le_mul_of_nonneg_right hgen (apply_nonneg _ _)

/-- **The form `Ψ` is alternating.** -/
theorem deningerPsi_antisymm (a b : DeningerHeightKothe) :
    deningerPsi a b = -deningerPsi b a := by
  have hsum : deningerPairing (deningerGenerator a) b
      = -deningerPairing (deningerGenerator b) a := by
    rw [deningerPairing, deningerPairing, ← tsum_neg]
    rw [← (Equiv.neg DeningerPrimeLattice).tsum_eq
      (fun m : DeningerPrimeLattice =>
        -(((deningerGenerator b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m *
          (a : DeningerPrimeLattice → ℂ) (-m)))]
    refine tsum_congr fun m => ?_
    show ((deningerGenerator a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m *
        (b : DeningerPrimeLattice → ℂ) (-m)
        = -(((deningerGenerator b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) (-m) *
            (a : DeningerPrimeLattice → ℂ) (- -m))
    rw [deningerGenerator_coe, deningerGenerator_coe, neg_neg, deningerFreq_neg]
    push_cast
    ring
  rw [deningerPsi, deningerPsi, hsum]
  ring

/-! ## The Green energy -/

private theorem deningerHeightEnergy_summable (a : DeningerHeightKothe) :
    Summable fun m : DeningerPrimeLattice =>
      |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) := by
  refine Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun m => ?_)
    ((a.2 1).mul_right (deningerHeightSeminorm 0 a))
  show |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ)
      ≤ deningerHeightKotheData.w 1 m * ‖(a : DeningerPrimeLattice → ℂ) m‖ *
        deningerHeightSeminorm 0 a
  rw [deningerHeightKotheData_w, pow_one]
  have h1 : |deningerFreq m| ≤ deningerHeight m := abs_deningerFreq_le_height m
  have h2 : ‖(a : DeningerPrimeLattice → ℂ) m‖ ≤ deningerHeightSeminorm 0 a :=
    deningerHeightKothe_norm_le a m
  have hnn : (0 : ℝ) ≤ ‖(a : DeningerPrimeLattice → ℂ) m‖ := norm_nonneg _
  calc |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ)
      = |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ *
          ‖(a : DeningerPrimeLattice → ℂ) m‖ := by ring
    _ ≤ deningerHeight m * ‖(a : DeningerPrimeLattice → ℂ) m‖ *
          deningerHeightSeminorm 0 a := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hnn) h2 hnn ?_
        exact mul_nonneg (deningerHeight_pos m).le hnn

/-- **The Green energy** `E(a) = ∑_m |ℓ(m)| |a_m|²`. -/
def deningerHeightEnergy (a : DeningerHeightKothe) : ℝ :=
  ∑' m, |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ)

theorem deningerHeightEnergy_nonneg (a : DeningerHeightKothe) : 0 ≤ deningerHeightEnergy a :=
  tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)

/-- **The Green energy is the pairing of a vector with the Hodge sign of its star.** -/
theorem deningerPsi_hodgeStar (a : DeningerHeightKothe) :
    deningerPsi a (deningerHodgeSign (deningerHeightStar a))
      = ((deningerHeightEnergy a : ℝ) : ℂ) := by
  have hterm : ∀ m : DeningerPrimeLattice,
      ((deningerGenerator a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m *
        ((deningerHodgeSign (deningerHeightStar a) : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) (-m)
        = -Complex.I * ((|deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro m
    rw [deningerGenerator_coe, deningerHodgeSign_coe, deningerHeightStar_coe]
    rw [neg_neg]
    by_cases hm : deningerFreq m = 0
    · have habs : |deningerFreq m| = 0 := by rw [hm, abs_zero]
      rw [habs, hm]
      push_cast
      ring
    · have hsign : deningerFreq m * deningerSign (-m) = -|deningerFreq m| := by
        have hneg : deningerFreq (-m) = -deningerFreq m := deningerFreq_neg m
        rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
        · have hpos : 0 < deningerFreq (-m) := by rw [hneg]; linarith
          rw [deningerSign_of_pos hpos, abs_of_neg h]
          ring
        · exact absurd h hm
        · have hneglt : deningerFreq (-m) < 0 := by rw [hneg]; linarith
          rw [deningerSign_of_neg hneglt, abs_of_pos h]
          ring
      have hmul : (a : DeningerPrimeLattice → ℂ) m *
          (starRingEnd ℂ) ((a : DeningerPrimeLattice → ℂ) m)
          = ((‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc ((deningerFreq m : ℝ) : ℂ) * (a : DeningerPrimeLattice → ℂ) m *
            (Complex.I * ((deningerSign (-m) : ℝ) : ℂ) *
              (starRingEnd ℂ) ((a : DeningerPrimeLattice → ℂ) m))
          = Complex.I * ((deningerFreq m * deningerSign (-m) : ℝ) : ℂ) *
              ((a : DeningerPrimeLattice → ℂ) m *
                (starRingEnd ℂ) ((a : DeningerPrimeLattice → ℂ) m)) := by
            push_cast; ring
        _ = -Complex.I *
              ((|deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
            rw [hsign, hmul]
            push_cast
            ring
  have hsumC : Summable fun m : DeningerPrimeLattice =>
      ((|deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) : ℝ) : ℂ) :=
    Complex.ofRealCLM.summable (deningerHeightEnergy_summable a)
  rw [deningerPsi, deningerPairing, tsum_congr hterm,
    Summable.tsum_mul_left _ hsumC, deningerHeightEnergy, Complex.ofReal_tsum,
    ← mul_assoc]
  have hI : Complex.I * -Complex.I = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [hI, one_mul]

/-- **The Green energy vanishes exactly at the origin of the zero-character sector.** -/
theorem deningerHeightEnergy_eq_zero_iff (a : DeningerHeightKothe)
    (ha : a ∈ deningerHeightKotheZero) :
    deningerHeightEnergy a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have ha0 : (a : DeningerPrimeLattice → ℂ) 0 = 0 := ha
    have hterm : ∀ m : DeningerPrimeLattice,
        |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) = 0 := by
      intro m
      have hsum := deningerHeightEnergy_summable a
      have hle := hsum.le_tsum m (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      have hnn : 0 ≤ |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) :=
        mul_nonneg (abs_nonneg _) (sq_nonneg _)
      have : |deningerFreq m| * ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) ≤ 0 := by
        rw [← h]
        exact hle
      linarith
    ext m
    show (a : DeningerPrimeLattice → ℂ) m = 0
    by_cases hm : m = 0
    · subst hm; exact ha0
    · have hfreq : |deningerFreq m| ≠ 0 := abs_ne_zero.mpr (deningerFreq_ne_zero hm)
      have := hterm m
      have hsq : ‖(a : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) = 0 :=
        (mul_eq_zero.mp this).resolve_left hfreq
      have hnorm : ‖(a : DeningerPrimeLattice → ℂ) m‖ = 0 := by
        nlinarith [norm_nonneg ((a : DeningerPrimeLattice → ℂ) m)]
      exact norm_eq_zero.mp hnorm
  · intro h
    rw [h, deningerHeightEnergy]
    have hzero : ∀ m : DeningerPrimeLattice, |deningerFreq m| *
        ‖((0 : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) = 0 := by
      intro m
      show |deningerFreq m| * ‖(0 : DeningerPrimeLattice → ℂ) m‖ ^ (2 : ℕ) = 0
      simp
    rw [tsum_congr hzero, tsum_zero]

/-! ## The Lagrangian graph of the modulus -/

/-- The modulus is symmetric for the reflected pairing. -/
theorem deningerPairing_modulus_symm (a b : DeningerHeightKothe) :
    deningerPairing (deningerModulus a) b = deningerPairing a (deningerModulus b) := by
  rw [deningerPairing, deningerPairing]
  refine tsum_congr fun m => ?_
  rw [deningerModulus_coe, deningerModulus_coe, deningerFreq_neg, abs_neg]
  ring

/-- **The graph of the modulus is isotropic** for the symplectic form
`Ω((x,u),(y,v)) = ⟨u,y⟩₀ - ⟨v,x⟩₀`. -/
theorem deningerLagrangian_isotropic (x y : DeningerHeightKothe) :
    deningerPairing (deningerModulus x) y - deningerPairing (deningerModulus y) x = 0 := by
  rw [deningerPairing_modulus_symm x y, deningerPairing_comm x (deningerModulus y)]
  ring

/-- **The graph of the modulus is its own symplectic annihilator** inside the double of the
zero-character sector. -/
theorem deningerLagrangian_maximal (y v : DeningerHeightKothe)
    (hv : v ∈ deningerHeightKotheZero)
    (h : ∀ x : DeningerHeightKothe,
      deningerPairing (deningerModulus x) y - deningerPairing v x = 0) :
    v = deningerModulus y := by
  have hv0 : (v : DeningerPrimeLattice → ℂ) 0 = 0 := hv
  ext m
  by_cases hm : m = 0
  · subst hm
    rw [hv0, deningerModulus_coe]
    simp
  · have hdelta := h (deningerKotheDelta deningerHeightKotheData (-m))
    have e1 : deningerPairing (deningerModulus
        (deningerKotheDelta deningerHeightKotheData (-m))) y
        = ((deningerModulus y : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m := by
      rw [deningerPairing_modulus_symm, deningerPairing_delta, neg_neg]
    have e2 : deningerPairing v (deningerKotheDelta deningerHeightKotheData (-m))
        = (v : DeningerPrimeLattice → ℂ) m := by
      rw [deningerPairing_comm, deningerPairing_delta, neg_neg]
    rw [e1, e2] at hdelta
    exact (sub_eq_zero.mp hdelta).symm

/-- **The graph of the modulus is closed**: a sequence of graph points converging in every
seminorm has its limit on the graph. -/
theorem deningerLagrangian_closed (x : ℕ → DeningerHeightKothe) (y v : DeningerHeightKothe)
    (hx : DeningerKotheTendsto deningerHeightKotheData x y)
    (hAx : DeningerKotheTendsto deningerHeightKotheData
      (fun i => deningerModulus (x i)) v) :
    v = deningerModulus y := by
  ext m
  have h1 : Tendsto (fun i => ((deningerModulus (x i) : DeningerHeightKothe) :
      DeningerPrimeLattice → ℂ) m) atTop
      (nhds ((v : DeningerPrimeLattice → ℂ) m)) := hAx.coord m
  have h2 : Tendsto (fun i => ((|deningerFreq m| : ℝ) : ℂ) *
      ((x i : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m) atTop
      (nhds (((|deningerFreq m| : ℝ) : ℂ) * (y : DeningerPrimeLattice → ℂ) m)) :=
    (hx.coord m).const_mul _
  have h1' : Tendsto (fun i => ((|deningerFreq m| : ℝ) : ℂ) *
      ((x i : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m) atTop
      (nhds ((v : DeningerPrimeLattice → ℂ) m)) := by
    refine h1.congr fun i => ?_
    rw [deningerModulus_coe]
  have := tendsto_nhds_unique h1' h2
  rw [this, deningerModulus_coe]

end

end RHTower
