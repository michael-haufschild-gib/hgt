import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedSpatialMellinL2
import GaloisForLFunctions.RHTower.Sieve.MaynardAdditiveEnergy

/-!
# Maynard spatial fourth moment and additive energy

This module formalizes the analytic content of Maynard's equation (112).
Squaring a selected-cell Mellin packet produces its exact additive
convolution.  The weighted spatial `L²` theorem applied to that square gives
an `L⁴` estimate controlled by Maynard's integer-cell additive energy
`R*`.  Unit-cell averaging, fixed-ambient physical transport, and the
fourth-moment superlevel estimate are all closed here.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section
namespace RHTower.Sieve

/-- Additive-convolution coefficient of the square of a discrete Mellin
packet. -/
def maynardAdditiveSquareCoeff
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (S.product S).filter (fun p => p.1 + p.2 = k), a p.1 * a p.2

/-- Pair-sum-fibre presentation of additive energy on nonnegative cells. -/
def maynardNatRStar (S : Finset ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * N),
    ((S.product S).filter (fun p => p.1 + p.2 = k)).card ^ 2

/-- Ordered additive quadruples in natural frequency cells, grouped as two
ordered pairs. -/
def maynardNatAdditiveQuadruples (S : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((S.product S).product (S.product S)).filter fun q =>
    q.1.1 + q.1.2 = q.2.1 + q.2.2

/-- Natural frequency cells embedded in the integer cells used by Maynard's
existing `R*` interface. -/
def maynardNatToIntEmbedding : ℕ ↪ ℤ where
  toFun n := (n : ℤ)
  inj' := by
    intro m n h
    apply Int.ofNat.inj
    exact h

/-- Reassociation and coordinatewise natural-to-integer embedding for
additive quadruples. -/
def maynardNatQuadToIntEmbedding :
    ((ℕ × ℕ) × (ℕ × ℕ)) ↪ (ℤ × (ℤ × (ℤ × ℤ))) where
  toFun q := ((q.1.1 : ℤ), ((q.1.2 : ℤ), ((q.2.1 : ℤ), (q.2.2 : ℤ))))
  inj' := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    simp only [Prod.mk.injEq, Int.ofNat_inj] at h
    simp only [h]

/-- Casting natural additive quadruples gives exactly the integer additive
quadruples on the cast frequency set. -/
theorem maynardAdditiveQuadruples_map_natCast (S : Finset ℕ) :
    maynardAdditiveQuadruples (S.map maynardNatToIntEmbedding) =
      (maynardNatAdditiveQuadruples S).map maynardNatQuadToIntEmbedding := by
  classical
  ext z
  simp [maynardAdditiveQuadruples, maynardNatAdditiveQuadruples,
    maynardNatToIntEmbedding, maynardNatQuadToIntEmbedding]
  constructor
  · rintro ⟨⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩, ⟨c, hc, hcz⟩,
        ⟨d, hd, hdz⟩⟩, hadd⟩
    refine ⟨a, b, c, d, ⟨⟨⟨ha, hb⟩, hc, hd⟩, ?_⟩, ?_⟩
    · have hcast : (a : ℤ) + (b : ℤ) = (c : ℤ) + (d : ℤ) := by
        simpa only [haz, hbz, hcz, hdz] using hadd
      exact_mod_cast hcast
    · exact Prod.ext haz (Prod.ext hbz (Prod.ext hcz hdz))
  · rintro ⟨a, b, c, d, ⟨⟨⟨ha, hb⟩, hc, hd⟩, hadd⟩, rfl⟩
    exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩,
      ⟨d, hd, rfl⟩⟩, by
        have hcast : (a : ℤ) + (b : ℤ) = (c : ℤ) + (d : ℤ) := by
          exact_mod_cast hadd
        simpa using hcast⟩

/-- Pair-sum-fibre energy equals the existing quadruple-count definition of
`R*` after the canonical embedding into integer cells. -/
theorem maynardNatRStar_eq_maynardRStar_map
    {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.range N) :
    maynardNatRStar S N = maynardRStar (S.map maynardNatToIntEmbedding) := by
  classical
  let P : Finset (ℕ × ℕ) := S.product S
  let Q : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (P.product P).filter fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2
  have hfiber : ∀ k : ℕ,
      (Q.filter fun q => q.1.1 + q.1.2 = k).card =
        ((P.filter fun p => p.1 + p.2 = k).card) ^ 2 := by
    intro k
    have hset : (Q.filter fun q => q.1.1 + q.1.2 = k) =
        (P.filter fun p => p.1 + p.2 = k).product
          (P.filter fun p => p.1 + p.2 = k) := by
      ext q
      simp only [Q, Finset.mem_filter]
      aesop
    rw [hset]
    exact (Finset.card_product _ _).trans (pow_two _).symm
  have hsum :
      (∑ k ∈ Finset.range (2 * N),
          (Q.filter fun q => q.1.1 + q.1.2 = k).card) =
        (Q.filter fun q => q.1.1 + q.1.2 ∈ Finset.range (2 * N)).card := by
    simpa only [Finset.card_eq_sum_ones] using
      (Finset.sum_fiberwise_eq_sum_filter Q (Finset.range (2 * N))
        (fun q => q.1.1 + q.1.2) (fun _ => 1))
  have hrange : Q.filter (fun q => q.1.1 + q.1.2 ∈ Finset.range (2 * N)) = Q := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    change q ∈ (P.product P).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2) at hq
    have hqPP : q ∈ P.product P := (Finset.mem_filter.mp hq).1
    have hqPP' : q.1 ∈ P ∧ q.2 ∈ P := by simpa using hqPP
    have hqP : q.1 ∈ P := hqPP'.1
    have hqS : q.1.1 ∈ S ∧ q.1.2 ∈ S := by
      change q.1 ∈ S.product S at hqP
      simpa using hqP
    have h1 := hS hqS.1
    have h2 := hS hqS.2
    simp only [Finset.mem_range] at h1 h2 ⊢
    omega
  have hnat : maynardNatRStar S N = (maynardNatAdditiveQuadruples S).card := by
    calc
      maynardNatRStar S N =
          ∑ k ∈ Finset.range (2 * N),
            (Q.filter fun q => q.1.1 + q.1.2 = k).card := by
        unfold maynardNatRStar
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [P] using (hfiber k).symm
      _ = Q.card := by rw [hsum, hrange]
      _ = (maynardNatAdditiveQuadruples S).card := by rfl
  rw [hnat, maynardRStar, maynardAdditiveQuadruples_map_natCast,
    Finset.card_map]

/-- Unit-interval averaging is contractive from `L⁴` to fourth power of
norm of the average. -/
theorem norm_four_intervalIntegral_unit_le_integral_norm_four
    {D : ℝ → ℂ} (hD : Continuous D) :
    ‖∫ v : ℝ in (0 : ℝ)..1, D v‖ ^ 4 ≤
      ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 4 := by
  let I2 : ℝ := ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 2
  let I4 : ℝ := ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 4
  have hI2 : 0 ≤ I2 := by
    dsimp only [I2]
    exact intervalIntegral.integral_nonneg zero_le_one fun v _ => by positivity
  have hI4 : 0 ≤ I4 := by
    dsimp only [I4]
    exact intervalIntegral.integral_nonneg zero_le_one fun v _ => by positivity
  have hnorm : ‖∫ v : ℝ in (0 : ℝ)..1, D v‖ ≤
      ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hcs1 :=
    GaloisForLFunctions.HTGeometry.integral_norm_le_sqrt_length_mul_sqrt_meanSquare
      hD (a := (0 : ℝ)) (b := 1) zero_le_one
  simp only [sub_zero, Real.sqrt_one, one_mul] at hcs1
  have hnorm2 : ‖∫ v : ℝ in (0 : ℝ)..1, D v‖ ^ 2 ≤ I2 := by
    have hsqrt : Real.sqrt I2 ^ 2 = I2 := Real.sq_sqrt hI2
    nlinarith [norm_nonneg (∫ v : ℝ in (0 : ℝ)..1, D v),
      Real.sqrt_nonneg I2]
  let E : ℝ → ℂ := fun v => (‖D v‖ ^ 2 : ℝ)
  have hE : Continuous E := by
    dsimp only [E]
    exact Complex.continuous_ofReal.comp (hD.norm.pow 2)
  have hcs2 :=
    GaloisForLFunctions.HTGeometry.integral_norm_le_sqrt_length_mul_sqrt_meanSquare
      hE (a := (0 : ℝ)) (b := 1) zero_le_one
  have hEI2 : (∫ v : ℝ in (0 : ℝ)..1, ‖E v‖) = I2 := by
    dsimp only [E, I2]
    apply intervalIntegral.integral_congr
    intro v hv
    simp
  have hEI4 : (∫ v : ℝ in (0 : ℝ)..1, ‖E v‖ ^ 2) = I4 := by
    dsimp only [E, I4]
    apply intervalIntegral.integral_congr
    intro v hv
    simp
    ring
  rw [sub_zero, Real.sqrt_one, one_mul, hEI2, hEI4] at hcs2
  have hI2sq : I2 ^ 2 ≤ I4 := by
    have hsqrt : Real.sqrt I4 ^ 2 = I4 := Real.sq_sqrt hI4
    nlinarith [Real.sqrt_nonneg I4]
  calc
    ‖∫ v : ℝ in (0 : ℝ)..1, D v‖ ^ 4 =
        (‖∫ v : ℝ in (0 : ℝ)..1, D v‖ ^ 2) ^ 2 := by ring
    _ ≤ I2 ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hnorm2 2
    _ ≤ I4 := hI2sq
    _ = ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 4 := rfl

/-- Exact square of a discrete Mellin packet as a packet of additive
convolution coefficients. -/
theorem maynardDiscreteMellinPacket_sq_eq
    {y : ℝ} (hy : 0 < y) {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) (a : ℕ → ℂ) (c : ℝ) :
    maynardDiscreteMellinPacket S a c y ^ 2 =
      maynardDiscreteMellinPacket (Finset.range (2 * N))
        (maynardAdditiveSquareCoeff S a) (2 * c) y := by
  classical
  rw [pow_two, maynardDiscreteMellinPacket, maynardDiscreteMellinPacket,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  let F : ℕ × ℕ → ℂ := fun p =>
    (a p.1 * a p.2) *
      (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((p.1 + p.2 : ℕ) : ℝ) : ℂ) * I)
  have hmaps : ∀ p ∈ S.product S, p.1 + p.2 ∈ Finset.range (2 * N) := by
    intro p hp
    have hp' : p.1 ∈ S ∧ p.2 ∈ S := by simpa using hp
    have h1 := Finset.mem_range.mp (hS hp'.1)
    have h2 := Finset.mem_range.mp (hS hp'.2)
    simp only [Finset.mem_range]
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps F
  have hproduct : (S.product S).sum F =
      ∑ x ∈ S, ∑ i ∈ S, F (x, i) := by
    exact Finset.sum_product S S F
  calc
    (∑ x ∈ S, ∑ i ∈ S,
        a x * (y : ℂ) ^ ((c : ℂ) + (x : ℂ) * I) *
          (a i * (y : ℂ) ^ ((c : ℂ) + (i : ℂ) * I))) =
        (S.product S).sum F := by
      rw [hproduct]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [F]
      have hpow :
          (y : ℂ) ^ ((c : ℂ) + (x : ℂ) * I) *
              (y : ℂ) ^ ((c : ℂ) + (i : ℂ) * I) =
            (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((x + i : ℕ) : ℝ) : ℂ) * I) := by
        rw [← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hy.ne')]
        congr 1
        push_cast
        apply Complex.ext
        · simp
          ring
        · simp
      calc
        a x * (y : ℂ) ^ ((c : ℂ) + (x : ℂ) * I) *
            (a i * (y : ℂ) ^ ((c : ℂ) + (i : ℂ) * I)) =
            (a x * a i) *
              ((y : ℂ) ^ ((c : ℂ) + (x : ℂ) * I) *
                (y : ℂ) ^ ((c : ℂ) + (i : ℂ) * I)) := by ring
        _ = (a x * a i) *
            (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((x + i : ℕ) : ℝ) : ℂ) * I) := by
          rw [hpow]
    _ = ∑ k ∈ Finset.range (2 * N),
        ∑ p ∈ S.product S with p.1 + p.2 = k, F p := hfiber.symm
    _ = ∑ k ∈ Finset.range (2 * N),
        maynardAdditiveSquareCoeff S a k *
          (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((k : ℝ) : ℂ) * I) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [maynardAdditiveSquareCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hpsum : p.1 + p.2 = k := (Finset.mem_filter.mp hp).2
      dsimp only [F]
      rw [hpsum]

/-- Squared coefficient energy is bounded by coefficient amplitude to fourth
power times exact pair-sum energy. -/
theorem sum_norm_sq_maynardAdditiveSquareCoeff_le_rstar
    {N : ℕ} (S : Finset ℕ) (a : ℕ → ℂ) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ m ∈ S, ‖a m‖ ≤ A) :
    (∑ k ∈ Finset.range (2 * N),
        ‖maynardAdditiveSquareCoeff S a k‖ ^ 2) ≤
      A ^ 4 * (maynardNatRStar S N : ℝ) := by
  classical
  have hterm : ∀ k ∈ Finset.range (2 * N),
      ‖maynardAdditiveSquareCoeff S a k‖ ^ 2 ≤
        A ^ 4 *
          (((S.product S).filter (fun p => p.1 + p.2 = k)).card : ℝ) ^ 2 := by
    intro k hk
    let Fk : Finset (ℕ × ℕ) :=
      (S.product S).filter (fun p => p.1 + p.2 = k)
    have hnorm : ‖maynardAdditiveSquareCoeff S a k‖ ≤
        (Fk.card : ℝ) * A ^ 2 := by
      calc
        ‖maynardAdditiveSquareCoeff S a k‖ ≤
            ∑ p ∈ Fk, ‖a p.1 * a p.2‖ := by
          dsimp only [maynardAdditiveSquareCoeff, Fk]
          exact norm_sum_le _ _
        _ ≤ ∑ _p ∈ Fk, A ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          have hpProd : p ∈ S.product S := (Finset.mem_filter.mp hp).1
          have hpS : p.1 ∈ S ∧ p.2 ∈ S := by simpa using hpProd
          rw [norm_mul]
          have hmul := mul_le_mul (ha p.1 hpS.1) (ha p.2 hpS.2)
            (norm_nonneg _) hA
          simpa [pow_two] using hmul
        _ = (Fk.card : ℝ) * A ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    change ‖maynardAdditiveSquareCoeff S a k‖ ^ 2 ≤
      A ^ 4 * (Fk.card : ℝ) ^ 2
    calc
      ‖maynardAdditiveSquareCoeff S a k‖ ^ 2 ≤
          ((Fk.card : ℝ) * A ^ 2) ^ 2 := hsq
      _ = A ^ 4 * (Fk.card : ℝ) ^ 2 := by ring
  calc
    (∑ k ∈ Finset.range (2 * N),
        ‖maynardAdditiveSquareCoeff S a k‖ ^ 2) ≤
        ∑ k ∈ Finset.range (2 * N),
          A ^ 4 *
            (((S.product S).filter (fun p => p.1 + p.2 = k)).card : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun k hk => hterm k hk
    _ = A ^ 4 * (maynardNatRStar S N : ℝ) := by
      unfold maynardNatRStar
      push_cast
      rw [Finset.mul_sum]

/-- Spatial fourth moment of a discrete Mellin packet, controlled by exact
additive energy of selected frequency cells. -/
theorem integral_norm_four_maynardDiscreteMellinPacket_le_rstar
    {x c A : ℝ} {N : ℕ} (hx : 0 < x) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A) :
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 4) ≤
      4 * (2 * x) ^ (4 * c + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
  let q : ℕ → ℂ := maynardAdditiveSquareCoeff S a
  have hpoint : ∀ y ∈ Set.Icc x (2 * x),
      ‖maynardDiscreteMellinPacket S a c y‖ ^ 4 =
        ‖maynardDiscreteMellinPacket (Finset.range (2 * N)) q (2 * c) y‖ ^ 2 := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    rw [← maynardDiscreteMellinPacket_sq_eq hypos S hS a c]
    rw [norm_pow]
    ring
  have heq :
      (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 4) =
        ∫ y : ℝ in x..(2 * x),
          ‖maynardDiscreteMellinPacket (Finset.range (2 * N)) q (2 * c) y‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
    exact hpoint y hy
  rw [heq]
  have hc2 : 0 ≤ 2 * c := mul_nonneg (by norm_num) hc
  have hL2 := integral_norm_sq_maynardDiscreteMellinPacket_le_energy
    (N := 2 * N) hx hc2 (Finset.range (2 * N)) (by simp) q
  have henergy := sum_norm_sq_maynardAdditiveSquareCoeff_le_rstar
    (N := N) S a hA ha
  have hfactor : 0 ≤
      4 * (2 * x) ^ (2 * (2 * c) + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) := by
    by_cases hN : N = 0
    · subst N
      norm_num
      positivity
    · have hN1 : 1 ≤ 2 * N := by omega
      have hlog : 0 ≤ Real.log (2 * N) :=
        Real.log_nonneg (by exact_mod_cast hN1)
      positivity
  calc
    (∫ y : ℝ in x..(2 * x),
        ‖maynardDiscreteMellinPacket (Finset.range (2 * N)) q (2 * c) y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * (2 * c) + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) *
          ∑ k ∈ Finset.range (2 * N), ‖q k‖ ^ 2 := by
      simpa [Nat.cast_mul] using hL2
    _ ≤ 4 * (2 * x) ^ (2 * (2 * c) + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) *
          (A ^ 4 * (maynardNatRStar S N : ℝ)) :=
      mul_le_mul_of_nonneg_left henergy hfactor
    _ = 4 * (2 * x) ^ (4 * c + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
      rw [← maynardNatRStar_eq_maynardRStar_map hS]
      ring_nf

/-- Continuous unit-cell spatial fourth moment controlled by additive energy.
Unit-cell averaging costs no factor because its interval has length one. -/
theorem integral_norm_four_maynardUnitCellMellinPacket_le_rstar
    {x c A : ℝ} {N : ℕ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (b : ℕ → ℝ → ℂ)
    (hb : ∀ m ∈ S, Continuous (b m))
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖b m v‖ ≤ A) :
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 4) ≤
      4 * (2 * x) ^ (4 * c + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let Q : ℝ → ℝ → ℂ := fun v y =>
    maynardUnitCellMellinIntegrandPosExtension S b c v y
  let P : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b c
  let F : ℝ → ℝ → ℝ := fun y v => ‖Q v y‖ ^ 4
  let C : ℝ := 4 * (2 * x) ^ (4 * c + 1) *
    (1 + 2 * (1 + Real.log (2 * N))) * A ^ 4 *
      (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ)
  have hQ : Continuous fun p : ℝ × ℝ => Q p.1 p.2 :=
    continuous_maynardUnitCellMellinIntegrandPosExtension S b c hb
  have hP : Continuous P :=
    continuous_maynardUnitCellMellinPacketPosExtension S b c hb
  have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    dsimp only [F]
    exact (hQ.comp (continuous_snd.prodMk continuous_fst)).norm.pow 4
  have hleft :
      (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 4) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 4 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    change ‖maynardUnitCellMellinPacket S b c y‖ ^ 4 =
      ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 4
    rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
  have hpoint : ∀ y ∈ Set.Icc x (2 * x),
      ‖P y‖ ^ 4 ≤ ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    intro y hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    have hD := norm_four_intervalIntegral_unit_le_integral_norm_four
      (continuous_maynardUnitCellMellinIntegrand_fixed_base hy1 S b c hb)
    calc
      ‖P y‖ ^ 4 = ‖maynardUnitCellMellinPacket S b c y‖ ^ 4 := by
        change ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 4 = _
        rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
      _ ≤ ∫ v : ℝ in (0 : ℝ)..1,
          ‖maynardUnitCellMellinIntegrand S b c v y‖ ^ 4 := hD
      _ = ∫ v : ℝ in (0 : ℝ)..1, F y v := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only [F, Q]
        rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
          norm_maynardUnitCellMellinIntegrand_eq_discrete
            (lt_of_lt_of_le zero_lt_one hy1)]
  have hinnerContinuous : Continuous fun y =>
      ∫ v : ℝ in (0 : ℝ)..1, F y v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hmono :
      (∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 4) ≤
        ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    exact intervalIntegral.integral_mono_on (by linarith)
      (hP.norm.pow 4 |>.intervalIntegrable x (2 * x))
      (hinnerContinuous.intervalIntegrable x (2 * x)) hpoint
  have hswap :
      (∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v) =
        ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v :=
    intervalIntegral_swap_of_continuous_maynard hF x (2 * x) 0 1
  have houterContinuous : Continuous fun v =>
      ∫ y : ℝ in x..(2 * x), F y v := by
    change Continuous fun v => ∫ y : ℝ in x..(2 * x), ‖Q v y‖ ^ 4
    have hFswap : Continuous fun p : ℝ × ℝ => ‖Q p.1 p.2‖ ^ 4 := hQ.norm.pow 4
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hFswap x (2 * x)
  have houterPoint : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    intro v hv
    have heq :
        (∫ y : ℝ in x..(2 * x), F y v) =
          ∫ y : ℝ in x..(2 * x),
            ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 4 := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
      have hy1 : 1 ≤ y := hx.trans hy.1
      dsimp only [F, Q]
      rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
        norm_maynardUnitCellMellinIntegrand_eq_discrete
          (lt_of_lt_of_le zero_lt_one hy1)]
    rw [heq]
    have hd := integral_norm_four_maynardDiscreteMellinPacket_le_rstar
      hxpos hc hA S hS (fun m => b m v) (fun m hm => hbnd m hm v hv)
    simpa only [C] using hd
  have houter :
      (∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    have hcst : IntervalIntegrable (fun _v : ℝ => C) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hle := intervalIntegral.integral_mono_on zero_le_one
      (houterContinuous.intervalIntegrable 0 1) hcst houterPoint
    simpa using hle
  calc
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 4) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 4 := hleft
    _ ≤ ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := hmono
    _ = ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v := hswap
    _ ≤ C := houter
    _ = 4 * (2 * x) ^ (4 * c + 1) *
        (1 + 2 * (1 + Real.log (2 * N))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := rfl

/-- Fixed-ambient spatial fourth moment: equation-(112) analytic shape before
inserting a particular Dirichlet-polynomial source. -/
theorem integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar
    {x sigma A N R H : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hsigma : 1 ≤ sigma) (hA : 0 ≤ A)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount) (a : ℝ → ℂ)
    (ha : Continuous a)
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H sigma m v‖ ≤ A) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket
          S a lambda N R H sigma‖ ^ 4) ≤
      4 * (2 * x) ^ (4 * (sigma - 1) + 1) *
        (1 + 2 * (1 + Real.log (2 * cellCount))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
  have hb : ∀ m ∈ S,
      Continuous (maynardFixedAmbientDefectCellCoefficient a N R H sigma m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient ha hN hR hH
      (lt_of_lt_of_le zero_lt_one hsigma) m
  have hL4 := integral_norm_four_maynardUnitCellMellinPacket_le_rstar
    hx (sub_nonneg.mpr hsigma) hA S hS
      (maynardFixedAmbientDefectCellCoefficient a N R H sigma) hb hbnd
  calc
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma‖ ^ 4) =
        ∫ lambda : ℝ in x..(2 * x),
          ‖maynardUnitCellMellinPacket S
            (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
            (sigma - 1) lambda‖ ^ 4 := by
      apply intervalIntegral.integral_congr
      intro lambda hlambda
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
      change ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma‖ ^ 4 =
        ‖maynardUnitCellMellinPacket S
          (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
          (sigma - 1) lambda‖ ^ 4
      rw [maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
        S a lambda N R H sigma
          (lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)) hR hH]
    _ ≤ 4 * (2 * x) ^ (4 * (sigma - 1) + 1) *
        (1 + 2 * (1 + Real.log (2 * cellCount))) * A ^ 4 *
          (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := hL4

/-- Restricted-volume fourth-moment Markov law on an ordered compact
interval. -/
theorem maynard_restrictVolume_norm_ge_le_of_intervalIntegral_four_le
    (f : ℝ → ℂ) (hf : Continuous f) {a b A B : ℝ}
    (hab : a ≤ b) (hA : 0 < A)
    (hmean : (∫ t in a..b, ‖f t‖ ^ 4) ≤ B) :
    (volume.restrict (Set.Icc a b)).real {t | A ≤ ‖f t‖} ≤ B / A ^ 4 := by
  let mu : Measure ℝ := volume.restrict (Set.Icc a b)
  have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 4) mu := by
    exact (hf.norm.pow 4).integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[mu] fun t : ℝ => ‖f t‖ ^ 4 :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    hnonneg hint (A ^ 4)
  have hset : {t : ℝ | A ^ 4 ≤ ‖f t‖ ^ 4} = {t : ℝ | A ≤ ‖f t‖} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hpow
      by_contra hnot
      have hlt : ‖f t‖ < A := lt_of_not_ge hnot
      have hp : ‖f t‖ ^ 4 < A ^ 4 :=
        pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
      exact (not_lt_of_ge hpow) hp
    · intro h
      exact pow_le_pow_left₀ hA.le h 4
  rw [hset] at hmark
  have hintegral : (∫ t, ‖f t‖ ^ 4 ∂mu) ≤ B := by
    change (∫ t in Set.Icc a b, ‖f t‖ ^ 4) ≤ B
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    exact hmean
  apply (le_div_iff₀ (pow_pos hA 4)).2
  simpa [mu, mul_comm] using hmark.trans hintegral

/-- Equation-(112) bad-base measure bound for a fixed-ambient physical
defect packet, with exact selected-cell additive energy. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_rstar
    {x N R H A D : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hA : 0 ≤ A) (hD : 0 < D)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H 1 m v‖ ≤ A) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} ≤
      (4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        A ^ 4 * (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ)) / D ^ 4 := by
  let b : ℕ → ℝ → ℂ :=
    maynardFixedAmbientDefectCellCoefficient a N R H 1
  let Q : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b 0
  let E : ℝ → ℂ := fun lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  have hb : ∀ m ∈ S, Continuous (b m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient
      ha hN hR hH (by norm_num) m
  have hQ : Continuous Q :=
    continuous_maynardUnitCellMellinPacketPosExtension S b 0 hb
  have hQE : ∀ lambda ∈ Set.Icc x (2 * x), Q lambda = E lambda := by
    intro lambda hlambda
    have hlambdaOne : 1 ≤ lambda := hx.trans hlambda.1
    have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaOne
    dsimp only [Q, E, b]
    rw [maynardUnitCellMellinPacketPosExtension_eq hlambdaOne]
    simpa using (maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
      S a lambda N R H 1 hlambdaPos hR hH).symm
  have hmeanE :=
    integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar
      (x := x) (sigma := (1 : ℝ)) (A := A) (cellCount := cellCount)
      hx (by norm_num) hA hN hR hH S hS a ha hbnd
  have hmeanQ :
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 4) ≤
        4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
          A ^ 4 * (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ) := by
    calc
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 4) =
          ∫ lambda : ℝ in x..(2 * x), ‖E lambda‖ ^ 4 := by
        apply intervalIntegral.integral_congr
        intro lambda hlambda
        rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
        change ‖Q lambda‖ ^ 4 = ‖E lambda‖ ^ 4
        rw [hQE lambda hlambda]
      _ ≤ _ := by
        simpa only [sub_self, mul_zero, zero_add, Real.rpow_one] using hmeanE
  have hmark := maynard_restrictVolume_norm_ge_le_of_intervalIntegral_four_le
    Q hQ (by linarith : x ≤ 2 * x) hD hmeanQ
  let mu : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hae : {lambda | D ≤ ‖E lambda‖} =ᵐ[mu]
      {lambda | D ≤ ‖Q lambda‖} := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    apply propext
    change (D ≤ ‖E lambda‖) ↔ (D ≤ ‖Q lambda‖)
    rw [← hQE lambda hlambda]
  have hmeasure : mu.real {lambda | D ≤ ‖E lambda‖} =
      mu.real {lambda | D ≤ ‖Q lambda‖} := by
    rw [measureReal_def, measureReal_def, measure_congr hae]
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} =
        mu.real {lambda | D ≤ ‖E lambda‖} := by rfl
    _ = mu.real {lambda | D ≤ ‖Q lambda‖} := hmeasure
    _ ≤ (4 * (2 * x) * (1 + 2 * (1 + Real.log (2 * cellCount))) *
        A ^ 4 * (maynardRStar (S.map maynardNatToIntEmbedding) : ℝ)) / D ^ 4 := by
      simpa only [mu] using hmark

end RHTower.Sieve
