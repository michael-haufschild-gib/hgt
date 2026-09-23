import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniPhaseTaxHeightThreshold

/-!
# Pair-energy transport law for degree-one Cassini contact

For nodes `zᵢ`, define ordered interaction energy

`Eᵢⱼ = zᵢ zⱼ (zᵢ-zⱼ)²`

and its radial transport `Eᵢⱼ(zᵢ+zⱼ)`.  Absolute convergence turns the first Hankel minor and
its next transport numerator into the exact pair sums

`2(m₀m₂-m₁²) = ∑ᵢⱼ Eᵢⱼ`,

`2(m₀m₃-m₁m₂) = ∑ᵢⱼ Eᵢⱼ(zᵢ+zⱼ)`.

The result is proved first for every countable complex packet with four summable powers, then for
the full multiplicity-exact Xi zero-copy divisor.  At an actual flat Xi face, total interaction
energy is exactly zero and terminal flux is its velocity-weighted transport divided by the
strictly positive Cassini response.  Degree-one Route U is therefore a signed transport problem,
not an atomwise positivity or fixed-sector problem.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem summable_prod_mul_of_summable
    {α β : Type*} {f : α → ℂ} {g : β → ℂ}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : α × β => f p.1 * g p.2) :=
  summable_mul_of_summable_norm hf.norm hg.norm

def countableCassiniPairEnergy {α : Type*} (z : α → ℂ) (p : α × α) : ℂ :=
  z p.1 * z p.2 * (z p.1 - z p.2) ^ (2 : ℕ)

def countableCassiniPairTransport {α : Type*} (z : α → ℂ) (p : α × α) : ℂ :=
  countableCassiniPairEnergy z p * (z p.1 + z p.2)

theorem summable_countableCassiniPairEnergy
    {α : Type*} {z : α → ℂ}
    (h1 : Summable z)
    (h2 : Summable (fun i => z i ^ (2 : ℕ)))
    (h3 : Summable (fun i => z i ^ (3 : ℕ))) :
    Summable (countableCassiniPairEnergy z) := by
  have h31 : Summable (fun p : α × α => z p.1 ^ (3 : ℕ) * z p.2) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (3 : ℕ)) z h3 h1
  have h22 : Summable (fun p : α × α => z p.1 ^ (2 : ℕ) * z p.2 ^ (2 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (2 : ℕ))
      (fun i => z i ^ (2 : ℕ)) h2 h2
  have h13 : Summable (fun p : α × α => z p.1 * z p.2 ^ (3 : ℕ)) :=
    @summable_prod_mul_of_summable α α z (fun i => z i ^ (3 : ℕ)) h1 h3
  exact ((h31.sub (h22.mul_left 2)).add h13).congr (fun p => by
    simp only [countableCassiniPairEnergy]
    ring)

theorem summable_countableCassiniPairTransport
    {α : Type*} {z : α → ℂ}
    (h1 : Summable z)
    (h2 : Summable (fun i => z i ^ (2 : ℕ)))
    (h3 : Summable (fun i => z i ^ (3 : ℕ)))
    (h4 : Summable (fun i => z i ^ (4 : ℕ))) :
    Summable (countableCassiniPairTransport z) := by
  have h41 : Summable (fun p : α × α => z p.1 ^ (4 : ℕ) * z p.2) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (4 : ℕ)) z h4 h1
  have h32 : Summable (fun p : α × α => z p.1 ^ (3 : ℕ) * z p.2 ^ (2 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (3 : ℕ))
      (fun i => z i ^ (2 : ℕ)) h3 h2
  have h23 : Summable (fun p : α × α => z p.1 ^ (2 : ℕ) * z p.2 ^ (3 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (2 : ℕ))
      (fun i => z i ^ (3 : ℕ)) h2 h3
  have h14 : Summable (fun p : α × α => z p.1 * z p.2 ^ (4 : ℕ)) :=
    @summable_prod_mul_of_summable α α z (fun i => z i ^ (4 : ℕ)) h1 h4
  exact (((h41.sub h32).sub h23).add h14).congr (fun p => by
    simp only [countableCassiniPairTransport, countableCassiniPairEnergy]
    ring)

theorem two_mul_countableCassiniMinor_eq_pairEnergy
    {α : Type*} {z : α → ℂ}
    (h1 : Summable z)
    (h2 : Summable (fun i => z i ^ (2 : ℕ)))
    (h3 : Summable (fun i => z i ^ (3 : ℕ))) :
    2 * ((∑' i, z i) * (∑' i, z i ^ (3 : ℕ)) - (∑' i, z i ^ (2 : ℕ)) ^ (2 : ℕ)) =
      ∑' p, countableCassiniPairEnergy z p := by
  have h31 : Summable (fun p : α × α => z p.1 ^ (3 : ℕ) * z p.2) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (3 : ℕ)) z h3 h1
  have h22 : Summable (fun p : α × α => z p.1 ^ (2 : ℕ) * z p.2 ^ (2 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (2 : ℕ))
      (fun i => z i ^ (2 : ℕ)) h2 h2
  have h13 : Summable (fun p : α × α => z p.1 * z p.2 ^ (3 : ℕ)) :=
    @summable_prod_mul_of_summable α α z (fun i => z i ^ (3 : ℕ)) h1 h3
  rw [show countableCassiniPairEnergy z =
      (fun p : α × α => z p.1 ^ (3 : ℕ) * z p.2 -
        2 * (z p.1 ^ (2 : ℕ) * z p.2 ^ (2 : ℕ)) + z p.1 * z p.2 ^ (3 : ℕ)) by
    funext p
    simp only [countableCassiniPairEnergy]
    ring]
  rw [Summable.tsum_add (h31.sub (h22.mul_left 2)) h13,
    Summable.tsum_sub h31 (h22.mul_left 2), tsum_mul_left,
    ← h3.tsum_mul_tsum h1 h31, ← h2.tsum_mul_tsum h2 h22,
    ← h1.tsum_mul_tsum h3 h13]
  ring

theorem two_mul_countableCassiniTransportNumerator_eq_pairTransport
    {α : Type*} {z : α → ℂ}
    (h1 : Summable z)
    (h2 : Summable (fun i => z i ^ (2 : ℕ)))
    (h3 : Summable (fun i => z i ^ (3 : ℕ)))
    (h4 : Summable (fun i => z i ^ (4 : ℕ))) :
    2 * ((∑' i, z i) * (∑' i, z i ^ (4 : ℕ)) -
      (∑' i, z i ^ (2 : ℕ)) * (∑' i, z i ^ (3 : ℕ))) =
      ∑' p, countableCassiniPairTransport z p := by
  have h41 : Summable (fun p : α × α => z p.1 ^ (4 : ℕ) * z p.2) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (4 : ℕ)) z h4 h1
  have h32 : Summable (fun p : α × α => z p.1 ^ (3 : ℕ) * z p.2 ^ (2 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (3 : ℕ))
      (fun i => z i ^ (2 : ℕ)) h3 h2
  have h23 : Summable (fun p : α × α => z p.1 ^ (2 : ℕ) * z p.2 ^ (3 : ℕ)) :=
    @summable_prod_mul_of_summable α α (fun i => z i ^ (2 : ℕ))
      (fun i => z i ^ (3 : ℕ)) h2 h3
  have h14 : Summable (fun p : α × α => z p.1 * z p.2 ^ (4 : ℕ)) :=
    @summable_prod_mul_of_summable α α z (fun i => z i ^ (4 : ℕ)) h1 h4
  rw [show countableCassiniPairTransport z =
      (fun p : α × α => z p.1 ^ (4 : ℕ) * z p.2 - z p.1 ^ (3 : ℕ) * z p.2 ^ (2 : ℕ) -
        z p.1 ^ (2 : ℕ) * z p.2 ^ (3 : ℕ) + z p.1 * z p.2 ^ (4 : ℕ)) by
    funext p
    simp only [countableCassiniPairTransport, countableCassiniPairEnergy]
    ring]
  rw [Summable.tsum_add ((h41.sub h32).sub h23) h14,
    Summable.tsum_sub (h41.sub h32) h23, Summable.tsum_sub h41 h32,
    ← h4.tsum_mul_tsum h1 h41, ← h3.tsum_mul_tsum h2 h32,
    ← h2.tsum_mul_tsum h3 h23, ← h1.tsum_mul_tsum h4 h14]
  ring

def xiShiftedCassiniPairEnergy (y : ℝ) : XiZeroCopy × XiZeroCopy → ℂ :=
  countableCassiniPairEnergy (xiShiftedReciprocalSquare y)

def xiShiftedCassiniPairTransport (y : ℝ) : XiZeroCopy × XiZeroCopy → ℂ :=
  countableCassiniPairTransport (xiShiftedReciprocalSquare y)

theorem summable_xiShiftedCassiniPairEnergy {y : ℝ} (hy : 0 ≤ y) :
    Summable (xiShiftedCassiniPairEnergy y) := by
  have h1 : Summable (xiShiftedReciprocalSquare y) := by
    simpa only [Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  exact summable_countableCassiniPairEnergy
    h1
    (summable_xiShiftedReciprocalSquare_pow hy 1)
    (summable_xiShiftedReciprocalSquare_pow hy 2)

theorem summable_xiShiftedCassiniPairTransport {y : ℝ} (hy : 0 ≤ y) :
    Summable (xiShiftedCassiniPairTransport y) := by
  have h1 : Summable (xiShiftedReciprocalSquare y) := by
    simpa only [Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  exact summable_countableCassiniPairTransport
    h1
    (summable_xiShiftedReciprocalSquare_pow hy 1)
    (summable_xiShiftedReciprocalSquare_pow hy 2)
    (summable_xiShiftedReciprocalSquare_pow hy 3)

theorem two_mul_xiShiftedCassiniMinorComplex_eq_pairEnergy
    {y : ℝ} (hy : 0 ≤ y) :
    2 * (xiShiftedReciprocalMoment y 0 * xiShiftedReciprocalMoment y 2 -
      xiShiftedReciprocalMoment y 1 ^ (2 : ℕ)) =
      ∑' p, xiShiftedCassiniPairEnergy y p := by
  have h1 : Summable (xiShiftedReciprocalSquare y) := by
    simpa only [Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  simpa only [xiShiftedReciprocalMoment, xiShiftedCassiniPairEnergy,
      Nat.zero_add, Nat.reduceAdd, pow_one] using
    two_mul_countableCassiniMinor_eq_pairEnergy
      h1
      (summable_xiShiftedReciprocalSquare_pow hy 1)
      (summable_xiShiftedReciprocalSquare_pow hy 2)

theorem two_mul_xiShiftedCassiniTransportNumerator_eq_pairTransport
    {y : ℝ} (hy : 0 ≤ y) :
    2 * (xiShiftedReciprocalMoment y 0 * xiShiftedReciprocalMoment y 3 -
      xiShiftedReciprocalMoment y 1 * xiShiftedReciprocalMoment y 2) =
      ∑' p, xiShiftedCassiniPairTransport y p := by
  have h1 : Summable (xiShiftedReciprocalSquare y) := by
    simpa only [Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  simpa only [xiShiftedReciprocalMoment, xiShiftedCassiniPairTransport,
      Nat.zero_add, Nat.reduceAdd, pow_one] using
    two_mul_countableCassiniTransportNumerator_eq_pairTransport
      h1
      (summable_xiShiftedReciprocalSquare_pow hy 1)
      (summable_xiShiftedReciprocalSquare_pow hy 2)
      (summable_xiShiftedReciprocalSquare_pow hy 3)

private theorem xiShiftedReciprocalMoment_eq_ofReal_re
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    xiShiftedReciprocalMoment y n =
      ((xiShiftedReciprocalMoment y n).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [xiShiftedReciprocalMoment_im_eq_zero hy n]

/-- The actual ordered pair energy is exactly twice the real first Hankel minor. -/
theorem tsum_xiShiftedCassiniPairEnergy_eq_two_mul_minor
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' p, xiShiftedCassiniPairEnergy y p =
      ((2 * xiShiftedDegreeOneHankelMinor y : ℝ) : ℂ) := by
  have h := two_mul_xiShiftedCassiniMinorComplex_eq_pairEnergy hy
  rw [xiShiftedReciprocalMoment_eq_ofReal_re hy 0,
    xiShiftedReciprocalMoment_eq_ofReal_re hy 1,
    xiShiftedReciprocalMoment_eq_ofReal_re hy 2] at h
  rw [← h]
  simp only [xiShiftedDegreeOneHankelMinor, xiShiftedCassiniResponse]
  push_cast
  ring

/-- A flat actual Xi face is literal zero total pair-interaction energy. -/
theorem tsum_xiShiftedCassiniPairEnergy_eq_zero_of_flat
    {y : ℝ} (hy : 0 ≤ y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    ∑' p, xiShiftedCassiniPairEnergy y p = 0 := by
  rw [tsum_xiShiftedCassiniPairEnergy_eq_two_mul_minor hy, hflat]
  norm_num

/-- At a flat face, terminal flux is exactly normalized pair-energy transport. -/
theorem tsum_xiShiftedCassiniPairTransport_eq_two_mul_response_mul_terminalFlux_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    ∑' p, xiShiftedCassiniPairTransport y p =
      ((2 * xiShiftedCassiniResponse y * xiShiftedDegreeOneTerminalFlux y : ℝ) : ℂ) := by
  let m0 : ℝ := (xiShiftedReciprocalMoment y 0).re
  let m1 : ℝ := (xiShiftedReciprocalMoment y 1).re
  let m2 : ℝ := (xiShiftedReciprocalMoment y 2).re
  let m3 : ℝ := (xiShiftedReciprocalMoment y 3).re
  have hm0 : 0 < m0 := xiShiftedCassiniResponse_pos hy
  have hcontact : m0 * m2 = m1 ^ (2 : ℕ) := by
    rw [xiShiftedDegreeOneHankelMinor] at hflat
    dsimp only [xiShiftedCassiniResponse, m0, m1, m2] at hflat
    linarith
  have hterminal := xiShiftedDegreeOneTerminalFlux_eq_moments y
  have hterminalTransport :
      m0 * xiShiftedDegreeOneTerminalFlux y = m0 * m3 - m1 * m2 := by
    rw [hterminal]
    change m0 * (m3 - 2 * (m1 / m0) * m2 + (m1 / m0) ^ (2 : ℕ) * m1) =
      m0 * m3 - m1 * m2
    have hcubic : m1 ^ (3 : ℕ) = m0 * m1 * m2 := by
      calc
        m1 ^ (3 : ℕ) = m1 * (m1 ^ (2 : ℕ)) := by ring
        _ = m1 * (m0 * m2) := by rw [← hcontact]
        _ = m0 * m1 * m2 := by ring
    field_simp [hm0.ne']
    nlinarith [hcubic]
  have htransport :=
    two_mul_xiShiftedCassiniTransportNumerator_eq_pairTransport hy.le
  rw [xiShiftedReciprocalMoment_eq_ofReal_re hy.le 0,
    xiShiftedReciprocalMoment_eq_ofReal_re hy.le 1,
    xiShiftedReciprocalMoment_eq_ofReal_re hy.le 2,
    xiShiftedReciprocalMoment_eq_ofReal_re hy.le 3] at htransport
  rw [← htransport]
  change 2 * (((m0 : ℂ) * (m3 : ℂ)) - ((m1 : ℂ) * (m2 : ℂ))) =
    ((2 * m0 * xiShiftedDegreeOneTerminalFlux y : ℝ) : ℂ)
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hterminalTransport
  push_cast at hcast ⊢
  rw [← hcast]
  ring

end


end RHTower
