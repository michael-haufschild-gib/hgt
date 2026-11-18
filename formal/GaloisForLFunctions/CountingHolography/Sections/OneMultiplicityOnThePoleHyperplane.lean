import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor

/-!
# One section comparison per pole-balanced divisor

The square root of the prime horizon suffices as multiplicity for every
bounded-mass signed divisor. Above that threshold the logarithm of the
ordinary generator divided by the squared multiplicity differs from the
negative Weil degree by a constant depending only on coefficient mass.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography Zeta23

private theorem sampling_above_horizon {M : ℝ} (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ} (a : Fin N → ℤ), (∑ i, |(a i:ℝ)|) ≤ M →
      ∀ {m : ℕ}, 0 < m → ((3*windowEnd N:ℕ):ℝ) ≤ (m:ℝ)^2 →
        |Real.log (ordinaryPrimeGenerator (m • a):ℝ)-(m:ℝ)^2*ordinaryPrimeContact a| ≤ D*(m:ℝ)^2 := by
  obtain ⟨C,hC,hs⟩ := ordinaryPrimeContact_sampling_at_mass hM
  refine ⟨C+7,by linarith only [hC],fun {N} a ha {m} hm hL => ?_⟩
  by_cases hz : a = 0
  · subst a
    rw [log_ordinaryPrimeGenerator]
    simp [ordinaryPrimeContact,integratedContact,contactMultiplicity,degreeSample,packet,splineSource]
    <;> positivity
  let r := resolution (m • a)
  let t := (m:ℝ)^2
  let L := 3*windowEnd N
  have hr : m ≤ r := by
    dsimp only [r]
    rw [resolution_smul]
    exact Nat.le_mul_of_pos_right _ (resolution_pos hz)
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr (hm.trans_le hr)
  have hroot : Real.sqrt L ≤ r := ((Real.sqrt_le_iff).mpr ⟨Nat.cast_nonneg _,hL⟩).trans (by exact_mod_cast hr)
  have hmesh : (t*C/r)*Real.sqrt L ≤ t*C := (mul_le_mul_of_nonneg_left hroot
    (div_nonneg (mul_nonneg (sq_nonneg _) hC) hr'.le)).trans_eq (div_mul_cancel₀ _ hr'.ne')
  have he := abs_le.mp (hs N a ha m (hm.trans_le hr))
  obtain ⟨hf,hf'⟩ := ordinaryFloorLoss_bounds (m • a)
  change ((L:ℝ) ≤ t) at hL
  change ordinaryFloorLoss (m • a) ≤ 7*(L:ℝ) at hf'
  change |Real.log (ordinaryPrimeGenerator (m • a):ℝ)-t*ordinaryPrimeContact a| ≤ (C+7)*t
  rw [abs_le]
  constructor <;> linarith only [he.1,he.2,hf,hf',hmesh,hL]

/-- The threshold depends only on the prime horizon, and the additive
allowance per squared multiplicity depends only on total coefficient mass. -/
theorem poleBalanced_single_multiplicity_error {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} (a : Fin N → ℤ), positivePoleDegree a = 0 →
      (∑ i, |(a i:ℝ)|) ≤ M → ∀ {m : ℕ}, 0 < m →
      ((3*windowEnd N:ℕ):ℝ) ≤ (m:ℝ)^2 →
      |Real.log (ordinaryPrimeGenerator (m • a):ℝ)+(m:ℝ)^2*integerProbe N a| ≤ K*(m:ℝ)^2 := by
  obtain ⟨D,hD,hd⟩ := sampling_above_horizon hM
  obtain ⟨C,hC,hc⟩ := poleBalanced_ordinary_error
  let E := C*M^2+4
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨2*D+E,by positivity,fun {N} a hbal ha {m} hm hL => ?_⟩
  let P := ordinaryPrimeContact a
  let Q := integerProbe N a
  have he : C*(∑ i, |(a i:ℝ)|)^2+4 ≤ E := add_le_add_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) ha 2) hC) _
  have hdeg : |P+Q| ≤ D+E := by
    let L := 3*windowEnd N
    obtain ⟨j,hj,hj'⟩ := ((hc N a hbal).and (eventually_ge_atTop (L+1))).exists
    have hjpos : 0 < j := by omega
    have hj2 : L ≤ j^2 := (show L ≤ j by omega).trans
      (by simpa only [sq] using Nat.le_mul_self j)
    have hjs := abs_le.mp (hd a ha hjpos (by exact_mod_cast hj2))
    have hjq := abs_le.mp (hj.trans (mul_le_mul_of_nonneg_right he (sq_nonneg (j:ℝ))))
    have ht : 0 < (j:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hjpos)
    rw [abs_le]
    constructor <;> apply (mul_le_mul_iff_right₀ ht).mp <;> dsimp only [P,Q] <;>
      linarith only [hjs.1,hjs.2,hjq.1,hjq.2]
  let t := (m:ℝ)^2
  let z := Real.log (ordinaryPrimeGenerator (m • a):ℝ)
  have hsample : |z-t*P| ≤ D*t := hd a ha hm hL
  change |z+t*Q| ≤ (2*D+E)*t
  rw [show z+t*Q=(z-t*P)+t*(P+Q) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
  linarith only [hsample,mul_le_mul_of_nonneg_left hdeg (sq_nonneg (m:ℝ))]

/-- A prescribed positive integer multiplicity at each horizon. -/
def horizonMultiplicity (N : ℕ) := ⌈Real.sqrt (3*windowEnd N : ℕ)⌉₊+1

theorem horizonMultiplicity_spec (N : ℕ) : 0 < horizonMultiplicity N ∧
    ((3*windowEnd N:ℕ):ℝ) ≤ (horizonMultiplicity N:ℝ)^2 := by
  refine ⟨Nat.succ_pos _,?_⟩
  have hl : Real.sqrt (3*windowEnd N:ℕ) ≤ (horizonMultiplicity N:ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (Nat.le_succ _))
  exact ((Real.sqrt_le_iff).mp hl).2

/-- On any bounded-mass family in the pole hyperplane a uniform lower
Weil bound is equivalent to one rational comparison for each member. -/
theorem lower_degree_iff_horizon_power {ι : Type*} (N : ι → ℕ) (a : (i : ι) → Fin (N i) → ℤ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, positivePoleDegree (a i) = 0)
    (hmass : ∀ i, (∑ j, |(a i j:ℝ)|) ≤ M) :
    (∃ A : ℝ, ∀ i, -A ≤ integerProbe (N i) (a i)) ↔
    ∃ B : ℕ, 0 < B ∧ ∀ i, let m := horizonMultiplicity (N i)
      ordinaryPrimeGenerator (m • a i) ≤ (B:ℚ)^(m^2) := by
  obtain ⟨K,_,h⟩ := poleBalanced_single_multiplicity_error hM
  have he (i : ι) := h (a i) (hb i) (hmass i)
    (horizonMultiplicity_spec (N i)).1 (horizonMultiplicity_spec (N i)).2
  have hp (i : ι) {B : ℕ} (hB : 0 < B) :=
    generator_le_power_iff (horizonMultiplicity (N i) • a i) hB 1 (horizonMultiplicity (N i))
  simp only [one_mul,Nat.cast_one,one_pow,mul_one] at hp
  constructor
  · rintro ⟨A,hA⟩
    let B := ⌈Real.exp (K+A)⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hl : K+A ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
    refine ⟨B,hB,fun i => (hp i hB).mpr ?_⟩
    have ht := sq_nonneg (horizonMultiplicity (N i):ℝ)
    linarith only [(abs_le.mp (he i)).2,mul_le_mul_of_nonneg_right hl ht,
      mul_le_mul_of_nonneg_right (hA i) ht]
  · rintro ⟨B,hB,hB'⟩
    refine ⟨K+Real.log B,fun i => ?_⟩
    have ht := sq_pos_of_pos (Nat.cast_pos.mpr (horizonMultiplicity_spec (N i)).1 : (0:ℝ) < _)
    apply (mul_le_mul_iff_right₀ ht).mp
    linarith only [(abs_le.mp (he i)).1,(hp i hB).mp (hB' i)]

end GaloisForLFunctions.CountingHolography.Sections
