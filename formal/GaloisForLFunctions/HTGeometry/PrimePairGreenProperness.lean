import GaloisForLFunctions.HTGeometry.HypoexponentialGreenFormation
import GaloisForLFunctions.HTGeometry.DiagonalHistoryResponse
import GaloisForLFunctions.HTGeometry.CrowdedPrimeLogPairs

/-!
# Global all-prime pair properness of the Green-exactified response

Index the distinct prime pairs by `p < q`.  Unique factorization makes the endpoints `e_{pq}` of
`ℓ²(ℕ≥1)` pairwise distinct, so the Green-exactified response
`(𝒢_T c)(t) = ∑_{p<q} c_{p,q} H_{log p, log q}(t) e_{pq}` `(RGE.12)` is a diagonal history response.
Its channel energies `∫₀ᵀ H²` lie between the floor `c_T² = ∫₀ᵀ G_{log 2}²` (stochastic envelope,
`log p ≥ log 2`) and `T` (`H ≤ 1`).  Hence for every `T > 0`
`c_T² ‖c‖² ≤ ‖𝒢_T c‖² ≤ T ‖c‖²` `(RGE.13)`: `𝒢_T` is injective with closed range, its inverse
on the range has norm at most `c_T⁻¹`, `c_T² ≤ 𝒢_T* 𝒢_T ≤ T` `(RGE.14)`, and the inverse cost of a
response is `∑ |y_{p,q}|² / ∫₀ᵀ H²` in the orthonormal carrier `(RGE.15)`.

The intermediate Green inverse `Δ₋⁻¹ = (log q - log p)⁻¹` is unbounded over prime pairs, because
crowded prime pairs have logarithmic gaps tending to zero `(RGE.16)`.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- Distinct prime pairs `p < q`. -/
abbrev PrimePair : Type := {pq : ℕ × ℕ // pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2}

/-- Unique factorization: the product `pq` of primes `p < q` determines the pair. -/
theorem primePair_mul_injective : Function.Injective fun x : PrimePair => x.1.1 * x.1.2 := by
  rintro ⟨⟨p, q⟩, hp, hq, hpq⟩ ⟨⟨p', q'⟩, hp', hq', hpq'⟩ h
  simp only at h hpq hpq'
  have h1 : p ∣ p' * q' := ⟨q, h.symm⟩
  have h2 : p' ∣ p * q := ⟨q', h⟩
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h1 | h1
  · obtain rfl : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp h1
    obtain rfl : q = q' := Nat.eq_of_mul_eq_mul_left hp.pos h
    rfl
  · have e : p = q' := (Nat.prime_dvd_prime_iff_eq hp hq').mp h1
    rcases (Nat.Prime.dvd_mul hp').mp h2 with h2 | h2
    · have e' : p' = p := (Nat.prime_dvd_prime_iff_eq hp' hp).mp h2
      omega
    · have e' : p' = q := (Nat.prime_dvd_prime_iff_eq hp' hq).mp h2
      omega

namespace PrimePair

/-- The arithmetic endpoint `pq ∈ ℕ≥1`. -/
def endpoint (x : PrimePair) : ℕ+ := ⟨x.1.1 * x.1.2, Nat.mul_pos x.2.1.pos x.2.2.1.pos⟩

theorem endpoint_injective : Function.Injective endpoint := fun _ _ h =>
  primePair_mul_injective (congrArg PNat.val h)

/-- The lower log-grade `log p`. -/
def lo (x : PrimePair) : ℝ := Real.log x.1.1

/-- The upper log-grade `log q`. -/
def hi (x : PrimePair) : ℝ := Real.log x.1.2

theorem log_two_le_log_prime {p : ℕ} (hp : p.Prime) : Real.log 2 ≤ Real.log p :=
  Real.log_le_log two_pos (by exact_mod_cast hp.two_le)

theorem log_two_le_lo (x : PrimePair) : Real.log 2 ≤ x.lo := log_two_le_log_prime x.2.1

theorem log_two_le_hi (x : PrimePair) : Real.log 2 ≤ x.hi := log_two_le_log_prime x.2.2.1

theorem lo_pos (x : PrimePair) : 0 < x.lo := (Real.log_pos one_lt_two).trans_le x.log_two_le_lo

theorem hi_pos (x : PrimePair) : 0 < x.hi := (Real.log_pos one_lt_two).trans_le x.log_two_le_hi

theorem lo_lt_hi (x : PrimePair) : x.lo < x.hi :=
  Real.log_lt_log (by exact_mod_cast x.2.1.pos) (by exact_mod_cast x.2.2.2)

end PrimePair

/-- The Green-exactified pair histories `t ↦ H_{log p, log q}(t⁺) e_{pq}` `(RGE.12)`. -/
def greenPairFamily : HistoryFamily PrimePair where
  endpoint := PrimePair.endpoint
  endpoint_injective := PrimePair.endpoint_injective
  weight x t := greenExact x.lo x.hi (max t 0)
  continuous_weight x := (continuous_greenExact _ _).comp (continuous_id.max continuous_const)
  abs_weight_le x t := by
    have h0 := greenExact_nonneg x.lo_pos x.hi_pos (le_max_right t 0)
    have h1 := greenExact_le_one x.lo_pos x.hi_pos (le_max_right t 0)
    rw [abs_le]
    exact ⟨by linarith, h1⟩

/-- The channel energy is `∫₀ᵀ H_{log p, log q}(t)² dt`. -/
theorem greenPair_energy_eq {T : ℝ} (hT : 0 ≤ T) (x : PrimePair) :
    greenPairFamily.energy T x = ∫ t in (0 : ℝ)..T, greenExact x.lo x.hi t ^ 2 := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  show greenExact x.lo x.hi (max t 0) ^ 2 = _
  rw [max_eq_left ht.1]

/-- Every channel energy dominates the pair floor `c_T²`. -/
theorem pairFloor_le_energy {T : ℝ} (hT : 0 ≤ T) (x : PrimePair) :
    pairFloor T ≤ greenPairFamily.energy T x := by
  rw [greenPair_energy_eq hT]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine intervalIntegral.integral_mono_on hT
    (Continuous.intervalIntegrable (by unfold erlangThreeCDF; fun_prop) _ _)
    (Continuous.intervalIntegrable ((continuous_greenExact _ _).pow 2) _ _) fun t ht => ?_
  have h0 := (hasHalfLineCDF_erlangThree hl).nonneg t ht.1
  exact pow_le_pow_left₀ h0
    (erlangThreeCDF_le_greenExact hl x.log_two_le_lo x.log_two_le_hi ht.1) 2

/-- **Theorem 4.1, `(RGE.13)`**: `c_T² ‖c‖² ≤ ‖𝒢_T c‖² ≤ T ‖c‖²`. -/
theorem greenPair_frame {T : ℝ} (hT : 0 ≤ T) (c : HistoryFamily.Controls PrimePair) :
    pairFloor T * ‖c‖ ^ 2 ≤ ‖greenPairFamily.response T c‖ ^ 2 ∧
      ‖greenPairFamily.response T c‖ ^ 2 ≤ T * ‖c‖ ^ 2 :=
  greenPairFamily.frame_bounds hT (pairFloor_le_energy hT) (greenPairFamily.energy_le hT) c

theorem greenPair_injective {T : ℝ} (hT : 0 < T) :
    Function.Injective (greenPairFamily.response T) :=
  greenPairFamily.response_injective hT.le (pairFloor_pos hT) (pairFloor_le_energy hT.le)

theorem isClosed_range_greenPair {T : ℝ} (hT : 0 < T) :
    IsClosed (Set.range (greenPairFamily.response T)) :=
  greenPairFamily.isClosed_range_response hT.le (pairFloor_pos hT) (pairFloor_le_energy hT.le)

/-- The inverse on the range has norm at most `c_T⁻¹`. -/
theorem norm_le_pairFloor_inv_mul {T : ℝ} (hT : 0 < T) (c : HistoryFamily.Controls PrimePair) :
    ‖c‖ ≤ (Real.sqrt (pairFloor T))⁻¹ * ‖greenPairFamily.response T c‖ :=
  greenPairFamily.norm_le_inv_mul_response hT.le (pairFloor_pos hT) (pairFloor_le_energy hT.le) c

/-- **`(RGE.14)`**: `c_T² ≤ 𝒢_T* 𝒢_T ≤ T` as quadratic forms. -/
theorem greenPair_gram_bounds {T : ℝ} (hT : 0 ≤ T) (c : HistoryFamily.Controls PrimePair) :
    pairFloor T * ‖c‖ ^ 2 ≤
        RCLike.re ⟪(ContinuousLinearMap.adjoint (greenPairFamily.response T) ∘L
          greenPairFamily.response T) c, c⟫_ℂ ∧
      RCLike.re ⟪(ContinuousLinearMap.adjoint (greenPairFamily.response T) ∘L
          greenPairFamily.response T) c, c⟫_ℂ ≤ T * ‖c‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq]
  exact greenPair_frame hT c

/-- **`(RGE.15)`: the inverse cost** `‖c‖² = ∑_{p<q} |⟨ψ_{p,q}, 𝒢_T c⟩|² / ∫₀ᵀ H²`. -/
theorem greenPair_inverseCost {T : ℝ} (hT : 0 < T) (c : HistoryFamily.Controls PrimePair) :
    ‖c‖ ^ 2 = ∑' x, ‖⟪greenPairFamily.carrier T x, greenPairFamily.response T c⟫_ℂ‖ ^ 2 /
      ∫ t in (0 : ℝ)..T, greenExact x.lo x.hi t ^ 2 := by
  rw [greenPairFamily.inverseCost hT.le
    (fun x => (pairFloor_pos hT).trans_le (pairFloor_le_energy hT.le x)) c]
  exact tsum_congr fun x => by rw [greenPair_energy_eq hT.le]

/-- **`(RGE.16)`: the intermediate Green inverse is unbounded.**  The relative-grade inverse
`(log q - log p)⁻¹` is unbounded over prime pairs. -/
theorem not_bddAbove_inv_logGap :
    ¬ BddAbove (Set.range fun x : PrimePair => (x.hi - x.lo)⁻¹) := by
  rintro ⟨M, hM⟩
  obtain ⟨P⟩ := CrowdedPairs.nonempty
  have hpair : ∀ j, (P.b j - P.a j)⁻¹ ≤ M := fun j =>
    hM ⟨⟨⟨P.p j, P.q j⟩, P.p_prime j, P.q_prime j, by
      have h := P.a_lt_b j
      unfold CrowdedPairs.a CrowdedPairs.b at h
      exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (P.p_prime j).pos)
        (by exact_mod_cast (P.q_prime j).pos)).mp h⟩, rfl⟩
  have hgap : ∀ j, 0 < P.b j - P.a j := fun j => sub_pos.mpr (P.a_lt_b j)
  have hM0 : 0 < M := (inv_pos.mpr (hgap 0)).trans_le (hpair 0)
  have hbase : Tendsto P.base atTop atTop := by
    rw [show P.base = fun j : ℕ => P.R₀ + 4 * (j : ℝ) from funext P.base_eq]
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hη : Tendsto P.η atTop (𝓝 0) := (tendsto_crowdWidth P.hc).comp hbase
  obtain ⟨j, hj⟩ := (hη.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < M⁻¹ / 3))).exists
  have h1 : M⁻¹ ≤ P.b j - P.a j := by
    rw [inv_le_comm₀ hM0 (hgap j)]
    exact hpair j
  linarith [P.b_sub_a_le j]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
