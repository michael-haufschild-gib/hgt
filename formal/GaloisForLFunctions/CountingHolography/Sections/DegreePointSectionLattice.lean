import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsIsThePoleMinusWeilsFunctional
import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOfARationalLattice

/-!
# A rational section lattice for the degree-point pairing

The contact row at each prime power gives one signed integral valuation.
Their product generates a fractional ideal of ℤ in ℚ. At infinity the metric
uses the two sampled degrees and the jet pairing with its diagonal subtraction.
Rounding the valuations costs at most one copy of each prime-power weight,
independently of the multiplicities and the mesh.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory AbsoluteGeometryOfSpecZ Zeta23
open scoped ArithmeticFunction.vonMangoldt

/-- At a prime power the residue prime imposes the local condition. -/
def contactBase (k : ℕ) : ℕ := if IsPrimePow k then k.minFac else 1

theorem contactBase_pos (k : ℕ) : 0 < contactBase k := by
  unfold contactBase
  split_ifs
  · exact Nat.minFac_pos _
  · exact one_pos

theorem log_contactBase (k : ℕ) : Real.log (contactBase k) = Λ k := by
  rw [ArithmeticFunction.vonMangoldt_apply, contactBase]
  split_ifs <;> simp

/-- Signed multiplicity of the contact, before rounding. Both orientations contribute. -/
def contactMultiplicity (f : ℝ → ℝ) (L n k : ℕ) : ℝ :=
  2 / Real.sqrt k * ∑ j ∈ Ioc n (n + L*n),
    degreeSample f n j * degreeSample f n (j*k) / j

/-- Positive rational generator of the fractional ideal imposed at all finite places. -/
def contactGenerator (f : ℝ → ℝ) (L n : ℕ) : ℚ :=
  ∏ k ∈ Icc 2 L, (contactBase k : ℚ) ^ ⌊contactMultiplicity f L n k⌋

theorem contactGenerator_pos (f : ℝ → ℝ) (L n : ℕ) : 0 < contactGenerator f L n :=
  prod_pos fun k _ => zpow_pos (by exact_mod_cast contactBase_pos k) _

theorem log_contactGenerator (f : ℝ → ℝ) (L n : ℕ) :
    Real.log (contactGenerator f L n : ℝ) =
      ∑ k ∈ Icc 2 L, (⌊contactMultiplicity f L n k⌋ : ℤ) * (Λ k : ℝ) := by
  unfold contactGenerator
  push_cast
  rw [Real.log_prod (fun k _ => (zpow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℝ) < _) _).ne')]
  simp only [Real.log_zpow, log_contactBase]

theorem contact_rounding_bounds (f : ℝ → ℝ) (L n : ℕ) :
    0 ≤ 2 * degreeContact f L n - Real.log (contactGenerator f L n : ℝ) ∧
    2 * degreeContact f L n - Real.log (contactGenerator f L n : ℝ) ≤ ∑ k ∈ Icc 2 L, Λ k := by
  have he : 2 * degreeContact f L n - Real.log (contactGenerator f L n : ℝ) =
      ∑ k ∈ Icc 2 L, (contactMultiplicity f L n k - ⌊contactMultiplicity f L n k⌋) * Λ k := by
    rw [degreeContact, mul_sum, log_contactGenerator, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    unfold contactMultiplicity contactWeight
    ring
  rw [he]
  exact ⟨sum_nonneg fun k _ => mul_nonneg (sub_nonneg.mpr (Int.floor_le _))
    ArithmeticFunction.vonMangoldt_nonneg, sum_le_sum fun k _ =>
      mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (by linarith [Int.lt_floor_add_one (contactMultiplicity f L n k)])⟩

/-- Degree at one pole on the logarithmic mesh. -/
def sampledDegree (f : ℝ → ℝ) (L n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Ioc n (n + L*n), degreeSample f n j * Real.exp (t * Real.log ((j : ℝ) / n)) / j

/-- Logarithmic radius at infinity. The two degrees use the same samples as the jets. -/
def logRadius (f : ℝ → ℝ) (L n : ℕ) : ℝ :=
  2 * (sampledDegree f L n (-(1/2)) * sampledDegree f L n (1/2)) - degreeForm f L n

/-- Signed degree with the finite-place valuations before rounding. -/
def meshDegree (f : ℝ → ℝ) (L n : ℕ) : ℝ :=
  logRadius f L n - 2 * degreeContact f L n

private theorem tendsto_sampledDegree {f : ℝ → ℝ} (hf : Continuous f) {K : ℕ} (hK : 1 ≤ K)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) (t : ℝ) :
    Tendsto (sampledDegree f (3*K) · t) atTop (𝓝 (∫ u, f u * Real.exp (t*u))) := by
  have hL : 1 ≤ 3*K := by omega
  have hlog : 0 ≤ Real.log (1 + ((3*K : ℕ) : ℝ)) := Real.log_nonneg (by positivity)
  have he : (∫ u in (0:ℝ)..Real.log (1 + ((3*K : ℕ) : ℝ)), f u * Real.exp (t*u)) =
      ∫ u, f u * Real.exp (t*u) := by
    rw [intervalIntegral.integral_of_le hlog]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    obtain hu | hu := not_and_or.mp hu
    · rw [hs u (.inl ((not_lt.mp hu).trans (Real.log_nonneg (by norm_num)))), zero_mul]
    · have hk : (K : ℝ) ≤ 1 + ((3*K : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
      rw [hs u (.inr ((Real.log_le_log (by exact_mod_cast (by omega : 0 < K)) hk).trans
        (not_le.mp hu).le)), zero_mul]
  rw [← he]
  exact tendsto_degreeSum (hf.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))) hL

/-- With prime contacts, both poles and the logarithmic diagonal on one mesh,
the signed degree converges to the complete form. -/
theorem tendsto_meshDegree {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (meshDegree f (3*K)) atTop
      (𝓝 ((_root_.RHTower.weilFullFunctional (fun k => (Λ k : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)) := by
  have hp := ((tendsto_sampledDegree hf.continuous hK hs (-(1/2))).mul
    (tendsto_sampledDegree hf.continuous hK hs (1/2))).const_mul 2
  have hj := tendsto_degreeForm_add_contacts hf hc hK hs
  change Tendsto _ _ (𝓝 ((_root_.RHTower.weilPoleTerm
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re - _)) at hj
  rw [weilPoleTerm_packet hf.continuous hc] at hj
  have he (u : ℝ) : -(1 / 2 : ℝ) * u = -u / 2 := by ring
  have he' (u : ℝ) : (1 / 2 : ℝ) * u = u / 2 := by ring
  simp only [he, he'] at hp
  simpa only [meshDegree, logRadius, sub_add_eq_sub_sub, sub_sub_cancel] using hp.sub hj

/-- All three parts of the unrounded mesh use divisor multiplicities quadratically. -/
theorem meshDegree_mul (c : ℝ) (f : ℝ → ℝ) (L n : ℕ) :
    meshDegree (fun u => c * f u) L n = c ^ 2 * meshDegree f L n := by
  have hs (j : ℕ) : degreeSample (fun u => c * f u) n j = c * degreeSample f n j := rfl
  have hp (t : ℝ) : sampledDegree (fun u => c * f u) L n t = c * sampledDegree f L n t := by
    unfold sampledDegree
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [hs]; ring
  have hj : degreePairing (fun u => c * f u) L n = c^2 * degreePairing f L n := by
    unfold degreePairing
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by simp only [hs]; ring
  have hd : degreeForm (fun u => c * f u) L n = c^2 * degreeForm f L n := by
    unfold degreeForm
    rw [hj, mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by rw [hs]; ring
  have hc : degreeContact (fun u => c * f u) L n = c^2 * degreeContact f L n := by
    unfold degreeContact
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [mul_left_comm (c^2), mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by simp only [hs]; ring
  simp only [meshDegree, logRadius, hp, hd, hc]
  ring

end GaloisForLFunctions.CountingHolography.Sections
