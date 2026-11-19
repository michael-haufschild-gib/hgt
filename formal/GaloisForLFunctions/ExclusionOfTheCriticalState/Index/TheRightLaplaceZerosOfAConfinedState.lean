import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheSecondConfinedStateSeesEveryRightZero

/-!
# The right Laplace zeros of a confined state

A Laplace zero in the upper right quadrant supplies two real resolvent components.
At distinct zeros these planes together are strictly negative. The quadratic
factor for a conjugate pair cancels its own plane while increasing the energy
and preserving every other coefficient's nonvanishing.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- One representative per nonreal conjugate pair of open-right Laplace zeros. -/
abbrev UpperLaplaceZeros (F : ℝ → ℝ) :=
  {z : ℂ // 0 < z.re ∧ 0 < z.im ∧ negativeHalfLineLaplace (cx F) z = 0}

namespace UpperLaplaceZeros

variable {F : ℝ → ℝ}

private def a (z : UpperLaplaceZeros F) := z.val.re / Real.pi
private def b (z : UpperLaplaceZeros F) := z.val.im / (2 * Real.pi)

private theorem rate (z : UpperLaplaceZeros F) : modulatedLaplaceRate (a z) (b z) = z.val := by
  have hx : Real.pi * a z = z.val.re := by unfold a; field_simp
  have hy : (2 * Real.pi) * b z = z.val.im := by unfold b; field_simp
  unfold modulatedLaplaceRate
  rw [hx, hy]
  exact Complex.re_add_im _

/-- A coefficient selects a real component of the complex causal resolvent. -/
def component (z : UpperLaplaceZeros F) (c : ℂ) := resolventComponent (a z) (b z) c F

theorem domain_component (z : UpperLaplaceZeros F) (hF : CriticalHalfLineEnergyDomain F) (c : ℂ) :
    CriticalHalfLineEnergyDomain (component z c) :=
  domain_resolventComponent (a := a z) (b := b z) (div_pos z.property.1 Real.pi_pos) hF
    (by rw [rate]; exact z.property.2.2) c

private theorem component_neg {R : ℝ} (hr : 0 < R) (hF : IsConfinedNullVector R F)
    (z : UpperLaplaceZeros F) {c : ℂ} (hc : c ≠ 0) :
    criticalHalfLineFullEnergy R (component z c) < 0 :=
  hF.negative_resolventComponent hr (a := a z) (b := b z) (div_pos z.property.1 Real.pi_pos)
    (div_ne_zero z.property.2.1.ne' (mul_ne_zero (by norm_num) Real.pi_ne_zero))
    (by rw [rate]; exact z.property.2.2) hc

/-- Real resolvent profile associated with a finite set of conjugate pairs. -/
def profile (s : Finset (UpperLaplaceZeros F)) (c : UpperLaplaceZeros F → ℂ) (u : ℝ) : ℝ :=
  ∑ z ∈ s, component z (c z) u

variable (s : Finset (UpperLaplaceZeros F))

theorem domain_profile (hF : CriticalHalfLineEnergyDomain F) (c : UpperLaplaceZeros F → ℂ) :
    CriticalHalfLineEnergyDomain (profile s c) := by
  change CriticalHalfLineEnergyDomain (fun u => ∑ z ∈ s, component z (c z) u)
  simpa only [one_mul] using criticalHalfLineEnergyDomain_finsetSum s
    (fun z => domain_component z hF (c z)) (fun _ => 1)

private theorem profile_add_scaled (c d : UpperLaplaceZeros F → ℂ) (t : ℝ) :
    profile s (fun z => c z + (t : ℂ) * d z) =
      fun u => profile s c u + t * profile s d u := by
  funext u
  simp only [profile, component, resolventComponent, add_mul, mul_assoc, Complex.add_re,
    Complex.re_ofReal_mul, Finset.sum_add_distrib, Finset.mul_sum]

private theorem laplace_admissible {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {q : ℂ} (hq : |q.re| ≤ 1/2) : Integrable (fun u : ℝ => Complex.exp (q * u) * cx G u) :=
  integrable_complexLaplaceWeighted_of_halfLine_memLp hq hG.memLp_complex hG.memLp_weightedComplex
    (fun u hu => by change (G u : ℂ) = 0; rw [hG.support u hu, Complex.ofReal_zero])

private theorem laplace_profile (hF : CriticalHalfLineEnergyDomain F)
    (c : UpperLaplaceZeros F → ℂ) {q : ℂ} (hq : |q.re| ≤ 1/2) :
    negativeHalfLineLaplace (cx (profile s c)) q =
      ∑ z ∈ s, negativeHalfLineLaplace (cx (component z (c z))) q := by
  unfold negativeHalfLineLaplace
  rw [← integral_finsetSum s fun z _ => laplace_admissible (domain_component z hF (c z)) hq]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by simp only [cx, profile, Complex.ofReal_sum, Finset.mul_sum]

private theorem laplace_add_scaled {G H : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hH : CriticalHalfLineEnergyDomain H) {q : ℂ} (hq : |q.re| ≤ 1/2) (t : ℝ) :
    negativeHalfLineLaplace (cx (fun u => G u + t * H u)) q =
      negativeHalfLineLaplace (cx G) q + (t : ℂ) * negativeHalfLineLaplace (cx H) q := by
  unfold negativeHalfLineLaplace
  rw [← integral_const_mul, ← integral_add (laplace_admissible hG hq)
    ((laplace_admissible hH hq).const_mul (t : ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by simp only [cx, Complex.ofReal_add, Complex.ofReal_mul]; ring

/-- Multiplication by the individual rates pairs nonpositively against every
coefficient vector, because the input state disappears from its weak equation. -/
private theorem mixed_rate_nonpos {R : ℝ} (hr : 0 < R) (hF : IsConfinedNullVector R F)
    (c : UpperLaplaceZeros F → ℂ) :
    criticalHalfLineMixedEnergy R (profile s (fun z => z.val * c z)) (profile s c) ≤ 0 := by
  let d := fun z : UpperLaplaceZeros F => z.val * c z
  let t : ℝ := -(Real.pi * ∑ z ∈ s, (c z).re)
  have hU := domain_profile s hF.1 c
  have hV := domain_profile s hF.1 d
  have hj (q : ℂ) (hq : |q.re| ≤ 1/2) :
      negativeHalfLineLaplace (cx (fun u => profile s d u + t * F u)) q =
        q * negativeHalfLineLaplace (cx (profile s c)) q := by
    rw [laplace_add_scaled hV hF.1 hq, laplace_profile s hF.1 d hq, laplace_profile s hF.1 c hq,
      Finset.mul_sum]
    have hl (z : UpperLaplaceZeros F) :
        q * negativeHalfLineLaplace (cx (component z (c z))) q =
          negativeHalfLineLaplace (cx (component z (d z))) q -
            (Real.pi : ℂ) * (c z).re * negativeHalfLineLaplace (cx F) q := by
      have h := laplace_mul_resolventComponent (div_pos z.property.1 Real.pi_pos) hF.1
        (a := a z) (b := b z) (by rw [rate]; exact z.property.2.2) (c z) hq
      rwa [rate] at h
    simp_rw [hl]
    rw [Finset.sum_sub_distrib]
    dsimp only [t]
    push_cast
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have he := confinedMixedEnergy_laplace_factor (hV.add_const_mul hF.1 t) hU hj R
  rw [criticalHalfLineMixedEnergy_add_const_mul_left R hV hF.1 hU, hF.2.2 _ hU,
    mul_zero, add_zero, criticalHalfLineExponentialPair_self] at he
  exact he.trans_le (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (by norm_num) (criticalAliasCoefficient_positive hr).le))
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))

private def plusFactor (w z : ℂ) := (z + w) * (z + (starRingEnd ℂ) w)
private def minusFactor (w z : ℂ) := (z - w) * (z - (starRingEnd ℂ) w)

private theorem factor_expand (w z : ℂ) :
    plusFactor w z = z*z + (Complex.normSq w : ℂ) + (2 * (w.re : ℂ)) * z ∧
    minusFactor w z = z*z + (Complex.normSq w : ℂ) - (2 * (w.re : ℂ)) * z := by
  have h := Complex.add_conj w
  have k := Complex.mul_conj w
  push_cast at h
  rw [← h, ← k]
  simp only [plusFactor, minusFactor]
  constructor <;> ring

private theorem plus_ne_zero (w z : UpperLaplaceZeros F) : plusFactor w.val z.val ≠ 0 := by
  apply mul_ne_zero <;> intro e <;> have h := congrArg Complex.re e <;>
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at h <;>
    exact (add_pos z.property.1 w.property.1).ne' h

private theorem minus_ne_zero {w z : UpperLaplaceZeros F} (hz : z ≠ w) :
    minusFactor w.val z.val ≠ 0 := by
  refine mul_ne_zero (sub_ne_zero.mpr (fun e => hz (Subtype.ext e))) (sub_ne_zero.mpr ?_)
  intro he
  have h := congrArg Complex.im he
  rw [Complex.conj_im] at h
  linarith only [h, z.property.2.1, w.property.2.1]

/-- The factors reflected across the imaginary axis satisfy the energy
inequality on the entire sum. The factor on the right kills the chosen pair. -/
private theorem factor_energy_le {R : ℝ} (hr : 0 < R) (hF : IsConfinedNullVector R F)
    (w : UpperLaplaceZeros F) (d : UpperLaplaceZeros F → ℂ) :
    criticalHalfLineFullEnergy R (profile s fun z => plusFactor w.val z.val * d z) ≤
      criticalHalfLineFullEnergy R (profile s fun z => minusFactor w.val z.val * d z) := by
  let N := Complex.normSq w.val
  let p := 2 * w.val.re
  let v := fun z : UpperLaplaceZeros F => z.val * d z
  let v₂ := fun z : UpperLaplaceZeros F => z.val * v z
  let e := fun z : UpperLaplaceZeros F => v₂ z + (N : ℂ) * d z
  have hp : 0 ≤ p := mul_nonneg (by norm_num) w.property.1.le
  have hN : 0 ≤ N := Complex.normSq_nonneg _
  have h₁ := mixed_rate_nonpos s hr hF d
  have h₂ := mixed_rate_nonpos s hr hF v
  have hmix : criticalHalfLineMixedEnergy R (profile s e) (profile s v) ≤ 0 := by
    dsimp only [e]
    rw [profile_add_scaled s v₂ d N, criticalHalfLineMixedEnergy_add_const_mul_left R
      (domain_profile s hF.1 v₂) (domain_profile s hF.1 d) (domain_profile s hF.1 v)]
    rw [criticalHalfLineMixedEnergy_comm R (profile s d) (profile s v)]
    exact add_nonpos h₂ (mul_nonpos_of_nonneg_of_nonpos hN h₁)
  have hplus : (fun z : UpperLaplaceZeros F => plusFactor w.val z.val * d z) =
      fun z => e z + (p : ℂ) * v z := by
    funext z; rw [(factor_expand _ _).1]; dsimp only [e,v₂,v,N,p]; push_cast; ring
  have hminus : (fun z : UpperLaplaceZeros F => minusFactor w.val z.val * d z) =
      fun z => e z + ((-p : ℝ) : ℂ) * v z := by
    funext z; rw [(factor_expand _ _).2]; dsimp only [e,v₂,v,N,p]; push_cast; ring
  rw [hplus, hminus, profile_add_scaled s e v p, profile_add_scaled s e v (-p),
    criticalHalfLineFullEnergy_add_const_mul R (domain_profile s hF.1 e) (domain_profile s hF.1 v),
    criticalHalfLineFullEnergy_add_const_mul R (domain_profile s hF.1 e) (domain_profile s hF.1 v)]
  rw [neg_sq]
  linarith only [mul_nonpos_of_nonneg_of_nonpos hp hmix]

/-- Independent complex coefficients at any finite set of distinct upper-right
Laplace zeros generate two strictly negative real directions per zero. -/
theorem profile_energy_neg {R : ℝ} (hr : 0 < R) (hF : IsConfinedNullVector R F)
    (c : UpperLaplaceZeros F → ℂ) (hc : ∃ z ∈ s, c z ≠ 0) :
    criticalHalfLineFullEnergy R (profile s c) < 0 := by
  classical
  obtain ⟨i, hi, hci⟩ := hc
  have keep (t : Finset (UpperLaplaceZeros F)) (hit : i ∉ t)
      (v : UpperLaplaceZeros F → ℂ) (hv : v i ≠ 0) :
      criticalHalfLineFullEnergy R (profile (insert i t) v) < 0 := by
    induction t using Finset.induction_on generalizing v with
    | empty =>
      have he : profile (insert i ∅) v = component i (v i) := by funext u; simp [profile]
      rw [he]
      exact component_neg hr hF i hv
    | insert j t hj ih =>
      have hij : i ≠ j := fun h => hit (by simp [h])
      have hi' : i ∉ t := fun h => hit (Finset.mem_insert_of_mem h)
      let d := fun z : UpperLaplaceZeros F => v z / plusFactor j.val z.val
      let g := fun z : UpperLaplaceZeros F => minusFactor j.val z.val * d z
      have hgi : g i ≠ 0 := mul_ne_zero (minus_ne_zero hij) (div_ne_zero hv (plus_ne_zero j i))
      have hgj : g j = 0 := by simp [g, minusFactor]
      have hleft : (fun z : UpperLaplaceZeros F => plusFactor j.val z.val * d z) = v := by
        funext z; dsimp only [d]; rw [mul_comm, div_mul_cancel₀ _ (plus_ne_zero j z)]
      have hright : profile (insert i (insert j t)) g = profile (insert i t) g := by
        funext u
        rw [Finset.insert_comm, profile, Finset.sum_insert (by simpa [Ne.symm hij] using hj), hgj]
        simp [component, resolventComponent, profile]
      have h := factor_energy_le (insert i (insert j t)) hr hF j d
      rw [hleft] at h
      change _ ≤ criticalHalfLineFullEnergy R (profile (insert i (insert j t)) g) at h
      rw [hright] at h
      exact h.trans_lt (ih hi' g hgi)
  simpa only [Finset.insert_erase hi] using keep (s.erase i) (Finset.notMem_erase i s) c hci

#print axioms profile_energy_neg

end UpperLaplaceZeros
end GaloisForLFunctions.ExclusionOfTheCriticalState
