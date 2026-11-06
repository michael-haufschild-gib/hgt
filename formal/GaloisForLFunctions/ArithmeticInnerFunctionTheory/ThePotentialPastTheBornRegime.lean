import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheForwardMapFromPrimesToReflectors
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheDatumIsTheSzegoThreshold
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeAnchorFlow
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilChainIsOneScalarFlow

/-!
# The potential past the Born regime

How does the potential depend on the data? On a lattice the flow is a contraction followed by an additive kick, `artanh r_{n+1} = artanh(s r_n) − artanh γ_n`, so the potential of stage `n` is the kick `q_n = −artanh γ_n` (`latticeKick`).

* **Born at the vacuum** (`hasDerivAt_reflCoeff_vacuum`). At `κ = κ₀δ₀` a perturbation `η` moves reflector `n` by exactly `η(n + 1)/κ₀`. So each reflector reads its own echo, and the map from data to potential is linear to first order: this is the Born regime.
* **The Born defect** (`abs_schurParam_sub_le`, `abs_reflCoeff_sub_born_le`). In general `|β_n − κ(n + 1)| ≤ K(Π_{k<n}(1 + |γ_k|) − 1)`, with `K` bounding the earlier data, because the predictor has mass at most `Π(1 + |γ_k|) − 1` (`one_add_predMass_le`). So the Born regime lasts as long as the accumulated reflection is small.
* **The first correction** (`reflCoeff_one_sub_born`). `γ₁ − κ₂/κ₀ = κ₁²(κ₂ − κ₀)/(κ₀(κ₀² − κ₁²))`.
* **The tangent past the Born regime** (`hasDerivAt_latticeKick`, `hasDerivAt_latticeKick_weight`). At every positive stage the derivative of `q_n` is the forward map of the reflector divided by `1 − γ_n²`. The factor `1/(1 − γ²)` blows up at contact, and the echo is read through the collars of the whole predictor rather than at one lag.
* **The continuous potential** (`ae_canonicalPotential_eq_born_add`). Before contact `Ψ′ = (r′ + 2r) + (r′ + 2r) r²/(1 − r²)` almost everywhere: the linear Born term `r′ + 2r` plus an exact geometric correction, which is small only while `r` is.
-/

open Finset Filter Topology Set

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

noncomputable section

variable {κ η : ℤ → ℝ}

/-- The potential of stage `n`: the additive kick `q_n = −artanh γ_n`. -/
def latticeKick (κ : ℤ → ℝ) (n : ℕ) : ℝ := -Real.artanh (reflCoeff κ n)

/-- **The flow is a contraction plus the kick.** -/
theorem artanh_latticeReflection_succ_kick {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ}
    (hw : (s * latticeReflection κ s n) ^ 2 < 1) (hL : latticeLeftTrace κ s n ≠ 0)
    (hE : 0 < levinsonErr κ n) (hE' : 0 < levinsonErr κ (n + 1)) :
    Real.artanh (latticeReflection κ s (n + 1)) =
      Real.artanh (s * latticeReflection κ s n) + latticeKick κ n := by
  rw [artanh_latticeReflection_succ hs hw hL hE hE', latticeKick, sub_eq_add_neg]

/-! ### The vacuum -/

/-- The free medium. -/
def vacuum (κ₀ : ℝ) (d : ℤ) : ℝ := if d = 0 then κ₀ else 0

theorem vacuum_isEven (κ₀ : ℝ) : IsEvenSeq (vacuum κ₀) := fun d => by simp [vacuum]

theorem schurParam_vacuum (κ₀ : ℝ) (n : ℕ) : schurParam (vacuum κ₀) n = 0 := by
  have hne : ∀ m : ℕ, ((m : ℤ) + 1) ≠ 0 := fun m => by omega
  simp only [schurParam, schurCoupling, vacuum]
  rw [if_neg (hne n), zero_add]
  exact Finset.sum_eq_zero fun k _ => by rw [if_neg (hne k), zero_mul]

theorem reflCoeff_vacuum (κ₀ : ℝ) (n : ℕ) : reflCoeff (vacuum κ₀) n = 0 := by
  rw [reflCoeff, schurParam_vacuum, zero_div]

theorem levinsonErr_vacuum (κ₀ : ℝ) : ∀ n, levinsonErr (vacuum κ₀) n = κ₀
  | 0 => by simp [levinsonErr_zero, vacuum]
  | n + 1 => by
    rw [levinsonErr_succ, schurParam_vacuum, levinsonErr_vacuum κ₀ n]
    simp

theorem levinsonPred_vacuum (κ₀ : ℝ) : ∀ n, levinsonPred (vacuum κ₀) n = 0
  | 0 => by
    funext i
    exact i.elim0
  | n + 1 => by
    rw [levinsonPred_succ, reflCoeff_vacuum, levinsonPred_vacuum κ₀ n]
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp
    · simp

/-- The form on a vector carried by two sites. -/
theorem toeplitzForm_two_point (hη : IsEvenSeq η) {N : ℕ} {a b : Fin N} (hab : a ≠ b) {x : Fin N → ℝ}
    (hx : ∀ i, i ≠ a → i ≠ b → x i = 0) :
    toeplitzForm η N x = η 0 * (x a ^ 2 + x b ^ 2) + 2 * η ((b : ℤ) - a) * (x a * x b) := by
  classical
  have hsub : ∀ f : Fin N → ℝ, (∀ i, i ≠ a → i ≠ b → f i = 0) → ∑ i, f i = f a + f b := fun f hf => by
    rw [← Finset.sum_pair hab]
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hf i hi.1 hi.2
  have h1 : ∑ i : Fin N, ∑ j : Fin N, η ((i : ℤ) - j) * x i * x j =
      ∑ j : Fin N, η ((a : ℤ) - j) * x a * x j + ∑ j : Fin N, η ((b : ℤ) - j) * x b * x j :=
    hsub _ fun i hia hib => by simp only [hx i hia hib, mul_zero, zero_mul, Finset.sum_const_zero]
  have h2 : ∑ j : Fin N, η ((a : ℤ) - j) * x a * x j =
      η ((a : ℤ) - a) * x a * x a + η ((a : ℤ) - b) * x a * x b :=
    hsub _ fun j hja hjb => by simp only [hx j hja hjb, mul_zero]
  have h3 : ∑ j : Fin N, η ((b : ℤ) - j) * x b * x j =
      η ((b : ℤ) - a) * x b * x a + η ((b : ℤ) - b) * x b * x b :=
    hsub _ fun j hja hjb => by simp only [hx j hja hjb, mul_zero]
  have e : η ((a : ℤ) - b) = η ((b : ℤ) - a) := by rw [← hη, neg_sub]
  rw [toeplitzForm, h1, h2, h3, e, sub_self, sub_self]
  ring

/-- At the vacuum the collar is carried by the two end sites. -/
theorem toeplitzForm_collarVec_vacuum (hη : IsEvenSeq η) (κ₀ : ℝ) (n : ℕ) (ε : ℝ) :
    toeplitzForm η (n + 2) (collarVec (vacuum κ₀) n ε) = η 0 * (1 + ε ^ 2) + 2 * η ((n : ℤ) + 1) * ε := by
  have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := (Fin.last_pos).ne
  have hx : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → collarVec (vacuum κ₀) n ε i = 0 := by
    intro i h0 hl
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr h0
    rw [collarVec, Fin.cons_succ, levinsonPred_vacuum]
    refine Fin.lastCases (fun hj => ?_) (fun k _ => ?_) j hl
    · exact absurd (Fin.succ_last n) hj
    · simp
  have h0 : collarVec (vacuum κ₀) n ε 0 = 1 := by rw [collarVec, Fin.cons_zero]
  have hl : collarVec (vacuum κ₀) n ε (Fin.last (n + 1)) = ε := by
    rw [collarVec, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
  rw [toeplitzForm_two_point hη hne hx, h0, hl]
  have e : (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) : ℤ) - ((0 : Fin (n + 2)) : ℕ) = (n : ℤ) + 1 := by
    simp
  rw [e]
  ring

/-- **The Born regime.** At the vacuum a perturbation moves reflector `n` by its own echo. -/
theorem hasDerivAt_reflCoeff_vacuum {κ₀ : ℝ} (h0 : 0 < κ₀) (hη : IsEvenSeq η) (n : ℕ) :
    HasDerivAt (fun t => reflCoeff (tiltSeq (vacuum κ₀) η t) n) (η ((n : ℤ) + 1) / κ₀) 0 := by
  have hpd : ToeplitzPosDef (vacuum κ₀) (n + 1) :=
    (toeplitzForm_posDef_iff (vacuum_isEven κ₀) n).mpr fun k _ => by
      rw [levinsonErr_vacuum]
      exact h0
  refine (hasDerivAt_reflCoeff (vacuum_isEven κ₀) hη hpd).congr_deriv ?_
  rw [toeplitzForm_collarVec_vacuum hη, toeplitzForm_collarVec_vacuum hη, reflCoeff_vacuum,
    levinsonErr_vacuum]
  ring

/-! ### The Born defect -/

/-- The mass of the predictor. -/
def predMass (κ : ℤ → ℝ) (n : ℕ) : ℝ := ∑ k, |levinsonPred κ n k|

private theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_sub_le a 0 b
  simpa using h

theorem sum_abs_rev (n : ℕ) : ∑ k : Fin n, |levinsonPred κ n (Fin.rev k)| = predMass κ n :=
  Equiv.sum_comp Fin.revPerm fun k => |levinsonPred κ n k|

/-- One Levinson step multiplies the mass by at most `1 + |γ_n|`. -/
theorem one_add_predMass_succ_le (n : ℕ) :
    1 + predMass κ (n + 1) ≤ (1 + predMass κ n) * (1 + |reflCoeff κ n|) := by
  have hb : ∑ k : Fin n, |levinsonPred κ n k - reflCoeff κ n * levinsonPred κ n (Fin.rev k)| ≤
      predMass κ n + |reflCoeff κ n| * predMass κ n := by
    calc ∑ k : Fin n, |levinsonPred κ n k - reflCoeff κ n * levinsonPred κ n (Fin.rev k)|
        ≤ ∑ k : Fin n, (|levinsonPred κ n k| + |reflCoeff κ n| * |levinsonPred κ n (Fin.rev k)|) :=
          Finset.sum_le_sum fun k _ => by
            rw [← abs_mul]
            exact abs_sub_le_add _ _
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_abs_rev, predMass]
  have e : predMass κ (n + 1) =
      ∑ k : Fin n, |levinsonPred κ n k - reflCoeff κ n * levinsonPred κ n (Fin.rev k)| + |reflCoeff κ n| := by
    rw [predMass, levinsonPred_succ, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, abs_neg]
  rw [e]
  nlinarith

/-- **The predictor has mass at most the accumulated reflection.** -/
theorem one_add_predMass_le (n : ℕ) :
    1 + predMass κ n ≤ ∏ k ∈ Finset.range n, (1 + |reflCoeff κ k|) := by
  induction n with
  | zero => simp [predMass]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact (one_add_predMass_succ_le n).trans (mul_le_mul_of_nonneg_right ih (by positivity))

/-- **The Born defect of a Schur parameter.** -/
theorem abs_schurParam_sub_le {K : ℝ} (hK0 : 0 ≤ K) {n : ℕ}
    (hK : ∀ k : ℕ, k < n → |κ ((k : ℤ) + 1)| ≤ K) :
    |schurParam κ n - κ ((n : ℤ) + 1)| ≤ K * (∏ k ∈ Finset.range n, (1 + |reflCoeff κ k|) - 1) := by
  have e : schurParam κ n - κ ((n : ℤ) + 1) =
      ∑ k : Fin n, κ ((k : ℤ) + 1) * levinsonPred κ n (Fin.rev k) := by
    rw [schurParam, schurCoupling, add_sub_cancel_left]
  have h1 : |∑ k : Fin n, κ ((k : ℤ) + 1) * levinsonPred κ n (Fin.rev k)| ≤ K * predMass κ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← sum_abs_rev, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK k k.2) (abs_nonneg _)
  rw [e]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK0)
  linarith [one_add_predMass_le (κ := κ) n]

/-- **The Born defect of a reflector.** -/
theorem abs_reflCoeff_sub_born_le {K : ℝ} (hK0 : 0 ≤ K) {n : ℕ}
    (hK : ∀ k : ℕ, k < n → |κ ((k : ℤ) + 1)| ≤ K) (h0 : κ 0 ≠ 0) (hE : 0 < levinsonErr κ n) :
    |reflCoeff κ n - κ ((n : ℤ) + 1) / κ 0| ≤
      (K * (∏ k ∈ Finset.range n, (1 + |reflCoeff κ k|) - 1) +
        |κ ((n : ℤ) + 1)| * |1 - levinsonErr κ n / κ 0|) / levinsonErr κ n := by
  have hid : reflCoeff κ n - κ ((n : ℤ) + 1) / κ 0 =
      ((schurParam κ n - κ ((n : ℤ) + 1)) + κ ((n : ℤ) + 1) * (1 - levinsonErr κ n / κ 0)) /
        levinsonErr κ n := by
    rw [reflCoeff]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hE]
  refine div_le_div_of_nonneg_right ?_ hE.le
  have htri : |(schurParam κ n - κ ((n : ℤ) + 1)) + κ ((n : ℤ) + 1) * (1 - levinsonErr κ n / κ 0)| ≤
      |schurParam κ n - κ ((n : ℤ) + 1)| + |κ ((n : ℤ) + 1) * (1 - levinsonErr κ n / κ 0)| := by
    have h := abs_sub_le_add (schurParam κ n - κ ((n : ℤ) + 1)) (-(κ ((n : ℤ) + 1) * (1 - levinsonErr κ n / κ 0)))
    rwa [sub_neg_eq_add, abs_neg] at h
  rw [abs_mul] at htri
  linarith [abs_schurParam_sub_le hK0 hK]

/-- **The first correction to Born.** -/
theorem reflCoeff_one_sub_born (κ : ℤ → ℝ) (h0 : κ 0 ≠ 0) (h1 : κ 0 ^ 2 - κ 1 ^ 2 ≠ 0) :
    reflCoeff κ 1 - κ 2 / κ 0 = κ 1 ^ 2 * (κ 2 - κ 0) / (κ 0 * (κ 0 ^ 2 - κ 1 ^ 2)) := by
  rw [reflCoeff_one_eq κ h0 h1]
  field_simp
  ring

/-! ### The tangent past the Born regime -/

/-- The tangent of the potential from the tangent of the reflector. -/
theorem hasDerivAt_latticeKick_of {F : ℝ → ℤ → ℝ} {d : ℝ} {n : ℕ}
    (hd : HasDerivAt (fun t => reflCoeff (F t) n) d 0) (hγ : reflCoeff (F 0) n ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => latticeKick (F t) n) (-(d / (1 - reflCoeff (F 0) n ^ 2))) 0 := by
  have ha := CanonicalSystemOfTheWindowTower.hasDerivAt_artanh hγ
  have hc := (ha.comp 0 hd).fun_neg
  refine hc.congr_deriv ?_
  ring

/-- **The tangent of the potential.** The forward map of the reflector, divided by `1 − γ_n²`. -/
theorem hasDerivAt_latticeKick (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) (hγ : reflCoeff κ n ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => latticeKick (tiltSeq κ η t) n)
      (-(((toeplitzForm η (n + 2) (collarVec κ n 1) - toeplitzForm η (n + 2) (collarVec κ n (-1))) / 4 -
        reflCoeff κ n * toeplitzForm η (n + 1) (levinsonVec κ n)) / levinsonErr κ n /
          (1 - reflCoeff κ n ^ 2))) 0 := by
  have e : reflCoeff (tiltSeq κ η 0) n = reflCoeff κ n := by rw [tiltSeq_zero]
  have hγ' : reflCoeff (tiltSeq κ η 0) n ∈ Ioo (-1 : ℝ) 1 := by rwa [e]
  have hd := hasDerivAt_latticeKick_of (hasDerivAt_reflCoeff hκ hη h) hγ'
  rwa [e] at hd

/-- **The prime tangent of the potential.** -/
theorem hasDerivAt_latticeKick_weight {φ : ℝ → ℝ} {h r : ℝ} (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0)
    (lam : ℕ → ℝ) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {n : ℕ} (hpd : ToeplitzPosDef (weilSeqW lam φ h) (n + 1))
    (hγ : reflCoeff (weilSeqW lam φ h) n ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => latticeKick (weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h) n)
      (-(((toeplitzForm (primeEcho φ h n₀) (n + 2) (collarVec (weilSeqW lam φ h) n 1) -
          toeplitzForm (primeEcho φ h n₀) (n + 2) (collarVec (weilSeqW lam φ h) n (-1))) / 4 -
        reflCoeff (weilSeqW lam φ h) n *
          toeplitzForm (primeEcho φ h n₀) (n + 1) (levinsonVec (weilSeqW lam φ h) n)) /
        levinsonErr (weilSeqW lam φ h) n / (1 - reflCoeff (weilSeqW lam φ h) n ^ 2))) 0 := by
  have e0 : Function.update lam n₀ (lam n₀ + 0) = lam := by
    rw [add_zero, Function.update_eq_self]
  have hγ' : reflCoeff (weilSeqW (Function.update lam n₀ (lam n₀ + 0)) φ h) n ∈ Ioo (-1 : ℝ) 1 := by
    rwa [e0]
  have hd := hasDerivAt_latticeKick_of (F := fun t => weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h)
    (hasDerivAt_reflCoeff_weight hφ lam hn₀ hpd) hγ'
  simp only [e0] at hd
  exact hd

/-! ### The continuous potential -/

/-- **The potential before contact.** The linear Born term `r′ + 2r` and its exact geometric correction. -/
theorem ae_canonicalPotential_eq_born_add {base a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ CriticalHardyTheoryOfTheWindowCone.precontactSet)
    (hbase : base ∈ Icc a b) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b → ∀ ρ, HasDerivAt anchorReflection ρ x →
      HasDerivAt (canonicalPotential base)
        ((ρ + 2 * anchorReflection x) +
          (ρ + 2 * anchorReflection x) * anchorReflection x ^ 2 / (1 - anchorReflection x ^ 2)) x := by
  filter_upwards [ae_anchorReflection_riccati hab hs hbase] with x hx hxI ρ hρ
  have hmem := anchorReflection_mem (hs (Ioo_subset_Icc_self hxI))
  have hden : 1 - anchorReflection x ^ 2 ≠ 0 := by
    have : 0 < 1 - anchorReflection x ^ 2 := by nlinarith [hmem.1, hmem.2]
    exact this.ne'
  refine ((hx hxI).2 ρ hρ).congr_deriv ?_
  field_simp
  ring

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
