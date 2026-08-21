/-
# Rational common times and rational coefficient witnesses

The common-time law produces, at unboundedly late deterministic times, a coefficient set of
positive Gaussian mass whose endpoints are far from every dictionary target.  Farness is strict and
the dictionary is finite, so on a subset of positive mass the margin is uniform.  A uniform margin
is stable: the generator is bounded on the coefficient box, so Duhamel's inequality lets the time
move to a nearby rational one and the coefficients move to nearby rational ones without losing
hardness.  Both moves are made inside the margin, so the witnesses are exactly rational.

Main results:
* `norm_pauliEnsemble_le_of_box`, `norm_pauliEnsemble_sub_le` — the generator bounds on the box.
* `exists_uniform_margin` — a strict miss of a finite dictionary is a uniform margin.
* `exists_rational_time_positive_mass` — **`(17)`--`(18)`**.
* `exists_rational_witness` — **`(19)`--`(20)`**.
-/
import GaloisForLFunctions.HTGeometry.CommonTimeCircuitHardness
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.ObserverInvisibleTubeShortcut

open MeasureTheory Filter Set Matrix
open scoped ENNReal Topology Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## Generator bounds on the coefficient box -/

section Generator

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The total weight of the ensemble. -/
def pauliWeightSum (w : (σ → Option (Fin 3)) → ℝ) : ℝ := ∑ P, |w P|

theorem pauliWeightSum_nonneg (w : (σ → Option (Fin 3)) → ℝ) : 0 ≤ pauliWeightSum w :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The generator is bounded on the coefficient box** by the total weight times the box radius. -/
theorem norm_pauliEnsemble_le_of_box (w : (σ → Option (Fin 3)) → ℝ)
    {J : (σ → Option (Fin 3)) → ℝ} {B : ℝ} (hJ : ∀ a, |J a| ≤ B) :
    ‖pauliEnsemble w J‖ ≤ pauliWeightSum w * B := by
  have hstep := opNorm_pauliCombination_le (σ := σ) (fun P => ((w P * J P : ℝ) : ℂ))
  refine le_trans hstep ?_
  rw [pauliWeightSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun P _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hJ P) (abs_nonneg _)

/-- **The generator is Lipschitz in the coefficients** with constant the total weight. -/
theorem norm_pauliEnsemble_sub_le (w : (σ → Option (Fin 3)) → ℝ)
    (J K : (σ → Option (Fin 3)) → ℝ) {rho : ℝ} (hrho : ∀ a, |J a - K a| ≤ rho) :
    ‖pauliEnsemble w J - pauliEnsemble w K‖ ≤ pauliWeightSum w * rho := by
  have hdiff : pauliEnsemble w J - pauliEnsemble w K
      = ∑ P, ((w P * (J P - K P) : ℝ) : ℂ) • finitePauliMatrix P := by
    rw [pauliEnsemble, pauliEnsemble, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hdiff]
  refine le_trans (opNorm_pauliCombination_le (σ := σ) _) ?_
  rw [pauliWeightSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun P _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hrho P) (abs_nonneg _)

end Generator

/-! ## Uniform margins and their stability -/

section Margin

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

/-- **A strict miss of a finite dictionary is a uniform margin.** -/
theorem exists_uniform_margin {H : Matrix I I ℂ} {psi : I → ℂ} {eps : ℝ}
    {Z : C → (I → ℂ)} {t : ℝ} (ht : t ∉ metricEasySet H psi eps Z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ, eps + δ ≤ dist (orbitVec H psi t) (eucVec (Z κ)) := by
  classical
  obtain ⟨κ₀, -, hκ₀⟩ := Finset.exists_min_image (Finset.univ : Finset C)
    (fun κ => dist (orbitVec H psi t) (eucVec (Z κ))) ⟨Classical.arbitrary C, Finset.mem_univ _⟩
  have hlt : eps < dist (orbitVec H psi t) (eucVec (Z κ₀)) := by
    by_contra hcon
    exact ht ⟨κ₀, not_lt.mp hcon⟩
  exact ⟨dist (orbitVec H psi t) (eucVec (Z κ₀)) - eps, by linarith,
    fun κ => by have := hκ₀ κ (Finset.mem_univ κ); linarith⟩

/-- Two generators evolve a state to points at distance at most the elapsed time times the
generator distance. -/
theorem dist_orbitVec_generator_le {H K : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    (hK : IsSelfAdjoint K) (psi : I → ℂ) (t : ℝ) :
    dist (orbitVec H psi t) (orbitVec K psi t) ≤ |t| * ‖H - K‖ * ‖eucVec psi‖ := by
  rw [dist_eq_norm]
  exact QuantumAlg.norm_unitaryEvolution_mulVec_sub_le hH hK t (eucVec psi)

end Margin

/-! ## Rational witnesses -/

variable {n q : ℕ} {C : Type} [Fintype C] [Nonempty C]

/-- **`(17)`--`(20)`.**  Beyond every horizon there is a positive rational time at which a set of
coefficient vectors of positive Gaussian mass is hard, and a rational coefficient vector in the
enlarged box which is itself hard at that time. -/
theorem exists_rational_common_time_witness
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - eps ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (horizon : ℝ) :
    ∃ (τ : ℚ) (Jq : (Fin n → Option (Fin 3)) → ℚ),
      horizon < (τ : ℝ) ∧ 0 < τ ∧ (∀ a, |(Jq a : ℝ)| ≤ B + 1) ∧
      0 < centredProductGaussian (Fin n → Option (Fin 3)) 1
          {J | (J, (τ : ℝ)) ∈ hardCircuitEvent w (zeroProductState (Fin n)) eps Z} ∧
      ((fun a => (Jq a : ℝ)), (τ : ℝ))
        ∈ hardCircuitEvent w (zeroProductState (Fin n)) eps Z := by
  classical
  have hOmega : finiteComplexInner (zeroProductState (Fin n)) (zeroProductState (Fin n)) = 1 := by
    rw [finiteComplexInner_self_eq_sum_normSq, sum_normSq_zeroProductState]
    norm_num
  have hOmeganorm : ‖eucVec (zeroProductState (Fin n))‖ = 1 := norm_eucVec_eq_one hOmega
  obtain ⟨G, hGmeas, hGsub, hGmass, hGwin, -⟩ :=
    exists_restricted_goodSet_common_time_hardness w hq hwsupp hw hwne hcard0 hB0 hB Z hZ
      heps0 heps1 hr hscale hM hcard hs
  -- the window-average floor is positive
  have hfloor : (0 : ℝ≥0∞) < (1 - ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))) / 2 := by
    have hexpneg : -((r : ℝ) / 2) < 0 := by
      have hone : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hlt : ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) < 1 := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexpneg)
    exact ENNReal.div_pos (by simp [tsub_eq_zero_iff_le, not_le.mpr hlt]) (by norm_num)
  have hfreq := frequently_lt_quenchedFixedTimeProb
    (hardCircuitEvent w (zeroProductState (Fin n)) eps Z ∩ G ×ˢ (Set.univ : Set ℝ))
    hfloor hGwin
  obtain ⟨t, htmass, htbig⟩ :=
    (hfreq.and_eventually (eventually_gt_atTop (max horizon 0))).exists
  -- decompose the positive-mass fibre by the size of the margin
  set Ak : ℕ → Set ((Fin n → Option (Fin 3)) → ℝ) := fun k =>
    {J | J ∈ G ∧ ∀ κ, eps + 1 / ((k : ℝ) + 1)
      ≤ dist (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) t) (eucVec (Z κ))}
    with hAkdef
  have hcover : {J | (J, t) ∈ hardCircuitEvent w (zeroProductState (Fin n)) eps Z ∩
      G ×ˢ (Set.univ : Set ℝ)} ⊆ ⋃ k, Ak k := by
    rintro J ⟨hJhard, hJG, -⟩
    obtain ⟨δ, hδ0, hδ⟩ := exists_uniform_margin (H := pauliEnsemble w J)
      (psi := zeroProductState (Fin n)) (eps := eps) (Z := Z) (t := t) hJhard
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ0
    exact Set.mem_iUnion.mpr ⟨k, hJG, fun κ => le_trans (by linarith [hk]) (hδ κ)⟩
  have hAkpos : ∃ k, 0 < centredProductGaussian (Fin n → Option (Fin 3)) 1 (Ak k) := by
    by_contra hcon
    push Not at hcon
    have hnull : ∀ k, centredProductGaussian (Fin n → Option (Fin 3)) 1 (Ak k) = 0 :=
      fun k => nonpos_iff_eq_zero.mp (hcon k)
    have := measure_mono_null hcover (measure_iUnion_null hnull)
    exact absurd this (by simpa [quenchedFixedTimeProb] using ne_of_gt htmass)
  obtain ⟨k, hkpos⟩ := hAkpos
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδdef
  have hδ0 : 0 < δ := by positivity
  -- the uniform generator bound on the good set
  set speed : ℝ := pauliWeightSum w * B with hspeeddef
  have hspeed0 : 0 ≤ speed := mul_nonneg (pauliWeightSum_nonneg w) hB0
  have hspeed : ∀ J ∈ G, ‖pauliEnsemble w J‖ ≤ speed := by
    intro J hJ
    exact norm_pauliEnsemble_le_of_box w (fun a => (hGsub hJ).1 a)
  -- move the time to a rational one
  set rho : ℝ := δ / (2 * (speed + 1)) with hrhodef
  have hrho0 : 0 < rho := by positivity
  obtain ⟨τ, hτ1, hτ2⟩ := exists_rat_btwn (show max (t - rho) (max horizon 0) < t by
    refine max_lt (by linarith) htbig)
  have hτhorizon : horizon < (τ : ℝ) := lt_of_le_of_lt (le_max_left _ _)
    (lt_of_le_of_lt (le_max_right _ _) hτ1)
  have hτpos : (0 : ℝ) < (τ : ℝ) := lt_of_le_of_lt (le_max_right _ _)
    (lt_of_le_of_lt (le_max_right _ _) hτ1)
  have hτclose : |(τ : ℝ) - t| ≤ rho := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have := lt_of_le_of_lt (le_max_left (t - rho) (max horizon 0)) hτ1
    linarith
  -- hardness survives the rational time
  have hAkτ : ∀ J ∈ Ak k, ∀ κ,
      eps + δ / 2 ≤ dist (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) (τ : ℝ))
        (eucVec (Z κ)) := by
    intro J hJ κ
    have hmove : dist (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) (τ : ℝ))
        (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) t) ≤ speed * |(τ : ℝ) - t| :=
      dist_orbitVec_le (Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_pauliEnsemble w J))
        hOmega (hspeed J hJ.1) _ _
    have hsmall : speed * |(τ : ℝ) - t| ≤ δ / 2 := by
      refine le_trans (mul_le_mul_of_nonneg_left hτclose hspeed0) ?_
      rw [hrhodef, mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 2 * (speed + 1))]
      nlinarith [hδ0.le, hspeed0]
    have htri := dist_triangle (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) t)
      (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) (τ : ℝ)) (eucVec (Z κ))
    have hcomm : dist (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) t)
        (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) (τ : ℝ))
        = dist (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) (τ : ℝ))
          (orbitVec (pauliEnsemble w J) (zeroProductState (Fin n)) t) := dist_comm _ _
    have hbase := hJ.2 κ
    rw [← hδdef] at hbase
    linarith [hmove, hsmall, hbase, htri, hcomm]
  have hmassτ : 0 < centredProductGaussian (Fin n → Option (Fin 3)) 1
      {J | (J, (τ : ℝ)) ∈ hardCircuitEvent w (zeroProductState (Fin n)) eps Z} := by
    refine lt_of_lt_of_le hkpos (measure_mono ?_)
    intro J hJ
    rintro ⟨κ, hκ⟩
    have := hAkτ J hJ κ
    linarith [hκ, hδ0]
  -- move the coefficients to rational ones
  obtain ⟨J₀, hJ₀⟩ := nonempty_of_measure_ne_zero (ne_of_gt hkpos)
  set lip : ℝ := |(τ : ℝ)| * pauliWeightSum w with hlipdef
  have hlip0 : 0 ≤ lip := mul_nonneg (abs_nonneg _) (pauliWeightSum_nonneg w)
  set rho' : ℝ := min 1 (δ / (4 * (lip + 1))) with hrho'def
  have hrho'0 : 0 < rho' := lt_min (by norm_num) (by positivity)
  have hchoose : ∀ a, ∃ x : ℚ, |J₀ a - (x : ℝ)| < rho' := fun a => exists_rat_near (J₀ a) hrho'0
  choose Jq hJq using hchoose
  refine ⟨τ, Jq, hτhorizon, by exact_mod_cast hτpos, ?_, hmassτ, ?_⟩
  · intro a
    have h1 : |J₀ a| ≤ B := (hGsub hJ₀.1).1 a
    have h2 : |J₀ a - (Jq a : ℝ)| < rho' := hJq a
    have h3 : rho' ≤ 1 := min_le_left _ _
    have := abs_sub_abs_le_abs_sub ((Jq a : ℝ)) (J₀ a)
    rw [abs_sub_comm ((Jq a : ℝ)) (J₀ a)] at this
    linarith
  · rintro ⟨κ, hκ⟩
    have hgen : ‖pauliEnsemble w (fun a => (Jq a : ℝ)) - pauliEnsemble w J₀‖
        ≤ pauliWeightSum w * rho' := by
      refine norm_pauliEnsemble_sub_le w _ _ fun a => ?_
      have := hJq a
      rw [abs_sub_comm] at this
      exact le_of_lt this
    have hmove : dist (orbitVec (pauliEnsemble w (fun a => (Jq a : ℝ)))
          (zeroProductState (Fin n)) (τ : ℝ))
        (orbitVec (pauliEnsemble w J₀) (zeroProductState (Fin n)) (τ : ℝ))
        ≤ |(τ : ℝ)| * ‖pauliEnsemble w (fun a => (Jq a : ℝ)) - pauliEnsemble w J₀‖ * 1 := by
      rw [← hOmeganorm]
      exact dist_orbitVec_generator_le
        (Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_pauliEnsemble w _))
        (Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_pauliEnsemble w J₀)) _ _
    have hsmall : |(τ : ℝ)| * ‖pauliEnsemble w (fun a => (Jq a : ℝ)) - pauliEnsemble w J₀‖ * 1
        ≤ δ / 4 := by
      have hstep : |(τ : ℝ)| * ‖pauliEnsemble w (fun a => (Jq a : ℝ)) - pauliEnsemble w J₀‖
          ≤ lip * rho' := by
        rw [hlipdef, mul_assoc]
        exact mul_le_mul_of_nonneg_left hgen (abs_nonneg _)
      have hstep2 : lip * rho' ≤ δ / 4 := by
        have hle : rho' ≤ δ / (4 * (lip + 1)) := min_le_right _ _
        have : lip * rho' ≤ lip * (δ / (4 * (lip + 1))) :=
          mul_le_mul_of_nonneg_left hle hlip0
        refine le_trans this ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 4 * (lip + 1))]
        nlinarith [hδ0.le, hlip0]
      linarith [hstep, hstep2]
    have hbase := hAkτ J₀ hJ₀ κ
    have htri := dist_triangle (orbitVec (pauliEnsemble w J₀) (zeroProductState (Fin n)) (τ : ℝ))
      (orbitVec (pauliEnsemble w (fun a => (Jq a : ℝ))) (zeroProductState (Fin n)) (τ : ℝ))
      (eucVec (Z κ))
    have hcomm : dist (orbitVec (pauliEnsemble w J₀) (zeroProductState (Fin n)) (τ : ℝ))
        (orbitVec (pauliEnsemble w (fun a => (Jq a : ℝ))) (zeroProductState (Fin n)) (τ : ℝ))
        = dist (orbitVec (pauliEnsemble w (fun a => (Jq a : ℝ)))
            (zeroProductState (Fin n)) (τ : ℝ))
          (orbitVec (pauliEnsemble w J₀) (zeroProductState (Fin n)) (τ : ℝ)) := dist_comm _ _
    linarith [hκ, hmove, hsmall, hbase, htri, hδ0, hcomm]


/-! ## The integer-coefficient form -/

section Rescale

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Rescaling the generator is the inverse rescaling of the time. -/
theorem unitaryEvolution_smul_generator (H : Matrix I I ℂ) (c t : ℝ) :
    unitaryEvolution (((c : ℝ) : ℂ) • H) t = unitaryEvolution H (c * t) := by
  unfold unitaryEvolution
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem orbitVec_smul_generator (H : Matrix I I ℂ) (psi : I → ℂ) (c t : ℝ) :
    orbitVec (((c : ℝ) : ℂ) • H) psi t = orbitVec H psi (c * t) := by
  rw [orbitVec, orbitVec, unitaryEvolution_smul_generator]

end Rescale

/-- A finite family of rationals has a positive common denominator. -/
theorem exists_common_denominator {α : Type*} [Fintype α] (x : α → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, ∃ z : ℤ, ((D : ℚ)) * x a = (z : ℚ) := by
  classical
  refine ⟨∏ a, (x a).den, Finset.prod_pos fun a _ => (x a).pos, fun a => ?_⟩
  obtain ⟨m, hm⟩ : (x a).den ∣ ∏ b, (x b).den :=
    Finset.dvd_prod_of_mem (fun b => (x b).den) (Finset.mem_univ a)
  refine ⟨(x a).num * m, ?_⟩
  rw [hm]
  push_cast
  linear_combination (m : ℚ) * Rat.mul_den_eq_num (x a)

/-- **The integer-coefficient form.**  The same endpoint is reached by rational-time evolution
under an integer-coefficient Hamiltonian: moving the common denominator from the coefficients to
the time preserves the product. -/
theorem exists_integer_coefficient_witness
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    (hcard0 : 0 < Fintype.card (Fin n → Option (Fin 3)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : 2 * Real.log (8 * Fintype.card (Fin n → Option (Fin 3))) ≤ B ^ 2)
    (Z : C → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 * (2 / 3 : ℝ) ^ n) / (1 - eps ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (horizon : ℝ) :
    ∃ (Jz : (Fin n → Option (Fin 3)) → ℤ) (τ : ℚ), 0 < τ ∧
      ((fun a => (Jz a : ℝ)), (τ : ℝ))
        ∈ hardCircuitEvent w (zeroProductState (Fin n)) eps Z := by
  classical
  obtain ⟨τ, Jq, -, hτpos, -, -, hhard⟩ := exists_rational_common_time_witness w hq hwsupp hw hwne
    hcard0 hB0 hB Z hZ heps0 heps1 hr hscale hM hcard hs horizon
  obtain ⟨D, hD0, hDdvd⟩ := exists_common_denominator Jq
  choose Jz hJz using hDdvd
  refine ⟨Jz, τ / (D : ℚ), by positivity, ?_⟩
  have hDreal : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD0
  have hcoeff : (fun a => ((Jz a : ℤ) : ℝ)) = fun a => (D : ℝ) * ((Jq a : ℚ) : ℝ) := by
    funext a
    have := hJz a
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) this.symm
  have hgen : pauliEnsemble w (fun a => ((Jz a : ℤ) : ℝ))
      = (((D : ℝ) : ℂ)) • pauliEnsemble w (fun a => ((Jq a : ℚ) : ℝ)) := by
    rw [hcoeff]
    exact pauliEnsemble_smul w (D : ℝ) _
  have htime : (D : ℝ) * (((τ / (D : ℚ) : ℚ)) : ℝ) = ((τ : ℚ) : ℝ) := by
    push_cast
    field_simp
  intro hmem
  refine hhard ?_
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, ?_⟩
  rwa [hgen, orbitVec_smul_generator, htime] at hκ

end GaloisForLFunctions.HTGeometry

end
