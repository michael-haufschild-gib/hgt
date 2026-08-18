import GaloisForLFunctions.HTGeometry.CollectiveTwirlIdentity
import GaloisForLFunctions.HTGeometry.CompletedPhaseReplicaMoment

/-!
# The design barrier: exact designs, the invariant projector, and the ensemble bound

The collective commutant is a `*`-subalgebra, so the difference of a moment and the normalized
symmetric projector is central whenever the moment is.  Pairing that difference with its own
adjoint through the twirl identity makes its Hilbert--Schmidt energy vanish, so a moment lying in
the collective commutant *is* the normalized symmetric projector: an exact projective replica design
has no freedom at all.

Conjugating the symmetric projector by a collective unitary returns it, so it is annihilated by
every collective adjoint action, which is what places it inside every quenched centralizer.

Finally, the one-word capture inequality, the exact split of a collision into its completed baseline
and its centralizer-centered defect, and a baseline bound combine, after averaging against any
ensemble, into the exact criterion: the ensemble mass of the shortcut event is at most the padded
word count over the threshold power, times the baseline bound plus the signed averaged defect.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Algebra

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isCollectiveCentral_conjTranspose (r : ℕ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) : IsCollectiveCentral r Zᴴ := by
  intro U hU
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h := hZ Uᴴ hUU
  have hc := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    replicaTensorPowerMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose] at hc
  exact hc.symm

theorem isCollectiveCentral_sub (r : ℕ) {Z W : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) (hW : IsCollectiveCentral r W) :
    IsCollectiveCentral r (Z - W) := by
  intro U hU
  rw [Matrix.mul_sub, Matrix.sub_mul, hZ U hU, hW U hU]

theorem isCollectiveCentral_smul (r : ℕ) (c : ℂ) {Z : Matrix (Fin r → α) (Fin r → α) ℂ}
    (hZ : IsCollectiveCentral r Z) : IsCollectiveCentral r (c • Z) := by
  intro U hU
  rw [Matrix.mul_smul, Matrix.smul_mul, hZ U hU]

theorem eq_zero_of_hsNormSq_eq_zero {n : Type*} [Fintype n] (A : Matrix n n ℂ)
    (h : hsNormSq A = 0) : A = 0 := by
  classical
  funext x y
  have hall : ∀ v ∈ (Finset.univ : Finset n), (∑ u, ‖A u v‖ ^ 2) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun v _ => ?_).mp h
    exact Finset.sum_nonneg fun u _ => sq_nonneg _
  have hrow := hall y (Finset.mem_univ y)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => sq_nonneg ‖A u y‖).mp hrow x
    (Finset.mem_univ x)
  have hnorm : ‖A x y‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry
    exact this
  simpa using hnorm

theorem replicaTensorPower_mul_conjTranspose (r : ℕ) {A : Matrix α α ℂ} (hA : Aᴴ * A = 1) :
    replicaTensorPowerMatrix r A * (replicaTensorPowerMatrix r A)ᴴ = 1 :=
  mul_eq_one_comm.mp (replicaTensorPower_conjTranspose_mul r hA)

/-- **The symmetric projector lies in every quenched centralizer.**  Conjugation by a collective
unitary returns it, so every collective adjoint action annihilates it. -/
theorem symReplicaProjection_conj (r : ℕ) {U : Matrix α α ℂ} (hU : Uᴴ * U = 1) :
    replicaTensorPowerMatrix r U * symReplicaProjection (α := α) r *
        (replicaTensorPowerMatrix r U)ᴴ = symReplicaProjection (α := α) r := by
  rw [← symReplicaProjection_commute r U, Matrix.mul_assoc,
    replicaTensorPower_mul_conjTranspose r hU, Matrix.mul_one]

/-- **`(12)`.**  A replica moment lying in the collective commutant is exactly the normalized
symmetric projector: an exact projective replica design has no freedom. -/
theorem replicaMoment_eq_omega_of_isCollectiveCentral (r : ℕ) [Nonempty α]
    {C : Type*} [Fintype C] (w : C → ℝ) (target : C → α → ℂ)
    (hunit : ∀ c, finiteComplexInner (target c) (target c) = 1) (hsum : ∑ c, w c = 1)
    (hcentral : IsCollectiveCentral r (replicaMoment r w target)) (a0 : α) :
    replicaMoment r w target
      = ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ)⁻¹ •
          symReplicaProjection (α := α) r := by
  classical
  set Om : Matrix (Fin r → α) (Fin r → α) ℂ :=
    ((((Fintype.card α + r - 1).choose r : ℕ) : ℝ) : ℂ)⁻¹ •
      symReplicaProjection (α := α) r with hOm
  have hOmCentral : IsCollectiveCentral r Om :=
    isCollectiveCentral_smul r _ (isCollectiveCentral_symReplicaProjection r)
  have hDiff : IsCollectiveCentral r (replicaMoment r w target - Om) :=
    isCollectiveCentral_sub r hcentral hOmCentral
  have hAdj : IsCollectiveCentral r ((replicaMoment r w target - Om)ᴴ) :=
    isCollectiveCentral_conjTranspose r hDiff
  have h21 := trace_mul_replicaMoment_eq_omega r hAdj w target hunit hsum a0
  rw [← hOm] at h21
  have hzero : (((replicaMoment r w target - Om)ᴴ) *
      (replicaMoment r w target - Om)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, h21, sub_self]
  have hnorm : hsNormSq (replicaMoment r w target - Om) = 0 := by
    have := hsNormSq_eq_trace (replicaMoment r w target - Om)
    rw [hzero] at this
    exact_mod_cast this
  have := eq_zero_of_hsNormSq_eq_zero _ hnorm
  rw [sub_eq_zero] at this
  exact this

end Algebra

section Ensemble

/-- **`(17)`, `(18)`.**  The ensemble mass of the shortcut event is at most the capture scale times
the completed baseline bound plus the signed centralizer-centered defect. -/
theorem ensemble_shortcut_bound {E : Type*} [Fintype E] (mu : E → ℝ) (hmu : ∀ e, 0 ≤ mu e)
    (hmusum : ∑ e, mu e = 1) (event : Finset E)
    (A Abar defect : E → ℝ) (hAnn : ∀ e, 0 ≤ A e)
    (hsplit : ∀ e, A e = Abar e + defect e) {bound : ℝ} (hbase : ∀ e, Abar e ≤ bound)
    {scale : ℝ} (hscale : 0 < scale)
    (hcapture : ∀ e ∈ event, (1 : ℝ) ≤ scale * A e) :
    (∑ e ∈ event, mu e) ≤ scale * (bound + ∑ e, mu e * defect e) := by
  classical
  have hstep : ∀ e ∈ event, mu e ≤ scale * (mu e * A e) := by
    intro e he
    calc mu e = mu e * 1 := (mul_one _).symm
      _ ≤ mu e * (scale * A e) := mul_le_mul_of_nonneg_left (hcapture e he) (hmu e)
      _ = scale * (mu e * A e) := by ring
  have hsum1 : (∑ e ∈ event, mu e) ≤ scale * ∑ e ∈ event, mu e * A e := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  have hsum2 : (∑ e ∈ event, mu e * A e) ≤ ∑ e, mu e * A e :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ event)
      fun e _ _ => mul_nonneg (hmu e) (hAnn e)
  have hexpand : (∑ e, mu e * A e)
      = (∑ e, mu e * Abar e) + ∑ e, mu e * defect e := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [hsplit e]; ring
  have hbaseline : (∑ e, mu e * Abar e) ≤ bound := by
    calc (∑ e, mu e * Abar e) ≤ ∑ e, mu e * bound :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hbase e) (hmu e)
      _ = bound := by rw [← Finset.sum_mul, hmusum, one_mul]
  calc (∑ e ∈ event, mu e) ≤ scale * ∑ e ∈ event, mu e * A e := hsum1
    _ ≤ scale * ∑ e, mu e * A e := mul_le_mul_of_nonneg_left hsum2 hscale.le
    _ = scale * ((∑ e, mu e * Abar e) + ∑ e, mu e * defect e) := by rw [hexpand]
    _ ≤ scale * (bound + ∑ e, mu e * defect e) := by
        refine mul_le_mul_of_nonneg_left ?_ hscale.le
        linarith

end Ensemble

end

end GaloisForLFunctions.HTGeometry
