import GaloisForLFunctions.RHTower.FiniteJetGradedRealityNoGo

/-!
# Simultaneous Hermite-flat completed-flux perturbations

The one-quartet construction used the special local factor

`1 + (x * (2 * α + x))^(2N+1)`.

For a finite packet of quartet factors, the local form at each selected center is instead

`1 + x^M * u(x)`,

where `u` is an analytic unit containing every other nonvanishing quartet factor.  This module
proves the exact general statement: its completed logarithmic-flux correction has analytic order
`M`.  Consequently any two independently chosen unit factors perturbing the same analytic base
have identical Taylor coefficients at every order below `M`.

This is the reusable local core of the simultaneous multi-quartet realization theorem.  The global
real-even `cosh` envelope, zero-free real axis, exact order one, and aperiodicity are recorded in
`simultaneous-multiquartet-finite-passport-realization.md`.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- A general Hermite-flat local factor.  In a simultaneous finite product, `u` contains all
factors that remain nonzero at the selected center. -/
def hermiteFlatFactor (M : ℕ) (u : ℂ → ℂ) (x : ℂ) : ℂ :=
  1 + x ^ M * u x

/-- The analytic unit in the completed logarithmic-flux correction of `hermiteFlatFactor`. -/
def hermiteFlatFluxUnit (M : ℕ) (u : ℂ → ℂ) (x : ℂ) : ℂ :=
  -((M : ℂ) * u x + x * deriv u x) / hermiteFlatFactor M u x

/-- The completed logarithmic-flux correction, factored by its exact Hermite-flat power. -/
def hermiteFlatFluxCorrection (M : ℕ) (u : ℂ → ℂ) (x : ℂ) : ℂ :=
  x ^ M * hermiteFlatFluxUnit M u x

@[simp] theorem hermiteFlatFactor_zero {M : ℕ} (hM : 0 < M) (u : ℂ → ℂ) :
    hermiteFlatFactor M u 0 = 1 := by
  simp [hermiteFlatFactor, hM.ne']

theorem hermiteFlatFluxUnit_analyticAt_zero {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (hermiteFlatFluxUnit M u) 0 := by
  rw [show hermiteFlatFluxUnit M u = fun x : ℂ =>
    -((M : ℂ) * u x + x * deriv u x) / hermiteFlatFactor M u x by rfl]
  apply AnalyticAt.div
  · exact ((analyticAt_const.mul hu).add (analyticAt_id.mul hu.deriv)).neg
  · unfold hermiteFlatFactor
    fun_prop
  · simp [hermiteFlatFactor, hM.ne']

@[simp] theorem hermiteFlatFluxUnit_zero {M : ℕ} (hM : 0 < M)
    (u : ℂ → ℂ) :
    hermiteFlatFluxUnit M u 0 = -(M : ℂ) * u 0 := by
  simp [hermiteFlatFluxUnit, hermiteFlatFactor, hM.ne']

theorem hermiteFlatFluxUnit_zero_ne {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu0 : u 0 ≠ 0) :
    hermiteFlatFluxUnit M u 0 ≠ 0 := by
  rw [hermiteFlatFluxUnit_zero hM]
  exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hM.ne')) hu0

theorem hermiteFlatFluxCorrection_analyticAt_zero {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (hermiteFlatFluxCorrection M u) 0 := by
  exact (analyticAt_id.pow _).mul (hermiteFlatFluxUnit_analyticAt_zero hM hu)

/-- Near the center, the factored correction is the actual `-x`-normalized logarithmic derivative
of the Hermite-flat factor. -/
theorem hermiteFlatFluxCorrection_eventuallyEq_neg_mul_logDeriv
    {M : ℕ} (hM : 0 < M) {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    hermiteFlatFluxCorrection M u =ᶠ[𝓝 0]
      fun x => -x * deriv (hermiteFlatFactor M u) x / hermiteFlatFactor M u x := by
  have hfac : AnalyticAt ℂ (hermiteFlatFactor M u) 0 := by
    unfold hermiteFlatFactor
    fun_prop
  have hne : ∀ᶠ x in 𝓝 (0 : ℂ), hermiteFlatFactor M u x ≠ 0 :=
    hfac.continuousAt.eventually_ne (by simp [hermiteFlatFactor, hM.ne'])
  filter_upwards [hu.eventually_analyticAt, hne] with x hux hx
  have hpow : HasDerivAt (fun y : ℂ => y ^ M) ((M : ℂ) * x ^ (M - 1)) x := by
    simpa using (hasDerivAt_id x).pow M
  have hfactor : HasDerivAt (hermiteFlatFactor M u)
      (((M : ℂ) * x ^ (M - 1)) * u x + x ^ M * deriv u x) x := by
    change HasDerivAt (fun y : ℂ => 1 + y ^ M * u y) _ x
    convert (hasDerivAt_const (x := x) (c := (1 : ℂ))).add
      (hpow.mul hux.differentiableAt.hasDerivAt) using 1
    all_goals ring
  rw [hermiteFlatFluxCorrection, hermiteFlatFluxUnit, hfactor.deriv]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  simp only [Nat.succ_sub_one, pow_succ]
  field_simp [hx]

/-- The completed-flux correction has exactly the prescribed flatness order. -/
theorem hermiteFlatFluxCorrection_order {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    analyticOrderAt (hermiteFlatFluxCorrection M u) 0 = M := by
  change analyticOrderAt ((id : ℂ → ℂ) ^ M * hermiteFlatFluxUnit M u) 0 = M
  rw [analyticOrderAt_mul (analyticAt_id.pow _)
    (hermiteFlatFluxUnit_analyticAt_zero hM hu), analyticOrderAt_pow analyticAt_id,
    analyticOrderAt_id]
  have hunit : analyticOrderAt (hermiteFlatFluxUnit M u) 0 = 0 :=
    (hermiteFlatFluxUnit_analyticAt_zero hM hu).analyticOrderAt_eq_zero.mpr
      (hermiteFlatFluxUnit_zero_ne hM hu0)
  rw [hunit]
  simp

theorem hermiteFlatFluxCorrection_iteratedDeriv_zero {M n : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hn : n < M) :
    iteratedDeriv n (hermiteFlatFluxCorrection M u) 0 = 0 := by
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    (hermiteFlatFluxCorrection_analyticAt_zero hM hu) M
    (hermiteFlatFluxCorrection_order hM hu hu0)
  simpa only [iteratedDeriv_eq_iterate] using h.1 n hn

theorem hermiteFlatFluxCorrection_iteratedDeriv_escape_ne_zero {M : ℕ} (hM : 0 < M)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    iteratedDeriv M (hermiteFlatFluxCorrection M u) 0 ≠ 0 := by
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
    (hermiteFlatFluxCorrection_analyticAt_zero hM hu) M
    (hermiteFlatFluxCorrection_order hM hu hu0)
  simpa only [iteratedDeriv_eq_iterate] using h.2

/-- One analytic base germ with one independently chosen Hermite-flat unit correction. -/
def hermiteFlatPerturbedGerm (M : ℕ) (base u : ℂ → ℂ) (x : ℂ) : ℂ :=
  base x + hermiteFlatFluxCorrection M u x

theorem hermiteFlatPerturbedGerm_analyticAt_zero {M : ℕ} (hM : 0 < M)
    {base u : ℂ → ℂ} (hbase : AnalyticAt ℂ base 0) (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (hermiteFlatPerturbedGerm M base u) 0 := by
  exact hbase.add (hermiteFlatFluxCorrection_analyticAt_zero hM hu)

theorem hermiteFlatPerturbedGerm_iteratedDeriv_eq_base_of_lt
    {M n : ℕ} (hM : 0 < M) {base u : ℂ → ℂ}
    (hbase : AnalyticAt ℂ base 0) (hu : AnalyticAt ℂ u 0)
    (hu0 : u 0 ≠ 0) (hn : n < M) :
    iteratedDeriv n (hermiteFlatPerturbedGerm M base u) 0 =
      iteratedDeriv n base 0 := by
  change iteratedDeriv n (base + hermiteFlatFluxCorrection M u) 0 = _
  rw [iteratedDeriv_add hbase.contDiffAt
    (hermiteFlatFluxCorrection_analyticAt_zero hM hu).contDiffAt,
    hermiteFlatFluxCorrection_iteratedDeriv_zero hM hu hu0 hn, add_zero]

/-- **Simultaneous finite-prefix law.** Two independently chosen Hermite-flat perturbations of one
analytic base have the same Taylor prefix below their common flatness order.  In the multi-quartet
construction, the two units are the products of all factors nonvanishing at the FE and Schwarz
partner centers. -/
theorem hermiteFlatPerturbedGerm_pair_same_prefix
    {M n : ℕ} (hM : 0 < M) {base u v : ℂ → ℂ}
    (hbase : AnalyticAt ℂ base 0) (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0)
    (hu0 : u 0 ≠ 0) (hv0 : v 0 ≠ 0) (hn : n < M) :
    iteratedDeriv n (hermiteFlatPerturbedGerm M base u) 0 =
      iteratedDeriv n (hermiteFlatPerturbedGerm M base v) 0 := by
  rw [hermiteFlatPerturbedGerm_iteratedDeriv_eq_base_of_lt hM hbase hu hu0 hn,
    hermiteFlatPerturbedGerm_iteratedDeriv_eq_base_of_lt hM hbase hv hv0 hn]

/-! ## Finite-packet instantiation -/

/-- The real-even quartet polynomial with roots `±α` and `±conj α`. -/
def quartetFlatAtom (α z : ℂ) : ℂ :=
  (z ^ 2 - α ^ 2) * (z ^ 2 - ((starRingEnd ℂ) α) ^ 2)

/-- The product carrying independently prescribed multiplicities at a finite packet of quartets. -/
def simultaneousFlatProduct {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (z : ℂ) : ℂ :=
  ∏ i, quartetFlatAtom (α i) z ^ M i

/-- The simultaneous real-even Hermite-flat multiplier `1 + ∏ᵢ Qᵢ^Mᵢ`. -/
def simultaneousFlatMultiplier {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (z : ℂ) : ℂ :=
  1 + simultaneousFlatProduct M α z

/-- The unit left after extracting `x` from the selected quartet atom at `α`. -/
def quartetFlatAtomUnit (α x : ℂ) : ℂ :=
  (2 * α + x) * ((α + x) ^ 2 - ((starRingEnd ℂ) α) ^ 2)

/-- The local analytic unit obtained at packet center `α i` after extracting `x^(M i)`. -/
def simultaneousFlatUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) (x : ℂ) : ℂ :=
  quartetFlatAtomUnit (α i) x ^ M i *
    ∏ j ∈ Finset.univ.erase i, quartetFlatAtom (α j) (α i + x) ^ M j

theorem quartetFlatAtom_shift (α x : ℂ) :
    quartetFlatAtom α (α + x) = x * quartetFlatAtomUnit α x := by
  unfold quartetFlatAtom quartetFlatAtomUnit
  ring

/-- Every selected center is retained by the packet multiplier with value one. -/
@[simp] theorem simultaneousFlatMultiplier_at_center
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) (hMi : 0 < M i) :
    simultaneousFlatMultiplier M α (α i) = 1 := by
  rw [simultaneousFlatMultiplier, simultaneousFlatProduct]
  have hzero : quartetFlatAtom (α i) (α i) ^ M i = 0 := by
    rw [quartetFlatAtom]
    simp [hMi.ne']
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), hzero]
  simp

/-- Exact local factorization of the full finite packet at one selected center. -/
theorem simultaneousFlatProduct_shift_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) (x : ℂ) :
    simultaneousFlatProduct M α (α i + x) =
      x ^ M i * simultaneousFlatUnit M α i x := by
  rw [simultaneousFlatProduct, simultaneousFlatUnit,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), quartetFlatAtom_shift,
    mul_pow]
  ring

/-- At each selected center, the simultaneous packet is exactly the general Hermite-flat factor. -/
theorem simultaneousFlatMultiplier_shift_eq_hermiteFlatFactor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) (x : ℂ) :
    simultaneousFlatMultiplier M α (α i + x) =
      hermiteFlatFactor (M i) (simultaneousFlatUnit M α i) x := by
  rw [simultaneousFlatMultiplier, simultaneousFlatProduct_shift_factorization]
  rfl

theorem simultaneousFlatUnit_analyticAt_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) :
    AnalyticAt ℂ (simultaneousFlatUnit M α i) 0 := by
  unfold simultaneousFlatUnit quartetFlatAtomUnit quartetFlatAtom
  fun_prop

@[simp] theorem simultaneousFlatUnit_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ) (α : ι → ℂ) (i : ι) :
    simultaneousFlatUnit M α i 0 =
      ((2 * α i) * ((α i) ^ 2 - ((starRingEnd ℂ) (α i)) ^ 2)) ^ M i *
        ∏ j ∈ Finset.univ.erase i, quartetFlatAtom (α j) (α i) ^ M j := by
  simp [simultaneousFlatUnit, quartetFlatAtomUnit]

/-- The extracted packet factor is a unit whenever the selected quartet is simple and disjoint
from every other quartet in the packet. -/
theorem simultaneousFlatUnit_zero_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → ℕ} {α : ι → ℂ} {i : ι}
    (hself : (2 * α i) * ((α i) ^ 2 - ((starRingEnd ℂ) (α i)) ^ 2) ≠ 0)
    (hother : ∀ j, j ≠ i → quartetFlatAtom (α j) (α i) ≠ 0) :
    simultaneousFlatUnit M α i 0 ≠ 0 := by
  rw [simultaneousFlatUnit_zero]
  apply mul_ne_zero (pow_ne_zero _ hself)
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (hother j (Finset.ne_of_mem_erase hj))

/-- **Finite-packet flatness theorem.** At each simple disjoint selected quartet, the actual local
completed-flux correction of the simultaneous multiplier has exactly its independently prescribed
order `M i`. -/
theorem simultaneousFlatMultiplier_localFluxCorrection_order
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → ℕ} {α : ι → ℂ} {i : ι} (hMi : 0 < M i)
    (hself : (2 * α i) * ((α i) ^ 2 - ((starRingEnd ℂ) (α i)) ^ 2) ≠ 0)
    (hother : ∀ j, j ≠ i → quartetFlatAtom (α j) (α i) ≠ 0) :
    analyticOrderAt
      (hermiteFlatFluxCorrection (M i) (simultaneousFlatUnit M α i)) 0 = M i := by
  exact hermiteFlatFluxCorrection_order hMi
    (simultaneousFlatUnit_analyticAt_zero M α i)
    (simultaneousFlatUnit_zero_ne hself hother)

/-! ## Positive imaginary-axis realization -/

/-- On the imaginary axis, one real-even quartet atom is exactly a real norm square. -/
theorem quartetFlatAtom_mul_I_ofReal (α : ℂ) (y : ℝ) :
    quartetFlatAtom α ((y : ℂ) * I) =
      ((Complex.normSq (((y : ℂ) ^ 2) + α ^ 2) : ℝ) : ℂ) := by
  have hzsq : (((y : ℂ) * I) ^ 2) = -((y : ℂ) ^ 2) := by
    rw [mul_pow, I_sq]
    ring
  have hconj : (starRingEnd ℂ) (((y : ℂ) ^ 2) + α ^ 2) =
      ((y : ℂ) ^ 2) + ((starRingEnd ℂ) α) ^ 2 := by simp
  rw [quartetFlatAtom, hzsq]
  calc
    (-((y : ℂ) ^ 2) - α ^ 2) *
        (-((y : ℂ) ^ 2) - ((starRingEnd ℂ) α) ^ 2) =
      (((y : ℂ) ^ 2) + α ^ 2) *
        (starRingEnd ℂ) (((y : ℂ) ^ 2) + α ^ 2) := by rw [hconj]; ring
    _ = ((Complex.normSq (((y : ℂ) ^ 2) + α ^ 2) : ℝ) : ℂ) :=
      Complex.mul_conj _

/-- A nondegenerate quartet atom takes a strictly positive real value on the imaginary axis. -/
theorem quartetFlatAtom_mul_I_pos_real {α : ℂ} {y : ℝ}
    (hne : ((y : ℂ) ^ 2) + α ^ 2 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ quartetFlatAtom α ((y : ℂ) * I) = (r : ℂ) := by
  refine ⟨Complex.normSq (((y : ℂ) ^ 2) + α ^ 2),
    Complex.normSq_pos.mpr hne, ?_⟩
  exact quartetFlatAtom_mul_I_ofReal α y

/-- The entire finite packet is strictly positive real on the imaginary axis whenever none of its
quartet atoms degenerates there.  This is the algebraic source of the zero-free-real-axis repair in
the arbitrary finite-packet theorem. -/
theorem simultaneousFlatProduct_mul_I_pos_real
    {ι : Type*} [Fintype ι] (M : ι → ℕ) (α : ι → ℂ) (y : ℝ)
    (hne : ∀ i, ((y : ℂ) ^ 2) + (α i) ^ 2 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ simultaneousFlatProduct M α ((y : ℂ) * I) = (r : ℂ) := by
  let v : ι → ℝ := fun i => Complex.normSq (((y : ℂ) ^ 2) + (α i) ^ 2) ^ M i
  refine ⟨∏ i, v i, Finset.prod_pos fun i _ => pow_pos
    (Complex.normSq_pos.mpr (hne i)) _, ?_⟩
  rw [simultaneousFlatProduct]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  rw [quartetFlatAtom_mul_I_ofReal]
  simp [v]

end

end RHTower
