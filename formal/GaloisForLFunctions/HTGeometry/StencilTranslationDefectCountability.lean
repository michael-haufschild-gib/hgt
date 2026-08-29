import GaloisForLFunctions.HTGeometry.StencilJetExpansion
import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDefectCountability
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum

/-!
# Countability of the DA parameter set of a finite translation stencil

For a fixed nonzero finite translation stencil `A_h F (z) = ∑ l, c l * F (z + λ l * h)` with first
nonzero moment `M k`, the normalized family `h ↦ (k ! / M k) * h ^ (-k) * A_h F` converges, jointly
in every jet coordinate, to `F ^ (k)`.  The dichotomy of the additive theorem therefore repeats
verbatim: either one bounded complexity level annihilates every small stencil, and then `F ^ (k)` —
hence `F` — satisfies an algebraic differential equation, or each complexity level contributes only
a countable zero set in the shift parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

variable {J : ℕ}

/-! ## Jets of the stencil -/

theorem iteratedDeriv_stencilApply {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) (h : ℂ) (j : ℕ) {z : ℂ}
    (hz : ∀ l, z + lam l * h ∈ W) :
    iteratedDeriv j (stencilApply F c lam h) z = stencilShiftProfile F c lam z j h := by
  classical
  have hfun : ∀ l : Fin J,
      (fun w : ℂ => F (w + lam l * h)) = fun t : ℂ => F (lam l * h + 1 * t) := by
    intro l
    funext t
    ring_nf
  have hcd : ∀ l : Fin J, ContDiffAt ℂ (j : ℕ) (fun w : ℂ => F (w + lam l * h)) z := by
    intro l
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + lam l * h) z := analyticAt_id.add analyticAt_const
    have hout : AnalyticAt ℂ F (z + lam l * h) := hF _ (hz l)
    have hcomp : AnalyticAt ℂ (F ∘ fun w : ℂ => w + lam l * h) z :=
      AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun w : ℂ => w + lam l * h) (x := z) hout hinner
    exact hcomp.contDiffAt
  have hsum : stencilApply F c lam h = ∑ l : Fin J, fun w : ℂ => c l * F (w + lam l * h) := by
    funext w
    simp [stencilApply, Finset.sum_apply]
  rw [hsum, iteratedDeriv_sum (fun l _ => contDiffAt_const.mul (hcd l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [iteratedDeriv_const_mul _ (hcd l)]
  congr 1
  rw [hfun l]
  have hmem : lam l * h + 1 * z ∈ W := by
    have := hz l
    have heq : lam l * h + 1 * z = z + lam l * h := by ring
    rwa [heq]
  rw [iteratedDeriv_comp_affine_on hW hF (lam l * h) 1 j hmem]
  have heq : lam l * h + 1 * z = z + lam l * h := by ring
  rw [heq, one_pow, one_mul]

/-! ## The normalized stencil jet vector -/

/-- The jet vector of the normalized stencil, analytically extended to shift zero. -/
def stencilSlopeJetVector (F : ℂ → ℂ) (c lam : Fin J → ℂ) (k n : ℕ) (h a : ℂ) :
    Fin (n + 2) → ℂ :=
  Fin.cons a fun j : Fin (n + 1) =>
    ((k.factorial : ℂ) / stencilMoment c lam k) * stencilNormalizedProfile F c lam a (j : ℕ) k h

theorem stencilSlopeJetVector_zero {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {k : ℕ}
    (hk : stencilMoment c lam k ≠ 0) (n : ℕ) {a : ℂ} (ha : a ∈ W) :
    stencilSlopeJetVector F c lam k n 0 a = entireJetVector (iteratedDeriv k F) n a := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      have hfac : ((k.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      simp only [stencilSlopeJetVector, Fin.cons_succ, entireJetVector]
      rw [stencilNormalizedProfile_center hW hF c lam ha (j : ℕ) k,
        iteratedDeriv_iteratedDeriv (j : ℕ) k F]
      field_simp

/-- Total value-jet degree scaling of the normalized stencil away from shift zero. -/
theorem stencilSlopeJetVector_of_ne {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {k : ℕ}
    (hlow : ∀ m, m < k → stencilMoment c lam m = 0) (n : ℕ) {h a : ℂ} (hh : h ≠ 0)
    (ha : a ∈ W) (hshift : ∀ l, a + lam l * h ∈ W) :
    stencilSlopeJetVector F c lam k n h a =
      Fin.cons a fun j : Fin (n + 1) =>
        ((k.factorial : ℂ) / stencilMoment c lam k * (h⁻¹) ^ k) *
          iteratedDeriv (j : ℕ) (stencilApply F c lam h) a := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      have hvanish : ∀ m, m < k → dslopeIterZero (stencilShiftProfile F c lam a (j : ℕ)) m 0 = 0 :=
        fun m hm => stencilNormalizedProfile_center_eq_zero hW hF ha (j : ℕ) (hlow m hm)
      simp only [stencilSlopeJetVector, Fin.cons_succ]
      rw [stencilNormalizedProfile, dslopeIterZero_of_ne hvanish hh,
        iteratedDeriv_stencilApply hW hF c lam h (j : ℕ) hshift]
      rw [div_eq_mul_inv, inv_pow]
      ring

/-! ## The normalized stencil minor -/

/-- Sample row of a normalized stencil monomial at nodes inside a disc. -/
def stencilSlopeSampleRow (F : ℂ → ℂ) (c lam : Fin J → ℂ) (z₀ : ℂ) (r : ℝ) (k n d : ℕ)
    (m : JetExponent n d) : ℕ → ℂ → ℂ :=
  fun i h => ∏ a : Fin (n + 2),
    (stencilSlopeJetVector F c lam k n h (domainSampleNode z₀ r i) a) ^ (m a : ℕ)

def stencilSlopeMinor (F : ℂ → ℂ) (c lam : Fin J → ℂ) (z₀ : ℂ) (r : ℝ) (k n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : Matrix (JetExponent n d) (JetExponent n d) ℂ :=
  fun i j => stencilSlopeSampleRow F c lam z₀ r k n d j (φ i) h

def stencilSlopeMinorDet (F : ℂ → ℂ) (c lam : Fin J → ℂ) (z₀ : ℂ) (r : ℝ) (k n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : ℂ :=
  (stencilSlopeMinor F c lam z₀ r k n d φ h).det

theorem stencilSlopeMinorDet_zero {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {k : ℕ}
    (hk : stencilMoment c lam k ≠ 0) {z₀ : ℂ} {r : ℝ} (n d : ℕ)
    (hnodes : ∀ i, domainSampleNode z₀ r i ∈ W) (φ : JetExponent n d → ℕ) :
    stencilSlopeMinorDet F c lam z₀ r k n d φ 0 =
      (coordinateMinor (domainJetSampleRow (iteratedDeriv k F) z₀ r n d) φ).det := by
  unfold stencilSlopeMinorDet stencilSlopeMinor
  congr 1
  ext i j
  rw [coordinateMinor_apply, domainJetSampleRow, jetMon, stencilSlopeSampleRow,
    stencilSlopeJetVector_zero hW hF hk n (hnodes (φ i))]

theorem continuousAt_stencilSlopeMinorDet {F : ℂ → ℂ} {W : Set ℂ}
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) (k : ℕ) {z₀ : ℂ} {r : ℝ} (n d : ℕ)
    (hnodes : ∀ i, domainSampleNode z₀ r i ∈ W) (φ : JetExponent n d → ℕ) :
    ContinuousAt (stencilSlopeMinorDet F c lam z₀ r k n d φ) 0 := by
  classical
  have hcoord : ∀ (i : ℕ) (a : Fin (n + 2)),
      ContinuousAt (fun h : ℂ =>
        stencilSlopeJetVector F c lam k n h (domainSampleNode z₀ r i) a) 0 := by
    intro i a
    induction a using Fin.cases with
    | zero =>
        simpa [stencilSlopeJetVector] using (continuousAt_const :
          ContinuousAt (fun _ : ℂ => domainSampleNode z₀ r i) 0)
    | succ j =>
        simp only [stencilSlopeJetVector, Fin.cons_succ]
        refine continuousAt_const.mul ?_
        exact (analyticAt_stencilNormalizedProfile hF c lam (hnodes i) (j : ℕ) k).continuousAt
  have hrow : ∀ (i : ℕ) (m : JetExponent n d),
      ContinuousAt (stencilSlopeSampleRow F c lam z₀ r k n d m i) 0 := by
    intro i m
    unfold stencilSlopeSampleRow
    apply continuousAt_finsetProd' Finset.univ
    intro a _
    exact (hcoord i a).pow _
  have hcont : ContinuousAt (fun h : ℂ =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, stencilSlopeMinor F c lam z₀ r k n d φ h (σ i) i) 0 := by
    apply continuousAt_finsetSum' Finset.univ
    intro σ _
    apply continuousAt_const.mul
    apply continuousAt_finsetProd' Finset.univ
    intro i _
    exact hrow (φ (σ i)) i
  change ContinuousAt (fun h => (stencilSlopeMinor F c lam z₀ r k n d φ h).det) 0
  simpa only [Matrix.det_apply'] using hcont

theorem stencilSlopeSampleRow_of_ne {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {k : ℕ}
    (hlow : ∀ m, m < k → stencilMoment c lam m = 0) {z₀ : ℂ} {r : ℝ} (n d : ℕ)
    (m : JetExponent n d) (i : ℕ) {h : ℂ} (hh : h ≠ 0)
    (hnode : domainSampleNode z₀ r i ∈ W)
    (hshift : ∀ l, domainSampleNode z₀ r i + lam l * h ∈ W) :
    stencilSlopeSampleRow F c lam z₀ r k n d m i h =
      ((k.factorial : ℂ) / stencilMoment c lam k * (h⁻¹) ^ k) ^ jetValueDegree m *
        domainJetSampleRow (stencilApply F c lam h) z₀ r n d m i := by
  classical
  set a : ℂ := domainSampleNode z₀ r i with hadef
  set β : ℂ := (k.factorial : ℂ) / stencilMoment c lam k * (h⁻¹) ^ k with hβ
  have hvec := stencilSlopeJetVector_of_ne hW hF hlow n hh hnode hshift
  have hraw : domainJetSampleRow (stencilApply F c lam h) z₀ r n d m i =
      a ^ (m 0 : ℕ) *
        ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) (stencilApply F c lam h) a) ^ (m j.succ : ℕ) := by
    rw [domainJetSampleRow, jetMon, Fin.prod_univ_succ]
    simp only [entireJetVector, Fin.cons_zero, Fin.cons_succ, ← hadef]
  have hscaled : (∏ j : Fin (n + 1),
        (β * iteratedDeriv (j : ℕ) (stencilApply F c lam h) a) ^ (m j.succ : ℕ)) =
      β ^ jetValueDegree m *
        ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) (stencilApply F c lam h) a) ^ (m j.succ : ℕ) := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, jetValueDegree, Finset.prod_pow_eq_pow_sum]
  rw [stencilSlopeSampleRow, hvec, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hscaled, hraw]
  ring

theorem stencilSlopeMinorDet_eq_mul {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {k : ℕ}
    (hlow : ∀ m, m < k → stencilMoment c lam m = 0) {z₀ : ℂ} {r : ℝ} (n d : ℕ)
    (φ : JetExponent n d → ℕ) {h : ℂ} (hh : h ≠ 0)
    (hnodes : ∀ i, domainSampleNode z₀ r i ∈ W)
    (hshift : ∀ i l, domainSampleNode z₀ r i + lam l * h ∈ W) :
    stencilSlopeMinorDet F c lam z₀ r k n d φ h =
      (coordinateMinor (domainJetSampleRow (stencilApply F c lam h) z₀ r n d) φ).det *
        ∏ m : JetExponent n d,
          ((k.factorial : ℂ) / stencilMoment c lam k * (h⁻¹) ^ k) ^ jetValueDegree m := by
  classical
  have hmat : stencilSlopeMinor F c lam z₀ r k n d φ h =
      coordinateMinor (domainJetSampleRow (stencilApply F c lam h) z₀ r n d) φ *
        Matrix.diagonal (fun m : JetExponent n d =>
          ((k.factorial : ℂ) / stencilMoment c lam k * (h⁻¹) ^ k) ^ jetValueDegree m) := by
    ext i j
    rw [stencilSlopeMinor, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [stencilSlopeSampleRow_of_ne hW hF hlow n d j (φ i) hh (hnodes (φ i))
        (fun l => hshift (φ i) l), coordinateMinor]
      ring
    · intro b _ hbj
      simp [Matrix.diagonal, hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [stencilSlopeMinorDet, hmat, Matrix.det_mul, Matrix.det_diagonal]

/-! ## Antiderivatives of higher order -/

theorem differentiallyAlgebraicOn_of_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} :
    ∀ (k : ℕ), DifferentiallyAlgebraicOn (iteratedDeriv k f) U → DifferentiallyAlgebraicOn f U := by
  intro k
  induction k generalizing f with
  | zero => intro h; simpa using h
  | succ k ih =>
      intro h
      rw [iteratedDeriv_succ'] at h
      exact differentiallyAlgebraicOn_of_deriv (ih h)

/-! ## The uniform branch -/

/-- Uniform bounded-complexity relations for all small stencils force the `k`-th derivative of the
source — hence the source itself — to satisfy an algebraic differential equation. -/
theorem differentiallyAlgebraicOn_of_uniform_stencil_relations {F : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hWc : IsPreconnected W) (hF : AnalyticOnNhd ℂ F W)
    {c lam : Fin J → ℂ} {k : ℕ} (hlow : ∀ m, m < k → stencilMoment c lam m = 0)
    (hk : stencilMoment c lam k ≠ 0)
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz₀ : z₀ ∈ W)
    (hnodes : ∀ i, domainSampleNode z₀ r i ∈ W)
    {n d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hshift : ∀ h : ℂ, ‖h‖ < ρ → ∀ i l, domainSampleNode z₀ r i + lam l * h ∈ W)
    (hrel : ∀ (φ : JetExponent n d → ℕ) (h : ℂ), ‖h‖ < ρ →
      (coordinateMinor (domainJetSampleRow (stencilApply F c lam h) z₀ r n d) φ).det = 0) :
    DifferentiallyAlgebraicOn F W := by
  refine differentiallyAlgebraicOn_of_iteratedDeriv k ?_
  refine (differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero hWc
    (analyticOnNhd_iteratedDeriv hF k) hz₀ hnodes hr).2 ⟨n, d, fun φ => ?_⟩
  rw [← stencilSlopeMinorDet_zero hW hF hk n d hnodes φ]
  set t : ℕ → ℂ := domainSampleNode 0 ρ with ht
  have htnorm : ∀ i, ‖t i‖ < ρ := by
    intro i
    have hd := dist_domainSampleNode (0 : ℂ) hρ i
    rw [dist_zero_right] at hd
    rw [ht, hd]
    have h2 : (1:ℝ) < (i : ℝ) + 2 := by
      have : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    calc ρ / ((i:ℝ) + 2) < ρ / 1 := div_lt_div_of_pos_left hρ one_pos h2
      _ = ρ := by ring
  have htne : ∀ i, t i ≠ 0 := fun i => by simpa using domainSampleNode_ne (0 : ℂ) hρ i
  have htend : Tendsto t atTop (𝓝 (0 : ℂ)) :=
    (tendsto_domainSampleNode (0 : ℂ) hρ).mono_right inf_le_left
  have hslope : Tendsto (fun i : ℕ => stencilSlopeMinorDet F c lam z₀ r k n d φ (t i)) atTop
      (𝓝 (stencilSlopeMinorDet F c lam z₀ r k n d φ 0)) :=
    (continuousAt_stencilSlopeMinorDet hF c lam k n d hnodes φ).tendsto.comp htend
  have hslope0 : Tendsto (fun i : ℕ => stencilSlopeMinorDet F c lam z₀ r k n d φ (t i)) atTop
      (𝓝 0) := by
    have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
    refine hz.congr' ?_
    filter_upwards with i
    rw [stencilSlopeMinorDet_eq_mul hW hF hlow n d φ (htne i) hnodes
      (fun j l => hshift (t i) (htnorm i) j l), hrel φ (t i) (htnorm i), zero_mul]
  exact tendsto_nhds_unique hslope hslope0


/-! ## The stencil domain -/

/-- The singular set of a finite translation stencil at shift `h`. -/
def stencilSingularSet (S : Set ℂ) (lam : Fin J → ℂ) (h : ℂ) : Set ℂ :=
  ⋃ l, ((fun z : ℂ => z + lam l * h) ⁻¹' S)

/-- The domain of a finite translation stencil at shift `h`. -/
def stencilDomain (S : Set ℂ) (lam : Fin J → ℂ) (h : ℂ) : Set ℂ :=
  (stencilSingularSet S lam h)ᶜ

theorem countable_stencilSingularSet {S : Set ℂ} (hS : S.Countable) (lam : Fin J → ℂ) (h : ℂ) :
    (stencilSingularSet S lam h).Countable :=
  Set.countable_iUnion fun l => hS.preimage (fun x y hxy => by simpa using hxy)

theorem isClosed_stencilSingularSet {S : Set ℂ} (hS : IsClosed S) (lam : Fin J → ℂ) (h : ℂ) :
    IsClosed (stencilSingularSet S lam h) := by
  refine isClosed_iUnion_of_finite fun l => ?_
  exact IsClosed.preimage (by fun_prop) hS

theorem mem_stencilDomain {S : Set ℂ} {lam : Fin J → ℂ} {h z : ℂ}
    (hz : ∀ l, z + lam l * h ∉ S) : z ∈ stencilDomain S lam h := by
  simp only [stencilDomain, stencilSingularSet, Set.mem_compl_iff, Set.mem_iUnion,
    Set.mem_preimage, not_exists]
  exact hz

theorem stencilDomain_mem_compl {S : Set ℂ} {lam : Fin J → ℂ} {h z : ℂ}
    (hz : z ∈ stencilDomain S lam h) (l : Fin J) : z + lam l * h ∈ Sᶜ := by
  simp only [stencilDomain, stencilSingularSet, Set.mem_compl_iff, Set.mem_iUnion,
    Set.mem_preimage, not_exists] at hz
  exact hz l

theorem analyticOnNhd_stencilApply {F : ℂ → ℂ} {S : Set ℂ} (hF : AnalyticOnNhd ℂ F Sᶜ)
    (c lam : Fin J → ℂ) (h : ℂ) :
    AnalyticOnNhd ℂ (stencilApply F c lam h) (stencilDomain S lam h) := by
  intro z hz
  have hterm : ∀ l : Fin J, AnalyticAt ℂ (fun w : ℂ => c l * F (w + lam l * h)) z := by
    intro l
    refine analyticAt_const.mul ?_
    have hout : AnalyticAt ℂ F (z + lam l * h) := hF _ (stencilDomain_mem_compl hz l)
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + lam l * h) z := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun w : ℂ => w + lam l * h) (x := z) hout hinner
  have heq : stencilApply F c lam h = ∑ l : Fin J, fun w : ℂ => c l * F (w + lam l * h) := by
    funext w
    simp [stencilApply, Finset.sum_apply]
  rw [heq]
  exact Finset.analyticAt_sum _ fun l _ => hterm l

/-! ## The shift-analytic stencil minor -/

/-- The jet vector of the stencil at `a`, written manifestly through the jets of `F`. -/
def stencilJetVec (F : ℂ → ℂ) (c lam : Fin J → ℂ) (a : ℂ) (n : ℕ) (h : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons a fun j : Fin (n + 1) => stencilShiftProfile F c lam a (j : ℕ) h

/-- The differential monomial of the stencil, as a function of the shift. -/
def stencilMonAt (F : ℂ → ℂ) (c lam : Fin J → ℂ) (a : ℂ) (n d : ℕ) (m : JetExponent n d)
    (h : ℂ) : ℂ :=
  ∏ i : Fin (n + 2), (stencilJetVec F c lam a n h i) ^ (m i : ℕ)

theorem stencilJetVec_eq_entireJetVector {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W)
    (c lam : Fin J → ℂ) {a h : ℂ} (n : ℕ) (ha : ∀ l, a + lam l * h ∈ W) :
    stencilJetVec F c lam a n h = entireJetVector (stencilApply F c lam h) n a := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      simp only [stencilJetVec, entireJetVector, Fin.cons_succ]
      exact (iteratedDeriv_stencilApply hW hF c lam h (j : ℕ) ha).symm

theorem stencilMonAt_eq_jetMon {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W)
    (c lam : Fin J → ℂ) {a h : ℂ} (n d : ℕ) (m : JetExponent n d)
    (ha : ∀ l, a + lam l * h ∈ W) :
    stencilMonAt F c lam a n d m h = jetMon (stencilApply F c lam h) n d m a := by
  unfold stencilMonAt jetMon
  rw [stencilJetVec_eq_entireJetVector hW hF c lam n ha]

theorem analyticAt_stencilMonAt {F : ℂ → ℂ} {W : Set ℂ} (hF : AnalyticOnNhd ℂ F W)
    (c lam : Fin J → ℂ) {a h₀ : ℂ} (ha : ∀ l, a + lam l * h₀ ∈ W) (n d : ℕ)
    (m : JetExponent n d) :
    AnalyticAt ℂ (stencilMonAt F c lam a n d m) h₀ := by
  have hbase : ∀ i : Fin (n + 2),
      AnalyticAt ℂ (fun h : ℂ => (stencilJetVec F c lam a n h i) ^ (m i : ℕ)) h₀ := by
    intro i
    refine AnalyticAt.pow ?_ _
    induction i using Fin.cases with
    | zero =>
        simpa [stencilJetVec] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) h₀)
    | succ j =>
        simpa [stencilJetVec] using
          analyticAt_stencilShiftProfile hF c lam a (j : ℕ) ha
  have heq : stencilMonAt F c lam a n d m
      = ∏ i : Fin (n + 2), fun h : ℂ => (stencilJetVec F c lam a n h i) ^ (m i : ℕ) := by
    funext h
    simp [stencilMonAt, Finset.prod_apply]
  rw [heq]
  exact Finset.analyticAt_prod _ fun i _ => hbase i

/-- The sample minor determinant of the stencil, as a function of the shift. -/
def stencilShiftMinorDet (F : ℂ → ℂ) (c lam : Fin J → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : ℂ :=
  (Matrix.of fun i j : JetExponent n d =>
    stencilMonAt F c lam (domainSampleNode z₀ r (φ i)) n d j h).det

theorem stencilShiftMinorDet_eq {F : ℂ → ℂ} {W : Set ℂ} {z₀ : ℂ} {r : ℝ} {h : ℂ}
    (hW : IsOpen W) (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) (n d : ℕ)
    (φ : JetExponent n d → ℕ)
    (hshift : ∀ i l, domainSampleNode z₀ r i + lam l * h ∈ W) :
    stencilShiftMinorDet F c lam z₀ r n d φ h =
      (coordinateMinor (domainJetSampleRow (stencilApply F c lam h) z₀ r n d) φ).det := by
  unfold stencilShiftMinorDet
  congr 1
  ext i j
  rw [coordinateMinor_apply, domainJetSampleRow]
  exact stencilMonAt_eq_jetMon hW hF c lam n d j (fun l => hshift (φ i) l)

theorem analyticAt_stencilShiftMinorDet {F : ℂ → ℂ} {W : Set ℂ} (hF : AnalyticOnNhd ℂ F W)
    (c lam : Fin J → ℂ) {z₀ : ℂ} {r : ℝ} (n d : ℕ) (φ : JetExponent n d → ℕ) {h₀ : ℂ}
    (hshift : ∀ (i : JetExponent n d) (l : Fin J),
      domainSampleNode z₀ r (φ i) + lam l * h₀ ∈ W) :
    AnalyticAt ℂ (stencilShiftMinorDet F c lam z₀ r n d φ) h₀ := by
  classical
  have hentry : ∀ i j : JetExponent n d,
      AnalyticAt ℂ (stencilMonAt F c lam (domainSampleNode z₀ r (φ i)) n d j) h₀ :=
    fun i j => analyticAt_stencilMonAt hF c lam (fun l => hshift i l) n d j
  have hdet : stencilShiftMinorDet F c lam z₀ r n d φ
      = ∑ σ : Equiv.Perm (JetExponent n d), fun h : ℂ => (Equiv.Perm.sign σ : ℂ) *
          ∏ i : JetExponent n d,
            stencilMonAt F c lam (domainSampleNode z₀ r (φ (σ i))) n d i h := by
    funext h
    rw [stencilShiftMinorDet, Matrix.det_apply']
    simp [Finset.sum_apply]
  rw [hdet]
  refine Finset.analyticAt_sum _ fun σ _ => ?_
  refine analyticAt_const.mul ?_
  have hprodeq : (fun h : ℂ => ∏ i : JetExponent n d,
        stencilMonAt F c lam (domainSampleNode z₀ r (φ (σ i))) n d i h)
      = ∏ i : JetExponent n d,
        stencilMonAt F c lam (domainSampleNode z₀ r (φ (σ i))) n d i := by
    funext h
    simp [Finset.prod_apply]
  rw [hprodeq]
  exact Finset.analyticAt_prod _ fun i _ => hentry (σ i) i

/-! ## The stencil countability theorem -/

/-- The set of shift parameters at which the stencil satisfies an algebraic differential
equation. -/
def stencilDAStabilizer (F : ℂ → ℂ) (S : Set ℂ) (c lam : Fin J → ℂ) : Set ℂ :=
  {h : ℂ | DifferentiallyAlgebraicOn (stencilApply F c lam h) (stencilDomain S lam h)}

/-- **Finite-stencil parameter countability.**  For a fixed finite translation stencil whose first
nonzero moment is `M k`, a source analytic off a closed countable set and satisfying no algebraic
differential equation there has at most countably many differentially algebraic stencil
parameters. -/
theorem countable_stencilDAStabilizer {F : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable)
    (hF : AnalyticOnNhd ℂ F Sᶜ) (hFht : ¬ DifferentiallyAlgebraicOn F Sᶜ)
    (c lam : Fin J → ℂ) {k : ℕ}
    (hlow : ∀ m, m < k → stencilMoment c lam m = 0) (hk : stencilMoment c lam k ≠ 0) :
    (stencilDAStabilizer F S c lam).Countable := by
  classical
  have hopen : IsOpen (Sᶜ) := hSclosed.isOpen_compl
  obtain ⟨z₀, hz₀⟩ : ∃ z : ℂ, z ∈ Sᶜ := nonempty_compl_of_countable hScount
  obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.1 hopen z₀ hz₀
  set Lam : ℝ := 1 + ∑ l : Fin J, ‖lam l‖ with hLamdef
  have hLam1 : (1:ℝ) ≤ Lam := by
    rw [hLamdef]
    have : (0:ℝ) ≤ ∑ l : Fin J, ‖lam l‖ := Finset.sum_nonneg fun l _ => norm_nonneg _
    linarith
  have hLampos : (0:ℝ) < Lam := lt_of_lt_of_le one_pos hLam1
  have hLamle : ∀ l : Fin J, ‖lam l‖ ≤ Lam := by
    intro l
    rw [hLamdef]
    have hle : ‖lam l‖ ≤ ∑ l' : Fin J, ‖lam l'‖ :=
      Finset.single_le_sum (f := fun l' : Fin J => ‖lam l'‖)
        (fun l' _ => norm_nonneg _) (Finset.mem_univ l)
    linarith
  set R : ℝ := ε / (4 * Lam) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    positivity
  have hnear : ∀ w : ℂ, dist w z₀ < 3 * Lam * R → w ∈ Sᶜ := by
    intro w hw
    refine hballsub ?_
    rw [Metric.mem_ball]
    have h3 : 3 * Lam * R = 3 * ε / 4 := by
      rw [hRdef]
      field_simp
    rw [h3] at hw
    linarith
  set a : ℕ → ℂ := domainSampleNode z₀ R with hadef
  have hnodedist : ∀ i, dist (a i) z₀ ≤ R / 2 := by
    intro i
    rw [hadef, dist_domainSampleNode z₀ hRpos i]
    have hk2 : (2:ℝ) ≤ (i : ℝ) + 2 := by
      have : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    exact div_le_div_of_nonneg_left hRpos.le (by norm_num) hk2
  have hnodes : ∀ i, a i ∈ Sᶜ := by
    intro i
    refine hnear _ ?_
    have h1 := hnodedist i
    nlinarith [hRpos, hLam1]
  have hshift : ∀ h : ℂ, ‖h‖ < R → ∀ i (l : Fin J), a i + lam l * h ∈ Sᶜ := by
    intro h hh i l
    refine hnear _ ?_
    have h1 : dist (a i + lam l * h) (a i) = ‖lam l * h‖ := by simp [dist_eq_norm]
    have h2 := dist_triangle (a i + lam l * h) (a i) z₀
    have h3 := hnodedist i
    have h4 : ‖lam l * h‖ ≤ Lam * R := by
      rw [norm_mul]
      have := hLamle l
      nlinarith [norm_nonneg (lam l), norm_nonneg h, hh.le, hLampos]
    rw [h1] at h2
    nlinarith [hRpos, hLam1]
  have hshiftz₀ : ∀ h : ℂ, ‖h‖ < R → ∀ l : Fin J, z₀ + lam l * h ∈ Sᶜ := by
    intro h hh l
    refine hnear _ ?_
    have h1 : dist (z₀ + lam l * h) z₀ = ‖lam l * h‖ := by simp [dist_eq_norm]
    have h4 : ‖lam l * h‖ ≤ Lam * R := by
      rw [norm_mul]
      have := hLamle l
      nlinarith [norm_nonneg (lam l), norm_nonneg h, hh.le, hLampos]
    rw [h1]
    nlinarith [hRpos, hLam1]
  by_cases hcase : ∃ n d : ℕ, ∀ (φ : JetExponent n d → ℕ) (h : ℂ), ‖h‖ < R →
      (coordinateMinor (domainJetSampleRow (stencilApply F c lam h) z₀ R n d) φ).det = 0
  · exfalso
    obtain ⟨n, d, hrel⟩ := hcase
    have hconn : IsPreconnected (Sᶜ) := isPreconnected_compl_of_countable hScount hz₀
    exact hFht (differentiallyAlgebraicOn_of_uniform_stencil_relations hopen hconn hF hlow hk
      hRpos hz₀ hnodes hRpos (fun h hh i l => hshift h hh i l) hrel)
  · push Not at hcase
    choose φ hwit hwitlt hwitne using hcase
    set Bad : Set ℂ :=
      (⋃ l : Fin J, ((fun h : ℂ => z₀ + lam l * h) ⁻¹' S)) ∪
        ⋃ (i : ℕ) (l : Fin J), ((fun h : ℂ => a i + lam l * h) ⁻¹' S) with hBaddef
    have hpreCount : ∀ (b : ℂ) (l : Fin J), b ∈ Sᶜ →
        ((fun h : ℂ => b + lam l * h) ⁻¹' S).Countable := by
      intro b l hb
      by_cases hl : lam l = 0
      · have hempty : ((fun h : ℂ => b + lam l * h) ⁻¹' S) = ∅ := by
          ext h
          simp only [Set.mem_preimage, hl, zero_mul, add_zero, Set.mem_empty_iff_false,
            iff_false]
          exact hb
        rw [hempty]
        exact Set.countable_empty
      · refine hScount.preimage ?_
        intro x y hxy
        have := add_left_cancel hxy
        exact mul_left_cancel₀ hl this
    have hBadCount : Bad.Countable := by
      refine Set.Countable.union (Set.countable_iUnion fun l => hpreCount z₀ l hz₀) ?_
      exact Set.countable_iUnion fun i => Set.countable_iUnion fun l => hpreCount (a i) l (hnodes i)
    set U : ℕ × ℕ → Set ℂ := fun p =>
      (⋃ (i : JetExponent p.1 p.2) (l : Fin J),
        ((fun h : ℂ => a (φ p.1 p.2 i) + lam l * h) ⁻¹' S))ᶜ with hUdef
    have hUcount : ∀ p : ℕ × ℕ,
        (⋃ (i : JetExponent p.1 p.2) (l : Fin J),
          ((fun h : ℂ => a (φ p.1 p.2 i) + lam l * h) ⁻¹' S)).Countable := by
      intro p
      exact Set.countable_iUnion fun i => Set.countable_iUnion fun l =>
        hpreCount (a (φ p.1 p.2 i)) l (hnodes _)
    have hmemU : ∀ (p : ℕ × ℕ) (h : ℂ), (∀ i (l : Fin J), a i + lam l * h ∈ Sᶜ) → h ∈ U p := by
      intro p h hik
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
      intro i l
      exact hik (φ p.1 p.2 i) l
    have hUanal : ∀ p : ℕ × ℕ,
        AnalyticOnNhd ℂ (stencilShiftMinorDet F c lam z₀ R p.1 p.2 (φ p.1 p.2)) (U p) := by
      intro p h₀ hh₀
      refine analyticAt_stencilShiftMinorDet hF c lam p.1 p.2 (φ p.1 p.2) ?_
      intro i l
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists] at hh₀
      exact hh₀ i l
    have hUwit : ∀ p : ℕ × ℕ, hwit p.1 p.2 ∈ U p := by
      intro p
      exact hmemU p _ (fun i l => hshift _ (hwitlt p.1 p.2) i l)
    have hUwitne : ∀ p : ℕ × ℕ,
        stencilShiftMinorDet F c lam z₀ R p.1 p.2 (φ p.1 p.2) (hwit p.1 p.2) ≠ 0 := by
      intro p
      rw [stencilShiftMinorDet_eq hopen hF c lam p.1 p.2 (φ p.1 p.2)
        (fun i l => hshift _ (hwitlt p.1 p.2) i l)]
      exact hwitne p.1 p.2
    have hUconn : ∀ p : ℕ × ℕ, IsPreconnected (U p) := fun p =>
      isPreconnected_compl_of_countable (hUcount p) (hUwit p)
    have hzeroCount : ∀ p : ℕ × ℕ,
        {h ∈ U p | stencilShiftMinorDet F c lam z₀ R p.1 p.2 (φ p.1 p.2) h = 0}.Countable :=
      fun p => Bottcher.analyticOnNhd_zeros_countable (hUanal p) (hUconn p) (hUwit p) (hUwitne p)
    refine Set.Countable.mono ?_ (Set.Countable.union hBadCount
      (Set.countable_iUnion fun p : ℕ × ℕ => hzeroCount p))
    intro h hh
    by_cases hbad : h ∈ Bad
    · exact Or.inl hbad
    · refine Or.inr ?_
      have hgood : ∀ i (l : Fin J), a i + lam l * h ∈ Sᶜ := by
        intro i l hmem
        exact hbad (Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨l, hmem⟩⟩))
      have hz₀good : ∀ l : Fin J, z₀ + lam l * h ∈ Sᶜ := by
        intro l hmem
        exact hbad (Or.inl (Set.mem_iUnion.2 ⟨l, hmem⟩))
      have hz₀dom : z₀ ∈ stencilDomain S lam h := mem_stencilDomain (fun l => hz₀good l)
      have hnodesdom : ∀ i, a i ∈ stencilDomain S lam h := fun i =>
        mem_stencilDomain (fun l => hgood i l)
      have hdomconn : IsPreconnected (stencilDomain S lam h) :=
        isPreconnected_compl_of_countable (countable_stencilSingularSet hScount lam h) hz₀dom
      have hdefanal : AnalyticOnNhd ℂ (stencilApply F c lam h) (stencilDomain S lam h) :=
        analyticOnNhd_stencilApply hF c lam h
      obtain ⟨n, d, hall⟩ :=
        (differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero (z₀ := z₀) (r := R)
          hdomconn hdefanal hz₀dom hnodesdom hRpos).1 hh
      refine Set.mem_iUnion.2 ⟨(n, d), ?_, ?_⟩
      · exact hmemU (n, d) h hgood
      · rw [stencilShiftMinorDet_eq hopen hF c lam n d (φ n d) (fun i l => hgood i l)]
        exact hall (φ n d)


/-- **The differentially algebraic side of the dichotomy.**  If the source itself satisfies an
algebraic differential equation, then so does every stencil, at every shift parameter. -/
theorem stencilDAStabilizer_eq_univ_of_differentiallyAlgebraicOn {F : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable) (hF : AnalyticOnNhd ℂ F Sᶜ)
    (hFDA : DifferentiallyAlgebraicOn F Sᶜ) (c lam : Fin J → ℂ) :
    stencilDAStabilizer F S c lam = Set.univ := by
  classical
  ext h
  simp only [Set.mem_univ, iff_true, stencilDAStabilizer, Set.mem_setOf_eq]
  have hDopen : IsOpen (stencilDomain S lam h) :=
    (isClosed_stencilSingularSet hSclosed lam h).isOpen_compl
  have hDcount := countable_stencilSingularSet hScount lam h
  obtain ⟨w₀, hw₀⟩ : (stencilDomain S lam h).Nonempty := nonempty_compl_of_countable hDcount
  have hDconn : IsPreconnected (stencilDomain S lam h) :=
    isPreconnected_compl_of_countable hDcount hw₀
  have hDinf : (stencilDomain S lam h).Infinite := infinite_compl_of_countable hDcount
  have hsub : ∀ l : Fin J,
      stencilDomain S lam h ⊆ {z : ℂ | z + lam l * h ∈ Sᶜ} := by
    intro l z hz
    exact stencilDomain_mem_compl hz l
  have hshiftAnal : ∀ l : Fin J,
      AnalyticOnNhd ℂ (fun z => F (z + lam l * h)) (stencilDomain S lam h) := by
    intro l z hz
    have hout : AnalyticAt ℂ F (z + lam l * h) := hF _ (stencilDomain_mem_compl hz l)
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + lam l * h) z := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun w : ℂ => w + lam l * h) (x := z) hout hinner
  have hshiftDA : ∀ l : Fin J,
      DifferentiallyAlgebraicOn (fun z => F (z + lam l * h)) (stencilDomain S lam h) := by
    intro l
    obtain ⟨n, P, hP0, hPv⟩ := DifferentiallyAlgebraicOn.comp_add_const hFDA (lam l * h)
    exact ⟨n, P, hP0, fun z hz => hPv z (hsub l hz)⟩
  have hterm : ∀ l : Fin J,
      AnalyticOnNhd ℂ (fun z => c l * F (z + lam l * h)) (stencilDomain S lam h) := by
    intro l z hz
    exact analyticAt_const.mul (hshiftAnal l z hz)
  have htermDA : ∀ l : Fin J,
      DifferentiallyAlgebraicOn (fun z => c l * F (z + lam l * h)) (stencilDomain S lam h) :=
    fun l => differentiallyAlgebraicOn_const_mul hDopen hDconn ⟨w₀, hw₀⟩ hDinf (c l)
      (hshiftAnal l) (hshiftDA l)
  have hsum := differentiallyAlgebraicOn_finsetSum hDopen hDconn ⟨w₀, hw₀⟩ hDinf
    (Finset.univ : Finset (Fin J)) (fun l _ => hterm l) (fun l _ => htermDA l)
  exact hsum

end

end GaloisForLFunctions.HTGeometry
