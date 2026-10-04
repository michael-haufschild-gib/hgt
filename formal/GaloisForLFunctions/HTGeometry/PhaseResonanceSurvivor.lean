import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The positive resonant survivor of a phase packet

For a finite phase packet `U eⱼ = zⱼ eⱼ` on `ℂ^ι`, the resonance pinching
`Π_U(X) = ∑_λ P_λ X P_λ` keeps the entries with `zⱼ = z_k`, and
`δ_U(X)_{jk} = (1 - z̄ⱼ z_k) X_{jk}`.

* **No positive coboundary.**  For `X ≥ 0`, `Π_U X ≥ 0` and `tr Π_U X = tr X`; a nonzero positive
  matrix therefore has a nonzero positive survivor and is not a transgression `δ_U Y`.
* **Rank transmutation.**  `Π_U(v v*) = ∑_λ v_λ v_λ*` with `v_λ = P_λ v`; its rank is the number of
  occupied phase classes; the Hilbert–Schmidt energy splits as
  `‖v v*‖² = ‖Π_U(v v*)‖² + ‖(1 - Π_U)(v v*)‖²` with `‖Π_U(v v*)‖² = ∑_λ ‖v_λ‖⁴`.
* **Cofinal prediction.**  Along an exhausting aperture sequence of a packet with infinitely many
  distinct phases and a nowhere-vanishing vector, the survivor rank and the oscillatory inverse
  norm both tend to infinity, and the limiting transgression range is not closed.
-/

open Filter Topology Set Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section FiniteMatrix

variable {ι : Type*} (z : ι → ℂ)

/-- The resonance pinching `Π_U` on matrices. -/
def resonancePinch (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun j k => if z j = z k then X j k else 0

/-- The transgression `δ_U` on matrices. -/
def phaseTransgressionMat (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun j k => (1 - conj (z j) * z k) * X j k

/-- The spectral projection `P_λ` of `U` onto the phase class `λ`. -/
def phaseSpectralProj [DecidableEq ι] (c : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun j => if z j = c then 1 else 0

/-- The component `v_λ = P_λ v` of a vector in the phase class `λ`. -/
def phaseComponent (c : ℂ) (v : ι → ℂ) : ι → ℂ := fun j => if z j = c then v j else 0

variable {z}

theorem conjTranspose_phaseSpectralProj [DecidableEq ι] (c : ℂ) :
    (phaseSpectralProj z c)ᴴ = phaseSpectralProj z c := by
  ext i j
  simp only [phaseSpectralProj, conjTranspose_apply, diagonal_apply]
  split_ifs <;> simp_all

/-- `Π_U(X) = ∑_λ P_λ X P_λ`. -/
theorem resonancePinch_eq_sum [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    resonancePinch z X =
      ∑ c ∈ Finset.univ.image z, phaseSpectralProj z c * X * phaseSpectralProj z c := by
  ext j k
  rw [Matrix.sum_apply, Finset.sum_eq_single (z j)]
  · simp only [resonancePinch, phaseSpectralProj, of_apply, mul_diagonal, diagonal_mul,
      if_true, one_mul]
    split_ifs with h1 h2 <;> simp_all
  · intro c _ hc
    simp only [phaseSpectralProj, mul_diagonal, diagonal_mul]
    rw [if_neg (Ne.symm hc)]
    simp
  · intro h
    exact absurd (Finset.mem_image_of_mem z (Finset.mem_univ j)) h

/-- **Theorem 5.1.**  The pinching of a positive matrix is positive. -/
theorem resonancePinch_posSemidef [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) :
    (resonancePinch z X).PosSemidef := by
  rw [resonancePinch_eq_sum]
  refine posSemidef_sum _ fun c _ => ?_
  have h := hX.conjTranspose_mul_mul_same (phaseSpectralProj z c)
  rwa [conjTranspose_phaseSpectralProj] at h

/-- **Theorem 5.1.**  Block compression preserves the trace. -/
theorem trace_resonancePinch [Fintype ι] (X : Matrix ι ι ℂ) :
    trace (resonancePinch z X) = trace X := by
  simp [trace, resonancePinch]

/-- The pinching kills every transgression: `Π_U δ_U = 0`. -/
theorem resonancePinch_phaseTransgressionMat (hz : ∀ j, ‖z j‖ = 1) (Y : Matrix ι ι ℂ) :
    resonancePinch z (phaseTransgressionMat z Y) = 0 := by
  ext j k
  simp only [resonancePinch, phaseTransgressionMat, of_apply, Matrix.zero_apply]
  split_ifs with h
  · have := (one_sub_phaseRatio_eq_zero_iff hz (j, k)).mpr h
    simp only [phaseRatio] at this
    rw [this, zero_mul]
  · rfl

/-- **Theorem 5.1.**  A nonzero positive packet has a nonzero positive survivor of the same
positive trace, and is not a transgression. -/
theorem positive_resonant_survivor [Fintype ι] [DecidableEq ι] (hz : ∀ j, ‖z j‖ = 1)
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (hX0 : X ≠ 0) :
    (resonancePinch z X).PosSemidef ∧ trace (resonancePinch z X) = trace X ∧ 0 < trace X ∧
      resonancePinch z X ≠ 0 ∧ ¬ ∃ Y, phaseTransgressionMat z Y = X := by
  have htr : 0 < trace X :=
    lt_of_le_of_ne hX.trace_nonneg (Ne.symm fun h => hX0 (hX.trace_eq_zero_iff.mp h))
  have hne : resonancePinch z X ≠ 0 := by
    intro h
    have := trace_resonancePinch (z := z) X
    rw [h, trace_zero] at this
    exact htr.ne this
  refine ⟨resonancePinch_posSemidef hX, trace_resonancePinch X, htr, hne, ?_⟩
  rintro ⟨Y, rfl⟩
  exact hne (resonancePinch_phaseTransgressionMat hz Y)

/-! ### Rank transmutation -/

theorem phaseComponent_apply_of_eq {c : ℂ} {v : ι → ℂ} {j : ι} (h : z j = c) :
    phaseComponent z c v j = v j := if_pos h

theorem phaseComponent_apply_of_ne {c : ℂ} {v : ι → ℂ} {j : ι} (h : z j ≠ c) :
    phaseComponent z c v j = 0 := if_neg h

/-- **`(CTR.13)`.**  `Π_U(v v*) = ∑_λ v_λ v_λ*`. -/
theorem resonancePinch_vecMulVec [Fintype ι] (v : ι → ℂ) :
    resonancePinch z (vecMulVec v (star v)) =
      ∑ c ∈ Finset.univ.image z,
        vecMulVec (phaseComponent z c v) (star (phaseComponent z c v)) := by
  ext j k
  rw [Matrix.sum_apply, Finset.sum_eq_single (z j)]
  · simp only [resonancePinch, of_apply, vecMulVec_apply, Pi.star_apply, phaseComponent, if_true]
    split_ifs with h1 h2 <;> simp_all
  · intro c _ hc
    simp [vecMulVec_apply, phaseComponent, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_image_of_mem z (Finset.mem_univ j)) h

/-- The occupied phase classes of `v`. -/
def occupiedPhases [Fintype ι] (z : ι → ℂ) (v : ι → ℂ) : Finset ℂ :=
  (Finset.univ.image z).filter fun c => phaseComponent z c v ≠ 0

theorem resonancePinch_vecMulVec_occupied [Fintype ι] (v : ι → ℂ) :
    resonancePinch z (vecMulVec v (star v)) =
      ∑ c ∈ occupiedPhases z v,
        vecMulVec (phaseComponent z c v) (star (phaseComponent z c v)) := by
  rw [resonancePinch_vecMulVec, occupiedPhases, Finset.sum_filter_of_ne]
  intro c _ hc h
  exact hc (by rw [h]; simp)

theorem dotProduct_star_phaseComponent [Fintype ι] {c d : ℂ} (hcd : c ≠ d) (v : ι → ℂ) :
    star (phaseComponent z c v) ⬝ᵥ phaseComponent z d v = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [Pi.star_apply, phaseComponent]
  split_ifs with h1 h2 <;> simp_all

theorem mulVec_resonancePinch_phaseComponent [Fintype ι] (v : ι → ℂ) {c : ℂ}
    (hc : c ∈ occupiedPhases z v) :
    resonancePinch z (vecMulVec v (star v)) *ᵥ phaseComponent z c v =
      (star (phaseComponent z c v) ⬝ᵥ phaseComponent z c v) • phaseComponent z c v := by
  rw [resonancePinch_vecMulVec_occupied, sum_mulVec, Finset.sum_eq_single c]
  · rw [vecMulVec_mulVec]
    ext j
    simp [mul_comm]
  · intro d _ hdc
    rw [vecMulVec_mulVec, dotProduct_star_phaseComponent hdc]
    ext j
    simp
  · intro h
    exact absurd hc h

theorem dotProduct_star_self_ne_zero [Fintype ι] {w : ι → ℂ} (hw : w ≠ 0) : star w ⬝ᵥ w ≠ 0 := by
  intro h
  exact hw (dotProduct_star_self_eq_zero.mp h)

theorem linearIndependent_phaseComponent [Fintype ι] (v : ι → ℂ) :
    LinearIndependent ℂ fun c : occupiedPhases z v => phaseComponent z c v := by
  rw [linearIndependent_iff']
  intro s g hsum c hc
  have hocc := (Finset.mem_filter.mp c.2).2
  obtain ⟨j, hj⟩ : ∃ j, phaseComponent z c v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hocc (funext h)
  have hjc : z j = c := by
    by_contra h
    exact hj (phaseComponent_apply_of_ne h)
  have h := congrFun hsum j
  rw [Finset.sum_apply, Finset.sum_eq_single c] at h
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right hj
  · intro d _ hdc
    have : z j ≠ d := by
      rw [hjc]
      exact fun h => hdc (Subtype.ext h.symm)
    simp [phaseComponent_apply_of_ne this]
  · intro h'
    exact absurd hc h'

/-- **`(CTR.14)`.**  The rank of the survivor of a rank-one packet is the number of occupied phase
classes. -/
theorem rank_resonancePinch_vecMulVec [Fintype ι] (v : ι → ℂ) :
    (resonancePinch z (vecMulVec v (star v))).rank = (occupiedPhases z v).card := by
  set M := resonancePinch z (vecMulVec v (star v))
  have hrange : LinearMap.range M.mulVecLin =
      Submodule.span ℂ (Set.range fun c : occupiedPhases z v => phaseComponent z c v) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [mulVecLin_apply, show M = _ from resonancePinch_vecMulVec_occupied v, sum_mulVec]
      refine Submodule.sum_mem _ fun c hc => ?_
      rw [vecMulVec_mulVec, op_smul_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      have hne := dotProduct_star_self_ne_zero (Finset.mem_filter.mp c.2).2
      refine ⟨(star (phaseComponent z c v) ⬝ᵥ phaseComponent z c v)⁻¹ • phaseComponent z c v, ?_⟩
      rw [mulVecLin_apply, mulVec_smul, mulVec_resonancePinch_phaseComponent v c.2, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
  rw [Matrix.rank, hrange, finrank_span_eq_card (linearIndependent_phaseComponent v),
    Fintype.card_coe]

/-- The squared Hilbert–Schmidt (Frobenius) norm `∑_{j,k} |X_{jk}|²`. -/
def matrixHSNormSq [Fintype ι] (X : Matrix ι ι ℂ) : ℝ := ∑ j, ∑ k, ‖X j k‖ ^ 2

/-- **`(CTR.15)`.**  Exact conservation of Hilbert–Schmidt energy: formation separates neutral
population from oscillatory coherence. -/
theorem matrixHSNormSq_eq_resonancePinch_add [Fintype ι] (X : Matrix ι ι ℂ) :
    matrixHSNormSq X =
      matrixHSNormSq (resonancePinch z X) + matrixHSNormSq (X - resonancePinch z X) := by
  simp only [matrixHSNormSq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [resonancePinch, Matrix.sub_apply, of_apply]
  split_ifs <;> simp

/-- **`(CTR.16)`.**  `‖Π_U(v v*)‖² = ∑_λ ‖v_λ‖⁴`. -/
theorem matrixHSNormSq_resonancePinch_vecMulVec [Fintype ι] (v : ι → ℂ) :
    matrixHSNormSq (resonancePinch z (vecMulVec v (star v))) =
      ∑ c ∈ Finset.univ.image z, (∑ j, ‖phaseComponent z c v j‖ ^ 2) ^ 2 := by
  have hcomp : ∀ c, ∑ j, ‖phaseComponent z c v j‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j => z j = c), ‖v j‖ ^ 2 := by
    intro c
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold phaseComponent
    split_ifs <;> simp
  simp_rw [hcomp]
  have hrow : ∀ j, ∑ k, ‖resonancePinch z (vecMulVec v (star v)) j k‖ ^ 2 =
      ‖v j‖ ^ 2 * ∑ k ∈ Finset.univ.filter (fun k => z k = z j), ‖v k‖ ^ 2 := by
    intro j
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [resonancePinch, of_apply, vecMulVec_apply, Pi.star_apply]
    split_ifs with h1 h2 h2
    · rw [norm_mul, mul_pow, norm_star]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [matrixHSNormSq]
  simp_rw [hrow]
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.univ.image z)
    (fun j _ => Finset.mem_image_of_mem z (Finset.mem_univ j))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]

/-- Reflection `z ↦ z̄` leaves the pinching, hence the survivor and its rank, unchanged. -/
theorem resonancePinch_conj (X : Matrix ι ι ℂ) :
    resonancePinch (fun j => conj (z j)) X = resonancePinch z X := by
  ext j k
  simp only [resonancePinch, of_apply, (RingHom.injective (starRingEnd ℂ)).eq_iff]

end FiniteMatrix

/-! ### Cofinal prediction -/

section Cofinal

variable {J : Type*} [DecidableEq J] {z : J → ℂ}

/-- With a nowhere-vanishing vector every phase class is occupied, so the survivor rank is the
number of distinct phases. -/
theorem rank_resonancePinch_vecMulVec_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ι → ℂ} {v : ι → ℂ} (hv : ∀ j, v j ≠ 0) :
    (resonancePinch w (vecMulVec v (star v))).rank = (Finset.univ.image w).card := by
  rw [rank_resonancePinch_vecMulVec]
  congr 1
  refine Finset.filter_true_of_mem fun c hc => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hc
  intro h
  have := congrFun h j
  rw [phaseComponent_apply_of_eq rfl] at this
  exact hv j this

theorem exists_eventually_mem_of_exhaust {E : ℕ → Finset J} (hmono : Monotone E)
    (hexh : ∀ j, ∃ N, j ∈ E N) (s : Finset J) : ∀ᶠ N in atTop, s ⊆ E N := by
  induction s using Finset.induction_on with
  | empty => exact Eventually.of_forall fun N => Finset.empty_subset _
  | insert j s hj ih =>
      obtain ⟨N₀, hN₀⟩ := hexh j
      filter_upwards [ih, eventually_ge_atTop N₀] with N hN hNN
      exact Finset.insert_subset (hmono hNN hN₀) hN

/-- **Corollary 6.2.**  Along an exhausting aperture sequence of a packet with infinitely many
distinct unit phases and a nowhere-vanishing vector: the survivor rank tends to infinity, the
aperture gaps tend to zero so the oscillatory inverse norms `g_N⁻¹ = ‖G_{U_N}‖` tend to infinity,
and the limiting transgression range is not closed. -/
theorem cofinal_rank_topology (hz : ∀ j, ‖z j‖ = 1) (hinf : (Set.range z).Infinite)
    {E : ℕ → Finset J} (hmono : Monotone E) (hexh : ∀ j, ∃ N, j ∈ E N) {v : J → ℂ}
    (hv : ∀ j, v j ≠ 0) :
    Tendsto (fun N => (resonancePinch (fun j : E N => z j)
        (vecMulVec (fun j : E N => v j) (star fun j : E N => v j))).rank) atTop atTop ∧
      (∀ᶠ N in atTop, (∃ p : E N × E N, z p.1 ≠ z p.2) ∧
        0 < transgressionGap (fun j : E N => z j)) ∧
      Tendsto (fun N => (transgressionGap (fun j : E N => z j))⁻¹) atTop atTop ∧
      ¬ IsClosed (Set.range (phaseTransgression hz)) := by
  refine ⟨?_, ?_, ?_, fun h => hinf ((isClosed_range_phaseTransgression_iff_finite hz).mp h)⟩
  · -- survivor rank = number of distinct phases in the aperture
    have hrank : ∀ N, (resonancePinch (fun j : E N => z j)
        (vecMulVec (fun j : E N => v j) (star fun j : E N => v j))).rank =
        (Finset.univ.image fun j : E N => z j).card := fun N =>
      rank_resonancePinch_vecMulVec_of_ne_zero (fun j : E N => hv j)
    simp_rw [hrank]
    rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq M
    choose f hf using fun c : T => hTsub c.2
    obtain ⟨N, hN⟩ := (exists_eventually_mem_of_exhaust hmono hexh
      (Finset.univ.image f)).exists_forall_of_atTop
    refine ⟨N, fun N' hN' => ?_⟩
    have hsub := hN N' hN'
    rw [← hTcard]
    refine Finset.card_le_card fun c hc => ?_
    have hfc : f ⟨c, hc⟩ ∈ E N' := hsub (Finset.mem_image_of_mem f (Finset.mem_univ _))
    exact Finset.mem_image.mpr ⟨⟨f ⟨c, hc⟩, hfc⟩, Finset.mem_univ _, hf ⟨c, hc⟩⟩
  · -- eventually two distinct phases occur
    obtain ⟨a, ⟨j, rfl⟩, b, ⟨k, rfl⟩, hab, -⟩ :=
      exists_ne_norm_sub_lt_of_infinite hinf (by rintro _ ⟨j, rfl⟩; exact hz j) one_pos
    filter_upwards [exists_eventually_mem_of_exhaust hmono hexh {j, k}] with N hN
    have hj : j ∈ E N := hN (by simp)
    have hk : k ∈ E N := hN (by simp)
    have hzF : ∀ i : E N, ‖z i‖ = 1 := fun i => hz i
    obtain ⟨c, hc⟩ := exists_phaseSeparated_of_finite (J := E N) hzF
    refine ⟨⟨(⟨j, hj⟩, ⟨k, hk⟩), hab⟩, lt_of_lt_of_le hc.1 (le_csInf
      ⟨_, (⟨j, hj⟩, ⟨k, hk⟩), hab, rfl⟩ (by rintro _ ⟨p, hp, rfl⟩; exact hc.2 p hp))⟩
  · -- the aperture gaps tend to zero
    refine Tendsto.inv_tendsto_nhdsGT_zero ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨a, ⟨j, rfl⟩, b, ⟨k, rfl⟩, hab, hlt⟩ :=
        exists_ne_norm_sub_lt_of_infinite hinf (by rintro _ ⟨j, rfl⟩; exact hz j) hε
      obtain ⟨N, hN⟩ := (exists_eventually_mem_of_exhaust hmono hexh {j, k}).exists_forall_of_atTop
      refine ⟨N, fun N' hN' => ?_⟩
      have hj : j ∈ E N' := hN N' hN' (by simp)
      have hk : k ∈ E N' := hN N' hN' (by simp)
      have hzF : ∀ i : E N', ‖z i‖ = 1 := fun i => hz i
      obtain ⟨c, hc⟩ := exists_phaseSeparated_of_finite (J := E N') hzF
      have hpos : 0 < transgressionGap (fun i : E N' => z i) := lt_of_lt_of_le hc.1 (le_csInf
        ⟨_, (⟨j, hj⟩, ⟨k, hk⟩), hab, rfl⟩ (by rintro _ ⟨p, hp, rfl⟩; exact hc.2 p hp))
      have hle := transgressionGap_le (z := fun i : E N' => z i) (p := (⟨j, hj⟩, ⟨k, hk⟩)) hab
      rw [norm_one_sub_phaseRatio hzF] at hle
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      exact lt_of_le_of_lt hle hlt
    · obtain ⟨a, ⟨j, rfl⟩, b, ⟨k, rfl⟩, hab, -⟩ :=
        exists_ne_norm_sub_lt_of_infinite hinf (by rintro _ ⟨j, rfl⟩; exact hz j) one_pos
      filter_upwards [exists_eventually_mem_of_exhaust hmono hexh {j, k}] with N hN
      have hj : j ∈ E N := hN (by simp)
      have hk : k ∈ E N := hN (by simp)
      have hzF : ∀ i : E N, ‖z i‖ = 1 := fun i => hz i
      obtain ⟨c, hc⟩ := exists_phaseSeparated_of_finite (J := E N) hzF
      exact lt_of_lt_of_le hc.1 (le_csInf
        ⟨_, (⟨j, hj⟩, ⟨k, hk⟩), hab, rfl⟩ (by rintro _ ⟨p, hp, rfl⟩; exact hc.2 p hp))

end Cofinal

end GaloisForLFunctions.HTGeometry
