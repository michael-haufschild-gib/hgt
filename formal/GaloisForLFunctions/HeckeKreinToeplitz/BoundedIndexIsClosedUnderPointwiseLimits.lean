import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise

/-!
# Bounded index is closed under pointwise limits

The transfer theorem of the theory: the topology in which indefinite kernels of bounded index
form a closed set is pointwise convergence of kernels.

**Matrix level** (`eventually_le_hermNegIndex`). If `H_n → H` entrywise and `H` is Hermitian, then
eventually `hermNegIndex H ≤ hermNegIndex H_n`. Compressing by the negative eigenvectors `S` of `H`
turns `Sᴴ H S` into a negative diagonal; `Sᴴ H_n S` converges to it entrywise and is eventually
negative definite (`eventually_negDef_of_entrywise_tendsto_diagonal`), so `S` carries a
negative-definite subspace of `H_n` of the same dimension.

**Kernel level** (`negIndex_le_of_tendsto`). If `k_n → k` pointwise, `k` is Hermitian and
eventually `κ(k_n) ≤ m`, then `κ(k) ≤ m`: the negative index is lower semicontinuous. Atomic and
truncated families converge in this topology; the Weil form is not continuous on `L²` of tests,
and that topology does not carry index bounds.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Complex Matrix Finset Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lower semicontinuity of the negative index for matrices.** -/
theorem eventually_le_hermNegIndex {β : Type*} {l : Filter β} {H : β → Matrix ι ι ℂ}
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (hH : ∀ a b, Tendsto (fun n => H n a b) l (𝓝 (H₀ a b))) :
    ∀ᶠ n in l, hermNegIndex H₀ ≤ hermNegIndex (H n) := by
  set s : Finset ι := {i | hH₀.eigenvalues i < 0}
  rw [negIndex_eq_card_neg_eigenvalues hH₀]
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · exact Eventually.of_forall fun n => by rw [h0]; exact Nat.zero_le _
  -- compression to the negative eigenvectors
  set f : Fin s.card → ι := fun j => (s.equivFin.symm j : ι)
  have hf : Function.Injective f := fun j k h => s.equivFin.symm.injective (Subtype.ext h)
  set U : Matrix ι ι ℂ := (hH₀.eigenvectorUnitary : Matrix ι ι ℂ)
  set S : Matrix ι (Fin s.card) ℂ := U.submatrix id f
  set c : Fin s.card → ℝ := fun j => hH₀.eigenvalues (f j)
  have hcneg : ∀ j, c j < 0 := fun j => (Finset.mem_filter.mp (s.equivFin.symm j).2).2
  have hcomp : ∀ M : Matrix ι ι ℂ, Sᴴ * M * S = (Uᴴ * M * U).submatrix f f := fun M => by
    rw [submatrix_mul _ _ f id f Function.bijective_id, submatrix_mul _ _ f id id
      Function.bijective_id, submatrix_id_id, conjTranspose_submatrix]
  have hG₀ : Sᴴ * H₀ * S = diagonal fun j => ((c j : ℝ) : ℂ) := by
    rw [hcomp, conjTranspose_mul_mul_eigenvectorUnitary hH₀, submatrix_diagonal _ _ hf]
    rfl
  -- the margin
  obtain ⟨j₀, -, hj₀⟩ := exists_min_image univ (fun j => -c j) ⟨⟨0, hpos⟩, mem_univ _⟩
  have hδ : 0 < -c j₀ := neg_pos.mpr (hcneg j₀)
  have hc : ∀ j, c j ≤ -(-c j₀) := fun j => by linarith [hj₀ j (mem_univ j)]
  -- entrywise convergence of the compressions
  have hT : Tendsto (fun n => Sᴴ * H n * S) l (𝓝 (Sᴴ * H₀ * S)) := by
    have hHt : Tendsto H l (𝓝 H₀) :=
      tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => hH a b
    exact (((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).tendsto H₀).comp hHt
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ j k,
      ‖(Sᴴ * H n * S) j k - (diagonal fun j => ((c j : ℝ) : ℂ)) j k‖ ≤ ε := fun ε hε => by
    rw [← hG₀]
    refine eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
    have hjk : Tendsto (fun n => (Sᴴ * H n * S) j k) l (𝓝 ((Sᴴ * H₀ * S) j k)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT j) k
    exact (Metric.tendsto_nhds.mp hjk ε hε).mono fun n hn => by
      rw [← dist_eq_norm]; exact hn.le
  filter_upwards [eventually_negDef_of_entrywise_tendsto_diagonal (fun n => Sᴴ * H n * S) c hδ hc
    hconv] with n hn
  refine (Fintype.card_fin s.card).symm.le.trans
    (card_le_hermNegIndex_of_forall_neg (H n) S.mulVecLin fun x hx => ?_)
  rw [Matrix.mulVecLin_apply, ← hermQuad_rect_conjugate]
  exact hn x hx

variable {G : Type*} [Group G]

/-- A pointwise limit of Hermitian kernels is Hermitian. -/
theorem isHermKernel_of_tendsto {β : Type*} {l : Filter β} [l.NeBot] {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g)))
    (hh : ∀ᶠ n in l, IsHermKernel (k n)) : IsHermKernel k₀ := fun u =>
  tendsto_nhds_unique (hk u⁻¹) (((continuous_conj.tendsto _).comp (hk u)).congr'
    (hh.mono fun _ hn => (hn u).symm))

/-- **Transfer: bounded index is closed under pointwise limits.** If Hermitian kernels `k_n`
converge pointwise to `k` and eventually `κ(k_n) ≤ m`, then `κ(k) ≤ m`. -/
theorem negIndex_le_of_tendsto {β : Type*} {l : Filter β} [l.NeBot] {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g)))
    (hh : ∀ᶠ n in l, IsHermKernel (k n)) {m : ℕ∞} (hm : ∀ᶠ n in l, negIndex (k n) ≤ m) :
    negIndex k₀ ≤ m := by
  classical
  rw [negIndex_le_iff]
  intro _ x
  have hconv := eventually_le_hermNegIndex (H := fun n => gram (k n) x)
    (gram_isHermitian (isHermKernel_of_tendsto hk hh) x) fun a b => hk _
  obtain ⟨n, hn, hnm⟩ := (hconv.and hm).exists
  exact (Nat.cast_le.mpr hn).trans ((hermNegIndex_gram_le_negIndex _ x).trans hnm)

/-- Positive definiteness is closed under pointwise limits. -/
theorem isPosDefKernel_of_tendsto {β : Type*} {l : Filter β} [l.NeBot] {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g)))
    (hp : ∀ᶠ n in l, IsPosDefKernel (k n)) : IsPosDefKernel k₀ := by
  have hh := hp.mono fun _ h => h.1
  refine (isPosDefKernel_iff (isHermKernel_of_tendsto hk hh)).mpr (nonpos_iff_eq_zero.mp ?_)
  exact negIndex_le_of_tendsto hk hh (hp.mono fun _ h => h.negIndex_eq_zero.le)

end GaloisForLFunctions.HeckeKreinToeplitz
