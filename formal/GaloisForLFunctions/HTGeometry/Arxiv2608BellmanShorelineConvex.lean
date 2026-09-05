import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature

/-!
# Exposed-face certificates from arXiv:2608.29060

The paper's historical-certificate theorem sharpens the usual `D + 1` Carathéodory bound to `D`:
at a bottleneck, every supplier in a positive convex certificate lies on one exposed affine
hyperplane. This module proves that dimension drop for arbitrary subsets of coordinate space.

The result is stated through `atomicSpan D`, so zero-weight padding exposes a fixed-size API while
retaining the mathematical claim “at most `D` genuine suppliers”.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {N : ℕ}

/-- Slice of `K` on the support plane `n ⬝ᵥ x = μ`. -/
def bellmanShorelineExposedSlice
    (K : Set (Fin N → ℝ)) (n : Fin N → ℝ) (mu : ℝ) : Set (Fin N → ℝ) :=
  {x | x ∈ K ∧ dotProduct n x = mu}

/-- **Historical certificate of rank at most `N`.**

If a convex-hull point saturates a nonzero linear reporter that bounds every generator, it is a
convex combination of at most `N` generators on that exposed face, rather than the generic
`N + 1`. -/
theorem bellmanShoreline_convexHull_mem_exposedSlice_atomicSpan
    {K : Set (Fin N → ℝ)} {x n : Fin N → ℝ} {mu : ℝ}
    (hx : x ∈ convexHull ℝ K) (hn : n ≠ 0)
    (hsupport : ∀ y ∈ K, dotProduct n y ≤ mu)
    (hcontact : dotProduct n x = mu) :
    x ∈ atomicSpan N (bellmanShorelineExposedSlice K n mu) := by
  obtain ⟨ι, hιfin, z, w, hzrange, hindep, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  classical
  have hface : ∀ i, dotProduct n (z i) = mu := by
    have hsumzero : ∑ i, w i * (dotProduct n (z i) - mu) = 0 := by
      calc
        ∑ i, w i * (dotProduct n (z i) - mu) =
            dotProduct n (∑ i, w i • z i) - (∑ i, w i) * mu := by
              rw [dotProduct_sum]
              simp_rw [dotProduct_smul, mul_sub]
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
              have hcomm : ∑ i, w i * dotProduct n (z i) =
                  ∑ i, dotProduct n (z i) * w i := by
                apply Finset.sum_congr rfl
                intro i _
                exact mul_comm _ _
              rw [hcomm]
              ring_nf
        _ = 0 := by rw [hwz, hwsum, hcontact]; ring_nf
    have hterm : ∀ i ∈ (Finset.univ : Finset ι),
        w i * (dotProduct n (z i) - mu) ≤ 0 := by
      intro i _
      exact mul_nonpos_of_nonneg_of_nonpos (hwpos i).le
        (sub_nonpos.mpr (hsupport (z i) (hzrange ⟨i, rfl⟩)))
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsumzero
    intro i
    have hi := hall i (Finset.mem_univ i)
    have hdiff : dotProduct n (z i) - mu = 0 :=
      (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hwpos i))
    exact sub_eq_zero.mp hdiff
  have hιne : Nonempty ι := by
    by_contra hne
    letI : IsEmpty ι := not_nonempty_iff.mp hne
    have hzero : ∑ i, w i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact isEmptyElim i
    rw [hzero] at hwsum
    exact zero_ne_one hwsum
  letI : Nonempty ι := hιne
  let phi : (Fin N → ℝ) →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin N) n
  have hphi : phi ≠ 0 := by
    exact fun hzero =>
      hn ((dotProductEquiv ℝ (Fin N)).injective (by simpa [phi] using hzero))
  let H : AffineSubspace ℝ (Fin N → ℝ) := AffineSubspace.mk' x phi.ker
  have hzH : Set.range z ⊆ (H : Set (Fin N → ℝ)) := by
    rintro y ⟨i, rfl⟩
    change z i - x ∈ phi.ker
    rw [LinearMap.mem_ker]
    dsimp [phi]
    change dotProduct n (z i - x) = 0
    rw [dotProduct_sub, hface i, hcontact, sub_self]
  have hspan : affineSpan ℝ (Set.range z) ≤ H := affineSpan_le.mpr hzH
  have hvspan : vectorSpan ℝ (Set.range z) ≤ phi.ker := by
    have hdir := AffineSubspace.direction_le hspan
    rw [direction_affineSpan] at hdir
    simpa [H] using hdir
  have hfinrank : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 ≤ N := by
    calc
      Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 ≤
          Module.finrank ℝ phi.ker + 1 :=
        Nat.add_le_add_right (Submodule.finrank_mono hvspan) 1
      _ = Module.finrank ℝ (Fin N → ℝ) :=
        Module.Dual.finrank_ker_add_one_of_ne_zero hphi
      _ = N := Module.finrank_fin_fun ℝ
  have hcard : Fintype.card ι ≤ N := by
    rw [← hindep.finrank_vectorSpan_add_one]
    exact hfinrank
  let k0 : Fin N → ℝ := z (Classical.choice hιne)
  have hk0 : k0 ∈ bellmanShorelineExposedSlice K n mu := by
    exact ⟨hzrange ⟨Classical.choice hιne, rfl⟩, hface (Classical.choice hιne)⟩
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin N) := by
    exact Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  set w' : Fin N → ℝ := Function.extend e w (fun _ => 0) with hw'def
  set z' : Fin N → (Fin N → ℝ) := Function.extend e z (fun _ => k0) with hz'def
  have hw'e : ∀ i : ι, w' (e i) = w i :=
    fun i => e.injective.extend_apply w (fun _ => 0) i
  have hz'e : ∀ i : ι, z' (e i) = z i :=
    fun i => e.injective.extend_apply z (fun _ => k0) i
  have hw'out : ∀ j : Fin N, (¬ ∃ i, e i = j) → w' j = 0 := by
    intro j hj
    rw [hw'def]
    exact Function.extend_apply' w (fun _ => 0) j hj
  have hz'out : ∀ j : Fin N, (¬ ∃ i, e i = j) → z' j = k0 := by
    intro j hj
    rw [hz'def]
    exact Function.extend_apply' z (fun _ => k0) j hj
  refine ⟨w', z', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j
    by_cases hex : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hex
      rw [hw'e i]
      exact (hwpos i).le
    · rw [hw'out j hex]
  · rw [sum_extend_embedding e w' hw'out]
    rw [Finset.sum_congr rfl (fun i _ => hw'e i)]
    exact hwsum
  · intro j
    by_cases hex : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hex
      rw [hz'e i]
      exact ⟨hzrange ⟨i, rfl⟩, hface i⟩
    · rw [hz'out j hex]
      exact hk0
  · have hzero : ∀ j : Fin N, (¬ ∃ i, e i = j) →
        (fun j => w' j • z' j) j = 0 := by
      intro j hj
      simp only []
      rw [hw'out j hj, zero_smul]
    rw [sum_extend_embedding e (fun j => w' j • z' j) hzero]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hw'e i, hz'e i])]
    exact hwz

/-- Exposed boundary points in the closed convex hull of a compact generator also admit the sharp
`N`-atom certificate. This strengthens `exists_atomic_of_mem_closure_convexHull` by one atom on
every saturated support plane. -/
theorem bellmanShoreline_exists_exposed_atomic_of_mem_closure_convexHull
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    {x n : Fin N → ℝ} {mu : ℝ}
    (hx : x ∈ closure (convexHull ℝ K)) (hn : n ≠ 0)
    (hsupport : ∀ y ∈ K, dotProduct n y ≤ mu)
    (hcontact : dotProduct n x = mu) :
    ∃ (w : Fin N → ℝ) (z : Fin N → (Fin N → ℝ)),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        (∀ i, z i ∈ bellmanShorelineExposedSlice K n mu) ∧
          ∑ i, w i • z i = x := by
  obtain ⟨w, z, hw0, hw1, hz, hwz⟩ :=
    exists_atomic_of_mem_closure_convexHull hK hne hx
  have hxHull : x ∈ convexHull ℝ K := by
    rw [← hwz]
    exact (convex_convexHull ℝ K).sum_mem
      (fun i _ => hw0 i) hw1 (fun i _ => subset_convexHull ℝ K (hz i))
  obtain ⟨w', z', hw', hz', hsum'⟩ :=
    bellmanShoreline_convexHull_mem_exposedSlice_atomicSpan
      hxHull hn hsupport hcontact
  exact ⟨w', z', hw'.1, hw'.2, hz', hsum'⟩

end GaloisForLFunctions.HTGeometry

end
