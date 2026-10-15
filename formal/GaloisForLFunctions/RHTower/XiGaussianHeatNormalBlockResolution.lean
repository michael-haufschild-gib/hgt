import GaloisForLFunctions.HTGeometry.MomentHankelHyperbolicResolution
import GaloisForLFunctions.RHTower.XiGaussianHeatEndpointRigidity
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelInertia

/-!
# Unconditional normal-block resolution of the actual heat Hankel ladder

At every positive heat time, existing nondegeneracy of the actual heat form
produces a unique finite normal block around each rank. Its singular kernels
are consecutive multiples of one canonical monic polynomial, with exact
nullity `min k (d-k)`. The next head is invertible, regular heads are cofinal,
and each genuine gap produces an explicit hyperbolic plane orthogonal to its
old head. No RH, positivity, generic-time, or nonzero-pivot premise is added.

This resolves singular finite-section geometry. It does not orient the
arithmetic source, assert positivity, or give a full block-inertia census.
-/

open scoped BigOperators
open Polynomial Matrix HTGeometry
namespace RHTower
noncomputable section

theorem ofReal_heatRealMoments (a : ℝ) (i : ℕ) :
    (heatRealMoments a i : ℂ) = xiHeatMoment i a := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (im_xiHeatMoment i a).symm

theorem heatHankel_mapReal_eq_momentRows {a : ℝ} (ha : 0 < a)
    (P : ℝ[X]) (R : ℂ[X]) :
    heatHankel a (P.map Complex.ofRealHom) R =
      ∑ j ∈ R.support, (starRingEnd ℂ) (R.coeff j) *
        (momentFunctional (heatRealMoments a) (X ^ j * P) : ℂ) := by
  rw [heatHankel_eq_moments ha, Polynomial.sum_def]
  rw [Polynomial.support_map_of_injective P Complex.ofReal_injective]
  simp only [Polynomial.coeff_map, Polynomial.sum_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hrow : momentFunctional (heatRealMoments a) (X ^ j * P) =
      ∑ k ∈ P.support, P.coeff k * heatRealMoments a (j + k) := by
    simpa only [one_mul, mul_one, momentFunctional_X_pow] using
      momentFunctional_X_pow_mul_mul_eq_sum (heatRealMoments a) 1 P j
  rw [hrow, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.ofReal_mul, ofReal_heatRealMoments, Nat.add_comm j k]
  change (P.coeff k : ℂ) * (starRingEnd ℂ) (R.coeff j) * xiHeatMoment (k + j) a = _
  ring

/-- Actual heat moments have no invisible real polynomial. -/
theorem nondegenerate_heatRealMoments (a : {t : ℝ // 0 < t}) :
    NondegenerateMomentSequence (heatRealMoments a) := by
  intro P hP
  have hz : P.map Complex.ofRealHom = 0 :=
    eq_zero_of_forall_heatHankel_eq_zero a.property (fun R => by
      rw [heatHankel_mapReal_eq_momentRows a.property]
      simp only [hP, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero])
  exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hz

/-- Regular heads are cofinal at every actual positive heat time. -/
theorem hcf_regular_heads_cofinal (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ n ≥ N, (momentHankelMatrix (heatRealMoments a) n).det ≠ 0 :=
  cofinal_regular_momentHeads (nondegenerate_heatRealMoments a) N

/-- Unconditional classification of every actual heat-Hankel kernel, including all singular times.
The block is unique by `MomentNormalBlock.cover_unique`, and its next head is invertible. -/
theorem hcf_normal_block_resolution (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ n d, MomentNormalBlock (heatRealMoments a) n d ∧ n ≤ N ∧ N < n + d ∧
      (momentHankelMatrix (heatRealMoments a) (n + d)).det ≠ 0 ∧
      (∀ c : Fin N → ℝ, momentHankelMatrix (heatRealMoments a) N *ᵥ c = 0 ↔
        ∃ q : ℝ[X], q.degree < ((min (N - n) (d - (N - n)) : ℕ) : WithBot ℕ) ∧
          Polynomial.ofFn N c = monicMomentAdmissionPolynomial (heatRealMoments a) n * q) ∧
      Module.finrank ℝ (LinearMap.ker (momentHankelMatrix (heatRealMoments a) N).mulVecLin) =
        min (N - n) (d - (N - n)) := by
  obtain ⟨n, d, h, hn, hN⟩ :=
    exists_momentNormalBlock_cover (nondegenerate_heatRealMoments a) N
  have he : n + (N - n) = N := by omega
  have hk : N - n ≤ d := by omega
  refine ⟨n, d, h, hn, hN, h.next_regular, ?_, ?_⟩
  · intro c
    have hh := h.kernel_iff hk (Polynomial.ofFn N c)
    rw [he, momentSectionKernel_ofFn_iff] at hh
    exact hh
  · have hh := h.nullity hk
    rwa [he] at hh

/-- A singular actual section cannot be a terminal obstruction: its next regular block contains
an explicit hyperbolic plane orthogonal to the preceding regular head. -/
theorem hcf_singular_section_resolution (a : {t : ℝ // 0 < t}) (N : ℕ) :
    (momentHankelMatrix (heatRealMoments a) N).det ≠ 0 ∨
      ∃ (n d : ℕ) (U V : ℝ[X]), MomentNormalBlock (heatRealMoments a) n d ∧
        n < N ∧ N < n + d ∧
        (momentHankelMatrix (heatRealMoments a) (n + d)).det ≠ 0 ∧
        U.natDegree < n + d ∧ V.natDegree < n + d ∧
        momentInner (heatRealMoments a) U U = 2 ∧
        momentInner (heatRealMoments a) V V = -2 ∧
        momentInner (heatRealMoments a) U V = 0 ∧
        ∀ i : Fin n, momentInner (heatRealMoments a) (X ^ (i : ℕ)) U = 0 ∧
          momentInner (heatRealMoments a) (X ^ (i : ℕ)) V = 0 := by
  classical
  by_cases hreg : (momentHankelMatrix (heatRealMoments a) N).det ≠ 0
  · exact Or.inl hreg
  obtain ⟨n, d, h, hn, hN⟩ :=
    exists_momentNormalBlock_cover (nondegenerate_heatRealMoments a) N
  have hnN : n < N := by
    by_contra hh
    have he : n = N := by omega
    exact hreg (he ▸ h.head_regular)
  have hd : 1 < d := by omega
  obtain ⟨U, V, hU, hV, hUU, hVV, hUV, horth⟩ := h.exists_hyperbolic_plane hd
  exact Or.inr ⟨n, d, U, V, h, hnN, hN, h.next_regular, hU, hV, hUU, hVV, hUV, horth⟩

end
end RHTower
